"""
test_port.py -- sanity checks of the numpy ports in spfilters.py.

torch is not available on this machine, so the ports cannot be cross-checked against the original
functions numerically.  Instead each port is checked against an independent mathematical
characterisation of what the torch code computes:

  T1  NS5 acts on singular values as the scalar quintic iterated 5 times on sigma/(||G||_F+1e-7),
      and keeps the singular vectors (off-diagonal energy ~ 1e-30).
  T2  the Gram-root Newton-Schulz iteration acts on the eigenvalues of G^T G as the scalar model
      `gram_root_scalar`, and equals (G^T G + eps)^(1/16) when the spectrum is well conditioned.
  T3  HT-NS = NS5 x gram root has the transfer  ns5(sigma/||G||_F) * gramroot(sigma^2).
  T4  the stream QR filter applied repeatedly to a FIXED matrix converges to U S^p V^T.
  T5  Echelon with exact frame and exact tau equals U diag(min(1, sigma_i/sigma_{r+1})) V^T; the
      Lean identities gram_split (O^T O = P^T P + tau^-2 T^T T), ||O||_2 <= sqrt 2 and the polished
      bound ||cubic(O)||_2 <= 1 hold for a random (wrong) orthonormal frame.
  T6  nesterov_lerp reproduces  m <- m + (1-b)(g-m);  u = g + b (m - g).
  T7  bf16 rounding: representable values are fixed points, ties go to even, relative error <= 2^-8.
  T8  the interval optimizer uses the HT filter exactly on steps 5, 10, 15, ...

Run:  python3 test_port.py
"""
import numpy as np
import spfilters as sp

rng = np.random.default_rng(123)
ok = True


def check(name, cond, info=''):
    global ok
    ok = ok and bool(cond)
    print(f"[{'ok' if cond else 'FAIL'}] {name} {info}")


d, n = 200, 40
G = rng.standard_normal((d, n)) * np.geomspace(1.0, 1e-4, n)[None, :]
U, S, Vh = np.linalg.svd(G, full_matrices=False)

# T1
out = sp.zeropower_via_newtonschulz5(G)
t, off = sp.transfer(out, U, Vh)
pred = sp.ns5_scalar(S / (np.linalg.norm(G) + 1e-7))
check('T1 NS5 scalar model', np.max(np.abs(t - pred)) < 1e-9 and off < 1e-12,
      f'max|t-pred|={np.max(np.abs(t - pred)):.2e} offdiag={off:.1e}')
Gw = rng.standard_normal((n, d))       # wide input: no transposition branch
Uw, Sw, Vhw = np.linalg.svd(Gw, full_matrices=False)
tw, offw = sp.transfer(sp.zeropower_via_newtonschulz5(Gw), Uw, Vhw)
check('T1 NS5 wide', np.max(np.abs(tw - sp.ns5_scalar(Sw / (np.linalg.norm(Gw) + 1e-7)))) < 1e-9)

# T2
R = sp.gram_root_1_16_via_newtonschulz(G, 0.125)
ev = np.diag(Vh @ R @ Vh.T)
pred = sp.gram_root_scalar(S ** 2, 0.125)
check('T2 gram-root scalar model', np.max(np.abs(ev - pred) / pred) < 1e-8,
      f'max rel={np.max(np.abs(ev - pred) / pred):.2e}')
Gc = sp.haar(d, n, rng) @ np.diag(np.linspace(1.0, 0.7, n)) @ sp.haar(n, n, rng).T
Uc, Sc, Vhc = np.linalg.svd(Gc, full_matrices=False)
Rc = sp.gram_root_1_16_via_newtonschulz(Gc, 0.125)
ex = (Vhc.T * (Sc ** 2 + 1e-6) ** (1 / 16)) @ Vhc
check('T2 gram-root exact on a well-conditioned input', sp.rel_err(Rc, ex) < 2e-2,
      f'rel err={sp.rel_err(Rc, ex):.2e}')
# power = 0.25 -> 3 square roots, power = 0.5 -> 2
for p, nroot in [(0.25, 3), (0.5, 2), (0.125, 4)]:
    Rp = sp.gram_root_1_16_via_newtonschulz(Gc, p)
    exp_ = (Vhc.T * (Sc ** 2) ** (p / 2)) @ Vhc
    check(f'T2 exponent for power={p} is sigma^{p}', sp.rel_err(Rp, exp_) < 5e-2,
          f'rel err={sp.rel_err(Rp, exp_):.2e}')

# T3
o = sp.Opt('ht_ns', (d, n))
t3, off3 = sp.transfer(o.filter(G), U, Vh)
pred3 = sp.ns5_scalar(S / (np.linalg.norm(G) + 1e-7)) * sp.gram_root_scalar(S ** 2, 0.125)
check('T3 HT-NS transfer = ns5 * gramroot', np.max(np.abs(t3 - pred3)) < 1e-8 and off3 < 1e-10,
      f'max|diff|={np.max(np.abs(t3 - pred3)):.2e}')

# T4
Gs = sp.haar(d, n, rng) @ np.diag(np.geomspace(1.0, 0.05, n)) @ sp.haar(n, n, rng).T
ex = sp.msign_generalized_ht_v2(Gs, 0.125)
V = None
errs = []
for j in range(400):
    out, V = sp.msign_generalized_ht_v2_stream_qr(Gs, V, p=0.125)
    if j in (0, 9, 99, 399):
        errs.append(sp.rel_err(out, ex))
check('T4 stream converges on a fixed matrix', errs[-1] < 1e-6 and errs[0] > errs[1] > errs[2],
      f'rel err after 1/10/100/400 calls: {errs}')
check('T4 stream V orthonormal', np.max(np.abs(V.T @ V - np.eye(n))) < 1e-10)

# T5
for r in (1, 4, 16):
    e = sp.Echelon(r, frame='exact', tau='exact')
    O = e(G)
    f = np.minimum(1.0, S / S[r])
    f[:r] = 1.0
    check(f'T5 ideal Echelon({r}) = spectral filter min(1, s/s_r+1)', sp.rel_err(O, (U * f) @ Vh) < 1e-8)
Ur = sp.haar(d, 6, rng)                      # arbitrary orthonormal frame
H = Ur.T @ G
Uh, _, Vhh = np.linalg.svd(H, full_matrices=False)
P = Uh @ Vhh
T = G - Ur @ H
tau = np.linalg.norm(T, 2)
O = Ur @ P + T / tau
check('T5 gram_split', sp.rel_err(O.T @ O, P.T @ P + T.T @ T / tau ** 2) < 1e-10)
check('T5 ||O||_2 <= sqrt 2', np.linalg.norm(O, 2) <= np.sqrt(2) + 1e-12, f'{np.linalg.norm(O, 2):.4f}')
check('T5 polished ||O||_2 <= 1', np.linalg.norm(sp.cubic_step(O), 2) <= 1 + 1e-12,
      f'{np.linalg.norm(sp.cubic_step(O), 2):.4f}')
e = sp.Echelon(4, frame='tracked', tau='pi', diagnose=True)
for j in range(60):
    O = e(G)
check('T5 tracked frame converges on a fixed matrix', e.last_frame_err < 1e-6 and abs(e.last_tau_ratio - 1) < 1e-3,
      f'frame err={e.last_frame_err:.1e} tau/||T||_2={e.last_tau_ratio:.6f}')

# T6
g1 = rng.standard_normal((3, 2))
m0 = rng.standard_normal((3, 2))
u, m1 = sp.nesterov_lerp(g1, m0, 0.95, True)
check('T6 nesterov lerp', np.allclose(m1, 0.95 * m0 + 0.05 * g1) and np.allclose(u, 0.05 * g1 + 0.95 * m1)
      and np.allclose(u, 0.9025 * m0 + 0.0975 * g1))

# T7
x = np.array([1.0, 1.0 + 2.0 ** -7, 1.0 + 2.0 ** -8, 1.0 + 3 * 2.0 ** -8, 3.14159265, -2.5e-5], dtype=np.float32)
y = sp.bf16_round(x)
check('T7 bf16 fixed points and ties-to-even',
      y[0] == 1.0 and y[1] == np.float32(1.0 + 2.0 ** -7) and y[2] == 1.0 and y[3] == np.float32(1.0 + 2.0 ** -6),
      str(y[:4]))
z = rng.standard_normal(10000).astype(np.float32)
check('T7 bf16 relative error <= 2^-8', np.max(np.abs(sp.bf16_round(z) - z) / np.abs(z)) <= 2.0 ** -8 + 1e-9)

# T8
o = sp.Opt('ht_interval', (d, n), interval=5)
flags = []
for j in range(12):
    o.direction(G)
    flags.append(o.last_was_ht)
check('T8 interval schedule', [i + 1 for i, f in enumerate(flags) if f] == [5, 10], str(flags))

print('ALL OK' if ok else 'SOME CHECKS FAILED')
