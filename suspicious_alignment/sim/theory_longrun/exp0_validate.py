"""exp0: sanity checks of the numpy ports and of the exact scalar reduction.

(a) Gram-based filter == SVD-based filter (all kinds).
(b) Commuting (M2) initialisation: one step of the full matrix update W+ = W - eta F(A W)
    equals the decoupled scalar recursion a_i+ = a_i - eta f(lam_i a_i) on the row norms
    (Theorem 1 of the note), for sgd / muon / ht(p) / echelon(r), over many steps.
(c) Muon, d <= n, generic init: exact identities
       K+ = |K - eta*Lam|,   L(t+2) - L(t) = -2 eta tr (K_t - eta Lam)_+   (Theorem 6).
(d) Echelon definition O = U_r P + T/tau reproduces f = (1,..,1, s_{r+1..}/s_{r+1}).
"""
import numpy as np

from common import spectral_filter, spectrum, save_json

rng = np.random.default_rng(12345)
out = {}

# (a) ------------------------------------------------------------------ gram vs svd
errs = {}
for (d, n) in [(12, 30), (30, 12), (20, 20)]:
    G = rng.standard_normal((d, n))
    for kind, kw in [("sgd", {}), ("muon", {}), ("ht", {"p": 0.125}), ("ht", {"p": 0.5}),
                     ("ech", {"r": 3}), ("ns5", {}), ("htns", {"p": 0.125})]:
        A = spectral_filter(G, kind, **kw)
        B = spectral_filter(G, kind, use_svd=True, **kw)
        errs[f"{kind}{kw}_{d}x{n}"] = float(np.abs(A - B).max())
out["gram_vs_svd_maxerr"] = max(errs.values())
print("(a) max |gram - svd| over filters/shapes:", out["gram_vs_svd_maxerr"])

# (d) ------------------------------------------------------------------ Echelon definition
d, n, r = 15, 25, 4
X = rng.standard_normal((d, n))
U, s, Vt = np.linalg.svd(X, full_matrices=False)
Ur = U[:, :r]
H = Ur.T @ X
Uh, sh, Vht = np.linalg.svd(H, full_matrices=False)
P = Uh @ Vht
T = X - Ur @ (Ur.T @ X)
tau = np.linalg.norm(T, 2)
O = Ur @ P + T / tau
out["echelon_def_err"] = float(np.abs(O - spectral_filter(X, "ech", r=r, use_svd=True)).max())
print("(d) |U_r P + T/tau - U f(S) V^T| =", out["echelon_def_err"])

# (b) ------------------------------------------------------------------ scalar reduction
d, n, k, m, eta = 12, 16, 3, 10.0, 0.05
lam = spectrum(d, k, m)
Q, _ = np.linalg.qr(rng.standard_normal((n, d)))  # orthonormal columns -> rows of Q^T orthonormal
a0 = 1.0 + rng.random(d)
red = {}
from common import fvals
for kind, kw, et in [("sgd", {}, 0.4 / lam[0]), ("muon", {}, eta), ("ht", {"p": 0.125}, eta),
                     ("ht", {"p": 0.5}, eta), ("ech", {"r": 2}, eta), ("ech", {"r": 5}, eta)]:
    C = a0[:, None] * Q.T.copy()
    a = a0.copy()          # free-running scalar recursion
    worst_free, worst_step = 0.0, 0.0
    for t in range(400):
        # one-step prediction from the CURRENT matrix state (exact statement of Theorem 1)
        ac = np.linalg.norm(C, axis=1)
        sig = lam * ac
        order = np.argsort(-sig)
        f = np.empty(d)
        f[order] = fvals(sig[order], kind, **kw)
        pred = np.abs(ac - et * f)
        C = C - et * spectral_filter(lam[:, None] * C, kind, use_svd=True, **kw)
        worst_step = max(worst_step, float(np.abs(np.linalg.norm(C, axis=1) - pred).max()))
        # free-running recursion (can separate from the matrix run by round-off amplification
        # when the dynamics has an expanding transient, as for Echelon with r + 1 <= k)
        sig = lam * a
        order = np.argsort(-sig)
        f[order] = fvals(sig[order], kind, **kw)
        a = np.abs(a - et * f)
        worst_free = max(worst_free, float(np.abs(np.linalg.norm(C, axis=1) - a).max()))
    offd = C @ C.T
    offd = offd - np.diag(np.diag(offd))
    red[f"{kind}{kw}"] = {"max_one_step_err": worst_step, "max_free_running_err": worst_free,
                          "max_offdiag_CCt": float(np.abs(offd).max())}
    print(f"(b) {kind}{kw}: one-step err = {worst_step:.2e}, free-running err over 400 steps = "
          f"{worst_free:.2e}, offdiag(CC^T) = {np.abs(offd).max():.2e}")
out["scalar_reduction"] = red

# (c) ------------------------------------------------------------------ K-iteration / Lyapunov
d, n, k, m, eta = 10, 14, 2, 8.0, 0.03
lam = spectrum(d, k, m)
C = 0.2 * rng.standard_normal((d, n))


def loss(C):
    return 0.5 * float((lam[:, None] * C * C).sum())


def Kof(C):
    G = lam[:, None] * C
    w, U = np.linalg.eigh(G @ G.T)
    return (U * np.sqrt(np.clip(w, 0, None))) @ U.T


def absm(X):
    w, U = np.linalg.eigh(X)
    return (U * np.abs(w)) @ U.T, float(np.clip(w, 0, None).sum())


Ls, errK, errL, absorbed_at = [loss(C)], 0.0, 0.0, None
Ks, pos = [Kof(C)], []
for t in range(600):
    C = C - eta * spectral_filter(lam[:, None] * C, "muon", use_svd=True)
    Ls.append(loss(C))
    Ks.append(Kof(C))
    Kabs, trpos = absm(Ks[-2] - eta * np.diag(lam))
    pos.append(trpos)
    errK = max(errK, float(np.abs(Kabs - Ks[-1]).max()))
    if absorbed_at is None and trpos < 1e-13:
        absorbed_at = t
for t in range(len(Ls) - 2):
    errL = max(errL, abs((Ls[t + 2] - Ls[t]) + 2 * eta * pos[t]))
Lbar = 0.5 * (Ls[-1] + Ls[-2]) / (eta ** 2 * lam.sum())
out["K_iteration"] = {"max_err_K_recursion": errK, "max_err_two_step_identity": errL,
                      "first_t_with_tr_pos_part_below_1e-13": absorbed_at,
                      "two_step_mean_loss_over_eta2_trA": Lbar,
                      "max_two_step_increase": float(max(Ls[t + 2] - Ls[t] for t in range(len(Ls) - 2)))}
print("(c) max |K+ - |K - eta Lam||            =", errK)
print("    max |L(t+2)-L(t) + 2 eta tr(K-eta Lam)_+| =", errL)
print("    absorbed (tr pos part < 1e-13) at t =", absorbed_at,
      "; mean loss / (eta^2 tr A) =", Lbar, "(theory: in [1/8, 1/4])")

save_json("exp0_validate.json", out)
