"""exp2b: momentum (beta, Nesterov, exactly as in muon.py) in the noise-free commuting model.

Per eigen-direction (signed radial coordinate a, eigenvalue lam):
    g = lam * a;  mom <- beta*mom + (1-beta)*g;  u = (1-beta)*g + beta*mom   (Nesterov lerp)
    a <- a - eta * |u|^p sign(u)
Scale covariance (Theorem 5): a(t) = s * b(t) with s = (eta lam^p)^(1/(1-p)) and b the universal
(eta = lam = 1) trajectory started at a(0)/s.  Hence long-run energy = (eta lam)^(2/(1-p)) * <b^2>.

(i)   universal constants C(p, beta) = long-run time average of b^2, for several b(0);
(ii)  numerical check of scale covariance;
(iii) theta_inf over the m-grid with beta = 0.95 (d = 500, k = 50) vs sum_D lam^q / sum lam^q;
(iv)  faithful scalar port of 'htmuon_ns' (NS5 polar factor times Newton-Schulz (G^T G)^(1/16)).
"""
import math
import time

import numpy as np

from common import msd, ns5_scalar, ratio_pred, save_json, spectrum, theta_from_energy

t0 = time.time()
out = {}


def universal(p, beta, b0, T, tail):
    """b0: array of initial conditions (vectorised).  Returns <b^2>, max|b|, detected period."""
    b = np.array(b0, dtype=float)
    mom = np.zeros_like(b)
    acc = np.zeros_like(b)
    mx = np.zeros_like(b)
    hist = np.empty((tail, b.size))
    for t in range(T):
        mom = beta * mom + (1 - beta) * b
        u = (1 - beta) * b + beta * mom
        b = b - np.abs(u) ** p * np.sign(u)
        if t >= T - tail:
            acc += b * b
            mx = np.maximum(mx, np.abs(b))
            hist[t - (T - tail)] = b
    per = []
    for j in range(b.size):
        h = hist[:, j]
        pj = -1
        for L in range(1, tail // 2):
            if np.allclose(h[L:], h[:-L], rtol=1e-9, atol=1e-12):
                pj = L
                break
        per.append(pj)
    return acc / tail, mx, per


rows = []
B0 = [3.3, 17.77, 61.5, 240.123, 999.9]
for p in [0.0, 0.125, 0.25, 0.5]:
    for beta in [0.0, 0.5, 0.9, 0.95]:
        C, mx, per = universal(p, beta, B0, T=60000, tail=8000)
        rows.append(dict(p=p, beta=beta, C_mean=float(C.mean()), C_min=float(C.min()), C_max=float(C.max()),
                         max_abs_b=float(mx.max()), periods=per))
        print(f"[universal] p={p} beta={beta}: <b^2> = {C.mean():.5g} (min {C.min():.5g}, max {C.max():.5g} over "
              f"{len(B0)} inits), max|b| = {mx.max():.4g}, period = {per}")
out["universal"] = rows

# (ii) scale covariance
p, beta, eta, lam, a0 = 0.125, 0.95, 0.01, 37.0, 4.2
s = (eta * lam ** p) ** (1 / (1 - p))
a, mom = a0, 0.0
b, momb = a0 / s, 0.0
worst = 0.0
for t in range(3000):
    g = lam * a
    mom = beta * mom + (1 - beta) * g
    u = (1 - beta) * g + beta * mom
    a = a - eta * abs(u) ** p * np.sign(u)
    momb = beta * momb + (1 - beta) * b
    ub = (1 - beta) * b + beta * momb
    b = b - abs(ub) ** p * np.sign(ub)
    worst = max(worst, abs(a - s * b) / s)
out["scale_covariance_max_rel_err"] = worst
print("[covariance] max |a(t) - s b(t)| / s over 3000 steps:", worst)

# (iii) theta_inf with momentum over the m grid
D, K, ETA, N_INIT = 500, 50, 0.01, 100
MS = [2, 5, 10, 20, 50, 100, 200, 500]
SEEDS = list(range(8))
a_init = np.stack([np.linalg.norm(np.random.default_rng(100 + s_).standard_normal((D, N_INIT)), axis=1)
                   for s_ in SEEDS])
rows = []
for p in [0.0, 0.125]:
    q = 2 / (1 - p)
    for m in MS:
        lam = spectrum(D, K, m)
        a = a_init.copy()
        mom = np.zeros_like(a)
        T, tail = 30000, 6000
        thm = np.empty(T)
        Eacc = np.zeros_like(a)
        for t in range(T):
            g = lam * a
            E = g * g
            thm[t] = (E[:, :K].sum(1) / E.sum(1)).mean()
            if t >= T - tail:
                Eacc += E
            mom = 0.95 * mom + 0.05 * g
            u = 0.05 * g + 0.95 * mom
            a = a - ETA * np.abs(u) ** p * np.sign(u)
        Ebar = Eacc / tail
        th = theta_from_energy(Ebar, K)
        Cdir = Ebar / (ETA * lam) ** q          # should be the universal constant C(p, beta)
        rows.append(dict(p=p, m=m, pred=ratio_pred(lam, K, q), meas=msd(th),
                         C_dir_mean=float(Cdir.mean()), C_dir_cv=float(Cdir.std() / Cdir.mean()),
                         theta0=float(thm[0]), theta_min=float(thm.min()), tmin=int(np.argmin(thm))))
        r_ = rows[-1]
        print(f"[mom 0.95, p={p}] m={m:4d} pred={r_['pred']:.8f} meas={r_['meas'][0]:.8f}+-{r_['meas'][1]:.1e} "
              f"E_i/(eta lam_i)^q = {r_['C_dir_mean']:.4g} (cv {r_['C_dir_cv']:.2e}) theta_min={r_['theta_min']:.3e} at {r_['tmin']}")
        if m == 100:
            sub = np.unique(np.concatenate([np.arange(0, 6000, 2), np.arange(6000, T, 40)]))
            out[f"mom_p{p}_curve_m100"] = dict(t=sub, theta_mean=thm[sub])
out["momentum_theta"] = rows


# (iv) faithful scalar port of htmuon_ns in the commuting model -----------------------------
def gram_root_scalar(sig, n_extra_zeros, power=0.125, ns_steps=5, eps=1e-6):
    """Eigenvalue map of gram_root_1_16_via_newtonschulz for a matrix whose G^T G has eigenvalues
    sig^2 (and n_extra_zeros zero eigenvalues).  sig: (S, d).  Returns the eigenvalues attached to
    the d non-zero directions."""
    s = sig * sig + eps
    z0 = np.full((sig.shape[0], 1), eps)          # the zero eigenvalues (+eps)
    val = int(round(math.log(power, 0.5) + 1))
    for _ in range(val):
        alpha = np.sqrt((s * s).sum(1, keepdims=True) + n_extra_zeros * z0 * z0)
        alpha = np.maximum(alpha, eps)
        y, z = s / alpha, np.ones_like(s)
        y0, zz0 = z0 / alpha, np.ones_like(z0)
        for _ in range(ns_steps):
            T_ = 3.0 - z * y
            y, z = 0.5 * y * T_, 0.5 * T_ * z
            T0 = 3.0 - zz0 * y0
            y0, zz0 = 0.5 * y0 * T0, 0.5 * T0 * zz0
        s = np.sqrt(alpha) * y + eps
        z0 = np.sqrt(alpha) * y0 + eps
    return s


rows = []
N_COLS = 600   # pretend the matrix is d x 600 (so G^T G has 100 zero eigenvalues)
for m in MS:
    lam = spectrum(D, K, m)
    a = a_init.copy()
    T, tail = 12000, 1000
    Eacc = np.zeros_like(a)
    thm = np.empty(T)
    for t in range(T):
        sig = lam * a
        E = sig * sig
        thm[t] = (E[:, :K].sum(1) / E.sum(1)).mean()
        if t >= T - tail:
            Eacc += E
        f = ns5_scalar(sig / (np.sqrt(E.sum(1, keepdims=True)) + 1e-7)) * gram_root_scalar(sig, N_COLS - D)
        a = np.maximum(np.abs(a - ETA * f), 1e-280)
    Ebar = Eacc / tail
    th = theta_from_energy(Ebar, K)
    rows.append(dict(m=m, meas=msd(th), one_minus=float(1 - th.mean()), pred_q16_7=ratio_pred(lam, K, 16 / 7),
                     theta_min=float(thm.min()), tmin=int(np.argmin(thm)),
                     E_D_over_floor=float((Ebar[:, :K] / (ETA * lam[:K] / 2) ** (16 / 7)).mean()),
                     E_B_over_floor=float((Ebar[:, K:] / (ETA * lam[K:] / 2) ** (16 / 7)).mean())))
    r_ = rows[-1]
    print(f"[htmuon_ns faithful scalar port] m={m:4d} meas={r_['meas'][0]:.8f}+-{r_['meas'][1]:.1e} "
          f"(exact-HT pred {r_['pred_q16_7']:.8f}) E_D/floor={r_['E_D_over_floor']:.3g} "
          f"E_B/floor={r_['E_B_over_floor']:.3g} theta_min={r_['theta_min']:.2e} at {r_['tmin']}")
out["htmuon_ns_faithful"] = rows

save_json("exp2b_momentum_scalar.json", out)
print("elapsed", time.time() - t0)
