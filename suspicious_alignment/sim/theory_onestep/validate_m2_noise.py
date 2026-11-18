"""Model (M2) with noise (Section 3.6-3.7 and 5.4 of the note).

 N1  co-diagonal noise Xi = U diag(zeta) Q: per-realisation exactness of the signed-coordinate map
     alpha_i+ = alpha_i - eta f_odd(lam_i alpha_i + zeta_i) against the direct SVD; commuting preserved
 N2  closed forms of the Gaussian-smoothed filters  fbar(sigma) = E f_odd(sigma + zeta),
     f2(sigma) = E f(|sigma + zeta|)^2   (Muon: erf; HTMuon: Kummer functions) vs numerical quadrature
 N3  direct-SVD Monte Carlo of E[s_+^S] and of the projected loss change vs the closed forms
 N4  i.i.d. Gaussian matrix noise: E[U^T F(G) Qt^T] is "diagonal" and E[Phi Phi^T] is diagonal
     (symmetry lemma); Muon: ||phi_i|| = 1 for every realisation
 N5  wide limit n >> d: m_i ~ sigma_i gamma(sqrt(sigma_i^2 + varsigma^2 n)), v_i ~ f(sqrt(...))^2
Output: results/m2_noise.json
"""
import os
import sys
import time
import numpy as np
from scipy import special, integrate

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import (FILTERS, f_echelon, apply_filter, rand_orth, make_spectrum, block_masks,
                    commuting_state, energies, loss_of, jdump, fbar_muon, fbar_ht, f2_ht)

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
os.makedirs(OUT, exist_ok=True)
rng = np.random.default_rng(20261122)
res = {"seed": 20261122, "checks": {}}
t0 = time.time()


def upd(dic, key, val):
    dic[key] = max(dic.get(key, 0.0), float(val))


def rel(x, y):
    return abs(x - y) / max(abs(x), abs(y), 1e-300)


# ---------------------------------------------------------------- N2 closed forms vs quadrature
n2 = {}
for p in (0.0, 0.125, 0.25, 0.5):
    for snr in (0.0, 0.05, 0.3, 1.0, 2.5, 6.0):
        kap = 0.7
        sig = snr * kap
        dens = lambda x: np.exp(-(x - sig) ** 2 / (2 * kap ** 2)) / (kap * np.sqrt(2 * np.pi))
        lo, hi = sig - 12 * kap, sig + 12 * kap
        I1 = integrate.quad(lambda x: np.sign(x) * abs(x) ** p * dens(x), lo, hi, points=[0.0], epsabs=1e-13, epsrel=1e-13, limit=400)[0]
        I2 = integrate.quad(lambda x: abs(x) ** (2 * p) * dens(x), lo, hi, points=[0.0], epsabs=1e-13, epsrel=1e-13, limit=400)[0]
        if p == 0.0:
            upd(n2, "muon_erf_abs_err", abs(I1 - fbar_muon(sig, kap)))
            upd(n2, "muon_second_moment_abs_err", abs(I2 - 1.0))
        else:
            upd(n2, "ht_fbar_abs_err", abs(I1 - fbar_ht(sig, kap, p)))
            upd(n2, "ht_f2_abs_err", abs(I2 - f2_ht(sig, kap, p)))
# linear response at small SNR:  fbar(sigma) ~ sigma * E[f_odd(zeta) zeta] / kappa^2
for p in (0.0, 0.125, 0.5):
    kap, sig = 1.3, 1e-4
    slope = (fbar_muon(sig, kap) if p == 0 else fbar_ht(sig, kap, p)) / sig
    stein = 2 ** ((p + 1) / 2) * special.gamma(p / 2 + 1) / np.sqrt(np.pi) * kap ** (p - 1)
    upd(n2, "linear_response_slope_relerr", rel(slope, stein))
res["checks"]["N2_smoothed_filter_closed_forms"] = n2

# ---------------------------------------------------------------- N1 per-realisation exactness
n1 = {}
d, n = 60, 80
k = 6
lam = make_spectrum(d, k, 10.0, rng)
D, B = block_masks(d, k)
U = rand_orth(d, rng)
a = np.exp(rng.normal(0, 0.7, d))
W, Q = commuting_state(U, a, n, rng)
C = U.T @ W
sig = lam * a
kap = 0.8 * np.median(sig) * np.exp(rng.normal(0, 0.3, d))       # heterogeneous noise levels
filts = {kk: FILTERS[kk] for kk in ("sgd", "muon", "ht0.125", "ht0.5", "ns5")}
filts["echelon_k"] = f_echelon(k)
for it in range(60):
    zeta = kap * rng.standard_normal(d)
    G = (U * lam) @ C + (U * zeta) @ Q
    for name, fvec in filts.items():
        eta = 0.3 * np.median(a) / max(np.median(fvec(np.abs(sig + zeta))), 1e-300)
        Cn = U.T @ (W - eta * apply_filter(G, fvec))
        fr = fvec(np.abs(sig + zeta))            # filter evaluated on the realised singular values
        alpha_new = a - eta * np.sign(sig + zeta) * fr
        upd(n1, name + ":signed_coordinate_relerr", np.abs(np.sum(Cn * Q, axis=1) - alpha_new).max() / a.max())
        Gram = Cn @ Cn.T
        upd(n1, name + ":offdiag_gram_rel", np.abs(Gram - np.diag(np.diag(Gram))).max() / np.diag(Gram).max())
        sDn, sBn = energies(lam, Cn, D)
        upd(n1, name + ":sD_next_relerr", rel(sDn, np.sum(lam[D] ** 2 * alpha_new[D] ** 2)))
        upd(n1, name + ":sB_next_relerr", rel(sBn, np.sum(lam[B] ** 2 * alpha_new[B] ** 2)))
res["checks"]["N1_codiagonal_noise_per_realisation"] = n1

# ---------------------------------------------------------------- N3 direct-SVD Monte Carlo
n3 = {"rows": []}
d, n, k = 40, 50, 5
lam = make_spectrum(d, k, 5.0, rng)
D, B = block_masks(d, k)
U = rand_orth(d, rng)
a = np.exp(rng.normal(0, 0.5, d))
W, Q = commuting_state(U, a, n, rng)
C = U.T @ W
sig = lam * a
A = (U * lam) @ U.T
L0 = loss_of(lam, C)
sD0, sB0 = energies(lam, C, D)
NMC = 3000
for kap_scale in (0.3, 3.0):
    kap = kap_scale * np.median(sig) * np.ones(d)
    for name, p in (("muon", 0.0), ("ht0.125", 0.125), ("ht0.5", 0.5)):
        fvec = FILTERS[name]
        fb = fbar_muon(sig, kap) if p == 0 else fbar_ht(sig, kap, p)
        f2 = np.ones(d) if p == 0 else f2_ht(sig, kap, p)
        eta = 0.5 * np.sum(sig * fb) / np.sum(lam * f2)
        pred = dict(sD=sD0 - 2 * eta * np.sum(lam[D] * sig[D] * fb[D]) + eta ** 2 * np.sum(lam[D] ** 2 * f2[D]),
                    sB=sB0 - 2 * eta * np.sum(lam[B] * sig[B] * fb[B]) + eta ** 2 * np.sum(lam[B] ** 2 * f2[B]))
        etaL = {key: 2 * np.sum(sig[S] * fb[S]) / np.sum(lam[S] * f2[S]) for key, S in (("D", D), ("B", B))}
        samples = np.zeros((NMC, 4))
        rs = np.random.default_rng(7)             # common random numbers across filters
        for it in range(NMC):
            zeta = kap * rs.standard_normal(d)
            F = apply_filter(A @ W + (U * zeta) @ Q, fvec)
            Phi = U.T @ F
            Cn = C - eta * Phi
            sDn, sBn = energies(lam, Cn, D)
            # projected loss changes at the predicted thresholds (expected value should vanish)
            dLD = loss_of(lam, C - etaL["D"] * np.where(D[:, None], Phi, 0.0)) - L0
            dLB = loss_of(lam, C - etaL["B"] * np.where(B[:, None], Phi, 0.0)) - L0
            samples[it] = (sDn, sBn, dLD, dLB)
        mean = samples.mean(axis=0)
        se = samples.std(axis=0, ddof=1) / np.sqrt(NMC)
        # when the noise never flips a sign the statistic is deterministic (se = rounding noise):
        # floor the standard error at 1e-9 of the natural scale so that z stays meaningful
        scale = np.array([sD0, sB0, L0, L0])
        z = (mean - np.array([pred["sD"], pred["sB"], 0.0, 0.0])) / np.maximum(se, 1e-9 * scale)
        n3["rows"].append(dict(filter=name, kappa_over_median_sigma=kap_scale, eta=eta, z_sD_sB_dLD_dLB=z,
                               relerr_sD=rel(mean[0], pred["sD"]), relerr_sB=rel(mean[1], pred["sB"]),
                               mean_dL_at_threshold_over_L0=[mean[2] / L0, mean[3] / L0],
                               etaLoss_D=etaL["D"], etaLoss_B=etaL["B"]))
n3["NMC"] = NMC
n3["max_abs_z"] = max(float(np.abs(r["z_sD_sB_dLD_dLB"]).max()) for r in n3["rows"])
res["checks"]["N3_codiagonal_noise_monte_carlo"] = n3

# ---------------------------------------------------------------- N4 i.i.d. Gaussian matrix noise
n4 = {"rows": []}
d, n, k = 20, 30, 3
lam = make_spectrum(d, k, 5.0, rng)
D, B = block_masks(d, k)
U = rand_orth(d, rng)
a = np.exp(rng.normal(0, 0.5, d))
Qt = rand_orth(n, rng)                 # full n x n orthogonal completion; Q = first d rows
C = a[:, None] * Qt[:d]
W = U @ C
sig = lam * a
Gc = (U * lam) @ C
NMC4 = 40000
for vs_scale in (0.1, 0.5):
    vs = vs_scale * np.median(sig)                       # entrywise noise std
    for name in ("muon", "ht0.125"):
        fvec = FILTERS[name]
        S1 = np.zeros((d, n))
        S2 = np.zeros((d, n))
        P1 = np.zeros((d, d))
        P2 = np.zeros((d, d))
        maxrow = 0.0
        rs = np.random.default_rng(11)
        for it in range(NMC4):
            G = Gc + vs * rs.standard_normal((d, n))
            Phi = U.T @ apply_filter(G, fvec)
            Y = Phi @ Qt.T                              # coordinates in the (u_i, q_j) frame
            S1 += Y
            S2 += Y ** 2
            PP = Phi @ Phi.T
            P1 += PP
            P2 += PP ** 2
            if name == "muon":
                maxrow = max(maxrow, np.abs(np.diag(PP) - 1).max())
        mY = S1 / NMC4
        seY = np.sqrt(np.maximum(S2 / NMC4 - mY ** 2, 1e-300) / NMC4)
        zY = mY / seY
        offmask = np.ones((d, n), bool)
        offmask[np.arange(d), np.arange(d)] = False
        mP = P1 / NMC4
        seP = np.sqrt(np.maximum(P2 / NMC4 - mP ** 2, 1e-300) / NMC4)
        offP = ~np.eye(d, dtype=bool)
        row = dict(filter=name, noise_std_over_median_sigma=vs_scale,
                   max_abs_z_offdiag_mean=float(np.abs(zY[offmask]).max()), n_offdiag=int(offmask.sum()),
                   max_abs_offdiag_mean=float(np.abs(mY[offmask]).max()),
                   min_diag_mean=float(np.diag(mY[:, :d]).min()), max_diag_mean=float(np.diag(mY[:, :d]).max()),
                   max_abs_offdiag_second_moment=float(np.abs(mP[offP]).max()),
                   max_abs_z_offdiag_second_moment=(float(np.abs((mP / seP)[offP]).max()) if name != "muon" else None),
                   muon_max_abs_rownorm2_minus_1=maxrow if name == "muon" else None)
        n4["rows"].append(row)
n4["NMC"] = NMC4
res["checks"]["N4_iid_noise_symmetry"] = n4

# ---------------------------------------------------------------- N5 wide limit
n5 = {"rows": []}
d, k = 10, 2
lam = make_spectrum(d, k, 4.0, rng)
U = rand_orth(d, rng)
a = np.exp(rng.normal(0, 0.6, d))
sig = lam * a
nu = np.median(sig)                    # varsigma^2 n = nu^2 held fixed
for n in (10, 40, 160, 640, 2560):
    Qt_rows = np.linalg.qr(rng.standard_normal((n, d)))[0].T      # d orthonormal rows in R^n
    C = a[:, None] * Qt_rows
    Gc = (U * lam) @ C
    vs = nu / np.sqrt(n)
    NMC5 = 3000 if n <= 640 else 1200
    for name, p in (("muon", 0.0), ("ht0.125", 0.125)):
        fvec = FILTERS[name]
        m_acc = np.zeros(d)
        v_acc = np.zeros(d)
        rs = np.random.default_rng(13)
        for it in range(NMC5):
            Phi = U.T @ apply_filter(Gc + vs * rs.standard_normal((d, n)), fvec)
            m_acc += np.sum(Phi * Qt_rows, axis=1)
            v_acc += np.sum(Phi ** 2, axis=1)
        m_i, v_i = m_acc / NMC5, v_acc / NMC5
        eff = np.sqrt(sig ** 2 + nu ** 2)
        m_pred = sig * eff ** (p - 1)
        v_pred = eff ** (2 * p)
        n5["rows"].append(dict(n=n, d=d, filter=name, max_relerr_m=float(np.max(np.abs(m_i - m_pred) / m_pred)),
                               max_relerr_v=float(np.max(np.abs(v_i - v_pred) / v_pred)), NMC=NMC5))
res["checks"]["N5_wide_limit"] = n5

res["runtime_sec"] = time.time() - t0
jdump(res, os.path.join(OUT, "m2_noise.json"))
print("N2", {k: "%.1e" % v for k, v in n2.items()})
print("N1", {k: "%.1e" % v for k, v in sorted(n1.items())})
print("N3 max|z| %.2f" % n3["max_abs_z"])
for r in n3["rows"]:
    print("   ", r["filter"], r["kappa_over_median_sigma"], "z", np.round(r["z_sD_sB_dLD_dLB"], 2), "relerr sD %.1e sB %.1e" % (r["relerr_sD"], r["relerr_sB"]), "etaL D %.3g B %.3g" % (r["etaLoss_D"], r["etaLoss_B"]))
for r in n4["rows"]:
    print("N4", r)
for r in n5["rows"]:
    print("N5", r)
print("runtime %.1fs" % res["runtime_sec"])
