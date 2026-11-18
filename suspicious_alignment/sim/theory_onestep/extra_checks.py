"""Formula-level checks of the corollaries of the note that are not covered by the other scripts.

 E1  "three alignments":  p = s V (theta_upd - theta),  q = -2 s T (vartheta_T - theta)   (any update)
 E2  (M1, spherical Gaussian noise)  theta <= theta_iso => p^f > 0 ;  theta >= theta*_f => p^f <= 0
 E3  (M2, co-diagonal noise) noise-dominated regime == Deng with (eta chi, kappa_eff^2)
 E4  noise-dominated critical alignment of the projected thresholds -> tr_D(A) / tr(A)
 E5  Muon, two-level state above theta_iso: the sign of q flips from > 0 (signal-dominated) to < 0
     (noise-dominated) as the noise level grows -- verified with direct SVDs + Monte Carlo
 E6  Echelon(r): head/tail ordering criterion  nu_j / nu_i = (lam_j / lam_i) / (sigma_j / tau)
Output: results/extra.json
"""
import os
import sys
import time
import numpy as np
from scipy import special

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import (FILTERS, f_echelon, f_muon, apply_filter, rand_orth, make_spectrum, block_masks,
                    commuting_state, commuting_coeffs, echelon_tau, energies, jdump, fbar_muon, fbar_ht,
                    f2_ht)

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
rng = np.random.default_rng(20261124)
res = {"seed": 20261124}
t0 = time.time()


def rel(x, y):
    return abs(x - y) / max(abs(x), abs(y), 1e-300)


# ---------------------------------------------------------------- E1
e1 = 0.0
for trial in range(200):
    d, n = 30, 40
    k = 4
    lam = make_spectrum(d, k, 3.0, rng)
    D, B = block_masks(d, k)
    C = rng.standard_normal((d, n))
    Phi = rng.standard_normal((d, n))            # ANY update direction
    s = {key: np.sum(lam[S] ** 2 * np.sum(C[S] ** 2, 1)) for key, S in (("D", D), ("B", B))}
    T = {key: np.sum(lam[S] ** 2 * np.sum(C[S] * Phi[S], 1)) for key, S in (("D", D), ("B", B))}
    V = {key: np.sum(lam[S] ** 2 * np.sum(Phi[S] ** 2, 1)) for key, S in (("D", D), ("B", B))}
    p = s["B"] * V["D"] - s["D"] * V["B"]
    q = 2 * (s["D"] * T["B"] - s["B"] * T["D"])
    st, Vt, Tt = s["D"] + s["B"], V["D"] + V["B"], T["D"] + T["B"]
    th = s["D"] / st
    e1 = max(e1, abs(p - st * Vt * (V["D"] / Vt - th)) / (st * Vt), abs(q + 2 * st * Tt * (T["D"] / Tt - th)) / (st * abs(Tt)))
    eta = rng.uniform(0.01, 2.0)
    Cn = C - eta * Phi
    sDn, sBn = energies(lam, Cn, D)
    e1 = max(e1, abs((sDn / (sDn + sBn) - th) - eta * (p * eta + q) / (st * (sDn + sBn))))
res["E1_three_alignments_max_err"] = e1


# ---------------------------------------------------------------- E2 (uses the quadrature of validate_m1)
def sph_scalars(f, d, snr, sig, nq=120):
    xh, wh = np.polynomial.hermite_e.hermegauss(nq)
    wh = wh / wh.sum()
    tl, wl = special.roots_genlaguerre(nq, (d - 1) / 2.0 - 1.0)
    wl = wl / wl.sum()
    w = snr + xh[:, None]
    R = np.sqrt(w ** 2 + 2.0 * tl[None, :])
    cos = w / R
    fw = f(sig * R)
    W2 = wh[:, None] * wl[None, :]
    return np.sum(W2 * fw * cos), np.sum(W2 * fw ** 2 * cos ** 2), np.sum(W2 * fw ** 2 * (1 - cos ** 2)) / (d - 1)


e2 = dict(low_tests=0, low_violations=0, high_tests=0, high_violations=0, q_tests=0, q_violations=0)
SC = {"muon": lambda t: np.ones_like(t), "ht0.125": lambda t: t ** 0.125, "ht0.5": lambda t: t ** 0.5}
for trial in range(120):
    d = int(rng.choice([40, 100]))
    k = int(rng.integers(3, d // 4))
    m = float(rng.choice([1.5, 3.0, 10.0]))
    lam = make_spectrum(d, k, m, rng)
    D, B = block_masks(d, k)
    psiD, psiB = np.sum(lam[D] ** 2), np.sum(lam[B] ** 2)
    th_iso = psiD / (psiD + psiB)
    c = rng.standard_normal(d) * np.where(D, 10 ** rng.uniform(-2.5, 1.5), 1.0)
    mom = lambda S, q: np.sum(lam[S] ** q * c[S] ** 2)
    sD, sB = mom(D, 2), mom(B, 2)
    s = sD + sB
    th = sD / s
    p0 = sB * mom(D, 4) - sD * mom(B, 4)
    q0 = -2 * (sB * mom(D, 3) - sD * mom(B, 3))
    snr = 10 ** rng.uniform(-1, 1.5)
    sig = np.sqrt(s) / snr
    name = list(SC)[trial % 3]
    m1, Apar, Aperp = sph_scalars(SC[name], d, snr, sig)
    ell, b2 = m1 / np.sqrt(s), (Apar - Aperp) / s
    pf = b2 * p0 + Aperp * (sB * psiD - sD * psiB)
    qf = ell * q0
    e2["q_tests"] += 1
    e2["q_violations"] += int(not qf < 0)
    if th <= th_iso:
        e2["low_tests"] += 1
        e2["low_violations"] += int(not pf > 0)
    # Deng's Theorem-4 quadratic with (s_min, s_max, s_t) -> (A_perp, A_perp, beta2 s_t)
    a_aux, h_aux, m_aux = Aperp * psiB, Aperp * psiD, b2 * s * (lam[0] ** 2 - lam[-1] ** 2)
    bq = a_aux - m_aux - h_aux
    r0 = (-bq + np.sqrt(bq ** 2 + 4 * a_aux * h_aux)) / (2 * a_aux)
    th_star = r0 / (1 + r0)
    if th >= th_star:
        e2["high_tests"] += 1
        e2["high_violations"] += int(not pf <= 1e-12 * abs(b2 * p0))
res["E2_M1_spherical_thresholds"] = e2

# ---------------------------------------------------------------- E3 / E4
e3 = {}
d, k = 80, 8
lam = make_spectrum(d, k, 5.0, rng)
D, B = block_masks(d, k)
a = np.exp(rng.normal(0, 0.5, d))
sig = lam * a
mom = lambda S, q: np.sum(lam[S] ** q * a[S] ** 2)
for name, p in (("muon", 0.0), ("ht0.125", 0.125), ("ht0.5", 0.5)):
    for ratio in (1e-1, 1e-2, 1e-3):           # max sigma_i / kappa
        kap = sig.max() / ratio
        fb = fbar_muon(sig, kap) if p == 0 else fbar_ht(sig, kap, p)
        f2 = np.ones(d) if p == 0 else f2_ht(sig, kap, p)
        chi = 2 ** ((p + 1) / 2) * special.gamma(p / 2 + 1) / np.sqrt(np.pi) * kap ** (p - 1)
        f20 = kap ** (2 * p) * 2 ** p * special.gamma(p + 0.5) / np.sqrt(np.pi)
        kap_eff2 = f20 / chi ** 2
        ref = kap ** 2 * np.sqrt(np.pi) * special.gamma(p + 0.5) / (2 * special.gamma(p / 2 + 1) ** 2)
        e3["%s:kappa_eff_formula_relerr" % name] = max(e3.get("%s:kappa_eff_formula_relerr" % name, 0), rel(kap_eff2, ref))
        worst = 0.0
        for S in (D, B):
            lin_exact = np.sum(lam[S] * sig[S] * fb[S])
            quad_exact = np.sum(lam[S] ** 2 * f2[S])
            lin_deng = chi * mom(S, 3)
            quad_deng = chi ** 2 * (mom(S, 4) + kap_eff2 * np.sum(lam[S] ** 2))
            worst = max(worst, rel(lin_exact, lin_deng), rel(quad_exact, quad_deng))
        e3["%s:snr_max=%g:relerr_vs_renormalised_Deng" % (name, ratio)] = worst
        # E4: projected thresholds; ordering flips at theta = tr_D / tr in the noise-dominated limit
        etaD = 2 * np.sum(sig[D] * fb[D]) / np.sum(lam[D] * f2[D])
        etaB = 2 * np.sum(sig[B] * fb[B]) / np.sum(lam[B] * f2[B])
        th = mom(D, 2) / (mom(D, 2) + mom(B, 2))
        th_tr = lam[D].sum() / lam.sum()
        # predicted ratio in the limit: (s^D / tr_D) / (s^B / tr_B)
        e3["%s:snr_max=%g:ratio_etaD_over_etaB_relerr_vs_trace_formula" % (name, ratio)] = rel(etaD / etaB, (mom(D, 2) / lam[D].sum()) / (mom(B, 2) / lam[B].sum()))
res["E3_E4_noise_dominated_regime"] = e3

# ---------------------------------------------------------------- E5 direct SVD + Monte Carlo
e5 = {"rows": []}
d, n, k, m = 40, 50, 4, 5.0
lam = make_spectrum(d, k, m, rng, kind="twolevel")
D, B = block_masks(d, k)
psiD, psiB = np.sum(lam[D] ** 2), np.sum(lam[B] ** 2)
th_iso = psiD / (psiD + psiB)
U = rand_orth(d, rng)
a = np.where(D, 2.0, 1.0)                       # a_D > a_B  => theta > theta_iso
W, Q = commuting_state(U, a, n, rng)
C = U.T @ W
sig = lam * a
sD, sB = energies(lam, C, D)
th = sD / (sD + sB)
NMC = 1500
for kap_rel in (0.01, 0.3, 1.0, 3.0, 10.0, 100.0):      # kappa / sigma_B
    kap = kap_rel * sig[-1]
    fb = fbar_muon(sig, kap)
    q_formula = 2 * (sD * np.sum(lam[B] * sig[B] * fb[B]) - sB * np.sum(lam[D] * sig[D] * fb[D]))
    p_formula = sB * psiD - sD * psiB
    rs = np.random.default_rng(3)
    qs = np.zeros(NMC)
    for it in range(NMC):
        zeta = kap * rs.standard_normal(d)
        Phi = U.T @ apply_filter((U * lam) @ C + (U * zeta) @ Q, f_muon())
        TD = np.sum(lam[D] ** 2 * np.sum(C[D] * Phi[D], 1))
        TB = np.sum(lam[B] ** 2 * np.sum(C[B] * Phi[B], 1))
        qs[it] = 2 * (sD * TB - sB * TD)
    se = max(qs.std(ddof=1) / np.sqrt(NMC), 1e-9 * abs(q_formula))
    e5["rows"].append(dict(kappa_over_sigmaB=kap_rel, theta=th, theta_iso=th_iso, p=p_formula, q_formula=q_formula,
                           q_mc=qs.mean(), z=(qs.mean() - q_formula) / se,
                           regime=("q>0: increases for small eta" if q_formula > 0 else "q<0: decreases for every eta (p<0)")))
res["E5_noise_restores_deng_sign_muon"] = e5

# ---------------------------------------------------------------- E6
e6 = 0.0
for trial in range(100):
    d = 60
    k = 6
    lam = make_spectrum(d, k, float(rng.choice([2.0, 10.0])), rng)
    D, B = block_masks(d, k)
    a = np.exp(rng.normal(0, 0.8, d))
    r = int(rng.integers(1, 30))
    sig = lam * a
    tau = echelon_tau(sig, r)
    co = commuting_coeffs(lam, a, D, f_echelon(r))
    head = sig > tau
    nu_pred = np.where(head, 1.0 / a, lam / tau)
    e6 = max(e6, np.abs(co["nu"] - nu_pred).max() / nu_pred.max())
    j, i = np.flatnonzero(head)[0], np.flatnonzero(~head)[-1]
    e6 = max(e6, rel(co["nu"][j] / co["nu"][i], (lam[j] / lam[i]) / (sig[j] / tau)))
res["E6_echelon_effective_curvature_max_err"] = e6

res["runtime_sec"] = time.time() - t0
jdump(res, os.path.join(OUT, "extra.json"))
print("E1", e1)
print("E2", e2)
for kk, vv in e3.items():
    print("E3/4 %-70s %.2e" % (kk, vv))
for r in e5["rows"]:
    print("E5", {a: (round(float(b), 5) if not isinstance(b, str) else b) for a, b in r.items()})
print("E6", e6)
print("runtime %.1fs" % res["runtime_sec"])
