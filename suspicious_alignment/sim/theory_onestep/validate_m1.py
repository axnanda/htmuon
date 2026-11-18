"""Model (M1): vector parameters, the gradient is a d x 1 matrix (Section 2 of the note).

 A1  noise-free: F(g) = gamma(||g||) g  (direct SVD of the d x 1 matrix);  one filtered step ==
     Deng's GD step with eta_eff = eta f(||Ax||)/||Ax||;  eta*_f = eta*_0 * ||Ax|| / f(||Ax||)
 A2  spherical Gaussian noise: exact formulas with three scalars (ell, beta2, A_perp) computed by
     2-D Gauss quadrature, validated against Monte Carlo of the actual update; Muon closed forms
 A3  projected updates with spherical noise (FP and PF)
 A4  anisotropic noise: quality of the mean-field replacement eta_eff = eta gamma(sqrt(s + Tr Sigma))
 A5  Deng's Theorem 8 / Corollary 9 (upper bound on eta*): numerical counterexample, and the
     corrected noise-free bounds 2/(lam_1+lam_{k+1}) <= eta*_0 <= 2/(lam_k+lam_d)
Output: results/m1.json
"""
import os
import sys
import time
import numpy as np
from scipy import special

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import (FILTERS, f_echelon, apply_filter, rand_orth, make_spectrum, block_masks, jdump)

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
os.makedirs(OUT, exist_ok=True)
rng = np.random.default_rng(20261121)
res = {"seed": 20261121, "checks": {}}
t0 = time.time()


def upd(dic, key, val):
    dic[key] = max(dic.get(key, 0.0), float(val))


def rel(x, y):
    return abs(x - y) / max(abs(x), abs(y), 1e-300)


SC = {"sgd": lambda t: t, "muon": lambda t: np.ones_like(t), "ht0.125": lambda t: t ** 0.125,
      "ht0.5": lambda t: t ** 0.5}


def moments(lam, c, D):
    out = {}
    for name, S in (("D", D), ("B", ~D)):
        for q in (2, 3, 4):
            out["m%d%s" % (q, name)] = np.sum(lam[S] ** q * c[S] ** 2)
        out["psi" + name] = np.sum(lam[S] ** 2)
        out["tr" + name] = np.sum(lam[S])
    return out


# ---------------------------------------------------------------- A1 noise-free
a1 = {"dichotomy_tests": 0, "dichotomy_violations": 0}
for d in (50, 100, 200):
    for trial in range(5):
        k = int(rng.integers(3, d // 5))
        m = [1.5, 3.0, 10.0, 30.0, 100.0][trial]
        lam = make_spectrum(d, k, m, rng)
        D, B = block_masks(d, k)
        U = rand_orth(d, rng)
        c = rng.standard_normal(d) * np.where(D, 10 ** rng.uniform(-1, 1), 1.0) * 10 ** rng.uniform(-1, 1)
        x = (U @ c)[:, None]
        g = (U * lam) @ (U.T @ x)
        mo = moments(lam, c, D)
        sD, sB = mo["m2D"], mo["m2B"]
        s = sD + sB
        th = sD / s
        p0 = sB * mo["m4D"] - sD * mo["m4B"]
        q0 = -2 * (sB * mo["m3D"] - sD * mo["m3B"])
        eta0 = -q0 / p0                       # Deng's noise-free critical step size
        # corrected noise-free bounds (A5)
        a1["dichotomy_tests"] += 1
        a1["dichotomy_violations"] += int(not (2 / (lam[0] + lam[k]) <= eta0 * (1 + 1e-12) and eta0 <= 2 / (lam[k - 1] + lam[-1]) * (1 + 1e-12)))
        filts = {kk: FILTERS[kk] for kk in ("sgd", "muon", "ht0.125", "ht0.5", "ns5")}
        filts["echelon0"] = f_echelon(0)
        filts["echelon3"] = f_echelon(3)
        for name, fvec in filts.items():
            F = apply_filter(g, fvec)                       # SVD of the d x 1 matrix
            gam = fvec(np.array([np.sqrt(s)]))[0] / np.sqrt(s)
            upd(a1, name + ":F_minus_gamma_g", np.abs(F - gam * g).max() / np.abs(F).max())
            if name.startswith("echelon"):
                upd(a1, "echelon_equals_muon_in_M1", np.abs(F - apply_filter(g, FILTERS["muon"])).max())
            eta_star_f = eta0 / gam
            for fac in (0.3, 0.97, 1.0, 1.03, 3.0):
                eta = fac * eta_star_f
                cn = (U.T @ (x - eta * F))[:, 0]
                upd(a1, name + ":c_next_vs_GD_with_eta_eff", np.abs(cn - (1 - eta * gam * lam) * c).max() / np.abs(c).max())
                thn = np.sum(lam[D] ** 2 * cn[D] ** 2) / np.sum(lam ** 2 * cn ** 2)
                if fac == 1.0:
                    upd(a1, name + ":dtheta_at_etastar_abs", abs(thn - th))
                else:
                    a1["dichotomy_tests"] += 1
                    a1["dichotomy_violations"] += int(np.sign(thn - th) != np.sign(fac - 1))
res["checks"]["A1_noise_free"] = a1


# ---------------------------------------------------------------- A2 spherical Gaussian noise
def sph_scalars(f, d, snr, sig, nq=120):
    """m1 = E[f(N) cos], A_par = E[f(N)^2 cos^2], A_perp = E[f(N)^2 sin^2]/(d-1) for
    g = mu + sig z, |mu|/sig = snr, by Gauss-Hermite (w ~ N(snr,1)) x Gauss-Laguerre (r^2 ~ chi2_{d-1})."""
    xh, wh = np.polynomial.hermite_e.hermegauss(nq)
    wh = wh / wh.sum()
    alpha = (d - 1) / 2.0 - 1.0
    tl, wl = special.roots_genlaguerre(nq, alpha)
    wl = wl / wl.sum()
    w = snr + xh[:, None]
    r2 = 2.0 * tl[None, :]
    R = np.sqrt(w ** 2 + r2)
    N = sig * R
    cos = w / R
    fw = f(N)
    W2 = wh[:, None] * wl[None, :]
    m1 = np.sum(W2 * fw * cos)
    Apar = np.sum(W2 * fw ** 2 * cos ** 2)
    Aperp = np.sum(W2 * fw ** 2 * (1 - cos ** 2)) / (d - 1)
    return m1, Apar, Aperp


a2 = {"rows": []}
NMC = 300000
CH = 50000
for d in (50, 200):
    k = d // 10
    lam = make_spectrum(d, k, 5.0, rng)
    D, B = block_masks(d, k)
    c = rng.standard_normal(d) * np.where(D, 0.6, 1.0)
    mo = moments(lam, c, D)
    mu = lam * c                      # gradient in eigen-coordinates (rotation invariance: U = I wlog)
    s = np.sum(mu ** 2)
    for snr in (0.3, 3.0, 30.0):
        sig = np.sqrt(s) / snr
        acc = {name: np.zeros(8) for name in SC}
        acc2 = {name: np.zeros(8) for name in SC}
        for ch in range(NMC // CH):
            g = mu[None, :] + sig * rng.standard_normal((CH, d))
            Nn = np.linalg.norm(g, axis=1)
            gD = g[:, D]
            gB = g[:, B]
            NnD = np.linalg.norm(gD, axis=1)
            NnB = np.linalg.norm(gB, axis=1)
            for name, f in SC.items():
                gam = f(Nn) / Nn
                # T^S = sum_S lam^2 c F,  V^S = sum_S lam^2 F^2,  projected: <Ax, P F>, <PF, A PF>
                stats = np.stack([
                    gam * (gD @ (lam[D] ** 2 * c[D])), gam * (gB @ (lam[B] ** 2 * c[B])),
                    gam ** 2 * (gD ** 2 @ lam[D] ** 2), gam ** 2 * (gB ** 2 @ lam[B] ** 2),
                    gam ** 2 * (gD ** 2 @ lam[D]), gam ** 2 * (gB ** 2 @ lam[B]),
                    # PF variant: filter the projected gradient
                    (f(NnD) / NnD) * (gD @ mu[D]), (f(NnD) / NnD) ** 2 * (gD ** 2 @ lam[D]),
                ], axis=1)
                acc[name] += stats.sum(axis=0)
                acc2[name] += (stats ** 2).sum(axis=0)
        for name, f in SC.items():
            mean = acc[name] / NMC
            se = np.sqrt(np.maximum(acc2[name] / NMC - mean ** 2, 0) / NMC)
            m1, Apar, Aperp = sph_scalars(f, d, snr, sig)
            ell = m1 / np.sqrt(s)
            b2 = (Apar - Aperp) / s
            pred = np.array([
                ell * mo["m3D"], ell * mo["m3B"],
                b2 * mo["m4D"] + Aperp * mo["psiD"], b2 * mo["m4B"] + Aperp * mo["psiB"],
                b2 * mo["m3D"] + Aperp * mo["trD"], b2 * mo["m3B"] + Aperp * mo["trB"],
                0.0, 0.0])
            # PF_D: spherical formulas inside the |D|-dimensional subspace
            sD = mo["m2D"]
            kD = int(D.sum())
            m1D, AparD, AperpD = sph_scalars(f, kD, np.sqrt(sD) / sig, sig)
            pred[6] = m1D * np.sqrt(sD)
            pred[7] = AperpD * mo["trD"] + (AparD - AperpD) * mo["m3D"] / sD
            z = (mean - pred) / np.where(se > 0, se, 1.0)
            row = dict(d=d, snr=snr, filter=name, ell=ell, beta2=b2, A_perp=Aperp,
                       max_abs_z=float(np.abs(z).max()), max_relerr=float(np.max(np.abs(mean - pred) / np.abs(pred))),
                       z=z, ell_positive=bool(ell > 0), beta2_nonneg=bool(b2 >= -1e-15))
            if name == "sgd":
                row["sgd_exact_check"] = max(abs(ell - 1), abs(b2 - 1), abs(Aperp / sig ** 2 - 1))
            if name == "muon":
                lamb = snr ** 2 / 2
                m1_cf = snr / np.sqrt(2) * np.exp(special.gammaln((d + 1) / 2) - special.gammaln(d / 2 + 1)) * special.hyp1f1(0.5, d / 2 + 1, -lamb)
                Apar_cf = 1 - (d - 1) / d * special.hyp1f1(1.0, d / 2 + 1, -lamb)
                row["muon_closed_form_relerr"] = max(rel(m1, m1_cf), rel(Apar, Apar_cf))
                # mean-field values: gamma(sqrt(s + sig^2 d))
                Nbar = np.sqrt(s + sig ** 2 * d)
                row["meanfield_relerr_ell_beta2_Aperp"] = [rel(ell, 1 / Nbar), rel(b2, 1 / Nbar ** 2), rel(Aperp, sig ** 2 / Nbar ** 2)]
            a2["rows"].append(row)
a2["NMC"] = NMC
a2["max_abs_z_overall"] = max(r["max_abs_z"] for r in a2["rows"])
a2["max_relerr_overall"] = max(r["max_relerr"] for r in a2["rows"])
a2["n_z_tests"] = 8 * len(a2["rows"])
a2["sgd_exact_check_max"] = max(r.get("sgd_exact_check", 0.0) for r in a2["rows"])
a2["muon_closed_form_relerr_max"] = max(r.get("muon_closed_form_relerr", 0.0) for r in a2["rows"])
a2["all_ell_positive"] = all(r["ell_positive"] for r in a2["rows"])
a2["all_beta2_nonneg"] = all(r["beta2_nonneg"] for r in a2["rows"])
res["checks"]["A2_A3_spherical_noise"] = a2

# ---------------------------------------------------------------- A4 anisotropic noise: mean field
a4 = {"rows": []}
NMC4 = 100000
for d in (50, 200, 800):
    k = d // 10
    lam = make_spectrum(d, k, 5.0, rng)
    D, B = block_masks(d, k)
    c = rng.standard_normal(d) * np.where(D, 0.6, 1.0)
    mu = lam * c
    s = np.sum(mu ** 2)
    mo = moments(lam, c, D)
    for shape in ("isotropic", "powerlaw_i^-1", "spiked_30pct"):
        if shape == "isotropic":
            kap2 = np.ones(d)
        elif shape == "powerlaw_i^-1":
            kap2 = 1.0 / np.arange(1, d + 1)
            kap2 = kap2[rng.permutation(d)]
        else:
            kap2 = np.ones(d)
            kap2[rng.integers(d)] = 0.3 / 0.7 * (d - 1)
        for ratio in (0.1, 1.0, 10.0):          # Tr Sigma / s
            kk2 = kap2 / kap2.sum() * ratio * s
            Nbar = np.sqrt(s * (1 + ratio))
            eps_conc = 2 * np.sqrt(kk2.max()) / Nbar
            acc = {name: np.zeros(4) for name in ("muon", "ht0.125")}
            for ch in range(NMC4 // 25000):
                g = mu[None, :] + np.sqrt(kk2)[None, :] * rng.standard_normal((25000, d))
                Nn = np.linalg.norm(g, axis=1)
                for name in acc:
                    gam = SC[name](Nn) / Nn
                    acc[name] += np.array([
                        np.sum(gam * (g[:, D] @ (lam[D] ** 2 * c[D]))), np.sum(gam * (g[:, B] @ (lam[B] ** 2 * c[B]))),
                        np.sum(gam ** 2 * (g[:, D] ** 2 @ lam[D] ** 2)), np.sum(gam ** 2 * (g[:, B] ** 2 @ lam[B] ** 2))])
            for name in acc:
                mean = acc[name] / NMC4
                gb = SC[name](np.array([Nbar]))[0] / Nbar
                pred = np.array([gb * mo["m3D"], gb * mo["m3B"],
                                 gb ** 2 * (mo["m4D"] + np.sum(lam[D] ** 2 * kk2[D])),
                                 gb ** 2 * (mo["m4B"] + np.sum(lam[B] ** 2 * kk2[B]))])
                a4["rows"].append(dict(d=d, noise=shape, trSigma_over_s=ratio, filter=name, eps_conc=eps_conc,
                                       relerr_TD_TB_VD_VB=np.abs(mean - pred) / np.abs(pred)))
res["checks"]["A4_meanfield_anisotropic"] = a4

# ---------------------------------------------------------------- A5 Deng Thm 8 / Cor 9
def deng_eta_star(lam, c, D, kap2):
    mo = moments(lam, c, D)
    eD, eB = np.sum(lam[D] ** 2 * kap2[D]), np.sum(lam[~D] ** 2 * kap2[~D])
    sD, sB = mo["m2D"], mo["m2B"]
    q = 2 * (sD * mo["m3B"] - sB * mo["m3D"])
    p = sB * (mo["m4D"] + eD) - sD * (mo["m4B"] + eB)
    return -q / p, sD / (sD + sB), eB / (eB + eD)


a5 = {"examples": []}
lam1, lamk, lamk1, lamd = 10.0, 1.0, 0.1, 0.1
for rep, c3 in ((1, (0.0, 1.0, 1.0)), (1, (0.01, 1.0, 1.0)), (100, (0.01, 1.0, 1.0))):
    lam = np.repeat(np.array([10.0, 1.0, 0.1]), rep)
    D = np.repeat(np.array([True, True, False]), rep)
    c = np.repeat(np.array(c3), rep)
    kap2 = np.full(lam.size, 1e-8)
    es, th, hyp = deng_eta_star(lam, c, D, kap2)
    eta_test = 0.5                                   # = 2.5 x (2 / lam_1)
    cn = (1 - eta_test * lam) * c                    # noise-free SGD step in eigen-coordinates
    a5["examples"].append(dict(
        d=int(lam.size), c_pattern=c3, kappa2=1e-8, theta=th, hypothesis_threshold_eB_over_eB_plus_eD=hyp,
        hypothesis_holds=bool(th >= hyp), eta_star=es,
        thm8_bound_main_text=(lam1 - lamd) / (lamk * lam1 - lamk1 * lamd),
        thm8_bound_appendix_restatement=2 * (lam1 - lamd) / (lamk * lam1 - lamk1 * lamd),
        cor9_bound_2_over_lam1=2 / lam1,
        corrected_lower_2_over_lam1_plus_lamk1=2 / (lam1 + lamk1),
        corrected_upper_2_over_lamk_plus_lamd=2 / (lamk + lamd),
        eta_test=eta_test,
        theta_after_noise_free_step=np.sum(lam[D] ** 2 * cn[D] ** 2) / np.sum(lam ** 2 * cn ** 2)))
# random search: the factor-2 (appendix) version of Thm 8 and the corrected bounds are never violated
viol_app, viol_corr, viol_main, viol_cor9, ntest = 0, 0, 0, 0, 0
for trial in range(4000):
    d = int(rng.integers(3, 12))
    k = int(rng.integers(1, d - 1))
    lam = make_spectrum(d, k, 1.0 + rng.exponential(2.0) + 1e-3, rng)
    D, B = block_masks(d, k)
    c = rng.standard_normal(d) * np.exp(rng.normal(0, 2.0, d))
    es, th, hyp = deng_eta_star(lam, c, D, np.zeros(d) + 1e-300)
    l1, lk, lk1, ld = lam[0], lam[k - 1], lam[k], lam[-1]
    ntest += 1
    viol_main += int(es > (l1 - ld) / (lk * l1 - lk1 * ld) * (1 + 1e-9))
    viol_app += int(es > 2 * (l1 - ld) / (lk * l1 - lk1 * ld) * (1 + 1e-9))
    viol_cor9 += int(es > 2 / l1 * (1 + 1e-9))
    viol_corr += int(not (2 / (l1 + lk1) <= es * (1 + 1e-9) and es <= 2 / (lk + ld) * (1 + 1e-9)))
a5["random_search_noise_free"] = dict(n=ntest, violations_thm8_main_text=viol_main, violations_thm8_appendix_factor2=viol_app,
                                      violations_cor9=viol_cor9, violations_corrected_bounds=viol_corr)
res["checks"]["A5_deng_thm8_counterexample"] = a5

res["runtime_sec"] = time.time() - t0
jdump(res, os.path.join(OUT, "m1.json"))
print("A1", {k: ("%.1e" % v if isinstance(v, float) else v) for k, v in sorted(a1.items())})
print("A2 max|z| %.2f over %d tests; max relerr %.2e; sgd exact %.1e; muon closed form %.1e; ell>0 %s beta2>=0 %s" % (
    a2["max_abs_z_overall"], a2["n_z_tests"], a2["max_relerr_overall"], a2["sgd_exact_check_max"],
    a2["muon_closed_form_relerr_max"], a2["all_ell_positive"], a2["all_beta2_nonneg"]))
for r in a2["rows"]:
    print("   d=%d snr=%g %-8s ell=%.4g beta2=%.4g Aperp=%.4g max|z|=%.2f relerr=%.1e %s" % (
        r["d"], r["snr"], r["filter"], r["ell"], r["beta2"], r["A_perp"], r["max_abs_z"], r["max_relerr"],
        ("MF relerr " + str(np.round(r["meanfield_relerr_ell_beta2_Aperp"], 4))) if "meanfield_relerr_ell_beta2_Aperp" in r else ""))
for r in a4["rows"]:
    print("A4 d=%d %-14s TrS/s=%g %-8s eps=%.3f relerr(T_D,T_B,V_D,V_B)=%s" % (
        r["d"], r["noise"], r["trSigma_over_s"], r["filter"], r["eps_conc"], np.array2string(np.asarray(r["relerr_TD_TB_VD_VB"]), precision=4)))
for ex in a5["examples"]:
    print("A5", ex)
print("A5 random search", a5["random_search_noise_free"])
print("runtime %.1fs" % res["runtime_sec"])
