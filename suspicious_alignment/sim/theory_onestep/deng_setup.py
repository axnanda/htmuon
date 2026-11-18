"""One-step quantities of the note evaluated in the setup of Deng et al.'s own simulation script
(quad_sim.py: d = 500, k = 50, eta = 0.003, isotropic noise sigma = 0.5, x_0 ~ N(0, I), dominant
eigenvalues linspace(100, 80, k), bulk eigenvalues linspace(7, 1, d-k) rescaled so that the largest
is 80/(m + 0.1)), plus one check that is not covered by the other scripts.

 S1  SGD reference numbers at x_0: theta_0, eta*_Deng(x_0), the noise-free eta*_0 with the bounds
     2/(lam_1+lam_{k+1}) <= eta*_0 <= 2/(lam_k+lam_d), Deng's Theorem-7 lower bound, 2/lam_1,
     g_gap, theta_iso, theta*_Deng(x_0), the projected loss thresholds
 S2  model (M1) + spherical Gaussian noise (Theorem 2.3): (ell, beta2, A_perp) by quadrature,
     eta*_f = -q^f/p^f, mean-field value eta*_Deng / gamma(sqrt(s + sigma^2 d)), and a direct Monte
     Carlo of E[f(eta)] and of E[theta_+ - theta] at eta = eta*_f * {0.5, 1, 2}
 S3  model (M2), d = 500, n in {600, 3000}, generic states (Gaussian rows; Gaussian rows with
     log-normal row norms), noise-free: exact (direct SVD) p, q, eta*, loss thresholds vs the
     commuting row-norm formulas; Muon pinning
     (S2 is also evaluated at 0.05 x_0 and 0.01 x_0 for m = 10: later, noisier stages)
 S4  Stein identity behind the accuracy of the mean-field replacement (Remark 2.6):
     E[gamma(N) g] = E[gamma(N)] mu - (1-p) Sigma E[N^(p-3) g]   (anisotropic Gaussian noise)
Output: results/deng_setup.json
"""
import os
import sys
import time
import numpy as np
from scipy import special

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import FILTERS, f_echelon, block_masks, commuting_coeffs, jdump

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
os.makedirs(OUT, exist_ok=True)
t0 = time.time()
res = {"seed": 42}
D_, K_, ETA, SIG = 500, 50, 0.003, 0.5


def deng_spectrum(m, d=D_, k=K_):
    large = np.linspace(100, 80, k)
    small = np.linspace(7, 1, d - k)
    small = small * ((large[-1] / (m + 0.1)) / small[0])
    return np.concatenate([large, small])


def sph_scalars(f, d, snr, sig, nq=160, nr=1200):
    """m1 = E[f(N) cos], A_par = E[f(N)^2 cos^2], A_perp = E[f(N)^2 sin^2]/(d-1) for g = mu + sig z,
    |mu|/sig = snr.  w ~ N(snr, 1) by Gauss-Hermite; r^2 ~ chi2_{d-1} by Gauss-Legendre on
    [max(0, nu - 14 sqrt(2 nu)), nu + 14 sqrt(2 nu)] with the log-density (stable for large d)."""
    xh, wh = np.polynomial.hermite_e.hermegauss(nq)
    wh = wh / wh.sum()
    nu = d - 1
    lo, hi = max(1e-12, nu - 14 * np.sqrt(2 * nu)), nu + 14 * np.sqrt(2 * nu)
    xl, wl = np.polynomial.legendre.leggauss(nr)
    t = 0.5 * (hi - lo) * xl + 0.5 * (hi + lo)
    logpdf = (nu / 2 - 1) * np.log(t) - t / 2 - (nu / 2) * np.log(2.0) - special.gammaln(nu / 2)
    wl = 0.5 * (hi - lo) * wl * np.exp(logpdf)
    assert abs(wl.sum() - 1) < 1e-10, wl.sum()
    wl = wl / wl.sum()
    w = snr + xh[:, None]
    R = np.sqrt(w ** 2 + t[None, :])
    cos = w / R
    fw = f(sig * R)
    W2 = wh[:, None] * wl[None, :]
    return np.sum(W2 * fw * cos), np.sum(W2 * fw ** 2 * cos ** 2), np.sum(W2 * fw ** 2 * (1 - cos ** 2)) / (d - 1)


SC = {"sgd": (lambda t: t, 1.0), "muon": (lambda t: np.ones_like(t), 0.0), "ht0.125": (lambda t: t ** 0.125, 0.125)}
D, B = block_masks(D_, K_)
rows1, rows2, rows3 = [], [], []
for m, scale in ((2.0, 1.0), (10.0, 1.0), (50.0, 1.0), (10.0, 0.05), (10.0, 0.01)):
    lam = deng_spectrum(m)
    rng = np.random.default_rng(42)
    c = scale * rng.standard_normal(D_)              # x_0 ~ N(0, I) in eigen-coordinates (times scale)
    mom = lambda S, q: np.sum(lam[S] ** q * c[S] ** 2)
    sD, sB = mom(D, 2), mom(B, 2)
    s = sD + sB
    th = sD / s
    psiD, psiB = np.sum(lam[D] ** 2), np.sum(lam[B] ** 2)
    trD, trB = lam[D].sum(), lam[B].sum()
    q0 = 2 * (sD * mom(B, 3) - sB * mom(D, 3))
    p0 = sB * mom(D, 4) - sD * mom(B, 4)
    pN = p0 + SIG ** 2 * (sB * psiD - sD * psiB)
    rho = K_ / (D_ - K_)
    l1, lk, lk1, ld = lam[0], lam[K_ - 1], lam[K_], lam[-1]
    a_aux, h_aux, m_aux = SIG ** 2 * psiB, SIG ** 2 * psiD, s * (l1 ** 2 - ld ** 2)
    bq = a_aux - m_aux - h_aux
    r0 = (-bq + np.sqrt(bq ** 2 + 4 * a_aux * h_aux)) / (2 * a_aux)
    rows1.append(dict(
        m_nominal=m, scale=scale, m_actual=lk / lk1, theta0=th, s=s, grad_norm=np.sqrt(s),
        eta_star_deng=-q0 / pN, eta_star_noise_free=-q0 / p0,
        lower_2_over_lam1_plus_lamk1=2 / (l1 + lk1), upper_2_over_lamk_plus_lamd=2 / (lk + ld),
        deng_thm7_lower=2 * (lk - lk1) / ((l1 ** 2 - ld ** 2) + SIG ** 2 * psiD / (s * th)),
        two_over_lam1=2 / l1, eta_used=ETA,
        g_gap=1 / (1 + (1 / rho) * (lk1 / lk) ** 2), theta_iso=psiD / (psiD + psiB), theta_star_deng=r0 / (1 + r0),
        theta_trace=trD / (trD + trB),
        etaD_loss_sgd=2 * sD / (mom(D, 3) + SIG ** 2 * trD), etaB_loss_sgd=2 * sB / (mom(B, 3) + SIG ** 2 * trB)))
    # ---------------- S2: model (M1) with spherical noise, direct Monte Carlo
    snr = np.sqrt(s) / SIG
    mu = lam * c
    for name, (f, pdeg) in SC.items():
        m1, Apar, Aperp = sph_scalars(f, D_, snr, SIG)
        ell, b2 = m1 / np.sqrt(s), (Apar - Aperp) / s
        qf = ell * q0
        pf = b2 * p0 + Aperp * (sB * psiD - sD * psiB)
        es = -qf / pf
        Nbar = np.sqrt(s + SIG ** 2 * D_)
        gam_bar = f(np.array([Nbar]))[0] / Nbar
        es_mf = (-q0 / pN) / gam_bar
        # projected thresholds (filter-then-project), Theorem 5.7(b)
        etaD = 2 * ell * sD / (b2 * mom(D, 3) + Aperp * trD)
        etaB = 2 * ell * sB / (b2 * mom(B, 3) + Aperp * trB)
        NMC, CH = 40000, 10000
        facs = (0.5, 1.0, 2.0)
        accf = np.zeros((len(facs), 2))
        acct = np.zeros((len(facs), 2))
        accL = np.zeros((2, 2))
        rs = np.random.default_rng(4242)
        for ch in range(NMC // CH):
            g = mu[None, :] + SIG * rs.standard_normal((CH, D_))
            Nn = np.linalg.norm(g, axis=1)
            Fg = (f(Nn) / Nn)[:, None] * g                      # F(g) for the d x 1 matrix g
            for j, fac in enumerate(facs):
                cn = c[None, :] - fac * es * Fg
                sDn = (cn[:, D] ** 2) @ lam[D] ** 2
                sBn = (cn[:, B] ** 2) @ lam[B] ** 2
                fv = sB * sDn - sBn * sD
                dth = sDn / (sDn + sBn) - th
                accf[j] += (fv.sum(), (fv ** 2).sum())
                acct[j] += (dth.sum(), (dth ** 2).sum())
            for j, (S, e_) in enumerate(((D, etaD), (B, etaB))):
                dL = -e_ * (Fg[:, S] @ (lam[S] * c[S])) + 0.5 * e_ ** 2 * ((Fg[:, S] ** 2) @ lam[S])
                accL[j] += (dL.sum(), (dL ** 2).sum())
        meanf = accf[:, 0] / NMC
        sef = np.sqrt(accf[:, 1] / NMC - meanf ** 2) / np.sqrt(NMC)
        meant = acct[:, 0] / NMC
        set_ = np.sqrt(acct[:, 1] / NMC - meant ** 2) / np.sqrt(NMC)
        meanL = accL[:, 0] / NMC
        seL = np.sqrt(accL[:, 1] / NMC - meanL ** 2) / np.sqrt(NMC)
        predf = np.array([pf * (fac * es) ** 2 + qf * (fac * es) for fac in facs])
        L0 = 0.5 * np.sum(lam * c ** 2)
        rows2.append(dict(m=m, scale=scale, filter=name, snr=snr, snr_total=np.sqrt(s) / (SIG * np.sqrt(D_)), theta=th, ell=ell, beta2=b2, A_perp=Aperp, p_f=pf, q_f=qf,
                          eta_star_f=es, eta_star_meanfield=es_mf, relerr_meanfield=abs(es - es_mf) / es,
                          eta_eff_meanfield_at_eta=ETA * gam_bar, eta_ratio_eta_over_eta_star_f=ETA / es,
                          mc_E_f_over_scale=meanf / (sD * sB), pred_E_f_over_scale=predf / (sD * sB),
                          z_E_f=(meanf - predf) / sef, mc_E_dtheta=meant, se_E_dtheta=set_,
                          etaD_loss_FP=etaD, etaB_loss_FP=etaB, mc_E_dL_at_thresholds_over_L0=meanL / L0,
                          z_E_dL_at_thresholds=meanL / seL, NMC=NMC))
    # ---------------- S3: model (M2), d = 500, generic states, noise-free, direct SVD
    if scale != 1.0:
        continue
    for n in (600, 3000):
        for kind in ("gaussian", "heterogeneous"):
            rs = np.random.default_rng(4243 + n)
            C = rs.standard_normal((D_, n)) / np.sqrt(n)             # rows of norm ~ 1 (isotropic state)
            if kind == "heterogeneous":
                C = np.exp(rs.normal(0, 0.5, D_))[:, None] * C         # log-normal row norms
            Gm = lam[:, None] * C                                    # eigen-coordinates (U = I wlog)
            Um, Sm, Vtm = np.linalg.svd(Gm, full_matrices=False)
            a = np.linalg.norm(C, axis=1)
            e = lam ** 2 * a ** 2
            sD2, sB2 = e[D].sum(), e[B].sum()
            th2 = sD2 / (sD2 + sB2)
            filts = {"sgd": FILTERS["sgd"], "muon": FILTERS["muon"], "ht0.125": FILTERS["ht0.125"], "echelon_k": f_echelon(K_)}
            for name, fvec in filts.items():
                Phi = (Um * fvec(Sm)) @ Vtm
                ex = {}
                for key, S in (("D", D), ("B", B)):
                    ex["T" + key] = np.sum(lam[S] ** 2 * np.sum(C[S] * Phi[S], axis=1))
                    ex["V" + key] = np.sum(lam[S] ** 2 * np.sum(Phi[S] ** 2, axis=1))
                    ex["N" + key] = np.sum(lam[S] * np.sum(C[S] * Phi[S], axis=1))
                    ex["R" + key] = np.sum(lam[S] * np.sum(Phi[S] ** 2, axis=1))
                q = 2 * (sD2 * ex["TB"] - sB2 * ex["TD"])
                p = sB2 * ex["VD"] - sD2 * ex["VB"]
                co = commuting_coeffs(lam, a, D, fvec)
                scl = (sD2 + sB2) ** 2
                row = dict(m=m, filter=name, n=n, state=kind, theta=th2, theta_iso=psiD / (psiD + psiB),
                           q_exact_over_s2=q / scl, p_exact_over_s2=p / scl,
                           q_rownorm_over_s2=co["q"] / scl, p_rownorm_over_s2=co["p"] / scl,
                           eta_star_exact=(-q / p if -q / p > 0 else None),
                           eta_star_rownorm=(-co["q"] / co["p"] if -co["q"] / co["p"] > 0 else None),
                           etaD_loss_exact=2 * ex["ND"] / ex["RD"], etaB_loss_exact=2 * ex["NB"] / ex["RB"],
                           etaD_loss_rownorm=2 * co["ND"] / co["RD"], etaB_loss_rownorm=2 * co["NB"] / co["RB"],
                           window_ratio_exact=(ex["NB"] / ex["RB"]) / (ex["ND"] / ex["RD"]),
                           window_ratio_rownorm=(co["NB"] / co["RB"]) / (co["ND"] / co["RD"]))
                if name == "muon":
                    row["pinning_relerr_p"] = abs(p - (sD2 + sB2) * (psiD + psiB) * (psiD / (psiD + psiB) - th2)) / ((sD2 + sB2) * (psiD + psiB))
                # sign of the one-step alignment change on the actual matrices == sign(p eta + q)
                eta_ref = 2 * (ex["ND"] + ex["NB"]) / (ex["RD"] + ex["RB"])       # loss threshold of the full step
                ok = True
                for fac in (0.01, 0.1, 0.5, 1.0):
                    Cn = C - fac * eta_ref * Phi
                    en = lam ** 2 * np.sum(Cn ** 2, axis=1)
                    ok = ok and (np.sign(en[D].sum() / en.sum() - th2) == np.sign(p * fac * eta_ref + q))
                row["sign_identity_ok"] = bool(ok)
                row["eta_full_loss_threshold"] = eta_ref
                rows3.append(row)
res["S1_sgd_reference"] = rows1
res["S2_M1_spherical_noise"] = rows2
res["S3_M2_generic_state"] = rows3

# ---------------- S4: Stein identity, anisotropic noise
rng = np.random.default_rng(7)
d = 60
lam = np.concatenate([np.linspace(10, 8, 6), np.linspace(1, 0.2, d - 6)])
c = rng.standard_normal(d)
mu = lam * c
s = np.sum(mu ** 2)
kap2 = 1.0 / np.arange(1, d + 1)
kap2 = kap2[rng.permutation(d)]
kap2 = kap2 / kap2.sum() * 2.0 * s                         # Tr Sigma = 2 s
rows4 = []
NMC, CH = 600000, 50000
tests = [mu / np.linalg.norm(mu), np.sqrt(kap2) / np.linalg.norm(np.sqrt(kap2)), np.eye(d)[int(np.argmax(kap2))],
         rng.standard_normal(d) / np.sqrt(d)]
for pdeg in (0.0, 0.125, 0.5):
    acc = np.zeros((len(tests), 4))
    rs = np.random.default_rng(99)
    for ch in range(NMC // CH):
        g = mu[None, :] + np.sqrt(kap2)[None, :] * rs.standard_normal((CH, d))
        Nn = np.linalg.norm(g, axis=1)
        gam = Nn ** (pdeg - 1)
        for j, v in enumerate(tests):
            lhs = gam * (g @ v)                                               # <v, F(g)>
            rhs = gam * (mu @ v) - (1 - pdeg) * Nn ** (pdeg - 3) * (g @ (kap2 * v))
            diff = lhs - rhs
            acc[j] += (lhs.sum(), diff.sum(), (diff ** 2).sum(), (gam * (mu @ v)).sum())
    for j in range(len(tests)):
        lhs, dm = acc[j, 0] / NMC, acc[j, 1] / NMC
        se = np.sqrt(acc[j, 2] / NMC - dm ** 2) / np.sqrt(NMC)
        Nbar = np.sqrt(s + kap2.sum())
        rows4.append(dict(p=pdeg, test_vector=j, E_vF=lhs, stein_residual=dm, z=dm / se,
                          naive_parallel_part=acc[j, 3] / NMC, meanfield=Nbar ** (pdeg - 1) * (mu @ tests[j]),
                          relerr_meanfield=abs(lhs - Nbar ** (pdeg - 1) * (mu @ tests[j])) / abs(lhs),
                          relerr_meanfield_corrected=abs(lhs - Nbar ** (pdeg - 1) * (mu @ tests[j]) + (1 - pdeg) * Nbar ** (pdeg - 3) * (mu @ (kap2 * tests[j]))) / abs(lhs)))
res["S4_stein_identity"] = dict(d=d, trSigma_over_s=2.0, NMC=NMC, rows=rows4,
                                max_abs_z=max(abs(r["z"]) for r in rows4))
res["runtime_sec"] = time.time() - t0
jdump(res, os.path.join(OUT, "deng_setup.json"))

for r in rows1:
    print("S1", {k: (round(float(v), 6) if isinstance(v, (float, np.floating)) else v) for k, v in r.items()})
for r in rows2:
    print("S2 m=%g scale=%g theta=%.4f snr_tot=%.2f %-8s snr=%.1f ell=%.4g beta2=%.4g Aperp=%.4g eta*_f=%.5g (mean-field %.5g, relerr %.1e) eta/eta*_f=%.3g" % (
        r["m"], r["scale"], r["theta"], r["snr_total"], r["filter"], r["snr"], r["ell"], r["beta2"], r["A_perp"], r["eta_star_f"], r["eta_star_meanfield"], r["relerr_meanfield"], r["eta_ratio_eta_over_eta_star_f"]))
    print("      E f/(sD sB): MC %s pred %s z %s" % (np.array2string(r["mc_E_f_over_scale"], precision=4), np.array2string(r["pred_E_f_over_scale"], precision=4), np.round(r["z_E_f"], 2)))
    print("      E dtheta at eta*_f x (0.5,1,2): %s  (se %s)" % (np.array2string(r["mc_E_dtheta"], precision=3), np.array2string(r["se_E_dtheta"], precision=1)))
    print("      FP loss thresholds D %.5g B %.5g ; E dL/L0 at thresholds %s z %s" % (r["etaD_loss_FP"], r["etaB_loss_FP"], np.array2string(r["mc_E_dL_at_thresholds_over_L0"], precision=2), np.round(r["z_E_dL_at_thresholds"], 2)))
for r in rows3:
    print("S3", {k: (float("%.4g" % v) if isinstance(v, (float, np.floating)) else v) for k, v in r.items()})
for r in rows4:
    print("S4 p=%.3f v%d  E<v,F>=%.5g  Stein residual %.2e (z=%.2f)  mean-field relerr %.2e -> corrected %.2e" % (
        r["p"], r["test_vector"], r["E_vF"], r["stein_residual"], r["z"], r["relerr_meanfield"], r["relerr_meanfield_corrected"]))
print("runtime %.1fs" % res["runtime_sec"])
