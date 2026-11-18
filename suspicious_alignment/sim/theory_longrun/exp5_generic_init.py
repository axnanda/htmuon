"""exp5: noise-free (M2) from GENERIC (non-commuting) Gaussian initialisation.

 A  Muon, d <= n:  autonomous iteration  K+ = |K - eta*Lam|,  K = (G G^T)^(1/2), G = Lam C   (Theorem 6).
    d = 60, k = 6, eta = 0.01, C_0 = Gaussian d x n with row norms ~ 1 (= 100 eta), n in {d, 4d}.
    Measured: absorption time, two-step-averaged alignment  thetabar = sum_D M_ii / tr M,
    M = (K_e^2 + K_o^2)/2, compared with psi_D/psi and with the rigorous bounds of Theorem 6;
    phase matrix Z = B^(-1/2) (K_e - B) B^(-1/2), B = eta*Lam/2  (commuting + uniform phases: tr Z^2/d = 1/3).
 B  HTMuon(p), d <= n, full matrix simulation: convergence to the unique 2-cycle
    K* = (eta*Lam/2)^(1/(1-p)), theta_inf = sum_D lam^q / sum lam^q  (Theorem 7);
    finite-difference check of the multipliers  m_ij = -1 + 2 (rho^(1-p) - rho^(1+p))/(1 - rho^2).
 C  Echelon(r), d <= n, full matrix simulation: number of active directions and theta_inf.
 D  tall matrices n < d (rank-n gradient): which eigen-directions carry the long-run energy?
"""
import sys
import time

import numpy as np

from common import msd, ratio_pred, save_json, spectral_filter, spectrum

PART = sys.argv[1] if len(sys.argv) > 1 else "ABCD"
ETA = 0.01
t0 = time.time()
out = {}


def psd_sqrt(S):
    w, U = np.linalg.eigh(S)
    return (U * np.sqrt(np.clip(w, 0, None))) @ U.T


# ------------------------------------------------------------------------------------ A
if "A" in PART:
    D, K = 60, 6
    rows, curves = [], {}
    for n_mult in [1, 4]:
        n = n_mult * D
        for m in [2, 5, 10, 20, 50, 100, 200, 500]:
            lam = spectrum(D, K, m)
            B = ETA * lam / 2
            psiD, psiB = (lam[:K] ** 2).sum(), (lam[K:] ** 2).sum()
            acc = {key: [] for key in ["thbar", "th_even", "th_odd", "absorb", "Lbar", "trZ2", "normZ", "ZDB",
                                       "th0", "thmin", "tmin", "thmax_descent", "desc_err", "t1"]}
            for seed in range(5):
                rng = np.random.default_rng(50_000 + 1000 * n_mult + 10 * m + seed)
                C0 = rng.standard_normal((D, n)) / np.sqrt(n)
                G0 = lam[:, None] * C0
                Kt = psd_sqrt(G0 @ G0.T)
                K0 = Kt.copy()
                # length of the exact linear-descent phase K_t = K_0 - t eta Lam
                R0 = K0 / np.sqrt(lam[:, None] * lam[None, :])
                t1 = int(np.floor(np.linalg.eigvalsh(R0)[0] / ETA))
                T = 700
                th = np.empty(T + 1)
                absorbed = -1
                desc_err = 0.0
                for t in range(T + 1):
                    e = (Kt * Kt).sum(1)
                    th[t] = e[:K].sum() / e.sum()
                    if t <= t1:
                        desc_err = max(desc_err, float(np.abs(Kt - (K0 - t * ETA * np.diag(lam))).max()))
                    w, V = np.linalg.eigh(Kt - ETA * np.diag(lam))
                    if absorbed < 0 and np.clip(w, 0, None).sum() < 1e-13 * ETA * lam.sum():
                        absorbed = t
                    Kprev = Kt
                    Kt = (V * np.abs(w)) @ V.T
                Ke, Ko = Kprev, Kt
                M = 0.5 * (Ke @ Ke + Ko @ Ko)
                dM = np.diag(M)
                Z = (Ke - np.diag(B)) / np.sqrt(B[:, None] * B[None, :])
                acc["thbar"].append(dM[:K].sum() / dM.sum())
                acc["th_even"].append(th[T - 1])
                acc["th_odd"].append(th[T])
                acc["absorb"].append(absorbed)
                acc["Lbar"].append(0.5 * (dM / lam).sum() / (ETA ** 2 * lam.sum()))
                acc["trZ2"].append((Z * Z).sum() / D)
                acc["normZ"].append(np.abs(np.linalg.eigvalsh(Z)).max())
                acc["ZDB"].append((Z[:K, K:] ** 2).sum() / K)
                acc["th0"].append(th[0])
                acc["thmin"].append(th[:max(absorbed, 1) + 1].min())
                acc["tmin"].append(int(np.argmin(th[:max(absorbed, 1) + 1])))
                acc["thmax_descent"].append(th[:max(absorbed, 1) + 1].max())
                acc["desc_err"].append(desc_err)
                acc["t1"].append(t1)
                if seed == 0 and m in (10, 100):
                    curves[f"n{n_mult}d_m{m}"] = dict(theta=th)
            lower = 1 - (2 * (D - K) * lam[K] ** 2 + K * lam[0] * lam[K]) / psiD
            lower_sharp = psiD / (psiD + psiB + lam[K] * (lam[0] * min(K, D - K) + lam[K] * (D - K)))
            upper = (psiD + lam[0] * lam[:K].sum()) / (psiD + lam[0] * lam[:K].sum() + psiB)
            row = dict(n_over_d=n_mult, m=m, psi_ratio=psiD / (psiD + psiB), lower_bound=lower_sharp,
                       lower_bound_simple=lower, upper_bound=upper,
                       thetabar=msd(acc["thbar"]), theta_even=msd(acc["th_even"]), theta_odd=msd(acc["th_odd"]),
                       absorb_time=msd(acc["absorb"]), never_absorbed=int(sum(a < 0 for a in acc["absorb"])),
                       Lbar_over_eta2trA=msd(acc["Lbar"]), trZ2_over_d=msd(acc["trZ2"]), normZ=msd(acc["normZ"]),
                       ZDB_fro2_over_k=msd(acc["ZDB"]), theta0=msd(acc["th0"]), theta_min_before_absorb=msd(acc["thmin"]),
                       tmin=msd(acc["tmin"]), theta_max_before_absorb=msd(acc["thmax_descent"]),
                       linear_descent_len=msd(acc["t1"]), linear_descent_max_err=float(max(acc["desc_err"])))
            rows.append(row)
            print(f"[A muon n={n_mult}d m={m:3d}] thetabar={row['thetabar'][0]:.6f}+-{row['thetabar'][1]:.1e} "
                  f"psiD/psi={row['psi_ratio']:.6f} bounds=[{lower_sharp:.4f},{upper:.6f}] | even/odd="
                  f"{row['theta_even'][0]:.5f}/{row['theta_odd'][0]:.5f} | absorbed at {row['absorb_time'][0]:.0f} "
                  f"(never: {row['never_absorbed']}) Lbar/(eta^2 trA)={row['Lbar_over_eta2trA'][0]:.4f} "
                  f"trZ^2/d={row['trZ2_over_d'][0]:.3f} |Z|={row['normZ'][0]:.3f} |Z_DB|^2/k={row['ZDB_fro2_over_k'][0]:.3f} | "
                  f"theta0={row['theta0'][0]:.4f} min={row['theta_min_before_absorb'][0]:.4f} at {row['tmin'][0]:.0f} "
                  f"max={row['theta_max_before_absorb'][0]:.4f} | lin-descent len {row['linear_descent_len'][0]:.0f} "
                  f"err {row['linear_descent_max_err']:.1e}", flush=True)
    out["A_muon"] = rows
    out["A_curves"] = curves
    save_json("exp5_generic_init_A.json", dict(rows=rows, curves=curves, config=dict(d=D, k=K, eta=ETA)))

# ------------------------------------------------------------------------------------ B
if "B" in PART:
    # (i) multipliers of the K-map at K*  (finite differences, d = 4)
    lam4 = np.array([8.0, 5.0, 2.0, 1.0])
    jac = []
    for p in [0.125, 0.5, 0.8]:
        kap = (ETA * lam4 / 2) ** (1 / (1 - p))

        def Phi(Km):
            w, U = np.linalg.eigh(Km)
            Kp = (U * np.clip(w, 0, None) ** p) @ U.T
            N = Km - ETA * lam4[:, None] * Kp
            return psd_sqrt(N @ N.T)

        worst = 0.0
        mmin, mmax = 1.0, -1.0
        for i in range(4):
            for j in range(i, 4):
                Eij = np.zeros((4, 4))
                Eij[i, j] = Eij[j, i] = 1.0
                eps = 1e-6 * min(kap[i], kap[j])
                dK = (Phi(np.diag(kap) + eps * Eij) - Phi(np.diag(kap) - eps * Eij)) / (2 * eps)
                rho = min(kap[i], kap[j]) / max(kap[i], kap[j])
                mij = 2 * p - 1 if i == j else -1 + 2 * (rho ** (1 - p) - rho ** (1 + p)) / (1 - rho ** 2)
                worst = max(worst, float(np.abs(dK - mij * Eij).max()))
                mmin, mmax = min(mmin, mij), max(mmax, mij)
        jac.append(dict(p=p, max_abs_err_jacobian=worst, multiplier_range=[mmin, mmax],
                        fixed_point_residual=float(np.abs(Phi(np.diag(kap)) - np.diag(kap)).max() / kap.max())))
        print(f"[B jacobian p={p}] max |dPhi[E_ij] - m_ij E_ij| = {worst:.2e}; multipliers in [{mmin:.4f},{mmax:.4f}]; "
              f"|Phi(K*)-K*|/|K*| = {jac[-1]['fixed_point_residual']:.1e}")
    out["B_jacobian"] = jac

    # (ii) full matrix simulations
    D, K = 40, 4
    rows, curves = [], {}
    for n in [40, 160]:
        for p in [0.125, 0.5]:
            q = 2 / (1 - p)
            for m in [2, 10, 100]:
                lam = spectrum(D, K, m)
                Estar = (ETA * lam / 2) ** q
                T = 4000
                res = {key: [] for key in ["th", "relK", "offd", "thmin", "tmin", "t99"]}
                for seed in range(3):
                    rng = np.random.default_rng(60_000 + n + int(1000 * p) + 10 * m + seed)
                    C = rng.standard_normal((D, n)) / np.sqrt(n)
                    th = np.empty(T + 1)
                    for t in range(T + 1):
                        G = lam[:, None] * C
                        e = (G * G).sum(1)
                        th[t] = e[:K].sum() / e.sum()
                        if t < T:
                            C = C - ETA * spectral_filter(G, "ht", p=p)
                    GG = G @ G.T
                    Kfin = psd_sqrt(GG)
                    Kstar = np.diag((ETA * lam / 2) ** (1 / (1 - p)))
                    res["th"].append(th[-1])
                    res["relK"].append(np.linalg.norm(Kfin - Kstar) / np.linalg.norm(Kstar))
                    res["offd"].append(np.abs(GG - np.diag(np.diag(GG))).max() / Estar.max())
                    res["thmin"].append(th.min())
                    res["tmin"].append(int(np.argmin(th)))
                    tm = int(np.argmin(th))
                    after = np.where(np.abs(th[tm:] - th[-1]) <= 0.01 * th[-1])[0]
                    res["t99"].append(int(tm + after[0]))
                    if seed == 0 and m in (10, 100) and n == 160:
                        curves[f"p{p}_m{m}"] = dict(theta=th[:1500])
                pred = ratio_pred(lam, K, q)
                row = dict(n=n, p=p, m=m, pred=pred, theta_final=msd(res["th"]),
                           abs_err_theta=float(np.abs(np.array(res["th"]) - pred).max()),
                           rel_err_K=float(max(res["relK"])), max_offdiag_GGt_over_Estar=float(max(res["offd"])),
                           theta_min=msd(res["thmin"]), tmin=msd(res["tmin"]), t_back_within_1pct=msd(res["t99"]),
                           TD_pred=1 / ((1 - p) * ETA * lam[K - 1] ** p), TB_pred=1 / ((1 - p) * ETA * lam[-1] ** p))
                rows.append(row)
                print(f"[B ht p={p} n={n} m={m:3d}] theta_final={row['theta_final'][0]:.8f} pred={pred:.8f} "
                      f"|err|={row['abs_err_theta']:.1e} |K-K*|/|K*|={row['rel_err_K']:.1e} offdiag={row['max_offdiag_GGt_over_Estar']:.1e} "
                      f"| min theta={row['theta_min'][0]:.2e} at {row['tmin'][0]:.0f} (T_D ~ {row['TD_pred']:.0f}), back at "
                      f"{row['t_back_within_1pct'][0]:.0f} (T_B ~ {row['TB_pred']:.0f})", flush=True)
    out["B_ht"] = rows
    save_json("exp5_generic_init_B.json", dict(jacobian=jac, rows=rows, curves=curves, config=dict(d=D, k=K, eta=ETA)))


# ------------------------------------------------------------------------------------ C, D
def run_generic(lam, n, kind, T, tail, seed, K, p=0.125, r=0):
    D = len(lam)
    rng = np.random.default_rng(seed)
    C = rng.standard_normal((D, n)) / np.sqrt(n)
    Eacc = np.zeros(D)
    th = np.empty(T)
    for t in range(T):
        G = lam[:, None] * C
        e = (G * G).sum(1)
        th[t] = e[:K].sum() / e.sum()
        if t >= T - tail:
            Eacc += e
        C = C - ETA * spectral_filter(G, kind, p=p, r=r)
    return Eacc / tail, th


if "C" in PART:
    D, K, n = 40, 4, 160
    rows = []
    for r in [2, 4, 8, 16]:
        for m in [10, 100]:
            lam = spectrum(D, K, m)
            res = {key: [] for key in ["th", "active", "top", "thmin", "tmin"]}
            for seed in range(3):
                E, th = run_generic(lam, n, "ech", 8000, 1000, 70_000 + 100 * r + m + seed, K, r=r)
                res["th"].append(E[:K].sum() / E.sum())
                res["active"].append(int((E > 1e-12 * E.max()).sum()))
                res["top"].append(E[:r + 1].sum() / E.sum())
                res["thmin"].append(th.min())
                res["tmin"].append(int(np.argmin(th)))
            w2 = lam ** 2
            pred = w2[:min(K, r + 1)].sum() / w2[:r + 1].sum()
            row = dict(r=r, m=m, pred_top_r1_uniform=pred, theta=msd(res["th"]), active=msd(res["active"]),
                       frac_energy_top_r1=msd(res["top"]), theta_min=msd(res["thmin"]), tmin=msd(res["tmin"]))
            rows.append(row)
            print(f"[C ech r={r:2d} m={m:3d}] theta={row['theta'][0]:.6f}+-{row['theta'][1]:.1e} pred(top r+1)={pred:.6f} "
                  f"active={row['active'][0]:.1f} fracTop={row['frac_energy_top_r1'][0]:.4f} min theta={row['theta_min'][0]:.2e} "
                  f"at {row['tmin'][0]:.0f}", flush=True)
    out["C_echelon"] = rows
    save_json("exp5_generic_init_C.json", dict(rows=rows, config=dict(d=D, k=K, n=n, eta=ETA)))

if "D" in PART:
    D, K, m = 40, 4, 10
    lam = spectrum(D, K, m)
    rows = []
    for n in [1, 2, 8]:
        for name, kind, p in [("muon", "muon", 0.0), ("ht0.125", "ht", 0.125), ("ht0.5", "ht", 0.5)]:
            q = 2 / (1 - p)
            res = {key: [] for key in ["th", "top", "relE"]}
            for seed in range(3):
                E, th = run_generic(lam, n, kind, 12000, 2000, 80_000 + 100 * n + int(1000 * p) + seed, K, p=p)
                res["th"].append(E[:K].sum() / E.sum())
                res["top"].append(E[:n].sum() / E.sum())
                Estar = (ETA * lam[:n] / 2) ** q
                res["relE"].append(float(np.abs(E[:n] / Estar - 1).max()))
            pred = (lam[:min(K, n)] ** q).sum() / (lam[:n] ** q).sum()
            row = dict(n=n, opt=name, pred_top_n=pred, theta=msd(res["th"]), frac_energy_top_n=msd(res["top"]),
                       max_rel_dev_energy_from_floor=float(max(res["relE"])))
            rows.append(row)
            print(f"[D tall n={n} {name:8s}] theta={row['theta'][0]:.6f}+-{row['theta'][1]:.1e} pred(top-n, lam^q)={pred:.6f} "
                  f"energy share of top-n eigen-directions={row['frac_energy_top_n'][0]:.6f} "
                  f"max |E_i/(eta lam_i/2)^q - 1| (i<=n) = {row['max_rel_dev_energy_from_floor']:.2e}", flush=True)
    out["D_tall"] = rows
    save_json("exp5_generic_init_D.json", dict(rows=rows, config=dict(d=D, k=K, m=m, eta=ETA)))
print("elapsed", time.time() - t0)
