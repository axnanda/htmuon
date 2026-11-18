"""exp1b: the authors' own experimental setup (deng-code/quad_sim.py), re-implemented in the eigenbasis.

  d = 500, k = 50, eta = 0.003, T = 30000, isotropic noise N(0, sigma^2 I), sigma = 0.5, x_0 ~ N(0, I),
  dominant eigenvalues linspace(100, 80, k), bulk linspace(7, 1, d-k) rescaled so that the largest
  bulk eigenvalue is 80/(m + 0.1);  m in {5, 10, 20, 50, 100, 200, 300, 400, 500};
  seeds {42, 87, 568, 12138, 1101, 70425, 4008001} (the authors' list).
  (A x is orthogonally equivariant and the noise is isotropic, so simulating in the eigenbasis is
  equivalent in law to the authors' random orthogonal Q.)

Part 1 (SGD):  Deng's two-phase picture and Theorem 16.
   statistics: (i) the authors' own estimator  mean_{t > T-10000} theta_t,
               (ii) ratio of time-averaged block energies,
   predictions: Theorem 16 (stationary), the finite-T deterministic equivalent
               thetabar(t) = sum_D lam^2 Ec^2 / sum lam^2 Ec^2,  Ec_i(t)^2 = (1-eta lam_i)^(2t) (1 - beta_i) + beta_i,
               averaged over the same window, and the small-step value sum_D lam / sum lam;
   two phases: argmin of the seed-mean theta_t, argmin of thetabar, Theorem 15's t*.

Part 2 ((M1) filtered updates in the same setup):  x+ = x - eta_p |g|^(p-1) g,  g = A x + xi,
   p in {0 (Muon = normalised SGD), 0.125 (HTMuon), 0.5}, with eta_p chosen so that the
   noise-dominated effective step  eta_p * nu^(p-1)  (nu = sigma sqrt(d))  equals
      'matched': 0.003 (the authors' SGD step)   and   'large': 0.024 (> 2/lam_1 = 0.02).
   prediction: frozen-effective-step self-consistent equation (common.m1_selfconsistent) = Theorem 16
   evaluated at eta_eff.
"""
import sys
import time

import numpy as np

from common import deng_beta, deng_theta_inf, deng_tstar, m1_selfconsistent, msd, save_json

D, K, ETA, T, SIG = 500, 50, 0.003, 30000, 0.5
MS = [5, 10, 20, 50, 100, 200, 300, 400, 500]
SEEDS = [42, 87, 568, 12138, 1101, 70425, 4008001]
STEADY = 10000
PART = sys.argv[1] if len(sys.argv) > 1 else "12"


def deng_spectrum(d, k, m):
    large = np.linspace(100, 80, k)
    small = np.linspace(7, 1, d - k)
    small = small * ((large[-1] / (m + 0.1)) / small[0])
    return np.concatenate([large, small])


def subsample(T):
    return np.unique(np.concatenate([np.arange(0, 600), np.unique(np.geomspace(600, T, 300).astype(int))]))


t0 = time.time()
out = dict(config=dict(d=D, k=K, eta=ETA, T=T, sigma=SIG, seeds=SEEDS, steady=STEADY, ms=MS,
                       spectrum="linspace(100,80,k) ++ linspace(7,1,d-k)*80/(7(m+0.1))"))
S = len(SEEDS)

if "1" in PART:
    rows, curves = [], {}
    for m in MS:
        lam = deng_spectrum(D, K, m)
        lam2 = lam ** 2
        c = np.stack([np.random.default_rng(s).standard_normal(D) for s in SEEDS])
        rng = np.random.default_rng(900 + m)
        fac = 1 - ETA * lam
        th = np.empty((T + 1, S))
        accD, accT = np.zeros(S), np.zeros(S)
        for t in range(T + 1):
            E = lam2 * c * c
            sD, sT = E[:, :K].sum(1), E.sum(1)
            th[t] = sD / sT
            if t > T - STEADY:
                accD += sD
                accT += sT
            c = fac * c - ETA * SIG * rng.standard_normal((S, D))
        beta = deng_beta(lam, ETA, SIG ** 2)
        # deterministic equivalent with E c_i0^2 = 1 (x_0 ~ N(0, I)); computed in log space, in chunks
        thbar = np.empty(T + 1)
        winD = winT = 0.0
        logfac = np.log(np.abs(fac))
        for a in range(0, T + 1, 3000):
            tt = np.arange(a, min(a + 3000, T + 1))
            with np.errstate(under="ignore"):
                Eg = lam2 * (np.exp(2 * tt[:, None] * logfac[None, :]) * (1 - beta[None, :]) + beta[None, :])
            thbar[tt] = Eg[:, :K].sum(1) / Eg.sum(1)
            w = tt > T - STEADY
            winD += Eg[w][:, :K].sum()
            winT += Eg[w].sum()
        thm = th.mean(1)
        tmin_emp, tmin_det = int(np.argmin(thm)), int(np.argmin(thbar))
        tstar, delta = deng_tstar(lam, K, ETA, np.ones(D), SIG ** 2, SIG ** 2)
        varrho = float((1 - beta[:K]).sum())
        gap_rhs = 2 * (lam[K - 1] - lam[K]) / (lam[0] ** 2 - lam[-1] ** 2)
        row = dict(m=m, lam_k1=float(lam[K]), lam_d=float(lam[-1]), eta_lam1=ETA * lam[0],
                   step_assumption=bool(ETA < min(2 / lam[0], gap_rhs)),
                   init_assumption=bool(varrho > delta - beta[:K].sum()) if np.isfinite(delta) else False,
                   varrho_D=varrho, delta=delta, tstar_thm15=tstar,
                   pred_thm16=float(deng_theta_inf(lam, K, ETA, SIG ** 2)),
                   pred_small_eta=float(lam[:K].sum() / lam.sum()),
                   pred_finite_T_window=float(thbar[T - STEADY + 1:].mean()),
                   pred_finite_T_ratio=float(winD / winT),
                   meas_authors_stat=msd(th[T - STEADY + 1:].mean(0)),
                   meas_ratio=msd(accD / accT),
                   within_run_std=float(th[T - STEADY + 1:].std(0).mean()),
                   theta0=float(thm[0]), theta_min=float(thm.min()), tmin_emp=tmin_emp, tmin_det=tmin_det,
                   bulk_relax_time_slowest=float(1 / (ETA * lam[-1])))
        rows.append(row)
        sub = subsample(T)
        curves[str(m)] = dict(t=sub, theta_mean=thm[sub], theta_sd=th.std(1)[sub], theta_det=thbar[sub])
        print(f"[sgd m={m:3d}] Thm16={row['pred_thm16']:.5f} finiteT={row['pred_finite_T_window']:.5f} "
              f"small-eta={row['pred_small_eta']:.5f} | meas(authors)={row['meas_authors_stat'][0]:.5f}"
              f"+-{row['meas_authors_stat'][1]:.5f} meas(ratio)={row['meas_ratio'][0]:.5f}+-{row['meas_ratio'][1]:.5f} "
              f"| theta0={row['theta0']:.4f} min={row['theta_min']:.2e} at t={tmin_emp} (det {tmin_det}); "
              f"t*={tstar:.1f} delta={delta:.2f} varrho={varrho:.1f} assum(step,init)="
              f"({row['step_assumption']},{row['init_assumption']})", flush=True)
    out["sgd"] = rows
    out["sgd_curves"] = curves
    save_json("exp1b_deng_setup_sgd.json", out)

if "2" in PART:
    nu = SIG * np.sqrt(D)
    rows, curves = [], {}
    for p in [0.0, 0.125, 0.5]:
        for label, target in [("matched", 0.003), ("large", 0.024)]:
            eta_p = target * nu ** (1 - p)
            for m in MS:
                lam = deng_spectrum(D, K, m)
                lam2 = lam ** 2
                c = np.stack([np.random.default_rng(s).standard_normal(D) for s in SEEDS])
                rng = np.random.default_rng(int(7000 + 13 * m + 1000 * p + (0 if label == "matched" else 5)))
                th = np.empty((T + 1, S))
                accD, accT, acceff = np.zeros(S), np.zeros(S), np.zeros(S)
                for t in range(T + 1):
                    gc = lam * c
                    E = gc * gc
                    sD, sT = E[:, :K].sum(1), E.sum(1)
                    th[t] = sD / sT
                    g = gc + SIG * rng.standard_normal((S, D))
                    eff = eta_p * (g * g).sum(1) ** ((p - 1) / 2)
                    if t > T - STEADY:
                        accD += sD
                        accT += sT
                        acceff += eff
                    c = c - eff[:, None] * g
                x_eff, E_pred = m1_selfconsistent(lam, eta_p, SIG, p)
                thm = th.mean(1)
                row = dict(p=p, step=label, eta_p=float(eta_p), m=m,
                           pred_selfconsistent=float(E_pred[:K].sum() / E_pred.sum()),
                           pred_etaeff_lam1=float(x_eff * lam[0]),
                           pred_thm16_at_target=float(deng_theta_inf(lam, K, min(target, 1.999 / lam[0]), SIG ** 2)),
                           meas_authors_stat=msd(th[T - STEADY + 1:].mean(0)), meas_ratio=msd(accD / accT),
                           meas_etaeff_lam1=msd(acceff / STEADY * lam[0]),
                           theta0=float(thm[0]), theta_min=float(thm.min()), tmin_emp=int(np.argmin(thm)))
                rows.append(row)
                if m in (5, 50, 200):
                    sub = subsample(T)
                    curves[f"p{p}_{label}_m{m}"] = dict(t=sub, theta_mean=thm[sub], theta_sd=th.std(1)[sub])
                print(f"[M1 p={p} {label:7s} m={m:3d}] pred(SC)={row['pred_selfconsistent']:.5f} "
                      f"meas(authors)={row['meas_authors_stat'][0]:.5f}+-{row['meas_authors_stat'][1]:.5f} "
                      f"meas(ratio)={row['meas_ratio'][0]:.5f}+-{row['meas_ratio'][1]:.5f} | eta_eff*lam1 pred="
                      f"{row['pred_etaeff_lam1']:.4f} meas={row['meas_etaeff_lam1'][0]:.4f} | theta0={row['theta0']:.4f} "
                      f"min={row['theta_min']:.2e} at t={row['tmin_emp']}", flush=True)
    save_json("exp1b_deng_setup_m1.json", dict(config=out["config"], nu=float(nu), rows=rows, curves=curves))
print("elapsed", time.time() - t0)
