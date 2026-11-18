"""exp1: baseline -- Deng et al.'s two-phase picture for constant-step SGD (Theorems 15, 16).

Setting copied from the paper's numerical section: d = 500, k = 50, eta = 0.003, T = 30000,
m = lam_k/lam_{k+1} in {5,...,500}.  (The paper does not specify the spectrum inside the blocks,
the noise or the initialisation; we use dominant eigenvalues linearly spaced in [m, 1.2 m], bulk in
[0.5, 1], isotropic noise Sigma = I, x_0 ~ N(0, r0^2 I) with r0 = 10 -- a 'large' initialisation.)

Checked quantities
  * theta_inf (Thm 16):  sum_D lam^2 beta / sum lam^2 beta,  beta_i = eta/(2 lam_i - eta lam_i^2)
      measured  (i) time average of theta_t over the second half, (ii) ratio of time-averaged
      block energies (the 'ratio of expectations' that the theorem actually computes).
  * two phases: seed-averaged theta_t first decreases then increases; argmin compared with
      - the deterministic equivalent  thetabar(t) = sum_D lam^2 E c^2 / sum lam^2 E c^2,
        E c_i(t)^2 = (1-eta lam_i)^(2t) (c_i0^2 - beta_i) + beta_i,
      - t* of Theorem 15 (a lower bound for the length of the decreasing phase).
"""
import time

import numpy as np

from common import (deng_beta, deng_theta_inf, deng_tstar, msd, save_json, spectrum,
                    theta_from_energy)

D, K, ETA, T = 500, 50, 0.003, 30000
MS = [5, 10, 20, 50, 100, 200, 300, 400, 500]
SEEDS = [42, 87, 568, 1101, 12138, 70425, 4008001, 7]
R0, SIG = 10.0, 1.0

t0 = time.time()
rows, curves = [], {}
for m in MS:
    lam = spectrum(D, K, m, dom_spread=1.2)
    S = len(SEEDS)
    c = np.stack([np.random.default_rng(s).standard_normal(D) * R0 for s in SEEDS])
    rngs = np.random.default_rng(1000 + m)
    th = np.empty((T + 1, S))
    accD = np.zeros(S)
    accT = np.zeros(S)
    lam2 = lam ** 2
    fac = 1 - ETA * lam
    for t in range(T + 1):
        E = lam2 * c * c
        sD = E[:, :K].sum(1)
        sT = E.sum(1)
        th[t] = sD / sT
        if t >= T // 2:
            accD += sD
            accT += sT
        c = fac * c - ETA * SIG * rngs.standard_normal((S, D))
    th_time = th[T // 2:].mean(0)          # per-seed time average of theta_t
    th_ratio = accD / accT                 # per-seed ratio of time-averaged energies
    th_std_time = th[T // 2:].std(0).mean()
    pred = deng_theta_inf(lam, K, ETA, SIG ** 2)
    pred_small = lam[:K].sum() / lam.sum()
    # deterministic equivalent
    beta = deng_beta(lam, ETA, SIG ** 2)
    tt = np.arange(0, 6001)
    Ec2 = (fac[None, :] ** (2 * tt[:, None])) * (R0 ** 2 - beta[None, :]) + beta[None, :]
    thbar = theta_from_energy(lam2 * Ec2, K)
    tmin_det = int(np.argmin(thbar))
    thm = th.mean(1)
    tmin_emp = int(np.argmin(thm[:6001]))
    tstar, delta = deng_tstar(lam, K, ETA, np.full(D, R0 ** 2), SIG ** 2, SIG ** 2)
    # monotone decrease of the seed-mean up to t*?
    ts = int(np.floor(tstar)) if np.isfinite(tstar) else 0
    mono = bool(np.all(np.diff(thm[: ts + 1]) < 0)) if ts > 0 else None
    cond_gap = 2 * (lam[K - 1] - lam[K]) / (lam[0] ** 2 - lam[-1] ** 2)
    rows.append(dict(m=m, eta=ETA, eta_lam1=ETA * lam[0], gap_cond_rhs=cond_gap,
                     assumption_holds=bool(ETA < min(2 / lam[0], cond_gap)),
                     theta0=float(thm[0]), theta_min=float(thm.min()),
                     pred_thm16=pred, pred_small_eta=pred_small,
                     meas_time_avg=msd(th_time), meas_ratio_of_avgs=msd(th_ratio),
                     within_run_std_theta=float(th_std_time),
                     tmin_emp=tmin_emp, tmin_det=tmin_det, tstar_thm15=tstar, delta=delta,
                     mean_theta_monotone_decreasing_until_tstar=mono))
    sub = np.unique(np.concatenate([np.arange(0, 400), np.unique(np.geomspace(400, T, 300).astype(int))]))
    curves[str(m)] = dict(t=sub, theta_mean=thm[sub], theta_sd=th.std(1)[sub],
                          t_det=tt[::5], theta_det=thbar[::5])
    r = rows[-1]
    print(f"m={m:4d} eta*lam1={r['eta_lam1']:.2f} assum={r['assumption_holds']} | theta0={r['theta0']:.4f} "
          f"min={r['theta_min']:.4f} | Thm16={pred:.5f} small-eta={pred_small:.5f} "
          f"meas(time)={r['meas_time_avg'][0]:.5f}+-{r['meas_time_avg'][1]:.5f} "
          f"meas(ratio)={r['meas_ratio_of_avgs'][0]:.5f}+-{r['meas_ratio_of_avgs'][1]:.5f} | "
          f"tmin emp={tmin_emp} det={tmin_det} t*={tstar:.1f} mono={mono}")

save_json("exp1_sgd_baseline.json", dict(config=dict(d=D, k=K, eta=ETA, T=T, seeds=SEEDS, r0=R0, sigma=SIG,
                                                     spectrum="dominant linspace(1.2m, m, k), bulk linspace(1, 0.5, d-k)"),
                                         rows=rows, curves=curves))
print("elapsed", time.time() - t0)
