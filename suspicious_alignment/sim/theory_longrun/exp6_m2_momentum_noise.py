"""exp6: (M2) with isotropic gradient noise -- (M) momentum beta = 0.95 (Nesterov-EMA exactly as in
muon.py) and (R) dependence on the aspect ratio d/n of the mean-field law.

 M  d = 24, k = 4, n = 600, eta = 0.01, beta = 0.95;  muon / ht(0.125) / ech(4);  m in {10, 100};
    chi_B = eta lam_{k+1}/nu in {0.03, 0.3, 3};  T = 5000, burn-in 2500, 3 seeds.
    Predictions:  (H4) momentum mean field (common.mf_momentum_energy: per-row frozen-step linear
    recursion with momentum, stationary second moments from the 2x2 Lyapunov equation, self-consistent
    filter-input norm g_i);  (H2) the momentum-free mean field for comparison.
 R  no momentum, d = 24, n in {24, 96} (the mean field assumes d << n; exp4 used n = 600).
"""
import sys
import time

import numpy as np

from common import (mf_energy, mf_momentum_energy, mom_xcrit, msd, ratio_pred, run_m2, save_json,
                    spectrum)

D, K, ETA = 24, 4, 0.01
SEEDS = [0, 1, 2]
PART = sys.argv[1] if len(sys.argv) > 1 else "MR"
t0 = time.time()
OPTS = {"muon": dict(kind="muon", p=0.0), "ht0.125": dict(kind="ht", p=0.125), "ech4": dict(kind="ech", p=0.0, r=4)}

if "M" in PART:
    N, BETA, T, BURN = 600, 0.95, 5000, 2500
    rows = []
    for m in [10, 100]:
        lam = spectrum(D, K, m)
        for chiB in [0.03, 0.3, 3.0]:
            nu = ETA * lam[K] / chiB
            sigma = nu / np.sqrt(N)
            for name, o in OPTS.items():
                Es = []
                for sd in SEEDS:
                    rng = np.random.default_rng(31_000 + 97 * sd + 7 * m + int(100 * chiB) + len(name))
                    C0 = rng.standard_normal((D, N)) * (20 * ETA / np.sqrt(N))
                    Es.append(run_m2(lam, N, o["kind"], ETA, sigma, T, BURN, rng, C0, p=o["p"], r=o.get("r", 0),
                                     beta=BETA, k=K)["E"])
                Es = np.array(Es)
                Emom, gm = mf_momentum_energy(lam, ETA, nu, o["p"], BETA)
                E0 = mf_energy(lam, ETA, nu, o["p"])
                q = 2 / (1 - o["p"])
                row = dict(opt=name, m=m, chi_B=chiB, nu=nu, beta=BETA,
                           meas=msd(Es[:, :K].sum(1) / Es.sum(1)),
                           pred_mf_momentum=float(Emom[:K].sum() / Emom.sum()),
                           pred_mf_no_momentum=float(E0[:K].sum() / E0.sum()),
                           deng_small=float(lam[:K].sum() / lam.sum()), lam_q=float(ratio_pred(lam, K, q)),
                           ED_meas_over_pred=float(Es[:, :K].sum(1).mean() / Emom[:K].sum()),
                           EB_meas_over_pred=float(Es[:, K:].sum(1).mean() / Emom[K:].sum()),
                           ED_meas_over_nomom=float(Es[:, :K].sum(1).mean() / E0[:K].sum()),
                           EB_meas_over_nomom=float(Es[:, K:].sum(1).mean() / E0[K:].sum()),
                           E_meas=Es.mean(0), E_pred=Emom)
                rows.append(row)
                print(f"[M m={m} chiB={chiB:5.2f}] {name:8s} meas={row['meas'][0]:.5f}+-{row['meas'][1]:.5f} "
                      f"MF(mom)={row['pred_mf_momentum']:.5f} MF(no mom)={row['pred_mf_no_momentum']:.5f} | "
                      f"Deng-small={row['deng_small']:.5f} lam^q={row['lam_q']:.5f} | E_D meas/MF(mom)={row['ED_meas_over_pred']:.3f} "
                      f"E_B meas/MF(mom)={row['EB_meas_over_pred']:.3f} | vs no-mom MF: E_D {row['ED_meas_over_nomom']:.3f} "
                      f"E_B {row['EB_meas_over_nomom']:.3f}", flush=True)
    save_json("exp6_momentum_noise.json", dict(config=dict(d=D, k=K, n=N, eta=ETA, beta=BETA, T=T, burn=BURN, seeds=SEEDS,
                                                           x_crit=mom_xcrit(BETA)), rows=rows))

if "R" in PART:
    T, BURN = 4000, 1500
    rows = []
    m = 10
    lam = spectrum(D, K, m)
    for N in [24, 96]:
        for chiB in [0.1, 1.0]:
            nu = ETA * lam[K] / chiB
            sigma = nu / np.sqrt(N)
            for name in ["muon", "ht0.125"]:
                o = OPTS[name]
                Es = []
                for sd in SEEDS:
                    rng = np.random.default_rng(41_000 + 97 * sd + N + int(100 * chiB) + len(name))
                    C0 = rng.standard_normal((D, N)) * (20 * ETA / np.sqrt(N))
                    Es.append(run_m2(lam, N, o["kind"], ETA, sigma, T, BURN, rng, C0, p=o["p"], k=K)["E"])
                Es = np.array(Es)
                E0 = mf_energy(lam, ETA, nu, o["p"])
                row = dict(opt=name, n=N, d_over_n=D / N, m=m, chi_B=chiB,
                           meas=msd(Es[:, :K].sum(1) / Es.sum(1)), pred_mf=float(E0[:K].sum() / E0.sum()),
                           ED_meas_over_pred=float(Es[:, :K].sum(1).mean() / E0[:K].sum()),
                           EB_meas_over_pred=float(Es[:, K:].sum(1).mean() / E0[K:].sum()))
                rows.append(row)
                print(f"[R n={N:3d} chiB={chiB:4.1f}] {name:8s} meas={row['meas'][0]:.5f}+-{row['meas'][1]:.5f} "
                      f"MF={row['pred_mf']:.5f} | E_D m/p={row['ED_meas_over_pred']:.3f} E_B m/p={row['EB_meas_over_pred']:.3f}",
                      flush=True)
    save_json("exp6_aspect_ratio.json", dict(config=dict(d=D, k=K, eta=ETA, m=m, T=T, burn=BURN, seeds=SEEDS), rows=rows))
print("elapsed", time.time() - t0)
