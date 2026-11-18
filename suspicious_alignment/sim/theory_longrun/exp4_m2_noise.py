"""exp4: (M2) with isotropic gradient noise, d << n -- test of the row-decoupled mean-field law

      E_i = (eta lam_i / 2) g_i^(1+p),     2 (g_i^2 - nu^2) = eta lam_i g_i^(1+p),   nu = sigma sqrt(n)

(E_i = stationary clean-gradient energy lam_i^2 E|c_i|^2 of eigen-direction i; p = 1: SGD = Deng's
Theorem 16 exactly; p = 0: Muon; p = 0.125: HTMuon), and of its heuristic Echelon(r) version
(directions 1..r+1 follow the Muon law, the others SGD with step eta / tau, tau = g_{r+1}).

d = 24, k = 4, n = 600 (sqrt(d/n) = 0.2), eta = 0.01, generic Gaussian init with row norms 20 eta,
burn-in 1500 steps, average over 2500 steps, 3 seeds.

 part A: noise sweep  chi_B = eta*lam_{k+1}/nu in {0.01 .. 10}  for m in {10, 100}
 part B: m sweep at chi_B = 0.1 (bulk noise-dominated, dominant block step-dominated for m >= 20)
"""
import sys
import time

import numpy as np

from common import (deng_theta_inf, mf_energy, mf_energy_echelon, mf_theta, msd, ratio_pred, run_m2,
                    save_json, spectrum)

D, K, N, ETA = 24, 4, 600, 0.01
T, BURN = 4000, 1500
SEEDS = [0, 1, 2]
PART = sys.argv[1] if len(sys.argv) > 1 else "AB"
t0 = time.time()

OPTS = {"muon": dict(kind="muon", p=0.0), "ht0.125": dict(kind="ht", p=0.125), "ht0.5": dict(kind="ht", p=0.5),
        "ech2": dict(kind="ech", r=2), "ech4": dict(kind="ech", r=4), "ech8": dict(kind="ech", r=8)}


def predict(name, lam, nu):
    o = OPTS[name]
    if o["kind"] == "ech":
        E = mf_energy_echelon(lam, ETA, nu, o["r"])
        sig = nu / np.sqrt(N)
        edge = nu * (1 + np.sqrt((D - o["r"]) / N))          # largest singular value of a pure-noise tail
        E2 = mf_energy_echelon(lam, ETA, nu, o["r"], tau_edge=edge)
        return E, E2
    return mf_energy(lam, ETA, nu, o["p"]), None


def one(name, lam, nu):
    o = OPTS[name]
    sigma = nu / np.sqrt(N)
    Es, ths, taus = [], [], []
    for sd in SEEDS:
        rng = np.random.default_rng(10_000 + 97 * sd + int(1e3 * lam[0]) + hash(name) % 1000)
        C0 = rng.standard_normal((D, N)) * (20 * ETA / np.sqrt(N))
        res = run_m2(lam, N, o["kind"], ETA, sigma, T, BURN, rng, C0, p=o.get("p", 0.0), r=o.get("r", 0), k=K)
        Es.append(res["E"])
        ths.append(res["theta_time"])
        taus.append(res["tau"])
    Es = np.array(Es)
    th_ratio = Es[:, :K].sum(1) / Es.sum(1)
    Ep, Ep2 = predict(name, lam, nu)
    row = dict(opt=name, nu=nu, meas_ratio=msd(th_ratio), meas_time=msd(ths),
               pred_mf=float(Ep[:K].sum() / Ep.sum()),
               pred_mf_edge=(float(Ep2[:K].sum() / Ep2.sum()) if Ep2 is not None else None),
               E_meas=Es.mean(0), E_pred=Ep,
               ED_meas_over_pred=float(Es[:, :K].sum(1).mean() / Ep[:K].sum()),
               EB_meas_over_pred=float(Es[:, K:].sum(1).mean() / Ep[K:].sum()),
               tau_over_nu=float(np.mean(taus) / nu))
    return row


out = {}
if "A" in PART:
    rows = []
    for m in [10, 100]:
        lam = spectrum(D, K, m)
        for chiB in [0.01, 0.03, 0.1, 0.3, 1.0, 3.0, 10.0]:
            nu = ETA * lam[K] / chiB
            for name in ["muon", "ht0.125", "ech2", "ech4"]:
                row = one(name, lam, nu)
                q = 2 / (1 - OPTS[name].get("p", 0.0))
                row.update(m=m, chi_B=chiB, chi_D_min=ETA * lam[K - 1] / nu, deng_small=float(lam[:K].sum() / lam.sum()),
                           lam_q=float(ratio_pred(lam, K, q)))
                rows.append(row)
                print(f"[A m={m} chiB={chiB:5.2f}] {name:8s} meas={row['meas_ratio'][0]:.5f}+-{row['meas_ratio'][1]:.5f} "
                      f"MF={row['pred_mf']:.5f}" + (f" MF(edge)={row['pred_mf_edge']:.5f}" if row['pred_mf_edge'] else "")
                      + f" | Deng-small={row['deng_small']:.5f} lam^q={row['lam_q']:.5f} | E_D m/p={row['ED_meas_over_pred']:.3f} "
                      f"E_B m/p={row['EB_meas_over_pred']:.3f} tau/nu={row['tau_over_nu']:.3f}", flush=True)
    out["A"] = rows
    save_json("exp4_m2_noise_A.json", dict(config=dict(d=D, k=K, n=N, eta=ETA, T=T, burn=BURN, seeds=SEEDS), rows=rows))

if "B" in PART:
    rows = []
    chiB = 0.1
    for m in [2, 5, 10, 20, 50, 100, 200]:
        lam = spectrum(D, K, m)
        nu = ETA * lam[K] / chiB
        sigma = nu / np.sqrt(N)
        # SGD reference (Deng): eta_sgd = 1/lam_1, started in its exact stationary law
        eta_s = 1.0 / lam[0]
        beta = eta_s * sigma ** 2 / (2 * lam - eta_s * lam ** 2)
        Es = []
        for sd in SEEDS:
            rng = np.random.default_rng(555 + sd + 13 * m)
            C0 = rng.standard_normal((D, N)) * np.sqrt(beta)[:, None]
            Es.append(run_m2(lam, N, "sgd", eta_s, sigma, T, BURN, rng, C0, k=K)["E"])
        Es = np.array(Es)
        row = dict(opt="sgd", m=m, chi_B=chiB, nu=nu, meas_ratio=msd(Es[:, :K].sum(1) / Es.sum(1)),
                   pred_mf=float(deng_theta_inf(lam, K, eta_s, sigma ** 2)), deng_small=float(lam[:K].sum() / lam.sum()),
                   lam_q=float(lam[:K].sum() / lam.sum()))
        rows.append(row)
        print(f"[B m={m}] sgd      meas={row['meas_ratio'][0]:.5f}+-{row['meas_ratio'][1]:.5f} Thm16={row['pred_mf']:.5f}", flush=True)
        for name in ["muon", "ht0.125", "ht0.5", "ech2", "ech4", "ech8"]:
            row = one(name, lam, nu)
            q = 2 / (1 - OPTS[name].get("p", 0.0))
            row.update(m=m, chi_B=chiB, deng_small=float(lam[:K].sum() / lam.sum()), lam_q=float(ratio_pred(lam, K, q)))
            rows.append(row)
            print(f"[B m={m}] {name:8s} meas={row['meas_ratio'][0]:.5f}+-{row['meas_ratio'][1]:.5f} MF={row['pred_mf']:.5f}"
                  + (f" MF(edge)={row['pred_mf_edge']:.5f}" if row['pred_mf_edge'] else "")
                  + f" | Deng-small={row['deng_small']:.5f} lam^q={row['lam_q']:.5f} | E_D m/p={row['ED_meas_over_pred']:.3f} "
                  f"E_B m/p={row['EB_meas_over_pred']:.3f} tau/nu={row['tau_over_nu']:.3f}", flush=True)
    out["B"] = rows
    save_json("exp4_m2_noise_B.json", dict(config=dict(d=D, k=K, n=N, eta=ETA, T=T, burn=BURN, seeds=SEEDS, chi_B=chiB), rows=rows))
print("elapsed", time.time() - t0)
