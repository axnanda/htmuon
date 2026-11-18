"""E1 / (M1): the vector case n = 1, where F(g) = f(|g|) g/|g| (SGD, Muon = normalized SGD, HTMuon f = s^p).
Deng's exact protocol: d=500, k=50, sigma=0.5, x0 ~ N(0,I), T=30000, E[Alignment] over the last 10000 steps.

Groups (all vectorised over runs, eigenbasis):
  proto : kappa = 1 (rule learning rate), m in Deng's 9 values, 4 seeds, 5 filters
  kappa : m = 20, kappa in {1/4, 4, 16, 64}, 2 seeds
  free  : noise-free (sigma = 0), m in {5, 20, 100}, 2 seeds, T = 30000
Usage:  python3 e1_n1.py          (about 1.5 CPU-min)
"""
import os

import numpy as np

import specfilt as sf

D, K, T, STEADY = 500, 50, 30000, 10000
MS = [5, 10, 20, 50, 100, 200, 300, 400, 500]
SEEDS = [42, 87, 568, 12138, 1101, 70425, 4008001]
OPTS = ["sgd", "muon", "ht0.125", "ht0.25", "ht0.5"]


def fscalar(nrm, opt):
    kind, par = sf.parse_opt(opt)
    if kind == "sgd":
        return nrm
    if kind == "muon":
        return np.ones_like(nrm)
    return nrm ** par


def batch(runs, T=T, tsub=None):
    """runs: list of dicts (opt, m, sigma, eta, seed, init_scale).  Returns loss/theta arrays (R, len(tsub))
    plus the late-window statistics."""
    R = len(runs)
    lam = np.stack([sf.deng_spectrum(D, K, r["m"]) for r in runs])
    x = np.stack([r["init_scale"] * np.random.default_rng([r["seed"], int(r["m"]), 0]).standard_normal(D) for r in runs])
    sig = np.array([r["sigma"] for r in runs])[:, None]
    eta = np.array([r["eta"] for r in runs])[:, None]
    groups = {}
    for i, r in enumerate(runs):
        groups.setdefault(r["opt"], []).append(i)
    groups = {o: np.array(ix) for o, ix in groups.items()}
    rng = np.random.default_rng(987654321)
    tsub = np.arange(T + 1) if tsub is None else tsub
    tset = {int(t): a for a, t in enumerate(tsub)}
    loss = np.zeros((R, len(tsub)), np.float32)
    th = np.zeros((R, len(tsub)), np.float32)
    acc = np.zeros((R, 4))      # sum theta, sum theta^2, sum loss, sum (step * |g_true| / |update|)
    gn_true_late = np.zeros(R)
    gn_stoch_late = np.zeros(R)
    for t in range(T + 1):
        g = lam * x
        g2 = g * g
        tot = g2.sum(1)
        al = g2[:, :K].sum(1) / np.where(tot > 0, tot, 1.0)
        ls = 0.5 * (x * g).sum(1)
        a = tset.get(t)
        if a is not None:
            loss[:, a] = ls
            th[:, a] = al
        if t > T - STEADY:
            acc[:, 0] += al
            acc[:, 1] += al * al
            acc[:, 2] += ls
            gn_true_late += np.sqrt(tot)
        if t == T:
            break
        G = g + sig * rng.standard_normal((R, D))
        nrm = np.sqrt((G * G).sum(1, keepdims=True))
        if t > T - STEADY:
            gn_stoch_late += nrm[:, 0]
        step = np.empty_like(nrm)
        for o, ix in groups.items():
            step[ix] = fscalar(nrm[ix], o) / np.where(nrm[ix] > 0, nrm[ix], 1.0)
        x = x - eta * step * G
    E = acc[:, 0] / STEADY
    Sd = np.sqrt(np.maximum(acc[:, 1] / STEADY - E * E, 0))
    return dict(loss=loss, theta=th, E_align=E, Std_align=Sd, loss_late=acc[:, 2] / STEADY,
                gn_true_late=gn_true_late / STEADY, gn_stoch_late=gn_stoch_late / STEADY)


def rule(opt, m, sigma=sf.SIGMA0):
    prob = sf.Problem(D, K, 1, m, sigma=sigma)
    return sf.calibrate(prob, opt, nmc=400)


def main():
    cpu = sf.CpuLog("e1_n1")
    tsub = np.unique(np.concatenate([np.arange(0, 300), np.arange(300, T + 1, 20)]))
    cals = {o: rule(o, 20) for o in OPTS}
    runs = []
    for m in MS:
        for o in OPTS:
            for sd in SEEDS[:4]:
                runs.append(dict(group="proto", opt=o, m=m, sigma=sf.SIGMA0, kappa=1.0, eta=cals[o]["eta_rule"],
                                 eta_eff=cals[o]["eta_eff"], seed=sd, init_scale=1.0))
    for kap in (0.25, 4.0, 16.0, 64.0):
        for o in OPTS:
            if o == "sgd" and kap > 4:
                continue
            for sd in SEEDS[:2]:
                runs.append(dict(group="kappa", opt=o, m=20, sigma=sf.SIGMA0, kappa=kap, eta=kap * cals[o]["eta_rule"],
                                 eta_eff=kap * cals[o]["eta_eff"], seed=sd, init_scale=1.0))
    for m in (5, 20, 100):
        for o in OPTS:
            for sd in SEEDS[:2]:
                runs.append(dict(group="free", opt=o, m=m, sigma=0.0, kappa=1.0, eta=cals[o]["eta_rule"],
                                 eta_eff=cals[o]["eta_eff"], seed=sd, init_scale=1.0))
    res = batch(runs, tsub=tsub)
    rows = []
    keyf = lambda r: (r["group"], r["opt"], r["m"], r["kappa"])
    keys = []
    for r in runs:
        if keyf(r) not in keys:
            keys.append(keyf(r))
    curves = {}
    for key in keys:
        ix = np.array([i for i, r in enumerate(runs) if keyf(r) == key])
        r0 = runs[ix[0]]
        prob = sf.Problem(D, K, 1, r0["m"], sigma=max(r0["sigma"], 1e-12))
        thc = res["theta"][ix].mean(0)
        imin = int(np.argmin(thc))
        row = dict(group=key[0], opt=key[1], m=key[2], kappa=key[3], sigma=r0["sigma"], eta=r0["eta"],
                   eta_eff=r0["eta_eff"], n_seeds=len(ix),
                   E_align=float(res["E_align"][ix].mean()), E_align_sd=float(res["E_align"][ix].std(ddof=1)),
                   Std_align=float(res["Std_align"][ix].mean()),
                   loss_late=float(res["loss_late"][ix].mean()), loss_late_sd=float(res["loss_late"][ix].std(ddof=1)),
                   theta0=float(thc[0]), theta_min=float(thc[imin]), t_min=int(tsub[imin]),
                   gn_true_late=float(res["gn_true_late"][ix].mean()), gn_stoch_late=float(res["gn_stoch_late"][ix].mean()),
                   ratio1=float(prob.ratio(1)), ratio2=float(prob.ratio(2)))
        if r0["sigma"] > 0 and r0["eta_eff"] * 100 < 2:
            row["thm16_at_eta_eff"] = float(prob.theta_inf(r0["eta_eff"]))
        rows.append(row)
        tag = "{}_{}_m{}_k{}".format(*key)
        curves[tag + "__theta"] = thc
        curves[tag + "__loss"] = res["loss"][ix].mean(0)
        print(f"{tag}: eta={row['eta']:.4g} E[Align]={row['E_align']:.4f}+-{row['E_align_sd']:.4f} "
              f"thm16@eff={row.get('thm16_at_eta_eff', float('nan')):.4f} r1={row['ratio1']:.4f} r2={row['ratio2']:.5f} "
              f"min={row['theta_min']:.4f}@{row['t_min']} loss_late={row['loss_late']:.4g} "
              f"|g_true|/|g_stoch|={row['gn_true_late'] / max(row['gn_stoch_late'], 1e-300):.3f}", flush=True)
    sf.save_json(os.path.join(sf.RES, "e1_n1.json"),
                 dict(d=D, k=K, T=T, steady=STEADY, seeds=SEEDS, calibration=cals, rows=rows))
    np.savez_compressed(os.path.join(sf.RES, "e1_n1_curves.npz"), t=tsub, **curves)
    cpu.done(n_runs=len(runs))


if __name__ == "__main__":
    main()
