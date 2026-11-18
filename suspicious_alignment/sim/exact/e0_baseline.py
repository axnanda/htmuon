"""E0 -- replication of Deng et al., Section 7 / Appendix B (constant-step SGD, d=500, k=50, eta=0.003,
sigma=0.5, T=30000, m in {5,...,500}).

(a) literal port of the authors' quad_sim.py (dense A = Q Lambda Q^T, legacy numpy RNG, same call order)
    for seeds 42 and 87;
(b) the same model in the eigenbasis (vectorised) for the seven seeds listed in quad_sim.py.
Statistic: E[Alignment] / Std[Alignment] = mean / std of theta_t over the last 10000 steps (as in quad_sim.py).

Usage:  python3 e0_baseline.py            (about 1.5 CPU-min)
"""
import os

import numpy as np

import specfilt as sf

D, K, ETA, SIGMA, T, STEADY = 500, 50, 0.003, 0.5, 30000, 10000
MS = [5, 10, 20, 50, 100, 200, 300, 400, 500]
SEEDS = [42, 87, 568, 12138, 1101, 70425, 4008001]
DENSE_SEEDS = [42, 87]


def dense_run(m, seed):
    """Port of quad_sim.py::simulate_quadratic_sgd (same RNG stream)."""
    np.random.seed(seed)
    lam = sf.deng_spectrum(D, K, m)
    Q, _ = np.linalg.qr(np.random.randn(D, D))
    A = Q @ np.diag(lam) @ Q.T
    w, V = np.linalg.eigh(A)
    V = V[:, np.argsort(w)[::-1]][:, :K]
    x = np.random.randn(D)
    loss = np.zeros(T + 1)
    al = np.zeros(T + 1)
    g = A @ x
    for t in range(T + 1):
        loss[t] = 0.5 * x @ g
        pg = V.T @ g
        al[t] = (pg @ pg) / (g @ g)
        if t == T:
            break
        x = x - ETA * (g + np.random.normal(0, SIGMA, D))
        g = A @ x
    return loss, al


def eig_runs():
    """All (m, seed) pairs at once in the eigenbasis."""
    R = len(MS) * len(SEEDS)
    lam = np.zeros((R, D))
    x = np.zeros((R, D))
    rngs = []
    for a, m in enumerate(MS):
        for b, sd in enumerate(SEEDS):
            r = a * len(SEEDS) + b
            lam[r] = sf.deng_spectrum(D, K, m)
            rng = np.random.default_rng([sd, m])
            x[r] = rng.standard_normal(D)
            rngs.append(rng)
    noise_rng = np.random.default_rng(20260118)
    loss = np.zeros((R, T + 1))
    al = np.zeros((R, T + 1))
    for t in range(T + 1):
        g = lam * x
        g2 = g * g
        loss[:, t] = 0.5 * (x * g).sum(1)
        al[:, t] = g2[:, :K].sum(1) / g2.sum(1)
        if t == T:
            break
        x = x - ETA * (g + SIGMA * noise_rng.standard_normal((R, D)))
    return loss, al


def summarize(loss, al):
    tmin = int(np.argmin(al))
    late = al[-STEADY:]
    return dict(theta0=al[0], theta_min=al[tmin], t_min=tmin, E_align=late.mean(), Std_align=late.std(),
                loss0=loss[0], loss_late=loss[-STEADY:].mean())


def main():
    cpu = sf.CpuLog("e0_baseline")
    rows = []
    curves = {}
    tsub = np.unique(np.concatenate([np.arange(0, 300), np.arange(300, T + 1, 20)]))
    # theory
    theory = {}
    for m in MS:
        prob = sf.Problem(D, K, 1, m, sigma=SIGMA)
        tt = np.arange(T - STEADY + 1, T + 1)
        th_fin = float(np.mean(prob.sgd_theta_bar(ETA, tt, 1.0)))
        theory[m] = dict(theta_inf=float(prob.theta_inf(ETA)), theta_bar_window=th_fin,
                         ratio1=float(prob.ratio(1)), ratio2=float(prob.ratio(2)),
                         loss_inf=float(0.5 * (prob.H * prob.beta(ETA)).sum()),
                         loss_bar_window=float(np.mean(prob.sgd_loss_bar(ETA, tt, 1.0))),
                         lam_k=float(prob.lam[K - 1]), lam_k1=float(prob.lam[K]), lam_d=float(prob.lam[-1]),
                         tau_slowest_steps=float(1 / (2 * ETA * prob.lam[-1])),
                         eta_bound_gap=float(2 * (prob.lam[K - 1] - prob.lam[K]) / (prob.lam[0] ** 2 - prob.lam[-1] ** 2)),
                         theta_bar_curve=prob.sgd_theta_bar(ETA, tsub, 1.0))
    # (a) dense literal port
    for sd in DENSE_SEEDS:
        for m in MS:
            loss, al = dense_run(m, sd)
            s = summarize(loss, al)
            rows.append(dict(kind="dense", m=m, seed=sd, **s))
            if sd == 42:
                curves[f"dense_m{m}_loss"] = loss[tsub]
                curves[f"dense_m{m}_theta"] = al[tsub]
            print(f"dense m={m:4d} seed={sd}: theta0={s['theta0']:.4f} min={s['theta_min']:.4f}@{s['t_min']} "
                  f"E[Align]={s['E_align']:.4f} (Thm16 {theory[m]['theta_inf']:.4f}, finite-T {theory[m]['theta_bar_window']:.4f})",
                  flush=True)
    # (b) eigenbasis, all seeds
    loss, al = eig_runs()
    for a, m in enumerate(MS):
        for b, sd in enumerate(SEEDS):
            r = a * len(SEEDS) + b
            rows.append(dict(kind="eig", m=m, seed=sd, **summarize(loss[r], al[r])))
        curves[f"eig_m{m}_theta_seedmean"] = al[a * len(SEEDS):(a + 1) * len(SEEDS)][:, tsub].mean(0)
        curves[f"eig_m{m}_loss_seedmean"] = loss[a * len(SEEDS):(a + 1) * len(SEEDS)][:, tsub].mean(0)
    table = []
    for m in MS:
        e = [r for r in rows if r["kind"] == "eig" and r["m"] == m]
        dn = [r for r in rows if r["kind"] == "dense" and r["m"] == m]
        th = theory[m]
        table.append(dict(
            m=m, E_align_mean=float(np.mean([r["E_align"] for r in e])),
            E_align_sd=float(np.std([r["E_align"] for r in e], ddof=1)),
            Std_align_mean=float(np.mean([r["Std_align"] for r in e])),
            E_align_dense=[float(r["E_align"]) for r in dn],
            theta_min_mean=float(np.mean([r["theta_min"] for r in e])),
            t_min_median=float(np.median([r["t_min"] for r in e])),
            theta0_mean=float(np.mean([r["theta0"] for r in e])),
            loss_late_mean=float(np.mean([r["loss_late"] for r in e])),
            **{k_: v for k_, v in th.items() if k_ != "theta_bar_curve"}))
        curves[f"theory_m{m}_theta_bar"] = th["theta_bar_curve"]
    os.makedirs(sf.RES, exist_ok=True)
    np.savez_compressed(os.path.join(sf.RES, "e0_baseline_curves.npz"), t=tsub, **curves)
    sf.save_json(os.path.join(sf.RES, "e0_baseline.json"),
                 dict(config=dict(d=D, k=K, eta=ETA, sigma=SIGMA, T=T, steady=STEADY, ms=MS, seeds=SEEDS,
                                  dense_seeds=DENSE_SEEDS), table=table, rows=rows))
    print("\n m  | E[Align] eig (7 seeds) | dense 42/87      | Thm16  | finite-T | sum lam ratio | sum lam^2 ratio | theta_min")
    for r in table:
        print(f"{r['m']:4d}| {r['E_align_mean']:.4f} +- {r['E_align_sd']:.4f}      | "
              f"{r['E_align_dense'][0]:.4f} {r['E_align_dense'][1]:.4f} | {r['theta_inf']:.4f} | {r['theta_bar_window']:.4f}   | "
              f"{r['ratio1']:.4f}        | {r['ratio2']:.5f}        | {r['theta_min_mean']:.4f}@{r['t_min_median']:.0f}")
    cpu.done()


if __name__ == "__main__":
    main()
