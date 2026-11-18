"""E1 extra checks.

 limit : noise-free limit cycles as a function of the number of columns n (M2, d=200, k=20, sigma=0,
         W0 ~ 0.01 N(0,1), T=2000, seed 0).  Tests the prediction
             theta_late = sum_{i<=k} lam_i^q / sum_{i<=min(n,d)} lam_i^q ,   q = 2/(1-p)   (Muon: p=0, q=2)
         i.e. the limit cycle of a rank-n spectral-filter update lives in the top-n Hessian eigen-directions
         with per-direction amplitude ∝ lam^(p/(1-p)).  Also records where the gradient energy sits
         (rows < k, rows k..n-1, rows >= n).
 stat  : stationarity cross-check of the 'late' runs: start from SGD's exact stationary law instead of zero
         (sigma=0.5, kappa=1, m in {100, 200}, T=1500, 2 seeds).
Usage:  python3 e1_extra.py limit|stat
"""
import os
import sys

import numpy as np

import specfilt as sf
import e1_trajectories as e1

D, K = 200, 20


def part_limit():
    rows = []
    T = 2000
    cfgs = []
    for m in (5, 20):
        for n in (20, 50, 100):
            for o in ("muon", "ht0.125", "ht0.5"):
                cfgs.append((m, n, o))
    cfgs.append((5, 200, "muon"))
    cfgs.append((20, 1, "muon"))
    cfgs.append((20, 5, "muon"))
    for m, n, o in cfgs:
        prob = sf.Problem(D, K, n, m, sigma=0.0)
        eta = e1.cal(o)["eta_rule"]          # the step only sets the scale of the limit cycle
        Tn = T if n < 200 else 1200
        out = sf.run(prob, o, eta, Tn, [0], init_scale=0.01, log_idx=np.arange(0, Tn, 10), true_sv_stride=10 ** 6)
        ls = sf.late_stats(out)
        p = sf.parse_opt(o)[1] or 0.0
        q = 2.0 / (1.0 - p)
        lam = prob.lam
        nn = min(n, D)
        pred = (lam[:min(K, nn)] ** q).sum() / (lam[:nn] ** q).sum()
        # gradient energy by eigen-direction block, averaged over the last 200 steps (re-run tail cheaply)
        W = out["W_final"][0]
        acc = np.zeros(D)
        for _ in range(200):
            G = prob.grad(W)
            acc += (G * G).sum(1)
            Dl, _ = sf.apply_filter(G, o)
            W = W - eta * Dl
        tot = acc.sum()
        e_blocks = [acc[:K].sum() / tot, acc[K:max(nn, K)].sum() / tot, acc[max(nn, K):].sum() / tot]
        # theta over the same 200-step tail (ratio of time-averaged energies)
        rows.append(dict(m=m, n=n, opt=o, T=Tn, eta=eta, theta_late=float(ls["theta"][0]), pred_topn=float(pred),
                         ratio2=float(prob.ratio(2)), ratio_q=float(prob.ratio(q)), q=q,
                         theta_tail_energy=float(e_blocks[0]), energy_rows_k_to_n=float(e_blocks[1]),
                         energy_rows_ge_n=float(e_blocks[2]), loss_late=float(ls["loss"][0]),
                         upd_frac_late=float(ls["upd_frac"][0])))
        r = rows[-1]
        print(f"m={m} n={n} {o}: theta_late={r['theta_late']:.5f} pred(top-n, q={q:.2f})={pred:.5f} "
              f"ratio_q(all d)={r['ratio_q']:.5f} energy[D, k..n, >=n]={np.round(e_blocks, 5)} updD={r['upd_frac_late']:.3f}",
              flush=True)
    sf.save_json(os.path.join(sf.RES, "e1_extra_limit.json"), dict(rows=rows))


def part_stat():
    rows, logs, ck = [], {}, {}
    for m in (100, 200):
        for o in ("sgd", "muon", "ht0.125", "ech20"):
            rows.append(e1.run_config(dict(opt=o, m=m, T=1500, seeds=[0, 1], init="stat"), logs, ck))
    sf.save_json(os.path.join(sf.RES, "e1_extra_stat.json"), dict(rows=rows))


if __name__ == "__main__":
    part = sys.argv[1]
    cpu = sf.CpuLog("e1_extra_" + part)
    {"limit": part_limit, "stat": part_stat}[part]()
    cpu.done()
