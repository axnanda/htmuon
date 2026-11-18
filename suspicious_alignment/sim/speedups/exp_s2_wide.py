"""
exp_s2_wide.py -- robustness check of S2 on a WIDE layer (n >= d), the setting of
notes/research/filter_spec.md: W in R^{100 x 120}, k = 10, m = 100, sigma in {0, 0.3}, seeds {0, 1}.

In a wide layer every Hessian eigen-direction has its own singular value (d = 100 singular values,
90 of them bulk), the shape factor is 1, and the Gram matrix of HTMuon-NS is n x n = 120 x 120 with
20 null directions.  Learning rates are re-tuned for the exact filters on the tuning seed with the
same criterion as tune_lr.py; a reduced set of optimizers is run.

Output: results/s2_wide.json
Run:    nice -n 10 python3 exp_s2_wide.py        (~4 CPU-min, 2 worker processes)
"""
import json
import os
import time
from multiprocessing import Pool

import numpy as np

import config as cfg
import spfilters as sp

D, K, N, M = 100, 10, 120, 100
SIGMAS = [0.0, 0.3]
SEEDS = [0, 1]
OPTS = ['muon_exact', 'muon_ns5', 'ech_r4', 'ech_rk', 'ech_rk_ideal', 'ech_r4_ideal',
        'ht_exact', 'ht_ns', 'ht_interval', 'ht_stream', 'ht_stream_rk']
EXACT = {'muon': 'muon_exact', 'ht': 'ht_exact'}


def tune(sigma):
    model = sp.QuadM2(D, K, N, M, seed=cfg.TUNE_SEED)
    W0 = model.init_W(cfg.TUNE_SEED)
    out = {}
    for fam, name in EXACT.items():
        best = None
        rows = []
        for lr in cfg.LR_GRID_SPECTRAL:
            opt = sp.make_opt(name, (D, N), K, seed=cfg.TUNE_SEED)
            r = sp.run(model, opt, lr, cfg.T_TUNE, sigma, W0, noise_seed=cfg.TUNE_SEED, rec_every=cfg.REC_EVERY)
            L = r['loss']
            late = float(np.mean(L[-(len(L) // 3):])) if not r['diverged'] else float('inf')
            rows.append((lr, late))
            if best is None or late < best[1]:
                best = (lr, late)
        out[fam] = dict(lr=best[0], grid=rows)
    return sigma, out


def job(args):
    sigma, seed, tuned = args
    model = sp.QuadM2(D, K, N, M, seed=seed)
    W0 = model.init_W(seed)
    reg = sp.optimizer_registry(K)
    rows = {}
    for name in OPTS:
        fam = reg[name][0]
        opt = sp.make_opt(name, (D, N), K, seed=seed)
        r = sp.run(model, opt, tuned[fam]['lr'], cfg.T_EVAL, sigma, W0, noise_seed=seed, rec_every=cfg.REC_EVERY)
        nrec = len(r['upd_dom'])
        lo = (2 * nrec) // 3
        th = r['theta']
        rows[name] = dict(lr=tuned[fam]['lr'], theta0=float(th[0]), theta_late=float(np.nanmean(th[lo:])),
                          omt_late=float(max(np.nanmean(1 - th[lo:]), 1e-16)),
                          theta_min=float(np.nanmin(th)), t_min=float(np.nanargmin(th) * cfg.REC_EVERY),
                          loss_late=float(np.nanmean(r['loss'][lo:])), upd_late=float(np.nanmean(r['upd_dom'][lo:])),
                          upd_early=float(np.nanmean(r['upd_dom'][:20])),
                          diverged=bool(r['diverged']))
    return dict(sigma=sigma, seed=seed, rows=rows)


def main():
    t0 = time.time()
    with Pool(2) as pool:
        tuned = dict(pool.map(tune, SIGMAS))
        res = pool.map(job, [(s, seed, tuned[s]) for s in SIGMAS for seed in SEEDS], chunksize=1)
    json.dump(dict(meta=dict(D=D, K=K, N=N, M=M, T=cfg.T_EVAL, wall_s=time.time() - t0),
                   tuned={str(s): v for s, v in tuned.items()}, runs=res),
              open(os.path.join(cfg.RES, 's2_wide.json'), 'w'), indent=1)
    for s in SIGMAS:
        print(f'--- sigma = {s}  (lr muon {tuned[s]["muon"]["lr"]}, ht {tuned[s]["ht"]["lr"]})')
        for name in OPTS:
            v = [r['rows'][name] for r in res if r['sigma'] == s]
            print(f"{name:14s} theta_late={np.mean([x['theta_late'] for x in v]):.5f} 1-theta={np.mean([x['omt_late'] for x in v]):.2e} "
                  f"upd_D early={np.mean([x['upd_early'] for x in v]):.3f} late={np.mean([x['upd_late'] for x in v]):.3f} "
                  f"loss_late={np.mean([x['loss_late'] for x in v]):.3g} theta_min={np.mean([x['theta_min'] for x in v]):.3f}@{np.mean([x['t_min'] for x in v]):.0f}")
    print('wall', time.time() - t0)


if __name__ == '__main__':
    main()
