"""
tune_lr.py -- learning-rate tuning of the EXACT filters (sgd, sgdm, muon_exact, ht_exact).

For every (m, sigma) the constant learning rate is chosen on a grid to minimise the mean loss over
the last third of a T_TUNE-step run on the tuning seed (TUNE_SEED, never used for evaluation).
The approximations inherit the learning rate of the exact filter they approximate
(muon family: muon_ns5, ech_*;  ht family: ht_ns, ht_interval, ht_avg, ht_stream*).

Output: results/tuned_lr.json  (full grid of late losses + the selected lr per family).
Run:    nice -n 10 python3 tune_lr.py          (~3 CPU-min, 2 worker processes)
"""
import json
import os
import sys
import time
from multiprocessing import Pool

import numpy as np

import config as cfg
import spfilters as sp


def tune_one(args):
    m, sigma = args
    model = sp.QuadM2(cfg.D, cfg.K, cfg.N, m, seed=cfg.TUNE_SEED)
    W0 = model.init_W(cfg.TUNE_SEED)
    out = {}
    fams = {'sgd': ('sgd', [c / model.lam[0] for c in cfg.LR_GRID_SGD_C]),
            'sgdm': ('sgdm', [c / model.lam[0] for c in cfg.LR_GRID_SGD_C]),
            'muon': ('muon_exact', cfg.LR_GRID_SPECTRAL),
            'ht': ('ht_exact', cfg.LR_GRID_SPECTRAL)}
    for fam, (name, grid) in fams.items():
        rows = []
        for lr in grid:
            opt = sp.make_opt(name, (cfg.D, cfg.N), cfg.K, seed=cfg.TUNE_SEED)
            r = sp.run(model, opt, lr, cfg.T_TUNE, sigma, W0, noise_seed=cfg.TUNE_SEED,
                       rec_every=cfg.REC_EVERY)
            L = r['loss']
            nlate = len(L) // 3
            late = float(np.mean(L[-nlate:])) if not r['diverged'] else float('inf')
            rows.append(dict(lr=float(lr), late_loss=late, diverged=bool(r['diverged']),
                             late_theta=float(np.nanmean(r['theta'][-nlate:]))))
        best = min(rows, key=lambda x: x['late_loss'])
        out[fam] = dict(grid=rows, lr=best['lr'], late_loss=best['late_loss'],
                        at_grid_edge=bool(best['lr'] in (grid[0], grid[-1])))
    return (m, sigma, out)


if __name__ == '__main__':
    t0 = time.time()
    jobs = [(m, s) for m in cfg.MS for s in cfg.SIGMAS]
    with Pool(2) as pool:
        res = pool.map(tune_one, jobs, chunksize=1)
    table = {}
    for m, s, out in res:
        table[f'm{m}_s{s}'] = out
        print(f"m={m:4d} sigma={s:<5}", '  '.join(
            f"{fam}: lr={out[fam]['lr']:.4g} L={out[fam]['late_loss']:.3g}{'*' if out[fam]['at_grid_edge'] else ''}"
            for fam in out))
    meta = dict(D=cfg.D, K=cfg.K, N=cfg.N, T_TUNE=cfg.T_TUNE, TUNE_SEED=cfg.TUNE_SEED,
                criterion='mean loss over last third of T_TUNE steps', wall_s=time.time() - t0)
    json.dump(dict(meta=meta, table=table), open(os.path.join(cfg.RES, 'tuned_lr.json'), 'w'), indent=1)
    print('wall', time.time() - t0, 's   (* = optimum at the edge of the grid)')
