"""
exp_long.py -- is the "late-time" window of S2 (steps 1600..2400) stationary?

Re-runs a subset of the optimizers of S2 for a 4x longer horizon (T = 9600 steps) on seed 0 with
the same problem, initialisation, learning rate and noise stream as exp_s2_alignment.py (the first
2400 steps are therefore identical to the S2 run), and compares the alignment / loss averaged over
   window A = steps 1600..2400   (the "late" window of S2)
   window B = steps 6400..9600   (last third of the long run).
A variant whose late-time alignment in S2 is only a transient (it has not reached its loss floor
within 2400 steps: ech_r4_fro, ht_stream_r4) shows up as a large A-to-B change.

Output: results/long.json
Run:    nice -n 10 python3 exp_long.py        (~3 CPU-min, 2 worker processes)
"""
import json
import os
import time
from multiprocessing import Pool

import numpy as np

import config as cfg
import spfilters as sp

T_LONG = 9600
REC = 20
CONFIGS = [(20, 0.02), (100, 0.3)]
SEED = 0
OPTS = ['sgd', 'muon_exact', 'muon_ns5', 'ht_exact', 'ht_ns', 'ht_interval', 'ht_stream', 'ht_stream_rk',
        'ht_stream_r4', 'ech_r1', 'ech_r4', 'ech_r16', 'ech_rk', 'ech_r4_pol', 'ech_r4_fro', 'ech_rk_fro']


def job(args):
    m, sigma = args
    tuned = json.load(open(os.path.join(cfg.RES, 'tuned_lr.json')))['table'][f'm{m}_s{sigma}']
    model = sp.QuadM2(cfg.D, cfg.K, cfg.N, m, seed=SEED)
    W0 = model.init_W(SEED)
    reg = sp.optimizer_registry(cfg.K)
    rows = {}
    for name in OPTS:
        fam = reg[name][0]
        opt = sp.make_opt(name, (cfg.D, cfg.N), cfg.K, seed=SEED)
        r = sp.run(model, opt, tuned[fam]['lr'], T_LONG, sigma, W0, noise_seed=SEED, rec_every=REC)
        th, L, u = r['theta'], r['loss'], r['upd_dom']
        a0, a1 = 1600 // REC, 2400 // REC
        b0 = 6400 // REC
        rows[name] = dict(theta_A=float(np.nanmean(th[a0:a1])), theta_B=float(np.nanmean(th[b0:])),
                          theta_B_tsd=float(np.nanstd(th[b0:])),
                          loss_A=float(np.nanmean(L[a0:a1])), loss_B=float(np.nanmean(L[b0:])),
                          upd_A=float(np.nanmean(u[a0:a1])), upd_B=float(np.nanmean(u[b0:])),
                          diverged=bool(r['diverged']))
    return dict(m=m, sigma=sigma, seed=SEED, rows=rows)


if __name__ == '__main__':
    t0 = time.time()
    with Pool(2) as pool:
        res = pool.map(job, CONFIGS, chunksize=1)
    json.dump(dict(meta=dict(T=T_LONG, rec_every=REC, seed=SEED, wall_s=time.time() - t0), runs=res),
              open(os.path.join(cfg.RES, 'long.json'), 'w'), indent=1)
    for r in res:
        print(f"--- m = {r['m']}, sigma = {r['sigma']}")
        ex = {'muon': r['rows']['muon_exact'], 'ht': r['rows']['ht_exact']}
        reg = sp.optimizer_registry(cfg.K)
        for name, v in r['rows'].items():
            e = ex.get(reg[name][0])
            dA = v['theta_A'] - e['theta_A'] if e else float('nan')
            dB = v['theta_B'] - e['theta_B'] if e else float('nan')
            print(f"{name:13s} theta A={v['theta_A']:.4f} B={v['theta_B']:.4f} (tsd {v['theta_B_tsd']:.4f})  "
                  f"d_theta vs exact A={dA:+.4f} B={dB:+.4f}   loss A={v['loss_A']:.3g} B={v['loss_B']:.3g}")
    print('wall', time.time() - t0)
