"""
exp_s2_alignment.py -- S2: alignment outcomes of every optimizer on the Deng-style quadratic (M2).

For each (m, sigma, seed) all optimizers of `spfilters.optimizer_registry` are run for T_EVAL steps
from the same W0, on the same problem and with the SAME noise stream (common random numbers), at
the learning rate tuned for the exact filter of their family (results/tuned_lr.json).

Recorded every REC_EVERY steps: loss, Deng's alignment theta_t = ||P^D A W||^2/||A W||^2 of the TRUE
gradient, and the fraction of the update in the dominant Hessian subspace ||P^D O||^2/||O||^2.

Output: results/s2_m{m}_s{sigma}_seed{seed}.npz
Run (two invocations, each ~13 CPU-min on 2 worker processes; ~7 min wall on an idle machine):
    nice -n 10 python3 exp_s2_alignment.py --ms 5 20
    nice -n 10 python3 exp_s2_alignment.py --ms 100 500
Existing result files are skipped (the script resumes); use --force to recompute.
then  python3 analyze_s2.py
"""
import argparse
import json
import os
import time
from multiprocessing import Pool

import numpy as np

import config as cfg
import spfilters as sp


def job(args):
    m, sigma, seed = args
    t0 = time.time()
    tuned = json.load(open(os.path.join(cfg.RES, 'tuned_lr.json')))['table'][f'm{m}_s{sigma}']
    model = sp.QuadM2(cfg.D, cfg.K, cfg.N, m, seed=seed)
    W0 = model.init_W(seed)
    reg = sp.optimizer_registry(cfg.K)
    names = list(reg.keys())
    loss, theta, upd, lrs, div, secs, nfb = [], [], [], [], [], [], []
    for name in names:
        fam = reg[name][0]
        lr = tuned[fam]['lr']
        opt = sp.make_opt(name, (cfg.D, cfg.N), cfg.K, seed=seed)
        t1 = time.time()
        fb0 = sp.SVD_FALLBACKS
        r = sp.run(model, opt, lr, cfg.T_EVAL, sigma, W0, noise_seed=seed, rec_every=cfg.REC_EVERY)
        secs.append(time.time() - t1)
        nfb.append(sp.SVD_FALLBACKS - fb0)      # gesdd failures handled by the gesvd fallback
        loss.append(r['loss'])
        theta.append(r['theta'])
        upd.append(r['upd_dom'])
        lrs.append(lr)
        div.append(r['diverged'])
    np.savez_compressed(os.path.join(cfg.RES, f's2_m{m}_s{sigma}_seed{seed}.npz'),
                        names=np.array(names), family=np.array([reg[n][0] for n in names]),
                        loss=np.array(loss), theta=np.array(theta), upd_dom=np.array(upd),
                        lr=np.array(lrs), diverged=np.array(div), secs=np.array(secs),
                        svd_fallbacks=np.array(nfb),
                        lam=model.lam, m=m, sigma=sigma, seed=seed,
                        T=cfg.T_EVAL, rec_every=cfg.REC_EVERY)
    return (m, sigma, seed, time.time() - t0)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--ms', type=int, nargs='+', default=cfg.MS)
    ap.add_argument('--seeds', type=int, nargs='+', default=cfg.SEEDS)
    ap.add_argument('--sigmas', type=float, nargs='+', default=cfg.SIGMAS)
    ap.add_argument('--force', action='store_true', help='recompute existing result files')
    a = ap.parse_args()
    jobs = [(m, s, seed) for m in a.ms for s in a.sigmas for seed in a.seeds]
    if not a.force:      # resume: skip configurations whose result file already exists
        jobs = [j for j in jobs if not os.path.exists(os.path.join(cfg.RES, f's2_m{j[0]}_s{j[1]}_seed{j[2]}.npz'))]
    print(len(jobs), 'jobs to run', flush=True)
    t0 = time.time()
    with Pool(2) as pool:
        for m, s, seed, dt in pool.imap_unordered(job, jobs, chunksize=1):
            print(f'done m={m} sigma={s} seed={seed} in {dt:.1f}s', flush=True)
    print('wall', time.time() - t0)
