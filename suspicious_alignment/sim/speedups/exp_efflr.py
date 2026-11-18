"""
exp_efflr.py -- control experiment: is the (small) alignment shift of NS5-Muon / HTMuon-NS /
HTMuon-interval explained by their overall GAIN (an effective learning-rate factor) rather than by
the shape of their spectral transfer?

For each configuration the gain g = <F_approx(M), F_exact(M)> / ||F_exact(M)||^2 of the approximation,
measured in the late window of the shadow experiment (results/shadow_summary.json), is used to run the
EXACT filter at the learning rate lr * g.  If the approximation only rescales the step, the exact
filter at lr * g reproduces the approximation's late-time alignment.

Output: results/efflr.json
Run:    nice -n 10 python3 exp_efflr.py      (needs exp_shadow.py + analyze_shadow.py and the S2 results; ~2 CPU-min)
"""
import json
import os
import time
from multiprocessing import Pool

import numpy as np

import config as cfg
import spfilters as sp

CONFIGS = [(5, 0.02), (5, 0.3), (100, 0.02), (100, 0.3), (500, 0.3)]
PAIRS = [('muon', 'muon_exact', 'muon_ns5', 'muon_ns5'),
         ('ht', 'ht_exact', 'ht_ns', 'ht_ns'),
         ('ht', 'ht_exact', 'ht_interval', 'ht_avg')]      # gain of the interval scheme = gain of its time average


def job(args):
    m, sigma = args
    tuned = json.load(open(os.path.join(cfg.RES, 'tuned_lr.json')))['table'][f'm{m}_s{sigma}']
    shadow = json.load(open(os.path.join(cfg.RES, 'shadow_summary.json')))
    out = []
    for fam, exact, approx, gain_key in PAIRS:
        gain = shadow[f'{fam}_m{m}_s{sigma}']['late']['stats'][gain_key]['gain']
        for seed in cfg.SEEDS:
            model = sp.QuadM2(cfg.D, cfg.K, cfg.N, m, seed=seed)
            W0 = model.init_W(seed)
            opt = sp.make_opt(exact, (cfg.D, cfg.N), cfg.K, seed=seed)
            r = sp.run(model, opt, tuned[fam]['lr'] * gain, cfg.T_EVAL, sigma, W0, noise_seed=seed, rec_every=cfg.REC_EVERY)
            nrec = len(r['upd_dom'])
            lo = (2 * nrec) // 3
            z = np.load(os.path.join(cfg.RES, f's2_m{m}_s{sigma}_seed{seed}.npz'))
            names = [str(x) for x in z['names']]
            th_approx = float(np.nanmean(z['theta'][names.index(approx)][lo:nrec + 1]))
            th_exact = float(np.nanmean(z['theta'][names.index(exact)][lo:nrec + 1]))
            out.append(dict(m=m, sigma=sigma, seed=seed, approx=approx, gain=gain,
                            theta_exact_lr=th_exact, theta_approx=th_approx,
                            theta_exact_lr_times_gain=float(np.nanmean(r['theta'][lo:])),
                            loss_exact_lr_times_gain=float(np.nanmean(r['loss'][lo:])),
                            loss_approx=float(np.nanmean(z['loss'][names.index(approx)][lo:nrec + 1]))))
    return out


if __name__ == '__main__':
    t0 = time.time()
    with Pool(2) as pool:
        res = sum(pool.map(job, CONFIGS, chunksize=1), [])
    json.dump(dict(rows=res, wall_s=time.time() - t0), open(os.path.join(cfg.RES, 'efflr.json'), 'w'), indent=1)
    print(f"{'m':>4} {'sigma':>5} {'approx':12s} {'gain':>6} {'d_theta approx-exact':>22} {'d_theta approx-exact(lr*gain)':>30}")
    for m, sigma in CONFIGS:
        for _, _, approx, _ in PAIRS:
            rows = [r for r in res if r['m'] == m and r['sigma'] == sigma and r['approx'] == approx]
            d1 = np.array([r['theta_approx'] - r['theta_exact_lr'] for r in rows])
            d2 = np.array([r['theta_approx'] - r['theta_exact_lr_times_gain'] for r in rows])
            print(f"{m:4d} {sigma:5.2f} {approx:12s} {rows[0]['gain']:6.3f} {d1.mean():+12.4f} ({d1.std(ddof=1):.4f}) {d2.mean():+18.4f} ({d2.std(ddof=1):.4f})")
    print('wall', time.time() - t0)
