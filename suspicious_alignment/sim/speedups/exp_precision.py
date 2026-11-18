"""
exp_precision.py -- does reduced precision change the conclusions?

The originals run Newton-Schulz in bfloat16 and the SVD / Gram-root / stream paths in float32; our
main experiments use float64.  Two checks:

 (a) static fidelity: transfer and off-diagonal energy of NS5 Muon, HTMuon-NS and stream-QR in
     float64 / float32 / emulated bfloat16 (float32 arithmetic, every operation result rounded to
     bfloat16) on the geometric and spiked spectra of exp_s1_static.py;
 (b) trajectories: muon_ns5 (f64, f32, bf16), ht_exact / ht_ns / ht_stream (f64, f32) on model M2,
     m in {100, 500}, sigma in {0, 0.3}, seeds 0 and 1, same learning rates and noise streams as S2.
     Only the filter runs in reduced precision; parameters and momentum stay in float64.

Output: results/precision.json, figs/precision_transfer.png
Run:    nice -n 10 python3 exp_precision.py        (~3 CPU-min, 2 worker processes)
"""
import json
import os
import time
from multiprocessing import Pool

import numpy as np
import plotstyle
import matplotlib.pyplot as plt

import config as cfg
import spfilters as sp
from exp_s1_static import spectra

plotstyle.apply()
D, N, K, P = cfg.D, cfg.N, cfg.K, 0.125
TRAJ = [('muon_ns5', 'f64'), ('muon_ns5', 'f32'), ('muon_ns5', 'bf16'),
        ('ht_exact', 'f64'), ('ht_exact', 'f32'),
        ('ht_ns', 'f64'), ('ht_ns', 'f32'), ('ht_ns', 'bf16'),
        ('ht_stream', 'f64'), ('ht_stream', 'f32')]


def static_part():
    specs = spectra()
    out = {}
    arrays = {}
    for sname in ['geom6', 'spiked_0.01', 'spiked_0.0001', 'spiked_1e-06', 'flat']:
        S = specs[sname]
        rng = np.random.default_rng([0, 11])
        U = sp.haar(D, N, rng)
        Vh = sp.haar(N, N, rng).T
        G = (U * S[None, :]) @ Vh
        ex_muon = U @ Vh
        ex_ht = (U * (S ** P)[None, :]) @ Vh
        res = {}
        for prec in ['f64', 'f32', 'bf16']:
            o = np.asarray(sp.zeropower_via_newtonschulz5(G, 5, prec), dtype=np.float64)
            t, off = sp.transfer(o, U, Vh)
            res[f'muon_ns5_{prec}'] = dict(rel=float(sp.rel_err(o, ex_muon)), off=float(off),
                                           head=float(t[:K].mean()), bulk=float(t[K:].mean()),
                                           bulk_out_norm=float(np.sqrt(max(np.sum(o * o) - np.sum((U[:, :K].T @ o) ** 2), 0.0))))
            arrays[f'{sname}__muon_ns5_{prec}'] = t
            opt = sp.Opt('ht_ns', (D, N), prec=prec)
            o = opt.filter(G)
            t, off = sp.transfer(o, U, Vh)
            res[f'ht_ns_{prec}'] = dict(rel=float(sp.rel_err(o, ex_ht)), off=float(off),
                                        head=float(t[:K].mean()), bulk=float(t[K:].mean()))
            arrays[f'{sname}__ht_ns_{prec}'] = t
            if prec != 'bf16':
                V_ = None
                for j in range(100):
                    o, V_ = sp.msign_generalized_ht_v2_stream_qr(G, V_, p=P, prec=prec)
                o = np.asarray(o, dtype=np.float64)
                t, off = sp.transfer(o, U, Vh)
                res[f'ht_stream_j100_{prec}'] = dict(rel=float(sp.rel_err(o, ex_ht)), off=float(off),
                                                     head=float(t[:K].mean()), bulk=float(t[K:].mean()))
                o = np.asarray(sp.msign_generalized_ht_v2(G, P, prec), dtype=np.float64)
                res[f'ht_exact_{prec}'] = dict(rel=float(sp.rel_err(o, ex_ht)))
        out[sname] = res
        arrays[f'{sname}__sigma'] = S
    return out, arrays


def traj_job(args):
    m, sigma, seed = args
    tuned = json.load(open(os.path.join(cfg.RES, 'tuned_lr.json')))['table'][f'm{m}_s{sigma}']
    model = sp.QuadM2(D, K, N, m, seed=seed)
    W0 = model.init_W(seed)
    reg = sp.optimizer_registry(K)
    rows = {}
    for name, prec in TRAJ:
        fam = reg[name][0]
        opt = sp.make_opt(name, (D, N), K, seed=seed, prec=prec)
        r = sp.run(model, opt, tuned[fam]['lr'], cfg.T_EVAL, sigma, W0, noise_seed=seed, rec_every=cfg.REC_EVERY)
        nrec = len(r['upd_dom'])
        lo = (2 * nrec) // 3
        rows[f'{name}_{prec}'] = dict(theta_late=float(np.nanmean(r['theta'][lo:])), loss_late=float(np.nanmean(r['loss'][lo:])),
                                      upd_late=float(np.nanmean(r['upd_dom'][lo:])), diverged=bool(r['diverged']),
                                      theta_min=float(np.nanmin(r['theta'])))
    return dict(m=m, sigma=sigma, seed=seed, rows=rows)


def main():
    t0 = time.time()
    static, arrays = static_part()
    jobs = [(m, s, seed) for m in [100, 500] for s in [0.0, 0.3] for seed in [0, 1]]
    with Pool(2) as pool:
        traj = pool.map(traj_job, jobs, chunksize=1)
    json.dump(dict(static=static, traj=traj, wall_s=time.time() - t0),
              open(os.path.join(cfg.RES, 'precision.json'), 'w'), indent=1)
    np.savez_compressed(os.path.join(cfg.RES, 'precision.npz'), **arrays)

    S = arrays['geom6__sigma']
    fig, ax = plt.subplots(1, 2, figsize=(10.5, 4.0), sharey=True)
    for a, fam, ttl in [(ax[0], 'muon_ns5', 'NS5 Muon'), (ax[1], 'ht_ns', 'HTMuon-NS')]:
        if fam == 'muon_ns5':
            a.loglog(S, np.ones_like(S), color=plotstyle.INK, lw=2, label='exact filter')
        else:
            a.loglog(S, S ** P, color=plotstyle.INK, lw=2, label='exact filter')
        for prec, mk in [('f64', 'o'), ('f32', 's'), ('bf16', '^')]:
            t = arrays[f'geom6__{fam}_{prec}']
            a.loglog(S, np.abs(t), mk + '-', ms=3.5, label=f'{prec}  (|transfer|)')
        a.set_xlabel('singular value (top = 1)')
        a.set_title(f'{ttl}: geometric spectrum 1 ... 1e-6, 200 x 40')
        a.legend()
    ax[0].set_ylabel('|u_i^T F(G) v_i|')
    fig.tight_layout()
    fig.savefig(os.path.join(cfg.FIG, 'precision_transfer.png'), dpi=130)
    plt.close(fig)
    print('wall', time.time() - t0)


if __name__ == '__main__':
    main()
