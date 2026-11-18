"""
exp_s3_frozen.py -- S3 (part b) and S1 (part c): projected-update test and bulk fidelity at FROZEN
synthetic states with prescribed (very high) alignment.

State: W* = Q [alpha Z_D ; gamma Z_B], Z Gaussian, alpha/gamma chosen such that Deng's alignment is
theta and the true gradient has rms entry 1 (||A W*||_F^2 = d n).  The optimizer's momentum rule is
fed g_t = A W* + sigma Xi_t (fresh noise each step, W* not moved): after WARM steps the momentum
matrix M_t is stationary around A W* and the stateful filters have their stationary state.  Over
MEAS further steps we average, for every filter output O (shape factor included),
      a_S = <P^S A W*, O>,   b_S = <P^S O, A P^S O>,   S in {D, B},
which give the expected one-step loss change of the projected update exactly:
      E[L(W* - eta P^S O) - L(W*)] = -eta a_S + eta^2 b_S / 2,    eta_S^loss = 2 a_S / b_S.
With sigma = 0 the input is static (the stateful filters are then fully converged -- best case).

Sanity check included: plain SGD without momentum reproduces Deng's Theorem (thm:proj-loss-corr)
      eta_S^loss = 2 s^S / (tau^S + n sigma^2 sum_{i in S} lam_i).

Output: results/s3_frozen.json ; figs/s3_frozen_thresholds.png
Run:    nice -n 10 python3 exp_s3_frozen.py        (~3 CPU-min, 2 worker processes)
"""
import json
import os
import time
from multiprocessing import Pool

import numpy as np

import config as cfg
import spfilters as sp
from exp_shadow import measure, KEYS

P = 0.125
MS = [20, 100, 500]
ONE_MINUS_THETA = [1e-1, 1e-2, 1e-3, 1e-4, 1e-5, 1e-6, 1e-8]
SIGMAS = [0.0, 0.01, 0.3]
SEEDS = [0, 1]
WARM, MEAS = 150, 100


def make_state(model, theta, seed):
    d, k, n = model.d, model.k, model.n
    rng = np.random.default_rng([int(seed), 5])
    Z = rng.standard_normal((d, n))
    e = model.lam ** 2 * np.sum(Z * Z, axis=1)
    alpha = np.sqrt(theta * d * n / e[:k].sum())
    gamma = np.sqrt((1.0 - theta) * d * n / e[k:].sum())
    C = Z.copy()
    C[:k] *= alpha
    C[k:] *= gamma
    return model.Q @ C


def job(args):
    m, omt, sigma, seed = args
    d, k, n = cfg.D, cfg.K, cfg.N
    model = sp.QuadM2(d, k, n, m, seed=seed)
    Q, lam = model.Q, model.lam
    W = make_state(model, 1.0 - omt, seed)
    G = model.A @ W
    Gt = Q.T @ G
    e = np.sum(Gt * Gt, axis=1)
    theta = e[:k].sum() / e.sum()
    sf = sp.shape_factor((d, n))
    rng = np.random.default_rng([int(seed), 6, int(round(-np.log10(omt) * 10)), int(sigma * 1000), int(m)])
    rs = [1, 4, 16, k]
    ech = {r: sp.Echelon(r, frame='tracked', tau='pi', seed=seed) for r in rs}
    ranks = {'ht_stream': None, 'ht_stream_rk': k, 'ht_stream_r4': 4}
    Vst = {nm: None for nm in ranks}
    ht_ns_opt = sp.Opt('ht_ns', (d, n))
    acc = {}
    mom = G.copy()                      # momentum initialised at its stationary mean
    nmeas = MEAS if sigma > 0 else 1
    sgd_a = np.zeros(4)
    for t in range(WARM + nmeas):
        xi = sigma * rng.standard_normal((d, n)) if sigma > 0 else 0.0
        g = G + xi
        M, mom = sp.nesterov_lerp(g, mom, 0.95, True)
        parts = {r: ech[r].parts(M) for r in rs}
        outs = {}
        for nm, rk in ranks.items():
            outs[nm], Vst[nm] = sp.msign_generalized_ht_v2_stream_qr(M, Vst[nm], p=P, rank=rk)
        if t < WARM:
            continue
        U, S, Vh = sp.svd(M, full_matrices=False)
        Em = U @ Vh
        Eh = (U * (S ** P)[None, :]) @ Vh
        Emt, Eht = Q.T @ Em, Q.T @ Eh
        mkm = lambda F, sfac=sf: measure(F, sfac, U, Vh, Em, Emt, Q, lam, k, Gt)
        mkh = lambda F, sfac=sf: measure(F, sfac, U, Vh, Eh, Eht, Q, lam, k, Gt)
        cur = {}
        cur['muon_exact'] = mkm(Em)
        cur['sgdm'] = mkm(M, 1.0)
        ns5 = sp.zeropower_via_newtonschulz5(M)
        cur['muon_ns5'] = mkm(ns5)
        for r in rs:
            tag = 'k' if r == k else str(r)
            f = np.minimum(1.0, S / S[r])
            f[:r] = 1.0
            cur[f'ech_r{tag}_ideal'] = mkm((U * f[None, :]) @ Vh)
            p_ = parts[r]
            O = sp.Echelon.assemble(p_, p_['tau_pi'])
            cur[f'ech_r{tag}'] = mkm(O)
            if r in (4, k):
                cur[f'ech_r{tag}_pol'] = mkm(sp.cubic_step(O))
                cur[f'ech_r{tag}_fro'] = mkm(sp.Echelon.assemble(p_, p_['tau_fro']))
            # the two pieces of the tracked Echelon update separately: orthogonalised head U P and
            # normalised-SGD tail T / tau  (thresholds "inside the tail")
            cur[f'ech_r{tag}_headonly'] = mkm(p_['U'] @ p_['P'])
            if p_['tau_pi'] > 1e-300:
                cur[f'ech_r{tag}_tailonly'] = mkm(p_['T'] / p_['tau_pi'])
        cur['ht_exact'] = mkh(Eh)
        cur['ht_ns'] = mkh(ht_ns_opt.filter(M))
        cur['ht_avg'] = mkh(0.8 * ns5 + 0.2 * Eh)
        cur['ht_ns5part'] = mkh(ns5)            # the 4-of-5 steps of the interval scheme
        for nm in ranks:
            cur[nm] = mkh(outs[nm])
        for nm, v in cur.items():
            acc.setdefault(nm, []).append(v)
        # plain SGD without momentum (Deng): O = g
        gt = Gt + (Q.T @ xi if sigma > 0 else 0.0)
        rowsq = np.sum(gt * gt, axis=1)
        rowdot = np.sum(Gt * gt, axis=1)
        sgd_a += np.array([rowdot[:k].sum(), np.sum(lam[:k] * rowsq[:k]), rowdot[k:].sum(), np.sum(lam[k:] * rowsq[k:])])
    res = {}
    for nm, lst in acc.items():
        arr = np.array(lst)
        mean = np.nanmean(arr, axis=0)
        res[nm] = {key: float(mean[j]) for j, key in enumerate(KEYS)}
    # interval scheme: cycle average of the one-step loss change (4 NS5 steps + 1 exact-HT step)
    res['ht_interval_cycle'] = {key: 0.8 * res['ht_ns5part'][key] + 0.2 * res['ht_exact'][key]
                                for key in ('aD', 'bD', 'aB', 'bB')}
    sgd_a /= nmeas
    res['sgd_mc'] = dict(aD=float(sgd_a[0]), bD=float(sgd_a[1]), aB=float(sgd_a[2]), bB=float(sgd_a[3]))
    # Deng closed form
    tauD = float(np.sum(e[:k] * lam[:k]))
    tauB = float(np.sum(e[k:] * lam[k:]))
    res['sgd_deng'] = dict(aD=float(e[:k].sum()), bD=tauD + n * sigma ** 2 * float(lam[:k].sum()),
                           aB=float(e[k:].sum()), bB=tauB + n * sigma ** 2 * float(lam[k:].sum()))
    for nm in res:
        r_ = res[nm]
        r_['etaD'] = 2 * r_['aD'] / r_['bD'] if r_['bD'] > 0 else float('nan')
        r_['etaB'] = 2 * r_['aB'] / r_['bB'] if r_['bB'] > 0 else float('nan')
        r_['ratio_D_over_B'] = r_['etaD'] / r_['etaB'] if r_['etaB'] != 0 else float('nan')
        r_['eta_full'] = 2 * (r_['aD'] + r_['aB']) / (r_['bD'] + r_['bB']) if (r_['bD'] + r_['bB']) > 0 else float('nan')
    return dict(m=m, one_minus_theta=omt, theta=float(theta), sigma=sigma, seed=seed,
                loss=float(0.5 * np.sum(e / lam)), res=res)


def main():
    t0 = time.time()
    jobs = [(m, omt, s, seed) for m in MS for omt in ONE_MINUS_THETA for s in SIGMAS for seed in SEEDS]
    with Pool(2) as pool:
        out = pool.map(job, jobs, chunksize=4)
    json.dump(dict(meta=dict(D=cfg.D, K=cfg.K, N=cfg.N, WARM=WARM, MEAS=MEAS, seeds=SEEDS, wall_s=time.time() - t0),
                   rows=out), open(os.path.join(cfg.RES, 's3_frozen.json'), 'w'))
    print('wall', time.time() - t0)


if __name__ == '__main__':
    main()
