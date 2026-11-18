"""
exp_shadow.py -- S1 (part b) and S3 (part a): the approximations evaluated on the inputs that
actually arise along trajectories of the EXACT filter they approximate ("shadow" protocol).

A driver (exact Muon or exact HTMuon, tuned lr, model M2) is run for T_EVAL steps.  At every step
the Nesterov-momentum matrix M_t that the driver filters is ALSO fed to each approximate filter
(the stateful ones -- stream QR, tracked Echelon frames -- keep their own state across steps, as
they would in training, but they do not influence the trajectory).  Every REC_EVERY steps we record,
for the exact filter E_t = F_exact(M_t) and each approximation F_t = F_approx(M_t):

  fidelity (S1)   rel      = ||F_t - E_t||_F / ||E_t||_F
                  off      = off-diagonal energy of F_t in the exact singular basis of M_t
                  t_head, t_bulk = mean transfer u_i^T F_t v_i over singular directions 1..k / k+1..n
                  bulk_gain = ||P^B F_t||_F / ||P^B E_t||_F,  bulk_cos = cos(P^B F_t, P^B E_t)
                  dom_frac = ||P^D F_t||_F^2 / ||F_t||_F^2      (P^D, P^B: Hessian projectors)
                  gain     = <F_t, E_t> / ||E_t||_F^2  (best scalar fit of F_t by the exact output:
                             the "effective step-size factor" of the approximation)
  projected-update test (S3; O = shape_factor * F_t, G_t = A W_t the true gradient)
                  a_S = <P^S G_t, O>,   b_S = <P^S O, A P^S O>,   S in {D, B}
                  so that  L(W_t - eta P^S O) - L(W_t) = -eta a_S + eta^2 b_S / 2  exactly, and the
                  loss threshold of the S-projected update is eta_S^loss = 2 E[a_S] / E[b_S].

Output: results/shadow_{family}_m{m}_s{sigma}_seed{seed}.npz
Run:    nice -n 10 python3 exp_shadow.py            (~5 CPU-min, 2 worker processes)
then    python3 analyze_shadow.py
"""
import argparse
import json
import os
import time
from multiprocessing import Pool

import numpy as np

import config as cfg
import spfilters as sp

P = 0.125
SHADOW_SEEDS = [0, 1]
KEYS = ['rel', 'off', 't_head', 't_bulk', 'bulk_gain', 'bulk_cos', 'dom_frac', 'aD', 'bD', 'aB', 'bB', 'gain']


def measure(F, sf, U, Vh, E, Et, Q, lam, k, Gt):
    """All recorded quantities for one filter output F (no shape factor) -- see module docstring."""
    t, off = sp.transfer(F, U, Vh)
    Ft = Q.T @ F
    nE = np.linalg.norm(E)
    fb, eb = Ft[k:], Et[k:]
    nfb, neb = np.linalg.norm(fb), np.linalg.norm(eb)
    tot = np.sum(Ft * Ft)
    O = sf * Ft
    rowsq = np.sum(O * O, axis=1)
    rowdot = np.sum(Gt * O, axis=1)
    return [np.linalg.norm(F - E) / nE, off, np.mean(t[:k]), np.mean(t[k:]),
            nfb / neb if neb > 0 else np.nan,
            np.sum(fb * eb) / (nfb * neb) if nfb > 0 and neb > 0 else np.nan,
            np.sum(Ft[:k] ** 2) / tot if tot > 0 else np.nan,
            rowdot[:k].sum(), np.sum(lam[:k] * rowsq[:k]), rowdot[k:].sum(), np.sum(lam[k:] * rowsq[k:]),
            np.sum(F * E) / (nE * nE)]


def job(args):
    family, m, sigma, seed = args
    t0 = time.time()
    tuned = json.load(open(os.path.join(cfg.RES, 'tuned_lr.json')))['table'][f'm{m}_s{sigma}']
    lr = tuned[family]['lr']
    d, k, n = cfg.D, cfg.K, cfg.N
    model = sp.QuadM2(d, k, n, m, seed=seed)
    Q, lam, A = model.Q, model.lam, model.A
    W = model.init_W(seed)
    rng = np.random.default_rng([int(seed), 3])          # same noise stream as exp_s2
    sf = sp.shape_factor((d, n))
    mom = np.zeros((d, n))
    T, rec_every = cfg.T_EVAL, cfg.REC_EVERY
    nrec = T // rec_every
    rs = [1, 4, 16, k]
    if family == 'muon':
        ech = {r: sp.Echelon(r, frame='tracked', tau='pi', seed=seed) for r in rs}
        names = ['exact', 'identity', 'muon_ns5']
        for r in rs:
            tag = 'k' if r == k else str(r)
            names += [f'ech_r{tag}_ideal', f'ech_r{tag}']
        names += ['ech_r4_pol', 'ech_rk_pol', 'ech_r4_fro', 'ech_rk_fro']
    else:
        ranks = {'ht_stream': None, 'ht_stream_rk': k, 'ht_stream_r4': 4}
        Vst = {nm: None for nm in ranks}
        names = ['exact', 'identity', 'ht_ns', 'muon_ns5', 'ht_avg', 'ht_stream', 'ht_stream_rk', 'ht_stream_r4']
    data = {nm: np.full((nrec, len(KEYS)), np.nan) for nm in names}
    extra = {}
    if family == 'muon':
        extra = {f'frame_err_r{r}': np.full(nrec, np.nan) for r in rs}
        extra.update({f'tau_ratio_r{r}': np.full(nrec, np.nan) for r in rs})
    loss = np.full(nrec, np.nan)
    theta = np.full(nrec, np.nan)
    svals = np.full((nrec, n), np.nan)
    ht_ns_opt = sp.Opt('ht_ns', (d, n))
    for t in range(T):
        G = A @ W
        g = G + sigma * rng.standard_normal((d, n)) if sigma > 0 else G
        M, mom = sp.nesterov_lerp(g, mom, 0.95, True)
        U, S, Vh = np.linalg.svd(M, full_matrices=False)
        E = U @ Vh if family == 'muon' else (U * (S ** P)[None, :]) @ Vh
        rec = (t % rec_every == 0)
        # stateful shadows: every step
        if family == 'muon':
            parts = {r: ech[r].parts(M) for r in rs}
        else:
            outs = {}
            for nm, rk in ranks.items():
                outs[nm], Vst[nm] = sp.msign_generalized_ht_v2_stream_qr(M, Vst[nm], p=P, rank=rk)
        if rec:
            i = t // rec_every
            Gt = Q.T @ G
            e = np.sum(Gt * Gt, axis=1)
            loss[i] = 0.5 * np.sum(e / lam)
            theta[i] = e[:k].sum() / e.sum()
            svals[i] = S
            Et = Q.T @ E
            mk = lambda F, sfac=sf: measure(F, sfac, U, Vh, E, Et, Q, lam, k, Gt)
            data['exact'][i] = mk(E)
            data['identity'][i] = mk(M, 1.0)
            ns5 = sp.zeropower_via_newtonschulz5(M)
            data['muon_ns5'][i] = mk(ns5)
            if family == 'muon':
                for r in rs:
                    tag = 'k' if r == k else str(r)
                    f = np.minimum(1.0, S / S[r])
                    f[:r] = 1.0
                    data[f'ech_r{tag}_ideal'][i] = mk((U * f[None, :]) @ Vh)
                    p_ = parts[r]
                    O = sp.Echelon.assemble(p_, p_['tau_pi'])
                    data[f'ech_r{tag}'][i] = mk(O)
                    extra[f'frame_err_r{r}'][i] = 1.0 - np.sum((U[:, :r].T @ p_['U']) ** 2) / r
                    extra[f'tau_ratio_r{r}'][i] = p_['tau_pi'] / np.linalg.norm(p_['T'], 2)
                    if r in (4, k):
                        data[f'ech_r{tag}_pol'][i] = mk(sp.cubic_step(O))
                        data[f'ech_r{tag}_fro'][i] = mk(sp.Echelon.assemble(p_, p_['tau_fro']))
            else:
                data['ht_ns'][i] = mk(ht_ns_opt.filter(M))
                data['ht_avg'][i] = mk(0.8 * ns5 + 0.2 * E)
                for nm in ranks:
                    data[nm][i] = mk(outs[nm])
        W = W - lr * sf * E
    np.savez_compressed(os.path.join(cfg.RES, f'shadow_{family}_m{m}_s{sigma}_seed{seed}.npz'),
                        names=np.array(names), keys=np.array(KEYS),
                        data=np.array([data[nm] for nm in names]),
                        loss=loss, theta=theta, svals=svals, lr=lr, m=m, sigma=sigma, seed=seed,
                        lam=lam, T=T, rec_every=rec_every,
                        **extra)
    return (family, m, sigma, seed, time.time() - t0)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--ms', type=int, nargs='+', default=cfg.MS)
    ap.add_argument('--seeds', type=int, nargs='+', default=SHADOW_SEEDS)
    ap.add_argument('--families', nargs='+', default=['muon', 'ht'])
    ap.add_argument('--force', action='store_true', help='recompute existing result files')
    a = ap.parse_args()
    jobs = [(f, m, s, seed) for f in a.families for m in a.ms for s in cfg.SIGMAS for seed in a.seeds]
    if not a.force:      # resume: skip configurations whose result file already exists
        jobs = [j for j in jobs if not os.path.exists(
            os.path.join(cfg.RES, f'shadow_{j[0]}_m{j[1]}_s{j[2]}_seed{j[3]}.npz'))]
    print(len(jobs), 'jobs to run', flush=True)
    t0 = time.time()
    with Pool(2) as pool:
        for f, m, s, seed, dt in pool.imap_unordered(job, jobs, chunksize=1):
            print(f'done {f} m={m} sigma={s} seed={seed} in {dt:.1f}s', flush=True)
    print('wall', time.time() - t0)
