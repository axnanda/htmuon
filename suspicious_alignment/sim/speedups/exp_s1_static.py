"""
exp_s1_static.py -- S1 (part a): filter fidelity on synthetic 200 x 40 matrices with prescribed
singular values (flat / power-law / geometric / spiked), no momentum, no shape factor.

For every filter the effective singular-value transfer t_i = u_i^T F(G) v_i in the EXACT singular
basis of the input is recorded, together with the off-diagonal energy 1 - sum t_i^2/||F(G)||_F^2
and the relative Frobenius error against the exact filter it approximates
(polar factor for the Muon family, U S^p V^T with p = 1/8 for the HTMuon family).

Stateful filters (stream QR, tracked Echelon) are applied j times to the SAME matrix (cold start at
j = 1), which isolates the convergence of the warm-started iteration; the trajectory experiment
exp_shadow.py measures them on inputs that actually move.

Output: results/s1_static.json (summaries), results/s1_static.npz (transfer arrays),
        figs/s1_transfer_curves.png, figs/s1_spiked_bulk.png, figs/s1_stateful_convergence.png
Run:    nice -n 10 python3 exp_s1_static.py        (< 1 CPU-min)
"""
import json
import os
import time

import numpy as np
import plotstyle
import matplotlib.pyplot as plt

import config as cfg
import spfilters as sp

plotstyle.apply()

D, N, K, P = cfg.D, cfg.N, cfg.K, 0.125
NSEED = 3
STREAM_J = [1, 2, 5, 20, 100, 1000]
ECH_J = [1, 2, 5, 20, 100]


def spectra():
    i = np.arange(1, N + 1, dtype=float)
    out = {
        'flat': np.linspace(1.0, 0.5, N),
        'powerlaw1': i ** -1.0,
        'powerlaw2': i ** -2.0,
        'geom6': np.geomspace(1.0, 1e-6, N),
    }
    for e in [1e-1, 1e-2, 1e-3, 1e-4, 1e-6]:
        out[f'spiked_{e:g}'] = np.concatenate([np.linspace(2.0, 1.0, K), e * np.linspace(1.0, 0.5, N - K)])
    return out


def slope(t, s):
    """log-log slope of the transfer on a block (nan if some t <= 0)."""
    if np.any(t <= 0):
        return float('nan')
    return float(np.polyfit(np.log(s), np.log(t), 1)[0])


def summarize(out, U, S, Vh, exact):
    t, off = sp.transfer(out, U, Vh)
    return dict(t=t, off=float(off), rel=float(sp.rel_err(out, exact)),
                head=float(np.mean(t[:K])), bulk=float(np.mean(t[K:])),
                bulk_slope=slope(t[K:], S[K:]))


def main():
    t0 = time.time()
    specs = spectra()
    summ = {}
    arrays = {}
    for sname, S in specs.items():
        rows = {}
        for seed in range(NSEED):
            rng = np.random.default_rng([seed, 11])
            U = sp.haar(D, N, rng)
            V = sp.haar(N, N, rng)
            Vh = V.T
            G = (U * S[None, :]) @ Vh
            ex_muon = U @ Vh
            ex_ht = (U * (S ** P)[None, :]) @ Vh
            res = {}
            # ---- Muon family
            res['muon_ns5'] = summarize(sp.zeropower_via_newtonschulz5(G), U, S, Vh, ex_muon)
            for r in [1, 4, 16, K]:
                tag = 'k' if r == K else str(r)
                e = sp.Echelon(r, frame='exact', tau='exact')
                res[f'ech_r{tag}_ideal'] = summarize(e(G), U, S, Vh, ex_muon)
                e = sp.Echelon(r, frame='tracked', tau='pi', seed=seed)
                efro = None
                for j in range(1, max(ECH_J) + 1):
                    parts = e.parts(G)
                    if j in ECH_J:
                        O = sp.Echelon.assemble(parts, parts['tau_pi'])
                        res[f'ech_r{tag}_j{j}'] = summarize(O, U, S, Vh, ex_muon)
                        res[f'ech_r{tag}_j{j}']['tau_ratio'] = float(parts['tau_pi'] / np.linalg.norm(parts['T'], 2))
                        if j in (1, 100):
                            res[f'ech_r{tag}_pol_j{j}'] = summarize(sp.cubic_step(O), U, S, Vh, ex_muon)
                            Of = sp.Echelon.assemble(parts, parts['tau_fro'])
                            res[f'ech_r{tag}_fro_j{j}'] = summarize(Of, U, S, Vh, ex_muon)
            # normalised SGD reference (linear transfer): G / sigma_max
            res['sgd_norm'] = summarize(G / S[0], U, S, Vh, ex_muon)
            # ---- HT family
            res['ht_exact'] = summarize(sp.msign_generalized_ht_v2(G, P), U, S, Vh, ex_ht)
            for scale in [1.0, 1e-2, 1e-4]:
                o = sp.Opt('ht_ns', (D, N))
                ex_s = (U * ((scale * S) ** P)[None, :]) @ Vh
                r_ = summarize(o.filter(scale * G), U, S, Vh, ex_s)
                r_['t_exact'] = (scale * S) ** P
                res[f'ht_ns_scale{scale:g}'] = r_
            for rank, tag in [(None, 'full'), (K, 'rk'), (4, 'r4')]:
                V_ = None
                rr = N if rank is None else rank
                ex_trunc = (U[:, :rr] * (S[:rr] ** P)[None, :]) @ Vh[:rr]
                for j in range(1, max(STREAM_J) + 1):
                    out, V_ = sp.msign_generalized_ht_v2_stream_qr(G, V_, p=P, rank=rank)
                    if j in STREAM_J:
                        r_ = summarize(out, U, S, Vh, ex_ht)
                        r_['rel_trunc'] = float(sp.rel_err(out, ex_trunc))
                        res[f'ht_stream_{tag}_j{j}'] = r_
            for kname, v in res.items():
                rows.setdefault(kname, []).append(v)
        # aggregate over seeds
        summ[sname] = {}
        for kname, lst in rows.items():
            agg = {}
            for key in lst[0]:
                if key in ('t', 't_exact'):
                    continue
                vals = np.array([x[key] for x in lst], dtype=float)
                agg[key] = float(np.nanmean(vals))
                agg[key + '_sd'] = float(np.nanstd(vals))
            summ[sname][kname] = agg
            arrays[f'{sname}__{kname}__t'] = np.mean([x['t'] for x in lst], axis=0)
        arrays[f'{sname}__sigma'] = S
    # scalar transfer curves (exact formulas, verified against the matrix code by test_port.py)
    x = np.geomspace(1e-7, 1.0, 400)
    arrays['ns5_x'] = x
    arrays['ns5_fx'] = sp.ns5_scalar(x)
    thr = {f'ns5_reaches_{lvl}': float(x[np.argmax(sp.ns5_scalar(x) >= lvl)]) for lvl in (0.1, 0.5, 0.68)}
    thr['ns5_slope_at_zero'] = float(sp.NS5_COEFFS[0] ** 5)
    summ['_scalar'] = thr
    json.dump(dict(meta=dict(D=D, N=N, K=K, p=P, nseed=NSEED, wall_s=time.time() - t0), summary=summ),
              open(os.path.join(cfg.RES, 's1_static.json'), 'w'), indent=1)
    np.savez_compressed(os.path.join(cfg.RES, 's1_static.npz'), **arrays)

    # ------------------------------------------------------------------ figures
    S = specs['geom6']
    rel = S / S[0]
    fig, ax = plt.subplots(1, 2, figsize=(11, 4.2))
    a = ax[0]
    a.loglog(rel, np.ones_like(rel), 'k-', lw=2, label='exact Muon (f = 1)')
    a.loglog(rel, arrays['geom6__muon_ns5__t'], 'o-', ms=3, label='NS5 Muon')
    for r, c in [(4, 'C2'), (16, 'C3')]:
        a.loglog(rel, arrays[f'geom6__ech_r{r}_ideal__t'], 's-', ms=3, color=c, label=f'Echelon({r}), exact frame')
        a.loglog(rel, np.clip(arrays[f'geom6__ech_r{r}_j100__t'], 1e-9, None), ':', color=c, label=f'Echelon({r}), tracked, 100 calls')
    a.loglog(rel, rel, 'k--', lw=1, label='normalised SGD (f = s/s_max)')
    a.set_xlabel('singular value / top singular value')
    a.set_ylabel('transfer  u_i^T F(G) v_i')
    a.set_title('Muon family, geometric spectrum 1 ... 1e-6')
    a.set_ylim(1e-7, 3)
    a.legend(fontsize=7)
    a = ax[1]
    a.loglog(rel, S ** P, 'k-', lw=2, label='exact HTMuon (s^0.125), scale 1')
    for scale, c in [(1.0, 'C0'), (1e-2, 'C1'), (1e-4, 'C4')]:
        a.loglog(rel, np.clip(arrays[f'geom6__ht_ns_scale{scale:g}__t'], 1e-12, None), 'o-', ms=3, color=c,
                 label=f'HTMuon-NS, ||G||_2 = {scale:g}')
        if scale != 1.0:
            a.loglog(rel, (scale * S) ** P, '-', color=c, lw=1, alpha=0.6, label=f'exact, ||G||_2 = {scale:g}')
    for j, c in [(1, 'C5'), (20, 'C6'), (1000, 'C7')]:
        a.loglog(rel, np.clip(arrays[f'geom6__ht_stream_full_j{j}__t'], 1e-12, None), '^:', ms=3, color=c,
                 label=f'stream (full rank), {j} calls')
    a.set_xlabel('singular value / top singular value')
    a.set_title('HTMuon family, geometric spectrum')
    a.set_ylim(1e-9, 3)
    a.legend(fontsize=7)
    fig.tight_layout()
    fig.savefig(os.path.join(cfg.FIG, 's1_transfer_curves.png'), dpi=130)
    plt.close(fig)

    eps = [1e-1, 1e-2, 1e-3, 1e-4, 1e-6]
    fig, ax = plt.subplots(1, 2, figsize=(11, 4.2))
    a = ax[0]
    for kname, lab in [('muon_ns5', 'NS5 Muon'), ('ech_r4_ideal', 'Echelon(4) exact frame'),
                       ('ech_r16_ideal', 'Echelon(16) exact frame'), ('ech_rk_ideal', 'Echelon(k=20) exact frame'),
                       ('ech_rk_j100', 'Echelon(k) tracked, 100 calls'), ('ech_rk_fro_j100', 'Echelon(k) tracked, tau = Frobenius'),
                       ('sgd_norm', 'normalised SGD')]:
        a.loglog(eps, [max(summ[f'spiked_{e:g}'][kname]['bulk'], 1e-12) for e in eps], 'o-', ms=4, label=lab)
    a.axhline(1.0, color='k', lw=2, label='exact Muon')
    a.set_xlabel('bulk / head singular-value ratio  eps')
    a.set_ylabel('mean transfer on the 20 bulk directions')
    a.set_title('spiked spectrum: Muon family')
    a.legend(fontsize=7)
    a = ax[1]
    a.loglog(eps, [np.mean((e * np.linspace(1, 0.5, N - K)) ** P) for e in eps], 'k-', lw=2, label='exact HTMuon')
    for kname, lab in [('ht_ns_scale1', 'HTMuon-NS'), ('ht_stream_full_j1', 'stream, 1 call (cold)'),
                       ('ht_stream_full_j20', 'stream, 20 calls'), ('ht_stream_full_j1000', 'stream, 1000 calls'),
                       ('ht_stream_rk_j20', 'stream rank k, 20 calls')]:
        a.loglog(eps, [max(summ[f'spiked_{e:g}'][kname]['bulk'], 1e-12) for e in eps], 'o-', ms=4, label=lab)
    a.set_xlabel('bulk / head singular-value ratio  eps')
    a.set_title('spiked spectrum: HTMuon family')
    a.legend(fontsize=7)
    fig.tight_layout()
    fig.savefig(os.path.join(cfg.FIG, 's1_spiked_bulk.png'), dpi=130)
    plt.close(fig)

    fig, ax = plt.subplots(1, 2, figsize=(11, 4.2))
    a = ax[0]
    for sname in ['flat', 'powerlaw1', 'geom6', 'spiked_0.01', 'spiked_0.0001']:
        a.loglog(STREAM_J, [summ[sname][f'ht_stream_full_j{j}']['rel'] for j in STREAM_J], 'o-', ms=4, label=sname)
    a.set_xlabel('number of calls on the same matrix (warm start)')
    a.set_ylabel('relative error vs exact U S^p V^T')
    a.set_title('stream QR (full rank): convergence')
    a.legend(fontsize=7)
    a = ax[1]
    for sname in ['flat', 'powerlaw1', 'geom6', 'spiked_0.01', 'spiked_0.0001']:
        a.semilogx(STREAM_J, [summ[sname][f'ht_stream_full_j{j}']['bulk_slope'] for j in STREAM_J], 'o-', ms=4, label=sname)
    a.axhline(P, color='k', lw=1)
    a.axhline(1.0, color='k', lw=1, ls='--')
    a.set_xlabel('number of calls on the same matrix')
    a.set_ylabel('log-log slope of the transfer on singular values 21..40')
    a.set_title('stream QR: 1 = SGD-like (linear), 0.125 = exact HTMuon')
    a.legend(fontsize=7)
    fig.tight_layout()
    fig.savefig(os.path.join(cfg.FIG, 's1_stateful_convergence.png'), dpi=130)
    plt.close(fig)
    print('wall', time.time() - t0)


if __name__ == '__main__':
    main()
