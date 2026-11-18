"""
analyze_s2.py -- aggregate the S2 runs (results/s2_*.npz) into tables and figures.

Per (m, sigma, optimizer, seed):
  theta_late   mean of Deng's alignment over the last third of the run (steps 1600..2400)
  theta_tsd    its standard deviation over time inside that window
  loss_late    mean loss over the window;  upd_late: mean fraction of the update in P^D
  theta_min, t_min  minimum of the (25-step smoothed) alignment curve and its position
  two_phase    theta_0 - theta_min > 0.05  and  theta_late - theta_min > 0.05
  t_1e-2, t_1e-3   first recorded step with loss <= 1e-2 L0, 1e-3 L0
  t_floor      first recorded step with loss <= 2 x (late loss of the family's exact filter, same seed)
Across seeds: mean and standard deviation (ddof = 1).  For every approximation the PAIRED
difference to its exact filter (same seed = same problem, init and noise stream) is reported:
  d_theta = theta_late(approx) - theta_late(exact)   (mean, sd over seeds)
A difference is "resolved" when |mean d_theta| > 3 x sd of the paired difference.
An outcome change is called "material" when |mean d_theta| > max(0.02, 3 x seed-sd of theta_late of
the exact filter, 3 x sd of the paired difference).  Because theta saturates at 1 in the low-noise
runs, a second criterion is reported: "material_log" when the late mean of (1 - theta) differs by
more than a factor 2 (|d log10(1-theta)| > max(0.3, 3 x sd of the paired difference)).

Output: results/s2_summary.json, results/s2_tables.md, figs/s2_*.png
Run:    python3 analyze_s2.py
"""
import glob
import json
import os

import numpy as np
import plotstyle
import matplotlib.pyplot as plt
from matplotlib.colors import LinearSegmentedColormap, TwoSlopeNorm

import config as cfg

plotstyle.apply()
EXACT = {'muon': 'muon_exact', 'ht': 'ht_exact', 'sgd': 'sgd', 'sgdm': 'sgdm'}
ECH_IDEAL = {'ech_r1': 'ech_r1_ideal', 'ech_r4': 'ech_r4_ideal', 'ech_r16': 'ech_r16_ideal', 'ech_rk': 'ech_rk_ideal',
             'ech_r4_pol': 'ech_r4_ideal', 'ech_rk_pol': 'ech_rk_ideal', 'ech_r4_fro': 'ech_r4_ideal', 'ech_rk_fro': 'ech_rk_ideal'}


def first_below(L, thr, rec_every):
    idx = np.where(L <= thr)[0]
    return float(idx[0] * rec_every) if len(idx) else float('inf')


def smooth(x, w=5):
    return np.convolve(x, np.ones(w) / w, mode='valid')


def load():
    data = {}
    for f in sorted(glob.glob(os.path.join(cfg.RES, 's2_m*_seed*.npz'))):
        z = np.load(f, allow_pickle=False)
        key = (int(z['m']), float(z['sigma']))
        data.setdefault(key, {})[int(z['seed'])] = {k: z[k] for k in z.files}
    return data


def per_run(z):
    names = [str(n) for n in z['names']]
    fam = [str(n) for n in z['family']]
    rec = int(z['rec_every'])
    loss, theta, upd = z['loss'], z['theta'], z['upd_dom']
    nrec = upd.shape[1]
    lo = (2 * nrec) // 3
    out = {}
    for j, nm in enumerate(names):
        L, th, u = loss[j], theta[j], upd[j]
        div = bool(z['diverged'][j])
        ths = smooth(th[:nrec])
        imin = int(np.nanargmin(ths)) if np.isfinite(ths).any() else 0
        d = dict(family=fam[j], lr=float(z['lr'][j]), diverged=div,
                 theta0=float(th[0]), theta_late=float(np.nanmean(th[lo:])), theta_tsd=float(np.nanstd(th[lo:])),
                 omt_late=float(max(np.nanmean(1.0 - th[lo:]), 1e-16)),
                 loss0=float(L[0]), loss_late=float(np.nanmean(L[lo:])), upd_late=float(np.nanmean(u[lo:])),
                 theta_min=float(ths[imin]), t_min=float((imin + 2) * rec),
                 t_1e2=first_below(L, 1e-2 * L[0], rec), t_1e3=first_below(L, 1e-3 * L[0], rec))
        d['two_phase'] = bool((d['theta0'] - d['theta_min'] > 0.05) and (d['theta_late'] - d['theta_min'] > 0.05))
        out[nm] = d
    for j, nm in enumerate(names):
        ex = EXACT[out[nm]['family']]
        out[nm]['t_floor'] = first_below(loss[j], 2.0 * out[ex]['loss_late'], rec)
    return out


def msd(v):
    v = np.asarray(v, dtype=float)
    fin = v[np.isfinite(v)]
    if len(fin) == 0:
        return float('nan'), float('nan')
    return float(np.mean(fin)), float(np.std(fin, ddof=1)) if len(fin) > 1 else 0.0


def main():
    data = load()
    summary = {}
    for key in sorted(data):
        m, sigma = key
        runs = {seed: per_run(z) for seed, z in data[key].items()}
        seeds = sorted(runs)
        names = list(runs[seeds[0]].keys())
        S = {}
        for nm in names:
            r = {}
            for q in ['theta_late', 'theta_tsd', 'omt_late', 'loss_late', 'upd_late', 'theta_min', 't_min', 't_1e2', 't_1e3', 't_floor', 'theta0']:
                r[q], r[q + '_sd'] = msd([runs[s][nm][q] for s in seeds])
            r['n_inf_t_floor'] = int(sum(not np.isfinite(runs[s][nm]['t_floor']) for s in seeds))
            r['two_phase'] = int(sum(runs[s][nm]['two_phase'] for s in seeds))
            r['diverged'] = int(sum(runs[s][nm]['diverged'] for s in seeds))
            r['family'] = runs[seeds[0]][nm]['family']
            r['lr'] = runs[seeds[0]][nm]['lr']
            r['nseeds'] = len(seeds)
            ex = EXACT[r['family']]
            for ref_name, tag in [(ex, 'vs_exact'), (ECH_IDEAL.get(nm), 'vs_ideal')]:
                if ref_name is None or ref_name == nm:
                    continue
                dth = [runs[s][nm]['theta_late'] - runs[s][ref_name]['theta_late'] for s in seeds]
                dup = [runs[s][nm]['upd_late'] - runs[s][ref_name]['upd_late'] for s in seeds]
                dl = [np.log10(runs[s][nm]['loss_late'] / runs[s][ref_name]['loss_late']) for s in seeds]
                do = [np.log10(runs[s][nm]['omt_late'] / runs[s][ref_name]['omt_late']) for s in seeds]
                r[f'dlog10omt_{tag}'], r[f'dlog10omt_{tag}_sd'] = msd(do)
                rt = [runs[s][nm]['t_floor'] / runs[s][ref_name]['t_floor'] for s in seeds]
                r[f'd_theta_{tag}'], r[f'd_theta_{tag}_sd'] = msd(dth)
                r[f'd_upd_{tag}'], r[f'd_upd_{tag}_sd'] = msd(dup)
                r[f'dlog10loss_{tag}'], r[f'dlog10loss_{tag}_sd'] = msd(dl)
                r[f'tfloor_ratio_{tag}'], r[f'tfloor_ratio_{tag}_sd'] = msd(rt)
            S[nm] = r
        for nm in names:
            r = S[nm]
            if 'd_theta_vs_exact' in r:
                ex = EXACT[r['family']]
                thr = max(0.02, 3 * S[ex]['theta_late_sd'], 3 * r['d_theta_vs_exact_sd'])
                r['material'] = bool(abs(r['d_theta_vs_exact']) > thr)
                # statistically resolved (paired over seeds), whatever its size
                r['resolved'] = bool(abs(r['d_theta_vs_exact']) > 3 * r['d_theta_vs_exact_sd'] and r['nseeds'] >= 2)
                r['material_threshold'] = float(thr)
                # second criterion, relevant when theta is within 1e-2 of 1: factor >= 2 in (1 - theta)
                r['material_log'] = bool(abs(r['dlog10omt_vs_exact']) > max(0.3, 3 * r['dlog10omt_vs_exact_sd']))
        summary[f'm{m}_s{sigma}'] = S
    json.dump(summary, open(os.path.join(cfg.RES, 's2_summary.json'), 'w'), indent=1)

    keys = sorted(data)
    names = list(summary[f'm{keys[0][0]}_s{keys[0][1]}'].keys())
    approx = [n for n in names if 'd_theta_vs_exact' in summary[f'm{keys[0][0]}_s{keys[0][1]}'][n]]

    # ------------------------------------------------------------------ markdown tables
    def fmt_t(x):
        return 'never' if not np.isfinite(x) else f'{x:.0f}'
    lines = ['# S2 tables (generated by analyze_s2.py)\n']
    lines.append('theta_late: mean over steps 1600..2400, then mean +- sd over seeds; (tsd) = sd over time inside the window.\n')
    for key in keys:
        m, sigma = key
        S = summary[f'm{m}_s{sigma}']
        lines.append(f'\n## m = {m}, sigma = {sigma}\n')
        lines.append('| optimizer | lr | theta_late (seed sd) [tsd] | d_theta vs exact (sd) | material | upd in D | loss_late | t(1e-2 L0) | t_floor | two-phase | div |')
        lines.append('|---|---|---|---|---|---|---|---|---|---|---|')
        for nm in names:
            r = S[nm]
            dth = f"{r['d_theta_vs_exact']:+.4f} ({r['d_theta_vs_exact_sd']:.4f})" if 'd_theta_vs_exact' in r else 'ref'
            mat = ('YES' if r.get('material') else 'no') if 'material' in r else ''
            lines.append(f"| {nm} | {r['lr']:.4g} | {r['theta_late']:.4f} ({r['theta_late_sd']:.4f}) [{r['theta_tsd']:.4f}] | {dth} | {mat} | "
                         f"{r['upd_late']:.3f} | {r['loss_late']:.3g} | {fmt_t(r['t_1e2'])} | {fmt_t(r['t_floor'])}{'*' if r['n_inf_t_floor'] else ''} | "
                         f"{r['two_phase']}/{r['nseeds']} | {r['diverged']} |")
    lines.append('\n\n# Condensed: paired difference of late-time alignment, approximation minus exact filter\n')
    lines.append('entries: mean d_theta (sd over seeds); **bold** = material by the criterion in the docstring; ~ = not resolved (|mean| <= 3 sd of the paired difference).\n')
    hdr = '| approximation | ' + ' | '.join(f'm={m}, s={s:g}' for m, s in keys) + ' |'
    lines.append(hdr)
    lines.append('|---|' + '---|' * len(keys))
    for nm in approx:
        row = []
        for m, s in keys:
            r = summary[f'm{m}_s{s}'][nm]
            cell = f"{r['d_theta_vs_exact']:+.4f} ({r['d_theta_vs_exact_sd']:.4f})"
            if not r.get('resolved'):
                cell = '~' + cell
            row.append(f'**{cell}**' if r.get('material') else cell)
        lines.append(f'| {nm} | ' + ' | '.join(row) + ' |')
    lines.append('\n\n# Condensed: log10[(1 - theta_late)_approx / (1 - theta_late)_exact], mean (sd over seeds); **bold** = more than a factor 2 and > 3 sd\n')
    lines.append(hdr)
    lines.append('|---|' + '---|' * len(keys))
    for nm in approx:
        row = []
        for m, s in keys:
            r = summary[f'm{m}_s{s}'][nm]
            cell = f"{r['dlog10omt_vs_exact']:+.2f} ({r['dlog10omt_vs_exact_sd']:.2f})"
            row.append(f'**{cell}**' if r.get('material_log') else cell)
        lines.append(f'| {nm} | ' + ' | '.join(row) + ' |')
    lines.append('\n\n# Reference: exact filters, late-time 1 - theta (mean over seeds)\n')
    lines.append('| optimizer | ' + ' | '.join(f'm={m}, s={s:g}' for m, s in keys) + ' |')
    lines.append('|---|' + '---|' * len(keys))
    for nm in ['sgd', 'sgdm', 'muon_exact', 'ht_exact']:
        lines.append(f'| {nm} | ' + ' | '.join(f"{summary[f'm{m}_s{s}'][nm]['omt_late']:.3g}" for m, s in keys) + ' |')
    lines.append('\n\n# Condensed: late loss ratio log10(L_approx / L_exact), mean (sd over seeds)\n')
    lines.append(hdr)
    lines.append('|---|' + '---|' * len(keys))
    for nm in approx:
        row = [f"{summary[f'm{m}_s{s}'][nm]['dlog10loss_vs_exact']:+.2f} ({summary[f'm{m}_s{s}'][nm]['dlog10loss_vs_exact_sd']:.2f})" for m, s in keys]
        lines.append(f'| {nm} | ' + ' | '.join(row) + ' |')
    lines.append('\n\n# Condensed: fraction of the update in the dominant subspace (late), approximation minus exact\n')
    lines.append(hdr)
    lines.append('|---|' + '---|' * len(keys))
    for nm in approx:
        row = [f"{summary[f'm{m}_s{s}'][nm]['d_upd_vs_exact']:+.3f} ({summary[f'm{m}_s{s}'][nm]['d_upd_vs_exact_sd']:.3f})" for m, s in keys]
        lines.append(f'| {nm} | ' + ' | '.join(row) + ' |')
    lines.append('\n\n# Condensed: time to reach 2x the exact filter\'s late loss, ratio approx / exact (inf = never within 2400 steps)\n')
    lines.append(hdr)
    lines.append('|---|' + '---|' * len(keys))
    for nm in approx:
        row = []
        for m, s in keys:
            r = summary[f'm{m}_s{s}'][nm]
            row.append('never' if r['n_inf_t_floor'] == r['nseeds'] else
                       f"{r['tfloor_ratio_vs_exact']:.2f} ({r['tfloor_ratio_vs_exact_sd']:.2f}){'*' if r['n_inf_t_floor'] else ''}")
        lines.append(f'| {nm} | ' + ' | '.join(row) + ' |')
    open(os.path.join(cfg.RES, 's2_tables.md'), 'w').write('\n'.join(lines) + '\n')

    # ------------------------------------------------------------------ figures
    # (1) heatmap of d_theta
    Dm = np.array([[summary[f'm{m}_s{s}'][nm]['d_theta_vs_exact'] for m, s in keys] for nm in approx])
    Mt = np.array([[summary[f'm{m}_s{s}'][nm].get('material', False) for m, s in keys] for nm in approx])
    cmap = LinearSegmentedColormap.from_list('div', ['#1c5cab', '#86b6ef', '#f0efec', '#f2a583', '#b8451a'])
    vmax = max(0.05, float(np.nanmax(np.abs(Dm))))
    fig, ax = plt.subplots(figsize=(11.5, 0.36 * len(approx) + 1.6))
    im = ax.imshow(Dm, cmap=cmap, norm=TwoSlopeNorm(0.0, -vmax, vmax), aspect='auto')
    ax.grid(False)
    ax.set_xticks(range(len(keys)))
    ax.set_xticklabels([f'm={m}\ns={s:g}' for m, s in keys])
    ax.set_yticks(range(len(approx)))
    ax.set_yticklabels(approx)
    for i in range(len(approx)):
        for j in range(len(keys)):
            v = Dm[i, j]
            txt = f'{v:+.3f}' + ('*' if Mt[i, j] else '')
            ax.text(j, i, txt, ha='center', va='center', fontsize=7,
                    color='#ffffff' if abs(v) > 0.6 * vmax else plotstyle.INK,
                    fontweight='bold' if Mt[i, j] else 'normal')
    ax.set_title('Late-time alignment: approximation minus exact filter (paired over 3 seeds; * = material)')
    fig.colorbar(im, ax=ax, fraction=0.025, pad=0.02, label='d theta_late')
    fig.tight_layout()
    fig.savefig(os.path.join(cfg.FIG, 's2_dtheta_heatmap.png'), dpi=130)
    plt.close(fig)

    # (2) alignment and loss curves, one figure per m: rows = family, cols = sigma
    panels = {'muon': ['muon_exact', 'muon_ns5', 'ech_r1', 'ech_r4', 'ech_r16', 'ech_rk', 'ech_rk_ideal', 'sgd'],
              'ht': ['ht_exact', 'ht_ns', 'ht_interval', 'ht_avg', 'ht_stream', 'ht_stream_rk', 'ht_stream_r4', 'sgd']}
    for m in sorted({k[0] for k in keys}):
        for quantity, ylab in [('theta', "Deng's alignment theta_t"), ('loss', 'loss')]:
            sig = sorted({k[1] for k in keys if k[0] == m})
            fig, axes = plt.subplots(2, len(sig), figsize=(4.4 * len(sig), 6.6), sharex=True, squeeze=False)
            for ci, s in enumerate(sig):
                zs = data[(m, s)]
                seeds = sorted(zs)
                nm_all = [str(n) for n in zs[seeds[0]]['names']]
                rec = int(zs[seeds[0]]['rec_every'])
                for ri, famname in enumerate(['muon', 'ht']):
                    a = axes[ri, ci]
                    for li, nm in enumerate(panels[famname]):
                        j = nm_all.index(nm)
                        arr = np.array([zs[sd][quantity][j] for sd in seeds])
                        y = np.nanmean(arr, axis=0)
                        x = np.arange(len(y)) * rec
                        if li == 0:
                            a.plot(x, y, color=plotstyle.INK, lw=2.0, label=nm, zorder=5)
                        elif nm == 'sgd':
                            a.plot(x, y, color=plotstyle.MUTED, lw=1.2, ls='--', label='sgd (baseline)')
                        else:
                            a.plot(x, y, color=plotstyle.PALETTE[li - 1], lw=1.3, label=nm)
                    if quantity == 'loss':
                        a.set_yscale('log')
                    else:
                        a.set_ylim(-0.02, 1.02)
                    if ri == 0:
                        a.set_title(f'm = {m}, sigma = {s:g}')
                    if ri == 1:
                        a.set_xlabel('step')
                    if ci == 0:
                        a.set_ylabel(f'{famname} family: {ylab}')
                    a.legend(loc='best', ncol=1)
            fig.suptitle(f'{ylab} (mean of 3 seeds), exact filter in black, approximations at the same learning rate', fontsize=10)
            fig.tight_layout()
            fig.savefig(os.path.join(cfg.FIG, f's2_{quantity}_curves_m{m}.png'), dpi=130)
            plt.close(fig)
    print('configs:', len(keys), ' approximations:', len(approx))
    nmat = {nm: int(Mt[i].sum()) for i, nm in enumerate(approx)}
    print('material changes (theta criterion) per approximation (out of %d configs):' % len(keys), nmat)
    nlog = {nm: int(sum(summary[f'm{m}_s{s}'][nm].get('material_log', False) for m, s in keys)) for nm in approx}
    print('material changes (log(1-theta) criterion):', nlog)


if __name__ == '__main__':
    main()
