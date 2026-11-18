"""exp3: (M1) vector model, x+ = x - eta |g|^(p-1) g,  g = A x + xi  (p = 0: normalised GD = Muon
= Echelon(r >= 1) for a d x 1 'matrix';  p = 0.125: HTMuon;  p = 1 would be SGD).

(a) noise-free: effective step eta_eff(t) = eta |A x_t|^(p-1) grows as the gradient shrinks.
    Checks:  * exact one-step criterion  theta_{t+1} < theta_t  <=>  eta_eff(t) < eta*_t  (noise-free
               critical step of Deng et al., eq. (2) with e_D = e_B = 0);
             * long run: gradient -> period-2 orbit on the TOP eigenvector (edge of stability),
               theta -> 1, share of u_1 -> 1, |g_t| + |g_{t+1}| -> eta lam_1 (p = 0),
               |g| -> (eta lam_1/2)^(1/(1-p)) (p > 0);  two-phase curve (dip then rise).
(b) isotropic noise xi ~ N(0, sigma^2 I): compare the long-run alignment with the
    'frozen effective step' self-consistent heuristic (common.m1_selfconsistent), i.e. Deng's
    Theorem 16 evaluated at eta_eff, and with Deng's small-step value sum_D lam / sum lam.
"""
import json
import os
import sys
import time

import numpy as np

from common import RES, m1_selfconsistent, msd, save_json, spectrum

PARTS = sys.argv[1] if len(sys.argv) > 1 else "ab"     # "a", "b" or "ab"
FLOOR = 1e-290   # |c_i| is clamped from below (sign kept): in exact arithmetic c_i never reaches 0,
                 # but for m >= 100 the dominant coordinates underflow in float64 during phase I.

D, K, ETA = 500, 50, 0.01
SEEDS = list(range(8))
t0 = time.time()
out = dict(config=dict(d=D, k=K, eta=ETA, seeds=SEEDS, underflow_floor=FLOOR))
_old = os.path.join(RES, "exp3_m1_vector.json")
if PARTS != "ab" and os.path.exists(_old):
    out = json.load(open(_old))
    out["config"]["underflow_floor"] = FLOOR


def eta_star_noise_free(lam, c2):
    """Deng's eta*_t without noise: 2 (sB tauD - sD tauB) / (sB wD - sD wB)."""
    l2, l3, l4 = lam ** 2, lam ** 3, lam ** 4
    sD, sB = (l2[:K] * c2[:, :K]).sum(1), (l2[K:] * c2[:, K:]).sum(1)
    tD, tB = (l3[:K] * c2[:, :K]).sum(1), (l3[K:] * c2[:, K:]).sum(1)
    wD, wB = (l4[:K] * c2[:, :K]).sum(1), (l4[K:] * c2[:, K:]).sum(1)
    with np.errstate(invalid="ignore", divide="ignore"):
        return 2 * (sB * tD - sD * tB) / (sB * wD - sD * wB)


# ----------------------------------------------------------------------------- (a) noise-free
rows = []
for p in ([0.0, 0.125, 0.5] if "a" in PARTS else []):
    for m in [2, 5, 10, 20, 50, 100, 200, 500]:
        lam = spectrum(D, K, m)
        c = np.stack([np.random.default_rng(200 + s).standard_normal(D) for s in SEEDS])
        S = len(SEEDS)
        T, tail = 20000, 1000
        thm = np.empty(T)
        viol = 0
        checked = 0
        th_prev = None
        crit_prev = None
        first_up = np.full(S, -1)
        tailacc = dict(th=np.zeros(S), top1=np.zeros(S), g=np.zeros(S), geff=np.zeros(S))
        for t in range(T):
            g = lam * c
            E = g * g
            s = E.sum(1)
            th = E[:, :K].sum(1) / s
            thm[t] = th.mean()
            gn = np.sqrt(s)
            eff = ETA * gn ** (p - 1)
            if t < 6000:
                est = eta_star_noise_free(lam, c * c)
                if th_prev is not None:
                    dec = th < th_prev                  # theta decreased in the last step
                    ok = (dec == crit_prev) | (np.abs(th - th_prev) < 1e-13)
                    viol += int((~ok).sum())
                    checked += S
                    newly = (first_up < 0) & (~dec)
                    first_up[newly] = t - 1
                crit_prev = eff < est
                th_prev = th
            if t >= T - tail:
                tailacc["th"] += th
                tailacc["top1"] += E[:, 0] / s
                tailacc["g"] += gn
                tailacc["geff"] += eff * lam[0]
            c = c - eff[:, None] * g
            small = np.abs(c) < FLOOR
            if small.any():
                c = np.where(small, np.where(c < 0, -FLOOR, FLOOR), c)
        for kk in tailacc:
            tailacc[kk] /= tail
        gstar = (ETA * lam[0] / 2) ** (1 / (1 - p))
        rows.append(dict(p=p, m=m, theta_inf=msd(tailacc["th"]), one_minus_theta_inf=float(1 - tailacc["th"].mean()),
                         top1_share=msd(tailacc["top1"]), mean_gnorm_over_pred=msd(tailacc["g"] / gstar),
                         mean_etaeff_lam1=msd(tailacc["geff"]), theta0=float(thm[0]), theta_min=float(thm.min()),
                         tmin=int(np.argmin(thm)), first_increase_step=msd(first_up),
                         criterion_violations=viol, criterion_checked=checked))
        r_ = rows[-1]
        print(f"[M1 noise-free p={p}] m={m:4d} theta_inf={r_['theta_inf'][0]:.10f} top1={r_['top1_share'][0]:.6f} "
              f"<|g|>/pred={r_['mean_gnorm_over_pred'][0]:.4f} <eta_eff lam1>={r_['mean_etaeff_lam1'][0]:.4f} | "
              f"theta0={r_['theta0']:.4f} min={r_['theta_min']:.2e} at {r_['tmin']} | criterion violations "
              f"{viol}/{checked}, first increase at {r_['first_increase_step'][0]:.0f}")
        if m == 100:
            sub = np.unique(np.concatenate([np.arange(0, 6000, 2), np.arange(6000, T, 25)]))
            out[f"m1_nf_p{p}_curve_m100"] = dict(t=sub, theta_mean=thm[sub])
if "a" in PARTS:
    out["noise_free"] = rows

# ----------------------------------------------------------------------------- (b) with noise
rows = []
for p in ([0.0, 0.125] if "b" in PARTS else []):
    for m in [10, 100]:
        lam = spectrum(D, K, m)
        gstar = (ETA * lam[0] / 2) ** (1 / (1 - p))
        for rel in [0.03, 0.1, 0.3, 1.0, 3.0, 10.0, 30.0]:
            sigma = rel * gstar / np.sqrt(D)
            x_eff, E_pred = m1_selfconsistent(lam, ETA, sigma, p)
            rng = np.random.default_rng(int(1e6 * p) + 7 * m + int(1000 * rel))
            S = len(SEEDS)
            c = np.sqrt(E_pred)[None, :] / lam * rng.standard_normal((S, D))   # start at predicted scale
            T, burn = 40000, 15000
            accE = np.zeros((S, D))
            accth = np.zeros(S)
            acceff = np.zeros(S)
            for t in range(T):
                g = lam * c + sigma * rng.standard_normal((S, D))
                gn = np.sqrt((g * g).sum(1))
                eff = ETA * gn ** (p - 1)
                if t >= burn:
                    E = (lam * c) ** 2
                    accE += E
                    accth += E[:, :K].sum(1) / E.sum(1)
                    acceff += eff
                c = c - eff[:, None] * g
            n_ = T - burn
            Ebar = accE / n_
            th_ratio = Ebar[:, :K].sum(1) / Ebar.sum(1)
            pred = E_pred[:K].sum() / E_pred.sum()
            rows.append(dict(p=p, m=m, noise_rel=rel, sigma=sigma, pred_selfconsistent=pred,
                             pred_etaeff_lam1=x_eff * lam[0], deng_small_eta=lam[:K].sum() / lam.sum(),
                             pred_noise_dominated_etaeff_lam1=ETA * (sigma * np.sqrt(D)) ** (p - 1) * lam[0],
                             meas_ratio=msd(th_ratio), meas_time=msd(accth / n_),
                             meas_etaeff_lam1=msd(acceff / n_ * lam[0]),
                             top1_share_meas=msd(Ebar[:, 0] / Ebar.sum(1)), top1_share_pred=float(E_pred[0] / E_pred.sum()),
                             bulk_energy_meas_over_pred=float(Ebar[:, K:].sum() / S / E_pred[K:].sum()),
                             dom_energy_meas_over_pred=float(Ebar[:, :K].sum() / S / E_pred[:K].sum())))
            r_ = rows[-1]
            print(f"[M1 noise p={p} m={m}] nu/g*={rel:5.2f}: theta pred(SC)={pred:.5f} meas(ratio)={r_['meas_ratio'][0]:.5f}"
                  f"+-{r_['meas_ratio'][1]:.5f} meas(time)={r_['meas_time'][0]:.5f} Deng-small={r_['deng_small_eta']:.5f} | "
                  f"eta_eff*lam1 pred={r_['pred_etaeff_lam1']:.4f} meas={r_['meas_etaeff_lam1'][0]:.4f} | "
                  f"top1 pred={r_['top1_share_pred']:.4f} meas={r_['top1_share_meas'][0]:.4f} | "
                  f"E_B meas/pred={r_['bulk_energy_meas_over_pred']:.3f} E_D meas/pred={r_['dom_energy_meas_over_pred']:.3f}")
if "b" in PARTS:
    out["noisy"] = rows
save_json("exp3_m1_vector.json", out)
print("elapsed", time.time() - t0)
