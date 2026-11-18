"""exp2: noise-free commuting (M2) model = exact decoupled scalar recursions (Theorem 1).

  a_i(t+1) = | a_i(t) - eta * f_i(t) |,   sigma_i = lam_i a_i  (a_i = row norm ||c_i||),
  muon : f_i = 1                ht(p): f_i = sigma_i^p
  ech(r): f_i = 1 if sigma_i >= tau else sigma_i/tau,  tau = (r+1)-th largest sigma
  ns5  : f_i = phi5(sigma_i/||sigma||_2)        htns: f_i = phi5(.) * sigma_i^p
  int10: ht(p) step every 10th step, exact Muon step otherwise ('htmuon_interval', idealised)

d = 500, k = 50, eta = 0.01; initial row norms = norms of the rows of a Gaussian d x n matrix
(n = 100, unit variance), i.e. a_i(0) ~ chi_100 ~ 10 +- 0.7 ('large' initialisation, 1000 eta).

Outputs (results/exp2_commuting.json): theta_inf measured vs predicted over a grid of m,
per-direction energy checks, two-phase timing (argmin of theta vs predicted T_D, T_B).
"""
import sys
import time

import numpy as np

from common import fvals, msd, ns5_scalar, ratio_pred, save_json, spectrum, theta_from_energy

D, K, ETA, N_INIT = 500, 50, 0.01, 100
MS = [2, 5, 10, 20, 50, 100, 200, 500]
SEEDS = list(range(8))
TINY = 1e-280

t0 = time.time()
out = dict(config=dict(d=D, k=K, eta=ETA, n_init=N_INIT, seeds=SEEDS, ms=MS))


def init_norms():
    return np.stack([np.linalg.norm(np.random.default_rng(100 + s).standard_normal((D, N_INIT)), axis=1)
                     for s in SEEDS])


def run(lam, kind, T, p=0.125, r=0, a0=None, rec_every=1, tail=200):
    """Vectorised over seeds.  Returns theta_t (seed mean), per-seed tail averages."""
    a = init_norms() if a0 is None else a0.copy()
    S = a.shape[0]
    lam2 = lam ** 2
    th_mean = np.empty(T + 1)
    th_sd = np.empty(T + 1)
    Eacc = np.zeros((S, D))
    thacc = np.zeros(S)
    for t in range(T + 1):
        E = lam2 * a * a
        th = E[:, :K].sum(1) / E.sum(1)
        th_mean[t] = th.mean()
        th_sd[t] = th.std()
        if t > T - tail:
            Eacc += E
            thacc += th
        sig = lam * a
        if kind == "muon":
            f = 1.0
        elif kind == "ht":
            f = sig ** p
        elif kind == "ech":
            tau = -np.partition(-sig, r, axis=1)[:, r:r + 1]
            f = np.minimum(1.0, sig / tau)
        elif kind == "ns5":
            f = ns5_scalar(sig / (np.sqrt((sig * sig).sum(1, keepdims=True)) + 1e-7))
        elif kind == "htns":
            f = ns5_scalar(sig / (np.sqrt((sig * sig).sum(1, keepdims=True)) + 1e-7)) * sig ** p
        elif kind == "int10":
            f = sig ** p if (t + 1) % 10 == 0 else 1.0
        elif kind == "int10ns":
            f = sig ** p if (t + 1) % 10 == 0 else ns5_scalar(
                sig / (np.sqrt((sig * sig).sum(1, keepdims=True)) + 1e-7))
        a = np.maximum(np.abs(a - ETA * f), TINY)
    return th_mean, th_sd, Eacc / tail, thacc / tail, a


# ------------------------------------------------------------------ (A) Muon
rows = []
for m in MS:
    lam = spectrum(D, K, m)
    a0 = init_norms()
    T = 2000
    thm, thsd, Ebar, thbar, a_fin = run(lam, "muon", T)
    # exact solution: |a_t| in {rho, eta - rho}, rho = a0 mod eta, entered at q = floor(a0/eta)
    rho = np.mod(a0, ETA)
    q = np.floor(a0 / ETA)
    exact = np.where((T + 1 - q) % 2 == 0, rho, ETA - rho)
    err_exact = float(np.abs(a_fin - exact).max())
    w = (rho ** 2 + (ETA - rho) ** 2) / 2
    th_exact = theta_from_energy(lam ** 2 * w, K)          # ratio of 2-step averaged energies
    th_ratio = theta_from_energy(Ebar, K)
    psiD, psiB = (lam[:K] ** 2).sum(), (lam[K:] ** 2).sum()
    rows.append(dict(m=m, pred_psi=psiD / (psiD + psiB), lower=psiD / (psiD + 2 * psiB),
                     upper=2 * psiD / (2 * psiD + psiB), meas_ratio=msd(th_ratio), meas_time=msd(thbar),
                     exact_from_phases=msd(th_exact), max_err_exact_solution=err_exact,
                     mean_w_over_eta2=float(w.mean() / ETA ** 2),
                     theta0=float(thm[0]), theta_min_descent=float(thm[:900].min()),
                     theta_max_descent=float(thm[:900].max())))
    r_ = rows[-1]
    print(f"[muon] m={m:4d} pred psiD/psi={r_['pred_psi']:.6f} bounds=[{r_['lower']:.6f},{r_['upper']:.6f}] "
          f"meas={r_['meas_ratio'][0]:.6f}+-{r_['meas_ratio'][1]:.6f} exact-solution err={err_exact:.1e} "
          f"<w>/eta^2={r_['mean_w_over_eta2']:.3f} theta(descent) in [{r_['theta_min_descent']:.5f},{r_['theta_max_descent']:.5f}]")
    if m == 100:
        out["muon_curve_m100"] = dict(theta_mean=thm, theta_sd=thsd)
out["muon"] = rows

# equal initial norms: theta is exactly constant during the descent phase
lam = spectrum(D, K, 100)
a0 = np.full((1, D), 10.0037)
thm, _, _, _, _ = run(lam, "muon", 1200, a0=a0)
out["muon_equal_init_theta_range_t<=1000"] = [float(thm[:1001].min()), float(thm[:1001].max())]
print("[muon] equal init: theta range over descent:", out["muon_equal_init_theta_range_t<=1000"],
      " psiD/psi =", ratio_pred(lam, K, 2))

# ------------------------------------------------------------------ (B) HTMuon(p)
rows = []
for p in [0.125, 0.25, 0.5, 0.75]:
    q = 2 / (1 - p)
    for m in MS:
        lam = spectrum(D, K, m)
        a0m = 10.0
        TD = a0m ** (1 - p) / ((1 - p) * ETA * lam[K - 1] ** p)     # slowest dominant direction
        TB = a0m ** (1 - p) / ((1 - p) * ETA * lam[-1] ** p)        # slowest bulk direction
        T = int(1.25 * TB + 400)
        thm, thsd, Ebar, thbar, a_fin = run(lam, "ht", T, p=p, tail=50)
        Estar = (ETA * lam / 2) ** q
        rel = float(np.abs(lam ** 2 * a_fin ** 2 / Estar - 1).max())
        pred = ratio_pred(lam, K, q)
        tmin = int(np.argmin(thm))
        # first time theta is back within 1% (relative, on 1-theta scale too) of its limit
        fin = thm[-1]
        after = np.where(np.abs(thm[tmin:] - fin) <= 0.01 * max(fin, 1e-300))[0]
        t_rise = int(tmin + after[0]) if len(after) else -1
        rows.append(dict(p=p, q=q, m=m, pred=pred, one_minus_pred=1 - pred, meas=msd(thbar),
                         one_minus_meas=float(1 - thbar.mean()), max_rel_err_energy=rel,
                         theta0=float(thm[0]), theta_min=float(thm.min()), tmin=tmin, TD_pred=TD,
                         t_rise_99=t_rise, TB_pred=TB))
        r_ = rows[-1]
        print(f"[ht p={p}] m={m:4d} pred={pred:.8f} meas={r_['meas'][0]:.8f}+-{r_['meas'][1]:.1e} "
              f"relErr(E_i)={rel:.1e} | theta0={r_['theta0']:.4f} min={r_['theta_min']:.2e} at t={tmin} "
              f"(T_D pred {TD:.0f}); back at t={t_rise} (T_B pred {TB:.0f})")
        if m == 100 and p in (0.125, 0.5):
            out[f"ht{p}_curve_m100"] = dict(theta_mean=thm, theta_sd=thsd, TD=TD, TB=TB)
out["ht"] = rows

if "--skip-echelon" not in sys.argv:
    # -------------------------------------------------------------- (C) Echelon(r)
    rows = []
    for r in [10, 49, 50, 100, 250]:
        for m in MS:
            lam = spectrum(D, K, m)
            T = 30000
            thm, thsd, Ebar, thbar, a_fin = run(lam, "ech", T, r=r, tail=1000)
            active = (Ebar > 1e-20 * Ebar.max(1, keepdims=True)).sum(1)
            frac_top = Ebar[:, :r + 1].sum(1) / Ebar.sum(1)
            w2 = lam ** 2
            pred_unif = w2[:min(K, r + 1)].sum() / w2[:r + 1].sum()
            rows.append(dict(r=r, m=m, pred_uniform_phase=pred_unif, meas=msd(theta_from_energy(Ebar, K)),
                             active=msd(active), frac_energy_top_r_plus_1=msd(frac_top),
                             theta0=float(thm[0]), theta_min=float(thm.min()), tmin=int(np.argmin(thm))))
            r_ = rows[-1]
            print(f"[ech r={r}] m={m:4d} pred(top-(r+1), uniform phases)={pred_unif:.6f} "
                  f"meas={r_['meas'][0]:.6f}+-{r_['meas'][1]:.1e} active={r_['active'][0]:.1f} "
                  f"fracTop={r_['frac_energy_top_r_plus_1'][0]:.6f} min theta={r_['theta_min']:.1e} at {r_['tmin']}")
            if m == 100 and r in (10, 100):
                sub = np.unique(np.concatenate([np.arange(0, 4000, 2), np.arange(4000, T, 50)]))
                out[f"ech{r}_curve_m100"] = dict(t=sub, theta_mean=thm[sub])
    out["ech"] = rows

# ------------------------------------------------------------------ (D) NS5 / htns / interval
rows = []
for kind in ["ns5", "htns", "int10", "int10ns"]:
    for m in MS:
        lam = spectrum(D, K, m)
        T = 12000
        thm, thsd, Ebar, thbar, a_fin = run(lam, kind, T, p=0.125, tail=1000)
        # log-log slope of time-averaged energy vs lam inside the bulk and inside D
        slB = float(np.polyfit(np.log(lam[K:]), np.log(np.maximum(Ebar.mean(0)[K:], 1e-300)), 1)[0])
        slD = float(np.polyfit(np.log(lam[:K]), np.log(np.maximum(Ebar.mean(0)[:K], 1e-300)), 1)[0])
        rows.append(dict(kind=kind, m=m, meas=msd(theta_from_energy(Ebar, K)),
                         one_minus_meas=float(1 - theta_from_energy(Ebar, K).mean()),
                         pred_q2=ratio_pred(lam, K, 2), pred_q16_7=ratio_pred(lam, K, 16 / 7),
                         slope_bulk=slB, slope_dom=slD,
                         bulk_energy_over_eta2lam2=float((Ebar[:, K:] / (ETA * lam[K:]) ** 2).mean())))
        r_ = rows[-1]
        print(f"[{kind}] m={m:4d} meas={r_['meas'][0]:.8f}+-{r_['meas'][1]:.1e} (q=2: {r_['pred_q2']:.8f}, "
              f"q=16/7: {r_['pred_q16_7']:.8f}) slopes: D {slD:.2f} B {slB:.2f} "
              f"<E_B>/(eta lam)^2={r_['bulk_energy_over_eta2lam2']:.3e}")
out["variants"] = rows

save_json("exp2_commuting.json", out)
print("elapsed", time.time() - t0)
