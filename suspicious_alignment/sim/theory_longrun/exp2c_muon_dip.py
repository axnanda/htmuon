"""exp2c: is there a 'phase I' for Muon in the noise-free commuting model?  Exact scalar dynamics
a_i(t+1) = |a_i(t) - eta|  (d = 500, k = 50, eta = 0.01).  Three initialisations:
  equal   a_i(0) = 10.0037 for all i                      (theta is exactly constant during the descent)
  chi100  a_i(0) = row norms of a Gaussian d x 100 matrix (relative spread 7%;  as in exp2)
  chi4    a_i(0) = 5 * row norms of a Gaussian d x 4 matrix (relative spread 35%)
Reports min_t theta_t before the last direction reaches the floor, and the long-run two-step value.
For comparison the same for HTMuon p = 0.125 with the 'equal' initialisation (gap-driven dip)."""
import numpy as np

from common import msd, save_json, spectrum

D, K, ETA = 500, 50, 0.01
MS = [2, 5, 10, 20, 50, 100, 200, 500]
SEEDS = list(range(8))


def inits(kind):
    if kind == "equal":
        return np.full((1, D), 10.0037)
    n, sc = (100, 1.0) if kind == "chi100" else (4, 5.0)
    return np.stack([sc * np.linalg.norm(np.random.default_rng(100 + s).standard_normal((D, n)), axis=1) for s in SEEDS])


rows, curves = [], {}
for kind in ["equal", "chi100", "chi4"]:
    for m in MS:
        lam = spectrum(D, K, m)
        a = inits(kind)
        T = int(a.max() / ETA) + 40
        th = np.empty((T + 1, a.shape[0]))
        for t in range(T + 1):
            E = lam ** 2 * a * a
            th[t] = E[:, :K].sum(1) / E.sum(1)
            a = np.abs(a - ETA)
        tmin = th.argmin(0)
        psi = (lam[:K] ** 2).sum() / (lam ** 2).sum()
        rows.append(dict(opt="muon", init=kind, m=m, psi_ratio=psi, theta0=msd(th[0]), theta_min=msd(th.min(0)),
                         tmin=msd(tmin), theta_end_two_step=msd(0.5 * (th[-1] + th[-2])),
                         first_arrival=float(np.floor(inits(kind).min() / ETA)), last_arrival=float(np.floor(inits(kind).max() / ETA))))
        r = rows[-1]
        print(f"[muon {kind:6s} m={m:3d}] psiD/psi={psi:.6f} theta0={r['theta0'][0]:.6f} min={r['theta_min'][0]:.4e}+-{r['theta_min'][1]:.1e} "
              f"at t={r['tmin'][0]:.0f} (arrivals {r['first_arrival']:.0f}..{r['last_arrival']:.0f}) end={r['theta_end_two_step'][0]:.6f}")
        if m in (2, 100):
            curves[f"muon_{kind}_m{m}"] = dict(theta_mean=th.mean(1), theta_seed0=th[:, 0])
# HT p = 0.125 from the equal initialisation: the dip is produced by the gap alone
p = 0.125
for m in MS:
    lam = spectrum(D, K, m)
    a = inits("equal")
    T = int(10.0037 ** (1 - p) / ((1 - p) * ETA * lam[-1] ** p)) + 200
    th = np.empty(T + 1)
    for t in range(T + 1):
        E = lam ** 2 * a * a
        th[t] = (E[:, :K].sum(1) / E.sum(1))[0]
        a = np.maximum(np.abs(a - ETA * (lam * a) ** p), 1e-280)
    q = 2 / (1 - p)
    w = (lam / lam.max()) ** q
    rows.append(dict(opt="ht0.125", init="equal", m=m, theta0=float(th[0]), theta_min=float(th.min()), tmin=int(th.argmin()),
                     theta_end=float(th[-1]), pred=float(w[:K].sum() / w.sum()),
                     TD_upper=1 + (10.0037 ** (1 - p) / (ETA * lam[K - 1] ** p) - 1) / (1 - p),
                     TB_lower=10.0037 ** (1 - p) / (ETA * lam[K] ** p) - 1))
    r = rows[-1]
    print(f"[ht0.125 equal m={m:3d}] theta0={r['theta0']:.6f} min={r['theta_min']:.3e} at t={r['tmin']} end={r['theta_end']:.8f} "
          f"pred={r['pred']:.8f} | rigorous window: T_D <= {r['TD_upper']:.0f}, T_B(k+1) >= {r['TB_lower']:.0f}")
    if m in (2, 100):
        curves[f"ht0.125_equal_m{m}"] = dict(theta=th)
save_json("exp2c_muon_dip.json", dict(config=dict(d=D, k=K, eta=ETA, seeds=SEEDS), rows=rows, curves=curves))
