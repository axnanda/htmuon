"""E4 -- robustness of the key comparisons.

 aniso : (M2) with anisotropic gradient noise, Sigma ∝ A (row i has variance sigma^2 lam_i / mean(lam);
         same trace as the isotropic case).  d=200, k=20, n=50, m in {20, 100}.
 kron  : (M3) Kronecker lift L = 1/2 tr(W^T A W B), B = diag(j^-alpha), isotropic noise.
           V1: alpha = 0.5, dominant set = the K = k*n = 1000 largest products lam_i mu_j
               (for m >= 10 these are exactly the D rows, i.e. the same projector as in M2)
           V2: alpha = 1.0, K = 500 (a 'staircase' set of entries, not a product set; no spectral gap)
Each: large-init run (T=2000) and zero-init 'late' run, kappa = 1 rule learning rates, 2 seeds, plus the
one-step alignment / projected-loss statistics (as in e2e3_onestep.py) at t in {0, 100, 2000} of the
large-init trajectories (SGD's trajectory: all filters; filter X's trajectory: X and SGD).

Usage:  python3 e4_robust.py aniso|kron        (about 2 + 3.5 CPU-min)
"""
import os
import sys

import numpy as np

import specfilt as sf
import e1_trajectories as e1
import e2e3_onestep as os1

OPTS = ["sgd", "muon", "ht0.125", "ht0.5", "ech1", "ech20", "ech40"]
CK = [0, 100, 2000]


def main():
    part = sys.argv[1]
    cpu = sf.CpuLog("e4_" + part)
    e1.CKPT_STEPS = CK
    rows, logs, ck = [], {}, {}
    settings = []
    if part == "aniso":
        for m, Tl in ((20, 800), (100, 2500)):
            settings.append((dict(noise="propA", m=m), Tl))
    elif part == "kron":
        for m in (20, 100):
            settings.append((dict(mu_alpha=0.5, Kdom=1000, m=m), 1500))
            settings.append((dict(mu_alpha=1.0, Kdom=500, m=m), 1500))
    else:
        raise SystemExit(part)
    onestep_rows = []
    for base, Tl in settings:
        etas = {}
        ridmap = {}
        for o in OPTS:
            r = e1.run_config(dict(opt=o, T=2000, seeds=[0, 1], ckpt=True, **base), logs, ck)
            r["setting"] = "large"
            rows.append(r)
            etas[o] = r["eta"]
            ridmap[o] = r["rid"]
        for o in OPTS:
            r = e1.run_config(dict(opt=o, T=Tl, seeds=[0, 1], init="zero", **base), logs, ck)
            r["setting"] = "late"
            rows.append(r)
        mu = None if base.get("mu_alpha") is None else np.arange(1, e1.N + 1) ** (-float(base["mu_alpha"]))
        prob = sf.Problem(e1.D, e1.K, e1.N, base["m"], noise=base.get("noise", "iso"), mu=mu, K=base.get("Kdom"))
        for o in OPTS:
            for step in CK:
                W = ck[f"{ridmap[o]}__{step}"].astype(np.float64)
                opts = OPTS if o == "sgd" else [o, "sgd"]
                info, per, _ = os1.analyse_state(prob, W, opts, 32, seed=step + 17, eta_run=etas)
                onestep_rows.append(dict(traj=o, t=step, **base, **info, per_opt=per))
        print("one-step done for", base, flush=True)
    for r in rows:
        r.pop("ckpt", None)
    sf.save_json(os.path.join(sf.RES, f"e4_{part}.json"),
                 dict(part=part, d=e1.D, k=e1.K, n=e1.N, rows=rows, onestep=onestep_rows))
    np.savez_compressed(os.path.join(sf.RES, f"e4_{part}_logs.npz"), **logs)
    cpu.done(n_runs=len(rows), n_svd=int(sum(r["n_svd"] for r in rows)))


if __name__ == "__main__":
    main()
