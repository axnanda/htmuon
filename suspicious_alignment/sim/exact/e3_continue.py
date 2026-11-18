"""E3 (continuation) -- the Song et al. experiment for every filter.

From checkpoints on each optimizer's OWN E1 'twophase' trajectory (seed 0; M2, d=200, k=20, n=50, sigma=0.5,
large init, kappa=1) we continue for TC steps at the optimizer's own learning rate with
   full   : W <- W - eta F(G)
   updD   : W <- W - eta P^D F(G)          updB : W <- W - eta P^B F(G)       (project the update)
   gradD  : W <- W - eta F(P^D G)          gradB: W <- W - eta F(P^B G)       (filter the projected gradient)
with two fresh noise seeds.  Output: results/e3_continue.json (+ loss curves in results/e3_continue_curves.npz).

Usage:  python3 e3_continue.py            (about 1.5 CPU-min)
"""
import json
import os

import numpy as np

import specfilt as sf

D, K, N = 200, 20, 50
TC = 200
OPTS = ["sgd", "muon", "ht0.125", "ht0.25", "ht0.5", "ech1", "ech10", "ech20", "ech40"]
# (m, checkpoint steps): chosen from the E1 curves -- see the note for theta / loss-excess of each state
CASES = {20: [100, 1000], 100: [400, 2000], 500: [200, 3000]}
VARIANTS = [("full", None, "update"), ("updD", "D", "update"), ("updB", "B", "update"),
            ("gradD", "D", "grad"), ("gradB", "B", "grad")]


def main():
    cpu = sf.CpuLog("e3_continue")
    rows, curves = [], {}
    log_idx = np.arange(0, TC, 2)
    for tag in ("twophase_a", "twophase_b"):
        ck = np.load(os.path.join(sf.RES, f"e1_{tag}_ckpt.npz"))
        meta = json.load(open(os.path.join(sf.RES, f"e1_{tag}.json")))
        for r in meta["rows"]:
            m = int(r["m"])
            if m not in CASES:
                continue
            prob = sf.Problem(D, K, N, m)
            for step in CASES[m]:
                W = ck[f"{r['rid']}__{step}"].astype(np.float64)
                L0 = float(prob.loss(W))
                th0 = float(prob.theta(prob.grad(W)))
                LD0 = float(0.5 * (prob.maskf * prob.H * W * W).sum())
                for name, proj, mode in VARIANTS:
                    out = sf.run(prob, r["opt"], r["eta"], TC, [101, 102], W0=np.stack([W, W]), proj=proj,
                                 proj_mode=mode, log_idx=log_idx, true_sv_stride=10 ** 6, noise_stream=11)
                    loss = out["loss"]                     # (2, L+1), last column = t = TC
                    Lend = loss[:, -10:].mean(1)
                    row = dict(opt=r["opt"], m=m, t_ckpt=step, variant=name, eta=r["eta"], L0=L0, theta0=th0,
                               LD0_frac=LD0 / L0, loss_final_run=r["loss_late"],
                               L_end=float(Lend.mean()), L_end_sd=float(Lend.std(ddof=1)),
                               ratio=float(Lend.mean() / L0), dL=float(Lend.mean() - L0),
                               L_max_ratio=float(np.nanmax(loss) / L0),
                               theta_end=float(np.nanmean(out["theta"][:, -10:])), diverged=out["diverged"])
                    rows.append(row)
                    curves[f"{r['opt']}_m{m}_t{step}__{name}"] = np.nanmean(loss, axis=0).astype(np.float32)
                rr = [x for x in rows[-5:]]
                print(f"{r['opt']:8s} m={m:3d} t={step:4d} theta={th0:.3f} L0={L0:9.4g} (L_D/L={LD0 / L0:.3f}) | "
                      + "  ".join(f"{x['variant']}:{x['ratio']:.3f}" for x in rr), flush=True)
    curves["t"] = np.concatenate([log_idx, [TC]])
    sf.save_json(os.path.join(sf.RES, "e3_continue.json"), dict(TC=TC, cases=CASES, rows=rows))
    np.savez_compressed(os.path.join(sf.RES, "e3_continue_curves.npz"), **curves)
    cpu.done(n_runs=len(rows))


if __name__ == "__main__":
    main()
