"""Dependence on the Hessian gap m = lam_k / lam_{k+1} of (i) the sign of q_f (Deng's sign fact),
(ii) the effective gap <nu>_D / <nu>_B, (iii) the loss-threshold window eta_B^loss / eta_D^loss,
for commuting states of model (M2), measured on the actual matrices (direct SVD).

Two protocols:
  "fixed coefficients": row norms a_i i.i.d. log-normal, same law on D and B; only lam changes with m
  "fixed alignment"   : same, then the dominant rows are rescaled so that theta equals a target
Output: results/gap_dependence.json
"""
import os
import sys
import time
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import (FILTERS, f_echelon, apply_filter, rand_orth, block_masks, commuting_state,
                    commuting_coeffs, jdump)

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
os.makedirs(OUT, exist_ok=True)
t0 = time.time()
d, n, k = 100, 120, 10
D, B = block_masks(d, k)
NST = 20
ms = [2.0, 5.0, 20.0, 100.0, 1000.0]
names = ["sgd", "ht0.5", "ht0.25", "ht0.125", "muon", "echelon_k", "echelon_0"]
rows = []
maxdisc = 0.0
for protocol in ("fixed_coefficients", "fixed_alignment_0.9", "fixed_alignment_0.99"):
    for name in names:
        fvec = {"echelon_k": f_echelon(k), "echelon_0": f_echelon(0)}.get(name) or FILTERS[name]
        for m in ms:
            rs = np.random.default_rng(77)                 # same base states for every (filter, m)
            ratios, effgap, qneg = [], [], []
            for st in range(NST):
                dom = 1.0 + rs.uniform(0, 1.5, k)
                dom[np.argmin(dom)] = 1.0
                blk = rs.uniform(0.1, 1.0, d - k)
                blk[np.argmax(blk)] = 1.0
                lam = np.concatenate([m * np.sort(dom)[::-1], np.sort(blk)[::-1]])
                a = np.exp(rs.normal(0, 0.5, d))
                U = rand_orth(d, rs)
                if protocol.startswith("fixed_alignment"):
                    target = float(protocol.split("_")[-1])
                    sD = np.sum(lam[D] ** 2 * a[D] ** 2)
                    sB = np.sum(lam[B] ** 2 * a[B] ** 2)
                    a = a * np.where(D, np.sqrt(target / (1 - target) * sB / sD), 1.0)
                co = commuting_coeffs(lam, a, D, fvec)
                # direct evaluation of the two loss thresholds on the actual matrices
                W, Q = commuting_state(U, a, n, rs)
                G = (U * lam) @ (U.T @ W)
                Phi = U.T @ apply_filter(G, fvec)
                C = U.T @ W
                et = {}
                for S, key in ((D, "D"), (B, "B")):
                    N = np.sum(lam[S] * np.sum(C[S] * Phi[S], axis=1))
                    R = np.sum(lam[S] * np.sum(Phi[S] ** 2, axis=1))
                    et[key] = 2 * N / R
                    maxdisc = max(maxdisc, abs(et[key] - 2 * co["N" + key] / co["R" + key]) / et[key])
                ratios.append(et["B"] / et["D"])
                effgap.append((co["tauD"] / co["sD"]) / (co["tauB"] / co["sB"]))
                qneg.append(float(co["q"] < 0))
            rows.append(dict(protocol=protocol, filter=name, m=m, median_window_ratio=float(np.median(ratios)),
                             frac_deng_ordering=float(np.mean(np.array(ratios) > 1)),
                             median_effective_gap=float(np.median(effgap)), frac_q_negative=float(np.mean(qneg))))
# log-log slopes of the median window ratio in m (between m = 20 and m = 1000)
slopes = {}
for protocol in ("fixed_coefficients", "fixed_alignment_0.9", "fixed_alignment_0.99"):
    for name in names:
        r = {x["m"]: x["median_window_ratio"] for x in rows if x["protocol"] == protocol and x["filter"] == name}
        slopes[protocol + ":" + name] = float(np.log(r[1000.0] / r[20.0]) / np.log(1000.0 / 20.0))
res = dict(seed=77, d=d, n=n, k=k, n_states=NST, rows=rows, loglog_slope_window_ratio_vs_m=slopes,
           max_relerr_formula_vs_direct_thresholds=maxdisc, runtime_sec=time.time() - t0)
jdump(res, os.path.join(OUT, "gap_dependence.json"))
for protocol in ("fixed_coefficients", "fixed_alignment_0.9", "fixed_alignment_0.99"):
    print(protocol)
    for name in names:
        rr = [x for x in rows if x["protocol"] == protocol and x["filter"] == name]
        print("  %-10s window ratio: %s | slope %.3f | P(q<0): %s | eff.gap: %s" % (
            name, " ".join("%9.3g" % x["median_window_ratio"] for x in rr), slopes[protocol + ":" + name],
            " ".join("%.2f" % x["frac_q_negative"] for x in rr), " ".join("%8.3g" % x["median_effective_gap"] for x in rr)))
print("max relerr formula vs direct %.1e ; runtime %.1fs" % (maxdisc, res["runtime_sec"]))
