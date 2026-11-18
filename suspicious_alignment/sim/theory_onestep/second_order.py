"""First correction to the commuting (row-norm) formulas for generic states of model (M2)
(Proposition 8.1 of the note).

For an index-wise filter and M = Lam C C^T Lam = diag(sigma_i^2) + E (E = off-diagonal part),
    g(M)_ii  ~  g(sigma_i^2) + sum_{j != i} M_ij^2 * g[sigma_i^2, sigma_i^2, sigma_j^2]
(second-order divided difference; Daleckii-Krein expansion).  With g1(t) = sqrt(t) f(sqrt t) and
g2(t) = f(sqrt t)^2 this corrects T^S, V^S, N^S, R^S.  We compare, against the direct SVD,
  (0) the commuting row-norm formula            (error first order in |E|^2 ~ d/n)
  (2) the second-order corrected formula        (error of higher order)
for Gaussian states with heterogeneous row scales, d = 100, n in {400, 1600, 6400, 25600}.
Output: results/second_order.json
"""
import os
import sys
import time
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import FILTERS, apply_filter, make_spectrum, block_masks, jdump

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
t0 = time.time()
P = {"muon": 0.0, "ht0.125": 0.125, "ht0.5": 0.5}


def dd2(g, dg, x, y):
    """g[x, x, y] = (g[x, y] - g'(x)) / (y - x), with the confluent limit handled by a guard."""
    gxy = (g(x) - g(y)) / (x - y)
    return (gxy - dg(x)) / (y - x)


def corrected_diag(M, g, dg):
    dvec = np.diag(M).copy()
    d = dvec.size
    out = g(dvec).copy()
    for i in range(d):
        j = np.arange(d) != i
        x, y = dvec[i], dvec[j]
        ok = np.abs(y - x) > 1e-9 * x
        out[i] += np.sum(M[i, j][ok] ** 2 * dd2(g, dg, x, y[ok]))
    return out


rows = []
d = 100
for n in (400, 1600, 6400, 25600):
    acc = {name: dict(e0=[], e2=[], q0=[], q2=[], w0=[], w2=[]) for name in P}
    rs = np.random.default_rng(31 + n)
    for trial in range(6):
        k = int(rs.integers(5, 20))
        m = [2.0, 5.0, 20.0][trial % 3]
        lam = make_spectrum(d, k, m, rs)
        D, B = block_masks(d, k)
        scale = np.exp(rs.normal(0, 0.5, d))
        C = scale[:, None] * rs.standard_normal((d, n)) / np.sqrt(n)
        G = lam[:, None] * C
        M = G @ G.T
        sig2 = np.diag(M)
        sD, sB = sig2[D].sum(), sig2[B].sum()
        for name, p in P.items():
            Phi = apply_filter(G, FILTERS[name])
            g1 = lambda t, p=p: t ** ((1 + p) / 2)
            dg1 = lambda t, p=p: (1 + p) / 2 * t ** ((p - 1) / 2)
            g2 = lambda t, p=p: t ** p
            dg2 = lambda t, p=p: p * t ** (p - 1)
            G1_0, G2_0 = g1(sig2), g2(sig2)
            G1_2 = corrected_diag(M, g1, dg1)
            G2_2 = corrected_diag(M, g2, dg2) if p > 0 else np.ones(d)
            ex, f0, f2 = {}, {}, {}
            for key, S in (("D", D), ("B", B)):
                ex["T" + key] = np.sum(lam[S] ** 2 * np.sum(C[S] * Phi[S], axis=1))
                ex["V" + key] = np.sum(lam[S] ** 2 * np.sum(Phi[S] ** 2, axis=1))
                ex["N" + key] = np.sum(lam[S] * np.sum(C[S] * Phi[S], axis=1))
                ex["R" + key] = np.sum(lam[S] * np.sum(Phi[S] ** 2, axis=1))
                for dst, A1, A2 in ((f0, G1_0, G2_0), (f2, G1_2, G2_2)):
                    dst["T" + key] = np.sum(lam[S] * A1[S])
                    dst["V" + key] = np.sum(lam[S] ** 2 * A2[S])
                    dst["N" + key] = np.sum(A1[S])
                    dst["R" + key] = np.sum(lam[S] * A2[S])
            a = acc[name]
            for kk in ("TD", "TB", "VD", "VB", "ND", "NB", "RD", "RB"):
                a["e0"].append(abs(f0[kk] - ex[kk]) / abs(ex[kk]))
                a["e2"].append(abs(f2[kk] - ex[kk]) / abs(ex[kk]))
            qf = lambda z: 2 * (sD * z["TB"] - sB * z["TD"]) / (sD + sB) ** 2
            wf = lambda z: (z["NB"] / z["RB"]) / (z["ND"] / z["RD"])
            a["q0"].append(abs(qf(f0) - qf(ex)) / abs(qf(ex)))
            a["q2"].append(abs(qf(f2) - qf(ex)) / abs(qf(ex)))
            a["w0"].append(abs(wf(f0) - wf(ex)) / wf(ex))
            a["w2"].append(abs(wf(f2) - wf(ex)) / wf(ex))
    for name in P:
        a = acc[name]
        rows.append(dict(d=d, n=n, filter=name, n_states=6,
                         TVNR_relerr_rownorm_max=float(np.max(a["e0"])), TVNR_relerr_second_order_max=float(np.max(a["e2"])),
                         q_relerr_rownorm_median=float(np.median(a["q0"])), q_relerr_second_order_median=float(np.median(a["q2"])),
                         q_relerr_rownorm_max=float(np.max(a["q0"])), q_relerr_second_order_max=float(np.max(a["q2"])),
                         window_ratio_relerr_rownorm_max=float(np.max(a["w0"])), window_ratio_relerr_second_order_max=float(np.max(a["w2"]))))
jdump(dict(seed="31+n", rows=rows, runtime_sec=time.time() - t0), os.path.join(OUT, "second_order.json"))
for r in rows:
    print("n=%6d %-8s T,V,N,R max relerr: row-norm %.2e -> 2nd order %.2e | q relerr med %.2e -> %.2e (max %.2e -> %.2e) | window ratio max %.2e -> %.2e" % (
        r["n"], r["filter"], r["TVNR_relerr_rownorm_max"], r["TVNR_relerr_second_order_max"], r["q_relerr_rownorm_median"], r["q_relerr_second_order_median"],
        r["q_relerr_rownorm_max"], r["q_relerr_second_order_max"], r["window_ratio_relerr_rownorm_max"], r["window_ratio_relerr_second_order_max"]))
print("runtime %.1fs" % (time.time() - t0))
