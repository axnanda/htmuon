"""How far are the commuting-case formulas from the truth for generic states?  (Section 8 of the note)

 Q1  model (M2), Gaussian states of aspect ratio n/d: the commuting ("row-norm") formulas use only
     a_i = ||c_i||; the truth is the direct SVD.  We report relative errors of T^S, V^S, of eta*, of
     the loss thresholds, the absolute error of the one-step alignment change, and how often the
     commuting formulas predict the SIGN of the alignment change / the ORDER of the loss thresholds.
 Q2  model (M3), L = 1/2 tr(W^T A W B):
     (a) exact one-step formula when the rows of U^T W B are mutually orthogonal ("left-commuting")
     (b) aligned states (generalised-permutation coefficient matrix) == coordinate model with
         spectrum lam_i * beta_pi(i)   [product dominant block]
     (c) generic states: error of the Rayleigh-quotient version of the commuting formula
Output: results/noncommuting.json
"""
import os
import sys
import time
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import (FILTERS, f_echelon, apply_filter, rand_orth, make_spectrum, block_masks,
                    energies, commuting_coeffs, jdump)

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
os.makedirs(OUT, exist_ok=True)
rng = np.random.default_rng(20261123)
res = {"seed": 20261123, "checks": {}}
t0 = time.time()


def rel(x, y):
    return abs(x - y) / max(abs(x), abs(y), 1e-300)


def exact_coeffs(lam, C, Phi, D):
    out = {}
    for name, S in (("D", D), ("B", ~D)):
        out["s" + name] = np.sum(lam[S] ** 2 * np.sum(C[S] ** 2, axis=1))
        out["T" + name] = np.sum(lam[S] ** 2 * np.sum(C[S] * Phi[S], axis=1))
        out["V" + name] = np.sum(lam[S] ** 2 * np.sum(Phi[S] ** 2, axis=1))
        out["N" + name] = np.sum(lam[S] * np.sum(C[S] * Phi[S], axis=1))
        out["R" + name] = np.sum(lam[S] * np.sum(Phi[S] ** 2, axis=1))
    out["q"] = 2 * (out["sD"] * out["TB"] - out["sB"] * out["TD"])
    out["p"] = out["sB"] * out["VD"] - out["sD"] * out["VB"]
    return out


def dtheta(co, eta, T="T", V="V"):
    sDn = co["sD"] - 2 * eta * co[T + "D"] + eta ** 2 * co[V + "D"]
    sBn = co["sB"] - 2 * eta * co[T + "B"] + eta ** 2 * co[V + "B"]
    return sDn / (sDn + sBn) - co["sD"] / (co["sD"] + co["sB"])


# ---------------------------------------------------------------- Q1  model (M2)
q1 = {"rows": []}
d = 100
NTR = 24
for n in (100, 200, 500, 2000, 8000):
    for name in ("muon", "ht0.125", "ht0.5", "echelon_k", "sgd"):
        acc = dict(T=[], V=[], etastar=[], etaLD=[], etaLB=[], dth_abs=[], dth_rel=[], sign_ok=[], order_ok=[],
                   offdiag=[], sign_tests=0, root_both=0, qsign_ok=[])
        rs = np.random.default_rng(1000 + n)       # same states for every filter
        for trial in range(NTR):
            k = int(rs.integers(5, 20))
            m = [2.0, 5.0, 20.0][trial % 3]
            lam = make_spectrum(d, k, m, rs)
            D, B = block_masks(d, k)
            scale = np.exp(rs.normal(0, 0.6, d)) * np.where(D, 10 ** rs.uniform(-1.2, 0.8), 1.0)
            C = scale[:, None] * rs.standard_normal((d, n)) / np.sqrt(n)
            G = lam[:, None] * C                       # eigen-coordinates (U = I without loss of generality)
            fvec = f_echelon(k) if name == "echelon_k" else FILTERS[name]
            Phi = apply_filter(G, fvec)
            ex = exact_coeffs(lam, C, Phi, D)
            a = np.linalg.norm(C, axis=1)
            if name == "echelon_k":
                # the commuting formula needs the filter on the row-norm "spectrum" lam_i a_i
                cm = commuting_coeffs(lam, a, D, f_echelon(k))
            else:
                cm = commuting_coeffs(lam, a, D, fvec)
            cmx = dict(sD=cm["sD"], sB=cm["sB"], TD=cm["tauD"], TB=cm["tauB"], VD=cm["uD"], VB=cm["uB"])
            M = G @ G.T
            acc["offdiag"].append(np.linalg.norm(M - np.diag(np.diag(M))) / np.linalg.norm(np.diag(M)))
            for key in ("D", "B"):
                acc["T"].append(rel(ex["T" + key], cm["tau" + key]))
                acc["V"].append(rel(ex["V" + key], cm["u" + key]))
            acc["etaLD"].append(rel(2 * ex["ND"] / ex["RD"], 2 * cm["ND"] / cm["RD"]))
            acc["etaLB"].append(rel(2 * ex["NB"] / ex["RB"], 2 * cm["NB"] / cm["RB"]))
            acc["order_ok"].append(float((ex["ND"] / ex["RD"] < ex["NB"] / ex["RB"]) == (cm["ND"] / cm["RD"] < cm["NB"] / cm["RB"])))
            acc["qsign_ok"].append(float(np.sign(ex["q"]) == np.sign(cm["q"])))
            es_ex = -ex["q"] / ex["p"]
            es_cm = -cm["q"] / cm["p"]
            if es_ex > 0 and es_cm > 0:
                acc["etastar"].append(rel(es_ex, es_cm))
                acc["root_both"] += 1
            eta_ref = es_cm if es_cm > 0 else np.sum(a * cm["f"]) / np.sum(cm["f"] ** 2)
            for fac in (0.25, 0.7, 1.5, 4.0):
                dt_ex = dtheta(ex, fac * eta_ref)
                dt_cm = dtheta(cmx, fac * eta_ref)
                acc["dth_abs"].append(abs(dt_ex - dt_cm))
                acc["dth_rel"].append(abs(dt_ex - dt_cm) / max(abs(dt_ex), 1e-12))
                acc["sign_ok"].append(float(np.sign(dt_ex) == np.sign(dt_cm)))
        q1["rows"].append(dict(d=d, n=n, filter=name, n_states=NTR,
                               offdiag_ratio_median=float(np.median(acc["offdiag"])),
                               T_relerr_median=float(np.median(acc["T"])), T_relerr_max=float(np.max(acc["T"])),
                               V_relerr_median=float(np.median(acc["V"])), V_relerr_max=float(np.max(acc["V"])),
                               etastar_relerr_median=(float(np.median(acc["etastar"])) if acc["etastar"] else None),
                               etastar_relerr_max=(float(np.max(acc["etastar"])) if acc["etastar"] else None),
                               n_both_roots_positive=acc["root_both"],
                               etaLossD_relerr_median=float(np.median(acc["etaLD"])), etaLossB_relerr_median=float(np.median(acc["etaLB"])),
                               etaLossD_relerr_max=float(np.max(acc["etaLD"])), etaLossB_relerr_max=float(np.max(acc["etaLB"])),
                               dtheta_abserr_median=float(np.median(acc["dth_abs"])), dtheta_abserr_max=float(np.max(acc["dth_abs"])),
                               dtheta_relerr_median=float(np.median(acc["dth_rel"])),
                               sign_agreement=float(np.mean(acc["sign_ok"])), q_sign_agreement=float(np.mean(acc["qsign_ok"])),
                               threshold_order_agreement=float(np.mean(acc["order_ok"]))))
res["checks"]["Q1_M2_generic_states"] = q1

# ---------------------------------------------------------------- Q2  model (M3)
q2 = {"a_left_commuting": {}, "b_aligned": {}, "c_generic_rows": []}


def upd(dic, key, val):
    dic[key] = max(dic.get(key, 0.0), float(val))


INDEX = {"sgd": 1.0, "muon": 0.0, "ht0.125": 0.125, "ht0.5": 0.5}
for (d, n) in [(40, 60), (80, 80), (100, 150)]:
    for trial in range(4):
        k = int(rng.integers(3, d // 5))
        lam = make_spectrum(d, k, [2.0, 5.0, 20.0, 50.0][trial], rng)
        D, B = block_masks(d, k)
        U = rand_orth(d, rng)
        VB = rand_orth(n, rng)
        condB = [1.0, 3.0, 10.0, 30.0][trial]
        beta = np.exp(rng.uniform(0, np.log(condB), n)) if condB > 1 else np.ones(n)
        Bm = (VB * beta) @ VB.T
        A = (U * lam) @ U.T
        # ---- (a) left-commuting: rows of C' = U^T W B mutually orthogonal (not eigenvectors of B)
        ap = np.exp(rng.normal(0, 0.7, d))
        Qr = rand_orth(n, rng)[:d]
        Cp = ap[:, None] * Qr                                  # C' = U^T W B
        W = U @ Cp @ np.linalg.inv(Bm)
        G = A @ W @ Bm
        sig = lam * ap
        bi = np.einsum("ij,jk,ik->i", Qr, Bm, Qr)
        b2i = np.einsum("ij,jk,ik->i", Qr, Bm @ Bm, Qr)
        for name in INDEX:
            fv = FILTERS[name](sig)
            F = apply_filter(G, FILTERS[name])
            eta = 0.4 * np.sum(ap * fv * bi) / np.sum(fv ** 2 * b2i)
            for e in (0.3 * eta, eta, 3 * eta):
                Wn = W - e * F
                Cpn = U.T @ Wn @ Bm
                for S, key in ((D, "D"), (B, "B")):
                    direct = np.sum(lam[S] ** 2 * np.sum(Cpn[S] ** 2, axis=1))
                    form = np.sum(lam[S] ** 2 * (ap[S] ** 2 - 2 * e * fv[S] * ap[S] * bi[S] + e ** 2 * fv[S] ** 2 * b2i[S]))
                    upd(q2["a_left_commuting"], name + ":s_next_relerr", rel(direct, form))
                # loss:  L = 1/2 tr(W^T A W B)
                dL = 0.5 * np.sum((A @ Wn) * (Wn @ Bm)) - 0.5 * np.sum((A @ W) * (W @ Bm))
                formL = -e * np.sum(sig * fv) + 0.5 * e ** 2 * np.sum(lam * fv ** 2 * bi)
                upd(q2["a_left_commuting"], name + ":dL_relerr", abs(dL - formL) / (0.5 * np.sum((A @ W) * (W @ Bm))))
        # ---- (b) aligned states: C = U^T W V_B has one non-zero per row and column
        r = min(d, n)
        perm = rng.permutation(n)[:r]
        aa = np.exp(rng.normal(0, 0.7, r))
        Cal = np.zeros((d, n))
        Cal[np.arange(r), perm] = aa * rng.choice([-1.0, 1.0], r)
        W = U @ Cal @ VB.T
        G = A @ W @ Bm
        h = lam[:r] * beta[perm]                              # Hessian eigenvalue of the pair (i, pi(i))
        # product dominant block: the K pairs with the largest Hessian eigenvalue among occupied pairs
        K = max(2, r // 8)
        Dp = np.zeros(r, bool)
        Dp[np.argsort(-h)[:K]] = True
        for name in INDEX:
            F = apply_filter(G, FILTERS[name])
            co = commuting_coeffs(h, aa, Dp, FILTERS[name])
            eta = 0.4 * np.sum(aa * co["f"]) / np.sum(co["f"] ** 2)
            Cn = U.T @ (W - eta * F) @ VB
            offsupport = Cn.copy()
            offsupport[np.arange(r), perm] = 0.0
            upd(q2["b_aligned"], name + ":mass_leaving_support", np.abs(offsupport).max() / np.abs(Cn).max())
            an = np.abs(Cn[np.arange(r), perm])
            upd(q2["b_aligned"], name + ":coefficient_relerr", np.abs(an - np.abs(aa - eta * co["f"])).max() / aa.max())
            e_dir = h ** 2 * an ** 2
            th_dir = e_dir[Dp].sum() / e_dir.sum()
            th0 = co["sD"] / (co["sD"] + co["sB"])
            sn = (co["sD"] - 2 * eta * co["tauD"] + eta ** 2 * co["uD"]) + (co["sB"] - 2 * eta * co["tauB"] + eta ** 2 * co["uB"])
            upd(q2["b_aligned"], name + ":dtheta_abserr", abs((th_dir - th0) - eta * (co["p"] * eta + co["q"]) / ((co["sD"] + co["sB"]) * sn)))

# ---- (c) generic M3 states, left dominant block {i <= k} x all columns
d = 60
for n in (60, 240, 960):
    for condB in (1.0, 3.0, 30.0):
        for name in ("muon", "ht0.125", "sgd"):
            errT, errV, errdth, sign_ok = [], [], [], []
            rs = np.random.default_rng(5000 + n + int(10 * condB))
            for trial in range(12):
                k = int(rs.integers(4, 12))
                lam = make_spectrum(d, k, [2.0, 5.0, 20.0][trial % 3], rs)
                D, B = block_masks(d, k)
                beta = np.exp(rs.uniform(0, np.log(condB), n)) if condB > 1 else np.ones(n)
                scale = np.exp(rs.normal(0, 0.5, d)) * np.where(D, 10 ** rs.uniform(-1, 0.5), 1.0)
                # coordinates C = U^T W V_B generic; work directly in the (u_i, v_j) frame
                C = scale[:, None] * rs.standard_normal((d, n)) / np.sqrt(n)
                Cp = C * beta[None, :]                           # C' = C diag(beta)
                Gt = lam[:, None] * Cp                           # U^T G V_B
                Phi = apply_filter(Gt, FILTERS[name])
                PhiB = Phi * beta[None, :]                       # update of C' is  -eta Phi diag(beta)
                ex = dict()
                for S, key in ((D, "D"), (B, "B")):
                    ex["s" + key] = np.sum(lam[S] ** 2 * np.sum(Cp[S] ** 2, axis=1))
                    ex["T" + key] = np.sum(lam[S] ** 2 * np.sum(Cp[S] * PhiB[S], axis=1))
                    ex["V" + key] = np.sum(lam[S] ** 2 * np.sum(PhiB[S] ** 2, axis=1))
                # Rayleigh-quotient commuting formula
                ap = np.linalg.norm(Cp, axis=1)
                Qr = Cp / ap[:, None]
                bi = np.sum(Qr ** 2 * beta[None, :], axis=1)
                b2i = np.sum(Qr ** 2 * beta[None, :] ** 2, axis=1)
                fv = FILTERS[name](lam * ap)
                cm = dict(sD=ex["sD"], sB=ex["sB"])
                for S, key in ((D, "D"), (B, "B")):
                    cm["T" + key] = np.sum(lam[S] ** 2 * ap[S] * fv[S] * bi[S])
                    cm["V" + key] = np.sum(lam[S] ** 2 * fv[S] ** 2 * b2i[S])
                    errT.append(rel(ex["T" + key], cm["T" + key]))
                    errV.append(rel(ex["V" + key], cm["V" + key]))
                eta_ref = 0.5 * (cm["TD"] + cm["TB"]) / (cm["VD"] + cm["VB"])
                for fac in (0.3, 1.0, 3.0):
                    d1, d2 = dtheta(ex, fac * eta_ref), dtheta(cm, fac * eta_ref)
                    errdth.append(abs(d1 - d2))
                    sign_ok.append(float(np.sign(d1) == np.sign(d2)))
            q2["c_generic_rows"].append(dict(d=d, n=n, condB=condB, filter=name,
                                             T_relerr_median=float(np.median(errT)), V_relerr_median=float(np.median(errV)),
                                             T_relerr_max=float(np.max(errT)), V_relerr_max=float(np.max(errV)),
                                             dtheta_abserr_median=float(np.median(errdth)), dtheta_abserr_max=float(np.max(errdth)),
                                             sign_agreement=float(np.mean(sign_ok))))
res["checks"]["Q2_M3"] = q2

res["runtime_sec"] = time.time() - t0
jdump(res, os.path.join(OUT, "noncommuting.json"))
print("Q1  (d=100)   n   filter      offdiag  T med/max        V med/max        eta* med/max (#)   etaL_D med  etaL_B med  dth abs med/max   sign  qsign order")
for r in q1["rows"]:
    print("   %5d %-10s %.3f   %.3f/%.3f   %.3f/%.3f   %s/%s (%d)   %.3f  %.3f   %.1e/%.1e   %.2f  %.2f  %.2f" % (
        r["n"], r["filter"], r["offdiag_ratio_median"], r["T_relerr_median"], r["T_relerr_max"], r["V_relerr_median"], r["V_relerr_max"],
        "%.3f" % r["etastar_relerr_median"] if r["etastar_relerr_median"] is not None else "-",
        "%.3f" % r["etastar_relerr_max"] if r["etastar_relerr_max"] is not None else "-", r["n_both_roots_positive"],
        r["etaLossD_relerr_median"], r["etaLossB_relerr_median"], r["dtheta_abserr_median"], r["dtheta_abserr_max"],
        r["sign_agreement"], r["q_sign_agreement"], r["threshold_order_agreement"]))
print("Q2a", {k: "%.1e" % v for k, v in sorted(q2["a_left_commuting"].items())})
print("Q2b", {k: "%.1e" % v for k, v in sorted(q2["b_aligned"].items())})
for r in q2["c_generic_rows"]:
    print("Q2c n=%4d condB=%4.0f %-8s T med %.3f max %.3f | V med %.3f max %.3f | dth abs med %.1e max %.1e | sign %.2f" % (
        r["n"], r["condB"], r["filter"], r["T_relerr_median"], r["T_relerr_max"], r["V_relerr_median"], r["V_relerr_max"],
        r["dtheta_abserr_median"], r["dtheta_abserr_max"], r["sign_agreement"]))
print("runtime %.1fs" % res["runtime_sec"])
