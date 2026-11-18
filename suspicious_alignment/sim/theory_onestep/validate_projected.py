"""Projected filtered updates (Section 5 of the note): noise-free validation against direct SVDs.

 FP_S(G) = P^S F(G)   "filter, then project the update"
 PF_S(G) = F(P^S G)   "project the gradient, then filter"

 P1  coincidence FP = PF  (commuting / block-commuting states, index-wise filters); they differ for
     generic states and for Echelon (state-dependent filter)
 P2  exact loss change  dL = -eta <AW, Delta> + eta^2/2 <Delta, A Delta>  and threshold 2<AW,Delta>/<Delta,A Delta>
 P3  commuting formulas  eta_S^loss = 2 sum_S sigma f(sigma) / sum_S lam f(sigma)^2 ; window test
 P4  additivity  dL(full) = dL(FP_D) + dL(FP_B)  for arbitrary states and filters
 P5  two-level states: ratio eta_B/eta_D = m^p (a_B/a_D)^(1-p) = m (rho (1-theta)/theta)^((1-p)/2)
 P6  Echelon(r): both notions in commuting states (global tau vs block tau)
 P7  model (M1): both notions, thresholds and critical alignment of the PF variant
Output: results/projected.json
"""
import os
import sys
import time
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import (FILTERS, f_echelon, f_muon, f_ht, f_sgd, apply_filter, rand_orth,
                    make_spectrum, block_masks, commuting_state, energies, theta_of, loss_of,
                    commuting_coeffs, echelon_tau, jdump)

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
os.makedirs(OUT, exist_ok=True)
rng = np.random.default_rng(20261120)
res = {"seed": 20261120, "checks": {}}
t0 = time.time()
INDEXWISE = ["sgd", "muon", "ht0.125", "ht0.25", "ht0.5"]


def upd(dic, key, val):
    dic[key] = max(dic.get(key, 0.0), float(val))


def rel(x, y):
    return abs(x - y) / max(abs(x), abs(y), 1e-300)


def proj(U, S):
    return U[:, S] @ U[:, S].T


def lossW(U, lam, W):
    return loss_of(lam, U.T @ W)


def NR(U, lam, W, Delta):
    G = (U * lam) @ (U.T @ W)
    return np.sum(G * Delta), np.sum(Delta * ((U * lam) @ (U.T @ Delta)))


# ---------------------------------------------------------------- P1 coincidence
p1 = {}
for (d, n) in [(40, 60), (80, 80), (100, 150)]:
    for trial in range(3):
        k = int(rng.integers(3, d // 4))
        lam = make_spectrum(d, k, [2.0, 10.0, 50.0][trial], rng)
        D, B = block_masks(d, k)
        U = rand_orth(d, rng)
        A = (U * lam) @ U.T
        a = np.exp(rng.normal(0, 0.8, d))
        Wc, Q = commuting_state(U, a, n, rng)
        # block-commuting: dominant rows span R_D, bulk rows span R_B, R_D orthogonal to R_B,
        # but rows inside a block are NOT orthogonal
        Qn = rand_orth(n, rng)
        kb = min(d - k, n - k)
        Cb = np.zeros((d, n))
        Cb[D] = rng.standard_normal((k, k)) @ Qn[:k]
        Cb[B] = rng.standard_normal((d - k, kb)) @ Qn[k:k + kb]
        Wb = U @ Cb
        Wg = U @ (rng.standard_normal((d, n)) / np.sqrt(n))
        for S, sname in ((D, "D"), (B, "B")):
            PS = proj(U, S)
            for name in INDEXWISE:
                for W, wname in ((Wc, "commuting"), (Wb, "block_commuting"), (Wg, "generic")):
                    G = A @ W
                    FP = PS @ apply_filter(G, FILTERS[name])
                    PF = apply_filter(PS @ G, FILTERS[name])
                    upd(p1, "%s:%s:relF_diff" % (wname, name), np.linalg.norm(FP - PF) / np.linalg.norm(FP))
            for r in (k, 2 * k):
                G = A @ Wc
                FP = PS @ apply_filter(G, f_echelon(r))
                PF = apply_filter(PS @ G, f_echelon(r))
                upd(p1, "commuting:echelon(r=%s):relF_diff" % ("k" if r == k else "2k"), np.linalg.norm(FP - PF) / np.linalg.norm(FP))
res["checks"]["P1_coincidence_FP_vs_PF"] = p1

# ---------------------------------------------------------------- P2, P3, P4, P6
p2 = {}
p3 = {"window_tests": 0, "window_violations": 0, "Splus_tests": 0, "Splus_violations": 0}
p4 = {}
p6 = {}
for (d, n) in [(50, 60), (100, 100), (120, 200), (200, 240), (150, 70)]:
    for trial in range(4):
        k = int(rng.integers(3, d // 5))
        m = [1.5, 3.0, 10.0, 100.0][trial]
        lam = make_spectrum(d, k, m, rng)
        D, B = block_masks(d, k)
        U = rand_orth(d, rng)
        A = (U * lam) @ U.T
        a = np.exp(rng.normal(0, 0.8, d)) * np.where(D, 10 ** rng.uniform(-1, 1), 1.0)
        if d > n:
            mask = np.zeros(d, bool)
            mask[:min(k, 6)] = True
            mask[k + rng.choice(d - k, size=n - 10, replace=False)] = True
            a = a * mask
        W, Q = commuting_state(U, a, n, rng)
        G = A @ W
        L0 = lossW(U, lam, W)
        # generic state for P2/P4
        Wg = U @ ((np.exp(rng.normal(0, 0.5, d))[:, None]) * rng.standard_normal((d, n)) / np.sqrt(n))
        Gg = A @ Wg
        Lg = lossW(U, lam, Wg)
        filts = dict(FILTERS)
        filts["echelon_k"] = f_echelon(k)
        filts["echelon_2k"] = f_echelon(2 * k)
        for name, fvec in filts.items():
            co = commuting_coeffs(lam, a, D, fvec)
            F = apply_filter(G, fvec)
            Fg = apply_filter(Gg, fvec)
            eta_loss = {}
            for S, sname in ((D, "D"), (B, "B")):
                PS = proj(U, S)
                # ---- P2 on a generic state, both notions
                for Delta in (PS @ Fg, apply_filter(PS @ Gg, fvec)):
                    N, R = NR(U, lam, Wg, Delta)
                    for e in (0.3 * 2 * N / R, 2 * N / R, 2.5 * 2 * N / R):
                        dL = lossW(U, lam, Wg - e * Delta) - Lg
                        upd(p2, name + ":dL_identity_relerr", abs(dL - (-e * N + 0.5 * e ** 2 * R)) / Lg)
                    upd(p2, name + ":dL_at_threshold_rel", abs(lossW(U, lam, Wg - (2 * N / R) * Delta) - Lg) / Lg)
                # ---- P3 commuting formula (FP = PF for index-wise filters; FP for all filters)
                Delta = PS @ F
                N, R = NR(U, lam, W, Delta)
                eta_loss[sname] = 2 * co["N" + sname] / co["R" + sname]
                upd(p3, name + ":etaLoss_formula_relerr", rel(2 * N / R, eta_loss[sname]))
                for fac, sgn in ((0.95, -1), (1.05, 1)):
                    dL = lossW(U, lam, W - fac * eta_loss[sname] * Delta) - L0
                    p3["window_tests"] += 1
                    p3["window_violations"] += int(np.sign(dL) != sgn)
            # window: between the two thresholds exactly one projected update increases the loss
            lo, hi = sorted(eta_loss.values())
            if hi / lo > 1.02:
                e = np.sqrt(lo * hi)
                dLD = lossW(U, lam, W - e * proj(U, D) @ F) - L0
                dLB = lossW(U, lam, W - e * proj(U, B) @ F) - L0
                exp_D = 1 if eta_loss["D"] < eta_loss["B"] else -1
                p3["window_tests"] += 1
                p3["window_violations"] += int(not (np.sign(dLD) == exp_D and np.sign(dLB) == -exp_D))
            # sufficient condition (S+): min_D nu > max_B nu  =>  eta_D < eta_B, ratio >= min_D nu / max_B nu
            nu = co["nu"]
            sup = a > 0
            if nu[D & sup].min() > nu[B & sup].max():
                p3["Splus_tests"] += 1
                p3["Splus_violations"] += int(not (eta_loss["B"] / eta_loss["D"] >= nu[D & sup].min() / nu[B & sup].max() * (1 - 1e-12)))
            if nu[D & sup].max() < nu[B & sup].min():
                p3["Splus_tests"] += 1
                p3["Splus_violations"] += int(not (eta_loss["D"] / eta_loss["B"] >= nu[B & sup].min() / nu[D & sup].max() * (1 - 1e-12)))
            # ---- P4 additivity on a generic state (filter-then-project)
            for e in (0.1, 1.0):
                dfull = lossW(U, lam, Wg - e * Fg) - Lg
                dD = lossW(U, lam, Wg - e * proj(U, D) @ Fg) - Lg
                dB = lossW(U, lam, Wg - e * proj(U, B) @ Fg) - Lg
                upd(p4, name + ":additivity_relerr", abs(dfull - dD - dB) / Lg)
        # ---- P6 Echelon: FP uses the global tau, PF the block tau
        sig = lam * a
        for r in (max(1, k // 2), k, 2 * k):
            for S, sname in ((D, "D"), (B, "B")):
                PS = proj(U, S)
                tau_g = echelon_tau(sig, r)
                fg = np.where(sig > 0, np.minimum(sig, tau_g) / tau_g if tau_g > 0 else 1.0, 0.0)
                tau_s = echelon_tau(sig[S], r)
                fs_ = np.where(sig > 0, np.minimum(sig, tau_s) / tau_s if tau_s > 0 else 1.0, 0.0)
                for Delta, fv, tag in ((PS @ apply_filter(G, f_echelon(r)), fg, "FP"),
                                       (apply_filter(PS @ G, f_echelon(r)), fs_, "PF")):
                    N, R = NR(U, lam, W, Delta)
                    form = 2 * np.sum(sig[S] * fv[S]) / np.sum(lam[S] * fv[S] ** 2)
                    upd(p6, "echelon_%s_etaLoss_relerr" % tag, rel(2 * N / R, form))
res["checks"]["P2_loss_identity_generic"] = p2
res["checks"]["P3_commuting_thresholds"] = p3
res["checks"]["P4_additivity"] = p4
res["checks"]["P6_echelon_two_notions"] = p6

# ---------------------------------------------------------------- P5 two-level
p5 = {"rows": []}
for (d, k, m) in [(60, 6, 3.0), (100, 10, 10.0), (100, 10, 100.0)]:
    lam = make_spectrum(d, k, m, rng, kind="twolevel")
    D, B = block_masks(d, k)
    U = rand_orth(d, rng)
    A = (U * lam) @ U.T
    rho = k / (d - k)
    for p in (0.0, 0.125, 0.5, 1.0):
        fvec = f_muon() if p == 0 else (f_sgd() if p == 1 else f_ht(p))
        for th_target in (0.5, 0.9, 0.99, 0.999, 0.99999):
            ratio = np.sqrt(th_target / (1 - th_target) / (rho * m ** 2))   # a_D / a_B
            a = np.where(D, ratio, 1.0)
            W, Q = commuting_state(U, a, d + 5, rng)
            G = A @ W
            F = apply_filter(G, fvec)
            th = theta_of(lam, U.T @ W, D)
            et = {}
            for S, sname in ((D, "D"), (B, "B")):
                N, R = NR(U, lam, W, proj(U, S) @ F)
                et[sname] = 2 * N / R
            pred = m * (rho * (1 - th) / th) ** ((1 - p) / 2)
            pred2 = m ** p * (1 / ratio) ** (1 - p)
            p5["rows"].append(dict(d=d, k=k, m=m, p=p, theta=th, etaD=et["D"], etaB=et["B"],
                                   ratio_direct=et["B"] / et["D"], ratio_formula=pred,
                                   relerr=max(rel(et["B"] / et["D"], pred), rel(pred, pred2)),
                                   theta_flip=(rho * m ** (2 / (1 - p)) / (1 + rho * m ** (2 / (1 - p)))) if p < 1 else 1.0))
p5["max_relerr"] = max(r["relerr"] for r in p5["rows"])
# rows with theta == theta_flip exactly (ratio == 1) are ties, not ordering tests
p5["ties_theta_eq_theta_flip"] = sum(int(abs(r["ratio_direct"] - 1) <= 1e-9) for r in p5["rows"])
p5["ordering_violations"] = sum(int((r["ratio_direct"] > 1) != (r["theta"] < r["theta_flip"]))
                                for r in p5["rows"] if abs(r["ratio_direct"] - 1) > 1e-9)
res["checks"]["P5_two_level_window_ratio"] = p5

# ---------------------------------------------------------------- P7 model (M1)
p7 = {"tests": 0, "crit_violations": 0}
for d in (50, 100, 200):
    for trial in range(6):
        k = int(rng.integers(3, d // 5))
        m = [1.5, 3.0, 10.0][trial % 3]
        lam = make_spectrum(d, k, m, rng)
        D, B = block_masks(d, k)
        U = rand_orth(d, rng)
        A = (U * lam) @ U.T
        c = rng.standard_normal(d) * np.where(D, 10 ** rng.uniform(-1.5, 1.0), 1.0)
        x = (U @ c)[:, None]                      # d x 1 matrix parameter
        g = A @ x
        sig2 = lam ** 2 * c ** 2
        sS = {"D": sig2[D].sum(), "B": sig2[B].sum()}
        tauS = {"D": np.sum(lam[D] * sig2[D]), "B": np.sum(lam[B] * sig2[B])}
        s = sS["D"] + sS["B"]
        L0 = lossW(U, lam, x)
        for name, pdeg in (("sgd", 1.0), ("muon", 0.0), ("ht0.125", 0.125), ("ht0.5", 0.5)):
            fvec = FILTERS[name]
            gam = lambda t: fvec(np.array([t]))[0] / t
            F = apply_filter(g, fvec)
            upd(p7, name + ":F_is_radial_rescaling", np.abs(F - gam(np.sqrt(s)) * g).max() / np.abs(F).max())
            et_a, et_b = {}, {}
            for S, sname in ((D, "D"), (B, "B")):
                PS = proj(U, S)
                Nb, Rb = NR(U, lam, x, PS @ F)
                Na, Ra = NR(U, lam, x, apply_filter(PS @ g, fvec))
                et_b[sname] = 2 * Nb / Rb
                et_a[sname] = 2 * Na / Ra
                upd(p7, name + ":FP_threshold_relerr", rel(et_b[sname], 2 * sS[sname] / (tauS[sname] * gam(np.sqrt(s)))))
                upd(p7, name + ":PF_threshold_relerr", rel(et_a[sname], 2 * sS[sname] / (tauS[sname] * gam(np.sqrt(sS[sname])))))
            muD, muB = tauS["D"] / sS["D"], tauS["B"] / sS["B"]
            # FP: ratio is SGD's, mu^D/mu^B >= m, for every filter
            upd(p7, name + ":FP_ratio_relerr", rel(et_b["B"] / et_b["D"], muD / muB))
            p7["tests"] += 1
            p7["crit_violations"] += int(not (et_b["B"] / et_b["D"] >= m * (1 - 1e-12)))
            # PF: eta_D < eta_B  <=>  theta < M^(2/(1-p)) / (1 + M^(2/(1-p))),  M = mu^D / mu^B
            if pdeg < 1:
                Mr = muD / muB
                th_crit = Mr ** (2 / (1 - pdeg)) / (1 + Mr ** (2 / (1 - pdeg)))
                th = sS["D"] / s
                p7["tests"] += 1
                p7["crit_violations"] += int((et_a["D"] < et_a["B"]) != (th < th_crit))
res["checks"]["P7_model_M1"] = p7

res["runtime_sec"] = time.time() - t0
jdump(res, os.path.join(OUT, "projected.json"))
print("P1", {k: "%.1e" % v for k, v in sorted(p1.items())})
print("P2", {k: "%.1e" % v for k, v in sorted(p2.items())})
print("P3", {k: ("%.1e" % v if isinstance(v, float) else v) for k, v in sorted(p3.items())})
print("P4", {k: "%.1e" % v for k, v in sorted(p4.items())})
print("P6", {k: "%.1e" % v for k, v in sorted(p6.items())})
print("P5 max_relerr %.2e ordering_violations %d ties %d" % (p5["max_relerr"], p5["ordering_violations"], p5["ties_theta_eq_theta_flip"]))
for r in p5["rows"]:
    if r["m"] == 10.0:
        print("   m=%g p=%.3f theta=%.5f etaD=%.4g etaB=%.4g ratio=%.4g theta_flip=%.6f" % (r["m"], r["p"], r["theta"], r["etaD"], r["etaB"], r["ratio_direct"], r["theta_flip"]))
print("P7", {k: ("%.1e" % v if isinstance(v, float) else v) for k, v in sorted(p7.items())})
print("runtime %.1fs" % res["runtime_sec"])
