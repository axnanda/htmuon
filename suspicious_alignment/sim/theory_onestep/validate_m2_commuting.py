"""Noise-free validation of the commuting-case theory in model (M2)  (Sections 3-4 of the note).

Every check compares a closed formula in eigen-coordinates with a DIRECT matrix computation
(numpy SVD of the actual d x n gradient).  Output: results/m2_commuting.json
"""
import os
import sys
import time
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import (FILTERS, HOMOG_DEG, f_echelon, f_muon, f_ht, f_sgd, f_ns5, apply_filter,
                    echelon_headtail, ns5_matrix, rand_orth, make_spectrum, block_masks,
                    commuting_state, energies, theta_of, loss_of, commuting_coeffs,
                    commuting_step, echelon_tau, jdump)

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
os.makedirs(OUT, exist_ok=True)
rng = np.random.default_rng(20261118)
res = {"seed": 20261118, "checks": {}}
t0 = time.time()


def upd(dic, key, val):
    dic[key] = max(dic.get(key, 0.0), float(val))


def rel(x, y):
    return abs(x - y) / max(abs(x), abs(y), 1e-300)


# ----------------------------------------------------------------------------------------------
# C1  Echelon(r) literal head-tail construction == spectral filter min(sigma,tau)/tau ; NS5 port
# ----------------------------------------------------------------------------------------------
c1 = {}
for (d, n) in [(40, 60), (60, 40), (80, 80), (120, 150)]:
    G = rng.standard_normal((d, n)) @ np.diag(rng.uniform(0.2, 3.0, n)) / np.sqrt(n)
    for r in [0, 1, 5, 17, min(d, n) - 1, min(d, n)]:
        O1 = echelon_headtail(G, r)
        O2 = apply_filter(G, f_echelon(r))
        upd(c1, "echelon_headtail_vs_filter_maxabs", np.abs(O1 - O2).max())
    # r = 0 is G / ||G||_2 ; r = rank is Muon
    upd(c1, "echelon_r0_vs_spectral_normalised", np.abs(echelon_headtail(G, 0) - G / np.linalg.norm(G, 2)).max())
    upd(c1, "echelon_rfull_vs_muon", np.abs(echelon_headtail(G, min(d, n)) - apply_filter(G, f_muon())).max())
    upd(c1, "ns5_matrix_vs_filter_maxabs", np.abs(ns5_matrix(G) - apply_filter(G, f_ns5())).max())
res["checks"]["C1_filters"] = c1

# ----------------------------------------------------------------------------------------------
# C2-C5  random commuting states: per-mode dynamics, quadratic form, root, loss, scaling law
# ----------------------------------------------------------------------------------------------
configs = [(50, 50), (50, 80), (100, 130), (100, 200), (200, 220), (120, 60), (200, 90)]
gaps = [1.5, 3.0, 10.0, 100.0]
c2 = {}
per_filter = {}
ntrial = 0
sign_cases = {}
for (d, n) in configs:
    for trial in range(4):
        k = int(rng.integers(3, max(4, d // 5)))
        m = gaps[(trial + d) % len(gaps)]
        lam = make_spectrum(d, k, m, rng)
        D, B = block_masks(d, k)
        U = rand_orth(d, rng)
        # random non-degenerate row norms, log-normal, independent scales on D and B
        a = np.exp(rng.normal(0, 0.8, d)) * np.where(D, 10 ** rng.uniform(-1, 1), 10 ** rng.uniform(-1, 1))
        if d > n:  # rank-deficient commuting state: support of size <= n meeting both blocks
            supp = np.concatenate([rng.choice(k, size=min(k, max(2, n // 6)), replace=False),
                                   k + rng.choice(d - k, size=n - min(k, max(2, n // 6)) - 3, replace=False)])
            mask = np.zeros(d, bool)
            mask[supp] = True
            a = a * mask
        W, Q = commuting_state(U, a, n, rng)
        C = U.T @ W
        G = (U * lam) @ C
        sD, sB = energies(lam, C, D)
        th = sD / (sD + sB)
        L0 = loss_of(lam, C)
        filts = dict(FILTERS)
        for r in (0, k, 3 * k):
            filts["echelon%d" % r if r in (0,) else ("echelon_k" if r == k else "echelon_3k")] = f_echelon(r)
        for name, fvec in filts.items():
            pf = per_filter.setdefault(name, {})
            co = commuting_coeffs(lam, a, D, fvec)
            Fd = apply_filter(G, fvec)
            # the filtered gradient is U diag(f(sigma_i)) Q
            upd(pf, "filtered_gradient_maxabs", np.abs(U.T @ Fd - co["f"][:, None] * Q).max() / max(co["f"].max(), 1e-300))
            eta_scale = np.sum(a * co["f"]) / max(np.sum(co["f"] ** 2), 1e-300)
            etas = [0.03 * eta_scale, 0.3 * eta_scale, 1.0 * eta_scale, 3.0 * eta_scale]
            pos_root = co["p"] != 0 and (-co["q"] / co["p"]) > 0
            if pos_root:
                es = -co["q"] / co["p"]
                etas += [0.9 * es, 1.1 * es]
            for eta in etas:
                Cn = U.T @ (W - eta * Fd)
                pred = commuting_step(lam, a, D, fvec, eta)
                rn = np.linalg.norm(Cn, axis=1)
                upd(pf, "rownorm_relerr", np.abs(rn - pred["a_new"]).max() / max(a.max(), 1e-300))
                # rows stay mutually orthogonal (commuting structure preserved)
                Gram = Cn @ Cn.T
                off = Gram - np.diag(np.diag(Gram))
                upd(pf, "offdiag_gram_rel", np.abs(off).max() / max(np.diag(Gram).max(), 1e-300))
                sDn, sBn = energies(lam, Cn, D)
                upd(pf, "sD_next_relerr", rel(sDn, pred["sD"]))
                upd(pf, "sB_next_relerr", rel(sBn, pred["sB"]))
                dth = sDn / (sDn + sBn) - th
                upd(pf, "dtheta_abserr", abs(dth - pred["dtheta"]))
                if abs(dth) > 1e-9:
                    upd(pf, "dtheta_relerr", rel(dth, pred["dtheta"]))
                dL = loss_of(lam, Cn) - L0
                upd(pf, "dL_relerr", abs(dL - pred["dL"]) / max(abs(L0), 1e-300))
                # comparison functional  s^B s+^D - s+^B s^D = p eta^2 + q eta
                fc = sB * sDn - sBn * sD
                upd(pf, "fcompare_relerr", abs(fc - (co["p"] * eta ** 2 + co["q"] * eta)) / (sD * sB + 1e-300) / max(1.0, eta ** 2 * (co["uD"] / sD + co["uB"] / sB), eta * (co["tauD"] / sD + co["tauB"] / sB)))
            if pos_root:
                es = -co["q"] / co["p"]
                Cn = U.T @ (W - es * Fd)
                sDn, sBn = energies(lam, Cn, D)
                upd(pf, "dtheta_at_etastar_abs", abs(sDn / (sDn + sBn) - th))
                # sign pattern around the root: sign(dtheta) = sign(p) * sign(eta - eta*)
                for fac in (0.9, 1.1):
                    Cn = U.T @ (W - fac * es * Fd)
                    sDn, sBn = energies(lam, Cn, D)
                    ok = np.sign(sDn / (sDn + sBn) - th) == np.sign(co["p"]) * np.sign(fac - 1)
                    pf["sign_pattern_violations"] = pf.get("sign_pattern_violations", 0) + int(not ok)
                    pf["sign_pattern_tests"] = pf.get("sign_pattern_tests", 0) + 1
            case = ("q<0" if co["q"] < 0 else "q>0") + "," + ("p>0" if co["p"] > 0 else "p<0")
            sc = sign_cases.setdefault(name, {})
            sc[case] = sc.get(case, 0) + 1
            # scaling law eta*(tC) = t^(1-p) eta*(C)
            deg = HOMOG_DEG.get(name, 0.0 if name.startswith("echelon") else None)
            if deg is not None and pos_root:
                t = 3.7
                co2 = commuting_coeffs(lam, t * a, D, fvec)
                upd(pf, "scaling_law_relerr", rel(-co2["q"] / co2["p"], t ** (1 - deg) * es))
        ntrial += 1
res["checks"]["C2_C5_random_commuting_states"] = {"n_states": ntrial, "configs_d_n": configs,
                                                 "per_filter_max_discrepancy": per_filter,
                                                 "sign_cases_counts": sign_cases}

# ----------------------------------------------------------------------------------------------
# C6  bounds on eta* under effective separation (S+) and inversion (S-)
# ----------------------------------------------------------------------------------------------
c6 = {"tests": 0, "violations": 0, "min_slack_lower": np.inf, "min_slack_upper": np.inf}
for trial in range(60):
    d, n = (60, 80) if trial % 2 == 0 else (120, 120)
    k = int(rng.integers(3, d // 4))
    m = gaps[trial % 4]
    lam = make_spectrum(d, k, m, rng)
    D, B = block_masks(d, k)
    U = rand_orth(d, rng)
    name = ["muon", "ht0.125", "ht0.5", "sgd", "echelon_k", "ns5"][trial % 6]
    fvec = f_echelon(k) if name == "echelon_k" else FILTERS[name]
    want_plus = (trial // 6) % 2 == 0
    # rejection-free construction: start from random a and rescale the dominant block until the
    # effective curvatures nu_i = f(sigma_i)/a_i are separated in the wanted direction
    a = np.exp(rng.normal(0, 0.3, d))
    ok = False
    for it in range(80):
        co = commuting_coeffs(lam, a, D, fvec)
        nu = co["nu"]
        if want_plus and nu[D].min() > nu[B].max():
            ok = True
            break
        if (not want_plus) and nu[D].max() < nu[B].min():
            ok = True
            break
        a = a * np.where(D, 0.7 if want_plus else 1.4, 1.0)
    if not ok:
        continue
    W, Q = commuting_state(U, a, n, rng)
    es = -co["q"] / co["p"]
    lo = 2.0 / (nu[D].max() + nu[B].max())
    hi = 2.0 / (nu[D].min() + nu[B].min())
    signs_ok = (co["q"] < 0 < co["p"]) if want_plus else (co["p"] < 0 < co["q"])
    c6["tests"] += 1
    c6["violations"] += int(not (signs_ok and lo <= es * (1 + 1e-12) and es <= hi * (1 + 1e-12)))
    c6["min_slack_lower"] = min(c6["min_slack_lower"], es / lo - 1)
    c6["min_slack_upper"] = min(c6["min_slack_upper"], hi / es - 1)
    # direct confirmation of the dichotomy (or reversed dichotomy) on the actual matrix
    G = (U * lam) @ (U.T @ W)
    Fd = apply_filter(G, fvec)
    th = theta_of(lam, U.T @ W, D)
    for fac in (0.5, 0.95, 1.05, 2.0):
        dth = theta_of(lam, U.T @ (W - fac * es * Fd), D) - th
        expect = np.sign(fac - 1) * (1 if want_plus else -1)
        c6["violations"] += int(np.sign(dth) != expect)
        c6["tests"] += 1
res["checks"]["C6_etastar_bounds_and_dichotomy"] = c6

# ----------------------------------------------------------------------------------------------
# C7  two-level states: theta_flip(p) = rho m^{2/(1-p)} / (1 + rho m^{2/(1-p)}), eta* = 2/(nu_D+nu_B)
# ----------------------------------------------------------------------------------------------
c7 = {"rows": []}
for (d, k, m) in [(60, 6, 3.0), (100, 10, 10.0), (100, 25, 2.0)]:
    lam = make_spectrum(d, k, m, rng, kind="twolevel")
    D, B = block_masks(d, k)
    U = rand_orth(d, rng)
    rho = k / (d - k)
    for p in (0.0, 0.125, 0.25, 0.5):
        fvec = f_muon() if p == 0.0 else f_ht(p)
        x = rho * m ** (2.0 / (1.0 - p))
        th_flip = x / (1 + x)
        row = dict(d=d, k=k, m=m, p=p, theta_flip=th_flip, one_minus_theta_flip=1 / (1 + x))
        worst_inv = 0.0
        worst_root = 0.0
        viol = 0
        for odds_fac in [0.05, 0.5, 1.0, 2.0, 20.0]:
            th_target = th_flip if odds_fac == 1.0 else x * odds_fac / (1 + x * odds_fac)
            # theta/(1-theta) = rho m^2 (aD/aB)^2
            ratio = np.sqrt(th_target / (1 - th_target) / (rho * m ** 2))
            a = np.where(D, ratio, 1.0) * 0.8
            W, Q = commuting_state(U, a, d + 10, rng)
            C = U.T @ W
            G = (U * lam) @ C
            th = theta_of(lam, C, D)
            co = commuting_coeffs(lam, a, D, fvec)
            Fd = apply_filter(G, fvec)
            if th_target == th_flip:
                for eta in (0.01, 0.1, 0.37):
                    worst_inv = max(worst_inv, abs(theta_of(lam, U.T @ (W - eta * Fd), D) - th))
            else:
                es = -co["q"] / co["p"]
                nuD, nuB = co["nu"][0], co["nu"][-1]
                worst_root = max(worst_root, rel(es, 2 / (nuD + nuB)))
                below = th_target < th_flip
                viol += int(not ((co["q"] < 0 < co["p"]) if below else (co["p"] < 0 < co["q"])))
                for fac in (0.5, 1.5):
                    dth = theta_of(lam, U.T @ (W - fac * es * Fd), D) - th
                    viol += int(np.sign(dth) != np.sign(fac - 1) * (1 if below else -1))
        row.update(max_abs_dtheta_at_theta_flip=worst_inv, etastar_vs_2_over_nuD_plus_nuB_relerr=worst_root,
                   sign_violations=viol)
        c7["rows"].append(row)
res["checks"]["C7_two_level_theta_flip"] = c7

# ----------------------------------------------------------------------------------------------
# C8  all four sign patterns of (q, p) occur under Muon (explicit small examples, direct SVD)
# ----------------------------------------------------------------------------------------------
c8 = {}
lam = np.array([5.0, 1.0, 1.0])
D = np.array([True, False, False])
U = rand_orth(3, rng)
examples = {
    "q<0,p>0 (Deng-like)": np.array([0.5, 1.0, 1.0]),
    "q>0,p<0 (reversed)": np.array([2.0, 1.0, 1.0]),
    "q<0,p<0 (decrease for all eta)": np.array([0.8, 0.05, 1.0]),
    "q>0,p>0 (increase for all eta)": None,
}
# case 4 needs a heterogeneous dominant block: two dominant modes, one bulk mode
lam4 = np.array([5.0, 5.0, 1.0])
D4 = np.array([True, True, False])
a4 = np.array([0.05, 1.0, 0.8])
for key, a in examples.items():
    if a is None:
        lam_, D_, a_ = lam4, D4, a4
    else:
        lam_, D_, a_ = lam, D, a
    co = commuting_coeffs(lam_, a_, D_, f_muon())
    W, Q = commuting_state(U, a_, 5, rng)
    G = (U * lam_) @ (U.T @ W)
    Fd = apply_filter(G, f_muon())
    th = theta_of(lam_, U.T @ W, D_)
    etas = np.concatenate([np.geomspace(1e-3, 20, 400)])
    dths = np.array([theta_of(lam_, U.T @ (W - e * Fd), D_) - th for e in etas])
    c8[key] = dict(a=a_, lam=lam_, q=co["q"], p=co["p"], frac_eta_with_decrease=float(np.mean(dths < 0)),
                   frac_eta_with_increase=float(np.mean(dths > 0)))
res["checks"]["C8_four_sign_cases_muon"] = c8

res["runtime_sec"] = time.time() - t0
jdump(res, os.path.join(OUT, "m2_commuting.json"))

# compact console summary
print("C1", {k: "%.2e" % v for k, v in c1.items()})
for name, pf in per_filter.items():
    print("%-11s" % name, {k: ("%.1e" % v if isinstance(v, float) else v) for k, v in pf.items()})
print("sign cases", sign_cases)
print("C6", c6)
for row in c7["rows"]:
    print("C7", row)
for kk, vv in c8.items():
    print("C8", kk, {a: (np.round(b, 4).tolist() if isinstance(b, np.ndarray) else round(float(b), 5)) for a, b in vv.items()})
print("runtime %.1fs" % res["runtime_sec"])
