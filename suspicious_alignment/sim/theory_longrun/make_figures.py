"""Figures for notes/research/theory_longrun.md (reads results/*.json only; no simulation here)."""
import json
import os

import numpy as np

from common import FIGS, RES, deng_theta_inf, mf_energy, mf_energy_echelon, ratio_pred, spectrum
from plotstyle import AQUA, BLUE, BLUE_RAMP, INK, INK2, MUTED, ORANGE, mk, setup

plt = setup()


def load(name):
    path = os.path.join(RES, name)
    return json.load(open(path)) if os.path.exists(path) else None


def save(fig, name):
    fig.savefig(os.path.join(FIGS, name))
    plt.close(fig)
    print("wrote", name)


def legend_below(a, ncol=2, y=-0.2):
    a.legend(loc="upper center", bbox_to_anchor=(0.5, y), ncol=ncol, handlelength=3.0, columnspacing=1.2)


def one_minus_ratio(lam, k, q):
    w = (lam / lam.max()) ** q
    return w[k:].sum() / w.sum()


# ------------------------------------------------------------------ fig 1: SGD baseline (Deng's setup)
d1 = load("exp1b_deng_setup_sgd.json")
if d1:
    fig, ax = plt.subplots(1, 2, figsize=(10.2, 3.9))
    for j, m in enumerate(["5", "20", "50", "200"]):
        c = d1["sgd_curves"][m]
        t = np.array(c["t"]) + 1
        ax[0].plot(t, c["theta_mean"], color=BLUE_RAMP[j + 1], label=f"m = {m} (mean of 7 seeds)")
        ax[0].plot(t, c["theta_det"], color=INK, lw=0.9, ls=(0, (4, 2)),
                   label="deterministic equivalent" if j == 0 else None)
    ax[0].set_xscale("log")
    ax[0].set_xlabel("step t + 1")
    ax[0].set_ylabel("alignment theta_t")
    ax[0].set_title("SGD, authors' setup: decrease, then rise to theta_inf")
    legend_below(ax[0], 2)
    rows = d1["sgd"]
    ms = np.array([r["m"] for r in rows])
    ax[1].plot(ms, [1 - r["pred_thm16"] for r in rows], color=INK, label="Theorem 16")
    ax[1].plot(ms, [1 - r["pred_small_eta"] for r in rows], color=MUTED, ls=":", label="sum_D lam / sum lam (small eta)")
    ax[1].errorbar(ms, [1 - r["meas_ratio"][0] for r in rows], yerr=[r["meas_ratio"][1] for r in rows],
                   **mk(INK, "o"), ms=9, capsize=2, label="measured: ratio of time-averaged energies")
    ax[1].errorbar(ms, [1 - r["meas_authors_stat"][0] for r in rows], yerr=[r["meas_authors_stat"][1] for r in rows],
                   **mk(BLUE, "s"), ms=5, capsize=2, label="measured: time average of theta_t (authors' statistic)")
    ax[1].set_xscale("log")
    ax[1].set_yscale("log")
    ax[1].set_xlabel("gap m = lam_k / lam_{k+1}")
    ax[1].set_ylabel("1 - theta_inf")
    ax[1].set_title("Theorem 16 versus simulation")
    legend_below(ax[1], 1)
    save(fig, "fig1_sgd_baseline.png")

# ------------------------------------------------------------------ fig 2: noise-free curves, m = 100
d2, d2b, d3, d2c = load("exp2_commuting.json"), load("exp2b_momentum_scalar.json"), load("exp3_m1_vector.json"), load("exp2c_muon_dip.json")
if d2 and d2b and d3 and d2c:
    fig, ax = plt.subplots(1, 3, figsize=(13.2, 3.9), sharey=True)
    a = ax[0]
    a.plot(d2c["curves"]["muon_equal_m100"]["theta_mean"], color=BLUE, ls=(0, (1, 1.5)), label="Muon, equal initial row norms")
    a.plot(d2["muon_curve_m100"]["theta_mean"], color=BLUE, label="Muon, initial norms with 7% spread")
    a.plot(d2["ht0.125_curve_m100"]["theta_mean"], color=ORANGE, label="HTMuon p = 0.125")
    a.plot(d2["ht0.5_curve_m100"]["theta_mean"], color=ORANGE, ls=":", label="HTMuon p = 0.5")
    e = d2["ech10_curve_m100"]
    a.plot(e["t"], e["theta_mean"], color=AQUA, ls="-.", label="Echelon r = 10 (< k)")
    e = d2["ech100_curve_m100"]
    a.plot(e["t"], e["theta_mean"], color=AQUA, ls="--", label="Echelon r = 100 (> k)")
    a.set_xlim(0, 3000)
    a.set_title("(M2) commuting, no momentum")
    a.set_ylabel("alignment theta_t (mean of 8 seeds)")
    a = ax[1]
    for p, col, lab in [("0.0", BLUE, "Muon"), ("0.125", ORANGE, "HTMuon p = 0.125")]:
        c = d2b[f"mom_p{p}_curve_m100"]
        a.plot(c["t"], c["theta_mean"], color=col, label=lab + ", beta = 0.95 (Nesterov)")
    a.set_xlim(0, 3000)
    a.set_title("(M2) commuting, momentum 0.95")
    a = ax[2]
    for p, col, ls, lab in [("0.0", BLUE, "-", "p = 0 (normalised GD)"), ("0.125", ORANGE, "-", "p = 0.125"),
                            ("0.5", ORANGE, ":", "p = 0.5")]:
        c = d3[f"m1_nf_p{p}_curve_m100"]
        a.plot(c["t"], c["theta_mean"], color=col, ls=ls, label=lab)
    a.set_xlim(0, 4000)
    a.set_title("(M1) vector model")
    for a in ax:
        a.set_xlabel("step t")
        legend_below(a, 1 if a is ax[1] else 2, y=-0.17)
    fig.suptitle("Noise-free filtered dynamics, d = 500, k = 50, m = 100, eta = 0.01", y=1.02, fontsize=11)
    save(fig, "fig2_noise_free_curves.png")

# ------------------------------------------------------------------ fig 3: 1 - theta_inf versus m (noise-free)
d1o = load("exp1_sgd_baseline.json")
if d2 and d1o:
    fig, ax = plt.subplots(1, 2, figsize=(10.6, 4.2))
    a = ax[0]
    mgrid = np.geomspace(2, 500, 60)
    D_, K_ = 500, 50
    # SGD (Deng, with noise), from exp1 (same block structure, dom_spread 1.2)
    rows = d1o["rows"]
    a.plot([r["m"] for r in rows], [1 - r["pred_thm16"] for r in rows], color=INK)
    a.errorbar([r["m"] for r in rows], [1 - r["meas_ratio_of_avgs"][0] for r in rows], **mk(INK, "o"),
               label="SGD with noise (Thm 16): ~ m^-1")
    a.plot(mgrid, [one_minus_ratio(spectrum(D_, K_, m), K_, 2) for m in mgrid], color=BLUE)
    a.errorbar([r["m"] for r in d2["muon"]], [1 - r["meas_ratio"][0] for r in d2["muon"]], **mk(BLUE, "s"),
               label="Muon: psi_B/psi ~ m^-2")
    for p, mkr, ls in [(0.125, "^", "-"), (0.25, "v", "--"), (0.5, "D", ":")]:
        q = 2 / (1 - p)
        a.plot(mgrid, [one_minus_ratio(spectrum(D_, K_, m), K_, q) for m in mgrid], color=ORANGE, ls=ls)
        rr = [r for r in d2["ht"] if r["p"] == p and r["one_minus_meas"] > 1e-13]
        a.errorbar([r["m"] for r in rr], [r["one_minus_meas"] for r in rr], **mk(ORANGE, mkr),
                   label=f"HTMuon p = {p}: ~ m^-{q:.2f}")
    a.set_xscale("log")
    a.set_yscale("log")
    a.set_ylim(1e-13, 2)
    a.set_xlabel("gap m")
    a.set_ylabel("1 - theta_inf")
    a.set_title("lines: predicted, markers: measured")
    legend_below(a, 2, y=-0.15)
    a = ax[1]
    a.plot(mgrid, [one_minus_ratio(spectrum(D_, K_, m), K_, 2) for m in mgrid], color=BLUE, label="Muon (all d directions on the floor)")
    for r_, mkr, ls in [(50, "h", "-"), (100, "X", "--"), (250, "P", ":")]:
        def pred(m):
            w2 = spectrum(D_, K_, m) ** 2
            return w2[K_:r_ + 1].sum() / w2[:r_ + 1].sum()
        a.plot(mgrid, [pred(m) for m in mgrid], color=AQUA, ls=ls)
        rr = [r for r in d2["ech"] if r["r"] == r_]
        a.errorbar([r["m"] for r in rr], [max(1 - r["meas"][0], 1e-16) for r in rr], **mk(AQUA, mkr),
                   label=f"Echelon r = {r_}: top-(r+1) heuristic")
    a.set_xscale("log")
    a.set_yscale("log")
    a.set_xlabel("gap m")
    a.set_ylabel("1 - theta_inf")
    a.set_title("Echelon(r >= k); for r < k: theta_inf = 1")
    legend_below(a, 1, y=-0.15)
    fig.suptitle("Long-run alignment in the noise-free commuting model (d = 500, k = 50, 8 seeds)", y=1.0, fontsize=11)
    save(fig, "fig3_theta_inf_vs_m.png")

# ------------------------------------------------------------------ fig 4: (M1) with noise
if d3:
    fig, ax = plt.subplots(1, 2, figsize=(10.2, 3.9))
    for p, col, mkr in [(0.0, BLUE, "s"), (0.125, ORANGE, "^")]:
        for m, ls in [(10, "-"), (100, "--")]:
            rr = [r for r in d3["noisy"] if r["p"] == p and r["m"] == m]
            x = [r["noise_rel"] for r in rr]
            ax[0].plot(x, [1 - r["pred_selfconsistent"] for r in rr], color=col, ls=ls)
            ax[0].errorbar(x, [1 - r["meas_ratio"][0] for r in rr], **mk(col, mkr),
                           label=f"p = {p}, m = {m}")
            ax[0].axhline(1 - rr[0]["deng_small_eta"], color=MUTED, lw=0.9, ls=":")
            ax[1].plot(x, [r["pred_etaeff_lam1"] for r in rr], color=col, ls=ls)
            ax[1].errorbar(x, [r["meas_etaeff_lam1"][0] for r in rr], **mk(col, mkr), label=f"p = {p}, m = {m}")
    for a in ax:
        a.set_xscale("log")
        a.set_xlabel("noise level  nu / g*   (nu = sigma sqrt(d), g* = (eta lam_1/2)^(1/(1-p)))")
    ax[0].set_yscale("log")
    ax[0].set_ylabel("1 - theta_inf")
    ax[0].set_title("lines: self-consistent prediction; dotted: Deng small-step value")
    legend_below(ax[0], 2)
    ax[1].axhline(2.0, color=INK2, lw=0.9, ls=":")
    ax[1].set_ylabel("mean effective step  eta_eff * lam_1")
    ax[1].set_title("effective step saturates at the edge of stability (2)")
    legend_below(ax[1], 2)
    save(fig, "fig4_m1_noise.png")

# ------------------------------------------------------------------ fig 5: (M2) with noise
d4a, d4b = load("exp4_m2_noise_A.json"), load("exp4_m2_noise_B.json")
if d4a and d4b:
    fig, ax = plt.subplots(1, 2, figsize=(10.6, 4.1))
    D_, K_, N_, ETA_ = 24, 4, 600, 0.01
    lam = spectrum(D_, K_, 10)
    chis = np.geomspace(0.01, 10, 50)
    a = ax[0]
    sty = {"muon": (BLUE, "s", "-", "Muon"), "ht0.125": (ORANGE, "^", "-", "HTMuon p = 0.125"),
           "ech2": (AQUA, "P", ":", "Echelon r = 2 (< k)"), "ech4": (AQUA, "h", "-", "Echelon r = 4 (= k)")}
    for name, (col, mkr, ls, lab) in sty.items():
        pr = []
        for chi in chis:
            nu = ETA_ * lam[K_] / chi
            E = (mf_energy(lam, ETA_, nu, 0.0 if name == "muon" else 0.125) if not name.startswith("ech")
                 else mf_energy_echelon(lam, ETA_, nu, int(name[3:])))
            pr.append(E[K_:].sum() / E.sum())
        a.plot(chis, pr, color=col, ls=ls)
        rr = [r for r in d4a["rows"] if r["m"] == 10 and r["opt"] == name]
        a.errorbar([r["chi_B"] for r in rr], [1 - r["meas_ratio"][0] for r in rr], **mk(col, mkr), label=lab)
    a.axhline(1 - lam[:K_].sum() / lam.sum(), color=MUTED, lw=0.9, ls=":")
    a.text(0.011, (1 - lam[:K_].sum() / lam.sum()) * 1.08, "Deng: sum_B lam / sum lam", color=INK2, fontsize=8)
    a.axhline(1 - ratio_pred(lam, K_, 2), color=MUTED, lw=0.9, ls=":")
    a.text(0.011, (1 - ratio_pred(lam, K_, 2)) * 1.08, "psi_B / psi", color=INK2, fontsize=8)
    a.set_xscale("log")
    a.set_yscale("log")
    a.set_xlabel("chi_B = eta lam_{k+1} / nu   (step over noise, bulk)")
    a.set_ylabel("1 - theta_inf")
    a.set_title("m = 10: noise sweep (lines: mean field)")
    legend_below(a, 2, y=-0.17)
    a = ax[1]
    sty = {"sgd": (INK, "o", "-", "SGD, eta = 1/lam_1 (Thm 16)"), "muon": (BLUE, "s", "-", "Muon"),
           "ht0.125": (ORANGE, "^", "-", "HTMuon p = 0.125"), "ht0.5": (ORANGE, "D", ":", "HTMuon p = 0.5"),
           "ech4": (AQUA, "h", "-", "Echelon r = 4 (= k)")}
    for name, (col, mkr, ls, lab) in sty.items():
        rr = [r for r in d4b["rows"] if r["opt"] == name]
        key = "pred_mf_edge" if name.startswith("ech") else "pred_mf"
        a.plot([r["m"] for r in rr], [1 - r[key] for r in rr], color=col, ls=ls)
        a.errorbar([r["m"] for r in rr], [1 - r["meas_ratio"][0] for r in rr], **mk(col, mkr), label=lab)
    a.set_xscale("log")
    a.set_yscale("log")
    a.set_xlabel("gap m")
    a.set_ylabel("1 - theta_inf")
    a.set_title("chi_B = 0.1: gap sweep (lines: mean field / Thm 16)")
    legend_below(a, 2, y=-0.17)
    fig.suptitle("(M2) with isotropic gradient noise, d = 24, k = 4, n = 600, 3 seeds", y=1.0, fontsize=11)
    save(fig, "fig5_m2_noise.png")

# ------------------------------------------------------------------ fig 6: generic initialisation
d5a, d5b = load("exp5_generic_init_A.json"), load("exp5_generic_init_B.json")
if d5a and d5b:
    fig, ax = plt.subplots(1, 3, figsize=(13.4, 3.9))
    a = ax[0]
    for key, ls, lab in [("n1d_m10", "-", "n = d, m = 10"), ("n4d_m10", "--", "n = 4d, m = 10"),
                         ("n1d_m100", ":", "n = d, m = 100"), ("n4d_m100", "-.", "n = 4d, m = 100")]:
        a.plot(d5a["curves"][key]["theta"][:400], color=BLUE, ls=ls, label=lab)
    a.set_xlabel("step t")
    a.set_ylabel("alignment theta_t (one seed)")
    a.set_title("Muon, generic Gaussian init (d = 60, k = 6)")
    legend_below(a, 2, y=-0.17)
    a = ax[1]
    for key, ls, lab in [("p0.125_m10", "-", "p = 0.125, m = 10"), ("p0.125_m100", "--", "p = 0.125, m = 100"),
                         ("p0.5_m10", ":", "p = 0.5, m = 10"), ("p0.5_m100", "-.", "p = 0.5, m = 100")]:
        a.plot(d5b["curves"][key]["theta"][:600], color=ORANGE, ls=ls, label=lab)
    a.set_xlabel("step t")
    a.set_title("HTMuon, generic Gaussian init (d = 40, k = 4, n = 160)")
    legend_below(a, 2, y=-0.17)
    a = ax[2]
    for nm, mkr, lab in [(1, "s", "measured, n = d"), (4, "D", "measured, n = 4d")]:
        rr = [r for r in d5a["rows"] if r["n_over_d"] == nm]
        a.errorbar([r["m"] for r in rr], [1 - r["thetabar"][0] for r in rr], yerr=[r["thetabar"][1] for r in rr],
                   **mk(BLUE, mkr), capsize=2, label=lab)
    rr = [r for r in d5a["rows"] if r["n_over_d"] == 1]
    ms = [r["m"] for r in rr]
    a.plot(ms, [1 - r["psi_ratio"] for r in rr], color=BLUE, label="psi_B/psi (commuting, uniform phases)")
    a.plot(ms, [1 - r["lower_bound"] for r in rr], color=INK2, ls="--", lw=1.2, label="rigorous bounds (Theorem 6)")
    a.plot(ms, [1 - r["upper_bound"] for r in rr], color=INK2, ls="--", lw=1.2)
    a.set_xscale("log")
    a.set_yscale("log")
    a.set_xlabel("gap m")
    a.set_ylabel("1 - theta_inf (two-step average)")
    a.set_title("Muon limit cycle: generic init vs bounds")
    legend_below(a, 1, y=-0.17)
    save(fig, "fig6_generic_init.png")

# ------------------------------------------------------------------ fig 7: (M1) filters in the authors' setup
d7 = load("exp1b_deng_setup_m1.json")
if d1 and d7:
    fig, ax = plt.subplots(1, 2, figsize=(10.6, 4.0))
    a = ax[0]
    c = d1["sgd_curves"]["50"]
    a.plot(np.array(c["t"]) + 1, c["theta_mean"], color=INK, label="SGD, eta = 0.003")
    for p, col, ls, lab in [("0.0", BLUE, "-", "p = 0 (Muon / normalised SGD)"), ("0.125", ORANGE, "-", "p = 0.125 (HTMuon)"),
                            ("0.5", ORANGE, ":", "p = 0.5")]:
        c = d7["curves"][f"p{p}_matched_m50"]
        a.plot(np.array(c["t"]) + 1, c["theta_mean"], color=col, ls=ls, label=lab + ", matched step")
    c = d7["curves"]["p0.125_large_m50"]
    a.plot(np.array(c["t"]) + 1, c["theta_mean"], color=ORANGE, ls="--", label="p = 0.125, 8x larger step")
    a.set_xscale("log")
    a.set_xlabel("step t + 1")
    a.set_ylabel("alignment theta_t (mean of 7 seeds)")
    a.set_title("m = 50: two phases for every filter")
    legend_below(a, 1, y=-0.17)
    a = ax[1]
    rows = d1["sgd"]
    a.plot([r["m"] for r in rows], [1 - r["pred_thm16"] for r in rows], color=INK)
    a.errorbar([r["m"] for r in rows], [1 - r["meas_ratio"][0] for r in rows], **mk(INK, "o"), label="SGD (line: Thm 16)")
    for p, col, mkr in [(0.0, BLUE, "s"), (0.125, ORANGE, "^")]:
        for step, ls, fill in [("matched", "-", True), ("large", "--", False)]:
            rr = [r for r in d7["rows"] if r["p"] == p and r["step"] == step]
            a.plot([r["m"] for r in rr], [1 - r["pred_selfconsistent"] for r in rr], color=col, ls=ls)
            kw = mk(col, mkr)
            if not fill:
                kw.update(mfc="none", mec=col)
            a.errorbar([r["m"] for r in rr], [1 - r["meas_ratio"][0] for r in rr], **kw,
                       label=f"p = {p}, {step} step (line: self-consistent)")
    a.set_xscale("log")
    a.set_yscale("log")
    a.set_xlabel("gap m")
    a.set_ylabel("1 - theta_inf")
    a.set_title("predicted vs measured theta_inf")
    legend_below(a, 1, y=-0.17)
    fig.suptitle("(M1) filtered updates in the authors' setup (d = 500, k = 50, sigma = 0.5, T = 30000)", y=1.0, fontsize=11)
    save(fig, "fig7_deng_setup_filters.png")
