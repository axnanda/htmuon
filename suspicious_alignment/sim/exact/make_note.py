"""Build notes/research/sim_exact_filters.md from note_src.md (prose) + compact tables computed from results/*.json.

Markers `{{T:name}}` in note_src.md are replaced by the table `name` built below, so that every number in the
note's tables is regenerated from the raw results.   Usage:  python3 make_note.py [--list]
"""
import json
import os
import sys

import numpy as np

import make_tables as mt
import specfilt as sf

HERE = os.path.dirname(os.path.abspath(__file__))
NOTE = os.path.normpath(os.path.join(HERE, "..", "..", "notes", "research", "sim_exact_filters.md"))
CORE = ["sgd", "muon", "ht0.125", "ht0.5", "ech1", "ech20", "ech40"]
ALL = mt.OPTS
NAME = mt.NAME
f, g, pm, load = mt.f, mt.g, mt.pm, mt.load


def table(header, rows):
    out = ["| " + " | ".join(header) + " |", "|" + "|".join(["---"] * len(header)) + "|"]
    out += ["| " + " | ".join(str(x) for x in r) + " |" for r in rows]
    return "\n".join(out)


def capture(fn, opts=None):
    """Run a make_tables section and return its markdown (optionally with a reduced filter list)."""
    old, mt.out[:] = mt.OPTS, []
    if opts is not None:
        mt.OPTS = opts
    try:
        fn()
    finally:
        mt.OPTS = old
    txt = "\n".join(mt.out)
    mt.out[:] = []
    return txt


def drop_heading(txt):
    return "\n".join(l for l in txt.split("\n") if not l.startswith("### ")).strip()


def rows_of(*names):
    r = []
    for n in names:
        j = load(n)
        r += j["rows"] if j else []
    return r


T = {}


def reg(name):
    def deco(fn):
        T[name] = fn
        return fn
    return deco


# ----------------------------------------------------------------------------------------- E0
@reg("e0")
def t_e0():
    j = load("e0_baseline.json")
    rows = [[r["m"], pm(r["E_align_mean"], r["E_align_sd"]), f(r["Std_align_mean"]),
             " / ".join(f(x) for x in r["E_align_dense"]), f(r["theta_inf"]), f(r["ratio1"]), f(r["ratio2"], 5),
             f"{r['theta0_mean']:.4f} → {r['theta_min_mean']:.4f} @ t={r['t_min_median']:.0f}",
             f"{r['tau_slowest_steps']:.0f}"] for r in j["table"]]
    return table(["m", "E[Align], eigenbasis runs, 7 seeds (mean ± sd over seeds)", "Std[Align] within a run",
                  "E[Align], literal port of quad_sim.py, seeds 42 / 87", "Theorem 16 θ_∞", "Σ_D λ / Σ λ", "Σ_D λ² / Σ λ²",
                  "θ_0 → θ_min @ t (seed mean; median t)", "slowest time constant 1/(2ηλ_d) [steps]"], rows)


# ----------------------------------------------------------------------------------------- E1
@reg("calib")
def t_calib():
    j = load("e1_twophase_a.json")
    c = j["calibration"]
    rows = [[NAME[o], g(c[o]["eta_rule"], 4), g(c[o]["c"], 4), g(c[o]["f2"], 4), g(c[o]["eta_eff"], 4),
             g(c[o]["eta_rule"] / 0.003, 3)] for o in ALL]
    return table(["filter", "η_rule (κ = 1)", "c = E⟨Ξ,F(Ξ)⟩ / (σ² d n)", "E mean_j f(s_j)²", "η_eff = η_rule · c",
                  "η_rule / η_SGD"], rows)


@reg("twophase")
def t_twophase():
    rows = rows_of("e1_twophase_a.json", "e1_twophase_b.json")
    out = []
    ms = (5, 20, 100, 500)
    for o in ALL:
        line = [NAME[o]]
        for m in ms:
            r = [r for r in rows if r["opt"] == o and r["m"] == m][0]
            line.append(f"{r['theta_min']:.3f} @ {r['t_min']} → {r['theta_late']:.4f} ± {r['theta_late_sd']:.4f}")
        r20 = [r for r in rows if r["opt"] == o and r["m"] == 20][0]
        s20 = [r for r in rows if r["opt"] == "sgd" and r["m"] == 20][0]
        line.append(g(r20["loss_late"] / s20["loss_late"], 3))
        out.append(line)
    ref = {m: [r for r in rows if r["opt"] == "sgd" and r["m"] == m][0] for m in ms}
    out.append(["*θ_0*"] + [f(ref[m]["theta0"], 4) for m in ms] + [""])
    out.append(["*SGD exact (finite T) at η = 0.003*"] + [f(ref[m]["sgd_finiteT_at_eta_eff"]) for m in ms] + [""])
    out.append(["*Theorem 16 θ_∞*"] + [f(ref[m]["thm16_at_eta_eff"]) for m in ms] + [""])
    return table(["filter"] + [f"m = {m}: θ_min @ t → θ late (t ≥ 2400, 3 seeds)" for m in ms] + ["late loss / SGD's (m = 20)"], out)


@reg("late")
def t_late():
    rows = rows_of("e1_late_a.json", "e1_late_b.json")
    ms = sorted(set(r["m"] for r in rows))
    out = []
    for o in ALL:
        rr = {m: [r for r in rows if r["m"] == m and r["opt"] == o][0] for m in ms}
        dev = max(abs(rr[m]["theta_late"] - rr[m]["sgd_finiteT_at_eta_eff"]) for m in ms)
        lr = [rr[m]["loss_late"] / [r for r in rows if r["m"] == m and r["opt"] == "sgd"][0]["loss_late"] for m in ms]
        out.append([NAME[o]] + [pm(rr[m]["theta_late"], rr[m]["theta_late_sd"]) for m in ms] + [f(dev), f"{min(lr):.3f}–{max(lr):.3f}"])
    ref = {m: [r for r in rows if r["m"] == m and r["opt"] == "sgd"][0] for m in ms}
    out.append(["*SGD exact, finite T (ratio of expectations)*"] + [f(ref[m]["sgd_finiteT_at_eta_eff"]) for m in ms] + ["", ""])
    out.append(["*Theorem 16 θ_∞ (η = 0.003)*"] + [f(ref[m]["thm16_at_eta_eff"]) for m in ms] + ["", ""])
    out.append(["*Σ_D λ / Σ λ*"] + [f(ref[m]["ratio1"]) for m in ms] + ["", ""])
    out.append(["*Σ_D λ² / Σ λ²*"] + [f(ref[m]["ratio2"], 5) for m in ms] + ["", ""])
    out.append(["*T ; seeds*"] + [f"{ref[m]['T']} ; {len(ref[m]['seeds'])}" for m in ms] + ["", ""])
    return table(["filter"] + [f"m = {m}" for m in ms] + ["max over m of abs(θ_late − SGD formula at the filter's η_eff)", "late loss / SGD's (range over m)"], out)


@reg("late_diag")
def t_late_diag():
    rows = rows_of("e1_late_a.json")
    out = []
    for o in ALL:
        r = [r for r in rows if r["m"] == 20 and r["opt"] == o][0]
        out.append([NAME[o], f(r["snr_frob_late"], 3), f"{r['sv_inp_late'][0]:.2f} / {r['sv_inp_late'][5]:.2f}",
                    f"{r['sv_true_late'][0]:.2f} / {r['sv_true_late'][5]:.2f}", f(r["theta_late"], 3), f(r["theta_stoch_late"], 3),
                    f(r["upd_frac_late"], 3), f(r["ovl_inp_late"], 3), f(r["ovl_true_late"], 3)])
    return table(["filter", "‖AW‖²_F / E‖Ξ‖²_F", "top / median s.v. of G", "top / median s.v. of AW", "θ (true gradient)",
                  "θ of the stochastic gradient G", "fraction of ‖update‖² in D", "overlap of top-k left sing. subspace of G with D",
                  "same for the true gradient AW"], out)


@reg("sweep")
def t_sweep():
    rows = rows_of("e1_sweep.json") + [r for r in rows_of("e1_twophase_a.json") if r["m"] == 20]
    ks = sorted(set(r["kappa"] for r in rows))
    out = []
    for o in ALL:
        line = [NAME[o]]
        for kp in ks:
            r = [r for r in rows if r["opt"] == o and r["kappa"] == kp]
            if not r:
                line.append("–")
            elif r[0]["diverged"]:
                line.append("diverged")
            else:
                r = r[0]
                line.append(f"{r['theta_late']:.3f} ({r['loss_late']:.3g}; {r['sv_true_late'][0] / r['sv_inp_late'][0]:.2f}; {r['upd_frac_late']:.2f})")
        out.append(line)
    prob = sf.Problem(200, 20, 50, 20)
    line = ["*Theorem 16 at η = κ · 0.003*"]
    for kp in ks:
        line.append(f(prob.theta_inf(kp * 0.003)) if kp * 0.003 * 100 < 2 else "unstable")
    out.append(line)
    return table(["filter"] + [f"κ = {kp:g}" for kp in ks], out)


@reg("signal")
def t_signal():
    rows = rows_of("e1_signal.json")
    out = []
    ms = (5, 20, 100)
    prob = {m: sf.Problem(200, 20, 50, m) for m in ms}
    for o in ALL:
        line = [NAME[o]]
        for sig in (0.0, 0.5):
            for m in ms:
                r = [r for r in rows if r["opt"] == o and r["m"] == m and r["sigma"] == sig]
                if not r:
                    line.append("–")
                else:
                    r = r[0]
                    line.append(f"{r['theta_late']:.4f} ({r['upd_frac_late']:.2f})")
        kind, p = sf.parse_opt(o)
        if kind in ("muon", "ht"):
            q = 2.0 / (1.0 - (p or 0.0))
            line.append(" / ".join(f"{(prob[m].lam[:20] ** q).sum() / (prob[m].lam[:50] ** q).sum():.4f}" for m in ms))
        else:
            line.append("–")
        out.append(line)
    out.append(["*Σ_D λ² / Σ λ² (all d)*"] + [f(prob[m].ratio(2), 4) for m in ms] * 2 + [""])
    out.append(["*Theorem 16 θ_∞ (η = 0.003)*"] + [f(prob[m].theta_inf(0.003), 4) for m in ms] * 2 + [""])
    return table(["filter"] + [f"noise-free, m = {m}" for m in ms] + [f"σ = 0.5, κ = 16, m = {m}" for m in ms] +
                 ["limit-cycle prediction Σ_{i≤k} λ^q / Σ_{i≤n} λ^q, q = 2/(1−p), m = 5 / 20 / 100"], out)


@reg("limit")
def t_limit():
    j = load("e1_extra_limit.json")
    return table(["m", "n", "filter", "θ late (measured)", "prediction Σ_{i≤k} λ^q / Σ_{i≤min(n,d)} λ^q", "q = 2/(1−p)",
                  "gradient energy in Hessian rows < k / k..n−1 / ≥ n", "fraction of ‖update‖² in D"],
                 [[r["m"], r["n"], NAME[r["opt"]], f(r["theta_late"], 5), f(r["pred_topn"], 5), g(r["q"], 3),
                   f"{r['theta_tail_energy']:.4f} / {r['energy_rows_k_to_n']:.4f} / {r['energy_rows_ge_n']:.1g}",
                   f(r["upd_frac_late"], 3)] for r in j["rows"]])


@reg("lownoise")
def t_lownoise():
    rows = [r for r in rows_of("e1_lownoise.json") if r["sigma"] == 0.05]
    out = []
    for r in rows:
        prob = sf.Problem(200, 20, 50, r["m"], sigma=0.05)
        out.append([NAME[r["opt"]], r["m"], f"{r['theta_min']:.3f} @ {r['t_min']}", pm(r["theta_late"], r["theta_late_sd"]),
                    g(r["loss_late"], 3), f(r["snr_frob_late"], 2), f"{r['sv_inp_late'][0]:.2f} / {r['sv_true_late'][0]:.2f}",
                    f(r["upd_frac_late"], 3), f(r["ovl_inp_late"], 3), f(prob.theta_inf(r["eta_eff_drift"]))])
    return table(["filter", "m", "θ_min @ t", "θ late (t ≥ 1600, 2 seeds)", "late loss", "‖AW‖² / E‖Ξ‖²",
                  "top s.v. of G / of AW", "fraction of ‖update‖² in D", "overlap_k(G)", "Theorem 16 at η_eff"], out)


@reg("largeinit")
def t_largeinit():
    return drop_heading(capture(mt.e1_largeinit))


@reg("momentum_late")
def t_momentum_late():
    rows = [r for r in rows_of("e1_momentum.json") if r.get("tag") is None and r["sigma"] > 0]
    ms = (5, 20, 100)
    out = []
    for o in CORE:
        line = [NAME[o]]
        for m in ms:
            r = [r for r in rows if r["opt"] == o and r["m"] == m][0]
            line.append(f"{r['theta_late']:.4f} ± {r['theta_late_sd']:.4f} ({r['sgdmom_finiteT_at_eta_eff']:.4f})")
        out.append(line)
    s = {m: [r for r in rows if r["opt"] == "sgd" and r["m"] == m][0] for m in ms}
    out.append(["*SGD + Nesterov, exact stationary, η = 0.003*"] + [f(s[m]["sgdmom_theta_inf_at_eta_eff"]) for m in ms])
    out.append(["*Theorem 16 (no momentum), η = 0.003*"] + [f(s[m]["thm16_at_eta_eff"]) for m in ms])
    out.append(["*Σ_D λ / Σ λ*"] + [f(s[m]["ratio1"]) for m in ms])
    out.append(["*T (2 seeds)*"] + [s[m]["T"] for m in ms])
    return table(["filter"] + [f"m = {m}: θ late (exact SGD+Nesterov value at the filter's η_eff)" for m in ms], out)


@reg("momentum_runs")
def t_momentum_runs():
    rows = rows_of("e1_momentum.json")
    logs = np.load(os.path.join(sf.RES, "e1_momentum_logs.npz"))
    out = []
    for tag, lab in (("large", "drift-matched η, T = 6000"), ("nomomlr", "momentum-free η, T = 2000")):
        for o in CORE:
            r = [r for r in rows if r.get("tag") == tag and r["opt"] == o][0]
            fin, _ = mt._final_theta(logs, r["rid"])
            out.append([lab, NAME[o], g(r["eta"], 4), g(r["eta_eff_drift"], 4), f"{r['theta_min']:.3f} @ {r['t_min']}", f(fin),
                        g(r["loss_late"], 4), f(r["sgdmom_theta_inf_at_eta_eff"]), f(r["thm16_at_eta_eff"])])
    return table(["setting (m = 20, W0 ~ N(0,1), 2 seeds)", "filter", "η", "η_eff", "θ_min @ t", "θ over the final 200 steps",
                  "late loss (last 20 %)", "SGD + Nesterov exact stationary at η_eff", "Theorem 16 (no momentum) at η_eff"], out)


@reg("n1")
def t_n1():
    return drop_heading(capture(mt.e1_n1))


# ----------------------------------------------------------------------------------------- E2
def regs(d, scale=1.0):
    return mt.reg_str2(d, scale)


@reg("e2_sgdtraj")
def t_e2_sgdtraj():
    rows = load("e23_states.json")["rows"]
    out = []
    for m in (20,):
        rr = sorted([r for r in rows if r["traj"] == "sgd" and r["m"] == m], key=lambda r: r["t"])
        for r in rr:
            d = r["per_opt"]
            deng = g(r["deng_eta_star"], 3) if (r["deng_num"] > 0 and r["deng_den"] > 0) else "↓ all"
            out.append([r["t"], f(r["theta"], 3), g(r["snr_frob"], 3), deng] + [regs(d[o]) for o in CORE] +
                       [g(d["muon"]["eta_star"] * d["muon"]["nfac"], 3)])
    return table(["t", "θ_t", "‖AW‖² / E‖Ξ‖²", "Deng η* (closed form)"] + [NAME[o] + " (MC)" for o in CORE] +
                 ["Muon, in SGD-norm units η*·‖F(G)‖/‖G‖"], out)


@reg("e2_owntraj")
def t_e2_owntraj():
    rows = load("e23_states.json")["rows"]
    out = []
    ts = (0, 30, 100, 400, 700, 1000, 2000, 3000)
    for m in (20, 100):
        for o in CORE:
            line = [m, NAME[o]]
            for tt in ts:
                r = [r for r in rows if r["traj"] == o and r["m"] == m and r["t"] == tt][0]
                d = r["per_opt"][o]
                line.append(f"{r['theta']:.2f}; {regs(d, 1.0 / d['eta_run'])}")
            out.append(line)
    return table(["m", "filter"] + [f"t = {tt}: θ; regime, η*/η_run" for tt in ts], out)


@reg("e2_regimes")
def t_e2_regimes():
    rows = load("e23_states.json")["rows"]
    cnt = {}
    for r in rows:
        for o, d in r["per_opt"].items():
            cnt.setdefault(o, {}).setdefault(d["regime"], 0)
            cnt[o][d["regime"]] += 1
    out = [[NAME[o], sum(cnt[o].values()), cnt[o].get("dec<inc", 0), cnt[o].get("dec", 0), cnt[o].get("inc", 0),
            cnt[o].get("inc<dec", 0)] for o in ALL]
    return table(["filter", "state evaluations", "↓↑ (decrease below η*, increase above)", "↓ for every η", "↑ for every η",
                  "↑↓ (increase below η*, decrease above)"], out)


@reg("e2_scale")
def t_e2_scale():
    j = load("e23_scale.json")
    out = []
    for step in (0, 100):
        rr = [r for r in j["rows"] if r["t"] == step and r["gamma"] != "noise-free"]
        for lab, cond in (("signal-dominated (‖AW‖²/E‖Ξ‖² > 30)", lambda r: r["snr_frob"] > 30),
                          ("noise-dominated (‖AW‖²/E‖Ξ‖² < 0.3)", lambda r: r["snr_frob"] < 0.3)):
            line = [f"SGD traj. t = {step}", lab]
            for o in CORE:
                xs = [np.log(r["gamma"]) for r in rr if cond(r) and r["per_opt"][o]["regime"] == "dec<inc"]
                ys = [np.log(r["per_opt"][o]["eta_star"]) for r in rr if cond(r) and r["per_opt"][o]["regime"] == "dec<inc"]
                line.append(f"{np.polyfit(xs, ys, 1)[0]:.2f} (n={len(xs)})" if len(xs) >= 2 else "–")
            out.append(line)
    out.append(["*prediction, signal-dominated*", "1 − p (Echelon: 1)"] + ["0", "1", "0.875", "0.5", "1", "1", "1"])
    return table(["state (scaled by γ = 2^-6 … 2^8)", "regime"] + [NAME[o] for o in CORE], out)


@reg("e2_scale_rows")
def t_e2_scale_rows():
    j = load("e23_scale.json")
    rr = [r for r in j["rows"] if r["t"] == 0 and r["gamma"] != "noise-free"]
    out = [[f"{r['gamma']:g}", g(r["gnorm_true"], 3), g(r["snr_frob"], 3)] + [g(r["per_opt"][o]["eta_star"], 3) for o in CORE]
           for r in rr]
    return table(["γ", "‖A(γW)‖_F", "‖AW‖² / E‖Ξ‖²"] + [NAME[o] for o in CORE], out)


@reg("e2_mdep")
def t_e2_mdep():
    j = load("e23_mdep.json")
    out = []
    for state in ("init", "rise"):
        for r in sorted([r for r in j["rows"] if r["state"] == state], key=lambda r: r["m"]):
            out.append([state, r["m"], f(r["theta"], 4), f(r["deng_theta_star"], 4), g(r["snr_frob"], 3)] +
                       [regs(r["per_opt"][o]) for o in CORE])
    return table(["state", "m", "θ", "Deng θ*", "‖AW‖² / E‖Ξ‖²"] + [NAME[o] for o in CORE], out)


@reg("highalign")
def t_highalign():
    return drop_heading(capture(mt.e2_highalign, opts=CORE))


@reg("bounds")
def t_bounds():
    j = load("e2_etastar_bounds.json")
    out = []
    for r in j["rows"]:
        if r["seed"] != 42 or r["t"] not in (0, 5, 100, 1000, 30000):
            continue
        es = r["eta_star"]
        out.append([r["m"], r["t"], f(r["theta"]), g(r["snr"], 3), g(es, 4), g(r["L7"], 3), g(r["U8"], 4), "0.02",
                    f"[{r['nf_lo']:.4f}, {r['nf_hi']:.4f}]", "yes" if r["cond_thm8"] else "no",
                    "**violated**" if (r["cond_thm8"] and es > 0.02) else ("ok" if r["cond_thm8"] else "n/a"),
                    "**violated**" if (r["cond_thm8"] and es > r["U8"]) else ("ok" if r["cond_thm8"] else "n/a")])
    return table(["m", "t", "θ_t", "‖Ax‖² / E‖ξ‖²", "η*_t (closed form)", "Thm 7 lower bound", "Thm 8 upper bound", "2/λ_1",
                  "noise-free sandwich [2/(λ_1+λ_{k+1}), 2/(λ_k+λ_d)]", "Thm 8 hypothesis θ_t ≥ e_B/(e_B+e_D)",
                  "Cor. 9: η* ≤ 2/λ_1", "Thm 8: η* ≤ bound"], out)


@reg("bounds_count")
def t_bounds_count():
    j = load("e2_etastar_bounds.json")
    rows = j["rows"]
    hyp = [r for r in rows if r["cond_thm8"] and r["eta_star"] is not None]
    v9 = [r for r in hyp if r["eta_star"] > 0.02]
    v8 = [r for r in hyp if r["eta_star"] > r["U8"]]
    l7 = all(r["eta_star"] is None or r["eta_star"] >= r["L7"] for r in rows)
    return (f"{len(rows)} states (4 values of m × 2 seeds × 7 times); Theorem-8 hypothesis holds in {len(hyp)}; "
            f"Corollary 9 (η* ≤ 2/λ_1) violated in {len(v9)} of them, Theorem 8's bound violated in {len(v8)}; "
            f"Theorem 7's lower bound holds in all {len(rows)}: {l7}.")


@reg("bounds_mc")
def t_bounds_mc():
    mc = load("e2_etastar_bounds.json")["mc"]
    return table(["η", "E[θ_1] − θ_0 (mean over 20000 draws)", "s.e.", "ratio of expectations"],
                 [[f"{e:.5f}", f"{a:+.3e}", f"{b:.1e}", f"{c:+.3e}"] for e, a, b, c in
                  zip(mc["etas"], mc["dtheta_mean"], mc["dtheta_se"], mc["dtheta_ratio_of_expectations"])])


# ----------------------------------------------------------------------------------------- E3
@reg("e3_own")
def t_e3_own():
    rows = load("e23_states.json")["rows"]
    out = []
    ts = {20: (0, 100, 400, 1000, 1500, 3000), 100: (0, 100, 400, 1000, 2000, 3000), 500: (0, 100, 400, 1000, 2000, 3000)}
    for m in (20, 100, 500):
        for o in CORE:
            line = [m, NAME[o]]
            for tt in ts[m]:
                r = [r for r in rows if r["traj"] == o and r["m"] == m and r["t"] == tt][0]
                d = r["per_opt"][o]
                er = d["eta_run"]
                a, b = d["etaD"] / er, d["etaB"] / er
                s = f"t={tt}, θ={r['theta']:.2f}: {a:.3g} / {b:.3g} / {d['etaD_gp'] / er:.3g}"
                line.append(f"**{s}**" if d["ratio_DB"] > 1 else s)
            out.append(line)
    return table(["m", "filter"] + [f"state {i + 1}" for i in range(6)], out)


@reg("e3_mdep")
def t_e3_mdep():
    j = load("e23_mdep.json")
    out = []
    for state in ("init", "rise"):
        for r in sorted([r for r in j["rows"] if r["state"] == state], key=lambda r: r["m"]):
            line = [state, r["m"], f(r["theta"], 4), f(r["deng_theta_crit"], 4)]
            for o in ALL:
                x = r["per_opt"][o]["ratio_DB"]
                line.append(f"**{x:.3g}**" if x > 1 else f"{x:.3g}")
            out.append(line)
    return table(["state", "m", "θ", "Deng θ^crit"] + [NAME[o] for o in ALL], out)


@reg("e3_mdep_gp")
def t_e3_mdep_gp():
    j = load("e23_mdep.json")
    out = []
    for state in ("init", "rise"):
        for r in sorted([r for r in j["rows"] if r["state"] == state], key=lambda r: r["m"]):
            if r["m"] not in (5, 20, 100, 500):
                continue
            line = [state, r["m"]]
            for o in ALL:
                d = r["per_opt"][o]
                x = d["ratio_DB_gp"]
                line.append((f"**{x:.3g}**" if x > 1 else f"{x:.3g}") + f" ({d['etaD_gp'] / d['etaD']:.2f})")
            out.append(line)
    return table(["state", "m"] + [NAME[o] for o in ALL], out)


@reg("e3_reversals")
def t_e3_reversals():
    rows = load("e23_states.json")["rows"]
    n = n_rev = 0
    big = []
    for r in rows:
        for o, d in r["per_opt"].items():
            if o != r["traj"] and r["traj"] != "sgd":
                continue
            n += 1
            if d["ratio_DB"] > 1:
                n_rev += 1
                if d["ratio_DB"] > 1.15:
                    big.append((r["m"], r["traj"], o, r["t"], d["ratio_DB"], r["theta"], r["snr_frob"]))
    ms = sorted(set(b[0] for b in big))
    smin = min(b[6] for b in big) if big else float("nan")
    return (f"{n_rev} of {n} (state, filter) evaluations have η_D^loss > η_B^loss; {len(big)} of them by more than 15 %, "
            f"all at m ∈ {ms} with θ ≥ {min(b[5] for b in big):.3f} and ‖AW‖²/E‖Ξ‖² ≥ {smin:.0f} "
            f"(largest ratio {max(b[4] for b in big):.2f}); the remaining {n_rev - len(big)} are within 10 % of 1 and occur at "
            f"(near-)stationary states.")


@reg("e3_continue")
def t_e3_continue():
    j = load("e3_continue.json")
    rows = j["rows"]
    out = []
    cases = [(20, 100), (20, 1500), (100, 400), (100, 2000), (100, 3000), (500, 200), (500, 3000)]
    for m, st in cases:
        for o in CORE:
            ro = {r["variant"]: r for r in rows if r["m"] == m and r["t_ckpt"] == st and r["opt"] == o}
            if not ro:
                continue
            r0 = ro["full"]
            x2 = [f"{ro[v]['ratio']:.3f}" if v in ro else "–" for v in ("updD_x2", "updB_x2")]
            out.append([m, st, NAME[o], f(r0["theta0"], 3), g(r0["L0"] / r0["loss_final_run"], 3), f(r0["LD0_frac"], 3)] +
                       [f"{ro[v]['ratio']:.3f}" for v in ("full", "updD", "updB", "gradD", "gradB")] + x2)
    return table(["m", "t0", "filter", "θ(t0)", "L(t0) / late loss of the run", "share of L in D", "full", "P^D F(G)", "P^B F(G)",
                  "F(P^D G)", "F(P^B G)", "2η: P^D F(G)", "2η: P^B F(G)"], out)


# ----------------------------------------------------------------------------------------- E4
@reg("e4_aniso")
def t_e4_aniso():
    j = load("e4_aniso.json")
    ex = {(r["m"], r["opt"]): r for r in load("extra_checks.json")["aniso_calibration"]}
    out = []
    for m in (20, 100):
        rr = [r for r in j["rows"] if r["m"] == m]
        for o in CORE:
            a = [r for r in rr if r["opt"] == o and r["setting"] == "large"][0]
            b = [r for r in rr if r["opt"] == o and r["setting"] == "late"][0]
            e = ex[(m, o)]
            out.append([m, NAME[o], f"{a['theta_min']:.3f} @ {a['t_min']}", pm(b["theta_late"], b["theta_late_sd"]),
                        f"{1 - b['theta_late']:.4f}", f(b["sgd_finiteT_at_eta_eff"]), f(b["linresp_theta_finiteT"]),
                        f"{e['c_B'] / e['c_D']:.2f}", f"{e['nu_D'] / e['nu_B']:.1f}", f(b["upd_frac_late"], 3),
                        f(b["theta_stoch_late"], 3)])
    return table(["m", "filter", "large init: θ_min @ t", "zero-init late θ (2 seeds)", "1 − θ late", "SGD formula (Thm 16, finite T) at η_eff",
                  "row-resolved linear-response prediction", "drift coefficient ratio c_B / c_D", "injected-noise ratio ν_D / ν_B",
                  "fraction of ‖update‖² in D", "θ of stochastic gradient"], out)


@reg("e4_kron")
def t_e4_kron():
    j = load("e4_kron.json")
    keyf = lambda r: (r.get("mu_alpha"), r.get("Kdom"), r["m"])
    keys = sorted(set(keyf(r) for r in j["rows"]), key=lambda x: (x[0], x[2]))
    out = []
    for o in CORE:
        line = [NAME[o]]
        for key in keys:
            b = [r for r in j["rows"] if keyf(r) == key and r["opt"] == o and r["setting"] == "late"][0]
            a = [r for r in j["rows"] if keyf(r) == key and r["opt"] == o and r["setting"] == "large"][0]
            line.append(f"{b['theta_late']:.4f} ± {b['theta_late_sd']:.4f} ({b['sgd_finiteT_at_eta_eff']:.4f}); {a['theta_min']:.3f} @ {a['t_min']}")
        out.append(line)
    s = {key: [r for r in j["rows"] if keyf(r) == key and r["opt"] == "sgd"][0] for key in keys}
    out.append(["*Σ_D h / Σ h ; Σ_D h² / Σ h² ; gap ratio at the block boundary*"] +
               [f"{s[k]['ratio1']:.4f} ; {s[k]['ratio2']:.4f} ; {s[k]['gap_ratio']:.3g}" for k in keys])
    return table(["filter"] + [f"α = {k[0]}, K = {k[1]}, m = {k[2]}: zero-init late θ (SGD exact at η_eff); large-init θ_min @ t" for k in keys], out)


@reg("e4_onestep")
def t_e4_onestep():
    out = []
    for part in ("aniso", "kron"):
        j = load(f"e4_{part}.json")
        keyf = lambda r: (r.get("mu_alpha"), r.get("Kdom"), r["m"])
        for key in sorted(set(keyf(r) for r in j["onestep"]), key=lambda x: (x[0] or 0, x[2])):
            lab = ("Σ ∝ A" if part == "aniso" else f"Kronecker α = {key[0]}, K = {key[1]}") + f", m = {key[2]}"
            for tt in (0, 2000):
                line = [lab, tt]
                for o in CORE:
                    r = [r for r in j["onestep"] if keyf(r) == key and r["traj"] == o and r["t"] == tt][0]
                    d = r["per_opt"][o]
                    x = d["ratio_DB"]
                    line.append(f"{r['theta']:.2f}; {regs(d, 1 / d['eta_run'])}; " + (f"**{x:.3g}**" if x > 1 else f"{x:.3g}"))
                out.append(line)
    return table(["setting", "t (own large-init trajectory)"] + [NAME[o] + ": θ; regime η*/η_run; η_D^loss/η_B^loss" for o in CORE], out)


@reg("underflow")
def t_underflow():
    u = load("extra_checks.json")["underflow"]
    return table(["run (n = 1, d = 500, m = 100, HT p = 0.5, seed 42, T = 30000)", "E[Align] (last 10000 steps)", "late loss",
                  "first step at which all 50 dominant coordinates are exactly 0.0", "limit-cycle loss prediction ½λ_1(η²λ_1/4)²"],
                 [[k_, f(v["E_align"], 4), g(v["loss_late"], 4), v["first_step_all_dominant_coords_exactly_zero"],
                   g(v["limit_cycle_loss_prediction"], 4)] for k_, v in u.items()])


@reg("echfrob")
def t_echfrob():
    j = load("e1_echfrob.json")
    base = rows_of("e1_late_a.json", "e1_twophase_a.json", "e1_signal.json")
    os_ = {(r["m"], r["state"]): r for r in load("e23_echfrob.json")["rows"]}
    cal = j["calibration"]
    out = []
    for r_ in (1, 10, 20, 40):
        for kind, lab in (("ech", "τ = ‖T‖_2 = s_{r+1}"), ("echf", "τ = ‖T‖_F")):
            o = f"{kind}{r_}"
            src = j["rows"] if kind == "echf" else base
            z = [r for r in src if r["opt"] == o and r["m"] == 20 and r["init"] == "zero" and r["sigma"] == 0.5 and r["kappa"] == 1.0][0]
            l = [r for r in src if r["opt"] == o and r["m"] == 20 and r["init"] == "gauss" and r["sigma"] == 0.5
                 and r["init_scale"] == 1.0 and r["kappa"] == 1.0][0]
            n0 = [r for r in src if r["opt"] == o and r["m"] == 20 and r["sigma"] == 0.0][0]
            c = cal[o] if o in cal else load("e1_late_a.json")["calibration"][o]
            out.append([r_, lab, g(c["eta_rule"], 4), g(c["c"], 3), g(c["eta_eff"], 4),
                        pm(z["theta_late"], z["theta_late_sd"]), f(z["sgd_finiteT_at_eta_eff"]),
                        f"{l['theta_min']:.3f} @ {l['t_min']}", f(n0["theta_late"]),
                        g(os_[(20, "init")]["per_opt"][o]["ratio_DB"], 3), g(os_[(500, "init")]["per_opt"][o]["ratio_DB"], 3),
                        g(os_[(20, "rise")]["per_opt"][o]["ratio_DB"], 3)])
    return table(["r", "tail scale", "η_rule", "c", "η_eff", "zero-init late θ, m = 20 (2 seeds)", "SGD formula at η_eff",
                  "large init: θ_min @ t", "noise-free late θ", "η_D^loss/η_B^loss at 'init', m = 20", "same, m = 500",
                  "same at 'rise', m = 20"], out)


@reg("reversal_noise")
def t_reversal_noise():
    rows = load("extra_checks.json")["reversal_noise"]
    out = [[r["m"], g(r["bulk_signal_over_noise"], 3)] +
           [(f"**{r[o]['ratio_noisy']:.3g}**" if r[o]["ratio_noisy"] > 1 else f"{r[o]['ratio_noisy']:.3g}") +
            f" / {r[o]['ratio_noise_free']:.3g}" for o in CORE] for r in rows]
    return table(["m", "‖P^B AW‖² / E‖P^B Ξ‖² (bulk block)"] + [NAME[o] + ": σ = 0.5 / noise-free" for o in CORE], out)


@reg("cpu")
def t_cpu():
    recs = [json.loads(l) for l in open(os.path.join(sf.RES, "cpu_log.jsonl"))]
    agg = {}
    for r in recs:
        a = agg.setdefault(r["name"], [0, 0.0, 0])
        a[0] += 1
        a[1] += r["cpu_s"]
        a[2] = r.get("n_svd", a[2])
    rows = [[k_, v[0], f"{v[1]:.0f}", v[2] or ""] for k_, v in agg.items()]
    tot = sum(r["cpu_s"] for r in recs)
    return table(["script / group", "times run", "CPU s (all runs)", "SVDs (last run)"], rows) + \
        f"\n\nTotal CPU time logged: {tot:.0f} s = {tot / 60:.1f} min (single thread; includes a repeated pilot and the sanity tests)."


def main():
    if "--list" in sys.argv:
        for k_ in T:
            print("=" * 20, k_)
            print(T[k_]())
        return
    src = open(os.path.join(HERE, "note_src.md")).read()
    missing = []
    for k_, fn in T.items():
        mark = "{{T:" + k_ + "}}"
        if mark in src:
            src = src.replace(mark, fn())
        else:
            missing.append(k_)
    if "{{T:" in src:
        bad = sorted(set(x.split("}}")[0] for x in src.split("{{T:")[1:]))
        raise SystemExit(f"unknown table markers: {bad}")
    os.makedirs(os.path.dirname(NOTE), exist_ok=True)
    with open(NOTE, "w") as fh:
        fh.write(src)
    print("wrote", NOTE, f"({len(src.splitlines())} lines); tables not used: {missing}")


if __name__ == "__main__":
    main()
