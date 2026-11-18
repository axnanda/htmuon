"""Turn results/*.json into the markdown tables embedded in notes/research/sim_exact_filters.md.
Usage:  python3 make_tables.py   ->  results/tables.md  (sections are skipped if their inputs are missing)
"""
import json
import os

import numpy as np

import specfilt as sf

OPTS = ["sgd", "muon", "ht0.125", "ht0.25", "ht0.5", "ech1", "ech10", "ech20", "ech40"]
NAME = {"sgd": "SGD", "muon": "Muon", "ht0.125": "HT p=.125", "ht0.25": "HT p=.25", "ht0.5": "HT p=.5",
        "ech1": "Ech r=1", "ech10": "Ech r=10", "ech20": "Ech r=20", "ech40": "Ech r=40"}
out = []


def P(*a):
    out.append(" ".join(str(x) for x in a))


def load(name):
    p = os.path.join(sf.RES, name)
    return json.load(open(p)) if os.path.exists(p) else None


def tab(header, rows):
    P("| " + " | ".join(header) + " |")
    P("|" + "|".join(["---"] * len(header)) + "|")
    for r in rows:
        P("| " + " | ".join(str(x) for x in r) + " |")
    P("")


def f(x, nd=4):
    if x is None or (isinstance(x, float) and not np.isfinite(x)):
        return "–"
    if isinstance(x, str):
        return x
    return f"{x:.{nd}f}"


def g(x, nd=3):
    if x is None or (isinstance(x, float) and not np.isfinite(x)):
        return "–"
    if isinstance(x, str):
        return x
    return f"{x:.{nd}g}"


def pm(a, b, nd=4):
    return f"{a:.{nd}f} ± {b:.{nd}f}"


# ------------------------------------------------------------------ E0
def e0():
    j = load("e0_baseline.json")
    if not j:
        return
    P("### T0. E0 baseline (d=500, k=50, eta=0.003, sigma=0.5, T=30000; E[Align] = mean of theta_t over the last 10000 steps)\n")
    rows = []
    for r in j["table"]:
        rows.append([r["m"], pm(r["E_align_mean"], r["E_align_sd"]), f(r["Std_align_mean"]),
                     " / ".join(f(x) for x in r["E_align_dense"]), f(r["theta_inf"]), f(r["theta_bar_window"]),
                     f(r["ratio1"]), f(r["ratio2"], 5), f(r["theta0_mean"]), f"{r['theta_min_mean']:.4f} @ t={r['t_min_median']:.0f}",
                     g(r["loss_late_mean"] / r["loss_inf"], 4), f"{r['tau_slowest_steps']:.0f}"])
    tab(["m", "E[Align] eigenbasis, 7 seeds (mean ± sd)", "Std[Align] (within run)", "E[Align] literal port, seeds 42 / 87",
         "Thm 16 theta_inf", "exact finite-T ratio-of-expectations", "sum_D lam / sum lam", "sum_D lam^2 / sum lam^2",
         "theta_0", "theta_min (seed mean) @ median t", "late loss / stationary loss", "slowest time constant 1/(2 eta lam_d)"], rows)


# ------------------------------------------------------------------ E1
def e1_rows(name):
    j = load(name)
    return j["rows"] if j else []


def e1_twophase():
    rows = e1_rows("e1_twophase_a.json") + e1_rows("e1_twophase_b.json")
    if not rows:
        return
    P("### T1a. E1 two-phase runs (M2, d=200, k=20, n=50, sigma=0.5, W0 ~ N(0,1), kappa=1, T=3000, 3 seeds; late = t >= 2400)\n")
    for m in (5, 20, 100, 500):
        rr = {r["opt"]: r for r in rows if r["m"] == m}
        if not rr:
            continue
        s = rr["sgd"]
        P(f"**m = {m}** (sum_D lam/sum lam = {s['ratio1']:.4f}, sum_D lam^2/sum lam^2 = {s['ratio2']:.5f}; "
          f"SGD stationary floor = 1.875 x (1+O(eta lam)); SGD loss at t=0: {s['loss0']:.4g})\n")
        t = []
        for o in OPTS:
            r = rr[o]
            t.append([NAME[o], g(r["eta"], 4), g(r["eta_eff_drift"], 4), f(r["theta0"], 3), f"{r['theta_min']:.3f} @ {r['t_min']}",
                      pm(r["theta_late"], r["theta_late_sd"]), f(r["sgd_finiteT_at_eta_eff"]), f(r["thm16_at_eta_eff"]),
                      g(r["loss_late"] / s["loss_late"], 3), "yes" if r["two_phase"] else "no",
                      f(r["theta_stoch_late"], 3), f(r["upd_frac_late"], 3), f(r["ovl_inp_late"], 3), f(r["ovl_true_late"], 3)])
        tab(["filter", "eta", "eta_eff = eta c", "theta_0", "theta_min @ t", "theta late (mean ± sd over seeds)",
             "SGD exact finite-T at eta_eff", "Thm 16 at eta_eff", "late loss / SGD's", "two-phase",
             "theta of stochastic gradient (late)", "update fraction in D (late)",
             "overlap top-k left sing. subspace of stoch. grad with D (late)", "same for true gradient"], t)


def e1_late():
    rows = e1_rows("e1_late_a.json") + e1_rows("e1_late_b.json")
    if not rows:
        return
    P("### T1b. E1 late-time alignment versus m (zero init, sigma=0.5, kappa=1; time average over the last 20% of the run)\n")
    ms = sorted(set(r["m"] for r in rows))
    hdr = ["filter"] + [f"m={m}" for m in ms]
    t = []
    for o in OPTS:
        t.append([NAME[o]] + [pm(*[(r["theta_late"], r["theta_late_sd"]) for r in rows if r["m"] == m and r["opt"] == o][0])
                              for m in ms])
    ref = {m: [r for r in rows if r["m"] == m and r["opt"] == "sgd"][0] for m in ms}
    t.append(["*SGD exact finite-T (ratio of expectations)*"] + [f(ref[m]["sgd_finiteT_at_eta_eff"]) for m in ms])
    t.append(["*Thm 16 theta_inf (eta=0.003)*"] + [f(ref[m]["thm16_at_eta_eff"]) for m in ms])
    t.append(["*sum_D lam / sum lam*"] + [f(ref[m]["ratio1"]) for m in ms])
    t.append(["*sum_D lam^2 / sum lam^2*"] + [f(ref[m]["ratio2"], 5) for m in ms])
    t.append(["*T, seeds*"] + [f"{ref[m]['T']}, {len(ref[m]['seeds'])}" for m in ms])
    tab(hdr, t)
    P("Deviation of each filter from its own linear-response prediction (theta_late − exact finite-T SGD formula at eta_eff), "
      "and late loss relative to SGD:\n")
    t = []
    for o in OPTS:
        rr = {m: [r for r in rows if r["m"] == m and r["opt"] == o][0] for m in ms}
        t.append([NAME[o]] + [f"{rr[m]['theta_late'] - rr[m]['sgd_finiteT_at_eta_eff']:+.4f} / {rr[m]['loss_late'] / ref[m]['loss_late']:.3f}"
                              for m in ms])
    tab(["filter (theta dev / loss ratio)"] + [f"m={m}" for m in ms], t)
    P("Late-phase diagnostics at m=20 (stochastic gradient = filter input):\n")
    t = []
    for o in OPTS:
        r = [r for r in rows if r["m"] == 20 and r["opt"] == o][0]
        t.append([NAME[o], f(r["snr_frob_late"], 3), f(r["sv_inp_late"][0], 2), f(r["sv_inp_late"][5], 2), f(r["sv_true_late"][0], 2),
                  f(r["sv_true_late"][5], 2), f(r["theta_stoch_late"], 3), f(r["upd_frac_late"], 3), f(r["ovl_inp_late"], 3),
                  f(r["ovl_true_late"], 3)])
    tab(["filter", "||AW||_F^2 / E||Xi||_F^2", "top s.v. of G", "median s.v. of G", "top s.v. of AW", "median s.v. of AW",
         "theta(G)", "update fraction in D", "overlap_k(G)", "overlap_k(AW)"], t)


def e1_sweep():
    rows = e1_rows("e1_sweep.json") + [r for r in e1_rows("e1_twophase_a.json") if r["m"] == 20]
    if not rows:
        return
    P("### T1c. E1 learning-rate sweep (m=20, sigma=0.5, W0 ~ N(0,1); eta = kappa x eta_rule; T=2000, 2 seeds (kappa=1: T=3000, 3 seeds))\n")
    ks = sorted(set(r["kappa"] for r in rows))
    for key, title, fmt in (("theta_late", "late alignment theta (true gradient)", lambda r: f(r["theta_late"])),
                            ("loss_late", "late loss", lambda r: g(r["loss_late"], 4)),
                            ("theta_min", "theta_min @ t", lambda r: f"{r['theta_min']:.3f} @ {r['t_min']}"),
                            ("upd", "update fraction in D / theta(G) / overlap_k(G), late",
                             lambda r: f"{r['upd_frac_late']:.3f} / {r['theta_stoch_late']:.3f} / {r['ovl_inp_late']:.3f}"),
                            ("sv", "top s.v. of filter input / top s.v. of AW, late",
                             lambda r: f"{r['sv_inp_late'][0]:.1f} / {r['sv_true_late'][0]:.1f}")):
        P(f"*{title}*\n")
        t = []
        for o in OPTS:
            line = [NAME[o]]
            for kp in ks:
                r = [r for r in rows if r["opt"] == o and r["kappa"] == kp]
                line.append("diverged" if (r and r[0]["diverged"]) else (fmt(r[0]) if r else "–"))
            t.append(line)
        tab(["filter"] + [f"kappa={kp:g}" for kp in ks], t)


def e1_signal():
    rows = e1_rows("e1_signal.json")
    if not rows:
        return
    P("### T1d. E1 signal-dominated late phase (T=1500, 2 seeds; late = last 20%)\n")
    for sig, title in ((0.0, "noise-free (sigma=0), W0 ~ 0.01 N(0,1), eta = eta_rule"),
                       (0.5, "sigma=0.5, kappa=16 (eta = 16 eta_rule), zero init")):
        P(f"*{title}*: late theta (mean ± sd) / update fraction in D / overlap_k(filter input)\n")
        rr = [r for r in rows if r["sigma"] == sig]
        ms = sorted(set(r["m"] for r in rr))
        t = []
        for o in OPTS:
            line = [NAME[o]]
            for m in ms:
                r = [r for r in rr if r["opt"] == o and r["m"] == m]
                if not r:
                    line.append("–")
                elif r[0]["diverged"]:
                    line.append("diverged")
                else:
                    r = r[0]
                    line.append(f"{r['theta_late']:.4f} ± {r['theta_late_sd']:.4f} / {r['upd_frac_late']:.3f} / {r['ovl_inp_late']:.3f}")
            t.append(line)
        prob = {m: sf.Problem(200, 20, 50, m) for m in ms}
        t.append(["*sum_D lam / sum lam*"] + [f(prob[m].ratio(1)) for m in ms])
        t.append(["*sum_D lam^2 / sum lam^2*"] + [f(prob[m].ratio(2), 5) for m in ms])
        t.append(["*sum_D lam^(2/(1-p)), p=.125 / .25 / .5*"] +
                 [" / ".join(f(prob[m].ratio(2 / (1 - p)), 5) for p in (0.125, 0.25, 0.5)) for m in ms])
        tab(["filter"] + [f"m={m}" for m in ms], t)
        P("late loss (mean) and top / k-th / (k+1)-th / median singular value of the TRUE gradient:\n")
        t = []
        for o in OPTS:
            line = [NAME[o]]
            for m in ms:
                r = [r for r in rr if r["opt"] == o and r["m"] == m]
                if not r or r[0]["diverged"]:
                    line.append("–")
                else:
                    r = r[0]
                    sv = r["sv_true_late"]
                    line.append(f"{r['loss_late']:.3g}; {sv[0]:.3g} / {sv[3]:.3g} / {sv[4]:.3g} / {sv[5]:.3g}")
            t.append(line)
        tab(["filter"] + [f"m={m}" for m in ms], t)


def e1_lownoise():
    rows = e1_rows("e1_lownoise.json")
    if not rows:
        return
    P("### T1e. E1 low noise (sigma=0.05, learning rates of the sigma=0.5 setting, W0 ~ N(0,1), T=2000, 2 seeds) and large init\n")
    t = []
    for r in rows:
        if r["sigma"] != 0.05:
            continue
        t.append([NAME[r["opt"]], r["m"], g(r["eta"], 4), f(r["theta0"], 3), f"{r['theta_min']:.3f} @ {r['t_min']}",
                  pm(r["theta_late"], r["theta_late_sd"]), g(r["loss_late"], 4), f(r["snr_frob_late"], 3),
                  f"{r['sv_inp_late'][0]:.2f} / {r['sv_true_late'][0]:.2f}", f(r["upd_frac_late"], 3), f(r["ovl_inp_late"], 3),
                  f(r["ratio1"]), f(r["ratio2"], 5)])
    tab(["filter", "m", "eta", "theta_0", "theta_min @ t", "theta late", "late loss", "||AW||^2/E||Xi||^2 (late)",
         "top s.v. of G / of AW (late)", "update fraction in D", "overlap_k(G)", "sum lam ratio", "sum lam^2 ratio"], t)
    t = []
    for r in rows:
        if r["sigma"] == 0.05:
            continue
        t.append([NAME[r["opt"]], r["m"], r["init_scale"], r["T"], f(r["theta0"], 3), f"{r['theta_min']:.3f} @ {r['t_min']}",
                  f(r["theta_late"]), g(r["loss_late"], 4), f(r["sgd_finiteT_at_eta_eff"])])
    if t:
        P("Large init (W0 std 10, sigma=0.5, kappa=1, 1 seed):\n")
        tab(["filter", "m", "init std", "T", "theta_0", "theta_min @ t", "theta late", "late loss", "SGD exact finite-T at eta_eff"], t)


def e1_momentum():
    rows = e1_rows("e1_momentum.json")
    if not rows:
        return
    P("### T1f. E1 with Nesterov momentum beta=0.95 (as in muon.py; sigma=0.5 unless stated; 2 seeds)\n")
    for init, title in (("gauss", "W0 ~ N(0,1), T=2000"), ("zero", "zero init (late-time runs)")):
        rr = [r for r in rows if r["init"] == init and r["sigma"] > 0]
        t = []
        for r in rr:
            t.append([NAME[r["opt"]], r["m"], r["T"], g(r["eta"], 4), f(r["theta0"], 3), f"{r['theta_min']:.3f} @ {r['t_min']}",
                      pm(r["theta_late"], r["theta_late_sd"]), g(r["loss_late"], 4), f(r["thm16_at_eta_eff"]),
                      f(r["sgd_finiteT_at_eta_eff"]), f(r["theta_inp_late"], 3), f(r["upd_frac_late"], 3), f(r["ovl_inp_late"], 3),
                      f"{r['sv_inp_late'][0]:.2f} / {r['sv_inp_late'][5]:.2f} / {r['sv_true_late'][0]:.2f}"])
        P(f"*{title}*\n")
        tab(["filter", "m", "T", "eta", "theta_0", "theta_min @ t", "theta late", "late loss", "Thm 16 at eta_eff",
             "SGD exact finite-T at eta_eff (no momentum)", "theta of filter input X", "update fraction in D", "overlap_k(X)",
             "top / median s.v. of X / top s.v. of AW"], t)
    rr = [r for r in rows if r["sigma"] == 0]
    if rr:
        P("*noise-free, W0 ~ 0.01 N(0,1), m=20, T=1500*\n")
        tab(["filter", "eta", "theta late", "late loss", "update fraction in D", "sum lam^2 ratio"],
            [[NAME[r["opt"]], g(r["eta"], 4), pm(r["theta_late"], r["theta_late_sd"]), g(r["loss_late"], 4),
              f(r["upd_frac_late"], 3), f(r["ratio2"], 5)] for r in rr])


def e1_n1():
    j = load("e1_n1.json")
    if not j:
        return
    rows = j["rows"]
    P("### T1g. (M1) n=1: F(g) = f(|g|) g/|g|, Deng's protocol (d=500, k=50, sigma=0.5, T=30000, E[Align] over last 10000 steps)\n")
    o5 = ["sgd", "muon", "ht0.125", "ht0.25", "ht0.5"]
    pr = [r for r in rows if r["group"] == "proto"]
    ms = sorted(set(r["m"] for r in pr))
    t = []
    for o in o5:
        t.append([NAME[o] + f" (eta={[r for r in pr if r['opt'] == o][0]['eta']:.4g})"] +
                 [pm(*[(r["E_align"], r["E_align_sd"]) for r in pr if r["opt"] == o and r["m"] == m][0]) for m in ms])
    t.append(["*Thm 16 (eta=0.003)*"] + [f([r for r in pr if r["opt"] == "sgd" and r["m"] == m][0]["thm16_at_eta_eff"]) for m in ms])
    tab(["filter (kappa=1, 4 seeds)"] + [f"m={m}" for m in ms], t)
    t = []
    for o in o5:
        line = [NAME[o]]
        for m in ms:
            r = [r for r in pr if r["opt"] == o and r["m"] == m][0]
            line.append(f"{r['theta_min']:.3f} @ {r['t_min']}")
        t.append(line)
    P("theta_min of the seed-mean curve @ t:\n")
    tab(["filter"] + [f"m={m}" for m in ms], t)
    kr = [r for r in rows if r["group"] == "kappa"] + [r for r in pr if r["m"] == 20]
    ks = sorted(set(r["kappa"] for r in kr))
    t = []
    for o in o5:
        line = [NAME[o]]
        for kp in ks:
            r = [r for r in kr if r["opt"] == o and r["kappa"] == kp]
            line.append(f"{r[0]['E_align']:.4f} (loss {r[0]['loss_late']:.3g}; |AW|/|G| {r[0]['gn_true_late'] / r[0]['gn_stoch_late']:.2f})"
                        if r else "–")
        t.append(line)
    P("m=20, learning-rate sweep (eta = kappa x eta_rule): E[Align] (late loss; ratio of true to stochastic gradient norm):\n")
    tab(["filter"] + [f"kappa={kp:g}" for kp in ks], t)
    fr = [r for r in rows if r["group"] == "free"]
    t = []
    for o in o5:
        line = [NAME[o]]
        for m in (5, 20, 100):
            r = [r for r in fr if r["opt"] == o and r["m"] == m][0]
            line.append(f"{r['E_align']:.4f} ± {r['E_align_sd']:.4f} (loss {r['loss_late']:.3g})")
        t.append(line)
    P("noise-free (sigma=0), 2 seeds: E[Align] over the last 10000 of 30000 steps (late loss):\n")
    tab(["filter", "m=5", "m=20", "m=100"], t)


# ------------------------------------------------------------------ E2 / E3 one-step
def reg_str(d, eta_scale=1.0):
    if d["regime"] == "dec<inc":
        return f"↓↑ {d['eta_star'] * eta_scale:.3g}"
    if d["regime"] == "inc<dec":
        return f"↑↓ {d['eta_star'] * eta_scale:.3g}"
    return "↓ all" if d["regime"] == "dec" else "↑ all"


def e2():
    j = load("e23_states.json")
    if not j:
        return
    rows = j["rows"]
    P("### T2a. E2: one-step alignment response at states on SGD's trajectory (all filters at the same state)\n")
    P("Entry: regime and critical step in NORM-EQUALISED units eta_n = eta ||F(G)||/||G|| (↓↑ x: E[theta] decreases for "
      "eta_n < x and increases above — Deng's low-alignment behaviour; ↓ all: decreases for every eta; ↑ all: increases "
      "for every eta; ↑↓ x: increases below x, decreases above).  From the ratio-of-expectations response (48 draws).\n")
    for m in (20, 100):
        rr = sorted([r for r in rows if r["traj"] == "sgd" and r["m"] == m], key=lambda r: r["t"])
        t = []
        for r in rr:
            line = [r["t"], f(r["theta"], 3), f(r["snr_frob"], 3),
                    g(r["deng_eta_star"], 3) if (r["deng_num"] > 0 and r["deng_den"] > 0) else ("↓ all" if r["deng_num"] > 0 else "?")]
            for o in OPTS:
                d = r["per_opt"][o]
                line.append(reg_str(d, d["nfac"]))
            t.append(line)
        P(f"**m = {m}**\n")
        tab(["t", "theta", "||AW||^2/E||Xi||^2", "Deng eta* (closed form)"] + [NAME[o] for o in OPTS], t)
    P("### T2b. E2: each filter on its OWN trajectory — critical step relative to the step actually used (eta*/eta_run), "
      "and the measured expected one-step change of theta at the running step (x 1e3, ± s.e.)\n")
    for m in (20, 100, 500):
        P(f"**m = {m}**\n")
        ts = sorted(set(r["t"] for r in rows if r["m"] == m))
        t = []
        for o in OPTS:
            line = [NAME[o]]
            for tt in ts:
                r = [r for r in rows if r["traj"] == o and r["m"] == m and r["t"] == tt]
                if not r:
                    line.append("–")
                    continue
                d = r[0]["per_opt"][o]
                er = d.get("eta_run")
                line.append(f"θ={r[0]['theta']:.2f}; {reg_str(d, 1.0 / er)}; {1e3 * d['dtheta_at_run']:+.2f}±{1e3 * d['dtheta_at_run_se']:.2f}")
            t.append(line)
        tab(["filter"] + [f"t={tt}" for tt in ts], t)
    P("### T2c. Expectation-of-ratio check: first sign change of the directly averaged E[theta(W − eta F(G))] − theta(W) on the "
      "step grid versus the ratio-of-expectations root (SGD-trajectory states, m=20; raw eta)\n")
    rr = sorted([r for r in rows if r["traj"] == "sgd" and r["m"] == 20], key=lambda r: r["t"])
    t = []
    for r in rr:
        line = [r["t"]]
        for o in ("sgd", "muon", "ht0.125", "ech20"):
            d = r["per_opt"][o]
            line.append(f"{g(d['eta_cross_EoR'])} vs {g(d['eta_star'])} ± {g(d['eta_star_se'], 2)}")
        t.append(line)
    tab(["t"] + [NAME[o] for o in ("sgd", "muon", "ht0.125", "ech20")], t)


def e2_scale():
    j = load("e23_scale.json")
    if not j:
        return
    P("### T2d. E2: scaling of the critical step with the gradient norm (state gamma x W, noise fixed, sigma=0.5; m=20)\n")
    for step in (0, 100):
        rr = [r for r in j["rows"] if r["t"] == step and r["gamma"] != "noise-free"]
        nf = [r for r in j["rows"] if r["t"] == step and r["gamma"] == "noise-free"][0]
        P(f"**state: SGD trajectory, t = {step}** (theta = {nf['theta']:.3f}); entries: regime, critical step eta* (raw units)\n")
        t = []
        for r in rr:
            t.append([f"{r['gamma']:g}", g(r["gnorm_true"], 3), f(r["snr_frob"], 3)] + [reg_str(r["per_opt"][o]) for o in OPTS])
        t.append(["noise-free, gamma=1", "", "inf"] + [reg_str(nf["per_opt"][o]) for o in OPTS])
        tab(["gamma", "||AW||_F", "||AW||^2/E||Xi||^2"] + [NAME[o] for o in OPTS], t)
        # fitted exponents over the signal-dominated range
        sl = []
        for o in OPTS:
            xs, ys = [], []
            for r in rr:
                d = r["per_opt"][o]
                if r["snr_frob"] > 30 and d["regime"] in ("dec<inc", "inc<dec"):
                    xs.append(np.log(r["gamma"]))
                    ys.append(np.log(d["eta_star"]))
            sl.append(f"{np.polyfit(xs, ys, 1)[0]:.3f} (n={len(xs)})" if len(xs) >= 2 else "–")
        tab(["fitted d log eta* / d log gamma (states with ||AW||^2/E||Xi||^2 > 30)"] + [NAME[o] for o in OPTS], [["slope"] + sl])


def e2_mdep():
    j = load("e23_mdep.json")
    if not j:
        return
    P("### T2e / T3c. m-dependence at states constructed identically for every m (same Gaussian Z; 32 draws)\n")
    for state, title in (("init", "'init': W = Z (isotropic, std 1)"),
                         ("rise", "'rise': typical SGD state at the first time theta_bar has recovered to 0.75 theta_inf")):
        rr = sorted([r for r in j["rows"] if r["state"] == state], key=lambda r: r["m"])
        P(f"**{title}** — alignment response: regime and raw critical step eta*\n")
        t = []
        for r in rr:
            t.append([r["m"], f(r["theta"], 4), f(r["deng_g_gap"], 4), f(r["deng_theta_star"], 4),
                      g(r["loss_over_floor"], 3) + (f" (t_r={r['t_r']})" if state == "rise" else "")] +
                     [reg_str(r["per_opt"][o]) for o in OPTS])
        tab(["m", "theta", "Deng g_gap", "Deng theta*", "loss / SGD floor"] + [NAME[o] for o in OPTS], t)
        P(f"**{title}** — loss thresholds: eta_D^loss / eta_B^loss (ratio)\n")
        t = []
        for r in rr:
            line = [r["m"], f(r["theta"], 4), f(r["deng_theta_crit"], 4)]
            for o in OPTS:
                d = r["per_opt"][o]
                line.append(f"{g(d['etaD'])} / {g(d['etaB'])} ({g(d['ratio_DB'])})")
            t.append(line)
        tab(["m", "theta", "Deng theta_crit"] + [NAME[o] for o in OPTS], t)


def e3():
    j = load("e23_states.json")
    if not j:
        return
    rows = j["rows"]
    P("### T3a. E3: loss thresholds of the projected updates on each filter's OWN trajectory\n")
    P("Entry: eta_D^loss/eta_run , eta_B^loss/eta_run  (ratio eta_D^loss/eta_B^loss).  A value below 1 in the first slot means the "
      "D-projected update at the running step raises the expected loss; **bold** = window (D raises, B lowers) contains the "
      "running step.\n")
    for m in (20, 100, 500):
        P(f"**m = {m}**\n")
        ts = sorted(set(r["t"] for r in rows if r["m"] == m))
        t = []
        for o in OPTS:
            line = [NAME[o]]
            for tt in ts:
                r = [r for r in rows if r["traj"] == o and r["m"] == m and r["t"] == tt]
                if not r:
                    line.append("–")
                    continue
                d = r[0]["per_opt"][o]
                er = d["eta_run"]
                a, b = d["etaD"] / er, d["etaB"] / er
                s = f"{a:.3g}, {b:.3g} ({d['ratio_DB']:.3g})"
                line.append(f"**{s}**" if (a < 1 < b) else s)
            t.append(line)
        tab(["filter"] + [f"t={tt}" for tt in ts], t)
    P("### T3b. E3: thresholds for all filters at the same state (SGD's trajectory), raw step sizes: "
      "eta_D^loss / eta_B^loss (ratio); second line: the same for the variant F(P^S G)\n")
    for m in (20, 100, 500):
        rr = sorted([r for r in rows if r["traj"] == "sgd" and r["m"] == m], key=lambda r: r["t"])
        P(f"**m = {m}** (Deng closed form for SGD in the first column)\n")
        t = []
        for r in rr:
            if r["t"] not in (0, 10, 30, 100, 400, 1000, 2000, 3000):
                continue
            line = [r["t"], f(r["theta"], 3), f(r["deng_theta_crit"], 4),
                    f"{g(r['deng_etaD'])} / {g(r['deng_etaB'])} ({g(r['deng_etaD'] / r['deng_etaB'])})"]
            for o in OPTS:
                d = r["per_opt"][o]
                line.append(f"{g(d['etaD'])} / {g(d['etaB'])} ({g(d['ratio_DB'])})<br>{g(d['etaD_gp'])} / {g(d['etaB_gp'])} ({g(d['ratio_DB_gp'])})")
            t.append(line)
        tab(["t", "theta", "Deng theta_crit", "Deng Thm 9"] + [NAME[o] for o in OPTS], t)


def e3_continue():
    j = load("e3_continue.json")
    if not j:
        return
    rows = j["rows"]
    P(f"### T3d. E3 continuation: L(t0+{j['TC']}) / L(t0) for each update variant (own trajectory, own eta, 2 noise seeds)\n")
    for m, steps in sorted((int(k_), v) for k_, v in j["cases"].items()):
        for st in steps:
            rr = [r for r in rows if r["m"] == m and r["t_ckpt"] == st]
            P(f"**m = {m}, checkpoint t0 = {st}**\n")
            t = []
            for o in OPTS:
                ro = {r["variant"]: r for r in rr if r["opt"] == o}
                if not ro:
                    continue
                r0 = ro["full"]
                t.append([NAME[o], f(r0["theta0"], 3), g(r0["L0"], 4), g(r0["L0"] / r0["loss_final_run"], 3), f(r0["LD0_frac"], 3)] +
                         [("div" if ro[v]["diverged"] else f"{ro[v]['ratio']:.3f}") for v in ("full", "updD", "updB", "gradD", "gradB")])
            tab(["filter", "theta(t0)", "L(t0)", "L(t0) / late loss of the run", "share of L in D", "full", "P^D F(G)", "P^B F(G)",
                 "F(P^D G)", "F(P^B G)"], t)


# ------------------------------------------------------------------ E4
def e4():
    o7 = ["sgd", "muon", "ht0.125", "ht0.5", "ech1", "ech20", "ech40"]
    for part, title in (("aniso", "anisotropic noise Sigma ∝ A (M2)"), ("kron", "Kronecker lift (M3), B = diag(j^-alpha)")):
        j = load(f"e4_{part}.json")
        if not j:
            continue
        rows = j["rows"]
        P(f"### T4 ({part}). E4 — {title}\n")
        keyf = lambda r: (r.get("mu_alpha"), r.get("Kdom"), r["m"])
        for key in sorted(set(keyf(r) for r in rows), key=lambda x: (x[0] or 0, x[2])):
            rr = [r for r in rows if keyf(r) == key]
            s = [r for r in rr if r["opt"] == "sgd"][0]
            lab = f"m = {key[2]}" + (f", alpha = {key[0]}, K = {key[1]}" if key[0] is not None else "")
            P(f"**{lab}** (sum h ratio = {s['ratio1']:.4f}, sum h^2 ratio = {s['ratio2']:.5f}, gap ratio at the block boundary "
              f"= {s['gap_ratio']:.3g})\n")
            t = []
            for o in o7:
                a = [r for r in rr if r["opt"] == o and r["setting"] == "large"][0]
                b = [r for r in rr if r["opt"] == o and r["setting"] == "late"][0]
                sb = [r for r in rr if r["opt"] == "sgd" and r["setting"] == "late"][0]
                t.append([NAME[o], g(a["eta"], 4), f(a["theta0"], 3), f"{a['theta_min']:.3f} @ {a['t_min']}", f(a["theta_late"]),
                          "yes" if a["two_phase"] else "no",
                          pm(b["theta_late"], b["theta_late_sd"]), f(b.get("sgd_finiteT_at_eta_eff")),
                          f(b.get("linresp_theta_finiteT")) if part == "aniso" else "n/a",
                          g(b["loss_late"] / sb["loss_late"], 3), f(b["upd_frac_late"], 3), f(b["theta_stoch_late"], 3),
                          f(b["ovl_inp_late"], 3)])
            tab(["filter", "eta", "theta_0 (large init)", "theta_min @ t", "theta at T=2000 (late 20%)", "two-phase",
                 "zero-init late theta", "SGD exact finite-T at eta_eff", "filter linear-response prediction",
                 "late loss / SGD's", "update fraction in D (late)", "theta(G) (late)", "overlap_k(G) (late)"], t)
        # one-step part
        os_ = j["onestep"]
        P("One-step statistics on each filter's own large-init trajectory: alignment-response regime (critical step / running step) "
          "and loss thresholds eta_D^loss/eta_run, eta_B^loss/eta_run (ratio D/B)\n")
        for key in sorted(set(keyf(r) for r in os_), key=lambda x: (x[0] or 0, x[2])):
            lab = f"m = {key[2]}" + (f", alpha = {key[0]}, K = {key[1]}" if key[0] is not None else "")
            P(f"**{lab}**\n")
            t = []
            for o in o7:
                line = [NAME[o]]
                for tt in (0, 100, 2000):
                    r = [r for r in os_ if keyf(r) == key and r["traj"] == o and r["t"] == tt][0]
                    d = r["per_opt"][o]
                    er = d["eta_run"]
                    line.append(f"θ={r['theta']:.3f}; {reg_str(d, 1 / er)}; {d['etaD'] / er:.3g}, {d['etaB'] / er:.3g} ({d['ratio_DB']:.3g})")
                t.append(line)
            tab(["filter", "t=0", "t=100", "t=2000"], t)


def cpu():
    p = os.path.join(sf.RES, "cpu_log.jsonl")
    if not os.path.exists(p):
        return
    recs = [json.loads(l) for l in open(p)]
    P("### Compute log (CPU seconds per script run, single thread)\n")
    tab(["script", "CPU s", "wall s", "runs", "SVDs"], [[r["name"], r["cpu_s"], r["wall_s"], r.get("n_runs", ""), r.get("n_svd", "")] for r in recs])
    P(f"Total CPU: {sum(r['cpu_s'] for r in recs):.0f} s = {sum(r['cpu_s'] for r in recs) / 60:.1f} min\n")


if __name__ == "__main__":
    for fn in (e0, e1_twophase, e1_late, e1_sweep, e1_signal, e1_lownoise, e1_momentum, e1_n1, e2, e2_scale, e2_mdep, e3,
               e3_continue, e4, cpu):
        try:
            fn()
        except Exception as ex:           # keep going; report the problem in the output
            P(f"\n**[{fn.__name__} failed: {type(ex).__name__}: {ex}]**\n")
    with open(os.path.join(sf.RES, "tables.md"), "w") as fh:
        fh.write("\n".join(out) + "\n")
    print("wrote", os.path.join(sf.RES, "tables.md"), len(out), "lines")
