"""Figures for notes/research/sim_exact_filters.md  (PNG, dpi 130, written to figs/).
Usage:  python3 make_figures.py [name ...]     (no argument: all figures whose inputs exist)
"""
import json
import os
import sys

import numpy as np

import specfilt as sf
import plotstyle as ps
from plotstyle import plt

ps.setup()
OPTS = ["sgd", "muon", "ht0.125", "ht0.25", "ht0.5", "ech1", "ech10", "ech20", "ech40"]
CORE = ["sgd", "muon", "ht0.125", "ht0.5", "ech1", "ech20"]
R = sf.RES


def jl(name):
    return json.load(open(os.path.join(R, name)))


def save(fig, name):
    os.makedirs(sf.FIG, exist_ok=True)
    p = os.path.join(sf.FIG, name)
    fig.savefig(p)
    plt.close(fig)
    print("wrote", p)


def ref(ax, y, text, x=0.01, va="bottom"):
    ax.axhline(y, color=ps.MUTED, lw=1.0, ls=(0, (1, 2)))
    ax.text(x, y, " " + text, transform=ax.get_yaxis_transform(), color=ps.INK2, fontsize=7.5, va=va)


# ---------------------------------------------------------------------------------------------
def fig_e0():
    j = jl("e0_baseline.json")
    c = np.load(os.path.join(R, "e0_baseline_curves.npz"))
    t = c["t"]
    fig, axs = plt.subplots(1, 3, figsize=(13.5, 3.9))
    ms = [5, 20, 100, 500]
    for m, col in zip(ms, ps.BLUE_RAMP[::1][1:5]):
        axs[0].plot(t + 1, c[f"dense_m{m}_theta"], color=col, lw=1.6, label=f"m = {m}")
        axs[0].plot(t + 1, c[f"theory_m{m}_theta_bar"], color=ps.INK, lw=0.9, ls=(0, (4, 2)),
                    label="exact ratio of expectations" if m == 5 else None)
        axs[1].plot(t + 1, c[f"dense_m{m}_loss"], color=col, lw=1.6, label=f"m = {m}")
    axs[0].set_xscale("log")
    axs[0].set_xlabel("step t + 1")
    axs[0].set_ylabel("alignment θ_t (true gradient)")
    axs[0].set_title("Two-phase alignment, SGD (literal port, seed 42)")
    axs[0].legend(loc="lower left")
    axs[1].set_xscale("log")
    axs[1].set_yscale("log")
    axs[1].set_xlabel("step t + 1")
    axs[1].set_ylabel("loss")
    axs[1].set_title("Loss")
    axs[1].legend(loc="lower left")
    tb = j["table"]
    mm = np.array([r["m"] for r in tb])
    axs[2].errorbar(mm, [r["E_align_mean"] for r in tb], yerr=[r["E_align_sd"] for r in tb], color=ps.BLUE, marker="o",
                    mec=ps.SURFACE, capsize=2, label="simulation, 7 seeds (mean ± sd)")
    axs[2].plot(mm, [r["theta_inf"] for r in tb], color=ps.INK, lw=1.2, ls=(0, (4, 2)), label="Theorem 16  θ∞")
    axs[2].plot(mm, [r["ratio1"] for r in tb], color=ps.ORANGE, lw=1.4, ls=":", label="Σ_D λ / Σ λ")
    axs[2].plot(mm, [r["ratio2"] for r in tb], color=ps.AQUA, lw=1.4, ls="-.", label="Σ_D λ² / Σ λ²")
    axs[2].set_xscale("log")
    axs[2].set_xlabel("spectral gap m = λ_k / λ_{k+1}")
    axs[2].set_ylabel("E[Alignment], last 10 000 steps")
    axs[2].set_title("Late-time alignment versus m")
    axs[2].legend(loc="lower right")
    save(fig, "e0_baseline.png")


def _logs(tags):
    rows, L = [], {}
    for tag in tags:
        rows += jl(f"e1_{tag}.json")["rows"]
        z = np.load(os.path.join(R, f"e1_{tag}_logs.npz"))
        L.update({k_: z[k_] for k_ in z.files})
    return rows, L


def fig_twophase():
    rows, L = _logs(["twophase_a", "twophase_b"])
    ms = [5, 20, 100, 500]
    fig, axs = plt.subplots(3, 4, figsize=(15, 9.2), sharex=True)
    for jx, m in enumerate(ms):
        for o in OPTS:
            r = [r for r in rows if r["m"] == m and r["opt"] == o][0]
            t = L[r["rid"] + "__t"] + 1
            ps.line(axs[0, jx], t, np.nanmean(L[r["rid"] + "__theta"], 0), o, lw=1.7)
            ps.line(axs[1, jx], t, np.nanmean(L[r["rid"] + "__loss"], 0), o, lw=1.7)
            ps.line(axs[2, jx], t[:-1], L[r["rid"] + "__upd_frac"][:-1], o, lw=1.5)
        s = [r for r in rows if r["m"] == m and r["opt"] == "sgd"][0]
        ref(axs[0, jx], s["ratio1"], "Σ_D λ / Σ λ", va="top")
        ref(axs[0, jx], s["ratio2"], "Σ_D λ² / Σ λ²")
        ref(axs[2, jx], 0.1, "k/d (pure noise)")
        axs[0, jx].set_title(f"m = {m}")
        axs[1, jx].set_yscale("log")
        axs[2, jx].set_xlabel("step t + 1")
        for a in axs[:, jx]:
            a.set_xscale("log")
    axs[0, 0].set_ylabel("alignment θ_t (true gradient)")
    axs[1, 0].set_ylabel("loss")
    axs[2, 0].set_ylabel("fraction of ‖update‖² in D")
    ps.legend_below(fig, axs[0, 0], ncol=5, y=0.06)
    fig.suptitle("E1: exact spectral filters vs SGD, left-Hessian lift (d=200, k=20, n=50, σ=0.5, W0~N(0,1), κ=1; mean of 3 seeds)",
                 y=0.93, fontsize=11)
    save(fig, "e1_twophase.png")


def fig_late():
    rows = jl("e1_late_a.json")["rows"] + jl("e1_late_b.json")["rows"]
    ms = sorted(set(r["m"] for r in rows))
    fig, axs = plt.subplots(1, 3, figsize=(15, 4.2))
    s = {m: [r for r in rows if r["m"] == m and r["opt"] == "sgd"][0] for m in ms}
    ax = axs[0]
    ax.plot(ms, [s[m]["ratio1"] for m in ms], color=ps.MUTED, lw=1.2, ls=":", label="Σ_D λ / Σ λ")
    ax.plot(ms, [s[m]["ratio2"] for m in ms], color=ps.MUTED, lw=1.2, ls="-.", label="Σ_D λ² / Σ λ²")
    ax.plot(ms, [s[m]["thm16_at_eta_eff"] for m in ms], color=ps.MUTED, lw=1.2, ls=(0, (4, 2)), label="Theorem 16 (η=0.003)")
    for o in OPTS:
        rr = [[r for r in rows if r["m"] == m and r["opt"] == o][0] for m in ms]
        ps.pts(ax, ms, [r["theta_late"] for r in rr], o, yerr=[r["theta_late_sd"] for r in rr], lw=1.0, ms=5)
    ax.set_xscale("log")
    ax.set_xlabel("m")
    ax.set_ylabel("late-time alignment θ")
    ax.set_title("Noise-dominated late phase (σ=0.5, κ=1)")
    ax = axs[1]
    for o in OPTS:
        rr = [[r for r in rows if r["m"] == m and r["opt"] == o][0] for m in ms]
        ps.pts(ax, ms, [r["theta_late"] - r["sgd_finiteT_at_eta_eff"] for r in rr], o, yerr=[r["theta_late_sd"] for r in rr],
               lw=1.0, ms=5)
    ax.axhline(0, color=ps.AXIS, lw=1)
    ax.set_xscale("log")
    ax.set_xlabel("m")
    ax.set_ylabel("θ_late − Deng finite-T formula at η_eff")
    ax.set_title("Deviation from the linear-response prediction")
    ax = axs[2]
    try:
        sig = jl("e1_signal.json")["rows"]
        m3 = [5, 20, 100]
        for o in OPTS:
            rr = [[r for r in sig if r["m"] == m and r["opt"] == o and r["sigma"] == 0.0][0] for m in m3]
            ps.pts(ax, m3, [1 - r["theta_late"] for r in rr], o, lw=1.0, ms=5)
        pr = [sf.Problem(200, 20, 50, m) for m in m3]
        ax.plot(m3, [1 - p.ratio(1) for p in pr], color=ps.MUTED, lw=1.2, ls=":")
        ax.plot(m3, [1 - p.ratio(2) for p in pr], color=ps.MUTED, lw=1.2, ls="-.")
        ax.set_yscale("log")
        ax.set_xscale("log")
        ax.set_xlabel("m")
        ax.set_ylabel("1 − θ_late")
        ax.set_title("Noise-free late phase (σ=0): 1 − θ")
    except Exception as ex:
        ax.set_title(f"(signal data missing: {ex})")
    h, l = axs[0].get_legend_handles_labels()
    fig.legend(h, l, loc="upper center", bbox_to_anchor=(0.5, 0.0), ncol=6, handlelength=3.2)
    save(fig, "e1_late_vs_m.png")


def fig_sweep():
    rows = jl("e1_sweep.json")["rows"] + [r for r in jl("e1_twophase_a.json")["rows"] if r["m"] == 20]
    ks = sorted(set(r["kappa"] for r in rows))
    fig, axs = plt.subplots(1, 4, figsize=(17, 3.9))
    keys = [("theta_late", "late alignment θ (true gradient)"), ("loss_late", "late loss"),
            ("upd_frac_late", "late fraction of ‖update‖² in D"), ("ovl_inp_late", "late overlap of top-k left s.-subspace of G with D")]
    for ax, (key, title) in zip(axs, keys):
        for o in OPTS:
            xs, ys = [], []
            for kp in ks:
                r = [r for r in rows if r["opt"] == o and r["kappa"] == kp]
                if r and not r[0]["diverged"]:
                    xs.append(kp)
                    ys.append(r[0][key])
            ps.pts(ax, xs, ys, o, lw=1.2, ms=5)
        ax.set_xscale("log", base=2)
        ax.set_xlabel("κ = η / η_rule")
        ax.set_title(title, fontsize=9.5)
    axs[1].set_yscale("log")
    p = sf.Problem(200, 20, 50, 20)
    ref(axs[0], p.ratio(1), "Σ_D λ / Σ λ", va="top")
    ref(axs[0], p.ratio(2), "Σ_D λ² / Σ λ²")
    ref(axs[2], 0.1, "k/d")
    ref(axs[3], 0.1, "k/d")
    ps.legend_below(fig, axs[0], ncol=9, y=0.02)
    fig.suptitle("E1 learning-rate sweep at m=20 (σ=0.5, W0~N(0,1), T=2000; SGD diverges for κ ≥ 8)", y=1.0, fontsize=11)
    save(fig, "e1_sweep.png")


def fig_diag():
    rows, L = _logs(["twophase_a"])
    fig, axs = plt.subplots(2, 3, figsize=(14.5, 7.2), sharex=True)
    meta = jl("e1_twophase_a.json")
    lo, hi = meta["noise_sv_edges"]
    for jx, o in enumerate(["sgd", "muon", "ht0.125"]):
        r = [r for r in rows if r["m"] == 20 and r["opt"] == o][0]
        t = L[r["rid"] + "__t"][:-1] + 1
        sv = L[r["rid"] + "__sv_inp"][:-1]
        svt = L[r["rid"] + "__sv_true"][:-1]
        ok = np.isfinite(svt[:, 0])
        ax = axs[0, jx]
        ax.plot(t, sv[:, 0], color=ps.BLUE, lw=1.6, label="filter input G: s_1")
        ax.plot(t, sv[:, 3], color=ps.BLUE, lw=1.6, ls="--", label="G: s_k")
        ax.plot(t, sv[:, 5], color=ps.BLUE, lw=1.6, ls=":", label="G: median")
        ax.plot(t[ok], svt[ok, 0], color=ps.ORANGE, lw=1.6, label="true gradient AW: s_1")
        ax.plot(t[ok], svt[ok, 3], color=ps.ORANGE, lw=1.6, ls="--", label="AW: s_k")
        ax.plot(t[ok], svt[ok, 5], color=ps.ORANGE, lw=1.6, ls=":", label="AW: median")
        ax.axhspan(lo, hi, color=ps.MUTED, alpha=0.12, lw=0)
        ax.text(1.2, hi * 1.08, "pure-noise singular values", color=ps.INK2, fontsize=7.5)
        ax.set_yscale("log")
        ax.set_xscale("log")
        ax.set_title(f"{ps.OPT_STYLE[o]['label']}: singular values (m=20)")
        ax = axs[1, jx]
        ax.plot(t, L[r["rid"] + "__theta"].mean(0)[:-1], color=ps.INK, lw=1.6, label="θ(AW)  (Deng's alignment)")
        ax.plot(t, L[r["rid"] + "__theta_stoch"][:-1], color=ps.BLUE, lw=1.6, ls="--", label="θ(G)  (stochastic gradient)")
        ax.plot(t, L[r["rid"] + "__upd_frac"][:-1], color=ps.ORANGE, lw=1.6, label="fraction of ‖update‖² in D")
        ax.plot(t, L[r["rid"] + "__ovl_inp"][:-1], color=ps.AQUA, lw=1.6, ls="-.", label="overlap_k(G) with D")
        ov = L[r["rid"] + "__ovl_true"][:-1]
        ax.plot(t[ok], ov[ok], color=ps.AQUA, lw=1.6, ls=":", label="overlap_k(AW) with D")
        ax.set_xlabel("step t + 1")
        ax.set_ylim(-0.02, 1.02)
    axs[0, 0].set_ylabel("singular value")
    axs[1, 0].set_ylabel("fraction / overlap")
    axs[0, 2].legend(loc="upper right", fontsize=7.5)
    axs[1, 2].legend(loc="center right", fontsize=7.5)
    save(fig, "e1_diagnostics_m20.png")


def fig_momentum():
    rows, L = _logs(["momentum"])
    fig, axs = plt.subplots(2, 2, figsize=(11.5, 7.0))
    panels = [("large", "drift-matched learning rate (T = 6000)"),
              ("nomomlr", "momentum-free learning rate (T = 2000)")]
    for jx, (tag, title) in enumerate(panels):
        rr = [r for r in rows if r.get("tag") == tag]
        for o in CORE:
            r = [r for r in rr if r["opt"] == o][0]
            t = L[r["rid"] + "__t"] + 1
            ps.line(axs[0, jx], t, np.nanmean(L[r["rid"] + "__theta"], 0), o, lw=1.7)
            ps.line(axs[1, jx], t, np.nanmean(L[r["rid"] + "__loss"], 0), o, lw=1.7)
        s = [r for r in rr if r["opt"] == "sgd"][0]
        ref(axs[0, jx], s["sgdmom_theta_inf_at_eta_eff"], "SGD + Nesterov, exact stationary (η = 0.003)", va="top")
        ref(axs[0, jx], s["thm16_at_eta_eff"], "Theorem 16 (no momentum, η = 0.003)")
        axs[0, jx].set_title(f"m = 20, Nesterov β = 0.95, {title}", fontsize=9.5)
        axs[1, jx].set_yscale("log")
        axs[1, jx].set_xlabel("step t + 1")
        for a in axs[:, jx]:
            a.set_xscale("log")
    axs[0, 0].set_ylabel("alignment θ_t (true gradient)")
    axs[1, 0].set_ylabel("loss")
    ps.legend_below(fig, axs[0, 0], ncol=6, y=0.04)
    save(fig, "e1_momentum.png")


def fig_n1():
    j = jl("e1_n1.json")
    c = np.load(os.path.join(R, "e1_n1_curves.npz"))
    t = c["t"] + 1
    o5 = ["sgd", "muon", "ht0.125", "ht0.25", "ht0.5"]
    fig, axs = plt.subplots(1, 3, figsize=(14.5, 3.9))
    for o in o5:
        ps.line(axs[0], t, c[f"proto_{o}_m20_k1.0__theta"], o, lw=1.6)
        ps.line(axs[1], t, c[f"free_{o}_m20_k1.0__theta"], o, lw=1.6)
    pr = [r for r in j["rows"] if r["group"] == "proto"]
    ms = sorted(set(r["m"] for r in pr))
    for o in o5:
        rr = [[r for r in pr if r["opt"] == o and r["m"] == m][0] for m in ms]
        ps.pts(axs[2], ms, [1 - r["E_align"] for r in rr], o, lw=1.0, ms=5)
    axs[2].plot(ms, [1 - [r for r in pr if r["opt"] == "sgd" and r["m"] == m][0]["thm16_at_eta_eff"] for m in ms],
                color=ps.MUTED, ls=(0, (4, 2)), lw=1.2, label="Theorem 16")
    for a in axs[:2]:
        a.set_xscale("log")
        a.set_xlabel("step t + 1")
    axs[0].set_title("n = 1, σ = 0.5, m = 20, κ = 1")
    axs[1].set_title("n = 1, noise-free, m = 20")
    axs[0].set_ylabel("alignment θ_t")
    axs[2].set_xscale("log")
    axs[2].set_yscale("log")
    axs[2].set_xlabel("m")
    axs[2].set_ylabel("1 − E[Alignment]")
    axs[2].set_title("n = 1: late-time alignment vs m (σ = 0.5)")
    axs[2].legend(fontsize=7.5)
    axs[0].legend(fontsize=7.5, loc="lower left")
    save(fig, "e1_n1.png")


def fig_e2():
    j = jl("e23_states.json")
    c = np.load(os.path.join(R, "e23_states_curves.npz"))
    fig, axs = plt.subplots(2, 4, figsize=(16.5, 7.4))
    sel = [0, 30, 400, 3000]
    for jx, tt in enumerate(sel):
        ax = axs[0, jx]
        st = [r for r in j["rows"] if r["traj"] == "sgd" and r["m"] == 20 and r["t"] == tt][0]
        ymax = 0
        for o in CORE:
            arr = c[f"sgd_m20_t{tt}__{o}"]
            nf = st["per_opt"][o]["nfac"]
            ps.line(ax, arr[0] * nf, arr[1], o, lw=1.6)
            ymax = max(ymax, np.nanmax(np.abs(arr[1][arr[0] * nf < 0.3])))
        ax.axhline(0, color=ps.AXIS, lw=1)
        ax.set_xscale("log")
        ax.set_yscale("symlog", linthresh=max(ymax * 1e-3, 1e-9))
        ax.set_xlim(1e-4, 3)
        ax.set_title(f"state: SGD trajectory, t = {tt} (θ = {st['theta']:.3f})", fontsize=9.5)
        ax.set_xlabel("norm-equalised step  η ‖F(G)‖/‖G‖")
    axs[0, 0].set_ylabel("E[θ(W − ηF(G))] − θ(W)   (symlog)")
    for jx, m in enumerate((20, 100)):
        ax = axs[1, jx]
        for o in CORE:
            rr = sorted([r for r in j["rows"] if r["traj"] == o and r["m"] == m], key=lambda r: r["t"])
            xs = [r["t"] + 1 for r in rr if r["per_opt"][o]["regime"] == "dec<inc"]
            ys = [r["per_opt"][o]["eta_star"] / r["per_opt"][o]["eta_run"] for r in rr if r["per_opt"][o]["regime"] == "dec<inc"]
            ps.pts(ax, xs, ys, o, lw=1.0, ms=5)
        ax.axhline(1, color=ps.INK2, lw=1)
        ax.text(1.1, 1.08, "running step", color=ps.INK2, fontsize=7.5)
        ax.set_xscale("log")
        ax.set_yscale("log")
        ax.set_xlabel("step t + 1 (own trajectory)")
        ax.set_title(f"critical step η* / running step, m = {m}\n(only states in the 'decrease below, increase above' regime)", fontsize=9)
    axs[1, 0].set_ylabel("η*_F / η_run")
    try:
        js = jl("e23_scale.json")
        for jx, step in enumerate((0, 100)):
            ax = axs[1, 2 + jx]
            rr = [r for r in js["rows"] if r["t"] == step and r["gamma"] != "noise-free"]
            for o in CORE:
                xs = [r["gnorm_true"] for r in rr if r["per_opt"][o]["regime"] == "dec<inc"]
                ys = [r["per_opt"][o]["eta_star"] for r in rr if r["per_opt"][o]["regime"] == "dec<inc"]
                ps.pts(ax, xs, ys, o, lw=1.0, ms=5)
            ax.set_xscale("log")
            ax.set_yscale("log")
            ax.set_xlabel("true gradient norm ‖A(γW)‖_F   (γ = 2^-6 … 2^8)")
            ax.set_title(f"critical step vs gradient norm\n(state: SGD trajectory t = {step}, m = 20, noise fixed)", fontsize=9)
        axs[1, 2].set_ylabel("η*_F (raw)")
    except Exception as ex:
        axs[1, 2].set_title(str(ex))
    fig.subplots_adjust(hspace=0.55, wspace=0.28)
    ps.legend_below(fig, axs[0, 0], ncol=6, y=0.03)
    save(fig, "e2_alignment_response.png")


def fig_e3():
    j = jl("e23_states.json")
    fig, axs = plt.subplots(2, 3, figsize=(15, 7.4), sharex=True)
    for jx, m in enumerate((20, 100, 500)):
        for o in CORE:
            rr = sorted([r for r in j["rows"] if r["traj"] == o and r["m"] == m], key=lambda r: r["t"])
            t = [r["t"] + 1 for r in rr]
            ps.line(axs[0, jx], t, [r["per_opt"][o]["etaD"] / r["per_opt"][o]["eta_run"] for r in rr], o, lw=1.6, marker="o", ms=3.5)
            ps.line(axs[1, jx], t, [r["per_opt"][o]["ratio_DB"] for r in rr], o, lw=1.6, marker="o", ms=3.5)
        for a in axs[:, jx]:
            a.set_xscale("log")
            a.set_yscale("log")
            a.axhline(1, color=ps.INK2, lw=1)
        axs[0, jx].set_title(f"m = {m}")
        axs[1, jx].set_xlabel("step t + 1 (own trajectory)")
    axs[0, 0].set_ylabel("η_D^loss / η_run   (<1: D-update raises loss)")
    axs[1, 0].set_ylabel("η_D^loss / η_B^loss   (>1: order reversed)")
    ps.legend_below(fig, axs[0, 0], ncol=6, y=0.04)
    save(fig, "e3_loss_thresholds.png")


def fig_e3c():
    j = jl("e3_continue.json")
    c = np.load(os.path.join(R, "e3_continue_curves.npz"))
    t = c["t"]
    cases = [(100, 400), (100, 2000), (500, 3000)]
    opts = ["sgd", "muon", "ht0.125", "ech20"]
    fig, axs = plt.subplots(len(cases), len(opts), figsize=(15, 9.5), sharex=True)
    sty = {"full": (ps.INK, "-", "full update"), "updD": (ps.ORANGE, "-", "P^D F(G)"), "updB": (ps.BLUE, "-", "P^B F(G)"),
           "gradD": (ps.ORANGE, ":", "F(P^D G)"), "gradB": (ps.BLUE, ":", "F(P^B G)")}
    for ix, (m, st) in enumerate(cases):
        for jx, o in enumerate(opts):
            ax = axs[ix, jx]
            r0 = [r for r in j["rows"] if r["m"] == m and r["t_ckpt"] == st and r["opt"] == o and r["variant"] == "full"][0]
            for v, (col, ls, lab) in sty.items():
                ax.plot(t, c[f"{o}_m{m}_t{st}__{v}"] / r0["L0"], color=col, ls=ls, lw=1.7, label=lab)
            ax.axhline(1, color=ps.AXIS, lw=1)
            ax.set_title(f"{ps.OPT_STYLE[o]['label']}; m={m}, t0={st}, θ={r0['theta0']:.2f}", fontsize=9)
            if ix == len(cases) - 1:
                ax.set_xlabel("steps after the checkpoint")
            if jx == 0:
                ax.set_ylabel("L(t0 + s) / L(t0)")
    ps.legend_below(fig, axs[0, 0], ncol=5, y=0.05)
    save(fig, "e3_continuation.png")


def fig_e4():
    fig, axs = plt.subplots(2, 3, figsize=(15, 7.4))
    o7 = ["sgd", "muon", "ht0.125", "ht0.5", "ech1", "ech20", "ech40"]
    panels = []
    try:
        ja = jl("e4_aniso.json")
        La = np.load(os.path.join(R, "e4_aniso_logs.npz"))
        for m in (20, 100):
            panels.append((ja, La, dict(m=m), f"anisotropic noise Σ ∝ A, m = {m}"))
    except Exception:
        pass
    try:
        jk = jl("e4_kron.json")
        Lk = np.load(os.path.join(R, "e4_kron_logs.npz"))
        for al, K in ((0.5, 1000), (1.0, 500)):
            for m in (20, 100):
                panels.append((jk, Lk, dict(m=m, mu_alpha=al, Kdom=K), f"Kronecker α = {al}, K = {K}, m = {m}"))
    except Exception:
        pass
    for ax, (j, L, sel, title) in zip(axs.ravel(), panels):
        rr = [r for r in j["rows"] if r["setting"] == "large" and all(r.get(k_) == v for k_, v in sel.items())]
        for o in o7:
            r = [r for r in rr if r["opt"] == o][0]
            ps.line(ax, L[r["rid"] + "__t"] + 1, np.nanmean(L[r["rid"] + "__theta"], 0), o, lw=1.6)
        s = rr[0]
        ref(ax, s["ratio1"], "Σ_D h / Σ h", va="top")
        ref(ax, s["ratio2"], "Σ_D h² / Σ h²")
        ax.set_xscale("log")
        ax.set_title(title, fontsize=9.5)
        ax.set_xlabel("step t + 1")
        ax.set_ylabel("alignment θ_t")
    fig.tight_layout()
    ps.legend_below(fig, axs[0, 0], ncol=7, y=0.0)
    save(fig, "e4_robustness.png")


FIGS = dict(e0=fig_e0, twophase=fig_twophase, late=fig_late, sweep=fig_sweep, diag=fig_diag, momentum=fig_momentum,
            n1=fig_n1, e2=fig_e2, e3=fig_e3, e3c=fig_e3c, e4=fig_e4)

if __name__ == "__main__":
    names = sys.argv[1:] or list(FIGS)
    for nm in names:
        try:
            FIGS[nm]()
        except FileNotFoundError as ex:
            print(f"[skip {nm}: missing {ex.filename}]")
