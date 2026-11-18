"""Markdown tables for notes/research/theory_longrun.md (reads results/*.json; writes results/tables.md).
Also checks the closed forms of the momentum mean field (H4) against the numerical Lyapunov solution."""
import json
import os

import numpy as np

from common import RES, _mom_stationary, mom_two_cycle_const, mom_xcrit

class Blocks(list):
    """A list of lines that also files every added line under the current block name."""

    def __init__(self):
        super().__init__()
        self.blocks, self.cur = {}, None

    def start(self, name):
        self.cur = name
        self.blocks[name] = []

    def append(self, x):
        super().append(x)
        self.blocks[self.cur].append(x)

    def __iadd__(self, xs):
        for x in xs:
            self.append(x)
        return self


L = Blocks()


def load(name):
    return json.load(open(os.path.join(RES, name)))


def f(x, nd=5):
    return f"{x:.{nd}f}"


def pm(v, nd=5):
    return f"{v[0]:.{nd}f} ± {v[1]:.{nd}f}"


def e(x):
    return f"{x:.2e}"


# ---------------------------------------------------------------- T1: SGD, authors' setup
d = load("exp1b_deng_setup_sgd.json")
L.start("T1")
L += ["### T1. SGD in the authors' setup (exp1b; d=500, k=50, eta=0.003, sigma=0.5, T=30000, 7 seeds)", "",
      "| m | Thm 16 | finite-T det. equiv. (window) | sum_D lam/sum lam | measured, ratio of avg energies | measured, time-avg of theta (authors) | within-run sd of theta | theta_min (seed mean) | argmin t (emp / det. equiv.) | t* (Thm 15) | init. assumption holds |",
      "|---|---|---|---|---|---|---|---|---|---|---|"]
for r in d["sgd"]:
    L.append(f"| {r['m']} | {f(r['pred_thm16'])} | {f(r['pred_finite_T_window'])} | {f(r['pred_small_eta'])} | {pm(r['meas_ratio'])} | "
             f"{pm(r['meas_authors_stat'])} | {f(r['within_run_std'],4)} | {e(r['theta_min'])} | {r['tmin_emp']} / {r['tmin_det']} | "
             f"{r['tstar_thm15']:.1f} | {'yes' if r['init_assumption'] else 'no (delta = %.0f > varrho_D = 50)' % r['delta']} |")
L.append("")

# ---------------------------------------------------------------- T2: M1 filters, authors' setup
d = load("exp1b_deng_setup_m1.json")
L.start("T2")
L += ["### T2. (M1) filtered updates in the authors' setup (exp1b; same spectrum/noise/seeds; eta_p = target * nu^(1-p), nu = sigma sqrt(d))", "",
      "| p | step | m | predicted (self-consistent, H1) | measured (ratio) | measured (time-avg) | eta_eff*lam_1 pred / meas | theta_min | argmin t |",
      "|---|---|---|---|---|---|---|---|---|"]
for r in d["rows"]:
    if r["m"] in (5, 20, 100, 500):
        L.append(f"| {r['p']} | {r['step']} | {r['m']} | {f(r['pred_selfconsistent'])} | {pm(r['meas_ratio'])} | {pm(r['meas_authors_stat'])} | "
                 f"{r['pred_etaeff_lam1']:.3f} / {r['meas_etaeff_lam1'][0]:.3f} | {e(r['theta_min'])} | {r['tmin_emp']} |")
err = max(abs(r["pred_selfconsistent"] - r["meas_ratio"][0]) for r in d["rows"] if r["step"] == "matched")
err2 = max(abs(r["pred_selfconsistent"] - r["meas_ratio"][0]) for r in d["rows"] if r["step"] == "large")
L += ["", f"Max |pred - meas(ratio)| over all 27 (p, m): matched step {err:.4f}, large step {err2:.4f}.", ""]

# ---------------------------------------------------------------- T3: noise-free commuting
d = load("exp2_commuting.json")
L.start("T3")
L += ["### T3. Noise-free commuting (M2): theta_inf predicted vs measured (exp2; d=500, k=50, eta=0.01, 8 seeds)", "",
      "| m | Muon pred psi_D/psi | Muon meas | HT 0.125 pred | HT 0.125 meas | HT 0.25 pred | HT 0.25 meas | HT 0.5: 1-pred | HT 0.5: 1-meas |",
      "|---|---|---|---|---|---|---|---|---|"]
ht = {(r["p"], r["m"]): r for r in d["ht"]}
for r in d["muon"]:
    m = r["m"]
    L.append(f"| {m} | {f(r['pred_psi'],6)} | {pm(r['meas_ratio'],6)} | {f(ht[(0.125,m)]['pred'],8)} | {f(ht[(0.125,m)]['meas'][0],8)} | "
             f"{f(ht[(0.25,m)]['pred'],8)} | {f(ht[(0.25,m)]['meas'][0],8)} | {e(ht[(0.5,m)]['one_minus_pred'])} | {e(ht[(0.5,m)]['one_minus_meas'])} |")
L.start("T3b")
L += ["", "Two-phase timing for HTMuon (seed-mean theta; initial row norms chi_100 ~ 10 +- 0.7):", "",
      "| p | m | theta_0 | theta_min | argmin t | T_D pred (a_0 = 10) | back within 1% at t | T_B pred |", "|---|---|---|---|---|---|---|---|"]
for r in d["ht"]:
    if r["m"] in (2, 10, 100, 500):
        L.append(f"| {r['p']} | {r['m']} | {f(r['theta0'],4)} | {e(r['theta_min'])} | {r['tmin']} | {r['TD_pred']:.0f} | {r['t_rise_99']} | {r['TB_pred']:.0f} |")
L.start("T3c")
L += ["", "Echelon(r), noise-free commuting (exp2):", "",
      "| r | m | pred (top-(r+1) eigen-directions, uniform phases) | measured | # active directions | theta_min during transient |", "|---|---|---|---|---|---|"]
for r in d["ech"]:
    if r["m"] in (2, 10, 100, 500):
        L.append(f"| {r['r']} | {r['m']} | {f(r['pred_uniform_phase'],6)} | {pm(r['meas'],6)} | {r['active'][0]:.1f} | {e(r['theta_min'])} |")
L.start("T3d")
L += ["", "Speed-up variants (idealised scalar ports; exp2 'variants', exp2b 'htmuon_ns_faithful'):", "",
      "| variant | m | measured theta_inf | Muon law psi_D/psi | HT(0.125) law |", "|---|---|---|---|---|"]
for r in d["variants"]:
    if r["m"] in (2, 10, 100, 500):
        L.append(f"| {r['kind']} | {r['m']} | {r['meas'][0]:.8f} | {r['pred_q2']:.8f} | {r['pred_q16_7']:.8f} |")
d2b = load("exp2b_momentum_scalar.json")
for r in d2b["htmuon_ns_faithful"]:
    if r["m"] in (2, 10, 100, 500):
        L.append(f"| htmuon_ns (NS5 polar x NS gram root, faithful scalar port) | {r['m']} | {r['meas'][0]:.8f} | - | {r['pred_q16_7']:.8f} |")
L.append("")

# ---------------------------------------------------------------- T4: Muon dip
d = load("exp2c_muon_dip.json")
L.start("T4")
L += ["### T4. Is there a phase I for Muon? (exp2c; exact scalar dynamics, d=500, k=50, eta=0.01)", "",
      "| m | psi_D/psi | equal init: theta_min | 7% spread: theta_min | 35% spread: theta_min | HT(0.125), equal init: theta_min | HT: argmin t | HT: rigorous T_D upper / T_B(k+1) lower |",
      "|---|---|---|---|---|---|---|---|"]
rows = d["rows"]
for m in [2, 5, 10, 20, 50, 100, 200, 500]:
    g = lambda opt, init: [r for r in rows if r["opt"] == opt and r["init"] == init and r["m"] == m][0]
    h = g("ht0.125", "equal")
    L.append(f"| {m} | {f(g('muon','equal')['psi_ratio'],6)} | {f(g('muon','equal')['theta_min'][0],6)} | {pm(g('muon','chi100')['theta_min'],4)} | "
             f"{pm(g('muon','chi4')['theta_min'],4)} | {e(h['theta_min'])} | {h['tmin']} | {h['TD_upper']:.0f} / {h['TB_lower']:.0f} |")
L.append("")

# ---------------------------------------------------------------- T5: momentum constants
L.start("T5")
L += ["### T5. Momentum: universal energy constant C(p, beta) = <b^2> (exp2b) vs closed form C_2 = x_c^(2-q)/4", "",
      "| p | beta | x_c(beta) | C_2 closed form | measured: min / mean / max over 5 initial conditions | detected periods |", "|---|---|---|---|---|---|"]
for r in d2b["universal"]:
    c2 = mom_two_cycle_const(r["p"], r["beta"]) if r["p"] > 0 else 0.25
    L.append(f"| {r['p']} | {r['beta']} | {mom_xcrit(r['beta']):.3f} | {c2:.6g}{' (mid-floor)' if r['p']==0 else ''} | {r['C_min']:.6g} / {r['C_mean']:.6g} / {r['C_max']:.6g} | {r['periods']} |")
L.start("T5b")
L += ["", "theta_inf with momentum 0.95 (commuting, d=500, k=50, 8 seeds):", "",
      "| p | m | pred sum_D lam^q/sum lam^q | measured | E_i/(eta lam_i)^q: mean (cv over directions) | theta_min |", "|---|---|---|---|---|---|"]
for r in d2b["momentum_theta"]:
    if r["m"] in (2, 10, 100, 500):
        L.append(f"| {r['p']} | {r['m']} | {r['pred']:.8f} | {r['meas'][0]:.8f} ± {r['meas'][1]:.1e} | {r['C_dir_mean']:.4g} ({r['C_dir_cv']:.2f}) | {e(r['theta_min'])} |")
L.append("")

# ---------------------------------------------------------------- T6: M1
d = load("exp3_m1_vector.json")
L.start("T6")
L += ["### T6. (M1) vector model (exp3; d=500, k=50, eta=0.01, 8 seeds)", "", "Noise-free:", "",
      "| p | m | theta_inf | share of u_1 | <|g|>/g* | <eta_eff lam_1> | theta_min | argmin t | first increase of theta (mean step) | criterion violations |",
      "|---|---|---|---|---|---|---|---|---|---|"]
for r in d["noise_free"]:
    if r["m"] in (2, 10, 100, 500):
        L.append(f"| {r['p']} | {r['m']} | {r['theta_inf'][0]:.10f} | {r['top1_share'][0]:.6f} | {r['mean_gnorm_over_pred'][0]:.4f} | {r['mean_etaeff_lam1'][0]:.3f} | "
                 f"{e(r['theta_min'])} | {r['tmin']} | {r['first_increase_step'][0]:.0f} | {r['criterion_violations']}/{r['criterion_checked']} |")
L.start("T6b")
L += ["", "With isotropic noise (nu = sigma sqrt(d), g* = (eta lam_1/2)^(1/(1-p))):", "",
      "| p | m | nu/g* | pred (self-consistent, H1) | measured (ratio) | Deng small-step | eta_eff*lam_1 pred / meas | share of u_1 pred / meas |", "|---|---|---|---|---|---|---|---|"]
for r in d["noisy"]:
    L.append(f"| {r['p']} | {r['m']} | {r['noise_rel']} | {f(r['pred_selfconsistent'])} | {pm(r['meas_ratio'])} | {f(r['deng_small_eta'])} | "
             f"{r['pred_etaeff_lam1']:.4f} / {r['meas_etaeff_lam1'][0]:.4f} | {r['top1_share_pred']:.4f} / {r['top1_share_meas'][0]:.4f} |")
L.append("")

# ---------------------------------------------------------------- T7: M2 noise
da, db = load("exp4_m2_noise_A.json"), load("exp4_m2_noise_B.json")
L.start("T7")
L += ["### T7. (M2) with noise, d=24, k=4, n=600, eta=0.01, 3 seeds (exp4)", "", "Noise sweep (part A):", "",
      "| m | chi_B | optimizer | measured | mean field | mean field (edge-corrected tau, Echelon) | E_D meas/pred | E_B meas/pred | Deng small-step | lam^q law |", "|---|---|---|---|---|---|---|---|---|---|"]
for r in da["rows"]:
    L.append(f"| {r['m']} | {r['chi_B']} | {r['opt']} | {pm(r['meas_ratio'])} | {f(r['pred_mf'])} | {f(r['pred_mf_edge']) if r['pred_mf_edge'] else '-'} | "
             f"{r['ED_meas_over_pred']:.3f} | {r['EB_meas_over_pred']:.3f} | {f(r['deng_small'])} | {f(r['lam_q'])} |")
L.start("T7b")
L += ["", "Gap sweep at chi_B = 0.1 (part B):", "",
      "| m | SGD meas / Thm 16 | Muon meas / MF | HT 0.125 meas / MF | HT 0.5 meas / MF | Ech 2 meas / MF | Ech 4 meas / MF(edge) | Ech 8 meas / MF(edge) | Deng small-step |", "|---|---|---|---|---|---|---|---|---|"]
for m in [2, 5, 10, 20, 50, 100, 200]:
    g = {r["opt"]: r for r in db["rows"] if r["m"] == m}
    c = lambda o, key="pred_mf": f"{g[o]['meas_ratio'][0]:.5f} / {g[o][key]:.5f}"
    L.append(f"| {m} | {c('sgd')} | {c('muon')} | {c('ht0.125')} | {c('ht0.5')} | {c('ech2')} | {c('ech4','pred_mf_edge')} | {c('ech8','pred_mf_edge')} | {f(g['muon']['deng_small'])} |")
L.append("")

# ---------------------------------------------------------------- T8: generic init
d5a, d5b, d5c, d5d = [load(f"exp5_generic_init_{x}.json") for x in "ABCD"]
L.start("T8")
L += ["### T8. Noise-free (M2), generic Gaussian initialisation (exp5)", "", "Muon (K-iteration, d=60, k=6, eta=0.01, 5 seeds):", "",
      "| n/d | m | thetabar_inf (2-step avg) | psi_D/psi | rigorous lower / upper bound | absorbed at step | Lbar/(eta^2 tr A) | tr Z^2/d | ||Z_DB||_F^2/k | theta_0 | theta_min before absorption | argmin t |",
      "|---|---|---|---|---|---|---|---|---|---|---|---|"]
for r in d5a["rows"]:
    L.append(f"| {r['n_over_d']} | {r['m']} | {r['thetabar'][0]:.6f} ± {r['thetabar'][1]:.1e} | {r['psi_ratio']:.6f} | {r['lower_bound']:.4f} / {r['upper_bound']:.6f} | "
             f"{r['absorb_time'][0]:.0f} | {r['Lbar_over_eta2trA'][0]:.4f} | {r['trZ2_over_d'][0]:.3f} | {r['ZDB_fro2_over_k'][0]:.3f} | {r['theta0'][0]:.4f} | "
             f"{r['theta_min_before_absorb'][0]:.4f} | {r['tmin'][0]:.0f} |")
L.start("T8b")
L += ["", "HTMuon (full matrix simulation, d=40, k=4, eta=0.01, T=4000, 3 seeds):", "",
      "| n | p | m | theta final | pred sum_D lam^q/sum lam^q | max abs err | ||K-K*||/||K*|| | theta_min | argmin t | T_D ~ | back within 1% at | T_B ~ |", "|---|---|---|---|---|---|---|---|---|---|---|---|"]
for r in d5b["rows"]:
    L.append(f"| {r['n']} | {r['p']} | {r['m']} | {r['theta_final'][0]:.8f} | {r['pred']:.8f} | {r['abs_err_theta']:.1e} | {r['rel_err_K']:.1e} | {e(r['theta_min'][0])} | "
             f"{r['tmin'][0]:.0f} | {r['TD_pred']:.0f} | {r['t_back_within_1pct'][0]:.0f} | {r['TB_pred']:.0f} |")
L.start("T8c")
L += ["", "Multipliers of the K-map at K* (finite differences, d=4, lam=(8,5,2,1)):", "", "| p | max abs error of the predicted Jacobian | range of m_ij |", "|---|---|---|"]
for r in d5b["jacobian"]:
    L.append(f"| {r['p']} | {r['max_abs_err_jacobian']:.1e} | [{r['multiplier_range'][0]:.4f}, {r['multiplier_range'][1]:.4f}] |")
L.start("T8d")
L += ["", "Echelon(r) (full matrix simulation, d=40, k=4, n=160, T=8000, 3 seeds):", "",
      "| r | m | theta (time avg, last 1000 steps) | pred top-(r+1), uniform phases | # active directions | energy share of top-(r+1) eigen-directions | theta_min |", "|---|---|---|---|---|---|---|"]
for r in d5c["rows"]:
    L.append(f"| {r['r']} | {r['m']} | {r['theta'][0]:.6f} ± {r['theta'][1]:.1e} | {r['pred_top_r1_uniform']:.6f} | {r['active'][0]:.1f} | {r['frac_energy_top_r1'][0]:.4f} | {e(r['theta_min'][0])} |")
L.start("T8e")
L += ["", "Tall matrices n < d (d=40, k=4, m=10, T=12000, 3 seeds):", "",
      "| n | optimizer | theta | pred (top-n eigen-directions, lam^q weights) | energy share of top-n eigen-directions | max rel. deviation of E_i from (eta lam_i/2)^q, i<=n |", "|---|---|---|---|---|---|"]
for r in d5d["rows"]:
    L.append(f"| {r['n']} | {r['opt']} | {r['theta'][0]:.6f} ± {r['theta'][1]:.1e} | {r['pred_top_n']:.6f} | {r['frac_energy_top_n'][0]:.6f} | {r['max_rel_dev_energy_from_floor']:.1e} |")
L.append("")

# ---------------------------------------------------------------- T9: momentum + noise, aspect ratio
d6, d6r = load("exp6_momentum_noise.json"), load("exp6_aspect_ratio.json")
L.start("T9")
L += ["### T9. (M2) with noise and momentum beta=0.95 (exp6; d=24, k=4, n=600, eta=0.01, 3 seeds)", "",
      "| m | chi_B | optimizer | measured | MF with momentum (H4) | MF without momentum (H2) | E_D meas/H4 | E_B meas/H4 | Deng small-step |", "|---|---|---|---|---|---|---|---|---|"]
for r in d6["rows"]:
    h4 = f(r['pred_mf_momentum']) + (" (Muon law, not an Echelon prediction)" if r["opt"].startswith("ech") else "")
    L.append(f"| {r['m']} | {r['chi_B']} | {r['opt']} | {pm(r['meas'])} | {h4} | {f(r['pred_mf_no_momentum'])} | {r['ED_meas_over_pred']:.3f} | {r['EB_meas_over_pred']:.3f} | {f(r['deng_small'])} |")
L.start("T9b")
L += ["", "Aspect ratio (no momentum, m=10):", "", "| n | d/n | chi_B | optimizer | measured | mean field | E_D meas/pred | E_B meas/pred |", "|---|---|---|---|---|---|---|---|"]
for r in d6r["rows"]:
    L.append(f"| {r['n']} | {r['d_over_n']:.2f} | {r['chi_B']} | {r['opt']} | {pm(r['meas'])} | {f(r['pred_mf'])} | {r['ED_meas_over_pred']:.3f} | {r['EB_meas_over_pred']:.3f} |")
L.append("")


# ---------------------------------------------------------------- closed forms of H4
def Phi(x, b):
    return x * ((1 + b) + x * b * (1 - b) * (1 + 2 * b)) / ((1 + x * b) * (2 * (1 + b) - x * (1 - b) * (1 + 2 * b)))


worst = 0.0
for b in [0.0, 0.5, 0.9, 0.95]:
    for x in [0.01, 0.3, 1.0, 5.0, 0.9 * mom_xcrit(b)]:
        if x >= mom_xcrit(b):
            continue
        lam_, nu_ = 3.7, 0.9
        st = _mom_stationary(lam_, x / lam_, nu_, b)
        E_num, g2_num = lam_ ** 2 * st[0], st[1]
        E_cf = nu_ ** 2 * Phi(x, b)
        g2_cf = 2 * (1 - b) * nu_ ** 2 * (Phi(x, b) / x + b * (1 - b ** 2)) / (1 + b - x * b * (1 - b))
        worst = max(worst, abs(E_cf / E_num - 1), abs(g2_cf / g2_num - 1))
L.start("T9c")
L += [f"Closed forms of (H4) (Phi_beta and g^2) vs numerical Lyapunov solution: max relative error {worst:.1e}.", ""]
print(f"closed-form check of H4: max rel err {worst:.2e}")

open(os.path.join(RES, "tables.md"), "w").write("\n".join(L))
json.dump({k: "\n".join(v).strip("\n") for k, v in L.blocks.items()}, open(os.path.join(RES, "tables.json"), "w"), indent=1)
print("wrote results/tables.md,", len(L), "lines")
