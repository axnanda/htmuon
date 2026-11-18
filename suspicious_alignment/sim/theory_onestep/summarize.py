"""Collects the maximal discrepancies of all validation scripts into results/summary.json and prints them."""
import json
import os

R = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
L = lambda n: json.load(open(os.path.join(R, n)))
out = {}

c = L("m2_commuting.json")["checks"]
out["C1_filters"] = c["C1_filters"]
pf = c["C2_C5_random_commuting_states"]["per_filter_max_discrepancy"]
keys = sorted({k for v in pf.values() for k in v})
out["C2_C5_max_over_filters"] = {k: max(v.get(k, 0) for v in pf.values()) for k in keys}
out["C2_C5_n_states"] = c["C2_C5_random_commuting_states"]["n_states"]
out["C2_C5_sign_cases"] = c["C2_C5_random_commuting_states"]["sign_cases_counts"]
out["C6"] = c["C6_etastar_bounds_and_dichotomy"]
r7 = c["C7_two_level_theta_flip"]["rows"]
out["C7"] = dict(n_configs=len(r7), max_abs_dtheta_at_theta_flip=max(r["max_abs_dtheta_at_theta_flip"] for r in r7),
                 max_etastar_relerr=max(r["etastar_vs_2_over_nuD_plus_nuB_relerr"] for r in r7),
                 sign_violations=sum(r["sign_violations"] for r in r7))
out["C8"] = {k: dict(q=v["q"], p=v["p"], dec=v["frac_eta_with_decrease"], inc=v["frac_eta_with_increase"]) for k, v in c["C8_four_sign_cases_muon"].items()}

g = L("m2_general.json")["checks"]
out["G1_max"] = max(g["G1_gram_formulas_generic_states"]["max_discrepancy"].values())
out["G2_max"] = max(g["G2_muon_pinning_any_noise"].values())
out["G3"] = g["G3_muon_large_step_attraction"]
out["G4"] = g["G4_jensen_upper_bounds"]
out["G5_max"] = max(g["G5_sgd_rownorm_exact"].values())

p = L("projected.json")["checks"]
p1 = p["P1_coincidence_FP_vs_PF"]
out["P1_max_commuting_or_block_commuting_indexwise"] = max(v for k, v in p1.items() if (k.startswith("commuting") or k.startswith("block")) and "echelon" not in k)
out["P1_generic_range_nonSGD"] = [min(v for k, v in p1.items() if k.startswith("generic") and "sgd" not in k), max(v for k, v in p1.items() if k.startswith("generic") and "sgd" not in k)]
out["P1_echelon_commuting"] = {k: v for k, v in p1.items() if "echelon" in k}
out["P2_max"] = max(p["P2_loss_identity_generic"].values())
p3 = p["P3_commuting_thresholds"]
out["P3"] = dict(max_formula_relerr=max(v for k, v in p3.items() if k.endswith("relerr")), window_tests=p3["window_tests"],
                 window_violations=p3["window_violations"], Splus_tests=p3["Splus_tests"], Splus_violations=p3["Splus_violations"])
out["P4_max"] = max(p["P4_additivity"].values())
out["P5"] = {k: v for k, v in p["P5_two_level_window_ratio"].items() if k != "rows"}
out["P6"] = p["P6_echelon_two_notions"]
p7 = p["P7_model_M1"]
out["P7"] = dict(max_relerr=max(v for k, v in p7.items() if isinstance(v, float)), tests=p7["tests"], violations=p7["crit_violations"])

m = L("m1.json")["checks"]
a1 = m["A1_noise_free"]
out["A1"] = dict(max=max(v for k, v in a1.items() if isinstance(v, float)), tests=a1["dichotomy_tests"], violations=a1["dichotomy_violations"])
a2 = m["A2_A3_spherical_noise"]
out["A2"] = {k: v for k, v in a2.items() if k != "rows"}
a4 = m["A4_meanfield_anisotropic"]["rows"]
out["A4_max_relerr_by_eps"] = {"eps<0.15": max(max(r["relerr_TD_TB_VD_VB"]) for r in a4 if r["eps_conc"] < 0.15),
                              "0.15<=eps<0.5": max(max(r["relerr_TD_TB_VD_VB"]) for r in a4 if 0.15 <= r["eps_conc"] < 0.5),
                              "eps>=0.5": max(max(r["relerr_TD_TB_VD_VB"]) for r in a4 if r["eps_conc"] >= 0.5)}
out["A5"] = m["A5_deng_thm8_counterexample"]

nz = L("m2_noise.json")["checks"]
out["N1_max"] = max(nz["N1_codiagonal_noise_per_realisation"].values())
out["N2"] = nz["N2_smoothed_filter_closed_forms"]
out["N3"] = dict(max_abs_z=nz["N3_codiagonal_noise_monte_carlo"]["max_abs_z"], NMC=nz["N3_codiagonal_noise_monte_carlo"]["NMC"],
                 max_relerr=max(max(r["relerr_sD"], r["relerr_sB"]) for r in nz["N3_codiagonal_noise_monte_carlo"]["rows"]))
out["N4"] = nz["N4_iid_noise_symmetry"]
out["N5"] = nz["N5_wide_limit"]["rows"]

q = L("noncommuting.json")["checks"]
out["Q1"] = [{k: r[k] for k in ("n", "filter", "T_relerr_median", "T_relerr_max", "V_relerr_median", "etastar_relerr_median",
                                 "dtheta_abserr_median", "dtheta_abserr_max", "sign_agreement", "q_sign_agreement", "threshold_order_agreement")}
             for r in q["Q1_M2_generic_states"]["rows"]]
out["Q2a_max"] = max(q["Q2_M3"]["a_left_commuting"].values())
out["Q2b_max"] = max(q["Q2_M3"]["b_aligned"].values())
out["Q2c"] = q["Q2_M3"]["c_generic_rows"]
ex = L("extra.json")
out["E1_max"] = ex["E1_three_alignments_max_err"]
out["E2"] = ex["E2_M1_spherical_thresholds"]
out["E3_E4"] = ex["E3_E4_noise_dominated_regime"]
out["E5"] = ex["E5_noise_restores_deng_sign_muon"]["rows"]
out["E6_max"] = ex["E6_echelon_effective_curvature_max_err"]
gd = L("gap_dependence.json")
out["gap_slopes"] = gd["loglog_slope_window_ratio_vs_m"]
out["runtime_sec_total"] = sum(L(n)["runtime_sec"] for n in ("m2_commuting.json", "m2_general.json", "projected.json", "m1.json", "m2_noise.json", "noncommuting.json", "gap_dependence.json", "extra.json"))
json.dump(out, open(os.path.join(R, "summary.json"), "w"), indent=1)
for k, v in out.items():
    if k in ("Q1", "Q2c", "N5", "A5", "C2_C5_sign_cases", "N4", "E3_E4", "E5"):
        continue
    print(k, v)
