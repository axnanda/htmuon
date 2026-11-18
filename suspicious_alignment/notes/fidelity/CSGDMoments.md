# Fidelity note — `SuspiciousAlignment/CSGD/Moments.lean`

Module `SuspiciousAlignment.CSGD.Moments` (imports `Mathlib`, `SuspiciousAlignment.Defs` only).
Paper: Deng et al., *Suspicious Alignment of SGD* (arXiv:2601.11789v2), §6 "Constant Step Size SGD"
(tex 657–760), Appendix A.6 (tex 2292–2320 assumption restated, 2407–2456 proof of Theorem 16);
neighbouring lines used: Assumption 1 (tex 367–384), Lemma "Concentration at time t"
(tex 2135–2189), proof of Theorem 15 (tex 2337–2404).

State of the file: 2577 lines, compiles with no errors and no Lean warnings (20–50 s),
`scripts/leancheck --build SuspiciousAlignment.CSGD.Moments` succeeds, no
`sorry`/`admit`/`axiom`/`native_decide`; all 366 constants of the module (326 theorems) depend only
on `propext`, `Classical.choice`, `Quot.sound` (checked with a scratch file importing the module).

Layer: this file is the **exact finite-`d` core** (plus the measure-theoretic derivation of the
second-moment recursion, and the deterministic-equivalent form of the `lim_t`/`lim_d` interchange).
The object replacing `𝔼[θ_t]` is the ratio of expected energies
`Spec.thetaBarCSGD = 𝔼[s_t^𝒟] / 𝔼[s_t]`; the transfer `𝔼[θ_t] − thetaBarCSGD → 0` as `d → ∞`
(tex 2444–2447) belongs to the asymptotic layer and is **not** formalized here.

Definitions used from `Defs.lean`: `Spec.betaC`, `varrhoD`, `deltaC`, `tStar`, `secondMoment`,
`thetaInf`.  New auxiliary definitions (suffix `C`): `expEnergyC`, `statEnergyC`, `thetaBarCSGD`,
`initExcessC`, `contrC`, `wEnergyC`, `thetaSmallStep`, `etaGapC`; structures `Spec.CSGDStep`,
`Spec.CSGDAssumption`.  No definition of `Defs.lean` was found to be unfaithful.  (Remark:
`Spec.tStar` uses `Real.log`, i.e. `log |x|`; this silently repairs the paper's formula when
`1 − ηλ_1 < 0`, see G3.)

## 1. Table: paper item → Lean declaration

| Paper item (tex lines) | Lean declaration(s) | Status | Explanation |
|---|---|---|---|
| `β_i := ηκ_i²/(2λ_i − ηλ_i²)` (662, 750, 2314) | `Spec.betaC` (Defs); `Spec.betaC_den_pos`, `Spec.betaC_nonneg` | exact | For `0 < η < 2/λ_1` the denominator is `λ_i(2 − ηλ_i) > 0` and `β_i ≥ 0`. |
| "`β_i > 0`" (662, 750, 2148, 2314, 2413) | `Spec.betaC_pos_iff`, `Spec.betaC_pos`, `Spec.betaC_eq_zero_of_kap2_eq_zero` | hypotheses-added | `β_i > 0 ⟺ κ_i² > 0`. True for all `i` if `s_min = λ_min(Σ) > 0`; not implied by the paper's `Σ ⪰ 0`, `Tr Σ > 0` (G1). |
| `β_i` is the stationary second moment | `Spec.betaC_fixed_point`, `Spec.eq_betaC_of_fixed_point` | exact | Fixed point of `m ↦ (1−ηλ_i)² m + η²κ_i²`, unique when `ηλ_i ∉ {0, 2}`. |
| `ϱ_𝒟 := ∑_𝒟 (c_{i,0}² − β_i)` (662) | `Spec.varrhoD` (Defs); `Spec.CSGDAssumption.varrhoD_eq`, `.varrhoD_pos` | exact | `ϱ_𝒟 = ‖P^𝒟 x_0‖² − ∑_𝒟 β_i`, positive under Assumption 14. |
| `δ` (665, 2317) | `Spec.deltaC` (Defs); `Spec.CSGDStep.gapDen_pos`, `.deltaC_den_pos`, `.deltaC_eq`, `.deltaC_nonneg`, `.deltaC_pos_iff`, `.deltaC_pos` | exact | Under the step-size row the bracket `2(λ_k−λ_{k+1})/η − (λ_1²−λ_d²)` is `> 0` (this is exactly what the second entry of the `min` is for); `δ > 0 ⟺ s_max > 0`. |
| Assumption 14, step-size row (679, 2303) | `Spec.CSGDStep`; `Spec.cSGDStep_iff`, `Spec.etaGapC_lt_two_div_lam1`, `Spec.min_two_div_lam1_etaGapC`, `Spec.etaGapC_le_two_div_add` | exact | Stated literally with the `min`. The `min` is redundant: `2(λ_k−λ_{k+1})/(λ_1²−λ_d²) < 2/λ_1` always (G2). |
| Assumption 14, full (668–687, 2295–2311) | `Spec.CSGDAssumption` | exact | Fields `step`, `init_gt : ∀ i ∈ 𝒟, β_i < c_{i,0}²`, `varrho_gt : δ − ∑_𝒟 β_i < ϱ_𝒟`. Non-vacuity: `CSGDMoments.ex_assumption`, `CSGDMoments.ex3_assumption`, `LatePhaseCounterexample.assumption14`. |
| Consequences of Assumption 14 (not stated in the paper) | `Spec.CSGDStep.lt_stab`, `.one_sub_eta_lam1_mem`, `.eta_mul_add_lt_two`, `.one_sub_eta_lam_bulk_pos`, `.abs_dom_lt_bulk`, `.contrC_eq`, `.lamd_le_lam_mul`, `.betaC_le`, `.betaC_le_paper`, `.two_mul_sum_betaC_le_deltaC`, `.sum_betaC_lt_deltaC`; `Spec.CSGDAssumption.varrho_gt_iff`, `.deltaC_lt_normSqD`, `.logDen_pos`, `.one_lt_logArg`, `.log_logArg_pos` | extra | `1 − ηλ_1 ∈ (−1, 1)`; `η(λ_1+λ_{k+1}) < 2`; every dominant mode contracts strictly faster than every bulk mode, `|1−ηλ_i| < 1−ηλ_j` (`i ∈ 𝒟`, `j ∈ ℬ`); `β_i ≤ η s_max/λ_d`; `δ ≥ 2∑_𝒟 β_i`; the 2nd initialization condition is equivalent to `‖P^𝒟 x_0‖² > δ`; the argument of the log in `t*` is `> 1` (when `s_max > 0`). |
| `t*` of Theorem 15 (705, 2324): well-definedness | `Spec.tStar` (Defs); `Spec.CSGDAssumption.le_tStar_iff`, `.deltaC_lt_of_lt_tStar`, `.one_le_tStar_iff`; `CSGDMoments.ex_one_sub_eta_lam1_neg`, `CSGDMoments.ex_tStar_eq_zero` | hypotheses-added / paper-claim-false (well-definedness) | `t ≤ t* ⟺ δ ≤ (1−ηλ_1)^{2t} ϱ_𝒟 + ∑_𝒟 β_i` (needs `s_max > 0`); for `t < t*` the inequality is strict (tex 2372–2375). Assumption 14 allows `1 − ηλ_1 ≤ 0`, where the paper's `log(1−ηλ_1)` is not real (G3), and allows `t* = 0` (G4). |
| Proof of Theorem 15, tex 2369–2370: `lim 𝔼[∑_𝒟 c_{i,t}²] = (1−ηλ_1)^{2t} ϱ_𝒟 + ∑_𝒟 β_i` | `Spec.CSGDAssumption.le_sum_secondMoment_D`; `Spec.CSGDAssumption.sum_secondMoment_D_lt`, `CSGDMoments.ex3_lower_bound_fails` | hypotheses-added; paper-claim-false in general | It is an inequality `≥`, valid when `ηλ_1 ≤ 1`; reversed for all `t ≥ 1` in a concrete instance satisfying Assumption 14 with `ηλ_1 = 5/4` (G5). (Theorem 15 itself is the next file.) |
| Proof of Thm 16, closed form `𝔼[c_{i,t}²] = (1−ηλ_i)^{2t}(c_{i,0}²−β_i)+β_i` (2423–2427; 2152–2163) | `Spec.secondMoment` (Defs); `Spec.secondMoment_zero`, `Spec.secondMoment_succ`, `Spec.eq_secondMoment_of_recursion`, `Spec.eq_secondMoment_of_recursion'`, `Spec.secondMoment_eq_mean_add_var`; probability layer `csgd_integral_step_sq`, `csgd_integral_sq_eq_secondMoment` | exact | Algebraic: any sequence with `m_0 = c_{i,0}²`, `m_{t+1} = (1−ηλ_i)² m_t + η²κ_i²` equals the closed form, provided `2λ_i − ηλ_i² ≠ 0` (true for `0 < η < 2/λ_1`; necessity: `Spec.secondMoment_ne_of_den_eq_zero`). Probability: the recursion is derived from `c_{t+1} = (1−ηλ)c_t − ηζ_t` for centred `L²` noise independent of `c_t` (Gaussianity not needed). |
| `|1−ηλ_i| < 1` for all `i` (2428) | `Spec.abs_one_sub_eta_lam_lt_one` | exact | Needs only `0 < η < 2/λ_1`. |
| `lim_t 𝔼[c_{i,t}²] = β_i` (2428–2431) | `Spec.tendsto_secondMoment`; rate `Spec.abs_secondMoment_sub_betaC_le` | exact | `Filter.Tendsto … atTop (𝓝 β_i)`. |
| `𝔼[s_t^𝒟] = ∑_𝒟 λ_i² 𝔼[c_{i,t}²]`, `𝔼[s_t] = ∑ λ_i² 𝔼[c_{i,t}²]` (2433–2437) | `Spec.expEnergyC`; `csgd_integral_mom` | exact | `∫ mom S 2 (c_t) = expEnergyC S t` on a probability space. |
| `lim_t 𝔼[s_t^S] = ∑_S λ_i² β_i` (2438–2442) | `Spec.tendsto_expEnergyC`; rate `Spec.abs_expEnergyC_sub_statEnergyC_le` | exact | For every block `S`. |
| **Theorem 16**, finite-`d` core: `lim_t 𝔼[s_t^𝒟]/𝔼[s_t] = θ_∞` (744–749, 2444–2453) | `Spec.tendsto_thetaBarCSGD`, `Spec.CSGDAssumption.tendsto_thetaBarCSGD`, `csgd_tendsto_ratio_expected_energies`; rate `Spec.abs_thetaBarCSGD_sub_thetaInf_le`, `Spec.CSGDAssumption.abs_thetaBarCSGD_sub_thetaInf_le` | weakened (finite `d`, ratio of expectations instead of `lim_d 𝔼[θ_t]`); hypothesis `∃ i, κ_i² > 0` explicit | Needs `0 < η < 2/λ_1` and non-zero noise (`⟺ Tr Σ > 0`, `Spec.exists_kap2_pos_iff_trace_pos`); the initialization part of Assumption 14 is not used. Necessity of non-zero noise: `CSGDMoments.ex'_not_tendsto`. |
| Theorem 16, "Equivalently" display (751–753) | `Spec.thetaInf_eq_equivalently`; also `Spec.thetaInf_eq_wEnergyC` | exact | Pure rewriting (finite `d`); `θ_∞ = A_𝒟/(A_𝒟+A_ℬ)` with `A_S = ∑_S λ_iκ_i²/(2−ηλ_i)`. |
| Theorem 16, `d → ∞` display: ratio of limits of unnormalised sums (747–749) | `Spec.statEnergyC_le_trace`, `Spec.trace_le_statEnergyC`, `Spec.card_mul_smin_le_trace`, `Spec.card_mul_smin_le_statEnergyC` | not-formalized as stated (ill-posed); supporting bounds proved | `(ηλ_d/2) Tr_S Σ ≤ ∑_S λ_i²β_i ≤ (ηλ_1/(2−ηλ_1)) Tr_S Σ`; `d·s_min ≤ Tr Σ`. See G6. |
| Proof of Thm 16, tex 2448: "convergence uniform in `i` ⇒ interchange `lim_t`/`lim_d`" | `LatePhaseCounterexample.late_phase_interchange_fails` (with `.assumption14`, `.rho_eq_one`, `.blockMoments`, `.trace_eq_one`, `.secondMoment_le_one`, `.statEnergyC_D`, `.statEnergyC_univ`, `.thetaInf_eq`, `.tendsto_thetaBar`, `.tendsto_L`) | paper-claim-false | Family satisfying Assumptions 1 and 14 literally with `lim_t lim_d = 0 ≠ 7/10 =` RHS of Theorem 16 (G7). |
| Theorem 16, corrected asymptotic form (deterministic-equivalent level) | `late_phase_interchange`, `late_phase_interchange_of_extensive_noise` | hypotheses-added | Interchange holds under uniform contraction and *uniform domination* `∑λ_i²|c_{i,0}²−β_i| ≤ C ∑λ_i²β_i`; in particular in the extensive-noise regime `s_min ≥ s > 0`, `λ_d ≥ λ_min > 0`, `ηλ_1 ≤ ηΛ < 2`, `‖x_0‖² ≤ M d`. |
| Interpretation (756–759): isotropic noise, `η ≪ 1`: `θ_∞ ≈ ∑_𝒟 λ_i/∑ λ_i` | `Spec.tendsto_thetaInf_isotropic`, `Spec.thetaInf_isotropic_bounds`, `Spec.thetaInf_isotropic`, `Spec.thetaSmallStep_isotropic`; general noise: `Spec.thetaSmallStep`, `Spec.tendsto_thetaInf_zero`, `Spec.thetaSmallStep_le_thetaInf`, `Spec.thetaInf_sub_le`, `Spec.thetaInf_sub_le_quarter` | exact (finite `d`, as a limit `η → 0⁺`) + strengthened (two-sided quantitative bound) | `0 ≤ θ_∞(η) − ∑_𝒟λ_i/∑λ_i ≤ η(λ_1−λ_d)/(4(2−ηλ_1))`; for general noise the limit is `∑_𝒟 λ_iκ_i²/∑λ_iκ_i²` and `θ_∞ − θ_0 ≤ θ_0(1−θ_0)·η(λ_1−λ_d)/(2−ηλ_1)` (G8). The `lim_{d→∞}` in the paper's display is not formalized. |
| Interpretation (760): `θ_∞ → 1` as `λ_k/λ_{k+1} → ∞` "while the bulk spectrum remains bounded away from zero" | `Spec.one_sub_thetaInf`, `Spec.one_sub_thetaInf_le`, `Spec.one_sub_thetaInf_le_div_mRatio`, `Spec.noise_trace_ratio_le`, `Spec.one_sub_thetaInf_le_cond`, `Spec.thetaInf_ge_gap_form`, `thetaInf_tendsto_one_uniform`, `tendsto_thetaInf_one_of_gap`; necessity `Spec.thetaInf_eq_zero_of_noise_bulk_only`; step-size interaction `Spec.eta_mul_mRatio_mul_lamk1_lt_two`, `Spec.eta_lt_of_bulk_bounded_below`, `csgd_tendsto_eta_zero_of_gap` | hypotheses-added (noise condition) / strengthened (explicit uniform bound) | `1 − θ_∞ ≤ (Tr_ℬΣ/Tr_𝒟Σ)·(λ_{k+1}/λ_k)·(2−ηλ_k)/(2−ηλ_{k+1}) ≤ (Tr_ℬΣ/Tr_𝒟Σ)/m ≤ (s_max/s_min)(1/ρ)(1/m)`. What must stay bounded is the noise-trace ratio, not the bulk spectrum (G9). |
| `0 ≤ θ_∞ ≤ 1`, `0 ≤ thetaBarCSGD ≤ 1`, `thetaBarCSGD 0 = θ(x_0)` | `Spec.thetaInf_nonneg`, `Spec.thetaInf_le_one`, `Spec.thetaBarCSGD_nonneg`, `Spec.thetaBarCSGD_le_one`, `Spec.thetaBarCSGD_zero` | extra | sanity lemmas |
| Theorem 15 statement (702–711) | — | not-formalized (here) | Next file; this module provides `CSGDAssumption`, the `t*` characterisation and the second-moment bounds it needs. |
| tex 2444–2447: `lim_d 𝔼[θ_t] = lim_d 𝔼[s_t^𝒟] / lim_d 𝔼[s_t]` (concentration) | — | not-formalized (here) | Asymptotic/probability layer. Note the display must use the normalised sums `s^𝒟/k`, `s/d` and needs a positive limit of the denominator. |

## 2. Gaps and errors found in the source

**G1. `β_i > 0` is asserted but needs `κ_i² > 0`.**  `β_i = ηκ_i²/(λ_i(2−ηλ_i))`; for
`0 < η < 2/λ_1` one has `β_i ≥ 0` and `β_i > 0 ⟺ κ_i² = u_iᵀΣu_i > 0` (`Spec.betaC_pos_iff`).
The paper only assumes `Σ ⪰ 0` (tex 353) and `Tr Σ ∈ (0, ∞)` (Assumption 1), which allows
`κ_i² = 0` for some `i`; `s_min > 0` suffices (`Spec.betaC_pos`).  Nothing in Theorem 16 needs
`β_i > 0` for every `i`; what is needed is `∑_i λ_i²β_i > 0`, i.e. `κ_i² > 0` for *some* `i`
(`Spec.statEnergyC_pos_iff`), which is `Tr Σ > 0`.  With zero noise the ratio of expected energies
need not converge to `θ_∞` (`CSGDMoments.ex'_not_tendsto`: it is constantly `1`, `θ_∞ = 0/0`).

**G2. The `min` in Assumption 14 is redundant.**
`2(λ_k−λ_{k+1})/(λ_1²−λ_d²) < 2/λ_1` for every admissible spectrum, because
`λ_1(λ_k−λ_{k+1}) ≤ λ_1(λ_1−λ_d) < (λ_1−λ_d)(λ_1+λ_d)` (`Spec.etaGapC_lt_two_div_lam1`).  In fact
the step-size row gives the stronger `η(λ_1+λ_{k+1}) < 2` (`Spec.CSGDStep.eta_mul_add_lt_two`).

**G3. Assumption 14 does not make `t*` well defined: `log(1−ηλ_1)` may be the log of a
non-positive number.**  Signs under Assumption 14 with `s_max > 0`:
* `δ > 0` and its denominator is positive (`Spec.CSGDStep.deltaC_pos`);
* `δ − ∑_𝒟 β_i > 0`: not obvious and not addressed in the paper; it holds because
  `δ ≥ 2∑_𝒟 β_i` (`Spec.CSGDStep.two_mul_sum_betaC_le_deltaC`; uses `β_i ≤ ηs_max/λ_d`,
  `ψ_𝒟 ≥ kλ_k²`, `λ_1² ≥ 4λ_d(λ_k−λ_{k+1})`);
* `ϱ_𝒟 > 0` (first initialization condition) and `ϱ_𝒟/(δ−∑_𝒟β_i) > 1` (second), so the numerator
  `log(…) > 0` (`Spec.CSGDAssumption.one_lt_logArg`, `.log_logArg_pos`);
* the denominator `−2 log(1−ηλ_1)` is a positive real **only if `ηλ_1 < 1`**.  Assumption 14 gives
  `ηλ_1 < 2λ_1(λ_k−λ_{k+1})/(λ_1²−λ_d²)`, which exceeds `1` whenever
  `2λ_1(λ_k−λ_{k+1}) > λ_1²−λ_d²`.  Concrete instance (`CSGDMoments.ex_one_sub_eta_lam1_neg`):
  `λ = (1, 1/2)`, `k = 1`, `Σ = I`, `η = 5/4 < min{2, 4/3}`, `x_0 = (10, 0)`: Assumption 14 holds
  (`β_1 = 5/3 < 100`, `δ = 80`, `ϱ_𝒟 = 100 − 5/3 > 80 − 5/3`) and `1 − ηλ_1 = −1/4`.
  For `ηλ_1 = 1` the formula contains `log 0`.

  Repair: read `log(1−ηλ_1)` as `log|1−ηλ_1|` (only `(1−ηλ_1)^{2t}` enters the proof).  Lean's
  `Real.log` is `log|·|` with `Real.log 0 = 0`, `x/0 = 0`, so `Spec.tStar` implements exactly this
  repair (and gives `t* = 0` when `ηλ_1 = 1`), and
  `Spec.CSGDAssumption.le_tStar_iff : t ≤ t* ⟺ δ ≤ (1−ηλ_1)^{2t}ϱ_𝒟 + ∑_𝒟β_i` holds for every step
  size allowed by Assumption 14.  The hypothesis `s_max > 0` is necessary for the formula to make
  sense (with `Σ = 0`: `δ = 0 = ∑β`, argument `ϱ/0`); it follows from `Tr Σ > 0`.

**G4. Under Assumption 14 the phase of Theorem 15 can be empty (`t* = 0`).**
`t* ≥ 1 ⟺ (1−ηλ_1)² ϱ_𝒟 ≥ δ − ∑_𝒟β_i` (`Spec.CSGDAssumption.one_le_tStar_iff`), whereas the
assumption only requires `ϱ_𝒟 > δ − ∑_𝒟β_i`.  In the instance of G3, `t* = 0`
(`CSGDMoments.ex_tStar_eq_zero`).  The Interpretation's "a positive-length phase is guaranteed when
the initial `ϱ_𝒟` exceeds a threshold" (tex 713) is right only for the larger threshold
`(δ−∑_𝒟β_i)/(1−ηλ_1)²`.

**G5. Proof of Theorem 15, tex 2369–2370: the displayed "`=`" is false, and the intended "`≥`" can
fail.**  `𝔼[∑_𝒟 c_{i,t}²] = ∑_𝒟 ((1−ηλ_i)^{2t}(c_{i,0}²−β_i)+β_i)`.  Replacing every
`(1−ηλ_i)^{2t}` by `(1−ηλ_1)^{2t}` gives a lower bound iff `|1−ηλ_1| ≤ |1−ηλ_i|` on `𝒟`, which
holds when `ηλ_1 ≤ 1` (`Spec.CSGDAssumption.le_sum_secondMoment_D`) but not in general.  Formal
counterexample (`CSGDMoments.ex3_lower_bound_fails`): `λ = (1, 4/5, 1/100)`, `k = 2`, `Σ = I`,
`η = 5/4` (`< 2·0.79/0.9999 ≈ 1.58`), `x_0 = (400, 400, 0)`; Assumption 14 holds
(`δ ≈ 9.70·10⁴ < 3.2·10⁵ = ‖P^𝒟x_0‖²`) and for all `t ≥ 1`
`𝔼[∑_𝒟 c_{i,t}²] < (1−ηλ_1)^{2t}ϱ_𝒟 + ∑_𝒟β_i` (here `1−ηλ_2 = 0` while `1−ηλ_1 = −1/4`).  A
random exact-rational search over instances satisfying Assumption 14 found the reversed inequality
at 797 sampled (instance, `t`) pairs with `ηλ_1 > 1` and at none of the 84 340 pairs with
`ηλ_1 ≤ 1`.  So the proof of Theorem 15 needs the extra hypothesis
`η ≤ 1/λ_1` (or `(1−ηλ_1)^{2t}` replaced by `min_{i∈𝒟}(1−ηλ_i)^{2t}` in `t*`).

Side remark (tex 2176, outside the assigned range): "`β_i ≤ ηs_max/(2λ_d−ηλ_d²)` since `λ_d > 0`
and `η < 2/λ_1`" is not justified by `η < 2/λ_1` alone (`x ↦ x(2−ηx)` is not monotone; e.g.
`λ = (1, 1/2)`, `η = 1.9`: `β_1 = 19κ²` but the bound is `≈ 3.6 s_max`).  It is true under
Assumption 14, because `η(λ_1+λ_d) < 2` makes `λ_d(2−ηλ_d)` the minimum of `λ_i(2−ηλ_i)`
(`Spec.CSGDStep.betaC_le_paper`); the file also proves the simpler `β_i ≤ ηs_max/λ_d`
(`Spec.CSGDStep.betaC_le`).

**G6. Theorem 16's display (a ratio of two `d → ∞` limits of unnormalised sums) is not well defined
under Assumption 1.**
* *Literal Assumption 1, "bounded trace" `Tr Σ ∈ (0,∞)`.*  Then
  `∑_i λ_i²β_i ≤ (ηλ_1/(2−ηλ_1)) Tr Σ` (`Spec.statEnergyC_le_trace`) stays bounded (given
  `sup_d ηλ_1 < 2`), and `s_min ≤ Tr Σ/d → 0` (`Spec.card_mul_smin_le_trace`): the noise per
  coordinate vanishes, `β_i = O(1/d)` on average.  The two limits need not exist (Assumption 1 only
  gives convergence of the polynomial block moments `(1/k)∑λ_i^p`, `p ∈ {2,3,4,6,8}`, while
  `λ_i²β_i = ηλ_iκ_i²/(2−ηλ_i)` involves `κ_i²` and a non-polynomial function of `λ_i`), the
  denominator limit may be `0` (only `≥ (ηλ_d/2) Tr Σ`, `Spec.trace_le_statEnergyC`, and
  Assumption 1 allows `λ_{ℬ,p} = 0`, i.e. `λ_d → 0`), and — decisively — even when both limits
  exist and are positive the claimed equality is false (G7).
* *The regime the paper actually simulates* (`quad_sim.py`: `Σ = σ²I`, `σ = 0.5`, `d = 500`, so
  `Tr Σ = 125 = σ²d`): `s_min` bounded below.  Then
  `∑_iλ_i²β_i ≥ (ηλ_d/2)·d·s_min → ∞` (`Spec.card_mul_smin_le_statEnergyC`) and likewise the
  `𝒟`-sum (as `k = ρd/(1+ρ) → ∞`): the display is `∞/∞`, and "bounded trace" is violated.
  The meaningful object is `lim_{d→∞} θ_∞(d)`, the limit of the *ratio* (equivalently of the sums
  normalised by `d`), whose existence is an additional assumption (e.g. joint convergence of the
  empirical distribution of `(λ_i, κ_i²)` on each block).
  Presumably "bounded trace" in Assumption 1 should read "`Tr Σ/d` bounded" (or `s_max` bounded,
  which is what the proof of the concentration lemma uses, tex 2176).

**G7. The interchange of `lim_t` and `lim_d` (tex 2448) is invalid; Theorem 16 is false as stated
under Assumptions 1 and 14.**  The paper argues: "the convergence `𝔼[c_{i,t}²] → β_i` is uniform in
`i` (bounded spectrum and noise). Therefore, we can interchange the limits".
* Uniformity in `i` (and `d`) needs `sup_d max_i|1−ηλ_i| < 1`, i.e. `λ_d(d) ≥ λ_min > 0` and
  `sup_d ηλ_1 < 2`, and a bound on `sup_i|c_{i,0}²−β_i|`; none of these is in Assumption 1 (which
  allows `λ_{ℬ,p} = 0` and bounds only the average `(1/d)∑c_{i,t}²`).
* More importantly, uniform convergence of the *summands* does not control the *ratio*: what is
  needed is that the convergence in `t` of `𝔼[s_t^𝒟]/𝔼[s_t]` is uniform in `d`.  The exact rate is
  `|𝔼[s_t^𝒟]/𝔼[s_t] − θ_∞| ≤ 2 r^{2t} ∑_iλ_i²|c_{i,0}²−β_i| / ∑_iλ_i²β_i`,
  `r = max(ηλ_1−1, 1−ηλ_d)` (`Spec.abs_thetaBarCSGD_sub_thetaInf_le`), which is uniform in `d`
  iff the initial excess energy is dominated by the stationary energy uniformly in `d`.
* **Counterexample** (`LatePhaseCounterexample.late_phase_interchange_fails`): `d = 2(n+1)`,
  `k = n+1` (`ρ = 1`), `λ_i = 2` on `𝒟`, `λ_i = 1` on `ℬ`, `Σ = I/d` (`Tr Σ = 1`), `c_{i,0} = 1`,
  `η = 1/4`.  Then Assumption 14 holds for every `n` (`η < min{1, 2/3}`, `β_i = 1/(12d)` resp.
  `1/(7d) < 1`, `δ = 2/5 < n+1`), all items of Assumption 1 hold (`ρ = 1`; block moments `2^p` and
  `1`; `Tr Σ = 1`; `𝔼[c_{i,t}²] ≤ 1`), the unnormalised sums are *constant* in `d`
  (`∑_𝒟λ_i²β_i = 1/6`, `∑_iλ_i²β_i = 5/21`), so the right-hand side of Theorem 16 is the
  well-defined number `7/10`, and the convergence `𝔼[c_{i,t}²] → β_i` *is* uniform in `i` and `d`
  (rate `(3/4)^{2t}`).  Nevertheless for each fixed `t`
  `lim_{d→∞} 𝔼[s_t^𝒟]/𝔼[s_t] = L(t) = 4·4^{−t}/(4·4^{−t} + (9/16)^t)` and `lim_{t→∞} L(t) = 0 ≠ 7/10`.
  Mechanism: with bounded trace the noise floor `β_i = O(1/d)` disappears as `d → ∞` at fixed `t`,
  leaving the noise-free dynamics, in which (under Assumption 14, by
  `Spec.CSGDStep.abs_dom_lt_bulk`) the dominant block decays strictly faster than the bulk, so the
  alignment tends to `0` whenever the bulk carries a non-negligible share of `x_0`.  The phenomenon
  is therefore generic under the literal Assumption 1, not special to this family.
  Scope of the formal statement: it is at the level of the ratio of expected energies, which is
  what the paper's proof uses for `lim_d 𝔼[θ_t]` (tex 2444–2447).  That `𝔼[θ_t]` itself converges
  to `L(t)` follows from the paper's own concentration lemma (the normalised block sums have
  variance `O(1/d)` and positive limits); it is not formalized here, but a Monte-Carlo run agrees:
  `𝔼[θ_t]` at `t = 4, 8, 12, 20, 40` is `0.135, 0.008, 0.017, 0.490, 0.701` for `d = 20000`
  (and `0.225, 0.497, 0.665, 0.671, 0.692` for `d = 20`), against
  `L(t) = 0.135, 0.006, 0.000, 0.000, 0.000` and `θ_∞ = 0.7`.
* **Corrected statement** (`late_phase_interchange`): if `0 < η < 2/λ_1(d)`,
  `max(ηλ_1−1, 1−ηλ_d) ≤ r < 1`, `∑λ_i²β_i > 0` and
  `∑λ_i²|c_{i,0}²−β_i| ≤ C∑λ_i²β_i` for all `d`, and the inner limits
  `L(t) = lim_d 𝔼[s_t^𝒟]/𝔼[s_t]` and `θ = lim_d θ_∞(d)` exist, then `lim_t L(t) = θ`.
  `late_phase_interchange_of_extensive_noise` derives the domination from
  `λ_1 ≤ Λ`, `ηΛ < 2`, `λ_d ≥ λ_min > 0`, `s_min ≥ s > 0`, `‖x_0‖² ≤ M d`
  (with `C = 1 + 2MΛ²/(ηλ_min s)`); this is the paper's simulated regime and contradicts the
  literal "bounded trace".  Hypotheses are jointly satisfiable (e.g. the two-level family above
  with `Σ = I` instead of `I/d`: `Λ = 2`, `λ_min = s = M = 1`; or any constant family).

**G8. Interpretation, small step size.**  "`η ≪ 1`" must be read as `ηλ_1 ≪ 1`: the exact
statement is `0 ≤ θ_∞(η) − θ_0 ≤ θ_0(1−θ_0)·η(λ_1−λ_d)/(2−ηλ_1)` with
`θ_0 = ∑_𝒟λ_iκ_i²/∑_iλ_iκ_i²` (`Spec.thetaSmallStep_le_thetaInf`, `Spec.thetaInf_sub_le`); for
isotropic noise `θ_0 = ∑_𝒟λ_i/∑_iλ_i` (`Spec.thetaInf_isotropic_bounds`).  Two by-products the
paper does not mention: a finite step size always *increases* `θ_∞` above its `η → 0` value, and
`σ²` must be `≠ 0`.  The limits `lim_{d→∞}` of the unnormalised sums `∑_𝒟λ_i`, `∑_iλ_i` in the
paper's display are `∞/∞` under Assumption 1 (`(1/k)∑_𝒟λ_i²→λ_{𝒟,2} > 0` forces `∑_𝒟λ_i → ∞`
when the `λ_i` are bounded); only the limit of the ratio makes sense.

**G9. Interpretation, large gap.**  Proven: for `0 < η < 2/λ_1` and `Tr_𝒟Σ = ∑_𝒟κ_i² > 0`,
`1 − θ_∞ ≤ (Tr_ℬΣ/Tr_𝒟Σ)·(λ_{k+1}/λ_k)·(2−ηλ_k)/(2−ηλ_{k+1}) ≤ (Tr_ℬΣ/Tr_𝒟Σ)/m`, and with
`s_min > 0`: `θ_∞ ≥ 1/(1 + (s_max/s_min)(1/ρ)(λ_{k+1}/λ_k))` (`Spec.thetaInf_ge_gap_form`; compare
`g_gap`, where the square `(λ_{k+1}/λ_k)²` appears).  Consequently `θ_∞ → 1` as `m → ∞` uniformly
over all problems (any `d`, any spectrum, any admissible `η`) with a bounded noise-trace ratio
(`thetaInf_tendsto_one_uniform`, `tendsto_thetaInf_one_of_gap`).
* What must stay bounded is `Tr_ℬΣ/Tr_𝒟Σ` (for isotropic noise this is `(d−k)/k = 1/ρ`), i.e.
  `(s_max/s_min)/ρ`.  The claim is false without a noise condition: if the noise lives in the bulk
  only, `θ_∞ = 0` for every gap (`Spec.thetaInf_eq_zero_of_noise_bulk_only`).  The sentence follows
  the isotropic case in the paper, where the condition holds with `ρ` fixed.
* "The bulk spectrum remains bounded away from zero" is **not needed**.  It interacts with the
  step-size constraint: `η < 2/λ_1 ≤ 2/λ_k = 2/(mλ_{k+1})`, so `λ_{k+1} ≥ c > 0` and `m → ∞` force
  `η < 2/(mc) → 0` (`Spec.eta_lt_of_bulk_bounded_below`, `csgd_tendsto_eta_zero_of_gap`): a fixed
  `η` is incompatible with that regime, and the limit is necessarily a joint limit `m → ∞`,
  `η → 0` (harmless for our bound, which is uniform in `η`).  It also sits uneasily with
  Assumption 1: within one asymptotic family `λ_k² ≤ (1/k)∑_𝒟λ_i² → λ_{𝒟,2} < ∞` bounds `λ_k`, so
  `m → ∞` requires either `λ_{k+1} → 0` or a sequence of families whose dominant moments
  `λ_{𝒟,p}` diverge (this is the objection in the commented-out remark at tex 595); the order of
  the limits `d → ∞`, `m → ∞`, `η → 0` is left unspecified in the paper.

**G10. Minor.**  (i) Theorem 16 is stated "under Assumption 14" but only `0 < η < 2/λ_1` is used;
the initialization conditions are irrelevant for the late phase.  (ii) The closed form needs
`η ≠ 2/λ_i`; at `η = 2/λ_i` with `κ_i² ≠ 0` the second moment grows linearly
(`Spec.secondMoment_ne_of_den_eq_zero`) — excluded by `η < 2/λ_1`.  (iii) The first initialization
condition `c_{i,0}² > β_i` is used only for `ϱ_𝒟 > 0` and the term-wise comparison of G5; the second
is just `‖P^𝒟x_0‖² > δ` (`Spec.CSGDAssumption.varrho_gt_iff`).

## 3. Non-vacuity

* `Spec.CSGDAssumption`: three explicit instances (`CSGDMoments.ex_assumption`,
  `CSGDMoments.ex3_assumption`, `LatePhaseCounterexample.assumption14`), with non-zero noise.
* Hypotheses of the `Spec.*` theorems are `0 < η < 2/λ_1` (non-empty interval), `∃ i, 0 < κ_i²`,
  `0 < s_min`, `0 < ∑_𝒟κ_i²`, isotropy with `σ² > 0`: all satisfied e.g. by `CSGDMoments.exP`,
  `CSGDMoments.exN` (`Σ = I`).
* No statement relies on `x/0 = 0` except where this is the documented content
  (`Spec.lam_sq_mul_betaC`, `Spec.thetaInf_eq_equivalently` are identities valid with the same
  convention on both sides; `Spec.secondMoment_ne_of_den_eq_zero`, `CSGDMoments.ex'_not_tendsto`
  and the case `ηλ_1 = 1` of `le_tStar_iff` are explicitly about the degenerate cases).
* Probability-layer lemmas (`csgd_integral_*`, `csgd_tendsto_ratio_expected_energies`) assume, per
  coordinate, `ζ_{i,t} ∈ L²`, `𝔼ζ_{i,t} = 0`, `𝔼ζ_{i,t}² = κ_i²` and independence of `c_{i,t}` and
  `ζ_{i,t}`; satisfied by the paper's i.i.d. Gaussian noise (construction of such a process is in
  the probability-layer files, not here).

## 4. Numerical sanity checks (python, not part of the proof)

`scratchpad/csgd2/verify.py` (60 000 random admissible instances): closed form vs. recursion;
`δ/∑_𝒟β_i ≥ 6.77 (≥ 2)`; `max_𝒟|1−ηλ_i| < min_ℬ(1−ηλ_j)`; `θ_0 ≤ θ_∞ ≤ θ_0 + θ_0(1−θ_0)η(λ_1−λ_d)/(2−ηλ_1)`;
the three large-gap bounds; the trace sandwich; the geometric rate bound; the characterisation of
`t*` with `log|1−ηλ_1|` (55 354 instances, 0 violations; 3 237 instances had `ηλ_1 > 1`).
`verify2.py` (exact rationals): G5 in both directions.  `sim.py`: Monte-Carlo of G7.

## 5. Suggestions for downstream files

* Theorem 15: import this module; use `Spec.CSGDAssumption`, `Spec.CSGDAssumption.le_tStar_iff`,
  `.deltaC_lt_of_lt_tStar`, `.le_sum_secondMoment_D` (needs `ηλ_1 ≤ 1`, see G5),
  `Spec.CSGDStep.deltaC_eq`/`.gapDen_pos`, and `csgd_integral_sq_eq_secondMoment`.
* Asymptotic layer for Theorem 16: combine concentration of the normalised block sums with
  `late_phase_interchange(_of_extensive_noise)`; state the result for `lim_d θ_∞(d)` in the
  extensive-noise regime, not for the ratio of limits of unnormalised sums.
* The file is long (2577 lines); if a split is wanted, natural pieces are: moments + Theorem 16 core
  (to "Interchange"), Interpretation, Assumption 14 + `t*`, examples/counterexamples.
