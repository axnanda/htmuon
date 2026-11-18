import Mathlib
import SuspiciousAlignment.Defs

/-!
# Suspicious Alignment of SGD — abstract probabilistic lemmas (Appendix A.3–A.4)

This file formalizes the general probability lemmas of Appendix A.3–A.4 of Deng et al.,
*Suspicious Alignment of SGD* (arXiv:2601.11789v2), tex lines 948–1058.  It is abstract probability:
the variances of the Gaussian forms enter only as hypotheses, and the `Spec` structure of
`Defs.lean` is used only in the final interface section (Part 5).

Because the probability space changes with the dimension `d`, everything is stated for a *family*
`(Ω n, μ n)` of probability spaces and random variables `Y n : Ω n → ℝ`.  "`Y_n → l` in
probability" (`l` a constant) is written out directly as

`∀ ε : ℝ, 0 < ε → Tendsto (fun n => μ n {ω | ε ≤ |Y n ω - l|}) atTop (𝓝 0)`

(`Concentration.tendstoInMeasure_const_iff` shows that on a fixed space this is Mathlib's
`MeasureTheory.TendstoInMeasure`).

## Main results

* **Lemma "A Weak Law of Large Numbers for Block Averages"** (tex 962–984):
  `wlln_block_average_centered`, `wlln_block_average` (block sum `S_n`, block size `N_n`), their
  literal `Finset` forms `wlln_finset_block_average_centered`, `wlln_finset_block_average`, and the
  sharper `wlln_centered_of_variance_div_sq_tendsto_zero` (`Var(S_n) = o(N_n²)` suffices).
* **Lemma "Continuous Mapping Theorem with Dominated Convergence"** (tex 986–988):
  `tendsto_integral_comp_of_tendstoInProb`, with the variant
  `tendsto_integral_comp_of_tendstoInProb_of_ae_bounded` (`f` bounded only along the `Y_n`, which is
  what the paper's application to `f(y) = (1+y)⁻¹` needs) and the bounded convergence theorem
  `tendsto_integral_of_tendstoInProb_of_bounded`.
* **Lemma "Asymptotic ratio of expectations"** (tex 995–1036):
  * quantitative, single probability space: for `0 ≤ X ≤ Z`, `𝔼 Z > 0`,
    `|𝔼[X/Z] - 𝔼X/𝔼Z| ≤ 𝔼|Z - 𝔼Z| / (2 𝔼Z) ≤ √Var(Z) / (2 𝔼Z)`
    (`abs_integral_ratio_sub_ratio_integral_le_L1`, `abs_integral_ratio_sub_ratio_integral_le`;
    the constant `1/2` is optimal: `abs_integral_ratio_sub_ratio_integral_le_sharp`), and the
    two-block form `abs_integral_ratio_add_sub_ratio_integral_le` with
    `(√Var X + √Var Y) / (2 (𝔼X + 𝔼Y))`;
  * asymptotic: `tendsto_integral_ratio_sub_ratio_integral`,
    `tendsto_integral_ratio_of_tendsto_ratio_integral`,
    `tendsto_integral_ratio_add_sub_ratio_integral`,
    `tendsto_integral_ratio_add_of_tendsto_ratio_integral`;
  * the paper's own formulation, eq. (ratio-asymp): `tendstoInProb_ratio_of_tendstoInProb`,
    `tendsto_integral_ratio_of_tendstoInProb`, `tendsto_integral_ratio_paper`,
    `tendsto_integral_ratio_of_variance_bound`; the hypothesis `ℓ'_𝒟 > 0` (asserted but not
    justified in the paper) cannot be dropped: `ratio_asymp_fails_without_positive_limit`.
* **The displayed "consequence"** (tex 1038–1048): the algebra `Concentration.ratio_sub_ratio_eq`,
  `Concentration.ratio_lt_ratio_iff`, `Concentration.ratio_limit_lt_iff`, the correct sign
  `Concentration.ratio_eq_one_div_one_add` (and `Concentration.ratio_ne_one_div_one_sub` for the
  typo), the correct asymptotic statements `eventually_integral_ratio_add_lt_add_of_le`,
  `eventually_integral_ratio_add_lt_of_gap`, `eventually_integral_ratio_add_lt_of_tendsto_lt`, and
  the counterexample `strict_drift_not_preserved_in_limit` to the passage "strict inequality for
  every `d` ⟹ strict inequality of the limits".
* **Interface with `Defs.lean`**: `Concentration.abs_integral_theta_sub_thetaBarNext_le` and
  `Concentration.tendsto_integral_theta_sub_thetaBarNext`, i.e.
  `𝔼[θ_{t+1} | x_t] - Spec.thetaBarNext → 0` under variance hypotheses.

Division follows Lean's convention `x / 0 = 0`.  In the ratio lemmas this is exactly the paper's
convention `θ(0) = 0`: on the event `Z = 0` we also have `X = 0` (as `0 ≤ X ≤ Z`), so `X / Z` is
`0 / 0 = 0`; no statement below is made true by a vanishing denominator (`𝔼 Z > 0`, `ρ ≠ 0`,
`ρ a + b ≠ 0` are explicit hypotheses).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace SuspiciousAlignment

/-! ## Part 1. A weak law of large numbers for block averages -/

namespace Concentration

/-- On a fixed measure space, the formulation of convergence in probability to a constant used in
this file is Mathlib's `MeasureTheory.TendstoInMeasure` (towards the constant function). -/
theorem tendstoInMeasure_const_iff {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Y : ℕ → Ω → ℝ} {l : ℝ} :
    TendstoInMeasure μ Y atTop (fun _ => l) ↔
      ∀ ε : ℝ, 0 < ε → Tendsto (fun n => μ {ω | ε ≤ |Y n ω - l|}) atTop (𝓝 0) := by
  rw [tendstoInMeasure_iff_norm]
  simp only [Real.norm_eq_abs]

/-- If `Y_n - c_n → 0` in probability and the deterministic centres satisfy `c_n → l`, then
`Y_n → l` in probability.  (No finiteness of the measures is needed.) -/
theorem tendstoInProb_of_sub_of_tendsto {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {μ : ∀ n, Measure (Ω n)} {Y : ∀ n, Ω n → ℝ} {c : ℕ → ℝ} {l : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => μ n {ω | ε ≤ |Y n ω - c n|}) atTop (𝓝 0))
    (hc : Tendsto c atTop (𝓝 l)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => μ n {ω | ε ≤ |Y n ω - l|}) atTop (𝓝 0) := by
  intro ε hε
  have hev : ∀ᶠ n in atTop, |c n - l| < ε / 2 := by
    have := (Metric.tendsto_nhds.mp hc) (ε / 2) (half_pos hε)
    simpa [Real.dist_eq] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (h (ε / 2) (half_pos hε))
    (Eventually.of_forall fun n => zero_le) ?_
  filter_upwards [hev] with n hn
  apply measure_mono
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  have : |Y n ω - l| ≤ |Y n ω - c n| + |c n - l| := abs_sub_le _ _ _
  linarith

end Concentration

section WLLN

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {μ : ∀ n, Measure (Ω n)}
  [∀ n, IsProbabilityMeasure (μ n)]

/-- **Chebyshev along a family of probability spaces** (the engine of Lemma "A Weak Law of Large
Numbers for Block Averages", tex 969–984): if `Y_n ∈ L²` and `Var(Y_n) → 0`, then
`Y_n - 𝔼[Y_n] → 0` in probability. -/
theorem tendstoInProb_sub_integral_of_variance_tendsto_zero {Y : ∀ n, Ω n → ℝ}
    (hY : ∀ n, MemLp (Y n) 2 (μ n))
    (hvar : Tendsto (fun n => Var[Y n; μ n]) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ n {ω | ε ≤ |Y n ω - ∫ ω', Y n ω' ∂μ n|}) atTop (𝓝 0) := by
  intro ε hε
  have hbound : ∀ n, μ n {ω | ε ≤ |Y n ω - ∫ ω', Y n ω' ∂μ n|}
      ≤ ENNReal.ofReal (Var[Y n; μ n] / ε ^ 2) :=
    fun n => meas_ge_le_variance_div_sq (hY n) hε
  have hlim : Tendsto (fun n => ENNReal.ofReal (Var[Y n; μ n] / ε ^ 2)) atTop (𝓝 0) := by
    have h := hvar.div_const (ε ^ 2)
    rw [zero_div] at h
    simpa using ENNReal.tendsto_ofReal h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => zero_le)
    hbound

/-- If `Y_n ∈ L²`, `Var(Y_n) → 0` and `𝔼[Y_n] → l`, then `Y_n → l` in probability. -/
theorem tendstoInProb_of_variance_tendsto_zero {Y : ∀ n, Ω n → ℝ}
    (hY : ∀ n, MemLp (Y n) 2 (μ n))
    (hvar : Tendsto (fun n => Var[Y n; μ n]) atTop (𝓝 0)) {l : ℝ}
    (hmean : Tendsto (fun n => ∫ ω, Y n ω ∂μ n) atTop (𝓝 l)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => μ n {ω | ε ≤ |Y n ω - l|}) atTop (𝓝 0) :=
  Concentration.tendstoInProb_of_sub_of_tendsto
    (tendstoInProb_sub_integral_of_variance_tendsto_zero hY hvar) hmean

/-- **WLLN for block averages under the weaker variance condition `Var(S_n) = o(N_n²)`.**
If `Var(S_n) / N_n² → 0` then `S_n/N_n - 𝔼[S_n/N_n] → 0` in probability.  This is strictly more
general than the paper's hypothesis `Var(S_n) = O(N_n)`, `N_n → ∞`
(`wlln_block_average_centered`). -/
theorem wlln_centered_of_variance_div_sq_tendsto_zero {S : ∀ n, Ω n → ℝ}
    (hS : ∀ n, MemLp (S n) 2 (μ n)) {N : ℕ → ℝ}
    (hvar : Tendsto (fun n => Var[S n; μ n] / N n ^ 2) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ n {ω | ε ≤ |S n ω / N n - ∫ ω', S n ω' / N n ∂μ n|}) atTop (𝓝 0) := by
  refine tendstoInProb_sub_integral_of_variance_tendsto_zero (Y := fun n ω => S n ω / N n)
    (fun n => ?_) ?_
  · simpa [div_eq_mul_inv] using (hS n).mul_const (N n)⁻¹
  · refine hvar.congr fun n => ?_
    simp only [div_eq_mul_inv]
    rw [variance_mul_const, inv_pow]

/-- **Lemma "A Weak Law of Large Numbers for Block Averages", first part** (tex 962–966).
`S_n` is the block sum `∑_{i∈𝒮_d} y_i`, `N_n = |𝒮_d| → ∞`, and `Var(S_n) = O(N_n)`, i.e.
`Var(S_n) ≤ K · N_n` for all large `n`.  Then `S_n/N_n - 𝔼[S_n/N_n] → 0` in probability. -/
theorem wlln_block_average_centered {S : ∀ n, Ω n → ℝ}
    (hS : ∀ n, MemLp (S n) 2 (μ n)) {N : ℕ → ℝ} (hN : Tendsto N atTop atTop) {K : ℝ}
    (hvar : ∀ᶠ n in atTop, Var[S n; μ n] ≤ K * N n) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ n {ω | ε ≤ |S n ω / N n - ∫ ω', S n ω' / N n ∂μ n|}) atTop (𝓝 0) := by
  apply wlln_centered_of_variance_div_sq_tendsto_zero hS
  have hK : Tendsto (fun n => K / N n) atTop (𝓝 0) := hN.const_div_atTop K
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hK
    (Eventually.of_forall fun n => div_nonneg (variance_nonneg _ _) (sq_nonneg _)) ?_
  filter_upwards [hvar, hN.eventually_gt_atTop 0] with n hn hpos
  rw [div_le_div_iff₀ (pow_pos hpos 2) hpos]
  nlinarith [variance_nonneg (S n) (μ n)]

/-- **Lemma "A Weak Law of Large Numbers for Block Averages", second part** (tex 967).
If moreover `𝔼[S_n]/N_n → l`, then `S_n/N_n → l` in probability. -/
theorem wlln_block_average {S : ∀ n, Ω n → ℝ}
    (hS : ∀ n, MemLp (S n) 2 (μ n)) {N : ℕ → ℝ} (hN : Tendsto N atTop atTop) {K : ℝ}
    (hvar : ∀ᶠ n in atTop, Var[S n; μ n] ≤ K * N n) {l : ℝ}
    (hmean : Tendsto (fun n => (∫ ω, S n ω ∂μ n) / N n) atTop (𝓝 l)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => μ n {ω | ε ≤ |S n ω / N n - l|}) atTop (𝓝 0) := by
  refine Concentration.tendstoInProb_of_sub_of_tendsto
    (wlln_block_average_centered hS hN hvar) ?_
  simpa only [integral_div] using hmean

/-- **Lemma "A Weak Law of Large Numbers for Block Averages", literal form, first part**
(tex 962–966): index sets `𝒮_d = s n` with `|s n| → ∞`, scalar random variables `y_i ∈ L²`
(`i ∈ s n`) with `Var(∑_{i∈s n} y_i) ≤ K |s n|` for large `n`.  Then the block average minus its
expectation tends to `0` in probability. -/
theorem wlln_finset_block_average_centered {ι : ℕ → Type*} {s : ∀ n, Finset (ι n)}
    {y : ∀ n, ι n → Ω n → ℝ} (hy : ∀ n, ∀ i ∈ s n, MemLp (y n i) 2 (μ n))
    (hcard : Tendsto (fun n => ((s n).card : ℝ)) atTop atTop) {K : ℝ}
    (hvar : ∀ᶠ n in atTop, Var[fun ω => ∑ i ∈ s n, y n i ω; μ n] ≤ K * (s n).card) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ n {ω | ε ≤ |(∑ i ∈ s n, y n i ω) / ((s n).card : ℝ)
        - ∫ ω', (∑ i ∈ s n, y n i ω') / ((s n).card : ℝ) ∂μ n|}) atTop (𝓝 0) :=
  wlln_block_average_centered (S := fun n ω => ∑ i ∈ s n, y n i ω)
    (fun n => memLp_finsetSum (s n) (hy n)) hcard hvar

/-- **Lemma "A Weak Law of Large Numbers for Block Averages", literal form, second part**
(tex 967): if moreover `(1/|s n|) ∑_{i∈s n} 𝔼[y_i] → l`, the block average tends to `l` in
probability. -/
theorem wlln_finset_block_average {ι : ℕ → Type*} {s : ∀ n, Finset (ι n)}
    {y : ∀ n, ι n → Ω n → ℝ} (hy : ∀ n, ∀ i ∈ s n, MemLp (y n i) 2 (μ n))
    (hcard : Tendsto (fun n => ((s n).card : ℝ)) atTop atTop) {K : ℝ}
    (hvar : ∀ᶠ n in atTop, Var[fun ω => ∑ i ∈ s n, y n i ω; μ n] ≤ K * (s n).card) {l : ℝ}
    (hmean : Tendsto (fun n => (∑ i ∈ s n, ∫ ω, y n i ω ∂μ n) / ((s n).card : ℝ)) atTop (𝓝 l)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ n {ω | ε ≤ |(∑ i ∈ s n, y n i ω) / ((s n).card : ℝ) - l|})
        atTop (𝓝 0) := by
  refine wlln_block_average (S := fun n ω => ∑ i ∈ s n, y n i ω)
    (fun n => memLp_finsetSum (s n) (hy n)) hcard hvar ?_
  refine hmean.congr fun n => ?_
  rw [integral_finsetSum (s n) fun i hi => (hy n i hi).integrable one_le_two]

end WLLN

/-! ## Part 2. Continuous mapping theorem with bounded convergence -/

namespace Concentration

/-- Quantitative bounded-convergence estimate on one probability space: if `|f(Y)| ≤ M` a.s. and
`|f y - f y₀| ≤ ε` whenever `|y - y₀| < δ`, then
`|𝔼 f(Y) - f(y₀)| ≤ ε + (M + |f y₀|) · ℙ(|Y - y₀| ≥ δ)`. -/
theorem abs_integral_comp_sub_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY : AEMeasurable Y μ) {f : ℝ → ℝ}
    (hfY : AEStronglyMeasurable (fun ω => f (Y ω)) μ) {M : ℝ}
    (hM : ∀ᵐ ω ∂μ, |f (Y ω)| ≤ M) {y₀ ε δ : ℝ} (hε : 0 ≤ ε)
    (hδ : ∀ y, |y - y₀| < δ → |f y - f y₀| ≤ ε) :
    |∫ ω, f (Y ω) ∂μ - f y₀| ≤ ε + (M + |f y₀|) * (μ {ω | δ ≤ |Y ω - y₀|}).toReal := by
  set A : Set Ω := {ω | δ ≤ |Y ω - y₀|} with hA_def
  have hA : NullMeasurableSet A μ :=
    nullMeasurableSet_le aemeasurable_const
      (continuous_abs.measurable.comp_aemeasurable (hY.sub_const y₀))
  have hfYint : Integrable (fun ω => f (Y ω)) μ :=
    Integrable.of_bound hfY M (by
      filter_upwards [hM] with ω hω
      rwa [Real.norm_eq_abs])
  have hind : Integrable (fun ω => (M + |f y₀|) * A.indicator (fun _ => (1 : ℝ)) ω) μ :=
    ((integrable_const (1 : ℝ)).indicator₀ hA).const_mul (M + |f y₀|)
  have hpt : ∀ᵐ ω ∂μ,
      ‖f (Y ω) - f y₀‖ ≤ ε + (M + |f y₀|) * A.indicator (fun _ => (1 : ℝ)) ω := by
    filter_upwards [hM] with ω hMω
    rw [Real.norm_eq_abs]
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]
      have h1 : |f (Y ω) - f y₀| ≤ |f (Y ω)| + |f y₀| := abs_sub _ _
      linarith
    · rw [Set.indicator_of_notMem hω]
      have h1 : |Y ω - y₀| < δ := not_le.mp hω
      have h2 := hδ _ h1
      linarith
  have hint : ∫ ω, f (Y ω) ∂μ - f y₀ = ∫ ω, (f (Y ω) - f y₀) ∂μ := by
    rw [integral_sub hfYint (integrable_const _), integral_const]
    simp
  have hrhs : ∫ ω, (ε + (M + |f y₀|) * A.indicator (fun _ => (1 : ℝ)) ω) ∂μ
      = ε + (M + |f y₀|) * (μ A).toReal := by
    rw [integral_add (integrable_const ε) hind, integral_const, integral_const_mul,
      integral_indicator₀ hA, setIntegral_const]
    simp [Measure.real]
  rw [hint, ← Real.norm_eq_abs, ← hrhs]
  exact norm_integral_le_of_norm_le ((integrable_const ε).add hind) hpt

end Concentration

section CMT

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {μ : ∀ n, Measure (Ω n)}
  [∀ n, IsProbabilityMeasure (μ n)]

/-- **Continuous mapping + bounded convergence, with `f` bounded only along the `Y_n`.**
If `Y_n → y₀` in probability, `f` is continuous at `y₀`, each `f ∘ Y_n` is a.e. strongly
measurable and `|f(Y_n)| ≤ M` almost surely (uniformly in `n`), then `𝔼[f(Y_n)] → f(y₀)`.

This is the version actually needed in the paper's proof of Lemma "Asymptotic ratio of
expectations", where `f(y) = (1 + y)⁻¹` is bounded on `[0, ∞)` (where the `Y_n` live) but not on
`ℝ`. -/
theorem tendsto_integral_comp_of_tendstoInProb_of_ae_bounded {Y : ∀ n, Ω n → ℝ}
    (hY : ∀ n, AEMeasurable (Y n) (μ n)) {y₀ : ℝ}
    (hconv : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => μ n {ω | ε ≤ |Y n ω - y₀|}) atTop (𝓝 0))
    {f : ℝ → ℝ} (hfY : ∀ n, AEStronglyMeasurable (fun ω => f (Y n ω)) (μ n))
    (hbdd : ∃ M, ∀ n, ∀ᵐ ω ∂μ n, |f (Y n ω)| ≤ M) (hcont : ContinuousAt f y₀) :
    Tendsto (fun n => ∫ ω, f (Y n ω) ∂μ n) atTop (𝓝 (f y₀)) := by
  obtain ⟨M, hM⟩ := hbdd
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.mp hcont (ε / 2) (half_pos hε)
  have ht : Tendsto (fun n => (M + |f y₀|) * (μ n {ω | δ ≤ |Y n ω - y₀|}).toReal) atTop
      (𝓝 0) := by
    simpa using
      ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hconv δ hδ)).const_mul (M + |f y₀|)
  filter_upwards [(tendsto_order.1 ht).2 (ε / 2) (half_pos hε)] with n hn
  have hb := Concentration.abs_integral_comp_sub_le (μ := μ n) (hY n) (hfY n) (hM n) (y₀ := y₀)
    (ε := ε / 2) (δ := δ) (half_pos hε).le
    (fun y hy => (hδf (by rwa [Real.dist_eq])).le.trans_eq' (by rw [Real.dist_eq]))
  rw [Real.dist_eq]
  linarith

/-- **Lemma "Continuous Mapping Theorem with Dominated Convergence"** (tex 986–988).
If `y_n → y₀` in probability (`y₀` a constant) and `f : ℝ → ℝ` is bounded, (Borel) measurable and
continuous at `y₀`, then `𝔼[f(y_n)] → f(y₀)`.

Measurability of `f` and a.e.-measurability of the `y_n` are implicit in the paper (they are
needed for `𝔼[f(y_n)]` to be defined). -/
theorem tendsto_integral_comp_of_tendstoInProb {Y : ∀ n, Ω n → ℝ}
    (hY : ∀ n, AEMeasurable (Y n) (μ n)) {y₀ : ℝ}
    (hconv : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => μ n {ω | ε ≤ |Y n ω - y₀|}) atTop (𝓝 0))
    {f : ℝ → ℝ} (hf : Measurable f) (hbdd : ∃ M, ∀ y, |f y| ≤ M) (hcont : ContinuousAt f y₀) :
    Tendsto (fun n => ∫ ω, f (Y n ω) ∂μ n) atTop (𝓝 (f y₀)) := by
  obtain ⟨M, hM⟩ := hbdd
  exact tendsto_integral_comp_of_tendstoInProb_of_ae_bounded hY hconv
    (fun n => (hf.comp_aemeasurable (hY n)).aestronglyMeasurable)
    ⟨M, fun n => Eventually.of_forall fun ω => hM _⟩ hcont

/-- **Bounded convergence along a family of probability spaces.** If `A ≤ Y_n ≤ B` almost surely
and `Y_n → y₀` in probability, then `𝔼[Y_n] → y₀`.  (Apply the previous lemma to the clamp onto
`[min A y₀, max B y₀]`.) -/
theorem tendsto_integral_of_tendstoInProb_of_bounded {Y : ∀ n, Ω n → ℝ}
    (hY : ∀ n, AEMeasurable (Y n) (μ n)) {A B y₀ : ℝ}
    (hbd : ∀ n, ∀ᵐ ω ∂μ n, A ≤ Y n ω ∧ Y n ω ≤ B)
    (hconv : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => μ n {ω | ε ≤ |Y n ω - y₀|}) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, Y n ω ∂μ n) atTop (𝓝 y₀) := by
  set A' := min A y₀
  set B' := max B y₀
  set f : ℝ → ℝ := fun y => max A' (min B' y) with hf_def
  have hA'y : A' ≤ y₀ := min_le_right _ _
  have hyB' : y₀ ≤ B' := le_max_right _ _
  have hfm : Measurable f := measurable_const.max (measurable_const.min measurable_id)
  have hfc : Continuous f := continuous_const.max (continuous_const.min continuous_id)
  have hfb : ∀ y, |f y| ≤ max |A'| |B'| := by
    intro y
    have h1 : A' ≤ f y := le_max_left _ _
    have h2 : f y ≤ B' := max_le (hA'y.trans hyB') (min_le_left _ _)
    exact abs_le_max_abs_abs h1 h2
  have hfy : f y₀ = y₀ := by
    simp only [hf_def]
    rw [min_eq_right hyB', max_eq_right hA'y]
  have h := tendsto_integral_comp_of_tendstoInProb hY hconv hfm ⟨_, hfb⟩ hfc.continuousAt
  rw [hfy] at h
  refine h.congr fun n => integral_congr_ae ?_
  filter_upwards [hbd n] with ω hω
  simp only [hf_def]
  rw [min_eq_right (hω.2.trans (le_max_left _ _)),
    max_eq_right ((min_le_left _ _).trans hω.1)]

end CMT

/-! ## Part 3. Ratio of expectations

### Auxiliary second-moment inequalities -/

namespace Concentration

section OneSpace

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Cauchy–Schwarz for the covariance: `cov(X,Y)² ≤ Var X · Var Y`. -/
theorem covariance_sq_le_variance_mul_variance [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    cov[X, Y; μ] ^ 2 ≤ Var[X; μ] * Var[Y; μ] := by
  have h : ∀ t : ℝ, 0 ≤ Var[Y; μ] * (t * t) + 2 * cov[X, Y; μ] * t + Var[X; μ] := by
    intro t
    have h0 := variance_nonneg (X + t • Y) μ
    rw [variance_add hX (hY.const_smul t), variance_smul, covariance_smul_right] at h0
    nlinarith [h0]
  have hd := discrim_le_zero h
  unfold discrim at hd
  nlinarith [hd]

/-- Minkowski's inequality for standard deviations: `σ(X+Y) ≤ σ(X) + σ(Y)`. -/
theorem sqrt_variance_add_le [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    √Var[X + Y; μ] ≤ √Var[X; μ] + √Var[Y; μ] := by
  have hc := covariance_sq_le_variance_mul_variance hX hY
  have hx := Real.sq_sqrt (variance_nonneg X μ)
  have hy := Real.sq_sqrt (variance_nonneg Y μ)
  have hsx := Real.sqrt_nonneg Var[X; μ]
  have hsy := Real.sqrt_nonneg Var[Y; μ]
  have hcov : cov[X, Y; μ] ≤ √Var[X; μ] * √Var[Y; μ] := by
    refine (abs_le_of_sq_le_sq' ?_ (mul_nonneg hsx hsy)).2
    rw [mul_pow, hx, hy]
    exact hc
  refine Real.sqrt_le_iff.mpr ⟨add_nonneg hsx hsy, ?_⟩
  rw [variance_add hX hY]
  nlinarith [hcov]

/-- The mean absolute deviation is at most the standard deviation: `𝔼|Z - 𝔼Z| ≤ √Var(Z)`. -/
theorem integral_abs_sub_integral_le_sqrt_variance [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    (hZ : MemLp Z 2 μ) : ∫ ω, |Z ω - ∫ ω', Z ω' ∂μ| ∂μ ≤ √Var[Z; μ] := by
  set m := ∫ ω', Z ω' ∂μ with hm
  have hW : MemLp (fun ω => |Z ω - m|) 2 μ := by
    simpa [Real.norm_eq_abs] using (hZ.sub (memLp_const m)).norm
  have h0 := variance_nonneg (fun ω => |Z ω - m|) μ
  rw [variance_eq_sub hW] at h0
  have hsq : μ[(fun ω => |Z ω - m|) ^ 2] = Var[Z; μ] := by
    rw [variance_eq_integral hZ.aemeasurable]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp [sq_abs, hm]
  rw [hsq] at h0
  exact (le_abs_self _).trans (Real.abs_le_sqrt (by linarith))

end OneSpace

end Concentration

/-! ### The quantitative transfer inequality on one probability space -/

section RatioOneSpace

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Quantitative ratio-of-expectations bound, `L¹` form** (abstract core of Lemma "Asymptotic
ratio of expectations", tex 995–1036).  Let `0 ≤ X ≤ Z` almost surely with `Z` integrable and
`𝔼 Z > 0` (think `X = s^𝒟_{t+1}`, `Z = s_{t+1}`, so `X / Z = θ_{t+1}`, with `0 / 0 = 0`).  Then

`|𝔼[X/Z] - 𝔼X / 𝔼Z| ≤ 𝔼|Z - 𝔼Z| / (2 𝔼Z)`.

Proof: with `R = X/Z ∈ [0,1]` one has `X = R Z`, hence
`𝔼Z · 𝔼R - 𝔼X = 𝔼[(R - 1/2)(𝔼Z - Z)]` and `|R - 1/2| ≤ 1/2`.  Only the fluctuation of the
*denominator* matters; no moment of `X` beyond integrability (automatic) is needed. -/
theorem abs_integral_ratio_sub_ratio_integral_le_L1 {X Z : Ω → ℝ}
    (hX : AEStronglyMeasurable X μ) (hZ : Integrable Z μ)
    (hX0 : ∀ᵐ ω ∂μ, 0 ≤ X ω) (hXZ : ∀ᵐ ω ∂μ, X ω ≤ Z ω) (hEZ : 0 < ∫ ω, Z ω ∂μ) :
    |∫ ω, X ω / Z ω ∂μ - (∫ ω, X ω ∂μ) / ∫ ω, Z ω ∂μ|
      ≤ (∫ ω, |Z ω - ∫ ω', Z ω' ∂μ| ∂μ) / (2 * ∫ ω, Z ω ∂μ) := by
  set m := ∫ ω, Z ω ∂μ with hm
  have hXint : Integrable X μ := hZ.mono' hX (by
    filter_upwards [hX0, hXZ] with ω h1 h2
    rw [Real.norm_eq_abs, abs_of_nonneg h1]
    exact h2)
  have hRmeas : AEStronglyMeasurable (fun ω => X ω / Z ω) μ :=
    (hX.aemeasurable.div hZ.aemeasurable).aestronglyMeasurable
  have hRbd : ∀ᵐ ω ∂μ, 0 ≤ X ω / Z ω ∧ X ω / Z ω ≤ 1 := by
    filter_upwards [hX0, hXZ] with ω h1 h2
    exact ⟨div_nonneg h1 (h1.trans h2), div_le_one_of_le₀ h2 (h1.trans h2)⟩
  have hRint : Integrable (fun ω => X ω / Z ω) μ :=
    Integrable.of_bound hRmeas 1 (by
      filter_upwards [hRbd] with ω h
      rw [Real.norm_eq_abs, abs_of_nonneg h.1]
      exact h.2)
  have hdev : Integrable (fun ω => |Z ω - m|) μ := (hZ.sub (integrable_const m)).abs
  -- pointwise: `m R - X - (m - Z)/2 = (R - 1/2)(m - Z)`, of modulus `≤ |Z - m| / 2`
  have hG : ∀ᵐ ω ∂μ, ‖m * (X ω / Z ω) - X ω - 1 / 2 * (m - Z ω)‖ ≤ 1 / 2 * |Z ω - m| := by
    filter_upwards [hX0, hXZ, hRbd] with ω h1 h2 hR
    have hx : X ω = X ω / Z ω * Z ω := by
      rcases (h1.trans h2).eq_or_lt with hz | hz
      · have hx0 : X ω = 0 := le_antisymm (hz ▸ h2) h1
        rw [hx0]
        simp
      · field_simp
    have hfac : m * (X ω / Z ω) - X ω - 1 / 2 * (m - Z ω)
        = (X ω / Z ω - 1 / 2) * (m - Z ω) := by
      linear_combination (-1 : ℝ) * hx
    rw [hfac, Real.norm_eq_abs, abs_mul, abs_sub_comm m (Z ω)]
    have hhalf : |X ω / Z ω - 1 / 2| ≤ 1 / 2 :=
      abs_le.mpr ⟨by linarith [hR.1], by linarith [hR.2]⟩
    exact mul_le_mul_of_nonneg_right hhalf (abs_nonneg _)
  -- its integral is `m 𝔼R - 𝔼X`, because `𝔼[m - Z] = 0`
  have hint : ∫ ω, (m * (X ω / Z ω) - X ω - 1 / 2 * (m - Z ω)) ∂μ
      = m * ∫ ω, X ω / Z ω ∂μ - ∫ ω, X ω ∂μ := by
    have e1 : ∫ ω, (m * (X ω / Z ω) - X ω - 1 / 2 * (m - Z ω)) ∂μ
        = ∫ ω, (m * (X ω / Z ω) - X ω) ∂μ - ∫ ω, 1 / 2 * (m - Z ω) ∂μ :=
      integral_sub ((hRint.const_mul m).sub hXint)
        (((integrable_const m).sub hZ).const_mul (1 / 2))
    have e2 : ∫ ω, (m * (X ω / Z ω) - X ω) ∂μ
        = ∫ ω, m * (X ω / Z ω) ∂μ - ∫ ω, X ω ∂μ :=
      integral_sub (hRint.const_mul m) hXint
    have e3 : ∫ ω, (m - Z ω) ∂μ = ∫ _, m ∂μ - ∫ ω, Z ω ∂μ :=
      integral_sub (integrable_const m) hZ
    rw [e1, e2, integral_const_mul, integral_const_mul, e3, integral_const]
    simp [← hm]
  have hmain : |m * ∫ ω, X ω / Z ω ∂μ - ∫ ω, X ω ∂μ| ≤ 1 / 2 * ∫ ω, |Z ω - m| ∂μ := by
    rw [← hint, ← Real.norm_eq_abs, ← integral_const_mul]
    exact norm_integral_le_of_norm_le (hdev.const_mul (1 / 2)) hG
  have hfinal : ∫ ω, X ω / Z ω ∂μ - (∫ ω, X ω ∂μ) / m
      = (m * ∫ ω, X ω / Z ω ∂μ - ∫ ω, X ω ∂μ) / m := by
    field_simp
  rw [hfinal, abs_div, abs_of_pos hEZ, div_le_div_iff₀ hEZ (by positivity)]
  have := mul_le_mul_of_nonneg_right hmain hEZ.le
  linarith

/-- **Quantitative ratio-of-expectations bound** (abstract core of Lemma "Asymptotic ratio of
expectations").  For `0 ≤ X ≤ Z` a.s., `Z ∈ L²`, `𝔼 Z > 0`:

`|𝔼[X/Z] - 𝔼X / 𝔼Z| ≤ √Var(Z) / (2 𝔼Z)`.

The error is at most half the coefficient of variation of the denominator; the constant `1/2` is
optimal (`abs_integral_ratio_sub_ratio_integral_le_sharp`), and `Var(X)` does not enter. -/
theorem abs_integral_ratio_sub_ratio_integral_le {X Z : Ω → ℝ}
    (hX : AEStronglyMeasurable X μ) (hZ : MemLp Z 2 μ)
    (hX0 : ∀ᵐ ω ∂μ, 0 ≤ X ω) (hXZ : ∀ᵐ ω ∂μ, X ω ≤ Z ω) (hEZ : 0 < ∫ ω, Z ω ∂μ) :
    |∫ ω, X ω / Z ω ∂μ - (∫ ω, X ω ∂μ) / ∫ ω, Z ω ∂μ|
      ≤ √Var[Z; μ] / (2 * ∫ ω, Z ω ∂μ) :=
  (abs_integral_ratio_sub_ratio_integral_le_L1 hX (hZ.integrable one_le_two) hX0 hXZ hEZ).trans
    (div_le_div_of_nonneg_right (Concentration.integral_abs_sub_integral_le_sqrt_variance hZ)
      (by positivity))

/-- **Quantitative ratio-of-expectations bound, two-block form.**  For `X, Y ≥ 0` a.s. in `L²`
with `𝔼X + 𝔼Y > 0` (think `X = s^𝒟_{t+1}`, `Y = s^ℬ_{t+1}`, `X/(X+Y) = θ_{t+1}`):

`|𝔼[X/(X+Y)] - 𝔼X / (𝔼X + 𝔼Y)| ≤ (√Var X + √Var Y) / (2 (𝔼X + 𝔼Y))`.

Only the two block variances are needed (no covariance between the blocks). -/
theorem abs_integral_ratio_add_sub_ratio_integral_le {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hX0 : ∀ᵐ ω ∂μ, 0 ≤ X ω) (hY0 : ∀ᵐ ω ∂μ, 0 ≤ Y ω)
    (hpos : 0 < ∫ ω, X ω ∂μ + ∫ ω, Y ω ∂μ) :
    |∫ ω, X ω / (X ω + Y ω) ∂μ - (∫ ω, X ω ∂μ) / (∫ ω, X ω ∂μ + ∫ ω, Y ω ∂μ)|
      ≤ (√Var[X; μ] + √Var[Y; μ]) / (2 * (∫ ω, X ω ∂μ + ∫ ω, Y ω ∂μ)) := by
  have hint : ∫ ω, (X ω + Y ω) ∂μ = ∫ ω, X ω ∂μ + ∫ ω, Y ω ∂μ :=
    integral_add (hX.integrable one_le_two) (hY.integrable one_le_two)
  have h := abs_integral_ratio_sub_ratio_integral_le (Z := fun ω => X ω + Y ω)
    hX.aestronglyMeasurable (hX.add hY) hX0
    (by filter_upwards [hY0] with ω h; linarith) (by rw [hint]; exact hpos)
  rw [hint] at h
  exact h.trans (div_le_div_of_nonneg_right (Concentration.sqrt_variance_add_le hX hY)
    (by positivity))

end RatioOneSpace

/-! ### Sharpness of the constant `1/2` (and a warning) -/

namespace Concentration

/-- The fair coin on `Bool`. -/
noncomputable def coin : Measure Bool :=
  (2⁻¹ : ℝ≥0) • Measure.dirac true + (2⁻¹ : ℝ≥0) • Measure.dirac false

instance coin_isProbabilityMeasure : IsProbabilityMeasure coin := by
  refine ⟨?_⟩
  simp [coin, ENNReal.inv_two_add_inv_two]

theorem integral_coin (f : Bool → ℝ) : ∫ b, f b ∂coin = (f true + f false) / 2 := by
  unfold coin
  rw [integral_add_measure Integrable.of_finite Integrable.of_finite,
    integral_smul_nnreal_measure, integral_smul_nnreal_measure, integral_dirac, integral_dirac]
  simp [NNReal.smul_def]
  ring

end Concentration

open Concentration in
/-- **The bound `|𝔼[X/Z] - 𝔼X/𝔼Z| ≤ √Var(Z) / (2 𝔼Z)` is attained.**  On a fair coin take
`Z = 1/2, 3/2` and `X = 1/2, 0`.  Then `0 ≤ X ≤ Z`, `𝔼Z = 1`, and
`𝔼[X/Z] - 𝔼X/𝔼Z = 1/2 - 1/4 = 1/4 = √Var(Z) / (2 𝔼Z)`.

In particular, *without concentration* the expectation of the ratio is **not** the ratio of the
expectations: the interchange asserted by Lemma "Asymptotic ratio of expectations" is a genuinely
asymptotic statement and needs `Var(Z)/(𝔼Z)² → 0`. -/
theorem abs_integral_ratio_sub_ratio_integral_le_sharp :
    ∃ (μ : Measure Bool) (_ : IsProbabilityMeasure μ) (X Z : Bool → ℝ),
      (∀ b, 0 ≤ X b) ∧ (∀ b, X b ≤ Z b) ∧ 0 < ∫ b, Z b ∂μ ∧
      ∫ b, X b / Z b ∂μ - (∫ b, X b ∂μ) / ∫ b, Z b ∂μ = 1 / 4 ∧
      √Var[Z; μ] / (2 * ∫ b, Z b ∂μ) = 1 / 4 := by
  refine ⟨coin, inferInstance, fun b => if b then 1 / 2 else 0,
    fun b => if b then 1 / 2 else 3 / 2, ?_, ?_, ?_, ?_, ?_⟩
  · intro b; cases b <;> norm_num
  · intro b; cases b <;> norm_num
  · rw [integral_coin]; norm_num
  · rw [integral_coin, integral_coin, integral_coin]; norm_num
  · have hZ : MemLp (fun b : Bool => if b then (1 / 2 : ℝ) else 3 / 2) 2 coin :=
      MemLp.of_discrete
    rw [variance_eq_sub hZ, integral_coin, integral_coin]
    norm_num

namespace Concentration

/-- A bounded random variable divided by `n + 1` tends to `0` in probability (trivially: the
deviation event is eventually empty). -/
theorem tendstoInProb_div_of_bounded {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f : Ω → ℝ} {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => μ {ω | ε ≤ |f ω / ((n : ℝ) + 1) - 0|}) atTop (𝓝 0) := by
  intro ε hε
  have hev : ∀ᶠ n : ℕ in atTop, C / ε < (n : ℝ) + 1 := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop (C / ε)] with n hn
    linarith
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hev] with n hn
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hempty : {ω | ε ≤ |f ω / ((n : ℝ) + 1) - 0|} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le, sub_zero]
    rw [abs_div, abs_of_pos hpos, div_lt_iff₀ hpos]
    rw [div_lt_iff₀ hε] at hn
    calc |f ω| ≤ C := hC ω
      _ < ((n : ℝ) + 1) * ε := hn
      _ = ε * ((n : ℝ) + 1) := mul_comm _ _
  rw [hempty, measure_empty]

end Concentration

open Concentration in
/-- **The hypothesis `ℓ'_𝒟 > 0` (more precisely `ρ a + b ≠ 0`) cannot be dropped from Lemma
"Asymptotic ratio of expectations".**  On a fair coin let `X = 1/2, 0` and `Y = 0, 3/2`
(independent of `n`), `k_n = m_n = n + 1`.  Then `X/k_n → 0` and `Y/m_n → 0` in probability
(`a = b = 0`, `ρ = 1`), but for every `n`
`𝔼[X/(X+Y)] = 1/2 ≠ 1/4 = 𝔼X/(𝔼X+𝔼Y)`:
the expected alignment is not the ratio of the expected energies, and the paper's formula
`1/(1 + ℓ'_ℬ/(ρ ℓ'_𝒟))` is `0/0`. -/
theorem ratio_asymp_fails_without_positive_limit :
    ∃ (μ : Measure Bool) (_ : IsProbabilityMeasure μ) (X Y : Bool → ℝ),
      (∀ b, 0 ≤ X b) ∧ (∀ b, 0 ≤ Y b) ∧
      (∀ ε : ℝ, 0 < ε →
        Tendsto (fun n : ℕ => μ {b | ε ≤ |X b / ((n : ℝ) + 1) - 0|}) atTop (𝓝 0)) ∧
      (∀ ε : ℝ, 0 < ε →
        Tendsto (fun n : ℕ => μ {b | ε ≤ |Y b / ((n : ℝ) + 1) - 0|}) atTop (𝓝 0)) ∧
      ∫ b, X b / (X b + Y b) ∂μ = 1 / 2 ∧
      (∫ b, X b ∂μ) / (∫ b, X b ∂μ + ∫ b, Y b ∂μ) = 1 / 4 := by
  refine ⟨coin, inferInstance, fun b => if b then 1 / 2 else 0,
    fun b => if b then 0 else 3 / 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b; cases b <;> norm_num
  · intro b; cases b <;> norm_num
  · exact tendstoInProb_div_of_bounded coin (C := 1 / 2) (fun b => by cases b <;> norm_num)
  · exact tendstoInProb_div_of_bounded coin (C := 3 / 2) (fun b => by cases b <;> norm_num)
  · rw [integral_coin]; norm_num
  · rw [integral_coin, integral_coin]; norm_num

/-! ### Asymptotic versions along a family of probability spaces -/

section RatioAsymptotic

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {μ : ∀ n, Measure (Ω n)}
  [∀ n, IsProbabilityMeasure (μ n)]

/-- **Asymptotic ratio of expectations, quantitative route** (replaces the proof of Lemma
"Asymptotic ratio of expectations", tex 1010–1036).  If `0 ≤ X_n ≤ Z_n` a.s., `Z_n ∈ L²`,
`𝔼 Z_n > 0` eventually and the squared coefficient of variation `Var(Z_n) / (𝔼 Z_n)² → 0`, then

`𝔼[X_n / Z_n] - 𝔼X_n / 𝔼Z_n → 0`.

No normalisation by `k`, no existence of the limits `ℓ'_𝒟, ℓ'_ℬ`, no condition on `Var(X_n)`. -/
theorem tendsto_integral_ratio_sub_ratio_integral {X Z : ∀ n, Ω n → ℝ}
    (hX : ∀ n, AEStronglyMeasurable (X n) (μ n)) (hZ : ∀ n, MemLp (Z n) 2 (μ n))
    (hX0 : ∀ n, ∀ᵐ ω ∂μ n, 0 ≤ X n ω) (hXZ : ∀ n, ∀ᵐ ω ∂μ n, X n ω ≤ Z n ω)
    (hEZ : ∀ᶠ n in atTop, 0 < ∫ ω, Z n ω ∂μ n)
    (hcv : Tendsto (fun n => Var[Z n; μ n] / (∫ ω, Z n ω ∂μ n) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, X n ω / Z n ω ∂μ n - (∫ ω, X n ω ∂μ n) / ∫ ω, Z n ω ∂μ n)
      atTop (𝓝 0) := by
  have hsq : Tendsto (fun n => (1 / 2 : ℝ) * √(Var[Z n; μ n] / (∫ ω, Z n ω ∂μ n) ^ 2))
      atTop (𝓝 0) := by
    have h := ((Real.continuous_sqrt.tendsto 0).comp hcv).const_mul (1 / 2 : ℝ)
    simpa using h
  refine squeeze_zero_norm' ?_ hsq
  filter_upwards [hEZ] with n hn
  rw [Real.norm_eq_abs]
  refine (abs_integral_ratio_sub_ratio_integral_le (hX n) (hZ n) (hX0 n) (hXZ n) hn).trans_eq ?_
  rw [Real.sqrt_div (variance_nonneg _ _), Real.sqrt_sq hn.le]
  ring

/-- If moreover the ratio of expectations converges, `𝔼X_n / 𝔼Z_n → L`, then the expected ratio
has the same limit: `𝔼[X_n / Z_n] → L`. -/
theorem tendsto_integral_ratio_of_tendsto_ratio_integral {X Z : ∀ n, Ω n → ℝ}
    (hX : ∀ n, AEStronglyMeasurable (X n) (μ n)) (hZ : ∀ n, MemLp (Z n) 2 (μ n))
    (hX0 : ∀ n, ∀ᵐ ω ∂μ n, 0 ≤ X n ω) (hXZ : ∀ n, ∀ᵐ ω ∂μ n, X n ω ≤ Z n ω)
    (hEZ : ∀ᶠ n in atTop, 0 < ∫ ω, Z n ω ∂μ n)
    (hcv : Tendsto (fun n => Var[Z n; μ n] / (∫ ω, Z n ω ∂μ n) ^ 2) atTop (𝓝 0)) {L : ℝ}
    (hL : Tendsto (fun n => (∫ ω, X n ω ∂μ n) / ∫ ω, Z n ω ∂μ n) atTop (𝓝 L)) :
    Tendsto (fun n => ∫ ω, X n ω / Z n ω ∂μ n) atTop (𝓝 L) := by
  have h := (tendsto_integral_ratio_sub_ratio_integral hX hZ hX0 hXZ hEZ hcv).add hL
  rw [zero_add] at h
  exact h.congr fun n => by ring

/-- **Asymptotic ratio of expectations, two-block form.**  If `X_n, Y_n ≥ 0` a.s. are in `L²`,
`𝔼X_n + 𝔼Y_n > 0` eventually, and `Var(X_n)/(𝔼X_n+𝔼Y_n)² → 0`, `Var(Y_n)/(𝔼X_n+𝔼Y_n)² → 0`, then

`𝔼[X_n/(X_n+Y_n)] - 𝔼X_n/(𝔼X_n+𝔼Y_n) → 0`.

With `X = s^𝒟_{t+1}`, `Y = s^ℬ_{t+1}` this reads `𝔼[θ_{t+1} | x_t] - thetaBarNext → 0`. -/
theorem tendsto_integral_ratio_add_sub_ratio_integral {X Y : ∀ n, Ω n → ℝ}
    (hX : ∀ n, MemLp (X n) 2 (μ n)) (hY : ∀ n, MemLp (Y n) 2 (μ n))
    (hX0 : ∀ n, ∀ᵐ ω ∂μ n, 0 ≤ X n ω) (hY0 : ∀ n, ∀ᵐ ω ∂μ n, 0 ≤ Y n ω)
    (hpos : ∀ᶠ n in atTop, 0 < ∫ ω, X n ω ∂μ n + ∫ ω, Y n ω ∂μ n)
    (hvX : Tendsto (fun n => Var[X n; μ n] / (∫ ω, X n ω ∂μ n + ∫ ω, Y n ω ∂μ n) ^ 2)
      atTop (𝓝 0))
    (hvY : Tendsto (fun n => Var[Y n; μ n] / (∫ ω, X n ω ∂μ n + ∫ ω, Y n ω ∂μ n) ^ 2)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, X n ω / (X n ω + Y n ω) ∂μ n
      - (∫ ω, X n ω ∂μ n) / (∫ ω, X n ω ∂μ n + ∫ ω, Y n ω ∂μ n)) atTop (𝓝 0) := by
  have hsq : Tendsto (fun n => (1 / 2 : ℝ) *
      (√(Var[X n; μ n] / (∫ ω, X n ω ∂μ n + ∫ ω, Y n ω ∂μ n) ^ 2)
        + √(Var[Y n; μ n] / (∫ ω, X n ω ∂μ n + ∫ ω, Y n ω ∂μ n) ^ 2))) atTop (𝓝 0) := by
    have h := ((((Real.continuous_sqrt.tendsto 0).comp hvX).add
      ((Real.continuous_sqrt.tendsto 0).comp hvY))).const_mul (1 / 2 : ℝ)
    simpa using h
  refine squeeze_zero_norm' ?_ hsq
  filter_upwards [hpos] with n hn
  rw [Real.norm_eq_abs]
  refine (abs_integral_ratio_add_sub_ratio_integral_le (hX n) (hY n) (hX0 n) (hY0 n)
    hn).trans_eq ?_
  rw [Real.sqrt_div (variance_nonneg _ _), Real.sqrt_div (variance_nonneg _ _),
    Real.sqrt_sq hn.le]
  have hne := hn.ne'
  field_simp

/-- Two-block form with a limit: if moreover `𝔼X_n/(𝔼X_n+𝔼Y_n) → L` then
`𝔼[X_n/(X_n+Y_n)] → L`. -/
theorem tendsto_integral_ratio_add_of_tendsto_ratio_integral {X Y : ∀ n, Ω n → ℝ}
    (hX : ∀ n, MemLp (X n) 2 (μ n)) (hY : ∀ n, MemLp (Y n) 2 (μ n))
    (hX0 : ∀ n, ∀ᵐ ω ∂μ n, 0 ≤ X n ω) (hY0 : ∀ n, ∀ᵐ ω ∂μ n, 0 ≤ Y n ω)
    (hpos : ∀ᶠ n in atTop, 0 < ∫ ω, X n ω ∂μ n + ∫ ω, Y n ω ∂μ n)
    (hvX : Tendsto (fun n => Var[X n; μ n] / (∫ ω, X n ω ∂μ n + ∫ ω, Y n ω ∂μ n) ^ 2)
      atTop (𝓝 0))
    (hvY : Tendsto (fun n => Var[Y n; μ n] / (∫ ω, X n ω ∂μ n + ∫ ω, Y n ω ∂μ n) ^ 2)
      atTop (𝓝 0)) {L : ℝ}
    (hL : Tendsto (fun n => (∫ ω, X n ω ∂μ n) / (∫ ω, X n ω ∂μ n + ∫ ω, Y n ω ∂μ n))
      atTop (𝓝 L)) :
    Tendsto (fun n => ∫ ω, X n ω / (X n ω + Y n ω) ∂μ n) atTop (𝓝 L) := by
  have h := (tendsto_integral_ratio_add_sub_ratio_integral hX hY hX0 hY0 hpos hvX hvY).add hL
  rw [zero_add] at h
  exact h.congr fun n => by ring

end RatioAsymptotic

/-! ### The paper's own formulation, eq. (ratio-asymp) -/

section RatioPaper

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {μ : ∀ n, Measure (Ω n)}

/-- **Continuous mapping for the alignment ratio** (the step "`y_{k,d} → y_0` in probability" of
the proof of Lemma "Asymptotic ratio of expectations", tex 1023–1028, in `θ`-form).
If `X_n/k_n → a` and `Y_n/m_n → b` in probability, `k_n/m_n → ρ ≠ 0` and `ρ a + b ≠ 0`, then

`X_n/(X_n+Y_n) → ρ a / (ρ a + b)` in probability.

(`m_n` plays the role of `d - k`.)  The hypothesis `k_n/m_n → ρ ≠ 0` forces `k_n ≠ 0 ≠ m_n` for
large `n`. -/
theorem tendstoInProb_ratio_of_tendstoInProb {X Y : ∀ n, Ω n → ℝ} {k m : ℕ → ℝ} {ρ a b : ℝ}
    (hρ : Tendsto (fun n => k n / m n) atTop (𝓝 ρ)) (hρ0 : ρ ≠ 0) (hab : ρ * a + b ≠ 0)
    (hXa : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => μ n {ω | ε ≤ |X n ω / k n - a|}) atTop (𝓝 0))
    (hYb : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => μ n {ω | ε ≤ |Y n ω / m n - b|}) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ n {ω | ε ≤ |X n ω / (X n ω + Y n ω) - ρ * a / (ρ * a + b)|})
        atTop (𝓝 0) := by
  intro ε hε
  have hgc : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.1 * p.2.1 / (p.1 * p.2.1 + p.2.2))
      (ρ, a, b) := by
    refine ContinuousAt.div ?_ ?_ hab
    · fun_prop
    · fun_prop
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousAt_iff.mp hgc ε hε
  have hev1 : ∀ᶠ n in atTop, |k n / m n - ρ| < δ := by
    have := (Metric.tendsto_nhds.mp hρ) δ hδ
    simpa [Real.dist_eq] using this
  have hev2 : ∀ᶠ n in atTop, k n / m n ≠ 0 := hρ.eventually_ne hρ0
  have hsum : Tendsto (fun n => μ n {ω | δ ≤ |X n ω / k n - a|}
      + μ n {ω | δ ≤ |Y n ω / m n - b|}) atTop (𝓝 0) := by
    simpa using (hXa δ hδ).add (hYb δ hδ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun n => zero_le) ?_
  filter_upwards [hev1, hev2] with n h1 h2
  have hk : k n ≠ 0 := fun h => h2 (by rw [h, zero_div])
  have hm : m n ≠ 0 := fun h => h2 (by rw [h, div_zero])
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  by_contra hcon
  rw [Set.mem_union, not_or] at hcon
  obtain ⟨hU, hV⟩ := hcon
  have hU' : |X n ω / k n - a| < δ := not_le.mp hU
  have hV' : |Y n ω / m n - b| < δ := not_le.mp hV
  have hdist : dist (k n / m n, X n ω / k n, Y n ω / m n) (ρ, a, b) < δ := by
    rw [Prod.dist_eq, Prod.dist_eq]
    simp only [Real.dist_eq]
    exact max_lt h1 (max_lt hU' hV')
  have hval : k n / m n * (X n ω / k n) / (k n / m n * (X n ω / k n) + Y n ω / m n)
      = X n ω / (X n ω + Y n ω) := by
    have e1 : k n / m n * (X n ω / k n) = X n ω / m n := by field_simp
    rw [e1, ← add_div, div_div_div_cancel_right₀ hm]
  have hlt := hδg hdist
  simp only [Real.dist_eq] at hlt
  rw [hval] at hlt
  exact absurd hω (not_le.mpr hlt)

variable [∀ n, IsProbabilityMeasure (μ n)]

/-- **Lemma "Asymptotic ratio of expectations", general form.**  Let `X_n, Y_n ≥ 0` a.s. be
a.e.-measurable, `X_n/k_n → a`, `Y_n/m_n → b` in probability, `k_n/m_n → ρ ≠ 0` and
`ρ a + b ≠ 0`.  Then `𝔼[X_n/(X_n+Y_n)] → ρ a / (ρ a + b)`.

This covers the boundary regimes `b = 0` (limit `1`) and `a = 0 < b` (limit `0`) which the paper
excludes by asserting `y_0 ∈ (0, ∞)`. -/
theorem tendsto_integral_ratio_of_tendstoInProb {X Y : ∀ n, Ω n → ℝ}
    (hX : ∀ n, AEMeasurable (X n) (μ n)) (hY : ∀ n, AEMeasurable (Y n) (μ n))
    (hX0 : ∀ n, ∀ᵐ ω ∂μ n, 0 ≤ X n ω) (hY0 : ∀ n, ∀ᵐ ω ∂μ n, 0 ≤ Y n ω)
    {k m : ℕ → ℝ} {ρ a b : ℝ}
    (hρ : Tendsto (fun n => k n / m n) atTop (𝓝 ρ)) (hρ0 : ρ ≠ 0) (hab : ρ * a + b ≠ 0)
    (hXa : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => μ n {ω | ε ≤ |X n ω / k n - a|}) atTop (𝓝 0))
    (hYb : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => μ n {ω | ε ≤ |Y n ω / m n - b|}) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, X n ω / (X n ω + Y n ω) ∂μ n) atTop (𝓝 (ρ * a / (ρ * a + b))) :=
  tendsto_integral_of_tendstoInProb_of_bounded (Y := fun n ω => X n ω / (X n ω + Y n ω))
    (A := 0) (B := 1) (fun n => (hX n).div ((hX n).add (hY n)))
    (fun n => by
      filter_upwards [hX0 n, hY0 n] with ω h1 h2
      exact ⟨div_nonneg h1 (add_nonneg h1 h2),
        div_le_one_of_le₀ (by linarith) (add_nonneg h1 h2)⟩)
    (tendstoInProb_ratio_of_tendstoInProb hρ hρ0 hab hXa hYb)

/-- **Lemma "Asymptotic ratio of expectations", eq. (ratio-asymp)** (tex 995–1009), in the paper's
own formulation.  `X_n = s^𝒟_{t+1}`, `Y_n = s^ℬ_{t+1}`, `k_n = k`, `m_n = d - k`,
`a = ℓ'_𝒟 > 0`, `b = ℓ'_ℬ ≥ 0`, `k_n/m_n → ρ > 0`.  If `X_n/k_n → a` and `Y_n/m_n → b` in
probability then

`𝔼[θ_{t+1}] = 𝔼[X_n/(X_n+Y_n)] → 1 / (1 + b / (ρ a))`. -/
theorem tendsto_integral_ratio_paper {X Y : ∀ n, Ω n → ℝ}
    (hX : ∀ n, AEMeasurable (X n) (μ n)) (hY : ∀ n, AEMeasurable (Y n) (μ n))
    (hX0 : ∀ n, ∀ᵐ ω ∂μ n, 0 ≤ X n ω) (hY0 : ∀ n, ∀ᵐ ω ∂μ n, 0 ≤ Y n ω)
    {k m : ℕ → ℝ} {ρ a b : ℝ}
    (hρ : Tendsto (fun n => k n / m n) atTop (𝓝 ρ)) (hρpos : 0 < ρ) (ha : 0 < a) (hb : 0 ≤ b)
    (hXa : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => μ n {ω | ε ≤ |X n ω / k n - a|}) atTop (𝓝 0))
    (hYb : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => μ n {ω | ε ≤ |Y n ω / m n - b|}) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, X n ω / (X n ω + Y n ω) ∂μ n) atTop (𝓝 (1 / (1 + b / (ρ * a)))) := by
  have hρa : 0 < ρ * a := mul_pos hρpos ha
  have hne : ρ * a + b ≠ 0 := (add_pos_of_pos_of_nonneg hρa hb).ne'
  have hEq : ρ * a / (ρ * a + b) = 1 / (1 + b / (ρ * a)) := by
    field_simp
  rw [← hEq]
  exact tendsto_integral_ratio_of_tendstoInProb hX hY hX0 hY0 hρ hρpos.ne' hne hXa hYb

/-- **Lemma "Asymptotic ratio of expectations", complete abstract form** (WLLN + continuous
mapping, exactly the paper's proof with the Gaussian variance bounds as hypotheses).
`X_n, Y_n ≥ 0` in `L²` with `Var(X_n) ≤ K₁ k_n`, `Var(Y_n) ≤ K₂ m_n` for large `n`
(`k_n, m_n → ∞`), `𝔼X_n/k_n → a > 0`, `𝔼Y_n/m_n → b ≥ 0`, `k_n/m_n → ρ > 0`.  Then
`𝔼[X_n/(X_n+Y_n)] → 1 / (1 + b / (ρ a))`. -/
theorem tendsto_integral_ratio_of_variance_bound {X Y : ∀ n, Ω n → ℝ}
    (hX : ∀ n, MemLp (X n) 2 (μ n)) (hY : ∀ n, MemLp (Y n) 2 (μ n))
    (hX0 : ∀ n, ∀ᵐ ω ∂μ n, 0 ≤ X n ω) (hY0 : ∀ n, ∀ᵐ ω ∂μ n, 0 ≤ Y n ω)
    {k m : ℕ → ℝ} (hk : Tendsto k atTop atTop) (hm : Tendsto m atTop atTop) {K₁ K₂ : ℝ}
    (hvX : ∀ᶠ n in atTop, Var[X n; μ n] ≤ K₁ * k n)
    (hvY : ∀ᶠ n in atTop, Var[Y n; μ n] ≤ K₂ * m n) {ρ a b : ℝ}
    (hρ : Tendsto (fun n => k n / m n) atTop (𝓝 ρ)) (hρpos : 0 < ρ) (ha : 0 < a) (hb : 0 ≤ b)
    (hEX : Tendsto (fun n => (∫ ω, X n ω ∂μ n) / k n) atTop (𝓝 a))
    (hEY : Tendsto (fun n => (∫ ω, Y n ω ∂μ n) / m n) atTop (𝓝 b)) :
    Tendsto (fun n => ∫ ω, X n ω / (X n ω + Y n ω) ∂μ n) atTop (𝓝 (1 / (1 + b / (ρ * a)))) :=
  tendsto_integral_ratio_paper (fun n => (hX n).aemeasurable) (fun n => (hY n).aemeasurable)
    hX0 hY0 hρ hρpos ha hb (wlln_block_average hX hk hvX hEX) (wlln_block_average hY hm hvY hEY)

/-- Non-vacuity of `tendsto_integral_ratio_of_variance_bound` (hence of the WLLN and of
`tendsto_integral_ratio_paper`): the deterministic family `X_n = 2(n+1)`, `Y_n = n+1`,
`k_n = m_n = n+1` satisfies all hypotheses with `ρ = 1`, `a = 2`, `b = 1`, `K₁ = K₂ = 0`. -/
example (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)] :
    Tendsto (fun n : ℕ => ∫ _ω : Ω n, 2 * ((n : ℝ) + 1) / (2 * ((n : ℝ) + 1) + ((n : ℝ) + 1)) ∂μ n)
      atTop (𝓝 (1 / (1 + 1 / (1 * 2)))) := by
  have hk : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hvar : ∀ (c : ℝ) (n : ℕ), Var[fun _ : Ω n => c; μ n] ≤ 0 * ((n : ℝ) + 1) := by
    intro c n
    rw [variance_eq_sub (memLp_const c)]
    simp
  refine tendsto_integral_ratio_of_variance_bound (μ := μ) (X := fun n _ => 2 * ((n : ℝ) + 1))
    (Y := fun n _ => (n : ℝ) + 1) (k := fun n => (n : ℝ) + 1) (m := fun n => (n : ℝ) + 1)
    (ρ := 1) (a := 2) (b := 1) (K₁ := 0) (K₂ := 0)
    (fun n => memLp_const _) (fun n => memLp_const _)
    (fun n => Eventually.of_forall fun _ => by positivity)
    (fun n => Eventually.of_forall fun _ => by positivity) hk hk
    (Eventually.of_forall fun n => hvar _ n) (Eventually.of_forall fun n => hvar _ n)
    ?_ one_pos two_pos zero_le_one ?_ ?_
  · refine tendsto_const_nhds.congr fun n => ?_
    rw [div_self (by positivity)]
  · refine tendsto_const_nhds.congr fun n => ?_
    rw [integral_const]
    have h : ((n : ℝ) + 1) ≠ 0 := by positivity
    simp
    field_simp
  · refine tendsto_const_nhds.congr fun n => ?_
    rw [integral_const]
    have h : ((n : ℝ) + 1) ≠ 0 := by positivity
    simp
    field_simp

end RatioPaper

/-! ## Part 4. The displayed "consequence" of the ratio lemma (tex 1038–1048)

The paper's display reads (with `a' = ℓ'_𝒟`, `b' = ℓ'_ℬ` the limits of the normalised conditional
expectations of `s^𝒟_{t+1}`, `s^ℬ_{t+1}` and `a, b` the limits of the normalised `s^𝒟_t`, `s^ℬ_t`)

`lim 𝔼[θ_{t+1}|x_t] = 1/(1 + b'/(ρ a')) < lim θ_t = 1/(1 - b/(ρ a))  ⟹  lim 𝔼[f_t(η_t)|x_t] < 0`.

* The `-` sign is a typo: `θ = 1/(1 + (1/ρ)(s^ℬ/(d-k))/(s^𝒟/k))`
  (`Concentration.ratio_eq_one_div_one_add`; with `-` the identity is false,
  `Concentration.ratio_ne_one_div_one_sub`).
* After normalising `𝔼 f_t` by `k (d-k)` the implication is in fact an equivalence *between the
  limits* (`Concentration.ratio_limit_lt_iff`); at finite `d` the exact statement is
  `Concentration.ratio_lt_ratio_iff` / `Concentration.ratio_sub_ratio_eq`.
* What the paper then uses ("it suffices to analyse the sign of `𝔼[f_t | x_t]`") is the converse
  direction, from the sign of `𝔼 f_t` at each finite `d` to a *strict* inequality between limits.
  This is not justified: a strict inequality for every `d` only gives a non-strict inequality in
  the limit (`strict_drift_not_preserved_in_limit`).  The correct statements are
  `eventually_integral_ratio_add_lt_add_of_le` (non-strict, no margin needed),
  `eventually_integral_ratio_add_lt_of_gap` (strict, for all large `d`, under a uniform margin) and
  `eventually_integral_ratio_add_lt_of_tendsto_lt` (strict limits ⟹ strict for all large `d`). -/

namespace Concentration

/-- If `E_n - R_n → 0` and eventually `R_n ≤ θ_n`, then for every `c > 0` eventually
`E_n < θ_n + c`. -/
theorem eventually_lt_add_of_tendsto_sub {E R θ : ℕ → ℝ}
    (h : Tendsto (fun n => E n - R n) atTop (𝓝 0)) (hle : ∀ᶠ n in atTop, R n ≤ θ n) {c : ℝ}
    (hc : 0 < c) : ∀ᶠ n in atTop, E n < θ n + c := by
  filter_upwards [(tendsto_order.1 h).2 c hc, hle] with n h1 h2
  linarith

/-- The identity behind eq. (theta-next)/(ratio-asymp), with the correct `+` sign:
`x/(x+y) = 1 / (1 + (1/ρ) · (y/m)/(x/k))` where `ρ = k/m`
(`x = s^𝒟`, `y = s^ℬ`, `m = d - k`). -/
theorem ratio_eq_one_div_one_add {x y k m : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (hk : 0 < k)
    (hm : 0 < m) : x / (x + y) = 1 / (1 + 1 / (k / m) * ((y / m) / (x / k))) := by
  have hxy : x + y ≠ 0 := (add_pos_of_pos_of_nonneg hx hy).ne'
  field_simp

/-- The sign typo in the display at tex 1043: with `1 - …` in place of `1 + …` the formula for
`θ_t` is false (e.g. `x = 2`, `y = k = m = 1`: `2/3 ≠ 2`). -/
theorem ratio_ne_one_div_one_sub :
    ¬ ∀ x y k m : ℝ, 0 < x → 0 ≤ y → 0 < k → 0 < m →
      x / (x + y) = 1 / (1 - 1 / (k / m) * ((y / m) / (x / k))) := by
  intro h
  have h2 := h 2 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h2

/-- Exact finite-`d` link between the ratio of expectations and the comparison functional:
with `x = s^𝒟_t`, `y = s^ℬ_t`, `x' = 𝔼 s^𝒟_{t+1}`, `y' = 𝔼 s^ℬ_{t+1}`,
`x'/(x'+y') - x/(x+y) = (y x' - y' x) / ((x'+y')(x+y)) = 𝔼[f_t] / (𝔼[s_{t+1}] · s_t)`. -/
theorem ratio_sub_ratio_eq {x y x' y' : ℝ} (hs : x + y ≠ 0) (hs' : x' + y' ≠ 0) :
    x' / (x' + y') - x / (x + y) = (y * x' - y' * x) / ((x' + y') * (x + y)) := by
  field_simp
  ring

/-- Exact finite-`d` equivalence: the ratio of expectations decreases iff `𝔼[f_t] < 0`. -/
theorem ratio_lt_ratio_iff {x y x' y' : ℝ} (hs : 0 < x + y) (hs' : 0 < x' + y') :
    x' / (x' + y') < x / (x + y) ↔ y * x' - y' * x < 0 := by
  rw [div_lt_div_iff₀ hs' hs]
  constructor <;> intro h <;> linarith

/-- The (corrected) display at tex 1040–1048, as an equivalence between the limits:
`1/(1 + b'/(ρ a')) < 1/(1 + b/(ρ a)) ↔ b a' - b' a < 0`, where `b a' - b' a` is the limit of
`𝔼[f_t | x_t] / (k (d - k))`. -/
theorem ratio_limit_lt_iff {ρ a b a' b' : ℝ} (hρ : 0 < ρ) (ha : 0 < a) (ha' : 0 < a')
    (hb : 0 ≤ b) (hb' : 0 ≤ b') :
    1 / (1 + b' / (ρ * a')) < 1 / (1 + b / (ρ * a)) ↔ b * a' - b' * a < 0 := by
  have h1 : 0 < 1 + b' / (ρ * a') := by positivity
  have h2 : 0 < 1 + b / (ρ * a) := by positivity
  rw [one_div_lt_one_div h1 h2, add_lt_add_iff_left,
    div_lt_div_iff₀ (mul_pos hρ ha) (mul_pos hρ ha')]
  constructor
  · intro h
    have : ρ * (b * a' - b' * a) < 0 := by linarith
    by_contra hcon
    have := mul_nonneg hρ.le (not_lt.mp hcon)
    linarith
  · intro h
    have := mul_neg_of_pos_of_neg hρ h
    linarith

end Concentration

section Consequence

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {μ : ∀ n, Measure (Ω n)}
  [∀ n, IsProbabilityMeasure (μ n)]

/-- **Correct non-strict form of the "consequence".**  Under the concentration hypotheses of
`tendsto_integral_ratio_add_sub_ratio_integral`, if the ratio of expectations is eventually
`≤ θ_n` (e.g. because `𝔼[f_t | x_t] ≤ 0` for every `d`), then for every margin `c > 0`,
`𝔼[X_n/(X_n+Y_n)] < θ_n + c` for all large `n` — i.e. `limsup (𝔼[θ_{t+1}] - θ_t) ≤ 0`. -/
theorem eventually_integral_ratio_add_lt_add_of_le {X Y : ∀ n, Ω n → ℝ}
    (hX : ∀ n, MemLp (X n) 2 (μ n)) (hY : ∀ n, MemLp (Y n) 2 (μ n))
    (hX0 : ∀ n, ∀ᵐ ω ∂μ n, 0 ≤ X n ω) (hY0 : ∀ n, ∀ᵐ ω ∂μ n, 0 ≤ Y n ω)
    (hpos : ∀ᶠ n in atTop, 0 < ∫ ω, X n ω ∂μ n + ∫ ω, Y n ω ∂μ n)
    (hvX : Tendsto (fun n => Var[X n; μ n] / (∫ ω, X n ω ∂μ n + ∫ ω, Y n ω ∂μ n) ^ 2)
      atTop (𝓝 0))
    (hvY : Tendsto (fun n => Var[Y n; μ n] / (∫ ω, X n ω ∂μ n + ∫ ω, Y n ω ∂μ n) ^ 2)
      atTop (𝓝 0)) {θ : ℕ → ℝ}
    (hle : ∀ᶠ n in atTop,
      (∫ ω, X n ω ∂μ n) / (∫ ω, X n ω ∂μ n + ∫ ω, Y n ω ∂μ n) ≤ θ n) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n in atTop, ∫ ω, X n ω / (X n ω + Y n ω) ∂μ n < θ n + c :=
  Concentration.eventually_lt_add_of_tendsto_sub
    (tendsto_integral_ratio_add_sub_ratio_integral hX hY hX0 hY0 hpos hvX hvY) hle hc

/-- **Correct strict form of the "consequence".**  Under the concentration hypotheses, if the
ratio of expectations stays below `θ_n` by a *uniform* margin `c > 0` (by
`Concentration.ratio_sub_ratio_eq`: `𝔼[f_t] ≤ -c · 𝔼[s_{t+1}] · s_t`), then
`𝔼[X_n/(X_n+Y_n)] < θ_n` for all large `n`: the expected alignment strictly decreases for every
sufficiently large dimension. -/
theorem eventually_integral_ratio_add_lt_of_gap {X Y : ∀ n, Ω n → ℝ}
    (hX : ∀ n, MemLp (X n) 2 (μ n)) (hY : ∀ n, MemLp (Y n) 2 (μ n))
    (hX0 : ∀ n, ∀ᵐ ω ∂μ n, 0 ≤ X n ω) (hY0 : ∀ n, ∀ᵐ ω ∂μ n, 0 ≤ Y n ω)
    (hpos : ∀ᶠ n in atTop, 0 < ∫ ω, X n ω ∂μ n + ∫ ω, Y n ω ∂μ n)
    (hvX : Tendsto (fun n => Var[X n; μ n] / (∫ ω, X n ω ∂μ n + ∫ ω, Y n ω ∂μ n) ^ 2)
      atTop (𝓝 0))
    (hvY : Tendsto (fun n => Var[Y n; μ n] / (∫ ω, X n ω ∂μ n + ∫ ω, Y n ω ∂μ n) ^ 2)
      atTop (𝓝 0)) {θ : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hgap : ∀ᶠ n in atTop,
      (∫ ω, X n ω ∂μ n) / (∫ ω, X n ω ∂μ n + ∫ ω, Y n ω ∂μ n) ≤ θ n - c) :
    ∀ᶠ n in atTop, ∫ ω, X n ω / (X n ω + Y n ω) ∂μ n < θ n := by
  have h := eventually_integral_ratio_add_lt_add_of_le hX hY hX0 hY0 hpos hvX hvY
    (θ := fun n => θ n - c) hgap hc
  simpa using h

/-- **Limit form of the "consequence"** (the direction that is true): if the ratio of expectations
converges to `L'`, the current alignment `θ_n` converges to `L`, and `L' < L`, then
`𝔼[X_n/(X_n+Y_n)] < θ_n` for all large `n`. -/
theorem eventually_integral_ratio_add_lt_of_tendsto_lt {X Y : ∀ n, Ω n → ℝ}
    (hX : ∀ n, MemLp (X n) 2 (μ n)) (hY : ∀ n, MemLp (Y n) 2 (μ n))
    (hX0 : ∀ n, ∀ᵐ ω ∂μ n, 0 ≤ X n ω) (hY0 : ∀ n, ∀ᵐ ω ∂μ n, 0 ≤ Y n ω)
    (hpos : ∀ᶠ n in atTop, 0 < ∫ ω, X n ω ∂μ n + ∫ ω, Y n ω ∂μ n)
    (hvX : Tendsto (fun n => Var[X n; μ n] / (∫ ω, X n ω ∂μ n + ∫ ω, Y n ω ∂μ n) ^ 2)
      atTop (𝓝 0))
    (hvY : Tendsto (fun n => Var[Y n; μ n] / (∫ ω, X n ω ∂μ n + ∫ ω, Y n ω ∂μ n) ^ 2)
      atTop (𝓝 0)) {θ : ℕ → ℝ} {L L' : ℝ}
    (hL' : Tendsto (fun n => (∫ ω, X n ω ∂μ n) / (∫ ω, X n ω ∂μ n + ∫ ω, Y n ω ∂μ n))
      atTop (𝓝 L'))
    (hθ : Tendsto θ atTop (𝓝 L)) (hlt : L' < L) :
    ∀ᶠ n in atTop, ∫ ω, X n ω / (X n ω + Y n ω) ∂μ n < θ n :=
  (tendsto_integral_ratio_add_of_tendsto_ratio_integral hX hY hX0 hY0 hpos hvX hvY
    hL').eventually_lt hθ hlt

/-- **Strictness is lost in the limit** (counterexample to the passage from "`𝔼[f_t] < 0` for every
`d`" to "`lim 𝔼[θ_{t+1}] < lim θ_t`").  Take the deterministic blocks `X_n = 1`, `Y_n = 1/(n+1)`
and the current alignment `θ_n = 1` (abstract shadow of a state `x_t` lying in the dominant
subspace with vanishing normalised bulk noise).  For every `n` the expected next alignment
`𝔼[X_n/(X_n+Y_n)]` is `< 1 = θ_n`, yet its limit is `1 = lim θ_n`. -/
theorem strict_drift_not_preserved_in_limit (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] :
    (∀ n : ℕ, ∫ _ω : Ω n, (1 : ℝ) / (1 + 1 / ((n : ℝ) + 1)) ∂μ n < 1) ∧
      Tendsto (fun n : ℕ => ∫ _ω : Ω n, (1 : ℝ) / (1 + 1 / ((n : ℝ) + 1)) ∂μ n) atTop (𝓝 1) := by
  have hc : ∀ n : ℕ, ∫ _ω : Ω n, (1 : ℝ) / (1 + 1 / ((n : ℝ) + 1)) ∂μ n
      = 1 / (1 + 1 / ((n : ℝ) + 1)) := fun n => by
    rw [integral_const]; simp
  refine ⟨fun n => ?_, ?_⟩
  · rw [hc, div_lt_one (by positivity)]
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · simp only [hc]
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / (1 + 1 / ((n : ℝ) + 1))) atTop
        (𝓝 (1 / (1 + 0))) :=
      tendsto_const_nhds.div (tendsto_const_nhds.add h0) (by norm_num)
    simpa using h1

end Consequence

/-! ## Part 5. Interface with `Defs.lean`: `𝔼[θ_{t+1} | x_t]` versus `Spec.thetaBarNext`

The two-block transfer theorems specialised to `X = s^𝒟_{t+1}`, `Y = s^ℬ_{t+1}` (functions of the
realised noise `ζ` in the eigenbasis).  The identification of the conditional expectations
`𝔼[s^S_{t+1} | x_t]` with `Spec.EsNext` (Lemma "Elementwise expectation") and the variance bounds
(Lemma "Variance of Gaussian Forms") are hypotheses here; they are proved in other files. -/

namespace Concentration

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Finite-`d` quantitative transfer for the alignment.**  For one SGD step with realised noise
`ζ : Ω → ι → ℝ` (eigen-coordinates), if `𝔼[s^S_{t+1}] = Spec.EsNext` for `S = 𝒟, ℬ` and
`𝔼[s_{t+1}] > 0`, then

`|𝔼[θ_{t+1}] - thetaBarNext| ≤ (√Var(s^𝒟_{t+1}) + √Var(s^ℬ_{t+1})) / (2 𝔼[s_{t+1}])`. -/
theorem abs_integral_theta_sub_thetaBarNext_le (P : Spec ι) (N : Noise ι) {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (η : ℝ) (c : ι → ℝ)
    (ζ : Ω → ι → ℝ)
    (hD : MemLp (fun ω => P.sD (P.cNext η c (ζ ω))) 2 μ)
    (hB : MemLp (fun ω => P.sB (P.cNext η c (ζ ω))) 2 μ)
    (hED : ∫ ω, P.sD (P.cNext η c (ζ ω)) ∂μ = P.EsNext N P.D η c)
    (hEB : ∫ ω, P.sB (P.cNext η c (ζ ω)) ∂μ = P.EsNext N P.B η c)
    (hpos : 0 < P.EsNext N P.D η c + P.EsNext N P.B η c) :
    |∫ ω, P.theta (P.cNext η c (ζ ω)) ∂μ - P.thetaBarNext N η c|
      ≤ (√Var[fun ω => P.sD (P.cNext η c (ζ ω)); μ]
          + √Var[fun ω => P.sB (P.cNext η c (ζ ω)); μ])
        / (2 * (P.EsNext N P.D η c + P.EsNext N P.B η c)) := by
  have h := abs_integral_ratio_add_sub_ratio_integral_le hD hB
    (Eventually.of_forall fun ω => P.sD_nonneg _) (Eventually.of_forall fun ω => P.sB_nonneg _)
    (by rw [hED, hEB]; exact hpos)
  rw [hED, hEB] at h
  exact h

/-- **Asymptotic transfer `𝔼[θ_{t+1} | x_t] - thetaBarNext → 0`** along a sequence of problems
(index `n`, dimension `|ι n|`), under `𝔼[s^S_{t+1}] = Spec.EsNext` and
`Var(s^S_{t+1}) / (𝔼 s_{t+1})² → 0` for `S = 𝒟, ℬ`. -/
theorem tendsto_integral_theta_sub_thetaBarNext {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    [∀ n, DecidableEq (ι n)] {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {μ : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
    (P : ∀ n, Spec (ι n)) (N : ∀ n, Noise (ι n)) (η : ℕ → ℝ) (c : ∀ n, ι n → ℝ)
    (ζ : ∀ n, Ω n → ι n → ℝ)
    (hD : ∀ n, MemLp (fun ω => (P n).sD ((P n).cNext (η n) (c n) (ζ n ω))) 2 (μ n))
    (hB : ∀ n, MemLp (fun ω => (P n).sB ((P n).cNext (η n) (c n) (ζ n ω))) 2 (μ n))
    (hED : ∀ n, ∫ ω, (P n).sD ((P n).cNext (η n) (c n) (ζ n ω)) ∂μ n
      = (P n).EsNext (N n) (P n).D (η n) (c n))
    (hEB : ∀ n, ∫ ω, (P n).sB ((P n).cNext (η n) (c n) (ζ n ω)) ∂μ n
      = (P n).EsNext (N n) (P n).B (η n) (c n))
    (hpos : ∀ᶠ n in atTop,
      0 < (P n).EsNext (N n) (P n).D (η n) (c n) + (P n).EsNext (N n) (P n).B (η n) (c n))
    (hvD : Tendsto (fun n => Var[fun ω => (P n).sD ((P n).cNext (η n) (c n) (ζ n ω)); μ n]
      / ((P n).EsNext (N n) (P n).D (η n) (c n) + (P n).EsNext (N n) (P n).B (η n) (c n)) ^ 2)
      atTop (𝓝 0))
    (hvB : Tendsto (fun n => Var[fun ω => (P n).sB ((P n).cNext (η n) (c n) (ζ n ω)); μ n]
      / ((P n).EsNext (N n) (P n).D (η n) (c n) + (P n).EsNext (N n) (P n).B (η n) (c n)) ^ 2)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, (P n).theta ((P n).cNext (η n) (c n) (ζ n ω)) ∂μ n
      - (P n).thetaBarNext (N n) (η n) (c n)) atTop (𝓝 0) := by
  have h := tendsto_integral_ratio_add_sub_ratio_integral hD hB
    (fun n => Eventually.of_forall fun ω => (P n).sD_nonneg _)
    (fun n => Eventually.of_forall fun ω => (P n).sB_nonneg _)
    (by simpa only [hED, hEB] using hpos) (by simpa only [hED, hEB] using hvD)
    (by simpa only [hED, hEB] using hvB)
  simp only [hED, hEB] at h
  exact h

end Concentration

end SuspiciousAlignment
