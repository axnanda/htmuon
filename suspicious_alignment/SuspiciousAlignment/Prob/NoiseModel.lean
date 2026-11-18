import Mathlib
import SuspiciousAlignment.Defs

/-!
# Suspicious Alignment of SGD — the probability layer for the one-step results

Paper: Deng et al., *Suspicious Alignment of SGD* (arXiv:2601.11789v2), §3.2 (setup), Appendix A.2
(incl. the Remark on null sets), Lemma "Elementwise expectation of `x_{t+1}`", Lemma "Quadratic form
for step size condition", Theorem 10 ("Condition differences on different alignment regime").

## The model

The paper writes `𝔼[· | x_t]` for expectations over the SGD noise `ξ_t ~ 𝒩(0, Σ)` at a *given*
state `x_t`.  Here these become honest Bochner integrals `∫ ω, f ω ∂μ` over a probability space
`(Ω, μ)`:

* the noise is a family `ζ : ι → Ω → ℝ` of real random variables, `ζ i = ⟪ξ, u_i⟫` being the
  coordinate of the noise along the `i`-th Hessian eigenvector;
* `IsNoise N μ ζ` packages what the one-step lemmas need: every `ζ i` is in `L²(μ)`,
  `𝔼[ζ i] = 0` and `𝔼[ζ i ²] = κ_i² = N.kap2 i`.  No Gaussianity, no independence between the
  coordinates and no information on the off-diagonal covariances `C_{ij}` is used — in agreement
  with the paper's sentence "SGD with arbitrary noise of finite second moment" (§3.2);
* the state `x_t`, i.e. its eigen-coefficients `c : ι → ℝ`, is **deterministic**.  This is exactly
  what "conditioning on `x_t`" means when the noise `ξ_t` is independent of `x_t`:
  `𝔼[g(x_t, ξ_t) | x_t] = G(x_t)` with `G(c) = ∫ ω, g(c, ξ_t(ω)) ∂μ`, the integral over the noise
  with the state frozen.  Section "Genuine conditional expectations" below proves this bridge for
  the elementwise lemma: for a random `σ(x_t)`-measurable state and noise independent of it, the
  Mathlib conditional expectation `μ[· | m]` is the frozen-state formula evaluated at the state.

The realised noise vector at `ω` is written `fun i => ζ i ω`.

## Main results

* `IsNoise` and its basic API (`IsNoise.integrable`, `IsNoise.integrable_sq`, …).
* Integrability: `integrable_cNext_sq`, `integrable_mom_cNext`, `integrable_sD_cNext`,
  `integrable_sB_cNext`, `integrable_s_cNext`, `integrable_fCompare`, `integrable_loss_cNextProj`,
  `integrable_theta_cNext`.
* Lemma "Elementwise expectation": `integral_cNext`, `integral_cNext_sq`,
  `integral_lam_sq_mul_cNext_sq`, `integral_mom_two_cNext` (`= Spec.EsNext`), `integral_sD_cNext`
  (eq. (Eat)), `integral_sB_cNext` (eq. (Ebt)), `integral_s_cNext`.
* Lemma "Quadratic form": `integral_fCompare`.
* Theorem 10: `integral_loss_cNextProj_sub` and `integral_loss_cNextProj_sub_neg_iff` (+ the `𝒟`/`ℬ`
  specialisations).
* Remark of A.2: `measure_mom_two_cNext_eq_zero` (+ corollaries for `s^𝒟_{t+1}`, `s_{t+1}`,
  atomless and Gaussian coordinates), the failure for degenerate noise
  (`measure_sD_cNext_eq_zero_eq_one_of_degenerate`, `exists_gaussian_noise_sD_cNext_eq_zero`), and
  `0 ≤ 𝔼[θ_{t+1}] ≤ 1`.
* `𝔼[θ_{t+1}] ≠ thetaBarNext` at finite `d`: `exists_integral_theta_cNext_ne_thetaBarNext`.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace SuspiciousAlignment

variable {ι : Type*} {Ω : Type*} [MeasurableSpace Ω]

/-- **The noise model of the one-step lemmas.**  `ζ i : Ω → ℝ` is the coordinate `⟪ξ_t, u_i⟫` of
the SGD noise along the `i`-th eigenvector of the Hessian.  `IsNoise N μ ζ` says that every
coordinate has a finite second moment, mean zero and second moment `κ_i² = N.kap2 i`
(`= u_iᵀ Σ u_i`, paper §3.2).

This is all that Lemmas "Elementwise expectation", "Quadratic form" and Theorem 10 use.  The paper
takes `ξ_t ~ 𝒩(0, Σ)`, for which these three properties hold; neither Gaussianity nor any
assumption on the joint law of different coordinates is needed. -/
structure IsNoise (N : Noise ι) (μ : Measure Ω) (ζ : ι → Ω → ℝ) : Prop where
  /-- each noise coordinate has a finite second moment -/
  memLp : ∀ i, MemLp (ζ i) 2 μ
  /-- the noise is centred: `𝔼[ζ_i] = 0` -/
  integral_eq_zero : ∀ i, ∫ ω, ζ i ω ∂μ = 0
  /-- the second moment of the `i`-th coordinate is `κ_i²` -/
  integral_sq : ∀ i, ∫ ω, ζ i ω ^ 2 ∂μ = N.kap2 i

namespace IsNoise

variable {N : Noise ι} {μ : Measure Ω} {ζ : ι → Ω → ℝ}

theorem aestronglyMeasurable (h : IsNoise N μ ζ) (i : ι) : AEStronglyMeasurable (ζ i) μ :=
  (h.memLp i).aestronglyMeasurable

theorem aemeasurable (h : IsNoise N μ ζ) (i : ι) : AEMeasurable (ζ i) μ :=
  (h.aestronglyMeasurable i).aemeasurable

/-- The realised noise vector `ω ↦ (ζ_i(ω))_i` is a.e. measurable. -/
theorem aemeasurable_vec [Countable ι] (h : IsNoise N μ ζ) :
    AEMeasurable (fun ω i => ζ i ω) μ :=
  AEMeasurable.of_eval fun i => h.aemeasurable i

theorem integrable_sq (h : IsNoise N μ ζ) (i : ι) : Integrable (fun ω => ζ i ω ^ 2) μ :=
  (h.memLp i).integrable_sq

theorem integrable [IsFiniteMeasure μ] (h : IsNoise N μ ζ) (i : ι) : Integrable (ζ i) μ :=
  (h.memLp i).integrable one_le_two

/-- The variance of the `i`-th noise coordinate is `κ_i²`. -/
theorem variance_eq (h : IsNoise N μ ζ) (i : ι) : Var[ζ i; μ] = N.kap2 i := by
  rw [variance_of_integral_eq_zero (h.aemeasurable i) (h.integral_eq_zero i)]
  exact h.integral_sq i

/-- A coordinate with `κ_i² = 0` vanishes almost surely. -/
theorem ae_eq_zero_of_kap2_eq_zero (h : IsNoise N μ ζ) {i : ι} (hi : N.kap2 i = 0) :
    ∀ᵐ ω ∂μ, ζ i ω = 0 := by
  have h0 : ∫ ω, ζ i ω ^ 2 ∂μ = 0 := by rw [h.integral_sq i, hi]
  have h1 := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (ζ i ω)) (h.integrable_sq i)).mp h0
  filter_upwards [h1] with ω hω
  simpa using hω

end IsNoise

variable [Fintype ι] [DecidableEq ι]

/-! ### Deterministic algebra used below -/

namespace NoiseModel

variable (P : Spec ι) (N : Noise ι)

/-- Expansion of the square of the next coordinate `c_{i,t+1} = (1 - ηλ_i) c_i - η ζ_i`. -/
theorem cNext_sq (η : ℝ) (c z : ι → ℝ) (i : ι) :
    P.cNext η c z i ^ 2 = ((1 - η * P.lam i) * c i) ^ 2
      + (-(2 * η * ((1 - η * P.lam i) * c i))) * z i + η ^ 2 * z i ^ 2 := by
  simp only [Spec.cNext]; ring

/-- `Spec.EsNext` collected by powers of `η`:
`∑_S λ²c² - 2η ∑_S λ³c² + η² (∑_S λ⁴c² + ∑_S λ²κ²)`. -/
theorem EsNext_expand (S : Finset ι) (η : ℝ) (c : ι → ℝ) :
    P.EsNext N S η c = P.mom S 2 c - 2 * η * P.mom S 3 c
      + η ^ 2 * (P.mom S 4 c + ∑ i ∈ S, P.lam i ^ 2 * N.kap2 i) := by
  simp only [Spec.EsNext, Spec.mom]
  rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The algebra behind Lemma "Quadratic form":
`s^ℬ 𝔼[s^𝒟_{t+1}] - 𝔼[s^ℬ_{t+1}] s^𝒟 = p_t η² + q_t η`. -/
theorem sB_mul_EsNext_sub (η : ℝ) (c : ι → ℝ) :
    P.sB c * P.EsNext N P.D η c - P.EsNext N P.B η c * P.sD c
      = P.pCoef N c * η ^ 2 + P.qCoef c * η := by
  rw [EsNext_expand, EsNext_expand]
  simp only [Spec.pCoef, Spec.qCoef, Spec.sD, Spec.sB, Spec.tauD, Spec.tauB, Spec.eD, Spec.eB]
  ring

/-- The loss change of an `S`-projected step only involves the coordinates in `S`:
`L(x⁺) - L(x) = ½ ∑_{i∈S} λ_i (c_{i,t+1}² - c_i²)`. -/
theorem loss_cNextProj_sub (S : Finset ι) (η : ℝ) (c z : ι → ℝ) :
    P.loss (P.cNextProj S η c z) - P.loss c
      = 1 / 2 * (P.mom S 1 (P.cNext η c z) - P.mom S 1 c) := by
  have hterm : ∀ i, P.lam i * P.cNextProj S η c z i ^ 2 - P.lam i * c i ^ 2
      = if i ∈ S then P.lam i ^ 1 * P.cNext η c z i ^ 2 - P.lam i ^ 1 * c i ^ 2 else 0 := by
    intro i
    by_cases hi : i ∈ S <;> simp [Spec.cNextProj, Spec.cNext, hi]
  simp only [Spec.loss, Spec.mom]
  rw [← mul_sub, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_ite_mem, Finset.univ_inter]

/-- The projected step with `S = univ` is the plain SGD step. -/
theorem cNextProj_univ (η : ℝ) (c z : ι → ℝ) :
    P.cNextProj Finset.univ η c z = P.cNext η c z := by
  funext i; simp [Spec.cNextProj, Spec.cNext]

/-- The expected loss change written out, as a function of the expected energies. -/
theorem half_sum_sub_eq_expLossChange (S : Finset ι) (η : ℝ) (c : ι → ℝ) :
    1 / 2 * (∑ i ∈ S, P.lam i ^ 1 * ((1 - η * P.lam i) ^ 2 * c i ^ 2 + η ^ 2 * N.kap2 i)
        - P.mom S 1 c) = P.expLossChange N S η c := by
  simp only [Spec.expLossChange, Spec.mom, Spec.nLoss]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- If `∑_S λ^p c² > 0` then `∑_S λ^q c² > 0` (both say that `c` does not vanish on `S`). -/
theorem mom_pos_of_mom_pos {S : Finset ι} {p : ℕ} {c : ι → ℝ} (h : 0 < P.mom S p c) (q : ℕ) :
    0 < P.mom S q c := by
  have hex : ∃ i ∈ S, 0 < P.lam i ^ p * c i ^ 2 := by
    by_contra hcon
    push Not at hcon
    exact absurd h (not_lt.mpr (Finset.sum_nonpos hcon))
  obtain ⟨i, hi, hpos⟩ := hex
  have hc : 0 < c i ^ 2 := by
    rcases (sq_nonneg (c i)).eq_or_lt with h0 | h0
    · rw [← h0] at hpos; simp at hpos
    · exact h0
  exact Finset.sum_pos' (fun j _ => mul_nonneg (pow_nonneg (P.lam_pos j).le _) (sq_nonneg _))
    ⟨i, hi, mul_pos (pow_pos (P.lam_pos i) _) hc⟩

theorem nLoss_nonneg (S : Finset ι) : 0 ≤ P.nLoss N S :=
  Finset.sum_nonneg fun i _ => mul_nonneg (P.lam_pos i).le (Spec.kap2_nonneg N i)

/-- The algebra of Theorem 10: when the denominator `τ^S + n^loss_S` of `η^loss_S` is positive,
`-η s^S + (η²/2)(τ^S + n^loss_S) < 0 ↔ 0 < η < η^loss_S`, for every real `η`. -/
theorem expLossChange_neg_iff (S : Finset ι) (η : ℝ) (c : ι → ℝ)
    (hden : 0 < P.mom S 3 c + P.nLoss N S) :
    P.expLossChange N S η c < 0 ↔ 0 < η ∧ η < P.etaLoss N S c := by
  have hs : 0 ≤ P.mom S 2 c := P.mom_nonneg S 2 c
  have hfac : P.expLossChange N S η c
      = η * (η / 2 * (P.mom S 3 c + P.nLoss N S) - P.mom S 2 c) := by
    simp only [Spec.expLossChange]; ring
  unfold Spec.etaLoss
  rw [hfac, lt_div_iff₀ hden]
  constructor
  · intro h
    have hη : 0 < η := by
      by_contra hη
      rw [not_lt] at hη
      have : 0 ≤ η * (η / 2 * (P.mom S 3 c + P.nLoss N S) - P.mom S 2 c) :=
        mul_nonneg_of_nonpos_of_nonpos hη (by nlinarith)
      linarith
    refine ⟨hη, ?_⟩
    by_contra hcon
    rw [not_lt] at hcon
    have : 0 ≤ η * (η / 2 * (P.mom S 3 c + P.nLoss N S) - P.mom S 2 c) :=
      mul_nonneg hη.le (by linarith)
    linarith
  · rintro ⟨hη, h⟩
    exact mul_neg_of_pos_of_neg hη (by linarith)

/-- If the state has no component in `S` then no step size makes the written-out expected loss
change negative: it equals `(η²/2) n^loss_S ≥ 0`. -/
theorem expLossChange_nonneg_of_mom_eq_zero (S : Finset ι) (η : ℝ) (c : ι → ℝ)
    (h : P.mom S 2 c = 0) : 0 ≤ P.expLossChange N S η c := by
  simp only [Spec.expLossChange, h, mul_zero, zero_add]
  exact mul_nonneg (by positivity) (add_nonneg (P.mom_nonneg S 3 c) (nLoss_nonneg P N S))

/-- For `η ≠ 0`, the `i`-th term of the next block energy vanishes exactly on the hyperplane
`ζ_i = (1 - ηλ_i) c_i / η` (the set `𝒱` of the Remark in A.2 is the intersection over `i ∈ 𝒟`). -/
theorem lam_sq_mul_cNext_sq_eq_zero_iff {η : ℝ} (hη : η ≠ 0) (c z : ι → ℝ) (i : ι) :
    P.lam i ^ 2 * P.cNext η c z i ^ 2 = 0 ↔ z i = (1 - η * P.lam i) * c i / η := by
  have hl : P.lam i ^ 2 ≠ 0 := pow_ne_zero 2 (P.lam_pos i).ne'
  rw [mul_eq_zero, or_iff_right hl, sq_eq_zero_iff, Spec.cNext, sub_eq_zero, eq_div_iff hη]
  constructor <;> intro h <;> linarith

/-- For `η ≠ 0`: `s^S_{t+1} = 0` iff the noise hits the affine subspace
`{ζ_i = (1 - ηλ_i) c_i / η for all i ∈ S}`. -/
theorem mom_two_cNext_eq_zero_iff (S : Finset ι) {η : ℝ} (hη : η ≠ 0) (c z : ι → ℝ) :
    P.mom S 2 (P.cNext η c z) = 0 ↔ ∀ i ∈ S, z i = (1 - η * P.lam i) * c i / η := by
  unfold Spec.mom
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)]
  exact forall₂_congr fun i _ => lam_sq_mul_cNext_sq_eq_zero_iff P hη c z i

/-- The next coordinate is a measurable function of the realised noise. -/
theorem measurable_cNext (η : ℝ) (c : ι → ℝ) (i : ι) :
    Measurable fun z : ι → ℝ => P.cNext η c z i := by
  unfold Spec.cNext
  have hi : Measurable fun z : ι → ℝ => z i := measurable_pi_apply i
  exact measurable_const.sub (hi.const_mul η)

/-- The next block moments are measurable functions of the realised noise. -/
theorem measurable_mom_cNext (S : Finset ι) (p : ℕ) (η : ℝ) (c : ι → ℝ) :
    Measurable fun z : ι → ℝ => P.mom S p (P.cNext η c z) := by
  unfold Spec.mom
  exact Finset.measurable_sum _ fun i _ => ((measurable_cNext P η c i).pow_const 2).const_mul _

/-- The next alignment `θ_{t+1}` is a (Borel) measurable function of the realised noise. -/
theorem measurable_theta_cNext (η : ℝ) (c : ι → ℝ) :
    Measurable fun z : ι → ℝ => P.theta (P.cNext η c z) := by
  unfold Spec.theta Spec.s Spec.sD Spec.sB
  exact (measurable_mom_cNext P _ _ η c).div
    ((measurable_mom_cNext P _ _ η c).add (measurable_mom_cNext P _ _ η c))

end NoiseModel

/-! ### (1) Integrability and (2) Lemma "Elementwise expectation of `x_{t+1}`" -/

section OneStep

variable (P : Spec ι) {N : Noise ι} {μ : Measure Ω} [IsProbabilityMeasure μ] {ζ : ι → Ω → ℝ}

/-- The next coordinate `c_{i,t+1}` is integrable. -/
theorem integrable_cNext (h : IsNoise N μ ζ) (η : ℝ) (c : ι → ℝ) (i : ι) :
    Integrable (fun ω => P.cNext η c (fun j => ζ j ω) i) μ := by
  unfold Spec.cNext
  exact (integrable_const _).sub ((h.integrable i).const_mul _)

/-- `c_{i,t+1}²` is integrable. -/
theorem integrable_cNext_sq (h : IsNoise N μ ζ) (η : ℝ) (c : ι → ℝ) (i : ι) :
    Integrable (fun ω => P.cNext η c (fun j => ζ j ω) i ^ 2) μ := by
  simp only [NoiseModel.cNext_sq]
  exact ((integrable_const _).add ((h.integrable i).const_mul _)).add
    ((h.integrable_sq i).const_mul _)

/-- `𝔼[c_{i,t+1} | x_t] = (1 - η λ_i) c_{i,t}`. -/
theorem integral_cNext (h : IsNoise N μ ζ) (η : ℝ) (c : ι → ℝ) (i : ι) :
    ∫ ω, P.cNext η c (fun j => ζ j ω) i ∂μ = (1 - η * P.lam i) * c i := by
  unfold Spec.cNext
  rw [integral_sub (integrable_const _) ((h.integrable i).const_mul _), integral_const,
    integral_const_mul, h.integral_eq_zero]
  simp

/-- `𝔼[c_{i,t+1}² | x_t] = (1 - η λ_i)² c_{i,t}² + η² κ_i²`: the second-moment recursion of one
coordinate (the cross term vanishes since `𝔼[ζ_i] = 0`). -/
theorem integral_cNext_sq (h : IsNoise N μ ζ) (η : ℝ) (c : ι → ℝ) (i : ι) :
    ∫ ω, P.cNext η c (fun j => ζ j ω) i ^ 2 ∂μ
      = (1 - η * P.lam i) ^ 2 * c i ^ 2 + η ^ 2 * N.kap2 i := by
  simp only [NoiseModel.cNext_sq]
  have h1 : Integrable (fun _ : Ω => ((1 - η * P.lam i) * c i) ^ 2) μ := integrable_const _
  have h2 : Integrable (fun ω => -(2 * η * ((1 - η * P.lam i) * c i)) * ζ i ω) μ :=
    (h.integrable i).const_mul _
  have h3 : Integrable (fun ω => η ^ 2 * ζ i ω ^ 2) μ := (h.integrable_sq i).const_mul _
  have h12 : Integrable (fun ω => ((1 - η * P.lam i) * c i) ^ 2
      + -(2 * η * ((1 - η * P.lam i) * c i)) * ζ i ω) μ := h1.add h2
  rw [integral_add h12 h3, integral_add h1 h2, integral_const, integral_const_mul,
    integral_const_mul, h.integral_eq_zero, h.integral_sq]
  simp only [probReal_univ, one_smul, mul_zero, add_zero]
  ring

/-- **Lemma "Elementwise expectation of `x_{t+1}`"** (tex 1062–1066): for each `i` and a given
`x_t`, `𝔼[λ_i² c_{i,t+1}² | x_t] = (1 - η λ_i)² λ_i² c_{i,t}² + η² λ_i² κ_i²`. -/
theorem integral_lam_sq_mul_cNext_sq (h : IsNoise N μ ζ) (η : ℝ) (c : ι → ℝ) (i : ι) :
    ∫ ω, P.lam i ^ 2 * P.cNext η c (fun j => ζ j ω) i ^ 2 ∂μ
      = (1 - η * P.lam i) ^ 2 * P.lam i ^ 2 * c i ^ 2 + η ^ 2 * P.lam i ^ 2 * N.kap2 i := by
  rw [integral_const_mul, integral_cNext_sq P h]
  ring

/-- Weighted sums of the `c_{i,t+1}²` are integrable. -/
theorem integrable_sum_mul_cNext_sq (h : IsNoise N μ ζ) (S : Finset ι) (w : ι → ℝ) (η : ℝ)
    (c : ι → ℝ) : Integrable (fun ω => ∑ i ∈ S, w i * P.cNext η c (fun j => ζ j ω) i ^ 2) μ :=
  integrable_finsetSum _ fun i _ => (integrable_cNext_sq P h η c i).const_mul _

/-- Expectation of a weighted sum of the `c_{i,t+1}²`. -/
theorem integral_sum_mul_cNext_sq (h : IsNoise N μ ζ) (S : Finset ι) (w : ι → ℝ) (η : ℝ)
    (c : ι → ℝ) :
    ∫ ω, ∑ i ∈ S, w i * P.cNext η c (fun j => ζ j ω) i ^ 2 ∂μ
      = ∑ i ∈ S, w i * ((1 - η * P.lam i) ^ 2 * c i ^ 2 + η ^ 2 * N.kap2 i) := by
  rw [integral_finsetSum _ fun i _ => (integrable_cNext_sq P h η c i).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_cNext_sq P h]

/-- All next-step block moments `∑_{i∈S} λ_i^p c_{i,t+1}²` are integrable. -/
theorem integrable_mom_cNext (h : IsNoise N μ ζ) (S : Finset ι) (p : ℕ) (η : ℝ) (c : ι → ℝ) :
    Integrable (fun ω => P.mom S p (P.cNext η c (fun j => ζ j ω))) μ :=
  integrable_sum_mul_cNext_sq P h S (fun i => P.lam i ^ p) η c

/-- `𝔼[∑_{i∈S} λ_i^p c_{i,t+1}² | x_t] = ∑_{i∈S} λ_i^p ((1 - ηλ_i)² c_i² + η² κ_i²)`. -/
theorem integral_mom_cNext (h : IsNoise N μ ζ) (S : Finset ι) (p : ℕ) (η : ℝ) (c : ι → ℝ) :
    ∫ ω, P.mom S p (P.cNext η c (fun j => ζ j ω)) ∂μ
      = ∑ i ∈ S, P.lam i ^ p * ((1 - η * P.lam i) ^ 2 * c i ^ 2 + η ^ 2 * N.kap2 i) :=
  integral_sum_mul_cNext_sq P h S (fun i => P.lam i ^ p) η c

/-- **Lemma "Elementwise expectation", block form**: for every index set `S`,
`𝔼[s^S_{t+1} | x_t] = 𝔼[∑_{i∈S} λ_i² c_{i,t+1}² | x_t] = Spec.EsNext N S η c`. -/
theorem integral_mom_two_cNext (h : IsNoise N μ ζ) (S : Finset ι) (η : ℝ) (c : ι → ℝ) :
    ∫ ω, P.mom S 2 (P.cNext η c (fun j => ζ j ω)) ∂μ = P.EsNext N S η c := by
  rw [integral_mom_cNext P h, Spec.EsNext]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `s^𝒟_{t+1}` is integrable. -/
theorem integrable_sD_cNext (h : IsNoise N μ ζ) (η : ℝ) (c : ι → ℝ) :
    Integrable (fun ω => P.sD (P.cNext η c (fun j => ζ j ω))) μ :=
  integrable_mom_cNext P h P.D 2 η c

/-- `s^ℬ_{t+1}` is integrable. -/
theorem integrable_sB_cNext (h : IsNoise N μ ζ) (η : ℝ) (c : ι → ℝ) :
    Integrable (fun ω => P.sB (P.cNext η c (fun j => ζ j ω))) μ :=
  integrable_mom_cNext P h P.B 2 η c

/-- `s_{t+1} = ‖A x_{t+1}‖²` is integrable. -/
theorem integrable_s_cNext (h : IsNoise N μ ζ) (η : ℝ) (c : ι → ℝ) :
    Integrable (fun ω => P.s (P.cNext η c (fun j => ζ j ω))) μ :=
  (integrable_sD_cNext P h η c).add (integrable_sB_cNext P h η c)

/-- `𝔼[s^𝒟_{t+1} | x_t] = Spec.EsNext N 𝒟 η c`. -/
theorem integral_sD_cNext (h : IsNoise N μ ζ) (η : ℝ) (c : ι → ℝ) :
    ∫ ω, P.sD (P.cNext η c (fun j => ζ j ω)) ∂μ = P.EsNext N P.D η c :=
  integral_mom_two_cNext P h P.D η c

/-- `𝔼[s^ℬ_{t+1} | x_t] = Spec.EsNext N ℬ η c`. -/
theorem integral_sB_cNext (h : IsNoise N μ ζ) (η : ℝ) (c : ι → ℝ) :
    ∫ ω, P.sB (P.cNext η c (fun j => ζ j ω)) ∂μ = P.EsNext N P.B η c :=
  integral_mom_two_cNext P h P.B η c

/-- **Lemma "Elementwise expectation", eq. (Eat)** (tex 1069):
`𝔼[s^𝒟_{t+1} | x_t] = s^𝒟_t - 2η ∑_𝒟 λ_i³ c_i² + η² (∑_𝒟 λ_i⁴ c_i² + e_𝒟)`. -/
theorem integral_sD_cNext_eq (h : IsNoise N μ ζ) (η : ℝ) (c : ι → ℝ) :
    ∫ ω, P.sD (P.cNext η c (fun j => ζ j ω)) ∂μ
      = P.sD c - 2 * η * P.tauD c + η ^ 2 * (P.mom P.D 4 c + P.eD N) := by
  rw [integral_sD_cNext P h, NoiseModel.EsNext_expand]
  rfl

/-- **Lemma "Elementwise expectation", eq. (Ebt)** (tex 1070):
`𝔼[s^ℬ_{t+1} | x_t] = s^ℬ_t - 2η ∑_ℬ λ_i³ c_i² + η² (∑_ℬ λ_i⁴ c_i² + e_ℬ)`. -/
theorem integral_sB_cNext_eq (h : IsNoise N μ ζ) (η : ℝ) (c : ι → ℝ) :
    ∫ ω, P.sB (P.cNext η c (fun j => ζ j ω)) ∂μ
      = P.sB c - 2 * η * P.tauB c + η ^ 2 * (P.mom P.B 4 c + P.eB N) := by
  rw [integral_sB_cNext P h, NoiseModel.EsNext_expand]
  rfl

/-- `𝔼[s_{t+1} | x_t] = 𝔼[s^𝒟_{t+1} | x_t] + 𝔼[s^ℬ_{t+1} | x_t]`, the denominator of
`Spec.thetaBarNext`. -/
theorem integral_s_cNext (h : IsNoise N μ ζ) (η : ℝ) (c : ι → ℝ) :
    ∫ ω, P.s (P.cNext η c (fun j => ζ j ω)) ∂μ = P.EsNext N P.D η c + P.EsNext N P.B η c := by
  unfold Spec.s
  rw [integral_add (integrable_sD_cNext P h η c) (integrable_sB_cNext P h η c),
    integral_sD_cNext P h, integral_sB_cNext P h]

/-- `Spec.thetaBarNext` is literally the ratio of expectations
`𝔼[s^𝒟_{t+1} | x_t] / 𝔼[s_{t+1} | x_t]`. -/
theorem thetaBarNext_eq_integral_div_integral (h : IsNoise N μ ζ) (η : ℝ) (c : ι → ℝ) :
    P.thetaBarNext N η c = (∫ ω, P.sD (P.cNext η c (fun j => ζ j ω)) ∂μ)
      / ∫ ω, P.s (P.cNext η c (fun j => ζ j ω)) ∂μ := by
  rw [integral_sD_cNext P h, integral_s_cNext P h, Spec.thetaBarNext]

/-! ### (3) Lemma "Quadratic form for step size condition" -/

/-- The comparison functional `f_t(η)` is integrable. -/
theorem integrable_fCompare (h : IsNoise N μ ζ) (η : ℝ) (c : ι → ℝ) :
    Integrable (fun ω => P.fCompare η c (fun j => ζ j ω)) μ := by
  unfold Spec.fCompare
  exact ((integrable_sD_cNext P h η c).const_mul _).sub ((integrable_sB_cNext P h η c).mul_const _)

/-- **Lemma "Quadratic form for step size condition"**, eq. (quad-form) (tex 1098–1107): for a
given `x_t`, `𝔼[f_t(η) | x_t] = p_t η² + q_t η`. -/
theorem integral_fCompare (h : IsNoise N μ ζ) (η : ℝ) (c : ι → ℝ) :
    ∫ ω, P.fCompare η c (fun j => ζ j ω) ∂μ = P.pCoef N c * η ^ 2 + P.qCoef c * η := by
  unfold Spec.fCompare
  rw [integral_sub ((integrable_sD_cNext P h η c).const_mul _)
      ((integrable_sB_cNext P h η c).mul_const _),
    integral_const_mul, integral_mul_const, integral_sD_cNext P h, integral_sB_cNext P h]
  exact NoiseModel.sB_mul_EsNext_sub P N η c

/-! ### (4) Theorem 10: the expected one-step loss change of projected SGD -/

/-- The loss after an `S`-projected step is integrable. -/
theorem integrable_loss_cNextProj (h : IsNoise N μ ζ) (S : Finset ι) (η : ℝ) (c : ι → ℝ) :
    Integrable (fun ω => P.loss (P.cNextProj S η c (fun j => ζ j ω))) μ := by
  have heq : (fun ω => P.loss (P.cNextProj S η c (fun j => ζ j ω)))
      = fun ω => P.loss c + 1 / 2 * (P.mom S 1 (P.cNext η c (fun j => ζ j ω)) - P.mom S 1 c) := by
    funext ω
    linarith [NoiseModel.loss_cNextProj_sub P S η c (fun j => ζ j ω)]
  rw [heq]
  exact (integrable_const _).add
    (((integrable_mom_cNext P h S 1 η c).sub (integrable_const _)).const_mul _)

/-- The loss after a plain SGD step is integrable. -/
theorem integrable_loss_cNext (h : IsNoise N μ ζ) (η : ℝ) (c : ι → ℝ) :
    Integrable (fun ω => P.loss (P.cNext η c (fun j => ζ j ω))) μ := by
  simpa only [NoiseModel.cNextProj_univ] using integrable_loss_cNextProj P h Finset.univ η c

/-- **Theorem 10, the expected loss change** (tex 1490–1498): for the `S`-projected update
`x_{t+1} = x_t - η P^S (A x_t + ξ_t)` (DSGD: `S = 𝒟`; BSGD: `S = ℬ`) and a given `x_t`,
`𝔼[L(x_{t+1}) - L(x_t) | x_t] = -η s^S_t + (η²/2) (τ^S_t + n^loss_S)`. -/
theorem integral_loss_cNextProj_sub (h : IsNoise N μ ζ) (S : Finset ι) (η : ℝ) (c : ι → ℝ) :
    ∫ ω, (P.loss (P.cNextProj S η c (fun j => ζ j ω)) - P.loss c) ∂μ
      = P.expLossChange N S η c := by
  simp only [NoiseModel.loss_cNextProj_sub]
  rw [integral_const_mul, integral_sub (integrable_mom_cNext P h S 1 η c) (integrable_const _),
    integral_mom_cNext P h, integral_const]
  simp only [probReal_univ, one_smul]
  exact NoiseModel.half_sum_sub_eq_expLossChange P N S η c

/-- `𝔼[L(x_{t+1}) | x_t] = L(x_t) + (-η s^S_t + (η²/2) (τ^S_t + n^loss_S))`. -/
theorem integral_loss_cNextProj (h : IsNoise N μ ζ) (S : Finset ι) (η : ℝ) (c : ι → ℝ) :
    ∫ ω, P.loss (P.cNextProj S η c (fun j => ζ j ω)) ∂μ
      = P.loss c + P.expLossChange N S η c := by
  have := integral_loss_cNextProj_sub P h S η c
  rw [integral_sub (integrable_loss_cNextProj P h S η c) (integrable_const _), integral_const] at this
  simp only [probReal_univ, one_smul] at this
  linarith

/-- The same for the plain SGD step (`S = univ`): `𝔼[L(x_{t+1}) - L(x_t) | x_t]
= -η s_t + (η²/2) (∑_i λ_i³ c_i² + ∑_i λ_i κ_i²)`. -/
theorem integral_loss_cNext_sub (h : IsNoise N μ ζ) (η : ℝ) (c : ι → ℝ) :
    ∫ ω, (P.loss (P.cNext η c (fun j => ζ j ω)) - P.loss c) ∂μ
      = P.expLossChange N Finset.univ η c := by
  simpa only [NoiseModel.cNextProj_univ] using integral_loss_cNextProj_sub P h Finset.univ η c

/-- **Theorem 10** (tex 1477–1488), general block `S`, with the genuine expectation: provided the
denominator `τ^S_t + n^loss_S` of `η^loss_S` is positive, for *every* real step size `η`

`𝔼[L(x_{t+1}) - L(x_t) | x_t] < 0  ↔  0 < η < η^loss_S(x_t) = 2 s^S_t / (τ^S_t + n^loss_S)`.

The hypothesis holds as soon as `s^S_t > 0` (see `integral_loss_cNextProj_sub_neg_iff_of_pos`) or
`n^loss_S > 0`; when it fails (`s^S_t = 0` and `n^loss_S = 0`) the expected loss change is `0` for
every `η` and `η^loss_S = 0/0`. -/
theorem integral_loss_cNextProj_sub_neg_iff (h : IsNoise N μ ζ) (S : Finset ι) (η : ℝ)
    (c : ι → ℝ) (hden : 0 < P.mom S 3 c + P.nLoss N S) :
    ∫ ω, (P.loss (P.cNextProj S η c (fun j => ζ j ω)) - P.loss c) ∂μ < 0
      ↔ 0 < η ∧ η < P.etaLoss N S c := by
  rw [integral_loss_cNextProj_sub P h]
  exact NoiseModel.expLossChange_neg_iff P N S η c hden

/-- **Theorem 10** under the natural non-degeneracy `s^S_t > 0` (the state has a component in the
block that is being updated). -/
theorem integral_loss_cNextProj_sub_neg_iff_of_pos (h : IsNoise N μ ζ) (S : Finset ι) (η : ℝ)
    (c : ι → ℝ) (hs : 0 < P.mom S 2 c) :
    ∫ ω, (P.loss (P.cNextProj S η c (fun j => ζ j ω)) - P.loss c) ∂μ < 0
      ↔ 0 < η ∧ η < P.etaLoss N S c :=
  integral_loss_cNextProj_sub_neg_iff P h S η c
    (add_pos_of_pos_of_nonneg (NoiseModel.mom_pos_of_mom_pos P hs 3) (NoiseModel.nLoss_nonneg P N S))

/-- **Theorem 10, dominant update (DSGD)**: if `s^𝒟_t > 0` then
`𝔼[L(x_{t+1}) - L(x_t) | x_t] < 0 ↔ 0 < η < η^loss_𝒟(x_t)`. -/
theorem integral_loss_DSGD_sub_neg_iff (h : IsNoise N μ ζ) (η : ℝ) (c : ι → ℝ)
    (hs : 0 < P.sD c) :
    ∫ ω, (P.loss (P.cNextProj P.D η c (fun j => ζ j ω)) - P.loss c) ∂μ < 0
      ↔ 0 < η ∧ η < P.etaLossD N c :=
  integral_loss_cNextProj_sub_neg_iff_of_pos P h P.D η c hs

/-- **Theorem 10, bulk update (BSGD)**: if `s^ℬ_t > 0` then
`𝔼[L(x_{t+1}) - L(x_t) | x_t] < 0 ↔ 0 < η < η^loss_ℬ(x_t)`. -/
theorem integral_loss_BSGD_sub_neg_iff (h : IsNoise N μ ζ) (η : ℝ) (c : ι → ℝ)
    (hs : 0 < P.sB c) :
    ∫ ω, (P.loss (P.cNextProj P.B η c (fun j => ζ j ω)) - P.loss c) ∂μ < 0
      ↔ 0 < η ∧ η < P.etaLossB N c :=
  integral_loss_cNextProj_sub_neg_iff_of_pos P h P.B η c hs

/-- **Theorem 10, the degenerate case** `s^S_t = 0` (the state has no component in the updated
block): the expected loss change is `(η²/2) n^loss_S ≥ 0`, so *no* step size decreases the expected
loss.  (This is consistent with `η^loss_S = 0` when `n^loss_S > 0`; when also `n^loss_S = 0`,
`η^loss_S` is `0/0`.) -/
theorem integral_loss_cNextProj_sub_nonneg_of_mom_eq_zero (h : IsNoise N μ ζ) (S : Finset ι)
    (η : ℝ) (c : ι → ℝ) (hs : P.mom S 2 c = 0) :
    0 ≤ ∫ ω, (P.loss (P.cNextProj S η c (fun j => ζ j ω)) - P.loss c) ∂μ := by
  rw [integral_loss_cNextProj_sub P h]
  exact NoiseModel.expLossChange_nonneg_of_mom_eq_zero P N S η c hs

end OneStep

/-! ### (5) The Remark of Appendix A.2: `θ_{t+1}` is integrable; the events `{s_{t+1} = 0}`,
`{s^𝒟_{t+1} = 0}`

The paper (tex 928–934) claims that, for a fixed `x_t`, the sets `{ξ | s_{t+1}(ξ) = 0}` and
`{ξ | s^𝒟_{t+1}(ξ) = 0}` are null sets for the law of the noise, "by Sard's theorem", so that
`θ_{t+1} = 1 / (1 + s^ℬ_{t+1}/s^𝒟_{t+1})` may be used inside expectations.

* What is true (below): for `η ≠ 0`, `{s^S_{t+1} = 0}` is the event that the noise hits the affine
  subspace `𝒱_S = {ζ_i = (1 - ηλ_i) c_i / η ∀ i ∈ S}`; its probability is at most the mass of the
  single atom `{ζ_i = (1 - ηλ_i) c_i / η}` for any `i ∈ S`.  Hence it is null as soon as *one*
  coordinate `ζ_i`, `i ∈ S`, has no atom there — e.g. is a non-degenerate Gaussian (`κ_i² > 0`).
* The justification is not Sard's theorem (which concerns critical values of smooth maps) but the
  fact that a proper affine subspace is Lebesgue-null *together with* absolute continuity of the
  law of `ξ`, i.e. `Σ ≻ 0` on the relevant directions.  The paper only assumes `Σ ⪰ 0`; for
  degenerate `Σ` the claim is false: see `measure_sD_cNext_eq_zero_eq_one_of_degenerate` and the
  Gaussian counterexample `exists_gaussian_noise_sD_cNext_eq_zero`.
* The splitting `𝔼[θ_{t+1}] = ∫_{𝒱ᶜ} θ_{t+1}` that the Remark derives needs no null set at all:
  `θ_{t+1} = 0` on `{s^𝒟_{t+1} = 0}` (`setIntegral_theta_cNext_eq_zero`).  What the null set is
  really needed for is the a.e. identity `θ_{t+1} = 1/(1 + s^ℬ_{t+1}/s^𝒟_{t+1})`
  (`ae_theta_cNext_eq_one_div`).
* `θ_{t+1}` is a measurable function of the noise with values in `[0, 1]`, hence integrable, for
  every noise law (`integrable_theta_cNext`). -/

namespace NoiseModel

variable (P : Spec ι)

/-- `θ = 1 / (1 + s^ℬ/s^𝒟)` (eq. (theta-next)) — valid exactly when `s^𝒟 ≠ 0`. -/
theorem theta_eq_one_div (c : ι → ℝ) (h : P.sD c ≠ 0) :
    P.theta c = 1 / (1 + P.sB c / P.sD c) := by
  have hpos : 0 < P.sD c := lt_of_le_of_ne (P.sD_nonneg c) (Ne.symm h)
  have hB := P.sB_nonneg c
  have hs : P.sD c + P.sB c ≠ 0 := by positivity
  unfold Spec.theta Spec.s
  field_simp

/-- `θ = 0` when `s^𝒟 = 0` (including the convention `θ(0) = 0`). -/
theorem theta_eq_zero_of_sD_eq_zero (c : ι → ℝ) (h : P.sD c = 0) : P.theta c = 0 := by
  unfold Spec.theta; rw [h, zero_div]

end NoiseModel

section Theta

variable (P : Spec ι) {μ : Measure Ω} {ζ : ι → Ω → ℝ}

/-- `θ_{t+1}`, as a function on the sample space, is a.e. measurable. -/
theorem aemeasurable_theta_cNext (hζ : ∀ i, AEMeasurable (ζ i) μ) (η : ℝ) (c : ι → ℝ) :
    AEMeasurable (fun ω => P.theta (P.cNext η c (fun j => ζ j ω))) μ :=
  (NoiseModel.measurable_theta_cNext P η c).comp_aemeasurable (AEMeasurable.of_eval hζ)

/-- `θ_{t+1}` is measurable when the noise coordinates are. -/
theorem measurable_theta_cNext (hζ : ∀ i, Measurable (ζ i)) (η : ℝ) (c : ι → ℝ) :
    Measurable fun ω => P.theta (P.cNext η c (fun j => ζ j ω)) :=
  (NoiseModel.measurable_theta_cNext P η c).comp (measurable_pi_lambda _ hζ)

/-- `θ_{t+1} ∈ [0, 1]` for every realisation of the noise. -/
theorem theta_cNext_mem_Icc (η : ℝ) (c z : ι → ℝ) : P.theta (P.cNext η c z) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨P.theta_nonneg _, P.theta_le_one _⟩

/-- **Remark of A.2, integrability** (tex 931): `θ_{t+1}` is bounded and measurable, hence
integrable — for *every* law of the noise (no moment assumption, no non-degeneracy). -/
theorem integrable_theta_cNext [IsFiniteMeasure μ] (hζ : ∀ i, AEMeasurable (ζ i) μ) (η : ℝ)
    (c : ι → ℝ) : Integrable (fun ω => P.theta (P.cNext η c (fun j => ζ j ω))) μ :=
  Integrable.of_bound (aemeasurable_theta_cNext P hζ η c).aestronglyMeasurable 1
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (P.theta_nonneg _)]; exact P.theta_le_one _)

/-- `0 ≤ 𝔼[θ_{t+1} | x_t]`. -/
theorem integral_theta_cNext_nonneg (η : ℝ) (c : ι → ℝ) :
    0 ≤ ∫ ω, P.theta (P.cNext η c (fun j => ζ j ω)) ∂μ :=
  integral_nonneg fun _ => P.theta_nonneg _

/-- `𝔼[θ_{t+1} | x_t] ≤ 1`. -/
theorem integral_theta_cNext_le_one [IsProbabilityMeasure μ] (η : ℝ) (c : ι → ℝ) :
    ∫ ω, P.theta (P.cNext η c (fun j => ζ j ω)) ∂μ ≤ 1 := by
  by_cases hint : Integrable (fun ω => P.theta (P.cNext η c (fun j => ζ j ω))) μ
  · calc ∫ ω, P.theta (P.cNext η c (fun j => ζ j ω)) ∂μ ≤ ∫ _, (1 : ℝ) ∂μ :=
          integral_mono hint (integrable_const _) fun _ => P.theta_le_one _
      _ = 1 := by simp
  · rw [integral_undef hint]; exact zero_le_one

/-- On the event `{s^𝒟_{t+1} = 0}` the next alignment vanishes, so this event never contributes to
`𝔼[θ_{t+1}]` — whether or not it is a null set.  (This is the splitting
`𝔼[θ_{t+1}] = ∫_{ℝ^d ∖ 𝒱} θ_{t+1}` of the Remark, tex 932–934.) -/
theorem setIntegral_theta_cNext_eq_zero (μ : Measure Ω) (ζ : ι → Ω → ℝ) (η : ℝ) (c : ι → ℝ) :
    ∫ ω in {ω | P.sD (P.cNext η c (fun j => ζ j ω)) = 0},
      P.theta (P.cNext η c (fun j => ζ j ω)) ∂μ = 0 :=
  setIntegral_eq_zero_of_forall_eq_zero fun _ hω => NoiseModel.theta_eq_zero_of_sD_eq_zero P _ hω

end Theta

section NullSets

variable (P : Spec ι) (μ : Measure Ω) (ζ : ι → Ω → ℝ)

/-- For `η ≠ 0`, the event `{s^S_{t+1} = 0}` is the event that the noise lies in the affine
subspace `𝒱_S = {ζ_i = (1 - ηλ_i) c_i / η for all i ∈ S}` (tex 929–931, where `S = 𝒟`). -/
theorem setOf_mom_two_cNext_eq_zero (S : Finset ι) {η : ℝ} (hη : η ≠ 0) (c : ι → ℝ) :
    {ω | P.mom S 2 (P.cNext η c (fun j => ζ j ω)) = 0}
      = ⋂ i ∈ S, {ω | ζ i ω = (1 - η * P.lam i) * c i / η} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iInter]
  exact NoiseModel.mom_two_cNext_eq_zero_iff P S hη c _

/-- `ℙ(s^S_{t+1} = 0) ≤ ℙ(ζ_i = (1 - ηλ_i) c_i / η)` for every `i ∈ S` (and `η ≠ 0`). -/
theorem measure_mom_two_cNext_eq_zero_le {S : Finset ι} {i : ι} (hi : i ∈ S) {η : ℝ}
    (hη : η ≠ 0) (c : ι → ℝ) :
    μ {ω | P.mom S 2 (P.cNext η c (fun j => ζ j ω)) = 0}
      ≤ μ {ω | ζ i ω = (1 - η * P.lam i) * c i / η} :=
  measure_mono fun _ hω => (NoiseModel.mom_two_cNext_eq_zero_iff P S hη c _).mp hω i hi

/-- **Remark of A.2, corrected** (tex 928–931): if `η ≠ 0` and, for some `i ∈ S`, the noise
coordinate `ζ_i` has no atom at `(1 - ηλ_i) c_i / η`, then `{s^S_{t+1} = 0}` is a null event. -/
theorem measure_mom_two_cNext_eq_zero {S : Finset ι} {i : ι} (hi : i ∈ S) {η : ℝ} (hη : η ≠ 0)
    (c : ι → ℝ) (hatom : μ {ω | ζ i ω = (1 - η * P.lam i) * c i / η} = 0) :
    μ {ω | P.mom S 2 (P.cNext η c (fun j => ζ j ω)) = 0} = 0 :=
  le_antisymm ((measure_mom_two_cNext_eq_zero_le P μ ζ hi hη c).trans hatom.le) (zero_le _)

/-- **Remark of A.2 for `s^𝒟_{t+1}`**: `ℙ(s^𝒟_{t+1} = 0) = 0` if some dominant noise coordinate has
no atom at the critical value. -/
theorem measure_sD_cNext_eq_zero {i : ι} (hi : i ∈ P.D) {η : ℝ} (hη : η ≠ 0) (c : ι → ℝ)
    (hatom : μ {ω | ζ i ω = (1 - η * P.lam i) * c i / η} = 0) :
    μ {ω | P.sD (P.cNext η c (fun j => ζ j ω)) = 0} = 0 :=
  measure_mom_two_cNext_eq_zero P μ ζ hi hη c hatom

/-- **Remark of A.2 for `s_{t+1}`**: `ℙ(s_{t+1} = 0) = ℙ(x_{t+1} = 0) = 0` if *any* noise
coordinate has no atom at the critical value. -/
theorem measure_s_cNext_eq_zero (i : ι) {η : ℝ} (hη : η ≠ 0) (c : ι → ℝ)
    (hatom : μ {ω | ζ i ω = (1 - η * P.lam i) * c i / η} = 0) :
    μ {ω | P.s (P.cNext η c (fun j => ζ j ω)) = 0} = 0 := by
  have h := measure_mom_two_cNext_eq_zero P μ ζ (Finset.mem_univ i) hη c hatom
  simpa only [P.s_eq_sum, Spec.mom] using h

variable {μ ζ}

/-- A random variable whose law has no atoms hits a given value with probability `0`. -/
theorem NoiseModel.measure_eq_of_nullSingleton {X : Ω → ℝ} (hX : AEMeasurable X μ)
    [NullSingletonClass (μ.map X)] (a : ℝ) : μ {ω | X ω = a} = 0 := by
  have h := measure_singleton (μ := μ.map X) a
  rw [Measure.map_apply_of_aemeasurable hX (measurableSet_singleton a)] at h
  exact h

/-- **Remark of A.2, atomless version**: if for some `i ∈ 𝒟` the law of `ζ_i` has no atoms, then
`ℙ(s^𝒟_{t+1} = 0) = 0` for every state `x_t` and every `η ≠ 0`. -/
theorem measure_sD_cNext_eq_zero_of_nullSingleton {i : ι} (hi : i ∈ P.D)
    (hζ : AEMeasurable (ζ i) μ) [NullSingletonClass (μ.map (ζ i))] {η : ℝ} (hη : η ≠ 0)
    (c : ι → ℝ) : μ {ω | P.sD (P.cNext η c (fun j => ζ j ω)) = 0} = 0 :=
  measure_sD_cNext_eq_zero P μ ζ hi hη c (NoiseModel.measure_eq_of_nullSingleton hζ _)

/-- **Remark of A.2, atomless version for `s_{t+1}`**. -/
theorem measure_s_cNext_eq_zero_of_nullSingleton (i : ι)
    (hζ : AEMeasurable (ζ i) μ) [NullSingletonClass (μ.map (ζ i))] {η : ℝ} (hη : η ≠ 0)
    (c : ι → ℝ) : μ {ω | P.s (P.cNext η c (fun j => ζ j ω)) = 0} = 0 :=
  measure_s_cNext_eq_zero P μ ζ i hη c (NoiseModel.measure_eq_of_nullSingleton hζ _)

/-- **Remark of A.2, Gaussian version**: if for some `i ∈ 𝒟` the coordinate `ζ_i = ⟪ξ, u_i⟫` is a
*non-degenerate* Gaussian (variance `v ≠ 0`, i.e. `κ_i² > 0`), then `ℙ(s^𝒟_{t+1} = 0) = 0` for
every state and every `η ≠ 0`. -/
theorem measure_sD_cNext_eq_zero_of_gaussian {i : ι} (hi : i ∈ P.D) {m : ℝ} {v : ℝ≥0}
    (hlaw : HasLaw (ζ i) (gaussianReal m v) μ) (hv : v ≠ 0) {η : ℝ} (hη : η ≠ 0) (c : ι → ℝ) :
    μ {ω | P.sD (P.cNext η c (fun j => ζ j ω)) = 0} = 0 := by
  haveI : NullSingletonClass (μ.map (ζ i)) := by
    rw [hlaw.map_eq]; exact nullSingletonClass_gaussianReal hv
  exact measure_sD_cNext_eq_zero_of_nullSingleton P hi hlaw.aemeasurable hη c

/-- **Remark of A.2, Gaussian version for `s_{t+1}`**: one non-degenerate Gaussian coordinate
(anywhere) suffices for `ℙ(x_{t+1} = 0) = 0`. -/
theorem measure_s_cNext_eq_zero_of_gaussian (i : ι) {m : ℝ} {v : ℝ≥0}
    (hlaw : HasLaw (ζ i) (gaussianReal m v) μ) (hv : v ≠ 0) {η : ℝ} (hη : η ≠ 0) (c : ι → ℝ) :
    μ {ω | P.s (P.cNext η c (fun j => ζ j ω)) = 0} = 0 := by
  haveI : NullSingletonClass (μ.map (ζ i)) := by
    rw [hlaw.map_eq]; exact nullSingletonClass_gaussianReal hv
  exact measure_s_cNext_eq_zero_of_nullSingleton P i hlaw.aemeasurable hη c

/-- **Eq. (theta-next), almost surely**: under the no-atom condition,
`θ_{t+1} = 1 / (1 + s^ℬ_{t+1}/s^𝒟_{t+1})` almost surely. -/
theorem ae_theta_cNext_eq_one_div {i : ι} (hi : i ∈ P.D) {η : ℝ} (hη : η ≠ 0) (c : ι → ℝ)
    (hatom : μ {ω | ζ i ω = (1 - η * P.lam i) * c i / η} = 0) :
    ∀ᵐ ω ∂μ, P.theta (P.cNext η c (fun j => ζ j ω))
      = 1 / (1 + P.sB (P.cNext η c (fun j => ζ j ω)) / P.sD (P.cNext η c (fun j => ζ j ω))) := by
  have h0 := measure_sD_cNext_eq_zero P μ ζ hi hη c hatom
  rw [measure_eq_zero_iff_ae_notMem] at h0
  filter_upwards [h0] with ω hω
  exact NoiseModel.theta_eq_one_div P _ hω

/-- Consequently `𝔼[θ_{t+1}] = 𝔼[1 / (1 + s^ℬ_{t+1}/s^𝒟_{t+1})]` under the no-atom condition. -/
theorem integral_theta_cNext_eq_integral_one_div {i : ι} (hi : i ∈ P.D) {η : ℝ} (hη : η ≠ 0)
    (c : ι → ℝ) (hatom : μ {ω | ζ i ω = (1 - η * P.lam i) * c i / η} = 0) :
    ∫ ω, P.theta (P.cNext η c (fun j => ζ j ω)) ∂μ
      = ∫ ω, 1 / (1 + P.sB (P.cNext η c (fun j => ζ j ω))
          / P.sD (P.cNext η c (fun j => ζ j ω))) ∂μ :=
  integral_congr_ae (ae_theta_cNext_eq_one_div P hi hη c hatom)

/-! #### Failure of the Remark for degenerate noise -/

variable {N : Noise ι}

/-- If the noise has no variance in the directions of `S` (`κ_i² = 0` for `i ∈ S`), the next block
moments are almost surely deterministic: `∑_S λ_i^p c_{i,t+1}² = ∑_S λ_i^p (1 - ηλ_i)² c_i²`. -/
theorem ae_mom_cNext_eq_of_kap2_eq_zero (h : IsNoise N μ ζ) {S : Finset ι}
    (hS : ∀ i ∈ S, N.kap2 i = 0) (p : ℕ) (η : ℝ) (c : ι → ℝ) :
    ∀ᵐ ω ∂μ, P.mom S p (P.cNext η c (fun j => ζ j ω))
      = ∑ i ∈ S, P.lam i ^ p * ((1 - η * P.lam i) * c i) ^ 2 := by
  have hall : ∀ᵐ ω ∂μ, ∀ i ∈ S, ζ i ω = 0 :=
    (Filter.eventually_all_finset S).mpr fun i hi => h.ae_eq_zero_of_kap2_eq_zero (hS i hi)
  filter_upwards [hall] with ω hω
  unfold Spec.mom
  refine Finset.sum_congr rfl fun i hi => ?_
  simp [Spec.cNext, hω i hi]

/-- **The Remark of A.2 fails for degenerate `Σ`.**  If the noise has no variance in the dominant
directions (`κ_i² = 0` for all `i ∈ 𝒟`; allowed by the paper's assumption `Σ ⪰ 0`) and
`(1 - ηλ_i) c_i = 0` for all `i ∈ 𝒟` (e.g. `θ_t = 0`, or `k = 1` and `η = 1/λ_1`), then
`s^𝒟_{t+1} = 0` — hence `θ_{t+1} = 0` — with probability **one**, not zero. -/
theorem measure_sD_cNext_eq_zero_eq_one_of_degenerate [IsProbabilityMeasure μ]
    (h : IsNoise N μ ζ) (hD : ∀ i ∈ P.D, N.kap2 i = 0) (η : ℝ) (c : ι → ℝ)
    (hc : ∀ i ∈ P.D, (1 - η * P.lam i) * c i = 0) :
    μ {ω | P.sD (P.cNext η c (fun j => ζ j ω)) = 0} = 1 := by
  have hae : ∀ᵐ ω ∂μ, P.sD (P.cNext η c (fun j => ζ j ω)) = 0 := by
    filter_upwards [ae_mom_cNext_eq_of_kap2_eq_zero P h hD 2 η c] with ω hω
    rw [Spec.sD, hω]
    exact Finset.sum_eq_zero fun i hi => by rw [hc i hi]; simp
  have hset : {ω | P.sD (P.cNext η c (fun j => ζ j ω)) = 0} =ᵐ[μ] Set.univ :=
    ae_eq_univ.mpr (ae_iff.mp hae)
  rw [measure_congr hset, measure_univ]

/-- In the same degenerate situation but with `(1 - ηλ_i) c_i ≠ 0` for some `i ∈ 𝒟`, the event
`{s^𝒟_{t+1} = 0}` is null: for noise without dominant component, `ℙ(s^𝒟_{t+1} = 0) ∈ {0, 1}`. -/
theorem measure_sD_cNext_eq_zero_of_degenerate (h : IsNoise N μ ζ)
    (hD : ∀ i ∈ P.D, N.kap2 i = 0) (η : ℝ) (c : ι → ℝ) {i : ι} (hi : i ∈ P.D)
    (hc : (1 - η * P.lam i) * c i ≠ 0) :
    μ {ω | P.sD (P.cNext η c (fun j => ζ j ω)) = 0} = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [ae_mom_cNext_eq_of_kap2_eq_zero P h hD 2 η c] with ω hω
  rw [Set.mem_setOf_eq, Spec.sD, hω]
  exact (Finset.sum_pos' (fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    ⟨i, hi, mul_pos (pow_pos (P.lam_pos i) 2) (by positivity)⟩).ne'

end NullSets

end SuspiciousAlignment
