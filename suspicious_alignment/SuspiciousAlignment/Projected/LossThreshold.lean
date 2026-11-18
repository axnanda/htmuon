import Mathlib
import SuspiciousAlignment.Defs

/-!
# Projected SGD: loss thresholds and the alignment crossover (paper §5, Theorems 10 and 11)

Formalization, at the exact finite-`d` (algebraic) level, of Section 5 of

> Deng et al., *Suspicious Alignment of SGD: A Fine-Grained Step Size Condition Analysis*
> (arXiv:2601.11789v2),

up to and including Theorem 11, together with the two unnamed lemmas of Appendix A.5
("crossover quadratic properties" and "critical root") and the consequence displayed in the
*Summary* paragraph (for `η ∈ (η^loss_𝒟, η^loss_ℬ)` the dominant-projected update increases the
expected loss while the bulk-projected update decreases it).

## Main results (namespace `SuspiciousAlignment.Spec`)

* Theorem 10 (step size condition for projected updates)
  * `Spec.loss_cNextProj_sub_loss` — the pathwise identity
    `ΔL = -η gᵀAx + (η²/2) gᵀAg` for the `S`-projected update;
  * `Spec.loss_cNextProj_sub_loss_eq_expLossChange_add` — `ΔL = expLossChange + (mean-zero terms)`;
  * `Spec.expLossChange_eq_sum` — `expLossChange` is the sum of the per-coordinate expected changes;
  * `Spec.weighted_sum_loss_change` — the expectation for finitely supported noise;
  * `Spec.expLossChange_neg_iff` — `𝔼ΔL < 0 ↔ 0 < η < η^loss_S`;
  * `Spec.expLossChange_pos_iff`, `Spec.expLossChange_pos_iff_of_pos`,
    `Spec.expLossChange_eq_zero_iff`, `Spec.proj_loss_step_size_condition`.
* "Additional Notion" and the two lemmas
  * `Spec.alphaT_pos`, `Spec.gap_mul_s_le_alphaT`, `Spec.gammaT_neg`, `Spec.hQuad_zero`,
    `Spec.hQuad_one`, `Spec.crossover_quadratic_properties`;
  * `Spec.hQuad_thetaCrit`, `Spec.thetaCrit_mem_Ioo`, `Spec.hQuad_neg_iff`, `Spec.hQuad_pos_iff`,
    `Spec.hQuad_eq_zero_iff`, `Spec.existsUnique_hQuad_root`, `Spec.crossover_critical_root`.
* Theorem 11 (crossover of the two loss thresholds)
  * `Spec.etaLossD_sub_etaLossB` — `η^loss_𝒟 - η^loss_ℬ = 2 s h(θ) / (…)`;
  * `Spec.theta_lt_thetaCrit_iff`, `Spec.thetaCrit_lt_theta_iff`, `Spec.theta_eq_thetaCrit_iff`;
  * `Spec.loss_crossover` — the bundled statement of Theorem 11.
* Consequence (Summary paragraph)
  * `Spec.expLossChange_D_pos_B_neg`, `Spec.low_alignment_descent`, and the mirror statements
    `Spec.expLossChange_B_pos_D_neg`, `Spec.high_alignment_descent`.
* State dependence of `θ^crit_t`: `Spec.thetaCrit_congr`, `Spec.alphaT_smul`,
  `Spec.etaLossD_lt_etaLossB_smul_iff`, `LossThreshold.state_dependence_example`.

Generic helper lemmas (moments, noise energies, the alignment, an abstract quadratic) live in the
namespace `SuspiciousAlignment.LossThreshold`.

## Hypotheses

The paper states these results "for a given state `x_t`".  The precise hypotheses are:

* Theorem 10 needs `0 < τ^S + n^loss_S` (the denominator of `η^loss_S`).  It does **not** need
  `s^S > 0`, and `η > 0` is part of the equivalence, not an assumption.
* `α_t > 0` needs `s^𝒟 > 0` and `s^ℬ > 0`, i.e. `0 < θ_t < 1`; otherwise `μ^S(3,2)` is `0/0`.
* `θ^crit ∈ (0, 1)` needs in addition `n^loss_𝒟 > 0` and `n^loss_ℬ > 0` (both are claimed, but not
  implied by the paper's assumptions `Σ ⪰ 0`, `Tr Σ > 0`).
* The equivalences of Theorem 11 only need `0 < θ_t < 1`.

See `notes/fidelity/LossThreshold.md` for the full discussion.
-/

set_option linter.unusedSectionVars false

open Finset

namespace SuspiciousAlignment

namespace LossThreshold

/-! ## Abstract facts about the quadratic `a θ² + b θ + g` with `a > 0`, `g ≤ 0` -/

/-- The larger root `(-b + √(b² - 4ag)) / (2a)` of `a θ² + b θ + g`. -/
noncomputable def root (a b g : ℝ) : ℝ := (-b + Real.sqrt (b ^ 2 - 4 * a * g)) / (2 * a)

variable {a b g θ : ℝ}

theorem disc_nonneg (b : ℝ) (ha : 0 < a) (hg : g ≤ 0) : 0 ≤ b ^ 2 - 4 * a * g := by
  nlinarith [sq_nonneg b, mul_nonneg ha.le (neg_nonneg.2 hg)]

theorem abs_le_sqrt_disc (b : ℝ) (ha : 0 < a) (hg : g ≤ 0) :
    |b| ≤ Real.sqrt (b ^ 2 - 4 * a * g) := by
  apply Real.abs_le_sqrt
  nlinarith [mul_nonneg ha.le (neg_nonneg.2 hg)]

theorem abs_lt_sqrt_disc (b : ℝ) (ha : 0 < a) (hg : g < 0) :
    |b| < Real.sqrt (b ^ 2 - 4 * a * g) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_lt_sqrt (sq_nonneg b) (by nlinarith [mul_pos ha (neg_pos.2 hg)])

theorem add_sqrt_disc_nonneg (b : ℝ) (ha : 0 < a) (hg : g ≤ 0) :
    0 ≤ b + Real.sqrt (b ^ 2 - 4 * a * g) := by
  have h1 := abs_le_sqrt_disc b ha hg
  have h2 := neg_abs_le b
  linarith

/-- Factorisation of the quadratic through its larger root. -/
theorem quad_eq (b θ : ℝ) (ha : 0 < a) (hg : g ≤ 0) :
    a * θ ^ 2 + b * θ + g =
      (θ - root a b g) * (a * θ + (b + Real.sqrt (b ^ 2 - 4 * a * g)) / 2) := by
  have hs : Real.sqrt (b ^ 2 - 4 * a * g) ^ 2 = b ^ 2 - 4 * a * g :=
    Real.sq_sqrt (disc_nonneg b ha hg)
  have ha' : a ≠ 0 := ha.ne'
  unfold root
  generalize Real.sqrt (b ^ 2 - 4 * a * g) = s at hs ⊢
  field_simp
  linear_combination hs

theorem quad_root (b : ℝ) (ha : 0 < a) (hg : g ≤ 0) :
    a * root a b g ^ 2 + b * root a b g + g = 0 := by
  rw [quad_eq b _ ha hg, sub_self, zero_mul]

/-- `a r + b = (b + √(b² - 4ag)) / 2` for the larger root `r`. -/
theorem mul_root_add (b : ℝ) (ha : 0 < a) :
    a * root a b g + b = (b + Real.sqrt (b ^ 2 - 4 * a * g)) / 2 := by
  have ha' : a ≠ 0 := ha.ne'
  unfold root
  field_simp
  ring

theorem mul_root_add_nonneg (b : ℝ) (ha : 0 < a) (hg : g ≤ 0) : 0 ≤ a * root a b g + b := by
  rw [mul_root_add b ha]
  have := add_sqrt_disc_nonneg b ha hg
  linarith

/-- The second factor in `quad_eq` is positive for `θ > 0`. -/
theorem cofactor_pos (b : ℝ) (ha : 0 < a) (hg : g ≤ 0) (hθ : 0 < θ) :
    0 < a * θ + (b + Real.sqrt (b ^ 2 - 4 * a * g)) / 2 := by
  have h1 := add_sqrt_disc_nonneg b ha hg
  have h2 := mul_pos ha hθ
  linarith

theorem quad_neg_iff (b : ℝ) (ha : 0 < a) (hg : g ≤ 0) (hθ : 0 < θ) :
    a * θ ^ 2 + b * θ + g < 0 ↔ θ < root a b g := by
  have hpos := cofactor_pos b ha hg hθ
  rw [quad_eq b θ ha hg]
  constructor
  · intro h
    by_contra hc
    have := mul_nonneg (sub_nonneg.2 (not_lt.1 hc)) hpos.le
    linarith
  · intro h
    exact mul_neg_of_neg_of_pos (sub_neg.2 h) hpos

theorem quad_pos_iff (b : ℝ) (ha : 0 < a) (hg : g ≤ 0) (hθ : 0 < θ) :
    0 < a * θ ^ 2 + b * θ + g ↔ root a b g < θ := by
  have hpos := cofactor_pos b ha hg hθ
  rw [quad_eq b θ ha hg]
  constructor
  · intro h
    by_contra hc
    have := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (not_lt.1 hc)) hpos.le
    linarith
  · intro h
    exact mul_pos (sub_pos.2 h) hpos

theorem quad_eq_zero_iff (b : ℝ) (ha : 0 < a) (hg : g ≤ 0) (hθ : 0 < θ) :
    a * θ ^ 2 + b * θ + g = 0 ↔ θ = root a b g := by
  have hpos := cofactor_pos b ha hg hθ
  rw [quad_eq b θ ha hg, mul_eq_zero, sub_eq_zero]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h hpos.ne'
  · intro h
    exact Or.inl h

theorem root_nonneg (b : ℝ) (ha : 0 < a) (hg : g ≤ 0) : 0 ≤ root a b g := by
  have h1 := abs_le_sqrt_disc b ha hg
  have h2 := le_abs_self b
  unfold root
  exact div_nonneg (by linarith) (by linarith)

/-- The larger root is positive iff `g < 0` or `b < 0`. -/
theorem root_pos_iff (b : ℝ) (ha : 0 < a) (hg : g ≤ 0) : 0 < root a b g ↔ g < 0 ∨ b < 0 := by
  have h2a : (0 : ℝ) < 2 * a := by linarith
  unfold root
  rw [div_pos_iff_of_pos_right h2a]
  constructor
  · intro h
    by_contra hc
    obtain ⟨hg0, hb0⟩ := not_or.1 hc
    have hb0 : 0 ≤ b := not_lt.1 hb0
    have hg' : g = 0 := le_antisymm hg (not_lt.1 hg0)
    rw [hg', mul_zero, sub_zero, Real.sqrt_sq hb0] at h
    linarith
  · rintro (h | h)
    · have h1 := abs_lt_sqrt_disc b ha h
      have h2 := le_abs_self b
      linarith
    · have h1 := abs_le_sqrt_disc b ha hg
      have h2 := abs_nonneg b
      linarith

/-- The larger root is `< 1` iff the quadratic is positive at `1`. -/
theorem root_lt_one_iff (b : ℝ) (ha : 0 < a) (hg : g ≤ 0) : root a b g < 1 ↔ 0 < a + b + g := by
  have h := quad_pos_iff (θ := 1) b ha hg one_pos
  rw [← h]
  ring_nf

/-- The larger root is `≤ 1` iff the quadratic is nonnegative at `1`. -/
theorem root_le_one_iff (b : ℝ) (ha : 0 < a) (hg : g ≤ 0) : root a b g ≤ 1 ↔ 0 ≤ a + b + g := by
  have h := quad_neg_iff (θ := 1) b ha hg one_pos
  rw [← not_lt, ← not_lt, ← h]
  ring_nf

/-- `(1 - r) (a r + (a + b)) = a + b + g` for the larger root `r`. -/
theorem one_sub_root_mul (b : ℝ) (ha : 0 < a) (hg : g ≤ 0) :
    (1 - root a b g) * (a * root a b g + (a + b)) = a + b + g := by
  have h := quad_root b ha hg
  linear_combination (-1 : ℝ) * h

/-- Sign of `2 (s h) / den` for `s, den > 0`. -/
theorem sign_aux {s h den : ℝ} (hs : 0 < s) (hden : 0 < den) :
    (2 * (s * h) / den < 0 ↔ h < 0) ∧ (0 < 2 * (s * h) / den ↔ 0 < h) ∧
      (2 * (s * h) / den = 0 ↔ h = 0) := by
  have hk : 0 < 2 * s / den := by positivity
  have e : 2 * (s * h) / den = 2 * s / den * h := by ring
  rw [e]
  refine ⟨⟨fun h' => ?_, fun h' => mul_neg_of_pos_of_neg hk h'⟩,
    ⟨fun h' => ?_, fun h' => mul_pos hk h'⟩, ?_⟩
  · by_contra hc
    have := mul_nonneg hk.le (not_lt.1 hc)
    linarith
  · by_contra hc
    have := mul_nonpos_of_nonneg_of_nonpos hk.le (not_lt.1 hc)
    linarith
  · rw [mul_eq_zero]
    exact ⟨fun h' => h'.resolve_left hk.ne', Or.inr⟩

end LossThreshold

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace LossThreshold

variable (P : Spec ι) (N : Noise ι)

/-! ## Helper lemmas: noise energies, weighted moments, the alignment -/

theorem nLoss_nonneg (S : Finset ι) : 0 ≤ P.nLoss N S :=
  Finset.sum_nonneg fun i _ => mul_nonneg (P.lam_pos i).le (Spec.kap2_nonneg N i)

theorem nLossD_nonneg : 0 ≤ P.nLossD N := nLoss_nonneg P N _
theorem nLossB_nonneg : 0 ≤ P.nLossB N := nLoss_nonneg P N _

/-- `n^loss_S > 0` iff the noise has a non-zero component in the block `S`. -/
theorem nLoss_pos_iff (S : Finset ι) : 0 < P.nLoss N S ↔ ∃ i ∈ S, 0 < N.kap2 i := by
  unfold Spec.nLoss
  rw [Finset.sum_pos_iff_of_nonneg
    (fun i _ => mul_nonneg (P.lam_pos i).le (Spec.kap2_nonneg N i))]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, hi, lt_of_mul_lt_mul_left (by rwa [mul_zero]) (P.lam_pos i).le⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨i, hi, mul_pos (P.lam_pos i) h⟩

theorem nLoss_pos_of_smin_pos {S : Finset ι} (hS : S.Nonempty) (h : 0 < N.smin) :
    0 < P.nLoss N S := by
  obtain ⟨i, hi⟩ := hS
  exact (nLoss_pos_iff P N S).2 ⟨i, hi, lt_of_lt_of_le h (N.smin_le i)⟩

/-- If the noise covariance is positive definite (`s_min > 0`) then `n^loss_𝒟 > 0`. -/
theorem nLossD_pos_of_smin_pos (h : 0 < N.smin) : 0 < P.nLossD N :=
  nLoss_pos_of_smin_pos P N P.D_nonempty h

/-- If the noise covariance is positive definite (`s_min > 0`) then `n^loss_ℬ > 0`. -/
theorem nLossB_pos_of_smin_pos (h : 0 < N.smin) : 0 < P.nLossB N :=
  nLoss_pos_of_smin_pos P N P.B_nonempty h

/-- A weighted moment `∑_{i∈S} λ_i^p c_i²` is positive iff the state has a non-zero coordinate in
`S` (for any exponent `p`, since `λ_i > 0`). -/
theorem mom_pos_iff (S : Finset ι) (p : ℕ) (c : ι → ℝ) :
    0 < P.mom S p c ↔ ∃ i ∈ S, c i ≠ 0 := by
  unfold Spec.mom
  rw [Finset.sum_pos_iff_of_nonneg
    (fun i _ => mul_nonneg (pow_nonneg (P.lam_pos i).le p) (sq_nonneg (c i)))]
  constructor
  · rintro ⟨i, hi, h⟩
    refine ⟨i, hi, fun h0 => ?_⟩
    rw [h0] at h
    simp at h
  · rintro ⟨i, hi, h⟩
    exact ⟨i, hi, mul_pos (pow_pos (P.lam_pos i) p) (by positivity)⟩

/-- Positivity of a weighted moment does not depend on the exponent. -/
theorem mom_pos_of_mom_pos {S : Finset ι} (p q : ℕ) {c : ι → ℝ} (h : 0 < P.mom S p c) :
    0 < P.mom S q c :=
  (mom_pos_iff P S q c).2 ((mom_pos_iff P S p c).1 h)

theorem mom_eq_zero_iff (S : Finset ι) (p : ℕ) (c : ι → ℝ) :
    P.mom S p c = 0 ↔ ∀ i ∈ S, c i = 0 := by
  have h := mom_pos_iff P S p c
  have h0 := P.mom_nonneg S p c
  constructor
  · intro hz i hi
    by_contra hne
    have := h.2 ⟨i, hi, hne⟩
    linarith
  · intro hz
    by_contra hne
    obtain ⟨i, hi, hci⟩ := h.1 (lt_of_le_of_ne h0 (Ne.symm hne))
    exact hci (hz i hi)

/-- `∑_{i∈S} λ_i^{p+1} c_i² ≤ M ∑_{i∈S} λ_i^p c_i²` if `λ_i ≤ M` on `S`. -/
theorem mom_succ_le_mul {S : Finset ι} {M : ℝ} (h : ∀ i ∈ S, P.lam i ≤ M) (p : ℕ)
    (c : ι → ℝ) : P.mom S (p + 1) c ≤ M * P.mom S p c := by
  unfold Spec.mom
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have h2 : 0 ≤ P.lam i ^ p * c i ^ 2 :=
    mul_nonneg (pow_nonneg (P.lam_pos i).le p) (sq_nonneg _)
  calc P.lam i ^ (p + 1) * c i ^ 2 = P.lam i * (P.lam i ^ p * c i ^ 2) := by ring
    _ ≤ M * (P.lam i ^ p * c i ^ 2) := mul_le_mul_of_nonneg_right (h i hi) h2

/-- `M ∑_{i∈S} λ_i^p c_i² ≤ ∑_{i∈S} λ_i^{p+1} c_i²` if `M ≤ λ_i` on `S`. -/
theorem mul_mom_le_mom_succ {S : Finset ι} {M : ℝ} (h : ∀ i ∈ S, M ≤ P.lam i) (p : ℕ)
    (c : ι → ℝ) : M * P.mom S p c ≤ P.mom S (p + 1) c := by
  unfold Spec.mom
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have h2 : 0 ≤ P.lam i ^ p * c i ^ 2 :=
    mul_nonneg (pow_nonneg (P.lam_pos i).le p) (sq_nonneg _)
  calc M * (P.lam i ^ p * c i ^ 2) ≤ P.lam i * (P.lam i ^ p * c i ^ 2) :=
        mul_le_mul_of_nonneg_right (h i hi) h2
    _ = P.lam i ^ (p + 1) * c i ^ 2 := by ring

/-- `λ_k s^𝒟 ≤ τ^𝒟`. -/
theorem lamk_mul_sD_le_tauD (c : ι → ℝ) : P.lamk * P.sD c ≤ P.tauD c :=
  mul_mom_le_mom_succ P (fun i hi => P.lamk_le i hi) 2 c

/-- `τ^𝒟 ≤ λ_1 s^𝒟`. -/
theorem tauD_le_lam1_mul_sD (c : ι → ℝ) : P.tauD c ≤ P.lam1 * P.sD c :=
  mom_succ_le_mul P (fun i hi => P.le_lam1 i hi) 2 c

/-- `τ^ℬ ≤ λ_{k+1} s^ℬ`. -/
theorem tauB_le_lamk1_mul_sB (c : ι → ℝ) : P.tauB c ≤ P.lamk1 * P.sB c :=
  mom_succ_le_mul P (fun _ hi => P.le_lamk1_of_mem_B hi) 2 c

/-- `λ_d s^ℬ ≤ τ^ℬ`. -/
theorem lamd_mul_sB_le_tauB (c : ι → ℝ) : P.lamd * P.sB c ≤ P.tauB c :=
  mul_mom_le_mom_succ P (fun _ hi => P.lamd_le_of_mem_B hi) 2 c

/-- The denominator `τ^S + n^loss_S` of `η^loss_S` is nonnegative. -/
theorem lossDen_nonneg (S : Finset ι) (c : ι → ℝ) : 0 ≤ P.mom S 3 c + P.nLoss N S :=
  add_nonneg (P.mom_nonneg S 3 c) (nLoss_nonneg P N S)

/-- The denominator `τ^S + n^loss_S` of `η^loss_S` is positive iff the state or the noise has a
non-zero component in the block `S`. -/
theorem lossDen_pos_iff (S : Finset ι) (c : ι → ℝ) :
    0 < P.mom S 3 c + P.nLoss N S ↔ (∃ i ∈ S, c i ≠ 0) ∨ ∃ i ∈ S, 0 < N.kap2 i := by
  rw [← mom_pos_iff P S 3 c, ← nLoss_pos_iff P N S]
  have h1 := P.mom_nonneg S 3 c
  have h2 := nLoss_nonneg P N S
  constructor
  · intro h
    by_contra hc
    obtain ⟨h3, h4⟩ := not_or.1 hc
    linarith [not_lt.1 h3, not_lt.1 h4]
  · rintro (h | h) <;> linarith

/-- `s^S > 0` implies that the denominator `τ^S + n^loss_S` of `η^loss_S` is positive. -/
theorem lossDen_pos_of_mom_pos {S : Finset ι} {c : ι → ℝ} (h : 0 < P.mom S 2 c) :
    0 < P.mom S 3 c + P.nLoss N S :=
  add_pos_of_pos_of_nonneg (mom_pos_of_mom_pos P 2 3 h) (nLoss_nonneg P N S)

/-- `n^loss_S > 0` implies that the denominator `τ^S + n^loss_S` of `η^loss_S` is positive. -/
theorem lossDen_pos_of_nLoss_pos {S : Finset ι} (c : ι → ℝ) (h : 0 < P.nLoss N S) :
    0 < P.mom S 3 c + P.nLoss N S :=
  add_pos_of_nonneg_of_pos (P.mom_nonneg S 3 c) h

/-- If `τ^S + n^loss_S = 0` then also `s^S = 0`. -/
theorem mom_two_eq_zero_of_lossDen_eq_zero {S : Finset ι} {c : ι → ℝ}
    (h : P.mom S 3 c + P.nLoss N S = 0) : P.mom S 2 c = 0 := by
  have h1 := P.mom_nonneg S 3 c
  have h2 := nLoss_nonneg P N S
  have h3 : P.mom S 3 c = 0 := by linarith
  exact (mom_eq_zero_iff P S 2 c).2 ((mom_eq_zero_iff P S 3 c).1 h3)

theorem s_pos_of_sD_pos {c : ι → ℝ} (hD : 0 < P.sD c) : 0 < P.s c := by
  have := P.sB_nonneg c
  unfold Spec.s
  linarith

theorem s_pos_of_sB_pos {c : ι → ℝ} (hB : 0 < P.sB c) : 0 < P.s c := by
  have := P.sD_nonneg c
  unfold Spec.s
  linarith

/-- `θ_t > 0` if `s^𝒟 > 0`. -/
theorem theta_pos {c : ι → ℝ} (hD : 0 < P.sD c) : 0 < P.theta c :=
  div_pos hD (s_pos_of_sD_pos P hD)

/-- `θ_t < 1` if `s^ℬ > 0`. -/
theorem theta_lt_one {c : ι → ℝ} (hB : 0 < P.sB c) : P.theta c < 1 := by
  unfold Spec.theta
  rw [div_lt_one (s_pos_of_sB_pos P hB)]
  unfold Spec.s
  linarith

/-- `0 < θ_t < 1` iff both block energies `s^𝒟`, `s^ℬ` are positive, i.e. iff the gradient has a
non-zero component in both the dominant and the bulk subspace. -/
theorem theta_mem_Ioo_iff (c : ι → ℝ) :
    (0 < P.theta c ∧ P.theta c < 1) ↔ (0 < P.sD c ∧ 0 < P.sB c) := by
  constructor
  · rintro ⟨h0, h1⟩
    have hD : 0 < P.sD c := by
      rcases (P.sD_nonneg c).eq_or_lt with h | h
      · exfalso
        unfold Spec.theta at h0
        rw [← h, zero_div] at h0
        exact lt_irrefl _ h0
      · exact h
    refine ⟨hD, ?_⟩
    have hs := s_pos_of_sD_pos P hD
    unfold Spec.theta at h1
    rw [div_lt_one hs] at h1
    unfold Spec.s at h1
    linarith
  · rintro ⟨hD, hB⟩
    exact ⟨theta_pos P hD, theta_lt_one P hB⟩

/-- `λ_k ≤ μ^𝒟(3,2)` when `s^𝒟 > 0` (tex 1538–1541). -/
theorem lamk_le_mu_D {c : ι → ℝ} (hD : 0 < P.sD c) : P.lamk ≤ P.mu P.D 3 2 c :=
  (le_div_iff₀ hD).2 (lamk_mul_sD_le_tauD P c)

/-- `μ^𝒟(3,2) ≤ λ_1` when `s^𝒟 > 0`. -/
theorem mu_D_le_lam1 {c : ι → ℝ} (hD : 0 < P.sD c) : P.mu P.D 3 2 c ≤ P.lam1 :=
  (div_le_iff₀ hD).2 (tauD_le_lam1_mul_sD P c)

/-- `μ^ℬ(3,2) ≤ λ_{k+1}` when `s^ℬ > 0` (tex 1542–1545). -/
theorem mu_B_le_lamk1 {c : ι → ℝ} (hB : 0 < P.sB c) : P.mu P.B 3 2 c ≤ P.lamk1 :=
  (div_le_iff₀ hB).2 (tauB_le_lamk1_mul_sB P c)

/-- `λ_d ≤ μ^ℬ(3,2)` when `s^ℬ > 0`. -/
theorem lamd_le_mu_B {c : ι → ℝ} (hB : 0 < P.sB c) : P.lamd ≤ P.mu P.B 3 2 c :=
  (le_div_iff₀ hB).2 (lamd_mul_sB_le_tauB P c)

/-- `τ^S = μ^S(3,2) s^S` (tex 1698), valid when `s^S > 0`. -/
theorem mu_mul_mom {S : Finset ι} {c : ι → ℝ} (h : 0 < P.mom S 2 c) :
    P.mu S 3 2 c * P.mom S 2 c = P.mom S 3 c :=
  div_mul_cancel₀ _ h.ne'

/-- Weighted moments scale quadratically with the state. -/
theorem mom_smul (S : Finset ι) (p : ℕ) (t : ℝ) (c : ι → ℝ) :
    P.mom S p (fun i => t * c i) = t ^ 2 * P.mom S p c := by
  unfold Spec.mom
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The alignment is invariant under rescaling of the state. -/
theorem theta_smul {t : ℝ} (ht : t ≠ 0) (c : ι → ℝ) :
    P.theta (fun i => t * c i) = P.theta c := by
  unfold Spec.theta Spec.s Spec.sD Spec.sB
  rw [mom_smul, mom_smul, ← mul_add, mul_div_mul_left _ _ (pow_ne_zero 2 ht)]

end LossThreshold

namespace Spec

open LossThreshold

variable (P : Spec ι) (N : Noise ι)

/-! ## Theorem 10: step size condition for projected updates -/

theorem etaLoss_nonneg (S : Finset ι) (c : ι → ℝ) : 0 ≤ P.etaLoss N S c :=
  div_nonneg (mul_nonneg zero_le_two (P.mom_nonneg S 2 c)) (lossDen_nonneg P N S c)

/-- `η^loss_S > 0` as soon as `s^S > 0`. -/
theorem etaLoss_pos {S : Finset ι} {c : ι → ℝ} (h : 0 < P.mom S 2 c) : 0 < P.etaLoss N S c :=
  div_pos (mul_pos zero_lt_two h) (lossDen_pos_of_mom_pos P N h)

/-- Pathwise one-step loss change of the `S`-projected update, coordinate by coordinate:
`L(x_{t+1}) - L(x_t) = ∑_{i∈S} (λ_i/2) (c_{i,t+1}² - c_{i,t}²)`. -/
theorem loss_cNextProj_sub_loss_eq_sum (S : Finset ι) (η : ℝ) (c ζ : ι → ℝ) :
    P.loss (P.cNextProj S η c ζ) - P.loss c =
      ∑ i ∈ S, P.lam i / 2 * (((1 - η * P.lam i) * c i - η * ζ i) ^ 2 - c i ^ 2) := by
  have key : ∀ i, P.lam i * P.cNextProj S η c ζ i ^ 2 - P.lam i * c i ^ 2 =
      if i ∈ S then
        2 * (P.lam i / 2 * (((1 - η * P.lam i) * c i - η * ζ i) ^ 2 - c i ^ 2))
      else 0 := by
    intro i
    unfold cNextProj
    split_ifs <;> ring
  unfold loss
  rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun i _ => key i),
    Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum]
  ring

/-- **Proof of Theorem 10, first display** (tex 1492–1495).  Pathwise one-step loss change of the
`S`-projected update `x⁺ = x - η g`, `g = P^S (A x + ξ)`:
`L(x⁺) - L(x) = -η gᵀ A x + (η²/2) gᵀ A g`, where in eigen-coordinates `g_i = λ_i c_i + ζ_i` for
`i ∈ S` (and `g_i = 0` otherwise). -/
theorem loss_cNextProj_sub_loss (S : Finset ι) (η : ℝ) (c ζ : ι → ℝ) :
    P.loss (P.cNextProj S η c ζ) - P.loss c =
      -η * ∑ i ∈ S, (P.lam i * c i + ζ i) * (P.lam i * c i) +
        η ^ 2 / 2 * ∑ i ∈ S, P.lam i * (P.lam i * c i + ζ i) ^ 2 := by
  rw [P.loss_cNextProj_sub_loss_eq_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Theorem 10, the expected loss change as a sum over coordinates.**
`-η s^S + (η²/2)(τ^S + n^loss_S) = ∑_{i∈S} (λ_i/2) (𝔼[c_{i,t+1}² | x_t] - c_{i,t}²)` with
`𝔼[c_{i,t+1}² | x_t] = (1 - η λ_i)² c_i² + η² κ_i²`. -/
theorem expLossChange_eq_sum (S : Finset ι) (η : ℝ) (c : ι → ℝ) :
    P.expLossChange N S η c =
      ∑ i ∈ S, P.lam i / 2 *
        ((1 - η * P.lam i) ^ 2 * c i ^ 2 + η ^ 2 * N.kap2 i - c i ^ 2) := by
  unfold expLossChange mom nLoss
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Theorem 10, pathwise decomposition.**  For every realisation `ζ` of the noise,
`L(x_{t+1}) - L(x_t) = expLossChange - η ∑_{i∈S} λ_i (1 - η λ_i) c_i ζ_i
  + (η²/2) ∑_{i∈S} λ_i (ζ_i² - κ_i²)`.
The last two terms have zero mean as soon as `𝔼 ζ_i = 0` and `𝔼 ζ_i² = κ_i²` for `i ∈ S`, so that
`𝔼[L(x_{t+1}) - L(x_t) | x_t] = expLossChange = -η s^S + (η²/2)(τ^S + n^loss_S)`. -/
theorem loss_cNextProj_sub_loss_eq_expLossChange_add (S : Finset ι) (η : ℝ) (c ζ : ι → ℝ) :
    P.loss (P.cNextProj S η c ζ) - P.loss c =
      P.expLossChange N S η c
        - η * ∑ i ∈ S, P.lam i * (1 - η * P.lam i) * c i * ζ i
        + η ^ 2 / 2 * ∑ i ∈ S, P.lam i * (ζ i ^ 2 - N.kap2 i) := by
  rw [P.loss_cNextProj_sub_loss_eq_sum, P.expLossChange_eq_sum N, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Theorem 10, expectation for finitely supported noise** (a purely algebraic instance of the
expectation; the measure-theoretic version belongs to the probability layer).  If the noise takes
finitely many values `ζ ω` with weights `w ω` summing to one, and has mean `0` and second moments
`κ_i²` in the directions `i ∈ S`, then the average one-step loss change of the `S`-projected update
is `expLossChange = -η s^S + (η²/2)(τ^S + n^loss_S)`. -/
theorem weighted_sum_loss_change {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (ζ : Ω → ι → ℝ)
    (S : Finset ι) (η : ℝ) (c : ι → ℝ) (hw : ∑ ω, w ω = 1)
    (hmean : ∀ i ∈ S, ∑ ω, w ω * ζ ω i = 0)
    (hvar : ∀ i ∈ S, ∑ ω, w ω * ζ ω i ^ 2 = N.kap2 i) :
    ∑ ω, w ω * (P.loss (P.cNextProj S η c (ζ ω)) - P.loss c) = P.expLossChange N S η c := by
  have h1 : ∑ ω, w ω * ∑ i ∈ S, P.lam i * (1 - η * P.lam i) * c i * ζ ω i = 0 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i hi => ?_
    calc ∑ ω, w ω * (P.lam i * (1 - η * P.lam i) * c i * ζ ω i)
        = P.lam i * (1 - η * P.lam i) * c i * ∑ ω, w ω * ζ ω i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ω _ => by ring
      _ = 0 := by rw [hmean i hi, mul_zero]
  have h2 : ∑ ω, w ω * ∑ i ∈ S, P.lam i * (ζ ω i ^ 2 - N.kap2 i) = 0 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i hi => ?_
    calc ∑ ω, w ω * (P.lam i * (ζ ω i ^ 2 - N.kap2 i))
        = P.lam i * (∑ ω, w ω * ζ ω i ^ 2 - (∑ ω, w ω) * N.kap2 i) := by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.mul_sum]
          exact Finset.sum_congr rfl fun ω _ => by ring
      _ = 0 := by rw [hvar i hi, hw]; ring
  calc ∑ ω, w ω * (P.loss (P.cNextProj S η c (ζ ω)) - P.loss c)
      = (∑ ω, w ω) * P.expLossChange N S η c
          - η * ∑ ω, w ω * ∑ i ∈ S, P.lam i * (1 - η * P.lam i) * c i * ζ ω i
          + η ^ 2 / 2 * ∑ ω, w ω * ∑ i ∈ S, P.lam i * (ζ ω i ^ 2 - N.kap2 i) := by
        rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [P.loss_cNextProj_sub_loss_eq_expLossChange_add N]
        ring
    _ = P.expLossChange N S η c := by rw [hw, h1, h2]; ring

section Thm10
variable {S : Finset ι} {η : ℝ} {c : ι → ℝ}

/-- The expected loss change factors as `((τ^S + n^loss_S)/2) · η · (η - η^loss_S)`. -/
theorem expLossChange_eq_factor (hden : P.mom S 3 c + P.nLoss N S ≠ 0) :
    P.expLossChange N S η c =
      (P.mom S 3 c + P.nLoss N S) / 2 * η * (η - P.etaLoss N S c) := by
  unfold expLossChange etaLoss
  field_simp
  ring

/-- **Theorem 10 (Step Size Condition for Projected Updates).**  For the `S`-projected update
(`S = 𝒟`: DSGD, `S = ℬ`: BSGD) the expected one-step loss change is negative iff
`0 < η < η^loss_S = 2 s^S / (τ^S + n^loss_S)`.

The only hypothesis is that the denominator `τ^S + n^loss_S` is positive (i.e. the state or the
noise has a non-zero component in `S`, see `LossThreshold.lossDen_pos_iff`).  Neither `s^S > 0`
nor `η > 0` is assumed: `η` is an arbitrary real number and `0 < η` is part of the equivalence. -/
theorem expLossChange_neg_iff (hden : 0 < P.mom S 3 c + P.nLoss N S) :
    P.expLossChange N S η c < 0 ↔ 0 < η ∧ η < P.etaLoss N S c := by
  have ha := P.mom_nonneg S 2 c
  rw [etaLoss, lt_div_iff₀ hden]
  unfold expLossChange
  constructor
  · intro h
    have hη : 0 < η := by
      by_contra hc
      have h1 := mul_nonneg (neg_nonneg.2 (not_lt.1 hc)) ha
      have h2 := mul_nonneg (sq_nonneg η) hden.le
      nlinarith
    refine ⟨hη, ?_⟩
    by_contra hc
    have := mul_nonneg hη.le (sub_nonneg.2 (not_lt.1 hc))
    nlinarith
  · rintro ⟨hη, h⟩
    have := mul_pos hη (sub_pos.2 h)
    nlinarith

/-- Theorem 10 for a positive step size (the paper's standing convention `η_t > 0`):
`𝔼[L(x_{t+1}) - L(x_t) | x_t] < 0 ↔ η < η^loss_S`. -/
theorem expLossChange_neg_iff_of_pos (hden : 0 < P.mom S 3 c + P.nLoss N S) (hη : 0 < η) :
    P.expLossChange N S η c < 0 ↔ η < P.etaLoss N S c := by
  rw [P.expLossChange_neg_iff N hden]
  exact ⟨fun h => h.2, fun h => ⟨hη, h⟩⟩

/-- **Theorem 10, the loss-increasing side.**  The expected one-step loss change of the
`S`-projected update is positive iff `η < 0` or `η > η^loss_S`. -/
theorem expLossChange_pos_iff (hden : 0 < P.mom S 3 c + P.nLoss N S) :
    0 < P.expLossChange N S η c ↔ η < 0 ∨ P.etaLoss N S c < η := by
  have ha := P.mom_nonneg S 2 c
  rw [etaLoss, div_lt_iff₀ hden]
  unfold expLossChange
  constructor
  · intro h
    by_contra hc
    obtain ⟨h1, h2⟩ := not_or.1 hc
    have := mul_nonneg (not_lt.1 h1) (sub_nonneg.2 (not_lt.1 h2))
    nlinarith
  · rintro (h | h)
    · have h1 := mul_nonneg (neg_pos.2 h).le ha
      have h2 := mul_pos (pow_pos (neg_pos.2 h) 2) hden
      nlinarith
    · have h0 : 0 < η := by
        by_contra hc
        have := mul_nonneg (neg_nonneg.2 (not_lt.1 hc)) hden.le
        nlinarith
      have := mul_pos h0 (sub_pos.2 h)
      nlinarith

/-- **Theorem 10, the loss-increasing side for positive step sizes**: for `η > 0`,
`𝔼[L(x_{t+1}) - L(x_t) | x_t] > 0 ↔ η > η^loss_S`. -/
theorem expLossChange_pos_iff_of_pos (hden : 0 < P.mom S 3 c + P.nLoss N S) (hη : 0 < η) :
    0 < P.expLossChange N S η c ↔ P.etaLoss N S c < η := by
  rw [P.expLossChange_pos_iff N hden]
  constructor
  · rintro (h | h)
    · exact absurd h (not_lt.2 hη.le)
    · exact h
  · exact Or.inr

/-- The expected loss change vanishes exactly at `η = 0` and at the threshold `η = η^loss_S`. -/
theorem expLossChange_eq_zero_iff (hden : 0 < P.mom S 3 c + P.nLoss N S) :
    P.expLossChange N S η c = 0 ↔ η = 0 ∨ η = P.etaLoss N S c := by
  have hden2 : (P.mom S 3 c + P.nLoss N S) / 2 ≠ 0 := (half_pos hden).ne'
  rw [P.expLossChange_eq_factor N hden.ne', mul_eq_zero, mul_eq_zero, sub_eq_zero]
  constructor
  · rintro ((h | h) | h)
    · exact absurd h hden2
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

/-- Degenerate case of Theorem 10: if `τ^S + n^loss_S = 0` (the state and the noise both vanish
on `S`) the expected loss change is identically `0`; no step size decreases the expected loss, and
the paper's threshold `η^loss_S` is the undefined expression `0/0`. -/
theorem expLossChange_eq_zero_of_lossDen_eq_zero (η : ℝ)
    (h : P.mom S 3 c + P.nLoss N S = 0) : P.expLossChange N S η c = 0 := by
  unfold expLossChange
  rw [h, mom_two_eq_zero_of_lossDen_eq_zero P N h]
  ring

/-- Theorem 10 when `s^S = 0`: the projected update never decreases the expected loss
(consistently with `η^loss_S = 0` when `n^loss_S > 0`). -/
theorem expLossChange_nonneg_of_mom_eq_zero (η : ℝ) (h : P.mom S 2 c = 0) :
    0 ≤ P.expLossChange N S η c := by
  unfold expLossChange
  rw [h, mul_zero, zero_add]
  exact mul_nonneg (by positivity) (lossDen_nonneg P N S c)

/-- Bookkeeping about Lean's convention `x / 0 = 0` (not a claim of the paper): in the degenerate
case `τ^S + n^loss_S = 0` the formal expression `Spec.etaLoss` evaluates to `0`, so that the
interval `(0, η^loss_S)` is empty — consistently with
`Spec.expLossChange_eq_zero_of_lossDen_eq_zero`.  None of the theorems of this file relies on
this. -/
theorem etaLoss_eq_zero_of_lossDen_eq_zero (h : P.mom S 3 c + P.nLoss N S = 0) :
    P.etaLoss N S c = 0 := by
  unfold etaLoss
  rw [h, div_zero]

end Thm10

/-- **Theorem 10 (Step Size Condition for Projected Updates)**, as displayed in the paper
(tex 554–565), for the dominant and the bulk projected updates:
`𝔼[L(x_{t+1}) - L(x_t) | x_t] < 0 ↔ 0 < η_t < η^loss_S(x_t)` for `S = 𝒟` and for `S = ℬ`.

Hypotheses made explicit: the denominators `τ^S + n^loss_S` are positive. -/
theorem proj_loss_step_size_condition {c : ι → ℝ} (η : ℝ)
    (hdD : 0 < P.tauD c + P.nLossD N) (hdB : 0 < P.tauB c + P.nLossB N) :
    (P.expLossChange N P.D η c < 0 ↔ 0 < η ∧ η < P.etaLossD N c) ∧
      (P.expLossChange N P.B η c < 0 ↔ 0 < η ∧ η < P.etaLossB N c) :=
  ⟨P.expLossChange_neg_iff N hdD, P.expLossChange_neg_iff N hdB⟩

/-! ## "Additional Notion" and the crossover quadratic (Appendix A.5, first lemma) -/

/-- Quantitative form of `α_t > 0`: `α_t ≥ s_t (λ_k - λ_{k+1}) = s_t λ_{k+1} (m - 1)`. -/
theorem gap_mul_s_le_alphaT {c : ι → ℝ} (hD : 0 < P.sD c) (hB : 0 < P.sB c) :
    P.s c * P.gap1 ≤ P.alphaT c := by
  have h1 := lamk_le_mu_D P hD
  have h2 := mu_B_le_lamk1 P hB
  unfold alphaT gap1
  exact mul_le_mul_of_nonneg_left (by linarith) (P.s_nonneg c)

/-- `α_t ≤ s_t (λ_1 - λ_d)`. -/
theorem alphaT_le {c : ι → ℝ} (hD : 0 < P.sD c) (hB : 0 < P.sB c) :
    P.alphaT c ≤ P.s c * (P.lam1 - P.lamd) := by
  have h1 := mu_D_le_lam1 P hD
  have h2 := lamd_le_mu_B P hB
  unfold alphaT
  exact mul_le_mul_of_nonneg_left (by linarith) (P.s_nonneg c)

/-- **Lemma (crossover quadratic), item 1**: `α_t > 0`.

The paper claims this "for all `x_t`"; it requires `s^𝒟 > 0` and `s^ℬ > 0` (i.e. `0 < θ_t < 1`):
otherwise one of `μ^𝒟(3,2)`, `μ^ℬ(3,2)` is `0/0` (and `α_t = 0` at `x_t = 0`, see
`Spec.alphaT_zero`). -/
theorem alphaT_pos {c : ι → ℝ} (hD : 0 < P.sD c) (hB : 0 < P.sB c) : 0 < P.alphaT c := by
  have h1 := P.gap_mul_s_le_alphaT hD hB
  have h2 := mul_pos (s_pos_of_sD_pos P hD) P.gap1_pos
  linarith

/-- At the state `x_t = 0` the coefficient `α_t` vanishes: the paper's "`∀ x_t, α_t > 0`" fails
there. -/
theorem alphaT_zero : P.alphaT (0 : ι → ℝ) = 0 := by
  have h : P.s (0 : ι → ℝ) = 0 := (P.s_eq_zero_iff 0).2 rfl
  unfold alphaT
  rw [h, zero_mul]

theorem gammaT_nonpos : P.gammaT N ≤ 0 := neg_nonpos.2 (nLossD_nonneg P N)

/-- **Lemma (crossover quadratic), item 2**: `γ_t < 0`.

The paper claims `n^loss_𝒟 > 0` for every noise; this is an extra hypothesis (it holds e.g. when
`Σ ≻ 0`, see `LossThreshold.nLossD_pos_of_smin_pos`, but not for every `Σ ⪰ 0` with
`Tr Σ > 0`). -/
theorem gammaT_neg (hnD : 0 < P.nLossD N) : P.gammaT N < 0 := neg_neg_of_pos hnD

/-- `γ_t < 0` iff `n^loss_𝒟 > 0`: without noise in the dominant block, `γ_t = 0`. -/
theorem gammaT_neg_iff : P.gammaT N < 0 ↔ 0 < P.nLossD N := by
  unfold gammaT
  exact neg_lt_zero

/-- `h(0) = γ_t`. -/
theorem hQuad_zero (c : ι → ℝ) : P.hQuad N c 0 = P.gammaT N := by
  unfold hQuad
  ring

/-- `h(1) = α_t + β_t + γ_t`. -/
theorem hQuad_one_eq_sum (c : ι → ℝ) :
    P.hQuad N c 1 = P.alphaT c + P.betaT N c + P.gammaT N := by
  unfold hQuad
  ring

/-- `h(1) = n^loss_ℬ` (tex 1559–1563). -/
theorem hQuad_one (c : ι → ℝ) : P.hQuad N c 1 = P.nLossB N := by
  unfold hQuad betaT gammaT
  ring

/-- `α_t + β_t + γ_t = n^loss_ℬ`. -/
theorem alphaT_add_betaT_add_gammaT (c : ι → ℝ) :
    P.alphaT c + P.betaT N c + P.gammaT N = P.nLossB N := by
  unfold betaT gammaT
  ring

/-- **Lemma (crossover quadratic properties)** (tex 1514–1522,
`lem:crossover-quadratic-properties`): `α_t > 0`, `γ_t < 0`, `h(0) = γ_t < 0` and
`h(1) = α_t + β_t + γ_t > 0`.

Hypotheses made explicit: `s^𝒟 > 0`, `s^ℬ > 0` (for `α_t`), `n^loss_𝒟 > 0` (for `γ_t`) and
`n^loss_ℬ > 0` (for `h(1)`). -/
theorem crossover_quadratic_properties {c : ι → ℝ} (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hnD : 0 < P.nLossD N) (hnB : 0 < P.nLossB N) :
    0 < P.alphaT c ∧ P.gammaT N < 0 ∧
      (P.hQuad N c 0 = P.gammaT N ∧ P.hQuad N c 0 < 0) ∧
      (P.hQuad N c 1 = P.alphaT c + P.betaT N c + P.gammaT N ∧ 0 < P.hQuad N c 1) := by
  refine ⟨P.alphaT_pos hD hB, P.gammaT_neg N hnD, ⟨P.hQuad_zero N c, ?_⟩,
    ⟨P.hQuad_one_eq_sum N c, ?_⟩⟩
  · rw [P.hQuad_zero]
    exact P.gammaT_neg N hnD
  · rw [P.hQuad_one]
    exact hnB

/-! ## The critical root (Appendix A.5, second lemma)

The statements of this section are stated under the hypothesis `0 < α_t` (which holds as soon as
`s^𝒟 > 0` and `s^ℬ > 0`, see `Spec.alphaT_pos`). -/

/-- The explicit formula for `θ^crit_t` (this is the definition `Spec.thetaCrit`). -/
theorem thetaCrit_eq (c : ι → ℝ) :
    P.thetaCrit N c =
      (-P.betaT N c + Real.sqrt (P.betaT N c ^ 2 - 4 * P.alphaT c * P.gammaT N)) /
        (2 * P.alphaT c) := rfl

theorem thetaCrit_eq_root (c : ι → ℝ) :
    P.thetaCrit N c = LossThreshold.root (P.alphaT c) (P.betaT N c) (P.gammaT N) := rfl

/-- The discriminant `β_t² - 4 α_t γ_t` of `h` is nonnegative. -/
theorem hQuad_disc_nonneg {c : ι → ℝ} (hα : 0 < P.alphaT c) :
    0 ≤ P.betaT N c ^ 2 - 4 * P.alphaT c * P.gammaT N :=
  LossThreshold.disc_nonneg _ hα (P.gammaT_nonpos N)

/-- `θ^crit_t` depends on the state only through `α_t` (i.e. through `s_t`, `μ^𝒟(3,2)` and
`μ^ℬ(3,2)`): two states with the same `α` have the same critical alignment.  In particular
`θ^crit_t` is **not** a function of the alignment `θ_t` alone. -/
theorem thetaCrit_congr {c c' : ι → ℝ} (h : P.alphaT c = P.alphaT c') :
    P.thetaCrit N c = P.thetaCrit N c' := by
  unfold thetaCrit betaT
  rw [h]

section CriticalRoot
variable {c : ι → ℝ} {θ : ℝ}

/-- `θ^crit_t` is a root of `h`. -/
theorem hQuad_thetaCrit (hα : 0 < P.alphaT c) : P.hQuad N c (P.thetaCrit N c) = 0 :=
  LossThreshold.quad_root _ hα (P.gammaT_nonpos N)

/-- `h(θ) < 0 ↔ θ < θ^crit_t`, for every `θ > 0`. -/
theorem hQuad_neg_iff (hα : 0 < P.alphaT c) (hθ : 0 < θ) :
    P.hQuad N c θ < 0 ↔ θ < P.thetaCrit N c :=
  LossThreshold.quad_neg_iff _ hα (P.gammaT_nonpos N) hθ

/-- `h(θ) > 0 ↔ θ > θ^crit_t`, for every `θ > 0`. -/
theorem hQuad_pos_iff (hα : 0 < P.alphaT c) (hθ : 0 < θ) :
    0 < P.hQuad N c θ ↔ P.thetaCrit N c < θ :=
  LossThreshold.quad_pos_iff _ hα (P.gammaT_nonpos N) hθ

/-- `θ^crit_t` is the only positive root of `h`. -/
theorem hQuad_eq_zero_iff (hα : 0 < P.alphaT c) (hθ : 0 < θ) :
    P.hQuad N c θ = 0 ↔ θ = P.thetaCrit N c :=
  LossThreshold.quad_eq_zero_iff _ hα (P.gammaT_nonpos N) hθ

theorem thetaCrit_nonneg (hα : 0 < P.alphaT c) : 0 ≤ P.thetaCrit N c :=
  LossThreshold.root_nonneg _ hα (P.gammaT_nonpos N)

theorem thetaCrit_le_one (hα : 0 < P.alphaT c) : P.thetaCrit N c ≤ 1 := by
  rw [thetaCrit_eq_root, LossThreshold.root_le_one_iff _ hα (P.gammaT_nonpos N),
    P.alphaT_add_betaT_add_gammaT]
  exact nLossB_nonneg P N

/-- `θ^crit_t < 1` iff there is noise in the bulk block, `n^loss_ℬ > 0`. -/
theorem thetaCrit_lt_one_iff (hα : 0 < P.alphaT c) : P.thetaCrit N c < 1 ↔ 0 < P.nLossB N := by
  rw [thetaCrit_eq_root, LossThreshold.root_lt_one_iff _ hα (P.gammaT_nonpos N),
    P.alphaT_add_betaT_add_gammaT]

/-- `θ^crit_t > 0` iff there is noise in the dominant block (`n^loss_𝒟 > 0`), or else the bulk
noise is small, `n^loss_ℬ < α_t`. -/
theorem thetaCrit_pos_iff (hα : 0 < P.alphaT c) :
    0 < P.thetaCrit N c ↔ 0 < P.nLossD N ∨ P.nLossB N < P.alphaT c := by
  rw [thetaCrit_eq_root, LossThreshold.root_pos_iff _ hα (P.gammaT_nonpos N),
    P.gammaT_neg_iff]
  have hnD := nLossD_nonneg P N
  unfold betaT
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · exact Or.inl h
    · rcases hnD.eq_or_lt with h0 | h0
      · exact Or.inr (by linarith)
      · exact Or.inl h0

theorem thetaCrit_pos (hα : 0 < P.alphaT c) (hnD : 0 < P.nLossD N) : 0 < P.thetaCrit N c :=
  (P.thetaCrit_pos_iff N hα).2 (Or.inl hnD)

theorem thetaCrit_lt_one (hα : 0 < P.alphaT c) (hnB : 0 < P.nLossB N) : P.thetaCrit N c < 1 :=
  (P.thetaCrit_lt_one_iff N hα).2 hnB

/-- `θ^crit_t ∈ (0, 1)`, provided `n^loss_𝒟 > 0` and `n^loss_ℬ > 0`. -/
theorem thetaCrit_mem_Ioo (hα : 0 < P.alphaT c) (hnD : 0 < P.nLossD N)
    (hnB : 0 < P.nLossB N) : P.thetaCrit N c ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨P.thetaCrit_pos N hα hnD, P.thetaCrit_lt_one N hα hnB⟩

/-- Without noise in the bulk block the critical alignment is `1`: the "high-alignment regime"
`θ_t > θ^crit_t` is empty. -/
theorem thetaCrit_eq_one (hα : 0 < P.alphaT c) (hnB : P.nLossB N = 0) :
    P.thetaCrit N c = 1 := by
  refine le_antisymm (P.thetaCrit_le_one N hα) (not_lt.1 fun h => ?_)
  have := (P.thetaCrit_lt_one_iff N hα).1 h
  linarith

/-- Without noise in the dominant block and with `α_t ≤ n^loss_ℬ`, the critical alignment is `0`:
the "low-alignment regime" `θ_t < θ^crit_t` is empty. -/
theorem thetaCrit_eq_zero (hα : 0 < P.alphaT c) (hnD : P.nLossD N = 0)
    (h : P.alphaT c ≤ P.nLossB N) : P.thetaCrit N c = 0 := by
  refine le_antisymm (not_lt.1 fun h' => ?_) (P.thetaCrit_nonneg N hα)
  rcases (P.thetaCrit_pos_iff N hα).1 h' with h1 | h1 <;> linarith

/-- `h` has exactly one root in `(0, 1)`, namely `θ^crit_t`. -/
theorem existsUnique_hQuad_root (hα : 0 < P.alphaT c) (hnD : 0 < P.nLossD N)
    (hnB : 0 < P.nLossB N) : ∃! θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) 1 ∧ P.hQuad N c θ = 0 := by
  refine ⟨P.thetaCrit N c, ⟨P.thetaCrit_mem_Ioo N hα hnD hnB, P.hQuad_thetaCrit N hα⟩, ?_⟩
  rintro θ ⟨hθ, h0⟩
  exact (P.hQuad_eq_zero_iff N hα hθ.1).1 h0

/-- `(1 - θ^crit)(α θ^crit + n^loss_ℬ + n^loss_𝒟) = n^loss_ℬ`: the identity from which the rate of
`1 - θ^crit_t` (Theorem 13) is read off. -/
theorem one_sub_thetaCrit_mul (hα : 0 < P.alphaT c) :
    (1 - P.thetaCrit N c) * (P.alphaT c * P.thetaCrit N c + P.nLossB N + P.nLossD N) =
      P.nLossB N := by
  have h := LossThreshold.one_sub_root_mul (P.betaT N c) hα (P.gammaT_nonpos N)
  have hβ : P.alphaT c + P.betaT N c = P.nLossB N + P.nLossD N := by
    unfold betaT
    ring
  rw [← thetaCrit_eq_root, P.alphaT_add_betaT_add_gammaT, hβ] at h
  linear_combination h

/-- `(1 - θ^crit_t) α_t ≤ n^loss_ℬ`, i.e. `1 - θ^crit_t ≤ n^loss_ℬ / α_t`. -/
theorem one_sub_thetaCrit_mul_alphaT_le (hα : 0 < P.alphaT c) :
    (1 - P.thetaCrit N c) * P.alphaT c ≤ P.nLossB N := by
  have h1 := P.one_sub_thetaCrit_mul N hα
  have h2 : 0 ≤ P.alphaT c * P.thetaCrit N c + P.betaT N c := by
    rw [thetaCrit_eq_root]
    exact LossThreshold.mul_root_add_nonneg _ hα (P.gammaT_nonpos N)
  have h3 : 0 ≤ 1 - P.thetaCrit N c := sub_nonneg.2 (P.thetaCrit_le_one N hα)
  have h4 : P.alphaT c ≤ P.alphaT c * P.thetaCrit N c + P.nLossB N + P.nLossD N := by
    unfold betaT at h2
    linarith
  calc (1 - P.thetaCrit N c) * P.alphaT c
      ≤ (1 - P.thetaCrit N c) * (P.alphaT c * P.thetaCrit N c + P.nLossB N + P.nLossD N) :=
        mul_le_mul_of_nonneg_left h4 h3
    _ = P.nLossB N := h1

/-- `n^loss_ℬ ≤ (1 - θ^crit_t)(α_t + n^loss_ℬ + n^loss_𝒟)`, i.e.
`1 - θ^crit_t ≥ n^loss_ℬ / (α_t + n^loss_ℬ + n^loss_𝒟)`. -/
theorem nLossB_le_one_sub_thetaCrit_mul (hα : 0 < P.alphaT c) :
    P.nLossB N ≤ (1 - P.thetaCrit N c) * (P.alphaT c + P.nLossB N + P.nLossD N) := by
  have h1 := P.one_sub_thetaCrit_mul N hα
  have h3 : 0 ≤ 1 - P.thetaCrit N c := sub_nonneg.2 (P.thetaCrit_le_one N hα)
  have h4 : P.alphaT c * P.thetaCrit N c ≤ P.alphaT c := by
    have := mul_le_mul_of_nonneg_left (P.thetaCrit_le_one N hα) hα.le
    linarith
  calc P.nLossB N
      = (1 - P.thetaCrit N c) * (P.alphaT c * P.thetaCrit N c + P.nLossB N + P.nLossD N) :=
        h1.symm
    _ ≤ (1 - P.thetaCrit N c) * (P.alphaT c + P.nLossB N + P.nLossD N) :=
        mul_le_mul_of_nonneg_left (by linarith) h3

/-- A state-independent lower bound for the (state-dependent) critical alignment:
`n^loss_𝒟 / (n^loss_𝒟 + n^loss_ℬ) < θ^crit_t`.  Consequently every state with
`0 < θ_t ≤ n^loss_𝒟 / (n^loss_𝒟 + n^loss_ℬ)` is in the low-alignment regime. -/
theorem nLossD_div_lt_thetaCrit (hα : 0 < P.alphaT c) (hnD : 0 < P.nLossD N)
    (hnB : 0 < P.nLossB N) : P.nLossD N / (P.nLossD N + P.nLossB N) < P.thetaCrit N c := by
  have hsum : 0 < P.nLossD N + P.nLossB N := add_pos hnD hnB
  have h0 : 0 < P.nLossD N / (P.nLossD N + P.nLossB N) := div_pos hnD hsum
  have h1 : P.nLossD N / (P.nLossD N + P.nLossB N) < 1 := by
    rw [div_lt_one hsum]
    linarith
  have h2 : (P.nLossB N + P.nLossD N) * (P.nLossD N / (P.nLossD N + P.nLossB N)) =
      P.nLossD N := by
    field_simp
    ring
  rw [← P.hQuad_neg_iff N hα h0]
  unfold hQuad betaT gammaT
  nlinarith [mul_pos (mul_pos hα h0) (sub_pos.2 h1)]

end CriticalRoot

/-- **Lemma (critical root)** (tex 1570–1581, `lem:crossover-quadratic-critical-root`).
`θ^crit_t = (-β_t + √(β_t² - 4 α_t γ_t)) / (2 α_t)` lies in `(0, 1)`, `h < 0` on `(0, θ^crit_t)`,
`h > 0` on `(θ^crit_t, 1)`, and `θ^crit_t` is the unique root of `h` in `(0, 1)`.

Hypotheses made explicit: `s^𝒟 > 0`, `s^ℬ > 0`, `n^loss_𝒟 > 0`, `n^loss_ℬ > 0`. -/
theorem crossover_critical_root {c : ι → ℝ} (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hnD : 0 < P.nLossD N) (hnB : 0 < P.nLossB N) :
    P.thetaCrit N c ∈ Set.Ioo (0 : ℝ) 1 ∧
      (∀ θ ∈ Set.Ioo 0 (P.thetaCrit N c), P.hQuad N c θ < 0) ∧
      (∀ θ ∈ Set.Ioo (P.thetaCrit N c) 1, 0 < P.hQuad N c θ) ∧
      P.hQuad N c (P.thetaCrit N c) = 0 ∧
      (∀ θ ∈ Set.Ioo (0 : ℝ) 1, P.hQuad N c θ = 0 → θ = P.thetaCrit N c) := by
  have hα := P.alphaT_pos hD hB
  have hmem := P.thetaCrit_mem_Ioo N hα hnD hnB
  refine ⟨hmem, ?_, ?_, P.hQuad_thetaCrit N hα, ?_⟩
  · intro θ hθ
    exact (P.hQuad_neg_iff N hα hθ.1).2 hθ.2
  · intro θ hθ
    exact (P.hQuad_pos_iff N hα (lt_trans hmem.1 hθ.1)).2 hθ.1
  · intro θ hθ h0
    exact (P.hQuad_eq_zero_iff N hα hθ.1).1 h0

/-! ## Theorem 11: crossover of the two loss thresholds -/

section Thm11
variable {c : ι → ℝ}

/-- **Proof of Theorem 11, the numerator identity** (tex 1699–1711):
`s^𝒟 (τ^ℬ + n^loss_ℬ) - s^ℬ (τ^𝒟 + n^loss_𝒟) = s_t · h(θ_t)`. -/
theorem lossGap_eq_s_mul_hQuad (hD : 0 < P.sD c) (hB : 0 < P.sB c) :
    P.sD c * (P.tauB c + P.nLossB N) - P.sB c * (P.tauD c + P.nLossD N) =
      P.s c * P.hQuad N c (P.theta c) := by
  have hD' : P.sD c ≠ 0 := hD.ne'
  have hB' : P.sB c ≠ 0 := hB.ne'
  have hs : P.sD c + P.sB c ≠ 0 := (add_pos hD hB).ne'
  show _ = (P.sD c + P.sB c) *
    ((P.sD c + P.sB c) * (P.tauD c / P.sD c - P.tauB c / P.sB c) *
        (P.sD c / (P.sD c + P.sB c)) ^ 2 +
      (-((P.sD c + P.sB c) * (P.tauD c / P.sD c - P.tauB c / P.sB c)) + P.nLossB N +
        P.nLossD N) * (P.sD c / (P.sD c + P.sB c)) + -P.nLossD N)
  field_simp
  ring

/-- **Proof of Theorem 11, first display** (tex 1689–1691 and 1724–1726):
`η^loss_𝒟 - η^loss_ℬ = 2 s_t h(θ_t) / ((τ^𝒟 + n^loss_𝒟)(τ^ℬ + n^loss_ℬ))`. -/
theorem etaLossD_sub_etaLossB (hD : 0 < P.sD c) (hB : 0 < P.sB c) :
    P.etaLossD N c - P.etaLossB N c =
      2 * (P.s c * P.hQuad N c (P.theta c)) /
        ((P.tauD c + P.nLossD N) * (P.tauB c + P.nLossB N)) := by
  have hdD : P.tauD c + P.nLossD N ≠ 0 := (lossDen_pos_of_mom_pos P N hD).ne'
  have hdB : P.tauB c + P.nLossB N ≠ 0 := (lossDen_pos_of_mom_pos P N hB).ne'
  rw [← P.lossGap_eq_s_mul_hQuad N hD hB]
  show 2 * P.sD c / (P.tauD c + P.nLossD N) - 2 * P.sB c / (P.tauB c + P.nLossB N) = _
  field_simp

/-- `sign(η^loss_𝒟 - η^loss_ℬ) = sign(h(θ_t))`, negative case. -/
theorem etaLossD_lt_etaLossB_iff_hQuad_neg (hD : 0 < P.sD c) (hB : 0 < P.sB c) :
    P.etaLossD N c < P.etaLossB N c ↔ P.hQuad N c (P.theta c) < 0 := by
  rw [← sub_neg, P.etaLossD_sub_etaLossB N hD hB]
  exact (sign_aux (s_pos_of_sD_pos P hD) (mul_pos (lossDen_pos_of_mom_pos P N hD)
    (lossDen_pos_of_mom_pos P N hB))).1

/-- `sign(η^loss_𝒟 - η^loss_ℬ) = sign(h(θ_t))`, positive case. -/
theorem etaLossB_lt_etaLossD_iff_hQuad_pos (hD : 0 < P.sD c) (hB : 0 < P.sB c) :
    P.etaLossB N c < P.etaLossD N c ↔ 0 < P.hQuad N c (P.theta c) := by
  rw [← sub_pos, P.etaLossD_sub_etaLossB N hD hB]
  exact (sign_aux (s_pos_of_sD_pos P hD) (mul_pos (lossDen_pos_of_mom_pos P N hD)
    (lossDen_pos_of_mom_pos P N hB))).2.1

/-- `sign(η^loss_𝒟 - η^loss_ℬ) = sign(h(θ_t))`, zero case. -/
theorem etaLossD_eq_etaLossB_iff_hQuad_eq_zero (hD : 0 < P.sD c) (hB : 0 < P.sB c) :
    P.etaLossD N c = P.etaLossB N c ↔ P.hQuad N c (P.theta c) = 0 := by
  rw [← sub_eq_zero, P.etaLossD_sub_etaLossB N hD hB]
  exact (sign_aux (s_pos_of_sD_pos P hD) (mul_pos (lossDen_pos_of_mom_pos P N hD)
    (lossDen_pos_of_mom_pos P N hB))).2.2

/-- Square-root-free form of the crossover criterion:
`η^loss_𝒟 < η^loss_ℬ ↔ n^loss_ℬ θ_t - n^loss_𝒟 (1 - θ_t) < α_t θ_t (1 - θ_t)`. -/
theorem etaLossD_lt_etaLossB_iff (hD : 0 < P.sD c) (hB : 0 < P.sB c) :
    P.etaLossD N c < P.etaLossB N c ↔
      P.nLossB N * P.theta c - P.nLossD N * (1 - P.theta c) <
        P.alphaT c * P.theta c * (1 - P.theta c) := by
  rw [P.etaLossD_lt_etaLossB_iff_hQuad_neg N hD hB]
  unfold hQuad betaT gammaT
  constructor <;> intro h <;> linarith

/-- **Theorem 11, low-alignment regime**: `θ_t < θ^crit_t ↔ η^loss_𝒟 < η^loss_ℬ`.
Only `s^𝒟 > 0` and `s^ℬ > 0` (i.e. `0 < θ_t < 1`) are needed. -/
theorem theta_lt_thetaCrit_iff (hD : 0 < P.sD c) (hB : 0 < P.sB c) :
    P.theta c < P.thetaCrit N c ↔ P.etaLossD N c < P.etaLossB N c := by
  rw [P.etaLossD_lt_etaLossB_iff_hQuad_neg N hD hB,
    P.hQuad_neg_iff N (P.alphaT_pos hD hB) (theta_pos P hD)]

/-- **Theorem 11, high-alignment regime**: `θ_t > θ^crit_t ↔ η^loss_𝒟 > η^loss_ℬ`.
Only `s^𝒟 > 0` and `s^ℬ > 0` (i.e. `0 < θ_t < 1`) are needed. -/
theorem thetaCrit_lt_theta_iff (hD : 0 < P.sD c) (hB : 0 < P.sB c) :
    P.thetaCrit N c < P.theta c ↔ P.etaLossB N c < P.etaLossD N c := by
  rw [P.etaLossB_lt_etaLossD_iff_hQuad_pos N hD hB,
    P.hQuad_pos_iff N (P.alphaT_pos hD hB) (theta_pos P hD)]

/-- **Theorem 11, the boundary case**: `θ_t = θ^crit_t ↔ η^loss_𝒟 = η^loss_ℬ`. -/
theorem theta_eq_thetaCrit_iff (hD : 0 < P.sD c) (hB : 0 < P.sB c) :
    P.theta c = P.thetaCrit N c ↔ P.etaLossD N c = P.etaLossB N c := by
  rw [P.etaLossD_eq_etaLossB_iff_hQuad_eq_zero N hD hB,
    P.hQuad_eq_zero_iff N (P.alphaT_pos hD hB) (theta_pos P hD)]

/-- **Theorem 11 (Condition Differences on Different Alignment Regime).**
For a state `x_t` with `0 < θ_t < 1` and noise with `n^loss_𝒟 > 0`, `n^loss_ℬ > 0`:

* the quadratic `h(θ) = α_t θ² + β_t θ + γ_t` has a unique root in `(0, 1)`, and this root is
  `θ^crit_t = (-β_t + √(β_t² - 4 α_t γ_t)) / (2 α_t)`;
* `θ_t < θ^crit_t ↔ η^loss_𝒟(x_t) < η^loss_ℬ(x_t)`;
* `θ_t > θ^crit_t ↔ η^loss_𝒟(x_t) > η^loss_ℬ(x_t)`;
* `θ_t = θ^crit_t ↔ η^loss_𝒟(x_t) = η^loss_ℬ(x_t)`.

The threshold `θ^crit_t = P.thetaCrit N c` depends on the state `c` (through `α_t`, i.e. through
`s_t`, `μ^𝒟(3,2)`, `μ^ℬ(3,2)`), not only on the alignment.  The three equivalences hold without
the noise hypotheses (see `Spec.theta_lt_thetaCrit_iff` etc.); these are only needed for
`θ^crit_t ∈ (0, 1)`. -/
theorem loss_crossover (hθ0 : 0 < P.theta c) (hθ1 : P.theta c < 1)
    (hnD : 0 < P.nLossD N) (hnB : 0 < P.nLossB N) :
    (P.thetaCrit N c ∈ Set.Ioo (0 : ℝ) 1 ∧ P.hQuad N c (P.thetaCrit N c) = 0 ∧
        ∀ θ ∈ Set.Ioo (0 : ℝ) 1, P.hQuad N c θ = 0 → θ = P.thetaCrit N c) ∧
      (P.theta c < P.thetaCrit N c ↔ P.etaLossD N c < P.etaLossB N c) ∧
      (P.thetaCrit N c < P.theta c ↔ P.etaLossB N c < P.etaLossD N c) ∧
      (P.theta c = P.thetaCrit N c ↔ P.etaLossD N c = P.etaLossB N c) := by
  obtain ⟨hD, hB⟩ := (theta_mem_Ioo_iff P c).1 ⟨hθ0, hθ1⟩
  have h := P.crossover_critical_root N hD hB hnD hnB
  exact ⟨⟨h.1, h.2.2.2.1, h.2.2.2.2⟩, P.theta_lt_thetaCrit_iff N hD hB,
    P.thetaCrit_lt_theta_iff N hD hB, P.theta_eq_thetaCrit_iff N hD hB⟩

end Thm11

/-! ## Consequence: opposite descent behaviour between the two thresholds (Summary of §5) -/

section Consequence
variable {c : ι → ℝ} {η : ℝ}

/-- **Summary of §5, displayed consequence** (tex 619–626).  For a step size
`η ∈ (η^loss_𝒟, η^loss_ℬ)`, the dominant-projected update *increases* the expected loss while the
bulk-projected update *decreases* it.

Hypotheses made explicit: the two denominators `τ^S + n^loss_S` are positive, so that both
thresholds are well defined (this holds e.g. if `s^𝒟, s^ℬ > 0`, or if `n^loss_𝒟, n^loss_ℬ > 0`). -/
theorem expLossChange_D_pos_B_neg (hdD : 0 < P.tauD c + P.nLossD N)
    (hdB : 0 < P.tauB c + P.nLossB N) (h1 : P.etaLossD N c < η) (h2 : η < P.etaLossB N c) :
    0 < P.expLossChange N P.D η c ∧ P.expLossChange N P.B η c < 0 :=
  ⟨(P.expLossChange_pos_iff N hdD).2 (Or.inr h1),
    (P.expLossChange_neg_iff N hdB).2 ⟨lt_of_le_of_lt (P.etaLoss_nonneg N P.D c) h1, h2⟩⟩

/-- Mirror statement: for `η ∈ (η^loss_ℬ, η^loss_𝒟)`, the bulk-projected update increases the
expected loss while the dominant-projected update decreases it. -/
theorem expLossChange_B_pos_D_neg (hdD : 0 < P.tauD c + P.nLossD N)
    (hdB : 0 < P.tauB c + P.nLossB N) (h1 : P.etaLossB N c < η) (h2 : η < P.etaLossD N c) :
    0 < P.expLossChange N P.B η c ∧ P.expLossChange N P.D η c < 0 :=
  ⟨(P.expLossChange_pos_iff N hdB).2 (Or.inr h1),
    (P.expLossChange_neg_iff N hdD).2 ⟨lt_of_le_of_lt (P.etaLoss_nonneg N P.B c) h1, h2⟩⟩

/-- **Low-alignment regime** (Theorem 11 + Summary of §5): if `0 < θ_t < θ^crit_t` (and
`s^ℬ > 0`), then the window `(η^loss_𝒟, η^loss_ℬ)` is non-empty and for every step size in it
DSGD increases and BSGD decreases the expected loss — the paper's explanation of the observation of
Song et al. -/
theorem low_alignment_descent (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hθ : P.theta c < P.thetaCrit N c) :
    P.etaLossD N c < P.etaLossB N c ∧
      ∀ η, P.etaLossD N c < η → η < P.etaLossB N c →
        0 < P.expLossChange N P.D η c ∧ P.expLossChange N P.B η c < 0 :=
  ⟨(P.theta_lt_thetaCrit_iff N hD hB).1 hθ, fun _ h1 h2 =>
    P.expLossChange_D_pos_B_neg N (lossDen_pos_of_mom_pos P N hD)
      (lossDen_pos_of_mom_pos P N hB) h1 h2⟩

/-- **High-alignment regime**: if `θ^crit_t < θ_t < 1` (and `s^𝒟 > 0`), then the window
`(η^loss_ℬ, η^loss_𝒟)` is non-empty and for every step size in it BSGD increases and DSGD decreases
the expected loss. -/
theorem high_alignment_descent (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hθ : P.thetaCrit N c < P.theta c) :
    P.etaLossB N c < P.etaLossD N c ∧
      ∀ η, P.etaLossB N c < η → η < P.etaLossD N c →
        0 < P.expLossChange N P.B η c ∧ P.expLossChange N P.D η c < 0 :=
  ⟨(P.thetaCrit_lt_theta_iff N hD hB).1 hθ, fun _ h1 h2 =>
    P.expLossChange_B_pos_D_neg N (lossDen_pos_of_mom_pos P N hD)
      (lossDen_pos_of_mom_pos P N hB) h1 h2⟩

/-- A positive step size for which DSGD increases and BSGD decreases the expected loss exists
**iff** the state is in the low-alignment regime `θ_t < θ^crit_t`. -/
theorem exists_D_pos_B_neg_iff (hD : 0 < P.sD c) (hB : 0 < P.sB c) :
    (∃ η, 0 < η ∧ 0 < P.expLossChange N P.D η c ∧ P.expLossChange N P.B η c < 0) ↔
      P.theta c < P.thetaCrit N c := by
  have hdD := lossDen_pos_of_mom_pos P N hD
  have hdB := lossDen_pos_of_mom_pos P N hB
  rw [P.theta_lt_thetaCrit_iff N hD hB]
  constructor
  · rintro ⟨η, hη, h1, h2⟩
    have h3 := (P.expLossChange_pos_iff_of_pos N hdD hη).1 h1
    have h4 := ((P.expLossChange_neg_iff N hdB).1 h2).2
    exact lt_trans h3 h4
  · intro h
    obtain ⟨η, h1, h2⟩ := exists_between h
    exact ⟨η, lt_of_le_of_lt (P.etaLoss_nonneg N P.D c) h1,
      P.expLossChange_D_pos_B_neg N hdD hdB h1 h2⟩

end Consequence

/-! ## State dependence of the critical alignment

`θ_t` is invariant under rescaling of the state (`LossThreshold.theta_smul`), whereas `α_t` scales
quadratically and the noise terms `n^loss_S` do not scale at all.  Hence `θ^crit_t` genuinely
depends on the state (e.g. on the loss level), not only on the alignment. -/

/-- `α_t` scales quadratically with the state. -/
theorem alphaT_smul {t : ℝ} (ht : t ≠ 0) (c : ι → ℝ) :
    P.alphaT (fun i => t * c i) = t ^ 2 * P.alphaT c := by
  unfold alphaT mu s sD sB
  simp only [mom_smul]
  rw [mul_div_mul_left _ _ (pow_ne_zero 2 ht), mul_div_mul_left _ _ (pow_ne_zero 2 ht)]
  ring

/-- **State dependence, made explicit.**  Along the ray `t ↦ t x_t` (on which the alignment
`θ_t` is constant), the ordering of the two loss thresholds is
`η^loss_𝒟(t x) < η^loss_ℬ(t x) ↔ n^loss_ℬ θ - n^loss_𝒟 (1 - θ) < t² α θ (1 - θ)`.
So whenever `θ_t > n^loss_𝒟 / (n^loss_𝒟 + n^loss_ℬ)`, the ordering flips with the scale of the
state: "low-alignment" ordering for large `|t|` (large loss), "high-alignment" ordering for small
`|t|`. -/
theorem etaLossD_lt_etaLossB_smul_iff {c : ι → ℝ} (hD : 0 < P.sD c) (hB : 0 < P.sB c) {t : ℝ}
    (ht : t ≠ 0) :
    P.etaLossD N (fun i => t * c i) < P.etaLossB N (fun i => t * c i) ↔
      P.nLossB N * P.theta c - P.nLossD N * (1 - P.theta c) <
        t ^ 2 * (P.alphaT c * P.theta c * (1 - P.theta c)) := by
  have ht2 : 0 < t ^ 2 := by positivity
  have hD' : 0 < P.sD (fun i => t * c i) := by
    show 0 < P.mom P.D 2 (fun i => t * c i)
    rw [mom_smul]
    exact mul_pos ht2 hD
  have hB' : 0 < P.sB (fun i => t * c i) := by
    show 0 < P.mom P.B 2 (fun i => t * c i)
    rw [mom_smul]
    exact mul_pos ht2 hB
  rw [P.etaLossD_lt_etaLossB_iff N hD' hB', theta_smul P ht, P.alphaT_smul ht]
  constructor <;> intro h <;> linarith

end Spec

/-! ## Concrete instances: non-vacuity, state dependence, and sharpness of the noise hypotheses -/

namespace LossThreshold

/-- The two-direction problem `λ = (2, 1)`, `𝒟 = {0}`, `ℬ = {1}`. -/
def spec2 : Spec (Fin 2) where
  lam := ![2, 1]
  D := {0}
  i1 := 0
  ik := 0
  ik1 := 1
  id := 1
  i1_mem := by simp
  ik_mem := by simp
  ik1_not_mem := by simp
  id_not_mem := by simp
  lam_pos := by intro i; fin_cases i <;> simp
  le_lam1 := by intro i _; fin_cases i <;> simp
  lamk_le := by intro i hi; fin_cases i <;> simp at hi ⊢
  le_lamk1 := by intro i hi; fin_cases i <;> simp at hi ⊢
  lamd_le := by intro i hi; fin_cases i <;> simp at hi ⊢
  gap := by simp

/-- Diagonal noise with per-direction variances `κ² = (a, b)`. -/
def noise2 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : Noise (Fin 2) where
  kap2 := ![a, b]
  smin := min a b
  smax := max a b
  smin_nonneg := le_min ha hb
  smin_le := by intro i; fin_cases i <;> simp
  le_smax := by intro i; fin_cases i <;> simp

theorem spec2_B : spec2.B = {1} := by
  unfold Spec.B
  decide

theorem spec2_mom_D (p : ℕ) (c : Fin 2 → ℝ) : spec2.mom spec2.D p c = 2 ^ p * c 0 ^ 2 := by
  simp [Spec.mom, spec2]

theorem spec2_mom_B (p : ℕ) (c : Fin 2 → ℝ) : spec2.mom spec2.B p c = c 1 ^ 2 := by
  rw [spec2_B]
  simp [Spec.mom, spec2]

theorem spec2_nLossD (N : Noise (Fin 2)) : spec2.nLossD N = 2 * N.kap2 0 := by
  simp [Spec.nLossD, Spec.nLoss, spec2]

theorem spec2_nLossB (N : Noise (Fin 2)) : spec2.nLossB N = N.kap2 1 := by
  unfold Spec.nLossB
  rw [spec2_B]
  simp [Spec.nLoss, spec2]

theorem spec2_sD (c : Fin 2 → ℝ) : spec2.sD c = 4 * c 0 ^ 2 := by
  unfold Spec.sD
  rw [spec2_mom_D]
  norm_num

theorem spec2_sB (c : Fin 2 → ℝ) : spec2.sB c = c 1 ^ 2 := spec2_mom_B 2 c

theorem spec2_theta (c : Fin 2 → ℝ) :
    spec2.theta c = 4 * c 0 ^ 2 / (4 * c 0 ^ 2 + c 1 ^ 2) := by
  unfold Spec.theta Spec.s
  rw [spec2_sD, spec2_sB]

theorem spec2_etaLossD (N : Noise (Fin 2)) (c : Fin 2 → ℝ) :
    spec2.etaLossD N c = 2 * (4 * c 0 ^ 2) / (8 * c 0 ^ 2 + 2 * N.kap2 0) := by
  have h := spec2_nLossD N
  unfold Spec.nLossD at h
  unfold Spec.etaLossD Spec.etaLoss
  rw [spec2_mom_D, spec2_mom_D, h]
  norm_num

theorem spec2_etaLossB (N : Noise (Fin 2)) (c : Fin 2 → ℝ) :
    spec2.etaLossB N c = 2 * c 1 ^ 2 / (c 1 ^ 2 + N.kap2 1) := by
  have h := spec2_nLossB N
  unfold Spec.nLossB at h
  unfold Spec.etaLossB Spec.etaLoss
  rw [spec2_mom_B, spec2_mom_B, h]

theorem spec2_alphaT (c : Fin 2 → ℝ) :
    spec2.alphaT c =
      (4 * c 0 ^ 2 + c 1 ^ 2) * (8 * c 0 ^ 2 / (4 * c 0 ^ 2) - c 1 ^ 2 / c 1 ^ 2) := by
  unfold Spec.alphaT Spec.mu Spec.s
  rw [spec2_sD, spec2_sB, spec2_mom_D, spec2_mom_D, spec2_mom_B, spec2_mom_B]
  norm_num

/-- The noise `κ² = (1, 1)` used in the examples. -/
def noise11 : Noise (Fin 2) := noise2 1 1 zero_le_one zero_le_one

/-- **Non-vacuity of Theorems 10 and 11.**  For `λ = (2, 1)`, `κ² = (1, 1)` and the state
`c = (1, 1)`, all hypotheses of `Spec.loss_crossover` (and hence of every result of this file)
hold. -/
theorem loss_crossover_nonvacuous :
    0 < spec2.theta ![1, 1] ∧ spec2.theta ![1, 1] < 1 ∧
      0 < spec2.nLossD noise11 ∧ 0 < spec2.nLossB noise11 := by
  rw [spec2_theta, spec2_nLossD, spec2_nLossB]
  simp [noise11, noise2]
  norm_num

/-- **A concrete "suspicious" window** (non-vacuity of the Summary consequence).  For `λ = (2, 1)`,
`κ² = (1, 1)` and the state `c = (1, 1)` (alignment `θ = 4/5`), one has
`η^loss_𝒟 = 4/5 < 9/10 < 1 = η^loss_ℬ`, and with the step size `η = 9/10` the dominant-projected
update increases the expected loss while the bulk-projected update decreases it. -/
theorem suspicious_window_example :
    spec2.etaLossD noise11 ![1, 1] < 9 / 10 ∧ 9 / 10 < spec2.etaLossB noise11 ![1, 1] ∧
      0 < spec2.expLossChange noise11 spec2.D (9 / 10) ![1, 1] ∧
      spec2.expLossChange noise11 spec2.B (9 / 10) ![1, 1] < 0 := by
  have hD : 0 < spec2.sD ![1, 1] := by rw [spec2_sD]; simp
  have hB : 0 < spec2.sB ![1, 1] := by rw [spec2_sB]; simp
  have h1 : spec2.etaLossD noise11 ![1, 1] < 9 / 10 := by
    rw [spec2_etaLossD]; simp [noise11, noise2]; norm_num
  have h2 : 9 / 10 < spec2.etaLossB noise11 ![1, 1] := by
    rw [spec2_etaLossB]; simp [noise11, noise2]; norm_num
  exact ⟨h1, h2, spec2.expLossChange_D_pos_B_neg noise11
    (lossDen_pos_of_mom_pos spec2 noise11 hD) (lossDen_pos_of_mom_pos spec2 noise11 hB) h1 h2⟩

/-- **State dependence of `θ^crit_t`.**  For `λ = (2, 1)` and `κ² = (1, 1)`, the states
`c = (1, 1)` and `c' = (1/2, 1/2)` have the *same* alignment `θ = 4/5`, but
`η^loss_𝒟(c) = 4/5 < 1 = η^loss_ℬ(c)` whereas `η^loss_ℬ(c') = 2/5 < 1/2 = η^loss_𝒟(c')`.
Consequently `θ^crit(c') < 4/5 < θ^crit(c)`: the critical alignment of Theorem 11 is a function of
the state, not a universal threshold on `θ_t`. -/
theorem state_dependence_example :
    spec2.theta ![1, 1] = 4 / 5 ∧ spec2.theta ![1 / 2, 1 / 2] = 4 / 5 ∧
      spec2.etaLossD noise11 ![1, 1] < spec2.etaLossB noise11 ![1, 1] ∧
      spec2.etaLossB noise11 ![1 / 2, 1 / 2] < spec2.etaLossD noise11 ![1 / 2, 1 / 2] ∧
      spec2.thetaCrit noise11 ![1 / 2, 1 / 2] < 4 / 5 ∧
      4 / 5 < spec2.thetaCrit noise11 ![1, 1] := by
  have hθ1 : spec2.theta ![1, 1] = 4 / 5 := by
    rw [spec2_theta]; simp; norm_num
  have hθ2 : spec2.theta ![1 / 2, 1 / 2] = 4 / 5 := by
    rw [spec2_theta]; simp; norm_num
  have h1 : spec2.etaLossD noise11 ![1, 1] < spec2.etaLossB noise11 ![1, 1] := by
    rw [spec2_etaLossD, spec2_etaLossB]; simp [noise11, noise2]; norm_num
  have h2 : spec2.etaLossB noise11 ![1 / 2, 1 / 2] <
      spec2.etaLossD noise11 ![1 / 2, 1 / 2] := by
    rw [spec2_etaLossD, spec2_etaLossB]; simp [noise11, noise2]; norm_num
  have hD1 : 0 < spec2.sD ![1, 1] := by rw [spec2_sD]; simp
  have hB1 : 0 < spec2.sB ![1, 1] := by rw [spec2_sB]; simp
  have hD2 : 0 < spec2.sD ![1 / 2, 1 / 2] := by rw [spec2_sD]; simp
  have hB2 : 0 < spec2.sB ![1 / 2, 1 / 2] := by rw [spec2_sB]; simp
  refine ⟨hθ1, hθ2, h1, h2, ?_, ?_⟩
  · rw [← hθ2]
    exact (spec2.thetaCrit_lt_theta_iff _ hD2 hB2).2 h2
  · rw [← hθ1]
    exact (spec2.theta_lt_thetaCrit_iff _ hD1 hB1).2 h1

/-- **The hypothesis `n^loss_𝒟 > 0` cannot be dropped from `θ^crit_t ∈ (0, 1)`.**  For
`λ = (2, 1)`, the state `c = (1, 1)` and the noise `κ² = (0, 5)` (a nonzero positive semidefinite
covariance, `Tr Σ = 5 > 0`, supported on the bulk direction), one has `γ_t = 0` and
`θ^crit_t = 0 ∉ (0, 1)`, contradicting "`γ_t < 0` for all `x_t`" and "`θ^crit_t ∈ (0, 1)`". -/
theorem thetaCrit_eq_zero_example :
    spec2.gammaT (noise2 0 5 le_rfl (by norm_num)) = 0 ∧
      spec2.thetaCrit (noise2 0 5 le_rfl (by norm_num)) ![1, 1] = 0 := by
  have hD : 0 < spec2.sD ![1, 1] := by rw [spec2_sD]; simp
  have hB : 0 < spec2.sB ![1, 1] := by rw [spec2_sB]; simp
  have hnD : spec2.nLossD (noise2 0 5 le_rfl (by norm_num)) = 0 := by
    rw [spec2_nLossD]; simp [noise2]
  have hnB : spec2.nLossB (noise2 0 5 le_rfl (by norm_num)) = 5 := by
    rw [spec2_nLossB]; simp [noise2]
  have hα : spec2.alphaT ![1, 1] = 5 := by
    rw [spec2_alphaT]; simp; norm_num
  refine ⟨by unfold Spec.gammaT; rw [hnD, neg_zero], ?_⟩
  exact spec2.thetaCrit_eq_zero _ (spec2.alphaT_pos hD hB) hnD (by rw [hα, hnB])

/-- **The hypothesis `n^loss_ℬ > 0` cannot be dropped from `θ^crit_t ∈ (0, 1)`.**  For
`λ = (2, 1)`, the state `c = (1, 1)` and the noise `κ² = (1, 0)` (supported on the dominant
direction), one has `h(1) = 0` and `θ^crit_t = 1 ∉ (0, 1)`. -/
theorem thetaCrit_eq_one_example :
    spec2.thetaCrit (noise2 1 0 zero_le_one le_rfl) ![1, 1] = 1 := by
  have hD : 0 < spec2.sD ![1, 1] := by rw [spec2_sD]; simp
  have hB : 0 < spec2.sB ![1, 1] := by rw [spec2_sB]; simp
  have hnB : spec2.nLossB (noise2 1 0 zero_le_one le_rfl) = 0 := by
    rw [spec2_nLossB]; simp [noise2]
  exact spec2.thetaCrit_eq_one _ (spec2.alphaT_pos hD hB) hnB

end LossThreshold

end SuspiciousAlignment
