import Mathlib
import SuspiciousAlignment.Defs

/-!
# One SGD step: the comparison functional and its expectation (Appendix A.2 and A.5)

This file formalizes, at the exact finite-`d` (purely algebraic) level, the one-step analysis of

> Deng et al., *Suspicious Alignment of SGD: A Fine-Grained Step Size Condition Analysis*
> (arXiv:2601.11789v2), Appendix A.2 ("Next step alignment function") and
> Appendix A.5 ("Comparison Lemma").

Contents (paper item → section of this file):

* **A.2, eq. (10)** `θ_{t+1} = 1 / (1 + s^ℬ_{t+1} / s^𝒟_{t+1})` and the pathwise equivalences
  `θ_{t+1} > θ_t ↔ f_t(η) > 0`, `θ_{t+1} < θ_t ↔ f_t(η) < 0` — section *Pathwise facts*.
* **Lemma "Elementwise expectation"** (eqs. (Eat), (Ebt)) — section *Elementwise expectation*.
  The conditional expectation `𝔼[s^S_{t+1} | x_t]` is the finite sum `Spec.EsNext`; we prove its
  expansion in powers of `η`, the pathwise decomposition `s^S_{t+1} = χ + gᵀζ + ζᵀDζ` behind it,
  and (section *Abstract expectation*) that any normalised linear functional under which the noise
  has mean `0` and second moments `κ_i²` maps `s^S_{t+1}` to `EsNext` and `f_t(η)` to `expF`.
* **Lemma "Quadratic form for step size condition"** — section *Quadratic form*:
  `𝔼[f_t(η) | x_t] = p_t η² + q_t η` (`Spec.expF_eq`), the bound
  `q_t ≤ 2 s^ℬ s^𝒟 (λ_{k+1} - λ_k)` (`Spec.qCoef_le`), and the *exact* condition for `q_t < 0`
  (`Spec.qCoef_neg_iff`): the paper's unconditional claim `q_t < 0` fails precisely when
  `θ_t ∈ {0, 1}` (`Spec.exists_theta_eq_one_qCoef_eq_zero`,
  `Spec.exists_theta_eq_zero_qCoef_eq_zero`).
* **Remark after the lemma** (sign of the parabola) — section *Sign of the parabola*.
* **Bridge to the deterministic equivalent** `thetaBarNext` — section *Deterministic equivalent*:
  `thetaBarNext - θ_t = 𝔼[f_t(η) | x_t] / (s_t 𝔼[s_{t+1} | x_t])` (`Spec.thetaBarNext_sub_theta`).
* **Non-vacuity** — the last sections exhibit a concrete two-dimensional instance for each regime
  (`p_t > 0` with `η < η*_t`, `p_t > 0` with `η > η*_t`, `p_t ≤ 0`), a two-point noise realising
  the hypotheses of the abstract-expectation lemmas, and two explicit instances showing that at
  finite `d` the sign of `𝔼[f_t]` does *not* determine the sign of `𝔼[θ_{t+1}] - θ_t`
  (`OneStep.exSpec_expect_fCompare_pos_and_expect_theta_lt`,
  `OneStep.exSpec_expect_fCompare_neg_and_theta_lt_expect_theta`).

## Positivity hypotheses

Every positivity hypothesis is explicit, and each comparison lemma carries only the one it needs:

* the `>` equivalences (`Spec.theta_lt_theta_cNext_iff`, `Spec.theta_lt_thetaBarNext_iff`) assume
  only `s_t > 0` (`x_t ≠ 0`) — this hypothesis is missing in the paper;
* the `<` equivalences (`Spec.theta_cNext_lt_theta_iff`, `Spec.thetaBarNext_lt_theta_iff`) assume
  only `s_{t+1} > 0`, resp. `𝔼[s_{t+1} | x_t] > 0` — the first is the paper's own assumption
  (Remark in A.2), so the paper's `<` equivalence is correct as stated;
* the `=` equivalences and the difference identities (`Spec.theta_cNext_sub_theta`,
  `Spec.thetaBarNext_sub_theta`) need both;
* the implications `f_t > 0 → θ_{t+1} > θ_t`, `f_t < 0 → θ_{t+1} < θ_t`,
  `expF > 0 → θ_t < thetaBarNext`, `expF < 0 → thetaBarNext < θ_t` need none.

For each equivalence a `…_iff_sharp` lemma states *exactly* when it holds (e.g.
`θ_t < θ_{t+1} ↔ 0 < f_t` holds iff `x_t ≠ 0` or `s^𝒟_{t+1} = 0`), and companion lemmas
(`Spec.exists_theta_lt_theta_cNext_and_fCompare_eq_zero`,
`Spec.exists_theta_cNext_lt_theta_and_fCompare_eq_zero`,
`Spec.theta_zero_lt_thetaBarNext_and_expF_eq_zero`,
`Spec.exists_thetaBarNext_lt_theta_and_expF_eq_zero`,
`OneStep.theta_eq_zero_and_one_div_eq_one`) exhibit configurations where the hypothesis fails and
the conclusion with it. None of the equivalences or identities gets its content from Lean's
`x / 0 = 0`.

The totalised functions `θ` (with the paper's convention `θ(0) = 0`), `thetaBarNext` and `etaStar`
(both `0` when their denominator vanishes) are nevertheless used at degenerate points in the
following statements, which hold there as stated: the first equality of eq. (10)
(`Spec.theta_cNext_eq_sum_div_sum`), the facts on `θ` of an arbitrary state (`OneStep.theta_pos_iff`,
`OneStep.theta_eq_zero_iff`, `OneStep.theta_eq_zero_or_eq_one_iff`, …, and therefore
`Spec.qCoef_neg_iff_theta`, `Spec.qCoef_eq_zero_iff_theta`), the one-sided comparison lemmas above
(where "both sides are false" at the degenerate point), the bounds `0 ≤ thetaBarNext ≤ 1`,
`Spec.thetaBarNext_zero`, the rewriting `Spec.etaStar_eq`, and the lemmas about the sign of `η*_t`
when `p_t = 0` (`Spec.etaStar_nonpos_of_pCoef_nonpos`,
`Spec.etaStar_pos_iff_pCoef_pos_and_qCoef_neg`; consequently the hypothesis `0 < η < η*_t` of
`Spec.thetaBarNext_lt_theta_of_lt_etaStar` is empty when `p_t ≤ 0`, where the paper leaves `η*_t`
undefined (`p_t = 0`) or the Remark treats the case separately (`p_t < 0`)).

## Namespaces

Generic helper lemmas (real-variable facts, facts about `mom` and `theta` of an arbitrary state)
live in `SuspiciousAlignment.OneStep` and take the spectrum `P` as an explicit first argument; the
statements that are specific to the one-step analysis are in `SuspiciousAlignment.Spec` (dot
notation on `P`).
-/

set_option linter.unusedSectionVars false

open Finset

namespace SuspiciousAlignment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace OneStep

/-! ### Real-variable helper lemmas -/

/-- If a product of two nonnegative reals is positive, both factors are positive. -/
theorem pos_and_pos_of_mul_pos {a b : ℝ} (h : 0 < a * b) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 < a ∧ 0 < b :=
  ⟨pos_of_mul_pos_left h hb, pos_of_mul_pos_right h ha⟩

/-- `p η² + q η = η (p η + q)`. -/
theorem quad_eq_mul (p q η : ℝ) : p * η ^ 2 + q * η = η * (p * η + q) := by ring

/-- For `p > 0` and `η > 0`: `p η² + q η < 0 ↔ η < -q / p`. -/
theorem quad_neg_iff {p q η : ℝ} (hp : 0 < p) (hη : 0 < η) :
    p * η ^ 2 + q * η < 0 ↔ η < -q / p := by
  rw [quad_eq_mul, lt_div_iff₀ hp]
  constructor
  · intro h
    by_contra hh
    have h2 : 0 ≤ p * η + q := by linarith [not_lt.mp hh]
    have := mul_nonneg hη.le h2
    linarith
  · intro h
    have h2 : p * η + q < 0 := by linarith
    exact mul_neg_of_pos_of_neg hη h2

/-- For `p > 0` and `η > 0`: `0 < p η² + q η ↔ -q / p < η`. -/
theorem quad_pos_iff {p q η : ℝ} (hp : 0 < p) (hη : 0 < η) :
    0 < p * η ^ 2 + q * η ↔ -q / p < η := by
  rw [quad_eq_mul, div_lt_iff₀ hp]
  constructor
  · intro h
    by_contra hh
    have h2 : p * η + q ≤ 0 := by linarith [not_lt.mp hh]
    have := mul_nonpos_of_nonneg_of_nonpos hη.le h2
    linarith
  · intro h
    have h2 : 0 < p * η + q := by linarith
    exact mul_pos hη h2

/-- For `p > 0` and `η > 0`: `p η² + q η = 0 ↔ η = -q / p`. -/
theorem quad_eq_zero_iff {p q η : ℝ} (hp : 0 < p) (hη : 0 < η) :
    p * η ^ 2 + q * η = 0 ↔ η = -q / p := by
  rw [quad_eq_mul, eq_div_iff hp.ne', mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h hη.ne'
    · linarith
  · intro h
    right
    linarith

/-! ### Comparing two ratios `a / (a + b)`

Both the alignment `θ = s^𝒟 / (s^𝒟 + s^ℬ)` and its deterministic equivalent
`thetaBarNext = 𝔼s^𝒟 / (𝔼s^𝒟 + 𝔼s^ℬ)` are ratios `a / (a + b)` of nonnegative reals, with Lean's
convention `0 / 0 = 0` (the paper's `θ(0) = 0`). The lemmas below compare two such ratios through
the cross-difference `b a' - b' a` and say *exactly* when each comparison is valid. -/

/-- `a'/(a'+b') - a/(a+b) = (b a' - b' a) / ((a+b)(a'+b'))` when both denominators are
non-zero. -/
theorem ratio_sub_ratio {a b a' b' : ℝ} (h : a + b ≠ 0) (h' : a' + b' ≠ 0) :
    a' / (a' + b') - a / (a + b) = (b * a' - b' * a) / ((a + b) * (a' + b')) := by
  rw [div_sub_div _ _ h' h, mul_comm (a' + b') (a + b)]
  congr 1
  ring

/-- **Sharp comparison of ratios (`<`)**: for nonnegative reals, the equivalence
`a/(a+b) < a'/(a'+b') ↔ 0 < b a' - b' a` holds *if and only if* `a + b > 0` or `a' = 0`.
(It fails exactly when `a = b = 0 < a'`: then the left ratio is `0/0 = 0 < a'/(a'+b')` although the
cross-difference vanishes. No condition on `a' + b'` is needed: if `a' = b' = 0` both sides are
false.) -/
theorem ratio_lt_ratio_iff_sharp {a b a' b' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : 0 ≤ a')
    (hb' : 0 ≤ b') :
    (a / (a + b) < a' / (a' + b') ↔ 0 < b * a' - b' * a) ↔ (0 < a + b ∨ a' = 0) := by
  rcases (add_nonneg ha hb).eq_or_lt with h | h
  · -- `a = b = 0`: the left ratio is `0` and the cross-difference is `0`
    have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    have hcross : ¬ (0 < b * a' - b' * a) := by
      rw [ha0, hb0]
      simp
    have hratio : a / (a + b) = 0 := by rw [ha0, zero_div]
    constructor
    · intro hiff
      right
      by_contra hne
      have hpos : 0 < a' := lt_of_le_of_ne ha' (Ne.symm hne)
      have hlt : a / (a + b) < a' / (a' + b') := by
        rw [hratio]
        exact div_pos hpos (by linarith)
      exact hcross (hiff.mp hlt)
    · rintro (hpos | ha'0)
      · linarith
      · refine iff_of_false ?_ hcross
        rw [hratio, ha'0, zero_div]
        exact lt_irrefl 0
  · -- `a + b > 0`: the equivalence always holds
    refine iff_of_true ?_ (Or.inl h)
    rcases (add_nonneg ha' hb').eq_or_lt with h' | h'
    · have ha0 : a' = 0 := by linarith
      have hb0 : b' = 0 := by linarith
      refine iff_of_false ?_ ?_
      · rw [ha0, zero_div]
        exact not_lt.mpr (div_nonneg ha h.le)
      · rw [ha0, hb0]
        simp
    · rw [← sub_pos, ratio_sub_ratio h.ne' h'.ne', div_pos_iff_of_pos_right (mul_pos h h')]

/-- **Sharp comparison of ratios (`>`)**: for nonnegative reals, the equivalence
`a'/(a'+b') < a/(a+b) ↔ b a' - b' a < 0` holds *if and only if* `a' + b' > 0` or `a = 0`.
(It fails exactly when `a' = b' = 0 < a`. No condition on `a + b` is needed.) -/
theorem ratio_gt_ratio_iff_sharp {a b a' b' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : 0 ≤ a')
    (hb' : 0 ≤ b') :
    (a' / (a' + b') < a / (a + b) ↔ b * a' - b' * a < 0) ↔ (0 < a' + b' ∨ a = 0) := by
  have hflip : b * a' - b' * a < 0 ↔ 0 < b' * a - b * a' := by
    constructor <;> intro h <;> linarith
  rw [hflip]
  exact ratio_lt_ratio_iff_sharp ha' hb' ha hb

/-- **Sharp comparison of ratios (`=`)**: for nonnegative reals, the equivalence
`a'/(a'+b') = a/(a+b) ↔ b a' - b' a = 0` holds *if and only if* both
(`a + b > 0` or `a' = 0`) and (`a' + b' > 0` or `a = 0`). -/
theorem ratio_eq_ratio_iff_sharp {a b a' b' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : 0 ≤ a')
    (hb' : 0 ≤ b') :
    (a' / (a' + b') = a / (a + b) ↔ b * a' - b' * a = 0) ↔
      ((0 < a + b ∨ a' = 0) ∧ (0 < a' + b' ∨ a = 0)) := by
  rcases (add_nonneg ha hb).eq_or_lt with h | h
  · -- `a = b = 0`
    have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    have hcross : b * a' - b' * a = 0 := by
      rw [ha0, hb0]
      ring
    have hratio : a / (a + b) = 0 := by rw [ha0, zero_div]
    constructor
    · intro hiff
      have h0 : a' / (a' + b') = 0 := (hiff.mpr hcross).trans hratio
      refine ⟨Or.inr ?_, Or.inr ha0⟩
      by_contra hne
      have hpos : 0 < a' := lt_of_le_of_ne ha' (Ne.symm hne)
      have : 0 < a' / (a' + b') := div_pos hpos (by linarith)
      linarith
    · rintro ⟨hpos | ha'0, -⟩
      · linarith
      · refine iff_of_true ?_ hcross
        rw [hratio, ha'0, zero_div]
  · rcases (add_nonneg ha' hb').eq_or_lt with h' | h'
    · -- `a + b > 0`, `a' = b' = 0`
      have ha0 : a' = 0 := by linarith
      have hb0 : b' = 0 := by linarith
      have hcross : b * a' - b' * a = 0 := by
        rw [ha0, hb0]
        ring
      have hratio : a' / (a' + b') = 0 := by rw [ha0, zero_div]
      constructor
      · intro hiff
        have h0 : a / (a + b) = 0 := (hiff.mpr hcross).symm.trans hratio
        refine ⟨Or.inl h, Or.inr ?_⟩
        rcases div_eq_zero_iff.mp h0 with h1 | h1
        · exact h1
        · exact absurd h1 h.ne'
      · rintro ⟨-, hpos | ha0'⟩
        · linarith
        · refine iff_of_true ?_ hcross
          rw [hratio, ha0', zero_div]
    · -- both denominators positive
      refine iff_of_true ?_ ⟨Or.inl h, Or.inl h'⟩
      rw [← sub_eq_zero, ratio_sub_ratio h.ne' h'.ne', div_eq_zero_iff]
      constructor
      · rintro (h0 | h0)
        · exact h0
        · exact absurd h0 (mul_pos h h').ne'
      · exact Or.inl

variable (P : Spec ι)

/-! ### Elementary facts about moments -/

/-- A weighted moment vanishes iff the state vanishes on the block (as `λ_i > 0`). -/
theorem mom_eq_zero_iff (S : Finset ι) (p : ℕ) (c : ι → ℝ) :
    P.mom S p c = 0 ↔ ∀ i ∈ S, c i = 0 := by
  unfold Spec.mom
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => mul_nonneg (pow_nonneg (P.lam_pos i).le _) (sq_nonneg _))]
  refine forall₂_congr fun i _ => ?_
  have hl : P.lam i ^ p ≠ 0 := pow_ne_zero p (P.lam_pos i).ne'
  simp [hl]

/-- A weighted moment is positive iff the state is non-zero somewhere on the block. -/
theorem mom_pos_iff (S : Finset ι) (p : ℕ) (c : ι → ℝ) :
    0 < P.mom S p c ↔ ∃ i ∈ S, c i ≠ 0 := by
  rw [(P.mom_nonneg S p c).lt_iff_ne, ne_comm, Ne, mom_eq_zero_iff]
  push Not
  rfl

/-- If the `p`-th moment on a block vanishes, so does the `q`-th. -/
theorem mom_eq_zero_of_mom_eq_zero {S : Finset ι} {p : ℕ} {c : ι → ℝ} (h : P.mom S p c = 0)
    (q : ℕ) : P.mom S q c = 0 :=
  (mom_eq_zero_iff P S q c).mpr ((mom_eq_zero_iff P S p c).mp h)

/-- If `λ_i ≤ b` on the block `S` then `∑_S λ^{p+j} c² ≤ b^j ∑_S λ^p c²`. -/
theorem mom_add_le {S : Finset ι} {b : ℝ} (hb : ∀ i ∈ S, P.lam i ≤ b) (p j : ℕ) (c : ι → ℝ) :
    P.mom S (p + j) c ≤ b ^ j * P.mom S p c := by
  unfold Spec.mom
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have h1 : P.lam i ^ j ≤ b ^ j := pow_le_pow_left₀ (P.lam_pos i).le (hb i hi) j
  have h2 : 0 ≤ P.lam i ^ p * c i ^ 2 :=
    mul_nonneg (pow_nonneg (P.lam_pos i).le _) (sq_nonneg _)
  calc P.lam i ^ (p + j) * c i ^ 2 = P.lam i ^ j * (P.lam i ^ p * c i ^ 2) := by ring
    _ ≤ b ^ j * (P.lam i ^ p * c i ^ 2) := mul_le_mul_of_nonneg_right h1 h2

/-- If `0 ≤ a ≤ λ_i` on the block `S` then `a^j ∑_S λ^p c² ≤ ∑_S λ^{p+j} c²`. -/
theorem le_mom_add {S : Finset ι} {a : ℝ} (ha : 0 ≤ a) (h : ∀ i ∈ S, a ≤ P.lam i) (p j : ℕ)
    (c : ι → ℝ) : a ^ j * P.mom S p c ≤ P.mom S (p + j) c := by
  unfold Spec.mom
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have h1 : a ^ j ≤ P.lam i ^ j := pow_le_pow_left₀ ha (h i hi) j
  have h2 : 0 ≤ P.lam i ^ p * c i ^ 2 :=
    mul_nonneg (pow_nonneg (P.lam_pos i).le _) (sq_nonneg _)
  calc a ^ j * (P.lam i ^ p * c i ^ 2) ≤ P.lam i ^ j * (P.lam i ^ p * c i ^ 2) :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = P.lam i ^ (p + j) * c i ^ 2 := by ring

/-- `τ^ℬ = ∑_ℬ λ³ c² ≤ λ_{k+1} s^ℬ` (used for the bound on `q_t`). -/
theorem tauB_le (c : ι → ℝ) : P.tauB c ≤ P.lamk1 * P.sB c := by
  have h := mom_add_le P (fun i hi => P.le_lamk1_of_mem_B hi) 2 1 c
  rw [pow_one] at h
  exact h

/-- `λ_d s^ℬ ≤ τ^ℬ`. -/
theorem le_tauB (c : ι → ℝ) : P.lamd * P.sB c ≤ P.tauB c := by
  have h := le_mom_add P P.lamd_pos.le (fun i hi => P.lamd_le_of_mem_B hi) 2 1 c
  rw [pow_one] at h
  exact h

/-- `λ_k s^𝒟 ≤ τ^𝒟 = ∑_𝒟 λ³ c²` (used for the bound on `q_t`). -/
theorem le_tauD (c : ι → ℝ) : P.lamk * P.sD c ≤ P.tauD c := by
  have h := le_mom_add P P.lamk_pos.le (fun i hi => P.lamk_le_of_mem hi) 2 1 c
  rw [pow_one] at h
  exact h

/-- `τ^𝒟 ≤ λ_1 s^𝒟`. -/
theorem tauD_le (c : ι → ℝ) : P.tauD c ≤ P.lam1 * P.sD c := by
  have h := mom_add_le P (fun i hi => P.le_lam1_of_mem hi) 2 1 c
  rw [pow_one] at h
  exact h

/-- `∑_ℬ λ⁴ c² ≤ λ_{k+1}² s^ℬ`. -/
theorem mom_four_B_le (c : ι → ℝ) : P.mom P.B 4 c ≤ P.lamk1 ^ 2 * P.sB c :=
  mom_add_le P (fun _ hi => P.le_lamk1_of_mem_B hi) 2 2 c

/-- `λ_d² s^ℬ ≤ ∑_ℬ λ⁴ c²`. -/
theorem le_mom_four_B (c : ι → ℝ) : P.lamd ^ 2 * P.sB c ≤ P.mom P.B 4 c :=
  le_mom_add P P.lamd_pos.le (fun _ hi => P.lamd_le_of_mem_B hi) 2 2 c

/-- `∑_𝒟 λ⁴ c² ≤ λ_1² s^𝒟`. -/
theorem mom_four_D_le (c : ι → ℝ) : P.mom P.D 4 c ≤ P.lam1 ^ 2 * P.sD c :=
  mom_add_le P (fun _ hi => P.le_lam1_of_mem hi) 2 2 c

/-- `λ_k² s^𝒟 ≤ ∑_𝒟 λ⁴ c²`. -/
theorem le_mom_four_D (c : ι → ℝ) : P.lamk ^ 2 * P.sD c ≤ P.mom P.D 4 c :=
  le_mom_add P P.lamk_pos.le (fun _ hi => P.lamk_le_of_mem hi) 2 2 c

/-! ### Elementary facts about the alignment `θ` of an arbitrary state -/

/-- `θ(c) > 0` iff `s^𝒟(c) > 0`. -/
theorem theta_pos_iff (c : ι → ℝ) : 0 < P.theta c ↔ 0 < P.sD c := by
  constructor
  · intro h
    rcases (P.sD_nonneg c).eq_or_lt with h0 | h0
    · unfold Spec.theta at h
      rw [← h0, zero_div] at h
      exact absurd h (lt_irrefl _)
    · exact h0
  · intro h
    exact div_pos h (by unfold Spec.s; linarith [P.sB_nonneg c])

/-- `θ(c) = 0` iff `s^𝒟(c) = 0`. -/
theorem theta_eq_zero_iff (c : ι → ℝ) : P.theta c = 0 ↔ P.sD c = 0 := by
  constructor
  · intro h
    by_contra h0
    have : 0 < P.theta c :=
      (theta_pos_iff P c).mpr (lt_of_le_of_ne (P.sD_nonneg c) (Ne.symm h0))
    linarith
  · intro h
    unfold Spec.theta
    rw [h, zero_div]

/-- `θ(c) = 1` iff the state is non-zero and lies entirely in the dominant block. -/
theorem theta_eq_one_iff (c : ι → ℝ) : P.theta c = 1 ↔ 0 < P.sD c ∧ P.sB c = 0 := by
  constructor
  · intro h
    have hD : 0 < P.sD c := (theta_pos_iff P c).mp (by rw [h]; exact one_pos)
    have hs : 0 < P.s c := by unfold Spec.s; linarith [P.sB_nonneg c]
    refine ⟨hD, ?_⟩
    unfold Spec.theta at h
    rw [div_eq_one_iff_eq hs.ne'] at h
    unfold Spec.s at h
    linarith
  · rintro ⟨hD, hB⟩
    unfold Spec.theta Spec.s
    rw [hB, add_zero, div_self hD.ne']

/-- `0 < θ(c) < 1` iff both block energies are positive. -/
theorem theta_mem_Ioo_iff (c : ι → ℝ) :
    (0 < P.theta c ∧ P.theta c < 1) ↔ (0 < P.sD c ∧ 0 < P.sB c) := by
  constructor
  · rintro ⟨h0, h1⟩
    have hD := (theta_pos_iff P c).mp h0
    refine ⟨hD, ?_⟩
    rcases (P.sB_nonneg c).eq_or_lt with hB | hB
    · exact absurd ((theta_eq_one_iff P c).mpr ⟨hD, hB.symm⟩) h1.ne
    · exact hB
  · rintro ⟨hD, hB⟩
    refine ⟨(theta_pos_iff P c).mpr hD, ?_⟩
    unfold Spec.theta
    rw [div_lt_one (by unfold Spec.s; linarith)]
    unfold Spec.s
    linarith

/-- `θ(c) ∈ {0, 1}` iff one of the two block energies vanishes. -/
theorem theta_eq_zero_or_eq_one_iff (c : ι → ℝ) :
    (P.theta c = 0 ∨ P.theta c = 1) ↔ (P.sD c = 0 ∨ P.sB c = 0) := by
  constructor
  · rintro (h | h)
    · exact Or.inl ((theta_eq_zero_iff P c).mp h)
    · exact Or.inr ((theta_eq_one_iff P c).mp h).2
  · rintro (h | h)
    · exact Or.inl ((theta_eq_zero_iff P c).mpr h)
    · rcases (P.sD_nonneg c).eq_or_lt with hD | hD
      · exact Or.inl ((theta_eq_zero_iff P c).mpr hD.symm)
      · exact Or.inr ((theta_eq_one_iff P c).mpr ⟨hD, h⟩)

/-- Second equality of paper eq. (10) for an arbitrary state: if `s^𝒟(c) ≠ 0` then
`θ(c) = 1 / (1 + s^ℬ(c) / s^𝒟(c))`. -/
theorem theta_eq_one_div (c : ι → ℝ) (h : P.sD c ≠ 0) :
    P.theta c = 1 / (1 + P.sB c / P.sD c) := by
  have hD : 0 < P.sD c := lt_of_le_of_ne (P.sD_nonneg c) (Ne.symm h)
  have hB := P.sB_nonneg c
  have hs : P.sD c + P.sB c ≠ 0 := by positivity
  unfold Spec.theta Spec.s
  field_simp

/-- The hypothesis `s^𝒟(c) ≠ 0` in `theta_eq_one_div` cannot be dropped: if `s^𝒟(c) = 0` then
`θ(c) = 0`, whereas Lean's `x / 0 = 0` evaluates `1 / (1 + s^ℬ(c) / s^𝒟(c))` to `1`. -/
theorem theta_eq_zero_and_one_div_eq_one (c : ι → ℝ) (h : P.sD c = 0) :
    P.theta c = 0 ∧ 1 / (1 + P.sB c / P.sD c) = 1 := by
  refine ⟨(theta_eq_zero_iff P c).mpr h, ?_⟩
  rw [h, div_zero, add_zero, div_one]

/-- The difference of the alignments of two non-zero states:
`θ(c') - θ(c) = (s^ℬ(c) s^𝒟(c') - s^ℬ(c') s^𝒟(c)) / (s(c) s(c'))`. -/
theorem theta_sub_theta (c c' : ι → ℝ) (hs : P.s c ≠ 0) (hs' : P.s c' ≠ 0) :
    P.theta c' - P.theta c = (P.sB c * P.sD c' - P.sB c' * P.sD c) / (P.s c * P.s c') := by
  unfold Spec.theta
  rw [div_sub_div _ _ hs' hs, mul_comm (P.s c') (P.s c)]
  congr 1
  unfold Spec.s
  ring

/-- **Exact validity of the `>` comparison**: for two arbitrary states, the equivalence
`θ(c) < θ(c') ↔ 0 < s^ℬ(c) s^𝒟(c') - s^ℬ(c') s^𝒟(c)` holds *if and only if* `s(c) > 0` or
`s^𝒟(c') = 0`. It fails exactly when `c = 0` (where `θ(c) = 0` by convention and the
cross-difference vanishes) while `c'` has a dominant component (`θ(c') > 0`). -/
theorem theta_lt_theta_iff_sharp (c c' : ι → ℝ) :
    (P.theta c < P.theta c' ↔ 0 < P.sB c * P.sD c' - P.sB c' * P.sD c) ↔
      (0 < P.s c ∨ P.sD c' = 0) := by
  unfold Spec.theta Spec.s
  exact ratio_lt_ratio_iff_sharp (P.sD_nonneg c) (P.sB_nonneg c) (P.sD_nonneg c')
    (P.sB_nonneg c')

/-- **Exact validity of the `<` comparison**: for two arbitrary states, the equivalence
`θ(c') < θ(c) ↔ s^ℬ(c) s^𝒟(c') - s^ℬ(c') s^𝒟(c) < 0` holds *if and only if* `s(c') > 0` or
`s^𝒟(c) = 0`. It fails exactly when `c' = 0` while `c` has a dominant component. -/
theorem theta_gt_theta_iff_sharp (c c' : ι → ℝ) :
    (P.theta c' < P.theta c ↔ P.sB c * P.sD c' - P.sB c' * P.sD c < 0) ↔
      (0 < P.s c' ∨ P.sD c = 0) := by
  unfold Spec.theta Spec.s
  exact ratio_gt_ratio_iff_sharp (P.sD_nonneg c) (P.sB_nonneg c) (P.sD_nonneg c')
    (P.sB_nonneg c')

/-- **Exact validity of the `=` comparison**: for two arbitrary states, the equivalence
`θ(c') = θ(c) ↔ s^ℬ(c) s^𝒟(c') - s^ℬ(c') s^𝒟(c) = 0` holds *if and only if* both
(`s(c) > 0` or `s^𝒟(c') = 0`) and (`s(c') > 0` or `s^𝒟(c) = 0`). -/
theorem theta_eq_theta_iff_sharp (c c' : ι → ℝ) :
    (P.theta c' = P.theta c ↔ P.sB c * P.sD c' - P.sB c' * P.sD c = 0) ↔
      ((0 < P.s c ∨ P.sD c' = 0) ∧ (0 < P.s c' ∨ P.sD c = 0)) := by
  unfold Spec.theta Spec.s
  exact ratio_eq_ratio_iff_sharp (P.sD_nonneg c) (P.sB_nonneg c) (P.sD_nonneg c')
    (P.sB_nonneg c')

/-- If `c ≠ 0` (`s(c) > 0`; nothing is assumed on `c'`), then `θ(c) < θ(c')` iff the
cross-difference `s^ℬ(c) s^𝒟(c') - s^ℬ(c') s^𝒟(c)` is positive. (If `c' = 0` both sides are
false. The hypothesis is the only positivity assumption needed, see
`theta_lt_theta_iff_sharp`.) -/
theorem theta_lt_theta_iff (c c' : ι → ℝ) (hs : 0 < P.s c) :
    P.theta c < P.theta c' ↔ 0 < P.sB c * P.sD c' - P.sB c' * P.sD c :=
  (theta_lt_theta_iff_sharp P c c').mpr (Or.inl hs)

/-- If `c' ≠ 0` (`s(c') > 0`; nothing is assumed on `c`), then `θ(c') < θ(c)` iff the
cross-difference `s^ℬ(c) s^𝒟(c') - s^ℬ(c') s^𝒟(c)` is negative. (If `c = 0` both sides are
false. The hypothesis is the only positivity assumption needed, see
`theta_gt_theta_iff_sharp`.) -/
theorem theta_gt_theta_iff (c c' : ι → ℝ) (hs' : 0 < P.s c') :
    P.theta c' < P.theta c ↔ P.sB c * P.sD c' - P.sB c' * P.sD c < 0 :=
  (theta_gt_theta_iff_sharp P c c').mpr (Or.inl hs')

/-- For two non-zero states, `θ(c') = θ(c)` iff the cross-difference vanishes. (Here both
positivity hypotheses are needed, see `theta_eq_theta_iff_sharp`.) -/
theorem theta_eq_theta_iff (c c' : ι → ℝ) (hs : 0 < P.s c) (hs' : 0 < P.s c') :
    P.theta c' = P.theta c ↔ P.sB c * P.sD c' - P.sB c' * P.sD c = 0 :=
  (theta_eq_theta_iff_sharp P c c').mpr ⟨Or.inl hs, Or.inl hs'⟩

/-- A positive cross-difference forces `c ≠ 0`, hence `θ(c) < θ(c')`
(no positivity hypothesis needed). -/
theorem theta_lt_theta_of_pos (c c' : ι → ℝ)
    (h : 0 < P.sB c * P.sD c' - P.sB c' * P.sD c) : P.theta c < P.theta c' := by
  have h1 : 0 < P.sB c * P.sD c' := by
    have := mul_nonneg (P.sB_nonneg c') (P.sD_nonneg c)
    linarith
  obtain ⟨hB, -⟩ := pos_and_pos_of_mul_pos h1 (P.sB_nonneg _) (P.sD_nonneg _)
  have hs : 0 < P.s c := by unfold Spec.s; linarith [P.sD_nonneg c]
  exact (theta_lt_theta_iff P c c' hs).mpr h

/-- A negative cross-difference forces `c' ≠ 0`, hence `θ(c') < θ(c)`
(no positivity hypothesis needed). -/
theorem theta_gt_theta_of_neg (c c' : ι → ℝ)
    (h : P.sB c * P.sD c' - P.sB c' * P.sD c < 0) : P.theta c' < P.theta c := by
  have h1 : 0 < P.sB c' * P.sD c := by
    have := mul_nonneg (P.sB_nonneg c) (P.sD_nonneg c')
    linarith
  obtain ⟨hB', -⟩ := pos_and_pos_of_mul_pos h1 (P.sB_nonneg _) (P.sD_nonneg _)
  have hs' : 0 < P.s c' := by unfold Spec.s; linarith [P.sD_nonneg c']
  exact (theta_gt_theta_iff P c c' hs').mpr h

end OneStep

namespace Spec

open OneStep

variable (P : Spec ι) (N : Noise ι)

/-! ### Pathwise facts (Appendix A.2)

Throughout, `c` is the current state `x_t` (in eigen-coordinates), `ζ` the realised noise, and
`P.cNext η c ζ` the next state `x_{t+1}`. -/

/-- The coordinate update of A.2 in its first form:
`c_{i,t+1} = c_{i,t} - η (λ_i c_{i,t} + ζ_{i,t})` (`= (1 - ηλ_i) c_{i,t} - η ζ_{i,t}`, which is the
definition of `cNext`). -/
theorem cNext_eq (η : ℝ) (c ζ : ι → ℝ) (i : ι) :
    P.cNext η c ζ i = c i - η * (P.lam i * c i + ζ i) := by
  unfold cNext
  ring

/-- **Paper eq. (10), first equality**: `θ_{t+1}` written out,
`θ_{t+1} = ∑_{i∈𝒟} λ_i² ((1-ηλ_i)c_i - ηζ_i)² / ∑_{i} λ_i² ((1-ηλ_i)c_i - ηζ_i)²`. -/
theorem theta_cNext_eq_sum_div_sum (η : ℝ) (c ζ : ι → ℝ) :
    P.theta (P.cNext η c ζ) =
      (∑ i ∈ P.D, P.lam i ^ 2 * ((1 - η * P.lam i) * c i - η * ζ i) ^ 2) /
        (∑ i, P.lam i ^ 2 * ((1 - η * P.lam i) * c i - η * ζ i) ^ 2) := by
  unfold theta
  rw [P.s_eq_sum]
  rfl

/-- **Paper eq. (10), second equality**: if `s^𝒟_{t+1} ≠ 0` then
`θ_{t+1} = 1 / (1 + s^ℬ_{t+1} / s^𝒟_{t+1})`. -/
theorem theta_cNext_eq_one_div (η : ℝ) (c ζ : ι → ℝ) (h : P.sD (P.cNext η c ζ) ≠ 0) :
    P.theta (P.cNext η c ζ) = 1 / (1 + P.sB (P.cNext η c ζ) / P.sD (P.cNext η c ζ)) :=
  theta_eq_one_div P _ h

/-- The exceptional set of the Remark in A.2: the next-step block energy `s^S_{t+1}` vanishes iff
the noise satisfies `η ζ_i = (1 - η λ_i) c_i` for every `i ∈ S`
(for `η ≠ 0`: `ζ_i = (1 - η λ_i) c_i / η`, the paper's affine subspace `𝒱`). -/
theorem mom_cNext_eq_zero_iff (S : Finset ι) (p : ℕ) (η : ℝ) (c ζ : ι → ℝ) :
    P.mom S p (P.cNext η c ζ) = 0 ↔ ∀ i ∈ S, η * ζ i = (1 - η * P.lam i) * c i := by
  rw [mom_eq_zero_iff]
  refine forall₂_congr fun i _ => ?_
  unfold cNext
  constructor <;> intro h <;> linarith

/-- `s^𝒟_{t+1} = 0` iff `η ζ_i = (1 - η λ_i) c_i` for every `i ∈ 𝒟` (Remark in A.2). -/
theorem sD_cNext_eq_zero_iff (η : ℝ) (c ζ : ι → ℝ) :
    P.sD (P.cNext η c ζ) = 0 ↔ ∀ i ∈ P.D, η * ζ i = (1 - η * P.lam i) * c i :=
  P.mom_cNext_eq_zero_iff P.D 2 η c ζ

/-- Pathwise one-step change of the alignment:
`θ_{t+1} - θ_t = f_t(η) / (s_t s_{t+1})` whenever `s_t ≠ 0` and `s_{t+1} ≠ 0`. -/
theorem theta_cNext_sub_theta (η : ℝ) (c ζ : ι → ℝ) (hs : P.s c ≠ 0)
    (hs' : P.s (P.cNext η c ζ) ≠ 0) :
    P.theta (P.cNext η c ζ) - P.theta c =
      P.fCompare η c ζ / (P.s c * P.s (P.cNext η c ζ)) :=
  theta_sub_theta P c _ hs hs'

/-- The other exceptional set of the Remark in A.2: `s_{t+1} = 0` (i.e. `x_{t+1} = 0`) iff the
noise satisfies `η ζ_i = (1 - η λ_i) c_i` for **every** `i` — for `η ≠ 0` this is the single point
`ζ = ((1 - η λ_i) c_i / η)_i`. -/
theorem s_cNext_eq_zero_iff (η : ℝ) (c ζ : ι → ℝ) :
    P.s (P.cNext η c ζ) = 0 ↔ ∀ i, η * ζ i = (1 - η * P.lam i) * c i := by
  rw [P.s_eq_zero_iff]
  constructor
  · intro h i
    have := congrFun h i
    simp only [cNext, Pi.zero_apply] at this
    linarith
  · intro h
    funext i
    simp only [cNext, Pi.zero_apply]
    linarith [h i]

/-- `s_{t+1} > 0` (i.e. `x_{t+1} ≠ 0`) iff `η ζ_i ≠ (1 - η λ_i) c_i` for some `i`. -/
theorem s_cNext_pos_iff (η : ℝ) (c ζ : ι → ℝ) :
    0 < P.s (P.cNext η c ζ) ↔ ∃ i, η * ζ i ≠ (1 - η * P.lam i) * c i := by
  rw [(P.s_nonneg _).lt_iff_ne, ne_comm, Ne, P.s_cNext_eq_zero_iff]
  exact not_forall

/-- **Paper A.2 (after eq. (12))**: `θ_{t+1} > θ_t ↔ f_t(η) > 0`, for `x_t ≠ 0` (i.e. `s_t > 0`).
Nothing is assumed on `x_{t+1}`: if `x_{t+1} = 0` both sides are false. The hypothesis `x_t ≠ 0`
is missing in the paper and cannot be dropped (`theta_lt_theta_cNext_iff_sharp`,
`exists_theta_lt_theta_cNext_and_fCompare_eq_zero`). -/
theorem theta_lt_theta_cNext_iff (η : ℝ) (c ζ : ι → ℝ) (hs : 0 < P.s c) :
    P.theta c < P.theta (P.cNext η c ζ) ↔ 0 < P.fCompare η c ζ :=
  theta_lt_theta_iff P c _ hs

/-- **Paper A.2 (after eq. (12))**: `θ_{t+1} < θ_t ↔ f_t(η) < 0`, for `x_{t+1} ≠ 0` (i.e.
`s_{t+1} > 0`), which is the paper's own standing assumption (Remark in A.2: "we can assume
`s_{t+1} ≠ 0`"). Nothing is assumed on `x_t`: if `x_t = 0` both sides are false. The hypothesis
cannot be dropped (`theta_cNext_lt_theta_iff_sharp`,
`exists_theta_cNext_lt_theta_and_fCompare_eq_zero`). -/
theorem theta_cNext_lt_theta_iff (η : ℝ) (c ζ : ι → ℝ) (hs' : 0 < P.s (P.cNext η c ζ)) :
    P.theta (P.cNext η c ζ) < P.theta c ↔ P.fCompare η c ζ < 0 :=
  theta_gt_theta_iff P c _ hs'

/-- `θ_{t+1} = θ_t ↔ f_t(η) = 0`, for `s_t > 0`, `s_{t+1} > 0` (here both hypotheses are needed,
see `theta_cNext_eq_theta_iff_sharp`). -/
theorem theta_cNext_eq_theta_iff (η : ℝ) (c ζ : ι → ℝ) (hs : 0 < P.s c)
    (hs' : 0 < P.s (P.cNext η c ζ)) :
    P.theta (P.cNext η c ζ) = P.theta c ↔ P.fCompare η c ζ = 0 :=
  theta_eq_theta_iff P c _ hs hs'

/-- **Exact validity of the paper's `θ_{t+1} > θ_t ⟺ f_t(η) > 0`**: the equivalence holds *if and
only if* `x_t ≠ 0` or `s^𝒟_{t+1} = 0`. Under the paper's assumption `s^𝒟_{t+1} ≠ 0` it therefore
holds exactly when `x_t ≠ 0`. -/
theorem theta_lt_theta_cNext_iff_sharp (η : ℝ) (c ζ : ι → ℝ) :
    (P.theta c < P.theta (P.cNext η c ζ) ↔ 0 < P.fCompare η c ζ) ↔
      (0 < P.s c ∨ P.sD (P.cNext η c ζ) = 0) :=
  theta_lt_theta_iff_sharp P c _

/-- **Exact validity of the paper's `θ_{t+1} < θ_t ⟺ f_t(η) < 0`**: the equivalence holds *if and
only if* `x_{t+1} ≠ 0` or `s^𝒟_t = 0`. In particular it holds under the paper's assumption
`s_{t+1} ≠ 0`, for every `x_t` (including `x_t = 0`). -/
theorem theta_cNext_lt_theta_iff_sharp (η : ℝ) (c ζ : ι → ℝ) :
    (P.theta (P.cNext η c ζ) < P.theta c ↔ P.fCompare η c ζ < 0) ↔
      (0 < P.s (P.cNext η c ζ) ∨ P.sD c = 0) :=
  theta_gt_theta_iff_sharp P c _

/-- **Exact validity of `θ_{t+1} = θ_t ⟺ f_t(η) = 0`**: the equivalence holds *if and only if*
both (`x_t ≠ 0` or `s^𝒟_{t+1} = 0`) and (`x_{t+1} ≠ 0` or `s^𝒟_t = 0`). -/
theorem theta_cNext_eq_theta_iff_sharp (η : ℝ) (c ζ : ι → ℝ) :
    (P.theta (P.cNext η c ζ) = P.theta c ↔ P.fCompare η c ζ = 0) ↔
      ((0 < P.s c ∨ P.sD (P.cNext η c ζ) = 0) ∧ (0 < P.s (P.cNext η c ζ) ∨ P.sD c = 0)) :=
  theta_eq_theta_iff_sharp P c _

/-- `f_t(η) > 0 → θ_{t+1} > θ_t` holds with no positivity hypothesis. -/
theorem theta_lt_theta_cNext_of_fCompare_pos (η : ℝ) (c ζ : ι → ℝ) (h : 0 < P.fCompare η c ζ) :
    P.theta c < P.theta (P.cNext η c ζ) :=
  theta_lt_theta_of_pos P c _ h

/-- `f_t(η) < 0 → θ_{t+1} < θ_t` holds with no positivity hypothesis. -/
theorem theta_cNext_lt_theta_of_fCompare_neg (η : ℝ) (c ζ : ι → ℝ) (h : P.fCompare η c ζ < 0) :
    P.theta (P.cNext η c ζ) < P.theta c :=
  theta_gt_theta_of_neg P c _ h

/-- The hypothesis `s_t > 0` in `theta_lt_theta_cNext_iff` (and in `theta_cNext_eq_theta_iff`)
cannot be dropped: from `x_t = 0` (where `θ_t = 0` by convention) the alignment can increase
although `f_t(η) = 0` (here `x_{t+1} ≠ 0`, so this is a genuine counterexample to the paper's
`θ_{t+1} > θ_t ⟺ f_t(η) > 0` at `x_t = 0`). -/
theorem exists_theta_lt_theta_cNext_and_fCompare_eq_zero :
    ∃ (η : ℝ) (c ζ : ι → ℝ), P.theta c < P.theta (P.cNext η c ζ) ∧ P.fCompare η c ζ = 0 := by
  refine ⟨1, 0, Pi.single P.i1 1, ?_, ?_⟩
  · rw [P.theta_zero, theta_pos_iff]
    unfold sD
    rw [mom_pos_iff]
    exact ⟨P.i1, P.i1_mem, by simp [cNext]⟩
  · simp [fCompare, sB, sD, mom]

/-- The hypothesis `s_{t+1} > 0` in `theta_cNext_lt_theta_iff` (and in
`theta_cNext_eq_theta_iff`) cannot be dropped: the step `η = 1/λ_1` from a state on the
`λ_1`-eigendirection with zero noise lands on `x_{t+1} = 0`, so `θ_{t+1} = 0 < 1 = θ_t` although
`f_t(η) = 0`. (This configuration is excluded by the paper's assumption `s_{t+1} ≠ 0`, so it is
not an error of the paper.) -/
theorem exists_theta_cNext_lt_theta_and_fCompare_eq_zero :
    ∃ (η : ℝ) (c ζ : ι → ℝ), P.theta (P.cNext η c ζ) < P.theta c ∧ P.fCompare η c ζ = 0 := by
  have hc' : P.cNext (1 / P.lam P.i1) (Pi.single P.i1 1) 0 = 0 := by
    funext i
    by_cases hi : i = P.i1
    · subst hi
      simp [cNext, (P.lam_pos _).ne']
    · simp [cNext, hi]
  refine ⟨1 / P.lam P.i1, Pi.single P.i1 1, 0, ?_, ?_⟩
  · rw [hc', P.theta_zero, theta_pos_iff]
    unfold sD
    rw [mom_pos_iff]
    exact ⟨P.i1, P.i1_mem, by simp⟩
  · rw [fCompare, hc']
    simp [sB, sD, mom]

/-! ### Elementwise expectation (Lemma "Elementwise expectation of `x_{t+1}`") -/

/-- Per-coordinate pathwise expansion used in the proof of the lemma:
`λ_i² c_{i,t+1}² = λ_i² (1-ηλ_i)² c_i² - 2η λ_i² (1-ηλ_i) c_i ζ_i + η² λ_i² ζ_i²`. -/
theorem lam_sq_mul_cNext_sq (η : ℝ) (c ζ : ι → ℝ) (i : ι) :
    P.lam i ^ 2 * P.cNext η c ζ i ^ 2 =
      P.lam i ^ 2 * (1 - η * P.lam i) ^ 2 * c i ^ 2
        - 2 * η * (P.lam i ^ 2 * (1 - η * P.lam i) * c i * ζ i)
        + η ^ 2 * (P.lam i ^ 2 * ζ i ^ 2) := by
  unfold cNext
  ring

/-- Per-coordinate regrouping in powers of `η` (last display in the proof of the lemma):
`λ_i²(1-ηλ_i)²c_i² + η²λ_i²κ_i² = λ_i²c_i² - 2ηλ_i³c_i² + η²(λ_i⁴c_i² + λ_i²κ_i²)`. -/
theorem EsNext_term_eq (η : ℝ) (c : ι → ℝ) (i : ι) :
    P.lam i ^ 2 * (1 - η * P.lam i) ^ 2 * c i ^ 2 + η ^ 2 * P.lam i ^ 2 * N.kap2 i =
      P.lam i ^ 2 * c i ^ 2 - 2 * η * (P.lam i ^ 3 * c i ^ 2)
        + η ^ 2 * (P.lam i ^ 4 * c i ^ 2 + P.lam i ^ 2 * N.kap2 i) := by
  ring

/-- **Lemma "Elementwise expectation", per-coordinate statement**, in algebraic form:
`𝔼[λ_i² c_{i,t+1}² | x_t] = (1-ηλ_i)² λ_i² c_i² + η² λ_i² κ_i²`, where the left-hand side is
`EsNext` of the one-point block `{i}`. -/
theorem EsNext_singleton (η : ℝ) (c : ι → ℝ) (i : ι) :
    P.EsNext N {i} η c =
      (1 - η * P.lam i) ^ 2 * P.lam i ^ 2 * c i ^ 2 + η ^ 2 * P.lam i ^ 2 * N.kap2 i := by
  unfold EsNext
  rw [Finset.sum_singleton]
  ring

/-- `EsNext` of a block is the sum of the per-coordinate expectations. -/
theorem EsNext_eq_sum_singleton (S : Finset ι) (η : ℝ) (c : ι → ℝ) :
    P.EsNext N S η c = ∑ i ∈ S, P.EsNext N {i} η c := by
  unfold EsNext
  exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_singleton]

/-- Pathwise decomposition of the next-step block energy into its constant, linear and quadratic
parts in the noise (`s^S_{t+1} = χ_S + g_Sᵀ ζ + ζᵀ D_S ζ`, proof of Lemma "Asymptotic ratio of
expectations"). -/
theorem mom_two_cNext (S : Finset ι) (η : ℝ) (c ζ : ι → ℝ) :
    P.mom S 2 (P.cNext η c ζ) =
      ∑ i ∈ S, P.lam i ^ 2 * (1 - η * P.lam i) ^ 2 * c i ^ 2
        - 2 * η * ∑ i ∈ S, P.lam i ^ 2 * (1 - η * P.lam i) * c i * ζ i
        + η ^ 2 * ∑ i ∈ S, P.lam i ^ 2 * ζ i ^ 2 := by
  unfold mom
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => P.lam_sq_mul_cNext_sq η c ζ i

/-- **Lemma "Elementwise expectation", block form** (last display of its proof): for every block
`S`, `𝔼[s^S_{t+1} | x_t] = ∑_S λ²c² - 2η ∑_S λ³c² + η² (∑_S λ⁴c² + ∑_S λ²κ²)`. -/
theorem EsNext_eq (S : Finset ι) (η : ℝ) (c : ι → ℝ) :
    P.EsNext N S η c =
      P.mom S 2 c - 2 * η * P.mom S 3 c
        + η ^ 2 * (P.mom S 4 c + ∑ i ∈ S, P.lam i ^ 2 * N.kap2 i) := by
  unfold EsNext mom
  rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => P.EsNext_term_eq N η c i

/-- **Paper eq. (Eat)**:
`𝔼[s^𝒟_{t+1} | x_t] = s^𝒟 - 2η ∑_𝒟 λ³c² + η² (∑_𝒟 λ⁴c² + e_𝒟)`. -/
theorem EsNext_D (η : ℝ) (c : ι → ℝ) :
    P.EsNext N P.D η c = P.sD c - 2 * η * P.tauD c + η ^ 2 * (P.mom P.D 4 c + P.eD N) :=
  P.EsNext_eq N P.D η c

/-- **Paper eq. (Ebt)**:
`𝔼[s^ℬ_{t+1} | x_t] = s^ℬ - 2η ∑_ℬ λ³c² + η² (∑_ℬ λ⁴c² + e_ℬ)`. -/
theorem EsNext_B (η : ℝ) (c : ι → ℝ) :
    P.EsNext N P.B η c = P.sB c - 2 * η * P.tauB c + η ^ 2 * (P.mom P.B 4 c + P.eB N) :=
  P.EsNext_eq N P.B η c

/-- At `η = 0` nothing moves: `𝔼[s^S_{t+1} | x_t] = s^S_t`. -/
theorem EsNext_zero (S : Finset ι) (c : ι → ℝ) : P.EsNext N S 0 c = P.mom S 2 c := by
  rw [P.EsNext_eq]
  ring

/-- Pathwise deviation of the next-step block energy from its conditional expectation:
`s^S_{t+1} - 𝔼[s^S_{t+1} | x_t] = -2η ∑_S λ²(1-ηλ) c ζ + η² ∑_S λ² (ζ² - κ²)`.
Taking expectations with `𝔼 ζ_i = 0`, `𝔼 ζ_i² = κ_i²` kills the right-hand side. -/
theorem mom_two_cNext_sub_EsNext (S : Finset ι) (η : ℝ) (c ζ : ι → ℝ) :
    P.mom S 2 (P.cNext η c ζ) - P.EsNext N S η c =
      -(2 * η) * ∑ i ∈ S, P.lam i ^ 2 * (1 - η * P.lam i) * c i * ζ i
        + η ^ 2 * ∑ i ∈ S, P.lam i ^ 2 * (ζ i ^ 2 - N.kap2 i) := by
  rw [P.mom_two_cNext]
  unfold EsNext
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `𝔼[s^S_{t+1} | x_t] ≥ 0` for every block. -/
theorem EsNext_nonneg (S : Finset ι) (η : ℝ) (c : ι → ℝ) : 0 ≤ P.EsNext N S η c :=
  Finset.sum_nonneg fun i _ =>
    add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))
      (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (kap2_nonneg N i))

/-- `𝔼[s^S_{t+1} | x_t] = 0` iff, for every `i ∈ S`, the deterministic part `(1-ηλ_i) c_i` and the
noise part `η κ_i²` both vanish. -/
theorem EsNext_eq_zero_iff (S : Finset ι) (η : ℝ) (c : ι → ℝ) :
    P.EsNext N S η c = 0 ↔ ∀ i ∈ S, (1 - η * P.lam i) * c i = 0 ∧ η * N.kap2 i = 0 := by
  unfold EsNext
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
    add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))
      (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (kap2_nonneg N i)))]
  refine forall₂_congr fun i _ => ?_
  have hl : P.lam i ≠ 0 := (P.lam_pos i).ne'
  have h1 : 0 ≤ P.lam i ^ 2 * (1 - η * P.lam i) ^ 2 * c i ^ 2 :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  have h2 : 0 ≤ η ^ 2 * P.lam i ^ 2 * N.kap2 i :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (kap2_nonneg N i)
  rw [add_eq_zero_iff_of_nonneg h1 h2]
  simp [hl, mul_eq_zero]

/-- `𝔼[s^S_{t+1} | x_t] > 0` iff some coordinate of `S` has a non-zero deterministic part
`(1-ηλ_i) c_i` or a non-zero noise part `η κ_i²`. -/
theorem EsNext_pos_iff (S : Finset ι) (η : ℝ) (c : ι → ℝ) :
    0 < P.EsNext N S η c ↔ ∃ i ∈ S, (1 - η * P.lam i) * c i ≠ 0 ∨ η * N.kap2 i ≠ 0 := by
  rw [(P.EsNext_nonneg N S η c).lt_iff_ne, ne_comm, Ne, P.EsNext_eq_zero_iff]
  push Not
  refine exists_congr fun i => and_congr_right fun _ => ?_
  tauto

/-- Noise in one direction of `S` makes `𝔼[s^S_{t+1} | x_t]` positive (for `η ≠ 0`). -/
theorem EsNext_pos_of_kap2_pos {S : Finset ι} {i : ι} (hi : i ∈ S) {η : ℝ} (hη : η ≠ 0)
    (hk : 0 < N.kap2 i) (c : ι → ℝ) : 0 < P.EsNext N S η c :=
  (P.EsNext_pos_iff N S η c).mpr ⟨i, hi, Or.inr (mul_ne_zero hη hk.ne')⟩

/-- Non-degenerate noise (`s_min > 0`) makes `𝔼[s^S_{t+1} | x_t]` positive on every non-empty
block (for `η ≠ 0`). -/
theorem EsNext_pos_of_smin_pos {S : Finset ι} (hS : S.Nonempty) {η : ℝ} (hη : η ≠ 0)
    (hs : 0 < N.smin) (c : ι → ℝ) : 0 < P.EsNext N S η c := by
  obtain ⟨i, hi⟩ := hS
  exact P.EsNext_pos_of_kap2_pos N hi hη (lt_of_lt_of_le hs (N.smin_le i)) c

/-- A non-zero coordinate `c_i`, `i ∈ S`, with `η λ_i ≠ 1` makes `𝔼[s^S_{t+1} | x_t]` positive. -/
theorem EsNext_pos_of_state {S : Finset ι} {i : ι} (hi : i ∈ S) {η : ℝ} {c : ι → ℝ}
    (hc : c i ≠ 0) (hη : η * P.lam i ≠ 1) : 0 < P.EsNext N S η c :=
  (P.EsNext_pos_iff N S η c).mpr
    ⟨i, hi, Or.inl (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hη)) hc)⟩

/-- `𝔼[s_{t+1} | x_t] = 𝔼[s^𝒟_{t+1} | x_t] + 𝔼[s^ℬ_{t+1} | x_t]` is `EsNext` of the full index
set. -/
theorem EsNext_D_add_EsNext_B (η : ℝ) (c : ι → ℝ) :
    P.EsNext N P.D η c + P.EsNext N P.B η c = P.EsNext N Finset.univ η c :=
  P.sum_D_add_sum_B _

/-- Exact condition for `𝔼[s_{t+1} | x_t] > 0` (the denominator of `thetaBarNext`). -/
theorem EsNext_D_add_EsNext_B_pos_iff (η : ℝ) (c : ι → ℝ) :
    0 < P.EsNext N P.D η c + P.EsNext N P.B η c ↔
      ∃ i, (1 - η * P.lam i) * c i ≠ 0 ∨ η * N.kap2 i ≠ 0 := by
  rw [P.EsNext_D_add_EsNext_B, P.EsNext_pos_iff]
  simp

/-- `𝔼[s_{t+1} | x_t] > 0` for `η ≠ 0` under non-degenerate noise (`s_min > 0`). -/
theorem EsNext_D_add_EsNext_B_pos_of_smin_pos {η : ℝ} (hη : η ≠ 0) (hs : 0 < N.smin)
    (c : ι → ℝ) : 0 < P.EsNext N P.D η c + P.EsNext N P.B η c :=
  add_pos (P.EsNext_pos_of_smin_pos N P.D_nonempty hη hs c)
    (P.EsNext_pos_of_smin_pos N P.B_nonempty hη hs c)

/-! ### Quadratic form (Lemma "Quadratic form for step size condition") -/

/-- `𝔼[f_t(η) | x_t] = s^ℬ_t 𝔼[s^𝒟_{t+1} | x_t] - 𝔼[s^ℬ_{t+1} | x_t] s^𝒟_t`: the conditional
expectation of the comparison functional `fCompare` (first line of the proof of the lemma;
`expect_fCompare` below justifies the name for any abstract expectation). -/
def expF (η : ℝ) (c : ι → ℝ) : ℝ :=
  P.sB c * P.EsNext N P.D η c - P.EsNext N P.B η c * P.sD c

/-- Pathwise deviation of the comparison functional from its conditional expectation, in terms of
the deviations of the two block energies. -/
theorem fCompare_sub_expF (η : ℝ) (c ζ : ι → ℝ) :
    P.fCompare η c ζ - P.expF N η c =
      P.sB c * (P.sD (P.cNext η c ζ) - P.EsNext N P.D η c)
        - (P.sB (P.cNext η c ζ) - P.EsNext N P.B η c) * P.sD c := by
  unfold fCompare expF
  ring

/-- **Lemma "Quadratic form", eq. (quad-form)**: `𝔼[f_t(η) | x_t] = p_t η² + q_t η`. -/
theorem expF_eq (η : ℝ) (c : ι → ℝ) :
    P.expF N η c = P.pCoef N c * η ^ 2 + P.qCoef c * η := by
  unfold expF pCoef qCoef
  rw [P.EsNext_D, P.EsNext_B]
  ring

/-- `𝔼[f_t(η) | x_t] = η (p_t η + q_t)`. -/
theorem expF_eq_mul (η : ℝ) (c : ι → ℝ) :
    P.expF N η c = η * (P.pCoef N c * η + P.qCoef c) := by
  rw [P.expF_eq, quad_eq_mul]

/-- The parabola passes through the origin: `𝔼[f_t(0) | x_t] = 0` (Remark after the lemma). -/
@[simp] theorem expF_zero (c : ι → ℝ) : P.expF N 0 c = 0 := by
  rw [P.expF_eq]
  ring

/-- **Lemma "Quadratic form", eq. (q-sign), first inequality**:
`q_t ≤ 2 s^ℬ s^𝒟 (λ_{k+1} - λ_k)`. -/
theorem qCoef_le (c : ι → ℝ) : P.qCoef c ≤ 2 * P.sB c * P.sD c * (P.lamk1 - P.lamk) := by
  have h1 := mul_le_mul_of_nonneg_left (tauB_le P c) (P.sD_nonneg c)
  have h2 := mul_le_mul_of_nonneg_left (le_tauD P c) (P.sB_nonneg c)
  unfold qCoef
  linarith

/-- `q_t ≤ 0` always. -/
theorem qCoef_nonpos (c : ι → ℝ) : P.qCoef c ≤ 0 :=
  le_trans (P.qCoef_le c)
    (mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (mul_nonneg (by norm_num) (P.sB_nonneg c)) (P.sD_nonneg c))
      (sub_nonpos.mpr P.lamk1_lt_lamk.le))

/-- **Lemma "Quadratic form", eq. (q-sign), strict inequality**: `q_t < 0` when both block
energies are positive. -/
theorem qCoef_neg {c : ι → ℝ} (hD : 0 < P.sD c) (hB : 0 < P.sB c) : P.qCoef c < 0 :=
  lt_of_le_of_lt (P.qCoef_le c)
    (mul_neg_of_pos_of_neg (mul_pos (mul_pos (by norm_num) hB) hD)
      (sub_neg.mpr P.lamk1_lt_lamk))

/-- If `s^𝒟 = 0` (i.e. `θ_t = 0`) then `q_t = 0`. -/
theorem qCoef_eq_zero_of_sD_eq_zero {c : ι → ℝ} (h : P.sD c = 0) : P.qCoef c = 0 := by
  have hτ : P.tauD c = 0 := mom_eq_zero_of_mom_eq_zero P h 3
  unfold qCoef
  rw [h, hτ]
  ring

/-- If `s^ℬ = 0` (e.g. `θ_t = 1`) then `q_t = 0`. -/
theorem qCoef_eq_zero_of_sB_eq_zero {c : ι → ℝ} (h : P.sB c = 0) : P.qCoef c = 0 := by
  have hτ : P.tauB c = 0 := mom_eq_zero_of_mom_eq_zero P h 3
  unfold qCoef
  rw [h, hτ]
  ring

/-- **Exact strictness condition for eq. (q-sign)**: `q_t < 0` iff both block energies are
positive. -/
theorem qCoef_neg_iff (c : ι → ℝ) : P.qCoef c < 0 ↔ 0 < P.sD c ∧ 0 < P.sB c := by
  constructor
  · intro h
    constructor
    · rcases (P.sD_nonneg c).eq_or_lt with h0 | h0
      · exact absurd (P.qCoef_eq_zero_of_sD_eq_zero h0.symm) h.ne
      · exact h0
    · rcases (P.sB_nonneg c).eq_or_lt with h0 | h0
      · exact absurd (P.qCoef_eq_zero_of_sB_eq_zero h0.symm) h.ne
      · exact h0
  · rintro ⟨hD, hB⟩
    exact P.qCoef_neg hD hB

/-- **Exact strictness condition for eq. (q-sign)** in terms of the alignment:
`q_t < 0` iff `0 < θ_t < 1`. -/
theorem qCoef_neg_iff_theta (c : ι → ℝ) : P.qCoef c < 0 ↔ 0 < P.theta c ∧ P.theta c < 1 :=
  (P.qCoef_neg_iff c).trans (theta_mem_Ioo_iff P c).symm

/-- `q_t = 0` iff one of the block energies vanishes. -/
theorem qCoef_eq_zero_iff (c : ι → ℝ) : P.qCoef c = 0 ↔ P.sD c = 0 ∨ P.sB c = 0 := by
  constructor
  · intro h
    by_contra hne
    rw [not_or] at hne
    have hD : 0 < P.sD c := lt_of_le_of_ne (P.sD_nonneg c) (Ne.symm hne.1)
    have hB : 0 < P.sB c := lt_of_le_of_ne (P.sB_nonneg c) (Ne.symm hne.2)
    exact absurd h (P.qCoef_neg hD hB).ne
  · rintro (h | h)
    · exact P.qCoef_eq_zero_of_sD_eq_zero h
    · exact P.qCoef_eq_zero_of_sB_eq_zero h

/-- `q_t = 0` iff `θ_t ∈ {0, 1}` (this includes `x_t = 0`, where `θ_t = 0` by convention). -/
theorem qCoef_eq_zero_iff_theta (c : ι → ℝ) :
    P.qCoef c = 0 ↔ P.theta c = 0 ∨ P.theta c = 1 :=
  (P.qCoef_eq_zero_iff c).trans (theta_eq_zero_or_eq_one_iff P c).symm

/-- **Counterexample to the unconditional claim `q_t < 0` of eq. (q-sign)**: for every spectrum
there is a non-zero state with `θ_t = 1` and `q_t = 0` (the unit vector along `u_1`). -/
theorem exists_theta_eq_one_qCoef_eq_zero :
    ∃ c : ι → ℝ, c ≠ 0 ∧ P.theta c = 1 ∧ P.qCoef c = 0 := by
  have hB : P.sB (Pi.single P.i1 1) = 0 := by
    unfold sB
    rw [mom_eq_zero_iff]
    intro i hi
    have hne : i ≠ P.i1 := fun h => (P.mem_B.mp hi) (h ▸ P.i1_mem)
    simp [hne]
  have hD : 0 < P.sD (Pi.single P.i1 1) := by
    unfold sD
    rw [mom_pos_iff]
    exact ⟨P.i1, P.i1_mem, by simp⟩
  refine ⟨Pi.single P.i1 1, ?_, (theta_eq_one_iff P _).mpr ⟨hD, hB⟩,
    P.qCoef_eq_zero_of_sB_eq_zero hB⟩
  intro h
  have := congrFun h P.i1
  simp at this

/-- **Counterexample to the unconditional claim `q_t < 0` of eq. (q-sign)**: for every spectrum
there is a non-zero state with `θ_t = 0` and `q_t = 0` (the unit vector along `u_{k+1}`). -/
theorem exists_theta_eq_zero_qCoef_eq_zero :
    ∃ c : ι → ℝ, c ≠ 0 ∧ P.theta c = 0 ∧ P.qCoef c = 0 := by
  have hD : P.sD (Pi.single P.ik1 1) = 0 := by
    unfold sD
    rw [mom_eq_zero_iff]
    intro i hi
    have hne : i ≠ P.ik1 := fun h => P.ik1_not_mem (h ▸ hi)
    simp [hne]
  refine ⟨Pi.single P.ik1 1, ?_, (theta_eq_zero_iff P _).mpr hD,
    P.qCoef_eq_zero_of_sD_eq_zero hD⟩
  intro h
  have := congrFun h P.ik1
  simp at this

/-- If `s^𝒟 = 0` (`θ_t = 0`) then `p_t = s^ℬ e_𝒟 ≥ 0`. -/
theorem pCoef_of_sD_eq_zero {c : ι → ℝ} (h : P.sD c = 0) : P.pCoef N c = P.sB c * P.eD N := by
  have h4 : P.mom P.D 4 c = 0 := mom_eq_zero_of_mom_eq_zero P h 4
  unfold pCoef
  rw [h, h4]
  ring

/-- If `s^ℬ = 0` (e.g. `θ_t = 1`) then `p_t = -s^𝒟 e_ℬ ≤ 0`. -/
theorem pCoef_of_sB_eq_zero {c : ι → ℝ} (h : P.sB c = 0) :
    P.pCoef N c = -(P.sD c * P.eB N) := by
  have h4 : P.mom P.B 4 c = 0 := mom_eq_zero_of_mom_eq_zero P h 4
  unfold pCoef
  rw [h, h4]
  ring

/-! ### Sign of the parabola (Remark after Lemma "Quadratic form")

`η ↦ 𝔼[f_t(η) | x_t] = p_t η² + q_t η` for `η > 0`, with `η*_t = -q_t / p_t = P.etaStar N c`. -/

/-- For `η > 0` the sign of `𝔼[f_t(η) | x_t]` is the sign of the linear factor `p_t η + q_t`
(negative case; division-free form of the Remark). -/
theorem expF_neg_iff_linear (η : ℝ) (c : ι → ℝ) (hη : 0 < η) :
    P.expF N η c < 0 ↔ P.pCoef N c * η + P.qCoef c < 0 := by
  rw [P.expF_eq_mul]
  constructor
  · intro h
    by_contra hh
    exact absurd (mul_nonneg hη.le (not_lt.mp hh)) (not_le.mpr h)
  · exact mul_neg_of_pos_of_neg hη

/-- For `η > 0` the sign of `𝔼[f_t(η) | x_t]` is the sign of the linear factor `p_t η + q_t`
(positive case; division-free form of the Remark). -/
theorem expF_pos_iff_linear (η : ℝ) (c : ι → ℝ) (hη : 0 < η) :
    0 < P.expF N η c ↔ 0 < P.pCoef N c * η + P.qCoef c := by
  rw [P.expF_eq_mul]
  exact mul_pos_iff_of_pos_left hη

/-- The critical step size written out as in the main text, eq. (2):
`η*_t = 2 (s^ℬ τ^𝒟 - s^𝒟 τ^ℬ) / (s^ℬ (∑_𝒟 λ⁴c² + e_𝒟) - s^𝒟 (∑_ℬ λ⁴c² + e_ℬ))`. -/
theorem etaStar_eq (c : ι → ℝ) :
    P.etaStar N c =
      2 * (P.sB c * P.tauD c - P.sD c * P.tauB c) /
        (P.sB c * (P.mom P.D 4 c + P.eD N) - P.sD c * (P.mom P.B 4 c + P.eB N)) := by
  unfold etaStar qCoef pCoef
  congr 1
  ring

/-- `η*_t` is a root of the parabola when `p_t ≠ 0`. -/
theorem expF_etaStar (c : ι → ℝ) (hp : P.pCoef N c ≠ 0) : P.expF N (P.etaStar N c) c = 0 := by
  rw [P.expF_eq_mul]
  unfold etaStar
  field_simp
  ring

/-- For `p_t ≠ 0` the roots of the parabola are exactly `0` and `η*_t`. -/
theorem expF_eq_zero_iff (η : ℝ) (c : ι → ℝ) (hp : P.pCoef N c ≠ 0) :
    P.expF N η c = 0 ↔ η = 0 ∨ η = P.etaStar N c := by
  rw [P.expF_eq_mul, mul_eq_zero]
  unfold etaStar
  rw [eq_div_iff hp]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right; linarith
  · rintro (h | h)
    · exact Or.inl h
    · right; linarith

/-- The paper calls `η*_t` "the non-zero root" of the parabola. For `p_t ≠ 0` it is non-zero
exactly when `q_t ≠ 0`, i.e. when `0 < θ_t < 1`; for `θ_t ∈ {0, 1}` it coincides with the root
`0`. -/
theorem etaStar_eq_zero_iff (c : ι → ℝ) (hp : P.pCoef N c ≠ 0) :
    P.etaStar N c = 0 ↔ P.qCoef c = 0 := by
  unfold etaStar
  rw [div_eq_zero_iff, neg_eq_zero]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h hp
  · exact Or.inl

/-- `η*_t ≥ 0` when `p_t > 0` (because `q_t ≤ 0`). -/
theorem etaStar_nonneg (c : ι → ℝ) (hp : 0 < P.pCoef N c) : 0 ≤ P.etaStar N c :=
  div_nonneg (neg_nonneg.mpr (P.qCoef_nonpos c)) hp.le

/-- **Remark, case `p_t > 0`**: "since `q_t < 0`, there exists a positive critical step size
`η*_t = -q_t / p_t > 0`". -/
theorem etaStar_pos (c : ι → ℝ) (hp : 0 < P.pCoef N c) (hq : P.qCoef c < 0) :
    0 < P.etaStar N c :=
  div_pos (neg_pos.mpr hq) hp

/-- For `p_t > 0`, the critical step size is positive iff `q_t < 0`, i.e. iff both block energies
are positive (`0 < θ_t < 1`). -/
theorem etaStar_pos_iff (c : ι → ℝ) (hp : 0 < P.pCoef N c) :
    0 < P.etaStar N c ↔ 0 < P.sD c ∧ 0 < P.sB c := by
  rw [← P.qCoef_neg_iff]
  unfold etaStar
  rw [div_pos_iff_of_pos_right hp, neg_pos]

/-- `η*_t ≤ 0` when `p_t ≤ 0`: for `p_t < 0` because `q_t ≤ 0`, and for `p_t = 0` because the
totalised `η*_t = -q_t / 0` is `0` in Lean (the paper leaves `η*_t` undefined there). -/
theorem etaStar_nonpos_of_pCoef_nonpos (c : ι → ℝ) (hp : P.pCoef N c ≤ 0) :
    P.etaStar N c ≤ 0 :=
  div_nonpos_of_nonneg_of_nonpos (neg_nonneg.mpr (P.qCoef_nonpos c)) hp

/-- **Unconditional characterisation of a positive critical step size**:
`η*_t > 0 ↔ p_t > 0 ∧ q_t < 0`. -/
theorem etaStar_pos_iff_pCoef_pos_and_qCoef_neg (c : ι → ℝ) :
    0 < P.etaStar N c ↔ 0 < P.pCoef N c ∧ P.qCoef c < 0 := by
  constructor
  · intro h
    have hp : 0 < P.pCoef N c := by
      by_contra hp
      exact absurd h (not_lt.mpr (P.etaStar_nonpos_of_pCoef_nonpos N c (not_lt.mp hp)))
    refine ⟨hp, ?_⟩
    unfold etaStar at h
    rwa [div_pos_iff_of_pos_right hp, neg_pos] at h
  · rintro ⟨hp, hq⟩
    exact P.etaStar_pos N c hp hq

/-- `η*_t > 0 ↔ p_t > 0 ∧ 0 < θ_t < 1` (unconditional). -/
theorem etaStar_pos_iff_pCoef_pos_and_theta (c : ι → ℝ) :
    0 < P.etaStar N c ↔ 0 < P.pCoef N c ∧ 0 < P.theta c ∧ P.theta c < 1 := by
  rw [P.etaStar_pos_iff_pCoef_pos_and_qCoef_neg, P.qCoef_neg_iff_theta]

/-- **Remark, case `p_t > 0`, small steps**: for `η > 0`,
`𝔼[f_t(η) | x_t] < 0 ↔ η < η*_t`. -/
theorem expF_neg_iff_lt_etaStar (η : ℝ) (c : ι → ℝ) (hp : 0 < P.pCoef N c) (hη : 0 < η) :
    P.expF N η c < 0 ↔ η < P.etaStar N c := by
  rw [P.expF_eq]
  exact quad_neg_iff hp hη

/-- For `η > 0`: `η < η*_t ↔ p_t > 0 ∧ 𝔼[f_t(η) | x_t] < 0` (no assumption on `p_t`: a step size
`0 < η < η*_t` exists only when `p_t > 0`). -/
theorem lt_etaStar_iff (η : ℝ) (c : ι → ℝ) (hη : 0 < η) :
    η < P.etaStar N c ↔ 0 < P.pCoef N c ∧ P.expF N η c < 0 := by
  constructor
  · intro h
    have hp := ((P.etaStar_pos_iff_pCoef_pos_and_qCoef_neg N c).mp (hη.trans h)).1
    exact ⟨hp, (P.expF_neg_iff_lt_etaStar N η c hp hη).mpr h⟩
  · rintro ⟨hp, h⟩
    exact (P.expF_neg_iff_lt_etaStar N η c hp hη).mp h

/-- **Remark, small steps, with the hypotheses of Theorem 2 only**: if `0 < η < η*_t` then
`𝔼[f_t(η) | x_t] < 0`. No assumption on `p_t` is needed: `0 < η*_t` forces `p_t > 0` and
`q_t < 0` (`etaStar_pos_iff_pCoef_pos_and_qCoef_neg`). -/
theorem expF_neg_of_lt_etaStar (η : ℝ) (c : ι → ℝ) (hη : 0 < η) (h : η < P.etaStar N c) :
    P.expF N η c < 0 :=
  ((P.lt_etaStar_iff N η c hη).mp h).2

/-- **Remark, case `p_t > 0`, critical step**: for `η > 0`,
`𝔼[f_t(η) | x_t] = 0 ↔ η = η*_t`. -/
theorem expF_eq_zero_iff_eq_etaStar (η : ℝ) (c : ι → ℝ) (hp : 0 < P.pCoef N c) (hη : 0 < η) :
    P.expF N η c = 0 ↔ η = P.etaStar N c := by
  rw [P.expF_eq]
  exact quad_eq_zero_iff hp hη

/-- **Remark, case `p_t > 0`, large steps**: for `η > 0`,
`𝔼[f_t(η) | x_t] > 0 ↔ η > η*_t`. -/
theorem expF_pos_iff_etaStar_lt (η : ℝ) (c : ι → ℝ) (hp : 0 < P.pCoef N c) (hη : 0 < η) :
    0 < P.expF N η c ↔ P.etaStar N c < η := by
  rw [P.expF_eq]
  exact quad_pos_iff hp hη

/-- **Remark, case `p_t ≤ 0`** (the paper's Figure (b) is `p_t < 0`): if `q_t < 0` then
`𝔼[f_t(η) | x_t] < 0` for every `η > 0`. -/
theorem expF_neg_of_pCoef_nonpos (η : ℝ) (c : ι → ℝ) (hp : P.pCoef N c ≤ 0)
    (hq : P.qCoef c < 0) (hη : 0 < η) : P.expF N η c < 0 := by
  rw [P.expF_eq_mul]
  have h1 : P.pCoef N c * η ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hp hη.le
  exact mul_neg_of_pos_of_neg hη (by linarith)

/-- **Remark, case `p_t < 0`**: `𝔼[f_t(η) | x_t] < 0` for every `η > 0`. Only `q_t ≤ 0` (which
always holds) is needed, so this case of the Remark is correct even when `θ_t ∈ {0, 1}`. -/
theorem expF_neg_of_pCoef_neg (η : ℝ) (c : ι → ℝ) (hp : P.pCoef N c < 0) (hη : 0 < η) :
    P.expF N η c < 0 := by
  rw [P.expF_eq_mul]
  have h1 : P.pCoef N c * η < 0 := mul_neg_of_neg_of_pos hp hη
  have h2 := P.qCoef_nonpos c
  exact mul_neg_of_pos_of_neg hη (by linarith)

/-- If `p_t ≤ 0` then `𝔼[f_t(η) | x_t] ≤ 0` for every `η ≥ 0`. -/
theorem expF_nonpos_of_pCoef_nonpos (η : ℝ) (c : ι → ℝ) (hp : P.pCoef N c ≤ 0) (hη : 0 ≤ η) :
    P.expF N η c ≤ 0 := by
  rw [P.expF_eq_mul]
  have h1 : P.pCoef N c * η ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hp hη
  have h2 := P.qCoef_nonpos c
  exact mul_nonpos_of_nonneg_of_nonpos hη (by linarith)

/-- Complete description of the increase regime: for `η > 0`,
`𝔼[f_t(η) | x_t] > 0` iff `p_t > 0` and `η > η*_t`. -/
theorem expF_pos_iff (η : ℝ) (c : ι → ℝ) (hη : 0 < η) :
    0 < P.expF N η c ↔ 0 < P.pCoef N c ∧ P.etaStar N c < η := by
  constructor
  · intro h
    have hp : 0 < P.pCoef N c := by
      by_contra hp
      have := P.expF_nonpos_of_pCoef_nonpos N η c (not_lt.mp hp) hη.le
      linarith
    exact ⟨hp, (P.expF_pos_iff_etaStar_lt N η c hp hη).mp h⟩
  · rintro ⟨hp, h⟩
    exact (P.expF_pos_iff_etaStar_lt N η c hp hη).mpr h

/-- Complete description of the decrease regime: for `η > 0`, `𝔼[f_t(η) | x_t] < 0` iff either
`p_t > 0` and `η < η*_t`, or `p_t ≤ 0` and one of `p_t`, `q_t` is strictly negative. -/
theorem expF_neg_iff (η : ℝ) (c : ι → ℝ) (hη : 0 < η) :
    P.expF N η c < 0 ↔
      (0 < P.pCoef N c ∧ η < P.etaStar N c) ∨
        (P.pCoef N c ≤ 0 ∧ (P.pCoef N c < 0 ∨ P.qCoef c < 0)) := by
  constructor
  · intro h
    rcases lt_or_ge 0 (P.pCoef N c) with hp | hp
    · exact Or.inl ⟨hp, (P.expF_neg_iff_lt_etaStar N η c hp hη).mp h⟩
    · refine Or.inr ⟨hp, ?_⟩
      by_contra hne
      rw [not_or] at hne
      have hp0 : P.pCoef N c = 0 := le_antisymm hp (not_lt.mp hne.1)
      have hq0 : P.qCoef c = 0 := le_antisymm (P.qCoef_nonpos c) (not_lt.mp hne.2)
      rw [P.expF_eq, hp0, hq0] at h
      simp at h
  · rintro (⟨hp, h⟩ | ⟨hp, hp' | hq⟩)
    · exact (P.expF_neg_iff_lt_etaStar N η c hp hη).mpr h
    · exact P.expF_neg_of_pCoef_neg N η c hp' hη
    · exact P.expF_neg_of_pCoef_nonpos N η c hp hq hη

/-- **Counterexample to the Remark's "since `q_t < 0`, there exists a positive critical step size
`η*_t > 0`"**: whenever the dominant block carries noise (`e_𝒟 > 0`) there is a non-zero state
(with `θ_t = 0`) such that `p_t > 0` but `η*_t = 0`; there `𝔼[f_t(η) | x_t] > 0` for *every*
`η ≠ 0`, so there is no decrease regime at all. -/
theorem exists_pCoef_pos_and_etaStar_eq_zero (he : 0 < P.eD N) :
    ∃ c : ι → ℝ, c ≠ 0 ∧ 0 < P.pCoef N c ∧ P.etaStar N c = 0 ∧
      ∀ η : ℝ, η ≠ 0 → 0 < P.expF N η c := by
  have hD : P.sD (Pi.single P.ik1 1) = 0 := by
    unfold sD
    rw [mom_eq_zero_iff]
    intro i hi
    have hne : i ≠ P.ik1 := fun h => P.ik1_not_mem (h ▸ hi)
    simp [hne]
  have hB : 0 < P.sB (Pi.single P.ik1 1) := by
    unfold sB
    rw [mom_pos_iff]
    exact ⟨P.ik1, P.mem_B.mpr P.ik1_not_mem, by simp⟩
  have hq := P.qCoef_eq_zero_of_sD_eq_zero hD
  have hp : 0 < P.pCoef N (Pi.single P.ik1 1) := by
    rw [P.pCoef_of_sD_eq_zero N hD]
    exact mul_pos hB he
  refine ⟨Pi.single P.ik1 1, ?_, hp, ?_, ?_⟩
  · intro h
    have := congrFun h P.ik1
    simp at this
  · unfold etaStar
    rw [hq, neg_zero, zero_div]
  · intro η hη
    rw [P.expF_eq, hq, zero_mul, add_zero]
    exact mul_pos hp (by positivity)

/-! ### Deterministic equivalent (`thetaBarNext`) and the bridge to `expF` -/

/-- `0 ≤ thetaBarNext`. -/
theorem thetaBarNext_nonneg (η : ℝ) (c : ι → ℝ) : 0 ≤ P.thetaBarNext N η c :=
  div_nonneg (P.EsNext_nonneg N _ η c)
    (add_nonneg (P.EsNext_nonneg N _ η c) (P.EsNext_nonneg N _ η c))

/-- `thetaBarNext ≤ 1`. -/
theorem thetaBarNext_le_one (η : ℝ) (c : ι → ℝ) : P.thetaBarNext N η c ≤ 1 := by
  have hD := P.EsNext_nonneg N P.D η c
  have hB := P.EsNext_nonneg N P.B η c
  unfold thetaBarNext
  rcases (add_nonneg hD hB).eq_or_lt with h | h
  · rw [← h, div_zero]
    exact zero_le_one
  · rw [div_le_one h]
    linarith

/-- At `η = 0` the deterministic equivalent is the current alignment. -/
theorem thetaBarNext_zero (c : ι → ℝ) : P.thetaBarNext N 0 c = P.theta c := by
  unfold thetaBarNext theta s sD sB
  rw [P.EsNext_zero, P.EsNext_zero]

/-- The deterministic equivalent in the form of eq. (10) / eq. (ratio-asymp):
`thetaBarNext = 1 / (1 + 𝔼[s^ℬ_{t+1} | x_t] / 𝔼[s^𝒟_{t+1} | x_t])` when
`𝔼[s^𝒟_{t+1} | x_t] ≠ 0`. -/
theorem thetaBarNext_eq_one_div (η : ℝ) (c : ι → ℝ) (h : P.EsNext N P.D η c ≠ 0) :
    P.thetaBarNext N η c = 1 / (1 + P.EsNext N P.B η c / P.EsNext N P.D η c) := by
  have hD : 0 < P.EsNext N P.D η c := lt_of_le_of_ne (P.EsNext_nonneg N _ η c) (Ne.symm h)
  have hB := P.EsNext_nonneg N P.B η c
  have hs : P.EsNext N P.D η c + P.EsNext N P.B η c ≠ 0 := by positivity
  unfold thetaBarNext
  field_simp

/-- **Bridge**: `thetaBarNext - θ_t = 𝔼[f_t(η) | x_t] / (s_t · 𝔼[s_{t+1} | x_t])` whenever
`s_t ≠ 0` and `𝔼[s_{t+1} | x_t] ≠ 0`. -/
theorem thetaBarNext_sub_theta (η : ℝ) (c : ι → ℝ) (hs : P.s c ≠ 0)
    (hE : P.EsNext N P.D η c + P.EsNext N P.B η c ≠ 0) :
    P.thetaBarNext N η c - P.theta c =
      P.expF N η c / (P.s c * (P.EsNext N P.D η c + P.EsNext N P.B η c)) := by
  unfold thetaBarNext theta expF
  rw [div_sub_div _ _ hE hs, mul_comm (P.EsNext N P.D η c + P.EsNext N P.B η c) (P.s c)]
  congr 1
  unfold s
  ring

/-- **Exact validity of the bridge (decrease)**: the equivalence
`thetaBarNext < θ_t ↔ 𝔼[f_t(η) | x_t] < 0` holds *if and only if* `𝔼[s_{t+1} | x_t] > 0` or
`s^𝒟_t = 0`. -/
theorem thetaBarNext_lt_theta_iff_sharp (η : ℝ) (c : ι → ℝ) :
    (P.thetaBarNext N η c < P.theta c ↔ P.expF N η c < 0) ↔
      (0 < P.EsNext N P.D η c + P.EsNext N P.B η c ∨ P.sD c = 0) := by
  unfold thetaBarNext theta s expF
  exact ratio_gt_ratio_iff_sharp (P.sD_nonneg c) (P.sB_nonneg c) (P.EsNext_nonneg N P.D η c)
    (P.EsNext_nonneg N P.B η c)

/-- **Exact validity of the bridge (increase)**: the equivalence
`θ_t < thetaBarNext ↔ 𝔼[f_t(η) | x_t] > 0` holds *if and only if* `x_t ≠ 0` or
`𝔼[s^𝒟_{t+1} | x_t] = 0`. -/
theorem theta_lt_thetaBarNext_iff_sharp (η : ℝ) (c : ι → ℝ) :
    (P.theta c < P.thetaBarNext N η c ↔ 0 < P.expF N η c) ↔
      (0 < P.s c ∨ P.EsNext N P.D η c = 0) := by
  unfold thetaBarNext theta s expF
  exact ratio_lt_ratio_iff_sharp (P.sD_nonneg c) (P.sB_nonneg c) (P.EsNext_nonneg N P.D η c)
    (P.EsNext_nonneg N P.B η c)

/-- **Exact validity of the bridge (equality)**: the equivalence
`thetaBarNext = θ_t ↔ 𝔼[f_t(η) | x_t] = 0` holds *if and only if* both
(`x_t ≠ 0` or `𝔼[s^𝒟_{t+1} | x_t] = 0`) and (`𝔼[s_{t+1} | x_t] > 0` or `s^𝒟_t = 0`). -/
theorem thetaBarNext_eq_theta_iff_sharp (η : ℝ) (c : ι → ℝ) :
    (P.thetaBarNext N η c = P.theta c ↔ P.expF N η c = 0) ↔
      ((0 < P.s c ∨ P.EsNext N P.D η c = 0) ∧
        (0 < P.EsNext N P.D η c + P.EsNext N P.B η c ∨ P.sD c = 0)) := by
  unfold thetaBarNext theta s expF
  exact ratio_eq_ratio_iff_sharp (P.sD_nonneg c) (P.sB_nonneg c) (P.EsNext_nonneg N P.D η c)
    (P.EsNext_nonneg N P.B η c)

/-- **Bridge (decrease)**: for `𝔼[s_{t+1} | x_t] > 0`,
`thetaBarNext < θ_t ↔ 𝔼[f_t(η) | x_t] < 0`. Nothing is assumed on `x_t`: if `x_t = 0` both sides
are false. The hypothesis cannot be dropped (`thetaBarNext_lt_theta_iff_sharp`,
`exists_thetaBarNext_lt_theta_and_expF_eq_zero`); it holds for every state as soon as `η ≠ 0` and
`s_min > 0` (`thetaBarNext_lt_theta_iff_of_smin_pos`). -/
theorem thetaBarNext_lt_theta_iff (η : ℝ) (c : ι → ℝ)
    (hE : 0 < P.EsNext N P.D η c + P.EsNext N P.B η c) :
    P.thetaBarNext N η c < P.theta c ↔ P.expF N η c < 0 :=
  (P.thetaBarNext_lt_theta_iff_sharp N η c).mpr (Or.inl hE)

/-- **Bridge (increase)**: for `x_t ≠ 0` (`s_t > 0`),
`θ_t < thetaBarNext ↔ 𝔼[f_t(η) | x_t] > 0`. Nothing is assumed on `𝔼[s_{t+1} | x_t]`: if it
vanishes both sides are false. The hypothesis cannot be dropped
(`theta_lt_thetaBarNext_iff_sharp`, `theta_zero_lt_thetaBarNext_and_expF_eq_zero`). -/
theorem theta_lt_thetaBarNext_iff (η : ℝ) (c : ι → ℝ) (hs : 0 < P.s c) :
    P.theta c < P.thetaBarNext N η c ↔ 0 < P.expF N η c :=
  (P.theta_lt_thetaBarNext_iff_sharp N η c).mpr (Or.inl hs)

/-- **Bridge (equality)**: for `s_t > 0` and `𝔼[s_{t+1} | x_t] > 0`,
`thetaBarNext = θ_t ↔ 𝔼[f_t(η) | x_t] = 0` (here both hypotheses are needed, see
`thetaBarNext_eq_theta_iff_sharp`). -/
theorem thetaBarNext_eq_theta_iff (η : ℝ) (c : ι → ℝ) (hs : 0 < P.s c)
    (hE : 0 < P.EsNext N P.D η c + P.EsNext N P.B η c) :
    P.thetaBarNext N η c = P.theta c ↔ P.expF N η c = 0 :=
  (P.thetaBarNext_eq_theta_iff_sharp N η c).mpr ⟨Or.inl hs, Or.inl hE⟩

/-- **Bridge (decrease) under non-degenerate noise**: for `η ≠ 0` and `s_min > 0`,
`thetaBarNext < θ_t ↔ 𝔼[f_t(η) | x_t] < 0` holds for *every* state (including `x_t = 0`). -/
theorem thetaBarNext_lt_theta_iff_of_smin_pos {η : ℝ} (hη : η ≠ 0) (hs : 0 < N.smin)
    (c : ι → ℝ) : P.thetaBarNext N η c < P.theta c ↔ P.expF N η c < 0 :=
  P.thetaBarNext_lt_theta_iff N η c (P.EsNext_D_add_EsNext_B_pos_of_smin_pos N hη hs c)

/-- `𝔼[f_t(η) | x_t] < 0 → thetaBarNext < θ_t`, with no positivity hypothesis (negativity of
`expF` already forces `𝔼[s_{t+1} | x_t] > 0`). -/
theorem thetaBarNext_lt_theta_of_expF_neg (η : ℝ) (c : ι → ℝ) (h : P.expF N η c < 0) :
    P.thetaBarNext N η c < P.theta c := by
  have h1 : 0 < P.EsNext N P.B η c * P.sD c := by
    have := mul_nonneg (P.sB_nonneg c) (P.EsNext_nonneg N P.D η c)
    unfold expF at h
    linarith
  obtain ⟨hEB, -⟩ := pos_and_pos_of_mul_pos h1 (P.EsNext_nonneg N _ η c) (P.sD_nonneg c)
  have hE : 0 < P.EsNext N P.D η c + P.EsNext N P.B η c := by
    linarith [P.EsNext_nonneg N P.D η c]
  exact (P.thetaBarNext_lt_theta_iff N η c hE).mpr h

/-- `𝔼[f_t(η) | x_t] > 0 → θ_t < thetaBarNext`, with no positivity hypothesis (positivity of
`expF` already forces `s_t > 0`). -/
theorem theta_lt_thetaBarNext_of_expF_pos (η : ℝ) (c : ι → ℝ) (h : 0 < P.expF N η c) :
    P.theta c < P.thetaBarNext N η c := by
  have h1 : 0 < P.sB c * P.EsNext N P.D η c := by
    have := mul_nonneg (P.EsNext_nonneg N P.B η c) (P.sD_nonneg c)
    unfold expF at h
    linarith
  obtain ⟨hB, -⟩ := pos_and_pos_of_mul_pos h1 (P.sB_nonneg c) (P.EsNext_nonneg N _ η c)
  have hs : 0 < P.s c := by unfold s; linarith [P.sD_nonneg c]
  exact (P.theta_lt_thetaBarNext_iff N η c hs).mpr h

/-- The hypothesis `s_t > 0` in `theta_lt_thetaBarNext_iff` (and in `thetaBarNext_eq_theta_iff`)
cannot be dropped: at `x_t = 0` (where `θ_t = 0` by convention) with noise in the dominant block
(`e_𝒟 > 0`) and `η ≠ 0`, the deterministic equivalent is positive although
`𝔼[f_t(η) | x_t] = 0`. -/
theorem theta_zero_lt_thetaBarNext_and_expF_eq_zero {η : ℝ} (hη : η ≠ 0) (he : 0 < P.eD N) :
    P.theta 0 < P.thetaBarNext N η 0 ∧ P.expF N η 0 = 0 := by
  have hD : P.EsNext N P.D η 0 = η ^ 2 * P.eD N := by
    rw [P.EsNext_D]
    simp [sD, tauD, mom]
  have hB := P.EsNext_nonneg N P.B η 0
  have hDpos : 0 < P.EsNext N P.D η 0 := by
    rw [hD]
    positivity
  constructor
  · rw [P.theta_zero]
    unfold thetaBarNext
    positivity
  · simp [expF, sB, sD, mom]

/-- The hypothesis `𝔼[s_{t+1} | x_t] > 0` in `thetaBarNext_lt_theta_iff` (and in
`thetaBarNext_eq_theta_iff`) cannot be dropped: with no noise (`κ_i² = 0`), the step `η = 1/λ_1` from the unit vector along `u_1` gives
`𝔼[s_{t+1} | x_t] = 0`, so `thetaBarNext = 0 < 1 = θ_t` (Lean's `0 / 0 = 0`) although
`𝔼[f_t(η) | x_t] = 0`. -/
theorem exists_thetaBarNext_lt_theta_and_expF_eq_zero (hN : ∀ i, N.kap2 i = 0) :
    ∃ (η : ℝ) (c : ι → ℝ), P.thetaBarNext N η c < P.theta c ∧ P.expF N η c = 0 := by
  have hE : ∀ S, P.EsNext N S (1 / P.lam P.i1) (Pi.single P.i1 1) = 0 := by
    intro S
    rw [P.EsNext_eq_zero_iff]
    intro i _
    refine ⟨?_, by rw [hN i, mul_zero]⟩
    by_cases hi : i = P.i1
    · subst hi
      simp [(P.lam_pos _).ne']
    · simp [hi]
  refine ⟨1 / P.lam P.i1, Pi.single P.i1 1, ?_, ?_⟩
  · unfold thetaBarNext
    rw [hE, hE, add_zero, div_zero, theta_pos_iff]
    unfold sD
    rw [mom_pos_iff]
    exact ⟨P.i1, P.i1_mem, by simp⟩
  · unfold expF
    rw [hE, hE]
    ring

/-- **Finite-`d` core of the decrease condition (Theorem 2, deterministic equivalent)**, with
exactly the hypothesis of the paper's Theorem 2: if `0 < η < η*_t` then `thetaBarNext < θ_t`.
(The hypothesis forces `p_t > 0` and `0 < θ_t < 1`, see `lt_etaStar_iff` and
`etaStar_pos_iff_pCoef_pos_and_theta`; for `p_t ≤ 0` Lean's `η*_t` is `≤ 0`, the hypothesis is
empty, and the decrease is given by `thetaBarNext_lt_theta_of_pCoef_nonpos` instead.) -/
theorem thetaBarNext_lt_theta_of_lt_etaStar (η : ℝ) (c : ι → ℝ) (hη : 0 < η)
    (h : η < P.etaStar N c) : P.thetaBarNext N η c < P.theta c :=
  P.thetaBarNext_lt_theta_of_expF_neg N η c (P.expF_neg_of_lt_etaStar N η c hη h)

/-- **Finite-`d` core of the increase condition (deterministic equivalent)**:
if `p_t > 0` and `η > η*_t` then `θ_t < thetaBarNext`. -/
theorem theta_lt_thetaBarNext_of_etaStar_lt (η : ℝ) (c : ι → ℝ) (hp : 0 < P.pCoef N c)
    (h : P.etaStar N c < η) : P.theta c < P.thetaBarNext N η c := by
  have hη : 0 < η := lt_of_le_of_lt (P.etaStar_nonneg N c hp) h
  exact P.theta_lt_thetaBarNext_of_expF_pos N η c
    ((P.expF_pos_iff_etaStar_lt N η c hp hη).mpr h)

/-- **Finite-`d` core of the case `p_t ≤ 0` (deterministic equivalent)**: if `p_t ≤ 0` and both
block energies are positive (`0 < θ_t < 1`), then `thetaBarNext < θ_t` for every `η > 0`. -/
theorem thetaBarNext_lt_theta_of_pCoef_nonpos (η : ℝ) (c : ι → ℝ) (hp : P.pCoef N c ≤ 0)
    (hD : 0 < P.sD c) (hB : 0 < P.sB c) (hη : 0 < η) : P.thetaBarNext N η c < P.theta c :=
  P.thetaBarNext_lt_theta_of_expF_neg N η c
    (P.expF_neg_of_pCoef_nonpos N η c hp (P.qCoef_neg hD hB) hη)

/-! ### Abstract expectation

The two lemmas of A.5 only use `𝔼 ζ_i = 0` and `𝔼 ζ_i² = κ_i²`. We record this for an arbitrary
normalised linear functional `E` defined on *all* functions of the sample point. Finite averages
(and finitely additive expectations) are instances; the Bochner integral is not, since it is only
linear on integrable functions. The measure-theoretic version, with its integrability side
conditions, belongs to the probability layer (`SuspiciousAlignment/Prob/NoiseModel.lean`), where
it follows from linearity of the integral exactly as below; the pathwise identities
`mom_two_cNext_sub_EsNext` and `fCompare_sub_expF` isolate the two terms whose integrals vanish. -/

section AbstractExpectation

variable {Ω : Type*}

/-- **Lemma "Elementwise expectation"** for an abstract expectation `E`: if `E 1 = 1`,
`E ζ_i = 0` and `E ζ_i² = κ_i²`, then `E[s^S_{t+1}] = EsNext`. -/
theorem expect_mom_two_cNext (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (hE : E (fun _ => 1) = 1)
    (ζ : Ω → ι → ℝ) (hmean : ∀ i, E (fun ω => ζ ω i) = 0)
    (hvar : ∀ i, E (fun ω => ζ ω i ^ 2) = N.kap2 i) (S : Finset ι) (η : ℝ) (c : ι → ℝ) :
    E (fun ω => P.mom S 2 (P.cNext η c (ζ ω))) = P.EsNext N S η c := by
  have hfun : (fun ω => P.mom S 2 (P.cNext η c (ζ ω))) =
      ∑ i ∈ S, ((P.lam i ^ 2 * (1 - η * P.lam i) ^ 2 * c i ^ 2) • (fun _ : Ω => (1 : ℝ))
        + (-(2 * η) * (P.lam i ^ 2 * (1 - η * P.lam i) * c i)) • (fun ω => ζ ω i)
        + (η ^ 2 * P.lam i ^ 2) • (fun ω => ζ ω i ^ 2)) := by
    funext ω
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    unfold mom
    exact Finset.sum_congr rfl fun i _ => by rw [P.lam_sq_mul_cNext_sq]; ring
  rw [hfun, map_sum]
  unfold EsNext
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_add, map_add, map_smul, map_smul, map_smul, hE, hmean, hvar]
  simp only [smul_eq_mul]
  ring

/-- **Lemma "Quadratic form"**, first line of the proof, for an abstract expectation `E`:
`E[f_t(η)] = expF`, hence `= p_t η² + q_t η` by `expF_eq`. -/
theorem expect_fCompare (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (hE : E (fun _ => 1) = 1)
    (ζ : Ω → ι → ℝ) (hmean : ∀ i, E (fun ω => ζ ω i) = 0)
    (hvar : ∀ i, E (fun ω => ζ ω i ^ 2) = N.kap2 i) (η : ℝ) (c : ι → ℝ) :
    E (fun ω => P.fCompare η c (ζ ω)) = P.expF N η c := by
  have hfun : (fun ω => P.fCompare η c (ζ ω)) =
      P.sB c • (fun ω => P.mom P.D 2 (P.cNext η c (ζ ω)))
        - P.sD c • (fun ω => P.mom P.B 2 (P.cNext η c (ζ ω))) := by
    funext ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    unfold fCompare sD sB
    ring
  rw [hfun, map_sub, map_smul, map_smul, P.expect_mom_two_cNext N E hE ζ hmean hvar,
    P.expect_mom_two_cNext N E hE ζ hmean hvar]
  unfold expF
  simp only [smul_eq_mul]
  ring

end AbstractExpectation

end Spec

/-! ### Non-vacuity: concrete instances

The hypotheses of the main statements are jointly satisfiable. We exhibit the two-dimensional
problem `λ = (2, 1)`, `𝒟 = {0}`, `x_t = (1, 1)` (so `θ_t = 4/5`), for which, with isotropic unit
noise, `p_t = 12 > 0`, `q_t = -8 < 0` and `η*_t = 2/3`; and with noise only in the bulk direction
(`κ² = (0, 10)`) `p_t = -28 < 0`. -/

namespace OneStep

/-- The spectrum `λ = (2, 1)` on `Fin 2` with dominant block `𝒟 = {0}`. -/
def exSpec : Spec (Fin 2) where
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
  le_lam1 := by intro i hi; fin_cases i <;> simp at hi ⊢
  lamk_le := by intro i hi; fin_cases i <;> simp at hi ⊢
  le_lamk1 := by intro i hi; fin_cases i <;> simp at hi ⊢
  lamd_le := by intro i hi; fin_cases i <;> simp at hi ⊢
  gap := by simp

/-- Isotropic unit noise `κ_i² = 1` on `Fin 2`. -/
def exNoise : Noise (Fin 2) where
  kap2 := fun _ => 1
  smin := 1
  smax := 1
  smin_nonneg := zero_le_one
  smin_le := fun _ => le_refl _
  le_smax := fun _ => le_refl _

/-- Noise only in the bulk direction: `κ² = (0, 10)` on `Fin 2`. -/
def exNoiseB : Noise (Fin 2) where
  kap2 := ![0, 10]
  smin := 0
  smax := 10
  smin_nonneg := le_refl _
  smin_le := by intro i; fin_cases i <;> simp
  le_smax := by intro i; fin_cases i <;> simp

theorem exSpec_B : exSpec.B = {1} := by decide

theorem exSpec_mom_D (p : ℕ) (c : Fin 2 → ℝ) : exSpec.mom exSpec.D p c = 2 ^ p * c 0 ^ 2 := by
  change ∑ i ∈ ({0} : Finset (Fin 2)), exSpec.lam i ^ p * c i ^ 2 = _
  rw [Finset.sum_singleton]
  rfl

theorem exSpec_mom_B (p : ℕ) (c : Fin 2 → ℝ) : exSpec.mom exSpec.B p c = c 1 ^ 2 := by
  unfold Spec.mom
  rw [exSpec_B, Finset.sum_singleton]
  simp [exSpec]

theorem exSpec_eD (N : Noise (Fin 2)) : exSpec.eD N = 4 * N.kap2 0 := by
  change ∑ i ∈ ({0} : Finset (Fin 2)), exSpec.lam i ^ 2 * N.kap2 i = _
  rw [Finset.sum_singleton]
  simp [exSpec]
  norm_num

theorem exSpec_eB (N : Noise (Fin 2)) : exSpec.eB N = N.kap2 1 := by
  unfold Spec.eB
  rw [exSpec_B, Finset.sum_singleton]
  simp [exSpec]

theorem exSpec_sD : exSpec.sD ![1, 1] = 4 := by
  simp [Spec.sD, exSpec_mom_D]
  norm_num

theorem exSpec_sB : exSpec.sB ![1, 1] = 1 := by
  simp [Spec.sB, exSpec_mom_B]

theorem exSpec_qCoef : exSpec.qCoef ![1, 1] = -8 := by
  simp [Spec.qCoef, Spec.sD, Spec.sB, Spec.tauD, Spec.tauB, exSpec_mom_D, exSpec_mom_B]
  norm_num

theorem exSpec_pCoef : exSpec.pCoef exNoise ![1, 1] = 12 := by
  simp [Spec.pCoef, Spec.sD, Spec.sB, exSpec_eD, exSpec_eB, exSpec_mom_D, exSpec_mom_B, exNoise]
  norm_num

theorem exSpec_pCoef_B : exSpec.pCoef exNoiseB ![1, 1] = -28 := by
  simp [Spec.pCoef, Spec.sD, Spec.sB, exSpec_eD, exSpec_eB, exSpec_mom_D, exSpec_mom_B, exNoiseB]
  norm_num

theorem exSpec_etaStar : exSpec.etaStar exNoise ![1, 1] = 2 / 3 := by
  unfold Spec.etaStar
  rw [exSpec_qCoef, exSpec_pCoef]
  norm_num

/-- Decrease regime (`p_t > 0`, `0 < η = 1/2 < η*_t = 2/3`): the hypotheses of
`Spec.thetaBarNext_lt_theta_of_lt_etaStar` are satisfiable. -/
example : exSpec.thetaBarNext exNoise (1 / 2) ![1, 1] < exSpec.theta ![1, 1] :=
  exSpec.thetaBarNext_lt_theta_of_lt_etaStar exNoise _ _ (by norm_num)
    (by rw [exSpec_etaStar]; norm_num)

/-- Increase regime (`p_t > 0`, `η = 1 > η*_t = 2/3`): the hypotheses of
`Spec.theta_lt_thetaBarNext_of_etaStar_lt` are satisfiable. -/
example : exSpec.theta ![1, 1] < exSpec.thetaBarNext exNoise 1 ![1, 1] :=
  exSpec.theta_lt_thetaBarNext_of_etaStar_lt exNoise _ _ (by rw [exSpec_pCoef]; norm_num)
    (by rw [exSpec_etaStar]; norm_num)

/-- The regime `p_t ≤ 0` with `0 < θ_t < 1`: the hypotheses of
`Spec.thetaBarNext_lt_theta_of_pCoef_nonpos` are satisfiable. -/
example : exSpec.thetaBarNext exNoiseB 1 ![1, 1] < exSpec.theta ![1, 1] :=
  exSpec.thetaBarNext_lt_theta_of_pCoef_nonpos exNoiseB _ _ (by rw [exSpec_pCoef_B]; norm_num)
    (by rw [exSpec_sD]; norm_num) (by rw [exSpec_sB]; norm_num) one_pos

/-- The Rademacher average on `Bool`, a normalised linear functional. -/
noncomputable def boolE : (Bool → ℝ) →ₗ[ℝ] ℝ where
  toFun f := (f true + f false) / 2
  map_add' f g := by simp only [Pi.add_apply]; ring
  map_smul' a f := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The hypotheses of `Spec.expect_fCompare` are satisfiable for every spectrum and every noise
profile: the symmetric two-point noise `ζ_i = ± κ_i` has mean `0` and second moments `κ_i²`. -/
example (P : Spec ι) (N : Noise ι) (η : ℝ) (c : ι → ℝ) :
    boolE (fun b => P.fCompare η c
      (fun i => if b then Real.sqrt (N.kap2 i) else -Real.sqrt (N.kap2 i))) = P.expF N η c :=
  P.expect_fCompare N boolE (by simp [boolE]) _ (fun i => by simp [boolE])
    (fun i => by simp [boolE, Real.sq_sqrt (Spec.kap2_nonneg N i)]) η c

/-! ### The sign of `𝔼[f_t]` versus the sign of `𝔼[θ_{t+1}] - θ_t` at finite `d`

The Remark after Lemma "Quadratic form" says "`𝔼[f_t(η)] < 0`, implying the expected alignment
`𝔼[θ_{t+1}]` decreases" (and the analogue for `> 0`). At finite `d` the sign of `𝔼[f_t]` decides
the sign of `thetaBarNext - θ_t` (section *Deterministic equivalent*), **not** the sign of
`𝔼[θ_{t+1}] - θ_t`: the two lemmas of A.5 only use the first two moments of the noise, and the two
explicit instances below (two-point noise `ζ = ±(a, a)` with mean `0` and second moments `a²`, on
the example spectrum `λ = (2, 1)`, `x_t = (1, 1)`, `θ_t = 4/5`, `η*_t = 2/3`) show that these
moments do not determine the sign of `𝔼[θ_{t+1}] - θ_t`, in either direction. (For Gaussian noise
the same phenomenon is observed numerically, see the fidelity note; the paper's implication is
only valid in the limit `d → ∞`.) -/

/-- Isotropic noise `κ_i² = 4` on `Fin 2`. -/
def exNoise4 : Noise (Fin 2) where
  kap2 := fun _ => 4
  smin := 4
  smax := 4
  smin_nonneg := by norm_num
  smin_le := fun _ => le_refl _
  le_smax := fun _ => le_refl _

theorem exSpec_pCoef_4 : exSpec.pCoef exNoise4 ![1, 1] = 12 := by
  simp [Spec.pCoef, Spec.sD, Spec.sB, exSpec_eD, exSpec_eB, exSpec_mom_D, exSpec_mom_B, exNoise4]
  norm_num

theorem exSpec_etaStar_4 : exSpec.etaStar exNoise4 ![1, 1] = 2 / 3 := by
  unfold Spec.etaStar
  rw [exSpec_qCoef, exSpec_pCoef_4]
  norm_num

/-- The alignment of an explicit state for the example spectrum:
`θ(v) = 4 v_0² / (4 v_0² + v_1²)`. -/
theorem exSpec_theta (v : Fin 2 → ℝ) :
    exSpec.theta v = 4 * v 0 ^ 2 / (4 * v 0 ^ 2 + v 1 ^ 2) := by
  unfold Spec.theta Spec.s Spec.sD Spec.sB
  rw [exSpec_mom_D, exSpec_mom_B]
  norm_num

theorem exSpec_cNext_zero (η : ℝ) (c ζ : Fin 2 → ℝ) :
    exSpec.cNext η c ζ 0 = (1 - η * 2) * c 0 - η * ζ 0 := rfl

theorem exSpec_cNext_one (η : ℝ) (c ζ : Fin 2 → ℝ) :
    exSpec.cNext η c ζ 1 = (1 - η * 1) * c 1 - η * ζ 1 := rfl

theorem boolE_apply (f : Bool → ℝ) : boolE f = (f true + f false) / 2 := rfl

/-- The symmetric two-point noise `ζ = ±(a, a)` on the sample space `Bool`. -/
def exZeta (a : ℝ) : Bool → Fin 2 → ℝ := fun b _ => if b then a else -a

/-- The two-point noise `±(a, a)` has mean `0` and second moments `a²`; hence, for any noise
profile with `κ_i² = a²`, its expected comparison functional is `expF = p_t η² + q_t η`
(an instance of `Spec.expect_fCompare`). -/
theorem boolE_fCompare_exZeta (N : Noise (Fin 2)) (a : ℝ) (hN : ∀ i, N.kap2 i = a ^ 2) (η : ℝ)
    (c : Fin 2 → ℝ) :
    boolE (fun b => exSpec.fCompare η c (exZeta a b)) = exSpec.expF N η c :=
  exSpec.expect_fCompare N boolE (by simp [boolE]) _ (fun i => by simp [boolE, exZeta])
    (fun i => by rw [hN i]; simp [boolE, exZeta]) η c

/-- **At finite `d`, `𝔼[f_t] > 0` does not imply that `𝔼[θ_{t+1}]` increases.** For
`λ = (2, 1)`, `x_t = (1, 1)`, `κ² = (1, 1)`, `η = 1 > η*_t = 2/3` and the two-point noise
`ζ = ±(1, 1)`: `𝔼[f_t] = 4 > 0` and `θ_t = 4/5 < thetaBarNext = 8/9`, but
`𝔼[θ_{t+1}] = (16/17 + 0)/2 = 8/17 < 4/5 = θ_t`. -/
theorem exSpec_expect_fCompare_pos_and_expect_theta_lt :
    0 < boolE (fun b => exSpec.fCompare 1 ![1, 1] (exZeta 1 b)) ∧
      exSpec.theta ![1, 1] < exSpec.thetaBarNext exNoise 1 ![1, 1] ∧
      boolE (fun b => exSpec.theta (exSpec.cNext 1 ![1, 1] (exZeta 1 b))) <
        exSpec.theta ![1, 1] := by
  have h : 0 < exSpec.expF exNoise 1 ![1, 1] := by
    rw [Spec.expF_eq, exSpec_pCoef, exSpec_qCoef]
    norm_num
  refine ⟨?_, exSpec.theta_lt_thetaBarNext_of_expF_pos exNoise _ _ h, ?_⟩
  · rw [boolE_fCompare_exZeta exNoise 1 (fun _ => by norm_num [exNoise])]
    exact h
  · simp only [boolE_apply, exSpec_theta, exSpec_cNext_zero, exSpec_cNext_one, exZeta]
    norm_num

/-- **At finite `d`, `0 < η < η*_t` (hence `𝔼[f_t] < 0`) does not imply that `𝔼[θ_{t+1}]`
decreases.** For `λ = (2, 1)`, `x_t = (1, 1)`, `κ² = (4, 4)`, `η = 1/3 < η*_t = 2/3` and the
two-point noise `ζ = ±(2, 2)`: `𝔼[f_t] = -4/3 < 0` and `thetaBarNext = 5/7 < 4/5 = θ_t`, but
`𝔼[θ_{t+1}] = (1 + 9/13)/2 = 11/13 > 4/5 = θ_t`. -/
theorem exSpec_expect_fCompare_neg_and_theta_lt_expect_theta :
    (0 : ℝ) < 1 / 3 ∧ (1 / 3 : ℝ) < exSpec.etaStar exNoise4 ![1, 1] ∧
      boolE (fun b => exSpec.fCompare (1 / 3) ![1, 1] (exZeta 2 b)) < 0 ∧
      exSpec.thetaBarNext exNoise4 (1 / 3) ![1, 1] < exSpec.theta ![1, 1] ∧
      exSpec.theta ![1, 1] <
        boolE (fun b => exSpec.theta (exSpec.cNext (1 / 3) ![1, 1] (exZeta 2 b))) := by
  have h : exSpec.expF exNoise4 (1 / 3) ![1, 1] < 0 := by
    rw [Spec.expF_eq, exSpec_pCoef_4, exSpec_qCoef]
    norm_num
  refine ⟨by norm_num, by rw [exSpec_etaStar_4]; norm_num, ?_,
    exSpec.thetaBarNext_lt_theta_of_expF_neg exNoise4 _ _ h, ?_⟩
  · rw [boolE_fCompare_exZeta exNoise4 2 (fun _ => by norm_num [exNoise4])]
    exact h
  · simp only [boolE_apply, exSpec_theta, exSpec_cNext_zero, exSpec_cNext_one, exZeta]
    norm_num

end OneStep

end SuspiciousAlignment
