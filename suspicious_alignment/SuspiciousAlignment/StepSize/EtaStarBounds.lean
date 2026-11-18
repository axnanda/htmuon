import Mathlib
import SuspiciousAlignment.Defs

/-!
# State- and gap-aware bounds on the critical step size `η*_t`

Formalization of Theorem 7 (`thm:bounds-xnorm`), the Remark following it, Theorem 8
(`thm:state-gap-aware`) and Corollary 9 (`cor:conservative-limit2`) of

> S. Deng, B. Liao, Z. Ouyang, T. Pang, M. Song, Y. Yang,
> *Suspicious Alignment of SGD: A Fine-Grained Step Size Condition Analysis* (arXiv:2601.11789v2),

tex lines 490–523 (statements) and 1363–1456 (proofs).

Throughout, `η*_t = -q_t / p_t` (`Spec.etaStar`), where `q_t ≤ 0` always and the sign of `p_t`
is state dependent.  `η*_t` is the positive root of `𝔼[f_t(η)|x_t] = p_t η² + q_t η` only when
`p_t > 0`; for `p_t < 0` the quotient is *negative*.  Every bound below therefore carries the
hypothesis `0 < p_t` explicitly.

## Summary of what is proved (see `notes/fidelity/EtaStarBounds.md`)

* **Theorem 7** (`Spec.etaStar_ge_gap_bound`): if `p_t > 0` and `θ_t > 0` then
  `η* ≥ 2 gap₁ / ((λ₁² - λ_d²) + s_max ψ_𝒟 / (λ_d² ‖x‖² θ))`.  The paper states this "for any
  `x_t`"; it is false when `p_t < 0` (`EtaStarBounds.thm7_fails_of_pCoef_neg`).  A formulation that
  needs no sign condition on `p_t` is `Spec.quad_neg_of_lt_gap_bound`: every step size below the
  bound lies in the decrease regime `p_t η² + q_t η < 0`.
* **Remark after Theorem 7**: `θ ≥ λ_k² ‖P^𝒟 x‖² / (λ₁² ‖x‖²)` holds with `≥`
  (`Spec.normSqD_ratio_le_theta`), and the strict inequality claimed in the paper holds iff
  `P^𝒟 x ≠ 0 ∧ (P^ℬ x ≠ 0 ∨ λ_k < λ₁)` (`Spec.normSqD_ratio_lt_theta_iff`).  The resulting bound
  is `Spec.etaStar_ge_gap_bound_normSqD`; a sharper one is `Spec.etaStar_ge_gap_bound_normSqD_sharp`.
* **Theorem 8** is false as stated (wrong direction of the alignment hypothesis, lost factor `2`,
  invalid lower bound on `p_t`): `EtaStarBounds.thm8_cor9_fail`,
  `EtaStarBounds.thm8_hypothesis_gives_no_upper_bound`.  The corrected statement, under
  `s^𝒟 e_ℬ ≤ s^ℬ e_𝒟` (i.e. `θ ≤ e_𝒟 / (e_ℬ + e_𝒟)`), is
  `η* ≤ 2 / (λ_k + λ_d) ≤ 2 (λ₁ - λ_d) / (λ_k λ₁ - λ_{k+1} λ_d)`
  (`Spec.etaStar_le_two_div_lamk_add_lamd`, `Spec.etaStar_le_two_mul_gap_ratio`).
* **Corollary 9** is false as stated, even under the corrected hypothesis of Theorem 8
  (`EtaStarBounds.cor9_fails_under_corrected_hypothesis`); it holds under the extra spectral
  condition `λ₁ ≤ λ_k + λ_d` (`Spec.etaStar_le_two_div_lam1`).
-/

set_option linter.unusedSectionVars false

open Finset

namespace SuspiciousAlignment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace EtaStarBounds

/-! ### Two elementary facts about real numbers -/

/-- Monotone transfer of a lower bound: from `2 g u ≤ E (A u + C)` and `0 < t ≤ u` one gets
`2 g / (A + C / t) ≤ E`. -/
theorem two_mul_div_le {g A C E u t : ℝ} (hg : 0 ≤ g) (hA : 0 < A) (hC : 0 ≤ C) (ht : 0 < t)
    (htu : t ≤ u) (h : 2 * g * u ≤ E * (A * u + C)) : 2 * g / (A + C / t) ≤ E := by
  have hu : 0 < u := lt_of_lt_of_le ht htu
  have hAu : 0 < A * u + C := add_pos_of_pos_of_nonneg (mul_pos hA hu) hC
  have hE : 0 ≤ E := by
    by_contra hE
    have h1 : E * (A * u + C) < 0 := mul_neg_of_neg_of_pos (not_le.mp hE) hAu
    have h2 : 0 ≤ 2 * g * u := mul_nonneg (mul_nonneg zero_le_two hg) hu.le
    linarith
  have hden : 0 < A + C / t := add_pos_of_pos_of_nonneg hA (div_nonneg hC ht.le)
  rw [div_le_iff₀ hden]
  have h1 : C / u ≤ C / t := div_le_div_of_nonneg_left hC ht htu
  have h2 : E * (A + C / u) ≤ E * (A + C / t) :=
    mul_le_mul_of_nonneg_left (by linarith) hE
  have h3 : E * (A + C / u) = E * (A * u + C) / u := by
    field_simp
  have h4 : 2 * g ≤ E * (A * u + C) / u := by
    rw [le_div_iff₀ hu]
    exact h
  linarith

/-- Division-free transfer: from `2 g u ≤ E (A u + C)`, `E, C ≥ 0` and `0 ≤ t ≤ u` one gets
`2 g t ≤ E (A t + C)`. -/
theorem two_mul_le_of_le {g A C E u t : ℝ} (hE : 0 ≤ E) (hC : 0 ≤ C) (ht : 0 ≤ t) (htu : t ≤ u)
    (h : 2 * g * u ≤ E * (A * u + C)) : 2 * g * t ≤ E * (A * t + C) := by
  rcases (le_trans ht htu).eq_or_lt with hu | hu
  · have ht0 : t = 0 := le_antisymm (hu ▸ htu) ht
    rw [ht0]
    have : 0 ≤ E * C := mul_nonneg hE hC
    simpa using this
  · have h1 : 0 ≤ t * (E * (A * u + C) - 2 * g * u) := mul_nonneg ht (sub_nonneg.mpr h)
    have h2 : 0 ≤ (u - t) * (E * C) := mul_nonneg (sub_nonneg.mpr htu) (mul_nonneg hE hC)
    have h3 : u * (2 * g * t) ≤ u * (E * (A * t + C)) := by nlinarith
    exact le_of_mul_le_mul_left h3 hu

variable (P : Spec ι) (N : Noise ι)

/-! ### Block inequalities for the weighted moments -/

/-- If `λ_i ≤ b` on the block `S` then `∑_S λ^{p+1} c² ≤ b ∑_S λ^p c²`. -/
theorem mom_succ_le {S : Finset ι} {b : ℝ} (hb : ∀ i ∈ S, P.lam i ≤ b) (p : ℕ) (c : ι → ℝ) :
    P.mom S (p + 1) c ≤ b * P.mom S p c := by
  unfold Spec.mom
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have h2 : 0 ≤ P.lam i ^ p * c i ^ 2 :=
    mul_nonneg (pow_nonneg (P.lam_pos i).le _) (sq_nonneg _)
  calc P.lam i ^ (p + 1) * c i ^ 2 = P.lam i * (P.lam i ^ p * c i ^ 2) := by ring
    _ ≤ b * (P.lam i ^ p * c i ^ 2) := mul_le_mul_of_nonneg_right (hb i hi) h2

/-- If `a ≤ λ_i` on the block `S` then `a ∑_S λ^p c² ≤ ∑_S λ^{p+1} c²`. -/
theorem le_mom_succ {S : Finset ι} {a : ℝ} (ha : ∀ i ∈ S, a ≤ P.lam i) (p : ℕ) (c : ι → ℝ) :
    a * P.mom S p c ≤ P.mom S (p + 1) c := by
  unfold Spec.mom
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have h2 : 0 ≤ P.lam i ^ p * c i ^ 2 :=
    mul_nonneg (pow_nonneg (P.lam_pos i).le _) (sq_nonneg _)
  calc a * (P.lam i ^ p * c i ^ 2) ≤ P.lam i * (P.lam i ^ p * c i ^ 2) :=
        mul_le_mul_of_nonneg_right (ha i hi) h2
    _ = P.lam i ^ (p + 1) * c i ^ 2 := by ring

/-- `λ_k s^𝒟 ≤ τ^𝒟 = ∑_𝒟 λ³ c²`. -/
theorem le_tauD (c : ι → ℝ) : P.lamk * P.sD c ≤ P.tauD c :=
  le_mom_succ P (fun _ hi => P.lamk_le_of_mem hi) 2 c

/-- `τ^𝒟 ≤ λ_1 s^𝒟`. -/
theorem tauD_le (c : ι → ℝ) : P.tauD c ≤ P.lam1 * P.sD c :=
  mom_succ_le P (fun _ hi => P.le_lam1_of_mem hi) 2 c

/-- `τ^ℬ = ∑_ℬ λ³ c² ≤ λ_{k+1} s^ℬ`. -/
theorem tauB_le (c : ι → ℝ) : P.tauB c ≤ P.lamk1 * P.sB c :=
  mom_succ_le P (fun _ hi => P.le_lamk1_of_mem_B hi) 2 c

/-- `λ_d s^ℬ ≤ τ^ℬ`. -/
theorem le_tauB (c : ι → ℝ) : P.lamd * P.sB c ≤ P.tauB c :=
  le_mom_succ P (fun _ hi => P.lamd_le_of_mem_B hi) 2 c

/-- `∑_𝒟 λ⁴ c² ≤ λ_1² s^𝒟`. -/
theorem mom4D_le (c : ι → ℝ) : P.mom P.D 4 c ≤ P.lam1 ^ 2 * P.sD c :=
  calc P.mom P.D 4 c ≤ P.lam1 * P.mom P.D 3 c :=
        mom_succ_le P (fun _ hi => P.le_lam1_of_mem hi) 3 c
    _ ≤ P.lam1 * (P.lam1 * P.sD c) := mul_le_mul_of_nonneg_left (tauD_le P c) P.lam1_pos.le
    _ = P.lam1 ^ 2 * P.sD c := by ring

/-- `λ_k² s^𝒟 ≤ ∑_𝒟 λ⁴ c²`. -/
theorem le_mom4D (c : ι → ℝ) : P.lamk ^ 2 * P.sD c ≤ P.mom P.D 4 c :=
  calc P.lamk ^ 2 * P.sD c = P.lamk * (P.lamk * P.sD c) := by ring
    _ ≤ P.lamk * P.mom P.D 3 c := mul_le_mul_of_nonneg_left (le_tauD P c) P.lamk_pos.le
    _ ≤ P.mom P.D 4 c := le_mom_succ P (fun _ hi => P.lamk_le_of_mem hi) 3 c

/-- `∑_ℬ λ⁴ c² ≤ λ_{k+1}² s^ℬ`. -/
theorem mom4B_le (c : ι → ℝ) : P.mom P.B 4 c ≤ P.lamk1 ^ 2 * P.sB c :=
  calc P.mom P.B 4 c ≤ P.lamk1 * P.mom P.B 3 c :=
        mom_succ_le P (fun _ hi => P.le_lamk1_of_mem_B hi) 3 c
    _ ≤ P.lamk1 * (P.lamk1 * P.sB c) := mul_le_mul_of_nonneg_left (tauB_le P c) P.lamk1_pos.le
    _ = P.lamk1 ^ 2 * P.sB c := by ring

/-- `λ_d² s^ℬ ≤ ∑_ℬ λ⁴ c²`. -/
theorem le_mom4B (c : ι → ℝ) : P.lamd ^ 2 * P.sB c ≤ P.mom P.B 4 c :=
  calc P.lamd ^ 2 * P.sB c = P.lamd * (P.lamd * P.sB c) := by ring
    _ ≤ P.lamd * P.mom P.B 3 c := mul_le_mul_of_nonneg_left (le_tauB P c) P.lamd_pos.le
    _ ≤ P.mom P.B 4 c := le_mom_succ P (fun _ hi => P.lamd_le_of_mem_B hi) 3 c

/-! ### Energies versus Euclidean norms -/

/-- If `0 ≤ a ≤ λ_i` on `S` then `a² ∑_S c² ≤ ∑_S λ² c²`. -/
theorem sq_mul_sum_le_mom {S : Finset ι} {a : ℝ} (ha0 : 0 ≤ a) (ha : ∀ i ∈ S, a ≤ P.lam i)
    (c : ι → ℝ) : a ^ 2 * ∑ i ∈ S, c i ^ 2 ≤ P.mom S 2 c := by
  unfold Spec.mom
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi =>
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha0 (ha i hi) 2) (sq_nonneg _)

/-- If `λ_i ≤ b` on `S` then `∑_S λ² c² ≤ b² ∑_S c²`. -/
theorem mom_le_sq_mul_sum {S : Finset ι} {b : ℝ} (hb : ∀ i ∈ S, P.lam i ≤ b) (c : ι → ℝ) :
    P.mom S 2 c ≤ b ^ 2 * ∑ i ∈ S, c i ^ 2 := by
  unfold Spec.mom
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi =>
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (P.lam_pos i).le (hb i hi) 2) (sq_nonneg _)

/-- `‖x‖² = ‖P^𝒟 x‖² + ‖P^ℬ x‖²`. -/
theorem normSq_eq (c : ι → ℝ) : Spec.normSq c = P.normSqD c + ∑ i ∈ P.B, c i ^ 2 :=
  (P.sum_D_add_sum_B fun i => c i ^ 2).symm

theorem normSqD_nonneg (c : ι → ℝ) : 0 ≤ P.normSqD c :=
  Finset.sum_nonneg fun i _ => sq_nonneg (c i)

theorem normSq_nonneg (c : ι → ℝ) : 0 ≤ Spec.normSq c :=
  Finset.sum_nonneg fun i _ => sq_nonneg (c i)

theorem normSqB_nonneg (c : ι → ℝ) : 0 ≤ ∑ i ∈ P.B, c i ^ 2 :=
  Finset.sum_nonneg fun i _ => sq_nonneg (c i)

/-- `‖P^𝒟 x‖² ≤ ‖x‖²`. -/
theorem normSqD_le_normSq (c : ι → ℝ) : P.normSqD c ≤ Spec.normSq c := by
  rw [normSq_eq]
  linarith [normSqB_nonneg P c]

/-- `λ_d² ‖x‖² ≤ s = ‖A x‖²` (the step "using `s_t ≥ λ_d² ‖x_t‖²`" in the proof of Theorem 7). -/
theorem lamd_sq_mul_normSq_le_s (c : ι → ℝ) : P.lamd ^ 2 * Spec.normSq c ≤ P.s c := by
  rw [P.s_eq_sum]
  exact sq_mul_sum_le_mom P P.lamd_pos.le (fun i _ => P.lamd_le_all i) c

/-- `s = ‖A x‖² ≤ λ_1² ‖x‖²`. -/
theorem s_le_lam1_sq_mul_normSq (c : ι → ℝ) : P.s c ≤ P.lam1 ^ 2 * Spec.normSq c := by
  rw [P.s_eq_sum]
  exact mom_le_sq_mul_sum P (fun i _ => P.le_lam1_all i) c

/-- `λ_k² ‖P^𝒟 x‖² ≤ s^𝒟`. -/
theorem lamk_sq_mul_normSqD_le_sD (c : ι → ℝ) : P.lamk ^ 2 * P.normSqD c ≤ P.sD c :=
  sq_mul_sum_le_mom P P.lamk_pos.le (fun _ hi => P.lamk_le_of_mem hi) c

/-- `s^𝒟 ≤ λ_1² ‖P^𝒟 x‖²`. -/
theorem sD_le_lam1_sq_mul_normSqD (c : ι → ℝ) : P.sD c ≤ P.lam1 ^ 2 * P.normSqD c :=
  mom_le_sq_mul_sum P (fun _ hi => P.le_lam1_of_mem hi) c

/-- `s^ℬ ≤ λ_{k+1}² ‖P^ℬ x‖²`. -/
theorem sB_le_lamk1_sq_mul (c : ι → ℝ) : P.sB c ≤ P.lamk1 ^ 2 * ∑ i ∈ P.B, c i ^ 2 :=
  mom_le_sq_mul_sum P (fun _ hi => P.le_lamk1_of_mem_B hi) c

/-- `λ_d² ‖P^ℬ x‖² ≤ s^ℬ`. -/
theorem lamd_sq_mul_le_sB (c : ι → ℝ) : P.lamd ^ 2 * ∑ i ∈ P.B, c i ^ 2 ≤ P.sB c :=
  sq_mul_sum_le_mom P P.lamd_pos.le (fun _ hi => P.lamd_le_of_mem_B hi) c

/-- `s^𝒟 > 0` iff `P^𝒟 x ≠ 0`. -/
theorem sD_pos_iff_normSqD_pos (c : ι → ℝ) : 0 < P.sD c ↔ 0 < P.normSqD c := by
  constructor
  · intro h
    by_contra hn
    have h0 : P.normSqD c = 0 := le_antisymm (not_lt.mp hn) (normSqD_nonneg P c)
    have h1 := sD_le_lam1_sq_mul_normSqD P c
    rw [h0, mul_zero] at h1
    linarith
  · intro h
    have h1 := lamk_sq_mul_normSqD_le_sD P c
    have h2 : 0 < P.lamk ^ 2 * P.normSqD c := mul_pos (pow_pos P.lamk_pos 2) h
    linarith

/-- `s^ℬ > 0` iff `P^ℬ x ≠ 0`. -/
theorem sB_pos_iff_normSqB_pos (c : ι → ℝ) : 0 < P.sB c ↔ 0 < ∑ i ∈ P.B, c i ^ 2 := by
  constructor
  · intro h
    by_contra hn
    have h0 : ∑ i ∈ P.B, c i ^ 2 = 0 := le_antisymm (not_lt.mp hn) (normSqB_nonneg P c)
    have h1 := sB_le_lamk1_sq_mul P c
    rw [h0, mul_zero] at h1
    linarith
  · intro h
    have h1 := lamd_sq_mul_le_sB P c
    have h2 : 0 < P.lamd ^ 2 * ∑ i ∈ P.B, c i ^ 2 := mul_pos (pow_pos P.lamd_pos 2) h
    linarith

/-- `θ > 0` iff `s^𝒟 > 0`. -/
theorem theta_pos_iff_sD_pos (c : ι → ℝ) : 0 < P.theta c ↔ 0 < P.sD c := by
  constructor
  · intro h
    have hs : P.s c ≠ 0 := by
      intro h0
      unfold Spec.theta at h
      rw [h0, div_zero] at h
      exact lt_irrefl _ h
    have hs' : 0 < P.s c := lt_of_le_of_ne (P.s_nonneg c) (Ne.symm hs)
    rw [P.sD_eq_theta_mul_s]
    exact mul_pos h hs'
  · intro h
    have hs : 0 < P.s c := by
      unfold Spec.s
      linarith [P.sB_nonneg c]
    exact div_pos h hs

/-! ### Spectral constants -/

theorem lam1_sq_sub_lamd_sq_pos : 0 < P.lam1 ^ 2 - P.lamd ^ 2 := by
  have h1 := P.lamd_lt_lam1
  have h2 := P.lamd_pos
  nlinarith

theorem lamk_lam1_sub_pos : 0 < P.lamk * P.lam1 - P.lamk1 * P.lamd := by
  have h1 := mul_lt_mul_of_pos_right P.lamk1_lt_lamk P.lam1_pos
  have h2 := mul_le_mul_of_nonneg_left P.lamd_lt_lam1.le P.lamk1_pos.le
  linarith

theorem smax_psiD_nonneg : 0 ≤ N.smax * P.psiD := by
  have : Nonempty ι := ⟨P.i1⟩
  exact mul_nonneg (Spec.smax_nonneg N) P.psiD_pos.le

/-! ### Bounds on `q_t` and `p_t` -/

/-- Paper eq. (`eq:q-sign`): `-q_t ≥ 2 s^ℬ s^𝒟 gap₁ = 2 s² θ (1 - θ) gap₁`. -/
theorem neg_qCoef_ge (c : ι → ℝ) : 2 * P.sB c * P.sD c * P.gap1 ≤ -P.qCoef c := by
  have h1 := mul_le_mul_of_nonneg_left (le_tauD P c) (P.sB_nonneg c)
  have h2 := mul_le_mul_of_nonneg_left (tauB_le P c) (P.sD_nonneg c)
  unfold Spec.qCoef Spec.gap1
  linarith

/-- `q_t ≤ 0`. -/
theorem qCoef_nonpos' (c : ι → ℝ) : P.qCoef c ≤ 0 := by
  have h := neg_qCoef_ge P c
  have h0 : 0 ≤ 2 * P.sB c * P.sD c * P.gap1 :=
    mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (P.sB_nonneg c)) (P.sD_nonneg c))
      P.gap1_pos.le
  linarith

/-- `q_t < 0` when both blocks carry energy (`0 < θ < 1`). -/
theorem qCoef_neg' {c : ι → ℝ} (hD : 0 < P.sD c) (hB : 0 < P.sB c) : P.qCoef c < 0 := by
  have h := neg_qCoef_ge P c
  have h0 : 0 < 2 * P.sB c * P.sD c * P.gap1 :=
    mul_pos (mul_pos (mul_pos zero_lt_two hB) hD) P.gap1_pos
  linarith

/-- The upper bound on `-q_t` in the paper's proof of Theorem 8 — with the factor `2` that the
paper drops: `-q_t ≤ 2 (λ_1 - λ_d) s^𝒟 s^ℬ`. -/
theorem neg_qCoef_le (c : ι → ℝ) : -P.qCoef c ≤ 2 * (P.lam1 - P.lamd) * (P.sD c * P.sB c) := by
  have h1 := mul_le_mul_of_nonneg_left (tauD_le P c) (P.sB_nonneg c)
  have h2 := mul_le_mul_of_nonneg_left (le_tauB P c) (P.sD_nonneg c)
  unfold Spec.qCoef
  linarith

/-- `p_t` splits into a signal part and a noise part. -/
theorem pCoef_eq_signal_add_noise (c : ι → ℝ) :
    P.pCoef N c = (P.sB c * P.mom P.D 4 c - P.sD c * P.mom P.B 4 c) +
      (P.sB c * P.eD N - P.sD c * P.eB N) := by
  unfold Spec.pCoef
  ring

/-- Paper eq. (`eqptupbound`):
`p_t ≤ s^ℬ s^𝒟 (λ_1² - λ_d²) + s^ℬ s_max ψ_𝒟 - s^𝒟 s_min ψ_ℬ`. -/
theorem pCoef_le (c : ι → ℝ) :
    P.pCoef N c ≤ P.sB c * P.sD c * (P.lam1 ^ 2 - P.lamd ^ 2) +
      (P.sB c * (N.smax * P.psiD) - P.sD c * (N.smin * P.psiB)) := by
  have h1 := mul_le_mul_of_nonneg_left (mom4D_le P c) (P.sB_nonneg c)
  have h2 := mul_le_mul_of_nonneg_left (le_mom4B P c) (P.sD_nonneg c)
  have h3 := mul_le_mul_of_nonneg_left (P.eD_le_smax_psiD N) (P.sB_nonneg c)
  have h4 := mul_le_mul_of_nonneg_left (P.smin_psiB_le_eB N) (P.sD_nonneg c)
  unfold Spec.pCoef
  linarith

/-- The form of the upper bound used for Theorem 7:
`p_t ≤ s^ℬ ((λ_1² - λ_d²) s^𝒟 + s_max ψ_𝒟)`. -/
theorem pCoef_le_sB_mul (c : ι → ℝ) :
    P.pCoef N c ≤ P.sB c * ((P.lam1 ^ 2 - P.lamd ^ 2) * P.sD c + N.smax * P.psiD) := by
  have h := pCoef_le P N c
  have h5 : 0 ≤ P.sD c * (N.smin * P.psiB) :=
    mul_nonneg (P.sD_nonneg c) (mul_nonneg N.smin_nonneg P.psiB_pos.le)
  linarith

/-- If `p_t > 0` then the bulk carries energy: `s^ℬ > 0` (i.e. `θ < 1`). -/
theorem sB_pos_of_pCoef_pos {c : ι → ℝ} (hp : 0 < P.pCoef N c) : 0 < P.sB c := by
  by_contra h
  have h0 : P.sB c = 0 := le_antisymm (not_lt.mp h) (P.sB_nonneg c)
  have h1 := pCoef_le_sB_mul P N c
  rw [h0, zero_mul] at h1
  linarith

/-- `η* ≥ 0` when `p_t > 0`. -/
theorem etaStar_nonneg' {c : ι → ℝ} (hp : 0 < P.pCoef N c) : 0 ≤ P.etaStar N c :=
  div_nonneg (neg_nonneg.mpr (qCoef_nonpos' P c)) hp.le

/-- Core of Theorem 7 in division-free form: if `p_t > 0` then
`2 gap₁ s^𝒟 ≤ η* ((λ_1² - λ_d²) s^𝒟 + s_max ψ_𝒟)`. -/
theorem etaStar_mul_ge {c : ι → ℝ} (hp : 0 < P.pCoef N c) :
    2 * P.gap1 * P.sD c ≤
      P.etaStar N c * ((P.lam1 ^ 2 - P.lamd ^ 2) * P.sD c + N.smax * P.psiD) := by
  have hX0 : 0 ≤ (P.lam1 ^ 2 - P.lamd ^ 2) * P.sD c + N.smax * P.psiD :=
    add_nonneg (mul_nonneg (lam1_sq_sub_lamd_sq_pos P).le (P.sD_nonneg c))
      (smax_psiD_nonneg P N)
  have hq := neg_qCoef_ge P c
  have hpu := pCoef_le_sB_mul P N c
  have hg : 0 ≤ 2 * P.gap1 * P.sD c :=
    mul_nonneg (mul_nonneg zero_le_two P.gap1_pos.le) (P.sD_nonneg c)
  have key : 2 * P.gap1 * P.sD c * P.pCoef N c ≤
      -P.qCoef c * ((P.lam1 ^ 2 - P.lamd ^ 2) * P.sD c + N.smax * P.psiD) :=
    calc 2 * P.gap1 * P.sD c * P.pCoef N c
        ≤ 2 * P.gap1 * P.sD c *
            (P.sB c * ((P.lam1 ^ 2 - P.lamd ^ 2) * P.sD c + N.smax * P.psiD)) :=
          mul_le_mul_of_nonneg_left hpu hg
      _ = (2 * P.sB c * P.sD c * P.gap1) *
            ((P.lam1 ^ 2 - P.lamd ^ 2) * P.sD c + N.smax * P.psiD) := by ring
      _ ≤ -P.qCoef c * ((P.lam1 ^ 2 - P.lamd ^ 2) * P.sD c + N.smax * P.psiD) :=
          mul_le_mul_of_nonneg_right hq hX0
  unfold Spec.etaStar
  rw [div_mul_eq_mul_div, le_div_iff₀ hp]
  exact key

/-- Master lower bound: if `p_t > 0` and `0 < t ≤ s^𝒟` then
`η* ≥ 2 gap₁ / ((λ_1² - λ_d²) + s_max ψ_𝒟 / t)`.  Theorem 7 and the bounds of the Remark after it
are the instances `t = λ_d² ‖x‖² θ`, `t = λ_k² ‖P^𝒟 x‖²` and `t = λ_k² λ_d² ‖P^𝒟 x‖² / λ_1²`. -/
theorem etaStar_ge_of_le_sD {c : ι → ℝ} (hp : 0 < P.pCoef N c) {t : ℝ} (ht : 0 < t)
    (htD : t ≤ P.sD c) :
    2 * P.gap1 / ((P.lam1 ^ 2 - P.lamd ^ 2) + N.smax * P.psiD / t) ≤ P.etaStar N c :=
  two_mul_div_le P.gap1_pos.le (lam1_sq_sub_lamd_sq_pos P) (smax_psiD_nonneg P N) ht htD
    (etaStar_mul_ge P N hp)

/-! ### The signal part of `p_t` versus `-q_t` (for Theorem 8) -/

/-- `∑_S λ⁴c² - (a + b) ∑_S λ³c² + a b ∑_S λ²c² = ∑_S λ² c² (λ - a)(λ - b)`. -/
theorem mom_quad_eq (S : Finset ι) (a b : ℝ) (c : ι → ℝ) :
    P.mom S 4 c - (a + b) * P.mom S 3 c + a * b * P.mom S 2 c =
      ∑ i ∈ S, P.lam i ^ 2 * c i ^ 2 * ((P.lam i - a) * (P.lam i - b)) := by
  unfold Spec.mom
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- On the dominant block `(λ_i - λ_k)(λ_i - λ_d) ≥ 0`. -/
theorem mom_quad_D_nonneg (c : ι → ℝ) :
    0 ≤ P.mom P.D 4 c - (P.lamk + P.lamd) * P.tauD c + P.lamk * P.lamd * P.sD c := by
  show 0 ≤ P.mom P.D 4 c - (P.lamk + P.lamd) * P.mom P.D 3 c + P.lamk * P.lamd * P.mom P.D 2 c
  rw [mom_quad_eq]
  refine Finset.sum_nonneg fun i hi => ?_
  have h1 : 0 ≤ P.lam i - P.lamk := sub_nonneg.mpr (P.lamk_le_of_mem hi)
  have h2 : 0 ≤ P.lam i - P.lamd := sub_nonneg.mpr (P.lamd_le_all i)
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (mul_nonneg h1 h2)

/-- On the bulk block `(λ_i - λ_k)(λ_i - λ_d) ≤ 0`. -/
theorem mom_quad_B_nonpos (c : ι → ℝ) :
    P.mom P.B 4 c - (P.lamk + P.lamd) * P.tauB c + P.lamk * P.lamd * P.sB c ≤ 0 := by
  show P.mom P.B 4 c - (P.lamk + P.lamd) * P.mom P.B 3 c + P.lamk * P.lamd * P.mom P.B 2 c ≤ 0
  rw [mom_quad_eq]
  refine Finset.sum_nonpos fun i hi => ?_
  have h1 : P.lam i - P.lamk ≤ 0 :=
    sub_nonpos.mpr (le_trans (P.le_lamk1_of_mem_B hi) P.lamk1_lt_lamk.le)
  have h2 : 0 ≤ P.lam i - P.lamd := sub_nonneg.mpr (P.lamd_le_all i)
  exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (mul_nonpos_of_nonpos_of_nonneg h1 h2)

/-- The key (correct) inequality behind the upper bound on `η*`:
`(λ_k + λ_d) (s^ℬ τ^𝒟 - s^𝒟 τ^ℬ) ≤ s^ℬ ∑_𝒟 λ⁴c² - s^𝒟 ∑_ℬ λ⁴c²`.
(Pairwise: `(λ_k + λ_d)(λ_j - λ_i) ≤ λ_j² - λ_i²` for `j ∈ 𝒟`, `i ∈ ℬ`.) -/
theorem lam_add_mul_le_signal (c : ι → ℝ) :
    (P.lamk + P.lamd) * (P.sB c * P.tauD c - P.sD c * P.tauB c) ≤
      P.sB c * P.mom P.D 4 c - P.sD c * P.mom P.B 4 c := by
  have h1 := mul_nonneg (P.sB_nonneg c) (mom_quad_D_nonneg P c)
  have h2 := mul_nonpos_of_nonneg_of_nonpos (P.sD_nonneg c) (mom_quad_B_nonpos P c)
  linarith

/-- Paper eq. (`eq:ptc-lb-app`): the signal part of `p_t` is at least `gap₂ s^𝒟 s^ℬ`.  (The proof
of Theorem 8 in the paper claims the larger constant `λ_k λ_1 - λ_{k+1} λ_d`, which is false.) -/
theorem gap2_mul_le_signal (c : ι → ℝ) :
    P.gap2 * (P.sD c * P.sB c) ≤ P.sB c * P.mom P.D 4 c - P.sD c * P.mom P.B 4 c := by
  have h1 := mul_le_mul_of_nonneg_left (le_mom4D P c) (P.sB_nonneg c)
  have h2 := mul_le_mul_of_nonneg_left (mom4B_le P c) (P.sD_nonneg c)
  unfold Spec.gap2
  linarith

/-- `2 / (λ_k + λ_d) ≤ 2 (λ_1 - λ_d) / (λ_k λ_1 - λ_{k+1} λ_d)`: the sharp bound is at most the
bound appearing in (the appendix version of) Theorem 8. -/
theorem two_div_le_two_mul_ratio :
    2 / (P.lamk + P.lamd) ≤ 2 * (P.lam1 - P.lamd) / (P.lamk * P.lam1 - P.lamk1 * P.lamd) := by
  rw [div_le_div_iff₀ (add_pos P.lamk_pos P.lamd_pos) (lamk_lam1_sub_pos P)]
  have h : 0 ≤ P.lamd * (P.lam1 - P.lamk + P.lamk1 - P.lamd) :=
    mul_nonneg P.lamd_pos.le (by linarith [P.lamk_le_lam1, P.lamd_le_lamk1])
  linarith

/-- The inequality `(λ_1 - λ_d)/(λ_k λ_1 - λ_{k+1} λ_d) ≤ 1/λ_1` asserted in the paper's proof of
Corollary 9 is equivalent to `λ_1 (λ_1 - λ_k) ≤ λ_d (λ_1 - λ_{k+1})`, which is *not* implied by
the ordering of the eigenvalues (it fails e.g. for `λ = (10, 2, 1)`, `k = 2`). -/
theorem ratio_le_one_div_lam1_iff :
    (P.lam1 - P.lamd) / (P.lamk * P.lam1 - P.lamk1 * P.lamd) ≤ 1 / P.lam1 ↔
      P.lam1 * (P.lam1 - P.lamk) ≤ P.lamd * (P.lam1 - P.lamk1) := by
  rw [div_le_div_iff₀ (lamk_lam1_sub_pos P) P.lam1_pos]
  constructor <;> intro h <;> linarith

end EtaStarBounds

namespace Spec

open EtaStarBounds

variable (P : Spec ι) (N : Noise ι)

/-! ### Theorem 7 -/

/-- **Theorem 7, intermediate form of the paper's proof** (tex l. 1381–1384): if `p_t > 0` and
`θ_t > 0` then `η* ≥ 2 gap₁ / ((λ_1² - λ_d²) + s_max ψ_𝒟 / (s_t θ_t))`. -/
theorem etaStar_ge_gap_bound_s {c : ι → ℝ} (hp : 0 < P.pCoef N c) (hθ : 0 < P.theta c) :
    2 * P.gap1 / ((P.lam1 ^ 2 - P.lamd ^ 2) + N.smax * P.psiD / (P.s c * P.theta c)) ≤
      P.etaStar N c := by
  have hD : 0 < P.sD c := (theta_pos_iff_sD_pos P c).mp hθ
  have h : P.s c * P.theta c = P.sD c := by rw [P.sD_eq_theta_mul_s c, mul_comm]
  rw [h]
  exact etaStar_ge_of_le_sD P N hp hD le_rfl

/-- **Theorem 7** (`thm:bounds-xnorm`, state- and gap-aware lower bound on `η*_t`): if `p_t > 0`
and `θ_t > 0`, then
`η*_t ≥ 2 gap₁ / ((λ_1² - λ_d²) + s_max ψ_𝒟 / (λ_d² ‖x_t‖² θ_t))`.

The paper asserts this "for any `x_t`".  The hypothesis `p_t > 0` cannot be dropped
(`EtaStarBounds.thm7_fails_of_pCoef_neg`); `θ_t > 0` is only needed to give the right-hand side
its intended meaning (for `θ_t = 0` the paper's right-hand side is "`2 gap₁ / ∞ = 0`", see
`Spec.etaStar_mul_ge_gap` for a division-free form covering that case). -/
theorem etaStar_ge_gap_bound {c : ι → ℝ} (hp : 0 < P.pCoef N c) (hθ : 0 < P.theta c) :
    2 * P.gap1 /
        ((P.lam1 ^ 2 - P.lamd ^ 2) +
          N.smax * P.psiD / (P.lamd ^ 2 * Spec.normSq c * P.theta c)) ≤
      P.etaStar N c := by
  have hD : 0 < P.sD c := (theta_pos_iff_sD_pos P c).mp hθ
  have hn : 0 < Spec.normSq c :=
    lt_of_lt_of_le ((sD_pos_iff_normSqD_pos P c).mp hD) (normSqD_le_normSq P c)
  refine etaStar_ge_of_le_sD P N hp (mul_pos (mul_pos (pow_pos P.lamd_pos 2) hn) hθ) ?_
  calc P.lamd ^ 2 * Spec.normSq c * P.theta c ≤ P.s c * P.theta c :=
        mul_le_mul_of_nonneg_right (lamd_sq_mul_normSq_le_s P c) hθ.le
    _ = P.sD c := by rw [P.sD_eq_theta_mul_s c, mul_comm]

/-- **Theorem 7, division-free form** (valid also for `θ_t = 0`): if `p_t > 0` then, with
`T = λ_d² ‖x_t‖² θ_t`, `2 gap₁ T ≤ η*_t ((λ_1² - λ_d²) T + s_max ψ_𝒟)`. -/
theorem etaStar_mul_ge_gap {c : ι → ℝ} (hp : 0 < P.pCoef N c) :
    2 * P.gap1 * (P.lamd ^ 2 * Spec.normSq c * P.theta c) ≤
      P.etaStar N c *
        ((P.lam1 ^ 2 - P.lamd ^ 2) * (P.lamd ^ 2 * Spec.normSq c * P.theta c) +
          N.smax * P.psiD) := by
  refine two_mul_le_of_le (etaStar_nonneg' P N hp) (smax_psiD_nonneg P N)
    (mul_nonneg (mul_nonneg (sq_nonneg _) (normSq_nonneg c)) (P.theta_nonneg c)) ?_
    (etaStar_mul_ge P N hp)
  calc P.lamd ^ 2 * Spec.normSq c * P.theta c ≤ P.s c * P.theta c :=
        mul_le_mul_of_nonneg_right (lamd_sq_mul_normSq_le_s P c) (P.theta_nonneg c)
    _ = P.sD c := by rw [P.sD_eq_theta_mul_s c, mul_comm]

/-- **Theorem 7, sign-free semantic form.**  For *every* state with `0 < θ_t < 1` (no assumption
on the sign of `p_t`), every step size `0 < η` below the bound of Theorem 7 lies in the decrease
regime: `𝔼[f_t(η) | x_t] = p_t η² + q_t η < 0`.  This is the sense in which the paper's "for any
`x_t`" is correct (reading `η*_t = +∞` when `p_t ≤ 0`). -/
theorem quad_neg_of_lt_gap_bound {c : ι → ℝ} (hD : 0 < P.sD c) (hB : 0 < P.sB c) {η : ℝ}
    (hη : 0 < η)
    (hlt : η < 2 * P.gap1 /
        ((P.lam1 ^ 2 - P.lamd ^ 2) +
          N.smax * P.psiD / (P.lamd ^ 2 * Spec.normSq c * P.theta c))) :
    P.pCoef N c * η ^ 2 + P.qCoef c * η < 0 := by
  have hq : P.qCoef c < 0 := qCoef_neg' P hD hB
  rcases lt_or_ge 0 (P.pCoef N c) with hp | hp
  · have hθ : 0 < P.theta c := (theta_pos_iff_sD_pos P c).mpr hD
    have h1 : η < P.etaStar N c := lt_of_lt_of_le hlt (P.etaStar_ge_gap_bound N hp hθ)
    unfold Spec.etaStar at h1
    rw [lt_div_iff₀ hp] at h1
    have h2 : η * (η * P.pCoef N c + P.qCoef c) < 0 :=
      mul_neg_of_pos_of_neg hη (by linarith)
    nlinarith
  · have h1 : P.pCoef N c * η ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hp (sq_nonneg η)
    have h2 : P.qCoef c * η < 0 := mul_neg_of_neg_of_pos hq hη
    linarith

/-! ### The Remark after Theorem 7 -/

/-- **Remark after Theorem 7** (tex l. 503): `θ_t ≥ λ_k² ‖P^𝒟 x_t‖² / (λ_1² ‖x_t‖²)`, for every
state (including `x_t = 0`, where both sides are `0`).  The paper writes a strict inequality, which
is false in general; see `Spec.normSqD_ratio_lt_theta_iff` for exactly when it is strict. -/
theorem normSqD_ratio_le_theta (c : ι → ℝ) :
    P.lamk ^ 2 * P.normSqD c / (P.lam1 ^ 2 * Spec.normSq c) ≤ P.theta c := by
  rcases (P.s_nonneg c).eq_or_lt with hs | hs
  · have hc : c = 0 := (P.s_eq_zero_iff c).mp hs.symm
    subst hc
    simp [Spec.normSqD, Spec.normSq]
  · have hn : 0 < Spec.normSq c := by
      by_contra h
      have h1 := mul_nonpos_of_nonneg_of_nonpos (pow_pos P.lam1_pos 2).le (not_lt.mp h)
      have h2 := s_le_lam1_sq_mul_normSq P c
      linarith
    unfold Spec.theta
    rw [div_le_div_iff₀ (mul_pos (pow_pos P.lam1_pos 2) hn) hs]
    exact mul_le_mul (lamk_sq_mul_normSqD_le_sD P c) (s_le_lam1_sq_mul_normSq P c)
      (P.s_nonneg c) (P.sD_nonneg c)

/-- **Remark after Theorem 7, strictness.**  The strict inequality
`θ_t > λ_k² ‖P^𝒟 x_t‖² / (λ_1² ‖x_t‖²)` written in the paper holds iff `P^𝒟 x_t ≠ 0` and
(`P^ℬ x_t ≠ 0` or `λ_k < λ_1`).  In particular it fails when `P^𝒟 x_t = 0` (both sides `0`) and
when `x_t` lies in the dominant space and `λ_k = λ_1` (both sides `1`). -/
theorem normSqD_ratio_lt_theta_iff (c : ι → ℝ) :
    P.lamk ^ 2 * P.normSqD c / (P.lam1 ^ 2 * Spec.normSq c) < P.theta c ↔
      0 < P.normSqD c ∧ (0 < P.sB c ∨ P.lamk < P.lam1) := by
  constructor
  · intro h
    have hθ : 0 < P.theta c :=
      lt_of_le_of_lt (div_nonneg (mul_nonneg (sq_nonneg _) (normSqD_nonneg P c))
        (mul_nonneg (sq_nonneg _) (normSq_nonneg c))) h
    have hD : 0 < P.sD c := (theta_pos_iff_sD_pos P c).mp hθ
    have hnD : 0 < P.normSqD c := (sD_pos_iff_normSqD_pos P c).mp hD
    refine ⟨hnD, ?_⟩
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hB, hlam⟩ := hcon
    have hB0 : P.sB c = 0 := le_antisymm (not_lt.mp hB) (P.sB_nonneg c)
    have hlam' : P.lamk = P.lam1 := le_antisymm P.lamk_le_lam1 (not_lt.mp hlam)
    have hθ1 : P.theta c = 1 := by
      unfold Spec.theta Spec.s
      rw [hB0, add_zero]
      exact div_self hD.ne'
    have hnB : ∑ i ∈ P.B, c i ^ 2 = 0 := by
      by_contra hne
      have hpos : 0 < ∑ i ∈ P.B, c i ^ 2 := lt_of_le_of_ne (normSqB_nonneg P c) (Ne.symm hne)
      have := (sB_pos_iff_normSqB_pos P c).mpr hpos
      exact hB this
    have hn : Spec.normSq c = P.normSqD c := by rw [normSq_eq, hnB, add_zero]
    rw [hθ1, hn, hlam', div_self (mul_pos (pow_pos P.lam1_pos 2) hnD).ne'] at h
    exact lt_irrefl _ h
  · rintro ⟨hnD, hor⟩
    have hD : 0 < P.sD c := (sD_pos_iff_normSqD_pos P c).mpr hnD
    have hs : 0 < P.s c := by
      unfold Spec.s
      linarith [P.sB_nonneg c]
    have hn : 0 < Spec.normSq c := lt_of_lt_of_le hnD (normSqD_le_normSq P c)
    unfold Spec.theta
    rw [div_lt_div_iff₀ (mul_pos (pow_pos P.lam1_pos 2) hn) hs]
    by_cases hB : 0 < P.sB c
    · have hnB : 0 < ∑ i ∈ P.B, c i ^ 2 := (sB_pos_iff_normSqB_pos P c).mp hB
      have h3 : P.lamk1 ^ 2 < P.lam1 ^ 2 :=
        pow_lt_pow_left₀ (lt_of_lt_of_le P.lamk1_lt_lamk P.lamk_le_lam1) P.lamk1_pos.le
          two_ne_zero
      have hslt : P.s c < P.lam1 ^ 2 * Spec.normSq c := by
        have h1 := sD_le_lam1_sq_mul_normSqD P c
        have h2 := sB_le_lamk1_sq_mul P c
        have h4 := mul_lt_mul_of_pos_right h3 hnB
        rw [normSq_eq, mul_add]
        unfold Spec.s
        linarith
      calc P.lamk ^ 2 * P.normSqD c * P.s c ≤ P.sD c * P.s c :=
            mul_le_mul_of_nonneg_right (lamk_sq_mul_normSqD_le_sD P c) hs.le
        _ < P.sD c * (P.lam1 ^ 2 * Spec.normSq c) := mul_lt_mul_of_pos_left hslt hD
    · have hlam : P.lamk < P.lam1 := hor.resolve_left hB
      have hB0 : P.sB c = 0 := le_antisymm (not_lt.mp hB) (P.sB_nonneg c)
      have hsD : P.s c = P.sD c := by
        unfold Spec.s
        rw [hB0, add_zero]
      rw [hsD]
      have h1 : P.lamk ^ 2 < P.lam1 ^ 2 := pow_lt_pow_left₀ hlam P.lamk_pos.le two_ne_zero
      have h2 : P.lamk ^ 2 * P.normSqD c < P.lam1 ^ 2 * Spec.normSq c :=
        calc P.lamk ^ 2 * P.normSqD c < P.lam1 ^ 2 * P.normSqD c :=
              mul_lt_mul_of_pos_right h1 hnD
          _ ≤ P.lam1 ^ 2 * Spec.normSq c :=
              mul_le_mul_of_nonneg_left (normSqD_le_normSq P c) (sq_nonneg _)
      calc P.lamk ^ 2 * P.normSqD c * P.sD c < P.lam1 ^ 2 * Spec.normSq c * P.sD c :=
            mul_lt_mul_of_pos_right h2 hD
        _ = P.sD c * (P.lam1 ^ 2 * Spec.normSq c) := mul_comm _ _

/-- **Remark after Theorem 7**: the strict inequality holds whenever `0 < θ_t < 1`, i.e. both
blocks carry energy. -/
theorem normSqD_ratio_lt_theta {c : ι → ℝ} (hD : 0 < P.sD c) (hB : 0 < P.sB c) :
    P.lamk ^ 2 * P.normSqD c / (P.lam1 ^ 2 * Spec.normSq c) < P.theta c :=
  (P.normSqD_ratio_lt_theta_iff c).mpr ⟨(sD_pos_iff_normSqD_pos P c).mp hD, Or.inl hB⟩

/-- **Remark after Theorem 7, sharper bound** (not in the paper): if `p_t > 0` and `P^𝒟 x_t ≠ 0`
then `η*_t ≥ 2 gap₁ / ((λ_1² - λ_d²) + s_max ψ_𝒟 / (λ_k² ‖P^𝒟 x_t‖²))`.  This improves the paper's
bound `Spec.etaStar_ge_gap_bound_normSqD` by the factor `λ_1²/λ_d²` in the noise term. -/
theorem etaStar_ge_gap_bound_normSqD_sharp {c : ι → ℝ} (hp : 0 < P.pCoef N c)
    (hD : 0 < P.normSqD c) :
    2 * P.gap1 /
        ((P.lam1 ^ 2 - P.lamd ^ 2) + N.smax * P.psiD / (P.lamk ^ 2 * P.normSqD c)) ≤
      P.etaStar N c :=
  etaStar_ge_of_le_sD P N hp (mul_pos (pow_pos P.lamk_pos 2) hD)
    (lamk_sq_mul_normSqD_le_sD P c)

/-- **Remark after Theorem 7** (tex l. 504): if `p_t > 0` and `P^𝒟 x_t ≠ 0` then
`η*_t ≥ 2 gap₁ / ((λ_1² - λ_d²) + λ_1² s_max ψ_𝒟 / (λ_k² λ_d² ‖P^𝒟 x_t‖²))`. -/
theorem etaStar_ge_gap_bound_normSqD {c : ι → ℝ} (hp : 0 < P.pCoef N c)
    (hD : 0 < P.normSqD c) :
    2 * P.gap1 /
        ((P.lam1 ^ 2 - P.lamd ^ 2) +
          P.lam1 ^ 2 * N.smax * P.psiD / (P.lamk ^ 2 * P.lamd ^ 2 * P.normSqD c)) ≤
      P.etaStar N c := by
  have ht : 0 < P.lamk ^ 2 * P.lamd ^ 2 * P.normSqD c / P.lam1 ^ 2 :=
    div_pos (mul_pos (mul_pos (pow_pos P.lamk_pos 2) (pow_pos P.lamd_pos 2)) hD)
      (pow_pos P.lam1_pos 2)
  have hle : P.lamk ^ 2 * P.lamd ^ 2 * P.normSqD c / P.lam1 ^ 2 ≤ P.sD c := by
    rw [div_le_iff₀ (pow_pos P.lam1_pos 2)]
    have h1 := lamk_sq_mul_normSqD_le_sD P c
    have h2 : P.lamd ^ 2 ≤ P.lam1 ^ 2 := pow_le_pow_left₀ P.lamd_pos.le P.lamd_lt_lam1.le 2
    calc P.lamk ^ 2 * P.lamd ^ 2 * P.normSqD c = P.lamk ^ 2 * P.normSqD c * P.lamd ^ 2 := by
          ring
      _ ≤ P.sD c * P.lam1 ^ 2 := mul_le_mul h1 h2 (sq_nonneg _) (P.sD_nonneg c)
  have h := etaStar_ge_of_le_sD P N hp ht hle
  have he : N.smax * P.psiD / (P.lamk ^ 2 * P.lamd ^ 2 * P.normSqD c / P.lam1 ^ 2) =
      P.lam1 ^ 2 * N.smax * P.psiD / (P.lamk ^ 2 * P.lamd ^ 2 * P.normSqD c) := by
    rw [div_div_eq_mul_div]
    ring
  rw [he] at h
  exact h

/-- **Remark after Theorem 7**: the paper's route — the bound in terms of `‖P^𝒟 x_t‖` is implied
by Theorem 7 and `θ_t ≥ λ_k² ‖P^𝒟 x_t‖² / (λ_1² ‖x_t‖²)`: the right-hand side of the Remark is at
most the right-hand side of Theorem 7. -/
theorem gap_bound_normSqD_le_gap_bound {c : ι → ℝ} (hD : 0 < P.normSqD c) :
    2 * P.gap1 /
        ((P.lam1 ^ 2 - P.lamd ^ 2) +
          P.lam1 ^ 2 * N.smax * P.psiD / (P.lamk ^ 2 * P.lamd ^ 2 * P.normSqD c)) ≤
      2 * P.gap1 /
        ((P.lam1 ^ 2 - P.lamd ^ 2) +
          N.smax * P.psiD / (P.lamd ^ 2 * Spec.normSq c * P.theta c)) := by
  have hsD : 0 < P.sD c := (sD_pos_iff_normSqD_pos P c).mpr hD
  have hθ : 0 < P.theta c := (theta_pos_iff_sD_pos P c).mpr hsD
  have hn : 0 < Spec.normSq c := lt_of_lt_of_le hD (normSqD_le_normSq P c)
  have hA := lam1_sq_sub_lamd_sq_pos P
  have hC := smax_psiD_nonneg P N
  have ht : 0 < P.lamd ^ 2 * Spec.normSq c * P.theta c :=
    mul_pos (mul_pos (pow_pos P.lamd_pos 2) hn) hθ
  have ht' : 0 < P.lamk ^ 2 * P.lamd ^ 2 * P.normSqD c :=
    mul_pos (mul_pos (pow_pos P.lamk_pos 2) (pow_pos P.lamd_pos 2)) hD
  -- the noise term of Theorem 7 is at most the noise term of the Remark
  have hterm : N.smax * P.psiD / (P.lamd ^ 2 * Spec.normSq c * P.theta c) ≤
      P.lam1 ^ 2 * N.smax * P.psiD / (P.lamk ^ 2 * P.lamd ^ 2 * P.normSqD c) := by
    rw [div_le_div_iff₀ ht ht']
    have hr := P.normSqD_ratio_le_theta c
    rw [div_le_iff₀ (mul_pos (pow_pos P.lam1_pos 2) hn)] at hr
    -- hr : λ_k² ‖P^𝒟 x‖² ≤ θ (λ_1² ‖x‖²)
    have h1 : N.smax * P.psiD * (P.lamd ^ 2 * (P.lamk ^ 2 * P.normSqD c)) ≤
        N.smax * P.psiD * (P.lamd ^ 2 * (P.theta c * (P.lam1 ^ 2 * Spec.normSq c))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr (sq_nonneg _)) hC
    linarith
  exact div_le_div_of_nonneg_left (mul_nonneg zero_le_two P.gap1_pos.le)
    (add_pos_of_pos_of_nonneg hA (div_nonneg hC ht.le)) (by linarith)

/-- **Remark after Theorem 7** ("the lower bounds increase with `‖x_t‖` and with `θ_t`"): the
right-hand side `2 gap₁ / ((λ_1² - λ_d²) + s_max ψ_𝒟 / T)` of Theorem 7 is nondecreasing in
`T = λ_d² ‖x_t‖² θ_t > 0`. -/
theorem gap_bound_mono {t t' : ℝ} (ht : 0 < t) (htt : t ≤ t') :
    2 * P.gap1 / ((P.lam1 ^ 2 - P.lamd ^ 2) + N.smax * P.psiD / t) ≤
      2 * P.gap1 / ((P.lam1 ^ 2 - P.lamd ^ 2) + N.smax * P.psiD / t') := by
  have hA := lam1_sq_sub_lamd_sq_pos P
  have hC := smax_psiD_nonneg P N
  have ht' : 0 < t' := lt_of_lt_of_le ht htt
  refine div_le_div_of_nonneg_left (mul_nonneg zero_le_two P.gap1_pos.le)
    (add_pos_of_pos_of_nonneg hA (div_nonneg hC ht'.le)) ?_
  have h := div_le_div_of_nonneg_left hC ht htt
  linarith

/-- **Remark after Theorem 7** ("`η*`'s lower bound `≈ 2 gap₁ / (λ_1² - λ_d²)`"): the lower
bound of the Remark tends to `2 gap₁ / (λ_1² - λ_d²)` as `‖P^𝒟 x_t‖² → ∞`. -/
theorem tendsto_gap_bound_normSqD :
    Filter.Tendsto
      (fun r : ℝ => 2 * P.gap1 /
        ((P.lam1 ^ 2 - P.lamd ^ 2) +
          P.lam1 ^ 2 * N.smax * P.psiD / (P.lamk ^ 2 * P.lamd ^ 2 * r)))
      Filter.atTop (nhds (2 * P.gap1 / (P.lam1 ^ 2 - P.lamd ^ 2))) := by
  have hc : 0 < P.lamk ^ 2 * P.lamd ^ 2 := mul_pos (pow_pos P.lamk_pos 2) (pow_pos P.lamd_pos 2)
  have h1 : Filter.Tendsto (fun r : ℝ => P.lamk ^ 2 * P.lamd ^ 2 * r) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hc Filter.tendsto_id
  have h2 : Filter.Tendsto
      (fun r : ℝ => P.lam1 ^ 2 * N.smax * P.psiD / (P.lamk ^ 2 * P.lamd ^ 2 * r))
      Filter.atTop (nhds 0) := tendsto_const_nhds.div_atTop h1
  have h3 : Filter.Tendsto
      (fun r : ℝ => (P.lam1 ^ 2 - P.lamd ^ 2) +
        P.lam1 ^ 2 * N.smax * P.psiD / (P.lamk ^ 2 * P.lamd ^ 2 * r))
      Filter.atTop (nhds ((P.lam1 ^ 2 - P.lamd ^ 2) + 0)) := tendsto_const_nhds.add h2
  rw [add_zero] at h3
  exact tendsto_const_nhds.div h3 (lam1_sq_sub_lamd_sq_pos P).ne'

/-- **Remark after Theorem 7** ("`≈ 2/(λ_1 + λ_d)`"): `2 gap₁ / (λ_1² - λ_d²) ≤ 2 / (λ_1 + λ_d)`
always, with equality when the blocks are flat (`λ_k = λ_1`, `λ_{k+1} = λ_d`). -/
theorem two_gap1_div_le : 2 * P.gap1 / (P.lam1 ^ 2 - P.lamd ^ 2) ≤ 2 / (P.lam1 + P.lamd) := by
  rw [div_le_div_iff₀ (lam1_sq_sub_lamd_sq_pos P) (add_pos P.lam1_pos P.lamd_pos)]
  have h1 : P.gap1 ≤ P.lam1 - P.lamd := by
    unfold Spec.gap1
    linarith [P.lamk_le_lam1, P.lamd_le_lamk1]
  have h2 := mul_le_mul_of_nonneg_right h1 (add_pos P.lam1_pos P.lamd_pos).le
  nlinarith

theorem two_gap1_div_eq (h1 : P.lamk = P.lam1) (h2 : P.lamk1 = P.lamd) :
    2 * P.gap1 / (P.lam1 ^ 2 - P.lamd ^ 2) = 2 / (P.lam1 + P.lamd) := by
  unfold Spec.gap1
  rw [h1, h2, div_eq_div_iff (lam1_sq_sub_lamd_sq_pos P).ne'
    (add_pos P.lam1_pos P.lamd_pos).ne']
  ring

/-! ### Theorem 8 (corrected) -/

/-- The paper's alignment hypothesis of Theorem 8, `θ_t ≥ e_ℬ / (e_ℬ + e_𝒟)`, is equivalent to
`s^ℬ e_ℬ ≤ s^𝒟 e_𝒟` — *not* to `s^ℬ e_𝒟 - s^𝒟 e_ℬ ≥ 0` as claimed in the paper's proof
(tex l. 1421–1424). -/
theorem eB_ratio_le_theta_iff {c : ι → ℝ} (hs : 0 < P.s c) (he : 0 < P.eB N + P.eD N) :
    P.eB N / (P.eB N + P.eD N) ≤ P.theta c ↔ P.sB c * P.eB N ≤ P.sD c * P.eD N := by
  unfold Spec.theta
  rw [div_le_div_iff₀ he hs]
  unfold Spec.s
  constructor <;> intro h <;> linarith

/-- The condition actually needed in the proof of Theorem 8, `s^ℬ e_𝒟 - s^𝒟 e_ℬ ≥ 0`, is
equivalent to `θ_t ≤ e_𝒟 / (e_ℬ + e_𝒟)`, i.e. `1 - θ_t ≥ e_ℬ / (e_ℬ + e_𝒟)`. -/
theorem theta_le_eD_ratio_iff {c : ι → ℝ} (hs : 0 < P.s c) (he : 0 < P.eB N + P.eD N) :
    P.theta c ≤ P.eD N / (P.eB N + P.eD N) ↔ P.sD c * P.eB N ≤ P.sB c * P.eD N := by
  unfold Spec.theta
  rw [div_le_div_iff₀ hs he]
  unfold Spec.s
  constructor <;> intro h <;> linarith

/-- Under the corrected noise condition `s^𝒟 e_ℬ ≤ s^ℬ e_𝒟` and `0 < θ_t < 1`, the quadratic
coefficient is positive: `p_t ≥ gap₂ s^𝒟 s^ℬ > 0`. -/
theorem pCoef_pos_of_noise_cond {c : ι → ℝ} (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hnoise : P.sD c * P.eB N ≤ P.sB c * P.eD N) : 0 < P.pCoef N c := by
  have h1 := gap2_mul_le_signal P c
  have h2 : 0 < P.gap2 * (P.sD c * P.sB c) := mul_pos P.gap2_pos (mul_pos hD hB)
  rw [pCoef_eq_signal_add_noise]
  linarith

/-- **Theorem 8, corrected and sharpened.**  If `p_t > 0` and `s^𝒟 e_ℬ ≤ s^ℬ e_𝒟`
(equivalently `θ_t ≤ e_𝒟 / (e_ℬ + e_𝒟)`, see `Spec.theta_le_eD_ratio_iff`), then
`η*_t ≤ 2 / (λ_k + λ_d)`. -/
theorem etaStar_le_two_div_lamk_add_lamd {c : ι → ℝ} (hp : 0 < P.pCoef N c)
    (hnoise : P.sD c * P.eB N ≤ P.sB c * P.eD N) :
    P.etaStar N c ≤ 2 / (P.lamk + P.lamd) := by
  have hlam : 0 < P.lamk + P.lamd := add_pos P.lamk_pos P.lamd_pos
  have h1 := lam_add_mul_le_signal P c
  have h2 := pCoef_eq_signal_add_noise P N c
  have hq : -P.qCoef c = 2 * (P.sB c * P.tauD c - P.sD c * P.tauB c) := by
    unfold Spec.qCoef
    ring
  unfold Spec.etaStar
  rw [div_le_div_iff₀ hp hlam, hq]
  linarith

/-- **Theorem 8** (`thm:state-gap-aware`), corrected.  If `p_t > 0` and `s^𝒟 e_ℬ ≤ s^ℬ e_𝒟`,
then `η*_t ≤ 2 (λ_1 - λ_d) / (λ_k λ_1 - λ_{k+1} λ_d)`.

Deviations from the paper: (i) the paper's hypothesis `θ_t ≥ e_ℬ/(e_ℬ + e_𝒟)` points the wrong
way (its proof needs `s^ℬ e_𝒟 ≥ s^𝒟 e_ℬ`, i.e. `θ_t ≤ e_𝒟/(e_ℬ + e_𝒟)`); (ii) the main-text
statement lacks the factor `2` (the appendix restatement has it).  Under the paper's hypothesis
the claim is false for both versions of the constant, see `EtaStarBounds.thm8_cor9_fail`. -/
theorem etaStar_le_two_mul_gap_ratio {c : ι → ℝ} (hp : 0 < P.pCoef N c)
    (hnoise : P.sD c * P.eB N ≤ P.sB c * P.eD N) :
    P.etaStar N c ≤ 2 * (P.lam1 - P.lamd) / (P.lamk * P.lam1 - P.lamk1 * P.lamd) :=
  le_trans (P.etaStar_le_two_div_lamk_add_lamd N hp hnoise) (two_div_le_two_mul_ratio P)

/-- **Theorem 8, corrected, in alignment form.**  If `p_t > 0`, the noise is not identically
zero on the spectrum (`e_ℬ + e_𝒟 > 0`) and `θ_t ≤ e_𝒟 / (e_ℬ + e_𝒟)`, then
`η*_t ≤ 2 (λ_1 - λ_d) / (λ_k λ_1 - λ_{k+1} λ_d)`. -/
theorem etaStar_le_two_mul_gap_ratio_of_theta_le {c : ι → ℝ} (hp : 0 < P.pCoef N c)
    (he : 0 < P.eB N + P.eD N) (hθ : P.theta c ≤ P.eD N / (P.eB N + P.eD N)) :
    P.etaStar N c ≤ 2 * (P.lam1 - P.lamd) / (P.lamk * P.lam1 - P.lamk1 * P.lamd) := by
  have hs : 0 < P.s c := by
    have := sB_pos_of_pCoef_pos P N hp
    unfold Spec.s
    linarith [P.sD_nonneg c]
  exact P.etaStar_le_two_mul_gap_ratio N hp ((P.theta_le_eD_ratio_iff N hs he).mp hθ)

/-- **Theorem 8, sign-free semantic form.**  If `0 < θ_t < 1` and `s^𝒟 e_ℬ ≤ s^ℬ e_𝒟`, every step
size above `2 / (λ_k + λ_d)` lies in the increase regime `p_t η² + q_t η > 0`. -/
theorem quad_pos_of_two_div_lt {c : ι → ℝ} (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hnoise : P.sD c * P.eB N ≤ P.sB c * P.eD N) {η : ℝ} (hη : 2 / (P.lamk + P.lamd) < η) :
    0 < P.pCoef N c * η ^ 2 + P.qCoef c * η := by
  have hp : 0 < P.pCoef N c := P.pCoef_pos_of_noise_cond N hD hB hnoise
  have hη0 : 0 < η := lt_trans (div_pos zero_lt_two (add_pos P.lamk_pos P.lamd_pos)) hη
  have h1 : P.etaStar N c < η :=
    lt_of_le_of_lt (P.etaStar_le_two_div_lamk_add_lamd N hp hnoise) hη
  unfold Spec.etaStar at h1
  rw [div_lt_iff₀ hp] at h1
  have h2 : 0 < η * (η * P.pCoef N c + P.qCoef c) := mul_pos hη0 (by linarith)
  nlinarith

/-! ### Corollary 9 (corrected) -/

/-- **Corollary 9** (`cor:conservative-limit2`), corrected.  If `p_t > 0`,
`s^𝒟 e_ℬ ≤ s^ℬ e_𝒟` and additionally `λ_1 ≤ λ_k + λ_d`, then `η*_t ≤ 2 / λ_1`.

Without the spectral condition `λ_1 ≤ λ_k + λ_d` the claim is false, even under the corrected
hypothesis of Theorem 8: see `EtaStarBounds.cor9_fails_under_corrected_hypothesis`. -/
theorem etaStar_le_two_div_lam1 {c : ι → ℝ} (hp : 0 < P.pCoef N c)
    (hnoise : P.sD c * P.eB N ≤ P.sB c * P.eD N) (hlam : P.lam1 ≤ P.lamk + P.lamd) :
    P.etaStar N c ≤ 2 / P.lam1 :=
  le_trans (P.etaStar_le_two_div_lamk_add_lamd N hp hnoise)
    (div_le_div_of_nonneg_left zero_le_two P.lam1_pos hlam)

/-- **Corollary 9, unconditional variant**: under the corrected hypothesis of Theorem 8,
`η*_t < 2 / λ_k` (with `λ_k`, the *smallest* dominant eigenvalue, in place of `λ_1`). -/
theorem etaStar_lt_two_div_lamk {c : ι → ℝ} (hp : 0 < P.pCoef N c)
    (hnoise : P.sD c * P.eB N ≤ P.sB c * P.eD N) : P.etaStar N c < 2 / P.lamk :=
  lt_of_le_of_lt (P.etaStar_le_two_div_lamk_add_lamd N hp hnoise)
    (div_lt_div_of_pos_left zero_lt_two P.lamk_pos (by linarith [P.lamd_pos]))

end Spec

/-! ### Concrete instances: non-vacuity, sharpness and counterexamples -/

namespace EtaStarBounds

/-- Isotropic noise `Σ = σ² I`: `κ_i² = s_min = s_max = σ²`. -/
def ceIso (ι : Type*) (σ2 : ℝ) (h : 0 ≤ σ2) : Noise ι where
  kap2 := fun _ => σ2
  smin := σ2
  smax := σ2
  smin_nonneg := h
  smin_le := fun _ => le_refl _
  le_smax := fun _ => le_refl _

/-- The spectrum `λ = (2, 1)` on `Fin 2` with dominant block `𝒟 = {0}` (`k = 1`, `d = 2`). -/
def ceSpec2 : Spec (Fin 2) where
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

theorem ceSpec2_B : ceSpec2.B = {1} := by decide

theorem ceSpec2_lam1 : ceSpec2.lam1 = 2 := rfl
theorem ceSpec2_lamk : ceSpec2.lamk = 2 := rfl
theorem ceSpec2_lamk1 : ceSpec2.lamk1 = 1 := rfl
theorem ceSpec2_lamd : ceSpec2.lamd = 1 := rfl

theorem ceSpec2_gap1 : ceSpec2.gap1 = 1 := by
  unfold Spec.gap1
  rw [ceSpec2_lamk, ceSpec2_lamk1]
  norm_num

theorem ceSpec2_mom_D (p : ℕ) (c : Fin 2 → ℝ) :
    ceSpec2.mom ceSpec2.D p c = 2 ^ p * c 0 ^ 2 := by
  change ∑ i ∈ ({0} : Finset (Fin 2)), ceSpec2.lam i ^ p * c i ^ 2 = _
  rw [Finset.sum_singleton]
  rfl

theorem ceSpec2_mom_B (p : ℕ) (c : Fin 2 → ℝ) : ceSpec2.mom ceSpec2.B p c = c 1 ^ 2 := by
  unfold Spec.mom
  rw [ceSpec2_B, Finset.sum_singleton]
  simp [ceSpec2]

theorem ceSpec2_psiD : ceSpec2.psiD = 4 := by
  change ∑ i ∈ ({0} : Finset (Fin 2)), ceSpec2.lam i ^ 2 = 4
  rw [Finset.sum_singleton]
  change (2 : ℝ) ^ 2 = 4
  norm_num

theorem ceSpec2_eD (N : Noise (Fin 2)) : ceSpec2.eD N = 4 * N.kap2 0 := by
  change ∑ i ∈ ({0} : Finset (Fin 2)), ceSpec2.lam i ^ 2 * N.kap2 i = _
  rw [Finset.sum_singleton]
  change (2 : ℝ) ^ 2 * N.kap2 0 = _
  norm_num

theorem ceSpec2_eB (N : Noise (Fin 2)) : ceSpec2.eB N = N.kap2 1 := by
  unfold Spec.eB
  rw [ceSpec2_B, Finset.sum_singleton]
  simp [ceSpec2]

theorem ceSpec2_sD (c : Fin 2 → ℝ) : ceSpec2.sD c = 4 * c 0 ^ 2 := by
  unfold Spec.sD
  rw [ceSpec2_mom_D]
  norm_num

theorem ceSpec2_sB (c : Fin 2 → ℝ) : ceSpec2.sB c = c 1 ^ 2 := ceSpec2_mom_B 2 c

theorem ceSpec2_qCoef (c : Fin 2 → ℝ) : ceSpec2.qCoef c = -(8 * c 0 ^ 2 * c 1 ^ 2) := by
  unfold Spec.qCoef Spec.tauD Spec.tauB
  rw [ceSpec2_sD, ceSpec2_sB, ceSpec2_mom_D, ceSpec2_mom_B]
  ring

theorem ceSpec2_pCoef (N : Noise (Fin 2)) (c : Fin 2 → ℝ) :
    ceSpec2.pCoef N c =
      12 * c 0 ^ 2 * c 1 ^ 2 + 4 * (c 1 ^ 2 * N.kap2 0 - c 0 ^ 2 * N.kap2 1) := by
  unfold Spec.pCoef
  rw [ceSpec2_sD, ceSpec2_sB, ceSpec2_mom_D, ceSpec2_mom_B, ceSpec2_eD, ceSpec2_eB]
  ring

theorem ceSpec2_normSq (c : Fin 2 → ℝ) : Spec.normSq c = c 0 ^ 2 + c 1 ^ 2 := by
  simp [Spec.normSq, Fin.sum_univ_two]

theorem ceSpec2_normSqD (c : Fin 2 → ℝ) : ceSpec2.normSqD c = c 0 ^ 2 := by
  change ∑ i ∈ ({0} : Finset (Fin 2)), c i ^ 2 = _
  rw [Finset.sum_singleton]

/-- At `x = (2, 1)`: `θ = 16/17`. -/
theorem ceSpec2_theta : ceSpec2.theta ![2, 1] = 16 / 17 := by
  unfold Spec.theta Spec.s
  rw [ceSpec2_sD, ceSpec2_sB]
  norm_num

/-- At `x = (2, 1)` with isotropic noise `σ²`: `p = 48 - 12 σ²`. -/
theorem ceSpec2_pCoef_iso (σ2 : ℝ) (h : 0 ≤ σ2) :
    ceSpec2.pCoef (ceIso (Fin 2) σ2 h) ![2, 1] = 48 - 12 * σ2 := by
  rw [ceSpec2_pCoef]
  simp [ceIso]
  ring

/-- At `x = (2, 1)` with isotropic noise `σ²`: `η* = 32 / (48 - 12 σ²)`. -/
theorem ceSpec2_etaStar_iso (σ2 : ℝ) (h : 0 ≤ σ2) :
    ceSpec2.etaStar (ceIso (Fin 2) σ2 h) ![2, 1] = 32 / (48 - 12 * σ2) := by
  unfold Spec.etaStar
  rw [ceSpec2_pCoef_iso, ceSpec2_qCoef]
  norm_num

/-- **Theorem 7 is false as literally stated ("for any `x_t`").**  For `λ = (2, 1)`, `k = 1`,
`x_t = (2, 1)` and isotropic noise `Σ = 8 I` one has `0 < θ_t = 16/17 < 1` and `p_t = -48 < 0`,
so `η*_t = -q_t/p_t = -2/3`, while the right-hand side of Theorem 7 equals `10/49 > 0`. -/
theorem thm7_fails_of_pCoef_neg :
    ceSpec2.pCoef (ceIso (Fin 2) 8 (by norm_num)) ![2, 1] < 0 ∧
    0 < ceSpec2.theta ![2, 1] ∧ ceSpec2.theta ![2, 1] < 1 ∧
    ceSpec2.etaStar (ceIso (Fin 2) 8 (by norm_num)) ![2, 1] <
      2 * ceSpec2.gap1 /
        ((ceSpec2.lam1 ^ 2 - ceSpec2.lamd ^ 2) +
          (ceIso (Fin 2) 8 (by norm_num)).smax * ceSpec2.psiD /
            (ceSpec2.lamd ^ 2 * Spec.normSq (![2, 1] : Fin 2 → ℝ) * ceSpec2.theta ![2, 1])) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ceSpec2_pCoef_iso]; norm_num
  · rw [ceSpec2_theta]; norm_num
  · rw [ceSpec2_theta]; norm_num
  · rw [ceSpec2_etaStar_iso, ceSpec2_gap1, ceSpec2_lam1, ceSpec2_lamd, ceSpec2_psiD,
      ceSpec2_normSq, ceSpec2_theta]
    norm_num [ceIso]

/-- **Theorem 8 and Corollary 9 are false as stated.**  For `λ = (2, 1)`, `k = 1`,
`x_t = (2, 1)` and isotropic noise `Σ = 3 I`: `p_t = 12 > 0`, the paper's hypothesis
`θ_t = 16/17 ≥ e_ℬ/(e_ℬ + e_𝒟) = 1/5` holds, and `η*_t = 8/3`, which exceeds

* `(λ_1 - λ_d)/(λ_k λ_1 - λ_{k+1} λ_d) = 1/3` (Theorem 8, main text),
* `2 (λ_1 - λ_d)/(λ_k λ_1 - λ_{k+1} λ_d) = 2/3` (Theorem 8, appendix restatement),
* `2/λ_1 = 1` (Corollary 9). -/
theorem thm8_cor9_fail :
    0 < ceSpec2.pCoef (ceIso (Fin 2) 3 (by norm_num)) ![2, 1] ∧
    ceSpec2.eB (ceIso (Fin 2) 3 (by norm_num)) /
        (ceSpec2.eB (ceIso (Fin 2) 3 (by norm_num)) +
          ceSpec2.eD (ceIso (Fin 2) 3 (by norm_num))) ≤ ceSpec2.theta ![2, 1] ∧
    (ceSpec2.lam1 - ceSpec2.lamd) / (ceSpec2.lamk * ceSpec2.lam1 - ceSpec2.lamk1 * ceSpec2.lamd) <
      ceSpec2.etaStar (ceIso (Fin 2) 3 (by norm_num)) ![2, 1] ∧
    2 * (ceSpec2.lam1 - ceSpec2.lamd) /
        (ceSpec2.lamk * ceSpec2.lam1 - ceSpec2.lamk1 * ceSpec2.lamd) <
      ceSpec2.etaStar (ceIso (Fin 2) 3 (by norm_num)) ![2, 1] ∧
    2 / ceSpec2.lam1 < ceSpec2.etaStar (ceIso (Fin 2) 3 (by norm_num)) ![2, 1] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [ceSpec2_pCoef_iso]; norm_num
  · rw [ceSpec2_eB, ceSpec2_eD, ceSpec2_theta]; norm_num [ceIso]
  · rw [ceSpec2_etaStar_iso, ceSpec2_lam1, ceSpec2_lamk, ceSpec2_lamk1, ceSpec2_lamd]; norm_num
  · rw [ceSpec2_etaStar_iso, ceSpec2_lam1, ceSpec2_lamk, ceSpec2_lamk1, ceSpec2_lamd]; norm_num
  · rw [ceSpec2_etaStar_iso, ceSpec2_lam1]; norm_num

/-- **Under the hypothesis of Theorem 8 as stated in the paper, `η*_t` has no upper bound at
all** (not even one depending on the spectrum): for `λ = (2, 1)`, `x_t = (2, 1)` and every `M`
there is a non-degenerate isotropic noise with `p_t > 0`, `θ_t ≥ e_ℬ/(e_ℬ + e_𝒟)` and
`η*_t > M`. -/
theorem thm8_hypothesis_gives_no_upper_bound (M : ℝ) :
    ∃ N : Noise (Fin 2), 0 < N.smin ∧ 0 < ceSpec2.pCoef N ![2, 1] ∧
      ceSpec2.eB N / (ceSpec2.eB N + ceSpec2.eD N) ≤ ceSpec2.theta ![2, 1] ∧
      M < ceSpec2.etaStar N ![2, 1] := by
  have hM : 0 < |M| + 1 := by positivity
  have hε : 0 < 1 / (|M| + 1) := by positivity
  have hε1 : 1 / (|M| + 1) ≤ 1 := by
    rw [div_le_one hM]
    linarith [abs_nonneg M]
  refine ⟨ceIso (Fin 2) (4 - 1 / (|M| + 1)) (by linarith), ?_, ?_, ?_, ?_⟩
  · change 0 < 4 - 1 / (|M| + 1)
    linarith
  · rw [ceSpec2_pCoef_iso]
    linarith
  · rw [ceSpec2_eB, ceSpec2_eD, ceSpec2_theta]
    change (4 - 1 / (|M| + 1)) / ((4 - 1 / (|M| + 1)) + 4 * (4 - 1 / (|M| + 1))) ≤ 16 / 17
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  · rw [ceSpec2_etaStar_iso]
    have h : 48 - 12 * (4 - 1 / (|M| + 1)) = 12 / (|M| + 1) := by ring
    rw [h, div_div_eq_mul_div, lt_div_iff₀ (by norm_num)]
    nlinarith [le_abs_self M, abs_nonneg M]

/-- The spectrum `λ = (10, 2, 1)` on `Fin 3` with dominant block `𝒟 = {0, 1}` (`k = 2`, `d = 3`),
for which `λ_1 > λ_k + λ_d`. -/
def ceSpec3 : Spec (Fin 3) where
  lam := ![10, 2, 1]
  D := {0, 1}
  i1 := 0
  ik := 1
  ik1 := 2
  id := 2
  i1_mem := by decide
  ik_mem := by decide
  ik1_not_mem := by decide
  id_not_mem := by decide
  lam_pos := by intro i; fin_cases i <;> simp
  le_lam1 := by
    intro i _
    fin_cases i <;> simp
    norm_num
  lamk_le := by
    intro i hi
    fin_cases i
    · simp; norm_num
    · simp
    · exact absurd hi (by decide)
  le_lamk1 := by
    intro i hi
    fin_cases i
    · exact absurd (by decide) hi
    · exact absurd (by decide) hi
    · simp
  lamd_le := by intro i _; fin_cases i <;> simp
  gap := by simp

theorem ceSpec3_B : ceSpec3.B = {2} := by decide

theorem ceSpec3_lam1 : ceSpec3.lam1 = 10 := rfl
theorem ceSpec3_lamk : ceSpec3.lamk = 2 := rfl
theorem ceSpec3_lamk1 : ceSpec3.lamk1 = 1 := rfl
theorem ceSpec3_lamd : ceSpec3.lamd = 1 := rfl

theorem ceSpec3_mom_D (p : ℕ) (c : Fin 3 → ℝ) :
    ceSpec3.mom ceSpec3.D p c = 10 ^ p * c 0 ^ 2 + 2 ^ p * c 1 ^ 2 := by
  change ∑ i ∈ ({0, 1} : Finset (Fin 3)), ceSpec3.lam i ^ p * c i ^ 2 = _
  rw [Finset.sum_pair (by decide)]
  rfl

theorem ceSpec3_mom_B (p : ℕ) (c : Fin 3 → ℝ) : ceSpec3.mom ceSpec3.B p c = c 2 ^ 2 := by
  unfold Spec.mom
  rw [ceSpec3_B, Finset.sum_singleton]
  simp [ceSpec3]

theorem ceSpec3_eD (N : Noise (Fin 3)) : ceSpec3.eD N = 100 * N.kap2 0 + 4 * N.kap2 1 := by
  change ∑ i ∈ ({0, 1} : Finset (Fin 3)), ceSpec3.lam i ^ 2 * N.kap2 i = _
  rw [Finset.sum_pair (by decide)]
  change (10 : ℝ) ^ 2 * N.kap2 0 + (2 : ℝ) ^ 2 * N.kap2 1 = _
  norm_num

theorem ceSpec3_eB (N : Noise (Fin 3)) : ceSpec3.eB N = N.kap2 2 := by
  unfold Spec.eB
  rw [ceSpec3_B, Finset.sum_singleton]
  simp [ceSpec3]

/-- At `x = (0, 10, 10)`: `s^𝒟 = 400`. -/
theorem ceSpec3_sD : ceSpec3.sD ![0, 10, 10] = 400 := by
  unfold Spec.sD
  rw [ceSpec3_mom_D]
  norm_num

/-- At `x = (0, 10, 10)`: `s^ℬ = 100`. -/
theorem ceSpec3_sB : ceSpec3.sB ![0, 10, 10] = 100 := by
  unfold Spec.sB
  rw [ceSpec3_mom_B]
  norm_num

/-- At `x = (0, 10, 10)`: `θ = 4/5`. -/
theorem ceSpec3_theta : ceSpec3.theta ![0, 10, 10] = 4 / 5 := by
  unfold Spec.theta Spec.s
  rw [ceSpec3_sD, ceSpec3_sB]
  norm_num

/-- At `x = (0, 10, 10)`: `q = -80000`. -/
theorem ceSpec3_qCoef : ceSpec3.qCoef ![0, 10, 10] = -80000 := by
  unfold Spec.qCoef Spec.tauD Spec.tauB
  rw [ceSpec3_sD, ceSpec3_sB, ceSpec3_mom_D, ceSpec3_mom_B]
  norm_num

/-- At `x = (0, 10, 10)` with isotropic unit noise: `p = 130000`. -/
theorem ceSpec3_pCoef :
    ceSpec3.pCoef (ceIso (Fin 3) 1 zero_le_one) ![0, 10, 10] = 130000 := by
  unfold Spec.pCoef
  rw [ceSpec3_sD, ceSpec3_sB, ceSpec3_mom_D, ceSpec3_mom_B, ceSpec3_eD, ceSpec3_eB]
  norm_num [ceIso]

/-- At `x = (0, 10, 10)` with isotropic unit noise: `η* = 8/13`. -/
theorem ceSpec3_etaStar :
    ceSpec3.etaStar (ceIso (Fin 3) 1 zero_le_one) ![0, 10, 10] = 8 / 13 := by
  unfold Spec.etaStar
  rw [ceSpec3_pCoef, ceSpec3_qCoef]
  norm_num

/-- **Corollary 9 is false even under the corrected hypothesis of Theorem 8**, and the main-text
constant of Theorem 8 (without the factor `2`) is false under *both* hypotheses.  For
`λ = (10, 2, 1)`, `k = 2`, `x_t = (0, 10, 10)` and isotropic unit noise: `p_t = 130000 > 0`; the
corrected hypothesis `s^𝒟 e_ℬ ≤ s^ℬ e_𝒟` holds (`400 ≤ 10400`); the paper's hypothesis
`θ_t = 4/5 ≥ e_ℬ/(e_ℬ + e_𝒟) = 1/105` holds; and `η*_t = 8/13` exceeds both `2/λ_1 = 1/5`
(Corollary 9) and `(λ_1 - λ_d)/(λ_k λ_1 - λ_{k+1} λ_d) = 9/19` (Theorem 8, main text). -/
theorem cor9_fails_under_corrected_hypothesis :
    0 < ceSpec3.pCoef (ceIso (Fin 3) 1 zero_le_one) ![0, 10, 10] ∧
    ceSpec3.sD ![0, 10, 10] * ceSpec3.eB (ceIso (Fin 3) 1 zero_le_one) ≤
      ceSpec3.sB ![0, 10, 10] * ceSpec3.eD (ceIso (Fin 3) 1 zero_le_one) ∧
    ceSpec3.eB (ceIso (Fin 3) 1 zero_le_one) /
        (ceSpec3.eB (ceIso (Fin 3) 1 zero_le_one) + ceSpec3.eD (ceIso (Fin 3) 1 zero_le_one)) ≤
      ceSpec3.theta ![0, 10, 10] ∧
    2 / ceSpec3.lam1 < ceSpec3.etaStar (ceIso (Fin 3) 1 zero_le_one) ![0, 10, 10] ∧
    (ceSpec3.lam1 - ceSpec3.lamd) / (ceSpec3.lamk * ceSpec3.lam1 - ceSpec3.lamk1 * ceSpec3.lamd) <
      ceSpec3.etaStar (ceIso (Fin 3) 1 zero_le_one) ![0, 10, 10] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [ceSpec3_pCoef]; norm_num
  · rw [ceSpec3_sD, ceSpec3_sB, ceSpec3_eD, ceSpec3_eB]; norm_num [ceIso]
  · rw [ceSpec3_eD, ceSpec3_eB, ceSpec3_theta]; norm_num [ceIso]
  · rw [ceSpec3_etaStar, ceSpec3_lam1]; norm_num
  · rw [ceSpec3_etaStar, ceSpec3_lam1, ceSpec3_lamk, ceSpec3_lamk1, ceSpec3_lamd]; norm_num

/-- The inequality `(λ_1 - λ_d)/(λ_k λ_1 - λ_{k+1} λ_d) ≤ 1/λ_1` used in the paper's proof of
Corollary 9 fails for `λ = (10, 2, 1)`, `k = 2` (`9/19 > 1/10`). -/
theorem cor9_proof_step_fails :
    1 / ceSpec3.lam1 <
      (ceSpec3.lam1 - ceSpec3.lamd) /
        (ceSpec3.lamk * ceSpec3.lam1 - ceSpec3.lamk1 * ceSpec3.lamd) := by
  rw [ceSpec3_lam1, ceSpec3_lamk, ceSpec3_lamk1, ceSpec3_lamd]
  norm_num

/-- **The strict inequality in the Remark after Theorem 7 fails**: for `λ = (2, 1)`, `k = 1` and
`x_t = e_1 = (1, 0)` both sides equal `1`. -/
theorem remark_strict_fails :
    ceSpec2.theta ![1, 0] =
      ceSpec2.lamk ^ 2 * ceSpec2.normSqD ![1, 0] /
        (ceSpec2.lam1 ^ 2 * Spec.normSq (![1, 0] : Fin 2 → ℝ)) := by
  unfold Spec.theta Spec.s
  rw [ceSpec2_sD, ceSpec2_sB, ceSpec2_normSqD, ceSpec2_normSq, ceSpec2_lamk, ceSpec2_lam1]
  norm_num

/-- Why `θ_t > 0` is assumed in `Spec.etaStar_ge_gap_bound`: for `λ = (2, 1)`, `x_t = (0, 1)`
(so `θ_t = 0`) and `Σ = I` one has `p_t = 4 > 0` and `η*_t = 0`; the paper's right-hand side is
"`2 gap₁ / ∞ = 0`", but with Lean's convention `a / 0 = 0` it evaluates to `2/3`. -/
theorem thm7_theta_zero_artifact :
    0 < ceSpec2.pCoef (ceIso (Fin 2) 1 zero_le_one) ![0, 1] ∧
    ceSpec2.theta ![0, 1] = 0 ∧
    ceSpec2.etaStar (ceIso (Fin 2) 1 zero_le_one) ![0, 1] = 0 ∧
    2 * ceSpec2.gap1 /
        ((ceSpec2.lam1 ^ 2 - ceSpec2.lamd ^ 2) +
          (ceIso (Fin 2) 1 zero_le_one).smax * ceSpec2.psiD /
            (ceSpec2.lamd ^ 2 * Spec.normSq (![0, 1] : Fin 2 → ℝ) * ceSpec2.theta ![0, 1])) =
      2 / 3 := by
  have hθ : ceSpec2.theta ![0, 1] = 0 := by
    unfold Spec.theta Spec.s
    rw [ceSpec2_sD, ceSpec2_sB]
    norm_num
  refine ⟨?_, hθ, ?_, ?_⟩
  · rw [ceSpec2_pCoef]; norm_num [ceIso]
  · unfold Spec.etaStar
    rw [ceSpec2_qCoef]
    norm_num
  · rw [hθ, ceSpec2_gap1, ceSpec2_lam1, ceSpec2_lamd]
    norm_num

/-- **The step `θ_t ≥ e_ℬ/(e_ℬ + e_𝒟) ⟹ s^ℬ e_𝒟 - s^𝒟 e_ℬ ≥ 0` in the paper's proof of
Theorem 8 is wrong**: for `λ = (2, 1)`, `x_t = (2, 1)`, `Σ = 3 I` the hypothesis holds
(`16/17 ≥ 1/5`) but `s^ℬ e_𝒟 - s^𝒟 e_ℬ = 12 - 48 < 0`. -/
theorem thm8_noise_residual_neg :
    ceSpec2.eB (ceIso (Fin 2) 3 (by norm_num)) /
        (ceSpec2.eB (ceIso (Fin 2) 3 (by norm_num)) +
          ceSpec2.eD (ceIso (Fin 2) 3 (by norm_num))) ≤ ceSpec2.theta ![2, 1] ∧
    ceSpec2.sB ![2, 1] * ceSpec2.eD (ceIso (Fin 2) 3 (by norm_num)) -
        ceSpec2.sD ![2, 1] * ceSpec2.eB (ceIso (Fin 2) 3 (by norm_num)) < 0 := by
  refine ⟨thm8_cor9_fail.2.1, ?_⟩
  rw [ceSpec2_sD, ceSpec2_sB, ceSpec2_eB, ceSpec2_eD]
  norm_num [ceIso]

/-- **The lower bound `p_t^{signal} ≥ (λ_k λ_1 - λ_{k+1} λ_d) s^𝒟 s^ℬ` asserted in the paper's
proof of Theorem 8 (tex l. 1417–1420) is wrong**: for `λ = (10, 2, 1)`, `k = 2`,
`x_t = (0, 10, 10)` the left-hand side is `120000` and the right-hand side `760000`.  (The valid
constant is `gap₂ = λ_k² - λ_{k+1}²`, see `gap2_mul_le_signal`.) -/
theorem thm8_proof_step_fails :
    ceSpec3.sB ![0, 10, 10] * ceSpec3.mom ceSpec3.D 4 ![0, 10, 10] -
        ceSpec3.sD ![0, 10, 10] * ceSpec3.mom ceSpec3.B 4 ![0, 10, 10] <
      (ceSpec3.lamk * ceSpec3.lam1 - ceSpec3.lamk1 * ceSpec3.lamd) *
        (ceSpec3.sD ![0, 10, 10] * ceSpec3.sB ![0, 10, 10]) := by
  rw [ceSpec3_sD, ceSpec3_sB, ceSpec3_mom_D, ceSpec3_mom_B, ceSpec3_lam1, ceSpec3_lamk,
    ceSpec3_lamk1, ceSpec3_lamd]
  norm_num

/-- **Sharpness of the corrected Theorem 8**: the bound `η* ≤ 2/(λ_k + λ_d)` is attained for
`λ = (2, 1)`, `x_t = (1, 1)` and vanishing noise (`η* = 2/3`). -/
theorem corrected_thm8_sharp :
    0 < ceSpec2.pCoef (ceIso (Fin 2) 0 le_rfl) ![1, 1] ∧
    ceSpec2.sD ![1, 1] * ceSpec2.eB (ceIso (Fin 2) 0 le_rfl) ≤
      ceSpec2.sB ![1, 1] * ceSpec2.eD (ceIso (Fin 2) 0 le_rfl) ∧
    ceSpec2.etaStar (ceIso (Fin 2) 0 le_rfl) ![1, 1] = 2 / (ceSpec2.lamk + ceSpec2.lamd) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ceSpec2_pCoef]; norm_num [ceIso]
  · rw [ceSpec2_eB, ceSpec2_eD]; norm_num [ceIso]
  · unfold Spec.etaStar
    rw [ceSpec2_pCoef, ceSpec2_qCoef, ceSpec2_lamk, ceSpec2_lamd]
    norm_num [ceIso]

/-! #### Non-vacuity of the main theorems -/

/-- The hypotheses of Theorem 7 (`Spec.etaStar_ge_gap_bound`) and of the Remark
(`Spec.etaStar_ge_gap_bound_normSqD`) are satisfiable: `λ = (2, 1)`, `x_t = (2, 1)`, `Σ = 3 I`
(`p_t = 12 > 0`, `θ_t = 16/17`). -/
example :
    2 * ceSpec2.gap1 /
        ((ceSpec2.lam1 ^ 2 - ceSpec2.lamd ^ 2) +
          (ceIso (Fin 2) 3 (by norm_num)).smax * ceSpec2.psiD /
            (ceSpec2.lamd ^ 2 * Spec.normSq (![2, 1] : Fin 2 → ℝ) * ceSpec2.theta ![2, 1])) ≤
      ceSpec2.etaStar (ceIso (Fin 2) 3 (by norm_num)) ![2, 1] :=
  ceSpec2.etaStar_ge_gap_bound _ (by rw [ceSpec2_pCoef_iso]; norm_num)
    (by rw [ceSpec2_theta]; norm_num)

example :
    2 * ceSpec2.gap1 /
        ((ceSpec2.lam1 ^ 2 - ceSpec2.lamd ^ 2) +
          ceSpec2.lam1 ^ 2 * (ceIso (Fin 2) 3 (by norm_num)).smax * ceSpec2.psiD /
            (ceSpec2.lamk ^ 2 * ceSpec2.lamd ^ 2 * ceSpec2.normSqD ![2, 1])) ≤
      ceSpec2.etaStar (ceIso (Fin 2) 3 (by norm_num)) ![2, 1] :=
  ceSpec2.etaStar_ge_gap_bound_normSqD _ (by rw [ceSpec2_pCoef_iso]; norm_num)
    (by rw [ceSpec2_normSqD]; norm_num)

/-- The hypotheses of the corrected Theorem 8 are satisfiable with non-degenerate noise:
`λ = (10, 2, 1)`, `x_t = (0, 10, 10)`, `Σ = I`. -/
example :
    ceSpec3.etaStar (ceIso (Fin 3) 1 zero_le_one) ![0, 10, 10] ≤
      2 * (ceSpec3.lam1 - ceSpec3.lamd) /
        (ceSpec3.lamk * ceSpec3.lam1 - ceSpec3.lamk1 * ceSpec3.lamd) :=
  ceSpec3.etaStar_le_two_mul_gap_ratio _ cor9_fails_under_corrected_hypothesis.1
    cor9_fails_under_corrected_hypothesis.2.1

/-- The alignment form of the corrected Theorem 8 is non-vacuous as well
(`θ_t = 4/5 ≤ e_𝒟/(e_ℬ + e_𝒟) = 104/105`). -/
example :
    ceSpec3.etaStar (ceIso (Fin 3) 1 zero_le_one) ![0, 10, 10] ≤
      2 * (ceSpec3.lam1 - ceSpec3.lamd) /
        (ceSpec3.lamk * ceSpec3.lam1 - ceSpec3.lamk1 * ceSpec3.lamd) :=
  ceSpec3.etaStar_le_two_mul_gap_ratio_of_theta_le _ cor9_fails_under_corrected_hypothesis.1
    (by rw [ceSpec3_eD, ceSpec3_eB]; norm_num [ceIso])
    (by rw [ceSpec3_eD, ceSpec3_eB, ceSpec3_theta]; norm_num [ceIso])

/-- The hypotheses of the corrected Corollary 9 are satisfiable with non-degenerate noise:
`λ = (2, 1)` (so `λ_1 = 2 ≤ λ_k + λ_d = 3`), `x_t = (1, 1)`, `Σ = I` (`p_t = 12 > 0`,
`s^𝒟 e_ℬ = 4 = s^ℬ e_𝒟`). -/
example : ceSpec2.etaStar (ceIso (Fin 2) 1 zero_le_one) ![1, 1] ≤ 2 / ceSpec2.lam1 :=
  ceSpec2.etaStar_le_two_div_lam1 _ (by rw [ceSpec2_pCoef]; norm_num [ceIso])
    (by rw [ceSpec2_sD, ceSpec2_sB, ceSpec2_eB, ceSpec2_eD]; norm_num [ceIso])
    (by rw [ceSpec2_lam1, ceSpec2_lamk, ceSpec2_lamd]; norm_num)

end EtaStarBounds

end SuspiciousAlignment
