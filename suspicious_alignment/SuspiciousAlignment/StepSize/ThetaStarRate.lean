import Mathlib
import SuspiciousAlignment.Defs

/-!
# Theorem 5 — the rate of the high-alignment threshold `θ*_t`

Paper: Deng et al., *Suspicious Alignment of SGD* (arXiv:2601.11789v2), Theorem 5
("Asymptotic rate of `θ*_t`", tex lines 443–457, proof 1260–1350):

> with `m := λ_k / λ_{k+1} > 1` there are constants `α, β > 0` with
> `1 - β / m² ≤ θ*_t ≤ 1 - α / m²`, i.e. `θ*_t = 1 - Θ(1/m²)`.

For a single fixed problem such an existence statement is trivial, so the content is *which
quantities the constants depend on*.  This file proves the following, all for finite `d` and with
the only extra hypothesis `0 < s_min` (needed for `r_{0,t}` to be the root of a genuine quadratic).

Write `a = s_min ψ_ℬ`, `h = s_max ψ_𝒟`, `M = s_t (λ_1² - λ_d²)` for the coefficients of Theorem 4.

* `Spec.thetaStar_rate_aux_sandwich` — the exact size of `1 - θ*_t`:
  `a / (M + h + a) ≤ 1 - θ*_t < a / (M + h)` (and `1 - θ*_t ≤ a / (a + h)`).
* `Spec.thetaStar_rate_sharp` — in spectral quantities, with
  `β' = ρ s_max / s_min` and `ω_t = s_t / (s_min (d - k))`:
  `1 / (1 + (β' + ω_t) (λ_1/λ_d)²) ≤ 1 - θ*_t < 1 / (β' m² + ω_t (m² - 1))`.
* `Spec.thetaStar_rate` — **Theorem 5 with explicit constants**:
  `α_t / m² ≤ 1 - θ*_t < β / m²` with
  `β = s_min / (ρ s_max)` (`Spec.thetaStarRateBeta`; depends on `ρ, s_min, s_max` only) and
  `α_t = 1 / (1 + (ρ s_max / s_min + s_t / (s_min (d-k))) (λ_1/λ_k)² (λ_{k+1}/λ_d)²)`
  (`Spec.thetaStarRateAlpha`; depends in addition on the state through `s_t`, on `d - k`, and on
  the within-block condition numbers `λ_1/λ_k`, `λ_{k+1}/λ_d`).
* `Spec.thetaStar_rate_one_sub`, `Spec.thetaStar_rate_uniform`,
  `Spec.thetaStar_rate_of_bounded_state`, `Spec.thetaStar_rate_exists` — the same bound on
  `1 - θ*_t`, and its uniform / trajectory-bounded / purely existential forms.
* `thetaStar_rate_isTheta` — the `Θ` form `1 - θ* = Θ(1/m²)` for a family of problems along which
  `ρ s_max/s_min`, `s_t/(s_min (d-k))`, `λ_1/λ_k`, `λ_{k+1}/λ_d` stay bounded.
* `thetaStar_tendsto_one_of_gap` — the paper's interpretation "`θ*_t → 1` as
  `λ_k/λ_{k+1} → ∞`" (needs only `ρ s_max/s_min` bounded below).

The lower bound `θ*_t ≥ 1 - β / m²` is therefore genuinely uniform.  The upper bound
`θ*_t ≤ 1 - α / m²` is **not**: `α` cannot be chosen independently of `s_t`, and the claimed
`m⁻²` rate is false in natural regimes.

* `Spec.thetaStar_rate_energy_bound` — `1 - θ*_t < s_min (d-k) / (s_t (m² - 1))`.
* `Spec.thetaStar_rate_alpha_not_uniform_in_state` — for a fixed problem and every `α > 0` there
  is a state with `θ*_t > 1 - α / m²`.
* `Spec.thetaStar_rate_quartic` — `1 - θ*_t < C / (m² (m² - 1))` with
  `C = s_min (d-k) / (λ_{k+1}² ‖P^𝒟 x_t‖²)`: if `λ_{k+1} = Θ(1)` and the state is fixed, the rate is
  `m⁻⁴`, not `m⁻²`.
* `Spec.thetaStar_rate_trace_bound` — `1 - θ*_t < Tr Σ / ((1+ρ) s_t (m² - 1))`: under the paper's
  Assumption 1 (`Tr Σ` bounded) with `s_t` of order `d`, `θ*_t → 1` at *fixed* `m`.
* `thetaStar_rate_fails_fixed_state` — a concrete three-dimensional family (`λ = (μ, 1, 1)`,
  `𝒟 = {1}`, `Σ = I`, `x = u_1`; every parameter except `m = μ` is fixed) in which
  `1 - θ* < 2 / (μ² (μ² - 1))`, so no `α > 0` works for all `μ`.
* `thetaStar_rate_not_isTheta` — along `A_n = diag(n+2, 1, 1)`, `Σ = I`, `x = u_1`, the function
  `1 - θ*` is not `Θ(1/m²)`.
* `Spec.thetaStar_rate_cond_bound` — `1 - θ*_t ≤ ((d-k) s_min/s_max) / ((λ_1/λ_k)² m²)`: `α` must
  also degrade with the dominant-block condition number.
* `thetaStar_rate_paper_beta_fails` — the constant `β := ρ s_max/s_min` named in the paper's proof
  does not satisfy `1 - β/m² ≤ θ*_t` (it is the reciprocal of the correct constant).

Helper lemmas (facts about `r_{0,t}`, proved locally because the file for Theorem 4 is written
concurrently) live in `namespace SuspiciousAlignment.ThetaStarRate`.
-/

set_option linter.unusedSectionVars false

open Finset

namespace SuspiciousAlignment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace ThetaStarRate

/-! ### Real-variable facts about the quadratic `a r² + b r - h` -/

/-- The quadratic formula: `(-b + √(b² + 4ah)) / (2a)` is a root of `a r² + b r - h`. -/
theorem quad_formula_root {a b h : ℝ} (ha : 0 < a) (hh : 0 < h) :
    a * ((-b + Real.sqrt (b ^ 2 + 4 * a * h)) / (2 * a)) ^ 2
      + b * ((-b + Real.sqrt (b ^ 2 + 4 * a * h)) / (2 * a)) - h = 0 := by
  have hD : (0 : ℝ) ≤ b ^ 2 + 4 * a * h := by positivity
  have hsq := Real.sq_sqrt hD
  generalize Real.sqrt (b ^ 2 + 4 * a * h) = S at hsq ⊢
  field_simp
  linear_combination hsq

/-- The root given by the quadratic formula is positive when `a, h > 0`. -/
theorem quad_formula_root_pos {a b h : ℝ} (ha : 0 < a) (hh : 0 < h) :
    0 < (-b + Real.sqrt (b ^ 2 + 4 * a * h)) / (2 * a) := by
  have hlt : |b| < Real.sqrt (b ^ 2 + 4 * a * h) := by
    rw [Real.lt_sqrt (abs_nonneg b), sq_abs]
    nlinarith [mul_pos ha hh]
  have hb := le_abs_self b
  apply div_pos <;> linarith

/-- Factorisation of the quadratic through one of its roots `r`:
`(a x² + b x - h) r = (x - r) (a x r + h)`. -/
theorem quad_factor {a b h r : ℝ} (x : ℝ) (hr : a * r ^ 2 + b * r - h = 0) :
    (a * x ^ 2 + b * x - h) * r = (x - r) * (a * x * r + h) := by
  linear_combination x * hr

/-- If the quadratic is `≤ 0` at `x ≥ 0`, then `x` is at most the positive root. -/
theorem le_root_of_quad_nonpos {a b h r x : ℝ} (ha : 0 < a) (hh : 0 < h) (hr0 : 0 < r)
    (hr : a * r ^ 2 + b * r - h = 0) (hx : 0 ≤ x) (hq : a * x ^ 2 + b * x - h ≤ 0) : x ≤ r := by
  by_contra hlt
  have hlt := not_le.mp hlt
  have h1 := quad_factor x hr
  have h2 : 0 < (x - r) * (a * x * r + h) := mul_pos (sub_pos.mpr hlt) (by positivity)
  have h3 : (a * x ^ 2 + b * x - h) * r ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hq hr0.le
  linarith

/-- If the quadratic is `< 0` at `x ≥ 0`, then `x` is strictly below the positive root. -/
theorem lt_root_of_quad_neg {a b h r x : ℝ} (ha : 0 < a) (hh : 0 < h) (hr0 : 0 < r)
    (hr : a * r ^ 2 + b * r - h = 0) (hx : 0 ≤ x) (hq : a * x ^ 2 + b * x - h < 0) : x < r := by
  by_contra hle
  have hle := not_lt.mp hle
  have h1 := quad_factor x hr
  have h2 : 0 ≤ (x - r) * (a * x * r + h) := mul_nonneg (sub_nonneg.mpr hle) (by positivity)
  have h3 : (a * x ^ 2 + b * x - h) * r < 0 := mul_neg_of_neg_of_pos hq hr0
  linarith

/-- If the quadratic is `≥ 0` at `x ≥ 0`, then `x` is at least the positive root. -/
theorem root_le_of_quad_nonneg {a b h r x : ℝ} (ha : 0 < a) (hh : 0 < h) (hr0 : 0 < r)
    (hr : a * r ^ 2 + b * r - h = 0) (hx : 0 ≤ x) (hq : 0 ≤ a * x ^ 2 + b * x - h) : r ≤ x := by
  by_contra hlt
  have hlt := not_le.mp hlt
  have h1 := quad_factor x hr
  have h2 : (x - r) * (a * x * r + h) < 0 :=
    mul_neg_of_neg_of_pos (sub_neg.mpr hlt) (by positivity)
  have h3 : 0 ≤ (a * x ^ 2 + b * x - h) * r := mul_nonneg hq hr0.le
  linarith

/-- The value of `a r² + (a - M - h) r - h` at `r = (M + h)/a` is `M`. -/
theorem quad_eval_upper {a M h : ℝ} (ha : a ≠ 0) :
    a * ((M + h) / a) ^ 2 + (a - M - h) * ((M + h) / a) - h = M := by
  field_simp
  ring

/-- The value of `a r² + (a - M - h) r - h` at `r = (M + h)/a - 1` is `-h`. -/
theorem quad_eval_lower {a M h : ℝ} (ha : a ≠ 0) :
    a * ((M + h) / a - 1) ^ 2 + (a - M - h) * ((M + h) / a - 1) - h = -h := by
  field_simp
  ring

/-- The value of `a r² + (a - M - h) r - h` at `r = h/a` is `-(M h / a)`. -/
theorem quad_eval_mid {a M h : ℝ} (ha : a ≠ 0) :
    a * (h / a) ^ 2 + (a - M - h) * (h / a) - h = -(M * h / a) := by
  field_simp
  ring

/-! ### Positivity of the auxiliary coefficients and basic facts about `r_{0,t}`, `θ*_t` -/

/-- `s_max > 0` as soon as `s_min > 0` (the index type is nonempty since `P` exists). -/
theorem smax_pos (P : Spec ι) (N : Noise ι) (hs : 0 < N.smin) : 0 < N.smax :=
  lt_of_lt_of_le hs (le_trans (N.smin_le P.i1) (N.le_smax P.i1))

/-- `a^aux = s_min ψ_ℬ > 0` when `s_min > 0`. -/
theorem aAux_pos (P : Spec ι) (N : Noise ι) (hs : 0 < N.smin) : 0 < P.aAux N :=
  mul_pos hs P.psiB_pos

/-- `h^aux = s_max ψ_𝒟 > 0` when `s_min > 0`. -/
theorem hAux_pos (P : Spec ι) (N : Noise ι) (hs : 0 < N.smin) : 0 < P.hAux N :=
  mul_pos (smax_pos P N hs) P.psiD_pos

/-- `m^aux_t = s_t (λ_1² - λ_d²) ≥ 0`. -/
theorem mAux_nonneg (P : Spec ι) (c : ι → ℝ) : 0 ≤ P.mAux c := by
  unfold Spec.mAux
  have h1 := P.lamd_pos
  have h2 := P.lamd_lt_lam1
  exact mul_nonneg (P.s_nonneg c) (by nlinarith)

/-- `r_{0,t}` is a root of the quadratic of Theorem 4 (unfolded form). -/
theorem auxQuad_r0' (P : Spec ι) (N : Noise ι) (hs : 0 < N.smin) (c : ι → ℝ) :
    P.aAux N * P.r0 N c ^ 2 + (P.aAux N - P.mAux c - P.hAux N) * P.r0 N c - P.hAux N = 0 := by
  unfold Spec.r0
  exact quad_formula_root (aAux_pos P N hs) (hAux_pos P N hs)

/-- `r_{0,t}` is a root of the quadratic `Spec.auxQuad` of Theorem 4. -/
theorem auxQuad_r0 (P : Spec ι) (N : Noise ι) (hs : 0 < N.smin) (c : ι → ℝ) :
    P.auxQuad N c (P.r0 N c) = 0 :=
  auxQuad_r0' P N hs c

/-- `r_{0,t} > 0`. -/
theorem r0_pos (P : Spec ι) (N : Noise ι) (hs : 0 < N.smin) (c : ι → ℝ) : 0 < P.r0 N c := by
  unfold Spec.r0
  exact quad_formula_root_pos (aAux_pos P N hs) (hAux_pos P N hs)

/-- `r_{0,t}` is the *unique* positive root of the quadratic of Theorem 4. -/
theorem eq_r0_of_auxQuad_eq_zero (P : Spec ι) (N : Noise ι) (hs : 0 < N.smin) (c : ι → ℝ)
    {r : ℝ} (hr : 0 < r) (hq : P.auxQuad N c r = 0) : r = P.r0 N c := by
  have ha := aAux_pos P N hs
  have hh := hAux_pos P N hs
  have h0 := r0_pos P N hs c
  have hroot := auxQuad_r0' P N hs c
  unfold Spec.auxQuad at hq
  exact le_antisymm (le_root_of_quad_nonpos ha hh h0 hroot hr.le hq.le)
    (root_le_of_quad_nonneg ha hh h0 hroot hr.le hq.ge)

/-- `1 - θ*_t = 1 / (1 + r_{0,t})`. -/
theorem one_sub_thetaStar (P : Spec ι) (N : Noise ι) (hs : 0 < N.smin) (c : ι → ℝ) :
    1 - P.thetaStar N c = 1 / (1 + P.r0 N c) := by
  have h0 := r0_pos P N hs c
  unfold Spec.thetaStar
  field_simp
  ring

/-- `θ*_t ∈ (0, 1)` (Theorem 4). -/
theorem thetaStar_mem_Ioo (P : Spec ι) (N : Noise ι) (hs : 0 < N.smin) (c : ι → ℝ) :
    P.thetaStar N c ∈ Set.Ioo (0 : ℝ) 1 := by
  have h0 := r0_pos P N hs c
  have h1 := one_sub_thetaStar P N hs c
  have h2 : 0 < 1 / (1 + P.r0 N c) := by positivity
  refine ⟨?_, by linarith⟩
  unfold Spec.thetaStar
  positivity

/-- `r_{0,t} ≤ (m^aux + h^aux) / a^aux`. -/
theorem r0_le (P : Spec ι) (N : Noise ι) (hs : 0 < N.smin) (c : ι → ℝ) :
    P.r0 N c ≤ (P.mAux c + P.hAux N) / P.aAux N := by
  have ha := aAux_pos P N hs
  have hh := hAux_pos P N hs
  have hM := mAux_nonneg P c
  refine root_le_of_quad_nonneg ha hh (r0_pos P N hs c) (auxQuad_r0' P N hs c)
    (div_nonneg (by linarith) ha.le) ?_
  rw [quad_eval_upper ha.ne']
  exact hM

/-- `(m^aux + h^aux) / a^aux < 1 + r_{0,t}`. -/
theorem lt_one_add_r0 (P : Spec ι) (N : Noise ι) (hs : 0 < N.smin) (c : ι → ℝ) :
    (P.mAux c + P.hAux N) / P.aAux N < 1 + P.r0 N c := by
  have ha := aAux_pos P N hs
  have hh := hAux_pos P N hs
  have h0 := r0_pos P N hs c
  rcases le_or_gt 0 ((P.mAux c + P.hAux N) / P.aAux N - 1) with hx | hx
  · have := lt_root_of_quad_neg ha hh h0 (auxQuad_r0' P N hs c) hx
      (by rw [quad_eval_lower ha.ne']; linarith)
    linarith
  · linarith

/-- `h^aux / a^aux ≤ r_{0,t}` (with equality iff `m^aux_t = 0`). -/
theorem hAux_div_aAux_le_r0 (P : Spec ι) (N : Noise ι) (hs : 0 < N.smin) (c : ι → ℝ) :
    P.hAux N / P.aAux N ≤ P.r0 N c := by
  have ha := aAux_pos P N hs
  have hh := hAux_pos P N hs
  have hM := mAux_nonneg P c
  refine le_root_of_quad_nonpos ha hh (r0_pos P N hs c) (auxQuad_r0' P N hs c)
    (div_nonneg hh.le ha.le) ?_
  rw [quad_eval_mid ha.ne']
  have : 0 ≤ P.mAux c * P.hAux N / P.aAux N := by positivity
  linarith

/-! ### Elementary spectral bounds -/

/-- `ψ_ℬ ≤ (d - k) λ_{k+1}²`. -/
theorem psiB_le (P : Spec ι) : P.psiB ≤ P.dkR * P.lamk1 ^ 2 := by
  unfold Spec.psiB Spec.dkR
  have h := Finset.sum_le_card_nsmul P.B (fun i => P.lam i ^ 2) (P.lamk1 ^ 2)
    (fun i hi => pow_le_pow_left₀ (P.lam_pos i).le (P.le_lamk1_of_mem_B hi) 2)
  simpa [nsmul_eq_mul] using h

/-- `(d - k) λ_d² ≤ ψ_ℬ`. -/
theorem le_psiB (P : Spec ι) : P.dkR * P.lamd ^ 2 ≤ P.psiB := by
  unfold Spec.psiB Spec.dkR
  have h := Finset.card_nsmul_le_sum P.B (fun i => P.lam i ^ 2) (P.lamd ^ 2)
    (fun i hi => pow_le_pow_left₀ P.lamd_pos.le (P.lamd_le_of_mem_B hi) 2)
  simpa [nsmul_eq_mul] using h

/-- `ψ_𝒟 ≤ k λ_1²`. -/
theorem psiD_le (P : Spec ι) : P.psiD ≤ P.kR * P.lam1 ^ 2 := by
  unfold Spec.psiD Spec.kR
  have h := Finset.sum_le_card_nsmul P.D (fun i => P.lam i ^ 2) (P.lam1 ^ 2)
    (fun i hi => pow_le_pow_left₀ (P.lam_pos i).le (P.le_lam1_of_mem hi) 2)
  simpa [nsmul_eq_mul] using h

/-- `k λ_k² ≤ ψ_𝒟`. -/
theorem le_psiD (P : Spec ι) : P.kR * P.lamk ^ 2 ≤ P.psiD := by
  unfold Spec.psiD Spec.kR
  have h := Finset.card_nsmul_le_sum P.D (fun i => P.lam i ^ 2) (P.lamk ^ 2)
    (fun i hi => pow_le_pow_left₀ P.lamk_pos.le (P.lamk_le_of_mem hi) 2)
  simpa [nsmul_eq_mul] using h

/-- `λ_k² ‖P^𝒟 x‖² ≤ s_t`. -/
theorem lamk_sq_mul_normSqD_le_s (P : Spec ι) (c : ι → ℝ) :
    P.lamk ^ 2 * P.normSqD c ≤ P.s c := by
  have h1 : P.lamk ^ 2 * P.normSqD c ≤ P.sD c := by
    unfold Spec.normSqD Spec.sD Spec.mom
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ P.lamk_pos.le (P.lamk_le_of_mem hi) 2)
        (sq_nonneg _)
  have h2 := P.sB_nonneg c
  unfold Spec.s
  linarith

/-- `s_t ≤ λ_1² ‖x‖²`. -/
theorem s_le_lam1_sq_mul_normSq (P : Spec ι) (c : ι → ℝ) :
    P.s c ≤ P.lam1 ^ 2 * Spec.normSq c := by
  rw [P.s_eq_sum]
  unfold Spec.normSq
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (P.lam_pos i).le (P.le_lam1_all i) 2)
      (sq_nonneg _)

/-- `k + (d - k) = d`. -/
theorem kR_add_dkR (P : Spec ι) : P.kR + P.dkR = (Fintype.card ι : ℝ) := by
  unfold Spec.kR Spec.dkR Spec.B
  exact_mod_cast Finset.card_add_card_compl P.D

/-- `d · s_min ≤ ∑_i κ_i² = Tr Σ`. -/
theorem card_mul_smin_le_trace (N : Noise ι) :
    (Fintype.card ι : ℝ) * N.smin ≤ ∑ i, N.kap2 i := by
  have h := Finset.card_nsmul_le_sum (Finset.univ : Finset ι) N.kap2 N.smin
    (fun i _ => N.smin_le i)
  simpa [nsmul_eq_mul] using h

/-! ### The ratio `(m^aux + h^aux) / a^aux` in spectral quantities -/

/-- Upper bound: `(m^aux + h^aux)/a^aux ≤ (ρ s_max/s_min + s_t/(s_min (d-k))) (λ_1/λ_d)²`. -/
theorem aux_ratio_le (P : Spec ι) (N : Noise ι) (hs : 0 < N.smin) (c : ι → ℝ) :
    (P.mAux c + P.hAux N) / P.aAux N ≤
      (P.rho * N.smax / N.smin + P.s c / (N.smin * P.dkR)) * (P.lam1 / P.lamd) ^ 2 := by
  have hk := P.kR_pos
  have hn := P.dkR_pos
  have hd := P.lamd_pos
  have h1 := P.lam1_pos
  have hsmax := smax_pos P N hs
  have hsc := P.s_nonneg c
  have hRHS : (P.rho * N.smax / N.smin + P.s c / (N.smin * P.dkR)) * (P.lam1 / P.lamd) ^ 2
      = ((P.kR * N.smax + P.s c) * P.lam1 ^ 2) / (N.smin * (P.dkR * P.lamd ^ 2)) := by
    unfold Spec.rho
    field_simp
  rw [hRHS]
  apply div_le_div₀
  · positivity
  · unfold Spec.mAux Spec.hAux
    have e1 : P.s c * (P.lam1 ^ 2 - P.lamd ^ 2) ≤ P.s c * P.lam1 ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) hsc
    have e2 : N.smax * P.psiD ≤ N.smax * (P.kR * P.lam1 ^ 2) :=
      mul_le_mul_of_nonneg_left (psiD_le P) hsmax.le
    linarith
  · positivity
  · unfold Spec.aAux
    exact mul_le_mul_of_nonneg_left (le_psiB P) hs.le

/-- Lower bound:
`ρ s_max/s_min · m² + s_t/(s_min (d-k)) · (m² - 1) ≤ (m^aux + h^aux)/a^aux`. -/
theorem le_aux_ratio (P : Spec ι) (N : Noise ι) (hs : 0 < N.smin) (c : ι → ℝ) :
    P.rho * N.smax / N.smin * P.mRatio ^ 2 + P.s c / (N.smin * P.dkR) * (P.mRatio ^ 2 - 1) ≤
      (P.mAux c + P.hAux N) / P.aAux N := by
  have hk := P.kR_pos
  have hn := P.dkR_pos
  have hk1 := P.lamk1_pos
  have hsmax := smax_pos P N hs
  have hsc := P.s_nonneg c
  have hLHS : P.rho * N.smax / N.smin * P.mRatio ^ 2
        + P.s c / (N.smin * P.dkR) * (P.mRatio ^ 2 - 1)
      = (P.kR * N.smax * P.lamk ^ 2 + P.s c * (P.lamk ^ 2 - P.lamk1 ^ 2))
          / (N.smin * (P.dkR * P.lamk1 ^ 2)) := by
    unfold Spec.rho Spec.mRatio
    field_simp
  rw [hLHS]
  apply div_le_div₀
  · exact add_nonneg (mAux_nonneg P c) (hAux_pos P N hs).le
  · unfold Spec.mAux Spec.hAux
    have e1 : P.s c * (P.lamk ^ 2 - P.lamk1 ^ 2) ≤ P.s c * (P.lam1 ^ 2 - P.lamd ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hsc
      have a1 := P.lamk_le_lam1
      have a2 := P.lamd_le_lamk1
      have a3 := P.lamk_pos
      have a4 := P.lamd_pos
      nlinarith
    have e2 : N.smax * (P.kR * P.lamk ^ 2) ≤ N.smax * P.psiD :=
      mul_le_mul_of_nonneg_left (le_psiD P) hsmax.le
    linarith
  · exact aAux_pos P N hs
  · unfold Spec.aAux
    exact mul_le_mul_of_nonneg_left (psiB_le P) hs.le

/-- `(λ_1/λ_d)² = (λ_1/λ_k)² (λ_{k+1}/λ_d)² m²`: the global condition number factors through the
two within-block condition numbers and the gap ratio `m = λ_k/λ_{k+1}`. -/
theorem cond_sq_eq_mul_mRatio_sq (P : Spec ι) :
    (P.lam1 / P.lamd) ^ 2 = (P.lam1 / P.lamk) ^ 2 * (P.lamk1 / P.lamd) ^ 2 * P.mRatio ^ 2 := by
  have h1 := P.lamk_pos
  have h2 := P.lamk1_pos
  have h3 := P.lamd_pos
  unfold Spec.mRatio
  field_simp

end ThetaStarRate

namespace Spec

open ThetaStarRate

variable (P : Spec ι) (N : Noise ι)

/-! ### The constants of Theorem 5 -/

/-- The constant `β = s_min / (ρ s_max)` in the lower bound `θ*_t ≥ 1 - β / m²` of Theorem 5.
It depends only on the block proportion `ρ` and the noise conditioning `s_max / s_min`.
(The paper's proof names `β := ρ s_max / s_min`, the reciprocal; with that value the bound is
false, see the fidelity note.) -/
noncomputable def thetaStarRateBeta : ℝ := N.smin / (P.rho * N.smax)

/-- The (state-dependent) constant
`α_t = 1 / (1 + (ρ s_max / s_min + s_t / (s_min (d-k))) (λ_1/λ_k)² (λ_{k+1}/λ_d)²)`
in the upper bound `θ*_t ≤ 1 - α_t / m²` of Theorem 5.  It depends on `ρ`, `s_max/s_min`, the
gradient energy per bulk direction relative to the noise floor `s_t / (s_min (d-k))`, and the
within-block condition numbers `λ_1/λ_k` and `λ_{k+1}/λ_d`. -/
noncomputable def thetaStarRateAlpha (c : ι → ℝ) : ℝ :=
  1 / (1 + (P.rho * N.smax / N.smin + P.s c / (N.smin * P.dkR))
            * (P.lam1 / P.lamk) ^ 2 * (P.lamk1 / P.lamd) ^ 2)

theorem thetaStarRateBeta_pos (hs : 0 < N.smin) : 0 < P.thetaStarRateBeta N :=
  div_pos hs (mul_pos P.rho_pos (smax_pos P N hs))

theorem thetaStarRateAlpha_pos (hs : 0 < N.smin) (c : ι → ℝ) : 0 < P.thetaStarRateAlpha N c := by
  have h1 := P.rho_pos
  have h2 := smax_pos P N hs
  have h3 := P.s_nonneg c
  have h4 := P.dkR_pos
  have h5 := P.lam1_pos
  have h6 := P.lamk_pos
  have h7 := P.lamk1_pos
  have h8 := P.lamd_pos
  unfold thetaStarRateAlpha
  positivity

/-- `α_t ≤ 1`: the two bounds of Theorem 5 never contradict `θ*_t > 0`. -/
theorem thetaStarRateAlpha_le_one (hs : 0 < N.smin) (c : ι → ℝ) :
    P.thetaStarRateAlpha N c ≤ 1 := by
  have h1 := P.rho_pos
  have h2 := smax_pos P N hs
  have h3 := P.s_nonneg c
  have h4 := P.dkR_pos
  have h5 := P.lam1_pos
  have h6 := P.lamk_pos
  have h7 := P.lamk1_pos
  have h8 := P.lamd_pos
  unfold thetaStarRateAlpha
  rw [div_le_one (by positivity)]
  have : 0 ≤ (P.rho * N.smax / N.smin + P.s c / (N.smin * P.dkR))
      * (P.lam1 / P.lamk) ^ 2 * (P.lamk1 / P.lamd) ^ 2 := by positivity
  linarith

/-! ### Two-sided bounds on `1 - θ*_t` -/

/-- **Exact size of `1 - θ*_t`** (the core of Theorem 5).  With `a = s_min ψ_ℬ`,
`h = s_max ψ_𝒟`, `M = s_t (λ_1² - λ_d²)` the coefficients of Theorem 4,
`a / (M + h + a) ≤ 1 - θ*_t < a / (M + h)` and `1 - θ*_t ≤ a / (a + h)`. -/
theorem thetaStar_rate_aux_sandwich (hs : 0 < N.smin) (c : ι → ℝ) :
    P.aAux N / (P.mAux c + P.hAux N + P.aAux N) ≤ 1 - P.thetaStar N c ∧
      1 - P.thetaStar N c < P.aAux N / (P.mAux c + P.hAux N) ∧
      1 - P.thetaStar N c ≤ P.aAux N / (P.aAux N + P.hAux N) := by
  have ha := aAux_pos P N hs
  have hh := hAux_pos P N hs
  have hM := mAux_nonneg P c
  have h0 := r0_pos P N hs c
  have hle := r0_le P N hs c
  have hlt := lt_one_add_r0 P N hs c
  have hmid := hAux_div_aAux_le_r0 P N hs c
  rw [le_div_iff₀ ha] at hle
  rw [div_lt_iff₀ ha] at hlt
  rw [div_le_iff₀ ha] at hmid
  rw [one_sub_thetaStar P N hs c]
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  · rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  · rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith

/-- **Sharp two-sided bound in spectral quantities.**  With `β' = ρ s_max / s_min` and
`ω_t = s_t / (s_min (d-k))`,
`1 / (1 + (β' + ω_t) (λ_1/λ_d)²) ≤ 1 - θ*_t < 1 / (β' m² + ω_t (m² - 1))`.
When both blocks are flat (`λ_1 = λ_k`, `λ_{k+1} = λ_d`), `(λ_1/λ_d)² = m²` and the two sides
differ only by the `1 + ω_t` in the denominator. -/
theorem thetaStar_rate_sharp (hs : 0 < N.smin) (c : ι → ℝ) :
    1 / (1 + (P.rho * N.smax / N.smin + P.s c / (N.smin * P.dkR)) * (P.lam1 / P.lamd) ^ 2)
        ≤ 1 - P.thetaStar N c ∧
      1 - P.thetaStar N c
        < 1 / (P.rho * N.smax / N.smin * P.mRatio ^ 2
                + P.s c / (N.smin * P.dkR) * (P.mRatio ^ 2 - 1)) := by
  have h0 := r0_pos P N hs c
  rw [one_sub_thetaStar P N hs c]
  constructor
  · apply one_div_le_one_div_of_le (by linarith)
    have e1 := r0_le P N hs c
    have e2 := aux_ratio_le P N hs c
    linarith
  · apply one_div_lt_one_div_of_lt
    · have h1 := P.rho_pos
      have h2 := smax_pos P N hs
      have h3 := P.s_nonneg c
      have h4 := P.dkR_pos
      have h5 := P.one_lt_mRatio
      have h6 : 0 < P.rho * N.smax / N.smin * P.mRatio ^ 2 := by positivity
      have h7 : 0 ≤ P.s c / (N.smin * P.dkR) := by positivity
      have h8 : 0 ≤ P.mRatio ^ 2 - 1 := by nlinarith
      have h9 := mul_nonneg h7 h8
      linarith
    · have e1 := lt_one_add_r0 P N hs c
      have e2 := le_aux_ratio P N hs c
      linarith

/-- **Theorem 5 (asymptotic rate of `θ*_t`), with explicit constants.**
For `m = λ_k/λ_{k+1} > 1` and `s_min > 0`,
`1 - β / m² < θ*_t ≤ 1 - α_t / m²` with
`β = s_min / (ρ s_max)` (`Spec.thetaStarRateBeta`) and
`α_t = 1 / (1 + (ρ s_max/s_min + s_t/(s_min (d-k))) (λ_1/λ_k)² (λ_{k+1}/λ_d)²)`
(`Spec.thetaStarRateAlpha`).  `β` is state-independent; `α_t` depends on the state through
`s_t` — this dependence cannot be removed (`Spec.thetaStar_rate_alpha_not_uniform_in_state`). -/
theorem thetaStar_rate (hs : 0 < N.smin) (c : ι → ℝ) :
    0 < P.thetaStarRateAlpha N c ∧ 0 < P.thetaStarRateBeta N ∧
      1 - P.thetaStarRateBeta N / P.mRatio ^ 2 < P.thetaStar N c ∧
      P.thetaStar N c ≤ 1 - P.thetaStarRateAlpha N c / P.mRatio ^ 2 := by
  have hm := P.one_lt_mRatio
  have hm2 : 1 ≤ P.mRatio ^ 2 := by nlinarith
  have hρ := P.rho_pos
  have hsmax := smax_pos P N hs
  have hsc := P.s_nonneg c
  have hn := P.dkR_pos
  obtain ⟨hlo, hhi⟩ := P.thetaStar_rate_sharp N hs c
  refine ⟨P.thetaStarRateAlpha_pos N hs c, P.thetaStarRateBeta_pos N hs, ?_, ?_⟩
  · -- `1 - θ* < 1 / (β' m² + ω (m² - 1)) ≤ 1 / (β' m²) = β / m²`
    have hβ' : 0 < P.rho * N.smax / N.smin * P.mRatio ^ 2 := by positivity
    have hω : 0 ≤ P.s c / (N.smin * P.dkR) * (P.mRatio ^ 2 - 1) :=
      mul_nonneg (by positivity) (by linarith)
    have e1 : 1 / (P.rho * N.smax / N.smin * P.mRatio ^ 2
                + P.s c / (N.smin * P.dkR) * (P.mRatio ^ 2 - 1))
        ≤ 1 / (P.rho * N.smax / N.smin * P.mRatio ^ 2) :=
      one_div_le_one_div_of_le hβ' (by linarith)
    have e2 : 1 / (P.rho * N.smax / N.smin * P.mRatio ^ 2)
        = P.thetaStarRateBeta N / P.mRatio ^ 2 := by
      unfold thetaStarRateBeta
      field_simp
    linarith
  · -- `α / m² = 1 / ((1 + A) m²) ≤ 1 / (1 + A m²) ≤ 1 - θ*`
    set A : ℝ := (P.rho * N.smax / N.smin + P.s c / (N.smin * P.dkR))
            * (P.lam1 / P.lamk) ^ 2 * (P.lamk1 / P.lamd) ^ 2 with hA
    have hApos : 0 ≤ A := by
      have h5 := P.lam1_pos
      have h6 := P.lamk_pos
      have h7 := P.lamk1_pos
      have h8 := P.lamd_pos
      rw [hA]
      positivity
    have e0 : (P.rho * N.smax / N.smin + P.s c / (N.smin * P.dkR)) * (P.lam1 / P.lamd) ^ 2
        = A * P.mRatio ^ 2 := by
      rw [cond_sq_eq_mul_mRatio_sq P, hA]
      ring
    rw [e0] at hlo
    have e1 : P.thetaStarRateAlpha N c / P.mRatio ^ 2 = 1 / ((1 + A) * P.mRatio ^ 2) := by
      unfold thetaStarRateAlpha
      rw [← hA]
      field_simp
    have e2 : 1 / ((1 + A) * P.mRatio ^ 2) ≤ 1 / (1 + A * P.mRatio ^ 2) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    linarith

/-- **Theorem 5, literal (existential) form**: there are `α, β > 0` with
`1 - β / m² ≤ θ*_t ≤ 1 - α / m²`.  (For one fixed problem and state; see `Spec.thetaStar_rate` for
what `α, β` are.) -/
theorem thetaStar_rate_exists (hs : 0 < N.smin) (c : ι → ℝ) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
      1 - β / P.mRatio ^ 2 ≤ P.thetaStar N c ∧ P.thetaStar N c ≤ 1 - α / P.mRatio ^ 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := P.thetaStar_rate N hs c
  exact ⟨_, _, h1, h2, h3.le, h4⟩

/-- **Theorem 5 as a two-sided bound on `1 - θ*_t`**: `α_t / m² ≤ 1 - θ*_t < β / m²`, with the
explicit constants `Spec.thetaStarRateAlpha` and `Spec.thetaStarRateBeta`. -/
theorem thetaStar_rate_one_sub (hs : 0 < N.smin) (c : ι → ℝ) :
    P.thetaStarRateAlpha N c / P.mRatio ^ 2 ≤ 1 - P.thetaStar N c ∧
      1 - P.thetaStar N c < P.thetaStarRateBeta N / P.mRatio ^ 2 := by
  obtain ⟨-, -, h3, h4⟩ := P.thetaStar_rate N hs c
  constructor <;> linarith

/-- **Theorem 5, uniform form** (`θ*_t = 1 - Θ(1/m²)` with constants depending only on bounds for
five named quantities).  If
`R₁ ≤ ρ s_max / s_min ≤ R₂`, `s_t / (s_min (d-k)) ≤ Ω`, `λ_1/λ_k ≤ K_𝒟`, `λ_{k+1}/λ_d ≤ K_ℬ`, then
`(1 / (1 + (R₂ + Ω) K_𝒟² K_ℬ²)) / m² ≤ 1 - θ*_t < (1 / R₁) / m²`. -/
theorem thetaStar_rate_uniform (hs : 0 < N.smin) (c : ι → ℝ) {R₁ R₂ Ω KD KB : ℝ}
    (hR₁ : 0 < R₁) (hR₁' : R₁ ≤ P.rho * N.smax / N.smin) (hR₂ : P.rho * N.smax / N.smin ≤ R₂)
    (hΩ : P.s c / (N.smin * P.dkR) ≤ Ω) (hKD : P.lam1 / P.lamk ≤ KD)
    (hKB : P.lamk1 / P.lamd ≤ KB) :
    (1 / (1 + (R₂ + Ω) * KD ^ 2 * KB ^ 2)) / P.mRatio ^ 2 ≤ 1 - P.thetaStar N c ∧
      1 - P.thetaStar N c < (1 / R₁) / P.mRatio ^ 2 := by
  have hm := P.one_lt_mRatio
  have hm2 : 0 < P.mRatio ^ 2 := by positivity
  have hρ := P.rho_pos
  have hsmax := smax_pos P N hs
  have hsc := P.s_nonneg c
  have hn := P.dkR_pos
  have h5 := P.lam1_pos
  have h6 := P.lamk_pos
  have h7 := P.lamk1_pos
  have h8 := P.lamd_pos
  obtain ⟨-, -, hβ, hα⟩ := P.thetaStar_rate N hs c
  have hr : 0 < P.rho * N.smax / N.smin := by positivity
  have hω : 0 ≤ P.s c / (N.smin * P.dkR) := by positivity
  have hκD : 0 ≤ P.lam1 / P.lamk := by positivity
  have hκB : 0 ≤ P.lamk1 / P.lamd := by positivity
  constructor
  · have hA : (P.rho * N.smax / N.smin + P.s c / (N.smin * P.dkR))
          * (P.lam1 / P.lamk) ^ 2 * (P.lamk1 / P.lamd) ^ 2
        ≤ (R₂ + Ω) * KD ^ 2 * KB ^ 2 := by
      have i1 : P.rho * N.smax / N.smin + P.s c / (N.smin * P.dkR) ≤ R₂ + Ω := by linarith
      have i2 : (P.lam1 / P.lamk) ^ 2 ≤ KD ^ 2 := pow_le_pow_left₀ hκD hKD 2
      have i3 : (P.lamk1 / P.lamd) ^ 2 ≤ KB ^ 2 := pow_le_pow_left₀ hκB hKB 2
      have i4 : 0 ≤ P.rho * N.smax / N.smin + P.s c / (N.smin * P.dkR) := by linarith
      exact mul_le_mul (mul_le_mul i1 i2 (by positivity) (by linarith)) i3 (by positivity)
        (mul_nonneg (by linarith) (by positivity))
    have hαle : 1 / (1 + (R₂ + Ω) * KD ^ 2 * KB ^ 2) ≤ P.thetaStarRateAlpha N c := by
      unfold thetaStarRateAlpha
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have := div_le_div_of_nonneg_right hαle hm2.le
    linarith
  · have hβle : P.thetaStarRateBeta N ≤ 1 / R₁ := by
      have e : P.thetaStarRateBeta N = 1 / (P.rho * N.smax / N.smin) := by
        unfold thetaStarRateBeta
        field_simp
      rw [e]
      exact one_div_le_one_div_of_le hR₁ hR₁'
    have := div_le_div_of_nonneg_right hβle hm2.le
    linarith

/-- **Theorem 5 under the trajectory-boundedness part of Assumption 1.**  If
`‖x_t‖² ≤ C d`, then `s_t / (s_min (d-k)) ≤ (1 + ρ) C λ_1² / s_min`, hence
`θ*_t ≤ 1 - α_C / m²` with
`α_C = 1 / (1 + (ρ s_max/s_min + (1+ρ) C λ_1²/s_min) (λ_1/λ_k)² (λ_{k+1}/λ_d)²)`.
Note that `α_C` still involves `λ_1² / s_min`, which Assumption 1 does not control. -/
theorem thetaStar_rate_of_bounded_state (hs : 0 < N.smin) (c : ι → ℝ) {C : ℝ}
    (hC : Spec.normSq c ≤ C * (Fintype.card ι : ℝ)) :
    (1 / (1 + (P.rho * N.smax / N.smin + (1 + P.rho) * C * P.lam1 ^ 2 / N.smin)
            * (P.lam1 / P.lamk) ^ 2 * (P.lamk1 / P.lamd) ^ 2)) / P.mRatio ^ 2
        ≤ 1 - P.thetaStar N c := by
  have hk := P.kR_pos
  have hn := P.dkR_pos
  have hρ := P.rho_pos
  have hsmax := smax_pos P N hs
  have hΩ : P.s c / (N.smin * P.dkR) ≤ (1 + P.rho) * C * P.lam1 ^ 2 / N.smin := by
    have e : (1 + P.rho) * C * P.lam1 ^ 2 / N.smin
        = P.lam1 ^ 2 * (C * (P.kR + P.dkR)) / (N.smin * P.dkR) := by
      unfold rho
      field_simp
      ring
    rw [e]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have e1 := s_le_lam1_sq_mul_normSq P c
    have e2 : P.lam1 ^ 2 * Spec.normSq c ≤ P.lam1 ^ 2 * (C * (P.kR + P.dkR)) := by
      rw [kR_add_dkR P]
      exact mul_le_mul_of_nonneg_left hC (by positivity)
    linarith
  have hr : 0 < P.rho * N.smax / N.smin := by positivity
  exact (P.thetaStar_rate_uniform N hs c hr le_rfl le_rfl hΩ le_rfl le_rfl).1

/-! ### The constant `α` cannot be uniform: dependence on `s_t`, and the `m⁻⁴` regime -/

/-- `1 - θ*_t < s_min (d-k) / (s_t (m² - 1))`: at fixed spectrum and noise, `θ*_t → 1` as the
gradient energy `s_t = ‖A x_t‖²` grows. -/
theorem thetaStar_rate_energy_bound (hs : 0 < N.smin) (c : ι → ℝ) (hc : 0 < P.s c) :
    1 - P.thetaStar N c < N.smin * P.dkR / (P.s c * (P.mRatio ^ 2 - 1)) := by
  have hm := P.one_lt_mRatio
  have hm2 : 0 < P.mRatio ^ 2 - 1 := by nlinarith
  have hρ := P.rho_pos
  have hsmax := smax_pos P N hs
  have hn := P.dkR_pos
  obtain ⟨-, hhi⟩ := P.thetaStar_rate_sharp N hs c
  have hβ' : 0 ≤ P.rho * N.smax / N.smin * P.mRatio ^ 2 := by positivity
  have hω : 0 < P.s c / (N.smin * P.dkR) * (P.mRatio ^ 2 - 1) := by positivity
  have e1 : 1 / (P.rho * N.smax / N.smin * P.mRatio ^ 2
                + P.s c / (N.smin * P.dkR) * (P.mRatio ^ 2 - 1))
        ≤ 1 / (P.s c / (N.smin * P.dkR) * (P.mRatio ^ 2 - 1)) :=
    one_div_le_one_div_of_le hω (by linarith)
  have e2 : 1 / (P.s c / (N.smin * P.dkR) * (P.mRatio ^ 2 - 1))
      = N.smin * P.dkR / (P.s c * (P.mRatio ^ 2 - 1)) := by
    field_simp
  linarith

/-- For every `α > 0`, every state with gradient energy
`s_t ≥ s_min (d-k) m² / (α (m² - 1))` has `θ*_t > 1 - α / m²`. -/
theorem thetaStar_rate_gt_of_energy_large (hs : 0 < N.smin) {α : ℝ} (hα : 0 < α) (c : ι → ℝ)
    (hc : N.smin * P.dkR * P.mRatio ^ 2 / (α * (P.mRatio ^ 2 - 1)) ≤ P.s c) :
    1 - α / P.mRatio ^ 2 < P.thetaStar N c := by
  have hm := P.one_lt_mRatio
  have hm2 : 0 < P.mRatio ^ 2 - 1 := by nlinarith
  have hn := P.dkR_pos
  have hpos : 0 < N.smin * P.dkR * P.mRatio ^ 2 / (α * (P.mRatio ^ 2 - 1)) := by positivity
  have hsc : 0 < P.s c := lt_of_lt_of_le hpos hc
  have h1 := P.thetaStar_rate_energy_bound N hs c hsc
  have h2 : N.smin * P.dkR / (P.s c * (P.mRatio ^ 2 - 1)) ≤ α / P.mRatio ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hc
    nlinarith
  linarith

/-- **The constant `α` of Theorem 5 cannot be chosen independently of the state.**  For a fixed
problem `(A, Σ)` and every `α > 0` there is a state `x_t` whose threshold violates the paper's
upper bound: `θ*_t > 1 - α / m²`. -/
theorem thetaStar_rate_alpha_not_uniform_in_state (hs : 0 < N.smin) {α : ℝ} (hα : 0 < α) :
    ∃ c : ι → ℝ, 1 - α / P.mRatio ^ 2 < P.thetaStar N c := by
  have hm := P.one_lt_mRatio
  have hm2 : 0 < P.mRatio ^ 2 - 1 := by nlinarith
  have hn := P.dkR_pos
  set S : ℝ := N.smin * P.dkR * P.mRatio ^ 2 / (α * (P.mRatio ^ 2 - 1)) with hS
  have hSpos : 0 < S := by positivity
  have hΛ : 0 < ∑ i : ι, P.lam i ^ 2 :=
    Finset.sum_pos (fun i _ => pow_pos (P.lam_pos i) 2) ⟨P.i1, Finset.mem_univ _⟩
  set t : ℝ := S / (∑ i : ι, P.lam i ^ 2) + 1 with ht
  have ht1 : 1 ≤ t := by
    have : 0 ≤ S / (∑ i : ι, P.lam i ^ 2) := by positivity
    linarith
  refine ⟨fun _ => t, P.thetaStar_rate_gt_of_energy_large N hs hα _ ?_⟩
  rw [← hS, P.s_eq_sum, ← Finset.sum_mul]
  have e1 : S = (∑ i : ι, P.lam i ^ 2) * (S / (∑ i : ι, P.lam i ^ 2)) := by
    field_simp
  have e2 : S / (∑ i : ι, P.lam i ^ 2) ≤ t ^ 2 := by nlinarith
  calc S = (∑ i : ι, P.lam i ^ 2) * (S / (∑ i : ι, P.lam i ^ 2)) := e1
    _ ≤ (∑ i : ι, P.lam i ^ 2) * t ^ 2 := mul_le_mul_of_nonneg_left e2 hΛ.le

/-- **The `m⁻⁴` regime.**  If the state has a non-zero dominant component, then
`1 - θ*_t < C / (m² (m² - 1))` with `C = s_min (d-k) / (λ_{k+1}² ‖P^𝒟 x_t‖²)`.
`C` does not involve `λ_k`: when the gap ratio `m` grows through `λ_k → ∞` with
`λ_{k+1} = Θ(1)` and the state fixed, `1 - θ*_t = O(m⁻⁴)`, contradicting `1 - θ*_t = Θ(m⁻²)`. -/
theorem thetaStar_rate_quartic (hs : 0 < N.smin) (c : ι → ℝ) (hc : 0 < P.normSqD c) :
    1 - P.thetaStar N c
      < N.smin * P.dkR / (P.lamk1 ^ 2 * P.normSqD c) / (P.mRatio ^ 2 * (P.mRatio ^ 2 - 1)) := by
  have hm := P.one_lt_mRatio
  have hm2 : 0 < P.mRatio ^ 2 - 1 := by nlinarith
  have hn := P.dkR_pos
  have hk := P.lamk_pos
  have hk1 := P.lamk1_pos
  have hs1 := lamk_sq_mul_normSqD_le_s P c
  have hpos : 0 < P.lamk ^ 2 * P.normSqD c := by positivity
  have hsc : 0 < P.s c := lt_of_lt_of_le hpos hs1
  have h1 := P.thetaStar_rate_energy_bound N hs c hsc
  have h2 : N.smin * P.dkR / (P.s c * (P.mRatio ^ 2 - 1))
      ≤ N.smin * P.dkR / (P.lamk ^ 2 * P.normSqD c * (P.mRatio ^ 2 - 1)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_right hs1 hm2.le)
  have h3 : N.smin * P.dkR / (P.lamk ^ 2 * P.normSqD c * (P.mRatio ^ 2 - 1))
      = N.smin * P.dkR / (P.lamk1 ^ 2 * P.normSqD c)
          / (P.mRatio ^ 2 * (P.mRatio ^ 2 - 1)) := by
    have hmk : P.lamk = P.mRatio * P.lamk1 := by
      unfold mRatio
      field_simp
    rw [hmk]
    field_simp
  linarith

/-- **Dependence on the dominant-block condition number.**
`1 - θ*_t ≤ ((d-k) s_min / s_max) / ((λ_1/λ_k)² m²)`, for every state.  Hence any `α` with
`θ*_t ≤ 1 - α/m²` satisfies `α ≤ (d-k) (s_min/s_max) / (λ_1/λ_k)²`: it cannot depend on
`ρ, s_min, s_max, d - k` alone, it must degrade with the spread `λ_1/λ_k` of the dominant block. -/
theorem thetaStar_rate_cond_bound (hs : 0 < N.smin) (c : ι → ℝ) :
    1 - P.thetaStar N c
      ≤ N.smin * P.dkR / N.smax / ((P.lam1 / P.lamk) ^ 2 * P.mRatio ^ 2) := by
  have ha := aAux_pos P N hs
  have hh := hAux_pos P N hs
  have hsmax := smax_pos P N hs
  have hn := P.dkR_pos
  have h1 := P.lam1_pos
  have hk := P.lamk_pos
  have hk1 := P.lamk1_pos
  obtain ⟨-, -, hmid⟩ := P.thetaStar_rate_aux_sandwich N hs c
  have e1 : P.aAux N / (P.aAux N + P.hAux N) ≤ P.aAux N / P.hAux N :=
    div_le_div_of_nonneg_left ha.le hh (by linarith)
  have hψD : P.lam1 ^ 2 ≤ P.psiD := by
    unfold psiD lam1
    exact Finset.single_le_sum (f := fun i => P.lam i ^ 2) (fun i _ => sq_nonneg _) P.i1_mem
  have e2 : P.aAux N / P.hAux N
      ≤ N.smin * (P.dkR * P.lamk1 ^ 2) / (N.smax * P.lam1 ^ 2) := by
    unfold aAux hAux
    exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left (psiB_le P) hs.le)
      (by positivity) (mul_le_mul_of_nonneg_left hψD hsmax.le)
  have e3 : N.smin * (P.dkR * P.lamk1 ^ 2) / (N.smax * P.lam1 ^ 2)
      = N.smin * P.dkR / N.smax / ((P.lam1 / P.lamk) ^ 2 * P.mRatio ^ 2) := by
    unfold mRatio
    field_simp
  linarith

/-- **`θ*_t → 1` in the paper's own high-dimensional regime.**
`1 - θ*_t < Tr Σ / ((1 + ρ) s_t (m² - 1))`, where `Tr Σ = ∑_i κ_i²`.  Under Assumption 1 the
trace of `Σ` stays bounded, so whenever the gradient energy `s_t` grows with `d` (e.g.
`‖x_t‖² ≍ d`), `θ*_t → 1` at *fixed* gap ratio `m`; no `d`-independent `α` exists. -/
theorem thetaStar_rate_trace_bound (hs : 0 < N.smin) (c : ι → ℝ) (hc : 0 < P.s c) :
    1 - P.thetaStar N c < (∑ i, N.kap2 i) / ((1 + P.rho) * P.s c * (P.mRatio ^ 2 - 1)) := by
  have hm := P.one_lt_mRatio
  have hm2 : 0 < P.mRatio ^ 2 - 1 := by nlinarith
  have hn := P.dkR_pos
  have hk := P.kR_pos
  have hρ := P.rho_pos
  have h1 := P.thetaStar_rate_energy_bound N hs c hc
  have htr := card_mul_smin_le_trace N
  rw [← kR_add_dkR P] at htr
  have h2 : N.smin * P.dkR / (P.s c * (P.mRatio ^ 2 - 1))
      ≤ (∑ i, N.kap2 i) / ((1 + P.rho) * P.s c * (P.mRatio ^ 2 - 1)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have e : (1 + P.rho) * P.dkR = P.kR + P.dkR := by
      unfold rho
      field_simp
      ring
    have key : N.smin * P.dkR * (1 + P.rho) ≤ ∑ i, N.kap2 i := by
      calc N.smin * P.dkR * (1 + P.rho) = (P.kR + P.dkR) * N.smin := by rw [← e]; ring
        _ ≤ ∑ i, N.kap2 i := htr
    have hpos : 0 ≤ P.s c * (P.mRatio ^ 2 - 1) := by positivity
    calc N.smin * P.dkR * ((1 + P.rho) * P.s c * (P.mRatio ^ 2 - 1))
        = N.smin * P.dkR * (1 + P.rho) * (P.s c * (P.mRatio ^ 2 - 1)) := by ring
      _ ≤ (∑ i, N.kap2 i) * (P.s c * (P.mRatio ^ 2 - 1)) :=
          mul_le_mul_of_nonneg_right key hpos
  linarith

end Spec

/-! ### Asymptotic forms for families of problems -/

section Families

open Filter Topology Asymptotics ThetaStarRate

variable {J : Type*} {κ : J → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]

/-- **Theorem 5, `Θ` form** (`θ*_t = 1 - Θ(1/m²)`) for an arbitrary family of problems/states
(indexed by `j`, along any filter `l`): if along the family
`0 < R₁ ≤ ρ s_max/s_min ≤ R₂`, `s_t/(s_min (d-k)) ≤ Ω`, `λ_1/λ_k ≤ K_𝒟`, `λ_{k+1}/λ_d ≤ K_ℬ`,
then `1 - θ* = Θ(1/m²)`.  The boundedness hypotheses are exactly what the paper's "constants"
hide; without the bound `Ω` on `s_t/(s_min (d-k))` the statement is false
(`thetaStar_rate_fails_fixed_state`). -/
theorem thetaStar_rate_isTheta (l : Filter J) (P : ∀ j, Spec (κ j)) (N : ∀ j, Noise (κ j))
    (c : ∀ j, κ j → ℝ) (hs : ∀ j, 0 < (N j).smin) {R₁ R₂ Ω KD KB : ℝ} (hR₁ : 0 < R₁)
    (hR₁' : ∀ j, R₁ ≤ (P j).rho * (N j).smax / (N j).smin)
    (hR₂ : ∀ j, (P j).rho * (N j).smax / (N j).smin ≤ R₂)
    (hΩ : ∀ j, (P j).s (c j) / ((N j).smin * (P j).dkR) ≤ Ω)
    (hKD : ∀ j, (P j).lam1 / (P j).lamk ≤ KD) (hKB : ∀ j, (P j).lamk1 / (P j).lamd ≤ KB) :
    (fun j => 1 - (P j).thetaStar (N j) (c j)) =Θ[l] (fun j => 1 / (P j).mRatio ^ 2) := by
  have key : ∀ j, 0 < 1 - (P j).thetaStar (N j) (c j) ∧
      1 - (P j).thetaStar (N j) (c j) ≤ (1 / R₁) * (1 / (P j).mRatio ^ 2) ∧
      1 / (P j).mRatio ^ 2 ≤
        (1 + (R₂ + Ω) * KD ^ 2 * KB ^ 2) * (1 - (P j).thetaStar (N j) (c j)) := by
    intro j
    have hm := (P j).one_lt_mRatio
    have hm2 : 0 < (P j).mRatio ^ 2 := by positivity
    obtain ⟨hlo, hhi⟩ :=
      (P j).thetaStar_rate_uniform (N j) (hs j) (c j) hR₁ (hR₁' j) (hR₂ j) (hΩ j) (hKD j) (hKB j)
    have hmem := thetaStar_mem_Ioo (P j) (N j) (hs j) (c j)
    have hr : 0 < (P j).rho * (N j).smax / (N j).smin :=
      div_pos (mul_pos (P j).rho_pos (smax_pos (P j) (N j) (hs j))) (hs j)
    have hω : 0 ≤ (P j).s (c j) / ((N j).smin * (P j).dkR) :=
      div_nonneg ((P j).s_nonneg (c j)) (mul_pos (hs j) (P j).dkR_pos).le
    have hA : 0 ≤ (R₂ + Ω) * KD ^ 2 * KB ^ 2 :=
      mul_nonneg (mul_nonneg (by linarith [hR₂ j, hΩ j]) (sq_nonneg _)) (sq_nonneg _)
    refine ⟨by linarith [hmem.2], ?_, ?_⟩
    · have e : (1 / R₁) * (1 / (P j).mRatio ^ 2) = (1 / R₁) / (P j).mRatio ^ 2 := by ring
      rw [e]
      exact hhi.le
    · have e : 1 / (1 + (R₂ + Ω) * KD ^ 2 * KB ^ 2) / (P j).mRatio ^ 2
          = (1 / (P j).mRatio ^ 2) / (1 + (R₂ + Ω) * KD ^ 2 * KB ^ 2) := by ring
      rw [e, div_le_iff₀ (by linarith)] at hlo
      linarith
  constructor
  · refine IsBigO.of_bound (1 / R₁) (Eventually.of_forall fun j => ?_)
    obtain ⟨h1, h2, -⟩ := key j
    have hm2 : 0 < (P j).mRatio ^ 2 := by have := (P j).one_lt_mRatio; positivity
    rw [Real.norm_of_nonneg h1.le, Real.norm_of_nonneg (by positivity)]
    exact h2
  · refine IsBigO.of_bound (1 + (R₂ + Ω) * KD ^ 2 * KB ^ 2) (Eventually.of_forall fun j => ?_)
    obtain ⟨h1, -, h3⟩ := key j
    have hm2 : 0 < (P j).mRatio ^ 2 := by have := (P j).one_lt_mRatio; positivity
    rw [Real.norm_of_nonneg h1.le, Real.norm_of_nonneg (by positivity)]
    exact h3

/-- **Interpretation of Theorem 5** ("as the dominant–bulk gap grows, `θ*_t → 1`").  For any
family of problems and states along which `ρ s_max / s_min` stays bounded below by some
`R₁ > 0` and the gap ratio `m = λ_k/λ_{k+1}` tends to `∞`, the threshold `θ*` tends to `1`.
No assumption on the states is needed (the lower bound of Theorem 5 is state-independent). -/
theorem thetaStar_tendsto_one_of_gap (l : Filter J) (P : ∀ j, Spec (κ j)) (N : ∀ j, Noise (κ j))
    (c : ∀ j, κ j → ℝ) (hs : ∀ j, 0 < (N j).smin) {R₁ : ℝ} (hR₁ : 0 < R₁)
    (hR₁' : ∀ j, R₁ ≤ (P j).rho * (N j).smax / (N j).smin)
    (hm : Tendsto (fun j => (P j).mRatio) l atTop) :
    Tendsto (fun j => (P j).thetaStar (N j) (c j)) l (𝓝 1) := by
  have hpow : Tendsto (fun j => (P j).mRatio ^ 2) l atTop :=
    (tendsto_pow_atTop (two_ne_zero)).comp hm
  have h0 : Tendsto (fun j => (1 / R₁) / (P j).mRatio ^ 2) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop hpow
  have hlow : Tendsto (fun j => 1 - (1 / R₁) / (P j).mRatio ^ 2) l (𝓝 1) := by
    simpa using tendsto_const_nhds.sub h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun j => ?_)
    (fun j => ?_)
  · have h := ((P j).thetaStar_rate_uniform (N j) (hs j) (c j) hR₁ (hR₁' j) le_rfl le_rfl
      le_rfl le_rfl).2
    show 1 - (1 / R₁) / (P j).mRatio ^ 2 ≤ (P j).thetaStar (N j) (c j)
    linarith
  · exact (thetaStar_mem_Ioo (P j) (N j) (hs j) (c j)).2.le

end Families

/-! ### The threshold at the origin, and concrete counterexamples -/

namespace ThetaStarRate

/-- If `s_t = 0` (i.e. `x_t = 0`), then `m^aux_t = 0`, the quadratic factors as
`(a r - h)(r + 1)` and `r_{0,t} = h^aux / a^aux`. -/
theorem r0_of_s_eq_zero (P : Spec ι) (N : Noise ι) (hs : 0 < N.smin) (c : ι → ℝ)
    (hc : P.s c = 0) : P.r0 N c = P.hAux N / P.aAux N := by
  have ha := aAux_pos P N hs
  have hh := hAux_pos P N hs
  symm
  apply eq_r0_of_auxQuad_eq_zero P N hs c (div_pos hh ha)
  have hM : P.mAux c = 0 := by
    unfold Spec.mAux
    rw [hc, zero_mul]
  unfold Spec.auxQuad
  rw [quad_eval_mid ha.ne', hM]
  simp

/-- At the origin, `1 - θ* = a^aux / (a^aux + h^aux) = s_min ψ_ℬ / (s_min ψ_ℬ + s_max ψ_𝒟)`. -/
theorem one_sub_thetaStar_of_s_eq_zero (P : Spec ι) (N : Noise ι) (hs : 0 < N.smin)
    (c : ι → ℝ) (hc : P.s c = 0) :
    1 - P.thetaStar N c = P.aAux N / (P.aAux N + P.hAux N) := by
  have ha := aAux_pos P N hs
  have hh := hAux_pos P N hs
  rw [one_sub_thetaStar P N hs c, r0_of_s_eq_zero P N hs c hc]
  field_simp

/-- The three-dimensional spectrum `λ = (μ, 1, 1)` with `𝒟 = {0}`, `ℬ = {1, 2}` (`μ > 1`):
both blocks are flat, `ρ = 1/2`, `λ_{k+1} = λ_d = 1` and the gap ratio is `m = μ`. -/
def gapSpec (μ : ℝ) (hμ : 1 < μ) : Spec (Fin 3) where
  lam := ![μ, 1, 1]
  D := {0}
  i1 := 0
  ik := 0
  ik1 := 1
  id := 1
  i1_mem := by simp
  ik_mem := by simp
  ik1_not_mem := by simp
  id_not_mem := by simp
  lam_pos := by
    intro i
    fin_cases i
    · simpa using (by linarith : (0 : ℝ) < μ)
    · simp
    · simp
  le_lam1 := by
    intro i hi
    rw [Finset.mem_singleton] at hi
    rw [hi]
  lamk_le := by
    intro i hi
    rw [Finset.mem_singleton] at hi
    rw [hi]
  le_lamk1 := by
    intro i hi
    fin_cases i
    · simp at hi
    · simp
    · simp
  lamd_le := by
    intro i hi
    fin_cases i
    · simp at hi
    · simp
    · simp
  gap := by simpa using hμ

/-- Isotropic unit noise `Σ = I₃`: `κ_i² = s_min = s_max = 1`. -/
def unitNoise : Noise (Fin 3) where
  kap2 := fun _ => 1
  smin := 1
  smax := 1
  smin_nonneg := zero_le_one
  smin_le := fun _ => le_rfl
  le_smax := fun _ => le_rfl

/-- The unit state `x = u_1` (first eigenvector, in the dominant block). -/
def e1 : Fin 3 → ℝ := ![1, 0, 0]

theorem gapSpec_B (μ : ℝ) (hμ : 1 < μ) : (gapSpec μ hμ).B = {1, 2} := by
  show ({0} : Finset (Fin 3))ᶜ = {1, 2}
  decide

@[simp] theorem gapSpec_mRatio (μ : ℝ) (hμ : 1 < μ) : (gapSpec μ hμ).mRatio = μ := by
  simp [Spec.mRatio, Spec.lamk, Spec.lamk1, gapSpec]

@[simp] theorem gapSpec_lam1 (μ : ℝ) (hμ : 1 < μ) : (gapSpec μ hμ).lam1 = μ := by
  simp [Spec.lam1, gapSpec]

@[simp] theorem gapSpec_lamk (μ : ℝ) (hμ : 1 < μ) : (gapSpec μ hμ).lamk = μ := by
  simp [Spec.lamk, gapSpec]

@[simp] theorem gapSpec_lamk1 (μ : ℝ) (hμ : 1 < μ) : (gapSpec μ hμ).lamk1 = 1 := by
  simp [Spec.lamk1, gapSpec]

@[simp] theorem gapSpec_lamd (μ : ℝ) (hμ : 1 < μ) : (gapSpec μ hμ).lamd = 1 := by
  simp [Spec.lamd, gapSpec]

@[simp] theorem gapSpec_kR (μ : ℝ) (hμ : 1 < μ) : (gapSpec μ hμ).kR = 1 := by
  simp [Spec.kR, gapSpec]

@[simp] theorem gapSpec_dkR (μ : ℝ) (hμ : 1 < μ) : (gapSpec μ hμ).dkR = 2 := by
  simp [Spec.dkR, gapSpec_B]

@[simp] theorem gapSpec_rho (μ : ℝ) (hμ : 1 < μ) : (gapSpec μ hμ).rho = 1 / 2 := by
  simp [Spec.rho]

@[simp] theorem gapSpec_psiD (μ : ℝ) (hμ : 1 < μ) : (gapSpec μ hμ).psiD = μ ^ 2 := by
  simp [Spec.psiD, gapSpec]

@[simp] theorem gapSpec_psiB (μ : ℝ) (hμ : 1 < μ) : (gapSpec μ hμ).psiB = 2 := by
  rw [Spec.psiB, gapSpec_B]
  simp [gapSpec]
  norm_num

@[simp] theorem gapSpec_normSqD_e1 (μ : ℝ) (hμ : 1 < μ) : (gapSpec μ hμ).normSqD e1 = 1 := by
  simp [Spec.normSqD, gapSpec, e1]

theorem normSq_e1 : Spec.normSq e1 = 1 := by
  simp [Spec.normSq, e1, Fin.sum_univ_three]

@[simp] theorem unitNoise_smin : unitNoise.smin = 1 := rfl
@[simp] theorem unitNoise_smax : unitNoise.smax = 1 := rfl

/-- In the family `λ = (μ, 1, 1)`, `Σ = I`, `x = u_1` one has
`1 - θ* < 2 / (μ² (μ² - 1))`: the threshold approaches `1` at rate `m⁻⁴`. -/
theorem one_sub_thetaStar_gapSpec_lt (μ : ℝ) (hμ : 1 < μ) :
    1 - (gapSpec μ hμ).thetaStar unitNoise e1 < 2 / (μ ^ 2 * (μ ^ 2 - 1)) := by
  have h := (gapSpec μ hμ).thetaStar_rate_quartic unitNoise (by simp) e1 (by simp)
  simpa using h

/-- The sequence of problems `A_n = diag(n + 2, 1, 1)`, `n = 0, 1, 2, …` (gap ratio
`m_n = n + 2 → ∞`). -/
def gapSpecNat (n : ℕ) : Spec (Fin 3) :=
  gapSpec ((n : ℝ) + 2) (by have h : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)

@[simp] theorem gapSpecNat_mRatio (n : ℕ) : (gapSpecNat n).mRatio = (n : ℝ) + 2 :=
  gapSpec_mRatio _ _

theorem one_sub_thetaStar_gapSpecNat_lt (n : ℕ) :
    1 - (gapSpecNat n).thetaStar unitNoise e1
      < 2 / (((n : ℝ) + 2) ^ 2 * (((n : ℝ) + 2) ^ 2 - 1)) :=
  one_sub_thetaStar_gapSpec_lt _ _

end ThetaStarRate

open ThetaStarRate in
/-- **The rate `θ* = 1 - Θ(1/m²)` of Theorem 5 fails for a fixed state when `λ_{k+1} = Θ(1)`.**
In the family `A = diag(μ, 1, 1)`, `𝒟 = {1}`, `Σ = I`, `x = u_1` — where `ρ = 1/2`,
`s_min = s_max = 1`, `λ_1/λ_k = λ_{k+1}/λ_d = 1`, `λ_{k+1} = 1`, `‖x‖ = 1` are all fixed and only
the gap ratio `m = μ` varies (`ThetaStarRate.gapSpec_rho`, `gapSpec_lam1`, `gapSpec_lamk`,
`gapSpec_lamk1`, `gapSpec_lamd`, `unitNoise_smin`, `unitNoise_smax`, `normSq_e1`,
`gapSpec_mRatio`) — for every `α > 0` the paper's upper bound `θ* ≤ 1 - α/m²` is
violated for all sufficiently large `m`.  (Here in fact `1 - θ* < 2/(m²(m²-1))`.) -/
theorem thetaStar_rate_fails_fixed_state {α : ℝ} (hα : 0 < α) :
    ∃ μ₀ : ℝ, 1 < μ₀ ∧ ∀ (μ : ℝ) (hμ : 1 < μ), μ₀ ≤ μ →
      1 - α / (gapSpec μ hμ).mRatio ^ 2 < (gapSpec μ hμ).thetaStar unitNoise e1 := by
  refine ⟨1 + 2 / α, by linarith [div_pos (two_pos : (0 : ℝ) < 2) hα], ?_⟩
  intro μ hμ hμ₀
  have h := one_sub_thetaStar_gapSpec_lt μ hμ
  rw [gapSpec_mRatio]
  have hpos : 0 < 2 / α := div_pos two_pos hα
  have hμ2 : 2 / α ≤ μ ^ 2 - 1 := by nlinarith
  have hμ2' : 0 < μ ^ 2 - 1 := by linarith
  have hle : 2 / (μ ^ 2 * (μ ^ 2 - 1)) ≤ α / μ ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    rw [div_le_iff₀ hα] at hμ2
    nlinarith [sq_nonneg μ]
  linarith

open ThetaStarRate Asymptotics in
/-- **Formal negation of "`θ*_t = 1 - Θ(1/m²)`" along a concrete sequence.**  For
`A_n = diag(n + 2, 1, 1)`, `𝒟 = {1}`, `Σ = I`, `x = u_1` (so `m_n = n + 2 → ∞` while
`ρ, s_min, s_max, λ_1/λ_k, λ_{k+1}/λ_d, λ_{k+1}, ‖x‖` are constant), `1 - θ*` is **not**
`Θ(1/m²)`: it is `O(1/m⁴)`. -/
theorem thetaStar_rate_not_isTheta :
    ¬ ((fun n : ℕ => 1 - (gapSpecNat n).thetaStar unitNoise e1)
        =Θ[Filter.atTop] (fun n : ℕ => 1 / (gapSpecNat n).mRatio ^ 2)) := by
  intro h
  obtain ⟨C, hC⟩ := h.2.bound
  obtain ⟨n, hn, hnC⟩ := (hC.and (Filter.eventually_ge_atTop (⌈2 * C⌉₊ + 1))).exists
  have hmem := thetaStar_mem_Ioo (gapSpecNat n) unitNoise (by simp) e1
  have hpos : 0 < 1 - (gapSpecNat n).thetaStar unitNoise e1 := by linarith [hmem.2]
  have hlt := one_sub_thetaStar_gapSpecNat_lt n
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [gapSpecNat_mRatio, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hpos.le] at hn
  set X : ℝ := ((n : ℝ) + 2) ^ 2 with hX
  have hX1 : (n : ℝ) ≤ X - 1 := by rw [hX]; nlinarith
  have hXpos : 0 < X := by rw [hX]; positivity
  have hX1pos : 0 < X - 1 := by nlinarith
  have hCpos : 0 < C := by
    by_contra hC0
    have h1 : C * (1 - (gapSpecNat n).thetaStar unitNoise e1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hC0) hpos.le
    have h2 : 0 < 1 / X := by positivity
    linarith
  have h2C : 2 * C < n := by
    have h1 := Nat.le_ceil (2 * C)
    have h2 : ((⌈2 * C⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hnC
    push_cast at h2
    linarith
  have h3 : C * (1 - (gapSpecNat n).thetaStar unitNoise e1) < C * (2 / (X * (X - 1))) :=
    mul_lt_mul_of_pos_left hlt hCpos
  have h4 : 1 / X < C * (2 / (X * (X - 1))) := lt_of_le_of_lt hn h3
  have h5 := mul_lt_mul_of_pos_right h4 (mul_pos hXpos hX1pos)
  have e1' : 1 / X * (X * (X - 1)) = X - 1 := by field_simp
  have e2' : C * (2 / (X * (X - 1))) * (X * (X - 1)) = 2 * C := by field_simp
  rw [e1', e2'] at h5
  linarith

open ThetaStarRate in
/-- **The constant named in the paper's proof is wrong.**  The proof of Theorem 5 sets
`β := ρ s_max / s_min` and concludes `1 - β/m² ≤ θ*_t`.  For `A = diag(2, 1, 1)`, `𝒟 = {1}`,
`Σ = I`, `x = 0` one has `ρ = 1/2`, `m = 2`, `θ* = 2/3`, while `1 - β/m² = 7/8`.
(The correct constant is the reciprocal, `Spec.thetaStarRateBeta`.) -/
theorem thetaStar_rate_paper_beta_fails :
    ∃ (P : Spec (Fin 3)) (N : Noise (Fin 3)) (c : Fin 3 → ℝ), 0 < N.smin ∧
      P.thetaStar N c < 1 - (P.rho * N.smax / N.smin) / P.mRatio ^ 2 := by
  refine ⟨gapSpec 2 (by norm_num), unitNoise, 0, by simp, ?_⟩
  have h := one_sub_thetaStar_of_s_eq_zero (gapSpec 2 (by norm_num)) unitNoise (by simp) 0
    ((Spec.s_eq_zero_iff _ _).mpr rfl)
  have ha : (gapSpec 2 (by norm_num)).aAux unitNoise = 2 := by simp [Spec.aAux]
  have hh : (gapSpec 2 (by norm_num)).hAux unitNoise = 4 := by simp [Spec.hAux]; norm_num
  rw [ha, hh] at h
  simp only [gapSpec_rho, gapSpec_mRatio, unitNoise_smin, unitNoise_smax]
  norm_num at h ⊢
  linarith

/-- Non-vacuity: the hypotheses used in this file (`0 < s_min`, and for the `m⁻⁴` bound
`0 < ‖P^𝒟 x‖²`) are jointly satisfiable. -/
example : ∃ (P : Spec (Fin 3)) (N : Noise (Fin 3)) (c : Fin 3 → ℝ),
    0 < N.smin ∧ 0 < P.normSqD c :=
  ⟨ThetaStarRate.gapSpec 2 (by norm_num), ThetaStarRate.unitNoise, ThetaStarRate.e1,
    by simp, by simp⟩

end SuspiciousAlignment
