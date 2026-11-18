import Mathlib
import SuspiciousAlignment.Defs

/-!
# Spectrally filtered updates in Deng's quadratic model: the coordinate and the vector model

This file is an **extension** of

> Deng et al., *Suspicious Alignment of SGD: A Fine-Grained Step Size Condition Analysis*
> (arXiv:2601.11789v2)

to spectral-filter optimizers `W⁺ = W - η U f(S) Vᵀ` (SGD: `f = id`, Muon: `f ≡ 1`,
HTMuon: `f σ = σ ^ p`).  Its source of truth is the specification
`notes/research/filter_spec.md`, sections 1 (coordinate / commuting model) and 4 (vector model).

In the coordinate model the gradient coordinate `g_i = λ_i c_i` of Deng's eigen-coordinate model is
replaced by `φ_f(g_i)`, `φ_f(g) = sign(g) f(|g|)` (`Spec.oddExt`).  The key quantity is the
*effective curvature* `ν_i = f(λ_i |c_i|) / |c_i|` (`Spec.nu`): the filtered step is
`c_i⁺ = (1 - η ν_i) c_i`, i.e. Deng's noise-free SGD step with `λ_i` replaced by `ν_i`.

## Contents (spec item → declarations)

* Definitions: `Spec.oddExt`, `Spec.cNextF`, `Spec.nu`, `Spec.momF`, `Spec.qF`, `Spec.pF`,
  `Spec.etaStarF`, `Spec.fCompareF`; `Noise.noiseFree` (zero noise, so that the spec's `η*₀` is
  `P.etaStar Noise.noiseFree c`); `Spec.gradNorm`, `Spec.etaEff`, `Spec.cNextVec` (section 4).
* **(1.0)** `Spec.cNextF_apply` (`c_i⁺ = c_i - η sign(c_i) f(λ_i |c_i|)`), `Spec.cNextF_one`,
  `Spec.nu_one` (Muon).
* **1.1** `Spec.cNextF_eq`, `Spec.oddExt_lam_mul`.
* **1.2** `Spec.cNextF_id`, `Spec.nu_id`, `Spec.qF_id`, `Spec.pF_id`, `Spec.etaStarF_id`,
  `Spec.fCompareF_id`.
* **1.3** `Spec.momF_zero`, `Spec.mom_cNextF`.
* **1.4** `Spec.fCompareF_eq` (and `Spec.fCompare_noiseFree_eq` for SGD).
* **1.5** `Spec.theta_lt_iff_cross_neg`, `Spec.theta_gt_iff_cross_pos`,
  `Spec.theta_eq_iff_cross_eq_zero` (two arbitrary states), and `Spec.theta_cNextF_lt_iff`,
  `Spec.theta_cNextF_gt_iff`, `Spec.theta_cNextF_eq_iff` (the filtered step).
* **1.6** `Spec.qF_eq_double_sum`, `Spec.pF_eq_double_sum`, `Spec.etaStarF_eq_double_sum`.
* **1.7** `Spec.qF_neg_of_ordered`, `Spec.pF_pos_of_ordered`, `Spec.etaStarF_pos_of_ordered`,
  `Spec.s_cNextF_pos_of_ordered`, `Spec.theta_cNextF_lt_iff_of_ordered` (and `_eq_`, `_gt_`;
  primed versions for all real `η`), and the SGD case `Spec.theta_cNext_noiseFree_lt_iff`
  (and `_eq_`, `_gt_`), `Spec.pCoef_noiseFree_pos`, `Spec.etaStar_noiseFree_pos`.
* **1.8** `Spec.qF_pos_of_reversed`, `Spec.pF_neg_of_reversed`, `Spec.etaStarF_pos_of_reversed`,
  `Spec.s_cNextF_pos_of_reversed`, `Spec.theta_cNextF_gt_iff_of_reversed` (and `_eq_`, `_lt_`;
  primed versions for all real `η`), `Spec.not_reversed_id`, `Spec.qF_id_nonpos`.
* **1.9** `Spec.two_div_le_etaStarF_of_ordered`, `Spec.etaStarF_le_two_div_of_ordered`,
  `Spec.etaStarF_mem_Icc_of_ordered` (extra: the same bounds in the reversed case,
  `Spec.two_div_le_etaStarF_of_reversed`, `Spec.etaStarF_le_two_div_of_reversed`);
  SGD corollary `Spec.two_div_le_etaStar_noiseFree`, `Spec.etaStar_noiseFree_le_two_div`,
  `Spec.etaStar_noiseFree_mem_Icc`; comparison with Deng's Theorem 7
  `Spec.thm7_noiseFree_bound_eq`, `Spec.thm7_noiseFree_bound_le_two_div` (strict:
  `Spec.thm7_noiseFree_bound_lt_two_div`, equality case:
  `Spec.thm7_noiseFree_bound_eq_two_div_iff`), `Spec.thm7_noiseFree_bound_le_etaStar`.
* **4.1** `Spec.cNextVec_eq_cNext`, `Spec.theta_cNextVec`, `Spec.etaEff_one`, `Spec.etaEff_rpow`,
  `Spec.etaEff_id`.
* **4.2** `Spec.theta_cNextVec_noiseFree_lt_iff` (general filter; and `_gt_`, `_eq_`),
  `Spec.theta_cNextVec_rpow_lt_iff` (and `_gt_`, `_eq_`), `Spec.etaStar_noiseFree_smul`,
  `Spec.theta_cNextVec_rpow_ray_lt_iff`, `Spec.theta_cNextVec_rpow_ray_gt_iff`;
  `Spec.theta_cNextVec_rpow_gt_of_neg` shows that `η > 0` is needed.
* Non-vacuity and sharpness of hypotheses: `FilterCoordinate.exSpec` (`λ = (2, 1)` on `Fin 2`)
  with explicit Muon states where the alignment decreases (`exSpec_muon_decrease`, 1.7) resp.
  **increases** (`exSpec_muon_increase`, 1.8) for every `0 < η < 4/3`;
  `exSpec_ordered_without_sign`, `exSpec_reversed_without_sign` (the sign conditions of 1.7 and
  1.8 cannot be dropped);
  `exSpec_muon_annihilate` (the proviso `s(c') > 0` of 1.5 cannot be dropped);
  `exSpec_vector_ray` (4.2).

Deviations from the specification found while formalizing are recorded in
`notes/fidelity/FilterCoordinate.md`.  Inside `namespace Spec` the identifier `id` resolves to
the structure field `Spec.id` (the index of `λ_d`), so the identity filter is written `_root_.id`.

Helper lemmas specific to this file live in `SuspiciousAlignment.FilterCoordinate`.
-/

set_option linter.unusedSectionVars false

open Finset

namespace SuspiciousAlignment

/-- The zero noise (`κ_i² = 0`, `s_min = s_max = 0`): the noise-free case of Deng's model.
`P.etaStar Noise.noiseFree c` is the spec's `η*₀ = -q_t / p_t` with `e_𝒟 = e_ℬ = 0`. -/
def Noise.noiseFree {ι : Type*} : Noise ι where
  kap2 := fun _ => 0
  smin := 0
  smax := 0
  smin_nonneg := le_rfl
  smin_le := fun _ => le_rfl
  le_smax := fun _ => le_rfl

@[simp] theorem Noise.noiseFree_kap2 {ι : Type*} (i : ι) : (Noise.noiseFree : Noise ι).kap2 i = 0 :=
  rfl
@[simp] theorem Noise.noiseFree_smin {ι : Type*} : (Noise.noiseFree : Noise ι).smin = 0 := rfl
@[simp] theorem Noise.noiseFree_smax {ι : Type*} : (Noise.noiseFree : Noise ι).smax = 0 := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Real-variable helper lemmas -/

namespace FilterCoordinate

/-- `p η² + q η = η (p η + q)`. -/
theorem quad_eq_mul (p q η : ℝ) : p * η ^ 2 + q * η = η * (p * η + q) := by ring

/-- For `p > 0 > q` and **every** real `η`: `p η² + q η < 0 ↔ 0 < η < -q / p`. -/
theorem quad_neg_iff {p q η : ℝ} (hp : 0 < p) (hq : q < 0) :
    p * η ^ 2 + q * η < 0 ↔ 0 < η ∧ η < -q / p := by
  rw [quad_eq_mul, lt_div_iff₀ hp]
  constructor
  · intro h
    rcases lt_trichotomy η 0 with h0 | h0 | h0
    · exfalso
      have h2 : p * η + q < 0 := by nlinarith
      have := mul_pos_of_neg_of_neg h0 h2
      linarith
    · exfalso
      rw [h0] at h
      simp at h
    · refine ⟨h0, ?_⟩
      by_contra hh
      have h2 : 0 ≤ p * η + q := by linarith [not_lt.mp hh]
      have := mul_nonneg h0.le h2
      linarith
  · rintro ⟨h0, h1⟩
    exact mul_neg_of_pos_of_neg h0 (by linarith)

/-- For `p > 0 > q` and every real `η`: `p η² + q η = 0 ↔ η = 0 ∨ η = -q / p`. -/
theorem quad_eq_zero_iff {p q η : ℝ} (hp : p ≠ 0) :
    p * η ^ 2 + q * η = 0 ↔ η = 0 ∨ η = -q / p := by
  rw [quad_eq_mul, mul_eq_zero, eq_div_iff hp]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by linarith)

/-- For `p > 0 > q` and every real `η`: `0 < p η² + q η ↔ η < 0 ∨ -q / p < η`. -/
theorem quad_pos_iff {p q η : ℝ} (hp : 0 < p) (hq : q < 0) :
    0 < p * η ^ 2 + q * η ↔ η < 0 ∨ -q / p < η := by
  have hr : 0 < -q / p := div_pos (neg_pos.mpr hq) hp
  have hneg := quad_neg_iff (η := η) hp hq
  have hzero := quad_eq_zero_iff (q := q) (η := η) hp.ne'
  constructor
  · intro h
    rcases lt_trichotomy η 0 with h0 | h0 | h0
    · exact Or.inl h0
    · exact absurd (hzero.mpr (Or.inl h0)) h.ne'
    · right
      rcases lt_trichotomy η (-q / p) with h1 | h1 | h1
      · exact absurd (hneg.mpr ⟨h0, h1⟩) (not_lt.mpr h.le)
      · exact absurd (hzero.mpr (Or.inr h1)) h.ne'
      · exact h1
  · intro h
    rcases lt_trichotomy (p * η ^ 2 + q * η) 0 with h1 | h1 | h1
    · obtain ⟨h2, h3⟩ := hneg.mp h1
      rcases h with h | h <;> linarith
    · rcases hzero.mp h1 with h2 | h2 <;> rcases h with h | h <;> linarith
    · exact h1

/-- For `x, η, E > 0` and `p < 1`: `η x^{p-1} < E ↔ (η / E)^{1/(1-p)} < x`. -/
theorem rpow_ray_lt_iff {η E x p : ℝ} (hη : 0 < η) (hE : 0 < E) (hx : 0 < x) (hp : p < 1) :
    η * x ^ (p - 1) < E ↔ (η / E) ^ (1 / (1 - p)) < x := by
  have hz : 0 < 1 - p := by linarith
  have hxz : 0 < x ^ (1 - p) := Real.rpow_pos_of_pos hx _
  have h1 : x ^ (p - 1) = (x ^ (1 - p))⁻¹ := by
    rw [← Real.rpow_neg hx.le]; congr 1; ring
  rw [h1, one_div, Real.rpow_inv_lt_iff_of_pos (div_pos hη hE).le hx.le hz, ← div_eq_mul_inv,
    div_lt_iff₀ hxz, div_lt_iff₀' hE]

/-- For `x, η, E > 0` and `p < 1`: `E < η x^{p-1} ↔ x < (η / E)^{1/(1-p)}`. -/
theorem rpow_ray_gt_iff {η E x p : ℝ} (hη : 0 < η) (hE : 0 < E) (hx : 0 < x) (hp : p < 1) :
    E < η * x ^ (p - 1) ↔ x < (η / E) ^ (1 / (1 - p)) := by
  have hz : 0 < 1 - p := by linarith
  have hxz : 0 < x ^ (1 - p) := Real.rpow_pos_of_pos hx _
  have h1 : x ^ (p - 1) = (x ^ (1 - p))⁻¹ := by
    rw [← Real.rpow_neg hx.le]; congr 1; ring
  rw [h1, one_div, Real.lt_rpow_inv_iff_of_pos hx.le (div_pos hη hE).le hz, ← div_eq_mul_inv,
    lt_div_iff₀ hxz, lt_div_iff₀' hE]

end FilterCoordinate

namespace Spec

variable (P : Spec ι)

/-! ### Definitions (spec §1 and §4) -/

/-- The odd extension `φ_f(g) = sign(g) f(|g|)` of a spectral filter `f` (spec §1). -/
noncomputable def oddExt (f : ℝ → ℝ) (g : ℝ) : ℝ := Real.sign g * f |g|

/-- One filtered step in the coordinate (commuting) model, spec eq. (1.0):
`c_i⁺ = c_i - η φ_f(λ_i c_i) = c_i - η sign(c_i) f(λ_i |c_i|)`. -/
noncomputable def cNextF (f : ℝ → ℝ) (η : ℝ) (c : ι → ℝ) : ι → ℝ :=
  fun i => c i - η * oddExt f (P.lam i * c i)

/-- The effective curvature `ν_i = f(λ_i |c_i|) / |c_i|` (and `ν_i = 0` if `c_i = 0`, by Lean's
`x / 0 = 0`). -/
noncomputable def nu (f : ℝ → ℝ) (c : ι → ℝ) (i : ι) : ℝ := f (P.lam i * |c i|) / |c i|

/-- The `ν`-moments `∑_{i∈S} ν_i^a λ_i² c_i²`. -/
noncomputable def momF (f : ℝ → ℝ) (S : Finset ι) (a : ℕ) (c : ι → ℝ) : ℝ :=
  ∑ i ∈ S, P.nu f c i ^ a * P.lam i ^ 2 * c i ^ 2

/-- The linear coefficient `q^f = 2 (s^𝒟 ∑_ℬ ν s_j - s^ℬ ∑_𝒟 ν s_i)` of the filtered comparison
functional. -/
noncomputable def qF (f : ℝ → ℝ) (c : ι → ℝ) : ℝ :=
  2 * (P.sD c * P.momF f P.B 1 c - P.sB c * P.momF f P.D 1 c)

/-- The quadratic coefficient `p^f = s^ℬ ∑_𝒟 ν² s_i - s^𝒟 ∑_ℬ ν² s_j` of the filtered comparison
functional. -/
noncomputable def pF (f : ℝ → ℝ) (c : ι → ℝ) : ℝ :=
  P.sB c * P.momF f P.D 2 c - P.sD c * P.momF f P.B 2 c

/-- The critical step size `η*_f = -q^f / p^f` of the filtered update. -/
noncomputable def etaStarF (f : ℝ → ℝ) (c : ι → ℝ) : ℝ := -P.qF f c / P.pF f c

/-- The comparison functional `s^ℬ(c) s^𝒟(c⁺) - s^ℬ(c⁺) s^𝒟(c)` of the filtered step
`c⁺ = cNextF f η c` (Deng's eq. (12) for the filtered update; no noise, no expectation). -/
noncomputable def fCompareF (f : ℝ → ℝ) (η : ℝ) (c : ι → ℝ) : ℝ :=
  P.sB c * P.sD (P.cNextF f η c) - P.sB (P.cNextF f η c) * P.sD c

/-- The norm `‖g‖ = √(∑_i g_i²)` of the stochastic gradient `g_i = λ_i c_i + ζ_i` (spec §4): the
single singular value of the `d × 1` gradient matrix. -/
noncomputable def gradNorm (c ζ : ι → ℝ) : ℝ := Real.sqrt (∑ i, (P.lam i * c i + ζ i) ^ 2)

/-- The effective step size `η_eff = η f(‖g‖) / ‖g‖` of the vector model (spec 4.1). -/
noncomputable def etaEff (f : ℝ → ℝ) (η : ℝ) (c ζ : ι → ℝ) : ℝ :=
  η * f (P.gradNorm c ζ) / P.gradNorm c ζ

/-- One filtered step of the vector model (`n = 1`, spec 4.1):
`c_i⁺ = c_i - η f(‖g‖) g_i / ‖g‖` with `g_i = λ_i c_i + ζ_i`. -/
noncomputable def cNextVec (f : ℝ → ℝ) (η : ℝ) (c ζ : ι → ℝ) : ι → ℝ :=
  fun i => c i - η * f (P.gradNorm c ζ) * (P.lam i * c i + ζ i) / P.gradNorm c ζ

/-! ### The odd extension -/

@[simp] theorem oddExt_zero (f : ℝ → ℝ) : oddExt f 0 = 0 := by simp [oddExt]

theorem oddExt_of_pos (f : ℝ → ℝ) {g : ℝ} (hg : 0 < g) : oddExt f g = f g := by
  simp [oddExt, Real.sign_of_pos hg, abs_of_pos hg]

theorem oddExt_of_neg (f : ℝ → ℝ) {g : ℝ} (hg : g < 0) : oddExt f g = -f (-g) := by
  simp [oddExt, Real.sign_of_neg hg, abs_of_neg hg]

/-- `φ_f` is odd. -/
theorem oddExt_neg (f : ℝ → ℝ) (g : ℝ) : oddExt f (-g) = -oddExt f g := by
  simp [oddExt, Real.sign_neg]

/-- For the identity filter (SGD), `φ_f(g) = g`. -/
@[simp] theorem oddExt_id (g : ℝ) : oddExt _root_.id g = g := by
  rcases lt_trichotomy g 0 with h | h | h
  · rw [oddExt_of_neg _ h]; simp
  · rw [h]; simp
  · rw [oddExt_of_pos _ h]; simp

/-- For the constant filter `1` (Muon), `φ_f(g) = sign(g)`. -/
@[simp] theorem oddExt_one (g : ℝ) : oddExt (fun _ => (1 : ℝ)) g = Real.sign g := by
  simp [oddExt]

/-- As `λ_i > 0`, `sign(λ_i c_i) = sign(c_i)`. -/
theorem sign_lam_mul (c : ι → ℝ) (i : ι) : Real.sign (P.lam i * c i) = Real.sign (c i) := by
  have hl := P.lam_pos i
  rcases lt_trichotomy (c i) 0 with h | h | h
  · rw [Real.sign_of_neg h, Real.sign_of_neg (mul_neg_of_pos_of_neg hl h)]
  · rw [h]; simp
  · rw [Real.sign_of_pos h, Real.sign_of_pos (mul_pos hl h)]

/-- **Spec eq. (1.0).** The filtered step in the form
`c_i⁺ = c_i - η · sign(c_i) · f(λ_i |c_i|)`. -/
theorem cNextF_apply (f : ℝ → ℝ) (η : ℝ) (c : ι → ℝ) (i : ι) :
    P.cNextF f η c i = c i - η * (Real.sign (c i) * f (P.lam i * |c i|)) := by
  simp only [cNextF, oddExt, P.sign_lam_mul, abs_mul, abs_of_pos (P.lam_pos i)]

/-- Muon (`f ≡ 1`): `c_i⁺ = c_i - η sign(c_i)`. -/
theorem cNextF_one (η : ℝ) (c : ι → ℝ) (i : ι) :
    P.cNextF (fun _ => (1 : ℝ)) η c i = c i - η * Real.sign (c i) := by
  rw [P.cNextF_apply, mul_one]

/-- Muon (`f ≡ 1`): the effective curvature is `ν_i = 1 / |c_i|` — the eigenvalue drops out. -/
theorem nu_one (c : ι → ℝ) (i : ι) : P.nu (fun _ => (1 : ℝ)) c i = 1 / |c i| := rfl

/-- A filter that is non-negative on `[0, ∞)` has non-negative effective curvatures. -/
theorem nu_nonneg {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ x → 0 ≤ f x) (c : ι → ℝ) (i : ι) :
    0 ≤ P.nu f c i :=
  div_nonneg (hf _ (mul_nonneg (P.lam_pos i).le (abs_nonneg _))) (abs_nonneg _)

/-! ### Statement 1.1: the effective-curvature form -/

/-- At a vanishing coefficient the effective curvature is `0` (Lean's `x / 0 = 0`). -/
theorem nu_of_eq_zero (f : ℝ → ℝ) {c : ι → ℝ} {i : ι} (h : c i = 0) : P.nu f c i = 0 := by
  simp [nu, h]

/-- The filtered gradient coordinate is the effective curvature times the coefficient:
`φ_f(λ_i c_i) = ν_i c_i` (also at `c_i = 0`, where both sides vanish). -/
theorem oddExt_lam_mul (f : ℝ → ℝ) (c : ι → ℝ) (i : ι) :
    oddExt f (P.lam i * c i) = P.nu f c i * c i := by
  have hl := P.lam_pos i
  rcases lt_trichotomy (c i) 0 with h | h | h
  · have hlc : P.lam i * c i < 0 := mul_neg_of_pos_of_neg hl h
    have hc : c i ≠ 0 := h.ne
    rw [oddExt_of_neg _ hlc, nu, abs_of_neg h, mul_neg]
    field_simp
  · rw [h]; simp [nu]
  · have hlc : 0 < P.lam i * c i := mul_pos hl h
    rw [oddExt_of_pos _ hlc, nu, abs_of_pos h]
    field_simp

/-- **Spec 1.1 (effective-curvature form).** `c_i⁺ = (1 - η ν_i) c_i` for every `i`
(including `c_i = 0`, where both sides are `0`). -/
theorem cNextF_eq (f : ℝ → ℝ) (η : ℝ) (c : ι → ℝ) (i : ι) :
    P.cNextF f η c i = (1 - η * P.nu f c i) * c i := by
  unfold cNextF
  rw [P.oddExt_lam_mul]
  ring

/-! ### Statement 1.2: SGD is the identity filter -/

/-- **Spec 1.2.** For the identity filter the filtered step is Deng's SGD step with zero noise. -/
theorem cNextF_id (η : ℝ) (c : ι → ℝ) : P.cNextF _root_.id η c = P.cNext η c 0 := by
  funext i
  simp only [cNextF, cNext, oddExt_id, Pi.zero_apply]
  ring

/-- **Spec 1.2.** For the identity filter `ν_i = λ_i` whenever `c_i ≠ 0`. -/
theorem nu_id {c : ι → ℝ} {i : ι} (h : c i ≠ 0) : P.nu _root_.id c i = P.lam i := by
  have : |c i| ≠ 0 := abs_ne_zero.mpr h
  simp only [nu, id_eq]
  field_simp

/-- For the identity filter `0 ≤ ν_i` (it is `λ_i` or `0`). -/
theorem nu_id_nonneg (c : ι → ℝ) (i : ι) : 0 ≤ P.nu _root_.id c i := by
  by_cases h : c i = 0
  · rw [P.nu_of_eq_zero _ h]
  · rw [P.nu_id h]; exact (P.lam_pos i).le

/-- For the identity filter the `ν`-moments are Deng's moments: `∑_S ν^a λ² c² = ∑_S λ^{a+2} c²`. -/
theorem momF_id (S : Finset ι) (a : ℕ) (c : ι → ℝ) :
    P.momF _root_.id S a c = P.mom S (a + 2) c := by
  unfold momF mom
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : c i = 0
  · simp [h]
  · rw [P.nu_id h]; ring

/-- **Spec 1.2.** For the identity filter `q^f` is Deng's `q_t`. -/
theorem qF_id (c : ι → ℝ) : P.qF _root_.id c = P.qCoef c := by
  simp only [qF, qCoef, tauB, tauD, momF_id]

/-- **Spec 1.2.** For the identity filter `p^f` is Deng's `p_t` with zero noise. -/
theorem pF_id (c : ι → ℝ) : P.pF _root_.id c = P.pCoef Noise.noiseFree c := by
  simp [pF, pCoef, eD, eB, momF_id]

@[simp] theorem eD_noiseFree : P.eD Noise.noiseFree = 0 := by simp [eD]
@[simp] theorem eB_noiseFree : P.eB Noise.noiseFree = 0 := by simp [eB]

/-- The noise-free critical step size `η*₀` written out (Deng's eq. (2) with `e_𝒟 = e_ℬ = 0`):
`η*₀ = 2 (s^ℬ τ^𝒟 - s^𝒟 τ^ℬ) / (s^ℬ ∑_𝒟 λ⁴c² - s^𝒟 ∑_ℬ λ⁴c²)`. -/
theorem etaStar_noiseFree_eq (c : ι → ℝ) :
    P.etaStar Noise.noiseFree c =
      2 * (P.sB c * P.tauD c - P.sD c * P.tauB c) /
        (P.sB c * P.mom P.D 4 c - P.sD c * P.mom P.B 4 c) := by
  simp only [etaStar, qCoef, pCoef, eD_noiseFree, eB_noiseFree, add_zero]
  congr 1
  ring

/-- **Spec 1.2.** For the identity filter `η*_f` is Deng's `η*_t` with zero noise (`η*₀`). -/
theorem etaStarF_id (c : ι → ℝ) : P.etaStarF _root_.id c = P.etaStar Noise.noiseFree c := by
  simp only [etaStarF, etaStar, qF_id, pF_id]

/-- **Spec 1.2.** For the identity filter the filtered comparison functional is Deng's `f_t(η)` at
zero noise. -/
theorem fCompareF_id (η : ℝ) (c : ι → ℝ) : P.fCompareF _root_.id η c = P.fCompare η c 0 := by
  simp only [fCompareF, fCompare, cNextF_id]

/-! ### Statement 1.3: energies after one filtered step -/

/-- **Spec 1.3.** The zeroth `ν`-moment is the block energy `s^S`. -/
theorem momF_zero (f : ℝ → ℝ) (S : Finset ι) (c : ι → ℝ) : P.momF f S 0 c = P.mom S 2 c := by
  simp [momF, mom]

/-- **Spec 1.3 (energies).** `∑_{i∈S} λ_i² (c_i⁺)² = M₀ - 2 η M₁ + η² M₂` with
`M_a = momF f S a c`. -/
theorem mom_cNextF (f : ℝ → ℝ) (S : Finset ι) (η : ℝ) (c : ι → ℝ) :
    P.mom S 2 (P.cNextF f η c) =
      P.momF f S 0 c - 2 * η * P.momF f S 1 c + η ^ 2 * P.momF f S 2 c := by
  simp only [mom, momF, cNextF_eq]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ### Statement 1.4: the exact quadratic form -/

/-- **Spec 1.4 (quadratic form, exact — no expectation).**
`fCompareF f η c = p^f η² + q^f η`. -/
theorem fCompareF_eq (f : ℝ → ℝ) (η : ℝ) (c : ι → ℝ) :
    P.fCompareF f η c = P.pF f c * η ^ 2 + P.qF f c * η := by
  simp only [fCompareF, sD, sB, mom_cNextF, momF_zero, pF, qF]
  ring

/-- Noise-free Deng (Lemma "Quadratic form", pathwise at `ζ = 0`):
`f_t(η) = p_t η² + q_t η` with `e_𝒟 = e_ℬ = 0`. -/
theorem fCompare_noiseFree_eq (η : ℝ) (c : ι → ℝ) :
    P.fCompare η c 0 = P.pCoef Noise.noiseFree c * η ^ 2 + P.qCoef c * η := by
  rw [← P.fCompareF_id, P.fCompareF_eq, P.pF_id, P.qF_id]

/-! ### Statement 1.5: the alignment change of two arbitrary states -/

/-- **Spec 1.5 (alignment change), `<`.** For two arbitrary non-zero states `c, c'`:
`θ(c') < θ(c) ↔ s^ℬ(c) s^𝒟(c') - s^ℬ(c') s^𝒟(c) < 0`. -/
theorem theta_lt_iff_cross_neg {c c' : ι → ℝ} (hs : 0 < P.s c) (hs' : 0 < P.s c') :
    P.theta c' < P.theta c ↔ P.sB c * P.sD c' - P.sB c' * P.sD c < 0 := by
  unfold theta
  rw [div_lt_div_iff₀ hs' hs]
  unfold s
  constructor <;> intro h <;> linarith

/-- **Spec 1.5 (alignment change), `>`.** For two arbitrary non-zero states `c, c'`:
`θ(c) < θ(c') ↔ 0 < s^ℬ(c) s^𝒟(c') - s^ℬ(c') s^𝒟(c)`. -/
theorem theta_gt_iff_cross_pos {c c' : ι → ℝ} (hs : 0 < P.s c) (hs' : 0 < P.s c') :
    P.theta c < P.theta c' ↔ 0 < P.sB c * P.sD c' - P.sB c' * P.sD c := by
  unfold theta
  rw [div_lt_div_iff₀ hs hs']
  unfold s
  constructor <;> intro h <;> linarith

/-- **Spec 1.5 (alignment change), `=`.** For two arbitrary non-zero states `c, c'`:
`θ(c') = θ(c) ↔ s^ℬ(c) s^𝒟(c') - s^ℬ(c') s^𝒟(c) = 0`. -/
theorem theta_eq_iff_cross_eq_zero {c c' : ι → ℝ} (hs : 0 < P.s c) (hs' : 0 < P.s c') :
    P.theta c' = P.theta c ↔ P.sB c * P.sD c' - P.sB c' * P.sD c = 0 := by
  unfold theta
  rw [div_eq_div_iff hs'.ne' hs.ne']
  unfold s
  constructor <;> intro h <;> linarith

/-- **Spec 1.5 for the filtered step, `<`.** The alignment decreases iff `p^f η² + q^f η < 0`. -/
theorem theta_cNextF_lt_iff (f : ℝ → ℝ) {η : ℝ} {c : ι → ℝ} (hs : 0 < P.s c)
    (hs' : 0 < P.s (P.cNextF f η c)) :
    P.theta (P.cNextF f η c) < P.theta c ↔ P.pF f c * η ^ 2 + P.qF f c * η < 0 := by
  rw [P.theta_lt_iff_cross_neg hs hs', ← P.fCompareF_eq, fCompareF]

/-- **Spec 1.5 for the filtered step, `>`.** The alignment increases iff `0 < p^f η² + q^f η`. -/
theorem theta_cNextF_gt_iff (f : ℝ → ℝ) {η : ℝ} {c : ι → ℝ} (hs : 0 < P.s c)
    (hs' : 0 < P.s (P.cNextF f η c)) :
    P.theta c < P.theta (P.cNextF f η c) ↔ 0 < P.pF f c * η ^ 2 + P.qF f c * η := by
  rw [P.theta_gt_iff_cross_pos hs hs', ← P.fCompareF_eq, fCompareF]

/-- **Spec 1.5 for the filtered step, `=`.** The alignment is unchanged iff
`p^f η² + q^f η = 0`. -/
theorem theta_cNextF_eq_iff (f : ℝ → ℝ) {η : ℝ} {c : ι → ℝ} (hs : 0 < P.s c)
    (hs' : 0 < P.s (P.cNextF f η c)) :
    P.theta (P.cNextF f η c) = P.theta c ↔ P.pF f c * η ^ 2 + P.qF f c * η = 0 := by
  rw [P.theta_eq_iff_cross_eq_zero hs hs', ← P.fCompareF_eq, fCompareF]

end Spec

/-! ### Pair sums over `𝒟 × ℬ` (helpers for 1.6–1.9) -/

namespace FilterCoordinate

/-- The pair sum `∑_{i∈𝒟} ∑_{j∈ℬ} s_i s_j F i j` with `s_i = λ_i² c_i²`. -/
def pairSum (P : Spec ι) (c : ι → ℝ) (F : ι → ι → ℝ) : ℝ :=
  ∑ i ∈ P.D, ∑ j ∈ P.B, (P.lam i ^ 2 * c i ^ 2) * (P.lam j ^ 2 * c j ^ 2) * F i j

/-- A positive block moment has a non-zero coefficient in the block. -/
theorem exists_ne_zero_of_mom_pos (P : Spec ι) {S : Finset ι} {p : ℕ} {c : ι → ℝ}
    (h : 0 < P.mom S p c) : ∃ i ∈ S, c i ≠ 0 := by
  by_contra hne
  have hz : ∀ i ∈ S, c i = 0 := fun i hi => by
    by_contra hci
    exact hne ⟨i, hi, hci⟩
  have h0 : P.mom S p c = 0 := Finset.sum_eq_zero fun i hi => by rw [hz i hi]; ring
  linarith

/-- A non-zero coefficient in a block makes the block moment positive. -/
theorem mom_pos_of_ne_zero (P : Spec ι) {S : Finset ι} (p : ℕ) {c : ι → ℝ} {i : ι} (hi : i ∈ S)
    (hc : c i ≠ 0) : 0 < P.mom S p c := by
  unfold Spec.mom
  refine Finset.sum_pos' (fun j _ => mul_nonneg (pow_nonneg (P.lam_pos j).le _) (sq_nonneg _))
    ⟨i, hi, mul_pos (pow_pos (P.lam_pos i) _) (by positivity)⟩

/-- `∑_S λ^p (a c)² = a² ∑_S λ^p c²`. -/
theorem mom_smul (P : Spec ι) (S : Finset ι) (p : ℕ) (a : ℝ) (c : ι → ℝ) :
    P.mom S p (a • c) = a ^ 2 * P.mom S p c := by
  unfold Spec.mom
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem pairSum_term_le (P : Spec ι) {c : ι → ℝ} {F G : ι → ι → ℝ} {i j : ι}
    (h : c i ≠ 0 → c j ≠ 0 → F i j ≤ G i j) :
    (P.lam i ^ 2 * c i ^ 2) * (P.lam j ^ 2 * c j ^ 2) * F i j ≤
      (P.lam i ^ 2 * c i ^ 2) * (P.lam j ^ 2 * c j ^ 2) * G i j := by
  by_cases hci : c i = 0
  · simp [hci]
  by_cases hcj : c j = 0
  · simp [hcj]
  exact mul_le_mul_of_nonneg_left (h hci hcj)
    (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (mul_nonneg (sq_nonneg _) (sq_nonneg _)))

/-- Termwise comparison of pair sums; only pairs of non-zero coefficients matter. -/
theorem pairSum_le_pairSum (P : Spec ι) {c : ι → ℝ} {F G : ι → ι → ℝ}
    (h : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → F i j ≤ G i j) :
    pairSum P c F ≤ pairSum P c G :=
  Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => pairSum_term_le P (h i hi j hj)

/-- Strict termwise comparison of pair sums when both blocks carry energy. -/
theorem pairSum_lt_pairSum (P : Spec ι) {c : ι → ℝ} {F G : ι → ι → ℝ}
    (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (h : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → F i j < G i j) :
    pairSum P c F < pairSum P c G := by
  obtain ⟨i0, hi0, hci0⟩ := exists_ne_zero_of_mom_pos P hD
  obtain ⟨j0, hj0, hcj0⟩ := exists_ne_zero_of_mom_pos P hB
  have hterm : ∀ i ∈ P.D, ∀ j ∈ P.B,
      (P.lam i ^ 2 * c i ^ 2) * (P.lam j ^ 2 * c j ^ 2) * F i j ≤
        (P.lam i ^ 2 * c i ^ 2) * (P.lam j ^ 2 * c j ^ 2) * G i j :=
    fun i hi j hj => pairSum_term_le P fun hci hcj => (h i hi j hj hci hcj).le
  refine Finset.sum_lt_sum (fun i hi => Finset.sum_le_sum fun j hj => hterm i hi j hj)
    ⟨i0, hi0, ?_⟩
  refine Finset.sum_lt_sum (fun j hj => hterm i0 hi0 j hj) ⟨j0, hj0, ?_⟩
  have hi := P.lam_pos i0
  have hj := P.lam_pos j0
  exact mul_lt_mul_of_pos_left (h i0 hi0 j0 hj0 hci0 hcj0) (by positivity)

theorem pairSum_mul_left (P : Spec ι) (c : ι → ℝ) (a : ℝ) (F : ι → ι → ℝ) :
    pairSum P c (fun i j => a * F i j) = a * pairSum P c F := by
  simp only [pairSum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

@[simp] theorem pairSum_zero (P : Spec ι) (c : ι → ℝ) : pairSum P c (fun _ _ => 0) = 0 := by
  simp [pairSum]

/-- `s^𝒟 ∑_ℬ s_j g_j - s^ℬ ∑_𝒟 s_i h_i = ∑_𝒟 ∑_ℬ s_i s_j (g_j - h_i)`. -/
theorem cross_eq_pairSum (P : Spec ι) (c : ι → ℝ) (g h : ι → ℝ) :
    P.sD c * (∑ j ∈ P.B, P.lam j ^ 2 * c j ^ 2 * g j) -
        P.sB c * (∑ i ∈ P.D, P.lam i ^ 2 * c i ^ 2 * h i) =
      pairSum P c (fun i j => g j - h i) := by
  have h2 : P.sB c * (∑ i ∈ P.D, P.lam i ^ 2 * c i ^ 2 * h i) =
      ∑ i ∈ P.D, ∑ j ∈ P.B, (P.lam j ^ 2 * c j ^ 2) * (P.lam i ^ 2 * c i ^ 2 * h i) := by
    unfold Spec.sB Spec.mom
    rw [Finset.sum_mul_sum, Finset.sum_comm]
  unfold pairSum
  rw [h2]
  unfold Spec.sD Spec.mom
  rw [Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem momF_eq (P : Spec ι) (f : ℝ → ℝ) (S : Finset ι) (a : ℕ) (c : ι → ℝ) :
    P.momF f S a c = ∑ i ∈ S, P.lam i ^ 2 * c i ^ 2 * P.nu f c i ^ a :=
  Finset.sum_congr rfl fun i _ => by ring

theorem qF_eq_pairSum (P : Spec ι) (f : ℝ → ℝ) (c : ι → ℝ) :
    P.qF f c = 2 * pairSum P c (fun i j => P.nu f c j - P.nu f c i) := by
  have h := cross_eq_pairSum P c (fun j => P.nu f c j ^ 1) (fun i => P.nu f c i ^ 1)
  simp only [pow_one] at h
  rw [Spec.qF, momF_eq, momF_eq]
  simp only [pow_one]
  rw [h]

theorem pF_eq_pairSum (P : Spec ι) (f : ℝ → ℝ) (c : ι → ℝ) :
    P.pF f c = pairSum P c (fun i j => P.nu f c i ^ 2 - P.nu f c j ^ 2) := by
  have h := cross_eq_pairSum P c (fun j => P.nu f c j ^ 2) (fun i => P.nu f c i ^ 2)
  have h' : pairSum P c (fun i j => P.nu f c i ^ 2 - P.nu f c j ^ 2) =
      -1 * pairSum P c (fun i j => P.nu f c j ^ 2 - P.nu f c i ^ 2) := by
    rw [← pairSum_mul_left]
    congr 1
    funext i j
    ring
  rw [Spec.pF, momF_eq, momF_eq, h', ← h]
  ring

/-- `-q^f / 2` as a pair sum with the weights `w_ij = s_i s_j (ν_i - ν_j)`. -/
theorem neg_qF_eq_pairSum (P : Spec ι) (f : ℝ → ℝ) (c : ι → ℝ) :
    -P.qF f c = 2 * pairSum P c (fun i j => P.nu f c i - P.nu f c j) := by
  have h' : pairSum P c (fun i j => P.nu f c i - P.nu f c j) =
      -1 * pairSum P c (fun i j => P.nu f c j - P.nu f c i) := by
    rw [← pairSum_mul_left]
    congr 1
    funext i j
    ring
  rw [qF_eq_pairSum, h']
  ring

/-- `p^f > 0` if on pairs of non-zero coefficients `ν_j < ν_i` and `ν_i + ν_j > 0`. -/
theorem pF_pos_of_lt_of_add_pos (P : Spec ι) {f : ℝ → ℝ} {c : ι → ℝ}
    (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hord : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → P.nu f c j < P.nu f c i)
    (hsum : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → 0 < P.nu f c i + P.nu f c j) :
    0 < P.pF f c := by
  rw [pF_eq_pairSum, ← pairSum_zero P c]
  refine pairSum_lt_pairSum P hD hB fun i hi j hj hci hcj => ?_
  have h1 := hord i hi j hj hci hcj
  have h2 := hsum i hi j hj hci hcj
  nlinarith [mul_pos (sub_pos.mpr h1) h2]

/-- `p^f < 0` if on pairs of non-zero coefficients `ν_i < ν_j` and `ν_i + ν_j > 0`. -/
theorem pF_neg_of_lt_of_add_pos (P : Spec ι) {f : ℝ → ℝ} {c : ι → ℝ}
    (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hrev : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → P.nu f c i < P.nu f c j)
    (hsum : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → 0 < P.nu f c i + P.nu f c j) :
    P.pF f c < 0 := by
  rw [pF_eq_pairSum, ← pairSum_zero P c]
  refine pairSum_lt_pairSum P hD hB fun i hi j hj hci hcj => ?_
  have h1 := hrev i hi j hj hci hcj
  have h2 := hsum i hi j hj hci hcj
  nlinarith [mul_pos (sub_pos.mpr h1) h2]

/-- If two coordinates with non-zero coefficients, one in each block, have different effective
curvatures, the filtered step cannot annihilate the gradient: `s(c⁺) > 0` for every `η`. -/
theorem s_cNextF_pos_of_ne (P : Spec ι) {f : ℝ → ℝ} {c : ι → ℝ} {i j : ι}
    (hi : i ∈ P.D) (hj : j ∈ P.B) (hci : c i ≠ 0) (hcj : c j ≠ 0)
    (hne : P.nu f c i ≠ P.nu f c j) (η : ℝ) : 0 < P.s (P.cNextF f η c) := by
  have hDn := P.sD_nonneg (P.cNextF f η c)
  have hBn := P.sB_nonneg (P.cNextF f η c)
  by_cases h : 1 - η * P.nu f c i = 0
  · have h' : 1 - η * P.nu f c j ≠ 0 := by
      intro h2
      apply hne
      have hη : η ≠ 0 := by
        rintro rfl
        simp at h
      have h3 : η * P.nu f c i = η * P.nu f c j := by linarith
      exact mul_left_cancel₀ hη h3
    have hc : P.cNextF f η c j ≠ 0 := by
      rw [P.cNextF_eq]
      exact mul_ne_zero h' hcj
    have : 0 < P.sB (P.cNextF f η c) := mom_pos_of_ne_zero P 2 hj hc
    unfold Spec.s
    linarith
  · have hc : P.cNextF f η c i ≠ 0 := by
      rw [P.cNextF_eq]
      exact mul_ne_zero h hci
    have : 0 < P.sD (P.cNextF f η c) := mom_pos_of_ne_zero P 2 hi hc
    unfold Spec.s
    linarith

end FilterCoordinate

namespace Spec

variable (P : Spec ι)

open FilterCoordinate

/-! ### Statement 1.6: double-sum forms -/

/-- **Spec 1.6.** `q^f = 2 ∑_{i∈𝒟} ∑_{j∈ℬ} s_i s_j (ν_j - ν_i)` with `s_i = λ_i² c_i²`. -/
theorem qF_eq_double_sum (f : ℝ → ℝ) (c : ι → ℝ) :
    P.qF f c = 2 * ∑ i ∈ P.D, ∑ j ∈ P.B,
      (P.lam i ^ 2 * c i ^ 2) * (P.lam j ^ 2 * c j ^ 2) * (P.nu f c j - P.nu f c i) :=
  qF_eq_pairSum P f c

/-- **Spec 1.6.** `p^f = ∑_{i∈𝒟} ∑_{j∈ℬ} s_i s_j (ν_i² - ν_j²)` with `s_i = λ_i² c_i²`. -/
theorem pF_eq_double_sum (f : ℝ → ℝ) (c : ι → ℝ) :
    P.pF f c = ∑ i ∈ P.D, ∑ j ∈ P.B,
      (P.lam i ^ 2 * c i ^ 2) * (P.lam j ^ 2 * c j ^ 2) * (P.nu f c i ^ 2 - P.nu f c j ^ 2) :=
  pF_eq_pairSum P f c

/-- **Spec 1.9 (proof identity).** `η*_f = 2 ∑ w_ij / ∑ w_ij (ν_i + ν_j)` with the weights
`w_ij = s_i s_j (ν_i - ν_j)`, the sums running over `i ∈ 𝒟`, `j ∈ ℬ`. -/
theorem etaStarF_eq_double_sum (f : ℝ → ℝ) (c : ι → ℝ) :
    P.etaStarF f c =
      2 * (∑ i ∈ P.D, ∑ j ∈ P.B,
        (P.lam i ^ 2 * c i ^ 2) * (P.lam j ^ 2 * c j ^ 2) * (P.nu f c i - P.nu f c j)) /
      ∑ i ∈ P.D, ∑ j ∈ P.B, (P.lam i ^ 2 * c i ^ 2) * (P.lam j ^ 2 * c j ^ 2) *
        ((P.nu f c i - P.nu f c j) * (P.nu f c i + P.nu f c j)) := by
  have h : ∀ i j : ι, (P.nu f c i - P.nu f c j) * (P.nu f c i + P.nu f c j) =
      P.nu f c i ^ 2 - P.nu f c j ^ 2 := fun i j => by ring
  simp only [h]
  rw [etaStarF, neg_qF_eq_pairSum, pF_eq_pairSum]
  rfl

/-! ### Statement 1.7: curvature ordering preserved ⇒ Deng's dichotomy -/

section Ordered

variable {f : ℝ → ℝ} {c : ι → ℝ}

/-- **Spec 1.7.** If both blocks carry energy and `ν_j < ν_i` for all `i ∈ 𝒟`, `j ∈ ℬ` with
non-zero coefficients, then `q^f < 0`.  (No sign condition on `ν` is needed here.) -/
theorem qF_neg_of_ordered (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hord : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → P.nu f c j < P.nu f c i) :
    P.qF f c < 0 := by
  have h : pairSum P c (fun i j => P.nu f c j - P.nu f c i) < pairSum P c (fun _ _ => 0) :=
    pairSum_lt_pairSum P hD hB fun i hi j hj hci hcj => by
      linarith [hord i hi j hj hci hcj]
  rw [pairSum_zero] at h
  rw [qF_eq_pairSum]
  linarith

/-- **Spec 1.7.** If both blocks carry energy, `ν_j ≥ 0` on the bulk and `ν_j < ν_i` for all
`i ∈ 𝒟`, `j ∈ ℬ` (non-zero coefficients), then `p^f > 0`. -/
theorem pF_pos_of_ordered (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hnn : ∀ j ∈ P.B, c j ≠ 0 → 0 ≤ P.nu f c j)
    (hord : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → P.nu f c j < P.nu f c i) :
    0 < P.pF f c :=
  pF_pos_of_lt_of_add_pos P hD hB hord fun i hi j hj hci hcj => by
    linarith [hord i hi j hj hci hcj, hnn j hj hcj]

/-- **Spec 1.7.** Under the curvature ordering, `η*_f = -q^f / p^f > 0`. -/
theorem etaStarF_pos_of_ordered (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hnn : ∀ j ∈ P.B, c j ≠ 0 → 0 ≤ P.nu f c j)
    (hord : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → P.nu f c j < P.nu f c i) :
    0 < P.etaStarF f c :=
  div_pos (neg_pos.mpr (P.qF_neg_of_ordered hD hB hord)) (P.pF_pos_of_ordered hD hB hnn hord)

/-- **Spec 1.7 (the proviso `s(c⁺) > 0` is automatic).** Under the curvature ordering the filtered
step never annihilates the gradient: `s(c⁺) > 0` for every real `η`. -/
theorem s_cNextF_pos_of_ordered (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hord : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → P.nu f c j < P.nu f c i) (η : ℝ) :
    0 < P.s (P.cNextF f η c) := by
  obtain ⟨i, hi, hci⟩ := exists_ne_zero_of_mom_pos P hD
  obtain ⟨j, hj, hcj⟩ := exists_ne_zero_of_mom_pos P hB
  exact s_cNextF_pos_of_ne P hi hj hci hcj (hord i hi j hj hci hcj).ne' η

/-- **Spec 1.7, all real `η`.** Under the curvature ordering the alignment decreases iff
`0 < η < η*_f`. -/
theorem theta_cNextF_lt_iff_of_ordered' (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hnn : ∀ j ∈ P.B, c j ≠ 0 → 0 ≤ P.nu f c j)
    (hord : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → P.nu f c j < P.nu f c i) (η : ℝ) :
    P.theta (P.cNextF f η c) < P.theta c ↔ 0 < η ∧ η < P.etaStarF f c := by
  have hs : 0 < P.s c := by unfold s; linarith
  rw [P.theta_cNextF_lt_iff f hs (P.s_cNextF_pos_of_ordered hD hB hord η)]
  exact quad_neg_iff (P.pF_pos_of_ordered hD hB hnn hord) (P.qF_neg_of_ordered hD hB hord)

/-- **Spec 1.7, all real `η`.** Under the curvature ordering the alignment is unchanged iff
`η = 0` or `η = η*_f`. -/
theorem theta_cNextF_eq_iff_of_ordered' (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hnn : ∀ j ∈ P.B, c j ≠ 0 → 0 ≤ P.nu f c j)
    (hord : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → P.nu f c j < P.nu f c i) (η : ℝ) :
    P.theta (P.cNextF f η c) = P.theta c ↔ η = 0 ∨ η = P.etaStarF f c := by
  have hs : 0 < P.s c := by unfold s; linarith
  rw [P.theta_cNextF_eq_iff f hs (P.s_cNextF_pos_of_ordered hD hB hord η)]
  exact quad_eq_zero_iff (P.pF_pos_of_ordered hD hB hnn hord).ne'

/-- **Spec 1.7, all real `η`.** Under the curvature ordering the alignment increases iff
`η < 0` or `η > η*_f`. -/
theorem theta_cNextF_gt_iff_of_ordered' (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hnn : ∀ j ∈ P.B, c j ≠ 0 → 0 ≤ P.nu f c j)
    (hord : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → P.nu f c j < P.nu f c i) (η : ℝ) :
    P.theta c < P.theta (P.cNextF f η c) ↔ η < 0 ∨ P.etaStarF f c < η := by
  have hs : 0 < P.s c := by unfold s; linarith
  rw [P.theta_cNextF_gt_iff f hs (P.s_cNextF_pos_of_ordered hD hB hord η)]
  exact quad_pos_iff (P.pF_pos_of_ordered hD hB hnn hord) (P.qF_neg_of_ordered hD hB hord)

/-- **Spec 1.7 (Deng's dichotomy for a filtered step), decrease.** Suppose `s^𝒟, s^ℬ > 0`,
`ν_j ≥ 0` on the bulk and `ν_j < ν_i` for all `i ∈ 𝒟`, `j ∈ ℬ` (non-zero coefficients).  Then for
`η > 0` the alignment decreases iff `η < η*_f`. -/
theorem theta_cNextF_lt_iff_of_ordered (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hnn : ∀ j ∈ P.B, c j ≠ 0 → 0 ≤ P.nu f c j)
    (hord : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → P.nu f c j < P.nu f c i)
    {η : ℝ} (hη : 0 < η) :
    P.theta (P.cNextF f η c) < P.theta c ↔ η < P.etaStarF f c := by
  rw [P.theta_cNextF_lt_iff_of_ordered' hD hB hnn hord η]
  exact and_iff_right hη

/-- **Spec 1.7, unchanged.** Under the hypotheses of `theta_cNextF_lt_iff_of_ordered`, for `η > 0`
the alignment is unchanged iff `η = η*_f`. -/
theorem theta_cNextF_eq_iff_of_ordered (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hnn : ∀ j ∈ P.B, c j ≠ 0 → 0 ≤ P.nu f c j)
    (hord : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → P.nu f c j < P.nu f c i)
    {η : ℝ} (hη : 0 < η) :
    P.theta (P.cNextF f η c) = P.theta c ↔ η = P.etaStarF f c := by
  rw [P.theta_cNextF_eq_iff_of_ordered' hD hB hnn hord η]
  exact or_iff_right hη.ne'

/-- **Spec 1.7, increase.** Under the hypotheses of `theta_cNextF_lt_iff_of_ordered`, for `η > 0`
the alignment increases iff `η > η*_f`. -/
theorem theta_cNextF_gt_iff_of_ordered (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hnn : ∀ j ∈ P.B, c j ≠ 0 → 0 ≤ P.nu f c j)
    (hord : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → P.nu f c j < P.nu f c i)
    {η : ℝ} (hη : 0 < η) :
    P.theta c < P.theta (P.cNextF f η c) ↔ P.etaStarF f c < η := by
  rw [P.theta_cNextF_gt_iff_of_ordered' hD hB hnn hord η]
  exact or_iff_right (not_lt.mpr hη.le)

end Ordered

/-! ### Statement 1.8: curvature ordering reversed ⇒ the dichotomy flips -/

section Reversed

variable {f : ℝ → ℝ} {c : ι → ℝ}

/-- **Spec 1.8.** If both blocks carry energy and `ν_i < ν_j` for all `i ∈ 𝒟`, `j ∈ ℬ` with
non-zero coefficients, then `q^f > 0`. -/
theorem qF_pos_of_reversed (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hrev : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → P.nu f c i < P.nu f c j) :
    0 < P.qF f c := by
  have h : pairSum P c (fun _ _ => 0) < pairSum P c (fun i j => P.nu f c j - P.nu f c i) :=
    pairSum_lt_pairSum P hD hB fun i hi j hj hci hcj => by
      linarith [hrev i hi j hj hci hcj]
  rw [pairSum_zero] at h
  rw [qF_eq_pairSum]
  linarith

/-- **Spec 1.8.** If both blocks carry energy, `ν_i ≥ 0` on the dominant block and `ν_i < ν_j`
for all `i ∈ 𝒟`, `j ∈ ℬ` (non-zero coefficients), then `p^f < 0`. -/
theorem pF_neg_of_reversed (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hnn : ∀ i ∈ P.D, c i ≠ 0 → 0 ≤ P.nu f c i)
    (hrev : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → P.nu f c i < P.nu f c j) :
    P.pF f c < 0 :=
  pF_neg_of_lt_of_add_pos P hD hB hrev fun i hi j hj hci hcj => by
    linarith [hrev i hi j hj hci hcj, hnn i hi hci]

/-- **Spec 1.8.** Under the reversed curvature ordering, `η*_f = -q^f / p^f > 0`. -/
theorem etaStarF_pos_of_reversed (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hnn : ∀ i ∈ P.D, c i ≠ 0 → 0 ≤ P.nu f c i)
    (hrev : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → P.nu f c i < P.nu f c j) :
    0 < P.etaStarF f c :=
  div_pos_of_neg_of_neg (neg_neg_of_pos (P.qF_pos_of_reversed hD hB hrev))
    (P.pF_neg_of_reversed hD hB hnn hrev)

/-- **Spec 1.8 (the proviso `s(c⁺) > 0` is automatic).** Under the reversed curvature ordering
`s(c⁺) > 0` for every real `η`. -/
theorem s_cNextF_pos_of_reversed (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hrev : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → P.nu f c i < P.nu f c j) (η : ℝ) :
    0 < P.s (P.cNextF f η c) := by
  obtain ⟨i, hi, hci⟩ := exists_ne_zero_of_mom_pos P hD
  obtain ⟨j, hj, hcj⟩ := exists_ne_zero_of_mom_pos P hB
  exact s_cNextF_pos_of_ne P hi hj hci hcj (hrev i hi j hj hci hcj).ne η

/-- `η*_f` written with the signs of the reversed case: `η*_f = -(-q^f) / (-p^f)`. -/
private theorem etaStarF_eq_neg (f : ℝ → ℝ) (c : ι → ℝ) :
    P.etaStarF f c = -(-P.qF f c) / (-P.pF f c) := by
  rw [etaStarF, neg_div_neg_eq, neg_div]

/-- **Spec 1.8, all real `η`.** Under the reversed curvature ordering the alignment **increases**
iff `0 < η < η*_f`. -/
theorem theta_cNextF_gt_iff_of_reversed' (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hnn : ∀ i ∈ P.D, c i ≠ 0 → 0 ≤ P.nu f c i)
    (hrev : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → P.nu f c i < P.nu f c j) (η : ℝ) :
    P.theta c < P.theta (P.cNextF f η c) ↔ 0 < η ∧ η < P.etaStarF f c := by
  have hs : 0 < P.s c := by unfold s; linarith
  have hp := P.pF_neg_of_reversed hD hB hnn hrev
  have hq := P.qF_pos_of_reversed hD hB hrev
  rw [P.theta_cNextF_gt_iff f hs (P.s_cNextF_pos_of_reversed hD hB hrev η), P.etaStarF_eq_neg,
    ← quad_neg_iff (neg_pos.mpr hp) (neg_neg_of_pos hq)]
  constructor <;> intro h <;> linarith

/-- **Spec 1.8, all real `η`.** Under the reversed curvature ordering the alignment is unchanged
iff `η = 0` or `η = η*_f`. -/
theorem theta_cNextF_eq_iff_of_reversed' (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hnn : ∀ i ∈ P.D, c i ≠ 0 → 0 ≤ P.nu f c i)
    (hrev : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → P.nu f c i < P.nu f c j) (η : ℝ) :
    P.theta (P.cNextF f η c) = P.theta c ↔ η = 0 ∨ η = P.etaStarF f c := by
  have hs : 0 < P.s c := by unfold s; linarith
  rw [P.theta_cNextF_eq_iff f hs (P.s_cNextF_pos_of_reversed hD hB hrev η)]
  exact quad_eq_zero_iff (P.pF_neg_of_reversed hD hB hnn hrev).ne

/-- **Spec 1.8, all real `η`.** Under the reversed curvature ordering the alignment decreases iff
`η < 0` or `η > η*_f`. -/
theorem theta_cNextF_lt_iff_of_reversed' (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hnn : ∀ i ∈ P.D, c i ≠ 0 → 0 ≤ P.nu f c i)
    (hrev : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → P.nu f c i < P.nu f c j) (η : ℝ) :
    P.theta (P.cNextF f η c) < P.theta c ↔ η < 0 ∨ P.etaStarF f c < η := by
  have hs : 0 < P.s c := by unfold s; linarith
  have hp := P.pF_neg_of_reversed hD hB hnn hrev
  have hq := P.qF_pos_of_reversed hD hB hrev
  rw [P.theta_cNextF_lt_iff f hs (P.s_cNextF_pos_of_reversed hD hB hrev η), P.etaStarF_eq_neg,
    ← quad_pos_iff (neg_pos.mpr hp) (neg_neg_of_pos hq)]
  constructor <;> intro h <;> linarith

/-- **Spec 1.8 (the dichotomy flips), increase.** Suppose `s^𝒟, s^ℬ > 0`, `ν_i ≥ 0` on the
dominant block and `ν_i < ν_j` for all `i ∈ 𝒟`, `j ∈ ℬ` (non-zero coefficients).  Then for `η > 0`
the alignment **increases** iff `η < η*_f`. -/
theorem theta_cNextF_gt_iff_of_reversed (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hnn : ∀ i ∈ P.D, c i ≠ 0 → 0 ≤ P.nu f c i)
    (hrev : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → P.nu f c i < P.nu f c j)
    {η : ℝ} (hη : 0 < η) :
    P.theta c < P.theta (P.cNextF f η c) ↔ η < P.etaStarF f c := by
  rw [P.theta_cNextF_gt_iff_of_reversed' hD hB hnn hrev η]
  exact and_iff_right hη

/-- **Spec 1.8, unchanged.** Under the reversed curvature ordering, for `η > 0` the alignment is
unchanged iff `η = η*_f`. -/
theorem theta_cNextF_eq_iff_of_reversed (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hnn : ∀ i ∈ P.D, c i ≠ 0 → 0 ≤ P.nu f c i)
    (hrev : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → P.nu f c i < P.nu f c j)
    {η : ℝ} (hη : 0 < η) :
    P.theta (P.cNextF f η c) = P.theta c ↔ η = P.etaStarF f c := by
  rw [P.theta_cNextF_eq_iff_of_reversed' hD hB hnn hrev η]
  exact or_iff_right hη.ne'

/-- **Spec 1.8, decrease.** Under the reversed curvature ordering, for `η > 0` the alignment
decreases iff `η > η*_f`. -/
theorem theta_cNextF_lt_iff_of_reversed (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hnn : ∀ i ∈ P.D, c i ≠ 0 → 0 ≤ P.nu f c i)
    (hrev : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → P.nu f c i < P.nu f c j)
    {η : ℝ} (hη : 0 < η) :
    P.theta (P.cNextF f η c) < P.theta c ↔ P.etaStarF f c < η := by
  rw [P.theta_cNextF_lt_iff_of_reversed' hD hB hnn hrev η]
  exact or_iff_right (not_lt.mpr hη.le)

end Reversed

/-! ### Statement 1.9: two-sided bound on the critical step size -/

section Bounds

variable {f : ℝ → ℝ} {c : ι → ℝ}

/-- **Spec 1.9, lower bound.** Under the hypotheses of 1.7, if `ν_i ≤ b_𝒟` on `𝒟` and
`ν_j ≤ b_ℬ` on `ℬ` (non-zero coefficients), then `2 / (b_𝒟 + b_ℬ) ≤ η*_f`.
(`b_𝒟 + b_ℬ > 0` is automatic.) -/
theorem two_div_le_etaStarF_of_ordered (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hnn : ∀ j ∈ P.B, c j ≠ 0 → 0 ≤ P.nu f c j)
    (hord : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → P.nu f c j < P.nu f c i)
    {bD bB : ℝ} (hbD : ∀ i ∈ P.D, c i ≠ 0 → P.nu f c i ≤ bD)
    (hbB : ∀ j ∈ P.B, c j ≠ 0 → P.nu f c j ≤ bB) :
    2 / (bD + bB) ≤ P.etaStarF f c := by
  have hp := P.pF_pos_of_ordered hD hB hnn hord
  obtain ⟨i0, hi0, hci0⟩ := exists_ne_zero_of_mom_pos P hD
  obtain ⟨j0, hj0, hcj0⟩ := exists_ne_zero_of_mom_pos P hB
  have hb : 0 < bD + bB := by
    linarith [hbD i0 hi0 hci0, hbB j0 hj0 hcj0, hord i0 hi0 j0 hj0 hci0 hcj0, hnn j0 hj0 hcj0]
  have key : P.pF f c ≤ (bD + bB) * pairSum P c (fun i j => P.nu f c i - P.nu f c j) := by
    rw [pF_eq_pairSum, ← pairSum_mul_left]
    refine pairSum_le_pairSum P fun i hi j hj hci hcj => ?_
    have h1 := hord i hi j hj hci hcj
    have h2 := hbD i hi hci
    have h3 := hbB j hj hcj
    nlinarith [mul_nonneg (sub_nonneg.mpr h1.le)
      (show 0 ≤ bD + bB - (P.nu f c i + P.nu f c j) by linarith)]
  rw [etaStarF, div_le_div_iff₀ hb hp, neg_qF_eq_pairSum]
  linarith

/-- **Spec 1.9, upper bound.** If both blocks carry energy, `ν_j < ν_i` for all `i ∈ 𝒟`, `j ∈ ℬ`,
`a_𝒟 ≤ ν_i` on `𝒟`, `a_ℬ ≤ ν_j` on `ℬ` (non-zero coefficients) and `a_𝒟 + a_ℬ > 0`, then
`η*_f ≤ 2 / (a_𝒟 + a_ℬ)`.  (The sign condition `ν ≥ 0` of 1.7 is implied by `a_𝒟 + a_ℬ > 0` as
far as it is needed.) -/
theorem etaStarF_le_two_div_of_ordered (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hord : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → P.nu f c j < P.nu f c i)
    {aD aB : ℝ} (haD : ∀ i ∈ P.D, c i ≠ 0 → aD ≤ P.nu f c i)
    (haB : ∀ j ∈ P.B, c j ≠ 0 → aB ≤ P.nu f c j) (ha : 0 < aD + aB) :
    P.etaStarF f c ≤ 2 / (aD + aB) := by
  have hp : 0 < P.pF f c := pF_pos_of_lt_of_add_pos P hD hB hord fun i hi j hj hci hcj => by
    linarith [haD i hi hci, haB j hj hcj]
  have key : (aD + aB) * pairSum P c (fun i j => P.nu f c i - P.nu f c j) ≤ P.pF f c := by
    rw [pF_eq_pairSum, ← pairSum_mul_left]
    refine pairSum_le_pairSum P fun i hi j hj hci hcj => ?_
    have h1 := hord i hi j hj hci hcj
    have h2 := haD i hi hci
    have h3 := haB j hj hcj
    nlinarith [mul_nonneg (sub_nonneg.mpr h1.le)
      (show 0 ≤ P.nu f c i + P.nu f c j - (aD + aB) by linarith)]
  rw [etaStarF, div_le_div_iff₀ hp ha, neg_qF_eq_pairSum]
  linarith

/-- **Spec 1.9 (two-sided bound on the critical step size).** Under the hypotheses of 1.7, if
`a_𝒟 ≤ ν_i ≤ b_𝒟` on `𝒟`, `a_ℬ ≤ ν_j ≤ b_ℬ` on `ℬ` (non-zero coefficients) and `a_𝒟 + a_ℬ > 0`:
`2 / (b_𝒟 + b_ℬ) ≤ η*_f ≤ 2 / (a_𝒟 + a_ℬ)`. -/
theorem etaStarF_mem_Icc_of_ordered (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hnn : ∀ j ∈ P.B, c j ≠ 0 → 0 ≤ P.nu f c j)
    (hord : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → P.nu f c j < P.nu f c i)
    {aD bD aB bB : ℝ} (haD : ∀ i ∈ P.D, c i ≠ 0 → aD ≤ P.nu f c i)
    (hbD : ∀ i ∈ P.D, c i ≠ 0 → P.nu f c i ≤ bD)
    (haB : ∀ j ∈ P.B, c j ≠ 0 → aB ≤ P.nu f c j)
    (hbB : ∀ j ∈ P.B, c j ≠ 0 → P.nu f c j ≤ bB) (ha : 0 < aD + aB) :
    P.etaStarF f c ∈ Set.Icc (2 / (bD + bB)) (2 / (aD + aB)) :=
  ⟨P.two_div_le_etaStarF_of_ordered hD hB hnn hord hbD hbB,
    P.etaStarF_le_two_div_of_ordered hD hB hord haD haB ha⟩

/-- **Extra (1.9 in the reversed case of 1.8), lower bound.** Under the hypotheses of 1.8, if
`ν_i ≤ b_𝒟` on `𝒟` and `ν_j ≤ b_ℬ` on `ℬ` (non-zero coefficients): `2 / (b_𝒟 + b_ℬ) ≤ η*_f`. -/
theorem two_div_le_etaStarF_of_reversed (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hnn : ∀ i ∈ P.D, c i ≠ 0 → 0 ≤ P.nu f c i)
    (hrev : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → P.nu f c i < P.nu f c j)
    {bD bB : ℝ} (hbD : ∀ i ∈ P.D, c i ≠ 0 → P.nu f c i ≤ bD)
    (hbB : ∀ j ∈ P.B, c j ≠ 0 → P.nu f c j ≤ bB) :
    2 / (bD + bB) ≤ P.etaStarF f c := by
  have hp := P.pF_neg_of_reversed hD hB hnn hrev
  obtain ⟨i0, hi0, hci0⟩ := exists_ne_zero_of_mom_pos P hD
  obtain ⟨j0, hj0, hcj0⟩ := exists_ne_zero_of_mom_pos P hB
  have hb : 0 < bD + bB := by
    linarith [hbD i0 hi0 hci0, hbB j0 hj0 hcj0, hrev i0 hi0 j0 hj0 hci0 hcj0, hnn i0 hi0 hci0]
  have key : (bD + bB) * pairSum P c (fun i j => P.nu f c i - P.nu f c j) ≤ P.pF f c := by
    rw [pF_eq_pairSum, ← pairSum_mul_left]
    refine pairSum_le_pairSum P fun i hi j hj hci hcj => ?_
    have h1 := hrev i hi j hj hci hcj
    have h2 := hbD i hi hci
    have h3 := hbB j hj hcj
    nlinarith [mul_nonneg (sub_nonneg.mpr h1.le)
      (show 0 ≤ bD + bB - (P.nu f c i + P.nu f c j) by linarith)]
  have hq := neg_qF_eq_pairSum P f c
  rw [P.etaStarF_eq_neg, div_le_div_iff₀ hb (neg_pos.mpr hp), hq]
  linarith

/-- **Extra (1.9 in the reversed case of 1.8), upper bound.** If both blocks carry energy,
`ν_i < ν_j` for all `i ∈ 𝒟`, `j ∈ ℬ`, `a_𝒟 ≤ ν_i` on `𝒟`, `a_ℬ ≤ ν_j` on `ℬ` (non-zero
coefficients) and `a_𝒟 + a_ℬ > 0`: `η*_f ≤ 2 / (a_𝒟 + a_ℬ)`. -/
theorem etaStarF_le_two_div_of_reversed (hD : 0 < P.sD c) (hB : 0 < P.sB c)
    (hrev : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → P.nu f c i < P.nu f c j)
    {aD aB : ℝ} (haD : ∀ i ∈ P.D, c i ≠ 0 → aD ≤ P.nu f c i)
    (haB : ∀ j ∈ P.B, c j ≠ 0 → aB ≤ P.nu f c j) (ha : 0 < aD + aB) :
    P.etaStarF f c ≤ 2 / (aD + aB) := by
  have hp : P.pF f c < 0 := pF_neg_of_lt_of_add_pos P hD hB hrev fun i hi j hj hci hcj => by
    linarith [haD i hi hci, haB j hj hcj]
  have key : P.pF f c ≤ (aD + aB) * pairSum P c (fun i j => P.nu f c i - P.nu f c j) := by
    rw [pF_eq_pairSum, ← pairSum_mul_left]
    refine pairSum_le_pairSum P fun i hi j hj hci hcj => ?_
    have h1 := hrev i hi j hj hci hcj
    have h2 := haD i hi hci
    have h3 := haB j hj hcj
    nlinarith [mul_nonneg (sub_nonneg.mpr h1.le)
      (show 0 ≤ P.nu f c i + P.nu f c j - (aD + aB) by linarith)]
  have hq := neg_qF_eq_pairSum P f c
  rw [P.etaStarF_eq_neg, div_le_div_iff₀ (neg_pos.mpr hp) ha, hq]
  linarith

end Bounds

/-! ### SGD (`f = id`): the noise-free case of Deng's theory -/

section SGD

variable {c : ι → ℝ}

/-- For SGD the curvature ordering holds by the spectral gap: `ν_j = λ_j < λ_i = ν_i` for
`i ∈ 𝒟`, `j ∈ ℬ` with non-zero coefficients. -/
theorem nu_id_lt_nu_id {i j : ι} (hi : i ∈ P.D) (hj : j ∈ P.B) (hci : c i ≠ 0) (hcj : c j ≠ 0) :
    P.nu _root_.id c j < P.nu _root_.id c i := by
  rw [P.nu_id hci, P.nu_id hcj]
  calc P.lam j ≤ P.lamk1 := P.le_lamk1_of_mem_B hj
    _ < P.lamk := P.lamk1_lt_lamk
    _ ≤ P.lam i := P.lamk_le_of_mem hi

/-- Noise-free Deng: `p_t > 0` (with `e_𝒟 = e_ℬ = 0`) whenever both blocks carry energy. -/
theorem pCoef_noiseFree_pos (hD : 0 < P.sD c) (hB : 0 < P.sB c) :
    0 < P.pCoef Noise.noiseFree c := by
  rw [← P.pF_id]
  exact P.pF_pos_of_ordered hD hB (fun j _ _ => P.nu_id_nonneg c j)
    fun i hi j hj hci hcj => P.nu_id_lt_nu_id hi hj hci hcj

/-- Noise-free Deng: `η*₀ > 0` whenever both blocks carry energy. -/
theorem etaStar_noiseFree_pos (hD : 0 < P.sD c) (hB : 0 < P.sB c) :
    0 < P.etaStar Noise.noiseFree c := by
  rw [← P.etaStarF_id]
  exact P.etaStarF_pos_of_ordered hD hB (fun j _ _ => P.nu_id_nonneg c j)
    fun i hi j hj hci hcj => P.nu_id_lt_nu_id hi hj hci hcj

/-- A noise-free SGD step never annihilates the gradient when both blocks carry energy. -/
theorem s_cNext_noiseFree_pos (hD : 0 < P.sD c) (hB : 0 < P.sB c) (η : ℝ) :
    0 < P.s (P.cNext η c 0) := by
  rw [← P.cNextF_id]
  exact P.s_cNextF_pos_of_ordered hD hB (fun i hi j hj hci hcj => P.nu_id_lt_nu_id hi hj hci hcj) η

/-- **Spec 1.7 for `f = id`, all real `η`** (noise-free, exact finite-`d` form of Deng's
Theorem 2): the alignment decreases iff `0 < η < η*₀`. -/
theorem theta_cNext_noiseFree_lt_iff' (hD : 0 < P.sD c) (hB : 0 < P.sB c) (η : ℝ) :
    P.theta (P.cNext η c 0) < P.theta c ↔ 0 < η ∧ η < P.etaStar Noise.noiseFree c := by
  rw [← P.cNextF_id, ← P.etaStarF_id]
  exact P.theta_cNextF_lt_iff_of_ordered' hD hB (fun j _ _ => P.nu_id_nonneg c j)
    (fun i hi j hj hci hcj => P.nu_id_lt_nu_id hi hj hci hcj) η

/-- **Spec 1.7 for `f = id`, all real `η`**: the alignment is unchanged iff `η = 0` or
`η = η*₀`. -/
theorem theta_cNext_noiseFree_eq_iff' (hD : 0 < P.sD c) (hB : 0 < P.sB c) (η : ℝ) :
    P.theta (P.cNext η c 0) = P.theta c ↔ η = 0 ∨ η = P.etaStar Noise.noiseFree c := by
  rw [← P.cNextF_id, ← P.etaStarF_id]
  exact P.theta_cNextF_eq_iff_of_ordered' hD hB (fun j _ _ => P.nu_id_nonneg c j)
    (fun i hi j hj hci hcj => P.nu_id_lt_nu_id hi hj hci hcj) η

/-- **Spec 1.7 for `f = id`, all real `η`** (noise-free, exact finite-`d` form of Deng's
Theorem 3): the alignment increases iff `η < 0` or `η > η*₀`. -/
theorem theta_cNext_noiseFree_gt_iff' (hD : 0 < P.sD c) (hB : 0 < P.sB c) (η : ℝ) :
    P.theta c < P.theta (P.cNext η c 0) ↔ η < 0 ∨ P.etaStar Noise.noiseFree c < η := by
  rw [← P.cNextF_id, ← P.etaStarF_id]
  exact P.theta_cNextF_gt_iff_of_ordered' hD hB (fun j _ _ => P.nu_id_nonneg c j)
    (fun i hi j hj hci hcj => P.nu_id_lt_nu_id hi hj hci hcj) η

/-- **Spec 1.7 for `f = id`** (noise-free case of Deng's Theorem 2, exact for every finite `d`):
if both blocks carry energy and `η > 0`, the alignment decreases iff `η < η*₀`. -/
theorem theta_cNext_noiseFree_lt_iff (hD : 0 < P.sD c) (hB : 0 < P.sB c) {η : ℝ} (hη : 0 < η) :
    P.theta (P.cNext η c 0) < P.theta c ↔ η < P.etaStar Noise.noiseFree c := by
  rw [P.theta_cNext_noiseFree_lt_iff' hD hB η]
  exact and_iff_right hη

/-- **Spec 1.7 for `f = id`**: for `η > 0` the alignment is unchanged iff `η = η*₀`. -/
theorem theta_cNext_noiseFree_eq_iff (hD : 0 < P.sD c) (hB : 0 < P.sB c) {η : ℝ} (hη : 0 < η) :
    P.theta (P.cNext η c 0) = P.theta c ↔ η = P.etaStar Noise.noiseFree c := by
  rw [P.theta_cNext_noiseFree_eq_iff' hD hB η]
  exact or_iff_right hη.ne'

/-- **Spec 1.7 for `f = id`** (noise-free case of Deng's Theorem 3, exact for every finite `d`):
for `η > 0` the alignment increases iff `η > η*₀`. -/
theorem theta_cNext_noiseFree_gt_iff (hD : 0 < P.sD c) (hB : 0 < P.sB c) {η : ℝ} (hη : 0 < η) :
    P.theta c < P.theta (P.cNext η c 0) ↔ P.etaStar Noise.noiseFree c < η := by
  rw [P.theta_cNext_noiseFree_gt_iff' hD hB η]
  exact or_iff_right (not_lt.mpr hη.le)

/-- **Spec 1.8, "this cannot happen for SGD".** For the identity filter the reversed curvature
ordering is impossible at a state where both blocks carry energy. -/
theorem not_reversed_id (hD : 0 < P.sD c) (hB : 0 < P.sB c) :
    ¬ ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → P.nu _root_.id c i < P.nu _root_.id c j := by
  intro h
  obtain ⟨i, hi, hci⟩ := exists_ne_zero_of_mom_pos P hD
  obtain ⟨j, hj, hcj⟩ := exists_ne_zero_of_mom_pos P hB
  exact lt_asymm (h i hi j hj hci hcj) (P.nu_id_lt_nu_id hi hj hci hcj)

/-- **Spec 1.8, "this cannot happen for SGD".** For the identity filter `q^f ≤ 0` at *every*
state, so the conclusion `p^f < 0 < q^f` of 1.8 never holds for SGD. -/
theorem qF_id_nonpos (c : ι → ℝ) : P.qF _root_.id c ≤ 0 := by
  have h : pairSum P c (fun i j => P.nu _root_.id c j - P.nu _root_.id c i) ≤
      pairSum P c (fun _ _ => 0) :=
    pairSum_le_pairSum P fun i hi j hj hci hcj => by
      linarith [P.nu_id_lt_nu_id hi hj hci hcj]
  rw [pairSum_zero] at h
  rw [qF_eq_pairSum]
  linarith

/-- **Spec 1.9, corollary for SGD (lower bound).** Noise-free Deng:
`2 / (λ_1 + λ_{k+1}) ≤ η*₀`. -/
theorem two_div_le_etaStar_noiseFree (hD : 0 < P.sD c) (hB : 0 < P.sB c) :
    2 / (P.lam1 + P.lamk1) ≤ P.etaStar Noise.noiseFree c := by
  rw [← P.etaStarF_id]
  exact P.two_div_le_etaStarF_of_ordered hD hB (fun j _ _ => P.nu_id_nonneg c j)
    (fun i hi j hj hci hcj => P.nu_id_lt_nu_id hi hj hci hcj)
    (fun i hi hci => by rw [P.nu_id hci]; exact P.le_lam1_of_mem hi)
    (fun j hj hcj => by rw [P.nu_id hcj]; exact P.le_lamk1_of_mem_B hj)

/-- **Spec 1.9, corollary for SGD (upper bound).** Noise-free Deng:
`η*₀ ≤ 2 / (λ_k + λ_d)`. -/
theorem etaStar_noiseFree_le_two_div (hD : 0 < P.sD c) (hB : 0 < P.sB c) :
    P.etaStar Noise.noiseFree c ≤ 2 / (P.lamk + P.lamd) := by
  rw [← P.etaStarF_id]
  exact P.etaStarF_le_two_div_of_ordered hD hB
    (fun i hi j hj hci hcj => P.nu_id_lt_nu_id hi hj hci hcj)
    (fun i hi hci => by rw [P.nu_id hci]; exact P.lamk_le_of_mem hi)
    (fun j hj hcj => by rw [P.nu_id hcj]; exact P.lamd_le_of_mem_B hj)
    (add_pos P.lamk_pos P.lamd_pos)

/-- **Spec 1.9, corollary for SGD.** Noise-free Deng:
`2 / (λ_1 + λ_{k+1}) ≤ η*₀ ≤ 2 / (λ_k + λ_d)`. -/
theorem etaStar_noiseFree_mem_Icc (hD : 0 < P.sD c) (hB : 0 < P.sB c) :
    P.etaStar Noise.noiseFree c ∈ Set.Icc (2 / (P.lam1 + P.lamk1)) (2 / (P.lamk + P.lamd)) :=
  ⟨P.two_div_le_etaStar_noiseFree hD hB, P.etaStar_noiseFree_le_two_div hD hB⟩

/-- With zero noise the right-hand side of Deng's Theorem 7,
`2 gap₁ / ((λ_1² - λ_d²) + s_max ψ_𝒟 / (λ_d² ‖x‖² θ))`, is `2 gap₁ / (λ_1² - λ_d²)`. -/
theorem thm7_noiseFree_bound_eq (c : ι → ℝ) :
    2 * P.gap1 / ((P.lam1 ^ 2 - P.lamd ^ 2) +
        (Noise.noiseFree : Noise ι).smax * P.psiD / (P.lamd ^ 2 * normSq c * P.theta c)) =
      2 * P.gap1 / (P.lam1 ^ 2 - P.lamd ^ 2) := by
  simp

/-- **Spec 1.9, comparison with Deng's Theorem 7.** The new lower bound is at least as good as
the noise-free bound of Theorem 7: `2 gap₁ / (λ_1² - λ_d²) ≤ 2 / (λ_1 + λ_{k+1})`. -/
theorem thm7_noiseFree_bound_le_two_div :
    2 * P.gap1 / (P.lam1 ^ 2 - P.lamd ^ 2) ≤ 2 / (P.lam1 + P.lamk1) := by
  have h1 := P.lam1_pos
  have hk1 := P.lamk1_pos
  have hd := P.lamd_pos
  have h2 := P.lamk_le_lam1
  have h3 := P.lamd_le_lamk1
  have h4 := P.lamd_lt_lam1
  have h5 := P.lamk1_lt_lamk
  have hden : 0 < P.lam1 ^ 2 - P.lamd ^ 2 := by nlinarith
  rw [div_le_div_iff₀ hden (by linarith)]
  unfold gap1
  nlinarith [mul_nonneg (sub_nonneg.mpr h2) (add_pos h1 hk1).le,
    mul_nonneg (sub_nonneg.mpr h3) (add_pos hd hk1).le]

/-- The comparison with Deng's Theorem 7 is strict unless the spectrum is two-level
(`λ_k = λ_1` and `λ_d = λ_{k+1}`). -/
theorem thm7_noiseFree_bound_lt_two_div (h : P.lamk < P.lam1 ∨ P.lamd < P.lamk1) :
    2 * P.gap1 / (P.lam1 ^ 2 - P.lamd ^ 2) < 2 / (P.lam1 + P.lamk1) := by
  have h1 := P.lam1_pos
  have hk1 := P.lamk1_pos
  have hd := P.lamd_pos
  have h2 := P.lamk_le_lam1
  have h3 := P.lamd_le_lamk1
  have h4 := P.lamd_lt_lam1
  have h5 := P.lamk1_lt_lamk
  have hden : 0 < P.lam1 ^ 2 - P.lamd ^ 2 := by nlinarith
  rw [div_lt_div_iff₀ hden (by linarith)]
  unfold gap1
  rcases h with h | h
  · nlinarith [mul_pos (sub_pos.mpr h) (add_pos h1 hk1),
      mul_nonneg (sub_nonneg.mpr h3) (add_pos hd hk1).le]
  · nlinarith [mul_nonneg (sub_nonneg.mpr h2) (add_pos h1 hk1).le,
      mul_pos (sub_pos.mpr h) (add_pos hd hk1)]

/-- The two bounds coincide exactly for a two-level spectrum: equality holds in the comparison
with Deng's Theorem 7 iff `λ_k = λ_1` and `λ_d = λ_{k+1}`. -/
theorem thm7_noiseFree_bound_eq_two_div_iff :
    2 * P.gap1 / (P.lam1 ^ 2 - P.lamd ^ 2) = 2 / (P.lam1 + P.lamk1) ↔
      P.lamk = P.lam1 ∧ P.lamd = P.lamk1 := by
  constructor
  · intro h
    by_contra hne
    have h' : P.lamk < P.lam1 ∨ P.lamd < P.lamk1 := by
      by_contra hcon
      apply hne
      exact ⟨le_antisymm P.lamk_le_lam1 (not_lt.mp fun hlt => hcon (Or.inl hlt)),
        le_antisymm P.lamd_le_lamk1 (not_lt.mp fun hlt => hcon (Or.inr hlt))⟩
    exact (P.thm7_noiseFree_bound_lt_two_div h').ne h
  · rintro ⟨h1, h2⟩
    have hk1 := P.lamk1_pos
    have h5 : P.lamk1 < P.lam1 := h1 ▸ P.lamk1_lt_lamk
    have hden : P.lam1 ^ 2 - P.lamk1 ^ 2 ≠ 0 := by nlinarith
    have hsum : P.lam1 + P.lamk1 ≠ 0 := by linarith
    rw [gap1, h1, h2, div_eq_div_iff hden hsum]
    ring

/-- **Spec 1.9 sharpens the noise-free case of Deng's Theorem 7**:
`η*₀ ≥ 2 gap₁ / (λ_1² - λ_d²)` follows from `η*₀ ≥ 2 / (λ_1 + λ_{k+1})`. -/
theorem thm7_noiseFree_bound_le_etaStar (hD : 0 < P.sD c) (hB : 0 < P.sB c) :
    2 * P.gap1 / (P.lam1 ^ 2 - P.lamd ^ 2) ≤ P.etaStar Noise.noiseFree c :=
  le_trans P.thm7_noiseFree_bound_le_two_div (P.two_div_le_etaStar_noiseFree hD hB)

end SGD

end Spec

/-! ### Scaling lemmas (helpers for 4.2) -/

namespace FilterCoordinate

theorem sD_smul (P : Spec ι) (a : ℝ) (c : ι → ℝ) : P.sD (a • c) = a ^ 2 * P.sD c :=
  mom_smul P _ _ a c

theorem sB_smul (P : Spec ι) (a : ℝ) (c : ι → ℝ) : P.sB (a • c) = a ^ 2 * P.sB c :=
  mom_smul P _ _ a c

theorem s_smul (P : Spec ι) (a : ℝ) (c : ι → ℝ) : P.s (a • c) = a ^ 2 * P.s c := by
  unfold Spec.s
  rw [sD_smul, sB_smul]
  ring

/-- `q_t` is homogeneous of degree 4 in the state. -/
theorem qCoef_smul (P : Spec ι) (a : ℝ) (c : ι → ℝ) : P.qCoef (a • c) = a ^ 4 * P.qCoef c := by
  simp only [Spec.qCoef, Spec.sD, Spec.sB, Spec.tauD, Spec.tauB, mom_smul]
  ring

/-- The noise-free `p_t` is homogeneous of degree 4 in the state. -/
theorem pCoef_noiseFree_smul (P : Spec ι) (a : ℝ) (c : ι → ℝ) :
    P.pCoef Noise.noiseFree (a • c) = a ^ 4 * P.pCoef Noise.noiseFree c := by
  simp only [Spec.pCoef, Spec.sD, Spec.sB, Spec.eD, Spec.eB, mom_smul, Noise.noiseFree_kap2,
    mul_zero, Finset.sum_const_zero, add_zero]
  ring

end FilterCoordinate

namespace Spec

variable (P : Spec ι)

open FilterCoordinate

/-! ### Section 4: the vector model (`n = 1`) -/

section Vector

variable {c : ι → ℝ}

/-- **Spec 4.1.** The filtered step of the vector model is Deng's SGD step with the state- and
noise-dependent effective step size `η_eff = η f(‖g‖) / ‖g‖` (also when `‖g‖ = 0`, where both
sides equal `c`). -/
theorem cNextVec_eq_cNext (f : ℝ → ℝ) (η : ℝ) (c ζ : ι → ℝ) :
    P.cNextVec f η c ζ = P.cNext (P.etaEff f η c ζ) c ζ := by
  funext i
  simp only [cNextVec, cNext, etaEff]
  ring

/-- **Spec 4.1, consequence.** The alignment after a filtered step of the vector model is the
alignment after an SGD step with step size `η_eff` (same realised noise): every pathwise statement
of Deng's one-step theory transfers with `η` replaced by `η_eff`. -/
theorem theta_cNextVec (f : ℝ → ℝ) (η : ℝ) (c ζ : ι → ℝ) :
    P.theta (P.cNextVec f η c ζ) = P.theta (P.cNext (P.etaEff f η c ζ) c ζ) := by
  rw [P.cNextVec_eq_cNext]

/-- **Spec 4.1, consequence.** Deng's comparison functional `f_t` at step size `η_eff` is the
comparison functional of the filtered step of the vector model. -/
theorem fCompare_etaEff (f : ℝ → ℝ) (η : ℝ) (c ζ : ι → ℝ) :
    P.fCompare (P.etaEff f η c ζ) c ζ =
      P.sB c * P.sD (P.cNextVec f η c ζ) - P.sB (P.cNextVec f η c ζ) * P.sD c := by
  rw [P.cNextVec_eq_cNext, fCompare]

theorem gradNorm_nonneg (c ζ : ι → ℝ) : 0 ≤ P.gradNorm c ζ := Real.sqrt_nonneg _

/-- Without noise the gradient norm is `‖A x‖ = √(s(c))`. -/
theorem gradNorm_noiseFree (c : ι → ℝ) : P.gradNorm c 0 = Real.sqrt (P.s c) := by
  unfold gradNorm
  rw [P.s_eq_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.zero_apply, add_zero]
  ring

/-- **Spec 4.1 (Muon = normalised SGD).** For `f ≡ 1`: `η_eff = η / ‖g‖`. -/
theorem etaEff_one (η : ℝ) (c ζ : ι → ℝ) :
    P.etaEff (fun _ => (1 : ℝ)) η c ζ = η / P.gradNorm c ζ := by
  simp [etaEff]

/-- **Spec 4.1 (HTMuon).** For `f σ = σ ^ p`: `η_eff = η ‖g‖^{p-1}` (provided `‖g‖ ≠ 0` or
`p ≠ 1`; for `‖g‖ = 0` and `p = 1` Lean's conventions give `η_eff = 0` but `η · 0⁰ = η`). -/
theorem etaEff_rpow (p η : ℝ) {c ζ : ι → ℝ} (h : P.gradNorm c ζ ≠ 0 ∨ p ≠ 1) :
    P.etaEff (fun σ => σ ^ p) η c ζ = η * P.gradNorm c ζ ^ (p - 1) := by
  unfold etaEff
  by_cases hg : P.gradNorm c ζ = 0
  · have hp : p - 1 ≠ 0 := sub_ne_zero.mpr (h.resolve_left (not_not.mpr hg))
    rw [hg, Real.zero_rpow hp]
    simp
  · rw [Real.rpow_sub_one hg]
    ring

/-- **Spec 4.1 (SGD).** For `f = id`: `η_eff = η` (when `‖g‖ ≠ 0`). -/
theorem etaEff_id (η : ℝ) {c ζ : ι → ℝ} (hg : P.gradNorm c ζ ≠ 0) :
    P.etaEff _root_.id η c ζ = η := by
  unfold etaEff
  simp only [id_eq]
  field_simp

/-- **Spec 4.2, general filter, `<`.** Noise-free vector model at a state where both blocks carry
energy: the alignment decreases iff `0 < η_eff < η*₀`. -/
theorem theta_cNextVec_noiseFree_lt_iff (hD : 0 < P.sD c) (hB : 0 < P.sB c) (f : ℝ → ℝ) (η : ℝ) :
    P.theta (P.cNextVec f η c 0) < P.theta c ↔
      0 < P.etaEff f η c 0 ∧ P.etaEff f η c 0 < P.etaStar Noise.noiseFree c := by
  rw [P.cNextVec_eq_cNext]
  exact P.theta_cNext_noiseFree_lt_iff' hD hB _

/-- **Spec 4.2, general filter, `>`.** The alignment increases iff `η_eff < 0` or
`η_eff > η*₀`. -/
theorem theta_cNextVec_noiseFree_gt_iff (hD : 0 < P.sD c) (hB : 0 < P.sB c) (f : ℝ → ℝ) (η : ℝ) :
    P.theta c < P.theta (P.cNextVec f η c 0) ↔
      P.etaEff f η c 0 < 0 ∨ P.etaStar Noise.noiseFree c < P.etaEff f η c 0 := by
  rw [P.cNextVec_eq_cNext]
  exact P.theta_cNext_noiseFree_gt_iff' hD hB _

/-- **Spec 4.2, general filter, `=`.** The alignment is unchanged iff `η_eff = 0` or
`η_eff = η*₀`. -/
theorem theta_cNextVec_noiseFree_eq_iff (hD : 0 < P.sD c) (hB : 0 < P.sB c) (f : ℝ → ℝ) (η : ℝ) :
    P.theta (P.cNextVec f η c 0) = P.theta c ↔
      P.etaEff f η c 0 = 0 ∨ P.etaEff f η c 0 = P.etaStar Noise.noiseFree c := by
  rw [P.cNextVec_eq_cNext]
  exact P.theta_cNext_noiseFree_eq_iff' hD hB _

/-- Noise-free HTMuon in the vector model: `η_eff = η ‖A x‖^{p-1}` with `‖A x‖ = √(s(c))`. -/
theorem etaEff_rpow_noiseFree (p η : ℝ) (hs : 0 < P.s c) :
    P.etaEff (fun σ => σ ^ p) η c 0 = η * Real.sqrt (P.s c) ^ (p - 1) := by
  have hg : P.gradNorm c 0 ≠ 0 := by
    rw [P.gradNorm_noiseFree]
    exact (Real.sqrt_pos.mpr hs).ne'
  rw [P.etaEff_rpow p η (Or.inl hg), P.gradNorm_noiseFree]

/-- **Spec 4.2 (alignment regime selected by the gradient norm), `<`.** Noise-free vector model
with `f σ = σ ^ p`, state with `s^𝒟, s^ℬ > 0`, step size `η > 0`:
`θ(c⁺) < θ(c) ↔ η ‖A x‖^{p-1} < η*₀(c)`, where `‖A x‖ = √(s(c))`. -/
theorem theta_cNextVec_rpow_lt_iff (hD : 0 < P.sD c) (hB : 0 < P.sB c) (p : ℝ) {η : ℝ}
    (hη : 0 < η) :
    P.theta (P.cNextVec (fun σ => σ ^ p) η c 0) < P.theta c ↔
      η * Real.sqrt (P.s c) ^ (p - 1) < P.etaStar Noise.noiseFree c := by
  have hs : 0 < P.s c := by unfold s; linarith
  rw [P.theta_cNextVec_noiseFree_lt_iff hD hB, P.etaEff_rpow_noiseFree p η hs]
  exact and_iff_right (mul_pos hη (Real.rpow_pos_of_pos (Real.sqrt_pos.mpr hs) _))

/-- **Spec 4.2, `>`.** In the setting of `theta_cNextVec_rpow_lt_iff`:
`θ(c) < θ(c⁺) ↔ η*₀(c) < η ‖A x‖^{p-1}`. -/
theorem theta_cNextVec_rpow_gt_iff (hD : 0 < P.sD c) (hB : 0 < P.sB c) (p : ℝ) {η : ℝ}
    (hη : 0 < η) :
    P.theta c < P.theta (P.cNextVec (fun σ => σ ^ p) η c 0) ↔
      P.etaStar Noise.noiseFree c < η * Real.sqrt (P.s c) ^ (p - 1) := by
  have hs : 0 < P.s c := by unfold s; linarith
  rw [P.theta_cNextVec_noiseFree_gt_iff hD hB, P.etaEff_rpow_noiseFree p η hs]
  exact or_iff_right
    (not_lt.mpr (mul_pos hη (Real.rpow_pos_of_pos (Real.sqrt_pos.mpr hs) _)).le)

/-- **Spec 4.2, `=`.** In the setting of `theta_cNextVec_rpow_lt_iff`:
`θ(c⁺) = θ(c) ↔ η ‖A x‖^{p-1} = η*₀(c)`. -/
theorem theta_cNextVec_rpow_eq_iff (hD : 0 < P.sD c) (hB : 0 < P.sB c) (p : ℝ) {η : ℝ}
    (hη : 0 < η) :
    P.theta (P.cNextVec (fun σ => σ ^ p) η c 0) = P.theta c ↔
      η * Real.sqrt (P.s c) ^ (p - 1) = P.etaStar Noise.noiseFree c := by
  have hs : 0 < P.s c := by unfold s; linarith
  rw [P.theta_cNextVec_noiseFree_eq_iff hD hB, P.etaEff_rpow_noiseFree p η hs]
  exact or_iff_right (mul_pos hη (Real.rpow_pos_of_pos (Real.sqrt_pos.mpr hs) _)).ne'

/-- **Spec 4.2 needs `η > 0`.** For a *negative* step size the alignment increases although
`η ‖A x‖^{p-1} < η*₀(c)`: the equivalence of 4.2 is false for `η < 0`. -/
theorem theta_cNextVec_rpow_gt_of_neg (hD : 0 < P.sD c) (hB : 0 < P.sB c) (p : ℝ) {η : ℝ}
    (hη : η < 0) :
    P.theta c < P.theta (P.cNextVec (fun σ => σ ^ p) η c 0) ∧
      η * Real.sqrt (P.s c) ^ (p - 1) < P.etaStar Noise.noiseFree c := by
  have hs : 0 < P.s c := by unfold s; linarith
  have hneg : η * Real.sqrt (P.s c) ^ (p - 1) < 0 :=
    mul_neg_of_neg_of_pos hη (Real.rpow_pos_of_pos (Real.sqrt_pos.mpr hs) _)
  refine ⟨?_, lt_trans hneg (P.etaStar_noiseFree_pos hD hB)⟩
  rw [P.theta_cNextVec_noiseFree_gt_iff hD hB, P.etaEff_rpow_noiseFree p η hs]
  exact Or.inl hneg

/-- **Spec 4.2.** Deng's noise-free critical step size `η*₀` is invariant under the scaling
`c ↦ a c`, `a ≠ 0`. -/
theorem etaStar_noiseFree_smul {a : ℝ} (ha : a ≠ 0) (c : ι → ℝ) :
    P.etaStar Noise.noiseFree (a • c) = P.etaStar Noise.noiseFree c := by
  unfold etaStar
  rw [qCoef_smul, pCoef_noiseFree_smul, ← mul_neg, mul_div_mul_left _ _ (pow_ne_zero 4 ha)]

/-- **Spec 4.2 (ray statement), decrease.** Noise-free vector model with `f σ = σ ^ p`, `p < 1`,
`η > 0`, at a state `c` with `s^𝒟, s^ℬ > 0`: along the ray `{a c : a > 0}` the alignment decreases
iff `a ‖A x‖ > (η / η*₀(c))^{1/(1-p)}` — far from the optimum, whatever `η` is. -/
theorem theta_cNextVec_rpow_ray_lt_iff (hD : 0 < P.sD c) (hB : 0 < P.sB c) {p η a : ℝ}
    (hp : p < 1) (hη : 0 < η) (ha : 0 < a) :
    P.theta (P.cNextVec (fun σ => σ ^ p) η (a • c) 0) < P.theta (a • c) ↔
      (η / P.etaStar Noise.noiseFree c) ^ (1 / (1 - p)) < a * Real.sqrt (P.s c) := by
  have hs : 0 < P.s c := by unfold s; linarith
  have hDa : 0 < P.sD (a • c) := by rw [sD_smul]; positivity
  have hBa : 0 < P.sB (a • c) := by rw [sB_smul]; positivity
  have hsqrt : Real.sqrt (P.s (a • c)) = a * Real.sqrt (P.s c) := by
    rw [s_smul, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]
  rw [P.theta_cNextVec_rpow_lt_iff hDa hBa p hη, hsqrt, P.etaStar_noiseFree_smul ha.ne']
  exact rpow_ray_lt_iff hη (P.etaStar_noiseFree_pos hD hB)
    (mul_pos ha (Real.sqrt_pos.mpr hs)) hp

/-- **Spec 4.2 (ray statement), increase.** In the setting of `theta_cNextVec_rpow_ray_lt_iff`
the alignment increases iff `a ‖A x‖ < (η / η*₀(c))^{1/(1-p)}` — close to the optimum, whatever
`η` is. -/
theorem theta_cNextVec_rpow_ray_gt_iff (hD : 0 < P.sD c) (hB : 0 < P.sB c) {p η a : ℝ}
    (hp : p < 1) (hη : 0 < η) (ha : 0 < a) :
    P.theta (a • c) < P.theta (P.cNextVec (fun σ => σ ^ p) η (a • c) 0) ↔
      a * Real.sqrt (P.s c) < (η / P.etaStar Noise.noiseFree c) ^ (1 / (1 - p)) := by
  have hs : 0 < P.s c := by unfold s; linarith
  have hDa : 0 < P.sD (a • c) := by rw [sD_smul]; positivity
  have hBa : 0 < P.sB (a • c) := by rw [sB_smul]; positivity
  have hsqrt : Real.sqrt (P.s (a • c)) = a * Real.sqrt (P.s c) := by
    rw [s_smul, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]
  rw [P.theta_cNextVec_rpow_gt_iff hDa hBa p hη, hsqrt, P.etaStar_noiseFree_smul ha.ne']
  exact rpow_ray_gt_iff hη (P.etaStar_noiseFree_pos hD hB)
    (mul_pos ha (Real.sqrt_pos.mpr hs)) hp

end Vector

end Spec

/-! ### Non-vacuity: explicit instances on `Fin 2`

The spectrum `λ = (2, 1)` with `𝒟 = {0}`, `ℬ = {1}`, and the Muon filter `f ≡ 1`
(`ν_i = 1 / |c_i|`).

* At `c = (1, 2)` the curvature ordering of 1.7 holds (`ν_1 = 1/2 < 1 = ν_0`), `η*_f = 4/3`, and
  the alignment decreases for every `0 < η < 4/3`.
* At `c = (2, 1)` the *reversed* ordering of 1.8 holds (`ν_0 = 1/2 < 1 = ν_1`), `η*_f = 4/3`, and
  the alignment **increases** for every `0 < η < 4/3` — e.g. from `16/17` to `36/37` at `η = 1/2`.
-/

namespace FilterCoordinate

/-- The two-direction spectrum `λ = (2, 1)` with `𝒟 = {0}` and `ℬ = {1}`. -/
noncomputable def exSpec : Spec (Fin 2) where
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

theorem exSpec_B : exSpec.B = {1} := by
  ext i
  fin_cases i <;> simp [Spec.B, exSpec]

@[simp] theorem exSpec_lam_zero : exSpec.lam 0 = 2 := rfl
@[simp] theorem exSpec_lam_one : exSpec.lam 1 = 1 := rfl

/-- Block energies of `exSpec`: `s^𝒟 = 4 c_0²`, `s^ℬ = c_1²`. -/
theorem exSpec_mom_D (p : ℕ) (c : Fin 2 → ℝ) : exSpec.mom exSpec.D p c = 2 ^ p * c 0 ^ 2 := by
  have hD : exSpec.D = {0} := rfl
  simp [Spec.mom, hD]

theorem exSpec_mom_B (p : ℕ) (c : Fin 2 → ℝ) : exSpec.mom exSpec.B p c = c 1 ^ 2 := by
  simp [Spec.mom, exSpec_B]

theorem exSpec_sD (c : Fin 2 → ℝ) : exSpec.sD c = 4 * c 0 ^ 2 := by
  rw [Spec.sD, exSpec_mom_D]
  norm_num

theorem exSpec_sB (c : Fin 2 → ℝ) : exSpec.sB c = c 1 ^ 2 := by
  rw [Spec.sB, exSpec_mom_B]

/-- Muon `ν`-moments of `exSpec`. -/
theorem exSpec_momF_D (f : ℝ → ℝ) (a : ℕ) (c : Fin 2 → ℝ) :
    exSpec.momF f exSpec.D a c = exSpec.nu f c 0 ^ a * 4 * c 0 ^ 2 := by
  have hD : exSpec.D = {0} := rfl
  simp [Spec.momF, hD]
  norm_num

theorem exSpec_momF_B (f : ℝ → ℝ) (a : ℕ) (c : Fin 2 → ℝ) :
    exSpec.momF f exSpec.B a c = exSpec.nu f c 1 ^ a * c 1 ^ 2 := by
  simp [Spec.momF, exSpec_B]

/-- **Non-vacuity of 1.7 and 1.9.** Muon at `c = (1, 2)` on `exSpec`: the curvature ordering
holds, `η*_f = 4/3 = 2 / (ν_0 + ν_1)` (both bounds of 1.9 are attained). -/
theorem exSpec_muon_ordered :
    0 < exSpec.sD ![1, 2] ∧ 0 < exSpec.sB ![1, 2] ∧
      (∀ j ∈ exSpec.B, (![1, 2] : Fin 2 → ℝ) j ≠ 0 → 0 ≤ exSpec.nu (fun _ => (1 : ℝ)) ![1, 2] j) ∧
      (∀ i ∈ exSpec.D, ∀ j ∈ exSpec.B, (![1, 2] : Fin 2 → ℝ) i ≠ 0 → (![1, 2] : Fin 2 → ℝ) j ≠ 0 →
        exSpec.nu (fun _ => (1 : ℝ)) ![1, 2] j < exSpec.nu (fun _ => (1 : ℝ)) ![1, 2] i) ∧
      exSpec.etaStarF (fun _ => (1 : ℝ)) ![1, 2] = 4 / 3 := by
  have hD : exSpec.D = {0} := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [exSpec_sD]; norm_num
  · rw [exSpec_sB]; norm_num
  · intro j _ _
    rw [Spec.nu_one]; positivity
  · intro i hi j hj _ _
    rw [hD, Finset.mem_singleton] at hi
    rw [exSpec_B, Finset.mem_singleton] at hj
    subst hi; subst hj
    simp only [Spec.nu_one]
    norm_num
  · simp only [Spec.etaStarF, Spec.qF, Spec.pF, exSpec_sD, exSpec_sB, exSpec_momF_D,
      exSpec_momF_B, Spec.nu_one]
    norm_num

/-- **Non-vacuity of 1.7.** Muon at `c = (1, 2)` on `exSpec`: the alignment decreases for every
`0 < η < 4/3`. -/
theorem exSpec_muon_decrease {η : ℝ} (h0 : 0 < η) (h1 : η < 4 / 3) :
    exSpec.theta (exSpec.cNextF (fun _ => (1 : ℝ)) η ![1, 2]) < exSpec.theta ![1, 2] := by
  obtain ⟨hD, hB, hnn, hord, hstar⟩ := exSpec_muon_ordered
  rw [exSpec.theta_cNextF_lt_iff_of_ordered hD hB hnn hord h0, hstar]
  exact h1

/-- **Non-vacuity of 1.8.** Muon at `c = (2, 1)` on `exSpec`: the *reversed* curvature ordering
holds and `η*_f = 4/3`. -/
theorem exSpec_muon_reversed :
    0 < exSpec.sD ![2, 1] ∧ 0 < exSpec.sB ![2, 1] ∧
      (∀ i ∈ exSpec.D, (![2, 1] : Fin 2 → ℝ) i ≠ 0 → 0 ≤ exSpec.nu (fun _ => (1 : ℝ)) ![2, 1] i) ∧
      (∀ i ∈ exSpec.D, ∀ j ∈ exSpec.B, (![2, 1] : Fin 2 → ℝ) i ≠ 0 → (![2, 1] : Fin 2 → ℝ) j ≠ 0 →
        exSpec.nu (fun _ => (1 : ℝ)) ![2, 1] i < exSpec.nu (fun _ => (1 : ℝ)) ![2, 1] j) ∧
      exSpec.etaStarF (fun _ => (1 : ℝ)) ![2, 1] = 4 / 3 := by
  have hD : exSpec.D = {0} := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [exSpec_sD]; norm_num
  · rw [exSpec_sB]; norm_num
  · intro i _ _
    rw [Spec.nu_one]; positivity
  · intro i hi j hj _ _
    rw [hD, Finset.mem_singleton] at hi
    rw [exSpec_B, Finset.mem_singleton] at hj
    subst hi; subst hj
    simp only [Spec.nu_one]
    norm_num
  · simp only [Spec.etaStarF, Spec.qF, Spec.pF, exSpec_sD, exSpec_sB, exSpec_momF_D,
      exSpec_momF_B, Spec.nu_one]
    norm_num

/-- **Non-vacuity of 1.8: an explicit Muon state where the alignment increases for small `η`.**
Muon at `c = (2, 1)` on `exSpec` (`λ = (2, 1)`): the alignment **increases** for every
`0 < η < 4/3`. -/
theorem exSpec_muon_increase {η : ℝ} (h0 : 0 < η) (h1 : η < 4 / 3) :
    exSpec.theta ![2, 1] < exSpec.theta (exSpec.cNextF (fun _ => (1 : ℝ)) η ![2, 1]) := by
  obtain ⟨hD, hB, hnn, hrev, hstar⟩ := exSpec_muon_reversed
  rw [exSpec.theta_cNextF_gt_iff_of_reversed hD hB hnn hrev h0, hstar]
  exact h1

/-- Direct evaluation (independent of the general theorems): on `exSpec` the alignment of
`c = (2, 1)` is `16/17`, and after one Muon step with `η = 1/2` it is `36/37 > 16/17`. -/
theorem exSpec_muon_increase_explicit :
    exSpec.theta ![2, 1] = 16 / 17 ∧
      exSpec.theta (exSpec.cNextF (fun _ => (1 : ℝ)) (1 / 2) ![2, 1]) = 36 / 37 := by
  have h4 : Real.sign 4 = 1 := Real.sign_of_pos (by norm_num)
  constructor
  · simp only [Spec.theta, Spec.s, exSpec_sD, exSpec_sB]
    norm_num
  · simp only [Spec.theta, Spec.s, exSpec_sD, exSpec_sB, Spec.cNextF, Spec.oddExt_one,
      exSpec_lam_zero, exSpec_lam_one]
    norm_num [h4]

/-- **The sign condition `ν ≥ 0` of 1.7 cannot be dropped.** On `exSpec` at `c = (1, 1)` with the
filter `f σ = (11 σ - 21) / 10` one has `ν_0 = 1/10 > ν_1 = -1` (the curvature ordering holds) but
`p^f = -99/25 < 0`. -/
theorem exSpec_ordered_without_sign :
    (∀ i ∈ exSpec.D, ∀ j ∈ exSpec.B, (![1, 1] : Fin 2 → ℝ) i ≠ 0 → (![1, 1] : Fin 2 → ℝ) j ≠ 0 →
        exSpec.nu (fun σ => (11 * σ - 21) / 10) ![1, 1] j <
          exSpec.nu (fun σ => (11 * σ - 21) / 10) ![1, 1] i) ∧
      exSpec.pF (fun σ => (11 * σ - 21) / 10) ![1, 1] = -99 / 25 := by
  have hD : exSpec.D = {0} := rfl
  constructor
  · intro i hi j hj _ _
    rw [hD, Finset.mem_singleton] at hi
    rw [exSpec_B, Finset.mem_singleton] at hj
    subst hi; subst hj
    simp only [Spec.nu, exSpec_lam_zero, exSpec_lam_one]
    norm_num
  · simp only [Spec.pF, exSpec_sD, exSpec_sB, exSpec_momF_D, exSpec_momF_B, Spec.nu,
      exSpec_lam_zero, exSpec_lam_one]
    norm_num

/-- **The sign condition `ν ≥ 0` of 1.8 cannot be dropped either.** On `exSpec` at `c = (1, 1)`
with the filter `f σ = (12 - 11 σ) / 10` one has `ν_0 = -1 < ν_1 = 1/10` (the reversed curvature
ordering holds) but `p^f = 99/25 > 0`. -/
theorem exSpec_reversed_without_sign :
    (∀ i ∈ exSpec.D, ∀ j ∈ exSpec.B, (![1, 1] : Fin 2 → ℝ) i ≠ 0 → (![1, 1] : Fin 2 → ℝ) j ≠ 0 →
        exSpec.nu (fun σ => (12 - 11 * σ) / 10) ![1, 1] i <
          exSpec.nu (fun σ => (12 - 11 * σ) / 10) ![1, 1] j) ∧
      exSpec.pF (fun σ => (12 - 11 * σ) / 10) ![1, 1] = 99 / 25 := by
  have hD : exSpec.D = {0} := rfl
  constructor
  · intro i hi j hj _ _
    rw [hD, Finset.mem_singleton] at hi
    rw [exSpec_B, Finset.mem_singleton] at hj
    subst hi; subst hj
    simp only [Spec.nu, exSpec_lam_zero, exSpec_lam_one]
    norm_num
  · simp only [Spec.pF, exSpec_sD, exSpec_sB, exSpec_momF_D, exSpec_momF_B, Spec.nu,
      exSpec_lam_zero, exSpec_lam_one]
    norm_num

/-- **The proviso `s(c') > 0` of 1.5 cannot be dropped in general** (it is automatic under the
hypotheses of 1.7 and 1.8).  Muon on `exSpec` at the isotropic state `c = (1, 1)` with `η = 1`:
the step lands on `c⁺ = 0`, so `θ(c⁺) = 0 < 4/5 = θ(c)` although `p^f η² + q^f η = 0`. -/
theorem exSpec_muon_annihilate :
    exSpec.cNextF (fun _ => (1 : ℝ)) 1 ![1, 1] = 0 ∧
      exSpec.theta (exSpec.cNextF (fun _ => (1 : ℝ)) 1 ![1, 1]) < exSpec.theta ![1, 1] ∧
      exSpec.pF (fun _ => (1 : ℝ)) ![1, 1] * 1 ^ 2 +
        exSpec.qF (fun _ => (1 : ℝ)) ![1, 1] * 1 = 0 := by
  have h0 : exSpec.cNextF (fun _ => (1 : ℝ)) 1 ![1, 1] = 0 := by
    funext i
    fin_cases i <;> simp [Spec.cNextF_one]
  refine ⟨h0, ?_, ?_⟩
  · rw [h0, Spec.theta_zero]
    simp only [Spec.theta, Spec.s, exSpec_sD, exSpec_sB]
    norm_num
  · rw [← Spec.fCompareF_eq, Spec.fCompareF, h0]
    simp [exSpec_sD, exSpec_sB]

/-- Noise-free Deng on `exSpec` at `c = (1, 2)`: `η*₀ = 2/3 = 2 / (λ_0 + λ_1)` (both bounds of the
SGD corollary of 1.9 are attained). -/
theorem exSpec_etaStar_noiseFree : exSpec.etaStar Noise.noiseFree ![1, 2] = 2 / 3 := by
  simp only [Spec.etaStar_noiseFree_eq, Spec.sD, Spec.sB, Spec.tauD, Spec.tauB, exSpec_mom_D,
    exSpec_mom_B]
  norm_num

/-- **Non-vacuity of 4.2.** Normalised SGD (Muon in the vector model, `f σ = σ⁰ = 1`) on `exSpec`
along the ray through `c = (1, 2)`, where `‖A x‖ = √8` and `η*₀ = 2/3`: for every `η > 0` the
alignment decreases iff `a √8 > 3 η / 2`. -/
theorem exSpec_vector_ray {η a : ℝ} (hη : 0 < η) (ha : 0 < a) :
    exSpec.theta (exSpec.cNextVec (fun σ => σ ^ (0 : ℝ)) η (a • ![1, 2]) 0) <
        exSpec.theta (a • ![1, 2]) ↔ 3 * η / 2 < a * Real.sqrt 8 := by
  obtain ⟨hD, hB, -⟩ := exSpec_muon_ordered
  have hs : exSpec.s ![1, 2] = 8 := by
    simp only [Spec.s, exSpec_sD, exSpec_sB]
    norm_num
  have hpow : (η / (2 / 3)) ^ (1 / (1 - (0 : ℝ))) = 3 * η / 2 := by
    rw [sub_zero, div_one, Real.rpow_one]
    ring
  rw [exSpec.theta_cNextVec_rpow_ray_lt_iff hD hB (by norm_num) hη ha, exSpec_etaStar_noiseFree,
    hs, hpow]

end FilterCoordinate

end SuspiciousAlignment
