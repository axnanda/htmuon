import Mathlib
import SuspiciousAlignment.Defs

/-!
# Variance of Gaussian forms

Formalization of **Lemma "Variance of Gaussian Forms"** (`lem:gauss-var`, Appendix A.3
"Probabilistic Lemmas", tex l. 948–959) of

> Deng, Liao, Ouyang, Pang, Song, Yang, *Suspicious Alignment of SGD: A Fine-Grained Step Size
> Condition Analysis* (arXiv:2601.11789v2),

and of the way it is used in the proof of Lemma "Asymptotic ratio of expectations"
(tex l. 1010–1022): the next-step block energy `s_{t+1}^S` is `χ + gᵀz + zᵀDz` in the Gaussian
noise `z`, and its variance is controlled by the lemma.

> **Lemma.** Let `z ∼ 𝒩(0, C)` with `C = Cᵀ ⪰ 0`.  For any deterministic vector `g` and any
> deterministic diagonal matrix `D`:
> `Var(gᵀz) = gᵀ C g ≤ ‖C‖₂ ‖g‖₂²` and `Var(zᵀDz) = 2 tr((C D)²) ≤ 2 ‖C‖₂² tr(D²)`.

## The formal model of `z ∼ 𝒩(0, C)`

`IsCenteredGaussian z C μ` says that the random vector `z : Ω → (ι → ℝ)` has, under `μ`, the law
`ProbabilityTheory.multivariateGaussian 0 C` of Mathlib (read through `WithLp.toLp 2`, because
Mathlib's multivariate Gaussian lives on `EuclideanSpace ℝ ι`).  Two facts make this the right
notion:

* `isCenteredGaussian_of_iIndepFun`: if `w_k` (`k : κ`) are independent standard normal real
  random variables and `M : Matrix ι κ ℝ` is deterministic, then `z = M w` is
  `IsCenteredGaussian` with covariance `M Mᵀ` (the "textbook" construction; every PSD `C` is of
  this form with `M = C^{1/2}`, `GaussianForms.sqrt_mul_sqrt_transpose`);
* `IsCenteredGaussian.covariance_apply`: `Cov(z_i, z_j) = C_ij`.

Non-vacuity: `isCenteredGaussian_ofLp` realises `𝒩(0, C)` for every `C`.

## Main results (all for `z ∼ 𝒩(0, C)`, `C` positive semidefinite, `D` symmetric)

* `IsCenteredGaussian.integral_linear`, `IsCenteredGaussian.variance_linear`,
  `IsCenteredGaussian.variance_linear_le`: `𝔼 gᵀz = 0`, `Var(gᵀz) = gᵀCg ≤ ‖C‖₂ ‖g‖₂²`;
* `IsCenteredGaussian.integral_quadratic`, `IsCenteredGaussian.variance_quadratic`,
  `IsCenteredGaussian.variance_quadratic_le`:
  `𝔼 zᵀDz = tr(C D)`, `Var(zᵀDz) = 2 tr((C D)²) ≤ 2 ‖C‖₂² tr(D²)`;
* `IsCenteredGaussian.covariance_linear_quadratic`: `Cov(gᵀz, zᵀDz) = 0`;
* `IsCenteredGaussian.variance_form`: `Var(χ + gᵀz + zᵀDz) = gᵀCg + 2 tr((C D)²)`;
* `variance_gaussian_forms`: the lemma exactly as in the paper (diagonal `D`);
* `Spec.mom_cNext_eq_gaussian_form`, `Spec.integral_sNext_of_isCenteredGaussian`,
  `Spec.variance_sNext_of_isCenteredGaussian`, `Spec.variance_sNext_le_of_isCenteredGaussian`:
  the decomposition of `s_{t+1}^S`, its mean (`= Spec.EsNext`), variance and variance bound.

The pure linear-algebra inequalities are `GaussianForms.dotProduct_mulVec_le` and
`GaussianForms.trace_mul_sq_le_of_isSymm`; they hold for *every* real matrix `C` (no positivity
needed) and every symmetric `D`.  Symmetry of `D` cannot be dropped
(`GaussianForms.not_trace_mul_sq_le_of_not_isSymm`).

## Proof strategy

Everything is reduced to a standard normal vector `w` (law `Measure.pi (fun _ ↦ gaussianReal 0 1)`):
`z = C^{1/2} w`, so `χ + gᵀz + zᵀDz = χ + aᵀw + wᵀQw` with `Q = C^{1/2} D C^{1/2}` symmetric.
Diagonalising `Q = U diag(λ) Uᵀ` and using the rotation invariance of the standard normal law
(`stdNormalPi_map_orthonormalBasis`, from Mathlib's `stdGaussian_eq_map_pi_orthonormalBasis`),
the form becomes a sum `χ + ∑ᵢ (αᵢ yᵢ + λᵢ yᵢ²)` of *independent* terms, whose variance is
`∑ᵢ (αᵢ² + 2λᵢ²)` by the moments `𝔼y = 𝔼y³ = 0`, `𝔼y² = 1`, `𝔼y⁴ = 3` of `𝒩(0,1)`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator ENNReal NNReal

namespace SuspiciousAlignment
namespace GaussianForms

variable {ι κ ι' : Type*} [Fintype ι] [Fintype κ] [Fintype ι']
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ι']

/-! ### Linear algebra -/

omit [DecidableEq ι] in
/-- `‖C v‖₂² ≤ ‖C‖₂² ‖v‖₂²` for the spectral (l2-operator) norm. -/
theorem mulVec_dotProduct_mulVec_le (C : Matrix ι κ ℝ) (v : κ → ℝ) :
    (C *ᵥ v) ⬝ᵥ (C *ᵥ v) ≤ ‖C‖ ^ 2 * (v ⬝ᵥ v) := by
  have h := C.l2_opNorm_mulVec (toLp 2 v)
  have h1 : ‖(EuclideanSpace.equiv ι ℝ).symm (C *ᵥ v)‖ ^ 2 = (C *ᵥ v) ⬝ᵥ (C *ᵥ v) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [dotProduct, sq]
  have h2 : ‖toLp 2 v‖ ^ 2 = v ⬝ᵥ v := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [dotProduct, sq]
  rw [← h1, ← h2, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

omit [DecidableEq κ] in
/-- `vᵀv ≥ 0`. -/
theorem dotProduct_self_nonneg' (v : κ → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

/-- `gᵀ C g ≤ ‖C‖₂ ‖g‖₂²`. -/
theorem dotProduct_mulVec_le (C : Matrix ι ι ℝ) (g : ι → ℝ) :
    g ⬝ᵥ C *ᵥ g ≤ ‖C‖ * (g ⬝ᵥ g) := by
  have hcs : (g ⬝ᵥ C *ᵥ g) ^ 2 ≤ (g ⬝ᵥ g) * ((C *ᵥ g) ⬝ᵥ (C *ᵥ g)) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ g (C *ᵥ g)
    simpa [dotProduct, sq] using this
  have h2 := mulVec_dotProduct_mulVec_le C g
  have hgg : 0 ≤ g ⬝ᵥ g := dotProduct_self_nonneg' g
  have hC : 0 ≤ ‖C‖ := norm_nonneg C
  have h3 : (g ⬝ᵥ C *ᵥ g) ^ 2 ≤ (‖C‖ * (g ⬝ᵥ g)) ^ 2 := by
    calc (g ⬝ᵥ C *ᵥ g) ^ 2 ≤ (g ⬝ᵥ g) * ((C *ᵥ g) ⬝ᵥ (C *ᵥ g)) := hcs
      _ ≤ (g ⬝ᵥ g) * (‖C‖ ^ 2 * (g ⬝ᵥ g)) := mul_le_mul_of_nonneg_left h2 hgg
      _ = (‖C‖ * (g ⬝ᵥ g)) ^ 2 := by ring
  exact le_trans (le_abs_self _) (abs_le_of_sq_le_sq h3 (mul_nonneg hC hgg))

omit [DecidableEq ι] in
/-- `tr(X²) ≤ tr(Xᵀ X) = ‖X‖_F²` for every real square matrix. -/
theorem trace_mul_self_le (X : Matrix ι ι ℝ) : (X * X).trace ≤ (Xᵀ * X).trace := by
  simp only [trace, diag, mul_apply, transpose_apply]
  have h : ∀ i j, X i j * X j i ≤ (X i j ^ 2 + X j i ^ 2) / 2 := fun i j => by
    nlinarith [sq_nonneg (X i j - X j i)]
  calc ∑ i, ∑ j, X i j * X j i ≤ ∑ i, ∑ j, (X i j ^ 2 + X j i ^ 2) / 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = (∑ i, ∑ j, X i j ^ 2) / 2 + (∑ i, ∑ j, X j i ^ 2) / 2 := by
        simp only [add_div, Finset.sum_add_distrib, Finset.sum_div]
    _ = ∑ i, ∑ j, X j i * X j i := by
        rw [Finset.sum_comm (f := fun i j => X i j ^ 2)]
        simp only [sq]
        ring

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq ι'] in
/-- `tr(Xᵀ X) = ∑_j ‖X e_j‖²` (sum of squared column norms). -/
theorem trace_transpose_mul_self_eq_sum (X : Matrix ι κ ℝ) :
    (Xᵀ * X).trace = ∑ j, (fun i => X i j) ⬝ᵥ (fun i => X i j) := by
  simp [trace, mul_apply, dotProduct]

/-- `‖C D‖_F² ≤ ‖C‖₂² ‖D‖_F²`. -/
theorem trace_transpose_mul_mul_le (C : Matrix ι κ ℝ) (D : Matrix κ ι' ℝ) :
    ((C * D)ᵀ * (C * D)).trace ≤ ‖C‖ ^ 2 * (Dᵀ * D).trace := by
  rw [trace_transpose_mul_self_eq_sum, trace_transpose_mul_self_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have := mulVec_dotProduct_mulVec_le C (fun k => D k j)
  have e : (fun i => (C * D) i j) = C *ᵥ (fun k => D k j) := by
    ext i; simp [mul_apply, mulVec, dotProduct]
  rw [e]; exact this

/-- `tr((C D)²) ≤ ‖C‖₂² ‖D‖_F²` for *arbitrary* real square matrices `C`, `D`. -/
theorem trace_mul_mul_self_le (C D : Matrix ι ι ℝ) :
    ((C * D) * (C * D)).trace ≤ ‖C‖ ^ 2 * (Dᵀ * D).trace :=
  (trace_mul_self_le _).trans (trace_transpose_mul_mul_le C D)

/-- `tr((C D)²) ≤ ‖C‖₂² tr(D²)` for symmetric `D` (no assumption on `C`). -/
theorem trace_mul_mul_self_le_of_isSymm (C : Matrix ι ι ℝ) {D : Matrix ι ι ℝ} (hD : D.IsSymm) :
    ((C * D) * (C * D)).trace ≤ ‖C‖ ^ 2 * (D * D).trace := by
  have := trace_mul_mul_self_le C D
  rwa [hD.eq] at this

/-- `gᵀ C g ≤ ‖C‖₂ ∑ᵢ gᵢ²`. -/
theorem dotProduct_mulVec_le_sum_sq (C : Matrix ι ι ℝ) (g : ι → ℝ) :
    g ⬝ᵥ C *ᵥ g ≤ ‖C‖ * ∑ i, g i ^ 2 := by
  have h := dotProduct_mulVec_le C g
  have e : g ⬝ᵥ g = ∑ i, g i ^ 2 := Finset.sum_congr rfl fun i _ => (sq (g i)).symm
  rwa [e] at h

/-- `tr((C D)²) ≤ ‖C‖₂² tr(D²)` for symmetric `D` (and arbitrary `C`): the linear-algebra
inequality of Lemma "Variance of Gaussian Forms". -/
theorem trace_mul_sq_le_of_isSymm (C : Matrix ι ι ℝ) {D : Matrix ι ι ℝ} (hD : D.IsSymm) :
    ((C * D) ^ 2).trace ≤ ‖C‖ ^ 2 * (D ^ 2).trace := by
  have h := trace_mul_mul_self_le_of_isSymm C hD
  rwa [← pow_two, ← pow_two] at h

/-- The symmetry of `D` cannot be dropped in `tr((C D)²) ≤ ‖C‖₂² tr(D²)`, even for positive
semidefinite `C`: take `C = diag(1, 0)` and `D` the rotation by a quarter turn. -/
theorem not_trace_mul_sq_le_of_not_isSymm :
    ∃ C D : Matrix (Fin 2) (Fin 2) ℝ, C.PosSemidef ∧
      ¬ (((C * D) ^ 2).trace ≤ ‖C‖ ^ 2 * (D ^ 2).trace) := by
  refine ⟨diagonal ![1, 0], !![0, 1; -1, 0],
    PosSemidef.diagonal (fun i => by fin_cases i <;> simp), ?_⟩
  have hC : (diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 := by
    intro h
    have := congrFun (congrFun h 0) 0
    simp at this
  have hpos : 0 < ‖(diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℝ)‖ := norm_pos_iff.mpr hC
  have h1 : (((diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℝ) * !![0, 1; -1, 0]) ^ 2).trace
      = 0 := by
    simp [pow_two, Matrix.mul_apply, trace, Fin.sum_univ_two]
  have h2 : ((!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ) ^ 2).trace = -2 := by
    simp [pow_two, trace, Fin.sum_univ_two]
    norm_num
  rw [h1, h2]
  nlinarith [pow_pos hpos 2]

/-- `tr(C diag(d)) = ∑ᵢ C_ii dᵢ`. -/
theorem trace_mul_diagonal (C : Matrix ι ι ℝ) (d : ι → ℝ) :
    (C * diagonal d).trace = ∑ i, C i i * d i := by
  simp [trace]

/-- `tr(diag(d)²) = ∑ᵢ dᵢ²`. -/
theorem trace_diagonal_sq (d : ι → ℝ) : ((diagonal d) ^ 2).trace = ∑ i, d i ^ 2 := by
  rw [pow_two, diagonal_mul_diagonal, trace_diagonal]
  exact Finset.sum_congr rfl fun i _ => (sq (d i)).symm

/-- `zᵀ diag(d) z = ∑ᵢ dᵢ zᵢ²`. -/
theorem dotProduct_diagonal_mulVec (d z : ι → ℝ) :
    z ⬝ᵥ diagonal d *ᵥ z = ∑ i, d i * z i ^ 2 := by
  simp only [dotProduct, mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `M Mᵀ` is positive semidefinite. -/
theorem posSemidef_mul_transpose (M : Matrix ι κ ℝ) : (M * Mᵀ).PosSemidef := by
  simpa using Matrix.posSemidef_self_mul_conjTranspose M

/-- The spectral norm is dominated by the Frobenius norm: `‖A‖₂² ≤ tr(AᵀA)`. -/
theorem l2_opNorm_sq_le_trace (A : Matrix ι κ ℝ) : ‖A‖ ^ 2 ≤ (Aᵀ * A).trace := by
  have htr : 0 ≤ (Aᵀ * A).trace := by
    rw [trace_transpose_mul_self_eq_sum]
    exact Finset.sum_nonneg fun j _ => dotProduct_self_nonneg' _
  have hb : ‖A‖ ≤ Real.sqrt ((Aᵀ * A).trace) := by
    rw [l2_opNorm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    change ‖(EuclideanSpace.equiv ι ℝ).symm (A *ᵥ x)‖ ≤ _
    refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
    rw [mul_pow, Real.sq_sqrt htr, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      trace_transpose_mul_self_eq_sum]
    have h1 : ∀ i, (A *ᵥ ⇑x) i ^ 2 ≤ (∑ j, A i j ^ 2) * ∑ j, x j ^ 2 := fun i =>
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i) x
    calc ∑ i, ((EuclideanSpace.equiv ι ℝ).symm (A *ᵥ ⇑x)) i ^ 2
        = ∑ i, (A *ᵥ ⇑x) i ^ 2 := rfl
      _ ≤ ∑ i, (∑ j, A i j ^ 2) * ∑ j, x j ^ 2 := Finset.sum_le_sum fun i _ => h1 i
      _ = (∑ j, (fun i => A i j) ⬝ᵥ fun i => A i j) * ∑ j, x j ^ 2 := by
          rw [← Finset.sum_mul, Finset.sum_comm]
          simp [dotProduct, sq]
  calc ‖A‖ ^ 2 ≤ Real.sqrt ((Aᵀ * A).trace) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = (Aᵀ * A).trace := Real.sq_sqrt htr

/-- `gᵀ C g = ∑ᵢⱼ gᵢ C_ij gⱼ`. -/
theorem dotProduct_mulVec_eq_sum (C : Matrix ι ι ℝ) (g : ι → ℝ) :
    g ⬝ᵥ C *ᵥ g = ∑ i, ∑ j, g i * C i j * g j := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- For symmetric `C` and diagonal `D = diag(d)`: `tr((C D)²) = ∑ᵢⱼ dᵢ dⱼ C_ij²`. -/
theorem trace_mul_diagonal_sq {C : Matrix ι ι ℝ} (hC : C.IsSymm) (d : ι → ℝ) :
    ((C * diagonal d) ^ 2).trace = ∑ i, ∑ j, d i * d j * C i j ^ 2 := by
  rw [pow_two, trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_diagonal, mul_diagonal, hC.apply i j]
  ring

/-! ### Moments of the standard normal -/

/-- `d/dt [p(t) e^{t²/2}] = (p'(t) + t p(t)) e^{t²/2}`. -/
theorem hasDerivAt_mul_exp_sq {p : ℝ → ℝ} {p' t : ℝ} (hp : HasDerivAt p p' t) :
    HasDerivAt (fun t => p t * Real.exp (t ^ 2 / 2))
      ((p' + t * p t) * Real.exp (t ^ 2 / 2)) t := by
  have h1 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t := by
    have := (hasDerivAt_pow 2 t).div_const 2
    simpa using this
  have h2 := hp.mul h1.exp
  convert h2 using 1
  ring

/-- The functions `t ↦ p_k(t) e^{t²/2}`, `k = 0,…,4`, the successive derivatives of the moment
generating function `e^{t²/2}` of the standard normal law. -/
noncomputable def mgfDeriv : ℕ → ℝ → ℝ
  | 0 => fun t => 1 * Real.exp (t ^ 2 / 2)
  | 1 => fun t => t * Real.exp (t ^ 2 / 2)
  | 2 => fun t => (1 + t ^ 2) * Real.exp (t ^ 2 / 2)
  | 3 => fun t => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2)
  | 4 => fun t => (3 + 6 * t ^ 2 + t ^ 4) * Real.exp (t ^ 2 / 2)
  | _ => fun _ => 0

/-- `mgfDeriv (k+1)` is the derivative of `mgfDeriv k` (for `k < 4`). -/
theorem deriv_mgfDeriv (k : ℕ) (hk : k < 4) : deriv (mgfDeriv k) = mgfDeriv (k + 1) := by
  funext t
  interval_cases k
  · have hp : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 t := hasDerivAt_const t 1
    have := (hasDerivAt_mul_exp_sq hp).deriv
    simp only [mgfDeriv]
    rw [this]; ring
  · have hp : HasDerivAt (fun t : ℝ => t) 1 t := hasDerivAt_id t
    have := (hasDerivAt_mul_exp_sq hp).deriv
    simp only [mgfDeriv]
    rw [this]; ring
  · have hp : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
      have := (hasDerivAt_pow 2 t).const_add 1
      simpa using this
    have := (hasDerivAt_mul_exp_sq hp).deriv
    simp only [mgfDeriv]
    rw [this]; ring
  · have hp : HasDerivAt (fun t : ℝ => 3 * t + t ^ 3) (3 + 3 * t ^ 2) t := by
      have h0 : HasDerivAt (fun t : ℝ => 3 * t + t ^ 3)
          (3 * 1 + ((3 : ℕ) : ℝ) * t ^ (3 - 1)) t :=
        ((hasDerivAt_id' t).const_mul 3).add (hasDerivAt_pow 3 t)
      convert h0 using 1
      norm_num
    have := (hasDerivAt_mul_exp_sq hp).deriv
    simp only [mgfDeriv]
    rw [this]; ring

/-- `mgfDeriv n` is the `n`-th derivative of `t ↦ e^{t²/2}` (for `n ≤ 4`). -/
theorem iteratedDeriv_mgfDeriv (n : ℕ) (hn : n ≤ 4) :
    iteratedDeriv n (mgfDeriv 0) = mgfDeriv n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih (by omega), deriv_mgfDeriv n (by omega)]

/-- `𝔼[xⁿ]` for the standard normal, `n ≤ 4`, read off the moment generating function. -/
theorem integral_pow_stdNormal (n : ℕ) (hn : n ≤ 4) :
    ∫ x, x ^ n ∂(gaussianReal 0 1) = mgfDeriv n 0 := by
  have h := iteratedDeriv_mgf_zero (X := fun x : ℝ => x) (μ := gaussianReal 0 1) (by simp) n
  rw [mgf_fun_id_gaussianReal] at h
  have e : (fun t : ℝ => Real.exp (0 * t + ((1 : ℝ≥0) : ℝ) * t ^ 2 / 2)) = mgfDeriv 0 := by
    funext t; simp [mgfDeriv]
  rw [e, iteratedDeriv_mgfDeriv n hn] at h
  rw [h]
  rfl

/-- All moments of the standard normal law are finite. -/
theorem integrable_pow_stdNormal (n : ℕ) : Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 1) :=
  integrable_pow_of_mem_interior_integrableExpSet (X := fun x : ℝ => x) (by simp) n

/-- `𝔼x = 0` for `x ∼ 𝒩(0,1)`. -/
theorem integral_id_stdNormal : ∫ x, x ∂(gaussianReal 0 1) = 0 := by simp

/-- `𝔼x² = 1` for `x ∼ 𝒩(0,1)`. -/
theorem integral_sq_stdNormal : ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  rw [integral_pow_stdNormal 2 (by norm_num)]; simp [mgfDeriv]

/-- `𝔼x³ = 0` for `x ∼ 𝒩(0,1)`. -/
theorem integral_cube_stdNormal : ∫ x, x ^ 3 ∂(gaussianReal 0 1) = 0 := by
  rw [integral_pow_stdNormal 3 (by norm_num)]; simp [mgfDeriv]

/-- `𝔼x⁴ = 3` for `x ∼ 𝒩(0,1)`. -/
theorem integral_pow_four_stdNormal : ∫ x, x ^ 4 ∂(gaussianReal 0 1) = 3 := by
  rw [integral_pow_stdNormal 4 (by norm_num)]; simp [mgfDeriv]

/-- `x ↦ α x + β x²` is square integrable under the standard normal law. -/
theorem memLp_linear_add_sq_stdNormal (α β : ℝ) :
    MemLp (fun x : ℝ => α * x + β * x ^ 2) 2 (gaussianReal 0 1) := by
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  have e : (fun x : ℝ => (α * x + β * x ^ 2) ^ 2)
      = fun x => α ^ 2 * x ^ 2 + 2 * α * β * x ^ 3 + β ^ 2 * x ^ 4 := by
    funext x; ring
  rw [e]
  exact (((integrable_pow_stdNormal 2).const_mul _).add
    ((integrable_pow_stdNormal 3).const_mul _)).add ((integrable_pow_stdNormal 4).const_mul _)

/-- `𝔼[α x + β x²] = β` for `x ∼ 𝒩(0,1)`. -/
theorem integral_linear_add_sq_stdNormal (α β : ℝ) :
    ∫ x, (α * x + β * x ^ 2) ∂(gaussianReal 0 1) = β := by
  have h1 : Integrable (fun x : ℝ => α * x) (gaussianReal 0 1) := by
    simpa using (integrable_pow_stdNormal 1).const_mul α
  have h2 : Integrable (fun x : ℝ => β * x ^ 2) (gaussianReal 0 1) :=
    (integrable_pow_stdNormal 2).const_mul β
  rw [integral_add h1 h2, integral_const_mul, integral_const_mul, integral_id_stdNormal,
    integral_sq_stdNormal]
  ring

/-- `Var(α x + β x²) = α² + 2β²` for `x ∼ 𝒩(0,1)` (uses `𝔼x³ = 0`, `𝔼x⁴ = 3`). -/
theorem variance_linear_add_sq_stdNormal (α β : ℝ) :
    Var[fun x : ℝ => α * x + β * x ^ 2; gaussianReal 0 1] = α ^ 2 + 2 * β ^ 2 := by
  rw [variance_eq_sub (memLp_linear_add_sq_stdNormal α β), integral_linear_add_sq_stdNormal]
  have e : ∀ x : ℝ, ((fun x : ℝ => α * x + β * x ^ 2) ^ 2) x
      = α ^ 2 * x ^ 2 + 2 * α * β * x ^ 3 + β ^ 2 * x ^ 4 := by
    intro x; simp only [Pi.pow_apply]; ring
  have i2 := (integrable_pow_stdNormal 2).const_mul (α ^ 2)
  have i3 := (integrable_pow_stdNormal 3).const_mul (2 * α * β)
  have i4 := (integrable_pow_stdNormal 4).const_mul (β ^ 2)
  have i23 : Integrable (fun x : ℝ => α ^ 2 * x ^ 2 + 2 * α * β * x ^ 3) (gaussianReal 0 1) :=
    i2.add i3
  simp_rw [e]
  rw [integral_add i23 i4, integral_add i2 i3, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_sq_stdNormal, integral_cube_stdNormal,
    integral_pow_four_stdNormal]
  ring

/-! ### Forms in a standard normal vector -/

/-- The law on `κ → ℝ` of a vector of independent standard normal variables. -/
noncomputable abbrev stdNormalPi (κ : Type*) [Fintype κ] : Measure (κ → ℝ) :=
  Measure.pi (fun _ : κ => gaussianReal 0 1)

omit [DecidableEq κ] in
/-- Mean, variance and square integrability of a *diagonal* form
`c₀ + ∑ᵢ (αᵢ yᵢ + λᵢ yᵢ²)` in independent standard normals. -/
theorem diag_form_stdNormalPi (c₀ : ℝ) (α lam : κ → ℝ) :
    MemLp (fun y : κ → ℝ => c₀ + ∑ i, (α i * y i + lam i * y i ^ 2)) 2 (stdNormalPi κ) ∧
    ∫ y, (c₀ + ∑ i, (α i * y i + lam i * y i ^ 2)) ∂(stdNormalPi κ) = c₀ + ∑ i, lam i ∧
    Var[fun y : κ → ℝ => c₀ + ∑ i, (α i * y i + lam i * y i ^ 2); stdNormalPi κ]
      = ∑ i, (α i ^ 2 + 2 * lam i ^ 2) := by
  have hmem : ∀ i, MemLp (fun y : κ → ℝ => α i * y i + lam i * y i ^ 2) 2 (stdNormalPi κ) :=
    fun i => (memLp_linear_add_sq_stdNormal (α i) (lam i)).comp_measurePreserving
      (measurePreserving_eval _ i)
  have hsum : MemLp (fun y : κ → ℝ => ∑ i, (α i * y i + lam i * y i ^ 2)) 2 (stdNormalPi κ) :=
    memLp_finsetSum _ fun i _ => hmem i
  refine ⟨(memLp_const c₀).add hsum, ?_, ?_⟩
  · rw [integral_add (integrable_const _) (hsum.integrable one_le_two),
      integral_finsetSum _ fun i _ => (hmem i).integrable one_le_two]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_comp_eval (μ := fun _ : κ => gaussianReal 0 1) (i := i)
      (f := fun x : ℝ => α i * x + lam i * x ^ 2) (by fun_prop)]
    exact integral_linear_add_sq_stdNormal _ _
  · rw [variance_const_add hsum.aestronglyMeasurable]
    have e : (fun y : κ → ℝ => ∑ i, (α i * y i + lam i * y i ^ 2))
        = ∑ i, fun y : κ → ℝ => (fun x : ℝ => α i * x + lam i * x ^ 2) (y i) := by
      funext y; simp [Finset.sum_apply]
    rw [e, variance_sum_pi (fun i => memLp_linear_add_sq_stdNormal (α i) (lam i))]
    exact Finset.sum_congr rfl fun i _ => variance_linear_add_sq_stdNormal _ _

omit [DecidableEq κ] in
/-- **Rotation invariance** of the standard normal vector: for an orthonormal basis `b` of
`ℝ^κ`, the vector `∑ᵢ yᵢ bᵢ` is again standard normal. -/
theorem stdNormalPi_map_orthonormalBasis (b : OrthonormalBasis κ ℝ (EuclideanSpace ℝ κ)) :
    (stdNormalPi κ).map (fun y : κ → ℝ => fun j => ∑ i, y i * b i j) = stdNormalPi κ := by
  have h1 : (stdNormalPi κ).map (toLp 2) = stdGaussian (EuclideanSpace ℝ κ) :=
    map_pi_eq_stdGaussian
  have h2 := stdGaussian_eq_map_pi_orthonormalBasis b
  have e : (fun y : κ → ℝ => fun j => ∑ i, y i * b i j)
      = ofLp ∘ (fun x : κ → ℝ => ∑ i, x i • b i) := by
    funext y j; simp
  have hm : Measurable (fun x : κ → ℝ => ∑ i, x i • b i) := by fun_prop
  rw [e, ← Measure.map_map (WithLp.measurable_ofLp 2 _) hm, ← h2, ← h1,
    Measure.map_map (WithLp.measurable_ofLp 2 _) (WithLp.measurable_toLp 2 _)]
  exact Measure.map_id

/-- Orthogonal diagonalisation of a real symmetric matrix, packaged for our purposes: the matrix
`U` whose columns are an orthonormal eigenbasis `b`. -/
theorem exists_orthogonal_diagonalization {Q : Matrix κ κ ℝ} (hQ : Q.IsSymm) :
    ∃ (U : Matrix κ κ ℝ) (lam : κ → ℝ) (b : OrthonormalBasis κ ℝ (EuclideanSpace ℝ κ)),
      (∀ i j, U i j = b j i) ∧ Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧ Uᵀ * Q * U = diagonal lam := by
  have hH : Q.IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact hQ
  refine ⟨(hH.eigenvectorUnitary : Matrix κ κ ℝ), hH.eigenvalues, hH.eigenvectorBasis,
    fun i j => rfl, ?_, ?_, ?_⟩
  · have := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    simpa [star_eq_conjTranspose] using this
  · have := Unitary.coe_mul_star_self hH.eigenvectorUnitary
    simpa [star_eq_conjTranspose] using this
  · have := hH.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Unitary.conjStarAlgAut_star_apply, star_eq_conjTranspose] using this

omit [DecidableEq ι] [DecidableEq κ] in
/-- `y ↦ M y` is measurable. -/
theorem measurable_mulVec (M : Matrix ι κ ℝ) : Measurable (fun y : κ → ℝ => M *ᵥ y) := by
  refine measurable_pi_iff.mpr fun i => ?_
  simp only [mulVec, dotProduct]
  fun_prop

omit [DecidableEq κ] in
/-- The affine-quadratic form `x ↦ c₀ + aᵀx + xᵀQx` is measurable. -/
theorem measurable_form (c₀ : ℝ) (a : κ → ℝ) (Q : Matrix κ κ ℝ) :
    Measurable (fun x : κ → ℝ => c₀ + a ⬝ᵥ x + x ⬝ᵥ Q *ᵥ x) := by
  simp only [mulVec, dotProduct]
  fun_prop

omit [DecidableEq ι] [DecidableEq κ] in
/-- `‖Mᵀ g‖² = gᵀ (M Mᵀ) g`. -/
theorem vecMul_dotProduct_vecMul (M : Matrix ι κ ℝ) (g : ι → ℝ) :
    (g ᵥ* M) ⬝ᵥ (g ᵥ* M) = g ⬝ᵥ (M * Mᵀ) *ᵥ g := by
  rw [← mulVec_mulVec, dotProduct_mulVec, mulVec_transpose]

omit [DecidableEq ι] [DecidableEq κ] in
/-- Change of variables `z = M y` in the affine-quadratic form. -/
theorem form_mulVec (M : Matrix ι κ ℝ) (χ : ℝ) (g : ι → ℝ) (D : Matrix ι ι ℝ) (y : κ → ℝ) :
    χ + g ⬝ᵥ (M *ᵥ y) + (M *ᵥ y) ⬝ᵥ D *ᵥ (M *ᵥ y)
      = χ + (g ᵥ* M) ⬝ᵥ y + y ⬝ᵥ (Mᵀ * D * M) *ᵥ y := by
  have h1 : g ⬝ᵥ (M *ᵥ y) = (g ᵥ* M) ⬝ᵥ y := dotProduct_mulVec g M y
  have h2 : (M *ᵥ y) ⬝ᵥ D *ᵥ (M *ᵥ y) = y ⬝ᵥ (Mᵀ * D * M) *ᵥ y := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec y Mᵀ, vecMul_transpose]
  rw [h1, h2]

/-- Mean, variance and square integrability of the affine-quadratic form
`c₀ + aᵀx + xᵀQx` (`Q` symmetric) in a standard normal vector `x`. -/
theorem form_stdNormalPi (c₀ : ℝ) (a : κ → ℝ) {Q : Matrix κ κ ℝ} (hQ : Q.IsSymm) :
    MemLp (fun x : κ → ℝ => c₀ + a ⬝ᵥ x + x ⬝ᵥ Q *ᵥ x) 2 (stdNormalPi κ) ∧
    ∫ x, (c₀ + a ⬝ᵥ x + x ⬝ᵥ Q *ᵥ x) ∂(stdNormalPi κ) = c₀ + Q.trace ∧
    Var[fun x : κ → ℝ => c₀ + a ⬝ᵥ x + x ⬝ᵥ Q *ᵥ x; stdNormalPi κ]
      = a ⬝ᵥ a + 2 * (Q * Q).trace := by
  obtain ⟨U, lam, b, hUb, hU1, hU2, hdiag⟩ := exists_orthogonal_diagonalization hQ
  have hFm : Measurable (fun x : κ → ℝ => c₀ + a ⬝ᵥ x + x ⬝ᵥ Q *ᵥ x) := measurable_form c₀ a Q
  have hRm : Measurable (fun y : κ → ℝ => U *ᵥ y) := measurable_mulVec U
  have hR : (stdNormalPi κ).map (fun y : κ → ℝ => U *ᵥ y) = stdNormalPi κ := by
    have h := stdNormalPi_map_orthonormalBasis b
    have e : (fun y : κ → ℝ => U *ᵥ y) = fun y : κ → ℝ => fun j => ∑ i, y i * b i j := by
      funext y j
      simp [mulVec, dotProduct, hUb, mul_comm]
    rw [e]; exact h
  have hcomp : ∀ y : κ → ℝ, c₀ + a ⬝ᵥ (U *ᵥ y) + (U *ᵥ y) ⬝ᵥ Q *ᵥ (U *ᵥ y)
      = c₀ + ∑ i, ((a ᵥ* U) i * y i + lam i * y i ^ 2) := by
    intro y
    rw [form_mulVec, hdiag, Finset.sum_add_distrib]
    simp [dotProduct, mulVec_diagonal, sq, mul_comm, mul_left_comm, add_assoc]
  obtain ⟨d1, d2, d3⟩ := diag_form_stdNormalPi c₀ (a ᵥ* U) lam
  have hsum1 : ∑ i, lam i = Q.trace := by
    have h : (diagonal lam).trace = (Uᵀ * Q * U).trace := by rw [hdiag]
    rw [trace_diagonal] at h
    rw [h, trace_mul_comm, ← Matrix.mul_assoc, hU2, Matrix.one_mul]
  have hsum2 : ∑ i, lam i ^ 2 = (Q * Q).trace := by
    have h : (diagonal lam * diagonal lam).trace = (Uᵀ * Q * U * (Uᵀ * Q * U)).trace := by
      rw [hdiag]
    have e : Uᵀ * Q * U * (Uᵀ * Q * U) = Uᵀ * (Q * Q) * U := by
      calc Uᵀ * Q * U * (Uᵀ * Q * U) = Uᵀ * Q * (U * Uᵀ) * Q * U := by
            simp only [Matrix.mul_assoc]
        _ = Uᵀ * (Q * Q) * U := by rw [hU2]; simp only [Matrix.mul_assoc, Matrix.mul_one]
    rw [diagonal_mul_diagonal, trace_diagonal, e, trace_mul_comm, ← Matrix.mul_assoc, hU2,
      Matrix.one_mul] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => sq (lam i)
  have hsum3 : ∑ i, (a ᵥ* U) i ^ 2 = a ⬝ᵥ a := by
    have h := vecMul_dotProduct_vecMul U a
    rw [hU2, one_mulVec] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => sq _
  refine ⟨?_, ?_, ?_⟩
  · have h : MemLp (fun x : κ → ℝ => c₀ + a ⬝ᵥ x + x ⬝ᵥ Q *ᵥ x) 2
        ((stdNormalPi κ).map (fun y : κ → ℝ => U *ᵥ y)) := by
      have e : (fun x : κ → ℝ => c₀ + a ⬝ᵥ x + x ⬝ᵥ Q *ᵥ x) ∘ (fun y : κ → ℝ => U *ᵥ y)
          = fun y => c₀ + ∑ i, ((a ᵥ* U) i * y i + lam i * y i ^ 2) := funext hcomp
      rw [memLp_map_measure_iff hFm.aestronglyMeasurable hRm.aemeasurable, e]
      exact d1
    rwa [hR] at h
  · have h : ∫ x, (c₀ + a ⬝ᵥ x + x ⬝ᵥ Q *ᵥ x) ∂((stdNormalPi κ).map (fun y : κ → ℝ => U *ᵥ y))
        = c₀ + Q.trace := by
      rw [integral_map hRm.aemeasurable hFm.aestronglyMeasurable]
      simp_rw [hcomp]
      rw [d2, hsum1]
    rwa [hR] at h
  · have h : Var[fun x : κ → ℝ => c₀ + a ⬝ᵥ x + x ⬝ᵥ Q *ᵥ x;
        (stdNormalPi κ).map (fun y : κ → ℝ => U *ᵥ y)] = a ⬝ᵥ a + 2 * (Q * Q).trace := by
      rw [variance_map hFm.aemeasurable hRm.aemeasurable]
      have e : (fun x : κ → ℝ => c₀ + a ⬝ᵥ x + x ⬝ᵥ Q *ᵥ x) ∘ (fun y : κ → ℝ => U *ᵥ y)
          = fun y => c₀ + ∑ i, ((a ᵥ* U) i * y i + lam i * y i ^ 2) := funext hcomp
      rw [e, d3, Finset.sum_add_distrib, ← Finset.mul_sum, hsum2, hsum3]
    rwa [hR] at h

/-- The centered Gaussian law on `ι → ℝ` of `M w`, for `w` a standard normal vector in `ℝ^κ`.
Its covariance matrix is `M Mᵀ` (see `gaussianImage_map_toLp`). -/
noncomputable def gaussianImage (M : Matrix ι κ ℝ) : Measure (ι → ℝ) :=
  (stdNormalPi κ).map (fun y => M *ᵥ y)

omit [DecidableEq ι] [DecidableEq κ] in
/-- Mean, variance and square integrability of `χ + gᵀz + zᵀDz` (`D` symmetric) for `z = M w`,
`w` standard normal: with `C = M Mᵀ`, the mean is `χ + tr(C D)` and the variance is
`gᵀ C g + 2 tr((C D)²)`. -/
theorem form_gaussianImage (M : Matrix ι κ ℝ) (χ : ℝ) (g : ι → ℝ) {D : Matrix ι ι ℝ}
    (hD : D.IsSymm) :
    MemLp (fun z : ι → ℝ => χ + g ⬝ᵥ z + z ⬝ᵥ D *ᵥ z) 2 (gaussianImage M) ∧
    ∫ z, (χ + g ⬝ᵥ z + z ⬝ᵥ D *ᵥ z) ∂(gaussianImage M) = χ + (M * Mᵀ * D).trace ∧
    Var[fun z : ι → ℝ => χ + g ⬝ᵥ z + z ⬝ᵥ D *ᵥ z; gaussianImage M]
      = g ⬝ᵥ (M * Mᵀ) *ᵥ g + 2 * ((M * Mᵀ * D) * (M * Mᵀ * D)).trace := by
  classical
  have hFm : Measurable (fun z : ι → ℝ => χ + g ⬝ᵥ z + z ⬝ᵥ D *ᵥ z) := measurable_form χ g D
  have hMm : Measurable (fun y : κ → ℝ => M *ᵥ y) := measurable_mulVec M
  have hQ : (Mᵀ * D * M).IsSymm := by
    rw [Matrix.IsSymm, transpose_mul, transpose_mul, transpose_transpose, hD.eq, Matrix.mul_assoc]
  obtain ⟨d1, d2, d3⟩ := form_stdNormalPi χ (g ᵥ* M) hQ
  have htr1 : (Mᵀ * D * M).trace = (M * Mᵀ * D).trace := by
    rw [trace_mul_comm, Matrix.mul_assoc]
  have htr2 : ((Mᵀ * D * M) * (Mᵀ * D * M)).trace = ((M * Mᵀ * D) * (M * Mᵀ * D)).trace := by
    calc ((Mᵀ * D * M) * (Mᵀ * D * M)).trace = (Mᵀ * (D * M * Mᵀ * D * M)).trace := by
          simp only [Matrix.mul_assoc]
      _ = ((D * M * Mᵀ * D * M) * Mᵀ).trace := trace_mul_comm _ _
      _ = (D * (M * Mᵀ * D * M * Mᵀ)).trace := by simp only [Matrix.mul_assoc]
      _ = ((M * Mᵀ * D * M * Mᵀ) * D).trace := trace_mul_comm _ _
      _ = ((M * Mᵀ * D) * (M * Mᵀ * D)).trace := by simp only [Matrix.mul_assoc]
  have hcomp : (fun z : ι → ℝ => χ + g ⬝ᵥ z + z ⬝ᵥ D *ᵥ z) ∘ (fun y : κ → ℝ => M *ᵥ y)
      = fun y => χ + (g ᵥ* M) ⬝ᵥ y + y ⬝ᵥ (Mᵀ * D * M) *ᵥ y :=
    funext fun y => form_mulVec M χ g D y
  unfold gaussianImage
  refine ⟨?_, ?_, ?_⟩
  · rw [memLp_map_measure_iff hFm.aestronglyMeasurable hMm.aemeasurable, hcomp]
    exact d1
  · rw [integral_map hMm.aemeasurable hFm.aestronglyMeasurable]
    simp_rw [form_mulVec]
    rw [d2, htr1]
  · rw [variance_map hFm.aemeasurable hMm.aemeasurable, hcomp, d3, vecMul_dotProduct_vecMul,
      htr2]

instance (M : Matrix ι κ ℝ) : IsProbabilityMeasure (gaussianImage M) := by
  unfold gaussianImage; infer_instance

/-- **Bridge to Mathlib.**  The law of `M w` (`w` standard normal in `ℝ^κ`), viewed on
`EuclideanSpace ℝ ι`, is Mathlib's multivariate Gaussian `𝒩(0, M Mᵀ)`.  In particular it only
depends on the covariance matrix `C = M Mᵀ`. -/
theorem gaussianImage_map_toLp (M : Matrix ι κ ℝ) :
    (gaussianImage M).map (toLp 2) = multivariateGaussian 0 (M * Mᵀ) := by
  have hPSD : (M * Mᵀ).PosSemidef := by
    simpa using Matrix.posSemidef_self_mul_conjTranspose M
  have hMm := measurable_mulVec M
  refine Measure.ext_of_charFun ?_
  funext t
  have h0 := charFun_stdGaussian (E := EuclideanSpace ℝ κ) (toLp 2 (Mᵀ *ᵥ ofLp t))
  rw [← map_pi_eq_stdGaussian, charFun_apply,
    integral_map (WithLp.measurable_toLp 2 _).aemeasurable (by fun_prop)] at h0
  have e : ∀ y : κ → ℝ, ⟪toLp 2 (M *ᵥ y), t⟫ = ⟪toLp 2 y, toLp 2 (Mᵀ *ᵥ ofLp t)⟫ := by
    intro y
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    rw [dotProduct_mulVec, ← mulVec_transpose]
  rw [charFun_multivariateGaussian hPSD, gaussianImage,
    Measure.map_map (WithLp.measurable_toLp 2 _) hMm, charFun_apply,
    integral_map ((WithLp.measurable_toLp 2 _).comp hMm).aemeasurable (by fun_prop)]
  simp only [Function.comp_apply, e]
  rw [h0]
  congr 1
  have hn : ‖toLp 2 (Mᵀ *ᵥ ofLp t)‖ ^ 2 = ofLp t ⬝ᵥ (M * Mᵀ) *ᵥ ofLp t := by
    rw [EuclideanSpace.real_norm_sq_eq, ← vecMul_dotProduct_vecMul, ← mulVec_transpose]
    simp [dotProduct, sq]
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
  rw [← hn]
  push_cast
  ring

/-- The positive square root `C^{1/2}` of a real matrix is symmetric. -/
theorem transpose_sqrt (C : Matrix ι ι ℝ) : (CFC.sqrt C)ᵀ = CFC.sqrt C := by
  have := (CFC.sqrt_nonneg C).isSelfAdjoint
  rw [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  exact this

/-- Every positive semidefinite matrix is of the form `M Mᵀ` (take `M = C^{1/2}`). -/
theorem sqrt_mul_sqrt_transpose {C : Matrix ι ι ℝ} (hC : C.PosSemidef) :
    CFC.sqrt C * (CFC.sqrt C)ᵀ = C := by
  rw [transpose_sqrt, CFC.sqrt_mul_sqrt_self C hC.nonneg]

/-- A positive semidefinite real matrix is symmetric. -/
theorem isSymm_of_posSemidef {C : Matrix ι ι ℝ} (hC : C.PosSemidef) : C.IsSymm := by
  have := hC.isHermitian
  rwa [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] at this

/-- For a positive semidefinite matrix, `‖C‖₂ ≤ tr(C)`: a trace bound on the noise covariance
(Assumption "Noise spectral bounds") controls the spectral norm in Lemma "Variance of Gaussian
Forms". -/
theorem l2_opNorm_le_trace_of_posSemidef {C : Matrix ι ι ℝ} (hC : C.PosSemidef) :
    ‖C‖ ≤ C.trace := by
  have h2 : (CFC.sqrt C)ᵀ * CFC.sqrt C = C := by
    rw [transpose_sqrt, CFC.sqrt_mul_sqrt_self C hC.nonneg]
  have h3 := l2_opNorm_conjTranspose_mul_self (CFC.sqrt C)
  rw [conjTranspose_eq_transpose_of_trivial, h2] at h3
  have h4 := l2_opNorm_sq_le_trace (CFC.sqrt C)
  rw [h2] at h4
  rw [h3, ← pow_two]
  exact h4

/-- Mathlib's `𝒩(0, C)` read on `ι → ℝ` is the law of `C^{1/2} w`, `w` standard normal. -/
theorem multivariateGaussian_map_ofLp {C : Matrix ι ι ℝ} (hC : C.PosSemidef) :
    (multivariateGaussian 0 C).map ofLp = gaussianImage (CFC.sqrt C) := by
  have h := gaussianImage_map_toLp (CFC.sqrt C)
  rw [sqrt_mul_sqrt_transpose hC] at h
  rw [← h, Measure.map_map (WithLp.measurable_ofLp 2 _) (WithLp.measurable_toLp 2 _)]
  exact Measure.map_id

end GaussianForms

open GaussianForms

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- `z ∼ 𝒩(0, C)`: the random vector `z : Ω → ℝ^ι` is centered Gaussian with covariance matrix
`C` under `μ`, i.e. its law (read on `EuclideanSpace ℝ ι`) is Mathlib's
`ProbabilityTheory.multivariateGaussian 0 C`.  (Only meaningful for `C` positive semidefinite.) -/
def IsCenteredGaussian (z : Ω → ι → ℝ) (C : Matrix ι ι ℝ) (μ : Measure Ω) : Prop :=
  HasLaw (fun ω => toLp 2 (z ω)) (multivariateGaussian 0 C) μ

namespace IsCenteredGaussian

variable {z : Ω → ι → ℝ} {C : Matrix ι ι ℝ}

/-- Unfolding of the definition. -/
theorem hasLaw (hz : IsCenteredGaussian z C μ) :
    HasLaw (fun ω => toLp 2 (z ω)) (multivariateGaussian 0 C) μ := hz

/-- A centered Gaussian vector is a.e.-measurable. -/
theorem aemeasurable (hz : IsCenteredGaussian z C μ) : AEMeasurable z μ :=
  (WithLp.measurable_ofLp 2 (ι → ℝ)).comp_aemeasurable hz.hasLaw.aemeasurable

/-- The underlying measure of a centered Gaussian vector is a probability measure. -/
theorem isProbabilityMeasure (hz : IsCenteredGaussian z C μ) : IsProbabilityMeasure μ :=
  hz.hasLaw.isProbabilityMeasure

/-- A centered Gaussian vector has the law of `C^{1/2} w` with `w` standard normal. -/
theorem hasLaw_gaussianImage (hz : IsCenteredGaussian z C μ) (hC : C.PosSemidef) :
    HasLaw z (gaussianImage (CFC.sqrt C)) μ := by
  refine ⟨hz.aemeasurable, ?_⟩
  rw [← multivariateGaussian_map_ofLp hC, ← hz.hasLaw.map_eq,
    AEMeasurable.map_map_of_aemeasurable (WithLp.measurable_ofLp 2 _).aemeasurable
      hz.hasLaw.aemeasurable]
  rfl

/-- **Linear images.**  If `z ∼ 𝒩(0, C)` and `A` is a deterministic matrix, then
`A z ∼ 𝒩(0, A C Aᵀ)`.  In particular, if the SGD noise is `ξ ∼ 𝒩(0, Σ)` and `U` is the
eigenvector matrix of the Hessian, the eigen-coordinates `ζ = Uᵀ ξ` of the noise satisfy
`ζ ∼ 𝒩(0, Uᵀ Σ U)`, which is the matrix `C` of the paper (§3.2). -/
theorem mulVec {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (hz : IsCenteredGaussian z C μ)
    (hC : C.PosSemidef) (A : Matrix ι' ι ℝ) :
    IsCenteredGaussian (fun ω => A *ᵥ z ω) (A * C * Aᵀ) μ := by
  have hlaw := hz.hasLaw_gaussianImage hC
  have h2 : HasLaw (fun y : ι → ℝ => toLp 2 (A *ᵥ y)) (multivariateGaussian 0 (A * C * Aᵀ))
      (gaussianImage (CFC.sqrt C)) := by
    refine ⟨((WithLp.measurable_toLp 2 _).comp (measurable_mulVec A)).aemeasurable, ?_⟩
    have h := gaussianImage_map_toLp (A * CFC.sqrt C)
    rw [transpose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc A, sqrt_mul_sqrt_transpose hC] at h
    rw [← h, gaussianImage, gaussianImage,
      Measure.map_map (g := fun y : ι → ℝ => toLp 2 (A *ᵥ y))
        (f := fun y : ι → ℝ => CFC.sqrt C *ᵥ y)
        ((WithLp.measurable_toLp 2 _).comp (measurable_mulVec A)) (measurable_mulVec _),
      Measure.map_map (g := toLp 2) (f := fun y : ι → ℝ => (A * CFC.sqrt C) *ᵥ y)
        (WithLp.measurable_toLp 2 _) (measurable_mulVec _)]
    congr 1
    funext y
    simp [Function.comp, mulVec_mulVec]
  exact h2.comp hlaw

end IsCenteredGaussian

/-- Unfolding of `IsCenteredGaussian`. -/
theorem isCenteredGaussian_iff {z : Ω → ι → ℝ} {C : Matrix ι ι ℝ} :
    IsCenteredGaussian z C μ ↔ HasLaw (fun ω => toLp 2 (z ω)) (multivariateGaussian 0 C) μ :=
  Iff.rfl

/-- **Model (A) ⟹ `𝒩(0, M Mᵀ)`.**  If `w_k` are independent standard normal variables and `M` is
a deterministic matrix, then `z = M w` is centered Gaussian with covariance `M Mᵀ`. -/
theorem isCenteredGaussian_of_iIndepFun (M : Matrix ι κ ℝ) {w : κ → Ω → ℝ}
    (hw : ∀ k, HasLaw (w k) (gaussianReal 0 1) μ) (hind : iIndepFun w μ) :
    IsCenteredGaussian (fun ω => M *ᵥ (fun k => w k ω)) (M * Mᵀ) μ := by
  have h1 : HasLaw (fun ω k => w k ω) (stdNormalPi κ) μ := hind.hasLaw_pi hw
  have h2 : HasLaw (fun y : κ → ℝ => toLp 2 (M *ᵥ y)) (multivariateGaussian 0 (M * Mᵀ))
      (stdNormalPi κ) := by
    refine ⟨((WithLp.measurable_toLp 2 _).comp (measurable_mulVec M)).aemeasurable, ?_⟩
    rw [← gaussianImage_map_toLp, gaussianImage,
      Measure.map_map (WithLp.measurable_toLp 2 _) (measurable_mulVec M)]
    rfl
  exact h2.comp h1

/-- Non-vacuity: for every `C` the canonical realisation on `EuclideanSpace ℝ ι` is a centered
Gaussian vector with covariance `C`. -/
theorem isCenteredGaussian_ofLp (C : Matrix ι ι ℝ) :
    IsCenteredGaussian (fun x : EuclideanSpace ℝ ι => ofLp x) C (multivariateGaussian 0 C) := by
  refine ⟨aemeasurable_id, ?_⟩
  exact Measure.map_id

/-- Non-vacuity of the hypotheses of `isCenteredGaussian_of_iIndepFun`: on the product space
`(ℝ^κ, 𝒩(0,1)^{⊗κ})` the coordinates are independent standard normal variables. -/
theorem iIndepFun_eval_stdNormalPi :
    (∀ k, HasLaw (fun y : κ → ℝ => y k) (gaussianReal 0 1) (stdNormalPi κ)) ∧
      iIndepFun (fun (k : κ) (y : κ → ℝ) => y k) (stdNormalPi κ) :=
  ⟨fun k => (measurePreserving_eval (fun _ : κ => gaussianReal 0 1) k).hasLaw,
    iIndepFun_pi (X := fun _ x => x) fun _ => aemeasurable_id⟩

/-! ## Main results: Lemma "Variance of Gaussian Forms" (paper Lemma `lem:gauss-var`) -/

namespace IsCenteredGaussian

variable {z : Ω → ι → ℝ} {C : Matrix ι ι ℝ}

/-- Sanity check of the model: the covariance of the coordinates of `z ∼ 𝒩(0, C)` is `C`. -/
theorem covariance_apply (hz : IsCenteredGaussian z C μ) (hC : C.PosSemidef) (i j : ι) :
    cov[fun ω => z ω i, fun ω => z ω j; μ] = C i j := by
  have h := hz.hasLaw.covariance_fun_comp (f := fun x : EuclideanSpace ℝ ι => x i)
    (g := fun x : EuclideanSpace ℝ ι => x j) (by fun_prop) (by fun_prop)
  rw [covariance_eval_multivariateGaussian hC] at h
  exact h

/-- **Master statement.**  For `z ∼ 𝒩(0, C)`, `C ⪰ 0`, a constant `χ`, a deterministic vector
`g` and a deterministic *symmetric* matrix `D`, the affine-quadratic form
`χ + gᵀz + zᵀDz` is square integrable, has mean `χ + tr(C D)` and variance
`gᵀ C g + 2 tr((C D)²)`. -/
theorem affine_quadratic_form (hz : IsCenteredGaussian z C μ) (hC : C.PosSemidef)
    (χ : ℝ) (g : ι → ℝ) {D : Matrix ι ι ℝ} (hD : D.IsSymm) :
    MemLp (fun ω => χ + g ⬝ᵥ z ω + z ω ⬝ᵥ D *ᵥ z ω) 2 μ ∧
    ∫ ω, (χ + g ⬝ᵥ z ω + z ω ⬝ᵥ D *ᵥ z ω) ∂μ = χ + (C * D).trace ∧
    Var[fun ω => χ + g ⬝ᵥ z ω + z ω ⬝ᵥ D *ᵥ z ω; μ]
      = g ⬝ᵥ C *ᵥ g + 2 * ((C * D) ^ 2).trace := by
  have hlaw := hz.hasLaw_gaussianImage hC
  obtain ⟨d1, d2, d3⟩ := form_gaussianImage (CFC.sqrt C) χ g hD
  rw [sqrt_mul_sqrt_transpose hC] at d2 d3
  have hFm := measurable_form χ g D
  refine ⟨hlaw.memLp_comp d1, ?_, ?_⟩
  · rw [← d2]
    exact hlaw.integral_comp hFm.aestronglyMeasurable
  · rw [pow_two, ← d3, ← hlaw.map_eq, variance_map (by rw [hlaw.map_eq]; exact hFm.aemeasurable)
      hlaw.aemeasurable]
    rfl

/-- Square integrability of `χ + gᵀz + zᵀDz`. -/
theorem memLp_form (hz : IsCenteredGaussian z C μ) (hC : C.PosSemidef)
    (χ : ℝ) (g : ι → ℝ) {D : Matrix ι ι ℝ} (hD : D.IsSymm) :
    MemLp (fun ω => χ + g ⬝ᵥ z ω + z ω ⬝ᵥ D *ᵥ z ω) 2 μ :=
  (hz.affine_quadratic_form hC χ g hD).1

/-- `𝔼[χ + gᵀz + zᵀDz] = χ + tr(C D)`; for the `s_{t+1}^S` of the paper this is Lemma
"Elementwise expectation". -/
theorem integral_form (hz : IsCenteredGaussian z C μ) (hC : C.PosSemidef)
    (χ : ℝ) (g : ι → ℝ) {D : Matrix ι ι ℝ} (hD : D.IsSymm) :
    ∫ ω, (χ + g ⬝ᵥ z ω + z ω ⬝ᵥ D *ᵥ z ω) ∂μ = χ + (C * D).trace :=
  (hz.affine_quadratic_form hC χ g hD).2.1

/-- `Var(χ + gᵀz + zᵀDz) = gᵀ C g + 2 tr((C D)²)`: the variance used in the proof of Lemma
"Asymptotic ratio of expectations" (tex l. 1022), where `s_{t+1}^S = χ + gᵀz + zᵀDz`. -/
theorem variance_form (hz : IsCenteredGaussian z C μ) (hC : C.PosSemidef)
    (χ : ℝ) (g : ι → ℝ) {D : Matrix ι ι ℝ} (hD : D.IsSymm) :
    Var[fun ω => χ + g ⬝ᵥ z ω + z ω ⬝ᵥ D *ᵥ z ω; μ]
      = g ⬝ᵥ C *ᵥ g + 2 * ((C * D) ^ 2).trace :=
  (hz.affine_quadratic_form hC χ g hD).2.2

/-- The linear form `gᵀz`: square integrable, mean `0`, variance `gᵀ C g`. -/
theorem linear_form (hz : IsCenteredGaussian z C μ) (hC : C.PosSemidef) (g : ι → ℝ) :
    MemLp (fun ω => g ⬝ᵥ z ω) 2 μ ∧ ∫ ω, g ⬝ᵥ z ω ∂μ = 0 ∧
      Var[fun ω => g ⬝ᵥ z ω; μ] = g ⬝ᵥ C *ᵥ g := by
  have h := hz.affine_quadratic_form hC 0 g (D := 0) isSymm_zero
  simpa using h

/-- The quadratic form `zᵀDz` (`D` symmetric): square integrable, mean `tr(C D)`, variance
`2 tr((C D)²)`. -/
theorem quadratic_form (hz : IsCenteredGaussian z C μ) (hC : C.PosSemidef)
    {D : Matrix ι ι ℝ} (hD : D.IsSymm) :
    MemLp (fun ω => z ω ⬝ᵥ D *ᵥ z ω) 2 μ ∧ ∫ ω, z ω ⬝ᵥ D *ᵥ z ω ∂μ = (C * D).trace ∧
      Var[fun ω => z ω ⬝ᵥ D *ᵥ z ω; μ] = 2 * ((C * D) ^ 2).trace := by
  have h := hz.affine_quadratic_form hC 0 0 hD
  simpa using h

/-- `𝔼[gᵀz] = 0`. -/
theorem integral_linear (hz : IsCenteredGaussian z C μ) (hC : C.PosSemidef) (g : ι → ℝ) :
    ∫ ω, g ⬝ᵥ z ω ∂μ = 0 := (hz.linear_form hC g).2.1

/-- **Lemma "Variance of Gaussian Forms", first identity:** `Var(gᵀz) = gᵀ C g`. -/
theorem variance_linear (hz : IsCenteredGaussian z C μ) (hC : C.PosSemidef) (g : ι → ℝ) :
    Var[fun ω => g ⬝ᵥ z ω; μ] = g ⬝ᵥ C *ᵥ g := (hz.linear_form hC g).2.2

/-- **Lemma "Variance of Gaussian Forms", first display:** `Var(gᵀz) ≤ ‖C‖₂ ‖g‖₂²`
(`‖C‖` is the spectral norm `Matrix.Norms.L2Operator`). -/
theorem variance_linear_le (hz : IsCenteredGaussian z C μ) (hC : C.PosSemidef) (g : ι → ℝ) :
    Var[fun ω => g ⬝ᵥ z ω; μ] ≤ ‖C‖ * ∑ i, g i ^ 2 := by
  rw [hz.variance_linear hC g]
  exact dotProduct_mulVec_le_sum_sq C g

/-- `𝔼[zᵀDz] = tr(C D)` for symmetric `D`. -/
theorem integral_quadratic (hz : IsCenteredGaussian z C μ) (hC : C.PosSemidef)
    {D : Matrix ι ι ℝ} (hD : D.IsSymm) :
    ∫ ω, z ω ⬝ᵥ D *ᵥ z ω ∂μ = (C * D).trace := (hz.quadratic_form hC hD).2.1

/-- **Lemma "Variance of Gaussian Forms", second identity:** `Var(zᵀDz) = 2 tr((C D)²)`, for
every symmetric (in particular every diagonal) `D`. -/
theorem variance_quadratic (hz : IsCenteredGaussian z C μ) (hC : C.PosSemidef)
    {D : Matrix ι ι ℝ} (hD : D.IsSymm) :
    Var[fun ω => z ω ⬝ᵥ D *ᵥ z ω; μ] = 2 * ((C * D) ^ 2).trace := (hz.quadratic_form hC hD).2.2

/-- **Lemma "Variance of Gaussian Forms", second display:**
`Var(zᵀDz) ≤ 2 ‖C‖₂² tr(D²)` for symmetric `D`. -/
theorem variance_quadratic_le (hz : IsCenteredGaussian z C μ) (hC : C.PosSemidef)
    {D : Matrix ι ι ℝ} (hD : D.IsSymm) :
    Var[fun ω => z ω ⬝ᵥ D *ᵥ z ω; μ] ≤ 2 * ‖C‖ ^ 2 * (D ^ 2).trace := by
  rw [hz.variance_quadratic hC hD]
  have := trace_mul_sq_le_of_isSymm C hD
  linarith

/-- Coordinate form of the mean for diagonal `D = diag(d)`: `𝔼[∑ᵢ dᵢ zᵢ²] = ∑ᵢ C_ii dᵢ`. -/
theorem integral_diagonal_quadratic (hz : IsCenteredGaussian z C μ) (hC : C.PosSemidef)
    (d : ι → ℝ) : ∫ ω, ∑ i, d i * z ω i ^ 2 ∂μ = ∑ i, C i i * d i := by
  have h := hz.integral_quadratic hC (isSymm_diagonal d)
  simp_rw [dotProduct_diagonal_mulVec] at h
  rw [h, trace_mul_diagonal]

/-- Coordinate form of the variance for diagonal `D = diag(d)`:
`Var(∑ᵢ dᵢ zᵢ²) = 2 ∑ᵢⱼ dᵢ dⱼ C_ij²`. -/
theorem variance_diagonal_quadratic (hz : IsCenteredGaussian z C μ) (hC : C.PosSemidef)
    (d : ι → ℝ) :
    Var[fun ω => ∑ i, d i * z ω i ^ 2; μ] = 2 * ∑ i, ∑ j, d i * d j * C i j ^ 2 := by
  have h := hz.variance_quadratic hC (isSymm_diagonal d)
  simp_rw [dotProduct_diagonal_mulVec] at h
  rw [h, trace_mul_diagonal_sq (isSymm_of_posSemidef hC)]

/-- `Cov(gᵀz, zᵀDz) = 0`: the linear and the quadratic form in a centered Gaussian vector are
uncorrelated (odd moments vanish). -/
theorem covariance_linear_quadratic (hz : IsCenteredGaussian z C μ) (hC : C.PosSemidef)
    (g : ι → ℝ) {D : Matrix ι ι ℝ} (hD : D.IsSymm) :
    cov[fun ω => g ⬝ᵥ z ω, fun ω => z ω ⬝ᵥ D *ᵥ z ω; μ] = 0 := by
  have := hz.isProbabilityMeasure
  obtain ⟨l1, -, l3⟩ := hz.linear_form hC g
  obtain ⟨q1, -, q3⟩ := hz.quadratic_form hC hD
  have f3 := hz.variance_form hC 0 g hD
  simp only [zero_add] at f3
  have hadd := variance_fun_add l1 q1
  rw [f3, l3, q3] at hadd
  linarith

/-- Upper bound for the variance of the affine-quadratic form:
`Var(χ + gᵀz + zᵀDz) ≤ ‖C‖₂ ‖g‖₂² + 2 ‖C‖₂² tr(D²)`. -/
theorem variance_form_le (hz : IsCenteredGaussian z C μ) (hC : C.PosSemidef)
    (χ : ℝ) (g : ι → ℝ) {D : Matrix ι ι ℝ} (hD : D.IsSymm) :
    Var[fun ω => χ + g ⬝ᵥ z ω + z ω ⬝ᵥ D *ᵥ z ω; μ]
      ≤ ‖C‖ * ∑ i, g i ^ 2 + 2 * ‖C‖ ^ 2 * (D ^ 2).trace := by
  rw [hz.variance_form hC χ g hD]
  have h1 := dotProduct_mulVec_le_sum_sq C g
  have h2 := trace_mul_sq_le_of_isSymm C hD
  linarith

end IsCenteredGaussian

/-- **Lemma "Variance of Gaussian Forms"** (paper Lemma `lem:gauss-var`, tex l. 950–959), as
stated in the paper.  Let `z ∼ 𝒩(0, C)` with `C = Cᵀ ⪰ 0`.  For any deterministic vector `g` and
any deterministic diagonal matrix `D = diag(d₁, …, d_d)`:
`Var(gᵀz) = gᵀ C g ≤ ‖C‖₂ ‖g‖₂²` and `Var(zᵀDz) = 2 tr((C D)²) ≤ 2 ‖C‖₂² tr(D²)`. -/
theorem variance_gaussian_forms {z : Ω → ι → ℝ} {C : Matrix ι ι ℝ}
    (hz : IsCenteredGaussian z C μ) (hC : C.PosSemidef) (g d : ι → ℝ) :
    (Var[fun ω => g ⬝ᵥ z ω; μ] = g ⬝ᵥ C *ᵥ g ∧ g ⬝ᵥ C *ᵥ g ≤ ‖C‖ * ∑ i, g i ^ 2) ∧
    (Var[fun ω => z ω ⬝ᵥ diagonal d *ᵥ z ω; μ] = 2 * ((C * diagonal d) ^ 2).trace ∧
      2 * ((C * diagonal d) ^ 2).trace ≤ 2 * ‖C‖ ^ 2 * ((diagonal d) ^ 2).trace) := by
  refine ⟨⟨hz.variance_linear hC g, dotProduct_mulVec_le_sum_sq C g⟩,
    hz.variance_quadratic hC (isSymm_diagonal d), ?_⟩
  have := trace_mul_sq_le_of_isSymm C (isSymm_diagonal d)
  linarith

/-- The same lemma for the concrete model `z = M w` with `w_k` independent standard normal
variables (so `C = M Mᵀ`): variance of `χ + gᵀz + zᵀDz`. -/
theorem variance_form_of_iIndepFun (M : Matrix ι κ ℝ) {w : κ → Ω → ℝ}
    (hw : ∀ k, HasLaw (w k) (gaussianReal 0 1) μ) (hind : iIndepFun w μ)
    (χ : ℝ) (g : ι → ℝ) {D : Matrix ι ι ℝ} (hD : D.IsSymm) :
    Var[fun ω => χ + g ⬝ᵥ (M *ᵥ fun k => w k ω)
        + (M *ᵥ fun k => w k ω) ⬝ᵥ D *ᵥ (M *ᵥ fun k => w k ω); μ]
      = g ⬝ᵥ (M * Mᵀ) *ᵥ g + 2 * ((M * Mᵀ * D) ^ 2).trace :=
  (isCenteredGaussian_of_iIndepFun M hw hind).variance_form (posSemidef_mul_transpose M) χ g hD

/-! ## Application: the next-step block energy `s_{t+1}^S` (tex l. 1010–1022) -/

namespace GaussianForms

variable (P : Spec ι)

/-- `χ_{S,t} = ∑_{i∈S} λ_i² (1 - ηλ_i)² c_i²`, the noise-free part of `s_{t+1}^S`. -/
def chi (S : Finset ι) (η : ℝ) (c : ι → ℝ) : ℝ :=
  ∑ i ∈ S, P.lam i ^ 2 * (1 - η * P.lam i) ^ 2 * c i ^ 2

/-- `(g_{S,t})_i = -2η λ_i² (1 - ηλ_i) c_i` for `i ∈ S` and `0` otherwise. -/
def gVec (S : Finset ι) (η : ℝ) (c : ι → ℝ) : ι → ℝ :=
  fun i => if i ∈ S then -2 * η * P.lam i ^ 2 * (1 - η * P.lam i) * c i else 0

/-- `(D_{S,t})_{ii} = η² λ_i²` for `i ∈ S` and `0` otherwise. -/
def dVec (S : Finset ι) (η : ℝ) : ι → ℝ :=
  fun i => if i ∈ S then η ^ 2 * P.lam i ^ 2 else 0

/-- `‖g_{S,t}‖₂² = 4η² ∑_{i∈S} λ_i⁴ (1-ηλ_i)² c_i²`. -/
theorem gVec_dotProduct_self (S : Finset ι) (η : ℝ) (c : ι → ℝ) :
    ∑ i, gVec P S η c i ^ 2
      = 4 * η ^ 2 * ∑ i ∈ S, P.lam i ^ 4 * (1 - η * P.lam i) ^ 2 * c i ^ 2 := by
  have h : ∀ i, gVec P S η c i ^ 2
      = if i ∈ S then 4 * η ^ 2 * (P.lam i ^ 4 * (1 - η * P.lam i) ^ 2 * c i ^ 2) else 0 := by
    intro i
    unfold gVec
    split_ifs <;> ring
  simp_rw [h]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]

/-- `tr(D_{S,t}²) = η⁴ ∑_{i∈S} λ_i⁴`. -/
theorem trace_diagonal_dVec_sq (S : Finset ι) (η : ℝ) :
    ((diagonal (dVec P S η)) ^ 2).trace = η ^ 4 * ∑ i ∈ S, P.lam i ^ 4 := by
  rw [trace_diagonal_sq]
  have h : ∀ i, dVec P S η i ^ 2 = if i ∈ S then η ^ 4 * P.lam i ^ 4 else 0 := by
    intro i
    unfold dVec
    split_ifs <;> ring
  simp_rw [h]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]

end GaussianForms

namespace Spec

variable (P : Spec ι) (N : Noise ι)

/-- **Decomposition of `s_{t+1}^S`** (proof of Lemma "Asymptotic ratio of expectations", tex
l. 1011–1021): as a function of the noise `ζ` (in the eigenbasis),
`s_{t+1}^S = ∑_{i∈S} λ_i² ((1-ηλ_i) c_i - η ζ_i)² = χ_S + g_Sᵀ ζ + ζᵀ D_S ζ`. -/
theorem mom_cNext_eq_gaussian_form (S : Finset ι) (η : ℝ) (c ζ : ι → ℝ) :
    P.mom S 2 (P.cNext η c ζ)
      = chi P S η c + gVec P S η c ⬝ᵥ ζ + ζ ⬝ᵥ diagonal (dVec P S η) *ᵥ ζ := by
  simp only [mom, cNext, chi, gVec, dVec, dotProduct, mulVec_diagonal, ite_mul, zero_mul,
    mul_ite, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

variable {ζ : Ω → ι → ℝ} {C : Matrix ι ι ℝ}

/-- Square integrability of `s_{t+1}^S` for Gaussian noise `ζ ∼ 𝒩(0, C)`. -/
theorem memLp_sNext_of_isCenteredGaussian (hζ : IsCenteredGaussian ζ C μ) (hC : C.PosSemidef)
    (S : Finset ι) (η : ℝ) (c : ι → ℝ) :
    MemLp (fun ω => P.mom S 2 (P.cNext η c (ζ ω))) 2 μ := by
  simp_rw [P.mom_cNext_eq_gaussian_form]
  exact hζ.memLp_form hC _ _ (isSymm_diagonal _)

/-- **Lemma "Elementwise expectation" for Gaussian noise:** if `ζ ∼ 𝒩(0, C)` and
`κ_i² = C_ii`, then `𝔼[s_{t+1}^S | x_t] = ∑_{i∈S} (λ_i²(1-ηλ_i)² c_i² + η² λ_i² κ_i²)`,
i.e. `Spec.EsNext`. -/
theorem integral_sNext_of_isCenteredGaussian (hζ : IsCenteredGaussian ζ C μ)
    (hC : C.PosSemidef) (hN : ∀ i, N.kap2 i = C i i) (S : Finset ι) (η : ℝ) (c : ι → ℝ) :
    ∫ ω, P.mom S 2 (P.cNext η c (ζ ω)) ∂μ = P.EsNext N S η c := by
  simp_rw [P.mom_cNext_eq_gaussian_form]
  rw [hζ.integral_form hC _ _ (isSymm_diagonal _), trace_mul_diagonal]
  simp only [chi, dVec, EsNext, mul_ite, mul_zero, Finset.sum_ite_mem, Finset.univ_inter, hN]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Variance of `s_{t+1}^S`** for Gaussian noise `ζ ∼ 𝒩(0, C)` (tex l. 1022):
`Var(s_{t+1}^S | x_t) = g_Sᵀ C g_S + 2 tr((C D_S)²)`. -/
theorem variance_sNext_of_isCenteredGaussian (hζ : IsCenteredGaussian ζ C μ)
    (hC : C.PosSemidef) (S : Finset ι) (η : ℝ) (c : ι → ℝ) :
    Var[fun ω => P.mom S 2 (P.cNext η c (ζ ω)); μ]
      = gVec P S η c ⬝ᵥ C *ᵥ gVec P S η c + 2 * ((C * diagonal (dVec P S η)) ^ 2).trace := by
  simp_rw [P.mom_cNext_eq_gaussian_form]
  exact hζ.variance_form hC _ _ (isSymm_diagonal _)

/-- **Finite-`d` variance bound behind "`Var(s_{t+1}^S) = O(|S|)`"** (tex l. 1022):
`Var(s_{t+1}^S | x_t) ≤ 4η² ‖C‖₂ ∑_{i∈S} λ_i⁴ (1-ηλ_i)² c_i² + 2η⁴ ‖C‖₂² ∑_{i∈S} λ_i⁴`. -/
theorem variance_sNext_le_of_isCenteredGaussian (hζ : IsCenteredGaussian ζ C μ)
    (hC : C.PosSemidef) (S : Finset ι) (η : ℝ) (c : ι → ℝ) :
    Var[fun ω => P.mom S 2 (P.cNext η c (ζ ω)); μ]
      ≤ 4 * η ^ 2 * ‖C‖ * (∑ i ∈ S, P.lam i ^ 4 * (1 - η * P.lam i) ^ 2 * c i ^ 2)
        + 2 * η ^ 4 * ‖C‖ ^ 2 * ∑ i ∈ S, P.lam i ^ 4 := by
  simp_rw [P.mom_cNext_eq_gaussian_form]
  have h := hζ.variance_form_le hC (chi P S η c) (gVec P S η c)
    (isSymm_diagonal (dVec P S η))
  rw [gVec_dotProduct_self, trace_diagonal_dVec_sq] at h
  linarith

/-- The same bound in terms of the trace of the noise covariance (`‖C‖₂ ≤ tr C`, and
`tr C = tr Σ` is the quantity bounded in Assumption "Noise spectral bounds"):
`Var(s_{t+1}^S | x_t) ≤ 4η² tr(C) ∑_{i∈S} λ_i⁴ (1-ηλ_i)² c_i² + 2η⁴ tr(C)² ∑_{i∈S} λ_i⁴`. -/
theorem variance_sNext_le_trace_of_isCenteredGaussian (hζ : IsCenteredGaussian ζ C μ)
    (hC : C.PosSemidef) (S : Finset ι) (η : ℝ) (c : ι → ℝ) :
    Var[fun ω => P.mom S 2 (P.cNext η c (ζ ω)); μ]
      ≤ 4 * η ^ 2 * C.trace * (∑ i ∈ S, P.lam i ^ 4 * (1 - η * P.lam i) ^ 2 * c i ^ 2)
        + 2 * η ^ 4 * C.trace ^ 2 * ∑ i ∈ S, P.lam i ^ 4 := by
  have h := P.variance_sNext_le_of_isCenteredGaussian hζ hC S η c
  have hle : ‖C‖ ≤ C.trace := l2_opNorm_le_trace_of_posSemidef hC
  have hS1 : 0 ≤ ∑ i ∈ S, P.lam i ^ 4 * (1 - η * P.lam i) ^ 2 * c i ^ 2 :=
    Finset.sum_nonneg fun i _ => by positivity
  have hS2 : 0 ≤ ∑ i ∈ S, P.lam i ^ 4 := Finset.sum_nonneg fun i _ => by positivity
  have b1 : 4 * η ^ 2 * ‖C‖ * (∑ i ∈ S, P.lam i ^ 4 * (1 - η * P.lam i) ^ 2 * c i ^ 2)
      ≤ 4 * η ^ 2 * C.trace * (∑ i ∈ S, P.lam i ^ 4 * (1 - η * P.lam i) ^ 2 * c i ^ 2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (by positivity)) hS1
  have b2 : 2 * η ^ 4 * ‖C‖ ^ 2 * (∑ i ∈ S, P.lam i ^ 4)
      ≤ 2 * η ^ 4 * C.trace ^ 2 * ∑ i ∈ S, P.lam i ^ 4 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hle 2) (by positivity)) hS2
  linarith

/-- **Explicit "`Var(s_{t+1}^S) = O(|S|)`".**  With `λ_i ≤ λ_1`:
`Var(s_{t+1}^S | x_t) ≤ 4η² ‖C‖₂ λ_1⁴ (1 + |η| λ_1)² ∑_{i∈S} c_i² + 2η⁴ ‖C‖₂² λ_1⁴ |S|`.
Hence the variance is `O(|S|)` as soon as `η`, `λ_1`, `‖C‖₂` stay bounded and
`∑_{i∈S} c_i² = O(|S|)` (the paper's "trajectory boundedness").  Note that a bound on `λ_1` is
needed here; it is *not* part of the paper's Assumption 1 (see the fidelity note). -/
theorem variance_sNext_le_lam1_of_isCenteredGaussian (hζ : IsCenteredGaussian ζ C μ)
    (hC : C.PosSemidef) (S : Finset ι) (η : ℝ) (c : ι → ℝ) :
    Var[fun ω => P.mom S 2 (P.cNext η c (ζ ω)); μ]
      ≤ 4 * η ^ 2 * ‖C‖ * (P.lam1 ^ 4 * (1 + |η| * P.lam1) ^ 2 * ∑ i ∈ S, c i ^ 2)
        + 2 * η ^ 4 * ‖C‖ ^ 2 * (S.card * P.lam1 ^ 4) := by
  have h := P.variance_sNext_le_of_isCenteredGaussian hζ hC S η c
  have h4 : ∀ i, P.lam i ^ 4 ≤ P.lam1 ^ 4 := fun i =>
    pow_le_pow_left₀ (P.lam_pos i).le (P.le_lam1_all i) 4
  have h2 : ∀ i, (1 - η * P.lam i) ^ 2 ≤ (1 + |η| * P.lam1) ^ 2 := by
    intro i
    have u1 : η * P.lam i ≤ |η| * P.lam i :=
      mul_le_mul_of_nonneg_right (le_abs_self η) (P.lam_pos i).le
    have u2 : -|η| * P.lam i ≤ η * P.lam i :=
      mul_le_mul_of_nonneg_right (neg_abs_le η) (P.lam_pos i).le
    have u3 : |η| * P.lam i ≤ |η| * P.lam1 :=
      mul_le_mul_of_nonneg_left (P.le_lam1_all i) (abs_nonneg η)
    exact sq_le_sq' (by linarith) (by linarith)
  have hA : ∑ i ∈ S, P.lam i ^ 4 * (1 - η * P.lam i) ^ 2 * c i ^ 2
      ≤ P.lam1 ^ 4 * (1 + |η| * P.lam1) ^ 2 * ∑ i ∈ S, c i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (h4 i) (h2 i) (sq_nonneg _) (pow_nonneg P.lam1_pos.le 4)) (sq_nonneg _)
  have hB : ∑ i ∈ S, P.lam i ^ 4 ≤ S.card * P.lam1 ^ 4 := by
    have := Finset.sum_le_card_nsmul S (fun i => P.lam i ^ 4) (P.lam1 ^ 4) fun i _ => h4 i
    rwa [nsmul_eq_mul] at this
  have b1 := mul_le_mul_of_nonneg_left hA
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg η)) (norm_nonneg C))
  have b2 := mul_le_mul_of_nonneg_left hB
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (pow_nonneg (sq_nonneg η) 2))
      (sq_nonneg ‖C‖))
  have e : (η ^ 2) ^ 2 = η ^ 4 := by ring
  rw [e] at b2
  linarith

/-- For `S = 𝒟` (resp. `ℬ`) the statements above are literally about `Spec.sD` (resp.
`Spec.sB`) of the next state, e.g. `𝔼[s_{t+1}^𝒟 | x_t] = Spec.EsNext N 𝒟`. -/
example (hζ : IsCenteredGaussian ζ C μ) (hC : C.PosSemidef) (hN : ∀ i, N.kap2 i = C i i)
    (η : ℝ) (c : ι → ℝ) :
    MemLp (fun ω => P.sD (P.cNext η c (ζ ω))) 2 μ ∧
      ∫ ω, P.sD (P.cNext η c (ζ ω)) ∂μ = P.EsNext N P.D η c ∧
      ∫ ω, P.sB (P.cNext η c (ζ ω)) ∂μ = P.EsNext N P.B η c :=
  ⟨P.memLp_sNext_of_isCenteredGaussian hζ hC P.D η c,
    P.integral_sNext_of_isCenteredGaussian N hζ hC hN P.D η c,
    P.integral_sNext_of_isCenteredGaussian N hζ hC hN P.B η c⟩

end Spec

/-! ## Non-vacuity of the hypotheses -/

/-- For every positive semidefinite `C` the hypotheses of the lemma are realised (on the
canonical probability space `(ℝ^ι, 𝒩(0, C))`), so the statements are not vacuous. -/
example (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (g d : ι → ℝ) :
    Var[fun x : EuclideanSpace ℝ ι => g ⬝ᵥ ofLp x; multivariateGaussian 0 C] = g ⬝ᵥ C *ᵥ g ∧
    Var[fun x : EuclideanSpace ℝ ι => ofLp x ⬝ᵥ diagonal d *ᵥ ofLp x; multivariateGaussian 0 C]
      = 2 * ((C * diagonal d) ^ 2).trace :=
  ⟨(isCenteredGaussian_ofLp C).variance_linear hC g,
    (isCenteredGaussian_ofLp C).variance_quadratic hC (isSymm_diagonal d)⟩

/-- The concrete model `z = M w` with independent standard normal `w_k` is realised on the
product space `(ℝ^κ, 𝒩(0,1)^{⊗κ})`. -/
example (M : Matrix ι κ ℝ) (g : ι → ℝ) :
    Var[fun y : κ → ℝ => g ⬝ᵥ (M *ᵥ y); stdNormalPi κ] = g ⬝ᵥ (M * Mᵀ) *ᵥ g :=
  (isCenteredGaussian_of_iIndepFun M iIndepFun_eval_stdNormalPi.1
    iIndepFun_eval_stdNormalPi.2).variance_linear (posSemidef_mul_transpose M) g

end SuspiciousAlignment
