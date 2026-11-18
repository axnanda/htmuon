import Mathlib
import SuspiciousAlignment.Defs

/-!
# The matrix-level setting of the paper is an instance of the eigenbasis setting

Formalization of Section 3.2 ("Setup and Assumptions", tex 303–366) and Appendix A.1
("Preliminaries, Notation, and Assumptions", tex 832–908) of

> Deng et al., *Suspicious Alignment of SGD: A Fine-Grained Step Size Condition Analysis*
> (arXiv:2601.11789v2).

The paper works with a symmetric positive definite Hessian `A ∈ ℝ^{d×d}`, a symmetric positive
semidefinite noise covariance `Σ`, a dominant dimension `0 < k < d` and the spectral decomposition
`A = U Λ Uᵀ`, `λ_1 ≥ … ≥ λ_k > λ_{k+1} ≥ … ≥ λ_d > 0`.  All later statements are phrased through the
eigen-coordinates `c_i = ⟪x, u_i⟫`, `ζ_i = ⟪ξ, u_i⟫`, `κ_i² = u_iᵀ Σ u_i`.  `Defs.lean` axiomatises
exactly that coordinate picture (`Spec ι`, `Noise ι`).  This file closes the loop: it builds the
coordinate picture from honest matrices, so that every theorem about `Spec`/`Noise` is a theorem
about matrices.  The file is linear algebra only (no probability, no `d → ∞`).

## Layout

* `SuspiciousAlignment.MatrixBridge` — **generic layer**.  For an arbitrary orthonormal basis `u`
  of `EuclideanSpace ℝ n` consisting of eigenvectors of `A` (`IsEigenbasis A u lam`; this is the
  paper's "`A = U Λ Uᵀ` with `U` orthonormal", see `IsEigenbasis.spectral`) we prove
  - coordinates (`coord u x i = ⟪x, u_i⟫`): `x = ∑ c_i u_i`, `‖x‖² = ∑ c_i²`,
    `‖A x‖² = ∑ λ_i² c_i²`, `xᵀ A x = ∑ λ_i c_i²`;
  - projectors `P^S = ∑_{i∈S} u_i u_iᵀ` (`proj u S`) and `P^S_{λ^p}` (`projPow`):
    `‖P^S A x‖² = ∑_{i∈S} λ_i² c_i²`, `‖P^S x‖² = ∑_{i∈S} c_i²`, projector algebra;
  - dynamics: the coordinates of `x - η (A x + ξ)` and of `x - η P^S (A x + ξ)`;
  - noise: `κ_i² = u_iᵀ Σ u_i = (Uᵀ Σ U)_{ii}`, `∑_i κ_i² = Tr Σ`, Rayleigh bounds;
  - uniqueness: an antitone eigenvalue list is *the* sorted eigenvalue list
    (`IsEigenbasis.eq_sortedEigenvalues`), and the projector `P^S` does not depend on the choice
    of the eigenbasis as soon as `S` is spectrally separated (`IsEigenbasis.proj_eq_proj`).
* `sortedEigenvalues`, `sortedEigenvectorBasis` — Mathlib's spectral theorem for Hermitian
  matrices, **re-indexed by `Fin d` so that the eigenvalues are sorted decreasingly**
  (`Matrix.IsHermitian.eigenvalues₀` is antitone on `Fin (Fintype.card (Fin d))`; Mathlib's
  `eigenvalues : Fin d → ℝ` goes through an arbitrary bijection and is *not* sorted).  The paper's
  1-based index `j ∈ {1,…,d}` is the 0-based `⟨j-1, _⟩ : Fin d`.
* `SuspiciousAlignment.MatrixSetting d` — **the paper's setting**: `A` positive definite, `Σ`
  positive semidefinite, `0 < k < d`, and the gap `λ_{k+1} < λ_k` between the `(k+1)`-th and
  `k`-th largest eigenvalue.  From it we construct `MatrixSetting.spec : Spec (Fin d)` (with
  `D = {i | i < k}`) and `MatrixSetting.noise : Noise (Fin d)` and prove the dictionary
  (`sD_coord`, `sB_coord`, `s_coord`, `theta_coord`, `loss_coord`, `coord_sgdStep`,
  `coord_projStep`, `noise_kap2`, `sum_kap2`, …).
* Non-vacuity: `MatrixSetting.ofDiagonal` (every sorted positive spectrum with a gap is realised by
  a diagonal matrix) and the concrete `4 × 4` instance `MatrixBridge.exampleSetting`
  (`A = diag(4,3,2,1)`, `Σ = I`, `k = 2`).

Vectors are elements of `EuclideanSpace ℝ (Fin d)` (so `‖·‖` is the Euclidean norm and `⟪·,·⟫_ℝ`
the dot product); a matrix `A` acts through Mathlib's `Matrix.toEuclideanLin A`, i.e.
`A.toEuclideanLin x = toLp 2 (A *ᵥ x)` (`Matrix.toLpLin_apply`).
-/

set_option linter.unusedSectionVars false

open Finset Matrix
open scoped InnerProductSpace

noncomputable section

namespace SuspiciousAlignment

namespace MatrixBridge

/-! ## Generic layer: an orthonormal eigenbasis -/

section Generic

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- `u` is an orthonormal basis of eigenvectors of `A` with eigenvalues `lam`:
`A u_i = λ_i u_i` for all `i`.  This is the paper's spectral decomposition `A = U Λ Uᵀ` with
`U = [u_1, …, u_d]` orthonormal (see `IsEigenbasis.spectral`). -/
def IsEigenbasis (A : Matrix n n ℝ) (u : OrthonormalBasis ι ℝ (EuclideanSpace ℝ n))
    (lam : ι → ℝ) : Prop :=
  ∀ i, A.toEuclideanLin (u i) = lam i • u i

/-- The eigen-coordinates `c_i = ⟪x, u_i⟫` of a vector `x` (paper §3.2). -/
def coord (u : OrthonormalBasis ι ℝ (EuclideanSpace ℝ n)) (x : EuclideanSpace ℝ n) : ι → ℝ :=
  fun i => ⟪x, u i⟫_ℝ

/-- The projector `P^S = ∑_{i∈S} u_i u_iᵀ` (paper §3.2), as a matrix. -/
def proj (u : OrthonormalBasis ι ℝ (EuclideanSpace ℝ n)) (S : Finset ι) : Matrix n n ℝ :=
  ∑ i ∈ S, vecMulVec (u i) (u i)

/-- The weighted projector `P^S_{λ^p} = ∑_{i∈S} λ_i^p u_i u_iᵀ` (Appendix A.1). -/
def projPow (u : OrthonormalBasis ι ℝ (EuclideanSpace ℝ n)) (lam : ι → ℝ) (S : Finset ι)
    (p : ℕ) : Matrix n n ℝ :=
  ∑ i ∈ S, lam i ^ p • vecMulVec (u i) (u i)

/-- The matrix `U = [u_1, …, u_d]` whose columns are the basis vectors. -/
def eigMatrix (u : OrthonormalBasis ι ℝ (EuclideanSpace ℝ n)) : Matrix n ι ℝ :=
  Matrix.of fun a i => u i a

/-- The per-direction noise variance `κ_i² = u_iᵀ Σ u_i` (paper §3.2). -/
def kap2 (u : OrthonormalBasis ι ℝ (EuclideanSpace ℝ n)) (Sig : Matrix n n ℝ) (i : ι) : ℝ :=
  ⟪u i, Sig.toEuclideanLin (u i)⟫_ℝ

variable (u : OrthonormalBasis ι ℝ (EuclideanSpace ℝ n))

/-! ### Coordinates -/

theorem coord_apply (x : EuclideanSpace ℝ n) (i : ι) : coord u x i = ⟪x, u i⟫_ℝ := rfl

/-- `coord` is Mathlib's `OrthonormalBasis.repr`. -/
theorem coord_eq_repr (x : EuclideanSpace ℝ n) (i : ι) : coord u x i = u.repr x i := by
  rw [u.repr_apply_apply, coord_apply, real_inner_comm]

@[simp] theorem coord_zero : coord u 0 = 0 := by
  funext i; simp [coord]

theorem coord_add (x y : EuclideanSpace ℝ n) : coord u (x + y) = coord u x + coord u y := by
  funext i; simp [coord, inner_add_left]

theorem coord_sub (x y : EuclideanSpace ℝ n) : coord u (x - y) = coord u x - coord u y := by
  funext i; simp [coord, inner_sub_left]

theorem coord_smul (a : ℝ) (x : EuclideanSpace ℝ n) : coord u (a • x) = a • coord u x := by
  funext i; simp [coord, inner_smul_left]

theorem coord_sum {κ : Type*} (s : Finset κ) (f : κ → EuclideanSpace ℝ n) :
    coord u (∑ j ∈ s, f j) = ∑ j ∈ s, coord u (f j) := by
  funext i; simp [coord, sum_inner]

/-- `⟪u_j, u_i⟫ = δ_{ij}`. -/
theorem coord_basis (i j : ι) : coord u (u j) i = if i = j then 1 else 0 := by
  rw [coord_apply, u.inner_eq_ite]
  simp [eq_comm]

/-- The eigen-expansion `x = ∑_i c_i u_i` (paper §3.2). -/
theorem sum_coord_smul (x : EuclideanSpace ℝ n) : ∑ i, coord u x i • u i = x := by
  simp_rw [coord_eq_repr]; exact u.sum_repr x

/-- The coordinates of `∑_j a_j u_j` are `a`. -/
theorem coord_sum_smul (a : ι → ℝ) : coord u (∑ j, a j • u j) = a := by
  funext i
  rw [coord_sum, Finset.sum_apply]
  simp [coord_smul, coord_basis]

/-- Parseval: `⟪x, y⟫ = ∑_i c_i(x) c_i(y)`. -/
theorem inner_eq_sum_coord (x y : EuclideanSpace ℝ n) :
    ⟪x, y⟫_ℝ = ∑ i, coord u x i * coord u y i := by
  rw [← u.sum_inner_mul_inner x y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coord_apply, coord_apply, real_inner_comm (u i) y]

/-- `‖x‖² = ∑_i c_i²`. -/
theorem norm_sq_eq_sum_coord (x : EuclideanSpace ℝ n) : ‖x‖ ^ 2 = ∑ i, coord u x i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_sum_coord u]
  simp [sq]

theorem coord_eq_zero_iff (x : EuclideanSpace ℝ n) : coord u x = 0 ↔ x = 0 := by
  constructor
  · intro h
    rw [← sum_coord_smul u x, h]
    simp
  · rintro rfl
    exact coord_zero u

theorem coord_injective : Function.Injective (coord u) := by
  intro x y h
  have : coord u (x - y) = 0 := by rw [coord_sub, h, sub_self]
  exact sub_eq_zero.mp ((coord_eq_zero_iff u _).mp this)

/-- Two matrices are equal as soon as their actions have the same coordinates. -/
theorem matrix_ext_of_coord {M N : Matrix n n ℝ}
    (h : ∀ x i, coord u (M.toEuclideanLin x) i = coord u (N.toEuclideanLin x) i) : M = N := by
  apply Matrix.toEuclideanLin.injective
  ext1 x
  exact coord_injective u (funext (h x))

/-- The Euclidean inner product is the dot product of the underlying coordinate vectors. -/
theorem inner_eq_sum_mul (x y : EuclideanSpace ℝ n) : ⟪x, y⟫_ℝ = ∑ a, x a * y a := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, mul_comm]

/-! ### The action of `A` in an eigenbasis -/

section Eigen

variable {u} {A : Matrix n n ℝ} {lam : ι → ℝ}

/-- `⟪A x, u_i⟫ = λ_i ⟪x, u_i⟫`: in eigen-coordinates `A` is `diag(λ)`. -/
theorem IsEigenbasis.coord_mulVec (h : IsEigenbasis A u lam) (x : EuclideanSpace ℝ n) (i : ι) :
    coord u (A.toEuclideanLin x) i = lam i * coord u x i := by
  conv_lhs => rw [← sum_coord_smul u x]
  simp only [map_sum, map_smul, h _, smul_smul]
  rw [coord_sum_smul]
  ring

/-- `‖A x‖² = ∑_i λ_i² c_i²` (paper §3.2, the denominator of `θ`). -/
theorem IsEigenbasis.norm_sq_mulVec (h : IsEigenbasis A u lam) (x : EuclideanSpace ℝ n) :
    ‖A.toEuclideanLin x‖ ^ 2 = ∑ i, lam i ^ 2 * coord u x i ^ 2 := by
  rw [norm_sq_eq_sum_coord u]
  exact Finset.sum_congr rfl fun i _ => by rw [h.coord_mulVec, mul_pow]

/-- `xᵀ A x = ∑_i λ_i c_i²`. -/
theorem IsEigenbasis.inner_mulVec (h : IsEigenbasis A u lam) (x : EuclideanSpace ℝ n) :
    ⟪x, A.toEuclideanLin x⟫_ℝ = ∑ i, lam i * coord u x i ^ 2 := by
  rw [inner_eq_sum_coord u]
  exact Finset.sum_congr rfl fun i _ => by rw [h.coord_mulVec]; ring

/-- Rayleigh lower bound: if all eigenvalues are `≥ a` then `a ‖x‖² ≤ xᵀ A x`. -/
theorem IsEigenbasis.le_inner_mulVec (h : IsEigenbasis A u lam) {a : ℝ} (ha : ∀ i, a ≤ lam i)
    (x : EuclideanSpace ℝ n) : a * ‖x‖ ^ 2 ≤ ⟪x, A.toEuclideanLin x⟫_ℝ := by
  rw [h.inner_mulVec, norm_sq_eq_sum_coord u, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (ha i) (sq_nonneg _)

/-- Rayleigh upper bound: if all eigenvalues are `≤ b` then `xᵀ A x ≤ b ‖x‖²`. -/
theorem IsEigenbasis.inner_mulVec_le (h : IsEigenbasis A u lam) {b : ℝ} (hb : ∀ i, lam i ≤ b)
    (x : EuclideanSpace ℝ n) : ⟪x, A.toEuclideanLin x⟫_ℝ ≤ b * ‖x‖ ^ 2 := by
  rw [h.inner_mulVec, norm_sq_eq_sum_coord u, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hb i) (sq_nonneg _)

/-- A matrix with an orthonormal eigenbasis (and real eigenvalues) is symmetric. -/
theorem IsEigenbasis.isHermitian (h : IsEigenbasis A u lam) : A.IsHermitian := by
  rw [← Matrix.isSymmetric_toEuclideanLin_iff]
  intro x y
  rw [inner_eq_sum_coord u, inner_eq_sum_coord u]
  exact Finset.sum_congr rfl fun i _ => by rw [h.coord_mulVec, h.coord_mulVec]; ring

/-- `u` is also an eigenbasis of `A ^ p`, with eigenvalues `λ_i ^ p`. -/
theorem IsEigenbasis.pow (h : IsEigenbasis A u lam) (p : ℕ) :
    IsEigenbasis (A ^ p) u (fun i => lam i ^ p) := by
  intro i
  induction p with
  | zero => simp
  | succ p ih =>
    rw [pow_succ, Matrix.toLpLin_mul_same, LinearMap.comp_apply, h i, map_smul, ih, smul_smul]
    show (lam i * lam i ^ p) • u i = lam i ^ (p + 1) • u i
    rw [pow_succ, mul_comm]

/-- Eigenvectors of two eigenbases of the same matrix that belong to different eigenvalues are
orthogonal. -/
theorem IsEigenbasis.inner_eq_zero_of_ne {κ : Type*} [Fintype κ] [DecidableEq κ]
    {v : OrthonormalBasis κ ℝ (EuclideanSpace ℝ n)} {mu : κ → ℝ}
    (hu : IsEigenbasis A u lam) (hv : IsEigenbasis A v mu) {i : ι} {j : κ}
    (hne : lam i ≠ mu j) : ⟪u i, v j⟫_ℝ = 0 := by
  have h1 := hv.coord_mulVec (u i) j
  rw [hu i, coord_smul] at h1
  simp only [Pi.smul_apply, smul_eq_mul] at h1
  have h2 : (lam i - mu j) * coord v (u i) j = 0 := by linarith
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact h

end Eigen

/-! ### The projectors `P^S` and `P^S_{λ^p}` -/

/-- `P^S y = ∑_{i∈S} ⟪y, u_i⟫ u_i`. -/
theorem proj_apply (S : Finset ι) (y : EuclideanSpace ℝ n) :
    (proj u S).toEuclideanLin y = ∑ i ∈ S, coord u y i • u i := by
  simp only [proj, map_sum, LinearMap.sum_apply, toLpLin_apply, vecMulVec_mulVec, op_smul_eq_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coord_apply, EuclideanSpace.inner_eq_star_dotProduct]
  simp

/-- `P^S` keeps the coordinates in `S` and kills the others. -/
theorem coord_proj (S : Finset ι) (y : EuclideanSpace ℝ n) (i : ι) :
    coord u ((proj u S).toEuclideanLin y) i = if i ∈ S then coord u y i else 0 := by
  rw [proj_apply, coord_sum, Finset.sum_apply]
  simp [coord_smul, coord_basis]

/-- `‖P^S y‖² = ∑_{i∈S} c_i(y)²`. -/
theorem norm_sq_proj (S : Finset ι) (y : EuclideanSpace ℝ n) :
    ‖(proj u S).toEuclideanLin y‖ ^ 2 = ∑ i ∈ S, coord u y i ^ 2 := by
  rw [norm_sq_eq_sum_coord u]
  simp_rw [coord_proj]
  simp [Finset.sum_ite_mem]

/-- `‖P^S A x‖² = ∑_{i∈S} λ_i² c_i²` (paper §3.2, the numerator of `θ` for `S = 𝒟`). -/
theorem IsEigenbasis.norm_sq_proj_mulVec {A : Matrix n n ℝ} {lam : ι → ℝ}
    (h : IsEigenbasis A u lam) (S : Finset ι) (x : EuclideanSpace ℝ n) :
    ‖(proj u S).toEuclideanLin (A.toEuclideanLin x)‖ ^ 2 = ∑ i ∈ S, lam i ^ 2 * coord u x i ^ 2 := by
  rw [norm_sq_proj]
  exact Finset.sum_congr rfl fun i _ => by rw [h.coord_mulVec, mul_pow]

theorem proj_basis (S : Finset ι) (i : ι) :
    (proj u S).toEuclideanLin (u i) = if i ∈ S then u i else 0 := by
  apply coord_injective u
  funext j
  rw [coord_proj, coord_basis]
  by_cases hi : i ∈ S <;> by_cases hj : j = i
  · subst hj; simp [hi, coord_basis]
  · simp [hi, hj, coord_basis]
  · subst hj; simp [hi]
  · simp [hi, hj]

@[simp] theorem proj_empty : proj u ∅ = 0 := by simp [proj]

/-- Completeness: `∑_i u_i u_iᵀ = I`. -/
@[simp] theorem proj_univ : proj u Finset.univ = 1 := by
  apply matrix_ext_of_coord u
  intro x i
  rw [coord_proj]
  simp

theorem proj_union {S T : Finset ι} (h : Disjoint S T) :
    proj u (S ∪ T) = proj u S + proj u T := by
  simp [proj, Finset.sum_union h]

/-- `P^S + P^{Sᶜ} = I` (in particular `P^𝒟 + P^ℬ = I`). -/
theorem proj_add_proj_compl (S : Finset ι) : proj u S + proj u Sᶜ = 1 := by
  rw [← proj_union u disjoint_compl_right, Finset.union_compl, proj_univ]

theorem proj_mul_proj (S T : Finset ι) : proj u S * proj u T = proj u (S ∩ T) := by
  apply matrix_ext_of_coord u
  intro x i
  rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply, coord_proj, coord_proj, coord_proj]
  simp only [Finset.mem_inter]
  split_ifs <;> simp_all

/-- `P^S` is idempotent. -/
theorem proj_mul_self (S : Finset ι) : proj u S * proj u S = proj u S := by
  rw [proj_mul_proj, Finset.inter_self]

/-- `P^S P^{Sᶜ} = 0` (in particular `P^𝒟 P^ℬ = 0`). -/
theorem proj_mul_proj_compl (S : Finset ι) : proj u S * proj u Sᶜ = 0 := by
  rw [proj_mul_proj, Finset.inter_compl, proj_empty]

/-- `P^S` is symmetric. -/
theorem proj_transpose (S : Finset ι) : (proj u S)ᵀ = proj u S := by
  simp [proj, transpose_sum, transpose_vecMulVec]

theorem projPow_apply (lam : ι → ℝ) (S : Finset ι) (p : ℕ) (y : EuclideanSpace ℝ n) :
    (projPow u lam S p).toEuclideanLin y = ∑ i ∈ S, (lam i ^ p * coord u y i) • u i := by
  simp only [projPow, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, toLpLin_apply,
    vecMulVec_mulVec, op_smul_eq_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coord_apply, EuclideanSpace.inner_eq_star_dotProduct]
  simp [smul_smul]

theorem coord_projPow (lam : ι → ℝ) (S : Finset ι) (p : ℕ) (y : EuclideanSpace ℝ n) (i : ι) :
    coord u ((projPow u lam S p).toEuclideanLin y) i =
      if i ∈ S then lam i ^ p * coord u y i else 0 := by
  rw [projPow_apply, coord_sum, Finset.sum_apply]
  simp [coord_smul, coord_basis]

/-- `xᵀ P^S_{λ^p} x = ∑_{i∈S} λ_i^p c_i²` (the block moments `Spec.mom`). -/
theorem inner_projPow (lam : ι → ℝ) (S : Finset ι) (p : ℕ) (x : EuclideanSpace ℝ n) :
    ⟪x, (projPow u lam S p).toEuclideanLin x⟫_ℝ = ∑ i ∈ S, lam i ^ p * coord u x i ^ 2 := by
  rw [inner_eq_sum_coord u]
  simp_rw [coord_projPow, mul_ite, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  exact Finset.sum_congr rfl fun i _ => by ring

@[simp] theorem projPow_zero (lam : ι → ℝ) (S : Finset ι) : projPow u lam S 0 = proj u S := by
  simp [projPow, proj]

/-- `P^S_{λ^p} = P^S A^p`. -/
theorem IsEigenbasis.projPow_eq {A : Matrix n n ℝ} {lam : ι → ℝ} (h : IsEigenbasis A u lam)
    (S : Finset ι) (p : ℕ) : projPow u lam S p = proj u S * A ^ p := by
  apply matrix_ext_of_coord u
  intro x i
  rw [coord_projPow, Matrix.toLpLin_mul_same, LinearMap.comp_apply, coord_proj,
    (h.pow p).coord_mulVec]

/-- `P^S` commutes with `A`. -/
theorem IsEigenbasis.proj_mul_comm {A : Matrix n n ℝ} {lam : ι → ℝ} (h : IsEigenbasis A u lam)
    (S : Finset ι) : proj u S * A = A * proj u S := by
  apply matrix_ext_of_coord u
  intro x i
  rw [Matrix.toLpLin_mul_same, Matrix.toLpLin_mul_same, LinearMap.comp_apply, LinearMap.comp_apply,
    coord_proj, h.coord_mulVec, h.coord_mulVec, coord_proj]
  split_ifs <;> simp

/-- **The projector does not depend on the choice of the eigenbasis.**  If `u` (eigenvalues `lam`)
and `v` (eigenvalues `mu`) are two orthonormal eigenbases of `A` and the index sets `S`, `T` select
the same part of the spectrum (no eigenvalue of `S` occurs outside `T` and none of `T` outside `S`),
then `∑_{i∈S} u_i u_iᵀ = ∑_{j∈T} v_j v_jᵀ`. -/
theorem IsEigenbasis.proj_eq_proj {A : Matrix n n ℝ} {lam : ι → ℝ} {κ : Type*} [Fintype κ]
    [DecidableEq κ] {v : OrthonormalBasis κ ℝ (EuclideanSpace ℝ n)} {mu : κ → ℝ}
    (hu : IsEigenbasis A u lam) (hv : IsEigenbasis A v mu) {S : Finset ι} {T : Finset κ}
    (h1 : ∀ i ∈ S, ∀ j ∉ T, lam i ≠ mu j) (h2 : ∀ i ∉ S, ∀ j ∈ T, lam i ≠ mu j) :
    proj u S = proj v T := by
  apply Matrix.toEuclideanLin.injective
  apply u.toBasis.ext
  intro i
  rw [OrthonormalBasis.coe_toBasis, proj_basis, proj_apply]
  by_cases hi : i ∈ S
  · simp only [hi, ite_true]
    conv_lhs => rw [← sum_coord_smul v (u i)]
    symm
    apply Finset.sum_subset (Finset.subset_univ T)
    intro j _ hj
    rw [coord_apply, hu.inner_eq_zero_of_ne hv (h1 i hi j hj), zero_smul]
  · simp only [hi, ite_false]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    rw [coord_apply, hu.inner_eq_zero_of_ne hv (h2 i hi j hj), zero_smul]

/-! ### The matrix `U` of eigenvectors: `A = U Λ Uᵀ`, `C = Uᵀ Σ U` -/

theorem eigMatrix_apply (a : n) (i : ι) : eigMatrix u a i = u i a := rfl

/-- `Uᵀ U = I` (orthonormality). -/
theorem eigMatrix_transpose_mul_self : (eigMatrix u)ᵀ * eigMatrix u = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply, ← u.inner_eq_ite, inner_eq_sum_mul]
  rfl

/-- `U Uᵀ = I` (completeness). -/
theorem eigMatrix_mul_transpose_self : eigMatrix u * (eigMatrix u)ᵀ = 1 := by
  ext a b
  have h := u.sum_inner_mul_inner (EuclideanSpace.single a (1 : ℝ))
    (EuclideanSpace.single b (1 : ℝ))
  simp only [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right] at h
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.transpose_apply, eigMatrix_apply]
  simpa [Pi.single_apply, eq_comm] using h

/-- `(Uᵀ M U)_{ij} = ⟪u_i, M u_j⟫`: the matrix of `M` in the basis `u`. -/
theorem eigMatrix_conj_apply (M : Matrix n n ℝ) (i j : ι) :
    ((eigMatrix u)ᵀ * M * eigMatrix u) i j = ⟪u i, M.toEuclideanLin (u j)⟫_ℝ := by
  rw [inner_eq_sum_mul, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, eigMatrix_apply, toLpLin_apply, mulVec,
    dotProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- `Uᵀ A U = Λ`. -/
theorem IsEigenbasis.eigMatrix_conj {A : Matrix n n ℝ} {lam : ι → ℝ} (h : IsEigenbasis A u lam) :
    (eigMatrix u)ᵀ * A * eigMatrix u = diagonal lam := by
  ext i j
  rw [eigMatrix_conj_apply, h j, inner_smul_right, u.inner_eq_ite, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

/-- **The spectral decomposition `A = U Λ Uᵀ`** of the paper (§3.2) is equivalent to our
hypothesis `IsEigenbasis A u lam`; this is the direction used to read the paper. -/
theorem IsEigenbasis.spectral {A : Matrix n n ℝ} {lam : ι → ℝ} (h : IsEigenbasis A u lam) :
    A = eigMatrix u * diagonal lam * (eigMatrix u)ᵀ := by
  rw [← h.eigMatrix_conj]
  simp only [Matrix.mul_assoc]
  rw [eigMatrix_mul_transpose_self, Matrix.mul_one, ← Matrix.mul_assoc,
    eigMatrix_mul_transpose_self, Matrix.one_mul]

/-! ### Dynamics in eigen-coordinates -/

/-- One SGD step `x⁺ = x - η (A x + ξ)` in eigen-coordinates (Appendix A.2):
`c_i⁺ = (1 - η λ_i) c_i - η ζ_i` with `ζ_i = ⟪ξ, u_i⟫`. -/
theorem IsEigenbasis.coord_sgdStep {A : Matrix n n ℝ} {lam : ι → ℝ} (h : IsEigenbasis A u lam)
    (η : ℝ) (x ξ : EuclideanSpace ℝ n) (i : ι) :
    coord u (x - η • (A.toEuclideanLin x + ξ)) i =
      (1 - η * lam i) * coord u x i - η * coord u ξ i := by
  rw [coord_sub, coord_smul, coord_add]
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, h.coord_mulVec]
  ring

/-- One projected SGD step `x⁺ = x - η P^S (A x + ξ)` in eigen-coordinates (paper eq. (3)–(4)):
coordinates in `S` move as in SGD, the others are frozen. -/
theorem IsEigenbasis.coord_projStep {A : Matrix n n ℝ} {lam : ι → ℝ} (h : IsEigenbasis A u lam)
    (S : Finset ι) (η : ℝ) (x ξ : EuclideanSpace ℝ n) (i : ι) :
    coord u (x - η • (proj u S).toEuclideanLin (A.toEuclideanLin x + ξ)) i =
      if i ∈ S then (1 - η * lam i) * coord u x i - η * coord u ξ i else coord u x i := by
  rw [coord_sub, coord_smul]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, coord_proj, coord_add, Pi.add_apply,
    h.coord_mulVec]
  split_ifs <;> ring

/-! ### Noise in an orthonormal basis -/

/-- `κ_i² = u_iᵀ Σ u_i`, written with the dot product. -/
theorem kap2_eq_dotProduct (Sig : Matrix n n ℝ) (i : ι) :
    kap2 u Sig i = (u i).ofLp ⬝ᵥ Sig *ᵥ (u i).ofLp := by
  rw [kap2, EuclideanSpace.inner_eq_star_dotProduct]
  simp [toLpLin_apply, dotProduct_comm]

/-- `κ_i² = (C)_{ii}` with `C = Uᵀ Σ U` (paper §3.2). -/
theorem kap2_eq_diag (Sig : Matrix n n ℝ) (i : ι) :
    kap2 u Sig i = ((eigMatrix u)ᵀ * Sig * eigMatrix u) i i :=
  (eigMatrix_conj_apply u Sig i i).symm

/-- `∑_i κ_i² = Tr Σ` (the trace does not depend on the orthonormal basis). -/
theorem sum_kap2 (Sig : Matrix n n ℝ) : ∑ i, kap2 u Sig i = Sig.trace := by
  unfold kap2
  rw [← LinearMap.trace_eq_sum_inner, Matrix.toEuclideanLin_eq_toLin_orthonormal,
    Matrix.trace_toLin_eq]

/-- `∑_{i∈S} λ_i^p κ_i² = Tr(Σ P^S_{λ^p})`. -/
theorem sum_pow_mul_kap2 (lam : ι → ℝ) (S : Finset ι) (p : ℕ) (Sig : Matrix n n ℝ) :
    ∑ i ∈ S, lam i ^ p * kap2 u Sig i = (Sig * projPow u lam S p).trace := by
  simp only [projPow, Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul,
    mul_vecMulVec, trace_vecMulVec, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kap2_eq_dotProduct, dotProduct_comm]

/-- `κ_i² ≥ 0` for a positive semidefinite `Σ`. -/
theorem kap2_nonneg {Sig : Matrix n n ℝ} (hSig : Sig.PosSemidef) (i : ι) : 0 ≤ kap2 u Sig i := by
  rw [kap2_eq_dotProduct]
  simpa using hSig.dotProduct_mulVec_nonneg (u i).ofLp

/-- If all eigenvalues of `Σ` are `≥ a`, then `a ≤ κ_i² = u_iᵀ Σ u_i` (as `‖u_i‖ = 1`). -/
theorem le_kap2 {κ : Type*} [Fintype κ] [DecidableEq κ] {Sig : Matrix n n ℝ}
    {v : OrthonormalBasis κ ℝ (EuclideanSpace ℝ n)} {mu : κ → ℝ} (h : IsEigenbasis Sig v mu)
    {a : ℝ} (ha : ∀ j, a ≤ mu j) (i : ι) : a ≤ kap2 u Sig i := by
  have h1 := h.le_inner_mulVec ha (u i)
  rwa [u.norm_eq_one, one_pow, mul_one] at h1

/-- If all eigenvalues of `Σ` are `≤ b`, then `κ_i² = u_iᵀ Σ u_i ≤ b` (as `‖u_i‖ = 1`). -/
theorem kap2_le {κ : Type*} [Fintype κ] [DecidableEq κ] {Sig : Matrix n n ℝ}
    {v : OrthonormalBasis κ ℝ (EuclideanSpace ℝ n)} {mu : κ → ℝ} (h : IsEigenbasis Sig v mu)
    {b : ℝ} (hb : ∀ j, mu j ≤ b) (i : ι) : kap2 u Sig i ≤ b := by
  have h1 := h.inner_mulVec_le hb (u i)
  rwa [u.norm_eq_one, one_pow, mul_one] at h1

/-- For `Σ = I` every direction has unit variance: `u_iᵀ u_i = 1`. -/
theorem kap2_one (i : ι) : kap2 u (1 : Matrix n n ℝ) i = 1 := by
  rw [kap2, Matrix.toLpLin_one, LinearMap.id_apply, real_inner_self_eq_norm_sq, u.norm_eq_one,
    one_pow]

/-- `Tr(P^S_{λ^p}) = ∑_{i∈S} λ_i^p` (in particular `ψ_S = Tr(P^S_{λ²})`). -/
theorem trace_projPow (lam : ι → ℝ) (S : Finset ι) (p : ℕ) :
    (projPow u lam S p).trace = ∑ i ∈ S, lam i ^ p := by
  have h := sum_pow_mul_kap2 u lam S p (1 : Matrix n n ℝ)
  simp only [kap2_one, mul_one, Matrix.one_mul] at h
  exact h.symm

/-! ### Characteristic polynomial -/

/-- If `u` is an orthonormal eigenbasis of `A` with eigenvalues `lam`, the characteristic
polynomial of `A` is `∏_i (X - λ_i)`. -/
theorem IsEigenbasis.charpoly_eq {A : Matrix n n ℝ}
    {u : OrthonormalBasis n ℝ (EuclideanSpace ℝ n)} {lam : n → ℝ} (h : IsEigenbasis A u lam) :
    A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (lam i)) := by
  have h1 : A.charpoly = (diagonal lam).charpoly := by
    conv_lhs =>
      rw [h.spectral, Matrix.mul_assoc, Matrix.charpoly_mul_comm, Matrix.mul_assoc,
        eigMatrix_transpose_mul_self, Matrix.mul_one]
  rw [h1, Matrix.charpoly_diagonal]

/-- The multiset of roots of the characteristic polynomial is the multiset of the `λ_i`. -/
theorem IsEigenbasis.roots_charpoly {A : Matrix n n ℝ}
    {u : OrthonormalBasis n ℝ (EuclideanSpace ℝ n)} {lam : n → ℝ} (h : IsEigenbasis A u lam) :
    A.charpoly.roots = Finset.univ.val.map lam := by
  rw [h.charpoly_eq, Polynomial.roots_prod]
  · simp
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

/-- A diagonal matrix has the standard basis as eigenbasis. -/
theorem isEigenbasis_diagonal (w : n → ℝ) :
    IsEigenbasis (diagonal w) (EuclideanSpace.basisFun n ℝ) w := by
  intro i
  rw [EuclideanSpace.basisFun_apply, toLpLin_apply]
  ext j
  simp [Pi.single_apply]

end Generic

/-! ## Mathlib's spectral theorem, re-indexed so that eigenvalues are sorted -/

section Sorted

variable {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}

/-- The bijection `Fin d ≃ Fin d` that turns Mathlib's (arbitrarily indexed)
`Matrix.IsHermitian.eigenvalues`/`eigenvectorBasis` into the decreasingly sorted ones. -/
def sortEquiv (d : ℕ) : Fin d ≃ Fin d :=
  (finCongr (Fintype.card_fin d).symm).trans (Fintype.equivOfCardEq (Fintype.card_fin _))

/-- The eigenvalues of a symmetric matrix `A : Matrix (Fin d) (Fin d) ℝ`, **sorted decreasingly**:
`sortedEigenvalues hA ⟨j, _⟩` is the `(j+1)`-th largest eigenvalue (with multiplicity), i.e. the
paper's `λ_{j+1}`.  This is Mathlib's `Matrix.IsHermitian.eigenvalues₀` transported along
`Fin d ≃ Fin (Fintype.card (Fin d))`. -/
def sortedEigenvalues (hA : A.IsHermitian) : Fin d → ℝ :=
  fun i => hA.eigenvalues₀ (Fin.cast (Fintype.card_fin d).symm i)

/-- The orthonormal eigenvector basis matching `sortedEigenvalues` (the paper's `u_1, …, u_d`). -/
def sortedEigenvectorBasis (hA : A.IsHermitian) :
    OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
  hA.eigenvectorBasis.reindex (sortEquiv d).symm

theorem sortedEigenvalues_eq (hA : A.IsHermitian) (i : Fin d) :
    sortedEigenvalues hA i = hA.eigenvalues (sortEquiv d i) := by
  simp [sortedEigenvalues, sortEquiv, Matrix.IsHermitian.eigenvalues]

theorem sortedEigenvectorBasis_apply (hA : A.IsHermitian) (i : Fin d) :
    sortedEigenvectorBasis hA i = hA.eigenvectorBasis (sortEquiv d i) := by
  simp [sortedEigenvectorBasis]

/-- `λ_1 ≥ λ_2 ≥ … ≥ λ_d`. -/
theorem sortedEigenvalues_antitone (hA : A.IsHermitian) : Antitone (sortedEigenvalues hA) :=
  fun _ _ hij => hA.eigenvalues₀_antitone (by simpa using hij)

/-- The sorted eigen-decomposition is an eigen-decomposition: `A u_i = λ_i u_i`. -/
theorem isEigenbasis_sorted (hA : A.IsHermitian) :
    IsEigenbasis A (sortedEigenvectorBasis hA) (sortedEigenvalues hA) := by
  intro i
  rw [sortedEigenvectorBasis_apply, sortedEigenvalues_eq, toLpLin_apply,
    hA.mulVec_eigenvectorBasis]
  rfl

theorem range_sortedEigenvalues (hA : A.IsHermitian) :
    Set.range (sortedEigenvalues hA) = spectrum ℝ A := by
  rw [hA.spectrum_real_eq_range_eigenvalues]
  have : sortedEigenvalues hA = hA.eigenvalues ∘ sortEquiv d :=
    funext fun i => sortedEigenvalues_eq hA i
  rw [this, EquivLike.range_comp]

/-- `λ_1` (index `0`) is the largest element of the spectrum of `A`. -/
theorem isGreatest_sortedEigenvalues (hA : A.IsHermitian) (hd : 0 < d) :
    IsGreatest (spectrum ℝ A) (sortedEigenvalues hA ⟨0, hd⟩) := by
  rw [← range_sortedEigenvalues hA]
  refine ⟨Set.mem_range_self _, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact sortedEigenvalues_antitone hA (Fin.le_def.mpr (Nat.zero_le _))

/-- `λ_d` (index `d - 1`) is the smallest element of the spectrum of `A`. -/
theorem isLeast_sortedEigenvalues (hA : A.IsHermitian) (hd : 0 < d) :
    IsLeast (spectrum ℝ A) (sortedEigenvalues hA ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩) := by
  rw [← range_sortedEigenvalues hA]
  refine ⟨Set.mem_range_self _, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact sortedEigenvalues_antitone hA (Fin.le_def.mpr (Nat.le_sub_one_of_lt i.isLt))

theorem sortedEigenvalues_pos (hA : A.PosDef) (i : Fin d) :
    0 < sortedEigenvalues hA.isHermitian i := by
  rw [sortedEigenvalues_eq]
  exact hA.eigenvalues_pos _

theorem sortedEigenvalues_nonneg (hA : A.PosSemidef) (i : Fin d) :
    0 ≤ sortedEigenvalues hA.isHermitian i := by
  rw [sortedEigenvalues_eq]
  exact hA.eigenvalues_nonneg _

/-- The sorted eigenvalues are exactly the roots of the characteristic polynomial, counted with
multiplicity. -/
theorem roots_charpoly_eq_sortedEigenvalues (hA : A.IsHermitian) :
    A.charpoly.roots = (List.ofFn (sortedEigenvalues hA) : Multiset ℝ) := by
  rw [(isEigenbasis_sorted hA).roots_charpoly, Fin.univ_val_map]

/-- **Uniqueness of the sorted spectrum.**  If `u` is *any* orthonormal eigenbasis of `A` whose
eigenvalues `lam` are listed decreasingly (the paper's `A = U Λ Uᵀ`, `λ_1 ≥ … ≥ λ_d`), then `lam`
is `sortedEigenvalues`. -/
theorem IsEigenbasis.eq_sortedEigenvalues {u : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))}
    {lam : Fin d → ℝ} (h : IsEigenbasis A u lam) (hlam : Antitone lam) (hA : A.IsHermitian) :
    lam = sortedEigenvalues hA := by
  have h2 := roots_charpoly_eq_sortedEigenvalues hA
  rw [h.roots_charpoly, Fin.univ_val_map, Multiset.coe_eq_coe] at h2
  exact List.ofFn_injective
    (h2.eq_of_sortedGE hlam.sortedGE_ofFn (sortedEigenvalues_antitone hA).sortedGE_ofFn)

/-- The sorted eigenvalues of `diag(w)` with `w` decreasing are `w`. -/
theorem sortedEigenvalues_diagonal {w : Fin d → ℝ} (hw : Antitone w)
    (h : (diagonal w).IsHermitian) : sortedEigenvalues h = w :=
  ((isEigenbasis_diagonal w).eq_sortedEigenvalues hw h).symm

end Sorted

end MatrixBridge

open MatrixBridge

/-! ## The matrix-level setting of the paper -/

/-- **The setting of the paper** (§3.2, Appendix A.1): a symmetric positive definite Hessian
`A ∈ ℝ^{d×d}`, a symmetric positive semidefinite noise covariance `Σ`, and a dominant dimension
`k ∈ {1, …, d-1}` such that the `k`-th largest eigenvalue of `A` is strictly larger than the
`(k+1)`-th: `λ_1 ≥ … ≥ λ_k > λ_{k+1} ≥ … ≥ λ_d > 0`.  (Indices are 0-based in Lean: the paper's
`λ_j` is `sortedEigenvalues _ ⟨j - 1, _⟩`.) -/
structure MatrixSetting (d : ℕ) where
  /-- the Hessian `A` of the quadratic loss `L(x) = ½ xᵀ A x` -/
  A : Matrix (Fin d) (Fin d) ℝ
  /-- the covariance `Σ` of the SGD noise -/
  Sigma : Matrix (Fin d) (Fin d) ℝ
  /-- the dominant dimension `k` -/
  k : ℕ
  /-- `A` is symmetric positive definite -/
  A_posDef : A.PosDef
  /-- `Σ = Σᵀ ⪰ 0` -/
  Sigma_posSemidef : Sigma.PosSemidef
  /-- `1 ≤ k` -/
  k_pos : 0 < k
  /-- `k ≤ d - 1` -/
  k_lt : k < d
  /-- the spectral gap `λ_{k+1} < λ_k`, i.e. `gap₁ > 0` -/
  gap : sortedEigenvalues A_posDef.isHermitian ⟨k, k_lt⟩ <
    sortedEigenvalues A_posDef.isHermitian ⟨k - 1, lt_of_le_of_lt (Nat.sub_le k 1) k_lt⟩

namespace MatrixSetting

variable {d : ℕ} (M : MatrixSetting d)

include M in
theorem d_pos : 0 < d := lt_trans M.k_pos M.k_lt

theorem A_isHermitian : M.A.IsHermitian := M.A_posDef.isHermitian

theorem Sigma_isHermitian : M.Sigma.IsHermitian := M.Sigma_posSemidef.isHermitian

/-! ### Spectral data of `A` -/

/-- The eigenvalues `λ_1 ≥ … ≥ λ_d` of `A` (0-based: `M.lam ⟨j-1, _⟩` is the paper's `λ_j`). -/
def lam : Fin d → ℝ := sortedEigenvalues M.A_isHermitian

/-- The orthonormal eigenvectors `u_1, …, u_d` of `A` (the columns of `U`). -/
def u : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
  sortedEigenvectorBasis M.A_isHermitian

/-- `A u_i = λ_i u_i`. -/
theorem isEigenbasis : IsEigenbasis M.A M.u M.lam := isEigenbasis_sorted M.A_isHermitian

/-- `λ_1 ≥ λ_2 ≥ … ≥ λ_d`. -/
theorem lam_antitone : Antitone M.lam := sortedEigenvalues_antitone M.A_isHermitian

/-- `λ_i > 0` (`A` is positive definite). -/
theorem lam_pos (i : Fin d) : 0 < M.lam i := sortedEigenvalues_pos M.A_posDef i

/-- The paper's spectral decomposition `A = U Λ Uᵀ` (§3.2). -/
theorem A_eq : M.A = eigMatrix M.u * diagonal M.lam * (eigMatrix M.u)ᵀ := M.isEigenbasis.spectral

/-- `U` is orthogonal. -/
theorem U_orthogonal :
    (eigMatrix M.u)ᵀ * eigMatrix M.u = 1 ∧ eigMatrix M.u * (eigMatrix M.u)ᵀ = 1 :=
  ⟨eigMatrix_transpose_mul_self M.u, eigMatrix_mul_transpose_self M.u⟩

/-- Index of the paper's `λ_1`. -/
def idx1 : Fin d := ⟨0, M.d_pos⟩
/-- Index of the paper's `λ_k`. -/
def idxk : Fin d := ⟨M.k - 1, lt_of_le_of_lt (Nat.sub_le M.k 1) M.k_lt⟩
/-- Index of the paper's `λ_{k+1}`. -/
def idxk1 : Fin d := ⟨M.k, M.k_lt⟩
/-- Index of the paper's `λ_d`. -/
def idxd : Fin d := ⟨d - 1, Nat.sub_lt M.d_pos Nat.one_pos⟩

/-- **The abstract spectrum `Spec (Fin d)` of the matrix setting**: `lam` are the decreasingly
sorted eigenvalues of `A`, the dominant block is `𝒟 = {i | i < k}` (the paper's `{1, …, k}`), and
`λ_1, λ_k, λ_{k+1}, λ_d` sit at the indices `0, k-1, k, d-1`. -/
def spec : Spec (Fin d) where
  lam := M.lam
  D := Finset.univ.filter fun i : Fin d => (i : ℕ) < M.k
  i1 := M.idx1
  ik := M.idxk
  ik1 := M.idxk1
  id := M.idxd
  i1_mem := Finset.mem_filter.mpr ⟨Finset.mem_univ _, M.k_pos⟩
  ik_mem := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.sub_lt M.k_pos Nat.one_pos⟩
  ik1_not_mem := fun h => lt_irrefl _ (Finset.mem_filter.mp h).2
  id_not_mem := fun h => by
    have h1 : d - 1 < M.k := (Finset.mem_filter.mp h).2
    have h2 := M.k_lt
    omega
  lam_pos := M.lam_pos
  le_lam1 := fun i _ => M.lam_antitone (Fin.le_def.mpr (Nat.zero_le _))
  lamk_le := fun i hi =>
    M.lam_antitone (Fin.le_def.mpr (Nat.le_sub_one_of_lt (Finset.mem_filter.mp hi).2))
  le_lamk1 := fun i hi =>
    M.lam_antitone (Fin.le_def.mpr (not_lt.mp fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)))
  lamd_le := fun i _ => M.lam_antitone (Fin.le_def.mpr (Nat.le_sub_one_of_lt i.isLt))
  gap := M.gap

/-! ### What `M.spec` is: the dictionary for the spectrum -/

@[simp] theorem spec_lam : M.spec.lam = M.lam := rfl

theorem spec_D : M.spec.D = Finset.univ.filter fun i : Fin d => (i : ℕ) < M.k := rfl

/-- `𝒟 = {1, …, k}` (0-based: `{0, …, k-1}`). -/
theorem mem_spec_D {i : Fin d} : i ∈ M.spec.D ↔ (i : ℕ) < M.k := by
  simp [spec_D]

/-- `ℬ = {k+1, …, d}` (0-based: `{k, …, d-1}`). -/
theorem mem_spec_B {i : Fin d} : i ∈ M.spec.B ↔ M.k ≤ (i : ℕ) := by
  rw [Spec.mem_B, mem_spec_D, not_lt]

/-- `M.spec.lam1` is the paper's `λ_1`: the 1st entry of the decreasingly sorted spectrum. -/
theorem spec_lam1 : M.spec.lam1 = sortedEigenvalues M.A_isHermitian ⟨0, M.d_pos⟩ := rfl

/-- `M.spec.lamk` is the paper's `λ_k`: the `k`-th entry of the decreasingly sorted spectrum. -/
theorem spec_lamk : M.spec.lamk =
    sortedEigenvalues M.A_isHermitian ⟨M.k - 1, lt_of_le_of_lt (Nat.sub_le M.k 1) M.k_lt⟩ := rfl

/-- `M.spec.lamk1` is the paper's `λ_{k+1}`. -/
theorem spec_lamk1 : M.spec.lamk1 = sortedEigenvalues M.A_isHermitian ⟨M.k, M.k_lt⟩ := rfl

/-- `M.spec.lamd` is the paper's `λ_d`: the last entry of the decreasingly sorted spectrum. -/
theorem spec_lamd : M.spec.lamd =
    sortedEigenvalues M.A_isHermitian ⟨d - 1, Nat.sub_lt M.d_pos Nat.one_pos⟩ := rfl

/-- `λ_1 = λ_max(A)`. -/
theorem spec_lam1_isGreatest : IsGreatest (spectrum ℝ M.A) M.spec.lam1 :=
  isGreatest_sortedEigenvalues M.A_isHermitian M.d_pos

/-- `λ_d = λ_min(A)`. -/
theorem spec_lamd_isLeast : IsLeast (spectrum ℝ M.A) M.spec.lamd :=
  isLeast_sortedEigenvalues M.A_isHermitian M.d_pos

/-- The eigenvalues `λ_1, …, λ_d` are the roots of the characteristic polynomial of `A`, with
multiplicity; together with `lam_antitone` this pins down `M.lam` as *the* decreasing enumeration
of the spectrum, so `M.lam ⟨j-1, _⟩` is the `j`-th largest eigenvalue. -/
theorem roots_charpoly : M.A.charpoly.roots = (List.ofFn M.lam : Multiset ℝ) :=
  roots_charpoly_eq_sortedEigenvalues M.A_isHermitian

/-- The dominant block is determined by the spectrum alone: `i ∈ 𝒟 ↔ λ_i ≥ λ_k`. -/
theorem mem_spec_D_iff_lamk_le {i : Fin d} : i ∈ M.spec.D ↔ M.spec.lamk ≤ M.lam i := by
  constructor
  · exact fun hi => M.spec.lamk_le i hi
  · intro h
    by_contra hi
    have h1 : M.lam i ≤ M.spec.lamk1 := M.spec.le_lamk1 i hi
    have h2 : M.spec.lamk1 < M.spec.lamk := M.spec.gap
    linarith

/-- The bulk block is determined by the spectrum alone: `i ∈ ℬ ↔ λ_i ≤ λ_{k+1}`. -/
theorem mem_spec_B_iff_le_lamk1 {i : Fin d} : i ∈ M.spec.B ↔ M.lam i ≤ M.spec.lamk1 := by
  rw [Spec.mem_B]
  constructor
  · exact fun hi => M.spec.le_lamk1 i hi
  · intro h hi
    have h1 : M.spec.lamk ≤ M.lam i := M.spec.lamk_le i hi
    have h2 : M.spec.lamk1 < M.spec.lamk := M.spec.gap
    linarith

/-- `|𝒟| = k`. -/
theorem card_spec_D : M.spec.D.card = M.k := by
  have h : M.spec.D = Finset.Iio (⟨M.k, M.k_lt⟩ : Fin d) := by
    ext i
    rw [mem_spec_D, Finset.mem_Iio, Fin.lt_def]
  rw [h, Fin.card_Iio]

/-- `|ℬ| = d - k`. -/
theorem card_spec_B : M.spec.B.card = d - M.k := by
  rw [Spec.B, Finset.card_compl, card_spec_D, Fintype.card_fin]

theorem spec_kR : M.spec.kR = (M.k : ℝ) := by rw [Spec.kR, card_spec_D]

theorem spec_dkR : M.spec.dkR = (d : ℝ) - (M.k : ℝ) := by
  rw [Spec.dkR, card_spec_B, Nat.cast_sub M.k_lt.le]

/-- The block proportion `ρ = k / (d - k)` (Assumption 1, "Block proportion"). -/
theorem spec_rho : M.spec.rho = (M.k : ℝ) / ((d : ℝ) - (M.k : ℝ)) := by
  rw [Spec.rho, spec_kR, spec_dkR]

/-- "Which implies `k = ρ/(1+ρ) · d`" (Assumption 1, "Block proportion"). -/
theorem k_eq_rho_mul_d : (M.k : ℝ) = M.spec.rho / (1 + M.spec.rho) * (d : ℝ) := by
  rw [spec_rho]
  have h : (0 : ℝ) < (d : ℝ) - (M.k : ℝ) := sub_pos.mpr (by exact_mod_cast M.k_lt)
  have hd : (0 : ℝ) < (d : ℝ) := by exact_mod_cast M.d_pos
  field_simp
  ring

/-! ### The noise: `κ_i² = u_iᵀ Σ u_i`, `s_min = λ_min(Σ)`, `s_max = λ_max(Σ)` -/

/-- `s_min := λ_min(Σ)`, the smallest eigenvalue of the noise covariance. -/
def smin : ℝ := sortedEigenvalues M.Sigma_isHermitian M.idxd

/-- `s_max := λ_max(Σ)`, the largest eigenvalue of the noise covariance. -/
def smax : ℝ := sortedEigenvalues M.Sigma_isHermitian M.idx1

/-- `s_min` is the least element of the spectrum of `Σ`. -/
theorem smin_isLeast : IsLeast (spectrum ℝ M.Sigma) M.smin :=
  isLeast_sortedEigenvalues M.Sigma_isHermitian M.d_pos

/-- `s_max` is the greatest element of the spectrum of `Σ`. -/
theorem smax_isGreatest : IsGreatest (spectrum ℝ M.Sigma) M.smax :=
  isGreatest_sortedEigenvalues M.Sigma_isHermitian M.d_pos

/-- `0 ≤ λ_min(Σ)` since `Σ ⪰ 0`. -/
theorem smin_nonneg : 0 ≤ M.smin := sortedEigenvalues_nonneg M.Sigma_posSemidef _

theorem smin_le_sortedEigenvalues (j : Fin d) :
    M.smin ≤ sortedEigenvalues M.Sigma_isHermitian j :=
  sortedEigenvalues_antitone _ (Fin.le_def.mpr (Nat.le_sub_one_of_lt j.isLt))

theorem sortedEigenvalues_le_smax (j : Fin d) :
    sortedEigenvalues M.Sigma_isHermitian j ≤ M.smax :=
  sortedEigenvalues_antitone _ (Fin.le_def.mpr (Nat.zero_le _))

theorem smin_le_smax : M.smin ≤ M.smax := M.smin_le_sortedEigenvalues _

/-- Rayleigh bounds for the noise covariance: `λ_min(Σ) ‖y‖² ≤ yᵀ Σ y ≤ λ_max(Σ) ‖y‖²`. -/
theorem Sigma_rayleigh (y : EuclideanSpace ℝ (Fin d)) :
    M.smin * ‖y‖ ^ 2 ≤ ⟪y, M.Sigma.toEuclideanLin y⟫_ℝ ∧
      ⟪y, M.Sigma.toEuclideanLin y⟫_ℝ ≤ M.smax * ‖y‖ ^ 2 :=
  ⟨(isEigenbasis_sorted M.Sigma_isHermitian).le_inner_mulVec M.smin_le_sortedEigenvalues y,
    (isEigenbasis_sorted M.Sigma_isHermitian).inner_mulVec_le M.sortedEigenvalues_le_smax y⟩

/-- `λ_min(Σ) ≤ vᵀ Σ v` for every unit vector of an orthonormal basis `v`. -/
theorem smin_le_kap2 (v : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) (i : Fin d) :
    M.smin ≤ kap2 v M.Sigma i :=
  le_kap2 v (isEigenbasis_sorted M.Sigma_isHermitian) M.smin_le_sortedEigenvalues i

/-- `vᵀ Σ v ≤ λ_max(Σ)` for every unit vector of an orthonormal basis `v`. -/
theorem kap2_le_smax (v : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) (i : Fin d) :
    kap2 v M.Sigma i ≤ M.smax :=
  kap2_le v (isEigenbasis_sorted M.Sigma_isHermitian) M.sortedEigenvalues_le_smax i

/-- The abstract noise data `Noise (Fin d)` obtained by reading `Σ` in an arbitrary orthonormal
basis `v`: `κ_i² = v_iᵀ Σ v_i`, `s_min = λ_min(Σ)`, `s_max = λ_max(Σ)`. -/
def noiseOf (v : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) : Noise (Fin d) where
  kap2 := kap2 v M.Sigma
  smin := M.smin
  smax := M.smax
  smin_nonneg := M.smin_nonneg
  smin_le := M.smin_le_kap2 v
  le_smax := M.kap2_le_smax v

/-- **The abstract noise `Noise (Fin d)` of the matrix setting**: `κ_i² = u_iᵀ Σ u_i` in the
eigenbasis `u` of `A`, `s_min = λ_min(Σ)`, `s_max = λ_max(Σ)` (paper §3.2). -/
def noise : Noise (Fin d) := M.noiseOf M.u

@[simp] theorem noise_smin : M.noise.smin = M.smin := rfl
@[simp] theorem noise_smax : M.noise.smax = M.smax := rfl

/-- `κ_i² = u_iᵀ Σ u_i`. -/
theorem noise_kap2 (i : Fin d) :
    M.noise.kap2 i = (M.u i).ofLp ⬝ᵥ M.Sigma *ᵥ (M.u i).ofLp :=
  kap2_eq_dotProduct M.u M.Sigma i

/-- `κ_i² = (C)_{ii}` with `C = Uᵀ Σ U` (paper §3.2). -/
theorem noise_kap2_eq_diag (i : Fin d) :
    M.noise.kap2 i = ((eigMatrix M.u)ᵀ * M.Sigma * eigMatrix M.u) i i :=
  kap2_eq_diag M.u M.Sigma i

/-- `∑_i κ_i² = Tr Σ`. -/
theorem sum_noise_kap2 : ∑ i, M.noise.kap2 i = M.Sigma.trace := sum_kap2 M.u M.Sigma

/-- `λ_min(Σ) ≤ κ_i² ≤ λ_max(Σ)` (paper §3.2). -/
theorem noise_kap2_bounds (i : Fin d) : M.smin ≤ M.noise.kap2 i ∧ M.noise.kap2 i ≤ M.smax :=
  ⟨M.smin_le_kap2 M.u i, M.kap2_le_smax M.u i⟩

/-- `κ_i² ≥ 0` (Appendix A.1). -/
theorem noise_kap2_nonneg (i : Fin d) : 0 ≤ M.noise.kap2 i := kap2_nonneg M.u M.Sigma_posSemidef i

/-- `d · λ_min(Σ) ≤ Tr Σ ≤ d · λ_max(Σ)`. -/
theorem trace_Sigma_bounds :
    (d : ℝ) * M.smin ≤ M.Sigma.trace ∧ M.Sigma.trace ≤ (d : ℝ) * M.smax := by
  rw [← M.sum_noise_kap2]
  constructor
  · calc (d : ℝ) * M.smin = ∑ _i : Fin d, M.smin := by simp
      _ ≤ ∑ i, M.noise.kap2 i := Finset.sum_le_sum fun i _ => (M.noise_kap2_bounds i).1
  · calc ∑ i, M.noise.kap2 i ≤ ∑ _i : Fin d, M.smax :=
        Finset.sum_le_sum fun i _ => (M.noise_kap2_bounds i).2
      _ = (d : ℝ) * M.smax := by simp

/-! ### States: eigen-coordinates, gradient, loss, projectors, alignment -/

/-- The eigen-coordinates `c_i = ⟪x, u_i⟫` of a state `x` (paper §3.2).  The same map sends the
noise `ξ` to `ζ_i = ⟪ξ, u_i⟫` (Appendix A.2). -/
def coord (x : EuclideanSpace ℝ (Fin d)) : Fin d → ℝ := MatrixBridge.coord M.u x

theorem coord_apply (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) : M.coord x i = ⟪x, M.u i⟫_ℝ := rfl

/-- The eigen-expansion `x = ∑_i c_i u_i` (paper §3.2). -/
theorem sum_coord_smul (x : EuclideanSpace ℝ (Fin d)) : ∑ i, M.coord x i • M.u i = x :=
  MatrixBridge.sum_coord_smul M.u x

@[simp] theorem coord_zero : M.coord 0 = 0 := MatrixBridge.coord_zero M.u

theorem coord_eq_zero_iff (x : EuclideanSpace ℝ (Fin d)) : M.coord x = 0 ↔ x = 0 :=
  MatrixBridge.coord_eq_zero_iff M.u x

/-- Every coefficient vector `c` is the coordinate vector of a (unique) state. -/
theorem coord_surjective : Function.Surjective M.coord :=
  fun c => ⟨∑ j, c j • M.u j, MatrixBridge.coord_sum_smul M.u c⟩

theorem coord_injective : Function.Injective M.coord := MatrixBridge.coord_injective M.u

/-- The gradient `∇L(x) = A x` of the quadratic loss (see `hasGradientAt_loss`). -/
def grad (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) := M.A.toEuclideanLin x

/-- `grad x` is the matrix–vector product `A x`. -/
theorem grad_ofLp (x : EuclideanSpace ℝ (Fin d)) : (M.grad x).ofLp = M.A *ᵥ x.ofLp := rfl

/-- The quadratic loss `L(x) = ½ xᵀ A x`. -/
def loss (x : EuclideanSpace ℝ (Fin d)) : ℝ := 1 / 2 * ⟪x, M.A.toEuclideanLin x⟫_ℝ

/-- `L(x) = ½ xᵀ A x`, written with the dot product. -/
theorem loss_eq_dotProduct (x : EuclideanSpace ℝ (Fin d)) :
    M.loss x = 1 / 2 * (x.ofLp ⬝ᵥ M.A *ᵥ x.ofLp) := by
  rw [loss, EuclideanSpace.inner_eq_star_dotProduct]
  simp [toLpLin_apply, dotProduct_comm]

/-- The dominant projector `P^𝒟 = ∑_{i∈𝒟} u_i u_iᵀ` (paper §3.2). -/
def PD : Matrix (Fin d) (Fin d) ℝ := proj M.u M.spec.D

/-- The bulk projector `P^ℬ = ∑_{i∈ℬ} u_i u_iᵀ` (paper §3.2). -/
def PB : Matrix (Fin d) (Fin d) ℝ := proj M.u M.spec.B

theorem PD_eq_sum : M.PD = ∑ i ∈ M.spec.D, vecMulVec (M.u i) (M.u i) := rfl
theorem PB_eq_sum : M.PB = ∑ i ∈ M.spec.B, vecMulVec (M.u i) (M.u i) := rfl

/-- `P^𝒟 + P^ℬ = I`. -/
theorem PD_add_PB : M.PD + M.PB = 1 := proj_add_proj_compl M.u M.spec.D

theorem PD_mul_PD : M.PD * M.PD = M.PD := proj_mul_self M.u _
theorem PB_mul_PB : M.PB * M.PB = M.PB := proj_mul_self M.u _
theorem PD_mul_PB : M.PD * M.PB = 0 := proj_mul_proj_compl M.u M.spec.D
theorem PD_transpose : M.PDᵀ = M.PD := proj_transpose M.u _
theorem PB_transpose : M.PBᵀ = M.PB := proj_transpose M.u _
theorem PD_mul_A : M.PD * M.A = M.A * M.PD := M.isEigenbasis.proj_mul_comm M.u _
theorem PB_mul_A : M.PB * M.A = M.A * M.PB := M.isEigenbasis.proj_mul_comm M.u _

open Classical in
/-- **The paper's squared alignment** (§3.2, Appendix A.1), literally:
`θ(x) = ‖P^𝒟 ∇L(x)‖² / ‖∇L(x)‖²` if `x ≠ 0`, and `θ(0) = 0`. -/
def theta (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  if x = 0 then 0 else ‖M.PD.toEuclideanLin (M.grad x)‖ ^ 2 / ‖M.grad x‖ ^ 2

/-- `‖x‖² = ∑_i c_i²`. -/
theorem norm_sq_eq (x : EuclideanSpace ℝ (Fin d)) : ‖x‖ ^ 2 = Spec.normSq (M.coord x) :=
  norm_sq_eq_sum_coord M.u x

/-- `‖P^𝒟 x‖² = ∑_{i∈𝒟} c_i²`. -/
theorem norm_sq_PD (x : EuclideanSpace ℝ (Fin d)) :
    ‖M.PD.toEuclideanLin x‖ ^ 2 = M.spec.normSqD (M.coord x) :=
  norm_sq_proj M.u _ x

/-- `‖P^S A x‖² = ∑_{i∈S} λ_i² c_i²` for every index set `S`. -/
theorem norm_sq_proj_grad (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    ‖(proj M.u S).toEuclideanLin (M.grad x)‖ ^ 2 = M.spec.mom S 2 (M.coord x) :=
  M.isEigenbasis.norm_sq_proj_mulVec M.u S x

/-- `‖P^𝒟 A x‖² = ∑_{i∈𝒟} λ_i² c_i² = s^𝒟` (paper §3.2). -/
theorem norm_sq_PD_grad (x : EuclideanSpace ℝ (Fin d)) :
    ‖M.PD.toEuclideanLin (M.grad x)‖ ^ 2 = M.spec.sD (M.coord x) :=
  M.norm_sq_proj_grad _ x

/-- `‖P^ℬ A x‖² = ∑_{i∈ℬ} λ_i² c_i² = s^ℬ` (paper §3.2). -/
theorem norm_sq_PB_grad (x : EuclideanSpace ℝ (Fin d)) :
    ‖M.PB.toEuclideanLin (M.grad x)‖ ^ 2 = M.spec.sB (M.coord x) :=
  M.norm_sq_proj_grad _ x

/-- `‖A x‖² = ∑_i λ_i² c_i² = s` (paper §3.2). -/
theorem norm_sq_grad (x : EuclideanSpace ℝ (Fin d)) : ‖M.grad x‖ ^ 2 = M.spec.s (M.coord x) := by
  rw [Spec.s_eq_sum]
  exact M.isEigenbasis.norm_sq_mulVec x

/-- `xᵀ A x = ∑_i λ_i c_i²`. -/
theorem inner_grad (x : EuclideanSpace ℝ (Fin d)) :
    ⟪x, M.grad x⟫_ℝ = ∑ i, M.lam i * M.coord x i ^ 2 :=
  M.isEigenbasis.inner_mulVec x

/-- `L(x) = ½ xᵀ A x = ½ ∑_i λ_i c_i²`: the matrix loss is `Spec.loss` of the coordinates. -/
theorem loss_eq (x : EuclideanSpace ℝ (Fin d)) : M.loss x = M.spec.loss (M.coord x) := by
  unfold loss Spec.loss
  rw [M.isEigenbasis.inner_mulVec x]
  rfl

/-- `∇L(x) = 0 ↔ x = 0` (`A` is positive definite), so the quotient defining `θ(x)` for `x ≠ 0`
has a non-zero denominator. -/
theorem grad_eq_zero_iff (x : EuclideanSpace ℝ (Fin d)) : M.grad x = 0 ↔ x = 0 := by
  rw [← norm_eq_zero, ← sq_eq_zero_iff, M.norm_sq_grad, Spec.s_eq_zero_iff, coord_eq_zero_iff]

theorem norm_sq_grad_pos {x : EuclideanSpace ℝ (Fin d)} (hx : x ≠ 0) : 0 < ‖M.grad x‖ ^ 2 :=
  pow_pos (norm_pos_iff.mpr fun h => hx ((M.grad_eq_zero_iff x).mp h)) 2

@[simp] theorem theta_zero : M.theta 0 = 0 := by simp [theta]

theorem theta_of_ne_zero {x : EuclideanSpace ℝ (Fin d)} (hx : x ≠ 0) :
    M.theta x = ‖M.PD.toEuclideanLin (M.grad x)‖ ^ 2 / ‖M.grad x‖ ^ 2 := by
  simp [theta, hx]

/-- **The paper's alignment is `Spec.theta` of the eigen-coordinates** (for every `x`, including
`x = 0` where both sides are `0` by the paper's convention):
`θ(x) = ∑_{i∈𝒟} λ_i² c_i² / ∑_i λ_i² c_i²`. -/
theorem theta_eq (x : EuclideanSpace ℝ (Fin d)) : M.theta x = M.spec.theta (M.coord x) := by
  by_cases hx : x = 0
  · subst hx
    simp
  · rw [M.theta_of_ne_zero hx, Spec.theta, M.norm_sq_PD_grad, M.norm_sq_grad]

/-- `θ(x) ∈ [0, 1]` (paper §3.2). -/
theorem theta_mem_Icc (x : EuclideanSpace ℝ (Fin d)) : M.theta x ∈ Set.Icc (0 : ℝ) 1 := by
  rw [M.theta_eq]
  exact ⟨M.spec.theta_nonneg _, M.spec.theta_le_one _⟩

/-- `1 - θ(x) = ‖P^ℬ A x‖² / ‖A x‖²` for `x ≠ 0`. -/
theorem one_sub_theta {x : EuclideanSpace ℝ (Fin d)} (hx : x ≠ 0) :
    1 - M.theta x = ‖M.PB.toEuclideanLin (M.grad x)‖ ^ 2 / ‖M.grad x‖ ^ 2 := by
  have h := M.norm_sq_grad_pos hx
  rw [M.theta_of_ne_zero hx, M.norm_sq_PD_grad, M.norm_sq_PB_grad]
  rw [M.norm_sq_grad] at h ⊢
  unfold Spec.s at h ⊢
  field_simp
  ring

/-- The block moments `∑_{i∈S} λ_i^p c_i² = xᵀ P^S A^p x` (`s^S` for `p = 2`, `τ^S` for `p = 3`). -/
theorem mom_coord (S : Finset (Fin d)) (p : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    M.spec.mom S p (M.coord x) = ⟪x, (proj M.u S * M.A ^ p).toEuclideanLin x⟫_ℝ := by
  rw [← M.isEigenbasis.projPow_eq M.u, inner_projPow]
  rfl

/-! ### Dynamics: SGD and projected SGD in eigen-coordinates -/

/-- One SGD step `x⁺ = x - η (A x + ξ)` (paper §3.2). -/
def sgdStep (η : ℝ) (x ξ : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  x - η • (M.grad x + ξ)

/-- One projected SGD step `x⁺ = x - η P^S (A x + ξ)`, `P^S = ∑_{i∈S} u_i u_iᵀ`
(paper eq. (3)–(4): DSGD for `S = 𝒟`, BSGD for `S = ℬ`). -/
def projStep (S : Finset (Fin d)) (η : ℝ) (x ξ : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  x - η • (proj M.u S).toEuclideanLin (M.grad x + ξ)

/-- **SGD in eigen-coordinates** (Appendix A.2):
`c_{i,t+1} = (1 - η λ_i) c_{i,t} - η ζ_{i,t}` with `ζ_i = ⟪ξ, u_i⟫`, i.e. the coordinates of
`x - η (A x + ξ)` are `Spec.cNext η c ζ`. -/
theorem coord_sgdStep (η : ℝ) (x ξ : EuclideanSpace ℝ (Fin d)) :
    M.coord (M.sgdStep η x ξ) = M.spec.cNext η (M.coord x) (M.coord ξ) :=
  funext fun i => M.isEigenbasis.coord_sgdStep M.u η x ξ i

/-- **Projected SGD in eigen-coordinates**: the coordinates of `x - η P^S (A x + ξ)` are
`Spec.cNextProj S η c ζ`. -/
theorem coord_projStep (S : Finset (Fin d)) (η : ℝ) (x ξ : EuclideanSpace ℝ (Fin d)) :
    M.coord (M.projStep S η x ξ) = M.spec.cNextProj S η (M.coord x) (M.coord ξ) :=
  funext fun i => M.isEigenbasis.coord_projStep M.u S η x ξ i

/-- DSGD (paper eq. (3)): `x⁺ = x - η P^𝒟 (A x + ξ)`. -/
theorem coord_dsgdStep (η : ℝ) (x ξ : EuclideanSpace ℝ (Fin d)) :
    M.coord (x - η • M.PD.toEuclideanLin (M.grad x + ξ)) =
      M.spec.cNextProj M.spec.D η (M.coord x) (M.coord ξ) :=
  M.coord_projStep M.spec.D η x ξ

/-- BSGD (paper eq. (4)): `x⁺ = x - η P^ℬ (A x + ξ)`. -/
theorem coord_bsgdStep (η : ℝ) (x ξ : EuclideanSpace ℝ (Fin d)) :
    M.coord (x - η • M.PB.toEuclideanLin (M.grad x + ξ)) =
      M.spec.cNextProj M.spec.B η (M.coord x) (M.coord ξ) :=
  M.coord_projStep M.spec.B η x ξ

/-- The next-step alignment of SGD, eq. (9) of Appendix A.2:
`θ(x_{t+1}) = Spec.theta (Spec.cNext η c ζ)`. -/
theorem theta_sgdStep (η : ℝ) (x ξ : EuclideanSpace ℝ (Fin d)) :
    M.theta (M.sgdStep η x ξ) = M.spec.theta (M.spec.cNext η (M.coord x) (M.coord ξ)) := by
  rw [M.theta_eq, M.coord_sgdStep]

/-- The next-step loss of the projected update in coordinates. -/
theorem loss_projStep (S : Finset (Fin d)) (η : ℝ) (x ξ : EuclideanSpace ℝ (Fin d)) :
    M.loss (M.projStep S η x ξ) = M.spec.loss (M.spec.cNextProj S η (M.coord x) (M.coord ξ)) := by
  rw [M.loss_eq, M.coord_projStep]

/-! ### Trace formulas for the spectral and noise energies -/

/-- `ψ_𝒟 = ∑_{i∈𝒟} λ_i² = Tr(P^𝒟 A²)`. -/
theorem psiD_eq_trace : M.spec.psiD = (M.PD * M.A ^ 2).trace := by
  rw [PD, ← M.isEigenbasis.projPow_eq M.u, trace_projPow]
  rfl

/-- `ψ_ℬ = ∑_{i∈ℬ} λ_i² = Tr(P^ℬ A²)`. -/
theorem psiB_eq_trace : M.spec.psiB = (M.PB * M.A ^ 2).trace := by
  rw [PB, ← M.isEigenbasis.projPow_eq M.u, trace_projPow]
  rfl

/-- `∑_{i∈S} λ_i^p κ_i² = Tr(Σ P^S A^p)` for every index set `S`. -/
theorem sum_pow_mul_noise_kap2 (S : Finset (Fin d)) (p : ℕ) :
    ∑ i ∈ S, M.lam i ^ p * M.noise.kap2 i = (M.Sigma * (proj M.u S * M.A ^ p)).trace := by
  rw [← M.isEigenbasis.projPow_eq M.u, ← sum_pow_mul_kap2]
  rfl

/-- `e_𝒟 = ∑_{i∈𝒟} λ_i² κ_i² = Tr(Σ P^𝒟 A²)`. -/
theorem eD_eq_trace : M.spec.eD M.noise = (M.Sigma * (M.PD * M.A ^ 2)).trace :=
  M.sum_pow_mul_noise_kap2 _ 2

/-- `e_ℬ = ∑_{i∈ℬ} λ_i² κ_i² = Tr(Σ P^ℬ A²)`. -/
theorem eB_eq_trace : M.spec.eB M.noise = (M.Sigma * (M.PB * M.A ^ 2)).trace :=
  M.sum_pow_mul_noise_kap2 _ 2

/-- `n^loss_S = ∑_{i∈S} λ_i κ_i² = Tr(Σ P^S A)`. -/
theorem nLoss_eq_trace (S : Finset (Fin d)) :
    M.spec.nLoss M.noise S = (M.Sigma * (proj M.u S * M.A)).trace := by
  have h := M.sum_pow_mul_noise_kap2 S 1
  simp only [pow_one] at h
  exact h

/-- The bounds `s_min ψ_𝒟 ≤ e_𝒟 ≤ s_max ψ_𝒟` and `s_min ψ_ℬ ≤ e_ℬ ≤ s_max ψ_ℬ` of the paper
(§3.2, Appendix A.1), for the actual matrices. -/
theorem noise_energy_bounds :
    (M.smin * M.spec.psiD ≤ M.spec.eD M.noise ∧ M.spec.eD M.noise ≤ M.smax * M.spec.psiD) ∧
      (M.smin * M.spec.psiB ≤ M.spec.eB M.noise ∧ M.spec.eB M.noise ≤ M.smax * M.spec.psiB) :=
  ⟨⟨M.spec.smin_psiD_le_eD M.noise, M.spec.eD_le_smax_psiD M.noise⟩,
    ⟨M.spec.smin_psiB_le_eB M.noise, M.spec.eB_le_smax_psiB M.noise⟩⟩

/-! ### The gradient of the loss -/

/-- `∇L(x) = A x` (paper §3.2): the gradient of `L(x) = ½ xᵀ A x` at `x` is `A x`
(this uses the symmetry of `A`). -/
theorem hasGradientAt_loss (x : EuclideanSpace ℝ (Fin d)) : HasGradientAt M.loss (M.grad x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin d) =>
      (LinearMap.toContinuousLinearMap M.A.toEuclideanLin) y)
      (LinearMap.toContinuousLinearMap M.A.toEuclideanLin) x :=
    (LinearMap.toContinuousLinearMap M.A.toEuclideanLin).hasFDerivAt
  have h2 := ((hasFDerivAt_id x).inner ℝ h1).const_mul (1 / 2 : ℝ)
  have hsym : ∀ y, ⟪M.A.toEuclideanLin x, y⟫_ℝ = ⟪x, M.A.toEuclideanLin y⟫_ℝ := fun y =>
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr M.A_isHermitian) x y
  refine h2.congr_fderiv ?_
  ext y
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, ContinuousLinearMap.prod_apply, fderivInnerCLM_apply, smul_eq_mul,
    InnerProductSpace.toDual_apply_apply, LinearMap.coe_toContinuousLinearMap', id_eq,
    ContinuousLinearMap.coe_id']
  rw [grad, hsym y, real_inner_comm y (M.A.toEuclideanLin x), hsym y]
  ring

/-! ### Independence of the choice of the eigenvectors

The paper fixes "the" decomposition `A = U Λ Uᵀ`, but `U` is not unique (signs; rotations inside
eigenspaces of repeated eigenvalues).  We show that nothing block-level depends on the choice:
the sorted eigenvalue list is unique, the projectors `P^𝒟`, `P^ℬ` are unique *because of the gap*,
and therefore `s^𝒟, s^ℬ, s, θ, L, τ^𝒟, τ^ℬ, ψ_𝒟, ψ_ℬ, e_𝒟, e_ℬ` are intrinsic to `(A, Σ, k)`.
(Individual coordinates `c_i` and variances `κ_i²` do depend on `U`.) -/

section Indep

variable {v : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))}

/-- Any decreasing list of eigenvalues of an orthonormal eigenbasis of `A` is `M.lam`. -/
theorem lam_unique {mu : Fin d → ℝ} (h : IsEigenbasis M.A v mu) (hmu : Antitone mu) :
    mu = M.lam :=
  h.eq_sortedEigenvalues hmu M.A_isHermitian

/-- Dominant and bulk eigenvalues are different (the gap). -/
theorem lam_ne_of_mem_of_not_mem {i j : Fin d} (hi : i ∈ M.spec.D) (hj : j ∉ M.spec.D) :
    M.lam i ≠ M.lam j := by
  have h1 : M.spec.lamk ≤ M.lam i := M.spec.lamk_le i hi
  have h2 : M.lam j ≤ M.spec.lamk1 := M.spec.le_lamk1 j hj
  have h3 : M.spec.lamk1 < M.spec.lamk := M.spec.gap
  intro h
  linarith

/-- **`P^𝒟` does not depend on the choice of the eigenvectors**: for every orthonormal eigenbasis
`v` of `A` (with the sorted eigenvalues), `∑_{i<k} v_i v_iᵀ = P^𝒟`. -/
theorem proj_D_eq_PD (h : IsEigenbasis M.A v M.lam) : proj v M.spec.D = M.PD :=
  h.proj_eq_proj v M.isEigenbasis (fun _ hi _ hj => M.lam_ne_of_mem_of_not_mem hi hj)
    (fun _ hi _ hj => (M.lam_ne_of_mem_of_not_mem hj hi).symm)

/-- `P^ℬ` does not depend on the choice of the eigenvectors. -/
theorem proj_B_eq_PB (h : IsEigenbasis M.A v M.lam) : proj v M.spec.B = M.PB := by
  have h1 : proj v M.spec.D + proj v M.spec.B = 1 := proj_add_proj_compl v M.spec.D
  have h2 := M.PD_add_PB
  rw [M.proj_D_eq_PD h] at h1
  exact add_left_cancel (h1.trans h2.symm)

/-- The block moments in an arbitrary eigenbasis: `∑_{i∈S} λ_i^p ⟪x, v_i⟫² = xᵀ P^S_v A^p x`. -/
theorem mom_coord_of_isEigenbasis (h : IsEigenbasis M.A v M.lam) (S : Finset (Fin d)) (p : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) :
    M.spec.mom S p (MatrixBridge.coord v x) = ⟪x, (proj v S * M.A ^ p).toEuclideanLin x⟫_ℝ := by
  rw [← h.projPow_eq v, inner_projPow]
  rfl

/-- The dominant block moments (`s^𝒟`, `τ^𝒟`, …) do not depend on the eigenbasis. -/
theorem mom_D_coord_eq (h : IsEigenbasis M.A v M.lam) (p : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    M.spec.mom M.spec.D p (MatrixBridge.coord v x) = M.spec.mom M.spec.D p (M.coord x) := by
  rw [M.mom_coord_of_isEigenbasis h, M.proj_D_eq_PD h, M.mom_coord]
  rfl

/-- The bulk block moments (`s^ℬ`, `τ^ℬ`, …) do not depend on the eigenbasis. -/
theorem mom_B_coord_eq (h : IsEigenbasis M.A v M.lam) (p : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    M.spec.mom M.spec.B p (MatrixBridge.coord v x) = M.spec.mom M.spec.B p (M.coord x) := by
  rw [M.mom_coord_of_isEigenbasis h, M.proj_B_eq_PB h, M.mom_coord]
  rfl

/-- **The alignment does not depend on the eigenbasis**: `Spec.theta` of the coordinates in *any*
orthonormal eigenbasis of `A` is the paper's `θ(x)`. -/
theorem theta_coord_eq (h : IsEigenbasis M.A v M.lam) (x : EuclideanSpace ℝ (Fin d)) :
    M.spec.theta (MatrixBridge.coord v x) = M.theta x := by
  rw [M.theta_eq]
  simp only [Spec.theta, Spec.s, Spec.sD, Spec.sB, M.mom_D_coord_eq h, M.mom_B_coord_eq h]

/-- The loss does not depend on the eigenbasis. -/
theorem loss_coord_eq (h : IsEigenbasis M.A v M.lam) (x : EuclideanSpace ℝ (Fin d)) :
    M.spec.loss (MatrixBridge.coord v x) = M.loss x := by
  unfold loss Spec.loss
  rw [h.inner_mulVec x]
  rfl

/-- `∑_{i∈S} λ_i^p (v_iᵀ Σ v_i) = Tr(Σ P^S_v A^p)` in an arbitrary eigenbasis. -/
theorem sum_pow_mul_kap2_of_isEigenbasis (h : IsEigenbasis M.A v M.lam) (S : Finset (Fin d))
    (p : ℕ) :
    ∑ i ∈ S, M.lam i ^ p * (M.noiseOf v).kap2 i = (M.Sigma * (proj v S * M.A ^ p)).trace := by
  rw [← h.projPow_eq v, ← sum_pow_mul_kap2]
  rfl

/-- `e_𝒟` does not depend on the eigenbasis. -/
theorem eD_noiseOf_eq (h : IsEigenbasis M.A v M.lam) :
    M.spec.eD (M.noiseOf v) = M.spec.eD M.noise := by
  rw [M.eD_eq_trace, ← M.proj_D_eq_PD h]
  exact M.sum_pow_mul_kap2_of_isEigenbasis h _ 2

/-- `e_ℬ` does not depend on the eigenbasis. -/
theorem eB_noiseOf_eq (h : IsEigenbasis M.A v M.lam) :
    M.spec.eB (M.noiseOf v) = M.spec.eB M.noise := by
  rw [M.eB_eq_trace, ← M.proj_B_eq_PB h]
  exact M.sum_pow_mul_kap2_of_isEigenbasis h _ 2

end Indep

/-! ### Non-vacuity: diagonal instances -/

section Diagonal

variable {d : ℕ} (w σ : Fin d → ℝ) (k : ℕ) (hw : Antitone w) (hpos : ∀ i, 0 < w i)
  (hσ : ∀ i, 0 ≤ σ i) (hk : 0 < k) (hkd : k < d)
  (hgap : w ⟨k, hkd⟩ < w ⟨k - 1, lt_of_le_of_lt (Nat.sub_le k 1) hkd⟩)

/-- **Every admissible spectrum is realised**: for a decreasing positive `w : Fin d → ℝ` with a gap
`w_{k+1} < w_k` (`0 < k < d`) and nonnegative `σ`, the diagonal matrices `A = diag(w)`,
`Σ = diag(σ)` form a `MatrixSetting`. -/
def ofDiagonal : MatrixSetting d where
  A := diagonal w
  Sigma := diagonal σ
  k := k
  A_posDef := Matrix.posDef_diagonal_iff.mpr hpos
  Sigma_posSemidef := Matrix.posSemidef_diagonal_iff.mpr hσ
  k_pos := hk
  k_lt := hkd
  gap := by
    rw [sortedEigenvalues_diagonal hw]
    exact hgap

/-- The sorted spectrum of `diag(w)` is `w`. -/
theorem ofDiagonal_lam : (ofDiagonal w σ k hw hpos hσ hk hkd hgap).lam = w :=
  sortedEigenvalues_diagonal hw _

/-- The standard basis is an eigenbasis of `diag(w)`. -/
theorem ofDiagonal_isEigenbasis :
    IsEigenbasis (ofDiagonal w σ k hw hpos hσ hk hkd hgap).A (EuclideanSpace.basisFun (Fin d) ℝ)
      (ofDiagonal w σ k hw hpos hσ hk hkd hgap).lam := by
  rw [ofDiagonal_lam]
  exact isEigenbasis_diagonal w

end Diagonal

end MatrixSetting

end SuspiciousAlignment
