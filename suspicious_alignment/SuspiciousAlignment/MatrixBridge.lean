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
    rw [pow_succ, Matrix.toLpLin_mul_same, LinearMap.comp_apply, h i, map_smul, ih, smul_smul,
      pow_succ, mul_comm]

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
    vecMulVec_mulVec, op_smul_eq_smul, smul_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coord_apply, EuclideanSpace.inner_eq_star_dotProduct]
  simp

theorem coord_projPow (lam : ι → ℝ) (S : Finset ι) (p : ℕ) (y : EuclideanSpace ℝ n) (i : ι) :
    coord u ((projPow u lam S p).toEuclideanLin y) i =
      if i ∈ S then lam i ^ p * coord u y i else 0 := by
  rw [projPow_apply, coord_sum, Finset.sum_apply]
  simp [coord_smul, coord_basis]

/-- `xᵀ P^S_{λ^p} x = ∑_{i∈S} λ_i^p c_i²` (the block moments `Spec.mom`). -/
theorem inner_projPow (lam : ι → ℝ) (S : Finset ι) (p : ℕ) (x : EuclideanSpace ℝ n) :
    ⟪x, (projPow u lam S p).toEuclideanLin x⟫_ℝ = ∑ i ∈ S, lam i ^ p * coord u x i ^ 2 := by
  rw [inner_eq_sum_coord u]
  simp_rw [coord_projPow]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S)]
  simp [Finset.sum_ite_mem, Finset.filter_mem_eq_inter, mul_comm, mul_left_comm, sq]

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
  · simp only [hi, if_true]
    conv_lhs => rw [← sum_coord_smul v (u i)]
    symm
    apply Finset.sum_subset (Finset.subset_univ T)
    intro j _ hj
    rw [coord_apply, hu.inner_eq_zero_of_ne hv (h1 i hi j hj), zero_smul]
  · simp only [hi, if_false]
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
  simp [Matrix.diagonal_mulVec_single, Pi.single_apply]

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

end MatrixSetting

end SuspiciousAlignment
