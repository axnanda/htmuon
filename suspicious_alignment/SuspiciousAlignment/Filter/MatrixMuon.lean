import Mathlib
import SuspiciousAlignment.Defs

/-!
# General matrix Muon on wide layers (no commuting assumption)

This file is an **extension** of Deng et al., *Suspicious Alignment of SGD* (arXiv:2601.11789v2):
it formalizes Section 5 of `notes/research/filter_spec.md` (new mathematics, not in the paper).

Setting: `A ∈ ℝ^{d×d}` symmetric, parameters `W ∈ ℝ^{d×n}`, loss `L(W) = ½ tr(Wᵀ A W)`,
`G ∈ ℝ^{d×n}` any matrix (clean or stochastic gradient).  A *left polar pair* of `G` is `(S, O)`
with `S` symmetric positive semidefinite, `O Oᵀ = 1` and `G = S O`; `O = msign(G)` is Muon's update
direction.  Rows are indexed by a finite type `ι` (`d = |ι|`), columns by a finite type `κ`
(`n = |κ|`).  The projector is called `E` (`Π` is a reserved token in Lean).

## Definitions (namespace `SuspiciousAlignment.MatrixMuon`)

* `frob X Y = tr(Xᵀ Y)`, the Frobenius pairing;
* `loss A W = ½ tr(Wᵀ A W)`;
* `IsOrthProj E` : `Eᵀ = E` and `E E = E`;
* `IsLeftPolar G S O` : `S` positive semidefinite (`Matrix.PosSemidef`, which includes symmetry),
  `O Oᵀ = 1`, `G = S O`;
* `coordProj T`, the coordinate projector on a finset `T` of rows;
* `filterDir f S O = f(S) O` (Mathlib's `cfc`), the spectrally filtered direction.

## Main results (namespace `SuspiciousAlignment`)

* 5.1 `matrixMuon_equipartition`, `matrixMuon_energy_proj`, `matrixMuon_energy_proj_rank`,
  `matrixMuon_energy_total`, `matrixMuon_energy_fraction`: `‖E O‖_F² = ‖E‖_F²`; for an orthogonal
  projector the Muon update has energy `tr E = rank E` in its range, `d` in total, fraction `k/d`.
  For SGD the fraction is Deng's `θ` (`matrixMuon_sgd_energy_fraction`).
* 5.2 `matrixMuon_loss_projected_step`:
  `L(W - η E O) - L(W) = -η ⟪E A W, O⟫ + (η²/2) tr(E A)` for every `O` with `O Oᵀ = 1`
  (commutation of `E` with `A` is **not** needed; symmetry of `A` is:
  `matrixMuon_loss_projected_step_needs_symm`).
* 5.3 `matrixMuon_frob_proj_grad`, `matrixMuon_frob_grad_polar`,
  `matrixMuon_loss_decrease_iff`, `matrixMuon_loss_increase_iff`, `matrixMuon_loss_eq_iff`:
  noise-free threshold `2 tr(E S)/tr(E A)`; `⟪G, O⟫ = tr S` = nuclear norm
  (`matrixMuon_frob_grad_polar_eq_nuclear`).
* 5.4 `matrixMuon_isLeftPolar_sqrt`, `matrixMuon_exists_leftPolar`, `matrixMuon_leftPolar_unique`,
  `matrixMuon_existsUnique_leftPolar`, `matrixMuon_isLeftPolar_iff`: if `G Gᵀ` is positive
  definite, the unique left polar pair is `S = (G Gᵀ)^{1/2}` (`CFC.sqrt`), `O = S⁻¹ G`;
  `MatrixMuon.IsLeftPolar.card_le`: `d ≤ n`; `matrixMuon_leftPolar_not_unique`: uniqueness of `O`
  fails without definiteness.
* 5.5 `matrixMuon_isLeftPolar_diagonal`, `matrixMuon_leftPolar_diagonal_unique`,
  `matrixMuon_trace_ratio_coordProj`, `matrixMuon_step_row`, `matrixMuon_coordinate_step`,
  `matrixMuon_coordinate_loss_decrease_iff`: link with the coordinate model; the Muon step acts on
  a commuting state `W = diag(c) Q` by `c_i⁺ = c_i - η sign(c_i)`.
* General filters: `matrixFilter_id` (SGD), `matrixFilter_one` (Muon), `matrixFilter_svd`,
  `matrixFilter_svd_unique` (`f(S) O = U f(Σ) Vᵀ`), `matrixFilter_coordinate_step`,
  `matrixFilter_coordinate_step_basis`: the filtered step acts on a commuting state by
  `c_i⁺ = c_i - η sign(λ_i c_i) f(|λ_i c_i|)` — rule (1.0) of the spec.
* `MatrixMuon.Example`: a concrete non-commuting instance with `d = 2`, `n = 3`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Matrix

namespace SuspiciousAlignment

namespace MatrixMuon

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

/-! ### Definitions -/

/-- The Frobenius pairing `⟪X, Y⟫ = tr(Xᵀ Y) = ∑ᵢⱼ Xᵢⱼ Yᵢⱼ`. -/
def frob {m k : Type*} [Fintype m] [Fintype k] (X Y : Matrix m k ℝ) : ℝ := (Xᵀ * Y).trace

/-- The matrix quadratic loss `L(W) = ½ tr(Wᵀ A W)` (Hessian `I_n ⊗ A`). -/
noncomputable def loss (A : Matrix ι ι ℝ) (W : Matrix ι κ ℝ) : ℝ := 1 / 2 * (Wᵀ * A * W).trace

/-- `E` is an orthogonal projector: `Eᵀ = E` and `E E = E`. -/
structure IsOrthProj (E : Matrix ι ι ℝ) : Prop where
  /-- `E` is symmetric -/
  symm : Eᵀ = E
  /-- `E` is idempotent -/
  idem : E * E = E

/-- `(S, O)` is a *left polar pair* of `G`: `S` is symmetric positive semidefinite, `O` has
orthonormal rows (`O Oᵀ = 1`) and `G = S O`.  Then `O = msign(G)` is Muon's update direction. -/
structure IsLeftPolar (G : Matrix ι κ ℝ) (S : Matrix ι ι ℝ) (O : Matrix ι κ ℝ) : Prop where
  /-- `S` is symmetric positive semidefinite -/
  posSemidef : S.PosSemidef
  /-- `O` has orthonormal rows -/
  orth : O * Oᵀ = 1
  /-- `G = S O` -/
  eq : G = S * O

/-- The coordinate projector on the rows in `T`: the diagonal `0/1` matrix of `T`. -/
def coordProj (T : Finset ι) : Matrix ι ι ℝ := diagonal fun i => if i ∈ T then 1 else 0

/-! ### The Frobenius pairing -/

section frob

variable {m k : Type*} [Fintype m] [Fintype k]

theorem frob_eq_sum (X Y : Matrix m k ℝ) : frob X Y = ∑ i, ∑ j, X i j * Y i j := by
  simp only [frob, trace, diag, mul_apply, transpose_apply]
  exact Finset.sum_comm

theorem frob_comm (X Y : Matrix m k ℝ) : frob X Y = frob Y X := by
  simp only [frob_eq_sum, mul_comm]

theorem frob_self_nonneg (X : Matrix m k ℝ) : 0 ≤ frob X X := by
  rw [frob_eq_sum]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _

/-- `⟪X, X⟫ = ‖X‖_F² = ∑ᵢⱼ Xᵢⱼ²`. -/
theorem frob_self_eq_sum_sq (X : Matrix m k ℝ) : frob X X = ∑ i, ∑ j, X i j ^ 2 := by
  simp only [frob_eq_sum, sq]

theorem frob_self_eq_zero_iff (X : Matrix m k ℝ) : frob X X = 0 ↔ X = 0 := by
  rw [frob_eq_sum]
  constructor
  · intro h
    ext i j
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg (X i j))).mp h i (Finset.mem_univ i)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_self_nonneg (X i j))).mp h1 j (Finset.mem_univ j)
    simpa using h2
  · rintro rfl
    simp

/-- Moving a left factor to the other side of the pairing: `⟪M X, Y⟫ = ⟪X, Mᵀ Y⟫`. -/
theorem frob_mul_left {l : Type*} [Fintype l] (M : Matrix m l ℝ) (X : Matrix l k ℝ)
    (Y : Matrix m k ℝ) : frob (M * X) Y = frob X (Mᵀ * Y) := by
  simp only [frob, transpose_mul, Matrix.mul_assoc]

end frob

/-! ### Orthogonal projectors -/

theorem isOrthProj_one : IsOrthProj (1 : Matrix ι ι ℝ) := ⟨transpose_one, Matrix.mul_one 1⟩

theorem isOrthProj_zero : IsOrthProj (0 : Matrix ι ι ℝ) := ⟨transpose_zero, Matrix.mul_zero 0⟩

/-- The complementary projector `1 - E`. -/
theorem IsOrthProj.one_sub {E : Matrix ι ι ℝ} (h : IsOrthProj E) : IsOrthProj (1 - E) := by
  refine ⟨by rw [transpose_sub, transpose_one, h.symm], ?_⟩
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, h.idem]
  abel

/-- `tr(E M) = tr(Eᵀ M E)` for an orthogonal projector `E`. -/
theorem IsOrthProj.trace_mul {E : Matrix ι ι ℝ} (h : IsOrthProj E) (M : Matrix ι ι ℝ) :
    (E * M).trace = (Eᵀ * M * E).trace := by
  rw [h.symm, trace_mul_comm (E * M) E, ← Matrix.mul_assoc, h.idem]

/-- `tr(E M) ≥ 0` for an orthogonal projector `E` and a positive semidefinite `M`
(no commutation needed). -/
theorem IsOrthProj.trace_mul_nonneg {E : Matrix ι ι ℝ} (h : IsOrthProj E) {M : Matrix ι ι ℝ}
    (hM : M.PosSemidef) : 0 ≤ (E * M).trace := by
  rw [h.trace_mul]
  have := (hM.conjTranspose_mul_mul_same E).trace_nonneg
  simpa only [conjTranspose_eq_transpose_of_trivial] using this

/-- The trace of an orthogonal projector is nonnegative. -/
theorem IsOrthProj.trace_nonneg {E : Matrix ι ι ℝ} (h : IsOrthProj E) : 0 ≤ E.trace := by
  simpa using h.trace_mul_nonneg (PosSemidef.one (n := ι) (R := ℝ))

/-- The trace of an idempotent real matrix is its rank; in particular `tr E = rank E` for an
orthogonal projector (this is the "`tr Π = k`, the rank of `Π`" of spec 5.1). -/
theorem IsOrthProj.trace_eq_rank {E : Matrix ι ι ℝ} (h : IsOrthProj E) : E.trace = E.rank := by
  have hid : IsIdempotentElem (Matrix.toLin' E) := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, h.idem]
  have h1 := (LinearMap.IsIdempotentElem.isProj_range _ hid).trace
  rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ ι), LinearMap.toMatrix_eq_toMatrix',
    LinearMap.toMatrix'_toLin'] at h1
  rw [h1, Matrix.rank]
  rfl

/-! ### The coordinate projector -/

theorem coordProj_apply (T : Finset ι) (i j : ι) :
    coordProj T i j = if i = j then (if i ∈ T then 1 else 0) else 0 := by
  simp [coordProj, diagonal_apply]

theorem isOrthProj_coordProj (T : Finset ι) : IsOrthProj (coordProj T) := by
  refine ⟨diagonal_transpose _, ?_⟩
  rw [coordProj, diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

/-- `tr(Π_T diag(v)) = ∑_{i∈T} v_i`. -/
theorem trace_coordProj_mul_diagonal (T : Finset ι) (v : ι → ℝ) :
    (coordProj T * diagonal v).trace = ∑ i ∈ T, v i := by
  rw [coordProj, diagonal_mul_diagonal, trace_diagonal]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- The coordinate projector on `T` has trace (= rank) `|T|`. -/
theorem trace_coordProj (T : Finset ι) : (coordProj T).trace = T.card := by
  have := trace_coordProj_mul_diagonal T (fun _ => (1 : ℝ))
  simpa using this

/-- Coordinate projectors commute with diagonal matrices (e.g. with `A = diag(λ)`). -/
theorem coordProj_mul_diagonal_comm (T : Finset ι) (v : ι → ℝ) :
    coordProj T * diagonal v = diagonal v * coordProj T := by
  rw [coordProj, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  ring

end MatrixMuon

open MatrixMuon

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

/-! ## 5.1 Equipartition of the Muon update -/

/-- **Spec 5.1 (equipartition of the update).** If `O Oᵀ = 1` then for every matrix `E`
(with any number of rows): `tr((E O)ᵀ (E O)) = tr(Eᵀ E)`. -/
theorem matrixMuon_equipartition {m : Type*} [Fintype m] {O : Matrix ι κ ℝ} (hO : O * Oᵀ = 1)
    (E : Matrix m ι ℝ) : ((E * O)ᵀ * (E * O)).trace = (Eᵀ * E).trace := by
  rw [transpose_mul, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, hO,
    Matrix.mul_one]

/-- Spec 5.1 in terms of the Frobenius pairing: `‖E O‖_F² = ‖E‖_F²`. -/
theorem matrixMuon_frob_mul_orth {m : Type*} [Fintype m] {O : Matrix ι κ ℝ} (hO : O * Oᵀ = 1)
    (E : Matrix m ι ℝ) : frob (E * O) (E * O) = frob E E :=
  matrixMuon_equipartition hO E

/-- **Spec 5.1.** For an orthogonal projector `E` (`E² = E = Eᵀ`) the Muon update `O` has energy
`‖E O‖_F² = tr E` in the range of `E` (`tr E = k` is the rank of `E`), whatever the gradient is. -/
theorem matrixMuon_energy_proj {O : Matrix ι κ ℝ} (hO : O * Oᵀ = 1) {E : Matrix ι ι ℝ}
    (hE : IsOrthProj E) : frob (E * O) (E * O) = E.trace := by
  rw [matrixMuon_frob_mul_orth hO, frob, hE.symm, hE.idem]

/-- **Spec 5.1, rank form.** For an orthogonal projector `E` of rank `k`: `‖E O‖_F² = k`. -/
theorem matrixMuon_energy_proj_rank {O : Matrix ι κ ℝ} (hO : O * Oᵀ = 1) {E : Matrix ι ι ℝ}
    (hE : IsOrthProj E) : frob (E * O) (E * O) = E.rank := by
  rw [matrixMuon_energy_proj hO hE, hE.trace_eq_rank]

/-- **Spec 5.1.** The total energy of the Muon update is `‖O‖_F² = d`. -/
theorem matrixMuon_energy_total {O : Matrix ι κ ℝ} (hO : O * Oᵀ = 1) :
    frob O O = Fintype.card ι := by
  have h := matrixMuon_energy_proj hO (isOrthProj_one (ι := ι))
  rwa [Matrix.one_mul, trace_one] at h

/-- **Spec 5.1.** The fraction of Muon's update energy lying in the range of an orthogonal
projector `E` of trace `k` is exactly `k / d`, irrespective of the gradient
(`d = |ι| > 0`, so the quotient is a genuine one). -/
theorem matrixMuon_energy_fraction [Nonempty ι] {O : Matrix ι κ ℝ} (hO : O * Oᵀ = 1)
    {E : Matrix ι ι ℝ} (hE : IsOrthProj E) :
    frob (E * O) (E * O) / frob O O = E.trace / Fintype.card ι := by
  rw [matrixMuon_energy_proj hO hE, matrixMuon_energy_total hO]

/-- **Spec 5.1** for the coordinate projector on a block `T` of `k = |T|` directions:
the fraction of Muon's update energy in the block is `|T| / d`. -/
theorem matrixMuon_energy_fraction_coordProj [Nonempty ι] {O : Matrix ι κ ℝ} (hO : O * Oᵀ = 1)
    (T : Finset ι) :
    frob (coordProj T * O) (coordProj T * O) / frob O O = (T.card : ℝ) / Fintype.card ι := by
  rw [matrixMuon_energy_fraction hO (isOrthProj_coordProj T), trace_coordProj]

/-! ## 5.2 Exact loss change of a projected Muon step -/

/-- Exact second-order expansion of the quadratic loss along any direction `D`, for symmetric
`A`: `L(W - η D) = L(W) - η ⟪A W, D⟫ + (η²/2) tr(Dᵀ A D)`. -/
theorem matrixMuon_loss_step {A : Matrix ι ι ℝ} (hA : Aᵀ = A) (W D : Matrix ι κ ℝ) (η : ℝ) :
    loss A (W - η • D) = loss A W - η * frob (A * W) D + η ^ 2 / 2 * (Dᵀ * A * D).trace := by
  have h1 : (Wᵀ * A * D).trace = (Dᵀ * A * W).trace := by
    rw [← trace_transpose, transpose_mul, transpose_mul, transpose_transpose, hA,
      Matrix.mul_assoc]
  have h2 : frob (A * W) D = (Dᵀ * A * W).trace := by
    rw [frob_comm, frob, Matrix.mul_assoc]
  simp only [loss, transpose_sub, transpose_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, trace_sub, trace_smul, smul_eq_mul, h1, h2]
  ring

/-- **Spec 5.2 (exact loss change of a projected Muon step).** For `A` symmetric, `E` an orthogonal
projector and **any** `O` with `O Oᵀ = 1` (e.g. the polar factor of a noisy gradient):
`L(W - η E O) - L(W) = -η ⟪E A W, O⟫ + (η²/2) tr(E A)`.

The spec also assumes that `E` commutes with `A` and that `A` is positive semidefinite; neither
hypothesis is needed. -/
theorem matrixMuon_loss_projected_step {A : Matrix ι ι ℝ} (hA : Aᵀ = A) {E : Matrix ι ι ℝ}
    (hE : IsOrthProj E) {O : Matrix ι κ ℝ} (hO : O * Oᵀ = 1) (W : Matrix ι κ ℝ) (η : ℝ) :
    loss A (W - η • (E * O)) - loss A W
      = -η * frob (E * A * W) O + η ^ 2 / 2 * (E * A).trace := by
  have h1 : frob (A * W) (E * O) = frob (E * A * W) O := by
    rw [frob_comm, frob_mul_left, hE.symm, frob_comm, Matrix.mul_assoc]
  have h2 : ((E * O)ᵀ * A * (E * O)).trace = (E * A).trace := by
    calc ((E * O)ᵀ * A * (E * O)).trace = (Oᵀ * (E * A * E * O)).trace := by
          rw [transpose_mul, hE.symm]; simp only [Matrix.mul_assoc]
      _ = (E * A * E * (O * Oᵀ)).trace := by rw [trace_mul_comm, Matrix.mul_assoc]
      _ = (E * A * E).trace := by rw [hO, Matrix.mul_one]
      _ = (E * A).trace := by rw [trace_mul_comm, ← Matrix.mul_assoc, hE.idem]
  rw [matrixMuon_loss_step hA, h1, h2]
  ring

/-- **Spec 5.2 for a stochastic gradient.** If `(S, O)` is a left polar pair of *any* matrix `G`
(e.g. the noisy gradient `A W + noise`), the projected Muon step along `O` changes the loss by
`-η ⟪E A W, O⟫ + (η²/2) tr(E A)`: the second-order term does not depend on `W`, `G` or the noise. -/
theorem matrixMuon_loss_projected_step_noisy {A : Matrix ι ι ℝ} (hA : Aᵀ = A) {E : Matrix ι ι ℝ}
    (hE : IsOrthProj E) {G : Matrix ι κ ℝ} {S : Matrix ι ι ℝ} {O : Matrix ι κ ℝ}
    (h : IsLeftPolar G S O) (W : Matrix ι κ ℝ) (η : ℝ) :
    loss A (W - η • (E * O)) - loss A W
      = -η * frob (E * A * W) O + η ^ 2 / 2 * (E * A).trace :=
  matrixMuon_loss_projected_step hA hE h.orth W η

/-- Spec 5.2 with `E = 1` (the full Muon step): `L(W - η O) - L(W) = -η ⟪A W, O⟫ + (η²/2) tr A`. -/
theorem matrixMuon_loss_full_step {A : Matrix ι ι ℝ} (hA : Aᵀ = A) {O : Matrix ι κ ℝ}
    (hO : O * Oᵀ = 1) (W : Matrix ι κ ℝ) (η : ℝ) :
    loss A (W - η • O) - loss A W = -η * frob (A * W) O + η ^ 2 / 2 * A.trace := by
  have h := matrixMuon_loss_projected_step hA (isOrthProj_one (ι := ι)) hO W η
  simpa only [Matrix.one_mul] using h

/-- If `E` commutes with `A` (the situation of the spec, `E = P^𝒟` or `P^ℬ`), then `E A W` is the
gradient at the projected point: `E A W = A (E W)`. -/
theorem matrixMuon_proj_grad_of_commute {A E : Matrix ι ι ℝ} (hEA : E * A = A * E)
    (W : Matrix ι κ ℝ) : E * A * W = A * (E * W) := by
  rw [hEA, Matrix.mul_assoc]

/-- The symmetry of `A` cannot be dropped in spec 5.2: for `A = [[0,1],[0,0]]`,
`W = [[0,-1],[1,0]]`, `E = O = 1`, `η = 1` the left side is `0` and the right side is `-1`. -/
theorem matrixMuon_loss_projected_step_needs_symm :
    ∃ (A E : Matrix (Fin 2) (Fin 2) ℝ) (W O : Matrix (Fin 2) (Fin 2) ℝ) (η : ℝ),
      IsOrthProj E ∧ O * Oᵀ = 1 ∧
        loss A (W - η • (E * O)) - loss A W
          ≠ -η * frob (E * A * W) O + η ^ 2 / 2 * (E * A).trace := by
  refine ⟨!![0, 1; 0, 0], 1, !![0, -1; 1, 0], 1, 1, isOrthProj_one, by simp, ?_⟩
  simp [loss, frob, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## 5.3 Noise-free threshold -/

/-- **Spec 5.3.** If `O Oᵀ = 1` then `⟪E S O, O⟫ = tr(E S)` for all square `E`, `S`. -/
theorem matrixMuon_frob_mul_mul_orth {O : Matrix ι κ ℝ} (hO : O * Oᵀ = 1) (E S : Matrix ι ι ℝ) :
    frob (E * (S * O)) O = (E * S).trace := by
  rw [frob_comm, frob, ← Matrix.mul_assoc, ← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, hO, Matrix.one_mul]

/-- **Spec 5.3.** Noise-free case `A W = S O` (left polar pair): `⟪E A W, O⟫ = tr(E S)`. -/
theorem matrixMuon_frob_proj_grad {A : Matrix ι ι ℝ} {W : Matrix ι κ ℝ} {S : Matrix ι ι ℝ}
    {O : Matrix ι κ ℝ} (h : IsLeftPolar (A * W) S O) (E : Matrix ι ι ℝ) :
    frob (E * A * W) O = (E * S).trace := by
  rw [Matrix.mul_assoc, h.eq, matrixMuon_frob_mul_mul_orth h.orth]

/-- **Spec 5.3 (`E = 1`).** For a left polar pair, `⟪G, O⟫ = tr S` (the nuclear norm of `G`). -/
theorem matrixMuon_frob_grad_polar {G : Matrix ι κ ℝ} {S : Matrix ι ι ℝ} {O : Matrix ι κ ℝ}
    (h : IsLeftPolar G S O) : frob G O = S.trace := by
  have := matrixMuon_frob_mul_mul_orth h.orth 1 S
  rwa [Matrix.one_mul, Matrix.one_mul, ← h.eq] at this

/-- **Spec 5.3.** Exact loss change of the noise-free projected Muon step:
`L(W - η E O) - L(W) = -η tr(E S) + (η²/2) tr(E A)`. -/
theorem matrixMuon_loss_projected_step_noiseFree {A : Matrix ι ι ℝ} (hA : Aᵀ = A)
    {E : Matrix ι ι ℝ} (hE : IsOrthProj E) {W : Matrix ι κ ℝ} {S : Matrix ι ι ℝ}
    {O : Matrix ι κ ℝ} (h : IsLeftPolar (A * W) S O) (η : ℝ) :
    loss A (W - η • (E * O)) - loss A W = -η * (E * S).trace + η ^ 2 / 2 * (E * A).trace := by
  rw [matrixMuon_loss_projected_step hA hE h.orth, matrixMuon_frob_proj_grad h]

/-- **Spec 5.3 (noise-free loss threshold).** If `A W = S O` is a left polar pair, `E` is an
orthogonal projector and `tr(E A) > 0`, then the projected Muon step decreases the loss iff
`0 < η < 2 tr(E S) / tr(E A)`.

(The spec also assumes `tr(E S) > 0`; this is only needed for the interval to be nonempty, see
`matrixMuon_threshold_pos`; `tr(E S) ≥ 0` is automatic.) -/
theorem matrixMuon_loss_decrease_iff {A : Matrix ι ι ℝ} (hA : Aᵀ = A) {E : Matrix ι ι ℝ}
    (hE : IsOrthProj E) {W : Matrix ι κ ℝ} {S : Matrix ι ι ℝ} {O : Matrix ι κ ℝ}
    (h : IsLeftPolar (A * W) S O) (hEA : 0 < (E * A).trace) (η : ℝ) :
    loss A (W - η • (E * O)) < loss A W ↔ 0 < η ∧ η < 2 * (E * S).trace / (E * A).trace := by
  have hs : 0 ≤ (E * S).trace := hE.trace_mul_nonneg h.posSemidef
  have key := matrixMuon_loss_projected_step_noiseFree hA hE h η
  rw [← sub_neg, key, lt_div_iff₀ hEA]
  constructor
  · intro hlt
    have hη : 0 < η := by
      by_contra hcon
      rw [not_lt] at hcon
      nlinarith [mul_nonneg hs (neg_nonneg.mpr hcon), mul_nonneg (sq_nonneg η) hEA.le]
    refine ⟨hη, ?_⟩
    nlinarith
  · rintro ⟨hη, hlt⟩
    nlinarith

/-- **Spec 5.3.** Under the same hypotheses the projected Muon step increases the loss iff
`η < 0` or `η > 2 tr(E S) / tr(E A)`. -/
theorem matrixMuon_loss_increase_iff {A : Matrix ι ι ℝ} (hA : Aᵀ = A) {E : Matrix ι ι ℝ}
    (hE : IsOrthProj E) {W : Matrix ι κ ℝ} {S : Matrix ι ι ℝ} {O : Matrix ι κ ℝ}
    (h : IsLeftPolar (A * W) S O) (hEA : 0 < (E * A).trace) (η : ℝ) :
    loss A W < loss A (W - η • (E * O)) ↔ η < 0 ∨ 2 * (E * S).trace / (E * A).trace < η := by
  have hs : 0 ≤ (E * S).trace := hE.trace_mul_nonneg h.posSemidef
  have key := matrixMuon_loss_projected_step_noiseFree hA hE h η
  rw [← sub_pos, key, div_lt_iff₀ hEA]
  constructor
  · intro hgt
    by_contra hcon
    rw [not_or, not_lt, not_lt] at hcon
    obtain ⟨h0, h1⟩ := hcon
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
  · rintro (hη | hη)
    · nlinarith [mul_nonneg (neg_nonneg.mpr hη.le) hs, mul_pos (mul_pos_of_neg_of_neg hη hη) hEA]
    · have hη0 : 0 < η := by
        by_contra hcon
        rw [not_lt] at hcon
        nlinarith [mul_nonneg (neg_nonneg.mpr hcon) hEA.le]
      nlinarith [mul_pos hη0 (sub_pos.mpr hη)]

/-- **Spec 5.3.** Under the same hypotheses the projected Muon step leaves the loss unchanged iff
`η = 0` or `η = 2 tr(E S) / tr(E A)`. -/
theorem matrixMuon_loss_eq_iff {A : Matrix ι ι ℝ} (hA : Aᵀ = A) {E : Matrix ι ι ℝ}
    (hE : IsOrthProj E) {W : Matrix ι κ ℝ} {S : Matrix ι ι ℝ} {O : Matrix ι κ ℝ}
    (h : IsLeftPolar (A * W) S O) (hEA : 0 < (E * A).trace) (η : ℝ) :
    loss A (W - η • (E * O)) = loss A W ↔ η = 0 ∨ η = 2 * (E * S).trace / (E * A).trace := by
  have key := matrixMuon_loss_projected_step_noiseFree hA hE h η
  have hfac : -η * (E * S).trace + η ^ 2 / 2 * (E * A).trace
      = η * (η * (E * A).trace - 2 * (E * S).trace) / 2 := by ring
  rw [← sub_eq_zero, key, eq_div_iff hEA.ne', hfac, div_eq_zero_iff, mul_eq_zero, sub_eq_zero]
  simp

/-- The noise-free Muon loss threshold `2 tr(E S)/tr(E A)` is positive when both traces are. -/
theorem matrixMuon_threshold_pos {A S E : Matrix ι ι ℝ} (hEA : 0 < (E * A).trace)
    (hES : 0 < (E * S).trace) : 0 < 2 * (E * S).trace / (E * A).trace := by
  positivity

/-! ## 5.4 Existence and uniqueness of the left polar pair -/

section Polar

open scoped MatrixOrder

namespace MatrixMuon

variable {G : Matrix ι κ ℝ} {S : Matrix ι ι ℝ} {O : Matrix ι κ ℝ}

/-- The positive semidefinite factor of a left polar pair is symmetric. -/
theorem IsLeftPolar.symm (h : IsLeftPolar G S O) : Sᵀ = S :=
  (conjTranspose_eq_transpose_of_trivial S).symm.trans h.posSemidef.1

/-- In a left polar pair, `S² = G Gᵀ`. -/
theorem IsLeftPolar.mul_self (h : IsLeftPolar G S O) : S * S = G * Gᵀ := by
  rw [h.eq, transpose_mul, h.symm, Matrix.mul_assoc, ← Matrix.mul_assoc O, h.orth, Matrix.one_mul]

/-- In a left polar pair, `S = (G Gᵀ)^{1/2}` (Mathlib's `CFC.sqrt`); in particular `S` is
determined by `G`, with no rank assumption. -/
theorem IsLeftPolar.eq_sqrt (h : IsLeftPolar G S O) : S = CFC.sqrt (G * Gᵀ) :=
  (CFC.sqrt_unique h.mul_self h.posSemidef.nonneg).symm

/-- A left polar pair can only exist for wide matrices: `d ≤ n`. -/
theorem IsLeftPolar.card_le (h : IsLeftPolar G S O) : Fintype.card ι ≤ Fintype.card κ := by
  have h1 : (O * Oᵀ).rank = Fintype.card ι := by rw [h.orth, rank_one]
  calc Fintype.card ι = (O * Oᵀ).rank := h1.symm
    _ ≤ O.rank := rank_mul_le_left _ _
    _ ≤ Fintype.card κ := rank_le_card_width _

/-- If `G Gᵀ` is positive definite, the factor `S` of a left polar pair is invertible. -/
theorem IsLeftPolar.isUnit_det (h : IsLeftPolar G S O) (hG : (G * Gᵀ).PosDef) :
    IsUnit S.det := by
  have h1 : S.det * S.det = (G * Gᵀ).det := by rw [← det_mul, h.mul_self]
  have h2 := hG.det_pos
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [h0, mul_zero] at h1
  linarith

/-- If `G Gᵀ` is positive definite, the factor `S` of a left polar pair is positive definite. -/
theorem IsLeftPolar.posDef (h : IsLeftPolar G S O) (hG : (G * Gᵀ).PosDef) : S.PosDef :=
  h.posSemidef.posDef_iff_det_ne_zero.mpr (h.isUnit_det hG).ne_zero

/-- If `G Gᵀ` is positive definite, the orthogonal factor is `O = S⁻¹ G`. -/
theorem IsLeftPolar.O_eq (h : IsLeftPolar G S O) (hG : (G * Gᵀ).PosDef) : O = S⁻¹ * G := by
  have hdet := h.isUnit_det hG
  rw [h.eq, nonsing_inv_mul_cancel_left _ _ hdet]

/-- Existence from a given square root: if `S` is positive semidefinite, invertible and
`S² = G Gᵀ`, then `(S, S⁻¹ G)` is a left polar pair of `G`. -/
theorem isLeftPolar_of_mul_self (hS : S.PosSemidef) (hSS : S * S = G * Gᵀ)
    (hdet : IsUnit S.det) : IsLeftPolar G S (S⁻¹ * G) := by
  have hsymm : Sᵀ = S := (conjTranspose_eq_transpose_of_trivial S).symm.trans hS.1
  refine ⟨hS, ?_, (mul_nonsing_inv_cancel_left _ _ hdet).symm⟩
  calc S⁻¹ * G * (S⁻¹ * G)ᵀ = S⁻¹ * (G * Gᵀ) * S⁻¹ := by
        rw [transpose_mul, transpose_nonsing_inv, hsymm]
        simp only [Matrix.mul_assoc]
    _ = S⁻¹ * S * (S * S⁻¹) := by
        rw [← hSS]
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [nonsing_inv_mul _ hdet, mul_nonsing_inv _ hdet, Matrix.one_mul]

/-- `tr(E M) > 0` for a nonzero orthogonal projector `E` and a positive definite `M`. -/
theorem IsOrthProj.trace_mul_pos {E : Matrix ι ι ℝ} (h : IsOrthProj E) (hE : E ≠ 0)
    {M : Matrix ι ι ℝ} (hM : M.PosDef) : 0 < (E * M).trace := by
  have hB : (CFC.sqrt M).PosSemidef := (CFC.sqrt_nonneg M).posSemidef
  have hBB : CFC.sqrt M * CFC.sqrt M = M := CFC.sqrt_mul_sqrt_self M hM.posSemidef.nonneg
  have hBsymm : (CFC.sqrt M)ᵀ = CFC.sqrt M :=
    (conjTranspose_eq_transpose_of_trivial _).symm.trans hB.1
  have hBdet : IsUnit (CFC.sqrt M).det := by
    rw [← isUnit_iff_isUnit_det, CFC.isUnit_sqrt_iff M hM.posSemidef.nonneg]
    exact hM.isUnit
  have key : (E * M).trace = frob (CFC.sqrt M * E) (CFC.sqrt M * E) := by
    rw [h.trace_mul, frob, transpose_mul, hBsymm]
    conv_lhs => rw [← hBB]
    simp only [Matrix.mul_assoc]
  rw [key]
  refine lt_of_le_of_ne (frob_self_nonneg _) (Ne.symm ?_)
  rw [Ne, frob_self_eq_zero_iff]
  intro h0
  apply hE
  calc E = (CFC.sqrt M)⁻¹ * (CFC.sqrt M * E) := (nonsing_inv_mul_cancel_left _ _ hBdet).symm
    _ = 0 := by rw [h0, Matrix.mul_zero]

end MatrixMuon

variable {G : Matrix ι κ ℝ}

/-- **Spec 5.4 (existence, explicit).** If `G Gᵀ` is positive definite then
`S = (G Gᵀ)^{1/2}` (Mathlib's `CFC.sqrt`), `O = S⁻¹ G` is a left polar pair of `G`. -/
theorem matrixMuon_isLeftPolar_sqrt (hG : (G * Gᵀ).PosDef) :
    IsLeftPolar G (CFC.sqrt (G * Gᵀ)) ((CFC.sqrt (G * Gᵀ))⁻¹ * G) := by
  have hS : (CFC.sqrt (G * Gᵀ)).PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have hSS : CFC.sqrt (G * Gᵀ) * CFC.sqrt (G * Gᵀ) = G * Gᵀ :=
    CFC.sqrt_mul_sqrt_self _ hG.posSemidef.nonneg
  have hdet : IsUnit (CFC.sqrt (G * Gᵀ)).det := by
    rw [← isUnit_iff_isUnit_det, CFC.isUnit_sqrt_iff _ hG.posSemidef.nonneg]
    exact hG.isUnit
  exact isLeftPolar_of_mul_self hS hSS hdet

/-- **Spec 5.4 (existence).** If `G Gᵀ` is positive definite then `G` has a left polar pair. -/
theorem matrixMuon_exists_leftPolar (hG : (G * Gᵀ).PosDef) :
    ∃ (S : Matrix ι ι ℝ) (O : Matrix ι κ ℝ), IsLeftPolar G S O :=
  ⟨_, _, matrixMuon_isLeftPolar_sqrt hG⟩

/-- **Spec 5.4 (uniqueness).** If `G Gᵀ` is positive definite, any two left polar pairs of `G`
coincide. -/
theorem matrixMuon_leftPolar_unique (hG : (G * Gᵀ).PosDef) {S₁ S₂ : Matrix ι ι ℝ}
    {O₁ O₂ : Matrix ι κ ℝ} (h₁ : IsLeftPolar G S₁ O₁) (h₂ : IsLeftPolar G S₂ O₂) :
    S₁ = S₂ ∧ O₁ = O₂ := by
  have hS : S₁ = S₂ := h₁.eq_sqrt.trans h₂.eq_sqrt.symm
  refine ⟨hS, ?_⟩
  rw [h₁.O_eq hG, h₂.O_eq hG, hS]

/-- **Spec 5.4 (existence and uniqueness).** If `G Gᵀ` is positive definite then `G` has exactly
one left polar pair. -/
theorem matrixMuon_existsUnique_leftPolar (hG : (G * Gᵀ).PosDef) :
    ∃! p : Matrix ι ι ℝ × Matrix ι κ ℝ, IsLeftPolar G p.1 p.2 := by
  refine ⟨(_, _), matrixMuon_isLeftPolar_sqrt hG, ?_⟩
  rintro ⟨S, O⟩ h
  obtain ⟨h1, h2⟩ := matrixMuon_leftPolar_unique hG h (matrixMuon_isLeftPolar_sqrt hG)
  exact Prod.ext h1 h2

/-- **Spec 5.4 (characterisation).** If `G Gᵀ` is positive definite, `(S, O)` is a left polar pair
of `G` iff `S = (G Gᵀ)^{1/2}` and `O = S⁻¹ G`. -/
theorem matrixMuon_isLeftPolar_iff (hG : (G * Gᵀ).PosDef) {S : Matrix ι ι ℝ}
    {O : Matrix ι κ ℝ} :
    IsLeftPolar G S O ↔ S = CFC.sqrt (G * Gᵀ) ∧ O = (CFC.sqrt (G * Gᵀ))⁻¹ * G := by
  constructor
  · intro h
    exact matrixMuon_leftPolar_unique hG h (matrixMuon_isLeftPolar_sqrt hG)
  · rintro ⟨rfl, rfl⟩
    exact matrixMuon_isLeftPolar_sqrt hG

/-- `G Gᵀ` is always positive semidefinite, so "`G Gᵀ` invertible" (the wording of the spec) is
the same as "`G Gᵀ` positive definite". -/
theorem matrixMuon_posDef_iff_isUnit_det : (G * Gᵀ).PosDef ↔ IsUnit (G * Gᵀ).det := by
  have hpsd : (G * Gᵀ).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose G
  rw [hpsd.posDef_iff_det_ne_zero, isUnit_iff_ne_zero]

/-- Positive definiteness of `G Gᵀ` forces `d ≤ n` (spec §5, preamble). -/
theorem matrixMuon_card_le_of_posDef (hG : (G * Gᵀ).PosDef) :
    Fintype.card ι ≤ Fintype.card κ :=
  (matrixMuon_isLeftPolar_sqrt hG).card_le

/-- Muon's direction is a strict descent direction of the linearised loss: `⟪G, O⟫ > 0` for every
left polar pair of a nonzero `G`. -/
theorem matrixMuon_frob_grad_polar_pos {S : Matrix ι ι ℝ} {O : Matrix ι κ ℝ}
    (h : IsLeftPolar G S O) (hG : G ≠ 0) : 0 < frob G O := by
  rw [matrixMuon_frob_grad_polar h]
  refine lt_of_le_of_ne h.posSemidef.trace_nonneg (Ne.symm ?_)
  intro h0
  apply hG
  rw [h.eq, h.posSemidef.trace_eq_zero_iff.mp h0, Matrix.zero_mul]

/-- The trace of the positive semidefinite square root is the sum of the square roots of the
eigenvalues. -/
theorem MatrixMuon.trace_sqrt {M : Matrix ι ι ℝ} (hM : M.PosSemidef) :
    (CFC.sqrt M).trace = ∑ i, Real.sqrt (hM.1.eigenvalues i) := by
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ M hM.nonneg, hM.1.cfc_eq, IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply, trace_mul_comm, ← Matrix.mul_assoc]
  simp only [Unitary.coe_star_mul_self, Matrix.one_mul, trace_diagonal, Function.comp_apply,
    Real.coe_sqrt, Real.coe_toNNReal', RCLike.ofReal_real_eq_id, id_eq]
  exact Finset.sum_congr rfl fun i _ => by rw [max_eq_left (hM.eigenvalues_nonneg i)]

/-- **Spec 5.3, "the nuclear norm of `G`".** For a left polar pair, `⟪G, O⟫ = tr S` is the sum of
the singular values of `G`, i.e. of the square roots of the eigenvalues of `G Gᵀ`. -/
theorem matrixMuon_frob_grad_polar_eq_nuclear {S : Matrix ι ι ℝ} {O : Matrix ι κ ℝ}
    (h : IsLeftPolar G S O) (hH : (G * Gᵀ).IsHermitian) :
    frob G O = ∑ i, Real.sqrt (hH.eigenvalues i) := by
  have hpsd : (G * Gᵀ).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose G
  rw [matrixMuon_frob_grad_polar h, h.eq_sqrt, MatrixMuon.trace_sqrt hpsd]

/-- Without positive definiteness of `G Gᵀ` the orthogonal factor is **not** unique:
`G = 0` (`d = n = 1`) has the left polar pairs `(0, 1)` and `(0, -1)`. -/
theorem matrixMuon_leftPolar_not_unique :
    IsLeftPolar (0 : Matrix (Fin 1) (Fin 1) ℝ) 0 1 ∧
      IsLeftPolar (0 : Matrix (Fin 1) (Fin 1) ℝ) 0 (-1) ∧
      (1 : Matrix (Fin 1) (Fin 1) ℝ) ≠ -1 := by
  refine ⟨⟨PosSemidef.zero, by simp, by simp⟩, ⟨PosSemidef.zero, by simp, by simp⟩, ?_⟩
  intro h
  have := congrFun (congrFun h 0) 0
  norm_num at this

/-- In the noise-free setting with `A` and `G Gᵀ = (A W)(A W)ᵀ` positive definite, both traces in
the Muon threshold `2 tr(E S)/tr(E A)` are positive for every nonzero orthogonal projector `E`:
the hypotheses of `matrixMuon_loss_decrease_iff` / `matrixMuon_loss_increase_iff` hold
automatically. -/
theorem matrixMuon_traces_pos {A : Matrix ι ι ℝ} (hA : A.PosDef) {W : Matrix ι κ ℝ}
    {S : Matrix ι ι ℝ} {O : Matrix ι κ ℝ} (h : IsLeftPolar (A * W) S O)
    (hG : ((A * W) * (A * W)ᵀ).PosDef) {E : Matrix ι ι ℝ} (hE : IsOrthProj E) (hE0 : E ≠ 0) :
    0 < (E * A).trace ∧ 0 < (E * S).trace :=
  ⟨hE.trace_mul_pos hE0 hA, hE.trace_mul_pos hE0 (h.posDef hG)⟩

end Polar

/-! ## 5.5 Link with the coordinate model -/

namespace MatrixMuon

/-- Row `i` of `diag(r) Q` is `r_i` times row `i` of `Q`. -/
theorem diagonal_mul_row (r : ι → ℝ) (Q : Matrix ι κ ℝ) (i : ι) :
    (diagonal r * Q) i = r i • Q i := by
  ext j
  simp [diagonal_mul]

theorem realSign_mul_self {c : ℝ} (hc : c ≠ 0) : Real.sign c * Real.sign c = 1 := by
  rcases lt_or_gt_of_ne hc with h | h
  · rw [Real.sign_of_neg h]; norm_num
  · rw [Real.sign_of_pos h]; norm_num

theorem abs_mul_realSign (c : ℝ) : |c| * Real.sign c = c := by
  rcases lt_trichotomy c 0 with h | h | h
  · rw [Real.sign_of_neg h, abs_of_neg h]; ring
  · rw [h]; simp
  · rw [Real.sign_of_pos h, abs_of_pos h]; ring

theorem realSign_pos_mul {a : ℝ} (ha : 0 < a) (c : ℝ) : Real.sign (a * c) = Real.sign c := by
  rcases lt_trichotomy c 0 with h | h | h
  · rw [Real.sign_of_neg h, Real.sign_of_neg (mul_neg_of_pos_of_neg ha h)]
  · rw [h]; simp
  · rw [Real.sign_of_pos h, Real.sign_of_pos (mul_pos ha h)]

/-- `‖diag(v) Q‖_F² = ∑ v_i²` when `Q Qᵀ = 1`. -/
theorem frob_diagonal_mul_orth {Q : Matrix ι κ ℝ} (hQ : Q * Qᵀ = 1) (v : ι → ℝ) :
    frob (diagonal v * Q) (diagonal v * Q) = ∑ i, v i ^ 2 := by
  rw [matrixMuon_frob_mul_orth hQ, frob, diagonal_transpose, diagonal_mul_diagonal,
    trace_diagonal]
  simp only [sq]

/-- `Π_T diag(v) = diag(1_T v)`. -/
theorem coordProj_mul_diagonal (T : Finset ι) (v : ι → ℝ) :
    coordProj T * diagonal v = diagonal fun i => if i ∈ T then v i else 0 := by
  rw [coordProj, diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

/-- `‖Π_T diag(v) Q‖_F² = ∑_{i∈T} v_i²` when `Q Qᵀ = 1`. -/
theorem frob_coordProj_diagonal_mul_orth {Q : Matrix ι κ ℝ} (hQ : Q * Qᵀ = 1) (T : Finset ι)
    (v : ι → ℝ) :
    frob (coordProj T * (diagonal v * Q)) (coordProj T * (diagonal v * Q)) = ∑ i ∈ T, v i ^ 2 := by
  rw [← Matrix.mul_assoc, coordProj_mul_diagonal, frob_diagonal_mul_orth hQ]
  simp only [ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

end MatrixMuon

section Coordinate

variable {σ lam c : ι → ℝ} {Q : Matrix ι κ ℝ}

/-- **Spec 5.5.** If `σ_i ≥ 0` and `Q Qᵀ = 1`, then `(diag(σ), Q)` is a left polar pair of
`G = diag(σ) Q`. -/
theorem matrixMuon_isLeftPolar_diagonal (hσ : ∀ i, 0 ≤ σ i) (hQ : Q * Qᵀ = 1) :
    IsLeftPolar (diagonal σ * Q) (diagonal σ) Q :=
  ⟨PosSemidef.diagonal hσ, hQ, rfl⟩

/-- For `G = diag(σ) Q` with `σ_i ≠ 0` and `Q Qᵀ = 1`, `G Gᵀ = diag(σ²)` is positive definite. -/
theorem matrixMuon_posDef_diagonal_mul (hσ : ∀ i, σ i ≠ 0) (hQ : Q * Qᵀ = 1) :
    ((diagonal σ * Q) * (diagonal σ * Q)ᵀ).PosDef := by
  have h : diagonal σ * Q * (diagonal σ * Q)ᵀ = diagonal fun i => σ i * σ i := by
    rw [transpose_mul, diagonal_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc Q, hQ,
      Matrix.one_mul, diagonal_mul_diagonal]
  rw [h]
  exact PosDef.diagonal fun i => mul_self_pos.mpr (hσ i)

/-- **Spec 5.5 (with uniqueness).** If `σ_i > 0` and `Q Qᵀ = 1`, then `(diag(σ), Q)` is *the* left
polar pair of `G = diag(σ) Q`: Muon's update direction is `O = Q`. -/
theorem matrixMuon_leftPolar_diagonal_unique (hσ : ∀ i, 0 < σ i) (hQ : Q * Qᵀ = 1)
    {S : Matrix ι ι ℝ} {O : Matrix ι κ ℝ} (h : IsLeftPolar (diagonal σ * Q) S O) :
    S = diagonal σ ∧ O = Q :=
  matrixMuon_leftPolar_unique (matrixMuon_posDef_diagonal_mul (fun i => (hσ i).ne') hQ) h
    (matrixMuon_isLeftPolar_diagonal (fun i => (hσ i).le) hQ)

/-- **Spec 5.5.** For the coordinate projector on `T`, `S = diag(σ)` and `A = diag(λ)`:
`tr(Π_T S) / tr(Π_T A) = ∑_{i∈T} σ_i / ∑_{i∈T} λ_i`, so the matrix Muon threshold
`2 tr(Π S)/tr(Π A)` of 5.3 is the coordinate Muon threshold of spec 2.4. -/
theorem matrixMuon_trace_ratio_coordProj (T : Finset ι) (σ lam : ι → ℝ) :
    (coordProj T * diagonal σ).trace / (coordProj T * diagonal lam).trace
      = (∑ i ∈ T, σ i) / ∑ i ∈ T, lam i := by
  rw [trace_coordProj_mul_diagonal, trace_coordProj_mul_diagonal]

/-- **Spec 5.5 (commuting state, unsigned).** With `G = diag(σ) Q`, `σ_i > 0`, the Muon step from
`W = diag(r) Q` is `W - η O = diag(r - η) Q`: row `i` moves to `(r_i - η) · (row i of Q)`.
For `r_i > 0` this is the coordinate rule `c_i⁺ = c_i - η sign(c_i)` of spec §1. -/
theorem matrixMuon_step_row (hσ : ∀ i, 0 < σ i) (hQ : Q * Qᵀ = 1) {S : Matrix ι ι ℝ}
    {O : Matrix ι κ ℝ} (h : IsLeftPolar (diagonal σ * Q) S O) (r : ι → ℝ) (η : ℝ) (i : ι) :
    (diagonal r * Q - η • O) i = (r i - η) • Q i := by
  obtain ⟨-, rfl⟩ := matrixMuon_leftPolar_diagonal_unique hσ hQ h
  ext j
  simp [diagonal_mul, sub_mul]

/-- **Spec 5.5 (signed commuting state).** For `A = diag(λ)`, `λ_i > 0`, and `W = diag(c) Q` with
`c_i ≠ 0`, `Q Qᵀ = 1`, the clean gradient `A W = diag(λ_i c_i) Q` has the left polar pair
`S = diag(λ_i |c_i|)`, `O = diag(sign c_i) Q`. -/
theorem matrixMuon_isLeftPolar_coordinate (hlam : ∀ i, 0 < lam i) (hc : ∀ i, c i ≠ 0)
    (hQ : Q * Qᵀ = 1) :
    IsLeftPolar (diagonal lam * (diagonal c * Q)) (diagonal fun i => lam i * |c i|)
      (diagonal (fun i => Real.sign (c i)) * Q) := by
  refine ⟨PosSemidef.diagonal fun i => mul_nonneg (hlam i).le (abs_nonneg _), ?_, ?_⟩
  · rw [transpose_mul, diagonal_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc Q, hQ,
      Matrix.one_mul, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact realSign_mul_self (hc i)
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 2
    funext i
    rw [mul_assoc, abs_mul_realSign]

/-- In the coordinate model, `G Gᵀ` is positive definite (all `λ_i > 0`, `c_i ≠ 0`). -/
theorem matrixMuon_posDef_coordinate (hlam : ∀ i, 0 < lam i) (hc : ∀ i, c i ≠ 0)
    (hQ : Q * Qᵀ = 1) :
    ((diagonal lam * (diagonal c * Q)) * (diagonal lam * (diagonal c * Q))ᵀ).PosDef := by
  have h : diagonal lam * (diagonal c * Q) = diagonal (fun i => lam i * c i) * Q := by
    rw [← Matrix.mul_assoc, diagonal_mul_diagonal]
  rw [h]
  exact matrixMuon_posDef_diagonal_mul (fun i => mul_ne_zero (hlam i).ne' (hc i)) hQ

/-- **Spec 5.5 / (1.0), matrix-level justification of the coordinate model for Muon.**
`A = diag(λ)`, `λ_i > 0`; `W = diag(c) Q` with `c_i ≠ 0`, `Q Qᵀ = 1`; `(S, O)` any left polar
pair of the clean gradient `A W`.  Then the Muon step is
`W - η O = diag(c_i - η sign(c_i)) Q`: the state stays commuting with the same frame `Q`, and the
signed coefficients follow `c_i⁺ = c_i - η sign(c_i)`. -/
theorem matrixMuon_coordinate_step (hlam : ∀ i, 0 < lam i) (hc : ∀ i, c i ≠ 0)
    (hQ : Q * Qᵀ = 1) {S : Matrix ι ι ℝ} {O : Matrix ι κ ℝ}
    (h : IsLeftPolar (diagonal lam * (diagonal c * Q)) S O) (η : ℝ) :
    diagonal c * Q - η • O = diagonal (fun i => c i - η * Real.sign (c i)) * Q := by
  obtain ⟨-, rfl⟩ := matrixMuon_leftPolar_unique (matrixMuon_posDef_coordinate hlam hc hQ) h
    (matrixMuon_isLeftPolar_coordinate hlam hc hQ)
  ext i j
  simp [diagonal_mul, sub_mul, mul_assoc]

/-- Row form of `matrixMuon_coordinate_step`: row `i` of `W - η O` is
`(c_i - η sign(c_i)) · (row i of Q)`. -/
theorem matrixMuon_coordinate_step_row (hlam : ∀ i, 0 < lam i) (hc : ∀ i, c i ≠ 0)
    (hQ : Q * Qᵀ = 1) {S : Matrix ι ι ℝ} {O : Matrix ι κ ℝ}
    (h : IsLeftPolar (diagonal lam * (diagonal c * Q)) S O) (η : ℝ) (i : ι) :
    (diagonal c * Q - η • O) i = (c i - η * Real.sign (c i)) • Q i := by
  rw [matrixMuon_coordinate_step hlam hc hQ h, diagonal_mul_row]

end Coordinate

/-! ## General spectral filters `F(G) = f(S) O` (no SVD needed)

For the SVD `G = U Σ Vᵀ` the spec's filtered update is `F(G) = U f(Σ) Vᵀ`.  In terms of the left
polar pair `S = U Σ Uᵀ`, `O = U Vᵀ` this is `F(G) = f(S) O`, with `f(S)` the functional calculus
of the symmetric matrix `S` (Mathlib's `cfc`).  SGD is `f = id`, Muon is `f ≡ 1`. -/

namespace MatrixMuon

/-- Intertwining lemma: if `diag(a) X = X diag(b)` then `diag(f ∘ a) X = X diag(f ∘ b)`. -/
theorem diagonal_intertwine {m : Type*} [Fintype m] [DecidableEq m] (f : ℝ → ℝ) {a : ι → ℝ}
    {b : m → ℝ} {X : Matrix ι m ℝ} (h : diagonal a * X = X * diagonal b) :
    diagonal (fun i => f (a i)) * X = X * diagonal (fun j => f (b j)) := by
  ext i j
  have hij := congrFun (congrFun h i) j
  rw [diagonal_mul, mul_diagonal] at hij
  rw [diagonal_mul, mul_diagonal]
  by_cases hX : X i j = 0
  · simp [hX]
  · have hab : a i = b j := by
      have h' : (a i - b j) * X i j = 0 := by linarith
      rcases mul_eq_zero.mp h' with h0 | h0
      · linarith
      · exact absurd h0 hX
    rw [hab, mul_comm]

/-- Functional calculus of an orthogonally diagonalised matrix: if `M = U diag(σ) Uᵀ` with
`U Uᵀ = 1`, then `f(M) = U diag(f ∘ σ) Uᵀ` (for every function `f`, any diagonalisation). -/
theorem cfc_eq_of_eq_conj_diagonal (f : ℝ → ℝ) {U : Matrix ι ι ℝ} (hU : U * Uᵀ = 1) (σ : ι → ℝ)
    {M : Matrix ι ι ℝ} (hM : M = U * diagonal σ * Uᵀ) :
    cfc f M = U * diagonal (fun i => f (σ i)) * Uᵀ := by
  have hU' : Uᵀ * U = 1 := mul_eq_one_comm.mp hU
  have hH : M.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hM]
    simp [transpose_mul, Matrix.mul_assoc]
  rw [hH.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  set V : Matrix ι ι ℝ := (hH.eigenvectorUnitary : Matrix ι ι ℝ) with hV
  have hVV : V * star V = 1 := Unitary.coe_mul_star_self _
  have hVV' : star V * V = 1 := Unitary.coe_star_mul_self _
  have hspec : M = V * diagonal hH.eigenvalues * star V := by
    conv_lhs => rw [hH.spectral_theorem, Unitary.conjStarAlgAut_apply]
    simp [hV]
  have hint : diagonal σ * (Uᵀ * V) = (Uᵀ * V) * diagonal hH.eigenvalues := by
    have h1 : Uᵀ * (U * diagonal σ * Uᵀ) * V
        = Uᵀ * (V * diagonal hH.eigenvalues * star V) * V :=
      congrArg (fun X => Uᵀ * X * V) (hM.symm.trans hspec)
    calc diagonal σ * (Uᵀ * V) = (Uᵀ * U) * diagonal σ * (Uᵀ * V) := by rw [hU', Matrix.one_mul]
      _ = Uᵀ * (U * diagonal σ * Uᵀ) * V := by simp only [Matrix.mul_assoc]
      _ = Uᵀ * (V * diagonal hH.eigenvalues * star V) * V := h1
      _ = (Uᵀ * V) * diagonal hH.eigenvalues * (star V * V) := by simp only [Matrix.mul_assoc]
      _ = (Uᵀ * V) * diagonal hH.eigenvalues := by rw [hVV', Matrix.mul_one]
  have hint' := diagonal_intertwine f hint
  have hcomp : (RCLike.ofReal ∘ f ∘ hH.eigenvalues : ι → ℝ) = fun j => f (hH.eigenvalues j) := by
    funext j
    simp
  rw [hcomp]
  calc V * diagonal (fun j => f (hH.eigenvalues j)) * star V
      = (U * Uᵀ) * V * diagonal (fun j => f (hH.eigenvalues j)) * star V := by
        rw [hU, Matrix.one_mul]
    _ = U * ((Uᵀ * V) * diagonal (fun j => f (hH.eigenvalues j))) * star V := by
        simp only [Matrix.mul_assoc]
    _ = U * (diagonal (fun i => f (σ i)) * (Uᵀ * V)) * star V := by rw [hint']
    _ = U * diagonal (fun i => f (σ i)) * Uᵀ * (V * star V) := by simp only [Matrix.mul_assoc]
    _ = U * diagonal (fun i => f (σ i)) * Uᵀ := by rw [hVV, Matrix.mul_one]

/-- Functional calculus of a diagonal matrix: `f(diag σ) = diag(f ∘ σ)`. -/
theorem cfc_diagonal (f : ℝ → ℝ) (σ : ι → ℝ) :
    cfc f (diagonal σ : Matrix ι ι ℝ) = diagonal fun i => f (σ i) := by
  have h := cfc_eq_of_eq_conj_diagonal f (U := (1 : Matrix ι ι ℝ)) (by simp) σ
    (M := diagonal σ) (by simp)
  simpa using h

/-- The filtered update direction `F = f(S) O` of a left polar pair `(S, O)` of the gradient.
For an SVD `G = U Σ Vᵀ` it equals `U f(Σ) Vᵀ` (`matrixFilter_svd`). -/
noncomputable def filterDir (f : ℝ → ℝ) (S : Matrix ι ι ℝ) (O : Matrix ι κ ℝ) : Matrix ι κ ℝ :=
  cfc f S * O

end MatrixMuon

section Filter

variable {G : Matrix ι κ ℝ} {S : Matrix ι ι ℝ} {O : Matrix ι κ ℝ}

/-- SGD is the identity filter: `f = id` gives `F = S O = G`. -/
theorem matrixFilter_id (h : IsLeftPolar G S O) : filterDir (fun x => x) S O = G := by
  rw [filterDir, cfc_id' ℝ S h.posSemidef.1.isSelfAdjoint, h.eq]

/-- Muon is the constant filter: `f ≡ 1` gives `F = O`. -/
theorem matrixFilter_one (h : IsLeftPolar G S O) : filterDir (fun _ => 1) S O = O := by
  rw [filterDir, cfc_const_one ℝ S h.posSemidef.1.isSelfAdjoint, Matrix.one_mul]

/-- **The polar-pair filter is the SVD filter.** If `G = U diag(σ) V` is a (thin) singular value
decomposition — `U` orthogonal `d × d`, `σ_i ≥ 0`, `V` with orthonormal rows — then
`(U diag(σ) Uᵀ, U V)` is a left polar pair of `G` and `f(S) O = U diag(f ∘ σ) V`, the spec's
`F(G) = U f(Σ) Vᵀ`. -/
theorem matrixFilter_svd {U : Matrix ι ι ℝ} (hU : U * Uᵀ = 1) {σ : ι → ℝ} (hσ : ∀ i, 0 ≤ σ i)
    {V : Matrix ι κ ℝ} (hV : V * Vᵀ = 1) (f : ℝ → ℝ) :
    IsLeftPolar (U * diagonal σ * V) (U * diagonal σ * Uᵀ) (U * V) ∧
      filterDir f (U * diagonal σ * Uᵀ) (U * V) = U * diagonal (fun i => f (σ i)) * V := by
  have hU' : Uᵀ * U = 1 := mul_eq_one_comm.mp hU
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · have := (PosSemidef.diagonal (n := ι) (d := σ) hσ).mul_mul_conjTranspose_same U
    simpa only [conjTranspose_eq_transpose_of_trivial] using this
  · calc U * V * (U * V)ᵀ = U * (V * Vᵀ) * Uᵀ := by
          rw [transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hV, Matrix.mul_one, hU]
  · calc U * diagonal σ * V = U * diagonal σ * (Uᵀ * U) * V := by rw [hU', Matrix.mul_one]
      _ = U * diagonal σ * Uᵀ * (U * V) := by simp only [Matrix.mul_assoc]
  · rw [filterDir, cfc_eq_of_eq_conj_diagonal f hU σ rfl]
    calc U * diagonal (fun i => f (σ i)) * Uᵀ * (U * V)
        = U * diagonal (fun i => f (σ i)) * (Uᵀ * U) * V := by simp only [Matrix.mul_assoc]
      _ = U * diagonal (fun i => f (σ i)) * V := by rw [hU', Matrix.mul_one]

/-- For `G = U diag(σ) V` with `U` orthogonal, `σ_i ≠ 0` and `V Vᵀ = 1`,
`G Gᵀ = U diag(σ²) Uᵀ` is positive definite. -/
theorem matrixMuon_posDef_svd {U : Matrix ι ι ℝ} (hU : U * Uᵀ = 1) {σ : ι → ℝ}
    (hσ : ∀ i, σ i ≠ 0) {V : Matrix ι κ ℝ} (hV : V * Vᵀ = 1) :
    ((U * diagonal σ * V) * (U * diagonal σ * V)ᵀ).PosDef := by
  have h : (U * diagonal σ * V) * (U * diagonal σ * V)ᵀ
      = U * diagonal (fun i => σ i * σ i) * star U := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, transpose_mul,
      transpose_mul, diagonal_transpose]
    calc U * diagonal σ * V * (Vᵀ * (diagonal σ * Uᵀ))
        = U * diagonal σ * (V * Vᵀ) * diagonal σ * Uᵀ := by simp only [Matrix.mul_assoc]
      _ = U * (diagonal σ * diagonal σ) * Uᵀ := by
          rw [hV, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = U * diagonal (fun i => σ i * σ i) * Uᵀ := by rw [diagonal_mul_diagonal]
  rw [h, Matrix.IsUnit.posDef_star_right_conjugate_iff (IsUnit.of_mul_eq_one _ hU)]
  exact PosDef.diagonal fun i => mul_self_pos.mpr (hσ i)

/-- **`F(G) = U f(Σ) Vᵀ` is well defined and equals `f(S) O`.** If `G = U diag(σ) V` is a thin
SVD with all `σ_i > 0`, then for *every* left polar pair `(S, O)` of `G`:
`f(S) O = U diag(f ∘ σ) V`. -/
theorem matrixFilter_svd_unique {U : Matrix ι ι ℝ} (hU : U * Uᵀ = 1) {σ : ι → ℝ}
    (hσ : ∀ i, 0 < σ i) {V : Matrix ι κ ℝ} (hV : V * Vᵀ = 1)
    (h : IsLeftPolar (U * diagonal σ * V) S O) (f : ℝ → ℝ) :
    filterDir f S O = U * diagonal (fun i => f (σ i)) * V := by
  obtain ⟨hp, hf⟩ := matrixFilter_svd hU (fun i => (hσ i).le) hV f
  obtain ⟨rfl, rfl⟩ :=
    matrixMuon_leftPolar_unique (matrixMuon_posDef_svd hU (fun i => (hσ i).ne') hV) h hp
  exact hf

variable {σ lam c : ι → ℝ} {Q : Matrix ι κ ℝ}

/-- **Spec 5.5 for a general filter.** If `G = diag(σ) Q` with `σ_i > 0`, `Q Qᵀ = 1`, then for
*every* left polar pair `(S, O)` of `G` the filtered direction is `f(S) O = diag(f(σ_i)) Q`. -/
theorem matrixFilter_diagonal (hσ : ∀ i, 0 < σ i) (hQ : Q * Qᵀ = 1)
    (h : IsLeftPolar (diagonal σ * Q) S O) (f : ℝ → ℝ) :
    filterDir f S O = diagonal (fun i => f (σ i)) * Q := by
  obtain ⟨rfl, rfl⟩ := matrixMuon_leftPolar_diagonal_unique hσ hQ h
  rw [filterDir, cfc_diagonal]

/-- **Spec 5.5 for a general filter, unsigned commuting state.** `A = diag(λ)`, `W = diag(r) Q`
with `λ_i, r_i > 0`: the filtered step moves row `i` of `W` to
`(r_i - η f(λ_i r_i)) · (row i of Q)`. -/
theorem matrixFilter_step_row (hlam : ∀ i, 0 < lam i) {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    (hQ : Q * Qᵀ = 1) (h : IsLeftPolar (diagonal lam * (diagonal r * Q)) S O) (f : ℝ → ℝ)
    (η : ℝ) (i : ι) :
    (diagonal r * Q - η • filterDir f S O) i = (r i - η * f (lam i * r i)) • Q i := by
  have hG : diagonal lam * (diagonal r * Q) = diagonal (fun i => lam i * r i) * Q := by
    rw [← Matrix.mul_assoc, diagonal_mul_diagonal]
  rw [hG] at h
  rw [matrixFilter_diagonal (fun i => mul_pos (hlam i) (hr i)) hQ h f]
  ext j
  simp [diagonal_mul, sub_mul, mul_assoc]

/-- **Spec 5.5 for a general filter, signed commuting state.** `A = diag(λ)`, `λ_i > 0`,
`W = diag(c) Q`, `c_i ≠ 0`, `Q Qᵀ = 1`: for every left polar pair `(S, O)` of `A W`,
`f(S) O = diag(sign(c_i) f(λ_i |c_i|)) Q`. -/
theorem matrixFilter_coordinate (hlam : ∀ i, 0 < lam i) (hc : ∀ i, c i ≠ 0) (hQ : Q * Qᵀ = 1)
    (h : IsLeftPolar (diagonal lam * (diagonal c * Q)) S O) (f : ℝ → ℝ) :
    filterDir f S O = diagonal (fun i => Real.sign (c i) * f (lam i * |c i|)) * Q := by
  obtain ⟨rfl, rfl⟩ := matrixMuon_leftPolar_unique (matrixMuon_posDef_coordinate hlam hc hQ) h
    (matrixMuon_isLeftPolar_coordinate hlam hc hQ)
  rw [filterDir, cfc_diagonal, ← Matrix.mul_assoc, diagonal_mul_diagonal]
  congr 2
  funext i
  ring

/-- **Spec (1.0): matrix-level justification of the coordinate model for a general filter.**
In the setting of `matrixFilter_coordinate`, the filtered step `W⁺ = W - η f(S) O` is
`diag(c⁺) Q` with `c_i⁺ = c_i - η · sign(λ_i c_i) · f(|λ_i c_i|)`, i.e. the spec's
`cNextF f η c i = c_i - η · oddExt f (λ_i c_i)`: the state stays commuting with the same `Q`. -/
theorem matrixFilter_coordinate_step (hlam : ∀ i, 0 < lam i) (hc : ∀ i, c i ≠ 0)
    (hQ : Q * Qᵀ = 1) (h : IsLeftPolar (diagonal lam * (diagonal c * Q)) S O) (f : ℝ → ℝ)
    (η : ℝ) :
    diagonal c * Q - η • filterDir f S O
      = diagonal (fun i => c i - η * (Real.sign (lam i * c i) * f |lam i * c i|)) * Q := by
  rw [matrixFilter_coordinate hlam hc hQ h f]
  ext i j
  simp [diagonal_mul, sub_mul, mul_assoc, realSign_pos_mul (hlam i), abs_mul, abs_of_pos (hlam i)]

/-- **Spec §1 "where it comes from", basis-free form.** `A = U diag(λ) Uᵀ` with `U` orthogonal and
`λ_i > 0`; commuting state `W = U diag(c) Q` with `c_i ≠ 0`, `Q Qᵀ = 1`; `(S, O)` any left polar
pair of the clean gradient `A W`.  Then the filtered step is `W - η f(S) O = U diag(c⁺) Q` with
`c_i⁺ = c_i - η · sign(λ_i c_i) · f(|λ_i c_i|)`: the coordinate rule (1.0) in the Hessian
eigenbasis `U`, with the frame `Q` unchanged. -/
theorem matrixFilter_coordinate_step_basis {U : Matrix ι ι ℝ} (hU : U * Uᵀ = 1)
    (hlam : ∀ i, 0 < lam i) (hc : ∀ i, c i ≠ 0) (hQ : Q * Qᵀ = 1)
    (h : IsLeftPolar ((U * diagonal lam * Uᵀ) * (U * (diagonal c * Q))) S O) (f : ℝ → ℝ)
    (η : ℝ) :
    U * (diagonal c * Q) - η • filterDir f S O
      = U * (diagonal (fun i => c i - η * (Real.sign (lam i * c i) * f |lam i * c i|)) * Q) := by
  have hU' : Uᵀ * U = 1 := mul_eq_one_comm.mp hU
  have hpol := matrixMuon_isLeftPolar_coordinate hlam hc hQ
  have hG : (U * diagonal lam * Uᵀ) * (U * (diagonal c * Q))
      = U * diagonal (fun i => lam i * |c i|) * (diagonal (fun i => Real.sign (c i)) * Q) := by
    calc (U * diagonal lam * Uᵀ) * (U * (diagonal c * Q))
        = U * diagonal lam * (Uᵀ * U) * (diagonal c * Q) := by simp only [Matrix.mul_assoc]
      _ = U * (diagonal lam * (diagonal c * Q)) := by rw [hU', Matrix.mul_one, Matrix.mul_assoc]
      _ = U * (diagonal (fun i => lam i * |c i|) * (diagonal (fun i => Real.sign (c i)) * Q)) := by
          rw [hpol.eq]
      _ = U * diagonal (fun i => lam i * |c i|) * (diagonal (fun i => Real.sign (c i)) * Q) := by
          rw [Matrix.mul_assoc]
  rw [hG] at h
  rw [matrixFilter_svd_unique hU (fun i => mul_pos (hlam i) (abs_pos.mpr (hc i))) hpol.orth h f,
    Matrix.mul_assoc U, ← Matrix.mul_smul, ← Matrix.mul_sub]
  congr 1
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, diagonal_mul, smul_eq_mul,
    realSign_pos_mul (hlam i), abs_mul, abs_of_pos (hlam i)]
  ring

/-- The loss is invariant under an orthogonal change of basis:
`L_{U A Uᵀ}(U W) = L_A(W)` when `Uᵀ U = 1`. -/
theorem matrixMuon_loss_conj {U : Matrix ι ι ℝ} (hU : Uᵀ * U = 1) (A : Matrix ι ι ℝ)
    (W : Matrix ι κ ℝ) : MatrixMuon.loss (U * A * Uᵀ) (U * W) = MatrixMuon.loss A W := by
  have h : (U * W)ᵀ * (U * A * Uᵀ) * (U * W) = Wᵀ * A * W := by
    calc (U * W)ᵀ * (U * A * Uᵀ) * (U * W)
        = Wᵀ * (Uᵀ * U) * A * (Uᵀ * U) * W := by
          rw [transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = Wᵀ * A * W := by rw [hU, Matrix.mul_one, Matrix.mul_one]
  rw [MatrixMuon.loss, h, MatrixMuon.loss]

end Filter

/-! ## Link with the shared `Spec` (Deng's eigen-coordinate model)

`A = diag(λ)` with `λ = P.lam`, commuting state `W = diag(c) Q`, clean gradient `G = A W`. -/

section SpecLink

variable (P : Spec ι) {c : ι → ℝ} {Q : Matrix ι κ ℝ}

/-- The matrix loss of a commuting state is Deng's coordinate loss:
`½ tr(Wᵀ A W) = ½ ∑ λ_i c_i² = P.loss c` for `W = diag(c) Q`, `Q Qᵀ = 1`. -/
theorem matrixMuon_loss_eq_specLoss (c : ι → ℝ) (hQ : Q * Qᵀ = 1) :
    MatrixMuon.loss (diagonal P.lam) (diagonal c * Q) = P.loss c := by
  have h : ((diagonal c * Q)ᵀ * diagonal P.lam * (diagonal c * Q)).trace
      = ∑ i, P.lam i * c i ^ 2 := by
    rw [transpose_mul, diagonal_transpose, Matrix.mul_assoc Qᵀ, Matrix.mul_assoc Qᵀ,
      ← Matrix.mul_assoc (diagonal c * diagonal P.lam), diagonal_mul_diagonal,
      diagonal_mul_diagonal, trace_mul_comm, Matrix.mul_assoc, hQ, Matrix.mul_one,
      trace_diagonal]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [MatrixMuon.loss, h, Spec.loss]

/-- The energy of the clean gradient `G = A W` in the coordinate block `T` is Deng's
`∑_{i∈T} λ_i² c_i²` (`P.mom T 2 c`; `s^𝒟` for `T = 𝒟`, `s^ℬ` for `T = ℬ`). -/
theorem matrixMuon_grad_energy_coordProj (c : ι → ℝ) (hQ : Q * Qᵀ = 1) (T : Finset ι) :
    frob (coordProj T * (diagonal P.lam * (diagonal c * Q)))
        (coordProj T * (diagonal P.lam * (diagonal c * Q))) = P.mom T 2 c := by
  have hG : diagonal P.lam * (diagonal c * Q) = diagonal (fun i => P.lam i * c i) * Q := by
    rw [← Matrix.mul_assoc, diagonal_mul_diagonal]
  rw [hG, frob_coordProj_diagonal_mul_orth hQ, Spec.mom]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The total energy of the clean gradient is Deng's `s = ‖A x‖²`. -/
theorem matrixMuon_grad_energy (c : ι → ℝ) (hQ : Q * Qᵀ = 1) :
    frob (diagonal P.lam * (diagonal c * Q)) (diagonal P.lam * (diagonal c * Q)) = P.s c := by
  have hG : diagonal P.lam * (diagonal c * Q) = diagonal (fun i => P.lam i * c i) * Q := by
    rw [← Matrix.mul_assoc, diagonal_mul_diagonal]
  rw [hG, frob_diagonal_mul_orth hQ, P.s_eq_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Spec 5.1, the SGD side.** For SGD the update is the gradient `G = A W` itself, and the
fraction of its energy in the dominant block is Deng's alignment `θ = s^𝒟 / s`
(compare `matrixMuon_muon_energy_fraction`). -/
theorem matrixMuon_sgd_energy_fraction (c : ι → ℝ) (hQ : Q * Qᵀ = 1) :
    frob (coordProj P.D * (diagonal P.lam * (diagonal c * Q)))
        (coordProj P.D * (diagonal P.lam * (diagonal c * Q)))
      / frob (diagonal P.lam * (diagonal c * Q)) (diagonal P.lam * (diagonal c * Q))
      = P.theta c := by
  rw [matrixMuon_grad_energy_coordProj P c hQ, matrixMuon_grad_energy P c hQ]
  rfl

/-- **Spec 5.1, the Muon side.** For Muon (any `O` with `O Oᵀ = 1`) the fraction of the update
energy in the dominant block is `k / d`, whatever the alignment `θ` is
(compare `matrixMuon_sgd_energy_fraction`). -/
theorem matrixMuon_muon_energy_fraction [Nonempty ι] {O : Matrix ι κ ℝ} (hO : O * Oᵀ = 1) :
    frob (coordProj P.D * O) (coordProj P.D * O) / frob O O = P.kR / Fintype.card ι :=
  matrixMuon_energy_fraction_coordProj hO P.D

/-- The projected Muon step on a coordinate block `T` in the coordinate model:
`W - η Π_T O = diag(c⁺) Q` with `c_i⁺ = c_i - η sign(c_i)` on `T` and `c_i⁺ = c_i` off `T`. -/
theorem matrixMuon_coordinate_projected_step (hc : ∀ i, c i ≠ 0) (hQ : Q * Qᵀ = 1)
    {S : Matrix ι ι ℝ} {O : Matrix ι κ ℝ}
    (h : IsLeftPolar (diagonal P.lam * (diagonal c * Q)) S O) (T : Finset ι) (η : ℝ) :
    diagonal c * Q - η • (coordProj T * O)
      = diagonal (fun i => if i ∈ T then c i - η * Real.sign (c i) else c i) * Q := by
  obtain ⟨-, rfl⟩ := matrixMuon_leftPolar_unique (matrixMuon_posDef_coordinate P.lam_pos hc hQ) h
    (matrixMuon_isLeftPolar_coordinate P.lam_pos hc hQ)
  ext i j
  by_cases hi : i ∈ T <;> simp [coordProj, diagonal_mul, sub_mul, mul_assoc, hi]

/-- **Spec 5.3 + 5.5 ⇒ the Muon loss threshold of spec 2.4.** In the coordinate model
(`A = diag(λ)`, `W = diag(c) Q`, `c_i ≠ 0`), the Muon step projected on a nonempty coordinate
block `T` decreases the loss iff `0 < η < 2 ∑_{i∈T} λ_i |c_i| / ∑_{i∈T} λ_i`. -/
theorem matrixMuon_coordinate_loss_decrease_iff (hc : ∀ i, c i ≠ 0) (hQ : Q * Qᵀ = 1)
    {S : Matrix ι ι ℝ} {O : Matrix ι κ ℝ}
    (h : IsLeftPolar (diagonal P.lam * (diagonal c * Q)) S O) {T : Finset ι} (hT : T.Nonempty)
    (η : ℝ) :
    MatrixMuon.loss (diagonal P.lam) (diagonal c * Q - η • (coordProj T * O))
        < MatrixMuon.loss (diagonal P.lam) (diagonal c * Q)
      ↔ 0 < η ∧ η < 2 * (∑ i ∈ T, P.lam i * |c i|) / ∑ i ∈ T, P.lam i := by
  have hEA : 0 < (coordProj T * diagonal P.lam).trace := by
    rw [trace_coordProj_mul_diagonal]
    exact Finset.sum_pos (fun i _ => P.lam_pos i) hT
  have key := matrixMuon_loss_decrease_iff (diagonal_transpose P.lam) (isOrthProj_coordProj T) h
    hEA η
  obtain ⟨rfl, -⟩ := matrixMuon_leftPolar_unique (matrixMuon_posDef_coordinate P.lam_pos hc hQ) h
    (matrixMuon_isLeftPolar_coordinate P.lam_pos hc hQ)
  rwa [trace_coordProj_mul_diagonal, trace_coordProj_mul_diagonal] at key

/-- **Matrix-level justification of the coordinate model (spec (1.0)) for `P : Spec ι`.**
`A = diag(P.lam)`, commuting state `W = diag(c) Q` (`c_i ≠ 0`, `Q Qᵀ = 1`), `(S, O)` any left polar
pair of the clean gradient `A W`, `f` any filter.  The filtered step is
`W - η f(S) O = diag(c⁺) Q`, `c_i⁺ = c_i - η · sign(λ_i c_i) · f(|λ_i c_i|)`.
The right-hand side is, by unfolding definitions, `diag(P.cNextF f η c) Q` for the coordinate step
`Spec.cNextF` / `Spec.oddExt` of `Filter/Coordinate.lean` (not imported here). -/
theorem matrixFilter_spec_step (hc : ∀ i, c i ≠ 0) (hQ : Q * Qᵀ = 1) {S : Matrix ι ι ℝ}
    {O : Matrix ι κ ℝ} (h : IsLeftPolar (diagonal P.lam * (diagonal c * Q)) S O) (f : ℝ → ℝ)
    (η : ℝ) :
    diagonal c * Q - η • filterDir f S O
      = diagonal (fun i => c i - η * (Real.sign (P.lam i * c i) * f |P.lam i * c i|)) * Q :=
  matrixFilter_coordinate_step P.lam_pos hc hQ h f η

end SpecLink

/-! ## A concrete non-commuting instance (`d = 2`, `n = 3`) -/

namespace MatrixMuon.Example

/-- Hessian `A = diag(3, 1)`. -/
def exA : Matrix (Fin 2) (Fin 2) ℝ := !![3, 0; 0, 1]
/-- The positive semidefinite polar factor; it does **not** commute with `A`. -/
def exS : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 1, 2]
/-- The orthogonal polar factor (`O Oᵀ = 1`). -/
noncomputable def exO : Matrix (Fin 2) (Fin 3) ℝ := !![3/5, 4/5, 0; -4/5, 3/5, 0]
/-- The state `W = A⁻¹ S O`. -/
noncomputable def exW : Matrix (Fin 2) (Fin 3) ℝ := !![2/15, 11/15, 0; -1, 2, 0]

theorem exA_symm : exAᵀ = exA := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [exA]

theorem exS_posSemidef : exS.PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [exS]
  · simp only [exS, dotProduct, mulVec, Fin.sum_univ_two, star_trivial, Pi.star_apply,
      of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_fin_one]
    nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0), sq_nonneg (x 1)]

theorem exO_orth : exO * exOᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exO, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

theorem ex_grad : exA * exW = exS * exO := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exA, exW, exS, exO, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- The example is a genuine left polar pair of the clean gradient `A W`. -/
theorem ex_isLeftPolar : IsLeftPolar (exA * exW) exS exO :=
  ⟨exS_posSemidef, exO_orth, ex_grad⟩

/-- **Non-vacuity of spec 5.4**: here `G Gᵀ = S² = [[5,4],[4,5]]` is positive definite. -/
theorem ex_posDef : ((exA * exW) * (exA * exW)ᵀ).PosDef := by
  rw [matrixMuon_posDef_iff_isUnit_det, ← ex_isLeftPolar.mul_self, det_mul, isUnit_iff_ne_zero]
  simp [exS, det_fin_two_of]
  norm_num

/-- By spec 5.4, `(exS, exO)` is the only left polar pair of `A W`: `exO` is *the* Muon direction
of this (non-commuting) state. -/
theorem ex_unique {S : Matrix (Fin 2) (Fin 2) ℝ} {O : Matrix (Fin 2) (Fin 3) ℝ}
    (h : IsLeftPolar (exA * exW) S O) : S = exS ∧ O = exO :=
  matrixMuon_leftPolar_unique ex_posDef h ex_isLeftPolar

/-- The example is *not* a commuting state: `S A ≠ A S`. -/
theorem ex_not_commute : exS * exA ≠ exA * exS := by
  intro h
  have := congrFun (congrFun h 0) 1
  simp [exS, exA, Matrix.mul_apply, Fin.sum_univ_two] at this

theorem ex_trace_A : (coordProj ({0} : Finset (Fin 2)) * exA).trace = 3 := by
  simp [coordProj, exA, Matrix.trace, Matrix.mul_apply, diagonal_apply]

theorem ex_trace_S : (coordProj ({0} : Finset (Fin 2)) * exS).trace = 2 := by
  simp [coordProj, exS, Matrix.trace, Matrix.mul_apply, diagonal_apply]

/-- **Non-vacuity of spec 5.3** on a non-commuting state: the Muon step projected on the first
coordinate decreases the loss iff `0 < η < 4/3 = 2 tr(Π S)/tr(Π A)`. -/
theorem ex_loss_decrease_iff (η : ℝ) :
    loss exA (exW - η • (coordProj ({0} : Finset (Fin 2)) * exO)) < loss exA exW ↔ 0 < η ∧ η < 4 / 3 := by
  have h := matrixMuon_loss_decrease_iff exA_symm (isOrthProj_coordProj ({0} : Finset (Fin 2))) ex_isLeftPolar
    (by rw [ex_trace_A]; norm_num) η
  rw [ex_trace_A, ex_trace_S] at h
  rw [h]
  norm_num

/-- Spec 5.1 on the example: half of the Muon update energy lies in the first coordinate
(`k/d = 1/2`). -/
theorem ex_energy_fraction :
    frob (coordProj ({0} : Finset (Fin 2)) * exO) (coordProj ({0} : Finset (Fin 2)) * exO) / frob exO exO = 1 / 2 := by
  rw [matrixMuon_energy_fraction_coordProj exO_orth]
  simp

end MatrixMuon.Example

end SuspiciousAlignment
