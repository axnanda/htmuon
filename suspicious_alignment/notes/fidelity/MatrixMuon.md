# Fidelity note — `SuspiciousAlignment/Filter/MatrixMuon.lean`

Module `SuspiciousAlignment.Filter.MatrixMuon` (imports `Mathlib`, `SuspiciousAlignment.Defs`).

**Source of truth: `notes/research/filter_spec.md`, Section 5** ("General matrix Muon on wide
layers (no commuting assumption)"), plus the "where it comes from" paragraph of Section 1.
This is an *extension* of Deng et al. (arXiv:2601.11789v2); nothing in this file is claimed by
the paper itself.

Status: the file compiles, `lake build SuspiciousAlignment.Filter.MatrixMuon` succeeds, no
`sorry`/`admit`/`axiom`/`native_decide`; `#print axioms` on all 120 declarations of the file shows
only `propext`, `Classical.choice`, `Quot.sound`. Every statement was tested numerically (numpy,
random matrices, polar factor via SVD; 300 random trials per statement) before being proved.

## Conventions

* Real matrices; rows indexed by a finite type `ι` (`d = |ι|`), columns by a finite type `κ`
  (`n = |κ|`). Only `ι` needs `DecidableEq`.
* The spec's projector `Π` is called `E` (`Π` is a reserved token in Lean 4).
* Definitions (namespace `SuspiciousAlignment.MatrixMuon`):
  `frob X Y = tr(Xᵀ Y)`; `loss A W = ½ tr(Wᵀ A W)`; `IsOrthProj E := Eᵀ = E ∧ E E = E`;
  `IsLeftPolar G S O := S.PosSemidef ∧ O Oᵀ = 1 ∧ G = S O`
  (`Matrix.PosSemidef` over `ℝ` includes symmetry); `coordProj T` = diagonal `0/1` matrix of a
  finset `T`; `filterDir f S O := cfc f S * O` (the spectrally filtered direction `f(S) O`).
* The square root is Mathlib's `CFC.sqrt` on `Matrix ι ι ℝ` (needs `open scoped MatrixOrder`).
* No definition of `Defs.lean` was changed or shadowed. `Spec.loss`, `Spec.mom`, `Spec.s`,
  `Spec.theta`, `Spec.kR`, `Spec.lam`, `Spec.lam_pos`, `Spec.D` are used in the link section.

## Table

| Spec item | Lean declaration(s) | Status | Explanation |
|---|---|---|---|
| §5 preamble: `S = (G Gᵀ)^{1/2}` | `MatrixMuon.IsLeftPolar.mul_self`, `MatrixMuon.IsLeftPolar.eq_sqrt` | exact | `S² = G Gᵀ` and `S = CFC.sqrt (G Gᵀ)` for every left polar pair (no rank assumption). |
| §5 preamble: "exists when `G Gᵀ` is invertible, which forces `d ≤ n`" | `matrixMuon_posDef_iff_isUnit_det`, `MatrixMuon.IsLeftPolar.card_le`, `matrixMuon_card_le_of_posDef` | exact | `G Gᵀ` PD ⇔ `det(G Gᵀ)` is a unit; any left polar pair forces `|ι| ≤ |κ|`. |
| 5.1 `tr((ΠO)ᵀ(ΠO)) = tr(ΠᵀΠ)` for every `Π` | `matrixMuon_equipartition`, `matrixMuon_frob_mul_orth` | strengthened | Stated for rectangular `E : Matrix m ι ℝ` (any number of rows), and only `O Oᵀ = 1` is used (no polar pair needed). |
| 5.1 `‖ΠO‖_F² = k` for an orthogonal projector of rank `k` (`tr Π = k`) | `matrixMuon_energy_proj` (`= E.trace`), `matrixMuon_energy_proj_rank` (`= E.rank`), `MatrixMuon.IsOrthProj.trace_eq_rank` | exact | Both the trace form and the rank form; `tr E = rank E` is proved for idempotent real matrices. |
| 5.1 `‖O‖_F² = d` | `matrixMuon_energy_total` | exact | |
| 5.1 fraction `k/d` whatever `θ` | `matrixMuon_energy_fraction`, `matrixMuon_energy_fraction_coordProj`, `matrixMuon_muon_energy_fraction` | exact | `[Nonempty ι]` is assumed so that the quotient is not `0/0` (the identity also holds for `d = 0`). |
| 5.1 "for SGD that fraction equals `θ`" | `matrixMuon_grad_energy_coordProj`, `matrixMuon_grad_energy`, `matrixMuon_sgd_energy_fraction` | exact (coordinate model) | For `A = diag(P.lam)`, `W = diag(c) Q`: `‖Π_T G‖_F² = P.mom T 2 c`, `‖G‖_F² = P.s c`, ratio on `𝒟` is `P.theta c` (including the convention `θ(0) = 0`). |
| 5.2 exact loss change `−η⟪ΠAW,O⟫ + (η²/2) tr(ΠA)` | `matrixMuon_loss_step`, `matrixMuon_loss_projected_step`, `matrixMuon_loss_projected_step_noisy`, `matrixMuon_loss_full_step` | strengthened | Holds for every `O` with `O Oᵀ = 1` (noisy polar factor included), every `W`, every `η ∈ ℝ`. **The hypotheses "`Π` commutes with `A`" and "`A` positive semidefinite" of the spec are not needed** (see below). |
| 5.2 (necessity of `Aᵀ = A`) | `matrixMuon_loss_projected_step_needs_symm` | extra | Formal counterexample for non-symmetric `A` (`d = n = 2`). |
| 5.2 remark `Π A W = A (Π W)` when `Π` commutes with `A` | `matrixMuon_proj_grad_of_commute` | extra | The only place where commutation plays a role (interpretation, not the identity). |
| 5.3 `⟪ΠAW,O⟫ = tr(ΠS)` | `matrixMuon_frob_mul_mul_orth`, `matrixMuon_frob_proj_grad` | strengthened | True for *arbitrary* square `E` and `S` once `O Oᵀ = 1` (no projector, no symmetry, no PSD). |
| 5.3 loss decreases iff `0 < η < 2 tr(ΠS)/tr(ΠA)` | `matrixMuon_loss_projected_step_noiseFree`, `matrixMuon_loss_decrease_iff`, `matrixMuon_loss_increase_iff`, `matrixMuon_loss_eq_iff`, `matrixMuon_threshold_pos` | strengthened | Only `tr(EA) > 0` is assumed; the spec's `tr(ΠS) > 0` is not needed for the iff (`tr(ES) ≥ 0` is automatic: `MatrixMuon.IsOrthProj.trace_mul_nonneg`). The iff is for all real `η` (negative `η` included). Increase/equality versions added. |
| 5.3 (hypotheses automatic) | `MatrixMuon.IsOrthProj.trace_mul_pos`, `MatrixMuon.IsLeftPolar.posDef`, `matrixMuon_traces_pos` | extra | If `A` and `G Gᵀ` are PD then `tr(EA) > 0` and `tr(ES) > 0` for every nonzero orthogonal projector. |
| 5.3 `⟪G,O⟫ = tr S` | `matrixMuon_frob_grad_polar` | exact | Any left polar pair, any `G`. |
| 5.3 "(the nuclear norm of `G`)" | `MatrixMuon.trace_sqrt`, `matrixMuon_frob_grad_polar_eq_nuclear` | equivalent-reformulation | Mathlib has no nuclear norm; proved `⟪G,O⟫ = ∑ᵢ √(λᵢ(G Gᵀ))` (sum of singular values) with Mathlib's `IsHermitian.eigenvalues`. Also `matrixMuon_frob_grad_polar_pos`: `⟪G,O⟫ > 0` whenever `G ≠ 0`. |
| 5.4 existence | `MatrixMuon.isLeftPolar_of_mul_self`, `matrixMuon_isLeftPolar_sqrt`, `matrixMuon_exists_leftPolar` | exact | Explicit pair `S = CFC.sqrt (G Gᵀ)`, `O = S⁻¹ G`, fully through Mathlib's CFC square root (no "given square root" fallback was needed). |
| 5.4 uniqueness | `matrixMuon_leftPolar_unique`, `matrixMuon_existsUnique_leftPolar`, `matrixMuon_isLeftPolar_iff` | exact | `∃!` over pairs `(S, O)`. |
| 5.4 (necessity of definiteness for uniqueness) | `matrixMuon_leftPolar_not_unique` | extra | `G = 0`, `d = n = 1`: `(0, 1)` and `(0, −1)` are both left polar pairs. |
| 5.5 `(diag σ, Q)` is a left polar pair | `matrixMuon_isLeftPolar_diagonal`, `matrixMuon_posDef_diagonal_mul`, `matrixMuon_leftPolar_diagonal_unique` | strengthened | Polar pair already for `σ_i ≥ 0`; for `σ_i > 0` it is *the* polar pair (so "Muon's direction is `Q`" is unambiguous). |
| 5.5 `tr(ΠS)/tr(ΠA) = ∑_T σ_i / ∑_T λ_i` | `matrixMuon_trace_ratio_coordProj`, `MatrixMuon.trace_coordProj_mul_diagonal`, `MatrixMuon.isOrthProj_coordProj`, `MatrixMuon.trace_coordProj`, `MatrixMuon.coordProj_mul_diagonal_comm` | exact | Plain identity of two quotients (same numerators/denominators), no positivity needed. |
| 5.5 "the Muon threshold of 2.4" | `matrixMuon_coordinate_loss_decrease_iff`, `matrixMuon_coordinate_projected_step`, `matrixMuon_loss_eq_specLoss` | exact | For `P : Spec ι`, `W = diag(c) Q`, `c_i ≠ 0`, `T` nonempty: loss decreases iff `0 < η < 2 ∑_T λ_i|c_i| / ∑_T λ_i`; the matrix loss equals `P.loss c`. |
| Task: Muon step moves row `i` of `diag(r) Q` to `(r_i − η)·Q_i`; rule `c_i⁺ = c_i − η sign(c_i)` | `matrixMuon_step_row`, `matrixMuon_isLeftPolar_coordinate`, `matrixMuon_posDef_coordinate`, `matrixMuon_coordinate_step`, `matrixMuon_coordinate_step_row` | exact / strengthened | Unsigned (`r` arbitrary, `σ_i > 0`) and signed (`c_i ≠ 0`, polar pair `(diag(λ|c|), diag(sign c) Q)`) versions, for *every* left polar pair of the gradient. |
| Task (if time permits): general filter | `MatrixMuon.filterDir`, `MatrixMuon.cfc_diagonal`, `MatrixMuon.cfc_eq_of_eq_conj_diagonal`, `MatrixMuon.diagonal_intertwine`, `matrixFilter_id`, `matrixFilter_one`, `matrixFilter_diagonal`, `matrixFilter_step_row`, `matrixFilter_coordinate`, `matrixFilter_coordinate_step`, `matrixFilter_spec_step` | exact | `F = f(S) O` via `cfc`; SGD = `f = id`, Muon = `f ≡ 1`; in the coordinate model `F = diag(f σ_i) Q` for every polar pair and the step is `c_i⁺ = c_i − η sign(λ_i c_i) f(|λ_i c_i|)` (= `Spec.cNextF` of `Filter/Coordinate.lean` by unfolding). No continuity of `f` is needed. |
| Spec header: `F(G) = U f(Σ) Vᵀ` for the SVD | `matrixFilter_svd`, `matrixMuon_posDef_svd`, `matrixFilter_svd_unique` | extra | For any thin SVD `G = U diag(σ) V` (`U` orthogonal, `σ ≥ 0`, `V Vᵀ = 1`): `(U diag σ Uᵀ, U V)` is a left polar pair and `f(S) O = U diag(f σ) V`; for `σ > 0` this holds for every polar pair. Existence of an SVD is *not* proved (not needed). |
| Spec §1 "where it comes from" (general eigenbasis `U`) | `matrixFilter_coordinate_step_basis`, `matrixMuon_loss_conj` | extra | `A = U diag(λ) Uᵀ`, `W = U diag(c) Q` ⇒ `W − η f(S) O = U diag(c⁺) Q`. |
| Non-vacuity | `MatrixMuon.Example.*` (`ex_isLeftPolar`, `ex_not_commute`, `ex_posDef`, `ex_unique`, `ex_loss_decrease_iff`, `ex_energy_fraction`) | extra | `d = 2`, `n = 3`, `A = diag(3,1)`, `S = [[2,1],[1,2]]` (does not commute with `A`), `O = [[3/5,4/5,0],[−4/5,3/5,0]]`, `W = A⁻¹ S O`: loss decreases iff `0 < η < 4/3`; `G Gᵀ` PD; the polar pair is unique. |

## Discrepancies with the spec (all are *weakenings of hypotheses*; no claim of §5 is false)

1. **5.2: commutation of `Π` with `A` is superfluous.** The spec states the identity for "an
   orthogonal projector commuting with `A`". The second-order term is
   `tr((ΠO)ᵀ A (ΠO)) = tr(Π A Π · O Oᵀ) = tr(Π A Π) = tr(Π² A) = tr(Π A)` by cyclicity of the
   trace alone, and the first-order term only uses `Πᵀ = Π`. Verified numerically with random
   non-commuting projectors (error `≈ 3·10⁻¹⁴`). Commutation is only needed for the
   *interpretation* `Π A W = A Π W` (`matrixMuon_proj_grad_of_commute`).
2. **5.2: positive semidefiniteness of `A` is superfluous**; symmetry of `A` is necessary
   (`matrixMuon_loss_projected_step_needs_symm`: `A = [[0,1],[0,0]]`, `W = [[0,−1],[1,0]]`,
   `Π = O = 1`, `η = 1`: left side `0`, right side `−1`).
3. **5.3: `⟪Π A W, O⟫ = tr(Π S)` needs no hypothesis on `Π` or `S`** beyond `A W = S O`,
   `O Oᵀ = 1`.
4. **5.3: the hypothesis `tr(Π S) > 0` is not needed for the iff.** With `tr(Π A) > 0` alone,
   `L(W − ηΠO) < L(W) ⇔ 0 < η < 2 tr(ΠS)/tr(ΠA)` for all real `η`, because `tr(ΠS) ≥ 0`
   automatically (`tr(ΠS) = tr(Πᵀ S Π)`, `S ⪰ 0`); if `tr(ΠS) = 0` both sides are false.
   `tr(ΠS) > 0` only guarantees that the interval is nonempty.
5. **5.4: uniqueness of `S` never needs definiteness** (`S = (G Gᵀ)^{1/2}` always); only the
   uniqueness of `O` does, and it genuinely fails otherwise (`matrixMuon_leftPolar_not_unique`).
6. **5.5: `(diag σ, Q)` is a left polar pair already for `σ_i ≥ 0`**; `σ_i > 0` is what makes it
   the unique one.
7. **Wording "rank `k`" / "nuclear norm".** The spec identifies `tr Π` with the rank and `tr S`
   with the nuclear norm without proof; both identifications are proved here
   (`IsOrthProj.trace_eq_rank`, `matrixMuon_frob_grad_polar_eq_nuclear`), the nuclear norm being
   expressed as `∑ᵢ √λᵢ(G Gᵀ)` since Mathlib has no nuclear norm.

## Not formalized

* Existence of a singular value decomposition (never needed: all statements are phrased with the
  left polar pair, as the spec intends).
* The general (rank-deficient) case of 5.4: existence of *some* left polar pair for every wide `G`
  (the spec only claims the positive definite case).
* A bridge theorem literally mentioning `Spec.cNextF` (it lives in `Filter/Coordinate.lean`, which
  this file may not import); `matrixFilter_spec_step` has the right-hand side written out so that
  the bridge is `rfl` after unfolding `Spec.cNextF`, `Spec.oddExt`.

## Satisfiability of hypotheses

* `O Oᵀ = 1`, `IsLeftPolar (A W) S O`, `tr(E A) > 0`, `(G Gᵀ).PosDef`, non-commuting `S`, `A`:
  all realised simultaneously by `MatrixMuon.Example` (`d = 2`, `n = 3`).
* Coordinate-model hypotheses (`σ_i > 0` / `c_i ≠ 0`, `Q Qᵀ = 1`): satisfiable whenever
  `|ι| ≤ |κ|` (e.g. `κ = ι`, `Q = 1`); `matrixMuon_isLeftPolar_coordinate` produces the polar pair
  that the step theorems quantify over, so those theorems are not vacuous.
* No statement relies on `x / 0 = 0`: every quotient has a denominator that is assumed or proved
  positive (`tr(EA) > 0`, `[Nonempty ι]`, `T.Nonempty` with `λ_i > 0`), except the pure identities
  `matrixMuon_trace_ratio_coordProj` and `matrixMuon_sgd_energy_fraction`, where both sides are the
  same quotient (the latter matches the paper's convention `θ(0) = 0`).
