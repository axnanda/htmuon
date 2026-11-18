# Specification: spectrally filtered updates in Deng's quadratic model

This is the mathematical specification (source of truth) for the Lean files under
`SuspiciousAlignment/Filter/`. It extends Deng et al.'s one-step theory (Sections 4–5 of the paper)
from SGD to *spectral-filter* optimizers: the update is `W⁺ = W − η F(G)` with `F(G) = U f(S) Vᵀ`
for the SVD `G = U S Vᵀ` of the (stochastic) gradient matrix.

* SGD: `f(σ) = σ`.  Muon: `f(σ) = 1`.  HTMuon: `f(σ) = σ^p`, `0 ≤ p ≤ 1` (default `p = 1/8`).
* Echelon(r): `f = 1` on a head set of `r` singular directions, `f(σ) = σ/τ` on the tail.

All statements below were derived by hand and checked numerically (numpy, exact SVD) before being
written here; a statement that turns out to be false or to need extra hypotheses must be reported,
not silently changed.

Notation as in `Defs.lean`: spectrum `λ_i > 0`, dominant block `𝒟`, bulk `ℬ`, coefficients `c_i`,
`s_i := λ_i² c_i²`, `s^S = ∑_{i∈S} s_i`, `θ = s^𝒟 / (s^𝒟 + s^ℬ)`, `ψ_S = ∑_{i∈S} λ_i²`,
`m = λ_k/λ_{k+1}`, loss `L = ½ ∑ λ_i c_i²`.

## 1. The coordinate (commuting) model

**Where it comes from.** Take matrix parameters `W ∈ ℝ^{d×n}`, `n ≥ d`, loss `L(W) = ½ tr(Wᵀ A W)`
(Hessian `I_n ⊗ A`; `n = 1` is Deng's model). In the eigenbasis of `A`, write `UᵀW = diag(r) Q`
with `r_i ≥ 0` and `Q` having orthonormal rows ("commuting state": the rows of `UᵀW` are mutually
orthogonal). The clean gradient is `A W = U diag(λ_i r_i) Q`, an SVD with singular values
`σ_i = λ_i r_i` and left singular vectors = Hessian eigenvectors. Hence
`F(AW) = U diag(f(σ_i)) Q`, the filtered step keeps the state commuting, and along the fixed unit
row `q_i` the signed coefficient `c_i` (with `|c_i| = r_i`) evolves by

  `c_i⁺ = c_i − η · sign(c_i) · f(λ_i |c_i|)`.                                  (1.0)

So the coordinate model is Deng's eigen-coordinate model with the gradient coordinate
`g_i = λ_i c_i` replaced by `φ_f(g_i)`, `φ_f(g) := sign(g) f(|g|)` the odd extension of `f`.
(The matrix-level justification is the subject of `Filter/MatrixMuon.lean`, §5.)

**Definitions.**
* `oddExt f g := Real.sign g * f |g|`.
* `cNextF f η c i := c i − η * oddExt f (λ_i * c i)`.
* effective curvature `nu f c i := f (λ_i * |c i|) / |c i|` (Lean convention `x/0 = 0`).
* `ν`-moments `momF f S a c := ∑_{i∈S} (nu f c i)^a * λ_i² * c_i²` (`a ∈ ℕ`).
* `qF f c := 2 * (s^𝒟 * momF f ℬ 1 c − s^ℬ * momF f 𝒟 1 c)`,
  `pF f c := s^ℬ * momF f 𝒟 2 c − s^𝒟 * momF f ℬ 2 c`,  `etaStarF f c := −qF / pF`.
* `fCompareF f η c := s^ℬ(c) * s^𝒟(c⁺) − s^ℬ(c⁺) * s^𝒟(c)` with `c⁺ = cNextF f η c`.

**Statements.**
* **1.1 (effective-curvature form).** For every `i`: `cNextF f η c i = (1 − η * nu f c i) * c i`.
  (Also true at `c_i = 0`: both sides are `0`.)
* **1.2 (SGD is the identity filter).** `cNextF id η c = P.cNext η c 0`, and `nu id c i = λ_i`
  whenever `c_i ≠ 0`. Consequently for `f = id`: `qF = P.qCoef c` and `pF = P.pCoef` with zero
  noise (`e_𝒟 = e_ℬ = 0`).
* **1.3 (energies).** `∑_{i∈S} λ_i² (c_i⁺)² = momF f S 0 c − 2 η momF f S 1 c + η² momF f S 2 c`,
  and `momF f S 0 c = P.mom S 2 c`.
* **1.4 (quadratic form, exact — no expectation).** `fCompareF f η c = pF f c * η² + qF f c * η`.
* **1.5 (alignment change).** For arbitrary states `c, c'` with `s(c) > 0`, `s(c') > 0`:
  `θ(c') < θ(c) ⟺ s^ℬ(c) s^𝒟(c') − s^ℬ(c') s^𝒟(c) < 0`, same with `>` and `=`. Hence for the
  filtered step the sign of the one-step alignment change is the sign of `pF η² + qF η`.
* **1.6 (double-sum forms).** With `s_i = λ_i² c_i²`, `ν_i = nu f c i`:
  `qF = 2 ∑_{i∈𝒟} ∑_{j∈ℬ} s_i s_j (ν_j − ν_i)`,  `pF = ∑_{i∈𝒟} ∑_{j∈ℬ} s_i s_j (ν_i² − ν_j²)`.
* **1.7 (curvature ordering preserved ⇒ Deng's dichotomy).** Suppose `s^𝒟 > 0`, `s^ℬ > 0`,
  `ν_i ≥ 0`, and `ν_j < ν_i` for all `i ∈ 𝒟`, `j ∈ ℬ` with `c_i ≠ 0 ≠ c_j`. Then `qF < 0 < pF`,
  `etaStarF > 0`, and for `η > 0`: alignment decreases iff `η < etaStarF`, is unchanged iff
  `η = etaStarF`, increases iff `η > etaStarF` (given `s(c⁺) > 0`).
  For `f = id` this is the noise-free case of Deng's Theorems 2–3 (ordering holds by the gap).
* **1.8 (curvature ordering reversed ⇒ the dichotomy flips).** If instead `ν_i < ν_j` for all
  `i ∈ 𝒟`, `j ∈ ℬ` (nonzero coefficients), then `pF < 0 < qF`, `etaStarF > 0`, and alignment
  **increases** iff `0 < η < etaStarF` and decreases iff `η > etaStarF`. This cannot happen for SGD.
* **1.9 (two-sided bound on the critical step size).** Under the hypotheses of 1.7, if
  `a_𝒟 ≤ ν_i ≤ b_𝒟` on `𝒟` and `a_ℬ ≤ ν_j ≤ b_ℬ` on `ℬ` (nonzero coefficients), `a_𝒟 + a_ℬ > 0`:
  `2/(b_𝒟 + b_ℬ) ≤ etaStarF ≤ 2/(a_𝒟 + a_ℬ)`.
  (Proof: `−qF/pF = 2 ∑ w_ij / ∑ w_ij (ν_i + ν_j)` with weights `w_ij = s_i s_j (ν_i − ν_j) > 0`.)
  **Corollary for SGD (noise-free Deng):** `2/(λ_1 + λ_{k+1}) ≤ η*₀ ≤ 2/(λ_k + λ_d)` where
  `η*₀ = −qCoef / pCoef` with zero noise. This sharpens the noise-free case of Deng's Theorem 7,
  `η* ≥ 2 gap₁/(λ_1² − λ_d²)` (prove the comparison `2/(λ_1+λ_{k+1}) ≥ 2 gap₁/(λ_1² − λ_d²)`).

## 2. Muon (`f ≡ 1`)

Here `c_i⁺ = c_i − η sign(c_i)` and `ν_i = 1/|c_i|`: the effective curvature of a direction is the
inverse of its coefficient magnitude — **the Hessian eigenvalue drops out**.

* **2.1 (alignment is invariant at isotropic states).** If `|c_i| = r > 0` for all `i` and
  `η ≠ r`, then `θ(c⁺) = θ(c) = ψ_𝒟/(ψ_𝒟 + ψ_ℬ)`. (For SGD at the same state the alignment strictly
  decreases for every `0 < η < η*₀`.)
* **2.2 (the sign of the alignment change is decided by coefficient sizes, not by the gap).**
  If `0 < |c_i| < |c_j|` for all `i ∈ 𝒟, j ∈ ℬ`: hypotheses of 1.7 hold (decrease iff
  `η < etaStarF`). If `|c_i| > |c_j| > 0` for all `i ∈ 𝒟, j ∈ ℬ`: hypotheses of 1.8 hold (alignment
  increases for small `η`). Both hold for every spectrum `λ`; with `r_min^S ≤ |c_i| ≤ r_max^S`
  the bound 1.9 reads `2/(1/r_min^𝒟 + 1/r_min^ℬ) ≤ etaStarF ≤ 2/(1/r_max^𝒟 + 1/r_max^ℬ)`.
* **2.3 (the η-floor and its 2-cycle).** If `0 < |c_i| < η` then `|c_i⁺| = η − |c_i|` and
  `c_i⁺⁺ = c_i`: the coordinate is on a period-2 orbit and never converges. If `|c_i| ≥ η` then
  `|c_i⁺| = |c_i| − η`. Hence if all `|c_i| ∈ (0, η)`, the state is 2-periodic, and at the
  "mid-floor" state `|c_i| = η/2` for all `i` the alignment is `ψ_𝒟/(ψ_𝒟+ψ_ℬ)` forever.
* **2.4 (loss thresholds for projected filtered updates, general `f`).** Let
  `cNextFProj f S η c i := if i ∈ S then cNextF f η c i else c i` and `σ_i = λ_i |c_i|`. Then
  `L(c⁺) − L(c) = −η ∑_{i∈S} σ_i f(σ_i) + (η²/2) ∑_{i∈S} λ_i f(σ_i)²` (exact; restrict to `c_i ≠ 0`
  on `S` or note that zero coordinates contribute `0` with `Real.sign 0 = 0`), so with
  `etaLossF f S c := 2 ∑_{S} σ_i f(σ_i) / ∑_{S} λ_i f(σ_i)²` and both sums positive:
  loss decreases iff `0 < η < etaLossF`, increases iff `η > etaLossF`.
  For `f = id`: `etaLossF = 2 s^S/τ^S` = Deng's `η^loss_S` with zero noise.
  For Muon: `etaLossF = 2 ∑_S λ_i |c_i| / ∑_S λ_i` — twice a `λ`-weighted mean of `|c_i|`.
* **2.5 (no window at isotropic states).** Muon, `|c_i| = r > 0` for all `i`:
  `etaLossF 𝒟 = etaLossF ℬ = 2r`. For SGD at any state with `s^𝒟, s^ℬ > 0` (noise-free):
  `η^loss_𝒟 ≤ 2/λ_k < 2/λ_{k+1} ≤ η^loss_ℬ`, i.e. the window ratio is at least `m`.
* **2.6 (ordering of the thresholds by coefficient size; reversal).** Muon: if
  `max_𝒟 |c| < min_ℬ |c|` then `etaLossF 𝒟 < etaLossF ℬ`; if `min_𝒟 |c| > max_ℬ |c|` then
  `etaLossF 𝒟 > etaLossF ℬ` — the **bulk**-projected update becomes loss-increasing first: the
  reverse of the suspicious-alignment ordering.
* **2.7 (two-level crossover).** Muon, `|c_i| = r_𝒟` on `𝒟`, `|c_j| = r_ℬ` on `ℬ` (both `> 0`,
  arbitrary spectrum): `etaLossF 𝒟 = 2 r_𝒟`, `etaLossF ℬ = 2 r_ℬ`,
  `θ = ψ_𝒟 r_𝒟² / (ψ_𝒟 r_𝒟² + ψ_ℬ r_ℬ²)`, hence
  `etaLossF 𝒟 < etaLossF ℬ ⟺ θ < ψ_𝒟/(ψ_𝒟 + ψ_ℬ)`.
  So Muon has a *noise-free* critical alignment `θ^crit_Muon = ψ_𝒟/(ψ_𝒟+ψ_ℬ)`; above it the bulk is
  the unstable block. (For noise-free SGD `θ^crit = 1`.)

## 3. HTMuon (`f(σ) = σ^p`, `0 ≤ p ≤ 1`, real power `Real.rpow`)

`ν_i = λ_i^p |c_i|^{p−1}`.

* **3.1 (two-level formulas).** Two-level spectrum (`λ_i = λ_𝒟` on `𝒟`, `λ_ℬ` on `ℬ`,
  `λ_𝒟 > λ_ℬ > 0`) and two-level state (`|c| = r_𝒟`, `r_ℬ > 0`):
  `etaLossF S = 2 r_S^{1−p} / λ_S^p`, so `etaLossF ℬ / etaLossF 𝒟 = m^p (r_ℬ/r_𝒟)^{1−p}`.
  At isotropic states the window ratio is `m^p`: it interpolates SGD (`p = 1`: `m`) and Muon
  (`p = 0`: `1`).
* **3.2.** In the same setting `etaStarF = 2/(ν_𝒟 + ν_ℬ)`, `ν_S = λ_S^p r_S^{p−1}`, and the
  curvature ordering holds iff `m^p > (r_𝒟/r_ℬ)^{1−p}`.
* **3.3 (crossover).** `etaLossF 𝒟 < etaLossF ℬ ⟺ (r_𝒟/r_ℬ)^{1−p} < m^p`; for `p < 1`, in terms
  of the alignment (`θ/(1−θ) = ρ m² (r_𝒟/r_ℬ)²`, `ρ = k/(d−k)`):
  `⟺ θ/(1−θ) < ρ m^{2/(1−p)}`.
* **3.4 (isotropic states, general spectrum).** If `|c_i| = r > 0` for all `i`, then
  `ν_i = λ_i^p r^{p−1}` is ordered like `λ` (for `p > 0`), the hypotheses of 1.7 hold, and the
  effective gap is `ν_k/ν_{k+1} = m^p`.

## 4. The vector model (`n = 1`)

A `d × 1` gradient has the single singular value `‖g‖`, so `F(g) = f(‖g‖) g/‖g‖`. With
`g_i = λ_i c_i + ζ_i` and `‖g‖ = √(∑ g_i²)`:

* **4.1.** `cNextVec f η c ζ i := c_i − η f(‖g‖) g_i/‖g‖` equals `P.cNext η_eff c ζ i` with
  `η_eff = η f(‖g‖)/‖g‖`. So every *pathwise* statement of Deng's one-step theory holds with `η`
  replaced by the state- and noise-dependent `η_eff` (Muon: normalised SGD, `η_eff = η/‖g‖`;
  HTMuon: `η_eff = η ‖g‖^{p−1}`).
* **4.2 (noise-free; alignment regime selected by the gradient norm).** `ζ = 0`, `f(σ) = σ^p`,
  `p < 1`, state with `s^𝒟, s^ℬ > 0`: `θ(c⁺) < θ(c) ⟺ η ‖Ax‖^{p−1} < η*₀(c)` and `>` likewise,
  where `‖Ax‖ = √(s(c))` and `η*₀` (Deng's critical step size with zero noise) is invariant
  under scaling `c ↦ a c`, `a ≠ 0`. Hence along a ray `{a c : a > 0}` the alignment decreases iff
  `a ‖Ax‖ > (η/η*₀(c))^{1/(1−p)}`: far from the optimum the alignment decreases, close to it the
  alignment increases — whatever `η` is. (For SGD, `p = 1`, the regime is selected by `η` alone.)

## 5. General matrix Muon on wide layers (no commuting assumption) — `Filter/MatrixMuon.lean`

`A ∈ ℝ^{d×d}` symmetric positive semidefinite, `W ∈ ℝ^{d×n}`, loss `L(W) = ½ tr(Wᵀ A W)`,
`G ∈ ℝ^{d×n}` any matrix (clean or stochastic gradient). A *left polar pair* of `G` is `(S, O)`
with `S ∈ ℝ^{d×d}` symmetric positive semidefinite, `O ∈ ℝ^{d×n}`, `O Oᵀ = 1` and `G = S O`
(then `S = (G Gᵀ)^{1/2}`; `O = msign(G)` is Muon's update direction; it exists when `G Gᵀ` is
invertible, which forces `d ≤ n`).

* **5.1 (equipartition of the update).** For every matrix `Π ∈ ℝ^{d×d}`:
  `tr((Π O)ᵀ (Π O)) = tr(Πᵀ Π)`. In particular for an orthogonal projector of rank `k`
  (`Π² = Π = Πᵀ`, `tr Π = k`): `‖Π O‖_F² = k`, and `‖O‖_F² = d`. So the fraction of Muon's update
  energy lying in the dominant Hessian subspace is exactly `k/d`, whatever the gradient alignment
  `θ` is (for SGD that fraction equals `θ`).
* **5.2 (exact loss change of a projected Muon step).** If `Π` is an orthogonal projector
  commuting with `A` (e.g. `P^𝒟` or `P^ℬ`), then for every `η`:
  `L(W − η Π O) − L(W) = −η ⟪Π A W, O⟫ + (η²/2) tr(Π A)`,
  where `⟪X, Y⟫ = tr(Xᵀ Y)`. The second-order term does not depend on `W`, on `G`, or on the noise.
* **5.3 (noise-free threshold).** If moreover `G = A W` (so `A W = S O`):
  `⟪Π A W, O⟫ = tr(Π S)`, hence the loss decreases iff `0 < η < 2 tr(Π S)/tr(Π A)`
  (when `tr(Π S) > 0`, `tr(Π A) > 0`). With `Π = 1`: `⟪G, O⟫ = tr S` (the nuclear norm of `G`).
* **5.4 (existence).** If `G Gᵀ` is positive definite then a left polar pair exists (and is
  unique): `S = (G Gᵀ)^{1/2}`, `O = S⁻¹ G`. (Use Mathlib's positive-semidefinite square root /
  continuous functional calculus for matrices.)
* **5.5 (link with the coordinate model).** If `A = diag(λ)` and `G = diag(σ) Q` with `σ_i > 0`
  and `Q Qᵀ = 1`, then `(diag(σ), Q)` is a left polar pair, and for `Π` the coordinate projector on
  `S ⊆ Fin d`: `tr(Π S)/tr(Π A) = ∑_{i∈S} σ_i / ∑_{i∈S} λ_i` — the Muon threshold of 2.4.

## 6. Echelon(r) in the coordinate model

Head set `H ⊆ ι` (the `r` tracked directions), tail scale `τ > 0`:
`c_i⁺ = c_i − η sign(c_i)` for `i ∈ H` (Muon on the head), `c_i⁺ = (1 − η λ_i/τ) c_i` for `i ∉ H`
(SGD with step `η/τ` on the tail). With an exact frame, `H` = the `r` largest `σ_i = λ_i|c_i|` and
`τ = max_{j∉H} σ_j`.

* **6.1.** On the tail the step is exactly Deng's noise-free SGD step with step size `η/τ`:
  `c_i⁺ = P.cNext (η/τ) c 0 i` for `i ∉ H`.
* **6.2 (loss thresholds).** For a block `S ⊆ Hᶜ` (inside the tail):
  `etaLoss_Echelon S = τ · 2 s^S/τ^S` — `τ` times Deng's noise-free threshold; so for two tail
  blocks the ratio of thresholds is exactly SGD's (`≥` the eigenvalue ratio between the blocks):
  the SGD-type window survives *inside the tail*. For `S ⊆ H`: the Muon threshold
  `2 ∑_S λ_i|c_i| / ∑_S λ_i`.
* **6.3 (head = dominant block).** If `H = 𝒟`: `etaLoss 𝒟 = 2 ∑_𝒟 λ_i |c_i|/∑_𝒟 λ_i` and
  `etaLoss ℬ = 2 τ s^ℬ/τ^ℬ ≥ 2 τ/λ_{k+1}`; with `τ = max_ℬ λ_j |c_j|` this gives
  `etaLoss ℬ ≥ 2 max_ℬ(λ_j|c_j|)/λ_{k+1}`.
