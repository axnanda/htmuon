# Fidelity note — `SuspiciousAlignment/Prob/GaussianForms.lean`

Paper: Deng et al., *Suspicious Alignment of SGD* (arXiv:2601.11789v2), Appendix A.3
"Probabilistic Lemmas", **Lemma "Variance of Gaussian Forms"** (`lem:gauss-var`, tex l. 950–959),
the Remark at tex l. 990, and its use in the proof of Lemma "Asymptotic ratio of expectations"
(tex l. 1010–1022).

Status of the file: compiles, `lake build SuspiciousAlignment.Prob.GaussianForms` succeeds, no
`sorry`/`admit`/`axiom`/`native_decide`; `#print axioms` of every main theorem shows only
`propext`, `Classical.choice`, `Quot.sound`. **Nothing is left unproven**: items (i)–(v) of the
task are all proved.

## 1. Formal model of `z ∼ 𝒩(0, C)`

Mathlib v4.35 survey (what exists / what does not):

| needed | Mathlib |
|---|---|
| real Gaussian `gaussianReal μ v`, mean, variance, mgf, all moments finite | `Probability/Distributions/Gaussian/Real.lean` (but **no** `𝔼x³`, `𝔼x⁴`) |
| standard Gaussian on a Euclidean space, rotation invariance | `Gaussian/Multivariate.lean`: `stdGaussian`, `stdGaussian_eq_map_pi_orthonormalBasis`, `map_pi_eq_stdGaussian` |
| `𝒩(m, S)` on `EuclideanSpace ℝ ι` | `multivariateGaussian m S := (stdGaussian).map (x ↦ m + S^{1/2} x)`, `charFun_multivariateGaussian`, `covariance_eval_multivariateGaussian` |
| variance of a linear functional of a Gaussian | available abstractly (`covarianceBilin`) |
| variance of a **quadratic** form, Isserlis/Wick, fourth moments | **not available** |
| variance of sums of independent variables on a product space | `variance_sum_pi` |
| derivatives of the mgf = moments | `iteratedDeriv_mgf_zero` |

Choice made: `IsCenteredGaussian z C μ` (for `z : Ω → ι → ℝ`) is by definition
`HasLaw (fun ω ↦ toLp 2 (z ω)) (multivariateGaussian 0 C) μ`, i.e. the law of `z` is Mathlib's
multivariate Gaussian with mean `0` and covariance matrix `C` (characteristic function
`t ↦ exp(-tᵀCt/2)` for PSD `C`). This is the textbook meaning of `z ∼ 𝒩(0, C)`; degenerate
(singular) `C` is allowed, as in the paper (`C ⪰ 0`).

Supporting facts proved, showing the model is the expected one and is non-vacuous:

* `isCenteredGaussian_of_iIndepFun`: if `w_k` are independent real random variables with law
  `gaussianReal 0 1` (`iIndepFun`) and `M : Matrix ι κ ℝ`, then `z = M w` is
  `IsCenteredGaussian` with covariance `M Mᵀ` (the "robust" concrete model; the law depends on
  `M` only through `M Mᵀ`, `GaussianForms.gaussianImage_map_toLp`, proved by characteristic
  functions).
* `GaussianForms.sqrt_mul_sqrt_transpose`: every PSD `C` is `M Mᵀ` with `M = C^{1/2}`.
* `IsCenteredGaussian.covariance_apply`: `Cov(z_i, z_j) = C_ij`.
* `IsCenteredGaussian.mulVec`: `z ∼ 𝒩(0, C) ⟹ A z ∼ 𝒩(0, A C Aᵀ)`; with `A = Uᵀ` this is the
  paper's passage from the noise `ξ ∼ 𝒩(0, Σ)` to its eigen-coordinates `ζ ∼ 𝒩(0, UᵀΣU)`.
* `isCenteredGaussian_ofLp` (every `C` is realised on `(ℝ^ι, 𝒩(0,C))`),
  `iIndepFun_eval_stdNormalPi` (independent standard normals exist), plus two `example`s
  instantiating the main theorems on these spaces.

## 2. Table: paper item → Lean declaration

All Lean statements below assume `hz : IsCenteredGaussian z C μ` and `hC : C.PosSemidef`
(Mathlib's `PosSemidef` = symmetric + `xᵀCx ≥ 0`, i.e. the paper's `C = Cᵀ ⪰ 0`).
`‖C‖` is the l2-operator (spectral) norm `Matrix.Norms.L2Operator`, the paper's `‖C‖₂`.
`g ⬝ᵥ z` is `gᵀz`, `z ⬝ᵥ D *ᵥ z` is `zᵀDz`.

| Paper item (tex lines) | Lean declaration | Status | Explanation |
|---|---|---|---|
| Lemma gauss-var, whole statement (950–959) | `variance_gaussian_forms` | exact | Literal statement: diagonal `D = diagonal d`, both identities and both inequalities; `‖g‖₂² = ∑ gᵢ²`, `tr(D²) = ((diagonal d)^2).trace`. |
| `Var(gᵀz) = gᵀCg` (954) | `IsCenteredGaussian.variance_linear` | exact | |
| `gᵀCg ≤ ‖C‖₂‖g‖₂²` (954) | `GaussianForms.dotProduct_mulVec_le`, `GaussianForms.dotProduct_mulVec_le_sum_sq`, `IsCenteredGaussian.variance_linear_le` | strengthened | True for **every** real square matrix `C` (no symmetry/positivity needed). |
| `Var(zᵀDz) = 2 tr((CD)²)` (957) | `IsCenteredGaussian.variance_quadratic` | strengthened | Proved for every **symmetric** `D` (diagonal is a special case). Coordinate form for diagonal `D`: `IsCenteredGaussian.variance_diagonal_quadratic`: `Var(∑ dᵢ zᵢ²) = 2 ∑ᵢⱼ dᵢ dⱼ C_ij²`. |
| `2 tr((CD)²) ≤ 2‖C‖₂² tr(D²)` (957) | `GaussianForms.trace_mul_sq_le_of_isSymm`, `IsCenteredGaussian.variance_quadratic_le` | strengthened | True for every real `C` and every symmetric `D`; for arbitrary `D` with `tr(DᵀD)` on the right (`GaussianForms.trace_mul_mul_self_le`). Symmetry of `D` cannot be dropped: `GaussianForms.not_trace_mul_sq_le_of_not_isSymm`. |
| hypothesis `‖C‖₂ < ∞` (951) | — | (vacuous) | Automatic for a finite matrix; no Lean hypothesis. |
| (implicit) `𝔼[gᵀz] = 0` | `IsCenteredGaussian.integral_linear` | extra | |
| (implicit; gives Lemma "Elementwise expectation" `lem:blk-exp-t-app`, tex l. 1062, for Gaussian noise) `𝔼[zᵀDz] = tr(CD)` | `IsCenteredGaussian.integral_quadratic`, `IsCenteredGaussian.integral_diagonal_quadratic` | extra | |
| (used silently at 1022) variance of the **sum** of the linear and the quadratic form | `IsCenteredGaussian.covariance_linear_quadratic` (`Cov(gᵀz, zᵀDz) = 0`), `IsCenteredGaussian.variance_form` (`Var(χ + gᵀz + zᵀDz) = gᵀCg + 2tr((CD)²)`), `IsCenteredGaussian.variance_form_le`, `IsCenteredGaussian.memLp_form`, `IsCenteredGaussian.integral_form`; all three in one statement: `IsCenteredGaussian.affine_quadratic_form` | extra (fills a gap) | See gap G1 below. |
| same, concrete model `z = M w` | `variance_form_of_iIndepFun` | extra | |
| decomposition `s_{t+1}^S = χ_S + g_Sᵀz + zᵀD_S z` (1011–1021) | `Spec.mom_cNext_eq_gaussian_form` with `GaussianForms.chi`, `GaussianForms.gVec`, `GaussianForms.dVec` | exact | Pure algebra, for every noise vector `ζ`; the paper's `χ`, `g`, `D` are correct. `s_{t+1}^S` is `P.mom S 2 (P.cNext η c ζ)` (`= P.sD/P.sB` of the next state for `S = 𝒟/ℬ`, by definition). |
| `𝔼[s_{t+1}^S ∣ x_t]` | `Spec.integral_sNext_of_isCenteredGaussian` (`= Spec.EsNext N S η c` when `N.kap2 i = C i i`), `Spec.memLp_sNext_of_isCenteredGaussian` | exact (Gaussian case) | Confirms the definition `Spec.EsNext` in `Defs.lean`. |
| "`Var(s_{t+1}^S) = O(\|S\|)` by Lemma gauss-var and Assumption 1" (1022) | exact value: `Spec.variance_sNext_of_isCenteredGaussian`; bounds: `Spec.variance_sNext_le_of_isCenteredGaussian`, `Spec.variance_sNext_le_trace_of_isCenteredGaussian` (with `tr C` instead of `‖C‖₂`, via `GaussianForms.l2_opNorm_le_trace_of_posSemidef`), `Spec.variance_sNext_le_lam1_of_isCenteredGaussian` | hypotheses-added | Finite-`d` inequalities; the `O(\|S\|)` conclusion needs a bound on `λ_1` that Assumption 1 does not contain. See G2. |
| Remark (990): "standard results for Gaussian distributions" | — | (the paper gives no proof) | A complete proof is formalised here. |

## 3. Proof (the paper gives none)

`z = C^{1/2} w` with `w` standard normal, so `χ + gᵀz + zᵀDz = χ + aᵀw + wᵀQw`,
`a = C^{1/2}g`, `Q = C^{1/2} D C^{1/2}` (symmetric because `D` is). Diagonalise
`Q = U diag(λ) Uᵀ`; by rotation invariance `y = Uᵀw` is again standard normal and the form is
`χ + ∑ᵢ (αᵢ yᵢ + λᵢ yᵢ²)`, `α = Uᵀa`, a sum of independent terms. With
`𝔼y = 𝔼y³ = 0`, `𝔼y² = 1`, `𝔼y⁴ = 3` (obtained from the derivatives of the mgf `e^{t²/2}`;
`GaussianForms.integral_pow_four_stdNormal` etc.), `Var(αy + λy²) = α² + 2λ²`, so the variance
is `∑ αᵢ² + 2∑ λᵢ² = ‖a‖² + 2 tr(Q²) = gᵀCg + 2 tr((CD)²)` and the mean is
`χ + ∑ λᵢ = χ + tr(CD)`. Taking `D = 0`, resp. `g = 0`, gives the two identities of the lemma, and
`Cov(gᵀz, zᵀDz) = ½(Var(sum) − Var(lin) − Var(quad)) = 0`.

Inequalities: `gᵀCg ≤ ‖g‖‖Cg‖ ≤ ‖C‖₂‖g‖²` (Cauchy–Schwarz); and
`tr((CD)²) = ⟨(CD)ᵀ, CD⟩_F ≤ ‖CD‖_F² ≤ ‖C‖₂² ‖D‖_F²`, with `‖D‖_F² = tr(DᵀD) = tr(D²)` for
symmetric `D`. Numerical checks (random instances and Monte Carlo) were run before formalising
(`python3`, numpy): both identities, both inequalities, `Cov = 0`, and the failure of the
formula/inequality for non-symmetric `D`.

## 4. Gaps / inaccuracies found in the paper

**G0 (harmless).** The lemma itself is correct as stated. The hypothesis `‖C‖₂ < ∞` is vacuous.
Positivity of `C` is not needed for the two inequalities, only for `z ∼ 𝒩(0, C)` to make sense.
The restriction to diagonal `D` is unnecessary but *symmetry* matters: for non-symmetric `D`
the correct formula is `Var(zᵀDz) = 2 tr((C·(D+Dᵀ)/2)²)`, which differs from `2 tr((CD)²)`
(numerically: `C = MMᵀ` random, `D` random non-symmetric gave `107.7` vs `54.1`), and the
inequality `tr((CD)²) ≤ ‖C‖₂² tr(D²)` is false: `C = diag(1,0)`, `D = [[0,1],[-1,0]]` gives
`0 ≤ -2` (formal counterexample `GaussianForms.not_trace_mul_sq_le_of_not_isSymm`).

**G1 (gap in the use of the lemma, tex l. 1022).** "The variance of `s_{t+1}^S` is the variance
of the sum of the linear and quadratic forms. By Lemma gauss-var …". The lemma only gives the
two variances *separately*; the variance of the sum also involves `2 Cov(gᵀz, zᵀDz)`. The
covariance is in fact `0` (third moments of a centred Gaussian vanish), which we prove
(`IsCenteredGaussian.covariance_linear_quadratic`), so
`Var(s_{t+1}^S) = g_SᵀCg_S + 2tr((CD_S)²)` exactly (`Spec.variance_sNext_of_isCenteredGaussian`).
(Alternatively `Var(X+Y) ≤ 2Var X + 2Var Y` would suffice for an `O(·)` bound.)

**G2 (the claim `Var(s_{t+1}^S) = O(|S|)` does not follow from Assumption 1 as stated).**
Exactly, with `g_S`, `D_S` as in the paper,

`Var(s_{t+1}^S) = g_SᵀCg_S + 2tr((CD_S)²) ≤ 4η²‖C‖₂ ∑_{i∈S} λ_i⁴(1-ηλ_i)²c_i² + 2η⁴‖C‖₂² ∑_{i∈S} λ_i⁴`
(`Spec.variance_sNext_le_of_isCenteredGaussian`).

* *Role of the trace assumption.* What the bound needs is `‖C‖₂ = ‖Σ‖₂ = s_max = O(1)`
  uniformly in `d`. This follows from "`Tr(Σ) ∈ (0,∞)`" only if the trace bound is uniform in
  `d` (`‖C‖₂ ≤ tr C`, `GaussianForms.l2_opNorm_le_trace_of_posSemidef`; bound in terms of the
  trace: `Spec.variance_sNext_le_trace_of_isCenteredGaussian`). If the trace is merely finite for
  each `d` (e.g. `Σ = d·I`), no `O(|S|)` bound holds. Conversely a uniform trace bound is much
  stronger than needed (isotropic noise `Σ = σ²I` has `‖Σ‖₂ = σ²` but `Tr Σ = σ²d`) and it makes
  the noise asymptotically invisible: `e_S = ∑_{i∈S} λ_i²κ_i² ≤ (max_S λ_i²)·Tr Σ = o(|S|)`
  (because `max_S λ_i⁸ ≤ ∑_S λ_i⁸ = O(|S|)`), so `η²e_S/|S| → 0` and the limits
  `ℓ'_S = lim 𝔼[s_{t+1}^S]/|S|` do not depend on the noise at all. The natural hypothesis is
  `s_max = O(1)` (cf. the "bounded noise (`s_max < ∞`)" of Theorem "Separation of Alignment
  Regimes", tex l. 459).
* *Quadratic part: OK.* `2‖C‖₂² tr(D_S²) = 2η⁴‖C‖₂² ∑_{i∈S}λ_i⁴ = O(|S|)` by the block spectral
  moment `p = 4` (and `η = O(1)`, which the paper does not state either). This is the only place
  where the lemma's bound `2‖C‖₂²tr(D²)` is used, and there it does give `O(|S|)`.
  (With a uniform trace bound and bounded `λ_1` the quadratic part is even `O(1)`:
  `tr((CD)²) ≤ ‖D‖₂²‖C‖_F² ≤ η⁴λ_1⁴ (Tr Σ)²`.)
* *Linear part: not controlled by Assumption 1.* `‖C‖₂‖g_S‖² = 4η²‖C‖₂ ∑_{i∈S} λ_i⁴(1-ηλ_i)²c_i²`
  is a *weighted* energy of the state. Assumption 1 bounds `(1/d)∑c_i²` and the block moments
  `(1/|S|)∑_S λ_i^p`, `p ≤ 8`, but not `sup_i λ_i`. Counterexample (all four items of
  Assumption 1 hold): `d = 2k`, `λ_1 = k^{1/8}`, `λ_i = 1` for `1 < i ≤ k`, `λ_i = ½` on the
  bulk, `c_1² = d`, `c_i = 0` otherwise, `Σ = C = diag(½, 0, …, 0)`, `η` fixed. Then
  `(1/k)∑_𝒟 λ_i^p → 1` (`p < 8`), `→ 2` (`p = 8`), `(1/d)∑c_i² = 1`, `Tr Σ = ½`, but
  `Var(s_{t+1}^𝒟) = g_1²C_11 + 2(C_11 η²λ_1²)² ≈ 2η²k^{1/2}(1-ηk^{1/8})²·d`, which is
  `≫ d` (of order `d^{7/4}`); also `𝔼[s_{t+1}^𝒟]/k → ∞`, so `ℓ'_𝒟` is not finite, contrary to
  the statement of Lemma ratio-asymp. (Numerically, `Var/k = 0.27, 1.87, 7.66, …, 2.4·10³` for
  `k = 10², 10⁴, 10⁶, …, 10¹⁰`, `η = 0.1`.)
* *What is true.* (a) If additionally `λ_1 = O(1)` (uniformly bounded spectrum), then
  `Var(s_{t+1}^S) ≤ 4η²‖C‖₂λ_1⁴(1+|η|λ_1)² ∑_{i∈S}c_i² + 2η⁴‖C‖₂²λ_1⁴|S| = O(|S|)`
  (`Spec.variance_sNext_le_lam1_of_isCenteredGaussian`; needs `∑_S c_i² = O(d)` = trajectory
  boundedness and `|S| = Θ(d)` = block proportion). (b) Under Assumption 1 alone (plus
  `‖C‖₂, η = O(1)`): `max_S λ_i ≤ (∑_S λ_i⁸)^{1/8} = O(|S|^{1/8})`, so the same inequality gives
  `Var(s_{t+1}^S) = O(d^{7/4}) = o(|S|²)`. This is weaker than `O(|S|)` (so Lemma wlln-blocks
  does not apply as stated) but still enough for its Chebyshev argument, which only uses
  `Var(∑ y_i)/|S|² → 0`: the centred statement
  `s_{t+1}^S/|S| − 𝔼[s_{t+1}^S]/|S| → 0` in probability survives.
* *Relative size.* What the downstream transfer `𝔼[θ_{t+1}] − thetaBarNext → 0` needs is
  `Var(s_{t+1}^S)/(𝔼 s_{t+1})² → 0`. If `𝔼[s_{t+1}]/d → ℓ > 0` then `(𝔼 s_{t+1})² = Θ(d²)` and
  the ratio is `O(1/d)` in case (a), `O(d^{-1/4})` in case (b). The lemma gives no information
  when `𝔼[s_{t+1}] = o(d)` (e.g. `x_t` small and trace-bounded noise), and positivity of the
  limit of `𝔼[s_{t+1}^𝒟]/k` is an extra hypothesis (the paper asserts `y_0 ∈ (0,∞)` without
  proof; `λ_{ℬ,p} = 0` is even allowed by Assumption 1).

## 5. Notes for downstream files

* To use the results for the SGD noise: from `ξ ∼ 𝒩(0, Σ)` get `ζ = Uᵀξ ∼ 𝒩(0, UᵀΣU)` with
  `IsCenteredGaussian.mulVec`, or directly assume `IsCenteredGaussian ζ C μ` with
  `N.kap2 i = C i i`. Then `Spec.memLp_sNext_of_isCenteredGaussian`,
  `Spec.integral_sNext_of_isCenteredGaussian` and the variance bounds discharge exactly the
  hypotheses `MemLp … 2`, `∫ … = EsNext`, `Var …` used in `Prob/Concentration.lean`
  (statements with `P.sD`/`P.sB` follow by `exact`, since `sD c = mom D 2 c` by definition; see
  the `example` at the end of `namespace Spec`).
* The norm in all statements is the scoped instance `Matrix.Norms.L2Operator`; files using the
  bounds must `open scoped Matrix.Norms.L2Operator` (or use the `tr C` versions).
* Definitions introduced here (none in `Defs.lean` was changed): `IsCenteredGaussian`,
  `GaussianForms.stdNormalPi`, `GaussianForms.gaussianImage`, `GaussianForms.mgfDeriv`,
  `GaussianForms.chi`, `GaussianForms.gVec`, `GaussianForms.dVec`.
