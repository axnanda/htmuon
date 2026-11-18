# Fidelity note — `SuspiciousAlignment/Prob/Concentration.lean`

Module `SuspiciousAlignment.Prob.Concentration` (imports `Mathlib`, `SuspiciousAlignment.Defs`;
`Defs` is used only in Part 5). Paper: Deng et al., arXiv:2601.11789v2, Appendix A.3 (tex 948–991)
and A.4 (tex 993–1058).

Status of the file: compiles, `lake build SuspiciousAlignment.Prob.Concentration` succeeds, no
`sorry`/`admit`/`axiom`/`native_decide`; every theorem depends only on
`propext`, `Classical.choice`, `Quot.sound`. Nothing in scope was left unproved.

## Conventions

* The probability space depends on the dimension, so all asymptotic statements are about a family
  `(Ω n, μ n)` of probability spaces (`[∀ n, IsProbabilityMeasure (μ n)]`), `Y n : Ω n → ℝ`.
* "`Y_n → l` in probability" is written inline as
  `∀ ε : ℝ, 0 < ε → Tendsto (fun n => μ n {ω | ε ≤ |Y n ω - l|}) atTop (𝓝 0)` (no new definition).
  `Concentration.tendstoInMeasure_const_iff` identifies it with Mathlib's `TendstoInMeasure` on a
  fixed space.
* The paper's "`𝔼[· | x_t]`" is an integral over the law of the fresh noise with `x_t` fixed; here
  it is `∫ ω, … ∂μ n`.
* `X / Z` uses Lean's `x / 0 = 0`. In the ratio lemmas `0 ≤ X ≤ Z`, so on `{Z = 0}` this is
  `0 / 0 = 0`, i.e. the paper's convention `θ(0) = 0`. Denominators that matter are controlled by
  explicit hypotheses (`0 < 𝔼 Z`, `ρ ≠ 0`, `ρ a + b ≠ 0`); no theorem is true because of a
  vanishing denominator.

## Table

| Paper item (tex lines) | Lean declaration | Status | Explanation |
|---|---|---|---|
| Lemma "Variance of Gaussian Forms" (950–959) | — | not-formalized (here) | Owned by `Prob/GaussianForms.lean`; variances enter this file only as hypotheses. |
| Lemma "WLLN for Block Averages", part 1 (962–966), proof 969–984 | `wlln_block_average_centered` | equivalent-reformulation | Block sum `S_n`, block size `N_n : ℕ → ℝ`, `N_n → ∞`, `Var(S_n) ≤ K N_n` eventually (= `O(N_n)`), `S_n ∈ L²` (implicit in the paper since a variance is used). Conclusion `S_n/N_n − 𝔼[S_n/N_n] → 0` in probability. |
| same, literal form | `wlln_finset_block_average_centered` | exact | Index sets `s n : Finset (ι n)`, `y n i ∈ L²`, `|s n| → ∞`, `Var(∑ y_i) ≤ K |s n|` eventually. |
| WLLN part 2 (967) | `wlln_block_average`, `wlln_finset_block_average` | exact | `(1/|S_d|) ∑ 𝔼 y_i → ℓ` ⟹ block average → ℓ in probability. |
| (engine of the proof: Chebyshev, 971–983) | `tendstoInProb_sub_integral_of_variance_tendsto_zero`, `tendstoInProb_of_variance_tendsto_zero` | extra | `Var(Y_n) → 0` ⟹ `Y_n − 𝔼Y_n → 0` in probability; plus the version with `𝔼Y_n → l`. |
| WLLN under a weaker variance condition | `wlln_centered_of_variance_div_sq_tendsto_zero` | strengthened | `Var(S_n)/N_n² → 0` suffices (`O(N_n)` is not needed). Relevant because `Var(s^S_{t+1}) = O(|S|)` is not implied by Assumption 1 as stated (gap G3d). |
| Lemma "CMT with Dominated Convergence" (986–988; no proof in the paper) | `tendsto_integral_comp_of_tendstoInProb` | hypotheses-added | Added: `Measurable f`, `AEMeasurable (Y n)` — implicit in the paper (needed for `𝔼 f(y_n)` to exist). Otherwise exactly: `f` bounded, continuous at `y₀`, `y_n → y₀` in probability ⟹ `𝔼 f(y_n) → f(y₀)`. |
| same, `f` bounded only along the `y_n` | `tendsto_integral_comp_of_tendstoInProb_of_ae_bounded` | strengthened | Needed for the paper's own application `f(y) = (1+y)⁻¹`, which is not bounded on `ℝ` (gap G3c). |
| bounded convergence | `tendsto_integral_of_tendstoInProb_of_bounded` | extra | `A ≤ Y_n ≤ B` a.s., `Y_n → y₀` in probability ⟹ `𝔼Y_n → y₀`. |
| quantitative estimate behind the CMT | `Concentration.abs_integral_comp_sub_le` | extra | `|𝔼f(Y) − f(y₀)| ≤ ε + (M + |f y₀|)·ℙ(|Y − y₀| ≥ δ)`. |
| Lemma "Asymptotic ratio of expectations" (995–1009): quantitative core | `abs_integral_ratio_sub_ratio_integral_le_L1`, `abs_integral_ratio_sub_ratio_integral_le` | strengthened | Single probability space, `0 ≤ X ≤ Z` a.s., `𝔼Z > 0`: `|𝔼[X/Z] − 𝔼X/𝔼Z| ≤ 𝔼|Z − 𝔼Z|/(2𝔼Z) ≤ √Var(Z)/(2𝔼Z)`. Constant `1/2`; `Var X` is not needed. |
| optimality of the constant | `abs_integral_ratio_sub_ratio_integral_le_sharp` | extra | Fair coin, `Z = 1/2, 3/2`, `X = 1/2, 0`: both sides equal `1/4`. Also shows `𝔼[X/Z] ≠ 𝔼X/𝔼Z` without concentration. |
| two-block form (`X = s^𝒟_{t+1}`, `Y = s^ℬ_{t+1}`) | `abs_integral_ratio_add_sub_ratio_integral_le` | strengthened | `|𝔼[X/(X+Y)] − 𝔼X/(𝔼X+𝔼Y)| ≤ (√Var X + √Var Y)/(2(𝔼X+𝔼Y))`; no covariance between blocks needed. |
| asymptotic transfer | `tendsto_integral_ratio_sub_ratio_integral`, `tendsto_integral_ratio_add_sub_ratio_integral` | strengthened | `Var(Z_n)/(𝔼Z_n)² → 0` (resp. both block variances over `(𝔼X_n+𝔼Y_n)²`) ⟹ `𝔼[ratio] − ratio of 𝔼 → 0`. No normalisation by `k`, no existence of `ℓ'_𝒟, ℓ'_ℬ`, no `y₀ ∈ (0,∞)`. |
| … with a limit | `tendsto_integral_ratio_of_tendsto_ratio_integral`, `tendsto_integral_ratio_add_of_tendsto_ratio_integral` | strengthened | If the ratio of expectations → `L`, then `𝔼[ratio] → L`. |
| proof step "`y_{k,d} → y₀` in probability" (1023–1028) | `tendstoInProb_ratio_of_tendstoInProb` | equivalent-reformulation | In `θ`-form: `X_n/k_n → a`, `Y_n/m_n → b`, `k_n/m_n → ρ ≠ 0`, `ρa + b ≠ 0` ⟹ `X_n/(X_n+Y_n) → ρa/(ρa+b)` in probability. Avoids `s^ℬ/s^𝒟` (undefined when `s^𝒟 = 0`). |
| eq. (ratio-asymp) (1002–1008) | `tendsto_integral_ratio_paper` | hypotheses-added | `a = ℓ'_𝒟 > 0`, `b = ℓ'_ℬ ≥ 0`, `ρ > 0`, `X_n, Y_n ≥ 0` a.s. and a.e.-measurable, convergences in probability as hypotheses ⟹ `𝔼[X_n/(X_n+Y_n)] → 1/(1 + b/(ρa))`. `a > 0` and the existence of the limits are asserted, not proved, in the paper (G3a, G3b). `k_n/m_n → ρ` generalises the paper's constant `ρ`. |
| same, general form | `tendsto_integral_ratio_of_tendstoInProb` | strengthened | Only `ρ ≠ 0`, `ρa + b ≠ 0`; limit `ρa/(ρa+b)`. Covers `b = 0` and `a = 0 < b`, excluded in the paper by "`y₀ ∈ (0,∞)`". |
| Lemma 995–1009, complete abstract form (WLLN + CMT, variances as hypotheses) | `tendsto_integral_ratio_of_variance_bound` | hypotheses-added | `Var(X_n) ≤ K₁k_n`, `Var(Y_n) ≤ K₂m_n`, `k_n, m_n → ∞`, `𝔼X_n/k_n → a > 0`, `𝔼Y_n/m_n → b ≥ 0`, `k_n/m_n → ρ > 0`. A non-vacuity `example` follows it. |
| necessity of `ℓ'_𝒟 > 0` | `ratio_asymp_fails_without_positive_limit` | paper-claim-false (without the extra hypothesis) | Formal counterexample with `a = b = 0`: `𝔼[X/(X+Y)] = 1/2`, `𝔼X/(𝔼X+𝔼Y) = 1/4` for every `n`. |
| "consequence" display (1038–1048), sign of `θ_t` formula | `Concentration.ratio_eq_one_div_one_add`, `Concentration.ratio_ne_one_div_one_sub` | paper-claim-false (typo) | Correct: `θ = 1/(1 + (1/ρ)(s^ℬ/(d−k))/(s^𝒟/k))`. With the printed `1 − …` the identity fails (`x=2, y=k=m=1`: `2/3 ≠ 2`). |
| display 1040–1048 as a statement about limits | `Concentration.ratio_limit_lt_iff` | equivalent-reformulation | `1/(1+b'/(ρa')) < 1/(1+b/(ρa)) ↔ b a' − b' a < 0` for `ρ, a, a' > 0`, `b, b' ≥ 0`; `b a' − b' a = lim 𝔼[f_t]/(k(d−k))`. The paper omits the normalisation (G4b). |
| exact finite-`d` version | `Concentration.ratio_lt_ratio_iff`, `Concentration.ratio_sub_ratio_eq` | extra | `x'/(x'+y') < x/(x+y) ↔ y x' − y' x < 0`, and the difference equals `(y x' − y' x)/((x'+y')(x+y))`, i.e. `thetaBarNext − θ_t = 𝔼[f_t]/(𝔼[s_{t+1}] s_t)`. |
| "it suffices to analyse the sign of `𝔼[f_t]`" (1058) | `eventually_integral_ratio_add_lt_add_of_le`, `eventually_integral_ratio_add_lt_of_gap`, `eventually_integral_ratio_add_lt_of_tendsto_lt` | weakened / hypotheses-added | Correct forms: (i) ratio of expectations `≤ θ_n` eventually ⟹ `𝔼[θ'] < θ_n + c` eventually for every `c > 0`; (ii) uniform margin `c > 0` ⟹ `𝔼[θ'] < θ_n` eventually; (iii) strict inequality of limits ⟹ strict inequality for all large `n`. |
| passage "strict for every `d`" ⟹ "strict in the limit" | `strict_drift_not_preserved_in_limit` | paper-claim-false | `X_n = 1`, `Y_n = 1/(n+1)`, `θ_n = 1`: `𝔼[X_n/(X_n+Y_n)] < 1` for all `n`, limit `= 1`. |
| interface with `Defs.lean` | `Concentration.abs_integral_theta_sub_thetaBarNext_le`, `Concentration.tendsto_integral_theta_sub_thetaBarNext` | extra | `|𝔼θ_{t+1} − thetaBarNext| ≤ (√Var s^𝒟_{t+1} + √Var s^ℬ_{t+1})/(2(EsNext 𝒟 + EsNext ℬ))` and the asymptotic version, with `𝔼 s^S_{t+1} = EsNext` and the variance conditions as hypotheses. |

Helper lemmas (namespace `SuspiciousAlignment.Concentration`):
`tendstoInProb_of_sub_of_tendsto`, `covariance_sq_le_variance_mul_variance` (Cauchy–Schwarz),
`sqrt_variance_add_le` (Minkowski for standard deviations),
`integral_abs_sub_integral_le_sqrt_variance`, `coin`, `integral_coin`,
`tendstoInProb_div_of_bounded`, `eventually_lt_add_of_tendsto_sub`.

## The quantitative inequality (re-derivation)

Let `R = X/Z ∈ [0,1]`, `m = 𝔼Z > 0`. Since `0 ≤ X ≤ Z`, `X = R Z` everywhere (also where `Z = 0`).
Hence `m𝔼R − 𝔼X = 𝔼[R(m − Z)] = 𝔼[(R − 1/2)(m − Z)]` (as `𝔼[m − Z] = 0`), and `|R − 1/2| ≤ 1/2`:

`|𝔼[X/Z] − 𝔼X/𝔼Z| = |Cov(R, Z)|/𝔼Z ≤ 𝔼|Z − 𝔼Z|/(2𝔼Z) ≤ √Var(Z)/(2𝔼Z)`.

So the "right" statement has constant `1/2`, involves only the fluctuation of the denominator, and
needs no second moment of `X`. The form `C(√Var X + √Var Z)/𝔼Z` suggested in the task holds a
fortiori with `C = 1/2`; the two-block form with `√Var X + √Var Y` comes from Minkowski.
Checked numerically on 2·10⁵ random discrete laws (max ratio LHS/RHS = 0.9992).

## Gaps and errors found in the paper

**G1 (WLLN, 962–984).** Correct. Implicit: the `y_i` are in `L²`; the probability space depends on
`d`. The hypothesis `O(|S_d|)` is stronger than needed (`o(|S_d|²)` suffices).

**G2 (CMT, 986–988).** Stated without proof; correct once `f` is assumed Borel measurable.

**G3 (Lemma "Asymptotic ratio of expectations", 995–1036).**

* **G3a — existence of `ℓ'_S`.** The lemma treats
  `ℓ'_S = lim (1/|S|) 𝔼[s^S_{t+1} | x_t]` as existing. Assumption 1 only bounds `(1/d)∑ c_{i,t}²`;
  the limit of `(1/|S|)∑_S λ_i²(1−ηλ_i)²c_{i,t}²` need not exist. In Lean it is a hypothesis
  (`hEX`, `hEY`) of the paper-form theorems; the quantitative route does not need it.
* **G3b — "`y₀ ∈ (0,∞)`" (1027) is asserted, not derived.** `ℓ'_𝒟 > 0` is essential. Under
  Assumption 1 as written ("`Tr(Σ)` bounded") one has `e_S ≤ λ_1² Tr Σ = o(|S|)` (the `p = 8`
  moment gives `λ_1 = O(k^{1/8})`), so the noise does not contribute to `ℓ'_S`, and
  `ℓ'_𝒟 = ℓ'_ℬ = 0` e.g. whenever the `λ_i` are bounded and `‖x_t‖² = o(d)`. Then the formula
  `1/(1 + ℓ'_ℬ/(ρℓ'_𝒟))` is `0/0` and the interchange of `𝔼` and ratio can fail.
  Formal abstract counterexample: `ratio_asymp_fails_without_positive_limit`.
  Informal instance of the SGD model itself (checked by Monte Carlo, not formalized):
  `λ_i = 2` on `𝒟`, `1` on `ℬ`, `k = d/2`, `x_t = u_1 + u_{k+1}`, `Σ = uuᵀ` with
  `u = (u_1 + u_{k+1})/√2`, `η = 0.3`. All four items of Assumption 1 hold, yet for every `d`
  `𝔼[θ_{t+1}] ≈ 0.520` while `𝔼s^𝒟_{t+1}/𝔼s_{t+1} ≈ 0.605`.
  `ℓ'_ℬ > 0` is not needed (`tendsto_integral_ratio_of_tendstoInProb` allows `b = 0`).
* **G3c — application of the CMT lemma (1029).** `f(y) = (1+y)⁻¹` is "bounded and continuous" only
  on `[0,∞)`; on `ℝ` it is unbounded near `−1`, so the lemma as stated does not literally apply.
  Fixed by `tendsto_integral_comp_of_tendstoInProb_of_ae_bounded`, or by working with
  `θ = X/(X+Y) ∈ [0,1]` directly (what the Lean proof does). Also `y_{k,d} = s^ℬ/s^𝒟` is undefined
  on `{s^𝒟_{t+1} = 0}`; the Remark at tex 928–934 shows this is a null set only when the Gaussian
  noise is non-degenerate on `𝒟`, whereas the paper assumes just `Σ ⪰ 0` (tex 875). The `θ`-form
  with `0/0 = 0` needs no such assumption.
* **G3d — "`Var(s^S_{t+1}) = O(|S|)` by Lemma gauss-var and Assumption 1" (1022).** Not formalized
  here (hypothesis). Observation: the linear part has variance `gᵀCg ≤ s_max·4η²∑_S λ_i⁴(1−ηλ_i)²c_i²`,
  and bounding this by `O(|S|)` needs more than Assumption 1 (e.g. `sup_d λ_1 < ∞`). Example
  compatible with Assumption 1: `λ_1 = k^{1/8}`, other `λ_i = 1` on `𝒟`, `x_t = k^{1/4}u_1`,
  `Σ = u_1u_1ᵀ`; then `Var(s^𝒟_{t+1}) ≈ 4η⁴k^{5/4}`, not `O(k)`, although `𝔼s^𝒟_{t+1}/k → η²`.
  The WLLN conclusion survives because `Var = o(k²)`
  (`wlln_centered_of_variance_div_sq_tendsto_zero`).
* What **is** justified: given `Var(s^S_{t+1}) = O(|S|)`, existence of `ℓ'_𝒟 > 0`, `ℓ'_ℬ ≥ 0`, and
  `k/(d−k) → ρ > 0`, eq. (ratio-asymp) holds: `tendsto_integral_ratio_of_variance_bound`.

**G4 (the displayed "consequence", 1038–1048, and the sentence at 1058).**

* **G4a — sign typo.** `lim θ_t = 1/(1 − …)` should be `1/(1 + …)`.
* **G4b — missing normalisation.** `lim 𝔼[s^ℬ_t s^𝒟_{t+1}] − lim 𝔼[s^ℬ_{t+1} s^𝒟_t] < 0` is
  written without the factor `1/(k(d−k))`; each term is of order `k(d−k) → ∞`, so the expression
  is `∞ − ∞`. With the normalisation the display is an equivalence between limits
  (`Concentration.ratio_limit_lt_iff`), provided the four limits exist and `a, a' > 0`.
* **G4c — direction and strictness.** The display derives `lim 𝔼f_t < 0` from
  `lim 𝔼θ_{t+1} < lim θ_t`; the paper then uses the converse, starting from the sign of
  `𝔼[f_t | x_t]` at finite `d`. A strict inequality for every `d` only gives `≤` in the limit
  (`strict_drift_not_preserved_in_limit`). Informally (not formalized) this happens in the model:
  for `x_t` in the dominant subspace (`s^ℬ_t = 0`, `θ_t = 1`) one has
  `𝔼f_t = −η²e_ℬ s^𝒟_t < 0` for every `d`, but with bounded `λ_i`, bounded trace and
  `‖x_t‖² ≍ d` the bulk energy `𝔼s^ℬ_{t+1} = η²e_ℬ = O(1)` is negligible against
  `𝔼s^𝒟_{t+1} ≍ d`, so `lim 𝔼θ_{t+1} = 1 = lim θ_t`. Justified conclusions: non-strict
  (`eventually_integral_ratio_add_lt_add_of_le`), or strict under a uniform margin
  `𝔼[f_t] ≤ −c·𝔼[s_{t+1}]·s_t` (`eventually_integral_ratio_add_lt_of_gap`), or strict for all large
  `d` when the limits exist and are strictly ordered (`eventually_integral_ratio_add_lt_of_tendsto_lt`).
* **G4d — `lim θ_t`.** `θ_t` depends on the given (`d`-dependent) `x_t`; its limit need not exist.
  The Lean statements (i), (ii) above avoid it.

## Joint satisfiability of hypotheses

* WLLN / `tendsto_integral_ratio_paper` / `tendsto_integral_ratio_of_variance_bound`: the `example`
  after the latter instantiates all hypotheses (deterministic `X_n = 2(n+1)`, `Y_n = n+1`,
  `k_n = m_n = n+1`, `ρ = 1`, `a = 2`, `b = 1`) on an arbitrary family of probability spaces.
* Quantitative bounds: `abs_integral_ratio_sub_ratio_integral_le_sharp` is a genuinely random
  instance (with equality).
* CMT: any constant family `Y_n = y₀` and any bounded continuous `f`.
* Part 5: hypotheses hold e.g. for `ζ = 0` with `kap2 = 0`, and for Gaussian noise once
  `Prob/GaussianForms.lean` supplies moments (not instantiated here).

## Suggestions for downstream files

* To get `𝔼[θ_{t+1} | x_t] − thetaBarNext → 0`, use
  `Concentration.tendsto_integral_theta_sub_thetaBarNext`: supply `𝔼 s^S_{t+1} = EsNext` and
  `Var(s^S_{t+1})/(EsNext 𝒟 + EsNext ℬ)² → 0`. This requires `𝔼 s_{t+1}` to dominate the standard
  deviations; it is false in general otherwise (G3b).
* For strict statements "`𝔼θ_{t+1} < θ_t` for all large `d`" use
  `eventually_integral_ratio_add_lt_of_gap` together with `Concentration.ratio_sub_ratio_eq`; a
  uniform margin is unavoidable (G4c).
