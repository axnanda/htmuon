# Fidelity note — `SuspiciousAlignment/Projected/LossThreshold.lean`

Module `SuspiciousAlignment.Projected.LossThreshold` (imports `Mathlib`, `SuspiciousAlignment.Defs` only).
Paper: Deng et al., *Suspicious Alignment of SGD* (arXiv:2601.11789v2), Section 5 up to and including
Theorem 11 (tex 530–583, Summary 602–627) and Appendix A.5 (tex 1467–1728).
Layer: **exact finite-`d` algebra** (no probability space, no `d → ∞`).

Status of the file: compiles, `lake build SuspiciousAlignment.Projected.LossThreshold` succeeds, no
`sorry`/`admit`/`axiom`/`native_decide`; `#print axioms` on all 140 declarations gives only
`propext`, `Classical.choice`, `Quot.sound`. Nothing is left unproven.

Notation: `s^S = P.mom S 2 c`, `τ^S = P.mom S 3 c`, `n^loss_S = P.nLoss N S`,
`η^loss_S = P.etaLoss N S c`, `𝔼ΔL = P.expLossChange N S η c`, `θ_t = P.theta c`,
`α_t = P.alphaT c`, `β_t = P.betaT N c`, `γ_t = P.gammaT N`, `h = P.hQuad N c`,
`θ^crit_t = P.thetaCrit N c`. Main results are in `namespace SuspiciousAlignment.Spec`; generic
helpers in `namespace SuspiciousAlignment.LossThreshold`.

## 1. Table: paper item → Lean declaration

| Paper item (tex lines) | Lean declaration | Status | Explanation |
|---|---|---|---|
| Eq. (3)–(4) DSGD / BSGD update (539–542) | `Spec.cNextProj` (Defs) | exact | coordinates in `S` move as in SGD, others frozen |
| Proof of Thm 10, `ΔL = -η gᵀAx + (η²/2) gᵀAg` (1492–1495) | `Spec.loss_cNextProj_sub_loss` | exact | pathwise, for every noise realisation `ζ`; `g_i = λ_i c_i + ζ_i` on `S` |
| same, coordinatewise | `Spec.loss_cNextProj_sub_loss_eq_sum` | equivalent-reformulation | `ΔL = ∑_{i∈S} (λ_i/2)(c_{i,t+1}² − c_{i,t}²)` |
| Proof of Thm 10, `𝔼[ΔL∣x_t] = −η s^S + (η²/2)(τ^S + n^loss_S)` (1496–1498) | `Spec.loss_cNextProj_sub_loss_eq_expLossChange_add` | equivalent-reformulation | pathwise decomposition `ΔL = expLossChange − η∑_S λ_i(1−ηλ_i)c_iζ_i + (η²/2)∑_S λ_i(ζ_i² − κ_i²)`; the two extra terms have mean 0 when `𝔼ζ_i = 0`, `𝔼ζ_i² = κ_i²` (the integral itself belongs to the probability layer) |
| same | `Spec.expLossChange_eq_sum` | exact (algebra) | `expLossChange = ∑_{i∈S} (λ_i/2)((1−ηλ_i)²c_i² + η²κ_i² − c_i²)`, the sum of the per-coordinate expected changes |
| same | `Spec.weighted_sum_loss_change` | extra | the expectation identity for finitely supported noise (weights `w ω`, `∑w = 1`, mean 0, second moments `κ_i²` on `S`) |
| **Theorem 10** (554–565): `𝔼ΔL < 0 ⟺ 0 < η < η^loss_S` | `Spec.expLossChange_neg_iff`, `Spec.proj_loss_step_size_condition` (𝒟 and ℬ together) | hypotheses-added | hypothesis `0 < τ^S + n^loss_S` (denominator of the threshold). `η ∈ ℝ` arbitrary; `0 < η` is part of the iff. `s^S > 0` is **not** needed |
| Thm 10, for `η > 0` | `Spec.expLossChange_neg_iff_of_pos` | hypotheses-added | `𝔼ΔL < 0 ⟺ η < η^loss_S` |
| Thm 10, increasing side (used in the Summary, 619–626) | `Spec.expLossChange_pos_iff`, `Spec.expLossChange_pos_iff_of_pos` | extra / hypotheses-added | `𝔼ΔL > 0 ⟺ η < 0 ∨ η > η^loss_S`; for `η > 0`: `⟺ η > η^loss_S` |
| Thm 10, zero set, factorisation | `Spec.expLossChange_eq_zero_iff`, `Spec.expLossChange_eq_factor` | extra | `𝔼ΔL = ((τ^S+n^loss_S)/2)·η·(η − η^loss_S)` |
| Thm 10, degenerate cases | `Spec.expLossChange_eq_zero_of_lossDen_eq_zero`, `Spec.expLossChange_nonneg_of_mom_eq_zero`, `Spec.etaLoss_eq_zero_of_lossDen_eq_zero` | extra | see §2.1 |
| "Additional Notion" `α_t, β_t, γ_t` (1504–1512) | `Spec.alphaT`, `Spec.betaT`, `Spec.gammaT` (Defs) | exact | `γ_t` does not depend on `x_t` (the paper says all three do) |
| Lemma `crossover-quadratic-properties`, item 1: `∀x_t, α_t > 0` (1518, 1530–1550) | `Spec.alphaT_pos`; quantitative: `Spec.gap_mul_s_le_alphaT` (`α_t ≥ s_t(λ_k − λ_{k+1})`), `Spec.alphaT_le` (`α_t ≤ s_t(λ_1 − λ_d)`) | hypotheses-added | needs `s^𝒟 > 0` and `s^ℬ > 0` (⟺ `0 < θ_t < 1`); literal "∀ x_t" is false: `Spec.alphaT_zero` (`α = 0` at `x_t = 0`) — see §2.2 |
| same, `μ^𝒟(3,2) ≥ λ_k`, `μ^ℬ(3,2) ≤ λ_{k+1}` (1538–1548) | `LossThreshold.lamk_le_mu_D`, `LossThreshold.mu_B_le_lamk1` (+ `mu_D_le_lam1`, `lamd_le_mu_B`) | hypotheses-added | need `s^𝒟 > 0`, resp. `s^ℬ > 0` |
| item 2: `∀x_t, γ_t < 0` (1519, 1552–1556) | `Spec.gammaT_neg`, `Spec.gammaT_neg_iff`, `Spec.gammaT_nonpos` | hypotheses-added | needs `n^loss_𝒟 > 0`; not implied by `Σ ⪰ 0, Tr Σ > 0` — see §2.3 |
| `h(0) = γ_t < 0`, `h(1) = α+β+γ = n^loss_ℬ > 0` (1521, 1558–1564) | `Spec.hQuad_zero`, `Spec.hQuad_one_eq_sum`, `Spec.hQuad_one`, `Spec.alphaT_add_betaT_add_gammaT` | exact (identities) / hypotheses-added (signs) | `h(1) > 0` needs `n^loss_ℬ > 0` |
| the whole lemma | `Spec.crossover_quadratic_properties` | hypotheses-added | hypotheses `s^𝒟, s^ℬ, n^loss_𝒟, n^loss_ℬ > 0` |
| Lemma `crossover-quadratic-critical-root` (1570–1581): `θ^crit ∈ (0,1)`, `h<0` on `(0,θ^crit)`, `h>0` on `(θ^crit,1)`, unique root in `(0,1)`, explicit formula | `Spec.crossover_critical_root`; pieces: `Spec.thetaCrit_eq` (formula, `rfl`), `Spec.hQuad_thetaCrit`, `Spec.thetaCrit_mem_Ioo`, `Spec.hQuad_neg_iff`, `Spec.hQuad_pos_iff`, `Spec.hQuad_eq_zero_iff`, `Spec.existsUnique_hQuad_root` | hypotheses-added (and strengthened) | same four hypotheses. Strengthening: for **every** `θ > 0`, `h(θ) < 0 ⟺ θ < θ^crit`, `h(θ) > 0 ⟺ θ > θ^crit`, `h(θ) = 0 ⟺ θ = θ^crit` (needs only `α_t > 0`) |
| — exact location of the root | `Spec.thetaCrit_nonneg`, `Spec.thetaCrit_le_one`, `Spec.thetaCrit_pos_iff` (`θ^crit > 0 ⟺ n^loss_𝒟 > 0 ∨ n^loss_ℬ < α_t`), `Spec.thetaCrit_lt_one_iff` (`θ^crit < 1 ⟺ n^loss_ℬ > 0`), `Spec.thetaCrit_eq_one`, `Spec.thetaCrit_eq_zero` | extra | shows the noise hypotheses are sharp |
| Proof of Thm 11, numerator identity (1699–1711) | `Spec.lossGap_eq_s_mul_hQuad` | hypotheses-added | `s^𝒟(τ^ℬ+n^loss_ℬ) − s^ℬ(τ^𝒟+n^loss_𝒟) = s_t·h(θ_t)`, for `s^𝒟, s^ℬ > 0` |
| Proof of Thm 11, `sign(η^loss_𝒟 − η^loss_ℬ) = sign h(θ_t)` (1689–1696, 1724–1726) | `Spec.etaLossD_sub_etaLossB`, `Spec.etaLossD_lt_etaLossB_iff_hQuad_neg`, `Spec.etaLossB_lt_etaLossD_iff_hQuad_pos`, `Spec.etaLossD_eq_etaLossB_iff_hQuad_eq_zero` | hypotheses-added | `s^𝒟, s^ℬ > 0` |
| **Theorem 11** (568–583): `θ_t < θ^crit ⟺ η^loss_𝒟 < η^loss_ℬ`, `θ_t > θ^crit ⟺ η^loss_𝒟 > η^loss_ℬ` | `Spec.theta_lt_thetaCrit_iff`, `Spec.thetaCrit_lt_theta_iff`, `Spec.theta_eq_thetaCrit_iff` (equality case) | hypotheses-added | need exactly `s^𝒟 > 0`, `s^ℬ > 0`; **no** noise hypothesis |
| Theorem 11, bundled (unique root in `(0,1)` = `θ^crit`, + the three equivalences) | `Spec.loss_crossover` | hypotheses-added | `0 < θ_t`, `θ_t < 1`, `n^loss_𝒟 > 0`, `n^loss_ℬ > 0` |
| Summary consequence (619–626): for `η ∈ (η^loss_𝒟, η^loss_ℬ)`: `𝔼ΔL_𝒟 > 0`, `𝔼ΔL_ℬ < 0` | `Spec.expLossChange_D_pos_B_neg`; `Spec.low_alignment_descent` (with Thm 11) | hypotheses-added | both denominators `τ^S + n^loss_S > 0`; the 𝒟-denominator is genuinely needed (§2.5) |
| mirror statement (high-alignment regime) | `Spec.expLossChange_B_pos_D_neg`, `Spec.high_alignment_descent` | extra | |
| "window non-empty ⟺ low-alignment regime" | `Spec.exists_D_pos_B_neg_iff` | extra | `∃ η>0, 𝔼ΔL_𝒟 > 0 ∧ 𝔼ΔL_ℬ < 0 ⟺ θ_t < θ^crit_t` |
| state-dependence of `θ^crit_t` | `Spec.thetaCrit_congr`, `LossThreshold.theta_smul`, `Spec.alphaT_smul`, `Spec.etaLossD_lt_etaLossB_iff`, `Spec.etaLossD_lt_etaLossB_smul_iff`, `Spec.nLossD_div_lt_thetaCrit`, `LossThreshold.state_dependence_example` | extra | see §2.4 |
| toolkit for Theorems 12–13 | `Spec.one_sub_thetaCrit_mul`, `Spec.one_sub_thetaCrit_mul_alphaT_le`, `Spec.nLossB_le_one_sub_thetaCrit_mul`, `Spec.gap_mul_s_le_alphaT` | extra | `(1−θ^crit)(αθ^crit + n_ℬ + n_𝒟) = n_ℬ`, hence `n_ℬ/(α+n_ℬ+n_𝒟) ≤ 1−θ^crit ≤ n_ℬ/α` |
| non-vacuity | `LossThreshold.loss_crossover_nonvacuous`, `LossThreshold.suspicious_window_example` | extra | `λ=(2,1)`, `κ²=(1,1)`, `c=(1,1)`: all hypotheses hold; `η^loss_𝒟 = 4/5 < 9/10 < 1 = η^loss_ℬ` |
| sharpness of noise hypotheses | `LossThreshold.thetaCrit_eq_zero_example`, `LossThreshold.thetaCrit_eq_one_example` | paper-claim-false (formal counterexamples to "`γ_t<0 ∀x_t`", "`θ^crit ∈ (0,1)`" under `Σ ⪰ 0`, `Tr Σ > 0`) | §2.3 |
| Theorem 12, Theorem 13 | — | not-formalized here | next file |

## 2. Gaps / errors found in the paper

### 2.1 Theorem 10: hypotheses
`𝔼ΔL = −η a + (η²/2) b` with `a = s^S ≥ 0`, `b = τ^S + n^loss_S ≥ 0`, and `a > 0 ⇒ b > 0`.

* `b > 0` (state **or** noise has a component in `S`; `LossThreshold.lossDen_pos_iff`): the iff
  `𝔼ΔL < 0 ⟺ 0 < η < 2a/b` holds for every real `η`; `η > 0` is a *consequence* of descent, not an
  assumption. This includes `a = s^S = 0`, `n^loss_S > 0` (e.g. `x_t ∈ ℬ`-subspace, `S = 𝒟`):
  then `η^loss_S = 0`, both sides are false and `𝔼ΔL = (η²/2) n^loss_S ≥ 0`
  (`Spec.expLossChange_nonneg_of_mom_eq_zero`).
* `b = 0` (state and noise both vanish on `S`): `𝔼ΔL ≡ 0` (`Spec.expLossChange_eq_zero_of_lossDen_eq_zero`)
  and the paper's threshold is the undefined expression `0/0`. The paper's iff is then meaningless;
  in Lean, `Spec.etaLoss` evaluates to `0` by `x/0 = 0` (`Spec.etaLoss_eq_zero_of_lossDen_eq_zero`),
  so the iff would hold "by convention" (both sides false). We do **not** state this as a theorem;
  `Spec.expLossChange_neg_iff` carries the hypothesis `0 < b`.
* The proof (1498) only says "setting this to be less than zero holds for `0 < η < …`", i.e. argues
  one direction; the converse is true and proved here.
* The restated theorem (1477) carries the wrong title ("Condition Differences on Different
  Alignment Regime").

### 2.2 `α_t > 0` "for all `x_t`" (Lemma, item 1) is false / undefined on the boundary
`α_t = s_t(μ^𝒟(3,2) − μ^ℬ(3,2))` with `μ^S(3,2) = τ^S/s^S`.
* `x_t = 0`: `α_t = 0` (`Spec.alphaT_zero`) — formal counterexample to the literal claim.
  The proof (1534) asserts "for any `x_t`, `s_t > 0`".
* `s^𝒟 = 0` (`θ_t = 0`) or `s^ℬ = 0` (`θ_t = 1`): `μ^𝒟(3,2)` resp. `μ^ℬ(3,2)` is `0/0`; the bounds
  `μ^𝒟(3,2) ≥ λ_k`, `μ^ℬ(3,2) ≤ λ_{k+1}` (1538–1545) are meaningless there. (With Lean's
  `0/0 = 0`: `s^𝒟 = 0 < s^ℬ` gives `α_t = −τ^ℬ < 0`.)
* Correct hypothesis: `s^𝒟 > 0 ∧ s^ℬ > 0`, equivalently `0 < θ_t < 1`
  (`LossThreshold.theta_mem_Ioo_iff`). Then even `α_t ≥ s_t(λ_k − λ_{k+1}) > 0`.
* Consequently the second lemma's "critical function `θ^crit : ℝ^d → (0,1)`" is only defined on
  `{x : 0 < θ(x) < 1}`, and the Summary's "low-alignment regime `[0, θ^crit)`" should read
  `(0, θ^crit)`.
* Typo (1544): `μ^ℬ(3,2) = ∑ λ_j·(λ_j³ c_j²)/…` should be `∑ λ_j·(λ_j² c_j²)/…`.

### 2.3 `γ_t < 0` and `h(1) > 0` "for all `x_t` and noise" are extra assumptions
The lemma asserts `n^loss_𝒟 = ∑_𝒟 λ_iκ_i² > 0` and `n^loss_ℬ > 0` for every noise (1556, 1564; the
sentence "γ_t is the negative product of two positive definite quantities" is not meaningful).
The paper only assumes `Σ ⪰ 0` and `Tr Σ ∈ (0,∞)`, which does **not** give either inequality
(they hold if `Σ ≻ 0`: `LossThreshold.nLossD_pos_of_smin_pos`, `nLossB_pos_of_smin_pos`).
Precisely, for `α_t > 0`:
* `θ^crit_t < 1 ⟺ n^loss_ℬ > 0` (`Spec.thetaCrit_lt_one_iff`); if `n^loss_ℬ = 0` then `θ^crit_t = 1`.
* `θ^crit_t > 0 ⟺ n^loss_𝒟 > 0 ∨ n^loss_ℬ < α_t` (`Spec.thetaCrit_pos_iff`).

Formal counterexamples (`λ = (2,1)`, `𝒟 = {0}`, `c = (1,1)`, so `θ_t = 4/5`, `α_t = 5`):
* `κ² = (0,5)` (`Σ = diag(0,5) ⪰ 0`, `Tr Σ = 5`): `γ_t = 0` and `θ^crit_t = 0 ∉ (0,1)`
  (`LossThreshold.thetaCrit_eq_zero_example`).
* `κ² = (1,0)`: `h(1) = 0` and `θ^crit_t = 1 ∉ (0,1)` (`LossThreshold.thetaCrit_eq_one_example`).

The **equivalences** of Theorem 11 survive without any noise hypothesis (only `θ^crit ∈ (0,1)` and
the "one positive / one negative root" discussion need them).

### 2.4 Theorem 11: the "iff" is correct for a fixed state; `θ^crit_t` is state-dependent
For a fixed state with `0 < θ_t < 1` the paper's two equivalences are correct as stated (and the
equality case holds too). But `θ^crit_t = θ^crit(x_t)` is a function of the state through `α_t`
(i.e. `s_t`, `μ^𝒟(3,2)`, `μ^ℬ(3,2)`; `Spec.thetaCrit_congr`), **not** a universal threshold on the
alignment:
* `θ` is scale invariant (`LossThreshold.theta_smul`) while `α` scales like `t²`
  (`Spec.alphaT_smul`) and `n^loss_S` do not scale. Along the ray `t ↦ t x_t`:
  `η^loss_𝒟(tx) < η^loss_ℬ(tx) ⟺ n_ℬθ − n_𝒟(1−θ) < t² α θ(1−θ)`
  (`Spec.etaLossD_lt_etaLossB_smul_iff`). So for `θ_t > n_𝒟/(n_𝒟+n_ℬ)` the ordering flips with the
  scale (large loss ⇒ "low-alignment" ordering). This is consistent with the paper's remark after
  Theorem 13 that the phenomenon needs the loss to be "pre-convergence".
* Formal instance (`LossThreshold.state_dependence_example`): `λ = (2,1)`, `κ² = (1,1)`;
  `c = (1,1)` and `c' = (1/2,1/2)` both have `θ = 4/5`, but `η^loss_𝒟(c) = 4/5 < 1 = η^loss_ℬ(c)`
  whereas `η^loss_ℬ(c') = 2/5 < 1/2 = η^loss_𝒟(c')`; hence `θ^crit(c') < 4/5 < θ^crit(c)`.
* State-independent information: `n_𝒟/(n_𝒟+n_ℬ) < θ^crit_t < 1` (`Spec.nLossD_div_lt_thetaCrit`,
  `Spec.thetaCrit_lt_one`).
* At `x_t = 0` the theorem is false under the natural reading (`θ(0) = 0`, `α = 0`,
  `h(θ) = (n_ℬ+n_𝒟)θ − n_𝒟` with root `n_𝒟/(n_𝒟+n_ℬ) ∈ (0,1)`, yet `η^loss_𝒟 = η^loss_ℬ = 0`);
  the proof (1706) indeed assumes `x_t ≠ 0`. At `θ_t ∈ {0,1}` the coefficients are `0/0`.
* Typos in the proof: (1690) `u_t^ℬ` should be `τ_t^ℬ`; (1694) the displayed sign identity reads
  `s^𝒟(u^ℬ + n_ℬ) − s^𝒟(u^𝒟 + n_𝒟)` and should be `s^𝒟(τ^ℬ + n_ℬ) − s^ℬ(τ^𝒟 + n_𝒟)`; (1709) the
  coefficient of `θ_t` is printed as `s_t(μ^𝒟−μ^ℬ) + n_ℬ + n_𝒟` and should be
  `−s_t(μ^𝒟−μ^ℬ) + n_ℬ + n_𝒟 (= β_t)`. The final definitions of `α, β, γ` are correct, and the
  identity `numerator = s_t·h(θ_t)` is verified (`Spec.lossGap_eq_s_mul_hQuad`).

### 2.5 Summary consequence
For `η ∈ (η^loss_𝒟, η^loss_ℬ)`: `𝔼ΔL_𝒟 > 0` needs `τ^𝒟 + n^loss_𝒟 > 0`. If `s^𝒟 = 0` and
`n^loss_𝒟 = 0`, then `𝔼ΔL_𝒟 ≡ 0` (not `> 0`) although every `η ∈ (0, η^loss_ℬ)` lies in the
(conventional) window. With `0 < θ_t < 1` both denominators are automatically positive
(`Spec.low_alignment_descent`).

## 3. Non-vacuity
All hypotheses are jointly satisfiable: `LossThreshold.loss_crossover_nonvacuous`
(`λ=(2,1)`, `κ²=(1,1)`, `c=(1,1)`: `0<θ<1`, `n^loss_𝒟 = 2 > 0`, `n^loss_ℬ = 1 > 0`), and
`LossThreshold.suspicious_window_example` exhibits a concrete step size (`η = 9/10`) with
`𝔼ΔL_𝒟 > 0 > 𝔼ΔL_ℬ`. No theorem uses `x/0 = 0`: every division occurring in a statement has a
denominator made positive by the hypotheses (`s^𝒟, s^ℬ, s_t, τ^S + n^loss_S, α_t`).

## 4. Heads-up for the next file (Theorems 12–13; not formalized here)
* Tools: `Spec.gap_mul_s_le_alphaT` (`α_t ≥ s_t λ_{k+1}(m−1)`), `Spec.alphaT_le`,
  `Spec.one_sub_thetaCrit_mul`, `Spec.one_sub_thetaCrit_mul_alphaT_le`
  (`(1−θ^crit) α_t ≤ n_ℬ`), `Spec.nLossB_le_one_sub_thetaCrit_mul`
  (`n_ℬ ≤ (1−θ^crit)(α_t + n_ℬ + n_𝒟)`), `Spec.thetaCrit_mem_Ioo`.
* The **upper** bound of Theorem 13, `1−θ^crit ≤ n_ℬ/(s_tλ_{k+1}(m−1))`, follows from the above.
* The **lower** bound of Theorem 13, `n_ℬ/(s_tλ_{k+1}(m−1) + n_ℬ + n_𝒟) ≤ 1−θ^crit`, appears to be
  false in general (it would need `α_t ≤ s_tλ_{k+1}(m−1)`, whereas `α_t ≥ s_tλ_{k+1}(m−1)`).
  Numerical counterexample (python, not formalized): `λ = (10,2,1)`, `𝒟 = {1,2}`, `c = (1,0,1)`,
  `κ² = (1,1,1)`: `α_t = 909`, `s_tλ_{k+1}(m−1) = 101`, `1−θ^crit ≈ 0.001086`, paper's lower bound
  `= 1/114 ≈ 0.00877`. The correct lower bound is `n_ℬ/(α_t + n_ℬ + n_𝒟)`
  (e.g. `≥ n_ℬ/(s_t(λ_1−λ_d) + n_ℬ + n_𝒟)`).
