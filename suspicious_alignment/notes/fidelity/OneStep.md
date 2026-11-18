# Fidelity note — `SuspiciousAlignment/OneStep.lean`

Module `SuspiciousAlignment.OneStep` (imports `Mathlib`, `SuspiciousAlignment.Defs`).
Paper: Deng et al., *Suspicious Alignment of SGD* (arXiv:2601.11789v2), Appendix A.2 (tex 910–947),
Appendix A.5 (tex 1061–1148), main-text definition of `η*_t` (tex 386–397), and the display that
links `𝔼[θ_{t+1}]` to `𝔼[f_t]` (tex 1038–1058).

Layer: **exact finite-`d` core** only. Every statement is an identity/inequality between finite
sums and holds for every finite index type `ι`, every spectrum `P : Spec ι`, every noise profile
`N : Noise ι`, every state `c`, every step size `η : ℝ` and every realised noise `ζ`.
The conditional expectations `𝔼[s^S_{t+1} | x_t]` and `𝔼[f_t(η) | x_t]` appear as the explicit finite
sums `Spec.EsNext` (from `Defs.lean`) and `Spec.expF` (new, defined here as required by the task).

Status: 0 `sorry`, 0 axioms beyond `propext`, `Classical.choice`, `Quot.sound` (checked with
`#print axioms` on all 131 declarations); `lake build SuspiciousAlignment.OneStep` succeeds with no
warnings from this file.

New shared definition introduced here (not in `Defs.lean`):

```lean
def Spec.expF (P : Spec ι) (N : Noise ι) (η : ℝ) (c : ι → ℝ) : ℝ :=
  P.sB c * P.EsNext N P.D η c - P.EsNext N P.B η c * P.sD c
```

Namespaces: one-step statements are in `SuspiciousAlignment.Spec` (dot notation `P.…`); generic
helpers (facts about `mom`/`theta` of an arbitrary state, real-variable lemmas, the concrete example)
are in `SuspiciousAlignment.OneStep` and take `P` as an explicit first argument.

## Table

| Paper item (tex lines) | Lean declaration | Status | Explanation |
|---|---|---|---|
| A.2 coordinate update `c_{i,t+1} = c_i − η(λ_i c_i + ζ_i) = (1−ηλ_i)c_i − ηζ_i` (913–917) | `Spec.cNext` (Defs), `Spec.cNext_eq` | exact | Second form is the definition, first form is the lemma. |
| eq. (10), first equality: `θ_{t+1}` as a ratio of sums (919–921) | `Spec.theta_cNext_eq_sum_div_sum` | exact | Both sides use the same `0/0 = 0` convention, no hypothesis needed. |
| eq. (10), second equality `θ_{t+1} = 1/(1 + s^ℬ_{t+1}/s^𝒟_{t+1})` (922) | `Spec.theta_cNext_eq_one_div` (general state: `OneStep.theta_eq_one_div`) | hypotheses-added | Needs `s^𝒟_{t+1} ≠ 0` (the paper says so in the following Remark). `OneStep.theta_eq_zero_and_one_div_eq_one` shows the hypothesis is necessary in Lean. |
| Remark in A.2: exceptional sets `{s^𝒟_{t+1} = 0}`, the affine set `𝒱` (928–934) | `Spec.sD_cNext_eq_zero_iff`, `Spec.mom_cNext_eq_zero_iff` | equivalent-reformulation (algebraic part); measure-zero claim not-formalized here | We prove `s^S_{t+1} = 0 ↔ ∀ i ∈ S, η ζ_i = (1−ηλ_i) c_i`, i.e. the description of `𝒱`. The "zero measure" statement belongs to the probability layer; see gap G4. |
| eq. (12) `f_t(η) = s^ℬ_t s^𝒟_{t+1} − s^ℬ_{t+1} s^𝒟_t` (936–939) | `Spec.fCompare` (Defs) | exact | Definition. |
| `θ_{t+1} − θ_t = f_t / (s_t s_{t+1})` (implicit) | `Spec.theta_cNext_sub_theta` (general: `OneStep.theta_sub_theta`) | extra | Hypotheses `s_t ≠ 0`, `s_{t+1} ≠ 0`. |
| `θ_{t+1} > θ_t ⟺ f_t(η) > 0` (941–944) | `Spec.theta_lt_theta_cNext_iff` | hypotheses-added | Needs `s_t > 0` and `s_{t+1} > 0`. Necessity: `Spec.exists_theta_lt_theta_cNext_and_fCompare_eq_zero`. Direction `⇐` holds unconditionally: `Spec.theta_lt_theta_cNext_of_fCompare_pos`. |
| `θ_{t+1} < θ_t ⟺ f_t(η) < 0` (941–944) | `Spec.theta_cNext_lt_theta_iff` | hypotheses-added | Same hypotheses. Necessity: `Spec.exists_theta_cNext_lt_theta_and_fCompare_eq_zero`. Direction `⇐` unconditional: `Spec.theta_cNext_lt_theta_of_fCompare_neg`. |
| (`θ_{t+1} = θ_t ⟺ f_t = 0`) | `Spec.theta_cNext_eq_theta_iff` | extra | Same hypotheses. |
| Lemma "Elementwise expectation", per-coordinate identity (1062–1066) | `Spec.EsNext_singleton`, `Spec.EsNext_eq_sum_singleton`; pathwise expansion `Spec.lam_sq_mul_cNext_sq`; abstract-expectation form `Spec.expect_mom_two_cNext` | equivalent-reformulation | `𝔼[λ_i² c_{i,t+1}² | x_t]` is `EsNext N {i} η c`. The pathwise expansion (with the cross term `−2η λ_i²(1−ηλ_i)c_iζ_i` and `η²λ_i²ζ_i²`) is the step the paper's proof takes before using `𝔼ζ_i = 0`, `𝔼ζ_i² = κ_i²`. `expect_mom_two_cNext` proves the lemma for *any* normalised linear functional `E` with `E ζ_i = 0`, `E ζ_i² = κ_i²`. The measure-theoretic version is in the probability layer. |
| Last display of the proof (1090–1093): `𝔼[s^S_{t+1}] = ∑_S λ²c² − 2η∑_S λ³c² + η²(∑_S λ⁴c² + ∑_S λ²κ²)` | `Spec.EsNext_eq` (per-coordinate regrouping: `Spec.EsNext_term_eq`) | exact | For every block `S`. |
| eq. (Eat) (1069) | `Spec.EsNext_D` | exact | With `s^𝒟 = P.sD c`, `∑_𝒟 λ³c² = P.tauD c`, `e_𝒟 = P.eD N`. |
| eq. (Ebt) (1070) | `Spec.EsNext_B` | exact | Same for `ℬ`. |
| Decomposition `s^S_{t+1} = χ_S + g_Sᵀz + zᵀD_S z` (1011–1021, used again in A.5) | `Spec.mom_two_cNext`, `Spec.mom_two_cNext_sub_EsNext` | exact / extra | The second lemma is the centred form `s^S_{t+1} − 𝔼[s^S_{t+1}] = −2η∑λ²(1−ηλ)cζ + η²∑λ²(ζ²−κ²)`, the bridge for the probability layer. |
| Lemma "Quadratic form", eq. (quad-form) `𝔼[f_t(η) | x_t] = p_t η² + q_t η` (1098–1102, proof 1110–1122) | `Spec.expF`, `Spec.expF_eq`, `Spec.expF_eq_mul`; `Spec.fCompare_sub_expF`; `Spec.expect_fCompare` | exact (algebraic form) | `expF` is the first line of the paper's proof. `expect_fCompare` shows `E[f_t] = expF` for any abstract expectation with the two moment properties, so the name is justified. |
| eq. (q-sign), first inequality `q_t ≤ 2 s^ℬ s^𝒟 (λ_{k+1} − λ_k)` (1105) | `Spec.qCoef_le` | exact | Uses `OneStep.tauB_le` (`∑_ℬ λ³c² ≤ λ_{k+1} s^ℬ`) and `OneStep.le_tauD` (`λ_k s^𝒟 ≤ ∑_𝒟 λ³c²`), the two bounds of line 1123. |
| eq. (q-sign), strict inequality `q_t < 0` (1105, 1123) | `Spec.qCoef_neg` | hypotheses-added | Needs `s^𝒟 > 0` and `s^ℬ > 0`. |
| `q_t < 0` unconditionally (as literally stated) | `Spec.qCoef_neg_iff`, `Spec.qCoef_neg_iff_theta`, `Spec.qCoef_eq_zero_iff`, `Spec.qCoef_eq_zero_iff_theta`, `Spec.qCoef_nonpos`; counterexamples `Spec.exists_theta_eq_one_qCoef_eq_zero`, `Spec.exists_theta_eq_zero_qCoef_eq_zero` | paper-claim-false | Exact statement: `q_t ≤ 0` always; `q_t < 0 ⟺ (s^𝒟 > 0 ∧ s^ℬ > 0) ⟺ 0 < θ_t < 1`; `q_t = 0 ⟺ θ_t ∈ {0, 1}`. See G1. |
| eq. (p-def) (1106) | `Spec.pCoef` (Defs); `Spec.pCoef_of_sD_eq_zero`, `Spec.pCoef_of_sB_eq_zero` | exact / extra | Values of `p_t` in the degenerate cases: `p_t = s^ℬ e_𝒟` if `θ_t = 0`, `p_t = −s^𝒟 e_ℬ` if `s^ℬ = 0`. |
| "If `p_t ≠ 0` … the non-zero root `η*_t := −q_t/p_t`" (1108); main-text eq. (2) (388–395) | `Spec.etaStar` (Defs), `Spec.etaStar_eq`, `Spec.expF_etaStar`, `Spec.expF_eq_zero_iff`, `Spec.etaStar_eq_zero_iff` | exact, except "non-zero" is hypotheses-added | For `p_t ≠ 0` the roots are exactly `0` and `η*_t`; `η*_t ≠ 0 ⟺ q_t ≠ 0 ⟺ 0 < θ_t < 1`. See G2. |
| Remark: parabola through the origin (1126) | `Spec.expF_zero` | exact | |
| Remark, `p_t > 0`: `η*_t > 0` (1145) | `Spec.etaStar_pos`, `Spec.etaStar_pos_iff`, `Spec.etaStar_nonneg` | hypotheses-added | Needs `q_t < 0`; in general only `η*_t ≥ 0`, and `η*_t > 0 ⟺ 0 < θ_t < 1`. Counterexample to the unconditional claim: `Spec.exists_pCoef_pos_and_etaStar_eq_zero`. |
| Remark, `p_t > 0`: `𝔼f < 0` for `0 < η < η*_t`, `𝔼f > 0` for `η > η*_t` (1145) | `Spec.expF_neg_iff_lt_etaStar`, `Spec.expF_eq_zero_iff_eq_etaStar`, `Spec.expF_pos_iff_etaStar_lt` | strengthened | Stated as equivalences for `η > 0`, `p_t > 0` (no assumption on `q_t`). |
| Remark, `p_t < 0`: `𝔼f < 0` for all `η > 0` (1147) | `Spec.expF_neg_of_pCoef_neg`; with `p_t ≤ 0`, `q_t < 0`: `Spec.expF_neg_of_pCoef_nonpos`; `Spec.expF_nonpos_of_pCoef_nonpos` | exact / strengthened | For `p_t < 0` only `q_t ≤ 0` is needed, so this half of the Remark is true even at `θ_t ∈ {0,1}`. The paper's missing case `p_t = 0` is covered by the `≤ 0` version (given `q_t < 0`). |
| (complete sign description for `η > 0`) | `Spec.expF_pos_iff`, `Spec.expF_neg_iff`, `Spec.expF_neg_iff_linear`, `Spec.expF_pos_iff_linear` | extra | `𝔼f > 0 ⟺ p_t > 0 ∧ η > η*_t`; `𝔼f < 0 ⟺ (p_t > 0 ∧ η < η*_t) ∨ (p_t ≤ 0 ∧ (p_t < 0 ∨ q_t < 0))`; division-free: sign of `p_t η + q_t`. |
| Positivity of `𝔼[s^S_{t+1} | x_t]` (implicit; "`y_0 ∈ (0,∞)`" at 1027) | `Spec.EsNext_nonneg`, `Spec.EsNext_eq_zero_iff`, `Spec.EsNext_pos_iff`, `Spec.EsNext_pos_of_kap2_pos`, `Spec.EsNext_pos_of_smin_pos`, `Spec.EsNext_pos_of_state`, `Spec.EsNext_D_add_EsNext_B`, `Spec.EsNext_D_add_EsNext_B_pos_iff`, `Spec.EsNext_D_add_EsNext_B_pos_of_smin_pos`, `Spec.EsNext_zero` | extra | `EsNext ≥ 0`; `EsNext S = 0 ⟺ ∀ i ∈ S, (1−ηλ_i)c_i = 0 ∧ η κ_i² = 0`. In particular `𝔼[s_{t+1}] > 0` whenever `η ≠ 0` and `s_min > 0`, or some `c_i ≠ 0` with `ηλ_i ≠ 1`. |
| Display 1040–1048: `lim 𝔼[θ_{t+1}] < θ_t ⟹ 𝔼[f_t] < 0` (deterministic equivalent) | `Spec.thetaBarNext_sub_theta`, `Spec.thetaBarNext_lt_theta_iff`, `Spec.theta_lt_thetaBarNext_iff`, `Spec.thetaBarNext_eq_theta_iff`, `Spec.thetaBarNext_lt_theta_of_expF_neg`, `Spec.theta_lt_thetaBarNext_of_expF_pos`, `Spec.thetaBarNext_eq_one_div`, `Spec.thetaBarNext_nonneg`, `Spec.thetaBarNext_le_one`, `Spec.thetaBarNext_zero` | strengthened (finite `d`, equivalence) | Exact identity `thetaBarNext − θ_t = expF / (s_t (𝔼s^𝒟_{t+1} + 𝔼s^ℬ_{t+1}))` for `s_t ≠ 0`, `𝔼s_{t+1} ≠ 0`; hence the three equivalences under `s_t > 0`, `𝔼s_{t+1} > 0`. The implications `expF < 0 ⟹ thetaBarNext < θ_t` and `expF > 0 ⟹ θ_t < thetaBarNext` need **no** positivity hypothesis. Necessity of the two hypotheses for the equivalences: `Spec.theta_zero_lt_thetaBarNext_and_expF_eq_zero`, `Spec.exists_thetaBarNext_lt_theta_and_expF_eq_zero`. |
| Finite-`d` deterministic-equivalent cores of the step-size theorems | `Spec.thetaBarNext_lt_theta_of_lt_etaStar`, `Spec.theta_lt_thetaBarNext_of_etaStar_lt`, `Spec.thetaBarNext_lt_theta_of_pCoef_nonpos` | extra | `p_t > 0`, `0 < η < η*_t ⟹ thetaBarNext < θ_t`; `p_t > 0`, `η > η*_t ⟹ θ_t < thetaBarNext`; `p_t ≤ 0`, `0 < θ_t < 1`, `η > 0 ⟹ thetaBarNext < θ_t`. No other hypotheses. |
| Moment bounds (line 1123 and analogues needed downstream) | `OneStep.mom_add_le`, `OneStep.le_mom_add`, `OneStep.tauB_le`, `OneStep.le_tauB`, `OneStep.tauD_le`, `OneStep.le_tauD`, `OneStep.mom_four_B_le`, `OneStep.le_mom_four_B`, `OneStep.mom_four_D_le`, `OneStep.le_mom_four_D` | extra | `a^j ∑_S λ^p c² ≤ ∑_S λ^{p+j} c² ≤ b^j ∑_S λ^p c²` when `a ≤ λ_i ≤ b` on `S`. |
| Facts on `θ` of an arbitrary state | `OneStep.theta_pos_iff`, `OneStep.theta_eq_zero_iff`, `OneStep.theta_eq_one_iff`, `OneStep.theta_mem_Ioo_iff`, `OneStep.theta_eq_zero_or_eq_one_iff`, `OneStep.theta_lt_theta_iff`, `OneStep.theta_gt_theta_iff`, `OneStep.theta_eq_theta_iff`, `OneStep.theta_lt_theta_of_pos`, `OneStep.theta_gt_theta_of_neg`, `OneStep.mom_eq_zero_iff`, `OneStep.mom_pos_iff` | extra | Reusable for the projected updates (`cNextProj`) as well: the comparison lemmas are stated for two arbitrary states `c`, `c'`. |
| Zero-measure of the exceptional sets, integrability of `θ_{t+1}` (928–934); "implying `𝔼[θ_{t+1}]` decreases/increases" (1145–1147) | — | not-formalized (other layers) | Probability and asymptotic layers. |

## Non-vacuity

* Concrete instance in the file (`OneStep.exSpec`, `OneStep.exNoise`, `OneStep.exNoiseB`): `λ = (2, 1)`,
  `𝒟 = {0}`, `x_t = (1, 1)` (`θ_t = 4/5`). With `κ² = (1, 1)`: `q_t = −8`, `p_t = 12`, `η*_t = 2/3`
  (`exSpec_qCoef`, `exSpec_pCoef`, `exSpec_etaStar`); with `κ² = (0, 10)`: `p_t = −28`
  (`exSpec_pCoef_B`). Three `example`s instantiate the decrease regime (`η = 1/2`), the increase
  regime (`η = 1`), and the `p_t ≤ 0` regime.
* The hypotheses of `expect_mom_two_cNext` / `expect_fCompare` are satisfiable for every `P`, `N`:
  `OneStep.boolE` (Rademacher average on `Bool`) with `ζ_i = ±√κ_i²` (`example` at the end).
* The pathwise equivalences need `s_t > 0 ∧ s_{t+1} > 0`: satisfied e.g. by any `c ≠ 0`, `η = 0`.
* A numerical cross-check (Monte-Carlo with a full, non-diagonal `Σ`; `d = 7`, `k = 3`, 4·10⁵ samples)
  of `𝔼[f_t] = p_tη² + q_tη`, of the pathwise equivalences, and of the bridge identity was run with
  numpy and agrees.

## Gaps / errors found in the paper

**G1 — `q_t < 0` is not unconditional (eq. (q-sign), tex 1105 and 1123).**
The paper derives `q_t ≤ 2 s^ℬ_t s^𝒟_t (λ_{k+1} − λ_k)` (correct) and concludes "which makes `q_t` strictly
negative since `λ_k > λ_{k+1}`". This needs `s^ℬ_t s^𝒟_t > 0`. If `s^𝒟_t = 0` then also
`∑_𝒟 λ³c² = 0`, so `q_t = 2(0·τ^ℬ − s^ℬ·0) = 0`; symmetrically if `s^ℬ_t = 0`. Exact statement
(`Spec.qCoef_neg_iff_theta`, `Spec.qCoef_eq_zero_iff_theta`):
`q_t < 0 ⟺ 0 < θ_t < 1` and `q_t = 0 ⟺ θ_t ∈ {0, 1}` (the case `x_t = 0` is `θ_t = 0`).
Concrete counterexamples valid for **every** spectrum: `x_t = u_1` (`θ_t = 1`, `q_t = 0`) and
`x_t = u_{k+1}` (`θ_t = 0`, `q_t = 0`) — `Spec.exists_theta_eq_one_qCoef_eq_zero`,
`Spec.exists_theta_eq_zero_qCoef_eq_zero`. Numerically: `λ = (2,1)`, `x_t = (1,0)` gives `q_t = 0`.

**G2 — "there exists a positive critical step size `η*_t > 0`" (Remark, tex 1145) and "the non-zero
root" (tex 1108) fail at `θ_t = 0`.**
At `θ_t = 0` (`s^𝒟_t = 0`, `x_t ≠ 0`) one has `p_t = s^ℬ_t e_𝒟`, which is `> 0` as soon as the dominant
block carries noise, while `q_t = 0`; so `η*_t = 0`, the parabola is `p_t η²`, and
`𝔼[f_t(η) | x_t] > 0` for **every** `η ≠ 0` (`Spec.exists_pCoef_pos_and_etaStar_eq_zero`). Consequences
for downstream statements: the decrease condition `0 < η < η*_t` is vacuous there (no contradiction),
and the increase condition `η > η*_t` reads `η > 0`. The `p_t < 0` half of the Remark is unaffected:
it only needs `q_t ≤ 0` (`Spec.expF_neg_of_pCoef_neg`). Example at `θ_t = 1`: `p_t = −s^𝒟_t e_ℬ ≤ 0`,
`q_t = 0`.

**G3 — the Remark omits `p_t = 0`.** Then `𝔼[f_t(η)] = q_t η`, negative for all `η > 0` iff `q_t < 0`
(covered by `Spec.expF_neg_of_pCoef_nonpos`), and identically `0` if also `q_t = 0`
(e.g. `θ_t = 1` and `e_ℬ = 0`, where the bulk coordinates stay `0` almost surely and `θ ≡ 1`).
The sentence "the behavior for any positive step size is entirely determined by the sign of `p_t`"
is therefore slightly too strong: for `p_t ≤ 0` the strictness depends on `(p_t, q_t) ≠ (0, 0)`
(`Spec.expF_neg_iff`).

**G4 — the pathwise equivalences `θ_{t+1} ≷ θ_t ⟺ f_t(η) ≷ 0` (tex 941–944) need `x_t ≠ 0` and
`x_{t+1} ≠ 0`; the "zero-measure" justification (tex 928–934) needs non-degenerate noise.**
* If `x_t = 0` then `f_t ≡ 0` but `θ_{t+1} > 0 = θ_t` for generic noise
  (`Spec.exists_theta_lt_theta_cNext_and_fCompare_eq_zero`). If `x_{t+1} = 0` (e.g. `x_t = u_1`,
  `η = 1/λ_1`, `ξ_t = 0`) then `f_t = 0` but `θ_{t+1} = 0 < 1 = θ_t`
  (`Spec.exists_theta_cNext_lt_theta_and_fCompare_eq_zero`). With `s_t > 0`, `s_{t+1} > 0` the
  equivalences are exact (`θ_{t+1} − θ_t = f_t/(s_t s_{t+1})`); the implications
  `f_t > 0 ⟹ θ_{t+1} > θ_t` and `f_t < 0 ⟹ θ_{t+1} < θ_t` hold with no hypothesis.
* The Remark argues that `𝒱 = {ξ : s^𝒟_{t+1}(ξ) = 0}` is a null set "by Sard's theorem" because it is
  a "(d−k)-dim hyperplane". Algebraically `𝒱 = {ζ_i = (1−ηλ_i)c_i/η ∀ i ∈ 𝒟}` (for `η ≠ 0`;
  `Spec.sD_cNext_eq_zero_iff`), an affine subspace of dimension `d − k` (not a hyperplane unless
  `k = 1`). It is Lebesgue-null (no Sard needed), but that only gives probability `0` under
  `ξ ~ 𝒩(0, Σ)` when the law of `(ζ_i)_{i∈𝒟}` does not charge the point, and the standing assumption
  only asks `Tr(Σ) ∈ (0, ∞)`. A Gaussian vector hits a fixed point with positive probability iff
  its covariance is `0` and the point is its mean, so `ℙ(s^𝒟_{t+1} = 0) > 0` iff `κ_i² = 0` and
  `(1 − ηλ_i) c_i = 0` for all `i ∈ 𝒟` (for `η ≠ 0`) — by `Spec.EsNext_eq_zero_iff` this is exactly
  `𝔼[s^𝒟_{t+1} | x_t] = 0`. Hence the correct hypothesis for the Remark is
  `0 < P.EsNext N P.D η c` (implied by `η ≠ 0 ∧ s_min > 0`, `Spec.EsNext_pos_of_smin_pos`).
  Counter-scenario allowed by the paper's assumptions: noise supported in the bulk directions and
  `θ_t = 0`; then `s^𝒟_{t+1} = 0` surely, `θ_{t+1} = 0`, and the second form of eq. (10) is
  undefined. The integrals `∫ θ_{t+1} dξ` are also written without the Gaussian density. (The
  measure-zero statement itself is not formalized here — probability layer.)

**G5 — the bridge display (tex 1040–1048).** (i) Typo: `θ_t` is written as
`1 / (1 − (1/ρ) (…)/(…))`; the sign must be `+`. (ii) The display states only the implication
"`lim 𝔼θ_{t+1} < θ_t ⟹ 𝔼 f_t < 0`", whereas the theorems use the converse direction
(`𝔼 f_t < 0 ⟹` decrease). At finite `d` both directions hold for the deterministic equivalent:
`thetaBarNext − θ_t = 𝔼[f_t]/(s_t 𝔼[s_{t+1}])` (`Spec.thetaBarNext_sub_theta`), and the direction
actually needed is unconditional (`Spec.thetaBarNext_lt_theta_of_expF_neg`,
`Spec.theta_lt_thetaBarNext_of_expF_pos`). (iii) The equivalence itself requires `x_t ≠ 0` and
`𝔼[s_{t+1}] > 0`; both can fail (`Spec.theta_zero_lt_thetaBarNext_and_expF_eq_zero`,
`Spec.exists_thetaBarNext_lt_theta_and_expF_eq_zero`).

**G6 — remarks (no error).** Lemma "Elementwise expectation" uses only `𝔼ζ_i = 0` and
`𝔼ζ_i² = κ_i²`: neither Gaussianity nor diagonality of `Σ` in the eigenbasis is needed
(`Spec.expect_mom_two_cNext`, `Spec.expect_fCompare` are stated for an arbitrary normalised linear
functional). The lemma "Quadratic form" holds for every real `η` (including `η ≤ 0`), every state
(including `x_t = 0`, where `p_t = q_t = 0`) and every finite `d`.

## Suggestions for downstream files

* Probability layer: from `Spec.mom_two_cNext_sub_EsNext` and `Spec.fCompare_sub_expF`,
  `∫ s^S_{t+1} = EsNext` and `∫ f_t = expF` follow by linearity of the integral once `ζ_i`, `ζ_i²` are
  integrable with `∫ζ_i = 0`, `∫ζ_i² = κ_i²`.
* Theorems 2–4: reduce to the sign of `P.expF N η c` via `Spec.expF_neg_iff_lt_etaStar`,
  `Spec.expF_pos_iff_etaStar_lt`, or the division-free `Spec.expF_neg_iff_linear` /
  `Spec.expF_pos_iff_linear`; then use `Spec.thetaBarNext_lt_theta_of_expF_neg` /
  `Spec.theta_lt_thetaBarNext_of_expF_pos` (no positivity side conditions). For bounds on `p_t`, the
  moment inequalities `OneStep.mom_four_*`, `OneStep.tau*` are available.
* Any theorem that invokes "`q_t < 0`" or "`η*_t > 0`" must carry `0 < θ_t < 1`
  (equivalently `0 < P.sD c ∧ 0 < P.sB c`), cf. G1–G2.
