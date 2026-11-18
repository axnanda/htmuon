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

Status (after fix round 1): 0 `sorry`, 0 axioms beyond `propext`, `Classical.choice`, `Quot.sound`
(checked with `#print axioms` on all 163 named declarations: 156 theorems, 7 definitions; plus 4
anonymous `example`s); `scripts/leancheck SuspiciousAlignment/OneStep.lean` prints nothing (no
errors, no warnings) and `scripts/leancheck --build SuspiciousAlignment.OneStep` succeeds (its only
output is lake's generic "consider adding `module`" notice, printed for every file of the project).
The file has 1744 lines (above the preferred 1500; it was not split because splitting was not
authorised).

New shared definition introduced here (not in `Defs.lean`):

```lean
def Spec.expF (P : Spec ι) (N : Noise ι) (η : ℝ) (c : ι → ℝ) : ℝ :=
  P.sB c * P.EsNext N P.D η c - P.EsNext N P.B η c * P.sD c
```

Namespaces: one-step statements are in `SuspiciousAlignment.Spec` (dot notation `P.…`); generic
helpers (facts about `mom`/`theta` of an arbitrary state, real-variable lemmas, the concrete example)
are in `SuspiciousAlignment.OneStep` and take `P` as an explicit first argument.

## Changes in fix round 1 (signature changes — read this if you call these lemmas)

Names are unchanged; the following lemmas lost a superfluous hypothesis (review issue 1 and 3):

| Lemma | Old hypotheses | New hypotheses |
|---|---|---|
| `OneStep.theta_lt_theta_iff P c c'` | `hs : 0 < P.s c`, `hs' : 0 < P.s c'` | `hs : 0 < P.s c` |
| `OneStep.theta_gt_theta_iff P c c'` | `hs`, `hs'` | `hs' : 0 < P.s c'` |
| `Spec.theta_lt_theta_cNext_iff η c ζ` | `hs`, `hs'` | `hs : 0 < P.s c` |
| `Spec.theta_cNext_lt_theta_iff η c ζ` | `hs`, `hs'` | `hs' : 0 < P.s (P.cNext η c ζ)` |
| `Spec.theta_lt_thetaBarNext_iff N η c` | `hs`, `hE` | `hs : 0 < P.s c` |
| `Spec.thetaBarNext_lt_theta_iff N η c` | `hs`, `hE` | `hE : 0 < P.EsNext N P.D η c + P.EsNext N P.B η c` |
| `Spec.thetaBarNext_lt_theta_of_lt_etaStar N η c` | `hp : 0 < P.pCoef N c`, `hη`, `h` | `hη : 0 < η`, `h : η < P.etaStar N c` |

The `=` versions (`OneStep.theta_eq_theta_iff`, `Spec.theta_cNext_eq_theta_iff`,
`Spec.thetaBarNext_eq_theta_iff`) and the difference identities keep both hypotheses (both are
needed). No lemma was renamed or removed. New lemmas: `OneStep.ratio_sub_ratio`,
`OneStep.ratio_{lt,gt,eq}_ratio_iff_sharp`, `OneStep.theta_{lt,gt,eq}_theta_iff_sharp`,
`Spec.theta_lt_theta_cNext_iff_sharp`, `Spec.theta_cNext_lt_theta_iff_sharp`,
`Spec.theta_cNext_eq_theta_iff_sharp`, `Spec.theta_lt_thetaBarNext_iff_sharp`,
`Spec.thetaBarNext_lt_theta_iff_sharp`, `Spec.thetaBarNext_eq_theta_iff_sharp`,
`Spec.thetaBarNext_lt_theta_iff_of_smin_pos`, `Spec.s_cNext_eq_zero_iff`, `Spec.s_cNext_pos_iff`,
`Spec.etaStar_nonpos_of_pCoef_nonpos`, `Spec.etaStar_pos_iff_pCoef_pos_and_qCoef_neg`,
`Spec.etaStar_pos_iff_pCoef_pos_and_theta`, `Spec.lt_etaStar_iff`, `Spec.expF_neg_of_lt_etaStar`,
and the finite-`d` sign-mismatch instances `OneStep.exSpec_expect_fCompare_pos_and_expect_theta_lt`,
`OneStep.exSpec_expect_fCompare_neg_and_theta_lt_expect_theta` (with helpers `OneStep.exNoise4`,
`OneStep.exZeta`, `OneStep.exSpec_theta`, `OneStep.boolE_fCompare_exZeta`, …).

## Table

Statuses: exact, equivalent-reformulation, hypotheses-added, weakened, strengthened,
paper-claim-false, not-formalized. ("strengthened" is also used for statements that go beyond the
paper, e.g. an implication upgraded to an equivalence or an additional identity.)

| Paper item (tex lines) | Lean declaration | Status | Explanation |
|---|---|---|---|
| A.2 coordinate update, coordinate-level equalities `c_i − η(λ_i c_i + ζ_i) = (1−ηλ_i)c_i − ηζ_i` (913–917) | `Spec.cNext` (Defs), `Spec.cNext_eq` | exact | Second form is the definition, first form is the lemma. |
| A.2 coordinate update, matrix-level step `⟨x_{t+1}, u_i⟩ = ⟨x_t − η(Ax_t + ξ_t), u_i⟩ = c_i − η(λ_i c_i + ζ_i)` (915) | — | not-formalized | Not in this file (it works in eigen-coordinates throughout). It is `MatrixBridge.IsEigenbasis.coord_sgdStep` in `SuspiciousAlignment/MatrixBridge.lean`, which this module does not import. |
| eq. (10), first equality: `θ_{t+1}` as a ratio of sums (919–921) | `Spec.theta_cNext_eq_sum_div_sum` | exact | No hypothesis: at `x_{t+1} = 0` both sides are `0/0 = 0`, the paper's convention `θ(0) = 0` (tex 340, 861). |
| eq. (10), second equality `θ_{t+1} = 1/(1 + s^ℬ_{t+1}/s^𝒟_{t+1})` (922) | `Spec.theta_cNext_eq_one_div` (general state: `OneStep.theta_eq_one_div`) | hypotheses-added | Needs `s^𝒟_{t+1} ≠ 0`, which is the paper's own assumption (Remark, 928). `OneStep.theta_eq_zero_and_one_div_eq_one` shows it is necessary in Lean (LHS `0`, RHS `1` otherwise). |
| Remark in A.2: the exceptional sets `{s_{t+1} = 0}`, `{s^𝒟_{t+1} = 0}`, the affine set `𝒱` (928–931) | `Spec.s_cNext_eq_zero_iff`, `Spec.s_cNext_pos_iff`, `Spec.sD_cNext_eq_zero_iff`, `Spec.mom_cNext_eq_zero_iff` | equivalent-reformulation | Algebraic description only: `s_{t+1} = 0 ↔ ∀ i, η ζ_i = (1−ηλ_i) c_i` (a single point for `η ≠ 0`); `s^S_{t+1} = 0 ↔ ∀ i ∈ S, η ζ_i = (1−ηλ_i) c_i` (`S = 𝒟`: the set `𝒱`). |
| Remark in A.2: the exceptional sets are null, `θ_{t+1}` is integrable, the integral identity (928–934) | — | not-formalized | Not in this file: probability layer (`SuspiciousAlignment/Prob/NoiseModel.lean`, section `NullSets`). See gap G4 for the hypotheses the claim needs. |
| eq. (12) `f_t(η) = s^ℬ_t s^𝒟_{t+1} − s^ℬ_{t+1} s^𝒟_t` (936–939) | `Spec.fCompare` (Defs) | exact | Definition. |
| `θ_{t+1} − θ_t = f_t / (s_t s_{t+1})` (implicit behind 941–944) | `Spec.theta_cNext_sub_theta` (general: `OneStep.theta_sub_theta`) | strengthened | Additional identity; hypotheses `s_t ≠ 0`, `s_{t+1} ≠ 0`. |
| `θ_{t+1} > θ_t ⟺ f_t(η) > 0` (941–944) | `Spec.theta_lt_theta_cNext_iff`; exact validity `Spec.theta_lt_theta_cNext_iff_sharp` | hypotheses-added | Needs `x_t ≠ 0` (`s_t > 0`) **only** — nothing on `x_{t+1}` (if `x_{t+1} = 0` both sides are false). This is the one real gap of 941–944: the paper has no such hypothesis and the claim fails at `x_t = 0` (`Spec.exists_theta_lt_theta_cNext_and_fCompare_eq_zero`). Exactly: the equivalence holds iff `x_t ≠ 0` or `s^𝒟_{t+1} = 0`. Direction `⇐` holds unconditionally: `Spec.theta_lt_theta_cNext_of_fCompare_pos`. |
| `θ_{t+1} < θ_t ⟺ f_t(η) < 0` (941–944) | `Spec.theta_cNext_lt_theta_iff`; exact validity `Spec.theta_cNext_lt_theta_iff_sharp` | exact | Needs `s_{t+1} > 0` **only**, which is the paper's own standing assumption (Remark, 928); nothing on `x_t` (if `x_t = 0` both sides are false). So the paper's `<` equivalence is correct as stated. Exactly: it holds iff `x_{t+1} ≠ 0` or `s^𝒟_t = 0`; outside the paper's assumption it can fail (`Spec.exists_theta_cNext_lt_theta_and_fCompare_eq_zero`). Direction `⇐` unconditional: `Spec.theta_cNext_lt_theta_of_fCompare_neg`. |
| `θ_{t+1} = θ_t ⟺ f_t = 0` (not in the paper; task item (a)) | `Spec.theta_cNext_eq_theta_iff`; exact validity `Spec.theta_cNext_eq_theta_iff_sharp` | strengthened | Additional statement. Needs both `s_t > 0` and `s_{t+1} > 0`; exactly: holds iff (`x_t ≠ 0` or `s^𝒟_{t+1} = 0`) and (`x_{t+1} ≠ 0` or `s^𝒟_t = 0`). The two `exists_…` lemmas above show that neither hypothesis can be dropped. |
| Lemma "Elementwise expectation", per-coordinate identity (1062–1066) and the expansion in its proof (1074–1089) | `Spec.EsNext_singleton`, `Spec.EsNext_eq_sum_singleton`; pathwise expansion `Spec.lam_sq_mul_cNext_sq`, `Spec.EsNext_term_eq`; abstract-expectation form `Spec.expect_mom_two_cNext` | equivalent-reformulation | `𝔼[λ_i² c_{i,t+1}² ∣ x_t]` is represented by `EsNext N {i} η c` (so `EsNext_singleton` is definitional); the content is the pathwise expansion (cross term `−2η λ_i²(1−ηλ_i)c_iζ_i` and `η²λ_i²ζ_i²`) and `expect_mom_two_cNext`: for *any* normalised linear functional `E` on functions `Ω → ℝ` with `E ζ_i = 0`, `E ζ_i² = κ_i²`, `E[s^S_{t+1}] = EsNext`. The measure-theoretic version (Bochner integral) is in the probability layer (`integral_mom_two_cNext` in `SuspiciousAlignment/Prob/NoiseModel.lean`, a module this file does not import). |
| Last display of the proof (1090–1093): `𝔼[s^S_{t+1}] = ∑_S λ²c² − 2η∑_S λ³c² + η²(∑_S λ⁴c² + ∑_S λ²κ²)` | `Spec.EsNext_eq` | exact | For every block `S`. |
| eq. (Eat) (1069) | `Spec.EsNext_D` | exact | With `s^𝒟 = P.sD c`, `∑_𝒟 λ³c² = P.tauD c`, `e_𝒟 = P.eD N`. |
| eq. (Ebt) (1070) | `Spec.EsNext_B` | exact | Same for `ℬ`. |
| Decomposition `s^S_{t+1} = χ_S + g_Sᵀz + zᵀD_S z` (1011–1021, used again in A.5) | `Spec.mom_two_cNext` | exact | Term by term: `χ_S`, `g_S`, `D_S`. |
| Centred form `s^S_{t+1} − 𝔼[s^S_{t+1}] = −2η∑λ²(1−ηλ)cζ + η²∑λ²(ζ²−κ²)` (implicit) | `Spec.mom_two_cNext_sub_EsNext` | strengthened | Additional identity; the bridge to the probability layer. |
| Lemma "Quadratic form", eq. (quad-form) `𝔼[f_t(η) ∣ x_t] = p_t η² + q_t η` (1098–1102, proof 1110–1122) | `Spec.expF`, `Spec.expF_eq`, `Spec.expF_eq_mul`; `Spec.fCompare_sub_expF`; `Spec.expect_fCompare` | exact | In algebraic form: `expF` is the first line of the paper's proof, `expF_eq` the result. `expect_fCompare` shows `E[f_t] = expF` for any abstract expectation with the two moment properties, which justifies the name. `pCoef`, `qCoef` (Defs) match (p-def), (q-sign). |
| eq. (q-sign), first inequality `q_t ≤ 2 s^ℬ s^𝒟 (λ_{k+1} − λ_k)` (1105) | `Spec.qCoef_le` | exact | Uses `OneStep.tauB_le` (`∑_ℬ λ³c² ≤ λ_{k+1} s^ℬ`) and `OneStep.le_tauD` (`λ_k s^𝒟 ≤ ∑_𝒟 λ³c²`), the two bounds of line 1123. |
| eq. (q-sign), strict inequality `q_t < 0`, stated unconditionally (1105, 1123) | corrected: `Spec.qCoef_neg`, `Spec.qCoef_neg_iff`, `Spec.qCoef_neg_iff_theta`, `Spec.qCoef_eq_zero_iff`, `Spec.qCoef_eq_zero_iff_theta`, `Spec.qCoef_nonpos`; counterexamples `Spec.exists_theta_eq_one_qCoef_eq_zero`, `Spec.exists_theta_eq_zero_qCoef_eq_zero` | paper-claim-false | Exact statement: `q_t ≤ 0` always; `q_t < 0 ⟺ (s^𝒟 > 0 ∧ s^ℬ > 0) ⟺ 0 < θ_t < 1`; `q_t = 0 ⟺ θ_t ∈ {0, 1}`. See G1. |
| eq. (p-def) (1106) | `Spec.pCoef` (Defs) | exact | Definition. |
| Values of `p_t` in the degenerate cases (not in the paper) | `Spec.pCoef_of_sD_eq_zero`, `Spec.pCoef_of_sB_eq_zero` | strengthened | Additional: `p_t = s^ℬ e_𝒟` if `θ_t = 0`, `p_t = −s^𝒟 e_ℬ` if `s^ℬ = 0`. |
| "If `p_t ≠ 0` … the non-zero root `η*_t := −q_t/p_t`" (1108); main-text eq. (2) (388–395) | `Spec.etaStar` (Defs), `Spec.etaStar_eq`, `Spec.expF_etaStar`, `Spec.expF_eq_zero_iff`, `Spec.etaStar_eq_zero_iff` | hypotheses-added | `etaStar_eq` is eq. (2) verbatim. For `p_t ≠ 0` the roots are exactly `0` and `η*_t`; "non-zero" needs `q_t ≠ 0`, i.e. `0 < θ_t < 1`. See G2. |
| Remark: parabola through the origin (1126) | `Spec.expF_zero` | exact | |
| Remark, `p_t > 0`: `η*_t > 0` (1145) | `Spec.etaStar_pos`, `Spec.etaStar_pos_iff`, `Spec.etaStar_nonneg`; unconditional: `Spec.etaStar_pos_iff_pCoef_pos_and_qCoef_neg`, `Spec.etaStar_pos_iff_pCoef_pos_and_theta`, `Spec.etaStar_nonpos_of_pCoef_nonpos` | hypotheses-added | Needs `q_t < 0`. In general `η*_t > 0 ⟺ p_t > 0 ∧ q_t < 0 ⟺ p_t > 0 ∧ 0 < θ_t < 1` (no assumption). Counterexample to the Remark's claim: `Spec.exists_pCoef_pos_and_etaStar_eq_zero`. |
| Remark, `p_t > 0`: `𝔼f < 0` for `0 < η < η*_t`, `𝔼f > 0` for `η > η*_t` (1145) | `Spec.expF_neg_iff_lt_etaStar`, `Spec.expF_eq_zero_iff_eq_etaStar`, `Spec.expF_pos_iff_etaStar_lt`; without assuming `p_t > 0`: `Spec.lt_etaStar_iff`, `Spec.expF_neg_of_lt_etaStar` | strengthened | Equivalences for `η > 0`, `p_t > 0` (no assumption on `q_t`). `0 < η < η*_t ⟹ 𝔼f < 0` holds with no assumption on `p_t` (the hypothesis forces `p_t > 0`). |
| Remark, `p_t < 0`: `𝔼f < 0` for all `η > 0` (1147) | `Spec.expF_neg_of_pCoef_neg` | exact | Only `q_t ≤ 0` (always true) is needed, so this half of the Remark is correct even at `θ_t ∈ {0,1}`. |
| The case `p_t = 0`, omitted by the Remark; complete sign description for `η > 0` | `Spec.expF_neg_of_pCoef_nonpos`, `Spec.expF_nonpos_of_pCoef_nonpos`, `Spec.expF_pos_iff`, `Spec.expF_neg_iff`, `Spec.expF_neg_iff_linear`, `Spec.expF_pos_iff_linear` | strengthened | `𝔼f > 0 ⟺ p_t > 0 ∧ η > η*_t`; `𝔼f < 0 ⟺ (p_t > 0 ∧ η < η*_t) ∨ (p_t ≤ 0 ∧ (p_t < 0 ∨ q_t < 0))`; division-free: sign of `p_t η + q_t`. See G3. |
| Remark: "`𝔼[f_t] < 0`, implying the expected alignment `𝔼[θ_{t+1}]` decreases" / "`> 0` … increases" (1145–1147); finite-`d` cores of Theorems 2–3 | `Spec.thetaBarNext_lt_theta_of_lt_etaStar`, `Spec.theta_lt_thetaBarNext_of_etaStar_lt`, `Spec.thetaBarNext_lt_theta_of_pCoef_nonpos` | weakened | Proved for the ratio of expectations `thetaBarNext` (deterministic equivalent), not for `𝔼[θ_{t+1}]`: `0 < η < η*_t ⟹ thetaBarNext < θ_t` (exactly the hypothesis of Theorem 2); `p_t > 0`, `η > η*_t ⟹ θ_t < thetaBarNext`; `p_t ≤ 0`, `0 < θ_t < 1`, `η > 0 ⟹ thetaBarNext < θ_t`. The statement about `𝔼[θ_{t+1}]` itself is only valid as `d → ∞` (other layers); read literally at finite `d` it is false, see G7 and the instances `OneStep.exSpec_expect_fCompare_pos_and_expect_theta_lt`, `OneStep.exSpec_expect_fCompare_neg_and_theta_lt_expect_theta`. |
| Display 1040–1048: `lim 𝔼[θ_{t+1}] < θ_t ⟹ 𝔼[f_t] < 0` (deterministic equivalent) | `Spec.thetaBarNext_sub_theta`, `Spec.thetaBarNext_lt_theta_iff`, `Spec.theta_lt_thetaBarNext_iff`, `Spec.thetaBarNext_eq_theta_iff`, the three `…_iff_sharp` versions, `Spec.thetaBarNext_lt_theta_iff_of_smin_pos`, `Spec.thetaBarNext_lt_theta_of_expF_neg`, `Spec.theta_lt_thetaBarNext_of_expF_pos`, `Spec.thetaBarNext_eq_one_div`, `Spec.thetaBarNext_nonneg`, `Spec.thetaBarNext_le_one`, `Spec.thetaBarNext_zero` | strengthened | Finite `d`, equivalences instead of one implication. Identity `thetaBarNext − θ_t = expF / (s_t (𝔼s^𝒟_{t+1} + 𝔼s^ℬ_{t+1}))` for `s_t ≠ 0`, `𝔼s_{t+1} ≠ 0`. Decrease: `thetaBarNext < θ_t ⟺ expF < 0` needs only `𝔼s_{t+1} > 0` (true for every state when `η ≠ 0`, `s_min > 0`); increase: `θ_t < thetaBarNext ⟺ expF > 0` needs only `x_t ≠ 0`; equality needs both. The implications `expF < 0 ⟹ thetaBarNext < θ_t` and `expF > 0 ⟹ θ_t < thetaBarNext` need no hypothesis. Necessity: `Spec.theta_zero_lt_thetaBarNext_and_expF_eq_zero`, `Spec.exists_thetaBarNext_lt_theta_and_expF_eq_zero`. See G5. |
| Positivity of `𝔼[s^S_{t+1} ∣ x_t]` (implicit; "`y_0 ∈ (0,∞)`" at 1027; task item (e)) | `Spec.EsNext_nonneg`, `Spec.EsNext_eq_zero_iff`, `Spec.EsNext_pos_iff`, `Spec.EsNext_pos_of_kap2_pos`, `Spec.EsNext_pos_of_smin_pos`, `Spec.EsNext_pos_of_state`, `Spec.EsNext_D_add_EsNext_B`, `Spec.EsNext_D_add_EsNext_B_pos_iff`, `Spec.EsNext_D_add_EsNext_B_pos_of_smin_pos`, `Spec.EsNext_zero` | strengthened | Additional exact characterisations: `EsNext ≥ 0`; `EsNext S = 0 ⟺ ∀ i ∈ S, (1−ηλ_i)c_i = 0 ∧ η κ_i² = 0`. In particular `𝔼[s_{t+1}] > 0` whenever `η ≠ 0` and `s_min > 0`, or some `c_i ≠ 0` with `ηλ_i ≠ 1`. |
| Moment bounds (the two of line 1123 and analogues needed downstream) | `OneStep.mom_add_le`, `OneStep.le_mom_add`, `OneStep.tauB_le`, `OneStep.le_tauB`, `OneStep.tauD_le`, `OneStep.le_tauD`, `OneStep.mom_four_B_le`, `OneStep.le_mom_four_B`, `OneStep.mom_four_D_le`, `OneStep.le_mom_four_D` | strengthened | `tauB_le`, `le_tauD` are exactly the bounds of line 1123; the others are additional: `a^j ∑_S λ^p c² ≤ ∑_S λ^{p+j} c² ≤ b^j ∑_S λ^p c²` when `a ≤ λ_i ≤ b` on `S`. |
| Facts on `θ` of an arbitrary state; comparison of two ratios `a/(a+b)` (not in the paper) | `OneStep.theta_pos_iff`, `OneStep.theta_eq_zero_iff`, `OneStep.theta_eq_one_iff`, `OneStep.theta_mem_Ioo_iff`, `OneStep.theta_eq_zero_or_eq_one_iff`, `OneStep.theta_sub_theta`, `OneStep.theta_lt_theta_iff`, `OneStep.theta_gt_theta_iff`, `OneStep.theta_eq_theta_iff`, `OneStep.theta_{lt,gt,eq}_theta_iff_sharp`, `OneStep.theta_lt_theta_of_pos`, `OneStep.theta_gt_theta_of_neg`, `OneStep.ratio_sub_ratio`, `OneStep.ratio_{lt,gt,eq}_ratio_iff_sharp`, `OneStep.mom_eq_zero_iff`, `OneStep.mom_pos_iff` | strengthened | Additional, reusable for the projected updates (`cNextProj`): the comparison lemmas are stated for two arbitrary states `c`, `c'`. |
| Figure and caption (1128–1143) | — | not-formalized | No mathematical content beyond the Remark (the two panels are the cases `p_t > 0`, `p_t < 0` formalized above). |

## Non-vacuity

* Concrete instance in the file (`OneStep.exSpec`, `OneStep.exNoise`, `OneStep.exNoiseB`): `λ = (2, 1)`,
  `𝒟 = {0}`, `x_t = (1, 1)` (`θ_t = 4/5`). With `κ² = (1, 1)`: `q_t = −8`, `p_t = 12`, `η*_t = 2/3`
  (`exSpec_qCoef`, `exSpec_pCoef`, `exSpec_etaStar`); with `κ² = (0, 10)`: `p_t = −28`
  (`exSpec_pCoef_B`). Three `example`s instantiate the decrease regime (`η = 1/2`; the hypotheses
  `0 < η < η*_t` of `Spec.thetaBarNext_lt_theta_of_lt_etaStar`), the increase regime (`η = 1`), and
  the `p_t ≤ 0` regime.
* The hypotheses of `expect_mom_two_cNext` / `expect_fCompare` are satisfiable for every `P`, `N`:
  `OneStep.boolE` (Rademacher average on `Bool`) with `ζ_i = ±√κ_i²` (`example`), and
  `OneStep.boolE_fCompare_exZeta` for the two-point noise `±(a, a)`.
* The single positivity hypotheses of the comparison lemmas (`s_t > 0`, resp. `s_{t+1} > 0`,
  `𝔼s_{t+1} > 0`) are satisfied e.g. by any `c ≠ 0` with `η = 0`; the `…_iff_sharp` lemmas have no
  hypotheses at all.
* Numerical cross-checks (numpy): the prover's Monte-Carlo check (full non-diagonal `Σ`, `d = 7`,
  `k = 3`, 4·10⁵ samples) and the reviewer's exact discrete check (`d = 6`, 60 instances including
  `θ ∈ {0,1}`) of `𝔼[f_t] = p_tη² + q_tη`, of the pathwise equivalences and of the bridge identity
  agree with the formal statements. The fixer re-ran the finite-`d` sign-mismatch experiments of G7.

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
`q_t = 0`. In general `η*_t > 0 ⟺ p_t > 0 ∧ 0 < θ_t < 1`
(`Spec.etaStar_pos_iff_pCoef_pos_and_theta`); in particular the hypothesis `0 < η < η*_t` of
Theorem 2 already implies `p_t > 0` and `0 < θ_t < 1`, which is why
`Spec.thetaBarNext_lt_theta_of_lt_etaStar` needs no further hypothesis. (For `p_t = 0` the paper
leaves `η*_t` undefined; Lean's totalised value is `0`, so the hypothesis is empty there, and for
`p_t < 0` it is empty because `η*_t ≤ 0`. The decrease for `p_t ≤ 0` is the separate statement
`Spec.thetaBarNext_lt_theta_of_pCoef_nonpos`.)

**G3 — the Remark omits `p_t = 0`.** Then `𝔼[f_t(η)] = q_t η`, negative for all `η > 0` iff `q_t < 0`
(covered by `Spec.expF_neg_of_pCoef_nonpos`), and identically `0` if also `q_t = 0`
(e.g. `θ_t = 1` and `e_ℬ = 0`, where the bulk coordinates stay `0` almost surely and `θ ≡ 1`).
The sentence "the behavior for any positive step size is entirely determined by the sign of `p_t`"
is therefore slightly too strong: for `p_t ≤ 0` the strictness depends on `(p_t, q_t) ≠ (0, 0)`
(`Spec.expF_neg_iff`).

**G4 — the pathwise equivalences (tex 941–944): only `θ_{t+1} > θ_t ⟺ f_t > 0` has a gap, namely
`x_t ≠ 0`; the "zero-measure" justification (tex 928–934) needs non-degenerate noise for the
`𝒟`-set only.**
* `θ_{t+1} < θ_t ⟺ f_t < 0` is **correct as stated** under the paper's assumption `s_{t+1} ≠ 0`
  (tex 928), for every `x_t` including `x_t = 0` (there both sides are false):
  `Spec.theta_cNext_lt_theta_iff`. Exactly, it holds iff `x_{t+1} ≠ 0` or `s^𝒟_t = 0`
  (`Spec.theta_cNext_lt_theta_iff_sharp`); it fails e.g. for `x_t = u_1`, `η = 1/λ_1`, `ξ_t = 0`,
  where `x_{t+1} = 0`, `f_t = 0`, `θ_{t+1} = 0 < 1 = θ_t`
  (`Spec.exists_theta_cNext_lt_theta_and_fCompare_eq_zero`) — a configuration the paper excludes.
* `θ_{t+1} > θ_t ⟺ f_t > 0` needs `x_t ≠ 0`, which the paper does not assume: if `x_t = 0` then
  `f_t ≡ 0` but `θ_{t+1} > 0 = θ_t` as soon as `s^𝒟_{t+1} > 0`
  (`Spec.exists_theta_lt_theta_cNext_and_fCompare_eq_zero`). Exactly, the equivalence holds iff
  `x_t ≠ 0` or `s^𝒟_{t+1} = 0` (`Spec.theta_lt_theta_cNext_iff_sharp`); under the paper's own
  assumption `s^𝒟_{t+1} ≠ 0` it therefore holds iff `x_t ≠ 0`. No assumption on `x_{t+1}` is needed
  (`Spec.theta_lt_theta_cNext_iff`).
* The implications `f_t > 0 ⟹ θ_{t+1} > θ_t` and `f_t < 0 ⟹ θ_{t+1} < θ_t` hold with no hypothesis;
  the identity `θ_{t+1} − θ_t = f_t/(s_t s_{t+1})` and the `=` equivalence need both `s_t > 0` and
  `s_{t+1} > 0`.
* The two exceptional sets of the Remark behave differently.
  `{s_{t+1} = 0}` is, for `η ≠ 0`, the **single point** `ζ = ((1−ηλ_i)c_i/η)_i`
  (`Spec.s_cNext_eq_zero_iff`). A Gaussian vector with non-zero covariance has no atoms, so this set
  is null under the standing assumption `Tr(Σ) > 0` — no further hypothesis is needed.
  `{s^𝒟_{t+1} = 0}` is the set `𝒱 = {ζ_i = (1−ηλ_i)c_i/η ∀ i ∈ 𝒟}` (`Spec.sD_cNext_eq_zero_iff`), an
  affine subspace of dimension `d − k` (the paper says "hyperplane", which is right only for
  `k = 1`). It is Lebesgue-null (no Sard theorem needed), but that gives probability `0` under
  `ξ ~ 𝒩(0, Σ)` only when the law of `(ζ_i)_{i∈𝒟}` does not charge the point, and `Tr(Σ) > 0` does
  not ensure this. A Gaussian vector hits a fixed point with positive probability iff its
  covariance is `0` and the point is its mean, so `ℙ(s^𝒟_{t+1} = 0) > 0` iff `κ_i² = 0` and
  `(1 − ηλ_i) c_i = 0` for all `i ∈ 𝒟` (for `η ≠ 0`) — by `Spec.EsNext_eq_zero_iff` this is exactly
  `𝔼[s^𝒟_{t+1} | x_t] = 0`. Hence the correct hypothesis for this part of the Remark is
  `0 < P.EsNext N P.D η c` (implied by `η ≠ 0 ∧ s_min > 0`, `Spec.EsNext_pos_of_smin_pos`).
  Counter-scenario allowed by the paper's assumptions: noise supported in the bulk directions and
  `θ_t = 0`; then `s^𝒟_{t+1} = 0` surely, `θ_{t+1} = 0`, and the second form of eq. (10) is
  undefined. The integrals `∫ θ_{t+1} dξ` are also written without the Gaussian density. (The
  measure-zero statements themselves are not formalized here — probability layer.)

**G5 — the bridge display (tex 1040–1048).** (i) Typo: `θ_t` is written as
`1 / (1 − (1/ρ) (…)/(…))`; the sign must be `+`. (ii) The display states only the implication
"`lim 𝔼θ_{t+1} < θ_t ⟹ 𝔼 f_t < 0`", whereas the theorems use the converse direction
(`𝔼 f_t < 0 ⟹` decrease). At finite `d` both directions hold for the deterministic equivalent:
`thetaBarNext − θ_t = 𝔼[f_t]/(s_t 𝔼[s_{t+1}])` (`Spec.thetaBarNext_sub_theta`), and the direction
actually needed is unconditional (`Spec.thetaBarNext_lt_theta_of_expF_neg`,
`Spec.theta_lt_thetaBarNext_of_expF_pos`). (iii) Hypotheses of the equivalences: the decrease
equivalence `thetaBarNext < θ_t ⟺ 𝔼f_t < 0` needs only `𝔼[s_{t+1} | x_t] > 0` (it holds for every
state, `x_t = 0` included, as soon as `η ≠ 0` and `s_min > 0`:
`Spec.thetaBarNext_lt_theta_iff_of_smin_pos`); the increase equivalence `θ_t < thetaBarNext ⟺ 𝔼f_t > 0`
needs only `x_t ≠ 0`; the equality version needs both. Each hypothesis can fail and then so does the
equivalence (`Spec.exists_thetaBarNext_lt_theta_and_expF_eq_zero` with zero noise,
`Spec.theta_zero_lt_thetaBarNext_and_expF_eq_zero` at `x_t = 0`); the exact conditions are the
`…_iff_sharp` lemmas.

**G6 — remarks (no error).** Lemma "Elementwise expectation" uses only `𝔼ζ_i = 0` and
`𝔼ζ_i² = κ_i²`: neither Gaussianity nor diagonality of `Σ` in the eigenbasis is needed
(`Spec.expect_mom_two_cNext`, `Spec.expect_fCompare` are stated for an arbitrary normalised linear
functional on functions `Ω → ℝ`; the Bochner-integral version is in `Prob/NoiseModel.lean`). The
lemma "Quadratic form" holds for every real `η` (including `η ≤ 0`), every state (including
`x_t = 0`, where `p_t = q_t = 0`) and every finite `d`.

**G7 — at finite `d` the sign of `𝔼[f_t]` decides the sign of `thetaBarNext − θ_t` only, not of
`𝔼[θ_{t+1}] − θ_t` (Remark, tex 1145–1147).** The Remark says "`𝔼[f_t(η_t)] < 0`, implying the
expected alignment `𝔼[θ_{t+1}]` decreases" and "`𝔼[f_t(η_t)] > 0`, implying the expected alignment
increases". `𝔼[f_t] ≷ 0` is equivalent to `𝔼[s^𝒟_{t+1}]/𝔼[s_{t+1}] ≷ θ_t` (under the hypotheses
of G5), but
`𝔼[θ_{t+1}] = 𝔼[s^𝒟_{t+1}/s_{t+1}]` is the expectation of a ratio, and the two differ at finite `d`;
the "implying" is justified only through Lemma "Asymptotic ratio of expectations", i.e. as
`d → ∞`. Read literally at finite `d`, both implications are false:
* *Formal witnesses (two-point noise).* On `λ = (2, 1)`, `𝒟 = {u_1}`, `x_t = (1, 1)`
  (`θ_t = 4/5`), with the noise `ζ = ±(a, a)` (mean `0`, second moments `a²`, so that
  `𝔼[f_t] = p_tη² + q_tη` by `OneStep.boolE_fCompare_exZeta`), `p_t = 12`, `q_t = −8`, `η*_t = 2/3`:
  - `a = 1`, `η = 1 > η*_t`: `𝔼[f_t] = 4 > 0`, `thetaBarNext = 8/9 > θ_t`, but
    `𝔼[θ_{t+1}] = 8/17 < 4/5` (`OneStep.exSpec_expect_fCompare_pos_and_expect_theta_lt`);
  - `a = 2`, `η = 1/3 < η*_t` (the hypothesis of Theorem 2): `𝔼[f_t] = −4/3 < 0`,
    `thetaBarNext = 5/7 < θ_t`, but `𝔼[θ_{t+1}] = 11/13 > 4/5`
    (`OneStep.exSpec_expect_fCompare_neg_and_theta_lt_expect_theta`).
  These show that the two moment identities used in A.5 cannot give the sign of
  `𝔼[θ_{t+1}] − θ_t`. The noise here is not Gaussian, so they are not counterexamples to the paper
  under its Gaussian assumption.
* *Numerical counterexamples with Gaussian noise* (`d = 2`, `k = 1`, `λ = (2, 1)`, `ξ ~ 𝒩(0, Σ)`
  with `Σ = diag(κ²)`; Monte Carlo, 2·10⁷ samples, standard error ≈ 10⁻⁴; not formalized):
  - `x_t = (1, 1)`, `κ² = (1, 1)`, `η = 1`: `p_t = 12`, `q_t = −8`, `η*_t = 2/3 < η`,
    `𝔼[f_t] = +4`, `thetaBarNext = 0.8889 > θ_t = 0.8`, but `𝔼[θ_{t+1}] = 0.7588 < θ_t`;
  - `x_t = (1, 2)`, `κ² = (1/4, 9)`, `η = 5/4`: `p_t = 16`, `q_t = −32`, `η*_t = 2 > η`,
    `𝔼[f_t] = −15`, `thetaBarNext = 0.4246 < θ_t = 0.5`, but `𝔼[θ_{t+1}] = 0.5540 > θ_t`;
  - the reviewer's instance `x_t = (−1.1593, 0.8333)`, `κ² = (4.4638, 0.2543)`, `η = 0.6629`:
    `𝔼[f_t] = +4.82`, `thetaBarNext = 0.978 > θ_t = 0.8856`, but `𝔼[θ_{t+1}] = 0.866 < θ_t`
    (reproduced: `0.8661 ± 0.0002`).

  Script used (numpy):
  ```python
  import numpy as np
  lam = np.array([2.0, 1.0]); rng = np.random.default_rng(2024)
  def run(c, kap, eta, n=20_000_000):
      c = np.array(c, float); kap = np.array(kap, float)
      z = rng.normal(size=(n, 2)) * np.sqrt(kap)
      cn = (1 - eta * lam) * c - eta * z
      a, b = 4 * cn[:, 0] ** 2, cn[:, 1] ** 2
      sD, sB = 4 * c[0] ** 2, c[1] ** 2
      print("E f =", (sB * a - b * sD).mean(), " theta_t =", sD / (sD + sB),
            " thetaBar =", a.mean() / (a.mean() + b.mean()), " E theta_{t+1} =", (a / (a + b)).mean())
  run((1, 1), (1, 1), 1.0); run((1, 2), (0.25, 9), 1.25)
  ```
  Consequently every finite-`d` statement in this project about "decrease/increase in expectation"
  is a statement about `thetaBarNext`; the passage to `𝔼[θ_{t+1}]` is asymptotic.

**G8 — typo (tex 934).** "The case of `{ξ | s^𝒟_{t+1}(ξ) = 0}` is analogous" should read
`{ξ | s_{t+1}(ξ) = 0}`: the `𝒟`-set is the one that has just been treated. (And, by G4, the two
cases are not analogous: the second set is a single point and is null without further assumptions.)

## Reviewer disputes (fix round 1)

No blocker or major issue is disputed; the major issue (superfluous positivity hypotheses and the
over-claims that they are necessary) was fixed as suggested, and the minor issues 2–5 were all
addressed. Two *optional* suggestions of the last minor issue were deliberately not followed:

* *"Move or alias the generic lemmas into namespace `Spec`."* Not done. The task prescribes that
  helpers live in `SuspiciousAlignment.OneStep`; moving them would rename ~35 lemmas that other
  files may use, and aliasing them into `Spec` would put generic names such as `Spec.tauB_le`,
  `Spec.mom_eq_zero_iff`, `Spec.theta_mem_Ioo_iff` into the shared `Spec` namespace, where sibling
  modules that define the same short names in their own namespaces today
  (`EtaStarBounds.tauB_le`, `LossThreshold.mom_eq_zero_iff`, `LossThreshold.theta_mem_Ioo_iff`, …)
  could later clash with them. Downstream files can `open OneStep` and write `tauB_le P c`.
* *"Restate the abstract-expectation lemmas for a functional on a submodule containing `1`, `ζ_i`,
  `ζ_i²`."* Not done, because the measure-theoretic statements already exist in the probability
  layer, proved directly with the Bochner integral (`integral_mom_two_cNext`,
  `integrable_fCompare`, `integral_fCompare` in `SuspiciousAlignment/Prob/NoiseModel.lean`, under
  its `IsNoise` hypothesis), so a second abstract route would only duplicate them. The limitation is now stated in the section header of *Abstract expectation* in the Lean
  file and in G6: the functional there is defined on all functions `Ω → ℝ`, hence covers finite
  averages but not the Bochner integral.

## Suggestions for downstream files

* Probability layer: from `Spec.mom_two_cNext_sub_EsNext` and `Spec.fCompare_sub_expF`,
  `∫ s^S_{t+1} = EsNext` and `∫ f_t = expF` follow by linearity of the integral once `ζ_i`, `ζ_i²` are
  integrable with `∫ζ_i = 0`, `∫ζ_i² = κ_i²`.
* Theorems 2–4: reduce to the sign of `P.expF N η c` via `Spec.expF_neg_of_lt_etaStar` (hypotheses
  `0 < η < η*_t` only), `Spec.expF_neg_iff_lt_etaStar`, `Spec.expF_pos_iff_etaStar_lt`, or the
  division-free `Spec.expF_neg_iff_linear` / `Spec.expF_pos_iff_linear`; then use
  `Spec.thetaBarNext_lt_theta_of_expF_neg` / `Spec.theta_lt_thetaBarNext_of_expF_pos` (no positivity
  side conditions). For bounds on `p_t`, the moment inequalities `OneStep.mom_four_*`, `OneStep.tau*`
  are available.
* Any theorem that invokes "`q_t < 0`" or "`η*_t > 0`" must carry `0 < θ_t < 1`
  (equivalently `0 < P.sD c ∧ 0 < P.sB c`), cf. G1–G2 — or get it for free from `0 < η < η*_t`
  (`Spec.lt_etaStar_iff`, `Spec.etaStar_pos_iff_pCoef_pos_and_theta`).
* Do not state finite-`d` results about `𝔼[θ_{t+1}]` itself: only `thetaBarNext` is controlled by
  the sign of `𝔼[f_t]` at finite `d` (G7).
