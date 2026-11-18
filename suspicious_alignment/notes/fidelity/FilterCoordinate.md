# Fidelity note — `SuspiciousAlignment/Filter/Coordinate.lean`

Module `SuspiciousAlignment.Filter.Coordinate` (imports `Mathlib`, `SuspiciousAlignment.Defs`).

**This file is an extension of the paper (new mathematics).** Its source of truth is the
specification `notes/research/filter_spec.md`, sections 1 (coordinate / commuting model of
spectrally filtered updates) and 4 (vector model). The paper (Deng et al., arXiv:2601.11789v2) is
used only for comparison: `η*_t` (tex 386–397), the comparison functional (tex 910–947), the
quadratic form (tex 1061–1148) and Theorem 7 (tex 490–495).

Layer: exact finite-`d`, pathwise, purely algebraic (no probability, no limits). Every statement
holds for every finite index type `ι`, every spectrum `P : Spec ι`, every filter `f : ℝ → ℝ`
(no regularity assumed), every state `c`.

Status: 0 `sorry`; `#print axioms` on all 165 declarations of the file gives only `propext`,
`Classical.choice`, `Quot.sound`; `lake build SuspiciousAlignment.Filter.Coordinate` succeeds with
no warnings from this file. Nothing in the task is left unproven.

This file is the first formal check of the specification. Before proving, every statement was
tested with numpy on random instances (random spectra with `2 ≤ d ≤ 6`, random block sizes,
degenerate blocks, zero coefficients with probability 0.15–0.25, `η` equal to a coefficient
magnitude / to `1/ν_i` / to `η*(1 ± 10⁻³)`, negative `η`, filters `id`, `1`, `σ^p`, affine filters
with sign changes, `cos(3σ) + 1/2`; about 20 000 instances for 1.1–1.6, 40 000 ordered/reversed
states for 1.7–1.9, 67 000 for section 4). **No statement of sections 1 and 4 is false in the
reading intended by the spec; the deviations found are listed in "Discrepancies" below** (one
missing hypothesis in 4.2, one redundant proviso in 1.7/1.8, several hypotheses that can be
weakened, one Lean-convention edge case in 4.1).

## Definitions

| Spec | Lean | Status | Remark |
|---|---|---|---|
| `oddExt f g := Real.sign g * f |g|` | `Spec.oddExt` | exact | Lives in `namespace Spec` (as requested) but does not take `P`: write `Spec.oddExt f g`. |
| `cNextF f η c i := c i − η * oddExt f (λ_i * c i)` | `Spec.cNextF` | exact | |
| eq. (1.0) `c_i⁺ = c_i − η·sign(c_i)·f(λ_i|c_i|)` | `Spec.cNextF_apply` | exact | Proved equal to the definition (uses `λ_i > 0`). Muon: `Spec.cNextF_one`. |
| `nu f c i := f (λ_i * |c i|) / |c i|` | `Spec.nu` | exact | `ν_i = 0` at `c_i = 0` (`Spec.nu_of_eq_zero`); Muon: `Spec.nu_one`; `Spec.nu_nonneg` for `f ≥ 0` on `[0,∞)`. |
| `momF f S a c := ∑_{i∈S} ν_i^a λ_i² c_i²` | `Spec.momF` | exact | |
| `qF`, `pF`, `etaStarF := −qF/pF` | `Spec.qF`, `Spec.pF`, `Spec.etaStarF` | exact | |
| `fCompareF f η c` | `Spec.fCompareF` | exact | |
| zero noise (`κ² = 0`, `s_min = s_max = 0`) | `Noise.noiseFree` | (task) | The spec's `η*₀` is `P.etaStar Noise.noiseFree c`; written out in `Spec.etaStar_noiseFree_eq`. Only `e_𝒟 = e_ℬ = 0` (`Spec.eD_noiseFree`, `Spec.eB_noiseFree`) is used; quantities of `Defs.lean` that divide by `s_min` (e.g. `gGap`) are degenerate for this noise and are not used. |
| `‖g‖ = √(∑ (λ_i c_i + ζ_i)²)` | `Spec.gradNorm` | exact | |
| `cNextVec f η c ζ i := c_i − η f(‖g‖) g_i/‖g‖` | `Spec.cNextVec` | exact | Parsed as `η * f ‖g‖ * g_i / ‖g‖`. |
| `η_eff = η f(‖g‖)/‖g‖` | `Spec.etaEff` | exact | |

## Table

| Spec item | Lean declaration | Status | Explanation |
|---|---|---|---|
| 1.1 `cNextF f η c i = (1 − η ν_i) c_i` | `Spec.cNextF_eq` | exact | For every `i`, including `c_i = 0`. Key lemma `Spec.oddExt_lam_mul`: `φ_f(λ_i c_i) = ν_i c_i`. |
| 1.2 `cNextF id η c = P.cNext η c 0` | `Spec.cNextF_id` | exact | Equality of functions. |
| 1.2 `nu id c i = λ_i` if `c_i ≠ 0` | `Spec.nu_id` | exact | Also `Spec.nu_id_nonneg`. |
| 1.2 `qF = qCoef`, `pF = pCoef` with zero noise | `Spec.qF_id`, `Spec.pF_id` | exact | Via `Spec.momF_id`: `momF id S a c = P.mom S (a+2) c`. Also `Spec.etaStarF_id`, `Spec.fCompareF_id`. |
| 1.3 energies | `Spec.mom_cNextF`, `Spec.momF_zero` | exact | `P.mom S 2 (cNextF f η c) = M₀ − 2η M₁ + η² M₂`. |
| 1.4 `fCompareF f η c = pF η² + qF η` | `Spec.fCompareF_eq` | exact | No hypothesis. Consequence for SGD: `Spec.fCompare_noiseFree_eq` (Deng's quadratic-form lemma, pathwise at `ζ = 0`). |
| 1.5 `θ(c') < θ(c) ⟺ cross < 0`, same with `>`, `=` | `Spec.theta_lt_iff_cross_neg`, `Spec.theta_gt_iff_cross_pos`, `Spec.theta_eq_iff_cross_eq_zero` | exact | Arbitrary states `c, c'` with `0 < P.s c`, `0 < P.s c'`; `cross = P.sB c * P.sD c' − P.sB c' * P.sD c`. Reused by `Filter/MuonHT.lean`. |
| 1.5 "hence for the filtered step …" | `Spec.theta_cNextF_lt_iff`, `Spec.theta_cNextF_gt_iff`, `Spec.theta_cNextF_eq_iff` | exact | Hypotheses `0 < P.s c`, `0 < P.s (cNextF f η c)`. The second one is necessary: `FilterCoordinate.exSpec_muon_annihilate` (D3). |
| 1.6 double-sum forms | `Spec.qF_eq_double_sum`, `Spec.pF_eq_double_sum` | exact | |
| 1.9 (proof identity) `η* = 2∑w_ij / ∑w_ij(ν_i+ν_j)` | `Spec.etaStarF_eq_double_sum` | extra | No hypothesis (both sides use `x/0 = 0`). |
| 1.7 `qF < 0` | `Spec.qF_neg_of_ordered` | strengthened | Needs only `s^𝒟, s^ℬ > 0` and the ordering; no sign condition (D2). |
| 1.7 `0 < pF` | `Spec.pF_pos_of_ordered` | strengthened | Sign condition only on the bulk and only at non-zero coefficients: `∀ j ∈ ℬ, c_j ≠ 0 → 0 ≤ ν_j` (D2). It cannot be dropped: `FilterCoordinate.exSpec_ordered_without_sign`. |
| 1.7 `etaStarF > 0` | `Spec.etaStarF_pos_of_ordered` | strengthened | Same hypotheses. |
| 1.7 dichotomy for `η > 0` | `Spec.theta_cNextF_lt_iff_of_ordered`, `Spec.theta_cNextF_eq_iff_of_ordered`, `Spec.theta_cNextF_gt_iff_of_ordered` | strengthened | The spec's proviso "given `s(c⁺) > 0`" is **not assumed**: it is a consequence (`Spec.s_cNextF_pos_of_ordered`, D1). |
| 1.7 for all real `η` | `Spec.theta_cNextF_lt_iff_of_ordered'` (`↔ 0 < η ∧ η < η*`), `…_eq_…'` (`↔ η = 0 ∨ η = η*`), `…_gt_…'` (`↔ η < 0 ∨ η* < η`) | extra | |
| 1.7 "for `f = id` this is the noise-free case of Deng's Theorems 2–3" | `Spec.nu_id_lt_nu_id`, `Spec.pCoef_noiseFree_pos`, `Spec.etaStar_noiseFree_pos`, `Spec.s_cNext_noiseFree_pos`, `Spec.theta_cNext_noiseFree_lt_iff`, `…_eq_iff`, `…_gt_iff` (and primed all-`η` versions) | exact | Pathwise, exact for every finite `d`: with `ζ = 0`, `s^𝒟, s^ℬ > 0`, `η > 0`: `θ_{t+1} < θ_t ⟺ η < η*₀`, etc. (Deng's theorems are statements about `lim_{d→∞} 𝔼[θ_{t+1}]`; here there is no noise, so no expectation and no limit. Theorem 3's hypothesis `θ_t ≤ g_gap` is not needed without noise since `p_t > 0`.) |
| 1.8 `pF < 0 < qF`, `etaStarF > 0` | `Spec.qF_pos_of_reversed`, `Spec.pF_neg_of_reversed`, `Spec.etaStarF_pos_of_reversed` | strengthened | Sign condition only on the dominant block at non-zero coefficients (`∀ i ∈ 𝒟, c_i ≠ 0 → 0 ≤ ν_i`); needed for `pF < 0` (`FilterCoordinate.exSpec_reversed_without_sign`), not for `qF > 0`. See D2. |
| 1.8 dichotomy flips | `Spec.theta_cNextF_gt_iff_of_reversed` (`η > 0`: increase `⟺ η < η*`), `…_eq_…`, `…_lt_…` (decrease `⟺ η* < η`); primed versions for all real `η` | strengthened | `s(c⁺) > 0` not assumed (`Spec.s_cNextF_pos_of_reversed`). |
| 1.8 "this cannot happen for SGD" | `Spec.not_reversed_id`, `Spec.qF_id_nonpos` | exact | The reversed ordering is impossible for `f = id` when `s^𝒟, s^ℬ > 0`; moreover `qF id c ≤ 0` at every state, so the conclusion `pF < 0 < qF` never holds for SGD. |
| 1.9 lower bound `2/(b_𝒟+b_ℬ) ≤ etaStarF` | `Spec.two_div_le_etaStarF_of_ordered` | strengthened | Hypotheses of 1.7 plus the upper bounds on `ν`; `a_𝒟, a_ℬ` and `a_𝒟 + a_ℬ > 0` are not needed; `b_𝒟 + b_ℬ > 0` is automatic. |
| 1.9 upper bound `etaStarF ≤ 2/(a_𝒟+a_ℬ)` | `Spec.etaStarF_le_two_div_of_ordered` | strengthened | The sign condition of 1.7 is not needed (it is implied, as far as needed, by `a_𝒟 + a_ℬ > 0`). |
| 1.9 two-sided bound | `Spec.etaStarF_mem_Icc_of_ordered` | exact | Exactly the hypotheses of the spec (with the bulk-only sign condition). |
| (1.9 in the reversed case) | `Spec.two_div_le_etaStarF_of_reversed`, `Spec.etaStarF_le_two_div_of_reversed` | extra | The same two bounds hold under the hypotheses of 1.8 (useful for Muon, spec 2.2). |
| 1.9 corollary for SGD `2/(λ_1+λ_{k+1}) ≤ η*₀ ≤ 2/(λ_k+λ_d)` | `Spec.two_div_le_etaStar_noiseFree`, `Spec.etaStar_noiseFree_le_two_div`, `Spec.etaStar_noiseFree_mem_Icc` | exact | Hypotheses `0 < P.sD c`, `0 < P.sB c` (the hypotheses of 1.7; without them `η*₀ = 0/0 = 0` and the lower bound is false). `η*₀ = P.etaStar Noise.noiseFree c = −qCoef / pCoef` with zero noise. |
| 1.9 comparison with Deng's Theorem 7 | `Spec.thm7_noiseFree_bound_eq`, `Spec.thm7_noiseFree_bound_le_two_div`, `Spec.thm7_noiseFree_bound_le_etaStar` | exact | With zero noise the right-hand side of Theorem 7 is `2 gap₁/(λ_1² − λ_d²)`; `2 gap₁/(λ_1² − λ_d²) ≤ 2/(λ_1+λ_{k+1})` for every spectrum; hence the noise-free Theorem 7 follows from the corollary. |
| (sharpness of the comparison) | `Spec.thm7_noiseFree_bound_lt_two_div`, `Spec.thm7_noiseFree_bound_eq_two_div_iff` | extra | The improvement is strict unless the spectrum is two-level: equality `⟺ λ_k = λ_1 ∧ λ_d = λ_{k+1}`. |
| 4.1 `cNextVec f η c ζ = P.cNext η_eff c ζ` | `Spec.cNextVec_eq_cNext` | exact | Equality of functions, no hypothesis (also for `‖g‖ = 0`, where both sides are `c`). Consequences: `Spec.theta_cNextVec`, `Spec.fCompare_etaEff`. |
| 4.1 Muon `η_eff = η/‖g‖` | `Spec.etaEff_one` | exact | |
| 4.1 HTMuon `η_eff = η‖g‖^{p−1}` | `Spec.etaEff_rpow` | hypotheses-added | Needs `‖g‖ ≠ 0 ∨ p ≠ 1` (D5). SGD: `Spec.etaEff_id` (`η_eff = η` if `‖g‖ ≠ 0`). |
| 4.2 `‖Ax‖ = √(s(c))` | `Spec.gradNorm_noiseFree` | exact | |
| 4.2 `θ(c⁺) < θ(c) ⟺ η‖Ax‖^{p−1} < η*₀(c)` and `>` likewise | `Spec.theta_cNextVec_rpow_lt_iff`, `Spec.theta_cNextVec_rpow_gt_iff` (and `Spec.theta_cNextVec_rpow_eq_iff`) | hypotheses-added | **`0 < η` added** (D4). Strengthened in another direction: holds for every real `p` (the spec's `p < 1` is only needed for the ray statement). General-filter versions: `Spec.theta_cNextVec_noiseFree_lt_iff`, `…_gt_iff`, `…_eq_iff` (in terms of `η_eff`, any real `η`). |
| 4.2 as literally stated (no restriction on `η`) | `Spec.theta_cNextVec_rpow_gt_of_neg` | paper-claim-false | For every `η < 0` the alignment *increases* although `η‖Ax‖^{p−1} < η*₀(c)` (D4). |
| 4.2 `η*₀` invariant under `c ↦ a c`, `a ≠ 0` | `Spec.etaStar_noiseFree_smul` | exact | |
| 4.2 ray statement | `Spec.theta_cNextVec_rpow_ray_lt_iff`, `Spec.theta_cNextVec_rpow_ray_gt_iff` | hypotheses-added | `p < 1`, `0 < a`, and `0 < η` (added): decrease `⟺ (η/η*₀(c))^{1/(1−p)} < a √(s(c))`, increase `⟺` the reverse strict inequality. |
| non-vacuity of 1.7, 1.9 | `FilterCoordinate.exSpec`, `exSpec_muon_ordered`, `exSpec_muon_decrease` | extra | `λ = (2,1)` on `Fin 2`, `𝒟 = {0}`; Muon at `c = (1,2)`: ordering holds, `η* = 4/3 = 2/(ν_0+ν_1)` (both bounds of 1.9 attained), alignment decreases for all `0 < η < 4/3`. |
| non-vacuity of 1.8 | `exSpec_muon_reversed`, `exSpec_muon_increase`, `exSpec_muon_increase_explicit` | extra | Muon at `c = (2,1)`: reversed ordering, `η* = 4/3`, the alignment **increases** for all `0 < η < 4/3`; direct evaluation at `η = 1/2`: `θ` goes from `16/17` to `36/37`. |
| non-vacuity of the SGD corollary and of 4.2 | `exSpec_etaStar_noiseFree`, `exSpec_vector_ray` | extra | `η*₀ = 2/3 = 2/(λ_0+λ_1)` at `c = (1,2)`; normalised SGD along the ray through `c`: decrease `⟺ 3η/2 < a√8`. |

## Discrepancies between the specification and what is proved

**D1 (1.7 and 1.8: the proviso "given `s(c⁺) > 0`" is redundant).** Under the curvature ordering
(either direction) and `s^𝒟, s^ℬ > 0` there are `i ∈ 𝒟`, `j ∈ ℬ` with non-zero coefficients and
`ν_i ≠ ν_j`. Since `c⁺_i = (1 − ην_i) c_i`, `s(c⁺) = 0` would force `ην_i = 1 = ην_j`, i.e.
`ν_i = ν_j`. So `s(c⁺) > 0` for every real `η` (`Spec.s_cNextF_pos_of_ordered`,
`Spec.s_cNextF_pos_of_reversed`, core lemma `FilterCoordinate.s_cNextF_pos_of_ne`), and the Lean
theorems for 1.7/1.8 do not assume it. Same for noise-free SGD (`Spec.s_cNext_noiseFree_pos`).

**D2 (1.7, 1.8, 1.9: weaker hypotheses suffice; which ones are really needed).**
* The spec's "`ν_i ≥ 0`" is used only to get `ν_i + ν_j > 0` on pairs of non-zero coefficients. In
  1.7 it is enough to have `ν_j ≥ 0` for `j ∈ ℬ` with `c_j ≠ 0`; in 1.8 it is enough to have
  `ν_i ≥ 0` for `i ∈ 𝒟` with `c_i ≠ 0`. `qF < 0` (resp. `qF > 0`) needs no sign condition at all.
* The sign condition cannot be dropped: on `exSpec` at `c = (1,1)`, the filter
  `f σ = (11σ − 21)/10` gives `ν = (1/10, −1)` (ordering of 1.7 holds) but `pF = −99/25 < 0`
  (`exSpec_ordered_without_sign`); the filter `f σ = (12 − 11σ)/10` gives `ν = (−1, 1/10)`
  (ordering of 1.8 holds) but `pF = 99/25 > 0` (`exSpec_reversed_without_sign`). In particular 1.8
  must be read with the sign condition of 1.7 carried over (the spec's "if instead …" replaces only
  the ordering).
* 1.9: the lower bound needs neither `a_𝒟, a_ℬ` nor `a_𝒟 + a_ℬ > 0`; the upper bound does not need
  the sign condition.

**D3 (1.5: the hypothesis `s(c') > 0` is genuinely needed outside 1.7/1.8).** With the convention
`θ(0) = 0`, Muon on `exSpec` at the isotropic state `c = (1,1)` with `η = 1` lands on `c⁺ = 0`:
`θ(c⁺) = 0 < 4/5 = θ(c)` although `pF η² + qF η = 0` (`exSpec_muon_annihilate`). This is the
excluded case `η = r` of spec 2.1. The spec states the hypothesis, so this is not an error, only a
confirmation that it cannot be removed.

**D4 (4.2: the hypothesis `η > 0` is missing).** The spec states
`θ(c⁺) < θ(c) ⟺ η‖Ax‖^{p−1} < η*₀(c)` without restricting `η`. The exact statement for every real
`η` is `θ(c⁺) < θ(c) ⟺ 0 < η_eff < η*₀` (`Spec.theta_cNextVec_noiseFree_lt_iff`). For `η < 0` one
has `η_eff < 0 < η*₀`, so the right-hand side of the spec's equivalence holds while the alignment
strictly increases (`Spec.theta_cNextVec_rpow_gt_of_neg`, valid at every state with
`s^𝒟, s^ℬ > 0` and every `p`). Numerical instance: `λ = (2,1)`, `c = (1,1)`, `p = 1/2`,
`η = −0.1`: `θ(c⁺) − θ(c) = +0.0187`, `η‖Ax‖^{p−1} = −0.0669 < η*₀ = 2/3`. For `η = 0` the
equivalence happens to hold in the `<` form but fails in the `>` form … no: at `η = 0` both
`θ(c⁺) < θ(c)` and `θ(c⁺) > θ(c)` are false, while `0 < η*₀` is true, so the `<` form fails at
`η = 0` as well. The Lean statements carry `0 < η`. (Step sizes are positive in the intended
reading; 1.7 says "for `η > 0`" explicitly, 4.2 does not.)

**D5 (4.1: `η_eff = η‖g‖^{p−1}` at `‖g‖ = 0`).** With `Real.rpow`, `0^{p−1} = 0` for `p ≠ 1` and
`0⁰ = 1`, while `etaEff = η·0^p/0 = 0` by `x/0 = 0`. So the HTMuon formula holds iff `‖g‖ ≠ 0` or
`p ≠ 1` (hypothesis of `Spec.etaEff_rpow`); for `p = 1`, `‖g‖ = 0` it would read `0 = η`. The main
identity 4.1 (`Spec.cNextVec_eq_cNext`) needs no hypothesis.

**D6 (4.2: `p < 1` is not needed for the first equivalences).** `Spec.theta_cNextVec_rpow_lt_iff`
and `…_gt_iff` hold for every real `p` (for `p = 1` they reduce to Deng's noise-free dichotomy
`η < η*₀`). `p < 1` is used only in the ray statement, to invert `x ↦ x^{1−p}`.

**D7 (conventions at a vanishing coefficient).** `Real.sign 0 = 0`, so `φ_f(0) = 0` even if
`f 0 ≠ 0` (Muon): a zero coefficient stays zero, and `ν_i = 0` there. All of 1.1–1.6 hold with
these conventions without any hypothesis on `c`; in 1.7–1.9 every hypothesis is stated on non-zero
coefficients only, as in the spec. (At the matrix level a zero singular value has no canonical
singular direction; that is the business of `Filter/MatrixMuon.lean`, not of this file.)

**D8 (meta-claim of 4.1).** "Every *pathwise* statement of Deng's one-step theory holds with `η`
replaced by `η_eff`" is formalized as the identity `cNextVec f η c ζ = P.cNext (etaEff f η c ζ) c ζ`
plus its two immediate transfers (`Spec.theta_cNextVec`, `Spec.fCompare_etaEff`). The word
*pathwise* matters: `η_eff` depends on the realised noise `ζ`, so the expectation-level statements
(`𝔼[f_t(η)] = p_t η² + q_t η`) do **not** transfer by substituting `η_eff`. Nothing of that kind is
claimed here.

## Relation to the paper (comparison only)

* For `f = id` the quadratic form 1.4 is the paper's Lemma "Quadratic form for step size condition"
  with `ζ = 0` (`Spec.fCompare_noiseFree_eq`), and 1.5 is the paper's
  `θ_{t+1} ≷ θ_t ⟺ f_t(η) ≷ 0` (tex 941–944), which needs `s_t, s_{t+1} > 0`.
* The paper's `q_t < 0` (tex 1105) needs `s^𝒟, s^ℬ > 0`; in this file that is the hypothesis of
  1.7, and `Spec.qF_id_nonpos` gives `q_t ≤ 0` unconditionally.
* Noise-free corollary of 1.9 versus the paper's bounds on `η*`: the lower bound
  `2/(λ_1+λ_{k+1})` is at least Theorem 7's `2 gap₁/(λ_1² − λ_d²)` and strictly larger unless the
  spectrum is two-level. The upper bound `2/(λ_k+λ_d)` is attained (e.g. `d = 2`,
  `exSpec_etaStar_noiseFree`), so no better state-independent upper bound exists without noise. It
  coincides with the corrected form of the paper's Theorem 8 found independently in
  `StepSize/EtaStarBounds.lean` (the main-text constant `(λ_1−λ_d)/(λ_kλ_1−λ_{k+1}λ_d)` of
  Theorem 8 is violated already for `λ = (2,1)`, `c = (1,1)`: `η* = 2/3 > 1/3`); that discussion
  belongs to the other file and is not repeated here.

## Notes for downstream files (`Filter/MuonHT.lean`)

* Inside `namespace SuspiciousAlignment.Spec` the identifier `id` resolves to the structure field
  `Spec.id` (index of `λ_d`). The identity filter must be written `_root_.id` there (outside the
  namespace plain `id` works). All `…_id` lemmas of this file are about `_root_.id`.
* Shapes of the hypotheses of 1.7–1.9 (copy them verbatim):
  `hD : 0 < P.sD c`, `hB : 0 < P.sB c`,
  `hnn : ∀ j ∈ P.B, c j ≠ 0 → 0 ≤ P.nu f c j` (1.7) / `∀ i ∈ P.D, c i ≠ 0 → 0 ≤ P.nu f c i` (1.8),
  `hord : ∀ i ∈ P.D, ∀ j ∈ P.B, c i ≠ 0 → c j ≠ 0 → P.nu f c j < P.nu f c i` (1.7; `<` reversed in
  1.8), bounds `∀ i ∈ P.D, c i ≠ 0 → aD ≤ P.nu f c i`, etc.
* Useful small lemmas: `Spec.nu_one` (`ν = 1/|c|`, by `rfl`), `Spec.cNextF_one`, `Spec.cNextF_apply`,
  `Spec.nu_nonneg`, `Spec.nu_of_eq_zero`, `Spec.momF_id`, `Spec.etaStarF_eq_double_sum`;
  helpers in `namespace FilterCoordinate` (take `P` explicitly): `exists_ne_zero_of_mom_pos`,
  `mom_pos_of_ne_zero`, `mom_smul`, `sD_smul`, `sB_smul`, `s_smul`, `qCoef_smul`,
  `pCoef_noiseFree_smul`, the pair-sum calculus `pairSum`, `pairSum_le_pairSum`,
  `pairSum_lt_pairSum`, `qF_eq_pairSum`, `pF_eq_pairSum`, `neg_qF_eq_pairSum`, the real-variable
  lemmas `quad_neg_iff`, `quad_pos_iff`, `quad_eq_zero_iff`, and the example spectrum `exSpec`
  (with `exSpec_B`, `exSpec_mom_D`, `exSpec_mom_B`, `exSpec_sD`, `exSpec_sB`).
* Names that exist elsewhere in the project with a different namespace: `Spec.mom_smul` /
  `Spec.theta_smul` in `Projected/LossThreshold.lean` versus `FilterCoordinate.mom_smul` here — no
  clash, but `open FilterCoordinate` together with `namespace Spec` makes `mom_smul` ambiguous if
  both files are imported; use the qualified names.
