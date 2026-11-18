# Fidelity note — `SuspiciousAlignment/StepSize/ThetaStarRate.lean`

Paper item: **Theorem 5 ("Asymptotic rate of θ\*_t")**, statement tex 443–457, proof tex 1260–1350
(uses the definition of θ\*_t from Theorem 4, tex 425–441).

> Under Assumption 1, let m := λ_k/λ_{k+1} > 1. There exist constants α, β > 0 such that
> 1 − β/m² ≤ θ\*_t ≤ 1 − α/m². In particular θ\*_t = 1 − Θ(1/m²).

Module `SuspiciousAlignment.StepSize.ThetaStarRate` builds, is `sorry`-free, and every main theorem
depends only on `propext`, `Classical.choice`, `Quot.sound`. It imports only `Mathlib` and
`SuspiciousAlignment.Defs`. Layer: exact finite-`d` algebra (θ\*_t is a deterministic function of
the spectrum, the noise bounds and `s_t`), plus two family-level (filter) corollaries.

## 1. Verdict in one paragraph

For one fixed problem and state the literal statement ("there exist α, β > 0") is trivially true and
is proved (`Spec.thetaStar_rate_exists`). The content is the dependence of the constants, and there
the paper is half right:

* **Lower bound θ\* ≥ 1 − β/m² — true and uniform**, with β = s_min/(ρ s_max), depending only on
  ρ and s_max/s_min, valid for every state (including x = 0), every spectrum, every finite d.
  But the paper's proof of it is wrong at every step, and the constant it names
  (β := ρ s_max/s_min) is the *reciprocal* of the right one and does not work.
* **Upper bound θ\* ≤ 1 − α/m² — true only with a state-dependent α_t**, namely
  α_t = 1 / (1 + (ρ s_max/s_min + s_t/(s_min (d−k))) (λ_1/λ_k)² (λ_{k+1}/λ_d)²).
  The paper asserts "there exists a fixed scalar α" without computing it. No α that is independent
  of s_t exists; with the state fixed and λ_{k+1} = Θ(1) the true rate is **m⁻⁴, not m⁻²**; and in
  the paper's own regime (Tr Σ bounded, d → ∞) θ\*_t → 1 at fixed m whenever s_t grows with d.
  So "θ\*_t = 1 − Θ(1/m²)" is **false as a uniform statement**
  (`thetaStar_rate_not_isTheta`); it is proved under the explicit side conditions that
  ρ s_max/s_min (above and below), s_t/(s_min (d−k)), λ_1/λ_k and λ_{k+1}/λ_d stay bounded
  (`thetaStar_rate_isTheta`), and the bound on s_t/(s_min (d−k)) cannot be dropped.

Assumption 1 is not used anywhere, and does not supply the needed bounds (see §5).

## 2. Table

Notation: a = s_min ψ_B, h = s_max ψ_D, M = s_t(λ_1² − λ_d²) (`Spec.aAux`, `Spec.hAux`,
`Spec.mAux`); β' = ρ s_max/s_min; ω_t = s_t/(s_min (d−k)); κ_D = λ_1/λ_k; κ_B = λ_{k+1}/λ_d.
All theorems assume `0 < N.smin` and nothing else unless stated.

| Paper item | Lean declaration | Status | Explanation |
|---|---|---|---|
| Thm 5, literal statement (tex 443–451) | `Spec.thetaStar_rate_exists` | hypotheses-added | ∃ α β > 0 with 1 − β/m² ≤ θ\* ≤ 1 − α/m². Added `0 < s_min` (without it `a = 0`, the "quadratic" is linear and `r0` is `x/0`). Assumption 1 dropped (unused). |
| Thm 5 with explicit constants | `Spec.thetaStar_rate` (and `Spec.thetaStar_rate_one_sub` in the form α_t/m² ≤ 1 − θ\* < β/m²) | strengthened | β = `Spec.thetaStarRateBeta` = s_min/(ρ s_max); α_t = `Spec.thetaStarRateAlpha` = 1/(1 + (β' + ω_t) κ_D² κ_B²). Lower bound on θ\* is strict. Both constants proved positive; α_t ≤ 1 (`thetaStarRateAlpha_le_one`). |
| Thm 5, "θ\* = 1 − Θ(1/m²)" (tex 452–455) | `thetaStar_rate_isTheta` | hypotheses-added | For any family of problems/states and any filter: if R₁ ≤ β' ≤ R₂ (R₁ > 0), ω_t ≤ Ω, κ_D ≤ K_D, κ_B ≤ K_B along the family then `(1 − θ*) =Θ (1/m²)`. Pointwise version with constants 1/(1 + (R₂+Ω) K_D² K_B²) and 1/R₁: `Spec.thetaStar_rate_uniform`. |
| Thm 5, "θ\* = 1 − Θ(1/m²)" as a uniform claim in m | `thetaStar_rate_not_isTheta`, `thetaStar_rate_fails_fixed_state` | paper-claim-false | A_n = diag(n+2, 1, 1), D = {1}, Σ = I, x = u_1: ρ, s_min, s_max, κ_D, κ_B, λ_{k+1}, ‖x‖ constant, m_n = n+2 → ∞, and 1 − θ\* < 2/(m²(m²−1)); so `¬ (1 − θ*) =Θ (1/m²)` and for every α > 0 the bound θ\* ≤ 1 − α/m² fails for all large m. |
| Thm 5 proof, "fixed scalar α" (tex 1334–1337) | `Spec.thetaStar_rate_alpha_not_uniform_in_state`, `Spec.thetaStar_rate_gt_of_energy_large`, `Spec.thetaStar_rate_energy_bound` | paper-claim-false | 1 − θ\* < s_min(d−k)/(s_t(m²−1)). For a fixed (A, Σ) and every α > 0 there is a state with θ\* > 1 − α/m² (any state with s_t ≥ s_min(d−k)m²/(α(m²−1))). α cannot be state/time independent. |
| Thm 5 proof, constant "β := ρ s_max/s_min" and conclusion "1 − β/m² ≤ θ\*" (tex 1322, 1346) | `thetaStar_rate_paper_beta_fails` | paper-claim-false | A = diag(2,1,1), D = {1}, Σ = I, x = 0: ρ = 1/2, m = 2, θ\* = 2/3 < 7/8 = 1 − β_paper/m². |
| (core estimate; replaces tex 1302–1337) | `Spec.thetaStar_rate_aux_sandwich` | extra | a/(M+h+a) ≤ 1 − θ\* < a/(M+h), and 1 − θ\* ≤ a/(a+h). Tight to within the additive `a` in the denominator. |
| (sharp spectral form) | `Spec.thetaStar_rate_sharp` | extra | 1/(1 + (β'+ω_t)(λ_1/λ_d)²) ≤ 1 − θ\* < 1/(β' m² + ω_t (m²−1)). For flat blocks (λ_1/λ_d)² = m², so the two sides differ by 1 + ω_t in the denominator. |
| m⁻⁴ regime | `Spec.thetaStar_rate_quartic` | extra | 1 − θ\* < C/(m²(m²−1)), C = s_min(d−k)/(λ_{k+1}² ‖P^D x_t‖²). C is free of λ_k: fixed state + λ_{k+1} = Θ(1) ⇒ rate m⁻⁴. |
| dependence on κ_D | `Spec.thetaStar_rate_cond_bound` | extra | 1 − θ\* ≤ ((d−k) s_min/s_max)/(κ_D² m²) for every state: α ≤ (d−k)(s_min/s_max)/κ_D². |
| paper's regime d → ∞, Tr Σ bounded | `Spec.thetaStar_rate_trace_bound` | extra | 1 − θ\* < Tr Σ/((1+ρ) s_t (m²−1)) with Tr Σ = Σ_i κ_i². If Tr Σ = O(1) and s_t → ∞ (e.g. ‖x_t‖² ≍ d), θ\* → 1 at fixed m. |
| Assumption 1, trajectory boundedness | `Spec.thetaStar_rate_of_bounded_state` | extra | If ‖x_t‖² ≤ C d then ω_t ≤ (1+ρ) C λ_1²/s_min and θ\* ≤ 1 − α_C/m² with α_C = 1/(1 + (β' + (1+ρ)Cλ_1²/s_min) κ_D² κ_B²). Still involves λ_1²/s_min. |
| Interpretation "as λ_k/λ_{k+1} → ∞, θ\*_t → 1" (tex 456) | `thetaStar_tendsto_one_of_gap` | hypotheses-added | For any family with β' ≥ R₁ > 0 and m → ∞ (any filter), θ\* → 1. No assumption on states. The paper leaves the lower bound on ρ s_max/s_min implicit. |
| Thm 4 facts needed here (r_{0,t} is the positive root, θ\* ∈ (0,1)) | `ThetaStarRate.auxQuad_r0`, `r0_pos`, `eq_r0_of_auxQuad_eq_zero`, `one_sub_thetaStar`, `thetaStar_mem_Ioo`, `r0_le`, `lt_one_add_r0`, `hAux_div_aAux_le_r0`, `r0_of_s_eq_zero`, `one_sub_thetaStar_of_s_eq_zero` | exact (helpers) | Proved locally in `namespace SuspiciousAlignment.ThetaStarRate` because the Theorem 4 file is written concurrently. `Spec.r0` (quadratic formula) is a root, is positive, is the unique positive root; 1 − θ\* = 1/(1+r0); (M+h)/a − 1 < r0 ≤ (M+h)/a; h/a ≤ r0 with equality at x = 0. |

Non-vacuity: the only hypotheses are `0 < N.smin` (and `0 < P.s c` / `0 < P.normSqD c` for three
"extra" bounds). A concrete instance (`ThetaStarRate.gapSpec 2`, `unitNoise`, `e1`) is given as an
`example`; the uniform theorem is instantiated with `le_rfl` bounds inside
`thetaStar_rate_of_bounded_state`. No statement relies on `x/0 = 0`.

## 3. The correct mathematics

With u = 1 + r_{0,t} the quadratic of Theorem 4 becomes a u² − (a + M + h) u + M = 0, and
1 − θ\* = 1/u. Evaluating Q(r) = a r² + (a − M − h) r − h:

* Q((M+h)/a) = M ≥ 0, so r0 ≤ (M+h)/a;
* Q((M+h)/a − 1) = −h < 0, so r0 > (M+h)/a − 1;
* Q(h/a) = −M h/a ≤ 0, so r0 ≥ h/a (equality iff M = 0; then Q = (a r − h)(r + 1)).

(The sign transfer uses Q(x)·r0 = (x − r0)(a x r0 + h), `ThetaStarRate.quad_factor`.) Hence

    a/(M + h + a)  ≤  1 − θ*  <  a/(M + h),        1 − θ*  ≤  a/(a + h).

So 1 − θ\* is, up to the additive `a`, exactly a/(M+h), i.e.

    (M + h)/a = (s_max/s_min)·ψ_D/ψ_B  +  s_t (λ_1² − λ_d²)/(s_min ψ_B).

With the *correct* block bounds k λ_k² ≤ ψ_D ≤ k λ_1², (d−k) λ_d² ≤ ψ_B ≤ (d−k) λ_{k+1}²:

    β' m² + ω_t (m² − 1)  ≤  (M + h)/a  ≤  (β' + ω_t) (λ_1/λ_d)²  =  (β' + ω_t) κ_D² κ_B² m².

This gives `thetaStar_rate_sharp` and, using m² ≥ 1 once, Theorem 5 with
β = 1/β' = s_min/(ρ s_max) and α_t = 1/(1 + (β' + ω_t) κ_D² κ_B²).

Which quantities the constants depend on:

| quantity | enters β (lower bound on θ\*) | enters α (upper bound on θ\*) | removable? |
|---|---|---|---|
| ρ s_max/s_min | yes (β = its reciprocal) | yes | no |
| ω_t = s_t/(s_min(d−k)) (state/time dependent, not scale invariant) | no | yes | **no** (`thetaStar_rate_alpha_not_uniform_in_state`) |
| κ_D = λ_1/λ_k | no | yes | no in general (`thetaStar_rate_cond_bound`); it is a worst-case proxy for ψ_D/(k λ_k²) |
| κ_B = λ_{k+1}/λ_d | no | yes | worst-case proxy for (d−k) λ_{k+1}²/ψ_B ≤ min(κ_B², d−k); matters when most of the bulk is far below λ_{k+1} |
| λ_{k+1} (scale) | no | only through s_t | – |

The scale-invariant "natural" variable is ψ_D/ψ_B (mean-square block eigenvalues), not m; m² only
brackets it: ρ m² ≤ ψ_D/ψ_B ≤ ρ κ_D² κ_B² m².

## 4. Audit of the paper's proof (tex 1275–1350), step by step

1. tex 1302–1309: "λ_{k+1}² ≤ λ_i² ≤ λ_k² for i ∈ D, and λ_{k+1}² ≤ λ_i² for i ∈ B".
   **Both are reversed.** Since λ_1 ≥ … ≥ λ_k > λ_{k+1} ≥ … ≥ λ_d: λ_k² ≤ λ_i² ≤ λ_1² on D and
   λ_d² ≤ λ_i² ≤ λ_{k+1}² on B. They hold only for flat blocks.
2. tex 1310–1316: "ℓ_B ≤ ψ_B ≤ u_B and ρ ℓ_B ≤ ψ_D ≤ ρ u_B" with ℓ_B = (d−k)λ_{k+1}²,
   u_B = (d−k)λ_k². True parts: ψ_B ≤ ℓ_B (≤ u_B) and ψ_D ≥ ρ u_B (≥ ρ ℓ_B)
   (`ThetaStarRate.psiB_le`, `le_psiD`). **False parts:** ℓ_B ≤ ψ_B and ψ_D ≤ ρ u_B.
   Numeric counterexample: λ = (3, 2, 1, 0.5), k = 2 (ρ = 1): ψ_D = 13 > ρ u_B = 8 and
   ψ_B = 1.25 < ℓ_B = 2.
3. tex 1322–1327: "r0 ≥ (s_max ρ ℓ_B − s_min u_B)/(s_min u_B) = β/m² − 1", β := ρ s_max/s_min.
   True but vacuous (it is negative as soon as m² > β); it throws away a factor m⁴. The correct
   statement is r0 ≥ h/a ≥ β m² (`hAux_div_aAux_le_r0`, `le_aux_ratio`).
4. tex 1328–1333: "θ\* ≥ (β/m² − 1)/(1 + (β/m² − 1)) = 1 − 1/(β/m²)". The algebra is right and
   gives θ\* ≥ 1 − m²/β — a bound that *deteriorates* as m grows and is negative for m² > β.
5. tex 1344–1348: "which gives 1 − β/m² ≤ θ\*". **Non sequitur** (1 − m²/β is not 1 − β/m²), and
   with the paper's β it is **false**: d = 11, k = 1, λ = (2, 1, …, 1), Σ = I, x = 0 gives ρ = 0.1,
   m = 2, θ\* = 2/7 ≈ 0.2857 but 1 − β/m² = 0.975. Formal version (d = 3):
   `thetaStar_rate_paper_beta_fails` (θ\* = 2/3 < 7/8). The correct constant is 1/β.
6. tex 1334–1337: "since a ≥ s_min ℓ_B, h ≤ s_max ρ u_B and m^aux ≤ s_t(λ_1² − λ_d²), there exists a
   fixed scalar α > 0 such that r0 ≤ α m²". The first two inequalities are the false ones of
   step 2 (correct: a ≥ s_min (d−k) λ_d², h ≤ s_max k λ_1²). Even granting them,
   (M+h)/a ≤ β m² + s_t(λ_1² − λ_d²)/(s_min (d−k) λ_{k+1}²), and the last term is not ≤ const·m²
   with a constant independent of s_t; "fixed" is unjustified. Correct:
   r0 ≤ (β' + ω_t) κ_D² κ_B² m² (`r0_le`, `aux_ratio_le`).
7. tex 1338–1348: from r0 ≤ α m², θ\* ≤ 1 − 1/(1 + α m²) (correct), "which gives θ\* ≤ 1 − α/m²":
   only with a *different* constant, 1/(1+α) (uses m ≥ 1). Minor.

The statement "are all nonnegative scalars" (tex 1290) is fine, but a > 0 (i.e. s_min > 0) is needed
and never stated.

## 5. Assumptions

* **Used by the Lean proofs:** `0 < s_min` only (plus the structural facts in `Spec`, `Noise`).
* **Assumption 1 (tex 367–384):** not used. Its items do not give the bounds the Θ-claim needs:
  * *Block proportion* fixes ρ — fine.
  * *Noise spectral bounds* is "Tr Σ ∈ (0, ∞)". With d → ∞ this forces s_min ≤ Tr Σ/d → 0, so
    ω_t = s_t/(s_min(d−k)) ≥ (1+ρ) s_t/Tr Σ. `Spec.thetaStar_rate_trace_bound`:
    1 − θ\* < Tr Σ/((1+ρ) s_t (m²−1)). If s_t grows with d (generic when ‖x_t‖² ≍ d, which
    "trajectory boundedness" allows) then θ\*_t → 1 at fixed m and the "decrease region"
    (θ\*_t, 1) of Theorem 4 is asymptotically empty. Also s_max/s_min is not controlled.
  * *Trajectory boundedness* (‖x_t‖²/d bounded) gives s_t/(d−k) ≤ (1+ρ) C λ_1²
    (`thetaStar_rate_of_bounded_state`), which is bounded only if λ_1 is; if m → ∞ through
    λ_k → ∞ this grows like m².
* **Is λ_{k+1} = Θ(1) needed?** The opposite: with λ_{k+1} = Θ(1), λ_k → ∞ and a fixed state the
  rate is m⁻⁴. The m⁻² rate is the regime "λ_1 = O(1), λ_{k+1} = λ_k/m → 0" (bulk shrinking) with
  s_t/(s_min(d−k)) bounded and bounded within-block condition numbers. θ\* is not scale invariant in
  A (s_t and M scale), whereas m is; any correct statement must fix a normalisation, and
  ω_t is that normalisation.
* **Is boundedness of s_t needed?** Yes, from above, relative to s_min(d−k), for the upper bound
  on θ\*. Not from below: the lower bound on θ\* holds for every state including x_t = 0.

## 6. Numerical evidence (python3 / numpy, double precision)

All inequalities of the file were checked on 2·10⁴ random instances (d ≤ 8, random spectra,
states, noise bounds) — no violation. Selected values, θ\* computed from the quadratic formula:

m⁻⁴ regime — λ = (μ, 1, 1), D = {1}, Σ = I, x = u_1 (`thetaStar_rate_fails_fixed_state`):

| μ = m | 1 − θ\* | (1 − θ\*)·m² | (1 − θ\*)·m⁴ | bound 2/(m²(m²−1)) |
|---|---|---|---|---|
| 2 | 1.2085e-01 | 0.4834 | 1.9336 | 1.6667e-01 |
| 4 | 7.8087e-03 | 0.1249 | 1.9990 | 8.3333e-03 |
| 8 | 4.8828e-04 | 0.03125 | 2.0000 | 4.9603e-04 |
| 16 | 3.0518e-05 | 0.0078125 | 2.0000 | 3.0637e-05 |
| 32 | 1.9073e-06 | 0.0019531 | 2.0000 | 1.9092e-06 |

Dependence on s_t — λ = (2, 1), Σ = I, x = (t, 0), m = 2 fixed:

| t | s_t | (1 − θ\*)·m² |
|---|---|---|
| 0 | 0 | 8.000e-01 |
| 1 | 4 | 2.460e-01 |
| 10 | 400 | 3.322e-03 |
| 100 | 4·10⁴ | 3.333e-05 |
| 1000 | 4·10⁶ | 3.333e-07 |

Paper's regime — Σ = I/d (Tr Σ = 1), c_i = 1, λ = (2,…,2,1,…,1), ρ = 1, m = 2 fixed:

| d | θ\* | (1 − θ\*)·m² |
|---|---|---|
| 2 | 0.97069234 | 1.172e-01 |
| 20 | 0.99671067 | 1.316e-02 |
| 200 | 0.99966711 | 1.332e-03 |
| 2000 | 0.99996667 | 1.333e-04 |
| 20000 | 0.99999667 | 1.333e-05 |

Dependence on within-block conditioning — λ = (2K, 2, 1, 1/K), k = 2, Σ = I, x = 0, m = 2, ρ = 1:

| K | (1 − θ\*)·m² |
|---|---|
| 1 | 8.0000e-01 |
| 2 | 2.3529e-01 |
| 4 | 6.1538e-02 |
| 8 | 1.5564e-02 |
| 16 | 3.9024e-03 |

Reproduce:

```python
import numpy as np
def one_minus_theta_star(lam, k, c, smin, smax):
    lam, c = np.asarray(lam, float), np.asarray(c, float)
    a = smin*np.sum(lam[k:]**2); h = smax*np.sum(lam[:k]**2)
    M = np.sum(lam**2*c**2)*(lam[0]**2 - lam[-1]**2); b = a - M - h
    r0 = (-b + np.sqrt(b*b + 4*a*h))/(2*a)
    return 1/(1 + r0)
print(one_minus_theta_star([8, 1, 1], 1, [1, 0, 0], 1, 1) * 8**4)       # 2.0000  (m^-4)
print(1 - one_minus_theta_star([2] + [1]*10, 1, [0]*11, 1, 1))          # 0.2857 < 0.975
```

## 7. Notes for downstream files

* The constants live in `Spec`: `P.thetaStarRateAlpha N c`, `P.thetaStarRateBeta N`. Everything
  else file-specific is in `namespace SuspiciousAlignment.ThetaStarRate` (helper lemmas, the
  example family `gapSpec μ hμ : Spec (Fin 3)`, `gapSpecNat`, `unitNoise`, `e1`). The `gapSpec_*`
  and `unitNoise_*` evaluation lemmas are tagged `@[simp]`.
* The helper facts about `r0`/`thetaStar` duplicate what the Theorem 4 file will prove; they are
  deliberately not in `namespace Spec` to avoid name clashes.
* `Spec.thetaStar_rate_aux_sandwich` (third conjunct) gives the quantitative form of Theorem 4's
  remark "θ\*_t → 1 as ψ_D/ψ_B → ∞": 1 − θ\* ≤ 1/(1 + (s_max/s_min) ψ_D/ψ_B).
* `Defs.lean` was used unchanged; no definition there was found to be unfaithful for this item.
  (`Spec.normSq` does not take `P`, so it must be written `Spec.normSq c`, not `P.normSq c`.)
