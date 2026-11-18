# Fidelity note — `SuspiciousAlignment/StepSize/ThetaStarRate.lean`

Paper item: **Theorem 5 ("Asymptotic rate of θ\*_t")**, statement tex 443–457, proof tex 1260–1350
(uses the definition of θ\*_t from Theorem 4, tex 425–441, and Assumption 1, tex 367–384).

> Under Assumption 1, let m := λ_k/λ_{k+1} > 1. There exist constants α, β > 0 such that
> 1 − β/m² ≤ θ\*_t ≤ 1 − α/m². In particular θ\*_t = 1 − Θ(1/m²).

Module `SuspiciousAlignment.StepSize.ThetaStarRate` builds, is `sorry`-free, and every main theorem
depends only on `propext`, `Classical.choice`, `Quot.sound`. It imports only `Mathlib` and
`SuspiciousAlignment.Defs`. Layers: exact finite-`d` algebra (θ\*_t is a deterministic function of
the spectrum, the noise bounds and `s_t`), family-level (filter) corollaries, and sequences of
problems with `d → ∞` inside the regime of Assumption 1.

Status of this note: revised after review round 1 (fix round 1). What changed is listed in §8.

## 1. Verdict

For one fixed problem and state the literal statement ("there exist α, β > 0") is trivially true and
is proved (`Spec.thetaStar_rate_exists`). The content is the dependence of the constants.

* **Lower bound θ\* ≥ 1 − β/m² — true and uniform**, with β = s_min/(ρ s_max), depending only on
  ρ and s_max/s_min, valid for every state (including x = 0), every spectrum, every finite d.
  The paper's derivation yields only θ\* ≥ 1 − m²/β (valid but useless: it worsens as m grows);
  the final step from there to 1 − β/m² ≤ θ\* is a non sequitur, and with the β the paper names
  (β := ρ s_max/s_min, the *reciprocal* of the right constant) the conclusion is false.
* **Upper bound θ\* ≤ 1 − α/m² — true only with a state- and spectrum-dependent α_t**, namely
  α_t = 1 / (1 + (ρ s_max/s_min + s_t/(s_min (d−k))) (λ_1/λ_k)² (λ_{k+1}/λ_d)²).
  The paper asserts "there exists a fixed scalar α" without computing it.
* **Inside the regime of Assumption 1 (the theorem's stated hypothesis) the upper bound, and hence
  "θ\* = 1 − Θ(1/m²)", is false with dimension-free constants.** Three formal sequences of problems
  with d = 2(n+2) → ∞, k = n+2, ρ = 1, Σ = I/d (Tr Σ = 1), all satisfying the formal predicate
  `ThetaStarRate.Assumption1`:
  1. `thetaStar_rate_fails_under_assumption1` — A = diag(2,…,2,1,…,1), x = (1,…,1): all block
     moments are constant, m = 2, yet 1 − θ\* < 1/(24(n+2)) → 0.
     Mechanism: Tr Σ bounded forces s_min ≤ Tr Σ/d, so s_t/(s_min(d−k)) ≥ (1+ρ) s_t/Tr Σ → ∞.
  2. `thetaStar_rate_not_isTheta_under_assumption1` — A = diag(1,…,1,ε_n,…,ε_n), ε_n = 1/(n+2),
     x = (1,…,1): m_n = n+2 → ∞ and 1 − θ\* is not Θ(1/m²) (it is o(1/m²)).
     For the *same* (A_n, Σ_n) with x = 0 the Θ(1/m²) rate does hold
     (`thetaStar_rate_isTheta_under_assumption1_zero_state`): under Assumption 1 the truth of the
     claim depends on the scale of the state.
  3. `thetaStar_rate_fails_under_assumption1_all_states` — A = diag(2,…,2,1,ε_n,…,ε_n): m = 2,
     and 1 − θ\* ≤ ψ_B/ψ_D ≤ 1/(2(n+2)) for **every** state and **every** noise with s_min > 0.
     Mechanism: the bulk mean square ψ_B/(d−k) → 0 (limit λ_{B,2} = 0, which Assumption 1 allows)
     while λ_{k+1} = 1; the paper's step "ℓ_B = |B| λ_{k+1}² ≤ ψ_B" is false.
  The general statement behind 1 and 2 is `thetaStar_rate_isLittleO_of_trace_bounded` /
  `thetaStar_rate_isLittleO_of_assumption1`: bounded Tr Σ, m ≥ m₀ > 1 and s_t → ∞ imply
  1 − θ\* = o(1/m²).
* **At fixed d** (outside Assumption 1) the uniform-in-m reading also fails: with the state fixed
  and λ_{k+1} = Θ(1), λ_k → ∞, the true rate is m⁻⁴ (`thetaStar_rate_not_isTheta`,
  `thetaStar_rate_fails_fixed_state`, `Spec.thetaStar_rate_quartic`).
* **Positive result.** `1 − θ* =Θ (1/m²)` is proved for any family along which (eventually)
  ρ s_max/s_min (above and below), s_t/(s_min (d−k)), λ_1/λ_k and λ_{k+1}/λ_d stay bounded
  (`thetaStar_rate_isTheta`). These hypotheses are sufficient; §3 records which are known to be
  necessary.
* **The interpretation "θ\*_t → 1 as λ_k/λ_{k+1} → ∞" is correct** and, under Assumption 1, needs
  nothing beyond s_min > 0 (`thetaStar_tendsto_one_of_assumption1`).

Assumption 1 is not used by any of the positive theorems, and it does not supply the bounds the
Θ-claim needs (see §5).

## 2. Table

Notation: a = s_min ψ_B, h = s_max ψ_D, M = s_t(λ_1² − λ_d²) (`Spec.aAux`, `Spec.hAux`,
`Spec.mAux`); β' = ρ s_max/s_min; ω_t = s_t/(s_min (d−k)); κ_D = λ_1/λ_k; κ_B = λ_{k+1}/λ_d.
All theorems assume `0 < N.smin` and nothing else unless stated.

| Paper item | Lean declaration | Status | Explanation |
|---|---|---|---|
| Thm 5, literal statement (tex 443–451) | `Spec.thetaStar_rate_exists` | hypotheses-added | ∃ α β > 0 with 1 − β/m² ≤ θ\* ≤ 1 − α/m², for one problem and state (trivial content). Added `0 < s_min` (without it `a = 0`, the "quadratic" is linear and `r0` is `x/0`). Assumption 1 dropped (unused). |
| Thm 5 with explicit constants | `Spec.thetaStar_rate` (and `Spec.thetaStar_rate_one_sub` in the form α_t/m² ≤ 1 − θ\* < β/m²) | β: strengthened (explicit, state-independent, strict). α: **weakened** relative to the paper's intended fixed scalar — α_t depends on the state and the spectrum; see the paper-claim-false rows | β = `Spec.thetaStarRateBeta` = s_min/(ρ s_max); α_t = `Spec.thetaStarRateAlpha` = 1/(1 + (β' + ω_t) κ_D² κ_B²). Both proved positive; α_t ≤ 1 (`thetaStarRateAlpha_le_one`). Against the literal pointwise existential the statement is a strengthening. |
| Thm 5, "θ\* = 1 − Θ(1/m²)" (tex 452–455) — positive form | `thetaStar_rate_isTheta`; pointwise `Spec.thetaStar_rate_uniform` | hypotheses-added | For any family of problems/states and any filter `l`: if eventually along `l` R₁ ≤ β' ≤ R₂ (R₁ > 0), ω_t ≤ Ω, κ_D ≤ K_D, κ_B ≤ K_B then `(1 − θ*) =Θ[l] (1/m²)`, constants 1/(1 + (R₂+Ω) K_D² K_B²) and 1/R₁. Non-vacuous with m → ∞: `thetaStar_rate_isTheta_gapSpecNat_zero` (d = 3, A_n = diag(n+2,1,1), Σ = I, x = 0), `thetaStar_rate_isTheta_under_assumption1_zero_state` (inside Assumption 1). |
| **Thm 5 under Assumption 1 as stated (d, k → ∞): upper bound with a dimension-free α** | `thetaStar_rate_fails_under_assumption1` | **paper-claim-false** | A_n = diag(2,…,2,1,…,1) on `Fin (n+2) ⊕ Fin (n+2)`, Σ_n = I/d, x_n = (1,…,1). `Assumption1` holds (‖x‖²/d = 1, ρ = 1, moments 2^p and 1, Tr Σ = 1), m = 2 for all n, 1 − θ\* < 1/(24(n+2)); ∀ α > 0 ∃ n₀ ∀ n ≥ n₀: θ\* > 1 − α/m². |
| **Thm 5 under Assumption 1: "θ\* = 1 − Θ(1/m²)" with m → ∞** | `thetaStar_rate_not_isTheta_under_assumption1` | **paper-claim-false** | A_n = diag(1,…,1,ε_n,…,ε_n), ε_n = 1/(n+2), Σ_n = I/d, x_n = (1,…,1). `Assumption1` holds (bulk moment limits 0), m_n = n+2 → ∞, `¬ (1 − θ*) =Θ[atTop] (1/m²)`. |
| **Thm 5 under Assumption 1: failure for all states and noises** | `thetaStar_rate_fails_under_assumption1_all_states`, `Spec.thetaStar_rate_psi_bound` | **paper-claim-false** | A_n = diag(2,…,2,1,ε_n,…,ε_n). `Assumption1` holds (e.g. Σ = I/d, x = 0; bulk moment limits 0), m = 2, and ∀ N with s_min > 0, ∀ c: 1 − θ\* ≤ ψ_B/ψ_D ≤ 1/(2(n+2)); ∀ α > 0 ∃ n₀ ∀ n ≥ n₀ ∀ N c: θ\* > 1 − α/m². |
| Thm 5 under Assumption 1: general mechanism | `thetaStar_rate_isLittleO_of_trace_bounded`, `thetaStar_rate_fails_of_trace_bounded`, `thetaStar_rate_not_isTheta_of_trace_bounded`, `thetaStar_rate_isLittleO_of_assumption1`, `Spec.thetaStar_rate_trace_bound` | paper-claim-false (general form) | Any family with (eventually) Tr Σ ≤ T, m ≥ m₀ > 1, s_min > 0 and s_t → ∞ has 1 − θ\* = o(1/m²); so ∀ α > 0 eventually θ\* > 1 − α/m², and (non-trivial filter) not Θ(1/m²). Pointwise: 1 − θ\* < Tr Σ/((1+ρ) s_t (m²−1)). |
| Thm 5, "θ\* = 1 − Θ(1/m²)" read uniformly in m **at fixed d (outside Assumption 1)** | `thetaStar_rate_not_isTheta`, `thetaStar_rate_fails_fixed_state`, `Spec.thetaStar_rate_quartic` | paper-claim-false (fixed-d reading only) | A_n = diag(n+2, 1, 1), D = {1}, Σ = I, x = u_1: ρ, s_min, s_max, κ_D, κ_B, λ_{k+1}, ‖x‖ constant, m_n = n+2 → ∞, 1 − θ\* < 2/(m²(m²−1)). **This family has d = 3, k = 1 fixed and λ_k → ∞, so it violates Assumption 1** (d, k → ∞; block moments bounded ⇒ λ_k = O(1)); it refutes only the reading "constants independent of m" at fixed d. The m⁻⁴ mechanism (M ∼ m⁴) cannot occur under Assumption 1. |
| Thm 5 proof, "fixed scalar α" (tex 1334–1337) | `Spec.thetaStar_rate_alpha_not_uniform_in_state`, `Spec.thetaStar_rate_gt_of_energy_large`, `Spec.thetaStar_rate_energy_bound`, `Spec.thetaStar_rate_of_bounded_state` | paper-claim-false (with qualifier) | 1 − θ\* < s_min(d−k)/(s_t(m²−1)). For a fixed (A, Σ) and every α > 0 there is a state with θ\* > 1 − α/m² (any state with s_t ≥ s_min(d−k)m²/(α(m²−1))). **Qualifier:** this uses arbitrarily large states at fixed d. Over a bounded set ‖x_t‖² ≤ C d of states of one fixed problem a state- and time-independent α_C exists (`thetaStar_rate_of_bounded_state`), but it involves C λ_1²/s_min; under Assumption 1, λ_1²/s_min ≥ λ_1² d/Tr Σ → ∞, which is the real obstruction (formal: the Assumption-1 rows above). |
| Thm 5 proof, constant "β := ρ s_max/s_min" and conclusion "1 − β/m² ≤ θ\*" (tex 1322, 1346) | `thetaStar_rate_paper_beta_fails` | paper-claim-false | A = diag(2,1,1), D = {1}, Σ = I, x = 0: ρ = 1/2, m = 2, θ\* = 2/3 < 7/8 = 1 − β_paper/m². |
| Thm 5 proof, "ℓ_B := \|B\| λ_{k+1}² ≤ ψ_B" (tex 1312–1315), used as "a ≥ s_min ℓ_B" (tex 1334) | `thetaStar_rate_paper_psiB_bound_fails` | paper-claim-false | For A_n = diag(2,…,2,1,ε_n,…,ε_n): ψ_B < (d−k) λ_{k+1}² for every n (n = 0: 5/4 < 2). The other false half of that step (ψ_D ≤ ρ u_B = k λ_k²) is refuted numerically only (§4, step 2). |
| (core estimate; replaces tex 1302–1337) | `Spec.thetaStar_rate_aux_sandwich` | extra | a/(M+h+a) ≤ 1 − θ\* < a/(M+h), and 1 − θ\* ≤ a/(a+h). Tight to within the additive `a` in the denominator. |
| (sharp spectral form) | `Spec.thetaStar_rate_sharp` | extra | 1/(1 + (β'+ω_t)(λ_1/λ_d)²) ≤ 1 − θ\* < 1/(β' m² + ω_t (m²−1)). For flat blocks (λ_1/λ_d)² = m², so the two sides differ by 1 + ω_t in the denominator. |
| dependence on κ_D | `Spec.thetaStar_rate_cond_bound` | extra | 1 − θ\* ≤ ((d−k) s_min/s_max)/(κ_D² m²) for every state: α ≤ (d−k)(s_min/s_max)/κ_D². (Informative when κ_D² > d−k, e.g. along families with bounded d−k.) |
| dependence on the block mean squares | `Spec.thetaStar_rate_psi_bound` | extra | 1 − θ\* ≤ s_min ψ_B/(s_max ψ_D) ≤ ψ_B/ψ_D for every state; so α ≤ m² ψ_B/ψ_D = (1/ρ)·(ψ_B/((d−k)λ_{k+1}²))/(ψ_D/(kλ_k²)). |
| Assumption 1, trajectory boundedness | `Spec.thetaStar_rate_of_bounded_state` | extra | If ‖x_t‖² ≤ C d then ω_t ≤ (1+ρ) C λ_1²/s_min and θ\* ≤ 1 − α_C/m² with α_C = 1/(1 + (β' + (1+ρ)Cλ_1²/s_min) κ_D² κ_B²). Still involves λ_1²/s_min. |
| Interpretation "as λ_k/λ_{k+1} → ∞, θ\*_t → 1" (tex 456) | `thetaStar_tendsto_one_of_assumption1` (under `Assumption1`), `thetaStar_tendsto_one_of_gap_of_rho`, `thetaStar_tendsto_one_of_gap` | hypotheses-added (only `0 < s_min`, eventually) | For any family with (eventually) ρ ≥ ρ₀ > 0 and m → ∞, θ\* → 1; no assumption on states. Under Assumption 1's "block proportion" item ρ is a fixed constant, so the hypothesis is automatic: β' = ρ s_max/s_min ≥ ρ because s_max ≥ s_min. The more general `…_of_gap` takes β' ≥ R₁ > 0. |
| Assumption 1 (tex 367–384) | `ThetaStarRate.Assumption1` (local predicate), instances `assumption1_asp1Spec`, `assumption1_asp1GapSpec`, `assumption1_asp1SpikeSpec`, `assumption1_blockSpec` | equivalent-reformulation (of an informal assumption) | For a sequence (P_n, N_n, c_n): card → ∞, \|D\| → ∞; ∃ C, eventually ‖x‖² ≤ C d; ∃ ρ₀ > 0, ρ_n = ρ₀ for all n; for p ∈ {2,3,4,6,8}: (1/k)Σ_D λ^p → L_D ∈ (0,∞), (1/(d−k))Σ_B λ^p → L_B ∈ [0,∞); ∃ T, 0 < Tr Σ_n ≤ T. See §5 for the reading choices. |
| Thm 4 facts needed here (r_{0,t} is the positive root, θ\* ∈ (0,1)) | `ThetaStarRate.auxQuad_r0`, `r0_pos`, `eq_r0_of_auxQuad_eq_zero`, `one_sub_thetaStar`, `thetaStar_mem_Ioo`, `r0_le`, `lt_one_add_r0`, `hAux_div_aAux_le_r0`, `r0_of_s_eq_zero`, `one_sub_thetaStar_of_s_eq_zero` | exact (helpers; `0 < s_min` added) | Proved locally in `namespace SuspiciousAlignment.ThetaStarRate` because the Theorem 4 file is written concurrently. `Spec.r0` (quadratic formula) is a root, is positive, is the unique positive root; 1 − θ\* = 1/(1+r0); (M+h)/a − 1 < r0 ≤ (M+h)/a; h/a ≤ r0 with equality at x = 0. |

Non-vacuity. The only hypotheses of the finite-d theorems are `0 < N.smin` (and `0 < P.s c` /
`0 < P.normSqD c` for three "extra" bounds); a concrete instance (`ThetaStarRate.gapSpec 2`,
`unitNoise`, `e1`) is given as an `example`. The family theorem `thetaStar_rate_isTheta` is
instantiated on two families with m → ∞ (rows above). `ThetaStarRate.Assumption1` has three proved
instances. `thetaStar_rate_isLittleO_of_trace_bounded` is instantiated in
`thetaStar_rate_not_isTheta_under_assumption1`. No statement relies on `x/0 = 0`.

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

Which quantities the constants depend on, and what is known about the *necessity* of each bound
in `thetaStar_rate_isTheta` (the hypotheses there are sufficient; "needed" below means that
(1 − θ\*)·m² leaves every compact subset of (0, ∞) along suitable families when the bound is
dropped; the Lean statement showing it is cited, and where there is none this is said):

| quantity | enters β (lower bound on θ\*) | enters α (upper bound on θ\*) | is the bound needed? |
|---|---|---|---|
| β' = ρ s_max/s_min, upper bound R₂ | yes (β = 1/β') | yes | needed: (1 − θ\*) m² < 1/β' always (`Spec.thetaStar_rate`) |
| β', lower bound R₁ | yes | no | needed for the O(1/m²) direction, by the exact formula 1 − θ\* = 1/(1 + β' m²) at x = 0 with flat blocks (from `one_sub_thetaStar_of_s_eq_zero`; the necessity itself is not stated as a Lean theorem); automatic under Assumption 1 since β' ≥ ρ |
| ω_t = s_t/(s_min(d−k)) (state/time dependent, not scale invariant) | no | yes | **needed** (`Spec.thetaStar_rate_energy_bound`; fixed d: `thetaStar_rate_fails_fixed_state`; inside Assumption 1: `thetaStar_rate_fails_under_assumption1`, `thetaStar_rate_isLittleO_of_trace_bounded`) |
| κ_B = λ_{k+1}/λ_d | no | yes | **needed along d → ∞** (`thetaStar_rate_fails_under_assumption1_all_states`: β' = 1, ω_t = 0, κ_D = 1, m = 2 fixed, κ_B = n+2 → ∞ and (1 − θ\*) m² ≤ 2/(n+2)). It is a worst-case proxy for (d−k) λ_{k+1}²/ψ_B ≤ min(κ_B², d−k), so at fixed d dropping it costs at most a factor d−k |
| κ_D = λ_1/λ_k | no | yes | needed along families with bounded (d−k) s_min/s_max (`Spec.thetaStar_rate_cond_bound`); it is a worst-case proxy for ψ_D/(k λ_k²) and for the factor λ_1² in M. Not shown necessary in general (when κ_D² ≤ d−k the bound of `cond_bound` is vacuous) |
| λ_{k+1} (scale) | no | only through s_t | – |

The scale-invariant "natural" variable is ψ_D/ψ_B (mean-square block eigenvalues), not m; m² only
brackets it: ρ m² ≤ ψ_D/ψ_B ≤ ρ κ_D² κ_B² m². Under Assumption 1 with λ_{B,2} > 0 one has
ψ_D/ψ_B → ρ λ_{D,2}/λ_{B,2}; at x = 0 with isotropic noise 1 − θ\* = ψ_B/(ψ_B + ψ_D) exactly
(`ThetaStarRate.one_sub_thetaStar_of_s_eq_zero`).

## 4. Audit of the paper's proof (tex 1275–1350), step by step

1. tex 1302–1309: "λ_{k+1}² ≤ λ_i² ≤ λ_k² for i ∈ D, and λ_{k+1}² ≤ λ_i² for i ∈ B".
   **Both are reversed.** Since λ_1 ≥ … ≥ λ_k > λ_{k+1} ≥ … ≥ λ_d: λ_k² ≤ λ_i² ≤ λ_1² on D and
   λ_d² ≤ λ_i² ≤ λ_{k+1}² on B. They hold only for flat blocks.
2. tex 1310–1321: "ℓ_B ≤ ψ_B ≤ u_B and ρ ℓ_B ≤ ψ_D ≤ ρ u_B" with ℓ_B = (d−k)λ_{k+1}²,
   u_B = (d−k)λ_k². True parts: ψ_B ≤ ℓ_B (≤ u_B) and ψ_D ≥ ρ u_B (≥ ρ ℓ_B)
   (`ThetaStarRate.psiB_le`, `le_psiD`). **False parts:** ℓ_B ≤ ψ_B and ψ_D ≤ ρ u_B.
   Formal counterexample for the first: `thetaStar_rate_paper_psiB_bound_fails`
   (A = diag(2,…,2,1,ε,…,ε); n = 0 gives ψ_B = 5/4 < ℓ_B = 2). Numeric counterexample for both:
   λ = (3, 2, 1, 0.5), k = 2 (ρ = 1): ψ_D = 13 > ρ u_B = 8 and ψ_B = 1.25 < ℓ_B = 2. (The second
   false half has no Lean counterexample: all example spectra of this file have a flat dominant
   block.)
3. tex 1322–1327: "r0 ≥ (s_max ρ ℓ_B − s_min u_B)/(s_min u_B) = β/m² − 1", β := ρ s_max/s_min.
   **Valid**: it uses only h ≥ s_max ρ ℓ_B and a ≤ s_min u_B, the *true* halves of step 2.
   But vacuous (negative as soon as m² > β); it throws away a factor m⁴. The correct
   statement is r0 ≥ h/a ≥ β m² (`hAux_div_aAux_le_r0`, `le_aux_ratio`).
4. tex 1328–1333: "θ\* ≥ (β/m² − 1)/(1 + (β/m² − 1)) = 1 − 1/(β/m²)". **Valid** algebra (for
   β/m² > 0); it gives θ\* ≥ 1 − m²/β — a bound that *deteriorates* as m grows and is negative for
   m² > β.
5. tex 1344–1348: "which gives 1 − β/m² ≤ θ\*". **Non sequitur** (1 − m²/β is not 1 − β/m²) — the
   only invalid step of the lower-bound chain — and with the paper's β the conclusion is **false**:
   d = 11, k = 1, λ = (2, 1, …, 1), Σ = I, x = 0 gives ρ = 0.1, m = 2, θ\* = 2/7 ≈ 0.2857 but
   1 − β/m² = 0.975. Formal version (d = 3): `thetaStar_rate_paper_beta_fails`
   (θ\* = 2/3 < 7/8). The correct constant is 1/β.
6. tex 1334–1337: "since a ≥ s_min ℓ_B, h ≤ s_max ρ u_B and m^aux ≤ s_t(λ_1² − λ_d²), there exists a
   fixed scalar α > 0 such that r0 ≤ α m²". The first two inequalities are the false halves of
   step 2 (correct: a ≥ s_min (d−k) λ_d², h ≤ s_max k λ_1²). Even granting them,
   (M+h)/a ≤ β m² + s_t(λ_1² − λ_d²)/(s_min (d−k) λ_{k+1}²), and the last term is not ≤ const·m²
   with a constant independent of s_t and d; "fixed" is unjustified. Correct:
   r0 ≤ (β' + ω_t) κ_D² κ_B² m² (`r0_le`, `aux_ratio_le`). The two failures of this step are
   exactly the two in-regime counterexample mechanisms: the M-term
   (`thetaStar_rate_fails_under_assumption1`) and a ≥ s_min ℓ_B
   (`thetaStar_rate_fails_under_assumption1_all_states`).
7. tex 1338–1348: from r0 ≤ α m², θ\* ≤ 1 − 1/(1 + α m²) (correct), "which gives θ\* ≤ 1 − α/m²":
   only with a *different* constant, 1/(1+α) (uses m ≥ 1). Minor.

The statement "are all nonnegative scalars" (tex 1290) is fine, but a > 0 (i.e. s_min > 0) is needed
and never stated.

## 5. Assumptions

* **Used by the positive Lean theorems:** `0 < s_min` only (plus the structural facts in `Spec`,
  `Noise`).
* **Assumption 1 (tex 367–384) as formalized** (`ThetaStarRate.Assumption1`, a predicate on a
  sequence of problems P_n, noises N_n and states c_n; local to this file). Reading choices:
  "d and k(d) → ∞" as `Fintype.card → ∞` and `|D| → ∞`; trajectory boundedness
  (sup_t limsup_d (1/d)Σ c_{i,t}² < ∞) for the single time under consideration as
  "∃ C, eventually ‖x‖² ≤ C d"; "ρ is a fixed constant" as ρ_n = ρ₀ for all n; block moments as
  convergence of the normalized sums to a limit in (0,∞) for D and in [0,∞) for B, for each
  p ∈ {2,3,4,6,8}; "Tr Σ ∈ (0,∞), bounded trace" as 0 < Σ_i κ_i² ≤ T with T independent of n.
  The three example sequences satisfy much more than the predicate asks (‖x‖²/d constant, moments
  constant or explicitly → 0, Tr Σ = 1 exactly), so the refutations do not hinge on these choices.
  The third (`…_all_states`) does not use the noise or the state at all, so it also survives the
  weaker reading "Tr Σ finite for each d".
* **What Assumption 1 gives and does not give for Theorem 5**, item by item:
  * *Block proportion* fixes ρ. Enough for the lower bound constant β up to s_max/s_min, and for
    the interpretation θ\* → 1 (`thetaStar_tendsto_one_of_assumption1`).
  * *Block spectral moments.* They bound ψ_D/k and ψ_B/(d−k), hence λ_k² ≤ ψ_D/k = O(1): **λ_k is
    bounded along d → ∞, so m → ∞ is possible only through λ_{k+1} → 0**, and then every bulk
    moment limit is λ_{B,p} = 0 (which is why the assumption allows [0,∞) for B). Consequences:
    (i) the fixed-d counterexample `gapSpecNat` (λ_k → ∞, d = 3) and the m⁻⁴ regime of
    `Spec.thetaStar_rate_quartic` are **outside** Assumption 1; (ii) the moments do *not* bound
    λ_1/λ_k or λ_{k+1}/λ_d: they control the block mean squares ψ_D/k, ψ_B/(d−k), not the extreme
    eigenvalues. In particular λ_{k+1}² can stay Θ(1) while ψ_B/(d−k) → 0, which is the
    counterexample `thetaStar_rate_fails_under_assumption1_all_states`.
  * *Noise spectral bounds* is "Tr Σ ∈ (0, ∞)", bounded. With d → ∞ this forces
    s_min ≤ Tr Σ/d → 0, so ω_t = s_t/(s_min(d−k)) ≥ (1+ρ) s_t/Tr Σ.
    `Spec.thetaStar_rate_trace_bound`: 1 − θ\* < Tr Σ/((1+ρ) s_t (m²−1)). If s_t → ∞ (generic when
    ‖x_t‖² ≍ d, which "trajectory boundedness" allows) then θ\*_t → 1 at fixed m and the "decrease
    region" (θ\*_t, 1) of Theorem 4 is asymptotically empty
    (`thetaStar_rate_isLittleO_of_assumption1`, `thetaStar_rate_fails_under_assumption1`). Also
    s_max/s_min is not controlled.
  * *Trajectory boundedness* (‖x_t‖²/d bounded) gives s_t/(d−k) ≤ (1+ρ) C λ_1²
    (`thetaStar_rate_of_bounded_state`), i.e. it bounds s_t only by O(d), whereas the Θ-claim needs
    s_t = O(d·s_min), and d·s_min ≤ Tr Σ = O(1).
* **So under Assumption 1 the Θ(1/m²) claim holds only in a sub-regime** that the assumption
  does not single out. Sufficient (`thetaStar_rate_isTheta`): s_t = O(s_min d), s_max/s_min = O(1),
  bounded λ_1/λ_k and λ_{k+1}/λ_d; see §3 for which of these are known to be necessary. Example
  inside the sub-regime: `thetaStar_rate_isTheta_under_assumption1_zero_state`. Examples inside
  Assumption 1 but outside the sub-regime: the three paper-claim-false rows.
* **Is λ_{k+1} = Θ(1) needed?** At fixed d the opposite: with λ_{k+1} = Θ(1), λ_k → ∞ and a fixed
  state the rate is m⁻⁴. θ\* is not scale invariant in A (s_t and M scale), whereas m is; any correct
  statement must fix a normalisation, and ω_t is that normalisation.
* **Is boundedness of s_t needed?** Yes, from above, relative to s_min(d−k), for the upper bound
  on θ\*. Not from below: the lower bound on θ\* holds for every state including x_t = 0.

## 6. Numerical evidence (python3 / numpy, double precision)

All inequalities of the file (including the new `thetaStar_rate_psi_bound` and the trace bound)
were checked on 2·10⁴ random instances (d ≤ 8, random spectra, states, noise bounds) — no
violation. Selected values, θ\* computed from the quadratic formula.

Inside Assumption 1 — family 1, λ = (2,…,2,1,…,1), Σ = I/d, c_i = 1, m = 2
(`thetaStar_rate_fails_under_assumption1`):

| n | d | 1 − θ\* | (1 − θ\*)·m² | bound 1/(24(n+2)) |
|---|---|---|---|---|
| 0 | 4 | 1.5610e-02 | 6.244e-02 | 2.0833e-02 |
| 8 | 20 | 3.2893e-03 | 1.316e-02 | 4.1667e-03 |
| 98 | 200 | 3.3289e-04 | 1.332e-03 | 4.1667e-04 |
| 998 | 2000 | 3.3329e-05 | 1.333e-04 | 4.1667e-05 |
| 9998 | 20000 | 3.3333e-06 | 1.333e-05 | 4.1667e-06 |

Inside Assumption 1 — family 2, λ = (1,…,1,ε,…,ε), ε = 1/(n+2), Σ = I/d, m = n+2
(`thetaStar_rate_not_isTheta_under_assumption1`, `…_isTheta_under_assumption1_zero_state`):

| n | m | (1 − θ\*)·m², c_i = 1 | (1 − θ\*)·m², c = 0 (= m²/(1+m²)) |
|---|---|---|---|
| 0 | 2 | 0.2081 | 0.8000 |
| 1 | 3 | 0.1440 | 0.9000 |
| 8 | 10 | 0.04762 | 0.9901 |
| 98 | 100 | 0.004975 | 0.9999 |
| 998 | 1000 | 0.0004998 | 0.999999 |

Inside Assumption 1 — family 3, λ = (2,…,2,1,ε,…,ε), ε = 1/(n+2), m = 2; value at x = 0, Σ = I/d
(the maximum over 200 random states/noises per n was attained at x = 0 with s_max = s_min)
(`thetaStar_rate_fails_under_assumption1_all_states`):

| n | d | 1 − θ\* | (1 − θ\*)·m² | bound 1/(2(n+2)) |
|---|---|---|---|---|
| 0 | 4 | 1.3514e-01 | 0.5405 | 2.5000e-01 |
| 8 | 20 | 2.6527e-02 | 0.1061 | 5.0000e-02 |
| 98 | 200 | 2.5184e-03 | 0.01007 | 5.0000e-03 |
| 998 | 2000 | 2.5019e-04 | 0.001001 | 5.0000e-04 |

Fixed d, m⁻⁴ regime — λ = (μ, 1, 1), D = {1}, Σ = I, x = u_1 (`thetaStar_rate_fails_fixed_state`;
outside Assumption 1):

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
n = 98; k = n + 2; d = 2*k; e = 1/(n + 2)
print(one_minus_theta_star([2]*k + [1]*k, k, [1]*d, 1/d, 1/d))          # 3.3289e-04  (family 1)
print(one_minus_theta_star([1]*k + [e]*k, k, [1]*d, 1/d, 1/d) * k**2)   # 0.004975    (family 2)
print(one_minus_theta_star([2]*k + [1] + [e]*(n+1), k, [0]*d, 1/d, 1/d))# 2.5184e-03  (family 3)
```

## 7. Notes for downstream files

* **Signature change (review round 1):** `thetaStar_rate_isTheta` and `thetaStar_tendsto_one_of_gap`
  keep their names but now take their side conditions as *eventual* hypotheses
  (`∀ᶠ j in l, …` instead of `∀ j, …`). A caller with pointwise hypotheses passes
  `Filter.Eventually.of_forall h`. No other file imported these at the time of the change. No
  theorem was renamed or removed.
* The constants live in `Spec`: `P.thetaStarRateAlpha N c`, `P.thetaStarRateBeta N`. Everything
  else file-specific is in `namespace SuspiciousAlignment.ThetaStarRate`: helper lemmas, the
  fixed-d example family (`gapSpec μ hμ : Spec (Fin 3)`, `gapSpecNat`, `unitNoise`, `e1`), the
  predicate `Assumption1`, and the d → ∞ block family (`BlockIdx n = Fin (n+2) ⊕ Fin (n+2)`,
  `blockSpec n hε hεν hνμ` = diag(μ,…,μ,ν,ε,…,ε), `scaledNoise n` = I/d, `eps n` = 1/(n+2),
  `asp1Spec`, `asp1GapSpec`, `asp1SpikeSpec`, with `@[simp]` evaluation lemmas `blockSpec_*`).
* `ThetaStarRate.Assumption1` is this file's own rendering of Assumption 1; if a shared definition
  of Assumption 1 is introduced later, the three instances should be transported to it.
* The helper facts about `r0`/`thetaStar` duplicate what the Theorem 4 file will prove; they are
  deliberately not in `namespace Spec` to avoid name clashes.
* `Spec.thetaStar_rate_aux_sandwich` (third conjunct) and `Spec.thetaStar_rate_psi_bound` give the
  quantitative form of Theorem 4's remark "θ\*_t → 1 as ψ_D/ψ_B → ∞":
  1 − θ\* ≤ 1/(1 + (s_max/s_min) ψ_D/ψ_B) ≤ ψ_B/ψ_D.
* `Defs.lean` was used unchanged; no definition there was found to be unfaithful for this item.
  (`Spec.normSq` does not take `P`, so it must be written `Spec.normSq c`, not `P.normSq c`.)
* The file is about 1800 lines (above the preferred 1500) because the in-regime families were added
  in place; splitting was not authorised.

## 8. Changes in fix round 1 (response to `notes/status/ThetaStarRate.review1.json`)

| Review issue | Severity | Resolution |
|---|---|---|
| No formal refutation on a family satisfying Assumption 1; note omits "block spectral moments" and does not say the formal counterexamples are outside the regime | major | Added the predicate `ThetaStarRate.Assumption1`, the block family, and `thetaStar_rate_fails_under_assumption1` (the reviewer's suggested family, on `Fin (n+2) ⊕ Fin (n+2)`), plus the m → ∞ variant `thetaStar_rate_not_isTheta_under_assumption1`, the state- and noise-free variant `thetaStar_rate_fails_under_assumption1_all_states`, and the general `thetaStar_rate_isLittleO_of_trace_bounded` / `…_of_assumption1`. Docstrings of `thetaStar_rate_fails_fixed_state`, `thetaStar_rate_not_isTheta`, `Spec.thetaStar_rate_quartic` and §§1, 2, 5 now say these are fixed-d and outside Assumption 1; §5 analyses the block-moment item. |
| "wrong at every step" inaccurate | minor | §1 reworded as suggested; §4 steps 3–4 marked valid. |
| "α cannot be state/time independent" needs a qualifier | minor | Qualifier added in the docstring of `Spec.thetaStar_rate_alpha_not_uniform_in_state` and in the table row. |
| Filter theorems require bounds for all j | minor | `thetaStar_rate_isTheta`, `thetaStar_tendsto_one_of_gap` now take `∀ᶠ j in l` hypotheses (names unchanged). |
| Interpretation hypothesis automatic under Assumption 1 | minor | Added `thetaStar_tendsto_one_of_gap_of_rho` and `thetaStar_tendsto_one_of_assumption1`; table row relabelled. |
| "exactly what the constants hide" overclaims | minor | Docstring reworded ("sufficient", with what is known about necessity); §3 table column rewritten; necessity of the κ_B bound along d → ∞ now formal (`…_all_states`). |
| No non-vacuity instance of the Θ theorem with m → ∞ | minor | `thetaStar_rate_isTheta_gapSpecNat_zero` (the suggested instance) and `thetaStar_rate_isTheta_under_assumption1_zero_state`. |
| "strengthened" label hides state-dependent α | minor | Row relabelled. |
| False proof-step inequalities refuted only numerically (optional) | minor | Half done: `thetaStar_rate_paper_psiB_bound_fails` (ℓ_B ≤ ψ_B is false). The other half (ψ_D ≤ ρ u_B) is still numeric only; it needs a spectrum with a non-flat dominant block, which this file does not have. |

## Reviewer disputes

None: every issue of review 1 was accepted and addressed as listed in §8.

One clarification on the reviewer's optional suggestion for the κ_B bound ("a small example showing
(1 − θ\*) m² → 0 as λ_d → 0 with everything else fixed, e.g. bulk (1, ε, …, ε)"): at *fixed* d this
quantity does not tend to 0. With bulk (1, ε, …, ε), ψ_B → 1 as ε → 0, so
ψ_B/((d−k) λ_{k+1}²) → 1/(d−k) and (1 − θ\*) m² only loses a factor of at most d−k (as the reviewer's
own parenthesis says). The necessity of the κ_B bound in `thetaStar_rate_isTheta` is therefore
shown along d → ∞, with ε_n = 1/(n+2) and d − k = n+2 → ∞
(`thetaStar_rate_fails_under_assumption1_all_states`), which is also a counterexample inside
Assumption 1.
