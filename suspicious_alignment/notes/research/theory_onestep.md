# One-step theory of spectrally filtered updates in Deng's quadratic model

Analogue of Sections 4 and 5 of Deng, Liao, Ouyang, Pang, Song, Yang, *Suspicious Alignment of SGD:
A Fine-Grained Step Size Condition Analysis* (arXiv:2601.11789v2) for updates of the form
`W⁺ = W − η F(G)`, `F(G) = U f(S) Vᵀ` (SGD, Muon, HTMuon(p), Echelon(r)).

* Scripts: `sim/theory_onestep/` (`run_all.sh` reproduces every number; raw results in
  `sim/theory_onestep/results/*.json`, logs in `results/*.log`, digest in `results/summary.json`).
* Companion specification used by the Lean files: `notes/research/filter_spec.md` (same notation; the
  statements there are special cases of Sections 3–5 here).
* Every statement is tagged **[PROVED]** (complete proof given here), **[NUMERICAL]** (observed in a
  stated experiment only) or **[HEURISTIC]** (argument given, not a proof). Section 7 lists the
  numerical validation of every formula; Section 9 restates the provable core over finite sums.

---

## 0. Summary

**Effective curvature.** A spectral filter with gain `γ(σ) := f(σ)/σ` multiplies the step size of
each *singular direction of the gradient* by `γ(σ)`. In Deng's coordinates this replaces the Hessian
eigenvalue `λ_i` in every one-step formula by an **effective curvature**

| model | effective curvature `ν_i` | what replaces Deng's `η λ_i` |
|---|---|---|
| (M1) vector, `n = 1` | `λ_i · γ(‖g‖)`, one gain for all modes | `η_eff λ_i`, `η_eff = η f(‖Ax+ξ‖)/‖Ax+ξ‖` |
| (M2) commuting states | `λ_i · γ(σ_i) = f(λ_i a_i)/a_i`, `σ_i = λ_i a_i`, `a_i = ‖c_i‖` | `η ν_i`: SGD `λ_i`; Muon `1/a_i`; HTMuon `λ_i^p a_i^{p−1}`; Echelon(r) `λ_i / max(σ_i, τ)` |
| (M2) arbitrary states | matrix version: `Φ = h(M) Λ C`, `M = ΛCCᵀΛ`, `h(t) = f(√t)/√t` | Gram formulas (Thm 3.5) |

Deng's comparison functional keeps its form **exactly** (no expectation, no `d → ∞`):
`f(η) = s^ℬ s₊^𝒟 − s₊^ℬ s^𝒟 = p_f η² + q_f η`, `θ₊ − θ = f(η)/(s s₊)`, with (commuting states)

    q_f = 2 ∑_{i∈𝒟} ∑_{j∈ℬ} s_i s_j (ν_j − ν_i),     p_f = ∑_{i∈𝒟} ∑_{j∈ℬ} s_i s_j (ν_i² − ν_j²),     s_i = λ_i² a_i².

**What happens to Deng's takeaways** (details and counterexamples in Section 6):

| | (M1), any filter | (M2) Muon | (M2) HTMuon(p) | (M2) Echelon(r) |
|---|---|---|---|---|
| sign fact `q < 0` (from `λ_k > λ_{k+1}`) | survives (`q_f = γ q₀`; with spherical noise `E q = ℓ q₀`) | **fails**: sign of `q` is decided by coefficient sizes `a_i`, not by the gap | holds if `m^p > (max_𝒟 a / min_ℬ a)^{1−p}`; fails otherwise | inside the tail survives; head as Muon |
| (D1) critical step `η*` | survives with `η → η_eff`: `η*_f = η*₀ ‖Ax‖/f(‖Ax‖)`; regime selected by the **gradient norm** | modified: `p = s ψ (θ_iso − θ)` exactly (any state, any noise, `d ≤ n`); dichotomy only if `q < 0`; all four sign patterns of `(q, p)` occur noise-free | modified: holds under effective separation (S+); reversed under (S−) | `r = 0`: SGD with `η/‖G‖₂`; `r ≥ rank`: Muon |
| (D2) self-correction above `θ*` for any `η` | survives with `θ*_f` (spherical noise) | modified: thresholds `g_gap, θ*` collapse to `θ_iso = ψ_𝒟/(ψ_𝒟+ψ_ℬ)`; decrease for every `η > η_att` always, for every `η > 0` only if `E q ≤ 0` (noise-dominated); fails noise-free | fails noise-free above `θ_flip(p)` (alignment *increases* for small `η`) | mixed |
| (D3) bounds on `η*` | `η*_f ∈ [2/(λ_1+λ_{k+1}), 2/(λ_k+λ_d)] · ‖Ax‖/f(‖Ax‖)`; no state-free bound | under (S+): `2/(ν_𝒟^max+ν_ℬ^max) ≤ η* ≤ 2/(ν_𝒟^min+ν_ℬ^min)` | same | same |
| (D4) window `η_𝒟^loss < η < η_ℬ^loss` | filter-then-project: unchanged ratio `≥ m`; project-then-filter: only below `θ^crit_PF` | exists iff `⟨ν⟩_𝒟 > ⟨ν⟩_ℬ` (roughly: dominant coefficients smaller than bulk ones); **reversed** above `θ_flip(0) = θ_iso`; ratio `m⁰` at fixed coefficients | ratio `m^p (a_ℬ/a_𝒟)^{1−p}` (two-level); reversed above `θ_flip(p)` | `r=0`: SGD's; `H = 𝒟`: `m`-independent at fixed coefficients |

**Gap dependence.** At fixed *coefficients* the window ratio `η_ℬ^loss/η_𝒟^loss` scales as `m^p`
(SGD `m`, HTMuon(1/8) `m^{1/8}`, Muon and Echelon(k) `m⁰`); at fixed *gradient spectrum* (hence fixed
alignment) it scales as `m` for every filter, with a prefactor `(ρ(1−θ)/θ)^{(1−p)/2}` that vanishes
as `θ → 1`. The critical alignment below which the suspicious-alignment window exists is
`θ_flip(p) = ρ m^{2/(1−p)}/(1 + ρ m^{2/(1−p)})` (two-level states, noise-free); it still tends to 1 as
`m → ∞`, at rate `1 − θ_flip ≈ 1/(ρ m^{2/(1−p)})`.

**Noise.** Strong noise restores Deng's structure for every filter: in the noise-dominated regime
the filtered step is SGD with a renormalised step size and noise level (Cor 3.10, Prop 3.12,
Thm 2.3), so `q < 0` and the gap dependence come back.

**Side finding on the paper.** Theorem 8 as printed in the main text (`η* ≤ (λ_1−λ_d)/(λ_kλ_1−λ_{k+1}λ_d)`)
and Corollary 9 (`η* ≤ 2/λ_1`) are false as stated; the appendix version with the factor 2 is true
in the noise-free case, and the sharp noise-free bounds are `2/(λ_1+λ_{k+1}) ≤ η*₀ ≤ 2/(λ_k+λ_d)`
(Remark 2.8).

---

## 1. Setting, filters, and identities valid for every update

### 1.1 Notation

`A = U Λ Uᵀ ∈ ℝ^{d×d}`, `λ_1 ≥ … ≥ λ_k > λ_{k+1} ≥ … ≥ λ_d > 0`, `𝒟 = {1..k}`, `ℬ = {k+1..d}`,
`m = λ_k/λ_{k+1}`, `ρ = k/(d−k)`, `ψ_S = ∑_{i∈S} λ_i²`, `tr_S = ∑_{i∈S} λ_i`, `ψ = ψ_𝒟 + ψ_ℬ`,

    θ_iso := ψ_𝒟/ψ          (alignment of an "isotropic" gradient-generating state, all ‖c_i‖ equal),
    θ_tr  := tr_𝒟/(tr_𝒟+tr_ℬ).

Since `ψ_𝒟 ≥ k λ_k²` and `ψ_ℬ ≤ (d−k) λ_{k+1}²`, `θ_iso ≥ ρm²/(1+ρm²)` = Deng's `g_gap` for isotropic
noise (`s_max = s_min`), with equality for a two-level spectrum.

Parameters `W ∈ ℝ^{d×n}` (model (M1): `n = 1`, `W = x`). Eigen-coordinates `C := UᵀW` with rows
`c_i ∈ ℝⁿ`, `a_i := ‖c_i‖`. For (M2), `L(W) = ½ tr(WᵀAW) = ½ ∑ λ_i a_i²`, clean gradient `AW`,
`Uᵀ(AW) = ΛC`. Per-mode quantities

    σ_i := λ_i a_i  (norm of the i-th gradient row),   s_i := σ_i² = λ_i² a_i²,   ℓ_i := λ_i a_i²,
    s^S := ∑_{i∈S} s_i,   s := s^𝒟 + s^ℬ = ‖AW‖_F²,   θ := s^𝒟/s,
    τ^S := ∑_{i∈S} λ_i s_i = ∑ λ_i³ a_i²,    u^S := ∑_{i∈S} λ_i² s_i = ∑ λ_i⁴ a_i²   (Deng's sums).

An update direction is any `Δ ∈ ℝ^{d×n}`; `Φ := UᵀΔ` with rows `φ_i`; `W₊ = W − ηΔ`, `C₊ = C − ηΦ`.
For a block `S ∈ {𝒟, ℬ}`:

    T^S := ∑_{i∈S} λ_i² ⟨c_i, φ_i⟩,   V^S := ∑_{i∈S} λ_i² ‖φ_i‖²,
    N^S := ∑_{i∈S} λ_i  ⟨c_i, φ_i⟩,   R^S := ∑_{i∈S} λ_i  ‖φ_i‖²,       T := T^𝒟+T^ℬ, V := V^𝒟+V^ℬ.

### 1.2 Spectral filters

Let `f : [0,∞) → [0,∞)` with `f(0) = 0`, and for `G = ∑_k σ_k u_k v_kᵀ` (SVD) put
`F(G) := ∑_k f(σ_k) u_k v_kᵀ`. Gain `γ(σ) := f(σ)/σ` (`σ > 0`), and `h(t) := f(√t)/√t = γ(√t)` for
`t > 0`, `h(0) := 0`.

**Lemma 1.1 (filter calculus) [PROVED].** `F(G) = h(GGᵀ) G = G h(GᵀG)`. In particular `F(G)` does
not depend on the choice of the SVD, and `F(Q₁ G Q₂ᵀ) = Q₁ F(G) Q₂ᵀ` for orthogonal `Q₁, Q₂`.

*Proof.* `GGᵀ = ∑ σ_k² u_k u_kᵀ`, so `h(GGᵀ) = ∑_k h(σ_k²) u_k u_kᵀ` (zero on `ker GGᵀ` because
`h(0) = 0`), and `h(GGᵀ) G = ∑_k h(σ_k²) σ_k u_k v_kᵀ = ∑_k f(σ_k) u_k v_kᵀ`. The right-hand side is
a function of `G` alone. Equivariance: `h(Q₁GGᵀQ₁ᵀ) Q₁GQ₂ᵀ = Q₁ h(GGᵀ) G Q₂ᵀ`. ∎

Consequently `UᵀF(G) = F(UᵀG)`: **we may and do work in eigen-coordinates** (`U = I`), where the
filtered step reads `C₊ = C − η Φ`, `Φ = F(ΛC + UᵀΞ)`.

The filters considered (the first three are *index-wise*: `f` is a fixed function; the last two are
*spectrum-dependent*: `f` depends on the list of singular values of `G`, which is still invariant
under `G ↦ Q₁GQ₂ᵀ`, so Lemma 1.1 holds with `h` depending on `G`):

| optimizer | `f(σ)` | gain `γ(σ)` | homogeneity degree |
|---|---|---|---|
| SGD | `σ` | `1` | 1 |
| Muon (exact polar factor) | `1` (`σ > 0`) | `1/σ` | 0 |
| HTMuon(p), `0 ≤ p ≤ 1`, default `p = 1/8` | `σ^p` | `σ^{p−1}` | `p` |
| Echelon(r), exact top-r frame | `min(σ, τ)/τ`, `τ = σ_{r+1}(G)` | `1/max(σ, τ)` | 0 |
| Muon as implemented (NS5) | `φ^{∘5}(σ/‖G‖_F)`, `φ(x) = 3.4445x − 4.7750x³ + 2.0315x⁵` | — | 0 |

*Echelon.* With an exact frame `U_r` = top-`r` left singular vectors of `G`, `P = polar(U_rᵀG) = V_rᵀ`
and `T = G − U_rU_rᵀG = ∑_{k>r} σ_k u_k v_kᵀ`, `τ = ‖T‖₂ = σ_{r+1}`, hence
`O = U_rP + T/τ = ∑_{k≤r} u_kv_kᵀ + ∑_{k>r} (σ_k/τ) u_kv_kᵀ`, i.e. `f(σ) = min(σ,τ)/τ`. `r = 0` is
`G/‖G‖₂` (spectrally normalised SGD) and `r ≥ rank G` is Muon. (Check C1: the literal head–tail
construction and the filter agree to `5.5e-13`; the numpy port of `zeropower_via_newtonschulz5`
agrees with the scalar filter to `1.4e-15`.)

The speed-ups of HTMuon (`htmuon_ns`, `htmuon_interval`, `htmuon_stream`) change *which* filter is
applied at a given step (an approximate `σ^p`, or `σ^p` and `1` alternating, or an approximate
singular frame); the one-step theory below applies to whichever `f` is actually applied.

### 1.3 Identities for an arbitrary update direction

**Lemma 1.2 (comparison functional) [PROVED].** For every `Δ` and every `η`:

    s₊^S = s^S − 2η T^S + η² V^S,
    f(η) := s^ℬ s₊^𝒟 − s₊^ℬ s^𝒟 = p η² + q η,     q := 2 (s^𝒟 T^ℬ − s^ℬ T^𝒟),   p := s^ℬ V^𝒟 − s^𝒟 V^ℬ,

and if `s > 0`, `s₊ > 0`: `θ₊ − θ = f(η)/(s s₊)`. Hence for `η > 0` the sign of the one-step
alignment change is the sign of `p η + q`.

*Proof.* `s₊^S = ∑_S λ_i² ‖c_i − ηφ_i‖²`; expand. Then
`s^ℬ s₊^𝒟 − s₊^ℬ s^𝒟 = −2η(s^ℬT^𝒟 − s^𝒟T^ℬ) + η²(s^ℬV^𝒟 − s^𝒟V^ℬ)`, and
`θ₊ − θ = (s₊^𝒟 s − s^𝒟 s₊)/(s s₊) = (s₊^𝒟 s^ℬ − s^𝒟 s₊^ℬ)/(s s₊)`. ∎

This is Deng's `f_t` (their eq. for `f_t(η_t)` and Lemma "quadratic form"); for SGD (`φ_i = λ_i c_i + ξ_i`)
taking expectations gives their `q_t = 2(s^𝒟τ^ℬ − s^ℬτ^𝒟)`, `p_t = s^ℬ(u^𝒟+e_𝒟) − s^𝒟(u^ℬ+e_ℬ)`.

**Lemma 1.3 (three alignments) [PROVED].** Let `θ_upd := V^𝒟/V` (the alignment of the update, i.e.
`‖P^𝒟AΔ‖²/‖AΔ‖²`) and `ϑ := T^𝒟/T` (cross alignment), when `V > 0`, `T ≠ 0`. Then

    p = s V (θ_upd − θ),        q = −2 s T (ϑ − θ),

`lim_{η→∞} θ₊ = θ_upd`, and `dθ₊/dη|_{η=0} = q/s²`.

*Proof.* `p = (s − s^𝒟)V^𝒟 − s^𝒟(V − V^𝒟) = sV^𝒟 − s^𝒟V`; `q = 2(s^𝒟(T − T^𝒟) − (s − s^𝒟)T^𝒟) = 2(s^𝒟T − sT^𝒟)`.
The limits follow from `θ₊ = (s^𝒟 − 2ηT^𝒟 + η²V^𝒟)/(s − 2ηT + η²V)`. ∎

So: *large steps pull the alignment towards the alignment of the update, small steps move it
according to the cross alignment.* For SGD without noise `θ_upd = u^𝒟/(u^𝒟+u^ℬ) > θ` and
`ϑ = τ^𝒟/(τ^𝒟+τ^ℬ) > θ` always (gap); for a filtered update neither inequality is automatic.

**Lemma 1.4 (loss) [PROVED].** In (M1)/(M2), `L(W − ηΔ) − L(W) = −η N + (η²/2) R` with
`N = ⟨AW, Δ⟩ = N^𝒟 + N^ℬ` and `R = ⟨Δ, AΔ⟩ = R^𝒟 + R^ℬ ≥ 0`. If `N > 0`, `R > 0`, the loss decreases
iff `0 < η < η^loss := 2N/R` and increases iff `η > η^loss`.

*Proof.* `L` is quadratic with Hessian `I_n ⊗ A`. ∎

---

## 2. Model (M1): vector parameters

The gradient `g ∈ ℝ^{d×1}` has the single singular value `‖g‖`, left singular vector `g/‖g‖`, right
singular vector `1`. Hence, for every filter,

    F(g) = f(‖g‖) g/‖g‖ = γ(‖g‖) g,          x₊ = x − η γ(‖Ax + ξ‖) (Ax + ξ).                  (2.1)

**The filter is invisible except through a scalar, state- and noise-dependent step size**
`η_eff = η γ(‖Ax+ξ‖)`. Echelon(r) coincides with Muon for every `r ≥ 0` (rank one: `r = 0` gives
`g/‖g‖₂`, `r ≥ 1` gives the polar factor), and NS5 is `c_NS · g/‖g‖` with
`c_NS = φ^{∘5}(1) = 0.69644` (a constant multiple of Muon).

### 2.1 Noise-free

**Theorem 2.1 [PROVED].** Let `ξ = 0`, `s^𝒟, s^ℬ > 0`, `γ := γ(√s) > 0` where `√s = ‖Ax‖`. Then
`c_i⁺ = (1 − η γ λ_i) c_i`, i.e. the filtered step is Deng's noise-free step with `η` replaced by
`η_eff = ηγ(‖Ax‖)`, and

    q_f = γ q₀,   p_f = γ² p₀,     q₀ := 2(s^𝒟τ^ℬ − s^ℬτ^𝒟) < 0,   p₀ := s^ℬu^𝒟 − s^𝒟u^ℬ > 0,
    η*_f := −q_f/p_f = η*₀ · ‖Ax‖ / f(‖Ax‖),          η*₀ := −q₀/p₀,
    2/(λ_1 + λ_{k+1})  ≤  η*₀  ≤  2/(λ_k + λ_d).

For every `η > 0` with `x₊ ≠ 0`: `θ₊ < θ ⟺ η < η*_f`, `θ₊ = θ ⟺ η = η*_f`, `θ₊ > θ ⟺ η > η*_f`.

*Proof.* (2.1) gives `φ_i = γ λ_i c_i`, so `T^S = γτ^S`, `V^S = γ²u^S`, and Lemma 1.2 gives
`q_f, p_f`. Write `q₀ = 2∑_{i∈𝒟,j∈ℬ} s_is_j(λ_j − λ_i)` and `p₀ = ∑_{i∈𝒟,j∈ℬ} s_is_j(λ_i² − λ_j²)`;
all terms have a strict sign because `λ_i ≥ λ_k > λ_{k+1} ≥ λ_j` and some `s_is_j > 0`. With weights
`w_ij := s_is_j(λ_i − λ_j) ≥ 0`, `1/η*₀ = ∑ w_ij (λ_i+λ_j)/2 / ∑ w_ij` is a weighted mean of
`(λ_i+λ_j)/2 ∈ [(λ_k+λ_d)/2, (λ_1+λ_{k+1})/2]`. The trichotomy is Lemma 1.2 with `p_f > 0 > q_f`. ∎

**Corollary 2.2 (the regime is selected by the gradient norm) [PROVED].** For `f(σ) = σ^p`, `p < 1`:
`η*_f(x) = η*₀(x) ‖Ax‖^{1−p}`, `η*₀(tx) = η*₀(x)` and `η*_f(tx) = t^{1−p} η*_f(x)` for `t > 0`. Hence
for a fixed step size `η`

    θ₊ < θ   ⟺   ‖Ax‖ > (η/η*₀(x))^{1/(1−p)}       (Muon: ‖Ax‖ > η/η*₀(x)).

Along a ray `{t x}` the alignment decreases far from the optimum and increases close to it,
*whatever `η` is*; for SGD (`p = 1`) the regime depends on `η` only. Deng's "small-step phase /
large-step phase" becomes "large-gradient phase / small-gradient phase".

Validation (A1): 15 random states (`d ∈ {50,100,200}`, `m ∈ {1.5..100}`), filters SGD, Muon,
HTMuon(1/8), HTMuon(1/2), NS5, Echelon(0), Echelon(3), direct SVD of the `d×1` gradient:
`F(g) − γ g` relative error `≤ 7.8e-16`, coordinates after the step vs `(1−η_effλ_i)c_i` `≤ 7.2e-15`,
`|θ₊−θ|` at `η*_f` `≤ 1.0e-15`, 435 sign/bound tests, 0 violations.

### 2.2 Spherical Gaussian noise: exact formulas

Assume `ξ ~ N(0, ς² I_d)`. (Why this structure: the filter acts through `‖Ax+ξ‖`, which couples
all coordinates of the noise; for spherical noise the law of `g = Ax+ξ` is rotationally symmetric
about the axis `μ := Ax`, and everything reduces to three scalars. For anisotropic `Σ` see 2.3.)

Let `e := μ/‖μ‖`, `snr := ‖μ‖/ς = √s/ς`, and decompose `g/ς = w e + z_⊥` with
`w ~ N(snr, 1)` and `z_⊥` a standard Gaussian in `e^⊥` independent of `w`; `r := ‖z_⊥‖`
(`r² ~ χ²_{d−1}`), `N := ‖g‖ = ς√(w²+r²)`, `cos := w/√(w²+r²)`, `sin := r/√(w²+r²)`. Define

    m₁ := E[f(N) cos],   A_∥ := E[f(N)² cos²],   A_⊥ := E[f(N)² sin²]/(d−1),
    ℓ := m₁/√s,          β₂ := (A_∥ − A_⊥)/s.

(SGD: `ℓ = 1`, `β₂ = 1`, `A_⊥ = ς²`.)

**Theorem 2.3 [PROVED].** For every measurable `f ≥ 0` with `E f(N)² < ∞`:

    E[F(g)] = ℓ · Ax,          E[F(g)F(g)ᵀ] = β₂ (Ax)(Ax)ᵀ + A_⊥ I_d,
    E[c_i⁺] = (1 − η ℓ λ_i) c_i,
    E[s₊^S] = s^S − 2η ℓ τ^S + η² (β₂ u^S + A_⊥ ψ_S),
    E[f(η)] = p^f η² + q^f η,     q^f = ℓ q₀,     p^f = β₂ p₀ + A_⊥ (s^ℬψ_𝒟 − s^𝒟ψ_ℬ).

So the expected comparison functional has **exactly Deng's form** with three renormalised constants;
if `β₂ > 0` it equals `(ℓ²/β₂)·[p_Deng(κ²) η'² + q₀ η']` with `η' = η β₂/ℓ` and noise level
`κ² = A_⊥/β₂`.

*Proof.* `F(g) = f(N)(cos · e + sin · ω)` with `ω := z_⊥/r` uniform on the unit sphere of `e^⊥` and
independent of `(w, r)`, hence of `(N, cos, sin)`. `E ω = 0` and `E ωωᵀ = (I − eeᵀ)/(d−1)` give
`E F = m₁ e = ℓ μ` and `E FFᵀ = A_∥ eeᵀ + A_⊥ (I − eeᵀ) = A_⊥ I + (A_∥−A_⊥) μμᵀ/s`. In
eigen-coordinates `μ_i = λ_i c_i`, so `E F_i = ℓλ_ic_i`, `E F_i² = β₂λ_i²c_i² + A_⊥`;
`E T^S = ∑_S λ_i² c_i E F_i = ℓτ^S`, `E V^S = ∑_S λ_i² E F_i² = β₂u^S + A_⊥ψ_S`; apply Lemma 1.2. ∎

**Proposition 2.4 (sign facts and thresholds in (M1)) [PROVED].** Assume `snr > 0`, `d ≥ 2`,
`s^𝒟, s^ℬ > 0`, `f > 0` on a set of positive measure.
(a) `ℓ > 0`; hence `q^f < 0` — **Deng's sign fact survives**.
(b) `β₂ ≥ 0`.
(c) If `θ ≤ θ_iso` then `p^f ≥ 0`, with `p^f > 0` if `θ < θ_iso` or `β₂ > 0`. Then
    `η*_f := −q^f/p^f = ℓ(−q₀)/(β₂p₀ + A_⊥(s^ℬψ_𝒟 − s^𝒟ψ_ℬ))` and `E f(η) < 0 ⟺ η < η*_f`.
(d) If `θ ≥ θ*_f := r₀/(1+r₀)`, `r₀` the positive root of
    `A_⊥ψ_ℬ r² + (A_⊥ψ_ℬ − A_⊥ψ_𝒟 − β₂ s (λ_1²−λ_d²)) r − A_⊥ψ_𝒟 = 0`, then `p^f ≤ 0` and
    `E f(η) < 0` for every `η > 0`.
    This is Deng's Theorem 4 with `(s_min, s_max, s_t) → (A_⊥, A_⊥, β₂ s)`; `θ_iso ≤ θ*_f < 1`.
(e) (Muon.) `A_∥ = 1 − ((d−1)/d) ₁F₁(1; d/2+1; −snr²/2)`, `A_⊥ = (1/d) ₁F₁(1; d/2+1; −snr²/2)`,
    `m₁ = (snr/√2) Γ((d+1)/2)/Γ(d/2+1) · ₁F₁(1/2; d/2+1; −snr²/2)`.

*Proof.* (a) `N` depends on `(|w|, r)` only, and `P(w > 0 | |w| = v) = e^{snr·v}/(e^{snr·v}+e^{−snr·v})`,
so `m₁ = E[f(N) |cos| tanh(snr·|w|)] > 0`.
(b) `A_∥ − A_⊥ = E[f(N)² (d cos² − 1)]/(d−1)`. Conditionally on `N`, the direction `g/N` has density
`∝ exp(κ t)`, `t = cos`, `κ = N‖μ‖/ς² ≥ 0`, with respect to the uniform measure on the sphere, under
which `t` has a symmetric law `ρ_d` with `E t² = 1/d`. Symmetrising,
`E[t² | N] = ∫ t² cosh(κt) dρ_d / ∫ cosh(κt) dρ_d ≥ ∫ t² dρ_d = 1/d` by Chebyshev's association
inequality (`t²` and `cosh(κt)` are both non-decreasing in `|t|`).
(c) `p₀ > 0` (Theorem 2.1) and `s^ℬψ_𝒟 − s^𝒟ψ_ℬ ≥ 0 ⟺ θ ≤ θ_iso`; `A_⊥ > 0`.
(d) `p₀ ≤ s^𝒟s^ℬ(λ_1² − λ_d²)`, so `p^f ≤ 0` is implied by
`β₂ s² θ(1−θ)(λ_1²−λ_d²) ≤ A_⊥ s (θψ_ℬ − (1−θ)ψ_𝒟)`; divide by `s(1−θ)` and put `r = θ/(1−θ)`:
`A_⊥ψ_ℬ r² + (A_⊥ψ_ℬ − A_⊥ψ_𝒟 − β₂s(λ_1²−λ_d²)) r − A_⊥ψ_𝒟 ≥ 0`, i.e. `r ≥ r₀`. At `r = ψ_𝒟/ψ_ℬ` the
left side is `−β₂s(λ_1²−λ_d²) r ≤ 0`, so `r₀ ≥ ψ_𝒟/ψ_ℬ`. With `q^f < 0`, `E f(η) = η(p^fη + q^f) < 0`.
(e) `(w², r²)` is a Poisson(`snr²/2`) mixture over `J` of independent `χ²_{1+2J}`, `χ²_{d−1}`, so
`cos² | J ~ Beta((1+2J)/2, (d−1)/2)` and `E cos² = 1 − (d−1) E[1/(d+2J)] =
1 − ((d−1)/d) e^{−λ} ₁F₁(d/2; d/2+1; λ)` with `λ = snr²/2`; Kummer's transformation gives the stated
form, and `A_⊥ = (1 − A_∥)/(d−1)`. The formula for `m₁` is the classical mean resultant length of
the projected normal distribution; it is used here as **[NUMERICAL]**: it agrees with the 2-D
quadrature to `5.7e-14` (A2). ∎

Caveat (as in Deng): Theorem 2.3 controls the sign of `E f(η)`; passing to the sign of
`E[θ₊] − θ` needs concentration of `s₊` (Deng's ratio lemma, `d → ∞`), which we do not re-prove.
In the experiment S2 below the two signs agree whenever `E f` is not within noise of zero.

**Remark 2.5 (limits).** `snr → ∞`: `ℓ → γ(√s)`, `β₂ → γ(√s)²`, `A_⊥ → 0`, `θ*_f → 1` (Theorem 2.1).
Noise-dominated (`s ≪ ς²d`, `d` large): `‖g‖` concentrates at `N̄ := √(s + ς²d)`, and
`ℓ ≈ γ(N̄)`, `β₂ ≈ γ(N̄)²`, `A_⊥ ≈ ς²γ(N̄)²`: **Deng's theory with `η_eff = η γ(√(s + ς² d))` and the
same noise level `ς²`** (mean-field replacement). Numerically (A2, Muon, `d ∈ {50, 200}`,
`snr ∈ {0.3, 3, 30}`): relative deviation of `(ℓ, β₂, A_⊥)` from the mean-field values
`≤ (0.5%, 3.8%, 0.5%)`.

Validation of Theorem 2.3 (A2): `d ∈ {50, 200}`, `snr ∈ {0.3, 3, 30}`, filters SGD/Muon/HTMuon(1/8)/
HTMuon(1/2), `3·10⁵` Monte-Carlo samples of the actual update, 8 statistics each (`T^𝒟, T^ℬ, V^𝒟, V^ℬ`,
`R^𝒟, R^ℬ` and the two project-then-filter statistics of Section 5): 192 z-tests, `max |z| = 3.00`
(expected maximum of 192 standard normals ≈ 2.8–3.0), max relative error `1.6e-2` (at
`snr = 0.3`, where the Monte-Carlo error is of that size). `ℓ > 0` and `β₂ ≥ 0` in all cases.
Thresholds (E2): 120 random instances; `q^f < 0` 120/120; `θ ≤ θ_iso ⇒ p^f > 0` 74/74;
`θ ≥ θ*_f ⇒ p^f ≤ 0` 36/36.

### 2.3 Anisotropic noise

For `ξ ~ N(0, Σ)` with general `Σ` the *pathwise* statement (2.1) still holds — every realisation is a
Deng step with the random step size `η γ(‖Ax+ξ‖)` — but `η_eff` is correlated with `ξ` and there is
no closed form.

**Remark 2.6 (mean-field replacement) [HEURISTIC + NUMERICAL].** `‖g‖²` has mean `N̄² := s + Tr Σ` and
variance `2Tr Σ² + 4μᵀΣμ ≤ 4‖Σ‖_op N̄²`, so with `ε := 2√‖Σ‖_op / N̄` the relative fluctuation of
`‖g‖²` is at most `ε`. When `ε` is small, `γ(‖g‖) ≈ γ(N̄)` and

    E[T^S] ≈ γ(N̄) τ^S,     E[V^S] ≈ γ(N̄)² (u^S + e_S),     e_S = ∑_S λ_i² κ_i²,

i.e. Deng's formulas with `η → η γ(√(s + Tr Σ))`. The error is second order in `ε`; one of its two
sources is visible in the exact Stein identity (Gaussian integration by parts; `γ(N) = N^{p−1}`,
`d ≥ 3`)

    E[γ(N) g] = E[γ(N)] μ − (1−p) Σ E[N^{p−3} g],                                             (2.2)

whose last term is `O(‖Σ‖_op/N̄²) = O(ε²)` relative to the first (the other source is the Jensen gap
`E γ(N) ≠ γ(N̄)`, also `O(ε²)`). Identity (2.2) also shows that under anisotropic noise the mean
filtered gradient is *not* parallel to `Ax`: coordinates with a large noise variance are damped by
`≈ 1 − (1−p)κ_i²/N̄²`.
Numerics (A4; `d ∈ {50, 200, 800}`; isotropic, power-law `κ_i² ∝ 1/i` and "one spike carrying 30% of
the trace" covariances; `TrΣ/s ∈ {0.1, 1, 10}`; Muon and HTMuon(1/8); `10⁵` samples): the relative
error of the mean-field values of `(E T^𝒟, E T^ℬ, E V^𝒟, E V^ℬ)` is `≤ 0.27%` when `ε < 0.15`, `≤ 1.5%`
when `0.15 ≤ ε < 0.5`, and `≤ 9.1%` for `0.5 ≤ ε ≤ 1.04`. Identity (2.2) is confirmed by Monte Carlo in S4 (`d = 60`,
power-law `Σ` with `TrΣ = 2s`, `p ∈ {0, 1/8, 1/2}`, 4 test directions, `6·10⁵` samples: residual
`max |z| = 1.77`; the plain mean-field value is off by 0.6–12% there, `ε = 0.76`).

**Remark 2.7 ((M1) in the setup of the paper's simulation) [NUMERICAL, script `deng_setup.py`, S1–S2].**
Spectrum of `quad_sim.py` (`d = 500`, `k = 50`, dominant `linspace(100, 80)`, `λ_{k+1} = 80/(m+0.1)`),
`x₀ ~ N(0, I)` (seed 42), `ς = 0.5`, `η = 0.003`; states `x₀` (`‖Ax‖/(ς√d) ≈ 45–62`: signal-dominated)
and, for `m = 10`, `0.05·x₀` and `0.01·x₀` (`‖Ax‖/(ς√d) = 2.3` and `0.45`).

| `m` | state | `θ` | `η*` SGD (Deng) | `η*_f` Muon (Thm 2.3) | mean-field `η*_Deng·N̄` | `η*_f` HTMuon(1/8) | `η/η*_f` Muon |
|---|---|---|---|---|---|---|---|
| 2 | `x₀` | 0.522 | 0.016712 | 11.502 | 11.502 | 5.0821 | 2.6e-4 |
| 10 | `x₀` | 0.962 | 0.020322 | 10.305 | 10.305 | 4.7307 | 2.9e-4 |
| 50 | `x₀` | 0.998 | 0.021315 | 10.610 | 10.610 | 4.8817 | 2.8e-4 |
| 10 | `0.05 x₀` | 0.962 | 0.020198 | 0.55971 | 0.55958 | 0.36953 | 5.4e-3 |
| 10 | `0.01 x₀` | 0.962 | 0.017609 | 0.21662 | 0.21617 | 0.15832 | 1.4e-2 |

A direct Monte Carlo (`4·10⁴` samples of the actual update per row and filter) of `E f(η)` at
`η = η*_f·{0.5, 1, 2}` agrees with `p^fη² + q^fη` (`|z| ≤ 2.3` in 45 tests), and the Monte-Carlo
`E[θ₊ − θ]` is negative at `0.5η*_f` and positive at `2η*_f` in all 15 cases. At `η = η*_f` itself
`E[θ₊−θ]` is not zero: it is `≈ −1·10⁻³ ± 4·10⁻⁵` at `0.01x₀` (and `|·| ≤ 2·10⁻⁴` elsewhere) — the
finite-`d` gap between "sign of `E f`" and "sign of `E θ₊ − θ`" mentioned in the caveat above.
The projected loss thresholds of Theorem 5.7(b) are confirmed in the same runs (mean loss change at
the predicted thresholds `|z| ≤ 2.3`).
Two consequences: (i) the mean-field replacement `η_eff = ηγ(√(s+ς²d))` is accurate to `≤ 0.21%`
here; (ii) since `‖g‖ ≈ √(s + ς²d) ≥ ς√d = 11.2`, the SGD-equivalent step size of (M1)-Muon is
capped: `η_eff ≤ η/(ς√d) = 2.7·10⁻⁴`, eleven times smaller than the paper's `η = 0.003`, and it
varies along the trajectory as `η/√(s_t + ς²d)`. Deng's comparison "`η` versus `η*_t`" becomes
"`η/√(s_t + ς²d)` versus `η*_t`".

**Remark 2.8 (Deng's Theorem 8 and Corollary 9 need a correction) [PROVED + NUMERICAL].**
Theorem 8 (main text): if `θ_t ≥ e_ℬ/(e_ℬ+e_𝒟)` then `η*_t ≤ (λ_1−λ_d)/(λ_kλ_1−λ_{k+1}λ_d)`;
Corollary 9: then `η*_t ≤ 2/λ_1`. Both statements are false.

* *Counterexample.* `d = 3`, `λ = (10, 1, 0.1)`, `𝒟 = {1,2}`, `c = (0.01, 1, 1)`, `Σ = 10⁻⁸ I`. Then
  `θ = 0.9902 ≥ e_ℬ/(e_ℬ+e_𝒟) = 9.9·10⁻⁵`, but `η* = 1.00407 > 0.99099` (Theorem 8) `> 0.2 = 2/λ_1`
  (Corollary 9). Direct check: the noise-free step with `η = 0.5 = 2.5·(2/λ_1)` moves `θ` from
  `0.99020` to `0.97846` (a decrease, as it must for `η < η*`). Replicating every coordinate 100
  times (`d = 300`, `ρ = 2`) gives the same numbers, so this is not a finite-`d` artefact.
* *In the paper's own simulation setup* (Remark 2.7): `η*(x₀) = 0.020322` for `m = 10` and
  `0.021315` for `m = 50`, both above `2/λ_1 = 0.02`, although `θ₀ = 0.962, 0.998` satisfy the
  hypothesis (`e_ℬ/(e_ℬ+e_𝒟) = 0.026, 0.001`).
* *Where the proofs fail.* The proof of Theorem 8 bounds `−q_t` without its factor 2 (the appendix
  restatement has the factor 2), and it uses `∑_𝒟 λ_j⁴c_j² ≥ λ_kλ_1 s^𝒟`, which does not follow from
  `λ_j ≥ λ_k`. The proof of Corollary 9 needs `λ_1(λ_1−λ_d) ≤ λ_kλ_1 − λ_{k+1}λ_d`, i.e.
  `λ_1(λ_1−λ_k) ≤ λ_d(λ_1−λ_{k+1})`, which fails as soon as the dominant block is spread.
* *What is true.* Under Deng's hypothesis `s^ℬe_𝒟 − s^𝒟e_ℬ ≥ 0`, so `p_t ≥ p₀ > 0` and
  `η*_t ≤ η*₀ ≤ 2/(λ_k + λ_d)` (Theorem 2.1). The appendix form
  `η*₀ ≤ 2(λ_1−λ_d)/(λ_kλ_1−λ_{k+1}λ_d)` is also true but weaker: with `μ_S := τ^S/s^S`,
  `u^𝒟/s^𝒟 ≥ λ_kμ_𝒟` and `u^ℬ/s^ℬ ≤ λ_{k+1}μ_ℬ` give
  `η*₀ ≤ 2(μ_𝒟−μ_ℬ)/(λ_kμ_𝒟 − λ_{k+1}μ_ℬ)`, which is increasing in `μ_𝒟 ≤ λ_1` and decreasing in
  `μ_ℬ ≥ λ_d`; and `(λ_1−λ_d)(λ_k+λ_d) − (λ_kλ_1−λ_{k+1}λ_d) = λ_d((λ_1−λ_k)+(λ_{k+1}−λ_d)) ≥ 0`.
  `η* ≤ 2/λ_1` holds when `λ_1 ≤ λ_k + λ_d`.
* *Random search* (A5: 4000 noise-free instances, `d ≤ 11`): Theorem 8 (main text) violated 2539
  times, Corollary 9 violated 1329 times, appendix version 0, bounds of Theorem 2.1 0.

---

## 3. Model (M2): `L(W) = ½ tr(WᵀAW)`

### 3.1 Commuting states: exact per-mode dynamics

**Definition.** A state is *commuting* if the rows of `C = UᵀW` are mutually orthogonal:
`C = diag(a) Q` with `a_i ≥ 0` and `Q ∈ ℝ^{d×n}` such that `QQᵀ = diag(1[a_i > 0])` (unit rows `q_i`
on the support of `a`, which must have at most `n` elements). Equivalently `CCᵀ = diag(a_i²)`.
(Name: then `WWᵀ` commutes with `A`. Conversely, if `WWᵀ` commutes with `A`, an eigenbasis `U` of `A`
can be chosen for which the state is commuting.) The clean gradient is then

    Uᵀ(AW) = ΛC = diag(σ_i) Q,        σ_i = λ_i a_i,

which is a singular value decomposition: **the left singular vectors of the gradient are the Hessian
eigenvectors**, the singular values are `σ_i`, the right singular vectors are the `q_i`.

For a spectrum-dependent filter (Echelon, NS5), `f` below means the scalar function determined by
the multiset `{σ_j}`. Define the **effective curvature**

    ν_i := f(σ_i)/a_i = λ_i γ(σ_i)      (a_i > 0),          ν_i := 0  (a_i = 0).

**Theorem 3.1 (per-mode dynamics) [PROVED].** At a commuting state, noise-free,

    UᵀF(AW) = diag(f(σ_i)) Q,       C₊ = diag(a_i − η f(σ_i)) Q,       c_i⁺ = (1 − η ν_i) c_i.

The new state is commuting with the same `Q`; in the signed coordinate `α_i := ⟨c_i, q_i⟩` the whole
noise-free trajectory is the scalar recursion `α_i ← α_i − η · sign(α_i) f(λ_i|α_i|)`.

*Proof.* `(ΛC)(ΛC)ᵀ = diag(σ_i²)`, so by Lemma 1.1 `F(ΛC) = h(diag(σ_i²)) diag(σ_i) Q =
diag(h(σ_i²)σ_i) Q = diag(f(σ_i)) Q` (using `f(0) = 0`; no distinctness of the `σ_i` is needed).
Then `C₊ = C − ηF(ΛC)` and `a_i − ηf(σ_i) = (1 − ην_i)a_i`. If `a_i − ηf(σ_i) < 0` the row is
`|a_i − ηf(σ_i)|·(−q_i)`: still a commuting state. ∎

So **Deng's per-mode factor `(1 − ηλ_i)` becomes `(1 − ην_i)`**:

| filter | `ν_i` | comment |
|---|---|---|
| SGD | `λ_i` | |
| Muon | `1/a_i = λ_i/σ_i` | the Hessian eigenvalue drops out: `a_i⁺ = |a_i − η|` |
| HTMuon(p) | `λ_i^p a_i^{p−1} = λ_i σ_i^{p−1}` | geometric interpolation |
| Echelon(r) | `λ_i/max(σ_i, τ)`, `τ = σ_{(r+1)}` | head (`σ_i > τ`): Muon; tail: SGD with step `η/τ` |

### 3.2 The comparison functional at commuting states

**Theorem 3.2 (comparison functional) [PROVED].** At a commuting state, with
`τ_f^S := ∑_{i∈S} ν_i s_i = ∑_S λ_i σ_i f(σ_i)` and `u_f^S := ∑_{i∈S} ν_i² s_i = ∑_S λ_i² f(σ_i)²`:

    s₊^S = s^S − 2η τ_f^S + η² u_f^S,
    f(η) = p_f η² + q_f η,
    q_f = 2 (s^𝒟 τ_f^ℬ − s^ℬ τ_f^𝒟) = 2 ∑_{i∈𝒟} ∑_{j∈ℬ} s_i s_j (ν_j − ν_i),
    p_f = s^ℬ u_f^𝒟 − s^𝒟 u_f^ℬ    =   ∑_{i∈𝒟} ∑_{j∈ℬ} s_i s_j (ν_i² − ν_j²),
    L₊ − L = −η ∑_i σ_i f(σ_i) + (η²/2) ∑_i λ_i f(σ_i)² = ∑_i ℓ_i (−η ν_i + η² ν_i²/2).

These are Deng's `q_t, p_t` (noise-free) with `λ_i³c_i² → ν_i s_i`, `λ_i⁴c_i² → ν_i² s_i`: **the
weights `s_i = λ_i²a_i²` keep their Hessian dependence, the curvature `λ_i` is replaced by `ν_i`.**

*Proof.* Theorem 3.1 gives `φ_i = f(σ_i)q_i`, so `⟨c_i, φ_i⟩ = a_if(σ_i)`, `‖φ_i‖² = f(σ_i)²`,
`T^S = ∑_S λ_i²a_if(σ_i) = ∑_S ν_is_i`, `V^S = ∑_S λ_i²f(σ_i)² = ∑_S ν_i²s_i`; apply Lemmas 1.2 and
1.4. The double sums are `s^𝒟τ_f^ℬ − s^ℬτ_f^𝒟 = ∑_{i∈𝒟,j∈ℬ} s_is_j(ν_j − ν_i)` etc. ∎

### 3.3 Critical step size, dichotomy, reversed dichotomy

**Effective separation.** Let `supp S := {i ∈ S : a_i > 0}` and

    (S+)   min_{i ∈ supp 𝒟} ν_i  >  max_{j ∈ supp ℬ} ν_j,        (S−)   max_{supp 𝒟} ν_i  <  min_{supp ℬ} ν_j.

For SGD (S+) is the Hessian gap `λ_k > λ_{k+1}` and always holds.

**Theorem 3.3 (critical step size; dichotomy and reversed dichotomy) [PROVED].** Commuting state,
`s^𝒟, s^ℬ > 0`, `η > 0`, `s₊ > 0`.
(a) Under (S+): `q_f < 0 < p_f`, `η*_f := −q_f/p_f > 0`,

    2/(max_𝒟 ν + max_ℬ ν)  ≤  η*_f  ≤  2/(min_𝒟 ν + min_ℬ ν),

and `θ₊ < θ ⟺ η < η*_f`, `θ₊ = θ ⟺ η = η*_f`, `θ₊ > θ ⟺ η > η*_f` (Deng's dichotomy).
(b) Under (S−): `p_f < 0 < q_f`, the same bounds hold for `η*_f = −q_f/p_f`, and the dichotomy is
**reversed**: `θ₊ > θ ⟺ η < η*_f`, `θ₊ < θ ⟺ η > η*_f`.
(c) Without separation all four sign patterns of `(q_f, p_f)` occur (Proposition 4.2), including
`q_f, p_f < 0` (alignment decreases for every `η`) and `q_f, p_f > 0` (increases for every `η`),
with no noise.

*Proof.* (a) Every pair `(i, j) ∈ supp 𝒟 × supp ℬ` has `s_is_j > 0`, `ν_j − ν_i < 0` and
`ν_i² − ν_j² = (ν_i−ν_j)(ν_i+ν_j) > 0` (`ν ≥ 0`), and there is at least one pair. With
`w_ij := s_is_j(ν_i − ν_j) > 0`, `1/η*_f = ∑ w_ij (ν_i+ν_j)/2 / ∑ w_ij`, a weighted mean of
`(ν_i+ν_j)/2`. The trichotomy is Lemma 1.2: `sign(θ₊−θ) = sign(p_fη + q_f)`. (b) Same with all signs
reversed (`w_ij < 0`). ∎

**Corollary 3.4 (scaling law) [PROVED].** If `f` is homogeneous of degree `p` (`f(tσ) = t^pf(σ)`;
SGD `p=1`, HTMuon `p`, Muon/Echelon/NS5 `p = 0`) then `ν_i(tC) = t^{p−1}ν_i(C)`,
`q_f(tC) = t^{3+p}q_f(C)`, `p_f(tC) = t^{2+2p}p_f(C)`, hence `η*_f(tC) = t^{1−p} η*_f(C)`.
For `p < 1` the critical step size shrinks with the state: with a fixed `η` the alignment regime is
selected by the *size of the coefficients*, as in Corollary 2.2.

Validation (C2–C6): 28 random commuting states (`(d,n)` from `(50,50)` to `(200,220)` and two
rank-deficient tall cases `(120,60)`, `(200,90)`; `m ∈ {1.5, 3, 10, 100}`; log-normal row norms with
independent block scales), 9 filters (SGD, Muon, HTMuon(1/8, 1/4, 1/2), NS5, Echelon(0, k, 3k)),
6 step sizes each, everything through numpy's SVD of the actual `d×n` gradient. Maximal
discrepancies over all filters: filtered gradient vs `diag(f(σ))Q` `2.2e-12` (relative); row norms
after the step `1.6e-12`; off-diagonal Gram entries after the step `2.0e-12`; `s₊^𝒟, s₊^ℬ`
`3.3e-14`; `θ₊−θ` absolute `2.4e-15`; loss change `2.3e-13`; `f(η)` vs `p_fη²+q_fη` `7.7e-15`;
`|θ₊−θ|` at `η*_f` `1.4e-15`; sign pattern around the root 0 violations in 500 tests; scaling law
`9.4e-15` (NS5: `2.3e-8`, the `1e-7` regulariser in its normalisation). Bounds and (reversed)
dichotomy under (S+)/(S−) (C6): 250 tests, 0 violations.

### 3.4 Arbitrary states: Gram formulas

**Theorem 3.5 (Gram formulas) [PROVED].** Let `f` be index-wise, `W` arbitrary, noise-free, and
`M := (ΛC)(ΛC)ᵀ = Λ CCᵀ Λ` (the Gram matrix of the gradient rows in the Hessian eigenbasis),
`g₁(t) := √t f(√t)`, `g₂(t) := f(√t)²`, `P_S := diag(1[i ∈ S])`. Then `Φ = h(M)ΛC` and

    T^S = tr(P_S Λ g₁(M)),    V^S = tr(P_S Λ² g₂(M)),    N^S = tr(P_S g₁(M)),    R^S = tr(P_S Λ g₂(M)).

Hence `q, p`, `θ₊−θ` and all loss changes depend on the state only through `M`. With a noisy gradient
`Γ = ΛC + UᵀΞ` the same holds with `Φ = h(ΓΓᵀ)Γ`: `T^S = tr(P_S Λ² CΓᵀ h(ΓΓᵀ))`,
`V^S = tr(P_S Λ² g₂(ΓΓᵀ))`, `N^S = tr(P_S Λ CΓᵀ h(ΓΓᵀ))`, `R^S = tr(P_S Λ g₂(ΓΓᵀ))`.

*Proof.* Lemma 1.1. `∑_{S} λ_i²⟨c_i, φ_i⟩ = tr(P_SΛ² CΦᵀ) = tr(P_SΛ·ΛCCᵀΛ·h(M)) = tr(P_SΛ M h(M))`
and `M h(M) = g₁(M)`; `∑_S λ_i²‖φ_i‖² = tr(P_SΛ² h(M)Mh(M)) = tr(P_SΛ² g₂(M))`; same for `N, R`. ∎

For SGD `g₁(t) = g₂(t) = t` and only the diagonal `M_ii = σ_i²` enters: *the row-norm formulas of
Theorem 3.2 are exact for SGD at every state* (this is why Deng's vector analysis lifts verbatim to
(M2) for SGD). At a commuting state `M = diag(σ_i²)` and Theorem 3.5 reduces to Theorem 3.2.

**Proposition 3.6 (the commuting formulas are upper bounds for sub-linear filters) [PROVED].**
If `g₁` and `g₂` are concave on `[0,∞)` (HTMuon(p), `0 < p ≤ 1`; for Muon `g₁ = √t` is concave and
`g₂ = 1[t>0] ≤ 1`), then at every state, with `a_i = ‖c_i‖`, `σ_i = λ_ia_i`:

    T^S ≤ ∑_S λ_i σ_i f(σ_i),   V^S ≤ ∑_S λ_i² f(σ_i)²,   N^S ≤ ∑_S σ_i f(σ_i),   R^S ≤ ∑_S λ_i f(σ_i)²,

with equality at commuting states. Moreover (project-then-filter, Section 5)
`tr(P_S g₁(M)) ≤ tr(g₁(P_S M P_S))`.

*Proof.* For a unit vector `e` and a concave `g`, `⟨e, g(M)e⟩ ≤ g(⟨e, Me⟩)` (Jensen for the spectral
measure of `M` in the state `e`); take `e = e_i`, `⟨e_i, Me_i⟩ = σ_i²`, and sum with the positive
weights `λ_i, λ_i², 1`. For the last claim take for `e` the eigenvectors of `P_SMP_S` in the range of
`P_S`. ∎

(These one-sided bounds do not control the differences `q, p`.)

Validation (G1, G4, G5): 24 generic states (Gaussian rows with heterogeneous scales and a random
column covariance; `(d,n)` from `(50,50)` to `(150,400)` and tall `(90,40)`, `(160,100)`), filters
SGD/Muon/HTMuon(1/8, 1/4, 1/2): Gram formulas vs direct SVD — max relative error of
`T^S, V^S` `3.9e-12`, of `s₊^S` `7.2e-12`, of `θ₊−θ` (absolute) `1.1e-13`, of the loss thresholds
`3.1e-12`. Jensen bounds: 576 tests, 0 violations. SGD row-norm formulas exact to `6.9e-13`.

### 3.5 Muon: pinning of the quadratic coefficient, for every state and every noise

**Theorem 3.7 (pinning) [PROVED].** Let `d ≤ n` and let `G ∈ ℝ^{d×n}` be *any* matrix of full row
rank (the clean gradient, or a stochastic gradient with arbitrary noise). The Muon direction
`O = msign(G) = (GGᵀ)^{−1/2}G` satisfies `OOᵀ = I_d`, so the rows of `Φ = UᵀO` are orthonormal and

    V^S = ψ_S,     R^S = tr_S,     θ_upd = θ_iso,     p = s^ℬψ_𝒟 − s^𝒟ψ_ℬ = s ψ (θ_iso − θ)

for every state `W` — commuting or not — and for every realisation of the noise. Consequently:
`p > 0 ⟺ θ < θ_iso`; `θ₊ → θ_iso` as `η → ∞`; and the second-order term of every (projected) loss
change, `(η²/2) tr_S`, depends neither on the state nor on the noise.

*Proof.* `OOᵀ = (GGᵀ)^{−1/2}GGᵀ(GGᵀ)^{−1/2} = I`; `ΦΦᵀ = UᵀOOᵀU = I`, so `‖φ_i‖ = 1`. Lemma 1.3. ∎

(If `d > n` or `G` is rank-deficient, `OOᵀ = Π` is the projector onto the column space of `G` and
`‖φ_i‖² = (UᵀΠU)_ii ≤ 1`; the pinning fails and Theorem 3.5 must be used.)

For SGD, Deng needs the two thresholds `g_gap < θ*` to control the sign of `p_t`
(`θ ≤ g_gap ⇒ p_t > 0`, `θ ≥ θ* ⇒ p_t ≤ 0`), and both depend on the noise. **For Muon the two
thresholds collapse to the single, noise-independent value `θ_iso`**, and `1 − θ_iso ≤ 1/(1+ρm²)`
keeps Deng's `Θ(m^{−2})` gap dependence.

**Theorem 3.8 (large steps attract the alignment to `θ_iso`) [PROVED].** Under the hypotheses of
Theorem 3.7, with `s^𝒟, s^ℬ > 0`, `θ ≠ θ_iso`, let `ā_S := √(s^S/ψ_S)` (a `λ²`-weighted RMS of the row
norms of block `S`) and

    η_att := 2 / |1/ā_𝒟 − 1/ā_ℬ|.

Then `|q| ≤ 2√(s^𝒟s^ℬ)(√(s^𝒟ψ_ℬ) + √(s^ℬψ_𝒟))`, and for every `η > η_att` (with `s₊ > 0`)
`sign(θ₊ − θ) = sign(θ_iso − θ)`, for every state and every noise realisation.

*Proof.* `|T^S| ≤ ∑_S λ_i²a_i‖φ_i‖ = ∑_S λ_i·λ_ia_i ≤ √(ψ_Ss^S)` (Cauchy–Schwarz, `‖φ_i‖ = 1`), so
`|q| ≤ 2(s^𝒟√(ψ_ℬs^ℬ) + s^ℬ√(ψ_𝒟s^𝒟))`. Also
`|p| = |√(s^ℬψ_𝒟) − √(s^𝒟ψ_ℬ)|·(√(s^ℬψ_𝒟) + √(s^𝒟ψ_ℬ))`. Hence
`|q|/|p| ≤ 2√(s^𝒟s^ℬ)/|√(s^ℬψ_𝒟) − √(s^𝒟ψ_ℬ)| = η_att`, and for `η > |q|/|p|` the sign of `pη + q`
is the sign of `p`. ∎

Validation (G2, G3): 20 generic states × 5 noise types (none; i.i.d. Gaussian of twice the gradient
scale; Gaussian with row- and column-heteroscedastic variances; Student-t(2.5); rank-one), `(d,n)`
from `(40,40)` to `(150,300)`: `max |‖φ_i‖ − 1| = 1.8e-15`; `p` recovered from two direct
evaluations of `f(η)` vs `sψ(θ_iso−θ)`: `4.6e-16` relative; attraction for `η = η_att·{1.001, 1.5, 6}`:
300 tests, 0 violations; `|θ₊ − θ_iso| ≤ 3.7e-8` at `η = 10⁷η_att`; `max |q|/bound = 0.69`.

### 3.6 Noise that preserves the commuting structure

Let the state be commuting, `C = diag(a)Q`. A noise matrix `Ξ` keeps the stochastic gradient in the
same singular frame — and therefore the next state commuting, per realisation — if it is
**co-diagonal**: `UᵀΞ = diag(ζ)Q`, i.e. noise along the current gradient's own singular directions.
(More generally: if the rows of `ΛC + UᵀΞ` are mutually orthogonal and row `i` is orthogonal to
`c_j`, `j ≠ i`. A generic matrix noise, e.g. i.i.d. Gaussian entries, destroys the commuting
structure with probability one: Section 3.7.)

Write `f_odd(x) := sign(x) f(|x|)`.

**Theorem 3.9 (co-diagonal noise; Gaussian-smoothed filter) [PROVED].**
(a) (per realisation) `UᵀF(AW + Ξ) = diag(f_odd(σ_i + ζ_i)) Q`, so in signed coordinates
`α_i⁺ = α_i − η f_odd(λ_iα_i + ζ_i)` and the new state is commuting with the same `Q`.
(For spectrum-dependent filters `f` is determined by the multiset `{|σ_j + ζ_j|}`.)
(b) If `f` is index-wise and `ζ_i ~ N(0, κ_i²)` (any dependence between different `i`), with

    f̄_i(σ) := E f_odd(σ + ζ_i),          f2_i(σ) := E f(|σ + ζ_i|)²,

then `E α_i⁺ = α_i − η f̄_i(σ_i)`, and

    E s₊^S = s^S − 2η ∑_S λ_i σ_i f̄_i(σ_i) + η² ∑_S λ_i² f2_i(σ_i),
    E f(η) = p̄ η² + q̄ η,   q̄ = 2 ∑_{i∈𝒟,j∈ℬ} s_i s_j (ν̄_j − ν̄_i),   p̄ = s^ℬ ∑_𝒟 λ_i² f2_i − s^𝒟 ∑_ℬ λ_j² f2_j,

with the noise-averaged effective curvature `ν̄_i := f̄_i(σ_i)/a_i`.
(c) Closed forms. Muon: `f̄(σ) = erf(σ/(√2 κ))`, `f2 = 1`. HTMuon(p):

    f̄(σ) = σ κ^{p−1} 2^{(p+1)/2} Γ(p/2+1)/√π · ₁F₁((1−p)/2; 3/2; −σ²/(2κ²)),
    f2(σ) = κ^{2p} 2^p Γ(p+1/2)/√π · ₁F₁(−p; 1/2; −σ²/(2κ²)).

*Proof.* (a) `Uᵀ(AW+Ξ) = diag(σ_i+ζ_i)Q` has Gram matrix `diag((σ_i+ζ_i)²)`; Lemma 1.1 gives
`F = diag(h((σ_i+ζ_i)²)(σ_i+ζ_i))Q = diag(f_odd(σ_i+ζ_i))Q`. (b) Linearity of expectation in
Lemma 1.2: `T^S = ∑_S λ_i²a_i f_odd(σ_i+ζ_i)`, `V^S = ∑_S λ_i² f(|σ_i+ζ_i|)²`. (c) `E sign(X) =
erf(σ/(√2κ))` for `X ~ N(σ,κ²)`; the HTMuon expressions are the signed and absolute moments of a
Gaussian (Kummer-function form); used here as **[NUMERICAL]** facts: they agree with adaptive
quadrature to `1.8e-15` and `2.7e-15` (N2). ∎

**Corollary 3.10 (noise-dominated regime = renormalised SGD) [PROVED for the leading order].**
Let `κ_i = κ` and `σ_i ≪ κ` for all `i`. To first order in `σ/κ`,
`f̄(σ) = χ σ (1 + O(σ²/κ²))` with `χ := E[f_odd(ζ)ζ]/κ² = 2^{(p+1)/2}Γ(p/2+1)/√π · κ^{p−1}` (Muon:
`χ = √(2/π)/κ`), and `f2(σ) = f2(0)(1 + O(σ²/κ²))`, `f2(0) = κ^{2p}2^pΓ(p+1/2)/√π`. Hence

    E s₊^S ≈ s^S − 2(ηχ) τ^S + (ηχ)² κ_eff² ψ_S,      κ_eff² := f2(0)/χ² = κ² √π Γ(p+1/2) / (2 Γ(p/2+1)²),

which is Deng's SGD formula `s^S − 2η'τ^S + η'²(u^S + κ_eff²ψ_S)` with `η' = ηχ` up to the term
`η'²u^S`, itself `O(σ²/κ²)` relative to `η'²κ_eff²ψ_S`. In particular `ν̄_i ≈ χλ_i`: **the effective
curvatures are proportional to the Hessian eigenvalues again, `q̄ ≈ χ q₀ < 0`, and Deng's sign
facts and gap dependence are restored** (`κ_eff² = (π/2)κ²` for Muon, `κ²` for SGD).

*Proof.* `f̄(σ) = E f_odd(σ+ζ)` is odd and smooth in `σ` (Gaussian smoothing) with derivative at 0
equal to `E[f_odd(ζ)ζ]/κ²` (Stein); the constants follow from (c) with `₁F₁(·;·;0) = 1`. ∎

Validation: per-realisation map (N1; `d = 60, n = 80`, heterogeneous `κ_i`, 60 realisations, 6
filters incl. NS5 and Echelon(k)): signed coordinates `7.2e-15`, off-diagonal Gram `5.3e-15`,
`s₊^S` `8.0e-15`. Monte Carlo through the direct SVD (N3; `d = 40, n = 50`, `κ/median σ ∈ {0.3, 3}`,
Muon/HTMuon(1/8)/HTMuon(1/2), 3000 samples): `E s₊^𝒟, E s₊^ℬ` and the expected projected loss
changes at the predicted thresholds, 24 z-scores, `max |z| = 1.49`, relative errors `≤ 1.6e-3`.
Linear-response slope `χ`: `9.9e-10`. Corollary 3.10 (E3): relative deviation of the exact smoothed
sums from the renormalised Deng sums `3.6e-3, 3.6e-5, 3.6e-7` for `max σ/κ = 10⁻¹, 10⁻², 10⁻³`
(quadratic convergence, all three filters within a factor 1.5 of these numbers).
Sign of `q̄` under Muon at a two-level state above `θ_iso` (E5; direct SVD, 1500 samples): `q̄ > 0`
for `κ/σ_ℬ ∈ {0.01, 0.3, 1}`, `q̄ < 0` for `κ/σ_ℬ ∈ {3, 10, 100}`; Monte-Carlo vs formula `|z| ≤ 1.5`.

### 3.7 I.i.d. matrix noise

Let `Ξ` have i.i.d. `N(0, ς²)` entries and let the state be commuting, `C = diag(a)Q`, `d ≤ n`, all
`a_i > 0`. Complete `Q` to an orthogonal `Q̃ ∈ ℝ^{n×n}` and set `Y := UᵀF(G)Q̃ᵀ ∈ ℝ^{d×n}` (coordinates
of the update in the frame `(u_i, q̃_j)`).

**Lemma 3.11 (symmetry) [PROVED].** `E Y_ij = 0` for `j ≠ i`, and `E[ΦΦᵀ]` is diagonal. Hence

    E c_i⁺ = (1 − η m_i/a_i) c_i,   m_i := E Y_ii,       E s₊^S = s^S − 2η ∑_S λ_i²a_im_i + η² ∑_S λ_i² v_i,   v_i := E‖φ_i‖²:

the *mean* state stays commuting with noise-averaged curvature `ν̄_i = m_i/a_i`, although individual
realisations do not. For Muon `v_i = 1` (Theorem 3.7).

*Proof.* In frame coordinates `G̃ := UᵀGQ̃ᵀ = [diag(σ) 0] + Ξ̃` with `Ξ̃` again i.i.d. `N(0,ς²)`. For
sign matrices `D₁ = diag(ε_1..ε_d)`, `D₂ = diag(ε_1..ε_d, ε'_{d+1}..ε'_n)` we have
`D₁[diag(σ) 0]D₂ = [diag(σ) 0]` and `D₁Ξ̃D₂ ~ Ξ̃`, so `D₁G̃D₂ ~ G̃`, and by Lemma 1.1
`Y = F(G̃) ~ D₁YD₂`. Thus `E Y_ij = ε_iε_j E Y_ij` (`j ≤ d`) and `E Y_ij = ε_iε'_j E Y_ij` (`j > d`);
choosing `ε_i = −1` and all other signs `+1` gives `E Y_ij = 0` for `j ≠ i`. Likewise
`(YYᵀ)_ik ~ ε_iε_k (YYᵀ)_ik`, so `E(ΦΦᵀ)_ik = E(YYᵀ)_ik = 0` for `i ≠ k`. The displayed formulas are
Lemma 1.2 with `⟨c_i, φ_i⟩ = a_iY_ii`. ∎

The proof uses only the invariance of the law of `Ξ̃` under independent sign flips of rows and
columns, so it holds for any such noise.

**Proposition 3.12 (wide limit) [HEURISTIC + NUMERICAL].** For `n → ∞` with `d` fixed and `ς²n → ϖ²`:
`ΞΞᵀ → ϖ²I_d` and `ΛCΞᵀ → 0`, so `GGᵀ → diag(σ_i² + ϖ²)` and

    m_i → σ_i γ(√(σ_i² + ϖ²)),      v_i → f(√(σ_i² + ϖ²))²,      ν̄_i → λ_i γ(√(σ_i² + ϖ²)).

I.e. the filter gain is evaluated at the **noise-inflated singular value**. If `ϖ ≫ σ_i` for all
`i`, `ν̄_i ≈ γ(ϖ)λ_i`: SGD with step `ηγ(ϖ)`, and Deng's theory (sign of `q`, gap dependence) is
restored for every filter. Numerics (N5; `d = 10`, `ϖ = median σ`, direct SVD, 1200–3000 samples):
max relative error of `m_i` for Muon `0.32, 0.060, 0.015, 0.0056, 0.0009` and for HTMuon(1/8)
`0.25, 0.051, 0.013, 0.0050, 0.0010` at `n = 10, 40, 160, 640, 2560` (decay `≈ 1/n`); of `v_i` for
HTMuon(1/8) `0.16, 0.022, 0.0053, 0.0013, 0.0004`. Symmetry lemma (N4; `d = 20, n = 30`, `4·10⁴`
samples): largest off-diagonal `|E Y_ij|` `3.5e-3` with `max |z| = 3.6` over 580 entries (consistent
with zero; diagonal means range over `0.05–1.45`); off-diagonal `E(ΦΦᵀ)` `≤ 3.9e-4`
(`max |z| = 2.8`; identically 0 for Muon).

---

## 4. Regimes, thresholds, sign facts and the role of the Hessian gap

### 4.1 What governs the one-step alignment change

By Lemma 1.2 the sign of `θ₊ − θ` is the sign of `p_fη + q_f`, and by Theorems 2.1/3.2 the pair
`(q_f, p_f)` is Deng's pair computed with the per-mode step sizes `η·γ(σ_i)`:

* SGD: `γ ≡ 1`. Noise-free, `η*₀` is invariant under `W ↦ tW`: **`η` alone** decides.
* (M1), any filter: one gain `γ(‖g‖)` for all modes. The *signs* of `q, p` are Deng's; the position
  of the critical step size scales as `‖Ax‖/f(‖Ax‖)`: `η` **and the gradient norm** decide.
* (M2), commuting: mode `i` has its own gain `γ(σ_i)`, decreasing in `σ_i` for every sub-linear
  filter. The signs of `q_f, p_f` are decided by the ordering of `ν_i = λ_iγ(σ_i)` between the two
  blocks, i.e. by the **relative size of the dominant and bulk coefficients** (Muon: by
  `a_i` alone); the overall scale of the state moves `η*_f` by Corollary 3.4.

### 4.2 Two-level states and the flip alignment

**Proposition 4.1 [PROVED].** Let the spectrum be two-level (`λ_i = λ_𝒟` on `𝒟`, `λ_ℬ` on `ℬ`,
`m = λ_𝒟/λ_ℬ`) and the commuting state two-level (`a_i = a_𝒟 > 0` on `𝒟`, `a_ℬ > 0` on `ℬ`), and let
`ν_S := f(λ_Sa_S)/a_S`. Then

    q_f = 2 s^𝒟 s^ℬ (ν_ℬ − ν_𝒟),      p_f = s^𝒟 s^ℬ (ν_𝒟² − ν_ℬ²),      η*_f = 2/(ν_𝒟 + ν_ℬ)   (ν_𝒟 ≠ ν_ℬ),

and if `ν_𝒟 = ν_ℬ` then `f(η) ≡ 0`: the alignment is invariant for **every** step size. For
HTMuon(p), `p < 1`, with `θ/(1−θ) = ρm²(a_𝒟/a_ℬ)²`:

    ν_𝒟 > ν_ℬ   ⟺   θ < θ_flip(p) := ρ m^{2/(1−p)} / (1 + ρ m^{2/(1−p)}).

So for `θ < θ_flip(p)` Deng's dichotomy holds (decrease iff `η < η*_f`), for `θ > θ_flip(p)` it is
reversed (the alignment **increases** for every `0 < η < η*_f`), and at `θ = θ_flip(p)` the alignment
does not move. `θ_flip(0) = ρm²/(1+ρm²) = θ_iso` (Muon; this is also Deng's `g_gap` for isotropic
noise), `θ_flip(1) = 1` (SGD never flips), and `1 − θ_flip(p) = 1/(1 + ρ m^{2/(1−p)})`.

*Proof.* All pairs `(i,j) ∈ 𝒟×ℬ` have the same `ν_i = ν_𝒟`, `ν_j = ν_ℬ`; use the double sums of
Theorem 3.2. `ν_𝒟/ν_ℬ = m^p (a_ℬ/a_𝒟)^{1−p} > 1 ⟺ (a_𝒟/a_ℬ)² < m^{2p/(1−p)} ⟺ θ/(1−θ) < ρ m^{2+2p/(1−p)}`. ∎

| `θ_flip(p)` | `p = 0` (Muon) | `p = 1/8` | `p = 1/4` | `p = 1/2` | `p = 1` (SGD) |
|---|---|---|---|---|---|
| `m = 3`, `ρ = 1/9` | 0.5000 | 0.5778 | 0.6753 | 0.9000 | 1 |
| `m = 10`, `ρ = 1/9` | 0.9174 | 0.9555 | 0.9810 | 0.9991 | 1 |
| `m = 2`, `ρ = 1/3` | 0.5714 | 0.6191 | 0.6791 | 0.8421 | 1 |

Validation (C7): these 12 configurations, `d ∈ {60, 100}`, direct SVD: `|θ₊ − θ| ≤ 2.2e-16` at
`θ = θ_flip` for three step sizes; `η*_f` vs `2/(ν_𝒟+ν_ℬ)` `4.6e-15`; sign pattern on both sides of
`θ_flip` (odds ratio `×{0.05, 0.5, 2, 20}`): 0 violations.

*Mechanism.* `ν = λγ(σ)` and `γ` is decreasing: a mode with a large gradient gets a small gain.
Above `θ_flip` the dominant modes — which carry the large gradient — contract *more slowly* in
relative terms than the bulk modes, so a small filtered step makes the gradient even more dominant.
Under SGD the dominant modes always contract faster (for `η < η*`), which is Deng's phase 1.

### 4.3 All four sign patterns occur under Muon, without noise

**Proposition 4.2 (counterexamples) [PROVED by direct evaluation; checked with direct SVDs, C8].**
Muon, commuting states, `n = 5`:

| `λ` | `𝒟` | `a` | `q_f` | `p_f` | behaviour for `η > 0` |
|---|---|---|---|---|---|
| `(5,1,1)` | `{1}` | `(0.5, 1, 1)` | −25 | 37.5 | Deng: decrease iff `η < η* = 2/3` |
| `(5,1,1)` | `{1}` | `(2, 1, 1)` | 200 | −150 | reversed: **increase** iff `η < η* = 4/3` |
| `(5,1,1)` | `{1}` | `(0.8, 0.05, 1)` | −6.5 | −6.9375 | decrease for **every** `η` |
| `(5,5,1)` | `{1,2}` | `(0.05, 1, 0.8)` | 6.5 | 6.9375 | increase for **every** `η` |

(E.g. row 3: `s = (16, 0.0025, 1)`, `ν = (1.25, 20, 1)`,
`q = 2[16·0.0025·(20−1.25) + 16·1·(1−1.25)] = −6.5`, `p = 16·0.0025·(1.25²−20²) + 16·(1.25²−1) = −6.9375`.)
Rows 3–4 are consistent with Theorem 3.7: `θ = 0.941 > θ_iso = 0.926` and `θ = 0.975 < θ_iso = 0.980`.
On a grid of 400 step sizes in `[10⁻³, 20]` the fractions of step sizes with a decrease are
`0.655, 0.275, 1, 0`. In the random commuting states of C2–C5 (28 states): SGD and Echelon(0) always
`(q<0, p>0)`; Muon 14×`(q<0,p>0)` and 14×`(q>0,p<0)`; HTMuon(1/8) and (1/4) 16/12; HTMuon(1/2) 22/6;
Echelon(k) 16/11 and one `(q>0,p>0)`.

So Deng's sign fact "`q_t < 0` because `λ_k > λ_{k+1}`" **does not survive** in (M2) for sub-linear
filters; what survives is its abstract form "`q_f < 0` because `ν_i > ν_j`" (Theorem 3.3).

### 4.4 When does the Hessian gap still decide?

**Proposition 4.3 [PROVED].** HTMuon(p), `0 ≤ p ≤ 1`, commuting state with all `a_i > 0`.
(a) (S+) holds if `m^p > (max_𝒟 a / min_ℬ a)^{1−p}`; it also holds if
`m > (max_𝒟 σ / min_ℬ σ)^{1−p}` (a second sufficient condition, in terms of gradient row norms).
(b) (S−) holds if `(λ_1/λ_d)^p < (min_𝒟 a / max_ℬ a)^{1−p}`.
(c) At isotropic states (`a_i ≡ a`) and `p > 0`: (S+) holds with effective gap
`min_𝒟ν/max_ℬν = m^p`, and `2a^{1−p}/(λ_1^p+λ_{k+1}^p) ≤ η*_f ≤ 2a^{1−p}/(λ_k^p+λ_d^p)`. For Muon
(`p = 0`) at isotropic states `q_f = p_f = 0`: the alignment is invariant for every `η`.

*Proof.* `ν_i = λ_i^pa_i^{p−1} = λ_iσ_i^{p−1}`. (a) `min_𝒟ν ≥ λ_k^p(max_𝒟a)^{p−1}` and
`max_ℬν ≤ λ_{k+1}^p(min_ℬa)^{p−1}`; or `min_𝒟ν ≥ λ_k(max_𝒟σ)^{p−1}`, `max_ℬν ≤ λ_{k+1}(min_ℬσ)^{p−1}`.
(b) `max_𝒟ν ≤ λ_1^p(min_𝒟a)^{p−1}`, `min_ℬν ≥ λ_d^p(max_ℬa)^{p−1}`. (c) `ν_i = a^{p−1}λ_i^p`;
Theorem 3.3. ∎

So the gap dependence is **weakened, not removed, for `p > 0`**: against a given spread of
*coefficients* the gap acts with the reduced power `m^p` (HTMuon(1/8): a coefficient ratio 2 between
the blocks is compensated only by `m > 2⁷ = 128`); against a given spread of *gradient row norms* it
acts with full power. For Muon (`p = 0`) the coefficient form of (a) does not involve `m` at all:
the gap is **removed** from the sign of `q_f`, while it is fully retained in the sign of `p`
(Theorem 3.7: `θ_iso → 1` as `m → ∞`).

Numerics (`gap_dependence.py`; `d = 100, k = 10, n = 120`, 20 commuting states with i.i.d.
log-normal(0, 0.5) row norms, direct SVD). Fraction of states with `q_f < 0` at
`m = 2, 5, 20, 100, 1000`:

| filter | same law of `a_i` on both blocks | dominant rows rescaled to `θ = 0.99` |
|---|---|---|
| SGD, Echelon(0) | 1, 1, 1, 1, 1 | 1, 1, 1, 1, 1 |
| HTMuon(1/2) | 1, 1, 1, 1, 1 | 0.60, 1, 1, 1, 1 |
| HTMuon(1/4) | 0.95, 0.95, 1, 1, 1 | 0, 0.90, 1, 1, 1 |
| HTMuon(1/8) | 0.85, 0.90, 0.95, 1, 1 | 0, 0, 1, 1, 1 |
| Muon | 0.65, 0.65, 0.65, 0.65, 0.65 | 0, 0, 1, 1, 1 |
| Echelon(k) | 0.95, 1, 1, 1, 1 | 0, 0.85, 1, 1, 1 |

### 4.5 Echelon(r)

**Proposition 4.4 [PROVED].** Commuting state, exact frame, `τ` the `(r+1)`-th largest of the `σ_j`
(Muon if there are at most `r` non-zero `σ_j`). Then `f(σ_i) = min(σ_i,τ)/τ` and

    ν_i = λ_i / max(σ_i, τ):     head (σ_i > τ): ν_i = 1/a_i;      tail (σ_i ≤ τ): ν_i = λ_i/τ.

(a) `r = 0`: `ν_i = λ_i/‖AW‖₂` for all `i`: Echelon(0) is noise-free SGD with step `η/‖AW‖₂`; (S+)
always holds and `η*_Ech(0) = ‖AW‖₂·η*₀`.
(b) For two tail modes `ν_i/ν_j = λ_i/λ_j` (the Hessian ratio is kept exactly); for two head modes
`ν_i/ν_j = a_j/a_i` (Muon); for a head mode `j` and a tail mode `i`,
`ν_j/ν_i = (λ_j/λ_i)·(τ/σ_j)`: the Hessian ratio divided by the clipping ratio `σ_j/τ > 1`.
(c) If the head is exactly the dominant block (`r = k`, `min_𝒟σ > max_ℬσ = τ`):
(S+) `⟺ max_𝒟 a_i < τ/λ_{k+1}`, and (S+) for Muon at the same state implies (S+) for Echelon(k).

*Proof.* `f(σ)/a = λ min(σ,τ)/(τσ) = λ/max(σ,τ)`. (a) `τ = σ_max`. (b) Direct. (c) `min_𝒟ν = 1/max_𝒟a`,
`max_ℬν = λ_{k+1}/τ`; and `λ_j/τ ≤ λ_j/σ_j = 1/a_j` on `ℬ`, so `max_ℬν^{Ech} ≤ max_ℬν^{Muon}` while
the dominant values coincide. ∎

Validation (E6): 100 random states, `r ∈ [1, 30)`: `ν` vs the formula `3.1e-16`.
In (M1) Echelon(r) = Muon for every `r` (rank one), checked to machine precision (A1).

---

## 5. Projected filtered updates (analogue of Deng's Theorems 10–13)

### 5.1 Two notions and when they coincide

For a block `S ∈ {𝒟, ℬ}` with projector `P^S = ∑_{i∈S} u_iu_iᵀ` (acting on the left):

    FP_S(G) := P^S F(G)      "filter, then project the update",
    PF_S(G) := F(P^S G)      "project the gradient, then filter".

Deng's DSGD/BSGD use `P^S(Ax+ξ)`; for SGD both notions reduce to it. `FP` decomposes one actual
optimizer step into its dominant and bulk parts; `PF` runs the optimizer on the projected gradient.

**Proposition 5.1 (coincidence) [PROVED (a,b,d); NUMERICAL (c)].**
(a) SGD: `FP_S = PF_S` always.
(b) Index-wise filter and *block-commuting* gradient, `(P^𝒟G)(P^ℬG)ᵀ = 0` (the row spaces of the
dominant and bulk blocks of `UᵀG` are orthogonal; in particular commuting states, also with
co-diagonal noise): `FP_S(G) = PF_S(G)`.
(c) They differ otherwise: for generic Gaussian states `‖FP_S − PF_S‖_F/‖FP_S‖_F ∈ [0.49, 0.61]`
(Muon, HTMuon; P1), and for spectrum-dependent filters even at commuting states (Echelon: `FP` uses
the global `τ = σ_{r+1}(G)`, `PF` the block value `σ_{r+1}(P^SG)`; relative difference `0.38`–`3.1`).
(d) (M1): `FP_S(g) = γ(‖g‖)P^Sg`, `PF_S(g) = γ(‖P^Sg‖)P^Sg`.

*Proof.* (b) In eigen-coordinates `ΓΓᵀ = M_𝒟𝒟 ⊕ M_ℬℬ`, so `h(ΓΓᵀ) = h(M_𝒟𝒟) ⊕ h(M_ℬℬ)` and
`P_Sh(ΓΓᵀ)Γ = h(M_SS)P_SΓ = h((P_SΓ)(P_SΓ)ᵀ)P_SΓ` (using `h(0) = 0`), which is `F(P_SΓ)` by Lemma 1.1. ∎

(P1: for commuting and block-commuting states and index-wise filters the two notions agree to
`5.8e-13`.)

### 5.2 Exact loss thresholds for arbitrary states

**Theorem 5.2 [PROVED].** Noise-free, any state, any filter. For an update `Δ` with `⟨AW,Δ⟩ > 0`,
the loss decreases iff `0 < η < 2⟨AW,Δ⟩/⟨Δ,AΔ⟩` (Lemma 1.4). Hence

    η_S^{FP} = 2 N^S/R^S = 2 tr(P_S g₁(M)) / tr(P_S Λ g₂(M)),
    η_S^{PF} = 2 tr(g₁(M_SS)) / tr(Λ_S g₂(M_SS)),            M_SS := P_S M P_S restricted to S

(Gram forms for index-wise `f`). Moreover
(a) (additivity of `FP`) `L(W − ηF(G)) − L(W) = ∑_{S∈{𝒟,ℬ}} [L(W − ηFP_S(G)) − L(W)]`;
(b) for concave `g₁`, `N^S_{FP} ≤ N^S_{PF}`;
(c) Muon, `d ≤ n`, `AW` of full row rank: `η_S^{FP} = 2 tr(P_S M^{1/2})/tr_S` and
`η_S^{PF} = 2‖P^SAW‖_*/tr_S` (nuclear norm of the projected gradient over the trace of the Hessian
block).

*Proof.* Gram forms: Theorem 3.5, applied for `PF` to the gradient `P_SΓ` with Gram matrix `M_SS`.
(a) `F = FP_𝒟 + FP_ℬ` and `⟨FP_𝒟, A·FP_ℬ⟩ = 0` because `P^𝒟AP^ℬ = 0`; the first-order terms add.
(b) Proposition 3.6. (c) Theorem 3.7 (`R^S = tr_S`), `g₁(t) = √t`; for `PF` the polar factor of the
full-row-rank block `P_SΓ` has orthonormal rows on `S`, and `tr(M_SS^{1/2})` is the nuclear norm. ∎

Validation (P2, P4): 20 generic states, 8 filters (incl. NS5, Echelon(k), Echelon(2k)), both
notions: loss identity `7.9e-15` (relative to `L`), loss change at the threshold `9.1e-16`;
additivity `≤ 1.1e-11`.

### 5.3 Commuting states: thresholds, ordering, window

**Theorem 5.3 [PROVED].** Commuting state, noise-free; index-wise filter (then `FP = PF`) or
spectrum-dependent filter with `FP`. With `w_i := σ_if(σ_i) = ν_iℓ_i ≥ 0`:

    η_S^loss = 2 ∑_{i∈S} σ_i f(σ_i) / ∑_{i∈S} λ_i f(σ_i)² = 2/⟨ν⟩_S,       ⟨ν⟩_S := ∑_S ν_i w_i / ∑_S w_i,

the loss of the `S`-projected step decreases iff `0 < η < η_S^loss` and increases iff `η > η_S^loss`
(`s^S > 0`). Consequently
(a) `η_𝒟^loss < η_ℬ^loss ⟺ ⟨ν⟩_𝒟 > ⟨ν⟩_ℬ`;
(b) under (S+): `η_ℬ^loss/η_𝒟^loss ≥ min_𝒟ν/max_ℬν > 1`, and for every `η ∈ (η_𝒟^loss, η_ℬ^loss)` the
dominant-projected update increases the loss while the bulk-projected one decreases it
(the suspicious-alignment window);
(c) under (S−): `η_𝒟^loss/η_ℬ^loss ≥ min_ℬν/max_𝒟ν > 1`: the window is **reversed** — the
bulk-projected update is the one that becomes loss-increasing first;
(d) SGD: `⟨ν⟩_𝒟 ≥ λ_k > λ_{k+1} ≥ ⟨ν⟩_ℬ`, so `η_ℬ^loss/η_𝒟^loss ≥ m` at every state (Deng's
noise-free case: `θ^crit = 1`).

Special cases: SGD `2s^S/τ^S`; Muon `2∑_Sσ_i/∑_Sλ_i = 2‖P^SAW‖_*/tr_S` (twice a `λ`-weighted mean of
the `a_i`); HTMuon(p) `2∑_Sσ_i^{1+p}/∑_Sλ_iσ_i^{2p}`; Echelon(r): `f(σ_i) = min(σ_i,τ)/τ` with the
global `τ` for `FP` and with the block value `τ_S` (the `(r+1)`-th largest `σ_i`, `i ∈ S`) for `PF`.

*Proof.* `φ_i = f(σ_i)q_i` gives `N^S = ∑_S λ_ia_if(σ_i) = ∑_Sσ_if(σ_i) = ∑_Sν_iℓ_i` and
`R^S = ∑_Sλ_if(σ_i)² = ∑_Sν_i²ℓ_i`; Lemma 1.4. `⟨ν⟩_S` is a weighted mean of the `ν_i`, `i ∈ supp S`,
hence lies between their minimum and maximum; (a)–(d) follow. ∎

**Corollary 5.4 (two-level states) [PROVED].** In the setting of Proposition 4.1,
`η_S^loss = 2/ν_S` and, for HTMuon(p),

    η_ℬ^loss / η_𝒟^loss = ν_𝒟/ν_ℬ = m^p (a_ℬ/a_𝒟)^{1−p} = m · (ρ(1−θ)/θ)^{(1−p)/2}.

The window exists iff `θ < θ_flip(p)`; at two-level states the Deng-type alignment dichotomy
(Prop 4.1) and the suspicious-alignment window hold or fail together.

*Proof.* `(a_ℬ/a_𝒟)^{1−p} = (ρm²(1−θ)/θ)^{(1−p)/2}`. ∎

**Proposition 5.5 (how the window depends on `m`) [PROVED].** Multiply the dominant eigenvalues by
`t > 0` (`λ_i → tλ_i`, `i ∈ 𝒟`).
(a) *State fixed* (coefficients `a_i` fixed), `f` homogeneous of degree `p` and index-wise:
`η_𝒟^loss → t^{−p}η_𝒟^loss`, `η_ℬ^loss` unchanged: the window ratio scales as `t^p`
(SGD `t`, HTMuon(1/8) `t^{1/8}`, **Muon `t⁰`**).
(b) *Gradient fixed* (`σ_i` fixed, i.e. `a_i → a_i/t` on `𝒟`; then `θ` is fixed): for every filter
`η_𝒟^loss → η_𝒟^loss/t`, `η_ℬ^loss` unchanged: the window ratio scales as `t`.

*Proof.* (a) `σ_i → tσ_i` on `𝒟`: `N^𝒟 → t^{1+p}N^𝒟`, `R^𝒟 → t·t^{2p}R^𝒟`. (b) `N^𝒟 = ∑_𝒟σ_if(σ_i)` is
unchanged and `R^𝒟 = ∑_𝒟λ_if(σ_i)²` is multiplied by `t` (also for spectrum-dependent `f`, which
sees only the `σ`'s). ∎

Both are the same formula; (b) says that the curvature *along* any dominant update direction is
proportional to `m`, whatever the filter, and (a) that a filter with a decreasing gain lets the
first-order decrease `N^𝒟` grow with `m` and compensate. The prefactor in (b) is
filter-dependent: in the two-level case `(ρ(1−θ)/θ)^{(1−p)/2}`, which for `p < 1` vanishes as
`θ → 1`, so that at a fixed high alignment the window exists only if `m² > θ/(ρ(1−θ))` (Muon) resp.
`m^{2/(1−p)} > θ/(ρ(1−θ))`.

Numerics (`gap_dependence.py`, setting of Section 4.4; thresholds measured on the actual matrices;
formula vs direct `6.3e-14`). Median window ratio `η_ℬ^loss/η_𝒟^loss` at `m = 2, 5, 20, 100, 1000`
and its log-log slope between `m = 20` and `1000`:

| filter | same law of `a_i` on both blocks | slope | rescaled to `θ = 0.9` | slope | rescaled to `θ = 0.99` | slope |
|---|---|---|---|---|---|---|
| SGD, Echelon(0) | 5.01, 12.5, 50.1, 250, 2500 | 1.000 | same | 1.000 | same | 1.000 |
| HTMuon(1/2) | 2.38, 3.76, 7.51, 16.8, 53.1 | 0.500 | 1.87, 4.67, 18.7, 93.3, 933 | 1.000 | 1.02, 2.56, 10.2, 51.2, 512 | 1.000 |
| HTMuon(1/4) | 1.54, 1.93, 2.73, 4.08, 7.26 | 0.250 | 1.09, 2.73, 10.9, 54.7, 547 | 1.000 | 0.445, 1.11, 4.45, 22.3, 223 | 1.000 |
| HTMuon(1/8) | 1.22, 1.37, 1.63, 1.99, 2.66 | 0.125 | 0.828, 2.07, 8.28, 41.4, 414 | 1.000 | 0.290, 0.725, 2.90, 14.5, 145 | 1.000 |
| Muon | 0.969 (all `m`) | 0.000 | 0.629, 1.57, 6.29, 31.5, 315 | 1.000 | 0.190, 0.474, 1.90, 9.49, 94.9 | 1.000 |
| Echelon(k) | 2.20, 3.09, 3.25, 3.25, 3.25 | 0.000 | 1.61, 4.02, 16.1, 80.4, 804 | 1.000 | 0.593, 1.48, 5.93, 29.6, 296 | 1.000 |

(Ratios below 1 are reversed windows.) Echelon(k) at fixed coefficients saturates once the head is
exactly `𝒟`: then `η_𝒟^loss = 2∑_𝒟λ_ia_i/∑_𝒟λ_i` is invariant under `λ_𝒟 → tλ_𝒟` and
`η_ℬ^loss = 2τ s^ℬ/τ^ℬ` does not involve `λ_𝒟`.

Validation of Theorem 5.3 / Corollary 5.4 (P3, P5, P6): 20 commuting states (incl. tall,
rank-deficient), 8 filters: thresholds formula vs direct `5.3e-13`; sign of the loss change at
`0.95×` and `1.05×` the thresholds and inside the window: 799 tests, 0 violations; bounds (b)/(c):
42 tests, 0 violations; two-level ratio formula `2.8e-12` over 60 configurations
(`m ∈ {3, 10, 100}`, `θ ∈ {0.5, 0.9, 0.99, 0.999, 0.99999}`, `p ∈ {0, 1/8, 1/2, 1}`), ordering vs
`θ_flip`: 0 violations (2 exact ties); Echelon `FP` (global `τ`) `5.9e-13`, `PF` (block `τ`) `2.8e-14`.
Example (`m = 10`, `ρ = 1/9`, `a_ℬ = 1`): at `θ = 0.99`, SGD `(η_𝒟, η_ℬ) = (0.2, 2)`, ratio 10;
HTMuon(1/2) `(1.09, 2)`, ratio 1.83; HTMuon(1/8) `(3.91, 2)`, ratio 0.51; Muon `(5.97, 2)`, ratio 0.34.

**Proposition 5.6 ((M1), noise-free) [PROVED].** With `μ^S := τ^S/s^S` and `K := μ^𝒟/μ^ℬ ≥ m`:
(a) `FP`: `η_S^loss = 2s^S/(γ(√s)τ^S)` = Deng's noise-free threshold times `‖Ax‖/f(‖Ax‖)`;
`η_ℬ^loss/η_𝒟^loss = K ≥ m` for **every** filter: Deng's window, rescaled as a whole.
(b) `PF`: `η_S^loss = 2s^S/(γ(√s^S)τ^S)`; for HTMuon(p), `p < 1`,
`η_ℬ^loss/η_𝒟^loss = K·(θ/(1−θ))^{−(1−p)/2}`, so

    η_𝒟^loss < η_ℬ^loss   ⟺   θ < θ^crit_PF := K^{2/(1−p)}/(1 + K^{2/(1−p)}).

A noise-free critical alignment appears; `1 − θ^crit_PF ≤ 1/(1+m^{2/(1−p)})`.

*Proof.* `Δ = γ(‖g_S‖)P^SAx` with `g_S = Ax` (`FP`) or `P^SAx` (`PF`); `⟨Ax,Δ⟩ = γs^S`,
`⟨Δ,AΔ⟩ = γ²τ^S`. `γ(√s^𝒟)/γ(√s^ℬ) = (s^𝒟/s^ℬ)^{(p−1)/2}`. ∎

Validation (P7): 18 states, 4 filters: thresholds `6.6e-14`, `FP` ratio vs `K` `6.6e-14`, ordering
tests 126, 0 violations.

### 5.4 Projected updates with noise

**Theorem 5.7 [PROVED].**
(a) ((M2), commuting state, co-diagonal Gaussian noise, index-wise filter; then `FP = PF` per
realisation.) `E[L(W − ηFP_S) − L(W)] = −η∑_Sσ_if̄_i(σ_i) + (η²/2)∑_Sλ_if2_i(σ_i)`, so the expected loss
decreases iff

    0 < η < η_S^loss = 2 ∑_S σ_i f̄_i(σ_i) / ∑_S λ_i f2_i(σ_i).

In the noise-dominated regime of Corollary 3.10, `η_S^loss ≈ 2χ s^S/(f2(0) tr_S)`, hence
`η_𝒟^loss < η_ℬ^loss ⟺ θ < θ_tr = tr_𝒟/(tr_𝒟+tr_ℬ)` for **every** filter — the same critical
alignment as the noise-dominated limit of Deng's `θ^crit` (their quadratic with `α_t → 0` and
isotropic noise).
(b) ((M1), spherical Gaussian noise.) `FP`:
`E[L(x − ηFP_S) − L(x)] = −ηℓs^S + (η²/2)(β₂τ^S + A_⊥tr_S)`,
`η_S^loss = 2ℓs^S/(β₂τ^S + A_⊥tr_S)`: Deng's Theorem 10 with `(η, κ²) → (ηβ₂/ℓ, A_⊥/β₂)`, so Deng's
Theorems 11–13 hold verbatim with `n_S^loss = (A_⊥/β₂)tr_S`. `PF`: `P^Sg` is a spherical Gaussian in
the `|S|`-dimensional block with mean `P^SAx`, and the same formulas hold with the scalars
`(m₁, A_∥, A_⊥)` computed for dimension `|S|` and `snr_S = √s^S/ς`:
`E N = m₁^{(S)}√s^S`, `E R = A_⊥^{(S)}tr_S + (A_∥^{(S)}−A_⊥^{(S)})τ^S/s^S`.
(c) ((M2), Muon, any state, `d ≤ n`, any noise with `G` a.s. of full row rank.)
`E[L(W − ηFP_S) − L(W)] = −ηE[N^S] + (η²/2)tr_S`: the noise enters only through the first-order
term.

*Proof.* (a) Theorem 3.9(a): `φ_i = f_odd(σ_i+ζ_i)q_i`, so `N^S = ∑_Sσ_if_odd(σ_i+ζ_i)` and
`R^S = ∑_Sλ_if(|σ_i+ζ_i|)²`; take expectations; Corollary 3.10 for the limit. (b) Theorem 2.3:
`E N^S = ∑_Sλ_ic_iE F_i = ℓs^S`, `E R^S = ∑_Sλ_iE F_i² = β₂τ^S + A_⊥tr_S`. (c) Theorem 3.7. ∎

Validation: (a) N3 (mean loss change at the predicted thresholds, `|z| ≤ 1.3`) and E4 (ratio
`η_𝒟^loss/η_ℬ^loss` vs `(s^𝒟/tr_𝒟)/(s^ℬ/tr_ℬ)`: `1.2e-3 … 3.4e-3` at `max σ/κ = 0.1`, decreasing
quadratically to `1.2e-7 … 3.4e-7` at `10⁻³`). (b) A2 (statistics 5–8) and S2. In N3 the ordering of
the two thresholds flips with the noise level, e.g. Muon: `(η_𝒟, η_ℬ) = (1.60, 2.23)` at
`κ = 0.3·median σ` and `(1.57, 0.84)` at `κ = 3·median σ`.

---

## 6. Verdicts on Deng's takeaways (D1)–(D4)

"Survives" always refers to the one-step statement about the comparison functional `f(η)` (noise-free:
exact and pathwise; with noise: about `E f(η)`, as in Deng's Lemma "quadratic form").

### 6.0 Baseline: SGD in (M2) — everything survives unchanged [PROVED]

For SGD, `c_i⁺ = (1−ηλ_i)c_i − ηξ̃_i` row by row (`ξ̃_i` the `i`-th row of `UᵀΞ`), so with
`E ξ̃_i = 0`, `κ_i² := E‖ξ̃_i‖²` (for i.i.d. columns `N(0,Σ)`: `κ_i² = n·u_iᵀΣu_i`):
`E s₊^S = s^S − 2ητ^S + η²(u^S + e_S)`, `E[L₊−L]` likewise — Deng's formulas with `c_i² → a_i² = ‖c_i‖²`
at **every** state. (D1)–(D4) hold verbatim in (M2), commuting or not.

### 6.1 (D1) critical step size in the low-alignment regime

* **(M1), every filter — survives, modified.** Noise-free (Thm 2.1): the dichotomy holds at every
  state with `η*_f = η*₀·‖Ax‖/f(‖Ax‖)`. Spherical Gaussian noise (Thm 2.3, Prop 2.4):
  `E f(η) = p^fη² + q^fη`, `q^f = ℓq₀ < 0`; if `θ ≤ θ_iso` (in particular if `θ ≤ g_gap`) then
  `p^f > 0` and `E f(η) < 0 ⟺ η < η*_f = −q^f/p^f`. Modification: `η*_f` depends on the gradient
  norm and on the noise level through `(ℓ, β₂, A_⊥)`; for a fixed `η` the regime is selected by
  `‖Ax‖` (Cor 2.2). Anisotropic noise: only the mean-field version (Remark 2.6, numerical).
* **(M2), HTMuon(p)/Muon/Echelon, commuting states, noise-free — modified.** *Theorem:* under the
  effective separation (S+), `q_f < 0 < p_f` and `θ₊ < θ ⟺ η < η*_f` (Thm 3.3a); (S+) follows from
  `m^p > (max_𝒟a/min_ℬa)^{1−p}` for HTMuon(p) (Prop 4.3), holds at every state for Echelon(0)
  (Prop 4.4a), and for Muon is the gap-free condition `max_𝒟a < min_ℬa`.
  *It fails without (S+)*, also at low alignment: Muon, `λ = (5,5,1)`, `𝒟 = {1,2}`,
  `a = (0.05, 1, 0.8)`: `θ = 0.975 < θ_iso = 0.980`, yet `θ₊ > θ` for **every** `η > 0`
  (`q_f = 6.5 > 0`, `p_f = 6.94 > 0`); and Muon, `λ = (5,1,1)`, `a = (2,1,1)`: `θ₊ > θ` for
  `η < 4/3`, `θ₊ < θ` for `η > 4/3` (reversed) (Prop 4.2).
* **(M2), Muon, arbitrary states and noise, `d ≤ n` — the "large-step half" survives exactly.**
  `p = sψ(θ_iso − θ)` (Thm 3.7): for `θ < θ_iso` and `η > η_att` the alignment increases, pathwise
  (Thm 3.8). The "small-step half" (`θ₊ < θ` for small `η`) holds iff `q < 0`, which is not
  guaranteed by the gap; it is restored by strong noise (Cor 3.10, Prop 3.12, E5) and — numerically —
  favoured by non-commutativity (Section 8).

### 6.2 (D2) self-correction at high alignment, band near 1

* For SGD this is a *noise* effect: noise-free `p₀ > 0` always, `θ* = 1`.
* **(M1) — survives, modified** (Prop 2.4d): `θ ≥ θ*_f ⇒ E f(η) < 0` for every `η`, with Deng's
  quadratic evaluated at `(s_min, s_max, s_t) → (A_⊥, A_⊥, β₂s)`; `θ_iso ≤ θ*_f < 1`,
  `θ_iso ≥ g_gap → 1` as `m → ∞`.
* **(M2), Muon — modified.** `p ≤ 0 ⟺ θ ≥ θ_iso`, exactly, for every state and noise: Deng's band
  `[g_gap, θ*]` collapses to the single value `θ_iso = ψ_𝒟/ψ` (`1 − θ_iso = Θ(m^{−2})` as for Deng).
  For `θ > θ_iso`: `θ₊ < θ` for every `η > η_att` (Thm 3.8); for **every** `η > 0` iff `q ≤ 0`
  (in expectation: `E q ≤ 0`), which holds in the noise-dominated regime.
  *"For any `η`" fails noise-free:* two-level commuting state above `θ_iso` (Prop 4.1), e.g.
  `λ = (5,1,1)`, `a = (2,1,1)`: `θ = 0.980 > θ_iso = 0.926` and `θ₊ > θ` for all `η < 4/3`.
  With co-diagonal noise the same kind of state (E5: `d = 40, k = 4, m = 5`, `θ = 0.917 > θ_iso = 0.735`)
  has `q̄ > 0` for `κ/σ_ℬ ≤ 1` and `q̄ < 0` for `κ/σ_ℬ ≥ 3`.
* **(M2), HTMuon(p), commuting, noise-free — fails above `θ_flip(p)`** (two-level): the alignment
  increases for every `η < η*_f`. `θ_flip(p) → 1` as `m → ∞` at rate `m^{−2/(1−p)}`.

### 6.3 (D3) bounds on `η*`

* Deng's lower bound (Thm 7) is correct; his upper bounds (Thm 8 main text, Cor 9) are not
  (Remark 2.8). Correct noise-free statement: `2/(λ_1+λ_{k+1}) ≤ η*₀ ≤ 2/(λ_k+λ_d)`.
* **(M1) — modified:** `η*_f ∈ [2/(λ_1+λ_{k+1}), 2/(λ_k+λ_d)] × ‖Ax‖/f(‖Ax‖)` noise-free. No
  state-independent bound exists for `p < 1` (`η*_f(tx) = t^{1−p}η*_f(x)`); in particular
  "`η* ≲ 2/λ_1`" has no analogue.
* **(M2), commuting, (S+) or (S−) — modified:** `2/(max_𝒟ν+max_ℬν) ≤ η*_f ≤ 2/(min_𝒟ν+min_ℬν)`
  (Thm 3.3); Muon: `2/(1/min_𝒟a + 1/min_ℬa) ≤ η*_f ≤ 2/(1/max_𝒟a + 1/max_ℬa)` — set by coefficient
  magnitudes, not by eigenvalues; HTMuon isotropic: `2a^{1−p}/(λ_1^p+λ_{k+1}^p) ≤ η*_f ≤ 2a^{1−p}/(λ_k^p+λ_d^p)`.

### 6.4 (D4) projected updates and the suspicious-alignment window

* **(M1), filter-then-project — survives unchanged in shape:** both thresholds are Deng's times
  `‖Ax‖/f(‖Ax‖)`; ratio `K ≥ m`; with spherical noise Deng's Theorems 10–13 hold with
  `(η, κ²) → (ηβ₂/ℓ, A_⊥/β₂)` (Prop 5.6a, Thm 5.7b).
* **(M1), project-then-filter — modified:** a noise-free critical alignment
  `θ^crit_PF = K^{2/(1−p)}/(1+K^{2/(1−p)})` appears (Prop 5.6b).
* **(M2), commuting, noise-free — modified:** `η_S^loss = 2/⟨ν⟩_S`; the window exists iff
  `⟨ν⟩_𝒟 > ⟨ν⟩_ℬ`; under (S+) its ratio is `≥ min_𝒟ν/max_ℬν`; under (S−) it is reversed (Thm 5.3).
  Two-level: ratio `m^p(a_ℬ/a_𝒟)^{1−p} = m(ρ(1−θ)/θ)^{(1−p)/2}`, window iff `θ < θ_flip(p)` (Cor 5.4).
  *Counterexample to the SGD ordering:* Muon, `m = 10`, `ρ = 1/9`, two-level state with `θ = 0.99`:
  `η_𝒟^loss = 5.97 > η_ℬ^loss = 2`; for `η ∈ (2, 5.97)` the **bulk**-projected Muon update increases
  the loss and the dominant-projected one decreases it. (For SGD at the same state: `0.2 < 2`.)
* **Dependence of the window on `m`** (Prop 5.5 and the table there): fixed coefficients — SGD `m¹`,
  HTMuon(p) `m^p`, Muon `m⁰`, Echelon(0) `m¹`, Echelon(k) `m⁰` once the head is `𝒟`; fixed gradient —
  `m¹` for all. Critical alignment below which the window exists: SGD `1` noise-free
  (`1 − θ^crit = Θ(1/(s(m−1)))` with noise, Deng Thm 13); HTMuon(p) `1 − θ_flip = (1+ρm^{2/(1−p)})^{−1}`
  noise-free, state-independent; Muon `1 − θ_iso ≈ 1/(ρm²)`.
* **With strong noise** all filters share the SGD-type ordering with critical alignment
  `θ_tr = tr_𝒟/(tr_𝒟+tr_ℬ)` (Thm 5.7a).
* **(M2), Muon, arbitrary states:** `η_S^{FP} = 2tr(P_SM^{1/2})/tr_S`, with a state- and
  noise-independent curvature term (Thm 5.2c, 5.7c). At generic Gaussian (isotropic) states in the
  paper's spectrum the measured window ratio is `0.86–0.89` (`n = 600`) and `0.975–0.98`
  (`n = 3000`) for `m ∈ {2, 10, 50}`: no window, independently of `m` (Section 8, S3).

### 6.5 Short answers to the guiding questions

* *Which sign facts survive?* `q < 0` survives in (M1) (all filters, also with spherical noise) and
  in (M2) exactly when the effective curvatures are ordered like the Hessian eigenvalues (S+).
  `p > 0` noise-free survives in (M1) and under (S+). For Muon in (M2) the sign of `p` is the sign
  of `θ_iso − θ`, exactly — stronger than Deng's two-threshold statement.
* *Gap dependence?* **Preserved** in (M1) (through `η*₀`, `K ≥ m`) and in the Muon coefficient `p`
  (`θ_iso`). **Weakened** to `m^p` against coefficient spread for HTMuon (`p = 1/8`: nearly removed).
  **Removed** from the sign of `q_f` and from the fixed-state window ratio for Muon and Echelon(k).
  **Fully present for every filter** at fixed gradient spectrum (Prop 5.5b) and in the
  noise-dominated regime.
* *Governed by `η` alone?* No: by `ηγ(‖g‖)` in (M1) — step size and gradient norm — and by
  `ηλ_iγ(σ_i)` in (M2) — step size, overall scale (Cor 3.4), and the relative size of dominant and
  bulk coefficients, which under Muon decides the signs of `q_f` and of `⟨ν⟩_𝒟 − ⟨ν⟩_ℬ` on its own.

---

## 7. Numerical validation: index of checks

All checks use float64 numpy; "direct" means the filter is applied through `numpy.linalg.svd` to the
actual `d×n` gradient matrix. Seeds are fixed in each script. Total runtime of the scripts: about
5 CPU-minutes on one thread.

| ID | statement checked | script | sizes | max discrepancy / outcome |
|---|---|---|---|---|
| C1 | Echelon head–tail = filter `min(σ,τ)/τ`; NS5 port = scalar filter | `validate_m2_commuting.py` | `(d,n)` up to `(120,150)`, 6 ranks | `5.5e-13`; `1.4e-15` |
| C2–C5 | Thm 3.1, 3.2, Cor 3.4, loss formula | same | 28 states, 9 filters, 6 step sizes | `≤ 2.2e-12` (all), `|Δθ|` `2.4e-15`; signs 0/500 |
| C6 | Thm 3.3 (bounds, dichotomy, reversed dichotomy) | same | 250 tests | 0 violations |
| C7 | Prop 4.1 (`θ_flip`, `η* = 2/(ν_𝒟+ν_ℬ)`) | same | 12 configs | `2.2e-16`; `4.6e-15`; 0 violations |
| C8 | Prop 4.2 (four sign patterns) | same | 4 explicit states | as tabulated |
| G1 | Thm 3.5 (Gram formulas), Thm 5.2 (both projections) | `validate_m2_general.py` | 24 generic states, 5 filters | `≤ 7.2e-12` |
| G2 | Thm 3.7 (pinning, 5 noise types) | same | 20 states × 5 | `1.8e-15`; `4.6e-16` |
| G3 | Thm 3.8 (attraction) | same | 300 tests | 0 violations |
| G4 | Prop 3.6 (Jensen bounds) | same | 576 tests | 0 violations |
| G5 | SGD row-norm formulas exact | same | 24 states | `6.9e-13` |
| P1 | Prop 5.1 (coincidence / difference) | `validate_projected.py` | 9 states | `5.8e-13` when equal |
| P2, P4 | Lemma 1.4, Thm 5.2a (additivity) | same | 20 generic states, 8 filters | `7.9e-15`; `1.1e-11` |
| P3 | Thm 5.3 (thresholds, window, (S±) bounds) | same | 20 states, 8 filters | `5.3e-13`; 0/799; 0/42 |
| P5 | Cor 5.4 (two-level ratio, `θ_flip`) | same | 60 configs | `2.8e-12`; 0 violations |
| P6 | Thm 5.3 for Echelon (`FP` global `τ`, `PF` block `τ`) | same | 20 states × 3 ranks | `5.9e-13`; `2.8e-14` |
| P7 | Prop 5.6 ((M1) projected) | same | 18 states, 4 filters | `6.6e-14`; 0/126 |
| A1 | Thm 2.1, Cor 2.2 | `validate_m1.py` | 15 states, 7 filters | `7.2e-15`; 0/435 |
| A2 | Thm 2.3, Prop 2.4e, Thm 5.7b | same | `d ∈ {50,200}`, 3 SNRs, `3·10⁵` MC | 192 z-tests, max `3.00`; closed forms `5.7e-14` |
| A4 | Remark 2.6 (mean-field) | same | `d ∈ {50,200,800}`, 3 covariances, `10⁵` MC | 0.27% / 1.5% / 9.1% by `ε` |
| A5 | Remark 2.8 (Deng Thm 8, Cor 9) | same | 3 explicit + 4000 random | counterexamples; corrected bounds 0 violations |
| N1 | Thm 3.9a (per realisation) | `validate_m2_noise.py` | `d=60, n=80`, 60 draws, 6 filters | `8.0e-15` |
| N2 | Thm 3.9c closed forms, `χ` | same | 24 cases | `2.7e-15`; `9.9e-10` |
| N3 | Thm 3.9b, Thm 5.7a (direct-SVD MC) | same | `d=40, n=50`, 3000 MC | 24 z-tests, max `1.49` |
| N4 | Lemma 3.11 | same | `d=20, n=30`, `4·10⁴` MC | consistent with 0 (max `|z|` 3.6 of 580) |
| N5 | Prop 3.12 (wide limit) | same | `d=10`, `n` up to 2560 | error `≈ 1/n`, `9e-4` at `n = 2560` |
| E1 | Lemmas 1.2, 1.3 (arbitrary updates) | `extra_checks.py` | 200 random pairs | `8.7e-15` |
| E2 | Prop 2.4a,c,d | same | 120 instances | 0 violations |
| E3, E4 | Cor 3.10, Thm 5.7a limit | same | `d=80`, 3 filters | quadratic convergence, `3.6e-7` at `σ/κ = 10⁻³` |
| E5 | sign of `q̄` flips with noise (Muon) | same | `d=40, n=50`, 1500 MC | `|z| ≤ 1.5` |
| E6 | Prop 4.4 | same | 100 states | `3.1e-16` |
| gap | Prop 5.5, Section 4.4 tables | `gap_dependence.py` | `d=100, n=120`, 20 states × 5 gaps × 7 filters | slopes `p` resp. `1` to `1e-15`; formula vs direct `6.3e-14` |
| Q1, Q2 | Section 8 (generic states, (M3)) | `probe_noncommuting.py` | `d=100`, `n ≤ 8000`; (M3) `d=60` | see Section 8 |
| S1–S4 | Remarks 2.6–2.8, Section 8 in the paper's setup | `deng_setup.py` | `d=500, k=50`; `n ∈ {600, 3000}` | see there |
| SO | Prop 8.1 (second-order correction) | `second_order.py` | `d=100`, `n ≤ 25600` | error `∝ n^{−2}` vs `n^{−1}` |

---

## 8. Beyond commuting states: how far are the formulas from the truth?

The exact statements for arbitrary states are Lemma 1.2, Theorem 3.5 (Gram formulas), Theorem 3.7/3.8
(Muon) and Theorem 5.2. The *commuting (row-norm) formulas* of Theorems 3.2 and 5.3 evaluated at
`a_i = ‖c_i‖` are exact for SGD, and upper bounds for `T^S, V^S, N^S, R^S` under sub-linear filters
(Prop 3.6). Their accuracy for generic states:

### 8.1 First correction [PROVED as a second-order expansion; NUMERICAL accuracy]

**Proposition 8.1.** Write `M = diag(σ_i²) + E` (`E` = off-diagonal part, `M_ij = λ_iλ_j⟨c_i,c_j⟩`).
For `g` twice continuously differentiable near the `σ_i² > 0` (distinct),

    g(M)_ii = g(σ_i²) + ∑_{j≠i} M_ij² · g[σ_i², σ_i², σ_j²] + O(‖E‖³),
    g[x,x,y] := ( (g(x)−g(y))/(x−y) − g'(x) ) / (y − x)

(second-order term of the Daleckii–Krein expansion; the first-order term has zero diagonal). With
`g = g₁, g₂` this corrects `T^S, V^S, N^S, R^S` of Theorem 3.5. For Muon (`g₁ = √t`):

    (M^{1/2})_ii ≈ σ_i · [ 1 − ½ ∑_{j≠i} cos²(c_i,c_j) · σ_j²/(σ_i+σ_j)² ].

For concave `g` the correction is non-positive (consistent with Prop 3.6). The relative deficit of a
row is `≈ ½∑_j cos²(c_i,c_j)` over the rows `j` with a *much larger* gradient and negligible from
rows with a much smaller one: **bulk rows are penalised by the dominant rows, not vice versa.**
Consequently, relative to the commuting formula, non-commutativity lowers `T^ℬ` and `N^ℬ` more than
`T^𝒟` and `N^𝒟`: it shifts `q` towards negative values (towards Deng's sign) and lowers
`η_ℬ^loss/η_𝒟^loss` (towards a reversed window) — both effects are visible below.

Numerics (`second_order.py`; `d = 100`, Gaussian rows with log-normal(0, 0.5) scales, 6 states per
`n`, direct SVD). Max relative error of `T^S, V^S, N^S, R^S`:

| `n` | Muon: row-norm → 2nd order | HTMuon(1/8) | HTMuon(1/2) |
|---|---|---|---|
| 400 | `4.3e-2 → 1.8e-3` | `4.3e-2 → 1.6e-3` | `3.9e-2 → 1.6e-3` |
| 1600 | `9.9e-3 → 8.3e-5` | `1.0e-2 → 7.6e-5` | `9.1e-3 → 7.2e-5` |
| 6400 | `2.4e-3 → 6.5e-6` | `2.4e-3 → 5.6e-6` | `2.2e-3 → 5.7e-6` |
| 25600 | `6.4e-4 → 7.9e-7` | `6.6e-4 → 8.1e-7` | `6.0e-4 → 7.6e-7` |

(row-norm error `∝ d/n`, corrected error `∝ (d/n)²`). Median relative error of `q`:
Muon `0.16 → 3.0e-3` at `n = 400` and `1.7e-3 → 7.9e-7` at `n = 25600`.

### 8.2 Model (M2), generic Gaussian states [NUMERICAL, `probe_noncommuting.py` Q1]

`d = 100`, 24 states per `n` (rows `c_i = scale_i·N(0, I_n/n)`, log-normal(0, 0.6) scales times an
independent block factor `10^{U(−1.2, 0.8)}` on `𝒟`; `m ∈ {2, 5, 20}`). "off-diag" is
`‖M − diag M‖_F/‖diag M‖_F`. Relative errors of the row-norm formulas (median / max over states):

| `n` | off-diag | filter | `T^S` | `V^S` | `η*` | `η_𝒟^loss`, `η_ℬ^loss` (median) | `|Δθ|` error (median / max) | sign of `Δθ` | sign of `q` | order of thresholds |
|---|---|---|---|---|---|---|---|---|---|---|
| 100 | 0.22 | Muon | 0.092 / 0.17 | 0 | 0.066 / 0.35 | 0.018, 0.14 | 5.7e-3 / 6.5e-2 | 0.97 | 0.96 | 1.00 |
| 100 | 0.22 | HTMuon(1/8) | 0.084 / 0.17 | 0.060 / 0.087 | 0.033 / 0.29 | 0.006, 0.055 | 5.5e-3 / 4.6e-2 | 0.98 | 0.96 | 1.00 |
| 100 | 0.22 | Echelon(k) | 0.061 / 0.19 | 0.096 / 0.32 | 0.046 / 0.13 | 0.017, 0.065 | 2.9e-3 / 7.8e-2 | 1.00 | 1.00 | 1.00 |
| 500 | 0.11 | Muon | 0.016 / 0.032 | 0 | 0.016 / 0.18 | 0.006, 0.023 | 1.0e-3 / 1.6e-2 | 1.00 | 1.00 | 1.00 |
| 500 | 0.11 | HTMuon(1/8) | 0.015 / 0.031 | 0.009 / 0.015 | 0.010 / 0.11 | 0.002, 0.011 | 7.5e-4 / 1.1e-2 | 1.00 | 1.00 | 1.00 |
| 2000 | 0.061 | Muon | 0.004 / 0.008 | 0 | 0.007 / 0.073 | 0.001, 0.006 | 2.0e-4 / 4.2e-3 | 1.00 | 1.00 | 1.00 |
| 8000 | 0.025 | Muon | 0.001 / 0.002 | 0 | 0.002 / 0.022 | <0.001, 0.002 | 3.5e-5 / 7.6e-4 | 1.00 | 1.00 | 1.00 |
| 8000 | 0.025 | HTMuon(1/8) | 0.001 / 0.002 | 0.001 / 0.001 | 0.002 / 0.009 | <0.001, 0.001 | 2.1e-5 / 7.6e-4 | 0.98 | 0.96 | 1.00 |

(last three columns: fraction of cases in which the row-norm formula predicts the correct sign /
order; SGD: all errors `≤ 4e-15`. `V^S` is exact for Muon by Theorem 3.7. Full table for
`n ∈ {100, 200, 500, 2000, 8000}` and HTMuon(1/2) in `results/probe_noncommuting.log`. The one
order disagreement occurs for Muon at `n = 200`: agreement 0.92.) The errors decay like `d/n`: **for
wide layers the commuting formulas are quantitatively accurate; for square layers they are correct
to about 10% in `T^S` and usually, not always, in sign.** The bulk threshold is systematically less
accurate than the dominant one, as Proposition 8.1 predicts.

### 8.3 The paper's spectrum with isotropic generic states [NUMERICAL, `deng_setup.py` S3]

`d = 500`, `k = 50`, spectrum of `quad_sim.py`, states with i.i.d. Gaussian rows (all row norms
`≈ 1`: the matrix analogue of `x₀ ~ N(0,I)`), noise-free, direct SVD. Here `θ ≈ θ_iso`, the point
where the commuting Muon formulas are degenerate (`q_f ≈ p_f ≈ 0`, Prop 4.3c).

| `m` | `n` | filter | window ratio `η_ℬ^loss/η_𝒟^loss`: exact (row-norm) | `η*` exact (row-norm) | `q/s²` exact (row-norm) |
|---|---|---|---|---|---|
| 2 / 10 / 50 | 600 | SGD | 3.17 / 15.2 / 75.6 (same) | 0.0168 / 0.0206 / 0.0217 (same) | `< 0` |
| 2 / 10 / 50 | 600 | HTMuon(1/8) | 1.10 / 1.32 / 1.60 (1.17 / 1.42 / 1.74) | 0.84 / 0.81 / 0.82 (0.62 / 0.67 / 0.72) | `< 0` (`< 0`) |
| 2 / 10 / 50 | 600 | Muon | 0.89 / 0.87 / 0.86 (0.99) | none: `q, p < 0` (1.01) | −3.7e-2 / −5.3e-3 / −2.4e-4 (+2.9e-3 / +3.1e-4 / +1.3e-5) |
| 2 / 10 / 50 | 600 | Echelon(k) | 1.80 / 1.81 / 1.80 (1.37) | 1.34 / 1.36 / 1.37 (1.25) | `< 0` (`< 0`) |
| 2 / 10 / 50 | 3000 | HTMuon(1/8) | 1.16 / 1.41 / 1.72 (1.17 / 1.43 / 1.75) | 0.66 / 0.69 / 0.74 (0.61 / 0.67 / 0.72) | `< 0` (`< 0`) |
| 2 / 10 / 50 | 3000 | Muon | 0.98 / 0.98 / 0.98 (1.00) | none: `q, p < 0` (1.02) | −6.4e-3 / −9.6e-4 / −4.3e-5 (+5.7e-4 / +6.2e-5 / +2.6e-6) |
| 2 / 10 / 50 | 3000 | Echelon(k) | 1.50 / 1.50 / 1.50 (1.35) | 1.27 / 1.28 / 1.28 (1.25) | `< 0` (`< 0`) |

Observations. (i) The window ratio behaves as predicted by Prop 5.5a: `∝ m` for SGD, `≈ m^{1/8}`
for HTMuon(1/8) (`1.60/1.10 = 1.45` vs `(50.1/2.1)^{1/8} = 1.49`), independent of `m` and `≤ 1` for
Muon, independent of `m` and `≈ 1.5–1.8` for Echelon(k). (ii) At this degenerate point the commuting
Muon formula gets the **sign of `q` wrong** (it predicts `q ≈ 0⁺`); the exact `q` is negative, in the
direction predicted by Proposition 8.1, and since here `θ` is slightly above `θ_iso` (`p < 0`) the
alignment decreases for every `η`. Muon's `p` equals `sψ(θ_iso − θ)` to `1e-16` (Thm 3.7).
(iii) For Echelon(k) the row-norm formula is biased even at `n = 3000` (10%): its scale `τ = σ_{k+1}`
is an extreme singular value of the bulk block, which generic states inflate by a
Marchenko–Pastur-type factor. With heterogeneous (log-normal(0, 0.5)) row norms the picture is the
same except that the Echelon(k) ratio is `2.0–4.0` (table in `results/deng_setup.log`).

### 8.4 Model (M3): `L(W) = ½ tr(WᵀAWB)` [PROVED (a),(b); NUMERICAL (c); Q2]

Gradient `G = AWB`; Hessian `B ⊗ A`; let `B = V_B diag(β) V_Bᵀ`, `C' := UᵀWB` (rows `c'_i`), so
`UᵀG = ΛC'` and the left alignment is `θ = ∑_𝒟λ_i²‖c'_i‖²/∑_iλ_i²‖c'_i‖²`.

(a) *Left-commuting states* (rows of `C'` mutually orthogonal, `C' = diag(a')Q`): then
`UᵀF(G) = diag(f(σ_i))Q`, `σ_i = λ_ia'_i`, and, with `b_i := q_iBq_iᵀ`, `b2_i := q_iB²q_iᵀ`,

    ‖c'_i⁺‖² = a'_i² − 2η f(σ_i) a'_i b_i + η² f(σ_i)² b2_i,       L₊ − L = −η ∑ σ_i f(σ_i) + (η²/2) ∑ λ_i f(σ_i)² b_i,

so `T^S = ∑_Sλ_i²a'_if(σ_i)b_i`, `V^S = ∑_Sλ_i²f(σ_i)²b2_i`: the commuting formulas with Rayleigh
quotients of `B` inserted. (Proof: `C'₊ = C' − ηUᵀF(G)B = C' − η·diag(f(σ_i))QB`.) The structure is
*not* preserved by the step unless the `q_i` are eigenvectors of `B`. Checked to `2.6e-14`.
(b) *Aligned states* (`UᵀWV_B` has one non-zero entry per row and column, `(i, π(i))`, of modulus
`a_i`): the model is exactly the commuting coordinate model with spectrum `h_i := λ_iβ_{π(i)}` (the
Hessian eigenvalue of the pair), the support is preserved, and every theorem of Sections 3–5 holds
with `λ_i → h_i` and a *product* dominant block. Checked to `3.1e-14`.
(c) *Generic states*, left dominant block, `d = 60`, 12 states: the Rayleigh-quotient formula of (a)
evaluated at the row norms has median relative error in `T^S` of `0.097, 0.12, 0.32` for
`cond(B) = 1, 3, 30` at `n = 60`, `0.020, 0.047, 0.11` at `n = 240` and `0.005, 0.012, 0.033` at
`n = 960` (Muon; HTMuon(1/8) within 10% of these), and predicts the sign of `Δθ` in
`94%, 83%, 69%` of the cases at `n = 60` and `≥ 97%` at `n = 960` (Muon; `cond(B) = 30`, `n = 240`:
89%). **For an ill-conditioned right factor and a square layer the commuting formulas are not
reliable**; (M3) with generic states needs the Gram-type treatment with both factors.

---

## 9. Statements for formalisation (finite sums in eigen-coordinates)

Common data: a finite index type `ι`, disjoint finsets `𝒟, ℬ` with `𝒟 ∪ ℬ = univ`; `λ : ι → ℝ`,
`λ_i > 0`, and constants `λ_min^𝒟 > λ_max^ℬ` bounding the blocks (`m = λ_k/λ_{k+1}`); `a : ι → ℝ`,
`a_i ≥ 0`; `f : ℝ → ℝ`, `f ≥ 0` on `[0,∞)`; `σ_i = λ_ia_i`, `s_i = σ_i²`, `ν_i = f(σ_i)/a_i`
(`0` if `a_i = 0`), `s^S, τ_f^S, u_f^S, q_f, p_f` as in Theorem 3.2. Tags: **[ALG]** = ring/field
identities over finite sums; **[ORD]** = elementary inequalities (sums of signed terms, weighted
means, Cauchy–Schwarz); **[POW]** = needs monotonicity/algebra of real powers; **[AN]** = needs
integration / Gaussian measure / special functions; **[MAT]** = needs matrix functional calculus or
SVD. Items marked ◆ are (special cases of) statements already listed in `filter_spec.md`.

1. **[ALG] ◆ Comparison identity.** For reals: `s^ℬ(s^𝒟 − 2ηT^𝒟 + η²V^𝒟) − (s^ℬ − 2ηT^ℬ + η²V^ℬ)s^𝒟 = (s^ℬV^𝒟 − s^𝒟V^ℬ)η² + 2(s^𝒟T^ℬ − s^ℬT^𝒟)η`.
2. **[ALG] ◆ Alignment change.** If `s^𝒟+s^ℬ > 0`, `s₊^𝒟+s₊^ℬ > 0`:
   `s₊^𝒟/(s₊^𝒟+s₊^ℬ) − s^𝒟/(s^𝒟+s^ℬ) = (s^ℬs₊^𝒟 − s₊^ℬs^𝒟)/((s^𝒟+s^ℬ)(s₊^𝒟+s₊^ℬ))`; hence the three sign equivalences.
3. **[ALG] Three alignments.** `s^ℬV^𝒟 − s^𝒟V^ℬ = (s^𝒟+s^ℬ)V^𝒟 − s^𝒟(V^𝒟+V^ℬ)` and the analogue for `q`.
4. **[ALG] ◆ Filtered energies.** With `a_i⁺ := a_i − ηf(σ_i)`:
   `∑_{i∈S} λ_i²(a_i⁺)² = s^S − 2ητ_f^S + η²u_f^S`, and `∑_i λ_i((a_i⁺)² − a_i²)/2 = −η∑σ_if(σ_i) + (η²/2)∑λ_if(σ_i)²`.
5. **[ALG] ◆ Double sums.** `q_f = 2∑_{i∈𝒟}∑_{j∈ℬ}s_is_j(ν_j − ν_i)`, `p_f = ∑_{i∈𝒟}∑_{j∈ℬ}s_is_j(ν_i² − ν_j²)`.
6. **[ORD] ◆ Dichotomy under (S+).** If `s^𝒟, s^ℬ > 0`, `ν ≥ 0`, and `ν_j < ν_i` for all
   `i ∈ 𝒟, j ∈ ℬ` with `a_i, a_j > 0`: `q_f < 0 < p_f`; for `η > 0`:
   `p_fη² + q_fη < 0 ⟺ η < −q_f/p_f`, `= 0 ⟺ η = −q_f/p_f`, `> 0 ⟺ η > −q_f/p_f`.
7. **[ORD] ◆ Reversed dichotomy under (S−)** (all inequalities reversed).
8. **[ORD] ◆ Bounds.** Under 6 (or 7), if `α_𝒟 ≤ ν_i ≤ β_𝒟` on `supp 𝒟`, `α_ℬ ≤ ν_j ≤ β_ℬ` on
   `supp ℬ`, `α_𝒟+α_ℬ > 0`: `2/(β_𝒟+β_ℬ) ≤ −q_f/p_f ≤ 2/(α_𝒟+α_ℬ)`.
9. **[ORD] ◆ SGD corollary.** `f = id`: `2/(λ_1+λ_{k+1}) ≤ η*₀ ≤ 2/(λ_k+λ_d)`; and
   `η*₀ ≤ 2(λ_1−λ_d)/(λ_kλ_1−λ_{k+1}λ_d)`.
10. **[ALG] Counterexample to Deng Thm 8 (main text) / Cor 9.** `λ = (10, 1, 1/10)`, `𝒟 = {1,2}`,
    `c = (1/100, 1, 1)`: noise-free `η*₀ = 740/737 > 110/111 = (λ_1−λ_d)/(λ_kλ_1−λ_{k+1}λ_d) > 1/5 = 2/λ_1`;
    with `e_S = κ²ψ_S`, `κ² = 10⁻⁸`: hypothesis `θ ≥ e_ℬ/(e_ℬ+e_𝒟)` holds and `η* > 110/111` still.
11. **[ALG]/[POW] Scaling law.** If `f(tσ) = t^pf(σ)` for `t, σ > 0`: `q_f(ta) = t^{3+p}q_f(a)`,
    `p_f(ta) = t^{2+2p}p_f(a)`.
12. **[ALG] ◆ Two-level.** If `ν_i = ν_𝒟` on `supp 𝒟` and `ν_j = ν_ℬ` on `supp ℬ`:
    `q_f = 2s^𝒟s^ℬ(ν_ℬ−ν_𝒟)`, `p_f = s^𝒟s^ℬ(ν_𝒟²−ν_ℬ²)`, `−q_f/p_f = 2/(ν_𝒟+ν_ℬ)` if `ν_𝒟 ≠ ν_ℬ`;
    `p_f = q_f = 0` if `ν_𝒟 = ν_ℬ`.
13. **[POW] ◆ Flip alignment.** Two-level spectrum and state, `f(σ) = σ^p`, `0 ≤ p < 1`,
    `ρ = |𝒟|/|ℬ|`: `ν_𝒟 > ν_ℬ ⟺ θ/(1−θ) < ρm^{2/(1−p)}`.
14. **[ALG] Pinning (coordinate form).** If `V^S = ψ_S` for `S = 𝒟, ℬ`:
    `p = s^ℬψ_𝒟 − s^𝒟ψ_ℬ = (s^𝒟+s^ℬ)(ψ_𝒟+ψ_ℬ)(ψ_𝒟/(ψ_𝒟+ψ_ℬ) − s^𝒟/(s^𝒟+s^ℬ))`.
15. **[ORD] Attraction.** If moreover `T^S = ∑_Sλ_i²t_i` with `|t_i| ≤ a_i`: `|T^S| ≤ √(ψ_Ss^S)`,
    `|q| ≤ 2√(s^𝒟s^ℬ)(√(s^𝒟ψ_ℬ)+√(s^ℬψ_𝒟))`, and for `η > 2/|√(ψ_𝒟/s^𝒟) − √(ψ_ℬ/s^ℬ)|`:
    `sign(pη+q) = sign(p)`.
16. **[ORD] ◆ Loss thresholds.** With `N^S = ∑_Sσ_if(σ_i) > 0`, `R^S = ∑_Sλ_if(σ_i)² > 0`:
    `−ηN^S + (η²/2)R^S < 0 ⟺ 0 < η < 2N^S/R^S`; `min_{supp S}ν ≤ R^S/N^S ≤ max_{supp S}ν`; under
    (S+) `η_ℬ^loss/η_𝒟^loss ≥ min_𝒟ν/max_ℬν`; for `f = id` the ratio is `≥ λ_k/λ_{k+1}`.
17. **[ALG]/[POW] ◆ Two-level window.** `η_ℬ^loss/η_𝒟^loss = ν_𝒟/ν_ℬ = m^p(a_ℬ/a_𝒟)^{1−p}`.
18. **[ALG] Window scaling.** Replace `λ_i` by `tλ_i` on `𝒟`: (a) `a` fixed and `f` `p`-homogeneous:
    `η_𝒟^loss ↦ t^{−p}η_𝒟^loss`; (b) `σ` fixed: `η_𝒟^loss ↦ η_𝒟^loss/t`.
19. **[ORD] ◆ Echelon coordinate model.** `f(σ) = min(σ,τ)/τ`, `τ > 0`: `ν_i = λ_i/max(σ_i,τ)`;
    if `σ_j ≤ τ` on `ℬ` and `σ_i ≥ τ` on `𝒟`: (S+) for `f ≡ 1` implies (S+) for this `f`.
20. **[ALG] ◆ (M1) noise-free.** If `c_i⁺ = (1 − ηγλ_i)c_i` with `γ > 0`: `q_f = γq₀`, `p_f = γ²p₀`,
    and the trichotomy at `η*₀/γ`.
21. **[POW] (M1) project-then-filter.** `f = σ^p`, `p < 1`: `η_ℬ^loss/η_𝒟^loss = K(s^𝒟/s^ℬ)^{−(1−p)/2}`
    and the equivalence with `θ < K^{2/(1−p)}/(1+K^{2/(1−p)})`.
22. **[ALG]+[ORD] (M1) spherical noise, moment form.** *Assume* `E F_i = ℓλ_ic_i` and
    `E F_i² = β₂λ_i²c_i² + A_⊥` with `ℓ > 0`, `β₂ ≥ 0`, `A_⊥ > 0`. Then
    `E s₊^S = s^S − 2ηℓτ^S + η²(β₂u^S + A_⊥ψ_S)`, `q^f = ℓq₀ < 0`,
    `θ ≤ θ_iso ⇒ p^f ≥ 0`, and `θ ≥ θ*_f ⇒ p^f ≤ 0` (quadratic of Prop 2.4d).
    **[AN]** the hypotheses themselves: rotational symmetry of `N(μ, ς²I)` about `μ`; `ℓ > 0`;
    `β₂ ≥ 0` (Chebyshev association on the sphere); Muon closed forms (Kummer functions).
23. **[ALG] Co-diagonal noise, moment form.** *Assume* `E f_odd(σ_i+ζ_i) = f̄_i`,
    `E f(|σ_i+ζ_i|)² = f2_i`: the formulas of Thm 3.9b and Thm 5.7a. **[AN]** `f̄ = erf(σ/(√2κ))` for
    Muon; Kummer forms for HTMuon; linear response `f̄(σ) = χσ + O(σ³)`.
24. **[MAT] Matrix facts.** (i) `F(G) = h(GGᵀ)G`, equivariance (Lemma 1.1). (ii) Commuting state
    ⇒ `F(ΛC) = diag(f(σ_i))Q` (Thm 3.1). (iii) Gram formulas (Thm 3.5). (iv) ◆ `OOᵀ = I ⇒ ‖φ_i‖ = 1`,
    `V^S = ψ_S`, `R^S = tr_S` (Thm 3.7). (v) Block-commuting ⇒ `P^SF(G) = F(P^SG)` (Prop 5.1b).
    (vi) Additivity of `FP` (Thm 5.2a) — in fact [ALG] given `P^𝒟AP^ℬ = 0`.
    **[MAT]+[AN]** Jensen bound `⟨e, g(M)e⟩ ≤ g(⟨e, Me⟩)` (Prop 3.6); symmetry lemma 3.11 (invariance
    of a Gaussian matrix law under sign flips); second-order expansion (Prop 8.1).

Items 1–9, 11–12, 14–20 are finite-sum algebra/inequalities and should be routine in Lean/Mathlib;
13, 17, 21 need `Real.rpow` monotonicity; 22–23 split cleanly into an algebraic part (given the
moment identities) and an analytic part; 24 needs the spectral theorem / matrix functional calculus.

---

## 10. Caveats and open questions

1. **Sign of `E f` versus sign of `E θ₊ − θ`.** With noise we control `E f(η)` only (as Deng does
   before invoking a `d → ∞` ratio lemma). In S2 the two differ visibly at `η = η*_f` in the
   noise-dominated state. A ratio lemma for filtered updates is not proved here.
2. **The commuting class is special.** It is invariant under noise-free filtered steps and under
   co-diagonal noise, but generic states are not commuting; the exact tools there are Theorems 3.5,
   3.7, 3.8, 5.2. The row-norm formulas are accurate for wide layers (`d/n` small), carry `≈ 10%`
   errors for square layers, and can give the wrong sign of `q` near the degenerate (isotropic) point
   of Muon (Section 8.3).
3. **I.i.d. matrix noise.** `m_i, v_i` of Lemma 3.11 have no closed form at finite `n/d`; only the
   wide limit (Prop 3.12, heuristic) and the co-diagonal model (Thm 3.9) are treated. A
   deformed-Wishart calculation would close this gap.
4. **Anisotropic noise in (M1).** Only the mean-field replacement, with numerical error bars; no
   rigorous bound is given.
5. **Momentum.** Muon-type optimizers filter a momentum buffer, not the instantaneous gradient; the
   present theory is for `β = 0` (or for the first step). With momentum the singular frame of the
   buffer need not be the Hessian eigenbasis even from a commuting start.
6. **Echelon with a tracked (inexact) frame**, and the approximate filters of `htmuon_ns` /
   `htmuon_stream`, are covered only through "whichever `f` is applied"; frame error is not modelled.
7. **(M3).** Exact results only for left-commuting and aligned states; generic states with an
   ill-conditioned `B` are not captured by the commuting formulas (Section 8.4c).
8. **Conjecture (suggested by Prop 8.1 and Sections 8.2–8.3, not proved).** For Muon and generic
   states with independent isotropic rows, `q_exact ≤ q_row-norm` to leading order in `d/n`, i.e.
   non-commutativity always moves `q` towards Deng's sign and the window ratio towards reversal.
