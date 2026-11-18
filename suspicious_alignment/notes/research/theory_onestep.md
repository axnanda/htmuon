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

i.e. Deng's formulas with `η → η γ(√(s + Tr Σ))`. The accuracy is second order in `ε` because of the
Stein identity (Gaussian integration by parts, `γ(N) = N^{p−1}`, `d ≥ 3`)

    E[γ(N) g] = E[γ(N)] μ − (1−p) Σ E[N^{p−3} g],                                             (2.2)

whose last term is `O(‖Σ‖_op/N̄²) = O(ε²)` relative to the first; it also shows that under anisotropic
noise the mean filtered gradient is *not* parallel to `Ax`: coordinates with large noise variance
are damped by `≈ 1 − (1−p) κ_i²/N̄²`.
Numerics (A4; `d ∈ {50, 200, 800}`; isotropic, power-law `κ_i² ∝ 1/i` and "one spike carrying 30% of
the trace" covariances; `TrΣ/s ∈ {0.1, 1, 10}`; Muon and HTMuon(1/8); `10⁵` samples): the relative
error of the mean-field values of `(E T^𝒟, E T^ℬ, E V^𝒟, E V^ℬ)` is `≤ 0.27%` when `ε < 0.15`, `≤ 1.5%`
when `0.15 ≤ ε < 0.5`, and `≤ 9.1%` for `0.5 ≤ ε ≤ 1.04`. The identity (2.2) is checked in S4
(Section 7).

