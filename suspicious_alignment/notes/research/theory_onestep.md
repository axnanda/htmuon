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

