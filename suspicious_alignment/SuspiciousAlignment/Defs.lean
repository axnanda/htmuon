import Mathlib

/-!
# Suspicious Alignment of SGD — core definitions

Formalization of the setup of

> S. Deng, B. Liao, Z. Ouyang, T. Pang, M. Song, Y. Yang,
> *Suspicious Alignment of SGD: A Fine-Grained Step Size Condition Analysis*,
> ALT 2026 (arXiv:2601.11789v2).

Everything in the paper takes place in the eigenbasis of the Hessian `A = U Λ Uᵀ` of the quadratic
loss `L(x) = ½ xᵀ A x`.  A state `x` is represented by its coefficients `c i = ⟪x, u_i⟫`, and the
SGD noise `ξ` by `ζ i = ⟪ξ, u_i⟫`, whose second moments are `κ_i² = u_iᵀ Σ u_i`.

* `Spec ι` is the spectrum `λ` together with the dominant block `D` (the bulk block is `B = Dᶜ`)
  and the four distinguished eigenvalues `λ_1 ≥ … ≥ λ_k > λ_{k+1} ≥ … ≥ λ_d > 0` of the paper.
  We do not order the index type; instead the structure records indices realising
  `λ_1 = max_D`, `λ_k = min_D`, `λ_{k+1} = max_B`, `λ_d = min_B` and the gap `λ_{k+1} < λ_k`.
  (`SuspiciousAlignment/MatrixBridge.lean` shows that a sorted spectrum on `Fin d` with
  `D = {i | i < k}` is an instance.)
* `Noise ι` records the per-direction noise variances `κ_i²` and the extreme eigenvalues
  `s_min ≤ κ_i² ≤ s_max` of the noise covariance `Σ`.

All quantities below are named after the paper (Section 3–6 and Appendix A); the docstring of each
definition gives the paper's formula.  Division by zero follows Lean's convention `x / 0 = 0`, which
matches the paper's convention `θ(0) = 0`.
-/

set_option linter.unusedSectionVars false

open Finset

namespace SuspiciousAlignment

/-- The Hessian spectrum in its eigenbasis, with the dominant/bulk partition (paper §3.2).

`lam i = λ_i`; `D` is the dominant index set `𝒟`, its complement the bulk `ℬ`;
`i1, ik, ik1, id` are indices carrying `λ_1, λ_k, λ_{k+1}, λ_d`. -/
structure Spec (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- eigenvalues `λ_i` of the Hessian `A` -/
  lam : ι → ℝ
  /-- the dominant index set `𝒟` -/
  D : Finset ι
  /-- index of `λ_1`, the largest (dominant) eigenvalue -/
  i1 : ι
  /-- index of `λ_k`, the smallest dominant eigenvalue -/
  ik : ι
  /-- index of `λ_{k+1}`, the largest bulk eigenvalue -/
  ik1 : ι
  /-- index of `λ_d`, the smallest (bulk) eigenvalue -/
  id : ι
  i1_mem : i1 ∈ D
  ik_mem : ik ∈ D
  ik1_not_mem : ik1 ∉ D
  id_not_mem : id ∉ D
  /-- `A` is positive definite: `λ_i > 0` -/
  lam_pos : ∀ i, 0 < lam i
  /-- `λ_i ≤ λ_1` on the dominant block -/
  le_lam1 : ∀ i ∈ D, lam i ≤ lam i1
  /-- `λ_k ≤ λ_i` on the dominant block -/
  lamk_le : ∀ i ∈ D, lam ik ≤ lam i
  /-- `λ_i ≤ λ_{k+1}` on the bulk block -/
  le_lamk1 : ∀ i ∉ D, lam i ≤ lam ik1
  /-- `λ_d ≤ λ_i` on the bulk block -/
  lamd_le : ∀ i ∉ D, lam id ≤ lam i
  /-- the spectral gap `λ_{k+1} < λ_k`, i.e. `gap₁ > 0` -/
  gap : lam ik1 < lam ik

/-- SGD noise seen in the Hessian eigenbasis (paper §3.2): `kap2 i = κ_i² = u_iᵀ Σ u_i`, and
`smin = λ_min(Σ)`, `smax = λ_max(Σ)`.  Since `Σ ⪰ 0`, `0 ≤ s_min ≤ κ_i² ≤ s_max`. -/
structure Noise (ι : Type*) where
  /-- per-eigendirection noise variance `κ_i² = u_iᵀ Σ u_i` -/
  kap2 : ι → ℝ
  /-- `s_min = λ_min(Σ)` -/
  smin : ℝ
  /-- `s_max = λ_max(Σ)` -/
  smax : ℝ
  smin_nonneg : 0 ≤ smin
  smin_le : ∀ i, smin ≤ kap2 i
  le_smax : ∀ i, kap2 i ≤ smax

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Spec

variable (P : Spec ι) (N : Noise ι)

/-! ### Spectrum -/

/-- The bulk index set `ℬ = 𝒟ᶜ`. -/
def B : Finset ι := P.Dᶜ

/-- `λ_1`, the largest eigenvalue. -/
def lam1 : ℝ := P.lam P.i1
/-- `λ_k`, the smallest dominant eigenvalue. -/
def lamk : ℝ := P.lam P.ik
/-- `λ_{k+1}`, the largest bulk eigenvalue. -/
def lamk1 : ℝ := P.lam P.ik1
/-- `λ_d`, the smallest eigenvalue. -/
def lamd : ℝ := P.lam P.id

/-- `gap₁ = λ_k - λ_{k+1}`. -/
def gap1 : ℝ := P.lamk - P.lamk1
/-- `gap₂ = λ_k² - λ_{k+1}²`. -/
def gap2 : ℝ := P.lamk ^ 2 - P.lamk1 ^ 2
/-- The spectral gap ratio `m = λ_k / λ_{k+1}`. -/
noncomputable def mRatio : ℝ := P.lamk / P.lamk1

/-- `k = |𝒟|` as a real number. -/
def kR : ℝ := (P.D.card : ℝ)
/-- `d - k = |ℬ|` as a real number. -/
def dkR : ℝ := (P.B.card : ℝ)
/-- The block proportion `ρ = k / (d - k)`. -/
noncomputable def rho : ℝ := P.kR / P.dkR

/-- `ψ_𝒟 = ∑_{i∈𝒟} λ_i²`. -/
def psiD : ℝ := ∑ i ∈ P.D, P.lam i ^ 2
/-- `ψ_ℬ = ∑_{i∈ℬ} λ_i²`. -/
def psiB : ℝ := ∑ i ∈ P.B, P.lam i ^ 2

/-! ### State-dependent energies (paper eq. (1), (5)) -/

/-- The weighted moment `∑_{i∈S} λ_i^p c_i²`. -/
def mom (S : Finset ι) (p : ℕ) (c : ι → ℝ) : ℝ := ∑ i ∈ S, P.lam i ^ p * c i ^ 2

/-- `s^𝒟 = ∑_{i∈𝒟} λ_i² c_i² = ‖P^𝒟 A x‖²`. -/
def sD (c : ι → ℝ) : ℝ := P.mom P.D 2 c
/-- `s^ℬ = ∑_{i∈ℬ} λ_i² c_i² = ‖P^ℬ A x‖²`. -/
def sB (c : ι → ℝ) : ℝ := P.mom P.B 2 c
/-- `s = s^𝒟 + s^ℬ = ‖A x‖²`. -/
def s (c : ι → ℝ) : ℝ := P.sD c + P.sB c
/-- `τ^𝒟 = ∑_{i∈𝒟} λ_i³ c_i²`. -/
def tauD (c : ι → ℝ) : ℝ := P.mom P.D 3 c
/-- `τ^ℬ = ∑_{i∈ℬ} λ_i³ c_i²`. -/
def tauB (c : ι → ℝ) : ℝ := P.mom P.B 3 c
/-- `‖x‖² = ∑_i c_i²`. -/
def normSq (c : ι → ℝ) : ℝ := ∑ i, c i ^ 2
/-- `‖P^𝒟 x‖² = ∑_{i∈𝒟} c_i²`. -/
def normSqD (c : ι → ℝ) : ℝ := ∑ i ∈ P.D, c i ^ 2

/-- The squared alignment `θ(x) = ‖P^𝒟 A x‖² / ‖A x‖² = s^𝒟 / s` of the gradient with the dominant
subspace (and `θ(0) = 0`, which is Lean's `0 / 0 = 0`). -/
noncomputable def theta (c : ι → ℝ) : ℝ := P.sD c / P.s c

/-- The ratio `μ^S(p, q) = (∑_{i∈S} λ_i^p c_i²) / (∑_{i∈S} λ_i^q c_i²)` of eq. (5). -/
noncomputable def mu (S : Finset ι) (p q : ℕ) (c : ι → ℝ) : ℝ := P.mom S p c / P.mom S q c

/-- The quadratic loss `L(x) = ½ xᵀ A x = ½ ∑_i λ_i c_i²`. -/
noncomputable def loss (c : ι → ℝ) : ℝ := (1 / 2) * ∑ i, P.lam i * c i ^ 2

/-! ### Noise energies -/

/-- `e_𝒟 = ∑_{i∈𝒟} λ_i² κ_i²`. -/
def eD : ℝ := ∑ i ∈ P.D, P.lam i ^ 2 * N.kap2 i
/-- `e_ℬ = ∑_{i∈ℬ} λ_i² κ_i²`. -/
def eB : ℝ := ∑ i ∈ P.B, P.lam i ^ 2 * N.kap2 i
/-- `n^loss_S = ∑_{i∈S} λ_i κ_i²` (eq. (5)). -/
def nLoss (S : Finset ι) : ℝ := ∑ i ∈ S, P.lam i * N.kap2 i
/-- `n^loss_𝒟`. -/
def nLossD : ℝ := P.nLoss N P.D
/-- `n^loss_ℬ`. -/
def nLossB : ℝ := P.nLoss N P.B

/-! ### One SGD step in the eigenbasis (Appendix A.2) -/

/-- One SGD step `x⁺ = x - η (A x + ξ)` in eigen-coordinates:
`c_i⁺ = (1 - η λ_i) c_i - η ζ_i`, with `ζ_i = ⟪ξ, u_i⟫`. -/
def cNext (η : ℝ) (c ζ : ι → ℝ) : ι → ℝ := fun i => (1 - η * P.lam i) * c i - η * ζ i

/-- One *projected* SGD step `x⁺ = x - η P^S (A x + ξ)` (DSGD for `S = 𝒟`, BSGD for `S = ℬ`,
paper eq. (3)–(4)): coordinates in `S` move as in SGD, the others are frozen. -/
def cNextProj (S : Finset ι) (η : ℝ) (c ζ : ι → ℝ) : ι → ℝ :=
  fun i => if i ∈ S then (1 - η * P.lam i) * c i - η * ζ i else c i

/-- The comparison functional `f_t(η) = s_t^ℬ s_{t+1}^𝒟 - s_{t+1}^ℬ s_t^𝒟` (eq. (12)), as a
function of the realised noise `ζ`. -/
def fCompare (η : ℝ) (c ζ : ι → ℝ) : ℝ :=
  P.sB c * P.sD (P.cNext η c ζ) - P.sB (P.cNext η c ζ) * P.sD c

/-- The conditional expectation `𝔼[∑_{i∈S} λ_i² c_{i,t+1}² | x_t]` of the next-step block energy
(Lemma "Elementwise expectation"), written out: `∑_{i∈S} (λ_i² (1-ηλ_i)² c_i² + η² λ_i² κ_i²)`. -/
def EsNext (S : Finset ι) (η : ℝ) (c : ι → ℝ) : ℝ :=
  ∑ i ∈ S, (P.lam i ^ 2 * (1 - η * P.lam i) ^ 2 * c i ^ 2 + η ^ 2 * P.lam i ^ 2 * N.kap2 i)

/-- The "deterministic equivalent" of the expected next alignment: the ratio of expectations
`𝔼[s_{t+1}^𝒟 | x_t] / 𝔼[s_{t+1} | x_t]`, to which `𝔼[θ_{t+1} | x_t]` converges as `d → ∞`
(Lemma "Asymptotic ratio of expectations"). -/
noncomputable def thetaBarNext (η : ℝ) (c : ι → ℝ) : ℝ :=
  P.EsNext N P.D η c / (P.EsNext N P.D η c + P.EsNext N P.B η c)

/-! ### Step-size condition theory (Section 4) -/

/-- The linear coefficient `q_t = 2 (s^𝒟 τ^ℬ - s^ℬ τ^𝒟)` of `𝔼[f_t(η) | x_t] = p_t η² + q_t η`. -/
def qCoef (c : ι → ℝ) : ℝ := 2 * (P.sD c * P.tauB c - P.sB c * P.tauD c)

/-- The quadratic coefficient
`p_t = s^ℬ (∑_{𝒟} λ⁴c² + e_𝒟) - s^𝒟 (∑_{ℬ} λ⁴c² + e_ℬ)`. -/
def pCoef (c : ι → ℝ) : ℝ :=
  P.sB c * (P.mom P.D 4 c + P.eD N) - P.sD c * (P.mom P.B 4 c + P.eB N)

/-- The adaptive critical step size `η*_t = -q_t / p_t` (paper eq. (2)). -/
noncomputable def etaStar (c : ι → ℝ) : ℝ := -P.qCoef c / P.pCoef N c

/-- The low-alignment threshold
`g_gap = 1 / (1 + (s_max/s_min) (1/ρ) (λ_{k+1}/λ_k)²)` of Theorem 3. -/
noncomputable def gGap : ℝ :=
  1 / (1 + N.smax / N.smin * (1 / P.rho) * (P.lamk1 / P.lamk) ^ 2)

/-- The auxiliary threshold `g_noise = (1 + s_max ψ_ℬ / (s_min ψ_𝒟))⁻¹` in the proof of Theorem 3. -/
noncomputable def gNoise : ℝ := (1 + N.smax * P.psiB / (N.smin * P.psiD))⁻¹

/-- `a^aux = s_min ψ_ℬ` (Theorem 4). -/
def aAux : ℝ := N.smin * P.psiB
/-- `h^aux = s_max ψ_𝒟` (Theorem 4). -/
def hAux : ℝ := N.smax * P.psiD
/-- `m^aux_t = s_t (λ_1² - λ_d²)` (Theorem 4). -/
def mAux (c : ι → ℝ) : ℝ := P.s c * (P.lam1 ^ 2 - P.lamd ^ 2)

/-- The quadratic `a r² + (a - m - h) r - h` of Theorem 4. -/
def auxQuad (c : ι → ℝ) (r : ℝ) : ℝ :=
  P.aAux N * r ^ 2 + (P.aAux N - P.mAux c - P.hAux N) * r - P.hAux N

/-- `r_{0,t}`: the positive root of `a r² + (a - m - h) r - h = 0` (Theorem 4). -/
noncomputable def r0 (c : ι → ℝ) : ℝ :=
  (-(P.aAux N - P.mAux c - P.hAux N) +
      Real.sqrt ((P.aAux N - P.mAux c - P.hAux N) ^ 2 + 4 * P.aAux N * P.hAux N)) /
    (2 * P.aAux N)

/-- The high-alignment threshold `θ*_t = r_{0,t} / (1 + r_{0,t})` of Theorem 4. -/
noncomputable def thetaStar (c : ι → ℝ) : ℝ := P.r0 N c / (1 + P.r0 N c)

/-! ### Projected SGD (Section 5) -/

/-- The loss threshold `η^loss_S = 2 s^S / (τ^S + n^loss_S)` of Theorem 10. -/
noncomputable def etaLoss (S : Finset ι) (c : ι → ℝ) : ℝ :=
  2 * P.mom S 2 c / (P.mom S 3 c + P.nLoss N S)

/-- `η^loss_𝒟`. -/
noncomputable def etaLossD (c : ι → ℝ) : ℝ := P.etaLoss N P.D c
/-- `η^loss_ℬ`. -/
noncomputable def etaLossB (c : ι → ℝ) : ℝ := P.etaLoss N P.B c

/-- The expected one-step loss change `𝔼[L(x_{t+1}) - L(x_t) | x_t]` of the `S`-projected update,
written out: `-η s^S + (η²/2) (τ^S + n^loss_S)`. -/
noncomputable def expLossChange (S : Finset ι) (η : ℝ) (c : ι → ℝ) : ℝ :=
  -η * P.mom S 2 c + η ^ 2 / 2 * (P.mom S 3 c + P.nLoss N S)

/-- `α_t = s_t (μ^𝒟(3,2) - μ^ℬ(3,2))` (eq. (6)). -/
noncomputable def alphaT (c : ι → ℝ) : ℝ := P.s c * (P.mu P.D 3 2 c - P.mu P.B 3 2 c)
/-- `β_t = -α_t + n^loss_ℬ + n^loss_𝒟` (eq. (7)). -/
noncomputable def betaT (c : ι → ℝ) : ℝ := -P.alphaT c + P.nLossB N + P.nLossD N
/-- `γ_t = -n^loss_𝒟` (eq. (8)). -/
def gammaT : ℝ := -P.nLossD N

/-- The quadratic `h(θ) = α_t θ² + β_t θ + γ_t` of Theorem 11. -/
noncomputable def hQuad (c : ι → ℝ) (θ : ℝ) : ℝ :=
  P.alphaT c * θ ^ 2 + P.betaT N c * θ + P.gammaT N

/-- The critical alignment `θ^crit_t`: the root of `h` in `(0, 1)` (Theorem 11), given by the
quadratic formula `(-β + √(β² - 4αγ)) / (2α)`. -/
noncomputable def thetaCrit (c : ι → ℝ) : ℝ :=
  (-P.betaT N c + Real.sqrt (P.betaT N c ^ 2 - 4 * P.alphaT c * P.gammaT N)) / (2 * P.alphaT c)

/-! ### Constant step size SGD (Section 6) -/

/-- `β_i = η κ_i² / (2 λ_i - η λ_i²)`, the stationary second moment of `c_i` under CSGD. -/
noncomputable def betaC (η : ℝ) (i : ι) : ℝ := η * N.kap2 i / (2 * P.lam i - η * P.lam i ^ 2)

/-- `ϱ_𝒟 = ∑_{i∈𝒟} (c_{i,0}² - β_i)`. -/
noncomputable def varrhoD (η : ℝ) (c0 : ι → ℝ) : ℝ := ∑ i ∈ P.D, (c0 i ^ 2 - P.betaC N η i)

/-- `δ = s_max ψ_𝒟 λ_1² / (λ_d² λ_k² (2(λ_k - λ_{k+1})/η - (λ_1² - λ_d²)))`. -/
noncomputable def deltaC (η : ℝ) : ℝ :=
  N.smax * P.psiD * P.lam1 ^ 2 /
    (P.lamd ^ 2 * P.lamk ^ 2 * (2 * (P.lamk - P.lamk1) / η - (P.lam1 ^ 2 - P.lamd ^ 2)))

/-- The length `t* = ⌊ log(ϱ_𝒟 / (δ - ∑_𝒟 β_i)) / (-2 log(1 - η λ_1)) ⌋` of the initial
alignment-decreasing phase (Theorem 15). -/
noncomputable def tStar (η : ℝ) (c0 : ι → ℝ) : ℕ :=
  ⌊Real.log (P.varrhoD N η c0 / (P.deltaC N η - ∑ i ∈ P.D, P.betaC N η i)) /
      (-2 * Real.log (1 - η * P.lam1))⌋₊

/-- The closed form `𝔼[c_{i,t}²] = (1 - ηλ_i)^{2t} (c_{i,0}² - β_i) + β_i` of the second moment of
the `i`-th coordinate under CSGD. -/
noncomputable def secondMoment (η : ℝ) (c0 : ι → ℝ) (t : ℕ) (i : ι) : ℝ :=
  (1 - η * P.lam i) ^ (2 * t) * (c0 i ^ 2 - P.betaC N η i) + P.betaC N η i

/-- The late-time alignment `θ_∞ = ∑_{𝒟} λ_i² β_i / ∑_i λ_i² β_i` of Theorem 16 (finite `d`). -/
noncomputable def thetaInf (η : ℝ) : ℝ :=
  (∑ i ∈ P.D, P.lam i ^ 2 * P.betaC N η i) / (∑ i, P.lam i ^ 2 * P.betaC N η i)

/-! ### Basic facts -/

theorem mem_B {i : ι} : i ∈ P.B ↔ i ∉ P.D := by simp [B]

theorem disjoint_D_B : Disjoint P.D P.B := by
  simpa [B] using (disjoint_compl_right : Disjoint P.D P.Dᶜ)

theorem D_union_B : P.D ∪ P.B = Finset.univ := by simp [B]

/-- Splitting a sum over all directions into dominant and bulk parts. -/
theorem sum_D_add_sum_B (f : ι → ℝ) : ∑ i ∈ P.D, f i + ∑ i ∈ P.B, f i = ∑ i, f i := by
  rw [← Finset.sum_union P.disjoint_D_B, P.D_union_B]

theorem s_eq_sum (c : ι → ℝ) : P.s c = ∑ i, P.lam i ^ 2 * c i ^ 2 := by
  simp only [s, sD, sB, mom]
  exact P.sum_D_add_sum_B _

theorem lam1_pos : 0 < P.lam1 := P.lam_pos _
theorem lamk_pos : 0 < P.lamk := P.lam_pos _
theorem lamk1_pos : 0 < P.lamk1 := P.lam_pos _
theorem lamd_pos : 0 < P.lamd := P.lam_pos _

theorem lamk1_lt_lamk : P.lamk1 < P.lamk := P.gap
theorem lamk_le_lam1 : P.lamk ≤ P.lam1 := P.le_lam1 _ P.ik_mem
theorem lamd_le_lamk1 : P.lamd ≤ P.lamk1 := P.lamd_le _ P.ik1_not_mem
theorem lamd_lt_lam1 : P.lamd < P.lam1 :=
  lt_of_le_of_lt P.lamd_le_lamk1 (lt_of_lt_of_le P.lamk1_lt_lamk P.lamk_le_lam1)

theorem gap1_pos : 0 < P.gap1 := sub_pos.mpr P.gap

theorem gap2_pos : 0 < P.gap2 := by
  have h1 := P.lamk1_pos
  have h2 := P.lamk1_lt_lamk
  unfold gap2
  nlinarith

theorem one_lt_mRatio : 1 < P.mRatio := by
  unfold mRatio
  rw [one_lt_div P.lamk1_pos]
  exact P.gap

theorem lamk_le_of_mem {i : ι} (hi : i ∈ P.D) : P.lamk ≤ P.lam i := P.lamk_le i hi
theorem le_lam1_of_mem {i : ι} (hi : i ∈ P.D) : P.lam i ≤ P.lam1 := P.le_lam1 i hi
theorem le_lamk1_of_mem_B {i : ι} (hi : i ∈ P.B) : P.lam i ≤ P.lamk1 :=
  P.le_lamk1 i (P.mem_B.mp hi)
theorem lamd_le_of_mem_B {i : ι} (hi : i ∈ P.B) : P.lamd ≤ P.lam i :=
  P.lamd_le i (P.mem_B.mp hi)

/-- `λ_d ≤ λ_i` for every direction. -/
theorem lamd_le_all (i : ι) : P.lamd ≤ P.lam i := by
  by_cases hi : i ∈ P.D
  · exact le_trans (le_trans P.lamd_le_lamk1 P.lamk1_lt_lamk.le) (P.lamk_le i hi)
  · exact P.lamd_le i hi

/-- `λ_i ≤ λ_1` for every direction. -/
theorem le_lam1_all (i : ι) : P.lam i ≤ P.lam1 := by
  by_cases hi : i ∈ P.D
  · exact P.le_lam1 i hi
  · exact le_trans (P.le_lamk1 i hi) (le_trans P.lamk1_lt_lamk.le P.lamk_le_lam1)

theorem D_nonempty : P.D.Nonempty := ⟨_, P.i1_mem⟩
theorem B_nonempty : P.B.Nonempty := ⟨_, P.mem_B.mpr P.ik1_not_mem⟩

theorem kR_pos : 0 < P.kR := by
  unfold kR; exact_mod_cast P.D_nonempty.card_pos
theorem dkR_pos : 0 < P.dkR := by
  unfold dkR; exact_mod_cast P.B_nonempty.card_pos
theorem rho_pos : 0 < P.rho := div_pos P.kR_pos P.dkR_pos

theorem mom_nonneg (S : Finset ι) (p : ℕ) (c : ι → ℝ) : 0 ≤ P.mom S p c :=
  Finset.sum_nonneg fun i _ => mul_nonneg (pow_nonneg (P.lam_pos i).le _) (sq_nonneg _)

theorem sD_nonneg (c : ι → ℝ) : 0 ≤ P.sD c := P.mom_nonneg _ _ _
theorem sB_nonneg (c : ι → ℝ) : 0 ≤ P.sB c := P.mom_nonneg _ _ _
theorem s_nonneg (c : ι → ℝ) : 0 ≤ P.s c := add_nonneg (P.sD_nonneg c) (P.sB_nonneg c)

theorem psiD_pos : 0 < P.psiD :=
  Finset.sum_pos (fun i _ => pow_pos (P.lam_pos i) 2) P.D_nonempty
theorem psiB_pos : 0 < P.psiB :=
  Finset.sum_pos (fun i _ => pow_pos (P.lam_pos i) 2) P.B_nonempty

theorem kap2_nonneg (i : ι) : 0 ≤ N.kap2 i := le_trans N.smin_nonneg (N.smin_le i)
theorem smin_le_smax [Nonempty ι] : N.smin ≤ N.smax :=
  le_trans (N.smin_le (Classical.arbitrary ι)) (N.le_smax _)
theorem smax_nonneg [Nonempty ι] : 0 ≤ N.smax := le_trans N.smin_nonneg (smin_le_smax N)

theorem eD_nonneg : 0 ≤ P.eD N :=
  Finset.sum_nonneg fun i _ => mul_nonneg (pow_nonneg (P.lam_pos i).le _) (kap2_nonneg N i)
theorem eB_nonneg : 0 ≤ P.eB N :=
  Finset.sum_nonneg fun i _ => mul_nonneg (pow_nonneg (P.lam_pos i).le _) (kap2_nonneg N i)

/-- `s_min ψ_𝒟 ≤ e_𝒟 ≤ s_max ψ_𝒟` (paper §3.2). -/
theorem smin_psiD_le_eD : N.smin * P.psiD ≤ P.eD N := by
  unfold psiD eD
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_left (N.smin_le i) (pow_nonneg (P.lam_pos i).le _)

theorem eD_le_smax_psiD : P.eD N ≤ N.smax * P.psiD := by
  unfold psiD eD
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => by
    rw [mul_comm (N.smax)]; exact mul_le_mul_of_nonneg_left (N.le_smax i) (pow_nonneg (P.lam_pos i).le _)

/-- `s_min ψ_ℬ ≤ e_ℬ ≤ s_max ψ_ℬ` (paper §3.2). -/
theorem smin_psiB_le_eB : N.smin * P.psiB ≤ P.eB N := by
  unfold psiB eB
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_left (N.smin_le i) (pow_nonneg (P.lam_pos i).le _)

theorem eB_le_smax_psiB : P.eB N ≤ N.smax * P.psiB := by
  unfold psiB eB
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => by
    rw [mul_comm (N.smax)]; exact mul_le_mul_of_nonneg_left (N.le_smax i) (pow_nonneg (P.lam_pos i).le _)

/-- `s(c) = 0` iff the state is `0` (as `λ_i > 0`): the paper's case `x_t = 0`. -/
theorem s_eq_zero_iff (c : ι → ℝ) : P.s c = 0 ↔ c = 0 := by
  rw [P.s_eq_sum]
  constructor
  · intro h
    have h' := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_nonneg (pow_nonneg (P.lam_pos i).le 2) (sq_nonneg (c i)))).mp h
    funext i
    have hi := h' i (Finset.mem_univ i)
    have hl : P.lam i ^ 2 ≠ 0 := pow_ne_zero 2 (P.lam_pos i).ne'
    have : c i ^ 2 = 0 := by
      rcases mul_eq_zero.mp hi with h0 | h0
      · exact absurd h0 hl
      · exact h0
    simpa using this
  · rintro rfl
    simp

theorem theta_nonneg (c : ι → ℝ) : 0 ≤ P.theta c := div_nonneg (P.sD_nonneg c) (P.s_nonneg c)

theorem theta_le_one (c : ι → ℝ) : P.theta c ≤ 1 := by
  unfold theta
  rcases (P.s_nonneg c).eq_or_lt with h | h
  · rw [← h]; simp
  · rw [div_le_one h]; unfold s; linarith [P.sB_nonneg c]

/-- `θ(0) = 0`. -/
@[simp] theorem theta_zero : P.theta (0 : ι → ℝ) = 0 := by
  simp [theta, sD, mom]

/-- `s^𝒟 = θ s`. -/
theorem sD_eq_theta_mul_s (c : ι → ℝ) : P.sD c = P.theta c * P.s c := by
  unfold theta
  rcases (P.s_nonneg c).eq_or_lt with h | h
  · have hD : P.sD c = 0 := by
      have := P.sD_nonneg c; have := P.sB_nonneg c; unfold s at h; linarith
    rw [hD]; simp
  · field_simp

/-- `s^ℬ = (1 - θ) s`. -/
theorem sB_eq_one_sub_theta_mul_s (c : ι → ℝ) : P.sB c = (1 - P.theta c) * P.s c := by
  have h := P.sD_eq_theta_mul_s c
  have : P.s c = P.sD c + P.sB c := rfl
  linarith

end Spec

end SuspiciousAlignment
