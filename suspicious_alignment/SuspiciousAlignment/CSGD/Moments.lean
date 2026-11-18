import Mathlib
import SuspiciousAlignment.Defs

/-!
# Constant step size SGD: second-moment dynamics and the late phase (paper §6, Theorem 16)

This file formalizes, for the paper

> S. Deng et al., *Suspicious Alignment of SGD: A Fine-Grained Step Size Condition Analysis*
> (arXiv:2601.11789v2), Section 6 and Appendix A.6 (tex lines 657–760, 2292–2320, 2407–2456),

the deterministic ("exact finite-`d`") content of the constant-step-size analysis:

* **(a) Second-moment recursion.**  `m_{t+1} = (1 - η λ_i)² m_t + η² κ_i²`, its fixed point
  `β_i = η κ_i² / (2 λ_i - η λ_i²)` (`Spec.betaC`) and its closed form
  `(1 - η λ_i)^{2t} (c_{i,0}² - β_i) + β_i` (`Spec.secondMoment`):
  `Spec.betaC_fixed_point`, `Spec.secondMoment_succ`, `Spec.eq_secondMoment_of_recursion`.
  A measure-theoretic derivation of the recursion from the SGD update is in
  `csgd_integral_step_sq` / `csgd_integral_sq_eq_secondMoment`.
* **(b) Stability.**  For `0 < η < 2/λ_1`: `|1 - η λ_i| < 1` and `𝔼[c_{i,t}²] → β_i`
  (`Spec.abs_one_sub_eta_lam_lt_one`, `Spec.tendsto_secondMoment`).
* **(c) Theorem 16, finite-`d` core.**  The expected block energies converge
  (`Spec.tendsto_expEnergyC`) and the ratio of expected energies converges to `θ_∞`
  (`Spec.tendsto_thetaBarCSGD`), with an explicit geometric rate
  (`Spec.abs_thetaBarCSGD_sub_thetaInf_le`).  The interchange of `lim_t` and `lim_d` is proved
  under a *uniform domination* hypothesis (`late_phase_interchange`,
  `late_phase_interchange_of_extensive_noise`) and shown to **fail** for a family satisfying the
  paper's Assumptions 1 and 14 literally
  (`LatePhaseCounterexample.late_phase_interchange_fails`).
* **(d) Interpretation paragraph.**  Small-step limit `θ_∞ → ∑_𝒟 λ_i κ_i² / ∑ λ_i κ_i²`
  (`Spec.tendsto_thetaInf_zero`, isotropic: `Spec.tendsto_thetaInf_isotropic`) with the two-sided
  quantitative bound `Spec.thetaSmallStep_le_thetaInf` / `Spec.thetaInf_sub_le`; large-gap bound
  `1 - θ_∞ ≤ (∑_ℬ κ² / ∑_𝒟 κ²) / m` (`Spec.one_sub_thetaInf_le_div_mRatio`) and its uniform
  consequences `thetaInf_tendsto_one_uniform`, `tendsto_thetaInf_one_of_gap`.
* **(e) Assumption 14.**  `Spec.CSGDStep`, `Spec.CSGDAssumption` and their consequences
  (`Spec.etaGapC_lt_two_div_lam1`: the `min` is redundant; `Spec.CSGDStep.abs_dom_lt_bulk`;
  `Spec.CSGDStep.deltaC_pos`; `Spec.CSGDStep.two_mul_sum_betaC_le_deltaC`), including the
  well-definedness analysis of `t*` (`Spec.CSGDAssumption.le_tStar_iff`,
  `Spec.CSGDAssumption.deltaC_lt_of_lt_tStar`, `CSGDMoments.ex_one_sub_eta_lam1_neg`,
  `CSGDMoments.ex_tStar_eq_zero`, `CSGDMoments.ex3_lower_bound_fails`).

Naming: CSGD-specific auxiliary definitions carry a suffix `C` (`expEnergyC`, `statEnergyC`,
`contrC`, `initExcessC`, `wEnergyC`, `etaGapC`), like `betaC`/`deltaC` in `Defs.lean`.  Concrete
examples live in the namespaces `CSGDMoments` and `LatePhaseCounterexample`.

See `notes/fidelity/CSGDMoments.md` for the comparison with the paper.
-/

set_option linter.unusedSectionVars false

open Finset Filter Topology

namespace SuspiciousAlignment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Spec

variable (P : Spec ι) (N : Noise ι)

/-! ### (b) The stability region `0 < η < 2/λ_1` -/

/-- `η < 2/λ_1` restated as `η λ_1 < 2`. -/
theorem eta_lam1_lt_two {η : ℝ} (h : η < 2 / P.lam1) : η * P.lam1 < 2 :=
  (lt_div_iff₀ P.lam1_pos).mp h

/-- In the stability region, `η λ_i < 2` for every direction. -/
theorem eta_lam_lt_two {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) (i : ι) : η * P.lam i < 2 :=
  lt_of_le_of_lt (mul_le_mul_of_nonneg_left (P.le_lam1_all i) hη.le) (P.eta_lam1_lt_two h)

theorem eta_lam_pos {η : ℝ} (hη : 0 < η) (i : ι) : 0 < η * P.lam i := mul_pos hη (P.lam_pos i)

theorem eta_lamk_lt_two {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) : η * P.lamk < 2 :=
  P.eta_lam_lt_two hη h P.ik

theorem eta_lamk1_lt_two {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) : η * P.lamk1 < 2 :=
  P.eta_lam_lt_two hη h P.ik1

theorem eta_lamd_lt_two {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) : η * P.lamd < 2 :=
  P.eta_lam_lt_two hη h P.id

/-- The denominator of `β_i` factors as `λ_i (2 - η λ_i)`. -/
theorem betaC_den_eq (η : ℝ) (i : ι) :
    2 * P.lam i - η * P.lam i ^ 2 = P.lam i * (2 - η * P.lam i) := by ring

/-- In the stability region the denominator `2 λ_i - η λ_i²` of `β_i` is positive. -/
theorem betaC_den_pos {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) (i : ι) :
    0 < 2 * P.lam i - η * P.lam i ^ 2 := by
  rw [P.betaC_den_eq]
  exact mul_pos (P.lam_pos i) (by linarith [P.eta_lam_lt_two hη h i])

/-- **Paper, proof of Theorem 16**: for `0 < η < 2/λ_1`, `|1 - η λ_i| < 1` for all `i`. -/
theorem abs_one_sub_eta_lam_lt_one {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) (i : ι) :
    |1 - η * P.lam i| < 1 := by
  rw [abs_lt]
  constructor <;> linarith [P.eta_lam_lt_two hη h i, P.eta_lam_pos hη i]

/-- `0 ≤ (1 - η λ_i)^{2t} ≤ 1` in the stability region. -/
theorem decayC_nonneg (η : ℝ) (t : ℕ) (i : ι) : 0 ≤ (1 - η * P.lam i) ^ (2 * t) := by
  rw [pow_mul]; positivity

theorem decayC_le_one {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) (t : ℕ) (i : ι) :
    (1 - η * P.lam i) ^ (2 * t) ≤ 1 := by
  rw [pow_mul]
  exact pow_le_one₀ (sq_nonneg _)
    ((sq_lt_one_iff_abs_lt_one _).mpr (P.abs_one_sub_eta_lam_lt_one hη h i)).le

/-- `(1 - η λ_i)^{2t} → 0` as `t → ∞` in the stability region. -/
theorem tendsto_decayC {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) (i : ι) :
    Tendsto (fun t : ℕ => (1 - η * P.lam i) ^ (2 * t)) atTop (𝓝 0) := by
  simp_rw [pow_mul]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg _)
    ((sq_lt_one_iff_abs_lt_one _).mpr (P.abs_one_sub_eta_lam_lt_one hη h i))

/-! ### (a) The stationary second moment `β_i` and the second-moment recursion -/

/-- `β_i ≥ 0` in the stability region. -/
theorem betaC_nonneg {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) (i : ι) : 0 ≤ P.betaC N η i :=
  div_nonneg (mul_nonneg hη.le (kap2_nonneg N i)) (P.betaC_den_pos hη h i).le

/-- **The paper's claim `β_i > 0` (tex 662, 750)** holds iff the noise is non-degenerate in the
direction `u_i`, i.e. `κ_i² > 0`.  The paper's assumptions (`Σ ⪰ 0`, `Tr Σ > 0`) do not imply this
for every `i`; `s_min > 0` (i.e. `Σ ≻ 0`) does. -/
theorem betaC_pos_iff {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) (i : ι) :
    0 < P.betaC N η i ↔ 0 < N.kap2 i := by
  unfold betaC
  rw [div_pos_iff_of_pos_right (P.betaC_den_pos hη h i)]
  exact mul_pos_iff_of_pos_left hη

/-- `β_i > 0` for every `i` when `s_min = λ_min(Σ) > 0`. -/
theorem betaC_pos {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) (hs : 0 < N.smin) (i : ι) :
    0 < P.betaC N η i :=
  (P.betaC_pos_iff N hη h i).mpr (lt_of_lt_of_le hs (N.smin_le i))

/-- `β_i = 0` when the noise vanishes in direction `i`: the paper's `β_i > 0` can fail. -/
theorem betaC_eq_zero_of_kap2_eq_zero {η : ℝ} {i : ι} (h : N.kap2 i = 0) : P.betaC N η i = 0 := by
  simp [betaC, h]

/-- `β_i` is the fixed point of the second-moment recursion
`m ↦ (1 - η λ_i)² m + η² κ_i²`.  Only `2 λ_i - η λ_i² ≠ 0` (i.e. `η ≠ 2/λ_i`) is needed. -/
theorem betaC_fixed_point {η : ℝ} {i : ι} (hden : 2 * P.lam i - η * P.lam i ^ 2 ≠ 0) :
    (1 - η * P.lam i) ^ 2 * P.betaC N η i + η ^ 2 * N.kap2 i = P.betaC N η i := by
  have hβ : P.betaC N η i * (2 * P.lam i - η * P.lam i ^ 2) = η * N.kap2 i :=
    div_mul_cancel₀ _ hden
  apply mul_right_cancel₀ hden
  linear_combination ((1 - η * P.lam i) ^ 2 - 1) * hβ

/-- `β_i` is the *unique* fixed point of the recursion when `η λ_i ∉ {0, 2}`. -/
theorem eq_betaC_of_fixed_point {η : ℝ} {i : ι} (hden : 2 * P.lam i - η * P.lam i ^ 2 ≠ 0)
    (hη : η ≠ 0) {b : ℝ} (hb : (1 - η * P.lam i) ^ 2 * b + η ^ 2 * N.kap2 i = b) :
    b = P.betaC N η i := by
  unfold betaC
  rw [eq_div_iff hden]
  have h2 : η * (b * (2 * P.lam i - η * P.lam i ^ 2) - η * N.kap2 i) = 0 := by
    linear_combination -hb
  rcases mul_eq_zero.mp h2 with h0 | h0
  · exact absurd h0 hη
  · linarith

@[simp] theorem secondMoment_zero (η : ℝ) (c0 : ι → ℝ) (i : ι) :
    P.secondMoment N η c0 0 i = c0 i ^ 2 := by
  simp [secondMoment]

/-- The closed form `Spec.secondMoment` satisfies the second-moment recursion
`𝔼[c_{i,t+1}²] = (1 - η λ_i)² 𝔼[c_{i,t}²] + η² κ_i²`. -/
theorem secondMoment_succ {η : ℝ} {i : ι} (hden : 2 * P.lam i - η * P.lam i ^ 2 ≠ 0)
    (c0 : ι → ℝ) (t : ℕ) :
    P.secondMoment N η c0 (t + 1) i =
      (1 - η * P.lam i) ^ 2 * P.secondMoment N η c0 t i + η ^ 2 * N.kap2 i := by
  have hfix := P.betaC_fixed_point N hden
  unfold secondMoment
  rw [show 2 * (t + 1) = 2 * t + 2 by ring, pow_add]
  linear_combination (-1 : ℝ) * hfix

/-- **Second-moment dynamics of CSGD (tex 2423–2427, 2160–2163).**  Any real sequence obeying the
recursion `m_{t+1} = (1 - η λ_i)² m_t + η² κ_i²` with `m_0 = c_{i,0}²` equals the closed form
`(1 - η λ_i)^{2t} (c_{i,0}² - β_i) + β_i`, provided `2 λ_i - η λ_i² ≠ 0` (true for
`0 < η < 2/λ_1`, see `eq_secondMoment_of_recursion'`). -/
theorem eq_secondMoment_of_recursion {η : ℝ} {i : ι} (hden : 2 * P.lam i - η * P.lam i ^ 2 ≠ 0)
    (c0 : ι → ℝ) (m : ℕ → ℝ) (h0 : m 0 = c0 i ^ 2)
    (hrec : ∀ t, m (t + 1) = (1 - η * P.lam i) ^ 2 * m t + η ^ 2 * N.kap2 i) (t : ℕ) :
    m t = P.secondMoment N η c0 t i := by
  induction t with
  | zero => rw [h0, secondMoment_zero]
  | succ t ih => rw [hrec, ih, P.secondMoment_succ N hden]

/-- The closed form under the paper's step-size condition `0 < η < 2/λ_1`. -/
theorem eq_secondMoment_of_recursion' {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) (i : ι)
    (c0 : ι → ℝ) (m : ℕ → ℝ) (h0 : m 0 = c0 i ^ 2)
    (hrec : ∀ t, m (t + 1) = (1 - η * P.lam i) ^ 2 * m t + η ^ 2 * N.kap2 i) (t : ℕ) :
    m t = P.secondMoment N η c0 t i :=
  P.eq_secondMoment_of_recursion N (P.betaC_den_pos hη h i).ne' c0 m h0 hrec t

/-- The hypothesis `2 λ_i - η λ_i² ≠ 0` cannot be dropped: at the stability boundary
`η = 2/λ_i` with `κ_i² ≠ 0` the true second moment grows linearly (`m_1 = c_{i,0}² + η² κ_i²`),
whereas the closed form (with Lean's `β_i = x/0 = 0`) stays at `c_{i,0}²`. -/
theorem secondMoment_ne_of_den_eq_zero {η : ℝ} {i : ι}
    (hden : 2 * P.lam i - η * P.lam i ^ 2 = 0) (hκ : N.kap2 i ≠ 0) (c0 : ι → ℝ) (m : ℕ → ℝ)
    (h0 : m 0 = c0 i ^ 2)
    (hrec : ∀ t, m (t + 1) = (1 - η * P.lam i) ^ 2 * m t + η ^ 2 * N.kap2 i) :
    m 1 ≠ P.secondMoment N η c0 1 i := by
  have hl := P.lam_pos i
  have hη : η * P.lam i = 2 := by
    have : P.lam i * (2 - η * P.lam i) = 0 := by rw [← P.betaC_den_eq]; exact hden
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hl.ne'
    · linarith
  have hη0 : η ≠ 0 := by rintro rfl; simp at hη
  have hβ : P.betaC N η i = 0 := by simp [betaC, hden]
  have h1 : m 1 = c0 i ^ 2 + η ^ 2 * N.kap2 i := by
    rw [hrec 0, h0, hη]; ring
  have h2 : P.secondMoment N η c0 1 i = c0 i ^ 2 := by
    simp only [secondMoment, hβ, hη]; ring
  rw [h1, h2]
  intro hEq
  have : η ^ 2 * N.kap2 i = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact hη0 (pow_eq_zero_iff (two_ne_zero) |>.mp h)
  · exact hκ h

/-- "Mean² + variance" form of the closed form (tex 2162):
`𝔼[c_{i,t}²] = (1-ηλ_i)^{2t} c_{i,0}² + β_i (1 - (1-ηλ_i)^{2t})`. -/
theorem secondMoment_eq_mean_add_var (η : ℝ) (c0 : ι → ℝ) (t : ℕ) (i : ι) :
    P.secondMoment N η c0 t i =
      (1 - η * P.lam i) ^ (2 * t) * c0 i ^ 2 +
        P.betaC N η i * (1 - (1 - η * P.lam i) ^ (2 * t)) := by
  unfold secondMoment; ring

/-- The closed-form second moment is non-negative in the stability region. -/
theorem secondMoment_nonneg {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) (c0 : ι → ℝ) (t : ℕ)
    (i : ι) : 0 ≤ P.secondMoment N η c0 t i := by
  rw [P.secondMoment_eq_mean_add_var]
  have h1 := P.decayC_nonneg η t i
  have h2 := P.decayC_le_one hη h t i
  have h3 := P.betaC_nonneg N hη h i
  have h4 := sq_nonneg (c0 i)
  nlinarith [mul_nonneg h1 h4, mul_nonneg h3 (sub_nonneg.mpr h2)]

/-- The closed-form second moment stays below `max (c_{i,0}²) β_i` (it is a convex combination). -/
theorem secondMoment_le_max {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) (c0 : ι → ℝ) (t : ℕ)
    (i : ι) : P.secondMoment N η c0 t i ≤ max (c0 i ^ 2) (P.betaC N η i) := by
  rw [P.secondMoment_eq_mean_add_var]
  have h1 := P.decayC_nonneg η t i
  have h2 := P.decayC_le_one hη h t i
  have h3 := le_max_left (c0 i ^ 2) (P.betaC N η i)
  have h4 := le_max_right (c0 i ^ 2) (P.betaC N η i)
  nlinarith [mul_le_mul_of_nonneg_left h3 h1, mul_le_mul_of_nonneg_right h4 (sub_nonneg.mpr h2)]

/-- **Paper, proof of Theorem 16 (tex 2428–2431)**: `lim_{t→∞} 𝔼[c_{i,t}²] = β_i` for
`0 < η < 2/λ_1`. -/
theorem tendsto_secondMoment {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) (c0 : ι → ℝ) (i : ι) :
    Tendsto (fun t => P.secondMoment N η c0 t i) atTop (𝓝 (P.betaC N η i)) := by
  have := ((P.tendsto_decayC hη h i).mul_const (c0 i ^ 2 - P.betaC N η i)).add_const
    (P.betaC N η i)
  simpa [secondMoment] using this

/-! ### (c) Expected block energies and the ratio of expectations -/

/-- The expected block energy `𝔼[s_t^S] = ∑_{i∈S} λ_i² 𝔼[c_{i,t}²]` under CSGD (tex 2433–2437),
with `𝔼[c_{i,t}²]` given by the closed form `Spec.secondMoment`. -/
noncomputable def expEnergyC (S : Finset ι) (η : ℝ) (c0 : ι → ℝ) (t : ℕ) : ℝ :=
  ∑ i ∈ S, P.lam i ^ 2 * P.secondMoment N η c0 t i

/-- The stationary block energy `∑_{i∈S} λ_i² β_i` (tex 2440–2441). -/
noncomputable def statEnergyC (S : Finset ι) (η : ℝ) : ℝ := ∑ i ∈ S, P.lam i ^ 2 * P.betaC N η i

/-- The ratio of expected energies `𝔼[s_t^𝒟] / 𝔼[s_t]` under CSGD: the deterministic equivalent of
`𝔼[θ_t]` used in the paper's proof of Theorem 16 (tex 2444–2447). -/
noncomputable def thetaBarCSGD (η : ℝ) (c0 : ι → ℝ) (t : ℕ) : ℝ :=
  P.expEnergyC N P.D η c0 t / P.expEnergyC N Finset.univ η c0 t

/-- The initial excess energy `∑_{i∈S} λ_i² |c_{i,0}² - β_i|`, which controls the transient. -/
noncomputable def initExcessC (S : Finset ι) (η : ℝ) (c0 : ι → ℝ) : ℝ :=
  ∑ i ∈ S, P.lam i ^ 2 * |c0 i ^ 2 - P.betaC N η i|

theorem thetaInf_eq_statEnergyC (η : ℝ) :
    P.thetaInf N η = P.statEnergyC N P.D η / P.statEnergyC N Finset.univ η := rfl

/-- `𝔼[s_t] = 𝔼[s_t^𝒟] + 𝔼[s_t^ℬ]`. -/
theorem expEnergyC_D_add_B (η : ℝ) (c0 : ι → ℝ) (t : ℕ) :
    P.expEnergyC N P.D η c0 t + P.expEnergyC N P.B η c0 t = P.expEnergyC N Finset.univ η c0 t :=
  P.sum_D_add_sum_B _

theorem statEnergyC_D_add_B (η : ℝ) :
    P.statEnergyC N P.D η + P.statEnergyC N P.B η = P.statEnergyC N Finset.univ η :=
  P.sum_D_add_sum_B _

/-- At `t = 0` the expected energy is the initial energy `∑_S λ_i² c_{i,0}²`. -/
theorem expEnergyC_zero (S : Finset ι) (η : ℝ) (c0 : ι → ℝ) :
    P.expEnergyC N S η c0 0 = P.mom S 2 c0 := by
  simp [expEnergyC, mom]

/-- At `t = 0` the ratio of expected energies is the initial alignment `θ(x_0)`. -/
theorem thetaBarCSGD_zero (η : ℝ) (c0 : ι → ℝ) : P.thetaBarCSGD N η c0 0 = P.theta c0 := by
  unfold thetaBarCSGD theta
  rw [← P.expEnergyC_D_add_B, P.expEnergyC_zero, P.expEnergyC_zero]
  rfl

theorem expEnergyC_nonneg {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) (S : Finset ι) (c0 : ι → ℝ)
    (t : ℕ) : 0 ≤ P.expEnergyC N S η c0 t :=
  Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (P.secondMoment_nonneg N hη h c0 t i)

theorem statEnergyC_nonneg {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) (S : Finset ι) :
    0 ≤ P.statEnergyC N S η :=
  Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (P.betaC_nonneg N hη h i)

/-- The stationary block energy is positive iff the noise is non-zero somewhere on the block. -/
theorem statEnergyC_pos_iff {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) (S : Finset ι) :
    0 < P.statEnergyC N S η ↔ ∃ i ∈ S, 0 < N.kap2 i := by
  constructor
  · intro hpos
    by_contra hne
    push Not at hne
    have : P.statEnergyC N S η = 0 :=
      Finset.sum_eq_zero fun i hi => by
        have : N.kap2 i = 0 := le_antisymm (hne i hi) (kap2_nonneg N i)
        rw [P.betaC_eq_zero_of_kap2_eq_zero N this, mul_zero]
    linarith
  · rintro ⟨i, hi, hκ⟩
    exact Finset.sum_pos' (fun j _ => mul_nonneg (sq_nonneg _) (P.betaC_nonneg N hη h j))
      ⟨i, hi, mul_pos (pow_pos (P.lam_pos i) 2) ((P.betaC_pos_iff N hη h i).mpr hκ)⟩

/-- The total stationary energy `∑_i λ_i² β_i` is positive as soon as `κ_i² > 0` for some `i`,
i.e. as soon as `Tr Σ > 0` (Assumption 1). -/
theorem statEnergyC_univ_pos {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) (hκ : ∃ i, 0 < N.kap2 i) :
    0 < P.statEnergyC N Finset.univ η := by
  obtain ⟨i, hi⟩ := hκ
  exact (P.statEnergyC_pos_iff N hη h _).mpr ⟨i, Finset.mem_univ i, hi⟩

/-- `∃ i, κ_i² > 0` is the finite-`d` meaning of `Tr Σ = ∑_i κ_i² > 0`. -/
theorem exists_kap2_pos_iff_trace_pos : (∃ i, 0 < N.kap2 i) ↔ 0 < ∑ i, N.kap2 i := by
  constructor
  · rintro ⟨i, hi⟩
    exact Finset.sum_pos' (fun j _ => kap2_nonneg N j) ⟨i, Finset.mem_univ i, hi⟩
  · intro hpos
    by_contra hne
    push Not at hne
    have : ∑ i, N.kap2 i = 0 :=
      Finset.sum_eq_zero fun i _ => le_antisymm (hne i) (kap2_nonneg N i)
    linarith

/-- **Paper (tex 2438–2442)**: `lim_{t→∞} 𝔼[s_t^S] = ∑_{i∈S} λ_i² β_i` for every block `S`. -/
theorem tendsto_expEnergyC {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) (S : Finset ι)
    (c0 : ι → ℝ) :
    Tendsto (fun t => P.expEnergyC N S η c0 t) atTop (𝓝 (P.statEnergyC N S η)) :=
  tendsto_finsetSum S fun i _ => (P.tendsto_secondMoment N hη h c0 i).const_mul _

/-- **Theorem 16 (Late Phase), exact finite-`d` core.**  For `0 < η < 2/λ_1` and non-zero noise
(`κ_i² > 0` for some `i`, i.e. `Tr Σ > 0`), the ratio of expected energies converges:
`lim_{t→∞} 𝔼[s_t^𝒟] / 𝔼[s_t] = θ_∞ = ∑_𝒟 λ_i² β_i / ∑_i λ_i² β_i`. -/
theorem tendsto_thetaBarCSGD {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1)
    (hκ : ∃ i, 0 < N.kap2 i) (c0 : ι → ℝ) :
    Tendsto (fun t => P.thetaBarCSGD N η c0 t) atTop (𝓝 (P.thetaInf N η)) :=
  (P.tendsto_expEnergyC N hη h P.D c0).div (P.tendsto_expEnergyC N hη h Finset.univ c0)
    (P.statEnergyC_univ_pos N hη h hκ).ne'

/-! ### (c') Quantitative rate: the rigorous form of the paper's "uniform convergence" -/

/-- The worst-case contraction factor `max_i |1 - η λ_i| = max (η λ_1 - 1) (1 - η λ_d)`. -/
def contrC (η : ℝ) : ℝ := max (η * P.lam1 - 1) (1 - η * P.lamd)

theorem abs_one_sub_le_contrC {η : ℝ} (hη : 0 ≤ η) (i : ι) : |1 - η * P.lam i| ≤ P.contrC η := by
  have h1 := mul_le_mul_of_nonneg_left (P.le_lam1_all i) hη
  have h2 := mul_le_mul_of_nonneg_left (P.lamd_le_all i) hη
  have h3 := le_max_left (η * P.lam1 - 1) (1 - η * P.lamd)
  have h4 := le_max_right (η * P.lam1 - 1) (1 - η * P.lamd)
  rw [abs_le]; unfold contrC
  constructor <;> linarith

theorem contrC_nonneg {η : ℝ} (hη : 0 ≤ η) : 0 ≤ P.contrC η :=
  le_trans (abs_nonneg _) (P.abs_one_sub_le_contrC hη P.i1)

/-- In the stability region the contraction factor is `< 1`. -/
theorem contrC_lt_one {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) : P.contrC η < 1 := by
  unfold contrC
  exact max_lt (by linarith [P.eta_lam1_lt_two h]) (by linarith [mul_pos hη P.lamd_pos])

/-- Geometric convergence of each second moment:
`|𝔼[c_{i,t}²] - β_i| ≤ r^{2t} |c_{i,0}² - β_i|` with `r = max_j |1 - η λ_j|`. -/
theorem abs_secondMoment_sub_betaC_le {η : ℝ} (hη : 0 ≤ η) (c0 : ι → ℝ) (t : ℕ) (i : ι) :
    |P.secondMoment N η c0 t i - P.betaC N η i| ≤
      P.contrC η ^ (2 * t) * |c0 i ^ 2 - P.betaC N η i| := by
  have : P.secondMoment N η c0 t i - P.betaC N η i =
      (1 - η * P.lam i) ^ (2 * t) * (c0 i ^ 2 - P.betaC N η i) := by
    unfold secondMoment; ring
  rw [this, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg _) (P.abs_one_sub_le_contrC hη i) _) (abs_nonneg _)

theorem initExcessC_nonneg (S : Finset ι) (η : ℝ) (c0 : ι → ℝ) : 0 ≤ P.initExcessC N S η c0 :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (abs_nonneg _)

theorem initExcessC_le_univ (S : Finset ι) (η : ℝ) (c0 : ι → ℝ) :
    P.initExcessC N S η c0 ≤ P.initExcessC N Finset.univ η c0 :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    fun _ _ _ => mul_nonneg (sq_nonneg _) (abs_nonneg _)

/-- Geometric convergence of the expected block energies:
`|𝔼[s_t^S] - ∑_S λ_i² β_i| ≤ r^{2t} ∑_S λ_i² |c_{i,0}² - β_i|`. -/
theorem abs_expEnergyC_sub_statEnergyC_le {η : ℝ} (hη : 0 ≤ η) (S : Finset ι) (c0 : ι → ℝ)
    (t : ℕ) :
    |P.expEnergyC N S η c0 t - P.statEnergyC N S η| ≤
      P.contrC η ^ (2 * t) * P.initExcessC N S η c0 := by
  unfold expEnergyC statEnergyC initExcessC
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg (P.lam i))]
  calc P.lam i ^ 2 * |P.secondMoment N η c0 t i - P.betaC N η i|
      ≤ P.lam i ^ 2 * (P.contrC η ^ (2 * t) * |c0 i ^ 2 - P.betaC N η i|) :=
        mul_le_mul_of_nonneg_left (P.abs_secondMoment_sub_betaC_le N hη c0 t i) (sq_nonneg _)
    _ = P.contrC η ^ (2 * t) * (P.lam i ^ 2 * |c0 i ^ 2 - P.betaC N η i|) := by ring

theorem expEnergyC_D_le_univ {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) (c0 : ι → ℝ) (t : ℕ) :
    P.expEnergyC N P.D η c0 t ≤ P.expEnergyC N Finset.univ η c0 t :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun i _ _ => mul_nonneg (sq_nonneg _) (P.secondMoment_nonneg N hη h c0 t i)

theorem thetaBarCSGD_nonneg {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) (c0 : ι → ℝ) (t : ℕ) :
    0 ≤ P.thetaBarCSGD N η c0 t :=
  div_nonneg (P.expEnergyC_nonneg N hη h _ c0 t) (P.expEnergyC_nonneg N hη h _ c0 t)

theorem thetaBarCSGD_le_one {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) (c0 : ι → ℝ) (t : ℕ) :
    P.thetaBarCSGD N η c0 t ≤ 1 :=
  div_le_one_of_le₀ (P.expEnergyC_D_le_univ N hη h c0 t) (P.expEnergyC_nonneg N hη h _ c0 t)

/-- **Theorem 16, quantitative finite-`d` form.**  For `0 < η < 2/λ_1` and non-zero noise,
```
|𝔼[s_t^𝒟]/𝔼[s_t] - θ_∞| ≤ 2 r^{2t} (∑_i λ_i² |c_{i,0}² - β_i|) / (∑_i λ_i² β_i),
```
with `r = max (η λ_1 - 1) (1 - η λ_d) < 1`.  The bound is uniform in the dimension exactly when
the initial excess energy is dominated by the stationary energy uniformly in `d`; this is what
the paper's "uniform convergence" argument (tex 2448) actually needs. -/
theorem abs_thetaBarCSGD_sub_thetaInf_le {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1)
    (hpos : 0 < P.statEnergyC N Finset.univ η) (c0 : ι → ℝ) (t : ℕ) :
    |P.thetaBarCSGD N η c0 t - P.thetaInf N η| ≤
      2 * P.contrC η ^ (2 * t) * P.initExcessC N Finset.univ η c0 /
        P.statEnergyC N Finset.univ η := by
  have hNt0 := P.expEnergyC_nonneg N hη h P.D c0 t
  have hTt0 := P.expEnergyC_nonneg N hη h Finset.univ c0 t
  have hNT := P.expEnergyC_D_le_univ N hη h c0 t
  have hθ0 := P.thetaBarCSGD_nonneg N hη h c0 t
  have hθ1 := P.thetaBarCSGD_le_one N hη h c0 t
  have hθT : P.thetaBarCSGD N η c0 t * P.expEnergyC N Finset.univ η c0 t =
      P.expEnergyC N P.D η c0 t := by
    unfold thetaBarCSGD
    rcases hTt0.eq_or_lt with h0 | h0
    · rw [← h0, mul_zero]; linarith
    · exact div_mul_cancel₀ _ h0.ne'
  have hD := P.abs_expEnergyC_sub_statEnergyC_le N hη.le P.D c0 t
  have hU := P.abs_expEnergyC_sub_statEnergyC_le N hη.le Finset.univ c0 t
  have hED := P.initExcessC_le_univ N P.D η c0
  have hr : 0 ≤ P.contrC η ^ (2 * t) := pow_nonneg (P.contrC_nonneg hη.le) _
  have key : P.thetaBarCSGD N η c0 t - P.thetaInf N η =
      ((P.expEnergyC N P.D η c0 t - P.statEnergyC N P.D η) -
        P.thetaBarCSGD N η c0 t *
          (P.expEnergyC N Finset.univ η c0 t - P.statEnergyC N Finset.univ η)) /
        P.statEnergyC N Finset.univ η := by
    rw [P.thetaInf_eq_statEnergyC, eq_div_iff hpos.ne', sub_mul, div_mul_cancel₀ _ hpos.ne']
    linear_combination hθT
  rw [key, abs_div, abs_of_pos hpos]
  apply div_le_div_of_nonneg_right _ hpos.le
  calc |(P.expEnergyC N P.D η c0 t - P.statEnergyC N P.D η) -
          P.thetaBarCSGD N η c0 t *
            (P.expEnergyC N Finset.univ η c0 t - P.statEnergyC N Finset.univ η)|
      ≤ |P.expEnergyC N P.D η c0 t - P.statEnergyC N P.D η| +
          |P.thetaBarCSGD N η c0 t *
            (P.expEnergyC N Finset.univ η c0 t - P.statEnergyC N Finset.univ η)| := abs_sub _ _
    _ ≤ P.contrC η ^ (2 * t) * P.initExcessC N Finset.univ η c0 +
          P.contrC η ^ (2 * t) * P.initExcessC N Finset.univ η c0 := by
        apply add_le_add
        · exact hD.trans (mul_le_mul_of_nonneg_left hED hr)
        · rw [abs_mul, abs_of_nonneg hθ0]
          calc P.thetaBarCSGD N η c0 t *
                |P.expEnergyC N Finset.univ η c0 t - P.statEnergyC N Finset.univ η|
              ≤ 1 * |P.expEnergyC N Finset.univ η c0 t - P.statEnergyC N Finset.univ η| :=
                mul_le_mul_of_nonneg_right hθ1 (abs_nonneg _)
            _ ≤ _ := by rw [one_mul]; exact hU
    _ = 2 * P.contrC η ^ (2 * t) * P.initExcessC N Finset.univ η c0 := by ring

/-! ### Stationary energies versus the noise trace (well-definedness of Theorem 16's display) -/

/-- `λ_i² β_i = η λ_i κ_i² / (2 - η λ_i)` (valid for every `η`, including `η λ_i = 2` where both
sides are `0` by Lean's convention). -/
theorem lam_sq_mul_betaC (η : ℝ) (i : ι) :
    P.lam i ^ 2 * P.betaC N η i = η * (P.lam i * N.kap2 i / (2 - η * P.lam i)) := by
  have hl := (P.lam_pos i).ne'
  unfold betaC
  rw [P.betaC_den_eq]
  by_cases h2 : 2 - η * P.lam i = 0
  · simp [h2]
  · field_simp

/-- **Theorem 16, "Equivalently" display (tex 751–753).**
`θ_∞ = ∑_𝒟 η λ_i² κ_i² / (2 λ_i - η λ_i²) / ∑_i η λ_i² κ_i² / (2 λ_i - η λ_i²)`. -/
theorem thetaInf_eq_equivalently (η : ℝ) :
    P.thetaInf N η =
      (∑ i ∈ P.D, η * P.lam i ^ 2 * N.kap2 i / (2 * P.lam i - η * P.lam i ^ 2)) /
        (∑ i, η * P.lam i ^ 2 * N.kap2 i / (2 * P.lam i - η * P.lam i ^ 2)) := by
  unfold thetaInf betaC
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

/-- Upper bound of the stationary energy by the noise trace on the block:
`∑_S λ_i² β_i ≤ (η λ_1 / (2 - η λ_1)) ∑_S κ_i²`.  In particular a *bounded* `Tr Σ`
(Assumption 1 as literally stated) makes the unnormalised sums of Theorem 16 bounded in `d`. -/
theorem statEnergyC_le_trace {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) (S : Finset ι) :
    P.statEnergyC N S η ≤ η * P.lam1 / (2 - η * P.lam1) * ∑ i ∈ S, N.kap2 i := by
  unfold statEnergyC
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [P.lam_sq_mul_betaC]
  have h1 := P.eta_lam1_lt_two h
  have hi := P.eta_lam_lt_two hη h i
  have hκ := kap2_nonneg N i
  have hle := P.le_lam1_all i
  have hl := P.lam_pos i
  have key : P.lam i / (2 - η * P.lam i) ≤ P.lam1 / (2 - η * P.lam1) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  calc η * (P.lam i * N.kap2 i / (2 - η * P.lam i))
      = η * (P.lam i / (2 - η * P.lam i)) * N.kap2 i := by ring
    _ ≤ η * (P.lam1 / (2 - η * P.lam1)) * N.kap2 i :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left key hη.le) hκ
    _ = η * P.lam1 / (2 - η * P.lam1) * N.kap2 i := by ring

/-- Lower bound of the stationary energy by the noise trace on the block:
`(η λ_d / 2) ∑_S κ_i² ≤ ∑_S λ_i² β_i`. -/
theorem trace_le_statEnergyC {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) (S : Finset ι) :
    η * P.lamd / 2 * ∑ i ∈ S, N.kap2 i ≤ P.statEnergyC N S η := by
  unfold statEnergyC
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [P.lam_sq_mul_betaC]
  have hi := P.eta_lam_lt_two hη h i
  have hκ := kap2_nonneg N i
  have hle := P.lamd_le_all i
  have hl := P.lam_pos i
  have hd := P.lamd_pos
  have key : P.lamd / 2 ≤ P.lam i / (2 - η * P.lam i) := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith [mul_pos hη hl, mul_pos (mul_pos hη hl) hd]
  calc η * P.lamd / 2 * N.kap2 i = η * (P.lamd / 2) * N.kap2 i := by ring
    _ ≤ η * (P.lam i / (2 - η * P.lam i)) * N.kap2 i :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left key hη.le) hκ
    _ = η * (P.lam i * N.kap2 i / (2 - η * P.lam i)) := by ring

/-- `d · s_min ≤ Tr Σ`: a bounded trace forces `s_min = O(1/d)`. -/
theorem card_mul_smin_le_trace : (Fintype.card ι : ℝ) * N.smin ≤ ∑ i, N.kap2 i := by
  have : ∑ _i : ι, N.smin ≤ ∑ i, N.kap2 i := Finset.sum_le_sum fun i _ => N.smin_le i
  simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this

/-- Conversely, if `s_min > 0` is fixed, the unnormalised stationary energy grows at least
linearly in the dimension: `d · s_min · η λ_d / 2 ≤ ∑_i λ_i² β_i`.  So with `s_min` bounded below
the two limits `lim_{d→∞} ∑ λ_i² β_i` in Theorem 16's display are `+∞`. -/
theorem card_mul_smin_le_statEnergyC {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) :
    η * P.lamd / 2 * ((Fintype.card ι : ℝ) * N.smin) ≤ P.statEnergyC N Finset.univ η :=
  le_trans (mul_le_mul_of_nonneg_left (card_mul_smin_le_trace N)
    (by have := P.lamd_pos; positivity)) (P.trace_le_statEnergyC N hη h _)

/-- The initial excess energy is at most `λ_1² ‖x_0‖² + ∑_i λ_i² β_i`. -/
theorem initExcessC_univ_le {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) (c0 : ι → ℝ) :
    P.initExcessC N Finset.univ η c0 ≤
      P.lam1 ^ 2 * Spec.normSq c0 + P.statEnergyC N Finset.univ η := by
  unfold initExcessC normSq statEnergyC
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hβ := P.betaC_nonneg N hη h i
  have hc := sq_nonneg (c0 i)
  have habs : |c0 i ^ 2 - P.betaC N η i| ≤ c0 i ^ 2 + P.betaC N η i := by
    rw [abs_le]; constructor <;> linarith
  have hl : P.lam i ^ 2 ≤ P.lam1 ^ 2 := pow_le_pow_left₀ (P.lam_pos i).le (P.le_lam1_all i) 2
  calc P.lam i ^ 2 * |c0 i ^ 2 - P.betaC N η i|
      ≤ P.lam i ^ 2 * (c0 i ^ 2 + P.betaC N η i) :=
        mul_le_mul_of_nonneg_left habs (sq_nonneg _)
    _ = P.lam i ^ 2 * c0 i ^ 2 + P.lam i ^ 2 * P.betaC N η i := by ring
    _ ≤ P.lam1 ^ 2 * c0 i ^ 2 + P.lam i ^ 2 * P.betaC N η i := by
        have := mul_le_mul_of_nonneg_right hl hc
        linarith

end Spec

/-! ### Interchange of `lim_t` and `lim_d` under uniform domination -/

/-- **Theorem 16, interchange of limits (deterministic-equivalent level).**
Consider a sequence of problems indexed by `d` (index types `ι d`, spectra `P d`, noises `N d`,
initial states `c0 d`) with a common step size `η`.  Assume
* uniform stability: `0 < η < 2/λ_1(d)` and `max_i |1 - η λ_i| ≤ r < 1` for all `d`;
* **uniform domination**: `∑_i λ_i² |c_{i,0}² - β_i| ≤ C ∑_i λ_i² β_i` for all `d`
  (initial excess energy at most a constant multiple of the stationary energy);
* for each fixed `t`, `L t = lim_{d→∞} 𝔼[s_t^𝒟]/𝔼[s_t]` exists, and
  `θ_∞ = lim_{d→∞} θ_∞(d)` exists.
Then `lim_{t→∞} L t = θ_∞`, i.e. `lim_t lim_d = lim_d lim_t` for the ratio of expected energies.
The uniform-domination hypothesis is what the paper's "uniform convergence" sentence (tex 2448)
needs; it is *not* implied by Assumptions 1 and 14 (see
`LatePhaseCounterexample.late_phase_interchange_fails`). -/
theorem late_phase_interchange {ι : ℕ → Type*} [∀ d, Fintype (ι d)] [∀ d, DecidableEq (ι d)]
    (P : ∀ d, Spec (ι d)) (N : ∀ d, Noise (ι d)) (c0 : ∀ d, ι d → ℝ) {η : ℝ} (hη : 0 < η)
    (hstab : ∀ d, η < 2 / (P d).lam1) {r : ℝ} (hr : r < 1) (hcontr : ∀ d, (P d).contrC η ≤ r)
    (hpos : ∀ d, 0 < (P d).statEnergyC (N d) Finset.univ η) {C : ℝ}
    (hdom : ∀ d, (P d).initExcessC (N d) Finset.univ η (c0 d) ≤
      C * (P d).statEnergyC (N d) Finset.univ η)
    {L : ℕ → ℝ}
    (hL : ∀ t, Tendsto (fun d => (P d).thetaBarCSGD (N d) η (c0 d) t) atTop (𝓝 (L t)))
    {θ : ℝ} (hθ : Tendsto (fun d => (P d).thetaInf (N d) η) atTop (𝓝 θ)) :
    Tendsto L atTop (𝓝 θ) := by
  have hr0 : 0 ≤ r := le_trans ((P 0).contrC_nonneg hη.le) (hcontr 0)
  have hC0 : 0 ≤ C := by
    have h1 := (P 0).initExcessC_nonneg (N 0) Finset.univ η (c0 0)
    have h2 := hdom 0
    have h3 := hpos 0
    by_contra hneg
    push Not at hneg
    nlinarith
  -- uniform-in-`d` bound
  have hbound : ∀ t d, |(P d).thetaBarCSGD (N d) η (c0 d) t - (P d).thetaInf (N d) η| ≤
      2 * C * r ^ (2 * t) := by
    intro t d
    refine ((P d).abs_thetaBarCSGD_sub_thetaInf_le (N d) hη (hstab d) (hpos d) (c0 d) t).trans ?_
    rw [div_le_iff₀ (hpos d)]
    have h1 : (P d).contrC η ^ (2 * t) ≤ r ^ (2 * t) :=
      pow_le_pow_left₀ ((P d).contrC_nonneg hη.le) (hcontr d) _
    have h2 := (P d).initExcessC_nonneg (N d) Finset.univ η (c0 d)
    have h3 : 0 ≤ r ^ (2 * t) := pow_nonneg hr0 _
    calc 2 * (P d).contrC η ^ (2 * t) * (P d).initExcessC (N d) Finset.univ η (c0 d)
        ≤ 2 * r ^ (2 * t) * (P d).initExcessC (N d) Finset.univ η (c0 d) := by gcongr
      _ ≤ 2 * r ^ (2 * t) * (C * (P d).statEnergyC (N d) Finset.univ η) := by
          gcongr; exact hdom d
      _ = 2 * C * r ^ (2 * t) * (P d).statEnergyC (N d) Finset.univ η := by ring
  -- pass to the limit `d → ∞`
  have hlim : ∀ t, |L t - θ| ≤ 2 * C * r ^ (2 * t) := fun t =>
    le_of_tendsto ((hL t).sub hθ).abs (Eventually.of_forall fun d => hbound t d)
  -- `r^{2t} → 0`
  have hgeo : Tendsto (fun t : ℕ => 2 * C * r ^ (2 * t)) atTop (𝓝 0) := by
    have : Tendsto (fun t : ℕ => (r ^ 2) ^ t) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg _) (by nlinarith)
    simpa [pow_mul] using this.const_mul (2 * C)
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun t => dist_nonneg) (fun t => ?_) hgeo
  rw [Real.dist_eq]; exact hlim t

/-- **Theorem 16, a correct asymptotic form (deterministic-equivalent level).**  The interchange of
limits is valid in the *extensive noise* regime: if, uniformly in `d`,
`λ_1 ≤ Λ` with `η Λ < 2`, `λ_d ≥ λ_min > 0`, `s_min(Σ) ≥ s > 0` and `‖x_0‖² ≤ M d`
(the last is "trajectory boundedness" at `t = 0`), then
`lim_t lim_d 𝔼[s_t^𝒟]/𝔼[s_t] = lim_d θ_∞(d)` whenever the inner limits exist.
Note that `s_min ≥ s > 0` forces `Tr Σ ≥ s d → ∞`, contradicting the literal "bounded trace" of
Assumption 1, and makes both unnormalised sums in Theorem 16's display diverge
(`Spec.card_mul_smin_le_statEnergyC`): the limit must be taken of the *ratio* `θ_∞(d)`. -/
theorem late_phase_interchange_of_extensive_noise {ι : ℕ → Type*} [∀ d, Fintype (ι d)]
    [∀ d, DecidableEq (ι d)] (P : ∀ d, Spec (ι d)) (N : ∀ d, Noise (ι d)) (c0 : ∀ d, ι d → ℝ)
    {η : ℝ} (hη : 0 < η) {Λ lmin smin M : ℝ} (hΛ : η * Λ < 2) (hlmin : 0 < lmin)
    (hsmin : 0 < smin) (hlam1 : ∀ d, (P d).lam1 ≤ Λ) (hlamd : ∀ d, lmin ≤ (P d).lamd)
    (hs : ∀ d, smin ≤ (N d).smin)
    (hM : ∀ d, Spec.normSq (c0 d) ≤ M * (Fintype.card (ι d) : ℝ))
    {L : ℕ → ℝ}
    (hL : ∀ t, Tendsto (fun d => (P d).thetaBarCSGD (N d) η (c0 d) t) atTop (𝓝 (L t)))
    {θ : ℝ} (hθ : Tendsto (fun d => (P d).thetaInf (N d) η) atTop (𝓝 θ)) :
    Tendsto L atTop (𝓝 θ) := by
  have hstab : ∀ d, η < 2 / (P d).lam1 := fun d => by
    rw [lt_div_iff₀ (P d).lam1_pos]
    have := mul_le_mul_of_nonneg_left (hlam1 d) hη.le
    linarith
  have hcard : ∀ d, (0 : ℝ) < (Fintype.card (ι d) : ℝ) := fun d => by
    have : Nonempty (ι d) := ⟨(P d).i1⟩
    exact_mod_cast Fintype.card_pos
  have hM0 : 0 ≤ M := by
    have h1 : 0 ≤ Spec.normSq (c0 0) := Finset.sum_nonneg fun i _ => sq_nonneg _
    have h2 := hM 0
    have h3 := hcard 0
    by_contra hneg
    push Not at hneg
    nlinarith
  have hΛ0 : 0 < Λ := lt_of_lt_of_le (P 0).lam1_pos (hlam1 0)
  have hpos : ∀ d, 0 < (P d).statEnergyC (N d) Finset.univ η := fun d =>
    (P d).statEnergyC_univ_pos (N d) hη (hstab d)
      ⟨(P d).i1, lt_of_lt_of_le hsmin ((hs d).trans ((N d).smin_le _))⟩
  refine late_phase_interchange P N c0 hη hstab
    (r := max (η * Λ - 1) (1 - η * lmin)) (max_lt (by linarith) (by nlinarith))
    (fun d => ?_) hpos (C := 1 + 2 * M * Λ ^ 2 / (η * lmin * smin)) (fun d => ?_) hL hθ
  · unfold Spec.contrC
    have h1 := mul_le_mul_of_nonneg_left (hlam1 d) hη.le
    have h2 := mul_le_mul_of_nonneg_left (hlamd d) hη.le
    exact max_le_max (by linarith) (by linarith)
  · have hE := (P d).initExcessC_univ_le (N d) hη (hstab d) (c0 d)
    have hlow := (P d).card_mul_smin_le_statEnergyC (N d) hη (hstab d)
    have hS := hpos d
    have hl1sq : (P d).lam1 ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ (P d).lam1_pos.le (hlam1 d) 2
    have hnorm0 : 0 ≤ Spec.normSq (c0 d) := Finset.sum_nonneg fun i _ => sq_nonneg _
    -- `Λ² M d ≤ K · (η λ_min / 2) d s ≤ K · statEnergy`
    have hX : η * lmin / 2 * ((Fintype.card (ι d) : ℝ) * smin) ≤
        (P d).statEnergyC (N d) Finset.univ η := by
      refine le_trans ?_ hlow
      have hc := (hcard d).le
      have h1 : η * lmin / 2 ≤ η * (P d).lamd / 2 := by
        have := mul_le_mul_of_nonneg_left (hlamd d) hη.le; linarith
      have h2 : (Fintype.card (ι d) : ℝ) * smin ≤ (Fintype.card (ι d) : ℝ) * (N d).smin :=
        mul_le_mul_of_nonneg_left (hs d) hc
      exact mul_le_mul h1 h2 (mul_nonneg hc hsmin.le)
        (by have := (P d).lamd_pos; positivity)
    have hK : 0 ≤ 2 * M * Λ ^ 2 / (η * lmin * smin) := by positivity
    have hkey : Λ ^ 2 * (M * (Fintype.card (ι d) : ℝ)) =
        2 * M * Λ ^ 2 / (η * lmin * smin) *
          (η * lmin / 2 * ((Fintype.card (ι d) : ℝ) * smin)) := by
      field_simp
    calc (P d).initExcessC (N d) Finset.univ η (c0 d)
        ≤ (P d).lam1 ^ 2 * Spec.normSq (c0 d) + (P d).statEnergyC (N d) Finset.univ η := hE
      _ ≤ Λ ^ 2 * (M * (Fintype.card (ι d) : ℝ)) + (P d).statEnergyC (N d) Finset.univ η := by
          have := mul_le_mul hl1sq (hM d) hnorm0 (sq_nonneg Λ)
          linarith
      _ ≤ 2 * M * Λ ^ 2 / (η * lmin * smin) * (P d).statEnergyC (N d) Finset.univ η +
            (P d).statEnergyC (N d) Finset.univ η := by
          rw [hkey]
          have := mul_le_mul_of_nonneg_left hX hK
          linarith
      _ = (1 + 2 * M * Λ ^ 2 / (η * lmin * smin)) * (P d).statEnergyC (N d) Finset.univ η := by
          ring

namespace Spec

variable (P : Spec ι) (N : Noise ι)

/-! ### (d) Interpretation paragraph: small step size and large spectral gap -/

/-- The weighted noise energy `A_S(η) = ∑_{i∈S} λ_i κ_i² / (2 - η λ_i)`; one has
`∑_S λ_i² β_i = η A_S(η)`, so `θ_∞ = A_𝒟 / (A_𝒟 + A_ℬ)`. -/
noncomputable def wEnergyC (S : Finset ι) (η : ℝ) : ℝ :=
  ∑ i ∈ S, P.lam i * N.kap2 i / (2 - η * P.lam i)

theorem statEnergyC_eq_eta_mul (S : Finset ι) (η : ℝ) :
    P.statEnergyC N S η = η * P.wEnergyC N S η := by
  unfold statEnergyC wEnergyC
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => P.lam_sq_mul_betaC N η i

/-- `θ_∞ = A_𝒟 / (A_𝒟 + A_ℬ)` with `A_S = ∑_S λ_i κ_i² / (2 - η λ_i)`: the factor `η` cancels. -/
theorem thetaInf_eq_wEnergyC {η : ℝ} (hη : η ≠ 0) :
    P.thetaInf N η = P.wEnergyC N P.D η / (P.wEnergyC N P.D η + P.wEnergyC N P.B η) := by
  rw [P.thetaInf_eq_statEnergyC, ← P.statEnergyC_D_add_B, P.statEnergyC_eq_eta_mul,
    P.statEnergyC_eq_eta_mul, ← mul_add, mul_div_mul_left _ _ hη]

/-- `x ↦ x / (2 - η x)` is increasing on `(-∞, 2/η)`. -/
private theorem div_two_sub_mono {η x y : ℝ} (hη : 0 ≤ η) (hxy : x ≤ y) (hy : η * y < 2) :
    x / (2 - η * x) ≤ y / (2 - η * y) := by
  have hx2 : η * x ≤ η * y := mul_le_mul_of_nonneg_left hxy hη
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem wEnergyC_nonneg {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) (S : Finset ι) :
    0 ≤ P.wEnergyC N S η :=
  Finset.sum_nonneg fun i _ =>
    div_nonneg (mul_nonneg (P.lam_pos i).le (kap2_nonneg N i))
      (by linarith [P.eta_lam_lt_two hη h i])

private theorem nLoss_nonneg (S : Finset ι) : 0 ≤ P.nLoss N S :=
  Finset.sum_nonneg fun i _ => mul_nonneg (P.lam_pos i).le (kap2_nonneg N i)

/-- `A_S (2 - η hi) ≤ n^loss_S` when `λ_i ≤ hi` on `S`. -/
theorem wEnergyC_mul_le {η : ℝ} (hη : 0 ≤ η) (S : Finset ι) {hi : ℝ}
    (hhi : ∀ i ∈ S, P.lam i ≤ hi) (h2 : η * hi < 2) :
    P.wEnergyC N S η * (2 - η * hi) ≤ P.nLoss N S := by
  unfold wEnergyC nLoss
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hiS => ?_
  have h1 := mul_le_mul_of_nonneg_left (hhi i hiS) hη
  have hnum := mul_nonneg (P.lam_pos i).le (kap2_nonneg N i)
  have hden : 0 < 2 - η * P.lam i := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  exact mul_le_mul_of_nonneg_left (by linarith) hnum

/-- `n^loss_S ≤ A_S (2 - η lo)` when `lo ≤ λ_i` and `η λ_i < 2` on `S`. -/
theorem le_wEnergyC_mul {η : ℝ} (hη : 0 ≤ η) (S : Finset ι) {lo : ℝ}
    (hlo : ∀ i ∈ S, lo ≤ P.lam i) (h2 : ∀ i ∈ S, η * P.lam i < 2) :
    P.nLoss N S ≤ P.wEnergyC N S η * (2 - η * lo) := by
  unfold wEnergyC nLoss
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hiS => ?_
  have h1 := mul_le_mul_of_nonneg_left (hlo i hiS) hη
  have hnum := mul_nonneg (P.lam_pos i).le (kap2_nonneg N i)
  have hden : 0 < 2 - η * P.lam i := by linarith [h2 i hiS]
  rw [div_mul_eq_mul_div, le_div_iff₀ hden]
  exact mul_le_mul_of_nonneg_left (by linarith) hnum

/-- `A_S ≤ (hi / (2 - η hi)) ∑_S κ_i²` when `λ_i ≤ hi` on `S`. -/
theorem wEnergyC_le_trace {η : ℝ} (hη : 0 ≤ η) (S : Finset ι) {hi : ℝ}
    (hhi : ∀ i ∈ S, P.lam i ≤ hi) (h2 : η * hi < 2) :
    P.wEnergyC N S η ≤ hi / (2 - η * hi) * ∑ i ∈ S, N.kap2 i := by
  unfold wEnergyC
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hiS => ?_
  rw [mul_div_right_comm]
  exact mul_le_mul_of_nonneg_right
    (div_two_sub_mono hη (hhi i hiS) h2) (kap2_nonneg N i)

/-- `(lo / (2 - η lo)) ∑_S κ_i² ≤ A_S` when `lo ≤ λ_i` and `η λ_i < 2` on `S`. -/
theorem trace_le_wEnergyC {η : ℝ} (hη : 0 ≤ η) (S : Finset ι) {lo : ℝ}
    (hlo : ∀ i ∈ S, lo ≤ P.lam i) (h2 : ∀ i ∈ S, η * P.lam i < 2) :
    lo / (2 - η * lo) * ∑ i ∈ S, N.kap2 i ≤ P.wEnergyC N S η := by
  unfold wEnergyC
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hiS => ?_
  rw [mul_div_right_comm]
  exact mul_le_mul_of_nonneg_right
    (div_two_sub_mono hη (hlo i hiS) (h2 i hiS)) (kap2_nonneg N i)

/-- The small-step-size limit of `θ_∞`:
`θ₀ = n^loss_𝒟 / (n^loss_𝒟 + n^loss_ℬ) = ∑_𝒟 λ_i κ_i² / ∑_i λ_i κ_i²`
(for isotropic noise, `∑_𝒟 λ_i / ∑_i λ_i`, see `thetaSmallStep_isotropic`). -/
noncomputable def thetaSmallStep : ℝ := P.nLossD N / (P.nLossD N + P.nLossB N)

private theorem nLossD_add_nLossB : P.nLossD N + P.nLossB N = ∑ i, P.lam i * N.kap2 i :=
  P.sum_D_add_sum_B _

private theorem nLoss_total_pos (hκ : ∃ i, 0 < N.kap2 i) : 0 < P.nLossD N + P.nLossB N := by
  rw [P.nLossD_add_nLossB]
  obtain ⟨i, hi⟩ := hκ
  exact Finset.sum_pos' (fun j _ => mul_nonneg (P.lam_pos j).le (kap2_nonneg N j))
    ⟨i, Finset.mem_univ i, mul_pos (P.lam_pos i) hi⟩

theorem thetaSmallStep_nonneg : 0 ≤ P.thetaSmallStep N :=
  div_nonneg (P.nLoss_nonneg N _) (add_nonneg (P.nLoss_nonneg N _) (P.nLoss_nonneg N _))

theorem thetaSmallStep_le_one : P.thetaSmallStep N ≤ 1 :=
  div_le_one_of_le₀ (le_add_of_nonneg_right (P.nLoss_nonneg N _))
    (add_nonneg (P.nLoss_nonneg N _) (P.nLoss_nonneg N _))

/-- The four basic two-sided bounds on the weighted energies, in product form. -/
theorem wEnergyC_bounds {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) :
    P.nLossD N ≤ P.wEnergyC N P.D η * (2 - η * P.lamk) ∧
    P.wEnergyC N P.D η * (2 - η * P.lam1) ≤ P.nLossD N ∧
    P.nLossB N ≤ P.wEnergyC N P.B η * (2 - η * P.lamd) ∧
    P.wEnergyC N P.B η * (2 - η * P.lamk1) ≤ P.nLossB N := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact P.le_wEnergyC_mul N hη.le P.D (fun i hi => P.lamk_le i hi)
      (fun i _ => P.eta_lam_lt_two hη h i)
  · exact P.wEnergyC_mul_le N hη.le P.D (fun i hi => P.le_lam1 i hi) (P.eta_lam1_lt_two h)
  · exact P.le_wEnergyC_mul N hη.le P.B (fun i hi => P.lamd_le_of_mem_B hi)
      (fun i _ => P.eta_lam_lt_two hη h i)
  · exact P.wEnergyC_mul_le N hη.le P.B (fun i hi => P.le_lamk1_of_mem_B hi)
      (P.eta_lam_lt_two hη h P.ik1)

/-- `A_𝒟 + A_ℬ > 0` for non-zero noise. -/
theorem wEnergyC_total_pos {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) (hκ : ∃ i, 0 < N.kap2 i) :
    0 < P.wEnergyC N P.D η + P.wEnergyC N P.B η := by
  have hpos := P.statEnergyC_univ_pos N hη h hκ
  rw [← P.statEnergyC_D_add_B, P.statEnergyC_eq_eta_mul, P.statEnergyC_eq_eta_mul, ← mul_add] at hpos
  exact (mul_pos_iff_of_pos_left hη).mp hpos

/-- `0 ≤ θ_∞ ≤ 1`. -/
theorem thetaInf_nonneg {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) : 0 ≤ P.thetaInf N η :=
  div_nonneg (P.statEnergyC_nonneg N hη h _) (P.statEnergyC_nonneg N hη h _)

theorem thetaInf_le_one {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) : P.thetaInf N η ≤ 1 := by
  rw [P.thetaInf_eq_statEnergyC]
  refine div_le_one_of_le₀ ?_ (P.statEnergyC_nonneg N hη h _)
  rw [← P.statEnergyC_D_add_B]
  exact le_add_of_nonneg_right (P.statEnergyC_nonneg N hη h _)

/-- **Interpretation of Theorem 16, small step size (lower bound).**  For every admissible step
size, `θ_∞(η) ≥ θ₀ = ∑_𝒟 λ_i κ_i² / ∑_i λ_i κ_i²`: a finite step size always *increases* the
late-time alignment relative to its `η → 0` limit. -/
theorem thetaSmallStep_le_thetaInf {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1)
    (hκ : ∃ i, 0 < N.kap2 i) : P.thetaSmallStep N ≤ P.thetaInf N η := by
  obtain ⟨haLo, -, -, hbHi⟩ := P.wEnergyC_bounds N hη h
  have ha := P.wEnergyC_nonneg N hη h P.D
  have hb := P.wEnergyC_nonneg N hη h P.B
  have hn := P.nLoss_total_pos N hκ
  have hab := P.wEnergyC_total_pos N hη h hκ
  have hnD := P.nLoss_nonneg N P.D
  have hnB := P.nLoss_nonneg N P.B
  have huk : 2 - η * P.lamk ≤ 2 - η * P.lamk1 := by
    have := mul_le_mul_of_nonneg_left P.lamk1_lt_lamk.le hη.le; linarith
  have huk1 : 0 < 2 - η * P.lamk1 := by linarith [P.eta_lamk1_lt_two hη h]
  rw [P.thetaInf_eq_wEnergyC N hη.ne', thetaSmallStep, div_le_div_iff₀ hn hab]
  -- `nD * b ≤ a * nB`
  have key : P.nLossD N * P.wEnergyC N P.B η ≤ P.wEnergyC N P.D η * P.nLossB N := by
    have h1 : P.nLossD N * P.wEnergyC N P.B η ≤
        P.wEnergyC N P.D η * (2 - η * P.lamk) * P.wEnergyC N P.B η :=
      mul_le_mul_of_nonneg_right haLo hb
    have h2 : P.wEnergyC N P.D η * (2 - η * P.lamk) * P.wEnergyC N P.B η ≤
        P.wEnergyC N P.D η * (2 - η * P.lamk1) * P.wEnergyC N P.B η :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left huk ha) hb
    have h3 : P.wEnergyC N P.D η * (P.wEnergyC N P.B η * (2 - η * P.lamk1)) ≤
        P.wEnergyC N P.D η * P.nLossB N := mul_le_mul_of_nonneg_left hbHi ha
    nlinarith
  unfold nLossD nLossB at *
  nlinarith

/-- **Interpretation of Theorem 16, small step size (quantitative upper bound).**
`θ_∞(η) - θ₀ ≤ θ₀ (1 - θ₀) · η (λ_1 - λ_d) / (2 - η λ_1)`.  So the paper's approximation
`θ_∞ ≈ θ₀` holds with relative precision governed by `η (λ_1 - λ_d)`: "`η ≪ 1`" must be read as
`η λ_1 ≪ 1`. -/
theorem thetaInf_sub_le {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) (hκ : ∃ i, 0 < N.kap2 i) :
    P.thetaInf N η - P.thetaSmallStep N ≤
      P.thetaSmallStep N * (1 - P.thetaSmallStep N) *
        (η * (P.lam1 - P.lamd) / (2 - η * P.lam1)) := by
  obtain ⟨-, haHi, hbLo, hbHi⟩ := P.wEnergyC_bounds N hη h
  have ha := P.wEnergyC_nonneg N hη h P.D
  have hb := P.wEnergyC_nonneg N hη h P.B
  have hn := P.nLoss_total_pos N hκ
  have hab := P.wEnergyC_total_pos N hη h hκ
  have hnD : 0 ≤ P.nLossD N := P.nLoss_nonneg N P.D
  have hnB : 0 ≤ P.nLossB N := P.nLoss_nonneg N P.B
  have hu1 : 0 < 2 - η * P.lam1 := by linarith [P.eta_lam1_lt_two h]
  have hu1k1 : 2 - η * P.lam1 ≤ 2 - η * P.lamk1 := by
    have := mul_le_mul_of_nonneg_left (P.le_lam1_all P.ik1) hη.le
    unfold lamk1; linarith
  have hgap : 0 ≤ η * (P.lam1 - P.lamd) := mul_nonneg hη.le (by linarith [P.lamd_lt_lam1])
  set a := P.wEnergyC N P.D η with ha_def
  set b := P.wEnergyC N P.B η with hb_def
  set nD := P.nLossD N with hnD_def
  set nB := P.nLossB N with hnB_def
  set u1 := 2 - η * P.lam1 with hu1_def
  have hud : 2 - η * P.lamd = u1 + η * (P.lam1 - P.lamd) := by rw [hu1_def]; ring
  rw [hud] at hbLo
  -- `b * u1 ≤ nB`
  have hbu1 : b * u1 ≤ nB := le_trans (mul_le_mul_of_nonneg_left hu1k1 hb) hbHi
  -- numerator bound: `a nB - nD b ≤ a b η(λ₁ - λ_d)`
  have hnum : a * nB - nD * b ≤ a * b * (η * (P.lam1 - P.lamd)) := by
    have h1 : a * nB ≤ a * (b * (u1 + η * (P.lam1 - P.lamd))) :=
      mul_le_mul_of_nonneg_left hbLo ha
    have h2 : a * u1 * b ≤ nD * b := mul_le_mul_of_nonneg_right haHi hb
    nlinarith
  -- harmonic-type bound: `a b u1 (nD + nB) ≤ nD nB (a + b)`
  have hharm : a * b * u1 * (nD + nB) ≤ nD * nB * (a + b) := by
    have h1 : a * u1 * (b * nB) ≤ nD * (b * nB) :=
      mul_le_mul_of_nonneg_right haHi (mul_nonneg hb hnB)
    have h2 : b * u1 * (a * nD) ≤ nB * (a * nD) :=
      mul_le_mul_of_nonneg_right hbu1 (mul_nonneg ha hnD)
    nlinarith
  have h1mθ : 1 - P.thetaSmallStep N = nB / (nD + nB) := by
    unfold thetaSmallStep
    rw [one_sub_div hn.ne']
    congr 1; ring
  rw [P.thetaInf_eq_wEnergyC N hη.ne', h1mθ]
  unfold thetaSmallStep
  rw [div_sub_div _ _ hab.ne' hn.ne']
  have hrhs : nD / (nD + nB) * (nB / (nD + nB)) * (η * (P.lam1 - P.lamd) / u1) =
      nD * nB * (η * (P.lam1 - P.lamd)) / ((nD + nB) * (nD + nB) * u1) := by
    field_simp
  rw [hrhs, div_le_div_iff₀ (mul_pos hab hn) (mul_pos (mul_pos hn hn) hu1)]
  have hstep1 : (a * (nD + nB) - (a + b) * nD) * ((nD + nB) * (nD + nB) * u1) ≤
      a * b * (η * (P.lam1 - P.lamd)) * ((nD + nB) * (nD + nB) * u1) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have : a * (nD + nB) - (a + b) * nD = a * nB - nD * b := by ring
    rw [this]; exact hnum
  have hstep2 : a * b * (η * (P.lam1 - P.lamd)) * ((nD + nB) * (nD + nB) * u1) ≤
      nD * nB * (η * (P.lam1 - P.lamd)) * ((a + b) * (nD + nB)) := by
    have := mul_le_mul_of_nonneg_left hharm (mul_nonneg hgap hn.le)
    nlinarith
  exact hstep1.trans hstep2

/-- Cruder form of `thetaInf_sub_le`: `0 ≤ θ_∞(η) - θ₀ ≤ η (λ_1 - λ_d) / (4 (2 - η λ_1))`. -/
theorem thetaInf_sub_le_quarter {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1)
    (hκ : ∃ i, 0 < N.kap2 i) :
    P.thetaInf N η - P.thetaSmallStep N ≤ η * (P.lam1 - P.lamd) / (4 * (2 - η * P.lam1)) := by
  refine (P.thetaInf_sub_le N hη h hκ).trans ?_
  have hu1 : 0 < 2 - η * P.lam1 := by linarith [P.eta_lam1_lt_two h]
  have hgap : 0 ≤ η * (P.lam1 - P.lamd) / (2 - η * P.lam1) :=
    div_nonneg (mul_nonneg hη.le (by linarith [P.lamd_lt_lam1])) hu1.le
  have hq : P.thetaSmallStep N * (1 - P.thetaSmallStep N) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (P.thetaSmallStep N - 1 / 2)]
  calc P.thetaSmallStep N * (1 - P.thetaSmallStep N) * (η * (P.lam1 - P.lamd) / (2 - η * P.lam1))
      ≤ 1 / 4 * (η * (P.lam1 - P.lamd) / (2 - η * P.lam1)) :=
        mul_le_mul_of_nonneg_right hq hgap
    _ = η * (P.lam1 - P.lamd) / (4 * (2 - η * P.lam1)) := by field_simp

/-- **Interpretation of Theorem 16 (tex 756–759), general noise.**
`lim_{η→0⁺} θ_∞(η) = ∑_𝒟 λ_i κ_i² / ∑_i λ_i κ_i²`. -/
theorem tendsto_thetaInf_zero (hκ : ∃ i, 0 < N.kap2 i) :
    Tendsto (fun η => P.thetaInf N η) (𝓝[>] 0) (𝓝 (P.thetaSmallStep N)) := by
  have hl1 := P.lam1_pos
  have hmem : Set.Ioo (0 : ℝ) (1 / P.lam1) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by positivity)
  have hupper : Tendsto (fun η : ℝ => P.thetaSmallStep N + η * (P.lam1 - P.lamd)) (𝓝[>] 0)
      (𝓝 (P.thetaSmallStep N)) := by
    have hc : Continuous fun η : ℝ => P.thetaSmallStep N + η * (P.lam1 - P.lamd) := by fun_prop
    exact (hc.tendsto' 0 _ (by simp)).mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [hmem] with η hη
    have hstab : η < 2 / P.lam1 := lt_trans hη.2 (by gcongr; norm_num)
    exact P.thetaSmallStep_le_thetaInf N hη.1 hstab hκ
  · filter_upwards [hmem] with η hη
    have hstab : η < 2 / P.lam1 := lt_trans hη.2 (by gcongr; norm_num)
    have h1 : η * P.lam1 < 1 := (lt_div_iff₀ hl1).mp hη.2
    have hb := P.thetaInf_sub_le_quarter N hη.1 hstab hκ
    have hgap : 0 ≤ η * (P.lam1 - P.lamd) := mul_nonneg hη.1.le (by linarith [P.lamd_lt_lam1])
    have : η * (P.lam1 - P.lamd) / (4 * (2 - η * P.lam1)) ≤ η * (P.lam1 - P.lamd) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith

/-- For isotropic noise `κ_i² = σ²` the small-step limit is `∑_𝒟 λ_i / ∑_i λ_i`. -/
theorem thetaSmallStep_isotropic {σ2 : ℝ} (hσ : σ2 ≠ 0) (hiso : ∀ i, N.kap2 i = σ2) :
    P.thetaSmallStep N = (∑ i ∈ P.D, P.lam i) / ∑ i, P.lam i := by
  unfold thetaSmallStep
  rw [P.nLossD_add_nLossB]
  unfold nLossD nLoss
  simp_rw [hiso, ← Finset.sum_mul]
  rw [mul_div_mul_right _ _ hσ]

/-- For isotropic noise, `θ_∞ = ∑_𝒟 λ_i/(2 - η λ_i) / ∑_i λ_i/(2 - η λ_i)` exactly. -/
theorem thetaInf_isotropic {σ2 : ℝ} (hσ : σ2 ≠ 0) (hiso : ∀ i, N.kap2 i = σ2) {η : ℝ}
    (hη : η ≠ 0) :
    P.thetaInf N η =
      (∑ i ∈ P.D, P.lam i / (2 - η * P.lam i)) / ∑ i, P.lam i / (2 - η * P.lam i) := by
  rw [P.thetaInf_eq_wEnergyC N hη]
  have hw : ∀ S : Finset ι, P.wEnergyC N S η = σ2 * ∑ i ∈ S, P.lam i / (2 - η * P.lam i) := by
    intro S
    unfold wEnergyC
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hiso]; ring
  rw [hw, hw, ← mul_add, mul_div_mul_left _ _ hσ, P.sum_D_add_sum_B]

/-- **Interpretation of Theorem 16 (tex 756–759), isotropic noise.**  If `κ_i² = σ² > 0` for all
`i`, then `lim_{η→0⁺} θ_∞(η) = ∑_𝒟 λ_i / ∑_i λ_i`. -/
theorem tendsto_thetaInf_isotropic {σ2 : ℝ} (hσ : 0 < σ2) (hiso : ∀ i, N.kap2 i = σ2) :
    Tendsto (fun η => P.thetaInf N η) (𝓝[>] 0) (𝓝 ((∑ i ∈ P.D, P.lam i) / ∑ i, P.lam i)) := by
  rw [← P.thetaSmallStep_isotropic N hσ.ne' hiso]
  exact P.tendsto_thetaInf_zero N ⟨P.i1, by rw [hiso]; exact hσ⟩

/-- Quantitative isotropic statement: for `0 < η < 2/λ_1`,
`0 ≤ θ_∞(η) - ∑_𝒟 λ_i/∑_i λ_i ≤ η (λ_1 - λ_d) / (4 (2 - η λ_1))`. -/
theorem thetaInf_isotropic_bounds {σ2 : ℝ} (hσ : 0 < σ2) (hiso : ∀ i, N.kap2 i = σ2) {η : ℝ}
    (hη : 0 < η) (h : η < 2 / P.lam1) :
    0 ≤ P.thetaInf N η - (∑ i ∈ P.D, P.lam i) / ∑ i, P.lam i ∧
      P.thetaInf N η - (∑ i ∈ P.D, P.lam i) / ∑ i, P.lam i ≤
        η * (P.lam1 - P.lamd) / (4 * (2 - η * P.lam1)) := by
  have hκ : ∃ i, 0 < N.kap2 i := ⟨P.i1, by rw [hiso]; exact hσ⟩
  rw [← P.thetaSmallStep_isotropic N hσ.ne' hiso]
  exact ⟨sub_nonneg.mpr (P.thetaSmallStep_le_thetaInf N hη h hκ),
    P.thetaInf_sub_le_quarter N hη h hκ⟩

/-! ### (d') Interpretation paragraph: large spectral gap -/

/-- `1 - θ_∞ = A_ℬ / (A_𝒟 + A_ℬ)`. -/
theorem one_sub_thetaInf {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) (hκ : ∃ i, 0 < N.kap2 i) :
    1 - P.thetaInf N η = P.wEnergyC N P.B η / (P.wEnergyC N P.D η + P.wEnergyC N P.B η) := by
  rw [P.thetaInf_eq_wEnergyC N hη.ne', one_sub_div (P.wEnergyC_total_pos N hη h hκ).ne']
  congr 1; ring

/-- **Interpretation of Theorem 16, large gap (tex 760): explicit bound.**  If the noise has a
non-zero component in the dominant block (`∑_𝒟 κ_i² > 0`), then for every `0 < η < 2/λ_1`
```
1 - θ_∞ ≤ (∑_ℬ κ_i² / ∑_𝒟 κ_i²) · (λ_{k+1}/λ_k) · (2 - η λ_k)/(2 - η λ_{k+1}).
```
-/
theorem one_sub_thetaInf_le {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1)
    (hD : 0 < ∑ i ∈ P.D, N.kap2 i) :
    1 - P.thetaInf N η ≤
      (∑ i ∈ P.B, N.kap2 i) / (∑ i ∈ P.D, N.kap2 i) * (P.lamk1 / P.lamk) *
        ((2 - η * P.lamk) / (2 - η * P.lamk1)) := by
  have hκ : ∃ i, 0 < N.kap2 i := by
    by_contra hne
    push Not at hne
    have : ∑ i ∈ P.D, N.kap2 i ≤ 0 := Finset.sum_nonpos fun i _ => hne i
    linarith
  have huk : 0 < 2 - η * P.lamk := by linarith [P.eta_lamk_lt_two hη h]
  have huk1 : 0 < 2 - η * P.lamk1 := by linarith [P.eta_lamk1_lt_two hη h]
  have hk := P.lamk_pos
  have hk1 := P.lamk1_pos
  have hB : 0 ≤ ∑ i ∈ P.B, N.kap2 i := Finset.sum_nonneg fun i _ => kap2_nonneg N i
  -- `A_ℬ ≤ λ_{k+1}/(2 - ηλ_{k+1}) · Tr_ℬ` and `A_𝒟 ≥ λ_k/(2 - ηλ_k) · Tr_𝒟`
  have hb := P.wEnergyC_le_trace N hη.le P.B (fun i hi => P.le_lamk1_of_mem_B hi)
    (P.eta_lamk1_lt_two hη h)
  have ha := P.trace_le_wEnergyC N hη.le P.D (fun i hi => P.lamk_le i hi)
    (fun i _ => P.eta_lam_lt_two hη h i)
  have hb0 := P.wEnergyC_nonneg N hη h P.B
  have ha_pos : 0 < P.lamk / (2 - η * P.lamk) * ∑ i ∈ P.D, N.kap2 i :=
    mul_pos (div_pos hk huk) hD
  have ha0 : 0 < P.wEnergyC N P.D η := lt_of_lt_of_le ha_pos ha
  rw [P.one_sub_thetaInf N hη h hκ]
  calc P.wEnergyC N P.B η / (P.wEnergyC N P.D η + P.wEnergyC N P.B η)
      ≤ P.wEnergyC N P.B η / P.wEnergyC N P.D η :=
        div_le_div_of_nonneg_left hb0 ha0 (le_add_of_nonneg_right hb0)
    _ ≤ (P.lamk1 / (2 - η * P.lamk1) * ∑ i ∈ P.B, N.kap2 i) /
          (P.lamk / (2 - η * P.lamk) * ∑ i ∈ P.D, N.kap2 i) :=
        div_le_div₀ (mul_nonneg (div_nonneg hk1.le huk1.le) hB) hb ha_pos ha
    _ = (∑ i ∈ P.B, N.kap2 i) / (∑ i ∈ P.D, N.kap2 i) * (P.lamk1 / P.lamk) *
          ((2 - η * P.lamk) / (2 - η * P.lamk1)) := by
        field_simp

/-- **Interpretation of Theorem 16, large gap**: `1 - θ_∞ ≤ (∑_ℬ κ_i² / ∑_𝒟 κ_i²) / m` with
`m = λ_k/λ_{k+1}`.  Hence `θ_∞ → 1` as `m → ∞` *provided the ratio of bulk to dominant noise
traces stays bounded*; no lower bound on the bulk spectrum is needed. -/
theorem one_sub_thetaInf_le_div_mRatio {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1)
    (hD : 0 < ∑ i ∈ P.D, N.kap2 i) :
    1 - P.thetaInf N η ≤ (∑ i ∈ P.B, N.kap2 i) / (∑ i ∈ P.D, N.kap2 i) / P.mRatio := by
  refine (P.one_sub_thetaInf_le N hη h hD).trans ?_
  have huk : 0 < 2 - η * P.lamk := by linarith [P.eta_lamk_lt_two hη h]
  have huk1 : 0 < 2 - η * P.lamk1 := by linarith [P.eta_lamk1_lt_two hη h]
  have hk := P.lamk_pos
  have hk1 := P.lamk1_pos
  have hB : 0 ≤ ∑ i ∈ P.B, N.kap2 i := Finset.sum_nonneg fun i _ => kap2_nonneg N i
  have hratio : (2 - η * P.lamk) / (2 - η * P.lamk1) ≤ 1 := by
    rw [div_le_one huk1]
    have := mul_le_mul_of_nonneg_left P.lamk1_lt_lamk.le hη.le
    linarith
  have hfront : 0 ≤ (∑ i ∈ P.B, N.kap2 i) / (∑ i ∈ P.D, N.kap2 i) * (P.lamk1 / P.lamk) :=
    mul_nonneg (div_nonneg hB hD.le) (div_nonneg hk1.le hk.le)
  calc (∑ i ∈ P.B, N.kap2 i) / (∑ i ∈ P.D, N.kap2 i) * (P.lamk1 / P.lamk) *
        ((2 - η * P.lamk) / (2 - η * P.lamk1))
      ≤ (∑ i ∈ P.B, N.kap2 i) / (∑ i ∈ P.D, N.kap2 i) * (P.lamk1 / P.lamk) * 1 :=
        mul_le_mul_of_nonneg_left hratio hfront
    _ = (∑ i ∈ P.B, N.kap2 i) / (∑ i ∈ P.D, N.kap2 i) / P.mRatio := by
        unfold mRatio; field_simp

/-- The noise-trace ratio is controlled by the condition number of `Σ` and the block proportion:
`∑_ℬ κ_i² / ∑_𝒟 κ_i² ≤ (s_max/s_min) (1/ρ)` when `s_min > 0`. -/
theorem noise_trace_ratio_le (hs : 0 < N.smin) :
    (∑ i ∈ P.B, N.kap2 i) / (∑ i ∈ P.D, N.kap2 i) ≤ N.smax / N.smin * (1 / P.rho) := by
  have hBle : ∑ i ∈ P.B, N.kap2 i ≤ P.dkR * N.smax := by
    have : ∑ i ∈ P.B, N.kap2 i ≤ ∑ _i ∈ P.B, N.smax := Finset.sum_le_sum fun i _ => N.le_smax i
    simpa [dkR, Finset.sum_const, nsmul_eq_mul] using this
  have hDge : P.kR * N.smin ≤ ∑ i ∈ P.D, N.kap2 i := by
    have : ∑ _i ∈ P.D, N.smin ≤ ∑ i ∈ P.D, N.kap2 i := Finset.sum_le_sum fun i _ => N.smin_le i
    simpa [kR, Finset.sum_const, nsmul_eq_mul] using this
  have hk := P.kR_pos
  have hdk := P.dkR_pos
  have hsmax : 0 ≤ N.smax := le_trans hs.le (le_trans (N.smin_le P.i1) (N.le_smax P.i1))
  calc (∑ i ∈ P.B, N.kap2 i) / (∑ i ∈ P.D, N.kap2 i)
      ≤ (P.dkR * N.smax) / (P.kR * N.smin) :=
        div_le_div₀ (mul_nonneg hdk.le hsmax) hBle (mul_pos hk hs) hDge
    _ = N.smax / N.smin * (1 / P.rho) := by
        unfold rho; field_simp

/-- **Interpretation of Theorem 16, large gap, in the paper's parameters.**  If `s_min > 0`,
`1 - θ_∞ ≤ (s_max/s_min) (1/ρ) (1/m)`.  (Compare `Spec.gGap`, where `1/m²` appears.) -/
theorem one_sub_thetaInf_le_cond {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) (hs : 0 < N.smin) :
    1 - P.thetaInf N η ≤ N.smax / N.smin * (1 / P.rho) * (1 / P.mRatio) := by
  have hD : 0 < ∑ i ∈ P.D, N.kap2 i :=
    Finset.sum_pos (fun i _ => lt_of_lt_of_le hs (N.smin_le i)) P.D_nonempty
  refine (P.one_sub_thetaInf_le_div_mRatio N hη h hD).trans ?_
  rw [div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_right (P.noise_trace_ratio_le N hs)
    (by have := P.one_lt_mRatio; positivity)

/-- The corresponding lower bound in "`g_gap` form":
`θ_∞ ≥ 1 / (1 + (s_max/s_min) (1/ρ) (λ_{k+1}/λ_k))`. -/
theorem thetaInf_ge_gap_form {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) (hs : 0 < N.smin) :
    1 / (1 + N.smax / N.smin * (1 / P.rho) * (P.lamk1 / P.lamk)) ≤ P.thetaInf N η := by
  have hD : 0 < ∑ i ∈ P.D, N.kap2 i :=
    Finset.sum_pos (fun i _ => lt_of_lt_of_le hs (N.smin_le i)) P.D_nonempty
  have hκ : ∃ i, 0 < N.kap2 i := ⟨P.i1, lt_of_lt_of_le hs (N.smin_le _)⟩
  have huk : 0 < 2 - η * P.lamk := by linarith [P.eta_lamk_lt_two hη h]
  have huk1 : 0 < 2 - η * P.lamk1 := by linarith [P.eta_lamk1_lt_two hη h]
  have hk := P.lamk_pos
  have hk1 := P.lamk1_pos
  have hB : 0 ≤ ∑ i ∈ P.B, N.kap2 i := Finset.sum_nonneg fun i _ => kap2_nonneg N i
  have hb := P.wEnergyC_le_trace N hη.le P.B (fun i hi => P.le_lamk1_of_mem_B hi)
    (P.eta_lamk1_lt_two hη h)
  have ha := P.trace_le_wEnergyC N hη.le P.D (fun i hi => P.lamk_le i hi)
    (fun i _ => P.eta_lam_lt_two hη h i)
  have hb0 := P.wEnergyC_nonneg N hη h P.B
  have ha_pos : 0 < P.lamk / (2 - η * P.lamk) * ∑ i ∈ P.D, N.kap2 i :=
    mul_pos (div_pos hk huk) hD
  have ha0 : 0 < P.wEnergyC N P.D η := lt_of_lt_of_le ha_pos ha
  have hsmax : 0 ≤ N.smax := le_trans hs.le (le_trans (N.smin_le P.i1) (N.le_smax P.i1))
  have hC : 0 ≤ N.smax / N.smin * (1 / P.rho) :=
    mul_nonneg (div_nonneg hsmax hs.le) (by have := P.rho_pos; positivity)
  -- `b / a ≤ C λ_{k+1}/λ_k`
  have hba : P.wEnergyC N P.B η / P.wEnergyC N P.D η ≤
      N.smax / N.smin * (1 / P.rho) * (P.lamk1 / P.lamk) := by
    have hratio : (2 - η * P.lamk) / (2 - η * P.lamk1) ≤ 1 := by
      rw [div_le_one huk1]
      have := mul_le_mul_of_nonneg_left P.lamk1_lt_lamk.le hη.le
      linarith
    calc P.wEnergyC N P.B η / P.wEnergyC N P.D η
        ≤ (P.lamk1 / (2 - η * P.lamk1) * ∑ i ∈ P.B, N.kap2 i) /
            (P.lamk / (2 - η * P.lamk) * ∑ i ∈ P.D, N.kap2 i) :=
          div_le_div₀ (mul_nonneg (div_nonneg hk1.le huk1.le) hB) hb ha_pos ha
      _ = (∑ i ∈ P.B, N.kap2 i) / (∑ i ∈ P.D, N.kap2 i) * (P.lamk1 / P.lamk) *
            ((2 - η * P.lamk) / (2 - η * P.lamk1)) := by field_simp
      _ ≤ (∑ i ∈ P.B, N.kap2 i) / (∑ i ∈ P.D, N.kap2 i) * (P.lamk1 / P.lamk) * 1 :=
          mul_le_mul_of_nonneg_left hratio
            (mul_nonneg (div_nonneg hB hD.le) (div_nonneg hk1.le hk.le))
      _ ≤ N.smax / N.smin * (1 / P.rho) * (P.lamk1 / P.lamk) := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_right (P.noise_trace_ratio_le N hs) (div_nonneg hk1.le hk.le)
  rw [P.thetaInf_eq_wEnergyC N hη.ne']
  have h1 : P.wEnergyC N P.D η / (P.wEnergyC N P.D η + P.wEnergyC N P.B η) =
      1 / (1 + P.wEnergyC N P.B η / P.wEnergyC N P.D η) := by
    field_simp
  rw [h1]
  exact div_le_div_of_nonneg_left zero_le_one
    (by have := div_nonneg hb0 ha0.le; linarith) (by linarith)

/-- Necessity of dominant noise: if the noise vanishes on the dominant block then `θ_∞ = 0`,
whatever the spectral gap.  So the claim "`θ_∞ → 1` as `λ_k/λ_{k+1} → ∞`" is false without a
condition on the noise (it is stated in the paper right after the isotropic case). -/
theorem thetaInf_eq_zero_of_noise_bulk_only (η : ℝ) (hD : ∀ i ∈ P.D, N.kap2 i = 0) :
    P.thetaInf N η = 0 := by
  unfold thetaInf
  rw [Finset.sum_eq_zero fun i hi => by
    rw [P.betaC_eq_zero_of_kap2_eq_zero N (hD i hi), mul_zero], zero_div]

/-- **Interaction of the gap limit with the step-size constraint.**  `η < 2/λ_1` and
`λ_1 ≥ λ_k = m λ_{k+1}` force `η m λ_{k+1} < 2`: if the bulk edge `λ_{k+1}` stays bounded away
from zero and `m → ∞`, then necessarily `η → 0` (at rate `O(1/m)`). -/
theorem eta_mul_mRatio_mul_lamk1_lt_two {η : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) :
    η * (P.mRatio * P.lamk1) < 2 := by
  have : P.mRatio * P.lamk1 = P.lamk := by
    unfold mRatio; exact div_mul_cancel₀ _ P.lamk1_pos.ne'
  rw [this]
  exact P.eta_lamk_lt_two hη h

theorem eta_lt_of_bulk_bounded_below {η c : ℝ} (hη : 0 < η) (h : η < 2 / P.lam1) (hc : 0 < c)
    (hbulk : c ≤ P.lamk1) : η < 2 / (P.mRatio * c) := by
  have hm : 0 < P.mRatio := lt_trans zero_lt_one P.one_lt_mRatio
  rw [lt_div_iff₀ (mul_pos hm hc)]
  have h1 := P.eta_mul_mRatio_mul_lamk1_lt_two hη h
  have h2 : η * (P.mRatio * c) ≤ η * (P.mRatio * P.lamk1) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbulk hm.le) hη.le
  linarith

end Spec

universe u in
/-- **Interpretation of Theorem 16 (tex 760), uniform form.**  For every bound `K` on the noise
trace ratio `∑_ℬ κ² / ∑_𝒟 κ²` and every `ε > 0` there is a gap threshold `M` such that *every*
problem (any dimension, any spectrum, any admissible step size `0 < η < 2/λ_1`) with
`λ_k/λ_{k+1} ≥ M` has `1 - ε ≤ θ_∞ ≤ 1`. -/
theorem thetaInf_tendsto_one_uniform (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] (P : Spec ι) (N : Noise ι) (η : ℝ),
      0 < η → η < 2 / P.lam1 → 0 < ∑ i ∈ P.D, N.kap2 i →
      ∑ i ∈ P.B, N.kap2 i ≤ K * ∑ i ∈ P.D, N.kap2 i → M ≤ P.mRatio →
      1 - ε ≤ P.thetaInf N η ∧ P.thetaInf N η ≤ 1 := by
  refine ⟨K / ε, ?_⟩
  intro ι _ _ P N η hη h hD hK hM
  refine ⟨?_, P.thetaInf_le_one N hη h⟩
  have hm : 0 < P.mRatio := lt_trans zero_lt_one P.one_lt_mRatio
  have h1 := P.one_sub_thetaInf_le_div_mRatio N hη h hD
  have h2 : (∑ i ∈ P.B, N.kap2 i) / (∑ i ∈ P.D, N.kap2 i) ≤ K := by
    rw [div_le_iff₀ hD]; exact hK
  have h3 : (∑ i ∈ P.B, N.kap2 i) / (∑ i ∈ P.D, N.kap2 i) / P.mRatio ≤ ε := by
    rw [div_le_iff₀ hm]
    have : K ≤ ε * P.mRatio := by
      have := (div_le_iff₀ hε).mp hM
      linarith
    linarith
  linarith

/-- **Interpretation of Theorem 16 (tex 760), sequential form.**  Along any sequence of problems
(arbitrary dimensions and admissible step sizes) whose gap ratio `m_n = λ_k/λ_{k+1} → ∞` while
the noise trace ratio `∑_ℬ κ² / ∑_𝒟 κ²` stays bounded, `θ_∞ → 1`. -/
theorem tendsto_thetaInf_one_of_gap {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    [∀ n, DecidableEq (ι n)] (P : ∀ n, Spec (ι n)) (N : ∀ n, Noise (ι n)) (η : ℕ → ℝ)
    (hη : ∀ n, 0 < η n) (hstab : ∀ n, η n < 2 / (P n).lam1)
    (hD : ∀ n, 0 < ∑ i ∈ (P n).D, (N n).kap2 i) (K : ℝ)
    (hK : ∀ n, ∑ i ∈ (P n).B, (N n).kap2 i ≤ K * ∑ i ∈ (P n).D, (N n).kap2 i)
    (hm : Tendsto (fun n => (P n).mRatio) atTop atTop) :
    Tendsto (fun n => (P n).thetaInf (N n) (η n)) atTop (𝓝 1) := by
  have hlow : Tendsto (fun n => 1 - K / (P n).mRatio) atTop (𝓝 1) := by
    have : Tendsto (fun n => K / (P n).mRatio) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hm
    simpa using tendsto_const_nhds.sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun n => ?_)
    (fun n => (P n).thetaInf_le_one (N n) (hη n) (hstab n))
  have hmpos : 0 < (P n).mRatio := lt_trans zero_lt_one (P n).one_lt_mRatio
  have h1 := (P n).one_sub_thetaInf_le_div_mRatio (N n) (hη n) (hstab n) (hD n)
  have h2 : (∑ i ∈ (P n).B, (N n).kap2 i) / (∑ i ∈ (P n).D, (N n).kap2 i) ≤ K := by
    rw [div_le_iff₀ (hD n)]; exact hK n
  have h3 : (∑ i ∈ (P n).B, (N n).kap2 i) / (∑ i ∈ (P n).D, (N n).kap2 i) / (P n).mRatio ≤
      K / (P n).mRatio := div_le_div_of_nonneg_right h2 hmpos.le
  show 1 - K / (P n).mRatio ≤ (P n).thetaInf (N n) (η n)
  linarith

/-- In the regime of the paper's sentence ("gap `→ ∞` while the bulk spectrum remains bounded away
from zero") the stability constraint `η < 2/λ_1` forces the step sizes to vanish. -/
theorem csgd_tendsto_eta_zero_of_gap {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    [∀ n, DecidableEq (ι n)] (P : ∀ n, Spec (ι n)) (η : ℕ → ℝ)
    (hη : ∀ n, 0 < η n) (hstab : ∀ n, η n < 2 / (P n).lam1) {c : ℝ} (hc : 0 < c)
    (hbulk : ∀ n, c ≤ (P n).lamk1)
    (hm : Tendsto (fun n => (P n).mRatio) atTop atTop) :
    Tendsto η atTop (𝓝 0) := by
  have hup : Tendsto (fun n => 2 / ((P n).mRatio * c)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hm.atTop_mul_const hc)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => (hη n).le)
    (fun n => ((P n).eta_lt_of_bulk_bounded_below (hη n) (hstab n) hc (hbulk n)).le)

namespace Spec

variable (P : Spec ι) (N : Noise ι)

/-! ### (e) Assumption 14 (constant step size and initialization) -/

/-- The gap bound `2 (λ_k - λ_{k+1}) / (λ_1² - λ_d²)` on the step size in Assumption 14. -/
noncomputable def etaGapC : ℝ := 2 * (P.lamk - P.lamk1) / (P.lam1 ^ 2 - P.lamd ^ 2)

/-- `λ_1² - λ_d² > 0`: the gap bound of Assumption 14 never divides by zero. -/
theorem etaGapC_den_pos : 0 < P.lam1 ^ 2 - P.lamd ^ 2 := by
  nlinarith [P.lamd_pos, P.lamd_lt_lam1]

theorem etaGapC_pos : 0 < P.etaGapC :=
  div_pos (by linarith [P.lamk1_lt_lamk]) P.etaGapC_den_pos

/-- `(λ_k - λ_{k+1}) (λ_1 + λ_{k+1}) ≤ λ_1² - λ_d²`. -/
theorem gap_mul_lam1_add_lamk1_le :
    (P.lamk - P.lamk1) * (P.lam1 + P.lamk1) ≤ P.lam1 ^ 2 - P.lamd ^ 2 := by
  have h1 := P.lamk_le_lam1
  have h2 := P.lamd_le_lamk1
  have h3 := P.lamd_pos
  have h4 := P.lamk1_pos
  have h5 := P.lam1_pos
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (add_pos h5 h4).le,
    mul_nonneg (sub_nonneg.mpr h2) (add_pos h4 h3).le]

/-- **The `min` in Assumption 14 is redundant**: the gap bound is always strictly smaller than
the stability bound, `2 (λ_k - λ_{k+1}) / (λ_1² - λ_d²) < 2 / λ_1`. -/
theorem etaGapC_lt_two_div_lam1 : P.etaGapC < 2 / P.lam1 := by
  unfold etaGapC
  rw [div_lt_div_iff₀ P.etaGapC_den_pos P.lam1_pos]
  have h := P.gap_mul_lam1_add_lamk1_le
  have h1 := P.lamk1_pos
  have h2 := P.lamk1_lt_lamk
  nlinarith [mul_pos (sub_pos.mpr h2) h1]

theorem min_two_div_lam1_etaGapC : min (2 / P.lam1) P.etaGapC = P.etaGapC :=
  min_eq_right P.etaGapC_lt_two_div_lam1.le

/-- The gap bound is at most `2 / (λ_1 + λ_{k+1})`. -/
theorem etaGapC_le_two_div_add : P.etaGapC ≤ 2 / (P.lam1 + P.lamk1) := by
  unfold etaGapC
  rw [div_le_div_iff₀ P.etaGapC_den_pos (add_pos P.lam1_pos P.lamk1_pos)]
  have h := P.gap_mul_lam1_add_lamk1_le
  nlinarith

/-- **Assumption 14, "Constant Step Size" row** (tex 679):
`0 < η < min {2/λ_1, 2(λ_k - λ_{k+1})/(λ_1² - λ_d²)}`. -/
structure CSGDStep (η : ℝ) : Prop where
  /-- `0 < η` -/
  pos : 0 < η
  /-- `η < min {2/λ_1, 2(λ_k - λ_{k+1})/(λ_1² - λ_d²)}` -/
  lt_min : η < min (2 / P.lam1) (2 * (P.lamk - P.lamk1) / (P.lam1 ^ 2 - P.lamd ^ 2))

/-- **Assumption 14** (tex 668–687): the constant step size condition together with the
initialization conditions `∀ i ∈ 𝒟, c_{i,0}² > β_i` and `ϱ_𝒟 > δ - ∑_{i∈𝒟} β_i`. -/
structure CSGDAssumption (η : ℝ) (c0 : ι → ℝ) : Prop where
  /-- the step-size row -/
  step : P.CSGDStep η
  /-- `∀ i ∈ 𝒟, c_{i,0}² > β_i` -/
  init_gt : ∀ i ∈ P.D, P.betaC N η i < c0 i ^ 2
  /-- `ϱ_𝒟 > δ - ∑_{i∈𝒟} β_i` -/
  varrho_gt : P.deltaC N η - ∑ i ∈ P.D, P.betaC N η i < P.varrhoD N η c0

/-- Assumption 14's step-size row is equivalent to `0 < η < 2(λ_k - λ_{k+1})/(λ_1² - λ_d²)`. -/
theorem cSGDStep_iff {η : ℝ} : P.CSGDStep η ↔ 0 < η ∧ η < P.etaGapC := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, lt_of_lt_of_le h2 (min_le_right _ _)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have := P.min_two_div_lam1_etaGapC
    unfold etaGapC at this h2
    rw [this]; exact h2

namespace CSGDStep

variable {P} {η : ℝ}

theorem lt_stab (h : P.CSGDStep η) : η < 2 / P.lam1 := lt_of_lt_of_le h.lt_min (min_le_left _ _)

theorem lt_etaGapC (h : P.CSGDStep η) : η < P.etaGapC := lt_of_lt_of_le h.lt_min (min_le_right _ _)

/-- `η (λ_1² - λ_d²) < 2 (λ_k - λ_{k+1})`. -/
theorem mul_lt (h : P.CSGDStep η) : η * (P.lam1 ^ 2 - P.lamd ^ 2) < 2 * (P.lamk - P.lamk1) :=
  (lt_div_iff₀ P.etaGapC_den_pos).mp h.lt_etaGapC

theorem eta_lam_lt_two (h : P.CSGDStep η) (i : ι) : η * P.lam i < 2 :=
  P.eta_lam_lt_two h.pos h.lt_stab i

/-- **Assumption 14 ⟹ `1 - η λ_1 ∈ (-1, 1)`.** -/
theorem one_sub_eta_lam1_mem (h : P.CSGDStep η) :
    -1 < 1 - η * P.lam1 ∧ 1 - η * P.lam1 < 1 :=
  ⟨by linarith [P.eta_lam1_lt_two h.lt_stab], by linarith [mul_pos h.pos P.lam1_pos]⟩

/-- **Assumption 14 ⟹ `η (λ_1 + λ_{k+1}) < 2`** (strictly stronger than `η λ_1 < 2`). -/
theorem eta_mul_add_lt_two (h : P.CSGDStep η) : η * (P.lam1 + P.lamk1) < 2 := by
  have h1 := h.lt_etaGapC
  have h2 := P.etaGapC_le_two_div_add
  exact (lt_div_iff₀ (add_pos P.lam1_pos P.lamk1_pos)).mp (lt_of_lt_of_le h1 h2)

/-- Under Assumption 14 every bulk mode is non-oscillating: `0 < 1 - η λ_j` for `j ∈ ℬ`. -/
theorem one_sub_eta_lam_bulk_pos (h : P.CSGDStep η) {j : ι} (hj : j ∉ P.D) :
    0 < 1 - η * P.lam j := by
  have h1 := h.eta_mul_add_lt_two
  have h2 := mul_le_mul_of_nonneg_left (P.le_lamk1 j hj) h.pos.le
  have h3 := mul_lt_mul_of_pos_left
    (lt_of_lt_of_le P.lamk1_lt_lamk P.lamk_le_lam1) h.pos
  have h4 : η * P.lam j ≤ η * P.lamk1 := h2
  nlinarith

/-- **Under Assumption 14 every dominant mode contracts strictly faster than every bulk mode**:
`|1 - η λ_i| < 1 - η λ_j` for `i ∈ 𝒟`, `j ∈ ℬ`.  (This is why the transient part of the alignment
decays to `0`, and it is the mechanism behind `late_phase_interchange_fails`.) -/
theorem abs_dom_lt_bulk (h : P.CSGDStep η) {i j : ι} (hi : i ∈ P.D) (hj : j ∉ P.D) :
    |1 - η * P.lam i| < 1 - η * P.lam j := by
  have h1 := h.eta_mul_add_lt_two
  have hi1 := mul_le_mul_of_nonneg_left (P.le_lam1 i hi) h.pos.le
  have hj1 : η * P.lam j ≤ η * P.lamk1 := mul_le_mul_of_nonneg_left (P.le_lamk1 j hj) h.pos.le
  have hij : η * P.lam j < η * P.lam i :=
    mul_lt_mul_of_pos_left
      (lt_of_le_of_lt (P.le_lamk1 j hj) (lt_of_lt_of_le P.lamk1_lt_lamk (P.lamk_le i hi))) h.pos
  have hi1' : η * P.lam i ≤ η * P.lam1 := hi1
  rw [abs_lt]
  constructor <;> nlinarith

/-- In particular `|1 - η λ_1| < 1 - η λ_d`: the slowest mode is always the smallest bulk
eigenvalue, and `Spec.contrC η = 1 - η λ_d`. -/
theorem contrC_eq (h : P.CSGDStep η) : P.contrC η = 1 - η * P.lamd := by
  have := abs_lt.mp (h.abs_dom_lt_bulk P.i1_mem P.id_not_mem)
  unfold contrC
  exact max_eq_right (by unfold lam1 lamd; linarith [this.1])

/-- The bracket in the denominator of `δ` is positive under Assumption 14. -/
theorem gapDen_pos (h : P.CSGDStep η) :
    0 < 2 * (P.lamk - P.lamk1) / η - (P.lam1 ^ 2 - P.lamd ^ 2) := by
  rw [sub_pos, lt_div_iff₀ h.pos]
  linarith [h.mul_lt]

/-- `δ` without the nested fraction:
`δ = s_max ψ_𝒟 λ_1² η / (λ_d² λ_k² (2(λ_k - λ_{k+1}) - η(λ_1² - λ_d²)))`. -/
theorem deltaC_eq (N : Noise ι) (h : P.CSGDStep η) :
    P.deltaC N η = N.smax * P.psiD * P.lam1 ^ 2 * η /
      (P.lamd ^ 2 * P.lamk ^ 2 * (2 * (P.lamk - P.lamk1) - η * (P.lam1 ^ 2 - P.lamd ^ 2))) := by
  have hη := h.pos.ne'
  have hW : 2 * (P.lamk - P.lamk1) - η * (P.lam1 ^ 2 - P.lamd ^ 2) ≠ 0 := by
    linarith [h.mul_lt]
  have hd := P.lamd_pos.ne'
  have hk := P.lamk_pos.ne'
  unfold deltaC
  have : 2 * (P.lamk - P.lamk1) / η - (P.lam1 ^ 2 - P.lamd ^ 2) =
      (2 * (P.lamk - P.lamk1) - η * (P.lam1 ^ 2 - P.lamd ^ 2)) / η := by
    field_simp
  rw [this]
  field_simp

theorem deltaC_den_pos (h : P.CSGDStep η) :
    0 < P.lamd ^ 2 * P.lamk ^ 2 * (2 * (P.lamk - P.lamk1) / η - (P.lam1 ^ 2 - P.lamd ^ 2)) :=
  mul_pos (mul_pos (pow_pos P.lamd_pos 2) (pow_pos P.lamk_pos 2)) h.gapDen_pos

theorem smax_nonneg' (N : Noise ι) (P : Spec ι) : 0 ≤ N.smax :=
  le_trans (kap2_nonneg N P.i1) (N.le_smax P.i1)

/-- `δ ≥ 0` under Assumption 14's step-size condition. -/
theorem deltaC_nonneg (N : Noise ι) (h : P.CSGDStep η) : 0 ≤ P.deltaC N η :=
  div_nonneg (mul_nonneg (mul_nonneg (smax_nonneg' N P) P.psiD_pos.le) (sq_nonneg _))
    h.deltaC_den_pos.le

/-- **`δ > 0` under Assumption 14** iff the noise is non-zero (`s_max > 0`). -/
theorem deltaC_pos_iff (N : Noise ι) (h : P.CSGDStep η) : 0 < P.deltaC N η ↔ 0 < N.smax := by
  unfold deltaC
  rw [div_pos_iff_of_pos_right h.deltaC_den_pos]
  constructor
  · intro hpos
    by_contra hneg
    have h0 : N.smax = 0 := le_antisymm (not_lt.mp hneg) (smax_nonneg' N P)
    rw [h0] at hpos; simp at hpos
  · intro hs
    exact mul_pos (mul_pos hs P.psiD_pos) (pow_pos P.lam1_pos 2)

theorem deltaC_pos (N : Noise ι) (h : P.CSGDStep η) (hs : 0 < N.smax) : 0 < P.deltaC N η :=
  (h.deltaC_pos_iff N).mpr hs

/-- Under Assumption 14, `λ_d ≤ λ_i (2 - η λ_i)` for every direction `i`. -/
theorem lamd_le_lam_mul (h : P.CSGDStep η) (i : ι) : P.lamd ≤ P.lam i * (2 - η * P.lam i) := by
  have hη := h.pos
  have hl := P.lam_pos i
  have hd := P.lamd_pos
  have hdi := P.lamd_le_all i
  have hi1 := mul_le_mul_of_nonneg_left (P.le_lam1_all i) hη.le
  have hsum : η * (P.lam1 + P.lamd) < 2 := by
    have := h.eta_mul_add_lt_two
    have := mul_le_mul_of_nonneg_left P.lamd_le_lamk1 hη.le
    nlinarith
  rcases le_or_gt (η * P.lam i) 1 with hc | hc
  · nlinarith [mul_nonneg hl.le (sub_nonneg.mpr hc)]
  · have h1 : 0 < 2 - η * P.lam i - η * P.lamd := by nlinarith
    nlinarith [mul_pos hl h1, mul_pos hd (sub_pos.mpr hc)]

/-- Under Assumption 14, `β_i ≤ η s_max / λ_d` for every direction. -/
theorem betaC_le (N : Noise ι) (h : P.CSGDStep η) (i : ι) :
    P.betaC N η i ≤ η * N.smax / P.lamd := by
  unfold betaC
  rw [P.betaC_den_eq]
  exact div_le_div₀ (mul_nonneg h.pos.le (smax_nonneg' N P))
    (mul_le_mul_of_nonneg_left (N.le_smax i) h.pos.le) P.lamd_pos (h.lamd_le_lam_mul i)

/-- **The paper's bound `β_i ≤ η s_max / (2 λ_d - η λ_d²)` (tex 2176).**  It holds under
Assumption 14, where `η (λ_1 + λ_d) < 2` makes `λ_d (2 - η λ_d)` the minimum of `λ_i (2 - η λ_i)`;
the paper's justification "`η < 2/λ_1 ≤ 2/λ_d`" alone is not sufficient (`x ↦ x (2 - η x)` is not
monotone). -/
theorem betaC_le_paper (N : Noise ι) (h : P.CSGDStep η) (i : ι) :
    P.betaC N η i ≤ η * N.smax / (2 * P.lamd - η * P.lamd ^ 2) := by
  have hη := h.pos
  have hdi := P.lamd_le_all i
  have hi1 := mul_le_mul_of_nonneg_left (P.le_lam1_all i) hη.le
  have hsum : η * (P.lam1 + P.lamd) < 2 := by
    have := h.eta_mul_add_lt_two
    have := mul_le_mul_of_nonneg_left P.lamd_le_lamk1 hη.le
    nlinarith
  have hden : 0 < 2 * P.lamd - η * P.lamd ^ 2 := P.betaC_den_pos hη h.lt_stab P.id
  -- `λ_i (2 - η λ_i) - λ_d (2 - η λ_d) = (λ_i - λ_d) (2 - η (λ_i + λ_d)) ≥ 0`
  have h2 : 0 ≤ 2 - η * (P.lam i + P.lamd) := by nlinarith
  have hmono : 2 * P.lamd - η * P.lamd ^ 2 ≤ 2 * P.lam i - η * P.lam i ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdi) h2]
  unfold betaC
  exact div_le_div₀ (mul_nonneg hη.le (smax_nonneg' N P))
    (mul_le_mul_of_nonneg_left (N.le_smax i) hη.le) hden hmono

/-- `k λ_k² ≤ ψ_𝒟`. -/
theorem kR_mul_lamk_sq_le_psiD (P : Spec ι) : P.kR * P.lamk ^ 2 ≤ P.psiD := by
  have : ∑ _i ∈ P.D, P.lamk ^ 2 ≤ ∑ i ∈ P.D, P.lam i ^ 2 :=
    Finset.sum_le_sum fun i hi => pow_le_pow_left₀ P.lamk_pos.le (P.lamk_le i hi) 2
  simpa [kR, psiD, Finset.sum_const, nsmul_eq_mul] using this

/-- **`δ ≥ 2 ∑_{i∈𝒟} β_i` under Assumption 14's step-size condition.**  Consequently the
denominator `δ - ∑_𝒟 β_i` inside the logarithm of `t*` is positive (when `s_max > 0`). -/
theorem two_mul_sum_betaC_le_deltaC (N : Noise ι) (h : P.CSGDStep η) :
    2 * ∑ i ∈ P.D, P.betaC N η i ≤ P.deltaC N η := by
  have hη := h.pos
  have hd := P.lamd_pos
  have hk := P.lamk_pos
  have h1 := P.lam1_pos
  have hs := smax_nonneg' N P
  have hW : 0 < 2 * (P.lamk - P.lamk1) - η * (P.lam1 ^ 2 - P.lamd ^ 2) := by
    linarith [h.mul_lt]
  have hQ := P.etaGapC_den_pos
  -- `∑_𝒟 β_i ≤ k η s_max / λ_d`
  have hsum : ∑ i ∈ P.D, P.betaC N η i ≤ P.kR * (η * N.smax / P.lamd) := by
    have : ∑ i ∈ P.D, P.betaC N η i ≤ ∑ _i ∈ P.D, η * N.smax / P.lamd :=
      Finset.sum_le_sum fun i _ => h.betaC_le N i
    simpa [kR, Finset.sum_const, nsmul_eq_mul] using this
  -- `2 k η s_max / λ_d ≤ δ`
  have hδ : 2 * (P.kR * (η * N.smax / P.lamd)) ≤ P.deltaC N η := by
    rw [h.deltaC_eq N, le_div_iff₀ (mul_pos (mul_pos (pow_pos hd 2) (pow_pos hk 2)) hW)]
    have hW2 : 2 * (P.lamk - P.lamk1) - η * (P.lam1 ^ 2 - P.lamd ^ 2) ≤
        2 * (P.lamk - P.lamk1) := by nlinarith [mul_pos hη hQ]
    have hg : 4 * (P.lamd * (P.lamk - P.lamk1)) ≤ P.lam1 ^ 2 := by
      have hg1 : P.lamk - P.lamk1 ≤ P.lam1 - P.lamd := by
        linarith [P.lamk_le_lam1, P.lamd_le_lamk1]
      nlinarith [sq_nonneg (P.lam1 - 2 * P.lamd), mul_le_mul_of_nonneg_left hg1 hd.le]
    have hψ := kR_mul_lamk_sq_le_psiD P
    have hkR := P.kR_pos
    have e1 : 2 * (P.kR * (η * N.smax / P.lamd)) *
        (P.lamd ^ 2 * P.lamk ^ 2 * (2 * (P.lamk - P.lamk1) - η * (P.lam1 ^ 2 - P.lamd ^ 2))) =
        η * N.smax * (P.kR * P.lamk ^ 2) *
          (2 * P.lamd * (2 * (P.lamk - P.lamk1) - η * (P.lam1 ^ 2 - P.lamd ^ 2))) := by
      field_simp
    rw [e1]
    have e2 : 2 * P.lamd * (2 * (P.lamk - P.lamk1) - η * (P.lam1 ^ 2 - P.lamd ^ 2)) ≤
        P.lam1 ^ 2 := by
      have := mul_le_mul_of_nonneg_left hW2 (by positivity : (0:ℝ) ≤ 2 * P.lamd)
      nlinarith
    calc η * N.smax * (P.kR * P.lamk ^ 2) *
          (2 * P.lamd * (2 * (P.lamk - P.lamk1) - η * (P.lam1 ^ 2 - P.lamd ^ 2)))
        ≤ η * N.smax * P.psiD * P.lam1 ^ 2 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hψ (mul_nonneg hη.le hs)) e2
            (by positivity) (mul_nonneg (mul_nonneg hη.le hs) P.psiD_pos.le)
      _ = N.smax * P.psiD * P.lam1 ^ 2 * η := by ring
  linarith

/-- `∑_{i∈𝒟} β_i < δ` under Assumption 14 with non-zero noise. -/
theorem sum_betaC_lt_deltaC (N : Noise ι) (h : P.CSGDStep η) (hs : 0 < N.smax) :
    ∑ i ∈ P.D, P.betaC N η i < P.deltaC N η := by
  have h1 := h.two_mul_sum_betaC_le_deltaC N
  have h2 := h.deltaC_pos N hs
  have h3 : 0 ≤ ∑ i ∈ P.D, P.betaC N η i :=
    Finset.sum_nonneg fun i _ => P.betaC_nonneg N h.pos h.lt_stab i
  linarith

end CSGDStep

namespace CSGDAssumption

variable {P N} {η : ℝ} {c0 : ι → ℝ}

/-- `ϱ_𝒟 = ∑_𝒟 c_{i,0}² - ∑_𝒟 β_i`. -/
theorem varrhoD_eq (P : Spec ι) (N : Noise ι) (η : ℝ) (c0 : ι → ℝ) :
    P.varrhoD N η c0 = P.normSqD c0 - ∑ i ∈ P.D, P.betaC N η i := by
  unfold varrhoD normSqD
  rw [Finset.sum_sub_distrib]

/-- `ϱ_𝒟 > 0` under Assumption 14. -/
theorem varrhoD_pos (h : P.CSGDAssumption N η c0) : 0 < P.varrhoD N η c0 :=
  Finset.sum_pos (fun i hi => sub_pos.mpr (h.init_gt i hi)) P.D_nonempty

/-- The second initialization condition of Assumption 14 says exactly `‖P^𝒟 x_0‖² > δ`. -/
theorem varrho_gt_iff (P : Spec ι) (N : Noise ι) (η : ℝ) (c0 : ι → ℝ) :
    P.deltaC N η - ∑ i ∈ P.D, P.betaC N η i < P.varrhoD N η c0 ↔
      P.deltaC N η < P.normSqD c0 := by
  rw [varrhoD_eq]; constructor <;> intro h <;> linarith

theorem deltaC_lt_normSqD (h : P.CSGDAssumption N η c0) : P.deltaC N η < P.normSqD c0 :=
  (varrho_gt_iff P N η c0).mp h.varrho_gt

/-- The denominator inside the logarithm of `t*` is positive: `δ - ∑_𝒟 β_i > 0`
(needs non-zero noise `s_max > 0`). -/
theorem logDen_pos (h : P.CSGDAssumption N η c0) (hs : 0 < N.smax) :
    0 < P.deltaC N η - ∑ i ∈ P.D, P.betaC N η i :=
  sub_pos.mpr (h.step.sum_betaC_lt_deltaC N hs)

/-- **The argument of the logarithm in `t*` exceeds `1`** under Assumption 14 (with `s_max > 0`),
so the numerator `log (ϱ_𝒟 / (δ - ∑_𝒟 β_i))` of `t*` is well defined and positive. -/
theorem one_lt_logArg (h : P.CSGDAssumption N η c0) (hs : 0 < N.smax) :
    1 < P.varrhoD N η c0 / (P.deltaC N η - ∑ i ∈ P.D, P.betaC N η i) :=
  (one_lt_div (h.logDen_pos hs)).mpr h.varrho_gt

theorem log_logArg_pos (h : P.CSGDAssumption N η c0) (hs : 0 < N.smax) :
    0 < Real.log (P.varrhoD N η c0 / (P.deltaC N η - ∑ i ∈ P.D, P.betaC N η i)) :=
  Real.log_pos (h.one_lt_logArg hs)

/-- **Characterisation of `t*` (Theorem 15).**  Under Assumption 14 with non-zero noise, for every
admissible step size — including `1/λ_1 ≤ η`, where the paper's `log(1 - η λ_1)` is not a real
number and Lean's `Real.log x = log |x|`, `Real.log 0 = 0`, `x / 0 = 0` conventions are in force —
```
t ≤ t*  ↔  δ ≤ (1 - η λ_1)^{2t} ϱ_𝒟 + ∑_{i∈𝒟} β_i .
```
So `Spec.tStar` is the last time at which the paper's defining inequality holds. -/
theorem le_tStar_iff (h : P.CSGDAssumption N η c0) (hs : 0 < N.smax) (t : ℕ) :
    t ≤ P.tStar N η c0 ↔
      P.deltaC N η ≤ (1 - η * P.lam1) ^ (2 * t) * P.varrhoD N η c0 +
        ∑ i ∈ P.D, P.betaC N η i := by
  have hW := h.logDen_pos hs
  have hϱ := h.varrhoD_pos
  have hR := h.one_lt_logArg hs
  have hlogR := h.log_logArg_pos hs
  obtain ⟨hq1, hq2⟩ := h.step.one_sub_eta_lam1_mem
  set q := 1 - η * P.lam1 with hq_def
  set W := P.deltaC N η - ∑ i ∈ P.D, P.betaC N η i with hW_def
  set ϱ := P.varrhoD N η c0 with hϱ_def
  have hgoal : (P.deltaC N η ≤ q ^ (2 * t) * ϱ + ∑ i ∈ P.D, P.betaC N η i) ↔
      W ≤ q ^ (2 * t) * ϱ := by
    rw [hW_def]; constructor <;> intro h' <;> linarith
  rw [hgoal]
  unfold tStar
  rw [← hq_def, ← hW_def, ← hϱ_def]
  by_cases hq0 : q = 0
  · -- `η λ_1 = 1`: Lean's `t* = 0`
    rw [hq0, Real.log_zero, mul_zero, div_zero, Nat.floor_zero]
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp only [le_refl, mul_zero, pow_zero, one_mul, true_iff]
      exact (h.varrho_gt).le
    · have h0 : (0 : ℝ) ^ (2 * t) = 0 := zero_pow (by omega)
      rw [h0, zero_mul]
      constructor
      · intro h'; omega
      · intro h'; linarith
  · -- `0 < |q| < 1`
    have hlogq : Real.log q < 0 := by
      rcases lt_or_gt_of_ne hq0 with hneg | hpos
      · exact Real.log_neg_of_lt_zero hneg hq1
      · exact Real.log_neg hpos hq2
    have hden : 0 < -2 * Real.log q := by linarith
    have hx : 0 ≤ Real.log (ϱ / W) / (-2 * Real.log q) := (div_pos hlogR hden).le
    have hqpow : 0 < q ^ (2 * t) := by rw [pow_mul]; exact pow_pos (by positivity) _
    rw [Nat.le_floor_iff hx, le_div_iff₀ hden]
    have hlog : Real.log (ϱ / W * q ^ (2 * t)) =
        Real.log (ϱ / W) - (t : ℝ) * (-2 * Real.log q) := by
      rw [Real.log_mul (div_pos hϱ hW).ne' hqpow.ne', Real.log_pow]
      push_cast; ring
    have h1 : (t : ℝ) * (-2 * Real.log q) ≤ Real.log (ϱ / W) ↔
        0 ≤ Real.log (ϱ / W * q ^ (2 * t)) := by
      rw [hlog]; constructor <;> intro h' <;> linarith
    rw [h1, Real.log_nonneg_iff (mul_pos (div_pos hϱ hW) hqpow), div_mul_eq_mul_div,
      one_le_div hW, mul_comm]

/-- **Defining property of `t*` used in the proof of Theorem 15 (tex 2372–2375).**  For all
`t < t*`: `(1 - η λ_1)^{2t} ϱ_𝒟 + ∑_{i∈𝒟} β_i > δ`. -/
theorem deltaC_lt_of_lt_tStar (h : P.CSGDAssumption N η c0) (hs : 0 < N.smax) {t : ℕ}
    (ht : t < P.tStar N η c0) :
    P.deltaC N η < (1 - η * P.lam1) ^ (2 * t) * P.varrhoD N η c0 +
      ∑ i ∈ P.D, P.betaC N η i := by
  have h1 := (h.le_tStar_iff hs (t + 1)).mp ht
  have hϱ := h.varrhoD_pos
  have hβδ := h.step.sum_betaC_lt_deltaC N hs
  obtain ⟨hq1, hq2⟩ := h.step.one_sub_eta_lam1_mem
  have hq2' : (1 - η * P.lam1) ^ 2 < 1 := by
    rw [sq_lt_one_iff_abs_lt_one, abs_lt]; exact ⟨hq1, hq2⟩
  have hy : 0 ≤ (1 - η * P.lam1) ^ (2 * t) * P.varrhoD N η c0 :=
    mul_nonneg (by rw [pow_mul]; positivity) hϱ.le
  have hsplit : (1 - η * P.lam1) ^ (2 * (t + 1)) * P.varrhoD N η c0 =
      (1 - η * P.lam1) ^ 2 * ((1 - η * P.lam1) ^ (2 * t) * P.varrhoD N η c0) := by
    rw [show 2 * (t + 1) = 2 * t + 2 by ring, pow_add]; ring
  rw [hsplit] at h1
  rcases hy.eq_or_lt with hy0 | hypos
  · rw [← hy0, mul_zero] at h1; linarith
  · nlinarith [mul_pos (sub_pos.mpr hq2') hypos]

/-- **When is the initial phase non-empty?**  `t* ≥ 1` iff
`(1 - η λ_1)² ϱ_𝒟 ≥ δ - ∑_𝒟 β_i`.  Assumption 14 only gives `ϱ_𝒟 > δ - ∑_𝒟 β_i`, which is the
case `t* ≥ 0`: Theorem 15 can be vacuous under its own assumptions. -/
theorem one_le_tStar_iff (h : P.CSGDAssumption N η c0) (hs : 0 < N.smax) :
    1 ≤ P.tStar N η c0 ↔
      P.deltaC N η - ∑ i ∈ P.D, P.betaC N η i ≤ (1 - η * P.lam1) ^ 2 * P.varrhoD N η c0 := by
  rw [h.le_tStar_iff hs 1, mul_one]
  constructor <;> intro h' <;> linarith

/-- **Paper, proof of Theorem 15 (tex 2369–2370), corrected.**  If additionally `η λ_1 ≤ 1`
(so that `0 ≤ 1 - η λ_1 ≤ 1 - η λ_i`), then
`𝔼[∑_{i∈𝒟} c_{i,t}²] ≥ (1 - η λ_1)^{2t} ϱ_𝒟 + ∑_{i∈𝒟} β_i`.
(The paper writes "`=`"; it is an inequality, and it can fail when `η λ_1 > 1`.) -/
theorem le_sum_secondMoment_D (h : P.CSGDAssumption N η c0) (h1 : η * P.lam1 ≤ 1) (t : ℕ) :
    (1 - η * P.lam1) ^ (2 * t) * P.varrhoD N η c0 + ∑ i ∈ P.D, P.betaC N η i ≤
      ∑ i ∈ P.D, P.secondMoment N η c0 t i := by
  unfold varrhoD secondMoment
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  have hle : (1 - η * P.lam1) ^ (2 * t) ≤ (1 - η * P.lam i) ^ (2 * t) :=
    pow_le_pow_left₀ (by linarith)
      (by have := mul_le_mul_of_nonneg_left (P.le_lam1_of_mem hi) h.step.pos.le; linarith) _
  have := mul_le_mul_of_nonneg_right hle (sub_pos.mpr (h.init_gt i hi)).le
  linarith

/-- **The step at tex 2369–2370 can fail when `η λ_1 > 1`** (which Assumption 14 allows, see
`CSGDMoments.ex_one_sub_eta_lam1_neg`).  If every dominant mode contracts at least as fast as the
top mode, `|1 - η λ_i| ≤ |1 - η λ_1|` on `𝒟` (this forces `η λ_1 ≥ 1`), and strictly faster for
some `i ∈ 𝒟`, then for every `t ≥ 1` the paper's lower bound is *reversed*:
`𝔼[∑_𝒟 c_{i,t}²] < (1 - η λ_1)^{2t} ϱ_𝒟 + ∑_𝒟 β_i`.
(Numerical instance: `λ = (1, 4/5, 1/100)`, `k = 2`, `η = 5/4 < 2(λ_k - λ_{k+1})/(λ_1² - λ_d²)`,
where `1 - η λ_1 = -1/4` and `1 - η λ_2 = 0`.) -/
theorem sum_secondMoment_D_lt (h : P.CSGDAssumption N η c0)
    (hle : ∀ i ∈ P.D, |1 - η * P.lam i| ≤ |1 - η * P.lam1|)
    (hlt : ∃ i ∈ P.D, |1 - η * P.lam i| < |1 - η * P.lam1|) {t : ℕ} (ht : 1 ≤ t) :
    ∑ i ∈ P.D, P.secondMoment N η c0 t i <
      (1 - η * P.lam1) ^ (2 * t) * P.varrhoD N η c0 + ∑ i ∈ P.D, P.betaC N η i := by
  unfold varrhoD secondMoment
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  have he : Even (2 * t) := even_two_mul t
  apply Finset.sum_lt_sum
  · intro i hi
    have hpow : (1 - η * P.lam i) ^ (2 * t) ≤ (1 - η * P.lam1) ^ (2 * t) := by
      rw [← he.pow_abs (1 - η * P.lam i), ← he.pow_abs (1 - η * P.lam1)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hle i hi) _
    have := mul_le_mul_of_nonneg_right hpow (sub_pos.mpr (h.init_gt i hi)).le
    linarith
  · obtain ⟨i, hi, hi_lt⟩ := hlt
    refine ⟨i, hi, ?_⟩
    have hpow : (1 - η * P.lam i) ^ (2 * t) < (1 - η * P.lam1) ^ (2 * t) := by
      rw [← he.pow_abs (1 - η * P.lam i), ← he.pow_abs (1 - η * P.lam1)]
      exact pow_lt_pow_left₀ hi_lt (abs_nonneg _) (by omega)
    have := mul_lt_mul_of_pos_right hpow (sub_pos.mpr (h.init_gt i hi))
    linarith

/-- **Theorem 16, finite-`d` core, under the paper's hypotheses** (Assumption 14 and `Tr Σ > 0`
from Assumption 1): `lim_{t→∞} 𝔼[s_t^𝒟]/𝔼[s_t] = θ_∞`. -/
theorem tendsto_thetaBarCSGD (h : P.CSGDAssumption N η c0) (hκ : ∃ i, 0 < N.kap2 i) :
    Tendsto (fun t => P.thetaBarCSGD N η c0 t) atTop (𝓝 (P.thetaInf N η)) :=
  P.tendsto_thetaBarCSGD N h.step.pos h.step.lt_stab hκ c0

/-- Under Assumption 14 the convergence rate in Theorem 16 is governed by the smallest bulk
eigenvalue: `|𝔼[s_t^𝒟]/𝔼[s_t] - θ_∞| ≤ 2 (1 - η λ_d)^{2t} ∑ λ_i² |c_{i,0}² - β_i| / ∑ λ_i² β_i`. -/
theorem abs_thetaBarCSGD_sub_thetaInf_le (h : P.CSGDAssumption N η c0) (hκ : ∃ i, 0 < N.kap2 i)
    (t : ℕ) :
    |P.thetaBarCSGD N η c0 t - P.thetaInf N η| ≤
      2 * (1 - η * P.lamd) ^ (2 * t) * P.initExcessC N Finset.univ η c0 /
        P.statEnergyC N Finset.univ η := by
  rw [← h.step.contrC_eq]
  exact P.abs_thetaBarCSGD_sub_thetaInf_le N h.step.pos h.step.lt_stab
    (P.statEnergyC_univ_pos N h.step.pos h.step.lt_stab hκ) c0 t

end CSGDAssumption

end Spec

/-! ### Probability layer: the recursion `𝔼[c_{t+1}²] = (1-ηλ)² 𝔼[c_t²] + η² κ²` from the SGD update

The lemmas above are purely algebraic.  This section derives the second-moment recursion from the
SGD update `c_{i,t+1} = (1 - η λ_i) c_{i,t} - η ζ_{i,t}` on an actual probability space, assuming
only that the noise coordinate `ζ_{i,t}` is square integrable, centred, has variance `κ_i²` and is
independent of the current coordinate `c_{i,t}` (no Gaussianity is needed for second moments). -/

section Probability

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **One SGD step in second moment (tex 2152–2163).**  If `c, ζ ∈ L²` are independent and
`𝔼 ζ = 0`, then `𝔼[((1 - ηλ) c - η ζ)²] = (1 - ηλ)² 𝔼[c²] + η² 𝔼[ζ²]`. -/
theorem csgd_integral_step_sq [IsProbabilityMeasure μ] {c ζ : Ω → ℝ} (hc : MemLp c 2 μ)
    (hζ : MemLp ζ 2 μ) (hind : IndepFun c ζ μ) (hmean : ∫ ω, ζ ω ∂μ = 0) (η lam : ℝ) :
    ∫ ω, ((1 - η * lam) * c ω - η * ζ ω) ^ 2 ∂μ =
      (1 - η * lam) ^ 2 * ∫ ω, c ω ^ 2 ∂μ + η ^ 2 * ∫ ω, ζ ω ^ 2 ∂μ := by
  have hc2 : Integrable (fun ω => c ω ^ 2) μ := hc.integrable_sq
  have hζ2 : Integrable (fun ω => ζ ω ^ 2) μ := hζ.integrable_sq
  have hcζ : Integrable (fun ω => c ω * ζ ω) μ := hc.integrable_mul hζ
  have hprod : ∫ ω, c ω * ζ ω ∂μ = 0 := by
    rw [hind.integral_fun_mul_eq_mul_integral hc.aestronglyMeasurable hζ.aestronglyMeasurable,
      hmean, mul_zero]
  have hexp : ∀ ω, ((1 - η * lam) * c ω - η * ζ ω) ^ 2 =
      (1 - η * lam) ^ 2 * c ω ^ 2 - 2 * η * (1 - η * lam) * (c ω * ζ ω) + η ^ 2 * ζ ω ^ 2 :=
    fun ω => by ring
  simp_rw [hexp]
  have hI1 : Integrable (fun ω => (1 - η * lam) ^ 2 * c ω ^ 2) μ := hc2.const_mul _
  have hI2 : Integrable (fun ω => 2 * η * (1 - η * lam) * (c ω * ζ ω)) μ := hcζ.const_mul _
  have hI3 : Integrable (fun ω => η ^ 2 * ζ ω ^ 2) μ := hζ2.const_mul _
  have hI12 : Integrable
      (fun ω => (1 - η * lam) ^ 2 * c ω ^ 2 - 2 * η * (1 - η * lam) * (c ω * ζ ω)) μ :=
    hI1.sub hI2
  have e1 : ∫ ω, (1 - η * lam) ^ 2 * c ω ^ 2 - 2 * η * (1 - η * lam) * (c ω * ζ ω) +
      η ^ 2 * ζ ω ^ 2 ∂μ =
      (∫ ω, (1 - η * lam) ^ 2 * c ω ^ 2 - 2 * η * (1 - η * lam) * (c ω * ζ ω) ∂μ) +
        ∫ ω, η ^ 2 * ζ ω ^ 2 ∂μ := integral_add hI12 hI3
  have e2 : ∫ ω, (1 - η * lam) ^ 2 * c ω ^ 2 - 2 * η * (1 - η * lam) * (c ω * ζ ω) ∂μ =
      (∫ ω, (1 - η * lam) ^ 2 * c ω ^ 2 ∂μ) - ∫ ω, 2 * η * (1 - η * lam) * (c ω * ζ ω) ∂μ :=
    integral_sub hI1 hI2
  rw [e1, e2, integral_const_mul, integral_const_mul, integral_const_mul, hprod]
  ring

variable (P : Spec ι) (N : Noise ι)

/-- **Second moments of CSGD (tex 2423–2427).**  Let `c t ω` be the eigen-coordinates of a CSGD
trajectory, `c (t+1) = cNext η (c t) (ζ t)` with deterministic start `c 0 = c0`.  If, for the
coordinate `i`, the noise `ζ_{i,t}` is in `L²`, centred with variance `κ_i²`, and independent of
`c_{i,t}`, then `c_{i,t} ∈ L²` and
`𝔼[c_{i,t}²] = (1 - η λ_i)^{2t} (c_{i,0}² - β_i) + β_i = Spec.secondMoment`. -/
theorem csgd_integral_sq_eq_secondMoment [IsProbabilityMeasure μ] {η : ℝ} (c0 : ι → ℝ)
    (c ζ : ℕ → Ω → ι → ℝ) (h0 : ∀ ω, c 0 ω = c0)
    (hstep : ∀ t ω, c (t + 1) ω = P.cNext η (c t ω) (ζ t ω)) {i : ι}
    (hden : 2 * P.lam i - η * P.lam i ^ 2 ≠ 0)
    (hζ : ∀ t, MemLp (fun ω => ζ t ω i) 2 μ)
    (hind : ∀ t, IndepFun (fun ω => c t ω i) (fun ω => ζ t ω i) μ)
    (hmean : ∀ t, ∫ ω, ζ t ω i ∂μ = 0)
    (hvar : ∀ t, ∫ ω, ζ t ω i ^ 2 ∂μ = N.kap2 i) (t : ℕ) :
    MemLp (fun ω => c t ω i) 2 μ ∧ ∫ ω, c t ω i ^ 2 ∂μ = P.secondMoment N η c0 t i := by
  induction t with
  | zero =>
    have hfun : (fun ω => c 0 ω i) = fun _ => c0 i := by funext ω; rw [h0]
    refine ⟨by rw [hfun]; exact memLp_const _, ?_⟩
    simp [h0]
  | succ t ih =>
    obtain ⟨hL2, hint⟩ := ih
    have hfun : (fun ω => c (t + 1) ω i) =
        fun ω => (1 - η * P.lam i) * c t ω i - η * ζ t ω i := by
      funext ω; rw [hstep]; rfl
    constructor
    · rw [hfun]; exact (hL2.const_mul _).sub ((hζ t).const_mul _)
    · have e : ∀ ω, c (t + 1) ω i ^ 2 = ((1 - η * P.lam i) * c t ω i - η * ζ t ω i) ^ 2 :=
        fun ω => by rw [hstep]; rfl
      simp_rw [e]
      rw [csgd_integral_step_sq hL2 (hζ t) (hind t) (hmean t), hint, hvar,
        P.secondMoment_succ N hden]

/-- **Expected block energies of CSGD (tex 2433–2437)**:
`𝔼[∑_{i∈S} λ_i² c_{i,t}²] = ∑_{i∈S} λ_i² 𝔼[c_{i,t}²] = Spec.expEnergyC`. -/
theorem csgd_integral_mom [IsProbabilityMeasure μ] {η : ℝ} (hη : 0 < η) (hstab : η < 2 / P.lam1)
    (c0 : ι → ℝ) (c ζ : ℕ → Ω → ι → ℝ) (h0 : ∀ ω, c 0 ω = c0)
    (hstep : ∀ t ω, c (t + 1) ω = P.cNext η (c t ω) (ζ t ω))
    (hζ : ∀ t i, MemLp (fun ω => ζ t ω i) 2 μ)
    (hind : ∀ t i, IndepFun (fun ω => c t ω i) (fun ω => ζ t ω i) μ)
    (hmean : ∀ t i, ∫ ω, ζ t ω i ∂μ = 0)
    (hvar : ∀ t i, ∫ ω, ζ t ω i ^ 2 ∂μ = N.kap2 i) (S : Finset ι) (t : ℕ) :
    ∫ ω, P.mom S 2 (c t ω) ∂μ = P.expEnergyC N S η c0 t := by
  have key := fun i => csgd_integral_sq_eq_secondMoment P N c0 c ζ h0 hstep
    (P.betaC_den_pos hη hstab i).ne' (fun t => hζ t i) (fun t => hind t i) (fun t => hmean t i)
    (fun t => hvar t i) t
  unfold Spec.mom Spec.expEnergyC
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, (key i).2]
  · intro i _
    exact ((key i).1.integrable_sq).const_mul _

/-- **Theorem 16 (Late Phase), finite `d`, for the ratio of true expectations.**  For a CSGD
trajectory on a probability space with `0 < η < 2/λ_1`, coordinatewise centred `L²` noise of
variances `κ_i²` independent of the current state, and `Tr Σ > 0`:
`lim_{t→∞} 𝔼[s_t^𝒟] / 𝔼[s_t] = θ_∞`. -/
theorem csgd_tendsto_ratio_expected_energies [IsProbabilityMeasure μ] {η : ℝ} (hη : 0 < η)
    (hstab : η < 2 / P.lam1) (hκ : ∃ i, 0 < N.kap2 i)
    (c0 : ι → ℝ) (c ζ : ℕ → Ω → ι → ℝ) (h0 : ∀ ω, c 0 ω = c0)
    (hstep : ∀ t ω, c (t + 1) ω = P.cNext η (c t ω) (ζ t ω))
    (hζ : ∀ t i, MemLp (fun ω => ζ t ω i) 2 μ)
    (hind : ∀ t i, IndepFun (fun ω => c t ω i) (fun ω => ζ t ω i) μ)
    (hmean : ∀ t i, ∫ ω, ζ t ω i ∂μ = 0)
    (hvar : ∀ t i, ∫ ω, ζ t ω i ^ 2 ∂μ = N.kap2 i) :
    Tendsto (fun t => (∫ ω, P.sD (c t ω) ∂μ) / ∫ ω, P.s (c t ω) ∂μ) atTop
      (𝓝 (P.thetaInf N η)) := by
  have hD : ∀ t, ∫ ω, P.sD (c t ω) ∂μ = P.expEnergyC N P.D η c0 t := fun t =>
    csgd_integral_mom P N hη hstab c0 c ζ h0 hstep hζ hind hmean hvar P.D t
  have hU : ∀ t, ∫ ω, P.s (c t ω) ∂μ = P.expEnergyC N Finset.univ η c0 t := fun t => by
    rw [← csgd_integral_mom P N hη hstab c0 c ζ h0 hstep hζ hind hmean hvar Finset.univ t]
    simp_rw [P.s_eq_sum]
    rfl
  simp_rw [hD, hU]
  exact P.tendsto_thetaBarCSGD N hη hstab hκ c0

end Probability

/-! ### Examples and counterexamples -/

namespace CSGDMoments

/-- A two-level spectrum on `α ⊕ β`: eigenvalue `a` on the dominant block `α`, eigenvalue `b < a`
on the bulk block `β`. -/
def twoLevel (α β : Type) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (a0 : α) (b0 : β) (a b : ℝ) (hb : 0 < b) (hab : b < a) : Spec (α ⊕ β) where
  lam := Sum.elim (fun _ => a) (fun _ => b)
  D := Finset.univ.map Function.Embedding.inl
  i1 := Sum.inl a0
  ik := Sum.inl a0
  ik1 := Sum.inr b0
  id := Sum.inr b0
  i1_mem := by simp
  ik_mem := by simp
  ik1_not_mem := by simp
  id_not_mem := by simp
  lam_pos := by rintro (x | y) <;> simp <;> linarith
  le_lam1 := by rintro (x | y) h <;> simp at h ⊢
  lamk_le := by rintro (x | y) h <;> simp at h ⊢
  le_lamk1 := by rintro (x | y) h <;> simp at h ⊢
  lamd_le := by rintro (x | y) h <;> simp at h ⊢
  gap := by simpa using hab

/-- Isotropic noise `Σ = σ² I`. -/
def isoNoise (ι : Type*) (σ2 : ℝ) (h : 0 ≤ σ2) : Noise ι where
  kap2 := fun _ => σ2
  smin := σ2
  smax := σ2
  smin_nonneg := h
  smin_le := fun _ => le_rfl
  le_smax := fun _ => le_rfl

section twoLevel

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  (a0 : α) (b0 : β) (a b : ℝ) (hb : 0 < b) (hab : b < a)

@[simp] theorem twoLevel_lam_inl (x : α) : (twoLevel α β a0 b0 a b hb hab).lam (Sum.inl x) = a :=
  rfl
@[simp] theorem twoLevel_lam_inr (y : β) : (twoLevel α β a0 b0 a b hb hab).lam (Sum.inr y) = b :=
  rfl
@[simp] theorem twoLevel_lam1 : (twoLevel α β a0 b0 a b hb hab).lam1 = a := rfl
@[simp] theorem twoLevel_lamk : (twoLevel α β a0 b0 a b hb hab).lamk = a := rfl
@[simp] theorem twoLevel_lamk1 : (twoLevel α β a0 b0 a b hb hab).lamk1 = b := rfl
@[simp] theorem twoLevel_lamd : (twoLevel α β a0 b0 a b hb hab).lamd = b := rfl

theorem twoLevel_sum_D (f : α ⊕ β → ℝ) :
    ∑ i ∈ (twoLevel α β a0 b0 a b hb hab).D, f i = ∑ x : α, f (Sum.inl x) := by
  simp [twoLevel, Finset.sum_map]

theorem twoLevel_sum_B (f : α ⊕ β → ℝ) :
    ∑ i ∈ (twoLevel α β a0 b0 a b hb hab).B, f i = ∑ y : β, f (Sum.inr y) := by
  have h := (twoLevel α β a0 b0 a b hb hab).sum_D_add_sum_B f
  rw [twoLevel_sum_D, Fintype.sum_sum_type] at h
  linarith

theorem twoLevel_mem_D_inl (x : α) : Sum.inl x ∈ (twoLevel α β a0 b0 a b hb hab).D := by
  simp [twoLevel]

theorem twoLevel_forall_mem_D {p : α ⊕ β → Prop} :
    (∀ i ∈ (twoLevel α β a0 b0 a b hb hab).D, p i) ↔ ∀ x : α, p (Sum.inl x) := by
  simp [twoLevel]

end twoLevel

/-- Closed form of the expected dominant energy for a two-level spectrum. -/
theorem twoLevel_expEnergyC_D {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (a0 : α) (b0 : β) (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (N : Noise (α ⊕ β)) (η : ℝ) (c0 : α ⊕ β → ℝ) (t : ℕ) :
    (twoLevel α β a0 b0 a b hb hab).expEnergyC N (twoLevel α β a0 b0 a b hb hab).D η c0 t =
      ∑ x : α, a ^ 2 * ((1 - η * a) ^ (2 * t) *
        (c0 (Sum.inl x) ^ 2 - η * N.kap2 (Sum.inl x) / (2 * a - η * a ^ 2)) +
          η * N.kap2 (Sum.inl x) / (2 * a - η * a ^ 2)) := by
  unfold Spec.expEnergyC
  rw [twoLevel_sum_D]
  rfl

/-- Closed form of the expected total energy for a two-level spectrum. -/
theorem twoLevel_expEnergyC_univ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (a0 : α) (b0 : β) (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (N : Noise (α ⊕ β)) (η : ℝ) (c0 : α ⊕ β → ℝ) (t : ℕ) :
    (twoLevel α β a0 b0 a b hb hab).expEnergyC N Finset.univ η c0 t =
      ∑ x : α, a ^ 2 * ((1 - η * a) ^ (2 * t) *
        (c0 (Sum.inl x) ^ 2 - η * N.kap2 (Sum.inl x) / (2 * a - η * a ^ 2)) +
          η * N.kap2 (Sum.inl x) / (2 * a - η * a ^ 2)) +
      ∑ y : β, b ^ 2 * ((1 - η * b) ^ (2 * t) *
        (c0 (Sum.inr y) ^ 2 - η * N.kap2 (Sum.inr y) / (2 * b - η * b ^ 2)) +
          η * N.kap2 (Sum.inr y) / (2 * b - η * b ^ 2)) := by
  unfold Spec.expEnergyC
  rw [Fintype.sum_sum_type]
  rfl

/-- Closed form of the stationary energies for a two-level spectrum. -/
theorem twoLevel_statEnergyC_D {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (a0 : α) (b0 : β) (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (N : Noise (α ⊕ β)) (η : ℝ) :
    (twoLevel α β a0 b0 a b hb hab).statEnergyC N (twoLevel α β a0 b0 a b hb hab).D η =
      ∑ x : α, a ^ 2 * (η * N.kap2 (Sum.inl x) / (2 * a - η * a ^ 2)) := by
  unfold Spec.statEnergyC
  rw [twoLevel_sum_D]
  rfl

theorem twoLevel_statEnergyC_univ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (a0 : α) (b0 : β) (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (N : Noise (α ⊕ β)) (η : ℝ) :
    (twoLevel α β a0 b0 a b hb hab).statEnergyC N Finset.univ η =
      ∑ x : α, a ^ 2 * (η * N.kap2 (Sum.inl x) / (2 * a - η * a ^ 2)) +
      ∑ y : β, b ^ 2 * (η * N.kap2 (Sum.inr y) / (2 * b - η * b ^ 2)) := by
  unfold Spec.statEnergyC
  rw [Fintype.sum_sum_type]
  rfl

/-! #### Assumption 14 is satisfiable, but does not make `t*` meaningful -/

/-- The two-point spectrum `λ = (1, 1/2)`. -/
noncomputable def exP : Spec (Unit ⊕ Unit) :=
  twoLevel Unit Unit () () 1 (1 / 2) (by norm_num) (by norm_num)

/-- Unit isotropic noise. -/
noncomputable def exN : Noise (Unit ⊕ Unit) := isoNoise _ 1 zero_le_one

/-- Initial state `c_0 = (10, 0)`. -/
noncomputable def exC0 : Unit ⊕ Unit → ℝ := Sum.elim (fun _ => 10) (fun _ => 0)

theorem ex_betaC_inl (x : Unit) : exP.betaC exN (5 / 4) (Sum.inl x) = 5 / 3 := by
  show (5 / 4 : ℝ) * 1 / (2 * 1 - 5 / 4 * 1 ^ 2) = 5 / 3
  norm_num

theorem ex_deltaC : exP.deltaC exN (5 / 4) = 80 := by
  have hψ : exP.psiD = 1 := by
    unfold Spec.psiD exP
    rw [twoLevel_sum_D, Fintype.sum_unique]
    show (1 : ℝ) ^ 2 = 1
    norm_num
  unfold Spec.deltaC
  rw [hψ]
  show (1 : ℝ) * 1 * 1 ^ 2 / ((1 / 2) ^ 2 * 1 ^ 2 * (2 * (1 - 1 / 2) / (5 / 4) -
    (1 ^ 2 - (1 / 2) ^ 2))) = 80
  norm_num

theorem ex_sum_betaC : ∑ i ∈ exP.D, exP.betaC exN (5 / 4) i = 5 / 3 := by
  have : ∑ i ∈ exP.D, exP.betaC exN (5 / 4) i = ∑ x : Unit, exP.betaC exN (5 / 4) (Sum.inl x) :=
    twoLevel_sum_D _ _ _ _ _ _ _
  rw [this, Fintype.sum_unique]
  exact ex_betaC_inl _

theorem ex_varrhoD : exP.varrhoD exN (5 / 4) exC0 = 100 - 5 / 3 := by
  have h1 : ∑ i ∈ exP.D, exC0 i ^ 2 = 100 := by
    have : ∑ i ∈ exP.D, exC0 i ^ 2 = ∑ x : Unit, exC0 (Sum.inl x) ^ 2 :=
      twoLevel_sum_D _ _ _ _ _ _ _
    rw [this, Fintype.sum_unique]
    show (10 : ℝ) ^ 2 = 100
    norm_num
  unfold Spec.varrhoD
  rw [Finset.sum_sub_distrib, ex_sum_betaC, h1]

/-- **Assumption 14 is satisfiable** (non-vacuity), here with `η λ_1 = 5/4 > 1`. -/
theorem ex_assumption : exP.CSGDAssumption exN (5 / 4) exC0 := by
  refine ⟨⟨by norm_num, ?_⟩, ?_, ?_⟩
  · show (5 / 4 : ℝ) < min (2 / 1) (2 * (1 - 1 / 2) / (1 ^ 2 - (1 / 2) ^ 2))
    norm_num
  · have : ∀ x : Unit, exP.betaC exN (5 / 4) (Sum.inl x) < exC0 (Sum.inl x) ^ 2 := by
      intro x
      rw [ex_betaC_inl]
      show (5 / 3 : ℝ) < 10 ^ 2
      norm_num
    exact (twoLevel_forall_mem_D _ _ _ _ _ _).mpr this
  · rw [ex_deltaC, ex_sum_betaC, ex_varrhoD]; norm_num

/-- **Assumption 14 does not make the paper's `t*` well defined**: here Assumption 14 holds with
non-zero noise, but `1 - η λ_1 = -1/4 < 0`, so the paper's `log(1 - η λ_1)` is not a real number.
(With Lean's `Real.log x = log |x|` the formula still makes sense, see
`Spec.CSGDAssumption.le_tStar_iff`.) -/
theorem ex_one_sub_eta_lam1_neg :
    exP.CSGDAssumption exN (5 / 4) exC0 ∧ 0 < exN.smax ∧ 1 - 5 / 4 * exP.lam1 < 0 := by
  refine ⟨ex_assumption, ?_, ?_⟩
  · show (0 : ℝ) < 1
    norm_num
  · show (1 : ℝ) - 5 / 4 * 1 < 0
    norm_num

/-- **Theorem 15 can be vacuous under Assumption 14**: in this example `t* = 0`, so the set
`{0, …, t* - 1}` of time steps for which Theorem 15 asserts a decrease is empty. -/
theorem ex_tStar_eq_zero : exP.tStar exN (5 / 4) exC0 = 0 := by
  have hs : 0 < exN.smax := ex_one_sub_eta_lam1_neg.2.1
  have h := (ex_assumption.one_le_tStar_iff hs).not
  rw [ex_deltaC, ex_sum_betaC, ex_varrhoD] at h
  have : ¬ (1 ≤ exP.tStar exN (5 / 4) exC0) := by
    rw [h]
    show ¬ ((80 : ℝ) - 5 / 3 ≤ (1 - 5 / 4 * 1) ^ 2 * (100 - 5 / 3))
    norm_num
  omega

/-! #### The lower bound in the proof of Theorem 15 can be reversed when `η λ_1 > 1` -/

/-- The three-point spectrum `λ = (1, 4/5, 1/100)` with `k = 2`. -/
noncomputable def exP3 : Spec (Fin 3) where
  lam := ![1, 4 / 5, 1 / 100]
  D := {0, 1}
  i1 := 0
  ik := 1
  ik1 := 2
  id := 2
  i1_mem := by decide
  ik_mem := by decide
  ik1_not_mem := by decide
  id_not_mem := by decide
  lam_pos := by intro i; fin_cases i <;> simp
  le_lam1 := by
    intro i hi
    fin_cases i <;> first | (exfalso; revert hi; decide) | (simp; try norm_num)
  lamk_le := by
    intro i hi
    fin_cases i <;> first | (exfalso; revert hi; decide) | (simp; try norm_num)
  le_lamk1 := by
    intro i hi; fin_cases i <;> first | (exfalso; apply hi; decide) | simp
  lamd_le := by
    intro i hi; fin_cases i <;> first | (exfalso; apply hi; decide) | simp
  gap := by simp; norm_num

/-- Unit isotropic noise on three directions. -/
noncomputable def exN3 : Noise (Fin 3) := isoNoise _ 1 zero_le_one

/-- Initial state `c_0 = (400, 400, 0)`. -/
noncomputable def exC3 : Fin 3 → ℝ := ![400, 400, 0]

theorem ex3_sum_D (f : Fin 3 → ℝ) : ∑ i ∈ exP3.D, f i = f 0 + f 1 :=
  Finset.sum_pair (by decide)

theorem ex3_forall_mem_D {p : Fin 3 → Prop} (h0 : p 0) (h1 : p 1) : ∀ i ∈ exP3.D, p i := by
  intro i hi
  have : i = 0 ∨ i = 1 := by simpa [exP3] using hi
  rcases this with rfl | rfl
  · exact h0
  · exact h1

theorem ex3_assumption : exP3.CSGDAssumption exN3 (5 / 4) exC3 := by
  refine ⟨⟨by norm_num, ?_⟩, ?_, ?_⟩
  · show (5 / 4 : ℝ) < min (2 / 1) (2 * (4 / 5 - 1 / 100) / (1 ^ 2 - (1 / 100) ^ 2))
    norm_num
  · apply ex3_forall_mem_D
    · show (5 / 4 : ℝ) * 1 / (2 * 1 - 5 / 4 * 1 ^ 2) < 400 ^ 2
      norm_num
    · show (5 / 4 : ℝ) * 1 / (2 * (4 / 5) - 5 / 4 * (4 / 5) ^ 2) < 400 ^ 2
      norm_num
  · rw [Spec.CSGDAssumption.varrho_gt_iff]
    unfold Spec.deltaC Spec.psiD Spec.normSqD
    rw [ex3_sum_D, ex3_sum_D]
    show (1 : ℝ) * (1 ^ 2 + (4 / 5) ^ 2) * 1 ^ 2 /
        ((1 / 100) ^ 2 * (4 / 5) ^ 2 * (2 * (4 / 5 - 1 / 100) / (5 / 4) - (1 ^ 2 - (1 / 100) ^ 2))) <
      400 ^ 2 + 400 ^ 2
    norm_num

/-- **Formal counterexample to the step at tex 2369–2370.**  For `λ = (1, 4/5, 1/100)`, `k = 2`,
`Σ = I`, `η = 5/4`, `c_0 = (400, 400, 0)`: Assumption 14 holds, the noise is non-zero, and for
every `t ≥ 1`
`𝔼[∑_{i∈𝒟} c_{i,t}²] < (1 - η λ_1)^{2t} ϱ_𝒟 + ∑_{i∈𝒟} β_i`,
i.e. the paper's claimed lower bound (written there as an equality) is violated. -/
theorem ex3_lower_bound_fails :
    exP3.CSGDAssumption exN3 (5 / 4) exC3 ∧ 0 < exN3.smax ∧
    ∀ t, 1 ≤ t → ∑ i ∈ exP3.D, exP3.secondMoment exN3 (5 / 4) exC3 t i <
      (1 - 5 / 4 * exP3.lam1) ^ (2 * t) * exP3.varrhoD exN3 (5 / 4) exC3 +
        ∑ i ∈ exP3.D, exP3.betaC exN3 (5 / 4) i := by
  refine ⟨ex3_assumption, ?_, fun t ht => ?_⟩
  · show (0 : ℝ) < 1
    norm_num
  · have h1 : (1 - 5 / 4 * exP3.lam 1 : ℝ) = 0 := by
      show (1 - 5 / 4 * (4 / 5) : ℝ) = 0
      norm_num
    have h0 : (0 : ℝ) < |1 - 5 / 4 * exP3.lam1| := by
      apply abs_pos.mpr
      show (1 - 5 / 4 * 1 : ℝ) ≠ 0
      norm_num
    refine ex3_assumption.sum_secondMoment_D_lt ?_ ⟨1, by decide, ?_⟩ ht
    · apply ex3_forall_mem_D
      · exact le_rfl
      · rw [h1, abs_zero]; exact h0.le
    · rw [h1, abs_zero]; exact h0

/-! #### Non-zero noise is needed in the finite-`d` core of Theorem 16 -/

/-- The two-point spectrum `λ = (2, 1)`. -/
noncomputable def exP' : Spec (Unit ⊕ Unit) :=
  twoLevel Unit Unit () () 2 1 (by norm_num) (by norm_num)

/-- Zero noise. -/
noncomputable def exN0 : Noise (Unit ⊕ Unit) := isoNoise _ 0 le_rfl

/-- Initial state `c_0 = (1, 0)`, entirely in the dominant direction. -/
noncomputable def exC0' : Unit ⊕ Unit → ℝ := Sum.elim (fun _ => 1) (fun _ => 0)

theorem ex'_betaC (η : ℝ) (i : Unit ⊕ Unit) : exP'.betaC exN0 η i = 0 :=
  exP'.betaC_eq_zero_of_kap2_eq_zero exN0 rfl

/-- **The hypothesis "`κ_i² > 0` for some `i`" in `Spec.tendsto_thetaBarCSGD` cannot be dropped.**
With zero noise (which violates `Tr Σ > 0` of Assumption 1 but satisfies Assumption 14), the ratio
of expected energies is constantly `1`, whereas `θ_∞ = 0/0` (`= 0` in Lean). -/
theorem ex'_not_tendsto :
    exP'.CSGDAssumption exN0 (1 / 4) exC0' ∧
    (∀ t, exP'.thetaBarCSGD exN0 (1 / 4) exC0' t = 1) ∧
    exP'.thetaInf exN0 (1 / 4) = 0 ∧
    ¬ Tendsto (fun t => exP'.thetaBarCSGD exN0 (1 / 4) exC0' t) atTop
      (𝓝 (exP'.thetaInf exN0 (1 / 4))) := by
  have hbar : ∀ t, exP'.thetaBarCSGD exN0 (1 / 4) exC0' t = 1 := by
    intro t
    have hD : exP'.expEnergyC exN0 exP'.D (1 / 4) exC0' t = 2 ^ 2 * (1 - 1 / 4 * 2) ^ (2 * t) := by
      unfold exP'
      rw [twoLevel_expEnergyC_D, Fintype.sum_unique]
      show (2 : ℝ) ^ 2 * ((1 - 1 / 4 * 2) ^ (2 * t) * (1 ^ 2 - 1 / 4 * 0 / (2 * 2 - 1 / 4 * 2 ^ 2)) +
        1 / 4 * 0 / (2 * 2 - 1 / 4 * 2 ^ 2)) = 2 ^ 2 * (1 - 1 / 4 * 2) ^ (2 * t)
      ring
    have hU : exP'.expEnergyC exN0 Finset.univ (1 / 4) exC0' t =
        2 ^ 2 * (1 - 1 / 4 * 2) ^ (2 * t) := by
      unfold exP'
      rw [twoLevel_expEnergyC_univ, Fintype.sum_unique, Fintype.sum_unique]
      show (2 : ℝ) ^ 2 * ((1 - 1 / 4 * 2) ^ (2 * t) * (1 ^ 2 - 1 / 4 * 0 / (2 * 2 - 1 / 4 * 2 ^ 2)) +
        1 / 4 * 0 / (2 * 2 - 1 / 4 * 2 ^ 2)) +
        1 ^ 2 * ((1 - 1 / 4 * 1) ^ (2 * t) * (0 ^ 2 - 1 / 4 * 0 / (2 * 1 - 1 / 4 * 1 ^ 2)) +
        1 / 4 * 0 / (2 * 1 - 1 / 4 * 1 ^ 2)) = 2 ^ 2 * (1 - 1 / 4 * 2) ^ (2 * t)
      ring
    unfold Spec.thetaBarCSGD
    rw [hD, hU]
    exact div_self (by positivity)
  have hinf : exP'.thetaInf exN0 (1 / 4) = 0 :=
    exP'.thetaInf_eq_zero_of_noise_bulk_only exN0 _ (fun i _ => rfl)
  refine ⟨⟨⟨by norm_num, ?_⟩, ?_, ?_⟩, hbar, hinf, ?_⟩
  · show (1 / 4 : ℝ) < min (2 / 2) (2 * (2 - 1) / (2 ^ 2 - 1 ^ 2))
    norm_num
  · have : ∀ x : Unit, exP'.betaC exN0 (1 / 4) (Sum.inl x) < exC0' (Sum.inl x) ^ 2 := by
      intro x
      rw [ex'_betaC]
      show (0 : ℝ) < 1 ^ 2
      norm_num
    exact (twoLevel_forall_mem_D _ _ _ _ _ _).mpr this
  · have hδ : exP'.deltaC exN0 (1 / 4) = 0 := by
      unfold Spec.deltaC
      rw [show exN0.smax = 0 from rfl]; simp
    have hϱ : exP'.varrhoD exN0 (1 / 4) exC0' = 1 := by
      have h1 : ∑ i ∈ exP'.D, exC0' i ^ 2 = 1 := by
        have : ∑ i ∈ exP'.D, exC0' i ^ 2 = ∑ x : Unit, exC0' (Sum.inl x) ^ 2 :=
          twoLevel_sum_D _ _ _ _ _ _ _
        rw [this, Fintype.sum_unique]
        show (1 : ℝ) ^ 2 = 1
        norm_num
      unfold Spec.varrhoD
      rw [Finset.sum_sub_distrib, h1, Finset.sum_eq_zero (fun i _ => ex'_betaC _ i), sub_zero]
    rw [hδ, hϱ, Finset.sum_eq_zero (fun i _ => ex'_betaC _ i)]
    norm_num
  · rw [hinf]
    simp_rw [hbar]
    intro h
    have := tendsto_nhds_unique h tendsto_const_nhds
    norm_num at this

end CSGDMoments

/-! ### Theorem 16: the interchange of `lim_t` and `lim_d` fails under Assumptions 1 and 14 -/

namespace LatePhaseCounterexample

open CSGDMoments

/-- Index type of dimension `d = 2 (n + 1)`: `k = n + 1` dominant and `d - k = n + 1` bulk
directions (block proportion `ρ = 1`). -/
abbrev Idx (n : ℕ) : Type := Fin (n + 1) ⊕ Fin (n + 1)

/-- Two-level spectrum: `λ_i = 2` on the dominant block, `λ_i = 1` on the bulk. -/
noncomputable def P (n : ℕ) : Spec (Idx n) :=
  twoLevel (Fin (n + 1)) (Fin (n + 1)) 0 0 2 1 (by norm_num) (by norm_num)

/-- Isotropic noise with **bounded trace**: `Σ = I / d`, `d = 2 (n + 1)`, so `Tr Σ = 1`. -/
noncomputable def Nz (n : ℕ) : Noise (Idx n) :=
  isoNoise _ (1 / (2 * ((n : ℝ) + 1))) (by positivity)

/-- Initial state `c_{i,0} = 1` for all `i` (so `(1/d) ∑ c_{i,0}² = 1`). -/
def c0 (n : ℕ) : Idx n → ℝ := fun _ => 1

/-- `β_i` on the dominant block. -/
noncomputable def ba (n : ℕ) : ℝ := 1 / (24 * ((n : ℝ) + 1))
/-- `β_i` on the bulk block. -/
noncomputable def bb (n : ℕ) : ℝ := 1 / (14 * ((n : ℝ) + 1))
/-- `𝔼[c_{i,t}²]` on the dominant block. -/
noncomputable def sa (n t : ℕ) : ℝ := (1 / 2) ^ (2 * t) * (1 - ba n) + ba n
/-- `𝔼[c_{i,t}²]` on the bulk block. -/
noncomputable def sb (n t : ℕ) : ℝ := (3 / 4) ^ (2 * t) * (1 - bb n) + bb n

/-- The `d → ∞` limit of the ratio of expected energies at time `t`. -/
noncomputable def L (t : ℕ) : ℝ :=
  4 * (1 / 2) ^ (2 * t) / (4 * (1 / 2) ^ (2 * t) + (3 / 4) ^ (2 * t))

private theorem npos (n : ℕ) : (0 : ℝ) < (n : ℝ) + 1 := by positivity

theorem betaC_inl (n : ℕ) (x : Fin (n + 1)) : (P n).betaC (Nz n) (1 / 4) (Sum.inl x) = ba n := by
  show (1 / 4 : ℝ) * (1 / (2 * ((n : ℝ) + 1))) / (2 * 2 - 1 / 4 * 2 ^ 2) = 1 / (24 * ((n : ℝ) + 1))
  have := (npos n).ne'
  field_simp; ring

theorem betaC_inr (n : ℕ) (y : Fin (n + 1)) : (P n).betaC (Nz n) (1 / 4) (Sum.inr y) = bb n := by
  show (1 / 4 : ℝ) * (1 / (2 * ((n : ℝ) + 1))) / (2 * 1 - 1 / 4 * 1 ^ 2) = 1 / (14 * ((n : ℝ) + 1))
  have := (npos n).ne'
  field_simp; ring

theorem ba_pos (n : ℕ) : 0 < ba n := by unfold ba; have := npos n; positivity
theorem bb_pos (n : ℕ) : 0 < bb n := by unfold bb; have := npos n; positivity

theorem ba_le (n : ℕ) : ba n ≤ 1 / 24 := by
  unfold ba
  have := npos n
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

theorem bb_le (n : ℕ) : bb n ≤ 1 / 14 := by
  unfold bb
  have := npos n
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- `Tr Σ = ∑_i κ_i² = 1` for every `n`: the noise trace is bounded, as in Assumption 1. -/
theorem trace_eq_one (n : ℕ) : ∑ i, (Nz n).kap2 i = 1 := by
  rw [Fintype.sum_sum_type]
  show ∑ _x : Fin (n + 1), (1 / (2 * ((n : ℝ) + 1))) + ∑ _y : Fin (n + 1), (1 / (2 * ((n : ℝ) + 1))) = 1
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have := (npos n).ne'
  push_cast
  field_simp
  ring

theorem expEnergyC_D (n t : ℕ) :
    (P n).expEnergyC (Nz n) (P n).D (1 / 4) (c0 n) t = ((n : ℝ) + 1) * (4 * sa n t) := by
  unfold P
  rw [twoLevel_expEnergyC_D]
  show ∑ _x : Fin (n + 1), (2 : ℝ) ^ 2 * ((1 - 1 / 4 * 2) ^ (2 * t) *
      (1 ^ 2 - 1 / 4 * (1 / (2 * ((n : ℝ) + 1))) / (2 * 2 - 1 / 4 * 2 ^ 2)) +
      1 / 4 * (1 / (2 * ((n : ℝ) + 1))) / (2 * 2 - 1 / 4 * 2 ^ 2)) = _
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have e1 : (1 - 1 / 4 * 2 : ℝ) = 1 / 2 := by norm_num
  have e2 : (1 / 4 : ℝ) * (1 / (2 * ((n : ℝ) + 1))) / (2 * 2 - 1 / 4 * 2 ^ 2) = ba n :=
    betaC_inl n 0
  rw [e1, e2]
  unfold sa
  push_cast
  ring

theorem expEnergyC_univ (n t : ℕ) :
    (P n).expEnergyC (Nz n) Finset.univ (1 / 4) (c0 n) t =
      ((n : ℝ) + 1) * (4 * sa n t) + ((n : ℝ) + 1) * sb n t := by
  unfold P
  rw [twoLevel_expEnergyC_univ]
  show ∑ _x : Fin (n + 1), (2 : ℝ) ^ 2 * ((1 - 1 / 4 * 2) ^ (2 * t) *
      (1 ^ 2 - 1 / 4 * (1 / (2 * ((n : ℝ) + 1))) / (2 * 2 - 1 / 4 * 2 ^ 2)) +
      1 / 4 * (1 / (2 * ((n : ℝ) + 1))) / (2 * 2 - 1 / 4 * 2 ^ 2)) +
    ∑ _y : Fin (n + 1), (1 : ℝ) ^ 2 * ((1 - 1 / 4 * 1) ^ (2 * t) *
      (1 ^ 2 - 1 / 4 * (1 / (2 * ((n : ℝ) + 1))) / (2 * 1 - 1 / 4 * 1 ^ 2)) +
      1 / 4 * (1 / (2 * ((n : ℝ) + 1))) / (2 * 1 - 1 / 4 * 1 ^ 2)) = _
  rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    nsmul_eq_mul]
  have e1 : (1 - 1 / 4 * 2 : ℝ) = 1 / 2 := by norm_num
  have e1' : (1 - 1 / 4 * 1 : ℝ) = 3 / 4 := by norm_num
  have e2 : (1 / 4 : ℝ) * (1 / (2 * ((n : ℝ) + 1))) / (2 * 2 - 1 / 4 * 2 ^ 2) = ba n :=
    betaC_inl n 0
  have e3 : (1 / 4 : ℝ) * (1 / (2 * ((n : ℝ) + 1))) / (2 * 1 - 1 / 4 * 1 ^ 2) = bb n :=
    betaC_inr n 0
  rw [e1, e1', e2, e3]
  unfold sa sb
  push_cast
  ring

theorem sa_pos (n t : ℕ) : 0 < sa n t := by
  unfold sa
  have h1 := ba_pos n
  have h2 := ba_le n
  have h3 : (0 : ℝ) ≤ (1 / 2) ^ (2 * t) := by positivity
  nlinarith [mul_nonneg h3 (by linarith : (0 : ℝ) ≤ 1 - ba n)]

theorem sb_pos (n t : ℕ) : 0 < sb n t := by
  unfold sb
  have h1 := bb_pos n
  have h2 := bb_le n
  have h3 : (0 : ℝ) ≤ (3 / 4) ^ (2 * t) := by positivity
  nlinarith [mul_nonneg h3 (by linarith : (0 : ℝ) ≤ 1 - bb n)]

/-- The ratio of expected energies in dimension `2 (n + 1)` at time `t`. -/
theorem thetaBar_eq (n t : ℕ) :
    (P n).thetaBarCSGD (Nz n) (1 / 4) (c0 n) t = 4 * sa n t / (4 * sa n t + sb n t) := by
  unfold Spec.thetaBarCSGD
  rw [expEnergyC_D, expEnergyC_univ, ← mul_add, mul_div_mul_left _ _ (npos n).ne']

/-- The unnormalised stationary sums of Theorem 16's display are *constant* in `d`:
`∑_𝒟 λ_i² β_i = 1/6` and `∑_i λ_i² β_i = 5/21`.  So both `d → ∞` limits exist and the
right-hand side of Theorem 16 is the well-defined number `7/10`. -/
theorem statEnergyC_D (n : ℕ) : (P n).statEnergyC (Nz n) (P n).D (1 / 4) = 1 / 6 := by
  unfold P
  rw [twoLevel_statEnergyC_D]
  show ∑ _x : Fin (n + 1), (2 : ℝ) ^ 2 *
      (1 / 4 * (1 / (2 * ((n : ℝ) + 1))) / (2 * 2 - 1 / 4 * 2 ^ 2)) = 1 / 6
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have := (npos n).ne'
  push_cast
  field_simp
  ring

theorem statEnergyC_univ (n : ℕ) : (P n).statEnergyC (Nz n) Finset.univ (1 / 4) = 5 / 21 := by
  unfold P
  rw [twoLevel_statEnergyC_univ]
  show ∑ _x : Fin (n + 1), (2 : ℝ) ^ 2 *
      (1 / 4 * (1 / (2 * ((n : ℝ) + 1))) / (2 * 2 - 1 / 4 * 2 ^ 2)) +
    ∑ _y : Fin (n + 1), (1 : ℝ) ^ 2 *
      (1 / 4 * (1 / (2 * ((n : ℝ) + 1))) / (2 * 1 - 1 / 4 * 1 ^ 2)) = 5 / 21
  rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    nsmul_eq_mul]
  have := (npos n).ne'
  push_cast
  field_simp
  ring

/-- `θ_∞ = 7/10` in every dimension. -/
theorem thetaInf_eq (n : ℕ) : (P n).thetaInf (Nz n) (1 / 4) = 7 / 10 := by
  rw [Spec.thetaInf_eq_statEnergyC, statEnergyC_D, statEnergyC_univ]; norm_num

/-- Assumption 14 holds in every dimension. -/
theorem assumption14 (n : ℕ) : (P n).CSGDAssumption (Nz n) (1 / 4) (c0 n) := by
  have hn := npos n
  refine ⟨⟨by norm_num, ?_⟩, ?_, ?_⟩
  · show (1 / 4 : ℝ) < min (2 / 2) (2 * (2 - 1) / (2 ^ 2 - 1 ^ 2))
    norm_num
  · have : ∀ x : Fin (n + 1), (P n).betaC (Nz n) (1 / 4) (Sum.inl x) < c0 n (Sum.inl x) ^ 2 := by
      intro x
      rw [betaC_inl]
      show ba n < 1 ^ 2
      linarith [ba_le n]
    exact (twoLevel_forall_mem_D _ _ _ _ _ _).mpr this
  · rw [Spec.CSGDAssumption.varrho_gt_iff]
    have hψ : (P n).psiD = ((n : ℝ) + 1) * 4 := by
      unfold Spec.psiD P
      rw [twoLevel_sum_D]
      show ∑ _x : Fin (n + 1), (2 : ℝ) ^ 2 = _
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring
    have hδ : (P n).deltaC (Nz n) (1 / 4) = 2 / 5 := by
      unfold Spec.deltaC
      rw [hψ]
      show (1 / (2 * ((n : ℝ) + 1))) * (((n : ℝ) + 1) * 4) * 2 ^ 2 /
        (1 ^ 2 * 2 ^ 2 * (2 * (2 - 1) / (1 / 4) - (2 ^ 2 - 1 ^ 2))) = 2 / 5
      have := hn.ne'
      field_simp
      ring
    have hc : (P n).normSqD (c0 n) = (n : ℝ) + 1 := by
      unfold Spec.normSqD P
      rw [twoLevel_sum_D]
      show ∑ _x : Fin (n + 1), (1 : ℝ) ^ 2 = _
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring
    rw [hδ, hc]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

/-- The block proportion is `ρ = k/(d-k) = 1` in every dimension (Assumption 1). -/
theorem rho_eq_one (n : ℕ) : (P n).rho = 1 := by
  have hk : (P n).kR = (n : ℝ) + 1 := by
    simp [Spec.kR, P, twoLevel]
  have hdk : (P n).dkR = (n : ℝ) + 1 := by
    simp [Spec.dkR, Spec.B, P, twoLevel, Finset.card_compl]
  unfold Spec.rho
  rw [hk, hdk, div_self (npos n).ne']

/-- Block spectral moments (Assumption 1) are constant in `d`:
`(1/k) ∑_𝒟 λ_i^p = 2^p` and `(1/(d-k)) ∑_ℬ λ_i^p = 1` for every `p`. -/
theorem blockMoments (n p : ℕ) :
    (∑ i ∈ (P n).D, (P n).lam i ^ p) / (P n).kR = 2 ^ p ∧
    (∑ i ∈ (P n).B, (P n).lam i ^ p) / (P n).dkR = 1 := by
  have hk : (P n).kR = (n : ℝ) + 1 := by
    simp [Spec.kR, P, twoLevel]
  have hdk : (P n).dkR = (n : ℝ) + 1 := by
    simp [Spec.dkR, Spec.B, P, twoLevel, Finset.card_compl]
  have hn := (npos n).ne'
  constructor
  · rw [hk]
    unfold P
    rw [twoLevel_sum_D]
    show (∑ _x : Fin (n + 1), (2 : ℝ) ^ p) / ((n : ℝ) + 1) = 2 ^ p
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  · rw [hdk]
    unfold P
    rw [twoLevel_sum_B]
    show (∑ _y : Fin (n + 1), (1 : ℝ) ^ p) / ((n : ℝ) + 1) = 1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, one_pow]
    push_cast
    field_simp

/-- Trajectory boundedness (Assumption 1): `𝔼[c_{i,t}²] ≤ 1` for all `i`, `t`, `n`. -/
theorem secondMoment_le_one (n t : ℕ) (i : Idx n) :
    (P n).secondMoment (Nz n) (1 / 4) (c0 n) t i ≤ 1 := by
  have hstab : (1 / 4 : ℝ) < 2 / (P n).lam1 := (assumption14 n).step.lt_stab
  refine ((P n).secondMoment_le_max (Nz n) (by norm_num) hstab (c0 n) t i).trans ?_
  have hc : c0 n i ^ 2 = 1 := by simp [c0]
  rw [hc]
  rcases i with x | y
  · rw [betaC_inl]; exact max_le le_rfl (by linarith [ba_le n])
  · rw [betaC_inr]; exact max_le le_rfl (by linarith [bb_le n])

theorem tendsto_ba : Tendsto ba atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 24 : ℝ)
  rw [mul_zero] at h
  refine h.congr fun n => ?_
  unfold ba
  have := (npos n).ne'
  field_simp

theorem tendsto_bb : Tendsto bb atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 14 : ℝ)
  rw [mul_zero] at h
  refine h.congr fun n => ?_
  unfold bb
  have := (npos n).ne'
  field_simp

/-- For each fixed `t`, the ratio of expected energies converges as `d → ∞` to
`L t = 4 (1/4)^t / (4 (1/4)^t + (9/16)^t)`: the noise floor `β_i = O(1/d)` disappears. -/
theorem tendsto_thetaBar (t : ℕ) :
    Tendsto (fun n => (P n).thetaBarCSGD (Nz n) (1 / 4) (c0 n) t) atTop (𝓝 (L t)) := by
  simp_rw [thetaBar_eq]
  have hsa : Tendsto (fun n => sa n t) atTop (𝓝 ((1 / 2) ^ (2 * t))) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_ba).const_mul
      ((1 / 2 : ℝ) ^ (2 * t)) |>.add tendsto_ba
    simpa [sa] using this
  have hsb : Tendsto (fun n => sb n t) atTop (𝓝 ((3 / 4) ^ (2 * t))) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_bb).const_mul
      ((3 / 4 : ℝ) ^ (2 * t)) |>.add tendsto_bb
    simpa [sb] using this
  have hden : (4 * (1 / 2 : ℝ) ^ (2 * t) + (3 / 4) ^ (2 * t)) ≠ 0 := by positivity
  exact (hsa.const_mul 4).div ((hsa.const_mul 4).add hsb) hden

theorem L_nonneg (t : ℕ) : 0 ≤ L t := by unfold L; positivity

theorem L_le (t : ℕ) : L t ≤ 4 * ((2 / 3 : ℝ) ^ 2) ^ t := by
  unfold L
  have hq : (1 / 2 : ℝ) ^ (2 * t) = (2 / 3) ^ (2 * t) * (3 / 4) ^ (2 * t) := by
    rw [← mul_pow]; norm_num
  have hb : (0 : ℝ) < (3 / 4) ^ (2 * t) := by positivity
  have hr : (0 : ℝ) ≤ (2 / 3) ^ (2 * t) := by positivity
  rw [← pow_mul, hq, div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg hr hr) hb.le, mul_nonneg hr hb.le]

/-- `lim_{t→∞} lim_{d→∞} 𝔼[s_t^𝒟]/𝔼[s_t] = 0`. -/
theorem tendsto_L : Tendsto L atTop (𝓝 0) := by
  have hgeo : Tendsto (fun t : ℕ => 4 * ((2 / 3 : ℝ) ^ 2) ^ t) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := ((2 / 3 : ℝ) ^ 2)) (by positivity)
      (by norm_num)).const_mul (4 : ℝ)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgeo L_nonneg L_le

/-- **Theorem 16 is false as stated (at the level of the ratio of expected energies used in its
own proof).**  For the family `P n` (dimension `d = 2(n+1)`, `ρ = 1`, two-level spectrum
`λ ∈ {2, 1}`, noise `Σ = I/d` with `Tr Σ = 1`, initial state `c_{i,0} = 1`, step size `η = 1/4`):

* Assumption 14 holds for every `n`, and the hypotheses of Assumption 1 hold (`ρ = 1`, constant
  block spectral moments, `Tr Σ = 1 ∈ (0, ∞)`, `𝔼[c_{i,t}²] ≤ 1`);
* the two unnormalised sums in Theorem 16's display are constant in `d`
  (`∑_𝒟 λ_i² β_i = 1/6`, `∑_i λ_i² β_i = 5/21`), so the right-hand side of Theorem 16 is `7/10`;
* yet `lim_{t→∞} lim_{d→∞} 𝔼[s_t^𝒟]/𝔼[s_t] = 0 ≠ 7/10`.

The paper's "uniform convergence" argument for exchanging the limits (tex 2448) is therefore
invalid: `𝔼[c_{i,t}²] → β_i` uniformly in `i`, but `β_i = O(1/d)` while the transient is `O(1)`
per coordinate.  (Compare `late_phase_interchange`, whose uniform-domination hypothesis fails
here: `initExcessC ≍ d` while `statEnergyC = 5/21`.) -/
theorem late_phase_interchange_fails :
    (∀ n, (P n).CSGDAssumption (Nz n) (1 / 4) (c0 n)) ∧
    (∀ n, (P n).rho = 1) ∧
    (∀ n, ∑ i, (Nz n).kap2 i = 1) ∧
    (∀ n t i, (P n).secondMoment (Nz n) (1 / 4) (c0 n) t i ≤ 1) ∧
    (∀ n, (P n).statEnergyC (Nz n) (P n).D (1 / 4) = 1 / 6 ∧
      (P n).statEnergyC (Nz n) Finset.univ (1 / 4) = 5 / 21) ∧
    Tendsto (fun n => (P n).thetaInf (Nz n) (1 / 4)) atTop (𝓝 (7 / 10)) ∧
    (∀ t, Tendsto (fun n => (P n).thetaBarCSGD (Nz n) (1 / 4) (c0 n) t) atTop (𝓝 (L t))) ∧
    Tendsto L atTop (𝓝 0) ∧
    ¬ Tendsto L atTop (𝓝 (7 / 10)) := by
  refine ⟨assumption14, rho_eq_one, trace_eq_one, secondMoment_le_one,
    fun n => ⟨statEnergyC_D n, statEnergyC_univ n⟩, ?_, tendsto_thetaBar, tendsto_L, ?_⟩
  · simp_rw [thetaInf_eq]; exact tendsto_const_nhds
  · intro h
    have := tendsto_nhds_unique h tendsto_L
    norm_num at this

end LatePhaseCounterexample

end SuspiciousAlignment
