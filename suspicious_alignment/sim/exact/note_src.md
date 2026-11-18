# Exact spectral filters versus SGD on Deng-style quadratics — a simulation study

Task key `sim-exact-filters`. Reference paper: Deng, Liao, Ouyang, Pang, Song, Yang, *Suspicious Alignment of SGD:
A Fine-Grained Step Size Condition Analysis* (ALT 2026, arXiv:2601.11789v2); "Thm n" below is the n-th theorem
of the paper's main text (Thm 16 = late-phase alignment, Thm 9/10 = projected updates, Thm 5 = θ*, Thm 7/8 and
Cor. 9 = bounds on η*).

* Code: `sim/exact/` (README with all commands). Raw results: `sim/exact/results/` (JSON summaries, NPZ time
  series, logs). Full-width tables for all nine filters: `sim/exact/results/tables.md` (`make_tables.py`).
  Figures: `sim/exact/figs/*.png` (`make_figures.py`).
* **This file is generated**: `python3 sim/exact/make_note.py` substitutes the tables (computed from the raw
  results) into the prose of `sim/exact/note_src.md`. Edit the source, not this file.
* Everything is numpy / float64 with exact LAPACK SVDs, single thread; total compute 32 CPU-minutes (Section 9).

Notation: `d × n` matrix parameter `W`, loss `L(W) = ½ tr(Wᵀ A W)` (lift M2; `n = 1` is Deng's vector model M1),
Hessian eigenvalues `λ_1 ≥ … ≥ λ_d`, dominant block `D = {1..k}`, bulk `B`, gap `m = λ_k/λ_{k+1}`; stochastic
gradient `G = A W + Ξ`; update `W ← W − η F(G)`, `F(G) = U f(S) Vᵀ`. **θ always denotes Deng's alignment of the
TRUE gradient with the dominant Hessian subspace, `θ = ‖P^D A W‖²_F / ‖A W‖²_F`.** Other alignment notions are
named explicitly (alignment of the stochastic gradient, fraction of the update in `D`, overlap of singular
subspaces).

## 0. Bottom line

1. **Two regimes, and the answer depends on which one the filter input is in.**
   *Noise-dominated input* (singular values of `G` set by the noise; this is the late phase of Deng's own
   experiment, `‖AW‖²/E‖Ξ‖² ≈ 0.02`) with isotropic noise: every exact spectral filter behaves like SGD with a
   rescaled step `η_eff = c·η` (`c` = Stein linear-response coefficient of the filter on pure noise, §1.3). After
   this rescaling all five takeaways (D1)–(D5) carry over *quantitatively*: late alignment = Thm 16 at `η_eff`
   (largest deviation 0.0025 over 9 filters × 6 values of `m`), same critical step, same projected-loss
   thresholds, same Song-et-al. behaviour.
   *Signal-dominated input* (first phase from a large initialisation, noise-free or low-noise runs, large steps):
   the filters differ qualitatively from SGD — the first phase is a long plateau followed by an abrupt collapse,
   the critical step scales like `‖G‖^{1−p}` instead of being pinned near `2/λ_1`, the late state is a limit
   cycle in the top-`n` Hessian directions with alignment `Σ_{i≤k} λ_i^q / Σ_{i≤n} λ_i^q`, `q = 2/(1−p)`
   (above `Σ_D λ²/Σλ²`; SGD's alignment goes to 0 without noise), the window `η_D^loss < η < η_B^loss` is 4–60
   times narrower, and its ordering **reverses** when the dominant block is signal-dominated while the bulk is
   noise-dominated.
2. **Structured noise breaks the SGD-equivalence even in the noise-dominated regime.** With `Σ ∝ A` the noise
   matrix itself has its top singular directions in `D`; the filters damp exactly those directions. Muon's late
   alignment is lower than SGD's (`1 − θ` larger by ×3.2 at `m = 20`, ×8.5 at `m = 100`), in agreement with a
   row-resolved linear-response prediction (to 0.001), not with Thm 16.
3. **Nesterov momentum (β = 0.95, as in `muon.py`) changes the stationary alignment of SGD itself** (0.484
   instead of Thm 16's 0.560 at `m = 5`, below `Σ_D λ/Σλ = 0.527`) and reverses its step-size trend; the filters
   again track the exact SGD + Nesterov value at their `η_eff` (within 0.007).
4. **Song et al.'s phenomenon is reproduced by every filter**: from high-alignment, not-yet-converged states the
   update projected on `D` leaves the loss unchanged over 200 steps (ratio 0.998–1.000) while the bulk-projected
   update reproduces the full update; at twice the step the `D`-projected update raises the loss. For the filters
   the variant "filter the projected gradient" `F(P^D G)` is worse than `P^D F(G)`: its loss threshold is 0.35–0.75
   of the running step, so it *raises* the loss at the running step.
5. **Side finding on the paper**: in the paper's own experimental setup Deng's critical step exceeds `2/λ_1`
   at the early states (`η*_0 = 0.0214–0.0224 > 0.02` for `m ≥ 20`), contradicting Cor. 9 (and Thm 8's bound
   `≈ 1/λ_k`); a 20000-draw Monte-Carlo check confirms that the expected alignment still decreases at
   `η = 0.0205 > 2/λ_1` (§4.5). The lower bound of Thm 7 holds in all 56 probed states.

The plain answers for (D1)–(D5) are in Section 7.

## 1. Setting and protocol

### 1.1 Models and filters

* Spectrum exactly as in the authors' `quad_sim.py`: dominant eigenvalues `linspace(100, 80, k)`, bulk eigenvalues
  `linspace(7, 1, d−k)` rescaled so that the largest is `80/(m + 0.1)`; hence `λ_1 = 100`, `λ_k = 80`,
  `2/λ_1 = 0.02`.
* (M1) `n = 1`, `d = 500`, `k = 50` (Deng's sizes). (M2) `d = 200`, `k = 20`, `n = 50` (so `k < n < d`).
  (M3) `L = ½ tr(Wᵀ A W B)`, `B = diag(j^{−α})`, dominant set = the `K` largest products `λ_i μ_j`.
  All runs are carried out in the eigenbasis of the Hessian factors, which is exact for the filters and the
  noise models used (verified against dense random-`Q` implementations, §1.5).
* Filters (all with an exact SVD of the filter input): SGD `f(s) = s`; Muon `f = 1`; HTMuon `f(s) = s^p`,
  `p ∈ {0.125, 0.25, 0.5}`; Echelon with an exact top-`r` frame, `f = 1` on the top `r` singular directions and
  `f(s) = s/τ` on the rest, `r ∈ {1, k/2, k, 2k} = {1, 10, 20, 40}`. **Tail scale used: `τ = s_{r+1}`, i.e. the
  exact spectral norm of the tail** (so `f` is continuous and ≤ 1); the cheap upper estimate `τ = ‖T‖_F` is
  examined separately in §3.7. The shape factor `max(1, rows/cols)^{1/2} = 2` of `muon.py` is a constant and is
  absorbed in `η`.
* Momentum: none, or the Nesterov form of `muon.py` (`M ← βM + (1−β)G`, filter input `X = (1−β)G + βM`,
  β = 0.95).

### 1.2 Noise, initialisation, recorded quantities

* Noise: iid `N(0, σ²)` on the entries of `G`, `σ = 0.5` as in `quad_sim.py` (per-direction variance matched to
  E0); low-noise `σ = 0.05`; noise-free; anisotropic `Σ ∝ A` (row `i` has variance `σ² λ_i/mean(λ)`, same trace).
* Initialisation: `W_0 ~ N(0, 1)` entrywise (the paper's `x_0 ~ N(0, I)`; "large": loss `≈ 3·10⁴ ×` SGD's noise
  floor), std 3 and 10 ("larger"), std 0.01 and exactly 0 ("small"), and a sample of SGD's stationary law.
* Logged per step (every step for `t < 300`, every 10th afterwards): loss, θ, alignment of the stochastic
  gradient and of the filter input, fraction of the update's squared Frobenius norm in `D`
  (`‖P^D Δ‖²/‖Δ‖²`), top-3 / k-th / (k+1)-th / median / smallest singular value of the filter input and (every
  5th log point) of the true gradient, overlap of the top-`k` left singular subspace of the filter input / true
  gradient with `D` (`‖P^D U_k‖²_F / k`).

### 1.3 Learning rates: the linear-response ("rule") calibration

For pure-noise input `Ξ` and a small signal `S`, Stein's lemma gives `E F(S + Ξ) = c·S + o(S)` with
`c = E⟨Ξ, F(Ξ)⟩ / (σ² d n)` for any bi-orthogonally equivariant `F` and isotropic `Ξ`, while the injected noise
is `E‖F(Ξ)‖²_F = n · E mean_j f(s_j)²`. A filter fed with noise-dominated gradients is therefore SGD with drift
step `η_eff = c η` and a rescaled isotropic noise. The **rule learning rate** is the step that gives SGD's
stationary loss floor at `η_SGD = 0.003`: `η_rule(F) = η_SGD · E⟨Ξ, F(Ξ)⟩ / E‖F(Ξ)‖²_F` (200 Monte-Carlo noise
matrices). Runs use `η = κ · η_rule`; κ = 1 is the "tuned" setting (a), the κ-sweep is setting (b).
(`c` is *not* `E mean_j f(s_j)/s_j`; e.g. for Muon `c = E Σ_j s_j / (σ² d n)`.)

{{T:calib}}

At κ = 1 the achieved late loss is within 1.5 % of SGD's for every filter and every `m` (last column of the
table in §3.2). With Nesterov momentum the rule is evaluated for the averaged filter input, whose noise is
smaller by the factor 0.174 (β = 0.95); this makes the Muon-type learning rates ≈ 5.7× smaller at equal drift.

### 1.4 What was run

| exp. | model, sizes | filters | settings | steps `T` | seeds |
|---|---|---|---|---|---|
| E0 | M1, d=500, k=50 | SGD | η=0.003, σ=0.5, m ∈ {5,10,20,50,100,200,300,400,500} | 30000 | 42, 87 (literal port of `quad_sim.py`, dense `A`); 7 seeds of the paper's list (eigenbasis) |
| E1 two-phase | M2, d=200, k=20, n=50 | 9 | W0~N(0,1), κ=1, m ∈ {5,20,100,500} | 3000 | 3 |
| E1 late | M2 | 9 | zero init, κ=1, m ∈ {5,10,20,50,100,200} | 800–5000 (≥ 2.7 slowest time constants) | 3 (m<100), 2 |
| E1 sweep | M2 | 9 | W0~N(0,1), m=20, κ ∈ {¼,½,2,4,8,16} | 2000 | 2 |
| E1 signal | M2 | 9 | noise-free (W0 std 0.01), and σ=0.5 with κ=16 (zero init); m ∈ {5,20,100} | 1500 | 2 |
| E1 low noise | M2 | 7 | σ=0.05 with the σ=0.5 learning rates, m ∈ {20,100} | 2000 | 2 |
| E1 larger init | M2 | 5 (+1) | W0 std 3 (and 10 for Muon), m=20 | 5000 (14000) | 1 |
| E1 momentum | M2 | 7 | β=0.95: zero init m ∈ {5,20,100}; W0~N(0,1) m=20 at two learning rates; noise-free | 800–6000 (9000) | 2 (1) |
| E1 n=1 | M1, d=500, k=50 | 5 | Deng's protocol, m as in E0; κ-sweep at m=20; noise-free | 30000 | 4; 2; 2 |
| E1 limit cycles | M2 with n ∈ {1,5,20,50,100,200} | Muon, HT | noise-free | 2000 | 1 |
| E2/E3 one-step | M2 | 9 | 468 states = 36 E1 two-phase runs × 13 checkpoints; 48 (SGD trajectory) / 32 (own trajectory) antithetic noise draws per state; plus constructed states (§4.3–4.4, §5.2) | – | checkpoints of seed 0 |
| E2 bounds | M1, d=500, k=50 | SGD | closed forms at 56 states; 20000-draw MC at one | 30000 | 42, 87 |
| E3 continuation | M2 | 7 | 8 checkpoints × 5 update variants (+3 at 2η) | 200 | 2 noise seeds |
| E4 | M2 with Σ∝A; M3 (α=0.5, K=1000; α=1, K=500) | 7 | m ∈ {20,100}: large-init and zero-init runs + one-step statistics | 2000; 800–2500 | 2 |

"9 filters" = SGD, Muon, HT p ∈ {.125,.25,.5}, Echelon r ∈ {1,10,20,40}; "7" drops HT .25 and Echelon 10.
Reported spreads are standard deviations over seeds of per-seed time averages (late window = last 20 % of the
run unless stated). Scaled down relative to the paper: `d = 200` instead of 500 and `T ≤ 5000` in the matrix
runs (an exact SVD per step); E0 and the `n = 1` runs use the paper's `d`, `k`, `T`.

### 1.5 Validation of the code (`tests_sanity.py`, all pass)

Filters against their definitions (Muon = polar factor; HT = `polar(X)(XᵀX)^{p/2}` — the code path of
`msign_generalized_ht_v2`; Echelon = `U_r polar(U_rᵀX) + T/‖T‖_2` and `‖T‖_2 = s_{r+1}`) to 1e-11; eigenbasis runs
against dense runs with a random orthogonal eigenbasis for M2 and M3 (θ and final iterate to 1e-9); exact scale
covariance `(η, σ, W_0) → (a^{1−p}η, aσ, aW_0)`; Monte-Carlo one-step estimators against Deng's closed forms for
η* and `η_S^loss` (within 5 s.e.); stationarity of SGD started in its stationary law.

## 2. E0 — replication of Deng's experiment

{{T:e0}}

* The two-phase curve is reproduced for every `m` (θ drops from 0.91–1.00 to its minimum within 24–200 steps,
  then rises; Figure `figs/e0_baseline.png`), and E[Alignment] increases monotonically with `m` towards 1 while
  its within-run standard deviation decreases — the paper's Figures 2–3.
* **Thm 16 is quantitatively accurate**: E[Alignment] is 0.0006–0.0037 *below* `θ_∞` (the gap is largest at
  small `m`). The gap is not a seed effect (sd over seeds ≤ 0.0017); it is the difference between the time
  average of the ratio `θ_t` and the ratio of expectations that Thm 16 computes (a finite-`d` effect; in the
  `d × n` runs of §3.2, with 50× more coordinates, the gap is ≤ 0.0007).
* `θ_∞` lies slightly above `Σ_D λ/Σλ` (its `η → 0` limit) and far below `Σ_D λ²/Σλ²`.
* For `m ≥ 300` the run is not fully stationary at `T = 30000` (slowest time constant 4400–7300 steps); the exact
  finite-`T` value differs from `θ_∞` by ≤ 0.0004.
* The literal port (dense `A = QΛQᵀ`, legacy RNG, same call order as `quad_sim.py`) and the eigenbasis runs agree
  within the seed spread.

## 3. E1 — trajectories of the exact filters

### 3.1 The two-phase curve survives, with a different first phase

{{T:twophase}}

Figure `figs/e1_twophase.png` (θ, loss, update fraction in `D`; all nine filters, four gaps);
`figs/e1_diagnostics_m20.png` (singular values, overlaps).

* **Every filter shows the two-phase curve** (decrease to a minimum of 0.000–0.004 at `m ≤ 20`, then a rise).
* The first phase is different in kind. SGD's alignment decays immediately (minimum at `t ≈ 24–35` for every
  `m`, set by `1/(ηλ_D)`). Under Muon / HTMuon / Echelon θ stays at its initial value for hundreds of steps
  (0.99 at `t = 200` for Muon, `m = 20`) and then collapses within a few dozen steps: the dominant block is
  signal-dominated, the filter moves every singular direction at (nearly) constant speed, so the time to reach
  the noise floor is `∝ ‖W_0‖^{1−p}/η` and does not depend on `λ_D` — minimum at `t = 610` (Muon), 380
  (`p = .125`), 236 (`p = .25`), 103 (`p = .5`) at `m = 20`.
* During that plateau the *update* is much less aligned than the gradient: fraction of `‖Δ‖²` in `D` = 0.40
  (Muon, `= k/n`), 0.58 (`p = .125`), 0.92 (`p = .5`), 0.99 (Echelon `r = 1`), against θ = 0.99 for the true
  gradient and for SGD's update.
* At `m = 20` and `m = 5` all filters reach the same late alignment as SGD within 0.005. At `m = 100, 500` the
  runs are **not stationary at `T = 3000`** (slowest time constants 1460 and 7300 steps): the "late" values in
  the table are transients, and the filters lag behind SGD by the length of their first phase. The stationary
  comparison is §3.2.

### 3.2 Late-time alignment versus `m` in the noise-dominated regime

Zero initialisation (so that only the stationary state is probed), κ = 1, time average over the last 20 % of
each run. Figure `figs/e1_late_vs_m.png`.

{{T:late}}

* **Late alignment as a function of `m`: identical for all filters, and equal to Thm 16 evaluated at the
  filter's drift-equivalent step `η_eff`** — the largest deviation over all filters and gaps is 0.0025, of the
  order of the seed spread. Hence, like SGD's, it sits slightly above `Σ_D λ/Σλ` and far below `Σ_D λ²/Σλ²`,
  and tends to 1 as `m → ∞` at the same rate.
* Cross-check started from SGD's exact stationary law (`m = 100, 200`, T = 1500, 2 seeds; table T1j of
  `tables.md`): SGD 0.9618, Muon 0.9609, HT `.125` 0.9610, Echelon `r = k` 0.9614 at `m = 100` (Thm 16: 0.9620).

Diagnostics of that late phase at `m = 20`:

{{T:late_diag}}

* The phase is strongly noise-dominated (`‖AW‖²/E‖Ξ‖² ≈ 0.02`; the singular values of `G` are those of the
  noise, `σ(√d ± √n)` = 3.5…10.6, far above those of the true gradient).
* **The alignment that is high is the alignment of the TRUE gradient (0.83). The stochastic gradient that the
  optimizer sees is not aligned at all (0.113 ≈ k/d + signal share), nor is its top-`k` singular subspace
  (overlap 0.117 vs. 0.88 for the true gradient), nor is the update of any filter (0.109–0.113).** This is why
  the filters cannot act on the alignment: there is no spectral structure in their input to act on.

The vector model `n = 1` (where Muon is normalised SGD and HTMuon rescales the step by `|g|^{p−1}`) in Deng's
exact protocol (`d = 500`, `k = 50`, `T = 30000`, E[Align] over the last 10000 steps) gives the same picture —
Figure `figs/e1_n1.png`:

{{T:n1}}

(In the last table the `m = 100`, `p = .5` entry is a floating-point artefact, see §8.)

### 3.3 Learning-rate sweep (m = 20, W0 ~ N(0,1), T = 2000)

Cell: late θ (late loss; top singular value of `AW` / top singular value of `G`; fraction of update in `D`).

{{T:sweep}}

Figure `figs/e1_sweep.png`.

* κ = 1, 2, 4 (noise-dominated): all filters follow the SGD trend — θ increases with the step, as Thm 16
  predicts (the filters lag slightly at κ = 4: 0.882–0.898 vs. 0.905, the input is no longer strongly
  noise-dominated).
* κ = 8, 16: SGD diverges (`ηλ_1 = 2.4, 4.8`); the filters do not (their update is bounded) and enter a
  **signal-dominated late phase**: the true gradient carries 69–97 % of the top singular value of `G`, θ rises
  to 0.93–0.995 (above `Σ_D λ/Σλ = 0.81`, approaching and for `p = .5` exceeding `Σ_D λ²/Σλ² = 0.993`), the
  update fraction in `D` rises to 0.33–0.74 and the top-`k` singular subspace of `G` aligns with `D`
  (overlap 0.79–0.96, table T1c of `tables.md`).
* κ = ¼, ½: **not converged at `T = 2000`** for any optimizer (the first phase of the filters lasts `≈ 610/κ`
  steps; SGD's bulk needs `1/(2ηλ_d) ≈ 1170` steps at κ = ¼). These columns are transients and say nothing
  about stationary alignment.

### 3.4 Signal-dominated late phase: limit cycles

Cell: late θ (fraction of update in `D`); T = 1500, 2 seeds.

{{T:signal}}

* Noise-free SGD converges and its alignment goes to **0** (the gradient ends up in the slowest bulk
  direction). The Muon-type filters cannot converge with a constant step; they settle on a limit cycle whose
  true gradient is almost entirely in `D`: θ = 0.963–0.9997 (Muon), 0.977–1.000 (`p = .125`), above
  `Σ_D λ²/Σλ²`.
* **Prediction (commuting model of `notes/research/filter_spec.md`)**: on the 2-cycle `c_i → −c_i` of a
  direction with Hessian eigenvalue `λ_i`, `η f(λ_i|c_i|) = 2|c_i|`, hence `|g_i| = λ_i|c_i| ∝ λ_i^{1/(1−p)}`;
  a rank-`n` update can sustain only `n` such directions and selects the top `n`; so
  `θ = Σ_{i≤k} λ_i^q / Σ_{i≤min(n,d)} λ_i^q`, `q = 2/(1−p)`. Measured versus predicted for several `n`:

{{T:limit}}

  The prediction is exact to 5 digits for HTMuon and within 0.001 for Muon (whose 2-cycle is only marginally
  stable); the gradient energy outside the top-`n` Hessian directions is zero to machine precision. For `n ≤ k`
  the alignment is exactly 1.
* With noise but a large step (κ = 16) the late alignment (0.89–0.98 at `m = 5`) lies between Thm 16 and the
  limit-cycle value.
* Low noise (`σ = 0.05`, learning rates of the `σ = 0.5` setting, W0 ~ N(0,1), T = 2000) puts the filters in an
  intermediate regime — their step, tuned for `σ = 0.5`, is 10^{1−p} times too large for the smaller noise:

{{T:lownoise}}

  The filters' late alignment (0.93–0.97 at `m = 20`) is far above Thm 16 at their `η_eff` (0.83) and their loss
  floor is set by the step, not by the noise. (The SGD rows are transients: at `σ = 0.05` SGD has not reached
  its floor of 0.019 at `T = 2000`.)

### 3.5 Initialisation scale

{{T:largeinit}}

The two-phase shape and the late value do not depend on the initialisation scale; only the length of the first
phase does: SGD's minimum stays at `t = 35`, Muon's moves from 610 (std 1) to 1870 (std 3) and 6410 (std 10),
i.e. linearly in `‖W_0‖` (`p = .125`: 380 → 1010, `∝ ‖W_0‖^{0.875}` gives 990). Small initialisations (std 0.01
and zero) are the "late" and "signal" runs above: the first phase is absent and θ rises monotonically.
(An earlier std-10 attempt with T = 6000, kept in `e1_lownoise.json`, was too short for Muon and HT `.125` and
is not used.)

### 3.6 Nesterov momentum β = 0.95

Late-time alignment from zero initialisation at the drift-matched learning rate; in parentheses the exact value
for SGD with the same Nesterov momentum at the filter's `η_eff` (2×2 Lyapunov recursion per eigen-direction,
`Problem.sgd_nesterov_theta`, validated against simulation):

{{T:momentum_late}}

* **Momentum changes the reference**: SGD + Nesterov has a *lower* stationary alignment than Thm 16 (0.484 vs.
  0.560 at `m = 5`; 0.784 vs. 0.835 at `m = 20`), even below `Σ_D λ/Σλ` — the look-ahead term damps the
  high-curvature directions more.
* The filters again agree with the SGD(+Nesterov) value at their `η_eff`, within 0.003–0.007 (the residual is
  positive for all filters including SGD, i.e. mostly the time-average-versus-ratio-of-expectations bias and
  finite `T`).

Large-initialisation runs (`m = 20`), Figure `figs/e1_momentum.png`:

{{T:momentum_runs}}

* The two-phase curve persists. At the drift-matched learning rate the first phase of the Muon-type filters is
  5.7× longer (minimum at `t = 3500` instead of 610), and **Muon and the Echelon variants have not finished the
  rise at `T = 6000`** (their "final" values in the table are transients). Single-seed runs to `T = 9000`
  (table in §3.5) end at 0.784 (Muon) and 0.781 (Echelon `r = k`), the SGD + Nesterov value.
* If momentum is simply switched on at the momentum-free learning rate (what one does in practice), the drift
  step is 2.4–5.7× larger and the late alignment *drops* to 0.69–0.75, in agreement with the exact
  SGD + Nesterov value at that `η_eff` (0.69–0.75) and opposite to the momentum-free Thm 16, which would
  predict an increase to 0.87–0.95. With Nesterov momentum the stationary alignment decreases with the step.
* Noise-free with momentum (T = 1500): Muon 0.9987, HT `.125` 0.9990, HT `.5` 1.0000, SGD 0 — the limit-cycle
  picture of §3.4 is unchanged.

### 3.7 Echelon: which tail scale?

The study uses the exact `τ = ‖T‖_2 = s_{r+1}`. The cheap upper estimate `τ = ‖T‖_F` down-weights the tail by
`‖T‖_2/‖T‖_F` (≈ 1/5 for a noise tail here), so the update is dominated by the rank-`r` polar head:

{{T:echfrob}}

* Qualitatively nothing changes (two-phase curve, limit cycle, window at the 'rise' state).
* Quantitatively the Frobenius-scaled variant with small `r` is **not** captured by the linear-response
  picture: its late alignment is 0.011–0.012 above the SGD formula at its `η_eff` for `r = 1, 10` (seed sd
  0.0005–0.003), 0.005 for `r = k`; the head — the top singular directions of signal + noise — is a strongly
  non-linear function of the signal. For `r = 2k` the two variants coincide.
* In the signal-dominated initial state the Frobenius variant with `r ≤ k` is closer to SGD (ratio
  `η_D^loss/η_B^loss` = 0.10 instead of 0.39 at `r = k`, `m = 20`; no reversal at `m = 500` for `r ≤ k`).

## 4. E2 — one-step alignment response (D1–D3)

### 4.1 Method

At a state `W` and for `N` noise draws (antithetic pairs, common random numbers across filters) one SVD gives
`Δ = F(G)` for all filters. Because `θ(W − ηΔ)` is a ratio of two quadratics in `η`, the per-draw coefficients
give the whole curve `η ↦ E[θ(W − ηF(G))] − θ(W)` exactly, without a grid in `η`. We report (i) the regime and
root of the ratio-of-expectations response (the generalisation of Deng's `η* = −q_t/p_t`: with
`a_S = ‖P^S AW‖²`, `b_S = E⟨P^S AW, P^S AΔ⟩`, `c_S = E‖P^S AΔ‖²`, `η*_F = 2(a_B b_D − a_D b_B)/(a_B c_D − a_D c_B)`),
with bootstrap standard errors, and (ii) the first sign change of the directly averaged ratio on a 66-point
grid. The two agree within 1–3 % at every state checked (table T2c of `tables.md`; e.g. Muon at `t = 0`:
10.7 vs. 10.5; at `t = 3000`: 0.0203 vs. 0.0206), so the `d → ∞` idealisation of the paper is harmless at these
sizes. For SGD the Monte-Carlo root reproduces Deng's closed form (0.0212 vs. 0.0212; 0.00294 vs. 0.00294).
Regimes: **↓↑ x** = decrease for `η < x`, increase above (Deng's low-alignment behaviour); **↓ all** = decrease
for every step; **↑↓ x** = increase below `x`, decrease above.

### 4.2 Along the trajectories: Deng's dichotomy holds for every filter, with a different critical step

Regime counts over all states probed on E1 trajectories (36 runs × 13 checkpoints, `m ∈ {5, 20, 100, 500}`):

{{T:e2_regimes}}

All filters at the same states (SGD's trajectory, `m = 20`; raw critical steps):

{{T:e2_sgdtraj}}

Each filter on its own trajectory — critical step relative to the step actually used:

{{T:e2_owntraj}}

Figure `figs/e2_alignment_response.png`.

* **(D1) survives on trajectories**: at each of the 468 states and for each filter evaluated there, the expected
  alignment decreases below a critical step and increases above it. The measured expected change at the running
  step has the corresponding sign (table T2b of `tables.md`).
* **The critical value is filter-specific.** In the noise-dominated states (`t ≥ 400` on SGD's trajectory) the
  filters' critical steps are SGD's divided by `c`: e.g. at `t = 3000` Muon 0.0206 = 0.00282/c, HT `.125`
  0.0163 = 0.00285/c, against Deng's 0.00294 (in SGD-norm units 0.00289). In the signal-dominated states
  (`t ≤ 10`) they are 25–900 times larger than SGD's (Muon 10.5 vs. 0.0212 at `t = 0`) and unrelated to `2/λ_1`.
* **Why the first phase is a plateau**: on its own trajectory SGD runs at `η*/7` during the first phase, so θ
  decays at an `O(1)` rate per step (−0.006, −0.034, −0.092 per step at `t = 0, 3, 10`); Muon runs at `η*/500`
  and its θ changes by −2·10⁻⁵ per step.
* **Late phase: `η*_t/η_run = 0.93–1.04` for every filter** — the stationary state is self-consistently the
  state whose critical step equals the running step (the expected alignment change vanishes at stationarity).
  Deng's picture "η below η* in phase I, alignment rises once η* has dropped to η" is therefore reproduced by
  all filters; what differs is how long η* stays far above η.

### 4.3 Scaling of the critical step with the gradient norm and with `m`

State `γ·W` with the noise fixed (`σ = 0.5`); fitted exponents `d log η* / d log γ`:

{{T:e2_scale}}

Raw critical steps at `γ·W_0` (SGD trajectory `t = 0`, `m = 20`):

{{T:e2_scale_rows}}

* **Signal-dominated: `η*_F ∝ ‖G‖^{1−p}`** (exact homogeneity of the filter), i.e. constant for SGD
  (`≈ 2/(λ_D + λ_B)`), linear in the gradient norm for Muon and Echelon, exponent 0.875 / 0.5 for HTMuon.
  For Muon-type filters the critical step is not a property of the Hessian.
* **Noise-dominated and far below the noise floor: `η* ∝ ‖G‖²` for all filters including SGD** (the denominator
  of `η*` is dominated by the noise terms `s^B e_D − s^D e_B`).

Dependence on `m` at two states constructed identically for every `m` (same Gaussian `Z`): 'init' = `W = Z`;
'rise' = a typical SGD state at the first time the expected alignment has recovered to `0.75 θ_∞`
(high alignment, bulk not converged):

{{T:e2_mdep}}

* The critical step is nearly independent of `m` for every filter (SGD: 0.0194 → 0.0218 at 'init',
  ≈ `2/(λ_1 + λ_{k+1})`…`2/(λ_k+λ_d)`; Muon: 10.0 → 14.4; at 'rise' all filters within 3 % across `m`).
  `m` controls the *alignment band* (θ*, `θ_∞`), not the critical step.

### 4.4 (D2): states above the stationary band

Base state: a sample of SGD's stationary law at `η = 0.003` (θ ≈ θ_∞). 'bulk × g': bulk rows scaled by `g`
(dominant block at its noise floor, less bulk). 'D × g': dominant rows scaled by `g` (dominant block
signal-dominated, bulk at the noise floor). 48 draws.

{{T:highalign}}

* **Noise-dominated high-alignment states ('bulk × g'): (D2) holds for all filters, with the same threshold.**
  SGD and every filter switch to "decrease for every step" at the same state (between `g = 0.5` and `0.3` at
  `m = 5`; between 0.3 and 0.1 at `m = 20`; below 0.1 at `m = 100`), which is where θ crosses Deng's θ*
  (0.918, 0.994, 0.9998) — θ* is a sufficient threshold and it is close to sharp here. At `g = 0` (θ = 1) every
  step of every filter lowers the alignment, trivially.
* **Signal-dominated dominant block ('D × g'): the filters leave Deng's pattern.** SGD keeps a finite critical
  step (0.13, 0.027, 0.023 at `g = 100`). Muon, HTMuon and Echelon `r ≥ k` either decrease the alignment for
  *every* step although θ < θ* (e.g. `m = 20`, `g = 100`: θ = 0.999979 < θ* = 0.999996; `m = 5`, `g = 10`:
  θ = 0.9918 < θ* = 0.9946), or show the **reversed dichotomy** (`m = 5`, `g = 100`): the expected alignment
  *increases* for `η < η*` and decreases above (Muon `η* = 0.0072 ± 0.0001`, HT `.125` 0.0012, Echelon `r = k`
  0.0043; the directly averaged ratio has the same sign pattern and root, e.g. 0.00712 for Muon). This is the
  "curvature ordering reversed" case of `filter_spec.md` (§1.8): under Muon the effective curvature of a
  direction is `f(σ)/|c|`, small for the large dominant coefficients, so at small steps the bulk gradient
  decays relatively faster. It cannot happen for SGD.
* Such states (dominant block far above its floor while the bulk is at its floor) were **not visited by any of
  the 36 trajectories** from isotropic initialisation, where the dominant block reaches its floor first.

### 4.5 (D3): Deng's bounds on η* in the paper's own setup

Closed-form `η*_t` (Eq. (def-etatstar-body)) along SGD trajectories of the vector model (`d = 500`, `k = 50`,
`σ = 0.5`, `η = 0.003`; seed 42 shown, seed 87 in `results/e2_etastar_bounds.log`):

{{T:bounds}}

{{T:bounds_count}}

Monte-Carlo check at the initial state (`m = 20`, seed 42; closed form `η*_0 = 0.021365`, `2/λ_1 = 0.02`):

{{T:bounds_mc}}

* The lower bound of Thm 7 holds everywhere (it is loose by 1.5× in the early states and by 10–1000× later).
  The main-text approximation `η* ≳ 2 gap_1/(λ_1² − λ_d²)` (0.0152 at `m = 20`) is consistent with the early
  states.
* **The upper bound `η* ≤ 2/λ_1` (Cor. 9) fails** at the early states for `m ≥ 20`, and Thm 8's bound
  `(λ_1 − λ_d)/(λ_kλ_1 − λ_{k+1}λ_d) ≈ 1/λ_k` fails at all early states, although the hypothesis
  `θ_t ≥ e_B/(e_B + e_D)` holds. The expected alignment still *decreases* at `η = 0.0205 > 2/λ_1`
  (−1.778·10⁻³ ± 5·10⁻⁹) and changes sign exactly at the closed-form `η*`. Reading the proof (Appendix,
  proof of Thm 8), `−q_t` is written without the factor 2 of the definition `η* = −q_t/p_t`, and the lower
  bound on `p_t` uses `Σ_D λ⁴c² ≥ λ_kλ_1 s^D` and `Σ_B λ⁴c² ≤ λ_{k+1}λ_d s^B`, whereas only `λ_k² s^D` and
  `λ_{k+1}² s^B` are available. All measured early values lie inside the noise-free sandwich
  `2/(λ_1+λ_{k+1}) ≤ η* ≤ 2/(λ_k+λ_d)` of `filter_spec.md` (§1.9), whose upper end exceeds `2/λ_1` whenever
  `λ_k + λ_d < λ_1`.
* In the late phase `η*_t` fluctuates around the running step 0.003 (0.0023–0.0042), cf. §4.2.

## 5. E3 — projected updates (D4, Song et al.)

Thresholds: `η_S^loss = 2 E⟨AW, P^S Δ⟩ / E⟨P^S Δ, A P^S Δ⟩` (expected one-step loss change of the projected
update is negative iff `η < η_S^loss`; exact, since the loss change is quadratic in `η`). For SGD the
Monte-Carlo values reproduce Thm 9 (e.g. 0.022/0.646 at `t = 0`, 0.00296/0.00303 at `t = 3000`, `m = 20`).
Two ways of projecting are compared: `P^S F(G)` (project the update) and `F(P^S G)` (filter the projected
gradient); they coincide for SGD.

### 5.1 Thresholds along each filter's own trajectory

Cell: `η_D^loss/η_run` / `η_B^loss/η_run` for `P^S F(G)` / `η_D^loss/η_run` for `F(P^D G)`. Bold: ordering reversed
(`η_D^loss > η_B^loss`).

{{T:e3_own}}

Figure `figs/e3_loss_thresholds.png`.

* **Late phase, all filters: `η_D^loss/η_run = 0.93–1.05`, `η_B^loss/η_run ≫ 1` until the bulk has converged**
  (e.g. `m = 100`, `t = 2000`: 9.2 for SGD, 17.9 for Muon; `m = 500`, `t = 3000`: 40 and 50). The dominant block
  sits at its stationary level, where its loss threshold *equals* the running step (for SGD exactly: with the
  stationary second moment `β_i`, `2λ_iβ_i/(λ_i²β_i + κ_i²) = η` for every direction). So the running step is at
  the lower edge of Deng's window `[η_D^loss, η_B^loss]`: the `D`-projected update neither lowers nor raises
  the loss on average, any larger step raises it, and the bulk-projected update lowers it. At full
  stationarity both thresholds equal the running step (ratio 0.96–0.99) — the stationary alignment sits at
  Deng's critical alignment θ^crit (0.8345 vs. θ = 0.828–0.832 at `m = 20`).
* **First phase of the filters (signal-dominated): both thresholds are 100–1000× the running step** — both
  projected updates lower the loss, and the window is much narrower than SGD's (§5.2).
* **`F(P^D G)` has a smaller threshold than `P^D F(G)`** for every filter in the noise-dominated phase:
  0.48–0.50 (Muon), 0.55–0.58 (`p = .125`), 0.72–0.75 (`p = .5`), 0.41–0.43 (Echelon `r = k`) of the running
  step. Filtering the `k × n` projected noise produces an update whose rows are `d/n`-fold larger in squared
  norm than the `D`-rows of `F(G)` (Muon), while the drift coefficient only doubles.

### 5.2 Width of the window versus `m` and `p`; reversal

Ratio `η_D^loss/η_B^loss` for `P^S F(G)` at the two constructed states of §4.3 (bold: > 1):

{{T:e3_mdep}}

The same for `F(P^S G)`; in parentheses the threshold ratio `η_D^loss[F(P^D G)] / η_D^loss[P^D F(G)]`:

{{T:e3_mdep_gp}}

* **'rise' (noise-dominated, high alignment, not converged — the Song et al. situation): the window is the same
  for all filters and all `p`** (within 2 % of SGD's): `η_D^loss/η_B^loss` = 0.58, 0.35, 0.10, 0.023 at
  `m = 5, 20, 100, 500`. Its relative width grows roughly like `m`. θ is well below θ^crit in all rows.
* **'init' (signal-dominated): the window depends strongly on the filter.** For SGD the ratio is
  `≈ λ̄_B/λ̄_D ∝ 1/m` (0.13 → 0.012). For the Muon-type filters it is `O(1)`: 0.54–0.73 for Muon, and monotone
  in `p` at fixed `m` (m = 20: 0.034 SGD, 0.13 `p = .5`, 0.28 `p = .25`, 0.40 `p = .125`, 0.57 Muon). Echelon
  interpolates in `r`: `r = 1` and `k/2` behave like SGD (0.035, 0.043; the tail carries the bulk),
  `r = k` and `2k` like HT `.125` and Muon.
* **The ordering reverses** (`η_B^loss < η_D^loss`: the *bulk*-projected update becomes loss-increasing first)
  for Muon and Echelon `r = 2k` at `m = 200`, and for Muon, HT `.125`, Echelon `r = k, 2k` at `m = 500`
  (ratios 1.35–2.35). Along the E1 trajectories: {{T:e3_reversals}}
* **The reversal is a noise effect on the bulk block**, not a property of the filter on clean gradients:

{{T:reversal_noise}}

  Noise-free, Muon's ratio is 0.57–0.59 for every `m` (its thresholds do not depend on the Hessian gap at
  all), HT `.125` 0.28–0.39. The ratio exceeds 1 once the bulk block of the gradient is noise-dominated
  (bulk signal/noise ≤ 0.25) while the dominant block is still signal-dominated: the filter gives the bulk
  noise directions the same weight as the dominant signal directions, so the bulk-projected update is mostly
  noise. In that phase both thresholds are still hundreds of running steps away.
* Near stationarity the ratio fluctuates around 1 by a few percent (state fluctuations around θ^crit); those
  "reversals" (within 10 %) occur for SGD as well and are Deng's θ > θ^crit case.

### 5.3 Continuation runs

From checkpoints of each optimizer's own two-phase run (seed 0), 200 further steps at its own learning rate,
2 fresh noise seeds; entries are `L(t0 + 200)/L(t0)` (mean of the last 10 logged steps). The last two columns
use twice the running step.

{{T:e3_continue}}

Figure `figs/e3_continuation.png`.

* **High alignment, noise-dominated, not converged** (`m = 100`: `t0 = 2000, 3000`; `m = 500`: `t0 = 3000`;
  `m = 20`: `t0 = 1500`; θ = 0.55–0.90, loss 1.3–50× the final loss, 0.2–9 % of it in `D`): for **every**
  filter the `D`-projected update leaves the loss unchanged (0.998–1.000) and the bulk-projected update gives
  the full decrease (within 0.002). At `2η` the `D`-projected update raises the loss (1.005–1.12) while the
  bulk-projected one still lowers it — the running step is at the lower edge of the window. (Exception: the
  two nearly converged `m = 20`, `t0 = 1500` states of SGD and HT `.5`, where doubling the step raises the
  noise floor of the bulk as well.)
* **`F(P^D G)` raises the loss at the running step** for the filters (1.02–1.52 at `m = 20`; 1.003–1.08 at
  `m = 100`; 1.001–1.005 at `m = 500`), in line with its threshold of 0.35–0.75 running steps.
* **High alignment, signal-dominated** (first-phase checkpoints of the filters, θ = 0.96–1.00): the opposite —
  the `D`-projected update does almost all of the work (`m = 500`, `t0 = 200`, Muon: 0.118 vs. 0.115 for the
  full update, bulk-projected 0.997). High alignment of the true gradient is "suspicious" only when the
  dominant block is at its noise floor.

## 6. E4 — robustness

### 6.1 Anisotropic noise `Σ ∝ A` (M2)

{{T:e4_aniso}}

Figure `figs/e4_robustness.png` (top row).

* The two-phase curve persists (with the plateau-and-collapse first phase for the filters).
* **The filters are no longer SGD-equivalent.** SGD follows Thm 16 with `κ_i² ∝ λ_i` (0.9941 at `m = 20`). Muon
  ends at 0.9811, HT `.125` at 0.9838, Echelon `r = k` at 0.9865: the bulk share `1 − θ` of the gradient
  energy is 3.2×, 2.7×, 2.3× SGD's (m = 100: 8.5×, 6.5×, 6×). Echelon `r = 1` stays at SGD's value.
* Mechanism: the noise variance of the dominant rows is 40× (m = 20) / 197× (m = 100) that of the bulk rows, so
  the top singular directions *of the noise* lie in `D` — the stochastic gradient itself is aligned
  (0.83 / 0.96) — and the filter flattens them. Row-resolved calibration (`extra_checks.py`): Muon compresses
  the injected-noise ratio `ν_D/ν_B` from 40 to 5.0 and makes the drift coefficient 2.7× larger on bulk rows.
  The resulting prediction `E‖w_i‖² ∝ η ν_i / (c_i λ_i (2 − η c_i λ_i))` matches the simulation to 0.001
  (column "row-resolved linear-response prediction"), whereas the scalar-rescaled SGD formula does not.
* The update is far less aligned than the gradient it is computed from: fraction in `D` 0.36 (Muon), 0.43
  (`p = .125`) versus 0.83 for SGD.
* A by-product: at the rule learning rate the filters converge faster in the bulk (`m = 100`, `T = 2000`: loss
  3.0 for Muon vs. 39 for SGD), because of the larger bulk drift coefficient.

### 6.2 Kronecker lift (M3), isotropic noise

Cell: zero-init late θ (exact SGD value at `η_eff`, computed from the Kronecker eigenvalues `λ_iμ_j`);
large-init `θ_min @ t`.

{{T:e4_kron}}

* With isotropic noise the SGD-equivalence holds for the Kronecker Hessian as well: late alignment within
  0.003 of the exact SGD value for all filters, both when the dominant set is a set of rows (α = 0.5,
  K = 1000) and when it is a staircase of entries without a spectral gap (α = 1, K = 500).
* The two-phase curve persists. The large-init runs are far from stationary at `T = 2000` (the small
  eigenvalues of `B` make the bulk slow), so no late values are quoted for them (Figure `figs/e4_robustness.png`).

### 6.3 One-step statistics in the E4 settings

Cell: θ; alignment-response regime and `η*/η_run`; `η_D^loss/η_B^loss` (bold: > 1).

{{T:e4_onestep}}

Deng's dichotomy (↓↑) holds at all E4 states for all filters; `η*/η_run ≈ 0.83–1.0` in the late states; the
window is narrow for the Muon-type filters at the initial state and reverses in the Kronecker lift at `m = 100`
(1.05–1.51).

## 7. What changes under exact spectral filters, and what does not

**(D1) Critical step: decrease below, increase above.**
*Unchanged*: the dichotomy itself, at every state visited by the 36 trajectories (468 states, all filters) and
at all E4 states; and the self-consistency `η* ≈ η_run` (0.93–1.04) in the late phase.
*Changed*: the value. Noise-dominated: `η*_F = η*_SGD/c` (within 4 %; Muon 0.0206 vs. 0.00294/0.137 = 0.0215).
Signal-dominated: `η*_F ∝ ‖G‖^{1−p}` (fitted exponents 0.99 Muon, 0.87 `p=.125`, 0.50 `p=.5`, 1.00 Echelon,
0.00 SGD), 25–900× SGD's at the initial state and 100–650× the running step during the first phase — which is
why the first phase is a plateau. *New*: in constructed states with a signal-dominated dominant block and a
noise-level bulk, Muon / HT `.125` / Echelon `r ≥ k` show the reversed dichotomy (increase below
`η* = 0.001–0.007`, decrease above) at `m = 5`.

**(D2) High alignment ⇒ decrease for every step; band → 1 as `m → ∞`.**
*Unchanged* in noise-dominated states: all filters switch to all-step decrease at the same states as SGD, where
θ crosses θ*; the late band is Thm 16 at `η_eff` (deviation ≤ 0.0025) and approaches 1 with `m` exactly as for
SGD (0.555–0.560 at `m = 5`, 0.9804–0.9807 at `m = 200`).
*Changed*: with a signal-dominated dominant block the Muon-type filters are in the all-step-decrease regime
already below θ*; in a signal-dominated late phase (noise-free, low noise, κ ≥ 8) the band is the limit-cycle
value `Σ_{i≤k}λ^q/Σ_{i≤n}λ^q` (0.963 for Muon at `m = 5`, where Thm 16 gives 0.560 and `Σ_Dλ²/Σλ²` = 0.904);
with `Σ ∝ A` noise the band is lower than SGD's (`1 − θ` up to 8.5× larger); with Nesterov momentum the
reference itself changes (SGD + Nesterov: 0.484 at `m = 5`).

**(D3) `2 gap_1/(λ_1² − λ_d²) ≲ η* ≤ 2/λ_1`.**
For SGD: the lower bound (Thm 7) holds in all 56 states; the upper bound fails in the paper's own setup
(`η*_0 = 0.0214–0.0224 > 2/λ_1 = 0.02` for `m ≥ 20`; 12 of 48 states where the hypothesis holds; Monte-Carlo
confirmed). For the filters neither bound is meaningful: `η*` is `(2 gap…2/λ_1)/c` in the noise-dominated
regime and proportional to `‖G‖^{1−p}` in the signal-dominated regime; it is nearly independent of `m`
(Muon: 10.0 → 14.4 for `m` = 5 → 500 at the initial state).

**(D4) Window `η_D^loss < η < η_B^loss`; `D`-updates do not reduce the loss.**
*Unchanged* in the regime the paper's explanation addresses (high alignment, dominant block at its noise
floor, bulk not converged): identical ratio `η_D^loss/η_B^loss` for all filters and `p` (0.58 / 0.35 / 0.10 /
0.023 at `m` = 5 / 20 / 100 / 500), running step at the lower edge of the window, `D`-projected continuation
flat (0.998–1.000), bulk-projected continuation = full update.
*Changed*: (i) `F(P^D G)` is strictly worse than `P^D F(G)` for the filters (threshold 0.35–0.75 running
steps; it raises the loss at the running step); (ii) in signal-dominated states the window is narrow and
`p`-dependent (ratio 0.57 Muon … 0.13 `p = .5` … 0.034 SGD at `m = 20`) and the `D`-projected update does the
work; (iii) **the ordering reverses** (bulk-projected update unstable first, ratio up to 2.35) when the
dominant block is signal-dominated and the bulk block noise-dominated (`m ≥ 200` at the standard
initialisation; also in the Kronecker lift at `m = 100`), for Muon, HT `.125`, Echelon `r ≥ k` — never for
SGD, HT `.5` or Echelon `r < k` in these experiments.

**(D5) Two-phase curve and `θ_∞`.**
*Unchanged*: a two-phase curve in every setting tested (isotropic and `Σ ∝ A` noise, Kronecker, momentum,
`n = 1`, W0 std 1–10), and `θ_∞` = Thm 16 at `η_eff` with isotropic noise and no momentum.
*Changed*: the first phase is a plateau of length `∝ ‖W_0‖^{1−p}/η` followed by an abrupt collapse (Muon:
minimum at `t` = 610 / 1870 / 6410 for W0 std 1 / 3 / 10; SGD: 29–35) during which the update is far less
aligned than the gradient (0.40 vs. 0.99); `θ_∞` is replaced by the SGD + Nesterov value with momentum, by the
row-resolved linear-response value with `Σ ∝ A`, and by the limit-cycle value in a signal-dominated late phase.

**Is the late phase noise- or signal-dominated? It decides everything.** Noise-dominated ⇒ SGD-equivalent
(isotropic noise) or computable by row-resolved linear response (structured noise). Signal-dominated ⇒ limit
cycle with alignment near 1, above `Σ_Dλ²/Σλ²`.

## 8. Caveats and negative results

* **Sizes.** Matrix runs use `d = 200`, `k = 20`, `n = 50` and `T ≤ 5000` (14000 in one run) instead of the
  paper's `d = 500`, `T = 30000`; `m = 100, 500` large-init runs are not stationary at `T = 3000` (late
  alignments for `m ≥ 100` come from the zero-init runs, `m ≤ 200`). One aspect ratio only (`n/d = 1/4`,
  `k < n`), except for the noise-free limit-cycle check (`n` = 1 … 200).
* **Seeds.** 2–3 seeds per configuration (1 for the larger-init and the `T = 9000` momentum runs); one-step
  statistics use the checkpoints of seed 0 only (32–48 noise draws each; bootstrap s.e. of the critical steps
  ≤ 3 %). Statements at the 0.001–0.003 level about late alignments are at the edge of the seed spread.
* **Not converged**: the κ = ¼, ½ columns of the sweep; Muon and Echelon in the momentum group at `T = 6000`;
  the std-10 runs at `T = 6000`; SGD in the low-noise group; all large-init Kronecker runs. These are flagged
  where they appear and not used for stationary claims.
* **Floating-point artefact** in the noise-free `n = 1` runs: for HT `p = .5`, `m = 100` the 50 dominant
  coordinates underflow to exactly 0 (while the slow bulk still dominates `|g|`) and can never regrow, giving
  E[Align] = 0. A noise of `σ = 10⁻¹²` removes the artefact and restores the limit cycle:

{{T:underflow}}

* **Null result**: with isotropic noise, in the noise-dominated regime, there is no measurable effect of the
  exact filters on late alignment, critical step (in drift units) or loss-threshold ratio beyond the rescaling
  `η → cη` — for any `p`, any Echelon rank (with `τ = s_{r+1}`), `n = 1` or `n = 50`, M2 or M3.
* **Linear response is not universal**: it fails by 0.011 in late alignment for Echelon with `τ = ‖T‖_F` and
  small `r`, and it requires row-resolved coefficients for `Σ ∝ A`.
* **Constant step only.** Deng's decaying-step results (Thm 14/15) were not examined; no weight decay; no
  Newton–Schulz, interval or streaming approximations (those are the subject of `sim/speedups`).
* **Ratio of expectations.** Critical steps and thresholds are roots of ratio-of-expectation responses; the
  directly averaged ratio was checked on a grid for four filters at 13 states (agreement 1–3 %), not everywhere.
* **Paper's Thm 8 / Cor. 9**: the violation is established numerically for the closed-form η* of the paper's
  definition and by direct Monte Carlo; the diagnosis of the proof is from reading it, not from a formal check.

## 9. Reproduction and compute

All commands are in `sim/exact/README.md` (environment: `OMP_NUM_THREADS=1`, `nice -n 10`, python3 + numpy +
matplotlib). Seeds are fixed in the scripts. `make_tables.py`, `make_figures.py` and `make_note.py` regenerate
`results/tables.md`, `figs/*.png` and this note from the raw results.

{{T:cpu}}

Figures: `e0_baseline.png`, `e1_twophase.png`, `e1_diagnostics_m20.png`, `e1_late_vs_m.png`, `e1_sweep.png`,
`e1_momentum.png`, `e1_n1.png`, `e2_alignment_response.png`, `e3_loss_thresholds.png`, `e3_continuation.png`,
`e4_robustness.png` (all in `sim/exact/figs/`, dpi 130).
