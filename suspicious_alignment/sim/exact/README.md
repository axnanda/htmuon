# sim/exact — exact spectral filters versus SGD on Deng-style quadratics

Numpy / float64 simulation study for `notes/research/sim_exact_filters.md` (task key `sim-exact-filters`).
All filters use an exact LAPACK SVD (`numpy.linalg.svd`); no Newton–Schulz, no tracked frames.

## Environment

```
cd /home/user/htmuon/suspicious_alignment/sim/exact
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1      # single thread
nice -n 10 python3 <script> [args]                                    # python3 + numpy + matplotlib only
```

Every script appends its CPU time to `results/cpu_log.jsonl`; the total for the whole study is about
30 CPU-minutes (table "Compute log" at the end of `results/tables.md`).

## Files

| file | content |
|---|---|
| `specfilt.py` | reusable module: `Problem` (Deng spectrum, M2 / M3 lifts, iso and Sigma∝A noise, Deng's closed forms: `theta_inf`, `eta_star_deng`, `eta_loss_deng`, `theta_crit_deng`, `theta_star_deng`, exact finite-T moments, exact SGD+Nesterov Lyapunov reference), the filters (`apply_filter`: `sgd`, `muon`, `ht<p>`, `ech<r>`), the pure-noise calibration (`calibrate`, `linresp_theta`), the trajectory runner (`run`: momentum, projections, logging of loss / theta / update fraction / singular values / subspace overlap) and the one-step Monte-Carlo estimators (`onestep`, `align_response`, `loss_thresholds`). |
| `tests_sanity.py` | checks: filters versus their definitions (polar factor, `polar(X)(X^T X)^{p/2}`, Echelon `U_r polar(U_r^T X) + T/||T||_2`), eigenbasis implementation versus dense random-`Q` implementation (M2 and M3), scale covariance, Monte-Carlo one-step estimators versus Deng's closed forms, SGD stationarity. |
| `e0_baseline.py` | E0: Deng's Section-7 experiment (literal port of `quad_sim.py` for seeds 42/87 + eigenbasis runs for 7 seeds). |
| `e1_trajectories.py <group>` | E1 in (M2), d=200, k=20, n=50. Groups: `twophase_a` (m=5,20), `twophase_b` (m=100,500), `late_a`, `late_b` (zero init, m=5..200), `sweep` (learning-rate sweep), `signal` (noise-free and kappa=16), `lownoise`, `largeinit`, `momentum`, `pilot`. |
| `e1_n1.py` | E1 in (M1), n=1, Deng's protocol (d=500, k=50, T=30000). |
| `e1_extra.py limit\|stat` | noise-free limit cycles versus n; runs started from SGD's stationary law. |
| `e2e3_onestep.py states\|scale\|mdep\|highalign` | E2 + E3 one-step statistics (alignment response and projected-loss thresholds versus step size). `states` needs the checkpoints written by `twophase_a/b`. |
| `e2_etastar_bounds.py` | Deng's eta*_t against the bounds of Theorems 7, 8 and Corollary 9 in the paper's own setup. |
| `e3_continue.py` | E3 continuation runs (full / P^D F(G) / P^B F(G) / F(P^D G) / F(P^B G)), needs the `twophase` checkpoints. |
| `e4_robust.py aniso\|kron` | E4: Sigma ∝ A noise in (M2); Kronecker lift (M3). |
| `make_tables.py` | all tables of the note -> `results/tables.md`. |
| `make_figures.py [name ...]` | all figures -> `figs/*.png` (dpi 130). |
| `plotstyle.py` | matplotlib style. |

## Reproducing everything (in this order; CPU seconds measured on this machine in brackets)

```
python3 tests_sanity.py                                              # [5]
python3 e0_baseline.py              > results/e0_baseline.log       # [67]
python3 e1_trajectories.py twophase_a > results/e1_twophase_a.log   # [151]  writes checkpoints
python3 e1_trajectories.py twophase_b > results/e1_twophase_b.log   # [150]  writes checkpoints
python3 e1_trajectories.py late_a   > results/e1_late_a.log         # [111]
python3 e1_trajectories.py late_b   > results/e1_late_b.log         # [143]
python3 e1_trajectories.py sweep    > results/e1_sweep.log          # [198]
python3 e1_trajectories.py signal   > results/e1_signal.log         # [133]
python3 e1_trajectories.py lownoise > results/e1_lownoise.log       # [58]
python3 e1_trajectories.py largeinit > results/e1_largeinit.log     # [~70]
python3 e1_trajectories.py momentum > results/e1_momentum.log       # [184]
python3 e1_n1.py                    > results/e1_n1.log             # [80]
python3 e1_extra.py limit           > results/e1_extra_limit.log    # [~60]
python3 e1_extra.py stat            > results/e1_extra_stat.log     # [~25]
python3 e2e3_onestep.py states      > results/e23_states.log        # [49]
python3 e2e3_onestep.py scale       > results/e23_scale.log         # [2]
python3 e2e3_onestep.py mdep        > results/e23_mdep.log          # [4]
python3 e2e3_onestep.py highalign   > results/e23_highalign.log     # [6]
python3 e2_etastar_bounds.py        > results/e2_etastar_bounds.log # [3]
python3 e3_continue.py              > results/e3_continue.log       # [116]
python3 e4_robust.py aniso          > results/e4_aniso.log          # [~110]
python3 e4_robust.py kron           > results/e4_kron.log           # [~230]
python3 make_tables.py                                               # results/tables.md
python3 make_figures.py                                              # figs/*.png
```

Seeds are fixed inside the scripts (`numpy.random.default_rng([seed, stream])`; the literal port in
`e0_baseline.py` uses the legacy `numpy.random.seed` exactly like the authors' `quad_sim.py`).

## Conventions

* Everything runs in the eigenbasis of the Hessian factor(s); this is exact for the filters and for
  isotropic or `Sigma ∝ A` Gaussian noise (checked against dense random-`Q` runs in `tests_sanity.py`).
* `theta` always means Deng's alignment of the TRUE gradient with the dominant Hessian subspace,
  `||P^D A W||_F^2 / ||A W||_F^2`.  Other notions are logged under separate names: `theta_stoch`
  (stochastic gradient), `theta_inp` (filter input, = momentum-averaged gradient), `upd_frac`
  (fraction of the update's squared norm in `D`), `ovl_inp` / `ovl_true` (overlap of the top-k left
  singular subspace of the filter input / true gradient with `D`).
* Learning rates: `eta = kappa * eta_rule(F)`, `eta_rule(F) = eta_SGD * E<Xi, F(Xi)> / E||F(Xi)||_F^2` for
  pure-noise input `Xi` (the step with SGD's stationary loss floor in the noise-dominated regime);
  `eta_eff = eta * c` is the drift-equivalent SGD step (`c` = Stein linear-response coefficient).
  With Nesterov momentum the rule is evaluated for the averaged (less noisy) filter input.
