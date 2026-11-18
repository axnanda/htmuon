# Do the Muon / HTMuon / Echelon speed-ups change the alignment outcomes?

STATUS: WORK IN PROGRESS (skeleton written first; sections are filled in as experiments finish —
see "Progress log" at the end). Code, raw results and figures: `sim/speedups/` (README there lists
the command that regenerates every number).

## 0. Setup (what was run)

* Model M2: `L(W) = ½ tr(Wᵀ A W)`, `W ∈ ℝ^{200×40}`, `A = Q diag(λ) Qᵀ`, dominant block `k = 20`
  with `λ_D = linspace(2m, m, 20)`, bulk `λ_B = linspace(1, 0.1, 180)`, gap `m ∈ {5, 20, 100, 500}`.
  Stochastic gradient `A W + σ Ξ`, `Ξ` i.i.d. N(0,1); `σ ∈ {0, 0.02, 0.3}`; `W₀ ~ N(0, 1)` entries.
* Alignment = Deng's `θ_t = ‖P^D A W_t‖_F² / ‖A W_t‖_F²` of the TRUE gradient with the dominant
  HESSIAN subspace. Also recorded: fraction of the update in that subspace.
* Optimizers: numpy ports (float64) of `llama_pretraining/muon.py` (NS5 Muon, HTMuon exact / NS /
  interval / stream) and an implementation of Echelon(r) from the Lean definitions; see
  `sim/speedups/README.md` for the list and the port deviations.
* Learning rates: tuned for the exact filter of each family on a separate seed (grid, 1600 steps),
  re-used unchanged for its approximations. 3 seeds (problem rotation, init, noise), 2400 steps,
  "late" = last third.

## Results so far (preliminary, m ∈ {5, 20} only)

See `sim/speedups/results/s2_tables.md` (generated). m ∈ {100, 500}, S1, S3, precision: running.

## Progress log

* previous session: ports + tests, lr tuning, S2 for m ∈ {5, 20}, cost table (S4).
* this session: fixed a crash (LAPACK `gesdd` "SVD did not converge" on a finite, numerically
  rank-20 momentum matrix in the noise-free m = 100 run of `ech_r16_ideal`; now falls back to
  `gesvd`), S2 for m ∈ {100, 500} running.
