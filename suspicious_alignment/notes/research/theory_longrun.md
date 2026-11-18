# Long-run (constant step size) dynamics of spectrally filtered updates in Deng's quadratic model

STATUS: SKELETON (written early so that an interruption does not lose the results; the full note
replaces this file). Task key `theory-longrun`. Scripts and raw results:
`/home/user/htmuon/suspicious_alignment/sim/theory_longrun/` (`exp*.py`, `results/*.json|log`).

## Results in hand (from finished runs; see `results/*.log`)

Notation: spectrum `lam_1 >= .. >= lam_k > lam_{k+1} >= .. >= lam_d > 0`, `m = lam_k/lam_{k+1}`,
`theta = sum_D lam_i^2 |c_i|^2 / sum_i lam_i^2 |c_i|^2`, `psi_S = sum_S lam_i^2`, filter
`f(sigma) = sigma^p`, `q := 2/(1-p)`.

1. **SGD baseline (exp1).** Deng's Theorem 16 `theta_inf = sum_D lam^2 beta / sum lam^2 beta`,
   `beta_i = eta kappa_i^2/(2 lam_i - eta lam_i^2)` reproduced to 3-4 digits for
   `m in {5,..,500}` (d = 500, k = 50, eta = 0.003, 8 seeds) when measured as the ratio of
   time-averaged energies; the two-phase curve (decrease, then rise) is reproduced; the observed
   minimum is at the argmin of the deterministic equivalent
   `E c_i(t)^2 = (1-eta lam_i)^{2t}(c_{i0}^2 - beta_i) + beta_i`; Deng's `t*` (Theorem 15) is a valid
   but very conservative lower bound for the decreasing phase.
2. **Noise-free commuting (M2) = decoupled scalar maps (exp0, exp2).**
   `a_i(t+1) = |a_i(t) - eta f(lam_i a_i(t))|` for the row norms `a_i = |c_i|`.
   * Muon (`f = 1`): exact solution, linear descent `a_i(t) = a_i(0) - t eta`, then the 2-cycle
     `{rho_i, eta - rho_i}`, `rho_i = a_i(0) mod eta`. Two-step mean energy
     `lam_i^2 (rho_i^2 + (eta-rho_i)^2)/2 in [eta^2 lam_i^2/4, eta^2 lam_i^2/2)`.
     `theta_inf in [psi_D/(psi_D + 2 psi_B), 2 psi_D/(2 psi_D + psi_B)]`, `~ psi_D/psi` for generic
     phases: **lam^2 scaling instead of Deng's lam^1**; no noise needed; no two-phase behaviour for
     equal initial row norms (theta is exactly constant during the descent).
   * HTMuon (`0 < p < 1`): every orbit (outside a countable set) converges to the fixed point
     `a_i* = (eta lam_i^p/2)^{1/(1-p)}`; gradient energy floor `(eta lam_i/2)^q`;
     `theta_inf = sum_D lam^q / sum lam^q` (measured to 1e-15). Two-phase behaviour: yes; the
     dominant block reaches its floor at `T_D ~ a_0^{1-p}/((1-p) eta lam_k^p)`, the bulk at
     `T_B ~ a_0^{1-p}/((1-p) eta lam_d^p)`.
   * Echelon(r): the tail decays to 0, about `r+1` directions stay on Muon 2-cycles;
     `r < k`: `theta_inf = 1`; `r >= k`: `theta_inf ~ psi_D/(psi_D + sum of the r+1-k largest bulk lam^2)`.
3. **Momentum (exp2b).** Scale covariance: with Nesterov-EMA momentum the per-direction
   trajectory is `a_i(t) = (eta lam_i^p)^{1/(1-p)} b_i(t)` with `b_i` a solution of a universal
   recursion, so the long-run energy is `C(p, beta) (eta lam_i)^q` and the `lam^q` law is unchanged.
4. **(M1), noise-free (exp3a).** Normalised-GD-type dynamics with effective step
   `eta_eff = eta |A x|^{p-1}`; one-step criterion `theta decreases <=> eta_eff < eta*_t` verified
   (0 violations / 47992); long run: period-2 orbit on the TOP eigenvector, `theta_inf = 1`,
   `eta_eff lam_1 = 2` (edge of stability), `|g| = (eta lam_1/2)^{1/(1-p)}`.
5. **(M1), with noise (exp3b).** `theta_inf` = Deng's Theorem 16 evaluated at the self-consistent
   effective step `(eta/eta_eff)^{2/(1-p)} = sigma^2 d + sigma^2 eta_eff sum_i lam_i/(2-eta_eff lam_i)`;
   agreement to 3-4 digits over noise levels spanning 3 decades.
6. **(M2), with noise, d << n (exp4).** Row-decoupled mean-field law
   `E_i = (eta lam_i/2) g_i^{1+p}`, `2 (g_i^2 - nu^2) = eta lam_i g_i^{1+p}`, `nu = sigma sqrt(n)`:
   interpolates between Deng's `lam^1` scaling (noise-dominated) and the `lam^q` floor
   (step-dominated). Agreement within 0.5% for Muon/HTMuon in the noise-dominated regime.

(Complete statements, proofs, tables, figures and the Lean-ready theorem list follow in the full note.)
