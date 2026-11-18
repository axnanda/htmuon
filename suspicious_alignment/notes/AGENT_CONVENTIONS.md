# Conventions for agents working on this formalization

## What this project is
A Lean 4 / Mathlib formalization of **Deng, Liao, Ouyang, Pang, Song, Yang — "Suspicious Alignment of
SGD: A Fine-Grained Step Size Condition Analysis" (ALT 2026, arXiv:2601.11789v2)**, plus an extension
of its theory to spectrally-filtered optimizers (Muon / HTMuon / Echelon).

* Project root: `/home/user/htmuon/suspicious_alignment` (Lean lib `SuspiciousAlignment`).
* Paper LaTeX source (the source of truth for statements and proofs):
  `/tmp/claude-0/-home-user/b3254748-8fab-53a7-9b3f-cd840dc725a3/scratchpad/arxiv_src/x/alt2026-sample.tex`
  (2847 lines; main text 159–828, Appendix A proofs 829–2456, Appendix B numerics 2457–end).
  Read the line range you are given with the Read tool (use `offset`/`limit`); read neighbouring
  lines whenever a statement refers to something defined elsewhere.
* Shared definitions: `SuspiciousAlignment/Defs.lean` — READ IT FIRST. It defines `Spec ι` (spectrum
  `lam`, dominant block `D`, bulk `B = Dᶜ`, `lam1/lamk/lamk1/lamd`, `psiD/psiB`, `rho`), `Noise ι`
  (`kap2`, `smin`, `smax`), and the paper's quantities (`mom`, `sD/sB/s`, `theta`, `qCoef`, `pCoef`,
  `etaStar`, `gGap`, `gNoise`, `r0`, `thetaStar`, `cNext`, `cNextProj`, `fCompare`, `EsNext`,
  `thetaBarNext`, `etaLoss`, `expLossChange`, `alphaT/betaT/gammaT/hQuad/thetaCrit`, `betaC`,
  `varrhoD`, `deltaC`, `tStar`, `secondMoment`, `thetaInf`, `loss`, …) together with basic lemmas.
  Use these definitions; do not re-define them under other names.

## Toolchain
```
cd /home/user/htmuon/suspicious_alignment
scripts/leancheck SuspiciousAlignment/<Your/File>.lean        # type-check one file (10 s – several min)
scripts/leancheck --build SuspiciousAlignment.<Your.Module>   # build ONE module so later files can import it
```
* ALWAYS go through `scripts/leancheck` (it sets PATH and serialises Lean runs: at most 3 Lean
  processes at once on this 4-core / 15 GB machine; your call may wait a little for a free slot).
  Never call `lake`/`lean` directly, never run `lake update`, `lake exe cache …`, `lake clean` or a
  bare `lake build`; never touch `.lake/`. Run one check at a time, no background jobs.
* Lean `v4.35.0`, Mathlib `v4.35.0` (prebuilt, shared). Mathlib sources for grepping lemma names:
  `/home/user/htmuon/suspicious_alignment/.lake/packages/mathlib/Mathlib/`.
* A worked example of this style of Lean/Mathlib (matrix + analysis) project that compiles on this
  toolchain: `/home/user/echelon-lean/` (read-only reference).
* Only import project modules that are on your "built" list (their `.olean` exists). If an import
  fails with "object file ... does not exist", run `scripts/leancheck --build <that module>` once.
* If a check takes more than ~5 minutes, your proof is too heavy: split lemmas, replace big
  `nlinarith`/`simp` calls by explicit steps. Keep files moderate in size (prefer < 1500 lines; split
  into `Foo/Part1.lean`-style files only if you are told you may).
* Start every file with `import Mathlib` (plus project imports), and work inside
  `namespace SuspiciousAlignment`. `autoImplicit` is off.

## Interruptions (IMPORTANT)
The machine may be restarted at any time, killing your session; only files on disk survive.
* SAVE OFTEN: write your Lean file to disk early and after every proved lemma (never keep large
  unsaved work in your head); keep the file compiling at each save if possible (comment out, do not
  `sorry`, unfinished parts — and list them in a `-- TODO(unfinished): …` comment at the top).
* RESUME: a previous agent may have been interrupted while doing exactly your task. If your target
  file (or note, script, result) already exists, do NOT start over: read it, check what compiles,
  keep what is good, and complete or repair the rest.
* When you finish a stage, also write your final structured report as JSON to
  `notes/status/<key>.<stage>.json` (the task tells you the name).

## Hard rules
1. **No `sorry`, no `admit`, no new `axiom`, no `native_decide`, no `unsafe`**, no `implemented_by`.
   Before finishing, check each main theorem with a temporary `#print axioms <name>` — the output
   must only mention `propext`, `Classical.choice`, `Quot.sound` — then remove the `#print` lines.
   The final file must compile with **no errors** (warnings are tolerated but keep them low).
2. **Do not edit files you do not own** (in particular `Defs.lean`). If you need an extra shared
   definition or you think a definition in `Defs.lean` is wrong/unfaithful, define what you need in
   your own file and say so prominently in your report.
3. **Fidelity over convenience.** The goal is to formalize what the paper claims.
   * State every theorem as close to the paper as mathematically possible, with the paper's
     numbering and a one-line informal statement in the docstring.
   * The paper is informal in places (missing hypotheses, strict vs. non-strict inequalities,
     `d → ∞` limits written loosely, quantities that may be `0/0`). When the paper's statement is
     ambiguous, incomplete or false as written, DO NOT silently change it. Prove the closest correct
     statement, make every extra hypothesis explicit in the Lean statement, and record the deviation
     in your fidelity note (see below). If the paper's claim is false as literally stated, try to
     also prove a formal counterexample (a concrete instance where it fails).
   * Never make a theorem true by an unsatisfiable hypothesis or by exploiting `x / 0 = 0`. For each
     main theorem, convince yourself (and say in the report) that its hypotheses are jointly
     satisfiable; where cheap, include a concrete non-vacuity `example`.
4. **Fidelity note.** Write `notes/fidelity/<FileName>.md` with a table: paper item (number, tex
   lines) → Lean declaration name → status ∈ {exact, equivalent-reformulation, hypotheses-added,
   weakened, strengthened, paper-claim-false, not-formalized} → explanation. List every gap or
   error you found in the paper's statement or proof, with a precise mathematical explanation.
5. Keep proofs readable: small lemmas, docstrings, no 300-line tactic blocks.

## Layered treatment of the `d → ∞` statements
Many theorems are stated as `lim_{d→∞} 𝔼[θ_{t+1} | x_t] < θ_t`. We formalize them in layers:
* **Exact finite-`d` core**: statements about `𝔼[f_t(η) | x_t] = p_t η² + q_t η`
  (`Spec.pCoef`, `Spec.qCoef`) and about the ratio of expectations `Spec.thetaBarNext`
  ("deterministic equivalent" of `𝔼[θ_{t+1} | x_t]`). These hold for every finite `d`.
* **Probability layer**: the expectations are integrals over an actual probability space.
* **Asymptotic layer**: sequences of problems indexed by `d`, concentration, and the transfer
  `𝔼[θ_{t+1}] - thetaBarNext → 0`.
Your task description says which layer(s) you own.

## Final report
End with a compact report: files written, list of main theorem names with one-line statements,
deviations from the paper (the fidelity table in brief), anything you could not prove (must be
stated explicitly, never hidden), and suggestions for downstream files.
