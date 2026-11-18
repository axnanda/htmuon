#!/bin/sh
# Reproduces every number quoted in notes/research/theory_onestep.md (about 4.5 CPU-minutes, 1 thread).
cd "$(dirname "$0")"
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
for s in validate_m2_commuting validate_m2_general validate_projected validate_m1 validate_m2_noise probe_noncommuting gap_dependence extra_checks; do
  echo "=== $s"; nice -n 10 python3 $s.py > results/$s.log 2>&1 || echo "FAILED $s"
done
nice -n 10 python3 summarize.py
