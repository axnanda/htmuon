"""Shared configuration of the speed-up experiments (model M2, Deng-style quadratic)."""
import os

HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, 'results')
FIG = os.path.join(HERE, 'figs')
os.makedirs(RES, exist_ok=True)
os.makedirs(FIG, exist_ok=True)

D, K, N = 200, 20, 40            # W in R^{D x N}, dominant block of dimension K = D/10
MS = [5, 20, 100, 500]           # spectral gap m = lam_k / lam_{k+1}
SIGMAS = [0.0, 0.02, 0.3]        # isotropic gradient-noise std per entry: noise-free, low, high
SEEDS = [0, 1, 2]                # evaluation seeds (problem rotation Q, init W0, noise stream)
TUNE_SEED = 100                  # seed used only for learning-rate tuning
T_TUNE = 1600                    # tuning horizon; criterion = mean loss over its last third
T_EVAL = 2400                    # evaluation horizon; "late time" = its last third (steps 1600..2400)
REC_EVERY = 5

LR_GRID_SPECTRAL = [0.0025, 0.005, 0.01, 0.02, 0.04, 0.08]      # muon_exact, ht_exact
LR_GRID_SGD_C = [0.1, 0.2, 0.4, 0.8, 1.2, 1.6, 1.9]            # sgd, sgdm: lr = c / lam_1
