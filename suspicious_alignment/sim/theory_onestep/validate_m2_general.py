"""Model (M2), ARBITRARY (non-commuting) states: exact identities of Section 3.4-3.5 of the note.

 G1  Gram-matrix formulas   T^S = tr(P_S Lam g1(M)),  V^S = tr(P_S Lam^2 g2(M)),  M = Lam C C^T Lam,
     g1(t) = sqrt(t) f(sqrt t), g2(t) = f(sqrt t)^2   (index-wise filters; also d > n)
 G2  Muon pinning (d <= n, full row rank, ANY noise):  ||phi_i|| = 1,  p = s psi (theta_iso - theta)
 G3  large-step attraction:  eta > eta_att = 2 / |1/abar_D - 1/abar_B|  =>  theta moves towards theta_iso
 G4  Berezin/Jensen bounds: commuting-case formulas are upper bounds for sub-linear filters
 G5  SGD: the commuting-case (row-norm) formulas are exact for every state
Output: results/m2_general.json
"""
import os
import sys
import time
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import (FILTERS, f_muon, f_ht, f_sgd, apply_filter, rand_orth, make_spectrum,
                    block_masks, energies, theta_of, commuting_coeffs, jdump)

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
os.makedirs(OUT, exist_ok=True)
rng = np.random.default_rng(20261119)
res = {"seed": 20261119, "checks": {}}
t0 = time.time()


def upd(dic, key, val):
    dic[key] = max(dic.get(key, 0.0), float(val))


def rel(x, y):
    return abs(x - y) / max(abs(x), abs(y), 1e-300)


def gram_coeffs(lam, C, D, f_scalar):
    """Exact T^S, V^S, N^S, R^S for an index-wise filter on an arbitrary state via M = Lam C C^T Lam."""
    M = (lam[:, None] * (C @ C.T)) * lam[None, :]
    w, Z = np.linalg.eigh(M)
    w = np.clip(w, 0.0, None)
    sig = np.sqrt(w)
    # eigenvalues of M are only accurate to ~1e-16 * w.max(): exact zeros (d > n) show up at that level
    nz = w > 1e-11 * w.max()
    fv = np.where(nz, f_scalar(np.where(nz, sig, 1.0)), 0.0)
    g1 = (Z * (sig * fv)) @ Z.T          # sqrt(M) f(sqrt M)
    g2 = (Z * (fv ** 2)) @ Z.T           # f(sqrt M)^2
    out = {}
    for name, S in (("D", D), ("B", ~D)):
        out["s" + name] = np.sum(np.diag(M)[S])
        out["T" + name] = np.sum(lam[S] * np.diag(g1)[S])
        out["V" + name] = np.sum(lam[S] ** 2 * np.diag(g2)[S])
        out["N" + name] = np.sum(np.diag(g1)[S])
        out["R" + name] = np.sum(lam[S] * np.diag(g2)[S])
    out["q"] = 2 * (out["sD"] * out["TB"] - out["sB"] * out["TD"])
    out["p"] = out["sB"] * out["VD"] - out["sD"] * out["VB"]
    return out


SCALAR = {"sgd": lambda s: s, "muon": lambda s: np.ones_like(s), "ht0.125": lambda s: s ** 0.125,
          "ht0.25": lambda s: s ** 0.25, "ht0.5": lambda s: s ** 0.5}

# ---------------------------------------------------------------- G1, G4, G5
g1 = {}
g4 = {"tests": 0, "violations": 0}
g5 = {}
shapes = [(50, 50), (50, 60), (60, 200), (100, 120), (150, 400), (200, 210), (90, 40), (160, 100)]
for (d, n) in shapes:
    for trial in range(3):
        k = int(rng.integers(3, d // 5))
        m = [2.0, 10.0, 50.0][trial]
        lam = make_spectrum(d, k, m, rng)
        D, B = block_masks(d, k)
        U = rand_orth(d, rng)
        # generic state: Gaussian rows with heterogeneous scales and a random column covariance
        C = (np.exp(rng.normal(0, 0.7, d))[:, None] * rng.standard_normal((d, n))) @ np.diag(rng.uniform(0.3, 2.0, n)) / np.sqrt(n)
        W = U @ C
        G = (U * lam) @ C
        sD, sB = energies(lam, C, D)
        th = sD / (sD + sB)
        L0 = 0.5 * np.sum(lam * np.sum(C ** 2, axis=1))
        a = np.linalg.norm(C, axis=1)
        for name, fs in SCALAR.items():
            gc = gram_coeffs(lam, C, D, fs)
            Fd = apply_filter(G, FILTERS[name])
            Phi = U.T @ Fd
            for key, S in (("D", D), ("B", B)):
                T_dir = np.sum(lam[S] ** 2 * np.sum(C[S] * Phi[S], axis=1))
                V_dir = np.sum(lam[S] ** 2 * np.sum(Phi[S] ** 2, axis=1))
                upd(g1, name + ":T_relerr", rel(T_dir, gc["T" + key]))
                upd(g1, name + ":V_relerr", rel(V_dir, gc["V" + key]))
                # filter-then-project loss threshold 2 N^S / R^S
                Delta = U[:, S] @ Phi[S]
                Nd = np.sum(G * Delta)
                Rd = np.sum(Delta * ((U * lam) @ (U.T @ Delta)))
                upd(g1, name + ":etaLoss_FP_relerr", rel(2 * Nd / Rd, 2 * gc["N" + key] / gc["R" + key]))
                # project-then-filter: principal submatrix M_SS
                Delta2 = apply_filter(U[:, S] @ (U[:, S].T @ G), FILTERS[name])
                Nd2 = np.sum(G * Delta2)
                Rd2 = np.sum(Delta2 * ((U * lam) @ (U.T @ Delta2)))
                Csub = C[S]
                lam_s = lam[S]
                gsub = gram_coeffs(lam_s, Csub, np.ones(S.sum(), bool), fs)
                upd(g1, name + ":etaLoss_PF_relerr", rel(2 * Nd2 / Rd2, 2 * gsub["ND"] / gsub["RD"]))
                if name != "sgd":
                    # trace Jensen: tr P g1(M) <= tr g1(P M P) for concave g1 (sub-linear filters)
                    g4["tests"] += 1
                    g4["violations"] += int(gc["N" + key] > gsub["ND"] * (1 + 1e-10))
            eta = 0.4 * np.sum(a) / d / max(np.mean(np.linalg.norm(Phi, axis=1)), 1e-300)
            for e in (0.2 * eta, eta, 4 * eta):
                Cn = C - e * Phi
                sDn, sBn = energies(lam, Cn, D)
                upd(g1, name + ":sD_next_relerr", rel(sDn, gc["sD"] - 2 * e * gc["TD"] + e ** 2 * gc["VD"]))
                upd(g1, name + ":sB_next_relerr", rel(sBn, gc["sB"] - 2 * e * gc["TB"] + e ** 2 * gc["VB"]))
                dth = sDn / (sDn + sBn) - th
                upd(g1, name + ":dtheta_abserr", abs(dth - e * (gc["p"] * e + gc["q"]) / ((sD + sB) * (sDn + sBn))))
            # G4: commuting-case (row-norm) values are upper bounds for concave g1, g2
            co = commuting_coeffs(lam, a, D, FILTERS[name])
            if name != "sgd":
                for key in ("D", "B"):
                    g4["tests"] += 2
                    g4["violations"] += int(gc["T" + key] > co["tau" + key] * (1 + 1e-10))
                    g4["violations"] += int(gc["V" + key] > co["u" + key] * (1 + 1e-10))
            else:
                for key in ("D", "B"):
                    upd(g5, "sgd_T_rownorm_formula_relerr", rel(gc["T" + key], co["tau" + key]))
                    upd(g5, "sgd_V_rownorm_formula_relerr", rel(gc["V" + key], co["u" + key]))
res["checks"]["G1_gram_formulas_generic_states"] = {"shapes_d_n": shapes, "max_discrepancy": g1}
res["checks"]["G4_jensen_upper_bounds"] = g4
res["checks"]["G5_sgd_rownorm_exact"] = g5

# ---------------------------------------------------------------- G2, G3  Muon pinning + attraction
g2 = {}
g3 = {"tests": 0, "violations": 0, "max_abs_theta_gap_at_huge_eta": 0.0, "max_q_over_bound": 0.0}
noise_kinds = ["none", "iid_gauss", "aniso_gauss", "student_t2.5", "rank_one"]
for (d, n) in [(40, 40), (50, 70), (100, 130), (150, 300)]:
    for trial in range(5):
        k = int(rng.integers(3, d // 5))
        m = [1.5, 3.0, 10.0, 30.0, 100.0][trial]
        lam = make_spectrum(d, k, m, rng)
        D, B = block_masks(d, k)
        psiD, psiB = np.sum(lam[D] ** 2), np.sum(lam[B] ** 2)
        th_iso = psiD / (psiD + psiB)
        U = rand_orth(d, rng)
        scaleD = 10 ** rng.uniform(-1.0, 1.0)
        C = (np.where(D, scaleD, 1.0) * np.exp(rng.normal(0, 0.5, d)))[:, None] * rng.standard_normal((d, n)) / np.sqrt(n)
        W = U @ C
        sD, sB = energies(lam, C, D)
        s = sD + sB
        th = sD / s
        for kind in noise_kinds:
            Gc = (U * lam) @ C
            sc = np.linalg.norm(Gc) / np.sqrt(d * n)
            if kind == "none":
                Xi = 0.0
            elif kind == "iid_gauss":
                Xi = 2.0 * sc * rng.standard_normal((d, n))
            elif kind == "aniso_gauss":
                Xi = sc * (np.exp(rng.normal(0, 1, d))[:, None] * rng.standard_normal((d, n)) * np.exp(rng.normal(0, 1, n))[None, :])
            elif kind == "student_t2.5":
                Xi = sc * rng.standard_t(2.5, size=(d, n))
            else:
                Xi = 5 * sc * np.outer(rng.standard_normal(d), rng.standard_normal(n))
            G = Gc + Xi
            O = apply_filter(G, f_muon())
            Phi = U.T @ O
            upd(g2, kind + ":max_abs_rownorm_minus_1", np.abs(np.linalg.norm(Phi, axis=1) - 1).max())
            TD = np.sum(lam[D] ** 2 * np.sum(C[D] * Phi[D], axis=1))
            TB = np.sum(lam[B] ** 2 * np.sum(C[B] * Phi[B], axis=1))
            p_th = s * (psiD + psiB) * (th_iso - th)
            q = 2 * (sD * TB - sB * TD)
            # recover p from two direct evaluations of the comparison functional
            def fcomp(e):
                sDn, sBn = energies(lam, C - e * Phi, D)
                return sB * sDn - sBn * sD, sDn / (sDn + sBn)
            e1 = np.sqrt(s / (psiD + psiB))
            F1, _ = fcomp(e1)
            F2, _ = fcomp(2 * e1)
            p_dir = (F2 - 2 * F1) / (2 * e1 ** 2)
            upd(g2, kind + ":p_pinned_relerr", abs(p_dir - p_th) / (s * (psiD + psiB)))
            abD, abB = np.sqrt(sD / psiD), np.sqrt(sB / psiB)
            eta_att = 2.0 / abs(1 / abD - 1 / abB)
            qbound = 2 * np.sqrt(sD * sB) * (np.sqrt(sD * psiB) + np.sqrt(sB * psiD))
            g3["max_q_over_bound"] = max(g3["max_q_over_bound"], abs(q) / qbound)
            for fac in (1.001, 1.5, 6.0):
                _, thn = fcomp(fac * eta_att)
                g3["tests"] += 1
                g3["violations"] += int(np.sign(thn - th) != np.sign(th_iso - th))
            _, thn = fcomp(1e7 * eta_att)
            g3["max_abs_theta_gap_at_huge_eta"] = max(g3["max_abs_theta_gap_at_huge_eta"], abs(thn - th_iso))
res["checks"]["G2_muon_pinning_any_noise"] = g2
res["checks"]["G3_muon_large_step_attraction"] = g3

res["runtime_sec"] = time.time() - t0
jdump(res, os.path.join(OUT, "m2_general.json"))
print("G1", {k: "%.1e" % v for k, v in sorted(g1.items())})
print("G4", g4)
print("G5", {k: "%.1e" % v for k, v in g5.items()})
print("G2", {k: "%.1e" % v for k, v in sorted(g2.items())})
print("G3", g3)
print("runtime %.1fs" % res["runtime_sec"])
