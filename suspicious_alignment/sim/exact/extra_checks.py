"""Three small supporting checks  ->  results/extra_checks.json      (about 15 CPU-s)

 A. Floating-point caveat of the noise-free n = 1 run 'free_ht0.5_m100' of e1_n1.py (E[Align] = 0, loss ~ 1e-10):
    the dominant coordinates contract geometrically while the slow bulk still dominates |g|, underflow to
    EXACT zeros in float64 and can then never regrow.  We repeat the run (same seed-42 initial point and step)
    (i) noise-free, counting exact zeros, and (ii) with a negligible noise sigma = 1e-12, which removes the
    artefact and restores the limit cycle (theta -> 1, loss = 0.5 lam_1 (eta^2 lam_1 / 4)^2).
 B. Row-resolved linear-response coefficients of the filters for Sigma ∝ A noise (E4): drift coefficient c_i and
    injected noise nu_i averaged over the dominant / bulk rows (specfilt.calibrate), d=200, k=20, n=50.
 C. Reversal of the loss-threshold ordering at the isotropic initial state: noisy versus noise-free thresholds.
Usage:  python3 extra_checks.py
"""
import os

import numpy as np

import specfilt as sf


def part_a():
    d, k, m, T, p = 500, 50, 100, 30000, 0.5
    lam = sf.deng_spectrum(d, k, m)
    eta = sf.calibrate(sf.Problem(d, k, 1, 20), "ht0.5", nmc=400)["eta_rule"]      # as in e1_n1.py
    out = {}
    for name, sig in (("noise_free", 0.0), ("sigma_1e-12", 1e-12)):
        x = np.random.default_rng([42, m, 0]).standard_normal(d)
        rng = np.random.default_rng(5)
        zeros_at = None
        th_acc = ls_acc = 0.0
        for t in range(T + 1):
            g = lam * x
            if zeros_at is None and np.all(x[:k] == 0.0):
                zeros_at = t
            if t > T - 10000:
                g2 = g * g
                th_acc += g2[:k].sum() / g2.sum()
                ls_acc += 0.5 * (x * g).sum()
            G = g + sig * rng.standard_normal(d)
            nrm = np.sqrt((G * G).sum())
            x = x - eta * nrm ** (p - 1) * G
        out[name] = dict(eta=eta, E_align=th_acc / 10000, loss_late=ls_acc / 10000,
                         first_step_all_dominant_coords_exactly_zero=zeros_at,
                         n_exact_zero_dominant_coords_at_end=int((x[:k] == 0.0).sum()),
                         limit_cycle_loss_prediction=float(0.5 * lam[0] * (eta ** 2 * lam[0] / 4) ** 2))
        print(name, out[name], flush=True)
    return out


def part_b():
    rows = []
    for m in (20, 100):
        prob = sf.Problem(200, 20, 50, m, noise="propA")
        for o in ("sgd", "muon", "ht0.125", "ht0.5", "ech1", "ech20", "ech40"):
            c = sf.calibrate(prob, o, nmc=200)
            lam = prob.lam
            stat = c["nu_rows"] / (2 * c["c_rows"] * lam)            # stationary E||w_i||^2 / eta  (small-eta limit)
            w = lam ** 2 * stat
            rows.append(dict(m=m, opt=o, c_D=c["c_D"], c_B=c["c_B"], nu_D=c["nu_D"], nu_B=c["nu_B"], eta_rule=c["eta_rule"],
                             theta_small_eta=float(w[:20].sum() / w.sum()),
                             kap2_D=float((prob.kap[:20] ** 2).mean()), kap2_B=float((prob.kap[20:] ** 2).mean())))
            r = rows[-1]
            print(f"m={m} {o:8s} c_D={r['c_D']:.4f} c_B={r['c_B']:.4f} (c_B/c_D={r['c_B'] / r['c_D']:.2f})  "
                  f"nu_D={r['nu_D']:.4f} nu_B={r['nu_B']:.4f} (nu_D/nu_B={r['nu_D'] / r['nu_B']:.2f}; noise var ratio "
                  f"{r['kap2_D'] / r['kap2_B']:.1f})  theta(eta->0)={r['theta_small_eta']:.4f}", flush=True)
    return rows


def part_c():
    """Is the reversal eta_D^loss > eta_B^loss of the Muon-type filters at the isotropic initial state a noise effect?
    Same state W = Z (std 1) as e2e3_onestep.py::part_mdep, thresholds with sigma = 0.5 (32 draws) and noise-free
    (exact), plus the share of the TRUE bulk gradient in the bulk block of the stochastic gradient."""
    rows = []
    opts = ["sgd", "muon", "ht0.125", "ht0.5", "ech1", "ech20", "ech40"]
    for m in (20, 100, 200, 500):
        prob = sf.Problem(200, 20, 50, m)
        prob0 = sf.Problem(200, 20, 50, m, sigma=0.0)
        Z = sf.init_state(prob, [0])[0]
        st = sf.onestep(prob, Z, opts, N=32, seed=5 + m, gradproj=False)
        st0 = sf.onestep(prob0, Z, opts, N=1, seed=0, gradproj=False)
        gB = float(((prob.H * Z)[20:] ** 2).sum())
        row = dict(m=m, bulk_signal_over_noise=gB / float(prob.kap2[20:].sum()))
        for o in opts:
            L = sf.pair_avg(st["per_opt"][o]["Lq"])
            L0 = st0["per_opt"][o]["Lq"]
            row[o] = dict(ratio_noisy=float((L[:, 0].mean() / L[:, 3].mean()) / (L[:, 1].mean() / L[:, 4].mean())),
                          ratio_noise_free=float((L0[0, 0] / L0[0, 3]) / (L0[0, 1] / L0[0, 4])),
                          etaB_noisy=float(2 * L[:, 1].mean() / L[:, 4].mean()), etaB_noise_free=float(2 * L0[0, 1] / L0[0, 4]),
                          etaD_noisy=float(2 * L[:, 0].mean() / L[:, 3].mean()), etaD_noise_free=float(2 * L0[0, 0] / L0[0, 3]))
        rows.append(row)
        print(f"m={m} bulk signal/noise (||P^B AW||^2 / E||P^B Xi||^2) = {row['bulk_signal_over_noise']:.3g}: " +
              "  ".join(f"{o}: {row[o]['ratio_noisy']:.3g} (noise-free {row[o]['ratio_noise_free']:.3g})" for o in opts), flush=True)
    return rows


if __name__ == "__main__":
    cpu = sf.CpuLog("extra_checks")
    res = dict(underflow=part_a(), aniso_calibration=part_b(), reversal_noise=part_c())
    sf.save_json(os.path.join(sf.RES, "extra_checks.json"), res)
    cpu.done()
