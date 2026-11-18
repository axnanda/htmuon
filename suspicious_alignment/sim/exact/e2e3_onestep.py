"""E2 + E3(one-step) -- expected one-step alignment change and projected-loss change as functions of the step
size, for every filter, at states taken along the E1 'twophase' trajectories (M2, d=200, k=20, n=50,
sigma=0.5, large init; checkpoints of seed 0 at t in {0,3,10,30,60,100,200,400,700,1000,1500,2000,3000}).
Noise draws per state: 48 on SGD's trajectory, 32 on the filters' own trajectories (antithetic pairs).

For each state W and N noise draws (common random numbers across filters and step sizes) we estimate
  * E[theta(W - eta F(G))] - theta(W) on a grid of step sizes  (expectation of the ratio), its first sign
    change, and the 'ratio-of-expectations' generalisation of Deng's critical step
        eta*_F = 2 (aB E bD - aD E bB) / (aB E cD - aD E cB)      (specfilt.align_response);
  * the loss thresholds eta^loss_S = 2 E<AW, P^S Delta> / E<P^S Delta, A P^S Delta>, S in {D, B, full}, and the
    same for the variant Delta^S = F(P^S G).
States on SGD's trajectory are evaluated with all nine filters; states on filter X's own trajectory with X
and SGD.  Step sizes are also reported 'norm-equalised': eta_n = eta * sqrt(E||F(G)||^2 / E||G||^2), the SGD
step with the same update norm.

Parts:  states (default) | scale (gradient-norm scaling) | mdep (m-dependence at the common initial state)
        | highalign (states above the stationary alignment band, takeaway D2)
Usage:  python3 e2e3_onestep.py [states|scale|mdep|highalign|all]
"""
import os
import sys

import numpy as np

import specfilt as sf

D, K, N = 200, 20, 50
OPTS = ["sgd", "muon", "ht0.125", "ht0.25", "ht0.5", "ech1", "ech10", "ech20", "ech40"]
GRID_N = np.logspace(-5, 1.5, 66)        # norm-equalised step sizes


def analyse_state(prob, W, opts, N_draws, seed, eta_run=None):
    st = sf.onestep(prob, W, opts, N=N_draws, seed=seed, gradproj=True)
    gn2 = st["gn2"].mean()
    es_d, num_d, den_d = prob.eta_star_deng(W)
    eD_d, eB_d = prob.eta_loss_deng(W)
    info = dict(theta=st["theta"], loss=st["loss"], gnorm_true=float(np.sqrt(st["aD"] + st["aB"])),
                gnorm_stoch=float(np.sqrt(gn2)), snr_frob=float((st["aD"] + st["aB"]) / prob.kap2.sum()),
                deng_eta_star=float(es_d), deng_num=float(num_d), deng_den=float(den_d),
                deng_etaD=float(eD_d), deng_etaB=float(eB_d), deng_theta_crit=float(prob.theta_crit_deng(W)),
                deng_g_gap=float(prob.g_gap()), deng_theta_star=float(prob.theta_star_deng(W)))
    per = {}
    curves = {}
    for o in opts:
        r = st["per_opt"][o]
        nfac = float(np.sqrt(r["nrm2"].mean() / gn2))            # ||F(G)|| / ||G||  (rms)
        etas = GRID_N / nfac
        ar = sf.align_response(st["aD"], st["aB"], sf.pair_avg(r["Q"]))
        m_, se_, roe_ = sf.dtheta_curves(st["aD"], st["aB"], r["Q"], etas)
        cross, s0 = sf.first_sign_change(etas, m_)
        Lq, Gq = sf.pair_avg(r["Lq"]), sf.pair_avg(r["Gq"])
        etaD, seD = sf.loss_thresholds(Lq[:, 0], Lq[:, 3])
        etaB, seB = sf.loss_thresholds(Lq[:, 1], Lq[:, 4])
        etaF, seF = sf.loss_thresholds(Lq[:, 2], Lq[:, 5])
        gD, sgD = sf.loss_thresholds(Gq[:, 0], Gq[:, 2])
        gB, sgB = sf.loss_thresholds(Gq[:, 1], Gq[:, 3])
        d = dict(nfac=nfac, upd_fracD=float(np.nanmean(r["fracD"])), **ar,
                 eta_cross_EoR=cross, sign_small_eta=float(s0),
                 dtheta_at_small=float(m_[0]), dtheta_small_se=float(se_[0]),
                 etaD=etaD, etaD_se=seD, etaB=etaB, etaB_se=seB, etaF=etaF, etaF_se=seF,
                 etaD_gp=gD, etaD_gp_se=sgD, etaB_gp=gB, etaB_gp_se=sgB,
                 ratio_DB=etaD / etaB if etaB != 0 else float("nan"),
                 ratio_DB_gp=gD / gB if gB != 0 else float("nan"),
                 l1D=float(r["Lq"][:, 0].mean()), l1B=float(r["Lq"][:, 1].mean()),
                 l2D=float(r["Lq"][:, 3].mean()), l2B=float(r["Lq"][:, 4].mean()))
        if eta_run is not None and o in eta_run:
            e = eta_run[o]
            d["eta_run"] = e
            d["dL_D_at_run"] = float(-e * d["l1D"] + 0.5 * e * e * d["l2D"])
            d["dL_B_at_run"] = float(-e * d["l1B"] + 0.5 * e * e * d["l2B"])
            mm, ss, _ = sf.dtheta_curves(st["aD"], st["aB"], r["Q"], np.array([e]))
            d["dtheta_at_run"], d["dtheta_at_run_se"] = float(mm[0]), float(ss[0])
        per[o] = d
        curves[o] = np.stack([etas, m_, se_, roe_]).astype(np.float64)
    return info, per, curves


def part_states():
    import json
    rows, curves = [], {}
    for tag in ("twophase_a", "twophase_b"):
        ck = np.load(os.path.join(sf.RES, f"e1_{tag}_ckpt.npz"))
        meta = json.load(open(os.path.join(sf.RES, f"e1_{tag}.json")))
        cfg = {r["rid"]: r for r in meta["rows"]}
        etas_run = {}
        for r in meta["rows"]:
            etas_run.setdefault(r["m"], {})[r["opt"]] = r["eta"]
        for key in ck.files:
            rid, step = key.rsplit("__", 1)
            c = cfg[rid]
            prob = sf.Problem(D, K, N, c["m"])
            W = ck[key].astype(np.float64)
            opts = OPTS if c["opt"] == "sgd" else [c["opt"], "sgd"]
            info, per, cv = analyse_state(prob, W, opts, 48 if c["opt"] == "sgd" else 32,
                                          seed=int(step) + 1000 * int(c["m"]), eta_run=etas_run[c["m"]])
            rows.append(dict(traj=c["opt"], m=c["m"], t=int(step), **info, per_opt=per))
            if c["opt"] in ("sgd", "muon", "ht0.125", "ech20") and c["m"] in (20, 100):
                for o, arr in cv.items():
                    curves[f"{c['opt']}_m{c['m']}_t{step}__{o}"] = arr
        print(tag, "done", len(rows), flush=True)
    sf.save_json(os.path.join(sf.RES, "e23_states.json"), dict(d=D, k=K, n=N, N_draws_sgd_traj=48, N_draws_own_traj=32, rows=rows))
    np.savez_compressed(os.path.join(sf.RES, "e23_states_curves.npz"), **curves)


def part_scale():
    """Gradient-norm scaling: evaluate at gamma * W for fixed noise (sigma = 0.5)."""
    import json
    rows = []
    ck = np.load(os.path.join(sf.RES, "e1_twophase_a_ckpt.npz"))
    gammas = 2.0 ** np.arange(-6, 9, 2)
    for m, step in ((20, 0), (20, 100)):
        key = [k_ for k_ in ck.files if k_.startswith(f"sgd_m{m}_") and k_.endswith(f"__{step}")][0]
        W = ck[key].astype(np.float64)
        prob = sf.Problem(D, K, N, m)
        for g in gammas:
            info, per, _ = analyse_state(prob, g * W, OPTS, 24, seed=77)
            rows.append(dict(m=m, t=step, gamma=float(g), **info, per_opt=per))
        # noise-free limit (exact homogeneity), gamma = 1
        prob0 = sf.Problem(D, K, N, m, sigma=0.0)
        st = sf.onestep(prob0, W, OPTS, N=1, seed=0, gradproj=False)
        nf = {}
        for o in OPTS:
            r = st["per_opt"][o]
            ar = sf.align_response(st["aD"], st["aB"], r["Q"], n_boot=1)
            nf[o] = dict(eta_star=ar["eta_star"], regime=ar["regime"], q_lin=ar["q_lin"], q_quad=ar["q_quad"],
                         etaD=2 * r["Lq"][0, 0] / r["Lq"][0, 3], etaB=2 * r["Lq"][0, 1] / r["Lq"][0, 4],
                         nfac=float(np.sqrt(r["nrm2"][0] / st["gn2"][0])), upd_fracD=float(r["fracD"][0]))
        rows.append(dict(m=m, t=step, gamma="noise-free", theta=st["theta"], per_opt=nf))
        print("scale", m, step, flush=True)
    sf.save_json(os.path.join(sf.RES, "e23_scale.json"), dict(rows=rows, gammas=gammas))


def part_mdep():
    """m-dependence at states constructed the same way for every m (same Gaussian matrix Z):
      'init' : W = Z (std 1), the large isotropic initialisation;
      'rise' : a typical state of constant-step SGD (eta = 0.003) at the first time t_r after the alignment
               minimum at which Deng's expected alignment has recovered to 0.75 * theta_inf, i.e.
               W = sqrt(E c_t^2) * Z -- a high-alignment state whose bulk is not yet converged."""
    rows = []
    tgrid = np.unique(np.round(np.logspace(0, 5.5, 600)).astype(int))
    for m in (5, 10, 20, 50, 100, 200, 500):
        prob = sf.Problem(D, K, N, m)
        Z = sf.init_state(prob, [0])[0]
        thb = prob.sgd_theta_bar(sf.ETA0, tgrid, 1.0)
        imin = int(np.argmin(thb))
        ir = imin + int(np.argmax(thb[imin:] >= 0.75 * prob.theta_inf(sf.ETA0)))
        t_r = int(tgrid[ir])
        Wr = np.sqrt(prob.sgd_second_moment(sf.ETA0, t_r, 1.0)) * Z
        L_inf = 0.5 * (prob.H * prob.beta(sf.ETA0)).sum()
        for name, W in (("init", Z), ("rise", Wr)):
            info, per, _ = analyse_state(prob, W, OPTS, 32, seed=5 + m)
            rows.append(dict(m=m, state=name, t_r=t_r, loss_over_floor=info["loss"] / L_inf, **info, per_opt=per))
        print("mdep", m, t_r, flush=True)
    sf.save_json(os.path.join(sf.RES, "e23_mdep.json"), dict(rows=rows))


def part_highalign():
    """Probe of takeaway (D2): states with alignment ABOVE the stationary band.
    Base state: a sample of constant-step SGD's stationary law, W_s = sqrt(beta(eta0)) * Z  (theta ~ theta_inf).
      'bulk x g' : bulk rows multiplied by g in {1, 0.7, 0.5, 0.3, 0.1, 0}   (D at its noise floor, less bulk)
      'D x g'    : dominant rows multiplied by g in {3, 10, 100}             (D signal-dominated, bulk at floor)
    For every filter: regime of the expected one-step alignment change as a function of the step size."""
    rows = []
    for m in (5, 20, 100):
        prob = sf.Problem(D, K, N, m)
        Z = sf.init_state(prob, [0])[0]
        Ws = np.sqrt(prob.beta(sf.ETA0)) * Z
        states = [("bulk", g) for g in (1.0, 0.7, 0.5, 0.3, 0.1, 0.0)] + [("D", g) for g in (3.0, 10.0, 100.0)]
        for which, g in states:
            W = Ws.copy()
            if which == "bulk":
                W[K:] *= g
            else:
                W[:K] *= g
            info, per, _ = analyse_state(prob, W, OPTS, 48, seed=11 + m)
            rows.append(dict(m=m, scaled=which, factor=g, theta_inf=float(prob.theta_inf(sf.ETA0)), **info, per_opt=per))
        print("highalign", m, flush=True)
    sf.save_json(os.path.join(sf.RES, "e23_highalign.json"), dict(rows=rows, N_draws=48))


def part_echfrob():
    """Echelon with tau = ||tail||_F versus tau = ||tail||_2 at the 'init' and 'rise' states of part_mdep (m = 20, 500)."""
    opts = ["sgd", "muon", "ech1", "echf1", "ech10", "echf10", "ech20", "echf20", "ech40", "echf40"]
    rows = []
    tgrid = np.unique(np.round(np.logspace(0, 5.5, 600)).astype(int))
    for m in (20, 500):
        prob = sf.Problem(D, K, N, m)
        Z = sf.init_state(prob, [0])[0]
        thb = prob.sgd_theta_bar(sf.ETA0, tgrid, 1.0)
        imin = int(np.argmin(thb))
        t_r = int(tgrid[imin + int(np.argmax(thb[imin:] >= 0.75 * prob.theta_inf(sf.ETA0)))])
        Wr = np.sqrt(prob.sgd_second_moment(sf.ETA0, t_r, 1.0)) * Z
        for name, W in (("init", Z), ("rise", Wr)):
            info, per, _ = analyse_state(prob, W, opts, 32, seed=5 + m)
            rows.append(dict(m=m, state=name, **info, per_opt=per))
    sf.save_json(os.path.join(sf.RES, "e23_echfrob.json"), dict(rows=rows))


if __name__ == "__main__":
    part = sys.argv[1] if len(sys.argv) > 1 else "states"
    cpu = sf.CpuLog("e2e3_onestep_" + part)
    if part in ("states", "all"):
        part_states()
    if part in ("scale", "all"):
        part_scale()
    if part in ("mdep", "all"):
        part_mdep()
    if part in ("highalign", "all"):
        part_highalign()
    if part in ("echfrob", "all"):
        part_echfrob()
    cpu.done()
