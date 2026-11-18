"""E1 -- exact spectral filters versus SGD on the left-Hessian lift (M2), d=200, k=20, n=50
(and the vector model M1, n=1, group 'n1').

Usage:  python3 e1_trajectories.py <group>
        groups: twophase_a twophase_b sweep late_a late_b signal lownoise momentum   (n1: see e1_n1.py)
Each group writes results/e1_<group>.json (summary rows) and results/e1_<group>_logs.npz (time series).

Learning rates.  'rule' learning rate of a filter F (see specfilt.calibrate): the step that gives the same
stationary loss floor as SGD at eta = 0.003 if the filter input is pure noise,
    eta_rule(F) = eta_sgd * tr(Sigma) * c / f2,   f2 = E mean_j f(s_j)^2
(c: Stein/linear-response drift coefficient of the filter on pure noise, see specfilt.calibrate; for
isotropic noise eta_rule = eta_sgd E<Xi,F(Xi)> / E||F(Xi)||_F^2).  A run uses eta = kappa * eta_rule(F); kappa = 1 is the
"tuned" setting (the achieved loss ratio to SGD is reported), the sweep varies kappa.
"""
import os
import sys

import numpy as np

import specfilt as sf

D, K, N = 200, 20, 50
OPTS = ["sgd", "muon", "ht0.125", "ht0.25", "ht0.5", "ech1", "ech10", "ech20", "ech40"]
OPTS_CORE = ["sgd", "muon", "ht0.125", "ht0.5", "ech1", "ech20", "ech40"]
CKPT_STEPS = [0, 3, 10, 30, 60, 100, 200, 400, 700, 1000, 1500, 2000, 3000]
_CAL = {}


def cal(opt, n=N, sigma=sf.SIGMA0, noise="iso", m=20, d=D, k=K, mu=None, K_=None):
    key = (opt, n, sigma, noise, m if noise != "iso" else 0, d)
    if key not in _CAL:
        prob = sf.Problem(d, k, n, m, sigma=sigma, noise=noise, mu=mu, K=K_)
        _CAL[key] = sf.calibrate(prob, opt, nmc=200)
    return _CAL[key]


def lr_for(opt, kappa=1.0, beta=0.0, n=N, sigma=sf.SIGMA0, noise="iso", m=20, d=D, k=K):
    """eta = kappa * eta_rule; with Nesterov momentum the rule keeps the same drift step eta_eff = eta*c1
    for the (smaller) noise seen by the filter."""
    c = cal(opt, n=n, sigma=sigma, noise=noise, m=m, d=d, k=k)
    if beta == 0:
        return kappa * c["eta_rule"], kappa * c["eta_eff"]
    sc = sf.nesterov_noise_scale(beta)
    prob = sf.Problem(d, k, n, m, sigma=sigma, noise=noise)
    ci = sf.calibrate(prob, opt, nmc=100, sigma_in_scale=sc)
    return kappa * ci["eta_rule_in"], kappa * c["eta_eff"]


def two_phase_stats(t, th):
    """th: seed-mean theta curve."""
    imin = int(np.nanargmin(th))
    late = np.nanmean(th[t >= 0.8 * t[-1]])
    return dict(theta0=float(th[0]), theta_min=float(th[imin]), t_min=int(t[imin]), theta_late_curve=float(late),
                two_phase=bool(th[0] - th[imin] > 0.02 and late - th[imin] > 0.02))


def run_config(cfg, logs, ckstore):
    c = dict(opt="sgd", m=20, sigma=sf.SIGMA0, noise="iso", init="gauss", init_scale=1.0, kappa=1.0, beta=0.0,
             T=3000, seeds=[0, 1, 2], ckpt=False, n=N, sigma_rule=sf.SIGMA0, d=D, k=K)
    c.update(cfg)
    mu = None if c.get("mu_alpha") is None else np.arange(1, c["n"] + 1) ** (-float(c["mu_alpha"]))
    prob = sf.Problem(c["d"], c["k"], c["n"], c["m"], sigma=c["sigma"], noise=c["noise"], mu=mu, K=c.get("Kdom"))
    eta, eta_eff = lr_for(c["opt"], c["kappa"], c["beta"], n=c["n"], sigma=c["sigma_rule"], noise=c["noise"],
                          m=c["m"], d=c["d"], k=c["k"])
    if "eta" in cfg:
        eta = cfg["eta"]
    import time
    t0 = time.process_time()
    out = sf.run(prob, c["opt"], eta, c["T"], c["seeds"], init=c["init"], init_scale=c["init_scale"],
                 beta=c["beta"], ckpt_steps=[s for s in CKPT_STEPS if s <= c["T"]] if c["ckpt"] else ())
    cpu = time.process_time() - t0
    rid = c.get("rid") or "{opt}_m{m}_s{sigma}_{noise}_{init}{init_scale}_k{kappa}_b{beta}_n{n}".format(**c)
    if mu is not None:
        rid += "_a{mu_alpha}_K{Kdom}".format(**c)
    ls = sf.late_stats(out)
    t = out["t"]
    row = dict(rid=rid, **{k_: v for k_, v in c.items() if k_ != "rid"}, eta=eta, eta_eff_drift=eta_eff,
               diverged=out["diverged"], cpu_s=round(cpu, 2), n_svd=out["n_svd"])
    if not out["diverged"]:
        for key in ("loss", "theta", "theta_stoch", "theta_inp", "upd_frac", "ovl_inp", "ovl_true", "gnorm_true",
                    "upd_norm"):
            row[key + "_late"], row[key + "_late_sd"] = sf.mean_sd(ls[key])
        row["sv_inp_late"] = ls["sv_inp"].mean(0)
        row["sv_true_late"] = ls["sv_true"].mean(0)
        row.update(two_phase_stats(t, np.nanmean(out["theta"], axis=0)))
        row["loss0"] = float(np.mean(out["loss"][:, 0]))
        noise_F2 = float(prob.kap2.sum()) if c["sigma"] > 0 else 0.0
        row["snr_frob_late"] = row["gnorm_true_late"] ** 2 / noise_F2 if noise_F2 > 0 else float("inf")
        # Deng / Theorem-16 references
        row["ratio1"], row["ratio2"] = float(prob.ratio(1)), float(prob.ratio(2))
        if c["sigma"] > 0 and eta_eff * prob.H.max() < 2:
            row["thm16_at_eta_eff"] = float(prob.theta_inf(eta_eff))
            c0sq = (c["init_scale"] ** 2 if c["init"] == "gauss" else 0.0)
            sel = t[t >= 0.8 * t[-1]]
            row["sgd_finiteT_at_eta_eff"] = float(np.mean(prob.sgd_theta_bar(eta_eff, sel, c0sq)))
            row["sgd_loss_finiteT_at_eta_eff"] = float(np.mean(prob.sgd_loss_bar(eta_eff, sel, c0sq)))
            if mu is None and c["beta"] == 0:
                cl = cal(c["opt"], n=c["n"], sigma=c["sigma_rule"], noise=c["noise"], m=c["m"], d=c["d"], k=c["k"])
                row["linresp_theta_inf"] = float(sf.linresp_theta(prob, cl, eta))
                if c["init"] == "zero":
                    row["linresp_theta_finiteT"] = float(np.mean(sf.linresp_theta(prob, cl, eta, sel)))
        row["gap_ratio"] = float(prob.gap_ratio())
        row["Kdom_size"] = prob.K
    f32 = lambda x: np.asarray(x, np.float32)
    logs[rid + "__t"] = out["t"]
    logs[rid + "__loss"] = f32(out["loss"])
    logs[rid + "__theta"] = f32(out["theta"])
    for key in ("theta_stoch", "theta_inp", "upd_frac", "upd_norm", "gnorm_true", "ovl_inp", "ovl_true", "sv_inp",
                "sv_true"):
        with np.errstate(invalid="ignore"):
            logs[rid + "__" + key] = f32(np.nanmean(out[key], axis=0))
    if c["ckpt"]:
        for s, Wc in out["ckpts"].items():
            ckstore[f"{rid}__{s}"] = f32(Wc[0])        # seed index 0 only
    print(f"{rid}: eta={eta:.4g} div={out['diverged']} loss_late={row.get('loss_late', float('nan')):.4g} "
          f"theta0={row.get('theta0', float('nan')):.3f} min={row.get('theta_min', float('nan')):.3f}"
          f"@{row.get('t_min', -1)} late={row.get('theta_late', float('nan')):.4f} "
          f"updD={row.get('upd_frac_late', float('nan')):.3f} cpu={cpu:.1f}s", flush=True)
    return row


def group_configs(group):
    cfgs = []
    if group in ("twophase_a", "twophase_b"):
        for m in ((5, 20) if group.endswith("_a") else (100, 500)):
            for o in OPTS:
                cfgs.append(dict(opt=o, m=m, T=3000, seeds=[0, 1, 2], ckpt=True))
    elif group == "sweep":
        for kap in (0.25, 0.5, 2.0, 4.0, 8.0, 16.0):
            for o in OPTS:
                cfgs.append(dict(opt=o, m=20, T=2000, seeds=[0, 1], kappa=kap))
    elif group in ("late_a", "late_b"):
        Tm = {5: 800, 10: 800, 20: 800, 50: 1850} if group.endswith("_a") else {100: 3650, 200: 5000}
        for m, T in Tm.items():
            for o in OPTS:
                cfgs.append(dict(opt=o, m=m, T=T, seeds=[0, 1, 2] if m < 100 else [0, 1], init="zero"))
    elif group == "signal":
        for m in (5, 20, 100):
            for o in OPTS:
                # noise-free; small random init (std 0.01); eta = rule value for sigma=0.5 (sets only the scale)
                cfgs.append(dict(opt=o, m=m, T=1500, seeds=[0, 1], sigma=0.0, init_scale=0.01))
        for m in (5, 20, 100):
            for o in OPTS:
                if o == "sgd":
                    continue           # eta*lam_1 = 4.8: diverges (shown in the sweep group at kappa = 8)
                cfgs.append(dict(opt=o, m=m, T=1500, seeds=[0, 1], kappa=16.0, init="zero"))
    elif group == "lownoise":
        for m in (20, 100):
            for o in OPTS_CORE:
                # sigma = 0.05 with the learning rates of the sigma = 0.5 setting, standard init
                cfgs.append(dict(opt=o, m=m, T=2000, seeds=[0, 1], sigma=0.05))
        for o in ("sgd", "muon", "ht0.125"):
            # 'large init': W0 std 10 at sigma = 0.5 (== sigma 0.05, init std 1, rescaled eta, by scale covariance)
            cfgs.append(dict(opt=o, m=20, T=6000, seeds=[0], init_scale=10.0))
    elif group == "momentum":
        for m in (5, 20, 100):
            for o in OPTS_CORE:
                cfgs.append(dict(opt=o, m=m, T=2000, seeds=[0, 1], beta=0.95))
        for m, T in ((5, 800), (20, 800), (100, 3650)):
            for o in OPTS_CORE:
                cfgs.append(dict(opt=o, m=m, T=T, seeds=[0, 1], beta=0.95, init="zero"))
        for o in OPTS_CORE:
            cfgs.append(dict(opt=o, m=20, T=1500, seeds=[0, 1], beta=0.95, sigma=0.0, init_scale=0.01))
    elif group == "pilot":
        for o in OPTS:
            cfgs.append(dict(opt=o, m=20, T=600, seeds=[0], init="zero"))
    else:
        raise SystemExit(f"unknown group {group}")
    return cfgs


def main():
    group = sys.argv[1]
    cpu = sf.CpuLog("e1_" + group)
    rows, logs, ck = [], {}, {}
    for cfg in group_configs(group):
        rows.append(run_config(cfg, logs, ck))
    os.makedirs(sf.RES, exist_ok=True)
    cals = {o: {k_: v for k_, v in cal(o).items() if not k_.endswith("_rows")} for o in OPTS}
    sf.save_json(os.path.join(sf.RES, f"e1_{group}.json"),
                 dict(group=group, d=D, k=K, n=N, calibration=cals, sv_names=sf.SV_NAMES,
                      noise_sv_edges=[sf.SIGMA0 * (np.sqrt(D) - np.sqrt(N)), sf.SIGMA0 * (np.sqrt(D) + np.sqrt(N))],
                      rows=rows))
    np.savez_compressed(os.path.join(sf.RES, f"e1_{group}_logs.npz"), **logs)
    if ck:
        np.savez_compressed(os.path.join(sf.RES, f"e1_{group}_ckpt.npz"), **ck)
    cpu.done(n_runs=len(rows), n_svd=int(sum(r["n_svd"] for r in rows)))


if __name__ == "__main__":
    main()
