"""Sanity checks of specfilt.py (cheap; ~10 s).   Usage:  python3 tests_sanity.py"""
import numpy as np

import specfilt as sf


def check(name, err, tol):
    ok = err <= tol
    print(f"[{'ok' if ok else 'FAIL'}] {name}: err = {err:.3e} (tol {tol:.0e})")
    assert ok, name


def test_filters():
    rng = np.random.default_rng(0)
    X = rng.standard_normal((60, 17)) * np.linspace(3, 0.2, 17)[None, :]
    U, s, Vt = np.linalg.svd(X, full_matrices=False)
    D, _ = sf.apply_filter(X, "muon")
    check("muon = polar factor (D^T D = I)", np.abs(D.T @ D - np.eye(17)).max(), 1e-12)
    check("muon = X (X^T X)^{-1/2}", np.abs(D - X @ (Vt.T * (1 / s)) @ Vt).max(), 1e-11)
    for p in (0.125, 0.25, 0.5):
        D, _ = sf.apply_filter(X, f"ht{p}")
        check(f"ht{p}: singular values = s^p", np.abs(np.linalg.svd(D, compute_uv=False) - np.sort(s ** p)[::-1]).max(), 1e-12)
        # HTMuon code path: polar(X) @ (X^T X)^{p/2}
        w, V = np.linalg.eigh(X.T @ X)
        check(f"ht{p} = polar(X) (X^T X)^(p/2)", np.abs(D - (U @ Vt) @ ((V * w ** (p / 2)) @ V.T)).max(), 1e-11)
    # Echelon with an exact frame: O = U_r P + T / tau, P = polar(U_r^T X), T = X - U_r U_r^T X, tau = ||T||_2
    for r in (1, 5, 16):
        Ur = U[:, :r]
        Hm = Ur.T @ X
        Uh, sh, Vh = np.linalg.svd(Hm, full_matrices=False)
        P = Uh @ Vh
        Tl = X - Ur @ Hm
        tau = np.linalg.norm(Tl, 2)
        O = Ur @ P + Tl / tau
        D, _ = sf.apply_filter(X, f"ech{r}")
        check(f"ech{r} = U_r polar(U_r^T X) + tail/||tail||_2 (and tau = s_(r+1))",
              max(np.abs(D - O).max(), abs(tau - s[r])), 1e-11)
    g = rng.standard_normal((40, 1))
    for o, f in (("muon", lambda x: 1.0), ("ht0.125", lambda x: x ** 0.125), ("sgd", lambda x: x)):
        D, _ = sf.apply_filter(g, o)
        nr = np.linalg.norm(g)
        check(f"n=1 {o}: F(g) = f(|g|) g/|g|", np.abs(D - f(nr) * g / nr).max(), 1e-12)


def test_eigenbasis_equivalence():
    """Dense A = Q diag(lam) Q^T (random Q) versus the eigenbasis implementation, same noise."""
    d, k, n, m = 40, 4, 10, 20
    prob = sf.Problem(d, k, n, m)
    rng = np.random.default_rng(1)
    Q, _ = np.linalg.qr(rng.standard_normal((d, d)))
    A = (Q * prob.lam) @ Q.T
    for opt, eta in (("sgd", 0.003), ("muon", 0.02), ("ht0.125", 0.02), ("ech4", 0.02)):
        T = 40
        out = sf.run(prob, opt, eta, T, [3], log_idx=np.arange(T))
        C = sf.init_state(prob, [3])[0]
        Wd = Q @ C
        nrng = np.random.default_rng([3, 1])
        th = []
        PD = Q[:, :k] @ Q[:, :k].T
        for t in range(T):
            g = A @ Wd
            th.append(np.sum((PD @ g) ** 2) / np.sum(g ** 2))
            G = g + Q @ (prob.sigma * nrng.standard_normal((d, n)))
            D, _ = sf.apply_filter(G, opt)
            Wd = Wd - eta * D
        check(f"eigenbasis == dense random-Q ({opt}), theta over {T} steps",
              np.abs(np.array(th) - out["theta"][0, :T]).max(), 1e-9)
        check(f"eigenbasis == dense random-Q ({opt}), final W",
              np.abs(Q.T @ Wd - out["W_final"][0]).max(), 1e-9)


def test_kron_equivalence():
    d, k, n, m = 30, 3, 8, 20
    mu = np.arange(1, n + 1) ** -1.0
    prob = sf.Problem(d, k, n, m, mu=mu, K=40)
    rng = np.random.default_rng(2)
    QA, _ = np.linalg.qr(rng.standard_normal((d, d)))
    QB, _ = np.linalg.qr(rng.standard_normal((n, n)))
    A = (QA * prob.lam) @ QA.T
    B = (QB * mu) @ QB.T
    opt, eta, T = "muon", 0.02, 30
    out = sf.run(prob, opt, eta, T, [5], log_idx=np.arange(T))
    C = sf.init_state(prob, [5])[0]
    Wd = QA @ C @ QB.T
    nrng = np.random.default_rng([5, 1])
    th = []
    for t in range(T):
        g = A @ Wd @ B
        ge = QA.T @ g @ QB            # Kronecker-Hessian eigen-coordinates
        th.append(np.sum(prob.maskf * ge ** 2) / np.sum(ge ** 2))
        G = g + QA @ (prob.sigma * nrng.standard_normal((d, n))) @ QB.T
        D, _ = sf.apply_filter(G, opt)
        Wd = Wd - eta * D
    check("Kronecker (M3) eigenbasis == dense A W B, theta", np.abs(np.array(th) - out["theta"][0, :T]).max(), 1e-9)


def test_scale_covariance():
    prob1 = sf.Problem(60, 6, 15, 20, sigma=0.5)
    a = 0.1
    prob2 = sf.Problem(60, 6, 15, 20, sigma=0.5 * a)
    T = 200
    for opt, p in (("muon", 0.0), ("ht0.25", 0.25), ("sgd", 1.0), ("ech6", 0.0)):
        o1 = sf.run(prob1, opt, 0.02, T, [0], init_scale=1.0)
        o2 = sf.run(prob2, opt, 0.02 * a ** (1 - p), T, [0], init_scale=a)
        check(f"scale covariance (eta,sigma,W0)->(a^(1-p) eta, a sigma, a W0) [{opt}]",
              np.nanmax(np.abs(o1["theta"] - o2["theta"])), 1e-8)


def test_sgd_onestep_formulas():
    prob = sf.Problem(80, 8, 20, 20)
    out = sf.run(prob, "sgd", sf.ETA0, 60, [0], ckpt_steps=[0, 30, 60])
    for t in (0, 30, 60):
        W = out["ckpts"][t][0]
        st = sf.onestep(prob, W, ["sgd"], N=4000, seed=1, gradproj=True)
        r = st["per_opt"]["sgd"]
        eD, eB = prob.eta_loss_deng(W)
        mD, sD = sf.loss_thresholds(r["Lq"][:, 0], r["Lq"][:, 3])
        mB, sB = sf.loss_thresholds(r["Lq"][:, 1], r["Lq"][:, 4])
        check(f"t={t}: MC eta_D^loss vs Deng Thm 9 (rel., 5 s.e. allowed)", abs(mD - eD) / eD, max(5 * sD / eD, 1e-3))
        check(f"t={t}: MC eta_B^loss vs Deng Thm 9 (rel., 5 s.e. allowed)", abs(mB - eB) / eB, max(5 * sB / eB, 1e-3))
        gD, _ = sf.loss_thresholds(r["Gq"][:, 0], r["Gq"][:, 2])
        check(f"t={t}: SGD F(P^D G) == P^D F(G)", abs(gD - mD) / mD, 1e-10)
        es, num, den = prob.eta_star_deng(W)
        ar = sf.align_response(st["aD"], st["aB"], r["Q"])
        if np.isfinite(ar["eta_star"]) and den > 0 and num > 0:
            check(f"t={t}: MC eta* vs Deng eq.(def-etatstar) (rel., 5 s.e. allowed)", abs(ar["eta_star"] - es) / es,
                  max(5 * ar["eta_star_se"] / es, 1e-3))
        else:
            print(f"   t={t}: eta* undefined (num={num:.3g}, den={den:.3g}); MC regime = {ar['regime']}")


def test_stationary_sgd():
    prob = sf.Problem(100, 10, 20, 20)
    out = sf.run(prob, "sgd", sf.ETA0, 1500, list(range(4)), init="stat")
    ls = sf.late_stats(out, 0.8)
    Lth = 0.5 * (prob.H * prob.beta(sf.ETA0)).sum()
    check("SGD started in its stationary law stays there: loss (rel.)", abs(ls["loss"].mean() - Lth) / Lth, 0.03)
    check("... and theta_late ~ Theorem-16 theta_inf", abs(ls["theta"].mean() - prob.theta_inf(sf.ETA0)), 0.02)


if __name__ == "__main__":
    cpu = sf.CpuLog("tests_sanity")
    test_filters()
    test_eigenbasis_equivalence()
    test_kron_equivalence()
    test_scale_covariance()
    test_sgd_onestep_formulas()
    test_stationary_sgd()
    print("all sanity checks passed")
    cpu.done()
