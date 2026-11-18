"""specfilt.py -- EXACT spectral-filter optimizers on Deng-style quadratics (numpy, float64).

Everything is done in the eigenbasis of the Hessian factors.  For the left-Hessian lift (M2),
L(W) = 1/2 tr(W^T A W) with A = Q diag(lam) Q^T, the spectral filter F(G) = U f(S) V^T satisfies
F(Q G) = Q F(G) and iid Gaussian gradient noise is rotation invariant, so the dynamics of
C = Q^T W is the dynamics with A = diag(lam).  The same holds for the Kronecker lift (M3),
L(W) = 1/2 tr(W^T A W B), with C = Q_A^T W Q_B.  (tests_sanity.py checks this numerically.)
In the eigenbasis
    gradient          = H * W            (entrywise, H_ij = lam_i mu_j = Kronecker-Hessian eigenvalue)
    loss              = 1/2 sum H W^2
    P^D (.)           = mask * (.)       (mask = the top-K entries of H; in M2 the first k rows)
    Deng's alignment  = sum_mask (H W)^2 / sum (H W)^2.

Optimizers ("opt" strings):  'sgd' | 'muon' | 'ht<p>' (f = s^p) | 'ech<r>' (exact-frame Echelon:
f = 1 on the top r singular directions, s / tau on the rest, tau = s_{r+1} = ||tail||_2) |
'echf<r>' (the same with the cheap upper estimate tau = ||tail||_F).
"""
import json
import os
import time

import numpy as np

ETA0 = 0.003      # Deng et al., Section 7 / quad_sim.py
SIGMA0 = 0.5      # quad_sim.py: noise = np.random.normal(0, sigma=0.5, d)
HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, "results")
FIG = os.path.join(HERE, "figs")


# --------------------------------------------------------------------------------------
# problem
# --------------------------------------------------------------------------------------
def deng_spectrum(d, k, m):
    """Eigenvalues exactly as in quad_sim.py::generate_positive_definite_matrix."""
    large = np.linspace(100, 80, k)
    small = np.linspace(7, 1, d - k)
    small = small * ((large[-1] / (m + 0.1)) / small[0])
    return np.concatenate([large, small])


class Problem:
    """Deng-style quadratic in the Hessian eigenbasis.

    mu=None           -> (M2) left-Hessian lift, dominant set = first k rows (n=1: Deng's vector model)
    mu=array, K=int   -> (M3) Kronecker lift, dominant set = K largest products lam_i mu_j
    noise='iso'       -> iid N(0, sigma^2) entries
    noise='propA'     -> row i has variance sigma^2 lam_i / mean(lam)  (Sigma ∝ A, same trace)
    """

    def __init__(self, d=200, k=20, n=50, m=20.0, sigma=SIGMA0, noise="iso", mu=None, K=None):
        self.d, self.k, self.n, self.m, self.sigma, self.noise = d, k, n, float(m), float(sigma), noise
        self.lam = deng_spectrum(d, k, m)
        self.kron = mu is not None
        self.mu = np.ones(n) if mu is None else np.asarray(mu, float)
        self.H = self.lam[:, None] * self.mu[None, :]
        mask = np.zeros((d, n), bool)
        if mu is None and K is None:
            mask[:k] = True
        else:
            K = k * n if K is None else int(K)
            idx = np.argsort(-self.H.ravel(), kind="stable")[:K]
            mask.flat[idx] = True
        self.mask = mask
        self.maskf = mask.astype(float)
        self.K = int(mask.sum())
        if noise == "iso":
            kap = sigma * np.ones((d, 1))
        elif noise == "propA":
            kap = sigma * np.sqrt(self.lam / self.lam.mean())[:, None]
        else:
            raise ValueError(noise)
        self.kap = kap                                  # per-entry noise std, (d,1)
        self.kap2 = (kap ** 2) * np.ones((d, n))        # per-entry noise variance, (d,n)

    # -- basic functionals (broadcast over leading batch dims) --
    def grad(self, W):
        return self.H * W

    def loss(self, W):
        return 0.5 * np.sum(self.H * W * W, axis=(-2, -1))

    def theta(self, G):
        g2 = G * G
        tot = g2.sum(axis=(-2, -1))
        return np.where(tot > 0, (g2 * self.maskf).sum(axis=(-2, -1)) / np.where(tot > 0, tot, 1.0), 0.0)

    # -- reference ratios --
    def ratio(self, power):
        h = self.H ** power
        return h[self.mask].sum() / h.sum()

    def gap_ratio(self):
        hs = np.sort(self.H.ravel())[::-1]
        return hs[self.K - 1] / hs[self.K]

    # -- Deng's closed forms for SGD (the matrix problem is a d*n-dimensional vector problem) --
    def beta(self, eta):
        return eta * self.kap2 / (2 * self.H - eta * self.H ** 2)

    def theta_inf(self, eta):
        """Theorem 16 (late phase): sum_D lam^2 beta / sum lam^2 beta."""
        w = self.H ** 2 * self.beta(eta)
        return w[self.mask].sum() / w.sum()

    def sgd_second_moment(self, eta, t, c0sq):
        """E c_{ij,t}^2 for constant-step SGD; t scalar or array (returns (..., d, n))."""
        t = np.asarray(t, float)[..., None, None]
        rho = (1 - eta * self.H) ** 2
        b = self.beta(eta)
        return rho ** t * c0sq + b * (1 - rho ** t)

    def sgd_theta_bar(self, eta, t, c0sq):
        """Ratio-of-expectations alignment E s^D_t / E s_t for constant-step SGD."""
        e = self.H ** 2 * self.sgd_second_moment(eta, t, c0sq)
        return (e * self.maskf).sum(axis=(-2, -1)) / e.sum(axis=(-2, -1))

    def sgd_loss_bar(self, eta, t, c0sq):
        return 0.5 * (self.H * self.sgd_second_moment(eta, t, c0sq)).sum(axis=(-2, -1))

    # -- SGD with the muon.py Nesterov-EMA momentum (exact second moments, 2x2 Lyapunov per eigen-direction) --
    def sgd_nesterov_theta(self, eta, beta, T=None, c0sq=0.0, window=None):
        """Exact ratio-of-expectations alignment of SGD with
               M <- beta M + (1-beta) G,   X = (1-beta) G + beta M,   w <- w - eta X      (G = h w + xi)
        i.e. the linear recursion z+ = T z + b xi for z = (w, M) with
               T = [[1 - eta (1-beta^2) h, -eta beta^2], [(1-beta) h, beta]],  b = (-eta (1-beta^2), 1-beta).
        T=None: stationary value (solves the 3x3 Lyapunov system per entry); otherwise iterates the covariance
        recursion from E w^2 = c0sq, M = 0 and returns the mean of theta_bar_t over the steps t in `window`
        (default: t >= 0.8 T).  Also returns the corresponding loss 1/2 sum h E w^2."""
        h, s2 = self.H, self.kap2
        t11, t12 = 1 - eta * (1 - beta ** 2) * h, -eta * beta ** 2 * np.ones_like(h)
        t21, t22 = (1 - beta) * h, beta * np.ones_like(h)
        b1, b2 = -eta * (1 - beta ** 2), (1 - beta)

        def ratio(a):
            e = h ** 2 * a
            return float((e * self.maskf).sum() / e.sum()), float(0.5 * (h * a).sum())

        if T is None:
            K = np.empty(h.shape + (3, 3))
            K[..., 0, 0], K[..., 0, 1], K[..., 0, 2] = t11 ** 2, 2 * t11 * t12, t12 ** 2
            K[..., 1, 0], K[..., 1, 1], K[..., 1, 2] = t11 * t21, t11 * t22 + t12 * t21, t12 * t22
            K[..., 2, 0], K[..., 2, 1], K[..., 2, 2] = t21 ** 2, 2 * t21 * t22, t22 ** 2
            q = np.stack([s2 * b1 * b1, s2 * b1 * b2, s2 * b2 * b2], axis=-1)[..., None]
            sol = np.linalg.solve(np.eye(3) - K, q)[..., 0]
            return ratio(sol[..., 0])
        a = c0sq * np.ones_like(h)
        b = np.zeros_like(h)
        c = np.zeros_like(h)
        if window is None:
            window = [t for t in range(T + 1) if t >= 0.8 * T]
        wset = set(int(t) for t in window)
        th, ls = [], []
        for t in range(T + 1):
            if t in wset:
                r = ratio(a)
                th.append(r[0])
                ls.append(r[1])
            a, b, c = (t11 ** 2 * a + 2 * t11 * t12 * b + t12 ** 2 * c + s2 * b1 * b1,
                       t11 * t21 * a + (t11 * t22 + t12 * t21) * b + t12 * t22 * c + s2 * b1 * b2,
                       t21 ** 2 * a + 2 * t21 * t22 * b + t22 ** 2 * c + s2 * b2 * b2)
        return float(np.mean(th)), float(np.mean(ls))

    def blocks(self, W):
        """s, tau, q (=sum lam^4 c^2), e (=sum lam^2 kap^2), nloss (=sum lam kap^2) for S in D, B."""
        out = {}
        w2 = W * W
        for name, mk in (("D", self.maskf), ("B", 1 - self.maskf)):
            out["s" + name] = (mk * self.H ** 2 * w2).sum()
            out["tau" + name] = (mk * self.H ** 3 * w2).sum()
            out["q" + name] = (mk * self.H ** 4 * w2).sum()
            out["e" + name] = (mk * self.H ** 2 * self.kap2).sum()
            out["nl" + name] = (mk * self.H * self.kap2).sum()
        return out

    def eta_star_deng(self, W):
        """Eq. (def-etatstar-body); returns (eta_star, numerator, denominator)."""
        b = self.blocks(W)
        num = 2 * (b["sB"] * b["tauD"] - b["sD"] * b["tauB"])
        den = b["sB"] * (b["qD"] + b["eD"]) - b["sD"] * (b["qB"] + b["eB"])
        return (num / den if den != 0 else np.inf), num, den

    def eta_loss_deng(self, W):
        """Theorem 9: eta^loss_S = 2 s^S / (tau^S + n^loss_S)."""
        b = self.blocks(W)
        return 2 * b["sD"] / (b["tauD"] + b["nlD"]), 2 * b["sB"] / (b["tauB"] + b["nlB"])

    def theta_crit_deng(self, W):
        """Theorem 10: root in (0,1) of alpha th^2 + beta th + gamma."""
        b = self.blocks(W)
        s = b["sD"] + b["sB"]
        al = s * (b["tauD"] / b["sD"] - b["tauB"] / b["sB"])
        be = -al + b["nlB"] + b["nlD"]
        ga = -b["nlD"]
        if abs(al) < 1e-300:
            return -ga / be
        disc = np.sqrt(be * be - 4 * al * ga)
        r = np.array([(-be + disc) / (2 * al), (-be - disc) / (2 * al)])
        r = r[(r > 0) & (r < 1)]
        return float(r[0]) if len(r) else np.nan

    def g_gap(self):
        hs = np.sort(self.H.ravel())[::-1]
        K = self.K
        rho = K / (hs.size - K)
        smax, smin = self.kap2.max(), self.kap2.min()
        return 1.0 / (1.0 + (smax / smin) / rho * (hs[K] / hs[K - 1]) ** 2)

    def theta_star_deng(self, W):
        """Theorem 5: theta* = r0/(1+r0), r0 the positive root of a r^2 + (a-m-h) r - h = 0."""
        hs = self.H.ravel()
        a = self.kap2.min() * (hs[~self.mask.ravel()] ** 2).sum()
        h = self.kap2.max() * (hs[self.mask.ravel()] ** 2).sum()
        st = ((self.H * W) ** 2).sum()
        mm = st * (hs.max() ** 2 - hs.min() ** 2)
        bq = a - mm - h
        r0 = (-bq + np.sqrt(bq * bq + 4 * a * h)) / (2 * a)
        return r0 / (1 + r0)


# --------------------------------------------------------------------------------------
# spectral filters
# --------------------------------------------------------------------------------------
def parse_opt(opt):
    if opt == "sgd":
        return ("sgd", None)
    if opt == "muon":
        return ("muon", None)
    if opt.startswith("ht"):
        return ("ht", float(opt[2:]))
    if opt.startswith("echf"):
        return ("echf", int(opt[4:]))
    if opt.startswith("ech"):
        return ("ech", int(opt[3:]))
    raise ValueError(opt)


def fvals(s, opt):
    """Filter values f(s) for singular values s (..., n), sorted descending."""
    kind, par = parse_opt(opt)
    if kind == "sgd":
        return s
    if kind == "muon":
        return np.ones_like(s)
    if kind == "ht":
        return s ** par
    if kind in ("ech", "echf"):
        r = par
        n = s.shape[-1]
        if r >= n:
            return np.ones_like(s)
        if kind == "ech":
            tau = s[..., r:r + 1]                       # exact spectral norm of the tail, ||T||_2 = s_{r+1}
        else:
            tau = np.sqrt((s[..., r:] ** 2).sum(-1, keepdims=True))     # cheap upper estimate ||T||_F >= ||T||_2
        f = np.where(tau > 0, s / np.where(tau > 0, tau, 1.0), 0.0)
        f[..., :r] = 1.0
        return f
    raise ValueError(opt)


def svd(X):
    return np.linalg.svd(X, full_matrices=False)


def apply_filter(X, opt, usv=None):
    """F(X) = U f(S) V^T with an exact (LAPACK gesdd) SVD.  Returns (Delta, (U, s, Vt))."""
    if usv is None:
        usv = svd(X)
    U, s, Vt = usv
    if opt == "sgd":
        return X, usv
    f = fvals(s, opt)
    return (U * f[..., None, :]) @ Vt, usv


def calibrate(prob, opt, nmc=200, seed=12345, sigma_in_scale=1.0, eta_sgd=ETA0):
    """Pure-noise (linear-response) calibration of a filter, used for the noise-dominated regime.

    For G = S + Xi with a small signal S and Gaussian noise Xi (row i has variance kap_i^2), Stein's lemma
    gives the first-order response of the filtered update, row by row (eigenbasis of A):
        E[row_i F(S + Xi)] ~ c_i * row_i S,     c_i = E<row_i Xi, row_i F(Xi)> / (n kap_i^2),
    and the injected noise   nu_i = E||row_i F(Xi)||^2.
    For isotropic noise c_i = c = E[sum_j s_j f(s_j)] / (sigma^2 d n) and nu_i = E[sum_j f(s_j)^2] / d.
    (Note c != c1 := E mean_j f(s_j)/s_j, the naive 'E[R]' coefficient; c1 is returned for reference.)
    Noise-dominated dynamics of row i:  w <- (1 - eta c_i lam_i) w - eta * noise(nu_i), hence
        stationary  E||w_i||^2 ~ eta nu_i / (2 c_i lam_i),   loss floor ~ eta * sum_i nu_i / (4 c_i).
    'rule' learning rate = the step with SGD's loss floor (eta_sgd * n * tr(Sigma) / 4):
        eta_rule = eta_sgd * n * tr(Sigma) / sum_i (nu_i / c_i)      [iso: eta_sgd E<Xi,F(Xi)> / E||F(Xi)||_F^2]
    and eta_eff = eta_rule * c (c = row-mean of c_i) is the SGD-equivalent drift step.
    sigma_in_scale rescales the noise seen by the filter (Nesterov averaging): 'eta_rule_in' is the step
    that keeps the same drift step eta_eff for that smaller filter-input noise.
    """
    rng = np.random.default_rng(seed)
    d, n = prob.d, prob.n
    c_i = np.zeros(d)
    nu_i = np.zeros(d)
    c1 = f2 = 0.0
    c_in = 0.0
    for _ in range(nmc):
        Xi = prob.kap * rng.standard_normal((d, n))
        U, s, Vt = svd(Xi)
        f = fvals(s, opt)
        Fx = Xi if opt == "sgd" else (U * f) @ Vt
        c_i += (Xi * Fx).sum(1)
        nu_i += (Fx * Fx).sum(1)
        c1 += np.mean(f / s)
        f2 += np.mean(f * f)
        if sigma_in_scale != 1.0:
            s2 = s * sigma_in_scale
            c_in += np.sum(s2 * fvals(s2, opt))
    c_i /= nmc * n * prob.kap[:, 0] ** 2
    nu_i /= nmc
    c1 /= nmc
    f2 /= nmc
    trS = float((prob.kap ** 2).sum())
    eta_rule = eta_sgd * n * trS / float(np.sum(nu_i / c_i))
    c = float(c_i.mean())
    k = prob.k
    out = dict(c=c, c1=c1, f2=f2, eta_rule=eta_rule, eta_eff=eta_rule * c,
               c_D=float(c_i[:k].mean()), c_B=float(c_i[k:].mean()),
               nu_D=float(nu_i[:k].mean()), nu_B=float(nu_i[k:].mean()),
               c_rows=c_i, nu_rows=nu_i)
    if sigma_in_scale != 1.0:
        c_in = c_in / nmc / (sigma_in_scale ** 2 * trS * n)
        out["c_in"] = c_in
        out["eta_rule_in"] = out["eta_eff"] / c_in
    return out


def linresp_theta(prob, calib, eta, t=None):
    """Linear-response (noise-dominated) prediction of the alignment for the left-Hessian lift (M2):
    row i behaves like SGD with drift step eta*c_i and injected noise nu_i, so
        E||w_i||^2 = eta nu_i / (c_i lam_i (2 - eta c_i lam_i)) * (1 - (1 - eta c_i lam_i)^(2t))   [zero init]
    and theta = sum_D lam_i^2 E||w_i||^2 / sum_i lam_i^2 E||w_i||^2.  t=None gives the stationary value."""
    c, nu, lam = np.asarray(calib["c_rows"]), np.asarray(calib["nu_rows"]), prob.lam
    q = eta * nu / (c * lam * (2 - eta * c * lam))
    if t is not None:
        q = q * (1 - (1 - eta * c * lam) ** (2 * np.asarray(t, float)[..., None]))
    w = lam ** 2 * q
    return w[..., :prob.k].sum(-1) / w.sum(-1)


def nesterov_noise_scale(beta):
    """Std of the noise in X_t = (1-b) G_t + b M_t, M_t = b M_{t-1} + (1-b) G_t, relative to G's."""
    return np.sqrt((1 - beta) ** 2 * ((1 + beta) ** 2 + beta ** 4 / (1 - beta ** 2)))


# --------------------------------------------------------------------------------------
# trajectories
# --------------------------------------------------------------------------------------
def default_log_idx(T, dense=300, stride=10):
    idx = list(range(0, min(dense, T))) + list(range(min(dense, T), T, stride))
    return np.array(sorted(set(idx)), int)


SV_NAMES = ["s1", "s2", "s3", "s_k", "s_k+1", "s_med", "s_min"]


def _sv_stats(s, k):
    n = s.shape[-1]
    ii = [0, min(1, n - 1), min(2, n - 1), min(k - 1, n - 1), min(k, n - 1), n // 2, n - 1]
    return s[..., ii]


def _overlap(prob, U, Vt, kk):
    """Mass of the top-kk singular components in the dominant Hessian set:
    (1/kk) sum_{l<kk} sum_{ij in D} u_l[i]^2 v_l[j]^2.  In M2 this is ||P^D U_kk||_F^2 / kk."""
    if not prob.kron:
        return (U[..., :prob.k, :kk] ** 2).sum(axis=(-2, -1)) / kk
    U2 = U[..., :, :kk] ** 2
    V2 = Vt[..., :kk, :] ** 2
    return np.einsum("...dl,dn,...ln->...", U2, prob.maskf, V2) / kk


def init_state(prob, seeds, init="gauss", init_scale=1.0, eta_stat=ETA0):
    d, n = prob.d, prob.n
    W = np.zeros((len(seeds), d, n))
    for a, sd in enumerate(seeds):
        rng = np.random.default_rng([int(sd), 0])
        Z = rng.standard_normal((d, n))
        if init == "gauss":
            W[a] = init_scale * Z
        elif init == "zero":
            W[a] = 0.0
        elif init == "stat":            # SGD's stationary law at step eta_stat
            W[a] = np.sqrt(prob.beta(eta_stat)) * Z
        else:
            raise ValueError(init)
    return W


def run(prob, opt, eta, T, seeds, init="gauss", init_scale=1.0, beta=0.0, nesterov=True,
        log_idx=None, true_sv_stride=5, ckpt_steps=(), proj=None, proj_mode="update",
        W0=None, noise_stream=1, sigma=None, blowup=1e12):
    """Run  W <- W - eta * F(X_t),  X_t = G_t (beta=0) or the Nesterov-averaged gradient
    (M <- beta M + (1-beta) G;  X = (1-beta) G + beta M, as in muon.py), G_t = H*W + noise.

    proj in {None,'D','B'}: proj_mode='update' uses mask_S * F(X);  proj_mode='grad' uses F(mask_S * X).
    Logged at the steps in log_idx (state BEFORE the update of that step) and at t=T (loss/theta only).
    """
    seeds = list(seeds)
    S, d, n, k = len(seeds), prob.d, prob.n, prob.k
    H, kap = prob.H, (prob.kap if sigma is None else sigma * np.ones((d, 1)))
    noisy = bool(np.any(kap > 0))
    W = init_state(prob, seeds, init, init_scale) if W0 is None else np.array(W0, float).reshape(S, d, n).copy()
    rngs = [np.random.default_rng([int(sd), int(noise_stream)]) for sd in seeds]
    if log_idx is None:
        log_idx = default_log_idx(T)
    log_idx = np.asarray(log_idx, int)
    logset = {int(t): a for a, t in enumerate(log_idx)}
    L = len(log_idx) + 1
    kk = min(k, n)
    nan = lambda *sh: np.full((S,) + sh, np.nan)
    out = dict(loss=nan(L), theta=nan(L), theta_stoch=nan(L), theta_inp=nan(L), upd_frac=nan(L),
               upd_norm=nan(L), gnorm_true=nan(L), sv_inp=nan(L, 7), ovl_inp=nan(L),
               sv_true=nan(L, 7), ovl_true=nan(L))
    mk = None
    if proj is not None:
        mk = prob.maskf if proj == "D" else 1.0 - prob.maskf
    M = np.zeros_like(W)
    ckpts = {}
    ckset = set(int(c) for c in ckpt_steps)
    is_sgd = opt == "sgd"
    diverged = False
    n_svd = 0
    Z = np.empty((S, d, n))
    for t in range(T):
        if t in ckset:
            ckpts[t] = W.copy()
        Gt = H * W
        if noisy:
            for a in range(S):
                Z[a] = rngs[a].standard_normal((d, n))
            G = Gt + kap * Z
        else:
            G = Gt
        if beta > 0:
            M = beta * M + (1 - beta) * G
            X = (1 - beta) * G + beta * M if nesterov else M
        else:
            X = G
        Xf = X * mk if (mk is not None and proj_mode == "grad") else X
        a = logset.get(t)
        if is_sgd and a is None:
            Delta = Xf
        else:
            Delta, (U, s, Vt) = apply_filter(Xf, opt)
            n_svd += S
        if mk is not None and proj_mode == "update":
            Delta = Delta * mk
        if a is not None:
            out["loss"][:, a] = prob.loss(W)
            out["theta"][:, a] = prob.theta(Gt)
            out["theta_stoch"][:, a] = prob.theta(G)
            out["theta_inp"][:, a] = prob.theta(X)
            out["upd_frac"][:, a] = prob.theta(Delta)
            out["upd_norm"][:, a] = np.sqrt((Delta * Delta).sum(axis=(-2, -1)))
            out["gnorm_true"][:, a] = np.sqrt((Gt * Gt).sum(axis=(-2, -1)))
            out["sv_inp"][:, a] = _sv_stats(s, k)
            out["ovl_inp"][:, a] = _overlap(prob, U, Vt, kk)
            if a % true_sv_stride == 0:
                Ut, st, Vtt = svd(Gt)
                out["sv_true"][:, a] = _sv_stats(st, k)
                out["ovl_true"][:, a] = _overlap(prob, Ut, Vtt, kk)
        W = W - eta * Delta
        if not np.all(np.isfinite(W)) or np.max(np.abs(W)) > blowup:
            diverged = True
            break
    if T in ckset:
        ckpts[T] = W.copy()
    if not diverged:
        out["loss"][:, -1] = prob.loss(W)
        out["theta"][:, -1] = prob.theta(H * W)
    out["t"] = np.concatenate([log_idx, [T]])
    out["W_final"] = W
    out["ckpts"] = ckpts
    out["diverged"] = diverged
    out["n_svd"] = n_svd
    return out


def late_stats(out, frac=0.2):
    """Per-seed time averages over the last `frac` of the logged steps (t >= (1-frac) T)."""
    t = out["t"]
    T = t[-1]
    sel = t >= (1 - frac) * T
    res = {}
    for key in ("loss", "theta", "theta_stoch", "theta_inp", "upd_frac", "ovl_inp", "ovl_true", "gnorm_true",
                "upd_norm"):
        with np.errstate(invalid="ignore"):
            res[key] = np.nanmean(out[key][:, sel], axis=1)
    for key in ("sv_inp", "sv_true"):
        res[key] = np.nanmean(out[key][:, sel], axis=1)
    return res


# --------------------------------------------------------------------------------------
# one-step Monte Carlo (alignment response and projected-loss response)
# --------------------------------------------------------------------------------------
def onestep(prob, W, opts, N=64, seed=0, gradproj=True):
    """Common-random-number one-step statistics at the state W (d,n) for several filters.

    For every noise draw one SVD of G = H*W + Xi serves all filters.  Per draw and filter we store the
    coefficients of the exact polynomials in the step size eta:
      alignment:  theta(W - eta D) = (aD - 2 eta bD + eta^2 cD) / (a - 2 eta b + eta^2 c)
                  bS = <P^S H W, P^S H D>,  cS = ||P^S H D||^2,  aS = ||P^S H W||^2
      loss, update projected on S (S = D, B, or F = full):
                  L(W - eta P^S D) - L(W) = -eta l1S + (eta^2/2) l2S,
                  l1S = <H W, P^S D>,  l2S = <P^S D, H P^S D>
      loss, filter applied to the projected gradient, D^S = F(P^S G):
                  g1S = <H W, D^S>,  g2S = <D^S, H D^S>
    """
    rng = np.random.default_rng([int(seed), 7])
    d, n = prob.d, prob.n
    H, mk = prob.H, prob.maskf
    mkB = 1.0 - mk
    Gt = H * W
    aD = float((mk * Gt * Gt).sum())
    aB = float((mkB * Gt * Gt).sum())
    res = {o: dict(Q=np.zeros((N, 4)), Lq=np.zeros((N, 6)), Gq=np.zeros((N, 4)), nrm2=np.zeros(N),
                   fracD=np.zeros(N)) for o in opts}
    gn2 = np.zeros(N)
    noisy = bool(np.any(prob.kap > 0))
    Z = None
    for i in range(N):
        if noisy:
            # antithetic pairs: draw 2j uses +Z_j, draw 2j+1 uses -Z_j (use pair_avg() before taking s.e.)
            Z = rng.standard_normal((d, n)) if i % 2 == 0 else -Z
            G = Gt + prob.kap * Z
        else:
            G = Gt
        gn2[i] = (G * G).sum()
        usv = svd(G)
        if gradproj:
            usvD = svd(G * mk)
            usvB = svd(G * mkB)
        for o in opts:
            D_, _ = apply_filter(G, o, usv)
            HD = H * D_
            r = res[o]
            r["Q"][i] = ((mk * Gt * HD).sum(), (mkB * Gt * HD).sum(), (mk * HD * HD).sum(), (mkB * HD * HD).sum())
            l1D, l1B = (mk * Gt * D_).sum(), (mkB * Gt * D_).sum()
            l2D, l2B = (mk * HD * D_).sum(), (mkB * HD * D_).sum()
            r["Lq"][i] = (l1D, l1B, l1D + l1B, l2D, l2B, l2D + l2B)
            d2 = (D_ * D_).sum()
            r["nrm2"][i] = d2
            r["fracD"][i] = (mk * D_ * D_).sum() / d2 if d2 > 0 else np.nan
            if gradproj:
                DD, _ = apply_filter(G * mk, o, usvD)
                DB, _ = apply_filter(G * mkB, o, usvB)
                r["Gq"][i] = ((Gt * DD).sum(), (Gt * DB).sum(), (H * DD * DD).sum(), (H * DB * DB).sum())
    return dict(aD=aD, aB=aB, loss=float(prob.loss(W)), theta=aD / (aD + aB) if aD + aB > 0 else 0.0,
                gn2=gn2, per_opt=res, N=N)


def pair_avg(x):
    """Average the antithetic pairs produced by onestep (rows 2j, 2j+1)."""
    x = np.asarray(x)
    if x.shape[0] < 2:
        return x
    m = (x.shape[0] // 2) * 2
    return 0.5 * (x[0:m:2] + x[1:m:2])


def align_response(aD, aB, Q, n_boot=200, seed=0):
    """Ratio-of-expectations alignment response from per-draw (bD, bB, cD, cB).

    thetabar(eta) - theta = [ -2 eta q_lin + eta^2 q_quad ] / (a (a - 2 eta b + eta^2 c)),
        q_lin = aB bD - aD bB,   q_quad = aB cD - aD cB.
    regime: 'dec<inc' (q_lin>0,q_quad>0: decrease below eta*, increase above -- Deng's low-alignment case),
            'dec'     (q_lin>0,q_quad<=0: decrease for every eta),
            'inc'     (q_lin<=0,q_quad>0: increase for every eta),
            'inc<dec' (q_lin<0,q_quad<0: increase below eta*, decrease above).
    """
    def stat(Qm):
        bD, bB, cD, cB = Qm
        ql = aB * bD - aD * bB
        qq = aB * cD - aD * cB
        es = 2 * ql / qq if ql * qq > 0 else np.nan
        return ql, qq, es
    ql, qq, es = stat(Q.mean(0))
    if ql > 0 and qq > 0:
        reg = "dec<inc"
    elif ql > 0:
        reg = "dec"
    elif qq > 0:
        reg = "inc"
    else:
        reg = "inc<dec"
    rng = np.random.default_rng(seed)
    N = Q.shape[0]
    bs = np.array([stat(Q[rng.integers(0, N, N)].mean(0))[2] for _ in range(n_boot)]) if N > 1 else np.array([es])
    with np.errstate(invalid="ignore"):
        se = float(np.nanstd(bs)) if np.isfinite(bs).sum() > 1 else np.nan
    return dict(q_lin=float(ql), q_quad=float(qq), eta_star=float(es), eta_star_se=se, regime=reg,
                frac_boot_defined=float(np.isfinite(bs).mean()))


def dtheta_curves(aD, aB, Q, etas):
    """Returns (E[theta(eta)] - theta0  [expectation of the ratio, mean over draws], its s.e.,
    ratio-of-expectations curve)."""
    etas = np.asarray(etas, float)[None, :]
    bD, bB, cD, cB = (Q[:, j:j + 1] for j in range(4))
    num = aD - 2 * etas * bD + etas ** 2 * cD
    den = (aD + aB) - 2 * etas * (bD + bB) + etas ** 2 * (cD + cB)
    th0 = aD / (aD + aB)
    th = pair_avg(num / den - th0)          # per-draw ratio, then antithetic-pair average
    m = Q.mean(0)
    numb = aD - 2 * etas[0] * m[0] + etas[0] ** 2 * m[2]
    denb = (aD + aB) - 2 * etas[0] * (m[0] + m[1]) + etas[0] ** 2 * (m[2] + m[3])
    se = th.std(0, ddof=1) / np.sqrt(th.shape[0]) if th.shape[0] > 1 else np.zeros(etas.shape[1])
    return th.mean(0), se, numb / denb - th0


def first_sign_change(etas, y):
    """Smallest eta at which y changes sign (log-linear interpolation); nan if none.  Also returns the
    sign of y at the smallest eta (-1: decreasing, +1: increasing)."""
    sg = np.sign(y)
    s0 = sg[0]
    idx = np.where(sg[1:] * sg[:-1] < 0)[0]
    if len(idx) == 0:
        return np.nan, s0
    i = idx[0]
    x0, x1, y0, y1 = np.log(etas[i]), np.log(etas[i + 1]), y[i], y[i + 1]
    return float(np.exp(x0 - y0 * (x1 - x0) / (y1 - y0))), s0


def loss_thresholds(L1, L2, n_boot=200, seed=0):
    """eta^loss = 2 E[l1] / E[l2] from per-draw l1, l2 (bootstrap s.e.)."""
    est = 2 * L1.mean() / L2.mean()
    rng = np.random.default_rng(seed)
    N = len(L1)
    if N > 1:
        ii = rng.integers(0, N, (n_boot, N))
        bs = 2 * L1[ii].mean(1) / L2[ii].mean(1)
        se = float(bs.std())
    else:
        se = 0.0
    return float(est), se


# --------------------------------------------------------------------------------------
# io helpers
# --------------------------------------------------------------------------------------
class CpuLog:
    """Appends CPU seconds of each script run to results/cpu_log.jsonl."""

    def __init__(self, name):
        self.name = name
        self.t0 = time.process_time()
        self.w0 = time.time()

    def done(self, **extra):
        rec = dict(name=self.name, cpu_s=round(time.process_time() - self.t0, 1),
                   wall_s=round(time.time() - self.w0, 1), **extra)
        os.makedirs(RES, exist_ok=True)
        with open(os.path.join(RES, "cpu_log.jsonl"), "a") as fh:
            fh.write(json.dumps(rec) + "\n")
        print("[cpu]", rec, flush=True)
        return rec


def jsonable(o):
    if isinstance(o, dict):
        return {str(k): jsonable(v) for k, v in o.items()}
    if isinstance(o, (list, tuple)):
        return [jsonable(v) for v in o]
    if isinstance(o, np.ndarray):
        return jsonable(o.tolist())
    if isinstance(o, (np.floating,)):
        o = float(o)
    if isinstance(o, (np.integer,)):
        return int(o)
    if isinstance(o, (np.bool_,)):
        return bool(o)
    if isinstance(o, float) and not np.isfinite(o):
        return None if np.isnan(o) else ("inf" if o > 0 else "-inf")
    return o


def save_json(path, obj):
    with open(path, "w") as fh:
        json.dump(jsonable(obj), fh, indent=1)


def mean_sd(x):
    x = np.asarray(x, float)
    return float(np.mean(x)), (float(np.std(x, ddof=1)) if x.size > 1 else 0.0)
