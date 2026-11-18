"""Shared helpers for the long-run (constant step size) experiments.

Models (names as in the research context):
  (M1) vector model  x in R^d, gradient g = A x + xi, filter F(g) = f(|g|) g/|g|.
  (M2) left-Hessian model  W in R^{d x n}, L = 1/2 tr(W^T A W), G = A W + Xi.
All simulations are done in the eigenbasis of A, i.e. with C = U^T W and A = diag(lam).
The alignment is Deng et al.'s  theta = sum_{i in D} lam_i^2 |c_i|^2 / sum_i lam_i^2 |c_i|^2
(computed from the CLEAN gradient Lam C, as in the paper).

Spectral filters F(G) = U f(S) V^T (numpy ports of the torch code in llama_pretraining/muon.py):
  sgd      f(s) = s
  muon     f(s) = 1                       (exact polar factor;  svd_project_uvt)
  ht(p)    f(s) = s^p                     (msign_generalized_ht_v2, default p = 0.125)
  ech(r)   f(s_i) = 1 for i <= r, s_i / s_{r+1} for i > r   (Echelon, exact top-r frame,
           tau = ||T||_2 = s_{r+1};  O = U_r P + T / tau)
  ns5      f(s) = phi5(s / ||G||_F)       (zeropower_via_newtonschulz5, 5 quintic steps)
"""
import json
import os

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, "results")
FIGS = os.path.join(HERE, "figs")
os.makedirs(RES, exist_ok=True)
os.makedirs(FIGS, exist_ok=True)


# --------------------------------------------------------------------------- spectrum
def spectrum(d, k, m, dom_spread=1.5, bulk_lo=0.5):
    """lam_1 = dom_spread*m >= ... >= lam_k = m  >  lam_{k+1} = 1 >= ... >= lam_d = bulk_lo.

    So the gap ratio lam_k / lam_{k+1} is exactly m and the bulk stays in [bulk_lo, 1]."""
    lam_D = np.linspace(dom_spread * m, m, k) if k > 1 else np.array([float(m)])
    lam_B = np.linspace(1.0, bulk_lo, d - k) if d - k > 1 else np.array([1.0])
    return np.concatenate([lam_D, lam_B])


def theta_from_energy(E, k):
    """E[..., d] = lam_i^2 |c_i|^2  ->  alignment with the dominant block {0..k-1}."""
    return E[..., :k].sum(-1) / E.sum(-1)


def ratio_pred(lam, k, q):
    """sum_D lam^q / sum lam^q (computed stably for large q)."""
    w = (lam / lam.max()) ** q
    return w[:k].sum() / w.sum()


# --------------------------------------------------------------------------- Deng (SGD)
def deng_beta(lam, eta, kap2):
    return eta * kap2 / (2 * lam - eta * lam ** 2)


def deng_theta_inf(lam, k, eta, kap2=1.0):
    b = deng_beta(lam, eta, kap2) * lam ** 2
    return b[:k].sum() / b.sum()


def deng_tstar(lam, k, eta, c0sq, kap2, smax):
    """t* of Theorem 15 (floor omitted); returns nan when the formula is not defined."""
    beta = deng_beta(lam, eta, kap2) * np.ones_like(lam)
    psiD = (lam[:k] ** 2).sum()
    lam1, lamk, lamk1, lamd = lam[0], lam[k - 1], lam[k], lam[-1]
    den = 2 * (lamk - lamk1) / eta - (lam1 ** 2 - lamd ** 2)
    if den <= 0:
        return float("nan"), float("nan")
    delta = smax * psiD * lam1 ** 2 / (lamd ** 2 * lamk ** 2 * den)
    varrho = (c0sq[:k] - beta[:k]).sum()
    arg = varrho / (delta - beta[:k].sum())
    if arg <= 0 or delta - beta[:k].sum() <= 0:
        return float("nan"), delta
    return float(np.log(arg) / (-2 * np.log(abs(1 - eta * lam1)))), float(delta)


# --------------------------------------------------------------------------- filters
NS_A, NS_B, NS_C = 3.4445, -4.7750, 2.0315


def ns5_scalar(x, steps=5):
    """Singular-value map of zeropower_via_newtonschulz5 (input already divided by ||G||_F)."""
    for _ in range(steps):
        x2 = x * x
        x = x * (NS_A + NS_B * x2 + NS_C * x2 * x2)
    return x


def fvals(s, kind, p=0.125, r=0):
    """Filtered singular values f(s) for a vector s sorted in DECREASING order."""
    if kind == "sgd":
        return s.copy()
    if kind == "muon":
        return np.ones_like(s)
    if kind == "ht":
        return s ** p
    if kind == "ech":
        f = np.ones_like(s)
        if r < len(s) and s[r] > 0:
            f[r:] = s[r:] / s[r]
        return f
    if kind == "ns5":
        return ns5_scalar(s / (np.sqrt((s * s).sum()) + 1e-7))
    if kind == "htns":  # idealised htmuon_ns: NS5 polar factor times exact (G^T G)^{p/2}
        return ns5_scalar(s / (np.sqrt((s * s).sum()) + 1e-7)) * s ** p
    raise ValueError(kind)


def spectral_filter(G, kind, p=0.125, r=0, use_svd=False):
    """F(G) = U f(S) V^T.  Default: via the Gram matrix of the smaller side (fast);
    use_svd=True uses numpy's SVD directly (reference implementation)."""
    d, n = G.shape
    if use_svd:
        U, s, Vt = np.linalg.svd(G, full_matrices=False)
        return (U * fvals(s, kind, p, r)) @ Vt
    if d <= n:
        w, U = np.linalg.eigh(G @ G.T)
        s = np.sqrt(np.clip(w[::-1], 0, None))
        U = U[:, ::-1]
        fac = fvals(s, kind, p, r) / np.maximum(s, 1e-300)
        return (U * fac) @ (U.T @ G)
    w, V = np.linalg.eigh(G.T @ G)
    s = np.sqrt(np.clip(w[::-1], 0, None))
    V = V[:, ::-1]
    fac = fvals(s, kind, p, r) / np.maximum(s, 1e-300)
    return (G @ (V * fac)) @ V.T


# --------------------------------------------------------------------------- mean field
def mf_g(lam, eta, nu, p):
    """Root g >= nu of  2 (g^2 - nu^2) = eta*lam*g^(1+p)   (row-decoupled mean-field law).
    p = 1 (SGD) needs eta*lam < 2.  Vectorised bisection on log g."""
    lam = np.asarray(lam, dtype=float)
    if p == 1.0:
        return nu / np.sqrt(1 - eta * lam / 2)
    if nu == 0:
        return (eta * lam / 2) ** (1 / (1 - p))
    lo = np.full_like(lam, nu)
    hi = np.maximum(2 * nu, 2 * (eta * lam) ** (1 / (1 - p)) + 2 * nu)
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        h = 2 * (mid ** 2 - nu ** 2) - eta * lam * mid ** (1 + p)
        lo = np.where(h < 0, mid, lo)
        hi = np.where(h < 0, hi, mid)
    return 0.5 * (lo + hi)


def mf_energy(lam, eta, nu, p):
    """Stationary clean-gradient energy per eigen-direction, E_i = g_i^2 - nu^2."""
    g = mf_g(lam, eta, nu, p)
    return 0.5 * eta * lam * g ** (1 + p) if p < 1 else g ** 2 - nu ** 2


def mf_theta(lam, k, eta, nu, p):
    E = mf_energy(lam, eta, nu, p)
    return E[:k].sum() / E.sum()


def mf_energy_echelon(lam, eta, nu, r, tau_edge=None):
    """Heuristic mean field for Echelon(r): directions 1..r+1 follow the Muon law (p = 0),
    the others are SGD with step eta/tau, tau = g_{r+1} (optionally floored by tau_edge)."""
    lam = np.asarray(lam, dtype=float)
    E = mf_energy(lam, eta, nu, 0.0)
    if r + 1 >= len(lam):
        return E
    g = mf_g(lam, eta, nu, 0.0)
    tau = g[r]
    if tau_edge is not None:
        tau = max(tau, tau_edge)
    x = eta * lam[r + 1:] / tau
    E = E.copy()
    E[r + 1:] = nu ** 2 * x / (2 - x)
    return E


def m1_selfconsistent(lam, eta, sigma, p):
    """(M1) frozen-effective-step heuristic: eta_eff solves
       (eta/eta_eff)^(2/(1-p)) = sigma^2 d + sigma^2 eta_eff sum_i lam_i/(2 - eta_eff lam_i)."""
    d = len(lam)
    lo, hi = 0.0, 2.0 / lam.max()
    for _ in range(200):
        x = 0.5 * (lo + hi)
        lhs = (2 / (1 - p)) * (np.log(eta) - np.log(x))
        rhs = np.log(sigma ** 2 * d + sigma ** 2 * x * (lam / (2 - x * lam)).sum())
        if lhs > rhs:
            lo = x
        else:
            hi = x
    x = 0.5 * (lo + hi)
    E = sigma ** 2 * x * lam / (2 - x * lam)
    return x, E


# --------------------------------------------------------------------------- io
def save_json(name, obj):
    path = os.path.join(RES, name)

    def conv(o):
        if isinstance(o, np.ndarray):
            return o.tolist()
        if isinstance(o, (np.floating,)):
            return float(o)
        if isinstance(o, (np.integer,)):
            return int(o)
        raise TypeError(type(o))

    with open(path, "w") as fh:
        json.dump(obj, fh, default=conv, indent=1)
    return path


def msd(x):
    x = np.asarray(x, dtype=float)
    return float(x.mean()), float(x.std(ddof=1) if x.size > 1 else 0.0)


# --------------------------------------------------------------------------- matrix simulator
def run_m2(lam, n, kind, eta, sigma, T, burn, rng, C0, p=0.125, r=0, beta=None, k=None,
           record_theta=False, record_every=1):
    """(M2) in the eigenbasis:  C <- C - eta * F(u),  G = lam*C + sigma*Xi,
    u = G (no momentum) or the Nesterov-EMA combination of muon.py (beta given).
    Returns dict with time-averaged clean energies E_i = lam_i^2 |c_i|^2 (after burn-in),
    time-averaged theta, mean (r+1)-th singular value of the filter input, final C."""
    d = len(lam)
    C = C0.copy()
    lamc = lam[:, None]
    M = np.zeros_like(C) if beta is not None else None
    Eacc = np.zeros(d)
    thacc = 0.0
    tauacc = 0.0
    s1acc = 0.0
    cnt = 0
    ths = []
    wide = d <= n
    for t in range(T):
        Gc = lamc * C
        if record_theta or t >= burn:
            E = (Gc * Gc).sum(1)
            th = E[:k].sum() / E.sum()
            if record_theta and t % record_every == 0:
                ths.append(th)
            if t >= burn:
                Eacc += E
                thacc += th
                cnt += 1
        G = Gc + sigma * rng.standard_normal(C.shape) if sigma > 0 else Gc
        if beta is not None:
            M = beta * M + (1 - beta) * G
            G = (1 - beta) * G + beta * M
        if kind == "sgd":
            C = C - eta * G
            continue
        if wide:
            w, U = np.linalg.eigh(G @ G.T)
        else:
            w, U = np.linalg.eigh(G.T @ G)
        s = np.sqrt(np.clip(w[::-1], 1e-300, None))
        U = U[:, ::-1]
        if kind == "muon":
            fac = 1.0 / s
        elif kind == "ht":
            fac = s ** (p - 1.0)
        elif kind == "ech":
            fac = 1.0 / s
            if r < len(s):
                fac[r:] = 1.0 / s[r]
        else:
            raise ValueError(kind)
        if t >= burn:
            tauacc += s[min(r, len(s) - 1)]
            s1acc += s[0]
        if wide:
            C = C - eta * ((U * fac) @ (U.T @ G))
        else:
            C = C - eta * ((G @ (U * fac)) @ U.T)
    cnt = max(cnt, 1)
    return dict(E=Eacc / cnt, theta_time=thacc / cnt, tau=tauacc / cnt, s1=s1acc / cnt, C=C,
                theta_curve=np.array(ths))


# --------------------------------------------------------------------------- momentum (Nesterov-EMA, muon.py)
def mom_xcrit(beta):
    """Linear stability edge of  c+ = c - (x/lam) u,  u = Nesterov-EMA(lam c):  x < x_c(beta).
    x_c(0) = 2 (plain GD);  x_c(0.95) = 26.9."""
    return 2 * (1 + beta) / ((1 - beta) * (1 + 2 * beta))


def mom_two_cycle_const(p, beta):
    """Energy constant of the exact period-2 orbit with momentum:  lam^2 a*^2 = C (eta lam)^q,
    C = x_c^(2-q)/4, q = 2/(1-p).   (beta = 0: C = 2^(-q).)"""
    q = 2 / (1 - p)
    return mom_xcrit(beta) ** (2 - q) / 4


def _mom_stationary(lam, eta_i, nu, beta):
    """Stationary second moments of the frozen-step linear recursion with Nesterov-EMA momentum.
    Returns (E|c|^2, E|u|^2) or None if the recursion is unstable."""
    A = np.array([[1 - eta_i * (1 - beta ** 2) * lam, -eta_i * beta ** 2], [(1 - beta) * lam, beta]])
    if np.abs(np.linalg.eigvals(A)).max() >= 1 - 1e-12:
        return None
    b = np.array([-eta_i * (1 - beta ** 2), 1 - beta])
    P = np.linalg.solve(np.eye(4) - np.kron(A, A), nu ** 2 * np.outer(b, b).ravel()).reshape(2, 2)
    w = np.array([(1 - beta ** 2) * lam, beta ** 2])
    return P[0, 0], w @ P @ w + (1 - beta ** 2) ** 2 * nu ** 2


def mf_momentum_energy(lam, eta, nu, p, beta):
    """Heuristic (H4): row-decoupled mean field with momentum.  For each direction solve
    g^2 = E|u|^2 at the frozen step eta_i = eta g^(p-1); return clean energies lam^2 E|c|^2 and g."""
    lam = np.asarray(lam, dtype=float)
    E = np.empty_like(lam)
    gs = np.empty_like(lam)
    for i, l in enumerate(lam):
        lo = np.log((1 - beta ** 2) * nu) - 5.0
        hi = np.log(nu + (eta * l) ** (1 / (1 - p))) + 5.0
        for _ in range(100):
            mid = 0.5 * (lo + hi)
            g = np.exp(mid)
            st = _mom_stationary(l, eta * g ** (p - 1), nu, beta)
            if st is None or g * g - st[1] < 0:
                lo = mid
            else:
                hi = mid
        g = np.exp(0.5 * (lo + hi))
        st = _mom_stationary(l, eta * np.exp(hi) ** (p - 1), nu, beta)
        E[i] = l ** 2 * st[0]
        gs[i] = g
    return E, gs
