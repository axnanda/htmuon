"""Shared helpers for the one-step theory of spectrally filtered updates in Deng's model.

Everything here is plain numpy (float64).  "Direct" functions work on the actual gradient matrix
through numpy's SVD; "formula" functions evaluate the closed forms of
notes/research/theory_onestep.md in eigen-coordinates.

Conventions (as in the note):
  A = U diag(lam) U^T (d x d),  W in R^{d x n},  C = U^T W (rows c_i),  G = A W (+ noise),
  s^S = sum_{i in S} lam_i^2 |c_i|^2,  theta = s^D / (s^D + s^B),  L = 1/2 sum_i lam_i |c_i|^2.
  A spectral filter is F(G) = sum_k f(sigma_k) u_k v_k^T with f(0) = 0.
"""
import json
import numpy as np

RTOL0 = 1e-10  # singular values below RTOL0 * sigma_max are treated as exact zeros (f(0) = 0)


# ----------------------------------------------------------------------------------------------
# filters: each returns a function fvec(S) acting on an array of singular values in ANY order
# (state-dependent filters such as Echelon / NS5 look at the whole array)
# ----------------------------------------------------------------------------------------------
def _nz(S):
    S = np.asarray(S, dtype=float)
    smax = S.max() if S.size else 0.0
    return S > RTOL0 * max(smax, 1e-300)


def f_sgd():
    return lambda S: np.asarray(S, dtype=float).copy()


def f_muon():
    return lambda S: _nz(S).astype(float)


def f_ht(p):
    def fvec(S):
        S = np.asarray(S, dtype=float)
        out = np.zeros_like(S)
        nz = _nz(S)
        out[nz] = S[nz] ** p
        return out
    return fvec


def echelon_tau(S, r):
    """tau = sigma_{r+1} (the (r+1)-th largest singular value); 0 if rank <= r."""
    S = np.asarray(S, dtype=float)
    nz = _nz(S)
    Ss = np.sort(S[nz])[::-1]
    return float(Ss[r]) if r < Ss.size else 0.0


def f_echelon(r):
    """Echelon(r) with an exact top-r frame: f(sigma) = min(sigma, tau)/tau, tau = sigma_{r+1}."""
    def fvec(S):
        S = np.asarray(S, dtype=float)
        nz = _nz(S)
        tau = echelon_tau(S, r)
        out = np.zeros_like(S)
        if tau <= 0.0:
            out[nz] = 1.0
        else:
            out[nz] = np.minimum(S[nz], tau) / tau
        return out
    return fvec


NS_COEF = (3.4445, -4.7750, 2.0315)


def f_ns5(steps=5):
    """Muon as implemented (zeropower_via_newtonschulz5): Frobenius normalisation + odd quintic."""
    a, b, c = NS_COEF

    def fvec(S):
        S = np.asarray(S, dtype=float)
        x = S / (np.sqrt(np.sum(S ** 2)) + 1e-7)
        for _ in range(steps):
            x = a * x + b * x ** 3 + c * x ** 5
        return x
    return fvec


FILTERS = {
    "sgd": f_sgd(),
    "muon": f_muon(),
    "ht0.125": f_ht(0.125),
    "ht0.25": f_ht(0.25),
    "ht0.5": f_ht(0.5),
    "ns5": f_ns5(),
}
HOMOG_DEG = {"sgd": 1.0, "muon": 0.0, "ht0.125": 0.125, "ht0.25": 0.25, "ht0.5": 0.5, "ns5": 0.0}


# ----------------------------------------------------------------------------------------------
# direct matrix implementations
# ----------------------------------------------------------------------------------------------
def apply_filter(G, fvec):
    """F(G) = U f(S) V^T through numpy's SVD of the actual matrix."""
    U, S, Vt = np.linalg.svd(G, full_matrices=False)
    return (U * fvec(S)) @ Vt


def polar_factor(H):
    """Partial-isometry polar factor of H (singular values > 0 -> 1)."""
    U, S, Vt = np.linalg.svd(H, full_matrices=False)
    return (U * _nz(S).astype(float)) @ Vt


def echelon_headtail(G, r):
    """Literal head-tail construction with an exact top-r left frame:
    O = U_r P + T / tau,  P = polar(U_r^T G),  T = G - U_r U_r^T G,  tau = ||T||_2."""
    U, S, Vt = np.linalg.svd(G, full_matrices=False)
    Ur = U[:, :r]
    H = Ur.T @ G
    P = polar_factor(H) if r > 0 else H
    T = G - Ur @ H
    tau = np.linalg.norm(T, 2) if T.size else 0.0
    O = Ur @ P
    if tau > RTOL0 * max(S.max(), 1e-300):
        O = O + T / tau
    return O


def ns5_matrix(G, steps=5):
    """numpy port of zeropower_via_newtonschulz5 (float64 instead of bfloat16)."""
    a, b, c = NS_COEF
    X = G.copy()
    tr = G.shape[0] > G.shape[1]
    if tr:
        X = X.T
    X = X / (np.linalg.norm(X) + 1e-7)
    for _ in range(steps):
        Amat = X @ X.T
        Bmat = b * Amat + c * Amat @ Amat
        X = a * X + Bmat @ X
    return X.T if tr else X


# ----------------------------------------------------------------------------------------------
# problems and states
# ----------------------------------------------------------------------------------------------
def rand_orth(d, rng):
    Q, R = np.linalg.qr(rng.standard_normal((d, d)))
    return Q * np.sign(np.diag(R))


def make_spectrum(d, k, m, rng, kind="spread"):
    """lam_1 >= .. >= lam_k > lam_{k+1} >= .. >= lam_d > 0 with lam_k / lam_{k+1} = m."""
    if kind == "twolevel":
        lam = np.concatenate([np.full(k, float(m)), np.ones(d - k)])
    else:
        dom = m * (1.0 + rng.uniform(0, 1.5, size=k))
        dom[np.argmin(dom)] = m
        blk = rng.uniform(0.1, 1.0, size=d - k)
        blk[np.argmax(blk)] = 1.0
        lam = np.concatenate([np.sort(dom)[::-1], np.sort(blk)[::-1]])
    return lam


def block_masks(d, k):
    D = np.zeros(d, dtype=bool)
    D[:k] = True
    return D, ~D


def commuting_state(U, a, n, rng):
    """W = U diag(a) Q with Q (d x n) having orthonormal rows on the support of a.
    Needs #supp(a) <= n.  Returns W, Qfull (d x n; rows off the support are zero)."""
    d = U.shape[0]
    supp = np.flatnonzero(a > 0)
    assert supp.size <= n
    Qn = rand_orth(n, rng)
    Q = np.zeros((d, n))
    Q[supp] = Qn[: supp.size]
    return U @ (a[:, None] * Q), Q


def energies(lam, C, D):
    e = lam ** 2 * np.sum(C ** 2, axis=1)
    return e[D].sum(), e[~D].sum()


def theta_of(lam, C, D):
    sD, sB = energies(lam, C, D)
    return sD / (sD + sB)


def loss_of(lam, C):
    return 0.5 * np.sum(lam * np.sum(C ** 2, axis=1))


# ----------------------------------------------------------------------------------------------
# commuting-case formulas (Theorems 3.1-3.3 of the note)
# ----------------------------------------------------------------------------------------------
def commuting_coeffs(lam, a, D, fvec):
    """Returns dict with sigma, f, nu (effective curvature), s^S, tau_f^S, u_f^S, p_f, q_f."""
    sig = lam * a
    fs = fvec(sig)
    out = dict(sig=sig, f=fs)
    for name, S in (("D", D), ("B", ~D)):
        out["s" + name] = np.sum(sig[S] ** 2)
        out["tau" + name] = np.sum(lam[S] * sig[S] * fs[S])
        out["u" + name] = np.sum(lam[S] ** 2 * fs[S] ** 2)
        out["N" + name] = np.sum(sig[S] * fs[S])            # <G, Delta_S>
        out["R" + name] = np.sum(lam[S] * fs[S] ** 2)       # <Delta_S, A Delta_S>
    out["q"] = 2.0 * (out["sD"] * out["tauB"] - out["sB"] * out["tauD"])
    out["p"] = out["sB"] * out["uD"] - out["sD"] * out["uB"]
    with np.errstate(divide="ignore", invalid="ignore"):
        out["nu"] = np.where(a > 0, fs / np.where(a > 0, a, 1.0), 0.0)
    return out


def commuting_step(lam, a, D, fvec, eta):
    """Predicted row norms, block energies, alignment and loss after one filtered step."""
    co = commuting_coeffs(lam, a, D, fvec)
    a_new = np.abs(a - eta * co["f"])
    sDn = co["sD"] - 2 * eta * co["tauD"] + eta ** 2 * co["uD"]
    sBn = co["sB"] - 2 * eta * co["tauB"] + eta ** 2 * co["uB"]
    s, sn = co["sD"] + co["sB"], sDn + sBn
    dtheta = eta * (co["p"] * eta + co["q"]) / (s * sn) if sn > 0 else np.nan
    dL = -eta * (co["ND"] + co["NB"]) + 0.5 * eta ** 2 * (co["RD"] + co["RB"])
    return dict(a_new=a_new, sD=sDn, sB=sBn, dtheta=dtheta, dL=dL, co=co)


# ----------------------------------------------------------------------------------------------
# Gaussian-smoothed filters (Theorem 3.9 of the note):  X ~ N(sig, kap^2)
# ----------------------------------------------------------------------------------------------
def fbar_muon(sig, kap):
    """E[sign(X)] = erf(sig / (sqrt(2) kap))."""
    from scipy import special
    return special.erf(sig / (np.sqrt(2) * kap))


def fbar_ht(sig, kap, p):
    """E[sign(X)|X|^p] (Kummer function form)."""
    from scipy import special
    return (sig * kap ** (p - 1) * 2 ** ((p + 1) / 2) * special.gamma(p / 2 + 1) / np.sqrt(np.pi)
            * special.hyp1f1((1 - p) / 2, 1.5, -sig ** 2 / (2 * kap ** 2)))


def f2_ht(sig, kap, p):
    """E|X|^{2p} (Kummer function form)."""
    from scipy import special
    return (kap ** (2 * p) * 2 ** p * special.gamma(p + 0.5) / np.sqrt(np.pi)
            * special.hyp1f1(-p, 0.5, -sig ** 2 / (2 * kap ** 2)))


def jdump(obj, path):
    def conv(o):
        if isinstance(o, (np.floating,)):
            return float(o)
        if isinstance(o, (np.integer,)):
            return int(o)
        if isinstance(o, (np.bool_,)):
            return bool(o)
        if isinstance(o, np.ndarray):
            return o.tolist()
        raise TypeError(type(o))
    with open(path, "w") as fh:
        json.dump(obj, fh, indent=1, default=conv)
