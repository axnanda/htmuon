"""
spfilters.py -- numpy ports of the Muon / HTMuon speed-ups (llama_pretraining/muon.py) and of the
Echelon head-tail update (echelon-lean: FastMuon/HeadTail.lean, Polish.lean, Cost.lean), plus the
Deng-style matrix quadratic (model M2) used by every experiment in this directory.

Port notes (deviations from the torch originals are listed in README.md, section "Port fidelity"):
  * every function below follows the torch source line by line; the source line numbers of
    /home/user/htmuon/llama_pretraining/muon.py are given in the docstrings;
  * default precision is float64 (the originals use bfloat16 for Newton-Schulz and float32 for the
    SVD / Gram-root / stream paths); `prec` in {'f64','f32','bf16'} selects the working precision,
    'bf16' being an emulation (float32 arithmetic, every operation result rounded to bfloat16,
    round-to-nearest-even);
  * no distributed logic, no weight decay (the experiments use weight_decay = 0), no aux-Adam group.

Only numpy is required.
"""
import math
import numpy as np

# --------------------------------------------------------------------------------------------
# robust SVD
# --------------------------------------------------------------------------------------------
# numpy's SVD (LAPACK gesdd, divide and conquer) occasionally fails with "SVD did not converge" on
# FINITE but numerically rank-deficient matrices.  This happens here in noise-free runs with a large
# gap m, where an Echelon optimizer drives the bulk part of the momentum to ~1e-13 of the head (first
# seen: ech_r16_ideal, m = 100, sigma = 0, seed 0).  In that case we fall back to the QR-iteration
# driver gesvd (scipy).  SVD_FALLBACKS counts the fallbacks of the current process.
SVD_FALLBACKS = 0


def svd(X, full_matrices=False):
    """np.linalg.svd with a gesvd fallback (see above).  Returns (U, S, Vh)."""
    global SVD_FALLBACKS
    try:
        return np.linalg.svd(X, full_matrices=full_matrices)
    except np.linalg.LinAlgError:
        if not np.all(np.isfinite(X)):
            raise
        import scipy.linalg as sl
        SVD_FALLBACKS += 1
        return sl.svd(X, full_matrices=full_matrices, lapack_driver='gesvd')


def spec_norm(X):
    """Spectral norm ||X||_2 through the robust SVD."""
    if X.size == 0:
        return 0.0
    return float(svd(X)[1][0])

# --------------------------------------------------------------------------------------------
# precision helpers
# --------------------------------------------------------------------------------------------

def bf16_round(x):
    """Round a float32 array to the nearest bfloat16 value (round-to-nearest-even), returned as float32."""
    x32 = np.ascontiguousarray(x, dtype=np.float32)
    u = x32.view(np.uint32).astype(np.uint64)
    lsb = (u >> np.uint64(16)) & np.uint64(1)
    u = u + np.uint64(0x7FFF) + lsb
    u = (u >> np.uint64(16)) << np.uint64(16)
    return u.astype(np.uint32).view(np.float32).reshape(x32.shape)


def _ident(x):
    return x


def _prec(prec):
    """Return (dtype, rounding function) for a precision tag."""
    if prec == 'f64':
        return np.float64, _ident
    if prec == 'f32':
        return np.float32, _ident
    if prec == 'bf16':
        return np.float32, bf16_round
    raise ValueError(prec)


# --------------------------------------------------------------------------------------------
# 1. Muon: Newton-Schulz zeroth power and exact polar factor
# --------------------------------------------------------------------------------------------

NS5_COEFFS = (3.4445, -4.7750, 2.0315)


def zeropower_via_newtonschulz5(G, steps=5, prec='f64'):
    """Port of muon.py:5-31.  Quintic Newton-Schulz with coefficients (3.4445, -4.7750, 2.0315) on
    G / (||G||_F + 1e-7); the matrix is transposed when rows > cols."""
    a, b, c = NS5_COEFFS
    dt, rnd = _prec(prec)
    X = rnd(np.asarray(G, dtype=dt))
    tall = G.shape[-2] > G.shape[-1]
    if tall:
        X = X.T
    # Ensure spectral norm is at most 1
    X = rnd(X / (rnd(np.linalg.norm(X).astype(dt)) + dt(1e-7)))
    for _ in range(steps):
        A = rnd(X @ X.T)
        B = rnd(rnd(b * A) + rnd(c * rnd(A @ A)))
        X = rnd(rnd(a * X) + rnd(B @ X))
    if tall:
        X = X.T
    return X


def ns5_scalar(x, steps=5):
    """The scalar map applied by NS5 to a singular value x = sigma / ||G||_F."""
    a, b, c = NS5_COEFFS
    x = np.asarray(x, dtype=np.float64)
    for _ in range(steps):
        x = a * x + b * x ** 3 + c * x ** 5
    return x


def polar_svd(G):
    """Exact Muon filter: U V^T for the thin SVD G = U S V^T (float64)."""
    U, _, Vh = svd(np.asarray(G, dtype=np.float64), full_matrices=False)
    return U @ Vh


# --------------------------------------------------------------------------------------------
# 2. HTMuon: exact filter and the Newton-Schulz Gram root
# --------------------------------------------------------------------------------------------

def msign_generalized_ht_v2(g, p=0.25, prec='f64'):
    """Port of muon.py:320-332: U S^p V^T by SVD (float32 in the original)."""
    dt, _ = _prec('f32' if prec == 'bf16' else prec)
    U, S, Vh = svd(np.asarray(g, dtype=dt), full_matrices=False)
    Sp = S ** dt(p)
    return (U * Sp[None, :]) @ Vh


def gram_root_1_16_via_newtonschulz(G, power, ns_steps=5, eps=1e-6, prec='f64'):
    """Port of muon.py:83-131.  (G^T G + eps I)^(power/2) by repeated coupled Newton-Schulz matrix
    square roots: val = round(log_{1/2}(power)) + 1 square roots, each with `ns_steps` iterations
    on S / ||S||_F.  (float32 in the original.)"""
    dt, _ = _prec('f32' if prec == 'bf16' else prec)
    G_work = np.asarray(G, dtype=dt)
    A = G_work.T @ G_work
    n = A.shape[-1]
    I = np.eye(n, dtype=dt)
    A = A + dt(eps) * I
    S = A
    val = math.log(power, 0.5) + 1
    val = int(round(val))
    for _ in range(val):
        alpha = np.linalg.norm(S)
        alpha = max(alpha, dt(eps))
        S_tilde = S / alpha
        # Newton-Schulz for matrix square root of S_tilde
        Y = S_tilde.copy()
        Z = I.copy()
        for _ in range(ns_steps):
            T = dt(3.0) * I - Z @ Y
            Y = dt(0.5) * (Y @ T)
            Z = dt(0.5) * (T @ Z)
        S = dt(np.sqrt(alpha)) * Y
        S = dt(0.5) * (S + S.T)
        S = S + dt(eps) * I
    return S


def gram_root_scalar(lam, power=0.125, ns_steps=5, eps=1e-6, fro=None):
    """Scalar model of gram_root_1_16_via_newtonschulz for a spectrum `lam` of G^T G (array):
    the matrix iteration acts on each eigenvalue independently, coupled only through the Frobenius
    normalisation.  Returns the eigenvalues of the output (ideal value: (lam+eps)^(power/2))."""
    s = np.asarray(lam, dtype=np.float64) + eps
    val = int(round(math.log(power, 0.5) + 1))
    for _ in range(val):
        alpha = max(np.sqrt(np.sum(s ** 2)), eps)
        y = s / alpha
        z = np.ones_like(y)
        for _ in range(ns_steps):
            t = 3.0 - z * y
            y = 0.5 * y * t
            z = 0.5 * t * z
        s = np.sqrt(alpha) * y + eps
    return s


# --------------------------------------------------------------------------------------------
# 3. HTMuon streaming QR
# --------------------------------------------------------------------------------------------

def _init_v_matrix(M, rank=None, dt=np.float64):
    """Port of muon.py:1349-1359: first k columns of I_n."""
    m, n = M.shape
    k = min(m, n) if rank is None else min(rank, m, n)
    return np.eye(n, dtype=dt)[:, :k]


def _col_l2_normalize(X, eps=1e-8):
    """Port of muon.py:1362-1380."""
    col_norms = np.linalg.norm(X, axis=0)
    U = X / np.maximum(col_norms, eps)[None, :]
    small = col_norms <= eps
    if small.any():
        U[:, small] = 0.0
    return U, col_norms


def msign_generalized_ht_v2_stream_qr(g, V_prev=None, p=0.25, rank=None, eps=1e-8, prec='f64'):
    """Port of muon.py:1383-1444.  One warm-started step of orthogonal iteration:
        V_t = QR(M^T M V_{t-1}),  U_t = ColNorm(M V_t),  Sigma_t = diag(U_t^T M V_t),
        out = U_t Sigma_t^p V_t^T.
    (float32 in the original.)  Returns (out, V_t)."""
    dt, _ = _prec('f32' if prec == 'bf16' else prec)
    G = np.asarray(g, dtype=dt)
    m, n = G.shape
    k = min(m, n) if rank is None else min(rank, m, n)
    if V_prev is None or V_prev.shape != (n, k) or V_prev.dtype != dt:
        V_prev = _init_v_matrix(G, rank=k, dt=dt)
    Y = G.T @ (G @ V_prev)
    V_t, _ = np.linalg.qr(Y, mode='reduced')
    GV = G @ V_t
    U_t, _ = _col_l2_normalize(GV, eps=eps)
    sigma_t = np.sum(U_t * GV, axis=0)
    sigma_t = np.maximum(sigma_t, 0.0)
    sigma_p = np.where(sigma_t > eps, sigma_t ** dt(p), 0.0).astype(dt)
    out = (U_t * sigma_p[None, :]) @ V_t.T
    return out, V_t


# --------------------------------------------------------------------------------------------
# 4. Echelon head-tail update
# --------------------------------------------------------------------------------------------

def cubic_step(O):
    """Polish.lean `cubicStep`: O' = 1.5 O - 0.5 O O^T O."""
    return 1.5 * O - 0.5 * (O @ (O.T @ O))


class Echelon:
    """Rank-r head-tail direction  O = U P + T / tau  (HeadTail.lean `htDir`), with
        H = U^T X,  P = polar factor of the small r x n matrix H,  T = X - U H  (`tail`).

    frame = 'tracked': U is carried across calls; the frame used at call t is QR(X_{t-1} H_{t-1}^T)
                       = QR(X_{t-1} X_{t-1}^T U_{t-1}), i.e. ONE subspace-iteration step per call,
                       one call of lag (the three s*l*r products of Cost.lean: U^T X, U(P - H/tau),
                       X H^T).  First call: U = QR(X X^T QR(X Omega)), Omega Gaussian n x r.
    frame = 'exact'  : U = exact top-r left singular vectors of the current X (reference).
    tau   = 'pi'     : `pi_steps` warm-started power-iteration steps on T^T T (a slightly LOW
                       estimate of ||T||_2; `last_tau_ratio` records tau / ||T||_2 when
                       `diagnose=True`);
            'fro'    : ||T||_F (cheap upper bound);
            'exact'  : ||T||_2 from an SVD (reference).
    polish           : one cubic Newton-Schulz step on O (Polish.lean).
    """

    def __init__(self, r, frame='tracked', tau='pi', polish=False, pi_steps=2, seed=0,
                 diagnose=False):
        self.r = int(r)
        self.frame = frame
        self.tau = tau
        self.polish = polish
        self.pi_steps = pi_steps
        self.rng = np.random.default_rng([int(seed), 7919])
        self.U = None
        self.v = None
        self.diagnose = diagnose
        self.last_tau = np.nan
        self.last_tau_ratio = np.nan
        self.last_frame_err = np.nan

    def parts(self, X):
        """Head-tail pieces for the current input (and frame update for 'tracked'):
        returns dict(U, P, T, tau_pi | tau) -- used by __call__ and by the shadow experiments, which
        build the tau='pi' / tau='fro' / polished variants from ONE tracked frame."""
        X = np.asarray(X, dtype=np.float64)
        d, n = X.shape
        r = min(self.r, d, n)
        if self.frame == 'exact':
            Uf, _, _ = svd(X, full_matrices=False)
            U = Uf[:, :r]
        else:
            if self.U is None or self.U.shape != (d, r):
                Om = self.rng.standard_normal((n, r))
                U0, _ = np.linalg.qr(X @ Om)
                U0, _ = np.linalg.qr(X @ (X.T @ U0))
                self.U = U0
            U = self.U
        H = U.T @ X                                   # r x n
        Uh, _, Vhh = svd(H, full_matrices=False)
        P = Uh @ Vhh                                  # polar factor of the small matrix
        T = X - U @ H                                 # tail
        out = dict(U=U, P=P, T=T)
        if self.tau == 'exact':
            out['tau'] = spec_norm(T)
        else:
            # power iteration (always run for 'pi' and 'fro' objects so that both scales are
            # available from one tracked frame)
            v = self.v
            if v is None or v.shape != (n,):
                v = self.rng.standard_normal(n)
                v /= np.linalg.norm(v)
            for _ in range(self.pi_steps):
                w = T.T @ (T @ v)
                nw = np.linalg.norm(w)
                if nw <= 1e-300:
                    break
                v = w / nw
            self.v = v
            out['tau_pi'] = np.linalg.norm(T @ v)
            out['tau_fro'] = np.linalg.norm(T)
            out['tau'] = out['tau_fro'] if self.tau == 'fro' else out['tau_pi']
        if self.diagnose:
            t2 = spec_norm(T)
            self.last_tau_ratio = out['tau'] / t2 if t2 > 0 else np.nan
            Uf, _, _ = svd(X, full_matrices=False)
            Ue = Uf[:, :r]
            # mean squared-cosine deficit of the tracked frame w.r.t. the exact top-r left
            # singular subspace: 1 - ||Ue^T U||_F^2 / r  (0 = exact)
            self.last_frame_err = 1.0 - np.sum((Ue.T @ U) ** 2) / r
        if self.frame == 'tracked':
            Un, _ = np.linalg.qr(X @ H.T)             # next frame: one subspace-iteration step
            self.U = Un
        return out

    @staticmethod
    def assemble(parts, tau, polish=False):
        O = parts['U'] @ parts['P']
        if tau > 1e-300:
            O = O + parts['T'] / tau
        if polish:
            O = cubic_step(O)
        return O

    def __call__(self, X):
        parts = self.parts(X)
        self.last_tau = parts['tau']
        return self.assemble(parts, parts['tau'], self.polish)


# --------------------------------------------------------------------------------------------
# 5. Update rules (momentum handling of muon.py) and optimizer objects
# --------------------------------------------------------------------------------------------

def nesterov_lerp(grad, momentum, beta=0.95, nesterov=True):
    """Port of the first two lines of every *_update in muon.py (e.g. 353-355):
        momentum.lerp_(grad, 1 - beta);  update = grad.lerp_(momentum, beta) if nesterov else momentum
    Returns (update_input, new_momentum)."""
    momentum = momentum + (1.0 - beta) * (grad - momentum)
    upd = grad + beta * (momentum - grad) if nesterov else momentum
    return upd, momentum


def shape_factor(shape):
    """max(1, rows/cols)**0.5 (muon.py:359)."""
    return max(1.0, shape[-2] / shape[-1]) ** 0.5


class Opt:
    """One optimizer = momentum rule + spectral filter + state.  `direction(grad)` returns the
    update direction O (shape factor included); the caller applies  W <- W - lr * O.

    kind:
      'sgd'          plain SGD, no momentum (Deng's baseline)                       O = g
      'sgdm'         identity filter on the Nesterov-lerp momentum                  O = M
      'muon_exact'   U V^T by SVD                                                   (x shape factor)
      'muon_ns5'     muon_update (muon.py:353-360)
      'ht_exact'     muon_generalized_ht_update_v2 (muon.py:425-432)
      'ht_ns'        muon_generalized_ht_update_v2_acc (muon.py:435-444)
      'ht_interval'  HTMuonIntervalWithAuxAdam.step (muon.py:1645-1696): step counter incremented
                     first, HT (exact SVD) when step % interval == 0, muon_update (NS5) otherwise
      'ht_avg'       reference only: the time-averaged filter ((interval-1) NS5 + HT) / interval,
                     applied at every step
      'ht_stream'    muon_generalized_ht_update_v2_stream (muon.py:1447-1485), V carried in state
      'echelon'      Echelon(r) object (see class Echelon) in place of the Newton-Schulz step
    """

    def __init__(self, kind, shape, beta=0.95, nesterov=True, power=0.125, ns_steps=5,
                 ns_steps_2=5, interval=5, rank=None, qr_eps=1e-8, prec='f64',
                 ech_r=4, ech_frame='tracked', ech_tau='pi', ech_polish=False, seed=0,
                 diagnose=False):
        self.kind = kind
        self.shape = tuple(shape)
        self.beta = beta
        self.nesterov = nesterov
        self.power = power
        self.ns_steps = ns_steps
        self.ns_steps_2 = ns_steps_2
        self.interval = interval
        self.rank = rank
        self.qr_eps = qr_eps
        self.prec = prec
        self.sf = shape_factor(self.shape)
        self.momentum = np.zeros(self.shape)
        self.step_idx = 0
        self.V = None
        self.last_input = None       # matrix fed to the filter (after momentum)
        self.last_was_ht = None
        if kind == 'echelon':
            self.ech = Echelon(ech_r, frame=ech_frame, tau=ech_tau, polish=ech_polish, seed=seed,
                               diagnose=diagnose)

    # -- the filter alone (no momentum, no shape factor); used by the fidelity experiments
    def filter(self, M):
        k = self.kind
        if k in ('sgd', 'sgdm'):
            return M
        if k == 'muon_exact':
            return polar_svd(M)
        if k == 'muon_ns5':
            return np.asarray(zeropower_via_newtonschulz5(M, self.ns_steps, self.prec), dtype=np.float64)
        if k == 'ht_exact':
            return np.asarray(msign_generalized_ht_v2(M, self.power, self.prec), dtype=np.float64)
        if k == 'ht_ns':
            u1 = zeropower_via_newtonschulz5(M, self.ns_steps, self.prec)
            u2 = gram_root_1_16_via_newtonschulz(M, self.power, ns_steps=self.ns_steps_2, prec=self.prec)
            dt, rnd = _prec(self.prec)
            return np.asarray(rnd(u1 @ rnd(u2.astype(dt))), dtype=np.float64)
        if k == 'ht_interval':
            self.step_idx += 1
            self.last_was_ht = (self.step_idx % self.interval == 0)
            if self.last_was_ht:
                return np.asarray(msign_generalized_ht_v2(M, self.power, self.prec), dtype=np.float64)
            return np.asarray(zeropower_via_newtonschulz5(M, self.ns_steps, self.prec), dtype=np.float64)
        if k == 'ht_avg':
            w = 1.0 / self.interval
            return ((1.0 - w) * np.asarray(zeropower_via_newtonschulz5(M, self.ns_steps, self.prec), dtype=np.float64)
                    + w * np.asarray(msign_generalized_ht_v2(M, self.power, self.prec), dtype=np.float64))
        if k == 'ht_stream':
            out, self.V = msign_generalized_ht_v2_stream_qr(M, self.V, p=self.power, rank=self.rank,
                                                            eps=self.qr_eps, prec=self.prec)
            return np.asarray(out, dtype=np.float64)
        if k == 'echelon':
            return self.ech(M)
        raise ValueError(k)

    def direction(self, grad):
        if self.kind == 'sgd':
            self.last_input = grad
            return grad
        M, self.momentum = nesterov_lerp(grad, self.momentum, self.beta, self.nesterov)
        self.last_input = M
        O = self.filter(M)
        if self.kind == 'sgdm':
            return O
        return O * self.sf


# registry: name -> (family, constructor kwargs).  family = which exact filter the optimizer
# approximates (and whose tuned learning rate it inherits).
def optimizer_registry(k):
    """All optimizers of the study for a problem with dominant dimension k."""
    reg = {
        'sgd': ('sgd', dict(kind='sgd')),
        'sgdm': ('sgdm', dict(kind='sgdm')),
        'muon_exact': ('muon', dict(kind='muon_exact')),
        'muon_ns5': ('muon', dict(kind='muon_ns5')),
        'ht_exact': ('ht', dict(kind='ht_exact')),
        'ht_ns': ('ht', dict(kind='ht_ns')),
        'ht_interval': ('ht', dict(kind='ht_interval', interval=5)),
        'ht_avg': ('ht', dict(kind='ht_avg', interval=5)),
        'ht_stream': ('ht', dict(kind='ht_stream', rank=None)),
        'ht_stream_rk': ('ht', dict(kind='ht_stream', rank=k)),
        'ht_stream_r4': ('ht', dict(kind='ht_stream', rank=4)),
    }
    rs = [1, 4, 16, k]
    for r in rs:
        tag = 'k' if r == k else str(r)
        reg[f'ech_r{tag}'] = ('muon', dict(kind='echelon', ech_r=r, ech_frame='tracked', ech_tau='pi'))
        reg[f'ech_r{tag}_ideal'] = ('muon', dict(kind='echelon', ech_r=r, ech_frame='exact', ech_tau='exact'))
    for r in [4, k]:
        tag = 'k' if r == k else str(r)
        reg[f'ech_r{tag}_pol'] = ('muon', dict(kind='echelon', ech_r=r, ech_frame='tracked', ech_tau='pi', ech_polish=True))
        reg[f'ech_r{tag}_fro'] = ('muon', dict(kind='echelon', ech_r=r, ech_frame='tracked', ech_tau='fro'))
    return reg


def make_opt(name, shape, k, seed=0, **over):
    fam, kw = optimizer_registry(k)[name]
    kw = dict(kw)
    kw.update(over)
    return Opt(shape=shape, seed=seed, **kw)


# --------------------------------------------------------------------------------------------
# 6. Deng-style matrix quadratic (model M2)
# --------------------------------------------------------------------------------------------

class QuadM2:
    """L(W) = 1/2 tr(W^T A W),  W in R^{d x n},  A = Q diag(lam) Q^T,
       lam_D = linspace(2 m, m, k)  (dominant block, lam_k = m),
       lam_B = linspace(1, 0.1, d-k) (bulk, lam_{k+1} = 1, lam_d = 0.1),   gap m = lam_k/lam_{k+1}.
    Q is a Haar-random orthogonal matrix drawn from `seed` (the problem seed)."""

    def __init__(self, d=200, k=20, n=40, m=100.0, seed=0):
        self.d, self.k, self.n, self.m = d, k, n, float(m)
        rng = np.random.default_rng([int(seed), 1])
        lam_D = np.linspace(2.0 * m, 1.0 * m, k)
        lam_B = np.linspace(1.0, 0.1, d - k)
        self.lam = np.concatenate([lam_D, lam_B])
        Qm, R = np.linalg.qr(rng.standard_normal((d, d)))
        Qm = Qm * np.sign(np.diag(R))[None, :]
        self.Q = Qm
        self.A = (Qm * self.lam[None, :]) @ Qm.T
        self.A = 0.5 * (self.A + self.A.T)
        self.seed = seed

    def init_W(self, seed, scale=1.0):
        rng = np.random.default_rng([int(seed), 2])
        return scale * rng.standard_normal((self.d, self.n))

    def coords(self, W):
        return self.Q.T @ W

    def metrics_from_grad(self, G):
        """loss and Deng alignment theta from the TRUE gradient G = A W."""
        Gt = self.Q.T @ G                      # rows: lam_i c_i
        e = np.sum(Gt * Gt, axis=1)            # lam_i^2 |c_i|^2
        sD = e[:self.k].sum()
        s = e.sum()
        loss = 0.5 * np.sum(e / self.lam)
        theta = sD / s if s > 0 else 0.0
        return loss, theta

    def dom_fraction(self, O):
        """||P^D O||_F^2 / ||O||_F^2."""
        tot = np.sum(O * O)
        if tot <= 0:
            return np.nan
        Od = self.Q[:, :self.k].T @ O
        return np.sum(Od * Od) / tot

    def theta_inf_sgd(self, eta, sigma=1.0):
        """Deng's Theorem (late-time alignment of constant-step SGD, isotropic noise):
        sum_D lam^2 beta / sum lam^2 beta,  beta_i = eta kappa^2 / (2 lam_i - eta lam_i^2)."""
        lam = self.lam
        beta = eta * sigma ** 2 / (2 * lam - eta * lam ** 2)
        w = lam ** 2 * beta
        return w[:self.k].sum() / w.sum()


def run(model, opt, lr, T, sigma, W0, noise_seed, rec_every=1, checkpoints=(), blowup=1e8):
    """Run T steps of W <- W - lr * opt.direction(A W + sigma Xi_t).

    Common random numbers: the noise stream depends only on `noise_seed`, not on the optimizer.
    Returns dict with arrays loss, theta (Deng's alignment of the TRUE gradient), upd_dom (fraction
    of the update in the dominant Hessian subspace), recorded BEFORE each recorded step, plus
    `diverged` and optional checkpoints {t: W}."""
    rng = np.random.default_rng([int(noise_seed), 3])
    W = W0.copy()
    nrec = (T + rec_every - 1) // rec_every
    loss = np.full(nrec + 1, np.nan)
    theta = np.full(nrec + 1, np.nan)
    upd = np.full(nrec, np.nan)
    ck = {}
    diverged = False
    L0 = None
    A = model.A
    d, n = W.shape
    for t in range(T):
        G = A @ W
        rec = (t % rec_every == 0)
        if rec:
            i = t // rec_every
            loss[i], theta[i] = model.metrics_from_grad(G)
            if L0 is None:
                L0 = loss[i]
            if not np.isfinite(loss[i]) or loss[i] > blowup * L0:
                diverged = True
                break
        if t in checkpoints:
            ck[t] = W.copy()
        g = G + sigma * rng.standard_normal((d, n)) if sigma > 0 else G
        O = opt.direction(g)
        if not np.all(np.isfinite(O)):      # blow-up between two recorded steps
            diverged = True
            break
        if rec:
            upd[i] = model.dom_fraction(O)
        W = W - lr * O
    if not diverged:
        G = A @ W
        loss[-1], theta[-1] = model.metrics_from_grad(G)
        if not np.isfinite(loss[-1]) or loss[-1] > blowup * L0:
            diverged = True
    return dict(loss=loss, theta=theta, upd_dom=upd, diverged=diverged, W_final=W, checkpoints=ck)


# --------------------------------------------------------------------------------------------
# 7. Fidelity helpers
# --------------------------------------------------------------------------------------------

def transfer(out, U, Vh):
    """Effective singular-value transfer of a filter output `out` in the exact singular basis
    (U, Vh) of the input:  t_i = u_i^T out v_i, and the off-diagonal energy fraction
    1 - sum t_i^2 / ||out||_F^2."""
    Tm = U.T @ out @ Vh.T
    t = np.diag(Tm).copy()
    tot = np.sum(out * out)
    off = 1.0 - np.sum(t * t) / tot if tot > 0 else np.nan
    return t, off


def rel_err(approx, exact):
    return np.linalg.norm(approx - exact) / np.linalg.norm(exact)


def haar(rows, cols, rng):
    Qm, R = np.linalg.qr(rng.standard_normal((rows, cols)))
    return Qm * np.sign(np.diag(R))[None, :]


if __name__ == '__main__':
    # minimal self-test of the ports (see test_port.py for the full set)
    rng = np.random.default_rng(0)
    G = rng.standard_normal((200, 40))
    U, S, Vh = svd(G, full_matrices=False)
    t, off = transfer(zeropower_via_newtonschulz5(G), U, Vh)
    print('NS5 transfer range on a Gaussian 200x40:', t.min(), t.max(), 'offdiag', off)
    R = gram_root_1_16_via_newtonschulz(G, 0.125)
    print('gram root vs exact (rel err):', rel_err(R, (Vh.T * (S ** 2 + 1e-6) ** (1 / 16)) @ Vh))
