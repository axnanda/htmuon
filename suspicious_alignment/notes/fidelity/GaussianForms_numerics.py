"""Numerical sanity checks behind notes/fidelity/GaussianForms.md (reproducible, seeded).

Run:  python3 notes/fidelity/GaussianForms_numerics.py
Nothing here is used by the Lean development; every identity/inequality checked below is proved in
SuspiciousAlignment/Prob/GaussianForms.lean unless the output line says "(note only)".
"""
import numpy as np

rng = np.random.default_rng(0)


def op(C):
    return np.linalg.norm(C, 2)


print("== 1. Lemma gauss-var: inequalities on 20000 random instances (max of LHS-RHS, <= 0 expected)")
w_lin = w_diag = w_sym = w_gen = w_gen_tt = -np.inf
for _ in range(20000):
    d = rng.integers(1, 6)
    r = rng.integers(1, d + 2)
    M = rng.normal(size=(d, r)); C = M @ M.T
    g = rng.normal(size=d)
    w_lin = max(w_lin, g @ C @ g - op(C) * (g @ g))
    Dd = np.diag(rng.normal(size=d))
    w_diag = max(w_diag, np.trace(C @ Dd @ C @ Dd) - op(C) ** 2 * np.trace(Dd @ Dd))
    A = rng.normal(size=(d, d)); Ds = A + A.T
    w_sym = max(w_sym, np.trace(C @ Ds @ C @ Ds) - op(C) ** 2 * np.trace(Ds @ Ds))
    w_gen = max(w_gen, np.trace(C @ A @ C @ A) - op(C) ** 2 * np.trace(A @ A))
    Cg = rng.normal(size=(d, d))
    w_gen_tt = max(w_gen_tt, np.trace(Cg @ A @ Cg @ A) - op(Cg) ** 2 * np.trace(A.T @ A))
print("  g^T C g <= ||C|| |g|^2                      :", w_lin)
print("  tr((CD)^2) <= ||C||^2 tr(D^2), D diagonal   :", w_diag)
print("  same, D symmetric                           :", w_sym)
print("  same, D arbitrary  (FAILS, > 0 expected)    :", w_gen)
print("  any C, any D, tr(D^T D) on the right        :", w_gen_tt)
C = np.diag([1., 0.]); D = np.array([[0., 1.], [-1., 0.]])
print("  formal counterexample C=diag(1,0), D=rot: tr((CD)^2) =", np.trace(C @ D @ C @ D),
      " ||C||^2 tr(D^2) =", op(C) ** 2 * np.trace(D @ D))

print("== 2. Lemma gauss-var: Monte Carlo (4e6 samples, singular C of rank 3 in dimension 4)")
d, r = 4, 3
M = rng.normal(size=(d, r)); C = M @ M.T
g = rng.normal(size=d); A = rng.normal(size=(d, d)); Ds = A + A.T
Dd = np.diag(rng.normal(size=d)); chi = 1.7
N = 4_000_000
z = rng.normal(size=(N, r)) @ M.T
lin = z @ g
print("  E g^T z =", lin.mean(), "  Var g^T z =", lin.var(), " g^T C g =", g @ C @ g)
for name, D in [("symmetric", Ds), ("diagonal", Dd), ("non-symmetric", A)]:
    quad = np.einsum('ni,ij,nj->n', z, D, z)
    sym = (D + D.T) / 2
    print(f"  D {name}: E z^T D z = {quad.mean():.4f} (tr(CD) = {np.trace(C @ D):.4f});"
          f" Var = {quad.var():.3f}, 2tr((CD)^2) = {2 * np.trace(C @ D @ C @ D):.3f},"
          f" 2tr((C sym D)^2) = {2 * np.trace(C @ sym @ C @ sym):.3f};"
          f" Cov(lin, quad) = {np.cov(lin, quad)[0, 1]:.4f};"
          f" Var(chi+lin+quad) = {(chi + lin + quad).var():.3f}"
          f" vs g^T C g + 2tr((C sym D)^2) = {g @ C @ g + 2 * np.trace(C @ sym @ C @ sym):.3f}")

print("== 3. s^S_{t+1}: mean / variance formulas (Monte Carlo) and the finite-d bounds")
rng = np.random.default_rng(1)
d = 6; S = [0, 1, 2]
lam = np.sort(rng.uniform(0.5, 3, size=d))[::-1]; c = rng.normal(size=d); eta = 0.3
M = rng.normal(size=(d, d)); C = M @ M.T / d
N = 2_000_000
z = rng.normal(size=(N, d)) @ M.T / np.sqrt(d)
cn = (1 - eta * lam) * c - eta * z
s = (lam[S] ** 2 * cn[:, S] ** 2).sum(axis=1)
g = np.zeros(d); g[S] = -2 * eta * lam[S] ** 2 * (1 - eta * lam[S]) * c[S]
dv = np.zeros(d); dv[S] = eta ** 2 * lam[S] ** 2
D = np.diag(dv)
chi = (lam[S] ** 2 * (1 - eta * lam[S]) ** 2 * c[S] ** 2).sum()
print("  mean: MC", s.mean(), " chi + tr(C D) =", chi + np.trace(C @ D))
print("  var : MC", s.var(), " g^T C g + 2 tr((CD)^2) =", g @ C @ g + 2 * np.trace(C @ D @ C @ D))

print("== 4. relative bounds (max of LHS-RHS over 20000 random instances, <= 0 expected)")
w_rel = w_chi = w_bulk = w_card = -np.inf
for _ in range(20000):
    d = rng.integers(2, 8)
    lam = np.sort(rng.uniform(0.1, 3, size=d))[::-1]
    T = np.zeros(d, bool); T[rng.choice(d, size=rng.integers(1, d + 1), replace=False)] = True
    S = T & (rng.uniform(size=d) < 0.7)          # S subset of T (possibly empty)
    M = rng.normal(size=(d, d)); C = M @ M.T + 1e-3 * np.eye(d)
    nC = op(C); smin = np.diag(C)[T].min()        # smin <= C_ii on T
    eta = rng.uniform(-2, 2); c = rng.normal(size=d) * rng.choice([0, 1, 10])
    gS = np.where(S, -2 * eta * lam ** 2 * (1 - eta * lam) * c, 0.0)
    DS = np.diag(np.where(S, eta ** 2 * lam ** 2, 0.0))
    var = gS @ C @ gS + 2 * np.trace(C @ DS @ C @ DS)                     # Var(s^S_{t+1})
    chiS = (lam ** 2 * (1 - eta * lam) ** 2 * c ** 2)[S].sum()
    chiT = (lam ** 2 * (1 - eta * lam) ** 2 * c ** 2)[T].sum()
    ET = chiT + eta ** 2 * (lam ** 2 * np.diag(C))[T].sum()               # E s^T_{t+1}
    psiT = (lam[T] ** 2).sum(); QS = (lam[S] ** 4).sum()
    Lam = lam[S].max() if S.any() else 0.0
    # Spec.variance_sNext_mul_le_integral_sq_of_subset (division-free)
    w_rel = max(w_rel, (smin ** 2 * psiT ** 2 * var
                        - (nC * smin * Lam ** 2 * psiT + 2 * nC ** 2 * QS) * ET ** 2) / (1 + ET ** 2))
    # Spec.variance_sNext_le_chi_of_isCenteredGaussian
    w_chi = max(w_chi, var - (4 * eta ** 2 * nC * Lam ** 2 * chiS + 2 * eta ** 4 * nC ** 2 * QS))
    # (note only) bulk block against the total energy: Var(s^B)/(E s)^2 <= kappa/k + kappa^2/(2k)
    k = rng.integers(1, d)
    Bm = np.arange(d) >= k
    gB = np.where(Bm, -2 * eta * lam ** 2 * (1 - eta * lam) * c, 0.0)
    DB = np.diag(np.where(Bm, eta ** 2 * lam ** 2, 0.0))
    varB = gB @ C @ gB + 2 * np.trace(C @ DB @ C @ DB)
    Etot = (lam ** 2 * (1 - eta * lam) ** 2 * c ** 2).sum() + eta ** 2 * (lam ** 2 * np.diag(C)).sum()
    kap = nC / np.diag(C).min()
    if Etot > 0:
        w_bulk = max(w_bulk, varB / Etot ** 2 - (kap / k + kap ** 2 / (2 * k)))
    # Spec.variance_sNext_le_card_of_isCenteredGaussian (explicit O(|S|) constant)
    H = abs(eta); L = lam[0]; sC = nC
    K = (c[S] ** 2).sum() / max(S.sum(), 1)
    w_card = max(w_card, var - (4 * H ** 2 * sC * L ** 4 * (1 + H * L) ** 2 * K
                                + 2 * H ** 4 * sC ** 2 * L ** 4) * S.sum())
print("  smin^2 psi_T^2 Var(s^S) <= (||C|| smin Lam_S^2 psi_T + 2||C||^2 Q_S)(E s^T)^2 :", w_rel)
print("  Var(s^S) <= 4 eta^2 ||C|| Lam_S^2 chi_S + 2 eta^4 ||C||^2 Q_S                 :", w_chi)
print("  (note only) Var(s^B)/(E s)^2 <= kappa/k + kappa^2/(2k)                        :", w_bulk)
print("  Var(s^S) <= (4H^2 s L^4 (1+HL)^2 K + 2 H^4 s^2 L^4) |S|                       :", w_card)

print("== 5. counterexample to 'Var(s^S_{t+1}) = O(|S|) under Assumption 1' (GaussianForms.cexSpec)")
print("   d = 2k, lam_1 = L = k^(1/8), other dominant lam = 1, bulk lam = 1/2, c = sqrt(d) e_1,")
print("   C = diag(1/2, 0, ..., 0);  Var(s^D) = 4 sig eta^2 L^4 (1-eta L)^2 c_1^2 + 2 sig^2 eta^4 L^4")


def cex(k, eta):
    d = 2 * k; L = k ** 0.125; sig = 0.5; a2 = d
    var = 4 * sig * eta ** 2 * L ** 4 * (1 - eta * L) ** 2 * a2 + 2 * sig ** 2 * eta ** 4 * L ** 4
    mean = L ** 2 * (1 - eta * L) ** 2 * a2 + eta ** 2 * L ** 2 * sig
    mom = {p: (L ** p + (k - 1)) / k for p in (2, 3, 4, 6, 8)}
    return var, mean, mom


print("  stable step eta = 1/(2 lam_1)  (Var/k = L^2/4 + 1/(32k) = k^(1/4)/4 + ...):")
for k in [10 ** 2, 10 ** 4, 10 ** 6, 10 ** 8, 10 ** 10]:
    var, mean, mom = cex(k, 0.5 / k ** 0.125)
    print(f"   k={k:.0e}: Var/k={var / k:.4g}  E[s^D]/k={mean / k:.4g}  Var/E^2={var / mean ** 2:.3g}"
          f"  block moments p=2,4,8: {mom[2]:.4f} {mom[4]:.4f} {mom[8]:.4f}")
print("  fixed eta = 0.1 (step unstable once 0.1*lam_1 > 2, i.e. k > 20^8; at k = 1e8, 1 - eta*lam_1 = 0):")
for k in [10 ** 2, 10 ** 4, 10 ** 6, 10 ** 8, 10 ** 10]:
    var, mean, mom = cex(k, 0.1)
    print(f"   k={k:.0e}: Var/k={var / k:.4g}  E[s^D]/k={mean / k:.4g}")
# brute-force Monte Carlo validation of the closed form on a small instance
k = 8; d = 2 * k; eta = 0.1
lam = np.array([k ** 0.125] + [1.0] * (k - 1) + [0.5] * k)
c = np.zeros(d); c[0] = np.sqrt(d)
z = np.zeros((2_000_000, d)); z[:, 0] = rng.normal(size=2_000_000) * np.sqrt(0.5)
cn = (1 - eta * lam) * c - eta * z
sD = (lam[:k] ** 2 * cn[:, :k] ** 2).sum(1)
var, mean, _ = cex(k, eta)
print("  MC check (k=8, eta=0.1): Var", sD.var(), "closed form", var, "| mean", sD.mean(), mean)
