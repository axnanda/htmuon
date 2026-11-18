"""E2 (D3) -- Deng's critical step eta*_t versus the paper's bounds, in the paper's own experimental setup
(vector model n = 1, d = 500, k = 50, sigma = 0.5, x_0 ~ N(0, I), constant-step SGD with eta = 0.003).

For m in {5, 20, 100, 500} and seeds {42, 87} we follow one SGD trajectory (eigenbasis) and evaluate at
t in {0, 5, 20, 100, 1000, 10000, 30000}:
   eta*_t                 Eq. (def-etatstar-body)  (num / den; den <= 0 means 'decrease for every eta')
   L7                     Theorem 7 lower bound  2 gap_1 / ((lam_1^2 - lam_d^2) + s_max psi_D / (lam_d^2 |x|^2 theta))
   U8                     Theorem 8 upper bound  (lam_1 - lam_d) / (lam_k lam_1 - lam_{k+1} lam_d),
                          claimed when theta_t >= e_B / (e_B + e_D);   Corollary 9: eta* <= 2 / lam_1
   noise-free sandwich    2/(lam_1 + lam_{k+1}) <= eta*_0 <= 2/(lam_k + lam_d)   (filter_spec.md, 1.9)
Monte-Carlo check at t = 0 (m = 20, seed 42): E[theta_1] - theta_0 at step sizes around 2/lam_1 and eta*_0
(20000 antithetic noise draws) -- does the alignment still decrease for 2/lam_1 < eta < eta*_0 ?

Usage:  python3 e2_etastar_bounds.py        (about 20 CPU-s)   ->  results/e2_etastar_bounds.json
"""
import os

import numpy as np

import specfilt as sf

D, K, ETA, SIGMA, T = 500, 50, 0.003, 0.5, 30000
MS = [5, 20, 100, 500]
SEEDS = [42, 87]
TS = [0, 5, 20, 100, 1000, 10000, 30000]


def main():
    cpu = sf.CpuLog("e2_etastar_bounds")
    rows = []
    for m in MS:
        prob = sf.Problem(D, K, 1, m, sigma=SIGMA)
        lam = prob.lam
        l1, lk, lk1, ld = lam[0], lam[K - 1], lam[K], lam[-1]
        psiD = (lam[:K] ** 2).sum()
        eD, eB = SIGMA ** 2 * psiD, SIGMA ** 2 * (lam[K:] ** 2).sum()
        U8 = (l1 - ld) / (lk * l1 - lk1 * ld)
        for sd in SEEDS:
            rng = np.random.default_rng([sd, m])
            x = rng.standard_normal(D)
            for t in range(T + 1):
                if t in TS:
                    W = x[:, None]
                    es, num, den = prob.eta_star_deng(W)
                    th = float(prob.theta(prob.grad(W)))
                    L7 = 2 * (lk - lk1) / ((l1 ** 2 - ld ** 2) + SIGMA ** 2 * psiD / (ld ** 2 * (x @ x) * max(th, 1e-300)))
                    rows.append(dict(m=m, seed=sd, t=t, theta=th, eta_star=float(es) if (num > 0 and den > 0) else None,
                                     num=float(num), den=float(den), L7=float(L7), U8=float(U8), two_over_lam1=2 / l1,
                                     nf_lo=2 / (l1 + lk1), nf_hi=2 / (lk + ld), cond_thm8=bool(th >= eB / (eB + eD)),
                                     thr_thm8=float(eB / (eB + eD)),
                                     snr=float(((lam * x) ** 2).sum() / (SIGMA ** 2 * D))))
                x = x - ETA * (lam * x + SIGMA * rng.standard_normal(D))
        print("done m =", m, flush=True)
    # Monte-Carlo check at t = 0
    m, sd = 20, 42
    prob = sf.Problem(D, K, 1, m, sigma=SIGMA)
    x0 = np.random.default_rng([sd, m]).standard_normal(D)[:, None]
    es, num, den = prob.eta_star_deng(x0)
    st = sf.onestep(prob, x0, ["sgd"], N=20000, seed=3, gradproj=False)
    etas = np.array([0.0190, 0.0200, 0.0205, 0.0210, float(es), 0.0220, 0.0230])
    mean, se, roe = sf.dtheta_curves(st["aD"], st["aB"], st["per_opt"]["sgd"]["Q"], etas)
    mc = dict(m=m, seed=sd, eta_star_closed_form=float(es), two_over_lam1=0.02, etas=etas, dtheta_mean=mean, dtheta_se=se,
              dtheta_ratio_of_expectations=roe, N=20000)
    sf.save_json(os.path.join(sf.RES, "e2_etastar_bounds.json"), dict(d=D, k=K, eta=ETA, sigma=SIGMA, rows=rows, mc=mc))
    print(" m  seed     t  theta    eta*       L7(Thm7)   U8(Thm8)   2/lam1  [2/(l1+lk1), 2/(lk+ld)]  theta>=e_B/(e_B+e_D)")
    for r in rows:
        es_s = f"{r['eta_star']:.5f}" if r["eta_star"] is not None else "dec-all"
        print(f"{r['m']:4d} {r['seed']:3d} {r['t']:6d}  {r['theta']:.4f}  {es_s:>8s}  {r['L7']:.3e}  {r['U8']:.5f}   "
              f"{r['two_over_lam1']:.3f}   [{r['nf_lo']:.5f}, {r['nf_hi']:.5f}]   {r['cond_thm8']}")
    print("\nMC at t=0, m=20, seed 42: eta* (closed form) =", es)
    for e, a, b, c in zip(etas, mean, se, roe):
        print(f"  eta={e:.5f}  E[theta_1]-theta_0 = {a:+.3e} ± {b:.1e}   (ratio of expectations {c:+.3e})")
    cpu.done()


if __name__ == "__main__":
    main()
