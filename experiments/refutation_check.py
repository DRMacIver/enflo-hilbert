"""Sanity check of Proposition 5 and Theorem 7 of tex/refutation.tex (discretised model).

States: v_N = (x0 + W_N x0)/2 with W_N = multiplication by exp(i alpha0 sin(N lambda)),
alpha0 the first positive root of J0(alpha) = 1/2.
"""
import numpy as np
from scipy.special import j0
from scipy.optimize import brentq

kappa, n, J = 0.5, 40000, 60
lam = (np.arange(n) + 0.5) * kappa / n
dmu = kappa / n
ip = lambda a, b: np.sum(a * np.conj(b)) * dmu
norm = lambda a: np.sqrt(ip(a, a).real)
u0 = np.ones(n) / np.sqrt(kappa)
bump = (lam < 0.02 * kappa).astype(float)
u1 = bump - ip(bump, u0) * u0
u1 /= norm(u1)
x0 = np.sqrt(3) / 2 * u0 + 0.5 * u1
powers = np.vstack([lam**j for j in range(J)])
alpha0 = brentq(lambda a: j0(a) - 0.5, 1, 2)
print(f"alpha0={alpha0:.6f}  c*={(1 - j0(2 * alpha0)) / 8:.5f}")
print(f"{'N':>6} {'Delta(v_N)':>11} {'|x0-v_N|':>9} {'c_N':>8} | {'|1-b0|':>9} {'tail':>9} "
      f"{'|v_N-v_N`|':>10} {'tau(v_N`)':>10}")
for N in [50, 200, 800, 3200, 12800]:
    W = np.exp(1j * alpha0 * np.sin(N * lam))
    v = (x0 + W * x0) / 2
    Delta = np.max(np.abs((powers * v) @ np.conj(x0 - v) * dmu))
    eps = norm(x0 - v)
    cN = (norm(x0) ** 2 - norm(np.cos(alpha0 * np.sin(N * lam)) * x0) ** 2) / 4
    V = (powers * v).T * np.sqrt(dmu)
    xs = x0 * np.sqrt(dmu)
    G, rhs = V.conj().T @ V, V.conj().T @ xs
    f = lambda lt: np.linalg.norm(xs - V @ np.linalg.solve(G + np.exp(lt) * np.eye(J), rhs)) - eps
    b = np.linalg.solve(G + np.exp(brentq(f, -25, 20, xtol=1e-13)) * np.eye(J), rhs)
    vb = (V @ b) / np.sqrt(dmu)
    print(f"{N:>6} {Delta:>11.2e} {eps:>9.4f} {cN:>8.4f} | {abs(1 - b[0]):>9.2e} "
          f"{np.sum(np.abs(b[1:])**2):>9.2e} {norm(vb - v):>10.2e} {ip(vb, x0 - vb).real:>10.2e}")
