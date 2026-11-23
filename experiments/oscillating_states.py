"""Numerical check of the oscillating near-solutions of Section 7 of the notes.

Model: T = multiplication by lambda on L^2([0, kappa], dlambda), discretised on a grid.
x0 = sqrt(3)/2 u0 + 1/2 u1 with u1 concentrated near lambda = 0.
v_N = x0 * (1_A + 1_{A^c} (1 + exp(i N lambda)) / 2).

For each N we report
  Delta(v_N)      = sup_j |<T^j v, x0 - v>|
  eps             = ||x0 - v_N||
  dist_to_Sol     = distance from v_N to the nearest true solution x0 * 1_S
and, for the extremal series b of w = v_N at level eps (minimal l^2 norm with
||x0 - b(T) w|| <= eps):
  |1 - b_0|, tail = sum_{j>=1} |b_j|^2, ||b(T)w - w||, tau of the extremal image,
  and the extremal image's distance to the nearest true solution.
"""
import numpy as np
from scipy.optimize import brentq

kappa = 0.5
n = 40000
lam = (np.arange(n) + 0.5) * kappa / n
dmu = kappa / n
J = 60  # series truncated at degree J; kappa^J is negligible


def ip(a, b):  # linear in the first argument
    return np.sum(a * np.conj(b)) * dmu


def norm(a):
    return np.sqrt(ip(a, a).real)


u0 = np.ones(n) / np.sqrt(kappa)
bump = (lam < 0.02 * kappa).astype(float)
u1 = bump - ip(bump, u0) * u0
u1 /= norm(u1)
x0 = np.sqrt(3) / 2 * u0 + 0.5 * u1
powers = np.vstack([lam**j for j in range(J)])  # J x n


def Delta(v):
    return np.max(np.abs((powers * v) @ np.conj(x0 - v) * dmu))


def dist_to_solutions(v):
    # nearest x0*1_S: choose S pointwise
    return np.sqrt(np.sum(np.minimum(np.abs(v) ** 2, np.abs(v - x0) ** 2)) * dmu)


def extremal(w, eps):
    V = (powers * w).T * np.sqrt(dmu)  # n x J, so V b ~ b(T) w in l^2 normalisation
    xs = x0 * np.sqrt(dmu)
    G = V.conj().T @ V
    rhs = V.conj().T @ xs

    def resid(logt):
        b = np.linalg.solve(G + np.exp(logt) * np.eye(J), rhs)
        return np.linalg.norm(xs - V @ b) - eps

    logt = brentq(resid, -60, 20, xtol=1e-13)
    b = np.linalg.solve(G + np.exp(logt) * np.eye(J), rhs)
    return b, (V @ b) / np.sqrt(dmu)


# A^c carries half of the mass of |x0|^2, so eps^2 -> 1/4.
cum = np.cumsum(np.abs(x0) ** 2) * dmu
Ac = cum > 0.5

print(f"{'N':>7} {'Delta':>10} {'eps':>7} {'distSol':>8} | {'|1-b0|':>9} {'tail':>9} "
      f"{'|Vb-w|':>9} {'tau(Vb)':>9} {'distSol(Vb)':>11}")
for N in [50, 200, 800, 3200, 12800]:
    g = np.where(Ac, (1 + np.exp(1j * N * lam)) / 2, 1.0)
    v = x0 * g
    eps = norm(x0 - v)
    b, vb = extremal(v, eps)
    tau = ip(vb, x0 - vb)
    print(f"{N:>7} {Delta(v):>10.2e} {eps:>7.4f} {dist_to_solutions(v):>8.4f} | "
          f"{abs(1 - b[0]):>9.2e} {np.sum(np.abs(b[1:])**2):>9.2e} {norm(vb - v):>9.2e} "
          f"{tau.real:>9.2e} {dist_to_solutions(vb):>11.4f}")


# Non-degeneracy conditions of the paper for the extremal image at the largest N:
# balanced coefficients a_j = <R x0, T^j y>, b_j = <R^2 x0, T^j y> (y = t^{-1/2} w),
# to be compared with the thresholds tau^16 (tail) and tau^30 (individual coefficients).
V = (powers * v).T * np.sqrt(dmu)
xs = x0 * np.sqrt(dmu)
G = V.conj().T @ V
tval = None
for logt in np.linspace(-40, 10, 20001):
    bb = np.linalg.solve(G + np.exp(logt) * np.eye(J), V.conj().T @ xs)
    if np.linalg.norm(xs - V @ bb) >= eps:
        tval = np.exp(logt)
        break
Vh = V / np.sqrt(tval)
R = np.linalg.inv(np.eye(len(xs)) + Vh @ Vh.conj().T) if len(xs) <= 4000 else None
ah = np.sqrt(tval) * bb
tau_b = float(np.sum(np.abs(ah) ** 2))
print(f"\nN={N}: balanced tau={tau_b:.3e}, tail/tau={np.sum(np.abs(ah[1:])**2)/tau_b:.3e}, "
      f"thresholds tau^15={tau_b**15:.1e}, tau^30={tau_b**30:.1e}")
print("  |a_j|, j=1..6:", " ".join(f"{abs(a):.2e}" for a in ah[1:7]))
# b_j = <R^2 x0, T^j y> computed through the J x J system: V^* R^2 x0 = (I+G')^{-1} V^* R x0
Gh = Vh.conj().T @ Vh
rx = xs - Vh @ ah
bh = np.linalg.solve(np.eye(J) + Gh, Vh.conj().T @ rx)
print("  |b_j|, j=1..6:", " ".join(f"{abs(b):.2e}" for b in bh[1:7]))
