"""Shared code: the model operator T = multiplication by lambda on L^2[0, kappa].

Functions are stored by their values at Gauss-Legendre nodes; `wt` are the quadrature weights.
The inner product is linear in the first argument, as in the notes.
"""
import numpy as np

kappa = 0.5
J = 48  # truncation degree of power series; kappa^J ~ 4e-15


def make_grid(breaks, per_panel=40):
    xs, ws = np.polynomial.legendre.leggauss(per_panel)
    lam, wt = [], []
    for a, b in zip(breaks[:-1], breaks[1:]):
        lam.append((b - a) / 2 * xs + (a + b) / 2)
        wt.append((b - a) / 2 * ws)
    return np.concatenate(lam), np.concatenate(wt)


class Model:
    def __init__(self, bump_width=1e-3, per_panel=40):
        w = bump_width * kappa
        breaks = [0.0, w]
        while breaks[-1] * 2 < kappa:
            breaks.append(breaks[-1] * 2)
        breaks.append(kappa)
        self.lam, self.wt = make_grid(np.array(breaks), per_panel)
        self.n = len(self.lam)
        self.pow = np.vstack([self.lam**j for j in range(J)])  # J x n
        u0 = np.ones(self.n) / np.sqrt(kappa)
        bump = (self.lam < w).astype(float)
        u1 = bump - self.ip(bump, u0) * u0
        u1 = u1 / self.norm(u1)
        self.u0, self.u1 = u0, u1
        self.x0 = np.sqrt(3) / 2 * u0 + 0.5 * u1
        self.y0 = np.sqrt(3) / 2 * u0

    def ip(self, a, b):
        return np.sum(a * np.conj(b) * self.wt)

    def norm(self, a):
        return np.sqrt(self.ip(a, a).real)

    def state(self, y):
        """Balanced-form quantities for y: R = (I + V V*)^{-1}, v = x0 - R x0, a = V* R x0."""
        sw = np.sqrt(self.wt)
        V = (self.pow * (y * sw)).T  # n x J in orthonormal coordinates
        G = V.conj().T @ V
        a = np.linalg.solve(np.eye(J) + G, V.conj().T @ (self.x0 * sw))
        v = (V @ a) / sw
        res = self.x0 - v
        return dict(y=y, v=v, a=a, tau=float(np.sum(np.abs(a) ** 2)),
                    eps2=float(self.norm(res) ** 2), a0=a[0])

    def dist_sol(self, v):
        d2 = np.minimum(np.abs(v) ** 2, np.abs(v - self.x0) ** 2)
        return float(np.sqrt(np.sum(d2 * self.wt)))

    def Delta(self, v):
        return float(np.max(np.abs((self.pow * v) @ (np.conj(self.x0 - v) * self.wt))))
