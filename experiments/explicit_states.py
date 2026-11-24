"""Explicit extremal states in the model operator (multiplication by lambda on L^2[0,kappa]).

Checks, on a discretisation:
  1. the designed x0 has the paper's form and the extremal image of y0 = (sqrt3/2) u0 with
     Tikhonov parameter t0 has series a_j = mu sigma^j/(j+1);
  2. the states S(beta, alpha, N) defined by an explicit function c~ are extremal images with
     the predicted series, and their non-degeneracy data (tail, a_j, b_j);
  3. along a path from the start to an oscillating state, in the limit N -> infinity
     (phase-averaged), the defect decreases and the distance to x0 is held fixed.

The finite-N rows test only the algebraic identity behind the explicit formula; N is far
below what the estimates in tex/refutation.tex require. Usage: explicit_states.py [t0] [N]
(defaults 0.05, 200000; smaller t0 needs much larger N and a finer grid).
"""
import sys
import numpy as np
from scipy.optimize import brentq, fsolve
from scipy.special import j0

kappa = 0.5
k = np.sqrt(3) / 2 / np.sqrt(kappa)
J = 70


def design(t0):
    """Solve for (mu, sigma) so that x0 = k A0 + (t0 mu/(k sigma)) 1_[0,sigma] is a unit vector
    with <x0,u0> = sqrt3/2."""
    from scipy.integrate import quad

    def A0(lam, mu, sigma):
        z = sigma * lam
        return mu * np.where(z > 1e-12, -np.log1p(-z) / np.where(z > 1e-12, z, 1), 1.0)

    def eqs(p):
        mu, ls = p
        sigma = np.exp(ls)
        h = t0 * mu / (k * sigma)
        i1 = quad(lambda l: A0(l, mu, sigma), 0, kappa)[0]
        i2 = quad(lambda l: A0(l, mu, sigma) ** 2, 0, kappa)[0]
        i3 = quad(lambda l: A0(l, mu, sigma), 0, sigma)[0]
        e1 = (k * i1 + h * sigma) / np.sqrt(kappa) - np.sqrt(3) / 2
        e2 = k * k * i2 + 2 * k * h * i3 + h * h * sigma - 1
        return [e1, e2]

    mu, ls = fsolve(eqs, [1 / (1 + 4 * t0 / 3), np.log(4 * t0**2 / k**2)], xtol=1e-14)
    return mu, np.exp(ls)


class Model:
    def __init__(self, t0, n=2_000_000):
        self.t0 = t0
        self.mu, self.sigma = design(t0)
        # grid refined so that sigma is a cell boundary
        n1 = max(2000, int(n * 0.2))
        l1 = (np.arange(n1) + 0.5) * self.sigma / n1
        n2 = n - n1
        l2 = self.sigma + (np.arange(n2) + 0.5) * (kappa - self.sigma) / n2
        self.lam = np.concatenate([l1, l2])
        self.w = np.concatenate([np.full(n1, self.sigma / n1), np.full(n2, (kappa - self.sigma) / n2)])
        z = self.sigma * self.lam
        self.A0 = -self.mu * np.log1p(-z) / z
        self.p0 = np.where(self.lam < self.sigma, self.mu / self.sigma, 0.0)
        self.x0 = k * self.A0 + t0 * self.p0 / k
        self.pows = np.vstack([self.lam**j for j in range(2 * J)])

    def integ(self, f):
        return np.sum(f * self.w)

    def moments(self, f, m=None):
        return self.pows[: (m or J)] @ (f * self.w)

    def tikhonov(self, y, t):
        G = self.moments(np.abs(y) ** 2, 2 * J - 1)
        Gm = np.array([[G[i + j] for j in range(J)] for i in range(J)])
        rhs = self.moments(self.x0 * np.conj(y))
        a = np.linalg.solve(Gm + t * np.eye(J), rhs)
        return a, Gm

    def state(self, beta, alpha, N):
        lam, x0 = self.lam, self.x0
        U = lam < beta
        t = self.mu**2 * self.t0 * beta / self.sigma
        zb = beta * lam
        Lb = -np.log1p(-zb) / zb
        ct = np.where(U, (t / beta) / x0**2, 0.5j * np.sin(alpha * np.sin(N * lam)) / Lb)
        a = self.moments(x0**2 * np.conj(ct)) / t
        A = np.polyval(a[::-1], lam)
        c = ct * A
        rad = 0.25 - c.real - c.imag**2
        assert rad.min() > 0, rad.min()
        g = 0.5 + np.where(U, -1, 1) * np.sqrt(rad) + 1j * c.imag
        v = x0 * g
        y = v / A
        return dict(t=t, a=a, A=A, g=g, v=v, y=y, rad=rad.min())

    def report(self, beta, alpha, N, verbose=True):
        S = self.state(beta, alpha, N)
        t, a, v, y = S["t"], S["a"], S["v"], S["y"]
        a_num, Gm = self.tikhonov(y, t)
        err = np.max(np.abs(a_num - a))
        tau = self.integ(v * np.conj(self.x0 - v))
        eps2 = self.integ(np.abs(self.x0 - v) ** 2)
        tail = np.sum(np.abs(a[1:]) ** 2) / np.sum(np.abs(a) ** 2)
        e = np.linalg.solve(Gm + t * np.eye(J), a)
        bhat = t**1.5 * e
        ahat = np.sqrt(t) * a
        tn = t * np.sum(np.abs(a) ** 2)
        vN = 0.5 * self.x0 * (1 + np.exp(1j * alpha * np.sin(N * self.lam)))
        dist_vN = np.sqrt(self.integ(np.abs(v - vN) ** 2))
        cstar = 0.25 * self.integ(self.x0**2 * np.sin(alpha * np.sin(N * self.lam)) ** 2)
        if verbose:
            print(f"beta/sigma={beta/self.sigma:.3g} alpha={alpha:.4f} N={N}")
            print(f"  t={t:.3e}  tau=<v,x0-v>={tau.real:.3e}{tau.imag:+.1e}i  t|a|^2={tn:.3e}")
            print(f"  extremality: max|a_tikhonov - a_formula| = {err:.2e}; min radicand {S['rad']:.2e}")
            print(f"  eps^2={eps2:.6f}  a0={a[0]:.5f}  tail fraction={tail:.3e}  (tau^15/2={0.5*tn**15:.1e})")
            print(f"  |ahat_2|,|ahat_3| = {abs(ahat[2]):.2e}, {abs(ahat[3]):.2e};"
                  f"  |bhat_2..5| = {np.abs(bhat[2:6])}  (tau^30={tn**30:.1e})")
            print(f"  |e_2..5| = {np.abs(e[2:6])}")
            print(f"  ||v - v_N||={dist_vN:.4f}   c*={cstar:.4f}  ||y||={np.sqrt(self.integ(abs(y)**2)):.4f}"
                  f"  Re<y,u0>={self.integ(y.real)/np.sqrt(kappa):.4f}")
        return dict(t=t, tau=tn, eps2=eps2, tail=tail, v=v, y=y)


if __name__ == "__main__":
    t0 = float(sys.argv[1]) if len(sys.argv) > 1 else 0.05
    M = Model(t0)
    print(f"t0={t0}: mu={M.mu:.6f} sigma={M.sigma:.6e}  (4 t0^2/k^2={4*t0**2/k**2:.3e})")
    print(f"  ||x0||^2={M.integ(M.x0**2):.8f}  <x0,u0>={M.integ(M.x0)/np.sqrt(kappa):.8f} (sqrt3/2={np.sqrt(3)/2:.8f})")
    u1 = 2 * (M.x0 - np.sqrt(3) / 2 / np.sqrt(kappa))
    print(f"  ||u1||={np.sqrt(M.integ(u1**2)):.6f} <u1,u0>={M.integ(u1)/np.sqrt(kappa):.2e} ||T u1||={np.sqrt(M.integ((M.lam*u1)**2)):.3e}")
    # start state
    y0 = np.full_like(M.lam, k)
    a_num, _ = M.tikhonov(y0, t0)
    a_pred = M.mu * M.sigma ** np.arange(J) / (np.arange(J) + 1)
    print(f"  start: max|a_num - mu sigma^j/(j+1)| = {np.max(np.abs(a_num-a_pred)):.2e}; a0={a_num[0]:.6f}")
    print("== start state as S(sigma, 0, N) ==")
    r0 = M.report(M.sigma * (1 + 1e-9), 0.0, 1)
    eps0 = r0["eps2"]
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 200000
    print("== finite N checks ==")
    for frac, al in [(0.5, 0.5), (0.5, 1.0), (0.2, 1.2)]:
        M.report(M.sigma * frac, al, N)
    print("== path in the limit N -> infinity (phase-averaged) ==")
    lam, x0, w = M.lam, M.x0, M.w
    print(" beta/sigma  alpha     t        tau      eps^2(lim)  tail      |e_2|   |e_3|   |e_4|   c*      m(beta)")
    for frac in [1.0, 0.9, 0.7, 0.5, 0.3, 0.1, 0.03, 0.01, 0.001]:
        beta = M.sigma * frac
        U = lam < beta * (1 + 1e-12)
        t = M.mu**2 * t0 * beta / M.sigma
        zb = beta * lam
        Lb = -np.log1p(-zb) / zb
        c = (t / beta) * Lb / x0**2
        gm = 0.5 - np.sqrt(0.25 - c)
        D = np.sum((x0**2 * (1 - gm) ** 2 * w)[U])
        m = np.sum((x0**2 * w)[U])
        Phi = (eps0 - D) / (1 - m)
        al = 0.0 if Phi <= 0 else brentq(lambda a_: 0.5 * (1 - j0(a_)) - Phi, 0, 1.5707)
        a = beta ** np.arange(J) / (np.arange(J) + 1)
        tau = t * np.sum(a**2)
        tail = np.sum(a[1:] ** 2) / np.sum(a**2)
        W = np.where(U, (x0 * gm / Lb) ** 2, x0**2 * 0.5 * (1 + j0(al)) / Lb**2)
        G = M.moments(W, 2 * J - 1)
        Gm = np.array([[G[i + j] for j in range(J)] for i in range(J)])
        e = np.linalg.solve(Gm + t * np.eye(J), a)
        cstar = 0.125 * (1 - j0(2 * al)) * (1 - m)
        print(f" {frac:8.3f}  {al:.4f}  {t:.2e}  {tau:.2e}  {D+0.5*(1-j0(al))*(1-m):.6f}  {tail:.2e}  "
              f"{abs(e[2]):.3f}  {abs(e[3]):.3f}  {abs(e[4]):.3f}  {cstar:.4f}  {m:.4f}")
