"""Simulate a concrete version of the Main Construction in the model.

State: y.  Step: y -> (1 + r(lambda)) y with r a polynomial of degree < D, written as
r = sum_j c_j (lambda/kappa)^j.  At each step we ask, to first order, for
    tau   -> (1 - 2 beta) tau          (defect decreases)
    eps^2 -> eps^2                     (distance to x0 kept)
    a_0   -> (1 - beta) a_0            (leading coefficient tracks sqrt(tau)), optional
    <R x0, w> -> same                  (confinement constraint), optional
and take the solution c minimising sum_j (c_j * omega^j)^2.  The step is then applied exactly
and all quantities are recomputed; beta is halved if the realised decrease of tau is poor.
"""
import sys
import numpy as np
from model import Model, kappa


def quantities(M, y, w=None):
    s = M.state(y)
    q = [s["tau"], s["eps2"], float(np.real(s["a0"]))]
    if w is not None:
        q.append(float(np.real(M.ip(M.x0 - s["v"], w))))
    return np.array(q), s


def jacobian(M, y, D, w, h=1e-6):
    basis = [(M.lam / kappa) ** j for j in range(D)]
    q0, s = quantities(M, y, w)
    Jm = np.zeros((len(q0), D))
    for j, bj in enumerate(basis):
        qp, _ = quantities(M, y * (1 + h * bj), w)
        qm, _ = quantities(M, y * (1 - h * bj), w)
        Jm[:, j] = (qp - qm) / (2 * h)
    return Jm, q0, s, basis


def run(M, y, steps=400, D=14, beta0=0.05, omega=1.0, track_a0=True, w=None, w_from=None,
        tau_stop=1e-7, eps2_fixed=None, eps_rate=0.0, label=""):
    print(f"--- {label}  D={D} omega={omega} track_a0={track_a0}")
    print(f"{'step':>5} {'tau':>10} {'eps':>7} {'a0^2/tau':>9} {'distSol':>8} {'path':>8} "
          f"{'|c|':>9} {'smin':>9} {'beta':>8}")
    path, vprev, beta = 0.0, None, beta0
    hist = []
    for k in range(steps + 1):
        if w is None and w_from is not None and k == w_from:
            s = M.state(y)
            w = s["v"] / M.norm(s["v"])
        Jm, q0, s, basis = jacobian(M, y, D, w)
        tau, eps2, a0 = q0[0], q0[1], q0[2]
        if vprev is not None:
            path += M.norm(s["v"] - vprev)
        vprev = s["v"]
        rows = [0, 1] + ([2] if track_a0 else []) + ([3] if w is not None else [])
        A = Jm[rows] / (omega ** np.arange(D))  # minimise weighted norm
        # scale rows so the singular values measure independence of the constraints
        scale = np.linalg.norm(A, axis=1)
        sv = np.linalg.svd(A / scale[:, None], compute_uv=False)
        if k % max(1, steps // 25) == 0 or tau < tau_stop:
            print(f"{k:>5} {tau:>10.3e} {np.sqrt(eps2):>7.4f} {a0**2/tau:>9.5f} "
                  f"{M.dist_sol(s['v']):>8.4f} {path:>8.4f} {hist[-1][1] if hist else 0:>9.2e} "
                  f"{sv[-1]:>9.2e} {beta:>8.1e}")
        if tau < tau_stop or k == steps:
            break
        eps2_target = eps2 if eps2_fixed is None else eps2_fixed
        while True:
            # Newton iteration to hit the targets exactly (not just to first order)
            goal = {0: (1 - 2 * beta) * tau, 1: eps2_target - eps_rate * 2 * beta * tau, 2: (1 - beta) * a0, 3: q0[-1]}
            ycur, qcur, Acur, bcur = y, q0, A, basis
            csize, good = 0.0, False
            for it in range(8):
                t = np.array([goal[r] - qcur[r] for r in rows])
                ct = np.linalg.lstsq(Acur, t, rcond=None)[0]
                c = ct / (omega ** np.arange(D))
                csize += np.linalg.norm(c)
                if np.max(np.abs(c)) > 0.5:
                    break
                ycur = ycur * (1 + sum(cj * bj for cj, bj in zip(c, bcur)))
                Jc, qcur, _, bcur = jacobian(M, ycur, D, w)
                Acur = Jc[rows] / (omega ** np.arange(D))
                err = np.array([goal[r] - qcur[r] for r in rows])
                if np.all(np.abs(err) <= 1e-3 * beta * tau):
                    good = True
                    break
            if good:
                y = ycur
                hist.append((k, csize))
                beta = min(beta0, beta * 1.5)
                break
            beta /= 2
            if beta < 1e-9:
                print(f"STALLED at step {k}: tau={tau:.3e} |c| needed={csize:.2e} "
                      f"smin={sv[-1]:.2e}")
                return y, M.state(y)
    return y, M.state(y)


def dominant_start(M, st):
    """Lemma 2 of the paper: re-extremalise from w = v at the same level."""
    w, eps2 = st["v"], st["eps2"]
    lo, hi = 0.0, 16.0
    for _ in range(80):
        mid = (lo + hi) / 2
        if M.state(np.exp(mid) * w)["eps2"] > eps2:
            lo = mid
        else:
            hi = mid
    return np.exp(hi) * w


def start_state(M):
    """Lemma 3.5-style start: scale y0 until the extremal image is at distance ~ 1/2 - small."""
    best = None
    for s in np.exp(np.linspace(0, 12, 400)):
        st = M.state(s * M.y0)
        if 0.47 < np.sqrt(st["eps2"]) < 0.4999:
            if best is None or st["tau"] < best[1]["tau"]:
                best = (s, st)
    return best


if __name__ == "__main__":
    M = Model()
    print(f"n={M.n}  ||T* u1||={M.norm(M.lam*M.u1):.4f}")
    s, st = start_state(M)
    print(f"start: scale={s:.3g} tau={st['tau']:.3e} eps={np.sqrt(st['eps2']):.4f} "
          f"a0^2/tau={abs(st['a0'])**2/st['tau']:.5f} distSol={M.dist_sol(st['v']):.4f}")
    yd = dominant_start(M, st)
    sd = M.state(yd)
    print(f"dominant start: tau={sd['tau']:.3e} eps={np.sqrt(sd['eps2']):.4f} "
          f"a0^2/tau={abs(sd['a0'])**2/sd['tau']:.5f} distSol={M.dist_sol(sd['v']):.4f}")
    mode = sys.argv[1] if len(sys.argv) > 1 else "all"
    if mode in ("all", "plain"):
        run(M, yd, label="dominant start, no a0 tracking", track_a0=False)
    if mode in ("all", "track"):
        run(M, yd, label="dominant start, a0 tracking", track_a0=True)
    if mode in ("all", "mono"):
        run(M, yd, label="dominant start, a0 tracking, monomial norm", track_a0=True,
            omega=1 / kappa)
    if mode in ("all", "confine"):
        run(M, yd, label="dominant start, a0 tracking, confinement from step 40",
            track_a0=True, w_from=40)
