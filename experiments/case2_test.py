"""Test the paper's Case II claims ((26)-(27) and the factor 1 - 1/20) in the model.

A Case II state is an extremal image w with |<T^j w, x0 - w>| < tau^4 for all j >= 1.
In the model these exist when u1 is concentrated extremely close to lambda = 0.
For delta = tau/10 let w+ be the extremal image of w at level ||x0 - (1+delta) w||.
The paper claims ||w+ - (1+delta) w|| < tau^2 and tau(w+) < (1 - 1/20) tau.
"""
import numpy as np
from model import Model, J


def extremal_at_level(M, w, eps2):
    lo, hi = -5.0, 40.0
    for _ in range(200):
        mid = (lo + hi) / 2
        if M.state(np.exp(mid) * w)["eps2"] > eps2:
            lo = mid
        else:
            hi = mid
    s = np.exp(hi)
    st = M.state(s * w)
    return st, st["a"] * s  # series coefficients with respect to w itself


for width in [1e-6, 1e-9, 1e-12]:
    M = Model(bump_width=width)
    # start: extremal image of y0 at a level just below 1/2
    best, _ = extremal_at_level(M, M.y0, 0.4995 ** 2)
    w = best["v"]
    print(f"\nbump width {width:g}: n={M.n}")
    for it in range(6):
        tau = M.ip(w, M.x0 - w).real
        m = (M.pow * w) @ (np.conj(M.x0 - w) * M.wt)
        m1 = np.max(np.abs(m[1:]))
        delta = tau / 10
        target = M.norm(M.x0 - (1 + delta) * w) ** 2
        st, b = extremal_at_level(M, w, target)
        wp = st["v"]
        taup = M.ip(wp, M.x0 - wp).real
        print(f"  it {it}: tau={tau:.3e} eps={M.norm(M.x0-w):.5f} max_j>=1|m_j|={m1:.2e} "
              f"tau^4={tau**4:.1e} | b0-(1+delta)={b[0]-(1+delta):+.2e} "
              f"tail={np.sqrt(np.sum(b[1:]**2)):.2e} "
              f"|w+-(1+d)w|/tau^2={M.norm(wp-(1+delta)*w)/tau**2:.2e} tau+/tau={taup/tau:.4f}")
        w = wp
