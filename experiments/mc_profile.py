"""Run the flow variants and print the profile g = v / x0 of the final state."""
import sys
import io
import contextlib
import numpy as np
from model import Model, kappa
from mc_flow import run, start_state, dominant_start

M = Model()
s, st = start_state(M)
yd = dominant_start(M, st)
variants = {
    "plain": dict(track_a0=False),
    "track": dict(track_a0=True),
    "track_eps": dict(track_a0=True, eps_rate=1.0),
    "track_eps_hi": dict(track_a0=True, eps_rate=1.0, D=24),
    "plain_hi": dict(track_a0=False, D=24),
    "mono": dict(track_a0=True, omega=1 / kappa),
    "confine": dict(track_a0=True, w_from=40),
}
which = sys.argv[1:] or list(variants)
idx = [np.argmin(np.abs(M.lam - t)) for t in
       [1e-4, 3e-4, 6e-4, 1e-3, 2e-3, 5e-3, 0.01, 0.03, 0.1, 0.2, 0.3, 0.4, 0.49]]
print("lambda      " + " ".join(f"{M.lam[i]:8.1e}" for i in idx))
g0 = M.state(yd)["v"] / M.x0
print("g at start  " + " ".join(f"{g0[i]:8.3f}" for i in idx))
for name in which:
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        y, sf = run(M, yd, label=name, steps=400, **variants[name])
    lines = buf.getvalue().strip().splitlines()
    print(f"\n{name}: last line of log:\n  {lines[1].strip()}\n  {lines[-1].strip()}")
    g = sf["v"] / M.x0
    print("g at end    " + " ".join(f"{g[i]:8.3f}" for i in idx))
    yn = sf["y"] * np.sqrt(sf["tau"])
    print("y*sqrt(tau)/x0 " + " ".join(f"{(yn/M.x0)[i]:8.3f}" for i in idx))
