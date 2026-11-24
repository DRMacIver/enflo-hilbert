"""Cross-check explicit extremal states, not the infinite-dimensional theorem.

Run from the repository root: python experiments/check_core.py
The independent Tikhonov solve tests the designed series; grid refinement tests
selected integrated observables. Neither supplies rigorous quadrature bounds.
"""
import numpy as np
from numpy.testing import assert_allclose

from explicit_states import J, Model, k, kappa


def check_grid(points):
    model = Model(0.05, n=points)
    assert_allclose(model.integ(model.x0**2), 1, atol=2e-9, rtol=0)
    assert_allclose(model.integ(model.x0) / np.sqrt(kappa), np.sqrt(3) / 2,
                    atol=2e-9, rtol=0)
    u1 = 2 * (model.x0 - k)
    assert_allclose(model.integ(u1**2), 1, atol=1e-8, rtol=0)
    assert_allclose(model.integ(u1) / np.sqrt(kappa), 0, atol=1e-8, rtol=0)

    start, _ = model.tikhonov(np.full_like(model.lam, k), model.t0)
    expected = model.mu * model.sigma ** np.arange(J) / (np.arange(J) + 1)
    assert_allclose(start, expected, atol=2e-9, rtol=0)

    observables = []
    max_error = 0.0
    # Nearly complete periods on each of the chosen bump subintervals keep
    # this modest, resolved frequency in the positive-radicand regime.
    frequency = round(20 * np.pi / model.sigma)
    for fraction, alpha in [(1.0, 0.0), (0.5, 0.5), (0.5, 1.0), (0.2, 1.2)]:
        state = model.state(model.sigma * fraction, alpha, N=frequency)
        a, t, v, y = (state[key] for key in ("a", "t", "v", "y"))
        computed, _ = model.tikhonov(y, t)
        error = float(np.max(np.abs(computed - a)))
        max_error = max(max_error, error)
        assert_allclose(computed, a, atol=1e-10, rtol=1e-9)

        tau = t * np.sum(np.abs(a)**2)
        pairing = model.integ(v * np.conj(model.x0 - v))
        assert_allclose(pairing, tau, atol=1e-10, rtol=1e-9)
        eps2 = model.integ(np.abs(model.x0 - v)**2)
        assert_allclose(model.integ(np.abs(v)**2) + eps2 + 2 * tau, 1,
                        atol=2e-9, rtol=0)
        if tau <= 0 or not np.isfinite(tau):
            raise AssertionError(f"Invalid defect: {tau}")
        tail = np.sum(np.abs(a[1:])**2)
        if abs(a[0])**2 < 100 * tail:
            raise AssertionError("Leading-coefficient dominance failed")

        # All computed orbit pairings are bounded by tau. The omitted moments
        # have the elementary geometric bound stated in the paper.
        moments = model.moments(v * np.conj(model.x0 - v))
        if np.max(np.abs(moments)) > tau + 1e-10:
            raise AssertionError("Orbit pairing exceeds the extremal defect")
        tail_bound = kappa**J * np.sqrt(model.integ(abs(v)**2) * eps2)
        if tail_bound > 1e-12:
            raise AssertionError("Series truncation bound is too large")
        observables.append([tau, eps2, tail])
    print(f"{points:>6} points: extremal identities passed; max coefficient error {max_error:.2e}")
    return np.array(observables)


if __name__ == "__main__":
    coarse = check_grid(40_000)
    fine = check_grid(80_000)
    assert_allclose(coarse, fine, atol=2e-6, rtol=2e-4)
    print("Grid-refinement check passed (finite discretisation only).")
