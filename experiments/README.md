# Numerical companion

Run scripts from the repository root with the environment described in the main
README. All scripts use finite grids, truncated series, and double precision.
Their outputs illustrate or check identities; the proofs are in TeX and Lean.

## Primary checks

```sh
make check PYTHON=.venv/bin/python
.venv/bin/python experiments/explicit_states.py
```

`check_core.py` checks the explicit construction against a separate Tikhonov
linear solve at 40,000 and 80,000 grid points. It checks normalisation, the start
series, positivity of the radicand, the defect identity, coefficient dominance,
and stability of selected observables under grid refinement. Failed assertions
give a nonzero exit status. These are checks of the discretisation, not certified
quadrature or a verification of every hypothesis of the asymptotic theorem.

`explicit_states.py` prints a more detailed table, including the second coefficient
sequence and a **phase-averaged limiting path**. That table is not an executed
finite-frequency Main Construction. Defaults are `t0=0.05`, `N=200000`, and two
million grid points; the power table alone uses about 2.24 GB. For a smaller run:

```sh
.venv/bin/python experiments/explicit_states.py 0.05 10866 --points 80000
```

The finite-frequency examples check the algebraic formula. Their parameters are
not in the asymptotic regime required by the paper's no-continuation theorem.
Decreasing `t0` requires increasing both frequency and resolution. A small
linear-system residual alone cannot certify that oscillatory integrals are
resolved by the grid.

## Exploratory material

| Script | Purpose |
| --- | --- |
| `refutation_check.py` | Earlier oscillating states and their numerical re-extremalisation; uses a different `x₀` from the explicit construction. |
| `oscillating_states.py` | States and coefficient tables discussed in the broader notes. Its final parameter scan is comparatively slow. |
| `mc_flow.py` | A particular least-norm/Newton choice of steps; modes `plain`, `track`, `mono`, `confine`. |
| `mc_profile.py` | Profiles for selected flow variants, e.g. `track`. |
| `model.py` | Shared Gauss-Legendre discretisation for the flows. |

For example:

```sh
.venv/bin/python experiments/mc_flow.py track
.venv/bin/python experiments/refutation_check.py
```

The tracked flow was reproduced during preparation: after 400 steps its defect
was approximately `6.62e-4`, its distance to the solution set `0.0713` (up from
about `0.051`), and its smallest normalised constraint singular value `1.44e-4`.
Floating-point step choices can vary across BLAS implementations. This is
evidence about this particular algorithm, not all possible choices of steps.

The former `case2_test.py` is available in commit `7dd4a85`. It produced negative
computed defects and failed to attain its requested starting residual in some
runs, violating identities that exact extremal states must satisfy. It is omitted
from the maintained experiments. The historical ratios in the notes must not be
read as a verified Case II counterexample.
