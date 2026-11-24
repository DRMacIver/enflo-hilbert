# A local continuation obstruction in Enflo's argument

**Start with [the paper (PDF)](output/pdf/refutation.pdf).** Its source is
[tex/refutation.tex](tex/refutation.tex). This repository examines the convergence
step after equation (46) of P. H. Enflo's *On the invariant subspace problem in
Hilbert spaces*, [arXiv:2305.15442v2](https://arxiv.org/abs/2305.15442v2).

The core problem is that **small defect does not ensure that further improvement
is possible inside the ball imposed by the convergence constraint**. In the
multiplication operator on complex `L²[0, κ]`, the paper constructs explicit
extremal states satisfying the listed admissibility conditions, with arbitrarily
small defect, for which every state in a neighbourhood has defect bounded below
by a strictly positive number. The bound depends on the chosen state.

This is a critique of a continuation inference, not a disproof of the invariant
subspace theorem. The model has invariant subspaces. Applying the obstruction to
Enflo's reasoning requires checking which consequences of transitivity the
argument actually uses; the paper's Discussion gives that audit.

## The mechanism

For a unit vector `x₀`, define

$$
\Delta(u)=\sup_{j\geq0}|\langle T^j u,x_0-u\rangle|.
$$

For extremal images this equals the nonnegative defect `τ`. A nontrivial norm
limit with defect zero gives an invariant subspace. Enflo's constraint confines
the proposed descent to a small ball. The obstruction is the inequality

$$
\|u-v\|^2+K\Delta(u)\ \geq
\tfrac14\bigl(\|x_0\|^2-\|Cx_0\|^2\bigr),\qquad
v=\tfrac12(x_0+Wx_0),\quad C=\tfrac12(W+W^*),
$$

where `W` is an isometry and both `W` and `W*` are absolutely summable power
series in `T`, with coefficient norm sums at most `K`. In the model, oscillation
can make the defect small while the right side stays bounded away from zero.
The explicit extremal states transfer this obstruction to the admissibility
conditions used in the continuation claim.

## What is established where

| Material | Role and verification boundary |
| --- | --- |
| [Standalone paper](tex/refutation.tex) | Hand proofs of the explicit states, non-degeneracy conditions, and failure of Claim (C). The supplementary reachability result has the limitations below. |
| [Basic.lean](EnfloHilbert/Basic.lean) | Non-cyclicity criterion and confinement identity. |
| [Model.lean](EnfloHilbert/Model.lean) | Pointwise complex-number identities; it does **not** formalise the `L²` model. |
| [Rigidity.lean](EnfloHilbert/Rigidity.lean) | Abstract rigidity inequality and its self-adjoint specialisation. |
| [Oscillating.lean](EnfloHilbert/Oscillating.lean) | Abstract no-continuation inequality and oscillating-state defect identity. |
| [Companion notes](tex/main.tex) | Broader analysis: repaired lemmas, Case II, type 2, and exploratory numerical observations. These notes include explicitly open and outline-only statements. |
| [Numerical checks](experiments/README.md) | Finite discretisation checks and exploratory flows. They do not prove the infinite-dimensional assertions. |
| [Source under examination](paper/Enflo_06_April_2024-arXiv.tex) | Included version of Enflo's preprint, with its original figure. |

The Lean development contains no `sorry` or added axioms. It does not formalise
the explicit admissible family, its asymptotic estimates, or the reachability
argument. The mathematical text uses inner products linear in the first
variable; Mathlib uses the second, so arguments are reversed in Lean.

The reachability result preserves the listed **state conditions** along small
norm steps. It does not bound the step degrees or coefficient sizes as envisaged
in the original construction, and does not validate its first-order formulas.
It starts at the same vector `y₀`, with a residual level slightly above `1/2`
rather than in Enflo's prescribed interval ending at `1/2`. A special selection
rule avoiding the obstructed states is not ruled out. The core neighbourhood
obstruction does not depend on this supplementary result.

## Reproduce the checks

The three components can be used independently. `make help` lists the commands.

**Lean.** Install Lean's `elan` toolchain manager. The repository pins Lean and
Mathlib to `v4.29.1`; Lake uses `lake-manifest.json` for dependencies. From the
repository root:

```sh
lake exe cache get
make lean
```

The first command downloads Mathlib's compiled cache. A first setup needs network
access; subsequent checks use the installed dependencies.

**Python.** Use Python 3.12 or later. The pinned package versions were checked with
Python 3.14.2. Create an isolated environment:

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -r requirements.txt
make check PYTHON=.venv/bin/python
```

This runs assertions for the explicit-state identities at two grid resolutions,
including an independently solved Tikhonov system, the defect identity, and the
normalisation of `x₀`. It exits unsuccessfully on a failed check. See
[experiments/README.md](experiments/README.md) for larger runs and numerical limits.

**PDF.** Install a TeX distribution providing `pdflatex`, `latexmk`, the AMS
packages, `geometry`, `enumitem`, `microtype`, `xcolor`, and `hyperref`:

```sh
make pdf       # refresh output/pdf/refutation.pdf
make notes     # optional broader notes: build/tex/main.pdf
```

The shareable PDF is committed so a reader needs no TeX installation. Intermediate
files go into ignored `build/`. The PDF build fixes its timestamp to the draft
date; byte-for-byte reproduction also requires the same TeX distribution.
`make clean` removes intermediates, leaving the committed PDF and installed
dependencies in place.

## Repository history

Commit `7dd4a85` preserves the research workspace before preparation for sharing.
The unreliable Case II numerical script and the duplicate source tarball were
removed from the working tree after that snapshot. They remain recoverable from
Git history. The Case II discussion in the companion notes distinguishes its
hand argument from historical floating-point observations.

This is a research draft for scrutiny. The central question for a reviewer is
whether Claim (C) correctly isolates the local inference made after (46), and
whether the explicit states satisfy the conditions that inference needs.
