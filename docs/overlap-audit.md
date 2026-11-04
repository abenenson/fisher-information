# Mathlib overlap and contribution scope

The supported dependency is Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, paired with Lean 4.34.1.

The mathematical identities are classical. This package assembles a focused, explicitly
scoped formal API; it does not claim priority, exclusive formalization, new mathematical
results, or Mathlib acceptance.

## Existing foundations

- `Mathlib.Analysis.Calculus.ParametricIntegral` provides dominated differentiation of
  parametric Bochner integrals. The integral KL proof supplies its hypotheses explicitly.
- `Mathlib.Analysis.SpecialFunctions.Log.Deriv` and the ordinary derivative API provide
  the log, product, quotient, and finite-sum rules used by the finite proof.
- `Mathlib.Analysis.Calculus.LineDeriv.Basic` identifies the line derivative with the
  Fréchet derivative applied to the direction under differentiability.
- `Mathlib.InformationTheory.KullbackLeibler.Basic` and `KLFun` own measure KL and its
  real-valued integral representation. The package's measure adapter applies these APIs
  with densities; it does not reimplement measure KL or its data-processing theory.
- `Measure.withDensity`, Radon–Nikodym transport, and integration against densities
  provide the remaining adapter steps.

## Scoped API contribution

The finite and integral identities expose the equality between two concrete definitions:
KL curvature in the reference parameter and score-squared expectation. The line wrappers
reuse these identities after explicit parameter restriction. The regularity structures
package analytic assumptions; they do not discharge them automatically.

The density-to-measure bridge includes all its nonnegativity, equal-mass, integrability,
nonzero-reference, sigma-finiteness, and absolute-continuity assumptions. It is an adapter
to the existing extended-real KL API, stated with `.toReal`.

Potential upstream work would be one focused identity or adapter at a time, with naming,
minimal hypotheses, and equivalent Mathlib formulations reviewed first. The present source
inspection is not an exhaustive search of all equivalent formalizations or external libraries.
