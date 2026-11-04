# fisher-information

Finite and measure-theoretic Fisher information identities in Lean 4 with Mathlib:
the second derivative of KL in its second parameter equals the expected squared score.

The library provides:

- A finite-sample identity for twice differentiable normalized families with nonzero
  coordinates. The theorem retains its global real-parameter regularity assumptions.
- An integral identity on a measured sample space, under explicit measurability,
  integrability, nonvanishing, and dominated-differentiation hypotheses. A companion theorem
  derives the zero integral of the second density derivative from local normalization.
- A bridge from the real density expression `∫ p * log (p / q)` to Mathlib's
  extended-real measure KL, stated using `.toReal` and the listed density hypotheses.
- Line-directional variants for parameters in a real normed vector space, including a
  Fréchet-derivative expression for the integral score under pointwise differentiability.

These are formalizations of classical identities. This package does not include the
Čencov uniqueness theorem, a manifold connection, or a general statistical inference API.
The real-valued definitions are total expressions; positivity and analytic hypotheses must
be supplied when interpreting them as information of probability densities.

## Use

```lean
import FisherInformation

open FisherInformation
open scoped BigOperators

example {α : Type*} [Fintype α] (p : ℝ → α → ℝ) (θ : ℝ)
    (h0 : ∀ t x, p t x ≠ 0)
    (h1 : ∀ t, ∑ x, p t x = 1)
    (hd : ∀ x, Differentiable ℝ (fun t ↦ p t x))
    (hdd : ∀ x, Differentiable ℝ (fun t ↦ deriv (fun u ↦ p u x) t)) :
    fisherKL p θ = fisherScore p θ :=
  fisherKL_eq_fisherScore p θ h0 h1 hd hdd
```

The opt-in, built [Bernoulli examples](FisherInformationExamples/Bernoulli.lean) discharge
those hypotheses for the globally positive logistic family. They prove Fisher information
`1/4` at parameter zero through the finite KL Hessian, the counting-measure KL Hessian,
and the integral score. A further consumer applies the measure-KL bridge to two arbitrary
members of that family.

## Build

Supported pair: **Lean 4.34.1**, **Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`**. All dependencies are locked in
`lake-manifest.json`; other versions have not been qualified.

```bash
lake exe cache get
lake --rehash --wfail build
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/verify.py
```

The verifier rebuilds authored source artifacts, runs all 16 source linters with warnings
fatal, and checks every named public declaration's transitive axioms against
`Classical.choice`, `Quot.sound`, and `propext`. Examples build by default but are not
imported by the library root. See [API and qualification notes](docs/overview.md).
The [local qualification receipt](docs/qualification.md) records the checked source and results.

## References and license

- S. Amari and H. Nagaoka, *Methods of Information Geometry*, AMS/Oxford, 2000.
- T. Cover and J. Thomas, *Elements of Information Theory*, 2nd edition, Wiley, 2006.
- Mathlib's parametric-integral, derivative, and KL-divergence libraries.

Copyright 2026 Adam Benenson. Apache 2.0. See [LICENSE](LICENSE), [NOTICE](NOTICE),
and [extraction provenance](ORIGIN.json). The source comparison in
[docs/overlap-audit.md](docs/overlap-audit.md) distinguishes these identities and adapters
from their existing Mathlib foundations. Upstream submission or acceptance is a separate outcome.
