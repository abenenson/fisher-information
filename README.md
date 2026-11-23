# fisher-information

[![Lean verification](https://github.com/abenenson/fisher-information/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/abenenson/fisher-information/actions/workflows/lean.yml)

Finite and measure-theoretic Fisher information in Lean 4 with Mathlib: KL curvature
identities and smooth finite score Fisher metrics.

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
- A smooth tangent-bundle Fisher metric for finite sample spaces and finite-dimensional
  real parameter spaces, from positive smooth atoms whose scores separate directions.
- Centered scores, additivity for independent finite observations sharing a parameter,
  and exact Fisher scaling for any finite number of IID samples, including zero samples.
- Positive normalized categorical logit families with identifiable baseline coordinates,
  smooth atoms, and score separation.

These are formalizations of classical identities. This package does not include the
Čencov uniqueness theorem, a manifold connection, or a general statistical inference API.
The real-valued definitions are total expressions; positivity and analytic hypotheses must
be supplied when interpreting them as information of probability densities.

The finite theorem requires nonvanishing, normalization, and twice differentiable
coordinate functions over the whole real parameter line. The integral theorem retains
explicit domination and integrability hypotheses; `KLIntegralRegularAt` bundles those
obligations for callers. These assumptions remain part of each theorem's contract.

## Use

```lean
module

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

The [Bernoulli metric example](FisherInformationExamples/BernoulliRiemannian.lean) also
computes both log-density scores at every parameter, proves smoothness and score separation,
and constructs the actual smooth Fisher metric. At parameter zero its tangent pairing is
`u * v / 4`.

The metric constructor `FisherInformation.Fisher.fisherRiemannianMetric` takes a finite
family `p`, strict positivity, smoothness of every atom, and `ScoreSeparating p`. It proves
smoothness of the weighted score bilinear form and uses finite dimension to show compatibility
with the parameter space's topology. Normalization is a separate requirement for interpreting
the atoms as a probability law; the Bernoulli examples prove it explicitly.

## Independent samples and categorical models

`fisherScoreBilin_prod` adds the information of two independent normalized finite
observations, even when they share the same parameter. `fisherScoreBilin_iid` gives
`fisherScoreBilin (iidDensity p n) θ u v = (n : ℝ) * fisherScoreBilin p θ u v`.
The source atoms need only be nonzero and Fréchet differentiable at the parameter being
evaluated; normalization holds throughout the parameter space. The empty sample has
constant density one and zero information. Positive atoms give the probability interpretation.

The [categorical API](FisherInformation/Categorical.lean) fixes one baseline logit at zero
and uses a finite vector of remaining logits. It proves positivity, normalization,
smoothness, identifiability and score separation. The
[checked metric consumer](FisherInformationExamples/CategoricalRiemannian.lean) applies the
same smooth metric constructor. For two logits at zero, the three outcomes are equiprobable
and the tangent pairing is
`(u 0 * v 0 + u 1 * v 1) / 3 - (u 0 + u 1) * (v 0 + v 1) / 9`.
The zero-logit-coordinate case is also checked: one outcome, probability one, and a trivial
parameter space.

## Build

Supported pair: **Lean 4.35.0**, **Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`**. All dependencies are locked in
`lake-manifest.json`. The
[compatibility qualification](docs/compatibility-qualification.json) records fresh checks of this pair.

```bash
python3 scripts/fetch_mathlib_cache.py
lake --rehash --wfail build
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/verify.py
```

The verifier rebuilds authored source artifacts, runs all 16 source linters with warnings
fatal, and checks every named public declaration's transitive axioms against
`Classical.choice`, `Quot.sound`, and `propext`. Examples build by default but are not
imported by the library root. See [API and qualification notes](docs/overview.md).
The earlier [local qualification receipt](docs/qualification.md) and initial compatibility
receipt retain their original source and compiler identities. New verifier runs produce
separate receipts bound to the current source, configuration and utilities.

## References and license

- S. Amari and H. Nagaoka, *Methods of Information Geometry*, AMS/Oxford, 2000.
- T. Cover and J. Thomas, *Elements of Information Theory*, 2nd edition, Wiley, 2006.
- Mathlib's parametric-integral, derivative, and KL-divergence libraries.

Copyright 2026 Adam Benenson. Apache 2.0. See [LICENSE](LICENSE), [NOTICE](NOTICE),
and [initial public file inventory](ORIGIN.json). The source comparison in
[docs/overlap-audit.md](docs/overlap-audit.md) distinguishes these identities and adapters
from their existing Mathlib foundations. Upstream submission or acceptance is a separate outcome.

## Releases and related libraries

Start with the [`v0.1.0` release](https://github.com/abenenson/fisher-information/releases/tag/v0.1.0) for the supported toolchain and verification run.

- [cencov-petz](https://github.com/abenenson/cencov-petz) covers uniqueness of the finite Fisher metric.
- [finite-relative-entropy](https://github.com/abenenson/finite-relative-entropy) covers finite KL divergence.

[Browse the Lean library index](https://adambenenson.com/projects/#formal-methods).
