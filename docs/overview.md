# KL curvature and score Fisher information

The finite definitions are the real sum `∑ x, p x * log (p x / q x)`, its second-parameter
second derivative, and `∑ x, (p' x)^2 / p x`. The identity differentiates the normalized
sum twice, derives `∑ p'' = 0`, and cancels that term from the quotient-rule expansion.
The finite theorem assumes nonzero coordinates and normalization at every real parameter,
plus differentiability of each coordinate and of its first derivative. Nonzero real
coordinates alone are weaker than positivity; density interpretation retains that distinction.

The integral development uses Bochner integrals, whose total definitions do not themselves
establish integrability. It differentiates under the integral twice with supplied measurable
integrands and integrable domination bounds. The main theorem takes `∫ p'' = 0` as an explicit
premise; a companion theorem proves it from local constant total mass with its own complete
dominated-differentiation ledger. `KLIntegralRegularAt` packages the main theorem's premises
without proving them. Its fields remain visible and are not a new axiom.

The density-to-measure adapter keeps nonnegative integrable densities, equal total mass,
an almost-everywhere nonzero reference, sigma-finiteness of the base measure, integrability
of the logarithmic-ratio expression, and absolute continuity of the induced measures.
The conclusion explicitly applies `.toReal` to Mathlib's `klDiv`; the library does not use
`.toReal` as a test for finiteness or for equality of arbitrary extended-real divergences.

## Modules

- `KLFinite`: finite KL/score definitions and the finite Fisher identity.
- `KLIntegral`: integral definitions, differentiated KL, normalization, and Fisher identities.
- `KLDivBridge`: density formulas expressed through Mathlib's measure KL.
- `RegularFinite`: positive normalized finite families with twice differentiable line restrictions.
- `KLFiniteDirectional`: finite line-directional quantities in `FisherInformation.Fisher`.
- `KLIntegralRegularAt`: explicit local regularity data for the integral identity.
- `KLIntegralDirectional`: integral quantities along a vector-parameter line.
- `KLIntegralDirectionalFDeriv`: Fréchet-derivative rewrites of the directional integral score.
- `ScoreFinite`: log-density score differentials and their finite Fisher bilinear form.
- `FiniteRiemannian`: the actual score form as a smooth tangent-bundle Riemannian metric.

The top-level library imports all these focused mathematical modules. Only Mathlib and its
locked public dependencies are required.

## Smooth finite Fisher metric

`FisherInformation.Fisher.scoreCLM p θ x` is the Fréchet derivative of
`θ ↦ log (p θ x)`. The bilinear form `fisherScoreBilin p θ` is the finite sum
`∑ x, p θ x * scoreCLM p θ x u * scoreCLM p θ x v` on directions `u` and `v`.
The continuous bilinear map `fisherScoreContinuousBilin` has exactly this evaluation.

For a finite sample space and a finite-dimensional real normed parameter space,
`fisherRiemannianMetric` constructs Mathlib's `Bundle.ContMDiffRiemannianMetric` on the
tangent bundle. Its hypotheses are global strict positivity of every atom, global `C∞`
regularity of every atom, and `ScoreSeparating p`: each nonzero direction has a nonzero
score at every parameter. The proof derives positive definiteness, boundedness of each
metric unit ball, and smoothness of the actual score bilinear form. The evaluation theorem
`fisherRiemannianMetric_inner` identifies every tangent pairing with `fisherScoreBilin`.

This construction does not infer normalization or score separation from smoothness.
Normalization must be checked separately for a probability-law interpretation.

## Checked consumers

`FisherInformationExamples.Bernoulli` uses the log-odds family on `Bool`:
`pθ(false)=1/(1+exp θ)` and `pθ(true)=exp θ/(1+exp θ)`.
Both coordinates are positive and their sum is one at every real parameter. Explicit
derivatives show nonzero sensitivity at zero and a Fisher value of `1/4`. The consumer
applies the finite identity with all its premises discharged. Counting-measure conversion
then gives the same integral Hessian and score. The measure-KL example independently
discharges every bridge premise for two members of the family.

`FisherInformationExamples.BernoulliRiemannian` proves both atoms smooth and computes
their scores for arbitrary parameters and directions. The false-outcome score is
`-exp θ / (1 + exp θ) * u`, so it is nonzero whenever `u ≠ 0`. This discharges score
separation and supplies the smooth Fisher metric for the same positive normalized family.
Its pairing at the fair member is `u * v / 4`.

These examples do not assert that generic domination or regularity data follows merely
from normalization, nor do they claim a new theorem of statistical estimation.

## Qualification contract

The verification manifest covers every authored source and explicit public declaration.
Verification rebuilds the authored artifacts from the actual source, recompiles those same
module identities with all 16 environment linters and documentation checks, and audits named
transitive axioms against `propext`, `Classical.choice`, and `Quot.sound`. The axiom check
follows private/generated helpers used by each named declaration.
The verifier freezes the authored source inventory and source/configuration hashes before
running checks. It requires the same inventory and hashes before accepting the receipt;
an edit during qualification invalidates that run.

The pinned immutable CI workflow uses read-only repository permissions and retains raw
qualification evidence even on failure. Local evidence, a hosted CI run, and a public release
are different results; a workflow file is not an execution receipt.

Source hashes and stages are written to a new `verification-artifacts` directory on each run.
Failed attempts are retained. `ORIGIN.json` records the initial public package paths and
digests; later proof or documentation changes are recorded in Git history.

## Lean 4.35 compatibility

The initial [compatibility qualification](compatibility-qualification.json) records exact-source
builds of the original eleven modules and examples, all 16 source linters, and all 46 named
transitive axiom audits. Explicit public imports and exposed public sections retain the existing
exported API and definition bodies. All previous proof bodies and theorem hypotheses remain unchanged,
including the finite theorem's global real-line assumptions and the integral domination ledger.
Dependency preparation validates every locked dependency and requests only the focused Mathlib
import closure. Earlier qualification records remain historical; local checks do not establish
hosted CI success or upstream acceptance.
