# Local release qualification

The release candidate passed local qualification on 2026-11-04 with Lean 4.34.1 and
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. The exact source and public dependency
hashes, commands, and results are retained in [the receipt](release-logs/qualification.json).

- All 11 authored library and example modules were rebuilt from their actual source,
  after removing their previously built artifacts, with warnings fatal.
- Each original module identity passed all 16 environment linters, including definition
  and theorem documentation checks. No warning suppression was used.
- All 46 explicit public declarations passed the transitive axiom audit. The only allowed
  axioms were `Classical.choice`, `Quot.sound`, and `propext`.
- All 14 verifier regression controls passed, including stale-artifact, diagnostic,
  dependency-name, and import-boundary rejection checks.

The guarded run completed in approximately 83 seconds, used two CPUs, and sampled a
peak process-tree RSS of 4,344,975,360 bytes under a 16 GiB ceiling. The resource receipt
records no surviving processes. Raw compiler, lint, axiom, resource, and regression-control
logs are in [release-logs](release-logs/).

The checked consumers are a positive logistic Bernoulli family, its Fisher information
`1/4` at zero in finite and counting-measure formulations, and a measure-KL bridge for
arbitrary pairs of family members. Their analytic premises are proved in the example.

This is local qualification evidence. Hosted CI and public repository publication are
separate steps. The immutable CI workflow repeats the same source verifier on pushes
and pull requests.
