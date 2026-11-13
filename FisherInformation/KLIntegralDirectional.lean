/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import FisherInformation.KLIntegralRegularAt

/-!
# `FisherInformation.KLIntegralDirectional`

Directional (line-based) Fisher identities in the integral setting.

For a vector-space parameter `Θ` and a measurable sample space `X`, we can restrict a density
family `p : Θ → X → ℝ` to a 1D line `t ↦ θ + t • v`. This produces a 1D family
`pLine : ℝ → X → ℝ`, so the 1D integral Fisher identity from `KLIntegral` applies.

This module defines the corresponding “directional integral Fisher” quantities and provides a
wrapper theorem under the packaged `KLIntegralRegularAt` hypotheses on the line family.
-/

@[expose] public section

namespace FisherInformation

noncomputable section

open TopologicalSpace MeasureTheory Filter Metric
open scoped BigOperators

universe uΘ uX

variable {Θ : Type uΘ} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
variable {X : Type uX} [MeasurableSpace X]

/-- Restrict a `Θ`-indexed density family `p` to the line `t ↦ θ + t • v`. -/
noncomputable def pLine (p : Θ → X → ℝ) (θ v : Θ) : ℝ → X → ℝ :=
  fun t x ↦ p (θ + t • v) x

/-- Score-squared Fisher information (integral version) along the line family `t ↦ θ + t • v`,
evaluated at `t = 0`. -/
noncomputable def fisherScoreIntegralDir (μ : Measure X) (p : Θ → X → ℝ) (θ v : Θ) : ℝ :=
  fisherScoreIntegral (μ := μ) (p := pLine (p := p) θ v) 0

/-- KL-Hessian Fisher information (integral version) along the line family `t ↦ θ + t • v`,
evaluated at `t = 0`. -/
noncomputable def fisherKLIntegralDir (μ : Measure X) (p : Θ → X → ℝ) (θ v : Θ) : ℝ :=
  fisherKLIntegral (μ := μ) (p := pLine (p := p) θ v) 0

/-- Directional integral Fisher identity: along a line `t ↦ θ + t • v`, the KL-Hessian Fisher equals
the score-squared Fisher under `KLIntegralRegularAt` hypotheses for the line family at `t = 0`. -/
theorem fisherKLIntegralDir_eq_fisherScoreIntegralDir (μ : Measure X) (p : Θ → X → ℝ) (θ v : Θ)
    (h : KLIntegralRegularAt (μ := μ) (pLine (p := p) θ v) 0) :
    fisherKLIntegralDir (μ := μ) p θ v = fisherScoreIntegralDir (μ := μ) p θ v := by
  simpa [fisherKLIntegralDir, fisherScoreIntegralDir, pLine] using
    (fisherKLIntegral_eq_fisherScoreIntegral_of_regularAt (μ := μ)
      (p := pLine (p := p) θ v) (θ := (0 : ℝ)) h)

end

end FisherInformation
