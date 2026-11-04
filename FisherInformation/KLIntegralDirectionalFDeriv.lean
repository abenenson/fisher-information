/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import FisherInformation.KLIntegralDirectional

/-!
# `FisherInformation.KLIntegralDirectionalFDeriv`

Rewrite lemmas for directional integral Fisher quantities in terms of Fréchet derivatives.

The directional integral score Fisher `fisherScoreIntegralDir` is defined by restricting a
vector-parameter density family `p : Θ → X → ℝ` to a 1D line `t ↦ θ + t • v` and applying the 1D
integral score Fisher formula.

Under pointwise Fréchet differentiability of `p · x` at `θ`, we can rewrite the line derivative
`deriv (t ↦ p (θ + t•v) x) 0` as `(fderiv p θ) v`, giving a cleaner expression for the
directional score Fisher integral.
-/

namespace FisherInformation

noncomputable section

open TopologicalSpace MeasureTheory Filter Metric

universe uΘ uX

variable {Θ : Type uΘ} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
variable {X : Type uX} [MeasurableSpace X]

/-- Under pointwise Fréchet differentiability at the supplied base point, directional score
Fisher equals the integral of the squared Fréchet directional derivative divided by the same
density. -/
theorem fisherScoreIntegralDir_eq_integral_fderiv_sq_div (μ : Measure X) (p : Θ → X → ℝ) (θ v : Θ)
    (hp_diff : ∀ x : X, DifferentiableAt ℝ (fun t : Θ ↦ p t x) θ) :
    fisherScoreIntegralDir (μ := μ) p θ v =
      ∫ x, ((fderiv ℝ (fun t : Θ ↦ p t x) θ) v) ^ 2 / p θ x ∂μ := by
  have h_line (x : X) :
      deriv (fun t : ℝ ↦ p (θ + t • v) x) 0 =
        (fderiv ℝ (fun t : Θ ↦ p t x) θ) v := by
    have h :=
      (hp_diff x).lineDeriv_eq_fderiv (x := θ) (v := v) (f := fun t : Θ ↦ p t x)
    simpa [lineDeriv] using h
  -- Unfold definitions and rewrite the 1D derivative via `h_line`.
  simp [fisherScoreIntegralDir, fisherScoreIntegral, pLine, h_line]

/-- Directional integral KL-Hessian Fisher rewritten via Fréchet derivatives,
under `KLIntegralRegularAt`
for the line restriction and pointwise Fréchet differentiability at the base point. -/
theorem fisherKLIntegralDir_eq_integral_fderiv_sq_div (μ : Measure X) (p : Θ → X → ℝ) (θ v : Θ)
    (h : KLIntegralRegularAt (μ := μ) (pLine (p := p) θ v) 0)
    (hp_diff : ∀ x : X, DifferentiableAt ℝ (fun t : Θ ↦ p t x) θ) :
    fisherKLIntegralDir (μ := μ) p θ v =
      ∫ x, ((fderiv ℝ (fun t : Θ ↦ p t x) θ) v) ^ 2 / p θ x ∂μ := by
  calc
    fisherKLIntegralDir (μ := μ) p θ v
        = fisherScoreIntegralDir (μ := μ) p θ v := by
            simpa using fisherKLIntegralDir_eq_fisherScoreIntegralDir (μ := μ) (p := p) (θ := θ)
              (v := v) h
    _ = ∫ x, ((fderiv ℝ (fun t : Θ ↦ p t x) θ) v) ^ 2 / p θ x ∂μ := by
          simpa using fisherScoreIntegralDir_eq_integral_fderiv_sq_div (μ := μ) (p := p) (θ := θ)
            (v := v) hp_diff

end

end FisherInformation
