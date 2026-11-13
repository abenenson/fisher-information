/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import FisherInformation.KLIntegral

/-!
# `FisherInformation.KLIntegralRegularAt`

Packaged regularity hypotheses for `KLIntegral` Fisher identities.

`FisherInformation.KLIntegral` proves the identity

`fisherKLIntegral (μ := μ) p θ = fisherScoreIntegral (μ := μ) p θ`

under an explicit (and necessarily long) list of dominated-differentiation hypotheses.

This module packages those hypotheses into a single structure `KLIntegralRegularAt` so downstream
code can depend on a named interface rather than threading 20+ arguments.
-/

@[expose] public section

namespace FisherInformation

noncomputable section

open TopologicalSpace MeasureTheory Filter Metric

variable {α : Type*} [MeasurableSpace α]
variable (μ : Measure α)

/-- Regularity hypotheses at a base point `θ` sufficient to apply
`fisherKLIntegral_eq_fisherScoreIntegral` to `p`. -/
structure KLIntegralRegularAt (p : ℝ → α → ℝ) (θ : ℝ) : Type _ where
  /-- Radius of the parameter neighborhood used for differentiation. -/
  ε : ℝ
  /-- The parameter neighborhood has positive radius. -/
  ε_pos : 0 < ε
  /-- Each density value is nonzero at every parameter. -/
  hp0 : ∀ t : ℝ, ∀ x : α, p t x ≠ 0
  /-- Each pointwise density is differentiable on the neighborhood. -/
  hp1 : ∀ x : α, ∀ t ∈ ball θ ε, DifferentiableAt ℝ (fun u ↦ p u x) t
  /-- Each pointwise first derivative is differentiable on the neighborhood. -/
  hp2 : ∀ x : α, ∀ t ∈ ball θ ε, DifferentiableAt ℝ (fun u ↦ deriv (fun s ↦ p s x) u) t
  /-- The KL integrand is almost everywhere strongly measurable on the neighborhood. -/
  hKL_meas :
    ∀ t ∈ ball θ ε,
      AEStronglyMeasurable (fun x ↦ p θ x * Real.log (p θ x / p t x)) μ
  /-- The KL integrand is integrable on the neighborhood. -/
  hKL_int :
    ∀ t ∈ ball θ ε, Integrable (fun x ↦ p θ x * Real.log (p θ x / p t x)) μ
  /-- Its pointwise parameter derivative is almost everywhere strongly measurable. -/
  hKL'_meas :
    ∀ t ∈ ball θ ε,
      AEStronglyMeasurable (fun x ↦ (-(p θ x) * (deriv (fun u ↦ p u x) t / p t x))) μ
  /-- Dominating function for the first parameter derivative. -/
  bound₁ : α → ℝ
  /-- The first derivative is bounded uniformly over the parameter neighborhood. -/
  h_bound₁ :
    ∀ᵐ x ∂μ, ∀ t ∈ ball θ ε, ‖-(p θ x) * (deriv (fun u ↦ p u x) t / p t x)‖ ≤ bound₁ x
  /-- The first dominating function is integrable. -/
  bound₁_int : Integrable bound₁ μ
  /-- The first derivative integrand is integrable at the base parameter. -/
  hKL'_int :
    Integrable (fun x ↦ (-(p θ x) * (deriv (fun u ↦ p u x) θ / p θ x))) μ
  /-- The second derivative integrand is almost everywhere strongly measurable at the base. -/
  hKL''_meas :
    AEStronglyMeasurable
      (fun x ↦
        (-(p θ x) *
          ((deriv (fun u ↦ deriv (fun s ↦ p s x) u) θ * p θ x -
                  deriv (fun u ↦ p u x) θ * deriv (fun u ↦ p u x) θ) / (p θ x) ^ 2))) μ
  /-- Dominating function for the second parameter derivative. -/
  bound₂ : α → ℝ
  /-- The second derivative is bounded uniformly over the parameter neighborhood. -/
  h_bound₂ :
    ∀ᵐ x ∂μ, ∀ t ∈ ball θ ε,
      ‖-(p θ x) *
          ((deriv (fun u ↦ deriv (fun s ↦ p s x) u) t * p t x -
                  deriv (fun u ↦ p u x) t * deriv (fun u ↦ p u x) t) / (p t x) ^ 2)‖
        ≤ bound₂ x
  /-- The second dominating function is integrable. -/
  bound₂_int : Integrable bound₂ μ
  /-- The squared-score integrand is integrable at the base parameter. -/
  hScore_int : Integrable (fun x ↦ (deriv (fun t ↦ p t x) θ) ^ 2 / p θ x) μ
  /-- The density's second parameter derivative is integrable at the base parameter. -/
  hSecond_int : Integrable (fun x ↦ deriv (fun u ↦ deriv (fun s ↦ p s x) u) θ) μ
  /-- The density's second parameter derivative integrates to zero at the base parameter. -/
  hInt_second : (∫ x, deriv (fun u ↦ deriv (fun s ↦ p s x) u) θ ∂μ) = 0

/-- Apply the integral KL-Hessian identity using the packaged regularity hypotheses. -/
theorem fisherKLIntegral_eq_fisherScoreIntegral_of_regularAt
    (p : ℝ → α → ℝ) (θ : ℝ) (h : KLIntegralRegularAt (μ := μ) p θ) :
    fisherKLIntegral (μ := μ) p θ = fisherScoreIntegral (μ := μ) p θ := by
  classical
  exact
    fisherKLIntegral_eq_fisherScoreIntegral (μ := μ) (p := p) (θ := θ) (ε := h.ε) h.ε_pos
      h.hp0 h.hp1 h.hp2 h.hKL_meas h.hKL_int h.hKL'_meas h.bound₁ h.h_bound₁ h.bound₁_int
      h.hKL'_int h.hKL''_meas h.bound₂ h.h_bound₂ h.bound₂_int h.hScore_int h.hSecond_int
      h.hInt_second

end

end FisherInformation
