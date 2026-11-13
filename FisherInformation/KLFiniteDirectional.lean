/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import FisherInformation.KLFinite
public import FisherInformation.RegularFinite

/-!
# `FisherInformation.KLFiniteDirectional`

Directional (line-based) KL/Fisher identities for vector-space parameters, finite sample spaces.

Given a parameter space `Θ` (real normed vector space) and a finite sample space `α`, we can
evaluate KL divergence and Fisher information **along a 1D line** `t ↦ θ + t • v`.

This module packages that construction and lifts the existing 1D theorem
`FisherInformation.fisherKL_eq_fisherScore` to arbitrary `Θ` via this line restriction.

## Main results

- `FisherInformation.fisherKLDir_eq_fisherScoreDir` (under `RegularDensityModelFinite`)
-/

@[expose] public section

open scoped BigOperators

namespace FisherInformation

namespace Fisher

universe uΘ uα

variable {Θ : Type uΘ} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
variable {α : Type uα} [Fintype α]

/-- Restrict a density family `p : Θ → α → ℝ` to the line `t ↦ θ + t • v`. -/
noncomputable def pLine (p : Θ → α → ℝ) (θ v : Θ) : ℝ → α → ℝ :=
  fun t x ↦ p (θ + t • v) x

/-- Score Fisher information along the line family `t ↦ θ + t•v`, evaluated at `t=0`. -/
noncomputable def fisherScoreDir (p : Θ → α → ℝ) (θ v : Θ) : ℝ :=
  _root_.FisherInformation.fisherScore (α := α) (p := pLine (α := α) p θ v) 0

/-- KL-Hessian Fisher information along the line family `t ↦ θ + t•v`, evaluated at `t=0`. -/
noncomputable def fisherKLDir (p : Θ → α → ℝ) (θ v : Θ) : ℝ :=
  _root_.FisherInformation.fisherKL (α := α) (p := pLine (α := α) p θ v) 0

/-- Under `RegularDensityModelFinite`, the directional KL-Hessian Fisher equals the directional
score Fisher along every line `t ↦ θ + t • v`. -/
theorem fisherKLDir_eq_fisherScoreDir (M : _root_.FisherInformation.RegularDensityModelFinite Θ α)
    (θ v : Θ) :
    fisherKLDir (α := α) M.p θ v = fisherScoreDir (α := α) M.p θ v := by
  classical
  -- Apply the 1D theorem to the line restriction `pLine`.
  simpa [fisherKLDir, fisherScoreDir, pLine] using!
    (_root_.FisherInformation.fisherKL_eq_fisherScore (α := α)
      (p := fun t x ↦ M.p (θ + t • v) x)
      (θ := (0 : ℝ))
      (hp0 := by
        intro t x
        exact M.ne_zero (θ := θ + t • v) x)
      (hnorm := by
        intro t
        simpa using M.sum_eq_one (θ := θ + t • v))
      (hp1 := by
        intro x
        -- Line differentiability supplied by the interface.
        simpa using M.line_diff θ v x)
      (hp2 := by
        intro x
        -- 2nd-order line differentiability supplied by the interface.
        simpa using M.line_diff_deriv θ v x))

end Fisher

end FisherInformation
