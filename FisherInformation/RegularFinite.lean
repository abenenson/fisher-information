/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import FisherInformation.KLFinite

/-!
# `FisherInformation.RegularFinite`

Regularity interface for finite/discrete density models.

This module introduces a minimal “regular parametric density” interface for **finite sample
spaces**, designed to support derived Fisher-geometry results without committing to manifolds or
PDE/elliptic machinery.

The key design choice is to express differentiability requirements **along 1D lines**
`t ↦ θ + t • v`, which is sufficient to reuse existing 1D (`deriv`-based) finite KL/Fisher lemmas.

## Main definitions

- `FisherInformation.RegularDensityModelFinite`
-/

@[expose] public section

open scoped BigOperators

namespace FisherInformation

universe uΘ uα

variable {Θ : Type uΘ} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
variable {α : Type uα} [Fintype α]

/-- A regular parametric density family on a finite sample space.

This is an interface: it packages just enough hypotheses to (a) form finite-sum KL, and (b) apply
1D differentiation lemmas to the line family `t ↦ θ + t • v`. -/
structure RegularDensityModelFinite (Θ : Type uΘ) [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
    (α : Type uα) [Fintype α] : Type (max uΘ uα) where
  /-- The density family `p(θ,x)`. -/
  p : Θ → α → ℝ
  /-- Strict positivity. -/
  pos : ∀ θ x, 0 < p θ x
  /-- Finite-sum normalization `∑_x p(θ,x) = 1`. -/
  sum_eq_one : ∀ θ, (∑ x : α, p θ x) = 1
  /-- Differentiability of `t ↦ p(θ + t•v, x)` at every `t` (line regularity). -/
  line_diff : ∀ θ v x, Differentiable ℝ (fun t : ℝ ↦ p (θ + t • v) x)
  /-- Differentiability of the derivative of `t ↦ p(θ + t•v, x)` (2nd-order line regularity). -/
  line_diff_deriv :
    ∀ θ v x,
      Differentiable ℝ
        (fun t : ℝ ↦ deriv (fun u : ℝ ↦ p (θ + u • v) x) t)

namespace RegularDensityModelFinite

variable (M : RegularDensityModelFinite Θ α)

/-- Every coordinate of a regular finite density is nonzero. -/
lemma ne_zero (θ : Θ) (x : α) : M.p θ x ≠ 0 :=
  ne_of_gt (M.pos θ x)

/-- Every coordinate remains nonzero along each parameter line. -/
lemma line_ne_zero (θ v : Θ) (t : ℝ) (x : α) : M.p (θ + t • v) x ≠ 0 :=
  ne_of_gt (M.pos (θ + t • v) x)

end RegularDensityModelFinite

end FisherInformation
