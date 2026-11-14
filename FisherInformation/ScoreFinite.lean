/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Basic

/-!
# Finite score Fisher bilinear forms

The score differential is the Fréchet derivative of each log-density atom. Its weighted
outer products define the finite Fisher bilinear form. Strict positivity and separation
of parameter directions by the scores imply positive definiteness.

These definitions are total real expressions. Normalization is a separate hypothesis when
interpreting the atoms as a probability law.

## Main results

- `fisherScoreBilin.apply`: the bilinear form is the weighted finite score sum.
- `fisherScoreBilin_pos_of_exists`: a nonzero score gives a positive diagonal value.
- `ScoreSeparating`: scores detect every nonzero parameter direction.
-/

@[expose] public section

open scoped BigOperators

namespace FisherInformation.Fisher

variable {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
variable {α : Type*}

/-- The score differential `D_θ log(p θ x)` as a continuous linear map. -/
noncomputable def scoreCLM (p : Θ → α → ℝ) (θ : Θ) (x : α) : Θ →L[ℝ] ℝ :=
  fderiv ℝ (fun t ↦ Real.log (p t x)) θ

/-- The scores separate parameter directions at every parameter. -/
def ScoreSeparating (p : Θ → α → ℝ) : Prop :=
  ∀ (θ u : Θ), u ≠ 0 → ∃ x : α, scoreCLM p θ x u ≠ 0

variable [Fintype α]

/-- Finite score Fisher information as a bilinear form on the parameter space. -/
noncomputable def fisherScoreBilin (p : Θ → α → ℝ) (θ : Θ) : LinearMap.BilinForm ℝ Θ := by
  classical
  refine LinearMap.mk₂ ℝ
    (fun u v ↦ ∑ x : α, p θ x * scoreCLM p θ x u * scoreCLM p θ x v) ?_ ?_ ?_ ?_
  · intro u₁ u₂ v
    simp [mul_add, Finset.sum_add_distrib, mul_left_comm, mul_comm]
  · intro c u v
    simp [Finset.mul_sum, mul_left_comm, mul_comm, smul_eq_mul]
  · intro u v₁ v₂
    simp [mul_add, Finset.sum_add_distrib, mul_left_comm, mul_comm]
  · intro c u v
    simp [Finset.mul_sum, mul_left_comm, mul_comm, smul_eq_mul]

/-- Evaluation of the finite Fisher bilinear form is its defining score sum. -/
@[simp] theorem fisherScoreBilin.apply (p : Θ → α → ℝ) (θ u v : Θ) :
    fisherScoreBilin p θ u v = ∑ x : α, p θ x * scoreCLM p θ x u * scoreCLM p θ x v :=
  rfl

/-- The finite Fisher bilinear form is symmetric. -/
theorem fisherScoreBilin_symm (p : Θ → α → ℝ) (θ u v : Θ) :
    fisherScoreBilin p θ u v = fisherScoreBilin p θ v u := by
  classical
  simp [fisherScoreBilin.apply, mul_left_comm, mul_comm]

/-- Positive atoms and one nonzero score give a positive Fisher diagonal value. -/
theorem fisherScoreBilin_pos_of_exists (p : Θ → α → ℝ) (θ u : Θ)
    (hp : ∀ x : α, 0 < p θ x) (hx : ∃ x : α, scoreCLM p θ x u ≠ 0) :
    0 < fisherScoreBilin p θ u u := by
  classical
  obtain ⟨x₀, hx₀⟩ := hx
  have hnonneg (x : α) : 0 ≤ p θ x * scoreCLM p θ x u * scoreCLM p θ x u := by
    simpa only [pow_two, mul_assoc] using mul_nonneg (hp x).le (sq_nonneg (scoreCLM p θ x u))
  have hpos : 0 < p θ x₀ * scoreCLM p θ x₀ u * scoreCLM p θ x₀ u := by
    simpa only [pow_two, mul_assoc] using mul_pos (hp x₀) (sq_pos_of_ne_zero hx₀)
  exact Finset.sum_pos' (fun x _ ↦ hnonneg x) ⟨x₀, Finset.mem_univ _, hpos⟩

end FisherInformation.Fisher
