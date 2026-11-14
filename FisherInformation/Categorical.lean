/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import FisherInformation.FiniteRiemannian
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fintype.Option

/-!
# Finite categorical laws in baseline logit coordinates

An additional outcome has fixed logit zero. Thus each parameter in `α → ℝ` specifies a
positive normalized law on `Option α`, without a redundant common logit direction.
The construction also works when `α` is empty: then the parameter space is trivial and
the baseline outcome has probability one.

The contrast between the log density of `some i` and that of `none` is exactly the
coordinate logit `θ i`. Its differential proves that the actual log-density scores
separate every nonzero parameter direction.
-/

@[expose] public section

open scoped BigOperators ContDiff

namespace FisherInformation.Fisher

variable {α : Type*} [Fintype α]

/-- The partition function for categorical logits with a fixed baseline outcome. -/
noncomputable def categoricalPartition (θ : α → ℝ) : ℝ :=
  1 + ∑ i, Real.exp (θ i)

/-- A categorical law on `Option α`, with `none` as the baseline outcome. -/
noncomputable def categorical (θ : α → ℝ) : Option α → ℝ
  | none => 1 / categoricalPartition θ
  | some i => Real.exp (θ i) / categoricalPartition θ

/-- The partition function is positive, including when `α` is empty. -/
theorem categoricalPartition_pos (θ : α → ℝ) : 0 < categoricalPartition θ := by
  have h : 0 ≤ ∑ i, Real.exp (θ i) :=
    Finset.sum_nonneg fun i _ ↦ (Real.exp_pos (θ i)).le
  exact add_pos_of_pos_of_nonneg zero_lt_one h

/-- Every atom of the categorical law is positive. -/
theorem categorical_pos (θ : α → ℝ) (x : Option α) : 0 < categorical θ x := by
  cases x with
  | none => exact div_pos zero_lt_one (categoricalPartition_pos θ)
  | some i => exact div_pos (Real.exp_pos (θ i)) (categoricalPartition_pos θ)

/-- The categorical probabilities sum to one. -/
theorem categorical_sum (θ : α → ℝ) : ∑ x, categorical θ x = 1 := by
  classical
  rw [Fintype.sum_option]
  simp only [categorical, ← Finset.sum_div, ← add_div]
  exact div_self (ne_of_gt (categoricalPartition_pos θ))

/-- With no free logits, the only parameter is zero. -/
theorem categorical_fin0_parameter (θ : Fin 0 → ℝ) : θ = 0 :=
  Subsingleton.elim _ _

/-- With no free logits, the baseline is the only outcome and has probability one. -/
theorem categorical_fin0_baseline (θ : Fin 0 → ℝ) : categorical θ none = 1 := by
  simp [categorical, categoricalPartition]

/-- The partition function is smooth on the whole parameter space. -/
theorem categoricalPartition_contDiff :
    ContDiff ℝ ∞ (categoricalPartition (α := α)) := by
  apply contDiff_const.add
  exact ContDiff.sum fun i _ ↦
    (show ContDiff ℝ ∞ (fun θ : α → ℝ ↦ θ i) from
      contDiff_apply (n := ∞) ℝ (fun _ : α ↦ ℝ) i).exp

/-- Every categorical probability is smooth on the whole parameter space. -/
theorem categorical_contDiff (x : Option α) :
    ContDiff ℝ ∞ (fun θ : α → ℝ ↦ categorical θ x) := by
  have hZ := categoricalPartition_contDiff (α := α)
  have hne : ∀ θ : α → ℝ, categoricalPartition θ ≠ 0 :=
    fun θ ↦ ne_of_gt (categoricalPartition_pos θ)
  cases x with
  | none => exact contDiff_const.div hZ hne
  | some i =>
      exact (show ContDiff ℝ ∞ (fun θ : α → ℝ ↦ θ i) from
        contDiff_apply (n := ∞) ℝ (fun _ : α ↦ ℝ) i).exp.div hZ hne

/-- The baseline log density is minus the log partition function. -/
theorem categorical_log_none (θ : α → ℝ) :
    Real.log (categorical θ none) = -Real.log (categoricalPartition θ) := by
  rw [categorical, Real.log_div one_ne_zero
    (ne_of_gt (categoricalPartition_pos θ)), Real.log_one, zero_sub]

/-- A nonbaseline log density is its logit minus the log partition function. -/
theorem categorical_log_some (θ : α → ℝ) (i : α) :
    Real.log (categorical θ (some i)) = θ i - Real.log (categoricalPartition θ) := by
  rw [categorical, Real.log_div (ne_of_gt (Real.exp_pos (θ i)))
    (ne_of_gt (categoricalPartition_pos θ)), Real.log_exp]

/-- A log-density contrast recovers one coordinate of the parameter. -/
theorem categorical_log_contrast (θ : α → ℝ) (i : α) :
    Real.log (categorical θ (some i)) - Real.log (categorical θ none) = θ i := by
  rw [categorical_log_some, categorical_log_none]
  ring

/-- The baseline logit parameterization is identifiable. -/
theorem categorical_injective : Function.Injective (categorical (α := α)) := by
  intro θ η h
  funext i
  have hi := congrArg
    (fun p : Option α → ℝ ↦ Real.log (p (some i)) - Real.log (p none)) h
  simpa only [categorical_log_contrast] using hi

/-- A score contrast is the differential of the corresponding logit coordinate. -/
theorem categorical_score_contrast (θ u : α → ℝ) (i : α) :
    scoreCLM categorical θ (some i) u - scoreCLM categorical θ none u = u i := by
  have hZ : DifferentiableAt ℝ categoricalPartition θ :=
    ((categoricalPartition_contDiff (α := α)).contDiffAt).differentiableAt (by simp)
  have hlogZ := hZ.log (ne_of_gt (categoricalPartition_pos θ))
  have hsome : (fun t : α → ℝ ↦ Real.log (categorical t (some i))) =
      (fun t ↦ t i - Real.log (categoricalPartition t)) :=
    funext fun t ↦ categorical_log_some t i
  have hnone : (fun t : α → ℝ ↦ Real.log (categorical t none)) =
      (fun t ↦ -Real.log (categoricalPartition t)) :=
    funext fun t ↦ categorical_log_none t
  simp only [scoreCLM, hsome, hnone,
    fderiv_fun_sub (hasFDerivAt_apply i θ).differentiableAt hlogZ,
    fderiv_fun_neg, (hasFDerivAt_apply i θ).fderiv, sub_apply, neg_apply]
  simp

/-- The categorical scores detect every nonzero direction. For empty `α`, there are
no nonzero directions in the parameter space `α → ℝ`. -/
theorem categorical_scoreSeparating : ScoreSeparating (categorical (α := α)) := by
  intro θ u hu
  by_contra h
  have hz : ∀ x, scoreCLM (categorical (α := α)) θ x u = 0 := by
    simpa only [not_exists, not_not] using h
  apply hu
  funext i
  have hi := categorical_score_contrast θ u i
  simpa [hz] using hi.symm

end FisherInformation.Fisher
