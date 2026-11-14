/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import FisherInformation.Categorical

/-!
# The Fisher metric of a finite categorical family

Baseline logits give a positive, normalized, smooth family whose actual log-density
scores separate parameter directions. The general finite score constructor therefore
supplies a smooth Riemannian metric. With two free logits, this is a metric on a
two-dimensional parameter space for a three-outcome categorical law.
-/

@[expose] public section

namespace FisherInformation.Examples

open FisherInformation.Fisher
open scoped ContDiff Manifold

variable {α : Type*} [Fintype α]

/-- The smooth Fisher metric of the positive normalized categorical family. -/
noncomputable def categoricalRiemannianMetric :
    Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, α → ℝ) ∞ (α → ℝ)
      (fun θ : α → ℝ ↦ TangentSpace 𝓘(ℝ, α → ℝ) θ) :=
  fisherRiemannianMetric categorical categorical_pos categorical_contDiff
    categorical_scoreSeparating

/-- Its tangent pairing is the actual log-density score Fisher form. -/
theorem categoricalRiemannianMetric_inner (θ u v : α → ℝ) :
    (categoricalRiemannianMetric (α := α)).inner θ u v =
      fisherScoreBilin categorical θ u v :=
  fisherRiemannianMetric_inner categorical categorical_pos categorical_contDiff
    categorical_scoreSeparating θ u v

private theorem categoricalPartition_hasFDerivAt_zero :
    HasFDerivAt (categoricalPartition (α := Fin 2))
      (((ContinuousLinearMap.proj (0 : Fin 2)) : (Fin 2 → ℝ) →L[ℝ] ℝ) +
        ((ContinuousLinearMap.proj (1 : Fin 2)) : (Fin 2 → ℝ) →L[ℝ] ℝ))
      (0 : Fin 2 → ℝ) := by
  have h0 : HasFDerivAt (fun θ : Fin 2 → ℝ ↦ Real.exp (θ 0))
      ((ContinuousLinearMap.proj (0 : Fin 2)) : (Fin 2 → ℝ) →L[ℝ] ℝ)
      (0 : Fin 2 → ℝ) := by
    simpa using ((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) (0 : Fin 2 → ℝ)).exp)
  have h1 : HasFDerivAt (fun θ : Fin 2 → ℝ ↦ Real.exp (θ 1))
      ((ContinuousLinearMap.proj (1 : Fin 2)) : (Fin 2 → ℝ) →L[ℝ] ℝ)
      (0 : Fin 2 → ℝ) := by
    simpa using ((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) (0 : Fin 2 → ℝ)).exp)
  have h := (hasFDerivAt_const (1 : ℝ) (0 : Fin 2 → ℝ)).add (h0.add h1)
  have heq : (categoricalPartition (α := Fin 2)) =
      (fun θ : Fin 2 → ℝ ↦ 1 + (Real.exp (θ 0) + Real.exp (θ 1))) := by
    funext θ
    simp [categoricalPartition, Fin.sum_univ_two]
  rw [heq]
  simpa only [Pi.add_def, zero_add] using h

private theorem categorical_score_none_zero (u : Fin 2 → ℝ) :
    scoreCLM categorical 0 none u = -(u 0 + u 1) / 3 := by
  have hZ := categoricalPartition_hasFDerivAt_zero
  have hlog := hZ.log (by norm_num [categoricalPartition, Fin.sum_univ_two])
  have heq : (fun θ : Fin 2 → ℝ ↦ Real.log (categorical θ none)) =
      (fun θ ↦ -Real.log (categoricalPartition θ)) :=
    funext categorical_log_none
  rw [scoreCLM, heq, fderiv_fun_neg, hlog.fderiv]
  simp only [neg_apply, smul_apply, add_apply, ContinuousLinearMap.proj_apply]
  norm_num [categoricalPartition, Fin.sum_univ_two]
  ring

private theorem categorical_score_some_zero (u : Fin 2 → ℝ) (i : Fin 2) :
    scoreCLM categorical 0 (some i) u = u i - (u 0 + u 1) / 3 := by
  have h := categorical_score_contrast (0 : Fin 2 → ℝ) u i
  rw [categorical_score_none_zero] at h
  linarith

/-- At the uniform three-outcome law, the two-logit Fisher pairing is the covariance
of the two directions under the three equal outcome weights. -/
theorem categorical_fin2_inner_zero (u v : Fin 2 → ℝ) :
    (categoricalRiemannianMetric (α := Fin 2)).inner 0 u v =
      (u 0 * v 0 + u 1 * v 1) / 3 -
        (u 0 + u 1) * (v 0 + v 1) / 9 := by
  rw [categoricalRiemannianMetric_inner]
  simp only [fisherScoreBilin.apply, Fintype.sum_option, Fin.sum_univ_two]
  rw [categorical_score_none_zero u, categorical_score_none_zero v,
    categorical_score_some_zero u 0, categorical_score_some_zero v 0,
    categorical_score_some_zero u 1, categorical_score_some_zero v 1]
  norm_num [categorical, categoricalPartition, Fin.sum_univ_two]
  ring

/-- The three-outcome categorical family has a positive Fisher norm on every nonzero
direction in its two-dimensional logit parameter space. -/
theorem categorical_fin2_inner_pos (θ u : Fin 2 → ℝ) (hu : u ≠ 0) :
    0 < (categoricalRiemannianMetric (α := Fin 2)).inner θ u u := by
  rw [categoricalRiemannianMetric_inner]
  exact fisherScoreBilin_pos_of_exists categorical θ u (categorical_pos θ)
    (categorical_scoreSeparating θ u hu)

end FisherInformation.Examples
