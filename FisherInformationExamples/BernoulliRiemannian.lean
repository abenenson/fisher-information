/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import FisherInformationExamples.Bernoulli
public import FisherInformation.FiniteRiemannian

/-!
# The Fisher metric of the logistic Bernoulli family

The existing Bernoulli family is positive and normalized for every real log-odds parameter.
Here its atoms are proved smooth, its scores are computed in every direction, and a nonzero
score establishes separation. The resulting smooth tangent metric pairs `u` and `v` at the
fair member as `u * v / 4`.
-/

@[expose] public section

namespace FisherInformation.Examples

open FisherInformation.Fisher
open scoped ContDiff Manifold

private lemma bernoulli_denominator_pos (θ : ℝ) : 0 < 1 + Real.exp θ :=
  add_pos zero_lt_one (Real.exp_pos θ)

/-- Both Bernoulli atoms are smooth throughout the real log-odds parameter line. -/
theorem bernoulli_contDiff (b : Bool) : ContDiff ℝ ∞ (fun θ ↦ bernoulli θ b) := by
  cases b
  · exact contDiff_const.div (contDiff_const.add Real.contDiff_exp)
      (fun θ ↦ (bernoulli_denominator_pos θ).ne')
  · exact Real.contDiff_exp.div (contDiff_const.add Real.contDiff_exp)
      (fun θ ↦ (bernoulli_denominator_pos θ).ne')

private lemma bernoulli_false_hasDerivAt (θ : ℝ) :
    HasDerivAt (fun t ↦ bernoulli t false)
      (-Real.exp θ / (1 + Real.exp θ) ^ 2) θ := by
  simpa [bernoulli, Pi.div_def, Pi.add_def] using
    (hasDerivAt_const θ (1 : ℝ)).div
      ((hasDerivAt_const θ (1 : ℝ)).add (Real.hasDerivAt_exp θ))
      (bernoulli_denominator_pos θ).ne'

private lemma bernoulli_true_hasDerivAt (θ : ℝ) :
    HasDerivAt (fun t ↦ bernoulli t true)
      (Real.exp θ / (1 + Real.exp θ) ^ 2) θ := by
  have h := (Real.hasDerivAt_exp θ).div
    ((hasDerivAt_const θ (1 : ℝ)).add (Real.hasDerivAt_exp θ))
    (bernoulli_denominator_pos θ).ne'
  have hnum : Real.exp θ * (1 + Real.exp θ) - Real.exp θ * Real.exp θ = Real.exp θ := by
    ring
  simpa only [bernoulli, Pi.div_def, Pi.add_def, zero_add, hnum] using h

/-- The false-outcome score is nonzero in every nonzero parameter direction. -/
theorem bernoulli_scoreCLM_false (θ u : ℝ) :
    scoreCLM bernoulli θ false u = (-Real.exp θ / (1 + Real.exp θ)) * u := by
  rw [scoreCLM, fderiv_eq_deriv_mul,
    ((bernoulli_false_hasDerivAt θ).log (bernoulli_pos θ false).ne').deriv]
  dsimp only [bernoulli]
  field_simp [(bernoulli_denominator_pos θ).ne']

/-- The true-outcome score is the complementary Bernoulli probability times the direction. -/
theorem bernoulli_scoreCLM_true (θ u : ℝ) :
    scoreCLM bernoulli θ true u = (1 / (1 + Real.exp θ)) * u := by
  rw [scoreCLM, fderiv_eq_deriv_mul,
    ((bernoulli_true_hasDerivAt θ).log (bernoulli_pos θ true).ne').deriv]
  dsimp only [bernoulli]
  field_simp [(bernoulli_denominator_pos θ).ne', (Real.exp_pos θ).ne']

/-- The computed Bernoulli scores separate directions at every log-odds parameter. -/
theorem bernoulli_scoreSeparating : ScoreSeparating bernoulli := by
  intro θ u hu
  refine ⟨false, ?_⟩
  rw [bernoulli_scoreCLM_false]
  exact mul_ne_zero (div_ne_zero (neg_ne_zero.mpr (Real.exp_pos θ).ne')
    (bernoulli_denominator_pos θ).ne') hu

/-- The positive normalized logistic Bernoulli family has its actual smooth Fisher metric. -/
noncomputable def bernoulliRiemannianMetric :
    Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, ℝ) ∞ ℝ
      (fun θ : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) θ) :=
  fisherRiemannianMetric bernoulli bernoulli_pos bernoulli_contDiff bernoulli_scoreSeparating

/-- At the fair Bernoulli law, the Fisher tangent pairing is `u * v / 4`. -/
theorem bernoulliRiemannianMetric_inner_zero (u v : ℝ) :
    bernoulliRiemannianMetric.inner 0 u v = u * v / 4 := by
  change fisherScoreContinuousBilin bernoulli 0 u v = _
  rw [fisherScoreContinuousBilin_apply]
  simp only [fisherScoreBilin.apply, Fintype.sum_bool,
    bernoulli_scoreCLM_false, bernoulli_scoreCLM_true]
  norm_num [bernoulli]
  ring

end FisherInformation.Examples
