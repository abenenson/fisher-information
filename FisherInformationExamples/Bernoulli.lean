/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import FisherInformation
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Tactic.NormNum

/-!
# Logistic Bernoulli family

The success probability is `exp θ / (1 + exp θ)`. Every parameter gives a positive normalized
law. Its Fisher information at zero is `1/4`, proved both as KL curvature and as an integral
score. A separate consumer identifies the real KL integral with Mathlib's measure KL.
-/

@[expose] public section

namespace FisherInformation.Examples

open MeasureTheory
open scoped BigOperators ENNReal

/-- A globally positive Bernoulli family in its real-valued log-odds parameter. -/
noncomputable def bernoulli (θ : ℝ) : Bool → ℝ
  | false => 1 / (1 + Real.exp θ)
  | true => Real.exp θ / (1 + Real.exp θ)

private lemma denominator_pos (θ : ℝ) : 0 < 1 + Real.exp θ :=
  add_pos zero_lt_one (Real.exp_pos θ)

/-- Both outcomes have positive probability for every finite log-odds parameter. -/
theorem bernoulli_pos (θ : ℝ) (b : Bool) : 0 < bernoulli θ b := by
  cases b
  · exact div_pos zero_lt_one (denominator_pos θ)
  · exact div_pos (Real.exp_pos θ) (denominator_pos θ)

/-- The two Bernoulli coordinates sum to one at every parameter. -/
theorem bernoulli_sum (θ : ℝ) : ∑ b : Bool, bernoulli θ b = 1 := by
  simp only [Fintype.sum_bool, bernoulli]
  rw [← add_div]
  simpa only [add_comm] using div_self (denominator_pos θ).ne'

private lemma bernoulli_false_hasDerivAt (θ : ℝ) :
    HasDerivAt (fun t ↦ bernoulli t false)
      (-Real.exp θ / (1 + Real.exp θ) ^ 2) θ := by
  simpa [bernoulli, Pi.div_def, Pi.add_def] using
    (hasDerivAt_const θ (1 : ℝ)).div
      ((hasDerivAt_const θ (1 : ℝ)).add (Real.hasDerivAt_exp θ))
      (denominator_pos θ).ne'

private lemma bernoulli_true_hasDerivAt (θ : ℝ) :
    HasDerivAt (fun t ↦ bernoulli t true)
      (Real.exp θ / (1 + Real.exp θ) ^ 2) θ := by
  have h := (Real.hasDerivAt_exp θ).div
    ((hasDerivAt_const θ (1 : ℝ)).add (Real.hasDerivAt_exp θ))
    (denominator_pos θ).ne'
  have hnum : Real.exp θ * (1 + Real.exp θ) - Real.exp θ * Real.exp θ = Real.exp θ := by
    ring
  simpa only [bernoulli, Pi.div_def, Pi.add_def, zero_add, hnum] using h

private lemma bernoulli_differentiable (b : Bool) :
    Differentiable ℝ (fun θ ↦ bernoulli θ b) := by
  cases b
  · exact fun θ ↦ (bernoulli_false_hasDerivAt θ).differentiableAt
  · exact fun θ ↦ (bernoulli_true_hasDerivAt θ).differentiableAt

private lemma bernoulli_deriv_differentiable (b : Bool) :
    Differentiable ℝ (fun θ ↦ deriv (fun t ↦ bernoulli t b) θ) := by
  cases b
  · have h : (fun θ ↦ deriv (fun t ↦ bernoulli t false) θ) =
        fun θ ↦ -Real.exp θ / (1 + Real.exp θ) ^ 2 :=
      funext fun θ ↦ (bernoulli_false_hasDerivAt θ).deriv
    rw [h]
    exact Real.differentiable_exp.neg.div
      (((differentiable_const (1 : ℝ)).add Real.differentiable_exp).pow 2)
      (fun θ ↦ pow_ne_zero _ (denominator_pos θ).ne')
  · have h : (fun θ ↦ deriv (fun t ↦ bernoulli t true) θ) =
        fun θ ↦ Real.exp θ / (1 + Real.exp θ) ^ 2 :=
      funext fun θ ↦ (bernoulli_true_hasDerivAt θ).deriv
    rw [h]
    exact Real.differentiable_exp.div
      (((differentiable_const (1 : ℝ)).add Real.differentiable_exp).pow 2)
      (fun θ ↦ pow_ne_zero _ (denominator_pos θ).ne')

/-- The nonzero score at the fair member gives Fisher information `1/4`. -/
theorem bernoulli_fisherScore_zero : fisherScore bernoulli 0 = 1 / 4 := by
  simp only [fisherScore, Fintype.sum_bool]
  rw [(bernoulli_false_hasDerivAt 0).deriv, (bernoulli_true_hasDerivAt 0).deriv]
  norm_num [bernoulli]

/-- The general finite identity applies with all regularity hypotheses discharged. -/
theorem bernoulli_fisherKL_zero : fisherKL bernoulli 0 = 1 / 4 := by
  rw [fisherKL_eq_fisherScore bernoulli 0
    (fun θ b ↦ (bernoulli_pos θ b).ne') bernoulli_sum
    bernoulli_differentiable bernoulli_deriv_differentiable]
  exact bernoulli_fisherScore_zero

/-- Counting-measure score Fisher agrees with the finite sum and has the same nonzero value. -/
theorem bernoulli_fisherScoreIntegral_zero :
    fisherScoreIntegral (Measure.count : Measure Bool) bernoulli 0 = 1 / 4 := by
  simpa [fisherScoreIntegral, fisherScore, integral_count] using bernoulli_fisherScore_zero

/-- The integral KL expression for this family is exactly its finite-sum expression. -/
theorem bernoulli_counting_kl (θ θ' : ℝ) :
    klIntegralRealParam (Measure.count : Measure Bool) bernoulli θ θ' =
      klFiniteRealParam bernoulli θ θ' :=
  (klFiniteRealParam_eq_klIntegralRealParam_count bernoulli θ θ').symm

/-- The counting-measure KL Hessian also has Fisher value `1/4`. -/
theorem bernoulli_fisherKLIntegral_zero :
    fisherKLIntegral (Measure.count : Measure Bool) bernoulli 0 = 1 / 4 := by
  have h : (fun t ↦ klIntegralRealParam (Measure.count : Measure Bool) bernoulli 0 t) =
      fun t ↦ klFiniteRealParam bernoulli 0 t :=
    funext fun t ↦ bernoulli_counting_kl 0 t
  simpa only [fisherKLIntegral, fisherKL, h] using bernoulli_fisherKL_zero

private lemma counting_integrable (f : Bool → ℝ) :
    Integrable f (Measure.count : Measure Bool) :=
  integrable_count_iff.mpr (hasSum_fintype _).summable

/-- The density-to-measure bridge applies to two arbitrary members of this positive family. -/
theorem bernoulli_measure_kl (θ θ' : ℝ) :
    klIntegralRealParam (Measure.count : Measure Bool) bernoulli θ θ' =
      (InformationTheory.klDiv
        ((Measure.count : Measure Bool).withDensity fun b ↦ ENNReal.ofReal (bernoulli θ b))
        ((Measure.count : Measure Bool).withDensity
          fun b ↦ ENNReal.ofReal (bernoulli θ' b))).toReal := by
  apply klIntegralRealParam_eq_toReal_klDiv_withDensity_of_integral_eq
  · exact Filter.Eventually.of_forall fun b ↦ (bernoulli_pos θ b).le
  · exact Filter.Eventually.of_forall fun b ↦ (bernoulli_pos θ' b).le
  · exact Filter.Eventually.of_forall fun b ↦ (bernoulli_pos θ' b).ne'
  · exact counting_integrable _
  · exact counting_integrable _
  · exact counting_integrable _
  · simp only [integral_count, bernoulli_sum]
  · exact (withDensity_absolutelyContinuous _ _).trans
      (withDensity_absolutelyContinuous'
        (measurable_of_countable _).aemeasurable
        (Filter.Eventually.of_forall fun b ↦
          (ENNReal.ofReal_pos.mpr (bernoulli_pos θ' b)).ne'))

end FisherInformation.Examples
