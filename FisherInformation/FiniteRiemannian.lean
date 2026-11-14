/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import FisherInformation.ScoreFinite
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Smooth finite score Fisher metrics

Positive smooth atoms give a smoothly varying continuous bilinear Fisher form, computed
from the actual log-density score differentials. In finite dimension, score separation
makes the metric unit ball bounded in the existing topology at every parameter.

Normalization is not needed for this construction. For a statistical interpretation,
the atoms must additionally sum to one.

## Main results

- `fisherScoreContinuousBilin_apply`: evaluation equals the finite score Fisher form.
- `contDiff_fisherScoreContinuousBilin`: the continuous bilinear form is smooth.
- `fisherRiemannianMetric`: the actual Fisher form as a smooth tangent-bundle metric.
- `fisherRiemannianMetric_inner`: exact evaluation on every tangent fiber.
-/

@[expose] public section

open scoped BigOperators ContDiff Manifold

namespace FisherInformation.Fisher

variable {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
variable {α : Type*} [Fintype α]

/-- The finite score Fisher form as a continuous bilinear map. -/
noncomputable def fisherScoreContinuousBilin (p : Θ → α → ℝ) (θ : Θ) :
    Θ →L[ℝ] Θ →L[ℝ] ℝ :=
  ∑ x, p θ x • (scoreCLM p θ x).smulRight (scoreCLM p θ x)

/-- The continuous bilinear map evaluates to the finite score Fisher form. -/
@[simp] theorem fisherScoreContinuousBilin_apply (p : Θ → α → ℝ) (θ u v : Θ) :
    fisherScoreContinuousBilin p θ u v = fisherScoreBilin p θ u v := by
  classical
  simp [fisherScoreContinuousBilin, fisherScoreBilin.apply, mul_assoc]

omit [Fintype α] in
/-- Positive smooth atoms have smoothly varying log-density score differentials. -/
theorem contDiff_scoreCLM (p : Θ → α → ℝ)
    (hp : ∀ θ x, 0 < p θ x) (hs : ∀ x, ContDiff ℝ ∞ (fun θ ↦ p θ x)) (x : α) :
    ContDiff ℝ ∞ (fun θ ↦ scoreCLM p θ x) := by
  exact contDiff_infty_iff_fderiv.mp ((hs x).log (fun θ ↦ ne_of_gt (hp θ x))) |>.2

set_option backward.isDefEq.respectTransparency false in
/-- Positive smooth atoms give a smooth continuous bilinear Fisher form. -/
theorem contDiff_fisherScoreContinuousBilin (p : Θ → α → ℝ)
    (hp : ∀ θ x, 0 < p θ x) (hs : ∀ x, ContDiff ℝ ∞ (fun θ ↦ p θ x)) :
    ContDiff ℝ ∞ (fisherScoreContinuousBilin p) := by
  classical
  let : IsBoundedSMul ℝ (Θ →L[ℝ] Θ →L[ℝ] ℝ) :=
    IsBoundedSMul.of_norm_smul_le fun r f ↦ ContinuousLinearMap.opNorm_smul_le r f
  apply ContDiff.sum
  intro x _
  exact (hs x).smul ((contDiff_scoreCLM p hp hs x).smulRight
    (contDiff_scoreCLM p hp hs x))

private theorem isVonNBounded_bilinear_unitBall [FiniteDimensional ℝ Θ]
    (B : Θ →L[ℝ] Θ →L[ℝ] ℝ) (hpos : ∀ v, v ≠ 0 → 0 < B v v) :
    Bornology.IsVonNBounded ℝ {v : Θ | B v v < 1} := by
  have hcont : Continuous (fun v ↦ B v v) := B.continuous.clm_apply continuous_id
  obtain ⟨δ, hδ, hδB⟩ := (isCompact_sphere (0 : Θ) 1).exists_forall_le'
    hcont.continuousOn (fun v hv ↦ hpos v (by rintro rfl; simp at hv))
  have hscale (a : ℝ) (v : Θ) : B (a • v) (a • v) = a ^ 2 * B v v := by
    simp [smul_eq_mul, pow_two, mul_assoc]
  have hlower (v : Θ) (hv : v ≠ 0) : δ * ‖v‖ ^ 2 ≤ B v v := by
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hu : ‖‖v‖⁻¹ • v‖ = 1 := by simp [norm_smul, hn]
    have hunit : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : Θ) 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hu
    have h := mul_le_mul_of_nonneg_right (hδB _ hunit) (sq_nonneg ‖v‖)
    rw [hscale] at h
    have hcancel : (‖v‖⁻¹ ^ 2 * B v v) * ‖v‖ ^ 2 = B v v := by
      field_simp [hn]
    rwa [hcancel] at h
  refine (NormedSpace.isVonNBounded_iff' ℝ).2 ⟨1 + δ⁻¹, fun v hv ↦ ?_⟩
  have hi : 0 < δ⁻¹ := inv_pos.mpr hδ
  by_cases hz : v = 0
  · simpa only [hz, norm_zero] using (add_pos zero_lt_one hi).le
  by_cases hn : ‖v‖ ≤ 1
  · exact hn.trans (by linarith)
  have hn2 : ‖v‖ ≤ ‖v‖ ^ 2 := by nlinarith
  have hbound : δ * ‖v‖ < 1 :=
    (mul_le_mul_of_nonneg_left hn2 hδ.le).trans_lt ((hlower v hz).trans_lt hv)
  have hdiv : ‖v‖ < 1 / δ :=
    (lt_div_iff₀ hδ).2 (by simpa only [mul_comm] using hbound)
  exact hdiv.le.trans (by simp only [one_div]; linarith)

variable [FiniteDimensional ℝ Θ]

set_option backward.isDefEq.respectTransparency false in
/-- The finite Fisher form defines a smooth metric when scores separate directions. -/
noncomputable def fisherRiemannianMetric (p : Θ → α → ℝ)
    (hp : ∀ θ x, 0 < p θ x) (hs : ∀ x, ContDiff ℝ ∞ (fun θ ↦ p θ x))
    (hsep : ScoreSeparating p) :
    Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, Θ) ∞ Θ
      (fun θ : Θ ↦ TangentSpace 𝓘(ℝ, Θ) θ) where
  inner θ := (fisherScoreContinuousBilin p θ : Θ →L[ℝ] Θ →L[ℝ] ℝ)
  symm θ u v := by
    change fisherScoreContinuousBilin p θ (u : Θ) (v : Θ) =
      fisherScoreContinuousBilin p θ (v : Θ) (u : Θ)
    rw [fisherScoreContinuousBilin_apply, fisherScoreContinuousBilin_apply]
    exact fisherScoreBilin_symm p θ u v
  pos θ v hv := by
    change 0 < fisherScoreContinuousBilin p θ (v : Θ) (v : Θ)
    rw [fisherScoreContinuousBilin_apply]
    exact fisherScoreBilin_pos_of_exists p θ v (hp θ) (hsep θ v hv)
  isVonNBounded θ := by
    exact isVonNBounded_bilinear_unitBall (Θ := Θ)
      (fisherScoreContinuousBilin p θ) fun v hv ↦ by
      simpa only [fisherScoreContinuousBilin_apply] using
        fisherScoreBilin_pos_of_exists p θ v (hp θ) (hsep θ v hv)
  contMDiff := by
    intro θ
    rw [Bundle.contMDiffAt_section]
    convert! (contDiff_fisherScoreContinuousBilin p hp hs).contDiffAt.contMDiffAt using 1
    ext η u v
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, TangentSpace]

set_option backward.isDefEq.respectTransparency false in
/-- Every tangent pairing is exactly the original log-density score Fisher form. -/
@[simp] theorem fisherRiemannianMetric_inner (p : Θ → α → ℝ)
    (hp : ∀ θ x, 0 < p θ x) (hs : ∀ x, ContDiff ℝ ∞ (fun θ ↦ p θ x))
    (hsep : ScoreSeparating p) (θ u v : Θ) :
    (fisherRiemannianMetric p hp hs hsep).inner θ u v = fisherScoreBilin p θ u v :=
  fisherScoreContinuousBilin_apply p θ u v

end FisherInformation.Fisher
