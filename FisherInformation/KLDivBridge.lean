/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import FisherInformation.KLIntegral

/-!
# FisherInformation.KLDivBridge

Bridge between the real-valued density formula `∫ p * log(p/q)` and Mathlib's
`InformationTheory.klDiv` API.

This file is intended as an adapter layer: `FisherInformation.KLIntegral` develops a
real-valued `∫ p log(p/q)` KL formula and its differentiability lemmas, while Mathlib’s
`InformationTheory.klDiv` is formulated for measures and takes values in `ℝ≥0∞`.

## Main results

* `klIntegralReal_eq_toReal_klDiv_withDensity_of_integral_eq` : for nonnegative densities `p,q`
  with equal total mass, `klIntegralReal p q = (klDiv μp μq).toReal` where
  `μp = μ.withDensity (ofReal ∘ p)` and `μq = μ.withDensity (ofReal ∘ q)`.
-/

@[expose] public section

open TopologicalSpace MeasureTheory Filter Metric

open scoped ENNReal

namespace FisherInformation

noncomputable section

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- Under the supplied nonnegativity, integrability, equal-mass and absolute-continuity
assumptions, with the reference density nonzero almost everywhere, the real density KL formula
equals the measure KL divergence after `toReal`. -/
lemma klIntegralReal_eq_toReal_klDiv_withDensity_of_integral_eq
    [SigmaFinite μ]
    (p q : α → ℝ)
    (hp_nonneg : ∀ᵐ x ∂μ, 0 ≤ p x)
    (hq_nonneg : ∀ᵐ x ∂μ, 0 ≤ q x)
    (hq0 : ∀ᵐ x ∂μ, q x ≠ 0)
    (hp_int : Integrable p μ)
    (hq_int : Integrable q μ)
    (hkl_int : Integrable (fun x ↦ p x * Real.log (p x / q x)) μ)
    (h_eq : (∫ x, p x ∂μ) = ∫ x, q x ∂μ)
    (hAC :
      (μ.withDensity fun x ↦ ENNReal.ofReal (p x)) ≪
        (μ.withDensity fun x ↦ ENNReal.ofReal (q x))) :
    klIntegralReal (μ := μ) p q =
      (InformationTheory.klDiv
          (μ.withDensity fun x ↦ ENNReal.ofReal (p x))
          (μ.withDensity fun x ↦ ENNReal.ofReal (q x))).toReal := by
  classical
  -- Abbreviate the measures induced by the densities.
  let μp : Measure α := μ.withDensity fun x ↦ ENNReal.ofReal (p x)
  let μq : Measure α := μ.withDensity fun x ↦ ENNReal.ofReal (q x)
  -- Finiteness of `μp`/`μq` from integrability of densities.
  have hμp_fin : IsFiniteMeasure μp :=
    MeasureTheory.isFiniteMeasure_withDensity_ofReal (μ := μ) (f := p) (hp_int.hasFiniteIntegral)
  have hμq_fin : IsFiniteMeasure μq :=
    MeasureTheory.isFiniteMeasure_withDensity_ofReal (μ := μ) (f := q) (hq_int.hasFiniteIntegral)
  -- Work in a context where these instances are available.
  classical
  let : IsFiniteMeasure μp := hμp_fin
  let : IsFiniteMeasure μq := hμq_fin
  -- Rewrite `klIntegralReal` using Mathlib's `klFun` integrand, integrated against `μ`.
  have hKL :
      klIntegralReal (μ := μ) p q =
        ∫ x, q x * InformationTheory.klFun (p x / q x) ∂μ :=
    klIntegralReal_eq_integral_klFun_of_integral_eq (μ := μ) p q hq0 hp_int hq_int hkl_int h_eq
  -- Express `toReal (klDiv μp μq)` as an integral of `klFun` of the RN derivative against `μq`.
  have hDiv :
      (InformationTheory.klDiv μp μq).toReal =
        ∫ x, InformationTheory.klFun (μp.rnDeriv μq x).toReal ∂μq :=
    InformationTheory.toReal_klDiv_eq_integral_klFun (μ := μp) (ν := μq) hAC
  -- Compute `(μp.rnDeriv μq)` as a density ratio `p/q`.
  have hqE_ne_zero : ∀ᵐ x ∂μ, ENNReal.ofReal (q x) ≠ (0 : ℝ≥0∞) := by
    filter_upwards [hq_nonneg, hq0] with x hx0 hx_ne0
    have hq_pos : 0 < q x := lt_of_le_of_ne hx0 (Ne.symm hx_ne0)
    exact (ne_of_gt ((ENNReal.ofReal_pos).2 hq_pos))
  have hrnDeriv :
      μp.rnDeriv μq =ᵐ[μq] fun x ↦ ENNReal.ofReal (p x) * (ENNReal.ofReal (q x))⁻¹ := by
    have hpE_meas : AEMeasurable (fun x ↦ ENNReal.ofReal (p x)) μ :=
      (hp_int.aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    have hqE_meas : AEMeasurable (fun x ↦ ENNReal.ofReal (q x)) μ :=
      (hq_int.aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    have hpE_ne_top : ∀ᵐ x ∂μ, ENNReal.ofReal (p x) ≠ (⊤ : ℝ≥0∞) := by
      exact ae_of_all _ fun _x ↦ ENNReal.ofReal_ne_top
    have hqE_ne_top : ∀ᵐ x ∂μ, ENNReal.ofReal (q x) ≠ (⊤ : ℝ≥0∞) := by
      exact ae_of_all _ fun _x ↦ ENNReal.ofReal_ne_top
    have hpE_meas_μq : AEMeasurable (fun x ↦ ENNReal.ofReal (p x)) μq :=
      hpE_meas.mono_ac (withDensity_absolutelyContinuous μ fun x ↦ ENNReal.ofReal (q x))
    have h_left :
        μp.rnDeriv μq =ᵐ[μq] fun x ↦ ENNReal.ofReal (p x) * μ.rnDeriv μq x := by
      simpa [μp, μq] using
        (Measure.rnDeriv_withDensity_left (μ := μ) (ν := μq)
          (f := fun x ↦ ENNReal.ofReal (p x)) hpE_meas_μq hpE_ne_top)
    have h_right0 :
        μ.rnDeriv μq =ᵐ[μ] fun x ↦ (ENNReal.ofReal (q x))⁻¹ * μ.rnDeriv μ x := by
      simpa [μq] using
        (Measure.rnDeriv_withDensity_right (μ := μ) (ν := μ)
          (f := fun x ↦ ENNReal.ofReal (q x)) hqE_meas hqE_ne_zero hqE_ne_top)
    have h_self : μ.rnDeriv μ =ᵐ[μ] (1 : α → ℝ≥0∞) := by
      simpa only [Pi.one_def] using μ.rnDeriv_self
    have h_right : μ.rnDeriv μq =ᵐ[μ] fun x ↦ (ENNReal.ofReal (q x))⁻¹ := by
      have :
          (fun x ↦ (ENNReal.ofReal (q x))⁻¹ * μ.rnDeriv μ x) =ᵐ[μ]
            fun x ↦ (ENNReal.ofReal (q x))⁻¹ := by
        filter_upwards [h_self] with x hx
        simp [hx]
      exact h_right0.trans this
    have h_right' : μ.rnDeriv μq =ᵐ[μq] fun x ↦ (ENNReal.ofReal (q x))⁻¹ :=
      (withDensity_absolutelyContinuous μ fun x ↦ ENNReal.ofReal (q x)) h_right
    have :
        (fun x ↦ ENNReal.ofReal (p x) * μ.rnDeriv μq x) =ᵐ[μq]
          fun x ↦ ENNReal.ofReal (p x) * (ENNReal.ofReal (q x))⁻¹ := by
      filter_upwards [h_right'] with x hx
      simp [hx]
    exact h_left.trans this
  have hrnDeriv_toReal :
      (fun x ↦ (μp.rnDeriv μq x).toReal) =ᵐ[μq] fun x ↦ p x / q x := by
    -- Rewrite using `hrnDeriv`, then use positivity to simplify `toReal`.
    have hμq_ac : μq ≪ μ := withDensity_absolutelyContinuous μ fun x ↦ ENNReal.ofReal (q x)
    have hp_nonneg_μq : ∀ᵐ x ∂μq, 0 ≤ p x := hμq_ac hp_nonneg
    have hq_nonneg_μq : ∀ᵐ x ∂μq, 0 ≤ q x := hμq_ac hq_nonneg
    have hq0_μq : ∀ᵐ x ∂μq, q x ≠ 0 := hμq_ac hq0
    have hq_pos_μq : ∀ᵐ x ∂μq, 0 < q x := by
      filter_upwards [hq_nonneg_μq, hq0_μq] with x hx0 hx_ne0
      exact lt_of_le_of_ne hx0 (Ne.symm hx_ne0)
    filter_upwards [hrnDeriv, hp_nonneg_μq, hq_pos_μq] with x hx hp0 hqpos
    have hq0 : 0 ≤ q x := le_of_lt hqpos
    calc
      (μp.rnDeriv μq x).toReal =
          (ENNReal.ofReal (p x) * (ENNReal.ofReal (q x))⁻¹).toReal := by
            simp [hx]
      _ = p x / q x := by
            simp [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hp0,
              ENNReal.toReal_ofReal hq0, div_eq_mul_inv]
  -- Replace the RN-derivative integrand and convert the `μq`-integral to an `μ`-integral.
  have hDiv' :
      (InformationTheory.klDiv μp μq).toReal =
        ∫ x, q x * InformationTheory.klFun (p x / q x) ∂μ := by
    have h_integrand :
        (fun x ↦ InformationTheory.klFun (μp.rnDeriv μq x).toReal) =ᵐ[μq]
          fun x ↦ InformationTheory.klFun (p x / q x) := by
      exact hrnDeriv_toReal.mono fun x hx ↦ by simp [hx]
    -- Rewrite `∫ _ ∂μq` as `∫ (ofReal q).toReal * _ ∂μ` and simplify.
    have hqE_meas : AEMeasurable (fun x ↦ ENNReal.ofReal (q x)) μ :=
      (hq_int.aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    have hqE_lt_top : ∀ᵐ x ∂μ, ENNReal.ofReal (q x) < (⊤ : ℝ≥0∞) := by
      exact ae_of_all _ fun _x ↦ ENNReal.ofReal_lt_top
    have h2 :
        (∫ x, InformationTheory.klFun (p x / q x) ∂μq) =
          ∫ x, (ENNReal.ofReal (q x)).toReal * InformationTheory.klFun (p x / q x) ∂μ := by
      -- scalar multiplication is multiplication in `ℝ`
      simpa [μq, smul_eq_mul] using
        (integral_withDensity_eq_integral_toReal_smul₀ (μ := μ) (f := fun x ↦ ENNReal.ofReal (q x))
          hqE_meas hqE_lt_top (fun x ↦ InformationTheory.klFun (p x / q x)))
    have hqE_toReal : (fun x ↦ (ENNReal.ofReal (q x)).toReal) =ᵐ[μ] q := by
      filter_upwards [hq_nonneg] with x hx
      simp [ENNReal.toReal_ofReal hx]
    have h2' :
        (∫ x, (ENNReal.ofReal (q x)).toReal * InformationTheory.klFun (p x / q x) ∂μ) =
          ∫ x, q x * InformationTheory.klFun (p x / q x) ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hqE_toReal] with x hx
      simp [hx]
    -- Combine the steps.
    calc
      (InformationTheory.klDiv μp μq).toReal =
          ∫ x, InformationTheory.klFun (μp.rnDeriv μq x).toReal ∂μq := hDiv
      _ = ∫ x, InformationTheory.klFun (p x / q x) ∂μq := by
            exact integral_congr_ae h_integrand
      _ = ∫ x, (ENNReal.ofReal (q x)).toReal * InformationTheory.klFun (p x / q x) ∂μ := h2
      _ = ∫ x, q x * InformationTheory.klFun (p x / q x) ∂μ := h2'
  -- Finish by comparing with `hKL`.
  calc
    klIntegralReal (μ := μ) p q = ∫ x, q x * InformationTheory.klFun (p x / q x) ∂μ := hKL
    _ = (InformationTheory.klDiv μp μq).toReal := by
          simpa using hDiv'.symm

/-- Parametric wrapper for `klIntegralReal_eq_toReal_klDiv_withDensity_of_integral_eq`. -/
lemma klIntegralRealParam_eq_toReal_klDiv_withDensity_of_integral_eq
    [SigmaFinite μ]
    (p : ℝ → α → ℝ) (θ θ' : ℝ)
    (hp_nonneg : ∀ᵐ x ∂μ, 0 ≤ p θ x)
    (hq_nonneg : ∀ᵐ x ∂μ, 0 ≤ p θ' x)
    (hq0 : ∀ᵐ x ∂μ, p θ' x ≠ 0)
    (hp_int : Integrable (fun x ↦ p θ x) μ)
    (hq_int : Integrable (fun x ↦ p θ' x) μ)
    (hkl_int : Integrable (fun x ↦ p θ x * Real.log (p θ x / p θ' x)) μ)
    (h_eq : (∫ x, p θ x ∂μ) = ∫ x, p θ' x ∂μ)
    (hAC :
      (μ.withDensity fun x ↦ ENNReal.ofReal (p θ x)) ≪
        (μ.withDensity fun x ↦ ENNReal.ofReal (p θ' x))) :
    klIntegralRealParam (μ := μ) p θ θ' =
      (InformationTheory.klDiv
          (μ.withDensity fun x ↦ ENNReal.ofReal (p θ x))
          (μ.withDensity fun x ↦ ENNReal.ofReal (p θ' x))).toReal := by
  simpa [klIntegralRealParam] using
    (klIntegralReal_eq_toReal_klDiv_withDensity_of_integral_eq (μ := μ)
      (p := fun x ↦ p θ x) (q := fun x ↦ p θ' x)
      hp_nonneg hq_nonneg hq0 hp_int hq_int hkl_int h_eq hAC)

end

end FisherInformation
