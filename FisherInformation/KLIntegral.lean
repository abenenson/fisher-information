/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.InformationTheory.KullbackLeibler.KLFun
public import FisherInformation.KLFinite

/-!
# FisherInformation.KLIntegral

Measure-theoretic (integral) KL divergence and Fisher information.

This module complements `FisherInformation.KLFinite` by replacing finite sums over a `Fintype`
with Bochner integrals `∫ x, ... ∂μ` over an arbitrary measured space.

The main tool is Mathlib’s *differentiation under the integral sign* theorems from
`Mathlib.Analysis.Calculus.ParametricIntegral`, which let us turn analytic regularity hypotheses
(measurability, integrability, uniform derivative bounds) into `HasDerivAt` statements for
parametric integrals.

## Main definitions

* `klIntegralReal`: `∫ p * log(p/q)`.
* `klIntegralRealParam`: parametric KL `D_KL(p_θ || p_{θ'})` over a base measure `μ`.

## Main results

* `deriv_klIntegralRealParam_second` : derivative in the second parameter (under explicit
  dominated-differentiation hypotheses).
* `fisherKLIntegral_eq_fisherScoreIntegral` : integral analogue of `fisherKL_eq_fisherScore`.
* `klFiniteRealParam_eq_klIntegralRealParam_count` : the finite sum is the counting-measure
  specialization of the integral.
* `klIntegralReal_eq_integral_klFun_of_integral_eq` : bridge to Mathlib’s `InformationTheory.klFun`
  (the f-divergence integrand for KL).
-/

@[expose] public section

open scoped BigOperators

open TopologicalSpace MeasureTheory Filter Metric

namespace FisherInformation

noncomputable section

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- Real-valued KL divergence integrand, integrated against a base measure `μ`:

`∫ x, p x * log (p x / q x) ∂μ`.

This is the classical `∫ p log(p/q)` formula for densities on a common reference measure.
For now we keep the expression total by using `Real.log` on `ℝ`; typical information-geometry
applications will assume positivity / non-vanishing hypotheses so this matches the classical log.
-/
noncomputable def klIntegralReal (p q : α → ℝ) : ℝ :=
  ∫ x, p x * Real.log (p x / q x) ∂μ

/-- Parametric version of `klIntegralReal`: `D_KL(p_θ || p_{θ'})`. -/
noncomputable def klIntegralRealParam (p : ℝ → α → ℝ) (θ θ' : ℝ) : ℝ :=
  klIntegralReal (μ := μ) (p θ) (p θ')

/-- For equal total integrals, rewrite real KL using the weighted `klFun` integrand under
the stated integrability and almost-everywhere nonvanishing hypotheses. -/
lemma klIntegralReal_eq_integral_klFun_of_integral_eq
    (p q : α → ℝ)
    (hq0 : ∀ᵐ x ∂μ, q x ≠ 0)
    (hp_int : Integrable p μ)
    (hq_int : Integrable q μ)
    (hkl_int : Integrable (fun x ↦ p x * Real.log (p x / q x)) μ)
    (h_eq : (∫ x, p x ∂μ) = ∫ x, q x ∂μ) :
    klIntegralReal (μ := μ) p q =
      ∫ x, q x * InformationTheory.klFun (p x / q x) ∂μ := by
  have hpoint_ae :
      (fun x ↦ q x * InformationTheory.klFun (p x / q x)) =ᵐ[μ]
        fun x ↦ p x * Real.log (p x / q x) + (q x - p x) := by
    refine hq0.mono ?_
    intro x hqx
    -- `q * klFun(p/q) = p * log(p/q) + q - p` when `q ≠ 0` (so `q * (p/q) = p`).
    have hcancel : q x * p x * (q x)⁻¹ = p x := by
      calc
        q x * p x * (q x)⁻¹ = q x * p x / q x := by
          simp [div_eq_mul_inv, mul_assoc]
        _ = p x := by
          simpa using (mul_div_cancel_left₀ (b := p x) (a := q x) hqx)
    simp [InformationTheory.klFun, div_eq_mul_inv, mul_add, sub_eq_add_neg,
      add_assoc, add_left_comm,
      add_comm]
    ring_nf
    simp [hcancel]
  have h_integral :
      (∫ x, q x * InformationTheory.klFun (p x / q x) ∂μ) =
        (∫ x, p x * Real.log (p x / q x) ∂μ) + ∫ x, (q x - p x) ∂μ := by
    calc
      (∫ x, q x * InformationTheory.klFun (p x / q x) ∂μ) =
          ∫ x, (p x * Real.log (p x / q x) + (q x - p x)) ∂μ := by
            exact integral_congr_ae hpoint_ae
      _ = (∫ x, p x * Real.log (p x / q x) ∂μ) + ∫ x, (q x - p x) ∂μ := by
            exact integral_add hkl_int (hq_int.sub hp_int)
  have h_qmp_zero : (∫ x, (q x - p x) ∂μ) = 0 := by
    calc
      (∫ x, (q x - p x) ∂μ) = (∫ x, q x ∂μ) - ∫ x, p x ∂μ := by
        simpa using (integral_sub (μ := μ) hq_int hp_int)
      _ = 0 := sub_eq_zero.mpr h_eq.symm
  have h_qkl_eq :
      (∫ x, q x * InformationTheory.klFun (p x / q x) ∂μ) =
        ∫ x, p x * Real.log (p x / q x) ∂μ := by
    simpa [h_qmp_zero] using h_integral
  simpa [klIntegralReal] using h_qkl_eq.symm

/-!
## Differentiation in the second parameter

We now record a dominated-differentiation lemma for `θ' ↦ D_KL(p_θ || p_{θ'})`.

This is the integral analogue of `deriv_klFiniteRealParam_second` from the finite development.
-/

omit [MeasurableSpace α] μ in
/-- Differentiate the KL integrand in its denominator parameter when both density values are
nonzero and the parameterized density is differentiable. -/
lemma hasDerivAt_klIntegrand_secondArg
    (p : ℝ → α → ℝ) (θ t : ℝ) (x : α)
    (hpθ0 : p θ x ≠ 0)
    (hpt0 : p t x ≠ 0)
    (hp1 : DifferentiableAt ℝ (fun s ↦ p s x) t) :
    HasDerivAt (fun s ↦ p θ x * Real.log (p θ x / p s x))
      (-(p θ x) * (deriv (fun s ↦ p s x) t / p t x)) t := by
  have hlogDiff : DifferentiableAt ℝ (fun s ↦ Real.log (p θ x / p s x)) t := by
    have hdiv : DifferentiableAt ℝ (fun s ↦ p θ x / p s x) t := by
      simpa using! (differentiableAt_const (p θ x)).div hp1 hpt0
    refine hdiv.log ?_
    exact div_ne_zero hpθ0 hpt0
  have hlogHas :
      HasDerivAt (fun s ↦ Real.log (p θ x / p s x))
        (-(deriv (fun s ↦ p s x) t) / p t x) t := by
    simpa [FisherInformation.deriv_log_div_const (p := p) (θ := θ) (θ' := t)
      (x := x) hpθ0 hpt0 hp1] using
      hlogDiff.hasDerivAt
  have hmul :
      HasDerivAt (fun s ↦ p θ x * Real.log (p θ x / p s x))
        (p θ x * (-(deriv (fun s ↦ p s x) t) / p t x)) t :=
    hlogHas.const_mul (p θ x)
  simpa [neg_div, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Differentiate parametric real KL in its second parameter under the stated nonvanishing
and dominated-differentiation hypotheses on `ball θ' ε`. -/
theorem deriv_klIntegralRealParam_second
    (p : ℝ → α → ℝ) (θ θ' ε : ℝ) (ε_pos : 0 < ε)
    (hp0 : ∀ t : ℝ, ∀ x : α, p t x ≠ 0)
    (hF_meas :
      ∀ᶠ t in nhds θ', AEStronglyMeasurable (fun x ↦ p θ x * Real.log (p θ x / p t x)) μ)
    (hF_int : Integrable (fun x ↦ p θ x * Real.log (p θ x / p θ' x)) μ)
    (hF'_meas :
      AEStronglyMeasurable (fun x ↦ (-(p θ x) * (deriv (fun u ↦ p u x) θ' / p θ' x))) μ)
    (bound : α → ℝ)
    (h_bound :
      ∀ᵐ x ∂μ, ∀ t ∈ ball θ' ε, ‖-(p θ x) * (deriv (fun u ↦ p u x) t / p t x)‖ ≤ bound x)
    (bound_integrable : Integrable bound μ)
    (hp1 : ∀ x : α, ∀ t ∈ ball θ' ε, DifferentiableAt ℝ (fun u ↦ p u x) t) :
    deriv (fun t ↦ klIntegralRealParam (μ := μ) p θ t) θ' =
      ∫ x, (-(p θ x) * (deriv (fun u ↦ p u x) θ' / p θ' x)) ∂μ := by
  -- Use Mathlib’s dominated differentiation under the integral sign.
  have h_diff :
      ∀ᵐ x ∂μ, ∀ t ∈ ball θ' ε,
        HasDerivAt (fun s ↦ p θ x * Real.log (p θ x / p s x))
          (-(p θ x) * (deriv (fun u ↦ p u x) t / p t x)) t := by
    refine ae_of_all μ ?_
    intro x t ht
    exact
      hasDerivAt_klIntegrand_secondArg p θ t x (hp0 θ x) (hp0 t x) (hp1 x t ht)
  have h :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
        (F := fun t x ↦ p θ x * Real.log (p θ x / p t x))
        (F' := fun t x ↦ (-(p θ x) * (deriv (fun u ↦ p u x) t / p t x)))
        (bound := bound) (s := ball θ' ε) (x₀ := θ')
        (Metric.ball_mem_nhds θ' ε_pos)
        hF_meas hF_int hF'_meas h_bound bound_integrable h_diff)
  exact h.2.deriv

/-!
## Specializations / bridges
-/

/-- On a finite measurable type with measurable singletons, parametric integral KL for counting
measure equals the finite-sum KL expression. -/
theorem klFiniteRealParam_eq_klIntegralRealParam_count
    {β : Type} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (p : ℝ → β → ℝ) (θ θ' : ℝ) :
    klFiniteRealParam p θ θ' =
      klIntegralRealParam (μ := (Measure.count : Measure β)) p θ θ' := by
  classical
  simp [klIntegralRealParam, klIntegralReal, klFiniteRealParam, klFiniteReal,
    MeasureTheory.integral_count]

/-!
## Fisher information: KL Hessian vs score-squared

We now prove an integral analogue of `FisherInformation.fisherKL_eq_fisherScore` from the finite
development, under explicit dominated-differentiation hypotheses.

The proof follows the same algebraic pattern:

1. Differentiate the KL integral in the second argument to obtain `∫ -p_θ * (p'_{θ'} / p_{θ'})`.
2. Differentiate again at `θ' = θ` (dominated differentiation + quotient rule).
3. Use normalization `∫ p_t = 1` to eliminate the `∫ p''_θ` term.
-/

/-- Fisher information by the classical "score-squared expectation" formula:

`∫ (p'_θ(x))^2 / p_θ(x) ∂μ`.
-/
noncomputable def fisherScoreIntegral (p : ℝ → α → ℝ) (θ : ℝ) : ℝ :=
  ∫ x, (deriv (fun t ↦ p t x) θ) ^ 2 / p θ x ∂μ

/-- Fisher information defined as the KL Hessian:

`∂²/∂θ'² D_KL(p_θ || p_{θ'}) |_{θ'=θ}`.
-/
noncomputable def fisherKLIntegral (p : ℝ → α → ℝ) (θ : ℝ) : ℝ :=
  deriv (deriv (fun t ↦ klIntegralRealParam (μ := μ) p θ t)) θ

omit [MeasurableSpace α] μ in
/-- Differentiate the first KL-derivative integrand for a nonzero denominator under the stated
first- and second-differentiability hypotheses. -/
lemma hasDerivAt_scoreIntegrand_secondArg
    (p : ℝ → α → ℝ) (θ t : ℝ) (x : α)
    (hpt0 : p t x ≠ 0)
    (hp1 : DifferentiableAt ℝ (fun u ↦ p u x) t)
    (hp2 : DifferentiableAt ℝ (fun u ↦ deriv (fun s ↦ p s x) u) t) :
    HasDerivAt (fun s ↦ -(p θ x) * (deriv (fun u ↦ p u x) s / p s x))
      (-(p θ x) *
        ((deriv (fun u ↦ deriv (fun s ↦ p s x) u) t * p t x -
              deriv (fun u ↦ p u x) t * deriv (fun u ↦ p u x) t) / (p t x) ^ 2)) t := by
  have hnum :
      HasDerivAt (fun s ↦ deriv (fun u ↦ p u x) s)
        (deriv (fun u ↦ deriv (fun s ↦ p s x) u) t) t :=
    hp2.hasDerivAt
  have hden :
      HasDerivAt (fun s ↦ p s x) (deriv (fun u ↦ p u x) t) t :=
    hp1.hasDerivAt
  have hdiv :
      HasDerivAt (fun s ↦ deriv (fun u ↦ p u x) s / p s x)
        ((deriv (fun u ↦ deriv (fun s ↦ p s x) u) t * p t x -
              deriv (fun u ↦ p u x) t * deriv (fun u ↦ p u x) t) / (p t x) ^ 2) t := by
    simpa using! (hnum.div hden hpt0)
  simpa [mul_assoc] using (hdiv.const_mul (-(p θ x)))

/-- If `t ↦ ∫ p_t ∂μ` is constant on a neighborhood of `θ`, then
`∫ p''_θ ∂μ = 0`.

This is the measure-theoretic analogue of the finite identity `∑ p''_θ = 0`
used in `FisherInformation.KLFinite`.
-/
theorem integral_second_deriv_eq_zero_of_integral_eq_const
    (p : ℝ → α → ℝ) (θ ε c : ℝ) (ε_pos : 0 < ε)
    (hnorm : ∀ t ∈ ball θ ε, (∫ x, p t x ∂μ) = c)
    (hp1 : ∀ x : α, ∀ t ∈ ball θ ε, DifferentiableAt ℝ (fun u ↦ p u x) t)
    (hp2 : ∀ x : α, ∀ t ∈ ball θ ε, DifferentiableAt ℝ (fun u ↦ deriv (fun s ↦ p s x) u) t)
    (hP_meas : ∀ t ∈ ball θ ε, AEStronglyMeasurable (fun x ↦ p t x) μ)
    (hP_int : ∀ t ∈ ball θ ε, Integrable (fun x ↦ p t x) μ)
    (hP'_meas :
      ∀ t ∈ ball θ ε, AEStronglyMeasurable (fun x ↦ deriv (fun u ↦ p u x) t) μ)
    (bound₁ : α → ℝ)
    (h_bound₁ :
      ∀ᵐ x ∂μ, ∀ t ∈ ball θ ε, ‖deriv (fun u ↦ p u x) t‖ ≤ bound₁ x)
    (bound₁_int : Integrable bound₁ μ)
    (hP'_int : Integrable (fun x ↦ deriv (fun u ↦ p u x) θ) μ)
    (hP''_meas :
      AEStronglyMeasurable (fun x ↦ deriv (fun u ↦ deriv (fun s ↦ p s x) u) θ) μ)
    (bound₂ : α → ℝ)
    (h_bound₂ :
      ∀ᵐ x ∂μ, ∀ t ∈ ball θ ε, ‖deriv (fun u ↦ deriv (fun s ↦ p s x) u) t‖ ≤ bound₂ x)
    (bound₂_int : Integrable bound₂ μ) :
    (∫ x, deriv (fun u ↦ deriv (fun s ↦ p s x) u) θ ∂μ) = 0 := by
  classical
  -- `N(t) = ∫ p_t` and `M(t) = ∫ p'_t`.
  let N : ℝ → ℝ := fun t ↦ ∫ x, p t x ∂μ
  let M : ℝ → ℝ := fun t ↦ ∫ x, deriv (fun u ↦ p u x) t ∂μ
  have hnormEqOn : Set.EqOn N (fun _t : ℝ ↦ c) (ball θ ε) := by
    intro t ht
    simpa [N] using hnorm t ht
  -- Shrink the neighborhood so we can reuse uniform bounds on `ball θ ε`.
  have ε₂_pos : 0 < ε / 2 := half_pos ε_pos
  -- First derivative under the integral sign, pointwise on a neighborhood of `θ`.
  have hderivN_eqOn : Set.EqOn (deriv N) M (ball θ (ε / 2)) := by
    intro t ht
    have ht_big : t ∈ ball θ ε := by
      have ht' : dist t θ < ε / 2 := by
        simpa [Metric.ball] using ht
      have : dist t θ < ε := lt_of_lt_of_le ht' (le_of_lt (half_lt_self ε_pos))
      simpa [Metric.ball] using this
    have hF_meas_t :
        ∀ᶠ u in nhds t, AEStronglyMeasurable (fun x ↦ p u x) μ := by
      have hball : ∀ᶠ u in nhds t, u ∈ ball θ ε :=
        (Metric.isOpen_ball.mem_nhds ht_big : ball θ ε ∈ nhds t)
      exact hball.mono fun u hu ↦ hP_meas u hu
    have hF_int_t : Integrable (fun x ↦ p t x) μ :=
      hP_int t ht_big
    have hF'_meas_t : AEStronglyMeasurable (fun x ↦ deriv (fun u ↦ p u x) t) μ :=
      hP'_meas t ht_big
    have h_bound_t :
        ∀ᵐ x ∂μ, ∀ u ∈ ball t (ε / 2), ‖deriv (fun s ↦ p s x) u‖ ≤ bound₁ x := by
      refine h_bound₁.mono ?_
      intro x hx u hu
      have hu_big : u ∈ ball θ ε := by
        have ht' : dist t θ < ε / 2 := by
          simpa [Metric.ball] using ht
        have hu' : dist u t < ε / 2 := by
          simpa [Metric.ball] using hu
        have htriangle : dist u θ ≤ dist u t + dist t θ := dist_triangle u t θ
        have hlt : dist u t + dist t θ < ε := by
          have := add_lt_add hu' ht'
          simpa [add_halves, add_comm, add_left_comm, add_assoc] using this
        have : dist u θ < ε := lt_of_le_of_lt htriangle hlt
        simpa [Metric.ball] using this
      exact hx u hu_big
    have h_diff :
        ∀ᵐ x ∂μ, ∀ u ∈ ball t (ε / 2),
          HasDerivAt (fun s ↦ p s x) (deriv (fun u ↦ p u x) u) u := by
      refine ae_of_all μ ?_
      intro x u hu
      have hu_big : u ∈ ball θ ε := by
        have ht' : dist t θ < ε / 2 := by
          simpa [Metric.ball] using ht
        have hu' : dist u t < ε / 2 := by
          simpa [Metric.ball] using hu
        have htriangle : dist u θ ≤ dist u t + dist t θ := dist_triangle u t θ
        have hlt : dist u t + dist t θ < ε := by
          have := add_lt_add hu' ht'
          simpa [add_halves, add_comm, add_left_comm, add_assoc] using this
        have : dist u θ < ε := lt_of_le_of_lt htriangle hlt
        simpa [Metric.ball] using this
      exact (hp1 x u hu_big).hasDerivAt
    have h :=
      (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
          (F := fun u x ↦ p u x)
          (F' := fun u x ↦ deriv (fun s ↦ p s x) u)
          (bound := bound₁) (s := ball t (ε / 2)) (x₀ := t)
          (Metric.ball_mem_nhds t ε₂_pos)
          hF_meas_t hF_int_t hF'_meas_t h_bound_t bound₁_int h_diff)
    -- Extract the `deriv` formula at `t`.
    have : deriv N t = ∫ x, deriv (fun u ↦ p u x) t ∂μ := by
      simpa [N] using h.2.deriv
    simpa [M] using this
  -- Since `N` is constant on `ball θ ε`, we have `deriv N = 0` there.
  have hderivN_zero : Set.EqOn (deriv N) (fun _t : ℝ ↦ (0 : ℝ)) (ball θ ε) := by
    have hopen : IsOpen (ball θ ε) := Metric.isOpen_ball
    simpa using (hnormEqOn.deriv hopen : Set.EqOn (deriv N) (deriv (fun _t : ℝ ↦ c)) (ball θ ε))
  -- Therefore `M = 0` on `ball θ (ε/2)`.
  have hM_zero : Set.EqOn M (fun _t : ℝ ↦ (0 : ℝ)) (ball θ (ε / 2)) := by
    intro t ht
    have ht_big : t ∈ ball θ ε := by
      have ht' : dist t θ < ε / 2 := by
        simpa [Metric.ball] using ht
      have : dist t θ < ε := lt_of_lt_of_le ht' (le_of_lt (half_lt_self ε_pos))
      simpa [Metric.ball] using this
    have hderivNt : deriv N t = 0 := by
      simpa using (hderivN_zero ht_big)
    have hderivNt_eq : deriv N t = M t :=
      hderivN_eqOn ht
    simpa [hderivNt_eq] using hderivNt
  -- Hence `deriv M θ = 0`.
  have hderivM_zero : deriv M θ = 0 := by
    have hopen : IsOpen (ball θ (ε / 2)) := Metric.isOpen_ball
    have hEqDeriv :
        Set.EqOn (deriv M) (deriv (fun _t : ℝ ↦ (0 : ℝ))) (ball θ (ε / 2)) :=
      hM_zero.deriv hopen
    have hθ_in : θ ∈ ball θ (ε / 2) := mem_ball_self ε₂_pos
    simpa using (hEqDeriv hθ_in)
  -- Compute `deriv M θ` by dominated differentiation (second derivative under the integral sign).
  have hF_meas₂ :
      ∀ᶠ t in nhds θ,
        AEStronglyMeasurable (fun x ↦ deriv (fun u ↦ p u x) t) μ := by
    have hball : ∀ᶠ t in nhds θ, t ∈ ball θ ε := by
      exact Metric.ball_mem_nhds θ ε_pos
    exact hball.mono fun t ht ↦ hP'_meas t ht
  have h_diff₂ :
      ∀ᵐ x ∂μ, ∀ t ∈ ball θ ε,
        HasDerivAt (fun s ↦ deriv (fun u ↦ p u x) s)
          (deriv (fun u ↦ deriv (fun s ↦ p s x) u) t) t := by
    refine ae_of_all μ ?_
    intro x t ht
    exact (hp2 x t ht).hasDerivAt
  have h₂ :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
        (F := fun t x ↦ deriv (fun u ↦ p u x) t)
        (F' := fun t x ↦ deriv (fun u ↦ deriv (fun s ↦ p s x) u) t)
        (bound := bound₂) (s := ball θ ε) (x₀ := θ)
        (Metric.ball_mem_nhds θ ε_pos)
        hF_meas₂ hP'_int hP''_meas h_bound₂ bound₂_int h_diff₂)
  have hderivM :
      deriv M θ =
        ∫ x, deriv (fun u ↦ deriv (fun s ↦ p s x) u) θ ∂μ := by
    simpa [M] using h₂.2.deriv
  -- Compare the two computations of `deriv M θ`.
  have : (∫ x, deriv (fun u ↦ deriv (fun s ↦ p s x) u) θ ∂μ) = 0 := by
    -- `deriv M θ = 0` by constancy, but also by differentiation under the integral sign.
    simpa [hderivM] using hderivM_zero
  simpa using this

/-- The second KL derivative equals the score integral under the stated regularity,
integrability, domination and vanishing integral of the second density derivative. -/
theorem fisherKLIntegral_eq_fisherScoreIntegral
    (p : ℝ → α → ℝ) (θ ε : ℝ) (ε_pos : 0 < ε)
    (hp0 : ∀ t : ℝ, ∀ x : α, p t x ≠ 0)
    -- Regularity of `p` (pointwise in `x`) on a neighborhood of `θ`.
    (hp1 : ∀ x : α, ∀ t ∈ ball θ ε, DifferentiableAt ℝ (fun u ↦ p u x) t)
    (hp2 : ∀ x : α, ∀ t ∈ ball θ ε, DifferentiableAt ℝ (fun u ↦ deriv (fun s ↦ p s x) u) t)
    -- Measurability/integrability for the KL integrand on the same neighborhood.
    (hKL_meas :
      ∀ t ∈ ball θ ε,
        AEStronglyMeasurable (fun x ↦ p θ x * Real.log (p θ x / p t x)) μ)
    (hKL_int :
      ∀ t ∈ ball θ ε, Integrable (fun x ↦ p θ x * Real.log (p θ x / p t x)) μ)
    -- First-derivative integrand measurability + uniform domination on `ball θ ε`.
    (hKL'_meas :
      ∀ t ∈ ball θ ε,
        AEStronglyMeasurable (fun x ↦ (-(p θ x) * (deriv (fun u ↦ p u x) t / p t x))) μ)
    (bound₁ : α → ℝ)
    (h_bound₁ :
      ∀ᵐ x ∂μ, ∀ t ∈ ball θ ε, ‖-(p θ x) * (deriv (fun u ↦ p u x) t / p t x)‖ ≤ bound₁ x)
    (bound₁_int : Integrable bound₁ μ)
    (hKL'_int :
      Integrable (fun x ↦ (-(p θ x) * (deriv (fun u ↦ p u x) θ / p θ x))) μ)
    -- Second-derivative integrand measurability + uniform domination on `ball θ ε`.
    (hKL''_meas :
      AEStronglyMeasurable
        (fun x ↦
          (-(p θ x) *
            ((deriv (fun u ↦ deriv (fun s ↦ p s x) u) θ * p θ x -
                    deriv (fun u ↦ p u x) θ * deriv (fun u ↦ p u x) θ) / (p θ x) ^ 2))) μ)
    (bound₂ : α → ℝ)
    (h_bound₂ :
      ∀ᵐ x ∂μ, ∀ t ∈ ball θ ε,
        ‖-(p θ x) *
            ((deriv (fun u ↦ deriv (fun s ↦ p s x) u) t * p t x -
                    deriv (fun u ↦ p u x) t * deriv (fun u ↦ p u x) t) / (p t x) ^ 2)‖
          ≤ bound₂ x)
    (bound₂_int : Integrable bound₂ μ)
    -- Integrability at `θ` of the score-squared integrand (the RHS).
    (hScore_int : Integrable (fun x ↦ (deriv (fun t ↦ p t x) θ) ^ 2 / p θ x) μ)
    (hSecond_int : Integrable (fun x ↦ deriv (fun u ↦ deriv (fun s ↦ p s x) u) θ) μ)
    (hInt_second : (∫ x, deriv (fun u ↦ deriv (fun s ↦ p s x) u) θ ∂μ) = 0) :
    fisherKLIntegral (μ := μ) p θ = fisherScoreIntegral (μ := μ) p θ := by
  classical
  -- Shrink the neighborhood so we can reuse uniform bounds on `ball θ ε`.
  have ε₂_pos : 0 < ε / 2 := half_pos ε_pos
  have hθ_in_big : θ ∈ ball θ ε := mem_ball_self ε_pos
  -- `g(t) = D_KL(p_θ || p_t)` and its candidate derivative `h(t) = ∫ -p_θ * (p'_t/p_t)`.
  let g : ℝ → ℝ := fun t ↦ klIntegralRealParam (μ := μ) p θ t
  let h : ℝ → ℝ := fun t ↦ ∫ x, (-(p θ x) * (deriv (fun u ↦ p u x) t / p t x)) ∂μ
  -- First derivative: `deriv g = h` on a small ball around `θ`.
  have hderiv_eqOn : Set.EqOn (deriv g) h (ball θ (ε / 2)) := by
    intro t ht
    have ht_big : t ∈ ball θ ε := by
      have ht' : dist t θ < ε / 2 := by
        simpa [Metric.ball] using ht
      have : dist t θ < ε := lt_of_lt_of_le ht' (le_of_lt (half_lt_self ε_pos))
      simpa [Metric.ball] using this
    have hF_meas_t :
        ∀ᶠ u in nhds t, AEStronglyMeasurable (fun x ↦ p θ x * Real.log (p θ x / p u x)) μ := by
      have hball : ∀ᶠ u in nhds t, u ∈ ball θ ε :=
        (Metric.isOpen_ball.mem_nhds ht_big : ball θ ε ∈ nhds t)
      exact hball.mono fun u hu ↦ hKL_meas u hu
    have hF_int_t : Integrable (fun x ↦ p θ x * Real.log (p θ x / p t x)) μ :=
      hKL_int t ht_big
    have hF'_meas_t :
        AEStronglyMeasurable (fun x ↦ (-(p θ x) * (deriv (fun u ↦ p u x) t / p t x))) μ :=
      hKL'_meas t ht_big
    have h_bound_t :
        ∀ᵐ x ∂μ, ∀ u ∈ ball t (ε / 2),
          ‖-(p θ x) * (deriv (fun u ↦ p u x) u / p u x)‖ ≤ bound₁ x := by
      refine h_bound₁.mono ?_
      intro x hx u hu
      -- `u ∈ ball t (ε/2)` and `t ∈ ball θ (ε/2)` imply `u ∈ ball θ ε`.
      have hu_big : u ∈ ball θ ε := by
        have ht' : dist t θ < ε / 2 := by
          simpa [Metric.ball] using ht
        have hu' : dist u t < ε / 2 := by
          simpa [Metric.ball] using hu
        have htriangle : dist u θ ≤ dist u t + dist t θ := dist_triangle u t θ
        have hlt : dist u t + dist t θ < ε := by
          have := add_lt_add hu' ht'
          simpa [add_halves, add_comm, add_left_comm, add_assoc] using this
        have : dist u θ < ε := lt_of_le_of_lt htriangle hlt
        simpa [Metric.ball] using this
      exact hx u hu_big
    have hp1_t : ∀ x : α, ∀ u ∈ ball t (ε / 2), DifferentiableAt ℝ (fun u ↦ p u x) u := by
      intro x u hu
      have hu_big : u ∈ ball θ ε := by
        have ht' : dist t θ < ε / 2 := by
          simpa [Metric.ball] using ht
        have hu' : dist u t < ε / 2 := by
          simpa [Metric.ball] using hu
        have htriangle : dist u θ ≤ dist u t + dist t θ := dist_triangle u t θ
        have hlt : dist u t + dist t θ < ε := by
          have := add_lt_add hu' ht'
          simpa [add_halves, add_comm, add_left_comm, add_assoc] using this
        have : dist u θ < ε := lt_of_le_of_lt htriangle hlt
        simpa [Metric.ball] using this
      exact hp1 x u hu_big
    -- Apply the pointwise derivative lemma at `θ' = t` with radius `ε/2`.
    simpa [g, h, klIntegralRealParam] using
      (deriv_klIntegralRealParam_second (μ := μ) (p := p) (θ := θ) (θ' := t) (ε := ε / 2)
        ε₂_pos (hp0 := hp0) (hF_meas := hF_meas_t) (hF_int := hF_int_t)
        (hF'_meas := hF'_meas_t) (bound := bound₁) (h_bound := h_bound_t)
        (bound_integrable := bound₁_int) (hp1 := hp1_t))
  -- Second derivative at `θ`: use `Set.EqOn.deriv` to replace `deriv (deriv g)` by `deriv h`.
  have hsecond_eq : fisherKLIntegral (μ := μ) p θ = deriv h θ := by
    -- `ball θ (ε/2)` is open and contains `θ`.
    have hopen : IsOpen (ball θ (ε / 2)) := Metric.isOpen_ball
    have hEqDeriv : Set.EqOn (deriv (deriv g)) (deriv h) (ball θ (ε / 2)) :=
      hderiv_eqOn.deriv hopen
    have hθ_in_small : θ ∈ ball θ (ε / 2) := mem_ball_self ε₂_pos
    simpa [fisherKLIntegral, g] using (hEqDeriv hθ_in_small)
  -- Compute `deriv h θ` by dominated differentiation under the integral sign.
  have h_diff₂ :
      ∀ᵐ x ∂μ, ∀ t ∈ ball θ ε,
        HasDerivAt (fun s ↦ (-(p θ x) * (deriv (fun u ↦ p u x) s / p s x)))
          (-(p θ x) *
            ((deriv (fun u ↦ deriv (fun s ↦ p s x) u) t * p t x -
                    deriv (fun u ↦ p u x) t * deriv (fun u ↦ p u x) t) / (p t x) ^ 2)) t := by
    refine ae_of_all μ ?_
    intro x t ht
    exact
      hasDerivAt_scoreIntegrand_secondArg (p := p) (θ := θ) (t := t) (x := x)
        (hpt0 := hp0 t x) (hp1 := hp1 x t ht) (hp2 := hp2 x t ht)
  have hF_meas₂ :
      ∀ᶠ t in nhds θ,
        AEStronglyMeasurable (fun x ↦ (-(p θ x) * (deriv (fun u ↦ p u x) t / p t x))) μ := by
    have hball : ∀ᶠ t in nhds θ, t ∈ ball θ ε := (Metric.ball_mem_nhds _ ε_pos)
    exact hball.mono fun t ht ↦ hKL'_meas t ht
  have hF_int₂ : Integrable (fun x ↦ (-(p θ x) * (deriv (fun u ↦ p u x) θ / p θ x))) μ := by
    exact hKL'_int
  have h_dom :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
        (F := fun t x ↦ (-(p θ x) * (deriv (fun u ↦ p u x) t / p t x)))
        (F' := fun t x ↦
          (-(p θ x) *
            ((deriv (fun u ↦ deriv (fun s ↦ p s x) u) t * p t x -
                    deriv (fun u ↦ p u x) t * deriv (fun u ↦ p u x) t) / (p t x) ^ 2)))
        (bound := bound₂) (s := ball θ ε) (x₀ := θ)
        (Metric.ball_mem_nhds θ ε_pos)
        hF_meas₂ hF_int₂ hKL''_meas h_bound₂ bound₂_int h_diff₂)
  have hderiv_h :
      deriv h θ =
        ∫ x,
          (-(p θ x) *
            ((deriv (fun u ↦ deriv (fun s ↦ p s x) u) θ * p θ x -
                    deriv (fun u ↦ p u x) θ * deriv (fun u ↦ p u x) θ) / (p θ x) ^ 2)) ∂μ := by
    simpa [h] using h_dom.2.deriv
  -- Simplify the second-derivative integrand at `θ`.
  have hpoint_simpl :
      (fun x ↦
          -(p θ x *
            ((deriv (fun u ↦ deriv (fun s ↦ p s x) u) θ * p θ x -
                    deriv (fun u ↦ p u x) θ * deriv (fun u ↦ p u x) θ) / (p θ x) ^ 2))) =
        fun x ↦
          -(deriv (fun u ↦ deriv (fun s ↦ p s x) u) θ) +
            (deriv (fun u ↦ p u x) θ) ^ 2 / p θ x := by
    funext x
    have hpθx0 : p θ x ≠ 0 := hp0 θ x
    field_simp [hpθx0]
    ring
  -- Put everything together.
  calc
    fisherKLIntegral (μ := μ) p θ
        = deriv h θ := hsecond_eq
    _ = ∫ x,
          (-(p θ x) *
            ((deriv (fun u ↦ deriv (fun s ↦ p s x) u) θ * p θ x -
                    deriv (fun u ↦ p u x) θ * deriv (fun u ↦ p u x) θ) / (p θ x) ^ 2)) ∂μ := by
          simp [hderiv_h]
    _ = ∫ x,
          (-(deriv (fun u ↦ deriv (fun s ↦ p s x) u) θ) +
            (deriv (fun u ↦ p u x) θ) ^ 2 / p θ x) ∂μ := by
          simp [hpoint_simpl]
    _ = -(∫ x, deriv (fun u ↦ deriv (fun s ↦ p s x) u) θ ∂μ) +
          ∫ x, (deriv (fun u ↦ p u x) θ) ^ 2 / p θ x ∂μ := by
          -- split the integral
          have hInt1 : Integrable (fun x ↦ -(deriv (fun u ↦ deriv (fun s ↦ p s x) u) θ)) μ :=
            hSecond_int.neg
          have hInt2 :
              Integrable (fun x ↦ (deriv (fun u ↦ p u x) θ) ^ 2 / p θ x) μ :=
            hScore_int
          calc
            (∫ x,
                (-(deriv (fun u ↦ deriv (fun s ↦ p s x) u) θ) +
                  (deriv (fun u ↦ p u x) θ) ^ 2 / p θ x) ∂μ)
                =
                (∫ x, (-(deriv (fun u ↦ deriv (fun s ↦ p s x) u) θ)) ∂μ) +
                  ∫ x, (deriv (fun u ↦ p u x) θ) ^ 2 / p θ x ∂μ := by
                    simpa using (integral_add (μ := μ) hInt1 hInt2)
            _ = -(∫ x, deriv (fun u ↦ deriv (fun s ↦ p s x) u) θ ∂μ) +
                  ∫ x, (deriv (fun u ↦ p u x) θ) ^ 2 / p θ x ∂μ := by
                    simp [integral_neg]
    _ = ∫ x, (deriv (fun u ↦ p u x) θ) ^ 2 / p θ x ∂μ := by
          -- cancel the `∫ p''_θ` term
          simp [hInt_second]
    _ = fisherScoreIntegral (μ := μ) p θ := rfl

/-- Variant of `fisherKLIntegral_eq_fisherScoreIntegral` where the cancellation
`∫ p''_θ = 0` is derived from a local normalization hypothesis `∫ p_t = c`. -/
theorem fisherKLIntegral_eq_fisherScoreIntegral_of_integral_eq_const
    (p : ℝ → α → ℝ) (θ ε c : ℝ) (ε_pos : 0 < ε)
    (hnorm : ∀ t ∈ ball θ ε, (∫ x, p t x ∂μ) = c)
    (hp0 : ∀ t : ℝ, ∀ x : α, p t x ≠ 0)
    -- Regularity of `p` (pointwise in `x`) on a neighborhood of `θ`.
    (hp1 : ∀ x : α, ∀ t ∈ ball θ ε, DifferentiableAt ℝ (fun u ↦ p u x) t)
    (hp2 : ∀ x : α, ∀ t ∈ ball θ ε, DifferentiableAt ℝ (fun u ↦ deriv (fun s ↦ p s x) u) t)
    -- Regularity hypotheses for differentiating `t ↦ ∫ p_t` twice.
    (hP_meas : ∀ t ∈ ball θ ε, AEStronglyMeasurable (fun x ↦ p t x) μ)
    (hP_int : ∀ t ∈ ball θ ε, Integrable (fun x ↦ p t x) μ)
    (hP'_meas :
      ∀ t ∈ ball θ ε, AEStronglyMeasurable (fun x ↦ deriv (fun u ↦ p u x) t) μ)
    (pBound₁ : α → ℝ)
    (h_pBound₁ :
      ∀ᵐ x ∂μ, ∀ t ∈ ball θ ε, ‖deriv (fun u ↦ p u x) t‖ ≤ pBound₁ x)
    (pBound₁_int : Integrable pBound₁ μ)
    (hP'_int : Integrable (fun x ↦ deriv (fun u ↦ p u x) θ) μ)
    (hP''_meas :
      AEStronglyMeasurable (fun x ↦ deriv (fun u ↦ deriv (fun s ↦ p s x) u) θ) μ)
    (pBound₂ : α → ℝ)
    (h_pBound₂ :
      ∀ᵐ x ∂μ, ∀ t ∈ ball θ ε, ‖deriv (fun u ↦ deriv (fun s ↦ p s x) u) t‖ ≤ pBound₂ x)
    (pBound₂_int : Integrable pBound₂ μ)
    -- Measurability/integrability for the KL integrand on the same neighborhood.
    (hKL_meas :
      ∀ t ∈ ball θ ε,
        AEStronglyMeasurable (fun x ↦ p θ x * Real.log (p θ x / p t x)) μ)
    (hKL_int :
      ∀ t ∈ ball θ ε, Integrable (fun x ↦ p θ x * Real.log (p θ x / p t x)) μ)
    -- First-derivative integrand measurability + uniform domination on `ball θ ε`.
    (hKL'_meas :
      ∀ t ∈ ball θ ε,
        AEStronglyMeasurable (fun x ↦ (-(p θ x) * (deriv (fun u ↦ p u x) t / p t x))) μ)
    (bound₁ : α → ℝ)
    (h_bound₁ :
      ∀ᵐ x ∂μ, ∀ t ∈ ball θ ε, ‖-(p θ x) * (deriv (fun u ↦ p u x) t / p t x)‖ ≤ bound₁ x)
    (bound₁_int : Integrable bound₁ μ)
    (hKL'_int :
      Integrable (fun x ↦ (-(p θ x) * (deriv (fun u ↦ p u x) θ / p θ x))) μ)
    -- Second-derivative integrand measurability + uniform domination on `ball θ ε`.
    (hKL''_meas :
      AEStronglyMeasurable
        (fun x ↦
          (-(p θ x) *
            ((deriv (fun u ↦ deriv (fun s ↦ p s x) u) θ * p θ x -
                    deriv (fun u ↦ p u x) θ * deriv (fun u ↦ p u x) θ) / (p θ x) ^ 2))) μ)
    (bound₂ : α → ℝ)
    (h_bound₂ :
      ∀ᵐ x ∂μ, ∀ t ∈ ball θ ε,
        ‖-(p θ x) *
            ((deriv (fun u ↦ deriv (fun s ↦ p s x) u) t * p t x -
                    deriv (fun u ↦ p u x) t * deriv (fun u ↦ p u x) t) / (p t x) ^ 2)‖
          ≤ bound₂ x)
    (bound₂_int : Integrable bound₂ μ)
    -- Integrability at `θ` of the score-squared integrand (the RHS).
    (hScore_int : Integrable (fun x ↦ (deriv (fun t ↦ p t x) θ) ^ 2 / p θ x) μ)
    (hSecond_int : Integrable (fun x ↦ deriv (fun u ↦ deriv (fun s ↦ p s x) u) θ) μ) :
    fisherKLIntegral (μ := μ) p θ = fisherScoreIntegral (μ := μ) p θ := by
  have hInt_second :
      (∫ x, deriv (fun u ↦ deriv (fun s ↦ p s x) u) θ ∂μ) = 0 := by
    simpa using
      (integral_second_deriv_eq_zero_of_integral_eq_const (μ := μ) (p := p)
        (θ := θ) (ε := ε) (c := c) ε_pos hnorm hp1 hp2 hP_meas hP_int hP'_meas
        pBound₁ h_pBound₁ pBound₁_int hP'_int hP''_meas pBound₂ h_pBound₂ pBound₂_int)
  exact
    fisherKLIntegral_eq_fisherScoreIntegral (μ := μ) (p := p) (θ := θ) (ε := ε) ε_pos hp0 hp1 hp2
      hKL_meas hKL_int hKL'_meas bound₁ h_bound₁ bound₁_int hKL'_int hKL''_meas bound₂ h_bound₂
      bound₂_int hScore_int hSecond_int hInt_second

end

end FisherInformation
