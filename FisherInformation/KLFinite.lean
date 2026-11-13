/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# FisherInformation.KLFinite

Finite/discrete Fisher information via KL divergence.

This module develops a mathlib-only, finite sample-space (`Fintype`) version of a classical
information-geometry identity:

- the Fisher information defined as a second derivative (Hessian) of the KL divergence
  `D_KL(p_θ || p_{θ'})` in the second argument at `θ' = θ`, and
- the Fisher information defined by the classical "score-squared expectation" formula,

coincide under explicit regularity and normalization hypotheses.

## Main results

* `fisherKL_eq_fisherScore` : `fisherKL p θ = fisherScore p θ` under hypotheses.
-/

@[expose] public section

open scoped BigOperators

namespace FisherInformation

/-- The finite real sum of weighted logarithmic ratios, with no normalization built into the
definition. -/
noncomputable def klFiniteReal {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ x, p x * Real.log (p x / q x)

/-- Finite/discrete KL divergence `D_KL(p_θ || p_{θ'})` as a finite sum,
for an arbitrary parameter type `Θ`. -/
noncomputable def klFiniteRealParamGen {Θ α : Type*} [Fintype α] (p : Θ → α → ℝ) (θ θ' : Θ) : ℝ :=
  klFiniteReal (p θ) (p θ')

/-- The finite real logarithmic-ratio sum between two points of a real-parameter family. -/
noncomputable def klFiniteRealParam {α : Type*} [Fintype α] (p : ℝ → α → ℝ) (θ θ' : ℝ) : ℝ :=
  klFiniteReal (p θ) (p θ')

/-- The derivative of a constant-numerator logarithmic ratio under the stated nonzero and
differentiability hypotheses. -/
lemma deriv_log_div_const
    {α : Type*} (p : ℝ → α → ℝ) (θ θ' : ℝ) (x : α)
    (hpθ0 : p θ x ≠ 0)
    (hpθ'0 : p θ' x ≠ 0)
    (hp1 : DifferentiableAt ℝ (fun t ↦ p t x) θ') :
    deriv (fun t ↦ Real.log (p θ x / p t x)) θ' =
      -(deriv (fun t ↦ p t x) θ') / p θ' x := by
  have hnum : DifferentiableAt ℝ (fun _t ↦ p θ x) θ' := differentiableAt_const _
  have hden : DifferentiableAt ℝ (fun t ↦ p t x) θ' := hp1
  have hden0 : (fun t ↦ p t x) θ' ≠ 0 := hpθ'0
  have hf0 : (fun t ↦ p θ x / p t x) θ' ≠ 0 := by
    simpa using (div_ne_zero hpθ0 hpθ'0)
  have hlog :
      deriv (fun t ↦ Real.log ((p θ x) / (p t x))) θ' =
        deriv (fun t ↦ p θ x / p t x) θ' / ((p θ x) / (p θ' x)) := by
    simpa using
      (deriv.log (f := fun t ↦ p θ x / p t x) (x := θ') (hnum.div hden hden0) hf0)
  have hdiv :
      deriv (fun t ↦ p θ x / p t x) θ' =
        (0 * p θ' x - p θ x * deriv (fun t ↦ p t x) θ') / (p θ' x) ^ 2 := by
    simpa [Pi.div_def] using
      (deriv_div (c := fun _t ↦ p θ x) (d := fun t ↦ p t x)
        (x := θ') hnum hden hden0)
  calc
    deriv (fun t ↦ Real.log (p θ x / p t x)) θ'
        = ((0 * p θ' x - p θ x * deriv (fun t ↦ p t x) θ') / (p θ' x) ^ 2) / (p θ x / p θ' x) := by
          simp [hlog, hdiv]
    _ = -(deriv (fun t ↦ p t x) θ') / p θ' x := by
          field_simp [hpθ0, hpθ'0]
          ring

/-- The derivative in the second parameter is the stated weighted finite score sum under the
supplied hypotheses. -/
lemma deriv_klFiniteRealParam_second
    {α : Type*} [Fintype α]
    (p : ℝ → α → ℝ) (θ θ' : ℝ)
    (hpθ0 : ∀ x : α, p θ x ≠ 0)
    (hpθ'0 : ∀ x : α, p θ' x ≠ 0)
    (hp1 : ∀ x : α, DifferentiableAt ℝ (fun t ↦ p t x) θ') :
    deriv (fun t ↦ klFiniteRealParam p θ t) θ' =
      -∑ x : α, p θ x * (deriv (fun t ↦ p t x) θ' / p θ' x) := by
  classical
  unfold klFiniteRealParam klFiniteReal
  have hdiff : ∀ x : α,
      DifferentiableAt ℝ (fun t ↦ p θ x * Real.log (p θ x / p t x)) θ' := by
    intro x
    have hdiv : DifferentiableAt ℝ (fun t ↦ p θ x / p t x) θ' := by
      simpa only [Pi.div_def] using
        (differentiableAt_const (p θ x)).div (hp1 x) (hpθ'0 x)
    have hlog : DifferentiableAt ℝ (fun t ↦ Real.log (p θ x / p t x)) θ' := by
      refine hdiv.log ?_
      exact div_ne_zero (hpθ0 x) (hpθ'0 x)
    simpa only [Pi.mul_def] using (differentiableAt_const (p θ x)).mul hlog
  have hderiv_term : ∀ x : α,
      deriv (fun t ↦ p θ x * Real.log (p θ x / p t x)) θ' =
        -(p θ x * (deriv (fun t ↦ p t x) θ' / p θ' x)) := by
    intro x
    have hlog' :
        deriv (fun t ↦ Real.log (p θ x / p t x)) θ' =
          -(deriv (fun t ↦ p t x) θ') / p θ' x :=
      deriv_log_div_const p θ θ' x (hpθ0 x) (hpθ'0 x) (hp1 x)
    have hlogDiff : DifferentiableAt ℝ (fun t ↦ Real.log (p θ x / p t x)) θ' := by
      have hdiv : DifferentiableAt ℝ (fun t ↦ p θ x / p t x) θ' := by
        simpa only [Pi.div_def] using
          (differentiableAt_const (p θ x)).div (hp1 x) (hpθ'0 x)
      refine hdiv.log ?_
      exact div_ne_zero (hpθ0 x) (hpθ'0 x)
    have hmul :
        deriv (fun t ↦ p θ x * Real.log (p θ x / p t x)) θ' =
          p θ x * deriv (fun t ↦ Real.log (p θ x / p t x)) θ' := by
      exact
        deriv_const_mul (c := p θ x) (d := fun t ↦ Real.log (p θ x / p t x)) (x := θ') hlogDiff
    calc
      deriv (fun t ↦ p θ x * Real.log (p θ x / p t x)) θ'
          = p θ x * (-(deriv (fun t ↦ p t x) θ') / p θ' x) := by
            simp [hmul, hlog']
      _ = p θ x * (-(deriv (fun t ↦ p t x) θ' / p θ' x)) := by
            simp [neg_div]
      _ = -(p θ x * (deriv (fun t ↦ p t x) θ' / p θ' x)) := by
            simp
  have hsum :
      deriv (∑ x : α, fun t ↦ p θ x * Real.log (p θ x / p t x)) θ' =
        ∑ x : α, deriv (fun t ↦ p θ x * Real.log (p θ x / p t x)) θ' := by
    simpa using
      (deriv_sum (x := θ') (u := Finset.univ)
        (A := fun x : α ↦ fun t ↦ p θ x * Real.log (p θ x / p t x))
        (h := by
          intro x _hx
          exact hdiff x))
  have hfun :
      (fun t ↦ ∑ x : α, p θ x * Real.log (p θ x / p t x)) =
        (∑ x : α, fun t ↦ p θ x * Real.log (p θ x / p t x)) := by
    funext t
    simp
  calc
    deriv (fun t ↦ ∑ x : α, p θ x * Real.log (p θ x / p t x)) θ'
        = deriv (∑ x : α, fun t ↦ p θ x * Real.log (p θ x / p t x)) θ' := by
          simp [hfun]
    _ = ∑ x : α, deriv (fun t ↦ p θ x * Real.log (p θ x / p t x)) θ' := by
          simpa using hsum
    _ = ∑ x : α, (-(p θ x * (deriv (fun t ↦ p t x) θ' / p θ' x))) := by
          refine Finset.sum_congr rfl ?_
          intro x _hx
          simpa using (hderiv_term x)
    _ = -∑ x : α, p θ x * (deriv (fun t ↦ p t x) θ' / p θ' x) := by
          simp [Finset.sum_neg_distrib]

/-- The finite sum of coordinate derivative squares divided by their weights at one real
parameter. -/
noncomputable def fisherScore {α : Type*} [Fintype α] (p : ℝ → α → ℝ) (θ : ℝ) : ℝ :=
  ∑ x : α, (deriv (fun t ↦ p t x) θ) ^ 2 / p θ x

/-- The second derivative in the second parameter of the finite real logarithmic-ratio sum. -/
noncomputable def fisherKL {α : Type*} [Fintype α] (p : ℝ → α → ℝ) (θ : ℝ) : ℝ :=
  deriv (deriv (fun t ↦ klFiniteRealParam p θ t)) θ

/-- The two finite Fisher expressions agree under the explicit nonzero, normalization and
twice-differentiability hypotheses. -/
theorem fisherKL_eq_fisherScore
    {α : Type*} [Fintype α]
    (p : ℝ → α → ℝ) (θ : ℝ)
    (hp0 : ∀ t : ℝ, ∀ x : α, p t x ≠ 0)
    (hnorm : ∀ t : ℝ, (∑ x : α, p t x) = 1)
    (hp1 : ∀ x : α, Differentiable ℝ (fun t ↦ p t x))
    (hp2 : ∀ x : α, Differentiable ℝ (fun t ↦ deriv (fun u ↦ p u x) t)) :
    fisherKL p θ = fisherScore p θ := by
  classical
  -- Rewrite `deriv (klFiniteRealParam p θ ·)` as a concrete finite sum, pointwise in `t`.
  have hderivKL :
      deriv (fun t ↦ klFiniteRealParam p θ t) =
        fun t ↦ -∑ x : α, p θ x * (deriv (fun u ↦ p u x) t / p t x) := by
    funext t
    simpa using
      (deriv_klFiniteRealParam_second (p := p) (θ := θ) (θ' := t)
        (hpθ0 := hp0 θ) (hpθ'0 := hp0 t) (hp1 := fun x ↦ (hp1 x).differentiableAt))
  -- `∑x p_t(x) = 1` implies `∑x p''_θ(x) = 0`.
  have hsecond_sum :
      (∑ x : α, deriv (fun t ↦ deriv (fun u ↦ p u x) t) θ) = 0 := by
    -- First, `t ↦ ∑x p_t(x)` is constant.
    have hnormFun : (fun t ↦ (∑ x : α, p t x)) = fun _t : ℝ ↦ (1 : ℝ) := by
      funext t
      simp [hnorm]
    -- Differentiate once: `t ↦ ∑x p'_t(x)` is constantly `0`.
    have hsum_deriv_fun :
        (fun t ↦ ∑ x : α, deriv (fun u ↦ p u x) t) = fun _t : ℝ ↦ (0 : ℝ) := by
      funext t
      have hdiff : ∀ x : α, DifferentiableAt ℝ (fun s ↦ p s x) t :=
        fun x ↦ (hp1 x).differentiableAt
      have hsum :
          deriv (fun s ↦ (∑ x : α, p s x)) t = ∑ x : α, deriv (fun s ↦ p s x) t := by
        have hfun :
            (fun s ↦ ∑ x : α, p s x) = (∑ x : α, fun s ↦ p s x) := by
          funext s
          simp
        calc
          deriv (fun s ↦ (∑ x : α, p s x)) t
              = deriv (∑ x : α, fun s ↦ p s x) t := by
                simp [hfun]
          _ = ∑ x : α, deriv (fun s ↦ p s x) t := by
                simpa using
                  (deriv_sum (x := t) (u := Finset.univ)
                    (A := fun x : α ↦ fun s ↦ p s x)
                    (h := by
                      intro x _hx
                      exact hdiff x))
      -- Now use that `∑x p_t(x)` is constant.
      have hconst : deriv (fun s ↦ (∑ x : α, p s x)) t = 0 := by
        simp [hnormFun]
      simpa [hsum] using hconst
    -- Differentiate again at `θ`.
    have hsum'' :
        deriv (fun t ↦ (∑ x : α, deriv (fun u ↦ p u x) t)) θ =
          ∑ x : α, deriv (fun t ↦ deriv (fun u ↦ p u x) t) θ := by
      have hdiff : ∀ x : α, DifferentiableAt ℝ (fun t ↦ deriv (fun u ↦ p u x) t) θ :=
        fun x ↦ (hp2 x).differentiableAt
      have hfun :
          (fun t ↦ ∑ x : α, deriv (fun u ↦ p u x) t) =
            (∑ x : α, fun t ↦ deriv (fun u ↦ p u x) t) := by
        funext t
        simp
      calc
        deriv (fun t ↦ ∑ x : α, deriv (fun u ↦ p u x) t) θ
            = deriv (∑ x : α, fun t ↦ deriv (fun u ↦ p u x) t) θ := by
              simp [hfun]
        _ = ∑ x : α, deriv (fun t ↦ deriv (fun u ↦ p u x) t) θ := by
              simpa using
                (deriv_sum (x := θ) (u := Finset.univ)
                  (A := fun x : α ↦ fun t ↦ deriv (fun u ↦ p u x) t)
                  (h := by
                    intro x _hx
                    exact hdiff x))
    have hconst2 : deriv (fun t ↦ (∑ x : α, deriv (fun u ↦ p u x) t)) θ = 0 := by
      simp [hsum_deriv_fun]
    simpa [hsum''] using hconst2
  -- Compute `fisherKL` by differentiating the explicit derivative formula.
  have hkl'' :
      fisherKL p θ =
        -∑ x : α, p θ x * deriv (fun t ↦ deriv (fun u ↦ p u x) t / p t x) θ := by
    have hdiffQuot :
        ∀ x : α, DifferentiableAt ℝ (fun t ↦ deriv (fun u ↦ p u x) t / p t x) θ := by
      intro x
      have hnum : DifferentiableAt ℝ (fun t ↦ deriv (fun u ↦ p u x) t) θ :=
        (hp2 x).differentiableAt
      have hden : DifferentiableAt ℝ (fun t ↦ p t x) θ := (hp1 x).differentiableAt
      have hden0 : (fun t ↦ p t x) θ ≠ 0 := hp0 θ x
      exact hnum.div hden hden0
    have hderiv_sum :
        deriv (fun t ↦ ∑ x : α, p θ x * (deriv (fun u ↦ p u x) t / p t x)) θ =
          ∑ x : α, p θ x * deriv (fun t ↦ deriv (fun u ↦ p u x) t / p t x) θ := by
      have hdiffTerm :
          ∀ x : α, DifferentiableAt ℝ (fun t ↦ p θ x * (deriv (fun u ↦ p u x) t / p t x)) θ := by
        intro x
        simpa only [Pi.mul_def] using
          (differentiableAt_const (p θ x)).mul (hdiffQuot x)
      have hsum :
          deriv (∑ x : α, fun t ↦ p θ x * (deriv (fun u ↦ p u x) t / p t x)) θ =
            ∑ x : α, deriv (fun t ↦ p θ x * (deriv (fun u ↦ p u x) t / p t x)) θ := by
        simpa using
          (deriv_sum (x := θ) (u := Finset.univ)
            (A := fun x : α ↦ fun t ↦ p θ x * (deriv (fun u ↦ p u x) t / p t x))
            (h := by
              intro x _hx
              exact hdiffTerm x))
      have hfun :
          (fun t ↦ ∑ x : α, p θ x * (deriv (fun u ↦ p u x) t / p t x)) =
            (∑ x : α, fun t ↦ p θ x * (deriv (fun u ↦ p u x) t / p t x)) := by
        funext t
        simp
      calc
        deriv (fun t ↦ ∑ x : α, p θ x * (deriv (fun u ↦ p u x) t / p t x)) θ
            = deriv (∑ x : α, fun t ↦ p θ x * (deriv (fun u ↦ p u x) t / p t x)) θ := by
              simp [hfun]
        _ = ∑ x : α, deriv (fun t ↦ p θ x * (deriv (fun u ↦ p u x) t / p t x)) θ := by
              simpa using hsum
        _ = ∑ x : α, p θ x * deriv (fun t ↦ deriv (fun u ↦ p u x) t / p t x) θ := by
              refine Finset.sum_congr rfl ?_
              intro x _hx
              exact
                deriv_const_mul (c := p θ x)
                  (d := fun t ↦ deriv (fun u ↦ p u x) t / p t x) (x := θ) (hdiffQuot x)
    -- Put everything together.
    unfold fisherKL
    -- replace `deriv (fun t ↦ klFiniteRealParam p θ t)` using `hderivKL`.
    -- then differentiate the leading `-`.
    calc
      deriv (deriv (fun t ↦ klFiniteRealParam p θ t)) θ
          = deriv (fun t ↦ -∑ x : α, p θ x * (deriv (fun u ↦ p u x) t / p t x)) θ := by
            simp [hderivKL]
      _ = -deriv (fun t ↦ ∑ x : α, p θ x * (deriv (fun u ↦ p u x) t / p t x)) θ := by
            simp
      _ = -∑ x : α, p θ x * deriv (fun t ↦ deriv (fun u ↦ p u x) t / p t x) θ := by
            simp [hderiv_sum]
  -- Evaluate the inner derivative using the quotient rule.
  have hquot :
      ∀ x : α,
        deriv (fun t ↦ deriv (fun u ↦ p u x) t / p t x) θ =
          (deriv (fun t ↦ deriv (fun u ↦ p u x) t) θ * p θ x -
              deriv (fun t ↦ p t x) θ * deriv (fun t ↦ p t x) θ) / (p θ x) ^ 2 := by
    intro x
    have hnum : DifferentiableAt ℝ (fun t ↦ deriv (fun u ↦ p u x) t) θ := (hp2 x).differentiableAt
    have hden : DifferentiableAt ℝ (fun t ↦ p t x) θ := (hp1 x).differentiableAt
    have hden0 : (fun t ↦ p t x) θ ≠ 0 := hp0 θ x
    simpa only [Pi.div_def] using
      (deriv_div (c := fun t ↦ deriv (fun u ↦ p u x) t) (d := fun t ↦ p t x)
        (x := θ) hnum hden hden0)
  -- Final simplification using `∑ p'' = 0`.
  have hsummand :
      ∀ x : α,
        p θ x *
            ((deriv (fun t ↦ deriv (fun u ↦ p u x) t) θ * p θ x -
                deriv (fun t ↦ p t x) θ * deriv (fun t ↦ p t x) θ) / (p θ x) ^ 2) =
          deriv (fun t ↦ deriv (fun u ↦ p u x) t) θ -
            (deriv (fun t ↦ p t x) θ) ^ 2 / p θ x := by
    intro x
    have hpθx0 : p θ x ≠ 0 := hp0 θ x
    field_simp [hpθx0]
  calc
    fisherKL p θ
        = -∑ x : α, p θ x *
            ((deriv (fun t ↦ deriv (fun u ↦ p u x) t) θ * p θ x -
                deriv (fun t ↦ p t x) θ * deriv (fun t ↦ p t x) θ) / (p θ x) ^ 2) := by
          simp [hkl'', hquot]
    _ = -∑ x : α, (deriv (fun t ↦ deriv (fun u ↦ p u x) t) θ -
            (deriv (fun t ↦ p t x) θ) ^ 2 / p θ x) := by
          refine congrArg (fun z ↦ -z) ?_
          refine Finset.sum_congr rfl ?_
          intro x _hx
          simpa using (hsummand x)
    _ = fisherScore p θ := by
          -- Expand the sum and cancel `∑ p''` using `hsecond_sum`.
          have hsplit :
              -∑ x : α,
                  (deriv (fun t ↦ deriv (fun u ↦ p u x) t) θ -
                    (deriv (fun t ↦ p t x) θ) ^ 2 / p θ x) =
                -(∑ x : α, deriv (fun t ↦ deriv (fun u ↦ p u x) t) θ) +
                  ∑ x : α, (deriv (fun t ↦ p t x) θ) ^ 2 / p θ x := by
            classical
            calc
              -∑ x : α,
                  (deriv (fun t ↦ deriv (fun u ↦ p u x) t) θ -
                      (deriv (fun t ↦ p t x) θ) ^ 2 / p θ x)
                  = -∑ x : α,
                      (deriv (fun t ↦ deriv (fun u ↦ p u x) t) θ +
                        -((deriv (fun t ↦ p t x) θ) ^ 2 / p θ x)) := by
                      simp [sub_eq_add_neg]
              _ =
                  -((∑ x : α, deriv (fun t ↦ deriv (fun u ↦ p u x) t) θ) +
                    (∑ x : α, -((deriv (fun t ↦ p t x) θ) ^ 2 / p θ x))) := by
                      simp [Finset.sum_add_distrib]
              _ =
                  -((∑ x : α, deriv (fun t ↦ deriv (fun u ↦ p u x) t) θ) +
                    -∑ x : α, (deriv (fun t ↦ p t x) θ) ^ 2 / p θ x) := by
                      simp [Finset.sum_neg_distrib]
              _ =
                  -(∑ x : α, deriv (fun t ↦ deriv (fun u ↦ p u x) t) θ) +
                    ∑ x : α, (deriv (fun t ↦ p t x) θ) ^ 2 / p θ x := by
                      ring
          -- apply `hsecond_sum`
          simp [fisherScore, hsecond_sum]

end FisherInformation
