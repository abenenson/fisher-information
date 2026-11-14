/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import FisherInformation.ScoreFinite
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Fisher information of finite independent observations

Differentiating normalization centers the score. Consequently, the cross terms in the
score Fisher form of two independent observations vanish, even when both laws depend on
the same parameter. Iterating this identity gives linear scaling for a finite sample.

The algebraic results require nonzero atoms and Fréchet differentiability. Strictly
positive atoms give the usual statistical interpretation of the densities. The empty
sample has density one and Fisher information zero.

## Main results

- `sum_mul_scoreCLM_eq_zero`: the weighted score of a normalized finite law is zero.
- `scoreCLM_prod`: the score of a product law is the sum of its component scores.
- `fisherScoreBilin_prod`: information adds for two independent observations.
- `fisherScoreBilin_iid`: information of `n` independent copies is `n` times that of one.
-/

@[expose] public section

open scoped BigOperators

namespace FisherInformation.Fisher

variable {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
variable {α β : Type*}

/-- At a nonzero differentiable atom, its log-score is its relative derivative. -/
theorem scoreCLM_apply_eq_inv_mul_fderiv (p : Θ → α → ℝ) (θ v : Θ) (x : α)
    (hp0 : p θ x ≠ 0)
    (hdiff : DifferentiableAt ℝ (fun t ↦ p t x) θ) :
    scoreCLM p θ x v = (p θ x)⁻¹ * (fderiv ℝ (fun t ↦ p t x) θ) v := by
  have hlog :
      fderiv ℝ (fun t ↦ Real.log (p t x)) θ =
        (p θ x)⁻¹ • fderiv ℝ (fun t ↦ p t x) θ := by
    simpa using ((hdiff.hasFDerivAt.log hp0).fderiv)
  simp [scoreCLM, hlog, smul_eq_mul]

variable [Fintype α]

/-- The score has zero expectation when the finite density is normalized at every parameter.
The differentiability and nonzero hypotheses are needed only at `θ`. -/
theorem sum_mul_scoreCLM_eq_zero (p : Θ → α → ℝ) (θ v : Θ)
    (hp0 : ∀ x, p θ x ≠ 0)
    (hdiff : ∀ x, DifferentiableAt ℝ (fun t ↦ p t x) θ)
    (hnorm : ∀ t, ∑ x, p t x = 1) :
    ∑ x, p θ x * scoreCLM p θ x v = 0 := by
  have hsum : fderiv ℝ (fun t ↦ ∑ x, p t x) θ = 0 := by
    simp only [hnorm, fderiv_const_apply]
  rw [fderiv_fun_sum (fun x _ ↦ hdiff x)] at hsum
  have heval := congrArg (fun L : Θ →L[ℝ] ℝ ↦ L v) hsum
  simp only [sum_apply, zero_apply] at heval
  calc
    ∑ x, p θ x * scoreCLM p θ x v =
        ∑ x, (fderiv ℝ (fun t ↦ p t x) θ) v := by
      apply Finset.sum_congr rfl
      intro x _
      rw [scoreCLM_apply_eq_inv_mul_fderiv p θ v x (hp0 x) (hdiff x)]
      field_simp [hp0 x]
    _ = 0 := heval

omit [Fintype α] in
/-- The score of a product density is the sum of the two component scores. -/
theorem scoreCLM_prod (p : Θ → α → ℝ) (q : Θ → β → ℝ)
    (θ v : Θ) (x : α) (y : β)
    (hp0 : p θ x ≠ 0) (hq0 : q θ y ≠ 0)
    (hp : DifferentiableAt ℝ (fun t ↦ p t x) θ)
    (hq : DifferentiableAt ℝ (fun t ↦ q t y) θ) :
    scoreCLM (fun t (z : α × β) ↦ p t z.1 * q t z.2) θ (x, y) v =
      scoreCLM p θ x v + scoreCLM q θ y v := by
  rw [scoreCLM_apply_eq_inv_mul_fderiv _ θ v (x, y) (mul_ne_zero hp0 hq0)
      (hp.mul hq),
    scoreCLM_apply_eq_inv_mul_fderiv p θ v x hp0 hp,
    scoreCLM_apply_eq_inv_mul_fderiv q θ v y hq0 hq,
    fderiv_fun_mul hp hq]
  simp only [add_apply, smul_apply, smul_eq_mul]
  field_simp
  ring

variable [Fintype β]

/-- Fisher information adds for independent normalized finite observations that share a
parameter. The normalization identities hold at every parameter, while the other
hypotheses are local to `θ`. -/
theorem fisherScoreBilin_prod (p : Θ → α → ℝ) (q : Θ → β → ℝ)
    (θ u v : Θ)
    (hp0 : ∀ x, p θ x ≠ 0) (hq0 : ∀ y, q θ y ≠ 0)
    (hp : ∀ x, DifferentiableAt ℝ (fun t ↦ p t x) θ)
    (hq : ∀ y, DifferentiableAt ℝ (fun t ↦ q t y) θ)
    (hp_norm : ∀ t, ∑ x, p t x = 1)
    (hq_norm : ∀ t, ∑ y, q t y = 1) :
    fisherScoreBilin (fun t (z : α × β) ↦ p t z.1 * q t z.2) θ u v =
      fisherScoreBilin p θ u v + fisherScoreBilin q θ u v := by
  classical
  have hscore (x : α) (y : β) (w : Θ) :=
    scoreCLM_prod p q θ w x y (hp0 x) (hq0 y) (hp x) (hq y)
  simp only [fisherScoreBilin.apply, Fintype.sum_prod_type]
  simp_rw [hscore]
  calc
    _ = (∑ x, p θ x * scoreCLM p θ x u * scoreCLM p θ x v) * (∑ y, q θ y) +
        (∑ x, p θ x * scoreCLM p θ x u) * (∑ y, q θ y * scoreCLM q θ y v) +
        (∑ x, p θ x * scoreCLM p θ x v) * (∑ y, q θ y * scoreCLM q θ y u) +
        (∑ x, p θ x) * (∑ y, q θ y * scoreCLM q θ y u * scoreCLM q θ y v) := by
      simp only [Fintype.sum_mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = _ := by
      rw [hp_norm θ, hq_norm θ,
        sum_mul_scoreCLM_eq_zero p θ u hp0 hp hp_norm,
        sum_mul_scoreCLM_eq_zero p θ v hp0 hp hp_norm]
      ring

/-- The density of `n` independent copies of a finite observation. For `n = 0` this
is the constant density one on the unique empty sample. -/
def iidDensity (p : Θ → α → ℝ) (n : ℕ) : Θ → (Fin n → α) → ℝ :=
  fun θ xs ↦ ∏ i, p θ (xs i)

omit [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [Fintype α] in
/-- The empty observation has density one. -/
@[simp] theorem iidDensity_zero (p : Θ → α → ℝ) (θ : Θ) (xs : Fin 0 → α) :
    iidDensity p 0 θ xs = 1 := by
  simp [iidDensity]

omit [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [Fintype α] in
/-- Splitting the first observation factors the sample density. -/
@[simp] theorem iidDensity_succ_cons (p : Θ → α → ℝ) (n : ℕ) (θ : Θ)
    (x : α) (xs : Fin n → α) :
    iidDensity p (n + 1) θ (Fin.cons x xs) = p θ x * iidDensity p n θ xs := by
  simp [iidDensity, Fin.prod_univ_succ]

omit [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] in
/-- A globally normalized density gives a normalized law on each finite sample space. -/
theorem iidDensity_sum_eq_one (p : Θ → α → ℝ)
    (hnorm : ∀ θ, ∑ x, p θ x = 1) (n : ℕ) (θ : Θ) :
    ∑ xs : Fin n → α, iidDensity p n θ xs = 1 := by
  classical
  have h := Fintype.sum_pow (p θ) n
  rw [hnorm θ, one_pow] at h
  simpa only [iidDensity] using h.symm

omit [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [Fintype α] in
private theorem iidDensity_ne_zero (p : Θ → α → ℝ)
    (θ : Θ) (hp0 : ∀ x, p θ x ≠ 0) (n : ℕ) (xs : Fin n → α) :
    iidDensity p n θ xs ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun i _ ↦ hp0 (xs i))

omit [Fintype α] in
private theorem iidDensity_differentiableAt (p : Θ → α → ℝ)
    (θ : Θ) (hdiff : ∀ x, DifferentiableAt ℝ (fun t ↦ p t x) θ)
    (n : ℕ) (xs : Fin n → α) :
    DifferentiableAt ℝ (fun t ↦ iidDensity p n t xs) θ := by
  simpa only [iidDensity] using
    (HasFDerivAt.finsetProd (u := Finset.univ)
      (fun i _ ↦ (hdiff (xs i)).hasFDerivAt)).differentiableAt

/-- The empty sample has zero score Fisher information. -/
theorem fisherScoreBilin_iid_zero (p : Θ → α → ℝ) (θ u v : Θ) :
    fisherScoreBilin (iidDensity p 0) θ u v = 0 := by
  classical
  have hscore (xs : Fin 0 → α) (w : Θ) :
      scoreCLM (iidDensity p 0) θ xs w = 0 := by
    simp [scoreCLM]
  simp [fisherScoreBilin.apply, hscore]

/-- The information in `n` independent copies is `n` times the information in one.
Nonzero atoms and differentiability are needed only at `θ`; normalization holds at
every parameter. At `n = 0`, both sides are zero. -/
theorem fisherScoreBilin_iid (p : Θ → α → ℝ)
    (θ : Θ)
    (hp0 : ∀ x, p θ x ≠ 0)
    (hdiff : ∀ x, DifferentiableAt ℝ (fun t ↦ p t x) θ)
    (hnorm : ∀ t, ∑ x, p t x = 1)
    (n : ℕ) (u v : Θ) :
    fisherScoreBilin (iidDensity p n) θ u v =
      (n : ℝ) * fisherScoreBilin p θ u v := by
  classical
  induction n with
  | zero =>
    rw [fisherScoreBilin_iid_zero]
    simp
  | succ n ih =>
    let e : α × (Fin n → α) ≃ (Fin (n + 1) → α) :=
      Fin.consEquiv (fun _ ↦ α)
    have hmodel (z : α × (Fin n → α)) :
        iidDensity p (n + 1) θ (e z) = p θ z.1 * iidDensity p n θ z.2 := by
      change iidDensity p (n + 1) θ (Fin.cons z.1 z.2) = _
      exact iidDensity_succ_cons p n θ z.1 z.2
    have hscore (z : α × (Fin n → α)) (w : Θ) :
        scoreCLM (iidDensity p (n + 1)) θ (e z) w =
          scoreCLM (fun t (z : α × (Fin n → α)) ↦
            p t z.1 * iidDensity p n t z.2) θ z w := by
      have hf :
          (fun t ↦ Real.log (iidDensity p (n + 1) t (e z))) =
            (fun t ↦ Real.log (p t z.1 * iidDensity p n t z.2)) := by
        funext t
        change Real.log (iidDensity p (n + 1) t (Fin.cons z.1 z.2)) = _
        exact congrArg Real.log (iidDensity_succ_cons p n t z.1 z.2)
      simp only [scoreCLM, hf]
    have hreindex :
        fisherScoreBilin (iidDensity p (n + 1)) θ u v =
          fisherScoreBilin (fun t (z : α × (Fin n → α)) ↦
            p t z.1 * iidDensity p n t z.2) θ u v := by
      simp only [fisherScoreBilin.apply]
      exact (Fintype.sum_equiv e
        (fun z : α × (Fin n → α) ↦
          (p θ z.1 * iidDensity p n θ z.2) *
            scoreCLM (fun t (z : α × (Fin n → α)) ↦
              p t z.1 * iidDensity p n t z.2) θ z u *
            scoreCLM (fun t (z : α × (Fin n → α)) ↦
              p t z.1 * iidDensity p n t z.2) θ z v)
        (fun xs : Fin (n + 1) → α ↦
          iidDensity p (n + 1) θ xs *
            scoreCLM (iidDensity p (n + 1)) θ xs u *
            scoreCLM (iidDensity p (n + 1)) θ xs v)
        (by intro z; rw [hmodel, hscore z u, hscore z v])).symm
    rw [hreindex, fisherScoreBilin_prod p (iidDensity p n) θ u v
      hp0 (fun xs ↦ iidDensity_ne_zero p θ hp0 n xs)
      hdiff (fun xs ↦ iidDensity_differentiableAt p θ hdiff n xs)
      hnorm (iidDensity_sum_eq_one p hnorm n)]
    rw [ih]
    push_cast
    ring

end FisherInformation.Fisher
