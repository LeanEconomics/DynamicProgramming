/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import NumericalMethods.NILaguerre

/-!
# Hermite polynomials (Miao, §11.3.1, p. 357)

The `n`th Hermite polynomial is `Hₙ(x) = (−1)ⁿ e^{x²} dⁿ/dxⁿ e^{−x²}`, `H₀ = 1`, on `ℝ`, with
weighting function `w(x) = e^{−x²}` (the physicists' Hermite polynomials; Mathlib's `hermite`
are the probabilists' ones).

* `ni_hermOp p = p' − 2Xp`: `d/dx (p(x) e^{−x²}) = (p' − 2xp)(x) e^{−x²}`, and
  `ni_iteratedDeriv_poly_mul_exp_neg_sq`.
* `ni_hermite n = (−1)ⁿ hermOpⁿ 1`, with `ni_hermite_eval_eq_rodrigues` (the book's formula),
  `ni_hermite_zero` (`H₀ = 1`) and `ni_hermite_natDegree_le` (`deg Hₙ ≤ n`).
* `ni_hermite_weight`: `e^{−x²}` is a weighting function on `ℝ` (Definition 11.3.1).
* `ni_hermite_orthogonal_low`, `ni_hermite_orthogonal`: `Hₙ` is orthogonal to every polynomial
  of lower degree, hence the `Hₙ` are mutually orthogonal for the weight `e^{−x²}`.
-/

open Polynomial MeasureTheory Filter Topology Real

namespace Miao.NumericalMethods

/-- `x ↦ xⁱ e^{−x²}` is integrable on `ℝ`. -/
theorem ni_integrable_pow_mul_exp_neg_sq (i : ℕ) :
    Integrable (fun x : ℝ => x ^ i * exp (-x ^ 2)) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1) one_pos (s := (i : ℝ))
    (by have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith)
  refine h.congr (ae_of_all _ fun x => ?_)
  simp [Real.rpow_natCast]

/-- `x ↦ p(x) e^{−x²}` is integrable on `ℝ` for every polynomial `p`. -/
theorem ni_integrable_poly_mul_exp_neg_sq (p : ℝ[X]) :
    Integrable (fun x : ℝ => p.eval x * exp (-x ^ 2)) := by
  have e : (fun x : ℝ => p.eval x * exp (-x ^ 2)) = fun x =>
      ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (x ^ i * exp (-x ^ 2)) := by
    funext x
    rw [eval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e]
  exact integrable_finsetSum _ fun i _ => (ni_integrable_pow_mul_exp_neg_sq i).const_mul _

/-- `xⁱ e^{−x²} → 0` as `|x| → ∞`. -/
theorem ni_tendsto_pow_mul_exp_neg_sq (i : ℕ) :
    Tendsto (fun x : ℝ => x ^ i * exp (-x ^ 2)) (cocompact ℝ) (𝓝 0) := by
  have h := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (a := 1) one_pos (i : ℝ)
  refine squeeze_zero_norm (fun x => ?_) h
  rw [Real.norm_eq_abs, abs_mul, abs_pow, Real.rpow_natCast, abs_of_pos (exp_pos _)]
  simp

/-- `p(x) e^{−x²} → 0` as `|x| → ∞`. -/
theorem ni_tendsto_poly_mul_exp_neg_sq (p : ℝ[X]) :
    Tendsto (fun x : ℝ => p.eval x * exp (-x ^ 2)) (cocompact ℝ) (𝓝 0) := by
  have e : (fun x : ℝ => p.eval x * exp (-x ^ 2)) = fun x =>
      ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (x ^ i * exp (-x ^ 2)) := by
    funext x
    rw [eval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e]
  have h := tendsto_finsetSum (Finset.range (p.natDegree + 1)) fun i _ =>
    (ni_tendsto_pow_mul_exp_neg_sq i).const_mul (p.coeff i)
  simpa using h

/-- The operator `p ↦ p' − 2Xp`. -/
noncomputable def ni_hermOp (p : ℝ[X]) : ℝ[X] := derivative p - 2 * X * p

/-- `d/dx (p(x) e^{−x²}) = (p' − 2xp)(x) e^{−x²}`. -/
theorem ni_hasDerivAt_poly_mul_exp_neg_sq (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun y => p.eval y * exp (-y ^ 2)) ((ni_hermOp p).eval x * exp (-x ^ 2)) x := by
  have h := (Polynomial.hasDerivAt p x).mul ((hasDerivAt_pow 2 x).neg).exp
  convert h using 1
  simp only [ni_hermOp, eval_sub, eval_mul, eval_X, eval_ofNat, Pi.neg_apply]
  push_cast
  ring

/-- `dᵏ/dxᵏ (p(x) e^{−x²}) = (hermOpᵏ p)(x) e^{−x²}`. -/
theorem ni_iteratedDeriv_poly_mul_exp_neg_sq (p : ℝ[X]) (k : ℕ) :
    iteratedDeriv k (fun x => p.eval x * exp (-x ^ 2)) =
      fun x => (ni_hermOp^[k] p).eval x * exp (-x ^ 2) := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ']
    have : deriv (fun x => p.eval x * exp (-x ^ 2)) =
        fun x => (ni_hermOp p).eval x * exp (-x ^ 2) := by
      funext x
      exact (ni_hasDerivAt_poly_mul_exp_neg_sq p x).deriv
    rw [this, ih, Function.iterate_succ_apply]

/-- The `n`th Hermite polynomial `Hₙ = (−1)ⁿ hermOpⁿ 1` (Miao, p. 357). -/
noncomputable def ni_hermite (n : ℕ) : ℝ[X] :=
  C ((-1 : ℝ) ^ n) * ni_hermOp^[n] 1

/-- Miao, p. 357 (Rodrigues' formula): `Hₙ(x) = (−1)ⁿ e^{x²} dⁿ/dxⁿ e^{−x²}`. -/
theorem ni_hermite_eval_eq_rodrigues (n : ℕ) (x : ℝ) :
    (ni_hermite n).eval x = (-1) ^ n * exp (x ^ 2) * iteratedDeriv n (fun y => exp (-y ^ 2)) x := by
  have : (fun y : ℝ => exp (-y ^ 2)) = fun y => (1 : ℝ[X]).eval y * exp (-y ^ 2) := by
    funext y
    simp
  rw [this, ni_iteratedDeriv_poly_mul_exp_neg_sq]
  simp only [ni_hermite, eval_mul, eval_C]
  have hx : exp (x ^ 2) * exp (-x ^ 2) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
  calc (-1 : ℝ) ^ n * (ni_hermOp^[n] 1).eval x
      = (-1) ^ n * (ni_hermOp^[n] 1).eval x * (exp (x ^ 2) * exp (-x ^ 2)) := by
        rw [hx, mul_one]
    _ = _ := by ring

/-- Miao, p. 357: `H₀(x) = 1`. -/
theorem ni_hermite_zero : ni_hermite 0 = 1 := by
  simp [ni_hermite]

/-- `deg (p' − 2Xp) ≤ deg p + 1`. -/
theorem ni_hermOp_natDegree_le (p : ℝ[X]) : (ni_hermOp p).natDegree ≤ p.natDegree + 1 := by
  unfold ni_hermOp
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · exact (natDegree_derivative_le p).trans (by omega)
  · refine (natDegree_mul_le).trans ?_
    have : (2 * X : ℝ[X]).natDegree ≤ 1 := by
      refine (natDegree_mul_le).trans ?_
      simp
    omega

/-- The Hermite polynomial `Hₙ` has degree at most `n`. -/
theorem ni_hermite_natDegree_le (n : ℕ) : (ni_hermite n).natDegree ≤ n := by
  unfold ni_hermite
  refine (natDegree_C_mul_le _ _).trans ?_
  have : ∀ k, (ni_hermOp^[k] (1 : ℝ[X])).natDegree ≤ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact (ni_hermOp_natDegree_le _).trans (by omega)
  exact this n

/-- **Definition 11.3.1** for the Hermite weight (Miao, p. 357): `e^{−x²}` is a weighting
function on `ℝ`. -/
theorem ni_hermite_weight : ni_IsWeightingFunction (fun x => exp (-x ^ 2)) Set.univ :=
  ⟨fun x _ => exp_pos _, by simpa using ni_integrable_pow_mul_exp_neg_sq 0⟩

/-- `∫_ℝ (p' − 2xp)(x) e^{−x²} dx = 0`. -/
theorem ni_integral_hermOp (p : ℝ[X]) :
    ∫ x, (ni_hermOp p).eval x * exp (-x ^ 2) = 0 := by
  have h := integral_of_hasDerivAt_of_tendsto
    (f := fun y => p.eval y * exp (-y ^ 2)) (m := 0) (n := 0)
    (fun x => ni_hasDerivAt_poly_mul_exp_neg_sq p x)
    (ni_integrable_poly_mul_exp_neg_sq _)
    ((ni_tendsto_poly_mul_exp_neg_sq p).mono_left atBot_le_cocompact)
    ((ni_tendsto_poly_mul_exp_neg_sq p).mono_left atTop_le_cocompact)
  rw [h, sub_self]

/-- Repeated integration by parts on `ℝ` with weight `e^{−x²}`. -/
theorem ni_hermite_parts : ∀ m : ℕ, ∀ q : ℝ[X],
    ∫ x, q.eval x * (ni_hermOp^[m] 1).eval x * exp (-x ^ 2) =
      (-1) ^ m * ∫ x, (derivative^[m] q).eval x * exp (-x ^ 2) := by
  intro m
  induction m with
  | zero => intro q; simp
  | succ m ih =>
    intro q
    rw [Function.iterate_succ_apply']
    set t := ni_hermOp^[m] (1 : ℝ[X])
    have split : ∀ x, q.eval x * (ni_hermOp t).eval x * exp (-x ^ 2) =
        (ni_hermOp (q * t)).eval x * exp (-x ^ 2) -
          (derivative q).eval x * t.eval x * exp (-x ^ 2) := by
      intro x
      simp only [ni_hermOp, eval_sub, eval_mul, derivative_mul, eval_add]
      ring
    simp_rw [split]
    rw [integral_sub (ni_integrable_poly_mul_exp_neg_sq _), ni_integral_hermOp, zero_sub, ih,
      Function.iterate_succ_apply]
    · ring
    · have := ni_integrable_poly_mul_exp_neg_sq (derivative q * t)
      simp only [eval_mul] at this
      exact this

/-- Miao, p. 357: `∫_ℝ q(x) Hₙ(x) e^{−x²} dx = 0` for every polynomial `q` of degree `< n`. -/
theorem ni_hermite_orthogonal_low (n : ℕ) (q : ℝ[X]) (hq : q.natDegree < n) :
    ∫ x, q.eval x * (ni_hermite n).eval x * exp (-x ^ 2) = 0 := by
  have e : ∀ x, q.eval x * (ni_hermite n).eval x * exp (-x ^ 2) =
      (-1 : ℝ) ^ n * (q.eval x * (ni_hermOp^[n] 1).eval x * exp (-x ^ 2)) := by
    intro x
    simp only [ni_hermite, eval_mul, eval_C]
    ring
  simp_rw [e]
  rw [integral_const_mul, ni_hermite_parts n, iterate_derivative_eq_zero hq]
  simp

/-- **Definition 11.3.1** applied to the Hermite polynomials (Miao, p. 357): `Hᵢ` and `Hⱼ` are
orthogonal with respect to the weighting function `e^{−x²}` on `ℝ` for `i ≠ j`. -/
theorem ni_hermite_orthogonal :
    ni_Orthogonal (fun x => exp (-x ^ 2)) Set.univ (fun n x => (ni_hermite n).eval x) := by
  intro i j hij
  unfold ni_inner
  rw [setIntegral_univ]
  rcases lt_or_gt_of_ne hij with h | h
  · exact ni_hermite_orthogonal_low j _ ((ni_hermite_natDegree_le i).trans_lt h)
  · refine Eq.trans ?_ (ni_hermite_orthogonal_low i _ ((ni_hermite_natDegree_le j).trans_lt h))
    congr 1
    funext x
    ring

end Miao.NumericalMethods
