/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import NumericalMethods.NILegendre

/-!
# Laguerre polynomials (Miao, §11.3.1, p. 357)

The `n`th Laguerre polynomial is `Lₙ(x) = (eˣ/n!) dⁿ/dxⁿ (xⁿ e^{−x})`, `L₀ = 1`, on `[0, ∞)`,
with weighting function `w(x) = e^{−x}`.

* `ni_lagOp p = p' − p`: `d/dx (p(x) e^{−x}) = (p' − p)(x) e^{−x}`
  (`ni_hasDerivAt_poly_mul_exp_neg`), so `dᵏ/dxᵏ (p e^{−x}) = (lagOpᵏ p) e^{−x}`
  (`ni_iteratedDeriv_poly_mul_exp_neg`).
* `ni_laguerre n = (1/n!) lagOpⁿ Xⁿ`, with `ni_laguerre_eval_eq_rodrigues` (the book's formula),
  `ni_laguerre_zero` (`L₀ = 1`) and `ni_laguerre_natDegree_le` (`deg Lₙ ≤ n`).
* `ni_laguerre_weight`: `e^{−x}` is a weighting function on `(0, ∞)` (Definition 11.3.1).
* `ni_laguerre_orthogonal_low`, `ni_laguerre_orthogonal`: `Lₙ` is orthogonal to every
  polynomial of lower degree, hence the `Lₙ` are mutually orthogonal for the weight `e^{−x}`.
-/

open Polynomial MeasureTheory Filter Topology Real

namespace Miao.NumericalMethods

/-- `x ↦ xⁱ e^{−x}` is integrable on `(0, ∞)` (the Gamma integral). -/
theorem ni_integrableOn_pow_mul_exp_neg (i : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ i * exp (-x)) (Set.Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := (i : ℝ) + 1) (by positivity)
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [add_sub_cancel_right, Real.rpow_natCast]
  ring

/-- `x ↦ p(x) e^{−x}` is integrable on `(0, ∞)` for every polynomial `p`. -/
theorem ni_integrableOn_poly_mul_exp_neg (p : ℝ[X]) :
    IntegrableOn (fun x : ℝ => p.eval x * exp (-x)) (Set.Ioi 0) := by
  have e : (fun x : ℝ => p.eval x * exp (-x)) = fun x =>
      ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (x ^ i * exp (-x)) := by
    funext x
    rw [eval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e]
  exact integrable_finsetSum _ fun i _ => (ni_integrableOn_pow_mul_exp_neg i).const_mul _

/-- `p(x) e^{−x} → 0` as `x → ∞`. -/
theorem ni_tendsto_poly_mul_exp_neg (p : ℝ[X]) :
    Tendsto (fun x : ℝ => p.eval x * exp (-x)) atTop (𝓝 0) := by
  have e : (fun x : ℝ => p.eval x * exp (-x)) = fun x =>
      ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (x ^ i * exp (-x)) := by
    funext x
    rw [eval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e]
  have h := tendsto_finsetSum (Finset.range (p.natDegree + 1)) fun i _ =>
    (tendsto_pow_mul_exp_neg_atTop_nhds_zero i).const_mul (p.coeff i)
  simpa using h

/-- The operator `p ↦ p' − p`. -/
noncomputable def ni_lagOp (p : ℝ[X]) : ℝ[X] := derivative p - p

/-- `d/dx (p(x) e^{−x}) = (p' − p)(x) e^{−x}`. -/
theorem ni_hasDerivAt_poly_mul_exp_neg (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun y => p.eval y * exp (-y)) ((ni_lagOp p).eval x * exp (-x)) x := by
  have h := (Polynomial.hasDerivAt p x).mul (hasDerivAt_neg x).exp
  convert h using 1
  simp only [ni_lagOp, eval_sub]
  ring

/-- `dᵏ/dxᵏ (p(x) e^{−x}) = (lagOpᵏ p)(x) e^{−x}`. -/
theorem ni_iteratedDeriv_poly_mul_exp_neg (p : ℝ[X]) (k : ℕ) :
    iteratedDeriv k (fun x => p.eval x * exp (-x)) =
      fun x => (ni_lagOp^[k] p).eval x * exp (-x) := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ']
    have : deriv (fun x => p.eval x * exp (-x)) = fun x => (ni_lagOp p).eval x * exp (-x) := by
      funext x
      exact (ni_hasDerivAt_poly_mul_exp_neg p x).deriv
    rw [this, ih, Function.iterate_succ_apply]

/-- The `n`th Laguerre polynomial `Lₙ = (1/n!) lagOpⁿ Xⁿ` (Miao, p. 357). -/
noncomputable def ni_laguerre (n : ℕ) : ℝ[X] :=
  C (1 / (n.factorial : ℝ)) * ni_lagOp^[n] (X ^ n)

/-- Miao, p. 357 (Rodrigues' formula): `Lₙ(x) = (eˣ/n!) dⁿ/dxⁿ (xⁿ e^{−x})`. -/
theorem ni_laguerre_eval_eq_rodrigues (n : ℕ) (x : ℝ) :
    (ni_laguerre n).eval x =
      exp x / n.factorial * iteratedDeriv n (fun y => y ^ n * exp (-y)) x := by
  have : (fun y : ℝ => y ^ n * exp (-y)) = fun y => (X ^ n : ℝ[X]).eval y * exp (-y) := by
    funext y
    simp
  rw [this, ni_iteratedDeriv_poly_mul_exp_neg]
  simp only [ni_laguerre, eval_mul, eval_C]
  have hx : exp x * exp (-x) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
  calc 1 / (n.factorial : ℝ) * (ni_lagOp^[n] (X ^ n)).eval x
      = 1 / n.factorial * (ni_lagOp^[n] (X ^ n)).eval x * (exp x * exp (-x)) := by
        rw [hx, mul_one]
    _ = _ := by ring

/-- Miao, p. 357: `L₀(x) = 1`. -/
theorem ni_laguerre_zero : ni_laguerre 0 = 1 := by
  simp [ni_laguerre]

/-- `deg (p' − p) ≤ deg p`. -/
theorem ni_lagOp_natDegree_le (p : ℝ[X]) : (ni_lagOp p).natDegree ≤ p.natDegree :=
  (natDegree_sub_le _ _).trans (max_le (natDegree_derivative_le p |>.trans (Nat.sub_le _ _))
    le_rfl)

/-- The Laguerre polynomial `Lₙ` has degree at most `n`. -/
theorem ni_laguerre_natDegree_le (n : ℕ) : (ni_laguerre n).natDegree ≤ n := by
  unfold ni_laguerre
  refine (natDegree_C_mul_le _ _).trans ?_
  have : ∀ k (p : ℝ[X]), (ni_lagOp^[k] p).natDegree ≤ p.natDegree := by
    intro k
    induction k with
    | zero => intro p; simp
    | succ k ih =>
      intro p
      rw [Function.iterate_succ_apply']
      exact (ni_lagOp_natDegree_le _).trans (ih p)
  exact (this n _).trans (natDegree_X_pow_le n)

/-- **Definition 11.3.1** for the Laguerre weight (Miao, p. 357): `e^{−x}` is a weighting
function on `(0, ∞)`. -/
theorem ni_laguerre_weight : ni_IsWeightingFunction (fun x => exp (-x)) (Set.Ioi 0) :=
  ⟨fun x _ => exp_pos _, by simpa using ni_integrableOn_pow_mul_exp_neg 0⟩

/-- `∫_0^∞ (p' − p)(x) e^{−x} dx = −p(0)`. -/
theorem ni_integral_lagOp (p : ℝ[X]) :
    ∫ x in Set.Ioi (0 : ℝ), (ni_lagOp p).eval x * exp (-x) = -p.eval 0 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun y => p.eval y * exp (-y)) (m := 0)
    ((ni_hasDerivAt_poly_mul_exp_neg p 0).continuousAt.continuousWithinAt)
    (fun x _ => ni_hasDerivAt_poly_mul_exp_neg p x)
    (ni_integrableOn_poly_mul_exp_neg _) (ni_tendsto_poly_mul_exp_neg p)
  rw [h]
  simp

/-- `X^{j−l}` divides `lagOpˡ Xʲ`, so `(lagOpˡ Xʲ)(0) = 0` for `l < j`. -/
theorem ni_lagOp_iterate_eval_zero (j : ℕ) : ∀ l < j, (ni_lagOp^[l] (X ^ j)).eval 0 = 0 := by
  have hdvd : ∀ l ≤ j, (X : ℝ[X]) ^ (j - l) ∣ ni_lagOp^[l] (X ^ j) := by
    intro l
    induction l with
    | zero => intro _; simp
    | succ l ih =>
      intro hl
      obtain ⟨r, hr⟩ := ih (by omega)
      rw [Function.iterate_succ_apply', hr]
      have hk : j - l = (j - (l + 1)) + 1 := by omega
      rw [hk]
      refine ⟨((j - (l + 1) + 1 : ℕ) : ℝ[X]) * r + X * derivative r - X * r, ?_⟩
      simp only [ni_lagOp, derivative_mul, derivative_X_pow, Nat.add_sub_cancel, C_eq_natCast]
      push_cast
      ring
  intro l hl
  obtain ⟨r, hr⟩ := hdvd l hl.le
  rw [hr, eval_mul, eval_pow, eval_X, zero_pow (by omega), zero_mul]

/-- Repeated integration by parts on `(0, ∞)` with weight `e^{−x}`. -/
theorem ni_laguerre_parts (j : ℕ) : ∀ m ≤ j, ∀ q : ℝ[X],
    ∫ x in Set.Ioi (0 : ℝ), q.eval x * (ni_lagOp^[m] (X ^ j)).eval x * exp (-x) =
      (-1) ^ m * ∫ x in Set.Ioi (0 : ℝ), (derivative^[m] q).eval x * x ^ j * exp (-x) := by
  intro m
  induction m with
  | zero => intro _ q; simp
  | succ m ih =>
    intro hm q
    rw [Function.iterate_succ_apply']
    set t := ni_lagOp^[m] (X ^ j)
    have ht0 : t.eval 0 = 0 := ni_lagOp_iterate_eval_zero j m (by omega)
    have split : ∀ x, q.eval x * (ni_lagOp t).eval x * exp (-x) =
        (ni_lagOp (q * t)).eval x * exp (-x) - (derivative q).eval x * t.eval x * exp (-x) := by
      intro x
      simp only [ni_lagOp, eval_sub, eval_mul, derivative_mul, eval_add]
      ring
    simp_rw [split]
    rw [integral_sub (ni_integrableOn_poly_mul_exp_neg _), ni_integral_lagOp, eval_mul, ht0,
      mul_zero, neg_zero, zero_sub, ih (by omega), Function.iterate_succ_apply]
    · ring
    · have := ni_integrableOn_poly_mul_exp_neg (derivative q * t)
      simp only [eval_mul] at this
      exact this

/-- Miao, p. 357: `∫_0^∞ q(x) Lₙ(x) e^{−x} dx = 0` for every polynomial `q` of degree `< n`. -/
theorem ni_laguerre_orthogonal_low (n : ℕ) (q : ℝ[X]) (hq : q.natDegree < n) :
    ∫ x in Set.Ioi (0 : ℝ), q.eval x * (ni_laguerre n).eval x * exp (-x) = 0 := by
  have e : ∀ x, q.eval x * (ni_laguerre n).eval x * exp (-x) =
      1 / (n.factorial : ℝ) * (q.eval x * (ni_lagOp^[n] (X ^ n)).eval x * exp (-x)) := by
    intro x
    simp only [ni_laguerre, eval_mul, eval_C]
    ring
  simp_rw [e]
  rw [integral_const_mul, ni_laguerre_parts n n le_rfl, iterate_derivative_eq_zero hq]
  simp

/-- **Definition 11.3.1** applied to the Laguerre polynomials (Miao, p. 357): `Lᵢ` and `Lⱼ` are
orthogonal with respect to the weighting function `e^{−x}` on `[0, ∞)` for `i ≠ j`. -/
theorem ni_laguerre_orthogonal :
    ni_Orthogonal (fun x => exp (-x)) (Set.Ioi 0) (fun n x => (ni_laguerre n).eval x) := by
  intro i j hij
  unfold ni_inner
  rcases lt_or_gt_of_ne hij with h | h
  · exact ni_laguerre_orthogonal_low j _ ((ni_laguerre_natDegree_le i).trans_lt h)
  · refine Eq.trans ?_ (ni_laguerre_orthogonal_low i _ ((ni_laguerre_natDegree_le j).trans_lt h))
    congr 1
    funext x
    ring

end Miao.NumericalMethods
