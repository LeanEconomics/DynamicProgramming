/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The dividend-adjustment cost

AKMM, §19.4, Assumption 19.4.3 and the firm's problem (19.3), pp. 573–574.

To pay the dividend `d` the firm uses `ϕ(d) = d + κ(d − φ)²` units of resources (`cfPhi`), with
derivative `ϕ′(d) = 1 + 2κ(d − φ)` (`cfPhiD`, `div_hasDerivAt_phi`). For `κ ≥ 0` the largest
dividend that resources `X` can pay is the larger root of `ϕ(d) = X`,
`cfDiv X = φ + 2(X − φ)/(1 + √(1 + 4κ(X − φ)))` (also valid at `κ = 0`, where it is `X`):
`ϕ(cfDiv X) = X` when `1 + 4κ(X − φ) ≥ 0` (`div_phi_div`), every root is at most `cfDiv X`
(`div_le_div_of_phi`), `cfDiv ∘ ϕ = id` where `ϕ′ ≥ 0` (`div_div_phi`), and
`ϕ′(cfDiv X) = √(1 + 4κ(X − φ))` (`div_phiD_div`). Its derivative is `1/ϕ′` (by the inverse
function rule, `div_hasDerivAt_div`). On the region `ϕ′ > 0`, `ϕ` and `ϕ′` are increasing:
`ϕ(d₁) − ϕ(d₀) = (d₁ − d₀)(ϕ′(d₀) + ϕ′(d₁))/2` (`div_phi_sub`, `div_lt_of_phi_lt`,
`div_phiD_le`).
-/

namespace AKMM.CreditFrictions

open Filter Topology

/-- AKMM, p. 574: `ϕ(d) = d + κ(d − φ)²`, the resources needed to pay the dividend `d`
(Assumption 19.4.3, p. 573). -/
def cfPhi (κ φ d : ℝ) : ℝ := d + κ * (d - φ) ^ 2

/-- The derivative `ϕ′(d) = 1 + 2κ(d − φ)`. -/
def cfPhiD (κ φ d : ℝ) : ℝ := 1 + 2 * κ * (d - φ)

/-- The largest dividend payable out of resources `X`: the larger root of `ϕ(d) = X`. -/
noncomputable def cfDiv (κ φ X : ℝ) : ℝ :=
  φ + 2 * (X - φ) / (1 + Real.sqrt (1 + 4 * κ * (X - φ)))

/-- AKMM, p. 574: `ϕ′(d) = 1 + 2κ(d − φ)`. -/
theorem div_hasDerivAt_phi (κ φ d : ℝ) : HasDerivAt (cfPhi κ φ) (cfPhiD κ φ d) d := by
  have h1 : HasDerivAt (fun x : ℝ => x - φ) 1 d := (hasDerivAt_id d).sub_const φ
  have h2 := (hasDerivAt_id d).add ((h1.fun_pow 2).const_mul κ)
  unfold cfPhi cfPhiD
  convert h2 using 1
  · funext x
    simp only [Pi.add_apply, id]
  · norm_num
    ring

/-- `ϕ(d₁) − ϕ(d₀) = (d₁ − d₀)(ϕ′(d₀) + ϕ′(d₁))/2`. -/
theorem div_phi_sub (κ φ d₀ d₁ : ℝ) :
    cfPhi κ φ d₁ - cfPhi κ φ d₀ = (d₁ - d₀) * (cfPhiD κ φ d₀ + cfPhiD κ φ d₁) / 2 := by
  unfold cfPhi cfPhiD
  ring

/-- `ϕ′(d₁) − ϕ′(d₀) = 2κ(d₁ − d₀)`. -/
theorem div_phiD_sub (κ φ d₀ d₁ : ℝ) :
    cfPhiD κ φ d₁ - cfPhiD κ φ d₀ = 2 * κ * (d₁ - d₀) := by
  unfold cfPhiD
  ring

/-- `ϕ′` is increasing for `κ ≥ 0`. -/
theorem div_phiD_le {κ φ d₀ d₁ : ℝ} (hκ : 0 ≤ κ) (h : d₀ ≤ d₁) :
    cfPhiD κ φ d₀ ≤ cfPhiD κ φ d₁ := by
  have := div_phiD_sub κ φ d₀ d₁
  nlinarith

/-- Where `ϕ′ > 0`, `ϕ` is strictly increasing: `ϕ(d₁) < ϕ(d₀)` forces `d₁ < d₀`. -/
theorem div_lt_of_phi_lt {κ φ d₀ d₁ : ℝ} (h₀ : 0 < cfPhiD κ φ d₀) (h₁ : 0 < cfPhiD κ φ d₁)
    (h : cfPhi κ φ d₁ < cfPhi κ φ d₀) : d₁ < d₀ := by
  have e := div_phi_sub κ φ d₀ d₁
  by_contra hc
  have : 0 ≤ (d₁ - d₀) * (cfPhiD κ φ d₀ + cfPhiD κ φ d₁) :=
    mul_nonneg (by linarith) (by linarith)
  linarith

/-- The radicand at `ϕ(d)` is a square: `1 + 4κ(ϕ(d) − φ) = ϕ′(d)²`. -/
theorem div_radicand_phi (κ φ d : ℝ) :
    1 + 4 * κ * (cfPhi κ φ d - φ) = cfPhiD κ φ d ^ 2 := by
  unfold cfPhi cfPhiD
  ring

/-- `ϕ(cfDiv X) = X` when `1 + 4κ(X − φ) ≥ 0`. -/
theorem div_phi_div {κ φ X : ℝ} (h : 0 ≤ 1 + 4 * κ * (X - φ)) :
    cfPhi κ φ (cfDiv κ φ X) = X := by
  set s := Real.sqrt (1 + 4 * κ * (X - φ)) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = 1 + 4 * κ * (X - φ) := Real.sq_sqrt h
  have hd : (1 + s) ≠ 0 := by positivity
  unfold cfPhi cfDiv
  rw [← hs]
  field_simp
  linear_combination (-(X - φ)) * hss

/-- `ϕ′(cfDiv X) = √(1 + 4κ(X − φ))` when `1 + 4κ(X − φ) ≥ 0`. -/
theorem div_phiD_div {κ φ X : ℝ} (h : 0 ≤ 1 + 4 * κ * (X - φ)) :
    cfPhiD κ φ (cfDiv κ φ X) = Real.sqrt (1 + 4 * κ * (X - φ)) := by
  set s := Real.sqrt (1 + 4 * κ * (X - φ)) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = 1 + 4 * κ * (X - φ) := Real.sq_sqrt h
  have hd : (1 + s) ≠ 0 := by positivity
  unfold cfPhiD cfDiv
  rw [← hs]
  field_simp
  linear_combination -hss

/-- `cfDiv (ϕ(d)) = d` where `ϕ′(d) ≥ 0`. -/
theorem div_div_phi {κ φ d : ℝ} (h : 0 ≤ cfPhiD κ φ d) : cfDiv κ φ (cfPhi κ φ d) = d := by
  have hr := div_radicand_phi κ φ d
  have hs : Real.sqrt (1 + 4 * κ * (cfPhi κ φ d - φ)) = cfPhiD κ φ d := by
    rw [hr, Real.sqrt_sq h]
  unfold cfDiv
  rw [hs]
  have hd : 1 + cfPhiD κ φ d ≠ 0 := by linarith
  field_simp
  unfold cfPhi cfPhiD
  ring

/-- Every `d` with `ϕ(d) = X` is at most `cfDiv X` (`κ ≥ 0`): the firm pays the larger root. -/
theorem div_le_div_of_phi {κ φ d X : ℝ} (hκ : 0 ≤ κ) (h : cfPhi κ φ d = X) :
    d ≤ cfDiv κ φ X := by
  have hrad : 0 ≤ 1 + 4 * κ * (X - φ) := by
    rw [← h, div_radicand_phi]
    positivity
  have h1 := div_phi_div hrad
  have h2 := div_phiD_div hrad
  have e := div_phi_sub κ φ (cfDiv κ φ X) d
  rw [h1, h] at e
  have es := div_phiD_sub κ φ (cfDiv κ φ X) d
  by_contra hc
  push Not at hc
  have hs0 : 0 ≤ Real.sqrt (1 + 4 * κ * (X - φ)) := Real.sqrt_nonneg _
  have hk : 0 ≤ κ * (d - cfDiv κ φ X) := mul_nonneg hκ (by linarith)
  have hsum : 0 < cfPhiD κ φ (cfDiv κ φ X) + cfPhiD κ φ d := by
    rcases hκ.lt_or_eq with hκ' | hκ'
    · have : 0 < κ * (d - cfDiv κ φ X) := mul_pos hκ' (by linarith)
      linarith
    · unfold cfPhiD
      rw [← hκ']
      norm_num
  have : (d - cfDiv κ φ X) * (cfPhiD κ φ (cfDiv κ φ X) + cfPhiD κ φ d) = 0 := by linarith
  rcases mul_eq_zero.1 this with h0 | h0
  · linarith
  · linarith

/-- `cfDiv` is continuous (the denominator is at least `1`). -/
theorem div_continuous (κ φ : ℝ) : Continuous (cfDiv κ φ) := by
  unfold cfDiv
  refine continuous_const.add (Continuous.div (by fun_prop) (by fun_prop) fun X => ?_)
  have := Real.sqrt_nonneg (1 + 4 * κ * (X - φ))
  positivity

/-- The derivative of the dividend in the resources is `1/ϕ′`: where `1 + 4κ(X − φ) > 0`,
`cfDiv′(X) = 1/√(1 + 4κ(X − φ)) = 1/ϕ′(cfDiv X)`. -/
theorem div_hasDerivAt_div {κ φ X : ℝ} (h : 0 < 1 + 4 * κ * (X - φ)) :
    HasDerivAt (cfDiv κ φ) (cfPhiD κ φ (cfDiv κ φ X))⁻¹ X := by
  refine HasDerivAt.of_local_left_inverse (div_continuous κ φ).continuousAt
    (div_hasDerivAt_phi κ φ _) ?_ ?_
  · rw [div_phiD_div h.le]
    exact (Real.sqrt_pos.2 h).ne'
  · have hc : Continuous fun y : ℝ => 1 + 4 * κ * (y - φ) := by fun_prop
    filter_upwards [hc.continuousAt.eventually_const_lt h] with y hy
    exact div_phi_div hy.le

end AKMM.CreditFrictions
