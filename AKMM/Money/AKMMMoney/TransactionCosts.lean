/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Money reduces transactions costs

AKMM, §17.3.2, "Money reduces transactions costs", pp. 509–510. Purchases cost `ψ(x)c` with
`x = c/(M_{t+1}/P_t)` (consumption over real balances chosen at `t`) and `ψ(x) = κx^η`,
`κ, η > 0`.

* `tc_cost_homogeneous`: the cost `ψ(c/m)c` is homogeneous of degree one in `(c, m)`;
  `tc_psi_hasDerivAt`: `ψ′(x) = κηx^{η−1}`.
* `eq_17_28`: (17.26) and (17.27) give `1 − q_t/(p_{m,t}/p_{m,t+1}) = ψ′(x)x²`;
  `tc_fisher_lhs`: with the Fisher equation the left side is `i/(1 + i)`.
* `eq_17_29`: `M_{t+1}/P_t = c_t((1/(κη)) i_t/(1 + i_t))^{−1/(1+η)}`.
* `tc_demand_homogeneous`, `tc_demand_elasticity`, `tc_log_demand`: money demand is
  proportional to consumption and has the constant elasticity `−1/(1 + η)` with respect to the
  opportunity cost `i/(1 + i)`; `tc_demand_strictAntiOn`: it is decreasing in `i`.

The first-order conditions are taken as given, as in the book.
-/

namespace AKMM.Money

/-- AKMM, p. 510: the transaction-cost function `ψ(x) = κx^η`. -/
noncomputable def tcPsi (κ η x : ℝ) : ℝ := κ * x ^ η

/-- AKMM, p. 510: transactions costs `ψ(c/m)c` are homogeneous of degree one in consumption and
real balances jointly. -/
theorem tc_cost_homogeneous (κ η c m : ℝ) {k : ℝ} (hk : k ≠ 0) :
    tcPsi κ η (k * c / (k * m)) * (k * c) = k * (tcPsi κ η (c / m) * c) := by
  rw [mul_div_mul_left _ _ hk]; ring

/-- AKMM, p. 510: `ψ′(x) = κηx^{η−1}` for `x > 0`. -/
theorem tc_psi_hasDerivAt (κ η : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (tcPsi κ η) (κ * η * x ^ (η - 1)) x := by
  have := (Real.hasDerivAt_rpow_const (p := η) (Or.inl hx.ne')).const_mul κ
  refine this.congr_deriv ?_
  ring

/-- **AKMM, (17.28)**, p. 510: from the asset condition (17.26) `λ_tq_t = βλ_{t+1}` and the
money condition (17.27) `λ_t(p_{m,t}/p_{m,t+1})(1 − ψ′x²) = βλ_{t+1}`,
`1 − q_t/(p_{m,t}/p_{m,t+1}) = ψ′x²`. -/
theorem eq_17_28 {lam lam' q R D β : ℝ} (hlam : lam ≠ 0) (hR : R ≠ 0)
    (h26 : lam * q = β * lam') (h27 : lam * R * (1 - D) = β * lam') : 1 - q / R = D := by
  have : R * (1 - D) = q := mul_left_cancel₀ hlam (by rw [← mul_assoc, h27, h26])
  rw [← this]; field_simp; ring

/-- AKMM, p. 510: with the Fisher equation `q_t(1 + i_t) = p_{m,t}/p_{m,t+1}`, the left side of
(17.28) is the opportunity cost `i_t/(1 + i_t)`. -/
theorem tc_fisher_lhs {q i R : ℝ} (hi : 1 + i ≠ 0) (hq : q ≠ 0) (hF : q * (1 + i) = R) :
    1 - q / R = i / (1 + i) := by
  rw [← hF]; field_simp; ring

/-- AKMM, (17.29), p. 510: the money demand `M_{t+1}/P_t = c((1/(κη)) s)^{−1/(1+η)}` as a
function of consumption `c` and the opportunity cost `s = i/(1 + i)`. -/
noncomputable def tcDemand (κ η c s : ℝ) : ℝ := c * (1 / (κ * η) * s) ^ (-(1 / (1 + η)))

/-- **AKMM, (17.29)**, p. 510: with `ψ(x) = κx^η` and `x = c/m` (`m = M_{t+1}/P_t > 0`), the
condition (17.28) `i/(1 + i) = ψ′(x)x²` holds iff `m = c((1/(κη)) i/(1 + i))^{−1/(1+η)}`. -/
theorem eq_17_29 {κ η c m i : ℝ} (hκ : 0 < κ) (hη : 0 < η) (hc : 0 < c) (hm : 0 < m)
    (hi : 0 < i) :
    i / (1 + i) = κ * η * (c / m) ^ (η - 1) * (c / m) ^ 2 ↔ m = tcDemand κ η c (i / (1 + i)) := by
  set x := c / m with hx
  have hx0 : 0 < x := div_pos hc hm
  set s := i / (1 + i) with hs
  have hs0 : 0 < s := div_pos hi (by linarith)
  have hA : 0 < 1 / (κ * η) * s := by positivity
  have hpow : x ^ (η - 1) * x ^ 2 = x ^ (1 + η) := by
    rw [show (x ^ 2 : ℝ) = x ^ (2 : ℝ) by norm_cast, ← Real.rpow_add hx0]; ring_nf
  have h1η : (1 + η) ≠ 0 := by linarith
  rw [mul_assoc, hpow]
  unfold tcDemand
  constructor
  · intro h
    have hxA : x ^ (1 + η) = 1 / (κ * η) * s := by rw [h]; field_simp
    have hx' : x = (1 / (κ * η) * s) ^ (1 / (1 + η)) := by
      rw [← hxA, one_div, Real.rpow_rpow_inv hx0.le h1η]
    rw [Real.rpow_neg hA.le, ← hx', hx]
    field_simp
  · intro h
    have hx' : x = (1 / (κ * η) * s) ^ (1 / (1 + η)) := by
      rw [hx, h, Real.rpow_neg hA.le]
      have := Real.rpow_pos_of_pos hA (1 / (1 + η))
      field_simp
    rw [hx', ← Real.rpow_mul hA.le, one_div_mul_cancel h1η, Real.rpow_one]
    field_simp

/-- AKMM, p. 510: money demand is proportional to consumption (unit consumption elasticity). -/
theorem tc_demand_homogeneous (κ η c s k : ℝ) : tcDemand κ η (k * c) s = k * tcDemand κ η c s := by
  unfold tcDemand; ring

/-- AKMM, p. 510: the elasticity of money demand with respect to the opportunity cost
`s = i/(1 + i)` is the constant `−1/(1 + η)`: scaling `s` by `k > 0` scales demand by
`k^{−1/(1+η)}`. -/
theorem tc_demand_elasticity {κ η c s k : ℝ} (hκ : 0 < κ) (hη : 0 < η) (hs : 0 < s)
    (hk : 0 < k) : tcDemand κ η c (k * s) = k ^ (-(1 / (1 + η))) * tcDemand κ η c s := by
  unfold tcDemand
  rw [show 1 / (κ * η) * (k * s) = k * (1 / (κ * η) * s) by ring,
    Real.mul_rpow hk.le (by positivity)]
  ring

/-- AKMM, p. 510: in logarithms, `log m = log c − (1/(1 + η)) log(s/(κη))`, linear in `log s`
with slope `−1/(1 + η)`. -/
theorem tc_log_demand {κ η c s : ℝ} (hκ : 0 < κ) (hη : 0 < η) (hc : 0 < c) (hs : 0 < s) :
    Real.log (tcDemand κ η c s) =
      Real.log c - 1 / (1 + η) * (Real.log s - Real.log (κ * η)) := by
  unfold tcDemand
  have hA : 0 < 1 / (κ * η) * s := by positivity
  rw [Real.log_mul hc.ne' (Real.rpow_pos_of_pos hA _).ne', Real.log_rpow hA,
    Real.log_mul (by positivity) hs.ne', one_div (κ * η), Real.log_inv]
  ring

/-- AKMM, p. 510: real money demand is strictly decreasing in the nominal interest rate. -/
theorem tc_demand_strictAntiOn {κ η c : ℝ} (hκ : 0 < κ) (hη : 0 < η) (hc : 0 < c) :
    StrictAntiOn (fun i => tcDemand κ η c (i / (1 + i))) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  simp only [tcDemand]
  apply mul_lt_mul_of_pos_left _ hc
  apply Real.rpow_lt_rpow_of_neg (by positivity) _ (by
    have : 0 < 1 / (1 + η) := by positivity
    linarith)
  apply mul_lt_mul_of_pos_left _ (by positivity)
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  linarith

end AKMM.Money
