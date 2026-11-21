/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMFiscalPolicy.Ramsey

/-!
# Time consistency of the Ramsey plan

AKMM, §15.5.2, pp. 461–462.

* "One parameter configuration that would deliver [saving] is `β(1 + r) = 1` … and `A₀ > A₁`": with
  CRRA the Ramsey Euler equation gives `c₀ = c₁` (`tc_cons_equal`); the Ramsey labour condition
  gives `A₀ℓ₀ > A₁ℓ₁` (`tc_output_order`); and then the household saves,
  `b₀ = (1 − τ)(A₀ℓ₀ − A₁ℓ₁)/(2 + r) > 0` (`tc_saves`).
* Re-optimisation at date 1, with the household's wealth `b₀` and the government's `b_{g,0}`
  given. Every date-1 competitive equilibrium lies on the resource line
  `c = A₁ℓ + (1 + r)(b₀ + b_{g,0}) − g₁` (`tc_ce_on_line`). Setting `τ₁ = 0` and
  `τ_{b,1} = (g₁ − (1 + r)b_{g,0})/(rb₀)` balances the budget and makes the household's budget line
  that resource line (`tc_household_line`): the tax on income from wealth is lump-sum. A
  maximiser on the line satisfies `−u_ℓ = A₁u_c` (`tc_foc_on_line`). So if the Ramsey plan has
  `τ₁ ≠ 0`, its date-1 allocation is strictly worse than what the re-optimising planner obtains
  with `τ₁ = 0` (`tc_time_inconsistent`): the plan is time inconsistent.

Correction: p. 461 says "household wealth `b₁` is already determined"; in the two-period model the
wealth carried into date 1 is `b₀`.
-/

namespace AKMM.FiscalPolicy

/-- AKMM, p. 461: with `β(1 + r) = 1`, the Ramsey Euler equation `β(1 + r)u_{c,1} = u_{c,0}` with
`u_c = c^{−σ}` (`σ > 0`) gives `c₀ = c₁`. -/
theorem tc_cons_equal {β r σ c0 c1 : ℝ} (hσ : 0 < σ) (hc0 : 0 < c0) (hc1 : 0 < c1)
    (hβr : β * (1 + r) = 1) (hE : β * (1 + r) * c1 ^ (-σ) = c0 ^ (-σ)) : c0 = c1 := by
  rw [hβr, one_mul] at hE
  have key : ∀ c : ℝ, 0 < c → (c ^ (-σ)) ^ (-(1 / σ)) = c := fun c hc => by
    rw [← Real.rpow_mul hc.le, show -σ * -(1 / σ) = 1 by field_simp, Real.rpow_one]
  rw [← key c0 hc0, ← key c1 hc1, hE]

/-- AKMM, p. 461: with `c₀ = c₁` (so `u_{c,0} = u_{c,1} = q > 0`), the Ramsey labour condition
`ℓ_t^{1/φ} = qA_tκ` (`κ = (1 + µ − µσ)/(1 + µ + µ/φ) > 0`) and `A₀ > A₁ > 0` give
`A₀ℓ₀ > A₁ℓ₁`. -/
theorem tc_output_order {φ q κ A0 A1 l0 l1 : ℝ} (hφ : 0 < φ) (hq : 0 < q) (hκ : 0 < κ)
    (hA1 : 0 < A1) (hA : A1 < A0) (hl0 : 0 < l0) (hl1 : 0 < l1)
    (h0 : l0 ^ (1 / φ) = q * A0 * κ) (h1 : l1 ^ (1 / φ) = q * A1 * κ) : A1 * l1 < A0 * l0 := by
  have key : ∀ l : ℝ, 0 < l → (l ^ (1 / φ)) ^ φ = l := fun l hl => by
    rw [← Real.rpow_mul hl.le, one_div_mul_cancel hφ.ne', Real.rpow_one]
  have hlt : l1 < l0 := by
    rw [← key l0 hl0, ← key l1 hl1, h0, h1]
    exact Real.rpow_lt_rpow (by positivity)
      (mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hA hq) hκ) hφ
  exact mul_lt_mul hA hlt.le hl1 (by linarith)

/-- AKMM, p. 461: "the household saves in period 0": with `c₀ = c₁`, `τ_{b,1} = 0`,
`τ₀ = τ₁ = τ < 1`, `2 + r > 0` and the household budgets, `b₀ = (1 − τ)(A₀ℓ₀ − A₁ℓ₁)/(2 + r)`,
positive when `A₀ℓ₀ > A₁ℓ₁`. -/
theorem tc_saves {A0 A1 r τ c0 c1 l0 l1 b0 : ℝ} (hr : 0 < 2 + r) (hτ : τ < 1)
    (hc : c0 = c1) (h0 : c0 = (1 - τ) * A0 * l0 - b0)
    (h1 : c1 = (1 - τ) * A1 * l1 + (1 + r * (1 - 0)) * b0) :
    b0 = (1 - τ) * (A0 * l0 - A1 * l1) / (2 + r) ∧ (A1 * l1 < A0 * l0 → 0 < b0) := by
  have hb : b0 = (1 - τ) * (A0 * l0 - A1 * l1) / (2 + r) := by
    rw [eq_div_iff hr.ne']
    linear_combination h0 - h1 - hc
  refine ⟨hb, fun h => ?_⟩
  rw [hb]
  exact div_pos (mul_pos (by linarith) (by linarith)) hr

/-- AKMM, p. 461: at date 1, with `b₀`, `b_{g,0}` given, any household budget
`c = (1 − τ₁)A₁ℓ + (1 + r(1 − τ_{b,1}))b₀` and government budget
`g₁ = τ₁A₁ℓ + τ_{b,1}rb₀ + (1 + r)b_{g,0}` put the allocation on the resource line
`c = A₁ℓ + (1 + r)(b₀ + b_{g,0}) − g₁`. -/
theorem tc_ce_on_line {A1 r g1 b0 bg0 τ1 τb c l : ℝ}
    (hh : c = (1 - τ1) * A1 * l + (1 + r * (1 - τb)) * b0)
    (hg : g1 = τ1 * A1 * l + τb * r * b0 + (1 + r) * bg0) :
    c = A1 * l + ((1 + r) * (b0 + bg0) - g1) := by
  rw [hh, hg]
  ring

/-- AKMM, p. 461: "such a planner would set `τ₁ = 0` and `τ_{b,1}` as high as necessary to fund
required government purchases": with `rb₀ ≠ 0`, `τ_{b,1} = (g₁ − (1 + r)b_{g,0})/(rb₀)` balances
the date-1 budget with `τ₁ = 0`, and the household's date-1 budget line is then exactly the
resource line (the wealth tax is lump-sum). -/
theorem tc_household_line {A1 r g1 b0 bg0 : ℝ} (hrb : r * b0 ≠ 0) :
    g1 = 0 * A1 * 1 + (g1 - (1 + r) * bg0) / (r * b0) * r * b0 + (1 + r) * bg0 ∧
      ∀ c l : ℝ, c = (1 - 0) * A1 * l + (1 + r * (1 - (g1 - (1 + r) * bg0) / (r * b0))) * b0 ↔
        c = A1 * l + ((1 + r) * (b0 + bg0) - g1) := by
  have hb : b0 ≠ 0 := right_ne_zero_of_mul hrb
  have hr : r ≠ 0 := left_ne_zero_of_mul hrb
  constructor
  · field_simp
    ring
  · intro c l
    have : (1 - 0) * A1 * l + (1 + r * (1 - (g1 - (1 + r) * bg0) / (r * b0))) * b0 =
        A1 * l + ((1 + r) * (b0 + bg0) - g1) := by
      field_simp
      ring
    rw [this]

/-- AKMM, p. 461: a maximiser of `u` on the resource line `c = A₁ℓ + M`, at which `u` is
differentiable, satisfies the undistorted condition `−u_ℓ = A₁u_c`. -/
theorem tc_foc_on_line {u : ℝ → ℝ → ℝ} {A1 M c l uc ul : ℝ} (hcl : c = A1 * l + M)
    (hmax : ∀ c' l', c' = A1 * l' + M → u c' l' ≤ u c l) (hu : DTPartials u c l uc ul) :
    -ul = A1 * uc := by
  have hd := dt_curve_hasDerivAt (h := fun ε => A1 * ε) (g := fun ε => ε) hu
    ((hasDerivAt_id 0).const_mul A1) (hasDerivAt_id 0) (by simp) rfl
  have hloc : IsLocalMax (fun ε => u (c + A1 * ε) (l + ε)) 0 :=
    Filter.Eventually.of_forall fun ε => by
      simp only [mul_zero, add_zero]
      exact hmax _ _ (by rw [hcl]; ring)
  have := hloc.hasDerivAt_eq_zero hd
  linarith

/-- **Time inconsistency** (AKMM, p. 461): if the Ramsey plan has `τ₁ ≠ 0`, its date-1 allocation
`(c₁, ℓ₁)` (on the resource line, with the household condition `u_{c,1}A₁(1 − τ₁) = −u_{ℓ,1}`,
`u_{c,1}, A₁ ≠ 0`, `u` differentiable there) is strictly worse than the household's optimum
`(c*, ℓ*)` under the re-optimised plan `τ₁ = 0` (whose budget line is the resource line). -/
theorem tc_time_inconsistent {u : ℝ → ℝ → ℝ} {A1 M c1 l1 uc1 ul1 τ1 cs ls : ℝ}
    (hline : c1 = A1 * l1 + M) (hfoc : uc1 * A1 * (1 - τ1) = -ul1) (hτ : τ1 ≠ 0)
    (huc : uc1 ≠ 0) (hA : A1 ≠ 0) (hu : DTPartials u c1 l1 uc1 ul1)
    (hopt : ∀ c l, c = A1 * l + M → u c l ≤ u cs ls) : u c1 l1 < u cs ls := by
  rcases (hopt c1 l1 hline).lt_or_eq with h | h
  · exact h
  · exfalso
    have hmax : ∀ c' l', c' = A1 * l' + M → u c' l' ≤ u c1 l1 := fun c' l' hc' => by
      rw [h]
      exact hopt c' l' hc'
    have := tc_foc_on_line hline hmax hu
    have h0 : uc1 * A1 * τ1 = 0 := by linear_combination -hfoc - this
    rcases mul_eq_zero.mp h0 with h' | h'
    · exact mul_ne_zero huc hA h'
    · exact hτ h'

end AKMM.FiscalPolicy
