/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMFiscalPolicy.DistortionaryTaxes
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Ramsey taxation: the primal approach

AKMM, §15.5–15.5.1, (15.15)–(15.18), pp. 456–461.

Two periods, `y_t = A_tℓ_t`, `w_t = A_t` (15.15), storage at the exogenous rate `r`, government
spending `g₀, g₁`, a tax plan `(τ₀, τ₁, τ_{b,1})`. The marginal utilities at the allocation are
the numbers `u_{c,t}`, `u_{ℓ,t}`.

* A competitive equilibrium given the plan (`rmCE`) is, as on p. 459, the three household
  first-order conditions (15.16), the wages (15.15), and the household and government budgets.
  In a competitive equilibrium (15.18) holds (`eq_15_18`), and multiplying by `u_{c,0}` gives the
  implementability condition (`rmIC`).
* **The primal approach** (p. 459): an allocation is a competitive equilibrium for some tax plan
  iff it satisfies the resource constraint (15.17) (`rmRC`) and the implementability condition
  (`rm_primal`). The government's date-1 budget is implied by the others and (15.17) (Walras'
  law, `rm_walras`).
* The Lagrangian (`rmLagrangian`) and its four partial derivatives, which are the printed
  first-order conditions (`rm_foc_c0`, `rm_foc_l0`, `rm_foc_c1`, `rm_foc_l1`).
* Separable CRRA `u = c^{1−σ}/(1 − σ) − ℓ^{1+1/φ}/(1 + 1/φ)` (`rmU`): `u_c = c^{−σ}`,
  `u_ℓ = −ℓ^{1/φ}`, `u_{cc}c = −σu_c`, `u_{ℓℓ}ℓ = u_ℓ/φ` and no cross terms (`rm_crra_derivs`);
  the first-order conditions simplify as printed (`rm_crra_focs`); at a solution
  `β(1 + r)u_{c,1} = u_{c,0}` and `u_{c,t}A_t(1 + µ − µσ)/(1 + µ + µ/φ) = −u_{ℓ,t}`
  (`rm_crra_euler`, `rm_crra_labour`). Comparing with (15.16): `τ_{b,1} = 0` and
  `τ₀ = τ₁ = µ(σ + 1/φ)/(1 + µ + µ/φ)` (`rm_ramsey_taxes`).
* Sign of the tax (p. 461: positive "as long as either `g₀` or `g₁` is strictly positive"): from
  the government's budget, `τ` has the sign of the present value of spending when the present
  value of output is positive (`rm_tax_pos`); then `µ ≠ 0`, and `µ > 0` when
  `1 + µ + µ/φ > 0` or `σ ≥ 1` (`rm_mu_pos`).

Departures: the competitive equilibrium is characterised by first-order conditions, as the book
does on p. 459 (for concave `u` these are also sufficient for the household optimum, which we
do not restate). The existence of the multipliers `λ, µ` at a Ramsey optimum (a constraint
qualification) is assumed, as in the book: the Ramsey results are stated for allocations that
satisfy the printed first-order conditions with some `λ, µ`, with the interiority conditions
`1 + µ − µσ ≠ 0`, `1 + µ + µ/φ ≠ 0` explicit.
-/

namespace AKMM.FiscalPolicy

/-- The resource constraint (15.17), AKMM p. 459:
`c₀ + g₀ + (c₁ + g₁)/(1 + r) = A₀ℓ₀ + A₁ℓ₁/(1 + r)`. -/
def rmRC (A0 A1 r g0 g1 c0 l0 c1 l1 : ℝ) : Prop :=
  c0 + g0 + (c1 + g1) / (1 + r) = A0 * l0 + A1 * l1 / (1 + r)

/-- The implementability condition, AKMM p. 459:
`u_{c,0}c₀ + βu_{c,1}c₁ = −u_{ℓ,0}ℓ₀ − βu_{ℓ,1}ℓ₁`. -/
def rmIC (β uc0 ul0 uc1 ul1 c0 l0 c1 l1 : ℝ) : Prop :=
  uc0 * c0 + β * uc1 * c1 = -ul0 * l0 - β * ul1 * l1

/-- A competitive equilibrium given the tax plan `(τ₀, τ₁, τ_{b,1})` (AKMM, pp. 457–459): household
saving `b₀`, government saving `b_{g,0}`, the household budgets, the first-order conditions
(15.16) with wages `w_t = A_t` (15.15), and the government budgets. -/
def rmCE (β A0 A1 r g0 g1 uc0 ul0 uc1 ul1 c0 l0 c1 l1 τ0 τ1 τb b0 bg0 : ℝ) : Prop :=
  c0 = (1 - τ0) * A0 * l0 - b0 ∧ c1 = (1 - τ1) * A1 * l1 + (1 + r * (1 - τb)) * b0 ∧
    uc0 * A0 * (1 - τ0) = -ul0 ∧ uc1 * A1 * (1 - τ1) = -ul1 ∧
    uc0 = β * (1 + r * (1 - τb)) * uc1 ∧
    g0 + bg0 = τ0 * A0 * l0 ∧ g1 = τ1 * A1 * l1 + τb * r * b0 + (1 + r) * bg0

/-- AKMM, p. 459, **Walras' law**: the household budgets, the government's date-0 budget and the
resource constraint (15.17) imply the government's date-1 budget. -/
theorem rm_walras {A0 A1 r g0 g1 c0 l0 c1 l1 τ0 τ1 τb b0 bg0 : ℝ} (hr : 1 + r ≠ 0)
    (h0 : c0 = (1 - τ0) * A0 * l0 - b0)
    (h1 : c1 = (1 - τ1) * A1 * l1 + (1 + r * (1 - τb)) * b0)
    (hg0 : g0 + bg0 = τ0 * A0 * l0) (hRC : rmRC A0 A1 r g0 g1 c0 l0 c1 l1) :
    g1 = τ1 * A1 * l1 + τb * r * b0 + (1 + r) * bg0 := by
  unfold rmRC at hRC
  field_simp at hRC
  linear_combination hRC - (1 + r) * h0 - h1 - (1 + r) * hg0

/-- **(15.18)** (AKMM, p. 459): in a competitive equilibrium,
`c₀ + c₁/(u_{c,0}/(βu_{c,1})) =
−(u_{ℓ,0}/u_{c,0})ℓ₀ − (u_{ℓ,1}/u_{c,1})ℓ₁/(u_{c,0}/(βu_{c,1}))`, and
multiplying through by `u_{c,0}` gives the implementability condition. -/
theorem eq_15_18 {β A0 A1 r g0 g1 uc0 ul0 uc1 ul1 c0 l0 c1 l1 τ0 τ1 τb b0 bg0 : ℝ}
    (hβ : β ≠ 0) (huc0 : uc0 ≠ 0) (huc1 : uc1 ≠ 0)
    (h : rmCE β A0 A1 r g0 g1 uc0 ul0 uc1 ul1 c0 l0 c1 l1 τ0 τ1 τb b0 bg0) :
    c0 + c1 / (uc0 / (β * uc1)) = -(ul0 / uc0) * l0 - ul1 / uc1 * l1 / (uc0 / (β * uc1)) ∧
      rmIC β uc0 ul0 uc1 ul1 c0 l0 c1 l1 := by
  obtain ⟨h0, h1, hf0, hf1, he, -, -⟩ := h
  have hR : 1 + r * (1 - τb) = uc0 / (β * uc1) := by
    rw [he]
    field_simp
  have hw0 : (1 - τ0) * A0 = -(ul0 / uc0) := by
    field_simp
    linear_combination hf0
  have hw1 : (1 - τ1) * A1 = -(ul1 / uc1) := by
    field_simp
    linear_combination hf1
  have hpv : c0 + c1 / (1 + r * (1 - τb)) =
      (1 - τ0) * A0 * l0 + (1 - τ1) * A1 * l1 / (1 + r * (1 - τb)) := by
    have hRne : 1 + r * (1 - τb) ≠ 0 := by
      rw [hR]
      exact div_ne_zero huc0 (mul_ne_zero hβ huc1)
    rw [h1, h0]
    field_simp
    ring
  have h18 : c0 + c1 / (uc0 / (β * uc1)) =
      -(ul0 / uc0) * l0 - ul1 / uc1 * l1 / (uc0 / (β * uc1)) := by
    rw [← hR, hpv, hw0, hw1]
    ring
  refine ⟨h18, ?_⟩
  unfold rmIC
  field_simp at h18
  linear_combination h18

/-- **The primal approach** (AKMM, p. 459): "any allocation that satisfies the resource constraint
and the implementability condition can be implemented by some feasible tax plan", and
conversely. For `β, r, 1 + r, A₀, A₁, u_{c,0}, u_{c,1} ≠ 0`, an allocation `(c₀, ℓ₀, c₁, ℓ₁)` with
marginal utilities `u_{c,t}, u_{ℓ,t}` is a competitive equilibrium for some tax plan
`(τ₀, τ₁, τ_{b,1})` (and savings `b₀, b_{g,0}`) iff it satisfies (15.17) and the implementability
condition. -/
theorem rm_primal {β A0 A1 r g0 g1 uc0 ul0 uc1 ul1 c0 l0 c1 l1 : ℝ} (hβ : β ≠ 0) (hr : r ≠ 0)
    (hr1 : 1 + r ≠ 0) (hA0 : A0 ≠ 0) (hA1 : A1 ≠ 0) (huc0 : uc0 ≠ 0) (huc1 : uc1 ≠ 0) :
    (∃ τ0 τ1 τb b0 bg0, rmCE β A0 A1 r g0 g1 uc0 ul0 uc1 ul1 c0 l0 c1 l1 τ0 τ1 τb b0 bg0) ↔
      rmRC A0 A1 r g0 g1 c0 l0 c1 l1 ∧ rmIC β uc0 ul0 uc1 ul1 c0 l0 c1 l1 := by
  constructor
  · rintro ⟨τ0, τ1, τb, b0, bg0, h⟩
    refine ⟨?_, (eq_15_18 hβ huc0 huc1 h).2⟩
    obtain ⟨h0, h1, -, -, -, hg0, hg1⟩ := h
    unfold rmRC
    field_simp
    linear_combination (1 + r) * h0 + h1 + (1 + r) * hg0 + hg1
  · rintro ⟨hRC, hIC⟩
    set τ0 := 1 + ul0 / (uc0 * A0)
    set τ1 := 1 + ul1 / (uc1 * A1)
    set τb := 1 - (uc0 / (β * uc1) - 1) / r
    set b0 := (1 - τ0) * A0 * l0 - c0
    set bg0 := τ0 * A0 * l0 - g0
    have hR : 1 + r * (1 - τb) = uc0 / (β * uc1) := by
      simp only [τb]
      field_simp
      ring
    have hw0 : (1 - τ0) * A0 = -(ul0 / uc0) := by
      simp only [τ0]
      field_simp
      ring
    have hw1 : (1 - τ1) * A1 = -(ul1 / uc1) := by
      simp only [τ1]
      field_simp
      ring
    have h0 : c0 = (1 - τ0) * A0 * l0 - b0 := by simp only [b0]; ring
    have h1 : c1 = (1 - τ1) * A1 * l1 + (1 + r * (1 - τb)) * b0 := by
      simp only [b0]
      rw [hR, hw0, hw1]
      unfold rmIC at hIC
      field_simp
      linear_combination hIC
    have hg0 : g0 + bg0 = τ0 * A0 * l0 := by simp only [bg0]; ring
    refine ⟨τ0, τ1, τb, b0, bg0, h0, h1, ?_, ?_, ?_, hg0, rm_walras hr1 h0 h1 hg0 hRC⟩
    · rw [show uc0 * A0 * (1 - τ0) = uc0 * ((1 - τ0) * A0) by ring, hw0]
      field_simp
    · rw [show uc1 * A1 * (1 - τ1) = uc1 * ((1 - τ1) * A1) by ring, hw1]
      field_simp
    · rw [hR]
      field_simp

/-- The Lagrangian of the Ramsey problem (AKMM, p. 459), with marginal-utility functions
`uc`, `ul`. -/
noncomputable def rmLagrangian (u uc ul : ℝ → ℝ → ℝ) (β A0 A1 r g0 g1 lam mu c0 l0 c1 l1 : ℝ) :
    ℝ :=
  u c0 l0 + β * u c1 l1 + lam * (A0 * l0 + A1 * l1 / (1 + r) - c0 - g0 - (c1 + g1) / (1 + r)) +
    mu * (uc c0 l0 * c0 + β * uc c1 l1 * c1 + ul c0 l0 * l0 + β * ul c1 l1 * l1)

/-- AKMM, p. 460, first-order condition in `c₀`: `∂ℒ/∂c₀ = u_{c,0} − λ + µu_{c,0} + µu_{cc,0}c₀ +
µu_{ℓc,0}ℓ₀`. -/
theorem rm_foc_c0 {u uc ul : ℝ → ℝ → ℝ} {β A0 A1 r g0 g1 lam mu c0 l0 c1 l1 ucc ulc : ℝ}
    (hu : HasDerivAt (fun c => u c l0) (uc c0 l0) c0)
    (hucc : HasDerivAt (fun c => uc c l0) ucc c0) (hulc : HasDerivAt (fun c => ul c l0) ulc c0) :
    HasDerivAt (fun c => rmLagrangian u uc ul β A0 A1 r g0 g1 lam mu c l0 c1 l1)
      (uc c0 l0 - lam + mu * uc c0 l0 + mu * ucc * c0 + mu * ulc * l0) c0 := by
  unfold rmLagrangian
  have h1 := (hu.add_const (β * u c1 l1)).add
    (((hasDerivAt_id c0).const_sub (A0 * l0 + A1 * l1 / (1 + r))).sub_const
      (g0 + (c1 + g1) / (1 + r)) |>.const_mul lam)
  have h2 := (((hucc.mul (hasDerivAt_id c0)).add_const (β * uc c1 l1 * c1)).add
    ((hulc.mul_const l0))).add_const (β * ul c1 l1 * l1) |>.const_mul mu
  refine ((h1.add h2).congr_deriv (by simp; ring)).congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun c => by simp only [Pi.add_apply, Pi.mul_apply, id]; ring

/-- AKMM, p. 460, first-order condition in `ℓ₀`: `∂ℒ/∂ℓ₀ = u_{ℓ,0} + λA₀ + µu_{ℓ,0} + µu_{cℓ,0}c₀ +
µu_{ℓℓ,0}ℓ₀`. -/
theorem rm_foc_l0 {u uc ul : ℝ → ℝ → ℝ} {β A0 A1 r g0 g1 lam mu c0 l0 c1 l1 ucl ull : ℝ}
    (hu : HasDerivAt (fun l => u c0 l) (ul c0 l0) l0)
    (hucl : HasDerivAt (fun l => uc c0 l) ucl l0) (hull : HasDerivAt (fun l => ul c0 l) ull l0) :
    HasDerivAt (fun l => rmLagrangian u uc ul β A0 A1 r g0 g1 lam mu c0 l c1 l1)
      (ul c0 l0 + lam * A0 + mu * ul c0 l0 + mu * ucl * c0 + mu * ull * l0) l0 := by
  unfold rmLagrangian
  have h1 := (hu.add_const (β * u c1 l1)).add
    ((((hasDerivAt_id l0).const_mul A0).add_const (A1 * l1 / (1 + r))).sub_const
      (c0 + g0 + (c1 + g1) / (1 + r)) |>.const_mul lam)
  have h2 := (((hucl.mul_const c0).add_const (β * uc c1 l1 * c1)).add
    ((hull.mul (hasDerivAt_id l0)))).add_const (β * ul c1 l1 * l1) |>.const_mul mu
  refine ((h1.add h2).congr_deriv (by simp; ring)).congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun l => by simp only [Pi.add_apply, Pi.mul_apply, id]; ring

/-- AKMM, p. 460, first-order condition in `c₁`: `∂ℒ/∂c₁ = βu_{c,1} − λ/(1 + r) + βµu_{c,1} +
βµu_{cc,1}c₁ + βµu_{ℓc,1}ℓ₁`. -/
theorem rm_foc_c1 {u uc ul : ℝ → ℝ → ℝ} {β A0 A1 r g0 g1 lam mu c0 l0 c1 l1 ucc ulc : ℝ}
    (hu : HasDerivAt (fun c => u c l1) (uc c1 l1) c1)
    (hucc : HasDerivAt (fun c => uc c l1) ucc c1) (hulc : HasDerivAt (fun c => ul c l1) ulc c1) :
    HasDerivAt (fun c => rmLagrangian u uc ul β A0 A1 r g0 g1 lam mu c0 l0 c l1)
      (β * uc c1 l1 - lam / (1 + r) + β * mu * uc c1 l1 + β * mu * ucc * c1 +
        β * mu * ulc * l1) c1 := by
  unfold rmLagrangian
  have h1 := ((hu.const_mul β).const_add (u c0 l0)).add
    ((((hasDerivAt_id c1).add_const g1).div_const (1 + r)).const_sub
      (A0 * l0 + A1 * l1 / (1 + r) - c0 - g0) |>.const_mul lam)
  have h2 := ((((hucc.mul (hasDerivAt_id c1)).const_mul β).const_add (uc c0 l0 * c0)).add
    ((hulc.mul_const l1).const_mul β)).const_add (ul c0 l0 * l0) |>.const_mul mu
  refine ((h1.add h2).congr_deriv (by simp; ring)).congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun c => by simp only [Pi.add_apply, Pi.mul_apply, id]; ring

/-- AKMM, p. 460, first-order condition in `ℓ₁`: `∂ℒ/∂ℓ₁ = βu_{ℓ,1} + λA₁/(1 + r) + βµu_{ℓ,1} +
βµu_{cℓ,1}c₁ + βµu_{ℓℓ,1}ℓ₁`. -/
theorem rm_foc_l1 {u uc ul : ℝ → ℝ → ℝ} {β A0 A1 r g0 g1 lam mu c0 l0 c1 l1 ucl ull : ℝ}
    (hu : HasDerivAt (fun l => u c1 l) (ul c1 l1) l1)
    (hucl : HasDerivAt (fun l => uc c1 l) ucl l1) (hull : HasDerivAt (fun l => ul c1 l) ull l1) :
    HasDerivAt (fun l => rmLagrangian u uc ul β A0 A1 r g0 g1 lam mu c0 l0 c1 l)
      (β * ul c1 l1 + lam * A1 / (1 + r) + β * mu * ul c1 l1 + β * mu * ucl * c1 +
        β * mu * ull * l1) l1 := by
  unfold rmLagrangian
  have h1 := ((hu.const_mul β).const_add (u c0 l0)).add
    (((((hasDerivAt_id l1).const_mul A1).div_const (1 + r)).const_add (A0 * l0)).sub_const
      (c0 + g0 + (c1 + g1) / (1 + r)) |>.const_mul lam)
  have h2 := ((((hucl.mul_const c1).const_mul β).const_add (uc c0 l0 * c0)).add
    ((hull.mul (hasDerivAt_id l1)).const_mul β)).const_add (ul c0 l0 * l0) |>.const_mul mu
  refine ((h1.add h2).congr_deriv (by simp; ring)).congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun l => by simp only [Pi.add_apply, Pi.mul_apply, id]; ring

/-- Separable CRRA utility `c^{1−σ}/(1 − σ) − ℓ^{1+1/φ}/(1 + 1/φ)` (AKMM, p. 460). -/
noncomputable def rmU (σ φ c l : ℝ) : ℝ := c ^ (1 - σ) / (1 - σ) - l ^ (1 + 1 / φ) / (1 + 1 / φ)

/-- Its marginal utility of consumption `u_c = c^{−σ}`. -/
noncomputable def rmUc (σ : ℝ) (c _l : ℝ) : ℝ := c ^ (-σ)

/-- Its marginal utility of hours `u_ℓ = −ℓ^{1/φ}`. -/
noncomputable def rmUl (φ : ℝ) (_c l : ℝ) : ℝ := -l ^ (1 / φ)

/-- AKMM, p. 460: for separable CRRA at `c, ℓ > 0` (`σ ≠ 1`, `φ > 0`): `u_c = c^{−σ}`,
`u_ℓ = −ℓ^{1/φ}`, `u_{cc}c = −σu_c`, `u_{ℓℓ}ℓ = u_ℓ/φ`, and the cross derivatives vanish. -/
theorem rm_crra_derivs {σ φ c l : ℝ} (hσ : σ ≠ 1) (hφ : 0 < φ) (hc : 0 < c) (hl : 0 < l) :
    HasDerivAt (fun c => rmU σ φ c l) (rmUc σ c l) c ∧
      HasDerivAt (fun l => rmU σ φ c l) (rmUl φ c l) l ∧
      HasDerivAt (fun c => rmUc σ c l) (-σ * rmUc σ c l / c) c ∧
      HasDerivAt (fun l => rmUl φ c l) (rmUl φ c l / φ / l) l ∧
      HasDerivAt (fun l => rmUc σ c l) 0 l ∧ HasDerivAt (fun c => rmUl φ c l) 0 c := by
  have h1σ : (1 - σ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hσ)
  have hp : (1 + 1 / φ) ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_, ?_, hasDerivAt_const _ _, hasDerivAt_const _ _⟩
  · have h := ((Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hc.ne')).div_const
      (1 - σ)).sub_const (l ^ (1 + 1 / φ) / (1 + 1 / φ))
    refine h.congr_deriv ?_
    unfold rmUc
    rw [show 1 - σ - 1 = -σ by ring]
    field_simp
  · have h := ((Real.hasDerivAt_rpow_const (p := 1 + 1 / φ) (Or.inl hl.ne')).div_const
      (1 + 1 / φ)).const_sub (c ^ (1 - σ) / (1 - σ))
    refine h.congr_deriv ?_
    unfold rmUl
    rw [show 1 + 1 / φ - 1 = 1 / φ by ring]
    field_simp
  · have h := Real.hasDerivAt_rpow_const (p := -σ) (x := c) (Or.inl hc.ne')
    refine h.congr_deriv ?_
    unfold rmUc
    rw [Real.rpow_sub_one hc.ne']
    ring
  · have h := (Real.hasDerivAt_rpow_const (p := 1 / φ) (x := l) (Or.inl hl.ne')).neg
    refine h.congr_deriv ?_
    unfold rmUl
    rw [Real.rpow_sub_one hl.ne']
    ring

/-- AKMM, p. 460: with `u_{cc,t}c_t = −σu_{c,t}`, `u_{ℓℓ,t}ℓ_t = u_{ℓ,t}/φ` and no cross terms,
the four first-order conditions become `u_{c,0}(1 + µ − µσ) = λ`,
`u_{ℓ,0}(1 + µ + µ/φ) = −λA₀`, `βu_{c,1}(1 + µ − µσ) = λ/(1 + r)` and
`βu_{ℓ,1}(1 + µ + µ/φ) = −λA₁/(1 + r)`. -/
theorem rm_crra_focs {β A0 A1 r lam mu σ φ uc0 ul0 uc1 ul1 ucc0c0 ull0l0 ucc1c1 ull1l1 : ℝ}
    (hc0 : ucc0c0 = -σ * uc0) (hl0 : ull0l0 = ul0 / φ) (hc1 : ucc1c1 = -σ * uc1)
    (hl1 : ull1l1 = ul1 / φ)
    (f1 : uc0 - lam + mu * uc0 + mu * ucc0c0 + mu * 0 = 0)
    (f2 : ul0 + lam * A0 + mu * ul0 + mu * 0 + mu * ull0l0 = 0)
    (f3 : β * uc1 - lam / (1 + r) + β * mu * uc1 + β * mu * ucc1c1 + β * mu * 0 = 0)
    (f4 : β * ul1 + lam * A1 / (1 + r) + β * mu * ul1 + β * mu * 0 + β * mu * ull1l1 = 0) :
    uc0 * (1 + mu - mu * σ) = lam ∧ ul0 * (1 + mu + mu / φ) = -lam * A0 ∧
      β * uc1 * (1 + mu - mu * σ) = lam / (1 + r) ∧
      β * ul1 * (1 + mu + mu / φ) = -(lam * A1 / (1 + r)) := by
  subst hc0 hl0 hc1 hl1
  refine ⟨by linear_combination f1, by linear_combination f2, by linear_combination f3,
    by linear_combination f4⟩

/-- AKMM, p. 460: "Comparing the first and the third, it is immediate that, at an optimum
`β(1 + r)u_{c,1} = u_{c,0}`" (for `1 + µ − µσ ≠ 0`). -/
theorem rm_crra_euler {β r lam mu σ uc0 uc1 : ℝ} (hr : 1 + r ≠ 0) (hN : 1 + mu - mu * σ ≠ 0)
    (f1 : uc0 * (1 + mu - mu * σ) = lam) (f3 : β * uc1 * (1 + mu - mu * σ) = lam / (1 + r)) :
    β * (1 + r) * uc1 = uc0 := by
  have e : β * uc1 * (1 + mu - mu * σ) * (1 + r) = lam := by
    rw [f3]
    field_simp
  have : (β * (1 + r) * uc1 - uc0) * (1 + mu - mu * σ) = 0 := by
    linear_combination e - f1
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · exact absurd h hN

/-- AKMM, p. 460: "Comparing the first and the second, … `u_{c,0}A₀(1 + µ − µσ)/(1 + µ + µ/φ) =
−u_{ℓ,0}`"; similarly the third and fourth give the date-1 condition (for `1 + µ + µ/φ ≠ 0`,
`1 + r ≠ 0`, `β ≠ 0`). -/
theorem rm_crra_labour {β A0 A1 r lam mu σ φ uc0 ul0 uc1 ul1 : ℝ} (hβ : β ≠ 0)
    (hD : 1 + mu + mu / φ ≠ 0)
    (f1 : uc0 * (1 + mu - mu * σ) = lam) (f2 : ul0 * (1 + mu + mu / φ) = -lam * A0)
    (f3 : β * uc1 * (1 + mu - mu * σ) = lam / (1 + r))
    (f4 : β * ul1 * (1 + mu + mu / φ) = -(lam * A1 / (1 + r))) :
    uc0 * A0 * ((1 + mu - mu * σ) / (1 + mu + mu / φ)) = -ul0 ∧
      uc1 * A1 * ((1 + mu - mu * σ) / (1 + mu + mu / φ)) = -ul1 := by
  constructor
  · field_simp
    linear_combination A0 * f1 + f2
  · have : β * (uc1 * A1 * (1 + mu - mu * σ) + ul1 * (1 + mu + mu / φ)) = 0 := by
      have e1 : β * uc1 * (1 + mu - mu * σ) * A1 = lam / (1 + r) * A1 := by rw [f3]
      have e2 : lam / (1 + r) * A1 = lam * A1 / (1 + r) := by ring
      linear_combination e1 + f4 - e2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hβ
    · field_simp
      linear_combination h

/-- **The Ramsey taxes** (AKMM, p. 461): if the Ramsey allocation satisfies the household's
conditions (15.16) for the plan `(τ₀, τ₁, τ_{b,1})` and the CRRA conclusions
`β(1 + r)u_{c,1} = u_{c,0}`, `u_{c,t}A_t(1 + µ − µσ)/(1 + µ + µ/φ) = −u_{ℓ,t}`, then
`τ_{b,1} = 0` and `τ₀ = τ₁ = 1 − (1 + µ − µσ)/(1 + µ + µ/φ) = µ(σ + 1/φ)/(1 + µ + µ/φ)`
(for `r, β ≠ 0`, `u_{c,t}A_t ≠ 0`, `1 + µ + µ/φ ≠ 0`). -/
theorem rm_ramsey_taxes {β A0 A1 r mu σ φ uc0 ul0 uc1 ul1 τ0 τ1 τb : ℝ} (hr : r ≠ 0)
    (hβ : β ≠ 0) (h0 : uc0 * A0 ≠ 0) (h1 : uc1 * A1 ≠ 0) (huc1 : uc1 ≠ 0)
    (hD : 1 + mu + mu / φ ≠ 0)
    (e0 : uc0 * A0 * (1 - τ0) = -ul0) (e1 : uc1 * A1 * (1 - τ1) = -ul1)
    (eb : uc0 = β * (1 + r * (1 - τb)) * uc1) (eR : β * (1 + r) * uc1 = uc0)
    (l0 : uc0 * A0 * ((1 + mu - mu * σ) / (1 + mu + mu / φ)) = -ul0)
    (l1 : uc1 * A1 * ((1 + mu - mu * σ) / (1 + mu + mu / φ)) = -ul1) :
    τb = 0 ∧ τ0 = mu * (σ + 1 / φ) / (1 + mu + mu / φ) ∧
      τ1 = mu * (σ + 1 / φ) / (1 + mu + mu / φ) ∧
      1 - (1 + mu - mu * σ) / (1 + mu + mu / φ) = mu * (σ + 1 / φ) / (1 + mu + mu / φ) := by
  have hform : 1 - (1 + mu - mu * σ) / (1 + mu + mu / φ) =
      mu * (σ + 1 / φ) / (1 + mu + mu / φ) := by
    rw [eq_div_iff hD, sub_mul, div_mul_cancel₀ _ hD]
    ring
  refine ⟨?_, ?_, ?_, hform⟩
  · have : β * uc1 * (r * τb) = 0 := by linear_combination eR + eb
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (mul_ne_zero hβ huc1)
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hr
      · exact h'
  · rw [← hform]
    have : uc0 * A0 * ((1 - τ0) - (1 + mu - mu * σ) / (1 + mu + mu / φ)) = 0 := by
      linear_combination e0 - l0
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h h0
    · linarith
  · rw [← hform]
    have : uc1 * A1 * ((1 - τ1) - (1 + mu - mu * σ) / (1 + mu + mu / φ)) = 0 := by
      linear_combination e1 - l1
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h h1
    · linarith

/-- AKMM, p. 461: "the labor tax rate … will be positive as long as either `g₀` or `g₁` is
strictly positive": with `τ_{b,1} = 0` and `τ₀ = τ₁ = τ`, the government budgets give
`g₀ + g₁/(1 + r) = τ(A₀ℓ₀ + A₁ℓ₁/(1 + r))`, so if the present value of output is positive,
`τ > 0` iff the present value of spending is positive (`1 + r > 0`). -/
theorem rm_tax_pos {A0 A1 r g0 g1 l0 l1 τ b0 bg0 : ℝ} (hr : 0 < 1 + r)
    (hg0 : g0 + bg0 = τ * A0 * l0) (hg1 : g1 = τ * A1 * l1 + 0 * r * b0 + (1 + r) * bg0)
    (hY : 0 < A0 * l0 + A1 * l1 / (1 + r)) :
    g0 + g1 / (1 + r) = τ * (A0 * l0 + A1 * l1 / (1 + r)) ∧
      (0 < g0 + g1 / (1 + r) ↔ 0 < τ) := by
  have hpv : g0 + g1 / (1 + r) = τ * (A0 * l0 + A1 * l1 / (1 + r)) := by
    rw [hg1]
    field_simp
    linear_combination (1 + r) * hg0
  refine ⟨hpv, ?_⟩
  rw [hpv]
  exact ⟨fun h => pos_of_mul_pos_left h hY.le, fun h => mul_pos h hY⟩

/-- AKMM, p. 461, the sign of the multiplier: if the Ramsey tax
`τ = µ(σ + 1/φ)/(1 + µ + µ/φ)` lies in `(0, 1)` (positive by `rm_tax_pos`, below one by (15.16)
with `u_c > 0 > u_ℓ`), with `σ + 1/φ > 0`, then `µ ≠ 0`, and `µ > 0` if `1 + µ + µ/φ > 0` or
`σ ≥ 1`. -/
theorem rm_mu_pos {mu σ φ τ : ℝ} (hs : 0 < σ + 1 / φ) (hD : 1 + mu + mu / φ ≠ 0)
    (hτ : τ = mu * (σ + 1 / φ) / (1 + mu + mu / φ)) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    mu ≠ 0 ∧ (0 < 1 + mu + mu / φ ∨ 1 ≤ σ → 0 < mu) := by
  have hne : mu ≠ 0 := by
    rintro rfl
    rw [hτ] at hτ0
    simp at hτ0
  refine ⟨hne, ?_⟩
  rintro (hDpos | hσ)
  · rw [hτ, lt_div_iff₀ hDpos, zero_mul] at hτ0
    exact pos_of_mul_pos_left hτ0 hs.le
  · by_contra hmu
    push Not at hmu
    have hmu' : mu < 0 := lt_of_le_of_ne hmu hne
    rcases lt_or_gt_of_ne hD with hDneg | hDpos
    · -- `1 − τ = (1 + µ − µσ)/(1 + µ + µ/φ)` and `1 + µ − µσ ≥ 1`
      have h1 : 1 - τ = (1 + mu - mu * σ) / (1 + mu + mu / φ) := by
        rw [hτ, eq_div_iff hD, sub_mul, div_mul_cancel₀ _ hD]
        ring
      have hN : 1 ≤ 1 + mu - mu * σ := by nlinarith
      have : (1 + mu - mu * σ) / (1 + mu + mu / φ) < 0 := div_neg_of_pos_of_neg (by linarith) hDneg
      linarith
    · rw [hτ, lt_div_iff₀ hDpos, zero_mul] at hτ0
      have : mu * (σ + 1 / φ) < 0 := mul_neg_of_neg_of_pos hmu' hs
      linarith

end AKMM.FiscalPolicy
