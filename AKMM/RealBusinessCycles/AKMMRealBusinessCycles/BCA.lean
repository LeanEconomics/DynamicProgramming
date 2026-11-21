/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoclassicalGrowth.RXCopied
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Business-cycle accounting

AKMM, §14.6, pp. 434–437 (Chari, Kehoe and McGrattan, 2007). The prototype economy has an
efficiency wedge `z` (`Y = zF(k, ℓ)`), a labour wedge `1 − τ^ℓ`, an investment wedge
`1/(1 + τ^i)` and a government-consumption wedge `g`.

* **The household's first-order conditions** with a labour-income tax `τ^ℓ` and an investment
  price `1 + τ^i`: `(1 − τ^ℓ)wU₁ = U₂` (`bca_labour_foc`, giving the modified (14.8) with
  `w = zF₂`) and the investment-wedge Euler equation
  `U₁(1 + τ^i) = βE[(r′ + (1 − δ)(1 + τ^i′))U₁′]` (`bca_investment_euler`, with `r′ = z′F₁′`).
* **Backing out the wedges**: for any allocation with `F(k, ℓ) > 0`, `F₂ > 0`, `U₁ > 0`, the
  wedges `z = Y/F`, `1 − τ^ℓ = (U₂/U₁)/(zF₂)`, `g = Y − c − i` make the allocation satisfy the
  wedge economy's production function, labour condition and resource constraint, and they are the
  only such wedges (`bca_static_wedges`, `bca_static_unique`).
* For the investment wedge, given `τ^i` today, a successor wedge (constant across next period's
  states) exists and is unique when `δ < 1` (`bca_investment_wedge`).
* With zero wedges (`τ^ℓ = τ^i = 0`, `g = 0`) the wedge conditions are the planner's (14.8) and
  (14.11) (`bca_zero_wedges`).
-/

namespace AKMM.RealBusinessCycles

open Filter Topology Miao.NeoclassicalGrowth

/-- **AKMM, p. 435, the labour wedge.** If hours `ℓ` maximise `U(c(ℓ′), 1 − ℓ′)` locally with
`c(ℓ′) = (1 − τ^ℓ)wℓ′ + m` and `U` has partials `(U₁, U₂)` at the optimum, then
`(1 − τ^ℓ)wU₁ = U₂`; with `w = zF₂(k, ℓ)` this is the modified (14.8)
`(1 − τ^ℓ)zF₂ = U₂/U₁`. -/
theorem bca_labour_foc {U : ℝ × ℝ → ℝ} {τl w m ℓ U1 U2 : ℝ}
    (hU : rx_HasPartials U U1 U2 ((1 - τl) * w * ℓ + m, 1 - ℓ))
    (hmax : IsLocalMax (fun x => U ((1 - τl) * w * x + m, 1 - x)) ℓ) :
    (1 - τl) * w * U1 = U2 ∧ (U1 ≠ 0 → (1 - τl) * w = U2 / U1) := by
  have hc : HasDerivAt (fun x => (1 - τl) * w * x + m) ((1 - τl) * w) ℓ := by
    simpa using ((hasDerivAt_id ℓ).const_mul ((1 - τl) * w)).add_const m
  have hx : HasDerivAt (fun x : ℝ => 1 - x) (-1) ℓ := by simpa using (hasDerivAt_id ℓ).const_sub 1
  have h0 := hmax.hasDerivAt_eq_zero (hU.comp hc hx)
  refine ⟨by linarith, fun h1 => ?_⟩
  rw [eq_div_iff h1]
  linarith

/-- **AKMM, p. 435, the investment-wedge Euler equation.** A household pays `1 + τ^i` per unit of
investment `i = k′ − (1 − δ)k`. Today `c = m₀ − (1 + τ^i)(k′ − (1 − δ)k)`; in state `s` tomorrow
(probability `pₛ`) `c′ₛ = mₛ + rₛk′ − (1 + τ^i′ₛ)(k″ₛ − (1 − δ)k′)`. If `k′` maximises
`u(c) + βΣₛpₛu(c′ₛ)` locally, with `u′(c) = U₁` and `u′(c′ₛ) = U₁′ₛ`, then
`U₁(1 + τ^i) = βΣₛpₛ(rₛ + (1 − δ)(1 + τ^i′ₛ))U₁′ₛ`. -/
theorem bca_investment_euler {S : Type*} [Fintype S] {u : ℝ → ℝ} {β δ τ m0 k kp U1 : ℝ}
    {p m r τ' k2 U1' : S → ℝ}
    (hu0 : HasDerivAt u U1 (m0 - (1 + τ) * (kp - (1 - δ) * k)))
    (hus : ∀ s, HasDerivAt u (U1' s) (m s + r s * kp - (1 + τ' s) * (k2 s - (1 - δ) * kp)))
    (hmax : IsLocalMax (fun x => u (m0 - (1 + τ) * (x - (1 - δ) * k)) +
      β * ∑ s, p s * u (m s + r s * x - (1 + τ' s) * (k2 s - (1 - δ) * x))) kp) :
    U1 * (1 + τ) = β * ∑ s, p s * ((r s + (1 - δ) * (1 + τ' s)) * U1' s) := by
  have hc0 : HasDerivAt (fun x => m0 - (1 + τ) * (x - (1 - δ) * k)) (-(1 + τ)) kp :=
    ((((hasDerivAt_id' kp).sub_const ((1 - δ) * k)).const_mul (1 + τ)).const_sub m0).congr_deriv
      (by ring)
  have hcs : ∀ s, HasDerivAt (fun x => m s + r s * x - (1 + τ' s) * (k2 s - (1 - δ) * x))
      (r s + (1 - δ) * (1 + τ' s)) kp := fun s =>
    ((((hasDerivAt_id' kp).const_mul (r s)).const_add (m s)).sub
      ((((hasDerivAt_id' kp).const_mul (1 - δ)).const_sub (k2 s)).const_mul (1 + τ' s))).congr_deriv
        (by ring)
  have hsum : HasDerivAt
      (fun x => ∑ s, p s * u (m s + r s * x - (1 + τ' s) * (k2 s - (1 - δ) * x)))
      (∑ s, p s * (U1' s * (r s + (1 - δ) * (1 + τ' s)))) kp :=
    HasDerivAt.fun_sum (u := Finset.univ) fun s _ => ((hus s).comp kp (hcs s)).const_mul (p s)
  have h0 := hmax.hasDerivAt_eq_zero ((hu0.comp kp hc0).add (hsum.const_mul β))
  have e : ∑ s, p s * (U1' s * (r s + (1 - δ) * (1 + τ' s))) =
      ∑ s, p s * ((r s + (1 - δ) * (1 + τ' s)) * U1' s) :=
    Finset.sum_congr rfl fun s _ => by ring
  rw [← e]
  linarith

/-- **AKMM, p. 435, backing out the static wedges.** For any allocation `(c, i, ℓ, k, Y)` with
`F(k, ℓ) > 0`, `F₂ ≠ 0` and `U₁ ≠ 0`, the efficiency wedge `z = Y/F(k, ℓ)`, the labour wedge
`1 − τ^ℓ = (U₂/U₁)/(zF₂)` and the government wedge `g = Y − c − i` satisfy `Y = zF(k, ℓ)`,
`(1 − τ^ℓ)zF₂ = U₂/U₁` and `c + i + g = Y`. -/
theorem bca_static_wedges {c i Y Fkl F2 U1 U2 : ℝ} (hF : 0 < Fkl) (hY : Y ≠ 0) (hF2 : F2 ≠ 0) :
    let z := Y / Fkl
    let τl := 1 - (U2 / U1) / (z * F2)
    let g := Y - c - i
    Y = z * Fkl ∧ (1 - τl) * z * F2 = U2 / U1 ∧ c + i + g = Y := by
  intro z τl g
  have hz : z ≠ 0 := div_ne_zero hY hF.ne'
  refine ⟨by simp only [z]; field_simp, ?_, by simp only [g]; ring⟩
  simp only [τl]
  field_simp
  ring

/-- AKMM, p. 435: the static wedges are determined by the allocation: if `(z, τ^ℓ, g)` make the
allocation satisfy the wedge conditions, they are the backed-out ones. -/
theorem bca_static_unique {c i Y Fkl F2 U1 U2 z τl g : ℝ} (hF : 0 < Fkl) (hz : z ≠ 0)
    (hF2 : F2 ≠ 0) (hprod : Y = z * Fkl) (hlab : (1 - τl) * z * F2 = U2 / U1)
    (hres : c + i + g = Y) :
    z = Y / Fkl ∧ τl = 1 - (U2 / U1) / (z * F2) ∧ g = Y - c - i := by
  refine ⟨by rw [hprod]; field_simp, ?_, by linarith⟩
  rw [← hlab]
  field_simp
  ring

/-- AKMM, p. 435: backing out the investment wedge. Given today's `1 + τ^i`, marginal utility
`U₁`, and next period's states `s` with probabilities `pₛ`, returns `rₛ` and marginal utilities
`U₁′ₛ` with `D = (1 − δ)Σₛ pₛU₁′ₛ ≠ 0`, the constant successor wedge
`1 + τ^i′ = (U₁(1 + τ^i)/β − Σₛ pₛrₛU₁′ₛ)/D` solves the investment-wedge Euler equation, and it
is the only constant successor wedge that does. -/
theorem bca_investment_wedge {S : Type*} [Fintype S] {β δ τ U1 : ℝ} {p r U1' : S → ℝ}
    (hβ : β ≠ 0) (hD : (1 - δ) * ∑ s, p s * U1' s ≠ 0) (x : ℝ) :
    U1 * (1 + τ) = β * ∑ s, p s * ((r s + (1 - δ) * x) * U1' s) ↔
      x = (U1 * (1 + τ) / β - ∑ s, p s * r s * U1' s) / ((1 - δ) * ∑ s, p s * U1' s) := by
  have e : ∑ s, p s * ((r s + (1 - δ) * x) * U1' s) =
      ∑ s, p s * r s * U1' s + x * ((1 - δ) * ∑ s, p s * U1' s) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e, eq_div_iff hD]
  constructor
  · intro h
    rw [h]
    field_simp
    ring
  · intro h
    have : x * ((1 - δ) * ∑ s, p s * U1' s) = U1 * (1 + τ) / β - ∑ s, p s * r s * U1' s := h
    field_simp at this ⊢
    linarith

/-- AKMM, pp. 435–436: with zero wedges the wedge conditions are the planner's: the labour
condition `(1 − 0)zF₂ = U₂/U₁` is (14.8) and the investment condition with `τ^i = τ^i′ = 0` is
(14.11). -/
theorem bca_zero_wedges {S : Type*} [Fintype S] {β δ z F2 U1 U2 : ℝ} {p r U1' : S → ℝ} :
    ((1 - 0) * z * F2 = U2 / U1 ↔ z * F2 = U2 / U1) ∧
      (U1 * (1 + 0) = β * ∑ s, p s * ((r s + (1 - δ) * (1 + 0)) * U1' s) ↔
        U1 = β * ∑ s, p s * ((r s + 1 - δ) * U1' s)) := by
  constructor
  · simp
  · simp only [add_zero, mul_one]
    constructor <;> intro h <;> rw [h] <;> congr 1 <;>
      exact Finset.sum_congr rfl fun s _ => by ring

end AKMM.RealBusinessCycles
