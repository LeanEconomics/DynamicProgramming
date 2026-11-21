/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMLaborSupply.Dynamic
import NeoclassicalGrowth.RBModel
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# A simple business-cycle model

AKMM, §14.4.1, (14.2)–(14.7), pp. 420–422. The period utility of (14.2), `ln c + φ ln(1 − ℓ)`, is
Miao's `rb_u φ` (Chapter 14 of Miao, imported); production is `Y = zℓ` (14.3), the budget is
`c + B = wℓ + RB₋₁` (14.4).

* The firm: with linear technology, a profit-maximising firm employing `ℓ > 0` pays `w = z`
  (`sm_wage`).
* **(14.5)**: at an interior optimum of `ℓ ↦ ln(wℓ + m) + φ ln(1 − ℓ)` (`m = RB₋₁ − B`),
  `w/c = φ/(1 − ℓ)` (`eq_14_5`); conversely (14.5) makes `ℓ` a global maximiser
  (`sm_static_suff`, via Miao's tangent inequality `rb_u_tangent`).
* **(14.6)**: at an interior optimum of the bond choice, `1/c = βΣₛ pₛRₛ/c′ₛ` (`eq_14_6`).
* **(14.7)**: with `B = 0`, (14.5) becomes `φ/(1 − ℓ) = 1/ℓ`, so `ℓ = 1/(1 + φ)` (`eq_14_7`).
* Equilibrium (`sm_equilibrium`): hours `1/(1 + φ)` whatever `z`, and `c = Y = z/(1 + φ)`, so
  output, consumption and TFP are perfectly correlated.
* The interest rate: with `zₜ₊₁ = zₜ^ρ e^{εₛ}` (finitely many shocks), the Euler equation at
  `B = 0` gives `R = zₜ^{ρ−1}/(βΣ pₛe^{−εₛ})`, which falls when TFP rises if `ρ < 1`
  (`sm_interest_rate`, `sm_interest_rate_falls`).
* The Frisch elasticity of log–log preferences is `(1 − ℓ)/ℓ` (`sm_frisch`, through AKMM
  Chapter 12's `frischF`; also `sm_frisch_cd` from Chapter 12's `dyn_frisch_cd` at `σ = 1`), and
  `2` at `ℓ = 1/3` (`sm_frisch_two`); holding the marginal utility `λ` fixed, hours
  `ℓ(w) = 1 − φ/(λw)` respond to the wage with elasticity `(1 − ℓ)/ℓ` (`sm_frisch_response`).
-/

namespace AKMM.RealBusinessCycles

open Filter Topology Miao.NeoclassicalGrowth

/-- AKMM, p. 420: "perfect competition and linear production … imply that the equilibrium wage
will be equal to TFP, `w = z`": if employing `ℓ > 0` maximises the profit `(z − w)ℓ'` over
`ℓ' ≥ 0`, then `w = z`. -/
theorem sm_wage {z w ℓ : ℝ} (hℓ : 0 < ℓ) (hmax : ∀ ℓ', 0 ≤ ℓ' → (z - w) * ℓ' ≤ (z - w) * ℓ) :
    w = z := by
  have h0 := hmax 0 le_rfl
  have h2 := hmax (2 * ℓ) (by linarith)
  nlinarith

/-- The derivative of the static objective `ℓ ↦ ln(wℓ + m) + φ ln(1 − ℓ)`. -/
theorem sm_static_deriv {φ w m ℓ : ℝ} (hc : 0 < w * ℓ + m) (hℓ : ℓ < 1) :
    HasDerivAt (fun x => Real.log (w * x + m) + φ * Real.log (1 - x))
      (w / (w * ℓ + m) - φ / (1 - ℓ)) ℓ := by
  have h1 : HasDerivAt (fun x => w * x + m) w ℓ := by
    simpa using ((hasDerivAt_id ℓ).const_mul w).add_const m
  have h2 : HasDerivAt (fun x => 1 - x) (-1) ℓ := by
    simpa using (hasDerivAt_id ℓ).const_sub 1
  have := (h1.log hc.ne').add ((h2.log (by linarith)).const_mul φ)
  convert this using 1
  ring

/-- **AKMM, (14.5), p. 421.** If `ℓ ∈ (0, 1)` maximises `ln(wℓ′ + m) + φ ln(1 − ℓ′)` locally
(consumption `c = wℓ + m > 0`), then `w/c = φ/(1 − ℓ)`. -/
theorem eq_14_5 {φ w m ℓ : ℝ} (hc : 0 < w * ℓ + m) (hℓ : ℓ < 1)
    (hmax : IsLocalMax (fun x => Real.log (w * x + m) + φ * Real.log (1 - x)) ℓ) :
    w / (w * ℓ + m) = φ / (1 - ℓ) := by
  have := hmax.hasDerivAt_eq_zero (sm_static_deriv hc hℓ)
  linarith

/-- AKMM, p. 421: (14.5) is sufficient: if `w/c = φ/(1 − ℓ)` with `c = wℓ + m > 0`, `ℓ < 1`,
`φ ≥ 0`, then `ℓ` maximises `ln(wℓ′ + m) + φ ln(1 − ℓ′)` over all `ℓ′ < 1` with positive
consumption. -/
theorem sm_static_suff {φ w m ℓ : ℝ} (hφ : 0 ≤ φ) (hc : 0 < w * ℓ + m) (hℓ : ℓ < 1)
    (hfoc : w / (w * ℓ + m) = φ / (1 - ℓ)) (ℓ' : ℝ) (hc' : 0 < w * ℓ' + m) (hℓ' : ℓ' < 1) :
    rb_u φ (w * ℓ' + m) ℓ' ≤ rb_u φ (w * ℓ + m) ℓ := by
  have ht := rb_u_tangent hφ hc hℓ hc' hℓ'
  have e : (w * ℓ' + m - (w * ℓ + m)) / (w * ℓ + m) - φ * ((ℓ' - ℓ) / (1 - ℓ)) =
      (ℓ' - ℓ) * (w / (w * ℓ + m) - φ / (1 - ℓ)) := by
    field_simp
    ring
  rw [hfoc, sub_self, mul_zero] at e
  linarith

/-- **AKMM, (14.6), p. 421: the Euler equation.** With income `y₀` today and `yₛ` tomorrow in
state `s` (probability `pₛ`), gross returns `Rₛ`, if the bond holding `b` maximises
`ln(y₀ − b) + βΣₛ pₛ ln(yₛ + Rₛb)` locally (interior consumption), then
`1/c = βΣₛ pₛRₛ/c′ₛ`. -/
theorem eq_14_6 {S : Type*} [Fintype S] {β y0 b : ℝ} {p y R : S → ℝ} (hc : 0 < y0 - b)
    (hc' : ∀ s, 0 < y s + R s * b)
    (hmax : IsLocalMax (fun x => Real.log (y0 - x) + β * ∑ s, p s * Real.log (y s + R s * x)) b) :
    1 / (y0 - b) = β * ∑ s, p s * (R s / (y s + R s * b)) := by
  have h0 : HasDerivAt (fun x => y0 - x) (-1) b := by simpa using (hasDerivAt_id b).const_sub y0
  have hs : ∀ s, HasDerivAt (fun x => Real.log (y s + R s * x)) (R s / (y s + R s * b)) b := by
    intro s
    have : HasDerivAt (fun x => y s + R s * x) (R s) b := by
      simpa using ((hasDerivAt_id b).const_mul (R s)).const_add (y s)
    exact this.log (hc' s).ne'
  have hsum : HasDerivAt (fun x => ∑ s, p s * Real.log (y s + R s * x))
      (∑ s, p s * (R s / (y s + R s * b))) b :=
    HasDerivAt.fun_sum (u := Finset.univ) fun s _ => (hs s).const_mul (p s)
  have hd := (h0.log hc.ne').add (hsum.const_mul β)
  have := hmax.hasDerivAt_eq_zero hd
  have e : -1 / (y0 - b) = -(1 / (y0 - b)) := by ring
  linarith

/-- **AKMM, (14.7), p. 421.** With zero bond holdings `c = wℓ` (`w > 0`), the intratemporal
condition (14.5) reads `φ/(1 − ℓ) = 1/ℓ`, and holds iff `ℓ = 1/(1 + φ)`. -/
theorem eq_14_7 {φ w ℓ : ℝ} (hφ : 0 ≤ φ) (hw : 0 < w) (hℓ0 : 0 < ℓ) (hℓ1 : ℓ < 1) :
    (w / (w * ℓ + 0) = φ / (1 - ℓ) ↔ φ / (1 - ℓ) = w / (w * ℓ) ∧ w / (w * ℓ) = 1 / ℓ ∧
      ℓ = 1 / (1 + φ)) := by
  have h1 : 0 < 1 - ℓ := by linarith
  have hwl : w / (w * ℓ) = 1 / ℓ := by field_simp
  rw [add_zero]
  constructor
  · intro h
    refine ⟨h.symm, hwl, ?_⟩
    rw [hwl] at h
    field_simp at h ⊢
    linarith
  · rintro ⟨h, -, -⟩
    exact h.symm

/-- **AKMM, p. 421: constant hours in equilibrium.** With `w = z > 0` and `B = 0`, the household's
intratemporal condition holds iff `ℓ = 1/(1 + φ)`, whatever `z`; then `c = Y = zℓ = z/(1 + φ)`, so
output, consumption and TFP are proportional (perfectly correlated) and hours do not move. -/
theorem sm_equilibrium {φ z ℓ : ℝ} (hφ : 0 ≤ φ) (hz : 0 < z) (hℓ0 : 0 < ℓ) (hℓ1 : ℓ < 1)
    (hfoc : z / (z * ℓ + 0) = φ / (1 - ℓ)) :
    ℓ = 1 / (1 + φ) ∧ z * ℓ = z / (1 + φ) := by
  have h := ((eq_14_7 hφ hz hℓ0 hℓ1).1 hfoc).2.2
  refine ⟨h, by rw [h]; ring⟩

/-- AKMM, p. 421: "the real interest rate must adjust": with `B = 0`, `cₜ = zₜ/(1 + φ)` and
`zₜ₊₁ = zₜ^ρe^{εₛ}` in state `s` (probability `pₛ`), the Euler equation (14.6) with a risk-free
return `R` holds iff `R = zₜ^{ρ−1}/(βΣₛ pₛe^{−εₛ})`. -/
theorem sm_interest_rate {S : Type*} [Fintype S] {φ β ρ z R : ℝ} {p ε : S → ℝ} (hφ : 0 ≤ φ)
    (hβ : 0 < β) (hz : 0 < z) (hE : 0 < ∑ s, p s * Real.exp (-ε s)) :
    1 / (z / (1 + φ)) = β * ∑ s, p s * (R / (z ^ ρ * Real.exp (ε s) / (1 + φ))) ↔
      R = z ^ (ρ - 1) / (β * ∑ s, p s * Real.exp (-ε s)) := by
  have h1 : 0 < 1 + φ := by linarith
  have hzr : 0 < z ^ ρ := Real.rpow_pos_of_pos hz ρ
  have hsum : ∑ s, p s * (R / (z ^ ρ * Real.exp (ε s) / (1 + φ))) =
      R * (1 + φ) / z ^ ρ * ∑ s, p s * Real.exp (-ε s) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Real.exp_neg]
    field_simp
  have hzz : z ^ (ρ - 1) = z ^ ρ / z := Real.rpow_sub_one hz.ne' ρ
  rw [hsum, hzz]
  constructor
  · intro h
    field_simp at h ⊢
    linarith
  · intro h
    rw [h]
    field_simp

/-- AKMM, p. 421: "When TFP is high, consumption rises and the real interest rate falls": for
`ρ < 1`, `R(z) = z^{ρ−1}/(βΣₛ pₛe^{−εₛ})` is strictly decreasing in `z`. -/
theorem sm_interest_rate_falls {S : Type*} [Fintype S] {β ρ : ℝ} {p ε : S → ℝ} (hβ : 0 < β)
    (hρ : ρ < 1) (hE : 0 < ∑ s, p s * Real.exp (-ε s)) {z z' : ℝ} (hz : 0 < z) (hzz : z < z') :
    z' ^ (ρ - 1) / (β * ∑ s, p s * Real.exp (-ε s)) <
      z ^ (ρ - 1) / (β * ∑ s, p s * Real.exp (-ε s)) :=
  div_lt_div_of_pos_right (Real.rpow_lt_rpow_of_neg hz hzz (by linarith)) (mul_pos hβ hE)

/-- The partial derivatives of `φ ln(1 − ℓ)`: `U_ℓ = −φ/(1 − ℓ)`, `U_ℓℓ = −φ/(1 − ℓ)²`. -/
theorem sm_leisure_derivs {φ ℓ : ℝ} (hℓ : ℓ < 1) :
    HasDerivAt (fun x => φ * Real.log (1 - x)) (-(φ / (1 - ℓ))) ℓ ∧
      HasDerivAt (fun x => -(φ / (1 - x))) (-(φ / (1 - ℓ) ^ 2)) ℓ := by
  have h2 : HasDerivAt (fun x => 1 - x) (-1) ℓ := by
    simpa using (hasDerivAt_id ℓ).const_sub 1
  have h1 : 1 - ℓ ≠ 0 := by linarith
  constructor
  · convert (h2.log h1).const_mul φ using 1
    field_simp
  · convert ((h2.inv h1).const_mul φ).neg using 1
    · funext x; simp [div_eq_mul_inv]
    · field_simp

/-- **AKMM, p. 421: the Frisch elasticity of log–log preferences is `(1 − ℓ)/ℓ`**, by AKMM
Chapter 12's formula (12.21) `ε^F = U_ℓ/(ℓU_ℓℓ − ℓU_ℓc²/U_cc)` with the separable partials
`U_ℓ = −φ/(1 − ℓ)`, `U_ℓℓ = −φ/(1 − ℓ)²`, `U_ℓc = 0`. -/
theorem sm_frisch {φ ℓ Ucc : ℝ} (hφ : 0 < φ) (hℓ0 : 0 < ℓ) (hℓ1 : ℓ < 1) :
    AKMM.LaborSupply.frischF ℓ (-(φ / (1 - ℓ))) (-(φ / (1 - ℓ) ^ 2)) 0 0 Ucc = (1 - ℓ) / ℓ := by
  unfold AKMM.LaborSupply.frischF
  have h1 : 0 < 1 - ℓ := by linarith
  have := hφ.ne'
  simp only [mul_zero, zero_div, sub_zero]
  field_simp

/-- AKMM, p. 421: "If households work one-third of their available time, this gives a Frisch
elasticity of 2". -/
theorem sm_frisch_two {φ Ucc : ℝ} (hφ : 0 < φ) :
    AKMM.LaborSupply.frischF (1 / 3) (-(φ / (1 - 1 / 3))) (-(φ / (1 - 1 / 3) ^ 2)) 0 0 Ucc = 2 := by
  rw [sm_frisch hφ (by norm_num) (by norm_num)]
  norm_num

/-- The same value from AKMM Chapter 12's Cobb–Douglas formula `dyn_frisch_cd` at `σ = 1`
(the calibrated utility `(1 − ψ) ln c + ψ ln(1 − ℓ)` of p. 428 has these partials). -/
theorem sm_frisch_cd {ψ c ℓ : ℝ} (hψ : 0 < ψ) (hψ1 : ψ < 1) (hc : 0 < c) (hℓ0 : 0 < ℓ)
    (hℓ1 : 0 < 1 - ℓ) :
    AKMM.LaborSupply.frischF ℓ (-(ψ * c ^ ((1 - ψ) * (1 - 1)) * (1 - ℓ) ^ (ψ * (1 - 1) - 1)))
      (ψ * (ψ * (1 - 1) - 1) * c ^ ((1 - ψ) * (1 - 1)) * (1 - ℓ) ^ (ψ * (1 - 1) - 1 - 1))
      (-((1 - ψ) * ψ * (1 - 1) * c ^ ((1 - ψ) * (1 - 1) - 1) * (1 - ℓ) ^ (ψ * (1 - 1) - 1)))
      (-((1 - ψ) * ψ * (1 - 1) * c ^ ((1 - ψ) * (1 - 1) - 1) * (1 - ℓ) ^ (ψ * (1 - 1) - 1)))
      ((1 - ψ) * ((1 - ψ) * (1 - 1) - 1) * c ^ ((1 - ψ) * (1 - 1) - 1 - 1) *
        (1 - ℓ) ^ (ψ * (1 - 1))) = (1 - ℓ) / ℓ := by
  rw [AKMM.LaborSupply.dyn_frisch_cd hψ hψ1 one_ne_zero (by norm_num) hc hℓ0 hℓ1]
  ring

/-- AKMM, p. 421: the Frisch elasticity measures the response of hours to the wage "holding the
marginal utility of consumption constant": with `λ > 0` fixed, `φ/(1 − ℓ) = λw` gives
`ℓ(w) = 1 − φ/(λw)`, and along `w(s) = we^s` the derivative of `ln ℓ` at `s = 0` is
`(1 − ℓ)/ℓ`. -/
theorem sm_frisch_response {φ lam w : ℝ} (hφ : 0 < φ) (hlam : 0 < lam) (hw : 0 < w)
    (hℓ : 0 < 1 - φ / (lam * w)) :
    HasDerivAt (fun s => Real.log (1 - φ / (lam * (w * Real.exp s))))
      ((1 - (1 - φ / (lam * w))) / (1 - φ / (lam * w))) 0 := by
  have hg : HasDerivAt (fun s => 1 - φ / (lam * (w * Real.exp s))) (φ / (lam * w)) 0 := by
    have he : HasDerivAt (fun s => lam * (w * Real.exp s)) (lam * w) 0 := by
      have := ((Real.hasDerivAt_exp 0).const_mul w).const_mul lam
      simpa using this
    have hne : lam * (w * Real.exp 0) ≠ 0 := by positivity
    have := (he.inv hne).const_mul φ |>.const_sub 1
    convert this using 1
    · funext s; simp [div_eq_mul_inv]
    · simp only [Real.exp_zero, mul_one]
      field_simp
  have := hg.log (by simpa using hℓ.ne')
  convert this using 1
  simp

end AKMM.RealBusinessCycles
