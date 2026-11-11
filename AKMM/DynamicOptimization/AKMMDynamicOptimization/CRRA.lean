/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# CRRA utility and the elasticity of intertemporal substitution

AKMM, §4.2.4, the CRRA box (p. 104), the EIS (p. 105) and Example 4.2 (p. 105); also fn. 31 of
App. 4.A.2 (p. 830).

* `crra_tendsto_log`: `(c^{1−σ} − 1)/(1 − σ) → log c` as `σ → 1` (the box and fn. 31).
* As `σ → ∞` the CRRA utility tends to `0` for `c ≥ 1` (`crra_tendsto_zero_of_one_le`) but to
  `−∞` for `0 < c < 1` (`crra_tendsto_atBot_of_lt_one`): the box's "converges to zero for all
  `c`" is false.
* The Leontief limit: `(Σ_{t<n} βᵗc_t^{1−σ})^{1/(1−σ)} → min_t c_t` as `σ → ∞`
  (`crra_leontief_limit`), proved for finitely many periods.
* Example 4.2: repeated substitution in the Euler equation (`example42_repeated`), the ratio
  `c_{t+s}/c_t = (βˢ)^{1/σ}R_{t,t+s}^{1/σ}` (`example42_ratio`), the EIS `1/σ`
  (`example42_eis`), constant expenditure shares under log utility (`example42_log_shares`), and
  the income and substitution effects: `c_t` rises with the return when `σ > 1` and falls when
  `σ < 1` (`example42_income_effect`, `example42_substitution_effect`).
-/

namespace AKMM.DynamicOptimization

open Filter Topology Real

/-- AKMM, CRRA box, p. 104: `u(c) = (c^{1−σ} − 1)/(1 − σ)`. -/
noncomputable def crra (σ c : ℝ) : ℝ := (c ^ (1 - σ) - 1) / (1 - σ)

/-- AKMM, CRRA box (p. 104) and fn. 31 (p. 830): `σ → 1` gives logarithmic utility,
`(c^{1−σ} − 1)/(1 − σ) → log c`. -/
theorem crra_tendsto_log {c : ℝ} (hc : 0 < c) :
    Tendsto (fun σ => crra σ c) (𝓝[≠] 1) (𝓝 (Real.log c)) := by
  have hd : HasDerivAt (fun s : ℝ => c ^ s) (c ^ (0 : ℝ) * Real.log c) 0 :=
    (hasStrictDerivAt_const_rpow hc 0).hasDerivAt
  rw [rpow_zero, one_mul] at hd
  have hslope := hd.tendsto_slope
  have hmap : Tendsto (fun σ : ℝ => 1 - σ) (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun σ : ℝ => 1 - σ) (𝓝 1) (𝓝 (1 - 1)) :=
        (continuous_const.sub continuous_id).tendsto 1
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact sub_ne_zero.2 (Ne.symm hσ)
  refine (hslope.comp hmap).congr fun σ => ?_
  simp only [Function.comp_apply, slope_def_field, sub_zero, rpow_zero, crra]

/-- AKMM, CRRA box, p. 104: for `c ≥ 1` the CRRA utility tends to `0` as `σ → ∞`. -/
theorem crra_tendsto_zero_of_one_le {c : ℝ} (hc : 1 ≤ c) :
    Tendsto (fun σ => crra σ c) atTop (𝓝 0) := by
  rcases eq_or_lt_of_le hc with rfl | hc1
  · simp [crra]
  have hc0 : 0 < c := by linarith
  have hlog : 0 < Real.log c := Real.log_pos hc1
  have hnum : Tendsto (fun σ : ℝ => 1 - c ^ (1 - σ)) atTop (𝓝 (1 - 0)) := by
    refine tendsto_const_nhds.sub ?_
    have : Tendsto (fun σ : ℝ => (1 - σ) * Real.log c) atTop atBot :=
      (tendsto_atBot_add_const_left _ 1 (tendsto_neg_atTop_atBot)).atBot_mul_const hlog
        |>.congr fun σ => by ring
    exact (Real.tendsto_exp_atBot.comp this).congr fun σ => by
      simp [Function.comp_apply, rpow_def_of_pos hc0, mul_comm]
  have hden : Tendsto (fun σ : ℝ => σ - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  refine (hnum.div_atTop hden).congr' ?_
  filter_upwards [eventually_gt_atTop 1] with σ hσ
  simp only [crra]
  have : (1 - σ) ≠ 0 := by linarith
  have : (σ - 1) ≠ 0 := by linarith
  field_simp
  ring

/-- **AKMM, CRRA box, p. 104, corrected.** For `0 < c < 1` the CRRA utility tends to `−∞` as
`σ → ∞`, so the box's "utility converges to zero for all `c`" fails. -/
theorem crra_tendsto_atBot_of_lt_one {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    Tendsto (fun σ => crra σ c) atTop atBot := by
  set a := -Real.log c
  have ha : 0 < a := neg_pos.2 (Real.log_neg hc0 hc1)
  -- `c^{1−σ} = exp(a(σ − 1))` and `exp(ax)/x → ∞`
  have hx : Tendsto (fun σ : ℝ => σ - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  have hexp : Tendsto (fun x : ℝ => Real.exp (a * x) / x) atTop atTop := by
    have h1 : Tendsto (fun x : ℝ => a * x) atTop atTop := tendsto_id.const_mul_atTop ha
    have h2 := (tendsto_exp_div_pow_atTop 1).comp h1
    have h3 := h2.const_mul_atTop ha
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [Function.comp_apply, pow_one]
    field_simp
  have hmain : Tendsto (fun σ : ℝ => Real.exp (a * (σ - 1)) / (σ - 1) - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (hexp.comp hx)
  refine tendsto_atBot_mono' _ ?_ (tendsto_neg_atTop_atBot.comp hmain)
  filter_upwards [eventually_ge_atTop 2] with σ hσ
  have hpow : c ^ (1 - σ) = Real.exp (a * (σ - 1)) := by
    rw [rpow_def_of_pos hc0]; congr 1; simp only [a]; ring
  simp only [Function.comp_apply, crra, hpow]
  have hs : 0 < σ - 1 := by linarith
  have e : (Real.exp (a * (σ - 1)) - 1) / (1 - σ) =
      -(Real.exp (a * (σ - 1)) / (σ - 1)) + 1 / (σ - 1) := by
    have : (1 - σ) ≠ 0 := by linarith
    field_simp
    ring
  rw [e]
  have : 1 / (σ - 1) ≤ 1 := by rw [div_le_one hs]; linarith
  linarith

/-- **AKMM, CRRA box, p. 104: the Leontief limit.** For finitely many periods, positive
consumption and `β > 0`, `(Σ_{t<n} βᵗc_t^{1−σ})^{1/(1−σ)} → min_{t<n} c_t` as `σ → ∞`. (The book
states it for infinite sums, where the minimum need not exist.) -/
theorem crra_leontief_limit {β : ℝ} (hβ : 0 < β) {n : ℕ} (hn : (Finset.range n).Nonempty)
    {c : ℕ → ℝ} (hc : ∀ t, 0 < c t) :
    Tendsto (fun σ : ℝ => (∑ t ∈ Finset.range n, β ^ t * c t ^ (1 - σ)) ^ (1 / (1 - σ))) atTop
      (𝓝 ((Finset.range n).inf' hn c)) := by
  set m := (Finset.range n).inf' hn c
  obtain ⟨j, hj, hjm⟩ := Finset.exists_mem_eq_inf' hn c
  have hmj : m = c j := hjm
  have hm : 0 < m := by rw [hmj]; exact hc j
  have hmle : ∀ t ∈ Finset.range n, m ≤ c t := fun t ht => Finset.inf'_le c ht
  set W := ∑ t ∈ Finset.range n, β ^ t
  have hW : 0 < W := Finset.sum_pos (fun t _ => pow_pos hβ t) hn
  set w := β ^ j
  have hw : 0 < w := pow_pos hβ j
  have he : Tendsto (fun σ : ℝ => 1 / (1 - σ)) atTop (𝓝 0) := by
    have : Tendsto (fun σ : ℝ => 1 - σ) atTop atBot :=
      tendsto_atBot_add_const_left _ 1 tendsto_neg_atTop_atBot
    have h2 := tendsto_inv_atBot_zero.comp this
    simpa only [one_div, Function.comp_def] using h2
  have hlim : ∀ x : ℝ, 0 < x → Tendsto (fun σ : ℝ => x ^ (1 / (1 - σ)) * m) atTop (𝓝 m) := by
    intro x hx
    have := ((continuousAt_const_rpow hx.ne' (b := 0)).tendsto.comp he).mul_const m
    simpa only [Function.comp_def, rpow_zero, one_mul] using this
  have hscale : ∀ x : ℝ, 0 < x → ∀ σ : ℝ, 1 < σ →
      (x * m ^ (1 - σ)) ^ (1 / (1 - σ)) = x ^ (1 / (1 - σ)) * m := by
    intro x hx σ hσ
    rw [mul_rpow hx.le (rpow_nonneg hm.le _), ← rpow_mul hm.le]
    have : (1 - σ) * (1 / (1 - σ)) = 1 := by field_simp [show (1 - σ) ≠ 0 by linarith]
    rw [this, rpow_one]
  have hbounds : ∀ σ : ℝ, 1 < σ →
      W ^ (1 / (1 - σ)) * m ≤ (∑ t ∈ Finset.range n, β ^ t * c t ^ (1 - σ)) ^ (1 / (1 - σ)) ∧
      (∑ t ∈ Finset.range n, β ^ t * c t ^ (1 - σ)) ^ (1 / (1 - σ)) ≤ w ^ (1 / (1 - σ)) * m := by
    intro σ hσ
    have hp : 1 - σ ≤ 0 := by linarith
    have he0 : 1 / (1 - σ) ≤ 0 := div_nonpos_of_nonneg_of_nonpos zero_le_one hp
    have hupper : ∑ t ∈ Finset.range n, β ^ t * c t ^ (1 - σ) ≤ W * m ^ (1 - σ) := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_left
        (rpow_le_rpow_of_nonpos hm (hmle t ht) hp) (pow_nonneg hβ.le t)
    have hlower : w * m ^ (1 - σ) ≤ ∑ t ∈ Finset.range n, β ^ t * c t ^ (1 - σ) := by
      have := Finset.single_le_sum (f := fun t => β ^ t * c t ^ (1 - σ))
        (fun t _ => mul_nonneg (pow_nonneg hβ.le t) (rpow_nonneg (hc t).le _)) hj
      simpa only [w, hmj] using this
    have hpos : 0 < w * m ^ (1 - σ) := mul_pos hw (rpow_pos_of_pos hm _)
    rw [← hscale W hW σ hσ, ← hscale w hw σ hσ]
    exact ⟨rpow_le_rpow_of_nonpos (hpos.trans_le hlower) hupper he0,
      rpow_le_rpow_of_nonpos hpos hlower he0⟩
  have hW' := hlim W hW
  have hw' := hlim w hw
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hW' hw'
    ((eventually_gt_atTop 1).mono fun σ hσ => (hbounds σ hσ).1)
    ((eventually_gt_atTop 1).mono fun σ hσ => (hbounds σ hσ).2)

/-- **AKMM, Example 4.2, p. 105: repeated substitution.** The Euler equation
`u'(c_t) = βu'(c_{t+1})R_{t+1}` gives `u'(c_t) = βˢu'(c_{t+s})R_{t+1}⋯R_{t+s}`. -/
theorem example42_repeated {u' : ℝ → ℝ} {β : ℝ} {c R : ℕ → ℝ}
    (heuler : ∀ t, u' (c t) = β * u' (c (t + 1)) * R (t + 1)) (t s : ℕ) :
    u' (c t) = β ^ s * u' (c (t + s)) * ∏ i ∈ Finset.range s, R (t + i + 1) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [ih, heuler (t + s), Finset.prod_range_succ, pow_succ, ← add_assoc]
    ring

/-- **AKMM, Example 4.2, p. 105.** With `u'(c) = c^{−σ}`, `σ > 0`, the Euler relation
`c_t^{−σ} = βˢc_{t+s}^{−σ}R_{t,t+s}` gives `c_{t+s}/c_t = (βˢ)^{1/σ}R_{t,t+s}^{1/σ}`. -/
theorem example42_ratio {σ B R c0 c1 : ℝ} (hσ : 0 < σ) (hB : 0 < B) (hR : 0 < R) (hc0 : 0 < c0)
    (hc1 : 0 < c1) (h : c0 ^ (-σ) = B * c1 ^ (-σ) * R) :
    c1 / c0 = B ^ (1 / σ) * R ^ (1 / σ) := by
  have h' : (c1 / c0) ^ σ = B * R := by
    rw [div_rpow hc1.le hc0.le, rpow_neg hc0.le, rpow_neg hc1.le] at *
    have h0 : 0 < c0 ^ σ := rpow_pos_of_pos hc0 σ
    have h1 : 0 < c1 ^ σ := rpow_pos_of_pos hc1 σ
    field_simp at h
    rw [div_eq_iff h0.ne']
    linarith
  have hq : 0 < c1 / c0 := div_pos hc1 hc0
  rw [← mul_rpow hB.le hR.le, ← h', ← rpow_mul hq.le, mul_one_div_cancel hσ.ne', rpow_one]

/-- **AKMM, Example 4.2, p. 105: the EIS of CRRA utility is `1/σ`.** Writing the return as
`R = eˣ`, `log(c_{t+s}/c_t) = log((βˢ)^{1/σ}R^{1/σ})` has derivative `1/σ` in `x = log R`. -/
theorem example42_eis {σ B : ℝ} (hB : 0 < B) (x : ℝ) :
    HasDerivAt (fun x => Real.log (B ^ (1 / σ) * Real.exp x ^ (1 / σ))) (1 / σ) x := by
  have e : (fun x => Real.log (B ^ (1 / σ) * Real.exp x ^ (1 / σ))) =
      fun x => Real.log (B ^ (1 / σ)) + x * (1 / σ) := by
    funext x
    rw [Real.log_mul (rpow_pos_of_pos hB _).ne' (rpow_pos_of_pos (exp_pos x) _).ne',
      Real.log_rpow (exp_pos x), Real.log_exp, mul_comm]
  rw [e]
  simpa using ((hasDerivAt_id x).mul_const (1 / σ)).const_add (Real.log (B ^ (1 / σ)))

/-- AKMM, Example 4.2, p. 105: with log utility (`σ = 1`) the expenditure ratio
`c_t/(c_{t+s}/R_{t,t+s}) = 1/βˢ` does not depend on the return. -/
theorem example42_log_shares {B R c0 c1 : ℝ} (hB : 0 < B) (hR : 0 < R) (hc0 : 0 < c0)
    (h : c1 = B * R * c0) : c0 / (c1 / R) = 1 / B := by
  rw [h]; field_simp

/-- AKMM, Example 4.2, p. 105: with `c_{t+s} = (βˢR)^{1/σ}c_t` and the budget
`c_t + c_{t+s}/R = W`, consumption is `c_t = W/(1 + (βˢ)^{1/σ}R^{1/σ−1})`. -/
theorem example42_consumption {σ B R W c0 c1 : ℝ} (hB : 0 < B) (hR : 0 < R)
    (hratio : c1 = B ^ (1 / σ) * R ^ (1 / σ) * c0) (hbudget : c0 + c1 / R = W) :
    c0 = W / (1 + B ^ (1 / σ) * R ^ (1 / σ - 1)) := by
  have hpos : 0 < 1 + B ^ (1 / σ) * R ^ (1 / σ - 1) := by positivity
  rw [eq_div_iff hpos.ne', ← hbudget, hratio, rpow_sub_one hR.ne']
  field_simp

/-- **AKMM, Example 4.2, p. 105: the income effect dominates for `σ > 1`.** Then
`c_t = W/(1 + (βˢ)^{1/σ}R^{1/σ−1})` rises with the return `R` (and saving falls). -/
theorem example42_income_effect {σ B W : ℝ} (hσ : 1 < σ) (hB : 0 < B) (hW : 0 < W) :
    StrictMonoOn (fun R => W / (1 + B ^ (1 / σ) * R ^ (1 / σ - 1))) (Set.Ioi 0) := by
  intro R hR R' hR' hlt
  have he : 1 / σ - 1 < 0 := by
    rw [sub_neg, div_lt_one (by linarith)]; exact hσ
  have h1 : R' ^ (1 / σ - 1) < R ^ (1 / σ - 1) := rpow_lt_rpow_of_neg hR hlt he
  have hb : 0 < B ^ (1 / σ) := rpow_pos_of_pos hB _
  have hd' : 0 < 1 + B ^ (1 / σ) * R' ^ (1 / σ - 1) := by
    have := rpow_pos_of_pos (show (0 : ℝ) < R' from hR') (1 / σ - 1); positivity
  exact div_lt_div_of_pos_left hW hd' (by nlinarith)

/-- **AKMM, Example 4.2, p. 105: the substitution effect dominates for `σ < 1`.** Then `c_t`
falls with the return `R` (and saving rises). -/
theorem example42_substitution_effect {σ B W : ℝ} (hσ0 : 0 < σ) (hσ : σ < 1) (hB : 0 < B)
    (hW : 0 < W) :
    StrictAntiOn (fun R => W / (1 + B ^ (1 / σ) * R ^ (1 / σ - 1))) (Set.Ioi 0) := by
  intro R hR R' hR' hlt
  have he : 0 < 1 / σ - 1 := by rw [sub_pos, lt_div_iff₀ hσ0]; linarith
  have h1 : R ^ (1 / σ - 1) < R' ^ (1 / σ - 1) := rpow_lt_rpow (le_of_lt hR) hlt he
  have hb : 0 < B ^ (1 / σ) := rpow_pos_of_pos hB _
  have hd : 0 < 1 + B ^ (1 / σ) * R ^ (1 / σ - 1) := by
    have := rpow_pos_of_pos (show (0 : ℝ) < R from hR) (1 / σ - 1); positivity
  exact div_lt_div_of_pos_left hW hd (by nlinarith)

end AKMM.DynamicOptimization
