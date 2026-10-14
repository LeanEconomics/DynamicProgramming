/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicApplications.ConsumptionSavingsPolicy

/-!
# A consumption–savings problem: three corrections

SLP §5.17.

* **`m₁` need not exist** (`ex_5_17b_m1_fails`). Take `U(c) = c − e^{−c}`, which is `C¹`,
  strictly increasing and strictly concave, with `β = 1/2`, `R = 1`, `I = 1`. Then
  `U'(c) = 1 + e^{−c} > 1 > RβU'(I)`, so `U'(I + m₁) = RβU'(I)` has no solution. (Here consuming
  all wealth at once is optimal from every `x`.) Some condition such as `U'(c) → 0`, which
  `CSHyp` assumes, is needed.
* **The hint to 5.17g fails when `R < 1`** (`ex_5_17g_hint_fails`). With `W = RI/(R − 1) < 0`,
  `x_n ≤ Rⁿ(x₀ + W)` is false already at `n = 1`; at `R = 1`, `W` is undefined. The proof of
  `v = v*` in `ConsumptionSavings` does not use the hint.
* **`g(x') − g(x) < x' − x` fails when `R > 1`** (`ex_5_17h_counterexample`). Take `R = 2`,
  `β = 9/20`, `I = 1`. Let `U'` be almost flat on `[0, 2]`, at `1 − (c − 1)/100`, then falling
  steeply as `0.099/(c − 1.9)`. A consumer who will consume `c₁ ∈ (1, 2)` next period chooses
  `c₀` with `U'(c₀) = RβU'(c₁)`, which barely moves with `c₁`. So nearly all of an extra unit of
  wealth is saved, and saving grows at rate about `R = 2`. Concretely, at
  `x = 1 + 55/499 < x' = 11/10 + 55/498`, `g(x) = 1/5` and `g(x') = 2/5`. The correct bound is
  `g(x') − g(x) < R(x' − x)` (`ex_5_17h_slope`), and the book's bound holds for `R ≤ 1`
  (`ex_5_17h_slope_le_one`).
-/

open Set Filter Topology

namespace StokeyLucasPrescott.DeterministicApplications

/-! ### `m₁` need not exist -/

theorem hasDerivAt_cexp (c : ℝ) :
    HasDerivAt (fun c : ℝ => c - Real.exp (-c)) (1 + Real.exp (-c)) c := by
  convert (hasDerivAt_id' c).sub ((hasDerivAt_neg c).exp) using 1
  ring

/-- **Exercise 5.17b (correction).** `U(c) = c − e^{−c}` is `C¹`, strictly increasing and
strictly concave on `ℝ₊`, but with `β = 1/2`, `R = 1`, `I = 1` no `m ≥ 0` solves
`U'(I + m) = RβU'(I)`. -/
theorem ex_5_17b_m1_fails :
    (∀ c, HasDerivAt (fun c : ℝ => c - Real.exp (-c)) (1 + Real.exp (-c)) c) ∧
      Continuous (fun c : ℝ => 1 + Real.exp (-c)) ∧
      StrictMonoOn (fun c : ℝ => c - Real.exp (-c)) (Ici 0) ∧
      StrictConcaveOn ℝ (Ici 0) (fun c : ℝ => c - Real.exp (-c)) ∧
      ¬ ∃ m : ℝ, 0 ≤ m ∧
        1 + Real.exp (-(1 + m)) = 1 * (1 / 2) * (1 + Real.exp (-1)) := by
  have hcont : Continuous (fun c : ℝ => c - Real.exp (-c)) :=
    continuous_iff_continuousAt.2 fun c => (hasDerivAt_cexp c).continuousAt
  have hderiv : ∀ c, deriv (fun c : ℝ => c - Real.exp (-c)) c = 1 + Real.exp (-c) :=
    fun c => (hasDerivAt_cexp c).deriv
  refine ⟨hasDerivAt_cexp, by fun_prop, strictMonoOn_of_deriv_pos (convex_Ici 0)
    hcont.continuousOn fun c _ => by rw [hderiv]; positivity, ?_, ?_⟩
  · refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0) hcont.continuousOn ?_
    intro a _ b _ hab
    rw [hderiv, hderiv]
    have := Real.exp_lt_exp.2 (neg_lt_neg hab)
    linarith
  · rintro ⟨m, -, hm⟩
    have h1 : Real.exp (-1) < 1 := by
      have := Real.exp_lt_exp.2 (by norm_num : (-1 : ℝ) < 0)
      rwa [Real.exp_zero] at this
    have h2 := Real.exp_pos (-(1 + m))
    linarith

/-! ### The hint to 5.17g -/

/-- **Exercise 5.17g (correction to the hint).** With `R = 1/2`, `I = 1` and `x₀ = 0`, saving
all income, `x₁ = RI = 1/2`, is feasible, but `R(x₀ + W) = −1/2` with `W = RI/(R − 1)`. -/
theorem ex_5_17g_hint_fails :
    (1 / 2 : ℝ) ≤ (1 + 0) * (1 / 2) ∧
      (1 / 2 : ℝ) ^ 1 * (0 + 1 / 2 * 1 / (1 / 2 - 1)) < 1 / 2 := by
  norm_num

/-! ### `g(x') − g(x) < x' − x` fails for `R > 1` -/

/-- Utility of the counterexample: `c − (c − 1)²/200` on `(−∞, 2]`, then
`399/200 + 0.099 ln(10(c − 1.9))`. -/
noncomputable def ceU (c : ℝ) : ℝ :=
  if c ≤ 2 then c - (c - 1) ^ 2 / 200 else 399 / 200 + 99 / 1000 * Real.log ((c - 19 / 10) * 10)

/-- Its marginal utility: `1 − (c − 1)/100` on `(−∞, 2]`, then `0.099/(c − 1.9)`. -/
noncomputable def ceU' (c : ℝ) : ℝ := if c ≤ 2 then 1 - (c - 1) / 100 else 99 / 1000 / (c - 19 / 10)

theorem hasDerivAt_ce1 (c : ℝ) :
    HasDerivAt (fun c : ℝ => c - (c - 1) ^ 2 / 200) (1 - (c - 1) / 100) c := by
  convert (hasDerivAt_id' c).sub ((((hasDerivAt_id' c).sub_const 1).pow 2).div_const 200)
    using 1
  norm_num
  ring

theorem hasDerivAt_ce2 {c : ℝ} (hc : 19 / 10 < c) :
    HasDerivAt (fun c : ℝ => 399 / 200 + 99 / 1000 * Real.log ((c - 19 / 10) * 10))
      (99 / 1000 / (c - 19 / 10)) c := by
  have hne : (c - 19 / 10) * 10 ≠ 0 := by
    have : 0 < c - 19 / 10 := by linarith
    positivity
  have hlog := (((hasDerivAt_id' c).sub_const (19 / 10)).mul_const 10).log hne
  convert (hlog.const_mul (99 / 1000)).const_add (399 / 200) using 1
  have : c - 19 / 10 ≠ 0 := by linarith
  field_simp

theorem ceU'_low {c : ℝ} (hc : c ≤ 2) : ceU' c = 1 - (c - 1) / 100 := by
  simp only [ceU', hc, ↓reduceIte]

theorem ceU'_high {c : ℝ} (hc : 2 < c) : ceU' c = 99 / 1000 / (c - 19 / 10) := by
  simp only [ceU', not_le.2 hc, ↓reduceIte]

theorem hasDerivAt_ceU (c : ℝ) : HasDerivAt ceU (ceU' c) c := by
  rcases lt_trichotomy c 2 with hlt | rfl | hgt
  · rw [ceU'_low hlt.le]
    refine (hasDerivAt_ce1 c).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hlt] with y hy
    simp only [ceU, (mem_Iio.1 hy).le, ↓reduceIte]
  · have hl : HasDerivWithinAt ceU (ceU' 2) (Iic 2) 2 := by
      rw [ceU'_low le_rfl]
      exact (hasDerivAt_ce1 2).hasDerivWithinAt.congr
        (fun y hy => by simp only [ceU, mem_Iic.1 hy, ↓reduceIte])
        (by simp only [ceU, le_refl, ↓reduceIte])
    have hr : HasDerivWithinAt ceU (ceU' 2) (Ici 2) 2 := by
      have h2 : ceU' 2 = 99 / 1000 / ((2 : ℝ) - 19 / 10) := by rw [ceU'_low le_rfl]; norm_num
      rw [h2]
      refine (hasDerivAt_ce2 (by norm_num)).hasDerivWithinAt.congr (fun y hy => ?_) ?_
      · rcases eq_or_lt_of_le (mem_Ici.1 hy) with rfl | hlt
        · simp only [ceU, le_refl, ↓reduceIte]; norm_num
        · simp only [ceU, not_le.2 hlt, ↓reduceIte]
      · simp only [ceU, le_refl, ↓reduceIte]; norm_num
    have := hl.union hr
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · rw [ceU'_high hgt]
    refine (hasDerivAt_ce2 (by linarith)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hgt] with y hy
    simp only [ceU, not_le.2 (mem_Ioi.1 hy), ↓reduceIte]

theorem ceU'_strictAnti : StrictAnti ceU' := by
  intro a b hab
  rcases le_or_gt b 2 with hb | hb
  · rw [ceU'_low hb, ceU'_low (hab.le.trans hb)]
    linarith
  · rw [ceU'_high hb]
    have hb' : 0 < b - 19 / 10 := by linarith
    rcases le_or_gt a 2 with ha | ha
    · rw [ceU'_low ha, div_lt_iff₀ hb']
      nlinarith
    · rw [ceU'_high ha]
      exact div_lt_div_of_pos_left (by norm_num) (by linarith) (by linarith)

theorem ceU'_pos (c : ℝ) : 0 < ceU' c := by
  rcases le_or_gt c 2 with h2 | h2
  · rw [ceU'_low h2]; linarith
  · rw [ceU'_high h2]; exact div_pos (by norm_num) (by linarith)

theorem continuousAt_ceU' (c : ℝ) : ContinuousAt ceU' c := by
  have hlin : Continuous fun c : ℝ => 1 - (c - 1) / 100 := by fun_prop
  rcases lt_trichotomy c 2 with hlt | rfl | hgt
  · refine hlin.continuousAt.congr ?_
    filter_upwards [Iio_mem_nhds hlt] with y hy
    exact (ceU'_low hy.le).symm
  · refine continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩
    · exact hlin.continuousAt.continuousWithinAt.congr (fun y hy => ceU'_low hy) (ceU'_low le_rfl)
    · have ht : ContinuousAt (fun c : ℝ => 99 / 1000 / (c - 19 / 10)) 2 :=
        continuousAt_const.div (continuousAt_id.sub continuousAt_const) (by norm_num)
      refine ht.continuousWithinAt.congr (fun y hy => ?_) ?_
      · rcases eq_or_lt_of_le (mem_Ici.1 hy) with rfl | hlt
        · rw [ceU'_low le_rfl]; norm_num
        · exact ceU'_high hlt
      · rw [ceU'_low le_rfl]; norm_num
  · have ht : ContinuousAt (fun c : ℝ => 99 / 1000 / (c - 19 / 10)) c :=
      continuousAt_const.div (continuousAt_id.sub continuousAt_const) (by
        have : (19 : ℝ) / 10 < c := by linarith
        exact sub_ne_zero.2 this.ne')
    refine ht.congr ?_
    filter_upwards [Ioi_mem_nhds hgt] with y hy
    exact (ceU'_high hy).symm

/-- The counterexample satisfies the hypotheses of §5.17, with `R = 2 > 1`. -/
theorem ceHyp : CSHyp ceU ceU' (9 / 20) 2 1 := by
  have hcont : Continuous ceU :=
    continuous_iff_continuousAt.2 fun c => (hasDerivAt_ceU c).continuousAt
  have hderiv : ∀ c, deriv ceU c = ceU' c := fun c => (hasDerivAt_ceU c).deriv
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, hcont.continuousOn,
    fun c _ => hasDerivAt_ceU c, fun c _ => (continuousAt_ceU' c).continuousWithinAt,
    strictMonoOn_of_deriv_pos (convex_Ici 0) hcont.continuousOn fun c hc => ?_,
    StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0) hcont.continuousOn ?_, ?_⟩
  · rw [interior_Ici] at hc
    rw [hderiv]
    exact ceU'_pos c
  · intro a _ b _ hab
    rw [hderiv, hderiv]
    exact ceU'_strictAnti hab
  · have ht : Tendsto (fun c : ℝ => 99 / 1000 / (c - 19 / 10)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_atTop_add_const_right atTop (-(19 / 10)) tendsto_id).congr fun c => by
          simp [sub_eq_add_neg])
    refine ht.congr' ?_
    filter_upwards [eventually_gt_atTop 2] with c hc
    exact (ceU'_high hc).symm

/-- **Exercise 5.17h (correction).** In the counterexample (`R = 2`),
`x = 1 + 55/499 < x' = 11/10 + 55/498` but
`g(x') − g(x) = 1/5 > x' − x = 1/10 + 55/(498 · 499)`. -/
theorem ex_5_17h_counterexample :
    (1 : ℝ) < 2 ∧ ∃ x x' : ℝ, 0 ≤ x ∧ x < x' ∧ x' - x < gR ceHyp x' - gR ceHyp x := by
  have h := ceHyp
  have hU1 : ceU' 1 = 1 := by rw [ceU'_low (by norm_num)]; norm_num
  -- `g(Ξ(RβU'(1 + y))) = y` and `Ξ(RβU'(1 + y)) = cI(RβU'(1 + y)) − 1 + y/2`, for `y = 1/5, 2/5`
  have key : ∀ y c : ℝ, 0 < y → y ≤ 1 → 2 < c → ceU' c = 2 * (9 / 20) * ceU' (1 + y) →
      gR ceHyp (wealth ceU' (9 / 20) 2 1 (2 * (9 / 20) * ceU' (1 + y))) = y ∧
        wealth ceU' (9 / 20) 2 1 (2 * (9 / 20) * ceU' (1 + y)) = c - 1 + y / 2 := by
    intro y c hy hy1 hc hcU
    have hp : 0 < ceU' (1 + y) := ceU'_pos _
    have hρp : 0 < 2 * (9 / 20) * ceU' (1 + y) := by positivity
    have hpy : ceU' (1 + y) = 1 - y / 100 := by rw [ceU'_low (by linarith)]; ring
    have hw : wealth ceU' (9 / 20) 2 1 (ceU' (1 + y)) = y := by
      rw [h.wealth_shift hp, h.cI_U' (by linarith), h.wealth_of_ge (by
        rw [hU1, hpy, le_div_iff₀ (by norm_num)]; linarith)]
      ring
    refine ⟨?_, ?_⟩
    · rw [h.gR_wealth hρp, mul_div_cancel_left₀ _ (by norm_num), hw]
    · rw [h.wealth_shift hρp, mul_div_cancel_left₀ _ (by norm_num), hw, ← hcU,
        h.cI_U' (by linarith)]
      ring
  have hc1 : (2 : ℝ) < 19 / 10 + 55 / 499 := by norm_num
  have hc2 : (2 : ℝ) < 19 / 10 + 55 / 498 := by norm_num
  obtain ⟨hg1, hx1⟩ := key (1 / 5) (19 / 10 + 55 / 499) (by norm_num) (by norm_num) hc1 (by
    rw [ceU'_high hc1, ceU'_low (by norm_num)]; norm_num)
  obtain ⟨hg2, hx2⟩ := key (2 / 5) (19 / 10 + 55 / 498) (by norm_num) (by norm_num) hc2 (by
    rw [ceU'_high hc2, ceU'_low (by norm_num)]; norm_num)
  refine ⟨by norm_num, wealth ceU' (9 / 20) 2 1 (2 * (9 / 20) * ceU' (1 + 1 / 5)),
    wealth ceU' (9 / 20) 2 1 (2 * (9 / 20) * ceU' (1 + 2 / 5)), ?_, ?_, ?_⟩
  · rw [hx1]; norm_num
  · rw [hx1, hx2]; norm_num
  · rw [hg1, hg2, hx1, hx2]; norm_num

/-- **Exercise 5.17h (correction).** The book's bound `g(x') − g(x) < x' − x` does not hold for
every model satisfying its hypotheses. -/
theorem ex_5_17h_book_bound_fails :
    ¬ ∀ x x' : ℝ, 0 ≤ x → x < x' → gR ceHyp x' - gR ceHyp x < x' - x := by
  intro hall
  obtain ⟨-, x, x', hx, hxx', hlt⟩ := ex_5_17h_counterexample
  exact lt_asymm (hall x x' hx hxx') hlt

end StokeyLucasPrescott.DeterministicApplications
