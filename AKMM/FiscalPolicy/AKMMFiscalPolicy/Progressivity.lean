/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Moments.Variance

/-!
# Progressivity: the HSV tax and transfer system, and wealth effects

AKMM, §15.7–15.7.1, (15.25)–(15.27), pp. 464–466, and Appendix 15.A.2, p. 869.

* (15.25): `y − T(y) = λy^{1−τ}` (`hsvT`). For `λ, y > 0`, `T′(y) − T(y)/y = λτy^{−τ}`
  (`hsv_marginal_sub_average`), so the system is progressive (`T′ > T/y`) iff `τ > 0`, regressive
  iff `τ < 0`, and flat with `T′ = T/y = 1 − λ` when `τ = 0` (`eq_15_25`).
* The static model: `max log c − ℓ^{1+1/φ}/(1 + 1/φ)` with `c = λ(wℓ)^{1−τ}`. For `τ < 1` the
  unique maximiser over `ℓ > 0` is `ℓ* = (1 − τ)^{1/(1+1/φ)}` (`hsv_hours_optimal`), proved
  globally from `log x ≤ x − 1`; so (15.26) `log ℓ = log(1 − τ)/(1 + 1/φ)` (`eq_15_26`) and
  (15.27) `log c = log λ + (1 − τ)log(1 − τ)/(1 + 1/φ) + (1 − τ)log w` (`eq_15_27`). Hours do not
  depend on `w`, fall with `τ` (`hsv_hours_strictAntiOn`) and vanish as `τ → 1`
  (`hsv_hours_tendsto`).
* `Var(log c) = (1 − τ)²Var(log w)` for any distribution of wages (`hsv_var_log_c`).
* Appendix 15.A.2: with `u = ln c − ℓ^{1+1/φ}/(1 + 1/φ)` and hand-to-mouth workers
  `c_w = ((1 − τ_ℓ)/(1 + τ_c))wℓ`, labour supply is `ℓ = 1` whatever the taxes
  (`app_15_A_2`, `app_15_A_2_foc`).
-/

namespace AKMM.FiscalPolicy

open Real Filter Topology

/-- The HSV net tax `T(y) = y − λy^{1−τ}` (AKMM, (15.25), p. 465). -/
noncomputable def hsvT (lam τ y : ℝ) : ℝ := y - lam * y ^ (1 - τ)

/-- AKMM, p. 465: `T′(y) = 1 − λ(1 − τ)y^{−τ}` at `y > 0`. -/
theorem hsv_hasDerivAt {lam τ y : ℝ} (hy : 0 < y) :
    HasDerivAt (hsvT lam τ) (1 - lam * (1 - τ) * y ^ (-τ)) y := by
  have h := (hasDerivAt_id y).sub
    ((Real.hasDerivAt_rpow_const (p := 1 - τ) (Or.inl hy.ne')).const_mul lam)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => rfl)
  rw [show 1 - τ - 1 = -τ by ring]
  ring

/-- AKMM, p. 465: `T′(y) − T(y)/y = λτy^{−τ}` (`y > 0`). -/
theorem hsv_marginal_sub_average {lam τ y : ℝ} (hy : 0 < y) :
    (1 - lam * (1 - τ) * y ^ (-τ)) - hsvT lam τ y / y = lam * τ * y ^ (-τ) := by
  unfold hsvT
  have : y ^ (1 - τ) = y * y ^ (-τ) := by
    rw [show 1 - τ = 1 + -τ by ring, Real.rpow_add hy, Real.rpow_one]
  rw [this]
  field_simp
  ring

/-- **(15.25)** (AKMM, p. 465), for `λ, y > 0`: "when `0 < τ < 1`, the tax system is progressive in
the sense that the marginal tax rate `T′(y)` is larger than the average tax rate `T(y)/y`"
(indeed iff `τ > 0`); "when `τ < 0`, … `T′(y) < T(y)/y`"; "when `τ = 0`, …
`T′(y) = T(y)/y = 1 − λ`". -/
theorem eq_15_25 {lam τ y : ℝ} (hlam : 0 < lam) (hy : 0 < y) :
    (hsvT lam τ y / y < 1 - lam * (1 - τ) * y ^ (-τ) ↔ 0 < τ) ∧
      (1 - lam * (1 - τ) * y ^ (-τ) < hsvT lam τ y / y ↔ τ < 0) ∧
      (τ = 0 → 1 - lam * (1 - τ) * y ^ (-τ) = 1 - lam ∧ hsvT lam τ y / y = 1 - lam) := by
  have h := hsv_marginal_sub_average (lam := lam) (τ := τ) hy
  have hp : 0 < lam * y ^ (-τ) := mul_pos hlam (Real.rpow_pos_of_pos hy _)
  refine ⟨⟨fun h' => ?_, fun h' => ?_⟩, ⟨fun h' => ?_, fun h' => ?_⟩, fun h0 => ?_⟩
  · have : 0 < lam * τ * y ^ (-τ) := by linarith
    have : 0 < τ * (lam * y ^ (-τ)) := by linarith
    exact pos_of_mul_pos_left this hp.le
  · have : 0 < lam * τ * y ^ (-τ) := by
      have := mul_pos h' hp
      linarith
    linarith
  · have : lam * τ * y ^ (-τ) < 0 := by linarith
    have : τ * (lam * y ^ (-τ)) < 0 := by linarith
    by_contra hc
    push Not at hc
    exact absurd this (not_lt.mpr (mul_nonneg hc hp.le))
  · have : lam * τ * y ^ (-τ) < 0 := by
      have := mul_neg_of_neg_of_pos h' hp
      linarith
    linarith
  · subst h0
    constructor
    · simp
    · unfold hsvT
      simp only [sub_zero, Real.rpow_one]
      field_simp

/-- The worker's utility in the HSV economy as a function of hours (AKMM, p. 466):
`log(λ(wℓ)^{1−τ}) − ℓ^{1+1/φ}/(1 + 1/φ)`. -/
noncomputable def hsvObj (lam τ φ w l : ℝ) : ℝ :=
  Real.log (lam * (w * l) ^ (1 - τ)) - l ^ (1 + 1 / φ) / (1 + 1 / φ)

/-- The optimal hours `ℓ* = (1 − τ)^{1/(1+1/φ)}`. -/
noncomputable def hsvHours (τ φ : ℝ) : ℝ := (1 - τ) ^ (1 / (1 + 1 / φ))

/-- AKMM, p. 466: for `λ, w, φ > 0` and `τ < 1`, `ℓ* = (1 − τ)^{1/(1+1/φ)}` maximises the worker's
utility over `ℓ > 0`, uniquely. -/
theorem hsv_hours_optimal {lam τ φ w : ℝ} (hlam : 0 < lam) (hw : 0 < w) (hφ : 0 < φ)
    (hτ : τ < 1) :
    0 < hsvHours τ φ ∧ ∀ l, 0 < l → l ≠ hsvHours τ φ →
      hsvObj lam τ φ w l < hsvObj lam τ φ w (hsvHours τ φ) := by
  set p := 1 + 1 / φ with hp
  have hp0 : 0 < p := by positivity
  have h1τ : 0 < 1 - τ := by linarith
  have hs : 0 < hsvHours τ φ := Real.rpow_pos_of_pos h1τ _
  refine ⟨hs, fun l hl hne => ?_⟩
  have hsp : hsvHours τ φ ^ p = 1 - τ := by
    unfold hsvHours
    rw [← hp, ← Real.rpow_mul h1τ.le, one_div_mul_cancel hp0.ne', Real.rpow_one]
  -- the objective at `ℓ` equals `log λ + (1 − τ)log w + ((1 − τ)/p)log(ℓ^p) − ℓ^p/p`
  have hform : ∀ x, 0 < x → hsvObj lam τ φ w x =
      Real.log lam + (1 - τ) * Real.log w + (1 - τ) / p * Real.log (x ^ p) - x ^ p / p := by
    intro x hx
    unfold hsvObj
    rw [← hp, Real.log_mul hlam.ne' (Real.rpow_pos_of_pos (mul_pos hw hx) _).ne',
      Real.log_rpow (mul_pos hw hx), Real.log_mul hw.ne' hx.ne', Real.log_rpow hx]
    field_simp
    ring
  rw [hform l hl, hform _ hs, hsp]
  -- with `x = ℓ^p/(1 − τ) ≠ 1`, the gap is `((1 − τ)/p)(log x − (x − 1)) < 0`
  set x := l ^ p / (1 - τ) with hx
  have hx0 : 0 < x := div_pos (Real.rpow_pos_of_pos hl p) h1τ
  have hx1 : x ≠ 1 := by
    intro h1
    apply hne
    have : l ^ p = 1 - τ := by
      rw [hx, div_eq_one_iff_eq h1τ.ne'] at h1
      exact h1
    have key : ∀ z : ℝ, 0 < z → (z ^ p) ^ (1 / p) = z := fun z hz => by
      rw [← Real.rpow_mul hz.le, mul_one_div_cancel hp0.ne', Real.rpow_one]
    rw [← key l hl, this, ← hsp, key _ hs]
  have hlog : Real.log (l ^ p) = Real.log x + Real.log (1 - τ) := by
    rw [hx, Real.log_div (Real.rpow_pos_of_pos hl p).ne' h1τ.ne', sub_add_cancel]
  have hlp : l ^ p = x * (1 - τ) := by
    rw [hx]
    field_simp
  rw [hlog, hlp]
  have hlt := Real.log_lt_sub_one_of_pos hx0 hx1
  have hc : 0 < (1 - τ) / p := div_pos h1τ hp0
  have key : (1 - τ) / p * (Real.log x + Real.log (1 - τ)) - x * (1 - τ) / p -
      ((1 - τ) / p * Real.log (1 - τ) - (1 - τ) / p) =
      (1 - τ) / p * (Real.log x - (x - 1)) := by
    field_simp
    ring
  have : (1 - τ) / p * (Real.log x - (x - 1)) < 0 := mul_neg_of_pos_of_neg hc (by linarith)
  linarith

/-- **(15.26)** (AKMM, p. 466): `log ℓ = log(1 − τ)/(1 + 1/φ)`. -/
theorem eq_15_26 {τ φ : ℝ} (hτ : τ < 1) :
    Real.log (hsvHours τ φ) = Real.log (1 - τ) / (1 + 1 / φ) := by
  unfold hsvHours
  rw [Real.log_rpow (by linarith)]
  ring

/-- **(15.27)** (AKMM, p. 466): `log c = log λ + (1 − τ)log(1 − τ)/(1 + 1/φ) + (1 − τ)log w` at the
optimal hours, with `c = λ(wℓ)^{1−τ}`. -/
theorem eq_15_27 {lam τ φ w : ℝ} (hlam : 0 < lam) (hw : 0 < w) (hτ : τ < 1) :
    Real.log (lam * (w * hsvHours τ φ) ^ (1 - τ)) =
      Real.log lam + (1 - τ) * (Real.log (1 - τ) / (1 + 1 / φ)) + (1 - τ) * Real.log w := by
  have hs : 0 < hsvHours τ φ := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.log_mul hlam.ne' (Real.rpow_pos_of_pos (mul_pos hw hs) _).ne',
    Real.log_rpow (mul_pos hw hs), Real.log_mul hw.ne' hs.ne', eq_15_26 hτ]
  ring

/-- AKMM, p. 466: "Hours worked are falling in `τ`" (on `τ < 1`, `φ > 0`). -/
theorem hsv_hours_strictAntiOn {φ : ℝ} (hφ : 0 < φ) :
    StrictAntiOn (fun τ => hsvHours τ φ) (Set.Iio 1) := by
  intro a _ b hb hab
  have hb' : 0 < 1 - b := by have := Set.mem_Iio.mp hb; linarith
  exact Real.rpow_lt_rpow hb'.le (by linarith) (by positivity)

/-- AKMM, p. 466: "In the limit as `τ → 1` … hours will shrink to zero". -/
theorem hsv_hours_tendsto {φ : ℝ} (hφ : 0 < φ) :
    Tendsto (fun τ => hsvHours τ φ) (𝓝[<] 1) (𝓝 0) := by
  have he : 0 < 1 / (1 + 1 / φ) := by positivity
  have h1 : Tendsto (fun τ : ℝ => 1 - τ) (𝓝[<] 1) (𝓝[>] 0) := by
    have hc : Tendsto (fun τ : ℝ => 1 - τ) (𝓝 1) (𝓝 0) := by
      have := (continuous_sub_left (1 : ℝ)).tendsto 1
      simpa using this
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hc.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact sub_pos.mpr (Set.mem_Iio.mp hτ)
  have h2 : Tendsto (fun x : ℝ => x ^ (1 / (1 + 1 / φ))) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 (1 / (1 + 1 / φ)) (Or.inr he.le)).tendsto
    rw [Real.zero_rpow he.ne'] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact h2.comp h1

/-- AKMM, p. 466: "the variance of log consumption is `(1 − τ)²Var(log w)`": if
`log c_i = a + (1 − τ)log w_i` across individuals (15.27), for any probability distribution of
`i` under which `log w` is a.e. strongly measurable. -/
theorem hsv_var_log_c {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ] {logw : Ω → ℝ}
    (hX : MeasureTheory.AEStronglyMeasurable logw μ) (a τ : ℝ) :
    ProbabilityTheory.variance (fun i => a + (1 - τ) * logw i) μ =
      (1 - τ) ^ 2 * ProbabilityTheory.variance logw μ := by
  have h := ProbabilityTheory.variance_add_const (hX.const_mul (1 - τ)) a
  rw [← ProbabilityTheory.variance_const_mul]
  rw [← h]
  congr 1
  funext i
  ring

/-- **Appendix 15.A.2** (AKMM, p. 869): with `u = ln c − ℓ^{1+1/φ}/(1 + 1/φ)` and hand-to-mouth
workers `c_w = θwℓ`, `θ = (1 − τ_ℓ)/(1 + τ_c) > 0`, labour supply is `ℓ = 1` whatever the taxes:
`ℓ = 1` is the unique maximiser over `ℓ > 0` (the HSV problem with `τ = 0`, `λ = θ`). -/
theorem app_15_A_2 {θ φ w : ℝ} (hθ : 0 < θ) (hw : 0 < w) (hφ : 0 < φ) :
    ∀ l, 0 < l → l ≠ 1 →
      Real.log (θ * (w * l)) - l ^ (1 + 1 / φ) / (1 + 1 / φ) <
        Real.log (θ * (w * 1)) - (1 : ℝ) ^ (1 + 1 / φ) / (1 + 1 / φ) := by
  intro l hl hne
  have h := (hsv_hours_optimal (τ := 0) hθ hw hφ (by norm_num)).2 l hl
  have h1 : hsvHours 0 φ = 1 := by simp [hsvHours]
  rw [h1] at h
  have := h hne
  simpa [hsvObj] using this

/-- **Appendix 15.A.2, the first-order condition** (AKMM, p. 869):
`ℓ^{1/φ} = ((1 − τ_ℓ)/(1 + τ_c))w/c_w` with `c_w = ((1 − τ_ℓ)/(1 + τ_c))wℓ` gives `ℓ = 1`
(`ℓ > 0`, `θw ≠ 0`). The printed `c_w = ((1 − τ_ℓ)/(1 + τ_c))w` omits `ℓ`. -/
theorem app_15_A_2_foc {θ φ w l : ℝ} (hφ : 0 < φ) (hl : 0 < l) (hθw : θ * w ≠ 0)
    (h : l ^ (1 / φ) = θ * w * (1 / (θ * w * l))) : l = 1 := by
  have hθ : θ ≠ 0 := left_ne_zero_of_mul hθw
  have hw : w ≠ 0 := right_ne_zero_of_mul hθw
  have h1 : l ^ (1 / φ) * l = 1 := by
    rw [h]
    field_simp
  have h2 : l ^ (1 + 1 / φ) = 1 := by
    rw [Real.rpow_add hl, Real.rpow_one, mul_comm]
    exact h1
  have hp : 0 < 1 + 1 / φ := by positivity
  have := congrArg (fun z => z ^ (1 / (1 + 1 / φ))) h2
  simp only [Real.one_rpow] at this
  rwa [← Real.rpow_mul hl.le, mul_one_div_cancel hp.ne', Real.rpow_one] at this

end AKMM.FiscalPolicy
