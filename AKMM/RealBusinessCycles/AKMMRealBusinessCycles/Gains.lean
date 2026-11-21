/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Gain functions of linear filters

AKMM, Appendix 14.A, pp. 864–865.

* **The first difference** `C(L) = 1 − L`: `|1 − e^{−iω}|² = 2(1 − cos ω)`, so the gain is
  `√(2(1 − cos ω))` (`appx_gain_diff_sq`, `appx_gain_diff`); it is `0` at `ω = 0` and strictly
  increasing on `[0, π]` up to `2` (`appx_gain_diff_mono`).
* **The HP cyclical filter** `C(L) = λ(1 − L)²(1 − L⁻¹)²/(1 + λ(1 − L)²(1 − L⁻¹)²)`: since
  `(1 − e^{−iω})(1 − e^{iω}) = 2(1 − cos ω)` (`appx_diff_prod`),
  `C(e^{−iω}) = 4λ(1 − cos ω)²/(1 + 4λ(1 − cos ω)²)` (`appx_hp_gain_eq`, `hpGain`). It lies in
  `[0, 1)` (`appx_hp_gain_bounds`), vanishes at `ω = 0` (`appx_hp_gain_zero`), is strictly
  increasing on `[0, π]` (`appx_hp_gain_mono`) and tends to `1` as `λ → ∞` for `ω ∈ (0, π]`
  (`appx_hp_gain_limit`).
* A larger `λ` means **more** smoothing: the gain of the trend filter, `1 − C`, is
  `1/(1 + 4λ(1 − cos ω)²)`, strictly decreasing in `λ` for `ω ∈ (0, π]`
  (`appx_hp_trend_gain_anti`).
* **The ideal band-pass filter** with gain `1` on `ω₁ ≤ |ω| ≤ ω₂` and `0` elsewhere has
  coefficients `b_k = (1/2π)∫ G(ω)e^{ikω}dω = (sin kω₂ − sin kω₁)/(πk)` for `k ≠ 0`
  (`appx_bandpass_coeff`) and `b₀ = (ω₂ − ω₁)/π` (`appx_bandpass_coeff_zero`).
-/

namespace AKMM.RealBusinessCycles

open Complex Filter Topology

/-- `e^{ix} − e^{−ix} = 2i sin x` for real `x`. -/
theorem appx_exp_sub_exp (x : ℝ) :
    Complex.exp (x * I) - Complex.exp (-x * I) = 2 * Real.sin x * I := by
  rw [show (-x : ℂ) = ((-x : ℝ) : ℂ) by push_cast; ring, exp_mul_I, exp_mul_I, ← ofReal_cos,
    ← ofReal_sin, ← ofReal_cos, ← ofReal_sin, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-- `(1 − e^{−iω})(1 − e^{iω}) = 2(1 − cos ω)`. -/
theorem appx_diff_prod (ω : ℝ) :
    (1 - Complex.exp (-ω * I)) * (1 - Complex.exp (ω * I)) = 2 * (1 - Real.cos ω) := by
  have h : Complex.exp (-ω * I) * Complex.exp (ω * I) = 1 := by
    rw [← Complex.exp_add]; simp
  have hc : Complex.exp (ω * I) + Complex.exp (-ω * I) = 2 * Real.cos ω := by
    rw [show (-ω : ℂ) = ((-ω : ℝ) : ℂ) by push_cast; ring, exp_mul_I, exp_mul_I, ← ofReal_cos,
      ← ofReal_sin, ← ofReal_cos, ← ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  linear_combination h - hc

/-- **AKMM, p. 865: the squared gain of the first difference** `|1 − e^{−iω}|² = 2(1 − cos ω)`. -/
theorem appx_gain_diff_sq (ω : ℝ) :
    Complex.normSq (1 - Complex.exp (-ω * I)) = 2 * (1 - Real.cos ω) := by
  have hconj : (starRingEnd ℂ) (1 - Complex.exp (-ω * I)) = 1 - Complex.exp (ω * I) := by
    rw [map_sub, map_one, ← Complex.exp_conj]
    congr 2
    simp [Complex.conj_ofReal]
  have := Complex.mul_conj (1 - Complex.exp (-ω * I))
  rw [hconj, appx_diff_prod] at this
  exact_mod_cast this.symm

/-- **AKMM, p. 865: the gain of the first difference** `G(ω) = |1 − e^{−iω}| = √(2(1 − cos ω))`. -/
theorem appx_gain_diff (ω : ℝ) : ‖1 - Complex.exp (-ω * I)‖ = Real.sqrt (2 * (1 - Real.cos ω)) := by
  rw [← appx_gain_diff_sq, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- AKMM, p. 865: the first difference "fully attenuates" frequency `0` and its gain is strictly
increasing on `[0, π]`, reaching `2` at `π`. -/
theorem appx_gain_diff_mono :
    Real.sqrt (2 * (1 - Real.cos 0)) = 0 ∧ Real.sqrt (2 * (1 - Real.cos Real.pi)) = 2 ∧
      StrictMonoOn (fun ω => Real.sqrt (2 * (1 - Real.cos ω))) (Set.Icc 0 Real.pi) := by
  refine ⟨by simp, ?_, fun a ha b hb hab => ?_⟩
  · rw [Real.cos_pi, show (2 : ℝ) * (1 - -1) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  · have hc := Real.strictAntiOn_cos ha hb hab
    have h0 : 0 ≤ 2 * (1 - Real.cos a) := by linarith [Real.cos_le_one a]
    exact Real.sqrt_lt_sqrt h0 (by linarith)

/-- The gain of the HP cyclical filter, `4λ(1 − cos ω)²/(1 + 4λ(1 − cos ω)²)`. -/
noncomputable def hpGain (lam ω : ℝ) : ℝ :=
  4 * lam * (1 - Real.cos ω) ^ 2 / (1 + 4 * lam * (1 - Real.cos ω) ^ 2)

/-- **AKMM, p. 865: the HP filter's frequency response.** With `x = (1 − e^{−iω})²(1 − e^{iω})²`,
`λx/(1 + λx) = 4λ(1 − cos ω)²/(1 + 4λ(1 − cos ω)²)`, a real number. -/
theorem appx_hp_gain_eq (lam ω : ℝ) :
    lam * ((1 - Complex.exp (-ω * I)) ^ 2 * (1 - Complex.exp (ω * I)) ^ 2) /
      (1 + lam * ((1 - Complex.exp (-ω * I)) ^ 2 * (1 - Complex.exp (ω * I)) ^ 2)) =
      (hpGain lam ω : ℂ) := by
  have h : (1 - Complex.exp (-ω * I)) ^ 2 * (1 - Complex.exp (ω * I)) ^ 2 =
      4 * (1 - Real.cos ω) ^ 2 := by
    rw [← mul_pow, appx_diff_prod]; ring
  rw [h, hpGain]
  push_cast
  ring

theorem appx_hp_den_pos {lam : ℝ} (hlam : 0 ≤ lam) (ω : ℝ) :
    0 < 1 + 4 * lam * (1 - Real.cos ω) ^ 2 := by positivity

/-- The HP gain lies in `[0, 1)` for `λ ≥ 0`. -/
theorem appx_hp_gain_bounds {lam : ℝ} (hlam : 0 ≤ lam) (ω : ℝ) :
    0 ≤ hpGain lam ω ∧ hpGain lam ω < 1 := by
  have hd := appx_hp_den_pos hlam ω
  unfold hpGain
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hd]
  linarith

/-- AKMM, p. 865: "at very low frequencies … the gain function `G(ω) ≈ 0`": `G(0) = 0`. -/
theorem appx_hp_gain_zero (lam : ℝ) : hpGain lam 0 = 0 := by simp [hpGain]

/-- AKMM, p. 865: the HP filter removes low frequencies more than high ones: for `λ > 0` its gain
is strictly increasing on `[0, π]`. -/
theorem appx_hp_gain_mono {lam : ℝ} (hlam : 0 < lam) :
    StrictMonoOn (hpGain lam) (Set.Icc 0 Real.pi) := by
  intro a ha b hb hab
  have hc := Real.strictAntiOn_cos ha hb hab
  have hxa : 0 ≤ 1 - Real.cos a := by linarith [Real.cos_le_one a]
  have hx : (1 - Real.cos a) ^ 2 < (1 - Real.cos b) ^ 2 := by nlinarith
  unfold hpGain
  have h1 := appx_hp_den_pos hlam.le a
  have h2 := appx_hp_den_pos hlam.le b
  rw [div_lt_div_iff₀ h1 h2]
  nlinarith

theorem appx_cos_lt_one {ω : ℝ} (h0 : 0 < ω) (h1 : ω ≤ Real.pi) : 0 < 1 - Real.cos ω := by
  have := Real.strictAntiOn_cos (Set.left_mem_Icc.2 Real.pi_pos.le) ⟨h0.le, h1⟩ h0
  rw [Real.cos_zero] at this
  linarith

/-- AKMM, p. 865: "the spectrum of the filtered series converges to that of the original time
series": for `ω ∈ (0, π]`, `G(ω) → 1` as `λ → ∞`. -/
theorem appx_hp_gain_limit {ω : ℝ} (h0 : 0 < ω) (h1 : ω ≤ Real.pi) :
    Tendsto (fun lam => hpGain lam ω) atTop (𝓝 1) := by
  set a := 4 * (1 - Real.cos ω) ^ 2
  have ha : 0 < a := by have := appx_cos_lt_one h0 h1; positivity
  have e : ∀ lam, 0 < lam → hpGain lam ω = 1 - 1 / (1 + lam * a) := fun lam hl => by
    have : 0 < 1 + lam * a := by positivity
    unfold hpGain; simp only [a]; field_simp; ring
  have ht : Tendsto (fun lam : ℝ => 1 + lam * a) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_id.atTop_mul_const ha)
  have := (ht.inv_tendsto_atTop).const_sub 1
  simp only [sub_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with lam hl
  rw [e lam hl, one_div]
  rfl

/-- AKMM, p. 865, corrected: a larger `λ` gives **more** smoothing: the gain of the trend filter
`1 − C(e^{−iω}) = 1/(1 + 4λ(1 − cos ω)²)` is strictly decreasing in `λ` at every `ω ∈ (0, π]`. -/
theorem appx_hp_trend_gain_anti {ω : ℝ} (h0 : 0 < ω) (h1 : ω ≤ Real.pi) :
    (∀ lam, 0 ≤ lam → 1 - hpGain lam ω = 1 / (1 + 4 * lam * (1 - Real.cos ω) ^ 2)) ∧
      StrictAntiOn (fun lam => 1 / (1 + 4 * lam * (1 - Real.cos ω) ^ 2)) (Set.Ici 0) := by
  have hx : 0 < (1 - Real.cos ω) ^ 2 := by have := appx_cos_lt_one h0 h1; positivity
  refine ⟨fun lam hl => ?_, fun a ha b hb hab => ?_⟩
  · have := appx_hp_den_pos hl ω
    unfold hpGain; field_simp; ring
  · simp only [Set.mem_Ici] at ha hb
    have h1 := appx_hp_den_pos ha ω
    exact one_div_lt_one_div_of_lt h1 (by nlinarith)

/-- **AKMM, p. 865: the ideal band-pass filter's coefficients.** With gain `1` on
`ω₁ ≤ |ω| ≤ ω₂` and `0` elsewhere, for `k ≠ 0`,
`(1/2π)(∫_{ω₁}^{ω₂}e^{ikω}dω + ∫_{−ω₂}^{−ω₁}e^{ikω}dω) = (sin kω₂ − sin kω₁)/(πk)`. -/
theorem appx_bandpass_coeff {k : ℝ} (hk : k ≠ 0) (ω₁ ω₂ : ℝ) :
    (1 / (2 * Real.pi) : ℂ) * ((∫ ω in ω₁..ω₂, Complex.exp (k * I * ω)) +
      ∫ ω in (-ω₂)..(-ω₁), Complex.exp (k * I * ω)) =
      ((Real.sin (k * ω₂) - Real.sin (k * ω₁)) / (Real.pi * k) : ℝ) := by
  have hc : (k : ℂ) * I ≠ 0 := mul_ne_zero (ofReal_ne_zero.2 hk) I_ne_zero
  rw [integral_exp_mul_complex hc, integral_exp_mul_complex hc]
  have hS : ∀ x : ℝ, Complex.exp (k * I * x) - Complex.exp (k * I * ((-x : ℝ) : ℂ)) =
      2 * Real.sin (k * x) * I := fun x => by
    have := appx_exp_sub_exp (k * x)
    rw [← this]
    push_cast
    ring_nf
  have h2 := hS ω₂
  have h1 := hS ω₁
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hk' : (k : ℂ) ≠ 0 := ofReal_ne_zero.2 hk
  have e : (Complex.exp (k * I * ω₂) - Complex.exp (k * I * ω₁)) / (k * I) +
      (Complex.exp (k * I * ((-ω₁ : ℝ) : ℂ)) - Complex.exp (k * I * ((-ω₂ : ℝ) : ℂ))) / (k * I) =
      ((Complex.exp (k * I * ω₂) - Complex.exp (k * I * ((-ω₂ : ℝ) : ℂ))) -
        (Complex.exp (k * I * ω₁) - Complex.exp (k * I * ((-ω₁ : ℝ) : ℂ)))) / (k * I) := by
    ring
  rw [e, h1, h2]
  push_cast
  field_simp

/-- AKMM, p. 865: the central band-pass coefficient `b₀ = (ω₂ − ω₁)/π`
(`(1/2π)` times the length of the two bands). -/
theorem appx_bandpass_coeff_zero (ω₁ ω₂ : ℝ) :
    1 / (2 * Real.pi) * ((∫ _ in ω₁..ω₂, (1 : ℝ)) + ∫ _ in (-ω₂)..(-ω₁), (1 : ℝ)) =
      (ω₂ - ω₁) / Real.pi := by
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
  field_simp
  ring

end AKMM.RealBusinessCycles
