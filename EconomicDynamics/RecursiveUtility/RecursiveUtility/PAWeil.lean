/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveUtility.PALucasStokey

/-!
# Exercise 20.5: precautionary saving with Weil (1993) preferences

Miao, *Economic Dynamics in Discrete Time*, Exercise 20.5 (p. 735). Utility (20.4),
`U_t = ((1 − β)c_t^{1−ρ} + β(R_t U_{t+1})^{1−ρ})^{1/(1−ρ)}` with the exponential certainty
equivalent `R_t(X) = −(1/γ) ln E_t exp(−γX)`; budget `a_{t+1} = R(a_t − c_t) + y_{t+1}`;
labour income `y_{t+1} = ρ_y y_t + (1 − ρ_y)ȳ + σ_y ε_{t+1}`, `ε` IID `N(0, 1)` (the text
prints `y_t = ρ_y y_t + …`; the lag is meant).

Guess and verify `V(a, y) = A(a + By + D)`:

* the certainty equivalent of a Gaussian, `R(m + sε) = m − γs²/2` (`pa_expCE_gaussian`), gives
  `R_t V(a_{t+1}, y_{t+1}) = A(R(a − c) + K(y))` (`ex_20_5_ce`), with
  `K(y)/R = By + D` for `B = ρ_y/(R − ρ_y)` and the `D` below (`ex_20_5_K`);
* with `1 + x = (βR^{1−ρ})^{−1/ρ}` and `A` solving `ARk = x`, `k = (βAR/(1 − β))^{−1/ρ}`
  (such an `A` exists: `ex_20_5_A`), the consumption rule
  `c = x/(1 + x) (a + By + D)` satisfies the first-order condition of the Bellman problem and
  reproduces the guess, `V(a, y) = A(a + By + D)` (`ex_20_5`);
* effects of the parameters: the marginal propensity to consume out of total wealth is
  `1 − (βR^{1−ρ})^{1/ρ}`, which depends on the EIS `1/ρ` but not on `γ` (`ex_20_5_mpc`); risk
  aversion enters only through the precautionary term
  `D = ((1 + B)(1 − ρ_y)ȳ − γA(1 + B)²σ_y²/2)/(R − 1)`, which falls as `γ` rises
  (`ex_20_5_precautionary`).

The first-order condition is verified (stationarity); its sufficiency (concavity of the
objective) is not formalised.
-/

namespace Miao.RecursiveUtility

open MeasureTheory ProbabilityTheory Real

/-- The exponential certainty equivalent `R(X) = −(1/γ) ln E exp(−γX)` of (20.4). -/
noncomputable def pa_expCE {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (X : Ω → ℝ) : ℝ :=
  -(1 / γ) * Real.log (∫ ω, Real.exp (-γ * X ω) ∂P)

/-- The exponential certainty equivalent of a Gaussian: `R(m + sε) = m − γs²/2` for
`ε ∼ N(0, 1)`. -/
theorem pa_expCE_gaussian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ε : Ω → ℝ}
    (hε : HasLaw ε (gaussianReal 0 1) P) {γ : ℝ} (hγ : γ ≠ 0) (m s : ℝ) :
    pa_expCE P γ (fun ω => m + s * ε ω) = m - γ * s ^ 2 / 2 := by
  have h := mgf_gaussianReal hε (-γ * s)
  simp only [mgf] at h
  have hint : (∫ ω, Real.exp (-γ * (m + s * ε ω)) ∂P)
      = Real.exp (-γ * m) * ∫ ω, Real.exp (-γ * s * ε ω) ∂P := by
    rw [← integral_const_mul]
    congr 1
    funext ω
    rw [← Real.exp_add]
    ring_nf
  simp only [pa_expCE]
  rw [hint, h, ← Real.exp_add, Real.log_exp]
  field_simp
  push_cast
  ring

/-- `K(y) = (1 + B)(ρ_y y + (1 − ρ_y)ȳ) + D − γA(1 + B)²σ_y²/2`. -/
noncomputable def pa_weilK (A B D γ ρy ybar σy y : ℝ) : ℝ :=
  (1 + B) * (ρy * y + (1 - ρy) * ybar) + D - γ * A * (1 + B) ^ 2 * σy ^ 2 / 2

/-- Exercise 20.5 (Miao, p. 735), the certainty-equivalent step: with
`V(a', y') = A(a' + By' + D)`, `a' = R(a − c) + y'` and
`y' = ρ_y y + (1 − ρ_y)ȳ + σ_y ε`, `R_t V(a', y') = A(R(a − c) + K(y))`. -/
theorem ex_20_5_ce {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ε : Ω → ℝ}
    (hε : HasLaw ε (gaussianReal 0 1) P) {γ : ℝ} (hγ : γ ≠ 0) (A B D R ρy ybar σy a c y : ℝ) :
    pa_expCE P γ (fun ω => A * ((R * (a - c) + (ρy * y + (1 - ρy) * ybar + σy * ε ω))
        + B * (ρy * y + (1 - ρy) * ybar + σy * ε ω) + D))
      = A * (R * (a - c) + pa_weilK A B D γ ρy ybar σy y) := by
  have := pa_expCE_gaussian hε hγ (A * (R * (a - c) + (1 + B) * (ρy * y + (1 - ρy) * ybar) + D))
    (A * (1 + B) * σy)
  rw [show (fun ω => A * ((R * (a - c) + (ρy * y + (1 - ρy) * ybar + σy * ε ω))
      + B * (ρy * y + (1 - ρy) * ybar + σy * ε ω) + D))
      = fun ω => A * (R * (a - c) + (1 + B) * (ρy * y + (1 - ρy) * ybar) + D)
        + A * (1 + B) * σy * ε ω by funext ω; ring, this]
  simp only [pa_weilK]
  ring

/-- Exercise 20.5: with `B = ρ_y/(R − ρ_y)` and
`D = ((1 + B)(1 − ρ_y)ȳ − γA(1 + B)²σ_y²/2)/(R − 1)`, `K(y)/R = By + D`. -/
theorem ex_20_5_K {A γ R ρy ybar σy : ℝ} (hR1 : R ≠ 1) (hR0 : R ≠ 0) (hRy : R ≠ ρy) (y : ℝ) :
    pa_weilK A (ρy / (R - ρy))
        (((1 + ρy / (R - ρy)) * (1 - ρy) * ybar
          - γ * A * (1 + ρy / (R - ρy)) ^ 2 * σy ^ 2 / 2) / (R - 1)) γ ρy ybar σy y / R
      = ρy / (R - ρy) * y + ((1 + ρy / (R - ρy)) * (1 - ρy) * ybar
          - γ * A * (1 + ρy / (R - ρy)) ^ 2 * σy ^ 2 / 2) / (R - 1) := by
  have h1 : R - 1 ≠ 0 := sub_ne_zero.2 hR1
  have h2 : R - ρy ≠ 0 := sub_ne_zero.2 hRy
  simp only [pa_weilK]
  field_simp
  ring

/-- Exercise 20.5: an `A > 0` solving `A R k = x`, `k = (βAR/(1 − β))^{−1/ρ}`, exists for
`x > 0`, `ρ ≠ 1`: `A = (x(β/(1 − β))^{1/ρ})^{ρ/(ρ−1)}/R`. -/
theorem ex_20_5_A {β ρ R x : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ0 : 0 < ρ) (hρ1 : ρ ≠ 1)
    (hR : 0 < R) (hx : 0 < x) :
    let A := (x * (β / (1 - β)) ^ (1 / ρ)) ^ (ρ / (ρ - 1)) / R
    0 < A ∧ A * R * (β * A * R / (1 - β)) ^ (-1 / ρ) = x := by
  intro A
  have hβ' : 0 < 1 - β := by linarith
  have hq : 0 < (β / (1 - β)) ^ (1 / ρ) := Real.rpow_pos_of_pos (div_pos hβ0 hβ') _
  have hA : 0 < A := div_pos (Real.rpow_pos_of_pos (mul_pos hx hq) _) hR
  refine ⟨hA, ?_⟩
  have hρ' : ρ - 1 ≠ 0 := sub_ne_zero.2 hρ1
  apply pa_eq_of_log_eq (by positivity) hx
  have hAR : A * R = (x * (β / (1 - β)) ^ (1 / ρ)) ^ (ρ / (ρ - 1)) := by
    simp only [A]; field_simp
  rw [show β * A * R / (1 - β) = (β / (1 - β)) * (A * R) by ring]
  rw [hAR]
  simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_div]
  field_simp
  ring

/-- The objective of the Bellman equation of Exercise 20.5 after the certainty-equivalent
step: `f(c) = ((1 − β)c^{1−ρ} + β(AR(w − c))^{1−ρ})^{1/(1−ρ)}`, where `w = a + By + D` is total
wealth (so that `A(R(a − c) + K(y)) = AR(w − c)` by `ex_20_5_K`). -/
noncomputable def pa_weilObj (β ρ A R w c : ℝ) : ℝ := pa_W β ρ c (A * R * (w - c))

/-- **Exercise 20.5** (Miao, p. 735): guess and verify. With `1 + x = (βR^{1−ρ})^{−1/ρ}`,
`x > 0`, and `A > 0` solving `ARk = x` with `k = (βAR/(1 − β))^{−1/ρ}`, the consumption
`c = x/(1 + x) w` out of total wealth `w = a + By + D > 0` is interior, satisfies the
first-order condition `f'(c) = 0`, and attains `f(c) = A w`, reproducing
`V(a, y) = A(a + By + D)`. -/
theorem ex_20_5 {β ρ R A x w : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ0 : 0 < ρ) (hρ1 : ρ ≠ 1)
    (hR : 0 < R) (hA : 0 < A) (hx1 : 1 + x = (β * R ^ (1 - ρ)) ^ (-1 / ρ)) (hx : 0 < x)
    (hk : A * R * (β * A * R / (1 - β)) ^ (-1 / ρ) = x) (hw : 0 < w) :
    0 < x / (1 + x) * w ∧ x / (1 + x) * w < w ∧
      HasDerivAt (pa_weilObj β ρ A R w) 0 (x / (1 + x) * w) ∧
      pa_weilObj β ρ A R w (x / (1 + x) * w) = A * w := by
  have hβ' : 0 < 1 - β := by linarith
  have h1x : 0 < 1 + x := by linarith
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ1)
  set c := x / (1 + x) * w with hc
  set k := (β * A * R / (1 - β)) ^ (-1 / ρ) with hkdef
  have hkpos : 0 < k := Real.rpow_pos_of_pos (by positivity) _
  have hcpos : 0 < c := by positivity
  have hcw : c < w := by
    rw [hc, div_mul_eq_mul_div, div_lt_iff₀ h1x]; nlinarith
  have hQ : A * R * (w - c) = A * R * w / (1 + x) := by
    rw [hc]; field_simp; ring
  have hQpos : 0 < A * R * (w - c) := mul_pos (mul_pos hA hR) (by linarith)
  -- `c = k Q` at the candidate
  have hcQ : c = k * (A * R * (w - c)) := by
    rw [hQ, hc]
    have : k = x / (A * R) := by rw [← hk]; field_simp
    rw [this]
    field_simp
  -- `k^{−ρ} = βAR/(1 − β)`
  have hkρ : k ^ (-ρ) = β * A * R / (1 - β) := by
    rw [hkdef, ← Real.rpow_mul (by positivity), show -1 / ρ * -ρ = 1 by field_simp,
      Real.rpow_one]
  refine ⟨hcpos, hcw, ?_, ?_⟩
  · -- the first-order condition
    have e : (1 : ℝ) - ρ - 1 = -ρ := by ring
    have hd1 : HasDerivAt (fun c : ℝ => c ^ (1 - ρ)) ((1 - ρ) * c ^ (-ρ)) c := by
      have := Real.hasDerivAt_rpow_const (x := c) (p := 1 - ρ) (Or.inl hcpos.ne')
      rwa [e] at this
    have hd2 : HasDerivAt (fun c : ℝ => (A * R * (w - c)) ^ (1 - ρ))
        (A * R * -1 * (1 - ρ) * (A * R * (w - c)) ^ (-ρ)) c := by
      have := (((hasDerivAt_id c).const_sub w).const_mul (A * R)).rpow_const (p := 1 - ρ)
        (Or.inl hQpos.ne')
      simp only [id] at this
      rw [e] at this
      exact this
    have hin := (hd1.const_mul (1 - β)).add (hd2.const_mul β)
    have hinpos : 0 < (1 - β) * c ^ (1 - ρ) + β * (A * R * (w - c)) ^ (1 - ρ) := by positivity
    have hout := hin.rpow_const (p := 1 / (1 - ρ)) (Or.inl hinpos.ne')
    have hzero : (1 - β) * ((1 - ρ) * c ^ (-ρ))
        + β * (A * R * -1 * (1 - ρ) * (A * R * (w - c)) ^ (-ρ)) = 0 := by
      have hc' : c ^ (-ρ) = k ^ (-ρ) * (A * R * (w - c)) ^ (-ρ) := by
        conv_lhs => rw [hcQ]
        rw [Real.mul_rpow hkpos.le hQpos.le]
      rw [hc', hkρ]
      field_simp
      ring
    rw [hzero, zero_mul, zero_mul] at hout
    exact hout
  · -- the value
    simp only [pa_weilObj, pa_W]
    have hk1 : (1 - β) * c ^ (1 - ρ) + β * (A * R * (w - c)) ^ (1 - ρ)
        = (A * R * (w - c)) ^ (1 - ρ) * (β * (1 + x)) := by
      have hcr : c ^ (1 - ρ) = k ^ (1 - ρ) * (A * R * (w - c)) ^ (1 - ρ) := by
        conv_lhs => rw [hcQ]
        rw [Real.mul_rpow hkpos.le hQpos.le]
      have hk1ρ : (1 - β) * k ^ (1 - ρ) = β * x := by
        rw [show (1 : ℝ) - ρ = 1 + -ρ by ring, Real.rpow_add hkpos, Real.rpow_one, hkρ, ← hk]
        field_simp
      rw [hcr, ← mul_assoc, hk1ρ]
      ring
    rw [hk1, Real.mul_rpow (Real.rpow_nonneg hQpos.le _) (by positivity), ← Real.rpow_mul
      hQpos.le, mul_one_div_cancel h1, Real.rpow_one]
    -- `(β(1 + x))^{1/(1−ρ)} = (1 + x)/R`
    have hb : (β * (1 + x)) ^ (1 / (1 - ρ)) = (1 + x) / R := by
      apply pa_eq_of_log_eq (by positivity) (by positivity)
      have hl := congrArg Real.log hx1
      rw [Real.log_rpow (by positivity), Real.log_mul hβ0.ne' (by positivity),
        Real.log_rpow hR] at hl
      rw [Real.log_rpow (by positivity), Real.log_mul hβ0.ne' h1x.ne',
        Real.log_div h1x.ne' hR.ne']
      field_simp at hl ⊢
      linear_combination hl
    rw [hb, hQ]
    field_simp

/-- Exercise 20.5: the marginal propensity to consume out of total wealth,
`x/(1 + x) = 1 − (βR^{1−ρ})^{1/ρ}`, depends on the EIS `1/ρ` (and `β`, `R`) but not on the
risk aversion `γ`. -/
theorem ex_20_5_mpc {β ρ R x : ℝ} (hβ0 : 0 < β) (hR : 0 < R)
    (hx1 : 1 + x = (β * R ^ (1 - ρ)) ^ (-1 / ρ)) :
    x / (1 + x) = 1 - (β * R ^ (1 - ρ)) ^ (1 / ρ) := by
  have hb : 0 < β * R ^ (1 - ρ) := mul_pos hβ0 (Real.rpow_pos_of_pos hR _)
  have h1x : 0 < 1 + x := by rw [hx1]; exact Real.rpow_pos_of_pos hb _
  have : 1 / (1 + x) = (β * R ^ (1 - ρ)) ^ (1 / ρ) := by
    rw [hx1, one_div, ← Real.rpow_neg hb.le]
    ring_nf
  rw [← this]
  field_simp
  ring

/-- Exercise 20.5: precautionary saving. The constant `D` of total wealth falls strictly as risk
aversion `γ` rises (for `R > 1`, `A > 0`, `1 + B ≠ 0`, `σ_y ≠ 0`), lowering consumption. -/
theorem ex_20_5_precautionary {A B R ρy ybar σy γ γ' : ℝ} (hR : 1 < R) (hA : 0 < A)
    (hB : 1 + B ≠ 0) (hσ : σy ≠ 0) (hγ : γ < γ') :
    ((1 + B) * (1 - ρy) * ybar - γ' * A * (1 + B) ^ 2 * σy ^ 2 / 2) / (R - 1)
      < ((1 + B) * (1 - ρy) * ybar - γ * A * (1 + B) ^ 2 * σy ^ 2 / 2) / (R - 1) := by
  apply div_lt_div_of_pos_right _ (by linarith)
  have : 0 < A * (1 + B) ^ 2 * σy ^ 2 := by positivity
  nlinarith

end Miao.RecursiveUtility
