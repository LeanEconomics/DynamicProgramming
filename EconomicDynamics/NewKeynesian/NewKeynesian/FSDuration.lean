/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesian.FSZLB

/-!
# Duration of fiscal stimulus: the three-state example and the multiplier (19.61)

Miao, §19.3, pp. 654–656, and Exercise 19.4 (p. 669).

Three states: the crisis `L` (`r^net = r_L`, `Ĝ = Ĝ_L`, zero bound binding, persists with
probability `μ`), the transitional state `S` (`r^net = r̄`, `Ĝ = Ĝ_L`, Taylor rule, persists with
probability `λ`, entered from `L` with probability `(1 − μ)λ`), and the absorbing normal state
(`π = Ŷ = Ĝ = 0`). From `L`, `E_tx_{t+1} = μx_L + (1 − μ)λx_S`; from `S`, `E_tx_{t+j} = λʲx_S`.

* The transitional state (`ex_19_4_transitional`): `Ŷ_S = γ_yĜ_L`, `π_S = γ_πĜ_L`, with `γ_y` of
  (19.52) at `ρ = λ` and `γ_π = κ(γ_y − Γ)/(1 − βλ)`.
* The crisis state (`fs_crisis_three_state`):
  `Ŷ_L = ϑ_r r_L + ϑ_GĜ_L + ϑ_ππ_S + ϑ_C(Ŷ_S − Ĝ_L)` with
  `ϑ_π = σ(1 − μ)λ/h(μ) = (1 − μ)λϑ_r/(1 − βμ)` and `ϑ_C = (1 − μ)λ(1 − βμ)/h(μ)`;
  `ϑ_π, ϑ_C > 0` for `λ > 0` (`fs_thetaPi_pos`).
* **Correction.** The book prints `ϑ_π ≡ (1 − μ)λϑ_r` and `ϑ_C ≡ σ⁻¹ϑ_π`. Its `ϑ_C` is right
  (`fs_thetaC_eq_printed`), but its `ϑ_π` is `(1 − βμ)` times the true coefficient
  (`fs_thetaPi_printed`), and so differs from it whenever `μ, λ > 0` (`fs_thetaPi_printed_ne`);
  consequently the printed relation `ϑ_C = σ⁻¹ϑ_π` is false for the true `ϑ_π`. With the
  corrected `ϑ_π` the numbers in the text are reproduced
  (`fs_fig_19_6_point_eight`, `fs_fig_19_6_point_nine_one`).
* (19.61) and **Exercise 19.4** (`eq_19_61`, `ex_19_4`): `dY_L/dG_L = ϑ_G + ϑ_πγ_π + ϑ_C(γ_y − 1)`
  (with the corrected `ϑ_π`). The final term is negative for `λ > 0` (`fs_eq_19_61_last_neg`); if
  `γ_y ≤ Γ` (`φ_y` large, `fs_gammaY_lt_Gamma_iff`) the multiplier is below `ϑ_G`
  (`fs_eq_19_61_lt_thetaG`); at `λ = 0` it equals `ϑ_G` (`fs_eq_19_61_lambda_zero`).
* Numerical claims of pp. 652 and 656 at the Eggertsson parameters: `γ_y(μ) ≈ 0.324`,
  `ϑ_G ≈ 2.29` ("nearly 2.3") and the multiplier `< 1` at `λ = 0.8`, `< 0` at `λ = 0.91`
  (`fs_fig_19_4_gammaY`, `fs_fig_19_6_lambda_zero`, `fs_fig_19_6_point_eight`,
  `fs_fig_19_6_point_nine_one`). Monotonicity in `λ` (Figure 19.6) is not formalised.
-/

namespace Miao.NewKeynesian

/-- `ϑ_π = σ(1 − μ)λ/h(μ)` (Miao, p. 655, corrected). -/
noncomputable def fs_thetaPi (β κ σ μ lam : ℝ) : ℝ := σ * (1 - μ) * lam / fs_h β κ σ μ

/-- `ϑ_C = (1 − μ)λ(1 − βμ)/h(μ)` (Miao, p. 655). -/
noncomputable def fs_thetaC (β κ σ μ lam : ℝ) : ℝ := (1 - μ) * lam * (1 - β * μ) / fs_h β κ σ μ

/-- The multiplier (19.61) `ϑ_G + ϑ_πγ_π + ϑ_C(γ_y − 1)`, with `γ_y`, `γ_π` at `ρ = λ`. -/
noncomputable def fs_mult61 (β κ σ μ lam Γ φπ φy : ℝ) : ℝ :=
  fs_thetaG β κ σ μ Γ +
    fs_thetaPi β κ σ μ lam * (κ * (fs_gammaY σ φy κ φπ β lam Γ - Γ) / (1 - β * lam)) +
    fs_thetaC β κ σ μ lam * (fs_gammaY σ φy κ φπ β lam Γ - 1)

/-- **Exercise 19.4**, the transitional state (Miao, p. 655): if in state `S` (19.48) holds in
the summed form with `E x_{t+j} = λʲx_S`, (19.53) holds with `r^net = r̄` and the Taylor rule
`i_S = r̄ + φ_ππ_S + φ_yŶ_S`, then `Ŷ_S = γ_yĜ_L` and `π_S = γ_πĜ_L` with `γ_y` of (19.52) at
`ρ = λ` and `γ_π = κ(γ_y − Γ)/(1 − βλ)`. -/
theorem ex_19_4_transitional {β κ σ lam Γ φπ φy rb YS gL πS iS : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ) (hl0 : 0 ≤ lam) (hl1 : lam < 1) (hφπ : 1 < φπ)
    (hφy : 0 ≤ φy)
    (h48 : πS = κ * ∑' j : ℕ, β ^ j * (lam ^ j * (YS - Γ * gL) + (1 - lam ^ j) * (0 - Γ * 0)))
    (h53 : YS - gL = lam * (YS - gL) + (1 - lam) * (0 - 0) -
      σ * (iS - (lam * πS + (1 - lam) * 0) - rb))
    (hT : iS = rb + φπ * πS + φy * YS) :
    YS = fs_gammaY σ φy κ φπ β lam Γ * gL ∧
      πS = κ * (fs_gammaY σ φy κ φπ β lam Γ - Γ) / (1 - β * lam) * gL := by
  have h56 := eq_19_56 hβ0 hβ1 hl0 hl1 h48
  have h57 := (eq_19_57 (rL := rb)).1 h53
  have hY := fs_taylor_branch hβ0 hβ1 hσ hκ hl1 hφπ hφy h56 h57 hT
  rw [sub_self, mul_zero, zero_div, add_zero] at hY
  refine ⟨hY, ?_⟩
  rw [h56, hY]
  ring

/-- The crisis state of the three-state example (Miao, p. 655): with `i_L = 0`, the Phillips
curve `π_L = κ(Ŷ_L − ΓĜ_L) + β(μπ_L + (1 − μ)λπ_S)` and the Euler equation
`Ŷ_L − Ĝ_L = μ(Ŷ_L − Ĝ_L) + (1 − μ)λ(Ŷ_S − Ĝ_L) − σ(0 − (μπ_L + (1 − μ)λπ_S) − r_L)` give
`Ŷ_L = ϑ_r r_L + ϑ_GĜ_L + ϑ_ππ_S + ϑ_C(Ŷ_S − Ĝ_L)` (when `h(μ) ≠ 0`). -/
theorem fs_crisis_three_state {β κ σ μ lam Γ YL gL πL rL YS πS : ℝ}
    (hh : fs_h β κ σ μ ≠ 0)
    (hPC : πL = κ * (YL - Γ * gL) + β * (μ * πL + (1 - μ) * lam * πS))
    (hE : YL - gL = μ * (YL - gL) + (1 - μ) * lam * (YS - gL) -
      σ * (0 - (μ * πL + (1 - μ) * lam * πS) - rL)) :
    YL = fs_thetaR β κ σ μ * rL + fs_thetaG β κ σ μ Γ * gL + fs_thetaPi β κ σ μ lam * πS +
      fs_thetaC β κ σ μ lam * (YS - gL) := by
  unfold fs_thetaR fs_thetaG fs_thetaPi fs_thetaC
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
    ← add_div, ← add_div, ← add_div, eq_div_iff hh]
  unfold fs_h
  linear_combination (1 - β * μ) * hE + σ * μ * hPC

/-- Miao, p. 655: `ϑ_π > 0` and `ϑ_C > 0` for `λ > 0` under (19.55). -/
theorem fs_thetaPi_pos {β κ σ μ lam : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hμ1 : μ < 1) (hl : 0 < lam) (h55 : κ * σ * μ < (1 - μ) * (1 - β * μ)) :
    0 < fs_thetaPi β κ σ μ lam ∧ 0 < fs_thetaC β κ σ μ lam := by
  have hh : 0 < fs_h β κ σ μ := by unfold fs_h; linarith
  have hD : 0 < 1 - β * μ := by nlinarith
  have h1 : 0 < 1 - μ := by linarith
  exact ⟨div_pos (by positivity) hh, div_pos (by positivity) hh⟩

/-- Miao, p. 655: the book's `ϑ_C = σ⁻¹ϑ_π^{book}` with `ϑ_π^{book} = (1 − μ)λϑ_r` is the true
`ϑ_C`. -/
theorem fs_thetaC_eq_printed {β κ σ μ lam : ℝ} (hσ : σ ≠ 0) :
    fs_thetaC β κ σ μ lam = σ⁻¹ * ((1 - μ) * lam * fs_thetaR β κ σ μ) := by
  unfold fs_thetaC fs_thetaR
  field_simp

/-- **Correction** (Miao, p. 655): the printed `ϑ_π ≡ (1 − μ)λϑ_r` is `(1 − βμ)` times the true
coefficient: `(1 − μ)λϑ_r = (1 − βμ)ϑ_π`. -/
theorem fs_thetaPi_printed {β κ σ μ lam : ℝ} :
    (1 - μ) * lam * fs_thetaR β κ σ μ = (1 - β * μ) * fs_thetaPi β κ σ μ lam := by
  unfold fs_thetaR fs_thetaPi
  ring

/-- **Counterexample to the printed `ϑ_π`** (Miao, p. 655): for `0 < μ < 1`, `λ > 0` and
`h(μ) ≠ 0`, `(1 − μ)λϑ_r ≠ ϑ_π`, so the printed coefficient is not the one the derivation
gives (`fs_crisis_three_state`). -/
theorem fs_thetaPi_printed_ne {β κ σ μ lam : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hμ0 : 0 < μ)
    (hμ1 : μ < 1) (hl : 0 < lam) (hh : fs_h β κ σ μ ≠ 0) :
    (1 - μ) * lam * fs_thetaR β κ σ μ ≠ fs_thetaPi β κ σ μ lam := by
  rw [fs_thetaPi_printed]
  intro h
  have hne : fs_thetaPi β κ σ μ lam ≠ 0 := by
    unfold fs_thetaPi
    have : 0 < 1 - μ := by linarith
    exact div_ne_zero (by positivity) hh
  have : (1 - β * μ) = 1 := by
    have := mul_right_cancel₀ hne (h.trans (one_mul _).symm)
    exact this
  have : β * μ = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · linarith
  · linarith

/-- **Exercise 19.4** and (19.61) (Miao, pp. 655, 669): with the transitional values
`Ŷ_S = γ_yĜ_L`, `π_S = γ_πĜ_L` (`ex_19_4_transitional`), the crisis output is
`Ŷ_L = ϑ_r r_L + (ϑ_G + ϑ_πγ_π + ϑ_C(γ_y − 1))Ĝ_L`, so the multiplier `dY_L/dG_L` is (19.61). -/
theorem eq_19_61 {β κ σ μ lam Γ φπ φy YL gL πL rL YS πS : ℝ} (hh : fs_h β κ σ μ ≠ 0)
    (hYS : YS = fs_gammaY σ φy κ φπ β lam Γ * gL)
    (hπS : πS = κ * (fs_gammaY σ φy κ φπ β lam Γ - Γ) / (1 - β * lam) * gL)
    (hPC : πL = κ * (YL - Γ * gL) + β * (μ * πL + (1 - μ) * lam * πS))
    (hE : YL - gL = μ * (YL - gL) + (1 - μ) * lam * (YS - gL) -
      σ * (0 - (μ * πL + (1 - μ) * lam * πS) - rL)) :
    YL = fs_thetaR β κ σ μ * rL + fs_mult61 β κ σ μ lam Γ φπ φy * gL := by
  rw [fs_crisis_three_state hh hPC hE, hYS, hπS]
  unfold fs_mult61
  ring

/-- **Exercise 19.4** (Miao, p. 669): the full three-state statement. In the transitional state
(19.48) (summed), (19.53) with `r̄` and the Taylor rule; in the crisis the three-state Phillips
curve and Euler equation with `i_L = 0`. Then `Ŷ_S = γ_yĜ_L`, `π_S = γ_πĜ_L` and
`Ŷ_L = ϑ_r r_L + (ϑ_G + ϑ_πγ_π + ϑ_C(γ_y − 1))Ĝ_L`, whose slope in `Ĝ_L` is the multiplier
(19.61) (`HasDerivAt` of the affine map). -/
theorem ex_19_4 {β κ σ μ lam Γ φπ φy rb rL YL gL πL YS πS iS : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ) (hl0 : 0 ≤ lam) (hl1 : lam < 1) (hφπ : 1 < φπ)
    (hφy : 0 ≤ φy) (hh : fs_h β κ σ μ ≠ 0)
    (h48 : πS = κ * ∑' j : ℕ, β ^ j * (lam ^ j * (YS - Γ * gL) + (1 - lam ^ j) * (0 - Γ * 0)))
    (h53 : YS - gL = lam * (YS - gL) + (1 - lam) * (0 - 0) -
      σ * (iS - (lam * πS + (1 - lam) * 0) - rb))
    (hT : iS = rb + φπ * πS + φy * YS)
    (hPC : πL = κ * (YL - Γ * gL) + β * (μ * πL + (1 - μ) * lam * πS))
    (hE : YL - gL = μ * (YL - gL) + (1 - μ) * lam * (YS - gL) -
      σ * (0 - (μ * πL + (1 - μ) * lam * πS) - rL)) :
    YS = fs_gammaY σ φy κ φπ β lam Γ * gL ∧
      πS = κ * (fs_gammaY σ φy κ φπ β lam Γ - Γ) / (1 - β * lam) * gL ∧
      YL = fs_thetaR β κ σ μ * rL + fs_mult61 β κ σ μ lam Γ φπ φy * gL ∧
      HasDerivAt (fun g => fs_thetaR β κ σ μ * rL + fs_mult61 β κ σ μ lam Γ φπ φy * g)
        (fs_mult61 β κ σ μ lam Γ φπ φy) gL := by
  obtain ⟨hYS, hπS⟩ := ex_19_4_transitional hβ0 hβ1 hσ hκ hl0 hl1 hφπ hφy h48 h53 hT
  refine ⟨hYS, hπS, eq_19_61 hh hYS hπS hPC hE, ?_⟩
  simpa using ((hasDerivAt_id gL).const_mul (fs_mult61 β κ σ μ lam Γ φπ φy)).const_add
    (fs_thetaR β κ σ μ * rL)

/-- Miao, p. 655: "Since `γ_y < 1` ... the contribution of the final term is necessarily
negative": `ϑ_C(γ_y − 1) < 0` for `λ > 0`. -/
theorem fs_eq_19_61_last_neg {β κ σ μ lam Γ φπ φy : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hκ : 0 < κ) (hμ1 : μ < 1) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hφπ : 1 < φπ) (hφy : 0 ≤ φy) (hΓ : Γ < 1) (h55 : κ * σ * μ < (1 - μ) * (1 - β * μ)) :
    fs_thetaC β κ σ μ lam * (fs_gammaY σ φy κ φπ β lam Γ - 1) < 0 :=
  mul_neg_of_pos_of_neg (fs_thetaPi_pos hβ0 hβ1 hσ hμ1 hl0 h55).2
    (sub_neg.2 (fs_gammaY_lt_one hσ hφy hκ hβ0 hβ1 hl1 hφπ hΓ))

/-- Miao, p. 656: if the Taylor rule is aggressive enough that `γ_y ≤ Γ` (for instance `φ_y`
large, `fs_gammaY_lt_Gamma_iff`), the multiplier (19.61) is smaller than `ϑ_G` when `λ > 0`. -/
theorem fs_eq_19_61_lt_thetaG {β κ σ μ lam Γ φπ φy : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hκ : 0 < κ) (hμ1 : μ < 1) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hφπ : 1 < φπ) (hφy : 0 ≤ φy) (hΓ : Γ < 1) (h55 : κ * σ * μ < (1 - μ) * (1 - β * μ))
    (hγ : fs_gammaY σ φy κ φπ β lam Γ ≤ Γ) :
    fs_mult61 β κ σ μ lam Γ φπ φy < fs_thetaG β κ σ μ Γ := by
  have hlast := fs_eq_19_61_last_neg hβ0 hβ1 hσ hκ hμ1 hl0 hl1 hφπ hφy hΓ h55
  have hpi := (fs_thetaPi_pos hβ0 hβ1 hσ hμ1 hl0 h55).1
  have hD : 0 < 1 - β * lam := by nlinarith
  have hγπ : κ * (fs_gammaY σ φy κ φπ β lam Γ - Γ) / (1 - β * lam) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hκ.le (by linarith)) hD.le
  have := mul_nonpos_of_nonneg_of_nonpos hpi.le hγπ
  unfold fs_mult61
  linarith

/-- Miao, p. 656: at `λ = 0` the multiplier (19.61) is `ϑ_G`. -/
theorem fs_eq_19_61_lambda_zero {β κ σ μ Γ φπ φy : ℝ} :
    fs_mult61 β κ σ μ 0 Γ φπ φy = fs_thetaG β κ σ μ Γ := by
  simp [fs_mult61, fs_thetaPi, fs_thetaC]

/-- Miao, p. 652 (Figure 19.4): at `β = 0.997`, `κ = 0.00859`, `σ = 0.862`, `Γ = 0.425`,
`φ_π = 1.5`, `φ_y = 0.25`, `μ = 0.903`, the Taylor-branch multiplier is
`γ_y(μ) ∈ (0.324, 0.325)`, and (19.55) holds. -/
theorem fs_fig_19_4_gammaY :
    (0.324 : ℝ) < fs_gammaY 0.862 0.25 0.00859 1.5 0.997 0.903 0.425 ∧
      fs_gammaY 0.862 0.25 0.00859 1.5 0.997 0.903 0.425 < 0.325 ∧
      (0.00859 : ℝ) * 0.862 * 0.903 < (1 - 0.903) * (1 - 0.997 * 0.903) := by
  unfold fs_gammaY fs_psi
  norm_num

/-- Miao, p. 656 (Figure 19.6): at the same parameters with `λ = 0`, the multiplier is
`ϑ_G ∈ (2.28, 2.29)` ("nearly 2.3"). -/
theorem fs_fig_19_6_lambda_zero :
    (2.28 : ℝ) < fs_mult61 0.997 0.00859 0.862 0.903 0 0.425 1.5 0.25 ∧
      fs_mult61 0.997 0.00859 0.862 0.903 0 0.425 1.5 0.25 < 2.29 := by
  rw [fs_eq_19_61_lambda_zero]
  unfold fs_thetaG fs_h
  norm_num

/-- Miao, p. 656 (Figure 19.6): at `λ = 0.8` the multiplier (19.61) (with the corrected `ϑ_π`)
is below one. -/
theorem fs_fig_19_6_point_eight :
    fs_mult61 0.997 0.00859 0.862 0.903 0.8 0.425 1.5 0.25 < 1 := by
  unfold fs_mult61 fs_thetaG fs_thetaPi fs_thetaC fs_gammaY fs_psi fs_h
  norm_num

/-- Miao, p. 656 (Figure 19.6): at `λ = 0.91` the multiplier (19.61) (with the corrected `ϑ_π`)
is negative. With the printed `ϑ_π = (1 − μ)λϑ_r` it would be positive (about `0.23`), so the
text's numbers confirm the correction. -/
theorem fs_fig_19_6_point_nine_one :
    fs_mult61 0.997 0.00859 0.862 0.903 0.91 0.425 1.5 0.25 < 0 ∧
      0 < fs_thetaG 0.997 0.00859 0.862 0.903 0.425 +
        (1 - 0.903) * 0.91 * fs_thetaR 0.997 0.00859 0.862 0.903 *
          (0.00859 * (fs_gammaY 0.862 0.25 0.00859 1.5 0.997 0.91 0.425 - 0.425) /
            (1 - 0.997 * 0.91)) +
        fs_thetaC 0.997 0.00859 0.862 0.903 0.91 *
          (fs_gammaY 0.862 0.25 0.00859 1.5 0.997 0.91 0.425 - 1) := by
  unfold fs_mult61 fs_thetaG fs_thetaPi fs_thetaC fs_thetaR fs_gammaY fs_psi fs_h
  norm_num

end Miao.NewKeynesian
