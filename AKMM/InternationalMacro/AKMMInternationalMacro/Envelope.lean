/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMInternationalMacro.Armington

/-!
# The Lagrange multiplier as the marginal utility of income

AKMM, §23.3.2, the box "Lagrange multiplier as the marginal utility of income (wealth)",
p. 712.

A consumer with increasing utility `u` of the Armington aggregate (23.2) and income `Y` chooses
`(c_H, c_F)` subject to `p_H c_H + p_F c_F = Y`. By duality (`eq_23_3_cost_min`) the maximised
utility is `u(Y/P)`, attained at the demands (23.3) (`env_value`); its derivative in income is
`u′(Y/P)/P = χ`, the multiplier of the first-order condition `u′(C) = χP` (`env_hasDerivAt`); and
when `u′` is strictly decreasing (strict concavity) `χ` is strictly decreasing in income
(`env_chi_strictAntiOn`). The CRRA utility of (23.1) is an instance (`env_crra`).
-/

namespace AKMM.InternationalMacro

open Real Set
open ObstfeldRogoff.RealExchangeRate.CESIndex (cesIndex)
open ObstfeldRogoff.StickyPriceModels (cesDemand)
open ObstfeldRogoff.StickyPriceModels.ReduxPrimitives (blocPriceIndex blocPriceIndex_pos)

/-- AKMM, box p. 712: "the maximum utility equals `u(Y/P)`". For `u` increasing on `(0, ∞)`,
every interior bundle with `p_H c_H + p_F c_F = Y` gives at most `u(Y/P)`, and the demands (23.3)
at `C = Y/P` exhaust income and give exactly `u(Y/P)`. -/
theorem env_value {u : ℝ → ℝ} {a φ pH pF Y : ℝ} (hu : MonotoneOn u (Ioi 0)) (ha0 : 0 < a)
    (ha1 : a < 1) (hφ0 : 0 < φ) (hφ : φ ≠ 1) (hpH : 0 < pH) (hpF : 0 < pF) (hY : 0 < Y) :
    (∀ cH cF : ℝ, 0 < cH → 0 < cF → pH * cH + pF * cF = Y →
      u (cesIndex a φ cH cF) ≤ u (Y / blocPriceIndex φ a pH pF)) ∧
    pH * (a * cesDemand φ pH (blocPriceIndex φ a pH pF) (Y / blocPriceIndex φ a pH pF))
      + pF * ((1 - a) * cesDemand φ pF (blocPriceIndex φ a pH pF)
        (Y / blocPriceIndex φ a pH pF)) = Y ∧
    u (cesIndex a φ (a * cesDemand φ pH (blocPriceIndex φ a pH pF) (Y / blocPriceIndex φ a pH pF))
      ((1 - a) * cesDemand φ pF (blocPriceIndex φ a pH pF) (Y / blocPriceIndex φ a pH pF)))
      = u (Y / blocPriceIndex φ a pH pF) := by
  have hP := blocPriceIndex_pos (θ := φ) ha0 ha1 hpH hpF
  have h1a : 0 < 1 - a := by linarith
  refine ⟨fun cH cF hcH hcF hb => ?_, ?_, ?_⟩
  · have hle := eq_23_3_cost_min ha0 ha1 hφ0 hφ hpH hpF hcH.le hcF.le (fun _ => ⟨hcH, hcF⟩)
      (by rw [hb]; exact hY)
    rw [hb] at hle
    have hpos : 0 < cesIndex a φ cH cF := by unfold cesIndex; positivity
    exact hu hpos (div_pos hY hP) ((le_div_iff₀ hP).mpr (by linarith))
  · rw [eq_23_3_spending ha0 ha1 hφ hpH hpF]
    field_simp
  · rw [eq_23_3_index ha0 ha1 hφ0 hφ hpH hpF (div_pos hY hP)]

/-- AKMM, box p. 712: "the derivative of maximized utility with respect to income, `Y`, equals
`u′(Y/P)/P = χ`", where the first-order condition is `u′(C) = χP` at `C = Y/P`. -/
theorem env_hasDerivAt {u : ℝ → ℝ} {du : ℝ} {P Y : ℝ} (hP : P ≠ 0)
    (hu : HasDerivAt u du (Y / P)) :
    HasDerivAt (fun y => u (y / P)) (du / P) Y ∧ du = (du / P) * P := by
  refine ⟨?_, by field_simp⟩
  have h : HasDerivAt (fun y => u (y / P)) (du * (1 / P)) Y :=
    hu.comp Y ((hasDerivAt_id' Y).div_const P)
  exact h.congr_deriv (by ring)

/-- AKMM, box p. 712: "Given a strictly concave utility function `u`, therefore, `χ` is strictly
decreasing in income": if `u′` is strictly decreasing on `(0, ∞)` then
`Y ↦ u′(Y/P)/P` is strictly decreasing on `(0, ∞)`. -/
theorem env_chi_strictAntiOn {du : ℝ → ℝ} {P : ℝ} (hdu : StrictAntiOn du (Ioi 0)) (hP : 0 < P) :
    StrictAntiOn (fun Y => du (Y / P) / P) (Ioi 0) := by
  intro Y₁ h₁ Y₂ h₂ h12
  simp only [mem_Ioi] at h₁ h₂
  have := hdu (div_pos h₁ hP) (div_pos h₂ hP) (div_lt_div_of_pos_right h12 hP)
  exact div_lt_div_of_pos_right this hP

/-- AKMM, (23.1) and box p. 712: for CRRA utility `u(C) = (C^{1−σ} − 1)/(1 − σ)` (`σ > 0`,
`σ ≠ 1`), `u′(C) = C^{−σ}`, which is strictly decreasing, so `χ = (Y/P)^{−σ}/P` is strictly
decreasing in income. -/
theorem env_crra {σ P : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hP : 0 < P) :
    (∀ C : ℝ, 0 < C → HasDerivAt (fun c => (c ^ (1 - σ) - 1) / (1 - σ)) (C ^ (-σ)) C) ∧
      StrictAntiOn (fun Y => (Y / P) ^ (-σ) / P) (Ioi 0) := by
  have h1 : 1 - σ ≠ 0 := sub_ne_zero.mpr (Ne.symm hσ1)
  refine ⟨fun C hC => ?_, ?_⟩
  · have h := ((hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hC.ne')).sub_const 1).div_const (1 - σ)
    refine h.congr_deriv ?_
    rw [show 1 - σ - 1 = -σ by ring]
    field_simp
  · apply env_chi_strictAntiOn (du := fun c => c ^ (-σ)) _ hP
    intro x hx y hy hxy
    exact rpow_lt_rpow_of_neg hx hxy (by linarith)

end AKMM.InternationalMacro
