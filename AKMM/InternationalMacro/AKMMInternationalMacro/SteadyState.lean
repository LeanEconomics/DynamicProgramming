/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMInternationalMacro.PPP

/-!
# The symmetric steady state

AKMM, §23.3.3, p. 714: "We log-linearize the model around its symmetric non-stochastic steady
state with `Q = TOT = 1`".

Take symmetric endowments `Y_H = Y*_F = Y`, symmetric home bias `a*_H = 1 − a`, and the home good
as numeraire (`p_H = 1`, `p_F = T`). Under financial autarky (23.15) consumption is `C = Y/P`,
`C* = TY/P*`, and an equilibrium is a `T > 0` clearing the market for the home good (the foreign
market then clears by Walras' law, `ss_walras`). We prove:

* the excess demand for the home good is `Y[a/A + (1 − a)T/B − 1]` with
  `A = a + (1 − a)T^{1−φ}`, `B = (1 − a) + aT^{1−φ}`, and it vanishes iff
  `a(T − T^{2(1−φ)}) + (1 − a)T^{1−φ}(T − 1) = 0` (`ss_excess_eq`, `ss_equilibrium_iff`);
* **existence**: `T = 1` is an equilibrium, with `Q = 1`, `C = C* = Y`, `W = 1`
  (`ss_exists`), and it is also the complete-markets allocation with `κ₀ = 1` (`ss_cm_exists`);
* **uniqueness** for `φ ≥ 1/2`: `T = 1` is the only equilibrium (`ss_unique`);
* **non-uniqueness** with strong complementarity: for `a = 9/10`, `φ = 1/4` (below the threshold
  `1 − 1/(2a) = 4/9`) the autarky economy with symmetric endowments has a second equilibrium
  `T = ((9 + √77)/2)⁴ ≠ 1` (`ss_multiple`). The symmetric steady state the book linearises
  around exists for all parameters, but is not the only stationary equilibrium.
-/

namespace AKMM.InternationalMacro

open Real
open ObstfeldRogoff.RealExchangeRate.CESIndex (cesPrice cesPrice_pos cesPrice_rpow_one_sub)
open ObstfeldRogoff.StickyPriceModels (cesDemand)

/-- The excess demand for the home good under financial autarky with symmetric endowments `Y`,
`p_H = 1` and `p_F = T`: home demand (23.3) at `C = Y/P` plus foreign demand at `C* = TY/P*`,
minus supply. -/
noncomputable def ssExcess (a φ Y T : ℝ) : ℝ :=
  a * cesDemand φ 1 (cesPrice a φ T) (Y / cesPrice a φ T)
    + (1 - a) * cesDemand φ 1 (cesPrice (1 - a) φ T) (T * Y / cesPrice (1 - a) φ T) - Y

/-- The excess demand for the foreign good in the same economy. -/
noncomputable def ssExcessF (a φ Y T : ℝ) : ℝ :=
  (1 - a) * cesDemand φ T (cesPrice a φ T) (Y / cesPrice a φ T)
    + a * cesDemand φ T (cesPrice (1 - a) φ T) (T * Y / cesPrice (1 - a) φ T) - Y

/-- `(1/P)^{−φ} · X/P = X/P^{1−φ}`. -/
theorem ss_demand_one {φ P X : ℝ} (hP : 0 < P) :
    cesDemand φ 1 P (X / P) = X / P ^ (1 - φ) := by
  unfold cesDemand
  rw [one_div, inv_rpow hP.le, rpow_neg hP.le, inv_inv, rpow_sub hP, rpow_one]
  have := (rpow_pos_of_pos hP φ).ne'
  field_simp

/-- The closed form of the home-good excess demand. -/
theorem ss_excess_eq {a φ Y T : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1) (hT : 0 < T) :
    ssExcess a φ Y T = Y * (a / (a + (1 - a) * T ^ (1 - φ))
      + (1 - a) * T / ((1 - a) + (1 - (1 - a)) * T ^ (1 - φ)) - 1) := by
  have h1a : 0 < 1 - a := by linarith
  unfold ssExcess
  rw [ss_demand_one (cesPrice_pos ha0 ha1 hT), ss_demand_one (cesPrice_pos h1a (by linarith) hT),
    cesPrice_rpow_one_sub ha0 ha1 hT hφ, cesPrice_rpow_one_sub h1a (by linarith) hT hφ]
  ring

/-- **Walras' law** (AKMM p. 707, market clearing): with the autarky budgets, the value of the
two excess demands is zero, `ED_H + T·ED_F = 0`; so when the home-good market clears, so does
the foreign-good market. -/
theorem ss_walras {a φ Y T : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1) (hT : 0 < T) :
    ssExcess a φ Y T + T * ssExcessF a φ Y T = 0 := by
  have h1a : 0 < 1 - a := by linarith
  have b1 := eq_23_3_spending (C := Y / cesPrice a φ T) ha0 ha1 hφ one_pos hT
  have b2 := eq_23_3_spending (C := T * Y / cesPrice (1 - a) φ T) h1a (by linarith : 1 - a < 1)
    hφ one_pos hT
  have hP1 : ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.blocPriceIndex φ a 1 T
      = cesPrice a φ T := by
    rw [armington_price_homog ha0 ha1 hφ one_pos hT, one_mul, div_one]
  have hP2 : ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.blocPriceIndex φ (1 - a) 1 T
      = cesPrice (1 - a) φ T := by
    rw [armington_price_homog h1a (by linarith) hφ one_pos hT, one_mul, div_one]
  rw [hP1] at b1
  rw [hP2] at b2
  have hc1 := (cesPrice_pos (θ := φ) ha0 ha1 hT).ne'
  have hc2 := (cesPrice_pos (θ := φ) h1a (by linarith) hT).ne'
  rw [one_mul, mul_div_cancel₀ _ hc1] at b1
  rw [one_mul, sub_sub_cancel, mul_div_cancel₀ _ hc2] at b2
  unfold ssExcess ssExcessF
  linear_combination b1 + b2

/-- The equilibrium condition in polynomial form: for `T > 0`, the home-good market clears iff
`a(T − T^{1−φ}T^{1−φ}) + (1 − a)T^{1−φ}(T − 1) = 0`. -/
theorem ss_equilibrium_iff {a φ Y T : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1) (hY : 0 < Y)
    (hT : 0 < T) :
    ssExcess a φ Y T = 0 ↔
      a * (T - T ^ (1 - φ) * T ^ (1 - φ)) + (1 - a) * T ^ (1 - φ) * (T - 1) = 0 := by
  have h1a : 0 < 1 - a := by linarith
  have hx := rpow_pos_of_pos hT (1 - φ)
  have hA : 0 < a + (1 - a) * T ^ (1 - φ) := by positivity
  have hB : 0 < (1 - a) + (1 - (1 - a)) * T ^ (1 - φ) := by
    rw [sub_sub_cancel]; positivity
  rw [ss_excess_eq ha0 ha1 hφ hT, mul_eq_zero, or_iff_right hY.ne']
  rw [sub_sub_cancel] at hB ⊢
  constructor
  · intro h
    field_simp at h
    have h2 : (1 - a) * (a * (T - T ^ (1 - φ) * T ^ (1 - φ))
        + (1 - a) * T ^ (1 - φ) * (T - 1)) = 0 := by linear_combination h
    exact (mul_eq_zero.mp h2).resolve_left h1a.ne'
  · intro h
    field_simp
    linear_combination (1 - a) * h

/-- **Existence of the symmetric steady state**, AKMM p. 714: with symmetric endowments, `T = 1`
clears both goods markets under financial autarky, and there `Q = 1`, `C = C* = Y` and the
wealth gap `W = (C/C*)^σ/Q = 1`. -/
theorem ss_exists {a φ σ Y : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1) (hY : 0 < Y) :
    ssExcess a φ Y 1 = 0 ∧ ssExcessF a φ Y 1 = 0 ∧
      cesPrice (1 - a) φ 1 / cesPrice a φ 1 = 1 ∧
      Y / cesPrice a φ 1 = Y ∧ 1 * Y / cesPrice (1 - a) φ 1 = Y ∧
      ((Y / cesPrice a φ 1) / (1 * Y / cesPrice (1 - a) φ 1)) ^ σ
        / (cesPrice (1 - a) φ 1 / cesPrice a φ 1) = 1 := by
  have hone : ∀ γ : ℝ, cesPrice γ φ 1 = 1 := by intro γ; simp [cesPrice]
  have h1 : ssExcess a φ Y 1 = 0 := by
    rw [ss_equilibrium_iff ha0 ha1 hφ hY one_pos]; simp
  have h2 := ss_walras (Y := Y) ha0 ha1 hφ one_pos
  rw [h1, zero_add, one_mul] at h2
  simp only [hone, div_one, one_mul, div_self hY.ne', one_rpow]
  exact ⟨h1, h2, trivial, trivial, trivial, trivial⟩

/-- AKMM, pp. 710–711: the symmetric allocation is also the complete-markets equilibrium with
`κ₀ = 1`: at `T = 1` and `C = C* = Y` the demands (23.3) clear both goods markets and the risk
sharing condition (23.13) `Q = κ₀(C/C*)^σ` holds. -/
theorem ss_cm_exists {a φ σ Y : ℝ} (hY : 0 < Y) :
    a * cesDemand φ 1 (cesPrice a φ 1) Y + (1 - a) * cesDemand φ 1 (cesPrice (1 - a) φ 1) Y = Y ∧
      (1 - a) * cesDemand φ 1 (cesPrice a φ 1) Y + a * cesDemand φ 1 (cesPrice (1 - a) φ 1) Y
        = Y ∧
      cesPrice (1 - a) φ 1 / cesPrice a φ 1 = 1 * (Y / Y) ^ σ := by
  have hone : ∀ γ : ℝ, cesPrice γ φ 1 = 1 := by intro γ; simp [cesPrice]
  simp only [hone, cesDemand, div_one, one_rpow, one_mul, div_self hY.ne']
  exact ⟨by ring, by ring, trivial⟩

/-- **Uniqueness** for `φ ≥ 1/2` (and `φ ≠ 1`): with symmetric endowments the autarky
equilibrium terms of trade is `T = 1`. -/
theorem ss_unique {a φ Y T : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1) (hφh : 1 / 2 ≤ φ)
    (hY : 0 < Y) (hT : 0 < T) (heq : ssExcess a φ Y T = 0) : T = 1 := by
  rw [ss_equilibrium_iff ha0 ha1 hφ hY hT] at heq
  have h1a : 0 < 1 - a := by linarith
  have hx := rpow_pos_of_pos hT (1 - φ)
  have hxx : T ^ (1 - φ) * T ^ (1 - φ) = T ^ (2 * (1 - φ)) := by
    rw [← rpow_add hT]; ring_nf
  rw [hxx] at heq
  have he : 2 * (1 - φ) ≤ 1 := by linarith
  rcases lt_trichotomy T 1 with hlt | heq1 | hgt
  · exfalso
    have h1 : T ≤ T ^ (2 * (1 - φ)) := by
      calc T = T ^ (1 : ℝ) := (rpow_one T).symm
        _ ≤ T ^ (2 * (1 - φ)) := rpow_le_rpow_of_exponent_ge hT hlt.le he
    have h2 : (1 - a) * T ^ (1 - φ) * (T - 1) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) (by linarith)
    nlinarith
  · exact heq1
  · exfalso
    have h1 : T ^ (2 * (1 - φ)) ≤ T := by
      calc T ^ (2 * (1 - φ)) ≤ T ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hgt.le he
        _ = T := rpow_one T
    have h2 : 0 < (1 - a) * T ^ (1 - φ) * (T - 1) := by
      have : 0 < T - 1 := by linarith
      positivity
    nlinarith

/-- **Multiple equilibria** with strong complementarity: for `a = 9/10` and `φ = 1/4`, the
autarky economy with symmetric endowments has the equilibrium `T = s⁴`, `s = (9 + √77)/2`, besides
`T = 1`. (`s² − 9s + 1 = 0`, and with `T = s⁴` the equilibrium condition factors as
`s³(1 − s²)(9s − 1 − s²)/10 = 0`.) -/
theorem ss_multiple {Y : ℝ} (hY : 0 < Y) :
    ssExcess (9 / 10) (1 / 4) Y (((9 + √77) / 2) ^ 4) = 0 ∧ ((9 + √77) / 2) ^ 4 ≠ (1 : ℝ) := by
  set s := (9 + √77) / 2 with hs
  have h77 : √77 ^ 2 = 77 := sq_sqrt (by norm_num)
  have hs8 : 8 < s := by
    have : 7 < √77 := by
      rw [show (7 : ℝ) = √49 by rw [show (49 : ℝ) = 7 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
      exact sqrt_lt_sqrt (by norm_num) (by norm_num)
    rw [hs]; linarith
  have hspos : 0 < s := by linarith
  have hquad : s ^ 2 - 9 * s + 1 = 0 := by rw [hs]; nlinarith [h77]
  clear_value s
  have hT : 0 < s ^ 4 := by positivity
  have hpow : (s ^ 4) ^ (1 - (1 / 4 : ℝ)) = s ^ 3 := by
    rw [← rpow_natCast s 4, ← rpow_mul hspos.le]
    norm_num
  refine ⟨?_, ?_⟩
  · rw [ss_equilibrium_iff (by norm_num) (by norm_num) (by norm_num) hY hT, hpow]
    linear_combination (s ^ 3 / 10 * (s ^ 2 - 1)) * hquad
  · intro h
    have : 8 ^ 4 < s ^ 4 := by gcongr
    norm_num at this
    linarith

end AKMM.InternationalMacro
