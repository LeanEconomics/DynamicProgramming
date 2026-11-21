/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Growth and development accounting

AKMM, §13.2 (pp. 372–374) and §13.4 (pp. 382–384). With the Cobb–Douglas aggregate (13.1)
`Y = K^α(AH)^{1−α}`:

* (13.2): `Y/L = (K/Y)^{α/(1−α)}(H/L)A` (`eq_13_2`);
* (13.3): the same in logs, and its time differences (`eq_13_3_log`, `eq_13_3`);
* (13.17): in the two-sector model with `Y = K^α(A_y e^{γ_y t}e^{nt}h)^{1−α}` and the
  investment price `P_k = e^{−γ_x t}/A_x`, output per worker is
  `(P_k K/Y)^{α/(1−α)} · h · A_y A_x^{α/(1−α)} · e^{(γ_y + γ_x α/(1−α))t}` (`eq_13_17`);
* footnote 23: an income ratio `0.2 = (k̃^J/k̃^U)^α` implies the rental-rate ratio
  `0.2^{−(1−α)/α}`, which is `25` at `α = 1/3` (`accounting_footnote_23`,
  `accounting_footnote_23_value`);
* p. 384: with `γ_y + γ_x α/(1−α) = 0.0207`, `γ_x = 0.013`, `α = 1/3`, `γ_y = 0.0142` and the
  investment-specific share is `0.0065/0.0207 ≈ 31%` (`accounting_us_decomposition`).

The tables and figures (Tables 13.1–13.2, 13.A.1–13.A.2) are data and are not formalised.
-/

namespace AKMM.Growth

/-- Cobb–Douglas output `K^α X^{1−α}` with `X = AH` the effective labour input. -/
theorem accounting_ratio_pow {α K X : ℝ} (hα1 : α < 1) (hK : 0 < K) (hX : 0 < X) :
    (K / (K ^ α * X ^ (1 - α))) ^ (α / (1 - α)) = K ^ α * X ^ (-α) := by
  have h1α : (1 - α) ≠ 0 := by linarith
  have hY : 0 < K ^ α * X ^ (1 - α) := by positivity
  apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
  rw [Real.log_rpow (div_pos hK hY), Real.log_div hK.ne' hY.ne',
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_rpow hK, Real.log_rpow hX, Real.log_rpow hX]
  field_simp
  ring

/-- AKMM, (13.2), p. 372: from (13.1) `Y = K^α(AH)^{1−α}`, output per worker decomposes as
`Y/L = (K/Y)^{α/(1−α)} (H/L) A`. -/
theorem eq_13_2 {α K A H L Y : ℝ} (hα1 : α < 1) (hK : 0 < K) (hA : 0 < A) (hH : 0 < H)
    (hL : 0 < L) (h131 : Y = K ^ α * (A * H) ^ (1 - α)) :
    Y / L = (K / Y) ^ (α / (1 - α)) * (H / L) * A := by
  have hX : 0 < A * H := mul_pos hA hH
  rw [h131, accounting_ratio_pow hα1 hK hX]
  have e : (A * H) ^ (1 - α) = (A * H) ^ (-α) * (A * H) := by
    rw [show 1 - α = -α + 1 by ring, Real.rpow_add hX, Real.rpow_one]
  rw [e]
  field_simp

/-- AKMM, (13.2)–(13.3), p. 373, in levels of logs: `log(Y/L) = (α/(1−α))log(K/Y) + log(H/L)
+ log A`. -/
theorem eq_13_3_log {α K A H L Y : ℝ} (hα1 : α < 1) (hK : 0 < K) (hA : 0 < A) (hH : 0 < H)
    (hL : 0 < L) (h131 : Y = K ^ α * (A * H) ^ (1 - α)) :
    Real.log (Y / L) = α / (1 - α) * Real.log (K / Y) + Real.log (H / L) + Real.log A := by
  have hY : 0 < Y := by rw [h131]; have := mul_pos hA hH; positivity
  rw [eq_13_2 hα1 hK hA hH hL h131, Real.log_mul (by positivity) hA.ne',
    Real.log_mul (by positivity) (by positivity), Real.log_rpow (div_pos hK hY)]

/-- AKMM, (13.3), p. 373: **growth accounting**. If (13.1) holds at two dates (with the same
`α`), the change in log output per worker is `α/(1−α)` times the change in `log(K/Y)`, plus
the change in `log(H/L)`, plus the change in `log A`. -/
theorem eq_13_3 {α K A H L Y K' A' H' L' Y' : ℝ} (hα1 : α < 1) (hK : 0 < K) (hA : 0 < A)
    (hH : 0 < H) (hL : 0 < L) (h : Y = K ^ α * (A * H) ^ (1 - α)) (hK' : 0 < K')
    (hA' : 0 < A') (hH' : 0 < H') (hL' : 0 < L') (h' : Y' = K' ^ α * (A' * H') ^ (1 - α)) :
    Real.log (Y' / L') - Real.log (Y / L) =
      α / (1 - α) * (Real.log (K' / Y') - Real.log (K / Y)) +
        (Real.log (H' / L') - Real.log (H / L)) + (Real.log A' - Real.log A) := by
  rw [eq_13_3_log hα1 hK hA hH hL h, eq_13_3_log hα1 hK' hA' hH' hL' h']
  ring

/-- AKMM, (13.17), p. 383: **nominal development accounting**. In the model of §13.3, with
`Y(t) = K^α(A_y e^{γ_y t} e^{nt} h)^{1−α}` and investment price `P_k(t) = e^{−γ_x t}/A_x`,
output per worker in consumption units is
`Y/e^{nt} = (P_k K/Y)^{α/(1−α)} · h · A_y A_x^{α/(1−α)} · e^{(γ_y + γ_x α/(1−α))t}`. -/
theorem eq_13_17 {α Ax Ay h K γx γy n t : ℝ} (hα1 : α < 1) (hAx : 0 < Ax) (hAy : 0 < Ay)
    (hh : 0 < h) (hK : 0 < K) :
    K ^ α * (Ay * Real.exp (γy * t) * Real.exp (n * t) * h) ^ (1 - α) / Real.exp (n * t) =
      (Real.exp (-γx * t) / Ax * K / (K ^ α * (Ay * Real.exp (γy * t) * Real.exp (n * t) * h) ^
        (1 - α))) ^ (α / (1 - α)) * h * (Ay * Ax ^ (α / (1 - α))) *
        Real.exp ((γy + γx * (α / (1 - α))) * t) := by
  set X := Ay * Real.exp (γy * t) * Real.exp (n * t) * h with hXdef
  have hX : 0 < X := by positivity
  set p := α / (1 - α)
  have hPk : 0 ≤ Real.exp (-γx * t) / Ax := by positivity
  have hKY : 0 ≤ K / (K ^ α * X ^ (1 - α)) := by positivity
  rw [show Real.exp (-γx * t) / Ax * K / (K ^ α * X ^ (1 - α)) =
    Real.exp (-γx * t) / Ax * (K / (K ^ α * X ^ (1 - α))) by ring, Real.mul_rpow hPk hKY,
    accounting_ratio_pow hα1 hK hX,
    Real.div_rpow (Real.exp_pos _).le hAx.le, ← Real.exp_mul]
  have e1 : X ^ (1 - α) = X ^ (-α) * X := by
    rw [show 1 - α = -α + 1 by ring, Real.rpow_add hX, Real.rpow_one]
  have e2 : Real.exp ((γy + γx * p) * t) = Real.exp (-γx * t * p) * Real.exp (γy * t) *
      Real.exp (2 * (γx * p * t)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hAxp : 0 < Ax ^ p := by positivity
  rw [e1, e2, hXdef]
  field_simp
  rw [sq, ← Real.exp_add, ← Real.exp_add,
    show -(t * γx * p) + -(t * γx * p) + t * γx * p * 2 = 0 by ring, Real.exp_zero]

/-- AKMM, footnote 23, p. 383: with `y = k̃^α` and the rental rate `R = αk̃^{α−1}` (13.A.1)
in two countries, an income ratio `y^J/y^U = 0.2` implies `R^J/R^U = 0.2^{−(1−α)/α}`. -/
theorem accounting_footnote_23 {α kJ kU : ℝ} (hα0 : 0 < α) (hkJ : 0 < kJ) (hkU : 0 < kU)
    (hratio : kJ ^ α / kU ^ α = 0.2) :
    (α * kJ ^ (α - 1)) / (α * kU ^ (α - 1)) = (0.2 : ℝ) ^ (-(1 - α) / α) := by
  have hq : kJ / kU = (0.2 : ℝ) ^ (1 / α) := by
    rw [← hratio, ← Real.div_rpow hkJ.le hkU.le, ← Real.rpow_mul (by positivity),
      mul_one_div_cancel hα0.ne', Real.rpow_one]
  rw [mul_div_mul_left _ _ hα0.ne', ← Real.div_rpow hkJ.le hkU.le, hq,
    ← Real.rpow_mul (by norm_num)]
  congr 1
  field_simp
  ring

/-- AKMM, footnote 23, p. 383: at `α = 1/3` the rental rate in Japan in 1950 is `25` times
that in the U.S.: `0.2^{−(1−α)/α} = 0.2^{−2} = 25`. -/
theorem accounting_footnote_23_value : (0.2 : ℝ) ^ (-(1 - (1 / 3 : ℝ)) / (1 / 3)) = 25 := by
  rw [show (-(1 - (1 / 3 : ℝ)) / (1 / 3)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
  norm_num

/-- AKMM, p. 384: if `γ_y + γ_x α/(1−α) = 0.0207` with `γ_x = 0.013` and `α = 1/3`, then
`γ_y = 0.0142` (the book's `0.014`), and the investment-specific contribution
`γ_x α/(1−α) = 0.0065` is between 31% and 32% of per-capita growth. -/
theorem accounting_us_decomposition {γy : ℝ}
    (h : γy + 0.013 * ((1 / 3 : ℝ) / (1 - 1 / 3)) = 0.0207) :
    γy = 0.0142 ∧ 0.31 < 0.013 * ((1 / 3 : ℝ) / (1 - 1 / 3)) / 0.0207 ∧
      0.013 * ((1 / 3 : ℝ) / (1 - 1 / 3)) / 0.0207 < 0.32 := by
  refine ⟨by linarith [h], by norm_num, by norm_num⟩

end AKMM.Growth
