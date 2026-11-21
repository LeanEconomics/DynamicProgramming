import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.SpecialFunctions.Sqrt
import AKMMContinuousTime.Mangasarian
import AKMMContinuousTime.RamseySaddle
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The neoclassical growth model with investment-specific technical change

AKMM, §13.3 (pp. 376–379) and Appendix 13.A.1–13.A.2 (pp. 850–851): the economy of Greenwood,
Hercowitz and Krusell (1997) in continuous time. Output `Y = K^α(A_y e^{γ_y t}L)^{1−α}` (13.6)
turns one for one into consumption and one for `A_x e^{γ_x t}` into investment, so the
investment price is `P_x(t) = e^{−γ_x t}/A_x`.

* The return condition (13.5) `P_x r = R − δP_x + Ṗ_x` is `r = RA_x e^{γ_x t} − δ − γ_x`
  (`istc_price_hasDerivAt`, `eq_13_5`).
* The firm's first-order conditions (13.A.1)–(13.A.2) are the partial derivatives of output
  (`eq_13_A_1`, `eq_13_A_2`); at those prices the firm's problem (13.7) is solved and profits
  are zero (`istc_firm_optimal`); the interest rate is (13.A.3) (`eq_13_A_3`).
* The household's first-order conditions (13.A.4)–(13.A.5) give the Euler equation
  (13.A.7)/(13.9) (`eq_13_A_7`); conversely the Euler equation gives the costate equation
  (`istc_costate_of_euler`).
* The budget with asset-market clearing gives the capital accumulation equation (13.A.8)/(13.10)
  (`eq_13_A_8`, `eq_13_10`); it is equivalent to (13.A.9)–(13.A.10) (`istc_walras`).
* The TVC and asset-market clearing give (13.A.11)/(13.11) (`eq_13_A_11`).
* The planner's first-order conditions (13.A.12) give the same Euler equation
  (`istc_planner_euler`).
* In per-capita wealth `a = Ke^{−γ_x t}/(A_x e^{nt})` the budget is
  `ȧ = A_x^α(A_y h)^{1−α}e^{(1−α)g_c t}a^α − (δ + γ_x + n)a − c` and `r − n` is its slope in
  `a` (`istc_budget_reduced`, `istc_return_reduced`): the investment-specific change acts like
  labour-augmenting change at the rate `g_c = αγ_x/(1−α) + γ_y`, the remark on p. 379
  (`istc_labour_augmenting`).
-/

namespace AKMM.Growth

open Real

/-- AKMM, p. 378: the growth rate of capital on the balanced growth path,
`g_K = γ_x/(1−α) + γ_y + n`. -/
noncomputable def istcGK (α γx γy n : ℝ) : ℝ := γx / (1 - α) + γy + n

/-- AKMM, p. 379: the growth rate of per-capita consumption on the balanced growth path,
`g_c = αγ_x/(1−α) + γ_y`. -/
noncomputable def istcGc (α γx γy : ℝ) : ℝ := α * γx / (1 - α) + γy

/-- AKMM, (13.14), p. 379: the denominator `ασγ_x/(1−α) + γ_x + σγ_y + δ + ρ`, which equals
`σg_c + γ_x + δ + ρ`. -/
noncomputable def istcD (α σ ρ δ γx γy : ℝ) : ℝ := α * σ * γx / (1 - α) + γx + σ * γy + δ + ρ

/-- The left side of the boundedness condition (13.8), `n − ρ + α(1−σ)γ_x/(1−α) + (1−σ)γ_y`;
(13.8) says it is negative. -/
noncomputable def istcBound (α σ ρ n γx γy : ℝ) : ℝ :=
  n - ρ + α * (1 - σ) / (1 - α) * γx + (1 - σ) * γy

/-- AKMM, p. 379: `g_K = g_c + γ_x + n`. -/
theorem istc_gK_eq (α γx γy n : ℝ) (hα1 : α < 1) :
    istcGK α γx γy n = istcGc α γx γy + γx + n := by
  have : (1 - α) ≠ 0 := by linarith
  unfold istcGK istcGc
  field_simp
  ring

/-- AKMM, p. 379: `ασγ_x/(1−α) + γ_x + σγ_y + δ + ρ = σg_c + γ_x + δ + ρ`. -/
theorem istc_D_eq (α σ ρ δ γx γy : ℝ) :
    istcD α σ ρ δ γx γy = σ * istcGc α γx γy + γx + δ + ρ := by
  unfold istcD istcGc
  ring

/-- AKMM, (13.8): its left side is `n − ρ + (1 − σ)g_c`. -/
theorem istc_bound_eq (α σ ρ n γx γy : ℝ) :
    istcBound α σ ρ n γx γy = n - ρ + (1 - σ) * istcGc α γx γy := by
  unfold istcBound istcGc
  ring

/-- AKMM, (13.8) and p. 380: `D − (g_K + δ) = −(13.8)`, i.e. the gap between the steady-state
and golden-rule marginal products is minus the left side of (13.8). -/
theorem istc_D_sub_gK (α σ ρ δ γx γy n : ℝ) (hα1 : α < 1) :
    istcD α σ ρ δ γx γy - (istcGK α γx γy n + δ) = -istcBound α σ ρ n γx γy := by
  rw [istc_D_eq, istc_gK_eq _ _ _ _ hα1, istc_bound_eq]
  ring

/-- AKMM, p. 377: the investment price `P_x(t) = e^{−γ_x t}/A_x` falls at the rate `γ_x`. -/
theorem istc_price_hasDerivAt (Ax γx t : ℝ) :
    HasDerivAt (fun s => Real.exp (-γx * s) / Ax) (-γx * (Real.exp (-γx * t) / Ax)) t := by
  have h := ((hasDerivAt_id' t).const_mul (-γx)).exp.div_const Ax
  convert h using 1
  ring

/-- AKMM, (13.5), p. 377, and the return condition (item 3 of the equilibrium definition): with
`P_x(t) = e^{−γ_x t}/A_x`, `P_x r = R − δP_x + Ṗ_x` iff `r = RA_x e^{γ_x t} − δ − γ_x`. -/
theorem eq_13_5 {Ax γx δ t r R : ℝ} (hAx : 0 < Ax) :
    Real.exp (-γx * t) / Ax * r =
        R - δ * (Real.exp (-γx * t) / Ax) + -γx * (Real.exp (-γx * t) / Ax) ↔
      r = R * Ax * Real.exp (γx * t) - δ - γx := by
  have hE : Real.exp (-γx * t) = (Real.exp (γx * t))⁻¹ := by rw [neg_mul, Real.exp_neg]
  have hEp := Real.exp_pos (γx * t)
  rw [hE]
  constructor
  · intro h
    field_simp at h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- `K^{α−1} Z^{1−α} = (Z/K)^{1−α}` for `K, Z > 0`. -/
theorem istc_rpow_ratio {α K Z : ℝ} (hK : 0 < K) (hZ : 0 < Z) :
    K ^ (α - 1) * Z ^ (1 - α) = (Z / K) ^ (1 - α) := by
  rw [Real.div_rpow hZ.le hK.le, show α - 1 = -(1 - α) by ring, Real.rpow_neg hK.le]
  field_simp

/-- AKMM, (13.A.1), p. 850: the marginal product of capital of `K^α Z^{1−α}` is
`α(Z/K)^{1−α}`; with `Z = A_y e^{(γ_y+n)t}h` this is the rental rate `R(t)`. -/
theorem eq_13_A_1 {α K Z : ℝ} (hK : 0 < K) (hZ : 0 < Z) :
    HasDerivAt (fun k => k ^ α * Z ^ (1 - α)) (α * (Z / K) ^ (1 - α)) K := by
  have h := (Real.hasDerivAt_rpow_const (p := α) (Or.inl hK.ne')).mul_const (Z ^ (1 - α))
  convert h using 1
  rw [mul_assoc, istc_rpow_ratio hK hZ]

/-- AKMM, (13.A.2), p. 850: the marginal product of labour of `K^α(BL)^{1−α}` is
`(1−α)B(K/(BL))^α`; with `B = A_y e^{γ_y t}` and `L = e^{nt}h` this is the wage `w(t)`. -/
theorem eq_13_A_2 {α K B L : ℝ} (hK : 0 < K) (hB : 0 < B) (hL : 0 < L) :
    HasDerivAt (fun l => K ^ α * (B * l) ^ (1 - α)) ((1 - α) * B * (K / (B * L)) ^ α) L := by
  have hBL : 0 < B * L := mul_pos hB hL
  have h1 := ((hasDerivAt_id' L).const_mul B).rpow_const (p := 1 - α) (Or.inl hBL.ne')
  have h := h1.const_mul (K ^ α)
  convert h using 1
  rw [mul_one]
  rw [show 1 - α - 1 = -α by ring, Real.div_rpow hK.le hBL.le, Real.rpow_neg hBL.le]
  field_simp

/-- AKMM, (13.7), p. 377: at the rental rate (13.A.1) and wage (13.A.2) the firm's problem is
solved by `(K, L)` and maximal profits are zero: for every `K', L' ≥ 0`,
`K'^α(BL')^{1−α} − RK' − wL' ≤ 0 = K^α(BL)^{1−α} − RK − wL`. -/
theorem istc_firm_optimal {α K B L K' L' : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hK : 0 < K)
    (hB : 0 < B) (hL : 0 < L) (hK' : 0 ≤ K') (hL' : 0 ≤ L') :
    K' ^ α * (B * L') ^ (1 - α) - α * (B * L / K) ^ (1 - α) * K' -
        (1 - α) * B * (K / (B * L)) ^ α * L' ≤ 0 ∧
      K ^ α * (B * L) ^ (1 - α) - α * (B * L / K) ^ (1 - α) * K -
        (1 - α) * B * (K / (B * L)) ^ α * L = 0 := by
  have hBL : 0 < B * L := mul_pos hB hL
  set Y := K ^ α * (B * L) ^ (1 - α) with hY
  have hYpos : 0 < Y := by positivity
  have hR : α * (B * L / K) ^ (1 - α) = α * Y / K := by
    rw [hY, Real.div_rpow hBL.le hK.le, show (1 - α) = -(α - 1) by ring, Real.rpow_neg hK.le,
      Real.rpow_sub_one hK.ne']
    field_simp
  have hw : (1 - α) * B * (K / (B * L)) ^ α = (1 - α) * Y / L := by
    rw [hY, Real.div_rpow hK.le hBL.le, Real.mul_rpow hB.le hL.le, Real.mul_rpow hB.le hL.le,
      Real.rpow_sub hB, Real.rpow_sub hL, Real.rpow_one, Real.rpow_one]
    field_simp
  rw [hR, hw]
  refine ⟨?_, by field_simp; ring⟩
  have hgm := Real.geom_mean_le_arith_mean2_weighted hα0.le (by linarith : (0 : ℝ) ≤ 1 - α)
    (div_nonneg hK' hK.le) (div_nonneg hL' hL.le) (by ring)
  have e : K' ^ α * (B * L') ^ (1 - α) = Y * ((K' / K) ^ α * (L' / L) ^ (1 - α)) := by
    rw [hY, Real.div_rpow hK' hK.le, Real.div_rpow hL' hL.le, Real.mul_rpow hB.le hL',
      Real.mul_rpow hB.le hL.le]
    have : 0 < K ^ α := by positivity
    have : 0 < L ^ (1 - α) := by positivity
    field_simp
  rw [e]
  have := mul_le_mul_of_nonneg_left hgm hYpos.le
  have e2 : Y * (α * (K' / K) + (1 - α) * (L' / L)) = α * Y / K * K' + (1 - α) * Y / L * L' := by
    field_simp
  linarith

/-- AKMM, (13.A.3), p. 850: substituting (13.A.1) into the return condition gives
`r = A_x e^{γ_x t}α(A_y e^{(γ_y+n)t}h/K)^{1−α} − δ − γ_x`. -/
theorem eq_13_A_3 {α Ax Ay h γx γy n δ t K r : ℝ} (hAx : 0 < Ax)
    (hret : Real.exp (-γx * t) / Ax * r = α * (Ay * Real.exp ((γy + n) * t) * h / K) ^ (1 - α) -
      δ * (Real.exp (-γx * t) / Ax) + -γx * (Real.exp (-γx * t) / Ax)) :
    r = Ax * Real.exp (γx * t) * α * (Ay * Real.exp ((γy + n) * t) * h / K) ^ (1 - α) -
      δ - γx := by
  rw [(eq_13_5 hAx).mp hret]
  ring

/-- AKMM, (13.A.4)–(13.A.7), p. 850: **the Euler equation**. If the multiplier is
`λ(t) = e^{−(ρ−n)t}c(t)^{−σ}` (13.A.4) and it satisfies `λ̇ = −(r − n)λ` (13.A.5), then
`ċ/c = (r − ρ)/σ`. With (13.A.3) this is (13.9). -/
theorem eq_13_A_7 {σ ρ n r t cdot : ℝ} {c lam : ℝ → ℝ} (hσ : 0 < σ) (hc : 0 < c t)
    (hcd : HasDerivAt c cdot t)
    (h4 : lam = fun s => Real.exp (-(ρ - n) * s) * c s ^ (-σ))
    (h5 : HasDerivAt lam (-(r - n) * lam t) t) :
    cdot / c t = (r - ρ) / σ := by
  have hd : HasDerivAt lam (-(ρ - n) * Real.exp (-(ρ - n) * t) * c t ^ (-σ) +
      Real.exp (-(ρ - n) * t) * (cdot * (-σ) * c t ^ (-σ - 1))) t := by
    rw [h4]
    have h1 := ((hasDerivAt_id' t).const_mul (-(ρ - n))).exp
    have h2 := hcd.rpow_const (p := -σ) (Or.inl hc.ne')
    convert h1.fun_mul h2 using 1
    ring
  have hu := h5.unique hd
  rw [h4] at hu
  simp only at hu
  have hE := Real.exp_pos (-(ρ - n) * t)
  have hcs : c t ^ (-σ - 1) = c t ^ (-σ) / c t := by
    rw [Real.rpow_sub_one hc.ne']
  rw [hcs] at hu
  have hcp : 0 < c t ^ (-σ) := Real.rpow_pos_of_pos hc _
  field_simp at hu
  field_simp
  nlinarith [hu, mul_pos hE hcp]

/-- AKMM, (13.A.4)–(13.A.5), p. 850, converse of `eq_13_A_7`: if consumption obeys the Euler
equation `ċ = c(r − ρ)/σ`, then `λ(t) = e^{−(ρ−n)t}c(t)^{−σ}` obeys `λ̇ = −(r − n)λ`. -/
theorem istc_costate_of_euler {σ ρ n r t : ℝ} {c : ℝ → ℝ} (hσ : 0 < σ) (hc : 0 < c t)
    (hcd : HasDerivAt c (c t * (r - ρ) / σ) t) :
    HasDerivAt (fun s => Real.exp (-(ρ - n) * s) * c s ^ (-σ))
      (-(r - n) * (Real.exp (-(ρ - n) * t) * c t ^ (-σ))) t := by
  have h1 := ((hasDerivAt_id' t).const_mul (-(ρ - n))).exp
  have h2 := hcd.rpow_const (p := -σ) (Or.inl hc.ne')
  convert h1.fun_mul h2 using 1
  rw [Real.rpow_sub_one hc.ne']
  field_simp
  ring

/-- AKMM, (13.A.6), (13.A.8) and (13.10), pp. 377–378 and 850: **the capital accumulation
equation**. Let `B = A_y e^{γ_y t}`, `L = e^{nt}h`, let `R` and `w` be the marginal products
(13.A.1)–(13.A.2), `r` the return condition, and let asset-market clearing
`K(t)e^{−γ_x t}/A_x = a(t)e^{nt}` hold, so that `K̇ = (γ_x + n)K + A_x e^{(γ_x+n)t}ȧ`. If the
household budget (13.A.6) `ȧ = (r − n)a + wh − c` holds, then
`K̇ = A_x e^{γ_x t}(K^α(BL)^{1−α} − e^{nt}c) − δK`. -/
theorem eq_13_A_8 {α Ax h δ γx n t c a adot K R w B r : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hAx : 0 < Ax) (hh : 0 < h) (hK : 0 < K) (hB : 0 < B)
    (hR : R = α * (B * (Real.exp (n * t) * h) / K) ^ (1 - α))
    (hw : w = (1 - α) * B * (K / (B * (Real.exp (n * t) * h))) ^ α)
    (hr : r = R * Ax * Real.exp (γx * t) - δ - γx)
    (hclear : K * Real.exp (-γx * t) / Ax = a * Real.exp (n * t))
    (h6 : adot = (r - n) * a + w * h - c) :
    (γx + n) * K + Ax * Real.exp ((γx + n) * t) * adot =
      Ax * Real.exp (γx * t) * (K ^ α * (B * (Real.exp (n * t) * h)) ^ (1 - α) -
        Real.exp (n * t) * c) - δ * K := by
  have hL : 0 < Real.exp (n * t) * h := by positivity
  have hfirm := (istc_firm_optimal hα0 hα1 hK hB hL hK.le hL.le).2
  rw [← hR, ← hw] at hfirm
  have hE : Real.exp (-γx * t) = (Real.exp (γx * t))⁻¹ := by rw [neg_mul, Real.exp_neg]
  have hE2 : Real.exp ((γx + n) * t) = Real.exp (γx * t) * Real.exp (n * t) := by
    rw [← Real.exp_add]; ring_nf
  have hEx := Real.exp_pos (γx * t)
  have hEn := Real.exp_pos (n * t)
  have ha : a = K / (Ax * Real.exp (γx * t) * Real.exp (n * t)) := by
    rw [hE] at hclear
    field_simp at hclear ⊢
    linarith
  have hcan : Ax * (Real.exp (γx * t) * Real.exp (n * t)) *
      (K / (Ax * Real.exp (γx * t) * Real.exp (n * t))) = K := by
    field_simp
  rw [h6, hr, ha, hE2]
  linear_combination (-(Ax * Real.exp (γx * t))) * hfirm +
    (R * Ax * Real.exp (γx * t) - δ - γx - n) * hcan

/-- AKMM, (13.10), p. 378: the capital accumulation equation (13.A.8) divided by `K`, in the
printed form `K̇/K = A_x((e^{(γ_x/(1−α)+γ_y+n)t}A_y h/K)^{1−α} − e^{(γ_x+n)t}c/K) − δ`. -/
theorem eq_13_10 {α Ax Ay h δ γx γy n t c K : ℝ} (hα1 : α < 1) (hAy : 0 < Ay) (hh : 0 < h)
    (hK : 0 < K) :
    (Ax * Real.exp (γx * t) * (K ^ α * (Ay * Real.exp (γy * t) * (Real.exp (n * t) * h)) ^
        (1 - α) - Real.exp (n * t) * c) - δ * K) / K =
      Ax * ((Real.exp ((γx / (1 - α) + γy + n) * t) * Ay * h / K) ^ (1 - α) -
        Real.exp ((γx + n) * t) * c / K) - δ := by
  have h1α : (1 - α) ≠ 0 := by linarith
  have hZ : 0 < Ay * Real.exp (γy * t) * (Real.exp (n * t) * h) := by positivity
  have e1 : (Real.exp ((γx / (1 - α) + γy + n) * t) * Ay * h / K) ^ (1 - α) =
      Real.exp (γx * t) * (Ay * Real.exp (γy * t) * (Real.exp (n * t) * h) / K) ^ (1 - α) := by
    rw [show Real.exp ((γx / (1 - α) + γy + n) * t) * Ay * h / K =
      Real.exp (γx / (1 - α) * t) * (Ay * Real.exp (γy * t) * (Real.exp (n * t) * h) / K) by
        rw [show (γx / (1 - α) + γy + n) * t = γx / (1 - α) * t + γy * t + n * t by ring,
          Real.exp_add, Real.exp_add]; ring]
    rw [Real.mul_rpow (Real.exp_pos _).le (div_pos hZ hK).le, ← Real.exp_mul]
    congr 2
    field_simp
  have e2 : (Ay * Real.exp (γy * t) * (Real.exp (n * t) * h) / K) ^ (1 - α) * K =
      K ^ α * (Ay * Real.exp (γy * t) * (Real.exp (n * t) * h)) ^ (1 - α) := by
    rw [← istc_rpow_ratio hK hZ, Real.rpow_sub_one hK.ne']
    field_simp
  have e3 : Real.exp ((γx + n) * t) = Real.exp (γx * t) * Real.exp (n * t) := by
    rw [← Real.exp_add]; ring_nf
  rw [e1, e3, ← e2]
  field_simp

/-- AKMM, (13.A.9)–(13.A.10), p. 851: **Walras's law**. The accumulation equation (13.A.8)
holds iff there is investment `X` with `K̇ = X − δK` (13.A.9) and goods-market clearing
`Y = e^{nt}c + Xe^{−γ_x t}/A_x` (13.A.10). -/
theorem istc_walras {Ax γx n t c Y K Kdot δ : ℝ} (hAx : 0 < Ax) :
    Kdot = Ax * Real.exp (γx * t) * (Y - Real.exp (n * t) * c) - δ * K ↔
      ∃ X, Kdot = X - δ * K ∧ Y = Real.exp (n * t) * c + X * Real.exp (-γx * t) / Ax := by
  have hE : Real.exp (-γx * t) = (Real.exp (γx * t))⁻¹ := by rw [neg_mul, Real.exp_neg]
  have hEp := Real.exp_pos (γx * t)
  rw [hE]
  constructor
  · intro h
    refine ⟨Ax * Real.exp (γx * t) * (Y - Real.exp (n * t) * c), h, ?_⟩
    field_simp
    ring
  · rintro ⟨X, h1, h2⟩
    rw [h1, h2]
    field_simp
    ring

/-- AKMM, (13.A.11) and (13.11), p. 378 and p. 851: with asset-market clearing
`a(T) = K(T)e^{−γ_x T}/(A_x e^{nT})`, the household's transversality term
`e^{−(ρ−n)T}c(T)^{−σ}a(T)` equals `(K(T)/A_x)e^{−(γ_x+ρ)T}c(T)^{−σ}`. -/
theorem eq_13_A_11 {Ax γx n ρ σ T c K : ℝ} (hAx : 0 < Ax) :
    Real.exp (-(ρ - n) * T) * c ^ (-σ) * (K * Real.exp (-γx * T) / Ax / Real.exp (n * T)) =
      K / Ax * Real.exp (-(γx + ρ) * T) * c ^ (-σ) := by
  have e : Real.exp (-(γx + ρ) * T) =
      Real.exp (-(ρ - n) * T) * Real.exp (-γx * T) / Real.exp (n * T) := by
    rw [eq_div_iff (Real.exp_pos _).ne', ← Real.exp_add, ← Real.exp_add]
    ring_nf
  rw [e]
  field_simp

/-- AKMM, (13.A.12), p. 851: **the planner's Euler equation**. In the planner's problem with
the Hamiltonian of p. 851, the first-order condition for `c` is
`e^{−(ρ−n)t}c^{−σ} = μA_x e^{(γ_x+n)t}`, and the costate equation is
`μ̇ = −μ(A_x e^{γ_x t}α(Z/K)^{1−α} − δ)`. Together they give
`ċ/c = (A_x e^{γ_x t}α(Z/K)^{1−α} − δ − γ_x − ρ)/σ`, the equilibrium Euler equation (13.A.7). -/
theorem istc_planner_euler {σ ρ n δ Ax γx t cdot MPK : ℝ} {c μ : ℝ → ℝ} (hσ : 0 < σ)
    (hAx : 0 < Ax) (hc : 0 < c t) (hcd : HasDerivAt c cdot t)
    (hfoc : ∀ s, Real.exp (-(ρ - n) * s) * c s ^ (-σ) = μ s * (Ax * Real.exp ((γx + n) * s)))
    (hcost : HasDerivAt μ (-(μ t * (Ax * Real.exp (γx * t) * MPK - δ))) t) :
    cdot / c t = (Ax * Real.exp (γx * t) * MPK - δ - γx - ρ) / σ := by
  have hμ : μ = fun s => Real.exp (-(ρ + γx) * s) * c s ^ (-σ) / Ax := by
    funext s
    have h := hfoc s
    have e : Real.exp (-(ρ - n) * s) = Real.exp (-(ρ + γx) * s) * Real.exp ((γx + n) * s) := by
      rw [← Real.exp_add]; ring_nf
    rw [e] at h
    have hp := Real.exp_pos ((γx + n) * s)
    rw [eq_div_iff hAx.ne']
    apply mul_right_cancel₀ hp.ne'
    linear_combination -h
  have hd : HasDerivAt μ (-(ρ + γx) * Real.exp (-(ρ + γx) * t) * c t ^ (-σ) / Ax +
      Real.exp (-(ρ + γx) * t) * (cdot * (-σ) * c t ^ (-σ - 1)) / Ax) t := by
    rw [hμ]
    have h1 := ((hasDerivAt_id' t).const_mul (-(ρ + γx))).exp
    have h2 := hcd.rpow_const (p := -σ) (Or.inl hc.ne')
    convert (h1.fun_mul h2).div_const Ax using 1
    ring
  have hu := hcost.unique hd
  rw [hμ] at hu
  simp only at hu
  rw [Real.rpow_sub_one hc.ne'] at hu
  have hE := Real.exp_pos (-(ρ + γx) * t)
  have hcp : 0 < c t ^ (-σ) := Real.rpow_pos_of_pos hc _
  field_simp at hu
  field_simp
  nlinarith [hu, mul_pos hE hcp]

/-- AKMM, p. 379: capital-augmenting technical change in a Cobb–Douglas technology is
labour-augmenting change raised to the power `α/(1−α)`:
`(A_x e^{γ_x t}K)^α(A_y e^{γ_y t}L)^{1−α}
= K^α(A_y A_x^{α/(1−α)}e^{(γ_y + αγ_x/(1−α))t}L)^{1−α}`. -/
theorem istc_labour_augmenting {α Ax Ay γx γy t K L : ℝ} (hα1 : α < 1) (hAx : 0 < Ax)
    (hAy : 0 < Ay) (hK : 0 < K) (hL : 0 < L) :
    (Ax * Real.exp (γx * t) * K) ^ α * (Ay * Real.exp (γy * t) * L) ^ (1 - α) =
      K ^ α * (Ay * Ax ^ (α / (1 - α)) * Real.exp ((γy + α * γx / (1 - α)) * t) * L) ^
        (1 - α) := by
  have h1α : (1 - α) ≠ 0 := by linarith
  apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
  simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_exp]
  field_simp
  ring

/-- AKMM, p. 851: per-capita output in terms of per-capita wealth. With
`K = A_x e^{(γ_x+n)t}a` (asset-market clearing) and `L = e^{nt}h`,
`e^{−nt}K^α(A_y e^{γ_y t}L)^{1−α} = A_x^α(A_y h)^{1−α}e^{(1−α)g_c t}a^α`. -/
theorem istc_output_reduced {α Ax Ay h γx γy n t a : ℝ} (hα1 : α < 1) (hAx : 0 < Ax)
    (hAy : 0 < Ay) (hh : 0 < h) (ha : 0 < a) :
    Real.exp (-n * t) * (Ax * Real.exp ((γx + n) * t) * a) ^ α *
        (Ay * Real.exp (γy * t) * (Real.exp (n * t) * h)) ^ (1 - α) =
      Ax ^ α * (Ay * h) ^ (1 - α) * Real.exp ((1 - α) * istcGc α γx γy * t) * a ^ α := by
  have h1α : (1 - α) ≠ 0 := by linarith
  apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
  simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_exp]
  unfold istcGc
  field_simp
  ring

/-- AKMM, (13.A.6) with (13.A.2)–(13.A.3), p. 850: **the budget in per-capita wealth**. With
`K = A_x e^{(γ_x+n)t}a`, the factor prices (13.A.1)–(13.A.2) and the return condition, the
household's income is `(r − n)a + wh = A_x^α(A_y h)^{1−α}e^{(1−α)g_c t}a^α − (δ + γ_x + n)a`. -/
theorem istc_budget_reduced {α Ax Ay h δ γx γy n t a K R w r : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hAx : 0 < Ax) (hAy : 0 < Ay) (hh : 0 < h) (ha : 0 < a)
    (hKa : K = Ax * Real.exp ((γx + n) * t) * a)
    (hR : R = α * (Ay * Real.exp (γy * t) * (Real.exp (n * t) * h) / K) ^ (1 - α))
    (hw : w = (1 - α) * (Ay * Real.exp (γy * t)) *
      (K / (Ay * Real.exp (γy * t) * (Real.exp (n * t) * h))) ^ α)
    (hr : r = R * Ax * Real.exp (γx * t) - δ - γx) :
    (r - n) * a + w * h =
      Ax ^ α * (Ay * h) ^ (1 - α) * Real.exp ((1 - α) * istcGc α γx γy * t) * a ^ α -
        (δ + γx + n) * a := by
  have hK : 0 < K := by rw [hKa]; positivity
  have hB : 0 < Ay * Real.exp (γy * t) := by positivity
  have hL : 0 < Real.exp (n * t) * h := by positivity
  have hfirm := (istc_firm_optimal hα0 hα1 hK hB hL hK.le hL.le).2
  rw [← hR, ← hw] at hfirm
  rw [← istc_output_reduced hα1 hAx hAy hh ha, ← hKa]
  have hE : Real.exp ((γx + n) * t) = Real.exp (γx * t) * Real.exp (n * t) := by
    rw [← Real.exp_add]; ring_nf
  have hEn : Real.exp (-n * t) * Real.exp (n * t) = 1 := by
    rw [← Real.exp_add]; simp
  have hKE : K = Ax * Real.exp (γx * t) * Real.exp (n * t) * a := by rw [hKa, hE]; ring
  rw [hr]
  linear_combination (-Real.exp (-n * t)) * hfirm + (-Real.exp (-n * t) * R) * hKE +
    (-(R * Ax * Real.exp (γx * t) * a + w * h)) * hEn

/-- AKMM, (13.A.3), p. 850, in per-capita wealth: with `K = A_x e^{(γ_x+n)t}a`, the rental
rate (13.A.1) and the return condition, `r − n = αA_x^α(A_y h)^{1−α}e^{(1−α)g_c t}a^{α−1}
− (δ + γ_x + n)`, the marginal product of `a` in the reduced budget. -/
theorem istc_return_reduced {α Ax Ay h δ γx γy n t a K R r : ℝ} (hα1 : α < 1) (hAx : 0 < Ax)
    (hAy : 0 < Ay) (hh : 0 < h) (ha : 0 < a)
    (hKa : K = Ax * Real.exp ((γx + n) * t) * a)
    (hR : R = α * (Ay * Real.exp (γy * t) * (Real.exp (n * t) * h) / K) ^ (1 - α))
    (hr : r = R * Ax * Real.exp (γx * t) - δ - γx) :
    r - n = α * (Ax ^ α * (Ay * h) ^ (1 - α) * Real.exp ((1 - α) * istcGc α γx γy * t)) *
      a ^ (α - 1) - (δ + γx + n) := by
  have hK : 0 < K := by rw [hKa]; positivity
  have hZ : 0 < Ay * Real.exp (γy * t) * (Real.exp (n * t) * h) := by positivity
  have hout := istc_output_reduced (γx := γx) (γy := γy) (n := n) (t := t) hα1 hAx hAy hh ha
  rw [← hKa] at hout
  have hE : Real.exp ((γx + n) * t) = Real.exp (γx * t) * Real.exp (n * t) := by
    rw [← Real.exp_add]; ring_nf
  have hEn : Real.exp (-n * t) * Real.exp (n * t) = 1 := by
    rw [← Real.exp_add]; simp
  have hEnp := Real.exp_pos (n * t)
  have hKE : K = Ax * Real.exp (γx * t) * Real.exp (n * t) * a := by rw [hKa, hE]; ring
  have hEn' : Real.exp (-n * t) = (Real.exp (n * t))⁻¹ := by rw [neg_mul, Real.exp_neg]
  set Θ := Ax ^ α * (Ay * h) ^ (1 - α) * Real.exp ((1 - α) * istcGc α γx γy * t)
  set P := K ^ α * (Ay * Real.exp (γy * t) * (Real.exp (n * t) * h)) ^ (1 - α) with hP
  have hout' : Real.exp (-n * t) * P = Θ * a ^ α := by rw [hP, ← hout]; ring
  rw [hr, hR, ← istc_rpow_ratio hK hZ, Real.rpow_sub_one hK.ne', Real.rpow_sub_one ha.ne',
    show α * Θ * (a ^ α / a) = α * (Θ * a ^ α) / a by ring, ← hout',
    show K ^ α / K * (Ay * Real.exp (γy * t) * (Real.exp (n * t) * h)) ^ (1 - α) = P / K by
      rw [hP]; ring, hKE, hEn']
  have hEx := Real.exp_pos (γx * t)
  field_simp
  ring

/-- The slope of the reduced budget: `∂/∂a [Θa^α − (δ + γ_x + n)a] = αΘa^{α−1} − (δ + γ_x + n)`
for `a > 0`. -/
theorem istc_reduced_hasDerivAt {α Θ m a : ℝ} (ha : 0 < a) :
    HasDerivAt (fun y => Θ * y ^ α - m * y) (α * Θ * a ^ (α - 1) - m) a := by
  have h := ((Real.hasDerivAt_rpow_const (p := α) (Or.inl ha.ne')).const_mul Θ).sub
    ((hasDerivAt_id' a).const_mul m)
  convert h using 1
  ring

end AKMM.Growth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The balanced growth path of the investment-specific technical change model

AKMM, §13.3 (pp. 378–380). Along a balanced growth path capital grows at `g_K` and per-capita
consumption at `g_c`.

* With `K = k̃e^{g_K t}` and `c = c̃e^{g_c t}` the right sides of (13.9) and (13.10) are constant
  (`istc_bgp_rhs_9`, `istc_bgp_rhs_10`). The "standard candidate", capital growing at
  `γ_y + n`, is inconsistent with a balanced growth path when `γ_x > 0`
  (`istc_standard_candidate_fails`).
* Detrending turns (13.9)–(13.10) into (13.12)–(13.13) (`eq_13_12`, `eq_13_13`).
* Under (13.8) the detrended system has exactly one interior stationary point, (13.14)–(13.15)
  (`eq_13_14`, `eq_13_15`, `istc_steady_pos`, `istc_steady_unique`).
* The detrended terminal condition is (13.11) along the path (`istc_tvc_detrended`), and on the
  balanced growth path it holds iff (13.8) (`istc_bgp_tvc_iff`).
* Footnote 11, corrected: under (13.8) and `ρ > n` utility along the balanced growth path is
  finite (`istc_bgp_utility_integrable`), but (13.8) alone does not bound utility when
  `σ > 1`: with the `−1` in the utility (13.4) and `ρ < n` the integrand diverges
  (`istc_bgp_utility_unbounded`).
-/

namespace AKMM.Growth

open Real Filter Topology MeasureTheory

/-- AKMM, p. 378: along `K = k̃e^{g_K t}` the investment-sector term of (13.9) is constant:
`A_x e^{γ_x t}α(A_y e^{(γ_y+n)t}h/K)^{1−α} = αA_x(A_y h/k̃)^{1−α}`. -/
theorem istc_bgp_rhs_9 {α Ax Ay h γx γy n t k : ℝ} (hα1 : α < 1) (hAy : 0 < Ay) (hh : 0 < h)
    (hk : 0 < k) :
    Ax * Real.exp (γx * t) * α *
        (Ay * Real.exp ((γy + n) * t) * h / (k * Real.exp (istcGK α γx γy n * t))) ^ (1 - α) =
      α * Ax * (Ay * h / k) ^ (1 - α) := by
  have h1α : (1 - α) ≠ 0 := by linarith
  have e : Ay * Real.exp ((γy + n) * t) * h / (k * Real.exp (istcGK α γx γy n * t)) =
      Real.exp (-(γx / (1 - α)) * t) * (Ay * h / k) := by
    have : Real.exp (istcGK α γx γy n * t) =
        Real.exp ((γy + n) * t) * Real.exp ((γx / (1 - α)) * t) := by
      rw [← Real.exp_add]; unfold istcGK; ring_nf
    rw [this, show -(γx / (1 - α)) * t = -((γx / (1 - α)) * t) by ring, Real.exp_neg]
    field_simp
  rw [e, Real.mul_rpow (Real.exp_pos _).le (by positivity), ← Real.exp_mul,
    show -(γx / (1 - α)) * t * (1 - α) = -(γx * t) by field_simp, Real.exp_neg]
  field_simp

/-- AKMM, p. 378: along `K = k̃e^{g_K t}` and `c = c̃e^{g_c t}` the right side of (13.10) is
the constant `A_x((A_y h/k̃)^{1−α} − c̃/k̃) − δ`. -/
theorem istc_bgp_rhs_10 {α Ax Ay h δ γx γy n t k c : ℝ} (hα1 : α < 1) (hk : 0 < k) :
    Ax * ((Real.exp (istcGK α γx γy n * t) * Ay * h / (k * Real.exp (istcGK α γx γy n * t))) ^
        (1 - α) - Real.exp ((γx + n) * t) * (c * Real.exp (istcGc α γx γy * t)) /
          (k * Real.exp (istcGK α γx γy n * t))) - δ =
      Ax * ((Ay * h / k) ^ (1 - α) - c / k) - δ := by
  have e1 : Real.exp (istcGK α γx γy n * t) * Ay * h / (k * Real.exp (istcGK α γx γy n * t)) =
      Ay * h / k := by
    field_simp
  have e2 : Real.exp (istcGK α γx γy n * t) =
      Real.exp ((γx + n) * t) * Real.exp (istcGc α γx γy * t) := by
    rw [← Real.exp_add, istc_gK_eq _ _ _ _ hα1]; ring_nf
  rw [e1, e2]
  field_simp

/-- AKMM, p. 378: **the standard candidate fails**. Suppose `γ_x > 0`, `γ_y + n + δ > 0`, and
capital grows at `γ_y + n`, `K = K_0e^{(γ_y+n)t}`, while consumption grows at some constant rate
`μ`, `c = c_0e^{μt}`, with `K_0, c_0 > 0`. Then (13.10) cannot hold for all `t ≥ 0`: its right
side is `Ae^{γ_x t} − Be^{(γ_x+μ−γ_y)t} − δ` with `A, B > 0`, which is not identically
`γ_y + n`. -/
theorem istc_standard_candidate_fails {α Ax Ay h δ γx γy n μ K0 c0 : ℝ} (hα1 : α < 1)
    (hAx : 0 < Ax) (hAy : 0 < Ay) (hh : 0 < h) (hK0 : 0 < K0) (hc0 : 0 < c0) (hγx : 0 < γx)
    (hpos : 0 < γy + n + δ) :
    ¬ ∀ t, 0 ≤ t → Ax * ((Real.exp (istcGK α γx γy n * t) * Ay * h /
        (K0 * Real.exp ((γy + n) * t))) ^ (1 - α) - Real.exp ((γx + n) * t) *
          (c0 * Real.exp (μ * t)) / (K0 * Real.exp ((γy + n) * t))) - δ = γy + n := by
  intro hall
  have h1α : (1 - α) ≠ 0 := by linarith
  set A := Ax * (Ay * h / K0) ^ (1 - α) with hAdef
  set B := Ax * c0 / K0 with hBdef
  have hA : 0 < A := by positivity
  have hB : 0 < B := by positivity
  have hform : ∀ t, Ax * ((Real.exp (istcGK α γx γy n * t) * Ay * h /
      (K0 * Real.exp ((γy + n) * t))) ^ (1 - α) - Real.exp ((γx + n) * t) *
        (c0 * Real.exp (μ * t)) / (K0 * Real.exp ((γy + n) * t))) - δ =
      A * Real.exp (γx * t) - B * Real.exp ((γx + μ - γy) * t) - δ := by
    intro t
    have e1 : Real.exp (istcGK α γx γy n * t) * Ay * h / (K0 * Real.exp ((γy + n) * t)) =
        Real.exp (γx / (1 - α) * t) * (Ay * h / K0) := by
      have : Real.exp (istcGK α γx γy n * t) =
          Real.exp (γx / (1 - α) * t) * Real.exp ((γy + n) * t) := by
        rw [← Real.exp_add]; unfold istcGK; ring_nf
      rw [this]; field_simp
    have e2 : Real.exp ((γx + n) * t) * (c0 * Real.exp (μ * t)) =
        c0 * Real.exp ((γx + μ - γy) * t) * Real.exp ((γy + n) * t) := by
      have : Real.exp ((γx + n) * t) * Real.exp (μ * t) =
          Real.exp ((γx + μ - γy) * t) * Real.exp ((γy + n) * t) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      linear_combination c0 * this
    rw [e1, e2, Real.mul_rpow (Real.exp_pos _).le (by positivity), ← Real.exp_mul,
      show γx / (1 - α) * t * (1 - α) = γx * t by field_simp, hAdef, hBdef]
    field_simp
  set C := γy + n + δ
  have h0 := hall 0 le_rfl
  have h1 := hall 1 zero_le_one
  have h2 := hall 2 zero_le_two
  rw [hform] at h0 h1 h2
  simp only [mul_zero, Real.exp_zero, mul_one] at h0 h1
  set x := Real.exp γx
  set y := Real.exp (γx + μ - γy)
  have hx2 : Real.exp (γx * 2) = x ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  have hy2 : Real.exp ((γx + μ - γy) * 2) = y ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  rw [hx2, hy2] at h2
  have hx1 : 1 < x := Real.one_lt_exp_iff.mpr hγx
  have hy : 0 < y := Real.exp_pos _
  have e01 : A * (x - 1) = B * (y - 1) := by linarith
  have e12 : A * x * (x - 1) = B * y * (y - 1) := by nlinarith
  have hy1 : y ≠ 1 := by
    intro hy1
    rw [hy1, sub_self, mul_zero] at e01
    have : 0 < A * (x - 1) := mul_pos hA (by linarith)
    linarith
  have hxy : x = y := by
    have hne : B * (y - 1) ≠ 0 := mul_ne_zero hB.ne' (sub_ne_zero.mpr hy1)
    have : A * (x - 1) * x = A * (x - 1) * y := by
      calc A * (x - 1) * x = B * y * (y - 1) := by linarith
        _ = A * (x - 1) * y := by rw [e01]; ring
    exact mul_left_cancel₀ (by rw [e01]; exact hne) this
  rw [← hxy] at e01
  have hAB : A = B := by
    have := mul_right_cancel₀ (sub_ne_zero.mpr (ne_of_gt hx1)) e01
    exact this
  have hC : 0 < C := hpos
  linarith

/-- The detrending identity used for (13.12)–(13.13): `e^{γ_x t}(e^{(γ_y+n)t}/e^{g_K t})^{1−α}
= 1`. -/
theorem istc_detrend_exp {α γx γy n t : ℝ} (hα1 : α < 1) :
    Real.exp (γx * t) * (Real.exp ((γy + n) * t) / Real.exp (istcGK α γx γy n * t)) ^ (1 - α) =
      1 := by
  have h1α : (1 - α) ≠ 0 := by linarith
  rw [← Real.exp_sub, ← Real.exp_mul, ← Real.exp_add]
  unfold istcGK
  rw [Real.exp_eq_one_iff]
  field_simp
  ring

/-- AKMM, (13.12), p. 379: if per-capita consumption obeys the Euler equation (13.9) then
`c̃ = ce^{−g_c t}` obeys `c̃̇/c̃ = (αA_x(A_y h/k̃)^{1−α} − δ − γ_x − ρ)/σ − g_c`, where
`k̃ = Ke^{−g_K t}`. -/
theorem eq_13_12 {α σ ρ δ Ax Ay h γx γy n t : ℝ} {c K : ℝ → ℝ} (hα1 : α < 1) (hAy : 0 < Ay)
    (hh : 0 < h) (hK : 0 < K t)
    (h139 : HasDerivAt c (c t * ((Ax * Real.exp (γx * t) * α *
      (Ay * Real.exp ((γy + n) * t) * h / K t) ^ (1 - α) - δ - γx - ρ) / σ)) t) :
    HasDerivAt (fun s => c s * Real.exp (-(istcGc α γx γy) * s))
      (c t * Real.exp (-(istcGc α γx γy) * t) *
        ((α * Ax * (Ay * h / (K t * Real.exp (-(istcGK α γx γy n) * t))) ^ (1 - α) - δ - γx -
          ρ) / σ - istcGc α γx γy)) t := by
  have hd := h139.fun_mul ((hasDerivAt_id' t).const_mul (-(istcGc α γx γy))).exp
  convert hd using 1
  have hk : 0 < K t * Real.exp (-(istcGK α γx γy n) * t) := by positivity
  have e := istc_bgp_rhs_9 (Ax := Ax) (γx := γx) (γy := γy) (n := n) (t := t) hα1 hAy hh hk
  have e2 : K t * Real.exp (-(istcGK α γx γy n) * t) * Real.exp (istcGK α γx γy n * t) = K t := by
    rw [mul_assoc, ← Real.exp_add]; simp
  rw [e2] at e
  rw [← e]
  ring

/-- AKMM, (13.13), p. 379: if capital obeys (13.10), then `k̃ = Ke^{−g_K t}` obeys
`k̃̇/k̃ = A_x((A_y h/k̃)^{1−α} − c̃/k̃) − δ − g_K`, where `c̃ = ce^{−g_c t}`. -/
theorem eq_13_13 {α δ Ax Ay h γx γy n t : ℝ} {c K : ℝ → ℝ} (hα1 : α < 1) (hK : 0 < K t)
    (h1310 : HasDerivAt K (K t * (Ax * ((Real.exp (istcGK α γx γy n * t) * Ay * h / K t) ^
      (1 - α) - Real.exp ((γx + n) * t) * c t / K t) - δ)) t) :
    HasDerivAt (fun s => K s * Real.exp (-(istcGK α γx γy n) * s))
      (K t * Real.exp (-(istcGK α γx γy n) * t) *
        (Ax * ((Ay * h / (K t * Real.exp (-(istcGK α γx γy n) * t))) ^ (1 - α) -
          c t * Real.exp (-(istcGc α γx γy) * t) / (K t * Real.exp (-(istcGK α γx γy n) * t))) -
            δ - istcGK α γx γy n)) t := by
  have hd := h1310.fun_mul ((hasDerivAt_id' t).const_mul (-(istcGK α γx γy n))).exp
  convert hd using 1
  have hk : 0 < K t * Real.exp (-(istcGK α γx γy n) * t) := by positivity
  have e := istc_bgp_rhs_10 (Ax := Ax) (Ay := Ay) (h := h) (δ := δ) (γx := γx) (γy := γy)
    (n := n) (t := t) (c := c t * Real.exp (-(istcGc α γx γy) * t)) hα1 hk
  have e2 : K t * Real.exp (-(istcGK α γx γy n) * t) * Real.exp (istcGK α γx γy n * t) = K t := by
    rw [mul_assoc, ← Real.exp_add]; simp
  have e3 : c t * Real.exp (-(istcGc α γx γy) * t) * Real.exp (istcGc α γx γy * t) = c t := by
    rw [mul_assoc, ← Real.exp_add]; simp
  rw [e2, e3] at e
  rw [← e]
  ring

/-- AKMM, (13.14), p. 379: the detrended capital stock on the balanced growth path,
`k̃* = A_x^{1/(1−α)}A_y h(α/D)^{1/(1−α)}` with `D = ασγ_x/(1−α) + γ_x + σγ_y + δ + ρ`. -/
noncomputable def istcKStar (α σ ρ δ Ax Ay h γx γy : ℝ) : ℝ :=
  Ax ^ (1 / (1 - α)) * (Ay * h) * (α / istcD α σ ρ δ γx γy) ^ (1 / (1 - α))

/-- AKMM, (13.15), p. 379: detrended consumption on the balanced growth path,
`c̃* = k̃*^α(A_y h)^{1−α} − (g_K + δ)k̃*/A_x`. -/
noncomputable def istcCStar (α σ ρ δ Ax Ay h γx γy n : ℝ) : ℝ :=
  istcKStar α σ ρ δ Ax Ay h γx γy ^ α * (Ay * h) ^ (1 - α) -
    (istcGK α γx γy n + δ) * istcKStar α σ ρ δ Ax Ay h γx γy / Ax

/-- AKMM, (13.8) and (13.14): if `g_K + δ > 0` and (13.8) holds then `D > g_K + δ > 0`. -/
theorem istc_D_pos {α σ ρ δ γx γy n : ℝ} (hα1 : α < 1)
    (h138 : istcBound α σ ρ n γx γy < 0) :
    istcGK α γx γy n + δ < istcD α σ ρ δ γx γy := by
  have := istc_D_sub_gK α σ ρ δ γx γy n hα1
  linarith

/-- The marginal-product identity at `k̃*`: `A_x(A_y h/k̃*)^{1−α} = D/α`. -/
theorem istc_mpk_star {α σ ρ δ Ax Ay h γx γy : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hAx : 0 < Ax)
    (hAy : 0 < Ay) (hh : 0 < h) (hD : 0 < istcD α σ ρ δ γx γy) :
    Ax * (Ay * h / istcKStar α σ ρ δ Ax Ay h γx γy) ^ (1 - α) = istcD α σ ρ δ γx γy / α := by
  have h1α : 0 < 1 - α := by linarith
  set D := istcD α σ ρ δ γx γy
  unfold istcKStar
  rw [show Ay * h / (Ax ^ (1 / (1 - α)) * (Ay * h) * (α / D) ^ (1 / (1 - α))) =
      (Ax ^ (1 / (1 - α)) * (α / D) ^ (1 / (1 - α)))⁻¹ by field_simp,
    Real.inv_rpow (by positivity), Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hAx.le, ← Real.rpow_mul (by positivity), one_div_mul_cancel h1α.ne',
    Real.rpow_one, Real.rpow_one]
  field_simp

/-- AKMM, (13.14), p. 379: for `k̃ > 0`, the right side of (13.12) vanishes iff `k̃ = k̃*`. -/
theorem eq_13_14 {α σ ρ δ Ax Ay h γx γy k : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hσ : 0 < σ)
    (hAx : 0 < Ax) (hAy : 0 < Ay) (hh : 0 < h) (hD : 0 < istcD α σ ρ δ γx γy) (hk : 0 < k) :
    (α * Ax * (Ay * h / k) ^ (1 - α) - δ - γx - ρ) / σ - istcGc α γx γy = 0 ↔
      k = istcKStar α σ ρ δ Ax Ay h γx γy := by
  have h1α : 0 < 1 - α := by linarith
  have hmpk := istc_mpk_star hα0 hα1 hAx hAy hh hD
  set D := istcD α σ ρ δ γx γy with hDdef
  have hDe : D = σ * istcGc α γx γy + γx + δ + ρ := istc_D_eq α σ ρ δ γx γy
  have hiff : (α * Ax * (Ay * h / k) ^ (1 - α) - δ - γx - ρ) / σ - istcGc α γx γy = 0 ↔
      (Ay * h / k) ^ (1 - α) =
        (Ay * h / istcKStar α σ ρ δ Ax Ay h γx γy) ^ (1 - α) := by
    rw [div_sub' hσ.ne', div_eq_zero_iff, or_iff_left hσ.ne']
    have hmpk' : α * Ax * (Ay * h / istcKStar α σ ρ δ Ax Ay h γx γy) ^ (1 - α) = D := by
      rw [mul_assoc, hmpk]; field_simp
    constructor
    · intro h0
      apply mul_left_cancel₀ (mul_ne_zero hα0.ne' hAx.ne')
      rw [hmpk']
      linarith
    · intro h0
      rw [h0, hmpk']
      linarith
  rw [hiff]
  have hks : 0 < istcKStar α σ ρ δ Ax Ay h γx γy := by unfold istcKStar; positivity
  constructor
  · intro h0
    have h1 := congrArg (fun x : ℝ => x ^ (1 / (1 - α))) h0
    rw [← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity),
      mul_one_div_cancel h1α.ne', Real.rpow_one, Real.rpow_one] at h1
    field_simp at h1
    exact h1.symm
  · intro h0
    rw [h0]

/-- AKMM, (13.14)–(13.15), p. 379: under (13.8) and `g_K + δ > 0`, `k̃* > 0` and `c̃* > 0`. -/
theorem istc_steady_pos {α σ ρ δ Ax Ay h γx γy n : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hAx : 0 < Ax) (hAy : 0 < Ay) (hh : 0 < h) (hgK : 0 < istcGK α γx γy n + δ)
    (h138 : istcBound α σ ρ n γx γy < 0) :
    0 < istcKStar α σ ρ δ Ax Ay h γx γy ∧ 0 < istcCStar α σ ρ δ Ax Ay h γx γy n := by
  have hDg := istc_D_pos (δ := δ) hα1 h138
  have hD : 0 < istcD α σ ρ δ γx γy := hgK.trans hDg
  have hks : 0 < istcKStar α σ ρ δ Ax Ay h γx γy := by unfold istcKStar; positivity
  refine ⟨hks, ?_⟩
  have hmpk := istc_mpk_star hα0 hα1 hAx hAy hh hD
  set k := istcKStar α σ ρ δ Ax Ay h γx γy
  have hAh : 0 < Ay * h := by positivity
  have e : k ^ α * (Ay * h) ^ (1 - α) = k * (Ay * h / k) ^ (1 - α) := by
    rw [← istc_rpow_ratio hks hAh, Real.rpow_sub_one hks.ne']
    field_simp
  unfold istcCStar
  rw [e]
  have h2 : (Ay * h / k) ^ (1 - α) = istcD α σ ρ δ γx γy / α / Ax := by
    rw [← hmpk]; field_simp
  rw [h2]
  have : (istcGK α γx γy n + δ) < istcD α σ ρ δ γx γy / α := by
    rw [lt_div_iff₀ hα0]; nlinarith
  have : (istcGK α γx γy n + δ) / Ax < istcD α σ ρ δ γx γy / α / Ax :=
    div_lt_div_of_pos_right this hAx
  have : k * ((istcGK α γx γy n + δ) / Ax) < k * (istcD α σ ρ δ γx γy / α / Ax) :=
    mul_lt_mul_of_pos_left this hks
  have e3 : (istcGK α γx γy n + δ) * k / Ax = k * ((istcGK α γx γy n + δ) / Ax) := by ring
  linarith

/-- AKMM, (13.15), p. 379: at `k̃ = k̃* > 0`, the right side of (13.13) vanishes iff
`c̃ = c̃*`. -/
theorem eq_13_15 {α σ ρ δ Ax Ay h γx γy n c : ℝ} (hAx : 0 < Ax)
    (hks : 0 < istcKStar α σ ρ δ Ax Ay h γx γy) (hAy : 0 < Ay) (hh : 0 < h) :
    Ax * ((Ay * h / istcKStar α σ ρ δ Ax Ay h γx γy) ^ (1 - α) -
        c / istcKStar α σ ρ δ Ax Ay h γx γy) - δ - istcGK α γx γy n = 0 ↔
      c = istcCStar α σ ρ δ Ax Ay h γx γy n := by
  set k := istcKStar α σ ρ δ Ax Ay h γx γy
  have hAh : 0 < Ay * h := by positivity
  have e : k ^ α * (Ay * h) ^ (1 - α) = k * (Ay * h / k) ^ (1 - α) := by
    rw [← istc_rpow_ratio hks hAh, Real.rpow_sub_one hks.ne']
    field_simp
  unfold istcCStar
  rw [e]
  constructor
  · intro h0
    field_simp at h0 ⊢
    linarith
  · intro h0
    rw [h0]
    field_simp
    ring

/-- AKMM, (13.12)–(13.15), p. 379: **uniqueness of the balanced growth path**. Under (13.8)
and `g_K + δ > 0`, a pair `(c̃, k̃)` with `k̃ > 0` is a stationary point of (13.12)–(13.13)
(both right sides vanish) iff `(c̃, k̃) = (c̃*, k̃*)`, and then `c̃ > 0`. -/
theorem istc_steady_unique {α σ ρ δ Ax Ay h γx γy n c k : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hσ : 0 < σ) (hAx : 0 < Ax) (hAy : 0 < Ay) (hh : 0 < h) (hgK : 0 < istcGK α γx γy n + δ)
    (h138 : istcBound α σ ρ n γx γy < 0) (hk : 0 < k) :
    ((α * Ax * (Ay * h / k) ^ (1 - α) - δ - γx - ρ) / σ - istcGc α γx γy = 0 ∧
      Ax * ((Ay * h / k) ^ (1 - α) - c / k) - δ - istcGK α γx γy n = 0) ↔
      (k = istcKStar α σ ρ δ Ax Ay h γx γy ∧ c = istcCStar α σ ρ δ Ax Ay h γx γy n) := by
  have hD : 0 < istcD α σ ρ δ γx γy := hgK.trans (istc_D_pos (δ := δ) hα1 h138)
  have hpos := istc_steady_pos hα0 hα1 hAx hAy hh hgK h138
  rw [eq_13_14 hα0 hα1 hσ hAx hAy hh hD hk]
  constructor
  · rintro ⟨hk', hc⟩
    subst hk'
    exact ⟨rfl, (eq_13_15 hAx hpos.1 hAy hh).mp hc⟩
  · rintro ⟨hk', hc⟩
    subst hk'
    exact ⟨rfl, (eq_13_15 hAx hpos.1 hAy hh).mpr hc⟩

/-- AKMM, (13.11) and p. 379: the terminal term of (13.11) in detrended variables,
`(K(T)/A_x)e^{−(γ_x+ρ)T}c(T)^{−σ} = (k̃(T)c̃(T)^{−σ}/A_x)e^{(n + (1−σ)g_c − ρ)T}`, the exponent
being the left side of (13.8). -/
theorem istc_tvc_detrended {α σ ρ n Ax γx γy T k c : ℝ} (hα1 : α < 1) (hc : 0 < c) :
    k * Real.exp (istcGK α γx γy n * T) / Ax * Real.exp (-(γx + ρ) * T) *
        (c * Real.exp (istcGc α γx γy * T)) ^ (-σ) =
      k * c ^ (-σ) / Ax * Real.exp (istcBound α σ ρ n γx γy * T) := by
  rw [Real.mul_rpow hc.le (Real.exp_pos _).le, ← Real.exp_mul]
  have e : Real.exp (istcGK α γx γy n * T) * Real.exp (-(γx + ρ) * T) *
      Real.exp (istcGc α γx γy * T * -σ) = Real.exp (istcBound α σ ρ n γx γy * T) := by
    rw [← Real.exp_add, ← Real.exp_add, istc_gK_eq _ _ _ _ hα1, istc_bound_eq]
    ring_nf
  rw [← e]
  ring

/-- `C e^{bT} → 0` as `T → ∞` iff `b < 0`, for `C > 0`. -/
theorem istc_exp_tendsto_zero_iff {C b : ℝ} (hC : 0 < C) :
    Tendsto (fun T => C * Real.exp (b * T)) atTop (𝓝 0) ↔ b < 0 := by
  constructor
  · intro h
    by_contra hb'
    have hb := not_lt.mp hb'
    have hge : ∀ T, 0 ≤ T → C ≤ C * Real.exp (b * T) := fun T hT => by
      have : 1 ≤ Real.exp (b * T) := Real.one_le_exp (mul_nonneg hb hT)
      nlinarith
    have hlim : C ≤ 0 := ge_of_tendsto h (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT using hge T hT)
    linarith
  · intro hb
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (neg_pos.mpr hb))
    have h2 := h.const_mul C
    rw [mul_zero] at h2
    refine h2.congr fun T => ?_
    simp

/-- AKMM, p. 379: **the transversality condition on the balanced growth path**. For
`k̃, c̃ > 0`, the terminal condition `lim k̃c̃^{−σ}e^{(n+(1−σ)αγ_x/(1−α)+(1−σ)γ_y−ρ)T} = 0`
holds iff (13.8). -/
theorem istc_bgp_tvc_iff {α σ ρ n γx γy k c : ℝ} (hk : 0 < k) (hc : 0 < c) :
    Tendsto (fun T => k * c ^ (-σ) * Real.exp (istcBound α σ ρ n γx γy * T)) atTop (𝓝 0) ↔
      istcBound α σ ρ n γx γy < 0 :=
  istc_exp_tendsto_zero_iff (mul_pos hk (Real.rpow_pos_of_pos hc _))

/-- AKMM, (13.4) and footnote 11, p. 378: along the balanced growth path `c(t) = c̄e^{g_c t}`
the utility integrand is
`e^{−(ρ−n)t}u(c(t)) = (c̄^{1−σ}e^{(13.8)t} − e^{−(ρ−n)t})/(1 − σ)`. -/
theorem istc_bgp_utility_eq {α σ ρ n γx γy c t : ℝ} (hc : 0 < c) :
    Real.exp (-(ρ - n) * t) * (((c * Real.exp (istcGc α γx γy * t)) ^ (1 - σ) - 1) / (1 - σ)) =
      (c ^ (1 - σ) * Real.exp (istcBound α σ ρ n γx γy * t) - Real.exp (-(ρ - n) * t)) /
        (1 - σ) := by
  rw [Real.mul_rpow hc.le (Real.exp_pos _).le, ← Real.exp_mul]
  have e : Real.exp (-(ρ - n) * t) * Real.exp (istcGc α γx γy * t * (1 - σ)) =
      Real.exp (istcBound α σ ρ n γx γy * t) := by
    rw [← Real.exp_add, istc_bound_eq]; ring_nf
  rw [mul_div_assoc', mul_sub, mul_one, ← e]
  ring

/-- AKMM, footnote 11, p. 378, corrected: **utility is finite** on the balanced growth path if
(13.8) holds *and* `ρ > n`: the integrand `e^{−(ρ−n)t}u(c̄e^{g_c t})` is integrable on
`(0, ∞)`. -/
theorem istc_bgp_utility_integrable {α σ ρ n γx γy c : ℝ} (hc : 0 < c)
    (h138 : istcBound α σ ρ n γx γy < 0) (hρn : n < ρ) :
    IntegrableOn (fun t => Real.exp (-(ρ - n) * t) *
      (((c * Real.exp (istcGc α γx γy * t)) ^ (1 - σ) - 1) / (1 - σ))) (Set.Ioi 0) := by
  have e : (fun t => Real.exp (-(ρ - n) * t) *
      (((c * Real.exp (istcGc α γx γy * t)) ^ (1 - σ) - 1) / (1 - σ))) =
      fun t => (c ^ (1 - σ) / (1 - σ)) * Real.exp (-(-istcBound α σ ρ n γx γy) * t) -
        (1 / (1 - σ)) * Real.exp (-(ρ - n) * t) := by
    funext t
    rw [istc_bgp_utility_eq hc, neg_neg]
    ring
  rw [e]
  exact ((exp_neg_integrableOn_Ioi 0 (neg_pos.mpr h138)).const_mul _).sub
    ((exp_neg_integrableOn_Ioi 0 (sub_pos.mpr hρn)).const_mul _)

/-- AKMM, footnote 11, p. 378: **(13.8) alone does not bound utility**. With `σ = 2`,
`γ_x = 0`, `γ_y = 3/100`, `n = 2/100`, `ρ = 1/100` (any `α`) and `c̄ = 1`, condition (13.8)
holds (`n − ρ + (1−σ)g_c = −2/100`), but the utility integrand along the balanced growth path
is not integrable on `(0, ∞)`: it tends to `+∞`, because the constant `−1` of (13.4) is
discounted only at `ρ − n < 0`. -/
theorem istc_bgp_utility_unbounded (α : ℝ) :
    istcBound α 2 (1 / 100) (2 / 100) 0 (3 / 100) < 0 ∧
      ¬ IntegrableOn (fun t => Real.exp (-((1 / 100 : ℝ) - 2 / 100) * t) *
        (((1 * Real.exp (istcGc α 0 (3 / 100) * t)) ^ (1 - (2 : ℝ)) - 1) / (1 - 2)))
        (Set.Ioi 0) := by
  refine ⟨by unfold istcBound; norm_num, fun hint => ?_⟩
  have hge : ∀ t, 100 ≤ t → 1 ≤ Real.exp (-((1 / 100 : ℝ) - 2 / 100) * t) *
      (((1 * Real.exp (istcGc α 0 (3 / 100) * t)) ^ (1 - (2 : ℝ)) - 1) / (1 - 2)) := by
    intro t ht
    rw [istc_bgp_utility_eq one_pos, Real.one_rpow, one_mul]
    unfold istcBound
    norm_num
    have h1 : 2 ≤ Real.exp (1 / 100 * t) := by
      have := Real.add_one_le_exp (1 / 100 * t)
      linarith
    have h2 : Real.exp (-(1 / 50 * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [div_neg, div_one]
    linarith
  have hfin := Integrable.measure_norm_ge_lt_top hint one_pos
  have hsub : Set.Ioi (100 : ℝ) ⊆ {x | 1 ≤ ‖Real.exp (-((1 / 100 : ℝ) - 2 / 100) * x) *
      (((1 * Real.exp (istcGc α 0 (3 / 100) * x)) ^ (1 - (2 : ℝ)) - 1) / (1 - 2))‖} := by
    intro x hx
    change 1 ≤ ‖_‖
    have := hge x (le_of_lt (Set.mem_Ioi.mp hx))
    rw [Real.norm_eq_abs, abs_of_pos (by linarith)]
    exact this
  have hmono := measure_mono (μ := volume.restrict (Set.Ioi (0 : ℝ))) hsub
  rw [Measure.restrict_apply' measurableSet_Ioi,
    Set.inter_eq_left.mpr (Set.Ioi_subset_Ioi (by norm_num)), Real.volume_Ioi] at hmono
  exact absurd (lt_of_le_of_lt hmono hfin) (lt_irrefl _)

end AKMM.Growth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Predictions of the investment-specific technical change model

AKMM, §13.3 (pp. 380–381) and §13.4 (p. 383).

* The saving rate on the balanced growth path is `s* = α(g_K + δ)/D` (footnote 14,
  `istc_footnote_14`, `istc_saving_rate_bgp`).
* The golden rule (13.16): `k̃^{gold}` uniquely maximises steady-state consumption
  (`eq_13_16`), the golden-rule saving rate is `α` (`istc_golden_saving`), and
  `k̃* < k̃^{gold}` iff (13.8) (`istc_below_golden_iff`).
* Prices on the balanced growth path: `r* = σg_c + ρ` (`istc_r_star`); the rental rate falls at
  `γ_x` (`istc_rental_bgp`); the wage grows at `g_c` (`istc_wage_bgp`); output grows at
  `g_c + n` (`istc_output_bgp`).
* The nominal capital–output ratio is `s*/(g_K + δ) = α/D` (`istc_nominal_KY`, also (13.17)).
* The GDP deflator: the share-weighted (Divisia) deflator grows at `−s*γ_x`, not the printed
  `−(1 − s*)γ_x`; with it, real `K/Y` grows at `(1 − s*)γ_x` (`istc_deflator`,
  `istc_real_KY_growth`, `istc_deflator_printed_false`).
* For `σ = α`, the consumption rule `c̃ = φk̃` with
  `φ = (δ(1−α) + γ_x(1−α) − αn + ρ)/(αA_x)` is consistent with (13.12)–(13.13)
  (`istc_closed_form`), and the capital path has the closed form
  `k̃(t)^{1−α} = k̃*^{1−α} + (k̃(0)^{1−α} − k̃*^{1−α})e^{−(1−α)(D/α)t}`, which converges to `k̃*`
  (`istc_closed_form_path`, `istc_closed_form_converges`).
-/

namespace AKMM.Growth

open Real Filter Topology

/-- `k^α B^{1−α} = k(B/k)^{1−α}` for `k, B > 0`. -/
theorem istc_cd_eq {α k B : ℝ} (hk : 0 < k) (hB : 0 < B) :
    k ^ α * B ^ (1 - α) = k * (B / k) ^ (1 - α) := by
  rw [← istc_rpow_ratio hk hB, Real.rpow_sub_one hk.ne']
  field_simp

/-- The formula behind (13.14) and (13.16): for `X > 0`,
`k = A_x^{1/(1−α)}A_y h(α/X)^{1/(1−α)}` has `A_x(A_y h/k)^{1−α} = X/α`. -/
theorem istc_mpk_formula {α Ax Ay h X : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hAx : 0 < Ax)
    (hAy : 0 < Ay) (hh : 0 < h) (hX : 0 < X) :
    Ax * (Ay * h / (Ax ^ (1 / (1 - α)) * (Ay * h) * (α / X) ^ (1 / (1 - α)))) ^ (1 - α) =
      X / α := by
  have h1α : 0 < 1 - α := by linarith
  rw [show Ay * h / (Ax ^ (1 / (1 - α)) * (Ay * h) * (α / X) ^ (1 / (1 - α))) =
      (Ax ^ (1 / (1 - α)) * (α / X) ^ (1 / (1 - α)))⁻¹ by field_simp,
    Real.inv_rpow (by positivity), Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hAx.le, ← Real.rpow_mul (by positivity), one_div_mul_cancel h1α.ne',
    Real.rpow_one, Real.rpow_one]
  field_simp

/-- AKMM, p. 380: the saving rate on the balanced growth path, `s* = α(g_K + δ)/D`. -/
noncomputable def istcSStar (α σ ρ δ γx γy n : ℝ) : ℝ :=
  α * (istcGK α γx γy n + δ) / istcD α σ ρ δ γx γy

/-- AKMM, footnote 14, p. 380: `c̃* = (1 − s*)k̃*^α(A_y h)^{1−α}`. -/
theorem istc_footnote_14 {α σ ρ δ Ax Ay h γx γy n : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hAx : 0 < Ax) (hAy : 0 < Ay) (hh : 0 < h) (hD : 0 < istcD α σ ρ δ γx γy) :
    istcCStar α σ ρ δ Ax Ay h γx γy n =
      (1 - istcSStar α σ ρ δ γx γy n) * (istcKStar α σ ρ δ Ax Ay h γx γy ^ α *
        (Ay * h) ^ (1 - α)) := by
  have hmpk := istc_mpk_star hα0 hα1 hAx hAy hh hD
  have hks : 0 < istcKStar α σ ρ δ Ax Ay h γx γy := by unfold istcKStar; positivity
  have hAh : 0 < Ay * h := by positivity
  unfold istcCStar istcSStar
  rw [istc_cd_eq hks hAh]
  have h2 : (Ay * h / istcKStar α σ ρ δ Ax Ay h γx γy) ^ (1 - α) =
      istcD α σ ρ δ γx γy / α / Ax := by
    rw [← hmpk]; field_simp
  rw [h2]
  field_simp

/-- AKMM, p. 380: along the balanced growth path `K = k̃*e^{g_K t}`, `c = c̃*e^{g_c t}`, the
share of output not consumed, `1 − e^{nt}c/Y` with `Y = K^α(A_y e^{(γ_y+n)t}h)^{1−α}`, is the
constant `s*`. -/
theorem istc_saving_rate_bgp {α σ ρ δ Ax Ay h γx γy n t : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hAx : 0 < Ax) (hAy : 0 < Ay) (hh : 0 < h) (hD : 0 < istcD α σ ρ δ γx γy) :
    1 - Real.exp (n * t) * (istcCStar α σ ρ δ Ax Ay h γx γy n *
        Real.exp (istcGc α γx γy * t)) /
      ((istcKStar α σ ρ δ Ax Ay h γx γy * Real.exp (istcGK α γx γy n * t)) ^ α *
        (Ay * Real.exp ((γy + n) * t) * h) ^ (1 - α)) = istcSStar α σ ρ δ γx γy n := by
  have hks : 0 < istcKStar α σ ρ δ Ax Ay h γx γy := by unfold istcKStar; positivity
  have hAh : 0 < Ay * h := by positivity
  set k := istcKStar α σ ρ δ Ax Ay h γx γy
  have hY : (k * Real.exp (istcGK α γx γy n * t)) ^ α * (Ay * Real.exp ((γy + n) * t) * h) ^
      (1 - α) = k ^ α * (Ay * h) ^ (1 - α) * Real.exp ((istcGc α γx γy + n) * t) := by
    rw [Real.mul_rpow hks.le (Real.exp_pos _).le, ← Real.exp_mul,
      show Ay * Real.exp ((γy + n) * t) * h = Ay * h * Real.exp ((γy + n) * t) by ring,
      Real.mul_rpow hAh.le (Real.exp_pos _).le, ← Real.exp_mul]
    have e : Real.exp (istcGK α γx γy n * t * α) * Real.exp ((γy + n) * t * (1 - α)) =
        Real.exp ((istcGc α γx γy + n) * t) := by
      rw [← Real.exp_add]
      congr 1
      unfold istcGK istcGc
      have : (1 - α) ≠ 0 := by linarith
      field_simp
      ring
    rw [← e]
    ring
  rw [hY, istc_footnote_14 hα0 hα1 hAx hAy hh hD]
  have hE : Real.exp ((istcGc α γx γy + n) * t) =
      Real.exp (n * t) * Real.exp (istcGc α γx γy * t) := by
    rw [← Real.exp_add]; ring_nf
  rw [hE]
  have : 0 < k ^ α * (Ay * h) ^ (1 - α) := by positivity
  field_simp
  ring

/-- AKMM, (13.16), p. 380: the golden-rule capital stock
`k̃^{gold} = A_x^{1/(1−α)}A_y h(α/(g_K + δ))^{1/(1−α)}`. -/
noncomputable def istcKGold (α δ Ax Ay h γx γy n : ℝ) : ℝ :=
  Ax ^ (1 / (1 - α)) * (Ay * h) * (α / (istcGK α γx γy n + δ)) ^ (1 / (1 - α))

/-- AKMM, (13.15) as a function of `k̃`: steady-state consumption
`c̃(k̃) = k̃^α(A_y h)^{1−α} − (g_K + δ)k̃/A_x`. -/
noncomputable def istcSteadyC (α δ Ax Ay h γx γy n k : ℝ) : ℝ :=
  k ^ α * (Ay * h) ^ (1 - α) - (istcGK α γx γy n + δ) * k / Ax

/-- AKMM, (13.16), p. 380: **the golden rule**. If `g_K + δ > 0`, `k̃^{gold}` is the unique
maximiser of steady-state consumption (13.15) over `k̃ > 0`. -/
theorem eq_13_16 {α δ Ax Ay h γx γy n k : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hAx : 0 < Ax)
    (hAy : 0 < Ay) (hh : 0 < h) (hgK : 0 < istcGK α γx γy n + δ) (hk : 0 < k)
    (hne : k ≠ istcKGold α δ Ax Ay h γx γy n) :
    istcSteadyC α δ Ax Ay h γx γy n k <
      istcSteadyC α δ Ax Ay h γx γy n (istcKGold α δ Ax Ay h γx γy n) := by
  set kg := istcKGold α δ Ax Ay h γx γy n
  have hkg : 0 < kg := by simp only [kg, istcKGold]; positivity
  have hAh : 0 < Ay * h := by positivity
  have hmpk : Ax * (Ay * h / kg) ^ (1 - α) = (istcGK α γx γy n + δ) / α :=
    istc_mpk_formula hα0 hα1 hAx hAy hh hgK
  set B := (Ay * h) ^ (1 - α)
  have hB : 0 < B := by positivity
  have hbern := rpow_one_add_lt_one_add_mul_self (s := k / kg - 1) (by
    have : 0 < k / kg := div_pos hk hkg
    linarith) (by
      intro h0
      apply hne
      have : k / kg = 1 := by linarith
      field_simp at this
      linarith) hα0 hα1
  rw [show 1 + (k / kg - 1) = k / kg by ring, Real.div_rpow hk.le hkg.le] at hbern
  have hkga : 0 < kg ^ α := by positivity
  rw [div_lt_iff₀ hkga] at hbern
  have hslope : α * B * kg ^ (α - 1) = (istcGK α γx γy n + δ) / Ax := by
    have e : B * kg ^ (α - 1) = (Ay * h / kg) ^ (1 - α) := by
      rw [mul_comm, istc_rpow_ratio hkg hAh]
    have h3 : α * (Ax * (Ay * h / kg) ^ (1 - α)) = istcGK α γx γy n + δ := by
      rw [hmpk]; field_simp
    rw [mul_assoc, e, eq_div_iff hAx.ne']
    linarith [h3]
  have hkg1 : kg ^ (α - 1) = kg ^ α / kg := Real.rpow_sub_one hkg.ne' α
  unfold istcSteadyC
  rw [hkg1] at hslope
  have key : B * k ^ α < B * kg ^ α + α * B * (kg ^ α / kg) * (k - kg) := by
    have h1 : B * k ^ α < B * ((1 + α * (k / kg - 1)) * kg ^ α) :=
      mul_lt_mul_of_pos_left hbern hB
    have e : B * ((1 + α * (k / kg - 1)) * kg ^ α) =
        B * kg ^ α + α * B * (kg ^ α / kg) * (k - kg) := by
      field_simp
    linarith
  rw [hslope] at key
  have e2 : (istcGK α γx γy n + δ) / Ax * (k - kg) =
      (istcGK α γx γy n + δ) * k / Ax - (istcGK α γx γy n + δ) * kg / Ax := by ring
  rw [mul_comm (k ^ α), mul_comm (kg ^ α)]
  linarith

/-- AKMM, p. 380: **the golden-rule saving rate is `α`**: at `k̃^{gold}` the share
`(g_K + δ)k̃/(A_x k̃^α(A_y h)^{1−α})` of output saved is `α`. -/
theorem istc_golden_saving {α δ Ax Ay h γx γy n : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hAx : 0 < Ax) (hAy : 0 < Ay) (hh : 0 < h) (hgK : 0 < istcGK α γx γy n + δ) :
    (istcGK α γx γy n + δ) * istcKGold α δ Ax Ay h γx γy n /
        (Ax * (istcKGold α δ Ax Ay h γx γy n ^ α * (Ay * h) ^ (1 - α))) = α := by
  set kg := istcKGold α δ Ax Ay h γx γy n
  have hkg : 0 < kg := by simp only [kg, istcKGold]; positivity
  have hAh : 0 < Ay * h := by positivity
  have hmpk : Ax * (Ay * h / kg) ^ (1 - α) = (istcGK α γx γy n + δ) / α :=
    istc_mpk_formula hα0 hα1 hAx hAy hh hgK
  rw [istc_cd_eq hkg hAh, show Ax * (kg * (Ay * h / kg) ^ (1 - α)) =
    kg * (Ax * (Ay * h / kg) ^ (1 - α)) by ring, hmpk]
  field_simp

/-- AKMM, p. 380: **`k̃* < k̃^{gold}` iff (13.8)**, when `g_K + δ > 0` and `D > 0`. -/
theorem istc_below_golden_iff {α σ ρ δ Ax Ay h γx γy n : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hAx : 0 < Ax) (hAy : 0 < Ay) (hh : 0 < h) (hgK : 0 < istcGK α γx γy n + δ)
    (hD : 0 < istcD α σ ρ δ γx γy) :
    istcKStar α σ ρ δ Ax Ay h γx γy < istcKGold α δ Ax Ay h γx γy n ↔
      istcBound α σ ρ n γx γy < 0 := by
  have h1α : 0 < 1 / (1 - α) := by apply div_pos one_pos; linarith
  have hsub := istc_D_sub_gK α σ ρ δ γx γy n hα1
  unfold istcKStar istcKGold
  have hc : 0 < Ax ^ (1 / (1 - α)) * (Ay * h) := by positivity
  rw [mul_lt_mul_iff_right₀ hc, Real.rpow_lt_rpow_iff (by positivity) (by positivity) h1α,
    div_lt_div_iff_of_pos_left hα0 hD hgK]
  constructor <;> intro h <;> linarith

/-- AKMM, p. 380: **the interest rate on the balanced growth path**, `r* = σg_c + ρ`: the
return (13.A.3) at `k̃*` is `αA_x(A_y h/k̃*)^{1−α} − δ − γ_x = σg_c + ρ`. -/
theorem istc_r_star {α σ ρ δ Ax Ay h γx γy : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hAx : 0 < Ax)
    (hAy : 0 < Ay) (hh : 0 < h) (hD : 0 < istcD α σ ρ δ γx γy) :
    α * Ax * (Ay * h / istcKStar α σ ρ δ Ax Ay h γx γy) ^ (1 - α) - δ - γx =
      σ * istcGc α γx γy + ρ := by
  rw [mul_assoc, istc_mpk_star hα0 hα1 hAx hAy hh hD, istc_D_eq]
  field_simp
  ring

/-- AKMM, p. 380: on the balanced growth path `K = k̃e^{g_K t}` the rental rate
`R(t) = α(A_y e^{(γ_y+n)t}h/K)^{1−α}` falls at the rate `γ_x`:
`R(t) = α(A_y h/k̃)^{1−α}e^{−γ_x t}`. -/
theorem istc_rental_bgp {α Ay h γx γy n t k : ℝ} (hα1 : α < 1) (hAy : 0 < Ay) (hh : 0 < h)
    (hk : 0 < k) :
    α * (Ay * Real.exp ((γy + n) * t) * h / (k * Real.exp (istcGK α γx γy n * t))) ^ (1 - α) =
      α * (Ay * h / k) ^ (1 - α) * Real.exp (-γx * t) := by
  have e := istc_bgp_rhs_9 (Ax := 1) (γx := γx) (γy := γy) (n := n) (t := t) hα1 hAy hh hk
  have hE : Real.exp (γx * t) * Real.exp (-γx * t) = 1 := by rw [← Real.exp_add]; simp
  have e2 : α * (Ay * Real.exp ((γy + n) * t) * h / (k * Real.exp (istcGK α γx γy n * t))) ^
      (1 - α) = (1 * Real.exp (γx * t) * α * (Ay * Real.exp ((γy + n) * t) * h /
        (k * Real.exp (istcGK α γx γy n * t))) ^ (1 - α)) * Real.exp (-γx * t) := by
    linear_combination (-(α * (Ay * Real.exp ((γy + n) * t) * h /
      (k * Real.exp (istcGK α γx γy n * t))) ^ (1 - α))) * hE
  rw [e2, e]
  ring

/-- AKMM, p. 380: on the balanced growth path the wage (13.A.2),
`w(t) = (1−α)A_y e^{γ_y t}(K/(A_y e^{(γ_y+n)t}h))^α`, grows at `g_c`:
`w(t) = (1−α)A_y(k̃/(A_y h))^α e^{g_c t}`. -/
theorem istc_wage_bgp {α Ay h γx γy n t k : ℝ} (hα1 : α < 1) (hAy : 0 < Ay) (hh : 0 < h)
    (hk : 0 < k) :
    (1 - α) * (Ay * Real.exp (γy * t)) *
        (k * Real.exp (istcGK α γx γy n * t) / (Ay * Real.exp ((γy + n) * t) * h)) ^ α =
      (1 - α) * Ay * (k / (Ay * h)) ^ α * Real.exp (istcGc α γx γy * t) := by
  have h1α : (1 - α) ≠ 0 := by linarith
  have e : k * Real.exp (istcGK α γx γy n * t) / (Ay * Real.exp ((γy + n) * t) * h) =
      k / (Ay * h) * Real.exp (γx / (1 - α) * t) := by
    have : Real.exp (istcGK α γx γy n * t) =
        Real.exp ((γy + n) * t) * Real.exp ((γx / (1 - α)) * t) := by
      rw [← Real.exp_add]; unfold istcGK; ring_nf
    rw [this]
    field_simp
  rw [e, Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul]
  have e2 : Real.exp (γy * t) * Real.exp (γx / (1 - α) * t * α) =
      Real.exp (istcGc α γx γy * t) := by
    rw [← Real.exp_add]; unfold istcGc; congr 1; field_simp; ring
  rw [← e2]
  ring

/-- AKMM, p. 380: on the balanced growth path output
`Y(t) = K^α(A_y e^{(γ_y+n)t}h)^{1−α}` grows at `g_c + n`. -/
theorem istc_output_bgp {α Ay h γx γy n t k : ℝ} (hα1 : α < 1) (hAy : 0 < Ay) (hh : 0 < h)
    (hk : 0 < k) :
    (k * Real.exp (istcGK α γx γy n * t)) ^ α * (Ay * Real.exp ((γy + n) * t) * h) ^ (1 - α) =
      k ^ α * (Ay * h) ^ (1 - α) * Real.exp ((istcGc α γx γy + n) * t) := by
  have hAh : 0 < Ay * h := by positivity
  rw [Real.mul_rpow hk.le (Real.exp_pos _).le, ← Real.exp_mul,
    show Ay * Real.exp ((γy + n) * t) * h = Ay * h * Real.exp ((γy + n) * t) by ring,
    Real.mul_rpow hAh.le (Real.exp_pos _).le, ← Real.exp_mul]
  have e : Real.exp (istcGK α γx γy n * t * α) * Real.exp ((γy + n) * t * (1 - α)) =
      Real.exp ((istcGc α γx γy + n) * t) := by
    rw [← Real.exp_add]
    congr 1
    unfold istcGK istcGc
    have : (1 - α) ≠ 0 := by linarith
    field_simp
    ring
  rw [← e]
  ring

/-- AKMM, p. 380 and (13.17): **the nominal capital–output ratio** on the balanced growth path,
`e^{−γ_x t}A_x^{−1}K/Y`, is the constant `s*/(g_K + δ) = α/D`. -/
theorem istc_nominal_KY {α σ ρ δ Ax Ay h γx γy n t : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hAx : 0 < Ax) (hAy : 0 < Ay) (hh : 0 < h) (hgK : 0 < istcGK α γx γy n + δ)
    (hD : 0 < istcD α σ ρ δ γx γy) :
    Real.exp (-γx * t) / Ax * (istcKStar α σ ρ δ Ax Ay h γx γy *
        Real.exp (istcGK α γx γy n * t)) /
      ((istcKStar α σ ρ δ Ax Ay h γx γy * Real.exp (istcGK α γx γy n * t)) ^ α *
        (Ay * Real.exp ((γy + n) * t) * h) ^ (1 - α)) =
      istcSStar α σ ρ δ γx γy n / (istcGK α γx γy n + δ) ∧
    istcSStar α σ ρ δ γx γy n / (istcGK α γx γy n + δ) = α / istcD α σ ρ δ γx γy := by
  have hks : 0 < istcKStar α σ ρ δ Ax Ay h γx γy := by unfold istcKStar; positivity
  have hAh : 0 < Ay * h := by positivity
  have hmpk := istc_mpk_star hα0 hα1 hAx hAy hh hD
  set k := istcKStar α σ ρ δ Ax Ay h γx γy
  have hs : istcSStar α σ ρ δ γx γy n / (istcGK α γx γy n + δ) = α / istcD α σ ρ δ γx γy := by
    unfold istcSStar; field_simp
  refine ⟨?_, hs⟩
  rw [hs, istc_output_bgp hα1 hAy hh hks, istc_cd_eq hks hAh]
  have h2 : (Ay * h / k) ^ (1 - α) = istcD α σ ρ δ γx γy / α / Ax := by
    rw [← hmpk]; field_simp
  rw [h2]
  have e : Real.exp (-γx * t) * Real.exp (istcGK α γx γy n * t) =
      Real.exp ((istcGc α γx γy + n) * t) := by
    rw [← Real.exp_add, istc_gK_eq _ _ _ _ hα1]; ring_nf
  have hE := Real.exp_pos ((istcGc α γx γy + n) * t)
  rw [show Real.exp (-γx * t) / Ax * (k * Real.exp (istcGK α γx γy n * t)) =
    k / Ax * (Real.exp (-γx * t) * Real.exp (istcGK α γx γy n * t)) by ring, e]
  field_simp

/-- AKMM, p. 380: the share-weighted (Divisia) growth rate of the GDP deflator,
`s*(Ṗ_x/P_x) + (1 − s*)(Ṗ_c/P_c)`, with `Ṗ_x/P_x = −γ_x` and `Ṗ_c/P_c = 0`, is `−s*γ_x`. -/
theorem istc_deflator {s γx : ℝ} : s * (-γx) + (1 - s) * 0 = -(s * γx) := by ring

/-- AKMM, p. 380: **real capital–output growth**. Real output grows at nominal growth
(`g_c + n`, in consumption units) minus deflator growth `−s*γ_x`, which is also the Divisia
quantity index `s*g_K + (1 − s*)(g_c + n)`; real capital grows at `g_K`. Hence real `K/Y` grows
at `(1 − s*)γ_x`. -/
theorem istc_real_KY_growth {α γx γy n s : ℝ} (hα1 : α < 1) :
    istcGc α γx γy + n - (-(s * γx)) = s * istcGK α γx γy n + (1 - s) * (istcGc α γx γy + n) ∧
      istcGK α γx γy n - (istcGc α γx γy + n - (-(s * γx))) = (1 - s) * γx := by
  rw [istc_gK_eq _ _ _ _ hα1]
  constructor <;> ring

/-- AKMM, p. 380: **the printed deflator is wrong**. The printed growth rate `−(1 − s*)γ_x`
equals the share-weighted `−s*γ_x` only if `γ_x = 0` or `s* = 1/2`; with it, real `K/Y` would
grow at `s*γ_x`, not the stated `(1 − s*)γ_x` (unless `γ_x = 0` or `s* = 1/2`). Read literally,
the product `(Ṗ_x/P_x)^{s*}(Ṗ_c/P_c)^{1−s*}` is `0` for `s* < 1`, since `Ṗ_c = 0`. -/
theorem istc_deflator_printed_false {α γx γy n s : ℝ} (hα1 : α < 1) (hs1 : s < 1) :
    (-((1 - s) * γx) = -(s * γx) ↔ γx = 0 ∨ s = 1 / 2) ∧
      istcGK α γx γy n - (istcGc α γx γy + n - (-((1 - s) * γx))) = s * γx ∧
      (-γx) ^ s * (0 : ℝ) ^ (1 - s) = 0 := by
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ?_, ?_⟩
  · have : γx * (1 - 2 * s) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  · rcases h with h0 | h0
    · rw [h0]; ring
    · rw [h0]; ring
  · rw [istc_gK_eq _ _ _ _ hα1]; ring
  · rw [Real.zero_rpow (by linarith), mul_zero]

/-- AKMM, p. 381: the closed-form consumption–capital ratio for `σ = α`,
`φ = (δ(1−α) + γ_x(1−α) − αn + ρ)/(αA_x)`. -/
noncomputable def istcPhi (α ρ δ Ax γx n : ℝ) : ℝ :=
  (δ * (1 - α) + γx * (1 - α) - α * n + ρ) / (α * Ax)

/-- AKMM, p. 381: for `σ = α` and `c̃ = φk̃`, the growth rates (13.12) and (13.13) coincide for
every `k̃ > 0`, so the consumption rule is "globally consistent" with the system. -/
theorem istc_closed_form_rhs {α ρ δ Ax Ay h γx γy n k : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hAx : 0 < Ax) (hk : 0 < k) :
    Ax * ((Ay * h / k) ^ (1 - α) - istcPhi α ρ δ Ax γx n * k / k) - δ - istcGK α γx γy n =
      (α * Ax * (Ay * h / k) ^ (1 - α) - δ - γx - ρ) / α - istcGc α γx γy := by
  have h1α : (1 - α) ≠ 0 := by linarith
  unfold istcPhi istcGK istcGc
  field_simp
  ring

/-- AKMM, p. 381: **the closed form for `σ = α`**. If `k̃` satisfies (13.13) with the rule
`c̃ = φk̃`, then `c̃ = φk̃` satisfies (13.12) with `σ = α`. -/
theorem istc_closed_form {α ρ δ Ax Ay h γx γy n t : ℝ} {k : ℝ → ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) (hAx : 0 < Ax) (hk : 0 < k t)
    (h1313 : HasDerivAt k (k t * (Ax * ((Ay * h / k t) ^ (1 - α) -
      istcPhi α ρ δ Ax γx n * k t / k t) - δ - istcGK α γx γy n)) t) :
    HasDerivAt (fun s => istcPhi α ρ δ Ax γx n * k s)
      (istcPhi α ρ δ Ax γx n * k t * ((α * Ax * (Ay * h / k t) ^ (1 - α) - δ - γx - ρ) / α -
        istcGc α γx γy)) t := by
  rw [istc_closed_form_rhs (Ay := Ay) (h := h) (γy := γy) hα0 hα1 hAx hk] at h1313
  rw [mul_assoc]
  exact h1313.const_mul _

/-- AKMM, p. 381, with `σ = α`: `A_xφ + δ + g_K = D/α`, so the closed-form path converges at the
rate `(1 − α)D/α`. -/
theorem istc_closed_form_rate {α ρ δ Ax γx γy n : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hAx : 0 < Ax) :
    Ax * istcPhi α ρ δ Ax γx n + δ + istcGK α γx γy n = istcD α α ρ δ γx γy / α := by
  have h1α : (1 - α) ≠ 0 := by linarith
  unfold istcPhi istcGK istcD
  field_simp
  ring

/-- AKMM, p. 381: **the closed-form transition for `σ = α`**. With `z* = k̃*^{1−α}` and
`λ = (1 − α)D/α`, the path `k̃(t) = (z* + (k̃_0^{1−α} − z*)e^{−λt})^{1/(1−α)}` starts at `k̃_0` and,
for `t ≥ 0`, satisfies (13.13) with `c̃ = φk̃`. -/
theorem istc_closed_form_path {α ρ δ Ax Ay h γx γy n k0 t : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hAx : 0 < Ax) (hAy : 0 < Ay) (hh : 0 < h) (hk0 : 0 < k0) (hD : 0 < istcD α α ρ δ γx γy)
    (ht : 0 ≤ t) :
    let zs := istcKStar α α ρ δ Ax Ay h γx γy ^ (1 - α)
    let lam := (1 - α) * (istcD α α ρ δ γx γy / α)
    let k := fun s => (zs + (k0 ^ (1 - α) - zs) * Real.exp (-lam * s)) ^ (1 / (1 - α))
    k 0 = k0 ∧ 0 < k t ∧
      HasDerivAt k (k t * (Ax * ((Ay * h / k t) ^ (1 - α) - istcPhi α ρ δ Ax γx n * k t / k t) -
        δ - istcGK α γx γy n)) t := by
  intro zs lam k
  have h1α : 0 < 1 - α := by linarith
  have hks : 0 < istcKStar α α ρ δ Ax Ay h γx γy := by unfold istcKStar; positivity
  have hzs : 0 < zs := by positivity
  have hlam : 0 < lam := by positivity
  set u := fun s => zs + (k0 ^ (1 - α) - zs) * Real.exp (-lam * s) with hu
  have hupos : 0 < u t := by
    have hE : Real.exp (-lam * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hE0 := Real.exp_pos (-lam * t)
    have hk0p : 0 < k0 ^ (1 - α) := by positivity
    have : u t = zs * (1 - Real.exp (-lam * t)) + k0 ^ (1 - α) * Real.exp (-lam * t) := by
      simp only [hu]; ring
    rw [this]
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · simp only [k, mul_zero, Real.exp_zero, mul_one, add_sub_cancel]
    rw [← Real.rpow_mul hk0.le, mul_one_div_cancel h1α.ne', Real.rpow_one]
  · exact Real.rpow_pos_of_pos hupos _
  · have hud : HasDerivAt u ((k0 ^ (1 - α) - zs) * (Real.exp (-lam * t) * -lam)) t := by
      have := (((hasDerivAt_id' t).const_mul (-lam)).exp).const_mul (k0 ^ (1 - α) - zs)
      convert this.const_add zs using 1
      ring
    have hd := hud.rpow_const (p := 1 / (1 - α)) (Or.inl hupos.ne')
    change HasDerivAt (fun s => u s ^ (1 / (1 - α))) _ t
    convert hd using 1
    -- the algebra: express everything through `u t`
    have hkt : k t = u t ^ (1 / (1 - α)) := rfl
    have hpow : k t ^ (1 - α) = u t := by
      rw [hkt, ← Real.rpow_mul hupos.le, one_div_mul_cancel h1α.ne', Real.rpow_one]
    have hktpos : 0 < k t := Real.rpow_pos_of_pos hupos _
    have hAh : 0 < Ay * h := by positivity
    have hratio : (Ay * h / k t) ^ (1 - α) = (Ay * h) ^ (1 - α) / u t := by
      rw [Real.div_rpow hAh.le hktpos.le, hpow]
    have hrate := istc_closed_form_rate (γy := γy) (n := n) (ρ := ρ) (δ := δ) (γx := γx)
      hα0 hα1 hAx
    have hzsv : zs * (istcD α α ρ δ γx γy / α) = Ax * (Ay * h) ^ (1 - α) := by
      have hmpk := istc_mpk_star hα0 hα1 hAx hAy hh hD
      have e := istc_cd_eq (α := α) hks hAh
      simp only [zs]
      rw [← hmpk, Real.div_rpow hAh.le hks.le]
      field_simp
    have hexp : u t ^ (1 / (1 - α) - 1) = k t / u t := by
      rw [Real.rpow_sub_one hupos.ne', hkt]
    have hEd : (k0 ^ (1 - α) - zs) * Real.exp (-lam * t) = u t - zs := by simp only [hu]; ring
    have e1 : (k0 ^ (1 - α) - zs) * (Real.exp (-lam * t) * -lam) = -lam * (u t - zs) := by
      rw [← hEd]; ring
    have hφ : istcPhi α ρ δ Ax γx n * k t / k t = istcPhi α ρ δ Ax γx n := by
      field_simp
    have e2 : Ax * ((Ay * h) ^ (1 - α) / u t - istcPhi α ρ δ Ax γx n) - δ - istcGK α γx γy n =
        zs * (istcD α α ρ δ γx γy / α) / u t - istcD α α ρ δ γx γy / α := by
      rw [mul_sub, mul_div_assoc', ← hzsv]
      linarith [hrate]
    rw [hexp, e1, hratio, hφ, e2]
    simp only [lam]
    field_simp
    ring

/-- AKMM, p. 381: the closed-form path of `istc_closed_form_path` converges to `k̃*`, so that
`k̃` "increases over time until it asymptotically reaches `k̃*`" (for `k̃_0 < k̃*`). -/
theorem istc_closed_form_converges {α ρ δ Ax Ay h γx γy k0 : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hAx : 0 < Ax) (hAy : 0 < Ay) (hh : 0 < h) (hD : 0 < istcD α α ρ δ γx γy) :
    Tendsto (fun s => (istcKStar α α ρ δ Ax Ay h γx γy ^ (1 - α) +
        (k0 ^ (1 - α) - istcKStar α α ρ δ Ax Ay h γx γy ^ (1 - α)) *
          Real.exp (-((1 - α) * (istcD α α ρ δ γx γy / α)) * s)) ^ (1 / (1 - α))) atTop
      (𝓝 (istcKStar α α ρ δ Ax Ay h γx γy)) := by
  have h1α : 0 < 1 - α := by linarith
  have hks : 0 < istcKStar α α ρ δ Ax Ay h γx γy := by unfold istcKStar; positivity
  set zs := istcKStar α α ρ δ Ax Ay h γx γy ^ (1 - α)
  have hlam : 0 < (1 - α) * (istcD α α ρ δ γx γy / α) := by positivity
  have hE : Tendsto (fun s => Real.exp (-((1 - α) * (istcD α α ρ δ γx γy / α)) * s)) atTop
      (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hlam)
    refine this.congr fun s => ?_
    simp [neg_mul]
  have hu : Tendsto (fun s => zs + (k0 ^ (1 - α) - zs) *
      Real.exp (-((1 - α) * (istcD α α ρ δ γx γy / α)) * s)) atTop (𝓝 zs) := by
    have := (hE.const_mul (k0 ^ (1 - α) - zs)).const_add zs
    simpa using this
  have hzs : 0 < zs := by positivity
  have hc := (Real.continuousAt_rpow_const zs (1 / (1 - α)) (Or.inl hzs.ne')).tendsto.comp hu
  have hk : zs ^ (1 / (1 - α)) = istcKStar α α ρ δ Ax Ay h γx γy := by
    simp only [zs]
    rw [← Real.rpow_mul hks.le, mul_one_div_cancel h1α.ne', Real.rpow_one]
  rw [hk] at hc
  exact hc

end AKMM.Growth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Local dynamics around the balanced growth path

AKMM, §13.3 (p. 381) and Appendix 13.A.3 (pp. 851–852). Write the detrended system
(13.12)–(13.13) as `c̃̇ = F_c(c̃, k̃)`, `k̃̇ = F_k(c̃, k̃)` (`istcFc`, `istcFk`).

* The partial derivatives at `(c̃*, k̃*)` are the entries of the Jacobian (13.A.14)
  (`eq_13_A_14`).
* The characteristic equation `det(A − zI) = 0` is (13.A.15) (`eq_13_A_15`).
* Under (13.8) the right side of (13.A.15) is positive and the second zero of its left side is
  positive; both roots are real, one strictly negative and one strictly positive, and the stable
  root is the printed `½b(1 − √(1 + 4Q/b²))` (`istc_eigenvalues`, `istc_stable_root`,
  `istc_saddle`).
* The half-life of a deviation decaying at `e^{zt}` is `ln(1/2)/z` (`istc_half_life`).
-/

namespace AKMM.Growth

open Real

/-- AKMM, (13.12): `c̃̇ = F_c(c̃, k̃) = c̃((αA_x(A_y h)^{1−α}k̃^{α−1} − δ − γ_x − ρ)/σ − g_c)`. -/
noncomputable def istcFc (α σ ρ δ Ax Ay h γx γy c k : ℝ) : ℝ :=
  c * ((α * Ax * (Ay * h) ^ (1 - α) * k ^ (α - 1) - δ - γx - ρ) / σ - istcGc α γx γy)

/-- AKMM, (13.13): `k̃̇ = F_k(c̃, k̃) = A_x(A_y h)^{1−α}k̃^α − A_x c̃ − (δ + g_K)k̃`. -/
noncomputable def istcFk (α δ Ax Ay h γx γy n c k : ℝ) : ℝ :=
  Ax * (Ay * h) ^ (1 - α) * k ^ α - Ax * c - (δ + istcGK α γx γy n) * k

/-- `F_c` and `F_k` are (13.12)–(13.13) multiplied by `c̃` and `k̃`. -/
theorem istc_F_eq {α σ ρ δ Ax Ay h γx γy n c k : ℝ} (hk : 0 < k) (hAy : 0 < Ay) (hh : 0 < h) :
    istcFc α σ ρ δ Ax Ay h γx γy c k =
        c * ((α * Ax * (Ay * h / k) ^ (1 - α) - δ - γx - ρ) / σ - istcGc α γx γy) ∧
      istcFk α δ Ax Ay h γx γy n c k =
        k * (Ax * ((Ay * h / k) ^ (1 - α) - c / k) - δ - istcGK α γx γy n) := by
  have hAh : 0 < Ay * h := by positivity
  have e : (Ay * h) ^ (1 - α) * k ^ (α - 1) = (Ay * h / k) ^ (1 - α) := by
    rw [mul_comm, istc_rpow_ratio hk hAh]
  constructor
  · unfold istcFc
    rw [mul_assoc (α * Ax), e]
  · unfold istcFk
    have e2 : (Ay * h) ^ (1 - α) * k ^ α = k * (Ay * h / k) ^ (1 - α) := by
      rw [mul_comm, istc_cd_eq hk hAh]
    rw [mul_assoc Ax, e2]
    field_simp
    ring

/-- AKMM, (13.A.14), p. 851: **the Jacobian at the balanced growth path**. At `(c̃*, k̃*)`:
`∂F_c/∂c̃ = 0`, `∂F_c/∂k̃ = −(1−α)αA_x(A_y h)^{1−α}k̃*^{α−2}c̃*/σ`, `∂F_k/∂c̃ = −A_x` and
`∂F_k/∂k̃ = ρ − n − γ_xα(1−σ)/(1−α) − γ_y(1−σ)`. -/
theorem eq_13_A_14 {α σ ρ δ Ax Ay h γx γy n : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hσ : 0 < σ)
    (hAx : 0 < Ax) (hAy : 0 < Ay) (hh : 0 < h) (hD : 0 < istcD α σ ρ δ γx γy) :
    let ks := istcKStar α σ ρ δ Ax Ay h γx γy
    let cs := istcCStar α σ ρ δ Ax Ay h γx γy n
    HasDerivAt (fun c => istcFc α σ ρ δ Ax Ay h γx γy c ks) 0 cs ∧
      HasDerivAt (fun k => istcFc α σ ρ δ Ax Ay h γx γy cs k)
        (-((1 - α) * α * Ax * (Ay * h) ^ (1 - α) * ks ^ (α - 2) * cs / σ)) ks ∧
      HasDerivAt (fun c => istcFk α δ Ax Ay h γx γy n c ks) (-Ax) cs ∧
      HasDerivAt (fun k => istcFk α δ Ax Ay h γx γy n cs k)
        (ρ - n - γx * (α * (1 - σ) / (1 - α)) - γy * (1 - σ)) ks := by
  intro ks cs
  have hks : 0 < ks := by simp only [ks, istcKStar]; positivity
  have hAh : 0 < Ay * h := by positivity
  have hmpk := istc_mpk_star hα0 hα1 hAx hAy hh hD
  have hmpk' : α * Ax * (Ay * h) ^ (1 - α) * ks ^ (α - 1) = istcD α σ ρ δ γx γy := by
    have e : (Ay * h) ^ (1 - α) * ks ^ (α - 1) = (Ay * h / ks) ^ (1 - α) := by
      rw [mul_comm, istc_rpow_ratio hks hAh]
    rw [mul_assoc (α * Ax), e, mul_assoc, hmpk]
    field_simp
  have hzero : (α * Ax * (Ay * h) ^ (1 - α) * ks ^ (α - 1) - δ - γx - ρ) / σ -
      istcGc α γx γy = 0 := by
    rw [hmpk', istc_D_eq]
    field_simp
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := (hasDerivAt_id' cs).mul_const ((α * Ax * (Ay * h) ^ (1 - α) * ks ^ (α - 1) - δ -
      γx - ρ) / σ - istcGc α γx γy)
    unfold istcFc
    convert h using 1
    rw [hzero]
    ring
  · have h1 := (Real.hasDerivAt_rpow_const (p := α - 1) (Or.inl hks.ne'))
    have h2 := ((((h1.const_mul (α * Ax * (Ay * h) ^ (1 - α))).sub_const δ).sub_const γx).sub_const
      ρ).div_const σ
    have h3 := (h2.sub_const (istcGc α γx γy)).const_mul cs
    unfold istcFc
    convert h3 using 1
    rw [show α - 1 - 1 = α - 2 by ring]
    ring
  · have h := ((hasDerivAt_id' cs).const_mul Ax).const_sub (Ax * (Ay * h) ^ (1 - α) * ks ^ α)
    have h2 := h.sub_const ((δ + istcGK α γx γy n) * ks)
    unfold istcFk
    convert h2 using 1
    ring
  · have h1 := ((Real.hasDerivAt_rpow_const (p := α) (Or.inl hks.ne')).const_mul
      (Ax * (Ay * h) ^ (1 - α))).sub_const (Ax * cs)
    have h2 := h1.sub ((hasDerivAt_id' ks).const_mul (δ + istcGK α γx γy n))
    unfold istcFk
    convert h2 using 1
    have e : Ax * (Ay * h) ^ (1 - α) * (α * ks ^ (α - 1)) = istcD α σ ρ δ γx γy := by
      rw [← hmpk']; ring
    rw [mul_one, e]
    have := istc_D_sub_gK α σ ρ δ γx γy n hα1
    unfold istcBound at this
    linarith

/-- AKMM, (13.A.15), p. 852: **the characteristic equation**. For the Jacobian
`[[0, −P], [−A_x, b]]` of (13.A.14), `det(A − zI) = 0` iff `−z(b − z) = A_x P`. -/
theorem eq_13_A_15 {Ax P b z : ℝ} :
    Matrix.det !![0 - z, -P; -Ax, b - z] = 0 ↔ -z * (b - z) = Ax * P := by
  rw [Matrix.det_fin_two_of]
  constructor <;> intro h <;> linarith

/-- AKMM, p. 852: **the eigenvalues**. If `b > 0` and `Q > 0`, the roots of
`−z(b − z) = Q` are `z_± = (b ± √(b² + 4Q))/2`, and `z_− < 0 < z_+`. -/
theorem istc_eigenvalues {b Q z : ℝ} (hb : 0 < b) (hQ : 0 < Q) :
    (-z * (b - z) = Q ↔ z = (b + √(b ^ 2 + 4 * Q)) / 2 ∨ z = (b - √(b ^ 2 + 4 * Q)) / 2) ∧
      (b - √(b ^ 2 + 4 * Q)) / 2 < 0 ∧ 0 < (b + √(b ^ 2 + 4 * Q)) / 2 := by
  have hs : 0 ≤ b ^ 2 + 4 * Q := by positivity
  have hsq := Real.sq_sqrt hs
  have hgt : b < √(b ^ 2 + 4 * Q) := by
    rw [Real.lt_sqrt hb.le]
    linarith
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, by linarith, by positivity⟩
  · have hfac : (z - (b + √(b ^ 2 + 4 * Q)) / 2) * (z - (b - √(b ^ 2 + 4 * Q)) / 2) = 0 := by
      nlinarith [hsq]
    rcases mul_eq_zero.mp hfac with h1 | h1
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rcases h with h1 | h1 <;> rw [h1] <;> nlinarith [hsq]

/-- AKMM, p. 852: the stable root in the printed form,
`(b − √(b² + 4Q))/2 = ½b(1 − √(1 + 4Q/b²))` for `b > 0`. -/
theorem istc_stable_root {b Q : ℝ} (hb : 0 < b) (hQ : 0 < Q) :
    (b - √(b ^ 2 + 4 * Q)) / 2 = 1 / 2 * b * (1 - √(1 + 4 * Q / b ^ 2)) := by
  have hb2 : 0 < b ^ 2 := by positivity
  have e : √(b ^ 2 + 4 * Q) = b * √(1 + 4 * Q / b ^ 2) := by
    rw [show b ^ 2 + 4 * Q = b ^ 2 * (1 + 4 * Q / b ^ 2) by field_simp,
      Real.sqrt_mul hb2.le, Real.sqrt_sq hb.le]
  rw [e]
  ring

/-- AKMM, App. 13.A.3, p. 852: **saddle-path stability**. Under (13.8) and `g_K + δ > 0`, at the
balanced growth path the constant `Q = (1−α)αA_x²(A_y h)^{1−α}k̃*^{α−2}c̃*/σ` on the right of
(13.A.15) is positive, the second zero `b = ρ − n − γ_xα(1−σ)/(1−α) − γ_y(1−σ)` of its left side
is positive, and so the Jacobian has one strictly negative and one strictly positive real
eigenvalue. -/
theorem istc_saddle {α σ ρ δ Ax Ay h γx γy n : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hσ : 0 < σ)
    (hAx : 0 < Ax) (hAy : 0 < Ay) (hh : 0 < h) (hgK : 0 < istcGK α γx γy n + δ)
    (h138 : istcBound α σ ρ n γx γy < 0) :
    let b := ρ - n - γx * (α * (1 - σ) / (1 - α)) - γy * (1 - σ)
    let Q := (1 - α) * α * Ax ^ 2 * (Ay * h) ^ (1 - α) *
      istcKStar α σ ρ δ Ax Ay h γx γy ^ (α - 2) * istcCStar α σ ρ δ Ax Ay h γx γy n / σ
    0 < b ∧ 0 < Q ∧
      ∃ zm zp, zm < 0 ∧ 0 < zp ∧ ∀ z,
        Matrix.det !![0 - z, -((1 - α) * α * Ax * (Ay * h) ^ (1 - α) *
          istcKStar α σ ρ δ Ax Ay h γx γy ^ (α - 2) * istcCStar α σ ρ δ Ax Ay h γx γy n / σ);
          -Ax, b - z] = 0 ↔ z = zp ∨ z = zm := by
  intro b Q
  have hpos := istc_steady_pos hα0 hα1 hAx hAy hh hgK h138
  have hb : 0 < b := by
    have : b = -istcBound α σ ρ n γx γy := by
      simp only [b, istcBound]; ring
    linarith
  have h1α : 0 < 1 - α := by linarith
  have hQ : 0 < Q := by
    have := hpos.1; have := hpos.2
    simp only [Q]; positivity
  refine ⟨hb, hQ, (b - √(b ^ 2 + 4 * Q)) / 2, (b + √(b ^ 2 + 4 * Q)) / 2,
    (istc_eigenvalues (z := 0) hb hQ).2.1, (istc_eigenvalues (z := 0) hb hQ).2.2, fun z => ?_⟩
  rw [eq_13_A_15, ← (istc_eigenvalues (z := z) hb hQ).1]
  have e : Ax * ((1 - α) * α * Ax * (Ay * h) ^ (1 - α) * istcKStar α σ ρ δ Ax Ay h γx γy ^ (α - 2) *
      istcCStar α σ ρ δ Ax Ay h γx γy n / σ) = Q := by
    simp only [Q]; ring
  rw [e]

/-- AKMM, p. 852: **the half-life**. A deviation decaying as `e^{zt}` with `z < 0` halves at
`τ` iff `τ = ln(1/2)/z`, and `τ > 0`; the speed of convergence is `−z > 0`. -/
theorem istc_half_life {z τ : ℝ} (hz : z < 0) :
    (Real.exp (z * τ) = 1 / 2 ↔ τ = Real.log (1 / 2) / z) ∧ 0 < Real.log (1 / 2) / z := by
  have hlog : Real.log (1 / 2) < 0 := Real.log_neg (by norm_num) (by norm_num)
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, div_pos_of_neg_of_neg hlog hz⟩
  · have := congrArg Real.log h
    rw [Real.log_exp] at this
    rw [eq_div_iff hz.ne, ← this]
    ring
  · rw [h, mul_div_cancel₀ _ hz.ne, Real.exp_log (by norm_num)]

end AKMM.Growth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimality of the balanced growth path

AKMM, §13.3 (pp. 377–379) and Appendix 13.A.1–13.A.2 (pp. 850–851). Mathlib has no Pontryagin
maximum principle; the book's first-order conditions are shown to be *sufficient* using the
Mangasarian–Arrow theorem of AKMM Chapter 9 (`AKMM.ContinuousTime.mangasarian_catching_up`).

The planner's problem (13.A.12) is written in per-capita wealth `a = Ke^{−γ_x t}/(A_x e^{nt})`
(capital per head valued in consumption units, which is the household's wealth under
asset-market clearing): `ȧ = Θe^{(1−α)g_c t}a^α − (δ + γ_x + n)a − c` with
`Θ = A_x^α(A_y h)^{1−α}` (`istc_capital_to_wealth`, from `istc_budget_reduced`), discount rate
`ρ − n`, and `r − n = ∂ȧ/∂a` (`istc_return_reduced`).

* `istc_optimal`: a path with the budget, the Euler equation (13.A.7) and the TVC
  `e^{−(ρ−n)T}c(T)^{−σ}a(T) → 0` ((13.A.11)) is catching-up optimal against every feasible path
  with `a ≥ 0` from the same initial wealth, for any concave `u` with `u'(c) = c^{−σ}` (CRRA for
  `σ ≠ 1`, log for `σ = 1`: `istc_crra_concave`, `istc_log_concave`).
* `istc_bgp_optimal`: under (13.8), the balanced growth path (13.14)–(13.15) from
  `K(0) = k̃*` is optimal; hence it is also the equilibrium (planner = equilibrium, p. 851).
* `istc_closed_form_optimal`: for `σ = α` the closed-form transition (p. 381) is optimal from
  every `K(0) > 0`.
-/

namespace AKMM.Growth

open Real Filter Topology

/-- CRRA utility `(c^{1−σ} − 1)/(1 − σ)` (AKMM (13.4)) is concave on `(0, ∞)` with
`u'(c) = c^{−σ}`, for `0 < σ ≠ 1`. -/
theorem istc_crra_concave {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) :
    ConcaveOn ℝ (Set.Ioi 0) (AKMM.ContinuousTime.crraUtility σ) ∧
      ∀ y, 0 < y → HasDerivAt (AKMM.ContinuousTime.crraUtility σ) (y ^ (-σ)) y := by
  have h1σ : 1 - σ ≠ 0 := sub_ne_zero.mpr (Ne.symm hσ1)
  have hu : AKMM.ContinuousTime.crraUtility σ =
      fun x : ℝ => 1 / (1 - σ) * x ^ (1 - σ) + -(1 / (1 - σ)) := by
    funext x; simp only [AKMM.ContinuousTime.crraUtility]; ring
  have hp := AKMM.ContinuousTime.ramseySaddle_power_props (1 / (1 - σ)) (-(1 / (1 - σ)))
    (1 - σ) (by rw [one_div, inv_mul_cancel₀ h1σ]; exact one_pos) (by linarith)
  refine ⟨?_, fun y hy => (AKMM.ContinuousTime.continuousHamiltonian_crra_derivs hσ1 hy).1⟩
  rw [hu]
  exact hp.2.2.2.2.2.2.2.2.concaveOn

/-- Log utility (the case `σ = 1` of (13.4)) is concave on `(0, ∞)` with `u'(c) = c^{−1}`. -/
theorem istc_log_concave :
    ConcaveOn ℝ (Set.Ioi 0) Real.log ∧ ∀ y : ℝ, 0 < y → HasDerivAt Real.log (y ^ (-(1 : ℝ))) y :=
  ⟨strictConcaveOn_log_Ioi.concaveOn, fun y hy => by
    rw [Real.rpow_neg_one]; exact Real.hasDerivAt_log hy.ne'⟩

/-- The tangent-line inequality for `y^α`, `0 < α < 1`: `y^α ≤ x^α + αx^{α−1}(y − x)` for
`x > 0`, `y ≥ 0`. -/
theorem istc_rpow_tangent {α x y : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hx : 0 < x) (hy : 0 ≤ y) :
    y ^ α ≤ x ^ α + α * x ^ (α - 1) * (y - x) := by
  have hb := rpow_one_add_le_one_add_mul_self (s := y / x - 1) (by
    have : 0 ≤ y / x := div_nonneg hy hx.le
    linarith) hα0.le hα1.le
  rw [show 1 + (y / x - 1) = y / x by ring, Real.div_rpow hy hx.le] at hb
  have hxa : 0 < x ^ α := by positivity
  rw [div_le_iff₀ hxa] at hb
  rw [Real.rpow_sub_one hx.ne']
  have e : (1 + α * (y / x - 1)) * x ^ α = x ^ α + α * (x ^ α / x) * (y - x) := by
    field_simp
  linarith

/-- AKMM, (13.A.8) and p. 851: **the planner's constraint in per-capita wealth**. If capital
satisfies `K̇ = A_x e^{γ_x t}(K^α(A_y e^{γ_y t}e^{nt}h)^{1−α} − e^{nt}c) − δK` and
`K = A_x e^{(γ_x+n)t}a` with `a > 0`, then
`ȧ = A_x^α(A_y h)^{1−α}e^{(1−α)g_c t}a^α − (δ + γ_x + n)a − c`. -/
theorem istc_capital_to_wealth {α Ax Ay h δ γx γy n t c : ℝ} {K a : ℝ → ℝ} (hα1 : α < 1)
    (hAx : 0 < Ax) (hAy : 0 < Ay) (hh : 0 < h) (ha : 0 < a t)
    (hKa : K = fun s => Ax * Real.exp ((γx + n) * s) * a s)
    (hK : HasDerivAt K (Ax * Real.exp (γx * t) * (K t ^ α * (Ay * Real.exp (γy * t) *
      (Real.exp (n * t) * h)) ^ (1 - α) - Real.exp (n * t) * c) - δ * K t) t) :
    HasDerivAt a (Ax ^ α * (Ay * h) ^ (1 - α) * Real.exp ((1 - α) * istcGc α γx γy * t) *
      a t ^ α - (δ + γx + n) * a t - c) t := by
  have hEp := Real.exp_pos ((γx + n) * t)
  have haK : a = fun s => K s * (Real.exp (-(γx + n) * s) / Ax) := by
    funext s
    rw [hKa]
    have : Real.exp ((γx + n) * s) * Real.exp (-(γx + n) * s) = 1 := by
      rw [← Real.exp_add, show (γx + n) * s + -(γx + n) * s = 0 by ring, Real.exp_zero]
    rw [mul_div_assoc', eq_div_iff hAx.ne']
    linear_combination (-(a s * Ax)) * this
  have hd := hK.mul (((hasDerivAt_id' t).const_mul (-(γx + n))).exp.div_const Ax)
  have hKt : K t = Ax * Real.exp ((γx + n) * t) * a t := by rw [hKa]
  have hat : K t * (Real.exp (-(γx + n) * t) / Ax) = a t := by
    rw [haK]
  rw [haK]
  convert hd using 1
  beta_reduce
  rw [hat]
  have hout := istc_output_reduced (Ax := Ax) (Ay := Ay) (h := h) (γx := γx) (γy := γy) (n := n)
    (t := t) hα1 hAx hAy hh ha
  rw [← hKt] at hout
  rw [← hout]
  have hE1 : Real.exp (-(γx + n) * t) = (Real.exp ((γx + n) * t))⁻¹ := by
    rw [neg_mul, Real.exp_neg]
  have h1 : Ax * Ax⁻¹ = 1 := mul_inv_cancel₀ hAx.ne'
  have h2 : Real.exp (γx * t) * Real.exp (-(γx + n) * t) = Real.exp (-n * t) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp (-n * t) * Real.exp (n * t) = 1 := by rw [← Real.exp_add]; simp
  have h4 : K t * Real.exp (-(γx + n) * t) * Ax⁻¹ = a t := by
    rw [hKt, hE1]; field_simp
  set Y := K t ^ α * (Ay * Real.exp (γy * t) * (Real.exp (n * t) * h)) ^ (1 - α)
  set E := Real.exp (-(γx + n) * t)
  linear_combination (-(Real.exp (γx * t) * E * Y)) * h1 + (-Y) * h2 +
    (Real.exp (γx * t) * E * Real.exp (n * t) * c) * h1 + (c * Real.exp (n * t)) * h2 + c * h3 +
    (δ + γx + n) * h4

/-- AKMM, (13.A.4)–(13.A.12), pp. 850–851: **sufficiency of the first-order conditions**. Let
`u` be concave on `(0, ∞)` with `u'(c) = c^{−σ}`, `Θ > 0`, and write
`G(t, a) = Θe^{(1−α)g_c t}a^α − (δ + γ_x + n)a` and `r(t) − n = ∂G/∂a(t, a(t))`
(`istc_return_reduced`). If `(a, c)` has `a, c > 0`, `c` continuous, the budget `ȧ = G − c`,
the Euler equation `ċ = c(r − ρ)/σ` (13.A.7) and the TVC
`e^{−(ρ−n)T}c(T)^{−σ}a(T) → 0` (13.A.11), then it is catching-up optimal for
`∫e^{−(ρ−n)t}u(c)` against every path `(a', c')` from `a(0)` with `a' ≥ 0`, `c' > 0`
continuous and `ȧ' = G − c'`. -/
theorem istc_optimal {α σ ρ δ γx γy n Θ : ℝ} {u : ℝ → ℝ} {a c a' c' : ℝ → ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hσ : 0 < σ) (hΘ : 0 < Θ)
    (hconc : ConcaveOn ℝ (Set.Ioi 0) u) (hu : ∀ y, 0 < y → HasDerivAt u (y ^ (-σ)) y)
    (ha : ∀ t, 0 ≤ t → 0 < a t) (hc : ∀ t, 0 ≤ t → 0 < c t) (hcc : ContinuousOn c (Set.Ici 0))
    (hbud : ∀ t, 0 ≤ t → HasDerivAt a (Θ * Real.exp ((1 - α) * istcGc α γx γy * t) * a t ^ α -
      (δ + γx + n) * a t - c t) t)
    (heuler : ∀ t, 0 ≤ t → HasDerivAt c (c t * ((α * (Θ * Real.exp ((1 - α) * istcGc α γx γy *
      t)) * a t ^ (α - 1) - (δ + γx + n) + n) - ρ) / σ) t)
    (htvc : Tendsto (fun T => Real.exp (-(ρ - n) * T) * c T ^ (-σ) * a T) atTop (𝓝 0))
    (ha' : ∀ t, 0 ≤ t → 0 ≤ a' t) (hc' : ∀ t, 0 ≤ t → 0 < c' t)
    (hcc' : ContinuousOn c' (Set.Ici 0))
    (hbud' : ∀ t, 0 ≤ t → HasDerivAt a' (Θ * Real.exp ((1 - α) * istcGc α γx γy * t) *
      a' t ^ α - (δ + γx + n) * a' t - c' t) t) (h0 : a' 0 = a 0) :
    ∀ ε > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-(ρ - n) * t) * u (c' t) ≤
      (∫ t in (0 : ℝ)..T, Real.exp (-(ρ - n) * t) * u (c t)) + ε := by
  set E := fun t : ℝ => Θ * Real.exp ((1 - α) * istcGc α γx γy * t)
  have hE : ∀ t, 0 < E t := fun t => by positivity
  set μ := fun t => Real.exp (-(ρ - n) * t) * c t ^ (-σ)
  have hμ0 : ∀ t, 0 ≤ t → 0 ≤ μ t := fun t ht => by
    have := hc t ht; positivity
  have hμ : ∀ t, 0 ≤ t → HasDerivAt μ (-(μ t * (α * E t * a t ^ (α - 1) - (δ + γx + n)))) t :=
    fun t ht => by
      have h := istc_costate_of_euler (n := n) hσ (hc t ht) (heuler t ht)
      convert h using 1
      ring
  have hG : ∀ t, 0 ≤ t → E t * a' t ^ α - (δ + γx + n) * a' t ≤
      E t * a t ^ α - (δ + γx + n) * a t + (α * E t * a t ^ (α - 1) - (δ + γx + n)) *
        (a' t - a t) := fun t ht => by
    have htan := istc_rpow_tangent hα0 hα1 (ha t ht) (ha' t ht)
    have := mul_le_mul_of_nonneg_left htan (hE t).le
    nlinarith
  refine (AKMM.ContinuousTime.mangasarian_catching_up (ρ := ρ - n) (u' := fun y => y ^ (-σ))
    (G := fun t y => E t * y ^ α - (δ + γx + n) * y)
    (Gx := fun t y => α * E t * y ^ (α - 1) - (δ + γx + n)) (μ := μ)
    hconc hu hc hcc hbud hμ (fun t _ => rfl) hμ0 hc' hcc' hbud' h0 hG ?_).1
  intro ε hε
  filter_upwards [htvc.eventually (gt_mem_nhds hε), eventually_ge_atTop (0 : ℝ)] with T h1 hT
  have := mul_nonneg (hμ0 T hT) (ha' T hT)
  have e : μ T * (a T - a' T) = Real.exp (-(ρ - n) * T) * c T ^ (-σ) * a T - μ T * a' T := by
    simp only [μ]; ring
  rw [e]
  linarith

/-- AKMM, (13.14)–(13.15) and p. 379: **the balanced growth path is optimal**. Under (13.8)
and `g_K + δ > 0`, the path `a(t) = (k̃*/A_x)e^{g_c t}`, `c(t) = c̃*e^{g_c t}` (that is,
`K = k̃*e^{g_K t}`) satisfies the budget, the Euler equation and the TVC, so by `istc_optimal`
it is catching-up optimal for the planner's problem (13.A.12) from `K(0) = k̃*`. -/
theorem istc_bgp_optimal {α σ ρ δ Ax Ay h γx γy n : ℝ} {u : ℝ → ℝ} {a' c' : ℝ → ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hσ : 0 < σ) (hAx : 0 < Ax) (hAy : 0 < Ay) (hh : 0 < h)
    (hgK : 0 < istcGK α γx γy n + δ) (h138 : istcBound α σ ρ n γx γy < 0)
    (hconc : ConcaveOn ℝ (Set.Ioi 0) u) (hu : ∀ y, 0 < y → HasDerivAt u (y ^ (-σ)) y)
    (ha' : ∀ t, 0 ≤ t → 0 ≤ a' t) (hc' : ∀ t, 0 ≤ t → 0 < c' t)
    (hcc' : ContinuousOn c' (Set.Ici 0))
    (hbud' : ∀ t, 0 ≤ t → HasDerivAt a' (Ax ^ α * (Ay * h) ^ (1 - α) *
      Real.exp ((1 - α) * istcGc α γx γy * t) * a' t ^ α - (δ + γx + n) * a' t - c' t) t)
    (h0 : a' 0 = istcKStar α σ ρ δ Ax Ay h γx γy / Ax) :
    ∀ ε > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-(ρ - n) * t) * u (c' t) ≤
      (∫ t in (0 : ℝ)..T, Real.exp (-(ρ - n) * t) *
        u (istcCStar α σ ρ δ Ax Ay h γx γy n * Real.exp (istcGc α γx γy * t))) + ε := by
  obtain ⟨hks, hcs⟩ := istc_steady_pos hα0 hα1 hAx hAy hh hgK h138
  have hD : 0 < istcD α σ ρ δ γx γy := hgK.trans (istc_D_pos (δ := δ) hα1 h138)
  set ks := istcKStar α σ ρ δ Ax Ay h γx γy
  set cs := istcCStar α σ ρ δ Ax Ay h γx γy n
  set g := istcGc α γx γy
  set Θ := Ax ^ α * (Ay * h) ^ (1 - α)
  have hΘ : 0 < Θ := by positivity
  have hAh : 0 < Ay * h := by positivity
  set ab := ks / Ax
  have hab : 0 < ab := by positivity
  -- the two stationary equations in wealth units
  have hmpk := istc_mpk_star hα0 hα1 hAx hAy hh hD
  have hΘa : Θ * ab ^ (α - 1) = Ax * (Ay * h / ks) ^ (1 - α) := by
    simp only [Θ, ab]
    rw [Real.div_rpow hks.le hAx.le, Real.div_rpow hAh.le hks.le, Real.rpow_sub_one hks.ne',
      Real.rpow_sub_one hAx.ne', show (1 - α) = -(α - 1) by ring, Real.rpow_neg hks.le,
      Real.rpow_neg hAh.le, Real.rpow_sub_one hks.ne', Real.rpow_sub_one hAh.ne']
    have : 0 < Ax ^ α := by positivity
    have : 0 < ks ^ α := by positivity
    have : 0 < (Ay * h) ^ α := by positivity
    field_simp
  have hcs_eq : cs = Θ * ab ^ α - (δ + istcGK α γx γy n) * ab := by
    have e : Θ * ab ^ α = ab * (Θ * ab ^ (α - 1)) := by
      rw [Real.rpow_sub_one hab.ne']; field_simp
    rw [e, hΘa]
    simp only [cs, istcCStar, ab]
    rw [istc_cd_eq hks hAh]
    field_simp
    ring
  have heul : (α * (Θ * ab ^ (α - 1)) - (δ + γx + n) + n - ρ) / σ = g := by
    rw [hΘa, hmpk, istc_D_eq]
    field_simp
    ring
  have hgK : istcGK α γx γy n = g + γx + n := istc_gK_eq _ _ _ _ hα1
  set a := fun t => ab * Real.exp (g * t)
  set c := fun t => cs * Real.exp (g * t)
  have hEg : ∀ t, Θ * Real.exp ((1 - α) * g * t) * a t ^ α =
      Real.exp (g * t) * (Θ * ab ^ α) := fun t => by
    simp only [a]
    rw [Real.mul_rpow hab.le (Real.exp_pos _).le, ← Real.exp_mul]
    have : Real.exp ((1 - α) * g * t) * Real.exp (g * t * α) = Real.exp (g * t) := by
      rw [← Real.exp_add]; ring_nf
    rw [← this]; ring
  have hEg1 : ∀ t, Θ * Real.exp ((1 - α) * g * t) * a t ^ (α - 1) = Θ * ab ^ (α - 1) :=
    fun t => by
      simp only [a]
      rw [Real.mul_rpow hab.le (Real.exp_pos _).le, ← Real.exp_mul]
      have : Real.exp ((1 - α) * g * t) * Real.exp (g * t * (α - 1)) = 1 := by
        rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
      rw [show Θ * Real.exp ((1 - α) * g * t) * (ab ^ (α - 1) * Real.exp (g * t * (α - 1))) =
        Θ * ab ^ (α - 1) * (Real.exp ((1 - α) * g * t) * Real.exp (g * t * (α - 1))) by ring,
        this, mul_one]
  have hcont : ContinuousOn c (Set.Ici 0) := by
    simp only [c]; fun_prop
  refine istc_optimal (a := a) (c := c) hα0 hα1 hσ hΘ hconc hu (fun t _ => by positivity)
    (fun t _ => by positivity) hcont (fun t _ => ?_) (fun t _ => ?_) ?_ ha' hc' hcc' hbud' ?_
  · have hd := ((hasDerivAt_id' t).const_mul g).exp.const_mul ab
    convert hd using 1
    rw [hEg]
    simp only [a, c]
    rw [hcs_eq, hgK]
    ring
  · have hd := ((hasDerivAt_id' t).const_mul g).exp.const_mul cs
    convert hd using 1
    rw [mul_assoc α, hEg1, mul_div_assoc, heul]
    simp only [c]
    ring
  · have e : ∀ T, Real.exp (-(ρ - n) * T) * c T ^ (-σ) * a T =
        cs ^ (-σ) * ab * Real.exp (istcBound α σ ρ n γx γy * T) := fun T => by
      simp only [a, c]
      rw [Real.mul_rpow hcs.le (Real.exp_pos _).le, ← Real.exp_mul, istc_bound_eq]
      have : Real.exp (-(ρ - n) * T) * Real.exp (g * T * -σ) * Real.exp (g * T) =
          Real.exp ((n - ρ + (1 - σ) * g) * T) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      rw [← this]; ring
    simp only [e]
    exact (istc_exp_tendsto_zero_iff (by positivity)).mpr h138
  · rw [h0]
    simp [a]

/-- AKMM, p. 381: **the closed-form transition is optimal** (`σ = α`). Under (13.8) and
`φ > 0`, from any `K(0) = k̃_0 > 0` the path `k̃(t)` of `istc_closed_form_path` with
`c̃ = φk̃` — in wealth units `a(t) = k̃(t)e^{g_c t}/A_x`, `c(t) = φk̃(t)e^{g_c t}` — satisfies the
budget, the Euler equation and the TVC, so it is catching-up optimal for the planner's problem
(13.A.12) against every feasible path with `a ≥ 0`. -/
theorem istc_closed_form_optimal {α ρ δ Ax Ay h γx γy n k0 : ℝ} {u : ℝ → ℝ} {a' c' : ℝ → ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hAx : 0 < Ax) (hAy : 0 < Ay) (hh : 0 < h) (hk0 : 0 < k0)
    (hD : 0 < istcD α α ρ δ γx γy) (hφ : 0 < istcPhi α ρ δ Ax γx n)
    (h138 : istcBound α α ρ n γx γy < 0)
    (hconc : ConcaveOn ℝ (Set.Ioi 0) u) (hu : ∀ y, 0 < y → HasDerivAt u (y ^ (-α)) y)
    (ha' : ∀ t, 0 ≤ t → 0 ≤ a' t) (hc' : ∀ t, 0 ≤ t → 0 < c' t)
    (hcc' : ContinuousOn c' (Set.Ici 0))
    (hbud' : ∀ t, 0 ≤ t → HasDerivAt a' (Ax ^ α * (Ay * h) ^ (1 - α) *
      Real.exp ((1 - α) * istcGc α γx γy * t) * a' t ^ α - (δ + γx + n) * a' t - c' t) t)
    (h0 : a' 0 = k0 / Ax) :
    let zs := istcKStar α α ρ δ Ax Ay h γx γy ^ (1 - α)
    let lam := (1 - α) * (istcD α α ρ δ γx γy / α)
    let k := fun s => (zs + (k0 ^ (1 - α) - zs) * Real.exp (-lam * s)) ^ (1 / (1 - α))
    ∀ ε > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-(ρ - n) * t) * u (c' t) ≤
      (∫ t in (0 : ℝ)..T, Real.exp (-(ρ - n) * t) *
        u (istcPhi α ρ δ Ax γx n * k t * Real.exp (istcGc α γx γy * t))) + ε := by
  intro zs lam k
  have h1α : 0 < 1 - α := by linarith
  set φ := istcPhi α ρ δ Ax γx n
  set g := istcGc α γx γy
  set Θ := Ax ^ α * (Ay * h) ^ (1 - α)
  have hΘ : 0 < Θ := by positivity
  have hAh : 0 < Ay * h := by positivity
  have hpath := fun t (ht : 0 ≤ t) => istc_closed_form_path (n := n) (k0 := k0) (t := t)
    hα0 hα1 hAx hAy hh hk0 hD ht
  have hkpos : ∀ t, 0 ≤ t → 0 < k t := fun t ht => (hpath t ht).2.1
  have hkd : ∀ t, 0 ≤ t → HasDerivAt k (k t * (Ax * ((Ay * h / k t) ^ (1 - α) -
      φ * k t / k t) - δ - istcGK α γx γy n)) t := fun t ht => (hpath t ht).2.2
  set a := fun t => k t * Real.exp (g * t) / Ax
  set c := fun t => φ * k t * Real.exp (g * t)
  have hgK : istcGK α γx γy n = g + γx + n := istc_gK_eq _ _ _ _ hα1
  -- the two output identities in wealth units
  have hout : ∀ t, 0 ≤ t → Θ * Real.exp ((1 - α) * g * t) * a t ^ α =
      Real.exp (g * t) * (k t * (Ay * h / k t) ^ (1 - α)) := fun t ht => by
    have hk := hkpos t ht
    simp only [a]
    rw [Real.div_rpow (by positivity) hAx.le, Real.mul_rpow hk.le (Real.exp_pos _).le,
      ← Real.exp_mul, ← istc_cd_eq hk hAh]
    have : Real.exp ((1 - α) * g * t) * Real.exp (g * t * α) = Real.exp (g * t) := by
      rw [← Real.exp_add]; ring_nf
    have hAxa : 0 < Ax ^ α := by positivity
    simp only [Θ]
    field_simp
    rw [← this]
    ring
  have hmpk : ∀ t, 0 ≤ t → Θ * Real.exp ((1 - α) * g * t) * a t ^ (α - 1) =
      Ax * (Ay * h / k t) ^ (1 - α) := fun t ht => by
    have hk := hkpos t ht
    have ha : 0 < a t := by simp only [a]; positivity
    have e := hout t ht
    rw [Real.rpow_sub_one ha.ne', ← mul_div_assoc, e]
    simp only [a]
    field_simp
  have hcd : ∀ t, 0 ≤ t → HasDerivAt c (c t * ((α * (Θ * Real.exp ((1 - α) * g * t)) *
      a t ^ (α - 1) - (δ + γx + n) + n) - ρ) / α) t := fun t ht => by
    have hk := hkpos t ht
    have h1 := ((hkd t ht).const_mul φ).fun_mul ((hasDerivAt_id' t).const_mul g).exp
    have hrhs := istc_closed_form_rhs (Ay := Ay) (h := h) (γy := γy) (ρ := ρ) (δ := δ)
      (γx := γx) (n := n) hα0 hα1 hAx hk
    simp only [c]
    convert h1 using 1
    rw [mul_assoc α, hmpk t ht]
    rw [hrhs]
    field_simp
    ring
  have hbud : ∀ t, 0 ≤ t → HasDerivAt a (Θ * Real.exp ((1 - α) * g * t) * a t ^ α -
      (δ + γx + n) * a t - c t) t := fun t ht => by
    have hk := hkpos t ht
    have h1 := ((hkd t ht).fun_mul ((hasDerivAt_id' t).const_mul g).exp).div_const Ax
    convert h1 using 1
    rw [hout t ht, hgK]
    simp only [a, c]
    field_simp
    ring
  have hcont : ContinuousOn c (Set.Ici 0) := fun t ht =>
    (hcd t ht).continuousAt.continuousWithinAt
  have hzs : 0 < zs := by
    have : 0 < istcKStar α α ρ δ Ax Ay h γx γy := by unfold istcKStar; positivity
    positivity
  have hpow : ∀ t, 0 ≤ t → k t ^ (1 - α) = zs + (k0 ^ (1 - α) - zs) * Real.exp (-lam * t) :=
    fun t ht => by
      have hu' : 0 < zs + (k0 ^ (1 - α) - zs) * Real.exp (-lam * t) := by
        have hlam : 0 < lam := by positivity
        have hE : Real.exp (-lam * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
        have hE0 := Real.exp_pos (-lam * t)
        have hk0p : 0 < k0 ^ (1 - α) := by positivity
        nlinarith
      simp only [k]
      rw [← Real.rpow_mul hu'.le, one_div_mul_cancel h1α.ne', Real.rpow_one]
  have htvc : Tendsto (fun T => Real.exp (-(ρ - n) * T) * c T ^ (-α) * a T) atTop (𝓝 0) := by
    have hlam : 0 < lam := by positivity
    have hU : Tendsto (fun T => zs + (k0 ^ (1 - α) - zs) * Real.exp (-lam * T)) atTop
        (𝓝 zs) := by
      have hE := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hlam)
      have := (hE.const_mul (k0 ^ (1 - α) - zs)).const_add zs
      simp only [mul_zero, add_zero] at this
      refine this.congr fun T => ?_
      simp [neg_mul]
    have hX := (istc_exp_tendsto_zero_iff (C := 1) one_pos).mpr h138
    have hprod := (hU.mul hX).const_mul (φ ^ (-α) / Ax)
    rw [mul_zero, mul_zero] at hprod
    refine hprod.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    have hk := hkpos T hT
    simp only [a, c]
    rw [← hpow T hT, Real.mul_rpow (by positivity) (Real.exp_pos _).le,
      Real.mul_rpow hφ.le hk.le, ← Real.exp_mul, Real.rpow_sub hk, Real.rpow_one, istc_bound_eq]
    have : Real.exp (-(ρ - n) * T) * Real.exp (g * T * -α) * Real.exp (g * T) =
        Real.exp ((n - ρ + (1 - α) * g) * T) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    rw [← this]
    have : 0 < k T ^ α := by positivity
    field_simp
    rw [Real.rpow_neg hk.le]
    field_simp
  have h := istc_optimal (a := a) (c := c) hα0 hα1 hα0 hΘ hconc hu (fun t ht => by
    have := hkpos t ht; simp only [a]; positivity) (fun t ht => by
    have := hkpos t ht; simp only [c]; positivity) hcont hbud hcd htvc ha' hc' hcc' hbud'
    (by
      have hk00 : k 0 = k0 := (hpath 0 le_rfl).1
      rw [h0]; simp only [a]; rw [hk00]; simp)
  exact h

end AKMM.Growth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The AK model

AKMM, §13.5 (pp. 384–386) and footnotes 24–25. The planner maximises (13.18)
`∫e^{−(ρ−n)t}u(c)` subject to `K̇ = AK − e^{nt}c − δK`; with `g = (A − δ − ρ)/σ`:

* the planner's first-order conditions give the Euler equation (13.19) (`eq_13_19`) and the
  transversality term (13.20) (`eq_13_20`);
* the closed-form policy `c = (A − δ − n − g)e^{−nt}K` with `K̇/K = n + g` satisfies the
  resource constraint and the Euler equation (`ak_policy`);
* `σ(A − δ − n) > A − δ − ρ` iff `A − δ − n − g > 0` iff the TVC holds on this path
  (`ak_bounded_iff`, `ak_tvc`); the policy is then catching-up optimal (`ak_optimal`) and is the
  competitive equilibrium with `r = A − δ`, `w = 0` (`ak_decentralized`);
* footnote 24: every solution of the capital equation with Euler consumption is
  `Ξe^{(A−δ)t} + c(0)e^{(n+g)t}/(A − δ − n − g)` (`ak_footnote_24_general`), and the TVC forces
  `Ξ = 0` (`ak_footnote_24_unique`); the printed `K̇/K = A − δ − e^{(n+g)t}c(0)` lacks `/K(t)`
  (`ak_footnote_24_printed_false`);
* footnote 25: with a capital-income tax `τ` rebated lump-sum, the resource constraint is
  unchanged and growth `((1 − τ)(A − δ) − ρ)/σ` is strictly decreasing in `τ`
  (`ak_footnote_25`).

The AK model of InternationalEconomics' `GlobalGrowth` is in discrete time (Obstfeld–Rogoff),
so it is not reused.
-/

namespace AKMM.Growth

open Real Filter Topology

/-- AKMM, p. 385: the AK growth rate of consumption, `g = (A − δ − ρ)/σ`. -/
noncomputable def akG (A δ ρ σ : ℝ) : ℝ := (A - δ - ρ) / σ

/-- AKMM, (13.19), p. 385: **the planner's Euler equation**. With the Hamiltonian
`e^{−(ρ−n)t}u(c) + μ(AK − e^{nt}c − δK)`, the conditions `e^{−(ρ−n)t}c^{−σ} = μe^{nt}` and
`μ̇ = −μ(A − δ)` give `ċ/c = (A − δ − ρ)/σ`. -/
theorem eq_13_19 {A δ ρ σ n t cdot : ℝ} {c μ : ℝ → ℝ} (hσ : 0 < σ) (hc : 0 < c t)
    (hcd : HasDerivAt c cdot t)
    (hfoc : ∀ s, Real.exp (-(ρ - n) * s) * c s ^ (-σ) = μ s * Real.exp (n * s))
    (hcost : HasDerivAt μ (-(μ t * (A - δ))) t) :
    cdot / c t = akG A δ ρ σ := by
  have h := istc_planner_euler (Ax := 1) (γx := 0) (MPK := A) (δ := δ) (c := c) (μ := μ) hσ
    one_pos hc hcd (fun s => by rw [hfoc s]; simp) (by simpa using hcost)
  rw [h]
  unfold akG
  simp

/-- AKMM, (13.20), p. 385: along `c(t) = c(0)e^{gt}`, the transversality term
`c(T)^{−σ}e^{−ρT}K(T)` equals `c(0)^{−σ}e^{−(A−δ)T}K(T)`. -/
theorem eq_13_20 {A δ ρ σ c0 T KT : ℝ} (hσ : 0 < σ) (hc0 : 0 < c0) :
    (c0 * Real.exp (akG A δ ρ σ * T)) ^ (-σ) * Real.exp (-ρ * T) * KT =
      c0 ^ (-σ) * Real.exp (-(A - δ) * T) * KT := by
  rw [Real.mul_rpow hc0.le (Real.exp_pos _).le, ← Real.exp_mul]
  have : Real.exp (akG A δ ρ σ * T * -σ) * Real.exp (-ρ * T) = Real.exp (-(A - δ) * T) := by
    rw [← Real.exp_add]; unfold akG; congr 1; field_simp; ring
  rw [← this]
  ring

/-- AKMM, p. 385: per-capita capital `k = Ke^{−nt}` obeys `k̇ = (A − δ − n)k − c` when
`K̇ = AK − e^{nt}c − δK`. -/
theorem ak_capital_to_percapita {A δ n t c : ℝ} {K : ℝ → ℝ}
    (hK : HasDerivAt K (A * K t - Real.exp (n * t) * c - δ * K t) t) :
    HasDerivAt (fun s => K s * Real.exp (-n * s))
      ((A - δ - n) * (K t * Real.exp (-n * t)) - c) t := by
  have hd := hK.fun_mul ((hasDerivAt_id' t).const_mul (-n)).exp
  convert hd using 1
  have : Real.exp (n * t) * Real.exp (-n * t) = 1 := by rw [← Real.exp_add]; simp
  linear_combination c * this

/-- AKMM, p. 385: **the closed-form policy**. With `g = (A − δ − ρ)/σ`, the path
`K(t) = K_0e^{(n+g)t}`, `c(t) = (A − δ − n − g)e^{−nt}K(t)` satisfies the resource constraint
`K̇ = AK − e^{nt}c − δK` with equality, `K̇/K = n + g`, and the Euler equation
`ċ = gc`. -/
theorem ak_policy {A δ ρ σ n K0 t : ℝ} :
    let g := akG A δ ρ σ
    let K := fun s => K0 * Real.exp ((n + g) * s)
    let c := fun s => (A - δ - n - g) * Real.exp (-n * s) * K s
    HasDerivAt K (A * K t - Real.exp (n * t) * c t - δ * K t) t ∧
      HasDerivAt K ((n + g) * K t) t ∧ HasDerivAt c (g * c t) t := by
  intro g K c
  have hK : HasDerivAt K ((n + g) * K t) t := by
    have := ((hasDerivAt_id' t).const_mul (n + g)).exp.const_mul K0
    convert this using 1
    simp only [K]; ring
  have hE : Real.exp (n * t) * Real.exp (-n * t) = 1 := by rw [← Real.exp_add]; simp
  refine ⟨?_, hK, ?_⟩
  · convert hK using 1
    simp only [c]
    linear_combination (-(A - δ - n - g) * K t) * hE
  · have hc : c = fun s => (A - δ - n - g) * K0 * Real.exp (g * s) := by
      funext s
      simp only [c, K]
      have : Real.exp (-n * s) * Real.exp ((n + g) * s) = Real.exp (g * s) := by
        rw [← Real.exp_add]; ring_nf
      rw [← this]
      ring
    rw [hc]
    have := ((hasDerivAt_id' t).const_mul g).exp.const_mul ((A - δ - n - g) * K0)
    convert this using 1
    ring

/-- AKMM, p. 385: **the boundedness condition**. For `σ > 0`, `σ(A − δ − n) > A − δ − ρ` iff
consumption on the closed-form path is positive, `A − δ − n − g > 0`, iff the discounted growth
of marginal utility times capital, `ρ − n − (1 − σ)g`, is positive. -/
theorem ak_bounded_iff {A δ ρ σ n : ℝ} (hσ : 0 < σ) :
    (A - δ - ρ < σ * (A - δ - n) ↔ 0 < A - δ - n - akG A δ ρ σ) ∧
      ρ - n - (1 - σ) * akG A δ ρ σ = A - δ - n - akG A δ ρ σ := by
  unfold akG
  constructor
  · rw [sub_pos, div_lt_iff₀ hσ]
    constructor <;> intro h <;> linarith
  · field_simp
    ring

/-- AKMM, (13.20), p. 385: on the closed-form path the transversality term
`c(T)^{−σ}e^{−ρT}K(T)` tends to zero iff `σ(A − δ − n) > A − δ − ρ` (given `K_0 > 0`
and positive consumption). -/
theorem ak_tvc {A δ ρ σ n K0 : ℝ} (hσ : 0 < σ) (hK0 : 0 < K0)
    (hpos : 0 < A - δ - n - akG A δ ρ σ) :
    Tendsto (fun T => (((A - δ - n - akG A δ ρ σ) * K0) * Real.exp (akG A δ ρ σ * T)) ^ (-σ) *
      Real.exp (-ρ * T) * (K0 * Real.exp ((n + akG A δ ρ σ) * T))) atTop (𝓝 0) := by
  have hc0 : 0 < (A - δ - n - akG A δ ρ σ) * K0 := mul_pos hpos hK0
  have e : ∀ T, (((A - δ - n - akG A δ ρ σ) * K0) * Real.exp (akG A δ ρ σ * T)) ^ (-σ) *
      Real.exp (-ρ * T) * (K0 * Real.exp ((n + akG A δ ρ σ) * T)) =
      (((A - δ - n - akG A δ ρ σ) * K0) ^ (-σ) * K0) *
        Real.exp (-(A - δ - n - akG A δ ρ σ) * T) := fun T => by
    rw [eq_13_20 hσ hc0]
    have : Real.exp (-(A - δ) * T) * Real.exp ((n + akG A δ ρ σ) * T) =
        Real.exp (-(A - δ - n - akG A δ ρ σ) * T) := by rw [← Real.exp_add]; ring_nf
    rw [← this]; ring
  simp only [e]
  exact (istc_exp_tendsto_zero_iff (by positivity)).mpr (by linarith)

/-- AKMM, p. 385: **the AK planner's optimum**. If `σ(A − δ − n) > A − δ − ρ` and `u` is
concave with `u'(c) = c^{−σ}`, the closed-form per-capita path `k(t) = k_0e^{gt}`,
`c(t) = (A − δ − n − g)k(t)` is catching-up optimal for `∫e^{−(ρ−n)t}u(c)` against every path
from `k_0` with `k̇ = (A − δ − n)k − c`, `k ≥ 0` and positive continuous consumption. -/
theorem ak_optimal {A δ ρ σ n k0 : ℝ} {u : ℝ → ℝ} {k' c' : ℝ → ℝ} (hσ : 0 < σ) (hk0 : 0 < k0)
    (hbound : A - δ - ρ < σ * (A - δ - n))
    (hconc : ConcaveOn ℝ (Set.Ioi 0) u) (hu : ∀ y, 0 < y → HasDerivAt u (y ^ (-σ)) y)
    (hk' : ∀ t, 0 ≤ t → 0 ≤ k' t) (hc' : ∀ t, 0 ≤ t → 0 < c' t)
    (hcc' : ContinuousOn c' (Set.Ici 0))
    (hkd' : ∀ t, 0 ≤ t → HasDerivAt k' ((A - δ - n) * k' t - c' t) t) (h0 : k' 0 = k0) :
    ∀ ε > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-(ρ - n) * t) * u (c' t) ≤
      (∫ t in (0 : ℝ)..T, Real.exp (-(ρ - n) * t) *
        u ((A - δ - n - akG A δ ρ σ) * (k0 * Real.exp (akG A δ ρ σ * t)))) + ε := by
  set g := akG A δ ρ σ
  have hpos : 0 < A - δ - n - g := (ak_bounded_iff hσ).1.mp hbound
  set m := A - δ - n - g
  set k := fun t => k0 * Real.exp (g * t)
  set c := fun t => m * k t
  set μ := fun t => Real.exp (-(ρ - n) * t) * c t ^ (-σ)
  have hcpos : ∀ t, 0 < c t := fun t => by simp only [c, k]; positivity
  have hkd : ∀ t, HasDerivAt k (g * k t) t := fun t => by
    have := ((hasDerivAt_id' t).const_mul g).exp.const_mul k0
    convert this using 1; simp only [k]; ring
  have hcd : ∀ t, HasDerivAt c (c t * ((A - δ) - ρ) / σ) t := fun t => by
    have := (hkd t).const_mul m
    convert this using 1
    simp only [c, g, akG]
    field_simp
  have hμ : ∀ t, 0 ≤ t → HasDerivAt μ (-(μ t * (A - δ - n))) t := fun t _ => by
    have h := istc_costate_of_euler (n := n) hσ (hcpos t) (hcd t)
    convert h using 1
    ring
  have hμ0 : ∀ t, 0 ≤ t → 0 ≤ μ t := fun t _ => by
    have := hcpos t; simp only [μ]; positivity
  have hcc : ContinuousOn c (Set.Ici 0) := by simp only [c, k]; fun_prop
  refine (AKMM.ContinuousTime.mangasarian_catching_up (ρ := ρ - n) (u' := fun y => y ^ (-σ))
    (G := fun _ y => (A - δ - n) * y) (Gx := fun _ _ => A - δ - n) (x := k) (c := c) (μ := μ)
    hconc hu (fun t _ => hcpos t) hcc (fun t _ => ?_) hμ (fun t _ => rfl) hμ0 hc' hcc' hkd'
    (by rw [h0]; simp [k]) (fun t _ => by nlinarith) ?_).1
  · convert hkd t using 1
    simp only [c, m]
    ring
  · intro ε hε
    have htvc : Tendsto (fun T => μ T * k T) atTop (𝓝 0) := by
      have e : ∀ T, μ T * k T = (m ^ (-σ) * k0 ^ (1 - σ)) * Real.exp (-(A - δ - n - g) * T) :=
        fun T => by
          simp only [μ, c, k]
          rw [Real.mul_rpow hpos.le (by positivity), Real.mul_rpow hk0.le (Real.exp_pos _).le,
            ← Real.exp_mul, Real.rpow_sub hk0, Real.rpow_one]
          have h2 : Real.exp (-(ρ - n) * T) * Real.exp (g * T * -σ) * Real.exp (g * T) =
              Real.exp (-(A - δ - n - g) * T) := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 1
            simp only [g, akG]
            field_simp
            ring
          rw [← h2]
          have : 0 < k0 ^ σ := by positivity
          field_simp
          rw [← Real.rpow_add hk0, neg_add_cancel, Real.rpow_zero]
      simp only [e]
      exact (istc_exp_tendsto_zero_iff (by positivity)).mpr (by linarith)
    filter_upwards [htvc.eventually (gt_mem_nhds hε), eventually_ge_atTop (0 : ℝ)] with T h1 hT
    nlinarith [mul_nonneg (hμ0 T hT) (hk' T hT)]

/-- AKMM, p. 385: **decentralisation**. With competitive firms `r = A − δ` and `w = 0`, a
household with wealth `a` (per capita) and budget `ȧ = (r − n)a − c` facing the nPg
`liminf e^{−(r−n)T}a'(T) ≥ 0` finds the closed-form path optimal: it satisfies (9.24)–(9.25)
of AKMM Chapter 9 and the TVC, so `mangasarian_consumption_saving` applies. -/
theorem ak_decentralized {A δ ρ σ n k0 : ℝ} {u : ℝ → ℝ} {a' c' : ℝ → ℝ} (hσ : 0 < σ)
    (hk0 : 0 < k0) (hbound : A - δ - ρ < σ * (A - δ - n))
    (hconc : ConcaveOn ℝ (Set.Ioi 0) u) (hu : ∀ y, 0 < y → HasDerivAt u (y ^ (-σ)) y)
    (hc' : ∀ t, 0 ≤ t → 0 < c' t) (hcc' : ContinuousOn c' (Set.Ici 0))
    (ha' : ∀ t, 0 ≤ t → HasDerivAt a' (0 + (A - δ - n) * a' t - c' t) t) (h0 : a' 0 = k0)
    (hnpg : ∀ η > 0, ∀ᶠ T in atTop, -η ≤ Real.exp (-(A - δ - n) * T) * a' T) :
    ∀ ε > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-(ρ - n) * t) * u (c' t) ≤
      (∫ t in (0 : ℝ)..T, Real.exp (-(ρ - n) * t) *
        u ((A - δ - n - akG A δ ρ σ) * (k0 * Real.exp (akG A δ ρ σ * t)))) + ε := by
  set g := akG A δ ρ σ
  have hpos : 0 < A - δ - n - g := (ak_bounded_iff hσ).1.mp hbound
  set m := A - δ - n - g
  set k := fun t => k0 * Real.exp (g * t)
  set c := fun t => m * k t
  have hcpos : ∀ t, 0 < c t := fun t => by simp only [c, k]; positivity
  have hkd : ∀ t, HasDerivAt k (g * k t) t := fun t => by
    have := ((hasDerivAt_id' t).const_mul g).exp.const_mul k0
    convert this using 1; simp only [k]; ring
  have hcd : ∀ t, HasDerivAt c (c t * ((A - δ) - ρ) / σ) t := fun t => by
    have := (hkd t).const_mul m
    convert this using 1
    simp only [c, g, akG]
    field_simp
  have hcc : ContinuousOn c (Set.Ici 0) := by simp only [c, k]; fun_prop
  refine AKMM.ContinuousTime.mangasarian_consumption_saving (r := A - δ - n) (w := 0)
    (ρ := ρ - n) (u' := fun y => y ^ (-σ)) (a := k) (c := c)
    (μ := fun t => Real.exp (-(ρ - n) * t) * c t ^ (-σ)) hconc hu
    (fun y hy => (Real.rpow_pos_of_pos hy _).le) (fun t _ => hcpos t) hcc (fun t _ => ?_)
    (fun t _ => rfl) (fun t _ => ?_) ?_ hc' hcc' ha' (by rw [h0]; simp [k]) hnpg
  · convert hkd t using 1
    simp only [c, m]
    ring
  · have h := istc_costate_of_euler (n := n) hσ (hcpos t) (hcd t)
    convert h using 1
  · have e : ∀ T, Real.exp (-(ρ - n) * T) * c T ^ (-σ) * k T =
        (m ^ (-σ) * k0 ^ (1 - σ)) * Real.exp (-(A - δ - n - g) * T) := fun T => by
      simp only [c, k]
      rw [Real.mul_rpow hpos.le (by positivity), Real.mul_rpow hk0.le (Real.exp_pos _).le,
        ← Real.exp_mul, Real.rpow_sub hk0, Real.rpow_one]
      have h2 : Real.exp (-(ρ - n) * T) * Real.exp (g * T * -σ) * Real.exp (g * T) =
          Real.exp (-(A - δ - n - g) * T) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        simp only [g, akG]
        field_simp
        ring
      rw [← h2]
      have : 0 < k0 ^ σ := by positivity
      field_simp
      rw [← Real.rpow_add hk0, neg_add_cancel, Real.rpow_zero]
    simp only [e]
    exact (istc_exp_tendsto_zero_iff (by positivity)).mpr (by linarith)

/-- AKMM, footnote 24, p. 385: **the general solution**. Let `b = A − δ`, `q = n + g` and
`m = A − δ − n − g ≠ 0`. Every solution of `K̇ = bK − e^{qt}c(0)` on `[0, ∞)` is
`K(t) = Ξe^{bt} + (c(0)/m)e^{qt}` with the constant of integration `Ξ = K(0) − c(0)/m`. -/
theorem ak_footnote_24_general {A δ ρ σ n c0 : ℝ} {K : ℝ → ℝ}
    (hm : A - δ - n - akG A δ ρ σ ≠ 0)
    (hK : ∀ t, 0 ≤ t → HasDerivAt K ((A - δ) * K t -
      Real.exp ((n + akG A δ ρ σ) * t) * c0) t) :
    ∀ t, 0 ≤ t → K t = (K 0 - c0 / (A - δ - n - akG A δ ρ σ)) * Real.exp ((A - δ) * t) +
      c0 / (A - δ - n - akG A δ ρ σ) * Real.exp ((n + akG A δ ρ σ) * t) := by
  set g := akG A δ ρ σ
  set m := A - δ - n - g
  set f := fun s => (K s - c0 / m * Real.exp ((n + g) * s)) * Real.exp (-(A - δ) * s)
  have hf : ∀ s, 0 ≤ s → HasDerivAt f 0 s := fun s hs => by
    have h1 := ((hK s hs).fun_sub (((hasDerivAt_id' s).const_mul (n + g)).exp.const_mul
      (c0 / m))).fun_mul ((hasDerivAt_id' s).const_mul (-(A - δ))).exp
    convert h1 using 1
    have hmq : (A - δ) - (n + g) = m := by simp only [m]; ring
    have hinv : m * m⁻¹ = 1 := mul_inv_cancel₀ hm
    set e := Real.exp ((n + g) * s)
    set E := Real.exp (-(A - δ) * s)
    linear_combination (-(c0 * e * E * m⁻¹)) * hmq + (-(c0 * e * E)) * hinv
  intro t ht
  have hconst := constant_of_has_deriv_right_zero (f := f) (a := 0) (b := t)
    (fun s hs => (hf s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hf s hs.1).hasDerivWithinAt) t (Set.right_mem_Icc.mpr ht)
  simp only [f, mul_zero, Real.exp_zero, mul_one, neg_mul] at hconst
  have hE : Real.exp (-((A - δ) * t)) * Real.exp ((A - δ) * t) = 1 := by
    rw [← Real.exp_add]; simp
  have := congrArg (· * Real.exp ((A - δ) * t)) hconst
  rw [mul_assoc, hE, mul_one, neg_zero, Real.exp_zero, mul_one] at this
  linarith

/-- AKMM, footnote 24, p. 385: **the TVC forces `Ξ = 0`**. If `σ(A − δ − n) > A − δ − ρ`,
`c(0) > 0`, `K` solves `K̇ = (A − δ)K − e^{(n+g)t}c(0)` on `[0, ∞)` and the TVC
`c(0)^{−σ}e^{−(A−δ)T}K(T) → 0` (13.20) holds, then `c(0) = (A − δ − n − g)K(0)` and
`K(t) = K(0)e^{(n+g)t}`: the closed-form policy is the only solution. -/
theorem ak_footnote_24_unique {A δ ρ σ n c0 : ℝ} {K : ℝ → ℝ} (hσ : 0 < σ) (hc0 : 0 < c0)
    (hbound : A - δ - ρ < σ * (A - δ - n))
    (hK : ∀ t, 0 ≤ t → HasDerivAt K ((A - δ) * K t -
      Real.exp ((n + akG A δ ρ σ) * t) * c0) t)
    (htvc : Tendsto (fun T => c0 ^ (-σ) * Real.exp (-(A - δ) * T) * K T) atTop (𝓝 0)) :
    c0 = (A - δ - n - akG A δ ρ σ) * K 0 ∧
      ∀ t, 0 ≤ t → K t = K 0 * Real.exp ((n + akG A δ ρ σ) * t) := by
  set g := akG A δ ρ σ
  have hpos : 0 < A - δ - n - g := (ak_bounded_iff hσ).1.mp hbound
  set m := A - δ - n - g
  have hgen := ak_footnote_24_general (c0 := c0) hpos.ne' hK
  set Ξ := K 0 - c0 / m
  have hform : ∀ T, 0 ≤ T → c0 ^ (-σ) * Real.exp (-(A - δ) * T) * K T =
      c0 ^ (-σ) * Ξ + c0 ^ (-σ) * (c0 / m) * Real.exp (-m * T) := fun T hT => by
    rw [hgen T hT]
    have h1 : Real.exp (-(A - δ) * T) * Real.exp ((A - δ) * T) = 1 := by
      rw [← Real.exp_add, show -(A - δ) * T + (A - δ) * T = 0 by ring, Real.exp_zero]
    have h2 : Real.exp (-(A - δ) * T) * Real.exp ((n + g) * T) = Real.exp (-m * T) := by
      rw [← Real.exp_add]; simp only [m]; ring_nf
    linear_combination (c0 ^ (-σ) * Ξ) * h1 + (c0 ^ (-σ) * (c0 / m)) * h2
  have hlim2 : Tendsto (fun T => c0 ^ (-σ) * Ξ + c0 ^ (-σ) * (c0 / m) * Real.exp (-m * T))
      atTop (𝓝 (c0 ^ (-σ) * Ξ)) := by
    have := ((istc_exp_tendsto_zero_iff (C := c0 ^ (-σ) * (c0 / m)) (b := -m)
      (by positivity)).mpr (by linarith)).const_add (c0 ^ (-σ) * Ξ)
    simpa using this
  have hlim1 : Tendsto (fun T => c0 ^ (-σ) * Ξ + c0 ^ (-σ) * (c0 / m) * Real.exp (-m * T))
      atTop (𝓝 0) := by
    refine htvc.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT using hform T hT
  have hΞ : c0 ^ (-σ) * Ξ = 0 := tendsto_nhds_unique hlim2 hlim1
  have hΞ0 : Ξ = 0 := by
    rcases mul_eq_zero.mp hΞ with h | h
    · exact absurd h (Real.rpow_pos_of_pos hc0 _).ne'
    · exact h
  have hc0K : c0 = m * K 0 := by
    have : K 0 - c0 / m = 0 := hΞ0
    field_simp at this
    linarith
  refine ⟨hc0K, fun t ht => ?_⟩
  rw [hgen t ht, hΞ0, zero_mul, zero_add]
  change c0 / m * Real.exp ((n + g) * t) = K 0 * Real.exp ((n + g) * t)
  rw [hc0K]
  field_simp

/-- AKMM, footnote 24, p. 385: the printed `K̇/K = A − δ − e^{(n+g)t}c(0)` (without `/K(t)`)
fails on the closed-form path whenever `n + g ≠ 0`: with `K(t) = e^{(n+g)t}` and
`c(0) = A − δ − n − g > 0`, `K̇/K = n + g` is not `A − δ − e^{(n+g)t}c(0)` at `t = 1`. -/
theorem ak_footnote_24_printed_false {A δ ρ σ n : ℝ} (hq : n + akG A δ ρ σ ≠ 0)
    (hpos : 0 < A - δ - n - akG A δ ρ σ) :
    ¬ ∀ t : ℝ, n + akG A δ ρ σ =
      A - δ - Real.exp ((n + akG A δ ρ σ) * t) * (A - δ - n - akG A δ ρ σ) := by
  intro h
  have h0 := h 0
  have h1 := h 1
  simp only [mul_zero, Real.exp_zero, one_mul, mul_one] at h0 h1
  have : Real.exp (n + akG A δ ρ σ) * (A - δ - n - akG A δ ρ σ) =
      1 * (A - δ - n - akG A δ ρ σ) := by linarith
  have he : Real.exp (n + akG A δ ρ σ) = 1 := mul_right_cancel₀ hpos.ne' this
  exact hq (Real.exp_eq_one_iff _ |>.mp he)

/-- AKMM, footnote 25, p. 385: **a capital-income tax lowers growth**. With the net return
taxed at rate `τ` and the revenue `τ(A − δ)k` rebated lump-sum, the household's budget
`k̇ = ((1 − τ)(A − δ) − n)k + τ(A − δ)k − c` is the planner's resource constraint, and the
Euler growth rate `((1 − τ)(A − δ) − ρ)/σ` is strictly decreasing in `τ` when `A > δ`. -/
theorem ak_footnote_25 {A δ ρ σ n : ℝ} (hσ : 0 < σ) (hAδ : δ < A) :
    (∀ τ k c : ℝ, ((1 - τ) * (A - δ) - n) * k + τ * (A - δ) * k - c = (A - δ - n) * k - c) ∧
      StrictAnti (fun τ : ℝ => ((1 - τ) * (A - δ) - ρ) / σ) := by
  refine ⟨fun τ k c => by ring, fun τ₁ τ₂ h => ?_⟩
  simp only
  apply div_lt_div_of_pos_right _ hσ
  nlinarith

end AKMM.Growth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Expanding varieties: the decentralised equilibrium

AKMM, §13.5.1 (pp. 386–392) and Appendix 13.A.5 (p. 853): Romer (1990) without physical capital.
The allocation is symmetric across the `N` varieties (as in the text after (13.34)), so
`∫_0^N x(ν)^{1−φ}dν = Nx^{1−φ}`; the per-variety problems are solved pointwise. Write
`X = A(1−φ)/ψ`.

* Final-goods first-order conditions (13.23)–(13.24) (`eq_13_23`, `eq_13_24`).
* The monopolist's problem (13.25): `x = X^{1/φ}L_y` (13.33) is the global maximum, the price is
  `ψ/(1−φ)`, profits are (13.34) (`eq_13_33`, `eq_13_34`); footnote 32, the Lerner markup
  (`romer_footnote_32`).
* Output, wage and consumption (13.35)–(13.37) (`eq_13_35`, `eq_13_36`, `eq_13_37`); love of
  variety, footnote 29 (`romer_footnote_29`).
* Free entry (13.39)–(13.40), the HJB equation (13.41), the law of motion (13.42), and the
  single ODE (13.43) (`eq_13_40`, `eq_13_41`, `eq_13_42`, `eq_13_43`).
* The balanced growth path (13.44)–(13.46), `L_r* > 0` iff (13.32), the TVC iff (13.31), and
  (13.52) (`eq_13_44`, `romer_Lr_star`, `eq_13_45`, `eq_13_46`, `romer_tvc_iff`, `eq_13_52`).
* Comparative statics: growth falls with `ρ` and `σ` and rises with `L`, and so does the
  research share (`romer_comparative_statics`, `romer_research_share_mono`).
* p. 392: a profit tax or a lower markup lowers growth (`romer_markup_interest`,
  `romer_theta_growth_mono`).
-/

namespace AKMM.Growth

open Real Filter Topology

/-- The constant `X = A(1−φ)/ψ` of the Romer model. -/
noncomputable def romerX (A φ ψ : ℝ) : ℝ := A * (1 - φ) / ψ

/-- `A X^{(1−φ)/φ} = (ψ/(1−φ)) X^{1/φ}`. -/
theorem romer_X_identity {A φ ψ : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1) (hψ : 0 < ψ) :
    A * romerX A φ ψ ^ ((1 - φ) / φ) = ψ / (1 - φ) * romerX A φ ψ ^ (1 / φ) := by
  have h1φ : 0 < 1 - φ := by linarith
  have hX : 0 < romerX A φ ψ := by unfold romerX; positivity
  rw [show 1 / φ = (1 - φ) / φ + 1 by field_simp; ring, Real.rpow_add hX, Real.rpow_one]
  unfold romerX
  field_simp

/-- AKMM, (13.23), p. 387: the marginal product of production labour is `φY/L_y`. -/
theorem eq_13_23 {A φ S Ly : ℝ} (hLy : 0 < Ly) :
    HasDerivAt (fun l => A / (1 - φ) * l ^ φ * S) (φ * (A / (1 - φ) * Ly ^ φ * S) / Ly) Ly := by
  have h := ((Real.hasDerivAt_rpow_const (p := φ) (Or.inl hLy.ne')).const_mul
    (A / (1 - φ))).mul_const S
  convert h using 1
  rw [Real.rpow_sub_one hLy.ne']
  ring

/-- AKMM, (13.24), p. 387: the marginal product of machine `ν` is `AL_y^φx(ν)^{−φ}`. -/
theorem eq_13_24 {A φ Ly x : ℝ} (hφ1 : φ < 1) (hx : 0 < x) :
    HasDerivAt (fun y => A / (1 - φ) * Ly ^ φ * y ^ (1 - φ)) (A * Ly ^ φ * x ^ (-φ)) x := by
  have h1φ : (1 - φ) ≠ 0 := by linarith
  have h := (Real.hasDerivAt_rpow_const (p := 1 - φ) (Or.inl hx.ne')).const_mul
    (A / (1 - φ) * Ly ^ φ)
  convert h using 1
  rw [show 1 - φ - 1 = -φ by ring]
  field_simp

/-- AKMM, (13.33), p. 389: the monopoly quantity `x = X^{1/φ}L_y`. -/
noncomputable def romerXMon (A φ ψ Ly : ℝ) : ℝ := romerX A φ ψ ^ (1 / φ) * Ly

/-- AKMM, (13.25) and (13.33)–(13.34), p. 389: **the monopolist's problem**. Facing the inverse
demand (13.24) `p(x) = AL_y^φx^{−φ}`, profit `AL_y^φx^{1−φ} − ψx` is maximised over `x ≥ 0` at
`x = X^{1/φ}L_y`, where the price is `ψ/(1−φ)`. -/
theorem eq_13_33 {A φ ψ Ly x : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1) (hψ : 0 < ψ)
    (hLy : 0 < Ly) (hx : 0 ≤ x) :
    A * Ly ^ φ * x ^ (1 - φ) - ψ * x ≤
        A * Ly ^ φ * romerXMon A φ ψ Ly ^ (1 - φ) - ψ * romerXMon A φ ψ Ly ∧
      A * Ly ^ φ * romerXMon A φ ψ Ly ^ (-φ) = ψ / (1 - φ) := by
  have h1φ : 0 < 1 - φ := by linarith
  have hX : 0 < romerX A φ ψ := by unfold romerX; positivity
  set xs := romerXMon A φ ψ Ly
  have hxs : 0 < xs := by simp only [xs, romerXMon]; positivity
  have hprice : A * Ly ^ φ * xs ^ (-φ) = ψ / (1 - φ) := by
    simp only [xs, romerXMon]
    rw [Real.mul_rpow (by positivity) hLy.le, ← Real.rpow_mul hX.le,
      show 1 / φ * -φ = -1 by field_simp, Real.rpow_neg_one, Real.rpow_neg hLy.le]
    unfold romerX
    field_simp
  refine ⟨?_, hprice⟩
  have htan := istc_rpow_tangent (α := 1 - φ) (by linarith) (by linarith) hxs hx
  have hc : 0 ≤ A * Ly ^ φ := by positivity
  have := mul_le_mul_of_nonneg_left htan hc
  have hslope : A * Ly ^ φ * ((1 - φ) * xs ^ (1 - φ - 1)) = ψ := by
    rw [show 1 - φ - 1 = -φ by ring, show A * Ly ^ φ * ((1 - φ) * xs ^ (-φ)) =
      (1 - φ) * (A * Ly ^ φ * xs ^ (-φ)) by ring, hprice]
    field_simp
  nlinarith

/-- AKMM, (13.34), p. 389: monopoly profit `ψx/(1−φ) − ψx = φAX^{1/φ−1}L_y`. -/
theorem eq_13_34 {A φ ψ Ly : ℝ} (hA : 0 < A) (hφ1 : φ < 1) (hψ : 0 < ψ) :
    ψ / (1 - φ) * romerXMon A φ ψ Ly - ψ * romerXMon A φ ψ Ly =
      φ * A * romerX A φ ψ ^ (1 / φ - 1) * Ly := by
  have h1φ : 0 < 1 - φ := by linarith
  have hX : 0 < romerX A φ ψ := by unfold romerX; positivity
  unfold romerXMon
  rw [Real.rpow_sub_one hX.ne']
  unfold romerX
  field_simp
  ring

/-- AKMM, footnote 32, p. 389: the Lerner rule. With demand elasticity `−1/φ`, the markup
`(1/φ)/(1/φ − 1)` is `1/(1−φ)`, i.e. the price `ψ/(1−φ)`. -/
theorem romer_footnote_32 {φ : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < 1) :
    (1 / φ) / (1 / φ - 1) = 1 / (1 - φ) := by
  have h1φ : (1 - φ) ≠ 0 := by linarith
  have : (1 / φ - 1) = (1 - φ) / φ := by field_simp
  rw [this]
  field_simp

/-- AKMM, (13.35), p. 389: with every machine at (13.33), output is
`Y = (A/(1−φ))X^{(1−φ)/φ}L_yN`. -/
theorem eq_13_35 {A φ ψ Ly N : ℝ} (hLy : 0 < Ly) (hX : 0 < romerX A φ ψ) :
    A / (1 - φ) * Ly ^ φ * (N * romerXMon A φ ψ Ly ^ (1 - φ)) =
      A / (1 - φ) * romerX A φ ψ ^ ((1 - φ) / φ) * Ly * N := by
  unfold romerXMon
  rw [Real.mul_rpow (by positivity) hLy.le, ← Real.rpow_mul hX.le,
    show 1 / φ * (1 - φ) = (1 - φ) / φ by ring]
  have : Ly ^ φ * Ly ^ (1 - φ) = Ly := by
    rw [← Real.rpow_add hLy, show φ + (1 - φ) = 1 by ring, Real.rpow_one]
  linear_combination (A / (1 - φ) * N * romerX A φ ψ ^ ((1 - φ) / φ)) * this

/-- AKMM, (13.36), p. 389: the wage `w = φY/L_y = φ(A/(1−φ))X^{(1−φ)/φ}N`. -/
theorem eq_13_36 {A φ ψ Ly N : ℝ} (hLy : 0 < Ly) :
    φ * (A / (1 - φ) * romerX A φ ψ ^ ((1 - φ) / φ) * Ly * N) / Ly =
      φ * (A / (1 - φ)) * romerX A φ ψ ^ ((1 - φ) / φ) * N := by
  field_simp

/-- AKMM, (13.37), p. 390: goods-market clearing `c = Y − ψNx` gives
`c = (1/(1−φ)² − 1)ψX^{1/φ}L_yN`. -/
theorem eq_13_37 {A φ ψ Ly N : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1) (hψ : 0 < ψ) :
    A / (1 - φ) * romerX A φ ψ ^ ((1 - φ) / φ) * Ly * N - ψ * N * romerXMon A φ ψ Ly =
      (1 / (1 - φ) ^ 2 - 1) * ψ * romerX A φ ψ ^ (1 / φ) * Ly * N := by
  have h1φ : 0 < 1 - φ := by linarith
  have hid := romer_X_identity hA hφ0 hφ1 hψ
  unfold romerXMon
  have e : A / (1 - φ) * romerX A φ ψ ^ ((1 - φ) / φ) =
      ψ / (1 - φ) ^ 2 * romerX A φ ψ ^ (1 / φ) := by
    rw [div_mul_eq_mul_div, hid]
    field_simp
  rw [e]
  ring

/-- AKMM, footnote 29, p. 387: **love of variety**. With a budget `E` split equally over `N`
machines at price `p_x`, output is `(A/(1−φ))L_y^φN^φ(E/p_x)^{1−φ}`, increasing in `N`. -/
theorem romer_footnote_29 {A φ Ly E px : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1)
    (hLy : 0 < Ly) (hE : 0 < E) (hpx : 0 < px) :
    (∀ N : ℝ, 0 < N → A / (1 - φ) * Ly ^ φ * (N * (E / (px * N)) ^ (1 - φ)) =
      A / (1 - φ) * Ly ^ φ * N ^ φ * (E / px) ^ (1 - φ)) ∧
    StrictMonoOn (fun N : ℝ => A / (1 - φ) * Ly ^ φ * N ^ φ * (E / px) ^ (1 - φ))
      (Set.Ioi 0) := by
  have h1φ : 0 < 1 - φ := by linarith
  refine ⟨fun N hN => ?_, fun N₁ h₁ N₂ h₂ h => ?_⟩
  · rw [show E / (px * N) = E / px * N⁻¹ by field_simp, Real.mul_rpow (by positivity)
      (by positivity), Real.inv_rpow hN.le]
    have : N * (N ^ (1 - φ))⁻¹ = N ^ φ := by
      rw [← Real.rpow_neg hN.le]
      nth_rewrite 1 [← Real.rpow_one N]
      rw [← Real.rpow_add hN]; congr 1; ring
    linear_combination (A / (1 - φ) * Ly ^ φ * (E / px) ^ (1 - φ)) * this
  · simp only
    have := Real.rpow_lt_rpow (le_of_lt h₁) h hφ0
    have hc : 0 < A / (1 - φ) * Ly ^ φ := by positivity
    have hd : 0 < (E / px) ^ (1 - φ) := by positivity
    nlinarith [mul_lt_mul_of_pos_left this hc]

/-- AKMM, (13.39)–(13.40), p. 390: free entry `V = w/(ηN)` with the wage (13.36) gives the
constant firm value `V = (φA/(η(1−φ)))X^{(1−φ)/φ}`. -/
theorem eq_13_40 {A φ ψ η N : ℝ} (hη : 0 < η) (hN : 0 < N) :
    φ * (A / (1 - φ)) * romerX A φ ψ ^ ((1 - φ) / φ) * N / (η * N) =
      φ * A / (η * (1 - φ)) * romerX A φ ψ ^ ((1 - φ) / φ) := by
  field_simp

/-- AKMM, (13.41), p. 390: with `V` constant, the HJB equation `Vr = π + V̇` gives
`r = π/V = η(1−φ)L_y`. -/
theorem eq_13_41 {A φ ψ η Ly r : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1) (hψ : 0 < ψ)
    (hη : 0 < η)
    (hjb : φ * A / (η * (1 - φ)) * romerX A φ ψ ^ ((1 - φ) / φ) * r =
      φ * A * romerX A φ ψ ^ (1 / φ - 1) * Ly + 0) :
    r = η * (1 - φ) * Ly := by
  have h1φ : 0 < 1 - φ := by linarith
  have hX : 0 < romerX A φ ψ := by unfold romerX; positivity
  rw [show 1 / φ - 1 = (1 - φ) / φ by field_simp, add_zero] at hjb
  have hp : 0 < romerX A φ ψ ^ ((1 - φ) / φ) := by positivity
  field_simp at hjb
  nlinarith [hjb, mul_pos (mul_pos hφ0 hA) hp]

/-- AKMM, (13.42), p. 390: with labour-market clearing `L_r = L − L_y`, (13.26) gives
`Ṅ/N = η(L − L_y)`. -/
theorem eq_13_42 {η L Ly N Ndot : ℝ} (hN : 0 < N) (h1326 : Ndot = η * N * (L - Ly)) :
    Ndot / N = η * (L - Ly) := by
  rw [h1326]; field_simp

/-- AKMM, (13.43), p. 390: **the single ODE**. If `c = κL_yN` (13.37) with `κ ≠ 0`, the Euler
equation `ċ/c = (r − ρ)/σ` (13.38) holds with `r = η(1−φ)L_y` (13.41), and `Ṅ = η(L − L_y)N`
(13.42), then `L̇_y/L_y = (η(1−φ+σ)L_y − ρ)/σ − ηL`. -/
theorem eq_13_43 {κ φ η σ ρ L t Lydot : ℝ} {Ly N c : ℝ → ℝ} (hκ : κ ≠ 0) (hσ : 0 < σ)
    (hLy : 0 < Ly t) (hN : 0 < N t) (hc : c = fun s => κ * Ly s * N s)
    (hLyd : HasDerivAt Ly Lydot t) (hNd : HasDerivAt N (η * (L - Ly t) * N t) t)
    (heuler : HasDerivAt c (c t * (η * (1 - φ) * Ly t - ρ) / σ) t) :
    Lydot / Ly t = (η * (1 - φ + σ) * Ly t - ρ) / σ - η * L := by
  have hd : HasDerivAt c (κ * Lydot * N t + κ * Ly t * (η * (L - Ly t) * N t)) t := by
    rw [hc]; exact (hLyd.const_mul κ).fun_mul hNd
  have hu := heuler.unique hd
  rw [hc] at hu
  simp only at hu
  have hκN : κ * N t ≠ 0 := mul_ne_zero hκ hN.ne'
  have hL : Lydot = Ly t * (η * (1 - φ) * Ly t - ρ) / σ - Ly t * η * (L - Ly t) := by
    apply mul_left_cancel₀ hκN
    linear_combination -hu
  rw [hL]
  field_simp
  ring

/-- AKMM, (13.44), p. 390: the balanced-growth production labour
`L_y* = (σL + ρ/η)/(1 − φ + σ)`. -/
noncomputable def romerLyStar (φ η σ ρ L : ℝ) : ℝ := (σ * L + ρ / η) / (1 - φ + σ)

/-- AKMM, (13.44), p. 390: `L_y*` is the unique zero of the right side of (13.43). -/
theorem eq_13_44 {φ η σ ρ L Ly : ℝ} (hφ1 : φ < 1) (hη : 0 < η) (hσ : 0 < σ) :
    (η * (1 - φ + σ) * Ly - ρ) / σ - η * L = 0 ↔ Ly = romerLyStar φ η σ ρ L := by
  have h : 0 < 1 - φ + σ := by linarith
  unfold romerLyStar
  rw [div_sub' hσ.ne', div_eq_zero_iff, or_iff_left hσ.ne', eq_div_iff h.ne']
  constructor <;> intro h0
  · field_simp; linarith
  · field_simp at h0; linarith

/-- AKMM, p. 391: research labour on the balanced growth path
`L_r* = L − L_y* = ((1−φ)L − ρ/η)/(1 − φ + σ)`, positive iff (13.32) `ρ < (1−φ)ηL`. -/
theorem romer_Lr_star {φ η σ ρ L : ℝ} (hφ1 : φ < 1) (hη : 0 < η) (hσ : 0 < σ) :
    L - romerLyStar φ η σ ρ L = ((1 - φ) * L - ρ / η) / (1 - φ + σ) ∧
      (0 < L - romerLyStar φ η σ ρ L ↔ ρ < (1 - φ) * η * L) := by
  have h : 0 < 1 - φ + σ := by linarith
  have e : L - romerLyStar φ η σ ρ L = ((1 - φ) * L - ρ / η) / (1 - φ + σ) := by
    unfold romerLyStar; field_simp; ring
  refine ⟨e, ?_⟩
  rw [e, div_pos_iff_of_pos_right h, sub_pos, div_lt_iff₀ hη]
  constructor <;> intro h0 <;> linarith

/-- AKMM, (13.45), p. 391: the interest rate on the balanced growth path,
`r* = η(1−φ)L_y* = (1−φ)(ησL + ρ)/(1 − φ + σ)`. -/
theorem eq_13_45 {φ η σ ρ L : ℝ} (hφ1 : φ < 1) (hη : 0 < η) (hσ : 0 < σ) :
    η * (1 - φ) * romerLyStar φ η σ ρ L = (1 - φ) * (η * σ * L + ρ) / (1 - φ + σ) := by
  have h : 0 < 1 - φ + σ := by linarith
  unfold romerLyStar; field_simp

/-- AKMM, (13.46), p. 391: the growth rate of varieties `ηL_r* = ((1−φ)ηL − ρ)/(1 − φ + σ)`;
it also satisfies the Euler equation `g = (r* − ρ)/σ`. -/
theorem eq_13_46 {φ η σ ρ L : ℝ} (hφ1 : φ < 1) (hη : 0 < η) (hσ : 0 < σ) :
    η * (L - romerLyStar φ η σ ρ L) = ((1 - φ) * η * L - ρ) / (1 - φ + σ) ∧
      (η * (1 - φ) * romerLyStar φ η σ ρ L - ρ) / σ =
        ((1 - φ) * η * L - ρ) / (1 - φ + σ) := by
  have h : 0 < 1 - φ + σ := by linarith
  refine ⟨?_, ?_⟩ <;> unfold romerLyStar <;> field_simp <;> ring

/-- AKMM, (13.31) and p. 391: with `g` the balanced growth rate and `r* = σg + ρ`, the TVC
`e^{−r*T}a(T) → 0` for `a = a_0e^{gT}`, `a_0 > 0`, holds iff (13.31) `ρ > (1−σ)g`. -/
theorem romer_tvc_iff {σ ρ g a0 : ℝ} (ha0 : 0 < a0) :
    Tendsto (fun T => Real.exp (-(σ * g + ρ) * T) * (a0 * Real.exp (g * T))) atTop (𝓝 0) ↔
      (1 - σ) * g < ρ := by
  have e : ∀ T, Real.exp (-(σ * g + ρ) * T) * (a0 * Real.exp (g * T)) =
      a0 * Real.exp (((1 - σ) * g - ρ) * T) := fun T => by
    rw [mul_left_comm, ← Real.exp_add]; ring_nf
  simp only [e]
  rw [istc_exp_tendsto_zero_iff ha0, sub_neg]

/-- AKMM, (13.52), p. 392: on the balanced growth path `π*/r* = V`, the constant
`(φ/η)(A/(1−φ))X^{(1−φ)/φ}`. -/
theorem eq_13_52 {A φ ψ η Ly : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1)
    (hη : 0 < η) (hLy : 0 < Ly) :
    φ * A * romerX A φ ψ ^ (1 / φ - 1) * Ly / (η * (1 - φ) * Ly) =
      φ / η * (A / (1 - φ)) * romerX A φ ψ ^ ((1 - φ) / φ) := by
  have h1φ : 0 < 1 - φ := by linarith
  rw [show 1 / φ - 1 = (1 - φ) / φ by field_simp]
  field_simp

/-- AKMM, (13.46), p. 391: **comparative statics**. Under (13.32) the balanced growth rate
`((1−φ)ηL − ρ)/(1 − φ + σ)` is strictly decreasing in `ρ` and in `σ > 0`, and strictly
increasing in `L` (the strong scale effect). -/
theorem romer_comparative_statics {φ η σ ρ L : ℝ} (hφ1 : φ < 1) (hη : 0 < η) (hσ : 0 < σ)
    (h1332 : ρ < (1 - φ) * η * L) :
    StrictAnti (fun ρ' => ((1 - φ) * η * L - ρ') / (1 - φ + σ)) ∧
      StrictAntiOn (fun σ' => ((1 - φ) * η * L - ρ) / (1 - φ + σ')) (Set.Ioi 0) ∧
      StrictMono (fun L' => ((1 - φ) * η * L' - ρ) / (1 - φ + σ)) := by
  have h : 0 < 1 - φ + σ := by linarith
  have h1φ : 0 < 1 - φ := by linarith
  refine ⟨fun a b hab => ?_, fun a ha b hb hab => ?_, fun a b hab => ?_⟩
  · exact div_lt_div_of_pos_right (by linarith) h
  · simp only
    apply div_lt_div_of_pos_left (by linarith) (by simp at ha; linarith) (by linarith)
  · simp only
    apply div_lt_div_of_pos_right _ h
    have := mul_lt_mul_of_pos_left hab (mul_pos h1φ hη)
    linarith

/-- AKMM, p. 391: **the research share `L_r*/L` rises with `L`**:
`L_r*/L = ((1−φ) − ρ/(ηL))/(1 − φ + σ)` is strictly increasing in `L > 0` when `ρ > 0`. -/
theorem romer_research_share_mono {φ η σ ρ : ℝ} (hφ1 : φ < 1) (hη : 0 < η) (hσ : 0 < σ)
    (hρ : 0 < ρ) :
    StrictMonoOn (fun L => (L - romerLyStar φ η σ ρ L) / L) (Set.Ioi 0) := by
  have h : 0 < 1 - φ + σ := by linarith
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  simp only
  rw [(romer_Lr_star hφ1 hη hσ).1, (romer_Lr_star hφ1 hη hσ).1, div_div, div_div,
    div_lt_div_iff₀ (by positivity) (by positivity)]
  have hρη : 0 < ρ / η := div_pos hρ hη
  have key : ρ / η * a < ρ / η * b := mul_lt_mul_of_pos_left hab hρη
  nlinarith [mul_lt_mul_of_pos_left key h]

/-- AKMM, p. 392: **profit taxes and markups**. If a fraction `θ > 0` of the monopoly profit
`(μ−1)ψx` is kept (a profit tax `1 − θ`), with markup `μ`, then with `V` from free entry
the HJB equation gives `r = η(1−φ)θ(μ−1)/(φμ)·L_y`; at the Romer markup `μ = 1/(1−φ)` and
`θ = 1` this is (13.41). -/
theorem romer_markup_interest {φ : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < 1) :
    (1 / (1 - φ) - 1) / (φ * (1 / (1 - φ))) = 1 := by
  have h1φ : (1 - φ) ≠ 0 := by linarith
  field_simp
  ring

/-- AKMM, p. 392: with `r = η(1−φ)θL_y` (θ the profit share kept, e.g. after a profit tax or
with a lower markup, `θ = (μ−1)/(φμ)`), the balanced growth rate solving `g = ηL_r`,
`r = ρ + σg`, `L = L_y + L_r` is `g(θ) = ((1−φ)θηL − ρ)/((1−φ)θ + σ)`; it is strictly
increasing in `θ > 0` whenever `ρ > 0`. So taxing profits, or lowering the markup below
`1/(1−φ)` (which lowers `θ`), lowers growth. -/
theorem romer_theta_growth_mono {φ η σ ρ L : ℝ} (hφ1 : φ < 1) (hη : 0 < η) (hσ : 0 < σ)
    (hρ : 0 < ρ) (hL : 0 < L) :
    (∀ θ, 0 < θ → ∀ Ly, η * (1 - φ) * θ * Ly = ρ + σ * (η * (L - Ly)) →
      η * (L - Ly) = ((1 - φ) * θ * η * L - ρ) / ((1 - φ) * θ + σ)) ∧
    StrictMonoOn (fun θ => ((1 - φ) * θ * η * L - ρ) / ((1 - φ) * θ + σ)) (Set.Ioi 0) := by
  have h1φ : 0 < 1 - φ := by linarith
  refine ⟨fun θ hθ Ly h => ?_, fun a ha b hb hab => ?_⟩
  · have hden : 0 < (1 - φ) * θ + σ := by positivity
    rw [eq_div_iff hden.ne']
    nlinarith [h]
  · simp only [Set.mem_Ioi] at ha hb
    simp only
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have : 0 < (b - a) * ((1 - φ) * (σ * η * L + ρ)) := by positivity
    nlinarith

end AKMM.Growth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Expanding varieties: no transitional dynamics, and the corner

AKMM, §13.5.1, footnotes 33–34 (p. 391). The single ODE (13.43) is
`L̇_y = L_y(aL_y − b)` with `a = η(1−φ+σ)/σ` and `b = ρ/σ + ηL`, and `L_y* = b/a`.

* `romer_footnote_33_solution`: `1/L_y` solves a linear ODE, so every positive solution on
  `[0, ∞)` is `1/L_y(t) = 1/L_y* + (1/L_y(0) − 1/L_y*)e^{bt}`.
* `romer_footnote_33_above`: if `L_y(0) > L_y*` there is no positive solution on `[0, ∞)`
  (it explodes in finite time, and so certainly exceeds `L`).
* `romer_footnote_33_below`, `romer_footnote_33_tvc_fails`: if `L_y(0) < L_y*` then
  `L_y → 0`, so `r → 0`, and the TVC `e^{−∫r}a(T) → 0` fails.
* `romer_footnote_33`: hence every equilibrium path has `L_y ≡ L_y*` from date 0.
* `romer_footnote_34`: at the corner `L_r = 0`, `r* = ρ` and `V = π/ρ`, which exceeds the entry
  cost `w/(ηN)` iff (13.32). The printed `V = π/r* = φAX^{1/φ−1}L` omits the `/ρ`
  (`romer_footnote_34_printed_false`).
-/

namespace AKMM.Growth

open Real Filter Topology

/-- AKMM, footnote 33 and (13.43), p. 391: **the explicit solution**. If `L_y > 0` satisfies
`L̇_y = L_y((η(1−φ+σ)L_y − ρ)/σ − ηL)` on `[0, ∞)`, then with `b = ρ/σ + ηL`,
`1/L_y(t) = 1/L_y* + (1/L_y(0) − 1/L_y*)e^{bt}`. -/
theorem romer_footnote_33_solution {φ η σ ρ L : ℝ} {Ly : ℝ → ℝ} (hφ1 : φ < 1) (hη : 0 < η)
    (hσ : 0 < σ) (hLs : 0 < romerLyStar φ η σ ρ L) (hpos : ∀ t, 0 ≤ t → 0 < Ly t)
    (hode : ∀ t, 0 ≤ t → HasDerivAt Ly (Ly t * ((η * (1 - φ + σ) * Ly t - ρ) / σ - η * L)) t) :
    ∀ t, 0 ≤ t → (Ly t)⁻¹ = (romerLyStar φ η σ ρ L)⁻¹ +
      ((Ly 0)⁻¹ - (romerLyStar φ η σ ρ L)⁻¹) * Real.exp ((ρ / σ + η * L) * t) := by
  set b := ρ / σ + η * L
  set Ls := romerLyStar φ η σ ρ L
  have hden : 0 < 1 - φ + σ := by linarith
  have hrel : η * (1 - φ + σ) * Ls = σ * η * L + ρ := by
    simp only [Ls, romerLyStar]; field_simp
  have hrel0 : σ * η * L + ρ ≠ 0 := by rw [← hrel]; positivity
  have hLsinv : Ls⁻¹ = η * (1 - φ + σ) / (σ * η * L + ρ) := by
    rw [← hrel]; field_simp
  set f := fun s => ((Ly s)⁻¹ - Ls⁻¹) * Real.exp (-b * s)
  have hf : ∀ s, 0 ≤ s → HasDerivAt f 0 s := fun s hs => by
    have hw := (hode s hs).fun_inv (hpos s hs).ne'
    have h1 := (hw.sub_const Ls⁻¹).fun_mul ((hasDerivAt_id' s).const_mul (-b)).exp
    convert h1 using 1
    have hL := (hpos s hs).ne'
    set E := Real.exp (-b * s)
    have hb : b = (σ * η * L + ρ) / σ := by simp only [b]; field_simp; ring
    have key : -(Ly s * ((η * (1 - φ + σ) * Ly s - ρ) / σ - η * L)) / Ly s ^ 2 +
        ((Ly s)⁻¹ - Ls⁻¹) * (-b) = 0 := by
      rw [hb]
      have hLs0 := hLs.ne'
      field_simp
      linear_combination (-(Ly s)) * hrel
    linear_combination (-E) * key
  intro t ht
  have hconst := constant_of_has_deriv_right_zero (f := f) (a := 0) (b := t)
    (fun s hs => (hf s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hf s hs.1).hasDerivWithinAt) t (Set.right_mem_Icc.mpr ht)
  simp only [f, mul_zero, Real.exp_zero, mul_one] at hconst
  have hE : Real.exp (-b * t) * Real.exp (b * t) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have := congrArg (· * Real.exp (b * t)) hconst
  rw [mul_assoc, hE, mul_one] at this
  linarith

/-- AKMM, footnote 33, p. 391: **starting above `L_y*` is impossible**. If `ρ > 0`, `L > 0`
and `L_y(0) > L_y*`, no positive solution of (13.43) exists on `[0, ∞)`: `1/L_y` would become
negative. -/
theorem romer_footnote_33_above {φ η σ ρ L : ℝ} {Ly : ℝ → ℝ} (hφ1 : φ < 1) (hη : 0 < η)
    (hσ : 0 < σ) (hρ : 0 < ρ) (hL : 0 < L) (hpos : ∀ t, 0 ≤ t → 0 < Ly t)
    (hode : ∀ t, 0 ≤ t → HasDerivAt Ly (Ly t * ((η * (1 - φ + σ) * Ly t - ρ) / σ - η * L)) t)
    (habove : romerLyStar φ η σ ρ L < Ly 0) : False := by
  have hden : 0 < 1 - φ + σ := by linarith
  have hLs : 0 < romerLyStar φ η σ ρ L := by unfold romerLyStar; positivity
  have hsol := romer_footnote_33_solution hφ1 hη hσ hLs hpos hode
  set b := ρ / σ + η * L
  have hb : 0 < b := by positivity
  set ws := (romerLyStar φ η σ ρ L)⁻¹
  set w0 := (Ly 0)⁻¹
  have hw0 : 0 < w0 := by have := hpos 0 le_rfl; positivity
  have hlt : w0 < ws := inv_strictAnti₀ hLs habove
  set T := (w0 / (ws - w0) + 1) / b
  have hT : 0 ≤ T := by
    have : 0 < ws - w0 := sub_pos.mpr hlt
    positivity
  have hexp : 1 + b * T ≤ Real.exp (b * T) := by
    have := Real.add_one_le_exp (b * T); linarith
  have hbT : b * T = w0 / (ws - w0) + 1 := by simp only [T]; field_simp
  have hneg : ws + (w0 - ws) * Real.exp (b * T) < 0 := by
    have h1 : (w0 - ws) * Real.exp (b * T) ≤ (w0 - ws) * (1 + b * T) :=
      mul_le_mul_of_nonpos_left hexp (by linarith)
    have h2 : ws + (w0 - ws) * (1 + b * T) = w0 - ws := by
      rw [hbT]
      have : ws - w0 ≠ 0 := (sub_pos.mpr hlt).ne'
      field_simp
      ring
    linarith
  have hTpos := hpos T hT
  have := hsol T hT
  have : 0 < (Ly T)⁻¹ := by positivity
  linarith

/-- AKMM, footnote 33, p. 391: **starting below `L_y*`, `L_y → 0`** (for `ρ > 0`, `L > 0`). -/
theorem romer_footnote_33_below {φ η σ ρ L : ℝ} {Ly : ℝ → ℝ} (hφ1 : φ < 1) (hη : 0 < η)
    (hσ : 0 < σ) (hρ : 0 < ρ) (hL : 0 < L) (hpos : ∀ t, 0 ≤ t → 0 < Ly t)
    (hode : ∀ t, 0 ≤ t → HasDerivAt Ly (Ly t * ((η * (1 - φ + σ) * Ly t - ρ) / σ - η * L)) t)
    (hbelow : Ly 0 < romerLyStar φ η σ ρ L) : Tendsto Ly atTop (𝓝 0) := by
  have hden : 0 < 1 - φ + σ := by linarith
  have hLs : 0 < romerLyStar φ η σ ρ L := by unfold romerLyStar; positivity
  have hsol := romer_footnote_33_solution hφ1 hη hσ hLs hpos hode
  have hb : 0 < ρ / σ + η * L := by positivity
  have hgap : 0 < (Ly 0)⁻¹ - (romerLyStar φ η σ ρ L)⁻¹ :=
    sub_pos.mpr (inv_strictAnti₀ (hpos 0 le_rfl) hbelow)
  have hw : Tendsto (fun t => (romerLyStar φ η σ ρ L)⁻¹ +
      ((Ly 0)⁻¹ - (romerLyStar φ η σ ρ L)⁻¹) * Real.exp ((ρ / σ + η * L) * t)) atTop atTop := by
    apply tendsto_atTop_add_const_left
    apply Tendsto.const_mul_atTop hgap
    exact Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hb)
  have hinv := tendsto_inv_atTop_zero.comp hw
  refine hinv.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simp only [Function.comp]
  rw [← hsol t ht, inv_inv]

/-- AKMM, footnote 33, p. 391: **below `L_y*` the TVC fails**. Let `M` be the discount factor,
`Ṁ = −rM` with `r = η(1−φ)L_y` (13.41), `N` the varieties, `Ṅ = η(L − L_y)N` (13.42), both
positive, and `V > 0` the constant firm value, so that wealth is `a = VN`. If `L_y → 0`, then
`M(T)VN(T)` does not tend to `0`. -/
theorem romer_footnote_33_tvc_fails {φ η L V : ℝ} {Ly M N : ℝ → ℝ} (hφ1 : φ < 1) (hη : 0 < η)
    (hL : 0 < L) (hV : 0 < V) (hM : ∀ t, 0 ≤ t → 0 < M t) (hN : ∀ t, 0 ≤ t → 0 < N t)
    (hMd : ∀ t, 0 ≤ t → HasDerivAt M (-(η * (1 - φ) * Ly t) * M t) t)
    (hNd : ∀ t, 0 ≤ t → HasDerivAt N (η * (L - Ly t) * N t) t)
    (hLy : Tendsto Ly atTop (𝓝 0)) :
    ¬ Tendsto (fun T => M T * V * N T) atTop (𝓝 0) := by
  intro htvc
  have h2φ : 0 < 2 - φ := by linarith
  obtain ⟨T0, hT0⟩ := Filter.eventually_atTop.mp
    ((hLy.eventually (gt_mem_nhds (div_pos hL h2φ))).and (eventually_ge_atTop (0 : ℝ)))
  set T1 := max T0 0
  have hP : ∀ t, 0 ≤ t → HasDerivAt (fun s => M s * N s)
      (η * (L - (2 - φ) * Ly t) * (M t * N t)) t := fun t ht => by
    convert (hMd t ht).fun_mul (hNd t ht) using 1
    ring
  have hmono : MonotoneOn (fun s => M s * N s) (Set.Ici T1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici T1)
      (f' := fun t => η * (L - (2 - φ) * Ly t) * (M t * N t))
    · exact fun t ht => (hP t (le_trans (le_max_right _ _) ht)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact (hP t (le_trans (le_max_right _ _) ht.le)).hasDerivWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht0 : 0 ≤ t := le_trans (le_max_right _ _) ht.le
      have hlt := (hT0 t (le_trans (le_max_left _ _) ht.le)).1
      have : (2 - φ) * Ly t < L := by rw [lt_div_iff₀ h2φ] at hlt; linarith
      have := hM t ht0; have := hN t ht0
      have : 0 ≤ L - (2 - φ) * Ly t := by linarith
      positivity
  have hP1 : 0 < M T1 * N T1 := mul_pos (hM T1 (le_max_right _ _)) (hN T1 (le_max_right _ _))
  have hlower : ∀ T, T1 ≤ T → V * (M T1 * N T1) ≤ M T * V * N T := fun T hT => by
    have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hT) hT
    simp only at this
    nlinarith
  have hlim : V * (M T1 * N T1) ≤ 0 := ge_of_tendsto htvc (by
    filter_upwards [eventually_ge_atTop T1] with T hT using hlower T hT)
  have : 0 < V * (M T1 * N T1) := mul_pos hV hP1
  linarith

/-- AKMM, footnote 33 and p. 391: **the balanced growth path is the only equilibrium**. If
`L_y > 0` solves (13.43) on `[0, ∞)` and the TVC `M(T)VN(T) → 0` holds (with `M`, `N`, `V` as in
`romer_footnote_33_tvc_fails`), then `L_y(t) = L_y*` for all `t ≥ 0`: there are no
transitional dynamics. -/
theorem romer_footnote_33 {φ η σ ρ L V : ℝ} {Ly M N : ℝ → ℝ} (hφ1 : φ < 1) (hη : 0 < η)
    (hσ : 0 < σ) (hρ : 0 < ρ) (hL : 0 < L) (hV : 0 < V) (hpos : ∀ t, 0 ≤ t → 0 < Ly t)
    (hode : ∀ t, 0 ≤ t → HasDerivAt Ly (Ly t * ((η * (1 - φ + σ) * Ly t - ρ) / σ - η * L)) t)
    (hM : ∀ t, 0 ≤ t → 0 < M t) (hN : ∀ t, 0 ≤ t → 0 < N t)
    (hMd : ∀ t, 0 ≤ t → HasDerivAt M (-(η * (1 - φ) * Ly t) * M t) t)
    (hNd : ∀ t, 0 ≤ t → HasDerivAt N (η * (L - Ly t) * N t) t)
    (htvc : Tendsto (fun T => M T * V * N T) atTop (𝓝 0)) :
    ∀ t, 0 ≤ t → Ly t = romerLyStar φ η σ ρ L := by
  have hden : 0 < 1 - φ + σ := by linarith
  have hLs : 0 < romerLyStar φ η σ ρ L := by unfold romerLyStar; positivity
  rcases lt_trichotomy (Ly 0) (romerLyStar φ η σ ρ L) with hlt | heq | hgt
  · exact absurd htvc (romer_footnote_33_tvc_fails hφ1 hη hL hV hM hN hMd hNd
      (romer_footnote_33_below hφ1 hη hσ hρ hL hpos hode hlt))
  · intro t ht
    have := romer_footnote_33_solution hφ1 hη hσ hLs hpos hode t ht
    rw [heq, sub_self, zero_mul, add_zero] at this
    have h1 := hpos t ht
    field_simp at this
    linarith
  · exact absurd hgt (fun h => romer_footnote_33_above hφ1 hη hσ hρ hL hpos hode h)

/-- AKMM, footnote 34, p. 391: **the corner is not an equilibrium**. At `L_r = 0` (`L_y = L`)
there is no growth, so the Euler equation gives `r* = ρ`, and with `V̇ = 0` the HJB equation
gives `V = π/ρ`, `π = φAX^{1/φ−1}L`. Then `V > w/(ηN) = (φA/(η(1−φ)))X^{(1−φ)/φ}` iff (13.32)
`ρ < (1−φ)ηL`, so (13.32) rules the corner out. -/
theorem romer_footnote_34 {A φ ψ η ρ L : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1)
    (hψ : 0 < ψ) (hη : 0 < η) (hρ : 0 < ρ) :
    φ * A / (η * (1 - φ)) * romerX A φ ψ ^ ((1 - φ) / φ) <
        φ * A * romerX A φ ψ ^ (1 / φ - 1) * L / ρ ↔ ρ < (1 - φ) * η * L := by
  have h1φ : 0 < 1 - φ := by linarith
  have hX : 0 < romerX A φ ψ := by unfold romerX; positivity
  rw [show 1 / φ - 1 = (1 - φ) / φ by field_simp]
  set P := φ * A * romerX A φ ψ ^ ((1 - φ) / φ)
  have hP : 0 < P := by positivity
  rw [show φ * A / (η * (1 - φ)) * romerX A φ ψ ^ ((1 - φ) / φ) = P / (η * (1 - φ)) by
    simp only [P]; ring, div_lt_div_iff₀ (by positivity) hρ]
  constructor <;> intro h <;> nlinarith

/-- AKMM, footnote 34, p. 391: the printed `V = π/r* = φAX^{1/φ−1}L` is false: with `r* = ρ`,
`π/r* = π` only if `ρ = 1`. -/
theorem romer_footnote_34_printed_false {A φ ψ ρ L : ℝ} (hA : 0 < A) (hφ0 : 0 < φ)
    (hφ1 : φ < 1) (hψ : 0 < ψ) (hL : 0 < L) (hρ : 0 < ρ) (hρ1 : ρ ≠ 1) :
    φ * A * romerX A φ ψ ^ (1 / φ - 1) * L / ρ ≠ φ * A * romerX A φ ψ ^ (1 / φ - 1) * L := by
  have h1φ : 0 < 1 - φ := by linarith
  have hX : 0 < romerX A φ ψ := by unfold romerX; positivity
  have hP : 0 < φ * A * romerX A φ ψ ^ (1 / φ - 1) * L := by positivity
  intro h
  rw [div_eq_iff hρ.ne'] at h
  apply hρ1
  have h2 : φ * A * romerX A φ ψ ^ (1 / φ - 1) * L * (ρ - 1) = 0 := by linarith
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 hP.ne'
  · linarith

end AKMM.Growth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Expanding varieties: the planner and policy

AKMM, §13.5.1 (pp. 391–392) and Appendix 13.A.6 (pp. 853–854).

* The static problem (13.A.16): `x^{SP} = (A/ψ)^{1/φ}L_y` is the unique maximiser
  (`eq_13_A_16`); collapsing the constraints gives (13.A.17) (`eq_13_A_17`).
* The first-order conditions (13.A.18)–(13.A.19) give the Euler equation (13.A.21)
  (`eq_13_A_21`), and balanced growth gives `L_y^{SP}` and `g^{SP}` (13.50)–(13.51)
  (`romer_planner_Ly`, `eq_13_50`, `eq_13_51`).
* With `X = (M/η)N`, `M = ψ(A/ψ)^{1/φ}φ/(1−φ)`, the planner's problem is an AK problem
  `Ẋ = ηLX − c`; under (13.49) the balanced path is catching-up optimal from every `N(0)`, so
  there are no transitional dynamics (`romer_planner_optimal`).
* `x^{DE}/x^{SP} = (1−φ)^{1/φ} < 1`, not the printed `(1−φ)^φ` (`romer_machine_ratio`,
  `romer_machine_ratio_printed_false`).
* A purchase subsidy `τ` gives the planner's machine quantity iff `τ = φ` (`1 − τ = 1 − φ`), not
  the printed `1 − τ = (1−φ)^{−1}`, which lowers machine use (`romer_subsidy`); even then growth
  `(ηL − ρ)/(1 + σ)` is below `g^{SP}` (`romer_subsidy_not_efficient`).
* The decentralised growth rate is strictly below the planner's (`romer_planner_growth_gt`).
-/

namespace AKMM.Growth

open Real Filter Topology

/-- AKMM, (13.A.16), p. 853: **the planner's static problem**. Per variety, final output net of
machine costs, `(A/(1−φ))L_y^φx^{1−φ} − ψx`, is maximised over `x ≥ 0` at
`x^{SP} = (A/ψ)^{1/φ}L_y`, where `AL_y^φx^{−φ} = ψ`. -/
theorem eq_13_A_16 {A φ ψ Ly x : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1) (hψ : 0 < ψ)
    (hLy : 0 < Ly) (hx : 0 ≤ x) :
    A / (1 - φ) * Ly ^ φ * x ^ (1 - φ) - ψ * x ≤
        A / (1 - φ) * Ly ^ φ * ((A / ψ) ^ (1 / φ) * Ly) ^ (1 - φ) - ψ * ((A / ψ) ^ (1 / φ) * Ly) ∧
      A * Ly ^ φ * ((A / ψ) ^ (1 / φ) * Ly) ^ (-φ) = ψ := by
  have h1φ : 0 < 1 - φ := by linarith
  have hX : romerX (A / (1 - φ)) φ ψ = A / ψ := by unfold romerX; field_simp
  have h := eq_13_33 (A := A / (1 - φ)) (by positivity) hφ0 hφ1 hψ hLy hx
  unfold romerXMon at h
  rw [hX] at h
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  have : A * Ly ^ φ * ((A / ψ) ^ (1 / φ) * Ly) ^ (-φ) =
      (1 - φ) * (A / (1 - φ) * Ly ^ φ * ((A / ψ) ^ (1 / φ) * Ly) ^ (-φ)) := by field_simp
  rw [this, h2]
  field_simp

/-- AKMM, (13.A.17), p. 853: with `x = (A/ψ)^{1/φ}L_y` for every variety, the resource
constraint (13.48) `c = Y − ψNx` is `c = M L_yN` with `M = ψ(A/ψ)^{1/φ}φ/(1−φ)`. -/
theorem eq_13_A_17 {A φ ψ Ly N : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1) (hψ : 0 < ψ)
    (hLy : 0 < Ly) :
    A / (1 - φ) * Ly ^ φ * (N * ((A / ψ) ^ (1 / φ) * Ly) ^ (1 - φ)) -
        ψ * N * ((A / ψ) ^ (1 / φ) * Ly) =
      ψ * (A / ψ) ^ (1 / φ) * (φ / (1 - φ)) * Ly * N := by
  have h1φ : 0 < 1 - φ := by linarith
  have hAψ : 0 < A / ψ := by positivity
  rw [Real.mul_rpow (by positivity) hLy.le, ← Real.rpow_mul hAψ.le,
    show 1 / φ * (1 - φ) = 1 / φ - 1 by field_simp, Real.rpow_sub_one hAψ.ne']
  have : Ly ^ φ * Ly ^ (1 - φ) = Ly := by
    rw [← Real.rpow_add hLy, show φ + (1 - φ) = 1 by ring, Real.rpow_one]
  have e : A / (1 - φ) * Ly ^ φ * (N * ((A / ψ) ^ (1 / φ) / (A / ψ) * Ly ^ (1 - φ))) =
      ψ / (1 - φ) * (A / ψ) ^ (1 / φ) * N * (Ly ^ φ * Ly ^ (1 - φ)) := by
    field_simp
  rw [e, this]
  field_simp
  ring

/-- AKMM, (13.A.18)–(13.A.21), p. 854: **the planner's Euler equation**. If
`λ = e^{−ρt}c^{−σ}M/η` (13.A.18) and `λ̇ = −ηLλ` (13.A.19), then `ċ/c = (ηL − ρ)/σ`. -/
theorem eq_13_A_21 {σ ρ η L M t cdot : ℝ} {c lam : ℝ → ℝ} (hσ : 0 < σ) (hη : 0 < η)
    (hM : 0 < M) (hc : 0 < c t) (hcd : HasDerivAt c cdot t)
    (h18 : lam = fun s => Real.exp (-ρ * s) * c s ^ (-σ) * (M / η))
    (h19 : HasDerivAt lam (-(η * L) * lam t) t) :
    cdot / c t = (η * L - ρ) / σ := by
  have h := eq_13_A_7 (n := 0) (r := η * L) (lam := fun s => lam s * (η / M)) hσ hc hcd
    (by rw [h18]; funext s; field_simp; ring_nf) (by
      convert h19.mul_const (η / M) using 1; ring)
  rw [h]

/-- AKMM, p. 854: **balanced growth for the planner**. If `ċ/c = (ηL − ρ)/σ` and, with
`L_y` constant, `ċ/c = Ṅ/N = η(L − L_y)`, then `L_y^{SP} = ((σ − 1)L + ρ/η)/σ`. -/
theorem romer_planner_Ly {σ ρ η L Ly : ℝ} (hσ : 0 < σ) (hη : 0 < η)
    (h : (η * L - ρ) / σ = η * (L - Ly)) : Ly = ((σ - 1) * L + ρ / η) / σ := by
  field_simp at h ⊢
  nlinarith [h]

/-- AKMM, (13.50), p. 392: the planner's growth rate `g^{SP} = (ηL − ρ)/σ` is
`η(L − L_y^{SP})`. -/
theorem eq_13_50 {σ ρ η L : ℝ} (hσ : 0 < σ) (hη : 0 < η) :
    η * (L - ((σ - 1) * L + ρ / η) / σ) = (η * L - ρ) / σ := by
  field_simp; ring

/-- AKMM, (13.51), p. 392: the planner's machine quantity
`x = (A/ψ)^{1/φ}L_y^{SP} = (A/ψ)^{1/φ}((σ − 1)L + ρ/η)/σ`. -/
theorem eq_13_51 {A ψ φ σ ρ η L : ℝ} :
    (A / ψ) ^ (1 / φ) * (((σ - 1) * L + ρ / η) / σ) =
      (A / ψ) ^ (1 / φ) * ((σ - 1) * L + ρ / η) / σ := by ring

/-- AKMM, (13.47)–(13.51) and p. 392: **the planner's optimum**. Under (13.49)
`(1 − σ)ηL < ρ` and `u` concave with `u'(c) = c^{−σ}`, from `N(0) = N_0 > 0` the path with
`c(t) = (ηL − g)(M/η)N_0e^{gt}`, `g = (ηL − ρ)/σ` (so `L_y = c/(MN)` is constant at `L_y^{SP}`
and `N` grows at `g`) is catching-up optimal against every path with `N' ≥ 0` from `N_0`,
`Ṅ' = ηLN' − ηc'/M` ((13.A.17) in (13.42)), and positive continuous consumption. -/
theorem romer_planner_optimal {σ ρ η L M N0 : ℝ} {u : ℝ → ℝ} {N' c' : ℝ → ℝ} (hσ : 0 < σ)
    (hη : 0 < η) (hM : 0 < M) (hN0 : 0 < N0) (h1349 : (1 - σ) * η * L < ρ)
    (hconc : ConcaveOn ℝ (Set.Ioi 0) u) (hu : ∀ y, 0 < y → HasDerivAt u (y ^ (-σ)) y)
    (hN' : ∀ t, 0 ≤ t → 0 ≤ N' t) (hc' : ∀ t, 0 ≤ t → 0 < c' t)
    (hcc' : ContinuousOn c' (Set.Ici 0))
    (hNd' : ∀ t, 0 ≤ t → HasDerivAt N' (η * L * N' t - η * c' t / M) t) (h0 : N' 0 = N0) :
    ∀ ε > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c' t) ≤
      (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u ((η * L - (η * L - ρ) / σ) *
        (M / η * N0 * Real.exp ((η * L - ρ) / σ * t)))) + ε := by
  have hbound : η * L - 0 - ρ < σ * (η * L - 0 - 0) := by nlinarith
  have h := ak_optimal (A := η * L) (δ := 0) (n := 0) (k0 := M / η * N0)
    (k' := fun t => M / η * N' t) (c' := c') hσ (by positivity) hbound hconc hu
    (fun t ht => by have := hN' t ht; positivity)
    hc' hcc' (fun t ht => by
      convert (hNd' t ht).const_mul (M / η) using 1
      field_simp
      ring) (by rw [h0])
  simp only [sub_zero, akG] at h
  exact h

/-- AKMM, p. 392 and App. 13.A.10, p. 861: **machine use**. For the same `L_y > 0`,
`x^{DE}/x^{SP} = ((A(1−φ)/ψ)^{1/φ}L_y)/((A/ψ)^{1/φ}L_y) = (1−φ)^{1/φ} < 1`, so
`x^{SP}/x^{DE} = (1−φ)^{−1/φ} > 1`. -/
theorem romer_machine_ratio {A φ ψ Ly : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1)
    (hψ : 0 < ψ) (hLy : 0 < Ly) :
    romerXMon A φ ψ Ly / ((A / ψ) ^ (1 / φ) * Ly) = (1 - φ) ^ (1 / φ) ∧
      (1 - φ) ^ (1 / φ) < 1 ∧ 1 < (1 - φ) ^ (-(1 / φ)) := by
  have h1φ : 0 < 1 - φ := by linarith
  have hlt : (1 - φ) ^ (1 / φ) < 1 := Real.rpow_lt_one h1φ.le (by linarith) (by positivity)
  refine ⟨?_, hlt, ?_⟩
  · unfold romerXMon romerX
    rw [show A * (1 - φ) / ψ = (1 - φ) * (A / ψ) by ring, Real.mul_rpow h1φ.le (by positivity)]
    have : 0 < (A / ψ) ^ (1 / φ) := by positivity
    field_simp
  · rw [Real.rpow_neg h1φ.le]
    exact one_lt_inv_iff₀.mpr ⟨by positivity, hlt⟩

/-- AKMM, p. 392: **the printed factor is wrong**: for `0 < φ < 1`,
`(1−φ)^φ ≠ (1−φ)^{1/φ}`, so machine use is not "too low by a factor of `(1−φ)^φ`". -/
theorem romer_machine_ratio_printed_false {φ : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < 1) :
    (1 - φ) ^ φ ≠ (1 - φ) ^ (1 / φ) := by
  have h1φ : 0 < 1 - φ := by linarith
  have hφ : φ < 1 / φ := by
    rw [lt_div_iff₀ hφ0]; nlinarith
  exact (Real.rpow_lt_rpow_of_exponent_gt h1φ (by linarith) hφ).ne'

/-- AKMM, p. 392: **the machine subsidy**. With final producers paying `(1 − τ)p` (`τ < 1`), the
inverse demand facing a monopolist is `AL_y^φx^{−φ}/(1 − τ)`, so its quantity is
`x(τ) = ((A/(1−τ))(1−φ)/ψ)^{1/φ}L_y` (by `eq_13_33`). Then `x(τ) = x^{SP}` iff `τ = φ`, i.e.
`1 − τ = 1 − φ`; and the printed choice `1 − τ = (1−φ)^{−1}` gives `x(τ) < x^{DE}`. -/
theorem romer_subsidy {A φ ψ Ly τ : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1) (hψ : 0 < ψ)
    (hLy : 0 < Ly) (hτ : τ < 1) :
    (romerXMon (A / (1 - τ)) φ ψ Ly = (A / ψ) ^ (1 / φ) * Ly ↔ τ = φ) ∧
      (1 - τ = 1 / (1 - φ) → romerXMon (A / (1 - τ)) φ ψ Ly < romerXMon A φ ψ Ly) := by
  have h1φ : 0 < 1 - φ := by linarith
  have h1τ : 0 < 1 - τ := by linarith
  have hφinv : 0 < 1 / φ := by positivity
  unfold romerXMon romerX
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
  · have h2 := mul_right_cancel₀ hLy.ne' h
    have h3 := congrArg (fun x : ℝ => x ^ φ) h2
    rw [← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity),
      one_div_mul_cancel hφ0.ne', Real.rpow_one, Real.rpow_one] at h3
    field_simp at h3
    nlinarith [h3]
  · rw [h]
    congr 2
    field_simp
  · rw [h]
    apply mul_lt_mul_of_pos_right _ hLy
    apply Real.rpow_lt_rpow (by positivity) _ hφinv
    rw [show A / (1 / (1 - φ)) * (1 - φ) / ψ = (1 - φ) * (A * (1 - φ) / ψ) by field_simp]
    have : 0 < A * (1 - φ) / ψ := by positivity
    nlinarith

/-- AKMM, p. 392: **the subsidy does not restore efficiency**. With the subsidy `τ = φ` the
monopolist's quantity is `x^{SP}`, profits are `φ(A/(1−φ))(A/ψ)^{(1−φ)/φ}L_y` and free entry gives
`V = (φA/(η(1−φ)))(A/ψ)^{(1−φ)/φ}`, so `r = π/V = ηL_y`: this is `r = η(1−φ)θL_y` with
`θ = 1/(1−φ)`, and the balanced growth rate of `romer_theta_growth_mono` is
`(ηL − ρ)/(1 + σ)`, strictly below `g^{SP} = (ηL − ρ)/σ` when `ηL > ρ`. -/
theorem romer_subsidy_not_efficient {φ η σ ρ L : ℝ} (hφ1 : φ < 1) (hσ : 0 < σ)
    (hpos : ρ < η * L) :
    ((1 - φ) * (1 / (1 - φ)) * η * L - ρ) / ((1 - φ) * (1 / (1 - φ)) + σ) =
        (η * L - ρ) / (1 + σ) ∧ (η * L - ρ) / (1 + σ) < (η * L - ρ) / σ := by
  have h1φ : (1 - φ) ≠ 0 := by linarith
  refine ⟨by field_simp, div_lt_div_of_pos_left (by linarith) hσ (by linarith)⟩

/-- AKMM, p. 392: **decentralised growth is too low**. If `0 < φ < 1`, `σ > 0` and `ηL > ρ`,
`g^{DE} = ((1−φ)ηL − ρ)/(1 − φ + σ) < g^{SP} = (ηL − ρ)/σ`. -/
theorem romer_planner_growth_gt {φ η σ ρ L : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < 1) (hσ : 0 < σ)
    (hη : 0 < η) (hL : 0 < L) (hpos : ρ < η * L) :
    ((1 - φ) * η * L - ρ) / (1 - φ + σ) < (η * L - ρ) / σ := by
  have h : 0 < 1 - φ + σ := by linarith
  rw [div_lt_div_iff₀ h hσ]
  have : 0 < (1 - φ) * (η * L - ρ) + σ * φ * η * L := by
    have : 0 < η * L - ρ := by linarith
    positivity
  nlinarith

end AKMM.Growth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Semi-endogenous growth

AKMM, §13.5.1, "Less than proportional knowledge spillovers" (pp. 393–394), footnote 36, and
Appendix 13.A.7 (pp. 854–855): Jones (1995), with `Ṅ = ηN^εL_r` (13.53), `ε < 1`, and labour
`L(t) = Le^{nt}`.

* (13.54): with profits growing at `n`, `V = π/(r* − n)` is the unique solution of the HJB
  equation without a bubble (`eq_13_54`, `jones_value_unique`).
* (13.55): free entry `V = w/(ηN^ε)` is `L_y/(r* − n) = N^{1−ε}/(η(1−φ))` (`eq_13_55`).
* (13.56): (13.55) holds for all `t` iff `Ṅ/N = n/(1−ε)` (`eq_13_56`, `eq_13_56_converse`).
* `r* = ρ + σn/(1−ε)` and the TVC (`jones_r_star`).
* (13.59): the balanced-growth `N(t)` is unique, `N = (η(1−ε)L_r/n)^{1/(1−ε)}`
  (`eq_13_59`, `jones_N_unique`).
* (13.60): output per production worker, and the level effect of scale and research intensity
  (`eq_13_60`, `jones_level_effect`); with `n = 0` growth is zero (`jones_no_growth`).
* The planner (13.A.22)–(13.A.25): the costate equation (13.A.24) is the derivative of the
  Hamiltonian (`eq_13_A_24`); the growth of `λ` (`jones_planner_lambda_growth`); balanced
  growth forces `Ṅ/N = n/(1−ε)` (`jones_planner_bgp`), which needs (13.A.24) as well as
  (13.A.25) (`jones_planner_A25_alone_insufficient`).
-/

namespace AKMM.Growth

open Real Filter Topology

/-- AKMM, (13.54), p. 393: with profits `π(t) = π_0e^{nt}` and a constant interest rate `r`,
`V(t) = π_0e^{nt}/(r − n)` satisfies the HJB equation `rV = π + V̇` (p. 388). -/
theorem eq_13_54 {r n π0 t : ℝ} (hrn : r ≠ n) :
    HasDerivAt (fun s => π0 * Real.exp (n * s) / (r - n))
      (r * (π0 * Real.exp (n * t) / (r - n)) - π0 * Real.exp (n * t)) t := by
  have h := (((hasDerivAt_id' t).const_mul n).exp.const_mul π0).div_const (r - n)
  convert h using 1
  have : r - n ≠ 0 := sub_ne_zero.mpr hrn
  field_simp
  ring

/-- AKMM, (13.27) and (13.54), p. 393: **no bubble**. If `r > n` and `V` solves
`V̇ = rV − π_0e^{nt}` on `[0, ∞)` with `e^{−rT}V(T) → 0`, then `V(t) = π_0e^{nt}/(r − n)`. -/
theorem jones_value_unique {r n π0 : ℝ} {V : ℝ → ℝ} (hrn : n < r)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (r * V t - π0 * Real.exp (n * t)) t)
    (hnb : Tendsto (fun T => Real.exp (-r * T) * V T) atTop (𝓝 0)) :
    ∀ t, 0 ≤ t → V t = π0 * Real.exp (n * t) / (r - n) := by
  have hrn' : r - n ≠ 0 := (sub_pos.mpr hrn).ne'
  set f := fun s => (V s - π0 * Real.exp (n * s) / (r - n)) * Real.exp (-r * s)
  have hf : ∀ s, 0 ≤ s → HasDerivAt f 0 s := fun s hs => by
    have h1 := ((hV s hs).fun_sub (eq_13_54 (π0 := π0) (t := s) hrn.ne')).fun_mul
      ((hasDerivAt_id' s).const_mul (-r)).exp
    convert h1 using 1
    ring
  have hconst : ∀ t, 0 ≤ t → f t = f 0 := fun t ht =>
    constant_of_has_deriv_right_zero (f := f) (a := 0) (b := t)
      (fun s hs => (hf s hs.1).continuousAt.continuousWithinAt)
      (fun s hs => (hf s hs.1).hasDerivWithinAt) t (Set.right_mem_Icc.mpr ht)
  have hlim : Tendsto f atTop (𝓝 0) := by
    have h2 : Tendsto (fun T => π0 / (r - n) * Real.exp (-(r - n) * T)) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (sub_pos.mpr hrn))).const_mul (π0 / (r - n))
      rw [mul_zero] at this
      refine this.congr fun T => ?_
      simp only [Function.comp_apply, id]
      ring_nf
    have := hnb.sub h2
    rw [sub_zero] at this
    refine this.congr fun T => ?_
    simp only [f]
    have : Real.exp (n * T) * Real.exp (-r * T) = Real.exp (-(r - n) * T) := by
      rw [← Real.exp_add]; ring_nf
    rw [← this]
    field_simp
  have hf0 : f 0 = 0 := by
    have hev : ∀ᶠ T in atTop, f T = f 0 := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT using hconst T hT
    exact tendsto_nhds_unique (tendsto_const_nhds.congr' (EventuallyEq.symm hev)) hlim
  intro t ht
  have h := (hconst t ht).trans hf0
  simp only [f] at h
  rcases mul_eq_zero.mp h with h | h
  · linarith
  · exact absurd h (Real.exp_pos _).ne'

/-- AKMM, (13.55), p. 393: **free entry**. With `V = φAX^{1/φ−1}L_y/(r* − n)` (13.54) and
`w = φ(A/(1−φ))X^{(1−φ)/φ}N` (13.36), `V = w/(ηN^ε)` iff
`L_y/(r* − n) = N^{1−ε}/(η(1−φ))`. -/
theorem eq_13_55 {A φ ψ η ε r n Ly N : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1)
    (hψ : 0 < ψ) (hη : 0 < η) (hN : 0 < N) (hrn : n < r) :
    φ * A * romerX A φ ψ ^ (1 / φ - 1) * Ly / (r - n) =
        φ * (A / (1 - φ)) * romerX A φ ψ ^ ((1 - φ) / φ) * N / (η * N ^ ε) ↔
      Ly / (r - n) = N ^ (1 - ε) / (η * (1 - φ)) := by
  have h1φ : 0 < 1 - φ := by linarith
  have hX : 0 < romerX A φ ψ := by unfold romerX; positivity
  have hrn' : 0 < r - n := sub_pos.mpr hrn
  rw [show 1 / φ - 1 = (1 - φ) / φ by field_simp]
  set P := φ * A * romerX A φ ψ ^ ((1 - φ) / φ)
  have hP : 0 < P := by positivity
  have hN1 : N ^ (1 - ε) = N / N ^ ε := by
    rw [Real.rpow_sub hN, Real.rpow_one]
  rw [hN1]
  have hNe : 0 < N ^ ε := by positivity
  rw [show φ * (A / (1 - φ)) * romerX A φ ψ ^ ((1 - φ) / φ) * N / (η * N ^ ε) =
    P * (N / N ^ ε / (η * (1 - φ))) by simp only [P]; field_simp,
    show P * Ly / (r - n) = P * (Ly / (r - n)) by ring]
  exact ⟨fun h => mul_left_cancel₀ hP.ne' h, fun h => by rw [h]⟩

/-- AKMM, (13.56), p. 393: **(13.55) for all `t` forces `Ṅ/N = n/(1−ε)`**. If
`L_y(t) = L_{y0}e^{nt}`, `N > 0` is differentiable at `t` and (13.55) holds at every date,
then `Ṅ(t)/N(t) = n/(1−ε)`. -/
theorem eq_13_56 {φ η ε r n Ly0 t Ndot : ℝ} {N : ℝ → ℝ} (hφ1 : φ < 1) (hη : 0 < η)
    (hε : ε < 1) (hrn : n < r) (hLy0 : 0 < Ly0) (hN : ∀ s, 0 < N s)
    (hNd : HasDerivAt N Ndot t)
    (h1355 : ∀ s, Ly0 * Real.exp (n * s) / (r - n) = N s ^ (1 - ε) / (η * (1 - φ))) :
    Ndot / N t = n / (1 - ε) := by
  have h1φ : 0 < 1 - φ := by linarith
  have h1ε : 0 < 1 - ε := by linarith
  have hrn' : 0 < r - n := sub_pos.mpr hrn
  set κ := η * (1 - φ) * Ly0 / (r - n)
  have hκ : 0 < κ := by positivity
  have hNform : N = fun s => κ ^ (1 / (1 - ε)) * Real.exp (n / (1 - ε) * s) := by
    funext s
    have h1 := h1355 s
    have hpow : N s ^ (1 - ε) = κ * Real.exp (n * s) := by
      simp only [κ]; field_simp at h1 ⊢; linarith
    have := congrArg (fun x : ℝ => x ^ (1 / (1 - ε))) hpow
    rw [← Real.rpow_mul (hN s).le, mul_one_div_cancel h1ε.ne', Real.rpow_one,
      Real.mul_rpow hκ.le (Real.exp_pos _).le, ← Real.exp_mul] at this
    rw [this]
    congr 2
    ring
  have hd : HasDerivAt N (n / (1 - ε) * N t) t := by
    rw [hNform]
    have := ((hasDerivAt_id' t).const_mul (n / (1 - ε))).exp.const_mul (κ ^ (1 / (1 - ε)))
    convert this using 1
    ring
  rw [hNd.unique hd]
  field_simp [(hN t).ne']

/-- AKMM, (13.56), p. 393, converse: if `N` grows at `n/(1−ε)` and (13.55) holds at `t = 0`,
it holds at every date (with `L_y(t) = L_{y0}e^{nt}`). -/
theorem eq_13_56_converse {φ η ε r n Ly0 N0 : ℝ} (hε : ε < 1) (hN0 : 0 < N0)
    (h0 : Ly0 / (r - n) = N0 ^ (1 - ε) / (η * (1 - φ))) (s : ℝ) :
    Ly0 * Real.exp (n * s) / (r - n) =
      (N0 * Real.exp (n / (1 - ε) * s)) ^ (1 - ε) / (η * (1 - φ)) := by
  have h1ε : (1 - ε) ≠ 0 := by linarith
  rw [Real.mul_rpow hN0.le (Real.exp_pos _).le, ← Real.exp_mul,
    show n / (1 - ε) * s * (1 - ε) = n * s by field_simp]
  rw [show Ly0 * Real.exp (n * s) / (r - n) = Ly0 / (r - n) * Real.exp (n * s) by ring, h0]
  ring

/-- AKMM, p. 393: the interest rate `r* = ρ + σn/(1−ε)` from the Euler equation, and the TVC:
if `ρ − n > n/(1−ε)` and `σ > 0` then `r* − n > n/(1−ε) ≥ 0` (for `n ≥ 0`), so household wealth,
which grows at `n/(1−ε)` per capita, satisfies `e^{−(r*−n)T}a(T) → 0`. -/
theorem jones_r_star {σ ρ n ε a0 : ℝ} (hσ : 0 < σ) (hε : ε < 1) (hn : 0 ≤ n)
    (hbound : n / (1 - ε) < ρ - n) (ha0 : 0 < a0) :
    n / (1 - ε) < ρ + σ * (n / (1 - ε)) - n ∧
      Tendsto (fun T => Real.exp (-(ρ + σ * (n / (1 - ε)) - n) * T) *
        (a0 * Real.exp (n / (1 - ε) * T))) atTop (𝓝 0) := by
  have h1ε : 0 < 1 - ε := by linarith
  have hg : 0 ≤ n / (1 - ε) := div_nonneg hn h1ε.le
  have hlt : n / (1 - ε) < ρ + σ * (n / (1 - ε)) - n := by nlinarith
  refine ⟨hlt, ?_⟩
  have e : ∀ T, Real.exp (-(ρ + σ * (n / (1 - ε)) - n) * T) * (a0 * Real.exp (n / (1 - ε) * T)) =
      a0 * Real.exp ((n / (1 - ε) - (ρ + σ * (n / (1 - ε)) - n)) * T) := fun T => by
    rw [mul_left_comm, ← Real.exp_add]; ring_nf
  simp only [e]
  exact (istc_exp_tendsto_zero_iff ha0).mpr (by linarith)

/-- AKMM, (13.59), p. 394: on the balanced growth path, `Ṅ/N = ηN^{ε−1}L_r = n/(1−ε)` gives
`L_r = nN^{1−ε}/(η(1−ε))`, i.e. `N = (η(1−ε)L_r/n)^{1/(1−ε)}`. -/
theorem eq_13_59 {η ε n N Lr : ℝ} (hη : 0 < η) (hε : ε < 1) (hn : 0 < n) (hN : 0 < N)
    (h : η * N ^ (ε - 1) * Lr = n / (1 - ε)) :
    Lr = n * N ^ (1 - ε) / (η * (1 - ε)) ∧ N = (η * (1 - ε) * Lr / n) ^ (1 / (1 - ε)) := by
  have h1ε : 0 < 1 - ε := by linarith
  have hNe : N ^ (ε - 1) * N ^ (1 - ε) = 1 := by
    rw [← Real.rpow_add hN, show ε - 1 + (1 - ε) = 0 by ring, Real.rpow_zero]
  have hLr : Lr = n * N ^ (1 - ε) / (η * (1 - ε)) := by
    have hp : 0 < N ^ (1 - ε) := by positivity
    field_simp
    have := congrArg (· * N ^ (1 - ε)) h
    rw [show η * N ^ (ε - 1) * Lr * N ^ (1 - ε) = η * Lr * (N ^ (ε - 1) * N ^ (1 - ε)) by ring,
      hNe] at this
    field_simp at this
    linarith
  refine ⟨hLr, ?_⟩
  rw [hLr, show η * (1 - ε) * (n * N ^ (1 - ε) / (η * (1 - ε))) / n = N ^ (1 - ε) by
    field_simp, ← Real.rpow_mul hN.le, mul_one_div_cancel h1ε.ne', Real.rpow_one]

/-- AKMM, (13.59) with (13.55), p. 394: **the balanced-growth `N(t)` is unique**. With
labour-market clearing `L_y + L_r = Le^{nt}`, (13.55) and (13.59) give
`N(t)^{1−ε} = ηLe^{nt}/(n/(1−ε) + (r* − n)/(1−φ))`. -/
theorem jones_N_unique {φ η ε r n L t N Ly Lr : ℝ} (hφ1 : φ < 1) (hη : 0 < η) (hε : ε < 1)
    (hn : 0 < n) (hrn : n < r)
    (h1355 : Ly / (r - n) = N ^ (1 - ε) / (η * (1 - φ)))
    (h1359 : Lr = n * N ^ (1 - ε) / (η * (1 - ε)))
    (hclear : Ly + Lr = L * Real.exp (n * t)) :
    N ^ (1 - ε) = η * L * Real.exp (n * t) / (n / (1 - ε) + (r - n) / (1 - φ)) := by
  have h1φ : 0 < 1 - φ := by linarith
  have h1ε : 0 < 1 - ε := by linarith
  have hrn' : 0 < r - n := sub_pos.mpr hrn
  have hden : 0 < n / (1 - ε) + (r - n) / (1 - φ) := by positivity
  rw [eq_div_iff hden.ne']
  have hLy : Ly = (r - n) * N ^ (1 - ε) / (η * (1 - φ)) := by
    field_simp at h1355 ⊢; linarith
  rw [mul_assoc η, ← hclear, hLy, h1359]
  field_simp
  ring

/-- AKMM, (13.60), p. 394: with `N = (η(1−ε)L_r/n)^{1/(1−ε)}` in (13.35), output per production
worker is `Y/L_y = 𝒜(L_r/L)^{1/(1−ε)}L^{1/(1−ε)}` with the constant
`𝒜 = (A/(1−φ))X^{(1−φ)/φ}(η(1−ε)/n)^{1/(1−ε)}`. -/
theorem eq_13_60 {A φ ψ η ε n Lr L : ℝ} (hη : 0 < η) (hε : ε < 1) (hn : 0 < n) (hLr : 0 ≤ Lr)
    (hL : 0 < L) :
    A / (1 - φ) * romerX A φ ψ ^ ((1 - φ) / φ) * (η * (1 - ε) * Lr / n) ^ (1 / (1 - ε)) =
      A / (1 - φ) * romerX A φ ψ ^ ((1 - φ) / φ) * (η * (1 - ε) / n) ^ (1 / (1 - ε)) *
        ((Lr / L) ^ (1 / (1 - ε)) * L ^ (1 / (1 - ε))) := by
  have h1ε : 0 < 1 - ε := by linarith
  rw [← Real.mul_rpow (div_nonneg hLr hL.le) hL.le, div_mul_cancel₀ _ hL.ne',
    mul_assoc (A / (1 - φ) * romerX A φ ψ ^ ((1 - φ) / φ)),
    ← Real.mul_rpow (by positivity) hLr]
  congr 2
  ring

/-- AKMM, p. 394: **level effects**. For a given research intensity `L_r/L > 0`, output per
production worker `𝒜(L_r/L)^{1/(1−ε)}L^{1/(1−ε)}` (with `𝒜 > 0`) is strictly increasing in the
scale `L > 0`, and for given `L` strictly increasing in the research intensity. -/
theorem jones_level_effect {𝒜 ε s : ℝ} (h𝒜 : 0 < 𝒜) (hε : ε < 1) (hs : 0 < s) :
    StrictMonoOn (fun L : ℝ => 𝒜 * (s ^ (1 / (1 - ε)) * L ^ (1 / (1 - ε)))) (Set.Ioi 0) ∧
      ∀ L : ℝ, 0 < L →
        StrictMonoOn (fun s' : ℝ => 𝒜 * (s' ^ (1 / (1 - ε)) * L ^ (1 / (1 - ε)))) (Set.Ioi 0) := by
  have h1ε : 0 < 1 / (1 - ε) := by apply div_pos one_pos; linarith
  refine ⟨fun a ha b _ hab => ?_, fun L hL a ha b _ hab => ?_⟩
  · have := Real.rpow_lt_rpow (le_of_lt ha) hab h1ε
    have hsp : 0 < s ^ (1 / (1 - ε)) := by positivity
    simp only
    exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left this hsp) h𝒜
  · have := Real.rpow_lt_rpow (le_of_lt ha) hab h1ε
    have hLp : 0 < L ^ (1 / (1 - ε)) := by positivity
    simp only
    exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right this hLp) h𝒜

/-- AKMM, p. 394: without population growth there is no sustained growth: `n/(1−ε) = 0` when
`n = 0`; and the growth rate rises with the spillover `ε` when `n > 0`. -/
theorem jones_no_growth {ε : ℝ} : (0 : ℝ) / (1 - ε) = 0 ∧
    ∀ n : ℝ, 0 < n → StrictMonoOn (fun e : ℝ => n / (1 - e)) (Set.Iio 1) := by
  refine ⟨zero_div _, fun n hn a ha b hb hab => ?_⟩
  simp only [Set.mem_Iio] at ha hb
  exact div_lt_div_of_pos_left hn (by linarith) (by linarith)

/-- AKMM, (13.A.24), p. 854: the derivative in `N` of the bracket of the Hamiltonian
(13.A.22), `N^εLe^{nt} − cN^{−1}N^{ε}/M`, i.e. `N^εLe^{nt} − cN^{ε−1}/M`, is
`εN^{ε−1}Le^{nt} + (1−ε)cN^{ε−2}/M`. -/
theorem eq_13_A_24 {ε L n t c M N : ℝ} (hN : 0 < N) :
    HasDerivAt (fun y => y ^ ε * (L * Real.exp (n * t)) - c * y ^ (ε - 1) / M)
      (ε * N ^ (ε - 1) * (L * Real.exp (n * t)) + (1 - ε) * c * N ^ (ε - 2) / M) N := by
  have h1 := (Real.hasDerivAt_rpow_const (p := ε) (Or.inl hN.ne')).mul_const
    (L * Real.exp (n * t))
  have h2 := ((Real.hasDerivAt_rpow_const (p := ε - 1) (Or.inl hN.ne')).const_mul c).div_const M
  convert h1.sub h2 using 1
  rw [show ε - 1 - 1 = ε - 2 by ring]
  ring

/-- AKMM, (13.A.23), p. 855: if `λ = e^{−(ρ−n)t}c^{−σ}N^{1−ε}K` (`K = (ψ/η)(A/ψ)^{1/φ}φ/(1−φ)`),
then `λ̇/λ = −σċ/c + (1−ε)Ṅ/N − (ρ − n)`. -/
theorem jones_planner_lambda_growth {σ ρ n ε K t cdot Ndot : ℝ} {c N : ℝ → ℝ} (hc : 0 < c t)
    (hN : 0 < N t) (hcd : HasDerivAt c cdot t) (hNd : HasDerivAt N Ndot t) :
    HasDerivAt (fun s => Real.exp (-(ρ - n) * s) * c s ^ (-σ) * N s ^ (1 - ε) * K)
      ((-σ * (cdot / c t) + (1 - ε) * (Ndot / N t) - (ρ - n)) *
        (Real.exp (-(ρ - n) * t) * c t ^ (-σ) * N t ^ (1 - ε) * K)) t := by
  have h1 := ((hasDerivAt_id' t).const_mul (-(ρ - n))).exp
  have h2 := hcd.rpow_const (p := -σ) (Or.inl hc.ne')
  have h3 := hNd.rpow_const (p := 1 - ε) (Or.inl hN.ne')
  convert ((h1.fun_mul h2).fun_mul h3).mul_const K using 1
  rw [Real.rpow_sub_one hc.ne', Real.rpow_sub_one hN.ne']
  field_simp
  ring

/-- AKMM, App. 13.A.7, p. 855: **planner's balanced growth**. Along `N = N_0e^{gt}`, if the
growth rate of `N` from (13.A.25), `ηN^{ε−1}Le^{nt} − ηcN^{ε−2}/M`, and the bracket of (13.A.24),
`εN^{ε−1}Le^{nt} + (1−ε)cN^{ε−2}/M`, are both constant in `t`, then `N^{ε−1}Le^{nt}` is constant
and `g = n/(1−ε)`. -/
theorem jones_planner_bgp {η ε n L M N0 g k1 k2 : ℝ} {c : ℝ → ℝ} (hη : 0 < η) (hε : ε < 1)
    (hL : 0 < L) (hN0 : 0 < N0)
    (h25 : ∀ t, η * (N0 * Real.exp (g * t)) ^ (ε - 1) * L * Real.exp (n * t) -
      η * c t * (N0 * Real.exp (g * t)) ^ (ε - 2) / M = k1)
    (h24 : ∀ t, ε * (N0 * Real.exp (g * t)) ^ (ε - 1) * L * Real.exp (n * t) +
      (1 - ε) * c t * (N0 * Real.exp (g * t)) ^ (ε - 2) / M = k2) :
    g = n / (1 - ε) := by
  have h1ε : 0 < 1 - ε := by linarith
  have hu : ∀ t, (N0 * Real.exp (g * t)) ^ (ε - 1) * L * Real.exp (n * t) =
      ((1 - ε) * k1 / η + k2) := fun t => by
    have a := h25 t
    have b := h24 t
    have hab : (N0 * Real.exp (g * t)) ^ (ε - 1) * L * Real.exp (n * t) -
        c t * (N0 * Real.exp (g * t)) ^ (ε - 2) / M = k1 / η := by
      rw [eq_div_iff hη.ne']; linear_combination a
    linear_combination (1 - ε) * hab + b
  have hform : ∀ t, (N0 * Real.exp (g * t)) ^ (ε - 1) * L * Real.exp (n * t) =
      N0 ^ (ε - 1) * L * Real.exp (((ε - 1) * g + n) * t) := fun t => by
    rw [Real.mul_rpow hN0.le (Real.exp_pos _).le, ← Real.exp_mul]
    have : Real.exp (g * t * (ε - 1)) * Real.exp (n * t) = Real.exp (((ε - 1) * g + n) * t) := by
      rw [← Real.exp_add]; ring_nf
    rw [← this]; ring
  have h0 := hu 0
  have h1 := hu 1
  rw [hform] at h0 h1
  simp only [mul_zero, Real.exp_zero, mul_one] at h0 h1
  have hc : 0 < N0 ^ (ε - 1) * L := by positivity
  have he : Real.exp ((ε - 1) * g + n) = 1 := by
    have : N0 ^ (ε - 1) * L * Real.exp ((ε - 1) * g + n) = N0 ^ (ε - 1) * L * 1 := by
      linarith
    exact mul_left_cancel₀ hc.ne' this
  have := Real.exp_eq_one_iff _ |>.mp he
  field_simp
  linarith

/-- AKMM, App. 13.A.7, p. 855: **(13.A.25) alone does not force `N^{ε−1}Le^{nt}` constant**.
With `n > 0`, `N ≡ N_0` and `c(t) = MN_0Le^{nt}`, the law of motion (13.A.25)
`Ṅ = ηN^ε(Le^{nt} − cN^{−1}/M)` holds (both sides are `0`) and `Ṅ/N`, `ċ/c` are constant, yet
`N^{ε−1}Le^{nt}` is not constant; it is (13.A.24) that rules this out. -/
theorem jones_planner_A25_alone_insufficient {η ε n L M N0 : ℝ} (hn : 0 < n) (hL : 0 < L)
    (hM : 0 < M) (hN0 : 0 < N0) :
    (∀ t, (0 : ℝ) = η * N0 ^ ε * (L * Real.exp (n * t) -
      M * N0 * L * Real.exp (n * t) * N0⁻¹ / M)) ∧
    N0 ^ (ε - 1) * L * Real.exp (n * 0) ≠ N0 ^ (ε - 1) * L * Real.exp (n * 1) := by
  refine ⟨fun t => by field_simp; ring, fun h => ?_⟩
  have hc : 0 < N0 ^ (ε - 1) * L := by positivity
  have := mul_left_cancel₀ hc.ne' h
  simp only [mul_zero, Real.exp_zero, mul_one] at this
  have := (Real.exp_eq_one_iff n).mp this.symm
  linarith

end AKMM.Growth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Quality ladders and creative destruction

AKMM, §13.5.2 (pp. 398–404) and Appendix 13.A.9 (p. 861): Aghion and Howitt (1992) in a
lab-equipment version. Write `X = A(1−φ)/ψ` and `π̄ = φAX^{(1−φ)/φ}L`, the flow profit per
unit of quality.

* Final goods: (13.62)–(13.63) (`eq_13_62`, `eq_13_63`).
* Monopoly: the quantity `X^{1/φ}L` (independent of `q`), the price `ψq/(1−φ)` and profit
  (13.65) `π̄q` (`eq_13_65`); aggregates `Y` and `X(t)` in terms of `Q` (`quality_aggregates`).
* Drastic and incremental innovation: (13.A.26), (13.64), and limit pricing (13.A.27)
  (`eq_13_A_26`, `eq_13_64`, `eq_13_A_27`).
* Research: free entry `V/q = 1/(λη)` and the Arrow replacement effect
  (`quality_research_foc`, `quality_arrow_replacement`).
* The leader's value with creative destruction at rate `z`: `V = π̄q/(r + z)`
  (`quality_value`).
* The aggregate quality index is *defined* by its mean-field ODE `Q̇ = (λ−1)zQ`; for one ladder
  with Poisson arrivals, `E[q(t)] = q_0e^{(λ−1)zt}` (`quality_single_ladder`).
* The balanced growth path (13.66) (`eq_13_66`) and its comparative statics
  (`quality_comparative_statics`, `quality_growth_mono_lambda`, `quality_growth_anti_psi`).
-/

namespace AKMM.Growth

open Real Filter Topology

/-- AKMM, p. 400: flow profit per unit of quality, `π̄ = φAX^{(1−φ)/φ}L`. -/
noncomputable def qlPiBar (A φ ψ L : ℝ) : ℝ := φ * A * romerX A φ ψ ^ ((1 - φ) / φ) * L

/-- AKMM, (13.62), p. 400: the wage is the marginal product of labour, `w = φY/L`. -/
theorem eq_13_62 {A φ S L : ℝ} (hL : 0 < L) :
    HasDerivAt (fun l => A / (1 - φ) * l ^ φ * S) (φ * (A / (1 - φ) * L ^ φ * S) / L) L :=
  eq_13_23 hL

/-- AKMM, (13.63), p. 400: the first-order condition `AL^φqx^{−φ} = p` for `x > 0`, `p > 0`,
`A, q > 0`, is solved exactly by `x = (Aq/p)^{1/φ}L`. -/
theorem eq_13_63 {A φ q p L x : ℝ} (hφ0 : 0 < φ) (hA : 0 < A) (hq : 0 < q) (hp : 0 < p)
    (hL : 0 < L) (hx : 0 < x) :
    A * L ^ φ * q * x ^ (-φ) = p ↔ x = (A * q / p) ^ (1 / φ) * L := by
  have hAqp : 0 < A * q / p := by positivity
  constructor
  · intro h
    have e : x ^ φ = A * q / p * L ^ φ := by
      rw [Real.rpow_neg hx.le] at h
      have hxφ : 0 < x ^ φ := by positivity
      field_simp at h ⊢
      linarith
    have := congrArg (fun y : ℝ => y ^ (1 / φ)) e
    rw [← Real.rpow_mul hx.le, mul_one_div_cancel hφ0.ne', Real.rpow_one,
      Real.mul_rpow hAqp.le (by positivity), ← Real.rpow_mul hL.le,
      mul_one_div_cancel hφ0.ne', Real.rpow_one] at this
    exact this
  · intro h
    rw [h, Real.mul_rpow (by positivity) hL.le, ← Real.rpow_mul hAqp.le,
      show 1 / φ * -φ = -1 by field_simp, Real.rpow_neg_one, Real.rpow_neg hL.le]
    field_simp

/-- AKMM, (13.65), p. 400: **the quality-ladder monopolist**. Facing (13.63), the leader's
profit `AL^φqx^{1−φ} − ψqx` is maximised over `x ≥ 0` at `x = X^{1/φ}L` (independent of `q`),
where the price is `ψq/(1−φ)` and profit is `π̄q`. -/
theorem eq_13_65 {A φ ψ q L x : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1) (hψ : 0 < ψ)
    (hq : 0 < q) (hL : 0 < L) (hx : 0 ≤ x) :
    A * q * L ^ φ * x ^ (1 - φ) - ψ * q * x ≤
        A * q * L ^ φ * romerXMon A φ ψ L ^ (1 - φ) - ψ * q * romerXMon A φ ψ L ∧
      A * q * L ^ φ * romerXMon A φ ψ L ^ (-φ) = ψ * q / (1 - φ) ∧
      ψ * q / (1 - φ) * romerXMon A φ ψ L - ψ * q * romerXMon A φ ψ L = qlPiBar A φ ψ L * q := by
  have h1φ : 0 < 1 - φ := by linarith
  have hX : romerX (A * q) φ (ψ * q) = romerX A φ ψ := by unfold romerX; field_simp
  have hmon : romerXMon (A * q) φ (ψ * q) L = romerXMon A φ ψ L := by
    unfold romerXMon; rw [hX]
  have h := eq_13_33 (A := A * q) (ψ := ψ * q) (by positivity) hφ0 hφ1 (by positivity) hL hx
  rw [hmon] at h
  refine ⟨h.1, h.2, ?_⟩
  have hp := eq_13_34 (A := A) (Ly := L) hA hφ1 hψ (φ := φ)
  unfold qlPiBar
  rw [show 1 / φ - 1 = (1 - φ) / φ by field_simp] at hp
  rw [show ψ * q / (1 - φ) * romerXMon A φ ψ L - ψ * q * romerXMon A φ ψ L =
    q * (ψ / (1 - φ) * romerXMon A φ ψ L - ψ * romerXMon A φ ψ L) by ring, hp]
  ring

/-- AKMM, p. 401: **aggregates**. With every line at `x = X^{1/φ}L` and `Q = ∫q`, output is
`Y = (A/(1−φ))X^{(1−φ)/φ}QL` and intermediate spending is
`X(t) = ψQx = ψ^{1−1/φ}(A(1−φ))^{1/φ}QL`. -/
theorem quality_aggregates {A φ ψ Q L : ℝ} (hA : 0 < A) (hφ1 : φ < 1)
    (hψ : 0 < ψ) (hL : 0 < L) :
    A / (1 - φ) * L ^ φ * (Q * romerXMon A φ ψ L ^ (1 - φ)) =
        A / (1 - φ) * romerX A φ ψ ^ ((1 - φ) / φ) * Q * L ∧
      ψ * Q * romerXMon A φ ψ L = ψ ^ (1 - 1 / φ) * (A * (1 - φ)) ^ (1 / φ) * Q * L := by
  have h1φ : 0 < 1 - φ := by linarith
  have hX : 0 < romerX A φ ψ := by unfold romerX; positivity
  refine ⟨?_, ?_⟩
  · rw [eq_13_35 (N := Q) hL hX]; ring
  · unfold romerXMon romerX
    rw [Real.div_rpow (by positivity) hψ.le, Real.rpow_sub hψ, Real.rpow_one]
    ring

/-- AKMM, (13.A.26), p. 861: **limit pricing**. With quality-weighted perfect substitutes the
final producer buys the leader's version `v` (quality `λq'`) rather than the follower's
(quality `q'`, priced at marginal cost `ψq'`) iff
`p/(λq')^{1/(1−φ)} ≤ ψq'/q'^{1/(1−φ)}`, i.e. iff the markup `μ = p/(ψλq')` satisfies
`μ ≤ λ^{φ/(1−φ)}`. -/
theorem eq_13_A_26 {φ ψ lam q' p : ℝ} (hφ1 : φ < 1) (hψ : 0 < ψ) (hlam : 0 < lam)
    (hq' : 0 < q') :
    p / (lam * q') ^ (1 / (1 - φ)) ≤ ψ * q' / q' ^ (1 / (1 - φ)) ↔
      p / (ψ * (lam * q')) ≤ lam ^ (φ / (1 - φ)) := by
  have h1φ : 0 < 1 - φ := by linarith
  rw [Real.mul_rpow hlam.le hq'.le]
  have hq1 : 0 < q' ^ (1 / (1 - φ)) := by positivity
  have hl1 : 0 < lam ^ (1 / (1 - φ)) := by positivity
  have hlφ : lam ^ (1 / (1 - φ)) = lam * lam ^ (φ / (1 - φ)) := by
    rw [show 1 / (1 - φ) = φ / (1 - φ) + 1 by field_simp; ring, Real.rpow_add hlam,
      Real.rpow_one]; ring
  rw [div_le_div_iff₀ (by positivity) hq1, div_le_iff₀ (by positivity), hlφ]
  constructor <;> intro h <;> nlinarith [h, mul_pos hq1 (mul_pos hψ hq'),
    Real.rpow_pos_of_pos hlam (φ / (1 - φ))]

/-- AKMM, (13.64), p. 400, and App. 13.A.9: **the drastic-innovation condition**. The monopoly
markup `1/(1−φ)` is feasible under limit pricing, `1/(1−φ) ≤ λ^{φ/(1−φ)}`, iff
`λ ≥ (1/(1−φ))^{(1−φ)/φ}`. -/
theorem eq_13_64 {φ lam : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < 1) (hlam : 0 < lam) :
    1 / (1 - φ) ≤ lam ^ (φ / (1 - φ)) ↔ (1 / (1 - φ)) ^ ((1 - φ) / φ) ≤ lam := by
  have h1φ : 0 < 1 - φ := by linarith
  have hp : 0 < (1 - φ) / φ := by positivity
  have hinv : (lam ^ (φ / (1 - φ))) ^ ((1 - φ) / φ) = lam := by
    rw [← Real.rpow_mul hlam.le, show φ / (1 - φ) * ((1 - φ) / φ) = 1 by field_simp,
      Real.rpow_one]
  constructor
  · intro h
    have := Real.rpow_le_rpow (by positivity) h hp.le
    rwa [hinv] at this
  · intro h
    have := Real.rpow_le_rpow (by positivity) h (by positivity : (0 : ℝ) ≤ φ / (1 - φ))
    rwa [← Real.rpow_mul (by positivity), show (1 - φ) / φ * (φ / (1 - φ)) = 1 by field_simp,
      Real.rpow_one] at this

/-- The profit of a leader charging markup `μ` over marginal cost, up to a positive factor:
`(μ − 1)μ^{−1/φ}`. -/
noncomputable def qlMarkupProfit (φ μ : ℝ) : ℝ := (μ - 1) * μ ^ (-(1 / φ))

/-- AKMM, (13.A.27), p. 861: **profits and the markup**. With demand (13.63), profit at markup
`μ` is proportional to `(μ − 1)μ^{−1/φ}`, which is strictly increasing on `[1, 1/(1−φ)]` and
strictly decreasing on `[1/(1−φ), ∞)`. Hence under incremental innovation,
`λ^{φ/(1−φ)} < 1/(1−φ)`, the best feasible markup is the limit price `μ = λ^{φ/(1−φ)}`, and
under (13.64) it is the monopoly markup `1/(1−φ)`. -/
theorem eq_13_A_27 {φ : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < 1) :
    StrictMonoOn (qlMarkupProfit φ) (Set.Icc 1 (1 / (1 - φ))) ∧
      StrictAntiOn (qlMarkupProfit φ) (Set.Ici (1 / (1 - φ))) := by
  have h1φ : 0 < 1 - φ := by linarith
  have hd : ∀ μ, 0 < μ → HasDerivAt (qlMarkupProfit φ)
      (μ ^ (-(1 / φ) - 1) * ((1 - (1 - φ) * μ) / φ)) μ := fun μ hμ => by
    have h1 := ((hasDerivAt_id' μ).sub_const 1).mul
      (Real.hasDerivAt_rpow_const (p := -(1 / φ)) (Or.inl hμ.ne'))
    unfold qlMarkupProfit
    convert h1 using 1
    rw [Real.rpow_sub_one hμ.ne']
    field_simp
    ring
  have hcont : ∀ S : Set ℝ, S ⊆ Set.Ioi 0 → ContinuousOn (qlMarkupProfit φ) S := fun S hS μ hμ =>
    (hd μ (hS hμ)).continuousAt.continuousWithinAt
  have h1 : (1 : ℝ) ≤ 1 / (1 - φ) := by rw [le_div_iff₀ h1φ]; linarith
  refine ⟨strictMonoOn_of_deriv_pos (convex_Icc _ _) (hcont _ fun μ hμ => by
    simp only [Set.mem_Icc] at hμ; exact Set.mem_Ioi.mpr (by linarith)) fun μ hμ => ?_,
    strictAntiOn_of_deriv_neg (convex_Ici _) (hcont _ fun μ hμ => by
    simp only [Set.mem_Ici] at hμ; exact Set.mem_Ioi.mpr (by linarith)) fun μ hμ => ?_⟩
  · rw [interior_Icc] at hμ
    have hμ0 : 0 < μ := by linarith [hμ.1]
    rw [(hd μ hμ0).deriv]
    have : (1 - φ) * μ < 1 := by have := hμ.2; rw [lt_div_iff₀ h1φ] at this; linarith
    apply mul_pos (by positivity)
    exact div_pos (by linarith) hφ0
  · rw [interior_Ici] at hμ
    have hμ0 : 0 < μ := by simp only [Set.mem_Ioi] at hμ; linarith
    rw [(hd μ hμ0).deriv]
    have : 1 < (1 - φ) * μ := by
      simp only [Set.mem_Ioi] at hμ; rw [div_lt_iff₀ h1φ] at hμ; linarith
    apply mul_neg_of_pos_of_neg (by positivity)
    exact div_neg_of_neg_of_pos (by linarith) hφ0

/-- AKMM, p. 401: **the research first-order condition**. The research firm's objective
`(ηZ/q)λV − Z` is linear in `Z ≥ 0`; a positive `Z` is optimal iff `ηλV/q = 1`, and then the
ratio `V/q = 1/(λη)` is the same on every line. -/
theorem quality_research_foc {η lam V q Z : ℝ} (hZ : 0 < Z) :
    (∀ Z', 0 ≤ Z' → η * Z' / q * lam * V - Z' ≤ η * Z / q * lam * V - Z) ↔
      η / q * lam * V = 1 := by
  have key : ∀ Z', η * Z' / q * lam * V - Z' = Z' * (η / q * lam * V - 1) := fun Z' => by ring
  simp only [key]
  constructor
  · intro h
    have h0 := h 0 le_rfl
    have h2 := h (2 * Z) (by linarith)
    rw [zero_mul] at h0
    nlinarith
  · intro h Z' _
    rw [h]; simp

/-- AKMM, p. 401: free entry gives `V/q = 1/(λη)` (the first-order condition rearranged). -/
theorem quality_V_over_q {η lam V q : ℝ} (hη : 0 < η) (hlam : 0 < lam) (hq : 0 < q)
    (h : η / q * lam * V = 1) : V / q = 1 / (lam * η) := by
  field_simp at h ⊢; linarith

/-- AKMM, p. 401: **the Arrow replacement effect**. If entrants are indifferent,
`ηλV/q = 1`, with `V > 0`, then an incumbent improving its own product gains only
`(λ − 1)V`: `η(λ−1)V/q < ηλV/q = 1`, so its research objective `(ηZ/q)(λ−1)V − Z` is
uniquely maximised at `Z = 0`. -/
theorem quality_arrow_replacement {η lam V q : ℝ} (hη : 0 < η) (hq : 0 < q)
    (hV : 0 < V) (hfoc : η / q * lam * V = 1) :
    η / q * (lam - 1) * V < η / q * lam * V ∧
      ∀ Z, 0 < Z → η * Z / q * (lam - 1) * V - Z < 0 := by
  have hlt : η / q * (lam - 1) * V < η / q * lam * V := by
    have : 0 < η / q * V := by positivity
    nlinarith
  refine ⟨hlt, fun Z hZ => ?_⟩
  have e : η * Z / q * (lam - 1) * V - Z = Z * (η / q * (lam - 1) * V - 1) := by ring
  rw [e]
  exact mul_neg_of_pos_of_neg hZ (by linarith)

/-- AKMM, p. 402: **the leader's value**. With constant `r` and destruction rate `z`
(`r + z > 0`), the value `V` of a line of quality `q` solves `V̇ = (r + z)V − π̄q`; without a
bubble (`e^{−(r+z)T}V(T) → 0`) it is `V = π̄q/(r + z)`, so `V/q = π̄/(r + z)`. -/
theorem quality_value {r z πq : ℝ} {V : ℝ → ℝ} (hrz : 0 < r + z)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V ((r + z) * V t - πq) t)
    (hnb : Tendsto (fun T => Real.exp (-(r + z) * T) * V T) atTop (𝓝 0)) :
    ∀ t, 0 ≤ t → V t = πq / (r + z) := by
  have h := jones_value_unique (r := r + z) (n := 0) (π0 := πq) (V := V) hrz
    (fun t ht => by simpa using hV t ht) hnb
  intro t ht
  rw [h t ht]
  simp

/-- AKMM, p. 403: **one quality ladder**. If the number of steps by time `t` is Poisson with
mean `zt`, the expected quality `∑ₖ e^{−zt}(zt)^k/k! · q_0λ^k` is `q_0e^{(λ−1)zt}`, and it grows
at the rate `(λ − 1)z`, the mean-field law `Q̇ = (λ−1)zQ` used for the aggregate index. -/
theorem quality_single_ladder {z lam q0 t : ℝ} :
    ∑' k : ℕ, Real.exp (-(z * t)) * (z * t) ^ k / (k.factorial) * (q0 * lam ^ k) =
        q0 * Real.exp ((lam - 1) * z * t) ∧
      HasDerivAt (fun s => q0 * Real.exp ((lam - 1) * z * s))
        ((lam - 1) * z * (q0 * Real.exp ((lam - 1) * z * t))) t := by
  refine ⟨?_, ?_⟩
  · have hexp : Real.exp (lam * (z * t)) = ∑' k : ℕ, (lam * (z * t)) ^ k / (k.factorial) := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    have e : ∀ k : ℕ, Real.exp (-(z * t)) * (z * t) ^ k / (k.factorial) * (q0 * lam ^ k) =
        q0 * Real.exp (-(z * t)) * ((lam * (z * t)) ^ k / (k.factorial)) := fun k => by
      rw [mul_pow]; ring
    simp only [e]
    rw [tsum_mul_left, ← hexp, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  · have := (((hasDerivAt_id' t).const_mul ((lam - 1) * z)).exp).const_mul q0
    convert this using 1
    ring

/-- AKMM, (13.66), p. 403: **the balanced growth path**. If `r + z = ληπ̄` (free entry with
`V/q = π̄/(r + z)`), `r = σg + ρ` (Euler) and `g = (λ − 1)z` (the mean-field index), with
`λ > 1`, `σ > 0`, then `g = (ληπ̄ − ρ)/(σ + 1/(λ−1))`, `r = ρ + (ληπ̄ − ρ)/(1 + 1/(σ(λ−1)))`
and `z = (ληπ̄ − ρ)/(1 + (λ−1)σ)`. -/
theorem eq_13_66 {lam η πb σ ρ r z g : ℝ} (hlam : 1 < lam) (hσ : 0 < σ)
    (hfree : r + z = lam * η * πb) (heuler : r = σ * g + ρ) (hg : g = (lam - 1) * z) :
    g = (lam * η * πb - ρ) / (σ + 1 / (lam - 1)) ∧
      r = ρ + (lam * η * πb - ρ) / (1 + 1 / (σ * (lam - 1))) ∧
      z = (lam * η * πb - ρ) / (1 + (lam - 1) * σ) := by
  have hl : 0 < lam - 1 := by linarith
  have hz : z = (lam * η * πb - ρ) / (1 + (lam - 1) * σ) := by
    rw [eq_div_iff (by positivity)]
    rw [heuler, hg] at hfree
    linarith
  refine ⟨?_, ?_, hz⟩
  · rw [hg, hz]; field_simp; ring
  · rw [heuler, hg, hz]; field_simp; ring

/-- AKMM, p. 403: **comparative statics**. When `ληπ̄ > ρ` (positive growth), the growth rate
`g(η, π̄, ρ, σ) = (ληπ̄ − ρ)/(σ + 1/(λ−1))` is strictly increasing in `η` and in `π̄` (hence in
`L`, since `π̄ ∝ L`), strictly decreasing in `ρ`, and strictly decreasing in `σ > 0`. -/
theorem quality_comparative_statics {lam η πb σ ρ : ℝ} (hlam : 1 < lam) (hσ : 0 < σ)
    (hπ : 0 < πb) (hη : 0 < η) (hpos : ρ < lam * η * πb) :
    StrictMonoOn (fun η' => (lam * η' * πb - ρ) / (σ + 1 / (lam - 1))) (Set.Ioi 0) ∧
      StrictMonoOn (fun π' => (lam * η * π' - ρ) / (σ + 1 / (lam - 1))) (Set.Ioi 0) ∧
      StrictAnti (fun ρ' => (lam * η * πb - ρ') / (σ + 1 / (lam - 1))) ∧
      StrictAntiOn (fun σ' => (lam * η * πb - ρ) / (σ' + 1 / (lam - 1))) (Set.Ioi 0) := by
  have hl : 0 < lam - 1 := by linarith
  have hden : 0 < σ + 1 / (lam - 1) := by positivity
  refine ⟨fun a _ b _ hab => ?_, fun a _ b _ hab => ?_, fun a b hab => ?_,
    fun a ha b _ hab => ?_⟩
  · apply div_lt_div_of_pos_right _ hden
    have : lam * a * πb < lam * b * πb := by
      have := mul_lt_mul_of_pos_left hab (by linarith : (0 : ℝ) < lam)
      exact mul_lt_mul_of_pos_right this hπ
    linarith
  · apply div_lt_div_of_pos_right _ hden
    have := mul_lt_mul_of_pos_left hab (by positivity : (0 : ℝ) < lam * η)
    linarith
  · exact div_lt_div_of_pos_right (by linarith) hden
  · simp only [Set.mem_Ioi] at ha
    exact div_lt_div_of_pos_left (by linarith) (by positivity) (by linarith)

/-- AKMM, p. 403: **growth rises with the step size `λ`**. For `λ > 1` with `ληπ̄ > ρ`,
`g(λ) = (ληπ̄ − ρ)/(σ + 1/(λ−1))` is strictly increasing in `λ`. -/
theorem quality_growth_mono_lambda {η πb σ ρ : ℝ} (hσ : 0 < σ) (hπ : 0 < πb) (hη : 0 < η) :
    StrictMonoOn (fun lam => (lam * η * πb - ρ) / (σ + 1 / (lam - 1)))
      {lam | 1 < lam ∧ ρ < lam * η * πb} := by
  intro a ha b hb hab
  have ha1 : 0 < a - 1 := by linarith [ha.1]
  have hb1 : 0 < b - 1 := by linarith [hb.1]
  have hda : 0 < σ + 1 / (a - 1) := by positivity
  have hdb : 0 < σ + 1 / (b - 1) := by positivity
  have hden : σ + 1 / (b - 1) < σ + 1 / (a - 1) := by
    have := one_div_lt_one_div_of_lt ha1 (by linarith : a - 1 < b - 1)
    linarith
  have hnum : a * η * πb - ρ < b * η * πb - ρ := by
    have := mul_lt_mul_of_pos_right hab (mul_pos hη hπ)
    linarith
  calc (a * η * πb - ρ) / (σ + 1 / (a - 1)) < (b * η * πb - ρ) / (σ + 1 / (a - 1)) :=
        div_lt_div_of_pos_right hnum hda
    _ < (b * η * πb - ρ) / (σ + 1 / (b - 1)) :=
        div_lt_div_of_pos_left (by linarith [hb.2]) hdb hden

/-- AKMM, p. 403: **growth falls with the cost `ψ`**: `π̄ = φAX^{(1−φ)/φ}L` with
`X = A(1−φ)/ψ` is strictly decreasing in `ψ > 0`. -/
theorem quality_growth_anti_psi {A φ L : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1)
    (hL : 0 < L) : StrictAntiOn (fun ψ => qlPiBar A φ ψ L) (Set.Ioi 0) := by
  have h1φ : 0 < 1 - φ := by linarith
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  unfold qlPiBar romerX
  have hlt : A * (1 - φ) / b < A * (1 - φ) / a :=
    div_lt_div_of_pos_left (by positivity) ha hab
  have := Real.rpow_lt_rpow (by positivity) hlt (by positivity : (0 : ℝ) < (1 - φ) / φ)
  have hc : 0 < φ * A := by positivity
  nlinarith [mul_lt_mul_of_pos_left this hc]

end AKMM.Growth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Quality ladders: the planner

AKMM, §13.5.2 (p. 404) and Appendix 13.A.10 (pp. 861–862). Write
`κ = (A/(1−φ))(A/ψ)^{(1−φ)/φ}L`, so that the planner's output is `Y^{SP} = κQ`.

* Static: `x^{SP} = (A/ψ)^{1/φ}L` maximises net output on each line, `x^{SP} > x^{DE}`
  (`quality_planner_static`); `X^{SP} = (1−φ)Y^{SP}`, `Y − X = φY`, `Y^{SP} > Y^{DE}`
  (`quality_planner_aggregates`).
* Dynamic: with `Z = φY − C` and `Q̇ = (λ−1)ηZ`, the planner's problem is an AK problem with
  return `(λ−1)ηφκ`; the balanced path with growth (13.A.28)
  `g^{SP} = ((λ−1)ηφκ − ρ)/σ` is optimal (`eq_13_A_28`), with the stated comparative statics
  (`quality_planner_comparative_statics`).
* The printed Hamiltonian has `e^{ρt}`; with it the same conditions would give
  `((λ−1)ηφκ + ρ)/σ` (`quality_planner_hamiltonian_sign`).
* `g^{SP}` can be above or below `g^{DE}` (`quality_sp_vs_de_ambiguous`).
-/

namespace AKMM.Growth

open Real Filter Topology

/-- AKMM, App. 13.A.10, p. 861: **the planner's static problem**. On a line of quality `q > 0`,
net output `(A/(1−φ))L^φqx^{1−φ} − ψqx` is maximised over `x ≥ 0` at `x^{SP} = (A/ψ)^{1/φ}L`,
and `x^{SP} > x^{DE} = (A(1−φ)/ψ)^{1/φ}L`. -/
theorem quality_planner_static {A φ ψ q L x : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1)
    (hψ : 0 < ψ) (hq : 0 < q) (hL : 0 < L) (hx : 0 ≤ x) :
    A * q / (1 - φ) * L ^ φ * x ^ (1 - φ) - ψ * q * x ≤
        A * q / (1 - φ) * L ^ φ * ((A / ψ) ^ (1 / φ) * L) ^ (1 - φ) -
          ψ * q * ((A / ψ) ^ (1 / φ) * L) ∧
      romerXMon A φ ψ L < (A / ψ) ^ (1 / φ) * L := by
  have h := eq_13_A_16 (A := A * q) (ψ := ψ * q) (by positivity) hφ0 hφ1 (by positivity) hL hx
  rw [show A * q / (ψ * q) = A / ψ by field_simp] at h
  refine ⟨h.1, ?_⟩
  have hr := romer_machine_ratio hA hφ0 hφ1 hψ hL
  have hpos : 0 < (A / ψ) ^ (1 / φ) * L := by positivity
  have := hr.1
  rw [div_eq_iff hpos.ne'] at this
  rw [this]
  nlinarith [hr.2.1]

/-- AKMM, App. 13.A.10, p. 862: **the planner's aggregates**. With `x^{SP}` on every line,
`Y^{SP} = (A/(1−φ))(A/ψ)^{(1−φ)/φ}QL`, `X^{SP} = ψLQ(A/ψ)^{1/φ} = (1−φ)Y^{SP}`, so
`Y^{SP} − X^{SP} = φY^{SP}`, and `Y^{SP} > Y^{DE} = (A/(1−φ))(A(1−φ)/ψ)^{(1−φ)/φ}QL`. -/
theorem quality_planner_aggregates {A φ ψ Q L : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1)
    (hψ : 0 < ψ) (hQ : 0 < Q) (hL : 0 < L) :
    A / (1 - φ) * L ^ φ * (Q * ((A / ψ) ^ (1 / φ) * L) ^ (1 - φ)) =
        A / (1 - φ) * (A / ψ) ^ ((1 - φ) / φ) * Q * L ∧
      ψ * L * Q * (A / ψ) ^ (1 / φ) = (1 - φ) * (A / (1 - φ) * (A / ψ) ^ ((1 - φ) / φ) * Q * L) ∧
      A / (1 - φ) * romerX A φ ψ ^ ((1 - φ) / φ) * Q * L <
        A / (1 - φ) * (A / ψ) ^ ((1 - φ) / φ) * Q * L := by
  have h1φ : 0 < 1 - φ := by linarith
  have hAψ : 0 < A / ψ := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.mul_rpow (by positivity) hL.le, ← Real.rpow_mul hAψ.le,
      show 1 / φ * (1 - φ) = (1 - φ) / φ by ring]
    have : L ^ φ * L ^ (1 - φ) = L := by
      rw [← Real.rpow_add hL, show φ + (1 - φ) = 1 by ring, Real.rpow_one]
    linear_combination (A / (1 - φ) * Q * (A / ψ) ^ ((1 - φ) / φ)) * this
  · rw [show 1 / φ = (1 - φ) / φ + 1 by field_simp; ring, Real.rpow_add hAψ, Real.rpow_one]
    field_simp
  · have hlt : romerX A φ ψ < A / ψ := by
      unfold romerX
      rw [div_lt_div_iff_of_pos_right hψ]
      nlinarith
    have hX : 0 < romerX A φ ψ := by unfold romerX; positivity
    have := Real.rpow_lt_rpow hX.le hlt (by positivity : (0 : ℝ) < (1 - φ) / φ)
    have hc : 0 < A / (1 - φ) := by positivity
    have hQL : 0 < Q * L := by positivity
    nlinarith [mul_lt_mul_of_pos_left this hc, mul_lt_mul_of_pos_right
      (mul_lt_mul_of_pos_left this hc) hQL]

/-- AKMM, (13.A.28), p. 862: **the planner's growth rate**. With `Q̇ = (λ−1)η(φκQ − C)`
(`Z = φY^{SP} − C`, `z = ηZ/Q`, `Q̇ = (λ−1)zQ`), the planner's problem in `S = Q/((λ−1)η)` is
the AK problem `Ṡ = (λ−1)ηφκS − C`. If `σ(λ−1)ηφκ > (λ−1)ηφκ − ρ` and `u` is concave with
`u'(C) = C^{−σ}`, the path `C(t) = ((λ−1)ηφκ − g^{SP})S_0e^{g^{SP}t}` with
`g^{SP} = ((λ−1)ηφκ − ρ)/σ` is catching-up optimal against every path from `Q_0` with
`Q ≥ 0` and positive continuous consumption. -/
theorem eq_13_A_28 {lam η φκ σ ρ Q0 : ℝ} {u : ℝ → ℝ} {Q' C' : ℝ → ℝ} (hlam : 1 < lam)
    (hη : 0 < η) (hσ : 0 < σ) (hQ0 : 0 < Q0)
    (hbound : (lam - 1) * η * φκ - ρ < σ * ((lam - 1) * η * φκ))
    (hconc : ConcaveOn ℝ (Set.Ioi 0) u) (hu : ∀ y, 0 < y → HasDerivAt u (y ^ (-σ)) y)
    (hQ' : ∀ t, 0 ≤ t → 0 ≤ Q' t) (hC' : ∀ t, 0 ≤ t → 0 < C' t)
    (hCc' : ContinuousOn C' (Set.Ici 0))
    (hQd' : ∀ t, 0 ≤ t → HasDerivAt Q' ((lam - 1) * η * (φκ * Q' t - C' t)) t)
    (h0 : Q' 0 = Q0) :
    ∀ ε > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (C' t) ≤
      (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) *
        u (((lam - 1) * η * φκ - ((lam - 1) * η * φκ - ρ) / σ) *
          (Q0 / ((lam - 1) * η) * Real.exp (((lam - 1) * η * φκ - ρ) / σ * t)))) + ε := by
  have hl : 0 < (lam - 1) * η := mul_pos (by linarith) hη
  have hb : (lam - 1) * η * φκ - 0 - ρ < σ * ((lam - 1) * η * φκ - 0 - 0) := by
    simpa using hbound
  have h := ak_optimal (A := (lam - 1) * η * φκ) (δ := 0) (n := 0) (k0 := Q0 / ((lam - 1) * η))
    (k' := fun t => Q' t / ((lam - 1) * η)) (c' := C') hσ (by positivity) hb hconc hu
    (fun t ht => by have := hQ' t ht; positivity) hC' hCc' (fun t ht => by
      have hl1 : lam - 1 ≠ 0 := by linarith
      convert (hQd' t ht).div_const ((lam - 1) * η) using 1
      field_simp
      ring) (by rw [h0])
  simp only [sub_zero, akG] at h
  exact h

/-- AKMM, App. 13.A.10, p. 862: the comparative statics of (13.A.28): `g^{SP}` is strictly
increasing in `λ`, in `η` and in `κ` (so in `L`), strictly decreasing in `ρ`, and strictly
decreasing in `σ > 0` when positive. -/
theorem quality_planner_comparative_statics {lam η φκ σ ρ : ℝ} (hlam : 1 < lam) (hη : 0 < η)
    (hκ : 0 < φκ) (hσ : 0 < σ) (hpos : ρ < (lam - 1) * η * φκ) :
    StrictMono (fun l => ((l - 1) * η * φκ - ρ) / σ) ∧
      StrictMono (fun e => ((lam - 1) * e * φκ - ρ) / σ) ∧
      StrictMono (fun k => ((lam - 1) * η * k - ρ) / σ) ∧
      StrictAnti (fun r => ((lam - 1) * η * φκ - r) / σ) ∧
      StrictAntiOn (fun s => ((lam - 1) * η * φκ - ρ) / s) (Set.Ioi 0) := by
  have hl : 0 < lam - 1 := by linarith
  refine ⟨fun a b hab => ?_, fun a b hab => ?_, fun a b hab => ?_, fun a b hab => ?_,
    fun a ha b _ hab => ?_⟩
  · apply div_lt_div_of_pos_right _ hσ
    nlinarith [mul_pos hη hκ]
  · apply div_lt_div_of_pos_right _ hσ
    nlinarith [mul_pos hl hκ]
  · apply div_lt_div_of_pos_right _ hσ
    nlinarith [mul_pos hl hη]
  · exact div_lt_div_of_pos_right (by linarith) hσ
  · simp only [Set.mem_Ioi] at ha
    exact div_lt_div_of_pos_left (by linarith) ha hab

/-- AKMM, App. 13.A.10, p. 862: **the sign of the discount in the Hamiltonian**. The printed
Hamiltonian has `e^{ρt}`. With it, the first-order condition `e^{ρt}C^{−σ} = μ(λ−1)η` and the
costate equation `μ̇ = −μ(λ−1)ηφκ` give `Ċ/C = ((λ−1)ηφκ + ρ)/σ`, which differs from (13.A.28)
whenever `ρ ≠ 0`; (13.A.28) needs `e^{−ρt}`. -/
theorem quality_planner_hamiltonian_sign {lam η φκ σ ρ t Cdot : ℝ} {C μ : ℝ → ℝ}
    (hσ : 0 < σ) (hC : 0 < C t) (hCd : HasDerivAt C Cdot t)
    (hfoc : ∀ s, Real.exp (ρ * s) * C s ^ (-σ) = μ s * ((lam - 1) * η))
    (hcost : HasDerivAt μ (-(μ t * ((lam - 1) * η * φκ))) t) :
    Cdot / C t = ((lam - 1) * η * φκ + ρ) / σ ∧
      (((lam - 1) * η * φκ + ρ) / σ = ((lam - 1) * η * φκ - ρ) / σ ↔ ρ = 0) := by
  refine ⟨?_, ?_⟩
  · have h := eq_13_19 (A := (lam - 1) * η * φκ) (δ := 0) (ρ := -ρ) (n := 0)
      (μ := fun s => μ s * ((lam - 1) * η)) hσ hC hCd (fun s => by
        rw [← hfoc s]; simp) (by
        convert hcost.mul_const ((lam - 1) * η) using 1; ring)
    rw [h]
    unfold akG
    ring
  · constructor
    · intro h
      field_simp at h
      linarith
    · intro h; rw [h]; ring

/-- AKMM, p. 404 and App. 13.A.10: **`g^{SP}` versus `g^{DE}` is ambiguous**. Take `φ = 1/2`,
`A = 2`, `ψ = 1`, `η = 1`, so that `π̄ = L` and `φκ = 4L`, and `σ = 1`. With `λ = 2`, `L = 1`,
`ρ = 1/10`, `g^{DE} = 19/20 < g^{SP} = 39/10`; with `λ = 11/10`, `L = 10`, `ρ = 39/10`,
`g^{DE} = 71/110 > g^{SP} = 1/10 > 0`. -/
theorem quality_sp_vs_de_ambiguous :
    (∀ L : ℝ, qlPiBar 2 (1 / 2) 1 L = L) ∧
    (∀ L : ℝ, 1 / 2 * (2 / (1 - 1 / 2) * (2 / 1 : ℝ) ^ (((1 : ℝ) - 1 / 2) / (1 / 2)) * L) =
      4 * L) ∧
    ((2 * 1 * 1 - 1 / 10) / (1 + 1 / (2 - 1)) : ℝ) < ((2 - 1) * 1 * (4 * 1) - 1 / 10) / 1 ∧
    (((11 / 10 - 1) * 1 * (4 * 10) - 39 / 10) / 1 : ℝ) <
      (11 / 10 * 1 * 10 - 39 / 10) / (1 + 1 / (11 / 10 - 1)) ∧
    (0 : ℝ) < ((11 / 10 - 1) * 1 * (4 * 10) - 39 / 10) / 1 := by
  refine ⟨fun L => ?_, fun L => ?_, by norm_num, by norm_num, by norm_num⟩
  · unfold qlPiBar romerX
    rw [show ((1 : ℝ) - 1 / 2) / (1 / 2) = 1 by norm_num, Real.rpow_one]
    norm_num
  · rw [show ((1 : ℝ) - 1 / 2) / (1 / 2) = 1 by norm_num, Real.rpow_one]
    ring

end AKMM.Growth

set_option linter.style.longLine false
#print axioms AKMM.Growth.accounting_ratio_pow
#print axioms AKMM.Growth.eq_13_2
#print axioms AKMM.Growth.eq_13_3_log
#print axioms AKMM.Growth.eq_13_3
#print axioms AKMM.Growth.eq_13_17
#print axioms AKMM.Growth.accounting_footnote_23
#print axioms AKMM.Growth.accounting_footnote_23_value
#print axioms AKMM.Growth.accounting_us_decomposition
#print axioms AKMM.Growth.istcGK
#print axioms AKMM.Growth.istcGc
#print axioms AKMM.Growth.istcD
#print axioms AKMM.Growth.istcBound
#print axioms AKMM.Growth.istc_gK_eq
#print axioms AKMM.Growth.istc_D_eq
#print axioms AKMM.Growth.istc_bound_eq
#print axioms AKMM.Growth.istc_D_sub_gK
#print axioms AKMM.Growth.istc_price_hasDerivAt
#print axioms AKMM.Growth.eq_13_5
#print axioms AKMM.Growth.istc_rpow_ratio
#print axioms AKMM.Growth.eq_13_A_1
#print axioms AKMM.Growth.eq_13_A_2
#print axioms AKMM.Growth.istc_firm_optimal
#print axioms AKMM.Growth.eq_13_A_3
#print axioms AKMM.Growth.eq_13_A_7
#print axioms AKMM.Growth.istc_costate_of_euler
#print axioms AKMM.Growth.eq_13_A_8
#print axioms AKMM.Growth.eq_13_10
#print axioms AKMM.Growth.istc_walras
#print axioms AKMM.Growth.eq_13_A_11
#print axioms AKMM.Growth.istc_planner_euler
#print axioms AKMM.Growth.istc_labour_augmenting
#print axioms AKMM.Growth.istc_output_reduced
#print axioms AKMM.Growth.istc_budget_reduced
#print axioms AKMM.Growth.istc_return_reduced
#print axioms AKMM.Growth.istc_reduced_hasDerivAt
#print axioms AKMM.Growth.istc_bgp_rhs_9
#print axioms AKMM.Growth.istc_bgp_rhs_10
#print axioms AKMM.Growth.istc_standard_candidate_fails
#print axioms AKMM.Growth.istc_detrend_exp
#print axioms AKMM.Growth.eq_13_12
#print axioms AKMM.Growth.eq_13_13
#print axioms AKMM.Growth.istcKStar
#print axioms AKMM.Growth.istcCStar
#print axioms AKMM.Growth.istc_D_pos
#print axioms AKMM.Growth.istc_mpk_star
#print axioms AKMM.Growth.eq_13_14
#print axioms AKMM.Growth.istc_steady_pos
#print axioms AKMM.Growth.eq_13_15
#print axioms AKMM.Growth.istc_steady_unique
#print axioms AKMM.Growth.istc_tvc_detrended
#print axioms AKMM.Growth.istc_exp_tendsto_zero_iff
#print axioms AKMM.Growth.istc_bgp_tvc_iff
#print axioms AKMM.Growth.istc_bgp_utility_eq
#print axioms AKMM.Growth.istc_bgp_utility_integrable
#print axioms AKMM.Growth.istc_bgp_utility_unbounded
#print axioms AKMM.Growth.istc_cd_eq
#print axioms AKMM.Growth.istc_mpk_formula
#print axioms AKMM.Growth.istcSStar
#print axioms AKMM.Growth.istc_footnote_14
#print axioms AKMM.Growth.istc_saving_rate_bgp
#print axioms AKMM.Growth.istcKGold
#print axioms AKMM.Growth.istcSteadyC
#print axioms AKMM.Growth.eq_13_16
#print axioms AKMM.Growth.istc_golden_saving
#print axioms AKMM.Growth.istc_below_golden_iff
#print axioms AKMM.Growth.istc_r_star
#print axioms AKMM.Growth.istc_rental_bgp
#print axioms AKMM.Growth.istc_wage_bgp
#print axioms AKMM.Growth.istc_output_bgp
#print axioms AKMM.Growth.istc_nominal_KY
#print axioms AKMM.Growth.istc_deflator
#print axioms AKMM.Growth.istc_real_KY_growth
#print axioms AKMM.Growth.istc_deflator_printed_false
#print axioms AKMM.Growth.istcPhi
#print axioms AKMM.Growth.istc_closed_form_rhs
#print axioms AKMM.Growth.istc_closed_form
#print axioms AKMM.Growth.istc_closed_form_rate
#print axioms AKMM.Growth.istc_closed_form_path
#print axioms AKMM.Growth.istc_closed_form_converges
#print axioms AKMM.Growth.istcFc
#print axioms AKMM.Growth.istcFk
#print axioms AKMM.Growth.istc_F_eq
#print axioms AKMM.Growth.eq_13_A_14
#print axioms AKMM.Growth.eq_13_A_15
#print axioms AKMM.Growth.istc_eigenvalues
#print axioms AKMM.Growth.istc_stable_root
#print axioms AKMM.Growth.istc_saddle
#print axioms AKMM.Growth.istc_half_life
#print axioms AKMM.Growth.istc_crra_concave
#print axioms AKMM.Growth.istc_log_concave
#print axioms AKMM.Growth.istc_rpow_tangent
#print axioms AKMM.Growth.istc_capital_to_wealth
#print axioms AKMM.Growth.istc_optimal
#print axioms AKMM.Growth.istc_bgp_optimal
#print axioms AKMM.Growth.istc_closed_form_optimal
#print axioms AKMM.Growth.akG
#print axioms AKMM.Growth.eq_13_19
#print axioms AKMM.Growth.eq_13_20
#print axioms AKMM.Growth.ak_capital_to_percapita
#print axioms AKMM.Growth.ak_policy
#print axioms AKMM.Growth.ak_bounded_iff
#print axioms AKMM.Growth.ak_tvc
#print axioms AKMM.Growth.ak_optimal
#print axioms AKMM.Growth.ak_decentralized
#print axioms AKMM.Growth.ak_footnote_24_general
#print axioms AKMM.Growth.ak_footnote_24_unique
#print axioms AKMM.Growth.ak_footnote_24_printed_false
#print axioms AKMM.Growth.ak_footnote_25
#print axioms AKMM.Growth.romerX
#print axioms AKMM.Growth.romer_X_identity
#print axioms AKMM.Growth.eq_13_23
#print axioms AKMM.Growth.eq_13_24
#print axioms AKMM.Growth.romerXMon
#print axioms AKMM.Growth.eq_13_33
#print axioms AKMM.Growth.eq_13_34
#print axioms AKMM.Growth.romer_footnote_32
#print axioms AKMM.Growth.eq_13_35
#print axioms AKMM.Growth.eq_13_36
#print axioms AKMM.Growth.eq_13_37
#print axioms AKMM.Growth.romer_footnote_29
#print axioms AKMM.Growth.eq_13_40
#print axioms AKMM.Growth.eq_13_41
#print axioms AKMM.Growth.eq_13_42
#print axioms AKMM.Growth.eq_13_43
#print axioms AKMM.Growth.romerLyStar
#print axioms AKMM.Growth.eq_13_44
#print axioms AKMM.Growth.romer_Lr_star
#print axioms AKMM.Growth.eq_13_45
#print axioms AKMM.Growth.eq_13_46
#print axioms AKMM.Growth.romer_tvc_iff
#print axioms AKMM.Growth.eq_13_52
#print axioms AKMM.Growth.romer_comparative_statics
#print axioms AKMM.Growth.romer_research_share_mono
#print axioms AKMM.Growth.romer_markup_interest
#print axioms AKMM.Growth.romer_theta_growth_mono
#print axioms AKMM.Growth.romer_footnote_33_solution
#print axioms AKMM.Growth.romer_footnote_33_above
#print axioms AKMM.Growth.romer_footnote_33_below
#print axioms AKMM.Growth.romer_footnote_33_tvc_fails
#print axioms AKMM.Growth.romer_footnote_33
#print axioms AKMM.Growth.romer_footnote_34
#print axioms AKMM.Growth.romer_footnote_34_printed_false
#print axioms AKMM.Growth.eq_13_A_16
#print axioms AKMM.Growth.eq_13_A_17
#print axioms AKMM.Growth.eq_13_A_21
#print axioms AKMM.Growth.romer_planner_Ly
#print axioms AKMM.Growth.eq_13_50
#print axioms AKMM.Growth.eq_13_51
#print axioms AKMM.Growth.romer_planner_optimal
#print axioms AKMM.Growth.romer_machine_ratio
#print axioms AKMM.Growth.romer_machine_ratio_printed_false
#print axioms AKMM.Growth.romer_subsidy
#print axioms AKMM.Growth.romer_subsidy_not_efficient
#print axioms AKMM.Growth.romer_planner_growth_gt
#print axioms AKMM.Growth.eq_13_54
#print axioms AKMM.Growth.jones_value_unique
#print axioms AKMM.Growth.eq_13_55
#print axioms AKMM.Growth.eq_13_56
#print axioms AKMM.Growth.eq_13_56_converse
#print axioms AKMM.Growth.jones_r_star
#print axioms AKMM.Growth.eq_13_59
#print axioms AKMM.Growth.jones_N_unique
#print axioms AKMM.Growth.eq_13_60
#print axioms AKMM.Growth.jones_level_effect
#print axioms AKMM.Growth.jones_no_growth
#print axioms AKMM.Growth.eq_13_A_24
#print axioms AKMM.Growth.jones_planner_lambda_growth
#print axioms AKMM.Growth.jones_planner_bgp
#print axioms AKMM.Growth.jones_planner_A25_alone_insufficient
#print axioms AKMM.Growth.qlPiBar
#print axioms AKMM.Growth.eq_13_62
#print axioms AKMM.Growth.eq_13_63
#print axioms AKMM.Growth.eq_13_65
#print axioms AKMM.Growth.quality_aggregates
#print axioms AKMM.Growth.eq_13_A_26
#print axioms AKMM.Growth.eq_13_64
#print axioms AKMM.Growth.qlMarkupProfit
#print axioms AKMM.Growth.eq_13_A_27
#print axioms AKMM.Growth.quality_research_foc
#print axioms AKMM.Growth.quality_V_over_q
#print axioms AKMM.Growth.quality_arrow_replacement
#print axioms AKMM.Growth.quality_value
#print axioms AKMM.Growth.quality_single_ladder
#print axioms AKMM.Growth.eq_13_66
#print axioms AKMM.Growth.quality_comparative_statics
#print axioms AKMM.Growth.quality_growth_mono_lambda
#print axioms AKMM.Growth.quality_growth_anti_psi
#print axioms AKMM.Growth.quality_planner_static
#print axioms AKMM.Growth.quality_planner_aggregates
#print axioms AKMM.Growth.eq_13_A_28
#print axioms AKMM.Growth.quality_planner_comparative_statics
#print axioms AKMM.Growth.quality_planner_hamiltonian_sign
#print axioms AKMM.Growth.quality_sp_vs_de_ambiguous
