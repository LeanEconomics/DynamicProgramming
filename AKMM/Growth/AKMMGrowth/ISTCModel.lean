/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.FieldSimp

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
