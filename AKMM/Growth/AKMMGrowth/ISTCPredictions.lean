/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMGrowth.ISTCBGP
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

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
