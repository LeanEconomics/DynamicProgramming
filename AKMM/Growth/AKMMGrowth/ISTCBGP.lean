/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMGrowth.ISTCModel
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

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
