/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesian.MPEfficient
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Monetary policy design: price dispersion to second order (Miao §19.2.2, Step 1)

Miao, §19.2.2, Step 1, p. 633. Notation: `b = ε/(1 − α)`, `c = ε/((1 − α)(ε − 1))`,
`g(π) = (1 − θe^{(ε−1)π})/(1 − θ)` and `π_t = ln(P_t/P_{t−1})`.

* `mp_labor_log` (Step 1, first display): from (19.16), `Y = AN^{1−α}Δ^{α−1}`,
  `ln N = (ln Y − ln A)/(1 − α) + ln Δ` exactly; in deviations
  `n̂_t = (ŷ_t − a_t)/(1 − α) + Δ̂_t` (`mp_labor_dev`).
* `mp_dispersion_recursion`: (19.13) and (19.17) give
  `Δ_t = θe^{bπ_t}Δ_{t−1} + (1 − θ)g(π_t)^c` (the display "By (19.13) and (19.17)").
* `mp_dispersion_zero_inflation`: with `π_t = 0`, `Δ_t − 1 = θ(Δ_{t−1} − 1)` (no new dispersion).
* `mp_dispersion_delta`: with `δ_t = Δ_t − 1`, exactly
  `δ_t = θδ_{t−1} + h(π_t) + θ(e^{bπ_t} − 1)δ_{t−1}`, `h = mpH`.
* `mp_h_expansion`: `h(π) = Kπ² + o(π²)`, `K = (1 − α + αε)εθ/(2(1 − α)²(1 − θ))` (`mpK`):
  a precise Peano-remainder statement, proved from `h(0) = h'(0) = 0`, `h''(0) = 2K`
  (`mp_h_zero`, `mp_hd_zero`, `mp_hasDerivAt_h`, `mp_hasDerivAt_hd`) and the general lemma
  `mp_peano2`.
* `mp_dispersion_second_order`: the book's second-order expansion
  `Δ̂_t = θΔ̂_{t−1} + Kπ_t²`: for every `ε' > 0` there is `δ > 0` such that `|π_t| < δ` implies
  `|δ_t − θδ_{t−1} − Kπ_t²| ≤ ε'π_t² + 2θb|π_t||δ_{t−1}|`; the last term is a product of a
  first-order and a second-order term (third order), which the book drops.
  `mp_log_dev`: `|ln Δ − (Δ − 1)| ≤ 2(Δ − 1)²` for `|Δ − 1| ≤ 1/2`, so the expansion holds for
  `Δ̂ = ln Δ` up to fourth-order terms.
* `mp_dispersion_sum`: for the second-order law `Δ̂_t = θΔ̂_{t−1} + Kπ_t²`, `Δ̂_{−1} = 0`,
  `0 ≤ β, θ < 1` and bounded `π`, `∑βᵗΔ̂_t = K/(1 − θβ)·∑βᵗπ_t²`, and
  `K/(1 − θβ) = εθ/(2(1 − α)Θ(1 − θ)(1 − θβ))`, `Θ = (1 − α)/(1 − α + αε)` (`mp_K_Theta`).
-/

namespace Miao.NewKeynesian

open Filter Topology

/-! ### Step 1: labour and dispersion -/

/-- **Step 1** (Miao, p. 633). From (19.16) in the form `Y = AN^{1−α}Δ^{α−1}` (`A, N, Δ > 0`,
`α ≠ 1`), `ln N = (ln Y − ln A)/(1 − α) + ln Δ`. -/
theorem mp_labor_log {α A N Δ : ℝ} (hα : α ≠ 1) (hA : 0 < A) (hN : 0 < N) (hΔ : 0 < Δ) :
    Real.log N = (Real.log (A * N ^ (1 - α) * Δ ^ (α - 1)) - Real.log A) / (1 - α) +
      Real.log Δ := by
  have h1 : (1 - α) ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  rw [Real.log_mul (mul_pos hA (Real.rpow_pos_of_pos hN _)).ne' (Real.rpow_pos_of_pos hΔ _).ne',
    Real.log_mul hA.ne' (Real.rpow_pos_of_pos hN _).ne', Real.log_rpow hN, Real.log_rpow hΔ]
  field_simp
  ring

/-- **Step 1** in deviations (Miao, p. 633): if `n_t = (y_t − a_t)/(1 − α) + ln Δ_t` at every
date and in the steady state (`Δ = 1`, `A = 1`), then `n̂_t = (ŷ_t − a_t)/(1 − α) + Δ̂_t`. -/
theorem mp_labor_dev {α n y a d n0 y0 : ℝ} (ht : n = (y - a) / (1 - α) + d)
    (hs : n0 = (y0 - 0) / (1 - α) + 0) :
    n - n0 = ((y - y0) - a) / (1 - α) + d := by
  rw [ht, hs]
  ring

/-- `g(π) = (1 − θe^{(ε−1)π})/(1 − θ)`, the value of `(P*/P)^{1−ε}` implied by (19.13). -/
noncomputable def mpG (ε θ x : ℝ) : ℝ := (1 - θ * Real.exp ((ε - 1) * x)) / (1 - θ)

/-- `h(π) = θe^{bπ} + (1 − θ)g(π)^c − 1`, `b = ε/(1 − α)`, `c = ε/((1 − α)(ε − 1))`. -/
noncomputable def mpH (α ε θ x : ℝ) : ℝ :=
  θ * Real.exp (ε / (1 - α) * x) + (1 - θ) * mpG ε θ x ^ (ε / ((1 - α) * (ε - 1))) - 1

/-- `h'(π) = θb(e^{bπ} − g(π)^{c−1}e^{(ε−1)π})`. -/
noncomputable def mpHd (α ε θ x : ℝ) : ℝ :=
  θ * (ε / (1 - α)) * Real.exp (ε / (1 - α) * x) -
    θ * (ε / (1 - α)) * mpG ε θ x ^ (ε / ((1 - α) * (ε - 1)) - 1) * Real.exp ((ε - 1) * x)

/-- The coefficient `K = (1 − α + αε)εθ/(2(1 − α)²(1 − θ))` of `π_t²` (Miao, p. 633). -/
noncomputable def mpK (α ε θ : ℝ) : ℝ := (1 - α + α * ε) * ε * θ / (2 * (1 - α) ^ 2 * (1 - θ))

/-- `Θ = (1 − α)/(1 − α + αε)` (Miao, p. 633). -/
noncomputable def mpTheta (α ε : ℝ) : ℝ := (1 - α) / (1 - α + α * ε)

/-- **The dispersion recursion** (Miao, p. 633, "By (19.13) and (19.17)"). Let
`P, P_{−1}, P* > 0`, `θ ≠ 1`, `ε ≠ 1`, `α ≠ 1`, `π = ln(P/P_{−1})`. If (19.13)
`P^{1−ε} = θP_{−1}^{1−ε} + (1 − θ)P*^{1−ε}` and (19.17)
`Δ = θ(P/P_{−1})^{ε/(1−α)}Δ_{−1} + (1 − θ)(P*/P)^{−ε/(1−α)}` hold, then
`Δ = θe^{bπ}Δ_{−1} + (1 − θ)g(π)^c`. -/
theorem mp_dispersion_recursion {α ε θ P Pm Ps Δ Δm : ℝ} (hα : α ≠ 1) (hε : ε ≠ 1)
    (hθ : θ ≠ 1) (hP : 0 < P) (hPm : 0 < Pm) (hPs : 0 < Ps)
    (h13 : P ^ (1 - ε) = θ * Pm ^ (1 - ε) + (1 - θ) * Ps ^ (1 - ε))
    (h17 : Δ = θ * (P / Pm) ^ (ε / (1 - α)) * Δm + (1 - θ) * (Ps / P) ^ (-(ε / (1 - α)))) :
    Δ = θ * Real.exp (ε / (1 - α) * Real.log (P / Pm)) * Δm +
      (1 - θ) * mpG ε θ (Real.log (P / Pm)) ^ (ε / ((1 - α) * (ε - 1))) := by
  have h1 : (1 - θ) ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  have ha : (1 - α) ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  have he : (ε - 1) ≠ 0 := sub_ne_zero.2 hε
  have hPP := div_pos hP hPm
  have hg : mpG ε θ (Real.log (P / Pm)) = (Ps / P) ^ (1 - ε) := by
    simp only [mpG]
    rw [eq_comm, eq_div_iff h1, Real.div_rpow hPs.le hP.le, div_mul_eq_mul_div,
      div_eq_iff (Real.rpow_pos_of_pos hP _).ne']
    have hx : Real.exp ((ε - 1) * Real.log (P / Pm)) * P ^ (1 - ε) = Pm ^ (1 - ε) := by
      rw [Real.rpow_def_of_pos hP, Real.rpow_def_of_pos hPm, ← Real.exp_add,
        Real.log_div hP.ne' hPm.ne']
      congr 1
      ring
    linear_combination (-1) * h13 + θ * hx
  rw [h17, hg, ← Real.rpow_mul (div_pos hPs hP).le, Real.rpow_def_of_pos hPP,
    show (1 - ε) * (ε / ((1 - α) * (ε - 1))) = -(ε / (1 - α)) by field_simp; ring]
  ring_nf

/-- Miao, p. 633: with `δ_t = Δ_t − 1`, the dispersion recursion is exactly
`δ_t = θδ_{t−1} + h(π_t) + θ(e^{bπ_t} − 1)δ_{t−1}`. -/
theorem mp_dispersion_delta {α ε θ x Δ Δm : ℝ}
    (h : Δ = θ * Real.exp (ε / (1 - α) * x) * Δm +
      (1 - θ) * mpG ε θ x ^ (ε / ((1 - α) * (ε - 1)))) :
    Δ - 1 = θ * (Δm - 1) + mpH α ε θ x + θ * (Real.exp (ε / (1 - α) * x) - 1) * (Δm - 1) := by
  rw [h, mpH]
  ring

/-! ### The second-order expansion of `h` -/

/-- **A second-order Peano remainder.** If `φ` has derivative `φ'` near `0`, `φ(0) = 0`,
`φ'(0) = 0` and `φ'` has derivative `L` at `0`, then `φ(x) = (L/2)x² + o(x²)`: for every
`ε > 0` there is `δ > 0` with `|φ(x) − (L/2)x²| ≤ εx²` for `|x| < δ`. -/
theorem mp_peano2 {φ φ' : ℝ → ℝ} {L : ℝ} (hd : ∀ᶠ x in 𝓝 0, HasDerivAt φ (φ' x) x)
    (h0 : φ 0 = 0) (h0' : φ' 0 = 0) (h2 : HasDerivAt φ' L 0) :
    ∀ ε > 0, ∃ δ > 0, ∀ x, |x| < δ → |φ x - L / 2 * x ^ 2| ≤ ε * x ^ 2 := by
  intro ε hε
  have ho := (hasDerivAt_iff_isLittleO_nhds_zero.1 h2).def hε
  obtain ⟨δ, hδ, hP⟩ := Metric.eventually_nhds_iff.1 (hd.and ho)
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have hin : ∀ y ∈ Set.Icc (-|x|) |x|, |y| < δ := fun y hy => (abs_le.2 hy).trans_lt hx
  have hP' : ∀ y ∈ Set.Icc (-|x|) |x|, HasDerivAt φ (φ' y) y ∧ |φ' y - L * y| ≤ ε * |y| := by
    intro y hy
    obtain ⟨h1, h2⟩ := hP (show dist y 0 < δ by rw [Real.dist_eq, sub_zero]; exact hin y hy)
    refine ⟨h1, ?_⟩
    simpa [h0', smul_eq_mul, mul_comm] using h2
  have hψ : ∀ y ∈ Set.Icc (-|x|) |x|, HasDerivWithinAt (fun z => φ z - L / 2 * z ^ 2)
      (φ' y - L * y) (Set.Icc (-|x|) |x|) y := by
    intro y hy
    refine (((hP' y hy).1.sub ((hasDerivAt_pow 2 y).const_mul (L / 2))).congr_deriv ?_)
      |>.hasDerivWithinAt
    push_cast
    ring
  have hbd : ∀ y ∈ Set.Icc (-|x|) |x|, ‖φ' y - L * y‖ ≤ ε * |x| := by
    intro y hy
    rw [Real.norm_eq_abs]
    exact (hP' y hy).2.trans (mul_le_mul_of_nonneg_left (abs_le.2 hy) hε.le)
  have hmv := (convex_Icc (-|x|) |x|).norm_image_sub_le_of_norm_hasDerivWithin_le hψ hbd
    (show (0 : ℝ) ∈ Set.Icc (-|x|) |x| by simp)
    (show x ∈ Set.Icc (-|x|) |x| from ⟨neg_abs_le x, le_abs_self x⟩)
  simp only [h0, Real.norm_eq_abs, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero] at hmv
  calc |φ x - L / 2 * x ^ 2| ≤ ε * |x| * |x| := hmv
    _ = ε * x ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- `g(0) = 1`. -/
theorem mp_G_zero {ε θ : ℝ} (hθ : θ ≠ 1) : mpG ε θ 0 = 1 := by
  have h1 : (1 - θ) ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  simp [mpG, h1]

/-- Miao, p. 635 ("the relative price distortion is removed"): under zero inflation
(`P_t = P_{t−1}`) the dispersion recursion is `Δ_t − 1 = θ(Δ_{t−1} − 1)` (`θ ≠ 1`), so dispersion
stays at `1` if it starts there and otherwise decays to `1` geometrically. -/
theorem mp_dispersion_zero_inflation {α ε θ Δ Δm : ℝ} (hθ : θ ≠ 1)
    (h : Δ = θ * Real.exp (ε / (1 - α) * 0) * Δm +
      (1 - θ) * mpG ε θ 0 ^ (ε / ((1 - α) * (ε - 1)))) :
    Δ - 1 = θ * (Δm - 1) := by
  rw [h, mul_zero, Real.exp_zero, mp_G_zero hθ, Real.one_rpow]
  ring

/-- `g` has derivative `−θ(ε − 1)e^{(ε−1)π}/(1 − θ)`. -/
theorem mp_hasDerivAt_G (ε θ x : ℝ) :
    HasDerivAt (mpG ε θ) (-(θ * (ε - 1) * Real.exp ((ε - 1) * x)) / (1 - θ)) x := by
  have h := ((((hasDerivAt_id' x).const_mul (ε - 1)).exp).const_mul θ).const_sub 1
  refine (h.div_const (1 - θ)).congr_deriv ?_
  ring

/-- `g > 0` near `0`. -/
theorem mp_G_pos_near {ε θ : ℝ} (hθ1 : θ < 1) :
    ∀ᶠ x in 𝓝 0, 0 < mpG ε θ x := by
  have hc : ContinuousAt (mpG ε θ) 0 := (mp_hasDerivAt_G ε θ 0).continuousAt
  have h1 : (0 : ℝ) < mpG ε θ 0 := by rw [mp_G_zero hθ1.ne]; exact one_pos
  exact hc.eventually (lt_mem_nhds h1)
    |>.mono fun x hx => hx

/-- `h(0) = 0`. -/
theorem mp_h_zero {α ε θ : ℝ} (hθ : θ ≠ 1) : mpH α ε θ 0 = 0 := by
  simp only [mpH, mul_zero, Real.exp_zero, mp_G_zero hθ, Real.one_rpow]
  ring

/-- `h'(0) = 0`. -/
theorem mp_hd_zero {α ε θ : ℝ} (hθ : θ ≠ 1) : mpHd α ε θ 0 = 0 := by
  simp only [mpHd, mul_zero, Real.exp_zero, mp_G_zero hθ, Real.one_rpow]
  ring

/-- `h` has derivative `h' = mpHd` wherever `g > 0` (`α ≠ 1`, `ε ≠ 1`, `θ ≠ 1`). -/
theorem mp_hasDerivAt_h {α ε θ x : ℝ} (hα : α ≠ 1) (hε : ε ≠ 1) (hθ : θ ≠ 1)
    (hg : 0 < mpG ε θ x) : HasDerivAt (mpH α ε θ) (mpHd α ε θ x) x := by
  have ha : (1 - α) ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  have he : (ε - 1) ≠ 0 := sub_ne_zero.2 hε
  have h1 : (1 - θ) ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  have hA := (((hasDerivAt_id' x).const_mul (ε / (1 - α))).exp).const_mul θ
  have hB := ((mp_hasDerivAt_G ε θ x).rpow_const (p := ε / ((1 - α) * (ε - 1)))
    (Or.inl hg.ne')).const_mul (1 - θ)
  refine ((hA.add hB).sub_const 1).congr_deriv ?_
  simp only [mpHd]
  field_simp
  ring

/-- `h'` has derivative `2K` at `0`. -/
theorem mp_hasDerivAt_hd {α ε θ : ℝ} (hα : α ≠ 1) (hε : ε ≠ 1) (hθ : θ ≠ 1) :
    HasDerivAt (mpHd α ε θ) (2 * mpK α ε θ) 0 := by
  have ha : (1 - α) ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  have he : (ε - 1) ≠ 0 := sub_ne_zero.2 hε
  have h1 : (1 - θ) ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  have hA := (((hasDerivAt_id' (0 : ℝ)).const_mul (ε / (1 - α))).exp).const_mul
    (θ * (ε / (1 - α)))
  have hB := (((mp_hasDerivAt_G ε θ 0).rpow_const (p := ε / ((1 - α) * (ε - 1)) - 1)
    (Or.inl (by rw [mp_G_zero hθ]; exact one_ne_zero))).const_mul (θ * (ε / (1 - α)))).mul
    (((hasDerivAt_id' (0 : ℝ)).const_mul (ε - 1)).exp)
  refine (hA.sub hB).congr_deriv ?_
  simp only [mul_zero, Real.exp_zero, mp_G_zero hθ, Real.one_rpow, mpK]
  field_simp
  ring

/-- **The second-order expansion of `h`** (Miao, p. 633): for `θ < 1`, `ε ≠ 1`, `α ≠ 1`,
`h(π) = Kπ² + o(π²)`. -/
theorem mp_h_expansion {α ε θ : ℝ} (hα : α ≠ 1) (hε : ε ≠ 1) (hθ1 : θ < 1) :
    ∀ ε' > 0, ∃ δ > 0, ∀ x, |x| < δ → |mpH α ε θ x - mpK α ε θ * x ^ 2| ≤ ε' * x ^ 2 := by
  intro ε' hε'
  obtain ⟨δ, hδ, h⟩ := mp_peano2 ((mp_G_pos_near hθ1).mono fun x hx =>
    mp_hasDerivAt_h hα hε hθ1.ne hx) (mp_h_zero hθ1.ne) (mp_hd_zero hθ1.ne)
    (mp_hasDerivAt_hd hα hε hθ1.ne) ε' hε'
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have := h x hx
  rwa [show 2 * mpK α ε θ / 2 = mpK α ε θ by ring] at this

/-- **The second-order dispersion law** (Miao, p. 633,
`Δ̂_t = θΔ̂_{t−1} + (1 − α + αε)εθ/(2(1 − α)²(1 − θ)) π_t²`). For `0 ≤ θ < 1`, `ε > 1`,
`α < 1` and every `ε' > 0` there is `δ > 0` such that whenever (19.13) and (19.17) hold with
`|π_t| < δ`, `π_t = ln(P_t/P_{t−1})`,
`|(Δ_t − 1) − θ(Δ_{t−1} − 1) − Kπ_t²| ≤ ε'π_t² + 2θb|π_t||Δ_{t−1} − 1|`. -/
theorem mp_dispersion_second_order {α ε θ : ℝ} (hα : α < 1) (hε : 1 < ε) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) : ∀ ε' > 0, ∃ δ > 0, ∀ P Pm Ps Δ Δm : ℝ, 0 < P → 0 < Pm → 0 < Ps →
      P ^ (1 - ε) = θ * Pm ^ (1 - ε) + (1 - θ) * Ps ^ (1 - ε) →
      Δ = θ * (P / Pm) ^ (ε / (1 - α)) * Δm + (1 - θ) * (Ps / P) ^ (-(ε / (1 - α))) →
      |Real.log (P / Pm)| < δ →
      |(Δ - 1) - θ * (Δm - 1) - mpK α ε θ * Real.log (P / Pm) ^ 2| ≤
        ε' * Real.log (P / Pm) ^ 2 + 2 * θ * (ε / (1 - α)) * |Real.log (P / Pm)| * |Δm - 1| := by
  intro ε' hε'
  have hb : 0 < ε / (1 - α) := div_pos (by linarith) (by linarith)
  obtain ⟨δ, hδ, hh⟩ := mp_h_expansion hα.ne hε.ne' hθ1 ε' hε'
  refine ⟨min δ ((1 - α) / ε), lt_min hδ (div_pos (by linarith) (by linarith)),
    fun P Pm Ps Δ Δm hP hPm hPs h13 h17 hx => ?_⟩
  set x := Real.log (P / Pm)
  have hrec := mp_dispersion_delta (mp_dispersion_recursion hα.ne hε.ne' hθ1.ne hP hPm hPs h13
    h17)
  have hbx : |ε / (1 - α) * x| ≤ 1 := by
    rw [abs_mul, abs_of_pos hb]
    have := (lt_min_iff.1 hx).2
    rw [lt_div_iff₀ (by linarith)] at this
    rw [div_mul_eq_mul_div, div_le_one (by linarith)]
    linarith
  have he := Real.abs_exp_sub_one_le hbx
  rw [abs_mul, abs_of_pos hb] at he
  have h1 := hh x (lt_min_iff.1 hx).1
  have e : (Δ - 1) - θ * (Δm - 1) - mpK α ε θ * x ^ 2 =
      (mpH α ε θ x - mpK α ε θ * x ^ 2) + θ * (Real.exp (ε / (1 - α) * x) - 1) * (Δm - 1) := by
    rw [hrec]
    ring
  rw [e]
  calc |(mpH α ε θ x - mpK α ε θ * x ^ 2) + θ * (Real.exp (ε / (1 - α) * x) - 1) * (Δm - 1)|
      ≤ |mpH α ε θ x - mpK α ε θ * x ^ 2| +
          |θ * (Real.exp (ε / (1 - α) * x) - 1) * (Δm - 1)| := abs_add_le _ _
    _ ≤ ε' * x ^ 2 + 2 * θ * (ε / (1 - α)) * |x| * |Δm - 1| := by
        refine add_le_add h1 ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hθ0]
        have := mul_le_mul_of_nonneg_left he hθ0
        have := mul_le_mul_of_nonneg_right this (abs_nonneg (Δm - 1))
        linarith

/-- Miao, p. 633: the log deviation `Δ̂ = ln Δ` and `Δ − 1` agree to second order:
`|ln Δ − (Δ − 1)| ≤ 2(Δ − 1)²` for `|Δ − 1| ≤ 1/2`. -/
theorem mp_log_dev {Δ : ℝ} (h : |Δ - 1| ≤ 1 / 2) : |Real.log Δ - (Δ - 1)| ≤ 2 * (Δ - 1) ^ 2 := by
  have hl := Real.abs_log_sub_add_sum_range_le (x := 1 - Δ) (by rw [abs_sub_comm]; linarith) 1
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, Nat.cast_zero, pow_one,
    div_one, sub_sub_cancel] at hl
  have hb : |1 - Δ| ^ (1 + 1) / (1 - |1 - Δ|) ≤ 2 * (Δ - 1) ^ 2 := by
    rw [abs_sub_comm, div_le_iff₀ (by linarith), show 1 + 1 = 2 by rfl, sq_abs]
    nlinarith [sq_nonneg (Δ - 1)]
  have e : Real.log Δ - (Δ - 1) = 1 - Δ + Real.log Δ := by ring
  rw [e]
  exact hl.trans hb

/-! ### The discounted sum -/

/-- `K/(1 − θβ) = εθ/(2(1 − α)Θ(1 − θ)(1 − θβ))` (Miao, p. 633). -/
theorem mp_K_Theta {α ε θ β : ℝ} (hα : α ≠ 1) (hd : 1 - α + α * ε ≠ 0) (hθ : θ ≠ 1)
    (hθβ : 1 - θ * β ≠ 0) :
    mpK α ε θ / (1 - θ * β) =
      ε * θ / (2 * (1 - α) * mpTheta α ε * (1 - θ) * (1 - θ * β)) := by
  have ha : (1 - α) ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  have h1 : (1 - θ) ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  simp only [mpK, mpTheta]
  field_simp

/-- A path satisfying `d_t = θd_{t−1} + Kπ_t²` from `d_{−1} = 0` with `|π_t| ≤ M` and
`0 ≤ θ < 1` is bounded by `|K|M²/(1 − θ)`. -/
theorem mp_disp_bounded {θ K M : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (pin d : ℕ → ℝ)
    (hM : ∀ t, |pin t| ≤ M) (h0 : d 0 = K * pin 0 ^ 2)
    (hs : ∀ t, d (t + 1) = θ * d t + K * pin (t + 1) ^ 2) :
    ∀ t, |d t| ≤ |K| * M ^ 2 / (1 - θ) := by
  have hq : ∀ t, |K * pin t ^ 2| ≤ |K| * M ^ 2 := fun t => by
    rw [abs_mul, abs_pow]
    have h0' : 0 ≤ |pin t| := abs_nonneg _
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0' (hM t) 2) (abs_nonneg K)
  have hB : 0 ≤ |K| * M ^ 2 := by positivity
  intro t
  rw [le_div_iff₀ (by linarith)]
  induction t with
  | zero =>
    rw [h0]
    nlinarith [hq 0]
  | succ n ih =>
    rw [hs]
    have h1 : |θ * d n + K * pin (n + 1) ^ 2| ≤ θ * |d n| + |K| * M ^ 2 := by
      have := abs_add_le (θ * d n) (K * pin (n + 1) ^ 2)
      rw [abs_mul, abs_of_nonneg hθ0] at this
      linarith [hq (n + 1)]
    have h2 : θ * |d n| ≤ θ * (|K| * M ^ 2 / (1 - θ)) := by
      apply mul_le_mul_of_nonneg_left _ hθ0
      rw [le_div_iff₀ (by linarith)]
      exact ih
    have hne : (1 : ℝ) - θ ≠ 0 := ne_of_gt (by linarith)
    have h3 : θ * (|K| * M ^ 2 / (1 - θ)) + |K| * M ^ 2 = |K| * M ^ 2 / (1 - θ) := by
      field_simp
      ring
    nlinarith

/-- **Step 1, the discounted sum** (Miao, p. 633). If `Δ̂_t = θΔ̂_{t−1} + Kπ_t²` with
`Δ̂_{−1} = 0` (so `Δ̂_0 = Kπ_0²`), `0 ≤ β < 1`, `0 ≤ θ < 1` and `π` is bounded, then
`∑βᵗΔ̂_t = K/(1 − θβ) · ∑βᵗπ_t²`. -/
theorem mp_dispersion_sum {θ β K M : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (pin d : ℕ → ℝ) (hM : ∀ t, |pin t| ≤ M) (h0 : d 0 = K * pin 0 ^ 2)
    (hs : ∀ t, d (t + 1) = θ * d t + K * pin (t + 1) ^ 2) :
    ∑' t, β ^ t * d t = K / (1 - θ * β) * ∑' t, β ^ t * pin t ^ 2 := by
  have hdb := mp_disp_bounded hθ0 hθ1 pin d hM h0 hs
  have hg := summable_geometric_of_lt_one hβ0 hβ1
  have hsd : Summable fun t => β ^ t * d t := by
    refine Summable.of_norm_bounded (g := fun t => |K| * M ^ 2 / (1 - θ) * β ^ t)
      (hg.mul_left _) fun t => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t), mul_comm]
    exact mul_le_mul_of_nonneg_right (hdb t) (pow_nonneg hβ0 t)
  have hsp : Summable fun t => β ^ t * pin t ^ 2 := by
    refine Summable.of_norm_bounded (g := fun t => M ^ 2 * β ^ t) (hg.mul_left _) fun t => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t), mul_comm, abs_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hM t) 2)
      (pow_nonneg hβ0 t)
  have hθβ : 1 - θ * β ≠ 0 := by nlinarith
  have e1 := hsd.tsum_eq_zero_add
  have e2 := hsp.tsum_eq_zero_add
  have hshift : ∀ t, β ^ (t + 1) * d (t + 1) =
      θ * β * (β ^ t * d t) + K * (β ^ (t + 1) * pin (t + 1) ^ 2) := fun t => by
    rw [hs, pow_succ]
    ring
  have hsum2 : Summable fun t => β ^ (t + 1) * pin (t + 1) ^ 2 :=
    (summable_nat_add_iff 1).2 hsp
  rw [tsum_congr hshift, (hsd.mul_left (θ * β)).tsum_add (hsum2.mul_left K), tsum_mul_left,
    tsum_mul_left] at e1
  have e3 : ∑' t, β ^ (t + 1) * pin (t + 1) ^ 2 = (∑' t, β ^ t * pin t ^ 2) - pin 0 ^ 2 := by
    simp only [pow_zero, one_mul] at e2
    linarith
  rw [e3] at e1
  simp only [pow_zero, one_mul, h0] at e1
  rw [div_mul_eq_mul_div, eq_div_iff hθβ]
  linear_combination e1

end Miao.NewKeynesian
