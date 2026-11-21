/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMSustainability.Basics
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Damages

AKMM, §25.3.5 (pp. 759–764), the damage functions.

* Nordhaus–Sztorc damages `D(T) = 1 − 1/(1 + aT²)` (p. 763): `D = aT²/(1 + aT²)`
  (`nordhausD_eq`), `0 ≤ D ≤ aT²` and `aT² − D ≤ a²T⁴`, so `aT²` is the approximation near
  `0` (`nordhausD_approx`), which with `a = 0.00267` is `0.02403(T/3)²`, the book's
  "`0.024(T/3)²`" (`nordhausD_coefficient`); `D → 1` (footnote 12, `nordhausD_tendsto`).
  `D` is convex on `[−1/√(3a), 1/√(3a)]` (`nordhausD_convexOn`) but, footnote 12, not convex
  on `[0, ∞)` (`nordhausD_not_convexOn`).
* Adaptation (p. 763): with total damages `(T − a)^x/x + a`, `x > 1`, adaptation `a ∈ [0, T]`:
  for `T ≥ 1` the unique cost-minimising adaptation is `a = T − 1` and the reduced-form damage
  is `T + (1 − x)/x`, linear in `T` whatever `x` (`adaptation_optimal`,
  `adaptation_unique`); for `T < 1` the book's formula does not apply: the minimiser is
  `a = 0` with damage `T^x/x` (`adaptation_low_T`).
-/

namespace AKMM.Sustainability

open Real Filter Topology

/-- AKMM, p. 763: Nordhaus and Sztorc's damage share `D(T) = 1 − 1/(1 + aT²)` (`a = 0.00267`). -/
noncomputable def nordhausD (a T : ℝ) : ℝ := 1 - 1 / (1 + a * T ^ 2)

/-- AKMM, p. 763: `D(T) = aT²/(1 + aT²)`. -/
theorem nordhausD_eq {a : ℝ} (ha : 0 ≤ a) (T : ℝ) :
    nordhausD a T = a * T ^ 2 / (1 + a * T ^ 2) := by
  have : 0 < 1 + a * T ^ 2 := by positivity
  unfold nordhausD
  field_simp
  ring

/-- AKMM, p. 763: near `0`, `D(T) ≈ aT²`: `0 ≤ D ≤ aT²` and the error is at most `a²T⁴`. -/
theorem nordhausD_approx {a : ℝ} (ha : 0 ≤ a) (T : ℝ) :
    0 ≤ nordhausD a T ∧ nordhausD a T ≤ a * T ^ 2 ∧
      a * T ^ 2 - nordhausD a T ≤ a ^ 2 * T ^ 4 := by
  have hp : 0 ≤ a * T ^ 2 := by positivity
  have hd : 0 < 1 + a * T ^ 2 := by positivity
  rw [nordhausD_eq ha]
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_le_iff₀ hd]; nlinarith
  · have : a * T ^ 2 - a * T ^ 2 / (1 + a * T ^ 2) = (a * T ^ 2) ^ 2 / (1 + a * T ^ 2) := by
      field_simp; ring
    rw [this, div_le_iff₀ hd]
    nlinarith [sq_nonneg (a * T ^ 2)]

/-- AKMM, p. 763: the approximation `0.00267T²` is `0.02403(T/3)²`, the book's
"`0.024(T/3)²`". -/
theorem nordhausD_coefficient (T : ℝ) : (0.00267 : ℝ) * T ^ 2 = 0.02403 * (T / 3) ^ 2 := by
  ring

/-- AKMM, p. 763, footnote 12: "it asymptotes to 1 (all of output is lost) as `T` goes to
infinity". -/
theorem nordhausD_tendsto {a : ℝ} (ha : 0 < a) : Tendsto (nordhausD a) atTop (𝓝 1) := by
  have h : Tendsto (fun T : ℝ => 1 + a * T ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ 1
      ((tendsto_pow_atTop two_ne_zero).const_mul_atTop ha)
  have := (tendsto_inv_atTop_zero.comp h).const_sub 1
  rw [sub_zero] at this
  exact this.congr (fun T => by simp [nordhausD])

/-- AKMM, p. 763, footnote 12: `D` is convex near `0`, on `[−1/√(3a), 1/√(3a)]`, where
`D''(T) = 2a(1 − 3aT²)/(1 + aT²)³ ≥ 0`. -/
theorem nordhausD_convexOn {a : ℝ} (ha : 0 < a) :
    ConvexOn ℝ (Set.Icc (-(1 / Real.sqrt (3 * a))) (1 / Real.sqrt (3 * a))) (nordhausD a) := by
  set r := 1 / Real.sqrt (3 * a) with hr
  have hpos : ∀ T : ℝ, 0 < 1 + a * T ^ 2 := fun T => by positivity
  have hD : ∀ T, HasDerivAt (nordhausD a) (2 * a * T / (1 + a * T ^ 2) ^ 2) T := by
    intro T
    have h1 : HasDerivAt (fun T : ℝ => 1 + a * T ^ 2) (a * (2 * T)) T := by
      simpa using ((hasDerivAt_pow 2 T).const_mul a).const_add 1
    have h2 := (h1.inv (hpos T).ne').const_sub 1
    unfold nordhausD
    simp only [one_div]
    convert h2 using 1
    field_simp
  have hD2 : ∀ T, HasDerivAt (fun T => 2 * a * T / (1 + a * T ^ 2) ^ 2)
      (2 * a * (1 - 3 * a * T ^ 2) / (1 + a * T ^ 2) ^ 3) T := by
    intro T
    have h1 : HasDerivAt (fun T : ℝ => 1 + a * T ^ 2) (a * (2 * T)) T := by
      simpa using ((hasDerivAt_pow 2 T).const_mul a).const_add 1
    have h3 := ((hasDerivAt_id T).const_mul (2 * a)).div (h1.pow 2)
      (pow_ne_zero 2 (hpos T).ne')
    convert h3 using 1
    · funext y; simp [id]
    · have := (hpos T).ne'
      simp only [Pi.pow_apply, id]
      field_simp
      ring
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (fun T _ => (hD T).continuousAt.continuousWithinAt)
    (fun T _ => (hD T).hasDerivWithinAt) (fun T _ => (hD2 T).hasDerivWithinAt) ?_
  intro T hT
  rw [interior_Icc] at hT
  have h3a : 0 < 3 * a := by positivity
  have hsq : 0 < Real.sqrt (3 * a) := Real.sqrt_pos.mpr h3a
  have hT2 : T ^ 2 < r ^ 2 := by
    have : |T| < r := abs_lt.mpr ⟨hT.1, hT.2⟩
    have hr0 : 0 ≤ r := by positivity
    calc T ^ 2 = |T| ^ 2 := (sq_abs T).symm
      _ < r ^ 2 := by gcongr
  have hr2 : r ^ 2 = 1 / (3 * a) := by
    rw [hr, div_pow, Real.sq_sqrt h3a.le, one_pow]
  rw [hr2] at hT2
  have : 3 * a * T ^ 2 < 1 := by
    rw [lt_div_iff₀ h3a] at hT2; linarith
  have h4 := hpos T
  apply div_nonneg _ (by positivity)
  nlinarith

/-- AKMM, p. 763, footnote 12: "Globally, the damage function is not convex": `D` is not convex
on `[0, ∞)`. A convex function vanishing at `0` and positive at `1` grows at least linearly,
while `D < 1`. -/
theorem nordhausD_not_convexOn {a : ℝ} (ha : 0 < a) : ¬ ConvexOn ℝ (Set.Ici 0) (nordhausD a) := by
  intro hc
  set d := nordhausD a 1 with hd
  have hd0 : 0 < d := by
    rw [hd, nordhausD_eq ha.le]; positivity
  have hlt : ∀ T, nordhausD a T < 1 := fun T => by
    unfold nordhausD
    have : 0 < 1 / (1 + a * T ^ 2) := by positivity
    linarith
  -- at `T = 2/d ≥ 1`, convexity between `0` and `T` forces `D(1) ≤ D(T)/T < 1/T = d/2`
  set T := 2 / d with hT
  have hd1 : d < 1 := hlt 1
  have hT1 : 1 ≤ T := by rw [hT, le_div_iff₀ hd0]; linarith
  have hT0 : 0 < T := by positivity
  have hw1 : 0 ≤ 1 - 1 / T := by rw [sub_nonneg, div_le_one hT0]; exact hT1
  have hw2 : 0 ≤ 1 / T := by positivity
  have hw : (1 - 1 / T) + 1 / T = 1 := by ring
  have h := hc.2 (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hT0.le) hw1 hw2 hw
  simp only [smul_eq_mul, mul_zero, zero_add, one_div] at h
  have hx : T⁻¹ * T = 1 := inv_mul_cancel₀ hT0.ne'
  rw [hx] at h
  have h0 : nordhausD a 0 = 0 := by simp [nordhausD]
  rw [h0, mul_zero, zero_add] at h
  have hDT := hlt T
  have : d ≤ T⁻¹ * nordhausD a T := h
  have hTinv : T⁻¹ = d / 2 := by rw [hT]; field_simp
  rw [hTinv] at this
  nlinarith

/-- AKMM, p. 763: total damages in output units, `(T − a)^x/x + a`, with adaptation `a`. -/
noncomputable def adaptCost (x T a : ℝ) : ℝ := (T - a) ^ x / x + a

/-- AKMM, p. 763: for `x > 1` and `T ≥ 1` the adaptation `a = T − 1` minimises damages over
`a ∈ [0, T]`, and the reduced-form damage is `D(T) = T + (1 − x)/x`, linear in `T` whatever
`x`. -/
theorem adaptation_optimal {x T : ℝ} (hx : 1 < x) (hT : 1 ≤ T) :
    T - 1 ∈ Set.Icc 0 T ∧ adaptCost x T (T - 1) = T + (1 - x) / x ∧
      ∀ a ∈ Set.Icc 0 T, adaptCost x T (T - 1) ≤ adaptCost x T a := by
  have hx0 : 0 < x := by linarith
  have hval : adaptCost x T (T - 1) = T + (1 - x) / x := by
    simp only [adaptCost, sub_sub_cancel, one_rpow]
    field_simp
    ring
  refine ⟨⟨by linarith, by linarith⟩, hval, fun a ha => ?_⟩
  rw [hval]
  have hb := sust_tangent_le_rpow (y := T - a) hx.le (by linarith [ha.2]) one_pos
  simp only [one_rpow, mul_one] at hb
  unfold adaptCost
  rw [div_add' _ _ _ hx0.ne', le_div_iff₀ hx0]
  have : (T + (1 - x) / x) * x = T * x + 1 - x := by field_simp; ring
  rw [this]
  nlinarith

/-- AKMM, p. 763: the minimiser `a = T − 1` is unique. -/
theorem adaptation_unique {x T a : ℝ} (hx : 1 < x) (ha : a ∈ Set.Icc 0 T)
    (hne : a ≠ T - 1) : adaptCost x T (T - 1) < adaptCost x T a := by
  have hx0 : 0 < x := by linarith
  have hb := sust_tangent_lt_rpow (y := T - a) hx (by linarith [ha.2]) one_pos
    (by intro h; exact hne (by linarith))
  simp only [one_rpow, mul_one] at hb
  unfold adaptCost
  simp only [sub_sub_cancel, one_rpow]
  rw [div_add' _ _ _ hx0.ne', div_add' _ _ _ hx0.ne', div_lt_div_iff_of_pos_right hx0]
  nlinarith

/-- AKMM, p. 763 ("so long as `T ≥ 1`"): for `0 ≤ T ≤ 1` no adaptation is optimal and the
reduced-form damage is `T^x/x`, so the linear form holds only for `T ≥ 1`. -/
theorem adaptation_low_T {x T : ℝ} (hx : 1 ≤ x) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    adaptCost x T 0 = T ^ x / x ∧ ∀ a ∈ Set.Icc 0 T, adaptCost x T 0 ≤ adaptCost x T a := by
  have hx0 : 0 < x := by linarith
  refine ⟨by simp [adaptCost], fun a ha => ?_⟩
  unfold adaptCost
  simp only [sub_zero, add_zero]
  rcases hT0.lt_or_eq with hT | hT
  · have hb := sust_tangent_le_rpow (y := T - a) hx (by linarith [ha.2]) hT
    have hpow : T ^ (x - 1) ≤ 1 := Real.rpow_le_one hT0 hT1 (by linarith)
    have hxa : x * T ^ (x - 1) * a ≤ x * a := by
      have := mul_le_mul_of_nonneg_left hpow hx0.le
      nlinarith [ha.1]
    rw [div_add' _ _ _ hx0.ne', div_le_div_iff_of_pos_right hx0]
    nlinarith
  · subst hT
    have ha0 : a = 0 := le_antisymm ha.2 ha.1
    simp [ha0]

end AKMM.Sustainability
