/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import StructuralEstimation.MLBRContraction

/-!
# Tools for optimal stopping with i.i.d. offers

Copied from `EconomicDynamics/Applications` (module `ODBasic`, plus `od_integrable_sub` and
`od_setIntegral_Ioi_eq` from module `ODOption`), with the namespace renamed and the names
prefixed `ml_`. Used here for McCall's job search model (Miao Example 12.2.1).

Tools for Miao, §8.1, pp. 231–234, and Exercises 8.1–8.2, p. 288. In the option exercise and
McCall problems the offer is drawn afresh from a fixed distribution `F` each period, so the
continuation value is a number `q`, the value function is `V(z) = max(q, h(z))` for the stopping
payoff `h`, and the Bellman equation reduces to the scalar equation
`q = a + β ∫ max(q, h(z′)) dF(z′)`.

* `ml_od_integrable_of_continuous`: continuous functions are `F`-integrable when `F` is a
  probability measure concentrated on `[0, B]` (the book's offer distribution).
* `ml_od_abs_integral_sub_le`: if `|G(x, z) − G(y, z)| ≤ |x − y|`, then the same holds for the
  integrals; `ml_od_lipschitz_stop`: the scalar Bellman map `x ↦ a + β∫ max(x, h) dF` has modulus
  `β`.
* `ml_od_scalar_fixed`: a map of `ℝ` with modulus `β ∈ (0, 1)` has exactly one fixed point (the
  Contraction Mapping Theorem `ml_br_theorem_3_2` on `ℝ`).
* `ml_od_fixed_le_of_le`: fixed points are monotone in the map.
* `ml_od_integral_max_eq`: `∫ max(q, h) dF = q + ∫ max(h − q, 0) dF`.
* `ml_od_integrable_sub`, `ml_od_setIntegral_Ioi_eq`: `z ↦ z − I` is integrable, and
  `∫_{z > x} (z − x) dF = ∫ max(z − x, 0) dF`.
-/

namespace Miao.StructuralEstimation

open MeasureTheory

/-- Continuous functions are integrable for a probability measure concentrated on `[0, B]`. -/
theorem ml_od_integrable_of_continuous {F : Measure ℝ} [IsProbabilityMeasure F] {B : ℝ}
    (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) {g : ℝ → ℝ} (hg : Continuous g) : Integrable g F := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := B)).exists_bound_of_continuousOn
    hg.continuousOn
  exact Integrable.of_bound hg.aestronglyMeasurable C (hF.mono fun z hz => hC z hz)

/-- The integrals of a family that is `1`-Lipschitz in the parameter are `1`-Lipschitz. -/
theorem ml_od_abs_integral_sub_le {Ω : Type*} [MeasurableSpace Ω] {F : Measure Ω}
    [IsProbabilityMeasure F] {G : ℝ → Ω → ℝ} (hG : ∀ x, Integrable (G x) F)
    (hL : ∀ x y z, |G x z - G y z| ≤ |x - y|) (x y : ℝ) :
    |∫ z, G x z ∂F - ∫ z, G y z ∂F| ≤ |x - y| := by
  rw [← integral_sub (hG x) (hG y)]
  calc |∫ z, (G x z - G y z) ∂F| ≤ ∫ z, |G x z - G y z| ∂F := abs_integral_le_integral_abs
    _ ≤ ∫ _z, |x - y| ∂F :=
        integral_mono ((hG x).sub (hG y)).abs (integrable_const _) fun z => hL x y z
    _ = |x - y| := by simp

/-- The scalar Bellman map `x ↦ a + β ∫ max(x, h(z)) dF(z)` has modulus `β`. -/
theorem ml_od_lipschitz_stop {Ω : Type*} [MeasurableSpace Ω] {F : Measure Ω}
    [IsProbabilityMeasure F] {h : Ω → ℝ} (hh : Integrable h F) (a : ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (x y : ℝ) :
    |(a + β * ∫ z, max x (h z) ∂F) - (a + β * ∫ z, max y (h z) ∂F)| ≤ β * |x - y| := by
  have key := ml_od_abs_integral_sub_le (F := F) (G := fun x z => max x (h z))
    (fun x => (integrable_const x).sup hh) (fun x y z => abs_max_sub_max_le_abs x y (h z)) x y
  rw [show (a + β * ∫ z, max x (h z) ∂F) - (a + β * ∫ z, max y (h z) ∂F)
      = β * (∫ z, max x (h z) ∂F - ∫ z, max y (h z) ∂F) by ring, abs_mul, abs_of_nonneg hβ]
  exact mul_le_mul_of_nonneg_left key hβ

/-- A map of `ℝ` with modulus `β ∈ (0, 1)` has exactly one fixed point (the Contraction Mapping
Theorem, `ml_br_theorem_3_2`, on `ℝ`). -/
theorem ml_od_scalar_fixed {Φ : ℝ → ℝ} {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hΦ : ∀ x y, |Φ x - Φ y| ≤ β * |x - y|) : ∃! q, Φ q = q := by
  obtain ⟨q, hq, huniq, -⟩ := ml_br_theorem_3_2 (S := ℝ) (T := Φ) (β := β)
    ⟨hβ0, hβ1, fun x y => by simpa only [Real.dist_eq] using hΦ x y⟩
  exact ⟨q, hq, huniq⟩

/-- Fixed points are monotone in the map: if `Φ₂ ≤ Φ₁` and `Φ₂` has modulus `β < 1`, the fixed
point of `Φ₂` lies below that of `Φ₁`. -/
theorem ml_od_fixed_le_of_le {Φ₁ Φ₂ : ℝ → ℝ} {β : ℝ} (hβ1 : β < 1)
    (hΦ₂ : ∀ x y, |Φ₂ x - Φ₂ y| ≤ β * |x - y|) (hle : ∀ x, Φ₂ x ≤ Φ₁ x) {q₁ q₂ : ℝ}
    (hq₁ : Φ₁ q₁ = q₁) (hq₂ : Φ₂ q₂ = q₂) : q₂ ≤ q₁ := by
  by_contra hlt
  push Not at hlt
  have h1 : q₂ - q₁ ≤ Φ₂ q₂ - Φ₂ q₁ := by linarith [hle q₁]
  have h2 := (le_abs_self _).trans (hΦ₂ q₂ q₁)
  rw [abs_of_pos (sub_pos.2 hlt)] at h2
  nlinarith

/-- `∫ max(q, h) dF = q + ∫ max(h − q, 0) dF` for a probability measure `F`. -/
theorem ml_od_integral_max_eq {Ω : Type*} [MeasurableSpace Ω] {F : Measure Ω}
    [IsProbabilityMeasure F] {h : Ω → ℝ} (hh : Integrable h F) (q : ℝ) :
    ∫ z, max q (h z) ∂F = q + ∫ z, max (h z - q) 0 ∂F := by
  have hfun : (fun z => max q (h z)) = fun z => q + max (h z - q) 0 := by
    funext z
    rcases le_total q (h z) with hz | hz
    · rw [max_eq_right hz, max_eq_left (by linarith)]; ring
    · rw [max_eq_left hz, max_eq_right (by linarith)]; ring
  have hi : Integrable (fun z => max (h z - q) 0) F :=
    (hh.sub (integrable_const q)).sup (integrable_const 0)
  rw [hfun, integral_add (integrable_const q) hi]
  simp

/-- `z ↦ z − I` is integrable for a probability measure concentrated on `[0, B]`. -/
theorem ml_od_integrable_sub {F : Measure ℝ} [IsProbabilityMeasure F] {B : ℝ}
    (hF : ∀ᵐ z ∂F, z ∈ Set.Icc 0 B) (I : ℝ) : Integrable (fun z => z - I) F :=
  ml_od_integrable_of_continuous hF (continuous_id.sub continuous_const)

/-- `∫_{z > x} (z − x) dF = ∫ max(z − x, 0) dF`. -/
theorem ml_od_setIntegral_Ioi_eq {F : Measure ℝ} (x : ℝ) :
    ∫ z in Set.Ioi x, (z - x) ∂F = ∫ z, max (z - x) 0 ∂F := by
  rw [← integral_indicator measurableSet_Ioi]
  congr 1
  funext z
  by_cases hz : x < z
  · rw [Set.indicator_of_mem (Set.mem_Ioi.2 hz), max_eq_left (by linarith)]
  · rw [Set.indicator_of_notMem (by simpa using hz), max_eq_right (by linarith [not_lt.1 hz])]

end Miao.StructuralEstimation
