/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MathematicalPreliminaries.Contraction
import MathematicalPreliminaries.IntervalFunctions
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A differential equation by the contraction mapping theorem

SLP Exercise 3.10, pp. 53–54: `dx/ds = f(x(s))`, `x(0) = c`, with `f` Lipschitz with constant
`B`. On `C[0, τ]` (sup norm) the operator `(Tv)(s) = c + ∫₀ˢ f(v(z)) dz`

* maps `C[0, τ]` into itself (`continuous_picardFn`, `picard`; Ex 3.10a);
* is a contraction with modulus `τB` when `τB < 1` (`ex_3_10b`);
* has a unique fixed point, which is differentiable and is the unique solution of the
  differential equation on `[0, τ]` (`ex_3_10c`).
-/

open Set MeasureTheory intervalIntegral

namespace StokeyLucasPrescott.MathematicalPreliminaries

variable {τ : ℝ} {f : ℝ → ℝ} {c : ℝ}

/-- `s ↦ c + ∫₀ˢ f(v(z)) dz`, with `v` extended continuously to `ℝ`. -/
noncomputable def picardFn (hτ : 0 ≤ τ) (f : ℝ → ℝ) (c : ℝ) (v : C(Icc 0 τ, ℝ)) (s : ℝ) : ℝ :=
  c + ∫ z in (0 : ℝ)..s, f (ext hτ v z)

/-- **Ex 3.10a.** `Tv` is continuous. -/
theorem continuous_picardFn (hτ : 0 ≤ τ) (hf : Continuous f) (v : C(Icc 0 τ, ℝ)) :
    Continuous (picardFn hτ f c v) :=
  continuous_const.add (intervalIntegral.continuous_primitive
    (fun a b => (hf.comp (continuous_ext hτ v)).intervalIntegrable a b) 0)

/-- **Ex 3.10a.** The operator `T : C[0, τ] → C[0, τ]`. -/
noncomputable def picard (hτ : 0 ≤ τ) (hf : Continuous f) (c : ℝ) (v : C(Icc 0 τ, ℝ)) :
    C(Icc 0 τ, ℝ) :=
  ⟨fun s => picardFn hτ f c v s, (continuous_picardFn hτ hf v).comp continuous_subtype_val⟩

theorem picard_apply (hτ : 0 ≤ τ) (hf : Continuous f) (v : C(Icc 0 τ, ℝ)) (s : Icc 0 τ) :
    picard hτ hf c v s = c + ∫ z in (0 : ℝ)..s, f (ext hτ v z) := rfl

/-- **Ex 3.10b.** If `|f(a) − f(b)| ≤ B|a − b|` and `0 < τ`, `τB < 1`, then `T` is a contraction
on `C[0, τ]` with modulus `τB`. -/
theorem ex_3_10b {B : ℝ} (hB : 0 < B) (hf : Continuous f)
    (hlip : ∀ a b, |f a - f b| ≤ B * |a - b|) (hτ : 0 < τ) (hτB : τ * B < 1) :
    IsContraction (picard hτ.le hf c) (τ * B) := by
  refine ⟨mul_pos hτ hB, hτB, fun v w => ?_⟩
  refine (ContinuousMap.dist_le (mul_nonneg (mul_pos hτ hB).le dist_nonneg)).2 fun s => ?_
  have hpt : ∀ z, ‖f (ext hτ.le v z) - f (ext hτ.le w z)‖ ≤ B * dist v w := fun z => by
    rw [Real.norm_eq_abs]
    refine (hlip _ _).trans (mul_le_mul_of_nonneg_left ?_ hB.le)
    change |v (projIcc 0 τ hτ.le z) - w (projIcc 0 τ hτ.le z)| ≤ dist v w
    rw [← Real.dist_eq]
    exact ContinuousMap.dist_apply_le_dist _
  have hint : ∀ u : C(Icc 0 τ, ℝ), IntervalIntegrable (fun z => f (ext hτ.le u z)) volume 0 s :=
    fun u => (hf.comp (continuous_ext hτ.le u)).intervalIntegrable _ _
  rw [Real.dist_eq, picard_apply, picard_apply, add_sub_add_left_eq_sub,
    ← intervalIntegral.integral_sub (hint v) (hint w)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := (s : ℝ))
    fun z _ => hpt z
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg s.2.1] at h
  calc _ ≤ B * dist v w * s := h
    _ ≤ B * dist v w * τ := mul_le_mul_of_nonneg_left s.2.2
        (mul_nonneg hB.le dist_nonneg)
    _ = τ * B * dist v w := by ring

/-- **Ex 3.10c.** The unique fixed point `v` of `T` on `C[0, τ]` satisfies `v(0) = c` and is
differentiable on `[0, τ]` (one-sided at the ends) with `v′ = f ∘ v`; any `x`, continuous on
`[0, τ]` with `x(0) = c` and `x′(s) = f(x(s))` on `(0, τ)`, coincides with `v` on `[0, τ]`. -/
theorem ex_3_10c {B : ℝ} (hB : 0 < B) (hf : Continuous f)
    (hlip : ∀ a b, |f a - f b| ≤ B * |a - b|) (hτ : 0 < τ) (hτB : τ * B < 1) :
    ∃ v : C(Icc 0 τ, ℝ), picard hτ.le hf c v = v ∧ ext hτ.le v 0 = c ∧
      (∀ s ∈ Icc 0 τ, HasDerivWithinAt (ext hτ.le v) (f (ext hτ.le v s)) (Icc 0 τ) s) ∧
      ∀ x : ℝ → ℝ, ContinuousOn x (Icc 0 τ) → x 0 = c →
        (∀ s ∈ Ioo 0 τ, HasDerivAt x (f (x s)) s) → ∀ s ∈ Icc 0 τ, x s = ext hτ.le v s := by
  obtain ⟨v, hv, huniq, -⟩ := theorem_3_2 (ex_3_10b (c := c) hB hf hlip hτ hτB)
  -- on `[0, τ]` the fixed point is its own Picard integral
  have hfix : EqOn (ext hτ.le v) (picardFn hτ.le f c v) (Icc 0 τ) := fun s hs => by
    rw [ext_of_mem hτ.le v hs]
    conv_lhs => rw [← hv]
    rfl
  have h0 : (0 : ℝ) ∈ Icc 0 τ := ⟨le_rfl, hτ.le⟩
  refine ⟨v, hv, ?_, fun s hs => ?_, fun x hxc hx0 hxd s hs => ?_⟩
  · rw [hfix h0, picardFn, intervalIntegral.integral_same, add_zero]
  · have hd : HasDerivAt (picardFn hτ.le f c v) (f (ext hτ.le v s)) s :=
      ((hf.comp (continuous_ext hτ.le v)).integral_hasStrictDerivAt 0 s).hasDerivAt.const_add c
    exact hd.hasDerivWithinAt.congr hfix (hfix hs)
  · -- `x` restricted to `[0, τ]` is a fixed point of `T`
    set xv : C(Icc 0 τ, ℝ) :=
      ⟨fun u => x u, hxc.comp_continuous continuous_subtype_val fun u => u.2⟩
    have hxv : picard hτ.le hf c xv = xv := by
      ext u
      rw [picard_apply]
      have hsub : Icc 0 (u : ℝ) ⊆ Icc 0 τ := Icc_subset_Icc le_rfl u.2.2
      have hcongr : ∫ z in (0 : ℝ)..u, f (ext hτ.le xv z) = ∫ z in (0 : ℝ)..u, f (x z) := by
        refine intervalIntegral.integral_congr fun z hz => ?_
        rw [uIcc_of_le u.2.1] at hz
        simp only [ext_of_mem hτ.le xv (hsub hz)]
        rfl
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le u.2.1 (hxc.mono hsub)
        (fun z hz => hxd z ⟨hz.1, hz.2.trans_le u.2.2⟩)
        ((hf.comp_continuousOn (hxc.mono hsub)).intervalIntegrable_of_Icc u.2.1)
      rw [hcongr, hftc, hx0]
      change c + (x u - c) = x u
      ring
    have := huniq xv hxv
    rw [ext_of_mem hτ.le v hs, ← this]
    rfl

end StokeyLucasPrescott.MathematicalPreliminaries
