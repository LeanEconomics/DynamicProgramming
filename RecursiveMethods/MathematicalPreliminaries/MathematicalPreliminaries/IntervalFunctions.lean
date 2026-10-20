/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-!
# Continuous functions on `[a, b]` and the `L¹` distance

SLP §3.1 works with `C[a, b]`, the continuous functions on a closed interval, under the sup norm
and under `∫ₐᵇ |x(t)| dt`. A function `x ∈ C[a, b]` is a continuous map on the subtype
`Icc a b`; integrals use its continuous extension `ext x` to `ℝ`.

* `integral_pos_of_pos`: a continuous function, nonnegative on `[a, b]` and positive at one point
  of it, has positive integral (`a < b`).
* `l1`, `l1_nonneg`, `l1_eq_zero_iff`, `l1_add_le`, `l1_smul`: the `L¹` size of a continuous
  function is a norm; definiteness uses continuity and `a < b`.
-/

open Set MeasureTheory intervalIntegral

namespace StokeyLucasPrescott.MathematicalPreliminaries

/-- A continuous function on `ℝ`, nonnegative on `[a, b]` and positive at some `t₀ ∈ [a, b]`,
has positive integral over `[a, b]` when `a < b`. -/
theorem integral_pos_of_pos {g : ℝ → ℝ} (hg : Continuous g) {a b t₀ : ℝ} (hab : a < b)
    (hnn : ∀ t ∈ Icc a b, 0 ≤ g t) (ht₀ : t₀ ∈ Icc a b) (hpos : 0 < g t₀) :
    0 < ∫ t in a..b, g t := by
  have hint : IntervalIntegrable g volume a b := hg.intervalIntegrable a b
  have hnn' : 0 ≤ᵐ[volume.restrict (Set.uIoc a b)] g := by
    rw [uIoc_of_le hab.le]
    exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht =>
      hnn t (Ioc_subset_Icc_self ht))
  rw [integral_pos_iff_support_of_nonneg_ae' hnn' hint]
  refine ⟨hab, ?_⟩
  -- the support is open and contains `t₀`, so it meets `(a, b]` in an interval
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_lt continuous_const hg) t₀ hpos
  set δ := ε / 2
  set c := max a (t₀ - δ)
  set d := min b (t₀ + δ)
  have hδ : 0 < δ := half_pos hε
  have hδε : δ < ε := half_lt_self hε
  have hcd : c < d := max_lt (lt_min hab (by linarith [ht₀.1]))
    (lt_min (by linarith [ht₀.2]) (by linarith))
  have hsub : Ioo c d ⊆ Function.support g ∩ Ioc a b := fun s hs => by
    have h1 : c < s := hs.1
    have h2 : s < d := hs.2
    have ha1 : a < s := lt_of_le_of_lt (le_max_left _ _) h1
    have ha2 : t₀ - δ < s := lt_of_le_of_lt (le_max_right _ _) h1
    have hb1 : s < b := lt_of_lt_of_le h2 (min_le_left _ _)
    have hb2 : s < t₀ + δ := lt_of_lt_of_le h2 (min_le_right _ _)
    refine ⟨?_, ha1, hb1.le⟩
    have : s ∈ Metric.ball t₀ ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    exact (hball this).ne'
  calc (0 : ENNReal) < volume (Ioo c d) := by rw [Real.volume_Ioo]; simpa using hcd
    _ ≤ volume (Function.support g ∩ Ioc a b) := measure_mono hsub

variable {a b : ℝ}

/-- The continuous extension of `x ∈ C[a, b]` to `ℝ`. -/
noncomputable def ext (hab : a ≤ b) (x : C(Icc a b, ℝ)) : ℝ → ℝ := ContinuousMap.IccExtend hab x

theorem continuous_ext (hab : a ≤ b) (x : C(Icc a b, ℝ)) : Continuous (ext hab x) :=
  (ContinuousMap.IccExtend hab x).continuous

theorem ext_of_mem (hab : a ≤ b) (x : C(Icc a b, ℝ)) {t : ℝ} (ht : t ∈ Icc a b) :
    ext hab x t = x ⟨t, ht⟩ := by
  simp [ext, IccExtend_of_mem hab x ht]

theorem ext_add (hab : a ≤ b) (x y : C(Icc a b, ℝ)) (t : ℝ) :
    ext hab (x + y) t = ext hab x t + ext hab y t := by
  simp [ext, IccExtend_apply]

theorem ext_smul (hab : a ≤ b) (r : ℝ) (x : C(Icc a b, ℝ)) (t : ℝ) :
    ext hab (r • x) t = r * ext hab x t := by
  simp [ext, IccExtend_apply]

theorem ext_sub (hab : a ≤ b) (x y : C(Icc a b, ℝ)) (t : ℝ) :
    ext hab (x - y) t = ext hab x t - ext hab y t := by
  simp [ext, IccExtend_apply]

/-- The `L¹` size `∫ₐᵇ |x(t)| dt` of `x ∈ C[a, b]`. -/
noncomputable def l1 (hab : a ≤ b) (x : C(Icc a b, ℝ)) : ℝ := ∫ t in a..b, |ext hab x t|

theorem l1_nonneg (hab : a ≤ b) (x : C(Icc a b, ℝ)) : 0 ≤ l1 hab x :=
  integral_nonneg hab fun _ _ => abs_nonneg _

theorem l1_zero (hab : a ≤ b) : l1 hab 0 = 0 := by
  simp [l1, ext, IccExtend_apply]

/-- **Definiteness needs continuity**: `∫ₐᵇ |x| = 0` forces `x = 0` when `a < b`. -/
theorem l1_eq_zero_iff (hab : a < b) (x : C(Icc a b, ℝ)) : l1 hab.le x = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, l1_zero]⟩
  ext ⟨t, ht⟩
  by_contra hne
  have hpos : 0 < |ext hab.le x t| := by
    rw [ext_of_mem hab.le x ht]
    exact abs_pos.2 hne
  have := integral_pos_of_pos (continuous_ext hab.le x).abs hab (fun _ _ => abs_nonneg _) ht hpos
  unfold l1 at h
  linarith

theorem l1_add_le (hab : a ≤ b) (x y : C(Icc a b, ℝ)) :
    l1 hab (x + y) ≤ l1 hab x + l1 hab y := by
  unfold l1
  have hx := ((continuous_ext hab x).abs).intervalIntegrable (μ := volume) a b
  have hy := ((continuous_ext hab y).abs).intervalIntegrable (μ := volume) a b
  rw [← integral_add hx hy]
  refine integral_mono_on hab (((continuous_ext hab (x + y)).abs).intervalIntegrable a b)
    (hx.add hy) fun t _ => ?_
  rw [ext_add]
  exact abs_add_le _ _

theorem l1_smul (hab : a ≤ b) (r : ℝ) (x : C(Icc a b, ℝ)) :
    l1 hab (r • x) = |r| * l1 hab x := by
  unfold l1
  simp_rw [ext_smul, abs_mul]
  exact integral_const_mul _ _

theorem l1_neg (hab : a ≤ b) (x : C(Icc a b, ℝ)) : l1 hab (-x) = l1 hab x := by
  have := l1_smul hab (-1) x
  simpa using this

/-- The `L¹` size is at most `(b − a)` times the sup norm. -/
theorem l1_le_norm (hab : a ≤ b) (x : C(Icc a b, ℝ)) : l1 hab x ≤ (b - a) * ‖x‖ := by
  unfold l1
  have := integral_mono_on hab (((continuous_ext hab x).abs).intervalIntegrable (μ := volume) a b)
    (intervalIntegrable_const (c := ‖x‖)) fun t ht => by
      rw [ext_of_mem hab x ht]
      exact x.norm_coe_le_norm ⟨t, ht⟩
  rw [intervalIntegral.integral_const, smul_eq_mul] at this
  exact this

end StokeyLucasPrescott.MathematicalPreliminaries
