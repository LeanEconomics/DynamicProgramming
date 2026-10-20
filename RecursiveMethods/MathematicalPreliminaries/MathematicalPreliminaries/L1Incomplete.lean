/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MathematicalPreliminaries.Completeness
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# `C[a, b]` with the `L¹` norm is not complete

SLP Exercise 3.6a (for Exercise 3.4f), p. 47.

The ramps `s_n(t) = min{1, max{0, (n + 1)(t − m)}}`, `m = (a + b)/2`, increase with `n`, so their
`L¹` distances are differences of the increasing, bounded integrals `∫ s_n`: the sequence is
Cauchy (`isCauchy_stepRamp`). A continuous `L¹` limit `g` would vanish on `[a, m)`
(`limit_eq_zero_left`) and equal `1` on `(m, b]` (`limit_eq_one_right`), which continuity at `m`
forbids (`not_isComplete_l1`).
-/

open Set Filter Topology MeasureTheory intervalIntegral

namespace StokeyLucasPrescott.MathematicalPreliminaries

variable {a b : ℝ}

/-- A lower bound for an `L¹` integral from a subinterval where `|h| ≥ η`. -/
theorem integral_abs_ge {h : ℝ → ℝ} (hh : Continuous h) {c d η : ℝ} (hac : a ≤ c) (hcd : c ≤ d)
    (hdb : d ≤ b) (hη : ∀ t ∈ Icc c d, η ≤ |h t|) : (d - c) * η ≤ ∫ t in a..b, |h t| := by
  have hab : a ≤ b := hac.trans (hcd.trans hdb)
  have h1 : ∫ t in c..d, |h t| ≤ ∫ t in a..b, |h t| :=
    integral_mono_interval hac hcd hdb
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun _ _ => abs_nonneg _))
      (hh.abs.intervalIntegrable a b)
  have h2 : ∫ t in c..d, η ≤ ∫ t in c..d, |h t| :=
    integral_mono_on hcd intervalIntegrable_const (hh.abs.intervalIntegrable c d) hη
  rw [intervalIntegral.integral_const, smul_eq_mul] at h2
  linarith

/-- The ramp `s_n(t) = min{1, max{0, (n + 1)(t − m)}}`. -/
noncomputable def stepRamp (a b : ℝ) (n : ℕ) : C(Icc a b, ℝ) :=
  ⟨fun t => min 1 (max 0 ((n + 1) * ((t : ℝ) - (a + b) / 2))), by fun_prop⟩

theorem stepRamp_apply (n : ℕ) (t : Icc a b) :
    stepRamp a b n t = min 1 (max 0 ((n + 1) * ((t : ℝ) - (a + b) / 2))) := rfl

theorem stepRamp_nonneg (n : ℕ) (t : Icc a b) : 0 ≤ stepRamp a b n t := by
  rw [stepRamp_apply]
  exact le_min zero_le_one (le_max_left _ _)

theorem stepRamp_le_one (n : ℕ) (t : Icc a b) : stepRamp a b n t ≤ 1 := by
  rw [stepRamp_apply]
  exact min_le_left _ _

theorem stepRamp_mono {n k : ℕ} (hnk : n ≤ k) (t : Icc a b) :
    stepRamp a b n t ≤ stepRamp a b k t := by
  rw [stepRamp_apply, stepRamp_apply]
  refine min_le_min le_rfl ?_
  have hk : (n : ℝ) ≤ k := by exact_mod_cast hnk
  rcases le_total ((t : ℝ) - (a + b) / 2) 0 with h | h
  · rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos (by positivity) h)]
    exact le_max_left _ _
  · exact max_le_max le_rfl (by nlinarith)

theorem stepRamp_left (n : ℕ) (t : Icc a b) (ht : (t : ℝ) ≤ (a + b) / 2) :
    stepRamp a b n t = 0 := by
  rw [stepRamp_apply, max_eq_left (by nlinarith : (n + 1 : ℝ) * ((t : ℝ) - (a + b) / 2) ≤ 0)]
  exact min_eq_right zero_le_one

theorem stepRamp_right (n : ℕ) (t : Icc a b) (ht : (a + b) / 2 + 1 / (n + 1) ≤ t) :
    stepRamp a b n t = 1 := by
  rw [stepRamp_apply]
  have hn : (0 : ℝ) < n + 1 := by positivity
  have : 1 ≤ (n + 1 : ℝ) * ((t : ℝ) - (a + b) / 2) := by
    rw [← div_le_iff₀' hn]
    linarith
  rw [max_eq_right (by linarith), min_eq_left this]

/-- The integrals `∫ₐᵇ s_n`. -/
noncomputable def rampIntegral (hab : a ≤ b) (n : ℕ) : ℝ := ∫ t in a..b, ext hab (stepRamp a b n) t

theorem ext_stepRamp_mono (hab : a ≤ b) {n k : ℕ} (hnk : n ≤ k) (t : ℝ) :
    ext hab (stepRamp a b n) t ≤ ext hab (stepRamp a b k) t := by
  simp only [ext, ContinuousMap.coe_IccExtend, IccExtend_apply]
  exact stepRamp_mono hnk _

/-- For `n ≤ k`, the `L¹` distance is `∫ s_k − ∫ s_n`. -/
theorem l1_stepRamp_sub (hab : a ≤ b) {n k : ℕ} (hnk : n ≤ k) :
    l1 hab (stepRamp a b k - stepRamp a b n) = rampIntegral hab k - rampIntegral hab n := by
  unfold l1 rampIntegral
  rw [← integral_sub ((continuous_ext hab _).intervalIntegrable a b)
    ((continuous_ext hab _).intervalIntegrable a b)]
  refine integral_congr fun t _ => ?_
  rw [ext_sub, abs_of_nonneg (sub_nonneg.2 (ext_stepRamp_mono hab hnk t))]

theorem rampIntegral_mono (hab : a ≤ b) : Monotone (rampIntegral (a := a) (b := b) hab) :=
  fun n k hnk => by
    have := l1_nonneg hab (stepRamp a b k - stepRamp a b n)
    rw [l1_stepRamp_sub hab hnk] at this
    linarith

theorem rampIntegral_le (hab : a ≤ b) (n : ℕ) : rampIntegral hab n ≤ b - a := by
  unfold rampIntegral
  have := integral_mono_on hab ((continuous_ext hab (stepRamp a b n)).intervalIntegrable a b)
    (intervalIntegrable_const (μ := volume) (c := (1 : ℝ))) fun t ht => by
      rw [ext_of_mem hab _ ht]
      exact stepRamp_le_one n _
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at this
  exact this

/-- **The ramps form an `L¹`-Cauchy sequence.** -/
theorem isCauchy_stepRamp (hab : a ≤ b) :
    IsCauchy (fun x y : C(Icc a b, ℝ) => l1 hab (x - y)) (stepRamp a b) := fun ε hε => by
  have hbdd : BddAbove (range (rampIntegral (a := a) (b := b) hab)) :=
    ⟨b - a, by rintro _ ⟨n, rfl⟩; exact rampIntegral_le hab n⟩
  have hlim := tendsto_atTop_ciSup (rampIntegral_mono hab) hbdd
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hlim.cauchySeq ε hε
  refine ⟨N, fun n hn k hk => ?_⟩
  have hd := hN n hn k hk
  rw [Real.dist_eq] at hd
  change l1 hab (stepRamp a b n - stepRamp a b k) < ε
  rcases le_total k n with h | h
  · rw [l1_stepRamp_sub hab h]
    exact (le_abs_self _).trans_lt hd
  · rw [show stepRamp a b n - stepRamp a b k = -(stepRamp a b k - stepRamp a b n) by abel,
      l1_neg, l1_stepRamp_sub hab h]
    rw [abs_sub_comm] at hd
    exact (le_abs_self _).trans_lt hd

/-- Near a point where a continuous function differs from `c`, it stays away from `c`. -/
theorem away_of_ne {h : ℝ → ℝ} (hh : Continuous h) {t₀ c : ℝ} (hne : h t₀ ≠ c) :
    ∃ δ > 0, ∀ t, |t - t₀| < δ → |h t₀ - c| / 2 ≤ |h t - c| := by
  have hpos : 0 < |h t₀ - c| / 2 := half_pos (abs_pos.2 (sub_ne_zero.2 hne))
  obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.1 hh t₀ _ hpos
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have h1 := hball t (by rw [Real.dist_eq]; exact ht)
  rw [Real.dist_eq] at h1
  have := abs_sub_abs_le_abs_sub (h t₀ - c) (h t - c)
  rw [show h t₀ - c - (h t - c) = -(h t - h t₀) by ring, abs_neg] at this
  linarith

/-- The `L¹` limit of the ramps vanishes on `[a, m)`. -/
theorem limit_eq_zero_left (hab : a < b) {g : C(Icc a b, ℝ)}
    (hg : Converges (fun x y : C(Icc a b, ℝ) => l1 hab.le (x - y)) (stepRamp a b) g)
    {t₀ : ℝ} (ht₀a : a ≤ t₀) (ht₀m : t₀ < (a + b) / 2) : ext hab.le g t₀ = 0 := by
  by_contra hne
  obtain ⟨δ, hδ, hnear⟩ := away_of_ne (continuous_ext hab.le g) hne
  set η := |ext hab.le g t₀ - 0| / 2
  have hη : 0 < η := half_pos (abs_pos.2 (by simpa using hne))
  set d := min (t₀ + δ / 2) ((t₀ + (a + b) / 2) / 2)
  have hd : t₀ < d := lt_min (by linarith) (by linarith)
  have hdm : d ≤ (a + b) / 2 := (min_le_right _ _).trans (by linarith)
  have hd1 : d ≤ t₀ + δ / 2 := min_le_left _ _
  obtain ⟨N, hN⟩ := hg ((d - t₀) * η) (mul_pos (sub_pos.2 hd) hη)
  have hlow := integral_abs_ge (h := ext hab.le (stepRamp a b N - g))
    (continuous_ext hab.le _) ht₀a hd.le (hdm.trans (by linarith : (a + b) / 2 ≤ b)) fun t ht => by
      have ht' : t ∈ Icc a b :=
        ⟨ht₀a.trans ht.1, ht.2.trans (hdm.trans (by linarith : (a + b) / 2 ≤ b))⟩
      rw [ext_sub, ext_of_mem hab.le (stepRamp a b N) ht', stepRamp_left N _ (ht.2.trans hdm),
        zero_sub, abs_neg]
      have := hnear t (by
        rw [abs_lt]
        constructor <;> linarith [ht.1, ht.2])
      simpa [η] using this
  have := hN N le_rfl
  have key : (d - t₀) * η ≤ ∫ t in a..b, |ext hab.le (stepRamp a b N - g) t| := by
    convert hlow using 2
    simp [η]
  simp only [l1] at this
  linarith

/-- The `L¹` limit of the ramps equals `1` on `(m, b]`. -/
theorem limit_eq_one_right (hab : a < b) {g : C(Icc a b, ℝ)}
    (hg : Converges (fun x y : C(Icc a b, ℝ) => l1 hab.le (x - y)) (stepRamp a b) g)
    {t₀ : ℝ} (ht₀m : (a + b) / 2 < t₀) (ht₀b : t₀ ≤ b) : ext hab.le g t₀ = 1 := by
  by_contra hne
  obtain ⟨δ, hδ, hnear⟩ := away_of_ne (continuous_ext hab.le g) hne
  set η := |ext hab.le g t₀ - 1| / 2
  have hη : 0 < η := half_pos (abs_pos.2 (sub_ne_zero.2 hne))
  set c := max (t₀ - δ / 2) (((a + b) / 2 + t₀) / 2)
  have hc : c < t₀ := max_lt (by linarith) (by linarith)
  have hcm : (a + b) / 2 < c := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hc1 : t₀ - δ / 2 ≤ c := le_max_left _ _
  -- far enough along, the ramp is `1` on `[c, t₀]`
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (1 / (c - (a + b) / 2))
  have hramp : (a + b) / 2 + 1 / (N₁ + 1) ≤ c := by
    have hpos : 0 < c - (a + b) / 2 := sub_pos.2 hcm
    have : 1 / ((N₁ : ℝ) + 1) ≤ c - (a + b) / 2 := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hpos] at hN₁
      nlinarith
    linarith
  obtain ⟨N₂, hN₂⟩ := hg ((t₀ - c) * η) (mul_pos (sub_pos.2 hc) hη)
  set N := max N₁ N₂
  have hN1 : (a + b) / 2 + 1 / (N + 1) ≤ c := by
    refine le_trans ?_ hramp
    have : (N₁ : ℝ) ≤ N := by exact_mod_cast le_max_left N₁ N₂
    have : 1 / ((N : ℝ) + 1) ≤ 1 / (N₁ + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  have hca : a ≤ c := by linarith
  have hlow := integral_abs_ge (h := ext hab.le (stepRamp a b N - g))
    (continuous_ext hab.le _) hca hc.le ht₀b fun t ht => by
      have ht' : t ∈ Icc a b := ⟨hca.trans ht.1, ht.2.trans ht₀b⟩
      rw [ext_sub, ext_of_mem hab.le (stepRamp a b N) ht', stepRamp_right N _ (hN1.trans ht.1)]
      have := hnear t (by
        rw [abs_lt]
        constructor <;> linarith [ht.1, ht.2])
      rw [abs_sub_comm]
      simpa [η] using this
  have := hN₂ N (le_max_right _ _)
  have key : (t₀ - c) * η ≤ ∫ t in a..b, |ext hab.le (stepRamp a b N - g) t| := hlow
  simp only [l1] at this
  linarith

/-- **Ex 3.6a (Ex 3.4f).** `C[a, b]` with `‖x‖ = ∫ₐᵇ |x(t)| dt` is not complete (`a < b`). -/
theorem not_isComplete_l1 (hab : a < b) :
    ¬ IsCompleteFor fun x y : C(Icc a b, ℝ) => l1 hab.le (x - y) := by
  intro hc
  obtain ⟨g, hg⟩ := hc _ (isCauchy_stepRamp hab.le)
  set m := (a + b) / 2 with hm
  have hcont := (continuous_ext hab.le g).tendsto m
  -- from the left the limit is `0`, from the right `1`
  have hleft : Tendsto (fun k : ℕ => m - (m - a) / (k + 2)) atTop (𝓝 m) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)).const_mul
      (m - a)
    have h2 := tendsto_const_nhds (x := m) |>.sub this
    simp only [mul_zero, sub_zero] at h2
    refine h2.congr fun k => ?_
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    ring
  have hright : Tendsto (fun k : ℕ => m + (b - m) / (k + 2)) atTop (𝓝 m) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)).const_mul
      (b - m)
    have h2 := tendsto_const_nhds (x := m) |>.add this
    simp only [mul_zero, add_zero] at h2
    refine h2.congr fun k => ?_
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    ring
  have h0 : ext hab.le g m = 0 := by
    refine tendsto_nhds_unique (hcont.comp hleft) (tendsto_const_nhds.congr fun k => ?_)
    have hk : (0 : ℝ) < (m - a) / (k + 2) := div_pos (by linarith) (by positivity)
    have hk2 : (m - a) / (k + 2) ≤ m - a := div_le_self (by linarith) (by linarith)
    simp only [Function.comp_apply]
    exact (limit_eq_zero_left hab hg (by linarith) (by linarith)).symm
  have h1 : ext hab.le g m = 1 := by
    refine tendsto_nhds_unique (hcont.comp hright) (tendsto_const_nhds.congr fun k => ?_)
    have hk : (0 : ℝ) < (b - m) / (k + 2) := div_pos (by linarith) (by positivity)
    have hk2 : (b - m) / (k + 2) ≤ b - m := div_le_self (by linarith) (by linarith)
    simp only [Function.comp_apply]
    exact (limit_eq_one_right hab hg (by linarith) (by linarith)).symm
  rw [h0] at h1
  exact zero_ne_one h1

end StokeyLucasPrescott.MathematicalPreliminaries
