/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDriving.Discrepancy
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Topology.EMetricSpace.VariationOnFromTo

/-! # Koksma's inequality in one dimension

Copied from `RQMCMarkov/PointSets` (namespace and imports renamed); see that project for
its documentation.

Post #1 says QMC beats MC when the discrepancy of the point set falls faster than `n^{-1/2}`.
The link between discrepancy and integration error is Koksma's inequality (Koksma 1942;
Niederreiter 1992, Thm 2.9; L'Ecuyer 2016):
`|(1/n) ∑_{i<n} f(xᵢ) - ∫₀¹ f| ≤ V(f) D*ₙ` for `f` of bounded variation on `[0,1]`.

**Results.**
* `abs_sum_indicator_upperSet_sub_le`: for every upper set `U ⊆ ℝ`, the empirical measure of
  `U` and its Lebesgue measure in `(0,1]` differ by at most `D*ₙ`.
* `koksma_monotone`, `koksma_monotoneOn`: Koksma's inequality for monotone `f`, with
  `V(f) = f 1 - f 0`. The proof is the layer-cake formula on both sides
  (`Integrable.integral_eq_integral_Ioc_meas_le` for the Lebesgue side).
* `koksma_sub_monotoneOn`: for `f = p - q` with `p, q` monotone on `[0,1]`, the bound is
  `((p 1 - p 0) + (q 1 - q 0)) D*ₙ`.
* `koksma_boundedVariationOn`: **Koksma's inequality** for `f` of bounded variation on `[0,1]`,
  with `V(f) = totalVariation f = (eVariationOn f [0,1]).toReal`, via the Jordan decomposition
  into positive and negative variations (`variationOnFromTo.add_self_monotoneOn`,
  `variationOnFromTo.sub_self_monotoneOn`).
* `koksma_hasDerivAt`: the `C¹` corollary, with `V(f)` replaced by `∫₀¹ |f'|`, for `f`
  differentiable on `[0,1]` with integrable derivative (proved through the decomposition
  `f = (f 0 + ∫₀ˣ f'⁺) - ∫₀ˣ f'⁻`), and `totalVariation_le_integral_abs_deriv`:
  `V(f) ≤ ∫₀¹ |f'|` (only this inequality is needed for the bound; equality also holds
  classically but is not formalised).

The hypothesis `0 < n` is needed: for `n = 0` the estimator is `0` while `D*₀ = 1`, and the
inequality fails for constant `f ≠ 0`.
-/

namespace RQMCMarkov.MarkovDriving

open MeasureTheory

/-- The total variation `V(f)` of `f` on `[0,1]`, as a real number (the extended-real
`eVariationOn f [0,1]` converted with `toReal`, so `0` when the variation is infinite). -/
noncomputable def totalVariation (f : ℝ → ℝ) : ℝ := (eVariationOn f (Set.Icc 0 1)).toReal

/-- The counting function as a sum of indicators: `#{i < n : x i < t} = ∑ 1_{(-∞,t)}(x i)`. -/
theorem countBelow_eq_sum_indicator (x : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    (countBelow x n t : ℝ) = ∑ i ∈ Finset.range n, (Set.Iio t).indicator 1 (x i) := by
  unfold countBelow
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.cast_ite]
  split_ifs with h
  · rw [Set.indicator_of_mem (show x i ∈ Set.Iio t from h), Nat.cast_one, Pi.one_apply]
  · rw [Set.indicator_of_notMem (show x i ∉ Set.Iio t from h), Nat.cast_zero]

/-- The closed counting function as a sum of indicators: `#{i < n : x i ≤ t}`. -/
theorem countAtMost_eq_sum_indicator (x : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    (countAtMost x n t : ℝ) = ∑ i ∈ Finset.range n, (Set.Iic t).indicator 1 (x i) := by
  unfold countAtMost
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.cast_ite]
  split_ifs with h
  · rw [Set.indicator_of_mem (show x i ∈ Set.Iic t from h), Nat.cast_one, Pi.one_apply]
  · rw [Set.indicator_of_notMem (show x i ∉ Set.Iic t from h), Nat.cast_zero]

/-- At most `n` of the first `n` points lie at or below `t`. -/
theorem countAtMost_le (x : ℕ → ℝ) (n : ℕ) (t : ℝ) : countAtMost x n t ≤ n :=
  (Finset.card_filter_le _ _).trans (Finset.card_range n).le

/-- The right-limit bound `#{i < n : x i ≤ a}/n - a ≤ D*ₙ` holds on all of `[0,1]`. -/
theorem countAtMost_div_sub_le_starDiscrepancy_of_mem (x : ℕ → ℝ) (n : ℕ) {a : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) : (countAtMost x n a : ℝ) / n - a ≤ starDiscrepancy x n := by
  rcases ha.2.lt_or_eq with h | h
  · exact countAtMost_div_sub_le_starDiscrepancy x n ha.1 h
  · have hle : (countAtMost x n a : ℝ) / n ≤ 1 := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · rw [hn, Nat.cast_zero, div_zero]
        exact zero_le_one
      · rw [div_le_one (by exact_mod_cast hn)]
        exact_mod_cast countAtMost_le x n a
    linarith [starDiscrepancy_nonneg x n]

/-- An indicator with value `1` takes values in `[0,1]`. -/
theorem indicator_one_mem_Icc (U : Set ℝ) (y : ℝ) :
    U.indicator (1 : ℝ → ℝ) y ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases h : y ∈ U
  · rw [Set.indicator_of_mem h, Pi.one_apply]
    exact ⟨zero_le_one, le_refl 1⟩
  · rw [Set.indicator_of_notMem h]
    exact ⟨le_refl 0, zero_le_one⟩

/-- **Upper sets.** For every upper set `U ⊆ ℝ` the empirical measure `#{i < n : x i ∈ U}/n`
and the Lebesgue measure of `U ∩ (0,1]` differ by at most `D*ₙ`. -/
theorem abs_sum_indicator_upperSet_sub_le {x : ℕ → ℝ} {n : ℕ} (hx : InUnitIco x n)
    (hn : 0 < n) {U : Set ℝ} (hU : IsUpperSet U) :
    |(∑ i ∈ Finset.range n, U.indicator (1 : ℝ → ℝ) (x i)) / n - volume.real (U ∩ Set.Ioc 0 1)| ≤
      starDiscrepancy x n := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hD := starDiscrepancy_nonneg x n
  by_cases h1 : (1 : ℝ) ∈ U
  · have hSne : (U ∩ Set.Icc (0 : ℝ) 1).Nonempty := ⟨1, h1, zero_le_one, le_refl 1⟩
    have hSbdd : BddBelow (U ∩ Set.Icc (0 : ℝ) 1) := ⟨0, fun y hy => hy.2.1⟩
    have ha0 : 0 ≤ sInf (U ∩ Set.Icc (0 : ℝ) 1) := le_csInf hSne fun y hy => hy.2.1
    have ha1 : sInf (U ∩ Set.Icc (0 : ℝ) 1) ≤ 1 := csInf_le hSbdd ⟨h1, zero_le_one, le_refl 1⟩
    have hlow : ∀ y ∈ U ∩ Set.Icc (0 : ℝ) 1, sInf (U ∩ Set.Icc (0 : ℝ) 1) ≤ y :=
      fun y hy => csInf_le hSbdd hy
    have hup : ∀ y, sInf (U ∩ Set.Icc (0 : ℝ) 1) < y → y ∈ U := by
      intro y hay
      obtain ⟨u, hu, huy⟩ := exists_lt_of_csInf_lt hSne hay
      exact hU huy.le hu.1
    have hvol : volume.real (U ∩ Set.Ioc 0 1) = 1 - sInf (U ∩ Set.Icc (0 : ℝ) 1) := by
      apply le_antisymm
      · calc volume.real (U ∩ Set.Ioc 0 1)
            ≤ volume.real (Set.Icc (sInf (U ∩ Set.Icc (0 : ℝ) 1)) 1) := by
              refine measureReal_mono ?_ measure_Icc_lt_top.ne
              intro y hy
              exact ⟨hlow y ⟨hy.1, hy.2.1.le, hy.2.2⟩, hy.2.2⟩
          _ = 1 - sInf (U ∩ Set.Icc (0 : ℝ) 1) := Real.volume_real_Icc_of_le ha1
      · calc 1 - sInf (U ∩ Set.Icc (0 : ℝ) 1)
            = volume.real (Set.Ioc (sInf (U ∩ Set.Icc (0 : ℝ) 1)) 1) :=
              (Real.volume_real_Ioc_of_le ha1).symm
          _ ≤ volume.real (U ∩ Set.Ioc 0 1) := by
              refine measureReal_mono ?_
                (lt_of_le_of_lt (measure_mono Set.inter_subset_right) measure_Ioc_lt_top).ne
              intro y hy
              exact ⟨hup y hy.1, lt_of_le_of_lt ha0 hy.1, hy.2⟩
    have hsum_lo : (n : ℝ) - countAtMost x n (sInf (U ∩ Set.Icc (0 : ℝ) 1)) ≤
        ∑ i ∈ Finset.range n, U.indicator (1 : ℝ → ℝ) (x i) := by
      rw [countAtMost_eq_sum_indicator]
      have hn' : (n : ℝ) = ∑ _i ∈ Finset.range n, (1 : ℝ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      rw [hn', ← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum fun i hi => ?_
      have hxi := hx i (Finset.mem_range.mp hi)
      by_cases hle : x i ≤ sInf (U ∩ Set.Icc (0 : ℝ) 1)
      · rw [Set.indicator_of_mem (show x i ∈ Set.Iic _ from hle), Pi.one_apply, sub_self]
        exact (indicator_one_mem_Icc U (x i)).1
      · have hmem : x i ∈ U := hup (x i) (lt_of_not_ge hle)
        rw [Set.indicator_of_notMem (show x i ∉ Set.Iic _ from hle), Set.indicator_of_mem hmem,
          Pi.one_apply, sub_zero]
    have hsum_hi : ∑ i ∈ Finset.range n, U.indicator (1 : ℝ → ℝ) (x i) ≤
        (n : ℝ) - countBelow x n (sInf (U ∩ Set.Icc (0 : ℝ) 1)) := by
      rw [countBelow_eq_sum_indicator]
      have hn' : (n : ℝ) = ∑ _i ∈ Finset.range n, (1 : ℝ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      rw [hn', ← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum fun i hi => ?_
      have hxi := hx i (Finset.mem_range.mp hi)
      by_cases hlt : x i < sInf (U ∩ Set.Icc (0 : ℝ) 1)
      · have hnot : x i ∉ U := fun hmem =>
          absurd (hlow (x i) ⟨hmem, hxi.1, hxi.2.le⟩) (not_le.mpr hlt)
        rw [Set.indicator_of_mem (show x i ∈ Set.Iio _ from hlt), Pi.one_apply, sub_self,
          Set.indicator_of_notMem hnot]
      · rw [Set.indicator_of_notMem (show x i ∉ Set.Iio _ from hlt), sub_zero]
        exact (indicator_one_mem_Icc U (x i)).2
    have hA := countAtMost_div_sub_le_starDiscrepancy_of_mem x n
      (a := sInf (U ∩ Set.Icc (0 : ℝ) 1)) ⟨ha0, ha1⟩
    have hB : sInf (U ∩ Set.Icc (0 : ℝ) 1) -
        (countBelow x n (sInf (U ∩ Set.Icc (0 : ℝ) 1)) : ℝ) / n ≤ starDiscrepancy x n := by
      have h1 := neg_le_abs ((countBelow x n (sInf (U ∩ Set.Icc (0 : ℝ) 1)) : ℝ) / n -
        sInf (U ∩ Set.Icc (0 : ℝ) 1))
      have h2 := localDiscrepancy_le_starDiscrepancy x n
        (t := sInf (U ∩ Set.Icc (0 : ℝ) 1)) ⟨ha0, ha1⟩
      unfold localDiscrepancy at h2
      linarith
    have hlo' : ((n : ℝ) - countAtMost x n (sInf (U ∩ Set.Icc (0 : ℝ) 1))) / n ≤
        (∑ i ∈ Finset.range n, U.indicator (1 : ℝ → ℝ) (x i)) / n :=
      div_le_div_of_nonneg_right hsum_lo hpos.le
    have hhi' : (∑ i ∈ Finset.range n, U.indicator (1 : ℝ → ℝ) (x i)) / n ≤
        ((n : ℝ) - countBelow x n (sInf (U ∩ Set.Icc (0 : ℝ) 1))) / n :=
      div_le_div_of_nonneg_right hsum_hi hpos.le
    rw [sub_div, div_self hpos.ne'] at hlo' hhi'
    rw [hvol]
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  · have hnot : ∀ y, y ≤ 1 → y ∉ U := fun y hy hyU => h1 (hU hy hyU)
    have hsum : ∑ i ∈ Finset.range n, U.indicator (1 : ℝ → ℝ) (x i) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      exact Set.indicator_of_notMem (hnot (x i) (hx i (Finset.mem_range.mp hi)).2.le) _
    have hempty : U ∩ Set.Ioc (0 : ℝ) 1 = ∅ :=
      Set.eq_empty_of_forall_notMem fun y hy => hnot y hy.2.2 hy.1
    rw [hsum, hempty, measureReal_empty, zero_div, sub_zero, abs_zero]
    exact hD

/-- The indicator of `(-∞, c]` is antitone. -/
theorem antitone_indicator_Iic (c : ℝ) : Antitone ((Set.Iic c).indicator (1 : ℝ → ℝ)) := by
  intro s s' hss'
  by_cases hs' : s' ∈ Set.Iic c
  · have hs : s ∈ Set.Iic c := le_trans hss' hs'
    rw [Set.indicator_of_mem hs', Set.indicator_of_mem hs, Pi.one_apply, Pi.one_apply]
  · rw [Set.indicator_of_notMem hs']
    exact (indicator_one_mem_Icc _ s).1

/-- `∫₀^V 1_{s ≤ c} ds = c` for `0 ≤ c ≤ V`. -/
theorem integral_indicator_Iic_one {c V : ℝ} (hc0 : 0 ≤ c) (hcV : c ≤ V) :
    ∫ s in (0 : ℝ)..V, (Set.Iic c).indicator (1 : ℝ → ℝ) s = c := by
  rw [intervalIntegral.integral_of_le (hc0.trans hcV), setIntegral_indicator measurableSet_Iic,
    Set.Ioc_inter_Iic, inf_eq_right.mpr hcV]
  simp only [Pi.one_apply]
  rw [setIntegral_const, Real.volume_real_Ioc_of_le hc0, smul_eq_mul, mul_one, sub_zero]

/-- **Layer cake, empirical side.** If `0 ≤ h (x i) ≤ V` for `i < n`, then
`(1/n) ∑ h(xᵢ) = ∫₀^V (1/n) #{i : s ≤ h(xᵢ)} ds`. -/
theorem sum_div_eq_integral_indicator {h : ℕ → ℝ} {n : ℕ} {V : ℝ}
    (hh : ∀ i < n, 0 ≤ h i ∧ h i ≤ V) :
    (∑ i ∈ Finset.range n, h i) / n =
      ∫ s in (0 : ℝ)..V, (∑ i ∈ Finset.range n, (Set.Iic (h i)).indicator (1 : ℝ → ℝ) s) / n := by
  rw [intervalIntegral.integral_div, intervalIntegral.integral_finsetSum
    fun i _ => (antitone_indicator_Iic _).intervalIntegrable]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have := hh i (Finset.mem_range.mp hi)
  exact (integral_indicator_Iic_one this.1 this.2).symm

/-- **Layer cake, Lebesgue side.** For monotone `g`,
`∫₀¹ (g - g 0) = ∫₀^{g 1 - g 0} λ{t ∈ (0,1] : s ≤ g t - g 0} ds`. -/
theorem integral_sub_eq_integral_measureReal {g : ℝ → ℝ} (hg : Monotone g) :
    (∫ t in (0 : ℝ)..1, (g t - g 0)) =
      ∫ s in (0 : ℝ)..(g 1 - g 0), (volume.restrict (Set.Ioc (0 : ℝ) 1)).real
        {a | s ≤ g a - g 0} := by
  have hV : 0 ≤ g 1 - g 0 := sub_nonneg.mpr (hg zero_le_one)
  have hmono : Monotone fun t => g t - g 0 := fun a b hab => sub_le_sub_right (hg hab) _
  have hint : Integrable (fun t => g t - g 0) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (hmono.intervalIntegrable (μ := volume))
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] fun t => g t - g 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact sub_nonneg.mpr (hg ht.1.le)
  have hbdd : (fun t => g t - g 0) ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
      fun _ => g 1 - g 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact sub_le_sub_right (hg ht.2) _
  rw [intervalIntegral.integral_of_le zero_le_one, hint.integral_eq_integral_Ioc_meas_le hnn hbdd,
    intervalIntegral.integral_of_le hV]

/-- **Koksma's inequality for monotone `f`.** For `g` monotone on `ℝ` and `n ≥ 1` points in
`[0,1)`: `|(1/n) ∑ g(xᵢ) - ∫₀¹ g| ≤ (g 1 - g 0) D*ₙ`. -/
theorem koksma_monotone {g : ℝ → ℝ} (hg : Monotone g) {x : ℕ → ℝ} {n : ℕ}
    (hx : InUnitIco x n) (hn : 0 < n) :
    |qmcEstimate g x n - ∫ t in (0 : ℝ)..1, g t| ≤ (g 1 - g 0) * starDiscrepancy x n := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hV : 0 ≤ g 1 - g 0 := sub_nonneg.mpr (hg zero_le_one)
  have hQ : qmcEstimate g x n = (∑ i ∈ Finset.range n, (g (x i) - g 0)) / n + g 0 := by
    unfold qmcEstimate
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, sub_div,
      mul_div_cancel_left₀ _ hpos.ne']
    ring
  have hI : ∫ t in (0 : ℝ)..1, g t = (∫ t in (0 : ℝ)..1, (g t - g 0)) + g 0 := by
    rw [intervalIntegral.integral_sub (hg.intervalIntegrable) intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero, one_smul]
    ring
  have hh : ∀ i < n, 0 ≤ g (x i) - g 0 ∧ g (x i) - g 0 ≤ g 1 - g 0 := fun i hi =>
    ⟨sub_nonneg.mpr (hg (hx i hi).1), sub_le_sub_right (hg (hx i hi).2.le) _⟩
  have hanti : Antitone fun s => (volume.restrict (Set.Ioc (0 : ℝ) 1)).real
      {a | s ≤ g a - g 0} := fun s s' hss' => measureReal_mono fun a ha => le_trans hss' ha
  have hint1 : IntervalIntegrable (fun s => (∑ i ∈ Finset.range n,
      (Set.Iic (g (x i) - g 0)).indicator (1 : ℝ → ℝ) s) / n) volume 0 (g 1 - g 0) := by
    refine Antitone.intervalIntegrable fun s s' hss' => ?_
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ =>
      antitone_indicator_Iic _ hss') hpos.le
  rw [hQ, hI, show ∀ A B C : ℝ, A + C - (B + C) = A - B from fun A B C => by ring,
    sum_div_eq_integral_indicator (h := fun i => g (x i) - g 0) hh,
    integral_sub_eq_integral_measureReal hg,
    ← intervalIntegral.integral_sub hint1 hanti.intervalIntegrable, ← Real.norm_eq_abs]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := g 1 - g 0)
    (C := starDiscrepancy x n) (f := fun s => (∑ i ∈ Finset.range n,
      (Set.Iic (g (x i) - g 0)).indicator (1 : ℝ → ℝ) s) / n -
      (volume.restrict (Set.Ioc (0 : ℝ) 1)).real {a | s ≤ g a - g 0}) ?_
  · rw [sub_zero, abs_of_nonneg hV, mul_comm] at hbound
    exact hbound
  intro s _
  have hU : IsUpperSet {a : ℝ | s ≤ g a - g 0} := fun a b hab ha =>
    le_trans ha (sub_le_sub_right (hg hab) _)
  have hsum : ∑ i ∈ Finset.range n, (Set.Iic (g (x i) - g 0)).indicator (1 : ℝ → ℝ) s =
      ∑ i ∈ Finset.range n, {a : ℝ | s ≤ g a - g 0}.indicator (1 : ℝ → ℝ) (x i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hs : s ≤ g (x i) - g 0
    · rw [Set.indicator_of_mem (show s ∈ Set.Iic (g (x i) - g 0) from hs),
        Set.indicator_of_mem (show x i ∈ {a : ℝ | s ≤ g a - g 0} from hs), Pi.one_apply,
        Pi.one_apply]
    · rw [Set.indicator_of_notMem (show s ∉ Set.Iic (g (x i) - g 0) from hs),
        Set.indicator_of_notMem (show x i ∉ {a : ℝ | s ≤ g a - g 0} from hs)]
  rw [Real.norm_eq_abs, hsum, measureReal_restrict_apply' measurableSet_Ioc]
  exact abs_sum_indicator_upperSet_sub_le hx hn hU

/-- Extending a function monotone on `[0,1]` by its end values gives a monotone function on
`ℝ` that agrees with it on `[0,1]`. -/
theorem monotone_comp_projIcc {g : ℝ → ℝ} (hg : MonotoneOn g (Set.Icc 0 1)) :
    Monotone fun t => g (Set.projIcc (0 : ℝ) 1 zero_le_one t) := fun a b hab =>
  hg (Set.projIcc (0 : ℝ) 1 zero_le_one a).2 (Set.projIcc (0 : ℝ) 1 zero_le_one b).2
    (Set.monotone_projIcc zero_le_one hab)

/-- `g ∘ projIcc` agrees with `g` on `[0,1]`. -/
theorem comp_projIcc_eq {g : ℝ → ℝ} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    g (Set.projIcc (0 : ℝ) 1 zero_le_one t) = g t := by
  rw [Set.projIcc_of_mem zero_le_one ht]

/-- Functions that agree on `[0,1]` have the same QMC error at points of `[0,1)`. -/
theorem qmcError_congr {f g : ℝ → ℝ} (hfg : Set.EqOn f g (Set.Icc 0 1)) {x : ℕ → ℝ} {n : ℕ}
    (hx : InUnitIco x n) :
    qmcEstimate f x n - (∫ t in (0 : ℝ)..1, f t) =
      qmcEstimate g x n - ∫ t in (0 : ℝ)..1, g t := by
  have hQ : qmcEstimate f x n = qmcEstimate g x n := by
    unfold qmcEstimate
    congr 1
    exact Finset.sum_congr rfl fun i hi =>
      hfg (Set.Ico_subset_Icc_self (hx i (Finset.mem_range.mp hi)))
  have hI : ∫ t in (0 : ℝ)..1, f t = ∫ t in (0 : ℝ)..1, g t :=
    intervalIntegral.integral_congr (by rw [Set.uIcc_of_le zero_le_one]; exact hfg)
  rw [hQ, hI]

/-- **Koksma's inequality for `f` monotone on `[0,1]`**:
`|(1/n) ∑ f(xᵢ) - ∫₀¹ f| ≤ (f 1 - f 0) D*ₙ`. -/
theorem koksma_monotoneOn {g : ℝ → ℝ} (hg : MonotoneOn g (Set.Icc 0 1)) {x : ℕ → ℝ} {n : ℕ}
    (hx : InUnitIco x n) (hn : 0 < n) :
    |qmcEstimate g x n - ∫ t in (0 : ℝ)..1, g t| ≤ (g 1 - g 0) * starDiscrepancy x n := by
  have h := koksma_monotone (monotone_comp_projIcc hg) hx hn
  have hc : Set.EqOn g (fun t => g (Set.projIcc (0 : ℝ) 1 zero_le_one t)) (Set.Icc 0 1) :=
    fun t ht => (comp_projIcc_eq ht).symm
  rw [qmcError_congr hc hx]
  rwa [comp_projIcc_eq (g := g) (Set.right_mem_Icc.mpr zero_le_one),
    comp_projIcc_eq (g := g) (Set.left_mem_Icc.mpr zero_le_one)] at h

/-- **Koksma's inequality for differences of monotone functions.** If `f = p - q` on `[0,1]`
with `p, q` monotone on `[0,1]`, then
`|(1/n) ∑ f(xᵢ) - ∫₀¹ f| ≤ ((p 1 - p 0) + (q 1 - q 0)) D*ₙ`. -/
theorem koksma_sub_monotoneOn {f p q : ℝ → ℝ} (hp : MonotoneOn p (Set.Icc 0 1))
    (hq : MonotoneOn q (Set.Icc 0 1)) (hf : Set.EqOn f (p - q) (Set.Icc 0 1)) {x : ℕ → ℝ}
    {n : ℕ} (hx : InUnitIco x n) (hn : 0 < n) :
    |qmcEstimate f x n - ∫ t in (0 : ℝ)..1, f t| ≤
      ((p 1 - p 0) + (q 1 - q 0)) * starDiscrepancy x n := by
  have hpI : IntervalIntegrable p volume 0 1 :=
    MonotoneOn.intervalIntegrable (by rw [Set.uIcc_of_le zero_le_one]; exact hp)
  have hqI : IntervalIntegrable q volume 0 1 :=
    MonotoneOn.intervalIntegrable (by rw [Set.uIcc_of_le zero_le_one]; exact hq)
  have hsplit : qmcEstimate (p - q) x n - (∫ t in (0 : ℝ)..1, (p - q) t) =
      (qmcEstimate p x n - ∫ t in (0 : ℝ)..1, p t) -
        (qmcEstimate q x n - ∫ t in (0 : ℝ)..1, q t) := by
    unfold qmcEstimate
    simp only [Pi.sub_apply]
    rw [Finset.sum_sub_distrib, sub_div, intervalIntegral.integral_sub hpI hqI]
    ring
  rw [qmcError_congr hf hx, hsplit]
  have h1 := koksma_monotoneOn hp hx hn
  have h2 := koksma_monotoneOn hq hx hn
  calc _ ≤ |qmcEstimate p x n - ∫ t in (0 : ℝ)..1, p t| +
        |qmcEstimate q x n - ∫ t in (0 : ℝ)..1, q t| := abs_sub _ _
    _ ≤ _ := by linarith

/-- **Koksma's inequality** (one dimension). For `f` of bounded variation on `[0,1]` and
`n ≥ 1` points in `[0,1)`: `|(1/n) ∑ f(xᵢ) - ∫₀¹ f| ≤ V(f) D*ₙ`. -/
theorem koksma_boundedVariationOn {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc 0 1))
    {x : ℕ → ℝ} {n : ℕ} (hx : InUnitIco x n) (hn : 0 < n) :
    |qmcEstimate f x n - ∫ t in (0 : ℝ)..1, f t| ≤ totalVariation f * starDiscrepancy x n := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.left_mem_Icc.mpr zero_le_one
  have hloc := hf.locallyBoundedVariationOn
  have hadd := variationOnFromTo.add_self_monotoneOn hloc h0
  have hsub := variationOnFromTo.sub_self_monotoneOn hloc h0
  have hp : MonotoneOn (fun t => (variationOnFromTo f (Set.Icc 0 1) 0 t + f t) / 2)
      (Set.Icc 0 1) := fun a ha b hb hab =>
    div_le_div_of_nonneg_right (hadd ha hb hab) zero_le_two
  have hq : MonotoneOn (fun t => (variationOnFromTo f (Set.Icc 0 1) 0 t - f t) / 2)
      (Set.Icc 0 1) := fun a ha b hb hab =>
    div_le_div_of_nonneg_right (hsub ha hb hab) zero_le_two
  have hfpq : Set.EqOn f ((fun t => (variationOnFromTo f (Set.Icc 0 1) 0 t + f t) / 2) -
      fun t => (variationOnFromTo f (Set.Icc 0 1) 0 t - f t) / 2) (Set.Icc 0 1) := by
    intro t _
    simp only [Pi.sub_apply]
    ring
  have h := koksma_sub_monotoneOn hp hq hfpq hx hn
  have hV0 : variationOnFromTo f (Set.Icc 0 1) 0 0 = 0 := variationOnFromTo.self f _ 0
  have hV1 : variationOnFromTo f (Set.Icc 0 1) 0 1 = totalVariation f := by
    rw [variationOnFromTo.eq_of_le f _ zero_le_one, Set.inter_self]
    rfl
  rw [hV0, hV1] at h
  calc _ ≤ _ := h
    _ = totalVariation f * starDiscrepancy x n := by ring

/-- **Koksma's inequality, `C¹` form.** If `f` has derivative `f'` at every point of `[0,1]`
and `f'` is integrable on `[0,1]`, then `|(1/n) ∑ f(xᵢ) - ∫₀¹ f| ≤ (∫₀¹ |f'|) D*ₙ`. -/
theorem koksma_hasDerivAt {f f' : ℝ → ℝ} (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' t) t)
    (hint : IntervalIntegrable f' volume 0 1) {x : ℕ → ℝ} {n : ℕ} (hx : InUnitIco x n)
    (hn : 0 < n) :
    |qmcEstimate f x n - ∫ t in (0 : ℝ)..1, f t| ≤
      (∫ t in (0 : ℝ)..1, |f' t|) * starDiscrepancy x n := by
  have hplus : IntervalIntegrable (fun t => (|f' t| + f' t) / 2) volume 0 1 :=
    (hint.abs.add hint).div_const 2
  have hminus : IntervalIntegrable (fun t => (|f' t| - f' t) / 2) volume 0 1 :=
    (hint.abs.sub hint).div_const 2
  have hsubI : ∀ {a b : ℝ}, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      Set.uIcc a b ⊆ Set.uIcc 0 1 := by
    intro a b ha hb
    rw [Set.uIcc_of_le zero_le_one]
    exact Set.uIcc_subset_Icc ha hb
  -- monotonicity of `t ↦ ∫₀ᵗ φ` for nonnegative integrable `φ`
  have hmonoInt : ∀ φ : ℝ → ℝ, IntervalIntegrable φ volume 0 1 → (∀ t, 0 ≤ φ t) →
      MonotoneOn (fun t => ∫ s in (0 : ℝ)..t, φ s) (Set.Icc 0 1) := by
    intro φ hφ hnn a ha b hb hab
    have hsub := intervalIntegral.integral_interval_sub_left
      (hφ.mono_set (hsubI (Set.left_mem_Icc.mpr zero_le_one) hb))
      (hφ.mono_set (hsubI (Set.left_mem_Icc.mpr zero_le_one) ha))
    have hnonneg : 0 ≤ ∫ s in a..b, φ s := intervalIntegral.integral_nonneg hab fun u _ => hnn u
    linarith
  have hp : MonotoneOn (fun t => f 0 + ∫ s in (0 : ℝ)..t, (|f' s| + f' s) / 2)
      (Set.Icc 0 1) := by
    intro a ha b hb hab
    have := hmonoInt _ hplus (fun t => by
      have := neg_abs_le (f' t)
      linarith) ha hb hab
    simp only at this ⊢
    linarith
  have hq : MonotoneOn (fun t => ∫ s in (0 : ℝ)..t, (|f' s| - f' s) / 2) (Set.Icc 0 1) :=
    hmonoInt _ hminus fun t => by
      have := le_abs_self (f' t)
      linarith
  have hfpq : Set.EqOn f ((fun t => f 0 + ∫ s in (0 : ℝ)..t, (|f' s| + f' s) / 2) -
      fun t => ∫ s in (0 : ℝ)..t, (|f' s| - f' s) / 2) (Set.Icc 0 1) := by
    intro t ht
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.left_mem_Icc.mpr zero_le_one
    have hft : ∫ s in (0 : ℝ)..t, f' s = f t - f 0 := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u hu => hderiv u ?_)
        (hint.mono_set (hsubI h0 ht))
      rw [Set.uIcc_of_le ht.1] at hu
      exact ⟨hu.1, hu.2.trans ht.2⟩
    have hsplit : (∫ s in (0 : ℝ)..t, (|f' s| + f' s) / 2) -
        (∫ s in (0 : ℝ)..t, (|f' s| - f' s) / 2) = ∫ s in (0 : ℝ)..t, f' s := by
      rw [← intervalIntegral.integral_sub (hplus.mono_set (hsubI h0 ht))
        (hminus.mono_set (hsubI h0 ht))]
      exact intervalIntegral.integral_congr fun u _ => by ring
    simp only [Pi.sub_apply]
    linarith
  have h := koksma_sub_monotoneOn hp hq hfpq hx hn
  have htot : (f 0 + ∫ s in (0 : ℝ)..1, (|f' s| + f' s) / 2) -
      (f 0 + ∫ s in (0 : ℝ)..0, (|f' s| + f' s) / 2) +
      ((∫ s in (0 : ℝ)..1, (|f' s| - f' s) / 2) - (∫ s in (0 : ℝ)..0, (|f' s| - f' s) / 2)) =
      ∫ t in (0 : ℝ)..1, |f' t| := by
    rw [intervalIntegral.integral_same, intervalIntegral.integral_same, add_zero, sub_zero,
      add_sub_cancel_left, ← intervalIntegral.integral_add hplus hminus]
    exact intervalIntegral.integral_congr fun u _ => by ring
  beta_reduce at h
  rw [htot] at h
  exact h

/-- **Variation of a differentiable function.** If `f` has derivative `f'` on `[0,1]` and `f'` is
integrable there, then `eVariationOn f [0,1] ≤ ∫₀¹ |f'|`. -/
theorem eVariationOn_le_integral_abs_deriv {f f' : ℝ → ℝ}
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' t) t)
    (hint : IntervalIntegrable f' volume 0 1) :
    eVariationOn f (Set.Icc 0 1) ≤ ENNReal.ofReal (∫ t in (0 : ℝ)..1, |f' t|) := by
  have hsubI : ∀ {a b : ℝ}, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      Set.uIcc a b ⊆ Set.uIcc 0 1 := by
    intro a b ha hb
    rw [Set.uIcc_of_le zero_le_one]
    exact Set.uIcc_subset_Icc ha hb
  refine iSup_le fun ⟨N, u, hu, hus⟩ => ?_
  dsimp only
  have hstep : ∀ i, |f (u (i + 1)) - f (u i)| ≤ ∫ t in (u i)..(u (i + 1)), |f' t| := by
    intro i
    have hle : u i ≤ u (i + 1) := hu (Nat.le_succ i)
    have hFTC : ∫ t in (u i)..(u (i + 1)), f' t = f (u (i + 1)) - f (u i) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hderiv t ?_)
        (hint.mono_set (hsubI (hus i) (hus (i + 1))))
      rw [Set.uIcc_of_le hle] at ht
      exact ⟨(hus i).1.trans ht.1, ht.2.trans (hus (i + 1)).2⟩
    rw [← hFTC]
    exact intervalIntegral.abs_integral_le_integral_abs hle
  have htele : ∑ i ∈ Finset.range N, ∫ t in (u i)..(u (i + 1)), |f' t| =
      ∫ t in (u 0)..(u N), |f' t| :=
    intervalIntegral.sum_integral_adjacent_intervals fun k _ =>
      hint.abs.mono_set (hsubI (hus k) (hus (k + 1)))
  have hmono : ∫ t in (u 0)..(u N), |f' t| ≤ ∫ t in (0 : ℝ)..1, |f' t| :=
    intervalIntegral.integral_mono_interval (hus 0).1 (hu (Nat.zero_le N)) (hus N).2
      (Filter.Eventually.of_forall fun t => abs_nonneg (f' t)) hint.abs
  have hsum : ∑ i ∈ Finset.range N, |f (u (i + 1)) - f (u i)| ≤ ∫ t in (0 : ℝ)..1, |f' t| :=
    (Finset.sum_le_sum fun i _ => hstep i).trans (htele.le.trans hmono)
  have hed : ∀ i ∈ Finset.range N, edist (f (u (i + 1))) (f (u i)) =
      ENNReal.ofReal |f (u (i + 1)) - f (u i)| := fun i _ => by
    rw [edist_dist, Real.dist_eq]
  rw [Finset.sum_congr rfl hed, ← ENNReal.ofReal_sum_of_nonneg fun i _ => abs_nonneg _]
  exact ENNReal.ofReal_le_ofReal hsum

/-- A function with integrable derivative on `[0,1]` has bounded variation there. -/
theorem boundedVariationOn_of_hasDerivAt {f f' : ℝ → ℝ}
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' t) t)
    (hint : IntervalIntegrable f' volume 0 1) : BoundedVariationOn f (Set.Icc 0 1) :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (eVariationOn_le_integral_abs_deriv hderiv hint)

/-- **The `C¹` corollary.** `V(f) ≤ ∫₀¹ |f'|` for `f` with integrable derivative on `[0,1]`, so
Koksma's bound `V(f) D*ₙ` is at most `(∫₀¹ |f'|) D*ₙ` (see also `koksma_hasDerivAt`). -/
theorem totalVariation_le_integral_abs_deriv {f f' : ℝ → ℝ}
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' t) t)
    (hint : IntervalIntegrable f' volume 0 1) :
    totalVariation f ≤ ∫ t in (0 : ℝ)..1, |f' t| :=
  ENNReal.toReal_le_of_le_ofReal
    (intervalIntegral.integral_nonneg zero_le_one fun t _ => abs_nonneg (f' t))
    (eVariationOn_le_integral_abs_deriv hderiv hint)

end RQMCMarkov.MarkovDriving
