import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Order.CompletePartialOrder
import Mathlib.Data.Int.Star
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.LawfulXor.Basic
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Bitwise
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # Discrepancy of finite point sets in `[0,1)`

Posts #1-#2 of the VFI Toolkit discourse topic 687 call a point set *low-discrepancy* when the
discrepancy between its empirical distribution and `Uniform(0,1)` falls faster than `n^{-1/2}`.
This module fixes the one-dimensional definitions (Niederreiter 1992, Ch. 2; L'Ecuyer 2016).

**Representation.** A point set of size `n` is the first `n` terms `x 0, …, x (n-1)` of a
sequence `x : ℕ → ℝ`. Sequences (van der Corput) and finite sets (the midpoint rule) then share
one type, and blocks of consecutive terms are `Finset.range` shifts. The hypothesis that the
points lie in `[0,1)` is `InUnitIco x n`. A family `y : Fin n → ℝ` can be used through
`fun i => if h : i < n then y ⟨i, h⟩ else 0`.

**Definitions.**
* `countBelow x n t = #{i < n : x i < t}`, and `countAtMost x n t = #{i < n : x i ≤ t}`;
* `localDiscrepancy x n t = |#{i < n : x i < t}/n - t|`;
* `starDiscrepancy x n = D*ₙ = sup_{t ∈ [0,1]} localDiscrepancy x n t`;
* `qmcEstimate f x n = (1/n) ∑_{i<n} f (x i)`, the QMC estimator of post #1;
* `midpointRule n i = (2i+1)/(2n)`, the stratification QMC point set of post #2.

**Results.**
* `starDiscrepancy_nonneg`, `starDiscrepancy_le_one`: `0 ≤ D*ₙ ≤ 1`.
* `countAtMost_div_sub_le_starDiscrepancy`: the right limits of the local discrepancy are also
  bounded by `D*ₙ`.
* `inv_two_mul_le_starDiscrepancy`: every `n`-point set in `[0,1)` has `D*ₙ ≥ 1/(2n)`. No point
  set does better than order `1/n` (post #1's "faster than `n^{-1/2}`" is at most `n^{-1}`).
* `starDiscrepancy_midpointRule`: the midpoint rule has `D*ₙ = 1/(2n)` exactly, so it is an
  optimal point set (`starDiscrepancy_midpointRule_le`); for `n = 3` it is post #2's
  `{1/6, 1/2, 5/6}` with `D*₃ = 1/6` (`midpointRule_three`, `starDiscrepancy_midpointRule_three`).
-/

namespace RQMCMarkov.PointSets

open Finset

/-- The first `n` terms of `x` lie in `[0,1)`. -/
def InUnitIco (x : ℕ → ℝ) (n : ℕ) : Prop := ∀ i < n, x i ∈ Set.Ico (0 : ℝ) 1

/-- The number of the first `n` points that lie strictly below `t`: `#{i < n : x i < t}`. -/
noncomputable def countBelow (x : ℕ → ℝ) (n : ℕ) (t : ℝ) : ℕ :=
  ((Finset.range n).filter (fun i => x i < t)).card

/-- The number of the first `n` points that lie at or below `t`: `#{i < n : x i ≤ t}`. -/
noncomputable def countAtMost (x : ℕ → ℝ) (n : ℕ) (t : ℝ) : ℕ :=
  ((Finset.range n).filter (fun i => x i ≤ t)).card

/-- The local discrepancy at `t`: `|#{i < n : x i < t}/n - t|`, the gap between the empirical
distribution function of the first `n` points and the uniform one at `t`. -/
noncomputable def localDiscrepancy (x : ℕ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  |(countBelow x n t : ℝ) / n - t|

/-- The star discrepancy `D*ₙ = sup_{t ∈ [0,1]} |#{i < n : x i < t}/n - t|`. -/
noncomputable def starDiscrepancy (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ⨆ t : Set.Icc (0 : ℝ) 1, localDiscrepancy x n t

/-- The QMC estimator `(1/n) ∑_{i<n} f (x i)` of `∫₀¹ f` (post #1). -/
noncomputable def qmcEstimate (f : ℝ → ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range n, f (x i)) / n

/-- The midpoint rule `xᵢ = (2i+1)/(2n)`: the midpoints of the `n` equal strata of `[0,1)`
(post #2's stratification QMC set). -/
noncomputable def midpointRule (n : ℕ) : ℕ → ℝ := fun i => (2 * i + 1) / (2 * n)

/-- At most `n` of the first `n` points lie below `t`. -/
theorem countBelow_le (x : ℕ → ℝ) (n : ℕ) (t : ℝ) : countBelow x n t ≤ n :=
  (Finset.card_filter_le _ _).trans (Finset.card_range n).le

/-- The counting function is monotone in `t`. -/
theorem countBelow_mono (x : ℕ → ℝ) (n : ℕ) {s t : ℝ} (h : s ≤ t) :
    countBelow x n s ≤ countBelow x n t := by
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, lt_of_lt_of_le hi.2 h⟩

/-- The empirical distribution function `#{i < n : x i < t}/n` lies in `[0,1]`. -/
theorem countBelow_div_mem_Icc (x : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    (countBelow x n t : ℝ) / n ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨by positivity, ?_⟩
  rcases Nat.eq_zero_or_pos n with h | h
  · rw [h, Nat.cast_zero, div_zero]
    exact zero_le_one
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast countBelow_le x n t

/-- The local discrepancy at a point of `[0,1]` is at most `1`. -/
theorem localDiscrepancy_le_one (x : ℕ → ℝ) (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    localDiscrepancy x n t ≤ 1 := by
  have h := countBelow_div_mem_Icc x n t
  exact abs_sub_le_iff.mpr ⟨by linarith [h.2, ht.1], by linarith [h.1, ht.2]⟩

/-- For `n ≠ 0` the local discrepancy is `|#{i < n : x i < t} - n t| / n`. -/
theorem localDiscrepancy_eq_abs_div (x : ℕ → ℝ) {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    localDiscrepancy x n t = |(countBelow x n t : ℝ) - n * t| / n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by positivity
  unfold localDiscrepancy
  rw [show (countBelow x n t : ℝ) / n - t = ((countBelow x n t : ℝ) - n * t) / n by
    rw [sub_div, mul_div_cancel_left₀ _ hn0], abs_div, abs_of_pos hpos]

/-- The local discrepancies over `t ∈ [0,1]` are bounded above (by `1`). -/
theorem bddAbove_localDiscrepancy (x : ℕ → ℝ) (n : ℕ) :
    BddAbove (Set.range fun t : Set.Icc (0 : ℝ) 1 => localDiscrepancy x n t) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨t, rfl⟩
  exact localDiscrepancy_le_one x n t.2

/-- Each local discrepancy at `t ∈ [0,1]` is at most the star discrepancy. -/
theorem localDiscrepancy_le_starDiscrepancy (x : ℕ → ℝ) (n : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : localDiscrepancy x n t ≤ starDiscrepancy x n :=
  le_ciSup (bddAbove_localDiscrepancy x n) (⟨t, ht⟩ : Set.Icc (0 : ℝ) 1)

/-- A uniform bound on the local discrepancies over `[0,1]` bounds the star discrepancy. -/
theorem starDiscrepancy_le_of_forall (x : ℕ → ℝ) (n : ℕ) {c : ℝ}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, localDiscrepancy x n t ≤ c) : starDiscrepancy x n ≤ c := by
  have : Nonempty (Set.Icc (0 : ℝ) 1) := ⟨⟨0, Set.left_mem_Icc.mpr zero_le_one⟩⟩
  exact ciSup_le fun t => h t t.2

/-- `0 ≤ D*ₙ`. -/
theorem starDiscrepancy_nonneg (x : ℕ → ℝ) (n : ℕ) : 0 ≤ starDiscrepancy x n :=
  (abs_nonneg _).trans
    (localDiscrepancy_le_starDiscrepancy x n (Set.left_mem_Icc.mpr zero_le_one))

/-- `D*ₙ ≤ 1`. -/
theorem starDiscrepancy_le_one (x : ℕ → ℝ) (n : ℕ) : starDiscrepancy x n ≤ 1 :=
  starDiscrepancy_le_of_forall x n fun _ ht => localDiscrepancy_le_one x n ht

/-- The right limits of the local discrepancy are bounded by `D*ₙ` too: for `a ∈ [0,1)`,
`#{i < n : x i ≤ a}/n - a ≤ D*ₙ`. -/
theorem countAtMost_div_sub_le_starDiscrepancy (x : ℕ → ℝ) (n : ℕ) {a : ℝ} (ha0 : 0 ≤ a)
    (ha1 : a < 1) : (countAtMost x n a : ℝ) / n - a ≤ starDiscrepancy x n := by
  refine _root_.le_of_forall_pos_le_add fun ε hε => ?_
  have hδpos : 0 < min ε (1 - a) := lt_min hε (by linarith)
  have hδε : min ε (1 - a) ≤ ε := min_le_left _ _
  have hδa : min ε (1 - a) ≤ 1 - a := min_le_right _ _
  have hmem : a + min ε (1 - a) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hloc := localDiscrepancy_le_starDiscrepancy x n hmem
  have hcount : countAtMost x n a ≤ countBelow x n (a + min ε (1 - a)) := by
    apply Finset.card_le_card
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, by linarith [hi.2]⟩
  have hc : (countAtMost x n a : ℝ) / n ≤ (countBelow x n (a + min ε (1 - a)) : ℝ) / n :=
    div_le_div_of_nonneg_right (by exact_mod_cast hcount) (Nat.cast_nonneg n)
  have h1 : (countBelow x n (a + min ε (1 - a)) : ℝ) / n - (a + min ε (1 - a)) ≤
      localDiscrepancy x n (a + min ε (1 - a)) := le_abs_self _
  linarith

/-- **Lower bound.** Every set of `n ≥ 1` points in `[0,1)` has star discrepancy at least
`1/(2n)`. -/
theorem inv_two_mul_le_starDiscrepancy {x : ℕ → ℝ} {n : ℕ} (hx : InUnitIco x n) (hn : 0 < n) :
    1 / (2 * n) ≤ starDiscrepancy x n := by
  have h0 := hx 0 hn
  have hlow : x 0 - (countBelow x n (x 0) : ℝ) / n ≤ starDiscrepancy x n := by
    have h1 := neg_le_abs ((countBelow x n (x 0) : ℝ) / n - x 0)
    have h2 := localDiscrepancy_le_starDiscrepancy x n (Set.Ico_subset_Icc_self h0)
    unfold localDiscrepancy at h2
    linarith
  have hup := countAtMost_div_sub_le_starDiscrepancy x n h0.1 h0.2
  have hcnt : countBelow x n (x 0) + 1 ≤ countAtMost x n (x 0) := by
    have hnot : (0 : ℕ) ∉ (Finset.range n).filter (fun i => x i < x 0) := by
      intro h
      rw [Finset.mem_filter] at h
      exact lt_irrefl _ h.2
    unfold countBelow countAtMost
    rw [← Finset.card_insert_of_notMem hnot]
    apply Finset.card_le_card
    intro i hi
    rw [Finset.mem_insert] at hi
    rw [Finset.mem_filter]
    rcases hi with rfl | hi
    · exact ⟨Finset.mem_range.mpr hn, le_refl _⟩
    · rw [Finset.mem_filter] at hi
      exact ⟨hi.1, hi.2.le⟩
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hcntR : (countBelow x n (x 0) : ℝ) + 1 ≤ countAtMost x n (x 0) := by exact_mod_cast hcnt
  have hdiff : 1 / (n : ℝ) ≤ (countAtMost x n (x 0) : ℝ) / n - (countBelow x n (x 0) : ℝ) / n := by
    rw [← sub_div]
    exact div_le_div_of_nonneg_right (by linarith) hpos.le
  rw [show (1 : ℝ) / (2 * n) = (1 / n) / 2 by rw [div_div, mul_comm]]
  linarith

/-- The midpoint-rule points lie in `[0,1)`. -/
theorem midpointRule_mem (n : ℕ) : InUnitIco (midpointRule n) n := by
  intro i hi
  have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi
  have hpos : (0 : ℝ) < 2 * n := by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  change (0 : ℝ) ≤ (2 * i + 1) / (2 * n) ∧ (2 * (i : ℝ) + 1) / (2 * n) < 1
  refine ⟨div_nonneg (by positivity) hpos.le, ?_⟩
  rw [div_lt_one hpos]
  linarith

/-- A midpoint-rule point lies below `t` iff `2i + 1 < 2nt`. -/
theorem midpointRule_lt_iff {n : ℕ} (hn : 0 < n) (i : ℕ) (t : ℝ) :
    midpointRule n i < t ↔ 2 * (i : ℝ) + 1 < 2 * n * t := by
  have hpos : (0 : ℝ) < 2 * n := by positivity
  unfold midpointRule
  rw [div_lt_iff₀ hpos, mul_comm t]

/-- Upper bound on the midpoint-rule count: if `2nt ≤ 2m + 1` then at most `m` points lie
below `t`. -/
theorem countBelow_midpointRule_le {n : ℕ} (hn : 0 < n) {t : ℝ} {m : ℕ}
    (h : 2 * n * t ≤ 2 * (m : ℝ) + 1) : countBelow (midpointRule n) n t ≤ m := by
  calc countBelow (midpointRule n) n t ≤ (Finset.range m).card := by
        apply Finset.card_le_card
        intro i hi
        rw [Finset.mem_filter, midpointRule_lt_iff hn] at hi
        rw [Finset.mem_range]
        have : (i : ℝ) < m := by linarith [hi.2]
        exact_mod_cast this
    _ = m := Finset.card_range m

/-- Lower bound on the midpoint-rule count: if `m ≤ n` and `m < nt + 1/2` then at least `m`
points lie below `t`. -/
theorem le_countBelow_midpointRule {n : ℕ} (hn : 0 < n) {t : ℝ} {m : ℕ} (hmn : m ≤ n)
    (h : (m : ℝ) < n * t + 1 / 2) : m ≤ countBelow (midpointRule n) n t := by
  calc m = (Finset.range m).card := (Finset.card_range m).symm
    _ ≤ countBelow (midpointRule n) n t := by
        apply Finset.card_le_card
        intro i hi
        rw [Finset.mem_range] at hi
        rw [Finset.mem_filter, midpointRule_lt_iff hn, Finset.mem_range]
        have hi' : (i : ℝ) + 1 ≤ m := by exact_mod_cast hi
        exact ⟨lt_of_lt_of_le hi hmn, by linarith⟩

/-- The midpoint rule satisfies `|#{i < n : xᵢ < t} - nt| ≤ 1/2` for every `t ∈ [0,1]`. -/
theorem abs_countBelow_midpointRule_sub_le {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |(countBelow (midpointRule n) n t : ℝ) - n * t| ≤ 1 / 2 := by
  have hn0 : (0 : ℝ) ≤ n * t := mul_nonneg (Nat.cast_nonneg n) ht.1
  have hnt : (n : ℝ) * t ≤ n := by
    have := mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg n)
    linarith
  -- upper bound: `m = ⌊nt + 1/2⌋₊`
  have hA : (countBelow (midpointRule n) n t : ℝ) ≤ n * t + 1 / 2 := by
    have hfl := Nat.floor_le (show (0 : ℝ) ≤ n * t + 1 / 2 by linarith)
    have hlt := Nat.lt_floor_add_one (n * t + 1 / 2 : ℝ)
    have hc := countBelow_midpointRule_le hn (m := ⌊(n : ℝ) * t + 1 / 2⌋₊) (t := t)
      (by linarith)
    have hc' : (countBelow (midpointRule n) n t : ℝ) ≤ ⌊(n : ℝ) * t + 1 / 2⌋₊ := by
      exact_mod_cast hc
    linarith
  -- lower bound: `m = ⌈nt - 1/2⌉₊`
  have hB : n * t - 1 / 2 ≤ (countBelow (midpointRule n) n t : ℝ) := by
    have hmn : ⌈(n : ℝ) * t - 1 / 2⌉₊ ≤ n := Nat.ceil_le.mpr (by linarith)
    have hlt : (⌈(n : ℝ) * t - 1 / 2⌉₊ : ℝ) < n * t + 1 / 2 := by
      rcases le_or_gt 0 ((n : ℝ) * t - 1 / 2) with h | h
      · have := Nat.ceil_lt_add_one h
        linarith
      · rw [Nat.ceil_eq_zero.mpr h.le, Nat.cast_zero]
        linarith
    have hc := le_countBelow_midpointRule hn hmn hlt
    have hc' : (⌈(n : ℝ) * t - 1 / 2⌉₊ : ℝ) ≤ countBelow (midpointRule n) n t := by
      exact_mod_cast hc
    linarith [Nat.le_ceil ((n : ℝ) * t - 1 / 2)]
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- **The midpoint rule has star discrepancy exactly `1/(2n)`** (post #2's stratification QMC
point set). -/
theorem starDiscrepancy_midpointRule {n : ℕ} (hn : 0 < n) :
    starDiscrepancy (midpointRule n) n = 1 / (2 * n) := by
  apply le_antisymm _ (inv_two_mul_le_starDiscrepancy (midpointRule_mem n) hn)
  apply starDiscrepancy_le_of_forall
  intro t ht
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [localDiscrepancy_eq_abs_div _ hn.ne' t,
    show (1 : ℝ) / (2 * n) = (1 / 2) / n by rw [div_div]]
  exact div_le_div_of_nonneg_right (abs_countBelow_midpointRule_sub_le hn ht) hpos.le

/-- The midpoint rule is an optimal `n`-point set: no point set in `[0,1)` has smaller star
discrepancy. -/
theorem starDiscrepancy_midpointRule_le {x : ℕ → ℝ} {n : ℕ} (hx : InUnitIco x n) (hn : 0 < n) :
    starDiscrepancy (midpointRule n) n ≤ starDiscrepancy x n := by
  rw [starDiscrepancy_midpointRule hn]
  exact inv_two_mul_le_starDiscrepancy hx hn

/-- For `n = 3` the midpoint rule is post #2's set `{1/6, 1/2, 5/6}`. -/
theorem midpointRule_three :
    midpointRule 3 0 = 1 / 6 ∧ midpointRule 3 1 = 1 / 2 ∧ midpointRule 3 2 = 5 / 6 := by
  unfold midpointRule
  norm_num

/-- Post #2's stratification set `{1/6, 1/2, 5/6}` has star discrepancy `1/6`. -/
theorem starDiscrepancy_midpointRule_three : starDiscrepancy (midpointRule 3) 3 = 1 / 6 := by
  rw [starDiscrepancy_midpointRule (by norm_num)]
  norm_num

end RQMCMarkov.PointSets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # Koksma's inequality in one dimension

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

namespace RQMCMarkov.PointSets

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

end RQMCMarkov.PointSets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # The van der Corput sequence

Post #2 builds QMC point sets from the Sobol sequence. In one dimension the Sobol sequence is the
base-2 van der Corput sequence (radical inverse): write `k = ∑ⱼ bⱼ 2ʲ` in binary and reflect
the digits about the binary point, `φ(k) = ∑ⱼ bⱼ 2^{-(j+1)}` (van der Corput 1935;
Niederreiter 1992, Ch. 3; L'Ecuyer 2016).

**Definition.** `vanDerCorput 0 = 0` and `vanDerCorput k = (k mod 2)/2 + vanDerCorput (k/2)/2`,
which is the radical inverse read off the binary digits.

**Results.**
* `vanDerCorput_mem_Ico`: every term lies in `[0,1)`.
* `card_vanDerCorput_mem_dyadic`: **net property.** Any `2^m` *consecutive* terms
  `φ(a), …, φ(a + 2^m - 1)` put exactly one point in each dyadic interval
  `[j/2^m, (j+1)/2^m)`. This holds for every start `a`, in particular for the aligned blocks
  starting at a multiple of `2^m` (`card_vanDerCorput_mem_dyadic_aligned`).
* `abs_countBelow_vanDerCorput_sub_le`: `|#{i < n : φ(i) < t} - nt| ≤ log₂ n + 1`, by splitting
  `n` along its binary expansion into blocks of `2^m` consecutive terms.
* `starDiscrepancy_vanDerCorput_le`: `D*ₙ ≤ (⌊log₂ n⌋ + 1)/n`, and
  `starDiscrepancy_vanDerCorput_le_log`: `D*ₙ ≤ 2 (log n + 1)/n` (natural log).
* `abs_qmcError_vanDerCorput_le`: by Koksma, the QMC error for `f` of bounded variation is at
  most `V(f) · 2 (log n + 1)/n`.
* `tendsto_sqrt_mul_qmcError_vanDerCorput`: hence `√n · |QMC error| → 0`, i.e. the van der
  Corput QMC error is `o(n^{-1/2})`, faster than the MC root-mean-square error `σ/√n` (post #1,
  post #2 "QMC/RQMC have faster rates of convergence than MC").
-/

namespace RQMCMarkov.PointSets

open Filter Topology

/-- The base-2 van der Corput (radical-inverse) sequence: `φ(0) = 0` and
`φ(k) = (k mod 2)/2 + φ(⌊k/2⌋)/2`. -/
noncomputable def vanDerCorput : ℕ → ℝ
  | 0 => 0
  | k + 1 => (((k + 1) % 2 : ℕ) : ℝ) / 2 + vanDerCorput ((k + 1) / 2) / 2
decreasing_by omega

/-- The defining recursion of the van der Corput sequence, for every `k`. -/
theorem vanDerCorput_eq (k : ℕ) :
    vanDerCorput k = ((k % 2 : ℕ) : ℝ) / 2 + vanDerCorput (k / 2) / 2 := by
  cases k with
  | zero =>
    rw [Nat.zero_mod, Nat.zero_div, vanDerCorput.eq_1, Nat.cast_zero]
    ring
  | succ k => rw [vanDerCorput]

/-- `φ(2q + b) = b/2 + φ(q)/2` for a binary digit `b`. -/
theorem vanDerCorput_two_mul_add (q b : ℕ) (hb : b < 2) :
    vanDerCorput (2 * q + b) = (b : ℝ) / 2 + vanDerCorput q / 2 := by
  rw [vanDerCorput_eq, show (2 * q + b) % 2 = b by omega, show (2 * q + b) / 2 = q by omega]

/-- The first terms: `φ(1) = 1/2`, `φ(2) = 1/4`, `φ(3) = 3/4`. -/
theorem vanDerCorput_one_two_three :
    vanDerCorput 1 = 1 / 2 ∧ vanDerCorput 2 = 1 / 4 ∧ vanDerCorput 3 = 3 / 4 := by
  have h0 : vanDerCorput 0 = 0 := vanDerCorput.eq_1
  have h1 : vanDerCorput 1 = 1 / 2 := by
    rw [vanDerCorput_eq, show (1 : ℕ) / 2 = 0 by norm_num, h0]
    norm_num
  refine ⟨h1, ?_, ?_⟩
  · rw [vanDerCorput_eq, show (2 : ℕ) / 2 = 1 by norm_num, h1]
    norm_num
  · rw [vanDerCorput_eq, show (3 : ℕ) / 2 = 1 by norm_num, h1]
    norm_num

/-- Every van der Corput point lies in `[0,1)`. -/
theorem vanDerCorput_mem_Ico (k : ℕ) : vanDerCorput k ∈ Set.Ico (0 : ℝ) 1 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [vanDerCorput.eq_1]
      exact ⟨le_refl 0, zero_lt_one⟩
    · have h := ih (k / 2) (Nat.div_lt_self hk (by norm_num))
      have hb : ((k % 2 : ℕ) : ℝ) ≤ 1 := by
        exact_mod_cast Nat.le_of_lt_succ (Nat.mod_lt k (by norm_num))
      have hb0 : (0 : ℝ) ≤ ((k % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
      rw [vanDerCorput_eq]
      exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The first `n` van der Corput points lie in `[0,1)`, for every `n`. -/
theorem vanDerCorput_inUnitIco (n : ℕ) : InUnitIco vanDerCorput n :=
  fun i _ => vanDerCorput_mem_Ico i

/-- The `m`-digit index `⌊2^m φ(k)⌋` is below `2^m`. -/
theorem floor_two_pow_mul_vanDerCorput_lt (m k : ℕ) :
    ⌊(2 : ℝ) ^ m * vanDerCorput k⌋₊ < 2 ^ m := by
  have h := vanDerCorput_mem_Ico k
  have hpos : (0 : ℝ) < 2 ^ m := pow_pos two_pos m
  rw [Nat.floor_lt (mul_nonneg hpos.le h.1), Nat.cast_pow, Nat.cast_ofNat]
  exact mul_lt_of_lt_one_right hpos h.2

/-- The digit recursion: `⌊2^{m+1} φ(k)⌋ = (k mod 2) 2^m + ⌊2^m φ(⌊k/2⌋)⌋`. -/
theorem floor_two_pow_succ_mul_vanDerCorput (m k : ℕ) :
    ⌊(2 : ℝ) ^ (m + 1) * vanDerCorput k⌋₊ =
      k % 2 * 2 ^ m + ⌊(2 : ℝ) ^ m * vanDerCorput (k / 2)⌋₊ := by
  have h : (2 : ℝ) ^ (m + 1) * vanDerCorput k =
      (2 : ℝ) ^ m * vanDerCorput (k / 2) + ((k % 2 * 2 ^ m : ℕ) : ℝ) := by
    rw [vanDerCorput_eq k, pow_succ, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  rw [h, Nat.floor_add_natCast (mul_nonneg (pow_nonneg zero_le_two m)
    (vanDerCorput_mem_Ico _).1), add_comm]

/-- The `m`-digit index determines `k mod 2^m`. -/
theorem mod_eq_of_floor_vanDerCorput_eq (m : ℕ) : ∀ {k k' : ℕ},
    ⌊(2 : ℝ) ^ m * vanDerCorput k⌋₊ = ⌊(2 : ℝ) ^ m * vanDerCorput k'⌋₊ →
      k % 2 ^ m = k' % 2 ^ m := by
  induction m with
  | zero =>
    intro k k' _
    rw [pow_zero, Nat.mod_one, Nat.mod_one]
  | succ m ih =>
    intro k k' h
    rw [floor_two_pow_succ_mul_vanDerCorput, floor_two_pow_succ_mul_vanDerCorput] at h
    have hA := floor_two_pow_mul_vanDerCorput_lt m (k / 2)
    have hA' := floor_two_pow_mul_vanDerCorput_lt m (k' / 2)
    have hbits : k % 2 = k' % 2 ∧ ⌊(2 : ℝ) ^ m * vanDerCorput (k / 2)⌋₊ =
        ⌊(2 : ℝ) ^ m * vanDerCorput (k' / 2)⌋₊ := by
      generalize ⌊(2 : ℝ) ^ m * vanDerCorput (k / 2)⌋₊ = A at h hA ⊢
      generalize ⌊(2 : ℝ) ^ m * vanDerCorput (k' / 2)⌋₊ = A' at h hA' ⊢
      generalize (2 : ℕ) ^ m = P at h hA hA' ⊢
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk <;>
      rcases Nat.mod_two_eq_zero_or_one k' with hk' | hk' <;>
      rw [hk, hk'] at h ⊢ <;> omega
    rw [pow_succ', Nat.mod_mul, Nat.mod_mul, hbits.1, ih hbits.2]

/-- Within any block of `2^m` consecutive terms, the `m`-digit index is injective. -/
theorem floor_vanDerCorput_injOn (m a : ℕ) :
    Set.InjOn (fun r => ⌊(2 : ℝ) ^ m * vanDerCorput (a + r)⌋₊)
      (Finset.range (2 ^ m) : Set ℕ) := by
  intro r hr r' hr' h
  have hr1 : r < 2 ^ m := Finset.mem_range.mp (Finset.mem_coe.mp hr)
  have hr1' : r' < 2 ^ m := Finset.mem_range.mp (Finset.mem_coe.mp hr')
  have hmod : a + r ≡ a + r' [MOD 2 ^ m] := mod_eq_of_floor_vanDerCorput_eq m h
  have := Nat.ModEq.add_left_cancel' a hmod
  rwa [Nat.ModEq, Nat.mod_eq_of_lt hr1, Nat.mod_eq_of_lt hr1'] at this

/-- A point `v ≥ 0` lies in the dyadic interval `[j/2^m, (j+1)/2^m)` iff `⌊2^m v⌋ = j`. -/
theorem mem_dyadic_iff_floor (m j : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    v ∈ Set.Ico ((j : ℝ) / 2 ^ m) (((j : ℝ) + 1) / 2 ^ m) ↔ ⌊(2 : ℝ) ^ m * v⌋₊ = j := by
  have hpos : (0 : ℝ) < 2 ^ m := pow_pos two_pos m
  rw [Nat.floor_eq_iff (mul_nonneg hpos.le hv), Set.mem_Ico, div_le_iff₀ hpos, lt_div_iff₀ hpos,
    mul_comm v]

/-- **Net property.** Any `2^m` consecutive van der Corput terms `φ(a), …, φ(a + 2^m - 1)` put
exactly one point in each dyadic interval `[j/2^m, (j+1)/2^m)`, `j < 2^m`. -/
theorem card_vanDerCorput_mem_dyadic (m a j : ℕ) (hj : j < 2 ^ m) :
    ((Finset.range (2 ^ m)).filter (fun r => vanDerCorput (a + r) ∈
      Set.Ico ((j : ℝ) / 2 ^ m) (((j : ℝ) + 1) / 2 ^ m))).card = 1 := by
  have hmaps : Set.MapsTo (fun r => ⌊(2 : ℝ) ^ m * vanDerCorput (a + r)⌋₊)
      (Finset.range (2 ^ m) : Set ℕ) (Finset.range (2 ^ m) : Set ℕ) := fun r _ =>
    Finset.mem_coe.mpr (Finset.mem_range.mpr (floor_two_pow_mul_vanDerCorput_lt m (a + r)))
  have hsurj := Finset.surjOn_of_injOn_of_card_le _ hmaps (floor_vanDerCorput_injOn m a)
    (le_refl _)
  obtain ⟨r, hr, hrj⟩ := hsurj (Finset.mem_coe.mpr (Finset.mem_range.mpr hj))
  rw [Finset.card_eq_one]
  refine ⟨r, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
  · rw [Finset.mem_filter, mem_dyadic_iff_floor m j (vanDerCorput_mem_Ico _).1]
    exact ⟨Finset.mem_coe.mp hr, hrj⟩
  · intro r' hr'
    rw [Finset.mem_filter, mem_dyadic_iff_floor m j (vanDerCorput_mem_Ico _).1] at hr'
    exact floor_vanDerCorput_injOn m a (Finset.mem_coe.mpr hr'.1) hr (hr'.2.trans hrj.symm)

/-- **Net property, aligned blocks.** The block `φ(k 2^m), …, φ(k 2^m + 2^m - 1)` hits each
dyadic interval of length `2^{-m}` exactly once. -/
theorem card_vanDerCorput_mem_dyadic_aligned (m k j : ℕ) (hj : j < 2 ^ m) :
    ((Finset.range (2 ^ m)).filter (fun r => vanDerCorput (k * 2 ^ m + r) ∈
      Set.Ico ((j : ℝ) / 2 ^ m) (((j : ℝ) + 1) / 2 ^ m))).card = 1 :=
  card_vanDerCorput_mem_dyadic m (k * 2 ^ m) j hj

/-- A block of `2^m` consecutive van der Corput terms has local counting error at most `1`:
`|#{r < 2^m : φ(a + r) < t} - 2^m t| ≤ 1` for `t ∈ [0,1]`. -/
theorem abs_card_block_vanDerCorput_sub_le (m a : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |(((Finset.range (2 ^ m)).filter (fun r => vanDerCorput (a + r) < t)).card : ℝ) -
      2 ^ m * t| ≤ 1 := by
  have hpos : (0 : ℝ) < 2 ^ m := pow_pos two_pos m
  have hmt : 0 ≤ (2 : ℝ) ^ m * t := mul_nonneg hpos.le ht.1
  have hinj := floor_vanDerCorput_injOn m a
  -- upper bound
  have hup : ((Finset.range (2 ^ m)).filter (fun r => vanDerCorput (a + r) < t)).card ≤
      ⌊(2 : ℝ) ^ m * t⌋₊ + 1 := by
    have := Finset.card_le_card_of_injOn (t := Finset.range (⌊(2 : ℝ) ^ m * t⌋₊ + 1))
      (fun r => ⌊(2 : ℝ) ^ m * vanDerCorput (a + r)⌋₊) ?_
      (hinj.mono (Finset.coe_subset.mpr
        (Finset.filter_subset (fun r : ℕ => vanDerCorput (a + r) < t) _)))
    · rwa [Finset.card_range] at this
    intro r hr
    rw [Finset.mem_coe, Finset.mem_filter] at hr
    rw [Finset.mem_coe, Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.floor_le_floor (mul_le_mul_of_nonneg_left hr.2.le hpos.le)
  -- lower bound, through the complement
  have hcompl : ((Finset.range (2 ^ m)).filter (fun r => ¬ vanDerCorput (a + r) < t)).card ≤
      2 ^ m - ⌊(2 : ℝ) ^ m * t⌋₊ := by
    have := Finset.card_le_card_of_injOn (t := Finset.Ico ⌊(2 : ℝ) ^ m * t⌋₊ (2 ^ m))
      (fun r => ⌊(2 : ℝ) ^ m * vanDerCorput (a + r)⌋₊) ?_
      (hinj.mono (Finset.coe_subset.mpr
        (Finset.filter_subset (fun r : ℕ => ¬ vanDerCorput (a + r) < t) _)))
    · rwa [Nat.card_Ico] at this
    intro r hr
    rw [Finset.mem_coe, Finset.mem_filter] at hr
    rw [Finset.mem_coe, Finset.mem_Ico]
    exact ⟨Nat.floor_le_floor (mul_le_mul_of_nonneg_left (not_lt.mp hr.2) hpos.le),
      floor_two_pow_mul_vanDerCorput_lt m (a + r)⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.range (2 ^ m))
    (fun r : ℕ => vanDerCorput (a + r) < t)
  rw [Finset.card_range] at hsplit
  have hj : ⌊(2 : ℝ) ^ m * t⌋₊ ≤ 2 ^ m := by
    apply Nat.floor_le_of_le
    rw [Nat.cast_pow, Nat.cast_ofNat]
    have := mul_le_mul_of_nonneg_left ht.2 hpos.le
    linarith
  have hlow : ⌊(2 : ℝ) ^ m * t⌋₊ ≤
      ((Finset.range (2 ^ m)).filter (fun r => vanDerCorput (a + r) < t)).card := by omega
  have hupR : (((Finset.range (2 ^ m)).filter (fun r => vanDerCorput (a + r) < t)).card : ℝ) ≤
      (⌊(2 : ℝ) ^ m * t⌋₊ : ℝ) + 1 := by exact_mod_cast hup
  have hlowR : (⌊(2 : ℝ) ^ m * t⌋₊ : ℝ) ≤
      (((Finset.range (2 ^ m)).filter (fun r => vanDerCorput (a + r) < t)).card : ℝ) := by
    exact_mod_cast hlow
  have hfl := Nat.floor_le hmt
  have hfl' := Nat.lt_floor_add_one ((2 : ℝ) ^ m * t)
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- Splitting the counting function: the first `N + M` points are the first `N` points and the
block of `M` points starting at `N`. -/
theorem countBelow_add (x : ℕ → ℝ) (N M : ℕ) (t : ℝ) :
    countBelow x (N + M) t =
      countBelow x N t + ((Finset.range M).filter (fun r => x (N + r) < t)).card := by
  unfold countBelow
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.sum_range_add]

/-- **Counting error of the van der Corput sequence.** For `t ∈ [0,1]`,
`|#{i < n : φ(i) < t} - nt| ≤ ⌊log₂ n⌋ + 1`. -/
theorem abs_countBelow_vanDerCorput_sub_le (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |(countBelow vanDerCorput N t : ℝ) - N * t| ≤ Nat.log 2 N + 1 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · rw [show countBelow vanDerCorput 0 t = 0 from rfl, Nat.cast_zero, zero_mul, sub_zero,
        abs_zero]
      positivity
    · have hpow : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 hN.ne'
      have hlt : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
      obtain ⟨N', hN'⟩ : ∃ N', N = N' + 2 ^ Nat.log 2 N := ⟨N - 2 ^ Nat.log 2 N, by omega⟩
      have hN'lt : N' < 2 ^ Nat.log 2 N := by rw [pow_succ] at hlt; omega
      have hblock := abs_card_block_vanDerCorput_sub_le (Nat.log 2 N) N' ht
      have hsplit : (countBelow vanDerCorput N t : ℝ) - N * t =
          ((countBelow vanDerCorput N' t : ℝ) - N' * t) +
          ((((Finset.range (2 ^ Nat.log 2 N)).filter
            (fun r => vanDerCorput (N' + r) < t)).card : ℝ) - 2 ^ Nat.log 2 N * t) := by
        conv_lhs => rw [hN', countBelow_add]
        push_cast
        ring
      have hrest : |(countBelow vanDerCorput N' t : ℝ) - N' * t| ≤ Nat.log 2 N := by
        rcases Nat.eq_zero_or_pos N' with h0 | h0
        · rw [h0, show countBelow vanDerCorput 0 t = 0 from rfl, Nat.cast_zero, zero_mul,
            sub_zero, abs_zero]
          positivity
        · have hlog : Nat.log 2 N' < Nat.log 2 N := Nat.log_lt_of_lt_pow h0.ne' hN'lt
          have hlogR : (Nat.log 2 N' : ℝ) + 1 ≤ Nat.log 2 N := by exact_mod_cast hlog
          exact (ih N' (by omega)).trans hlogR
      rw [hsplit]
      calc _ ≤ |(countBelow vanDerCorput N' t : ℝ) - N' * t| +
            |(((Finset.range (2 ^ Nat.log 2 N)).filter
              (fun r => vanDerCorput (N' + r) < t)).card : ℝ) - 2 ^ Nat.log 2 N * t| :=
            abs_add_le _ _
        _ ≤ _ := by linarith

/-- **Star discrepancy of the van der Corput sequence:** `D*ₙ ≤ (⌊log₂ n⌋ + 1)/n`. -/
theorem starDiscrepancy_vanDerCorput_le {n : ℕ} (hn : 0 < n) :
    starDiscrepancy vanDerCorput n ≤ ((Nat.log 2 n : ℝ) + 1) / n := by
  apply starDiscrepancy_le_of_forall
  intro t ht
  rw [localDiscrepancy_eq_abs_div _ hn.ne' t]
  exact div_le_div_of_nonneg_right (abs_countBelow_vanDerCorput_sub_le n ht) (Nat.cast_nonneg n)

/-- `⌊log₂ n⌋ + 1 ≤ 2 (log n + 1)` for `n ≥ 1` (natural logarithm). -/
theorem natLog_two_add_one_le {n : ℕ} (hn : 0 < n) :
    (Nat.log 2 n : ℝ) + 1 ≤ 2 * (Real.log n + 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : ((2 ^ Nat.log 2 n : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 hn.ne'
  rw [Nat.cast_pow, Nat.cast_ofNat] at hpow
  have hlog := Real.log_le_log (pow_pos two_pos _) hpow
  rw [Real.log_pow] at hlog
  have hl2 := Real.log_two_gt_d9
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hk : (0 : ℝ) ≤ Nat.log 2 n := Nat.cast_nonneg _
  nlinarith

/-- **Star discrepancy of the van der Corput sequence, natural-log form:**
`D*ₙ ≤ 2 (log n + 1)/n`. -/
theorem starDiscrepancy_vanDerCorput_le_log {n : ℕ} (hn : 0 < n) :
    starDiscrepancy vanDerCorput n ≤ 2 * (Real.log n + 1) / n :=
  (starDiscrepancy_vanDerCorput_le hn).trans
    (div_le_div_of_nonneg_right (natLog_two_add_one_le hn) (Nat.cast_nonneg n))

/-- **QMC error of the van der Corput sequence** (Koksma): for `f` of bounded variation on
`[0,1]`, `|(1/n) ∑_{i<n} f(φ(i)) - ∫₀¹ f| ≤ V(f) · 2 (log n + 1)/n`. -/
theorem abs_qmcError_vanDerCorput_le {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc 0 1))
    {n : ℕ} (hn : 0 < n) :
    |qmcEstimate f vanDerCorput n - ∫ t in (0 : ℝ)..1, f t| ≤
      totalVariation f * (2 * (Real.log n + 1) / n) :=
  (koksma_boundedVariationOn hf (vanDerCorput_inUnitIco n) hn).trans
    (mul_le_mul_of_nonneg_left (starDiscrepancy_vanDerCorput_le_log hn) ENNReal.toReal_nonneg)

/-- `(log x + 1)/√x → 0`. -/
theorem tendsto_log_add_one_div_sqrt :
    Tendsto (fun x : ℝ => (Real.log x + 1) / Real.sqrt x) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have h2 : Tendsto (fun x : ℝ => (x ^ (1 / 2 : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2))
  have h := h1.add h2
  rw [add_zero] at h
  refine h.congr fun x => ?_
  rw [Real.sqrt_eq_rpow, add_div, one_div (x ^ (1 / 2 : ℝ))]

/-- **QMC beats MC (the bound).** `√n · 2 (log n + 1)/n → 0`: the van der Corput discrepancy
bound falls faster than the MC rate `n^{-1/2}`. -/
theorem tendsto_sqrt_mul_vanDerCorput_bound :
    Tendsto (fun n : ℕ => Real.sqrt n * (2 * (Real.log n + 1) / n)) atTop (𝓝 0) := by
  have h := (tendsto_log_add_one_div_sqrt.comp tendsto_natCast_atTop_atTop).const_mul 2
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnR.le
  simp only [Function.comp_apply]
  calc 2 * ((Real.log n + 1) / Real.sqrt n)
      = 2 * (Real.log n + 1) * Real.sqrt n / (Real.sqrt n * Real.sqrt n) := by
        rw [mul_div_mul_right _ _ hs.ne', mul_div_assoc]
    _ = Real.sqrt n * (2 * (Real.log n + 1) / n) := by
        rw [hsq]
        ring

/-- **QMC beats MC (the error).** For `f` of bounded variation on `[0,1]`, the van der Corput
QMC error is `o(n^{-1/2})`: `√n · |(1/n) ∑_{i<n} f(φ(i)) - ∫₀¹ f| → 0`. MC has root-mean-square
error exactly `σ(f)/√n`, so it is beaten whenever `σ(f) > 0`. -/
theorem tendsto_sqrt_mul_qmcError_vanDerCorput {f : ℝ → ℝ}
    (hf : BoundedVariationOn f (Set.Icc 0 1)) :
    Tendsto (fun n : ℕ => Real.sqrt n * |qmcEstimate f vanDerCorput n - ∫ t in (0 : ℝ)..1, f t|)
      atTop (𝓝 0) := by
  have h := tendsto_sqrt_mul_vanDerCorput_bound.const_mul (totalVariation f)
  rw [mul_zero] at h
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ h
  filter_upwards [eventually_gt_atTop 0] with n hn
  have := mul_le_mul_of_nonneg_left (abs_qmcError_vanDerCorput_le hf hn)
    (Real.sqrt_nonneg (n : ℝ))
  calc _ ≤ _ := this
    _ = _ := by ring

end RQMCMarkov.PointSets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Monte Carlo: unbiasedness, variance `σ²/n`, RMSE `n^{-1/2}`, CLT (post #1)

Post #1 introduces the Monte Carlo estimator `X̄ₙ = (1/n) Σᵢ f(Xᵢ)` for i.i.d. draws `Xᵢ`, says
that its error is of order `n^{-1/2}`, that it is asymptotically normal, and that it offers no
worst-case guarantee: "on rare occasion we will be very unlucky in our random draw and get, e.g.,
that all `n = 10` draws of our `U(0,1)` are less than 0.1".

**Choice of the uniform law.** The uniform law on `[0,1)` is `uniformIco = volume.restrict
(Ico 0 1)`, and on `[0,1)^s` it is `uniformCube s = Measure.pi fun _ ↦ uniformIco` on
`Fin s → ℝ`. Points live in `ℝ` (resp. `Fin s → ℝ`) rather than in a subtype, so that the shifts
and affine maps of the later modules are ordinary real functions.

**Estimator.** `sampleMean n f x = (n)⁻¹ * Σᵢ f (xᵢ)` for a point set `x : Fin n → E`; the random
estimator is `ω ↦ sampleMean n f (fun i ↦ X i ω)`.

## Main results

The general results take independent points `X i` whose laws `νᵢ = P.map (X i)` average to `μ`,
`Σᵢ νᵢ = n • μ` (identically distributed points, stratified points, ...):

* `integral_sampleMean_of_sum_map_eq`: the estimator is unbiased (no independence needed);
* `variance_sampleMean_of_sum_map_eq`: with independence, `Var = n⁻² Σᵢ Var_{νᵢ}(f)`;
* `variance_sampleMean_le_of_sum_map_eq`: with independence, `Var ≤ Var_μ(f) / n`, the MC
  variance. Independent points whose laws average to `μ` never do worse than MC.

Monte Carlo (post #1), i.i.d. draws with law `μ`:

* `integral_sampleMean_iid`: `E[X̄ₙ] = ∫ f dμ`;
* `variance_sampleMean_iid`: `Var(X̄ₙ) = σ² / n`;
* `rmse_sampleMean_iid`: `√E[(X̄ₙ − μ)²] = σ / √n`, the `n^{-1/2}` rate;
* `tendstoInDistribution_sampleMean_iid`: the CLT `√n (X̄ₙ − μ) ⇒ N(0, σ²)`, from Mathlib's
  `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`;
* `measure_all_draws_lt_tenth`, `measure_all_draws_lt_tenth_pos`: for i.i.d. `U[0,1)` draws,
  `P(all n draws < 1/10) = (1/10)ⁿ > 0`;
* `measure_sampleMean_far_pos`: hence for every `n ≥ 1`, `P(|X̄ₙ − 1/2| > 2/5) ≥ (1/10)ⁿ > 0`:
  MC has no worst-case error bound below `2/5`, for any sample size.
-/

namespace RQMCMarkov.PointSets

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

/-- The uniform law on `[0,1)`: Lebesgue measure restricted to `Ico 0 1`. -/
noncomputable abbrev uniformIco : Measure ℝ := volume.restrict (Ico (0 : ℝ) 1)

/-- `uniformIco` is a probability measure. -/
theorem isProbabilityMeasure_uniformIco : IsProbabilityMeasure uniformIco :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ico, sub_zero, ENNReal.ofReal_one]⟩

/-- The uniform law on the unit cube `[0,1)^s`, on `Fin s → ℝ`. -/
noncomputable abbrev uniformCube (s : ℕ) : Measure (Fin s → ℝ) :=
  Measure.pi fun _ ↦ uniformIco

/-- `uniformCube s` is a probability measure. -/
theorem isProbabilityMeasure_uniformCube (s : ℕ) : IsProbabilityMeasure (uniformCube s) := by
  have := isProbabilityMeasure_uniformIco
  exact Measure.pi.instIsProbabilityMeasure _

/-- The sample mean `(1/n) Σᵢ f (xᵢ)` of `f` over a point set `x : Fin n → E`. -/
noncomputable def sampleMean {E : Type*} (n : ℕ) (f : E → ℝ) (x : Fin n → E) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, f (x i)

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {mE : MeasurableSpace E}

/-- If the laws of the points sum to `n • μ`, each law is at most `n • μ`. -/
theorem map_le_of_sum_map_eq {n : ℕ} {P : Measure Ω} {X : Fin n → Ω → E} {μ : Measure E}
    (hμ : ∑ i, P.map (X i) = (n : ℝ≥0∞) • μ) (i : Fin n) : P.map (X i) ≤ (n : ℝ≥0∞) • μ := by
  rw [← hμ]
  exact Finset.single_le_sum (f := fun j ↦ P.map (X j)) (fun j _ ↦ Measure.zero_le _)
    (Finset.mem_univ i)

/-- If the laws of the points sum to `n • μ`, a `μ`-integrable `f` is integrable for each law. -/
theorem integrable_map_of_sum_map_eq {n : ℕ} {P : Measure Ω} {X : Fin n → Ω → E}
    {μ : Measure E} (hμ : ∑ i, P.map (X i) = (n : ℝ≥0∞) • μ) {f : E → ℝ} (hf : Integrable f μ)
    (i : Fin n) : Integrable f (P.map (X i)) :=
  (hf.smul_measure (ENNReal.natCast_ne_top n)).mono_measure (map_le_of_sum_map_eq hμ i)

/-- If the laws of the points sum to `n • μ`, an `f ∈ L^p(μ)` is in `L^p` of each law. -/
theorem memLp_map_of_sum_map_eq {n : ℕ} {P : Measure Ω} {X : Fin n → Ω → E}
    {μ : Measure E} (hμ : ∑ i, P.map (X i) = (n : ℝ≥0∞) • μ) {f : E → ℝ} {p : ℝ≥0∞}
    (hf : MemLp f p μ) (i : Fin n) : MemLp f p (P.map (X i)) :=
  (hf.smul_measure (ENNReal.natCast_ne_top n)).mono_measure (map_le_of_sum_map_eq hμ i)

/-- **Unbiasedness from averaged marginals.** If the laws of the points `X i` average to `μ`
(`Σᵢ P.map (X i) = n • μ`, no assumption on the joint law), then
`E[(1/n) Σᵢ f(Xᵢ)] = ∫ f dμ` for every `μ`-integrable `f`. -/
theorem integral_sampleMean_of_sum_map_eq {n : ℕ} (hn : n ≠ 0) {P : Measure Ω}
    {X : Fin n → Ω → E} {μ : Measure E} (hX : ∀ i, AEMeasurable (X i) P)
    (hμ : ∑ i, P.map (X i) = (n : ℝ≥0∞) • μ) {f : E → ℝ} (hf : Integrable f μ) :
    ∫ ω, sampleMean n f (fun i ↦ X i ω) ∂P = ∫ x, f x ∂μ := by
  have hi := integrable_map_of_sum_map_eq hμ hf
  have hcomp : ∀ i, ∫ ω, f (X i ω) ∂P = ∫ x, f x ∂(P.map (X i)) := fun i ↦
    (integral_map (hX i) (hi i).aestronglyMeasurable).symm
  have hic : ∀ i, Integrable (fun ω ↦ f (X i ω)) P := fun i ↦
    (integrable_map_measure (hi i).aestronglyMeasurable (hX i)).1 (hi i)
  unfold sampleMean
  change ∫ ω, (n : ℝ)⁻¹ * ∑ i, f (X i ω) ∂P = _
  rw [integral_const_mul, integral_finsetSum _ (fun i _ ↦ hic i),
    Finset.sum_congr rfl (fun i _ ↦ hcomp i),
    ← integral_finsetSum_measure (fun i _ ↦ hi i), hμ, integral_smul_measure,
    ENNReal.toReal_natCast, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn),
    one_mul]

/-- **Variance from averaged marginals, independent points.** For independent points `X i`,
`Var((1/n) Σᵢ f(Xᵢ)) = n⁻² Σᵢ Var_{νᵢ}(f)`, where `νᵢ = P.map (X i)`. -/
theorem variance_sampleMean_of_sum_map_eq {n : ℕ} {P : Measure Ω}
    {X : Fin n → Ω → E} {μ : Measure E} (hX : ∀ i, AEMeasurable (X i) P)
    (hind : iIndepFun X P) (hμ : ∑ i, P.map (X i) = (n : ℝ≥0∞) • μ) {f : E → ℝ}
    (hf : MemLp f 2 μ) :
    Var[fun ω ↦ sampleMean n f (fun i ↦ X i ω); P] =
      ((n : ℝ)⁻¹) ^ 2 * ∑ i, Var[f; P.map (X i)] := by
  have hL := memLp_map_of_sum_map_eq hμ hf
  have hLc : ∀ i, MemLp (fun ω ↦ f (X i ω)) 2 P := fun i ↦
    (memLp_map_measure_iff (hL i).aestronglyMeasurable (hX i)).1 (hL i)
  have hind' : iIndepFun (fun i ↦ f ∘ X i) P :=
    hind.comp₀ (fun _ ↦ f) hX (fun i ↦ (hL i).aestronglyMeasurable.aemeasurable)
  unfold sampleMean
  rw [variance_const_mul]
  congr 1
  have hsum : (fun ω ↦ ∑ i, f (X i ω)) = ∑ i, (fun ω ↦ f (X i ω)) := by
    funext ω
    rw [Finset.sum_apply]
  rw [hsum, IndepFun.variance_sum (fun i _ ↦ hLc i)
    (fun i _ j _ hij ↦ hind'.indepFun hij)]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [variance_map (hL i).aestronglyMeasurable.aemeasurable (hX i)]
  rfl

/-- **Independent points whose laws average to `μ` never do worse than MC.** For independent
points `X i` with `Σᵢ P.map (X i) = n • μ`, `Var((1/n) Σᵢ f(Xᵢ)) ≤ Var_μ(f) / n`. -/
theorem variance_sampleMean_le_of_sum_map_eq {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ}
    (hn : n ≠ 0) {X : Fin n → Ω → E} {μ : Measure E} (hX : ∀ i, AEMeasurable (X i) P)
    (hind : iIndepFun X P) (hμ : ∑ i, P.map (X i) = (n : ℝ≥0∞) • μ) {f : E → ℝ}
    (hf : MemLp f 2 μ) :
    Var[fun ω ↦ sampleMean n f (fun i ↦ X i ω); P] ≤ Var[f; μ] / n := by
  have hL := memLp_map_of_sum_map_eq hμ hf
  set m := ∫ x, f x ∂μ with hm
  have hle : ∀ i, Var[f; P.map (X i)] ≤ ∫ x, (f x - m) ^ 2 ∂(P.map (X i)) := by
    intro i
    rw [← variance_sub_const (hL i).aestronglyMeasurable m]
    exact variance_le_expectation_sq ((hL i).aestronglyMeasurable.sub aestronglyMeasurable_const)
  have hsq : ∀ i, Integrable (fun x ↦ (f x - m) ^ 2) (P.map (X i)) := fun i ↦
    ((hL i).sub (memLp_const m)).integrable_sq
  have hsum : ∑ i, ∫ x, (f x - m) ^ 2 ∂(P.map (X i)) = n * Var[f; μ] := by
    rw [← integral_finsetSum_measure (fun i _ ↦ hsq i), hμ, integral_smul_measure,
      ENNReal.toReal_natCast, smul_eq_mul,
      variance_eq_integral hf.aestronglyMeasurable.aemeasurable]
  rw [variance_sampleMean_of_sum_map_eq hX hind hμ hf]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  calc ((n : ℝ)⁻¹) ^ 2 * ∑ i, Var[f; P.map (X i)]
      ≤ ((n : ℝ)⁻¹) ^ 2 * ∑ i, ∫ x, (f x - m) ^ 2 ∂(P.map (X i)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ hle i) (sq_nonneg _)
    _ = Var[f; μ] / n := by
        rw [hsum]
        field_simp

/-- Identically distributed points have laws summing to `n • μ`. -/
theorem sum_map_eq_of_hasLaw {n : ℕ} {P : Measure Ω} {X : Fin n → Ω → E} {μ : Measure E}
    (hlaw : ∀ i, HasLaw (X i) μ P) : ∑ i, P.map (X i) = (n : ℝ≥0∞) • μ := by
  rw [Finset.sum_congr rfl (fun i _ ↦ (hlaw i).map_eq), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ≥0∞]

/-- **MC is unbiased** (post #1): for draws `Xᵢ` with law `μ` (no assumption on the joint law),
`E[X̄ₙ] = ∫ f dμ`. -/
theorem integral_sampleMean_iid {n : ℕ} (hn : n ≠ 0) {P : Measure Ω} {X : Fin n → Ω → E}
    {μ : Measure E} (hlaw : ∀ i, HasLaw (X i) μ P) {f : E → ℝ} (hf : Integrable f μ) :
    ∫ ω, sampleMean n f (fun i ↦ X i ω) ∂P = ∫ x, f x ∂μ :=
  integral_sampleMean_of_sum_map_eq hn (fun i ↦ (hlaw i).aemeasurable)
    (sum_map_eq_of_hasLaw hlaw) hf

/-- **MC variance** (post #1): for i.i.d. draws with law `μ`, `Var(X̄ₙ) = σ² / n` where
`σ² = Var_μ(f)`. -/
theorem variance_sampleMean_iid {n : ℕ} {P : Measure Ω} {X : Fin n → Ω → E}
    {μ : Measure E} (hlaw : ∀ i, HasLaw (X i) μ P) (hind : iIndepFun X P) {f : E → ℝ}
    (hf : MemLp f 2 μ) :
    Var[fun ω ↦ sampleMean n f (fun i ↦ X i ω); P] = Var[f; μ] / n := by
  rw [variance_sampleMean_of_sum_map_eq (fun i ↦ (hlaw i).aemeasurable) hind
    (sum_map_eq_of_hasLaw hlaw) hf, Finset.sum_congr rfl (fun i _ ↦ by rw [(hlaw i).map_eq]),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    rw [Nat.cast_zero, inv_zero, div_zero]
    ring
  · have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 h.ne'
    field_simp

/-- **MC root-mean-square error** (post #1): for i.i.d. draws with law `μ` and `n ≥ 1`,
`√E[(X̄ₙ − ∫ f dμ)²] = σ / √n`, the `n^{-1/2}` rate. -/
theorem rmse_sampleMean_iid {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : n ≠ 0)
    {X : Fin n → Ω → E}
    {μ : Measure E} (hlaw : ∀ i, HasLaw (X i) μ P) (hind : iIndepFun X P) {f : E → ℝ}
    (hf : MemLp f 2 μ) :
    Real.sqrt (∫ ω, (sampleMean n f (fun i ↦ X i ω) - ∫ x, f x ∂μ) ^ 2 ∂P) =
      Real.sqrt Var[f; μ] / Real.sqrt n := by
  have hL : ∀ i, MemLp f 2 (P.map (X i)) := fun i ↦ by rw [(hlaw i).map_eq]; exact hf
  have hμP : IsProbabilityMeasure μ := by
    rw [← (hlaw ⟨0, Nat.pos_of_ne_zero hn⟩).map_eq]
    infer_instance
  have hmeas : AEMeasurable (fun ω ↦ sampleMean n f (fun i ↦ X i ω)) P := by
    unfold sampleMean
    refine AEMeasurable.const_mul ?_ _
    exact Finset.aemeasurable_fun_sum _ (fun i _ ↦
      (hL i).aestronglyMeasurable.aemeasurable.comp_aemeasurable (hlaw i).aemeasurable)
  rw [← integral_sampleMean_iid hn hlaw (hf.integrable one_le_two), ← variance_eq_integral hmeas,
    variance_sampleMean_iid hlaw hind hf, Real.sqrt_div' _ (Nat.cast_nonneg n)]

/-- **MC central limit theorem** (post #2: "If we were to use standard MC, the asymptotic
distribution of the estimates would be normally distributed"). For an i.i.d. sequence `X k` with
law `μ` and `f ∈ L²(μ)`, `√n (X̄ₙ − ∫ f dμ)` converges in distribution to `N(0, σ²)`. A
restatement of Mathlib's `tendstoInDistribution_inv_sqrt_mul_sum_sub`. -/
theorem tendstoInDistribution_sampleMean_iid {P : Measure Ω} [IsProbabilityMeasure P] {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : ℕ → Ω → E}
    {μ : Measure E} (hlaw : ∀ k, HasLaw (X k) μ P) (hind : iIndepFun X P) {f : E → ℝ}
    (hf : MemLp f 2 μ) {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 Var[f; μ].toNNReal) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ Real.sqrt n * (sampleMean n f (fun i : Fin n ↦ X i ω) - ∫ x, f x ∂μ))
      atTop Z (fun _ ↦ P) P' := by
  have hL : ∀ k, MemLp f 2 (P.map (X k)) := fun k ↦ by rw [(hlaw k).map_eq]; exact hf
  have hfm : ∀ k, AEMeasurable f (P.map (X k)) := fun k ↦
    (hL k).aestronglyMeasurable.aemeasurable
  set Y : ℕ → Ω → ℝ := fun k ω ↦ f (X k ω) with hY
  have hident : ∀ k, IdentDistrib (Y k) (Y 0) P P := by
    intro k
    have h0 : IdentDistrib (X k) (X 0) P P :=
      ⟨(hlaw k).aemeasurable, (hlaw 0).aemeasurable, by rw [(hlaw k).map_eq, (hlaw 0).map_eq]⟩
    exact h0.comp_of_aemeasurable (hfm k)
  have hindY : iIndepFun Y P := hind.comp₀ (fun _ ↦ f) (fun k ↦ (hlaw k).aemeasurable) hfm
  have hY0 : MemLp (Y 0) 2 P :=
    (memLp_map_measure_iff (hL 0).aestronglyMeasurable (hlaw 0).aemeasurable).1 (hL 0)
  have hmean : P[Y 0] = ∫ x, f x ∂μ := by
    rw [hY, ← (hlaw 0).map_eq, integral_map (hlaw 0).aemeasurable (hL 0).aestronglyMeasurable]
  have hvar : Var[Y 0; P] = Var[f; μ] := by
    rw [← (hlaw 0).map_eq, variance_map (hfm 0) (hlaw 0).aemeasurable]
    rfl
  rw [← hvar] at hZ
  have key := tendstoInDistribution_inv_sqrt_mul_sum_sub hZ hY0 hindY hident
  rw [hmean] at key
  convert key using 1
  funext n ω
  unfold sampleMean
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ f (X k ω)) n]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    rw [Nat.cast_zero, Real.sqrt_zero, inv_zero, zero_mul, zero_mul]
  · have hs : Real.sqrt n ≠ 0 := Real.sqrt_ne_zero'.2 (Nat.cast_pos.2 h)
    have hsq : (n : ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt (Nat.cast_nonneg n)).symm
    obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt n := ⟨_, rfl⟩
    rw [← hr] at hs hsq
    rw [← hr, hsq]
    simp only [hY]
    field_simp

/-- **The unlucky draw** (post #1). For independent draws `Xᵢ ~ U[0,1)`,
`P(all n draws are < 1/10) = (1/10)ⁿ`. -/
theorem measure_all_draws_lt_tenth {n : ℕ} {P : Measure Ω} {X : Fin n → Ω → ℝ}
    (hlaw : ∀ i, HasLaw (X i) uniformIco P) (hind : iIndepFun X P) :
    P {ω | ∀ i, X i ω < 1 / 10} = (1 / 10 : ℝ≥0∞) ^ n := by
  have hset : {ω | ∀ i, X i ω < 1 / 10} = ⋂ i ∈ (Finset.univ : Finset (Fin n)),
      X i ⁻¹' Iio (1 / 10) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, Finset.mem_univ, mem_preimage, mem_Iio, true_imp_iff]
  have hI : Iio (1 / 10 : ℝ) ∩ Ico 0 1 = Ico 0 (1 / 10) := by
    ext x
    simp only [mem_inter_iff, mem_Iio, mem_Ico]
    constructor
    · rintro ⟨h1, h2, _⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1, by linarith⟩
  have hone : ∀ i, P (X i ⁻¹' Iio (1 / 10)) = 1 / 10 := by
    intro i
    rw [← Measure.map_apply_of_aemeasurable (hlaw i).aemeasurable measurableSet_Iio,
      (hlaw i).map_eq, Measure.restrict_apply measurableSet_Iio,
      hI, Real.volume_Ico, sub_zero, ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one,
      ENNReal.ofReal_ofNat]
  rw [hset, hind.measure_inter_preimage_eq_mul Finset.univ (fun _ _ ↦ measurableSet_Iio),
    Finset.prod_congr rfl (fun i _ ↦ hone i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- The unlucky draw has positive probability, for every `n` (post #1). -/
theorem measure_all_draws_lt_tenth_pos {n : ℕ} {P : Measure Ω} {X : Fin n → Ω → ℝ}
    (hlaw : ∀ i, HasLaw (X i) uniformIco P) (hind : iIndepFun X P) :
    0 < P {ω | ∀ i, X i ω < 1 / 10} := by
  rw [measure_all_draws_lt_tenth hlaw hind]
  exact ENNReal.pow_pos (by norm_num) n

/-- **MC has no worst-case guarantee** (post #1). For i.i.d. `U[0,1)` draws and every `n ≥ 1`,
the MC estimate of `μ = 1/2` misses by more than `2/5` with probability at least `(1/10)ⁿ > 0`. -/
theorem measure_sampleMean_far_pos {n : ℕ} (hn : n ≠ 0) {P : Measure Ω} {X : Fin n → Ω → ℝ}
    (hlaw : ∀ i, HasLaw (X i) uniformIco P) (hind : iIndepFun X P) :
    (1 / 10 : ℝ≥0∞) ^ n ≤ P {ω | 2 / 5 < |sampleMean n id (fun i ↦ X i ω) - 1 / 2|} ∧
      0 < P {ω | 2 / 5 < |sampleMean n id (fun i ↦ X i ω) - 1 / 2|} := by
  have hsub : {ω | ∀ i, X i ω < 1 / 10} ⊆
      {ω | 2 / 5 < |sampleMean n id (fun i ↦ X i ω) - 1 / 2|} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
    have hlt : sampleMean n id (fun i ↦ X i ω) < 1 / 10 := by
      unfold sampleMean
      have hs : ∑ i, id (X i ω) < ∑ _i : Fin n, (1 / 10 : ℝ) :=
        Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.2 ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩)
          (fun i _ ↦ hω i)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
      rw [inv_mul_lt_iff₀ hn']
      linarith
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    linarith
  have h1 := measure_mono (μ := P) hsub
  rw [measure_all_draws_lt_tenth hlaw hind] at h1
  exact ⟨h1, lt_of_lt_of_le (ENNReal.pow_pos (by norm_num) n) h1⟩

end RQMCMarkov.PointSets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# RQMC requirement (i): marginally uniform points give an unbiased estimator (posts #1–#2)

Posts #1 and #2 require of an RQMC point set `{z₁, …, zₙ}` that "(i) each individual point is
uniformly distributed (0,1), marginally", and say that RQMC then gives "an unbiased …
estimator". Reading: in `s` dimensions, points `zᵢ : Ω → (Fin s → ℝ)` with each law
`P.map zᵢ = uniformCube s` (nothing assumed on the joint law).

## Main results

* `integral_sampleMean_of_hasLaw_uniformCube`: under (i), `E[(1/n) Σᵢ f(zᵢ)] = ∫ f` over
  `[0,1)^s`, for every integrable `f`.
* Random shift modulo 1 (post #2's "random shift", the randomization of lattice rules):
  `measurePreserving_fract_add` (`u ↦ fract (c + u)` preserves `U[0,1)`),
  `measurePreserving_shiftMod1` (the same coordinatewise on `[0,1)^s`), `hasLaw_shiftMod1`,
  `shiftMod1_mem_cube`, and `integral_sampleMean_shiftMod1`: shifting ANY fixed point set
  `y₁, …, yₙ ∈ ℝ^s` by one common `U ~ U[0,1)^s` modulo 1 satisfies (i), hence is unbiased.
* Stratification (post #2): strata `stratum n i = [i/n, (i+1)/n)` and the affine maps
  `stratumMap n i u = (i + u)/n`; `map_stratumMap_uniformIco` (the law of `(i + U)/n` is uniform on
  stratum `i`), `iUnion_stratum`, `pairwise_disjoint_stratum`, `sum_map_stratumMap`,
  `sum_map_stratified` and `integral_sampleMean_stratified`: one point `(i + Vᵢ)/n` per stratum
  with `Vᵢ ~ U[0,1)` (any joint law: independent `Vᵢ`, or one common `V`) is unbiased.
* `integral_sampleMean_of_hasLaw_const`, `variance_sampleMean_const`: requirement (i) alone does
  not reduce variance (all points equal to one uniform `U`); requirement (ii) is what matters
  for the variance.

**Correction.** Requirement (i) is sufficient for unbiasedness but not necessary, and
stratified sampling — post #2's first RQMC method — violates it:
`not_hasLaw_stratumMap` shows that for `n ≥ 2` the point `(i + V)/n` of stratum `i` is NOT
marginally `U[0,1)` (it is uniform on its stratum). The exact condition is that the marginal laws
AVERAGE to the uniform law, `Σᵢ P.map zᵢ = n • μ`: it implies unbiasedness for every integrable
`f` (`integral_sampleMean_of_sum_map_eq`, in `MonteCarlo`), and it is implied by unbiasedness for
indicator functions (`sum_map_eq_of_integral_sampleMean_indicator`), so it is equivalent to
unbiasedness for all bounded measurable `f`. (Randomly permuting the labels of a stratified set
would restore (i) without changing the estimator.)
-/

namespace RQMCMarkov.PointSets

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **RQMC requirement (i) gives unbiasedness** (posts #1–#2): if each point `zᵢ` is marginally
uniform on `[0,1)^s` (no assumption on the joint law), then
`E[(1/n) Σᵢ f(zᵢ)] = ∫ f d U[0,1)^s` for every integrable `f`. -/
theorem integral_sampleMean_of_hasLaw_uniformCube {n s : ℕ} (hn : n ≠ 0) {P : Measure Ω}
    {z : Fin n → Ω → (Fin s → ℝ)} (hz : ∀ i, HasLaw (z i) (uniformCube s) P)
    {f : (Fin s → ℝ) → ℝ} (hf : Integrable f (uniformCube s)) :
    ∫ ω, sampleMean n f (fun i ↦ z i ω) ∂P = ∫ x, f x ∂(uniformCube s) :=
  integral_sampleMean_iid hn hz hf

/-- `uniformIco` is Lebesgue measure restricted to `(0,1]`. -/
theorem uniformIco_eq_restrict_Ioc : uniformIco = volume.restrict (Ioc (0 : ℝ) 1) :=
  Measure.restrict_congr_set Ico_ae_eq_Ioc

/-- The pushforward of Lebesgue measure on `(t, t+1]` by `Int.fract` does not depend on `t`. -/
theorem map_fract_restrict_Ioc (t : ℝ) :
    (volume.restrict (Ioc t (t + 1))).map Int.fract =
      (volume.restrict (Ioc (0 : ℝ) (0 + 1))).map Int.fract := by
  set h : UnitAddCircle → ℝ := fun x ↦ ((AddCircle.equivIco (1 : ℝ) 0 x : Ico (0 : ℝ) (0 + 1)) : ℝ)
    with hh
  have hhm : Measurable h :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable
  have hfr : (Int.fract : ℝ → ℝ) = h ∘ ((↑) : ℝ → UnitAddCircle) := by
    funext x
    simp only [hh, Function.comp_apply]
    rw [AddCircle.coe_equivIco_mk_apply, div_one, mul_one]
  have key : ∀ t : ℝ, (volume.restrict (Ioc t (t + 1))).map Int.fract =
      (volume : Measure UnitAddCircle).map h := by
    intro t
    rw [hfr, ← Measure.map_map hhm AddCircle.measurable_mk',
      (UnitAddCircle.measurePreserving_mk t).map_eq]
  rw [key t, key 0]

/-- **A shift modulo 1 preserves the uniform law**: `u ↦ fract (c + u)` maps `U[0,1)` to itself,
for every real `c`. -/
theorem measurePreserving_fract_add (c : ℝ) :
    MeasurePreserving (fun u ↦ Int.fract (c + u)) uniformIco uniformIco := by
  have hm : Measurable fun u : ℝ ↦ Int.fract (c + u) :=
    measurable_fract.comp (measurable_const_add c)
  refine ⟨hm, ?_⟩
  have hfr : (fun u : ℝ ↦ Int.fract (c + u)) = Int.fract ∘ (fun u ↦ c + u) := rfl
  have hshift : (volume.restrict (Ioc (0 : ℝ) 1)).map (fun u ↦ c + u) =
      volume.restrict (Ioc c (c + 1)) := by
    have hpre : (fun u : ℝ ↦ c + u) ⁻¹' Ioc c (c + 1) = Ioc 0 1 := by
      ext u
      simp only [mem_preimage, mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by linarith, by linarith⟩
    rw [← hpre, ← Measure.restrict_map (measurable_const_add c) measurableSet_Ioc,
      map_add_left_eq_self]
  have hid : uniformIco.map Int.fract = uniformIco := by
    have hae : Int.fract =ᵐ[uniformIco] id :=
      ae_restrict_of_forall_mem measurableSet_Ico (fun x hx ↦ Int.fract_eq_self.2 hx)
    rw [Measure.map_congr hae, Measure.map_id]
  rw [hfr, ← Measure.map_map measurable_fract (measurable_const_add c)]
  nth_rewrite 1 [uniformIco_eq_restrict_Ioc]
  rw [hshift, map_fract_restrict_Ioc, zero_add, ← uniformIco_eq_restrict_Ioc, hid]

/-- The random shift modulo 1 of a point `y ∈ ℝ^s` by `u`: `k ↦ fract (y k + u k)`. -/
noncomputable def shiftMod1 {s : ℕ} (y u : Fin s → ℝ) : Fin s → ℝ :=
  fun k ↦ Int.fract (y k + u k)

/-- A shifted point lies in `[0,1)^s`. -/
theorem shiftMod1_mem_cube {s : ℕ} (y u : Fin s → ℝ) (k : Fin s) :
    shiftMod1 y u k ∈ Ico (0 : ℝ) 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- **The shift modulo 1 preserves `U[0,1)^s`**, for every fixed `y ∈ ℝ^s`. -/
theorem measurePreserving_shiftMod1 {s : ℕ} (y : Fin s → ℝ) :
    MeasurePreserving (shiftMod1 y) (uniformCube s) (uniformCube s) := by
  have := isProbabilityMeasure_uniformIco
  exact measurePreserving_pi _ _ (fun k ↦ measurePreserving_fract_add (y k))

/-- If `U ~ U[0,1)^s` then `shiftMod1 y U ~ U[0,1)^s`. -/
theorem hasLaw_shiftMod1 {s : ℕ} (y : Fin s → ℝ) {P : Measure Ω} {U : Ω → Fin s → ℝ}
    (hU : HasLaw U (uniformCube s) P) : HasLaw (fun ω ↦ shiftMod1 y (U ω)) (uniformCube s) P :=
  (measurePreserving_shiftMod1 y).fun_comp_hasLaw hU

/-- **The randomly shifted point set is unbiased** (post #2): for ANY fixed points
`y₁, …, yₙ ∈ ℝ^s` and one common `U ~ U[0,1)^s`, the points `fract (yᵢ + U)` satisfy
requirement (i), so `E[(1/n) Σᵢ f(fract (yᵢ + U))] = ∫ f d U[0,1)^s`. -/
theorem integral_sampleMean_shiftMod1 {n s : ℕ} (hn : n ≠ 0) (y : Fin n → Fin s → ℝ)
    {P : Measure Ω} {U : Ω → Fin s → ℝ} (hU : HasLaw U (uniformCube s) P)
    {f : (Fin s → ℝ) → ℝ} (hf : Integrable f (uniformCube s)) :
    ∫ ω, sampleMean n f (fun i ↦ shiftMod1 (y i) (U ω)) ∂P = ∫ x, f x ∂(uniformCube s) :=
  integral_sampleMean_of_hasLaw_uniformCube hn (fun i ↦ hasLaw_shiftMod1 (y i) hU) hf

/-- The `i`-th stratum `[i/n, (i+1)/n)` of `[0,1)`. -/
def stratum (n i : ℕ) : Set ℝ := Ico ((i : ℝ) / n) ((i + 1) / n)

/-- Strata are measurable. -/
theorem measurableSet_stratum (n i : ℕ) : MeasurableSet (stratum n i) := measurableSet_Ico

/-- The affine map `u ↦ (i + u)/n` from `[0,1)` onto the `i`-th stratum. -/
noncomputable def stratumMap (n i : ℕ) (u : ℝ) : ℝ := (i + u) / n

/-- `stratumMap n i` is measurable. -/
theorem measurable_stratumMap (n i : ℕ) : Measurable (stratumMap n i) :=
  (measurable_const_add _).div_const _

/-- `stratumMap n i` maps `[0,1)` onto the stratum: `(i + u)/n ∈ stratum n i ↔ u ∈ [0,1)`. -/
theorem stratumMap_preimage_stratum {n : ℕ} (hn : n ≠ 0) (i : ℕ) :
    stratumMap n i ⁻¹' stratum n i = Ico 0 1 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  ext u
  simp only [stratum, stratumMap, mem_preimage, mem_Ico]
  rw [div_le_div_iff_of_pos_right hn', div_lt_div_iff_of_pos_right hn']
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- **The law of `(i + U)/n`**, `U ~ U[0,1)`, is `n` times Lebesgue measure on stratum `i`. -/
theorem map_stratumMap_uniformIco {n : ℕ} (hn : n ≠ 0) (i : ℕ) :
    uniformIco.map (stratumMap n i) = (n : ℝ≥0∞) • volume.restrict (stratum n i) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hvol : (volume : Measure ℝ).map (stratumMap n i) = (n : ℝ≥0∞) • volume := by
    have hcomp : stratumMap n i = (fun x : ℝ ↦ x * (n : ℝ)⁻¹) ∘ (fun u : ℝ ↦ (i : ℝ) + u) := by
      funext u
      simp only [stratumMap, Function.comp_apply, div_eq_mul_inv]
    rw [hcomp, ← Measure.map_map (measurable_mul_const _) (measurable_const_add _),
      map_add_left_eq_self, Real.map_volume_mul_right (inv_ne_zero hn'.ne'), inv_inv,
      abs_of_pos hn', ENNReal.ofReal_natCast]
  change (volume.restrict (Ico (0 : ℝ) 1)).map (stratumMap n i) = _
  rw [← stratumMap_preimage_stratum hn i,
    ← Measure.restrict_map (measurable_stratumMap n i) (measurableSet_stratum n i), hvol,
    Measure.restrict_smul]

/-- The strata cover `[0,1)`. -/
theorem iUnion_stratum {n : ℕ} (hn : n ≠ 0) : ⋃ i : Fin n, stratum n i = Ico 0 1 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  ext x
  simp only [mem_iUnion, stratum, mem_Ico]
  constructor
  · rintro ⟨i, h1, h2⟩
    have hi : (i : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
    refine ⟨le_trans (div_nonneg (Nat.cast_nonneg _) hn'.le) h1, ?_⟩
    calc x < ((i : ℝ) + 1) / n := h2
      _ ≤ n / n := div_le_div_of_nonneg_right hi hn'.le
      _ = 1 := div_self hn'.ne'
  · rintro ⟨h0, h1⟩
    have hnx : 0 ≤ (n : ℝ) * x := mul_nonneg hn'.le h0
    have hlt : ⌊(n : ℝ) * x⌋₊ < n := by
      rw [Nat.floor_lt hnx]
      calc (n : ℝ) * x < n * 1 := mul_lt_mul_of_pos_left h1 hn'
        _ = n := mul_one _
    refine ⟨⟨⌊(n : ℝ) * x⌋₊, hlt⟩, ?_, ?_⟩
    · change ((⌊(n : ℝ) * x⌋₊ : ℕ) : ℝ) / n ≤ x
      rw [div_le_iff₀ hn', mul_comm x]
      exact Nat.floor_le hnx
    · change x < ((⌊(n : ℝ) * x⌋₊ : ℕ) + 1 : ℝ) / n
      rw [lt_div_iff₀ hn', mul_comm x]
      exact Nat.lt_floor_add_one _

/-- Distinct strata are disjoint. -/
theorem pairwise_disjoint_stratum (n : ℕ) :
    Pairwise (Function.onFun Disjoint fun i : Fin n ↦ stratum n i) := by
  intro i j hij
  rw [Function.onFun, Set.disjoint_left]
  intro x hxi hxj
  simp only [stratum, mem_Ico] at hxi hxj
  rcases Nat.eq_zero_or_pos n with h | h
  · exact (Fin.elim0 (h ▸ i))
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 h
  rw [div_le_iff₀ hn', lt_div_iff₀ hn'] at hxi hxj
  have h1 : (i : ℝ) < j + 1 := by linarith
  have h2 : (j : ℝ) < i + 1 := by linarith
  have h1' : (i : ℕ) < j + 1 := by exact_mod_cast h1
  have h2' : (j : ℕ) < i + 1 := by exact_mod_cast h2
  exact hij (Fin.ext (by omega))

/-- **The stratum laws average to the uniform law**: `Σᵢ law((i + U)/n) = n • U[0,1)`. -/
theorem sum_map_stratumMap {n : ℕ} (hn : n ≠ 0) :
    ∑ i : Fin n, uniformIco.map (stratumMap n i) = (n : ℝ≥0∞) • uniformIco := by
  rw [Finset.sum_congr rfl (fun (i : Fin n) _ ↦ map_stratumMap_uniformIco hn i),
    ← Finset.smul_sum,
    ← Measure.sum_fintype, ← Measure.restrict_iUnion (pairwise_disjoint_stratum n)
      (fun _ ↦ measurableSet_Ico), iUnion_stratum hn]

/-- **Stratified points have uniformly averaged marginals**: if `Vᵢ ~ U[0,1)` for each `i` (any
joint law), the points `(i + Vᵢ)/n` satisfy `Σᵢ P.map ((i + Vᵢ)/n) = n • U[0,1)`. -/
theorem sum_map_stratified {n : ℕ} (hn : n ≠ 0) {P : Measure Ω} {V : Fin n → Ω → ℝ}
    (hV : ∀ i, HasLaw (V i) uniformIco P) :
    ∑ i : Fin n, P.map (fun ω ↦ stratumMap n i (V i ω)) = (n : ℝ≥0∞) • uniformIco := by
  rw [← sum_map_stratumMap hn]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [← (hV i).map_eq, AEMeasurable.map_map_of_aemeasurable
    (measurable_stratumMap n i).aemeasurable (hV i).aemeasurable]
  rfl

/-- **Stratified sampling is unbiased** (post #2): one point `(i + Vᵢ)/n` in each stratum, with
`Vᵢ ~ U[0,1)` (independent, or one common `V`, or any joint law), gives
`E[(1/n) Σᵢ f((i + Vᵢ)/n)] = ∫₀¹ f`. -/
theorem integral_sampleMean_stratified {n : ℕ} (hn : n ≠ 0) {P : Measure Ω}
    {V : Fin n → Ω → ℝ} (hV : ∀ i, HasLaw (V i) uniformIco P) {f : ℝ → ℝ}
    (hf : Integrable f uniformIco) :
    ∫ ω, sampleMean n f (fun i ↦ stratumMap n i (V i ω)) ∂P = ∫ x, f x ∂uniformIco :=
  integral_sampleMean_of_sum_map_eq hn
    (fun i ↦ (measurable_stratumMap n i).comp_aemeasurable (hV i).aemeasurable)
    (sum_map_stratified hn hV) hf

/-- **Correction: stratified points violate requirement (i).** For `n ≥ 2` the stratified point
`(i + V)/n`, `V ~ U[0,1)`, is not marginally uniform on `[0,1)` (it is uniform on its stratum),
although the stratified estimator is unbiased (`integral_sampleMean_stratified`). -/
theorem not_hasLaw_stratumMap {n : ℕ} (hn : 2 ≤ n) (i : Fin n) {P : Measure Ω} {V : Ω → ℝ}
    (hV : HasLaw V uniformIco P) :
    ¬ HasLaw (fun ω ↦ stratumMap n i (V ω)) uniformIco P := by
  intro h
  have hn0 : n ≠ 0 := by omega
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn0)
  have hlaw : uniformIco = (n : ℝ≥0∞) • volume.restrict (stratum n i) := by
    rw [← h.map_eq, ← map_stratumMap_uniformIco hn0 i, ← hV.map_eq,
      AEMeasurable.map_map_of_aemeasurable (measurable_stratumMap n i).aemeasurable
        hV.aemeasurable]
    rfl
  have hsub : stratum n i ⊆ Ico 0 1 := by
    rw [← iUnion_stratum hn0]
    exact subset_iUnion (fun j : Fin n ↦ stratum n j) i
  have hvol : volume (stratum n i) = ENNReal.ofReal (1 / n) := by
    rw [stratum, Real.volume_Ico]
    congr 1
    ring
  have h1 : uniformIco (stratum n i) = ENNReal.ofReal (1 / n) := by
    change volume.restrict (Ico (0 : ℝ) 1) (stratum n i) = _
    rw [Measure.restrict_apply (measurableSet_stratum n i), inter_eq_self_of_subset_left hsub,
      hvol]
  have h2 : ((n : ℝ≥0∞) • volume.restrict (stratum n i)) (stratum n i) = 1 := by
    rw [Measure.smul_apply, Measure.restrict_apply (measurableSet_stratum n i), inter_self, hvol,
      smul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n),
      mul_one_div_cancel hn'.ne', ENNReal.ofReal_one]
  rw [← hlaw, h1, ENNReal.ofReal_eq_one] at h2
  have : (n : ℝ) = 1 := by
    rw [div_eq_one_iff_eq hn'.ne'] at h2
    exact h2.symm
  have : n = 1 := by exact_mod_cast this
  omega

/-- **Corrected statement: averaged marginals are necessary.** If the estimator is unbiased for
every indicator function, `E[(1/n) Σᵢ 1_A(zᵢ)] = μ(A)`, then the marginal laws average to `μ`:
`Σᵢ P.map zᵢ = n • μ`. With `integral_sampleMean_of_sum_map_eq` this makes averaged marginals
the exact condition for unbiasedness. -/
theorem sum_map_eq_of_integral_sampleMean_indicator {E : Type*} {mE : MeasurableSpace E}
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] {z : Fin n → Ω → E} {μ : Measure E}
    [IsFiniteMeasure μ] (hz : ∀ i, AEMeasurable (z i) P)
    (h : ∀ A, MeasurableSet A →
      ∫ ω, sampleMean n (A.indicator 1) (fun i ↦ z i ω) ∂P = μ.real A) :
    ∑ i, P.map (z i) = (n : ℝ≥0∞) • μ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [Finset.univ_eq_empty, Finset.sum_empty, Nat.cast_zero, zero_smul]
  ext A hA
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hint : ∀ i, Integrable (fun ω ↦ A.indicator (1 : E → ℝ) (z i ω)) P := fun i ↦
    ((integrable_const (1 : ℝ)).indicator hA).comp_aemeasurable (hz i)
  have hreal : ∀ i, ∫ ω, A.indicator (1 : E → ℝ) (z i ω) ∂P = (P.map (z i)).real A := fun i ↦ by
    rw [← integral_indicator_one hA,
      integral_map (hz i) ((measurable_one.indicator hA).aestronglyMeasurable)]
  have hA' := h A hA
  unfold sampleMean at hA'
  change ∫ ω, (n : ℝ)⁻¹ * ∑ i, A.indicator (1 : E → ℝ) (z i ω) ∂P = _ at hA'
  rw [integral_const_mul, integral_finsetSum _ (fun i _ ↦ hint i),
    Finset.sum_congr rfl (fun i _ ↦ hreal i), inv_mul_eq_iff_eq_mul₀ hn'] at hA'
  rw [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  have hfin : ∀ i, P.map (z i) A = ENNReal.ofReal ((P.map (z i)).real A) := fun i ↦
    (ofReal_measureReal (measure_ne_top _ A)).symm
  rw [Finset.sum_congr rfl (fun i _ ↦ hfin i),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ measureReal_nonneg), hA',
    ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast,
    ofReal_measureReal (measure_ne_top _ A)]

/-- With all points equal, the sample mean is the value at that point. -/
theorem sampleMean_const_points {E : Type*} {n : ℕ} (hn : n ≠ 0) (f : E → ℝ) (x : E) :
    sampleMean n f (fun _ ↦ x) = f x := by
  rw [sampleMean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn), one_mul]

/-- **Requirement (i) alone: all points equal.** Taking every point equal to one `U ~ μ`
satisfies (i) and is unbiased ... -/
theorem integral_sampleMean_of_hasLaw_const {E : Type*} {mE : MeasurableSpace E} {n : ℕ}
    (hn : n ≠ 0) {P : Measure Ω} {U : Ω → E} {μ : Measure E} (hU : HasLaw U μ P) {f : E → ℝ}
    (hf : Integrable f μ) :
    ∫ ω, sampleMean n f (fun _ : Fin n ↦ U ω) ∂P = ∫ x, f x ∂μ :=
  integral_sampleMean_iid hn (fun _ ↦ hU) hf

/-- **... but its variance is the variance of ONE draw**, `Var_μ(f)`, not `Var_μ(f)/n`: (i)
says nothing about the variance; the joint structure (requirement (ii)) is what reduces it. -/
theorem variance_sampleMean_const {E : Type*} {mE : MeasurableSpace E} {n : ℕ} (hn : n ≠ 0)
    {P : Measure Ω} {U : Ω → E} {μ : Measure E} (hU : HasLaw U μ P) {f : E → ℝ}
    (hf : AEMeasurable f μ) :
    Var[fun ω ↦ sampleMean n f (fun _ : Fin n ↦ U ω); P] = Var[f; μ] := by
  have hfun : (fun ω ↦ sampleMean n f (fun _ : Fin n ↦ U ω)) = f ∘ U := by
    funext ω
    exact sampleMean_const_points hn f (U ω)
  rw [hfun, ← variance_map (hU.map_eq ▸ hf) hU.aemeasurable, hU.map_eq]

end RQMCMarkov.PointSets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # Randomly shifted QMC in one dimension

Post #1 says RQMC "happily happens to provide convergence of the estimator at least as fast as
QMC", and post #2 randomizes QMC sets by a random shift. The simplest such randomization is the
random shift modulo 1 (Cranley-Patterson 1976; L'Ecuyer 2016): `zᵢ = fract (xᵢ + U)` with
`U ~ Uniform[0,1)`. The law of `U` is `uniformIco = volume.restrict [0,1)` (from
`PointSets.MonteCarlo`). The marginal uniformity of each `zᵢ` is
`measurePreserving_fract_add` (in `Unbiased`).

**Results.**
* `integral_qmcEstimate_shiftMod`: the shifted estimator is unbiased, `E[Q(z)] = ∫₀¹ f`
  (a one-dimensional restatement of `integral_sampleMean_shiftMod1` in `qmcEstimate` notation).
* `localDiscrepancy_shiftMod_le`, `starDiscrepancy_shiftMod_le`: **deterministically, for every
  shift `u`, `D*ₙ(z) ≤ 2 D*ₙ(x)`**, since an interval `[0,t)` pulls back under the shift to one
  interval or the union of two intervals of `[0,1)`.
* `abs_shiftedError_le`: for every shift, `|Q(z) - ∫ f| ≤ 2 V(f) D*ₙ(x)` (Koksma).
* `integral_sq_shiftedError_le`, `sqrt_integral_sq_shiftedError_le`: the mean squared error of
  the randomly shifted estimator is at most `(2 V(f) D*ₙ(x))²`, and its root-mean-square error is
  at most `2 V(f) D*ₙ(x)`: RQMC by a random shift converges at least as fast as the Koksma bound
  of the QMC set it randomizes.
* `sqrt_integral_sq_shiftedError_vanDerCorput_le`, `tendsto_sqrt_mul_rmse_vanDerCorput`: for the
  randomly shifted van der Corput sequence, RMSE `≤ 4 V(f) (log n + 1)/n`, so `√n · RMSE → 0`,
  faster than MC's `σ/√n`.

**Correction (precise reading of "at least as fast as QMC").** The statement holds for the
worst-case (Koksma) error bounds and rates, with a factor `2`; it is false for the error on a
given integrand. `shiftedMidpoint_counterexample`: for the one-point midpoint rule `{1/2}` and
`f(x) = x`, the QMC error is `0` but the randomly shifted estimator has mean squared error
`1/12 > 0`.
-/

namespace RQMCMarkov.PointSets

open MeasureTheory Filter Topology

/-- The random shift modulo 1 of a point sequence: `zᵢ = fract (xᵢ + u)`. -/
noncomputable def shiftMod (x : ℕ → ℝ) (u : ℝ) : ℕ → ℝ := fun i => Int.fract (x i + u)

/-- Shifted points lie in `[0,1)`. -/
theorem shiftMod_inUnitIco (x : ℕ → ℝ) (u : ℝ) (n : ℕ) : InUnitIco (shiftMod x u) n :=
  fun _ _ => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- Only the fractional part of the shift matters. -/
theorem shiftMod_fract (x : ℕ → ℝ) (u : ℝ) : shiftMod x (Int.fract u) = shiftMod x u := by
  funext i
  unfold shiftMod
  rw [← Int.fract_add_intCast (x i + Int.fract u) ⌊u⌋, add_assoc, Int.fract_add_floor]

/-- The fractional part of `y ∈ [0,2)`: `y` if `y < 1`, else `y - 1`. -/
theorem fract_of_lt_one {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) : Int.fract y = y :=
  Int.fract_eq_self.mpr ⟨h0, h1⟩

/-- The fractional part of `y ∈ [1,2)` is `y - 1`. -/
theorem fract_of_one_le {y : ℝ} (h1 : 1 ≤ y) (h2 : y < 2) : Int.fract y = y - 1 := by
  rw [← Int.fract_sub_one]
  exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩

/-- Shifted count, case `t ≤ u`: `#{zᵢ < t} + #{xᵢ < 1 - u} = #{xᵢ < 1 - u + t}`. -/
theorem countBelow_shiftMod_of_le {x : ℕ → ℝ} {n : ℕ} (hx : InUnitIco x n) {u t : ℝ}
    (hu : u ∈ Set.Ico (0 : ℝ) 1) (ht0 : 0 ≤ t) (htu : t ≤ u) :
    countBelow (shiftMod x u) n t + countBelow x n (1 - u) = countBelow x n (1 - u + t) := by
  unfold countBelow
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hxi0 := (hx i (Finset.mem_range.mp hi)).1
  have hxi1 := (hx i (Finset.mem_range.mp hi)).2
  have hu0 := hu.1
  have hu1 := hu.2
  unfold shiftMod
  rcases lt_or_ge (x i + u) 1 with h | h
  · rw [fract_of_lt_one (by linarith) h]
    split_ifs <;> first | rfl | (exfalso; linarith)
  · rw [fract_of_one_le h (by linarith)]
    split_ifs <;> first | rfl | (exfalso; linarith)

/-- Shifted count, case `u < t ≤ 1`: `#{zᵢ < t} + #{xᵢ < 1 - u} = #{xᵢ < t - u} + n`. -/
theorem countBelow_shiftMod_of_lt {x : ℕ → ℝ} {n : ℕ} (hx : InUnitIco x n) {u t : ℝ}
    (hu : u ∈ Set.Ico (0 : ℝ) 1) (htu : u < t) (ht1 : t ≤ 1) :
    countBelow (shiftMod x u) n t + countBelow x n (1 - u) = countBelow x n (t - u) + n := by
  unfold countBelow
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  have hsum : ∑ i ∈ Finset.range n, ((if shiftMod x u i < t then 1 else 0) +
      (if x i < 1 - u then 1 else 0)) =
      ∑ i ∈ Finset.range n, ((if x i < t - u then 1 else 0) + 1) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hxi0 := (hx i (Finset.mem_range.mp hi)).1
    have hxi1 := (hx i (Finset.mem_range.mp hi)).2
    have hu0 := hu.1
    have hu1 := hu.2
    unfold shiftMod
    rcases lt_or_ge (x i + u) 1 with h | h
    · rw [fract_of_lt_one (by linarith) h]
      split_ifs <;> first | rfl | (exfalso; linarith)
    · rw [fract_of_one_le h (by linarith)]
      split_ifs <;> first | rfl | (exfalso; linarith)
  rw [hsum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

/-- The signed local discrepancy `#{xᵢ < a}/n - a` at `a ∈ [0,1]` is at most `D*ₙ` in absolute
value. -/
theorem abs_countBelow_div_sub_le (x : ℕ → ℝ) (n : ℕ) {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    |(countBelow x n a : ℝ) / n - a| ≤ starDiscrepancy x n :=
  localDiscrepancy_le_starDiscrepancy x n ha

/-- **The shift at most doubles the local discrepancy**: for `u ∈ [0,1)` and `t ∈ [0,1]`,
`|#{zᵢ < t}/n - t| ≤ 2 D*ₙ(x)`. -/
theorem localDiscrepancy_shiftMod_le {x : ℕ → ℝ} {n : ℕ} (hx : InUnitIco x n) {u t : ℝ}
    (hu : u ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    localDiscrepancy (shiftMod x u) n t ≤ 2 * starDiscrepancy x n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h1 := localDiscrepancy_le_starDiscrepancy x 0 (Set.right_mem_Icc.mpr zero_le_one)
    unfold localDiscrepancy at h1 ⊢
    rw [Nat.cast_zero, div_zero, zero_sub, abs_neg, abs_one] at h1
    rw [Nat.cast_zero, div_zero, zero_sub, abs_neg, abs_of_nonneg ht.1]
    linarith [ht.2]
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  unfold localDiscrepancy
  have ha : 1 - u ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hA := abs_countBelow_div_sub_le x n ha
  rcases le_or_gt t u with htu | htu
  · have hcount := countBelow_shiftMod_of_le hx hu ht.1 htu
    have hcR : (countBelow (shiftMod x u) n t : ℝ) =
        countBelow x n (1 - u + t) - countBelow x n (1 - u) := by
      rw [← hcount, Nat.cast_add]
      ring
    have hb : 1 - u + t ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hu.2, ht.1], by linarith⟩
    have hB := abs_countBelow_div_sub_le x n hb
    have heq : (countBelow (shiftMod x u) n t : ℝ) / n - t =
        ((countBelow x n (1 - u + t) : ℝ) / n - (1 - u + t)) -
          ((countBelow x n (1 - u) : ℝ) / n - (1 - u)) := by
      rw [hcR, sub_div]
      ring
    rw [heq]
    exact (abs_sub _ _).trans (by linarith)
  · have hcount := countBelow_shiftMod_of_lt hx hu htu ht.2
    have hcR : (countBelow (shiftMod x u) n t : ℝ) =
        countBelow x n (t - u) + n - countBelow x n (1 - u) := by
      rw [← Nat.cast_add, ← hcount, Nat.cast_add]
      ring
    have hb : t - u ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [hu.1, ht.2]⟩
    have hB := abs_countBelow_div_sub_le x n hb
    have heq : (countBelow (shiftMod x u) n t : ℝ) / n - t =
        ((countBelow x n (t - u) : ℝ) / n - (t - u)) -
          ((countBelow x n (1 - u) : ℝ) / n - (1 - u)) := by
      rw [hcR, sub_div, add_div, div_self hpos.ne']
      ring
    rw [heq]
    exact (abs_sub _ _).trans (by linarith)

/-- **A random shift at most doubles the star discrepancy**: for every shift `u ∈ ℝ` and every
point set in `[0,1)`, `D*ₙ(fract (x + u)) ≤ 2 D*ₙ(x)`. -/
theorem starDiscrepancy_shiftMod_le {x : ℕ → ℝ} {n : ℕ} (hx : InUnitIco x n) (u : ℝ) :
    starDiscrepancy (shiftMod x u) n ≤ 2 * starDiscrepancy x n := by
  rw [← shiftMod_fract x u]
  exact starDiscrepancy_le_of_forall _ _ fun t ht =>
    localDiscrepancy_shiftMod_le hx ⟨Int.fract_nonneg u, Int.fract_lt_one u⟩ ht

/-- **Koksma for every shift**: `|Q(fract (x + u)) - ∫₀¹ f| ≤ 2 V(f) D*ₙ(x)`. -/
theorem abs_shiftedError_le {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc 0 1)) {x : ℕ → ℝ}
    {n : ℕ} (hx : InUnitIco x n) (hn : 0 < n) (u : ℝ) :
    |qmcEstimate f (shiftMod x u) n - ∫ t in (0 : ℝ)..1, f t| ≤
      2 * totalVariation f * starDiscrepancy x n := by
  have h := koksma_boundedVariationOn hf (shiftMod_inUnitIco x u n) hn
  have hV : 0 ≤ totalVariation f := ENNReal.toReal_nonneg
  calc _ ≤ _ := h
    _ ≤ totalVariation f * (2 * starDiscrepancy x n) :=
        mul_le_mul_of_nonneg_left (starDiscrepancy_shiftMod_le hx u) hV
    _ = _ := by ring

/-- **Unbiasedness of the randomly shifted estimator** (one-dimensional `qmcEstimate` form):
for `U ~ Uniform[0,1)` and `f` integrable on `[0,1]`, `E[(1/n) ∑ f(fract (xᵢ + U))] = ∫₀¹ f`,
for any points `x` and `n ≥ 1`. -/
theorem integral_qmcEstimate_shiftMod {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 1)
    (x : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    ∫ u, qmcEstimate f (shiftMod x u) n ∂uniformIco = ∫ t in (0 : ℝ)..1, f t := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hfU : Integrable f uniformIco := by
    rw [uniformIco_eq_restrict_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hf
  have hcomp : ∀ c : ℝ, ∫ u, f (Int.fract (c + u)) ∂uniformIco = ∫ y, f y ∂uniformIco := by
    intro c
    have hmp := measurePreserving_fract_add c
    rw [← integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hfU.1),
      hmp.map_eq]
  have hint : ∀ i ∈ Finset.range n, Integrable (fun u => f (shiftMod x u i)) uniformIco :=
    fun i _ => (measurePreserving_fract_add (x i)).integrable_comp_of_integrable hfU
  unfold qmcEstimate
  rw [integral_div, integral_finsetSum _ hint]
  have hsum : ∑ i ∈ Finset.range n, ∫ u, f (shiftMod x u i) ∂uniformIco =
      ∑ _i ∈ Finset.range n, ∫ y, f y ∂uniformIco := by
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold shiftMod
    rw [← hcomp (x i)]
  rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_cancel_left₀ _ hpos.ne',
    intervalIntegral.integral_of_le zero_le_one, uniformIco_eq_restrict_Ioc]

/-- **Mean squared error of randomly shifted QMC.** For `f` of bounded variation, `n ≥ 1`
points in `[0,1)` and `U ~ Uniform[0,1)`:
`E[(Q(fract (x + U)) - ∫₀¹ f)²] ≤ (2 V(f) D*ₙ(x))²`. -/
theorem integral_sq_shiftedError_le {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc 0 1))
    {x : ℕ → ℝ} {n : ℕ} (hx : InUnitIco x n) (hn : 0 < n) :
    ∫ u, (qmcEstimate f (shiftMod x u) n - ∫ t in (0 : ℝ)..1, f t) ^ 2 ∂uniformIco ≤
      (2 * totalVariation f * starDiscrepancy x n) ^ 2 := by
  have := isProbabilityMeasure_uniformIco
  have hbound : ∀ᵐ u ∂uniformIco,
      ‖(qmcEstimate f (shiftMod x u) n - ∫ t in (0 : ℝ)..1, f t) ^ 2‖ ≤
        (2 * totalVariation f * starDiscrepancy x n) ^ 2 := by
    refine Eventually.of_forall fun u => ?_
    rw [Real.norm_eq_abs, abs_pow, ← sq_abs (2 * totalVariation f * starDiscrepancy x n)]
    exact pow_le_pow_left₀ (abs_nonneg _)
      ((abs_shiftedError_le hf hx hn u).trans (le_abs_self _)) 2
  have h := norm_integral_le_of_norm_le_const hbound
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

/-- **Root-mean-square error of randomly shifted QMC**: `√E[(Q - ∫ f)²] ≤ 2 V(f) D*ₙ(x)`, i.e.
RQMC by a random shift converges at least as fast as the Koksma bound of the QMC set. -/
theorem sqrt_integral_sq_shiftedError_le {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc 0 1))
    {x : ℕ → ℝ} {n : ℕ} (hx : InUnitIco x n) (hn : 0 < n) :
    Real.sqrt (∫ u, (qmcEstimate f (shiftMod x u) n - ∫ t in (0 : ℝ)..1, f t) ^ 2 ∂uniformIco) ≤
      2 * totalVariation f * starDiscrepancy x n := by
  have hV : 0 ≤ totalVariation f := ENNReal.toReal_nonneg
  have hD := starDiscrepancy_nonneg x n
  calc _ ≤ Real.sqrt ((2 * totalVariation f * starDiscrepancy x n) ^ 2) :=
        Real.sqrt_le_sqrt (integral_sq_shiftedError_le hf hx hn)
    _ = _ := Real.sqrt_sq (by positivity)

/-- **Randomly shifted van der Corput sequence**: RMSE `≤ 4 V(f) (log n + 1)/n`. -/
theorem sqrt_integral_sq_shiftedError_vanDerCorput_le {f : ℝ → ℝ}
    (hf : BoundedVariationOn f (Set.Icc 0 1)) {n : ℕ} (hn : 0 < n) :
    Real.sqrt (∫ u, (qmcEstimate f (shiftMod vanDerCorput u) n - ∫ t in (0 : ℝ)..1, f t) ^ 2
      ∂uniformIco) ≤ 2 * totalVariation f * (2 * (Real.log n + 1) / n) := by
  have hV : 0 ≤ totalVariation f := ENNReal.toReal_nonneg
  exact (sqrt_integral_sq_shiftedError_le hf (vanDerCorput_inUnitIco n) hn).trans
    (mul_le_mul_of_nonneg_left (starDiscrepancy_vanDerCorput_le_log hn) (by positivity))

/-- **Randomly shifted van der Corput beats MC**: `√n · RMSE → 0`, i.e. the RMSE is
`o(n^{-1/2})`, while MC has RMSE exactly `σ(f)/√n`. -/
theorem tendsto_sqrt_mul_rmse_vanDerCorput {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc 0 1)) :
    Tendsto (fun n : ℕ => Real.sqrt n * Real.sqrt (∫ u, (qmcEstimate f (shiftMod vanDerCorput u) n -
      ∫ t in (0 : ℝ)..1, f t) ^ 2 ∂uniformIco)) atTop (𝓝 0) := by
  have h := tendsto_sqrt_mul_vanDerCorput_bound.const_mul (2 * totalVariation f)
  rw [mul_zero] at h
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ h
  filter_upwards [eventually_gt_atTop 0] with n hn
  have := mul_le_mul_of_nonneg_left (sqrt_integral_sq_shiftedError_vanDerCorput_le hf hn)
    (Real.sqrt_nonneg (n : ℝ))
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **Counterexample: RQMC need not beat QMC on a given integrand.** For the one-point midpoint
rule `{1/2}` and `f(x) = x`, the QMC error is `0`, while the randomly shifted estimator
`fract (1/2 + U)` has mean squared error `1/12`. -/
theorem shiftedMidpoint_counterexample :
    qmcEstimate (fun t => t) (midpointRule 1) 1 - ∫ t in (0 : ℝ)..1, t = 0 ∧
      ∫ u, (qmcEstimate (fun t => t) (shiftMod (midpointRule 1) u) 1 -
        ∫ t in (0 : ℝ)..1, t) ^ 2 ∂uniformIco = 1 / 12 := by
  have hI : ∫ t in (0 : ℝ)..1, t = 1 / 2 := by
    rw [integral_id]
    norm_num
  have hQ : ∀ y : ℕ → ℝ, qmcEstimate (fun t => t) y 1 = y 0 := by
    intro y
    unfold qmcEstimate
    rw [Finset.sum_range_one, Nat.cast_one, div_one]
  have hm : midpointRule 1 0 = 1 / 2 := by
    unfold midpointRule
    norm_num
  refine ⟨by rw [hQ, hm, hI, sub_self], ?_⟩
  simp only [hQ, hI]
  have hmp := measurePreserving_fract_add (1 / 2)
  have hcont : Continuous fun y : ℝ => (y - 1 / 2) ^ 2 := by fun_prop
  have hcomp : ∫ u, (Int.fract (1 / 2 + u) - 1 / 2) ^ 2 ∂uniformIco =
      ∫ y, (y - 1 / 2) ^ 2 ∂uniformIco := by
    have h := integral_map (μ := uniformIco) hmp.measurable.aemeasurable
      (f := fun y : ℝ => (y - 1 / 2) ^ 2) (by rw [hmp.map_eq]; exact hcont.aestronglyMeasurable)
    rw [hmp.map_eq] at h
    exact h.symm
  have hval : ∫ y, (y - 1 / 2) ^ 2 ∂uniformIco = 1 / 12 := by
    rw [uniformIco_eq_restrict_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_comp_sub_right (fun y : ℝ => y ^ 2) (1 / 2), integral_pow]
    norm_num
  have hshift : ∀ u, shiftMod (midpointRule 1) u 0 = Int.fract (1 / 2 + u) := by
    intro u
    unfold shiftMod
    rw [hm]
  simp only [hshift]
  rw [hcomp, hval]

end RQMCMarkov.PointSets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Stratified sampling: variance at most MC, `O(n^{-3})` and `O(n^{-2})` rates (post #2)

Post #2: "RQMC using stratification would … use the same three sections and draw a random number
from each interval", and its codes do "stratification + random shift (it applies the same random
shift to all, rather than doing a different shift for each, both are valid)". Reading, in one
dimension with strata `[i/n, (i+1)/n)`, `i < n`, and `stratumMap n i u = (i + u)/n`:

* (a) independent stratification: points `(i + Vᵢ)/n` with `V₀, …, V_{n-1}` i.i.d. `U[0,1)`;
* (b) common shift: points `(i + U)/n` with one `U ~ U[0,1)`.

Both are unbiased (`integral_sampleMean_stratified` in `Unbiased`, and
`integral_sampleMean_commonShift` here); "valid" is read as unbiased.

## Main results

* `stratumMap_eq_midpoint_add`, `midpoint_shift_mem`: the stratified point `(i + u)/n` is the
  midpoint `(2i + 1)/(2n)` plus a shift in `[−1/(2n), 1/(2n))` (post #2's `U(−1/6, 1/6)`, `n = 3`).
* `variance_stratified_eq`: for (a), `Var = n⁻² Σᵢ Var(f | stratum i)`, with
  `Var(f | stratum i) = Var[u ↦ f((i + u)/n); U[0,1)]`, for every `f ∈ L²`.
* `variance_stratified_le_mc`: for (a), `Var ≤ σ²/n`, the MC variance (proportional allocation
  never loses), for every `f ∈ L²`.
* `integral_sq_sub_half_uniformIco`: `∫₀¹ (u − 1/2)² du = 1/12`; `variance_le_of_lipschitz_half`.
* `variance_stratified_le_lipschitz`: for (a) and `K`-Lipschitz `f`, `Var ≤ K²/(12 n³)`, the
  "faster than MC" rate `O(n^{-3})` (RMSE `O(n^{-3/2})`).
* `variance_commonShift_le_lipschitz`: for (b) and `K`-Lipschitz `f`, `Var ≤ K²/(12 n²)`
  (RMSE `O(n^{-1})`).
* `variance_uniformIco_id`, `variance_stratified_id`, `variance_commonShift_id`,
  `variance_stratified_id_lt_commonShift_id`: for `f(x) = x`, (a) has variance `1/(12 n³)` and
  (b) has `1/(12 n²)`, so for `n ≥ 2` the common shift is strictly worse, by the factor `n`.
* `sum_cond_eq_of_partition`, `variance_sampleMean_partition_le`: the general statement — for any
  probability space `(E, μ)`, a finite measurable partition into `n` cells of measure `1/n`, and
  independent points `Xᵢ ~ μ[|Aᵢ]` (`μ` conditioned on cell `i`), `Var ≤ Var_μ(f)/n`.

**Precision.** Post #2 calls both randomizations "valid": both are unbiased, but they are not
equally good. Independent shifts give `O(n^{-3})` variance for Lipschitz `f`, while one common
shift gives only `O(n^{-2})`, and `f(x) = x` shows the `n^{-2}` rate is attained
(`variance_commonShift_id`). The common shift is the randomly shifted lattice rule with generator
`1` (see `ShiftLimit`).
-/

namespace RQMCMarkov.PointSets

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `stratumMap n i` is continuous. -/
theorem continuous_stratumMap (n i : ℕ) : Continuous (stratumMap n i) :=
  (continuous_const.add continuous_id).div_const _

/-- **A stratified point is the QMC midpoint plus a shift** (post #2):
`(i + u)/n = (2i + 1)/(2n) + (u − 1/2)/n`. -/
theorem stratumMap_eq_midpoint_add {n : ℕ} (hn : n ≠ 0) (i : ℕ) (u : ℝ) :
    stratumMap n i u = (2 * i + 1) / (2 * n) + (u - 1 / 2) / n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  simp only [stratumMap]
  field_simp
  ring

/-- The shift `(u − 1/2)/n`, `u ∈ [0,1)`, lies in `[−1/(2n), 1/(2n))`; for `n = 3` this is post
#2's `U(−1/6, 1/6)`. -/
theorem midpoint_shift_mem {n : ℕ} (hn : n ≠ 0) {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) :
    (u - 1 / 2) / n ∈ Ico (-(1 / (2 * n : ℝ))) (1 / (2 * n)) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have h2n : (0 : ℝ) < 2 * n := by positivity
  have heq : (u - 1 / 2) / n = (2 * u - 1) / (2 * n) := by
    field_simp
  rw [heq, mem_Ico, ← neg_div, div_le_div_iff_of_pos_right h2n, div_lt_div_iff_of_pos_right h2n]
  exact ⟨by linarith [hu.1], by linarith [hu.2]⟩

/-- `∫₀¹ (u − 1/2)² du = 1/12`. -/
theorem integral_sq_sub_half_uniformIco : ∫ u, (u - 1 / 2) ^ 2 ∂uniformIco = 1 / 12 := by
  rw [uniformIco_eq_restrict_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_sub_right (fun x : ℝ ↦ x ^ 2), integral_pow]
  norm_num

/-- `∫₀¹ u du = 1/2`. -/
theorem integral_id_uniformIco : ∫ u, u ∂uniformIco = 1 / 2 := by
  rw [uniformIco_eq_restrict_Ioc, ← intervalIntegral.integral_of_le zero_le_one, integral_id]
  norm_num

/-- A continuous function is integrable for `U[0,1)`. -/
theorem integrable_uniformIco_of_continuous {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable g uniformIco :=
  (hg.integrableOn_Icc (a := 0) (b := 1)).mono_set Ico_subset_Icc_self

/-- **Variance bound from a Lipschitz-type bound at the midpoint.** If
`|g(u) − g(1/2)| ≤ C |u − 1/2|` on `[0,1)`, then `Var_{U[0,1)}(g) ≤ C²/12`. -/
theorem variance_le_of_lipschitz_half {g : ℝ → ℝ} (hg : AEStronglyMeasurable g uniformIco)
    {C : ℝ} (hC : ∀ u ∈ Ico (0 : ℝ) 1, |g u - g (1 / 2)| ≤ C * |u - 1 / 2|) :
    Var[g; uniformIco] ≤ C ^ 2 / 12 := by
  have := isProbabilityMeasure_uniformIco
  rw [← variance_sub_const hg (g (1 / 2))]
  refine (variance_le_expectation_sq (hg.sub aestronglyMeasurable_const)).trans ?_
  have hint : Integrable (fun u : ℝ ↦ C ^ 2 * (u - 1 / 2) ^ 2) uniformIco :=
    integrable_uniformIco_of_continuous (by fun_prop)
  calc ∫ u, ((fun u ↦ g u - g (1 / 2)) ^ 2) u ∂uniformIco
      ≤ ∫ u, C ^ 2 * (u - 1 / 2) ^ 2 ∂uniformIco := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun u ↦ sq_nonneg _) hint ?_
        refine ae_restrict_of_forall_mem measurableSet_Ico (fun u hu ↦ ?_)
        change (g u - g (1 / 2)) ^ 2 ≤ C ^ 2 * (u - 1 / 2) ^ 2
        have h0 : 0 ≤ |g u - g (1 / 2)| := abs_nonneg _
        calc (g u - g (1 / 2)) ^ 2 = |g u - g (1 / 2)| ^ 2 := (sq_abs _).symm
          _ ≤ (C * |u - 1 / 2|) ^ 2 := pow_le_pow_left₀ h0 (hC u hu) 2
          _ = C ^ 2 * (u - 1 / 2) ^ 2 := by rw [mul_pow, sq_abs]
    _ = C ^ 2 / 12 := by
        rw [integral_const_mul, integral_sq_sub_half_uniformIco]
        ring

/-- A Lipschitz function is in `L²(U[0,1))`. -/
theorem memLp_uniformIco_of_lipschitz {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (p : ℝ≥0∞) : MemLp f p uniformIco := by
  have := isProbabilityMeasure_uniformIco
  refine MemLp.of_bound hf.continuous.aestronglyMeasurable (|f 0| + K) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ico (fun x hx ↦ ?_)
  have h1 : |f x - f 0| ≤ K * |x - 0| := by
    have := hf.dist_le_mul x 0
    rwa [Real.dist_eq, Real.dist_eq] at this
  have h2 : |x - 0| ≤ 1 := by
    rw [sub_zero, abs_of_nonneg hx.1]
    exact hx.2.le
  rw [Real.norm_eq_abs]
  calc |f x| = |f 0 + (f x - f 0)| := by ring_nf
    _ ≤ |f 0| + |f x - f 0| := abs_add_le _ _
    _ ≤ |f 0| + K * 1 := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_left h2 K.2)
    _ = |f 0| + K := by rw [mul_one]

/-- The stratum-`i` component of a `K`-Lipschitz `f` satisfies the midpoint bound with
constant `K/n`. -/
theorem abs_sub_stratumMap_half_le {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) {n : ℕ}
    (hn : n ≠ 0) (i : ℕ) (u : ℝ) :
    |f (stratumMap n i u) - f (stratumMap n i (1 / 2))| ≤ (K / n) * |u - 1 / 2| := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have := hf.dist_le_mul (stratumMap n i u) (stratumMap n i (1 / 2))
  rw [Real.dist_eq, Real.dist_eq] at this
  have heq : stratumMap n i u - stratumMap n i (1 / 2) = (u - 1 / 2) / n := by
    simp only [stratumMap]
    ring
  rw [heq, abs_div, abs_of_pos hn'] at this
  calc |f (stratumMap n i u) - f (stratumMap n i (1 / 2))| ≤ K * (|u - 1 / 2| / n) := this
    _ = (K / n) * |u - 1 / 2| := by ring

/-- **Independent stratification, exact variance** (post #2): for `Vᵢ` i.i.d. `U[0,1)` and
`f ∈ L²`, `Var((1/n) Σᵢ f((i + Vᵢ)/n)) = n⁻² Σᵢ Var(f | stratum i)`. -/
theorem variance_stratified_eq {n : ℕ} (hn : n ≠ 0) {P : Measure Ω} {V : Fin n → Ω → ℝ}
    (hV : ∀ i, HasLaw (V i) uniformIco P) (hind : iIndepFun V P) {f : ℝ → ℝ}
    (hf : MemLp f 2 uniformIco) :
    Var[fun ω ↦ sampleMean n f (fun i ↦ stratumMap n i (V i ω)); P] =
      ((n : ℝ)⁻¹) ^ 2 * ∑ i : Fin n, Var[fun u ↦ f (stratumMap n i u); uniformIco] := by
  have hX : ∀ i : Fin n, AEMeasurable (fun ω ↦ stratumMap n i (V i ω)) P := fun i ↦
    (measurable_stratumMap n i).comp_aemeasurable (hV i).aemeasurable
  have hind' : iIndepFun (fun (i : Fin n) ω ↦ stratumMap n i (V i ω)) P :=
    hind.comp (fun i ↦ stratumMap n i) (fun i ↦ measurable_stratumMap n i)
  have hμ := sum_map_stratified hn hV
  rw [variance_sampleMean_of_sum_map_eq hX hind' hμ hf]
  congr 1
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  have hL := memLp_map_of_sum_map_eq hμ hf i
  have hmap : P.map (fun ω ↦ stratumMap n i (V i ω)) = uniformIco.map (stratumMap n i) := by
    rw [← (hV i).map_eq, AEMeasurable.map_map_of_aemeasurable
      (measurable_stratumMap n i).aemeasurable (hV i).aemeasurable]
    rfl
  rw [hmap] at hL ⊢
  rw [variance_map hL.aestronglyMeasurable.aemeasurable (measurable_stratumMap n i).aemeasurable]
  rfl

/-- **Independent stratification never does worse than MC** (post #2, proportional allocation):
for `Vᵢ` i.i.d. `U[0,1)` and every `f ∈ L²`, `Var((1/n) Σᵢ f((i + Vᵢ)/n)) ≤ σ²/n`, where
`σ² = Var_{U[0,1)}(f)` and `σ²/n` is the MC variance (`variance_sampleMean_iid`). -/
theorem variance_stratified_le_mc {n : ℕ} (hn : n ≠ 0) {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Fin n → Ω → ℝ} (hV : ∀ i, HasLaw (V i) uniformIco P) (hind : iIndepFun V P)
    {f : ℝ → ℝ} (hf : MemLp f 2 uniformIco) :
    Var[fun ω ↦ sampleMean n f (fun i ↦ stratumMap n i (V i ω)); P] ≤ Var[f; uniformIco] / n :=
  variance_sampleMean_le_of_sum_map_eq hn
    (fun i ↦ (measurable_stratumMap n i).comp_aemeasurable (hV i).aemeasurable)
    (hind.comp (fun i ↦ stratumMap n i) (fun i ↦ measurable_stratumMap n i))
    (sum_map_stratified hn hV) hf

/-- **Independent stratification, Lipschitz rate `O(n^{-3})`** (post #2): for `Vᵢ` i.i.d.
`U[0,1)` and `K`-Lipschitz `f`, `Var((1/n) Σᵢ f((i + Vᵢ)/n)) ≤ K²/(12 n³)`. -/
theorem variance_stratified_le_lipschitz {n : ℕ} (hn : n ≠ 0) {P : Measure Ω}
    {V : Fin n → Ω → ℝ} (hV : ∀ i, HasLaw (V i) uniformIco P) (hind : iIndepFun V P)
    {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    Var[fun ω ↦ sampleMean n f (fun i ↦ stratumMap n i (V i ω)); P] ≤
      (K : ℝ) ^ 2 / (12 * n ^ 3) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  rw [variance_stratified_eq hn hV hind (memLp_uniformIco_of_lipschitz hf 2)]
  have hle : ∀ i : Fin n, Var[fun u ↦ f (stratumMap n i u); uniformIco] ≤ (K / n) ^ 2 / 12 :=
    fun i ↦ variance_le_of_lipschitz_half
      (hf.continuous.comp (continuous_stratumMap n i)).aestronglyMeasurable
      (fun u _ ↦ abs_sub_stratumMap_half_le hf hn i u)
  calc ((n : ℝ)⁻¹) ^ 2 * ∑ i : Fin n, Var[fun u ↦ f (stratumMap n i u); uniformIco]
      ≤ ((n : ℝ)⁻¹) ^ 2 * ∑ _i : Fin n, ((K : ℝ) / n) ^ 2 / 12 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ hle i) (sq_nonneg _)
    _ = (K : ℝ) ^ 2 / (12 * n ^ 3) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-- **The common shift is unbiased** (post #2): with one `U ~ U[0,1)`,
`E[(1/n) Σᵢ f((i + U)/n)] = ∫₀¹ f`. -/
theorem integral_sampleMean_commonShift {n : ℕ} (hn : n ≠ 0) {P : Measure Ω} {U : Ω → ℝ}
    (hU : HasLaw U uniformIco P) {f : ℝ → ℝ} (hf : Integrable f uniformIco) :
    ∫ ω, sampleMean n f (fun i ↦ stratumMap n i (U ω)) ∂P = ∫ x, f x ∂uniformIco :=
  integral_sampleMean_stratified hn (V := fun _ ↦ U) (fun _ ↦ hU) hf

/-- **The common shift, Lipschitz rate `O(n^{-2})`** (post #2): with one `U ~ U[0,1)` and
`K`-Lipschitz `f`, `Var((1/n) Σᵢ f((i + U)/n)) ≤ K²/(12 n²)`. -/
theorem variance_commonShift_le_lipschitz {n : ℕ} (hn : n ≠ 0) {P : Measure Ω} {U : Ω → ℝ}
    (hU : HasLaw U uniformIco P) {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    Var[fun ω ↦ sampleMean n f (fun i ↦ stratumMap n i (U ω)); P] ≤ (K : ℝ) ^ 2 / (12 * n ^ 2) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  set G : ℝ → ℝ := fun u ↦ sampleMean n f (fun i ↦ stratumMap n i u) with hG
  have hGc : Continuous G := by
    simp only [hG, sampleMean]
    exact continuous_const.mul (continuous_finsetSum _ (fun i _ ↦
      hf.continuous.comp (continuous_stratumMap n i)))
  have hfun : (fun ω ↦ sampleMean n f (fun i ↦ stratumMap n i (U ω))) = G ∘ U := rfl
  rw [hfun, ← variance_map (hU.map_eq ▸ hGc.aemeasurable) hU.aemeasurable, hU.map_eq]
  have hbound : ∀ u ∈ Ico (0 : ℝ) 1, |G u - G (1 / 2)| ≤ (K / n) * |u - 1 / 2| := by
    intro u _
    simp only [hG, sampleMean]
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_inv, abs_of_pos hn']
    calc (n : ℝ)⁻¹ * |∑ i : Fin n, (f (stratumMap n i u) - f (stratumMap n i (1 / 2)))|
        ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, |f (stratumMap n i u) - f (stratumMap n i (1 / 2))| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.2 hn'.le)
      _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, (K / n) * |u - 1 / 2| :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦
            abs_sub_stratumMap_half_le hf hn i u) (inv_nonneg.2 hn'.le)
      _ = (K / n) * |u - 1 / 2| := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
            inv_mul_cancel₀ hn'.ne', one_mul]
  calc Var[G; uniformIco] ≤ ((K : ℝ) / n) ^ 2 / 12 :=
        variance_le_of_lipschitz_half hGc.aestronglyMeasurable hbound
    _ = (K : ℝ) ^ 2 / (12 * n ^ 2) := by
        field_simp

/-- `Var_{U[0,1)}(u) = 1/12`. -/
theorem variance_uniformIco_id : Var[fun u : ℝ ↦ u; uniformIco] = 1 / 12 := by
  rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_uniformIco,
    integral_sq_sub_half_uniformIco]

/-- `Var_{U[0,1)}(c + d u) = d²/12`. -/
theorem variance_uniformIco_affine (c d : ℝ) :
    Var[fun u : ℝ ↦ c + d * u; uniformIco] = d ^ 2 / 12 := by
  have := isProbabilityMeasure_uniformIco
  rw [variance_const_add (measurable_id'.const_mul d).aestronglyMeasurable c, variance_const_mul,
    variance_uniformIco_id]
  ring

/-- **Independent stratification for `f(x) = x`**: `Var = 1/(12 n³)`. -/
theorem variance_stratified_id {n : ℕ} (hn : n ≠ 0) {P : Measure Ω} {V : Fin n → Ω → ℝ}
    (hV : ∀ i, HasLaw (V i) uniformIco P) (hind : iIndepFun V P) :
    Var[fun ω ↦ sampleMean n id (fun i ↦ stratumMap n i (V i ω)); P] = 1 / (12 * n ^ 3) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  rw [variance_stratified_eq hn hV hind (memLp_uniformIco_of_lipschitz LipschitzWith.id 2)]
  have hi : ∀ i : Fin n, Var[fun u ↦ id (stratumMap n i u); uniformIco] = ((n : ℝ)⁻¹) ^ 2 / 12 := by
    intro i
    have hfun : (fun u ↦ id (stratumMap n i u)) = fun u : ℝ ↦ (i : ℝ) / n + (n : ℝ)⁻¹ * u := by
      funext u
      simp only [id, stratumMap]
      ring
    rw [hfun, variance_uniformIco_affine]
  rw [Finset.sum_congr rfl (fun i _ ↦ hi i), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

/-- **The common shift for `f(x) = x`**: `Var = 1/(12 n²)`, so the `n^{-2}` rate of
`variance_commonShift_le_lipschitz` is attained. -/
theorem variance_commonShift_id {n : ℕ} (hn : n ≠ 0) {P : Measure Ω} {U : Ω → ℝ}
    (hU : HasLaw U uniformIco P) :
    Var[fun ω ↦ sampleMean n id (fun i ↦ stratumMap n i (U ω)); P] = 1 / (12 * n ^ 2) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  set c : ℝ := (n : ℝ)⁻¹ * ∑ i : Fin n, (i : ℝ) / n with hc
  have hG : (fun u ↦ sampleMean n id (fun i ↦ stratumMap n i u)) =
      fun u : ℝ ↦ c + (n : ℝ)⁻¹ * u := by
    funext u
    simp only [hc, sampleMean, id, stratumMap]
    rw [Finset.sum_congr rfl (fun (i : Fin n) _ ↦ add_div (i : ℝ) u n), Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hfun : (fun ω ↦ sampleMean n id (fun i ↦ stratumMap n i (U ω))) =
      (fun u ↦ sampleMean n id (fun i ↦ stratumMap n i u)) ∘ U := rfl
  have hGm : Measurable (fun u ↦ sampleMean n id (fun i ↦ stratumMap n i u)) := by
    rw [hG]
    fun_prop
  rw [hfun, ← variance_map (hU.map_eq ▸ hGm.aemeasurable) hU.aemeasurable, hU.map_eq, hG,
    variance_uniformIco_affine]
  field_simp

/-- **The common shift is strictly worse for `f(x) = x`** once `n ≥ 2`:
`Var(independent) = 1/(12 n³) < 1/(12 n²) = Var(common shift)`. -/
theorem variance_stratified_id_lt_commonShift_id {n : ℕ} (hn : 2 ≤ n) {P : Measure Ω}
    {V : Fin n → Ω → ℝ} (hV : ∀ i, HasLaw (V i) uniformIco P) (hind : iIndepFun V P)
    {U : Ω → ℝ} (hU : HasLaw U uniformIco P) :
    Var[fun ω ↦ sampleMean n id (fun i ↦ stratumMap n i (V i ω)); P] <
      Var[fun ω ↦ sampleMean n id (fun i ↦ stratumMap n i (U ω)); P] := by
  have hn0 : n ≠ 0 := by omega
  rw [variance_stratified_id hn0 hV hind, variance_commonShift_id hn0 hU]
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < 12 * n ^ 2 := by positivity
  rw [div_lt_div_iff_of_pos_left one_pos (by positivity) hpos]
  nlinarith

/-- **Cells of a partition with `μ`-measure `1/n`**: the conditional laws `μ[|Aᵢ]` sum to
`n • μ`. -/
theorem sum_cond_eq_of_partition {E : Type*} {mE : MeasurableSpace E} {μ : Measure E} {n : ℕ}
    {A : Fin n → Set E} (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A)) (hcover : ⋃ i, A i = univ)
    (hμA : ∀ i, μ (A i) = (n : ℝ≥0∞)⁻¹) :
    ∑ i, μ[|A i] = (n : ℝ≥0∞) • μ := by
  have hc : ∀ i, μ[|A i] = (n : ℝ≥0∞) • μ.restrict (A i) := fun i ↦ by
    rw [ProbabilityTheory.cond, hμA i, inv_inv]
  rw [Finset.sum_congr rfl (fun i _ ↦ hc i), ← Finset.smul_sum, ← Measure.sum_fintype,
    ← Measure.restrict_iUnion hdisj hA, hcover, Measure.restrict_univ]

/-- **Stratified sampling with proportional allocation never loses to MC**, in any dimension:
for a measurable partition `A₀, …, A_{n-1}` of `E` into cells of `μ`-measure `1/n` and independent
points `Xᵢ ~ μ[|Aᵢ]` (one uniform point in each cell when `μ` is uniform),
`Var((1/n) Σᵢ f(Xᵢ)) ≤ Var_μ(f)/n` for every `f ∈ L²(μ)`; the estimator is unbiased. -/
theorem variance_sampleMean_partition_le {E : Type*} {mE : MeasurableSpace E} {μ : Measure E}
    {n : ℕ} (hn : n ≠ 0) {A : Fin n → Set E} (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A)) (hcover : ⋃ i, A i = univ)
    (hμA : ∀ i, μ (A i) = (n : ℝ≥0∞)⁻¹) {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Fin n → Ω → E} (hX : ∀ i, HasLaw (X i) μ[|A i] P) (hind : iIndepFun X P)
    {f : E → ℝ} (hf : MemLp f 2 μ) :
    ∫ ω, sampleMean n f (fun i ↦ X i ω) ∂P = ∫ x, f x ∂μ ∧
      Var[fun ω ↦ sampleMean n f (fun i ↦ X i ω); P] ≤ Var[f; μ] / n := by
  have hsum : ∑ i, P.map (X i) = (n : ℝ≥0∞) • μ := by
    rw [Finset.sum_congr rfl (fun i _ ↦ (hX i).map_eq)]
    exact sum_cond_eq_of_partition hA hdisj hcover hμA
  have hμ : IsFiniteMeasure μ := by
    have h1 : μ univ = ∑ i, μ (A i) := by
      rw [← hcover, measure_iUnion hdisj hA, tsum_fintype]
    refine ⟨?_⟩
    rw [h1, Finset.sum_congr rfl (fun i _ ↦ hμA i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ENNReal.mul_inv_cancel (Nat.cast_ne_zero.2 hn)
        (ENNReal.natCast_ne_top n)]
    exact ENNReal.one_lt_top
  exact ⟨integral_sampleMean_of_sum_map_eq hn (fun i ↦ (hX i).aemeasurable) hsum
      (hf.integrable one_le_two),
    variance_sampleMean_le_of_sum_map_eq hn (fun i ↦ (hX i).aemeasurable) hind hsum hf⟩

end RQMCMarkov.PointSets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The randomly shifted lattice rule is not asymptotically normal (post #2)

Post #2: "If we use an RQMC estimator with a randomly-shifted lattice rule, the limiting
distribution as `n → ∞` is usually a spline, not a normal distribution" (L'Ecuyer, Munger and
Tuffin 2010). Reading, in one dimension: the rank-1 lattice with generator `1`, `{i/n : i < n}`,
randomly shifted, is the common-shift stratified rule `μ̂ₙ(U) = (1/n) Σᵢ f((i + U)/n)` with
`U ~ U[0,1)` (as point SETS, `{fract (i/n + U)} = {(i + fract (n U))/n}`; we work with the labelling
`(i + U)/n`, which makes the convergence below almost sure; `ShiftLimitLattice` proves the
identification and transfers the results to the lattice labelling).

## Main results

* `scaled_error_id`: for `f(x) = x`, `n (μ̂ₙ(u) − 1/2) = u − 1/2` EXACTLY, for every `n ≥ 1` and
  every `u`; `hasLaw_scaled_error_id`: so the scaled error has law `U[−1/2, 1/2)` for every `n`.
* `cell_error_le`: on one cell `[a, a + h]`, for `C¹` `f` whose derivative varies by at most `ε`,
  `|f(a + u h) − (1/h)∫ₐ^{a+h} f − (u − 1/2)(f(a + h) − f(a))| ≤ 3 ε h`.
* `tendsto_scaled_error`: for `f` that is `C¹` on `[0,1]` and every `u ∈ [0,1]`,
  `n (μ̂ₙ(u) − ∫₀¹ f) → (f(1) − f(0)) (u − 1/2)`.
* `ae_tendsto_scaled_error`, `tendstoInDistribution_scaled_error`: hence almost surely, and in
  distribution, `n (μ̂ₙ(U) − μ) → (f(1) − f(0)) (U − 1/2)`.
* `map_mul_sub_half_uniformIco`: the limit law is uniform on `[−|c|/2, |c|/2]`, `c = f(1) − f(0)`,
  with density `1/|c|` — a degree-0 spline — whenever `f(1) ≠ f(0)` (a point mass at 0 otherwise).
* `ne_gaussianReal_of_measure_Ioi_eq_zero`: a law with bounded support is not a Gaussian
  `gaussianReal m v` with `v ≠ 0`; `limit_law_ne_gaussianReal` and
  `not_tendstoInDistribution_scaled_error_gaussian`: the scaled error `n (μ̂ₙ − μ)` does not
  converge in distribution to any non-degenerate normal law.
* `tendsto_sqrt_scaled_error`, `ae_tendsto_sqrt_scaled_error`,
  `not_tendstoInDistribution_sqrt_scaled_error_gaussian`: at the MC scale `√n`,
  `√n (μ̂ₙ − μ) → 0` almost surely, so the estimator is not asymptotically normal at the `√n`
  scale either (contrast `tendstoInDistribution_sampleMean_iid` for MC).

**Hypotheses.** `C¹` on `[0,1]` is `∀ x ∈ [0,1], HasDerivWithinAt f (f' x) [0,1] x` with `f'`
continuous on `[0,1]`. The random statements also assume `f` measurable (`f` is otherwise
unconstrained outside `[0,1]`).

**Precision.** "Usually a spline": in one dimension with the generator-1 lattice the limit is
exactly the uniform law (degree-0 spline) for every `C¹` `f` with `f(1) ≠ f(0)`, and the point mass
at `0` (a degenerate law, still not a non-degenerate normal) when `f(1) = f(0)` — then the error is
`o(1/n)` and a finer scale is needed. Owen scrambling's CLT (Loh 2003) is not formalised here.
-/

namespace RQMCMarkov.PointSets

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `∫ f dU[0,1) = ∫₀¹ f`. -/
theorem integral_uniformIco_eq_intervalIntegral (f : ℝ → ℝ) :
    ∫ x, f x ∂uniformIco = ∫ x in (0 : ℝ)..1, f x := by
  rw [uniformIco_eq_restrict_Ioc, intervalIntegral.integral_of_le zero_le_one]

/-- `Σ_{i<n} i = n (n − 1)/2`, in `ℝ`. -/
theorem sum_range_natCast (n : ℕ) : ∑ i ∈ Finset.range n, (i : ℝ) = n * (n - 1) / 2 := by
  induction n with
  | zero => rw [Finset.sum_range_zero, Nat.cast_zero, zero_mul, zero_div]
  | succ k ih =>
      rw [Finset.sum_range_succ, ih, Nat.cast_succ]
      ring

/-- **The scaled error for `f(x) = x` is exactly `u − 1/2`**: for every `n ≥ 1` and every `u`,
`n ((1/n) Σᵢ (i + u)/n − 1/2) = u − 1/2`. -/
theorem scaled_error_id {n : ℕ} (hn : n ≠ 0) (u : ℝ) :
    (n : ℝ) * (sampleMean n id (fun i ↦ stratumMap n i u) - 1 / 2) = u - 1 / 2 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  unfold sampleMean
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ id (stratumMap n k u)) n]
  simp only [id, stratumMap]
  rw [← Finset.sum_div, Finset.sum_add_distrib, sum_range_natCast, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  field_simp
  ring

/-- The law of `U − 1/2`, `U ~ U[0,1)`, is the uniform law on `[−1/2, 1/2)`. -/
theorem map_sub_half_uniformIco :
    uniformIco.map (fun u ↦ u - 1 / 2) = volume.restrict (Ico (-(1 / 2) : ℝ) (1 / 2)) := by
  have hfun : (fun u : ℝ ↦ u - 1 / 2) = fun u ↦ -(1 / 2) + u := by
    funext u
    ring
  have hpre : (fun u : ℝ ↦ -(1 / 2) + u) ⁻¹' Ico (-(1 / 2)) (1 / 2) = Ico 0 1 := by
    ext u
    simp only [mem_preimage, mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  change (volume.restrict (Ico (0 : ℝ) 1)).map _ = _
  rw [hfun, ← hpre, ← Measure.restrict_map (measurable_const_add _) measurableSet_Ico,
    map_add_left_eq_self]

/-- **The scaled error for `f(x) = x` is uniform on `[−1/2, 1/2)` for every `n ≥ 1`**: with
`U ~ U[0,1)`, `n (μ̂ₙ(U) − 1/2) ~ U[−1/2, 1/2)`. No normal limit is possible. -/
theorem hasLaw_scaled_error_id {n : ℕ} (hn : n ≠ 0) {P : Measure Ω} {U : Ω → ℝ}
    (hU : HasLaw U uniformIco P) :
    HasLaw (fun ω ↦ (n : ℝ) * (sampleMean n id (fun i ↦ stratumMap n i (U ω)) - 1 / 2))
      (volume.restrict (Ico (-(1 / 2) : ℝ) (1 / 2))) P := by
  have hfun : (fun ω ↦ (n : ℝ) * (sampleMean n id (fun i ↦ stratumMap n i (U ω)) - 1 / 2)) =
      (fun u ↦ u - 1 / 2) ∘ U := by
    funext ω
    exact scaled_error_id hn (U ω)
  rw [hfun, ← map_sub_half_uniformIco]
  exact (hasLaw_map (measurable_sub_const _).aemeasurable).comp hU

/-- **Error on one cell.** If `f` is differentiable on `[a, a + h]` (`h > 0`) with
`|f'(x) − f'(a)| ≤ ε` there, then for `u ∈ [0,1]`
`|f(a + u h) − (1/h) ∫ₐ^{a+h} f − (u − 1/2)(f(a + h) − f(a))| ≤ 3 ε h`. -/
theorem cell_error_le {f f' : ℝ → ℝ} {a h ε : ℝ} (hh : 0 < h)
    (hf : ∀ x ∈ Icc a (a + h), HasDerivWithinAt f (f' x) (Icc a (a + h)) x)
    (hε : ∀ x ∈ Icc a (a + h), |f' x - f' a| ≤ ε) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    |f (a + u * h) - h⁻¹ * (∫ x in a..a + h, f x) - (u - 1 / 2) * (f (a + h) - f a)| ≤
      3 * ε * h := by
  have hah : a ≤ a + h := by linarith
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hε a (left_mem_Icc.2 hah))
  set g : ℝ → ℝ := fun x ↦ f x - f' a * x with hg
  have hgd : ∀ x ∈ Icc a (a + h), HasDerivWithinAt g (f' x - f' a) (Icc a (a + h)) x := by
    intro x hx
    exact ((hf x hx).sub ((hasDerivWithinAt_id x _).const_mul (f' a))).congr_deriv (by ring)
  have hgc : ContinuousOn g (Icc a (a + h)) := fun x hx ↦ (hgd x hx).continuousWithinAt
  have hmvt : ∀ y ∈ Icc a (a + h), |g y - g a| ≤ ε * h := by
    intro y hy
    have := norm_image_sub_le_of_norm_deriv_le_segment' hgd
      (fun x hx ↦ by rw [Real.norm_eq_abs]; exact hε x (Ico_subset_Icc_self hx)) y hy
    rw [Real.norm_eq_abs] at this
    exact this.trans (mul_le_mul_of_nonneg_left (by linarith [hy.2]) hε0)
  have huIcc : uIcc a (a + h) = Icc a (a + h) := uIcc_of_le hah
  have hint1 : IntervalIntegrable (fun x ↦ g x - g a) volume a (a + h) :=
    ContinuousOn.intervalIntegrable (by rw [huIcc]; exact hgc.sub continuousOn_const)
  have hint2 : IntervalIntegrable (fun x ↦ g a + f' a * x) volume a (a + h) :=
    (continuous_const.add (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hfx : ∀ x, f x = (g x - g a) + (g a + f' a * x) := fun x ↦ by
    simp only [hg]
    ring
  have hI : (∫ x in a..a + h, f x) =
      (∫ x in a..a + h, (g x - g a)) + (g a * h + f' a * (((a + h) ^ 2 - a ^ 2) / 2)) := by
    rw [intervalIntegral.integral_congr (fun x _ ↦ hfx x),
      intervalIntegral.integral_add hint1 hint2,
      intervalIntegral.integral_add (f := fun _ ↦ g a) (g := fun x ↦ f' a * x)
        intervalIntegrable_const ((continuous_const.mul continuous_id).intervalIntegrable _ _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id,
      smul_eq_mul]
    ring
  set I := ∫ x in a..a + h, (g x - g a) with hIdef
  have hIb : |I| ≤ ε * h * h := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := a + h)
      (f := fun x ↦ g x - g a) (C := ε * h) (fun x hx ↦ by
        rw [Real.norm_eq_abs]
        rw [uIoc_of_le hah] at hx
        exact hmvt x (Ioc_subset_Icc_self hx))
    rw [Real.norm_eq_abs, add_sub_cancel_left, abs_of_pos hh] at this
    rw [hIdef]
    exact this
  have hE : f (a + u * h) - h⁻¹ * (∫ x in a..a + h, f x) - (u - 1 / 2) * (f (a + h) - f a) =
      (g (a + u * h) - g a) - h⁻¹ * I - (u - 1 / 2) * (g (a + h) - g a) := by
    rw [hI]
    simp only [hg]
    field_simp
    ring
  rw [hE]
  have hu' : a + u * h ∈ Icc a (a + h) := ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩
  have h1 := abs_le.1 (hmvt _ hu')
  have h2 : |h⁻¹ * I| ≤ ε * h := by
    rw [abs_mul, abs_inv, abs_of_pos hh]
    calc h⁻¹ * |I| ≤ h⁻¹ * (ε * h * h) := mul_le_mul_of_nonneg_left hIb (inv_nonneg.2 hh.le)
      _ = ε * h := by field_simp
  have h3 : |(u - 1 / 2) * (g (a + h) - g a)| ≤ ε * h := by
    rw [abs_mul]
    have hu2 : |u - 1 / 2| ≤ 1 := abs_le.2 ⟨by linarith [hu.1], by linarith [hu.2]⟩
    calc |u - 1 / 2| * |g (a + h) - g a| ≤ 1 * (ε * h) :=
          mul_le_mul hu2 (hmvt _ (right_mem_Icc.2 hah)) (abs_nonneg _) zero_le_one
      _ = ε * h := one_mul _
  have h2' := abs_le.1 h2
  have h3' := abs_le.1 h3
  exact abs_le.2 ⟨by linarith [h1.1, h2'.2, h3'.2], by linarith [h1.2, h2'.1, h3'.1]⟩

/-- **The scaled error of the randomly shifted lattice converges** (L'Ecuyer–Munger–Tuffin
2010, generator `1`, one dimension): if `f` is `C¹` on `[0,1]`, then for every `u ∈ [0,1]`,
`n ((1/n) Σᵢ f((i + u)/n) − ∫₀¹ f) → (f(1) − f(0)) (u − 1/2)` as `n → ∞`. -/
theorem tendsto_scaled_error {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) *
        (sampleMean n f (fun i ↦ stratumMap n i u) - ∫ x in (0 : ℝ)..1, f x))
      atTop (𝓝 ((f 1 - f 0) * (u - 1 / 2))) := by
  have hcont : ContinuousOn f (Icc 0 1) := fun x hx ↦ (hf x hx).continuousWithinAt
  have huc : UniformContinuousOn f' (Icc 0 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf'
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.1 huc (ε / 4) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  refine ⟨N + 1, fun n hn ↦ ?_⟩
  have hnN : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hnz : n ≠ 0 := by
    rintro rfl
    rw [Nat.cast_zero] at hn0
    exact lt_irrefl 0 hn0
  set h : ℝ := 1 / n with hhdef
  have hh : 0 < h := by positivity
  have hhδ : h < δ := by
    rw [hhdef, div_lt_iff₀ hn0]
    rw [div_lt_iff₀ hδ] at hN
    nlinarith
  set a : ℕ → ℝ := fun k ↦ (k : ℝ) / n with hadef
  have ha : ∀ k : ℕ, a k + h = a (k + 1) := by
    intro k
    simp only [hadef, hhdef]
    push_cast
    ring
  have ha0 : a 0 = 0 := by simp only [hadef, Nat.cast_zero, zero_div]
  have han : a n = 1 := by simp only [hadef]; exact div_self hn0.ne'
  have hcell : ∀ k < n, Icc (a k) (a k + h) ⊆ Icc 0 1 := by
    intro k hk x hx
    have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
    have hak : 0 ≤ a k := by simp only [hadef]; positivity
    have hak1 : a k + h ≤ 1 := by
      rw [ha k, hadef]
      simp only
      rw [div_le_one hn0]
      push_cast
      exact hk'
    exact ⟨hak.trans hx.1, hx.2.trans hak1⟩
  -- the sample mean, the integral and the telescoping sum, cell by cell
  have hsumf : (n : ℝ) * sampleMean n f (fun i ↦ stratumMap n i u) =
      ∑ k ∈ Finset.range n, f (a k + u * h) := by
    unfold sampleMean
    rw [← mul_assoc, mul_inv_cancel₀ hn0.ne', one_mul,
      Fin.sum_univ_eq_sum_range (fun k ↦ f (stratumMap n k u)) n]
    refine Finset.sum_congr rfl (fun k _ ↦ ?_)
    congr 1
    simp only [stratumMap, hadef, hhdef]
    ring
  have hint : (∫ x in (0 : ℝ)..1, f x) = ∑ k ∈ Finset.range n, ∫ x in a k..a k + h, f x := by
    have hii : ∀ k < n, IntervalIntegrable f volume (a k) (a (k + 1)) := by
      intro k hk
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le (by rw [← ha k]; linarith), ← ha k]
      exact hcont.mono (hcell k hk)
    rw [← ha0, ← han, ← intervalIntegral.sum_integral_adjacent_intervals hii]
    refine Finset.sum_congr rfl (fun k _ ↦ ?_)
    rw [ha k]
  have htel : ∑ k ∈ Finset.range n, (f (a k + h) - f (a k)) = f 1 - f 0 := by
    rw [Finset.sum_congr rfl (fun k _ ↦ by rw [ha k]),
      Finset.sum_range_sub (fun k ↦ f (a k)) n, han, ha0]
  have hid : (n : ℝ) * (sampleMean n f (fun i ↦ stratumMap n i u) - ∫ x in (0 : ℝ)..1, f x) -
      (f 1 - f 0) * (u - 1 / 2) = ∑ k ∈ Finset.range n,
        (f (a k + u * h) - h⁻¹ * (∫ x in a k..a k + h, f x) -
          (u - 1 / 2) * (f (a k + h) - f (a k))) := by
    have hhinv : h⁻¹ = n := by rw [hhdef, one_div, inv_inv]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← hsumf, ← hint, htel, hhinv]
    ring
  -- each cell contributes at most `3 (ε/4) h`
  have hbound : ∀ k ∈ Finset.range n, |f (a k + u * h) - h⁻¹ * (∫ x in a k..a k + h, f x) -
      (u - 1 / 2) * (f (a k + h) - f (a k))| ≤ 3 * (ε / 4) * h := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    have hsub := hcell k hk'
    refine cell_error_le hh (fun x hx ↦ (hf x (hsub hx)).mono hsub) (fun x hx ↦ ?_) hu
    have hdist : dist x (a k) < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hx.1])]
      linarith [hx.2]
    exact (hδf x (hsub hx) (a k) (hsub (left_mem_Icc.2 (by linarith))) hdist).le
  rw [Real.dist_eq, hid]
  calc |∑ k ∈ Finset.range n, (f (a k + u * h) - h⁻¹ * (∫ x in a k..a k + h, f x) -
          (u - 1 / 2) * (f (a k + h) - f (a k)))|
      ≤ ∑ k ∈ Finset.range n, |f (a k + u * h) - h⁻¹ * (∫ x in a k..a k + h, f x) -
          (u - 1 / 2) * (f (a k + h) - f (a k))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range n, 3 * (ε / 4) * h := Finset.sum_le_sum hbound
    _ = 3 * ε / 4 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hhdef]
        field_simp
    _ < ε := by linarith

/-- A uniform draw lies in `[0,1)` almost surely. -/
theorem ae_mem_Ico_of_hasLaw {P : Measure Ω} {U : Ω → ℝ} (hU : HasLaw U uniformIco P) :
    ∀ᵐ ω ∂P, U ω ∈ Ico (0 : ℝ) 1 := by
  have h : ∀ᵐ x ∂(P.map U), x ∈ Ico (0 : ℝ) 1 := by
    rw [hU.map_eq]
    exact ae_restrict_mem measurableSet_Ico
  exact ae_of_ae_map hU.aemeasurable h

/-- The common-shift estimate is a measurable function of the shift, for measurable `f`. -/
theorem measurable_sampleMean_stratumMap {f : ℝ → ℝ} (hfm : Measurable f) (n : ℕ) :
    Measurable fun u ↦ sampleMean n f (fun i ↦ stratumMap n i u) := by
  change Measurable fun u ↦ (n : ℝ)⁻¹ * ∑ i : Fin n, f (stratumMap n i u)
  refine Measurable.const_mul ?_ _
  exact Finset.measurable_fun_sum _ (fun i _ ↦ (hfm.comp (measurable_stratumMap n i) :))

/-- **Almost sure convergence of the scaled error** (L'Ecuyer–Munger–Tuffin 2010, one
dimension, generator `1`): for `f` `C¹` on `[0,1]` and `U ~ U[0,1)`,
`n (μ̂ₙ(U) − ∫₀¹ f) → (f(1) − f(0)) (U − 1/2)` almost surely. -/
theorem ae_tendsto_scaled_error {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) {P : Measure Ω} {U : Ω → ℝ} (hU : HasLaw U uniformIco P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ (n : ℝ) *
        (sampleMean n f (fun i ↦ stratumMap n i (U ω)) - ∫ x in (0 : ℝ)..1, f x))
      atTop (𝓝 ((f 1 - f 0) * (U ω - 1 / 2))) := by
  filter_upwards [ae_mem_Ico_of_hasLaw hU] with ω hω
  exact tendsto_scaled_error hf hf' (Ico_subset_Icc_self hω)

/-- **Convergence in distribution of the scaled error**: for measurable `f`, `C¹` on `[0,1]`,
`n (μ̂ₙ(U) − ∫₀¹ f) ⇒ (f(1) − f(0)) (U − 1/2)`. -/
theorem tendstoInDistribution_scaled_error {f f' : ℝ → ℝ} (hfm : Measurable f)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) {P : Measure Ω} [IsProbabilityMeasure P] {U : Ω → ℝ}
    (hU : HasLaw U uniformIco P) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (n : ℝ) *
        (sampleMean n f (fun i ↦ stratumMap n i (U ω)) - ∫ x in (0 : ℝ)..1, f x))
      atTop (fun ω ↦ (f 1 - f 0) * (U ω - 1 / 2)) (fun _ ↦ P) P :=
  tendstoInDistribution_of_ae_tendsto
    (fun n ↦ (((measurable_sampleMean_stratumMap hfm n).sub_const _).const_mul _).comp_aemeasurable
      hU.aemeasurable)
    (((measurable_id'.sub_const _).const_mul _).comp_aemeasurable hU.aemeasurable)
    (ae_tendsto_scaled_error hf hf' hU)

/-- **The limit law is uniform** (a degree-0 spline): for `c ≠ 0`, the law of `c (U − 1/2)`,
`U ~ U[0,1)`, is the uniform law on `[−|c|/2, |c|/2]`, with density `1/|c|`. -/
theorem map_mul_sub_half_uniformIco {c : ℝ} (hc : c ≠ 0) :
    uniformIco.map (fun u ↦ c * (u - 1 / 2)) =
      ENNReal.ofReal |c|⁻¹ • volume.restrict (Icc (-(|c| / 2)) (|c| / 2)) := by
  have hcpos : 0 < |c| := abs_pos.2 hc
  have hcomp : (fun u : ℝ ↦ c * (u - 1 / 2)) = (fun x ↦ c * x) ∘ (fun u ↦ u - 1 / 2) := rfl
  have hpre : (fun x : ℝ ↦ c * x) ⁻¹' Icc (-(|c| / 2)) (|c| / 2) = Icc (-(1 / 2)) (1 / 2) := by
    ext x
    simp only [mem_preimage, mem_Icc]
    rw [← abs_le, ← abs_le, abs_mul]
    constructor
    · intro h
      have h' : |c| * |x| ≤ |c| * (1 / 2) := by linarith
      exact le_of_mul_le_mul_left h' hcpos
    · intro h
      nlinarith
  rw [hcomp, ← Measure.map_map (measurable_const_mul c) (measurable_sub_const _),
    map_sub_half_uniformIco, Measure.restrict_congr_set Ico_ae_eq_Icc, ← hpre,
    ← Measure.restrict_map (measurable_const_mul c) measurableSet_Icc,
    Real.map_volume_mul_left hc, Measure.restrict_smul, abs_inv]

/-- **A law with bounded support is not a non-degenerate Gaussian**: if `ν((M, ∞)) = 0`, then
`ν ≠ gaussianReal m v` for every `m` and every `v ≠ 0`. -/
theorem ne_gaussianReal_of_measure_Ioi_eq_zero {ν : Measure ℝ} {M : ℝ} (hM : ν (Ioi M) = 0)
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : ν ≠ gaussianReal m v := by
  rintro rfl
  have h0 : volume (Ioi M) = 0 := gaussianReal_absolutelyContinuous' m hv hM
  rw [Real.volume_Ioi] at h0
  exact ENNReal.top_ne_zero h0

/-- **The limit law of the scaled error is not normal**: for every `c` (in particular
`c = f(1) − f(0)`), the law of `c (U − 1/2)` is not `gaussianReal m v` with `v ≠ 0`. -/
theorem limit_law_ne_gaussianReal (c : ℝ) {P : Measure Ω} {U : Ω → ℝ}
    (hU : HasLaw U uniformIco P) (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    P.map (fun ω ↦ c * (U ω - 1 / 2)) ≠ gaussianReal m v := by
  refine ne_gaussianReal_of_measure_Ioi_eq_zero (M := |c|) ?_ m hv
  have hmeas : AEMeasurable (fun ω ↦ c * (U ω - 1 / 2)) P :=
    ((measurable_id'.sub_const _).const_mul _).comp_aemeasurable hU.aemeasurable
  rw [Measure.map_apply_of_aemeasurable hmeas measurableSet_Ioi, measure_eq_zero_iff_ae_notMem]
  filter_upwards [ae_mem_Ico_of_hasLaw hU] with ω hω
  intro h
  rw [mem_preimage, mem_Ioi] at h
  have hb : |U ω - 1 / 2| ≤ 1 := abs_le.2 ⟨by linarith [hω.1], by linarith [hω.2]⟩
  have h1 : c * (U ω - 1 / 2) ≤ |c| * 1 :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hb (abs_nonneg c))
  linarith

/-- **The randomly shifted lattice is not asymptotically normal** (post #2): for measurable `f`,
`C¹` on `[0,1]`, the scaled error `n (μ̂ₙ(U) − ∫₀¹ f)` does not converge in distribution to any
`N(m, v)` with `v ≠ 0`. -/
theorem not_tendstoInDistribution_scaled_error_gaussian {f f' : ℝ → ℝ} (hfm : Measurable f)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) {P : Measure Ω} [IsProbabilityMeasure P] {U : Ω → ℝ}
    (hU : HasLaw U uniformIco P) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Y : Ω' → ℝ} (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (hY : HasLaw Y (gaussianReal m v) P') :
    ¬ TendstoInDistribution (fun (n : ℕ) ω ↦ (n : ℝ) *
        (sampleMean n f (fun i ↦ stratumMap n i (U ω)) - ∫ x in (0 : ℝ)..1, f x))
      atTop Y (fun _ ↦ P) P' := by
  intro h
  have heq := tendstoInDistribution_unique _ (tendstoInDistribution_scaled_error hfm hf hf' hU) h
  rw [hY.map_eq] at heq
  exact limit_law_ne_gaussianReal _ hU m hv heq

/-- **At the MC scale `√n` the error vanishes**: for `f` `C¹` on `[0,1]` and `u ∈ [0,1]`,
`√n (μ̂ₙ(u) − ∫₀¹ f) → 0`. -/
theorem tendsto_sqrt_scaled_error {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n : ℕ ↦ Real.sqrt n *
        (sampleMean n f (fun i ↦ stratumMap n i u) - ∫ x in (0 : ℝ)..1, f x)) atTop (𝓝 0) := by
  have h2 : Tendsto (fun n : ℕ ↦ (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have h := (tendsto_scaled_error hf hf' hu).mul h2
  rw [mul_zero] at h
  refine h.congr (fun n ↦ ?_)
  rw [mul_right_comm, ← div_eq_mul_inv, Real.div_sqrt]

/-- **Almost surely, `√n (μ̂ₙ(U) − ∫₀¹ f) → 0`.** -/
theorem ae_tendsto_sqrt_scaled_error {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) {P : Measure Ω} {U : Ω → ℝ} (hU : HasLaw U uniformIco P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ Real.sqrt n *
        (sampleMean n f (fun i ↦ stratumMap n i (U ω)) - ∫ x in (0 : ℝ)..1, f x))
      atTop (𝓝 0) := by
  filter_upwards [ae_mem_Ico_of_hasLaw hU] with ω hω
  exact tendsto_sqrt_scaled_error hf hf' (Ico_subset_Icc_self hω)

/-- **Not asymptotically normal at the `√n` scale either**: `√n (μ̂ₙ(U) − ∫₀¹ f)` does not
converge in distribution to any `N(m, v)` with `v ≠ 0` (it converges to the point mass at `0`).
Contrast MC, `tendstoInDistribution_sampleMean_iid`. -/
theorem not_tendstoInDistribution_sqrt_scaled_error_gaussian {f f' : ℝ → ℝ} (hfm : Measurable f)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) {P : Measure Ω} [IsProbabilityMeasure P] {U : Ω → ℝ}
    (hU : HasLaw U uniformIco P) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Y : Ω' → ℝ} (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (hY : HasLaw Y (gaussianReal m v) P') :
    ¬ TendstoInDistribution (fun (n : ℕ) ω ↦ Real.sqrt n *
        (sampleMean n f (fun i ↦ stratumMap n i (U ω)) - ∫ x in (0 : ℝ)..1, f x))
      atTop Y (fun _ ↦ P) P' := by
  intro h
  have h0 : TendstoInDistribution (fun (n : ℕ) ω ↦ Real.sqrt n *
        (sampleMean n f (fun i ↦ stratumMap n i (U ω)) - ∫ x in (0 : ℝ)..1, f x))
      atTop (fun _ ↦ (0 : ℝ)) (fun _ ↦ P) P :=
    tendstoInDistribution_of_ae_tendsto
      (fun n ↦ (((measurable_sampleMean_stratumMap hfm n).sub_const _).const_mul
        _).comp_aemeasurable hU.aemeasurable)
      aemeasurable_const (ae_tendsto_sqrt_scaled_error hf hf' hU)
  have heq := tendstoInDistribution_unique _ h0 h
  rw [hY.map_eq] at heq
  refine ne_gaussianReal_of_measure_Ioi_eq_zero (M := 0) ?_ m hv heq
  rw [Measure.map_apply measurable_const measurableSet_Ioi,
    preimage_const_of_notMem (s := Ioi (0 : ℝ)) (fun h ↦ lt_irrefl (0 : ℝ) h), measure_empty]

end RQMCMarkov.PointSets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The randomly shifted lattice `{fract (i/n + U)}` and the common-shift rule (post #2)

The rank-1 lattice rule with generator `1` in one dimension is `{i/n : i < n}`; its random shift
modulo 1 is `{fract (i/n + U)}`, `U ~ U[0,1)`, whose points are each marginally `U[0,1)`
(requirement (i), `measurePreserving_fract_add`). This module identifies it with the
common-shift stratified rule `(i + V)/n` of `Stratified` and `ShiftLimit`, with `V = fract (n U)`,
and transfers the limit theorems.

## Main results

* `sampleMean_fract_lattice`: for every `u`,
  `(1/n) Σᵢ f(fract (i/n + u)) = (1/n) Σᵢ f((i + fract (n u))/n)` (the two point sets coincide).
* `measurePreserving_fract_natCast_mul`, `hasLaw_fract_natCast_mul`: `u ↦ fract (n u)` preserves
  `U[0,1)` (via Haar measure on the circle `ℝ/ℤ`, `measurePreserving_zsmul`).
* `hasLaw_scaled_error_id_lattice`: for `f(x) = x`, the scaled lattice error
  `n (μ̂ₙ − 1/2) = fract (n U) − 1/2` is `U[−1/2, 1/2)` for every `n ≥ 1`.
* `tendstoInDistribution_scaled_error_lattice`: for measurable `f`, `C¹` on `[0,1]`, the scaled
  lattice error converges in distribution to `(f(1) − f(0)) (U − 1/2)`;
  `not_tendstoInDistribution_scaled_error_lattice_gaussian`: and not to any non-degenerate normal.
* `fract_natCast_mul_stratumMap`, `variance_commonShift_sawtooth`,
  `mc_variance_lt_commonShift_sawtooth`: for the sawtooth `f(x) = fract (n x)` the shifted lattice
  (common shift) has variance `1/12`, `n` times the MC variance `1/(12 n)`.

**Correction.** Posts #1–#2 say RQMC gives a "low-variance estimator" and that "RQMC is much
lower variance than the MC". For independent stratification this holds for every `f ∈ L²`
(`variance_stratified_le_mc`), but not for the randomly shifted lattice: for each `n ≥ 2` the
sawtooth `f(x) = fract (n x)` makes its variance `n` times the MC variance
(`mc_variance_lt_commonShift_sawtooth`). The gain of a shifted lattice depends on the smoothness
of `f` (`variance_commonShift_le_lipschitz`: `O(n^{-2})` for Lipschitz `f`, uniformly in `n` only
through the Lipschitz constant, which is `n` for the sawtooth).

**Remark (not formalised).** For the lattice labelling the convergence is only in distribution:
`n (μ̂ₙ − 1/2) = fract (n U) − 1/2` does not converge almost surely, since `fract (n U)` is
equidistributed for irrational `U` (Weyl). The labelling `(i + U)/n` of `ShiftLimit` gives the
same law for every `n` and converges almost surely.
-/

namespace RQMCMarkov.PointSets

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The randomly shifted lattice is the common-shift rule**: for every `u`,
`(1/n) Σᵢ f(fract (i/n + u)) = (1/n) Σᵢ f((i + fract (n u))/n)`. -/
theorem sampleMean_fract_lattice {n : ℕ} (hn : n ≠ 0) (f : ℝ → ℝ) (u : ℝ) :
    sampleMean n f (fun i ↦ Int.fract ((i : ℝ) / n + u)) =
      sampleMean n f (fun i ↦ stratumMap n i (Int.fract ((n : ℝ) * u))) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hnZ : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  set m : ℤ := ⌊(n : ℝ) * u⌋ with hm
  set v : ℝ := Int.fract ((n : ℝ) * u) with hvdef
  have hv : (n : ℝ) * u = m + v := (Int.floor_add_fract _).symm
  have hv0 : 0 ≤ v := Int.fract_nonneg _
  have hv1 : v < 1 := Int.fract_lt_one _
  set r : Fin n → ℤ := fun i ↦ ((i : ℤ) + m) % (n : ℤ) with hr
  have hr0 : ∀ i, 0 ≤ r i := fun i ↦ Int.emod_nonneg _ hnZ.ne'
  have hrn : ∀ i, r i < n := fun i ↦ Int.emod_lt_of_pos _ hnZ
  set σ : Fin n → Fin n := fun i ↦ ⟨(r i).toNat, by have := hr0 i; have := hrn i; omega⟩ with hσ
  have hσval : ∀ i, ((σ i : ℕ) : ℝ) = (r i : ℝ) := by
    intro i
    have h1 : (((r i).toNat : ℕ) : ℤ) = r i := Int.toNat_of_nonneg (hr0 i)
    have h2 : (((r i).toNat : ℕ) : ℝ) = ((((r i).toNat : ℕ) : ℤ) : ℝ) := (Int.cast_natCast _).symm
    change (((r i).toNat : ℕ) : ℝ) = _
    rw [h2, h1]
  have hfract : ∀ i : Fin n, Int.fract ((i : ℝ) / n + u) = stratumMap n (σ i) v := by
    intro i
    have hdec : (r i : ℝ) + n * (((i : ℤ) + m) / n : ℤ) = (i : ℝ) + m := by
      have := Int.emod_add_mul_ediv ((i : ℤ) + m) n
      have h' : ((((i : ℤ) + m) % n + n * (((i : ℤ) + m) / n) : ℤ) : ℝ) = (((i : ℤ) + m : ℤ) : ℝ) :=
        by rw [this]
      push_cast at h'
      rw [hr]
      exact h'
    have hri0 : (0 : ℝ) ≤ r i := by exact_mod_cast hr0 i
    have hrin : (r i : ℝ) + 1 ≤ n := by
      have : r i + 1 ≤ n := hrn i
      exact_mod_cast this
    rw [Int.fract_eq_iff]
    refine ⟨?_, ?_, ((i : ℤ) + m) / n, ?_⟩
    · simp only [stratumMap]
      rw [hσval]
      positivity
    · simp only [stratumMap]
      rw [hσval, div_lt_one hn']
      linarith
    · simp only [stratumMap]
      rw [hσval]
      field_simp
      linarith
  have hinj : Function.Injective σ := by
    intro i j hij
    have h1 : (r i).toNat = (r j).toNat := congrArg Fin.val hij
    have h2 : r i = r j := by
      rw [← Int.toNat_of_nonneg (hr0 i), ← Int.toNat_of_nonneg (hr0 j), h1]
    have h3 : ((i : ℤ) + m) ≡ ((j : ℤ) + m) [ZMOD n] := h2
    have h4 : (i : ℤ) ≡ (j : ℤ) [ZMOD n] := Int.ModEq.add_right_cancel' m h3
    have hi : ((i : ℕ) : ℤ) % n = (i : ℤ) :=
      Int.emod_eq_of_lt (Nat.cast_nonneg _) (by exact_mod_cast i.isLt)
    have hj : ((j : ℕ) : ℤ) % n = (j : ℤ) :=
      Int.emod_eq_of_lt (Nat.cast_nonneg _) (by exact_mod_cast j.isLt)
    have h5 : ((i : ℕ) : ℤ) = ((j : ℕ) : ℤ) := by
      have : ((i : ℕ) : ℤ) % n = ((j : ℕ) : ℤ) % n := h4
      rw [hi, hj] at this
      exact this
    exact Fin.ext (by exact_mod_cast h5)
  have hbij : Function.Bijective σ := Finite.injective_iff_bijective.1 hinj
  unfold sampleMean
  congr 1
  rw [Finset.sum_congr rfl (fun i _ ↦ congrArg f (hfract i))]
  exact hbij.sum_comp (fun j : Fin n ↦ f (stratumMap n j v))

/-- **`u ↦ fract (n u)` preserves the uniform law** on `[0,1)`, for every `n ≥ 1`. -/
theorem measurePreserving_fract_natCast_mul {n : ℕ} (hn : n ≠ 0) :
    MeasurePreserving (fun u ↦ Int.fract ((n : ℝ) * u)) uniformIco uniformIco := by
  have hm : Measurable fun u : ℝ ↦ Int.fract ((n : ℝ) * u) :=
    measurable_fract.comp (measurable_const_mul _)
  refine ⟨hm, ?_⟩
  set h : UnitAddCircle → ℝ := fun x ↦ ((AddCircle.equivIco (1 : ℝ) 0 x : Ico (0 : ℝ) (0 + 1)) : ℝ)
    with hh
  have hhm : Measurable h :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable
  have hfr : (Int.fract : ℝ → ℝ) = h ∘ ((↑) : ℝ → UnitAddCircle) := by
    funext x
    simp only [hh, Function.comp_apply]
    rw [AddCircle.coe_equivIco_mk_apply, div_one, mul_one]
  have hz : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  have hcomp : (fun u : ℝ ↦ Int.fract ((n : ℝ) * u)) =
      h ∘ (fun x : UnitAddCircle ↦ (n : ℤ) • x) ∘ ((↑) : ℝ → UnitAddCircle) := by
    funext u
    rw [hfr]
    simp only [Function.comp_apply]
    rw [← AddCircle.coe_zsmul, zsmul_eq_mul, Int.cast_natCast]
  have hid : uniformIco.map Int.fract = uniformIco := by
    have hae : Int.fract =ᵐ[uniformIco] id :=
      ae_restrict_of_forall_mem measurableSet_Ico (fun x hx ↦ Int.fract_eq_self.2 hx)
    rw [Measure.map_congr hae, Measure.map_id]
  have hcirc : (volume.restrict (Ioc (0 : ℝ) 1)).map ((↑) : ℝ → UnitAddCircle) = volume := by
    have := (UnitAddCircle.measurePreserving_mk 0).map_eq
    rwa [zero_add] at this
  have hzm := (Measure.measurePreserving_zsmul (volume : Measure UnitAddCircle) hz).measurable
  rw [hcomp, ← Measure.map_map hhm (hzm.comp AddCircle.measurable_mk'),
    ← Measure.map_map hzm AddCircle.measurable_mk',
    uniformIco_eq_restrict_Ioc, hcirc,
    (Measure.measurePreserving_zsmul (volume : Measure UnitAddCircle) hz).map_eq, ← hcirc,
    Measure.map_map hhm AddCircle.measurable_mk', ← hfr, ← uniformIco_eq_restrict_Ioc,
    hid]

/-- If `U ~ U[0,1)` then `fract (n U) ~ U[0,1)`. -/
theorem hasLaw_fract_natCast_mul {n : ℕ} (hn : n ≠ 0) {P : Measure Ω} {U : Ω → ℝ}
    (hU : HasLaw U uniformIco P) : HasLaw (fun ω ↦ Int.fract ((n : ℝ) * U ω)) uniformIco P :=
  (measurePreserving_fract_natCast_mul hn).fun_comp_hasLaw hU

/-- **The scaled lattice error for `f(x) = x` is `U[−1/2, 1/2)` for every `n ≥ 1`**: with
`U ~ U[0,1)`, `n ((1/n) Σᵢ fract (i/n + U) − 1/2) = fract (n U) − 1/2`. -/
theorem hasLaw_scaled_error_id_lattice {n : ℕ} (hn : n ≠ 0) {P : Measure Ω} {U : Ω → ℝ}
    (hU : HasLaw U uniformIco P) :
    HasLaw (fun ω ↦ (n : ℝ) * (sampleMean n id (fun i ↦ Int.fract ((i : ℝ) / n + U ω)) - 1 / 2))
      (volume.restrict (Ico (-(1 / 2) : ℝ) (1 / 2))) P := by
  have hfun : (fun ω ↦ (n : ℝ) * (sampleMean n id (fun i ↦ Int.fract ((i : ℝ) / n + U ω)) -
      1 / 2)) = fun ω ↦ (n : ℝ) * (sampleMean n id (fun i ↦ stratumMap n i
        (Int.fract ((n : ℝ) * U ω))) - 1 / 2) := by
    funext ω
    rw [sampleMean_fract_lattice hn]
  rw [hfun]
  exact hasLaw_scaled_error_id hn (hasLaw_fract_natCast_mul hn hU)

/-- **Convergence in distribution of the scaled lattice error**: for measurable `f`, `C¹` on
`[0,1]`, and `U ~ U[0,1)`, `n ((1/n) Σᵢ f(fract (i/n + U)) − ∫₀¹ f) ⇒ (f(1) − f(0)) (U − 1/2)`. -/
theorem tendstoInDistribution_scaled_error_lattice {f f' : ℝ → ℝ} (hfm : Measurable f)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) {P : Measure Ω} [IsProbabilityMeasure P] {U : Ω → ℝ}
    (hU : HasLaw U uniformIco P) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (n : ℝ) *
        (sampleMean n f (fun i ↦ Int.fract ((i : ℝ) / n + U ω)) - ∫ x in (0 : ℝ)..1, f x))
      atTop (fun ω ↦ (f 1 - f 0) * (U ω - 1 / 2)) (fun _ ↦ P) P := by
  have hS := tendstoInDistribution_scaled_error hfm hf hf' hU
  set G : ℕ → ℝ → ℝ := fun n u ↦ (n : ℝ) *
    (sampleMean n f (fun i ↦ stratumMap n i u) - ∫ x in (0 : ℝ)..1, f x) with hG
  have hGm : ∀ n, Measurable (G n) := fun n ↦
    ((measurable_sampleMean_stratumMap hfm n).sub_const _).const_mul _
  have hlaw : ∀ n : ℕ, n ≠ 0 →
      P.map (fun ω ↦ (n : ℝ) * (sampleMean n f (fun i ↦ Int.fract ((i : ℝ) / n + U ω)) -
        ∫ x in (0 : ℝ)..1, f x)) = P.map (fun ω ↦ G n (U ω)) := by
    intro n hn
    have hfun : (fun ω ↦ (n : ℝ) * (sampleMean n f (fun i ↦ Int.fract ((i : ℝ) / n + U ω)) -
        ∫ x in (0 : ℝ)..1, f x)) = G n ∘ (fun ω ↦ Int.fract ((n : ℝ) * U ω)) := by
      funext ω
      simp only [hG, Function.comp_apply]
      rw [sampleMean_fract_lattice hn]
    have hV := hasLaw_fract_natCast_mul hn hU
    rw [hfun, ← AEMeasurable.map_map_of_aemeasurable (hGm n).aemeasurable hV.aemeasurable,
      hV.map_eq, ← hU.map_eq, AEMeasurable.map_map_of_aemeasurable (hGm n).aemeasurable
        hU.aemeasurable]
    rfl
  have hmeasL : ∀ n : ℕ, AEMeasurable (fun ω ↦ (n : ℝ) *
      (sampleMean n f (fun i ↦ Int.fract ((i : ℝ) / n + U ω)) - ∫ x in (0 : ℝ)..1, f x)) P := by
    intro n
    have hm : Measurable fun u : ℝ ↦ (n : ℝ) *
        (sampleMean n f (fun i ↦ Int.fract ((i : ℝ) / n + u)) - ∫ x in (0 : ℝ)..1, f x) := by
      change Measurable fun u : ℝ ↦ (n : ℝ) * ((n : ℝ)⁻¹ * ∑ i : Fin n,
        f (Int.fract ((i : ℝ) / n + u)) - ∫ x in (0 : ℝ)..1, f x)
      refine Measurable.const_mul (Measurable.sub_const (Measurable.const_mul ?_ _) _) _
      exact Finset.measurable_fun_sum _ (fun i _ ↦
        (hfm.comp (measurable_fract.comp (measurable_const_add _)) :))
    exact hm.comp_aemeasurable hU.aemeasurable
  refine ⟨hmeasL, hS.aemeasurable_limit, ?_⟩
  refine (hS.tendsto).congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact Subtype.ext (hlaw n hn).symm

/-- **The randomly shifted lattice is not asymptotically normal**: the scaled lattice error
does not converge in distribution to any `N(m, v)` with `v ≠ 0`. -/
theorem not_tendstoInDistribution_scaled_error_lattice_gaussian {f f' : ℝ → ℝ}
    (hfm : Measurable f) (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) {P : Measure Ω} [IsProbabilityMeasure P] {U : Ω → ℝ}
    (hU : HasLaw U uniformIco P) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Y : Ω' → ℝ} (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (hY : HasLaw Y (gaussianReal m v) P') :
    ¬ TendstoInDistribution (fun (n : ℕ) ω ↦ (n : ℝ) *
        (sampleMean n f (fun i ↦ Int.fract ((i : ℝ) / n + U ω)) - ∫ x in (0 : ℝ)..1, f x))
      atTop Y (fun _ ↦ P) P' := by
  intro h
  have heq := tendstoInDistribution_unique _
    (tendstoInDistribution_scaled_error_lattice hfm hf hf' hU) h
  rw [hY.map_eq] at heq
  exact limit_law_ne_gaussianReal _ hU m hv heq

/-- The sawtooth `x ↦ fract (n x)` evaluated at the common-shift points `(i + u)/n`, `u ∈ [0,1)`,
is `u` at every point. -/
theorem fract_natCast_mul_stratumMap {n : ℕ} (hn : n ≠ 0) (i : ℕ) {u : ℝ}
    (hu : u ∈ Ico (0 : ℝ) 1) : Int.fract ((n : ℝ) * stratumMap n i u) = u := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h1 : (n : ℝ) * stratumMap n i u = (i : ℝ) + u := by
    simp only [stratumMap]
    field_simp
  rw [h1, Int.fract_natCast_add, Int.fract_eq_self.2 hu]

/-- **Correction: a randomly shifted lattice can be worse than MC.** For every `n ≥ 1` and the
sawtooth `f(x) = fract (n x)` (period `1/n`), the common-shift estimate `(1/n) Σᵢ f((i + U)/n)`
equals `U` almost surely, so its variance is `1/12 = Var_{U[0,1)}(f)`: `n` times the MC variance
`Var_{U[0,1)}(f)/n` (`variance_sampleMean_iid`). -/
theorem variance_commonShift_sawtooth {n : ℕ} (hn : n ≠ 0) {P : Measure Ω} {U : Ω → ℝ}
    (hU : HasLaw U uniformIco P) :
    Var[fun ω ↦ sampleMean n (fun x ↦ Int.fract ((n : ℝ) * x))
        (fun i ↦ stratumMap n i (U ω)); P] = 1 / 12 ∧
      Var[fun x ↦ Int.fract ((n : ℝ) * x); uniformIco] = 1 / 12 := by
  constructor
  · have hae : (fun ω ↦ sampleMean n (fun x ↦ Int.fract ((n : ℝ) * x))
        (fun i ↦ stratumMap n i (U ω))) =ᵐ[P] U := by
      filter_upwards [ae_mem_Ico_of_hasLaw hU] with ω hω
      change (n : ℝ)⁻¹ * ∑ i : Fin n, Int.fract ((n : ℝ) * stratumMap n i (U ω)) = U ω
      rw [Finset.sum_congr rfl (fun (i : Fin n) _ ↦ fract_natCast_mul_stratumMap hn i hω),
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn), one_mul]
    rw [variance_congr hae, ← variance_id_map hU.aemeasurable, hU.map_eq]
    exact variance_uniformIco_id
  · rw [(measurePreserving_fract_natCast_mul hn).variance_fun_comp
      (f := fun u : ℝ ↦ u) measurable_id'.aemeasurable]
    exact variance_uniformIco_id

/-- **The randomly shifted lattice loses to MC on the sawtooth**: for `n ≥ 2` and
`f(x) = fract (n x)`, the MC variance `Var(f)/n = 1/(12 n)` is strictly smaller than the
common-shift variance `1/12`. (Independent stratification never loses:
`variance_stratified_le_mc`.) -/
theorem mc_variance_lt_commonShift_sawtooth {n : ℕ} (hn : 2 ≤ n) {P : Measure Ω} {U : Ω → ℝ}
    (hU : HasLaw U uniformIco P) :
    Var[fun x ↦ Int.fract ((n : ℝ) * x); uniformIco] / n <
      Var[fun ω ↦ sampleMean n (fun x ↦ Int.fract ((n : ℝ) * x))
        (fun i ↦ stratumMap n i (U ω)); P] := by
  have hn0 : n ≠ 0 := by omega
  obtain ⟨h1, h2⟩ := variance_commonShift_sawtooth hn0 hU
  rw [h1, h2]
  have h2' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_lt_iff₀ (by linarith)]
  linarith

end RQMCMarkov.PointSets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # The random digital shift in one dimension

Post #2: "If we use an RQMC estimator with a digital net and a digital random shift, this is also
not normally distributed (in one dimension it is equivalent to a randomly-shifted lattice)." The
base-2 random digital shift XORs the binary digits of each point with those of one
`U ~ Uniform[0,1)` (L'Ecuyer 2016; Dick-Pillichshammer 2010, Ch. 4).

**Definition and the dyadic ambiguity.** Points of a base-2 digital net with `2^m` points have at
most `m` binary digits: `y = k/2^m`. Write `a = ⌊2^m u⌋` and `w = fract (2^m u)`, so that the first
`m` digits of `u` are the bits of `a` and its remaining digits are those of `w`. XORing digitwise,
the first `m` digits of `y ⊕ u` are the bits of `k XOR a`, and the remaining digits are those of `u`
(the digits of `y` there are `0`):
`digitalShift m y u = ((⌊2^m y⌋ XOR ⌊2^m u⌋) + fract (2^m u)) / 2^m`
(`floor_two_pow_mul_digitalShift`, `testBit_floor_two_pow_mul_digitalShift`,
`fract_two_pow_mul_digitalShift`). For a general `y` it XORs the first `m` digits and replaces the
later ones by those of `u` (an `m`-digit implementation). The digits of `u` are those of its
terminating expansion (`Nat.floor`). A dyadic rational `u` also has an expansion ending in `1`s,
and `digitalShiftUpper` uses that one (`Nat.ceil - 1`). The two can differ, even by leaving
`[0,1)`: `digitalShift_expansion_ambiguity` gives `1/2 ⊕ 1/2 = 0` against `1`. But they agree
unless `2^m u ∈ ℕ` (`digitalShiftUpper_eq_digitalShift`), a Lebesgue-null set
(`volume_two_pow_mul_eq_natCast`), so `digitalShiftUpper_ae_eq`: the choice is immaterial
almost surely.

**Results.**
* (i) `measurePreserving_digitalShift`: each digitally shifted point is marginally `U[0,1)`
  (a cell permutation `measurePreserving_cellPerm` of the `2^m` dyadic cells), hence
  `integral_qmcEstimate_digitalShiftSeq`: the digitally shifted estimator is unbiased.
* (ii) For `n = 2^m` and the first `2^m` van der Corput points (the grid `{k/2^m}`,
  `image_vanDerCorput_digit`): for EVERY `u ∈ [0,1)` the digitally shifted point set and the
  randomly shifted point set `{fract (φ(i) + u)}` are the same set `{(j + fract (2^m u))/2^m}`
  (`image_digitalShift_eq_image_shiftMod_vanDerCorput`), so the estimators coincide pointwise
  (`qmcEstimate_digitalShift_eq_shiftMod_vanDerCorput`) and have the same law for every `f`
  (`map_qmcEstimate_digitalShift_eq_shiftMod`).
* (iii) `digitalShift_ne_shiftMod_counterexample`: the equivalence is a property of the full net.
  For the three points `{0, 1/8, 1/4}` (`m = 3`) and `f = 1_{[0,1/2)}`, the digitally shifted
  estimator never equals `2/3`, while the randomly shifted one equals `2/3` with probability at
  least `1/8`; the two laws differ.
* (iv) `hasLaw_scaled_error_digitalShift_id`: for `n = 2^m` and `f(x) = x`, the scaled error
  `2^m (μ̂ - 1/2)` of the digitally shifted van der Corput estimator is `U[-1/2, 1/2)` for every
  `m`, via `hasLaw_scaled_error_id` (`ShiftLimit`), so it is not normal
  (`scaled_error_digitalShift_ne_gaussianReal`).

**Correction (to the suggested counterexample).** For the first `3` van der Corput points
`{0, 1/2, 1/4}` the two randomizations are NOT different in law: `map_digitalShift_three_eq`
proves that the digitally and randomly shifted estimators have the same law for every measurable
`f`. Both point sets are the four-cell grid shifted by `fract (4u)/4` with one cell removed, and
the removed cell is uniform in both cases. This holds for every prefix length:
`DigitalShiftPrefix.map_qmcEstimate_digitalShift_prefix_eq` proves the equality in law for the
first `n` van der Corput points whenever `n ≤ 2^m`. A counterexample therefore needs a point set
that is not a van der Corput prefix, as in (iii).
-/

namespace RQMCMarkov.PointSets

open MeasureTheory ProbabilityTheory Filter

/-- The base-2 random digital shift of a point `y` with `m` binary digits by `u`:
`((⌊2^m y⌋ XOR ⌊2^m u⌋) + fract (2^m u)) / 2^m` (terminating expansion of `u`). -/
noncomputable def digitalShift (m : ℕ) (y u : ℝ) : ℝ :=
  (((⌊(2 : ℝ) ^ m * y⌋₊ ^^^ ⌊(2 : ℝ) ^ m * u⌋₊ : ℕ) : ℝ) + Int.fract ((2 : ℝ) ^ m * u)) / 2 ^ m

/-- The digital shift computed with the non-terminating expansion of `u` (the one ending in `1`s
when `u` is dyadic): digits `⌈2^m u⌉ - 1` and tail `2^m u - (⌈2^m u⌉ - 1) ∈ (0,1]`. -/
noncomputable def digitalShiftUpper (m : ℕ) (y u : ℝ) : ℝ :=
  (((⌊(2 : ℝ) ^ m * y⌋₊ ^^^ (⌈(2 : ℝ) ^ m * u⌉₊ - 1) : ℕ) : ℝ) +
    ((2 : ℝ) ^ m * u - ((⌈(2 : ℝ) ^ m * u⌉₊ - 1 : ℕ) : ℝ))) / 2 ^ m

/-- The digitally shifted point sequence `i ↦ x i ⊕ u`. -/
noncomputable def digitalShiftSeq (m : ℕ) (x : ℕ → ℝ) (u : ℝ) : ℕ → ℝ :=
  fun i => digitalShift m (x i) u

/-- The dyadic cell `[a/2^m, (a+1)/2^m)`. -/
def dyadicCell (m a : ℕ) : Set ℝ := Set.Ico ((a : ℝ) / 2 ^ m) (((a : ℝ) + 1) / 2 ^ m)

/-- The cell permutation `u ↦ (σ ⌊2^m u⌋ + fract (2^m u))/2^m`: moves the dyadic cell `a` onto the
cell `σ a` by a translation. -/
noncomputable def cellPerm (m : ℕ) (σ : ℕ → ℕ) (u : ℝ) : ℝ :=
  (((σ ⌊(2 : ℝ) ^ m * u⌋₊ : ℕ) : ℝ) + Int.fract ((2 : ℝ) ^ m * u)) / 2 ^ m

/-- `⌊x⌋₊ + fract x = x` for `x ≥ 0`. -/
theorem natFloor_add_fract {x : ℝ} (hx : 0 ≤ x) : (⌊x⌋₊ : ℝ) + Int.fract x = x := by
  rw [natCast_floor_eq_intCast_floor hx, Int.floor_add_fract]

/-- For `y ∈ [0,1)`, `⌊2^m y⌋ < 2^m`. -/
theorem floor_two_pow_mul_lt (m : ℕ) {y : ℝ} (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    ⌊(2 : ℝ) ^ m * y⌋₊ < 2 ^ m := by
  have hpos : (0 : ℝ) < 2 ^ m := pow_pos two_pos m
  rw [Nat.floor_lt (mul_nonneg hpos.le hy.1), Nat.cast_pow, Nat.cast_ofNat]
  exact mul_lt_of_lt_one_right hpos hy.2

/-- XOR with a fixed number is injective. -/
theorem xor_left_cancel' (k a b : ℕ) (h : k ^^^ a = k ^^^ b) : a = b := by
  have := congrArg (fun c => k ^^^ c) h
  rwa [← Nat.xor_assoc, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, Nat.zero_xor] at this

/-- `2^m (y ⊕ u) = (⌊2^m y⌋ XOR ⌊2^m u⌋) + fract (2^m u)`. -/
theorem two_pow_mul_digitalShift (m : ℕ) (y u : ℝ) :
    (2 : ℝ) ^ m * digitalShift m y u =
      ((⌊(2 : ℝ) ^ m * y⌋₊ ^^^ ⌊(2 : ℝ) ^ m * u⌋₊ : ℕ) : ℝ) + Int.fract ((2 : ℝ) ^ m * u) := by
  unfold digitalShift
  field_simp

/-- **The first `m` digits are XORed**: `⌊2^m (y ⊕ u)⌋ = ⌊2^m y⌋ XOR ⌊2^m u⌋`. -/
theorem floor_two_pow_mul_digitalShift (m : ℕ) (y u : ℝ) :
    ⌊(2 : ℝ) ^ m * digitalShift m y u⌋₊ = ⌊(2 : ℝ) ^ m * y⌋₊ ^^^ ⌊(2 : ℝ) ^ m * u⌋₊ := by
  rw [two_pow_mul_digitalShift, add_comm, Nat.floor_add_natCast (Int.fract_nonneg _),
    Nat.floor_eq_zero.mpr (Int.fract_lt_one _), zero_add]

/-- Digitwise: bit `j` of `⌊2^m (y ⊕ u)⌋` (binary digit `m - j` of `y ⊕ u`) is the XOR of the
corresponding bits of `y` and `u`. -/
theorem testBit_floor_two_pow_mul_digitalShift (m : ℕ) (y u : ℝ) (j : ℕ) :
    Nat.testBit ⌊(2 : ℝ) ^ m * digitalShift m y u⌋₊ j =
      (Nat.testBit ⌊(2 : ℝ) ^ m * y⌋₊ j ^^ Nat.testBit ⌊(2 : ℝ) ^ m * u⌋₊ j) := by
  rw [floor_two_pow_mul_digitalShift, Nat.testBit_xor]

/-- **The later digits are those of `u`**: `fract (2^m (y ⊕ u)) = fract (2^m u)`. -/
theorem fract_two_pow_mul_digitalShift (m : ℕ) (y u : ℝ) :
    Int.fract ((2 : ℝ) ^ m * digitalShift m y u) = Int.fract ((2 : ℝ) ^ m * u) := by
  rw [two_pow_mul_digitalShift, Int.fract_natCast_add, Int.fract_fract]

/-- The digital shift of a point of `[0,1)` by `u ∈ [0,1)` lies in `[0,1)`. -/
theorem digitalShift_mem_Ico (m : ℕ) {y u : ℝ} (hy : y ∈ Set.Ico (0 : ℝ) 1)
    (hu : u ∈ Set.Ico (0 : ℝ) 1) : digitalShift m y u ∈ Set.Ico (0 : ℝ) 1 := by
  have hpos : (0 : ℝ) < 2 ^ m := pow_pos two_pos m
  have hK : ⌊(2 : ℝ) ^ m * y⌋₊ ^^^ ⌊(2 : ℝ) ^ m * u⌋₊ < 2 ^ m :=
    Nat.xor_lt_two_pow (floor_two_pow_mul_lt m hy) (floor_two_pow_mul_lt m hu)
  have hK' : ((⌊(2 : ℝ) ^ m * y⌋₊ ^^^ ⌊(2 : ℝ) ^ m * u⌋₊ : ℕ) : ℝ) + 1 ≤ 2 ^ m := by
    exact_mod_cast hK
  have hw := Int.fract_lt_one ((2 : ℝ) ^ m * u)
  have hw0 := Int.fract_nonneg ((2 : ℝ) ^ m * u)
  unfold digitalShift
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hpos]
  linarith

/-- **The two expansions agree off the dyadic grid**: if `2^m u ∉ ℕ`, the terminating and the
non-terminating expansions of `u` give the same digital shift. -/
theorem digitalShiftUpper_eq_digitalShift (m : ℕ) (y : ℝ) {u : ℝ} (hu : 0 ≤ u)
    (hnd : ∀ k : ℕ, (2 : ℝ) ^ m * u ≠ k) : digitalShiftUpper m y u = digitalShift m y u := by
  have hx : 0 ≤ (2 : ℝ) ^ m * u := mul_nonneg (pow_nonneg zero_le_two m) hu
  have hlt : ((⌊(2 : ℝ) ^ m * u⌋₊ : ℕ) : ℝ) < (2 : ℝ) ^ m * u :=
    lt_of_le_of_ne (Nat.floor_le hx) fun h => hnd _ h.symm
  have hceil : ⌈(2 : ℝ) ^ m * u⌉₊ = ⌊(2 : ℝ) ^ m * u⌋₊ + 1 := by
    rw [Nat.ceil_eq_iff (by omega : ⌊(2 : ℝ) ^ m * u⌋₊ + 1 ≠ 0), Nat.add_sub_cancel,
      Nat.cast_add, Nat.cast_one]
    exact ⟨hlt, (Nat.lt_floor_add_one _).le⟩
  have htail : (2 : ℝ) ^ m * u - ((⌊(2 : ℝ) ^ m * u⌋₊ : ℕ) : ℝ) = Int.fract ((2 : ℝ) ^ m * u) := by
    have := natFloor_add_fract hx
    linarith
  unfold digitalShiftUpper digitalShift
  rw [hceil, Nat.add_sub_cancel, htail]

/-- The dyadic grid of level `m` is Lebesgue-null: `volume {u : 2^m u ∈ ℕ} = 0`. -/
theorem volume_two_pow_mul_eq_natCast (m : ℕ) :
    volume {u : ℝ | ∃ k : ℕ, (2 : ℝ) ^ m * u = k} = 0 := by
  refine measure_mono_null ?_ ((Set.countable_range fun k : ℕ => (k : ℝ) / 2 ^ m).measure_zero
    volume)
  rintro u ⟨k, hk⟩
  refine ⟨k, ?_⟩
  change (k : ℝ) / 2 ^ m = u
  rw [div_eq_iff (pow_pos two_pos m).ne', ← hk, mul_comm]

/-- **The expansion ambiguity is immaterial almost surely**: under `U ~ U[0,1)` the two digital
shifts agree almost surely. -/
theorem digitalShiftUpper_ae_eq (m : ℕ) (y : ℝ) :
    digitalShiftUpper m y =ᵐ[uniformIco] digitalShift m y := by
  have h0 := measure_eq_zero_iff_ae_notMem.mp (volume_two_pow_mul_eq_natCast m)
  filter_upwards [ae_restrict_mem measurableSet_Ico, ae_restrict_of_ae h0] with u hu hnd
  exact digitalShiftUpper_eq_digitalShift m y hu.1 fun k hk => hnd ⟨k, hk⟩

/-- **The ambiguity is real on the null set**: `1/2 ⊕ 1/2` is `0` with the terminating
expansion `u = 0.1000…` but `1` with `u = 0.0111…` (`m = 1`). -/
theorem digitalShift_expansion_ambiguity :
    digitalShift 1 (1 / 2) (1 / 2) = 0 ∧ digitalShiftUpper 1 (1 / 2) (1 / 2) = 1 := by
  unfold digitalShift digitalShiftUpper
  norm_num

/-- Membership in a dyadic cell is read off the floor: `v ∈ cell a ↔ ⌊2^m v⌋ = a` (`v ≥ 0`). -/
theorem mem_dyadicCell_iff (m a : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    v ∈ dyadicCell m a ↔ ⌊(2 : ℝ) ^ m * v⌋₊ = a :=
  mem_dyadic_iff_floor m a hv

/-- Points of dyadic cells are nonnegative. -/
theorem nonneg_of_mem_dyadicCell {m a : ℕ} {v : ℝ} (h : v ∈ dyadicCell m a) : 0 ≤ v :=
  le_trans (by positivity) h.1

/-- On the cell `a`, `fract (2^m v) = 2^m v - a`. -/
theorem fract_eq_of_mem_dyadicCell {m a : ℕ} {v : ℝ} (h : v ∈ dyadicCell m a) :
    Int.fract ((2 : ℝ) ^ m * v) = (2 : ℝ) ^ m * v - a := by
  have hv := nonneg_of_mem_dyadicCell h
  have hfl := (mem_dyadicCell_iff m a hv).mp h
  have := natFloor_add_fract (mul_nonneg (pow_nonneg zero_le_two m) hv)
  rw [hfl] at this
  linarith

/-- Translating by `(b - a)/2^m` moves the cell `a` onto the cell `b`. -/
theorem mem_dyadicCell_add_iff (m a b : ℕ) (v : ℝ) :
    v + ((b : ℝ) - a) / 2 ^ m ∈ dyadicCell m b ↔ v ∈ dyadicCell m a := by
  unfold dyadicCell
  rw [Set.mem_Ico, Set.mem_Ico, sub_div, add_div, add_div]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩

/-- `X ∩ [0,1)` is the disjoint union of the `2^m` sets `cell a ∩ X`. -/
theorem inter_Ico_eq_biUnion_dyadicCell (m : ℕ) (X : Set ℝ) :
    X ∩ Set.Ico 0 1 = ⋃ a ∈ Finset.range (2 ^ m), dyadicCell m a ∩ X := by
  ext u
  rw [Set.mem_iUnion₂]
  constructor
  · rintro ⟨hX, hu⟩
    exact ⟨⌊(2 : ℝ) ^ m * u⌋₊, Finset.mem_range.mpr (floor_two_pow_mul_lt m hu),
      (mem_dyadicCell_iff m _ hu.1).mpr rfl, hX⟩
  · rintro ⟨a, ha, hcell, hX⟩
    have ha' : a + 1 ≤ 2 ^ m := Finset.mem_range.mp ha
    have ha'' : (a : ℝ) + 1 ≤ 2 ^ m := by exact_mod_cast ha'
    exact ⟨hX, nonneg_of_mem_dyadicCell hcell,
      lt_of_lt_of_le hcell.2 ((div_le_one (pow_pos two_pos m)).mpr ha'')⟩

/-- The sets `cell a ∩ X`, `a < 2^m`, are pairwise disjoint. -/
theorem pairwiseDisjoint_dyadicCell_inter (m : ℕ) (X : Set ℝ) :
    (↑(Finset.range (2 ^ m)) : Set ℕ).PairwiseDisjoint fun a => dyadicCell m a ∩ X := by
  intro a _ b _ hab
  change Disjoint (dyadicCell m a ∩ X) (dyadicCell m b ∩ X)
  refine Set.disjoint_left.mpr fun u hu hu' => hab ?_
  have hv := nonneg_of_mem_dyadicCell hu.1
  rw [← (mem_dyadicCell_iff m a hv).mp hu.1, ← (mem_dyadicCell_iff m b hv).mp hu'.1]

/-- A cell permutation is measurable. -/
theorem measurable_cellPerm (m : ℕ) (σ : ℕ → ℕ) : Measurable (cellPerm m σ) := by
  refine Measurable.div_const (Measurable.add ?_ ?_) _
  · exact (measurable_from_nat (f := fun a : ℕ => ((σ a : ℕ) : ℝ))).comp
      (Nat.measurable_floor.comp (measurable_const_mul _))
  · exact measurable_fract.comp (measurable_const_mul _)

/-- On the cell `a`, the cell permutation is the translation by `(σ a - a)/2^m`. -/
theorem cellPerm_of_mem {m a : ℕ} (σ : ℕ → ℕ) {v : ℝ} (h : v ∈ dyadicCell m a) :
    cellPerm m σ v = v + ((σ a : ℝ) - a) / 2 ^ m := by
  have hfl := (mem_dyadicCell_iff m a (nonneg_of_mem_dyadicCell h)).mp h
  unfold cellPerm
  rw [hfl, fract_eq_of_mem_dyadicCell h]
  field_simp
  ring

/-- **A permutation of the dyadic cells preserves `U[0,1)`.** If `σ` maps `{0, …, 2^m - 1}`
injectively into itself, then `u ↦ (σ ⌊2^m u⌋ + fract (2^m u))/2^m` preserves the uniform law. -/
theorem measurePreserving_cellPerm (m : ℕ) {σ : ℕ → ℕ} (hmaps : ∀ a < 2 ^ m, σ a < 2 ^ m)
    (hinj : ∀ a < 2 ^ m, ∀ b < 2 ^ m, σ a = σ b → a = b) :
    MeasurePreserving (cellPerm m σ) uniformIco uniformIco := by
  have hT := measurable_cellPerm m σ
  refine ⟨hT, ?_⟩
  ext S hS
  rw [Measure.map_apply hT hS, Measure.restrict_apply (hT hS), Measure.restrict_apply hS,
    inter_Ico_eq_biUnion_dyadicCell m, inter_Ico_eq_biUnion_dyadicCell m,
    measure_biUnion_finset (pairwiseDisjoint_dyadicCell_inter m _)
      (fun a _ => measurableSet_Ico.inter (hT hS)),
    measure_biUnion_finset (pairwiseDisjoint_dyadicCell_inter m _)
      (fun a _ => measurableSet_Ico.inter hS)]
  have hstep : ∀ a ∈ Finset.range (2 ^ m), volume (dyadicCell m a ∩ cellPerm m σ ⁻¹' S) =
      volume (dyadicCell m (σ a) ∩ S) := by
    intro a _
    have hset : dyadicCell m a ∩ cellPerm m σ ⁻¹' S =
        (fun v => v + ((σ a : ℝ) - a) / 2 ^ m) ⁻¹' (dyadicCell m (σ a) ∩ S) := by
      ext v
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      rw [mem_dyadicCell_add_iff]
      constructor
      · rintro ⟨hc, hTS⟩
        exact ⟨hc, by rwa [← cellPerm_of_mem σ hc]⟩
      · rintro ⟨hc, hS'⟩
        exact ⟨hc, by rwa [cellPerm_of_mem σ hc]⟩
    rw [hset, measure_preimage_add_right]
  rw [Finset.sum_congr rfl hstep]
  have hmapsTo : Set.MapsTo σ (Finset.range (2 ^ m) : Set ℕ) (Finset.range (2 ^ m) : Set ℕ) :=
    fun a ha => Finset.mem_coe.mpr (Finset.mem_range.mpr
      (hmaps a (Finset.mem_range.mp (Finset.mem_coe.mp ha))))
  have hinjOn : Set.InjOn σ (Finset.range (2 ^ m) : Set ℕ) := fun a ha b hb hab =>
    hinj a (Finset.mem_range.mp (Finset.mem_coe.mp ha)) b
      (Finset.mem_range.mp (Finset.mem_coe.mp hb)) hab
  exact Finset.sum_nbij σ (fun a ha => hmapsTo ha) hinjOn
    (Finset.surjOn_of_injOn_of_card_le σ hmapsTo hinjOn (le_refl _)) (fun _ _ => rfl)

/-- **(i) Marginal uniformity.** For `y ∈ [0,1)`, the digitally shifted point `y ⊕ U`,
`U ~ U[0,1)`, is `U[0,1)`. -/
theorem measurePreserving_digitalShift (m : ℕ) {y : ℝ} (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    MeasurePreserving (digitalShift m y) uniformIco uniformIco :=
  measurePreserving_cellPerm m (σ := fun a => ⌊(2 : ℝ) ^ m * y⌋₊ ^^^ a)
    (fun _ ha => Nat.xor_lt_two_pow (floor_two_pow_mul_lt m hy) ha)
    (fun a _ b _ hab => xor_left_cancel' _ a b hab)

/-- **(i) Unbiasedness of the digitally shifted estimator**: for points in `[0,1)`, `n ≥ 1` and
`f` integrable on `[0,1]`, `E[(1/n) ∑ f(xᵢ ⊕ U)] = ∫₀¹ f`. -/
theorem integral_qmcEstimate_digitalShiftSeq {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 1)
    (m : ℕ) {x : ℕ → ℝ} {n : ℕ} (hx : InUnitIco x n) (hn : 0 < n) :
    ∫ u, qmcEstimate f (digitalShiftSeq m x u) n ∂uniformIco = ∫ t in (0 : ℝ)..1, f t := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hfU : Integrable f uniformIco := by
    rw [uniformIco_eq_restrict_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hf
  have hcomp : ∀ i ∈ Finset.range n,
      ∫ u, f (digitalShiftSeq m x u i) ∂uniformIco = ∫ y, f y ∂uniformIco := by
    intro i hi
    have hmp := measurePreserving_digitalShift m (hx i (Finset.mem_range.mp hi))
    change ∫ u, f (digitalShift m (x i) u) ∂uniformIco = _
    rw [← integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hfU.1),
      hmp.map_eq]
  have hint : ∀ i ∈ Finset.range n, Integrable (fun u => f (digitalShiftSeq m x u i)) uniformIco :=
    fun i hi => (measurePreserving_digitalShift m
      (hx i (Finset.mem_range.mp hi))).integrable_comp_of_integrable hfU
  unfold qmcEstimate
  rw [integral_div, integral_finsetSum _ hint, Finset.sum_congr rfl hcomp, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_div_cancel_left₀ _ hpos.ne',
    intervalIntegral.integral_of_le zero_le_one, uniformIco_eq_restrict_Ioc]

/-- Reindexing a sum over `{0, …, N-1}` by an injective self-map. -/
theorem sum_range_comp_of_injOn {β : Type*} [AddCommMonoid β] {N : ℕ} {σ : ℕ → ℕ}
    (hmaps : ∀ a < N, σ a < N) (hinj : ∀ a < N, ∀ b < N, σ a = σ b → a = b) (g : ℕ → β) :
    ∑ i ∈ Finset.range N, g (σ i) = ∑ j ∈ Finset.range N, g j := by
  have hmapsTo : Set.MapsTo σ (Finset.range N : Set ℕ) (Finset.range N : Set ℕ) := fun a ha =>
    Finset.mem_coe.mpr (Finset.mem_range.mpr (hmaps a (Finset.mem_range.mp (Finset.mem_coe.mp ha))))
  have hinjOn : Set.InjOn σ (Finset.range N : Set ℕ) := fun a ha b hb hab =>
    hinj a (Finset.mem_range.mp (Finset.mem_coe.mp ha)) b
      (Finset.mem_range.mp (Finset.mem_coe.mp hb)) hab
  exact Finset.sum_nbij σ (fun a ha => hmapsTo ha) hinjOn
    (Finset.surjOn_of_injOn_of_card_le σ hmapsTo hinjOn (le_refl _)) (fun _ _ => rfl)

/-- The image of `{0, …, N-1}` under `g ∘ σ` is its image under `g`, for an injective self-map
`σ`. -/
theorem image_range_comp_of_injOn {N : ℕ} {σ : ℕ → ℕ} (hmaps : ∀ a < N, σ a < N)
    (hinj : ∀ a < N, ∀ b < N, σ a = σ b → a = b) (g : ℕ → ℝ) :
    (Finset.range N).image (fun i => g (σ i)) = (Finset.range N).image g := by
  have himg : (Finset.range N).image σ = Finset.range N := by
    apply Finset.eq_of_subset_of_card_le
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      exact Finset.mem_range.mpr (hmaps a (Finset.mem_range.mp ha))
    · rw [Finset.card_image_of_injOn fun a ha b hb hab =>
        hinj a (Finset.mem_range.mp (Finset.mem_coe.mp ha)) b
          (Finset.mem_range.mp (Finset.mem_coe.mp hb)) hab]
  have := Finset.image_image (s := Finset.range N) (f := σ) (g := g)
  rw [himg] at this
  exact this.symm

/-- The first `2^m` van der Corput points are multiples of `2^{-m}`. -/
theorem exists_two_pow_mul_vanDerCorput_eq (m : ℕ) :
    ∀ i < 2 ^ m, ∃ k : ℕ, (2 : ℝ) ^ m * vanDerCorput i = k := by
  induction m with
  | zero =>
    intro i hi
    rw [pow_zero] at hi
    have : i = 0 := by omega
    subst this
    exact ⟨0, by rw [vanDerCorput.eq_1, mul_zero, Nat.cast_zero]⟩
  | succ m ih =>
    intro i hi
    obtain ⟨k, hk⟩ := ih (i / 2) (by rw [pow_succ] at hi; omega)
    refine ⟨i % 2 * 2 ^ m + k, ?_⟩
    rw [vanDerCorput_eq i, pow_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      ← hk]
    ring

/-- `2^m φ(i) = ⌊2^m φ(i)⌋` for `i < 2^m`. -/
theorem two_pow_mul_vanDerCorput_eq_floor {m i : ℕ} (hi : i < 2 ^ m) :
    (2 : ℝ) ^ m * vanDerCorput i = ⌊(2 : ℝ) ^ m * vanDerCorput i⌋₊ := by
  obtain ⟨k, hk⟩ := exists_two_pow_mul_vanDerCorput_eq m i hi
  rw [hk, Nat.floor_natCast]

/-- The digit index `i ↦ ⌊2^m φ(i)⌋` is injective on `{0, …, 2^m - 1}`. -/
theorem vanDerCorput_digit_inj {m i j : ℕ} (hi : i < 2 ^ m) (hj : j < 2 ^ m)
    (h : ⌊(2 : ℝ) ^ m * vanDerCorput i⌋₊ = ⌊(2 : ℝ) ^ m * vanDerCorput j⌋₊) : i = j :=
  floor_vanDerCorput_injOn m 0 (Finset.mem_coe.mpr (Finset.mem_range.mpr hi))
    (Finset.mem_coe.mpr (Finset.mem_range.mpr hj)) (by
      change ⌊(2 : ℝ) ^ m * vanDerCorput (0 + i)⌋₊ = ⌊(2 : ℝ) ^ m * vanDerCorput (0 + j)⌋₊
      rw [zero_add, zero_add]
      exact h)

/-- **The first `2^m` van der Corput points form the grid `{k/2^m : k < 2^m}`.** -/
theorem image_vanDerCorput_digit (m : ℕ) :
    (Finset.range (2 ^ m)).image vanDerCorput =
      (Finset.range (2 ^ m)).image fun k : ℕ => (k : ℝ) / 2 ^ m := by
  have hpos : (0 : ℝ) < 2 ^ m := pow_pos two_pos m
  have h := image_range_comp_of_injOn (N := 2 ^ m)
    (σ := fun i => ⌊(2 : ℝ) ^ m * vanDerCorput i⌋₊)
    (fun i _ => floor_two_pow_mul_vanDerCorput_lt m i)
    (fun a ha b hb hab => vanDerCorput_digit_inj ha hb hab) (fun k : ℕ => (k : ℝ) / 2 ^ m)
  rw [← h]
  refine Finset.image_congr fun i hi => ?_
  rw [← two_pow_mul_vanDerCorput_eq_floor (Finset.mem_range.mp (Finset.mem_coe.mp hi)),
    mul_div_cancel_left₀ _ hpos.ne']

/-- The random shift of a van der Corput point `φ(i)`, `i < 2^m`, in cell coordinates:
`fract (φ(i) + u) = (((⌊2^m φ(i)⌋ + ⌊2^m u⌋) mod 2^m) + fract (2^m u))/2^m`. -/
theorem fract_vanDerCorput_add {m i : ℕ} (hi : i < 2 ^ m) {u : ℝ} (hu : 0 ≤ u) :
    Int.fract (vanDerCorput i + u) =
      ((((⌊(2 : ℝ) ^ m * vanDerCorput i⌋₊ + ⌊(2 : ℝ) ^ m * u⌋₊) % 2 ^ m : ℕ) : ℝ) +
        Int.fract ((2 : ℝ) ^ m * u)) / 2 ^ m := by
  have hpos : (0 : ℝ) < 2 ^ m := pow_pos two_pos m
  have hφ := two_pow_mul_vanDerCorput_eq_floor hi
  have hu' := natFloor_add_fract (mul_nonneg hpos.le hu)
  set d := ⌊(2 : ℝ) ^ m * vanDerCorput i⌋₊ with hd
  set a := ⌊(2 : ℝ) ^ m * u⌋₊ with ha
  set w := Int.fract ((2 : ℝ) ^ m * u) with hw
  have hdivR : (((d + a) / 2 ^ m : ℕ) : ℝ) * 2 ^ m + (((d + a) % 2 ^ m : ℕ) : ℝ) = d + a := by
    exact_mod_cast Nat.div_add_mod' (d + a) (2 ^ m)
  have hr : ((((d + a) % 2 ^ m : ℕ)) : ℝ) + 1 ≤ 2 ^ m := by
    exact_mod_cast Nat.mod_lt (d + a) (pow_pos two_pos m)
  have hw0 : 0 ≤ w := Int.fract_nonneg _
  have hw1 : w < 1 := Int.fract_lt_one _
  have e1 : vanDerCorput i = (d : ℝ) / 2 ^ m := by
    rw [eq_div_iff hpos.ne', mul_comm]
    exact hφ
  have e2 : u = ((a : ℝ) + w) / 2 ^ m := by
    rw [eq_div_iff hpos.ne', mul_comm, hu']
  rw [Int.fract_eq_iff]
  refine ⟨by positivity, ?_, (((d + a) / 2 ^ m : ℕ) : ℤ), ?_⟩
  · rw [div_lt_one hpos]
    linarith
  · rw [Int.cast_natCast, e1, e2, ← add_div, ← sub_div, div_eq_iff hpos.ne']
    linarith

/-- The digitally shifted first `2^m` van der Corput points, summed: for `u ∈ [0,1)`,
`∑_{i<2^m} f(φ(i) ⊕ u) = ∑_{j<2^m} f((j + fract (2^m u))/2^m)`. -/
theorem sum_digitalShift_vanDerCorput (f : ℝ → ℝ) (m : ℕ) {u : ℝ}
    (hu : u ∈ Set.Ico (0 : ℝ) 1) :
    ∑ i ∈ Finset.range (2 ^ m), f (digitalShiftSeq m vanDerCorput u i) =
      ∑ j ∈ Finset.range (2 ^ m), f (((j : ℝ) + Int.fract ((2 : ℝ) ^ m * u)) / 2 ^ m) :=
  sum_range_comp_of_injOn (N := 2 ^ m)
    (σ := fun i => ⌊(2 : ℝ) ^ m * vanDerCorput i⌋₊ ^^^ ⌊(2 : ℝ) ^ m * u⌋₊)
    (fun i _ => Nat.xor_lt_two_pow (floor_two_pow_mul_vanDerCorput_lt m i)
      (floor_two_pow_mul_lt m hu))
    (fun a ha b hb hab => vanDerCorput_digit_inj ha hb (by
      rw [Nat.xor_comm _ ⌊(2 : ℝ) ^ m * u⌋₊, Nat.xor_comm _ ⌊(2 : ℝ) ^ m * u⌋₊] at hab
      exact xor_left_cancel' _ _ _ hab))
    (fun j => f (((j : ℝ) + Int.fract ((2 : ℝ) ^ m * u)) / 2 ^ m))

/-- The randomly shifted first `2^m` van der Corput points, summed: for `u ∈ [0,1)`,
`∑_{i<2^m} f(fract (φ(i) + u)) = ∑_{j<2^m} f((j + fract (2^m u))/2^m)`. -/
theorem sum_shiftMod_vanDerCorput (f : ℝ → ℝ) (m : ℕ) {u : ℝ} (hu : u ∈ Set.Ico (0 : ℝ) 1) :
    ∑ i ∈ Finset.range (2 ^ m), f (shiftMod vanDerCorput u i) =
      ∑ j ∈ Finset.range (2 ^ m), f (((j : ℝ) + Int.fract ((2 : ℝ) ^ m * u)) / 2 ^ m) := by
  change ∑ i ∈ Finset.range (2 ^ m), f (Int.fract (vanDerCorput i + u)) = _
  rw [Finset.sum_congr rfl fun i hi => congrArg f
    (fract_vanDerCorput_add (Finset.mem_range.mp hi) hu.1)]
  exact sum_range_comp_of_injOn (N := 2 ^ m)
    (σ := fun i => (⌊(2 : ℝ) ^ m * vanDerCorput i⌋₊ + ⌊(2 : ℝ) ^ m * u⌋₊) % 2 ^ m)
    (fun i _ => Nat.mod_lt _ (pow_pos two_pos m))
    (fun a ha b hb hab => by
      have h1 := Nat.ModEq.add_right_cancel' _ hab
      unfold Nat.ModEq at h1
      rw [Nat.mod_eq_of_lt (floor_two_pow_mul_vanDerCorput_lt m a),
        Nat.mod_eq_of_lt (floor_two_pow_mul_vanDerCorput_lt m b)] at h1
      exact vanDerCorput_digit_inj ha hb h1)
    (fun j => f (((j : ℝ) + Int.fract ((2 : ℝ) ^ m * u)) / 2 ^ m))

/-- **(ii) Same point set.** For `n = 2^m` and every `u ∈ [0,1)`, the digitally shifted first
`2^m` van der Corput points and the randomly shifted ones form the same set
`{(j + fract (2^m u))/2^m : j < 2^m}`. -/
theorem image_digitalShift_eq_image_shiftMod_vanDerCorput (m : ℕ) {u : ℝ}
    (hu : u ∈ Set.Ico (0 : ℝ) 1) :
    (Finset.range (2 ^ m)).image (digitalShiftSeq m vanDerCorput u) =
      (Finset.range (2 ^ m)).image (shiftMod vanDerCorput u) := by
  have hD := image_range_comp_of_injOn (N := 2 ^ m)
    (σ := fun i => ⌊(2 : ℝ) ^ m * vanDerCorput i⌋₊ ^^^ ⌊(2 : ℝ) ^ m * u⌋₊)
    (fun i _ => Nat.xor_lt_two_pow (floor_two_pow_mul_vanDerCorput_lt m i)
      (floor_two_pow_mul_lt m hu))
    (fun a ha b hb hab => vanDerCorput_digit_inj ha hb (by
      rw [Nat.xor_comm _ ⌊(2 : ℝ) ^ m * u⌋₊, Nat.xor_comm _ ⌊(2 : ℝ) ^ m * u⌋₊] at hab
      exact xor_left_cancel' _ _ _ hab))
    (fun j => ((j : ℝ) + Int.fract ((2 : ℝ) ^ m * u)) / 2 ^ m)
  have hR := image_range_comp_of_injOn (N := 2 ^ m)
    (σ := fun i => (⌊(2 : ℝ) ^ m * vanDerCorput i⌋₊ + ⌊(2 : ℝ) ^ m * u⌋₊) % 2 ^ m)
    (fun i _ => Nat.mod_lt _ (pow_pos two_pos m))
    (fun a ha b hb hab => by
      have h1 := Nat.ModEq.add_right_cancel' _ hab
      unfold Nat.ModEq at h1
      rw [Nat.mod_eq_of_lt (floor_two_pow_mul_vanDerCorput_lt m a),
        Nat.mod_eq_of_lt (floor_two_pow_mul_vanDerCorput_lt m b)] at h1
      exact vanDerCorput_digit_inj ha hb h1)
    (fun j => ((j : ℝ) + Int.fract ((2 : ℝ) ^ m * u)) / 2 ^ m)
  have hR' : (Finset.range (2 ^ m)).image (shiftMod vanDerCorput u) =
      (Finset.range (2 ^ m)).image (fun i => (fun j : ℕ => ((j : ℝ) +
        Int.fract ((2 : ℝ) ^ m * u)) / 2 ^ m)
          ((⌊(2 : ℝ) ^ m * vanDerCorput i⌋₊ + ⌊(2 : ℝ) ^ m * u⌋₊) % 2 ^ m)) :=
    Finset.image_congr fun i hi =>
      fract_vanDerCorput_add (Finset.mem_range.mp (Finset.mem_coe.mp hi)) hu.1
  rw [hR', hR]
  exact hD

/-- **(ii) Same estimator.** For `n = 2^m`, every `f` and every `u ∈ [0,1)`, the digitally
shifted and the randomly shifted van der Corput estimators are equal. -/
theorem qmcEstimate_digitalShift_eq_shiftMod_vanDerCorput (f : ℝ → ℝ) (m : ℕ) {u : ℝ}
    (hu : u ∈ Set.Ico (0 : ℝ) 1) :
    qmcEstimate f (digitalShiftSeq m vanDerCorput u) (2 ^ m) =
      qmcEstimate f (shiftMod vanDerCorput u) (2 ^ m) := by
  unfold qmcEstimate
  rw [sum_digitalShift_vanDerCorput f m hu, sum_shiftMod_vanDerCorput f m hu]

/-- **(ii) Same law.** For `n = 2^m` and every `f`, the digitally shifted and the randomly
shifted van der Corput estimators have the same law under `U ~ U[0,1)` (post #2: "in one
dimension it is equivalent to a randomly-shifted lattice"). -/
theorem map_qmcEstimate_digitalShift_eq_shiftMod (f : ℝ → ℝ) (m : ℕ) :
    uniformIco.map (fun u => qmcEstimate f (digitalShiftSeq m vanDerCorput u) (2 ^ m)) =
      uniformIco.map (fun u => qmcEstimate f (shiftMod vanDerCorput u) (2 ^ m)) := by
  refine Measure.map_congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
  exact qmcEstimate_digitalShift_eq_shiftMod_vanDerCorput f m hu

/-- **(iv) The scaled error for `f(x) = x` is uniform.** For `n = 2^m`, the digitally shifted
van der Corput estimator satisfies `2^m (μ̂ - 1/2) ~ U[-1/2, 1/2)` for every `m` (through
`hasLaw_scaled_error_id`). -/
theorem hasLaw_scaled_error_digitalShift_id (m : ℕ) :
    HasLaw (fun u => (2 : ℝ) ^ m *
      (qmcEstimate (fun t => t) (digitalShiftSeq m vanDerCorput u) (2 ^ m) - 1 / 2))
      (volume.restrict (Set.Ico (-(1 / 2) : ℝ) (1 / 2))) uniformIco := by
  have hn : (2 : ℕ) ^ m ≠ 0 := pow_ne_zero m two_ne_zero
  have h := hasLaw_scaled_error_id hn
    (hasLaw_fract_natCast_mul hn (HasLaw.id (μ := uniformIco)))
  refine h.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
  unfold qmcEstimate sampleMean
  rw [sum_digitalShift_vanDerCorput (fun t => t) m hu,
    Fin.sum_univ_eq_sum_range (fun k => id (stratumMap (2 ^ m) k
      (Int.fract (((2 ^ m : ℕ) : ℝ) * id u)))) (2 ^ m)]
  simp only [id, stratumMap, Nat.cast_pow, Nat.cast_ofNat]
  rw [div_eq_inv_mul]

/-- **(iv) Not normal.** The law of the scaled error of the digitally shifted van der Corput
estimator for `f(x) = x` is not a non-degenerate Gaussian, for any `m`. -/
theorem scaled_error_digitalShift_ne_gaussianReal (m : ℕ) (μ₀ : ℝ) {v : NNReal} (hv : v ≠ 0) :
    uniformIco.map (fun u => (2 : ℝ) ^ m *
      (qmcEstimate (fun t => t) (digitalShiftSeq m vanDerCorput u) (2 ^ m) - 1 / 2)) ≠
      gaussianReal μ₀ v := by
  rw [(hasLaw_scaled_error_digitalShift_id m).map_eq]
  refine ne_gaussianReal_of_measure_Ioi_eq_zero (M := 1 / 2) ?_ μ₀ hv
  rw [Measure.restrict_apply measurableSet_Ioi]
  convert measure_empty (μ := (volume : Measure ℝ))
  exact Set.eq_empty_of_forall_notMem fun t ht => absurd ht.2.2 (not_lt.mpr ht.1.le)

/-- A grid point `(j + w)/8` with `w ∈ [0,1)` lies below `1/2` iff `j < 4`. -/
theorem cell_lt_half_iff (j : ℕ) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) :
    ((j : ℝ) + w) / 2 ^ 3 < 1 / 2 ↔ j < 4 := by
  constructor
  · intro h
    have h' : (j : ℝ) < 4 := by
      have := (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2 ^ 3)).mp h
      norm_num at this
      linarith
    exact_mod_cast h'
  · intro h
    have h' : (j : ℝ) ≤ 3 := by exact_mod_cast Nat.le_of_lt_succ h
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2 ^ 3)]
    norm_num
    linarith

/-- **(iii) Counterexample: for a point set that is not a net the two randomizations differ.**
For the three points `{0, 1/8, 1/4}` (`m = 3`) and `f = 1_{(-∞,1/2)}`, the digitally shifted
estimator is never `2/3` on `[0,1)`, while the randomly shifted estimator is `2/3` with
probability at least `1/8`; hence the two estimator laws differ. -/
theorem digitalShift_ne_shiftMod_counterexample :
    uniformIco {u | qmcEstimate ((Set.Iio (1 / 2 : ℝ)).indicator 1)
        (digitalShiftSeq 3 (fun i : ℕ => (i : ℝ) / 8) u) 3 = 2 / 3} = 0 ∧
      0 < uniformIco {u | qmcEstimate ((Set.Iio (1 / 2 : ℝ)).indicator 1)
        (shiftMod (fun i : ℕ => (i : ℝ) / 8) u) 3 = 2 / 3} ∧
      uniformIco.map (fun u => qmcEstimate ((Set.Iio (1 / 2 : ℝ)).indicator 1)
        (digitalShiftSeq 3 (fun i : ℕ => (i : ℝ) / 8) u) 3) ≠
      uniformIco.map (fun u => qmcEstimate ((Set.Iio (1 / 2 : ℝ)).indicator 1)
        (shiftMod (fun i : ℕ => (i : ℝ) / 8) u) 3) := by
  set f : ℝ → ℝ := (Set.Iio (1 / 2 : ℝ)).indicator 1 with hfdef
  set x : ℕ → ℝ := fun i : ℕ => (i : ℝ) / 8 with hxdef
  have hQ : ∀ y : ℕ → ℝ, qmcEstimate f y 3 = (f (y 0) + f (y 1) + f (y 2)) / 3 := by
    intro y
    unfold qmcEstimate
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
  have hfval : ∀ t : ℝ, f t = if t < 1 / 2 then 1 else 0 := by
    intro t
    by_cases ht : t < 1 / 2
    · rw [hfdef, Set.indicator_of_mem (show t ∈ Set.Iio (1 / 2 : ℝ) from ht), Pi.one_apply]
      simp only [ht, ↓reduceIte]
    · rw [hfdef, Set.indicator_of_notMem (show t ∉ Set.Iio (1 / 2 : ℝ) from ht)]
      simp only [ht, ↓reduceIte]
  -- the digital side: all three points lie on the same side of `1/2`
  have hD : ∀ u ∈ Set.Ico (0 : ℝ) 1,
      qmcEstimate f (digitalShiftSeq 3 x u) 3 = 0 ∨
        qmcEstimate f (digitalShiftSeq 3 x u) 3 = 1 := by
    intro u hu
    have ha := floor_two_pow_mul_lt 3 hu
    have hw0 := Int.fract_nonneg ((2 : ℝ) ^ 3 * u)
    have hw1 := Int.fract_lt_one ((2 : ℝ) ^ 3 * u)
    have hpt : ∀ i < 3, f (digitalShiftSeq 3 x u i) =
        if ⌊(2 : ℝ) ^ 3 * u⌋₊ < 4 then 1 else 0 := by
      intro i hi
      have hfl : ⌊(2 : ℝ) ^ 3 * x i⌋₊ = i := by
        rw [hxdef, show (2 : ℝ) ^ 3 * ((i : ℝ) / 8) = i by ring, Nat.floor_natCast]
      have hbit : (i ^^^ ⌊(2 : ℝ) ^ 3 * u⌋₊ < 4) ↔ ⌊(2 : ℝ) ^ 3 * u⌋₊ < 4 := by
        have key : ∀ a < 8, ∀ i < 3, ((i ^^^ a < 4) ↔ a < 4) := by decide
        exact key _ (lt_of_lt_of_eq ha (by norm_num)) i hi
      change f (digitalShift 3 (x i) u) = _
      unfold digitalShift
      rw [hfval, hfl]
      by_cases hlt : ⌊(2 : ℝ) ^ 3 * u⌋₊ < 4
      · have hc := (cell_lt_half_iff _ hw0 hw1).mpr (hbit.mpr hlt)
        simp only [hlt, hc, ↓reduceIte]
      · have hc : ¬ (((i ^^^ ⌊(2 : ℝ) ^ 3 * u⌋₊ : ℕ) : ℝ) +
            Int.fract ((2 : ℝ) ^ 3 * u)) / 2 ^ 3 < 1 / 2 :=
          fun h => hlt (hbit.mp ((cell_lt_half_iff _ hw0 hw1).mp h))
        simp only [hlt, hc, ↓reduceIte]
    rw [hQ, hpt 0 (by norm_num), hpt 1 (by norm_num), hpt 2 (by norm_num)]
    by_cases hlt : ⌊(2 : ℝ) ^ 3 * u⌋₊ < 4
    · right
      simp only [hlt, ↓reduceIte]
      norm_num
    · left
      simp only [hlt, ↓reduceIte]
      norm_num
  -- the random-shift side on `[1/4, 3/8)`
  have hR : ∀ u ∈ Set.Ico (1 / 4 : ℝ) (3 / 8), qmcEstimate f (shiftMod x u) 3 = 2 / 3 := by
    intro u hu
    have h1 := hu.1
    have h2 := hu.2
    have e0 : shiftMod x u 0 = u := by
      change Int.fract ((((0 : ℕ) : ℝ)) / 8 + u) = u
      rw [show (((0 : ℕ) : ℝ)) / 8 + u = u by norm_num]
      exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have e1 : shiftMod x u 1 = 1 / 8 + u := by
      change Int.fract ((((1 : ℕ) : ℝ)) / 8 + u) = 1 / 8 + u
      rw [show (((1 : ℕ) : ℝ)) / 8 + u = 1 / 8 + u by norm_num]
      exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have e2 : shiftMod x u 2 = 1 / 4 + u := by
      change Int.fract ((((2 : ℕ) : ℝ)) / 8 + u) = 1 / 4 + u
      rw [show (((2 : ℕ) : ℝ)) / 8 + u = 1 / 4 + u by norm_num]
      exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have c0 : u < 1 / 2 := by linarith
    have c1 : 1 / 8 + u < 1 / 2 := by linarith
    have c2 : ¬ (1 / 4 + u < 1 / 2) := by intro h; linarith
    rw [hQ, e0, e1, e2, hfval, hfval, hfval]
    simp only [c0, c1, c2, ↓reduceIte]
    norm_num
  have hDzero : uniformIco {u | qmcEstimate f (digitalShiftSeq 3 x u) 3 = 2 / 3} = 0 := by
    rw [Measure.restrict_apply' measurableSet_Ico]
    convert measure_empty (μ := (volume : Measure ℝ))
    refine Set.eq_empty_of_forall_notMem fun u hu => ?_
    have hu1 : qmcEstimate f (digitalShiftSeq 3 x u) 3 = 2 / 3 := hu.1
    rcases hD u hu.2 with h | h
    · rw [h] at hu1
      norm_num at hu1
    · rw [h] at hu1
      norm_num at hu1
  have hRpos : 0 < uniformIco {u | qmcEstimate f (shiftMod x u) 3 = 2 / 3} := by
    have hsub : Set.Ico (1 / 4 : ℝ) (3 / 8) ⊆
        {u | qmcEstimate f (shiftMod x u) 3 = 2 / 3} ∩ Set.Ico 0 1 := fun u hu =>
      ⟨hR u hu, by linarith [hu.1], by linarith [hu.2]⟩
    rw [Measure.restrict_apply' measurableSet_Ico]
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_pos.mpr (by norm_num)
  refine ⟨hDzero, hRpos, fun hmap => ?_⟩
  have hfm : Measurable f := measurable_one.indicator measurableSet_Iio
  have hmD : Measurable fun u => qmcEstimate f (digitalShiftSeq 3 x u) 3 := by
    unfold qmcEstimate
    refine Measurable.div_const (Finset.measurable_sum _ fun i hi => ?_) _
    have hxi : x i ∈ Set.Ico (0 : ℝ) 1 := by
      have := Finset.mem_range.mp hi
      have hi' : (i : ℝ) ≤ 2 := by exact_mod_cast Nat.le_of_lt_succ this
      exact ⟨by positivity, by rw [hxdef]; change (i : ℝ) / 8 < 1; linarith⟩
    exact hfm.comp (measurePreserving_digitalShift 3 hxi).measurable
  have hmR : Measurable fun u => qmcEstimate f (shiftMod x u) 3 := by
    unfold qmcEstimate
    refine Measurable.div_const (Finset.measurable_sum _ fun i _ => ?_) _
    exact hfm.comp (measurable_fract.comp (measurable_const_add _))
  have h1 := congrArg (fun μ : Measure ℝ => μ {2 / 3}) hmap
  rw [Measure.map_apply hmD (measurableSet_singleton _),
    Measure.map_apply hmR (measurableSet_singleton _)] at h1
  have h2 : (fun u => qmcEstimate f (digitalShiftSeq 3 x u) 3) ⁻¹' {2 / 3} =
      {u | qmcEstimate f (digitalShiftSeq 3 x u) 3 = 2 / 3} := rfl
  have h3 : (fun u => qmcEstimate f (shiftMod x u) 3) ⁻¹' {2 / 3} =
      {u | qmcEstimate f (shiftMod x u) 3 = 2 / 3} := rfl
  rw [h2, h3, hDzero] at h1
  exact (ne_of_lt hRpos) h1

/-- `2^m` times a cell permutation: `σ ⌊2^m u⌋ + fract (2^m u)`. -/
theorem two_pow_mul_cellPerm (m : ℕ) (σ : ℕ → ℕ) (u : ℝ) :
    (2 : ℝ) ^ m * cellPerm m σ u =
      ((σ ⌊(2 : ℝ) ^ m * u⌋₊ : ℕ) : ℝ) + Int.fract ((2 : ℝ) ^ m * u) := by
  unfold cellPerm
  field_simp

/-- The cell permutation sends the cell `a` to the cell `σ a`: `⌊2^m T(u)⌋ = σ ⌊2^m u⌋`. -/
theorem floor_two_pow_mul_cellPerm (m : ℕ) (σ : ℕ → ℕ) (u : ℝ) :
    ⌊(2 : ℝ) ^ m * cellPerm m σ u⌋₊ = σ ⌊(2 : ℝ) ^ m * u⌋₊ := by
  rw [two_pow_mul_cellPerm, add_comm, Nat.floor_add_natCast (Int.fract_nonneg _),
    Nat.floor_eq_zero.mpr (Int.fract_lt_one _), zero_add]

/-- The cell permutation keeps the position inside the cell: `fract (2^m T(u)) = fract (2^m u)`. -/
theorem fract_two_pow_mul_cellPerm (m : ℕ) (σ : ℕ → ℕ) (u : ℝ) :
    Int.fract ((2 : ℝ) ^ m * cellPerm m σ u) = Int.fract ((2 : ℝ) ^ m * u) := by
  rw [two_pow_mul_cellPerm, Int.fract_natCast_add, Int.fract_fract]

/-- The combinatorial core of `map_digitalShift_three_eq`: the cells `{0, 2, 1} XOR a` and
`{0, 2, 1} + τ(a) mod 4`, `τ(a) = (4 - a) mod 4`, are the same multiset for every `a < 4`. -/
theorem sum_xor_eq_sum_add_three (g : ℕ → ℝ) {a : ℕ} (ha : a < 4) :
    g (0 ^^^ a) + g (2 ^^^ a) + g (1 ^^^ a) =
      g ((0 + (4 - a) % 4) % 4) + g ((2 + (4 - a) % 4) % 4) + g ((1 + (4 - a) % 4) % 4) := by
  interval_cases a <;> norm_num <;> ring

/-- **Correction: for the first three van der Corput points the two randomizations agree in
law.** For `{φ(0), φ(1), φ(2)} = {0, 1/2, 1/4}` (digital shift with `m = 2`), the digitally
shifted and the randomly shifted estimators have the same law for every measurable `f`: the
digitally shifted set at `u` is the randomly shifted set at `ψ(u)`, where `ψ` permutes the four
dyadic cells by `τ(a) = (4 - a) mod 4` and so preserves `U[0,1)`. -/
theorem map_digitalShift_three_eq {f : ℝ → ℝ} (hf : Measurable f) :
    uniformIco.map (fun u => qmcEstimate f (digitalShiftSeq 2 vanDerCorput u) 3) =
      uniformIco.map (fun u => qmcEstimate f (shiftMod vanDerCorput u) 3) := by
  have hτmaps : ∀ a < 2 ^ 2, (4 - a) % 4 < 2 ^ 2 := by decide
  have hτinj : ∀ a < 2 ^ 2, ∀ b < 2 ^ 2, (4 - a) % 4 = (4 - b) % 4 → a = b := by decide
  have hψ := measurePreserving_cellPerm 2 (σ := fun a => (4 - a) % 4) hτmaps hτinj
  have hmR : Measurable fun v => qmcEstimate f (shiftMod vanDerCorput v) 3 := by
    unfold qmcEstimate
    refine Measurable.div_const (Finset.measurable_sum _ fun i _ => ?_) _
    exact hf.comp (measurable_fract.comp (measurable_const_add _))
  have h0 : vanDerCorput 0 = 0 := vanDerCorput.eq_1
  obtain ⟨h1, h2, -⟩ := vanDerCorput_one_two_three
  have hd0 : ⌊(2 : ℝ) ^ 2 * vanDerCorput 0⌋₊ = 0 := by rw [h0, mul_zero, Nat.floor_zero]
  have hd1 : ⌊(2 : ℝ) ^ 2 * vanDerCorput 1⌋₊ = 2 := by
    rw [h1, show (2 : ℝ) ^ 2 * (1 / 2) = ((2 : ℕ) : ℝ) by norm_num, Nat.floor_natCast]
  have hd2 : ⌊(2 : ℝ) ^ 2 * vanDerCorput 2⌋₊ = 1 := by
    rw [h2, show (2 : ℝ) ^ 2 * (1 / 4) = ((1 : ℕ) : ℝ) by norm_num, Nat.floor_natCast]
  have hQ : ∀ y : ℕ → ℝ, qmcEstimate f y 3 = (f (y 0) + f (y 1) + f (y 2)) / 3 := by
    intro y
    unfold qmcEstimate
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
  have hpt : ∀ u ∈ Set.Ico (0 : ℝ) 1, qmcEstimate f (digitalShiftSeq 2 vanDerCorput u) 3 =
      qmcEstimate f (shiftMod vanDerCorput (cellPerm 2 (fun a => (4 - a) % 4) u)) 3 := by
    intro u hu
    have hv : 0 ≤ cellPerm 2 (fun a => (4 - a) % 4) u := by
      unfold cellPerm
      have := Int.fract_nonneg ((2 : ℝ) ^ 2 * u)
      positivity
    have hR : ∀ i < 2 ^ 2, shiftMod vanDerCorput (cellPerm 2 (fun a => (4 - a) % 4) u) i =
        ((((⌊(2 : ℝ) ^ 2 * vanDerCorput i⌋₊ + (4 - ⌊(2 : ℝ) ^ 2 * u⌋₊) % 4) % 2 ^ 2 : ℕ) : ℝ) +
          Int.fract ((2 : ℝ) ^ 2 * u)) / 2 ^ 2 := by
      intro i hi
      change Int.fract (vanDerCorput i + cellPerm 2 (fun a => (4 - a) % 4) u) = _
      rw [fract_vanDerCorput_add hi hv, floor_two_pow_mul_cellPerm, fract_two_pow_mul_cellPerm]
    have ha : ⌊(2 : ℝ) ^ 2 * u⌋₊ < 4 := floor_two_pow_mul_lt 2 hu
    have key := sum_xor_eq_sum_add_three
      (fun j : ℕ => f (((j : ℝ) + Int.fract ((2 : ℝ) ^ 2 * u)) / 2 ^ 2)) ha
    rw [hQ, hQ, hR 0 (by norm_num), hR 1 (by norm_num), hR 2 (by norm_num), hd0, hd1, hd2]
    change (f (digitalShift 2 (vanDerCorput 0) u) + f (digitalShift 2 (vanDerCorput 1) u) +
      f (digitalShift 2 (vanDerCorput 2) u)) / 3 = _
    unfold digitalShift
    rw [hd0, hd1, hd2]
    norm_num at key ⊢
    rw [key]
  calc uniformIco.map (fun u => qmcEstimate f (digitalShiftSeq 2 vanDerCorput u) 3)
      = uniformIco.map ((fun v => qmcEstimate f (shiftMod vanDerCorput v) 3) ∘
          cellPerm 2 (fun a => (4 - a) % 4)) := by
        refine Measure.map_congr ?_
        filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
        exact hpt u hu
    _ = _ := by rw [← Measure.map_map hmR hψ.measurable, hψ.map_eq]

end RQMCMarkov.PointSets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # Digital shift versus random shift for every van der Corput prefix

`DigitalShift` shows that for `n = 2^m` the digitally shifted and the randomly shifted first `n`
van der Corput points are the same point set, and that this fails for general dyadic point sets.
This module proves that the two randomizations agree in law for EVERY prefix length `n`: for
`n ≤ 2^m` the digitally shifted first `n` points (`m`-digit shift) and the randomly shifted first
`n` points `{fract (φ(i) + U)}` have the same law as random point sets.

**Construction.** Write `Sₙ = {⌊2^m φ(i)⌋ : i < n} ⊆ {0, …, 2^m - 1}` for the cell indices of the
first `n` points. `exists_prefix_cellPerm` builds, by induction on `m`, a bijection `τ` of
`{0, …, 2^m - 1}` with `Sₙ XOR a = Sₙ + τ(a) (mod 2^m)` for every `a`. The induction step splits on
the lowest binary digit. With `N = 2^m`, `Sₙ^{(m+1)} = 2 Sₙ^{(m)}` if `n ≤ N`, and
`Sₙ^{(m+1)} = 2 {0, …, N-1} ∪ (2 S_{n-N}^{(m)} + 1)` if `n > N` (`vdcPrefixMem_succ_of_le`,
`vdcPrefixMem_succ_of_gt`). XOR and addition act on the two halves digit by digit; the only carry
is the uniform one from the lowest digit. The new bijection is `τ'(a) = 2 τ(a/2) + (a mod 2)` when
`n ≤ N`; when `n > N` it is `2 τ(a/2)` for even `a` and `2 ((τ(a/2) - 1) mod N) + 1` for odd `a`,
which absorbs the carry. The cell permutation `ψ = cellPerm m τ` then preserves `U[0,1)`
(`measurePreserving_cellPerm`) and moves the digitally shifted set at `u` onto the randomly
shifted set at `ψ(u)`.

**Results.**
* `exists_measurePreserving_digitalShift_prefix`: for `n ≤ 2^m` there is a measure-preserving
  `ψ` with `{φ(i) ⊕ u : i < n} = {fract (φ(i) + ψ(u)) : i < n}` for every `u ∈ [0,1)`; the two
  random point sets have the same law.
* `qmcEstimate_digitalShift_prefix_eq`: the corresponding estimators agree, `Q_D(u) = Q_R(ψ(u))`.
* `map_qmcEstimate_digitalShift_prefix_eq`: hence the two estimators have the same law for every
  measurable `f` (generalising `map_digitalShift_three_eq` and
  `map_qmcEstimate_digitalShift_eq_shiftMod` of `DigitalShift`).
-/

namespace RQMCMarkov.PointSets

open MeasureTheory

/-- The cell index `⌊2^m φ(i)⌋` of the `i`-th van der Corput point at precision `m`. -/
noncomputable def vdcDigit (m i : ℕ) : ℕ := ⌊(2 : ℝ) ^ m * vanDerCorput i⌋₊

/-- `x` is the cell index of one of the first `n` van der Corput points at precision `m`. -/
def vdcPrefixMem (m n x : ℕ) : Prop := ∃ i < n, vdcDigit m i = x

/-- The digital and the random shift of the cell indices of the first `n` points by `a` and `b`
produce the same set. -/
def PrefixShiftEq (m n a b : ℕ) : Prop :=
  ∀ y, (∃ x, vdcPrefixMem m n x ∧ x ^^^ a = y) ↔ (∃ x, vdcPrefixMem m n x ∧ (x + b) % 2 ^ m = y)

/-- `φ(2^m + i) = φ(i) + 2^{-(m+1)}` for `i < 2^m`. -/
theorem vanDerCorput_two_pow_add (m : ℕ) :
    ∀ i < 2 ^ m, vanDerCorput (2 ^ m + i) = vanDerCorput i + 1 / 2 ^ (m + 1) := by
  induction m with
  | zero =>
    intro i hi
    rw [pow_zero] at hi
    have : i = 0 := by omega
    subst this
    rw [pow_zero, add_zero, vanDerCorput_one_two_three.1, vanDerCorput.eq_1]
    norm_num
  | succ m ih =>
    intro i hi
    have hP : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
    rw [vanDerCorput_eq (2 ^ (m + 1) + i), vanDerCorput_eq i,
      show (2 ^ (m + 1) + i) % 2 = i % 2 by omega,
      show (2 ^ (m + 1) + i) / 2 = 2 ^ m + i / 2 by omega, ih (i / 2) (by omega),
      pow_succ (2 : ℝ) (m + 1)]
    ring

/-- The cell index is below `2^m`. -/
theorem vdcDigit_lt (m i : ℕ) : vdcDigit m i < 2 ^ m :=
  floor_two_pow_mul_vanDerCorput_lt m i

/-- Refining the precision doubles the cell index of the first `2^m` points. -/
theorem vdcDigit_succ_of_lt {m i : ℕ} (hi : i < 2 ^ m) :
    vdcDigit (m + 1) i = 2 * vdcDigit m i := by
  have hφ := two_pow_mul_vanDerCorput_eq_floor hi
  unfold vdcDigit
  set d := ⌊(2 : ℝ) ^ m * vanDerCorput i⌋₊ with hd
  rw [pow_succ, mul_comm ((2 : ℝ) ^ m) 2, mul_assoc, hφ,
    show (2 : ℝ) * (d : ℝ) = ((2 * d : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]

/-- The points `2^m + i`, `i < 2^m`, sit in the odd cells:
`⌊2^{m+1} φ(2^m + i)⌋ = 2 ⌊2^m φ(i)⌋ + 1`. -/
theorem vdcDigit_succ_two_pow_add {m i : ℕ} (hi : i < 2 ^ m) :
    vdcDigit (m + 1) (2 ^ m + i) = 2 * vdcDigit m i + 1 := by
  have hφ := two_pow_mul_vanDerCorput_eq_floor hi
  unfold vdcDigit
  set d := ⌊(2 : ℝ) ^ m * vanDerCorput i⌋₊ with hd
  have hpos : (0 : ℝ) < 2 ^ m := pow_pos two_pos m
  have h : (2 : ℝ) ^ (m + 1) * vanDerCorput (2 ^ m + i) = ((2 * d + 1 : ℕ) : ℝ) := by
    rw [vanDerCorput_two_pow_add m i hi, mul_add, pow_succ, mul_comm ((2 : ℝ) ^ m) 2, mul_assoc,
      hφ]
    push_cast
    field_simp
  rw [h, Nat.floor_natCast]

/-- Every cell index `x < 2^m` is attained by one of the first `2^m` points. -/
theorem exists_vdcDigit_eq {m x : ℕ} (hx : x < 2 ^ m) : ∃ i < 2 ^ m, vdcDigit m i = x := by
  have hmaps : Set.MapsTo (vdcDigit m) (Finset.range (2 ^ m) : Set ℕ)
      (Finset.range (2 ^ m) : Set ℕ) := fun i _ =>
    Finset.mem_coe.mpr (Finset.mem_range.mpr (vdcDigit_lt m i))
  have hinj : Set.InjOn (vdcDigit m) (Finset.range (2 ^ m) : Set ℕ) := fun i hi j hj h =>
    vanDerCorput_digit_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) h
  obtain ⟨i, hi, hix⟩ := Finset.surjOn_of_injOn_of_card_le _ hmaps hinj (le_refl _)
    (Finset.mem_coe.mpr (Finset.mem_range.mpr hx))
  exact ⟨i, Finset.mem_range.mp hi, hix⟩

/-- Low-digit recursion, case `n ≤ 2^m`: the cells at precision `m + 1` are the doubled cells. -/
theorem vdcPrefixMem_succ_of_le {m n : ℕ} (hn : n ≤ 2 ^ m) (x : ℕ) :
    vdcPrefixMem (m + 1) n x ↔
      (x % 2 = 0 ∧ vdcPrefixMem m n (x / 2)) ∨ (x % 2 = 1 ∧ (fun _ : ℕ => False) (x / 2)) := by
  constructor
  · rintro ⟨i, hi, rfl⟩
    left
    rw [vdcDigit_succ_of_lt (by omega)]
    exact ⟨by omega, i, hi, by omega⟩
  · rintro (⟨_, i, hi, hix⟩ | ⟨_, hf⟩)
    · refine ⟨i, hi, ?_⟩
      rw [vdcDigit_succ_of_lt (by omega)]
      omega
    · exact hf.elim

/-- Low-digit recursion, case `2^m < n ≤ 2^{m+1}`: all even cells, and the doubled cells of the
first `n - 2^m` points plus one. -/
theorem vdcPrefixMem_succ_of_gt {m n : ℕ} (hn1 : 2 ^ m < n) (hn2 : n ≤ 2 ^ (m + 1)) (x : ℕ) :
    vdcPrefixMem (m + 1) n x ↔
      (x % 2 = 0 ∧ (fun z : ℕ => z < 2 ^ m) (x / 2)) ∨
        (x % 2 = 1 ∧ vdcPrefixMem m (n - 2 ^ m) (x / 2)) := by
  have hP : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
  constructor
  · rintro ⟨i, hi, rfl⟩
    rcases lt_or_ge i (2 ^ m) with h | h
    · left
      rw [vdcDigit_succ_of_lt h]
      have := vdcDigit_lt m i
      exact ⟨by omega, by change 2 * vdcDigit m i / 2 < 2 ^ m; omega⟩
    · right
      obtain ⟨j, rfl⟩ : ∃ j, i = 2 ^ m + j := ⟨i - 2 ^ m, by omega⟩
      rw [vdcDigit_succ_two_pow_add (by omega)]
      exact ⟨by omega, j, by omega, by omega⟩
  · rintro (⟨_, hx⟩ | ⟨_, j, hj, hjx⟩)
    · obtain ⟨i, hi, hix⟩ := exists_vdcDigit_eq hx
      refine ⟨i, by omega, ?_⟩
      rw [vdcDigit_succ_of_lt hi]
      omega
    · refine ⟨2 ^ m + j, by omega, ?_⟩
      rw [vdcDigit_succ_two_pow_add (by omega)]
      omega

/-- XOR, digit by digit: `x XOR a = y` iff the halves XOR to `y/2` and the lowest digits match. -/
theorem xor_eq_iff_halves (x a y : ℕ) :
    x ^^^ a = y ↔ (x / 2 ^^^ a / 2 = y / 2 ∧ (x % 2 + a % 2) % 2 = y % 2) := by
  have hd : (x ^^^ a) / 2 = x / 2 ^^^ a / 2 := Nat.xor_div_two
  have hm : (x ^^^ a) % 2 = 1 ↔ ¬ (x % 2 = 1 ↔ a % 2 = 1) := Nat.xor_mod_two_eq_one
  constructor
  · rintro rfl
    exact ⟨hd.symm, by omega⟩
  · rintro ⟨h1, h2⟩
    omega

/-- Addition modulo `2N`, digit by digit (with the carry from the lowest digit). -/
theorem add_mod_two_mul_eq_iff (x b y N : ℕ) :
    (x + b) % (2 * N) = y ↔
      ((x / 2 + b / 2 + (x % 2 + b % 2) / 2) % N = y / 2 ∧ (x % 2 + b % 2) % 2 = y % 2) := by
  rw [Nat.mod_mul, show (x + b) / 2 = x / 2 + b / 2 + (x % 2 + b % 2) / 2 by omega]
  omega

/-- XOR-shifting a set given by its even part `A` and odd part `B`. -/
theorem exists_xor_iff_of_decomp {M A B : ℕ → Prop}
    (hM : ∀ x, M x ↔ (x % 2 = 0 ∧ A (x / 2)) ∨ (x % 2 = 1 ∧ B (x / 2))) (a y : ℕ) :
    (∃ x, M x ∧ x ^^^ a = y) ↔
      (y % 2 = a % 2 ∧ ∃ x, A x ∧ x ^^^ (a / 2) = y / 2) ∨
        (y % 2 = (a % 2 + 1) % 2 ∧ ∃ x, B x ∧ x ^^^ (a / 2) = y / 2) := by
  constructor
  · rintro ⟨x, hx, hxy⟩
    rw [xor_eq_iff_halves] at hxy
    rcases (hM x).mp hx with ⟨_, hA⟩ | ⟨_, hB⟩
    · exact Or.inl ⟨by omega, x / 2, hA, hxy.1⟩
    · exact Or.inr ⟨by omega, x / 2, hB, hxy.1⟩
  · rintro (⟨hy, x, hA, hx⟩ | ⟨hy, x, hB, hx⟩)
    · refine ⟨2 * x, (hM _).mpr (Or.inl ⟨by omega, by rwa [show 2 * x / 2 = x by omega]⟩), ?_⟩
      rw [xor_eq_iff_halves, show 2 * x / 2 = x by omega]
      exact ⟨hx, by omega⟩
    · refine ⟨2 * x + 1, (hM _).mpr (Or.inr ⟨by omega, by
        rwa [show (2 * x + 1) / 2 = x by omega]⟩), ?_⟩
      rw [xor_eq_iff_halves, show (2 * x + 1) / 2 = x by omega]
      exact ⟨hx, by omega⟩

/-- Shifting modulo `2N` a set given by its even part `A` and odd part `B`. -/
theorem exists_add_iff_of_decomp {M A B : ℕ → Prop}
    (hM : ∀ x, M x ↔ (x % 2 = 0 ∧ A (x / 2)) ∨ (x % 2 = 1 ∧ B (x / 2))) (b y N : ℕ) :
    (∃ x, M x ∧ (x + b) % (2 * N) = y) ↔
      (y % 2 = b % 2 ∧ ∃ x, A x ∧ (x + b / 2) % N = y / 2) ∨
        (y % 2 = (b % 2 + 1) % 2 ∧ ∃ x, B x ∧ (x + b / 2 + b % 2) % N = y / 2) := by
  constructor
  · rintro ⟨x, hx, hxy⟩
    rw [add_mod_two_mul_eq_iff] at hxy
    rcases (hM x).mp hx with ⟨h0, hA⟩ | ⟨h1, hB⟩
    · refine Or.inl ⟨by omega, x / 2, hA, ?_⟩
      rw [show x / 2 + b / 2 = x / 2 + b / 2 + (x % 2 + b % 2) / 2 by omega]
      exact hxy.1
    · refine Or.inr ⟨by omega, x / 2, hB, ?_⟩
      rw [show x / 2 + b / 2 + b % 2 = x / 2 + b / 2 + (x % 2 + b % 2) / 2 by omega]
      exact hxy.1
  · rintro (⟨hy, x, hA, hx⟩ | ⟨hy, x, hB, hx⟩)
    · refine ⟨2 * x, (hM _).mpr (Or.inl ⟨by omega, by rwa [show 2 * x / 2 = x by omega]⟩), ?_⟩
      rw [add_mod_two_mul_eq_iff,
        show 2 * x / 2 + b / 2 + (2 * x % 2 + b % 2) / 2 = x + b / 2 by omega]
      exact ⟨hx, by omega⟩
    · refine ⟨2 * x + 1, (hM _).mpr (Or.inr ⟨by omega, by
        rwa [show (2 * x + 1) / 2 = x by omega]⟩), ?_⟩
      rw [add_mod_two_mul_eq_iff,
        show (2 * x + 1) / 2 + b / 2 + ((2 * x + 1) % 2 + b % 2) / 2 = x + b / 2 + b % 2 by omega]
      exact ⟨hx, by omega⟩

/-- XOR-shifting the full set `{0, …, 2^m - 1}` gives the full set. -/
theorem exists_lt_xor_iff {m a : ℕ} (ha : a < 2 ^ m) (y : ℕ) :
    (∃ x, (fun z : ℕ => z < 2 ^ m) x ∧ x ^^^ a = y) ↔ y < 2 ^ m := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Nat.xor_lt_two_pow hx ha
  · intro hy
    exact ⟨y ^^^ a, Nat.xor_lt_two_pow hy ha, by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]⟩

/-- Shifting the full set `{0, …, N - 1}` modulo `N` gives the full set. -/
theorem exists_lt_add_mod_iff {N β : ℕ} (hβ : β < N) (y : ℕ) :
    (∃ x, (fun z : ℕ => z < N) x ∧ (x + β) % N = y) ↔ y < N := by
  constructor
  · rintro ⟨x, _, rfl⟩
    exact Nat.mod_lt _ (by omega)
  · intro hy
    refine ⟨(y + N - β) % N, Nat.mod_lt _ (by omega), ?_⟩
    rw [Nat.mod_add_mod, show y + N - β + β = y + N by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hy]

/-- `(x + ((t + N - 1) mod N) + 1) mod N = (x + t) mod N`. -/
theorem add_pred_mod_add_one (x t N : ℕ) (hN : 0 < N) :
    (x + (t + N - 1) % N + 1) % N = (x + t) % N := by
  have h : x + (t + N - 1) % N + 1 ≡ x + (t + N - 1) + 1 [MOD N] :=
    Nat.ModEq.add_right 1 (Nat.ModEq.add_left x (Nat.mod_modEq (t + N - 1) N))
  rw [h, show x + (t + N - 1) + 1 = x + t + N by omega, Nat.add_mod_right]

/-- An existential with a false first conjunct is false. -/
theorem exists_false_and_iff (p : ℕ → Prop) : (∃ x, (fun _ : ℕ => False) x ∧ p x) ↔ False :=
  ⟨fun ⟨_, h, _⟩ => h, False.elim⟩

/-- **The cell bijection.** For `n ≤ 2^m` there is a bijection `τ` of `{0, …, 2^m - 1}` such
that XOR-shifting the cell indices of the first `n` van der Corput points by `a` gives the same set
as shifting them by `τ(a)` modulo `2^m`. -/
theorem exists_prefix_cellPerm (m : ℕ) :
    ∀ n ≤ 2 ^ m, ∃ τ : ℕ → ℕ, (∀ a < 2 ^ m, τ a < 2 ^ m) ∧
      (∀ a < 2 ^ m, ∀ b < 2 ^ m, τ a = τ b → a = b) ∧
      ∀ a < 2 ^ m, PrefixShiftEq m n a (τ a) := by
  induction m with
  | zero =>
    intro n _
    refine ⟨fun a => a, fun a ha => ha, fun a _ b _ h => h, ?_⟩
    intro a ha y
    rw [pow_zero] at ha
    have ha0 : a = 0 := by omega
    subst ha0
    rw [pow_zero]
    constructor
    · rintro ⟨x, hx, hxy⟩
      refine ⟨x, hx, ?_⟩
      obtain ⟨i, _, rfl⟩ := hx
      have := vdcDigit_lt 0 i
      rw [pow_zero] at this
      rw [Nat.xor_zero] at hxy
      omega
    · rintro ⟨x, hx, hxy⟩
      refine ⟨x, hx, ?_⟩
      obtain ⟨i, _, rfl⟩ := hx
      have := vdcDigit_lt 0 i
      rw [pow_zero] at this
      rw [Nat.xor_zero]
      omega
  | succ m ih =>
    intro n hn
    have hP : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
    have hpos : 0 < 2 ^ m := pow_pos (by norm_num) m
    rcases le_or_gt n (2 ^ m) with hle | hgt
    · obtain ⟨τ, hmaps, hinj, heq⟩ := ih n hle
      refine ⟨fun a => 2 * τ (a / 2) + a % 2, ?_, ?_, ?_⟩
      · intro a ha
        have := hmaps (a / 2) (by omega)
        change 2 * τ (a / 2) + a % 2 < 2 ^ (m + 1)
        omega
      · intro a ha b hb h
        change 2 * τ (a / 2) + a % 2 = 2 * τ (b / 2) + b % 2 at h
        have h3 : τ (a / 2) = τ (b / 2) := by omega
        have := hinj (a / 2) (by omega) (b / 2) (by omega) h3
        omega
      · intro a ha y
        have hdec := vdcPrefixMem_succ_of_le hle
        change (∃ x, vdcPrefixMem (m + 1) n x ∧ x ^^^ a = y) ↔
          (∃ x, vdcPrefixMem (m + 1) n x ∧ (x + (2 * τ (a / 2) + a % 2)) % 2 ^ (m + 1) = y)
        rw [exists_xor_iff_of_decomp (A := vdcPrefixMem m n) (B := fun _ => False) hdec, hP,
          exists_add_iff_of_decomp (A := vdcPrefixMem m n) (B := fun _ => False) hdec,
          show (2 * τ (a / 2) + a % 2) % 2 = a % 2 by omega,
          show (2 * τ (a / 2) + a % 2) / 2 = τ (a / 2) by omega,
          heq (a / 2) (by omega) (y / 2), exists_false_and_iff, exists_false_and_iff]
    · obtain ⟨τ, hmaps, hinj, heq⟩ := ih (n - 2 ^ m) (by omega)
      have hdec := vdcPrefixMem_succ_of_gt hgt hn
      refine ⟨fun a => if a % 2 = 0 then 2 * τ (a / 2)
        else 2 * ((τ (a / 2) + 2 ^ m - 1) % 2 ^ m) + 1, ?_, ?_, ?_⟩
      · intro a ha
        have h1 := hmaps (a / 2) (by omega)
        have h2 := Nat.mod_lt (τ (a / 2) + 2 ^ m - 1) hpos
        change (if a % 2 = 0 then 2 * τ (a / 2)
          else 2 * ((τ (a / 2) + 2 ^ m - 1) % 2 ^ m) + 1) < 2 ^ (m + 1)
        split_ifs <;> omega
      · intro a ha b hb h
        change (if a % 2 = 0 then 2 * τ (a / 2)
          else 2 * ((τ (a / 2) + 2 ^ m - 1) % 2 ^ m) + 1) =
          (if b % 2 = 0 then 2 * τ (b / 2)
          else 2 * ((τ (b / 2) + 2 ^ m - 1) % 2 ^ m) + 1) at h
        have ha2 := hmaps (a / 2) (by omega)
        have hb2 := hmaps (b / 2) (by omega)
        split_ifs at h with h1 h2 h2
        · have := hinj (a / 2) (by omega) (b / 2) (by omega) (by omega)
          omega
        · omega
        · omega
        · have h3 : (τ (a / 2) + 2 ^ m - 1) % 2 ^ m = (τ (b / 2) + 2 ^ m - 1) % 2 ^ m := by
            omega
          have h4 := Nat.ModEq.add_right_cancel' (2 ^ m - 1) (show
            τ (a / 2) + (2 ^ m - 1) ≡ τ (b / 2) + (2 ^ m - 1) [MOD 2 ^ m] by
              unfold Nat.ModEq
              rw [show τ (a / 2) + (2 ^ m - 1) = τ (a / 2) + 2 ^ m - 1 by omega,
                show τ (b / 2) + (2 ^ m - 1) = τ (b / 2) + 2 ^ m - 1 by omega]
              exact h3)
          unfold Nat.ModEq at h4
          rw [Nat.mod_eq_of_lt ha2, Nat.mod_eq_of_lt hb2] at h4
          have := hinj (a / 2) (by omega) (b / 2) (by omega) h4
          omega
      · intro a ha y
        have ha2 := hmaps (a / 2) (by omega)
        change (∃ x, vdcPrefixMem (m + 1) n x ∧ x ^^^ a = y) ↔
          (∃ x, vdcPrefixMem (m + 1) n x ∧ ((x + if a % 2 = 0 then 2 * τ (a / 2)
            else 2 * ((τ (a / 2) + 2 ^ m - 1) % 2 ^ m) + 1)) % 2 ^ (m + 1) = y)
        rw [exists_xor_iff_of_decomp (A := fun z => z < 2 ^ m)
            (B := vdcPrefixMem m (n - 2 ^ m)) hdec, hP,
          exists_add_iff_of_decomp (A := fun z => z < 2 ^ m) (B := vdcPrefixMem m (n - 2 ^ m)) hdec,
          exists_lt_xor_iff (show a / 2 < 2 ^ m by omega), heq (a / 2) (by omega) (y / 2)]
        rcases Nat.mod_two_eq_zero_or_one a with h0 | h1
        · have hc : (if a % 2 = 0 then 2 * τ (a / 2)
              else 2 * ((τ (a / 2) + 2 ^ m - 1) % 2 ^ m) + 1) = 2 * τ (a / 2) := by
            simp only [h0, ↓reduceIte]
          rw [hc, show 2 * τ (a / 2) % 2 = 0 by omega,
            show 2 * τ (a / 2) / 2 = τ (a / 2) by omega]
          simp only [add_zero]
          rw [exists_lt_add_mod_iff ha2, h0]
        · have hc : (if a % 2 = 0 then 2 * τ (a / 2)
              else 2 * ((τ (a / 2) + 2 ^ m - 1) % 2 ^ m) + 1) =
              2 * ((τ (a / 2) + 2 ^ m - 1) % 2 ^ m) + 1 := by
            simp only [h1, one_ne_zero, ↓reduceIte]
          rw [hc,
            show (2 * ((τ (a / 2) + 2 ^ m - 1) % 2 ^ m) + 1) % 2 = 1 by omega,
            show (2 * ((τ (a / 2) + 2 ^ m - 1) % 2 ^ m) + 1) / 2 =
              (τ (a / 2) + 2 ^ m - 1) % 2 ^ m by omega,
            exists_lt_add_mod_iff (Nat.mod_lt _ hpos), h1]
          simp only [add_pred_mod_add_one _ (τ (a / 2)) (2 ^ m) hpos]

/-- Cell-index form as Finsets: membership in the cell set of the first `n` points. -/
theorem mem_image_vdcDigit_iff (m n x : ℕ) :
    x ∈ (Finset.range n).image (vdcDigit m) ↔ vdcPrefixMem m n x := by
  simp only [Finset.mem_image, Finset.mem_range, vdcPrefixMem]

/-- **The cell sets coincide**: `Sₙ XOR a = Sₙ + τ(a) (mod 2^m)` as Finsets. -/
theorem image_xor_eq_image_add_mod {m n : ℕ} {a b : ℕ} (h : PrefixShiftEq m n a b) :
    ((Finset.range n).image (vdcDigit m)).image (fun x => x ^^^ a) =
      ((Finset.range n).image (vdcDigit m)).image (fun x => (x + b) % 2 ^ m) := by
  ext y
  rw [Finset.mem_image, Finset.mem_image]
  have := h y
  constructor
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨x', hx', hx'y⟩ := this.mp ⟨x, (mem_image_vdcDigit_iff m n x).mp hx, hxy⟩
    exact ⟨x', (mem_image_vdcDigit_iff m n x').mpr hx', hx'y⟩
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨x', hx', hx'y⟩ := this.mpr ⟨x, (mem_image_vdcDigit_iff m n x).mp hx, hxy⟩
    exact ⟨x', (mem_image_vdcDigit_iff m n x').mpr hx', hx'y⟩

/-- **Same law as random point sets.** For `n ≤ 2^m` there is a measure-preserving map `ψ` of
`U[0,1)` such that for every `u ∈ [0,1)` the digitally shifted first `n` van der Corput points
`{φ(i) ⊕ u}` and the randomly shifted ones `{fract (φ(i) + ψ(u))}` are the same set. -/
theorem exists_measurePreserving_digitalShift_prefix {m n : ℕ} (hn : n ≤ 2 ^ m) :
    ∃ ψ : ℝ → ℝ, MeasurePreserving ψ uniformIco uniformIco ∧
      ∀ u ∈ Set.Ico (0 : ℝ) 1, (Finset.range n).image (digitalShiftSeq m vanDerCorput u) =
        (Finset.range n).image (shiftMod vanDerCorput (ψ u)) := by
  obtain ⟨τ, hmaps, hinj, heq⟩ := exists_prefix_cellPerm m n hn
  refine ⟨cellPerm m τ, measurePreserving_cellPerm m hmaps hinj, fun u hu => ?_⟩
  have ha := floor_two_pow_mul_lt m hu
  have hv : 0 ≤ cellPerm m τ u := by
    unfold cellPerm
    have := Int.fract_nonneg ((2 : ℝ) ^ m * u)
    positivity
  have e1 : (Finset.range n).image (digitalShiftSeq m vanDerCorput u) =
      (((Finset.range n).image (vdcDigit m)).image (fun x => x ^^^ ⌊(2 : ℝ) ^ m * u⌋₊)).image
        (fun j : ℕ => ((j : ℝ) + Int.fract ((2 : ℝ) ^ m * u)) / 2 ^ m) := by
    rw [Finset.image_image, Finset.image_image]
    rfl
  have e2 : (Finset.range n).image (shiftMod vanDerCorput (cellPerm m τ u)) =
      (((Finset.range n).image (vdcDigit m)).image
        (fun x => (x + τ ⌊(2 : ℝ) ^ m * u⌋₊) % 2 ^ m)).image
        (fun j : ℕ => ((j : ℝ) + Int.fract ((2 : ℝ) ^ m * u)) / 2 ^ m) := by
    rw [Finset.image_image, Finset.image_image]
    refine Finset.image_congr fun i hi => ?_
    have hi' : i < 2 ^ m := lt_of_lt_of_le (Finset.mem_range.mp (Finset.mem_coe.mp hi)) hn
    change Int.fract (vanDerCorput i + cellPerm m τ u) = _
    rw [fract_vanDerCorput_add hi' hv, floor_two_pow_mul_cellPerm, fract_two_pow_mul_cellPerm]
    rfl
  rw [e1, e2, image_xor_eq_image_add_mod (heq _ ha)]

/-- **Same estimator.** With `ψ` as in `exists_measurePreserving_digitalShift_prefix`, the
digitally shifted estimator at `u` equals the randomly shifted estimator at `ψ(u)`, for every `f`.
-/
theorem qmcEstimate_digitalShift_prefix_eq {m n : ℕ} (hn : n ≤ 2 ^ m) :
    ∃ ψ : ℝ → ℝ, MeasurePreserving ψ uniformIco uniformIco ∧ ∀ f : ℝ → ℝ,
      ∀ u ∈ Set.Ico (0 : ℝ) 1, qmcEstimate f (digitalShiftSeq m vanDerCorput u) n =
        qmcEstimate f (shiftMod vanDerCorput (ψ u)) n := by
  obtain ⟨ψ, hψ, hset⟩ := exists_measurePreserving_digitalShift_prefix hn
  refine ⟨ψ, hψ, fun f u hu => ?_⟩
  have hpos : (0 : ℝ) < 2 ^ m := pow_pos two_pos m
  have hD : Set.InjOn (digitalShiftSeq m vanDerCorput u) (Finset.range n : Set ℕ) := by
    intro i hi j hj hij
    have hi' := lt_of_lt_of_le (Finset.mem_range.mp hi) hn
    have hj' := lt_of_lt_of_le (Finset.mem_range.mp hj) hn
    have h0 := (div_left_inj' hpos.ne').mp hij
    have h1 : (⌊(2 : ℝ) ^ m * vanDerCorput i⌋₊ ^^^ ⌊(2 : ℝ) ^ m * u⌋₊ : ℕ) =
        (⌊(2 : ℝ) ^ m * vanDerCorput j⌋₊ ^^^ ⌊(2 : ℝ) ^ m * u⌋₊ : ℕ) := by
      have h2 := add_right_cancel h0
      exact_mod_cast h2
    rw [Nat.xor_comm _ ⌊(2 : ℝ) ^ m * u⌋₊, Nat.xor_comm _ ⌊(2 : ℝ) ^ m * u⌋₊] at h1
    exact vanDerCorput_digit_inj hi' hj' (xor_left_cancel' _ _ _ h1)
  have hcard : ((Finset.range n).image (shiftMod vanDerCorput (ψ u))).card =
      (Finset.range n).card := by
    rw [← hset u hu, Finset.card_image_of_injOn hD]
  have hR : Set.InjOn (shiftMod vanDerCorput (ψ u)) (Finset.range n : Set ℕ) :=
    Finset.card_image_iff.mp hcard
  unfold qmcEstimate
  rw [← Finset.sum_image (f := f) hD, ← Finset.sum_image (f := f) hR, hset u hu]

/-- **Same law of the estimators.** For `n ≤ 2^m` and every measurable `f`, the digitally shifted
and the randomly shifted estimators built on the first `n` van der Corput points have the same
law under `U ~ U[0,1)`. -/
theorem map_qmcEstimate_digitalShift_prefix_eq {f : ℝ → ℝ} (hf : Measurable f) {m n : ℕ}
    (hn : n ≤ 2 ^ m) :
    uniformIco.map (fun u => qmcEstimate f (digitalShiftSeq m vanDerCorput u) n) =
      uniformIco.map (fun u => qmcEstimate f (shiftMod vanDerCorput u) n) := by
  obtain ⟨ψ, hψ, hpt⟩ := qmcEstimate_digitalShift_prefix_eq hn
  have hmR : Measurable fun v => qmcEstimate f (shiftMod vanDerCorput v) n := by
    unfold qmcEstimate
    refine Measurable.div_const (Finset.measurable_sum _ fun i _ => ?_) _
    exact hf.comp (measurable_fract.comp (measurable_const_add _))
  calc uniformIco.map (fun u => qmcEstimate f (digitalShiftSeq m vanDerCorput u) n)
      = uniformIco.map ((fun v => qmcEstimate f (shiftMod vanDerCorput v) n) ∘ ψ) := by
        refine Measure.map_congr ?_
        filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
        exact hpt f u hu
    _ = _ := by rw [← Measure.map_map hmR hψ.measurable, hψ.map_eq]

end RQMCMarkov.PointSets

set_option linter.style.longLine false
#print axioms RQMCMarkov.PointSets.InUnitIco
#print axioms RQMCMarkov.PointSets.countBelow
#print axioms RQMCMarkov.PointSets.countAtMost
#print axioms RQMCMarkov.PointSets.localDiscrepancy
#print axioms RQMCMarkov.PointSets.starDiscrepancy
#print axioms RQMCMarkov.PointSets.qmcEstimate
#print axioms RQMCMarkov.PointSets.midpointRule
#print axioms RQMCMarkov.PointSets.countBelow_le
#print axioms RQMCMarkov.PointSets.countBelow_mono
#print axioms RQMCMarkov.PointSets.countBelow_div_mem_Icc
#print axioms RQMCMarkov.PointSets.localDiscrepancy_le_one
#print axioms RQMCMarkov.PointSets.localDiscrepancy_eq_abs_div
#print axioms RQMCMarkov.PointSets.bddAbove_localDiscrepancy
#print axioms RQMCMarkov.PointSets.localDiscrepancy_le_starDiscrepancy
#print axioms RQMCMarkov.PointSets.starDiscrepancy_le_of_forall
#print axioms RQMCMarkov.PointSets.starDiscrepancy_nonneg
#print axioms RQMCMarkov.PointSets.starDiscrepancy_le_one
#print axioms RQMCMarkov.PointSets.countAtMost_div_sub_le_starDiscrepancy
#print axioms RQMCMarkov.PointSets.inv_two_mul_le_starDiscrepancy
#print axioms RQMCMarkov.PointSets.midpointRule_mem
#print axioms RQMCMarkov.PointSets.midpointRule_lt_iff
#print axioms RQMCMarkov.PointSets.countBelow_midpointRule_le
#print axioms RQMCMarkov.PointSets.le_countBelow_midpointRule
#print axioms RQMCMarkov.PointSets.abs_countBelow_midpointRule_sub_le
#print axioms RQMCMarkov.PointSets.starDiscrepancy_midpointRule
#print axioms RQMCMarkov.PointSets.starDiscrepancy_midpointRule_le
#print axioms RQMCMarkov.PointSets.midpointRule_three
#print axioms RQMCMarkov.PointSets.starDiscrepancy_midpointRule_three
#print axioms RQMCMarkov.PointSets.totalVariation
#print axioms RQMCMarkov.PointSets.countBelow_eq_sum_indicator
#print axioms RQMCMarkov.PointSets.countAtMost_eq_sum_indicator
#print axioms RQMCMarkov.PointSets.countAtMost_le
#print axioms RQMCMarkov.PointSets.countAtMost_div_sub_le_starDiscrepancy_of_mem
#print axioms RQMCMarkov.PointSets.indicator_one_mem_Icc
#print axioms RQMCMarkov.PointSets.abs_sum_indicator_upperSet_sub_le
#print axioms RQMCMarkov.PointSets.antitone_indicator_Iic
#print axioms RQMCMarkov.PointSets.integral_indicator_Iic_one
#print axioms RQMCMarkov.PointSets.sum_div_eq_integral_indicator
#print axioms RQMCMarkov.PointSets.integral_sub_eq_integral_measureReal
#print axioms RQMCMarkov.PointSets.koksma_monotone
#print axioms RQMCMarkov.PointSets.monotone_comp_projIcc
#print axioms RQMCMarkov.PointSets.comp_projIcc_eq
#print axioms RQMCMarkov.PointSets.qmcError_congr
#print axioms RQMCMarkov.PointSets.koksma_monotoneOn
#print axioms RQMCMarkov.PointSets.koksma_sub_monotoneOn
#print axioms RQMCMarkov.PointSets.koksma_boundedVariationOn
#print axioms RQMCMarkov.PointSets.koksma_hasDerivAt
#print axioms RQMCMarkov.PointSets.eVariationOn_le_integral_abs_deriv
#print axioms RQMCMarkov.PointSets.boundedVariationOn_of_hasDerivAt
#print axioms RQMCMarkov.PointSets.totalVariation_le_integral_abs_deriv
#print axioms RQMCMarkov.PointSets.vanDerCorput
#print axioms RQMCMarkov.PointSets.vanDerCorput_eq
#print axioms RQMCMarkov.PointSets.vanDerCorput_two_mul_add
#print axioms RQMCMarkov.PointSets.vanDerCorput_one_two_three
#print axioms RQMCMarkov.PointSets.vanDerCorput_mem_Ico
#print axioms RQMCMarkov.PointSets.vanDerCorput_inUnitIco
#print axioms RQMCMarkov.PointSets.floor_two_pow_mul_vanDerCorput_lt
#print axioms RQMCMarkov.PointSets.floor_two_pow_succ_mul_vanDerCorput
#print axioms RQMCMarkov.PointSets.mod_eq_of_floor_vanDerCorput_eq
#print axioms RQMCMarkov.PointSets.floor_vanDerCorput_injOn
#print axioms RQMCMarkov.PointSets.mem_dyadic_iff_floor
#print axioms RQMCMarkov.PointSets.card_vanDerCorput_mem_dyadic
#print axioms RQMCMarkov.PointSets.card_vanDerCorput_mem_dyadic_aligned
#print axioms RQMCMarkov.PointSets.abs_card_block_vanDerCorput_sub_le
#print axioms RQMCMarkov.PointSets.countBelow_add
#print axioms RQMCMarkov.PointSets.abs_countBelow_vanDerCorput_sub_le
#print axioms RQMCMarkov.PointSets.starDiscrepancy_vanDerCorput_le
#print axioms RQMCMarkov.PointSets.natLog_two_add_one_le
#print axioms RQMCMarkov.PointSets.starDiscrepancy_vanDerCorput_le_log
#print axioms RQMCMarkov.PointSets.abs_qmcError_vanDerCorput_le
#print axioms RQMCMarkov.PointSets.tendsto_log_add_one_div_sqrt
#print axioms RQMCMarkov.PointSets.tendsto_sqrt_mul_vanDerCorput_bound
#print axioms RQMCMarkov.PointSets.tendsto_sqrt_mul_qmcError_vanDerCorput
#print axioms RQMCMarkov.PointSets.uniformIco
#print axioms RQMCMarkov.PointSets.isProbabilityMeasure_uniformIco
#print axioms RQMCMarkov.PointSets.uniformCube
#print axioms RQMCMarkov.PointSets.isProbabilityMeasure_uniformCube
#print axioms RQMCMarkov.PointSets.sampleMean
#print axioms RQMCMarkov.PointSets.map_le_of_sum_map_eq
#print axioms RQMCMarkov.PointSets.integrable_map_of_sum_map_eq
#print axioms RQMCMarkov.PointSets.memLp_map_of_sum_map_eq
#print axioms RQMCMarkov.PointSets.integral_sampleMean_of_sum_map_eq
#print axioms RQMCMarkov.PointSets.variance_sampleMean_of_sum_map_eq
#print axioms RQMCMarkov.PointSets.variance_sampleMean_le_of_sum_map_eq
#print axioms RQMCMarkov.PointSets.sum_map_eq_of_hasLaw
#print axioms RQMCMarkov.PointSets.integral_sampleMean_iid
#print axioms RQMCMarkov.PointSets.variance_sampleMean_iid
#print axioms RQMCMarkov.PointSets.rmse_sampleMean_iid
#print axioms RQMCMarkov.PointSets.tendstoInDistribution_sampleMean_iid
#print axioms RQMCMarkov.PointSets.measure_all_draws_lt_tenth
#print axioms RQMCMarkov.PointSets.measure_all_draws_lt_tenth_pos
#print axioms RQMCMarkov.PointSets.measure_sampleMean_far_pos
#print axioms RQMCMarkov.PointSets.integral_sampleMean_of_hasLaw_uniformCube
#print axioms RQMCMarkov.PointSets.uniformIco_eq_restrict_Ioc
#print axioms RQMCMarkov.PointSets.map_fract_restrict_Ioc
#print axioms RQMCMarkov.PointSets.measurePreserving_fract_add
#print axioms RQMCMarkov.PointSets.shiftMod1
#print axioms RQMCMarkov.PointSets.shiftMod1_mem_cube
#print axioms RQMCMarkov.PointSets.measurePreserving_shiftMod1
#print axioms RQMCMarkov.PointSets.hasLaw_shiftMod1
#print axioms RQMCMarkov.PointSets.integral_sampleMean_shiftMod1
#print axioms RQMCMarkov.PointSets.stratum
#print axioms RQMCMarkov.PointSets.measurableSet_stratum
#print axioms RQMCMarkov.PointSets.stratumMap
#print axioms RQMCMarkov.PointSets.measurable_stratumMap
#print axioms RQMCMarkov.PointSets.stratumMap_preimage_stratum
#print axioms RQMCMarkov.PointSets.map_stratumMap_uniformIco
#print axioms RQMCMarkov.PointSets.iUnion_stratum
#print axioms RQMCMarkov.PointSets.pairwise_disjoint_stratum
#print axioms RQMCMarkov.PointSets.sum_map_stratumMap
#print axioms RQMCMarkov.PointSets.sum_map_stratified
#print axioms RQMCMarkov.PointSets.integral_sampleMean_stratified
#print axioms RQMCMarkov.PointSets.not_hasLaw_stratumMap
#print axioms RQMCMarkov.PointSets.sum_map_eq_of_integral_sampleMean_indicator
#print axioms RQMCMarkov.PointSets.sampleMean_const_points
#print axioms RQMCMarkov.PointSets.integral_sampleMean_of_hasLaw_const
#print axioms RQMCMarkov.PointSets.variance_sampleMean_const
#print axioms RQMCMarkov.PointSets.shiftMod
#print axioms RQMCMarkov.PointSets.shiftMod_inUnitIco
#print axioms RQMCMarkov.PointSets.shiftMod_fract
#print axioms RQMCMarkov.PointSets.fract_of_lt_one
#print axioms RQMCMarkov.PointSets.fract_of_one_le
#print axioms RQMCMarkov.PointSets.countBelow_shiftMod_of_le
#print axioms RQMCMarkov.PointSets.countBelow_shiftMod_of_lt
#print axioms RQMCMarkov.PointSets.abs_countBelow_div_sub_le
#print axioms RQMCMarkov.PointSets.localDiscrepancy_shiftMod_le
#print axioms RQMCMarkov.PointSets.starDiscrepancy_shiftMod_le
#print axioms RQMCMarkov.PointSets.abs_shiftedError_le
#print axioms RQMCMarkov.PointSets.integral_qmcEstimate_shiftMod
#print axioms RQMCMarkov.PointSets.integral_sq_shiftedError_le
#print axioms RQMCMarkov.PointSets.sqrt_integral_sq_shiftedError_le
#print axioms RQMCMarkov.PointSets.sqrt_integral_sq_shiftedError_vanDerCorput_le
#print axioms RQMCMarkov.PointSets.tendsto_sqrt_mul_rmse_vanDerCorput
#print axioms RQMCMarkov.PointSets.shiftedMidpoint_counterexample
#print axioms RQMCMarkov.PointSets.continuous_stratumMap
#print axioms RQMCMarkov.PointSets.stratumMap_eq_midpoint_add
#print axioms RQMCMarkov.PointSets.midpoint_shift_mem
#print axioms RQMCMarkov.PointSets.integral_sq_sub_half_uniformIco
#print axioms RQMCMarkov.PointSets.integral_id_uniformIco
#print axioms RQMCMarkov.PointSets.integrable_uniformIco_of_continuous
#print axioms RQMCMarkov.PointSets.variance_le_of_lipschitz_half
#print axioms RQMCMarkov.PointSets.memLp_uniformIco_of_lipschitz
#print axioms RQMCMarkov.PointSets.abs_sub_stratumMap_half_le
#print axioms RQMCMarkov.PointSets.variance_stratified_eq
#print axioms RQMCMarkov.PointSets.variance_stratified_le_mc
#print axioms RQMCMarkov.PointSets.variance_stratified_le_lipschitz
#print axioms RQMCMarkov.PointSets.integral_sampleMean_commonShift
#print axioms RQMCMarkov.PointSets.variance_commonShift_le_lipschitz
#print axioms RQMCMarkov.PointSets.variance_uniformIco_id
#print axioms RQMCMarkov.PointSets.variance_uniformIco_affine
#print axioms RQMCMarkov.PointSets.variance_stratified_id
#print axioms RQMCMarkov.PointSets.variance_commonShift_id
#print axioms RQMCMarkov.PointSets.variance_stratified_id_lt_commonShift_id
#print axioms RQMCMarkov.PointSets.sum_cond_eq_of_partition
#print axioms RQMCMarkov.PointSets.variance_sampleMean_partition_le
#print axioms RQMCMarkov.PointSets.integral_uniformIco_eq_intervalIntegral
#print axioms RQMCMarkov.PointSets.sum_range_natCast
#print axioms RQMCMarkov.PointSets.scaled_error_id
#print axioms RQMCMarkov.PointSets.map_sub_half_uniformIco
#print axioms RQMCMarkov.PointSets.hasLaw_scaled_error_id
#print axioms RQMCMarkov.PointSets.cell_error_le
#print axioms RQMCMarkov.PointSets.tendsto_scaled_error
#print axioms RQMCMarkov.PointSets.ae_mem_Ico_of_hasLaw
#print axioms RQMCMarkov.PointSets.measurable_sampleMean_stratumMap
#print axioms RQMCMarkov.PointSets.ae_tendsto_scaled_error
#print axioms RQMCMarkov.PointSets.tendstoInDistribution_scaled_error
#print axioms RQMCMarkov.PointSets.map_mul_sub_half_uniformIco
#print axioms RQMCMarkov.PointSets.ne_gaussianReal_of_measure_Ioi_eq_zero
#print axioms RQMCMarkov.PointSets.limit_law_ne_gaussianReal
#print axioms RQMCMarkov.PointSets.not_tendstoInDistribution_scaled_error_gaussian
#print axioms RQMCMarkov.PointSets.tendsto_sqrt_scaled_error
#print axioms RQMCMarkov.PointSets.ae_tendsto_sqrt_scaled_error
#print axioms RQMCMarkov.PointSets.not_tendstoInDistribution_sqrt_scaled_error_gaussian
#print axioms RQMCMarkov.PointSets.sampleMean_fract_lattice
#print axioms RQMCMarkov.PointSets.measurePreserving_fract_natCast_mul
#print axioms RQMCMarkov.PointSets.hasLaw_fract_natCast_mul
#print axioms RQMCMarkov.PointSets.hasLaw_scaled_error_id_lattice
#print axioms RQMCMarkov.PointSets.tendstoInDistribution_scaled_error_lattice
#print axioms RQMCMarkov.PointSets.not_tendstoInDistribution_scaled_error_lattice_gaussian
#print axioms RQMCMarkov.PointSets.fract_natCast_mul_stratumMap
#print axioms RQMCMarkov.PointSets.variance_commonShift_sawtooth
#print axioms RQMCMarkov.PointSets.mc_variance_lt_commonShift_sawtooth
#print axioms RQMCMarkov.PointSets.digitalShift
#print axioms RQMCMarkov.PointSets.digitalShiftUpper
#print axioms RQMCMarkov.PointSets.digitalShiftSeq
#print axioms RQMCMarkov.PointSets.dyadicCell
#print axioms RQMCMarkov.PointSets.cellPerm
#print axioms RQMCMarkov.PointSets.natFloor_add_fract
#print axioms RQMCMarkov.PointSets.floor_two_pow_mul_lt
#print axioms RQMCMarkov.PointSets.xor_left_cancel'
#print axioms RQMCMarkov.PointSets.two_pow_mul_digitalShift
#print axioms RQMCMarkov.PointSets.floor_two_pow_mul_digitalShift
#print axioms RQMCMarkov.PointSets.testBit_floor_two_pow_mul_digitalShift
#print axioms RQMCMarkov.PointSets.fract_two_pow_mul_digitalShift
#print axioms RQMCMarkov.PointSets.digitalShift_mem_Ico
#print axioms RQMCMarkov.PointSets.digitalShiftUpper_eq_digitalShift
#print axioms RQMCMarkov.PointSets.volume_two_pow_mul_eq_natCast
#print axioms RQMCMarkov.PointSets.digitalShiftUpper_ae_eq
#print axioms RQMCMarkov.PointSets.digitalShift_expansion_ambiguity
#print axioms RQMCMarkov.PointSets.mem_dyadicCell_iff
#print axioms RQMCMarkov.PointSets.nonneg_of_mem_dyadicCell
#print axioms RQMCMarkov.PointSets.fract_eq_of_mem_dyadicCell
#print axioms RQMCMarkov.PointSets.mem_dyadicCell_add_iff
#print axioms RQMCMarkov.PointSets.inter_Ico_eq_biUnion_dyadicCell
#print axioms RQMCMarkov.PointSets.pairwiseDisjoint_dyadicCell_inter
#print axioms RQMCMarkov.PointSets.measurable_cellPerm
#print axioms RQMCMarkov.PointSets.cellPerm_of_mem
#print axioms RQMCMarkov.PointSets.measurePreserving_cellPerm
#print axioms RQMCMarkov.PointSets.measurePreserving_digitalShift
#print axioms RQMCMarkov.PointSets.integral_qmcEstimate_digitalShiftSeq
#print axioms RQMCMarkov.PointSets.sum_range_comp_of_injOn
#print axioms RQMCMarkov.PointSets.image_range_comp_of_injOn
#print axioms RQMCMarkov.PointSets.exists_two_pow_mul_vanDerCorput_eq
#print axioms RQMCMarkov.PointSets.two_pow_mul_vanDerCorput_eq_floor
#print axioms RQMCMarkov.PointSets.vanDerCorput_digit_inj
#print axioms RQMCMarkov.PointSets.image_vanDerCorput_digit
#print axioms RQMCMarkov.PointSets.fract_vanDerCorput_add
#print axioms RQMCMarkov.PointSets.sum_digitalShift_vanDerCorput
#print axioms RQMCMarkov.PointSets.sum_shiftMod_vanDerCorput
#print axioms RQMCMarkov.PointSets.image_digitalShift_eq_image_shiftMod_vanDerCorput
#print axioms RQMCMarkov.PointSets.qmcEstimate_digitalShift_eq_shiftMod_vanDerCorput
#print axioms RQMCMarkov.PointSets.map_qmcEstimate_digitalShift_eq_shiftMod
#print axioms RQMCMarkov.PointSets.hasLaw_scaled_error_digitalShift_id
#print axioms RQMCMarkov.PointSets.scaled_error_digitalShift_ne_gaussianReal
#print axioms RQMCMarkov.PointSets.cell_lt_half_iff
#print axioms RQMCMarkov.PointSets.digitalShift_ne_shiftMod_counterexample
#print axioms RQMCMarkov.PointSets.two_pow_mul_cellPerm
#print axioms RQMCMarkov.PointSets.floor_two_pow_mul_cellPerm
#print axioms RQMCMarkov.PointSets.fract_two_pow_mul_cellPerm
#print axioms RQMCMarkov.PointSets.sum_xor_eq_sum_add_three
#print axioms RQMCMarkov.PointSets.map_digitalShift_three_eq
#print axioms RQMCMarkov.PointSets.vdcDigit
#print axioms RQMCMarkov.PointSets.vdcPrefixMem
#print axioms RQMCMarkov.PointSets.PrefixShiftEq
#print axioms RQMCMarkov.PointSets.vanDerCorput_two_pow_add
#print axioms RQMCMarkov.PointSets.vdcDigit_lt
#print axioms RQMCMarkov.PointSets.vdcDigit_succ_of_lt
#print axioms RQMCMarkov.PointSets.vdcDigit_succ_two_pow_add
#print axioms RQMCMarkov.PointSets.exists_vdcDigit_eq
#print axioms RQMCMarkov.PointSets.vdcPrefixMem_succ_of_le
#print axioms RQMCMarkov.PointSets.vdcPrefixMem_succ_of_gt
#print axioms RQMCMarkov.PointSets.xor_eq_iff_halves
#print axioms RQMCMarkov.PointSets.add_mod_two_mul_eq_iff
#print axioms RQMCMarkov.PointSets.exists_xor_iff_of_decomp
#print axioms RQMCMarkov.PointSets.exists_add_iff_of_decomp
#print axioms RQMCMarkov.PointSets.exists_lt_xor_iff
#print axioms RQMCMarkov.PointSets.exists_lt_add_mod_iff
#print axioms RQMCMarkov.PointSets.add_pred_mod_add_one
#print axioms RQMCMarkov.PointSets.exists_false_and_iff
#print axioms RQMCMarkov.PointSets.exists_prefix_cellPerm
#print axioms RQMCMarkov.PointSets.mem_image_vdcDigit_iff
#print axioms RQMCMarkov.PointSets.image_xor_eq_image_add_mod
#print axioms RQMCMarkov.PointSets.exists_measurePreserving_digitalShift_prefix
#print axioms RQMCMarkov.PointSets.qmcEstimate_digitalShift_prefix_eq
#print axioms RQMCMarkov.PointSets.map_qmcEstimate_digitalShift_prefix_eq
