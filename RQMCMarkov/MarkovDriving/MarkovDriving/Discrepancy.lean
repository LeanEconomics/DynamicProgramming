/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real

/-! # Discrepancy of finite point sets in `[0,1)`

Copied from `RQMCMarkov/PointSets` (namespace and imports renamed); see that project for
its documentation.

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

namespace RQMCMarkov.MarkovDriving

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

end RQMCMarkov.MarkovDriving
