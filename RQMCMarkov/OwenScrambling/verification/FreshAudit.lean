import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Probability.UniformOn
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.GeomSum
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

namespace RQMCMarkov.OwenScrambling

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

end RQMCMarkov.OwenScrambling

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Monte Carlo: unbiasedness, variance `σ²/n`, RMSE `n^{-1/2}`, CLT (post #1)

Copied from `RQMCMarkov/PointSets` (namespace and imports renamed); see that project for
its documentation.

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

namespace RQMCMarkov.OwenScrambling

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

end RQMCMarkov.OwenScrambling

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# RQMC requirement (i): marginally uniform points give an unbiased estimator (posts #1–#2)

Copied from `RQMCMarkov/PointSets` (namespace and imports renamed); see that project for
its documentation.

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

namespace RQMCMarkov.OwenScrambling

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

end RQMCMarkov.OwenScrambling

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Owen's nested uniform scramble: definitions, uniformity, nets, pair law (post #2)

Post #2: "a more powerful but more computationally costly randomization for digital nets is
'Owen Scrambling' which is a 'nested uniform scramble'", and with it "a standard CLT applies"
(Loh 2003). This module sets up the `s`-dimensional objects (base `b ≥ 2`) and proves Owen's three
structural facts (Owen 1995, 1997).

**Digits and boxes.** A coordinate with `D` base-`b` digits is a string `x : Fin D → Fin b`
(digit `0` most significant), with prefix values `prefixVal x r = Σ_{k<r} x_k b^{r-1-k}` and cell
index `cellVal x = prefixVal x D`; `cellFin_bijective` identifies strings with the cells
`0, …, b^D - 1`. The real point with remainder `u` is `digitPoint x u = (cellVal x + u)/b^D`, and
`floor_pow_mul_digitPoint` reads its digits: `⌊b^r · digitPoint x u⌋ = prefixVal x r` for
`u ∈ [0,1)`, `r ≤ D`. The `b`-adic elementary box with levels `r` and index `a` is `elemBox b r a`
(volume `b^{-Σ r_j}`), membership is `boxIndex b r x = a` (`mem_elemBox_iff`), and `IsNet b t m x`
is the `(t,m,s)`-net property (Niederreiter 1992): `b^m` points of `[0,1)^s`, exactly `b^t` in
every elementary box of volume `b^{t-m}`.

**The scramble (reading).** A nested scramble of depth `D` is a family `ρ : Scramble b D` of
permutations of the digits, one for each node (level `k`, prefix `truncDigits k x`) of the
`b`-ary tree; `scramble ρ x` permutes digit `k` of `x` by the permutation of the node of its first
`k` digits. Owen's nested UNIFORM scramble takes `ρ` uniform on the finite set `Scramble b D`
(all node permutations independent and uniform), one independent scramble per coordinate, and
completes the scrambled `D` digits by independent `U[0,1)` remainders: `scrambledPoint ρ d u`. We
read Owen's scramble in this finite-depth form ("on finitely many digits plus uniform
remainders"). For points whose `D`-digit prefixes are distinct in each coordinate (e.g. a
`(0,m,s)`-net and `D ≥ m`, see `injective_coord_net` in `LohCLT`) the digits below depth `D` of the
full (infinite-depth) scramble are permuted at distinct nodes, so they are independent uniform and
the two readings have the same law; this identification is not formalised (the infinite
scramble is not defined here). The law of a random quantity built from `ρ` and the remainders `u`
is the mixture `mixLaw Q Φ = (#R)⁻¹ Σ_ρ Q.map (Φ ρ)`.

## Main results

* `agree_scramble_iff`, `scramble_injective`, `scramble_bijective`: the scramble preserves and
  reflects common prefixes (nested: points of one `b`-adic interval go to one `b`-adic interval).
* **(ii) A scrambled net is a net** (Owen 1995): `isNet_scrambledPoint` — if the digit points form
  a `(t,m,s)`-net, then for EVERY scramble and all remainders in `[0,1)` so do the scrambled
  points.
* **(i) Uniformity** (Owen 1995): `card_scramble_fiber_eq`, `card_scramble_fiber_mul` (each
  string is sent to each string by a fraction `b^{-D}` of the scrambles),
  `sum_map_digitPoint_scramble` (one scrambled coordinate is `U[0,1)`), and
  `mixLaw_scrambledPoint`: every scrambled point is `U[0,1)^s`, whatever the digit point.
  Unbiasedness follows (`ScrambleVariance.integral_scrambledLaw`, via `Unbiased`).
* **(iii) Pair law** (Owen 1997): `card_scramble_pair_eq`, `card_scramble_pair_eq_zero` and
  `card_scramble_pair`: for two strings with exactly `k = commonPrefix x x'` common leading
  digits, the scrambled pair is uniform on the pairs with exactly `k` common leading digits; its
  law `pairKernel k` depends on `(x, x')` only through `k`. The `s`-dimensional version (one
  scramble per coordinate) is `ScrambleHaar.card_scrambleVec_pair`.
* Tools: `card_agree` (`b^{D-r}` strings share a given `r`-digit prefix), `agreeKernel`
  (cell averaging kernels), `sum_pairKernel`, `pairKernel_eq_zero`, `pairKernel_eq_const`.
-/

namespace RQMCMarkov.OwenScrambling

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

variable {b D : ℕ}

/-- `Agree r x y`: the base-`b` digit strings `x, y` of length `D` have the same first `r` digits
(digit `0` is the most significant). -/
abbrev Agree (r : ℕ) (x y : Fin D → Fin b) : Prop := ∀ l : Fin D, (l : ℕ) < r → x l = y l

/-- The `k`-digit prefix of a digit string, as a node of the `b`-ary tree: the digits before
position `k`, and `none` from position `k` on. -/
def truncDigits (k : ℕ) (x : Fin D → Fin b) : Fin D → Option (Fin b) :=
  fun l ↦ if (l : ℕ) < k then some (x l) else none

/-- The `k`-th digit of `x` as a natural number (`0` beyond the length `D`). -/
def digitAt (x : Fin D → Fin b) (k : ℕ) : ℕ := if h : k < D then (x ⟨k, h⟩ : ℕ) else 0

/-- The value `Σ_{k<r} x_k b^{r-1-k}` of the first `r` digits of `x`. -/
def prefixVal (x : Fin D → Fin b) : ℕ → ℕ
  | 0 => 0
  | r + 1 => b * prefixVal x r + digitAt x r

/-- The cell index `Σ_{k<D} x_k b^{D-1-k} ∈ [0, b^D)` of a digit string. -/
def cellVal (x : Fin D → Fin b) : ℕ := prefixVal x D

/-- **Owen's nested scramble of depth `D`** (Owen 1995): one permutation `ρ (k, p)` of the `b`
digits for every node `(k, p)` of the `b`-ary tree (level `k`, prefix `p`). -/
abbrev Scramble (b D : ℕ) := Fin D × (Fin D → Option (Fin b)) → Equiv.Perm (Fin b)

/-- The nested scramble applied to a digit string: digit `k` is permuted by the permutation of
the node given by the first `k` digits. -/
def scramble (ρ : Scramble b D) (x : Fin D → Fin b) : Fin D → Fin b :=
  fun k ↦ ρ (k, truncDigits k x) (x k)

/-- Agreement on more digits implies agreement on fewer. -/
theorem agree_mono {r r' : ℕ} (h : r ≤ r') {x y : Fin D → Fin b} (hxy : Agree r' x y) :
    Agree r x y := fun l hl ↦ hxy l (lt_of_lt_of_le hl h)

/-- Agreement is symmetric. -/
theorem agree_symm {r : ℕ} {x y : Fin D → Fin b} (h : Agree r x y) : Agree r y x :=
  fun l hl ↦ (h l hl).symm

/-- Agreement is transitive. -/
theorem agree_trans {r : ℕ} {x y z : Fin D → Fin b} (h : Agree r x y) (h' : Agree r y z) :
    Agree r x z := fun l hl ↦ (h l hl).trans (h' l hl)

/-- Agreement on `D` (or more) digits is equality. -/
theorem agree_iff_eq {r : ℕ} (hr : D ≤ r) {x y : Fin D → Fin b} : Agree r x y ↔ x = y :=
  ⟨fun h ↦ funext fun l ↦ h l (lt_of_lt_of_le l.isLt hr), fun h l _ ↦ by rw [h]⟩

/-- Agreement on `r + 1` digits is agreement on `r` digits and at digit `r`. -/
theorem agree_succ_iff {r : ℕ} (hr : r < D) {x y : Fin D → Fin b} :
    Agree (r + 1) x y ↔ Agree r x y ∧ x ⟨r, hr⟩ = y ⟨r, hr⟩ := by
  constructor
  · intro h
    exact ⟨agree_mono (Nat.le_succ r) h, h ⟨r, hr⟩ (Nat.lt_succ_self r)⟩
  · rintro ⟨h1, h2⟩ l hl
    rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | hl
    · exact h1 l hl
    · have : l = ⟨r, hr⟩ := Fin.ext hl
      rw [this]
      exact h2

/-- Two `k`-digit prefixes (tree nodes) coincide iff the strings agree on `k` digits. -/
theorem truncDigits_eq_iff {k : ℕ} {x y : Fin D → Fin b} :
    truncDigits k x = truncDigits k y ↔ Agree k x y := by
  constructor
  · intro h l hl
    have := congrFun h l
    simp only [truncDigits, hl, ↓reduceIte, Option.some.injEq] at this
    exact this
  · intro h
    funext l
    by_cases hl : (l : ℕ) < k
    · simp only [truncDigits, hl, ↓reduceIte, h l hl]
    · simp only [truncDigits, hl, ↓reduceIte]

/-- **The nested scramble preserves and reflects common prefixes**: `scramble ρ x` and
`scramble ρ y` agree on their first `r` digits iff `x` and `y` do. -/
theorem agree_scramble_iff (ρ : Scramble b D) (r : ℕ) (x y : Fin D → Fin b) :
    Agree r (scramble ρ x) (scramble ρ y) ↔ Agree r x y := by
  constructor
  · induction r with
    | zero => intro _ l hl; exact absurd hl (Nat.not_lt_zero _)
    | succ r ih =>
      intro h
      have hr := ih (agree_mono (Nat.le_succ r) h)
      by_cases hrD : r < D
      · refine (agree_succ_iff hrD).2 ⟨hr, ?_⟩
        have h2 := h ⟨r, hrD⟩ (Nat.lt_succ_self r)
        have ht : truncDigits r x = truncDigits r y := truncDigits_eq_iff.2 hr
        simp only [scramble] at h2
        rw [ht] at h2
        exact (ρ _).injective h2
      · intro l hl
        exact hr l (lt_of_lt_of_le l.isLt (not_lt.1 hrD))
  · intro h l hl
    have ht : truncDigits l x = truncDigits l y := truncDigits_eq_iff.2 (agree_mono hl.le h)
    simp only [scramble]
    rw [ht, h l hl]

/-- The nested scramble is injective on digit strings. -/
theorem scramble_injective (ρ : Scramble b D) : Function.Injective (scramble ρ) := by
  intro x y h
  have : Agree D (scramble ρ x) (scramble ρ y) := fun l _ ↦ congrFun h l
  exact (agree_iff_eq le_rfl).1 ((agree_scramble_iff ρ D x y).1 this)

/-- The nested scramble is a bijection of the digit strings. -/
theorem scramble_bijective (ρ : Scramble b D) : Function.Bijective (scramble ρ) :=
  Finite.injective_iff_bijective.1 (scramble_injective ρ)

/-- Left-multiplying the scramble by a family `h` of permutations post-composes digit `k` with the
permutation `h` at the node of the original prefix. -/
theorem scramble_mul_apply (h ρ : Scramble b D) (x : Fin D → Fin b) (k : Fin D) :
    scramble (h * ρ) x k = h (k, truncDigits k x) (scramble ρ x k) := rfl

/-- A digit is less than the base. -/
theorem digitAt_lt (hb : 0 < b) (x : Fin D → Fin b) (k : ℕ) : digitAt x k < b := by
  unfold digitAt
  split_ifs with h
  · exact (x ⟨k, h⟩).isLt
  · exact hb

/-- `digitAt` at an index of the string is the digit. -/
theorem digitAt_fin (x : Fin D → Fin b) (l : Fin D) : digitAt x l = (x l : ℕ) := by
  simp only [digitAt, l.isLt, ↓reduceDIte]

/-- The value of an `r`-digit prefix is less than `b^r`. -/
theorem prefixVal_lt (hb : 0 < b) (x : Fin D → Fin b) (r : ℕ) : prefixVal x r < b ^ r := by
  induction r with
  | zero => exact Nat.one_pos
  | succ r ih =>
    change b * prefixVal x r + digitAt x r < b ^ (r + 1)
    have hd := digitAt_lt hb x r
    calc b * prefixVal x r + digitAt x r < b * prefixVal x r + b := by omega
      _ = b * (prefixVal x r + 1) := by ring
      _ ≤ b * b ^ r := Nat.mul_le_mul_left b ih
      _ = b ^ (r + 1) := by ring

/-- Two prefix values agree iff the digits agree. -/
theorem prefixVal_inj_iff (hb : 0 < b) (x y : Fin D → Fin b) (r : ℕ) :
    prefixVal x r = prefixVal y r ↔ ∀ k < r, digitAt x k = digitAt y k := by
  induction r with
  | zero => exact ⟨fun _ k hk ↦ absurd hk (Nat.not_lt_zero _), fun _ ↦ rfl⟩
  | succ r ih =>
    change b * prefixVal x r + digitAt x r = b * prefixVal y r + digitAt y r ↔ _
    have hx := digitAt_lt hb x r
    have hy := digitAt_lt hb y r
    constructor
    · intro h
      have h1 : prefixVal x r = prefixVal y r := by
        have h' : (b * prefixVal x r + digitAt x r) / b = (b * prefixVal y r + digitAt y r) / b :=
          by rw [h]
        rwa [Nat.mul_add_div hb, Nat.mul_add_div hb, Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hy,
          add_zero, add_zero] at h'
      have h2 : digitAt x r = digitAt y r := by
        rw [h1] at h
        exact Nat.add_left_cancel h
      intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
      · exact (ih.1 h1) k hk
      · rw [hk]
        exact h2
    · intro h
      rw [ih.2 (fun k hk ↦ h k (Nat.lt_succ_of_lt hk)), h r (Nat.lt_succ_self r)]

/-- For `r ≤ D`, two `r`-digit prefix values agree iff the strings agree on `r` digits. -/
theorem prefixVal_eq_iff_agree (hb : 0 < b) {r : ℕ} (hr : r ≤ D) (x y : Fin D → Fin b) :
    prefixVal x r = prefixVal y r ↔ Agree r x y := by
  rw [prefixVal_inj_iff hb]
  constructor
  · intro h l hl
    have := h l hl
    rw [digitAt_fin, digitAt_fin] at this
    exact Fin.ext this
  · intro h k hk
    have hkD : k < D := lt_of_lt_of_le hk hr
    have := h ⟨k, hkD⟩ hk
    have e1 := digitAt_fin x ⟨k, hkD⟩
    have e2 := digitAt_fin y ⟨k, hkD⟩
    rw [e1, e2, this]

/-- Dropping the last `n - r` digits: `prefixVal x n / b^(n-r) = prefixVal x r`. -/
theorem prefixVal_div (hb : 0 < b) (x : Fin D → Fin b) {r n : ℕ} (h : r ≤ n) :
    prefixVal x n / b ^ (n - r) = prefixVal x r := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left]
  clear h
  induction t with
  | zero => rw [add_zero, pow_zero, Nat.div_one]
  | succ t ih =>
    change (b * prefixVal x (r + t) + digitAt x (r + t)) / b ^ (t + 1) = _
    rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.mul_add_div hb,
      Nat.div_eq_of_lt (digitAt_lt hb x _), add_zero, ih]

/-- The cell index of a string is less than `b^D`. -/
theorem cellVal_lt (hb : 0 < b) (x : Fin D → Fin b) : cellVal x < b ^ D := prefixVal_lt hb x D

/-- The cell index is injective. -/
theorem cellVal_injective (hb : 0 < b) : Function.Injective (cellVal : (Fin D → Fin b) → ℕ) := by
  intro x y h
  exact (agree_iff_eq le_rfl).1 ((prefixVal_eq_iff_agree hb le_rfl x y).1 h)

/-- The cell index as an element of `Fin (b^D)`. -/
def cellFin (hb : 0 < b) (x : Fin D → Fin b) : Fin (b ^ D) := ⟨cellVal x, cellVal_lt hb x⟩

/-- **Digit strings and cells**: `x ↦ cellVal x` is a bijection onto `{0, …, b^D - 1}`. -/
theorem cellFin_bijective (hb : 0 < b) : Function.Bijective (cellFin (D := D) hb) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun x y h ↦ cellVal_injective hb (congrArg Fin.val h), ?_⟩
  simp only [Fintype.card_fun, Fintype.card_fin]

/-- Every value `a < b^r` (`r ≤ D`) is the `r`-digit prefix value of some string. -/
theorem exists_prefixVal_eq (hb : 0 < b) {r : ℕ} (hr : r ≤ D) {a : ℕ} (ha : a < b ^ r) :
    ∃ x : Fin D → Fin b, prefixVal x r = a := by
  have hlt : a * b ^ (D - r) < b ^ D := by
    calc a * b ^ (D - r) < b ^ r * b ^ (D - r) :=
          Nat.mul_lt_mul_of_pos_right ha (Nat.pow_pos hb)
      _ = b ^ D := by rw [← pow_add, Nat.add_sub_cancel' hr]
  obtain ⟨x, hx⟩ := (cellFin_bijective (D := D) hb).2 ⟨a * b ^ (D - r), hlt⟩
  refine ⟨x, ?_⟩
  have hv : cellVal x = a * b ^ (D - r) := congrArg Fin.val hx
  rw [← prefixVal_div hb x hr]
  change cellVal x / _ = a
  rw [hv, Nat.mul_div_cancel _ (Nat.pow_pos hb)]

/-- The real point of a digit string with remainder `u ∈ [0,1)`: `(cellVal x + u)/b^D`. -/
noncomputable def digitPoint (x : Fin D → Fin b) (u : ℝ) : ℝ :=
  ((cellVal x : ℝ) + u) / (b : ℝ) ^ D

/-- The digit point is `stratumMap (b^D) (cellVal x) u`. -/
theorem digitPoint_eq_stratumMap (x : Fin D → Fin b) (u : ℝ) :
    digitPoint x u = stratumMap (b ^ D) (cellVal x) u := by
  unfold digitPoint stratumMap
  rw [Nat.cast_pow]

/-- **Digits of a digit point**: for `u ∈ [0,1)` and `r ≤ D`,
`⌊b^r · (cellVal x + u)/b^D⌋ = prefixVal x r`. -/
theorem floor_pow_mul_digitPoint (hb : 0 < b) (x : Fin D → Fin b) {u : ℝ}
    (hu : u ∈ Ico (0 : ℝ) 1) {r : ℕ} (hr : r ≤ D) :
    ⌊(b : ℝ) ^ r * digitPoint x u⌋₊ = prefixVal x r := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have h1 : (b : ℝ) ^ r * digitPoint x u = ((cellVal x : ℝ) + u) / ((b ^ (D - r) : ℕ) : ℝ) := by
    unfold digitPoint
    rw [Nat.cast_pow]
    have hD : (b : ℝ) ^ D = (b : ℝ) ^ r * (b : ℝ) ^ (D - r) := by
      rw [← pow_add, Nat.add_sub_cancel' hr]
    rw [hD]
    have : (0 : ℝ) < (b : ℝ) ^ r := pow_pos hb' r
    have : (0 : ℝ) < (b : ℝ) ^ (D - r) := pow_pos hb' _
    field_simp
  rw [h1, Nat.floor_div_natCast, add_comm, Nat.floor_add_natCast hu.1, Nat.floor_eq_zero.2 hu.2,
    zero_add]
  exact prefixVal_div hb x hr

/-- A digit point with remainder in `[0,1)` lies in `[0,1)`. -/
theorem digitPoint_mem_Ico (hb : 0 < b) (x : Fin D → Fin b) {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) :
    digitPoint x u ∈ Ico (0 : ℝ) 1 := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have hpos : (0 : ℝ) < (b : ℝ) ^ D := pow_pos hb' D
  have hc : (cellVal x : ℝ) + 1 ≤ (b : ℝ) ^ D := by
    have := cellVal_lt hb x
    exact_mod_cast this
  unfold digitPoint
  constructor
  · exact div_nonneg (add_nonneg (Nat.cast_nonneg _) hu.1) hpos.le
  · rw [div_lt_one hpos]
    linarith [hu.2]
/-- The `b`-adic **elementary box** with levels `r` and index `a`:
`Π_j [a_j / b^{r_j}, (a_j + 1) / b^{r_j})`, of volume `b^{-Σ_j r_j}`. -/
def elemBox (b : ℕ) {s : ℕ} (r a : Fin s → ℕ) : Set (Fin s → ℝ) :=
  Set.pi univ fun j ↦ Ico ((a j : ℝ) / (b : ℝ) ^ r j) (((a j : ℝ) + 1) / (b : ℝ) ^ r j)

/-- The index of the level-`r` elementary box containing `x`: `j ↦ ⌊b^{r_j} x_j⌋`. -/
noncomputable def boxIndex (b : ℕ) {s : ℕ} (r : Fin s → ℕ) (x : Fin s → ℝ) : Fin s → ℕ :=
  fun j ↦ ⌊(b : ℝ) ^ r j * x j⌋₊

/-- A point with nonnegative coordinates lies in the elementary box `(r, a)` iff its box index
at levels `r` is `a`. -/
theorem mem_elemBox_iff (hb : 0 < b) {s : ℕ} (r a : Fin s → ℕ) {x : Fin s → ℝ}
    (hx : ∀ j, 0 ≤ x j) : x ∈ elemBox b r a ↔ boxIndex b r x = a := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  unfold elemBox boxIndex
  rw [Set.mem_univ_pi, funext_iff]
  refine forall_congr' fun j ↦ ?_
  have hq : (0 : ℝ) < (b : ℝ) ^ r j := pow_pos hb' _
  rw [Nat.floor_eq_iff (mul_nonneg hq.le (hx j)), mem_Ico, div_le_iff₀ hq, lt_div_iff₀ hq,
    mul_comm (x j)]

/-- A **`(t,m,s)`-net in base `b`** (Niederreiter 1992): `n = b^m` points of `[0,1)^s` such that
every elementary box of volume `b^{t-m}` (levels with `Σ_j r_j = m - t`) contains exactly `b^t`
of the points. Box membership is expressed by `boxIndex` (`mem_elemBox_iff`). -/
def IsNet (b t m : ℕ) {s n : ℕ} (x : Fin n → Fin s → ℝ) : Prop :=
  t ≤ m ∧ n = b ^ m ∧ (∀ i j, x i j ∈ Ico (0 : ℝ) 1) ∧
    ∀ r a : Fin s → ℕ, ∑ j, r j = m - t → (∀ j, a j < b ^ r j) →
      (Finset.univ.filter fun i ↦ boxIndex b r (x i) = a).card = b ^ t

/-- The **scrambled point**: coordinate `j` of the digit point `d` is scrambled by the nested
scramble `ρ j` and completed by the remainder `u j`. -/
noncomputable def scrambledPoint {s : ℕ} (ρ : Fin s → Scramble b D) (d : Fin s → Fin D → Fin b)
    (u : Fin s → ℝ) : Fin s → ℝ :=
  fun j ↦ digitPoint (scramble (ρ j) (d j)) (u j)

/-- **A scrambled net is a net** (Owen 1995, item (ii)): if the points
`x_i = (cellVal (d i j) / b^D)_j` form a `(t,m,s)`-net in base `b` with `m - t ≤ D` digits, then
for EVERY nested scramble `ρ` and all remainders `u ∈ [0,1)` the scrambled points form a
`(t,m,s)`-net in base `b`. -/
theorem isNet_scrambledPoint (hb : 0 < b) {t m s n : ℕ} {d : Fin n → Fin s → Fin D → Fin b}
    (hmD : m - t ≤ D) (hnet : IsNet b t m fun i j ↦ digitPoint (d i j) 0)
    (ρ : Fin s → Scramble b D) {u : Fin n → Fin s → ℝ} (hu : ∀ i j, u i j ∈ Ico (0 : ℝ) 1) :
    IsNet b t m fun i ↦ scrambledPoint ρ (d i) (u i) := by
  obtain ⟨htm, hn, _, hcount⟩ := hnet
  refine ⟨htm, hn, fun i j ↦ digitPoint_mem_Ico hb _ (hu i j), ?_⟩
  intro r a hr ha
  have hrD : ∀ j, r j ≤ D := fun j ↦ le_trans (le_trans
    (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (r j)) (Finset.mem_univ j)) hr.le) hmD
  have h0 : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, one_pos⟩
  -- a string whose scramble has prefix value `a j`
  have he : ∀ j, ∃ e : Fin D → Fin b, prefixVal (scramble (ρ j) e) (r j) = a j := by
    intro j
    obtain ⟨w, hw⟩ := exists_prefixVal_eq hb (hrD j) (ha j)
    obtain ⟨e, he⟩ := (scramble_bijective (ρ j)).2 w
    exact ⟨e, by rw [he, hw]⟩
  choose e he using he
  set a' : Fin s → ℕ := fun j ↦ prefixVal (e j) (r j) with ha'
  have ha'lt : ∀ j, a' j < b ^ r j := fun j ↦ prefixVal_lt hb _ _
  have key : ∀ i, boxIndex b r (scrambledPoint ρ (d i) (u i)) = a ↔
      boxIndex b r (fun j ↦ digitPoint (d i j) 0) = a' := by
    intro i
    unfold boxIndex scrambledPoint
    simp only [funext_iff, floor_pow_mul_digitPoint hb _ (hu i _) (hrD _),
      floor_pow_mul_digitPoint hb _ h0 (hrD _)]
    refine forall_congr' fun j ↦ ?_
    rw [← he j, ha', prefixVal_eq_iff_agree hb (hrD j), prefixVal_eq_iff_agree hb (hrD j),
      agree_scramble_iff]
  rw [Finset.filter_congr (fun i _ ↦ key i)]
  exact hcount r a' hr ha'lt

/-- **Uniformity of one scrambled string, combinatorial form**: for a fixed string `x`, the
number of nested scrambles `ρ` with `scramble ρ x = y` does not depend on the target `y`. -/
theorem card_scramble_fiber_eq (x y y' : Fin D → Fin b) :
    (Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = y).card =
      (Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = y').card := by
  have key : ∀ y y' : Fin D → Fin b,
      (Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = y).card ≤
        (Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = y').card := by
    intro y y'
    let h : Scramble b D := fun node ↦ Equiv.swap (y node.1) (y' node.1)
    refine Finset.card_le_card_of_injOn (fun ρ ↦ h * ρ) ?_ ?_
    · intro ρ hρ
      rw [Finset.mem_coe, Finset.mem_filter] at hρ ⊢
      refine ⟨Finset.mem_univ _, funext fun k ↦ ?_⟩
      rw [scramble_mul_apply, hρ.2]
      exact Equiv.swap_apply_left _ _
    · intro ρ _ ρ' _ hh
      exact mul_left_cancel hh
  exact le_antisymm (key y y') (key y' y)

/-- **Each scrambled string is uniform** (item (i), combinatorial form): exactly a fraction
`b^{-D}` of the nested scrambles send `x` to any given string `y`. -/
theorem card_scramble_fiber_mul (x y : Fin D → Fin b) :
    (Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = y).card * b ^ D =
      Fintype.card (Scramble b D) := by
  have h := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ)
    (f := fun ρ : Scramble b D ↦ scramble ρ x) (fun _ _ ↦ Finset.mem_coe.2 (Finset.mem_univ _))
  have hc : Fintype.card (Fin D → Fin b) = b ^ D := by
    simp only [Fintype.card_fun, Fintype.card_fin]
  rw [Finset.sum_congr rfl (fun y' _ ↦ card_scramble_fiber_eq x y' y), Finset.sum_const,
    Finset.card_univ, Finset.card_univ, hc, smul_eq_mul] at h
  rw [h, mul_comm]

/-- Summing a function of the scrambled string over all scrambles: each string is hit by
`#Scramble / b^D` scrambles. -/
theorem sum_scramble_eq {M : Type*} [AddCommMonoid M] (x : Fin D → Fin b)
    (G : (Fin D → Fin b) → M) :
    ∑ ρ : Scramble b D, G (scramble ρ x) =
      (Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = x).card • ∑ y, G y := by
  rw [← Finset.sum_fiberwise Finset.univ (fun ρ : Scramble b D ↦ scramble ρ x), Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [Finset.sum_congr rfl (fun ρ hρ ↦ by rw [(Finset.mem_filter.1 hρ).2]), Finset.sum_const,
    card_scramble_fiber_eq x y x]

/-- **A scrambled coordinate is uniform on `[0,1)`** (item (i), one coordinate): averaging over
the nested scrambles, the law of `(cellVal (scramble ρ x) + U)/b^D` with `U ~ U[0,1)` is
`U[0,1)`: `Σ_ρ law = #Scramble • U[0,1)`. -/
theorem sum_map_digitPoint_scramble (hb : 0 < b) (x : Fin D → Fin b) :
    ∑ ρ : Scramble b D, uniformIco.map (digitPoint (scramble ρ x)) =
      (Fintype.card (Scramble b D) : ℝ≥0∞) • uniformIco := by
  have hbD : b ^ D ≠ 0 := (Nat.pow_pos hb).ne'
  rw [sum_scramble_eq x (fun y ↦ uniformIco.map (digitPoint y))]
  have h1 : ∑ y : Fin D → Fin b, uniformIco.map (digitPoint y) =
      ∑ i : Fin (b ^ D), uniformIco.map (stratumMap (b ^ D) i) := by
    rw [← (cellFin_bijective (D := D) hb).sum_comp
      (fun i : Fin (b ^ D) ↦ uniformIco.map (stratumMap (b ^ D) i))]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    congr 1
    funext u
    rw [digitPoint_eq_stratumMap]
    rfl
  rw [h1, sum_map_stratumMap hbD, ← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul,
    ← card_scramble_fiber_mul x x, Nat.cast_mul]

/-- The law of a random quantity `Φ ρ u` when the scramble `ρ` is uniform on the finite type `R`
and independent of `u ~ Q`: the mixture `(#R)⁻¹ Σ_ρ Q.map (Φ ρ)`. -/
noncomputable def mixLaw {R E F : Type*} [Fintype R] [MeasurableSpace E] [MeasurableSpace F]
    (Q : Measure E) (Φ : R → E → F) : Measure F :=
  (Fintype.card R : ℝ≥0∞)⁻¹ • ∑ ρ, Q.map (Φ ρ)

/-- Measurability of a digit point in its remainder. -/
theorem measurable_digitPoint (x : Fin D → Fin b) : Measurable (digitPoint x) :=
  (measurable_const_add _).div_const _

/-- Measurability of a scrambled point in its remainders. -/
theorem measurable_scrambledPoint {s : ℕ} (ρ : Fin s → Scramble b D)
    (d : Fin s → Fin D → Fin b) : Measurable (scrambledPoint ρ d) :=
  measurable_pi_iff.2 fun j ↦ (measurable_digitPoint _).comp (measurable_pi_apply j)

/-- **Each scrambled point is uniform on `[0,1)^s`** (Owen 1995; item (i)): with independent
uniformly random nested scrambles in the `s` coordinates and independent `U[0,1)^s` remainders,
the scrambled point `scrambledPoint ρ d u` of ANY digit point `d` has law `U[0,1)^s`. -/
theorem mixLaw_scrambledPoint (hb : 0 < b) {s : ℕ} (d : Fin s → Fin D → Fin b) :
    mixLaw (uniformCube s) (fun (ρ : Fin s → Scramble b D) u ↦ scrambledPoint ρ d u) =
      uniformCube s := by
  have := isProbabilityMeasure_uniformIco
  have hmap : ∀ ρ : Fin s → Scramble b D, (uniformCube s).map (scrambledPoint ρ d) =
      Measure.pi fun j ↦ uniformIco.map (digitPoint (scramble (ρ j) (d j))) := fun ρ ↦
    Measure.pi_map_pi (fun j ↦ (measurable_digitPoint _).aemeasurable)
  unfold mixLaw
  simp only [hmap]
  symm
  refine Measure.pi_eq fun S hS ↦ ?_
  rw [Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  have h1 : ∀ ρ : Fin s → Scramble b D,
      (Measure.pi fun j ↦ uniformIco.map (digitPoint (scramble (ρ j) (d j)))) (Set.pi univ S) =
        ∏ j, uniformIco.map (digitPoint (scramble (ρ j) (d j))) (S j) := fun ρ ↦
    Measure.pi_pi _ _
  rw [Finset.sum_congr rfl (fun ρ _ ↦ h1 ρ)]
  rw [← Fintype.prod_sum (fun j (a : Scramble b D) ↦
    uniformIco.map (digitPoint (scramble a (d j))) (S j))]
  have h2 : ∀ j, ∑ a : Scramble b D, uniformIco.map (digitPoint (scramble a (d j))) (S j) =
      (Fintype.card (Scramble b D) : ℝ≥0∞) * uniformIco (S j) := by
    intro j
    rw [← Measure.finsetSum_apply, sum_map_digitPoint_scramble hb, Measure.smul_apply,
      smul_eq_mul]
  rw [Finset.prod_congr rfl (fun j _ ↦ h2 j), Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← mul_assoc, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_pow, ENNReal.inv_mul_cancel, one_mul]
  · exact pow_ne_zero _ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  · exact ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)

/-- Any two distinct digits can be sent to any two distinct digits by a permutation. -/
theorem exists_perm_pair {x x' z z' : Fin b} (hx : x ≠ x') (hz : z ≠ z') :
    ∃ τ : Equiv.Perm (Fin b), τ x = z ∧ τ x' = z' := by
  refine ⟨Equiv.swap (Equiv.swap x z x') z' * Equiv.swap x z, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    refine Equiv.swap_apply_of_ne_of_ne ?_ hz
    intro h
    have : Equiv.swap x z x = Equiv.swap x z x' := by rw [Equiv.swap_apply_left]; exact h
    exact hx ((Equiv.swap x z).injective this)
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

/-- Two strings whose `l`-digit prefixes agree, while they differ at digit `k` (and agree before
it), have `l ≤ k`. -/
theorem le_of_agree_of_ne {k : ℕ} (hk : k < D) {x x' : Fin D → Fin b}
    (hxk : x ⟨k, hk⟩ ≠ x' ⟨k, hk⟩) {l : ℕ} (hl : Agree l x x') : l ≤ k := by
  by_contra h
  exact hxk (hl ⟨k, hk⟩ (lt_of_not_ge h))

/-- The pair-fibre comparison behind the pair law: for two pairs of targets with the same exact
common prefix `k`, the second fibre is at least as large as the first. -/
theorem card_scramble_pair_le {k : ℕ} (hk : k < D) {x x' y y' z z' : Fin D → Fin b}
    (hxk : x ⟨k, hk⟩ ≠ x' ⟨k, hk⟩)
    (hy : Agree k y y') (hyk : y ⟨k, hk⟩ ≠ y' ⟨k, hk⟩)
    (hz : Agree k z z') (hzk : z ⟨k, hk⟩ ≠ z' ⟨k, hk⟩) :
    (Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = y ∧ scramble ρ x' = y').card ≤
      (Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = z ∧ scramble ρ x' = z').card := by
  obtain ⟨τ, hτ1, hτ2⟩ := exists_perm_pair hyk hzk
  let α : Fin D → Equiv.Perm (Fin b) := fun l ↦
    if (l : ℕ) = k then τ else Equiv.swap (y l) (z l)
  have hα : ∀ l, α l (y l) = z l := by
    intro l
    by_cases hl : (l : ℕ) = k
    · have : l = ⟨k, hk⟩ := Fin.ext hl
      simp only [α, hl, ↓reduceIte]
      rw [this, hτ1]
    · simp only [α, hl, ↓reduceIte]
      exact Equiv.swap_apply_left _ _
  let h : Scramble b D := fun node ↦
    if node.2 = truncDigits node.1 x then α node.1
    else if node.2 = truncDigits node.1 x' then Equiv.swap (y' node.1) (z' node.1) else 1
  refine Finset.card_le_card_of_injOn (fun ρ ↦ h * ρ) ?_ ?_
  · intro ρ hρ
    rw [Finset.mem_coe, Finset.mem_filter] at hρ ⊢
    obtain ⟨_, h1, h2⟩ := hρ
    refine ⟨Finset.mem_univ _, funext fun l ↦ ?_, funext fun l ↦ ?_⟩
    · rw [scramble_mul_apply, h1]
      simp only [h, ↓reduceIte]
      exact hα l
    · rw [scramble_mul_apply, h2]
      by_cases ht : truncDigits l x' = truncDigits l x
      · simp only [h, ht, ↓reduceIte]
        have hle := le_of_agree_of_ne hk hxk (truncDigits_eq_iff.1 ht.symm)
        rcases lt_or_eq_of_le hle with hlt | heq
        · rw [← hy l hlt, ← hz l hlt]
          exact hα l
        · have : l = ⟨k, hk⟩ := Fin.ext heq
          simp only [α, heq, ↓reduceIte]
          rw [this, hτ2]
      · simp only [h, ht, ↓reduceIte]
        exact Equiv.swap_apply_left _ _
  · intro ρ _ ρ' _ hh
    exact mul_left_cancel hh

/-- **Pair law of a nested scramble, combinatorial form** (Owen 1997, item (iii)): if `x, x'`
differ at digit `k < D`, then the number of scrambles sending `(x, x')` to a
target pair `(y, y')` is the same for every target pair that shares exactly its first `k` digits,
and zero for every other target pair. -/
theorem card_scramble_pair_eq {k : ℕ} (hk : k < D) {x x' : Fin D → Fin b}
    (hxk : x ⟨k, hk⟩ ≠ x' ⟨k, hk⟩) (y y' z z' : Fin D → Fin b)
    (hy : Agree k y y') (hyk : y ⟨k, hk⟩ ≠ y' ⟨k, hk⟩)
    (hz : Agree k z z') (hzk : z ⟨k, hk⟩ ≠ z' ⟨k, hk⟩) :
    (Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = y ∧ scramble ρ x' = y').card =
      (Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = z ∧ scramble ρ x' = z').card :=
  le_antisymm (card_scramble_pair_le hk hxk hy hyk hz hzk)
    (card_scramble_pair_le hk hxk hz hzk hy hyk)

/-- The pair fibre is empty unless the target pair has the same exact common prefix. -/
theorem card_scramble_pair_eq_zero {k : ℕ} (hk : k < D) {x x' : Fin D → Fin b}
    (hx : Agree k x x') (hxk : x ⟨k, hk⟩ ≠ x' ⟨k, hk⟩) {y y' : Fin D → Fin b}
    (hy : ¬ (Agree k y y' ∧ y ⟨k, hk⟩ ≠ y' ⟨k, hk⟩)) :
    (Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = y ∧ scramble ρ x' = y').card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ρ - ⟨h1, h2⟩
  apply hy
  rw [← h1, ← h2]
  refine ⟨(agree_scramble_iff ρ k x x').2 hx, fun hc ↦ hxk ?_⟩
  have hk1 : Agree (k + 1) (scramble ρ x) (scramble ρ x') :=
    (agree_succ_iff hk).2 ⟨(agree_scramble_iff ρ k x x').2 hx, hc⟩
  exact ((agree_succ_iff hk).1 ((agree_scramble_iff ρ (k + 1) x x').1 hk1)).2

/-- Agreement on `r` digits is agreement on `min r D` digits. -/
theorem agree_min_iff (r : ℕ) (x y : Fin D → Fin b) : Agree (min r D) x y ↔ Agree r x y := by
  constructor
  · intro h l hl
    exact h l (lt_min hl l.isLt)
  · intro h l hl
    exact h l (lt_of_lt_of_le hl (min_le_left _ _))

/-- **Counting a prefix class**: exactly `b^{D-r}` strings share their first `r` digits with a
given string. -/
theorem card_agree (hb : 0 < b) (r : ℕ) (y : Fin D → Fin b) :
    (Finset.univ.filter fun y' : Fin D → Fin b ↦ Agree r y y').card = b ^ (D - min r D) := by
  set r' := min r D with hr'
  have hrD : r' ≤ D := min_le_right _ _
  have hq : 0 < b ^ (D - r') := Nat.pow_pos hb
  have hbD : b ^ D = b ^ r' * b ^ (D - r') := by rw [← pow_add, Nat.add_sub_cancel' hrD]
  set q := b ^ (D - r') with hqdef
  set a := prefixVal y r' with ha
  have hcell : ∀ y' : Fin D → Fin b, Agree r y y' ↔ cellVal y' / q = a := by
    intro y'
    rw [← agree_min_iff, ← hr', ← prefixVal_eq_iff_agree hb hrD, ha, eq_comm, hqdef]
    unfold cellVal
    rw [prefixVal_div hb y' hrD]
  have halt : a < b ^ r' := prefixVal_lt hb y r'
  rw [← Finset.card_range q]
  refine Finset.card_bij (fun y' _ ↦ cellVal y' - a * q) ?_ ?_ ?_
  · intro y' hy'
    rw [Finset.mem_filter, hcell] at hy'
    rw [Finset.mem_range]
    have h1 := Nat.div_add_mod (cellVal y') q
    have h2 := Nat.mod_lt (cellVal y') hq
    rw [hy'.2] at h1
    have : q * a = a * q := mul_comm _ _
    omega
  · intro y₁ h₁ y₂ h₂ h12
    rw [Finset.mem_filter, hcell] at h₁ h₂
    have e1 := Nat.div_add_mod (cellVal y₁) q
    have e2 := Nat.div_add_mod (cellVal y₂) q
    rw [h₁.2] at e1
    rw [h₂.2] at e2
    have : q * a = a * q := mul_comm _ _
    exact cellVal_injective hb (by omega)
  · intro t ht
    rw [Finset.mem_range] at ht
    have hlt : a * q + t < b ^ D := by
      rw [hbD]
      calc a * q + t < a * q + q := by omega
        _ = (a + 1) * q := by ring
        _ ≤ b ^ r' * q := Nat.mul_le_mul_right _ halt
    obtain ⟨y', hy'⟩ := (cellFin_bijective (D := D) hb).2 ⟨a * q + t, hlt⟩
    have hv : cellVal y' = a * q + t := congrArg Fin.val hy'
    refine ⟨y', ?_, ?_⟩
    · rw [Finset.mem_filter, hcell, hv]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [add_comm, Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt ht, zero_add]
    · simp only [hv, Nat.add_sub_cancel_left]

/-- The number of leading digits common to `x` and `y` (`D` when `x = y`). -/
def commonPrefix (x y : Fin D → Fin b) : ℕ := Nat.findGreatest (fun r ↦ Agree r x y) D

/-- The common prefix length is at most `D`. -/
theorem commonPrefix_le (x y : Fin D → Fin b) : commonPrefix x y ≤ D := Nat.findGreatest_le D

/-- `x` and `y` agree on `r ≤ D` digits iff `r ≤ commonPrefix x y`. -/
theorem agree_iff_le_commonPrefix {r : ℕ} (hr : r ≤ D) (x y : Fin D → Fin b) :
    Agree r x y ↔ r ≤ commonPrefix x y := by
  constructor
  · exact fun h ↦ Nat.le_findGreatest hr h
  · intro h
    have hspec : Agree (commonPrefix x y) x y :=
      Nat.findGreatest_spec (P := fun r ↦ Agree r x y) (Nat.zero_le D)
        (fun l hl ↦ absurd hl (Nat.not_lt_zero _))
    exact agree_mono h hspec

/-- Two strings agree on their common prefix. -/
theorem agree_commonPrefix (x y : Fin D → Fin b) : Agree (commonPrefix x y) x y :=
  (agree_iff_le_commonPrefix (commonPrefix_le x y) x y).2 le_rfl

/-- Two strings differ right after their common prefix. -/
theorem ne_at_commonPrefix {x y : Fin D → Fin b} (h : commonPrefix x y < D) :
    x ⟨commonPrefix x y, h⟩ ≠ y ⟨commonPrefix x y, h⟩ := by
  intro hc
  have := (agree_succ_iff h).2 ⟨agree_commonPrefix x y, hc⟩
  have := (agree_iff_le_commonPrefix (Nat.succ_le_of_lt h) x y).1 this
  omega

/-- The common prefix length of the scrambled strings is that of the strings. -/
theorem commonPrefix_scramble (ρ : Scramble b D) (x y : Fin D → Fin b) :
    commonPrefix (scramble ρ x) (scramble ρ y) = commonPrefix x y := by
  unfold commonPrefix
  congr 1
  funext r
  exact propext (agree_scramble_iff ρ r x y)

/-- The **averaging kernel at level `r`**: `K_r(x, y) = b^{min(r,D)} / b^D` if `x, y` share their
first `r` digits, else `0`. `y ↦ K_r(x, y)` is the uniform law on the level-`r` cell of `x`. -/
noncomputable def agreeKernel (r : ℕ) (x y : Fin D → Fin b) : ℝ :=
  if Agree r x y then (b : ℝ) ^ min r D / (b : ℝ) ^ D else 0

/-- The averaging kernel is symmetric. -/
theorem agreeKernel_comm (r : ℕ) (x y : Fin D → Fin b) :
    agreeKernel r x y = agreeKernel r y x := by
  unfold agreeKernel
  by_cases h : Agree r x y
  · rw [ite_eq_left h, ite_eq_left (agree_symm h)]
  · have h' : ¬ Agree r y x := fun h' ↦ h (agree_symm h')
    rw [ite_eq_right h, ite_eq_right h']

/-- The averaging kernel has row sums `1`. -/
theorem sum_agreeKernel (hb : 0 < b) (r : ℕ) (x : Fin D → Fin b) :
    ∑ y, agreeKernel r x y = 1 := by
  unfold agreeKernel
  rw [← Finset.sum_filter, Finset.sum_const, card_agree hb, nsmul_eq_mul, Nat.cast_pow]
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have : (b : ℝ) ^ (D - min r D) * (b : ℝ) ^ min r D = (b : ℝ) ^ D := by
    rw [← pow_add, Nat.sub_add_cancel (min_le_right _ _)]
  rw [mul_div_assoc', this, div_self (pow_pos hb' D).ne']

/-- The **pair kernel** of `k` common digits: `π_k = (b K_k - K_{k+1}) / ((b - 1) b^D)`. For
`k < D` it is the uniform law on the pairs of strings with exactly `k` common leading digits; for
`k = D` it is the uniform law on the diagonal. -/
noncomputable def pairKernel (k : ℕ) (x y : Fin D → Fin b) : ℝ :=
  ((b : ℝ) * agreeKernel k x y - agreeKernel (k + 1) x y) / (((b : ℝ) - 1) * (b : ℝ) ^ D)

/-- The pair kernel is a probability on pairs. -/
theorem sum_pairKernel (hb : 1 < b) (k : ℕ) :
    ∑ x : Fin D → Fin b, ∑ y, pairKernel k x y = 1 := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  have hbD : (0 : ℝ) < (b : ℝ) ^ D := pow_pos (Nat.cast_pos.2 hb0) D
  unfold pairKernel
  simp only [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_agreeKernel hb0,
    mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow]
  rw [div_eq_one_iff_eq (mul_pos hb1 hbD).ne']
  ring

/-- The pair kernel vanishes off the pairs with exactly `k` common digits (`k < D`). -/
theorem pairKernel_eq_zero {k : ℕ} (hk : k < D) {x y : Fin D → Fin b}
    (h : ¬ (Agree k x y ∧ x ⟨k, hk⟩ ≠ y ⟨k, hk⟩)) : pairKernel k x y = 0 := by
  unfold pairKernel agreeKernel
  by_cases h1 : Agree k x y
  · have h2 : Agree (k + 1) x y := (agree_succ_iff hk).2 ⟨h1, not_not.1 fun h' ↦ h ⟨h1, h'⟩⟩
    rw [ite_eq_left h1, ite_eq_left h2,
      min_eq_left hk.le, min_eq_left (Nat.succ_le_of_lt hk), pow_succ]
    ring
  · have h2 : ¬ Agree (k + 1) x y := fun h' ↦ h1 (agree_mono (Nat.le_succ k) h')
    rw [ite_eq_right h1, ite_eq_right h2]
    ring

/-- The pair kernel is constant on the pairs with exactly `k` common digits (`k < D`). -/
theorem pairKernel_eq_const {k : ℕ} (hk : k < D) {x y : Fin D → Fin b}
    (h1 : Agree k x y) (h2 : x ⟨k, hk⟩ ≠ y ⟨k, hk⟩) :
    pairKernel k x y = (b : ℝ) ^ (k + 1) / (((b : ℝ) - 1) * (b : ℝ) ^ D * (b : ℝ) ^ D) := by
  have h3 : ¬ Agree (k + 1) x y := fun h' ↦ h2 ((agree_succ_iff hk).1 h').2
  unfold pairKernel agreeKernel
  rw [ite_eq_left h1, ite_eq_right h3, min_eq_left hk.le,
    pow_succ, sub_zero]
  field_simp

/-- The pair law off the diagonal (`k < D` exact common digits), see `card_scramble_pair`. -/
theorem card_scramble_pair_of_lt (hb : 1 < b) {k : ℕ} (hkD : k < D) {x x' : Fin D → Fin b}
    (hx : Agree k x x') (hxk : x ⟨k, hkD⟩ ≠ x' ⟨k, hkD⟩) (y y' : Fin D → Fin b) :
    ((Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = y ∧ scramble ρ x' = y').card : ℝ) =
      Fintype.card (Scramble b D) * pairKernel k y y' := by
  set T : (Fin D → Fin b) → (Fin D → Fin b) → Prop :=
    fun y y' ↦ Agree k y y' ∧ y ⟨k, hkD⟩ ≠ y' ⟨k, hkD⟩ with hT
  set c : ℕ := (Finset.univ.filter fun ρ : Scramble b D ↦
    scramble ρ x = x ∧ scramble ρ x' = x').card with hc
  have hfib : ∀ y y', ((Finset.univ.filter fun ρ : Scramble b D ↦
      scramble ρ x = y ∧ scramble ρ x' = y').card : ℝ) = if T y y' then (c : ℝ) else 0 := by
    intro y y'
    by_cases hyy : T y y'
    · simp only [hyy, ↓reduceIte]
      rw [hc, card_scramble_pair_eq hkD hxk y y' x x' hyy.1 hyy.2 hx hxk]
    · simp only [hyy, ↓reduceIte]
      rw [card_scramble_pair_eq_zero hkD hx hxk hyy, Nat.cast_zero]
  set κ : ℝ := (b : ℝ) ^ (k + 1) / (((b : ℝ) - 1) * (b : ℝ) ^ D * (b : ℝ) ^ D) with hκ
  have hker : ∀ y y', pairKernel k y y' = if T y y' then κ else 0 := by
    intro y y'
    by_cases hyy : T y y'
    · simp only [hyy, ↓reduceIte]
      rw [pairKernel_eq_const hkD hyy.1 hyy.2]
    · simp only [hyy, ↓reduceIte]
      rw [pairKernel_eq_zero hkD hyy]
  set NT : ℝ := ∑ y : Fin D → Fin b, ∑ y' : Fin D → Fin b, if T y y' then (1 : ℝ) else 0
  have hsumκ : κ * NT = 1 := by
    rw [← sum_pairKernel hb k (D := D), Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y' _ ↦ ?_
    rw [hker y y']
    split_ifs <;> ring
  have hsumc : (c : ℝ) * NT = Fintype.card (Scramble b D) := by
    have h := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ)
      (f := fun ρ : Scramble b D ↦ (scramble ρ x, scramble ρ x'))
      (fun _ _ ↦ Finset.mem_coe.2 (Finset.mem_univ _))
    rw [Finset.card_univ] at h
    rw [h, Nat.cast_sum, ← Finset.univ_product_univ, Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y' _ ↦ ?_
    have : (Finset.univ.filter fun ρ : Scramble b D ↦
        (scramble ρ x, scramble ρ x') = (y, y')) =
        (Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = y ∧ scramble ρ x' = y') := by
      refine Finset.filter_congr fun ρ _ ↦ ?_
      exact Prod.ext_iff
    rw [this, hfib y y']
    split_ifs <;> ring
  rw [hfib, hker]
  split_ifs
  · rw [← hsumc, mul_assoc, mul_comm NT κ, hsumκ, mul_one]
  · ring

/-- The pair law on the diagonal (`x = x'`), see `card_scramble_pair`. -/
theorem card_scramble_pair_diag (hb : 1 < b) (x y y' : Fin D → Fin b) :
    ((Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = y ∧ scramble ρ x = y').card : ℝ) =
      Fintype.card (Scramble b D) * pairKernel D y y' := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hfilter : (Finset.univ.filter fun ρ : Scramble b D ↦
      scramble ρ x = y ∧ scramble ρ x = y') =
      if y = y' then Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = y else ∅ := by
    split_ifs with hyy
    · subst hyy
      exact Finset.filter_congr fun ρ _ ↦ and_self_iff
    · rw [Finset.filter_eq_empty_iff]
      rintro ρ - ⟨h1, h2⟩
      exact hyy (h1.symm.trans h2)
  have hfib := card_scramble_fiber_mul x y
  have hbD : (0 : ℝ) < (b : ℝ) ^ D := pow_pos (Nat.cast_pos.2 hb0) D
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  unfold pairKernel agreeKernel
  rw [hfilter, min_eq_right (Nat.le_succ D), min_self]
  by_cases hyy : y = y'
  · have h1 : Agree D y y' := (agree_iff_eq le_rfl).2 hyy
    have h2 : Agree (D + 1) y y' := (agree_iff_eq (Nat.le_succ D)).2 hyy
    rw [ite_eq_left hyy, ite_eq_left h1, ite_eq_left h2]
    have hc : ((Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = y').card : ℝ) *
        (b : ℝ) ^ D = Fintype.card (Scramble b D) := by
      rw [← hyy]
      exact_mod_cast hfib
    rw [← hc]
    field_simp
    rw [hyy]
  · have h1 : ¬ Agree D y y' := fun h ↦ hyy ((agree_iff_eq le_rfl).1 h)
    have h2 : ¬ Agree (D + 1) y y' := fun h ↦ hyy ((agree_iff_eq (Nat.le_succ D)).1 h)
    rw [ite_eq_right hyy, ite_eq_right h1, ite_eq_right h2,
      Finset.card_empty, Nat.cast_zero]
    ring

/-- **Pair law of a nested scramble** (Owen 1997, item (iii)): if `x, x'` have exactly `k`
common leading digits (`k = commonPrefix x x'`), the fraction of nested scrambles sending
`(x, x')` to `(y, y')` is `pairKernel k y y'`: the scrambled pair is uniform on the pairs with
exactly `k` common leading digits (on the diagonal if `x = x'`). In particular the joint law of
the scrambled pair depends on `(x, x')` only through `k`. -/
theorem card_scramble_pair (hb : 1 < b) (x x' y y' : Fin D → Fin b) :
    ((Finset.univ.filter fun ρ : Scramble b D ↦ scramble ρ x = y ∧ scramble ρ x' = y').card : ℝ) =
      Fintype.card (Scramble b D) * pairKernel (commonPrefix x x') y y' := by
  rcases lt_or_eq_of_le (commonPrefix_le x x') with hkD | hkD
  · exact card_scramble_pair_of_lt hb hkD (agree_commonPrefix x x') (ne_at_commonPrefix hkD) y y'
  · have h := agree_commonPrefix x x'
    rw [hkD] at h
    have hxx : x = x' := (agree_iff_eq le_rfl).1 h
    subst hxx
    rw [hkD]
    exact card_scramble_pair_diag hb x y y'

end RQMCMarkov.OwenScrambling

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The base-`b` Haar decomposition and the second moment of a scrambled sum (Owen 1997)

Owen (1997) computes the variance of scrambled net quadrature through the base-`b` Haar
(multiresolution) ANOVA decomposition of the integrand. On the digit grid
`Fin s → Fin D → Fin b` this is finite linear algebra with kernels:

* `agreeKernel r` (`K_r`): average over the level-`r` cell; `sum_agreeKernel_mul`:
  `K_r K_{r'} = K_{min(r,r')}`; `agreeKernel_self_depth`: `K_D` is the identity.
* `detailKernel ℓ` (`δ_0 = K_0`, `δ_{ℓ+1} = K_{ℓ+1} - K_ℓ`): symmetric (`detailKernel_comm`),
  idempotent (`sum_detailKernel_mul`), telescoping to `K_r` (`sum_range_detailKernel`).
* `haarKernel ℓ = Π_j δ_{ℓ_j}` for `ℓ : Fin s → Fin (D + 1)`: symmetric, idempotent, summing to
  the identity (`sum_haarKernel`); hence the variance components
  `haarVar F ℓ = b^{-sD} Σ_{y,z} F(y) H_ℓ(y,z) F(z)` are sums of squares (`qform_eq_sum_sq`,
  `haarVar_nonneg`), add up to the mean square (`sum_haarVar`, Parseval), and `haarVar F 0` is
  the squared mean (`haarVar_zero`).
* `gainWeight b k ℓ` (`1` for `ℓ ≤ k`, `-1/(b-1)` for `ℓ = k+1`, `0` beyond) and
  `pairKernel_eq_sum`, `prod_pairKernel_eq_sum`: the pair law of two scrambled points with
  `k_j` common digits in coordinate `j` is `b^{-sD} Σ_ℓ (Π_j w(k_j, ℓ_j)) H_ℓ`.
* `scrambleVec`, `card_scrambleVec_pair` (**`s`-dimensional pair law**, item (iii)),
  `card_scrambleVec`, `sum_scrambleVec`, `sum_scrambleVec_pair`.
* `gainCoeff b d ℓ = n⁻¹ Σ_{i,i'} Π_j w(k_j(i,i'), ℓ_j)`: Owen's gain coefficients of a point
  set; `gainCoeff_zero`: `Γ_0 = n`.
* `sum_sq_sum_scrambleVec` (**the key identity**): averaging over the scrambles,
  `E[(Σ_i F(σ d_i))²] = n Σ_ℓ Γ_ℓ σ²_ℓ(F)`, for every function `F` on the grid and every point
  set `d`.
-/

namespace RQMCMarkov.OwenScrambling

open Finset

variable {b D : ℕ}

/-- Composition of averaging kernels, `r ≤ r'`. -/
theorem sum_agreeKernel_mul_of_le (hb : 0 < b) {r r' : ℕ} (h : r ≤ r') (x z : Fin D → Fin b) :
    ∑ y, agreeKernel r x y * agreeKernel r' y z = agreeKernel r x z := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have key : ∀ y, agreeKernel r x y * agreeKernel r' y z =
      if Agree r' z y then agreeKernel r x z * ((b : ℝ) ^ min r' D / (b : ℝ) ^ D) else 0 := by
    intro y
    unfold agreeKernel
    by_cases h1 : Agree r' z y
    · have h1' : Agree r' y z := agree_symm h1
      have hyz : Agree r y z := agree_mono h h1'
      rw [ite_eq_left h1', ite_eq_left h1]
      by_cases h2 : Agree r x y
      · rw [ite_eq_left h2, ite_eq_left (agree_trans h2 hyz)]
      · have h3 : ¬ Agree r x z := fun h3 ↦ h2 (agree_trans h3 (agree_symm hyz))
        rw [ite_eq_right h2, ite_eq_right h3, zero_mul]
    · have h1' : ¬ Agree r' y z := fun h' ↦ h1 (agree_symm h')
      rw [ite_eq_right h1', ite_eq_right h1, mul_zero]
  rw [Finset.sum_congr rfl (fun y _ ↦ key y), ← Finset.sum_filter, Finset.sum_const,
    card_agree hb, nsmul_eq_mul, Nat.cast_pow]
  have hp : (b : ℝ) ^ (D - min r' D) * (b : ℝ) ^ min r' D = (b : ℝ) ^ D := by
    rw [← pow_add, Nat.sub_add_cancel (min_le_right _ _)]
  rw [show (b : ℝ) ^ (D - min r' D) * (agreeKernel r x z * ((b : ℝ) ^ min r' D / (b : ℝ) ^ D)) =
      agreeKernel r x z * (((b : ℝ) ^ (D - min r' D) * (b : ℝ) ^ min r' D) / (b : ℝ) ^ D) by ring,
    hp, div_self (pow_pos hb' D).ne', mul_one]

/-- **Composition of averaging kernels**: `K_r K_{r'} = K_{min(r, r')}` (the cell averages
form a nested family of commuting projections). -/
theorem sum_agreeKernel_mul (hb : 0 < b) (r r' : ℕ) (x z : Fin D → Fin b) :
    ∑ y, agreeKernel r x y * agreeKernel r' y z = agreeKernel (min r r') x z := by
  rcases le_total r r' with h | h
  · rw [min_eq_left h]
    exact sum_agreeKernel_mul_of_le hb h x z
  · rw [min_eq_right h]
    calc ∑ y, agreeKernel r x y * agreeKernel r' y z
        = ∑ y, agreeKernel r' z y * agreeKernel r y x := by
          refine Finset.sum_congr rfl fun y _ ↦ ?_
          rw [agreeKernel_comm r x y, agreeKernel_comm r' y z, mul_comm]
      _ = agreeKernel r' z x := sum_agreeKernel_mul_of_le hb h z x
      _ = agreeKernel r' x z := agreeKernel_comm r' z x

/-- The averaging kernel at depth `D` is the identity. -/
theorem agreeKernel_self_depth (hb : 0 < b) (x y : Fin D → Fin b) :
    agreeKernel D x y = if x = y then 1 else 0 := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  unfold agreeKernel
  rw [min_self]
  by_cases h : x = y
  · rw [ite_eq_left ((agree_iff_eq le_rfl).2 h), ite_eq_left h, div_self (pow_pos hb' D).ne']
  · rw [ite_eq_right fun h' ↦ h ((agree_iff_eq le_rfl).1 h'), ite_eq_right h]

/-- The averaging kernel at level `0` is the constant `b^{-D}`. -/
theorem agreeKernel_zero (x y : Fin D → Fin b) :
    agreeKernel 0 x y = 1 / (b : ℝ) ^ D := by
  unfold agreeKernel
  rw [ite_eq_left fun l hl ↦ absurd hl (Nat.not_lt_zero _), Nat.zero_min, pow_zero]

/-- The level-`r` kernel only sees the first `min r D` digits. -/
theorem agreeKernel_min (r : ℕ) (x y : Fin D → Fin b) :
    agreeKernel (min r D) x y = agreeKernel r x y := by
  unfold agreeKernel
  rw [min_assoc, min_self]
  by_cases h : Agree r x y
  · rw [ite_eq_left ((agree_min_iff r x y).2 h), ite_eq_left h]
  · rw [ite_eq_right fun h' ↦ h ((agree_min_iff r x y).1 h'), ite_eq_right h]

/-- The **detail kernel** at level `ℓ`: `δ_0 = K_0` (the mean) and `δ_{ℓ+1} = K_{ℓ+1} - K_ℓ`
(the base-`b` Haar detail between resolutions `ℓ` and `ℓ + 1`). -/
noncomputable def detailKernel : ℕ → (Fin D → Fin b) → (Fin D → Fin b) → ℝ
  | 0 => agreeKernel 0
  | ℓ + 1 => fun x y ↦ agreeKernel (ℓ + 1) x y - agreeKernel ℓ x y

/-- The detail kernels are symmetric. -/
theorem detailKernel_comm (ℓ : ℕ) (x y : Fin D → Fin b) :
    detailKernel ℓ x y = detailKernel ℓ y x := by
  cases ℓ with
  | zero => exact agreeKernel_comm 0 x y
  | succ ℓ =>
    change agreeKernel (ℓ + 1) x y - agreeKernel ℓ x y = agreeKernel (ℓ + 1) y x - agreeKernel ℓ y x
    rw [agreeKernel_comm (ℓ + 1) x y, agreeKernel_comm ℓ x y]

/-- The detail kernels are idempotent: `δ_ℓ δ_ℓ = δ_ℓ`. -/
theorem sum_detailKernel_mul (hb : 0 < b) (ℓ : ℕ) (x z : Fin D → Fin b) :
    ∑ y, detailKernel ℓ x y * detailKernel ℓ y z = detailKernel ℓ x z := by
  cases ℓ with
  | zero =>
    change ∑ y, agreeKernel 0 x y * agreeKernel 0 y z = agreeKernel 0 x z
    rw [sum_agreeKernel_mul hb, min_self]
  | succ ℓ =>
    change ∑ y, (agreeKernel (ℓ + 1) x y - agreeKernel ℓ x y) *
      (agreeKernel (ℓ + 1) y z - agreeKernel ℓ y z) = agreeKernel (ℓ + 1) x z - agreeKernel ℓ x z
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, sum_agreeKernel_mul hb, min_self,
      min_eq_right (Nat.le_succ ℓ), min_eq_left (Nat.le_succ ℓ)]
    ring

/-- **Telescoping**: `K_r = Σ_{ℓ ≤ r} δ_ℓ`. -/
theorem sum_range_detailKernel (r : ℕ) (x y : Fin D → Fin b) :
    ∑ ℓ ∈ Finset.range (r + 1), detailKernel ℓ x y = agreeKernel r x y := by
  induction r with
  | zero => rw [Finset.sum_range_one]; rfl
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    change agreeKernel r x y + (agreeKernel (r + 1) x y - agreeKernel r x y) = _
    ring

/-- `K_r = Σ_{ℓ ≤ D, ℓ ≤ r} δ_ℓ`, as a sum over `Fin (D + 1)`. -/
theorem agreeKernel_eq_sum_fin (r : ℕ) (x y : Fin D → Fin b) :
    agreeKernel r x y =
      ∑ ℓ : Fin (D + 1), if (ℓ : ℕ) ≤ r then detailKernel ℓ x y else 0 := by
  rw [← agreeKernel_min, ← sum_range_detailKernel, Fin.sum_univ_eq_sum_range
    (fun ℓ ↦ if ℓ ≤ r then detailKernel ℓ x y else 0), ← Finset.sum_filter]
  congr 1
  ext ℓ
  rw [Finset.mem_range, Finset.mem_filter, Finset.mem_range]
  omega

/-- The **gain weight** of a detail level `ℓ` for a pair with `k` common digits:
`(b [ℓ ≤ k] - [ℓ ≤ k + 1]) / (b - 1)`, i.e. `1` for `ℓ ≤ k`, `-1/(b-1)` for `ℓ = k + 1` and `0`
beyond (Owen 1997). -/
noncomputable def gainWeight (b : ℕ) (k ℓ : ℕ) : ℝ :=
  ((b : ℝ) * (if ℓ ≤ k then 1 else 0) - (if ℓ ≤ k + 1 then 1 else 0)) / ((b : ℝ) - 1)

/-- The gain weight of the mean (`ℓ = 0`) is `1`. -/
theorem gainWeight_zero (hb : 1 < b) (k : ℕ) : gainWeight b k 0 = 1 := by
  have hb1 : (b : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  unfold gainWeight
  rw [ite_eq_left (Nat.zero_le k), ite_eq_left (Nat.zero_le _), mul_one, div_self hb1]

/-- **The pair kernel in the Haar basis**: `π_k = b^{-D} Σ_ℓ w(k, ℓ) δ_ℓ`. -/
theorem pairKernel_eq_sum (hb : 1 < b) (k : ℕ) (x y : Fin D → Fin b) :
    pairKernel k x y =
      (∑ ℓ : Fin (D + 1), gainWeight b k ℓ * detailKernel ℓ x y) / (b : ℝ) ^ D := by
  have hb1 : (b : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  unfold pairKernel gainWeight
  rw [agreeKernel_eq_sum_fin k, agreeKernel_eq_sum_fin (k + 1), Finset.mul_sum,
    ← Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun ℓ _ ↦ ?_
  split_ifs <;> field_simp <;> ring

/-- The `s`-dimensional Haar kernel `Π_j δ_{ℓ_j}` of the multiresolution component `ℓ`. -/
noncomputable def haarKernel {s : ℕ} (ℓ : Fin s → Fin (D + 1)) (y z : Fin s → Fin D → Fin b) :
    ℝ :=
  ∏ j, detailKernel (ℓ j) (y j) (z j)

/-- Products of coordinatewise kernels compose coordinatewise. -/
theorem sum_prod_mul_prod {s : ℕ} {X : Type*} [Fintype X] (A B : Fin s → X → X → ℝ)
    (y w : Fin s → X) :
    ∑ z : Fin s → X, (∏ j, A j (y j) (z j)) * ∏ j, B j (z j) (w j) =
      ∏ j, ∑ x, A j (y j) x * B j x (w j) := by
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [Finset.prod_mul_distrib]

/-- The Haar kernels are symmetric. -/
theorem haarKernel_comm {s : ℕ} (ℓ : Fin s → Fin (D + 1)) (y z : Fin s → Fin D → Fin b) :
    haarKernel ℓ y z = haarKernel ℓ z y :=
  Finset.prod_congr rfl fun _ _ ↦ detailKernel_comm _ _ _

/-- The Haar kernels are idempotent. -/
theorem sum_haarKernel_mul (hb : 0 < b) {s : ℕ} (ℓ : Fin s → Fin (D + 1))
    (y w : Fin s → Fin D → Fin b) :
    ∑ z, haarKernel ℓ y z * haarKernel ℓ z w = haarKernel ℓ y w := by
  unfold haarKernel
  rw [sum_prod_mul_prod (fun j ↦ detailKernel (ℓ j : ℕ)) (fun j ↦ detailKernel (ℓ j : ℕ))]
  exact Finset.prod_congr rfl fun _ _ ↦ sum_detailKernel_mul hb _ _ _

/-- The quadratic form `Σ_{y,z} F(y) K(y,z) F(z)` of a kernel. -/
noncomputable def qform {G : Type*} [Fintype G] (K : G → G → ℝ) (F : G → ℝ) : ℝ :=
  ∑ y, ∑ z, F y * K y z * F z

/-- The quadratic form of a symmetric idempotent kernel is a sum of squares. -/
theorem qform_eq_sum_sq {G : Type*} [Fintype G] {K : G → G → ℝ}
    (hsymm : ∀ y z, K y z = K z y) (hidem : ∀ y w, ∑ z, K y z * K z w = K y w) (F : G → ℝ) :
    qform K F = ∑ z, (∑ y, F y * K y z) ^ 2 := by
  unfold qform
  have e1 : ∀ z, (∑ y, F y * K y z) ^ 2 = ∑ y, ∑ w, F y * K y z * (F w * K w z) := by
    intro z
    rw [sq, Finset.sum_mul_sum]
  calc ∑ y, ∑ w, F y * K y w * F w = ∑ y, ∑ w, ∑ z, F y * K y z * (F w * K w z) := by
        refine Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun w _ ↦ ?_
        rw [← hidem y w, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun z _ ↦ ?_
        rw [hsymm z w]
        ring
    _ = ∑ y, ∑ z, ∑ w, F y * K y z * (F w * K w z) :=
        Finset.sum_congr rfl fun y _ ↦ Finset.sum_comm
    _ = ∑ z, ∑ y, ∑ w, F y * K y z * (F w * K w z) := Finset.sum_comm
    _ = ∑ z, (∑ y, F y * K y z) ^ 2 := Finset.sum_congr rfl fun z _ ↦ (e1 z).symm

/-- **Nonnegativity of the variance components**: `σ²_ℓ ≥ 0`. -/
theorem qform_haarKernel_nonneg (hb : 0 < b) {s : ℕ} (ℓ : Fin s → Fin (D + 1))
    (F : (Fin s → Fin D → Fin b) → ℝ) : 0 ≤ qform (haarKernel ℓ) F := by
  rw [qform_eq_sum_sq (haarKernel_comm ℓ) (sum_haarKernel_mul hb ℓ)]
  exact Finset.sum_nonneg fun z _ ↦ sq_nonneg _

/-- The Haar kernels sum to the identity. -/
theorem sum_haarKernel (hb : 0 < b) {s : ℕ} (y z : Fin s → Fin D → Fin b) :
    ∑ ℓ : Fin s → Fin (D + 1), haarKernel ℓ y z = if y = z then 1 else 0 := by
  unfold haarKernel
  rw [← Fintype.prod_sum (fun j (ℓ : Fin (D + 1)) ↦ detailKernel (ℓ : ℕ) (y j) (z j))]
  have h1 : ∀ j, ∑ ℓ : Fin (D + 1), detailKernel (ℓ : ℕ) (y j) (z j) =
      if y j = z j then 1 else 0 := by
    intro j
    rw [Fin.sum_univ_eq_sum_range (fun ℓ ↦ detailKernel ℓ (y j) (z j)), sum_range_detailKernel,
      agreeKernel_self_depth hb]
  rw [Finset.prod_congr rfl fun j _ ↦ h1 j]
  by_cases h : y = z
  · rw [ite_eq_left h]
    exact Finset.prod_eq_one fun j _ ↦ ite_eq_left (congrFun h j)
  · rw [ite_eq_right h]
    obtain ⟨j, hj⟩ : ∃ j, y j ≠ z j := by
      by_contra hc
      push Not at hc
      exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

/-- The Haar kernel of the mean (`ℓ = 0`) is the constant `b^{-sD}`. -/
theorem haarKernel_zero {s : ℕ} (y z : Fin s → Fin D → Fin b) :
    haarKernel (0 : Fin s → Fin (D + 1)) y z = 1 / ((b : ℝ) ^ D) ^ s := by
  unfold haarKernel
  have h0 : ∀ j, detailKernel (((0 : Fin s → Fin (D + 1)) j : ℕ)) (y j) (z j) = 1 / (b : ℝ) ^ D :=
    fun j ↦ by
      rw [Pi.zero_apply, Fin.val_zero]
      exact agreeKernel_zero _ _
  rw [Finset.prod_congr rfl fun j _ ↦ h0 j, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, div_pow, one_pow]

/-- **The `s`-dimensional pair kernel in the Haar basis**:
`Π_j π_{k_j}(y_j, z_j) = b^{-sD} Σ_ℓ (Π_j w(k_j, ℓ_j)) H_ℓ(y, z)`. -/
theorem prod_pairKernel_eq_sum (hb : 1 < b) {s : ℕ} (k : Fin s → ℕ)
    (y z : Fin s → Fin D → Fin b) :
    ∏ j, pairKernel (k j) (y j) (z j) =
      (∑ ℓ : Fin s → Fin (D + 1), (∏ j, gainWeight b (k j) (ℓ j)) * haarKernel ℓ y z) /
        ((b : ℝ) ^ D) ^ s := by
  rw [Finset.prod_congr rfl fun j _ ↦ pairKernel_eq_sum hb (k j) (y j) (z j),
    Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fintype.prod_sum (fun j (ℓ : Fin (D + 1)) ↦ gainWeight b (k j) ℓ * detailKernel ℓ (y j) (z j))]
  congr 1
  refine Finset.sum_congr rfl fun ℓ _ ↦ ?_
  rw [Finset.prod_mul_distrib]
  rfl

/-- The coordinatewise nested scramble of an `s`-dimensional digit point. -/
def scrambleVec {s : ℕ} (ρ : Fin s → Scramble b D) (c : Fin s → Fin D → Fin b) :
    Fin s → Fin D → Fin b :=
  fun j ↦ scramble (ρ j) (c j)

/-- **`s`-dimensional pair law** (Owen 1997, item (iii)): with independent uniform nested
scrambles in the `s` coordinates, the fraction of scrambles sending the digit points `(c, c')`
to `(y, z)` is `Π_j π_{k_j}(y_j, z_j)`, where `k_j` is the number of common leading digits of
`c_j, c'_j`. The joint law depends on `(c, c')` only through the vector `k`. -/
theorem card_scrambleVec_pair (hb : 1 < b) {s : ℕ} (c c' y z : Fin s → Fin D → Fin b) :
    ((Finset.univ.filter fun ρ : Fin s → Scramble b D ↦
        scrambleVec ρ c = y ∧ scrambleVec ρ c' = z).card : ℝ) =
      (Fintype.card (Scramble b D) : ℝ) ^ s *
        ∏ j, pairKernel (commonPrefix (c j) (c' j)) (y j) (z j) := by
  have hset : (Finset.univ.filter fun ρ : Fin s → Scramble b D ↦
      scrambleVec ρ c = y ∧ scrambleVec ρ c' = z) = Fintype.piFinset (fun j ↦
        Finset.univ.filter fun a : Scramble b D ↦ scramble a (c j) = y j ∧ scramble a (c' j) = z j)
      := by
    ext ρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, scrambleVec,
      funext_iff, forall_and]
  rw [hset, Fintype.card_piFinset, Nat.cast_prod,
    Finset.prod_congr rfl (fun j _ ↦ card_scramble_pair hb _ _ _ _), Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Sum over all scrambles of a function of a scrambled pair, by the pair law. -/
theorem sum_scrambleVec_pair (hb : 1 < b) {s : ℕ} (c c' : Fin s → Fin D → Fin b)
    (G : (Fin s → Fin D → Fin b) → (Fin s → Fin D → Fin b) → ℝ) :
    ∑ ρ : Fin s → Scramble b D, G (scrambleVec ρ c) (scrambleVec ρ c') =
      (Fintype.card (Scramble b D) : ℝ) ^ s * ∑ y, ∑ z,
        (∏ j, pairKernel (commonPrefix (c j) (c' j)) (y j) (z j)) * G y z := by
  rw [← Finset.sum_fiberwise Finset.univ (fun ρ ↦ (scrambleVec ρ c, scrambleVec ρ c'))
    (fun ρ ↦ G (scrambleVec ρ c) (scrambleVec ρ c')), ← Finset.univ_product_univ,
    Finset.sum_product, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  have h1 : ∀ ρ ∈ Finset.univ.filter (fun ρ : Fin s → Scramble b D ↦
      (scrambleVec ρ c, scrambleVec ρ c') = (y, z)),
      G (scrambleVec ρ c) (scrambleVec ρ c') = G y z := by
    intro ρ hρ
    obtain ⟨e1, e2⟩ := Prod.mk.inj (Finset.mem_filter.1 hρ).2
    rw [e1, e2]
  have h2 : (Finset.univ.filter fun ρ : Fin s → Scramble b D ↦
      (scrambleVec ρ c, scrambleVec ρ c') = (y, z)) = (Finset.univ.filter fun ρ ↦
        scrambleVec ρ c = y ∧ scrambleVec ρ c' = z) :=
    Finset.filter_congr fun ρ _ ↦ Prod.ext_iff
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, h2, card_scrambleVec_pair hb]
  ring

/-- **`s`-dimensional uniformity**: a fraction `b^{-sD}` of the scrambles send `c` to `y`. -/
theorem card_scrambleVec {s : ℕ} (c y : Fin s → Fin D → Fin b) :
    ((Finset.univ.filter fun ρ : Fin s → Scramble b D ↦ scrambleVec ρ c = y).card : ℝ) *
      ((b : ℝ) ^ D) ^ s = (Fintype.card (Scramble b D) : ℝ) ^ s := by
  have hset : (Finset.univ.filter fun ρ : Fin s → Scramble b D ↦ scrambleVec ρ c = y) =
      Fintype.piFinset (fun j ↦
        Finset.univ.filter fun a : Scramble b D ↦ scramble a (c j) = y j) := by
    ext ρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, scrambleVec,
      funext_iff]
  rw [hset, Fintype.card_piFinset, Nat.cast_prod]
  calc (∏ j, ((Finset.univ.filter fun a : Scramble b D ↦ scramble a (c j) = y j).card : ℝ)) *
        ((b : ℝ) ^ D) ^ s
      = ∏ j, (((Finset.univ.filter fun a : Scramble b D ↦ scramble a (c j) = y j).card : ℝ) *
          (b : ℝ) ^ D) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = ∏ _j : Fin s, (Fintype.card (Scramble b D) : ℝ) := by
        refine Finset.prod_congr rfl fun j _ ↦ ?_
        have := card_scramble_fiber_mul (c j) (y j)
        exact_mod_cast this
    _ = (Fintype.card (Scramble b D) : ℝ) ^ s := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Sum over all scrambles of a function of one scrambled digit point. -/
theorem sum_scrambleVec (hb : 0 < b) {s : ℕ} (c : Fin s → Fin D → Fin b)
    (G : (Fin s → Fin D → Fin b) → ℝ) :
    ∑ ρ : Fin s → Scramble b D, G (scrambleVec ρ c) =
      (Fintype.card (Scramble b D) : ℝ) ^ s * (∑ y, G y) / ((b : ℝ) ^ D) ^ s := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have hpos : (0 : ℝ) < ((b : ℝ) ^ D) ^ s := pow_pos (pow_pos hb' D) s
  rw [← Finset.sum_fiberwise Finset.univ (fun ρ ↦ scrambleVec ρ c)
    (fun ρ ↦ G (scrambleVec ρ c)), Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  have h1 : ∀ ρ ∈ Finset.univ.filter (fun ρ : Fin s → Scramble b D ↦ scrambleVec ρ c = y),
      G (scrambleVec ρ c) = G y := fun ρ hρ ↦ by rw [(Finset.mem_filter.1 hρ).2]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, ← card_scrambleVec c y]
  field_simp

/-- The **variance component** `σ²_ℓ(F) = b^{-sD} Σ_{y,z} F(y) H_ℓ(y,z) F(z) ≥ 0` of a function
on the digit grid (the squared norm of its Haar component `ℓ`). -/
noncomputable def haarVar {s : ℕ} (F : (Fin s → Fin D → Fin b) → ℝ) (ℓ : Fin s → Fin (D + 1)) :
    ℝ :=
  qform (haarKernel ℓ) F / ((b : ℝ) ^ D) ^ s

/-- The variance components are nonnegative. -/
theorem haarVar_nonneg (hb : 0 < b) {s : ℕ} (F : (Fin s → Fin D → Fin b) → ℝ)
    (ℓ : Fin s → Fin (D + 1)) : 0 ≤ haarVar F ℓ :=
  div_nonneg (qform_haarKernel_nonneg hb ℓ F) (pow_nonneg (pow_nonneg (Nat.cast_nonneg _) _) _)

/-- **Parseval**: the variance components add up to the mean square `b^{-sD} Σ_y F(y)²`. -/
theorem sum_haarVar (hb : 0 < b) {s : ℕ} (F : (Fin s → Fin D → Fin b) → ℝ) :
    ∑ ℓ, haarVar F ℓ = (∑ y, F y ^ 2) / ((b : ℝ) ^ D) ^ s := by
  unfold haarVar qform
  rw [← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single y]
  · rw [← Finset.sum_mul, ← Finset.mul_sum, sum_haarKernel hb, ite_eq_left rfl, sq]
    ring
  · intro z _ hz
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_haarKernel hb, ite_eq_right (Ne.symm hz)]
    ring
  · intro h
    exact absurd (Finset.mem_univ y) h

/-- The component of the mean: `σ²_0 = (b^{-sD} Σ_y F(y))²`. -/
theorem haarVar_zero {s : ℕ} (F : (Fin s → Fin D → Fin b) → ℝ) :
    haarVar F 0 = ((∑ y, F y) / ((b : ℝ) ^ D) ^ s) ^ 2 := by
  unfold haarVar qform
  simp only [haarKernel_zero]
  have e : ∀ y z, F y * (1 / ((b : ℝ) ^ D) ^ s) * F z = 1 / ((b : ℝ) ^ D) ^ s * (F y * F z) :=
    fun y z ↦ by ring
  simp only [e, ← Finset.mul_sum]
  rw [div_pow, sq (∑ y, F y), Finset.sum_mul]
  ring

/-- The **gain coefficients** of a point set of digit points (Owen 1997):
`Γ_ℓ = n⁻¹ Σ_{i,i'} Π_j w(k_j(i,i'), ℓ_j)`, with `k_j(i,i')` the number of common leading digits
of coordinate `j` of points `i, i'`. -/
noncomputable def gainCoeff (b : ℕ) {s n : ℕ} (d : Fin n → Fin s → Fin D → Fin b)
    (ℓ : Fin s → Fin (D + 1)) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, ∑ i', ∏ j, gainWeight b (commonPrefix (d i j) (d i' j)) (ℓ j)

/-- The gain coefficient of the mean is `n`. -/
theorem gainCoeff_zero (hb : 1 < b) {s n : ℕ} (hn : n ≠ 0) (d : Fin n → Fin s → Fin D → Fin b) :
    gainCoeff b d 0 = n := by
  unfold gainCoeff
  simp only [Pi.zero_apply, Fin.val_zero, gainWeight_zero hb, Finset.prod_const_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  field_simp

/-- Exchanging three finite sums. -/
theorem sum_sum_sum_rotate {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℝ) : ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ a, ∑ b, f a b c := by
  rw [Finset.sum_congr rfl fun a _ ↦ Finset.sum_comm, Finset.sum_comm]

/-- The pair sum `Σ_{y,z} Π_j π_{k_j}(y_j,z_j) F(y) F(z)` in terms of the gain weights and the
variance components. -/
theorem sum_pairKernel_mul_eq (hb : 1 < b) {s : ℕ} (k : Fin s → ℕ)
    (F : (Fin s → Fin D → Fin b) → ℝ) :
    ∑ y, ∑ z, (∏ j, pairKernel (k j) (y j) (z j)) * (F y * F z) =
      ∑ ℓ, (∏ j, gainWeight b (k j) (ℓ j)) * haarVar F ℓ := by
  unfold haarVar qform
  simp only [prod_pairKernel_eq_sum hb, Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
  rw [sum_sum_sum_rotate]
  refine Finset.sum_congr rfl fun ℓ _ ↦ Finset.sum_congr rfl fun y _ ↦
    Finset.sum_congr rfl fun z _ ↦ ?_
  ring

/-- **The scrambled sum, second moment** (Owen 1997): averaging over the nested scrambles,
`E[(Σ_i F(σ d_i))²] = n Σ_ℓ Γ_ℓ σ²_ℓ(F)`. -/
theorem sum_sq_sum_scrambleVec (hb : 1 < b) {s n : ℕ} (d : Fin n → Fin s → Fin D → Fin b)
    (F : (Fin s → Fin D → Fin b) → ℝ) :
    (∑ ρ : Fin s → Scramble b D, (∑ i, F (scrambleVec ρ (d i))) ^ 2) /
        (Fintype.card (Scramble b D) : ℝ) ^ s =
      n * ∑ ℓ, gainCoeff b d ℓ * haarVar F ℓ := by
  have hR : (0 : ℝ) < (Fintype.card (Scramble b D) : ℝ) ^ s :=
    pow_pos (Nat.cast_pos.2 Fintype.card_pos) s
  have e1 : ∀ ρ : Fin s → Scramble b D, (∑ i, F (scrambleVec ρ (d i))) ^ 2 =
      ∑ i, ∑ i', F (scrambleVec ρ (d i)) * F (scrambleVec ρ (d i')) := fun ρ ↦ by
    rw [sq, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl fun ρ _ ↦ e1 ρ, ← sum_sum_sum_rotate, Finset.sum_div]
  have e2 : ∀ i i', (∑ ρ : Fin s → Scramble b D,
      F (scrambleVec ρ (d i)) * F (scrambleVec ρ (d i'))) /
        (Fintype.card (Scramble b D) : ℝ) ^ s =
      ∑ ℓ, (∏ j, gainWeight b (commonPrefix (d i j) (d i' j)) (ℓ j)) * haarVar F ℓ := by
    intro i i'
    rw [sum_scrambleVec_pair hb _ _ (fun y z ↦ F y * F z), ← sum_pairKernel_mul_eq hb]
    field_simp
  simp only [Finset.sum_div, e2]
  unfold gainCoeff
  rw [Finset.mul_sum, sum_sum_sum_rotate]
  refine Finset.sum_congr rfl fun ℓ _ ↦ ?_
  simp only [← Finset.sum_mul]
  by_cases hn0 : n = 0
  · subst hn0
    simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_mul, mul_zero]
  · have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn0
    field_simp

end RQMCMarkov.OwenScrambling

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Gain coefficients of scrambled `(0,m,s)`-nets (Owen 1997)

For a `(0,m,s)`-net in base `b` (digit points with `D ≥ m` digits), Owen's gain coefficient of a
Haar component `ℓ ≠ 0` depends only on the number `p` of active coordinates (`ℓ_j ≠ 0`) and on the
total resolution `|κ| = Σ_j ℓ_j - p`: `Γ_ℓ = G(p, (m - |κ|)₊)` (`gainCoeff_net`), where the gain
sequence `gainSeq` is `G(0, L) = b^L`, `G(p+1, 0) = 1`,
`G(p+1, L+1) = -G(p, L+1)/(b-1) + b G(p, L)/(b-1)`.

## Main results

* Net counts: `card_agree_net` — every point of a `(0,m,s)`-net has exactly `b^{(m - |r|)₊}` net
  points in its level-`r` elementary box (`card_agree_net_eq_one`, `card_agree_net_of_le`,
  `card_agree_net_of_ge`; `exists_le_sum_eq`).
* `partialGain_empty`, `partialGain_insert`, `partialGain_eq_gainSeq`, `gainCoeff_net`: the gain
  coefficients of a scrambled `(0,m,s)`-net, by induction over the active coordinates.
* `gainSeq_eq_altSum`: the closed form `G(p, L) = (b/(b-1))^L Σ_{j < p-L} C(L-1+j, j)(-1/(b-1))^j`
  (`1 ≤ L`), hence `gainSeq_eq_zero`: `G(p, L) = 0` for `L ≥ p ≥ 1`.
* `alt_sum_mem_Icc`, `antitone_choose_div`, `gainAltSum_mem_Icc`, `gainSeq_mem_Icc`:
  `0 ≤ G(p, L) ≤ (b/(b-1))^{p-1}` for `1 ≤ p ≤ b + 1`.
* `gainCoeff_net_eq_zero` (**exactness**): `Γ_ℓ = 0` for every nonzero component with
  `Σ_j ℓ_j ≤ m`; `gainCoeff_net_mem_Icc` (**Owen's bound**): `0 ≤ Γ_ℓ ≤ (b/(b-1))^{s-1}` for
  `s ≤ b + 1`.

**Hypotheses.** `t = 0`. For `t > 0` the counts `card_agree_net` fail (boxes of volume below
`b^{t-m}` can hold up to `b^t` points) and Owen's `(t,m,s)` bounds are not formalised here; the
general variance formula of `ScrambleVariance` holds for any point set. `s ≤ b + 1` covers every
`(0,m,s)`-net with `m ≥ 2` (they exist only for `s ≤ b + 1`, Niederreiter 1992); where the
alternating terms stop decreasing (`L ≥ b`, possible only for `p ≥ b + 2`) the bound fails:
`gainSeq_two_four_two` gives `G(4, 2) = -4` in base `2`.
-/

namespace RQMCMarkov.OwenScrambling

open Finset

variable {b D : ℕ}

/-- `#{A < N q : ⌊A / q⌋ = K} = q` for `K < N`. -/
theorem card_filter_range_div {q N K : ℕ} (hq : 0 < q) (hK : K < N) :
    ((Finset.range (N * q)).filter fun A ↦ A / q = K).card = q := by
  calc ((Finset.range (N * q)).filter fun A ↦ A / q = K).card = (Finset.range q).card := by
        refine Finset.card_bij (fun A _ ↦ A - K * q) ?_ ?_ ?_
        · intro A hA
          rw [Finset.mem_filter, Finset.mem_range] at hA
          rw [Finset.mem_range]
          have h1 := Nat.div_add_mod A q
          have h2 := Nat.mod_lt A hq
          rw [hA.2] at h1
          have : q * K = K * q := mul_comm _ _
          omega
        · intro A₁ h₁ A₂ h₂ h12
          rw [Finset.mem_filter] at h₁ h₂
          have e1 := Nat.div_add_mod A₁ q
          have e2 := Nat.div_add_mod A₂ q
          rw [h₁.2] at e1
          rw [h₂.2] at e2
          have : q * K = K * q := mul_comm _ _
          omega
        · intro t ht
          rw [Finset.mem_range] at ht
          refine ⟨K * q + t, ?_, ?_⟩
          · rw [Finset.mem_filter, Finset.mem_range]
            constructor
            · calc K * q + t < K * q + q := by omega
                _ = (K + 1) * q := by ring
                _ ≤ N * q := Nat.mul_le_mul_right _ hK
            · rw [add_comm, Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt ht, zero_add]
          · simp only [Nat.add_sub_cancel_left]
    _ = q := Finset.card_range q

/-- The box index of a digit point (remainder `0`) at levels `r ≤ D` is the vector of prefix
values. -/
theorem boxIndex_digitPoint (hb : 0 < b) {s : ℕ} {r : Fin s → ℕ} (hr : ∀ j, r j ≤ D)
    (c : Fin s → Fin D → Fin b) :
    boxIndex b r (fun j ↦ digitPoint (c j) 0) = fun j ↦ prefixVal (c j) (r j) :=
  funext fun j ↦ floor_pow_mul_digitPoint hb _ ⟨le_rfl, one_pos⟩ (hr j)

/-- Two digit points lie in the same level-`r` box iff their coordinates agree on `r_j` digits. -/
theorem boxIndex_digitPoint_eq_iff (hb : 0 < b) {s : ℕ} {r : Fin s → ℕ} (hr : ∀ j, r j ≤ D)
    (c c' : Fin s → Fin D → Fin b) :
    boxIndex b r (fun j ↦ digitPoint (c' j) 0) = (fun j ↦ prefixVal (c j) (r j)) ↔
      ∀ j, Agree (r j) (c j) (c' j) := by
  rw [boxIndex_digitPoint hb hr, funext_iff]
  refine forall_congr' fun j ↦ ?_
  rw [eq_comm, prefixVal_eq_iff_agree hb (hr j)]

/-- **Points of a `(0,m,s)`-net in a box of volume `b^{-m}`**: exactly one. -/
theorem card_agree_net_eq_one (hb : 0 < b) {m s n : ℕ} {d : Fin n → Fin s → Fin D → Fin b}
    (hmD : m ≤ D) (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) {r : Fin s → ℕ}
    (hr : ∑ j, r j = m) (i : Fin n) :
    (Finset.univ.filter fun i' ↦ ∀ j, Agree (r j) (d i j) (d i' j)).card = 1 := by
  have hrD : ∀ j, r j ≤ D := fun j ↦ le_trans (le_trans
    (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (r j)) (Finset.mem_univ j)) hr.le) hmD
  have h := hnet.2.2.2 r (fun j ↦ prefixVal (d i j) (r j)) (by rw [hr, Nat.sub_zero])
    (fun j ↦ prefixVal_lt hb _ _)
  rw [pow_zero] at h
  rw [← h]
  congr 1
  exact Finset.filter_congr fun i' _ ↦ (boxIndex_digitPoint_eq_iff hb hrD (d i) (d i')).symm

/-- **Points of a `(0,m,s)`-net in a box of volume `b^{-|r|} ≥ b^{-m}`**: exactly
`b^{m - |r|}`. -/
theorem card_agree_net_of_le (hb : 0 < b) {m s n : ℕ} {d : Fin n → Fin s → Fin D → Fin b}
    (hmD : m ≤ D) (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) {r : Fin s → ℕ}
    (hr : ∑ j, r j ≤ m) (i : Fin n) :
    (Finset.univ.filter fun i' ↦ ∀ j, Agree (r j) (d i j) (d i' j)).card =
      b ^ (m - ∑ j, r j) := by
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    have : (Finset.univ.filter fun i' : Fin n ↦ ∀ j : Fin 0, Agree (r j) (d i j) (d i' j)) =
        Finset.univ := Finset.filter_true_of_mem fun i' _ j ↦ j.elim0
    rw [this, Finset.card_univ, Fintype.card_fin, hnet.2.1, Finset.univ_eq_empty,
      Finset.sum_empty, Nat.sub_zero]
  set j₀ : Fin s := ⟨0, hs⟩
  set e := m - ∑ j, r j with he
  set r' : Fin s → ℕ := Function.update r j₀ (r j₀ + e) with hr'
  have hsplit : ∀ g : Fin s → ℕ, ∑ j, g j = g j₀ + ∑ j ∈ Finset.univ \ {j₀}, g j := fun g ↦ by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀), Finset.sdiff_singleton_eq_erase]
  have hr'sum : ∑ j, r' j = m := by
    rw [hsplit r', hr', Function.update_self]
    have : ∑ j ∈ Finset.univ \ {j₀}, Function.update r j₀ (r j₀ + e) j =
        ∑ j ∈ Finset.univ \ {j₀}, r j := Finset.sum_congr rfl fun j hj ↦
      Function.update_of_ne (Finset.notMem_singleton.1 (Finset.mem_sdiff.1 hj).2) _ _
    rw [this]
    have := hsplit r
    omega
  have hr'D : ∀ j, r' j ≤ D := fun j ↦ le_trans (le_trans
    (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (r' j)) (Finset.mem_univ j)) hr'sum.le) hmD
  have hrD : ∀ j, r j ≤ D := fun j ↦ by
    have h1 := hr'D j
    by_cases hj : j = j₀
    · subst hj
      rw [hr', Function.update_self] at h1
      omega
    · rw [hr', Function.update_of_ne hj] at h1
      exact h1
  have hj₀D : r j₀ + e ≤ D := by
    have := hr'D j₀
    rwa [hr', Function.update_self] at this
  set S := Finset.univ.filter fun i' ↦ ∀ j, Agree (r j) (d i j) (d i' j) with hS
  set f : Fin n → ℕ := fun i' ↦ prefixVal (d i' j₀) (r j₀ + e) with hf
  set T := (Finset.range (b ^ r j₀ * b ^ e)).filter fun A ↦ A / b ^ e = prefixVal (d i j₀) (r j₀)
    with hT
  have hdiv : ∀ i' : Fin n, prefixVal (d i' j₀) (r j₀ + e) / b ^ e = prefixVal (d i' j₀) (r j₀) :=
    fun i' ↦ by
      have := prefixVal_div hb (d i' j₀) (Nat.le_add_right (r j₀) e)
      rwa [Nat.add_sub_cancel_left] at this
  have hmaps : (S : Set (Fin n)).MapsTo f T := by
    intro i' hi'
    rw [Finset.mem_coe, hS, Finset.mem_filter] at hi'
    rw [Finset.mem_coe, hT, Finset.mem_filter, Finset.mem_range, ← pow_add, hf]
    refine ⟨prefixVal_lt hb _ _, ?_⟩
    rw [hdiv i']
    exact ((prefixVal_eq_iff_agree hb (hrD j₀) _ _).2 (hi'.2 j₀)).symm
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ A ∈ T, (S.filter fun i' ↦ f i' = A).card = 1 := by
    intro A hA
    rw [hT, Finset.mem_filter, Finset.mem_range] at hA
    have h := hnet.2.2.2 r' (Function.update (fun j ↦ prefixVal (d i j) (r j)) j₀ A)
      (by rw [hr'sum, Nat.sub_zero]) (by
        intro j
        by_cases hj : j = j₀
        · subst hj
          rw [Function.update_self, hr', Function.update_self, pow_add]
          exact hA.1
        · rw [Function.update_of_ne hj, hr', Function.update_of_ne hj]
          exact prefixVal_lt hb _ _)
    rw [pow_zero] at h
    rw [← h, hS, Finset.filter_filter]
    congr 1
    refine Finset.filter_congr fun i' _ ↦ ?_
    rw [boxIndex_digitPoint hb hr'D, funext_iff]
    constructor
    · rintro ⟨hag, hfA⟩ j
      by_cases hj : j = j₀
      · subst hj
        rw [Function.update_self, hr', Function.update_self]
        exact hfA
      · rw [Function.update_of_ne hj, hr', Function.update_of_ne hj]
        exact ((prefixVal_eq_iff_agree hb (hrD j) _ _).2 (hag j)).symm
    · intro hall
      have h0 := hall j₀
      rw [Function.update_self, hr', Function.update_self] at h0
      refine ⟨fun j ↦ ?_, h0⟩
      by_cases hj : j = j₀
      · subst hj
        rw [← prefixVal_eq_iff_agree hb (hrD _), ← hdiv i', h0, hA.2]
      · have hj' := hall j
        rw [Function.update_of_ne hj, hr', Function.update_of_ne hj] at hj'
        exact (prefixVal_eq_iff_agree hb (hrD j) _ _).1 hj'.symm
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_one, hT,
    card_filter_range_div (Nat.pow_pos hb) (prefixVal_lt hb _ _)]

/-- Below any level vector of total `≥ m` there is one of total exactly `m`. -/
theorem exists_le_sum_eq {s : ℕ} {m : ℕ} :
    ∀ (k : ℕ) (r : Fin s → ℕ), ∑ j, r j = m + k → ∃ r' : Fin s → ℕ, (∀ j, r' j ≤ r j) ∧
      ∑ j, r' j = m := by
  intro k
  induction k with
  | zero => exact fun r hr ↦ ⟨r, fun _ ↦ le_rfl, hr⟩
  | succ k ih =>
    intro r hr
    obtain ⟨j, hj⟩ : ∃ j, r j ≠ 0 := by
      by_contra hc
      push Not at hc
      rw [Finset.sum_eq_zero fun j _ ↦ hc j] at hr
      omega
    have hsum : ∑ i, Function.update r j (r j - 1) i = m + k := by
      have h1 := Finset.add_sum_erase Finset.univ r (Finset.mem_univ j)
      have h2 := Finset.add_sum_erase Finset.univ (Function.update r j (r j - 1))
        (Finset.mem_univ j)
      have h3 : ∑ i ∈ Finset.univ.erase j, Function.update r j (r j - 1) i =
          ∑ i ∈ Finset.univ.erase j, r i := Finset.sum_congr rfl fun i hi ↦
        Function.update_of_ne (Finset.ne_of_mem_erase hi) _ _
      rw [Function.update_self, h3] at h2
      omega
    obtain ⟨r', hle, hr'⟩ := ih _ hsum
    refine ⟨r', fun i ↦ le_trans (hle i) ?_, hr'⟩
    by_cases hi : i = j
    · subst hi
      rw [Function.update_self]
      omega
    · rw [Function.update_of_ne hi]

/-- **Points of a `(0,m,s)`-net in a box of volume `b^{-|r|} ≤ b^{-m}`**: only the point
itself. -/
theorem card_agree_net_of_ge (hb : 0 < b) {m s n : ℕ} {d : Fin n → Fin s → Fin D → Fin b}
    (hmD : m ≤ D) (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) {r : Fin s → ℕ}
    (hr : m ≤ ∑ j, r j) (i : Fin n) :
    (Finset.univ.filter fun i' ↦ ∀ j, Agree (r j) (d i j) (d i' j)).card = 1 := by
  obtain ⟨r', hle, hr'⟩ := exists_le_sum_eq (m := m) (∑ j, r j - m) r (by omega)
  have hsub : (Finset.univ.filter fun i' ↦ ∀ j, Agree (r j) (d i j) (d i' j)) ⊆
      Finset.univ.filter fun i' ↦ ∀ j, Agree (r' j) (d i j) (d i' j) := by
    intro i' hi'
    rw [Finset.mem_filter] at hi' ⊢
    exact ⟨hi'.1, fun j ↦ agree_mono (hle j) (hi'.2 j)⟩
  have h1 := Finset.card_le_card hsub
  rw [card_agree_net_eq_one hb hmD hnet hr' i] at h1
  have h2 : 0 < (Finset.univ.filter fun i' ↦ ∀ j, Agree (r j) (d i j) (d i' j)).card :=
    Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun j l _ ↦ rfl⟩⟩
  omega

/-- **Pair counts of a `(0,m,s)`-net** (`m ≤ D`, levels `r_j ≤ D`): every point has exactly
`b^{(m - |r|)₊}` net points (itself included) in its level-`r` elementary box. -/
theorem card_agree_net (hb : 0 < b) {m s n : ℕ} {d : Fin n → Fin s → Fin D → Fin b}
    (hmD : m ≤ D) (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) (r : Fin s → ℕ)
    (i : Fin n) :
    (Finset.univ.filter fun i' ↦ ∀ j, Agree (r j) (d i j) (d i' j)).card =
      b ^ (m - ∑ j, r j) := by
  rcases le_total (∑ j, r j) m with h | h
  · exact card_agree_net_of_le hb hmD hnet h i
  · rw [card_agree_net_of_ge hb hmD hnet h i, Nat.sub_eq_zero_of_le h, pow_zero]

/-- **Owen's gain sequence** `G(p, L)`, the gain coefficient of a `(0,m,s)`-net for a Haar
component with `p` active coordinates and `L = (m - |κ|)₊` (`|κ|` the total resolution):
`G(0, L) = b^L`, `G(p+1, 0) = 1` and `G(p+1, L+1) = -G(p, L+1)/(b-1) + b G(p, L)/(b-1)`. -/
noncomputable def gainSeq (b : ℕ) : ℕ → ℕ → ℝ
  | 0, L => (b : ℝ) ^ L
  | _ + 1, 0 => 1
  | p + 1, L + 1 =>
      -1 / ((b : ℝ) - 1) * gainSeq b p (L + 1) + (b : ℝ) / ((b : ℝ) - 1) * gainSeq b p L

/-- `G(p, 0) = 1`. -/
theorem gainSeq_zero_right (b p : ℕ) : gainSeq b p 0 = 1 := by
  cases p with
  | zero => exact pow_zero _
  | succ p => rfl

/-- The recursion of the gain sequence, for every `L` (with `L - 1 = 0` when `L = 0`). -/
theorem gainSeq_succ (hb : 1 < b) (p L : ℕ) :
    gainSeq b (p + 1) L =
      -1 / ((b : ℝ) - 1) * gainSeq b p L + (b : ℝ) / ((b : ℝ) - 1) * gainSeq b p (L - 1) := by
  have hb1 : (b : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  cases L with
  | zero =>
    rw [gainSeq_zero_right, Nat.zero_sub, gainSeq_zero_right]
    field_simp
    ring
  | succ L => rfl

/-- The closed-form alternating sum `S(p, L'+1) = Σ_{j < p - L' - 1} C(L'+j, j) (-1/(b-1))^j`. -/
noncomputable def gainAltSum (b : ℕ) (p L' : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (p - (L' + 1)), ((L' + j).choose j : ℝ) * (-1 / ((b : ℝ) - 1)) ^ j

/-- Pascal recursion of the alternating sum, `S(p+1, L'+2) = S(p, L'+1) - S(p, L'+2)/(b-1)`. -/
theorem gainAltSum_succ (b p L' : ℕ) :
    gainAltSum b (p + 1) (L' + 1) =
      gainAltSum b p L' + -1 / ((b : ℝ) - 1) * gainAltSum b p (L' + 1) := by
  unfold gainAltSum
  set c : ℝ := -1 / ((b : ℝ) - 1)
  rw [show p + 1 - (L' + 1 + 1) = p - (L' + 1) by omega]
  rcases Nat.eq_zero_or_pos (p - (L' + 1)) with h | h
  · rw [h, show p - (L' + 1 + 1) = 0 by omega, Finset.sum_range_zero, Finset.sum_range_zero,
      mul_zero, add_zero]
  obtain ⟨N, hN⟩ : ∃ N, p - (L' + 1) = N + 1 := ⟨p - (L' + 1) - 1, by omega⟩
  rw [hN, show p - (L' + 1 + 1) = N by omega, Finset.sum_range_succ', Finset.sum_range_succ']
  have hpas : ∀ j, ((L' + 1 + (j + 1)).choose (j + 1) : ℝ) =
      ((L' + 1 + j).choose j : ℝ) + ((L' + (j + 1)).choose (j + 1) : ℝ) := by
    intro j
    rw [show L' + 1 + (j + 1) = (L' + 1 + j) + 1 by ring, Nat.choose_succ_succ',
      show L' + 1 + j = L' + (j + 1) by ring, Nat.cast_add]
  simp only [hpas, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, add_zero, pow_succ]
  have e : ∀ j, ((L' + 1 + j).choose j : ℝ) * (c ^ j * c) = c * (((L' + 1 + j).choose j : ℝ) *
      c ^ j) := fun j ↦ by ring
  simp only [e]
  ring

/-- **Closed form of the gain sequence**: for `p ≥ 1` and `L = L' + 1 ≥ 1`,
`G(p, L) = (b/(b-1))^L S(p, L)`. In particular `G(p, L) = 0` for `L ≥ p`. -/
theorem gainSeq_eq_altSum (hb : 1 < b) {p : ℕ} (hp : 1 ≤ p) (L' : ℕ) :
    gainSeq b p (L' + 1) = ((b : ℝ) / ((b : ℝ) - 1)) ^ (L' + 1) * gainAltSum b p L' := by
  have hb1 : (b : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  induction p, hp using Nat.le_induction generalizing L' with
  | base =>
    unfold gainAltSum
    rw [show 1 - (L' + 1) = 0 by omega, Finset.sum_range_zero, mul_zero]
    change -1 / ((b : ℝ) - 1) * (b : ℝ) ^ (L' + 1) + (b : ℝ) / ((b : ℝ) - 1) * (b : ℝ) ^ L' = 0
    rw [pow_succ]
    field_simp
    ring
  | succ p hp ih =>
    change -1 / ((b : ℝ) - 1) * gainSeq b p (L' + 1) + (b : ℝ) / ((b : ℝ) - 1) *
      gainSeq b p L' = _
    rw [ih L']
    cases L' with
    | zero =>
      rw [gainSeq_zero_right]
      unfold gainAltSum
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      rw [show q + 1 - (0 + 1) = q by omega, show q + 1 + 1 - (0 + 1) = q + 1 by omega,
        Finset.sum_range_succ']
      simp only [zero_add, Nat.choose_self, Nat.cast_one, one_mul, pow_zero,
        pow_succ, Finset.mul_sum]
      have e : ∀ j, (-1 / ((b : ℝ) - 1)) ^ j * (-1 / ((b : ℝ) - 1)) =
          (-1 / ((b : ℝ) - 1)) * (-1 / ((b : ℝ) - 1)) ^ j := fun j ↦ by ring
      simp only [e, ← Finset.mul_sum]
      ring
    | succ L' =>
      rw [ih L', gainAltSum_succ]
      ring

/-- The gain sequence vanishes for `L ≥ p ≥ 1`. -/
theorem gainSeq_eq_zero (hb : 1 < b) {p L : ℕ} (hp : 1 ≤ p) (hpL : p ≤ L) : gainSeq b p L = 0 := by
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  rw [gainSeq_eq_altSum hb hp, gainAltSum, show p - (L' + 1) = 0 by omega,
    Finset.sum_range_zero, mul_zero]

/-- **Alternating sums of a nonincreasing nonnegative sequence** lie between `0` and the first
term. -/
theorem alt_sum_mem_Icc : ∀ (N : ℕ) (t : ℕ → ℝ), (∀ j, 0 ≤ t j) → Antitone t →
    0 ≤ ∑ j ∈ Finset.range N, (-1) ^ j * t j ∧ ∑ j ∈ Finset.range N, (-1) ^ j * t j ≤ t 0 := by
  intro N
  induction N with
  | zero =>
    intro t ht _
    rw [Finset.sum_range_zero]
    exact ⟨le_rfl, ht 0⟩
  | succ N ih =>
    intro t ht hmono
    have hshift := ih (fun j ↦ t (j + 1)) (fun j ↦ ht (j + 1)) fun i j hij ↦ hmono (by omega)
    rw [Finset.sum_range_succ']
    have e : ∑ j ∈ Finset.range N, (-1 : ℝ) ^ (j + 1) * t (j + 1) =
        -∑ j ∈ Finset.range N, (-1) ^ j * t (j + 1) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [pow_succ]
      ring
    rw [e, pow_zero, one_mul]
    have h01 : t 1 ≤ t 0 := hmono (Nat.zero_le 1)
    constructor <;> linarith [hshift.1, hshift.2]

/-- The terms `C(L'+j, j) (b-1)^{-j}` are nonincreasing in `j` when `L' + 1 ≤ b - 1`. -/
theorem antitone_choose_div (hb : 1 < b) {L' : ℕ} (hL : L' + 1 ≤ b - 1) :
    Antitone fun j : ℕ ↦ ((L' + j).choose j : ℝ) * (1 / ((b : ℝ) - 1)) ^ j := by
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  refine antitone_nat_of_succ_le fun j ↦ ?_
  have hc := Nat.add_one_mul_choose_eq (L' + j) j
  have hc' : ((L' + (j + 1)).choose (j + 1) : ℝ) * ((j : ℝ) + 1) =
      ((L' + j : ℕ) + 1 : ℝ) * ((L' + j).choose j : ℝ) := by
    rw [show L' + (j + 1) = L' + j + 1 by ring]
    exact_mod_cast hc.symm
  have hbL : ((L' : ℝ) + 1) ≤ (b : ℝ) - 1 := by
    have : ((L' + 1 : ℕ) : ℝ) ≤ ((b - 1 : ℕ) : ℝ) := Nat.cast_le.2 hL
    rw [Nat.cast_sub hb.le, Nat.cast_one] at this
    push_cast at this
    exact this
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hC : (0 : ℝ) ≤ ((L' + j).choose j : ℝ) := Nat.cast_nonneg _
  have hpow : (0 : ℝ) < (1 / ((b : ℝ) - 1)) ^ j := pow_pos (by positivity) j
  rw [pow_succ]
  have key : ((L' + (j + 1)).choose (j + 1) : ℝ) * (1 / ((b : ℝ) - 1)) ≤
      ((L' + j).choose j : ℝ) := by
    rw [mul_one_div, div_le_iff₀ hb1]
    have h2 : ((L' + (j + 1)).choose (j + 1) : ℝ) * ((j : ℝ) + 1) ≤
        ((L' + j).choose j : ℝ) * (((b : ℝ) - 1) * ((j : ℝ) + 1)) := by
      rw [hc']
      have hk : ((L' + j : ℕ) : ℝ) + 1 ≤ ((b : ℝ) - 1) * ((j : ℝ) + 1) := by
        push_cast
        nlinarith [hbL, hj]
      rw [mul_comm _ ((L' + j).choose j : ℝ)]
      exact mul_le_mul_of_nonneg_left hk hC
    have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    nlinarith
  calc ((L' + (j + 1)).choose (j + 1) : ℝ) * ((1 / ((b : ℝ) - 1)) ^ j * (1 / ((b : ℝ) - 1)))
      = (((L' + (j + 1)).choose (j + 1) : ℝ) * (1 / ((b : ℝ) - 1))) * (1 / ((b : ℝ) - 1)) ^ j
        := by ring
    _ ≤ ((L' + j).choose j : ℝ) * (1 / ((b : ℝ) - 1)) ^ j :=
        mul_le_mul_of_nonneg_right key hpow.le

/-- `0 ≤ S(p, L) ≤ 1` when `L ≤ b - 1`. -/
theorem gainAltSum_mem_Icc (hb : 1 < b) (p : ℕ) {L' : ℕ} (hL : L' + 1 ≤ b - 1) :
    0 ≤ gainAltSum b p L' ∧ gainAltSum b p L' ≤ 1 := by
  have h := alt_sum_mem_Icc (p - (L' + 1))
    (fun j ↦ ((L' + j).choose j : ℝ) * (1 / ((b : ℝ) - 1)) ^ j)
    (fun j ↦ mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by
      have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
      have : (0 : ℝ) < (b : ℝ) - 1 := by linarith
      positivity) j))
    (antitone_choose_div hb hL)
  have e : gainAltSum b p L' = ∑ j ∈ Finset.range (p - (L' + 1)),
      (-1) ^ j * (((L' + j).choose j : ℝ) * (1 / ((b : ℝ) - 1)) ^ j) := by
    unfold gainAltSum
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [div_eq_mul_one_div (-1 : ℝ), mul_pow]
    ring
  rw [e]
  refine ⟨h.1, ?_⟩
  have := h.2
  simp only [add_zero, Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one] at this
  exact this

/-- **Owen's bound on the gain sequence**: for `1 ≤ p ≤ b + 1`,
`0 ≤ G(p, L) ≤ (b/(b-1))^{p-1}` for every `L`. -/
theorem gainSeq_mem_Icc (hb : 1 < b) {p : ℕ} (hp : 1 ≤ p) (hpb : p ≤ b + 1) (L : ℕ) :
    0 ≤ gainSeq b p L ∧ gainSeq b p L ≤ ((b : ℝ) / ((b : ℝ) - 1)) ^ (p - 1) := by
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  have ha : (1 : ℝ) ≤ (b : ℝ) / ((b : ℝ) - 1) := by
    rw [one_le_div hb1]
    linarith
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL
    rw [gainSeq_zero_right]
    exact ⟨zero_le_one, one_le_pow₀ ha⟩
  rcases le_or_gt p L with hpL | hpL
  · rw [gainSeq_eq_zero hb hp hpL]
    exact ⟨le_rfl, pow_nonneg (le_trans zero_le_one ha) _⟩
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  rw [gainSeq_eq_altSum hb hp]
  have hS : 0 ≤ gainAltSum b p L' ∧ gainAltSum b p L' ≤ 1 := by
    by_cases hLp : L' + 2 = p
    · unfold gainAltSum
      rw [show p - (L' + 1) = 1 by omega, Finset.sum_range_one, add_zero,
        Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one]
      exact ⟨zero_le_one, le_rfl⟩
    · exact gainAltSum_mem_Icc hb p (L' := L') (by omega)
  have hapos : (0 : ℝ) ≤ ((b : ℝ) / ((b : ℝ) - 1)) ^ (L' + 1) :=
    pow_nonneg (le_trans zero_le_one ha) _
  refine ⟨mul_nonneg hapos hS.1, ?_⟩
  calc ((b : ℝ) / ((b : ℝ) - 1)) ^ (L' + 1) * gainAltSum b p L'
      ≤ ((b : ℝ) / ((b : ℝ) - 1)) ^ (L' + 1) * 1 := mul_le_mul_of_nonneg_left hS.2 hapos
    _ = ((b : ℝ) / ((b : ℝ) - 1)) ^ (L' + 1) := mul_one _
    _ ≤ ((b : ℝ) / ((b : ℝ) - 1)) ^ (p - 1) := pow_le_pow_right₀ ha (by omega)

/-- **The gain bound needs `p ≤ b + 1`**: in base `2` with `p = 4` active coordinates and
`L = 2`, `G(4, 2) = -4 < 0`, outside `[0, (b/(b-1))^{p-1}]`. (No `(0,m,4)`-net in base `2` exists
for `m ≥ 2`, so this does not contradict Owen; it shows the bound is not a property of the gain
recursion alone.) -/
theorem gainSeq_two_four_two : gainSeq 2 4 2 = -4 := by
  simp only [gainSeq]
  norm_num

/-- The indicator that two strings agree on their first `r` digits. -/
noncomputable def agreeInd (r : ℕ) (x y : Fin D → Fin b) : ℝ := if Agree r x y then 1 else 0

/-- The gain factor of one active coordinate:
`(b/(b-1)) [agree on ℓ digits] - (1/(b-1)) [agree on ℓ - 1 digits]`. -/
noncomputable def gainFactor (b : ℕ) (ℓ : ℕ) (x y : Fin D → Fin b) : ℝ :=
  (b : ℝ) / ((b : ℝ) - 1) * agreeInd ℓ x y + -1 / ((b : ℝ) - 1) * agreeInd (ℓ - 1) x y

/-- The gain weight of a pair is its gain factor. -/
theorem gainWeight_commonPrefix (hb : 1 < b) {ℓ : ℕ} (hℓ : ℓ ≤ D) (x y : Fin D → Fin b) :
    gainWeight b (commonPrefix x y) ℓ = gainFactor b ℓ x y := by
  have hb1 : (b : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  have h1 : ℓ ≤ commonPrefix x y ↔ Agree ℓ x y := (agree_iff_le_commonPrefix hℓ x y).symm
  have h2 : ℓ ≤ commonPrefix x y + 1 ↔ Agree (ℓ - 1) x y := by
    rw [agree_iff_le_commonPrefix (by omega) x y]
    omega
  unfold gainWeight gainFactor agreeInd
  by_cases a1 : Agree ℓ x y <;> by_cases a2 : Agree (ℓ - 1) x y
  · rw [ite_eq_left (h1.2 a1), ite_eq_left (h2.2 a2), ite_eq_left a1, ite_eq_left a2]
    field_simp
    ring
  · rw [ite_eq_left (h1.2 a1), ite_eq_right (fun h ↦ a2 (h2.1 h)), ite_eq_left a1,
      ite_eq_right a2]
    field_simp
    ring
  · rw [ite_eq_right (fun h ↦ a1 (h1.1 h)), ite_eq_left (h2.2 a2), ite_eq_right a1,
      ite_eq_left a2]
    field_simp
    ring
  · rw [ite_eq_right (fun h ↦ a1 (h1.1 h)), ite_eq_right (fun h ↦ a2 (h2.1 h)), ite_eq_right a1,
      ite_eq_right a2]
    ring

/-- The partial gain: coordinates in `u` carry the gain factor of level `ℓ_j`, the others the
agreement indicator of level `ℓ_j`. -/
noncomputable def partialGain (b : ℕ) {s n : ℕ} (d : Fin n → Fin s → Fin D → Fin b)
    (u : Finset (Fin s)) (ℓ : Fin s → ℕ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, ∑ i', ∏ j,
    (if j ∈ u then gainFactor b (ℓ j) (d i j) (d i' j) else agreeInd (ℓ j) (d i j) (d i' j))

/-- The gain coefficient is the partial gain with all coordinates active. -/
theorem gainCoeff_eq_partialGain (hb : 1 < b) {s n : ℕ} (d : Fin n → Fin s → Fin D → Fin b)
    (ℓ : Fin s → Fin (D + 1)) :
    gainCoeff b d ℓ = partialGain b d Finset.univ fun j ↦ (ℓ j : ℕ) := by
  unfold gainCoeff partialGain
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun i' _ ↦
    Finset.prod_congr rfl fun j _ ↦ ?_
  rw [ite_eq_left (Finset.mem_univ j)]
  exact gainWeight_commonPrefix hb (Nat.lt_succ_iff.1 (ℓ j).isLt) _ _

/-- With no active coordinate the partial gain is the normalised pair count `b^{(m - |ℓ|)₊}`
of the net. -/
theorem partialGain_empty (hb : 0 < b) {m s n : ℕ} {d : Fin n → Fin s → Fin D → Fin b}
    (hmD : m ≤ D) (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) (ℓ : Fin s → ℕ) :
    partialGain b d ∅ ℓ = (b : ℝ) ^ (m - ∑ j, ℓ j) := by
  unfold partialGain agreeInd
  have hn : (n : ℝ) ≠ 0 := by
    rw [hnet.2.1, Nat.cast_pow]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 hb.ne')
  have h1 : ∀ i, ∑ i', ∏ j, (if j ∈ (∅ : Finset (Fin s)) then gainFactor b (ℓ j) (d i j) (d i' j)
      else if Agree (ℓ j) (d i j) (d i' j) then (1 : ℝ) else 0) = (b : ℝ) ^ (m - ∑ j, ℓ j) := by
    intro i
    simp only [Finset.notMem_empty, ↓reduceIte]
    rw [Finset.sum_congr rfl fun i' _ ↦ Fintype.prod_boole]
    have h2 : (∑ i', if ∀ j, Agree (ℓ j) (d i j) (d i' j) then (1 : ℝ) else 0) =
        (b : ℝ) ^ (m - ∑ j, ℓ j) := by
      rw [← Finset.natCast_card_filter, card_agree_net hb hmD hnet ℓ i, Nat.cast_pow]
    convert h2
  rw [Finset.sum_congr rfl fun i _ ↦ h1 i, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- **Recursion of the partial gain** in one more active coordinate `j ∉ u`. -/
theorem partialGain_insert {s n : ℕ} (d : Fin n → Fin s → Fin D → Fin b) {u : Finset (Fin s)}
    {j : Fin s} (hj : j ∉ u) (ℓ : Fin s → ℕ) :
    partialGain b d (insert j u) ℓ =
      (b : ℝ) / ((b : ℝ) - 1) * partialGain b d u ℓ +
        -1 / ((b : ℝ) - 1) * partialGain b d u (Function.update ℓ j (ℓ j - 1)) := by
  unfold partialGain
  have key : ∀ i i', ∏ j', (if j' ∈ insert j u then gainFactor b (ℓ j') (d i j') (d i' j')
      else agreeInd (ℓ j') (d i j') (d i' j')) =
      (b : ℝ) / ((b : ℝ) - 1) * ∏ j', (if j' ∈ u then gainFactor b (ℓ j') (d i j') (d i' j')
        else agreeInd (ℓ j') (d i j') (d i' j')) +
      -1 / ((b : ℝ) - 1) * ∏ j', (if j' ∈ u then
        gainFactor b (Function.update ℓ j (ℓ j - 1) j') (d i j') (d i' j')
        else agreeInd (Function.update ℓ j (ℓ j - 1) j') (d i j') (d i' j')) := by
    intro i i'
    rw [Fintype.prod_eq_mul_prod_compl j, Fintype.prod_eq_mul_prod_compl j,
      Fintype.prod_eq_mul_prod_compl j, ite_eq_left (Finset.mem_insert_self j u),
      ite_eq_right hj, ite_eq_right hj, Function.update_self]
    have hrest1 : ∏ j' ∈ {j}ᶜ, (if j' ∈ insert j u then gainFactor b (ℓ j') (d i j') (d i' j')
        else agreeInd (ℓ j') (d i j') (d i' j')) = ∏ j' ∈ {j}ᶜ,
          (if j' ∈ u then gainFactor b (ℓ j') (d i j') (d i' j')
          else agreeInd (ℓ j') (d i j') (d i' j')) := by
      refine Finset.prod_congr rfl fun j' hj' ↦ ?_
      have hne : j' ≠ j := by
        rw [Finset.mem_compl, Finset.mem_singleton] at hj'
        exact hj'
      simp only [Finset.mem_insert, hne, false_or]
    have hrest2 : ∏ j' ∈ {j}ᶜ, (if j' ∈ u then
        gainFactor b (Function.update ℓ j (ℓ j - 1) j') (d i j') (d i' j')
        else agreeInd (Function.update ℓ j (ℓ j - 1) j') (d i j') (d i' j')) = ∏ j' ∈ {j}ᶜ,
          (if j' ∈ u then gainFactor b (ℓ j') (d i j') (d i' j')
          else agreeInd (ℓ j') (d i j') (d i' j')) := by
      refine Finset.prod_congr rfl fun j' hj' ↦ ?_
      have hne : j' ≠ j := by
        rw [Finset.mem_compl, Finset.mem_singleton] at hj'
        exact hj'
      rw [Function.update_of_ne hne]
    rw [hrest1, hrest2]
    unfold gainFactor
    ring
  simp only [key, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- Coordinates with nonzero level contribute at least one each to the total level. -/
theorem card_filter_add_le_sum {s : ℕ} (ℓ : Fin s → ℕ) {u : Finset (Fin s)} {j : Fin s}
    (hj : j ∉ u) : (u.filter fun j' ↦ ℓ j' ≠ 0).card + ℓ j ≤ ∑ j', ℓ j' := by
  have hj' : j ∉ u.filter fun j' ↦ ℓ j' ≠ 0 := fun h ↦ hj (Finset.mem_filter.1 h).1
  calc (u.filter fun j' ↦ ℓ j' ≠ 0).card + ℓ j
      ≤ ∑ j' ∈ u.filter (fun j' ↦ ℓ j' ≠ 0), ℓ j' + ℓ j := by
        refine Nat.add_le_add_right ?_ _
        rw [Finset.card_eq_sum_ones]
        exact Finset.sum_le_sum fun j' hj'' ↦ Nat.one_le_iff_ne_zero.2 (Finset.mem_filter.1 hj'').2
    _ = ∑ j' ∈ insert j (u.filter fun j' ↦ ℓ j' ≠ 0), ℓ j' := by
        rw [Finset.sum_insert hj', add_comm]
    _ ≤ ∑ j', ℓ j' := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- **The partial gain of a `(0,m,s)`-net is Owen's gain sequence**: with `p` the number of active
coordinates of nonzero level, `partialGain u ℓ = G(p, (m - (|ℓ| - p))₊)`. -/
theorem partialGain_eq_gainSeq (hb : 1 < b) {m s n : ℕ} {d : Fin n → Fin s → Fin D → Fin b}
    (hmD : m ≤ D) (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) (u : Finset (Fin s)) :
    ∀ ℓ : Fin s → ℕ, partialGain b d u ℓ =
      gainSeq b (u.filter fun j ↦ ℓ j ≠ 0).card
        (m - (∑ j, ℓ j - (u.filter fun j ↦ ℓ j ≠ 0).card)) := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hb1 : (b : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  induction u using Finset.induction_on with
  | empty =>
    intro ℓ
    rw [partialGain_empty hb0 hmD hnet, Finset.filter_empty, Finset.card_empty, Nat.sub_zero]
    rfl
  | insert j u hj ih =>
    intro ℓ
    rw [partialGain_insert d hj ℓ, Finset.filter_insert]
    by_cases hℓ : ℓ j = 0
    · rw [ite_eq_right (not_not.2 hℓ), show ℓ j - 1 = ℓ j by omega, Function.update_eq_self, ih ℓ]
      field_simp
      ring
    · rw [ite_eq_left hℓ]
      have hj' : j ∉ u.filter fun j' ↦ ℓ j' ≠ 0 := fun h ↦ hj (Finset.mem_filter.1 h).1
      rw [Finset.card_insert_of_notMem hj']
      set ℓ' := Function.update ℓ j (ℓ j - 1) with hℓ'
      have hfil : (u.filter fun j' ↦ ℓ' j' ≠ 0) = u.filter fun j' ↦ ℓ j' ≠ 0 := by
        refine Finset.filter_congr fun j' hj'' ↦ ?_
        have hne : j' ≠ j := fun h ↦ hj (h ▸ hj'')
        rw [hℓ', Function.update_of_ne hne]
      have hsum : ∑ j', ℓ' j' + 1 = ∑ j', ℓ j' := by
        have h1 := Finset.add_sum_erase Finset.univ ℓ (Finset.mem_univ j)
        have h2 := Finset.add_sum_erase Finset.univ ℓ' (Finset.mem_univ j)
        have h3 : ∑ i ∈ Finset.univ.erase j, ℓ' i = ∑ i ∈ Finset.univ.erase j, ℓ i :=
          Finset.sum_congr rfl fun i hi ↦ Function.update_of_ne (Finset.ne_of_mem_erase hi) _ _
        rw [hℓ', Function.update_self] at h2
        rw [h3] at h2
        rw [hℓ']
        omega
      have hle := card_filter_add_le_sum ℓ hj
      rw [ih ℓ, ih ℓ', hfil, gainSeq_succ hb]
      set p := (u.filter fun j' ↦ ℓ j' ≠ 0).card
      rw [show m - (∑ j', ℓ' j' - p) = m - (∑ j', ℓ j' - (p + 1)) by omega,
        show m - (∑ j', ℓ j' - p) = m - (∑ j', ℓ j' - (p + 1)) - 1 by omega]
      ring

/-- **Gain coefficients of a scrambled `(0,m,s)`-net** (Owen 1997): for `m ≤ D` digits,
`Γ_ℓ = G(p, (m - |κ|)₊)` with `p = #{j : ℓ_j ≠ 0}` the number of active coordinates and
`|κ| = Σ_j ℓ_j - p` the total resolution of the Haar component. -/
theorem gainCoeff_net (hb : 1 < b) {m s n : ℕ} {d : Fin n → Fin s → Fin D → Fin b}
    (hmD : m ≤ D) (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    (ℓ : Fin s → Fin (D + 1)) :
    gainCoeff b d ℓ = gainSeq b (Finset.univ.filter fun j ↦ (ℓ j : ℕ) ≠ 0).card
      (m - (∑ j, (ℓ j : ℕ) - (Finset.univ.filter fun j ↦ (ℓ j : ℕ) ≠ 0).card)) := by
  rw [gainCoeff_eq_partialGain hb, partialGain_eq_gainSeq hb hmD hnet]

/-- The number of active coordinates of a nonzero component is at least `1`. -/
theorem one_le_card_active {s : ℕ} {ℓ : Fin s → Fin (D + 1)} (hℓ : ℓ ≠ 0) :
    1 ≤ (Finset.univ.filter fun j ↦ (ℓ j : ℕ) ≠ 0).card := by
  obtain ⟨j, hj⟩ : ∃ j, ℓ j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hℓ (funext hc)
  refine Finset.card_pos.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
  intro h
  exact hj (Fin.ext h)

/-- **Scrambled `(0,m,s)`-nets integrate low-resolution components exactly** (Owen 1997):
`Γ_ℓ = 0` for every nonzero component with `|ℓ| ≤ m`. -/
theorem gainCoeff_net_eq_zero (hb : 1 < b) {m s n : ℕ} {d : Fin n → Fin s → Fin D → Fin b}
    (hmD : m ≤ D) (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    {ℓ : Fin s → Fin (D + 1)} (hℓ : ℓ ≠ 0) (hsum : ∑ j, (ℓ j : ℕ) ≤ m) :
    gainCoeff b d ℓ = 0 := by
  rw [gainCoeff_net hb hmD hnet]
  have h1 := one_le_card_active hℓ
  have h2 : (Finset.univ.filter fun j ↦ (ℓ j : ℕ) ≠ 0).card ≤ ∑ j, (ℓ j : ℕ) := by
    rw [Finset.card_eq_sum_ones]
    calc ∑ j ∈ Finset.univ.filter (fun j ↦ (ℓ j : ℕ) ≠ 0), 1
        ≤ ∑ j ∈ Finset.univ.filter (fun j ↦ (ℓ j : ℕ) ≠ 0), (ℓ j : ℕ) :=
          Finset.sum_le_sum fun j hj ↦ Nat.one_le_iff_ne_zero.2 (Finset.mem_filter.1 hj).2
      _ ≤ ∑ j, (ℓ j : ℕ) := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  exact gainSeq_eq_zero hb h1 (by omega)

/-- **Owen's gain bound for scrambled `(0,m,s)`-nets with `s ≤ b + 1`** (Owen 1997): every
nonzero component has `0 ≤ Γ_ℓ ≤ (b/(b-1))^{s-1}`. (For `m ≥ 2`, `(0,m,s)`-nets in base `b`
exist only for `s ≤ b + 1`.) -/
theorem gainCoeff_net_mem_Icc (hb : 1 < b) {m s n : ℕ} {d : Fin n → Fin s → Fin D → Fin b}
    (hmD : m ≤ D) (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) (hsb : s ≤ b + 1)
    {ℓ : Fin s → Fin (D + 1)} (hℓ : ℓ ≠ 0) :
    0 ≤ gainCoeff b d ℓ ∧ gainCoeff b d ℓ ≤ ((b : ℝ) / ((b : ℝ) - 1)) ^ (s - 1) := by
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  have ha : (1 : ℝ) ≤ (b : ℝ) / ((b : ℝ) - 1) := by
    rw [one_le_div hb1]
    linarith
  rw [gainCoeff_net hb hmD hnet]
  have h1 := one_le_card_active hℓ
  have hps : (Finset.univ.filter fun j ↦ (ℓ j : ℕ) ≠ 0).card ≤ s := by
    calc (Finset.univ.filter fun j ↦ (ℓ j : ℕ) ≠ 0).card ≤ Finset.univ.card :=
          Finset.card_filter_le _ _
      _ = s := by rw [Finset.card_univ, Fintype.card_fin]
  have h := gainSeq_mem_Icc hb h1 (le_trans hps hsb)
    (m - (∑ j, (ℓ j : ℕ) - (Finset.univ.filter fun j ↦ (ℓ j : ℕ) ≠ 0).card))
  exact ⟨h.1, le_trans h.2 (pow_le_pow_right₀ ha (by omega))⟩

end RQMCMarkov.OwenScrambling

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Variance of scrambled net quadrature (Owen 1997; post #2)

The scrambled-net estimator `μ̂ = (1/n) Σ_i f(X_i)`, `X_i = scrambledPoint ρ (d i) (u i)`, with
`ρ` uniform over the `s`-fold nested scrambles and the remainders `u ~ remLaw s n`
(i.i.d. `U[0,1)^s`), has law `scrambledLaw f d` (a `mixLaw`). We compute its variance exactly.

**Reduction to the grid.** With the cell averages `F = cellAvg f` and cell mean squares
`cellSq f`, independence of the remainders (`integral_remLaw_mul`) gives the moments for a fixed
scramble (`integral_scrambledEstimate`, `integral_sq_scrambledEstimate`); the cells tile the cube
(`sum_map_cellPoint`, `sum_integral_cellPoint`).

## Main results

* `integral_scrambledLaw` (**unbiasedness**, posts #1–#2): `E[μ̂] = ∫ f` for ANY digit points.
* `variance_eq_cellResVar_add` (**ANOVA–Haar decomposition**): `Var f = σ²_{>D} + Σ_{ℓ≠0} σ²_ℓ`,
  with the within-cell variance `cellResVar b D f ≥ 0` (`cellResVar_nonneg`, Jensen
  `cellAvg_sq_le`) and the Haar components `σ²_ℓ = haarVar (cellAvg f) ℓ ≥ 0`.
* `mixLaw_scrambledPoint_pair_eq` (**pair law of real scrambled points**, item (iii)): the joint
  law of two scrambled points depends only on the common-digit counts of their coordinates.
* `variance_scrambledLaw` (**Owen's variance formula**):
  `Var(μ̂) = n⁻¹ (σ²_{>D} + Σ_{ℓ ≠ 0} Γ_ℓ σ²_ℓ)` for any digit points, `Γ_ℓ = gainCoeff b d ℓ`.
* `variance_scrambledLaw_le` (**never much worse than MC**, Owen 1997): for a `(0,m,s)`-net with
  `s ≤ b + 1`, `Var(μ̂) ≤ (b/(b-1))^{s-1} σ²/n`; `variance_scrambledLaw_le_exp_one`: `≤ e σ²/n`
  when `s ≤ b` (`pow_div_sub_one_le_exp_one`).
* Tools: `integral_mixLaw`, `isProbabilityMeasure_mixLaw`, `memLp_id_mixLaw`,
  `isProbabilityMeasure_remLaw`, `memLp_comp_cellPoint`, `memLp_scrambledEstimate`.

The `o(1/n)` statement is in `ScrambleAsymptotic`; the CLT in `LohCLT`.

**Reading.** Variances are those of the law `scrambledLaw f d` on `ℝ` (`Var[fun x ↦ x; ·]`); `f`
is measurable and in `L²(U[0,1)^s)`; the digit points have `D` digits (`D = m` for a net of
`b^m` points). The bound is stated for `t = 0`, the case of the post's claim (Loh 2003).
-/

namespace RQMCMarkov.OwenScrambling

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

variable {b D : ℕ}

/-- The real point of an `s`-dimensional digit point `y` with remainders `u`. -/
noncomputable def cellPoint {s : ℕ} (y : Fin s → Fin D → Fin b) (u : Fin s → ℝ) : Fin s → ℝ :=
  fun j ↦ digitPoint (y j) (u j)

/-- A scrambled point is the cell point of the scrambled digit point. -/
theorem scrambledPoint_eq_cellPoint {s : ℕ} (ρ : Fin s → Scramble b D)
    (c : Fin s → Fin D → Fin b) (u : Fin s → ℝ) :
    scrambledPoint ρ c u = cellPoint (scrambleVec ρ c) u := rfl

/-- Measurability of a cell point in its remainders. -/
theorem measurable_cellPoint {s : ℕ} (y : Fin s → Fin D → Fin b) : Measurable (cellPoint y) :=
  measurable_pi_iff.2 fun j ↦ (measurable_digitPoint _).comp (measurable_pi_apply j)

/-- **Pair law of scrambled points depends only on the common digits** (Owen 1997, item (iii),
real points): if the digit points `(c, c')` and `(e, e')` have the same numbers of common leading
digits in every coordinate, then the scrambled pairs `(X, X')` (independent uniform scrambles,
independent `U[0,1)^s` remainders `u, v`) have the same joint law. -/
theorem mixLaw_scrambledPoint_pair_eq (hb : 1 < b) {s : ℕ} {c c' e e' : Fin s → Fin D → Fin b}
    (hk : ∀ j, commonPrefix (c j) (c' j) = commonPrefix (e j) (e' j)) :
    mixLaw ((uniformCube s).prod (uniformCube s))
      (fun (ρ : Fin s → Scramble b D) uv ↦
        (scrambledPoint ρ c uv.1, scrambledPoint ρ c' uv.2)) =
    mixLaw ((uniformCube s).prod (uniformCube s))
      (fun (ρ : Fin s → Scramble b D) uv ↦
        (scrambledPoint ρ e uv.1, scrambledPoint ρ e' uv.2)) := by
  set G : (Fin s → Fin D → Fin b) × (Fin s → Fin D → Fin b) →
      Measure ((Fin s → ℝ) × (Fin s → ℝ)) := fun p ↦ ((uniformCube s).prod (uniformCube s)).map
      (fun uv ↦ (cellPoint p.1 uv.1, cellPoint p.2 uv.2)) with hG
  have hsum : ∀ x x' : Fin s → Fin D → Fin b,
      ∑ ρ : Fin s → Scramble b D, ((uniformCube s).prod (uniformCube s)).map
        (fun uv ↦ (scrambledPoint ρ x uv.1, scrambledPoint ρ x' uv.2)) =
      ∑ p, (Finset.univ.filter fun ρ : Fin s → Scramble b D ↦
        scrambleVec ρ x = p.1 ∧ scrambleVec ρ x' = p.2).card • G p := by
    intro x x'
    rw [← Finset.sum_fiberwise Finset.univ (fun ρ ↦ (scrambleVec ρ x, scrambleVec ρ x'))
      (fun ρ ↦ ((uniformCube s).prod (uniformCube s)).map
        (fun uv ↦ (scrambledPoint ρ x uv.1, scrambledPoint ρ x' uv.2)))]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [Finset.sum_congr rfl fun ρ hρ ↦ by
      obtain ⟨e1, e2⟩ := Prod.mk.inj (Finset.mem_filter.1 hρ).2
      change ((uniformCube s).prod (uniformCube s)).map
        (fun uv ↦ (cellPoint (scrambleVec ρ x) uv.1, cellPoint (scrambleVec ρ x') uv.2)) = G p
      rw [e1, e2], Finset.sum_const]
    congr 1
    exact congrArg Finset.card (Finset.filter_congr fun ρ _ ↦ Prod.ext_iff)
  have hcard : ∀ p : (Fin s → Fin D → Fin b) × (Fin s → Fin D → Fin b),
      (Finset.univ.filter fun ρ : Fin s → Scramble b D ↦
        scrambleVec ρ c = p.1 ∧ scrambleVec ρ c' = p.2).card =
      (Finset.univ.filter fun ρ : Fin s → Scramble b D ↦
        scrambleVec ρ e = p.1 ∧ scrambleVec ρ e' = p.2).card := by
    intro p
    have h1 := card_scrambleVec_pair hb c c' p.1 p.2
    have h2 := card_scrambleVec_pair hb e e' p.1 p.2
    simp only [hk] at h1
    exact_mod_cast h1.trans h2.symm
  unfold mixLaw
  rw [hsum c c', hsum e e']
  simp only [hcard]

/-- The cells `[cellVal x / b^D, (cellVal x + 1)/b^D)` tile `[0,1)`:
`Σ_x U[0,1).map (digitPoint x) = b^D • U[0,1)`. -/
theorem sum_map_digitPoint (hb : 0 < b) :
    ∑ x : Fin D → Fin b, uniformIco.map (digitPoint x) = ((b ^ D : ℕ) : ℝ≥0∞) • uniformIco := by
  have hbD : b ^ D ≠ 0 := (Nat.pow_pos hb).ne'
  have h1 : ∑ y : Fin D → Fin b, uniformIco.map (digitPoint y) =
      ∑ i : Fin (b ^ D), uniformIco.map (stratumMap (b ^ D) i) := by
    rw [← (cellFin_bijective (D := D) hb).sum_comp
      (fun i : Fin (b ^ D) ↦ uniformIco.map (stratumMap (b ^ D) i))]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    congr 1
    funext u
    rw [digitPoint_eq_stratumMap]
    rfl
  rw [h1, sum_map_stratumMap hbD]

/-- The cells of the digit grid tile `[0,1)^s`:
`Σ_y U[0,1)^s.map (cellPoint y) = b^{sD} • U[0,1)^s`. -/
theorem sum_map_cellPoint (hb : 0 < b) (s : ℕ) :
    ∑ y : Fin s → Fin D → Fin b, (uniformCube s).map (cellPoint y) =
      (((b ^ D) ^ s : ℕ) : ℝ≥0∞) • uniformCube s := by
  have := isProbabilityMeasure_uniformIco
  have hmap : ∀ y : Fin s → Fin D → Fin b, (uniformCube s).map (cellPoint y) =
      Measure.pi fun j ↦ uniformIco.map (digitPoint (y j)) := fun y ↦
    Measure.pi_map_pi (fun j ↦ (measurable_digitPoint _).aemeasurable)
  simp only [hmap]
  have hpi : uniformCube s = ((((b ^ D) ^ s : ℕ) : ℝ≥0∞))⁻¹ •
      ∑ y : Fin s → Fin D → Fin b, Measure.pi fun j ↦ uniformIco.map (digitPoint (y j)) := by
    refine Measure.pi_eq fun S hS ↦ ?_
    rw [Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl (fun y _ ↦ Measure.pi_pi _ _)]
    rw [← Fintype.prod_sum (fun j (x : Fin D → Fin b) ↦ uniformIco.map (digitPoint x) (S j))]
    have h2 : ∀ j, ∑ x : Fin D → Fin b, uniformIco.map (digitPoint x) (S j) =
        ((b ^ D : ℕ) : ℝ≥0∞) * uniformIco (S j) := by
      intro j
      rw [← Measure.finsetSum_apply, sum_map_digitPoint hb, Measure.smul_apply, smul_eq_mul]
    rw [Finset.prod_congr rfl (fun j _ ↦ h2 j), Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, ← mul_assoc, Nat.cast_pow, ENNReal.inv_mul_cancel,
      one_mul]
    · exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Nat.pow_pos hb).ne')
    · exact ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  rw [hpi, smul_smul, ENNReal.mul_inv_cancel, one_smul]
  · exact Nat.cast_ne_zero.2 (pow_ne_zero _ (Nat.pow_pos hb).ne')
  · exact ENNReal.natCast_ne_top _

/-- The law of one cell point is dominated by `b^{sD} • U[0,1)^s`. -/
theorem map_cellPoint_le (hb : 0 < b) {s : ℕ} (y : Fin s → Fin D → Fin b) :
    (uniformCube s).map (cellPoint y) ≤ (((b ^ D) ^ s : ℕ) : ℝ≥0∞) • uniformCube s := by
  rw [← sum_map_cellPoint hb s]
  exact Finset.single_le_sum (f := fun y ↦ (uniformCube s).map (cellPoint y))
    (fun _ _ ↦ Measure.zero_le _) (Finset.mem_univ y)

/-- `g ∈ L^p(U[0,1)^s)` restricted to a cell is in `L^p`. -/
theorem memLp_comp_cellPoint (hb : 0 < b) {s : ℕ} {p : ℝ≥0∞} {g : (Fin s → ℝ) → ℝ}
    (hg : MemLp g p (uniformCube s)) (y : Fin s → Fin D → Fin b) :
    MemLp (fun u ↦ g (cellPoint y u)) p (uniformCube s) := by
  have h1 : MemLp g p ((uniformCube s).map (cellPoint y)) :=
    (hg.smul_measure (ENNReal.natCast_ne_top _)).mono_measure (map_cellPoint_le hb y)
  exact h1.comp_of_map (measurable_cellPoint y).aemeasurable

/-- **Integrating cell by cell**: `Σ_y ∫ g(cellPoint y u) du = b^{sD} ∫ g`. -/
theorem sum_integral_cellPoint (hb : 0 < b) {s : ℕ} {g : (Fin s → ℝ) → ℝ}
    (hg : Integrable g (uniformCube s)) :
    ∑ y : Fin s → Fin D → Fin b, ∫ u, g (cellPoint y u) ∂(uniformCube s) =
      ((b : ℝ) ^ D) ^ s * ∫ x, g x ∂(uniformCube s) := by
  have hgi : ∀ y : Fin s → Fin D → Fin b, Integrable g ((uniformCube s).map (cellPoint y)) :=
    fun y ↦ (hg.smul_measure (ENNReal.natCast_ne_top _)).mono_measure (map_cellPoint_le hb y)
  have e : ∀ y : Fin s → Fin D → Fin b, ∫ u, g (cellPoint y u) ∂(uniformCube s) =
      ∫ x, g x ∂((uniformCube s).map (cellPoint y)) := fun y ↦
    (integral_map (measurable_cellPoint y).aemeasurable (hgi y).aestronglyMeasurable).symm
  rw [Finset.sum_congr rfl fun y _ ↦ e y, ← integral_finsetSum_measure fun y _ ↦ hgi y,
    sum_map_cellPoint hb s, integral_smul_measure, ENNReal.toReal_natCast, smul_eq_mul,
    Nat.cast_pow, Nat.cast_pow]

/-- The law of the remainders: one independent `U[0,1)^s` vector for each of the `n` points. -/
noncomputable abbrev remLaw (s n : ℕ) : Measure (Fin n → Fin s → ℝ) :=
  Measure.pi fun _ : Fin n ↦ uniformCube s

/-- `remLaw s n` is a probability measure. -/
theorem isProbabilityMeasure_remLaw (s n : ℕ) : IsProbabilityMeasure (remLaw s n) := by
  have := isProbabilityMeasure_uniformCube s
  exact Measure.pi.instIsProbabilityMeasure _

/-- The remainder of point `i` is `U[0,1)^s`. -/
theorem measurePreserving_remLaw_eval (s : ℕ) {n : ℕ} (i : Fin n) :
    MeasurePreserving (Function.eval i) (remLaw s n) (uniformCube s) := by
  have := isProbabilityMeasure_uniformCube s
  exact measurePreserving_eval (fun _ : Fin n ↦ uniformCube s) i

/-- `E[g(u_i)] = ∫ g` over the cube. -/
theorem integral_remLaw_eval {s n : ℕ} {g : (Fin s → ℝ) → ℝ}
    (hg : AEStronglyMeasurable g (uniformCube s)) (i : Fin n) :
    ∫ u, g (u i) ∂(remLaw s n) = ∫ x, g x ∂(uniformCube s) := by
  have hmp := measurePreserving_remLaw_eval s i
  rw [← hmp.map_eq] at hg ⊢
  exact (integral_map hmp.measurable.aemeasurable hg).symm

/-- `g ∈ L^p` of the cube gives `u ↦ g(u_i) ∈ L^p` of the remainders. -/
theorem memLp_remLaw_eval {s n : ℕ} {p : ℝ≥0∞} {g : (Fin s → ℝ) → ℝ}
    (hg : MemLp g p (uniformCube s)) (i : Fin n) :
    MemLp (fun u : Fin n → Fin s → ℝ ↦ g (u i)) p (remLaw s n) := by
  have hmp := measurePreserving_remLaw_eval s i
  rw [← hmp.map_eq] at hg
  exact hg.comp_of_map hmp.measurable.aemeasurable

/-- **Independent remainders**: `E[g(u_i) h(u_{i'})] = (∫ g)(∫ h)` for `i ≠ i'`. -/
theorem integral_remLaw_mul {s n : ℕ} {g h : (Fin s → ℝ) → ℝ}
    (hg : AEStronglyMeasurable g (uniformCube s)) (hh : AEStronglyMeasurable h (uniformCube s))
    {i i' : Fin n} (hii : i ≠ i') :
    ∫ u, g (u i) * h (u i') ∂(remLaw s n) =
      (∫ x, g x ∂(uniformCube s)) * ∫ x, h x ∂(uniformCube s) := by
  have := isProbabilityMeasure_uniformCube s
  have hind : iIndepFun (fun (k : Fin n) (u : Fin n → Fin s → ℝ) ↦ u k) (remLaw s n) :=
    iIndepFun_pi (X := fun _ (x : Fin s → ℝ) ↦ x) fun _ ↦ aemeasurable_id
  have hpair := hind.indepFun hii
  have hmi := measurePreserving_remLaw_eval s i
  have hmi' := measurePreserving_remLaw_eval s i'
  have hg' : AEStronglyMeasurable g ((remLaw s n).map (fun u : Fin n → Fin s → ℝ ↦ u i)) := by
    rw [show (fun u : Fin n → Fin s → ℝ ↦ u i) = Function.eval i from rfl, hmi.map_eq]
    exact hg
  have hh' : AEStronglyMeasurable h ((remLaw s n).map (fun u : Fin n → Fin s → ℝ ↦ u i')) := by
    rw [show (fun u : Fin n → Fin s → ℝ ↦ u i') = Function.eval i' from rfl, hmi'.map_eq]
    exact hh
  have h1 := hpair.integral_comp_mul_comp (f := g) (g := h) hmi.measurable.aemeasurable
    hmi'.measurable.aemeasurable hg' hh'
  calc ∫ u, g (u i) * h (u i') ∂(remLaw s n)
      = ∫ u, ((g ∘ fun u : Fin n → Fin s → ℝ ↦ u i) *
          (h ∘ fun u : Fin n → Fin s → ℝ ↦ u i')) u ∂(remLaw s n) := rfl
    _ = (∫ u, (g ∘ fun u : Fin n → Fin s → ℝ ↦ u i) u ∂(remLaw s n)) *
          ∫ u, (h ∘ fun u : Fin n → Fin s → ℝ ↦ u i') u ∂(remLaw s n) := h1
    _ = (∫ x, g x ∂(uniformCube s)) * ∫ x, h x ∂(uniformCube s) := by
        rw [← integral_remLaw_eval hg i, ← integral_remLaw_eval hh i']
        rfl

/-- The **cell average** `F(y) = ∫ f(cellPoint y u) du` of `f` over the cell of `y`. -/
noncomputable def cellAvg {s : ℕ} (f : (Fin s → ℝ) → ℝ) (y : Fin s → Fin D → Fin b) : ℝ :=
  ∫ u, f (cellPoint y u) ∂(uniformCube s)

/-- The **cell mean square** `∫ f(cellPoint y u)² du`. -/
noncomputable def cellSq {s : ℕ} (f : (Fin s → ℝ) → ℝ) (y : Fin s → Fin D → Fin b) : ℝ :=
  ∫ u, f (cellPoint y u) ^ 2 ∂(uniformCube s)

/-- **Jensen in a cell**: `F(y)² ≤ ∫ f(cellPoint y u)² du`. -/
theorem cellAvg_sq_le (hb : 0 < b) {s : ℕ} {f : (Fin s → ℝ) → ℝ}
    (hf : MemLp f 2 (uniformCube s)) (y : Fin s → Fin D → Fin b) :
    cellAvg f y ^ 2 ≤ cellSq f y := by
  have := isProbabilityMeasure_uniformCube s
  have hL := memLp_comp_cellPoint hb hf y
  have hv := variance_nonneg (fun u ↦ f (cellPoint y u)) (uniformCube s)
  rw [variance_eq_sub hL] at hv
  unfold cellAvg cellSq
  have e : ∫ u, ((fun u ↦ f (cellPoint y u)) ^ 2) u ∂(uniformCube s) =
      ∫ u, f (cellPoint y u) ^ 2 ∂(uniformCube s) := rfl
  linarith

/-- The **scrambled-net estimator** `(1/n) Σ_i f(X_i)` with `X_i = scrambledPoint ρ (d i) (u i)`.
-/
noncomputable def scrambledEstimate {s n : ℕ} (f : (Fin s → ℝ) → ℝ)
    (d : Fin n → Fin s → Fin D → Fin b) (ρ : Fin s → Scramble b D)
    (u : Fin n → Fin s → ℝ) : ℝ :=
  sampleMean n f fun i ↦ scrambledPoint ρ (d i) (u i)

/-- The **law of the scrambled-net estimator**: uniform independent nested scrambles in the `s`
coordinates, independent `U[0,1)^s` remainders. -/
noncomputable def scrambledLaw {s n : ℕ} (f : (Fin s → ℝ) → ℝ)
    (d : Fin n → Fin s → Fin D → Fin b) : Measure ℝ :=
  mixLaw (remLaw s n) (scrambledEstimate f d)

/-- The estimator for a fixed scramble is in `L²` of the remainders. -/
theorem memLp_scrambledEstimate (hb : 0 < b) {s n : ℕ} {f : (Fin s → ℝ) → ℝ}
    (hf : MemLp f 2 (uniformCube s)) (d : Fin n → Fin s → Fin D → Fin b)
    (ρ : Fin s → Scramble b D) : MemLp (scrambledEstimate f d ρ) 2 (remLaw s n) := by
  unfold scrambledEstimate sampleMean
  refine MemLp.const_mul ?_ _
  exact memLp_finsetSum _ fun i _ ↦ memLp_remLaw_eval (memLp_comp_cellPoint hb hf _) i

/-- The estimator for a fixed scramble is measurable when `f` is. -/
theorem measurable_scrambledEstimate {s n : ℕ} {f : (Fin s → ℝ) → ℝ} (hfm : Measurable f)
    (d : Fin n → Fin s → Fin D → Fin b) (ρ : Fin s → Scramble b D) :
    Measurable (scrambledEstimate f d ρ) := by
  unfold scrambledEstimate sampleMean
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ fun i _ ↦ hfm.comp ?_
  exact (measurable_scrambledPoint ρ (d i)).comp (measurable_pi_apply i)

/-- First moment for a fixed scramble: `E_u[μ̂] = (1/n) Σ_i F(σ d_i)`. -/
theorem integral_scrambledEstimate (hb : 0 < b) {s n : ℕ} {f : (Fin s → ℝ) → ℝ}
    (hf : MemLp f 2 (uniformCube s)) (d : Fin n → Fin s → Fin D → Fin b)
    (ρ : Fin s → Scramble b D) :
    ∫ u, scrambledEstimate f d ρ u ∂(remLaw s n) =
      (n : ℝ)⁻¹ * ∑ i, cellAvg f (scrambleVec ρ (d i)) := by
  unfold scrambledEstimate sampleMean
  beta_reduce
  rw [integral_const_mul, integral_finsetSum (f := fun i (u : Fin n → Fin s → ℝ) ↦
    f (scrambledPoint ρ (d i) (u i))) _ fun i _ ↦
    (memLp_remLaw_eval (memLp_comp_cellPoint hb hf _) i).integrable one_le_two]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact integral_remLaw_eval (g := fun v ↦ f (cellPoint (scrambleVec ρ (d i)) v))
    (memLp_comp_cellPoint hb hf _).aestronglyMeasurable i

/-- Second moment for a fixed scramble:
`E_u[μ̂²] = n⁻² (Σ_i (∫_cell f² - F²)(σ d_i) + (Σ_i F(σ d_i))²)`. -/
theorem integral_sq_scrambledEstimate (hb : 0 < b) {s n : ℕ} {f : (Fin s → ℝ) → ℝ}
    (hf : MemLp f 2 (uniformCube s)) (d : Fin n → Fin s → Fin D → Fin b)
    (ρ : Fin s → Scramble b D) :
    ∫ u, scrambledEstimate f d ρ u ^ 2 ∂(remLaw s n) =
      ((n : ℝ)⁻¹) ^ 2 * (∑ i, (cellSq f (scrambleVec ρ (d i)) -
        cellAvg f (scrambleVec ρ (d i)) ^ 2) + (∑ i, cellAvg f (scrambleVec ρ (d i))) ^ 2) := by
  set c : Fin n → Fin s → Fin D → Fin b := fun i ↦ scrambleVec ρ (d i) with hc
  set g : Fin n → (Fin n → Fin s → ℝ) → ℝ := fun i u ↦ f (cellPoint (c i) (u i)) with hg
  have hgL : ∀ i, MemLp (g i) 2 (remLaw s n) := fun i ↦
    memLp_remLaw_eval (memLp_comp_cellPoint hb hf _) i
  have hest : ∀ u, scrambledEstimate f d ρ u ^ 2 =
      ((n : ℝ)⁻¹) ^ 2 * ∑ i, ∑ i', g i u * g i' u := by
    intro u
    unfold scrambledEstimate sampleMean
    rw [mul_pow, sq (∑ i, _), Finset.sum_mul_sum]
    rfl
  have hpair : ∀ i i', ∫ u, g i u * g i' u ∂(remLaw s n) =
      cellAvg f (c i) * cellAvg f (c i') +
        if i = i' then cellSq f (c i) - cellAvg f (c i) ^ 2 else 0 := by
    intro i i'
    by_cases hii : i = i'
    · subst hii
      rw [ite_eq_left rfl]
      have e : ∫ u, g i u * g i u ∂(remLaw s n) = cellSq f (c i) := by
        unfold cellSq
        rw [← integral_remLaw_eval (g := fun v ↦ f (cellPoint (c i) v) ^ 2)
          ((memLp_comp_cellPoint hb hf (c i)).integrable_sq.aestronglyMeasurable) i]
        refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
        simp only [hg]
        ring
      rw [e]
      ring
    · rw [ite_eq_right hii, add_zero]
      exact integral_remLaw_mul (memLp_comp_cellPoint hb hf (c i)).aestronglyMeasurable
        (memLp_comp_cellPoint hb hf (c i')).aestronglyMeasurable hii
  rw [integral_congr_ae (Filter.Eventually.of_forall hest), integral_const_mul,
    integral_finsetSum (f := fun i u ↦ ∑ i', g i u * g i' u) _ fun i _ ↦
      integrable_finsetSum _ fun i' _ ↦ (hgL i).integrable_mul (hgL i')]
  rw [Finset.sum_congr rfl fun i _ ↦ integral_finsetSum (f := fun i' u ↦ g i u * g i' u) _
    fun i' _ ↦ (hgL i).integrable_mul (hgL i')]
  simp only [hpair, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [sq (∑ i, cellAvg f (c i)), Finset.sum_mul_sum]
  ring

/-- Integrals against a mixture law: `∫ g d(mixLaw Q Φ) = (#R)⁻¹ Σ_ρ ∫ g(Φ ρ u) dQ(u)`. -/
theorem integral_mixLaw {R E : Type*} [Fintype R] [MeasurableSpace E] {Q : Measure E}
    {Φ : R → E → ℝ} (hΦ : ∀ ρ, Measurable (Φ ρ)) {g : ℝ → ℝ} (hg : Continuous g)
    (hint : ∀ ρ, Integrable (fun u ↦ g (Φ ρ u)) Q) :
    ∫ x, g x ∂(mixLaw Q Φ) = (Fintype.card R : ℝ)⁻¹ * ∑ ρ, ∫ u, g (Φ ρ u) ∂Q := by
  have hgi : ∀ ρ, Integrable g (Q.map (Φ ρ)) := fun ρ ↦
    (integrable_map_measure hg.aestronglyMeasurable (hΦ ρ).aemeasurable).2 (hint ρ)
  unfold mixLaw
  rw [integral_smul_measure, integral_finsetSum_measure fun ρ _ ↦ hgi ρ, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul]
  congr 1
  exact Finset.sum_congr rfl fun ρ _ ↦ integral_map (hΦ ρ).aemeasurable hg.aestronglyMeasurable

/-- A mixture of probability laws is a probability law. -/
theorem isProbabilityMeasure_mixLaw {R E F : Type*} [Fintype R] [Nonempty R] [MeasurableSpace E]
    [MeasurableSpace F] {Q : Measure E} [IsProbabilityMeasure Q] {Φ : R → E → F}
    (hΦ : ∀ ρ, Measurable (Φ ρ)) : IsProbabilityMeasure (mixLaw Q Φ) := by
  refine ⟨?_⟩
  unfold mixLaw
  rw [Measure.smul_apply, Measure.finsetSum_apply,
    Finset.sum_congr rfl fun ρ _ ↦ by rw [Measure.map_apply (hΦ ρ) MeasurableSet.univ,
      Set.preimage_univ, measure_univ], Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, smul_eq_mul, ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
    (ENNReal.natCast_ne_top _)]

/-- The identity is in `L²` of a mixture of `L²` laws. -/
theorem memLp_id_mixLaw {R E : Type*} [Fintype R] [Nonempty R] [MeasurableSpace E] {Q : Measure E}
    {Φ : R → E → ℝ} (hΦ : ∀ ρ, Measurable (Φ ρ)) (hL : ∀ ρ, MemLp (Φ ρ) 2 Q) :
    MemLp (fun x : ℝ ↦ x) 2 (mixLaw Q Φ) := by
  refine (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 ?_
  unfold mixLaw
  refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 Fintype.card_ne_zero))
  rw [integrable_finsetSum_measure]
  intro ρ _
  exact (integrable_map_measure (continuous_pow 2).aestronglyMeasurable
    (hΦ ρ).aemeasurable).2 (hL ρ).integrable_sq

/-- The number of `s`-dimensional nested scrambles. -/
theorem card_scramble_pi (s : ℕ) :
    (Fintype.card (Fin s → Scramble b D) : ℝ) = (Fintype.card (Scramble b D) : ℝ) ^ s := by
  rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]

/-- **The scrambled-net estimator is unbiased** (Owen 1995): for ANY digit points `d`
(`n ≥ 1`) and every measurable `f ∈ L²(U[0,1)^s)`, `E[μ̂] = ∫ f`. -/
theorem integral_scrambledLaw (hb : 0 < b) {s n : ℕ} (hn : n ≠ 0) {f : (Fin s → ℝ) → ℝ}
    (hfm : Measurable f) (hf : MemLp f 2 (uniformCube s)) (d : Fin n → Fin s → Fin D → Fin b) :
    ∫ x, x ∂(scrambledLaw f d) = ∫ x, f x ∂(uniformCube s) := by
  have hR : (0 : ℝ) < (Fintype.card (Scramble b D) : ℝ) ^ s :=
    pow_pos (Nat.cast_pos.2 Fintype.card_pos) s
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have hbD : (0 : ℝ) < ((b : ℝ) ^ D) ^ s := pow_pos (pow_pos hb' D) s
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  unfold scrambledLaw
  rw [integral_mixLaw (g := fun x ↦ x) (measurable_scrambledEstimate hfm d) continuous_id
    fun ρ ↦ (memLp_scrambledEstimate hb hf d ρ).integrable one_le_two, card_scramble_pi]
  simp only [integral_scrambledEstimate hb hf d]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [sum_scrambleVec hb _ (cellAvg f)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold cellAvg
  rw [sum_integral_cellPoint hb (hf.integrable one_le_two)]
  field_simp

/-- The **within-cell variance** `b^{-sD} Σ_y (∫_cell f² - F(y)²)`: the part of `Var f` at
resolution finer than `D` digits in some coordinate. -/
noncomputable def cellResVar (b D : ℕ) {s : ℕ} (f : (Fin s → ℝ) → ℝ) : ℝ :=
  (∑ y : Fin s → Fin D → Fin b, (cellSq f y - cellAvg f y ^ 2)) / ((b : ℝ) ^ D) ^ s

/-- The within-cell variance is nonnegative. -/
theorem cellResVar_nonneg (hb : 0 < b) {s : ℕ} {f : (Fin s → ℝ) → ℝ}
    (hf : MemLp f 2 (uniformCube s)) : 0 ≤ cellResVar b D f :=
  div_nonneg (Finset.sum_nonneg fun y _ ↦ sub_nonneg.2 (cellAvg_sq_le hb hf y))
    (pow_nonneg (pow_nonneg (Nat.cast_nonneg _) _) _)

/-- **ANOVA–Haar decomposition of the variance** (Owen 1997):
`Var f = σ²_{>D} + Σ_{ℓ ≠ 0} σ²_ℓ`, the within-cell variance plus the base-`b` Haar components
`σ²_ℓ = haarVar F ℓ` of the cell averages `F`. -/
theorem variance_eq_cellResVar_add (hb : 0 < b) {s : ℕ} {f : (Fin s → ℝ) → ℝ}
    (hf : MemLp f 2 (uniformCube s)) :
    Var[f; uniformCube s] = cellResVar b D f +
      ∑ ℓ ∈ (Finset.univ : Finset (Fin s → Fin (D + 1))).erase 0,
        haarVar (cellAvg (b := b) f) ℓ := by
  have := isProbabilityMeasure_uniformCube s
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have hbD : (0 : ℝ) < ((b : ℝ) ^ D) ^ s := pow_pos (pow_pos hb' D) s
  have hsum := sum_haarVar hb (cellAvg f (b := b) (D := D))
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0), haarVar_zero] at hsum
  have h1 : ∑ y : Fin s → Fin D → Fin b, cellSq f y =
      ((b : ℝ) ^ D) ^ s * ∫ x, f x ^ 2 ∂(uniformCube s) :=
    sum_integral_cellPoint hb (g := fun x ↦ f x ^ 2) hf.integrable_sq
  have h2 : ∑ y : Fin s → Fin D → Fin b, cellAvg f y =
      ((b : ℝ) ^ D) ^ s * ∫ x, f x ∂(uniformCube s) :=
    sum_integral_cellPoint hb (hf.integrable one_le_two)
  rw [variance_eq_sub hf]
  unfold cellResVar
  rw [Finset.sum_sub_distrib, sub_div, h1]
  have e : ∑ ℓ ∈ (Finset.univ : Finset (Fin s → Fin (D + 1))).erase 0,
      haarVar (cellAvg (b := b) f) ℓ =
      (∑ y : Fin s → Fin D → Fin b, cellAvg f y ^ 2) / ((b : ℝ) ^ D) ^ s -
        ((∑ y : Fin s → Fin D → Fin b, cellAvg f y) / ((b : ℝ) ^ D) ^ s) ^ 2 := by linarith
  rw [e, h2]
  change ∫ x, f x ^ 2 ∂(uniformCube s) - (∫ x, f x ∂(uniformCube s)) ^ 2 = _
  field_simp
  ring

/-- **Owen's variance formula for scrambled nets** (Owen 1997): for any digit points `d`
(`n ≥ 1`) and measurable `f ∈ L²`,
`Var(μ̂) = n⁻¹ (σ²_{>D} + Σ_{ℓ ≠ 0} Γ_ℓ σ²_ℓ)`, with the gain coefficients `Γ_ℓ` of the point
set and the Haar components `σ²_ℓ` of `f`. -/
theorem variance_scrambledLaw (hb : 1 < b) {s n : ℕ} (hn : n ≠ 0) {f : (Fin s → ℝ) → ℝ}
    (hfm : Measurable f) (hf : MemLp f 2 (uniformCube s)) (d : Fin n → Fin s → Fin D → Fin b) :
    Var[fun x ↦ x; scrambledLaw f d] = (n : ℝ)⁻¹ * (cellResVar b D f +
      ∑ ℓ ∈ (Finset.univ : Finset (Fin s → Fin (D + 1))).erase 0,
        gainCoeff b d ℓ * haarVar (cellAvg (b := b) f) ℓ) := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hR : (0 : ℝ) < (Fintype.card (Scramble b D) : ℝ) ^ s :=
    pow_pos (Nat.cast_pos.2 Fintype.card_pos) s
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb0
  have hbD : (0 : ℝ) < ((b : ℝ) ^ D) ^ s := pow_pos (pow_pos hb' D) s
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hQ := isProbabilityMeasure_remLaw s n
  have hP := isProbabilityMeasure_mixLaw (Q := remLaw s n)
    (measurable_scrambledEstimate hfm d (b := b) (D := D))
  have hmean := integral_scrambledLaw hb0 hn hfm hf d
  have hL := memLp_id_mixLaw (measurable_scrambledEstimate hfm d)
    (memLp_scrambledEstimate hb0 hf d)
  unfold scrambledLaw at hmean hP hL ⊢
  rw [variance_eq_sub hL]
  change ∫ x, x ^ 2 ∂_ - (∫ x, x ∂_) ^ 2 = _
  rw [hmean, integral_mixLaw (g := fun x ↦ x ^ 2) (measurable_scrambledEstimate hfm d)
    (continuous_pow 2) fun ρ ↦ (memLp_scrambledEstimate hb0 hf d ρ).integrable_sq,
    card_scramble_pi]
  simp only [integral_sq_scrambledEstimate hb0 hf d]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_comm]
  simp only [sum_scrambleVec hb0 _ (fun y ↦ cellSq f y - cellAvg f y ^ 2)]
  have hsq := sum_sq_sum_scrambleVec hb d (cellAvg f)
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin s → Fin (D + 1)))
    (fun ℓ ↦ gainCoeff b d ℓ * haarVar (cellAvg (b := b) f) ℓ) (Finset.mem_univ 0)
  rw [gainCoeff_zero hb hn, haarVar_zero] at hsplit
  have h2 : ∑ y : Fin s → Fin D → Fin b, cellAvg f y =
      ((b : ℝ) ^ D) ^ s * ∫ x, f x ∂(uniformCube s) :=
    sum_integral_cellPoint hb0 (hf.integrable one_le_two)
  rw [h2] at hsplit
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold cellResVar
  rw [show (∑ ρ : Fin s → Scramble b D, (∑ i, cellAvg f (scrambleVec ρ (d i))) ^ 2) =
    (Fintype.card (Scramble b D) : ℝ) ^ s *
      (n * ∑ ℓ, gainCoeff b d ℓ * haarVar (cellAvg (b := b) f) ℓ) by
      rw [← hsq]
      field_simp, ← hsplit]
  field_simp
  ring

/-- The ratio `(b/(b-1))^{s-1}` is at most `e` when `s ≤ b`. -/
theorem pow_div_sub_one_le_exp_one (hb : 1 < b) {s : ℕ} (hsb : s ≤ b) :
    ((b : ℝ) / ((b : ℝ) - 1)) ^ (s - 1) ≤ Real.exp 1 := by
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  have ha : (b : ℝ) / ((b : ℝ) - 1) = 1 / ((b : ℝ) - 1) + 1 := by
    field_simp
    ring
  have h1 : (b : ℝ) / ((b : ℝ) - 1) ≤ Real.exp (1 / ((b : ℝ) - 1)) := by
    rw [ha]
    exact Real.add_one_le_exp _
  have h0 : (0 : ℝ) ≤ (b : ℝ) / ((b : ℝ) - 1) := div_nonneg (Nat.cast_nonneg _) hb1.le
  calc ((b : ℝ) / ((b : ℝ) - 1)) ^ (s - 1) ≤ Real.exp (1 / ((b : ℝ) - 1)) ^ (s - 1) :=
        pow_le_pow_left₀ h0 h1 _
    _ = Real.exp (((s - 1 : ℕ) : ℝ) * (1 / ((b : ℝ) - 1))) := by
        rw [← Real.exp_nat_mul]
    _ ≤ Real.exp 1 := by
        refine Real.exp_le_exp.2 ?_
        have hs : ((s - 1 : ℕ) : ℝ) ≤ (b : ℝ) - 1 := by
          have : ((s - 1 : ℕ) : ℝ) ≤ ((b - 1 : ℕ) : ℝ) := Nat.cast_le.2 (by omega)
          rwa [Nat.cast_sub hb.le, Nat.cast_one] at this
        rw [mul_one_div, div_le_one hb1]
        exact hs

/-- **Scrambled `(0,m,s)`-nets never do much worse than Monte Carlo** (Owen 1997,
`s ≤ b + 1`): `Var(μ̂) ≤ (b/(b-1))^{s-1} σ²/n` for every measurable `f ∈ L²`, where
`σ² = Var f` and `σ²/n` is the MC variance. -/
theorem variance_scrambledLaw_le (hb : 1 < b) {m s n : ℕ} {d : Fin n → Fin s → Fin D → Fin b}
    (hmD : m ≤ D) (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) (hsb : s ≤ b + 1)
    {f : (Fin s → ℝ) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (uniformCube s)) :
    Var[fun x ↦ x; scrambledLaw f d] ≤
      ((b : ℝ) / ((b : ℝ) - 1)) ^ (s - 1) * Var[f; uniformCube s] / n := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hn : n ≠ 0 := by
    rw [hnet.2.1]
    exact (Nat.pow_pos hb0).ne'
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  have ha : (1 : ℝ) ≤ ((b : ℝ) / ((b : ℝ) - 1)) ^ (s - 1) := by
    refine one_le_pow₀ ?_
    rw [one_le_div hb1]
    linarith
  rw [variance_scrambledLaw hb hn hfm hf d, variance_eq_cellResVar_add hb0 hf (D := D)]
  set C := ((b : ℝ) / ((b : ℝ) - 1)) ^ (s - 1)
  have hres := cellResVar_nonneg hb0 hf (D := D)
  have hterm : ∀ ℓ ∈ (Finset.univ : Finset (Fin s → Fin (D + 1))).erase 0,
      gainCoeff b d ℓ * haarVar (cellAvg (b := b) f) ℓ ≤ C * haarVar (cellAvg (b := b) f) ℓ := by
    intro ℓ hℓ
    exact mul_le_mul_of_nonneg_right
      (gainCoeff_net_mem_Icc hb hmD hnet hsb (Finset.ne_of_mem_erase hℓ)).2
      (haarVar_nonneg hb0 _ _)
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  have hsum0 : 0 ≤ ∑ ℓ ∈ (Finset.univ : Finset (Fin s → Fin (D + 1))).erase 0,
      haarVar (cellAvg (b := b) f) ℓ := Finset.sum_nonneg fun ℓ _ ↦ haarVar_nonneg hb0 _ _
  rw [inv_mul_eq_div, div_le_div_iff_of_pos_right hn']
  nlinarith

/-- **The `e` bound** (Owen 1997, `s ≤ b`): `Var(μ̂) ≤ e σ²/n` for scrambled `(0,m,s)`-nets,
whatever the (measurable, square integrable) integrand: scrambled nets never lose more than a
factor `e ≈ 2.718` against Monte Carlo. -/
theorem variance_scrambledLaw_le_exp_one (hb : 1 < b) {m s n : ℕ}
    {d : Fin n → Fin s → Fin D → Fin b} (hmD : m ≤ D)
    (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) (hsb : s ≤ b)
    {f : (Fin s → ℝ) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (uniformCube s)) :
    Var[fun x ↦ x; scrambledLaw f d] ≤ Real.exp 1 * Var[f; uniformCube s] / n := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hn : n ≠ 0 := by
    rw [hnet.2.1]
    exact (Nat.pow_pos hb0).ne'
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have := isProbabilityMeasure_uniformCube s
  have hV0 : 0 ≤ Var[f; uniformCube s] := variance_nonneg _ _
  exact (variance_scrambledLaw_le hb hmD hnet (le_trans hsb (Nat.le_succ b)) hfm hf).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (pow_div_sub_one_le_exp_one hb hsb) hV0) hn'.le)

end RQMCMarkov.OwenScrambling

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Scrambled nets are asymptotically better than Monte Carlo: `Var = o(1/n)` (Owen 1997)

Owen (1997): for every `f ∈ L²`, the scrambled `(0,m,s)`-net variance is `o(1/n)`. The proof here
avoids the infinite Haar expansion: the estimator is EXACT for step functions on elementary cubes
of level `R` with `sR ≤ m` (the scrambled net puts `b^{m-sR}` points in each), so it has the same
variance for `f` and `f - g` (`g` such a step function); by Owen's bound this is at most
`C ‖f - g‖²/n`, and step functions are dense in `L²` (`exists_stepFn_approx`).

## Main results

* `card_box_net_of_le`: a `(0,m,s)`-net puts exactly `b^{m-|r|}` points in every box with
  `|r| ≤ m`.
* `stepFn`, `sum_stepFn_scrambledPoint`, `integral_stepFn`, `sampleMean_stepFn_scrambledPoint`:
  scrambled nets integrate level-`R` step functions exactly when `sR ≤ m`, for every scramble.
* `variance_scrambledLaw_eq_sum`, `variance_scrambledLaw_sub_of_exact`: subtracting an exactly
  integrated function leaves the variance unchanged.
* `dist_corner_lt`, `exists_stepFn_approx`: bounded step functions approximate any `f ∈ L²` in
  mean square at every fine enough level (via a bounded continuous approximant, Mathlib's
  `MemLp.exists_boundedContinuous_integral_rpow_sub_le`, and Heine–Cantor on `[0,1]^s`).
* `tendsto_pow_mul_variance_scrambledLaw` (**Owen 1997, `Var = o(1/n)`**): for `(0,m,s)`-nets
  (`1 ≤ s ≤ b + 1`, `m` digits) and every measurable `f ∈ L²`, `n Var(μ̂) → 0`.
-/

namespace RQMCMarkov.OwenScrambling

open MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal Topology

variable {b D : ℕ}

/-- **Box counts of a `(0,m,s)`-net** (`m ≤ D`): every elementary box of levels `r` with
`|r| ≤ m` contains exactly `b^{m - |r|}` points. -/
theorem card_box_net_of_le (hb : 0 < b) {m s n : ℕ} {d : Fin n → Fin s → Fin D → Fin b}
    (hmD : m ≤ D) (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) {r : Fin s → ℕ}
    (hr : ∑ j, r j ≤ m) {a : Fin s → ℕ} (ha : ∀ j, a j < b ^ r j) :
    (Finset.univ.filter fun i' ↦ ∀ j, prefixVal (d i' j) (r j) = a j).card =
      b ^ (m - ∑ j, r j) := by
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    have : (Finset.univ.filter fun i' : Fin n ↦ ∀ j : Fin 0, prefixVal (d i' j) (r j) = a j) =
        Finset.univ := Finset.filter_true_of_mem fun i' _ j ↦ j.elim0
    rw [this, Finset.card_univ, Fintype.card_fin, hnet.2.1, Finset.univ_eq_empty,
      Finset.sum_empty, Nat.sub_zero]
  set j₀ : Fin s := ⟨0, hs⟩
  set e := m - ∑ j, r j with he
  set r' : Fin s → ℕ := Function.update r j₀ (r j₀ + e) with hr'
  have hsplit : ∀ g : Fin s → ℕ, ∑ j, g j = g j₀ + ∑ j ∈ Finset.univ \ {j₀}, g j := fun g ↦ by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀), Finset.sdiff_singleton_eq_erase]
  have hr'sum : ∑ j, r' j = m := by
    rw [hsplit r', hr', Function.update_self]
    have : ∑ j ∈ Finset.univ \ {j₀}, Function.update r j₀ (r j₀ + e) j =
        ∑ j ∈ Finset.univ \ {j₀}, r j := Finset.sum_congr rfl fun j hj ↦
      Function.update_of_ne (Finset.notMem_singleton.1 (Finset.mem_sdiff.1 hj).2) _ _
    rw [this]
    have := hsplit r
    omega
  have hr'D : ∀ j, r' j ≤ D := fun j ↦ le_trans (le_trans
    (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (r' j)) (Finset.mem_univ j)) hr'sum.le) hmD
  set S := Finset.univ.filter fun i' ↦ ∀ j, prefixVal (d i' j) (r j) = a j with hS
  set f : Fin n → ℕ := fun i' ↦ prefixVal (d i' j₀) (r j₀ + e) with hf
  set T := (Finset.range (b ^ r j₀ * b ^ e)).filter fun A ↦ A / b ^ e = a j₀ with hT
  have hdiv : ∀ i' : Fin n, prefixVal (d i' j₀) (r j₀ + e) / b ^ e = prefixVal (d i' j₀) (r j₀) :=
    fun i' ↦ by
      have := prefixVal_div hb (d i' j₀) (Nat.le_add_right (r j₀) e)
      rwa [Nat.add_sub_cancel_left] at this
  have hmaps : (S : Set (Fin n)).MapsTo f T := by
    intro i' hi'
    rw [Finset.mem_coe, hS, Finset.mem_filter] at hi'
    rw [Finset.mem_coe, hT, Finset.mem_filter, Finset.mem_range, ← pow_add, hf]
    refine ⟨prefixVal_lt hb _ _, ?_⟩
    rw [hdiv i']
    exact hi'.2 j₀
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ A ∈ T, (S.filter fun i' ↦ f i' = A).card = 1 := by
    intro A hA
    rw [hT, Finset.mem_filter, Finset.mem_range] at hA
    have h := hnet.2.2.2 r' (Function.update a j₀ A)
      (by rw [hr'sum, Nat.sub_zero]) (by
        intro j
        by_cases hj : j = j₀
        · subst hj
          rw [Function.update_self, hr', Function.update_self, pow_add]
          exact hA.1
        · rw [Function.update_of_ne hj, hr', Function.update_of_ne hj]
          exact ha j)
    rw [pow_zero] at h
    rw [← h, hS, Finset.filter_filter]
    congr 1
    refine Finset.filter_congr fun i' _ ↦ ?_
    rw [boxIndex_digitPoint hb hr'D, funext_iff]
    constructor
    · rintro ⟨hag, hfA⟩ j
      by_cases hj : j = j₀
      · subst hj
        rw [Function.update_self, hr', Function.update_self]
        exact hfA
      · rw [Function.update_of_ne hj, hr', Function.update_of_ne hj]
        exact hag j
    · intro hall
      have h0 := hall j₀
      rw [Function.update_self, hr', Function.update_self] at h0
      refine ⟨fun j ↦ ?_, h0⟩
      by_cases hj : j = j₀
      · subst hj
        rw [← hdiv i', h0, hA.2]
      · have hj' := hall j
        rw [Function.update_of_ne hj, hr', Function.update_of_ne hj] at hj'
        exact hj'
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_one, hT,
    card_filter_range_div (Nat.pow_pos hb) (ha j₀)]

/-- A **step function on the level-`R` elementary cubes**: `x ↦ G(⌊b^R x⌋)`. -/
noncomputable def stepFn (b R : ℕ) {s : ℕ} (G : (Fin s → ℕ) → ℝ) (x : Fin s → ℝ) : ℝ :=
  G (boxIndex b (fun _ ↦ R) x)

/-- Step functions are measurable. -/
theorem measurable_stepFn (b R : ℕ) {s : ℕ} (G : (Fin s → ℕ) → ℝ) : Measurable (stepFn b R G) := by
  have h : Measurable (boxIndex b (fun _ : Fin s ↦ R)) :=
    measurable_pi_iff.2 fun j ↦ ((measurable_pi_apply j).const_mul _).nat_floor
  exact (measurable_of_countable G).comp h

/-- A step function with bounded values is in `L^p` of the cube. -/
theorem memLp_stepFn (b R : ℕ) {s : ℕ} {G : (Fin s → ℕ) → ℝ} {M : ℝ} (hG : ∀ a, |G a| ≤ M)
    (p : ℝ≥0∞) : MemLp (stepFn b R G) p (uniformCube s) := by
  have := isProbabilityMeasure_uniformCube s
  exact MemLp.of_bound (measurable_stepFn b R G).aestronglyMeasurable M
    (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hG _)

/-- The level-`R` box index of a scrambled point is the vector of scrambled prefix values. -/
theorem boxIndex_scrambledPoint (hb : 0 < b) {s R : ℕ} (hRD : R ≤ D) (ρ : Fin s → Scramble b D)
    (c : Fin s → Fin D → Fin b) {u : Fin s → ℝ} (hu : ∀ j, u j ∈ Set.Ico (0 : ℝ) 1) :
    boxIndex b (fun _ ↦ R) (scrambledPoint ρ c u) = fun j ↦ prefixVal (scramble (ρ j) (c j)) R :=
  funext fun j ↦ floor_pow_mul_digitPoint hb _ (hu j) hRD

/-- **Scrambled `(0,m,s)`-nets sum step functions exactly** (levels `R` with `sR ≤ m`): every
level-`R` cube holds `b^{m - sR}` scrambled points, for every scramble and remainders. -/
theorem sum_stepFn_scrambledPoint (hb : 0 < b) {m s n R : ℕ} {d : Fin n → Fin s → Fin D → Fin b}
    (hmD : m ≤ D) (hRD : R ≤ D) (hsR : s * R ≤ m)
    (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    (G : (Fin s → ℕ) → ℝ) (ρ : Fin s → Scramble b D) {u : Fin n → Fin s → ℝ}
    (hu : ∀ i j, u i j ∈ Set.Ico (0 : ℝ) 1) :
    ∑ i, stepFn b R G (scrambledPoint ρ (d i) (u i)) =
      (b : ℝ) ^ (m - s * R) *
        ∑ a ∈ Fintype.piFinset fun _ : Fin s ↦ Finset.range (b ^ R), G a := by
  have hnet' : IsNet b 0 m fun i j ↦ digitPoint (scramble (ρ j) (d i j)) 0 :=
    isNet_scrambledPoint hb (by omega) hnet ρ (u := fun _ _ ↦ 0)
      (fun _ _ ↦ ⟨le_rfl, one_pos⟩)
  set key : Fin n → Fin s → ℕ := fun i j ↦ prefixVal (scramble (ρ j) (d i j)) R with hkey
  have hstep : ∀ i, stepFn b R G (scrambledPoint ρ (d i) (u i)) = G (key i) := fun i ↦ by
    unfold stepFn
    rw [boxIndex_scrambledPoint hb hRD ρ (d i) (hu i)]
  set T := Fintype.piFinset fun _ : Fin s ↦ Finset.range (b ^ R) with hT
  have hmaps : ∀ i ∈ (Finset.univ : Finset (Fin n)), key i ∈ T := by
    intro i _
    rw [hT, Fintype.mem_piFinset]
    exact fun j ↦ Finset.mem_range.2 (prefixVal_lt hb _ _)
  rw [Finset.sum_congr rfl fun i _ ↦ hstep i,
    ← Finset.sum_fiberwise_of_maps_to hmaps (fun i ↦ G (key i)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  rw [hT, Fintype.mem_piFinset] at ha
  have hcard : (Finset.univ.filter fun i ↦ key i = a).card = b ^ (m - s * R) := by
    have hsum : ∑ _j : Fin s, R = s * R := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have h := card_box_net_of_le hb hmD hnet' (r := fun _ ↦ R) (by rw [hsum]; exact hsR)
      (a := a) (fun j ↦ Finset.mem_range.1 (ha j))
    rw [hsum] at h
    rw [← h]
    congr 1
    exact Finset.filter_congr fun i _ ↦ funext_iff
  rw [Finset.sum_congr rfl fun i hi ↦ by rw [(Finset.mem_filter.1 hi).2], Finset.sum_const,
    hcard, nsmul_eq_mul, Nat.cast_pow]

/-- Points of `U[0,1)^s` lie in `[0,1)^s` almost surely. -/
theorem ae_mem_cube_uniformCube (s : ℕ) :
    ∀ᵐ u ∂(uniformCube s), ∀ j, u j ∈ Set.Ico (0 : ℝ) 1 := by
  rw [ae_all_iff]
  intro j
  have hmp : MeasurePreserving (Function.eval j) (uniformCube s) uniformIco := by
    have := isProbabilityMeasure_uniformIco
    exact measurePreserving_eval (fun _ : Fin s ↦ uniformIco) j
  have h0 : ∀ᵐ v ∂uniformIco, v ∈ Set.Ico (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ico
  rw [← hmp.map_eq] at h0
  exact ae_of_ae_map hmp.measurable.aemeasurable h0

/-- **The integral of a step function**: `∫ G(⌊b^R x⌋) dx = b^{-sR} Σ_a G(a)`. -/
theorem integral_stepFn (hb : 0 < b) {s : ℕ} (R : ℕ) {G : (Fin s → ℕ) → ℝ} {M : ℝ}
    (hG : ∀ a, |G a| ≤ M) :
    ∫ x, stepFn b R G x ∂(uniformCube s) =
      (∑ a ∈ Fintype.piFinset fun _ : Fin s ↦ Finset.range (b ^ R), G a) / ((b : ℝ) ^ R) ^ s := by
  have := isProbabilityMeasure_uniformCube s
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have hbR : (0 : ℝ) < ((b : ℝ) ^ R) ^ s := pow_pos (pow_pos hb' R) s
  have h := sum_integral_cellPoint (D := R) hb ((memLp_stepFn b R hG 1).integrable le_rfl)
  have hcube := ae_mem_cube_uniformCube s
  have hcell : ∀ y : Fin s → Fin R → Fin b,
      ∫ u, stepFn b R G (cellPoint y u) ∂(uniformCube s) = G fun j ↦ cellVal (y j) := by
    intro y
    rw [integral_congr_ae (g := fun _ ↦ G fun j ↦ cellVal (y j)) ?_, integral_const,
      probReal_univ, one_smul]
    filter_upwards [hcube] with u hu
    unfold stepFn
    congr 1
    funext j
    exact floor_pow_mul_digitPoint hb (y j) (hu j) le_rfl
  rw [Finset.sum_congr rfl fun y _ ↦ hcell y] at h
  have hbij : ∑ y : Fin s → Fin R → Fin b, G (fun j ↦ cellVal (y j)) =
      ∑ a ∈ Fintype.piFinset fun _ : Fin s ↦ Finset.range (b ^ R), G a := by
    refine Finset.sum_bij (fun y _ ↦ fun j ↦ cellVal (y j)) ?_ ?_ ?_ ?_
    · intro y _
      rw [Fintype.mem_piFinset]
      exact fun j ↦ Finset.mem_range.2 (cellVal_lt hb _)
    · intro y _ y' _ hyy
      funext j
      exact cellVal_injective hb (congrFun hyy j)
    · intro a ha
      rw [Fintype.mem_piFinset] at ha
      have hex : ∀ j, ∃ x : Fin R → Fin b, cellVal x = a j := fun j ↦ by
        obtain ⟨x, hx⟩ := (cellFin_bijective (D := R) hb).2 ⟨a j, Finset.mem_range.1 (ha j)⟩
        exact ⟨x, congrArg Fin.val hx⟩
      choose y hy using hex
      exact ⟨y, Finset.mem_univ _, funext hy⟩
    · intro y _
      rfl
  rw [hbij] at h
  rw [h]
  field_simp

/-- The remainders lie in the cube almost surely. -/
theorem ae_mem_cube_remLaw (s n : ℕ) :
    ∀ᵐ u ∂(remLaw s n), ∀ i j, u i j ∈ Set.Ico (0 : ℝ) 1 := by
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  have := isProbabilityMeasure_uniformIco
  have hmp : MeasurePreserving (fun u : Fin n → Fin s → ℝ ↦ u i j) (remLaw s n) uniformIco :=
    (measurePreserving_eval (fun _ : Fin s ↦ uniformIco) j).comp
      (measurePreserving_remLaw_eval s i)
  have h0 : ∀ᵐ v ∂uniformIco, v ∈ Set.Ico (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ico
  rw [← hmp.map_eq] at h0
  exact ae_of_ae_map hmp.measurable.aemeasurable h0

/-- **Exactness of the scrambled-net estimator for step functions**: for a scrambled
`(0,m,s)`-net and a bounded step function at level `R` with `sR ≤ m`, the estimator equals the
integral, for every scramble and all remainders in `[0,1)`. -/
theorem sampleMean_stepFn_scrambledPoint (hb : 0 < b) {m s R : ℕ}
    {d : Fin (b ^ m) → Fin s → Fin D → Fin b} (hmD : m ≤ D) (hRD : R ≤ D) (hsR : s * R ≤ m)
    (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) {G : (Fin s → ℕ) → ℝ} {M : ℝ}
    (hG : ∀ a, |G a| ≤ M) (ρ : Fin s → Scramble b D) {u : Fin (b ^ m) → Fin s → ℝ}
    (hu : ∀ i j, u i j ∈ Set.Ico (0 : ℝ) 1) :
    sampleMean (b ^ m) (stepFn b R G) (fun i ↦ scrambledPoint ρ (d i) (u i)) =
      ∫ x, stepFn b R G x ∂(uniformCube s) := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  unfold sampleMean
  rw [sum_stepFn_scrambledPoint hb hmD hRD hsR hnet G ρ hu, integral_stepFn hb R hG]
  have hpow : (b : ℝ) ^ (m - s * R) * ((b : ℝ) ^ R) ^ s = (b : ℝ) ^ m := by
    rw [← pow_mul, ← pow_add, mul_comm R s, Nat.sub_add_cancel hsR]
  have hbR : (0 : ℝ) < ((b : ℝ) ^ R) ^ s := pow_pos (pow_pos hb' R) s
  rw [Nat.cast_pow, ← hpow]
  field_simp

/-- The variance of the scrambled estimator as an average of mean squared errors. -/
theorem variance_scrambledLaw_eq_sum (hb : 0 < b) {s n : ℕ} (hn : n ≠ 0)
    {f : (Fin s → ℝ) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (uniformCube s))
    (d : Fin n → Fin s → Fin D → Fin b) :
    Var[fun x ↦ x; scrambledLaw f d] = (Fintype.card (Fin s → Scramble b D) : ℝ)⁻¹ *
      ∑ ρ, ∫ u, (scrambledEstimate f d ρ u - ∫ x, f x ∂(uniformCube s)) ^ 2 ∂(remLaw s n) := by
  rw [variance_eq_integral (X := fun x : ℝ ↦ x) aemeasurable_id]
  change ∫ x, (x - ∫ y, y ∂(scrambledLaw f d)) ^ 2 ∂(scrambledLaw f d) = _
  rw [integral_scrambledLaw hb hn hfm hf d]
  unfold scrambledLaw
  exact integral_mixLaw (g := fun x ↦ (x - ∫ x, f x ∂(uniformCube s)) ^ 2)
    (measurable_scrambledEstimate hfm d) ((continuous_id.sub continuous_const).pow 2)
    fun ρ ↦ ((memLp_scrambledEstimate hb hf d ρ).sub (memLp_const _)).integrable_sq

/-- **Subtracting an exactly integrated function does not change the variance**: if the
estimator of `g` equals `∫ g` for every scramble and all remainders in `[0,1)`, then the
scrambled estimators of `f` and `f - g` have the same variance. -/
theorem variance_scrambledLaw_sub_of_exact (hb : 0 < b) {s n : ℕ} (hn : n ≠ 0)
    {f g : (Fin s → ℝ) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (uniformCube s))
    (hgm : Measurable g) (hg : MemLp g 2 (uniformCube s)) (d : Fin n → Fin s → Fin D → Fin b)
    (hex : ∀ (ρ : Fin s → Scramble b D) (u : Fin n → Fin s → ℝ),
      (∀ i j, u i j ∈ Set.Ico (0 : ℝ) 1) →
      sampleMean n g (fun i ↦ scrambledPoint ρ (d i) (u i)) = ∫ x, g x ∂(uniformCube s)) :
    Var[fun x ↦ x; scrambledLaw f d] = Var[fun x ↦ x; scrambledLaw (f - g) d] := by
  rw [variance_scrambledLaw_eq_sum hb hn hfm hf d,
    variance_scrambledLaw_eq_sum hb hn (hfm.sub hgm) (hf.sub hg) d]
  congr 1
  refine Finset.sum_congr rfl fun ρ _ ↦ integral_congr_ae ?_
  filter_upwards [ae_mem_cube_remLaw s n] with u hu
  have hsplit : scrambledEstimate f d ρ u =
      scrambledEstimate (f - g) d ρ u + sampleMean n g (fun i ↦ scrambledPoint ρ (d i) (u i)) := by
    unfold scrambledEstimate sampleMean
    simp only [Pi.sub_apply, Finset.sum_sub_distrib]
    ring
  have hint : ∫ x, (f - g) x ∂(uniformCube s) =
      ∫ x, f x ∂(uniformCube s) - ∫ x, g x ∂(uniformCube s) :=
    integral_sub (hf.integrable one_le_two) (hg.integrable one_le_two)
  rw [hsplit, hex ρ u hu, hint]
  ring

/-- A point of `[0,1)^s` is within `b^{-R}` (sup distance) of the corner of its level-`R` cube,
and both lie in `[0,1]^s`. -/
theorem dist_corner_lt (hb : 1 < b) {s : ℕ} (R : ℕ) {x : Fin s → ℝ}
    (hx : ∀ j, x j ∈ Set.Ico (0 : ℝ) 1) {δ : ℝ} (hδ : (1 / (b : ℝ)) ^ R < δ) :
    dist x (fun j ↦ (boxIndex b (fun _ ↦ R) x j : ℝ) / (b : ℝ) ^ R) < δ ∧
      (fun j ↦ (boxIndex b (fun _ ↦ R) x j : ℝ) / (b : ℝ) ^ R) ∈
        Set.pi Set.univ fun _ ↦ Set.Icc (0 : ℝ) 1 := by
  have hb' : (0 : ℝ) < b := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  have hbR : (0 : ℝ) < (b : ℝ) ^ R := pow_pos hb' R
  have hδ0 : 0 < δ := lt_of_le_of_lt (pow_nonneg (by positivity) R) hδ
  have hc : ∀ j, (boxIndex b (fun _ ↦ R) x j : ℝ) / (b : ℝ) ^ R ≤ x j ∧
      x j < (boxIndex b (fun _ ↦ R) x j : ℝ) / (b : ℝ) ^ R + 1 / (b : ℝ) ^ R := by
    intro j
    unfold boxIndex
    have h0 : 0 ≤ (b : ℝ) ^ R * x j := mul_nonneg hbR.le (hx j).1
    have h1 := Nat.floor_le h0
    have h2 := Nat.lt_floor_add_one ((b : ℝ) ^ R * x j)
    constructor
    · rw [div_le_iff₀ hbR]
      linarith
    · rw [← add_div, lt_div_iff₀ hbR]
      linarith
  refine ⟨(dist_pi_lt_iff hδ0).2 fun j ↦ ?_, fun j _ ↦ ⟨?_, ?_⟩⟩
  · rw [Real.dist_eq, abs_of_nonneg (by linarith [(hc j).1])]
    have : 1 / (b : ℝ) ^ R = (1 / (b : ℝ)) ^ R := by rw [one_div_pow]
    linarith [(hc j).2]
  · exact div_nonneg (Nat.cast_nonneg _) hbR.le
  · linarith [(hc j).1, (hx j).2]

/-- **Step functions are dense in `L²` of the cube**: every `f ∈ L²` is approximated in mean
square, to any `ε > 0`, by bounded step functions at every sufficiently fine level `R`. -/
theorem exists_stepFn_approx (hb : 1 < b) {s : ℕ} {f : (Fin s → ℝ) → ℝ}
    (hf : MemLp f 2 (uniformCube s)) {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℕ, ∀ R ≥ R₀, ∃ (G : (Fin s → ℕ) → ℝ) (M : ℝ), (∀ a, |G a| ≤ M) ∧
      ∫ x, (f x - stepFn b R G x) ^ 2 ∂(uniformCube s) ≤ ε := by
  have := isProbabilityMeasure_uniformCube s
  have hb' : (0 : ℝ) < b := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  have hf' : MemLp f (ENNReal.ofReal 2) (uniformCube s) := by
    rw [ENNReal.ofReal_ofNat]
    exact hf
  obtain ⟨h, hfh, hhL⟩ := hf'.exists_boundedContinuous_integral_rpow_sub_le two_pos
    (ε := ε / 4) (by positivity)
  rw [ENNReal.ofReal_ofNat] at hhL
  have hfh' : ∫ x, (f x - h x) ^ 2 ∂(uniformCube s) ≤ ε / 4 := by
    refine le_trans (le_of_eq (integral_congr_ae (Eventually.of_forall fun x ↦ ?_))) hfh
    simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs]
  set K : Set (Fin s → ℝ) := Set.pi Set.univ fun _ ↦ Set.Icc (0 : ℝ) 1 with hK
  have hKc : IsCompact K := isCompact_univ_pi fun _ ↦ isCompact_Icc
  have huc := hKc.uniformContinuousOn_of_continuous h.continuous.continuousOn
  obtain ⟨δ, hδ, hδh⟩ := Metric.uniformContinuousOn_iff.1 huc (Real.sqrt (ε / 4))
    (Real.sqrt_pos.2 (by positivity))
  obtain ⟨R₀, hR₀⟩ := exists_pow_lt_of_lt_one hδ
    (show 1 / (b : ℝ) < 1 by rw [div_lt_one hb']; exact Nat.one_lt_cast.2 hb)
  refine ⟨R₀, fun R hR ↦ ⟨fun a ↦ h fun j ↦ (a j : ℝ) / (b : ℝ) ^ R, ‖h‖,
    fun a ↦ by rw [← Real.norm_eq_abs]; exact h.norm_coe_le_norm _, ?_⟩⟩
  have hRδ : (1 / (b : ℝ)) ^ R < δ := lt_of_le_of_lt
    (pow_le_pow_of_le_one (by positivity) (by rw [div_le_one hb']; exact (Nat.one_lt_cast.2 hb).le)
      hR) hR₀
  set g := stepFn b R fun a ↦ h fun j ↦ (a j : ℝ) / (b : ℝ) ^ R with hg
  have hgL : MemLp g 2 (uniformCube s) :=
    memLp_stepFn b R (M := ‖h‖) (fun a ↦ by rw [← Real.norm_eq_abs]; exact h.norm_coe_le_norm _) 2
  have hcube := ae_mem_cube_uniformCube s
  have hpt : ∀ᵐ x ∂(uniformCube s), (h x - g x) ^ 2 ≤ ε / 4 := by
    filter_upwards [hcube] with x hx
    obtain ⟨hd, hcK⟩ := dist_corner_lt hb R hx hRδ
    have hxK : x ∈ K := fun j _ ↦ ⟨(hx j).1, (hx j).2.le⟩
    have := hδh x hxK _ hcK hd
    rw [Real.dist_eq] at this
    have h2 : (h x - g x) ^ 2 ≤ Real.sqrt (ε / 4) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) this.le 2
    rwa [Real.sq_sqrt (by positivity)] at h2
  have hfhL := hf.sub hhL
  have hhgL := hhL.sub hgL
  calc ∫ x, (f x - g x) ^ 2 ∂(uniformCube s)
      ≤ ∫ x, (2 * (f x - h x) ^ 2 + 2 * (h x - g x) ^ 2) ∂(uniformCube s) := by
        refine integral_mono (hf.sub hgL).integrable_sq ?_ fun x ↦ ?_
        · exact (hfhL.integrable_sq.const_mul 2).add (hhgL.integrable_sq.const_mul 2)
        · nlinarith [sq_nonneg (f x - h x - (h x - g x))]
    _ = 2 * ∫ x, (f x - h x) ^ 2 ∂(uniformCube s) + 2 * ∫ x, (h x - g x) ^ 2 ∂(uniformCube s) := by
        have i1 : Integrable (fun x ↦ 2 * (f x - h x) ^ 2) (uniformCube s) :=
          hfhL.integrable_sq.const_mul 2
        have i2 : Integrable (fun x ↦ 2 * (h x - g x) ^ 2) (uniformCube s) :=
          hhgL.integrable_sq.const_mul 2
        rw [integral_add i1 i2, integral_const_mul, integral_const_mul]
    _ ≤ 2 * (ε / 4) + 2 * (ε / 4) := by
        have h3 : ∫ x, (h x - g x) ^ 2 ∂(uniformCube s) ≤ ε / 4 := by
          calc ∫ x, (h x - g x) ^ 2 ∂(uniformCube s) ≤ ∫ _x, ε / 4 ∂(uniformCube s) :=
                integral_mono_ae hhgL.integrable_sq (integrable_const _) hpt
            _ = ε / 4 := by rw [integral_const, probReal_univ, one_smul]
        linarith
    _ = ε := by ring

/-- **Scrambled `(0,m,s)`-nets are asymptotically better than Monte Carlo** (Owen 1997):
for a sequence of `(0,m,s)`-nets in base `b ≥ s - 1` (with `m` digits) and every measurable
`f ∈ L²`, `n Var(μ̂) → 0` as `m → ∞` (`n = b^m`), i.e. `Var(μ̂) = o(1/n)`. -/
theorem tendsto_pow_mul_variance_scrambledLaw (hb : 1 < b) {s : ℕ} (hs : 1 ≤ s)
    (hsb : s ≤ b + 1)
    (d : (m : ℕ) → Fin (b ^ m) → Fin s → Fin m → Fin b)
    (hnet : ∀ m, IsNet b 0 m fun i j ↦ digitPoint (d m i j) 0)
    {f : (Fin s → ℝ) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (uniformCube s)) :
    Tendsto (fun m ↦ (b : ℝ) ^ m * Var[fun x ↦ x; scrambledLaw f (d m)]) atTop (𝓝 0) := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb0
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  have hU := isProbabilityMeasure_uniformCube s
  set C : ℝ := ((b : ℝ) / ((b : ℝ) - 1)) ^ (s - 1) with hC
  have hC1 : 1 ≤ C := by
    refine one_le_pow₀ ?_
    rw [one_le_div hb1]
    linarith
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨R₀, hR₀⟩ := exists_stepFn_approx hb hf (ε := ε / (2 * C)) (by positivity)
  refine ⟨s * R₀, fun m hm ↦ ?_⟩
  set R := m / s with hRdef
  have hRR₀ : R₀ ≤ R := (Nat.le_div_iff_mul_le hs).2 (by rw [mul_comm]; exact hm)
  have hsR : s * R ≤ m := Nat.mul_div_le m s
  have hRm : R ≤ m := Nat.div_le_self m s
  obtain ⟨G, M, hG, hint⟩ := hR₀ R hRR₀
  set g := stepFn b R G with hg
  have hgm : Measurable g := measurable_stepFn b R G
  have hgL : MemLp g 2 (uniformCube s) := memLp_stepFn b R hG 2
  have hn : b ^ m ≠ 0 := (Nat.pow_pos hb0).ne'
  have hvar := variance_scrambledLaw_sub_of_exact hb0 hn hfm hf hgm hgL (d m)
    fun ρ u hu ↦ sampleMean_stepFn_scrambledPoint hb0 le_rfl hRm hsR (hnet m) hG ρ hu
  have hle := variance_scrambledLaw_le hb le_rfl (hnet m) hsb (hfm.sub hgm) (hf.sub hgL)
  have hVfg : Var[f - g; uniformCube s] ≤ ε / (2 * C) := by
    refine le_trans (variance_le_expectation_sq (hfm.sub hgm).aestronglyMeasurable) ?_
    exact le_trans (le_of_eq rfl) hint
  have hV0 : 0 ≤ Var[fun x ↦ x; scrambledLaw f (d m)] := variance_nonneg _ _
  have hbm : (0 : ℝ) < (b : ℝ) ^ m := pow_pos hb' m
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hbm.le hV0), hvar]
  rw [Nat.cast_pow] at hle
  calc (b : ℝ) ^ m * Var[fun x ↦ x; scrambledLaw (f - g) (d m)]
      ≤ (b : ℝ) ^ m * (C * Var[f - g; uniformCube s] / (b : ℝ) ^ m) :=
        mul_le_mul_of_nonneg_left hle hbm.le
    _ = C * Var[f - g; uniformCube s] := by field_simp
    _ ≤ C * (ε / (2 * C)) := mul_le_mul_of_nonneg_left hVfg (by linarith)
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

end RQMCMarkov.OwenScrambling

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The two-dimensional Hammersley net is a `(0,m,2)`-net in every base

To show the hypotheses of the scrambled-net theorems can be met in more than one dimension: the
Hammersley point set `{(i/b^m, φ_b(i)) : i < b^m}`, with `φ_b` the radical inverse (digits
reversed), is a `(0,m,2)`-net in base `b` for every `b ≥ 2` and `m` (Niederreiter 1992).

## Main results

* `revDigits`, `cellEnum`, `hammersleyDigits`: the net as digit points.
* `eq_of_agree_of_agree_rev`: `r₀` leading digits of `w` and `r₁` leading digits of its reversal,
  `r₀ + r₁ = m`, determine `w`.
* `isNet_hammersley`: the Hammersley net is a `(0,m,2)`-net in base `b`.
-/

namespace RQMCMarkov.OwenScrambling

open Finset

variable {b : ℕ}

/-- The digit string read backwards. -/
def revDigits {m : ℕ} (w : Fin m → Fin b) : Fin m → Fin b := fun k ↦ w (Fin.rev k)

/-- The enumeration of the `m`-digit strings by their cell index `0, …, b^m - 1`. -/
noncomputable def cellEnum (hb : 0 < b) (m : ℕ) : Fin (b ^ m) ≃ (Fin m → Fin b) :=
  (Equiv.ofBijective (cellFin (D := m) hb) (cellFin_bijective hb)).symm

/-- The **Hammersley net** in base `b` with `b^m` points: point `i` has the digits of `i/b^m` in
coordinate `0` and the same digits reversed in coordinate `1` (the radical inverse). -/
noncomputable def hammersleyDigits (hb : 0 < b) (m : ℕ) : Fin (b ^ m) → Fin 2 → Fin m → Fin b :=
  fun i ↦ ![cellEnum hb m i, revDigits (cellEnum hb m i)]

/-- A string is determined by its first `r₀` digits and the first `r₁` digits of its reversal
when `r₀ + r₁ = m`. -/
theorem eq_of_agree_of_agree_rev {m r₀ r₁ : ℕ} (hr : r₀ + r₁ = m) {w w' : Fin m → Fin b}
    (h₀ : Agree r₀ w w') (h₁ : Agree r₁ (revDigits w) (revDigits w')) : w = w' := by
  funext k
  by_cases hk : (k : ℕ) < r₀
  · exact h₀ k hk
  · have hrev : ((Fin.rev k : Fin m) : ℕ) < r₁ := by
      rw [Fin.val_rev]
      omega
    have := h₁ (Fin.rev k) hrev
    simp only [revDigits, Fin.rev_rev] at this
    exact this

/-- **The Hammersley net is a `(0,m,2)`-net in base `b`** (every `b ≥ 2`): each elementary box
of volume `b^{-m}` contains exactly one point. -/
theorem isNet_hammersley (hb : 1 < b) (m : ℕ) :
    IsNet b 0 m fun i j ↦ digitPoint (hammersleyDigits (lt_trans Nat.zero_lt_one hb) m i j) 0 := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  refine ⟨Nat.zero_le m, rfl, fun i j ↦ digitPoint_mem_Ico hb0 _ ⟨le_rfl, one_pos⟩, ?_⟩
  intro r a hr ha
  rw [Nat.sub_zero, Fin.sum_univ_two] at hr
  have hrD : ∀ j, r j ≤ m := by
    intro j
    fin_cases j
    · exact le_trans (Nat.le_add_right _ _) hr.le
    · exact le_trans (Nat.le_add_left _ _) hr.le
  rw [pow_zero]
  set Φ : (Fin m → Fin b) → Fin (b ^ r 0) × Fin (b ^ r 1) := fun w ↦
    (⟨prefixVal w (r 0), prefixVal_lt hb0 _ _⟩,
      ⟨prefixVal (revDigits w) (r 1), prefixVal_lt hb0 _ _⟩) with hΦ
  have hinj : Function.Injective Φ := by
    intro w w' h
    simp only [hΦ, Prod.mk.injEq, Fin.mk.injEq] at h
    exact eq_of_agree_of_agree_rev hr ((prefixVal_eq_iff_agree hb0 (hrD 0) _ _).1 h.1)
      ((prefixVal_eq_iff_agree hb0 (hrD 1) _ _).1 h.2)
  have hbij : Function.Bijective Φ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod]
    rw [← pow_add, hr]
  obtain ⟨w₀, hw₀⟩ := hbij.2 (⟨a 0, ha 0⟩, ⟨a 1, ha 1⟩)
  have hiff : ∀ i, boxIndex b r (fun j ↦ digitPoint (hammersleyDigits hb0 m i j) 0) = a ↔
      cellEnum hb0 m i = w₀ := by
    intro i
    rw [boxIndex_digitPoint hb0 hrD, funext_iff, Fin.forall_fin_two]
    simp only [hammersleyDigits, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    constructor
    · rintro ⟨h0, h1⟩
      refine hinj (hw₀.symm ▸ ?_)
      simp only [hΦ, Prod.mk.injEq, Fin.mk.injEq]
      exact ⟨h0, h1⟩
    · rintro rfl
      have := congrArg (fun p ↦ ((p.1 : ℕ), (p.2 : ℕ))) hw₀
      simp only [hΦ, Prod.mk.injEq] at this
      exact this
  rw [Finset.filter_congr fun i _ ↦ hiff i, Finset.card_eq_one]
  refine ⟨(cellEnum hb0 m).symm w₀, ?_⟩
  ext i
  rw [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨-, h⟩
    rw [← h, Equiv.symm_apply_apply]
  · rintro rfl
    exact ⟨Finset.mem_univ _, Equiv.apply_symm_apply _ _⟩

end RQMCMarkov.OwenScrambling

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Stratified sampling: variance at most MC, `O(n^{-3})` and `O(n^{-2})` rates (post #2)

Copied from `RQMCMarkov/PointSets` (namespace and imports renamed); see that project for
its documentation.

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

namespace RQMCMarkov.OwenScrambling

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

end RQMCMarkov.OwenScrambling

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Owen's nested uniform scramble in one dimension is stratified sampling (post #2)

Post #2: "a more powerful but more computationally costly randomization for digital nets is
'Owen Scrambling' which is a 'nested uniform scramble'" (Owen 1995, 1997). In one dimension and
base `b`, the `(0,m,1)`-net is `{k/bᵐ : k < bᵐ}`, one point in each `b`-adic cell
`[k/bᵐ, (k+1)/bᵐ)`.

**The scramble.** A point's first `m` base-`b` digits form a word `w : Fin m → Fin b` (most
significant digit first; `digitEquiv` identifies words with cells `k < bᵐ`, and
`digitEquiv_symm_apply_val` shows that digit `j` of the cell `k` is `⌊k / b^(m-1-j)⌋ mod b`, the
`(j+1)`-th base-`b` digit of `k/bᵐ`). An *Owen tree* `T : OwenTree b m` gives one permutation of
`Fin b` for each node, a level `j < m` together with a prefix of `j` digits. The scrambled word is
`owenWord T w j = T j (w₀ … w_{j-1}) (w j)`: digit `j` is permuted by the permutation attached to
the digits before it (`wordPrefix`). Owen's scramble takes all node permutations independent and
uniform, i.e. `T` uniform on the finite set `OwenTree b m`. Below the `m`-th digit the net points
have digits `0`; distinct cells sit below distinct nodes, so their lower digits are scrambled by
disjoint sets of independent uniform permutations and form independent uniform remainders. We
take this as the definition at depth `m` (`Owen1DDeep` proves it is exact: the genuine scramble
to any depth `M ≥ m` has the same law, `hasLaw_deepNetSorted`): the scrambled net is
`owenNet T r k = (owenCell T k + r k)/bᵐ`, with remainders `r k` i.i.d. `U[0,1)` independent of
`T`, where `owenCell T` is the induced permutation of the cells.

## Main results

* `DigitWord`, `wordPrefix`, `OwenTree`, `owenWord`, `digitEquiv` (`digitEquiv_apply_val`,
  `digitEquiv_symm_apply_val`), `owenCell`, `owenNet`, `owenNetSorted`, `owenRemainder`,
  `stratPoints`, `stratifiedLaw`: the definitions above.
* `wordPrefix_owenWord_eq`: the scramble is *nested*: the first `j` scrambled digits depend only on
  the first `j` digits (points in one `b`-adic interval of length `b^{-j}` go to one interval).
* `owenWord_injective`, `owenWordEquiv`, `owenCell`: for every tree the scramble permutes the words,
  hence the cells.
* `swapTree`, `card_filter_owenWord_eq`, `card_filter_owenWord`, `card_filter_owenCell`:
  `bᵐ · #{T | owenCell T k = j} = #OwenTree`: under a uniform tree each net point lands in each
  cell with probability `b^{-m}`.
* `owenNet_mem_stratum`, `owenNetSorted_apply`: exactly one scrambled point in each cell; relabelled
  by its cell, the point in cell `j` is `(j + r(σ⁻¹ j))/bᵐ`.
* `hasLaw_owenRemainder`, `owenNetSorted_eq_stratPoints`: the relabelled remainders
  `j ↦ R(σ_T⁻¹ j)` are again i.i.d. `U[0,1)`, and the relabelled net is their stratified point set.
* `hasLaw_owenNet` (requirement (i) of posts #1-#2): every scrambled point is `U[0,1)`.
* `hasLaw_owenNetSorted` (the key fact): the scrambled net, relabelled by cell, has EXACTLY the law
  `stratifiedLaw (bᵐ)` of independent stratified sampling, one independent uniform point in each
  cell. (This part uses only that the scramble permutes the cells independently of the
  remainders.)
* Tools: `measurePreserving_comp_perm` (relabelling preserves `U[0,1)ⁿ`),
  `measure_preimage_comp_of_indepFun` (mixing over an independent finite label),
  `measurable_comp_of_countable`, `sum_measure_preimage_singleton_eq_one`,
  `measure_preimage_singleton_of_uniform`, `hasLaw_apply_of_hasLaw_uniformCube`,
  `hasLaw_eval_uniformCube`, `iIndepFun_eval_uniformCube`, `measurable_sampleMean`,
  `sampleMean_owenNet` (relabelling leaves the estimator unchanged).
* `map_sampleMean_owenNet`, `identDistrib_sampleMean_owenNet`: hence the scrambled-net estimator
  has the law of the independent-stratified estimator of `Stratified`;
  `integral_sampleMean_owenNet` (unbiased), `variance_sampleMean_owenNet` (`Var = n⁻² Σᵢ Var(f |
  cell i)`), `variance_sampleMean_owenNet_le_mc` (never worse than MC) and
  `variance_sampleMean_owenNet_le_lipschitz` (`K²/(12 n³)` for `K`-Lipschitz `f`, `n = bᵐ`).

**Reading.** "Nested uniform scramble" is read at depth `m` with independent uniform remainders, as
above; this is exact in law for the net (whose points have distinct `m`-digit prefixes), not for
general point sets (`Owen1DDeep`).
-/

namespace RQMCMarkov.OwenScrambling

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

/-- A base-`b` word of length `m`: the first `m` base-`b` digits of a point, most significant
first. -/
abbrev DigitWord (b m : ℕ) : Type := Fin m → Fin b

/-- The first `j` digits `w₀, …, w_{j-1}` of a word. -/
def wordPrefix {b m : ℕ} (w : DigitWord b m) (j : Fin m) : Fin j → Fin b :=
  fun i ↦ w ⟨i, i.2.trans j.2⟩

/-- An Owen scrambling tree of depth `m`: a permutation of the digits `Fin b` for each node, i.e.
for each level `j < m` and each prefix of `j` digits. -/
abbrev OwenTree (b m : ℕ) : Type := (j : Fin m) → (Fin j → Fin b) → Equiv.Perm (Fin b)

/-- **Owen's nested scramble of a word**: digit `j` is permuted by the permutation of the node
given by the `j` digits before it, `owenWord T w j = T j (w₀ … w_{j-1}) (w j)`. -/
def owenWord {b m : ℕ} (T : OwenTree b m) (w : DigitWord b m) : DigitWord b m :=
  fun j ↦ T j (wordPrefix w j) (w j)

/-- **The scramble is nested**: the first `j` scrambled digits depend only on the first `j`
digits. -/
theorem wordPrefix_owenWord_eq {b m : ℕ} (T : OwenTree b m) {w w' : DigitWord b m} (j : Fin m)
    (h : wordPrefix w j = wordPrefix w' j) :
    wordPrefix (owenWord T w) j = wordPrefix (owenWord T w') j := by
  funext i
  have hi : ∀ i' : Fin m, (i' : ℕ) < j → w i' = w' i' := fun i' hi' ↦
    congrFun h ⟨i', hi'⟩
  have hp : wordPrefix w ⟨i, i.2.trans j.2⟩ = wordPrefix w' ⟨i, i.2.trans j.2⟩ := by
    funext l
    exact hi _ (l.2.trans i.2)
  change T _ (wordPrefix w _) (w _) = T _ (wordPrefix w' _) (w' _)
  rw [hp, hi _ i.2]

/-- **The scramble is injective** on words, for every tree. -/
theorem owenWord_injective {b m : ℕ} (T : OwenTree b m) : Function.Injective (owenWord T) := by
  intro w w' h
  have key : ∀ k : ℕ, ∀ i : Fin m, (i : ℕ) < k → w i = w' i := by
    intro k
    induction k with
    | zero => exact fun i hi ↦ absurd hi (Nat.not_lt_zero _)
    | succ k ih =>
        intro i hi
        have hp : wordPrefix w i = wordPrefix w' i := by
          funext l
          exact ih _ (lt_of_lt_of_le l.2 (Nat.lt_succ_iff.1 hi))
        have hi' := congrFun h i
        change T i (wordPrefix w i) (w i) = T i (wordPrefix w' i) (w' i) at hi'
        rw [hp] at hi'
        exact (T i (wordPrefix w' i)).injective hi'
  funext i
  exact key _ i (Nat.lt_succ_self _)

/-- The scramble as a permutation of the words. -/
noncomputable def owenWordEquiv {b m : ℕ} (T : OwenTree b m) : Equiv.Perm (DigitWord b m) :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.1 (owenWord_injective T))

/-- Words of length `m` are the cells `k < bᵐ`: digit `j` has weight `b^(m-1-j)`. -/
def digitEquiv (b m : ℕ) : DigitWord b m ≃ Fin (b ^ m) :=
  (Equiv.arrowCongr Fin.revPerm (Equiv.refl _)).trans finFunctionFinEquiv

/-- The cell of a word: `Σⱼ wⱼ b^(m-1-j)`. -/
theorem digitEquiv_apply_val (b m : ℕ) (w : DigitWord b m) :
    (digitEquiv b m w : ℕ) = ∑ j : Fin m, (w j : ℕ) * b ^ (m - (j + 1)) := by
  change (finFunctionFinEquiv (fun i ↦ w (Fin.revPerm.symm i)) : ℕ) = _
  rw [finFunctionFinEquiv_apply]
  refine Fintype.sum_equiv Fin.revPerm _ _ (fun i ↦ ?_)
  have h1 : Fin.revPerm.symm i = Fin.revPerm i := rfl
  rw [h1]
  change (w (Fin.rev i) : ℕ) * b ^ (i : ℕ) = (w (Fin.rev i) : ℕ) * b ^ (m - ((Fin.rev i : ℕ) + 1))
  rw [Fin.val_rev]
  congr 2
  omega

/-- **The digits of a cell**: digit `j` (most significant first) of the cell `k < bᵐ` is
`⌊k / b^(m-1-j)⌋ mod b`, the `(j+1)`-th base-`b` digit of the net point `k/bᵐ`. -/
theorem digitEquiv_symm_apply_val (b m : ℕ) (k : Fin (b ^ m)) (j : Fin m) :
    ((digitEquiv b m).symm k j : ℕ) = k / b ^ (m - (j + 1)) % b := by
  change (finFunctionFinEquiv.symm k (Fin.revPerm j) : ℕ) = _
  rw [finFunctionFinEquiv_symm_apply_val]
  rfl

/-- **The scrambled cell**: the permutation `σ_T` of the cells `k < bᵐ` induced by the scramble,
`σ_T k = digitEquiv (owenWord T (digits of k))`. -/
noncomputable def owenCell {b m : ℕ} (T : OwenTree b m) : Equiv.Perm (Fin (b ^ m)) :=
  ((digitEquiv b m).symm.trans (owenWordEquiv T)).trans (digitEquiv b m)

/-- `σ_T k` is the cell of the scrambled digits of `k`. -/
theorem owenCell_apply {b m : ℕ} (T : OwenTree b m) (k : Fin (b ^ m)) :
    owenCell T k = digitEquiv b m (owenWord T ((digitEquiv b m).symm k)) := rfl

/-- The tree that composes the permutations along the path of `w` with the transpositions
`(v j  v' j)`; it maps the trees scrambling `w` to `v` onto those scrambling `w` to `v'`. -/
def swapTree {b m : ℕ} (w v v' : DigitWord b m) (T : OwenTree b m) : OwenTree b m :=
  fun j p ↦ if p = wordPrefix w j then Equiv.swap (v j) (v' j) * T j p else T j p

/-- `swapTree` is an involution. -/
theorem swapTree_swapTree {b m : ℕ} (w v v' : DigitWord b m) (T : OwenTree b m) :
    swapTree w v v' (swapTree w v v' T) = T := by
  funext j p
  by_cases h : p = wordPrefix w j
  · simp only [swapTree, h, ite_true]
    exact Equiv.swap_mul_self_mul _ _ _
  · simp only [swapTree, h, ite_false]

/-- `swapTree` swaps the scrambled digits of `w`. -/
theorem owenWord_swapTree {b m : ℕ} (w v v' : DigitWord b m) (T : OwenTree b m) (j : Fin m) :
    owenWord (swapTree w v v' T) w j = Equiv.swap (v j) (v' j) (owenWord T w j) := by
  simp only [owenWord, swapTree, ite_true]
  rfl

/-- `swapTree` maps the trees with `owenWord T w = v` to those with `owenWord T w = v'`. -/
theorem owenWord_swapTree_eq_iff {b m : ℕ} (w v v' : DigitWord b m) (T : OwenTree b m) :
    owenWord (swapTree w v v' T) w = v' ↔ owenWord T w = v := by
  constructor
  · intro h
    funext j
    have hj := congrFun h j
    rw [owenWord_swapTree, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at hj
    exact hj
  · intro h
    funext j
    rw [owenWord_swapTree, h, Equiv.swap_apply_left]

/-- **All scrambled words are equally likely**: the number of trees scrambling `w` to `v` does not
depend on `v`. -/
theorem card_filter_owenWord_eq {b m : ℕ} (w v v' : DigitWord b m) :
    (Finset.univ.filter fun T : OwenTree b m ↦ owenWord T w = v).card =
      (Finset.univ.filter fun T : OwenTree b m ↦ owenWord T w = v').card := by
  refine Finset.card_nbij' (swapTree w v v') (swapTree w v v') (fun T hT ↦ ?_) (fun T hT ↦ ?_)
    (fun T _ ↦ swapTree_swapTree w v v' T) (fun T _ ↦ swapTree_swapTree w v v' T)
  · rw [Finset.mem_coe, Finset.mem_filter] at hT ⊢
    exact ⟨Finset.mem_univ _, (owenWord_swapTree_eq_iff w v v' T).2 hT.2⟩
  · rw [Finset.mem_coe, Finset.mem_filter] at hT ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← owenWord_swapTree_eq_iff w v v', swapTree_swapTree]
    exact hT.2

/-- `bᵐ` times the number of trees scrambling `w` to `v` is the number of trees. -/
theorem card_filter_owenWord {b m : ℕ} (w v : DigitWord b m) :
    b ^ m * (Finset.univ.filter fun T : OwenTree b m ↦ owenWord T w = v).card =
      Fintype.card (OwenTree b m) := by
  have h := Finset.card_eq_sum_card_fiberwise (f := fun T : OwenTree b m ↦ owenWord T w)
    (s := Finset.univ) (t := Finset.univ) (fun _ _ ↦ Finset.mem_univ _)
  rw [Finset.card_univ] at h
  rw [h, Finset.sum_congr rfl (fun v' _ ↦ card_filter_owenWord_eq w v' v), Finset.sum_const,
    Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, smul_eq_mul]

/-- **Each net point lands in each cell equally often**: `bᵐ · #{T | σ_T k = j} = #OwenTree`. -/
theorem card_filter_owenCell {b m : ℕ} (k j : Fin (b ^ m)) :
    b ^ m * (Finset.univ.filter fun T : OwenTree b m ↦ owenCell T k = j).card =
      Fintype.card (OwenTree b m) := by
  have hfilt : (Finset.univ.filter fun T : OwenTree b m ↦ owenCell T k = j) =
      Finset.univ.filter fun T : OwenTree b m ↦
        owenWord T ((digitEquiv b m).symm k) = (digitEquiv b m).symm j := by
    refine Finset.filter_congr (fun T _ ↦ ?_)
    rw [owenCell_apply, ← Equiv.eq_symm_apply]
  rw [hfilt, card_filter_owenWord]

/-- The scrambled net with remainders `r`: the point of cell `k` goes to
`(σ_T k + r k)/bᵐ`. -/
noncomputable def owenNet {b m : ℕ} (T : OwenTree b m) (r : Fin (b ^ m) → ℝ) :
    Fin (b ^ m) → ℝ :=
  fun k ↦ stratumMap (b ^ m) (owenCell T k) (r k)

/-- The scrambled point of net point `k` lies in the scrambled cell `σ_T k`. -/
theorem owenNet_mem_stratum {b m : ℕ} (hb : b ≠ 0) (T : OwenTree b m) {r : Fin (b ^ m) → ℝ}
    (k : Fin (b ^ m)) (hr : r k ∈ Ico (0 : ℝ) 1) :
    owenNet T r k ∈ stratum (b ^ m) (owenCell T k) := by
  have h := stratumMap_preimage_stratum (pow_ne_zero m hb) (owenCell T k)
  have hmem : r k ∈ stratumMap (b ^ m) (owenCell T k) ⁻¹' stratum (b ^ m) (owenCell T k) := by
    rw [h]
    exact hr
  exact hmem

/-- The scrambled net relabelled by cell: the point lying in cell `j`. -/
noncomputable def owenNetSorted {b m : ℕ} (T : OwenTree b m) (r : Fin (b ^ m) → ℝ) :
    Fin (b ^ m) → ℝ :=
  fun j ↦ owenNet T r ((owenCell T).symm j)

/-- The point in cell `j` is `(j + r(σ_T⁻¹ j))/bᵐ`. -/
theorem owenNetSorted_apply {b m : ℕ} (T : OwenTree b m) (r : Fin (b ^ m) → ℝ)
    (j : Fin (b ^ m)) :
    owenNetSorted T r j = stratumMap (b ^ m) j (r ((owenCell T).symm j)) := by
  simp only [owenNetSorted, owenNet, Equiv.apply_symm_apply]

/-- The stratified points `(i + vᵢ)/n` of `v : Fin n → ℝ`. -/
noncomputable def stratPoints (n : ℕ) (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ stratumMap n i (v i)

/-- `stratPoints n` is measurable. -/
theorem measurable_stratPoints (n : ℕ) : Measurable (stratPoints n) :=
  Measurable.of_eval fun (i : Fin n) ↦ (measurable_stratumMap n i).comp (measurable_pi_apply i)

/-- **The law of independent stratified sampling**: one independent uniform point `(i + Vᵢ)/n`
in each cell, `V ~ U[0,1)ⁿ`. -/
noncomputable def stratifiedLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  (uniformCube n).map (stratPoints n)

/-- Relabelling by a permutation preserves the uniform law on `[0,1)ⁿ`. -/
theorem measurePreserving_comp_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun (r : Fin n → ℝ) j ↦ r (σ.symm j)) (uniformCube n) (uniformCube n) := by
  have := isProbabilityMeasure_uniformIco
  have h := measurePreserving_piCongrLeft (fun _ : Fin n ↦ uniformIco) σ
  have hfun : (fun (r : Fin n → ℝ) j ↦ r (σ.symm j)) =
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) σ) := by
    funext r j
    rw [MeasurableEquiv.coe_piCongrLeft]
    conv_rhs => rw [← σ.apply_symm_apply j]
    rw [Equiv.piCongrLeft_apply_apply]
  rw [hfun]
  exact h

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Mixing over a finite independent label.** If `T` takes values in a finite discrete space and
is independent of `R`, then `P(G(T, R) ∈ A) = Σₜ P(T = t) · P(G(t, R) ∈ A)`. -/
theorem measure_preimage_comp_of_indepFun {τ E F : Type*} [Fintype τ] {mτ : MeasurableSpace τ}
    [DiscreteMeasurableSpace τ] {mE : MeasurableSpace E} [MeasurableSpace F]
    {P : Measure Ω} {T : Ω → τ} {R : Ω → E} (hT : Measurable T) (hR : Measurable R)
    (hind : IndepFun T R P) {G : τ → E → F} (hG : ∀ t, Measurable (G t)) {A : Set F}
    (hA : MeasurableSet A) :
    P ((fun ω ↦ G (T ω) (R ω)) ⁻¹' A) = ∑ t, P (T ⁻¹' {t}) * P.map R (G t ⁻¹' A) := by
  have hset : (fun ω ↦ G (T ω) (R ω)) ⁻¹' A = ⋃ t, (T ⁻¹' {t} ∩ R ⁻¹' (G t ⁻¹' A)) := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_singleton_iff]
    exact ⟨fun h ↦ ⟨T ω, rfl, h⟩, fun ⟨t, ht, h⟩ ↦ ht ▸ h⟩
  have hmeas : ∀ t, MeasurableSet (T ⁻¹' {t} ∩ R ⁻¹' (G t ⁻¹' A)) := fun t ↦
    (hT (measurableSet_singleton t)).inter (hR ((hG t) hA))
  have hdisj : Pairwise (Function.onFun Disjoint fun t ↦ T ⁻¹' {t} ∩ R ⁻¹' (G t ⁻¹' A)) := by
    intro t t' htt'
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2
    exact htt' (h1.1.symm.trans h2.1)
  rw [hset, measure_iUnion hdisj hmeas, tsum_fintype]
  refine Finset.sum_congr rfl (fun t _ ↦ ?_)
  rw [hind.measure_inter_preimage_eq_mul _ _ (measurableSet_singleton t) ((hG t) hA),
    Measure.map_apply hR ((hG t) hA)]

/-- `ω ↦ G(T ω, R ω)` is measurable when `T` takes values in a countable discrete space. -/
theorem measurable_comp_of_countable {τ E F : Type*} [Countable τ] {mτ : MeasurableSpace τ}
    [DiscreteMeasurableSpace τ] {mE : MeasurableSpace E} [MeasurableSpace F]
    {T : Ω → τ} {R : Ω → E} (hT : Measurable T) (hR : Measurable R) {G : τ → E → F}
    (hG : ∀ t, Measurable (G t)) : Measurable fun ω ↦ G (T ω) (R ω) :=
  (measurable_from_prod_countable_right (f := fun p : τ × E ↦ G p.1 p.2) hG).comp
    (hT.prodMk hR)

/-- With a finite discrete label, the fibre probabilities sum to one. -/
theorem sum_measure_preimage_singleton_eq_one {τ : Type*} [Fintype τ] {mτ : MeasurableSpace τ}
    [DiscreteMeasurableSpace τ] {P : Measure Ω} [IsProbabilityMeasure P] {T : Ω → τ}
    (hT : Measurable T) : ∑ t, P (T ⁻¹' {t}) = 1 := by
  rw [sum_measure_preimage_singleton Finset.univ (fun t _ ↦ hT (measurableSet_singleton t)),
    Finset.coe_univ, preimage_univ, measure_univ]

variable {b m : ℕ} {mT : MeasurableSpace (OwenTree b m)} [DiscreteMeasurableSpace (OwenTree b m)]

/-- **The key fact: the Owen-scrambled net is independent stratified sampling.** Let the tree `T`
(any law) be independent of the remainders `R ~ U[0,1)^(bᵐ)`. Relabelled by cell, the scrambled
net `{(σ_T k + R k)/bᵐ}` has exactly the law `stratifiedLaw (bᵐ)`: one independent uniform point in
each cell `[j/bᵐ, (j+1)/bᵐ)`. -/
theorem hasLaw_owenNetSorted {P : Measure Ω} [IsProbabilityMeasure P] {T : Ω → OwenTree b m}
    {R : Ω → Fin (b ^ m) → ℝ} (hT : Measurable T) (hR : Measurable R)
    (hRlaw : HasLaw R (uniformCube (b ^ m)) P) (hind : IndepFun T R P) :
    HasLaw (fun ω ↦ owenNetSorted (T ω) (R ω)) (stratifiedLaw (b ^ m)) P := by
  have hG : ∀ t : OwenTree b m, owenNetSorted t =
      stratPoints (b ^ m) ∘ (fun (r : Fin (b ^ m) → ℝ) j ↦ r ((owenCell t).symm j)) := by
    intro t
    funext r j
    rw [owenNetSorted_apply]
    rfl
  have hGm : ∀ t : OwenTree b m, Measurable (owenNetSorted t) := fun t ↦ by
    rw [hG t]
    exact (measurable_stratPoints _).comp (measurePreserving_comp_perm (owenCell t)).measurable
  have hGlaw : ∀ t : OwenTree b m, (uniformCube (b ^ m)).map (owenNetSorted t) =
      stratifiedLaw (b ^ m) := by
    intro t
    rw [hG t, ← Measure.map_map (measurable_stratPoints _)
      (measurePreserving_comp_perm (owenCell t)).measurable,
      (measurePreserving_comp_perm (owenCell t)).map_eq]
    rfl
  refine ⟨(measurable_comp_of_countable hT hR hGm).aemeasurable, ?_⟩
  ext A hA
  have hA' : ∀ t : OwenTree b m, uniformCube (b ^ m) (owenNetSorted t ⁻¹' A) =
      stratifiedLaw (b ^ m) A := fun t ↦ by
    rw [← Measure.map_apply (hGm t) hA, hGlaw t]
  rw [Measure.map_apply (measurable_comp_of_countable hT hR hGm) hA,
    measure_preimage_comp_of_indepFun hT hR hind hGm hA, hRlaw.map_eq,
    Finset.sum_congr rfl (fun t _ ↦ by rw [hA' t]), ← Finset.sum_mul,
    sum_measure_preimage_singleton_eq_one hT, one_mul]

/-- The remainders relabelled by cell: the remainder of the point lying in cell `j`,
`r(σ_T⁻¹ j)`. -/
noncomputable def owenRemainder {b m : ℕ} (T : OwenTree b m) (r : Fin (b ^ m) → ℝ) :
    Fin (b ^ m) → ℝ :=
  fun j ↦ r ((owenCell T).symm j)

/-- The scrambled net relabelled by cell is the stratified point set of the relabelled
remainders. -/
theorem owenNetSorted_eq_stratPoints {b m : ℕ} (T : OwenTree b m) (r : Fin (b ^ m) → ℝ) :
    owenNetSorted T r = stratPoints (b ^ m) (owenRemainder T r) := by
  funext j
  rw [owenNetSorted_apply]
  rfl

/-- **The relabelled remainders are i.i.d. uniform**: if the tree is independent of
`R ~ U[0,1)^(bᵐ)`, then `j ↦ R(σ_T⁻¹ j)` is again `U[0,1)^(bᵐ)`. -/
theorem hasLaw_owenRemainder {P : Measure Ω} [IsProbabilityMeasure P] {T : Ω → OwenTree b m}
    {R : Ω → Fin (b ^ m) → ℝ} (hT : Measurable T) (hR : Measurable R)
    (hRlaw : HasLaw R (uniformCube (b ^ m)) P) (hind : IndepFun T R P) :
    HasLaw (fun ω ↦ owenRemainder (T ω) (R ω)) (uniformCube (b ^ m)) P := by
  have hmp : ∀ t : OwenTree b m, MeasurePreserving (owenRemainder t) (uniformCube (b ^ m))
      (uniformCube (b ^ m)) := fun t ↦ measurePreserving_comp_perm (owenCell t)
  have hGm : ∀ t : OwenTree b m, Measurable (owenRemainder t) := fun t ↦ (hmp t).measurable
  refine ⟨(measurable_comp_of_countable hT hR hGm).aemeasurable, ?_⟩
  ext A hA
  have hA' : ∀ t : OwenTree b m, uniformCube (b ^ m) (owenRemainder t ⁻¹' A) =
      uniformCube (b ^ m) A := fun t ↦ by
    rw [← Measure.map_apply (hGm t) hA, (hmp t).map_eq]
  rw [Measure.map_apply (measurable_comp_of_countable hT hR hGm) hA,
    measure_preimage_comp_of_indepFun hT hR hind hGm hA, hRlaw.map_eq,
    Finset.sum_congr rfl (fun t _ ↦ by rw [hA' t]), ← Finset.sum_mul,
    sum_measure_preimage_singleton_eq_one hT, one_mul]

/-- A uniform tree gives each tree probability `1/#OwenTree`. -/
theorem measure_preimage_singleton_of_uniform {P : Measure Ω} {T : Ω → OwenTree b m}
    (hT : Measurable T) (hTlaw : HasLaw T (uniformOn univ) P) (t : OwenTree b m) :
    P (T ⁻¹' {t}) = (Fintype.card (OwenTree b m) : ℝ≥0∞)⁻¹ := by
  rw [← Measure.map_apply hT (measurableSet_singleton t), hTlaw.map_eq, uniformOn_univ,
    Measure.count_singleton, one_div]

/-- The coordinates of `R ~ U[0,1)ⁿ` are `U[0,1)`. -/
theorem hasLaw_apply_of_hasLaw_uniformCube {n : ℕ} {P : Measure Ω} {R : Ω → Fin n → ℝ}
    (hR : Measurable R) (hRlaw : HasLaw R (uniformCube n) P) (k : Fin n) :
    HasLaw (fun ω ↦ R ω k) uniformIco P := by
  have := isProbabilityMeasure_uniformIco
  refine ⟨((measurable_pi_apply k).comp hR).aemeasurable, ?_⟩
  change Measure.map ((fun f : Fin n → ℝ ↦ f k) ∘ R) P = uniformIco
  rw [← Measure.map_map (measurable_pi_apply k) hR, hRlaw.map_eq]
  exact (measurePreserving_eval (fun _ : Fin n ↦ uniformIco) k).map_eq

/-- **RQMC requirement (i) for the scrambled net** (posts #1-#2): with a uniform tree independent
of the remainders `R ~ U[0,1)^(bᵐ)`, each scrambled point `(σ_T k + R k)/bᵐ` is `U[0,1)`. -/
theorem hasLaw_owenNet (hb : b ≠ 0) {P : Measure Ω} {T : Ω → OwenTree b m}
    {R : Ω → Fin (b ^ m) → ℝ} (hT : Measurable T) (hR : Measurable R)
    (hTlaw : HasLaw T (uniformOn univ) P) (hRlaw : HasLaw R (uniformCube (b ^ m)) P)
    (hind : IndepFun T R P) (k : Fin (b ^ m)) :
    HasLaw (fun ω ↦ owenNet (T ω) (R ω) k) uniformIco P := by
  have hn0 : b ^ m ≠ 0 := pow_ne_zero m hb
  set G : OwenTree b m → (Fin (b ^ m) → ℝ) → ℝ :=
    fun t r ↦ stratumMap (b ^ m) (owenCell t k) (r k) with hGdef
  have hGm : ∀ t, Measurable (G t) := fun t ↦
    (measurable_stratumMap (b ^ m) _).comp (measurable_pi_apply k)
  have hm : Measurable fun ω ↦ G (T ω) (R ω) := measurable_comp_of_countable hT hR hGm
  have hRk := hasLaw_apply_of_hasLaw_uniformCube hR hRlaw k
  refine ⟨hm.aemeasurable, ?_⟩
  ext A hA
  set F : Fin (b ^ m) → ℝ≥0∞ := fun j ↦ uniformIco.map (stratumMap (b ^ m) j) A with hF
  have hterm : ∀ t, P.map R (G t ⁻¹' A) = F (owenCell t k) := fun t ↦ by
    have hRkm : Measurable fun ω ↦ R ω k := (measurable_pi_apply k).comp hR
    change P.map R (G t ⁻¹' A) = uniformIco.map (stratumMap (b ^ m) (owenCell t k)) A
    rw [Measure.map_apply hR ((hGm t) hA), ← hRk.map_eq,
      Measure.map_apply (measurable_stratumMap _ _) hA,
      Measure.map_apply hRkm ((measurable_stratumMap _ _) hA)]
    rfl
  set c : ℝ≥0∞ := (Fintype.card (OwenTree b m) : ℝ≥0∞)⁻¹ with hc
  have hfib : ∀ j : Fin (b ^ m),
      ((Finset.univ.filter fun t : OwenTree b m ↦ owenCell t k = j).card : ℝ≥0∞) * c =
        ((b ^ m : ℕ) : ℝ≥0∞)⁻¹ := by
    intro j
    have h := congrArg (Nat.cast : ℕ → ℝ≥0∞) (card_filter_owenCell (b := b) (m := m) k j)
    rw [Nat.cast_mul] at h
    set x : ℝ≥0∞ := ((Finset.univ.filter fun t : OwenTree b m ↦ owenCell t k = j).card : ℝ≥0∞)
    have hcard : (Fintype.card (OwenTree b m) : ℝ≥0∞) ≠ 0 :=
      Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have hx0 : x ≠ 0 := by
      intro hx
      rw [hx, mul_zero] at h
      exact hcard h.symm
    have hxt : x ≠ ⊤ := ENNReal.natCast_ne_top _
    have hnt : ((b ^ m : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hn0' : ((b ^ m : ℕ) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hn0
    rw [hc, ← h, ENNReal.mul_inv (Or.inl hn0') (Or.inl hnt), mul_comm, mul_assoc,
      ENNReal.inv_mul_cancel hx0 hxt, mul_one]
  change (P.map fun ω ↦ G (T ω) (R ω)) A = uniformIco A
  rw [Measure.map_apply hm hA, measure_preimage_comp_of_indepFun hT hR hind hGm hA,
    Finset.sum_congr rfl (fun t _ ↦ by
      rw [measure_preimage_singleton_of_uniform hT hTlaw t, hterm t]),
    ← Finset.sum_fiberwise Finset.univ (fun t : OwenTree b m ↦ owenCell t k)
      (fun t ↦ c * F (owenCell t k))]
  have hinner : ∀ j : Fin (b ^ m), ∑ t ∈ Finset.univ with owenCell t k = j, c * F (owenCell t k) =
      ((b ^ m : ℕ) : ℝ≥0∞)⁻¹ * F j := fun j ↦ by
    rw [Finset.sum_congr rfl (fun t ht ↦ by rw [(Finset.mem_filter.1 ht).2]), Finset.sum_const,
      nsmul_eq_mul, ← mul_assoc, hfib j]
  rw [Finset.sum_congr rfl (fun j _ ↦ hinner j), ← Finset.mul_sum]
  have hsum : ∑ j : Fin (b ^ m), F j = ((b ^ m : ℕ) : ℝ≥0∞) * uniformIco A := by
    have h := congrArg (fun μ : Measure ℝ ↦ μ A) (sum_map_stratumMap hn0)
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul] at h
    exact h
  rw [hsum, ← mul_assoc, ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 hn0)
    (ENNReal.natCast_ne_top _), one_mul]

/-- Relabelling does not change the estimator: `μ̂(owenNet) = μ̂(owenNetSorted)`. -/
theorem sampleMean_owenNet (T : OwenTree b m) (r : Fin (b ^ m) → ℝ) (f : ℝ → ℝ) :
    sampleMean (b ^ m) f (owenNet T r) = sampleMean (b ^ m) f (owenNetSorted T r) := by
  unfold sampleMean
  congr 1
  exact (Equiv.sum_comp (owenCell T).symm (fun k ↦ f (owenNet T r k))).symm

/-- The sample mean is a measurable function of the points, for measurable `f`. -/
theorem measurable_sampleMean {n : ℕ} {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (sampleMean n f) := by
  change Measurable fun x : Fin n → ℝ ↦ (n : ℝ)⁻¹ * ∑ i : Fin n, f (x i)
  refine Measurable.const_mul ?_ _
  exact Finset.measurable_fun_sum _ (fun (i : Fin n) _ ↦ hf.comp (measurable_pi_apply i))

/-- **The scrambled-net estimator has the law of the independent-stratified estimator**: for
measurable `f`, the law of `(1/bᵐ) Σₖ f(owenNet T R k)` is the law of
`(1/n) Σᵢ f((i + Vᵢ)/n)`, `V ~ U[0,1)ⁿ`, `n = bᵐ`. -/
theorem map_sampleMean_owenNet {P : Measure Ω} [IsProbabilityMeasure P] {T : Ω → OwenTree b m}
    {R : Ω → Fin (b ^ m) → ℝ} (hT : Measurable T) (hR : Measurable R)
    (hRlaw : HasLaw R (uniformCube (b ^ m)) P) (hind : IndepFun T R P) {f : ℝ → ℝ}
    (hf : Measurable f) :
    P.map (fun ω ↦ sampleMean (b ^ m) f (owenNet (T ω) (R ω))) =
      (uniformCube (b ^ m)).map (fun v ↦ sampleMean (b ^ m) f (stratPoints (b ^ m) v)) := by
  have hfun : (fun ω ↦ sampleMean (b ^ m) f (owenNet (T ω) (R ω))) =
      sampleMean (b ^ m) f ∘ (fun ω ↦ owenNetSorted (T ω) (R ω)) :=
    funext fun ω ↦ sampleMean_owenNet (T ω) (R ω) f
  have hL := hasLaw_owenNetSorted hT hR hRlaw hind
  rw [hfun, ← AEMeasurable.map_map_of_aemeasurable (measurable_sampleMean hf).aemeasurable
    hL.aemeasurable, hL.map_eq, stratifiedLaw,
    Measure.map_map (measurable_sampleMean hf) (measurable_stratPoints _)]
  rfl

/-- The same statement as an `IdentDistrib`. -/
theorem identDistrib_sampleMean_owenNet {P : Measure Ω} [IsProbabilityMeasure P]
    {T : Ω → OwenTree b m} {R : Ω → Fin (b ^ m) → ℝ} (hT : Measurable T) (hR : Measurable R)
    (hRlaw : HasLaw R (uniformCube (b ^ m)) P) (hind : IndepFun T R P) {f : ℝ → ℝ}
    (hf : Measurable f) :
    IdentDistrib (fun ω ↦ sampleMean (b ^ m) f (owenNet (T ω) (R ω)))
      (fun v ↦ sampleMean (b ^ m) f (stratPoints (b ^ m) v)) P (uniformCube (b ^ m)) where
  aemeasurable_fst := ((measurable_sampleMean hf).comp
    (measurable_comp_of_countable (G := fun t r ↦ owenNet t r) hT hR fun _ ↦
      Measurable.of_eval fun (k : Fin (b ^ m)) ↦
        (measurable_stratumMap _ _).comp (measurable_pi_apply k))).aemeasurable
  aemeasurable_snd := ((measurable_sampleMean hf).comp (measurable_stratPoints _)).aemeasurable
  map_eq := map_sampleMean_owenNet hT hR hRlaw hind hf

/-- On `U[0,1)ⁿ` the coordinates are i.i.d. `U[0,1)`. -/
theorem hasLaw_eval_uniformCube {n : ℕ} (i : Fin n) :
    HasLaw (fun v : Fin n → ℝ ↦ v i) uniformIco (uniformCube n) := by
  have := isProbabilityMeasure_uniformIco
  exact ⟨(measurable_pi_apply i).aemeasurable,
    (measurePreserving_eval (fun _ : Fin n ↦ uniformIco) i).map_eq⟩

/-- On `U[0,1)ⁿ` the coordinates are independent. -/
theorem iIndepFun_eval_uniformCube (n : ℕ) :
    iIndepFun (fun (i : Fin n) (v : Fin n → ℝ) ↦ v i) (uniformCube n) := by
  have := isProbabilityMeasure_uniformIco
  exact iIndepFun_pi (X := fun _ x ↦ x) (fun _ ↦ aemeasurable_id)

/-- **The scrambled net is unbiased** (post #2): `E[(1/bᵐ) Σₖ f(owenNet T R k)] = ∫₀¹ f`. -/
theorem integral_sampleMean_owenNet (hb : b ≠ 0) {P : Measure Ω} {T : Ω → OwenTree b m}
    {R : Ω → Fin (b ^ m) → ℝ} (hT : Measurable T) (hR : Measurable R)
    (hTlaw : HasLaw T (uniformOn univ) P) (hRlaw : HasLaw R (uniformCube (b ^ m)) P)
    (hind : IndepFun T R P) {f : ℝ → ℝ} (hf : Integrable f uniformIco) :
    ∫ ω, sampleMean (b ^ m) f (owenNet (T ω) (R ω)) ∂P = ∫ x, f x ∂uniformIco :=
  integral_sampleMean_iid (pow_ne_zero m hb)
    (fun k ↦ hasLaw_owenNet hb hT hR hTlaw hRlaw hind k) hf

/-- **Exact variance of the scrambled net** (post #2): it is the variance of independent
stratified sampling, `Var = n⁻² Σᵢ Var(f | cell i)`, `n = bᵐ`, for measurable `f ∈ L²`. -/
theorem variance_sampleMean_owenNet (hb : b ≠ 0) {P : Measure Ω} [IsProbabilityMeasure P]
    {T : Ω → OwenTree b m} {R : Ω → Fin (b ^ m) → ℝ} (hT : Measurable T) (hR : Measurable R)
    (hRlaw : HasLaw R (uniformCube (b ^ m)) P) (hind : IndepFun T R P) {f : ℝ → ℝ}
    (hfm : Measurable f) (hf : MemLp f 2 uniformIco) :
    Var[fun ω ↦ sampleMean (b ^ m) f (owenNet (T ω) (R ω)); P] =
      (((b ^ m : ℕ) : ℝ)⁻¹) ^ 2 *
        ∑ i : Fin (b ^ m), Var[fun u ↦ f (stratumMap (b ^ m) i u); uniformIco] := by
  rw [(identDistrib_sampleMean_owenNet hT hR hRlaw hind hfm).variance_eq]
  exact variance_stratified_eq (pow_ne_zero m hb) hasLaw_eval_uniformCube
    (iIndepFun_eval_uniformCube _) hf

/-- **The scrambled net never does worse than MC**: `Var ≤ Var_{U[0,1)}(f)/bᵐ`. -/
theorem variance_sampleMean_owenNet_le_mc (hb : b ≠ 0) {P : Measure Ω} [IsProbabilityMeasure P]
    {T : Ω → OwenTree b m} {R : Ω → Fin (b ^ m) → ℝ} (hT : Measurable T) (hR : Measurable R)
    (hRlaw : HasLaw R (uniformCube (b ^ m)) P) (hind : IndepFun T R P) {f : ℝ → ℝ}
    (hfm : Measurable f) (hf : MemLp f 2 uniformIco) :
    Var[fun ω ↦ sampleMean (b ^ m) f (owenNet (T ω) (R ω)); P] ≤
      Var[f; uniformIco] / (b ^ m : ℕ) := by
  have := isProbabilityMeasure_uniformIco
  rw [(identDistrib_sampleMean_owenNet hT hR hRlaw hind hfm).variance_eq]
  exact variance_stratified_le_mc (pow_ne_zero m hb) hasLaw_eval_uniformCube
    (iIndepFun_eval_uniformCube _) hf

/-- **The scrambled net, Lipschitz rate `O(n^{-3})`**: for `K`-Lipschitz `f` and `n = bᵐ`,
`Var ≤ K²/(12 n³)`, i.e. RMSE `O(n^{-3/2})`. -/
theorem variance_sampleMean_owenNet_le_lipschitz (hb : b ≠ 0) {P : Measure Ω}
    [IsProbabilityMeasure P] {T : Ω → OwenTree b m} {R : Ω → Fin (b ^ m) → ℝ}
    (hT : Measurable T) (hR : Measurable R) (hRlaw : HasLaw R (uniformCube (b ^ m)) P)
    (hind : IndepFun T R P) {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    Var[fun ω ↦ sampleMean (b ^ m) f (owenNet (T ω) (R ω)); P] ≤
      (K : ℝ) ^ 2 / (12 * ((b ^ m : ℕ) : ℝ) ^ 3) := by
  rw [(identDistrib_sampleMean_owenNet hT hR hRlaw hind hf.continuous.measurable).variance_eq]
  exact variance_stratified_le_lipschitz (pow_ne_zero m hb) hasLaw_eval_uniformCube
    (iIndepFun_eval_uniformCube _) hf

end RQMCMarkov.OwenScrambling

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A Lindeberg CLT for triangular arrays of bounded independent terms (for post #2)

Mathlib has the CLT for i.i.d. sequences only. Post #2's claim about Owen scrambling ("a standard
CLT applies") concerns sums of independent but NOT identically distributed terms (one per cell of
the net, see `Owen1DScramble`), whose number grows with `n`: a triangular array. This module
proves the CLT for such arrays under the bounded form of Lindeberg's condition, by characteristic
functions and Lévy's continuity theorem (Mathlib's
`ProbabilityMeasure.tendsto_iff_tendsto_charFun`).

## Main results

* `norm_prod_sub_prod_le`: `‖Πᵢ aᵢ − Πᵢ cᵢ‖ ≤ Σᵢ ‖aᵢ − cᵢ‖` when all `‖aᵢ‖, ‖cᵢ‖ ≤ 1`.
* `norm_charFun_sub_le_of_abs_le`: for centred `X` with `|X| ≤ δ` a.s. and `|t| δ ≤ 1`,
  `‖φ_X(t) − (1 − t² E[X²]/2)‖ ≤ |t|³ δ E[X²]`.
* `tendstoInDistribution_sum_of_bounded` (**Lindeberg CLT, bounded form**): for each `n` let
  `X n 0, …, X n (L n − 1)` be independent and centred on a probability space `(Ωₙ, Pₙ)` with
  `|X n i| ≤ δₙ` a.s., `δₙ → 0`, and `Σᵢ E[(X n i)²] → v`. Then `Σᵢ X n i ⇒ N(0, v)`.

The bounded condition `max |X n i| ≤ δₙ → 0` with `Σᵢ Var → v` implies Lindeberg's condition
(each truncated second moment vanishes once `δₙ < ε`), and it is what the stratified estimator
satisfies for `C¹` integrands.
-/

namespace RQMCMarkov.OwenScrambling

open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped ENNReal NNReal Topology

/-- **Telescoping bound for products** of complex numbers of norm at most one:
`‖Πᵢ aᵢ − Πᵢ cᵢ‖ ≤ Σᵢ ‖aᵢ − cᵢ‖`. -/
theorem norm_prod_sub_prod_le {ι : Type*} (s : Finset ι) (a c : ι → ℂ)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) (hc : ∀ i ∈ s, ‖c i‖ ≤ 1) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, c i‖ ≤ ∑ i ∈ s, ‖a i - c i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, sub_self, norm_zero, Finset.sum_empty]
  | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
      have ha' : ∀ i ∈ s, ‖a i‖ ≤ 1 := fun i hi ↦ ha i (Finset.mem_insert_of_mem hi)
      have hc' : ∀ i ∈ s, ‖c i‖ ≤ 1 := fun i hi ↦ hc i (Finset.mem_insert_of_mem hi)
      have hQ : ‖∏ i ∈ s, c i‖ ≤ 1 := by
        rw [norm_prod]
        exact Finset.prod_le_one₀ (fun i _ ↦ norm_nonneg _) hc'
      have haj := ha j (Finset.mem_insert_self j s)
      have heq : a j * ∏ i ∈ s, a i - c j * ∏ i ∈ s, c i =
          a j * (∏ i ∈ s, a i - ∏ i ∈ s, c i) + (a j - c j) * ∏ i ∈ s, c i := by ring
      rw [heq]
      calc ‖a j * (∏ i ∈ s, a i - ∏ i ∈ s, c i) + (a j - c j) * ∏ i ∈ s, c i‖
          ≤ ‖a j‖ * ‖∏ i ∈ s, a i - ∏ i ∈ s, c i‖ + ‖a j - c j‖ * ‖∏ i ∈ s, c i‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul]
        _ ≤ 1 * ∑ i ∈ s, ‖a i - c i‖ + ‖a j - c j‖ * 1 := by
            gcongr
            exact ih ha' hc'
        _ = ‖a j - c j‖ + ∑ i ∈ s, ‖a i - c i‖ := by ring

/-- The cubic Taylor bound for `e^{iy}`: `‖e^{iy} − (1 − y²/2 + i y)‖ ≤ |y|³` for `|y| ≤ 1`. -/
theorem norm_cexp_mul_I_sub_le {y : ℝ} (hy : |y| ≤ 1) :
    ‖cexp ((y : ℂ) * I) - (((1 - y ^ 2 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ |y| ^ 3 := by
  have hz : ‖(y : ℂ) * I‖ = |y| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hb := Complex.exp_bound (x := (y : ℂ) * I) (by rw [hz]; exact hy) (n := 3) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 3, ((y : ℂ) * I) ^ m / (m.factorial : ℂ) =
      ((1 - y ^ 2 / 2 : ℝ) : ℂ) + (y : ℂ) * I := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one,
      mul_pow, I_sq, Nat.factorial_zero, Nat.factorial_one, Nat.factorial_two]
    push_cast
    ring
  rw [hsum, hz] at hb
  refine hb.trans ?_
  have h3 : (0 : ℝ) ≤ |y| ^ 3 := by positivity
  have hc : ((Nat.succ 3 : ℕ) : ℝ) * (((Nat.factorial 3 : ℕ) : ℝ) * (3 : ℕ))⁻¹ ≤ 1 := by
    norm_num [Nat.factorial]
  calc |y| ^ 3 * (((Nat.succ 3 : ℕ) : ℝ) * (((Nat.factorial 3 : ℕ) : ℝ) * (3 : ℕ))⁻¹)
      ≤ |y| ^ 3 * 1 := mul_le_mul_of_nonneg_left hc h3
    _ = |y| ^ 3 := mul_one _

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Characteristic function of a bounded centred variable**: if `|X| ≤ δ` a.s., `E[X] = 0` and
`|t| δ ≤ 1`, then `‖φ_X(t) − (1 − t² E[X²]/2)‖ ≤ |t|³ δ E[X²]`. -/
theorem norm_charFun_sub_le_of_abs_le {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : AEMeasurable X P) {δ : ℝ} (hb : ∀ᵐ ω ∂P, |X ω| ≤ δ) (h0 : ∫ ω, X ω ∂P = 0) {t : ℝ}
    (ht : |t| * δ ≤ 1) :
    ‖charFun (P.map X) t - ((1 - t ^ 2 * (∫ ω, X ω ^ 2 ∂P) / 2 : ℝ) : ℂ)‖ ≤
      |t| ^ 3 * δ * ∫ ω, X ω ^ 2 ∂P := by
  have hXi : Integrable X P := Integrable.of_bound hX.aestronglyMeasurable δ
    (hb.mono fun ω hω ↦ by rw [Real.norm_eq_abs]; exact hω)
  have hX2 : Integrable (fun ω ↦ X ω ^ 2) P := by
    refine Integrable.of_bound (hX.pow_const 2).aestronglyMeasurable (δ ^ 2) ?_
    filter_upwards [hb] with ω hω
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hω 2
  set q : Ω → ℂ := fun ω ↦ ((1 - (t * X ω) ^ 2 / 2 : ℝ) : ℂ) + ((t * X ω : ℝ) : ℂ) * I with hq
  have hqi : Integrable q P := by
    refine Integrable.add ?_ ?_
    · exact ((integrable_const 1).sub ((hX2.const_mul (t ^ 2)).div_const 2)).ofReal.congr
        (Eventually.of_forall fun ω ↦ by
          change (((1 - t ^ 2 * X ω ^ 2 / 2 : ℝ)) : ℂ) = ((1 - (t * X ω) ^ 2 / 2 : ℝ) : ℂ)
          rw [mul_pow])
    · exact (hXi.const_mul t).ofReal.mul_const I
  have hqint : ∫ ω, q ω ∂P = ((1 - t ^ 2 * (∫ ω, X ω ^ 2 ∂P) / 2 : ℝ) : ℂ) := by
    rw [hq, integral_add, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal,
      integral_const_mul, h0, mul_zero, Complex.ofReal_zero, zero_mul, add_zero]
    · congr 1
      rw [integral_sub (integrable_const 1) ((hX2.const_mul (t ^ 2)).div_const 2 |>.congr
        (Eventually.of_forall fun ω ↦ by
          change t ^ 2 * X ω ^ 2 / 2 = (t * X ω) ^ 2 / 2
          rw [mul_pow])), integral_const, integral_div,
        integral_congr_ae (Eventually.of_forall fun ω ↦ (mul_pow t (X ω) 2 : _)),
        integral_const_mul]
      rw [probReal_univ, one_smul]
    · exact ((integrable_const 1).sub ((hX2.const_mul (t ^ 2)).div_const 2)).ofReal.congr
        (Eventually.of_forall fun ω ↦ by
          change (((1 - t ^ 2 * X ω ^ 2 / 2 : ℝ)) : ℂ) = ((1 - (t * X ω) ^ 2 / 2 : ℝ) : ℂ)
          rw [mul_pow])
    · exact (hXi.const_mul t).ofReal.mul_const I
  have he : Integrable (fun ω ↦ cexp (((t * X ω : ℝ) : ℂ) * I)) P := by
    refine Integrable.of_bound ?_ 1 (Eventually.of_forall fun ω ↦ ?_)
    · exact (Complex.continuous_exp.comp_aestronglyMeasurable
        ((Complex.continuous_ofReal.comp_aestronglyMeasurable
          (hX.const_mul t).aestronglyMeasurable).mul aestronglyMeasurable_const))
    · rw [Complex.norm_exp_ofReal_mul_I]
  have hcf : charFun (P.map X) t = ∫ ω, cexp (((t * X ω : ℝ) : ℂ) * I) ∂P := by
    rw [charFun_apply_real, integral_map hX]
    · congr 1
      funext ω
      push_cast
      rfl
    · exact (Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).mul
        continuous_const)).aestronglyMeasurable
  rw [hcf, ← hqint, ← integral_sub he hqi]
  refine (norm_integral_le_of_norm_le ((hX2.const_mul (|t| ^ 3 * δ))) ?_).trans ?_
  · filter_upwards [hb] with ω hω
    have hy : |t * X ω| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left hω (abs_nonneg t)).trans ht
    refine (norm_cexp_mul_I_sub_le hy).trans ?_
    have h3 : |X ω| ^ 3 = |X ω| * X ω ^ 2 := by
      rw [← sq_abs (X ω)]
      ring
    rw [abs_mul, mul_pow, h3]
    have hX0 : 0 ≤ X ω ^ 2 := sq_nonneg _
    have ht0 : 0 ≤ |t| ^ 3 := by positivity
    calc |t| ^ 3 * (|X ω| * X ω ^ 2) ≤ |t| ^ 3 * (δ * X ω ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hω hX0) ht0
      _ = |t| ^ 3 * δ * X ω ^ 2 := by ring
  · rw [integral_const_mul]

/-- **Lindeberg CLT for triangular arrays, bounded form.** For each `n` let `X n i`, `i < L n`, be
independent, centred random variables on a probability space `(Ωₙ, Pₙ)`, with `|X n i| ≤ δₙ`
almost surely, `δₙ → 0`, and `Σᵢ E[(X n i)²] → v`. Then `Σᵢ X n i` converges in distribution to
`N(0, v)`. -/
theorem tendstoInDistribution_sum_of_bounded {Ω : ℕ → Type*} {mΩ : ∀ n, MeasurableSpace (Ω n)}
    {P : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)] {L : ℕ → ℕ}
    {X : (n : ℕ) → Fin (L n) → Ω n → ℝ} (hXm : ∀ n i, AEMeasurable (X n i) (P n))
    (hind : ∀ n, iIndepFun (X n) (P n)) (h0 : ∀ n i, ∫ ω, X n i ω ∂(P n) = 0)
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) (hbd : ∀ n i, ∀ᵐ ω ∂(P n), |X n i ω| ≤ δ n)
    {v : ℝ} (hv : Tendsto (fun n ↦ ∑ i, ∫ ω, X n i ω ^ 2 ∂(P n)) atTop (𝓝 v))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 v.toNNReal) P') :
    TendstoInDistribution (fun n ω ↦ ∑ i, X n i ω) atTop Z P P' where
  forall_aemeasurable n := Finset.aemeasurable_fun_sum _ fun i _ ↦ hXm n i
  aemeasurable_limit := hZ.aemeasurable
  tendsto := by
    -- notation
    set w : (n : ℕ) → Fin (L n) → ℝ := fun n i ↦ ∫ ω, X n i ω ^ 2 ∂(P n) with hw
    set sv : ℕ → ℝ := fun n ↦ ∑ i, w n i with hsv
    have hw0 : ∀ n i, 0 ≤ w n i := fun n i ↦ integral_nonneg fun ω ↦ sq_nonneg _
    have hv0 : 0 ≤ v := ge_of_tendsto' hv fun n ↦ Finset.sum_nonneg fun i _ ↦ hw0 n i
    have hwδ : ∀ n i, w n i ≤ δ n ^ 2 := by
      intro n i
      have h : ∫ ω, X n i ω ^ 2 ∂(P n) ≤ ∫ _ω, δ n ^ 2 ∂(P n) := by
        refine integral_mono_ae ?_ (integrable_const _) ?_
        · refine Integrable.of_bound ((hXm n i).pow_const 2).aestronglyMeasurable (δ n ^ 2) ?_
          filter_upwards [hbd n i] with ω hω
          rw [Real.norm_eq_abs, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) hω 2
        · filter_upwards [hbd n i] with ω hω
          rw [← sq_abs (X n i ω)]
          exact pow_le_pow_left₀ (abs_nonneg _) hω 2
      rw [integral_const, probReal_univ, one_smul] at h
      exact h
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t ↦ ?_
    change Tendsto (fun n ↦ charFun ((P n).map fun ω ↦ ∑ i, X n i ω) t) atTop
      (𝓝 (charFun (P'.map Z) t))
    have htarget : charFun (P'.map Z) t = ((Real.exp (-(t ^ 2 * v / 2)) : ℝ) : ℂ) := by
      rw [hZ.map_eq, charFun_gaussianReal, Real.coe_toNNReal _ hv0]
      push_cast
      congr 1
      ring
    rw [htarget]
    have hprod : ∀ n, charFun ((P n).map fun ω ↦ ∑ i, X n i ω) t =
        ∏ i, charFun ((P n).map (X n i)) t := fun n ↦ by
      rw [(hind n).charFun_map_fun_sum_eq_prod (hXm n), Finset.prod_apply]
    simp_rw [hprod]
    -- the Gaussian comparison products
    set a : (n : ℕ) → Fin (L n) → ℝ := fun n i ↦ t ^ 2 * w n i / 2 with ha
    have hcprod : ∀ n, ∏ i, ((Real.exp (-a n i) : ℝ) : ℂ) =
        ((Real.exp (-(t ^ 2 * sv n / 2)) : ℝ) : ℂ) := fun n ↦ by
      rw [← Complex.ofReal_prod, ← Real.exp_sum, Finset.sum_neg_distrib]
      congr 3
      rw [ha, hsv, ← Finset.sum_div, ← Finset.mul_sum]
    have hlimc : Tendsto (fun n ↦ ∏ i, ((Real.exp (-a n i) : ℝ) : ℂ)) atTop
        (𝓝 ((Real.exp (-(t ^ 2 * v / 2)) : ℝ) : ℂ)) := by
      simp_rw [hcprod]
      refine Tendsto.ofReal ((Real.continuous_exp.tendsto _).comp ?_)
      exact ((hv.const_mul (t ^ 2)).div_const 2).neg
    -- the error bound
    set B : ℕ → ℝ := fun n ↦ |t| ^ 3 * |δ n| * sv n + t ^ 2 * δ n ^ 2 / 2 * (t ^ 2 * sv n / 2)
      with hB
    have hB0 : Tendsto B atTop (𝓝 0) := by
      have h1 : Tendsto B atTop
          (𝓝 (|t| ^ 3 * |(0 : ℝ)| * v + t ^ 2 * (0 : ℝ) ^ 2 / 2 * (t ^ 2 * v / 2))) := by
        refine Tendsto.add ((tendsto_const_nhds.mul hδ.abs).mul hv) ?_
        exact (((tendsto_const_nhds.mul (hδ.pow 2)).div_const 2).mul
          ((hv.const_mul (t ^ 2)).div_const 2))
      rw [abs_zero] at h1
      convert h1 using 2
      ring
    have hev : ∀ᶠ n in atTop, |t| * |δ n| ≤ 1 := by
      have h := (tendsto_const_nhds (x := |t|)).mul hδ.abs
      rw [abs_zero, mul_zero] at h
      exact h.eventually (ge_mem_nhds one_pos)
    have hbound : ∀ᶠ n in atTop, ‖∏ i, charFun ((P n).map (X n i)) t -
        ∏ i, ((Real.exp (-a n i) : ℝ) : ℂ)‖ ≤ B n := by
      filter_upwards [hev] with n hn
      have hai0 : ∀ i, 0 ≤ a n i := fun i ↦ by
        rw [ha]
        have := hw0 n i
        positivity
      have haiδ : ∀ i, a n i ≤ t ^ 2 * δ n ^ 2 / 2 := fun i ↦ by
        rw [ha]
        have := hwδ n i
        have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
        have := mul_le_mul_of_nonneg_left this ht2
        linarith
      have htd : t ^ 2 * δ n ^ 2 ≤ 1 := by
        have h1 : (|t| * |δ n|) ^ 2 ≤ 1 := by
          have h0' : 0 ≤ |t| * |δ n| := by positivity
          nlinarith
        rw [mul_pow, sq_abs, sq_abs] at h1
        exact h1
      have hai1 : ∀ i, a n i ≤ 1 := fun i ↦ by linarith [haiδ i]
      refine (norm_prod_sub_prod_le Finset.univ _ _ (fun i _ ↦ norm_charFun_le_one _)
        (fun i _ ↦ ?_)).trans ?_
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          Real.exp_le_one_iff]
        linarith [hai0 i]
      have hterm : ∀ i, ‖charFun ((P n).map (X n i)) t - ((Real.exp (-a n i) : ℝ) : ℂ)‖ ≤
          |t| ^ 3 * |δ n| * w n i + t ^ 2 * δ n ^ 2 / 2 * a n i := by
        intro i
        have h1 := norm_charFun_sub_le_of_abs_le (hXm n i)
          ((hbd n i).mono fun ω hω ↦ hω.trans (le_abs_self _)) (h0 n i) hn
        have h2 : |Real.exp (-a n i) - 1 - (-a n i)| ≤ (-a n i) ^ 2 :=
          Real.abs_exp_sub_one_sub_id_le (by rw [abs_neg, abs_of_nonneg (hai0 i)]; exact hai1 i)
        have h3 : ‖(((1 - t ^ 2 * w n i / 2 : ℝ)) : ℂ) - ((Real.exp (-a n i) : ℝ) : ℂ)‖ ≤
            t ^ 2 * δ n ^ 2 / 2 * a n i := by
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          have heq : 1 - t ^ 2 * w n i / 2 - Real.exp (-a n i) =
              -(Real.exp (-a n i) - 1 - (-a n i)) := by
            rw [ha]
            ring
          rw [heq, abs_neg]
          refine h2.trans ?_
          rw [neg_sq, sq]
          exact mul_le_mul_of_nonneg_right (haiδ i) (hai0 i)
        calc ‖charFun ((P n).map (X n i)) t - ((Real.exp (-a n i) : ℝ) : ℂ)‖
            ≤ ‖charFun ((P n).map (X n i)) t - (((1 - t ^ 2 * w n i / 2 : ℝ)) : ℂ)‖ +
              ‖(((1 - t ^ 2 * w n i / 2 : ℝ)) : ℂ) - ((Real.exp (-a n i) : ℝ) : ℂ)‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ |t| ^ 3 * |δ n| * w n i + t ^ 2 * δ n ^ 2 / 2 * a n i := add_le_add h1 h3
      refine (Finset.sum_le_sum fun i _ ↦ hterm i).trans (le_of_eq ?_)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hB]
      congr 2
      rw [ha, hsv, ← Finset.sum_div, ← Finset.mul_sum]
    have hdiff : Tendsto (fun n ↦ ∏ i, charFun ((P n).map (X n i)) t -
        ∏ i, ((Real.exp (-a n i) : ℝ) : ℂ)) atTop (𝓝 0) :=
      squeeze_zero_norm' hbound hB0
    have := hdiff.add hlimc
    rw [zero_add] at this
    refine this.congr (fun n ↦ ?_)
    ring

end RQMCMarkov.OwenScrambling

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The randomly shifted lattice rule is not asymptotically normal (post #2)

Copied from `RQMCMarkov/PointSets` (namespace and imports renamed); see that project for
its documentation.

Post #2: "If we use an RQMC estimator with a randomly-shifted lattice rule, the limiting
distribution as `n → ∞` is usually a spline, not a normal distribution" (L'Ecuyer, Munger and
Tuffin 2010). Reading, in one dimension: the rank-1 lattice with generator `1`, `{i/n : i < n}`,
randomly shifted, is the common-shift stratified rule `μ̂ₙ(U) = (1/n) Σᵢ f((i + U)/n)` with
`U ~ U[0,1)` (as point SETS, `{fract (i/n + U)} = {(i + fract (n U))/n}`; we work with the labelling
`(i + U)/n`, which makes the convergence below almost sure; `ShiftLimitLattice` in the
`PointSets` project proves the identification and transfers the results to the lattice labelling).

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
`o(1/n)` and a finer scale is needed. Owen scrambling's CLT (Loh 2003) is in
`Owen1DCLT` and `LohCLT`.
-/

namespace RQMCMarkov.OwenScrambling

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

end RQMCMarkov.OwenScrambling

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exact asymptotics of the stratified (= Owen-scrambled net) variance: `n³ σₙ² → ∫ f'²/12`

By `Owen1DScramble`, the Owen-scrambled `(0,m,1)`-net in base `b` has the law of independent
stratified sampling with `n = bᵐ` cells, so its variance is
`σₙ² = stratVar n f = n⁻² Σᵢ Var(f | cell i)` (`variance_stratified_eq`). `Stratified` bounds it
by `K²/(12 n³)` for `K`-Lipschitz `f`; here we find its exact first-order behaviour.

## Main results

* `stratVar`, `stratVar_nonneg`: `σₙ² = n⁻² Σᵢ Var_{u ~ U[0,1)} f((i + u)/n)`.
* `abs_variance_add_sub_le`: `|Var(X + Y) − Var(X)| ≤ 2η(2A + η)` when `|X| ≤ A`, `|Y| ≤ η`.
* `abs_sub_sub_deriv_mul_le`: the mean value bound `|f(y) − f(a) − f'(a)(y − a)| ≤ ε h` on a cell
  `[a, a + h]` where `f'` varies by at most `ε`.
* `abs_variance_cell_sub_le`: `|Var_u f(a + u h) − (f'(a) h)²/12| ≤ ε (7L + 25ε) h²`, `|f'(a)| ≤ L`.
* `abs_integral_sq_deriv_sub_le`: `|∫ₐ^{a+h} f'² − f'(a)² h| ≤ ε (2L + ε) h`;
  `abs_inv_mul_variance_cell_sub_le` combines the two cell estimates.
* `tendsto_cube_mul_stratVar`: for `f` `C¹` on `[0,1]`, `n³ σₙ² → (1/12) ∫₀¹ f'(x)² dx`, so the
  RMSE is `σₙ ~ n^{-3/2} (∫ f'²/12)^{1/2}` (Owen 1997's rate in one dimension).
* `integral_sq_deriv_pos`: if `f` is not constant on `[0,1]` then `∫₀¹ f'² > 0`, so then
  `σₙ > 0` for all large `n` (`eventually_stratVar_pos`).
* `stratVar_const`: for constant `f`, `σₙ = 0` for every `n` (the estimator is exact).

**Hypotheses.** `C¹` on `[0,1]` is as in `ShiftLimit`: `HasDerivWithinAt f (f' x) [0,1] x` for
`x ∈ [0,1]` with `f'` continuous on `[0,1]`.
-/

namespace RQMCMarkov.OwenScrambling

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The variance of the independent stratified estimator with `n` equal cells (and of the
Owen-scrambled net, `n = bᵐ`): `σₙ² = n⁻² Σᵢ Var_{u ~ U[0,1)} f((i + u)/n)`. -/
noncomputable def stratVar (n : ℕ) (f : ℝ → ℝ) : ℝ :=
  ((n : ℝ)⁻¹) ^ 2 * ∑ i : Fin n, Var[fun u ↦ f (stratumMap n i u); uniformIco]

/-- `σₙ² ≥ 0`. -/
theorem stratVar_nonneg (n : ℕ) (f : ℝ → ℝ) : 0 ≤ stratVar n f :=
  mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ ↦ variance_nonneg _ _)

/-- **Perturbation of a variance**: if `|X| ≤ A` and `|Y| ≤ η` a.s., then
`|Var(X + Y) − Var(X)| ≤ 2η(2A + η)`. -/
theorem abs_variance_add_sub_le {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) {A η : ℝ}
    (hXA : ∀ᵐ ω ∂μ, |X ω| ≤ A) (hYη : ∀ᵐ ω ∂μ, |Y ω| ≤ η) :
    |Var[fun ω ↦ X ω + Y ω; μ] - Var[X; μ]| ≤ 2 * η * (2 * A + η) := by
  have hXL : MemLp X 2 μ := MemLp.of_bound hX A (hXA.mono fun ω h ↦ by rwa [Real.norm_eq_abs])
  have hYL : MemLp Y 2 μ := MemLp.of_bound hY η (hYη.mono fun ω h ↦ by rwa [Real.norm_eq_abs])
  have hXYL : MemLp (fun ω ↦ X ω + Y ω) 2 μ := hXL.add hYL
  have hXi := hXL.integrable one_le_two
  have hYi := hYL.integrable one_le_two
  rw [variance_eq_sub hXYL, variance_eq_sub hXL]
  change |(∫ ω, (X ω + Y ω) ^ 2 ∂μ - (∫ ω, (X ω + Y ω) ∂μ) ^ 2) -
    (∫ ω, X ω ^ 2 ∂μ - (∫ ω, X ω ∂μ) ^ 2)| ≤ _
  have e1 : ∫ ω, (X ω + Y ω) ^ 2 ∂μ - ∫ ω, X ω ^ 2 ∂μ = ∫ ω, Y ω * (2 * X ω + Y ω) ∂μ := by
    rw [← integral_sub hXYL.integrable_sq hXL.integrable_sq]
    congr 1
    funext ω
    ring
  rw [integral_add hXi hYi]
  have hbd : ∀ {g : Ω → ℝ} {C : ℝ}, (∀ᵐ ω ∂μ, |g ω| ≤ C) → |∫ ω, g ω ∂μ| ≤ C := by
    intro g C hg
    have h := norm_integral_le_of_norm_le_const (μ := μ) (f := g) (C := C)
      (hg.mono fun ω h ↦ by rwa [Real.norm_eq_abs])
    rwa [probReal_univ, mul_one, Real.norm_eq_abs] at h
  have b2 : |∫ ω, X ω ∂μ| ≤ A := hbd hXA
  have b3 : |∫ ω, Y ω ∂μ| ≤ η := hbd hYη
  have hA0 : 0 ≤ A := (abs_nonneg _).trans b2
  have hη0 : 0 ≤ η := (abs_nonneg _).trans b3
  have b1 : |∫ ω, Y ω * (2 * X ω + Y ω) ∂μ| ≤ η * (2 * A + η) := by
    refine hbd ?_
    filter_upwards [hXA, hYη] with ω h1 h2
    rw [abs_mul]
    have h3 : |2 * X ω + Y ω| ≤ 2 * A + η := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_two]
      linarith
    exact mul_le_mul h2 h3 (abs_nonneg _) hη0
  have b4 : |(∫ ω, Y ω ∂μ) * (2 * (∫ ω, X ω ∂μ) + ∫ ω, Y ω ∂μ)| ≤ η * (2 * A + η) := by
    rw [abs_mul]
    have h3 : |2 * (∫ ω, X ω ∂μ) + ∫ ω, Y ω ∂μ| ≤ 2 * A + η := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_two]
      linarith
    exact mul_le_mul b3 h3 (abs_nonneg _) hη0
  have heq : (∫ ω, (X ω + Y ω) ^ 2 ∂μ - (∫ ω, X ω ∂μ + ∫ ω, Y ω ∂μ) ^ 2) -
      (∫ ω, X ω ^ 2 ∂μ - (∫ ω, X ω ∂μ) ^ 2) = ∫ ω, Y ω * (2 * X ω + Y ω) ∂μ -
        (∫ ω, Y ω ∂μ) * (2 * (∫ ω, X ω ∂μ) + ∫ ω, Y ω ∂μ) := by
    rw [← e1]
    ring
  rw [heq]
  calc |∫ ω, Y ω * (2 * X ω + Y ω) ∂μ - (∫ ω, Y ω ∂μ) * (2 * (∫ ω, X ω ∂μ) + ∫ ω, Y ω ∂μ)|
      ≤ |∫ ω, Y ω * (2 * X ω + Y ω) ∂μ| +
          |(∫ ω, Y ω ∂μ) * (2 * (∫ ω, X ω ∂μ) + ∫ ω, Y ω ∂μ)| := abs_sub _ _
    _ ≤ η * (2 * A + η) + η * (2 * A + η) := add_le_add b1 b4
    _ = 2 * η * (2 * A + η) := by ring

/-- **Mean value bound on a cell**: if `f' ` varies by at most `ε` on `[a, a + h]`, then
`|f(y) − f(a) − f'(a)(y − a)| ≤ ε h` for `y ∈ [a, a + h]`. -/
theorem abs_sub_sub_deriv_mul_le {f f' : ℝ → ℝ} {a h ε : ℝ} (hh : 0 < h)
    (hf : ∀ x ∈ Icc a (a + h), HasDerivWithinAt f (f' x) (Icc a (a + h)) x)
    (hε : ∀ x ∈ Icc a (a + h), |f' x - f' a| ≤ ε) {y : ℝ} (hy : y ∈ Icc a (a + h)) :
    |f y - f a - f' a * (y - a)| ≤ ε * h := by
  have hah : a ≤ a + h := by linarith
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hε a (left_mem_Icc.2 hah))
  set g : ℝ → ℝ := fun x ↦ f x - f' a * x with hg
  have hgd : ∀ x ∈ Icc a (a + h), HasDerivWithinAt g (f' x - f' a) (Icc a (a + h)) x := by
    intro x hx
    exact ((hf x hx).sub ((hasDerivWithinAt_id x _).const_mul (f' a))).congr_deriv (by ring)
  have := norm_image_sub_le_of_norm_deriv_le_segment' hgd
    (fun x hx ↦ by rw [Real.norm_eq_abs]; exact hε x (Ico_subset_Icc_self hx)) y hy
  rw [Real.norm_eq_abs] at this
  have heq : g y - g a = f y - f a - f' a * (y - a) := by
    simp only [hg]
    ring
  rw [← heq]
  exact this.trans (mul_le_mul_of_nonneg_left (by linarith [hy.2]) hε0)

/-- **Variance on one cell**: if `f` is differentiable on `[a, a + h]` with `|f' − f'(a)| ≤ ε` there
and `|f'(a)| ≤ L`, then `|Var_{u ~ U[0,1)} f(a + u h) − (f'(a) h)²/12| ≤ ε (7L + 25ε) h²`. -/
theorem abs_variance_cell_sub_le {f f' : ℝ → ℝ} {a h ε L : ℝ} (hh : 0 < h)
    (hf : ∀ x ∈ Icc a (a + h), HasDerivWithinAt f (f' x) (Icc a (a + h)) x)
    (hε : ∀ x ∈ Icc a (a + h), |f' x - f' a| ≤ ε) (hL : |f' a| ≤ L) :
    |Var[fun u ↦ f (a + u * h); uniformIco] - (f' a * h) ^ 2 / 12| ≤
      ε * (7 * L + 25 * ε) * h ^ 2 := by
  have := isProbabilityMeasure_uniformIco
  have hah : a ≤ a + h := by linarith
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hε a (left_mem_Icc.2 hah))
  have hL0 : 0 ≤ L := (abs_nonneg _).trans hL
  set Δ : ℝ := f (a + h) - f a with hΔ
  set c : ℝ := h⁻¹ * ∫ x in a..a + h, f x with hc
  set X : ℝ → ℝ := fun u ↦ -Δ / 2 + Δ * u with hX
  set Y : ℝ → ℝ := fun u ↦ f (a + u * h) - c - X u with hY
  have hfc : ContinuousOn f (Icc a (a + h)) := fun x hx ↦ (hf x hx).continuousWithinAt
  have hmaps : MapsTo (fun u : ℝ ↦ a + u * h) (Ico 0 1) (Icc a (a + h)) := fun u hu ↦
    ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩
  have hgc : ContinuousOn (fun u ↦ f (a + u * h)) (Ico 0 1) :=
    hfc.comp (continuous_const.add (continuous_id.mul continuous_const)).continuousOn hmaps
  have hgm : AEStronglyMeasurable (fun u ↦ f (a + u * h)) uniformIco :=
    hgc.aestronglyMeasurable measurableSet_Ico
  have hXc : Continuous X := continuous_const.add (continuous_const.mul continuous_id)
  have hXm : AEStronglyMeasurable X uniformIco := hXc.aestronglyMeasurable
  have hYm : AEStronglyMeasurable Y uniformIco := (hgm.sub aestronglyMeasurable_const).sub hXm
  have hfun : (fun u ↦ f (a + u * h)) = fun u ↦ c + (X u + Y u) := by
    funext u
    simp only [hY]
    ring
  have hVar : Var[fun u ↦ f (a + u * h); uniformIco] = Var[fun u ↦ X u + Y u; uniformIco] := by
    rw [hfun, variance_const_add (X := fun u ↦ X u + Y u) (hXm.add hYm) c]
  have hVX : Var[X; uniformIco] = Δ ^ 2 / 12 := variance_uniformIco_affine (-Δ / 2) Δ
  have hXb : ∀ᵐ u ∂uniformIco, |X u| ≤ |Δ| / 2 := by
    refine ae_restrict_of_forall_mem measurableSet_Ico (fun u hu ↦ ?_)
    have heq : X u = Δ * (u - 1 / 2) := by
      simp only [hX]
      ring
    rw [heq, abs_mul]
    have hu2 : |u - 1 / 2| ≤ 1 / 2 := abs_le.2 ⟨by linarith [hu.1], by linarith [hu.2]⟩
    calc |Δ| * |u - 1 / 2| ≤ |Δ| * (1 / 2) := mul_le_mul_of_nonneg_left hu2 (abs_nonneg _)
      _ = |Δ| / 2 := by ring
  have hYb : ∀ᵐ u ∂uniformIco, |Y u| ≤ 3 * ε * h := by
    refine ae_restrict_of_forall_mem measurableSet_Ico (fun u hu ↦ ?_)
    have heq : Y u = f (a + u * h) - h⁻¹ * (∫ x in a..a + h, f x) -
        (u - 1 / 2) * (f (a + h) - f a) := by
      simp only [hY, hX, hc, hΔ]
      ring
    rw [heq]
    exact cell_error_le hh hf hε (Ico_subset_Icc_self hu)
  have hmvt := abs_sub_sub_deriv_mul_le hh hf hε (right_mem_Icc.2 hah)
  rw [add_sub_cancel_left] at hmvt
  have hΔb : |Δ| ≤ (L + ε) * h := by
    have h1 : |f' a * h| ≤ L * h := by
      rw [abs_mul, abs_of_pos hh]
      exact mul_le_mul_of_nonneg_right hL hh.le
    have h2 : |Δ| ≤ |Δ - f' a * h| + |f' a * h| := by
      have := abs_add_le (Δ - f' a * h) (f' a * h)
      rwa [sub_add_cancel] at this
    linarith
  have b1 : |Var[fun u ↦ X u + Y u; uniformIco] - Δ ^ 2 / 12| ≤
      6 * ε * (L + 4 * ε) * h ^ 2 := by
    rw [← hVX]
    refine (abs_variance_add_sub_le hXm hYm hXb hYb).trans ?_
    have hle : 2 * (|Δ| / 2) + 3 * ε * h ≤ (L + ε) * h + 3 * ε * h := by linarith
    calc 2 * (3 * ε * h) * (2 * (|Δ| / 2) + 3 * ε * h)
        ≤ 2 * (3 * ε * h) * ((L + ε) * h + 3 * ε * h) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = 6 * ε * (L + 4 * ε) * h ^ 2 := by ring
  have b2 : |Δ ^ 2 / 12 - (f' a * h) ^ 2 / 12| ≤ ε * (2 * L + ε) * h ^ 2 / 12 := by
    have heq : Δ ^ 2 / 12 - (f' a * h) ^ 2 / 12 = (Δ - f' a * h) * (Δ + f' a * h) / 12 := by
      ring
    have h3 : |Δ + f' a * h| ≤ (2 * L + ε) * h := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos hh]
      have := mul_le_mul_of_nonneg_right hL hh.le
      linarith
    rw [heq, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 12)]
    have h4 : |Δ - f' a * h| * |Δ + f' a * h| ≤ (ε * h) * ((2 * L + ε) * h) :=
      mul_le_mul hmvt h3 (abs_nonneg _) (by positivity)
    calc |Δ - f' a * h| * |Δ + f' a * h| / 12 ≤ (ε * h) * ((2 * L + ε) * h) / 12 :=
          div_le_div_of_nonneg_right h4 (by norm_num)
      _ = ε * (2 * L + ε) * h ^ 2 / 12 := by ring
  rw [hVar]
  have key : ε * (7 * L + 25 * ε) * h ^ 2 -
      (6 * ε * (L + 4 * ε) * h ^ 2 + ε * (2 * L + ε) * h ^ 2 / 12) =
        ε * h ^ 2 * (5 * L / 6 + 11 * ε / 12) := by ring
  have hpos : 0 ≤ ε * h ^ 2 * (5 * L / 6 + 11 * ε / 12) := by positivity
  have htri : |Var[fun u ↦ X u + Y u; uniformIco] - (f' a * h) ^ 2 / 12| ≤
      |Var[fun u ↦ X u + Y u; uniformIco] - Δ ^ 2 / 12| +
        |Δ ^ 2 / 12 - (f' a * h) ^ 2 / 12| := abs_sub_le _ _ _
  linarith

/-- **Integral of `f'²` on one cell**: if `|f' − f'(a)| ≤ ε` on `[a, a + h]` and `|f'(a)| ≤ L`,
then `|∫ₐ^{a+h} f'² − f'(a)² h| ≤ ε (2L + ε) h`. -/
theorem abs_integral_sq_deriv_sub_le {f' : ℝ → ℝ} {a h ε L : ℝ} (hh : 0 < h)
    (hc : ContinuousOn f' (Icc a (a + h))) (hε : ∀ x ∈ Icc a (a + h), |f' x - f' a| ≤ ε)
    (hL : |f' a| ≤ L) :
    |(∫ x in a..a + h, f' x ^ 2) - f' a ^ 2 * h| ≤ ε * (2 * L + ε) * h := by
  have hah : a ≤ a + h := by linarith
  have hint : IntervalIntegrable (fun x ↦ f' x ^ 2) MeasureTheory.volume a (a + h) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hah]
    exact hc.pow 2
  have heq : (∫ x in a..a + h, f' x ^ 2) - f' a ^ 2 * h =
      ∫ x in a..a + h, (f' x ^ 2 - f' a ^ 2) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left, mul_comm]
  rw [heq]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := a + h)
    (f := fun x ↦ f' x ^ 2 - f' a ^ 2) (C := ε * (2 * L + ε)) (fun x hx ↦ by
      rw [uIoc_of_le hah] at hx
      have hx' := hε x (Ioc_subset_Icc_self hx)
      rw [Real.norm_eq_abs]
      have hfac : f' x ^ 2 - f' a ^ 2 = (f' x - f' a) * (f' x - f' a + 2 * f' a) := by ring
      rw [hfac, abs_mul]
      have h2 : |f' x - f' a + 2 * f' a| ≤ ε + 2 * L := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_two]
        linarith
      have hε0 : 0 ≤ ε := (abs_nonneg _).trans hx'
      calc |f' x - f' a| * |f' x - f' a + 2 * f' a| ≤ ε * (ε + 2 * L) :=
            mul_le_mul hx' h2 (abs_nonneg _) hε0
        _ = ε * (2 * L + ε) := by ring)
  rw [Real.norm_eq_abs, add_sub_cancel_left, abs_of_pos hh] at h
  exact h

/-- **One cell, combined**: `|h⁻¹ Var_u f(a + u h) − (1/12) ∫ₐ^{a+h} f'²| ≤ c(ε, L) h` with
`c(ε, L) = ε (7L + 25ε) + ε (2L + ε)/12`. -/
theorem abs_inv_mul_variance_cell_sub_le {f f' : ℝ → ℝ} {a h ε L : ℝ} (hh : 0 < h)
    (hf : ∀ x ∈ Icc a (a + h), HasDerivWithinAt f (f' x) (Icc a (a + h)) x)
    (hc : ContinuousOn f' (Icc a (a + h))) (hε : ∀ x ∈ Icc a (a + h), |f' x - f' a| ≤ ε)
    (hL : |f' a| ≤ L) :
    |h⁻¹ * Var[fun u ↦ f (a + u * h); uniformIco] - (∫ x in a..a + h, f' x ^ 2) / 12| ≤
      (ε * (7 * L + 25 * ε) + ε * (2 * L + ε) / 12) * h := by
  have h1 := abs_variance_cell_sub_le hh hf hε hL
  have h2 := abs_integral_sq_deriv_sub_le hh hc hε hL
  have heq : h⁻¹ * Var[fun u ↦ f (a + u * h); uniformIco] - (∫ x in a..a + h, f' x ^ 2) / 12 =
      h⁻¹ * (Var[fun u ↦ f (a + u * h); uniformIco] - (f' a * h) ^ 2 / 12) -
        ((∫ x in a..a + h, f' x ^ 2) - f' a ^ 2 * h) / 12 := by
    field_simp
    ring
  rw [heq]
  have hinv : 0 < h⁻¹ := inv_pos.2 hh
  have b1 : |h⁻¹ * (Var[fun u ↦ f (a + u * h); uniformIco] - (f' a * h) ^ 2 / 12)| ≤
      ε * (7 * L + 25 * ε) * h := by
    rw [abs_mul, abs_of_pos hinv]
    calc h⁻¹ * |Var[fun u ↦ f (a + u * h); uniformIco] - (f' a * h) ^ 2 / 12|
        ≤ h⁻¹ * (ε * (7 * L + 25 * ε) * h ^ 2) := mul_le_mul_of_nonneg_left h1 hinv.le
      _ = ε * (7 * L + 25 * ε) * h := by
          field_simp
  have b2 : |((∫ x in a..a + h, f' x ^ 2) - f' a ^ 2 * h) / 12| ≤ ε * (2 * L + ε) / 12 * h := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 12)]
    calc |(∫ x in a..a + h, f' x ^ 2) - f' a ^ 2 * h| / 12 ≤ ε * (2 * L + ε) * h / 12 :=
          div_le_div_of_nonneg_right h2 (by norm_num)
      _ = ε * (2 * L + ε) / 12 * h := by ring
  calc |h⁻¹ * (Var[fun u ↦ f (a + u * h); uniformIco] - (f' a * h) ^ 2 / 12) -
        ((∫ x in a..a + h, f' x ^ 2) - f' a ^ 2 * h) / 12|
      ≤ |h⁻¹ * (Var[fun u ↦ f (a + u * h); uniformIco] - (f' a * h) ^ 2 / 12)| +
        |((∫ x in a..a + h, f' x ^ 2) - f' a ^ 2 * h) / 12| := abs_sub _ _
    _ ≤ ε * (7 * L + 25 * ε) * h + ε * (2 * L + ε) / 12 * h := add_le_add b1 b2
    _ = (ε * (7 * L + 25 * ε) + ε * (2 * L + ε) / 12) * h := by ring

/-- **The exact rate of the stratified (= Owen-scrambled net) variance**: for `f` `C¹` on
`[0,1]`, `n³ σₙ² → (1/12) ∫₀¹ f'(x)² dx` as `n → ∞`. -/
theorem tendsto_cube_mul_stratVar {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 3 * stratVar n f) atTop
      (𝓝 ((∫ x in (0 : ℝ)..1, f' x ^ 2) / 12)) := by
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn hf'
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0 (left_mem_Icc.2 zero_le_one))
  have huc : UniformContinuousOn f' (Icc 0 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf'
  rw [Metric.tendsto_atTop]
  intro ε' hε'
  set K : ℝ := 9 * L + 26 with hK
  have hKpos : 0 < K := by positivity
  set ε : ℝ := min 1 (ε' / (2 * K)) with hεdef
  have hεpos : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεK : ε * K ≤ ε' / 2 := by
    have := min_le_right 1 (ε' / (2 * K))
    rw [← hεdef] at this
    calc ε * K ≤ ε' / (2 * K) * K := mul_le_mul_of_nonneg_right this hKpos.le
      _ = ε' / 2 := by field_simp
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.1 huc ε hεpos
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
  -- the scaled variance and the integral, cell by cell
  have hvar : (n : ℝ) ^ 3 * stratVar n f =
      ∑ k ∈ Finset.range n, h⁻¹ * Var[fun u ↦ f (a k + u * h); uniformIco] := by
    unfold stratVar
    rw [Fin.sum_univ_eq_sum_range (fun k ↦ Var[fun u ↦ f (stratumMap n k u); uniformIco]) n,
      ← mul_assoc, Finset.mul_sum]
    have hc : (n : ℝ) ^ 3 * ((n : ℝ)⁻¹) ^ 2 = h⁻¹ := by
      rw [hhdef, one_div, inv_inv]
      field_simp
    rw [hc]
    refine Finset.sum_congr rfl (fun k _ ↦ ?_)
    have hfun : (fun u ↦ f (stratumMap n k u)) = fun u ↦ f (a k + u * h) := by
      funext u
      congr 1
      simp only [stratumMap, hadef, hhdef]
      ring
    rw [hfun]
  have hint : (∫ x in (0 : ℝ)..1, f' x ^ 2) =
      ∑ k ∈ Finset.range n, ∫ x in a k..a k + h, f' x ^ 2 := by
    have hii : ∀ k < n, IntervalIntegrable (fun x ↦ f' x ^ 2) volume (a k) (a (k + 1)) := by
      intro k hk
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le (by rw [← ha k]; linarith), ← ha k]
      exact (hf'.mono (hcell k hk)).pow 2
    rw [← ha0, ← han, ← intervalIntegral.sum_integral_adjacent_intervals hii]
    refine Finset.sum_congr rfl (fun k _ ↦ ?_)
    rw [ha k]
  have hid : (n : ℝ) ^ 3 * stratVar n f - (∫ x in (0 : ℝ)..1, f' x ^ 2) / 12 =
      ∑ k ∈ Finset.range n, (h⁻¹ * Var[fun u ↦ f (a k + u * h); uniformIco] -
        (∫ x in a k..a k + h, f' x ^ 2) / 12) := by
    rw [hvar, hint, Finset.sum_div, ← Finset.sum_sub_distrib]
  have hbound : ∀ k ∈ Finset.range n, |h⁻¹ * Var[fun u ↦ f (a k + u * h); uniformIco] -
      (∫ x in a k..a k + h, f' x ^ 2) / 12| ≤
        (ε * (7 * L + 25 * ε) + ε * (2 * L + ε) / 12) * h := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    have hsub := hcell k hk'
    have hak : a k ∈ Icc (0 : ℝ) 1 := hsub (left_mem_Icc.2 (by linarith))
    refine abs_inv_mul_variance_cell_sub_le hh (fun x hx ↦ (hf x (hsub hx)).mono hsub)
      (hf'.mono hsub) (fun x hx ↦ ?_) ?_
    · have hdist : dist x (a k) < δ := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith [hx.1])]
        linarith [hx.2]
      have := hδf x (hsub hx) (a k) hak hdist
      rw [Real.dist_eq] at this
      exact this.le
    · have := hL (a k) hak
      rwa [Real.norm_eq_abs] at this
  have hcK : ε * (7 * L + 25 * ε) + ε * (2 * L + ε) / 12 ≤ ε * K := by
    have h1 : ε * (7 * L + 25 * ε) ≤ ε * (7 * L + 25) := by
      have : 7 * L + 25 * ε ≤ 7 * L + 25 := by linarith
      exact mul_le_mul_of_nonneg_left this hεpos.le
    have h2 : ε * (2 * L + ε) / 12 ≤ ε * (2 * L + 1) := by
      have : ε * (2 * L + ε) ≤ ε * (2 * L + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hεpos.le
      have h0 : 0 ≤ ε * (2 * L + 1) := by positivity
      linarith
    have h3 : ε * (7 * L + 25) + ε * (2 * L + 1) = ε * K := by
      rw [hK]
      ring
    linarith
  rw [Real.dist_eq, hid]
  calc |∑ k ∈ Finset.range n, (h⁻¹ * Var[fun u ↦ f (a k + u * h); uniformIco] -
          (∫ x in a k..a k + h, f' x ^ 2) / 12)|
      ≤ ∑ k ∈ Finset.range n, |h⁻¹ * Var[fun u ↦ f (a k + u * h); uniformIco] -
          (∫ x in a k..a k + h, f' x ^ 2) / 12| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range n, (ε * (7 * L + 25 * ε) + ε * (2 * L + ε) / 12) * h :=
        Finset.sum_le_sum hbound
    _ = ε * (7 * L + 25 * ε) + ε * (2 * L + ε) / 12 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hhdef]
        field_simp
    _ ≤ ε * K := hcK
    _ ≤ ε' / 2 := hεK
    _ < ε' := by linarith

/-- **A non-constant `C¹` function has `∫₀¹ f'² > 0`.** -/
theorem integral_sq_deriv_pos {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) (hnc : ∃ x ∈ Icc (0 : ℝ) 1, f x ≠ f 0) :
    0 < ∫ x in (0 : ℝ)..1, f' x ^ 2 := by
  have hcont : ContinuousOn (fun x ↦ f' x ^ 2) (Icc 0 1) := hf'.pow 2
  rcases (intervalIntegral.integral_nonneg zero_le_one
      (fun x _ ↦ sq_nonneg (f' x))).lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  have hzero : ∀ x ∈ Icc (0 : ℝ) 1, f' x ^ 2 = 0 := by
    have hii : IntervalIntegrable (fun x ↦ f' x ^ 2) volume 0 1 :=
      hcont.intervalIntegrable_of_Icc zero_le_one
    have h := (intervalIntegral.integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun x ↦ sq_nonneg (f' x)) hii).1 heq.symm
    rw [Ioc_eq_empty (not_lt.2 zero_le_one), union_empty,
      Measure.restrict_congr_set Ioc_ae_eq_Icc] at h
    have hEq := Measure.eqOn_of_ae_eq h hcont continuousOn_const (fun x hx ↦ by
      rwa [interior_Icc, closure_Ioo zero_ne_one])
    exact fun x hx ↦ hEq hx
  obtain ⟨x, hx, hfx⟩ := hnc
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hf (C := 0) (fun y hy ↦ by
    rw [Real.norm_eq_abs, (pow_eq_zero_iff two_ne_zero).1 (hzero y (Ico_subset_Icc_self hy)),
      abs_zero]) x hx
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at h
  exact hfx h

/-- **The scrambled-net variance is eventually positive** for non-constant `C¹` `f`: since
`n³ σₙ² → ∫ f'²/12 > 0`, `σₙ² > 0` for all large `n`. -/
theorem eventually_stratVar_pos {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) (hnc : ∃ x ∈ Icc (0 : ℝ) 1, f x ≠ f 0) :
    ∀ᶠ n : ℕ in atTop, 0 < stratVar n f := by
  have hpos : 0 < (∫ x in (0 : ℝ)..1, f' x ^ 2) / 12 :=
    div_pos (integral_sq_deriv_pos hf hf' hnc) (by norm_num)
  filter_upwards [(tendsto_cube_mul_stratVar hf hf').eventually (lt_mem_nhds hpos)] with n hn
  exact pos_of_mul_pos_right hn (by positivity)

/-- **Constant integrands are integrated exactly**: `σₙ² = 0` for every `n` when `f` is constant,
so the normalised error `(μ̂ₙ − μ)/σₙ` is `0/0` and no CLT can hold. -/
theorem stratVar_const (n : ℕ) (c : ℝ) : stratVar n (fun _ ↦ c) = 0 := by
  have := isProbabilityMeasure_uniformIco
  have h0 : ∀ i : Fin n, Var[fun u ↦ (fun _ : ℝ ↦ c) (stratumMap n i u); uniformIco] = 0 := by
    intro i
    have h := variance_const_add (μ := uniformIco) (X := (0 : ℝ → ℝ)) aestronglyMeasurable_const c
    rw [variance_zero] at h
    have hfun : (fun u ↦ (fun _ : ℝ ↦ c) (stratumMap n i u)) = fun ω ↦ c + (0 : ℝ → ℝ) ω := by
      funext u
      rw [Pi.zero_apply, add_zero]
    rw [hfun, h]
  unfold stratVar
  rw [Finset.sum_eq_zero (fun i _ ↦ h0 i), mul_zero]

end RQMCMarkov.OwenScrambling

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The CLT for the Owen-scrambled net in one dimension (post #2, Loh 2003)

Post #2: "If we use an RQMC estimator with a digital net and nested uniform scrambling (Owen
scrambling) then a standard CLT applies and the asymptotic distribution is normally distributed"
(Loh 2003). Reading, in dimension `d = 1`, base `b ≥ 2`: the Owen-scrambled `(0,m,1)`-net
estimator `μ̂ₙ = (1/n) Σₖ f(owenNet T R k)`, `n = bᵐ`, normalised by its own standard deviation
`σₙ = √Var(μ̂ₙ)`, converges in distribution to `N(0,1)` as `m → ∞`.

## Main results

* `tendstoInDistribution_stratified`: for measurable `f`, `C¹` on `[0,1]` and not constant there,
  independent stratified sampling with `N k → ∞` cells satisfies
  `(μ̂ − μ)/σ ⇒ N(0,1)` (any number of cells, not only `bᵐ`; any probability spaces).
* `tendstoInDistribution_stratified_all_n`: the same along all `n`.
* Tools: `cellTerm` (the centred normalised cell terms, `sum_cellTerm`), `integrable_cell`,
  `inv_mul_sum_integral_cell`, `iIndepFun_coords`, `abs_cellTerm_le`, `exists_lipschitz_of_C1`,
  `memLp_uniformIco_of_continuousOn`, `sampleMean_owenNet_eq_stratPoints`.
* `tendstoInDistribution_owenNet` (**post #2's claim in `d = 1`**): the Owen-scrambled net,
  `(μ̂ₙ − μ)/σₙ ⇒ N(0,1)` as `n = bᵐ → ∞`.
* `variance_owenNet_eq_stratVar`, `tendsto_cube_mul_variance_owenNet`: `σₙ² = stratVar n f` and
  `n³ σₙ² → (1/12) ∫₀¹ f'²`, so the RMSE is of order `n^{-3/2}`.
* `owenNet_exact_of_const`, `not_tendstoInDistribution_owenNet_const`: the correction below.
* `owenNet_normal_and_shift_not_normal` (the contrast of post #2): for the same `f`, Owen
  scrambling gives a normal limit while the randomly shifted lattice (`ShiftLimit`) has the uniform
  limit `n (μ̂ₙ − μ) ⇒ (f(1) − f(0))(U − 1/2)` and no normal limit.

**Correction.** "A standard CLT applies" needs a non-degenerate integrand: for constant `f`
(`stratVar_const`, `owenNet_exact_of_const`) the scrambled-net estimator is exact, `σₙ = 0`, and the
normalised error is identically `0`, which converges to the point mass at `0`, not to `N(0,1)`
(`not_tendstoInDistribution_owenNet_const`). The corrected statement assumes `f` non-constant on
`[0,1]`, which for `C¹` `f` gives `σₙ > 0` eventually (`eventually_stratVar_pos`). Smoothness is
also needed: for the discontinuous `f = 1_{[0,1/3)}` (base 2) `σₙ > 0` but the normalised error is
bounded and has no normal limit (`not_tendstoInDistribution_owenNet_indicator` in
`Owen1DCounterexample`). The theorem also
does not need the tree to be uniform: any random permutation of the cells independent of the
remainders gives the same law of the estimator (uniformity is what makes each point `U[0,1)`).
-/

namespace RQMCMarkov.OwenScrambling

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

/-- The centred, normalised contribution of cell `i` to the stratified estimator:
`(f((i + u)/n) − E f((i + U)/n)) / (n σₙ)`, with `σₙ = √(stratVar n f)`. -/
noncomputable def cellTerm (n : ℕ) (f : ℝ → ℝ) (i : Fin n) (u : ℝ) : ℝ :=
  (f (stratumMap n i u) - ∫ x, f (stratumMap n i x) ∂uniformIco) /
    (n * Real.sqrt (stratVar n f))

/-- A stratified point of `[0,1]` stays in `[0,1]`. -/
theorem stratumMap_mem_Icc {n : ℕ} (i : Fin n) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    stratumMap n i u ∈ Icc (0 : ℝ) 1 := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (Fin.pos i).ne')
  have hi : (i : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
  simp only [stratumMap, mem_Icc]
  refine ⟨div_nonneg (by linarith [hu.1, (Nat.cast_nonneg i : (0 : ℝ) ≤ i)]) hn.le, ?_⟩
  rw [div_le_one hn]
  linarith [hu.2]

/-- For `f` continuous on `[0,1]`, the cell function `u ↦ f((i + u)/n)` is integrable on
`U[0,1)`. -/
theorem integrable_cell {f : ℝ → ℝ} (hc : ContinuousOn f (Icc 0 1)) {n : ℕ} (i : Fin n) :
    Integrable (fun u ↦ f (stratumMap n i u)) uniformIco := by
  have hg : ContinuousOn (fun u ↦ f (stratumMap n i u)) (Icc 0 1) :=
    hc.comp (continuous_stratumMap n i).continuousOn (fun u hu ↦ stratumMap_mem_Icc i hu)
  exact (hg.integrableOn_Icc).mono_set Ico_subset_Icc_self

/-- **The cell means average to the integral**: `(1/n) Σᵢ E f((i + U)/n) = ∫₀¹ f`. -/
theorem inv_mul_sum_integral_cell {f : ℝ → ℝ} (hc : ContinuousOn f (Icc 0 1)) {n : ℕ}
    (hn : n ≠ 0) :
    (n : ℝ)⁻¹ * ∑ i : Fin n, ∫ x, f (stratumMap n i x) ∂uniformIco = ∫ x, f x ∂uniformIco := by
  have := isProbabilityMeasure_uniformIco
  have hfi : Integrable f uniformIco :=
    (hc.integrableOn_Icc (a := 0) (b := 1)).mono_set Ico_subset_Icc_self
  have h := integral_sampleMean_stratified hn (P := uniformCube n)
    (V := fun i v ↦ v i) hasLaw_eval_uniformCube hfi
  rw [← h]
  unfold sampleMean
  rw [integral_const_mul, integral_finsetSum]
  · congr 1
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    have := (hasLaw_eval_uniformCube (n := n) i).integral_comp
      (integrable_cell hc i).aestronglyMeasurable
    exact this.symm
  · intro i _
    exact (hasLaw_eval_uniformCube (n := n) i).integrable_comp (integrable_cell hc i)

/-- **The normalised error is the sum of the cell terms**: for every `v`,
`(μ̂(v) − ∫₀¹ f)/σₙ = Σᵢ cellTerm n f i (vᵢ)`. -/
theorem sum_cellTerm {f : ℝ → ℝ} (hc : ContinuousOn f (Icc 0 1)) (n : ℕ) (v : Fin n → ℝ) :
    ∑ i, cellTerm n f i (v i) =
      (sampleMean n f (stratPoints n v) - ∫ x, f x ∂uniformIco) / Real.sqrt (stratVar n f) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    have hs : stratVar 0 f = 0 := by
      unfold stratVar
      rw [Nat.cast_zero, inv_zero, zero_pow two_ne_zero, zero_mul]
    rw [hs, Real.sqrt_zero, div_zero]
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hpos.ne'
  have hmean := inv_mul_sum_integral_cell hc hpos.ne'
  unfold cellTerm
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← div_div, ← hmean]
  congr 1
  unfold sampleMean stratPoints
  field_simp

/-- The coordinates of a `U[0,1)ⁿ` vector are independent. -/
theorem iIndepFun_coords {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {V : Ω → Fin n → ℝ} (hV : HasLaw V (uniformCube n) P) :
    iIndepFun (fun i ω ↦ V ω i) P := by
  have := isProbabilityMeasure_uniformIco
  have hc : ∀ i : Fin n, HasLaw (fun ω ↦ V ω i) uniformIco P := fun i ↦
    (hasLaw_eval_uniformCube i).comp hV
  exact (iIndepFun_iff_hasLaw_pi_pi hc).2 hV

/-- A cell term is bounded: if `|f x − f y| ≤ K |x − y|` on `[0,1]` then
`|cellTerm n f i u| ≤ (K/n)/(n σₙ)` for `u ∈ [0,1)`. -/
theorem abs_cellTerm_le {f : ℝ → ℝ} (hc : ContinuousOn f (Icc 0 1)) {K : ℝ}
    (hK : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |f x - f y| ≤ K * |x - y|) {n : ℕ}
    (i : Fin n) {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) :
    |cellTerm n f i u| ≤ (K / n) / (n * Real.sqrt (stratVar n f)) := by
  have := isProbabilityMeasure_uniformIco
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (Fin.pos i).ne')
  have hK0 : 0 ≤ K := by
    have h := hK 1 (right_mem_Icc.2 zero_le_one) 0 (left_mem_Icc.2 zero_le_one)
    rw [sub_zero, abs_one, mul_one] at h
    exact (abs_nonneg _).trans h
  have hpt : ∀ x ∈ Ico (0 : ℝ) 1, |f (stratumMap n i u) - f (stratumMap n i x)| ≤ K / n := by
    intro x hx
    refine (hK _ (stratumMap_mem_Icc i (Ico_subset_Icc_self hu)) _
      (stratumMap_mem_Icc i (Ico_subset_Icc_self hx))).trans ?_
    have heq : stratumMap n i u - stratumMap n i x = (u - x) / n := by
      simp only [stratumMap]
      ring
    rw [heq, abs_div, abs_of_pos hn]
    have hux : |u - x| ≤ 1 := abs_le.2 ⟨by linarith [hu.1, hx.2], by linarith [hu.2, hx.1]⟩
    calc K * (|u - x| / n) ≤ K * (1 / n) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hux hn.le) hK0
      _ = K / n := by ring
  have hdiff : |f (stratumMap n i u) - ∫ x, f (stratumMap n i x) ∂uniformIco| ≤ K / n := by
    have heq : f (stratumMap n i u) - ∫ x, f (stratumMap n i x) ∂uniformIco =
        ∫ x, (f (stratumMap n i u) - f (stratumMap n i x)) ∂uniformIco := by
      rw [integral_sub (integrable_const _) (integrable_cell hc i), integral_const,
        probReal_univ, one_smul]
    rw [heq]
    have h := norm_integral_le_of_norm_le_const (μ := uniformIco)
      (f := fun x ↦ f (stratumMap n i u) - f (stratumMap n i x)) (C := K / n)
      (ae_restrict_of_forall_mem measurableSet_Ico fun x hx ↦ by
        rw [Real.norm_eq_abs]
        exact hpt x hx)
    rwa [probReal_univ, mul_one, Real.norm_eq_abs] at h
  unfold cellTerm
  rw [abs_div, abs_of_nonneg (mul_nonneg hn.le (Real.sqrt_nonneg _))]
  exact div_le_div_of_nonneg_right hdiff (mul_nonneg hn.le (Real.sqrt_nonneg _))

/-- A `C¹` function on `[0,1]` is Lipschitz there with constant `sup |f'|`. -/
theorem exists_lipschitz_of_C1 {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) :
    ∃ K : ℝ, ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |f x - f y| ≤ K * |x - y| := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hf'
  refine ⟨K, fun x hx y hy ↦ ?_⟩
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hf hK (convex_Icc 0 1) hy hx
  rwa [Real.norm_eq_abs, Real.norm_eq_abs] at h

/-- **CLT for independent stratified sampling** (any number of cells): let `f` be measurable,
`C¹` on `[0,1]` and not constant there. For probability spaces `(Ωₖ, Pₖ)` carrying
`Vₖ ~ U[0,1)^(Nₖ)` with `Nₖ → ∞`, the stratified estimator
`μ̂ₖ = (1/Nₖ) Σᵢ f((i + Vₖ i)/Nₖ)` satisfies `(μ̂ₖ − ∫₀¹ f)/σ_{Nₖ} ⇒ N(0,1)`, with
`σₙ² = stratVar n f` its variance. -/
theorem tendstoInDistribution_stratified {f f' : ℝ → ℝ} (hfm : Measurable f)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) (hnc : ∃ x ∈ Icc (0 : ℝ) 1, f x ≠ f 0)
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) {Ω : ℕ → Type*} {mΩ : ∀ k, MeasurableSpace (Ω k)}
    {P : (k : ℕ) → Measure (Ω k)} [∀ k, IsProbabilityMeasure (P k)]
    {V : (k : ℕ) → Ω k → Fin (N k) → ℝ} (hV : ∀ k, HasLaw (V k) (uniformCube (N k)) (P k))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦ (sampleMean (N k) f (stratPoints (N k) (V k ω)) -
      ∫ x, f x ∂uniformIco) / Real.sqrt (stratVar (N k) f)) atTop Z P P' := by
  have := isProbabilityMeasure_uniformIco
  have hc : ContinuousOn f (Icc 0 1) := fun x hx ↦ (hf x hx).continuousWithinAt
  obtain ⟨K, hK⟩ := exists_lipschitz_of_C1 hf hf'
  have hcoord : ∀ k (i : Fin (N k)), HasLaw (fun ω ↦ V k ω i) uniformIco (P k) := fun k i ↦
    (hasLaw_eval_uniformCube i).comp (hV k)
  have hcm : ∀ n (i : Fin n), Measurable (cellTerm n f i) := fun n i ↦
    ((hfm.comp (measurable_stratumMap n i)).sub_const _).div_const _
  have hfun : (fun k ω ↦ (sampleMean (N k) f (stratPoints (N k) (V k ω)) -
      ∫ x, f x ∂uniformIco) / Real.sqrt (stratVar (N k) f)) =
      fun k ω ↦ ∑ i, cellTerm (N k) f i (V k ω i) := by
    funext k ω
    rw [sum_cellTerm hc]
  rw [hfun]
  -- the asymptotics of the variance
  set c : ℝ := (∫ x in (0 : ℝ)..1, f' x ^ 2) / 12 with hcdef
  have hcpos : 0 < c := div_pos (integral_sq_deriv_pos hf hf' hnc) (by norm_num)
  have hlim : Tendsto (fun k ↦ (N k : ℝ) ^ 3 * stratVar (N k) f) atTop (𝓝 c) :=
    (tendsto_cube_mul_stratVar hf hf').comp hN
  have hspos : ∀ᶠ k in atTop, 0 < stratVar (N k) f :=
    hN.eventually (eventually_stratVar_pos hf hf' hnc)
  have hNpos : ∀ᶠ k in atTop, 0 < N k := hN.eventually (eventually_gt_atTop 0)
  set δ : ℕ → ℝ := fun k ↦ (K / N k) / (N k * Real.sqrt (stratVar (N k) f)) with hδdef
  have hδ0 : ∀ k, 0 ≤ δ k := by
    intro k
    rcases le_or_gt 0 K with hK0 | hK0
    · exact div_nonneg (div_nonneg hK0 (Nat.cast_nonneg _))
        (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
    · rcases Nat.eq_zero_or_pos (N k) with h0 | hp
      · simp only [hδdef, h0, Nat.cast_zero, div_zero, zero_div, le_refl]
      · have h := hK 1 (right_mem_Icc.2 zero_le_one) 0 (left_mem_Icc.2 zero_le_one)
        rw [sub_zero, abs_one, mul_one] at h
        linarith [abs_nonneg (f 1 - f 0)]
  have hδsq : ∀ᶠ k in atTop, δ k ^ 2 = K ^ 2 / N k * ((N k : ℝ) ^ 3 * stratVar (N k) f)⁻¹ := by
    filter_upwards [hspos, hNpos] with k hs hNk
    have hNr : (0 : ℝ) < N k := Nat.cast_pos.2 hNk
    have hsq : Real.sqrt (stratVar (N k) f) ^ 2 = stratVar (N k) f := Real.sq_sqrt hs.le
    simp only [hδdef]
    rw [div_pow, div_pow, mul_pow, hsq]
    field_simp
  have hδ2lim : Tendsto (fun k ↦ δ k ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k ↦ K ^ 2 / (N k : ℝ)) atTop (𝓝 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat (K ^ 2)).comp hN
    have h2 := h1.mul (hlim.inv₀ hcpos.ne')
    rw [zero_mul] at h2
    exact h2.congr' (hδsq.mono fun k hk ↦ hk.symm)
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hδ2lim
    rw [Real.sqrt_zero] at h
    refine h.congr (fun k ↦ ?_)
    change Real.sqrt (δ k ^ 2) = δ k
    exact Real.sqrt_sq (hδ0 k)
  refine tendstoInDistribution_sum_of_bounded (L := N)
    (X := fun k i ω ↦ cellTerm (N k) f i (V k ω i))
    (fun k i ↦ (hcm _ i).comp_aemeasurable (hcoord k i).aemeasurable)
    (fun k ↦ (iIndepFun_coords (hV k)).comp _ (fun i ↦ hcm _ i))
    (fun k i ↦ ?_) hδlim (fun k i ↦ ?_) (v := 1) ?_ (by rw [Real.toNNReal_one]; exact hZ)
  · -- centred
    change ∫ ω, (cellTerm (N k) f i ∘ fun ω ↦ V k ω i) ω ∂(P k) = 0
    rw [(hcoord k i).integral_comp (hcm _ i).aestronglyMeasurable]
    unfold cellTerm
    rw [integral_div, integral_sub (integrable_cell hc i) (integrable_const _), integral_const,
      probReal_univ, one_smul, sub_self, zero_div]
  · -- bounded
    filter_upwards [ae_mem_Ico_of_hasLaw (hcoord k i)] with ω hω
    exact abs_cellTerm_le hc hK i hω
  · -- the variances sum to one, eventually
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hspos] with k hs
    have hNk : N k ≠ 0 := by
      rintro h0
      have : stratVar (N k) f = 0 := by
        unfold stratVar
        rw [h0, Nat.cast_zero, inv_zero, zero_pow two_ne_zero, zero_mul]
      rw [this] at hs
      exact lt_irrefl 0 hs
    have hNr : (N k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hNk
    have hsq : Real.sqrt (stratVar (N k) f) ^ 2 = stratVar (N k) f := Real.sq_sqrt hs.le
    have hterm : ∀ i : Fin (N k), ∫ ω, cellTerm (N k) f i (V k ω i) ^ 2 ∂(P k) =
        Var[fun u ↦ f (stratumMap (N k) i u); uniformIco] /
          ((N k : ℝ) ^ 2 * stratVar (N k) f) := by
      intro i
      change ∫ ω, ((fun u ↦ cellTerm (N k) f i u ^ 2) ∘ fun ω ↦ V k ω i) ω ∂(P k) = _
      rw [(hcoord k i).integral_comp ((hcm _ i).pow_const 2).aestronglyMeasurable,
        variance_eq_integral (X := fun u ↦ f (stratumMap (N k) i u))
          (hfm.comp (measurable_stratumMap _ i)).aemeasurable]
      unfold cellTerm
      rw [← integral_div]
      congr 1
      funext u
      rw [div_pow, mul_pow, hsq]
    rw [Finset.sum_congr rfl (fun i _ ↦ hterm i), ← Finset.sum_div]
    have hS : (N k : ℝ) ^ 2 * stratVar (N k) f =
        ∑ i : Fin (N k), Var[fun u ↦ f (stratumMap (N k) i u); uniformIco] := by
      unfold stratVar
      field_simp
    have hS0 : ∑ i : Fin (N k), Var[fun u ↦ f (stratumMap (N k) i u); uniformIco] ≠ 0 := by
      rw [← hS]
      exact (mul_pos (by positivity) hs).ne'
    rw [hS, div_self hS0]

/-- **CLT for independent stratification with `n` cells, along all `n`** (target 3): for each `n`
let `Vₙ ~ U[0,1)ⁿ` on `(Ωₙ, Pₙ)`; then `(μ̂ₙ − ∫₀¹ f)/σₙ ⇒ N(0,1)` for every measurable `f`
that is `C¹` and non-constant on `[0,1]`. -/
theorem tendstoInDistribution_stratified_all_n {f f' : ℝ → ℝ} (hfm : Measurable f)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) (hnc : ∃ x ∈ Icc (0 : ℝ) 1, f x ≠ f 0)
    {Ω : ℕ → Type*} {mΩ : ∀ n, MeasurableSpace (Ω n)} {P : (n : ℕ) → Measure (Ω n)}
    [∀ n, IsProbabilityMeasure (P n)] {V : (n : ℕ) → Ω n → Fin n → ℝ}
    (hV : ∀ n, HasLaw (V n) (uniformCube n) (P n))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun n ω ↦ (sampleMean n f (stratPoints n (V n ω)) -
      ∫ x, f x ∂uniformIco) / Real.sqrt (stratVar n f)) atTop Z P P' :=
  tendstoInDistribution_stratified hfm hf hf' hnc (N := id) tendsto_id hV hZ

/-- The scrambled-net estimator is the stratified estimator of the relabelled remainders. -/
theorem sampleMean_owenNet_eq_stratPoints {b m : ℕ} (T : OwenTree b m) (r : Fin (b ^ m) → ℝ)
    (f : ℝ → ℝ) :
    sampleMean (b ^ m) f (owenNet T r) =
      sampleMean (b ^ m) f (stratPoints (b ^ m) (owenRemainder T r)) := by
  rw [sampleMean_owenNet, owenNetSorted_eq_stratPoints]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {b : ℕ}
  {mT : ∀ m, MeasurableSpace (OwenTree b m)} [∀ m, DiscreteMeasurableSpace (OwenTree b m)]

/-- **Post #2's CLT for Owen scrambling, one dimension** (Loh 2003 in `d = 1`): let `b ≥ 2`, and
for each `m` let the scrambling tree `T m` be independent of the remainders `R m ~ U[0,1)^(bᵐ)`.
For measurable `f`, `C¹` and non-constant on `[0,1]`, the Owen-scrambled net estimator
`μ̂ₙ = (1/n) Σₖ f(owenNet (T m) (R m) k)`, `n = bᵐ`, satisfies `(μ̂ₙ − ∫₀¹ f)/σₙ ⇒ N(0,1)`, where
`σₙ² = stratVar n f = Var(μ̂ₙ)` (`variance_owenNet_eq_stratVar`). -/
theorem tendstoInDistribution_owenNet (hb : 1 < b) {f f' : ℝ → ℝ} (hfm : Measurable f)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) (hnc : ∃ x ∈ Icc (0 : ℝ) 1, f x ≠ f 0)
    {P : Measure Ω} [IsProbabilityMeasure P] {T : (m : ℕ) → Ω → OwenTree b m}
    {R : (m : ℕ) → Ω → Fin (b ^ m) → ℝ} (hT : ∀ m, Measurable (T m)) (hR : ∀ m, Measurable (R m))
    (hRlaw : ∀ m, HasLaw (R m) (uniformCube (b ^ m)) P) (hind : ∀ m, IndepFun (T m) (R m) P)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun m ω ↦ (sampleMean (b ^ m) f (owenNet (T m ω) (R m ω)) -
      ∫ x, f x ∂uniformIco) / Real.sqrt (stratVar (b ^ m) f)) atTop Z (fun _ ↦ P) P' := by
  have hfun : (fun m ω ↦ (sampleMean (b ^ m) f (owenNet (T m ω) (R m ω)) -
      ∫ x, f x ∂uniformIco) / Real.sqrt (stratVar (b ^ m) f)) =
      fun m ω ↦ (sampleMean (b ^ m) f (stratPoints (b ^ m) (owenRemainder (T m ω) (R m ω))) -
        ∫ x, f x ∂uniformIco) / Real.sqrt (stratVar (b ^ m) f) := by
    funext m ω
    rw [sampleMean_owenNet_eq_stratPoints]
  rw [hfun]
  exact tendstoInDistribution_stratified hfm hf hf' hnc (N := fun m ↦ b ^ m)
    (tendsto_pow_atTop_atTop_of_one_lt hb) (Ω := fun _ ↦ Ω) (P := fun _ ↦ P)
    (V := fun m ω ↦ owenRemainder (T m ω) (R m ω))
    (fun m ↦ hasLaw_owenRemainder (hT m) (hR m) (hRlaw m) (hind m)) hZ

/-- A function continuous on `[0,1]` is in `L^p(U[0,1))` when measurable. -/
theorem memLp_uniformIco_of_continuousOn {f : ℝ → ℝ} (hfm : Measurable f)
    (hc : ContinuousOn f (Icc 0 1)) (p : ℝ≥0∞) : MemLp f p uniformIco := by
  have := isProbabilityMeasure_uniformIco
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  exact MemLp.of_bound hfm.aestronglyMeasurable C
    (ae_restrict_of_forall_mem measurableSet_Ico fun x hx ↦ hC x (Ico_subset_Icc_self hx))

/-- **The variance of the scrambled net is `stratVar`**: `Var(μ̂ₙ) = σₙ² = stratVar (bᵐ) f`. -/
theorem variance_owenNet_eq_stratVar (hb : b ≠ 0) {m : ℕ} {f : ℝ → ℝ} (hfm : Measurable f)
    (hc : ContinuousOn f (Icc 0 1)) {P : Measure Ω} [IsProbabilityMeasure P]
    {T : Ω → OwenTree b m} {R : Ω → Fin (b ^ m) → ℝ} (hT : Measurable T) (hR : Measurable R)
    (hRlaw : HasLaw R (uniformCube (b ^ m)) P) (hind : IndepFun T R P) :
    Var[fun ω ↦ sampleMean (b ^ m) f (owenNet (T ω) (R ω)); P] = stratVar (b ^ m) f :=
  variance_sampleMean_owenNet hb hT hR hRlaw hind hfm (memLp_uniformIco_of_continuousOn hfm hc 2)

/-- **The rate of the scrambled net**: `n³ Var(μ̂ₙ) → (1/12) ∫₀¹ f'²` as `n = bᵐ → ∞`, so the
RMSE is `n^{-3/2} (∫₀¹ f'²/12)^{1/2} (1 + o(1))`. -/
theorem tendsto_cube_mul_variance_owenNet (hb : 1 < b) {f f' : ℝ → ℝ} (hfm : Measurable f)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) {P : Measure Ω} [IsProbabilityMeasure P]
    {T : (m : ℕ) → Ω → OwenTree b m} {R : (m : ℕ) → Ω → Fin (b ^ m) → ℝ}
    (hT : ∀ m, Measurable (T m)) (hR : ∀ m, Measurable (R m))
    (hRlaw : ∀ m, HasLaw (R m) (uniformCube (b ^ m)) P) (hind : ∀ m, IndepFun (T m) (R m) P) :
    Tendsto (fun m ↦ ((b ^ m : ℕ) : ℝ) ^ 3 *
        Var[fun ω ↦ sampleMean (b ^ m) f (owenNet (T m ω) (R m ω)); P]) atTop
      (𝓝 ((∫ x in (0 : ℝ)..1, f' x ^ 2) / 12)) := by
  have hc : ContinuousOn f (Icc 0 1) := fun x hx ↦ (hf x hx).continuousWithinAt
  have h := (tendsto_cube_mul_stratVar hf hf').comp (tendsto_pow_atTop_atTop_of_one_lt hb)
  refine h.congr (fun m ↦ ?_)
  change ((b ^ m : ℕ) : ℝ) ^ 3 * stratVar (b ^ m) f = _
  rw [variance_owenNet_eq_stratVar (by omega) hfm hc (hT m) (hR m) (hRlaw m) (hind m)]

/-- **Post #2's contrast, as a theorem pair** (one dimension, the same `C¹` non-constant `f`):
(1) the Owen-scrambled net is asymptotically normal, `(μ̂ₙ − μ)/σₙ ⇒ N(0,1)`; (2) the randomly
shifted lattice `(1/n) Σᵢ f((i + U)/n)` has the uniform limit
`n (μ̂ₙ − μ) ⇒ (f(1) − f(0))(U − 1/2)` and (3) does not converge to any normal `N(m₀, v)`, `v ≠ 0`
(`ShiftLimit`). -/
theorem owenNet_normal_and_shift_not_normal (hb : 1 < b) {f f' : ℝ → ℝ} (hfm : Measurable f)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) (hnc : ∃ x ∈ Icc (0 : ℝ) 1, f x ≠ f 0)
    {P : Measure Ω} [IsProbabilityMeasure P] {T : (m : ℕ) → Ω → OwenTree b m}
    {R : (m : ℕ) → Ω → Fin (b ^ m) → ℝ} (hT : ∀ m, Measurable (T m)) (hR : ∀ m, Measurable (R m))
    (hRlaw : ∀ m, HasLaw (R m) (uniformCube (b ^ m)) P) (hind : ∀ m, IndepFun (T m) (R m) P)
    {U : Ω → ℝ} (hU : HasLaw U uniformIco P)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') {Y : Ω' → ℝ} (m₀ : ℝ) {v : ℝ≥0}
    (hv : v ≠ 0) (hY : HasLaw Y (gaussianReal m₀ v) P') :
    TendstoInDistribution (fun m ω ↦ (sampleMean (b ^ m) f (owenNet (T m ω) (R m ω)) -
      ∫ x, f x ∂uniformIco) / Real.sqrt (stratVar (b ^ m) f)) atTop Z (fun _ ↦ P) P' ∧
    TendstoInDistribution (fun (n : ℕ) ω ↦ (n : ℝ) *
        (sampleMean n f (fun i ↦ stratumMap n i (U ω)) - ∫ x in (0 : ℝ)..1, f x))
      atTop (fun ω ↦ (f 1 - f 0) * (U ω - 1 / 2)) (fun _ ↦ P) P ∧
    ¬ TendstoInDistribution (fun (n : ℕ) ω ↦ (n : ℝ) *
        (sampleMean n f (fun i ↦ stratumMap n i (U ω)) - ∫ x in (0 : ℝ)..1, f x))
      atTop Y (fun _ ↦ P) P' :=
  ⟨tendstoInDistribution_owenNet hb hfm hf hf' hnc hT hR hRlaw hind hZ,
    tendstoInDistribution_scaled_error hfm hf hf' hU,
    not_tendstoInDistribution_scaled_error_gaussian hfm hf hf' hU m₀ hv hY⟩

/-- **Correction: constant integrands are integrated exactly** by the scrambled net: for
`f ≡ c`, `μ̂ₙ = c = ∫₀¹ f` for every realisation, so `σₙ = 0` (`stratVar_const`). -/
theorem owenNet_exact_of_const (hb : b ≠ 0) {m : ℕ} (c : ℝ) (T : OwenTree b m)
    (r : Fin (b ^ m) → ℝ) :
    sampleMean (b ^ m) (fun _ ↦ c) (owenNet T r) = ∫ _x, c ∂uniformIco := by
  have := isProbabilityMeasure_uniformIco
  rw [integral_const, probReal_univ, one_smul]
  exact sampleMean_const_points (pow_ne_zero m hb) (fun _ ↦ c) 0

/-- **Correction: no CLT for constant `f`.** For `f ≡ c` the normalised error
`(μ̂ₙ − μ)/σₙ` of the scrambled net is identically `0`, so it does not converge in distribution to
any normal law `N(m₀, v)` with `v ≠ 0` (in particular not to `N(0,1)`). -/
theorem not_tendstoInDistribution_owenNet_const (hb : b ≠ 0) (c : ℝ) {P : Measure Ω}
    [IsProbabilityMeasure P] {T : (m : ℕ) → Ω → OwenTree b m}
    {R : (m : ℕ) → Ω → Fin (b ^ m) → ℝ}
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ} (m₀ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (hY : HasLaw Y (gaussianReal m₀ v) P') :
    ¬ TendstoInDistribution (fun m ω ↦ (sampleMean (b ^ m) (fun _ ↦ c) (owenNet (T m ω) (R m ω)) -
      ∫ _x, c ∂uniformIco) / Real.sqrt (stratVar (b ^ m) (fun _ ↦ c))) atTop Y (fun _ ↦ P) P' := by
  have hfun : (fun m ω ↦ (sampleMean (b ^ m) (fun _ ↦ c) (owenNet (T m ω) (R m ω)) -
      ∫ _x, c ∂uniformIco) / Real.sqrt (stratVar (b ^ m) (fun _ ↦ c))) =
      fun (_ : ℕ) (_ : Ω) ↦ (0 : ℝ) := by
    funext m ω
    rw [owenNet_exact_of_const hb c, sub_self, zero_div]
  rw [hfun]
  intro h
  have h0 : TendstoInDistribution (fun (_ : ℕ) (_ : Ω) ↦ (0 : ℝ)) atTop (fun _ ↦ (0 : ℝ))
      (fun _ ↦ P) P :=
    tendstoInDistribution_of_ae_tendsto (fun _ ↦ aemeasurable_const) aemeasurable_const
      (Eventually.of_forall fun _ ↦ tendsto_const_nhds)
  have heq := tendstoInDistribution_unique _ h0 h
  rw [hY.map_eq] at heq
  refine ne_gaussianReal_of_measure_Ioi_eq_zero (M := 0) ?_ m₀ hv heq
  rw [Measure.map_apply measurable_const measurableSet_Ioi,
    preimage_const_of_notMem (s := Ioi (0 : ℝ)) (fun h ↦ lt_irrefl (0 : ℝ) h), measure_empty]

end RQMCMarkov.OwenScrambling

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Loh's CLT for scrambled nets: the additive case, and two corrections (post #2, Loh 2003)

Post #2: "If we use an RQMC estimator with a digital net and nested uniform scrambling (Owen
scrambling) then a standard CLT applies and the asymptotic distribution is normally distributed"
(Loh 2003). Loh (2003) proves, by Stein's method, that for a scrambled `(0,m,s)`-net in base `b`
and an integrand whose mixed partial derivative `∂^s f/∂x₁⋯∂x_s` satisfies a Hölder condition
(Owen's smoothness class; the precise hypotheses, including the variance lower bound the proof
needs, are those of Loh's paper as summarised by Basu and Mukherjee 2017), the estimator
standardised by its own standard deviation is asymptotically `N(0,1)` as `m → ∞`.

**Reading.** "A standard CLT applies" is read as `(μ̂ - μ)/√Var(μ̂) ⇒ N(0,1)`, for the law
`scrambledLaw f (d m)` of the scrambled estimator of a sequence of `(0,m,s)`-nets `d m`
(`m` digits, `n = b^m` points).

## Main results

* **Loh's CLT for additive integrands, any dimension** (`tendstoInDistribution_scrambledLaw_addFn`):
  for `f(x) = Σ_j g_j(x_j)` with each `g_j` measurable and `C¹` on `[0,1]`, at least one not
  constant, `(μ̂ - μ)/√Var(μ̂) ⇒ N(0,1)`. Ingredients: in each coordinate a scrambled `(0,m,s)`-net
  visits every cell of length `b^{-m}` exactly once (`injective_coord_net`,
  `bijective_cellFin_scramble`), so the error is a sum over the points of independent, centred,
  bounded terms (`addTerm`, `sum_addTerm`, `integral_addTerm`, `abs_addTerm_le`) whose variances add
  to `Σ_j σ²_n(g_j)` (`sum_integral_sq_addTerm`, `integral_sq_sum_pi`); the bounded Lindeberg CLT
  of `Owen1DLindeberg` gives the CLT for EVERY fixed sequence of scrambles
  (`tendstoInDistribution_scrambledEstimate_addFn`), and `tendsto_avg_of_forall` passes to the
  mixture over the scrambles.
* `variance_scrambledLaw_addFn`: `Var(μ̂) = Σ_j σ²_n(g_j)` (the one-dimensional stratified
  variances `stratVar` of `Owen1DVariance`); `tendsto_cube_mul_variance_scrambledLaw_addFn`:
  `n³ Var(μ̂) → Σ_j (1/12) ∫₀¹ g_j'²`.
* Concrete instances for `s = 2` with the Hammersley net (`ScrambleHammersley`), any base `b ≥ 2`:
  `variance_scrambledLaw_hammersley_le` (`Var ≤ (b/(b-1)) σ²/n ≤ e σ²/n`),
  `tendsto_variance_scrambledLaw_hammersley` (`o(1/n)`) and
  `tendstoInDistribution_scrambledLaw_hammersley` (CLT, additive integrands).
* Digital shift versus nested scrambling (post #2's contrast): `digitShiftScramble` (the digital
  shift is the nested scramble with the same translation at every node of a level),
  `digitShift_ne_pair_law` (it does not have Owen's pair law). The non-normality of the
  digitally shifted estimator in one dimension is in `DigitalShift` of the `PointSets` project;
  `Owen1DCLT` contrasts the Owen net with the random shift.

**Correction 1 (scale).** The limit is not a "standard" CLT at the Monte Carlo scale: for EVERY
measurable `f ∈ L²`, `√n (μ̂ - μ) → 0` in probability (`tendsto_scrambledLaw_sqrt_error_ge`, from
`Var = o(1/n)`), so `√n (μ̂ - μ)` has no non-degenerate normal limit
(`not_tendstoInDistribution_sqrt_scaled_error`). Normality holds only after normalising by
`√Var(μ̂) = o(n^{-1/2})` (of order `n^{-3/2}` for smooth additive `f`).

**Correction 2 (integrand).** Smoothness and non-degeneracy are needed, in every dimension: a
scrambled `(0,m,s)`-net integrates step functions on elementary cubes of level `R` exactly once
`m ≥ sR` (`scrambledLaw_stepFn_ne_eq_zero`), so for such `f` no normalisation gives a normal
limit (`not_tendstoInDistribution_stepFn`). (In one dimension, `Owen1DCounterexample` gives a
discontinuous `f` with positive variance and no normal limit, and `Owen1DCLT` the constant case.)

**Not formalised.** Loh's theorem for non-additive integrands in `s ≥ 2` dimensions. There the
Haar components with two or more active coordinates couple the points through shared node
permutations, the error is no longer a sum of independent terms, and Loh's Stein-method argument
(with a lower bound on `Var(μ̂)`; Owen 1997b: `Var = O(n^{-3} (log n)^{s-1})` for smooth `f`) would
be needed. Nets with `t > 0` are not treated; the post's digital nets (e.g. Sobol' points in base
`2`) have `t > 0` in general once `s ≥ 3`, a case Loh's theorem does not cover.
-/

namespace RQMCMarkov.OwenScrambling

open MeasureTheory ProbabilityTheory Finset Filter Set
open scoped ENNReal NNReal Topology

variable {b D : ℕ}

/-- The law of the scrambled-net estimator is a probability measure. -/
theorem isProbabilityMeasure_scrambledLaw {s n : ℕ} {f : (Fin s → ℝ) → ℝ} (hfm : Measurable f)
    (d : Fin n → Fin s → Fin D → Fin b) : IsProbabilityMeasure (scrambledLaw f d) := by
  have := isProbabilityMeasure_remLaw s n
  exact isProbabilityMeasure_mixLaw (measurable_scrambledEstimate hfm d)

/-- **At the Monte Carlo scale the scrambled-net error vanishes** (Chebyshev and
`Var = o(1/n)`): for every `ε > 0`, `P(|√n (μ̂ - μ)| ≥ ε) → 0`. -/
theorem tendsto_scrambledLaw_sqrt_error_ge (hb : 1 < b) {s : ℕ} (hs : 1 ≤ s)
    (hsb : s ≤ b + 1)
    (d : (m : ℕ) → Fin (b ^ m) → Fin s → Fin m → Fin b)
    (hnet : ∀ m, IsNet b 0 m fun i j ↦ digitPoint (d m i j) 0)
    {f : (Fin s → ℝ) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (uniformCube s)) {ε : ℝ}
    (hε : 0 < ε) :
    Tendsto (fun m ↦ scrambledLaw f (d m)
      {x | ε ≤ |Real.sqrt ((b : ℝ) ^ m) * (x - ∫ y, f y ∂(uniformCube s))|}) atTop (𝓝 0) := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb0
  have hT := tendsto_pow_mul_variance_scrambledLaw hb hs hsb d hnet hfm hf
  have hbound : ∀ m, scrambledLaw f (d m)
      {x | ε ≤ |Real.sqrt ((b : ℝ) ^ m) * (x - ∫ y, f y ∂(uniformCube s))|} ≤
      ENNReal.ofReal ((b : ℝ) ^ m * Var[fun x ↦ x; scrambledLaw f (d m)] / ε ^ 2) := by
    intro m
    have hP := isProbabilityMeasure_scrambledLaw hfm (d m)
    have hL : MemLp (fun x : ℝ ↦ x) 2 (scrambledLaw f (d m)) :=
      memLp_id_mixLaw (measurable_scrambledEstimate hfm (d m))
        (memLp_scrambledEstimate hb0 hf (d m))
    have hn : b ^ m ≠ 0 := (Nat.pow_pos hb0).ne'
    have hmean := integral_scrambledLaw hb0 hn hfm hf (d m)
    have hsq : 0 < Real.sqrt ((b : ℝ) ^ m) := Real.sqrt_pos.2 (pow_pos hb' m)
    have hc : 0 < ε / Real.sqrt ((b : ℝ) ^ m) := div_pos hε hsq
    have hset : {x | ε ≤ |Real.sqrt ((b : ℝ) ^ m) * (x - ∫ y, f y ∂(uniformCube s))|} =
        {x | ε / Real.sqrt ((b : ℝ) ^ m) ≤
          |(fun x : ℝ ↦ x) x - ∫ y, (fun x : ℝ ↦ x) y ∂(scrambledLaw f (d m))|} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      rw [hmean, abs_mul, abs_of_pos hsq, div_le_iff₀ hsq, mul_comm]
    rw [hset]
    refine le_trans (meas_ge_le_variance_div_sq hL hc) (le_of_eq ?_)
    congr 1
    rw [div_pow, Real.sq_sqrt (pow_pos hb' m).le]
    field_simp
  have hlim : Tendsto (fun m ↦ ENNReal.ofReal ((b : ℝ) ^ m *
      Var[fun x ↦ x; scrambledLaw f (d m)] / ε ^ 2)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (hT.div_const (ε ^ 2))
    rwa [zero_div, ENNReal.ofReal_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ ↦ zero_le)
    hbound

/-- **Correction: no CLT at the Monte Carlo scale `√n`** (post #2): for scrambled `(0,m,s)`-nets
(`s ≤ b + 1`) and EVERY measurable `f ∈ L²`, `√n (μ̂ - μ)` does not converge in distribution to any
normal law `N(m₀, v)` with `v ≠ 0` (it converges to `0` in probability). The normal limit of
Loh (2003) holds only after normalising by the true standard deviation, which is `o(n^{-1/2})`. -/
theorem not_tendstoInDistribution_sqrt_scaled_error (hb : 1 < b) {s : ℕ} (hs : 1 ≤ s)
    (hsb : s ≤ b + 1) (d : (m : ℕ) → Fin (b ^ m) → Fin s → Fin m → Fin b)
    (hnet : ∀ m, IsNet b 0 m fun i j ↦ digitPoint (d m i j) 0)
    {f : (Fin s → ℝ) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (uniformCube s))
    [∀ m, IsProbabilityMeasure (scrambledLaw f (d m))]
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ} (m₀ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (hY : HasLaw Y (gaussianReal m₀ v) P') :
    ¬ TendstoInDistribution
      (fun m x ↦ Real.sqrt ((b : ℝ) ^ m) * (x - ∫ y, f y ∂(uniformCube s))) atTop Y
      (fun m ↦ scrambledLaw f (d m)) P' := by
  intro h
  have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto h.tendsto
    (isOpen_Ioi (a := (1 : ℝ)))
  change (P'.map Y) (Ioi 1) ≤ atTop.liminf fun m ↦ ((scrambledLaw f (d m)).map
    (fun x ↦ Real.sqrt ((b : ℝ) ^ m) * (x - ∫ y, f y ∂(uniformCube s)))) (Ioi 1) at hle
  have hmeas : ∀ m : ℕ, Measurable
      (fun x : ℝ ↦ Real.sqrt ((b : ℝ) ^ m) * (x - ∫ y, f y ∂(uniformCube s))) := fun m ↦
    (measurable_id.sub_const _).const_mul _
  have hzero : Tendsto (fun m ↦ ((scrambledLaw f (d m)).map
      (fun x ↦ Real.sqrt ((b : ℝ) ^ m) * (x - ∫ y, f y ∂(uniformCube s)))) (Ioi 1))
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_scrambledLaw_sqrt_error_ge hb hs hsb d hnet hfm hf one_pos) (fun _ ↦ zero_le)
      fun m ↦ ?_
    rw [Measure.map_apply (hmeas m) measurableSet_Ioi]
    refine measure_mono fun x hx ↦ ?_
    rw [Set.mem_preimage, Set.mem_Ioi] at hx
    rw [Set.mem_ofPred_eq]
    exact le_trans hx.le (le_abs_self _)
  rw [hzero.liminf_eq, nonpos_iff_eq_zero] at hle
  exact ne_gaussianReal_of_measure_Ioi_eq_zero hle m₀ hv hY.map_eq

/-- **Independent coordinates of a product law**: `E[g(v_j) h(v_k)] = (∫ g)(∫ h)` for
`j ≠ k` under `Measure.pi fun _ ↦ ν`. -/
theorem integral_pi_eval_mul {ι α : Type*} [Fintype ι] [MeasurableSpace α] {ν : Measure α}
    [IsProbabilityMeasure ν] {g h : α → ℝ} (hg : AEStronglyMeasurable g ν)
    (hh : AEStronglyMeasurable h ν) {j k : ι} (hjk : j ≠ k) :
    ∫ v, g (v j) * h (v k) ∂(Measure.pi fun _ : ι ↦ ν) = (∫ x, g x ∂ν) * ∫ x, h x ∂ν := by
  have hind : iIndepFun (fun (l : ι) (v : ι → α) ↦ v l) (Measure.pi fun _ : ι ↦ ν) :=
    iIndepFun_pi (X := fun _ (x : α) ↦ x) fun _ ↦ aemeasurable_id
  have hpair := hind.indepFun hjk
  have hmj := measurePreserving_eval (fun _ : ι ↦ ν) j
  have hmk := measurePreserving_eval (fun _ : ι ↦ ν) k
  have hg' : AEStronglyMeasurable g ((Measure.pi fun _ : ι ↦ ν).map (fun v : ι → α ↦ v j)) := by
    rw [show (fun v : ι → α ↦ v j) = Function.eval j from rfl, hmj.map_eq]
    exact hg
  have hh' : AEStronglyMeasurable h ((Measure.pi fun _ : ι ↦ ν).map (fun v : ι → α ↦ v k)) := by
    rw [show (fun v : ι → α ↦ v k) = Function.eval k from rfl, hmk.map_eq]
    exact hh
  have h1 := hpair.integral_comp_mul_comp (f := g) (g := h) hmj.measurable.aemeasurable
    hmk.measurable.aemeasurable hg' hh'
  have e1 : ∫ v, g (v j) ∂(Measure.pi fun _ : ι ↦ ν) = ∫ x, g x ∂ν := by
    have := integral_map hmj.measurable.aemeasurable (by rw [hmj.map_eq]; exact hg)
    rw [hmj.map_eq] at this
    exact this.symm
  have e2 : ∫ v, h (v k) ∂(Measure.pi fun _ : ι ↦ ν) = ∫ x, h x ∂ν := by
    have := integral_map hmk.measurable.aemeasurable (by rw [hmk.map_eq]; exact hh)
    rw [hmk.map_eq] at this
    exact this.symm
  calc ∫ v, g (v j) * h (v k) ∂(Measure.pi fun _ : ι ↦ ν)
      = ∫ v, ((g ∘ fun v : ι → α ↦ v j) * (h ∘ fun v : ι → α ↦ v k)) v
          ∂(Measure.pi fun _ : ι ↦ ν) := rfl
    _ = (∫ v, (g ∘ fun v : ι → α ↦ v j) v ∂(Measure.pi fun _ : ι ↦ ν)) *
          ∫ v, (h ∘ fun v : ι → α ↦ v k) v ∂(Measure.pi fun _ : ι ↦ ν) := h1
    _ = (∫ x, g x ∂ν) * ∫ x, h x ∂ν := by rw [← e1, ← e2]; rfl

/-- **Second moment of a sum of independent centred coordinates**:
`E[(Σ_j Z_j(v_j))²] = Σ_j E[Z_j²]` when the `Z_j` are centred and square integrable. -/
theorem integral_sq_sum_pi {ι α : Type*} [Fintype ι] [MeasurableSpace α] {ν : Measure α}
    [IsProbabilityMeasure ν] {Z : ι → α → ℝ} (hZ : ∀ j, MemLp (Z j) 2 ν)
    (h0 : ∀ j, ∫ x, Z j x ∂ν = 0) :
    ∫ v, (∑ j, Z j (v j)) ^ 2 ∂(Measure.pi fun _ : ι ↦ ν) = ∑ j, ∫ x, Z j x ^ 2 ∂ν := by
  classical
  have hmp : ∀ j, MeasurePreserving (Function.eval j) (Measure.pi fun _ : ι ↦ ν) ν :=
    fun j ↦ measurePreserving_eval (fun _ : ι ↦ ν) j
  have hL : ∀ j, MemLp (fun v : ι → α ↦ Z j (v j)) 2 (Measure.pi fun _ : ι ↦ ν) := by
    intro j
    have h : MemLp (Z j) 2 ((Measure.pi fun _ : ι ↦ ν).map (Function.eval j)) := by
      rw [(hmp j).map_eq]
      exact hZ j
    exact h.comp_of_map (hmp j).measurable.aemeasurable
  have e : ∀ v : ι → α, (∑ j, Z j (v j)) ^ 2 = ∑ j, ∑ k, Z j (v j) * Z k (v k) := fun v ↦ by
    rw [sq, Finset.sum_mul_sum]
  rw [integral_congr_ae (Eventually.of_forall e),
    integral_finsetSum (f := fun j (v : ι → α) ↦ ∑ k, Z j (v j) * Z k (v k)) _ fun j _ ↦
      integrable_finsetSum _ fun k _ ↦ (hL j).integrable_mul (hL k)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [integral_finsetSum (f := fun k (v : ι → α) ↦ Z j (v j) * Z k (v k)) _ fun k _ ↦
      (hL j).integrable_mul (hL k), Finset.sum_eq_single j]
  · have h := (hZ j).integrable_sq
    have := integral_map (hmp j).measurable.aemeasurable
      (f := fun x ↦ Z j x ^ 2) (by rw [(hmp j).map_eq]; exact h.aestronglyMeasurable)
    rw [(hmp j).map_eq] at this
    rw [this]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [Function.eval]; ring)
  · intro k _ hkj
    rw [integral_pi_eval_mul (hZ j).aestronglyMeasurable (hZ k).aestronglyMeasurable
      (Ne.symm hkj), h0 j, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- **A `(0,m,s)`-net has distinct coordinates**: the digit strings of coordinate `j` of
different points differ (the one-dimensional projections are `(0,m,1)`-nets). -/
theorem injective_coord_net (hb : 0 < b) {m s n : ℕ} {d : Fin n → Fin s → Fin D → Fin b}
    (hmD : m ≤ D) (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) (j : Fin s) :
    Function.Injective fun i ↦ d i j := by
  intro i i' h
  simp only at h
  set r : Fin s → ℕ := Function.update 0 j m with hr
  have hrs : ∑ k, r k = m := by
    rw [hr, Finset.sum_update_of_mem (Finset.mem_univ j)]
    simp only [Pi.zero_apply, Finset.sum_const_zero, add_zero]
  have hcard := card_agree_net_eq_one hb hmD hnet hrs i
  have hmem : ∀ i'', d i'' j = d i j →
      i'' ∈ Finset.univ.filter fun i' ↦ ∀ k, Agree (r k) (d i k) (d i' k) := by
    intro i'' hi''
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun k ↦ ?_⟩
    by_cases hk : k = j
    · subst hk
      rw [hr, Function.update_self, hi'']
      exact fun l _ ↦ rfl
    · rw [hr, Function.update_of_ne hk, Pi.zero_apply]
      exact fun l hl ↦ absurd hl (Nat.not_lt_zero _)
  exact Finset.card_le_one.1 hcard.le _ (hmem i rfl) _ (hmem i' h.symm)

/-- **The cell deviation bound**: for `g` `K`-Lipschitz on `[0,1]` and `w ∈ [0,1)`,
`|g((c + w)/n) - E g((c + U)/n)| ≤ K/n`. -/
theorem abs_cell_sub_integral_le {g : ℝ → ℝ} (hc : ContinuousOn g (Icc 0 1)) {K : ℝ}
    (hK : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |g x - g y| ≤ K * |x - y|) {n : ℕ}
    (c : Fin n) {w : ℝ} (hw : w ∈ Ico (0 : ℝ) 1) :
    |g (stratumMap n c w) - ∫ x, g (stratumMap n c x) ∂uniformIco| ≤ K / n := by
  have := isProbabilityMeasure_uniformIco
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (Fin.pos c).ne')
  have hK0 : 0 ≤ K := by
    have h := hK 1 (right_mem_Icc.2 zero_le_one) 0 (left_mem_Icc.2 zero_le_one)
    rw [sub_zero, abs_one, mul_one] at h
    exact (abs_nonneg _).trans h
  have hpt : ∀ x ∈ Ico (0 : ℝ) 1, |g (stratumMap n c w) - g (stratumMap n c x)| ≤ K / n := by
    intro x hx
    refine (hK _ (stratumMap_mem_Icc c (Ico_subset_Icc_self hw)) _
      (stratumMap_mem_Icc c (Ico_subset_Icc_self hx))).trans ?_
    have heq : stratumMap n c w - stratumMap n c x = (w - x) / n := by
      simp only [stratumMap]
      ring
    rw [heq, abs_div, abs_of_pos hn]
    have hux : |w - x| ≤ 1 := abs_le.2 ⟨by linarith [hw.1, hx.2], by linarith [hw.2, hx.1]⟩
    calc K * (|w - x| / n) ≤ K * (1 / n) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hux hn.le) hK0
      _ = K / n := by ring
  have heq : g (stratumMap n c w) - ∫ x, g (stratumMap n c x) ∂uniformIco =
      ∫ x, (g (stratumMap n c w) - g (stratumMap n c x)) ∂uniformIco := by
    rw [integral_sub (integrable_const _) (integrable_cell hc c), integral_const,
      probReal_univ, one_smul]
  rw [heq]
  have h := norm_integral_le_of_norm_le_const (μ := uniformIco)
    (f := fun x ↦ g (stratumMap n c w) - g (stratumMap n c x)) (C := K / n)
    (ae_restrict_of_forall_mem measurableSet_Ico fun x hx ↦ by
      rw [Real.norm_eq_abs]
      exact hpt x hx)
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at h

/-- In each coordinate, a scrambled `(0,m,s)`-net with `m` digits visits every cell of length
`b^{-m}` exactly once: `i ↦ cell of coordinate j of the scrambled point i` is a bijection. -/
theorem bijective_cellFin_scramble (hb : 0 < b) {m s : ℕ}
    {d : Fin (b ^ m) → Fin s → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    (ρ : Fin s → Scramble b m) (j : Fin s) :
    Function.Bijective fun i ↦ cellFin hb (scramble (ρ j) (d i j)) := by
  refine Finite.injective_iff_bijective.1 fun i i' h ↦ ?_
  have h1 : cellVal (scramble (ρ j) (d i j)) = cellVal (scramble (ρ j) (d i' j)) :=
    congrArg Fin.val h
  exact injective_coord_net hb le_rfl hnet j
    (scramble_injective (ρ j) (cellVal_injective hb h1))

/-- An additive integrand `x ↦ Σ_j g_j(x_j)`. -/
noncomputable def addFn {s : ℕ} (g : Fin s → ℝ → ℝ) (x : Fin s → ℝ) : ℝ := ∑ j, g j (x j)

/-- The centred contribution of point `i` to the scrambled-net estimator of an additive
integrand: `n⁻¹ Σ_j (g_j(X_{ij}) - E g_j(X_{ij} | cell))`. -/
noncomputable def addTerm {s n : ℕ} (g : Fin s → ℝ → ℝ) (d : Fin n → Fin s → Fin D → Fin b)
    (ρ : Fin s → Scramble b D) (i : Fin n) (v : Fin s → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ j, (g j (digitPoint (scramble (ρ j) (d i j)) (v j)) -
    ∫ w, g j (digitPoint (scramble (ρ j) (d i j)) w) ∂uniformIco)

/-- A digit point with `m` digits is the stratified point of its cell. -/
theorem digitPoint_eq_stratumMap_cellFin (hb : 0 < b) {m : ℕ} (x : Fin m → Fin b) (w : ℝ) :
    digitPoint x w = stratumMap (b ^ m) (cellFin hb x) w :=
  digitPoint_eq_stratumMap x w

/-- **The error of the scrambled estimator of an additive integrand is a sum over the points**:
`μ̂ - μ = Σ_i addTerm i (u_i)`. -/
theorem sum_addTerm (hb : 0 < b) {m s : ℕ} {d : Fin (b ^ m) → Fin s → Fin m → Fin b}
    (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) {g : Fin s → ℝ → ℝ}
    (hgc : ∀ j, ContinuousOn (g j) (Icc 0 1)) (ρ : Fin s → Scramble b m)
    (u : Fin (b ^ m) → Fin s → ℝ) :
    ∑ i, addTerm g d ρ i (u i) =
      scrambledEstimate (addFn g) d ρ u - ∑ j, ∫ x, g j x ∂uniformIco := by
  have hn : b ^ m ≠ 0 := (Nat.pow_pos hb).ne'
  have hcell : ∀ j, ∑ i, ∫ w, g j (digitPoint (scramble (ρ j) (d i j)) w) ∂uniformIco =
      ((b ^ m : ℕ) : ℝ) * ∫ x, g j x ∂uniformIco := by
    intro j
    have h1 : ∑ i, ∫ w, g j (digitPoint (scramble (ρ j) (d i j)) w) ∂uniformIco =
        ∑ c : Fin (b ^ m), ∫ w, g j (stratumMap (b ^ m) c w) ∂uniformIco := by
      rw [← (bijective_cellFin_scramble hb hnet ρ j).sum_comp
        (fun c : Fin (b ^ m) ↦ ∫ w, g j (stratumMap (b ^ m) c w) ∂uniformIco)]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only [digitPoint_eq_stratumMap_cellFin hb]
    rw [h1, ← inv_mul_sum_integral_cell (hgc j) hn]
    have : ((b ^ m : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
    field_simp
  unfold addTerm scrambledEstimate sampleMean addFn
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [Finset.sum_comm (f := fun i j ↦ ∫ w, g j (digitPoint (scramble (ρ j) (d i j)) w)
    ∂uniformIco)]
  simp only [hcell, ← Finset.mul_sum]
  have : ((b ^ m : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  field_simp
  rfl

/-- The cell function of a coordinate is in `L^p`. -/
theorem memLp_cell_coord {m : ℕ} {g₁ : ℝ → ℝ} (hgm : Measurable g₁)
    (hgc : ContinuousOn g₁ (Icc 0 1)) (hb : 0 < b) (x : Fin m → Fin b) (p : ℝ≥0∞) :
    MemLp (fun w ↦ g₁ (digitPoint x w)) p uniformIco := by
  refine memLp_uniformIco_of_continuousOn (hgm.comp (measurable_digitPoint x)) ?_ p
  have hc : ContinuousOn (fun w ↦ g₁ (stratumMap (b ^ m) (cellFin hb x) w)) (Icc 0 1) :=
    hgc.comp (continuous_stratumMap _ _).continuousOn
      (fun u hu ↦ stratumMap_mem_Icc (cellFin hb x) hu)
  refine hc.congr fun w _ ↦ ?_
  rw [Function.comp_apply, digitPoint_eq_stratumMap_cellFin hb]

/-- `E[g(v_j)] = ∫ g` for `v ~ U[0,1)^s`. -/
theorem integral_uniformCube_eval {s : ℕ} {g : ℝ → ℝ} (hg : AEStronglyMeasurable g uniformIco)
    (j : Fin s) : ∫ v, g (v j) ∂(uniformCube s) = ∫ x, g x ∂uniformIco := by
  have := isProbabilityMeasure_uniformIco
  have hmp := measurePreserving_eval (fun _ : Fin s ↦ uniformIco) j
  have := integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hg)
  rw [hmp.map_eq] at this
  exact this.symm

/-- `v ↦ g(v_j)` is in `L^p(U[0,1)^s)` when `g ∈ L^p(U[0,1))`. -/
theorem memLp_uniformCube_eval {s : ℕ} {p : ℝ≥0∞} {g : ℝ → ℝ} (hg : MemLp g p uniformIco)
    (j : Fin s) : MemLp (fun v : Fin s → ℝ ↦ g (v j)) p (uniformCube s) := by
  have := isProbabilityMeasure_uniformIco
  have hmp := measurePreserving_eval (fun _ : Fin s ↦ uniformIco) j
  have h : MemLp g p ((uniformCube s).map (Function.eval j)) := by
    rw [hmp.map_eq]
    exact hg
  exact h.comp_of_map hmp.measurable.aemeasurable

/-- The point terms are centred. -/
theorem integral_addTerm {m s : ℕ} {d : Fin (b ^ m) → Fin s → Fin m → Fin b}
    {g : Fin s → ℝ → ℝ} (hgm : ∀ j, Measurable (g j)) (hgc : ∀ j, ContinuousOn (g j) (Icc 0 1))
    (hb : 0 < b) (ρ : Fin s → Scramble b m) (i : Fin (b ^ m)) :
    ∫ v, addTerm g d ρ i v ∂(uniformCube s) = 0 := by
  have := isProbabilityMeasure_uniformIco
  have := isProbabilityMeasure_uniformCube s
  have hL : ∀ j, MemLp (fun w ↦ g j (digitPoint (scramble (ρ j) (d i j)) w)) 2 uniformIco :=
    fun j ↦ memLp_cell_coord (hgm j) (hgc j) hb _ 2
  unfold addTerm
  rw [integral_const_mul, integral_finsetSum (f := fun j (v : Fin s → ℝ) ↦
    g j (digitPoint (scramble (ρ j) (d i j)) (v j)) -
      ∫ w, g j (digitPoint (scramble (ρ j) (d i j)) w) ∂uniformIco) _ fun j _ ↦
    ((memLp_uniformCube_eval (hL j) j).integrable one_le_two).sub (integrable_const _)]
  rw [Finset.sum_eq_zero, mul_zero]
  intro j _
  rw [integral_sub ((memLp_uniformCube_eval (hL j) j).integrable one_le_two)
    (integrable_const _), integral_const, probReal_univ, one_smul,
    integral_uniformCube_eval (hL j).aestronglyMeasurable j, sub_self]

/-- The point terms are in `L²`. -/
theorem memLp_addTerm {m s : ℕ} {d : Fin (b ^ m) → Fin s → Fin m → Fin b}
    {g : Fin s → ℝ → ℝ} (hgm : ∀ j, Measurable (g j)) (hgc : ∀ j, ContinuousOn (g j) (Icc 0 1))
    (hb : 0 < b) (ρ : Fin s → Scramble b m) (i : Fin (b ^ m)) :
    MemLp (addTerm g d ρ i) 2 (uniformCube s) := by
  have := isProbabilityMeasure_uniformCube s
  unfold addTerm
  refine MemLp.const_mul ?_ _
  exact memLp_finsetSum _ fun j _ ↦
    (memLp_uniformCube_eval (memLp_cell_coord (hgm j) (hgc j) hb _ 2) j).sub (memLp_const _)

/-- **Variance of the point terms**: `Σ_i E[addTerm_i²] = Σ_j σ²_n(g_j)`, the sum over the
coordinates of the one-dimensional stratified variances (`stratVar`). -/
theorem sum_integral_sq_addTerm {m s : ℕ} {d : Fin (b ^ m) → Fin s → Fin m → Fin b}
    (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) {g : Fin s → ℝ → ℝ}
    (hgm : ∀ j, Measurable (g j)) (hgc : ∀ j, ContinuousOn (g j) (Icc 0 1)) (hb : 0 < b)
    (ρ : Fin s → Scramble b m) :
    ∑ i, ∫ v, addTerm g d ρ i v ^ 2 ∂(uniformCube s) = ∑ j, stratVar (b ^ m) (g j) := by
  have := isProbabilityMeasure_uniformIco
  set Z : Fin (b ^ m) → Fin s → ℝ → ℝ := fun i j w ↦
    g j (digitPoint (scramble (ρ j) (d i j)) w) -
      ∫ w, g j (digitPoint (scramble (ρ j) (d i j)) w) ∂uniformIco with hZ
  have hL : ∀ i j, MemLp (fun w ↦ g j (digitPoint (scramble (ρ j) (d i j)) w)) 2 uniformIco :=
    fun i j ↦ memLp_cell_coord (hgm j) (hgc j) hb _ 2
  have hZL : ∀ i j, MemLp (Z i j) 2 uniformIco := fun i j ↦ (hL i j).sub (memLp_const _)
  have hZ0 : ∀ i j, ∫ w, Z i j w ∂uniformIco = 0 := by
    intro i j
    rw [hZ, integral_sub ((hL i j).integrable one_le_two) (integrable_const _), integral_const,
      probReal_univ, one_smul, sub_self]
  have hvar : ∀ i j, ∫ w, Z i j w ^ 2 ∂uniformIco =
      Var[fun w ↦ g j (stratumMap (b ^ m) (cellFin hb (scramble (ρ j) (d i j))) w);
        uniformIco] := by
    intro i j
    rw [variance_eq_integral ((hL i j).aestronglyMeasurable.aemeasurable.congr
      (Eventually.of_forall fun w ↦ by
        simp only [digitPoint_eq_stratumMap_cellFin hb]))]
    simp only [hZ, digitPoint_eq_stratumMap_cellFin hb]
  have hterm : ∀ i, ∫ v, addTerm g d ρ i v ^ 2 ∂(uniformCube s) =
      ((b ^ m : ℕ) : ℝ)⁻¹ ^ 2 * ∑ j, ∫ w, Z i j w ^ 2 ∂uniformIco := by
    intro i
    have e : ∀ v : Fin s → ℝ, addTerm g d ρ i v ^ 2 =
        ((b ^ m : ℕ) : ℝ)⁻¹ ^ 2 * (∑ j, Z i j (v j)) ^ 2 := fun v ↦ by
      unfold addTerm
      rw [mul_pow]
    rw [integral_congr_ae (Eventually.of_forall e), integral_const_mul,
      integral_sq_sum_pi (hZL i) (hZ0 i)]
  simp only [hterm, hvar, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold stratVar
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  congr 1
  exact (bijective_cellFin_scramble hb hnet ρ j).sum_comp
    (fun c : Fin (b ^ m) ↦ Var[fun w ↦ g j (stratumMap (b ^ m) c w); uniformIco])

/-- **Bound on the point terms**: if each `g_j` is `K_j`-Lipschitz on `[0,1]`, then
`|addTerm_i(v)| ≤ (Σ_j K_j)/n²` for `v ∈ [0,1)^s`. -/
theorem abs_addTerm_le {m s : ℕ} {d : Fin (b ^ m) → Fin s → Fin m → Fin b}
    {g : Fin s → ℝ → ℝ} (hgc : ∀ j, ContinuousOn (g j) (Icc 0 1)) {K : Fin s → ℝ}
    (hK : ∀ j, ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |g j x - g j y| ≤ K j * |x - y|)
    (hb : 0 < b) (ρ : Fin s → Scramble b m) (i : Fin (b ^ m)) {v : Fin s → ℝ}
    (hv : ∀ j, v j ∈ Ico (0 : ℝ) 1) :
    |addTerm g d ρ i v| ≤ (∑ j, K j) / ((b ^ m : ℕ) : ℝ) ^ 2 := by
  have hn : (0 : ℝ) < ((b ^ m : ℕ) : ℝ) := Nat.cast_pos.2 (Nat.pow_pos hb)
  unfold addTerm
  rw [abs_mul, abs_of_pos (inv_pos.2 hn)]
  have h1 : |∑ j, (g j (digitPoint (scramble (ρ j) (d i j)) (v j)) -
      ∫ w, g j (digitPoint (scramble (ρ j) (d i j)) w) ∂uniformIco)| ≤
      ∑ j, K j / ((b ^ m : ℕ) : ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
    simp only [digitPoint_eq_stratumMap_cellFin hb]
    exact abs_cell_sub_integral_le (hgc j) (hK j) _ (hv j)
  calc ((b ^ m : ℕ) : ℝ)⁻¹ * |∑ j, (g j (digitPoint (scramble (ρ j) (d i j)) (v j)) -
        ∫ w, g j (digitPoint (scramble (ρ j) (d i j)) w) ∂uniformIco)|
      ≤ ((b ^ m : ℕ) : ℝ)⁻¹ * ∑ j, K j / ((b ^ m : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hn.le)
    _ = (∑ j, K j) / ((b ^ m : ℕ) : ℝ) ^ 2 := by
        rw [← Finset.sum_div]
        field_simp

/-- An additive integrand is measurable. -/
theorem measurable_addFn {s : ℕ} {g : Fin s → ℝ → ℝ} (hgm : ∀ j, Measurable (g j)) :
    Measurable (addFn g) :=
  Finset.measurable_sum _ fun j _ ↦ (hgm j).comp (measurable_pi_apply j)

/-- An additive integrand with coordinates continuous on `[0,1]` is in `L²` of the cube. -/
theorem memLp_addFn {s : ℕ} {g : Fin s → ℝ → ℝ} (hgm : ∀ j, Measurable (g j))
    (hgc : ∀ j, ContinuousOn (g j) (Icc 0 1)) (p : ℝ≥0∞) : MemLp (addFn g) p (uniformCube s) :=
  memLp_finsetSum _ fun j _ ↦
    memLp_uniformCube_eval (memLp_uniformIco_of_continuousOn (hgm j) (hgc j) p) j

/-- The integral of an additive integrand: `∫ Σ_j g_j(x_j) = Σ_j ∫₀¹ g_j`. -/
theorem integral_addFn {s : ℕ} {g : Fin s → ℝ → ℝ} (hgm : ∀ j, Measurable (g j))
    (hgc : ∀ j, ContinuousOn (g j) (Icc 0 1)) :
    ∫ x, addFn g x ∂(uniformCube s) = ∑ j, ∫ x, g j x ∂uniformIco := by
  unfold addFn
  rw [integral_finsetSum (f := fun j (x : Fin s → ℝ) ↦ g j (x j)) _ fun j _ ↦
    (memLp_uniformCube_eval (memLp_uniformIco_of_continuousOn (hgm j) (hgc j) 1) j).integrable
      le_rfl]
  exact Finset.sum_congr rfl fun j _ ↦
    integral_uniformCube_eval (hgm j).aestronglyMeasurable j

/-- **The variance of a scrambled `(0,m,s)`-net for an additive integrand** is the sum of the
one-dimensional stratified variances: `Var(μ̂) = Σ_j σ²_n(g_j)`. -/
theorem variance_scrambledLaw_addFn (hb : 0 < b) {m s : ℕ}
    {d : Fin (b ^ m) → Fin s → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    {g : Fin s → ℝ → ℝ} (hgm : ∀ j, Measurable (g j)) (hgc : ∀ j, ContinuousOn (g j) (Icc 0 1)) :
    Var[fun x ↦ x; scrambledLaw (addFn g) d] = ∑ j, stratVar (b ^ m) (g j) := by
  have hU := isProbabilityMeasure_uniformCube s
  have hn : b ^ m ≠ 0 := (Nat.pow_pos hb).ne'
  rw [variance_scrambledLaw_eq_sum hb hn (measurable_addFn hgm) (memLp_addFn hgm hgc 2) d,
    integral_addFn hgm hgc]
  have hρ : ∀ ρ : Fin s → Scramble b m, ∫ u, (scrambledEstimate (addFn g) d ρ u -
      ∑ j, ∫ x, g j x ∂uniformIco) ^ 2 ∂(remLaw s (b ^ m)) = ∑ j, stratVar (b ^ m) (g j) := by
    intro ρ
    rw [integral_congr_ae (Eventually.of_forall fun u ↦ by
      rw [← sum_addTerm hb hnet hgc ρ u]), integral_sq_sum_pi (ν := uniformCube s)
      (fun i ↦ memLp_addTerm hgm hgc hb ρ i) (fun i ↦ integral_addTerm hgm hgc hb ρ i),
      sum_integral_sq_addTerm hnet hgm hgc hb ρ]
  rw [Finset.sum_congr rfl fun ρ _ ↦ hρ ρ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card (Fin s → Scramble b m) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 Fintype.card_ne_zero
  field_simp

/-- The point terms are measurable. -/
theorem measurable_addTerm {s n : ℕ} {g : Fin s → ℝ → ℝ} (hgm : ∀ j, Measurable (g j))
    (d : Fin n → Fin s → Fin D → Fin b) (ρ : Fin s → Scramble b D) (i : Fin n) :
    Measurable (addTerm g d ρ i) := by
  unfold addTerm
  exact (Finset.measurable_sum _ fun j _ ↦
    ((hgm j).comp ((measurable_digitPoint _).comp (measurable_pi_apply j))).sub_const _).const_mul
      _

/-- **The CLT for a fixed sequence of scrambles, additive integrands** (Lindeberg): for
`(0,m,s)`-nets with `m` digits, additive `f = Σ_j g_j(x_j)` with each `g_j` measurable and `C¹`
on `[0,1]`, at least one non-constant, and ANY sequence of nested scrambles `ρ_m`, the
standardised estimator `(μ̂ - μ)/σ_n` with `σ_n² = Σ_j σ²_n(g_j)` converges in distribution to
`N(0,1)` over the remainders. -/
theorem tendstoInDistribution_scrambledEstimate_addFn (hb : 1 < b) {s : ℕ}
    (d : (m : ℕ) → Fin (b ^ m) → Fin s → Fin m → Fin b)
    (hnet : ∀ m, IsNet b 0 m fun i j ↦ digitPoint (d m i j) 0) {g g' : Fin s → ℝ → ℝ}
    (hgm : ∀ j, Measurable (g j))
    (hg : ∀ j, ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (g j) (g' j x) (Icc 0 1) x)
    (hg' : ∀ j, ContinuousOn (g' j) (Icc 0 1)) (hnc : ∃ j, ∃ x ∈ Icc (0 : ℝ) 1, g j x ≠ g j 0)
    (ρ : (m : ℕ) → Fin s → Scramble b m) [∀ m, IsProbabilityMeasure (remLaw s (b ^ m))]
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun m u ↦ (scrambledEstimate (addFn g) (d m) (ρ m) u -
      ∑ j, ∫ x, g j x ∂uniformIco) / Real.sqrt (∑ j, stratVar (b ^ m) (g j))) atTop Z
      (fun m ↦ remLaw s (b ^ m)) P' := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hU := isProbabilityMeasure_uniformCube s
  have hgc : ∀ j, ContinuousOn (g j) (Icc 0 1) := fun j x hx ↦ (hg j x hx).continuousWithinAt
  choose K hK using fun j ↦ exists_lipschitz_of_C1 (hg j) (hg' j)
  set σ2 : ℕ → ℝ := fun m ↦ ∑ j, stratVar (b ^ m) (g j) with hσ2
  have hσ2nn : ∀ m, 0 ≤ σ2 m := fun m ↦ Finset.sum_nonneg fun j _ ↦ stratVar_nonneg _ _
  set nR : ℕ → ℝ := fun m ↦ ((b ^ m : ℕ) : ℝ) with hnR
  have hnpos : ∀ m, 0 < nR m := fun m ↦ Nat.cast_pos.2 (Nat.pow_pos hb0)
  have hNtop : Tendsto (fun m : ℕ ↦ b ^ m) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hb
  have hnRtop : Tendsto nR atTop atTop := tendsto_natCast_atTop_atTop.comp hNtop
  -- the rate `n³ σ² → c > 0`
  set c : ℝ := ∑ j, (∫ x in (0 : ℝ)..1, g' j x ^ 2) / 12 with hc
  have hcube : Tendsto (fun m ↦ nR m ^ 3 * σ2 m) atTop (𝓝 c) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin s)) fun j _ ↦
      (tendsto_cube_mul_stratVar (hg j) (hg' j)).comp hNtop
    simp only [Function.comp_def] at h
    refine h.congr fun m ↦ ?_
    simp only [hnR, hσ2, Finset.mul_sum]
  have hcpos : 0 < c := by
    obtain ⟨j₀, hj₀⟩ := hnc
    have h₀ := integral_sq_deriv_pos (hg j₀) (hg' j₀) hj₀
    have hle : (∫ x in (0 : ℝ)..1, g' j₀ x ^ 2) / 12 ≤ c :=
      Finset.single_le_sum (f := fun j ↦ (∫ x in (0 : ℝ)..1, g' j x ^ 2) / 12)
        (fun j _ ↦ div_nonneg (intervalIntegral.integral_nonneg zero_le_one
          fun x _ ↦ sq_nonneg _) (by norm_num)) (Finset.mem_univ j₀)
    linarith [div_pos h₀ (show (0 : ℝ) < 12 by norm_num)]
  have hσpos : ∀ᶠ m in atTop, 0 < σ2 m := by
    filter_upwards [hcube.eventually (lt_mem_nhds hcpos)] with m hm
    exact pos_of_mul_pos_right hm (pow_nonneg (hnpos m).le 3)
  -- the terms
  set X : (m : ℕ) → Fin (b ^ m) → (Fin (b ^ m) → Fin s → ℝ) → ℝ := fun m i u ↦
    addTerm g (d m) (ρ m) i (u i) / Real.sqrt (σ2 m) with hX
  set δ : ℕ → ℝ := fun m ↦ (∑ j, K j) / Real.sqrt (nR m * (nR m ^ 3 * σ2 m)) with hδ
  have hfun : (fun m u ↦ (scrambledEstimate (addFn g) (d m) (ρ m) u -
      ∑ j, ∫ x, g j x ∂uniformIco) / Real.sqrt (∑ j, stratVar (b ^ m) (g j))) =
      fun m u ↦ ∑ i, X m i u := by
    funext m u
    rw [← sum_addTerm hb0 (hnet m) hgc (ρ m) u, Finset.sum_div]
  rw [hfun]
  refine tendstoInDistribution_sum_of_bounded (L := fun m ↦ b ^ m) (X := X)
    (fun m i ↦ ((measurable_addTerm hgm (d m) (ρ m) i).comp
      (measurable_pi_apply i)).aemeasurable.div_const _)
    (fun m ↦ iIndepFun_pi (X := fun i v ↦ addTerm g (d m) (ρ m) i v / Real.sqrt (σ2 m))
      fun i ↦ ((measurable_addTerm hgm (d m) (ρ m) i).div_const _).aemeasurable)
    (fun m i ↦ ?_) (δ := δ) ?_ (fun m i ↦ ?_) (v := 1) ?_ (by rwa [Real.toNNReal_one])
  · -- centred
    simp only [hX]
    rw [integral_div, integral_remLaw_eval (g := addTerm g (d m) (ρ m) i)
      (measurable_addTerm hgm (d m) (ρ m) i).aestronglyMeasurable i,
      integral_addTerm hgm hgc hb0 (ρ m) i, zero_div]
  · -- δ → 0
    have h1 : Tendsto (fun m ↦ nR m * (nR m ^ 3 * σ2 m)) atTop atTop :=
      hnRtop.atTop_mul_pos hcpos hcube
    exact tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp h1)
  · -- bounded
    filter_upwards [ae_mem_cube_remLaw s (b ^ m)] with u hu
    have hb1 := abs_addTerm_le (d := d m) hgc hK hb0 (ρ m) i (hu i)
    simp only [hX, hδ]
    have hsq : Real.sqrt (nR m * (nR m ^ 3 * σ2 m)) = nR m ^ 2 * Real.sqrt (σ2 m) := by
      rw [show nR m * (nR m ^ 3 * σ2 m) = (nR m ^ 2) ^ 2 * σ2 m by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg _)]
    rw [hsq, abs_div, abs_of_nonneg (Real.sqrt_nonneg _), ← div_div]
    exact div_le_div_of_nonneg_right hb1 (Real.sqrt_nonneg _)
  · -- variances sum to one
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hσpos] with m hm
    have e : ∀ i, ∫ u, X m i u ^ 2 ∂(remLaw s (b ^ m)) =
        (∫ v, addTerm g (d m) (ρ m) i v ^ 2 ∂(uniformCube s)) / σ2 m := by
      intro i
      simp only [hX, div_pow, Real.sq_sqrt (hσ2nn m)]
      rw [integral_div, integral_remLaw_eval (g := fun v ↦ addTerm g (d m) (ρ m) i v ^ 2)
        ((memLp_addTerm hgm hgc hb0 (ρ m) i).integrable_sq.aestronglyMeasurable) i]
    simp only [e, ← Finset.sum_div]
    rw [sum_integral_sq_addTerm (hnet m) hgm hgc hb0 (ρ m), div_self hm.ne']

/-- **Scrambled nets integrate step functions exactly**: for a level-`R` step function and every
`(0,m,s)`-net with `m ≥ sR` (and `R ≤ m`), the scrambled estimator equals `∫ f` almost surely:
its law puts no mass off `∫ f`. -/
theorem scrambledLaw_stepFn_ne_eq_zero (hb : 0 < b) {s R m : ℕ} (hsR : s * R ≤ m) (hRm : R ≤ m)
    {d : Fin (b ^ m) → Fin s → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    {G : (Fin s → ℕ) → ℝ} {M : ℝ} (hG : ∀ a, |G a| ≤ M) :
    scrambledLaw (stepFn b R G) d {x | x ≠ ∫ y, stepFn b R G y ∂(uniformCube s)} = 0 := by
  have hmeas : MeasurableSet {x : ℝ | x ≠ ∫ y, stepFn b R G y ∂(uniformCube s)} :=
    (measurableSet_singleton _).compl
  unfold scrambledLaw mixLaw
  rw [Measure.smul_apply, Measure.finsetSum_apply, Finset.sum_eq_zero, smul_zero]
  intro ρ _
  rw [Measure.map_apply (measurable_scrambledEstimate (measurable_stepFn b R G) d ρ) hmeas,
    measure_eq_zero_iff_ae_notMem]
  filter_upwards [ae_mem_cube_remLaw s (b ^ m)] with u hu
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, not_not]
  exact sampleMean_stepFn_scrambledPoint hb le_rfl hRm hsR hnet hG ρ hu

/-- **Correction: no CLT for step functions** (in every dimension): for a level-`R` step function
`f` and `(0,m,s)`-nets, the error `μ̂ - μ` vanishes almost surely once `m ≥ sR`, so for ANY
normalisation `c_m` the normalised error `(μ̂ - μ)/c_m` does not converge in distribution to a
normal law `N(m₀, v)` with `v ≠ 0`. Smoothness (and non-degeneracy) are needed, as in Loh (2003). -/
theorem not_tendstoInDistribution_stepFn (hb : 0 < b) {s R : ℕ}
    (d : (m : ℕ) → Fin (b ^ m) → Fin s → Fin m → Fin b)
    (hnet : ∀ m, IsNet b 0 m fun i j ↦ digitPoint (d m i j) 0)
    {G : (Fin s → ℕ) → ℝ} {M : ℝ} (hG : ∀ a, |G a| ≤ M) (c : ℕ → ℝ)
    [∀ m, IsProbabilityMeasure (scrambledLaw (stepFn b R G) (d m))]
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ} (m₀ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (hY : HasLaw Y (gaussianReal m₀ v) P') :
    ¬ TendstoInDistribution (fun m x ↦ (x - ∫ y, stepFn b R G y ∂(uniformCube s)) / c m) atTop
      Y (fun m ↦ scrambledLaw (stepFn b R G) (d m)) P' := by
  intro h
  have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto h.tendsto
    (isOpen_Ioi (a := (0 : ℝ)))
  change (P'.map Y) (Ioi 0) ≤ atTop.liminf fun m ↦ ((scrambledLaw (stepFn b R G) (d m)).map
    (fun x ↦ (x - ∫ y, stepFn b R G y ∂(uniformCube s)) / c m)) (Ioi 0) at hle
  have hev : ∀ᶠ m in atTop, ((scrambledLaw (stepFn b R G) (d m)).map
      (fun x ↦ (x - ∫ y, stepFn b R G y ∂(uniformCube s)) / c m)) (Ioi 0) = 0 := by
    filter_upwards [eventually_ge_atTop (s * R + R)] with m hm
    have hmeas : Measurable fun x : ℝ ↦ (x - ∫ y, stepFn b R G y ∂(uniformCube s)) / c m :=
      (measurable_id.sub_const _).div_const _
    rw [Measure.map_apply hmeas measurableSet_Ioi]
    refine measure_mono_null (fun x hx ↦ ?_)
      (scrambledLaw_stepFn_ne_eq_zero hb (by omega) (by omega) (hnet m) hG)
    rw [Set.mem_preimage, Set.mem_Ioi] at hx
    rw [Set.mem_ofPred_eq]
    intro hxe
    rw [hxe, sub_self, zero_div] at hx
    exact lt_irrefl 0 hx
  have hzero : Tendsto (fun m ↦ ((scrambledLaw (stepFn b R G) (d m)).map
      (fun x ↦ (x - ∫ y, stepFn b R G y ∂(uniformCube s)) / c m)) (Ioi 0)) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (hev.mono fun m hm ↦ hm.symm)
  rw [hzero.liminf_eq, nonpos_iff_eq_zero] at hle
  exact ne_gaussianReal_of_measure_Ioi_eq_zero hle m₀ hv hY.map_eq

/-- **The exact rate for additive integrands**: `n³ Var(μ̂) → Σ_j (1/12) ∫₀¹ g_j'²`, so the
RMSE of the scrambled `(0,m,s)`-net is of order `n^{-3/2}` (no `log n` factor, compare Owen
1997b's `O(n^{-3} (log n)^{s-1})` for general smooth integrands). -/
theorem tendsto_cube_mul_variance_scrambledLaw_addFn (hb : 1 < b) {s : ℕ}
    (d : (m : ℕ) → Fin (b ^ m) → Fin s → Fin m → Fin b)
    (hnet : ∀ m, IsNet b 0 m fun i j ↦ digitPoint (d m i j) 0) {g g' : Fin s → ℝ → ℝ}
    (hgm : ∀ j, Measurable (g j))
    (hg : ∀ j, ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (g j) (g' j x) (Icc 0 1) x)
    (hg' : ∀ j, ContinuousOn (g' j) (Icc 0 1)) :
    Tendsto (fun m ↦ ((b ^ m : ℕ) : ℝ) ^ 3 * Var[fun x ↦ x; scrambledLaw (addFn g) (d m)])
      atTop (𝓝 (∑ j, (∫ x in (0 : ℝ)..1, g' j x ^ 2) / 12)) := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hgc : ∀ j, ContinuousOn (g j) (Icc 0 1) := fun j x hx ↦ (hg j x hx).continuousWithinAt
  have hNtop : Tendsto (fun m : ℕ ↦ b ^ m) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hb
  have h := tendsto_finsetSum (Finset.univ : Finset (Fin s)) fun j _ ↦
    (tendsto_cube_mul_stratVar (hg j) (hg' j)).comp hNtop
  refine h.congr fun m ↦ ?_
  simp only [Function.comp_def]
  rw [variance_scrambledLaw_addFn hb0 (hnet m) hgm hgc, Finset.mul_sum]

/-- **Averages over finite sets converge when every selection does**: if `a m (ρ m) → L` for
every choice `ρ m ∈ R m`, then the averages `(#R m)⁻¹ Σ_ρ a m ρ → L` (take the worst `ρ`). -/
theorem tendsto_avg_of_forall {R : ℕ → Type*} [∀ m, Fintype (R m)] [∀ m, Nonempty (R m)]
    {a : (m : ℕ) → R m → ℝ} {L : ℝ}
    (h : ∀ ρ : (m : ℕ) → R m, Tendsto (fun m ↦ a m (ρ m)) atTop (𝓝 L)) :
    Tendsto (fun m ↦ (Fintype.card (R m) : ℝ)⁻¹ * ∑ ρ, a m ρ) atTop (𝓝 L) := by
  have hmax : ∀ m, ∃ ρ ∈ (Finset.univ : Finset (R m)), ∀ ρ' ∈ (Finset.univ : Finset (R m)),
      |a m ρ' - L| ≤ |a m ρ - L| := fun m ↦
    Finset.exists_max_image _ (fun ρ ↦ |a m ρ - L|) Finset.univ_nonempty
  choose ρ _ hρ using hmax
  have hstar := h ρ
  rw [tendsto_iff_norm_sub_tendsto_zero] at hstar ⊢
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun m ↦ ?_) hstar
  have hc : (0 : ℝ) < (Fintype.card (R m) : ℝ) := Nat.cast_pos.2 Fintype.card_pos
  have e : (Fintype.card (R m) : ℝ)⁻¹ * ∑ ρ', a m ρ' - L =
      (Fintype.card (R m) : ℝ)⁻¹ * ∑ ρ', (a m ρ' - L) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  rw [Real.norm_eq_abs, Real.norm_eq_abs, e, abs_mul, abs_of_pos (inv_pos.2 hc)]
  calc (Fintype.card (R m) : ℝ)⁻¹ * |∑ ρ', (a m ρ' - L)|
      ≤ (Fintype.card (R m) : ℝ)⁻¹ * ∑ _ρ' : R m, |a m (ρ m) - L| :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun ρ' _ ↦ hρ m ρ' (Finset.mem_univ _))) (inv_nonneg.2 hc.le)
    _ = |a m (ρ m) - L| := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp

/-- **Loh's CLT for additive integrands** (post #2; Loh 2003, for `f = Σ_j g_j(x_j)`): for
`(0,m,s)`-nets in base `b` with `m` digits, scrambled by independent uniform nested scrambles
with independent uniform remainders, and `g_j` measurable and `C¹` on `[0,1]` with at least one
non-constant, the scrambled-net estimator standardised by its own standard deviation converges in
distribution to `N(0,1)`: `(μ̂ - μ)/√Var(μ̂) ⇒ N(0,1)` as `n = b^m → ∞`. -/
theorem tendstoInDistribution_scrambledLaw_addFn (hb : 1 < b) {s : ℕ}
    (d : (m : ℕ) → Fin (b ^ m) → Fin s → Fin m → Fin b)
    (hnet : ∀ m, IsNet b 0 m fun i j ↦ digitPoint (d m i j) 0) {g g' : Fin s → ℝ → ℝ}
    (hgm : ∀ j, Measurable (g j))
    (hg : ∀ j, ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (g j) (g' j x) (Icc 0 1) x)
    (hg' : ∀ j, ContinuousOn (g' j) (Icc 0 1)) (hnc : ∃ j, ∃ x ∈ Icc (0 : ℝ) 1, g j x ≠ g j 0)
    [∀ m, IsProbabilityMeasure (scrambledLaw (addFn g) (d m))]
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun m x ↦ (x - ∫ y, addFn g y ∂(uniformCube s)) /
      Real.sqrt Var[fun x ↦ x; scrambledLaw (addFn g) (d m)]) atTop Z
      (fun m ↦ scrambledLaw (addFn g) (d m)) P' := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hgc : ∀ j, ContinuousOn (g j) (Icc 0 1) := fun j x hx ↦ (hg j x hx).continuousWithinAt
  have hrem : ∀ m, IsProbabilityMeasure (remLaw s (b ^ m)) := fun m ↦
    isProbabilityMeasure_remLaw s _
  have hseq := fun ρ ↦ tendstoInDistribution_scrambledEstimate_addFn hb d hnet hgm hg hg' hnc ρ hZ
  have hY : ∀ m, Measurable (fun x : ℝ ↦ (x - ∫ y, addFn g y ∂(uniformCube s)) /
      Real.sqrt Var[fun x ↦ x; scrambledLaw (addFn g) (d m)]) := fun m ↦
    (measurable_id.sub_const _).div_const _
  rw [tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ (fun m ↦ (hY m).aemeasurable)
    hZ.aemeasurable]
  intro φ
  have hvar : ∀ m, Var[fun x ↦ x; scrambledLaw (addFn g) (d m)] =
      ∑ j, stratVar (b ^ m) (g j) := fun m ↦ variance_scrambledLaw_addFn hb0 (hnet m) hgm hgc
  have hmean : ∫ y, addFn g y ∂(uniformCube s) = ∑ j, ∫ x, g j x ∂uniformIco :=
    integral_addFn hgm hgc
  have hint : ∀ m, ∫ x, φ ((x - ∫ y, addFn g y ∂(uniformCube s)) /
      Real.sqrt Var[fun x ↦ x; scrambledLaw (addFn g) (d m)]) ∂(scrambledLaw (addFn g) (d m)) =
      (Fintype.card (Fin s → Scramble b m) : ℝ)⁻¹ * ∑ ρ, ∫ u,
        φ ((scrambledEstimate (addFn g) (d m) ρ u - ∑ j, ∫ x, g j x ∂uniformIco) /
          Real.sqrt (∑ j, stratVar (b ^ m) (g j))) ∂(remLaw s (b ^ m)) := by
    intro m
    rw [hvar m, hmean]
    unfold scrambledLaw
    exact integral_mixLaw (measurable_scrambledEstimate (measurable_addFn hgm) (d m))
      (g := fun x ↦ φ ((x - ∑ j, ∫ x, g j x ∂uniformIco) /
        Real.sqrt (∑ j, stratVar (b ^ m) (g j))))
      (φ.continuous.comp ((continuous_id.sub continuous_const).div_const _))
      fun ρ ↦ Integrable.of_bound
        ((φ.continuous.measurable.comp (((measurable_scrambledEstimate (measurable_addFn hgm)
          (d m) ρ).sub_const _).div_const _)).aestronglyMeasurable) ‖φ‖
        (Eventually.of_forall fun u ↦ φ.norm_coe_le_norm _)
  simp only [hint]
  refine tendsto_avg_of_forall (R := fun m ↦ Fin s → Scramble b m) fun ρ ↦ ?_
  exact ((tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    (hseq ρ).forall_aemeasurable hZ.aemeasurable).1 (hseq ρ)) φ

/-- **Owen's bounds for the scrambled Hammersley net** (`s = 2`, any base `b ≥ 2`):
`Var(μ̂) ≤ (b/(b-1)) σ²/n ≤ e σ²/n` (so `≤ 2σ²/n` in base `2`), for every measurable
`f ∈ L²([0,1)²)`. The hypotheses of the general theorems are satisfiable. -/
theorem variance_scrambledLaw_hammersley_le (hb : 1 < b) (m : ℕ) {f : (Fin 2 → ℝ) → ℝ}
    (hfm : Measurable f) (hf : MemLp f 2 (uniformCube 2)) :
    Var[fun x ↦ x; scrambledLaw f (hammersleyDigits (lt_trans Nat.zero_lt_one hb) m)] ≤
      ((b : ℝ) / ((b : ℝ) - 1)) * Var[f; uniformCube 2] / (b ^ m : ℕ) ∧
    Var[fun x ↦ x; scrambledLaw f (hammersleyDigits (lt_trans Nat.zero_lt_one hb) m)] ≤
      Real.exp 1 * Var[f; uniformCube 2] / (b ^ m : ℕ) := by
  have h1 := variance_scrambledLaw_le hb le_rfl (isNet_hammersley hb m) (by omega) hfm hf
  rw [show 2 - 1 = 1 from rfl, pow_one] at h1
  exact ⟨h1, variance_scrambledLaw_le_exp_one hb le_rfl (isNet_hammersley hb m) hb hfm hf⟩

/-- **The scrambled Hammersley net beats Monte Carlo asymptotically**: `n Var(μ̂) → 0` for
every measurable `f ∈ L²([0,1)²)`. -/
theorem tendsto_variance_scrambledLaw_hammersley (hb : 1 < b) {f : (Fin 2 → ℝ) → ℝ}
    (hfm : Measurable f) (hf : MemLp f 2 (uniformCube 2)) :
    Tendsto (fun m ↦ (b : ℝ) ^ m *
      Var[fun x ↦ x; scrambledLaw f (hammersleyDigits (lt_trans Nat.zero_lt_one hb) m)])
      atTop (𝓝 0) :=
  tendsto_pow_mul_variance_scrambledLaw hb (by norm_num) (by omega) _ (isNet_hammersley hb) hfm hf

/-- **Loh's CLT for the scrambled Hammersley net and additive integrands**: in `s = 2`
dimensions, for `f(x) = g₀(x₀) + g₁(x₁)` with `C¹` coordinates, one non-constant,
`(μ̂ - μ)/√Var(μ̂) ⇒ N(0,1)`. -/
theorem tendstoInDistribution_scrambledLaw_hammersley (hb : 1 < b) {g g' : Fin 2 → ℝ → ℝ}
    (hgm : ∀ j, Measurable (g j))
    (hg : ∀ j, ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (g j) (g' j x) (Icc 0 1) x)
    (hg' : ∀ j, ContinuousOn (g' j) (Icc 0 1)) (hnc : ∃ j, ∃ x ∈ Icc (0 : ℝ) 1, g j x ≠ g j 0)
    [∀ m, IsProbabilityMeasure
      (scrambledLaw (addFn g) (hammersleyDigits (lt_trans Nat.zero_lt_one hb) m))]
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun m x ↦ (x - ∫ y, addFn g y ∂(uniformCube 2)) /
      Real.sqrt Var[fun x ↦ x;
        scrambledLaw (addFn g) (hammersleyDigits (lt_trans Nat.zero_lt_one hb) m)]) atTop Z
      (fun m ↦ scrambledLaw (addFn g) (hammersleyDigits (lt_trans Nat.zero_lt_one hb) m)) P' :=
  tendstoInDistribution_scrambledLaw_addFn hb _ (isNet_hammersley hb) hgm hg hg' hnc hZ

/-- The **random digital shift as a nested scramble**: the permutation at every node of level
`k` is the same translation `x ↦ x + c_k` (mod `b`), whatever the prefix. -/
def digitShiftScramble {D : ℕ} [NeZero b] (c : Fin D → Fin b) : Scramble b D :=
  fun node ↦ Equiv.addRight (c node.1)

/-- The digital shift adds the shift digitwise. -/
theorem scramble_digitShiftScramble {D : ℕ} [NeZero b] (c x : Fin D → Fin b) (k : Fin D) :
    scramble (digitShiftScramble c) x k = x k + c k := rfl

/-- **The digital shift does not have Owen's pair law** (post #2's contrast between the digital
shift and nested uniform scrambling). In base `2` with two digits, the strings `x = 00` and
`x' = 10` (no common leading digit) are sent to `y = 00`, `y' = 11` by NO digital shift, whereas a
positive fraction of nested uniform scrambles does so (`card_scramble_pair`): under the digital
shift the difference `σx' - σx = x' - x` is fixed, so the scrambled pair is far from uniform on
the pairs with the same common prefix. -/
theorem digitShift_ne_pair_law :
    (∀ c : Fin 2 → Fin 2, ¬ (scramble (digitShiftScramble c) ![0, 0] = ![0, 0] ∧
      scramble (digitShiftScramble c) ![1, 0] = ![1, 1])) ∧
    0 < (Finset.univ.filter fun ρ : Scramble 2 2 ↦
      scramble ρ ![0, 0] = ![0, 0] ∧ scramble ρ ![1, 0] = ![1, 1]).card := by
  constructor
  · rintro c ⟨h1, h2⟩
    have e0 := congrFun h1 0
    have e1 := congrFun h2 0
    have e2 := congrFun h1 1
    have e3 := congrFun h2 1
    rw [scramble_digitShiftScramble] at e0 e1 e2 e3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at e0 e1 e2 e3
    rw [zero_add] at e0 e2
    rw [e2] at e3
    exact absurd e3 (by decide)
  · have hcp : commonPrefix (![0, 0] : Fin 2 → Fin 2) ![1, 0] = 0 := by
      by_contra h
      have h1 : 1 ≤ commonPrefix (![0, 0] : Fin 2 → Fin 2) ![1, 0] := Nat.one_le_iff_ne_zero.2 h
      have := (agree_iff_le_commonPrefix (by norm_num) _ _).2 h1 0 (by norm_num)
      exact absurd this (by decide)
    have h := card_scramble_pair (b := 2) (by norm_num) ![0, 0] ![1, 0] ![0, 0] ![1, 1]
    rw [hcp, pairKernel_eq_const (by norm_num) (fun l hl ↦ absurd hl (Nat.not_lt_zero _))
      (by decide)] at h
    have hpos : (0 : ℝ) < (Fintype.card (Scramble 2 2) : ℝ) *
        ((2 : ℕ) : ℝ) ^ (0 + 1) /
          ((((2 : ℕ) : ℝ) - 1) * ((2 : ℕ) : ℝ) ^ 2 * ((2 : ℕ) : ℝ) ^ 2) := by
      have : (0 : ℝ) < (Fintype.card (Scramble 2 2) : ℝ) := Nat.cast_pos.2 Fintype.card_pos
      norm_num
      positivity
    rw [mul_div_assoc] at hpos
    rw [← h] at hpos
    exact_mod_cast hpos

end RQMCMarkov.OwenScrambling

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The variance of scrambled `(0,m,2)`-nets for smooth integrands: `Var ≍ n⁻³ log n`

Towards Loh's (2003) CLT beyond additive integrands (post #2). Loh's proof needs the exact order
of `Var(μ̂)`, Owen's (1997b) `n^{-3} (log n)^{s-1}`; this module proves it for `s = 2`, for
scrambled `(0,m,2)`-nets in any base `b ≥ 2` with `m` digits, from the gain-coefficient formula
of `ScrambleVariance`/`ScrambleGain` and an analysis of the base-`b` Haar coefficients of smooth
integrands.

**Smoothness hypotheses (reading).** Stated through the mixed difference
`mixDiff f x x' = f(x₀,x₁) - f(x₀,x'₁) - f(x'₀,x₁) + f(x'₀,x'₁)`:
* `|mixDiff f x x'| ≤ M |Δx₀| |Δx₁|` on the cube (bounded mixed derivative `∂²f/∂x₀∂x₁`);
* `|f x - f x'| ≤ L (|Δx₀| + |Δx₁|)` on the cube (Lipschitz);
* near a point `xc` of `[0,1)²`, `mixDiff f x x' = g₀ Δx₀ Δx₁ + o(|Δx₀| |Δx₁|)` uniformly, with
  `g₀ ≠ 0` (a non-vanishing strict mixed derivative at `xc`).
For `f` with a mixed partial `∂²f/∂x₀∂x₁` continuous on `[0,1]²` the first and third follow from
the mean value theorem (`abs_sub_sub_mul_le_of_deriv`, `abs_mixDiff_sub_le_of_deriv`,
`variance_scrambledLaw_two_asymp_of_deriv`); `prodFn` (`x₀ x₁`) satisfies all three with
`M = L = g₀ = 1`.

## Main results

* `haarProj`, `haarVar_eq_sum_sq`: `σ²_ℓ` is the mean square of the Haar projection `P_ℓ F`.
* `sum_mul_mul_eq_mixed`, `haarProj_cellAvg_eq`: in two dimensions `P_ℓ F` is a kernel average
  of mixed differences of `f` (the detail kernels have zero row sums).
* `abs_haarProj_cellAvg_le`, `haarVar_cellAvg_le`: `σ²_ℓ ≤ 16 M² b^{-2κ₀} b^{-2κ₁}` at levels
  `(κ₀ + 1, κ₁ + 1)`.
* `sum_agreeKernel_mul_cellVal`, `sum_detailKernel_mul_cellVal`, `abs_haarProj_cellAvg_ge`,
  `card_prefixVal_digit_eq`, `haarVar_cellAvg_ge`: `σ²_ℓ ≥ c b^{-2κ₀} b^{-2κ₁}` when
  `κ₀, κ₁ ≥ k`, from the cells near `xc` whose digit `κ_j` is `0`.
* `gainSeq_two_one`, `lvec2`, `gainCoeff_lvec2`: the `m` components with `κ₀ + κ₁ = m - 1` have
  gain `b/(b-1)`.
* `pow_mul_variance_scrambledLaw_two_ge` (**lower bound**):
  `b^{3m} Var(μ̂) ≥ (m - 2k) g₀² (b-1)⁴/(64 b^{2k+4})`.
* `cellResVar_le`, `sum_range_ite_pow_le`, `pow_mul_variance_scrambledLaw_two_le`
  (**upper bound**): `b^{3m} Var(μ̂) ≤ 4 L² + 64 M² b² (m + 1)`.
* `variance_scrambledLaw_two_asymp` (**Owen 1997b, `s = 2`**): `c m ≤ b^{3m} Var(μ̂) ≤ C (m+1)`
  eventually, i.e. `Var(μ̂) ≍ n^{-3} log n`; `variance_scrambledLaw_two_asymp_of_deriv`: the
  same for `f` Lipschitz with a continuous mixed partial derivative, non-zero at some point.
* `prodFn`, `mixDiff_prodFn`, `variance_scrambledLaw_prodFn`: for `f = x₀ x₁`,
  `m (b-1)⁴/(64 b⁴) ≤ b^{3m} Var(μ̂) ≤ 4 + 64 b² (m+1)` for every `(0,m,2)`-net, e.g. the
  Hammersley net. Compare `n³ Var(μ̂) → const` for additive `f`
  (`LohCLT.tendsto_cube_mul_variance_scrambledLaw_addFn`): interactions add the `log n`.
* `avg_variance_scrambledEstimate`: `E_ρ[Var(μ̂ | ρ)] = n⁻¹ σ²_{>D}` (any `s`, any point set).
* `tendsto_avg_variance_given_scramble_div`: for the smooth non-degenerate integrands above,
  `E_ρ[Var(μ̂ | ρ)]/Var(μ̂) → 0`.

## What remains for Loh's CLT (not formalised)

By `tendsto_avg_variance_given_scramble_div` and the law of total variance, for non-additive
smooth `f` almost all of `Var(μ̂)` is `Var(E[μ̂ | ρ])`, the fluctuation of
`E[μ̂ | ρ] = n⁻¹ Σ_i F(σ d_i)` under the nested scramble alone, where the points are dependent. So
the conditional-on-the-scramble Lindeberg argument behind the additive case
(`LohCLT.tendstoInDistribution_scrambledEstimate_addFn`) cannot give the general CLT. Conditioning
on the top levels instead does not split the points into independent blocks once `s ≥ 2`: a
point depends on one subtree in each coordinate, and the points sharing a subtree in coordinate
`0` and those sharing one in coordinate `1` interlock. The CLT for `E[μ̂ | ρ]` is what Loh's
Stein-method argument supplies. (Heuristically, each of the `m` resolution splits
`κ₀ + κ₁ = m - 1` contributes a two-way array in the level-`κ₀` and level-`κ₁` node
permutations of the two coordinates, centred in each coordinate separately, which need not be
normal by itself; normality comes from aggregating the `≍ log n` splits. This is not
formalised.) Also not formalised: general `s` (the `(log n)^{s-1}` order needs `s`-fold mixed
differences), nets with `t > 0`, and the infinite-depth identification of the scramble in `s`
dimensions (`Owen1DDeep` does `s = 1`).
-/

namespace RQMCMarkov.OwenScrambling

open MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal Topology

variable {b D : ℕ}

/-- The Haar projection `P_ℓ F(z) = Σ_y H_ℓ(z, y) F(y)` of a function on the digit grid. -/
noncomputable def haarProj {s : ℕ} (ℓ : Fin s → Fin (D + 1)) (F : (Fin s → Fin D → Fin b) → ℝ)
    (z : Fin s → Fin D → Fin b) : ℝ :=
  ∑ y, haarKernel ℓ z y * F y

/-- The variance component is the mean square of the Haar projection. -/
theorem haarVar_eq_sum_sq (hb : 0 < b) {s : ℕ} (F : (Fin s → Fin D → Fin b) → ℝ)
    (ℓ : Fin s → Fin (D + 1)) :
    haarVar F ℓ = (∑ z, haarProj ℓ F z ^ 2) / ((b : ℝ) ^ D) ^ s := by
  unfold haarVar
  rw [qform_eq_sum_sq (haarKernel_comm ℓ) (sum_haarKernel_mul hb ℓ)]
  congr 1
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  unfold haarProj
  congr 1
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [haarKernel_comm ℓ y z, mul_comm]

/-- The detail kernels of positive level have zero row sums. -/
theorem sum_detailKernel_succ (hb : 0 < b) (κ : ℕ) (x : Fin D → Fin b) :
    ∑ y, detailKernel (κ + 1) x y = 0 := by
  change ∑ y, (agreeKernel (κ + 1) x y - agreeKernel κ x y) = 0
  rw [Finset.sum_sub_distrib, sum_agreeKernel hb, sum_agreeKernel hb, sub_self]

/-- The averaging kernels are nonnegative. -/
theorem agreeKernel_nonneg (r : ℕ) (x y : Fin D → Fin b) : 0 ≤ agreeKernel r x y := by
  unfold agreeKernel
  split_ifs
  · exact div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (Nat.cast_nonneg _) _)
  · exact le_rfl

/-- The detail kernels of positive level have absolute row sums at most `2`. -/
theorem sum_abs_detailKernel_succ_le (hb : 0 < b) (κ : ℕ) (x : Fin D → Fin b) :
    ∑ y, |detailKernel (κ + 1) x y| ≤ 2 := by
  change ∑ y, |agreeKernel (κ + 1) x y - agreeKernel κ x y| ≤ 2
  calc ∑ y, |agreeKernel (κ + 1) x y - agreeKernel κ x y|
      ≤ ∑ y, (agreeKernel (κ + 1) x y + agreeKernel κ x y) := by
        refine Finset.sum_le_sum fun y _ ↦ ?_
        rw [abs_le]
        constructor <;> linarith [agreeKernel_nonneg (κ + 1) x y, agreeKernel_nonneg κ x y]
    _ = 2 := by rw [Finset.sum_add_distrib, sum_agreeKernel hb, sum_agreeKernel hb]; norm_num

/-- The detail kernel of level `κ + 1` lives on the level-`κ` cell. -/
theorem agree_of_detailKernel_ne_zero {κ : ℕ} {x y : Fin D → Fin b}
    (h : detailKernel (κ + 1) x y ≠ 0) : Agree κ x y := by
  by_contra hc
  apply h
  change agreeKernel (κ + 1) x y - agreeKernel κ x y = 0
  unfold agreeKernel
  rw [ite_eq_right hc, ite_eq_right fun h' ↦ hc (agree_mono (Nat.le_succ κ) h'), sub_zero]

/-- Strings agreeing on `κ ≤ D` digits have cell indices less than `b^{D-κ}` apart. -/
theorem abs_cellVal_sub_lt (hb : 0 < b) {κ : ℕ} (hκ : κ ≤ D) {x y : Fin D → Fin b}
    (h : Agree κ x y) : |(cellVal x : ℝ) - cellVal y| < (b : ℝ) ^ (D - κ) := by
  have hq : 0 < b ^ (D - κ) := Nat.pow_pos hb
  have hx := prefixVal_div hb x hκ
  have hy := prefixVal_div hb y hκ
  have hxy := (prefixVal_eq_iff_agree hb hκ x y).2 h
  change cellVal x / b ^ (D - κ) = prefixVal x κ at hx
  change cellVal y / b ^ (D - κ) = prefixVal y κ at hy
  set q := b ^ (D - κ) with hqdef
  have e1 := Nat.div_add_mod (cellVal x) q
  have e2 := Nat.div_add_mod (cellVal y) q
  have m1 := Nat.mod_lt (cellVal x) hq
  have m2 := Nat.mod_lt (cellVal y) hq
  rw [hx, hxy] at e1
  rw [hy] at e2
  set P := prefixVal y κ
  set rx := cellVal x % q
  set ry := cellVal y % q
  have ex : ((cellVal x : ℕ) : ℝ) = (q : ℝ) * P + rx := by exact_mod_cast e1.symm
  have ey : ((cellVal y : ℕ) : ℝ) = (q : ℝ) * P + ry := by exact_mod_cast e2.symm
  have m1' : (rx : ℝ) < q := by exact_mod_cast m1
  have m2' : (ry : ℝ) < q := by exact_mod_cast m2
  have hq' : ((b : ℝ) ^ (D - κ)) = q := by rw [hqdef, Nat.cast_pow]
  rw [hq', ex, ey, abs_lt]
  have h0x : (0 : ℝ) ≤ rx := Nat.cast_nonneg _
  have h0y : (0 : ℝ) ≤ ry := Nat.cast_nonneg _
  constructor <;> linarith

/-- Two digit points with the same remainder and strings agreeing on `κ` digits are less than
`b^{-κ}` apart. -/
theorem abs_digitPoint_sub_le (hb : 0 < b) {κ : ℕ} (hκ : κ ≤ D) {x y : Fin D → Fin b}
    (h : Agree κ x y) (u : ℝ) :
    |digitPoint x u - digitPoint y u| ≤ ((b : ℝ) ^ κ)⁻¹ := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have hD : (0 : ℝ) < (b : ℝ) ^ D := pow_pos hb' D
  have e : digitPoint x u - digitPoint y u = ((cellVal x : ℝ) - cellVal y) / (b : ℝ) ^ D := by
    unfold digitPoint
    ring
  rw [e, abs_div, abs_of_pos hD, div_le_iff₀ hD]
  have hlt := abs_cellVal_sub_lt hb hκ h
  have hpow : (b : ℝ) ^ D = (b : ℝ) ^ (D - κ) * (b : ℝ) ^ κ := by
    rw [← pow_add, Nat.sub_add_cancel hκ]
  rw [hpow, show ((b : ℝ) ^ κ)⁻¹ * ((b : ℝ) ^ (D - κ) * (b : ℝ) ^ κ) = (b : ℝ) ^ (D - κ) by
    field_simp]
  exact hlt.le

/-- Sums over pairs `Fin 2 → X` as double sums. -/
theorem sum_fin_two_pi {X : Type*} [Fintype X] (G : (Fin 2 → X) → ℝ) :
    ∑ y, G y = ∑ y₀, ∑ y₁, G ![y₀, y₁] := by
  rw [← Fintype.sum_prod_type (f := fun p : X × X ↦ G ![p.1, p.2])]
  refine Fintype.sum_equiv (finTwoArrowEquiv X) _ _ fun y ↦ ?_
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The two-dimensional Haar kernel is a product. -/
theorem haarKernel_two (ℓ : Fin 2 → Fin (D + 1)) (z y : Fin 2 → Fin D → Fin b) :
    haarKernel ℓ z y = detailKernel (ℓ 0) (z 0) (y 0) * detailKernel (ℓ 1) (z 1) (y 1) :=
  Fin.prod_univ_two _

/-- **Mixed differences**: with zero row sums, a double kernel sum only sees the mixed
difference `φ(y₀,y₁) - φ(y₀,w₁) - φ(w₀,y₁) + φ(w₀,w₁)`. -/
theorem sum_mul_mul_eq_mixed {X : Type*} [Fintype X] (h₀ h₁ : X → ℝ) (hs₀ : ∑ y, h₀ y = 0)
    (hs₁ : ∑ y, h₁ y = 0) (φ : X → X → ℝ) (w₀ w₁ : X) :
    ∑ y₀, ∑ y₁, h₀ y₀ * h₁ y₁ * φ y₀ y₁ = ∑ y₀, ∑ y₁, h₀ y₀ * h₁ y₁ *
      (φ y₀ y₁ - φ y₀ w₁ - φ w₀ y₁ + φ w₀ w₁) := by
  have e1 : ∑ y₀, ∑ y₁, h₀ y₀ * h₁ y₁ * φ y₀ w₁ = 0 := by
    refine Finset.sum_eq_zero fun y₀ _ ↦ ?_
    rw [show (∑ y₁, h₀ y₀ * h₁ y₁ * φ y₀ w₁) = h₀ y₀ * φ y₀ w₁ * ∑ y₁, h₁ y₁ by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring, hs₁, mul_zero]
  have e2 : ∑ y₀, ∑ y₁, h₀ y₀ * h₁ y₁ * φ w₀ y₁ = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun y₁ _ ↦ ?_
    rw [show (∑ y₀, h₀ y₀ * h₁ y₁ * φ w₀ y₁) = h₁ y₁ * φ w₀ y₁ * ∑ y₀, h₀ y₀ by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring, hs₀, mul_zero]
  have e3 : ∑ y₀, ∑ y₁, h₀ y₀ * h₁ y₁ * φ w₀ w₁ = 0 := by
    refine Finset.sum_eq_zero fun y₀ _ ↦ ?_
    rw [show (∑ y₁, h₀ y₀ * h₁ y₁ * φ w₀ w₁) = h₀ y₀ * φ w₀ w₁ * ∑ y₁, h₁ y₁ by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring, hs₁, mul_zero]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, e1, e2, e3]
  ring

/-- The **mixed difference** of a function of two variables:
`f(x₀,x₁) - f(x₀,x'₁) - f(x'₀,x₁) + f(x'₀,x'₁)`. -/
noncomputable def mixDiff (f : (Fin 2 → ℝ) → ℝ) (x x' : Fin 2 → ℝ) : ℝ :=
  f x - f ![x 0, x' 1] - f ![x' 0, x 1] + f x'

/-- The mixed difference of cell averages is the average of the mixed differences of `f` at
points with common remainders. -/
theorem cellAvg_mixed_eq (hb : 0 < b) {f : (Fin 2 → ℝ) → ℝ} (hf : MemLp f 2 (uniformCube 2))
    (y₀ y₁ z₀ z₁ : Fin D → Fin b) :
    cellAvg f ![y₀, y₁] - cellAvg f ![y₀, z₁] - cellAvg f ![z₀, y₁] + cellAvg f ![z₀, z₁] =
      ∫ u, mixDiff f (cellPoint ![y₀, y₁] u) (cellPoint ![z₀, z₁] u) ∂(uniformCube 2) := by
  have hI : ∀ y : Fin 2 → Fin D → Fin b,
      Integrable (fun u ↦ f (cellPoint y u)) (uniformCube 2) := fun y ↦
    (memLp_comp_cellPoint hb hf y).integrable one_le_two
  have c1 : ∀ u : Fin 2 → ℝ, cellPoint ![y₀, z₁] u =
      ![cellPoint ![y₀, y₁] u 0, cellPoint ![z₀, z₁] u 1] := fun u ↦ by
    funext j
    fin_cases j <;> rfl
  have c2 : ∀ u : Fin 2 → ℝ, cellPoint ![z₀, y₁] u =
      ![cellPoint ![z₀, z₁] u 0, cellPoint ![y₀, y₁] u 1] := fun u ↦ by
    funext j
    fin_cases j <;> rfl
  unfold cellAvg mixDiff
  simp only [← c1, ← c2]
  rw [integral_add (f := fun u ↦ f (cellPoint ![y₀, y₁] u) - f (cellPoint ![y₀, z₁] u) -
      f (cellPoint ![z₀, y₁] u)) (g := fun u ↦ f (cellPoint ![z₀, z₁] u))
      (((hI _).sub (hI _)).sub (hI _)) (hI _),
    integral_sub (f := fun u ↦ f (cellPoint ![y₀, y₁] u) - f (cellPoint ![y₀, z₁] u))
      (g := fun u ↦ f (cellPoint ![z₀, y₁] u)) ((hI _).sub (hI _)) (hI _),
    integral_sub (hI _) (hI _)]

/-- The Haar projection of the cell averages at a two-dimensional component of levels
`(κ₀ + 1, κ₁ + 1)`, as a double sum of averaged mixed differences. -/
theorem haarProj_cellAvg_eq (hb : 0 < b) {f : (Fin 2 → ℝ) → ℝ} (hf : MemLp f 2 (uniformCube 2))
    {ℓ : Fin 2 → Fin (D + 1)} {κ : Fin 2 → ℕ} (hℓ : ∀ j, (ℓ j : ℕ) = κ j + 1)
    (z : Fin 2 → Fin D → Fin b) :
    haarProj ℓ (cellAvg f) z = ∑ y₀, ∑ y₁, detailKernel (κ 0 + 1) (z 0) y₀ *
      detailKernel (κ 1 + 1) (z 1) y₁ *
        ∫ u, mixDiff f (cellPoint ![y₀, y₁] u) (cellPoint z u) ∂(uniformCube 2) := by
  unfold haarProj
  rw [sum_fin_two_pi]
  simp only [haarKernel_two, hℓ]
  have hz : z = ![z 0, z 1] := by
    funext j
    fin_cases j <;> rfl
  have hfin : ∀ (y₀ y₁ : Fin D → Fin b), (![y₀, y₁] : Fin 2 → Fin D → Fin b) 0 = y₀ ∧
      (![y₀, y₁] : Fin 2 → Fin D → Fin b) 1 = y₁ := fun _ _ ↦ ⟨rfl, rfl⟩
  simp only [hfin]
  rw [sum_mul_mul_eq_mixed _ _ (sum_detailKernel_succ hb _ _) (sum_detailKernel_succ hb _ _)
    (fun y₀ y₁ ↦ cellAvg f ![y₀, y₁]) (z 0) (z 1)]
  refine Finset.sum_congr rfl fun y₀ _ ↦ Finset.sum_congr rfl fun y₁ _ ↦ ?_
  rw [cellAvg_mixed_eq hb hf, ← hz]

/-- **Upper bound on a two-dimensional Haar projection**: if the mixed differences of `f` on the
cube are bounded by `M |Δx₀| |Δx₁|`, then `|P_ℓ F| ≤ 4 M b^{-κ₀} b^{-κ₁}` for the component of
levels `(κ₀ + 1, κ₁ + 1)`. -/
theorem abs_haarProj_cellAvg_le (hb : 0 < b) {f : (Fin 2 → ℝ) → ℝ}
    (hf : MemLp f 2 (uniformCube 2)) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      |mixDiff f x x'| ≤ M * |x 0 - x' 0| * |x 1 - x' 1|)
    {ℓ : Fin 2 → Fin (D + 1)} {κ : Fin 2 → ℕ} (hℓ : ∀ j, (ℓ j : ℕ) = κ j + 1)
    (hκD : ∀ j, κ j ≤ D) (z : Fin 2 → Fin D → Fin b) :
    |haarProj ℓ (cellAvg f) z| ≤ 4 * M * ((b : ℝ) ^ κ 0)⁻¹ * ((b : ℝ) ^ κ 1)⁻¹ := by
  have hU := isProbabilityMeasure_uniformCube 2
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  set β₀ := ((b : ℝ) ^ κ 0)⁻¹ with hβ₀
  set β₁ := ((b : ℝ) ^ κ 1)⁻¹ with hβ₁
  have hβ₀0 : 0 ≤ β₀ := inv_nonneg.2 (pow_nonneg hb'.le _)
  have hβ₁0 : 0 ≤ β₁ := inv_nonneg.2 (pow_nonneg hb'.le _)
  rw [haarProj_cellAvg_eq hb hf hℓ]
  set h₀ := fun y₀ ↦ detailKernel (κ 0 + 1) (z 0) y₀
  set h₁ := fun y₁ ↦ detailKernel (κ 1 + 1) (z 1) y₁
  have hB : ∀ y₀ y₁, h₀ y₀ ≠ 0 → h₁ y₁ ≠ 0 →
      |∫ u, mixDiff f (cellPoint ![y₀, y₁] u) (cellPoint z u) ∂(uniformCube 2)| ≤
        M * β₀ * β₁ := by
    intro y₀ y₁ h0 h1
    have a0 := agree_of_detailKernel_ne_zero h0
    have a1 := agree_of_detailKernel_ne_zero h1
    have h := norm_integral_le_of_norm_le_const (μ := uniformCube 2) (C := M * β₀ * β₁)
      (f := fun u ↦ mixDiff f (cellPoint ![y₀, y₁] u) (cellPoint z u)) (by
        filter_upwards [ae_mem_cube_uniformCube 2] with u hu
        rw [Real.norm_eq_abs]
        refine (hM _ _ (fun j ↦ digitPoint_mem_Ico hb _ (hu j))
          (fun j ↦ digitPoint_mem_Ico hb _ (hu j))).trans ?_
        have d0 : |cellPoint ![y₀, y₁] u 0 - cellPoint z u 0| ≤ β₀ :=
          abs_digitPoint_sub_le hb (hκD 0) (agree_symm a0) _
        have d1 : |cellPoint ![y₀, y₁] u 1 - cellPoint z u 1| ≤ β₁ :=
          abs_digitPoint_sub_le hb (hκD 1) (agree_symm a1) _
        calc M * |cellPoint ![y₀, y₁] u 0 - cellPoint z u 0| *
              |cellPoint ![y₀, y₁] u 1 - cellPoint z u 1|
            ≤ M * β₀ * β₁ := by
              apply mul_le_mul (mul_le_mul_of_nonneg_left d0 hM0) d1 (abs_nonneg _)
              exact mul_nonneg hM0 hβ₀0)
    rwa [probReal_univ, mul_one, Real.norm_eq_abs] at h
  have hterm : ∀ y₀ y₁, |h₀ y₀ * h₁ y₁ *
      ∫ u, mixDiff f (cellPoint ![y₀, y₁] u) (cellPoint z u) ∂(uniformCube 2)| ≤
      |h₀ y₀| * |h₁ y₁| * (M * β₀ * β₁) := by
    intro y₀ y₁
    rw [abs_mul, abs_mul]
    by_cases h0 : h₀ y₀ = 0
    · rw [h0, abs_zero]
      simp only [zero_mul, le_refl]
    by_cases h1 : h₁ y₁ = 0
    · rw [h1, abs_zero]
      simp only [mul_zero, zero_mul, le_refl]
    exact mul_le_mul_of_nonneg_left (hB y₀ y₁ h0 h1)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hs₀ := sum_abs_detailKernel_succ_le hb (κ 0) (z 0)
  have hs₁ := sum_abs_detailKernel_succ_le hb (κ 1) (z 1)
  calc |∑ y₀, ∑ y₁, h₀ y₀ * h₁ y₁ *
        ∫ u, mixDiff f (cellPoint ![y₀, y₁] u) (cellPoint z u) ∂(uniformCube 2)|
      ≤ ∑ y₀, ∑ y₁, |h₀ y₀| * |h₁ y₁| * (M * β₀ * β₁) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y₀ _ ↦
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y₁ _ ↦ hterm y₀ y₁))
    _ = (∑ y₀, |h₀ y₀|) * (∑ y₁, |h₁ y₁|) * (M * β₀ * β₁) := by
        rw [Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun y₀ _ ↦ ?_
        rw [Finset.sum_mul]
    _ ≤ 2 * 2 * (M * β₀ * β₁) := by
        have hMβ : 0 ≤ M * β₀ * β₁ := mul_nonneg (mul_nonneg hM0 hβ₀0) hβ₁0
        refine mul_le_mul_of_nonneg_right ?_ hMβ
        exact mul_le_mul hs₀ hs₁ (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (by norm_num)
    _ = 4 * M * β₀ * β₁ := by ring

/-- **Upper bound on a two-dimensional variance component**:
`σ²_ℓ ≤ 16 M² b^{-2κ₀} b^{-2κ₁}`. -/
theorem haarVar_cellAvg_le (hb : 0 < b) {f : (Fin 2 → ℝ) → ℝ}
    (hf : MemLp f 2 (uniformCube 2)) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      |mixDiff f x x'| ≤ M * |x 0 - x' 0| * |x 1 - x' 1|)
    {ℓ : Fin 2 → Fin (D + 1)} {κ : Fin 2 → ℕ} (hℓ : ∀ j, (ℓ j : ℕ) = κ j + 1)
    (hκD : ∀ j, κ j ≤ D) :
    haarVar (cellAvg (b := b) f) ℓ ≤ (4 * M * ((b : ℝ) ^ κ 0)⁻¹ * ((b : ℝ) ^ κ 1)⁻¹) ^ 2 := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have hbD : (0 : ℝ) < ((b : ℝ) ^ D) ^ 2 := pow_pos (pow_pos hb' D) 2
  rw [haarVar_eq_sum_sq hb, div_le_iff₀ hbD]
  have hcard : ((Finset.univ : Finset (Fin 2 → Fin D → Fin b)).card : ℝ) = ((b : ℝ) ^ D) ^ 2 := by
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    push_cast
    ring
  calc ∑ z, haarProj ℓ (cellAvg f) z ^ 2
      ≤ ∑ _z : Fin 2 → Fin D → Fin b, (4 * M * ((b : ℝ) ^ κ 0)⁻¹ * ((b : ℝ) ^ κ 1)⁻¹) ^ 2 := by
        refine Finset.sum_le_sum fun z _ ↦ ?_
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_haarProj_cellAvg_le hb hf hM0 hM hℓ hκD z) 2
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hcard, mul_comm]

/-- `Σ_{t < q} t = q (q - 1)/2`. -/
theorem sum_range_cast_id (q : ℕ) : ∑ t ∈ Finset.range q, (t : ℝ) = q * (q - 1) / 2 := by
  induction q with
  | zero => rw [Finset.sum_range_zero, Nat.cast_zero, zero_mul, zero_div]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- **The average cell index over a prefix class**: for `r ≤ D`,
`Σ_y K_r(x, y) cellVal y = b^{D-r} prefixVal x r + (b^{D-r} - 1)/2`. -/
theorem sum_agreeKernel_mul_cellVal (hb : 0 < b) {r : ℕ} (hr : r ≤ D) (x : Fin D → Fin b) :
    ∑ y, agreeKernel r x y * (cellVal y : ℝ) =
      (b : ℝ) ^ (D - r) * prefixVal x r + ((b : ℝ) ^ (D - r) - 1) / 2 := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have hq : 0 < b ^ (D - r) := Nat.pow_pos hb
  have hbD : b ^ D = b ^ r * b ^ (D - r) := by rw [← pow_add, Nat.add_sub_cancel' hr]
  set q := b ^ (D - r) with hqdef
  set a := prefixVal x r with ha
  have hcell : ∀ y : Fin D → Fin b, Agree r x y ↔ cellVal y / q = a := by
    intro y
    rw [← prefixVal_eq_iff_agree hb hr, ha, eq_comm, hqdef]
    unfold cellVal
    rw [prefixVal_div hb y hr]
  have halt : a < b ^ r := prefixVal_lt hb x r
  have hsum : ∑ y ∈ Finset.univ.filter (fun y : Fin D → Fin b ↦ Agree r x y), (cellVal y : ℝ) =
      ∑ t ∈ Finset.range q, ((a * q + t : ℕ) : ℝ) := by
    refine Finset.sum_bij (fun y _ ↦ cellVal y - a * q) ?_ ?_ ?_ ?_
    · intro y hy
      rw [Finset.mem_filter, hcell] at hy
      rw [Finset.mem_range]
      have h1 := Nat.div_add_mod (cellVal y) q
      have h2 := Nat.mod_lt (cellVal y) hq
      rw [hy.2] at h1
      have : q * a = a * q := mul_comm _ _
      omega
    · intro y₁ h₁ y₂ h₂ h12
      rw [Finset.mem_filter, hcell] at h₁ h₂
      have e1 := Nat.div_add_mod (cellVal y₁) q
      have e2 := Nat.div_add_mod (cellVal y₂) q
      rw [h₁.2] at e1
      rw [h₂.2] at e2
      have : q * a = a * q := mul_comm _ _
      exact cellVal_injective hb (by omega)
    · intro t ht
      rw [Finset.mem_range] at ht
      have hlt : a * q + t < b ^ D := by
        rw [hbD]
        calc a * q + t < a * q + q := by omega
          _ = (a + 1) * q := by ring
          _ ≤ b ^ r * q := Nat.mul_le_mul_right _ halt
      obtain ⟨y, hy⟩ := (cellFin_bijective (D := D) hb).2 ⟨a * q + t, hlt⟩
      have hv : cellVal y = a * q + t := congrArg Fin.val hy
      refine ⟨y, ?_, ?_⟩
      · rw [Finset.mem_filter, hcell, hv]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [add_comm, Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt ht, zero_add]
      · simp only [hv, Nat.add_sub_cancel_left]
    · intro y hy
      rw [Finset.mem_filter, hcell] at hy
      have h1 := Nat.div_add_mod (cellVal y) q
      rw [hy.2] at h1
      have : q * a = a * q := mul_comm _ _
      congr 1
      omega
  have hK : ∀ y, agreeKernel r x y * (cellVal y : ℝ) =
      if Agree r x y then (b : ℝ) ^ r / (b : ℝ) ^ D * cellVal y else 0 := by
    intro y
    unfold agreeKernel
    rw [min_eq_left hr]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun y _ ↦ hK y, ← Finset.sum_filter, ← Finset.mul_sum, hsum]
  simp only [Nat.cast_add, Nat.cast_mul, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, sum_range_cast_id]
  have hqR : ((q : ℕ) : ℝ) = (b : ℝ) ^ (D - r) := by rw [hqdef, Nat.cast_pow]
  have hbDR : (b : ℝ) ^ D = (b : ℝ) ^ r * (b : ℝ) ^ (D - r) := by
    rw [← pow_add, Nat.add_sub_cancel' hr]
  rw [hqR, hbDR]
  have h1 : (0 : ℝ) < (b : ℝ) ^ r := pow_pos hb' r
  have h2 : (0 : ℝ) < (b : ℝ) ^ (D - r) := pow_pos hb' _
  field_simp

/-- **The first moment of a detail kernel**: for `κ < D`,
`Σ_y δ_{κ+1}(x, y) cellVal y = b^{D-κ-1} (x_κ - (b-1)/2)`. -/
theorem sum_detailKernel_mul_cellVal (hb : 0 < b) {κ : ℕ} (hκ : κ < D) (x : Fin D → Fin b) :
    ∑ y, detailKernel (κ + 1) x y * (cellVal y : ℝ) =
      (b : ℝ) ^ (D - (κ + 1)) * (((x ⟨κ, hκ⟩ : ℕ) : ℝ) - ((b : ℝ) - 1) / 2) := by
  change ∑ y, (agreeKernel (κ + 1) x y - agreeKernel κ x y) * (cellVal y : ℝ) = _
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [sum_agreeKernel_mul_cellVal hb (Nat.succ_le_of_lt hκ),
    sum_agreeKernel_mul_cellVal hb hκ.le]
  change (b : ℝ) ^ (D - (κ + 1)) * ((b * prefixVal x κ + digitAt x κ : ℕ) : ℝ) +
    ((b : ℝ) ^ (D - (κ + 1)) - 1) / 2 -
    ((b : ℝ) ^ (D - κ) * (prefixVal x κ : ℝ) + ((b : ℝ) ^ (D - κ) - 1) / 2) = _
  have hdig : digitAt x κ = (x ⟨κ, hκ⟩ : ℕ) := by
    unfold digitAt
    rw [dite_eq_left hκ]
  have hpow : (b : ℝ) ^ (D - κ) = (b : ℝ) * (b : ℝ) ^ (D - (κ + 1)) := by
    rw [← pow_succ', show D - (κ + 1) + 1 = D - κ by omega]
  rw [hdig, hpow]
  push_cast
  ring

/-- The difference of two digit points with the same remainder. -/
theorem digitPoint_sub_digitPoint (x y : Fin D → Fin b) (u : ℝ) :
    digitPoint x u - digitPoint y u = ((cellVal x : ℝ) - cellVal y) / (b : ℝ) ^ D := by
  unfold digitPoint
  ring

/-- Points in the same `b`-adic interval of level `k` are less than `b^{-k}` apart. -/
theorem abs_sub_lt_of_floor_eq (hb : 0 < b) (k : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : ⌊(b : ℝ) ^ k * x⌋₊ = ⌊(b : ℝ) ^ k * y⌋₊) : |x - y| < ((b : ℝ) ^ k)⁻¹ := by
  have hc : (0 : ℝ) < (b : ℝ) ^ k := pow_pos (Nat.cast_pos.2 hb) k
  have h1 := Nat.floor_le (mul_nonneg hc.le hx)
  have h2 := Nat.lt_floor_add_one ((b : ℝ) ^ k * x)
  have h3 := Nat.floor_le (mul_nonneg hc.le hy)
  have h4 := Nat.lt_floor_add_one ((b : ℝ) ^ k * y)
  rw [h] at h1 h2
  have habs : |(b : ℝ) ^ k * x - (b : ℝ) ^ k * y| < 1 :=
    abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  have e : x - y = ((b : ℝ) ^ k * x - (b : ℝ) ^ k * y) / (b : ℝ) ^ k := by
    field_simp
  rw [e, abs_div, abs_of_pos hc, div_lt_iff₀ hc, inv_mul_cancel₀ hc.ne']
  exact habs

/-- The mixed difference of `f` at two cell points with common remainders is integrable. -/
theorem integrable_mixDiff_cellPoint (hb : 0 < b) {f : (Fin 2 → ℝ) → ℝ}
    (hf : MemLp f 2 (uniformCube 2)) (y z : Fin 2 → Fin D → Fin b) :
    Integrable (fun u ↦ mixDiff f (cellPoint y u) (cellPoint z u)) (uniformCube 2) := by
  have hI : ∀ y : Fin 2 → Fin D → Fin b,
      Integrable (fun u ↦ f (cellPoint y u)) (uniformCube 2) := fun y ↦
    (memLp_comp_cellPoint hb hf y).integrable one_le_two
  have e : (fun u ↦ mixDiff f (cellPoint y u) (cellPoint z u)) = fun u ↦
      f (cellPoint y u) - f (cellPoint ![y 0, z 1] u) - f (cellPoint ![z 0, y 1] u) +
        f (cellPoint z u) := by
    funext u
    unfold mixDiff
    have c1 : (![cellPoint y u 0, cellPoint z u 1] : Fin 2 → ℝ) = cellPoint ![y 0, z 1] u := by
      funext j
      fin_cases j <;> rfl
    have c2 : (![cellPoint z u 0, cellPoint y u 1] : Fin 2 → ℝ) = cellPoint ![z 0, y 1] u := by
      funext j
      fin_cases j <;> rfl
    rw [c1, c2]
  rw [e]
  exact (((hI _).sub (hI _)).sub (hI _)).add (hI _)

/-- **Lower bound on a two-dimensional Haar projection**. Suppose that near `xc` the mixed
differences of `f` are `g₀ Δx₀ Δx₁` up to `ε |Δx₀| |Δx₁|` (a strict mixed derivative `g₀` at
`xc`), and let `z` be a grid point in the level-`k` cube of `xc`, of side `b^{-k} ≤ δ`, whose digit
`κ_j ≥ k` is `0` in each coordinate. Then the Haar projection of levels `(κ₀ + 1, κ₁ + 1)` at `z`
is at least `|g₀| (b-1)²/(4 b^{κ₀+1} b^{κ₁+1}) - 4 ε b^{-κ₀} b^{-κ₁}`. -/
theorem abs_haarProj_cellAvg_ge (hb : 1 < b) {f : (Fin 2 → ℝ) → ℝ}
    (hf : MemLp f 2 (uniformCube 2)) {xc : Fin 2 → ℝ} (hxc : ∀ j, xc j ∈ Set.Ico (0 : ℝ) 1)
    {g₀ ε δ : ℝ} (hε : 0 ≤ ε)
    (hg : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      (∀ j, |x j - xc j| < δ) → (∀ j, |x' j - xc j| < δ) →
      |mixDiff f x x' - g₀ * (x 0 - x' 0) * (x 1 - x' 1)| ≤ ε * |x 0 - x' 0| * |x 1 - x' 1|)
    {k : ℕ} (hk : ((b : ℝ) ^ k)⁻¹ ≤ δ) {ℓ : Fin 2 → Fin (D + 1)} {κ : Fin 2 → ℕ}
    (hℓ : ∀ j, (ℓ j : ℕ) = κ j + 1) (hκk : ∀ j, k ≤ κ j) (hκD : ∀ j, κ j < D)
    {z : Fin 2 → Fin D → Fin b} (hz : ∀ j, prefixVal (z j) k = ⌊(b : ℝ) ^ k * xc j⌋₊)
    (hz0 : ∀ j, ((z j ⟨κ j, hκD j⟩ : Fin b) : ℕ) = 0) :
    |g₀| * ((b : ℝ) - 1) ^ 2 / (4 * (b : ℝ) ^ (κ 0 + 1) * (b : ℝ) ^ (κ 1 + 1)) -
      4 * ε * ((b : ℝ) ^ κ 0)⁻¹ * ((b : ℝ) ^ κ 1)⁻¹ ≤ |haarProj ℓ (cellAvg f) z| := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hU := isProbabilityMeasure_uniformCube 2
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb0
  have hbD : (0 : ℝ) < (b : ℝ) ^ D := pow_pos hb' D
  set β₀ := ((b : ℝ) ^ κ 0)⁻¹ with hβ₀
  set β₁ := ((b : ℝ) ^ κ 1)⁻¹ with hβ₁
  have hβ₀0 : 0 ≤ β₀ := inv_nonneg.2 (pow_nonneg hb'.le _)
  have hβ₁0 : 0 ≤ β₁ := inv_nonneg.2 (pow_nonneg hb'.le _)
  have hkD : k ≤ D := le_trans (hκk 0) (hκD 0).le
  rw [haarProj_cellAvg_eq hb0 hf hℓ]
  set h₀ := fun y₀ ↦ detailKernel (κ 0 + 1) (z 0) y₀ with hh₀
  set h₁ := fun y₁ ↦ detailKernel (κ 1 + 1) (z 1) y₁ with hh₁
  set Δ₀ : (Fin D → Fin b) → ℝ := fun y ↦ ((cellVal y : ℝ) - cellVal (z 0)) / (b : ℝ) ^ D
  set Δ₁ : (Fin D → Fin b) → ℝ := fun y ↦ ((cellVal y : ℝ) - cellVal (z 1)) / (b : ℝ) ^ D
  set B : (Fin D → Fin b) → (Fin D → Fin b) → ℝ := fun y₀ y₁ ↦
    ∫ u, mixDiff f (cellPoint ![y₀, y₁] u) (cellPoint z u) ∂(uniformCube 2) with hB
  -- closeness to `xc`
  have hclose : ∀ (j : Fin 2) (y : Fin D → Fin b), Agree (κ j) (z j) y → ∀ w ∈ Set.Ico (0 : ℝ) 1,
      |digitPoint y w - xc j| < δ := by
    intro j y hy w hw
    have hag : Agree k (z j) y := agree_mono (hκk j) hy
    have hfl : ⌊(b : ℝ) ^ k * digitPoint y w⌋₊ = ⌊(b : ℝ) ^ k * xc j⌋₊ := by
      rw [floor_pow_mul_digitPoint hb0 y hw hkD, ← hz j,
        (prefixVal_eq_iff_agree hb0 hkD _ _).2 (agree_symm hag)]
    exact lt_of_lt_of_le (abs_sub_lt_of_floor_eq hb0 k (digitPoint_mem_Ico hb0 y hw).1
      (hxc j).1 hfl) hk
  have hE : ∀ y₀ y₁, h₀ y₀ ≠ 0 → h₁ y₁ ≠ 0 →
      |B y₀ y₁ - g₀ * Δ₀ y₀ * Δ₁ y₁| ≤ ε * β₀ * β₁ := by
    intro y₀ y₁ h0 h1
    have a0 := agree_of_detailKernel_ne_zero h0
    have a1 := agree_of_detailKernel_ne_zero h1
    have hint := integrable_mixDiff_cellPoint hb0 hf ![y₀, y₁] z
    have e : B y₀ y₁ - g₀ * Δ₀ y₀ * Δ₁ y₁ = ∫ u, (mixDiff f (cellPoint ![y₀, y₁] u)
        (cellPoint z u) - g₀ * Δ₀ y₀ * Δ₁ y₁) ∂(uniformCube 2) := by
      rw [integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul]
    rw [e]
    have h := norm_integral_le_of_norm_le_const (μ := uniformCube 2) (C := ε * β₀ * β₁)
      (f := fun u ↦ mixDiff f (cellPoint ![y₀, y₁] u) (cellPoint z u) -
        g₀ * Δ₀ y₀ * Δ₁ y₁) (by
        filter_upwards [ae_mem_cube_uniformCube 2] with u hu
        rw [Real.norm_eq_abs]
        have p0 : cellPoint ![y₀, y₁] u 0 - cellPoint z u 0 = Δ₀ y₀ :=
          digitPoint_sub_digitPoint _ _ _
        have p1 : cellPoint ![y₀, y₁] u 1 - cellPoint z u 1 = Δ₁ y₁ :=
          digitPoint_sub_digitPoint _ _ _
        have hgu := hg (cellPoint ![y₀, y₁] u) (cellPoint z u)
          (fun j ↦ digitPoint_mem_Ico hb0 _ (hu j)) (fun j ↦ digitPoint_mem_Ico hb0 _ (hu j))
          (fun j ↦ by
            fin_cases j
            · exact hclose 0 y₀ a0 _ (hu 0)
            · exact hclose 1 y₁ a1 _ (hu 1))
          (fun j ↦ hclose j (z j) (fun _ _ ↦ rfl) _ (hu j))
        rw [p0, p1] at hgu
        refine hgu.trans ?_
        have d0 : |Δ₀ y₀| ≤ β₀ := by
          rw [← p0]
          exact abs_digitPoint_sub_le hb0 (hκD 0).le (agree_symm a0) _
        have d1 : |Δ₁ y₁| ≤ β₁ := by
          rw [← p1]
          exact abs_digitPoint_sub_le hb0 (hκD 1).le (agree_symm a1) _
        exact mul_le_mul (mul_le_mul_of_nonneg_left d0 hε) d1 (abs_nonneg _)
          (mul_nonneg hε hβ₀0))
    rwa [probReal_univ, mul_one, Real.norm_eq_abs] at h
  -- the main term
  have hmom : ∀ (j : Fin 2), ∑ y, detailKernel (κ j + 1) (z j) y *
      (((cellVal y : ℝ) - cellVal (z j)) / (b : ℝ) ^ D) =
      -(((b : ℝ) - 1) / (2 * (b : ℝ) ^ (κ j + 1))) := by
    intro j
    have e1 : ∀ y, detailKernel (κ j + 1) (z j) y * (((cellVal y : ℝ) - cellVal (z j)) /
        (b : ℝ) ^ D) = (detailKernel (κ j + 1) (z j) y * (cellVal y : ℝ) -
          detailKernel (κ j + 1) (z j) y * cellVal (z j)) / (b : ℝ) ^ D := fun y ↦ by ring
    rw [Finset.sum_congr rfl fun y _ ↦ e1 y, ← Finset.sum_div, Finset.sum_sub_distrib,
      ← Finset.sum_mul, sum_detailKernel_succ hb0, zero_mul, sub_zero,
      sum_detailKernel_mul_cellVal hb0 (hκD j), hz0 j, Nat.cast_zero, zero_sub]
    have hpow : (b : ℝ) ^ D = (b : ℝ) ^ (D - (κ j + 1)) * (b : ℝ) ^ (κ j + 1) := by
      rw [← pow_add, Nat.sub_add_cancel (hκD j)]
    rw [hpow]
    have : (0 : ℝ) < (b : ℝ) ^ (D - (κ j + 1)) := pow_pos hb' _
    have : (0 : ℝ) < (b : ℝ) ^ (κ j + 1) := pow_pos hb' _
    field_simp
  have hmain : ∑ y₀, ∑ y₁, h₀ y₀ * h₁ y₁ * (g₀ * Δ₀ y₀ * Δ₁ y₁) =
      g₀ * (((b : ℝ) - 1) / (2 * (b : ℝ) ^ (κ 0 + 1))) *
        (((b : ℝ) - 1) / (2 * (b : ℝ) ^ (κ 1 + 1))) := by
    have e2 : ∀ y₀ y₁, h₀ y₀ * h₁ y₁ * (g₀ * Δ₀ y₀ * Δ₁ y₁) =
        g₀ * ((h₀ y₀ * Δ₀ y₀) * (h₁ y₁ * Δ₁ y₁)) := fun _ _ ↦ by ring
    have hm0 : ∑ y, h₀ y * Δ₀ y = -(((b : ℝ) - 1) / (2 * (b : ℝ) ^ (κ 0 + 1))) := hmom 0
    have hm1 : ∑ y, h₁ y * Δ₁ y = -(((b : ℝ) - 1) / (2 * (b : ℝ) ^ (κ 1 + 1))) := hmom 1
    simp only [e2, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [hm0, hm1]
    ring
  -- the error term
  have herr : |∑ y₀, ∑ y₁, h₀ y₀ * h₁ y₁ * (B y₀ y₁ - g₀ * Δ₀ y₀ * Δ₁ y₁)| ≤
      4 * ε * β₀ * β₁ := by
    have hterm : ∀ y₀ y₁, |h₀ y₀ * h₁ y₁ * (B y₀ y₁ - g₀ * Δ₀ y₀ * Δ₁ y₁)| ≤
        |h₀ y₀| * |h₁ y₁| * (ε * β₀ * β₁) := by
      intro y₀ y₁
      rw [abs_mul, abs_mul]
      by_cases h0 : h₀ y₀ = 0
      · rw [h0, abs_zero]
        simp only [zero_mul, le_refl]
      by_cases h1 : h₁ y₁ = 0
      · rw [h1, abs_zero]
        simp only [mul_zero, zero_mul, le_refl]
      exact mul_le_mul_of_nonneg_left (hE y₀ y₁ h0 h1)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hs₀ := sum_abs_detailKernel_succ_le hb0 (κ 0) (z 0)
    have hs₁ := sum_abs_detailKernel_succ_le hb0 (κ 1) (z 1)
    calc |∑ y₀, ∑ y₁, h₀ y₀ * h₁ y₁ * (B y₀ y₁ - g₀ * Δ₀ y₀ * Δ₁ y₁)|
        ≤ ∑ y₀, ∑ y₁, |h₀ y₀| * |h₁ y₁| * (ε * β₀ * β₁) :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y₀ _ ↦
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y₁ _ ↦ hterm y₀ y₁))
      _ = (∑ y₀, |h₀ y₀|) * (∑ y₁, |h₁ y₁|) * (ε * β₀ * β₁) := by
          rw [Finset.sum_mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun y₀ _ ↦ ?_
          rw [Finset.sum_mul]
      _ ≤ 2 * 2 * (ε * β₀ * β₁) := by
          have hεβ : 0 ≤ ε * β₀ * β₁ := mul_nonneg (mul_nonneg hε hβ₀0) hβ₁0
          refine mul_le_mul_of_nonneg_right ?_ hεβ
          exact mul_le_mul hs₀ hs₁ (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (by norm_num)
      _ = 4 * ε * β₀ * β₁ := by ring
  have hdecomp : ∑ y₀, ∑ y₁, h₀ y₀ * h₁ y₁ * B y₀ y₁ =
      ∑ y₀, ∑ y₁, h₀ y₀ * h₁ y₁ * (g₀ * Δ₀ y₀ * Δ₁ y₁) +
        ∑ y₀, ∑ y₁, h₀ y₀ * h₁ y₁ * (B y₀ y₁ - g₀ * Δ₀ y₀ * Δ₁ y₁) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y₀ _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y₁ _ ↦ ?_
    ring
  change _ ≤ |∑ y₀, ∑ y₁, h₀ y₀ * h₁ y₁ * B y₀ y₁|
  rw [hdecomp, hmain]
  have hmainabs : |g₀ * (((b : ℝ) - 1) / (2 * (b : ℝ) ^ (κ 0 + 1))) *
      (((b : ℝ) - 1) / (2 * (b : ℝ) ^ (κ 1 + 1)))| =
      |g₀| * ((b : ℝ) - 1) ^ 2 / (4 * (b : ℝ) ^ (κ 0 + 1) * (b : ℝ) ^ (κ 1 + 1)) := by
    have hb1 : (0 : ℝ) ≤ (b : ℝ) - 1 := by
      have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
      linarith
    rw [abs_mul, abs_mul, abs_of_nonneg (div_nonneg hb1 (by positivity)),
      abs_of_nonneg (div_nonneg hb1 (by positivity))]
    ring
  have := abs_add_le (g₀ * (((b : ℝ) - 1) / (2 * (b : ℝ) ^ (κ 0 + 1))) *
      (((b : ℝ) - 1) / (2 * (b : ℝ) ^ (κ 1 + 1))) +
      ∑ y₀, ∑ y₁, h₀ y₀ * h₁ y₁ * (B y₀ y₁ - g₀ * Δ₀ y₀ * Δ₁ y₁))
    (-∑ y₀, ∑ y₁, h₀ y₀ * h₁ y₁ * (B y₀ y₁ - g₀ * Δ₀ y₀ * Δ₁ y₁))
  rw [add_neg_cancel_right, abs_neg, hmainabs] at this
  linarith

/-- A prefix class has `b^{D-k}` strings. -/
theorem card_prefixVal_eq (hb : 0 < b) {k : ℕ} (hk : k ≤ D) {a : ℕ} (ha : a < b ^ k) :
    (Finset.univ.filter fun x : Fin D → Fin b ↦ prefixVal x k = a).card = b ^ (D - k) := by
  obtain ⟨x₀, hx₀⟩ := exists_prefixVal_eq hb hk ha
  have h := card_agree hb k x₀
  rw [min_eq_left hk] at h
  rw [← h]
  congr 1
  refine Finset.filter_congr fun x _ ↦ ?_
  rw [← hx₀, eq_comm, prefixVal_eq_iff_agree hb hk]

/-- In a prefix class of level `k`, each value of a later digit `κ ≥ k` is taken by
`b^{D-k-1}` strings. -/
theorem card_prefixVal_digit_eq (hb : 0 < b) {k κ : ℕ} (hkκ : k ≤ κ) (hκ : κ < D) {a : ℕ}
    (ha : a < b ^ k) (c : Fin b) :
    (Finset.univ.filter fun x : Fin D → Fin b ↦ prefixVal x k = a ∧ x ⟨κ, hκ⟩ = c).card =
      b ^ (D - k - 1) := by
  set i : Fin D := ⟨κ, hκ⟩
  have hpre : ∀ (x : Fin D → Fin b) (v : Fin b), prefixVal (Function.update x i v) k =
      prefixVal x k := by
    intro x v
    rw [prefixVal_eq_iff_agree hb (le_trans hkκ hκ.le)]
    intro l hl
    have hne : l ≠ i := fun h ↦ by
      rw [h] at hl
      exact absurd hl (not_lt.2 hkκ)
    rw [Function.update_of_ne hne]
  have hle : ∀ c c' : Fin b,
      (Finset.univ.filter fun x : Fin D → Fin b ↦ prefixVal x k = a ∧ x i = c).card ≤
        (Finset.univ.filter fun x : Fin D → Fin b ↦ prefixVal x k = a ∧ x i = c').card := by
    intro c c'
    refine Finset.card_le_card_of_injOn (fun x ↦ Function.update x i c') ?_ ?_
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_filter] at hx ⊢
      exact ⟨Finset.mem_univ _, by rw [hpre]; exact hx.2.1, Function.update_self _ _ _⟩
    · intro x hx x' hx' h
      rw [Finset.mem_coe, Finset.mem_filter] at hx hx'
      funext l
      by_cases hl : l = i
      · rw [hl, hx.2.2, hx'.2.2]
      · have := congrFun h l
        simp only [Function.update_of_ne hl] at this
        exact this
  have heq : ∀ c' : Fin b,
      (Finset.univ.filter fun x : Fin D → Fin b ↦ prefixVal x k = a ∧ x i = c').card =
      (Finset.univ.filter fun x : Fin D → Fin b ↦ prefixVal x k = a ∧ x i = c).card :=
    fun c' ↦ le_antisymm (hle c' c) (hle c c')
  have htot := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter fun x : Fin D → Fin b ↦ prefixVal x k = a) (t := Finset.univ)
    (f := fun x ↦ x i) (fun _ _ ↦ Finset.mem_coe.2 (Finset.mem_univ _))
  rw [card_prefixVal_eq hb (le_trans hkκ hκ.le) ha] at htot
  have hfil : ∀ c' : Fin b, ((Finset.univ.filter fun x : Fin D → Fin b ↦ prefixVal x k = a).filter
      fun x ↦ x i = c') =
      Finset.univ.filter fun x : Fin D → Fin b ↦ prefixVal x k = a ∧ x i = c' := fun c' ↦ by
    rw [Finset.filter_filter]
  simp only [hfil, heq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at htot
  have hpow : b ^ (D - k) = b * b ^ (D - k - 1) := by
    rw [← pow_succ', show D - k - 1 + 1 = D - k by omega]
  rw [hpow] at htot
  exact (Nat.eq_of_mul_eq_mul_left hb htot).symm

/-- **Lower bound on a two-dimensional variance component** at a component of levels
`(κ₀ + 1, κ₁ + 1)` with `k ≤ κ_j < D`, under the local mixed-derivative condition with
`ε = |g₀| (b-1)²/(32 b²)`: `σ²_ℓ ≥ b^{-2k-2} (|g₀| (b-1)²/(8 b^{κ₀+κ₁+2}))²`. -/
theorem haarVar_cellAvg_ge (hb : 1 < b) {f : (Fin 2 → ℝ) → ℝ}
    (hf : MemLp f 2 (uniformCube 2)) {xc : Fin 2 → ℝ} (hxc : ∀ j, xc j ∈ Set.Ico (0 : ℝ) 1)
    {g₀ δ : ℝ}
    (hg : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      (∀ j, |x j - xc j| < δ) → (∀ j, |x' j - xc j| < δ) →
      |mixDiff f x x' - g₀ * (x 0 - x' 0) * (x 1 - x' 1)| ≤
        |g₀| * ((b : ℝ) - 1) ^ 2 / (32 * (b : ℝ) ^ 2) * |x 0 - x' 0| * |x 1 - x' 1|)
    {k : ℕ} (hk : ((b : ℝ) ^ k)⁻¹ ≤ δ) {ℓ : Fin 2 → Fin (D + 1)} {κ : Fin 2 → ℕ}
    (hℓ : ∀ j, (ℓ j : ℕ) = κ j + 1) (hκk : ∀ j, k ≤ κ j) (hκD : ∀ j, κ j < D) :
    ((b : ℝ) ^ (2 * k + 2))⁻¹ *
      (|g₀| * ((b : ℝ) - 1) ^ 2 / (8 * (b : ℝ) ^ (κ 0 + κ 1 + 2))) ^ 2 ≤
      haarVar (cellAvg (b := b) f) ℓ := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb0
  have hbD : (0 : ℝ) < ((b : ℝ) ^ D) ^ 2 := pow_pos (pow_pos hb' D) 2
  have hkD : k ≤ D := le_trans (hκk 0) (hκD 0).le
  set L := |g₀| * ((b : ℝ) - 1) ^ 2 / (8 * (b : ℝ) ^ (κ 0 + κ 1 + 2)) with hL
  have hL0 : 0 ≤ L := by positivity
  set a : Fin 2 → ℕ := fun j ↦ ⌊(b : ℝ) ^ k * xc j⌋₊ with ha
  have halt : ∀ j, a j < b ^ k := by
    intro j
    have h0 : 0 ≤ (b : ℝ) ^ k * xc j := mul_nonneg (pow_pos hb' k).le (hxc j).1
    have h1 : (b : ℝ) ^ k * xc j < (b : ℝ) ^ k := by
      have := (hxc j).2
      nlinarith [pow_pos hb' k]
    have := Nat.floor_lt h0 |>.2 (by exact_mod_cast h1 : (b : ℝ) ^ k * xc j < ((b ^ k : ℕ) : ℝ))
    exact this
  set good := Finset.univ.filter fun z : Fin 2 → Fin D → Fin b ↦
    ∀ j, prefixVal (z j) k = a j ∧ z j ⟨κ j, hκD j⟩ = ⟨0, hb0⟩ with hgood
  have hproj : ∀ z ∈ good, L ≤ |haarProj ℓ (cellAvg f) z| := by
    intro z hz
    rw [hgood, Finset.mem_filter] at hz
    have hε : 0 ≤ |g₀| * ((b : ℝ) - 1) ^ 2 / (32 * (b : ℝ) ^ 2) := by positivity
    have h := abs_haarProj_cellAvg_ge hb hf hxc hε hg hk hℓ hκk hκD
      (z := z) (fun j ↦ (hz.2 j).1) (fun j ↦ by rw [(hz.2 j).2])
    refine le_trans (le_of_eq ?_) h
    rw [hL]
    field_simp
    ring
  have hcard : (good.card : ℝ) = ((b ^ (D - k - 1) : ℕ) : ℝ) ^ 2 := by
    have hset : good = Fintype.piFinset fun j ↦ Finset.univ.filter fun x : Fin D → Fin b ↦
        prefixVal x k = a j ∧ x ⟨κ j, hκD j⟩ = ⟨0, hb0⟩ := by
      ext z
      simp only [hgood, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    rw [hset, Fintype.card_piFinset, Fin.prod_univ_two,
      card_prefixVal_digit_eq hb0 (hκk 0) (hκD 0) (halt 0),
      card_prefixVal_digit_eq hb0 (hκk 1) (hκD 1) (halt 1)]
    push_cast
    ring
  rw [haarVar_eq_sum_sq hb0, le_div_iff₀ hbD]
  calc ((b : ℝ) ^ (2 * k + 2))⁻¹ * L ^ 2 * ((b : ℝ) ^ D) ^ 2
      = (good.card : ℝ) * L ^ 2 := by
        rw [hcard]
        have hpow : ((b : ℝ) ^ D) ^ 2 =
            ((b : ℝ) ^ (2 * k + 2)) * (((b ^ (D - k - 1) : ℕ) : ℝ)) ^ 2 := by
          push_cast
          rw [← pow_mul, ← pow_mul, ← pow_add]
          congr 1
          have := hκk 0
          have := hκD 0
          omega
        rw [hpow]
        field_simp
    _ = ∑ _z ∈ good, L ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ z ∈ good, haarProj ℓ (cellAvg f) z ^ 2 := by
        refine Finset.sum_le_sum fun z hz ↦ ?_
        rw [← sq_abs (haarProj ℓ (cellAvg f) z)]
        exact pow_le_pow_left₀ hL0 (hproj z hz) 2
    _ ≤ ∑ z, haarProj ℓ (cellAvg f) z ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ ↦ sq_nonneg _

/-- `G(2, 1) = b/(b-1)`: the gain of a two-dimensional component one level above exactness. -/
theorem gainSeq_two_one (hb : 1 < b) : gainSeq b 2 1 = (b : ℝ) / ((b : ℝ) - 1) := by
  change -1 / ((b : ℝ) - 1) * gainSeq b 1 (0 + 1) + (b : ℝ) / ((b : ℝ) - 1) * gainSeq b 1 0 = _
  rw [gainSeq_eq_zero hb le_rfl le_rfl, gainSeq_zero_right]
  ring

/-- The two-dimensional Haar level vector `(κ₀ + 1, m - κ₀)` (total resolution `m - 1`). -/
def lvec2 (m κ₀ : ℕ) : Fin 2 → Fin (m + 1) :=
  ![⟨min (κ₀ + 1) m, Nat.lt_succ_of_le (min_le_right _ _)⟩,
    ⟨min (m - κ₀) m, Nat.lt_succ_of_le (min_le_right _ _)⟩]

/-- The levels of `lvec2`. -/
theorem lvec2_val {m κ₀ : ℕ} (h : κ₀ < m) :
    ((lvec2 m κ₀ 0 : ℕ) = κ₀ + 1) ∧ ((lvec2 m κ₀ 1 : ℕ) = (m - 1 - κ₀) + 1) := by
  constructor
  · change min (κ₀ + 1) m = κ₀ + 1
    omega
  · change min (m - κ₀) m = (m - 1 - κ₀) + 1
    omega

/-- The gain of the component `lvec2 m κ₀` of a `(0,m,2)`-net is `b/(b-1)`. -/
theorem gainCoeff_lvec2 (hb : 1 < b) {m : ℕ} {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b}
    (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) {κ₀ : ℕ} (h : κ₀ < m) :
    gainCoeff b d (lvec2 m κ₀) = (b : ℝ) / ((b : ℝ) - 1) := by
  obtain ⟨h0, h1⟩ := lvec2_val h
  rw [gainCoeff_net hb le_rfl hnet]
  have hfil : (Finset.univ.filter fun j ↦ ((lvec2 m κ₀ j : Fin (m + 1)) : ℕ) ≠ 0) =
      Finset.univ := by
    refine Finset.filter_true_of_mem fun j _ ↦ ?_
    fin_cases j
    · change ((lvec2 m κ₀ 0 : Fin (m + 1)) : ℕ) ≠ 0
      omega
    · change ((lvec2 m κ₀ 1 : Fin (m + 1)) : ℕ) ≠ 0
      omega
  rw [hfil, Finset.card_univ, Fintype.card_fin, Fin.sum_univ_two, h0, h1,
    show m - (κ₀ + 1 + (m - 1 - κ₀ + 1) - 2) = 1 by omega]
  exact gainSeq_two_one hb

/-- **Owen's variance lower bound for smooth integrands, `s = 2`** (Owen 1997b): for a
scrambled `(0,m,2)`-net in base `b` with `m` digits and an integrand whose mixed differences near
a point `xc` of the cube are `g₀ Δx₀ Δx₁` up to `ε |Δx₀| |Δx₁|`, `ε = |g₀|(b-1)²/(32 b²)`, on a
neighbourhood of radius `δ ≥ b^{-k}`,
`b^{3m} Var(μ̂) ≥ (m - 2k) g₀² (b-1)⁴ / (64 b^{2k+4})`. In particular, if `g₀ ≠ 0` then
`Var(μ̂) ≥ c n^{-3} log n` for large `n`. -/
theorem pow_mul_variance_scrambledLaw_two_ge (hb : 1 < b) {m : ℕ}
    {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    {f : (Fin 2 → ℝ) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (uniformCube 2))
    {xc : Fin 2 → ℝ} (hxc : ∀ j, xc j ∈ Set.Ico (0 : ℝ) 1) {g₀ δ : ℝ}
    (hg : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      (∀ j, |x j - xc j| < δ) → (∀ j, |x' j - xc j| < δ) →
      |mixDiff f x x' - g₀ * (x 0 - x' 0) * (x 1 - x' 1)| ≤
        |g₀| * ((b : ℝ) - 1) ^ 2 / (32 * (b : ℝ) ^ 2) * |x 0 - x' 0| * |x 1 - x' 1|)
    {k : ℕ} (hk : ((b : ℝ) ^ k)⁻¹ ≤ δ) (hkm : 2 * k + 1 ≤ m) :
    ((m : ℝ) - 2 * k) * (g₀ ^ 2 * ((b : ℝ) - 1) ^ 4 / (64 * (b : ℝ) ^ (2 * k + 4))) ≤
      (b : ℝ) ^ (3 * m) * Var[fun x ↦ x; scrambledLaw f d] := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb0
  have hn : b ^ m ≠ 0 := (Nat.pow_pos hb0).ne'
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  set C : ℝ := ((b : ℝ) ^ (2 * k + 2))⁻¹ *
    (|g₀| * ((b : ℝ) - 1) ^ 2 / (8 * (b : ℝ) ^ (m - 1 + 2))) ^ 2 with hC
  have hC0 : 0 ≤ C := by positivity
  set I := Finset.Icc k (m - 1 - k) with hI
  have hIm : ∀ κ₀ ∈ I, κ₀ < m := fun κ₀ h ↦ by
    rw [hI, Finset.mem_Icc] at h
    omega
  have hterm : ∀ κ₀ ∈ I, C ≤ gainCoeff b d (lvec2 m κ₀) * haarVar (cellAvg (b := b) f)
      (lvec2 m κ₀) := by
    intro κ₀ hκ₀
    have hκm := hIm κ₀ hκ₀
    rw [hI, Finset.mem_Icc] at hκ₀
    obtain ⟨h0, h1⟩ := lvec2_val hκm
    have hk0 : k ≤ κ₀ := hκ₀.1
    have hk1 : k ≤ m - 1 - κ₀ := by omega
    have hm0 : κ₀ < m := hκm
    have hm1 : m - 1 - κ₀ < m := by omega
    have hσ := haarVar_cellAvg_ge hb hf hxc hg hk (κ := ![κ₀, m - 1 - κ₀])
      (ℓ := lvec2 m κ₀) (Fin.forall_fin_two.2 ⟨h0, h1⟩) (Fin.forall_fin_two.2 ⟨hk0, hk1⟩)
      (Fin.forall_fin_two.2 ⟨hm0, hm1⟩)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      show κ₀ + (m - 1 - κ₀) = m - 1 by omega] at hσ
    rw [gainCoeff_lvec2 hb hnet hκm]
    have ha : (1 : ℝ) ≤ (b : ℝ) / ((b : ℝ) - 1) := by
      rw [one_le_div hb1]
      linarith
    calc C ≤ haarVar (cellAvg (b := b) f) (lvec2 m κ₀) := hσ
      _ ≤ (b : ℝ) / ((b : ℝ) - 1) * haarVar (cellAvg (b := b) f) (lvec2 m κ₀) :=
          le_mul_of_one_le_left (haarVar_nonneg hb0 _ _) ha
  have hinj : Set.InjOn (lvec2 m) I := by
    intro κ₀ h κ₀' h' he
    have := congrArg (fun ℓ ↦ ((ℓ 0 : Fin (m + 1)) : ℕ)) he
    rw [(lvec2_val (hIm κ₀ h)).1, (lvec2_val (hIm κ₀' h')).1] at this
    omega
  have hsub : I.image (lvec2 m) ⊆ (Finset.univ : Finset (Fin 2 → Fin (m + 1))).erase 0 := by
    intro ℓ hℓ
    rw [Finset.mem_image] at hℓ
    obtain ⟨κ₀, hκ₀, rfl⟩ := hℓ
    refine Finset.mem_erase.2 ⟨fun h0 ↦ ?_, Finset.mem_univ _⟩
    have := congrArg (fun ℓ ↦ ((ℓ 0 : Fin (m + 1)) : ℕ)) h0
    simp only [Pi.zero_apply, Fin.val_zero] at this
    rw [(lvec2_val (hIm κ₀ hκ₀)).1] at this
    omega
  have hsum : (I.card : ℝ) * C ≤ ∑ ℓ ∈ (Finset.univ : Finset (Fin 2 → Fin (m + 1))).erase 0,
      gainCoeff b d ℓ * haarVar (cellAvg (b := b) f) ℓ := by
    calc (I.card : ℝ) * C = ∑ _κ₀ ∈ I, C := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ κ₀ ∈ I, gainCoeff b d (lvec2 m κ₀) * haarVar (cellAvg (b := b) f) (lvec2 m κ₀) :=
          Finset.sum_le_sum hterm
      _ = ∑ ℓ ∈ I.image (lvec2 m), gainCoeff b d ℓ * haarVar (cellAvg (b := b) f) ℓ :=
          (Finset.sum_image (f := fun ℓ ↦ gainCoeff b d ℓ *
            haarVar (cellAvg (b := b) f) ℓ) hinj).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun ℓ hℓ _ ↦
          mul_nonneg (gainCoeff_net_mem_Icc hb le_rfl hnet (by omega)
            (Finset.ne_of_mem_erase hℓ)).1 (haarVar_nonneg hb0 _ _)
  have hcardI : (I.card : ℝ) = (m : ℝ) - 2 * k := by
    rw [hI, Nat.card_Icc]
    rw [show m - 1 - k + 1 - k = m - 2 * k by omega, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hcardI] at hsum
  have hres := cellResVar_nonneg hb0 hf (D := m) (b := b)
  rw [variance_scrambledLaw hb hn hfm hf d]
  have hpow3 : (b : ℝ) ^ (3 * m) * ((b ^ m : ℕ) : ℝ)⁻¹ = (b : ℝ) ^ (2 * m) := by
    push_cast
    rw [show 3 * m = 2 * m + m by ring, pow_add]
    field_simp
  calc ((m : ℝ) - 2 * k) * (g₀ ^ 2 * ((b : ℝ) - 1) ^ 4 / (64 * (b : ℝ) ^ (2 * k + 4)))
      = (b : ℝ) ^ (2 * m) * (((m : ℝ) - 2 * k) * C) := by
        rw [hC]
        have hm1 : m - 1 + 2 = m + 1 := by omega
        rw [hm1]
        field_simp
        rw [sq_abs]
        ring
    _ ≤ (b : ℝ) ^ (2 * m) * (cellResVar b m f + ∑ ℓ ∈ (Finset.univ : Finset
        (Fin 2 → Fin (m + 1))).erase 0, gainCoeff b d ℓ * haarVar (cellAvg (b := b) f) ℓ) :=
        mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hb'.le _)
    _ = _ := by
        rw [← hpow3]
        ring

/-- **The within-cell variance of a Lipschitz integrand**: if
`|f x - f x'| ≤ L Σ_j |x_j - x'_j|` on the cube, then `σ²_{>D} ≤ (L s b^{-D})²`. -/
theorem cellResVar_le (hb : 0 < b) {s : ℕ} {f : (Fin s → ℝ) → ℝ}
    (hf : MemLp f 2 (uniformCube s)) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x x' : Fin s → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      |f x - f x'| ≤ L * ∑ j, |x j - x' j|) :
    cellResVar b D f ≤ (L * s * ((b : ℝ) ^ D)⁻¹) ^ 2 := by
  have hU := isProbabilityMeasure_uniformCube s
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have hbD : (0 : ℝ) < ((b : ℝ) ^ D) ^ s := pow_pos (pow_pos hb' D) s
  have hcell : ∀ y : Fin s → Fin D → Fin b,
      cellSq f y - cellAvg f y ^ 2 ≤ (L * s * ((b : ℝ) ^ D)⁻¹) ^ 2 := by
    intro y
    have hXL := memLp_comp_cellPoint hb hf y
    have hv := variance_eq_sub hXL
    have e : cellSq f y - cellAvg f y ^ 2 = Var[fun u ↦ f (cellPoint y u); uniformCube s] := by
      rw [hv]
      rfl
    rw [e, ← variance_sub_const hXL.aestronglyMeasurable (f (cellPoint y 0))]
    refine (variance_le_expectation_sq
      (hXL.aestronglyMeasurable.sub aestronglyMeasurable_const)).trans ?_
    have hbound : ∀ᵐ u ∂(uniformCube s), ((fun u ↦ f (cellPoint y u) - f (cellPoint y 0)) ^ 2) u ≤
        (L * s * ((b : ℝ) ^ D)⁻¹) ^ 2 := by
      filter_upwards [ae_mem_cube_uniformCube s] with u hu
      have h0 : ∀ _j : Fin s, (0 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := fun _ ↦ ⟨le_rfl, one_pos⟩
      have hl := hL (cellPoint y u) (cellPoint y 0) (fun j ↦ digitPoint_mem_Ico hb _ (hu j))
        (fun j ↦ digitPoint_mem_Ico hb _ (h0 j))
      have hcoord : ∀ j, |cellPoint y u j - cellPoint y 0 j| ≤ ((b : ℝ) ^ D)⁻¹ := by
        intro j
        change |digitPoint (y j) (u j) - digitPoint (y j) 0| ≤ _
        unfold digitPoint
        rw [show ((cellVal (y j) : ℝ) + u j) / (b : ℝ) ^ D - ((cellVal (y j) : ℝ) + 0) /
          (b : ℝ) ^ D = u j / (b : ℝ) ^ D by ring, abs_div, abs_of_nonneg (hu j).1,
          abs_of_pos (pow_pos hb' D), div_eq_mul_inv]
        exact mul_le_of_le_one_left (inv_nonneg.2 (pow_pos hb' D).le) (hu j).2.le
      have hsum : ∑ j, |cellPoint y u j - cellPoint y 0 j| ≤ s * ((b : ℝ) ^ D)⁻¹ := by
        calc ∑ j, |cellPoint y u j - cellPoint y 0 j| ≤ ∑ _j : Fin s, ((b : ℝ) ^ D)⁻¹ :=
              Finset.sum_le_sum fun j _ ↦ hcoord j
          _ = s * ((b : ℝ) ^ D)⁻¹ := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have habs : |f (cellPoint y u) - f (cellPoint y 0)| ≤ L * s * ((b : ℝ) ^ D)⁻¹ := by
        rw [mul_assoc]
        exact hl.trans (mul_le_mul_of_nonneg_left hsum hL0)
      change (f (cellPoint y u) - f (cellPoint y 0)) ^ 2 ≤ _
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    calc ∫ u, ((fun u ↦ f (cellPoint y u) - f (cellPoint y 0)) ^ 2) u ∂(uniformCube s)
        ≤ ∫ _u, (L * s * ((b : ℝ) ^ D)⁻¹) ^ 2 ∂(uniformCube s) :=
          integral_mono_ae ((hXL.sub (memLp_const _)).integrable_sq) (integrable_const _) hbound
      _ = (L * s * ((b : ℝ) ^ D)⁻¹) ^ 2 := by rw [integral_const, probReal_univ, one_smul]
  unfold cellResVar
  rw [div_le_iff₀ hbD]
  calc ∑ y : Fin s → Fin D → Fin b, (cellSq f y - cellAvg f y ^ 2)
      ≤ ∑ _y : Fin s → Fin D → Fin b, (L * s * ((b : ℝ) ^ D)⁻¹) ^ 2 :=
        Finset.sum_le_sum fun y _ ↦ hcell y
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [Fintype.card_fun, Fintype.card_fin]
        push_cast
        ring

/-- A truncated geometric tail: for `0 ≤ x ≤ 1/2`, `Σ_{t ≤ j < N} x^j ≤ 2 x^t`. -/
theorem sum_range_ite_pow_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (t : ℕ) :
    ∀ N : ℕ, ∑ j ∈ Finset.range N, (if t ≤ j then x ^ j else 0) ≤ 2 * x ^ t - 2 * x ^ max N t := by
  intro N
  induction N with
  | zero =>
    rw [Finset.sum_range_zero, Nat.zero_max]
    ring_nf
    exact le_rfl
  | succ N ih =>
    rw [Finset.sum_range_succ]
    by_cases hN : t ≤ N
    · rw [ite_eq_left hN, max_eq_left (by omega)]
      rw [max_eq_left hN] at ih
      have h1 : x ^ (N + 1) ≤ x ^ N / 2 := by
        rw [pow_succ]
        nlinarith [pow_nonneg hx0 N]
      linarith
    · rw [ite_eq_right hN, add_zero, max_eq_right (by omega)]
      rw [max_eq_right (by omega)] at ih
      exact ih

/-- **Owen's variance upper bound for smooth integrands, `s = 2`** (Owen 1997b): for a scrambled
`(0,m,2)`-net in base `b` with `m` digits and an integrand that is `L`-Lipschitz on the cube
(`|f x - f x'| ≤ L (|Δx₀| + |Δx₁|)`) with mixed differences bounded by `M |Δx₀| |Δx₁|`,
`b^{3m} Var(μ̂) ≤ 4 L² + 64 M² b² (m + 1)`, i.e. `Var(μ̂) = O(n^{-3} log n)`. -/
theorem pow_mul_variance_scrambledLaw_two_le (hb : 1 < b) {m : ℕ}
    {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    {f : (Fin 2 → ℝ) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (uniformCube 2)) {M L : ℝ}
    (hM0 : 0 ≤ M)
    (hM : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      |mixDiff f x x'| ≤ M * |x 0 - x' 0| * |x 1 - x' 1|)
    (hL0 : 0 ≤ L)
    (hL : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      |f x - f x'| ≤ L * ∑ j, |x j - x' j|) :
    (b : ℝ) ^ (3 * m) * Var[fun x ↦ x; scrambledLaw f d] ≤
      4 * L ^ 2 + 64 * M ^ 2 * (b : ℝ) ^ 2 * (m + 1) := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb0
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hn : b ^ m ≠ 0 := (Nat.pow_pos hb0).ne'
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by linarith
  set a : ℝ := (b : ℝ) / ((b : ℝ) - 1) with ha
  have ha2 : a ≤ 2 := by
    rw [ha, div_le_iff₀ hb1]
    linarith
  have ha0 : 0 ≤ a := div_nonneg hb'.le hb1.le
  set x : ℝ := ((b : ℝ) ^ 2)⁻¹ with hx
  have hx0 : 0 ≤ x := inv_nonneg.2 (pow_nonneg hb'.le 2)
  have hx2 : x ≤ 1 / 2 := by
    rw [hx, inv_le_comm₀ (pow_pos hb' 2) (by norm_num)]
    nlinarith
  set T : (Fin 2 → Fin (m + 1)) → ℝ := fun ℓ ↦
    if m + 1 ≤ (ℓ 0 : ℕ) + ℓ 1 then a * (16 * M ^ 2 * (b : ℝ) ^ 4) * x ^ ((ℓ 0 : ℕ) + ℓ 1)
      else 0 with hT
  have hT0 : ∀ ℓ, 0 ≤ T ℓ := fun ℓ ↦ by
    simp only [hT]
    split_ifs
    · positivity
    · exact le_rfl
  have hinv : ∀ k : ℕ, 1 ≤ k → ((b : ℝ) ^ (k - 1))⁻¹ = (b : ℝ) * ((b : ℝ) ^ k)⁻¹ := by
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    field_simp
  have hper : ∀ ℓ ∈ (Finset.univ : Finset (Fin 2 → Fin (m + 1))).erase 0,
      gainCoeff b d ℓ * haarVar (cellAvg (b := b) f) ℓ ≤ T ℓ := by
    intro ℓ hℓ
    have hne := Finset.ne_of_mem_erase hℓ
    have hl0 : (ℓ 0 : ℕ) ≤ m := Nat.lt_succ_iff.1 (ℓ 0).isLt
    have hl1 : (ℓ 1 : ℕ) ≤ m := Nat.lt_succ_iff.1 (ℓ 1).isLt
    by_cases h : m + 1 ≤ (ℓ 0 : ℕ) + ℓ 1
    · simp only [hT, h, ↓reduceIte]
      have hκ : ∀ j, (ℓ j : ℕ) = ((ℓ j : ℕ) - 1) + 1 := fun j ↦ by
        fin_cases j
        · change (ℓ 0 : ℕ) = (ℓ 0 : ℕ) - 1 + 1
          omega
        · change (ℓ 1 : ℕ) = (ℓ 1 : ℕ) - 1 + 1
          omega
      have hσ := haarVar_cellAvg_le hb0 hf hM0 hM (κ := fun j ↦ (ℓ j : ℕ) - 1) hκ
        (fun j ↦ by have := Nat.lt_succ_iff.1 (ℓ j).isLt; omega)
      have hΓ := gainCoeff_net_mem_Icc hb le_rfl hnet (by omega) hne
      rw [show 2 - 1 = 1 from rfl, pow_one] at hΓ
      have hσ' : haarVar (cellAvg (b := b) f) ℓ ≤ 16 * M ^ 2 * (b : ℝ) ^ 4 *
          x ^ ((ℓ 0 : ℕ) + ℓ 1) := by
        refine hσ.trans (le_of_eq ?_)
        have hxk : ∀ k : ℕ, ((b : ℝ) ^ 2)⁻¹ ^ k = (((b : ℝ) ^ k)⁻¹) ^ 2 := fun k ↦ by
          rw [inv_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm]
        rw [hinv _ (by omega), hinv _ (by omega), hx, pow_add, hxk, hxk]
        ring
      calc gainCoeff b d ℓ * haarVar (cellAvg (b := b) f) ℓ
          ≤ a * haarVar (cellAvg (b := b) f) ℓ :=
            mul_le_mul_of_nonneg_right hΓ.2 (haarVar_nonneg hb0 _ _)
        _ ≤ a * (16 * M ^ 2 * (b : ℝ) ^ 4 * x ^ ((ℓ 0 : ℕ) + ℓ 1)) :=
            mul_le_mul_of_nonneg_left hσ' ha0
        _ = _ := by ring
    · simp only [hT, h, ↓reduceIte]
      rw [gainCoeff_net_eq_zero hb le_rfl hnet hne (by rw [Fin.sum_univ_two]; omega), zero_mul]
  have hsumT : ∑ ℓ : Fin 2 → Fin (m + 1), T ℓ ≤
      a * (16 * M ^ 2 * (b : ℝ) ^ 4) * ((m + 1) * (2 * x ^ (m + 1))) := by
    rw [sum_fin_two_pi]
    have e : ∀ l₀ l₁ : Fin (m + 1), T ![l₀, l₁] = a * (16 * M ^ 2 * (b : ℝ) ^ 4) *
        (x ^ (l₀ : ℕ) * (if m + 1 - l₀ ≤ (l₁ : ℕ) then x ^ (l₁ : ℕ) else 0)) := by
      intro l₀ l₁
      simp only [hT, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      have hl0 : (l₀ : ℕ) ≤ m := Nat.lt_succ_iff.1 l₀.isLt
      by_cases h : m + 1 ≤ (l₀ : ℕ) + l₁
      · rw [ite_eq_left h, ite_eq_left (by omega), pow_add]
      · rw [ite_eq_right h, ite_eq_right (by omega), mul_zero, mul_zero]
    simp only [e, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ∑ l₀ : Fin (m + 1), x ^ (l₀ : ℕ) * ∑ l₁ : Fin (m + 1),
          (if m + 1 - l₀ ≤ (l₁ : ℕ) then x ^ (l₁ : ℕ) else 0)
        ≤ ∑ l₀ : Fin (m + 1), x ^ (l₀ : ℕ) * (2 * x ^ (m + 1 - l₀)) := by
          refine Finset.sum_le_sum fun l₀ _ ↦ mul_le_mul_of_nonneg_left ?_ (pow_nonneg hx0 _)
          rw [Fin.sum_univ_eq_sum_range (fun l₁ ↦ if m + 1 - l₀ ≤ l₁ then x ^ l₁ else 0)]
          have := sum_range_ite_pow_le hx0 hx2 (m + 1 - l₀) (m + 1)
          have hmax : 0 ≤ 2 * x ^ max (m + 1) (m + 1 - (l₀ : ℕ)) := by positivity
          linarith
      _ = ∑ _l₀ : Fin (m + 1), 2 * x ^ (m + 1) := by
          refine Finset.sum_congr rfl fun l₀ _ ↦ ?_
          have hl0 : (l₀ : ℕ) ≤ m := Nat.lt_succ_iff.1 l₀.isLt
          rw [← mul_assoc, mul_comm (x ^ (l₀ : ℕ)) 2, mul_assoc, ← pow_add,
            Nat.add_sub_cancel' (by omega)]
      _ = (m + 1) * (2 * x ^ (m + 1)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have hsum := (Finset.sum_le_sum hper).trans (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.erase_subset 0 Finset.univ) fun ℓ _ _ ↦ hT0 ℓ)
  have hres := cellResVar_le hb0 hf hL0 hL (D := m)
  rw [variance_scrambledLaw hb hn hfm hf d]
  have hpow3 : (b : ℝ) ^ (3 * m) * ((b ^ m : ℕ) : ℝ)⁻¹ = (b : ℝ) ^ (2 * m) := by
    push_cast
    rw [show 3 * m = 2 * m + m by ring, pow_add]
    field_simp
  have hxm : (b : ℝ) ^ (2 * m) * x ^ (m + 1) = ((b : ℝ) ^ 2)⁻¹ := by
    rw [hx, inv_pow, pow_mul, pow_succ]
    have : (0 : ℝ) < ((b : ℝ) ^ 2) ^ m := pow_pos (pow_pos hb' 2) m
    field_simp
    ring
  rw [← mul_assoc, hpow3]
  calc (b : ℝ) ^ (2 * m) * (cellResVar b m f + ∑ ℓ ∈ (Finset.univ : Finset
        (Fin 2 → Fin (m + 1))).erase 0, gainCoeff b d ℓ * haarVar (cellAvg (b := b) f) ℓ)
      ≤ (b : ℝ) ^ (2 * m) * ((L * ((2 : ℕ) : ℝ) * ((b : ℝ) ^ m)⁻¹) ^ 2 +
          a * (16 * M ^ 2 * (b : ℝ) ^ 4) * ((m + 1) * (2 * x ^ (m + 1)))) :=
        mul_le_mul_of_nonneg_left (add_le_add hres (hsum.trans hsumT)) (pow_nonneg hb'.le _)
    _ = 4 * L ^ 2 + a * (32 * M ^ 2 * (b : ℝ) ^ 2 * (m + 1)) := by
        have hbm : (b : ℝ) ^ (2 * m) * (((b : ℝ) ^ m)⁻¹) ^ 2 = 1 := by
          rw [inv_pow, ← pow_mul, mul_comm m 2]
          field_simp
        have e1 : (b : ℝ) ^ (2 * m) * ((L * ((2 : ℕ) : ℝ) * ((b : ℝ) ^ m)⁻¹) ^ 2 +
            a * (16 * M ^ 2 * (b : ℝ) ^ 4) * ((m + 1) * (2 * x ^ (m + 1)))) =
            4 * L ^ 2 * ((b : ℝ) ^ (2 * m) * (((b : ℝ) ^ m)⁻¹) ^ 2) +
              a * (32 * M ^ 2 * (b : ℝ) ^ 4 * (m + 1)) * ((b : ℝ) ^ (2 * m) * x ^ (m + 1)) := by
          push_cast
          ring
        rw [e1, hbm, hxm]
        field_simp
    _ ≤ 4 * L ^ 2 + 2 * (32 * M ^ 2 * (b : ℝ) ^ 2 * (m + 1)) := by
        have : 0 ≤ 32 * M ^ 2 * (b : ℝ) ^ 2 * (m + 1) := by positivity
        nlinarith
    _ = 4 * L ^ 2 + 64 * M ^ 2 * (b : ℝ) ^ 2 * (m + 1) := by ring

/-- **`Var ≍ n⁻³ log n` for smooth non-degenerate integrands, `s = 2`** (Owen 1997b): for
scrambled `(0,m,2)`-nets with `m` digits and an integrand that is Lipschitz, has bounded mixed
differences, and has a non-zero strict mixed derivative `g₀` at some point `xc` of the cube, there
are constants `0 < c` and `C` with `c m ≤ b^{3m} Var(μ̂) ≤ C (m + 1)` for all large `m`. -/
theorem variance_scrambledLaw_two_asymp (hb : 1 < b)
    (d : (m : ℕ) → Fin (b ^ m) → Fin 2 → Fin m → Fin b)
    (hnet : ∀ m, IsNet b 0 m fun i j ↦ digitPoint (d m i j) 0)
    {f : (Fin 2 → ℝ) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (uniformCube 2)) {M L : ℝ}
    (hM0 : 0 ≤ M)
    (hM : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      |mixDiff f x x'| ≤ M * |x 0 - x' 0| * |x 1 - x' 1|)
    (hL0 : 0 ≤ L)
    (hL : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      |f x - f x'| ≤ L * ∑ j, |x j - x' j|)
    {xc : Fin 2 → ℝ} (hxc : ∀ j, xc j ∈ Set.Ico (0 : ℝ) 1) {g₀ : ℝ} (hg₀ : g₀ ≠ 0)
    (hg : ∀ ε > 0, ∃ δ > 0, ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) →
      (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, |x j - xc j| < δ) → (∀ j, |x' j - xc j| < δ) →
      |mixDiff f x x' - g₀ * (x 0 - x' 0) * (x 1 - x' 1)| ≤ ε * |x 0 - x' 0| * |x 1 - x' 1|) :
    ∃ c > 0, ∃ C : ℝ, ∀ᶠ m in atTop,
      c * m ≤ (b : ℝ) ^ (3 * m) * Var[fun x ↦ x; scrambledLaw f (d m)] ∧
      (b : ℝ) ^ (3 * m) * Var[fun x ↦ x; scrambledLaw f (d m)] ≤ C * (m + 1) := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb0
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  obtain ⟨δ, hδ, hgδ⟩ := hg (|g₀| * ((b : ℝ) - 1) ^ 2 / (32 * (b : ℝ) ^ 2)) (by positivity)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ
    (show 1 / (b : ℝ) < 1 by rw [div_lt_one hb']; exact Nat.one_lt_cast.2 hb)
  have hk' : ((b : ℝ) ^ k)⁻¹ ≤ δ := by
    rw [one_div_pow, one_div] at hk
    exact hk.le
  set c₀ : ℝ := g₀ ^ 2 * ((b : ℝ) - 1) ^ 4 / (64 * (b : ℝ) ^ (2 * k + 4)) with hc₀
  have hc₀pos : 0 < c₀ := by
    have : 0 < g₀ ^ 2 := by positivity
    positivity
  refine ⟨c₀ / 2, by positivity, 4 * L ^ 2 + 64 * M ^ 2 * (b : ℝ) ^ 2, ?_⟩
  filter_upwards [eventually_ge_atTop (4 * k + 1)] with m hm
  constructor
  · have h := pow_mul_variance_scrambledLaw_two_ge hb (hnet m) hfm hf hxc hgδ hk' (by omega)
    have hmk : (m : ℝ) / 2 ≤ (m : ℝ) - 2 * k := by
      have : ((4 * k + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
      push_cast at this
      linarith
    calc c₀ / 2 * m = (m / 2) * c₀ := by ring
      _ ≤ ((m : ℝ) - 2 * k) * c₀ := mul_le_mul_of_nonneg_right hmk hc₀pos.le
      _ ≤ _ := h
  · have h := pow_mul_variance_scrambledLaw_two_le hb (hnet m) hfm hf hM0 hM hL0 hL
    have hm1 : (1 : ℝ) ≤ m + 1 := by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    calc (b : ℝ) ^ (3 * m) * Var[fun x ↦ x; scrambledLaw f (d m)]
        ≤ 4 * L ^ 2 + 64 * M ^ 2 * (b : ℝ) ^ 2 * (m + 1) := h
      _ ≤ 4 * L ^ 2 * (m + 1) + 64 * M ^ 2 * (b : ℝ) ^ 2 * (m + 1) := by
          have : 0 ≤ 4 * L ^ 2 := by positivity
          nlinarith
      _ = (4 * L ^ 2 + 64 * M ^ 2 * (b : ℝ) ^ 2) * (m + 1) := by ring

/-- The product integrand `f(x) = x₀ x₁`. -/
def prodFn (x : Fin 2 → ℝ) : ℝ := x 0 * x 1

/-- The mixed difference of `x₀ x₁` is exactly `Δx₀ Δx₁`. -/
theorem mixDiff_prodFn (x x' : Fin 2 → ℝ) :
    mixDiff prodFn x x' = (x 0 - x' 0) * (x 1 - x' 1) := by
  unfold mixDiff prodFn
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- **The scrambled-net variance of `x₀ x₁` is of exact order `n⁻³ log n`** (`s = 2`, any base
`b ≥ 2`, `(0,m,2)`-nets with `m` digits, e.g. the Hammersley net):
`m (b-1)⁴/(64 b⁴) ≤ b^{3m} Var(μ̂) ≤ 4 + 64 b² (m + 1)`. For additive integrands
`b^{3m} Var(μ̂)` converges instead (`tendsto_cube_mul_variance_scrambledLaw_addFn`): the extra
`log n` comes from the interaction, spread over the `m` resolution splits `κ₀ + κ₁ = m - 1`. -/
theorem variance_scrambledLaw_prodFn (hb : 1 < b) {m : ℕ} (hm : 1 ≤ m)
    {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) :
    (m : ℝ) * (((b : ℝ) - 1) ^ 4 / (64 * (b : ℝ) ^ 4)) ≤
      (b : ℝ) ^ (3 * m) * Var[fun x ↦ x; scrambledLaw prodFn d] ∧
    (b : ℝ) ^ (3 * m) * Var[fun x ↦ x; scrambledLaw prodFn d] ≤
      4 + 64 * (b : ℝ) ^ 2 * (m + 1) := by
  have hU := isProbabilityMeasure_uniformCube 2
  have hfm : Measurable prodFn :=
    (measurable_pi_apply 0).mul (measurable_pi_apply 1)
  have hf : MemLp prodFn 2 (uniformCube 2) := by
    refine MemLp.of_bound hfm.aestronglyMeasurable 1 ?_
    filter_upwards [ae_mem_cube_uniformCube 2] with x hx
    rw [Real.norm_eq_abs, prodFn, abs_mul]
    have h0 : |x 0| ≤ 1 := abs_le.2 ⟨by linarith [(hx 0).1], (hx 0).2.le⟩
    have h1 : |x 1| ≤ 1 := abs_le.2 ⟨by linarith [(hx 1).1], (hx 1).2.le⟩
    nlinarith [abs_nonneg (x 0), abs_nonneg (x 1)]
  have hxc : ∀ j, (0 : Fin 2 → ℝ) j ∈ Set.Ico (0 : ℝ) 1 := fun _ ↦ ⟨le_rfl, one_pos⟩
  constructor
  · have h := pow_mul_variance_scrambledLaw_two_ge hb hnet hfm hf hxc (g₀ := 1) (δ := 2)
      (fun x x' _ _ _ _ ↦ by
        rw [mixDiff_prodFn, one_mul, sub_self, abs_zero]
        positivity) (k := 0) (by norm_num) (by omega)
    simp only [Nat.cast_zero, mul_zero, sub_zero, one_pow, one_mul, zero_add] at h
    exact h
  · have h := pow_mul_variance_scrambledLaw_two_le hb hnet hfm hf (M := 1) (L := 1) zero_le_one
      (fun x x' _ _ ↦ by rw [mixDiff_prodFn, abs_mul, one_mul]) zero_le_one
      (fun x x' hx hx' ↦ by
        rw [prodFn, prodFn, Fin.sum_univ_two, one_mul]
        have e : x 0 * x 1 - x' 0 * x' 1 = x 0 * (x 1 - x' 1) + x' 1 * (x 0 - x' 0) := by ring
        rw [e]
        have h0 : |x 0| ≤ 1 := abs_le.2 ⟨by linarith [(hx 0).1], (hx 0).2.le⟩
        have h1 : |x' 1| ≤ 1 := abs_le.2 ⟨by linarith [(hx' 1).1], (hx' 1).2.le⟩
        calc |x 0 * (x 1 - x' 1) + x' 1 * (x 0 - x' 0)|
            ≤ |x 0| * |x 1 - x' 1| + |x' 1| * |x 0 - x' 0| := by
              rw [← abs_mul, ← abs_mul]
              exact abs_add_le _ _
          _ ≤ 1 * |x 1 - x' 1| + 1 * |x 0 - x' 0| := by
              gcongr
          _ = |x 0 - x' 0| + |x 1 - x' 1| := by ring)
    simpa only [one_pow, mul_one] using h

/-- **The average conditional variance given the scramble** is the within-cell part:
`E_ρ[Var(μ̂ | ρ)] = n⁻¹ σ²_{>D}`. (Given the scramble, the points are independent and the only
randomness is in the remainders.) -/
theorem avg_variance_scrambledEstimate (hb : 0 < b) {s n : ℕ} (hn : n ≠ 0)
    {f : (Fin s → ℝ) → ℝ} (hf : MemLp f 2 (uniformCube s)) (d : Fin n → Fin s → Fin D → Fin b) :
    (Fintype.card (Fin s → Scramble b D) : ℝ)⁻¹ *
      ∑ ρ, Var[scrambledEstimate f d ρ; remLaw s n] = (n : ℝ)⁻¹ * cellResVar b D f := by
  have hQ := isProbabilityMeasure_remLaw s n
  have hR : (0 : ℝ) < (Fintype.card (Scramble b D) : ℝ) ^ s :=
    pow_pos (Nat.cast_pos.2 Fintype.card_pos) s
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have hbD : (0 : ℝ) < ((b : ℝ) ^ D) ^ s := pow_pos (pow_pos hb' D) s
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hvar : ∀ ρ, Var[scrambledEstimate f d ρ; remLaw s n] = ((n : ℝ)⁻¹) ^ 2 *
      ∑ i, (cellSq f (scrambleVec ρ (d i)) - cellAvg f (scrambleVec ρ (d i)) ^ 2) := by
    intro ρ
    rw [variance_eq_sub (memLp_scrambledEstimate hb hf d ρ)]
    change ∫ u, scrambledEstimate f d ρ u ^ 2 ∂(remLaw s n) -
      (∫ u, scrambledEstimate f d ρ u ∂(remLaw s n)) ^ 2 = _
    rw [integral_sq_scrambledEstimate hb hf d ρ, integral_scrambledEstimate hb hf d ρ]
    ring
  simp only [hvar, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [sum_scrambleVec hb _ (fun y ↦ cellSq f y - cellAvg f y ^ 2)]
  rw [card_scramble_pi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold cellResVar
  field_simp

/-- **For smooth non-degenerate integrands in `s = 2`, the remainders carry a vanishing share of
the variance**: `E_ρ[Var(μ̂ | ρ)] / Var(μ̂) → 0`. By the law of total variance, almost all of the
variance is `Var(E[μ̂ | ρ])`, the fluctuation due to the nested scramble, under which the points
are dependent. A CLT therefore cannot come from the independent remainders (a Lindeberg argument
conditional on the scramble), unlike in the additive case: this is the part of Loh's theorem that
needs his dependent-sum argument. -/
theorem tendsto_avg_variance_given_scramble_div (hb : 1 < b)
    (d : (m : ℕ) → Fin (b ^ m) → Fin 2 → Fin m → Fin b)
    (hnet : ∀ m, IsNet b 0 m fun i j ↦ digitPoint (d m i j) 0)
    {f : (Fin 2 → ℝ) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (uniformCube 2)) {M L : ℝ}
    (hM0 : 0 ≤ M)
    (hM : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      |mixDiff f x x'| ≤ M * |x 0 - x' 0| * |x 1 - x' 1|)
    (hL0 : 0 ≤ L)
    (hL : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      |f x - f x'| ≤ L * ∑ j, |x j - x' j|)
    {xc : Fin 2 → ℝ} (hxc : ∀ j, xc j ∈ Set.Ico (0 : ℝ) 1) {g₀ : ℝ} (hg₀ : g₀ ≠ 0)
    (hg : ∀ ε > 0, ∃ δ > 0, ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) →
      (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, |x j - xc j| < δ) → (∀ j, |x' j - xc j| < δ) →
      |mixDiff f x x' - g₀ * (x 0 - x' 0) * (x 1 - x' 1)| ≤ ε * |x 0 - x' 0| * |x 1 - x' 1|) :
    Tendsto (fun m ↦ ((Fintype.card (Fin 2 → Scramble b m) : ℝ)⁻¹ *
      ∑ ρ, Var[scrambledEstimate f (d m) ρ; remLaw 2 (b ^ m)]) /
        Var[fun x ↦ x; scrambledLaw f (d m)]) atTop (𝓝 0) := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb0
  obtain ⟨c, hc, C, hev⟩ := variance_scrambledLaw_two_asymp hb d hnet hfm hf hM0 hM hL0 hL hxc
    hg₀ hg
  have hlim : Tendsto (fun m : ℕ ↦ (4 * L ^ 2 / c) / (m : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards with m
    refine div_nonneg (mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun ρ _ ↦ variance_nonneg _ _)) (variance_nonneg _ _)
  · filter_upwards [hev, eventually_ge_atTop 1] with m hm hm1
    have hn : b ^ m ≠ 0 := (Nat.pow_pos hb0).ne'
    rw [avg_variance_scrambledEstimate hb0 hn hf (d m)]
    have hres := cellResVar_le hb0 hf hL0 hL (D := m)
    have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 hm1
    have hV : c * m / (b : ℝ) ^ (3 * m) ≤ Var[fun x ↦ x; scrambledLaw f (d m)] := by
      rw [div_le_iff₀ (pow_pos hb' _), mul_comm _ ((b : ℝ) ^ (3 * m))]
      exact hm.1
    have hVpos : 0 < Var[fun x ↦ x; scrambledLaw f (d m)] :=
      lt_of_lt_of_le (by positivity) hV
    rw [div_le_div_iff₀ hVpos hmpos]
    have hnum : ((b ^ m : ℕ) : ℝ)⁻¹ * cellResVar b m f ≤
        ((b ^ m : ℕ) : ℝ)⁻¹ * (L * ((2 : ℕ) : ℝ) * ((b : ℝ) ^ m)⁻¹) ^ 2 :=
      mul_le_mul_of_nonneg_left hres (inv_nonneg.2 (Nat.cast_nonneg _))
    have e : ((b ^ m : ℕ) : ℝ)⁻¹ * (L * ((2 : ℕ) : ℝ) * ((b : ℝ) ^ m)⁻¹) ^ 2 * (m : ℝ) =
        (4 * L ^ 2 / c) * (c * m / (b : ℝ) ^ (3 * m)) := by
      push_cast
      rw [show 3 * m = m + m + m by ring, pow_add, pow_add]
      field_simp
      ring
    calc ((b ^ m : ℕ) : ℝ)⁻¹ * cellResVar b m f * (m : ℝ)
        ≤ ((b ^ m : ℕ) : ℝ)⁻¹ * (L * ((2 : ℕ) : ℝ) * ((b : ℝ) ^ m)⁻¹) ^ 2 * (m : ℝ) :=
          mul_le_mul_of_nonneg_right hnum hmpos.le
      _ = (4 * L ^ 2 / c) * (c * m / (b : ℝ) ^ (3 * m)) := e
      _ ≤ 4 * L ^ 2 / c * Var[fun x ↦ x; scrambledLaw f (d m)] :=
          mul_le_mul_of_nonneg_left hV (by positivity)

/-- **A linear approximation from a derivative bound**: if `φ' t` stays within `η` of `c` on the
segment between `a` and `b`, then `|φ b - φ a - c (b - a)| ≤ η |b - a|`. -/
theorem abs_sub_sub_mul_le_of_deriv {φ φ' : ℝ → ℝ} {a b c η : ℝ}
    (hφ : ∀ t ∈ Set.uIcc a b, HasDerivAt φ (φ' t) t) (hη : ∀ t ∈ Set.uIcc a b, |φ' t - c| ≤ η) :
    |φ b - φ a - c * (b - a)| ≤ η * |b - a| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun t ↦ φ t - c * t)
    (f' := fun t ↦ φ' t - c) (s := Set.uIcc a b) (C := η)
    (fun t ht ↦ ((hφ t ht).sub ((hasDerivAt_id t).const_mul c)).hasDerivWithinAt.congr_deriv
      (by ring))
    (fun t ht ↦ by rw [Real.norm_eq_abs]; exact hη t ht) (convex_uIcc a b)
    Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [Real.norm_eq_abs] at h
  rw [show φ b - φ a - c * (b - a) = φ b - c * b - (φ a - c * a) by ring]
  exact h

/-- **Mixed differences from a mixed partial derivative** (mean value theorem twice): if
`f₁ = ∂f/∂x₁` and `f₀₁ = ∂f₁/∂x₀` exist everywhere and `|f₀₁ - g₀| ≤ ε` on the rectangle spanned
by `x` and `x'`, then `|mixDiff f x x' - g₀ Δx₀ Δx₁| ≤ ε |Δx₀| |Δx₁|`. -/
theorem abs_mixDiff_sub_le_of_deriv {f f₁ f₀₁ : (Fin 2 → ℝ) → ℝ}
    (h₁ : ∀ x : Fin 2 → ℝ, HasDerivAt (fun t ↦ f ![x 0, t]) (f₁ x) (x 1))
    (h₀₁ : ∀ x : Fin 2 → ℝ, HasDerivAt (fun t ↦ f₁ ![t, x 1]) (f₀₁ x) (x 0))
    {x x' : Fin 2 → ℝ} {g₀ ε : ℝ}
    (hε : ∀ r ∈ Set.uIcc (x' 0) (x 0), ∀ t ∈ Set.uIcc (x' 1) (x 1), |f₀₁ ![r, t] - g₀| ≤ ε) :
    |mixDiff f x x' - g₀ * (x 0 - x' 0) * (x 1 - x' 1)| ≤ ε * |x 0 - x' 0| * |x 1 - x' 1| := by
  have hv : ∀ y : Fin 2 → ℝ, (![y 0, y 1] : Fin 2 → ℝ) = y := fun y ↦ by
    funext j
    fin_cases j <;> rfl
  have hd1 : ∀ r t : ℝ, HasDerivAt (fun t' ↦ f ![r, t']) (f₁ ![r, t]) t := fun r t ↦ by
    have := h₁ ![r, t]
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] using this
  have hd01 : ∀ r t : ℝ, HasDerivAt (fun r' ↦ f₁ ![r', t]) (f₀₁ ![r, t]) r := fun r t ↦ by
    have := h₀₁ ![r, t]
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] using this
  set Δ₀ := x 0 - x' 0
  -- the inner difference
  have hinner : ∀ t ∈ Set.uIcc (x' 1) (x 1),
      |(f₁ ![x 0, t] - f₁ ![x' 0, t]) - g₀ * Δ₀| ≤ ε * |Δ₀| := by
    intro t ht
    exact abs_sub_sub_mul_le_of_deriv (φ := fun r ↦ f₁ ![r, t]) (fun r _ ↦ hd01 r t)
      (fun r hr ↦ hε r hr t ht)
  have houter := abs_sub_sub_mul_le_of_deriv (a := x' 1) (b := x 1)
    (φ := fun t ↦ f ![x 0, t] - f ![x' 0, t]) (φ' := fun t ↦ f₁ ![x 0, t] - f₁ ![x' 0, t])
    (c := g₀ * Δ₀) (fun t _ ↦ (hd1 (x 0) t).sub (hd1 (x' 0) t)) hinner
  have hmix : mixDiff f x x' = (f ![x 0, x 1] - f ![x' 0, x 1]) -
      (f ![x 0, x' 1] - f ![x' 0, x' 1]) := by
    unfold mixDiff
    rw [hv x, hv x']
    ring
  rw [hmix]
  calc |(f ![x 0, x 1] - f ![x' 0, x 1]) - (f ![x 0, x' 1] - f ![x' 0, x' 1]) -
        g₀ * Δ₀ * (x 1 - x' 1)| ≤ ε * |Δ₀| * |x 1 - x' 1| := houter
    _ = ε * |x 0 - x' 0| * |x 1 - x' 1| := rfl

/-- **Owen's `Var ≍ n⁻³ log n` from a continuous mixed partial derivative** (`s = 2`): if
`f₁ = ∂f/∂x₁` and `f₀₁ = ∂²f/∂x₀∂x₁` exist everywhere, `f₀₁` is continuous on `[0,1]²` and
non-zero at some point of `[0,1)²`, and `f` is Lipschitz on the cube, then for scrambled
`(0,m,2)`-nets with `m` digits, `c m ≤ b^{3m} Var(μ̂) ≤ C (m + 1)` eventually. -/
theorem variance_scrambledLaw_two_asymp_of_deriv (hb : 1 < b)
    (d : (m : ℕ) → Fin (b ^ m) → Fin 2 → Fin m → Fin b)
    (hnet : ∀ m, IsNet b 0 m fun i j ↦ digitPoint (d m i j) 0)
    {f f₁ f₀₁ : (Fin 2 → ℝ) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (uniformCube 2))
    (h₁ : ∀ x : Fin 2 → ℝ, HasDerivAt (fun t ↦ f ![x 0, t]) (f₁ x) (x 1))
    (h₀₁ : ∀ x : Fin 2 → ℝ, HasDerivAt (fun t ↦ f₁ ![t, x 1]) (f₀₁ x) (x 0))
    (hc : ContinuousOn f₀₁ (Set.pi Set.univ fun _ ↦ Set.Icc (0 : ℝ) 1))
    {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      |f x - f x'| ≤ L * ∑ j, |x j - x' j|)
    {xc : Fin 2 → ℝ} (hxc : ∀ j, xc j ∈ Set.Ico (0 : ℝ) 1) (hne : f₀₁ xc ≠ 0) :
    ∃ c > 0, ∃ C : ℝ, ∀ᶠ m in atTop,
      c * m ≤ (b : ℝ) ^ (3 * m) * Var[fun x ↦ x; scrambledLaw f (d m)] ∧
      (b : ℝ) ^ (3 * m) * Var[fun x ↦ x; scrambledLaw f (d m)] ≤ C * (m + 1) := by
  set K := Set.pi Set.univ fun _ : Fin 2 ↦ Set.Icc (0 : ℝ) 1 with hK
  have hKc : IsCompact K := isCompact_univ_pi fun _ ↦ isCompact_Icc
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hc
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM xc fun j _ ↦ ⟨(hxc j).1, (hxc j).2.le⟩)
  have hrect : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) →
      (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) → ∀ r ∈ Set.uIcc (x' 0) (x 0),
      ∀ t ∈ Set.uIcc (x' 1) (x 1), (![r, t] : Fin 2 → ℝ) ∈ K := by
    intro x x' hx hx' r hr t ht j _
    have hseg : ∀ {a a' v : ℝ}, a ∈ Set.Ico (0 : ℝ) 1 → a' ∈ Set.Ico (0 : ℝ) 1 →
        v ∈ Set.uIcc a' a → v ∈ Set.Icc (0 : ℝ) 1 := by
      intro a a' v ha ha' hv
      rw [Set.mem_uIcc] at hv
      constructor <;> rcases hv with hv | hv <;> linarith [ha.1, ha.2, ha'.1, ha'.2, hv.1, hv.2]
    fin_cases j
    · exact hseg (hx 0) (hx' 0) hr
    · exact hseg (hx 1) (hx' 1) ht
  refine variance_scrambledLaw_two_asymp hb d hnet hfm hf hM0 (fun x x' hx hx' ↦ ?_) hL0 hL hxc
    hne (fun ε hε ↦ ?_)
  · have h := abs_mixDiff_sub_le_of_deriv h₁ h₀₁ (x := x) (x' := x') (g₀ := 0) (ε := M)
      (fun r hr t ht ↦ by
        rw [sub_zero, ← Real.norm_eq_abs]
        exact hM _ (hrect x x' hx hx' r hr t ht))
    simpa only [zero_mul, sub_zero] using h
  · have hcw : ContinuousWithinAt f₀₁ K xc := hc xc fun j _ ↦ ⟨(hxc j).1, (hxc j).2.le⟩
    obtain ⟨δ, hδ, hδf⟩ := Metric.continuousWithinAt_iff.1 hcw ε hε
    refine ⟨δ, hδ, fun x x' hx hx' hxδ hx'δ ↦ ?_⟩
    refine abs_mixDiff_sub_le_of_deriv h₁ h₀₁ fun r hr t ht ↦ ?_
    have hseg : ∀ {a a' v : ℝ} (j : Fin 2), |a - xc j| < δ → |a' - xc j| < δ →
        v ∈ Set.uIcc a' a → |v - xc j| < δ := by
      intro a a' v j ha ha' hv
      rw [Set.mem_uIcc] at hv
      rw [abs_lt] at ha ha' ⊢
      constructor <;> rcases hv with hv | hv <;> linarith [ha.1, ha.2, ha'.1, ha'.2, hv.1, hv.2]
    have hdist : dist (![r, t] : Fin 2 → ℝ) xc < δ := by
      rw [dist_pi_lt_iff hδ]
      intro j
      fin_cases j
      · exact hseg 0 (hxδ 0) (hx'δ 0) hr
      · exact hseg 1 (hxδ 1) (hx'δ 1) ht
    exact (hδf (hrect x x' hx hx' r hr t ht) hdist).le

end RQMCMarkov.OwenScrambling

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# No CLT for the Owen-scrambled net with a discontinuous integrand (post #2, correction)

Post #2 says that with Owen scrambling "a standard CLT applies". In one dimension we proved it for
`C¹` non-constant integrands (`tendstoInDistribution_owenNet`). Here we show that smoothness cannot
be dropped, even when the variance is non-degenerate: for the indicator `f = 1_{[0,1/3)}` and the
base-2 scrambled net, `σₙ > 0` for every `n = 2ᵐ`, but the normalised error `(μ̂ₙ − μ)/σₙ` is
bounded by `3` almost surely for every `m`, so it cannot converge to any normal law. (Only the one
cell containing the jump at `1/3` is random; the estimator takes two values.) Loh's (2003) CLT
assumes a smooth integrand, so this is a correction of the post's unqualified claim, not of Loh.

## Main results

* `not_tendstoInDistribution_gaussian_of_abs_le`: a.s. uniformly bounded random variables do not
  converge in distribution to a normal law `N(m₀, v)`, `v ≠ 0` (portmanteau).
* `abs_sum_indicator_sub_le`: for points `xᵢ` in the cells `[i/n, (i+1)/n)` and `c ∈ [0,1]`,
  `|Σᵢ 1{xᵢ < c} − n c| ≤ 1`.
* `variance_indicator_uniformIco`: `Var_{U[0,1)} 1{u < p} = p (1 − p)` for `p ∈ [0,1]`.
* `two_pow_mod_three`, `stratVar_indicator_third_ge`: for `n = 2ᵐ`,
  `σₙ² ≥ (2/9)/n² > 0` for `f = 1_{[0,1/3)}`.
* `abs_normalised_error_indicator_le`: `|(μ̂ₙ − μ)/σₙ| ≤ 3` for every realisation of the
  scrambled base-2 net with remainders in `[0,1)`.
* `not_tendstoInDistribution_owenNet_indicator` (**counterexample**): for `f = 1_{[0,1/3)}`,
  `(μ̂ₙ − μ)/σₙ` does not converge in distribution to any `N(m₀, v)`, `v ≠ 0`.
-/

namespace RQMCMarkov.OwenScrambling

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

/-- **Bounded variables have no normal limit**: if `|X k| ≤ M` a.s. for every `k`, then `X k` does
not converge in distribution to `Y ~ N(m₀, v)` with `v ≠ 0`. -/
theorem not_tendstoInDistribution_gaussian_of_abs_le {Ω : ℕ → Type*}
    {mΩ : ∀ k, MeasurableSpace (Ω k)} {P : (k : ℕ) → Measure (Ω k)}
    [∀ k, IsProbabilityMeasure (P k)] {X : (k : ℕ) → Ω k → ℝ} {M : ℝ}
    (hM : ∀ k, ∀ᵐ ω ∂(P k), |X k ω| ≤ M) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {Y : Ω' → ℝ} (m₀ : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (hY : HasLaw Y (gaussianReal m₀ v) P') :
    ¬ TendstoInDistribution X atTop Y P P' := by
  intro h
  have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto h.tendsto
    (isOpen_Ioi (a := M))
  have hzero : ∀ k, ((P k).map (X k)) (Ioi M) = 0 := by
    intro k
    rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable k) measurableSet_Ioi,
      measure_eq_zero_iff_ae_notMem]
    filter_upwards [hM k] with ω hω
    intro hmem
    rw [mem_preimage, mem_Ioi] at hmem
    exact absurd (hω.trans' (le_abs_self _)) (not_le.2 hmem)
  change (P'.map Y) (Ioi M) ≤ atTop.liminf fun k ↦ ((P k).map (X k)) (Ioi M) at hle
  rw [funext hzero, liminf_const, nonpos_iff_eq_zero] at hle
  exact ne_gaussianReal_of_measure_Ioi_eq_zero hle m₀ hv hY.map_eq

/-- `Σ_{j<n} 1{j < k} = min n k`. -/
theorem sum_range_ite_lt (n k : ℕ) :
    ∑ j ∈ Finset.range n, (if j < k then (1 : ℕ) else 0) = min n k := by
  induction n with
  | zero => rw [Finset.sum_range_zero, Nat.zero_min]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      by_cases h : n < k
      · simp only [h, ↓reduceIte]
        omega
      · simp only [h, ↓reduceIte]
        omega

/-- `Σ_{i : Fin n} 1{i < k} = min n k`, in `ℝ`. -/
theorem sum_fin_ite_lt (n k : ℕ) :
    ∑ i : Fin n, (if (i : ℕ) < k then (1 : ℝ) else 0) = (min n k : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ if j < k then (1 : ℝ) else 0) n, ← sum_range_ite_lt,
    Nat.cast_sum]
  refine Finset.sum_congr rfl (fun j _ ↦ ?_)
  by_cases h : j < k
  · simp only [h, ↓reduceIte, Nat.cast_one]
  · simp only [h, ↓reduceIte, Nat.cast_zero]

/-- **One boundary cell**: for points `xᵢ ∈ [i/n, (i+1)/n)` and `c ∈ [0,1]`,
`|Σᵢ 1{xᵢ < c} − n c| ≤ 1`. -/
theorem abs_sum_indicator_sub_le {n : ℕ} (hn : n ≠ 0) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    {x : Fin n → ℝ} (hx : ∀ i : Fin n, x i ∈ stratum n i) :
    |∑ i, (Iio c).indicator (fun _ ↦ (1 : ℝ)) (x i) - n * c| ≤ 1 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  set k : ℕ := ⌊(n : ℝ) * c⌋₊ with hk
  have hnc0 : 0 ≤ (n : ℝ) * c := mul_nonneg hn'.le hc0
  have hk1 : (k : ℝ) ≤ n * c := Nat.floor_le hnc0
  have hk2 : (n : ℝ) * c < k + 1 := Nat.lt_floor_add_one _
  have hkn : k ≤ n := by
    have : (k : ℝ) ≤ n := hk1.trans (by nlinarith)
    exact_mod_cast this
  have hlo : ∀ i : Fin n, (if (i : ℕ) < k then (1 : ℝ) else 0) ≤
      (Iio c).indicator (fun _ ↦ (1 : ℝ)) (x i) := by
    intro i
    by_cases h : (i : ℕ) < k
    · simp only [h, ↓reduceIte]
      rw [indicator_of_mem]
      have hi : (i : ℝ) + 1 ≤ k := by exact_mod_cast h
      have hx2 := (hx i).2
      rw [mem_Iio]
      calc x i < ((i : ℝ) + 1) / n := hx2
        _ ≤ k / n := div_le_div_of_nonneg_right hi hn'.le
        _ ≤ c := by rw [div_le_iff₀ hn']; linarith
    · simp only [h, ↓reduceIte]
      exact indicator_nonneg (fun _ _ ↦ zero_le_one) _
  have hhi : ∀ i : Fin n, (Iio c).indicator (fun _ ↦ (1 : ℝ)) (x i) ≤
      (if (i : ℕ) < k + 1 then (1 : ℝ) else 0) := by
    intro i
    by_cases h : (i : ℕ) < k + 1
    · simp only [h, ↓reduceIte]
      exact indicator_le_self' (fun _ _ ↦ zero_le_one) _
    · simp only [h, ↓reduceIte]
      rw [indicator_of_notMem]
      have hi : (k : ℝ) + 1 ≤ i := by
        have : k + 1 ≤ (i : ℕ) := by omega
        exact_mod_cast this
      have hx1 := (hx i).1
      rw [mem_Iio, not_lt]
      calc c ≤ ((k : ℝ) + 1) / n := by rw [le_div_iff₀ hn']; linarith
        _ ≤ i / n := div_le_div_of_nonneg_right hi hn'.le
        _ ≤ x i := hx1
  have hS1 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hlo i
  have hS2 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hhi i
  rw [sum_fin_ite_lt, Nat.min_eq_right hkn] at hS1
  rw [sum_fin_ite_lt] at hS2
  have hmin : ((min n (k + 1) : ℕ) : ℝ) ≤ k + 1 := by
    have : min n (k + 1) ≤ k + 1 := Nat.min_le_right _ _
    exact_mod_cast this
  rw [abs_le]
  constructor <;> linarith

/-- **The variance of an indicator**: `Var_{u ~ U[0,1)} 1{u < p} = p (1 − p)` for `p ∈ [0,1]`. -/
theorem variance_indicator_uniformIco {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Var[(Iio p).indicator (fun _ ↦ (1 : ℝ)); uniformIco] = p * (1 - p) := by
  have := isProbabilityMeasure_uniformIco
  set g : ℝ → ℝ := (Iio p).indicator (fun _ ↦ (1 : ℝ)) with hg
  have hgm : Measurable g := measurable_const.indicator measurableSet_Iio
  have hgL : MemLp g 2 uniformIco := MemLp.of_bound hgm.aestronglyMeasurable 1
    (Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, hg]
      by_cases h : x ∈ Iio p
      · rw [indicator_of_mem h, abs_one]
      · rw [indicator_of_notMem h, abs_zero]
        exact zero_le_one)
  have hsq : g ^ 2 = g := by
    funext x
    rw [Pi.pow_apply, hg]
    by_cases h : x ∈ Iio p
    · rw [indicator_of_mem h, one_pow]
    · rw [indicator_of_notMem h, zero_pow two_ne_zero]
  have hint : ∫ x, g x ∂uniformIco = p := by
    have h1 : g = (Iio p).indicator 1 := rfl
    rw [h1, integral_indicator_one measurableSet_Iio]
    change (volume.restrict (Ico (0 : ℝ) 1)).real (Iio p) = p
    rw [measureReal_def, Measure.restrict_apply measurableSet_Iio]
    have hset : Iio p ∩ Ico (0 : ℝ) 1 = Ico 0 p := by
      ext x
      simp only [mem_inter_iff, mem_Iio, mem_Ico]
      constructor
      · rintro ⟨h1, h2, _⟩
        exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h2, h1, lt_of_lt_of_le h2 hp1⟩
    rw [hset, Real.volume_Ico, sub_zero, ENNReal.toReal_ofReal hp0]
  rw [variance_eq_sub hgL, hsq]
  change ∫ x, g x ∂uniformIco - (∫ x, g x ∂uniformIco) ^ 2 = _
  rw [hint]
  ring

/-- `2ᵐ mod 3 ∈ {1, 2}`. -/
theorem two_pow_mod_three (m : ℕ) : 2 ^ m % 3 = 1 ∨ 2 ^ m % 3 = 2 := by
  induction m with
  | zero => left; rfl
  | succ m ih =>
      rw [pow_succ, Nat.mul_mod]
      rcases ih with h | h <;> rw [h] <;> decide

/-- The integrand of the counterexample, `f = 1_{[0,1/3)}` (on `[0,1)`). -/
noncomputable def indicatorThird : ℝ → ℝ := (Iio (1 / 3 : ℝ)).indicator fun _ ↦ 1

/-- `∫₀¹ 1_{[0,1/3)} = 1/3`. -/
theorem integral_indicatorThird : ∫ x, indicatorThird x ∂uniformIco = 1 / 3 := by
  have := isProbabilityMeasure_uniformIco
  have h1 : indicatorThird = (Iio (1 / 3 : ℝ)).indicator 1 := rfl
  rw [h1, integral_indicator_one measurableSet_Iio]
  change (volume.restrict (Ico (0 : ℝ) 1)).real (Iio (1 / 3)) = 1 / 3
  rw [measureReal_def, Measure.restrict_apply measurableSet_Iio]
  have hset : Iio (1 / 3 : ℝ) ∩ Ico (0 : ℝ) 1 = Ico 0 (1 / 3) := by
    ext x
    simp only [mem_inter_iff, mem_Iio, mem_Ico]
    constructor
    · rintro ⟨h1, h2, _⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1, by linarith⟩
  rw [hset, Real.volume_Ico, sub_zero, ENNReal.toReal_ofReal (by norm_num)]

/-- **The variance is non-degenerate**: for `n = 2ᵐ`, `σₙ² ≥ (2/9)/n²` for `f = 1_{[0,1/3)}`
(the cell containing `1/3` contributes `p(1 − p) = 2/9`, `p = frac(n/3) ∈ {1/3, 2/3}`). -/
theorem stratVar_indicator_third_ge (m : ℕ) :
    2 / 9 / ((2 ^ m : ℕ) : ℝ) ^ 2 ≤ stratVar (2 ^ m) indicatorThird := by
  have := isProbabilityMeasure_uniformIco
  set n : ℕ := 2 ^ m with hn
  have hn0 : n ≠ 0 := pow_ne_zero m two_ne_zero
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn0)
  set k : ℕ := n / 3 with hk
  set r : ℕ := n % 3 with hr
  have hdiv : 3 * k + r = n := Nat.div_add_mod n 3
  have hr12 : r = 1 ∨ r = 2 := two_pow_mod_three m
  have hkn : k < n := by omega
  set p : ℝ := (r : ℝ) / 3 with hp
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by
    rw [hp, div_le_one (by norm_num : (0 : ℝ) < 3)]
    have : r ≤ 3 := by omega
    exact_mod_cast this
  have hpp : p * (1 - p) = 2 / 9 := by
    rcases hr12 with h | h <;> rw [hp, h] <;> norm_num
  -- the cell `k` function equals `1{u < p}` on `[0,1)`
  have hcell : (fun u ↦ indicatorThird (stratumMap n k u)) =ᵐ[uniformIco]
      (Iio p).indicator (fun _ ↦ (1 : ℝ)) := by
    refine ae_restrict_of_forall_mem measurableSet_Ico (fun u _ ↦ ?_)
    have hiff : stratumMap n k u < 1 / 3 ↔ u < p := by
      have hnr : (n : ℝ) = 3 * k + r := by exact_mod_cast hdiv.symm
      simp only [stratumMap, hp]
      rw [div_lt_iff₀ hn', hnr]
      constructor <;> intro h <;> linarith
    change (Iio (1 / 3 : ℝ)).indicator (fun _ ↦ (1 : ℝ)) (stratumMap n k u) =
      (Iio p).indicator (fun _ ↦ (1 : ℝ)) u
    by_cases h : u < p
    · rw [indicator_of_mem (mem_Iio.2 (hiff.2 h)), indicator_of_mem (mem_Iio.2 h)]
    · rw [indicator_of_notMem (fun h' ↦ h (hiff.1 (mem_Iio.1 h'))),
        indicator_of_notMem (fun h' ↦ h (mem_Iio.1 h'))]
  have hVk : Var[fun u ↦ indicatorThird (stratumMap n (⟨k, hkn⟩ : Fin n) u); uniformIco] =
      2 / 9 := by
    rw [variance_congr hcell, variance_indicator_uniformIco hp0 hp1, hpp]
  unfold stratVar
  have hle : Var[fun u ↦ indicatorThird (stratumMap n (⟨k, hkn⟩ : Fin n) u); uniformIco] ≤
      ∑ i : Fin n, Var[fun u ↦ indicatorThird (stratumMap n i u); uniformIco] :=
    Finset.single_le_sum (f := fun i : Fin n ↦
      Var[fun u ↦ indicatorThird (stratumMap n i u); uniformIco])
      (fun i _ ↦ variance_nonneg _ _) (Finset.mem_univ _)
  rw [hVk] at hle
  rw [inv_pow, ← div_eq_inv_mul]
  exact div_le_div_of_nonneg_right hle (sq_nonneg _)

/-- **The normalised error is bounded by `3`**: for every tree and every remainders `r` in
`[0,1)`, the base-2 scrambled net with `f = 1_{[0,1/3)}` has `|(μ̂ₙ − μ)/σₙ| ≤ 3`, `n = 2ᵐ`. -/
theorem abs_normalised_error_indicator_le {m : ℕ} (T : OwenTree 2 m) {r : Fin (2 ^ m) → ℝ}
    (hr : ∀ k, r k ∈ Ico (0 : ℝ) 1) :
    |(sampleMean (2 ^ m) indicatorThird (owenNet T r) - ∫ x, indicatorThird x ∂uniformIco) /
      Real.sqrt (stratVar (2 ^ m) indicatorThird)| ≤ 3 := by
  have hn0 : 2 ^ m ≠ 0 := pow_ne_zero m two_ne_zero
  have hn' : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn0)
  set x : Fin (2 ^ m) → ℝ := stratPoints (2 ^ m) (owenRemainder T r) with hx
  have hxmem : ∀ i : Fin (2 ^ m), x i ∈ stratum (2 ^ m) i := by
    intro i
    have h := stratumMap_preimage_stratum hn0 i
    have hmem : owenRemainder T r i ∈ stratumMap (2 ^ m) i ⁻¹' stratum (2 ^ m) i := by
      rw [h]
      exact hr _
    exact hmem
  have hsum := abs_sum_indicator_sub_le hn0 (c := 1 / 3) (by norm_num) (by norm_num) hxmem
  have herr : |sampleMean (2 ^ m) indicatorThird x - 1 / 3| ≤ 1 / ((2 ^ m : ℕ) : ℝ) := by
    have heq : sampleMean (2 ^ m) indicatorThird x - 1 / 3 =
        (∑ i, (Iio (1 / 3 : ℝ)).indicator (fun _ ↦ (1 : ℝ)) (x i) -
          ((2 ^ m : ℕ) : ℝ) * (1 / 3)) / ((2 ^ m : ℕ) : ℝ) := by
      unfold sampleMean
      rw [indicatorThird]
      field_simp
    rw [heq, abs_div, abs_of_pos hn']
    exact div_le_div_of_nonneg_right hsum hn'.le
  have hs := stratVar_indicator_third_ge m
  have hsq : 1 / (3 * ((2 ^ m : ℕ) : ℝ)) ≤ Real.sqrt (stratVar (2 ^ m) indicatorThird) := by
    refine Real.le_sqrt_of_sq_le ?_
    refine le_trans ?_ hs
    rw [div_pow, mul_pow]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg ((2 ^ m : ℕ) : ℝ)]
  have hspos : 0 < Real.sqrt (stratVar (2 ^ m) indicatorThird) := lt_of_lt_of_le (by positivity) hsq
  rw [sampleMean_owenNet_eq_stratPoints, integral_indicatorThird, abs_div, abs_of_pos hspos,
    div_le_iff₀ hspos]
  calc |sampleMean (2 ^ m) indicatorThird x - 1 / 3| ≤ 1 / ((2 ^ m : ℕ) : ℝ) := herr
    _ = 3 * (1 / (3 * ((2 ^ m : ℕ) : ℝ))) := by field_simp
    _ ≤ 3 * Real.sqrt (stratVar (2 ^ m) indicatorThird) := by linarith

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {mT : ∀ m, MeasurableSpace (OwenTree 2 m)} [∀ m, DiscreteMeasurableSpace (OwenTree 2 m)]

/-- **Counterexample to "a standard CLT applies" without smoothness** (post #2): for the
indicator `f = 1_{[0,1/3)}` and the base-2 Owen-scrambled net (any trees, remainders
`R m ~ U[0,1)^(2ᵐ)`), the variance is non-degenerate (`stratVar_indicator_third_ge`) but the
normalised error `(μ̂ₙ − μ)/σₙ` does not converge in distribution to any `N(m₀, v)`, `v ≠ 0`. -/
theorem not_tendstoInDistribution_owenNet_indicator {P : Measure Ω} [IsProbabilityMeasure P]
    {T : (m : ℕ) → Ω → OwenTree 2 m} {R : (m : ℕ) → Ω → Fin (2 ^ m) → ℝ}
    (hRlaw : ∀ m, HasLaw (R m) (uniformCube (2 ^ m)) P)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ} (m₀ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (hY : HasLaw Y (gaussianReal m₀ v) P') :
    ¬ TendstoInDistribution (fun m ω ↦
      (sampleMean (2 ^ m) indicatorThird (owenNet (T m ω) (R m ω)) -
        ∫ x, indicatorThird x ∂uniformIco) / Real.sqrt (stratVar (2 ^ m) indicatorThird))
      atTop Y (fun _ ↦ P) P' := by
  refine not_tendstoInDistribution_gaussian_of_abs_le (M := 3) (fun m ↦ ?_) m₀ hv hY
  have hall : ∀ k : Fin (2 ^ m), ∀ᵐ ω ∂P, R m ω k ∈ Ico (0 : ℝ) 1 := fun k ↦
    ae_mem_Ico_of_hasLaw ((hasLaw_eval_uniformCube k).comp (hRlaw m))
  filter_upwards [ae_all_iff.2 hall] with ω hω
  exact abs_normalised_error_indicator_le (T m ω) hω

end RQMCMarkov.OwenScrambling

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The genuine nested scramble to any depth is stratified sampling (post #2)

`Owen1DScramble` scrambles the `(0,m,1)`-net `{k/bᵐ}` at depth `m` (the precision of the net) and
takes the digits below as independent uniform remainders. This module removes that modelling
step. The net point `k/bᵐ` has `M = m + d` base-`b` digits `netWord m d k`: the digits of `k`
followed by `d` zeros (`digitEquiv_netWord_val`: its cell at depth `M` is `k bᵈ`). Owen's nested
scramble to depth `M` permutes each of its `M` digits by the permutation of the node given by the
digits before it, with ALL node permutations independent and uniform (a uniform tree
`T : OwenTree b (m + d)`), and adds an independent uniform remainder below digit `M`:
`deepNet T r k = (cell of owenWord T (netWord m d k) + r k)/b^M`.

## Main results

* `digitEquiv_add_val`: the cell of a word of length `m + d` is
  `(cell of its first m digits) · bᵈ + (cell of its last d digits)`.
* `wordFirst_owenWord`, `wordLast_owenWord_netWord`, `deepNet_eq`: the scrambled point of `k` is
  `(σ_T k + (τ_T k + r k)/bᵈ)/bᵐ`, where `σ_T = deepCell T` is the depth-`m` scramble of the top
  of the tree and `τ_T k = deepTail T k` collects the scrambled zero digits of point `k`.
* `card_filter_deepKey_eq`, `card_filter_deepKey_mul`: for a uniform tree the scrambled zero digits
  `τ_T` are uniform on `(Fin bᵈ)^(bᵐ)` and independent of `σ_T` (equal fibre counts, via the
  involution `swapTail`): distinct net points sit below distinct nodes at every level `≥ m`.
* `sum_measure_preimage_digitShift`: adding independent uniform digits to independent uniform
  remainders gives independent uniform remainders, `Σ_τ ν(H_τ⁻¹ A) = (bᵈ)^n ν(A)`.
* `hasLaw_deepRemainder`, `hasLaw_deepNetSorted` (**the gap closed**): for every depth
  `M = m + d ≥ m`, the genuine scramble of the net, relabelled by depth-`m` cell, has exactly the
  law `stratifiedLaw (bᵐ)`: one independent uniform point in each cell. The law does not depend on
  `M`, so it is also the law of the scramble of all infinitely many digits in the projective sense
  (every finite-depth truncation, with uniform remainder, has it); the depth-`m` model of
  `Owen1DScramble` (`d = 0`) is exact.
* `sampleMean_deepNet`, `variance_deepNet_eq_stratVar`: the genuine scrambled-net estimator is the
  stratified estimator of the relabelled remainders, with variance `stratVar (bᵐ) f`.
* `tendstoInDistribution_deepNet`: `tendstoInDistribution_owenNet` for the genuine scramble, with
  any depths `M_m = m + D m` (e.g. `M_m → ∞`): `(μ̂ₙ − μ)/σₙ ⇒ N(0,1)`.

Unlike the CLT of `Owen1DCLT`, these results use the uniformity of the tree: it is what makes the
scrambled zero digits uniform.
-/

namespace RQMCMarkov.OwenScrambling

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

variable {b : ℕ}

/-- The first `m` digits of a word of length `m + d`. -/
def wordFirst {m d : ℕ} (w : DigitWord b (m + d)) : DigitWord b m :=
  fun l ↦ w (Fin.castAdd d l)

/-- The last `d` digits of a word of length `m + d`. -/
def wordLast {m d : ℕ} (w : DigitWord b (m + d)) : DigitWord b d :=
  fun i ↦ w (Fin.natAdd m i)

/-- **Cells split by digits**: the cell of a word of length `m + d` is
`(cell of the first m digits) · bᵈ + (cell of the last d digits)`. -/
theorem digitEquiv_add_val (m d : ℕ) (w : DigitWord b (m + d)) :
    (digitEquiv b (m + d) w : ℕ) =
      (digitEquiv b m (wordFirst w) : ℕ) * b ^ d + digitEquiv b d (wordLast w) := by
  rw [digitEquiv_apply_val, digitEquiv_apply_val, digitEquiv_apply_val, Fin.sum_univ_add,
    Finset.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl (fun l _ ↦ ?_)
    change (w (Fin.castAdd d l) : ℕ) * b ^ (m + d - ((l : ℕ) + 1)) =
      (w (Fin.castAdd d l) : ℕ) * b ^ (m - ((l : ℕ) + 1)) * b ^ d
    rw [mul_assoc, ← pow_add]
    congr 2
    have := l.isLt
    omega
  · refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    change (w (Fin.natAdd m i) : ℕ) * b ^ (m + d - ((m + (i : ℕ)) + 1)) =
      (w (Fin.natAdd m i) : ℕ) * b ^ (d - ((i : ℕ) + 1))
    congr 2
    omega

/-- The first `j` digits of the net point `k/bᵐ`: the digits of `k`, then zeros. -/
def netPrefix [NeZero b] (m j : ℕ) (k : Fin (b ^ m)) : Fin j → Fin b :=
  fun l ↦ if h : (l : ℕ) < m then (digitEquiv b m).symm k ⟨l, h⟩ else 0

/-- The `m + d` digits of the net point `k/bᵐ`. -/
def netWord [NeZero b] (m d : ℕ) (k : Fin (b ^ m)) : DigitWord b (m + d) :=
  netPrefix m (m + d) k

/-- The first `m` digits of the net point are those of `k`. -/
theorem wordFirst_netWord [NeZero b] (m d : ℕ) (k : Fin (b ^ m)) :
    wordFirst (netWord m d k) = (digitEquiv b m).symm k := by
  funext l
  simp only [wordFirst, netWord, netPrefix, Fin.val_castAdd, l.isLt, ↓reduceDIte, Fin.eta]

/-- The last `d` digits of the net point are zero. -/
theorem wordLast_netWord [NeZero b] (m d : ℕ) (k : Fin (b ^ m)) :
    wordLast (netWord m d k) = fun _ ↦ 0 := by
  funext i
  have h : ¬ ((Fin.natAdd m i : Fin (m + d)) : ℕ) < m := by
    rw [Fin.val_natAdd]
    omega
  simp only [wordLast, netWord, netPrefix, h, ↓reduceDIte]

/-- **The net point `k/bᵐ` at depth `m + d`** is the cell `k bᵈ`. -/
theorem digitEquiv_netWord_val [NeZero b] (m d : ℕ) (k : Fin (b ^ m)) :
    (digitEquiv b (m + d) (netWord m d k) : ℕ) = (k : ℕ) * b ^ d := by
  rw [digitEquiv_add_val, wordFirst_netWord, wordLast_netWord, Equiv.apply_symm_apply,
    digitEquiv_apply_val]
  have h0 : ∑ j : Fin d, (((fun _ ↦ (0 : Fin b)) j : Fin b) : ℕ) * b ^ (d - (j + 1)) = 0 :=
    Finset.sum_eq_zero fun j _ ↦ by
      change ((0 : Fin b) : ℕ) * _ = 0
      rw [Fin.val_zero, zero_mul]
  rw [h0, add_zero]

/-- The prefix of the net word at level `m + i` is `netPrefix m (m + i) k`. -/
theorem wordPrefix_netWord [NeZero b] (m d : ℕ) (k : Fin (b ^ m)) (i : Fin d) :
    wordPrefix (netWord m d k) (Fin.natAdd m i) = netPrefix m (m + i) k :=
  rfl

/-- The top of a depth-`(m + d)` tree: its permutations at levels `< m`. -/
def topTree {m d : ℕ} (t : OwenTree b (m + d)) : OwenTree b m :=
  fun j p ↦ t (Fin.castAdd d j) p

/-- The first `m` scrambled digits only use the top of the tree. -/
theorem wordFirst_owenWord {m d : ℕ} (t : OwenTree b (m + d)) (w : DigitWord b (m + d)) :
    wordFirst (owenWord t w) = owenWord (topTree t) (wordFirst w) :=
  rfl

/-- The scrambled zero digits of the net point `k`: digit `i` is the image of `0` under the
permutation of the node `netPrefix m (m + i) k`. -/
def tailWord [NeZero b] {m d : ℕ} (t : OwenTree b (m + d)) (k : Fin (b ^ m)) : DigitWord b d :=
  fun i ↦ t (Fin.natAdd m i) (netPrefix m (m + i) k) 0

/-- The last `d` scrambled digits of the net point are `tailWord`. -/
theorem wordLast_owenWord_netWord [NeZero b] {m d : ℕ} (t : OwenTree b (m + d))
    (k : Fin (b ^ m)) : wordLast (owenWord t (netWord m d k)) = tailWord t k := by
  funext i
  have h := congrFun (wordLast_netWord (b := b) m d k) i
  change t (Fin.natAdd m i) (wordPrefix (netWord m d k) (Fin.natAdd m i))
    (netWord m d k (Fin.natAdd m i)) = _
  change netWord m d k (Fin.natAdd m i) = 0 at h
  rw [h, wordPrefix_netWord]
  rfl

/-- The depth-`m` cell permutation `σ_T` of the deep scramble (its top tree's `owenCell`). -/
noncomputable def deepCell {m d : ℕ} (t : OwenTree b (m + d)) : Equiv.Perm (Fin (b ^ m)) :=
  owenCell (topTree t)

/-- The scrambled zero digits of point `k` as a cell of depth `d`. -/
def deepTail [NeZero b] {m d : ℕ} (t : OwenTree b (m + d)) (k : Fin (b ^ m)) : Fin (b ^ d) :=
  digitEquiv b d (tailWord t k)

/-- **The genuine scramble to depth `M = m + d` of the net**, with uniform remainders `r` below
digit `M`: `(cell of owenWord t (netWord m d k) + r k)/b^M`. -/
noncomputable def deepNet [NeZero b] {m d : ℕ} (t : OwenTree b (m + d)) (r : Fin (b ^ m) → ℝ) :
    Fin (b ^ m) → ℝ :=
  fun k ↦ stratumMap (b ^ (m + d)) (digitEquiv b (m + d) (owenWord t (netWord m d k))) (r k)

/-- **The deep scrambled point**: `(σ_T k + (τ_T k + r k)/bᵈ)/bᵐ`. -/
theorem deepNet_eq [NeZero b] {m d : ℕ} (t : OwenTree b (m + d)) (r : Fin (b ^ m) → ℝ)
    (k : Fin (b ^ m)) :
    deepNet t r k =
      stratumMap (b ^ m) (deepCell t k) (stratumMap (b ^ d) (deepTail t k) (r k)) := by
  have hb : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne b)
  have hv := digitEquiv_add_val m d (owenWord t (netWord m d k))
  rw [wordFirst_owenWord, wordFirst_netWord, wordLast_owenWord_netWord] at hv
  have hc : (deepCell t k : ℕ) = (digitEquiv b m (owenWord (topTree t) ((digitEquiv b m).symm k))
      : ℕ) := rfl
  simp only [deepNet, stratumMap]
  rw [hv, hc]
  unfold deepTail
  push_cast
  rw [pow_add]
  field_simp
  ring

/-- The remainder of the point in depth-`m` cell `j`: `(τ_T(σ_T⁻¹ j) + r(σ_T⁻¹ j))/bᵈ`. -/
noncomputable def deepRemainder [NeZero b] {m d : ℕ} (t : OwenTree b (m + d))
    (r : Fin (b ^ m) → ℝ) : Fin (b ^ m) → ℝ :=
  fun j ↦ stratumMap (b ^ d) (deepTail t ((deepCell t).symm j)) (r ((deepCell t).symm j))

/-- The deep scrambled net relabelled by depth-`m` cell. -/
noncomputable def deepNetSorted [NeZero b] {m d : ℕ} (t : OwenTree b (m + d))
    (r : Fin (b ^ m) → ℝ) : Fin (b ^ m) → ℝ :=
  fun j ↦ deepNet t r ((deepCell t).symm j)

/-- Relabelled by cell, the deep net is the stratified point set of `deepRemainder`. -/
theorem deepNetSorted_eq [NeZero b] {m d : ℕ} (t : OwenTree b (m + d)) (r : Fin (b ^ m) → ℝ) :
    deepNetSorted t r = stratPoints (b ^ m) (deepRemainder t r) := by
  funext j
  simp only [deepNetSorted, deepNet_eq, Equiv.apply_symm_apply]
  rfl

/-- The scrambled-net estimator is the stratified estimator of the relabelled remainders. -/
theorem sampleMean_deepNet [NeZero b] {m d : ℕ} (t : OwenTree b (m + d)) (r : Fin (b ^ m) → ℝ)
    (f : ℝ → ℝ) :
    sampleMean (b ^ m) f (deepNet t r) =
      sampleMean (b ^ m) f (stratPoints (b ^ m) (deepRemainder t r)) := by
  rw [← deepNetSorted_eq]
  unfold sampleMean
  congr 1
  exact (Equiv.sum_comp (deepCell t).symm (fun k ↦ f (deepNet t r k))).symm

/-- The cell of depth `m` read off the first `m` digits of a node at level `j ≥ m`. -/
def kOfPrefix {m j : ℕ} (h : m ≤ j) (p : Fin j → Fin b) : Fin (b ^ m) :=
  digitEquiv b m (fun l ↦ p ⟨l, lt_of_lt_of_le l.2 h⟩)

/-- `kOfPrefix` recovers `k` from the net prefix. -/
theorem kOfPrefix_netPrefix [NeZero b] {m j : ℕ} (h : m ≤ j) (k : Fin (b ^ m)) :
    kOfPrefix h (netPrefix m j k) = k := by
  have hf : (fun l : Fin m ↦ netPrefix m j k ⟨l, lt_of_lt_of_le l.2 h⟩) =
      (digitEquiv b m).symm k := by
    funext l
    simp only [netPrefix, l.isLt, ↓reduceDIte, Fin.eta]
  unfold kOfPrefix
  rw [hf, Equiv.apply_symm_apply]

/-- The tail level `j − m` of a level `j ≥ m`. -/
def tailLevel {m d : ℕ} (j : Fin (m + d)) (h : m ≤ (j : ℕ)) : Fin d :=
  ⟨j - m, by have := j.isLt; omega⟩

/-- `tailLevel (m + i) = i`. -/
theorem tailLevel_natAdd {m d : ℕ} (i : Fin d) (h : m ≤ ((Fin.natAdd m i : Fin (m + d)) : ℕ)) :
    tailLevel (Fin.natAdd m i) h = i := by
  refine Fin.ext ?_
  change ((Fin.natAdd m i : Fin (m + d)) : ℕ) - m = i
  rw [Fin.val_natAdd]
  omega

/-- The tree that composes the permutations at the net nodes `netPrefix m (m + i) k` with the
transpositions `(v k i  v' k i)`, and leaves all other nodes alone. -/
def swapTail [NeZero b] {m d : ℕ} (v v' : Fin (b ^ m) → DigitWord b d)
    (t : OwenTree b (m + d)) : OwenTree b (m + d) :=
  fun j p ↦ if h : m ≤ (j : ℕ) then
    (if p = netPrefix m j (kOfPrefix h p) then
      Equiv.swap (v (kOfPrefix h p) (tailLevel j h)) (v' (kOfPrefix h p) (tailLevel j h)) * t j p
    else t j p)
  else t j p

/-- `swapTail` is an involution. -/
theorem swapTail_swapTail [NeZero b] {m d : ℕ} (v v' : Fin (b ^ m) → DigitWord b d)
    (t : OwenTree b (m + d)) : swapTail v v' (swapTail v v' t) = t := by
  funext j p
  unfold swapTail
  split_ifs with h hp <;> first | exact Equiv.swap_mul_self_mul _ _ _ | rfl

/-- `swapTail` leaves the top of the tree unchanged. -/
theorem topTree_swapTail [NeZero b] {m d : ℕ} (v v' : Fin (b ^ m) → DigitWord b d)
    (t : OwenTree b (m + d)) : topTree (swapTail v v' t) = topTree t := by
  funext j p
  have h : ¬ m ≤ ((Fin.castAdd d j : Fin (m + d)) : ℕ) := by
    rw [Fin.val_castAdd]
    have := j.isLt
    omega
  simp only [topTree, swapTail, h, ↓reduceDIte]

/-- `swapTail` swaps the scrambled zero digits. -/
theorem tailWord_swapTail [NeZero b] {m d : ℕ} (v v' : Fin (b ^ m) → DigitWord b d)
    (t : OwenTree b (m + d)) (k : Fin (b ^ m)) (i : Fin d) :
    tailWord (swapTail v v' t) k i = Equiv.swap (v k i) (v' k i) (tailWord t k i) := by
  have h : m ≤ ((Fin.natAdd m i : Fin (m + d)) : ℕ) := by
    rw [Fin.val_natAdd]
    omega
  have hk : kOfPrefix h (netPrefix m (m + i) k) = k := kOfPrefix_netPrefix h k
  have hi := tailLevel_natAdd i h
  change swapTail v v' t (Fin.natAdd m i) (netPrefix m (m + i) k) 0 = _
  unfold swapTail
  split_ifs with h1
  · rw [hk, hi]
    rfl
  · exact absurd (by rw [hk]; rfl) h1

/-- The key of a deep tree: its depth-`m` cell permutation and its scrambled zero digits. -/
noncomputable def deepKey [NeZero b] {m d : ℕ} (t : OwenTree b (m + d)) :
    Equiv.Perm (Fin (b ^ m)) × (Fin (b ^ m) → Fin (b ^ d)) :=
  (deepCell t, deepTail t)

/-- `swapTail` maps the trees with key `(s, τ)` onto those with key `(s, τ')`. -/
theorem deepKey_swapTail_eq_iff [NeZero b] {m d : ℕ} (s : Equiv.Perm (Fin (b ^ m)))
    (τ τ' : Fin (b ^ m) → Fin (b ^ d)) (t : OwenTree b (m + d)) :
    deepKey (swapTail (fun k ↦ (digitEquiv b d).symm (τ k)) (fun k ↦ (digitEquiv b d).symm (τ' k))
      t) = (s, τ') ↔ deepKey t = (s, τ) := by
  have hcell : deepCell (swapTail (fun k ↦ (digitEquiv b d).symm (τ k))
      (fun k ↦ (digitEquiv b d).symm (τ' k)) t) = deepCell t := by
    unfold deepCell
    rw [topTree_swapTail]
  have htail : ∀ k, deepTail (swapTail (fun k ↦ (digitEquiv b d).symm (τ k))
      (fun k ↦ (digitEquiv b d).symm (τ' k)) t) k = τ' k ↔ deepTail t k = τ k := by
    intro k
    unfold deepTail
    rw [← Equiv.eq_symm_apply, ← Equiv.eq_symm_apply]
    constructor
    · intro h
      funext i
      have hi := congrFun h i
      rw [tailWord_swapTail, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at hi
      exact hi
    · intro h
      funext i
      rw [tailWord_swapTail, h, Equiv.swap_apply_left]
  unfold deepKey
  rw [hcell, Prod.mk.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, funext fun k ↦ (htail k).1 (congrFun h2 k)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, funext fun k ↦ (htail k).2 (congrFun h2 k)⟩

/-- **The scrambled zero digits are uniform and independent of `σ_T`**: the number of trees with
key `(s, τ)` does not depend on `τ`. -/
theorem card_filter_deepKey_eq [NeZero b] {m d : ℕ} (s : Equiv.Perm (Fin (b ^ m)))
    (τ τ' : Fin (b ^ m) → Fin (b ^ d)) :
    (Finset.univ.filter fun t : OwenTree b (m + d) ↦ deepKey t = (s, τ)).card =
      (Finset.univ.filter fun t : OwenTree b (m + d) ↦ deepKey t = (s, τ')).card := by
  set v : Fin (b ^ m) → DigitWord b d := fun k ↦ (digitEquiv b d).symm (τ k)
  set v' : Fin (b ^ m) → DigitWord b d := fun k ↦ (digitEquiv b d).symm (τ' k)
  refine Finset.card_nbij' (swapTail v v') (swapTail v v') (fun t ht ↦ ?_) (fun t ht ↦ ?_)
    (fun t _ ↦ swapTail_swapTail v v' t) (fun t _ ↦ swapTail_swapTail v v' t)
  · rw [Finset.mem_coe, Finset.mem_filter] at ht ⊢
    exact ⟨Finset.mem_univ _, (deepKey_swapTail_eq_iff s τ τ' t).2 ht.2⟩
  · rw [Finset.mem_coe, Finset.mem_filter] at ht ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← deepKey_swapTail_eq_iff s τ τ' (swapTail v v' _), swapTail_swapTail]
    exact ht.2

/-- Summing the fibre counts over all keys counts all trees. -/
theorem sum_card_filter_deepKey [NeZero b] (m d : ℕ) :
    ∑ s : Equiv.Perm (Fin (b ^ m)), ∑ τ : Fin (b ^ m) → Fin (b ^ d),
      (Finset.univ.filter fun t : OwenTree b (m + d) ↦ deepKey t = (s, τ)).card =
        Fintype.card (OwenTree b (m + d)) := by
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := deepKey)
    (t := Finset.univ) (fun _ _ ↦ Finset.mem_univ _), Fintype.sum_prod_type]

/-- On the uniform cube, the coordinatewise maps `H_τ r k = (τ k + r k)/B`. -/
noncomputable def digitShift (B : ℕ) {n : ℕ} (τ : Fin n → Fin B) (r : Fin n → ℝ) : Fin n → ℝ :=
  fun k ↦ stratumMap B (τ k) (r k)

/-- `digitShift` is measurable. -/
theorem measurable_digitShift (B : ℕ) {n : ℕ} (τ : Fin n → Fin B) :
    Measurable (digitShift B τ) :=
  Measurable.of_eval fun k ↦ (measurable_stratumMap B _).comp (measurable_pi_apply k)

/-- **Uniform digits plus uniform remainders are uniform remainders**: averaging the laws of
`(τ k + U k)/B` over all `τ : Fin n → Fin B` gives `U[0,1)ⁿ` again. -/
theorem sum_measure_preimage_digitShift {B n : ℕ} (hB : B ≠ 0) {A : Set (Fin n → ℝ)}
    (hA : MeasurableSet A) :
    ∑ τ : Fin n → Fin B, uniformCube n (digitShift B τ ⁻¹' A) =
      ((B : ℝ≥0∞) ^ n) * uniformCube n A := by
  have := isProbabilityMeasure_uniformIco
  have hB0 : (B : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hB
  have hBt : (B : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top B
  have hBn0 : (B : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero n hB0
  have hBnt : (B : ℝ≥0∞) ^ n ≠ ⊤ := ENNReal.pow_ne_top hBt
  set μ' : Measure (Fin n → ℝ) := (((B : ℝ≥0∞) ^ n)⁻¹) •
    ∑ τ : Fin n → Fin B, (uniformCube n).map (digitShift B τ) with hμ'
  have h1 : ∀ S : Set ℝ, MeasurableSet S →
      ∑ c : Fin B, uniformIco (stratumMap B c ⁻¹' S) = (B : ℝ≥0∞) * uniformIco S := by
    intro S hS
    have h := congrArg (fun μ : Measure ℝ ↦ μ S) (sum_map_stratumMap hB)
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul] at h
    rw [← h]
    refine Finset.sum_congr rfl (fun c _ ↦ ?_)
    rw [Measure.map_apply (measurable_stratumMap B c) hS]
  have heq : uniformCube n = μ' := by
    refine Measure.pi_eq (fun s hs ↦ ?_)
    have hpre : ∀ τ : Fin n → Fin B, digitShift B τ ⁻¹' univ.pi s =
        univ.pi fun k ↦ stratumMap B (τ k) ⁻¹' s k := by
      intro τ
      ext r
      simp only [mem_preimage, mem_univ_pi, digitShift]
    rw [hμ', Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl (fun τ _ ↦ by
      rw [Measure.map_apply (measurable_digitShift B τ) (MeasurableSet.univ_pi hs), hpre τ,
        Measure.pi_pi])]
    rw [← Fintype.prod_sum (fun k (c : Fin B) ↦ uniformIco (stratumMap B c ⁻¹' s k)),
      Finset.prod_congr rfl (fun k _ ↦ h1 (s k) (hs k)), Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_assoc,
      ENNReal.inv_mul_cancel hBn0 hBnt, one_mul]
  have hval := congrArg (fun μ : Measure (Fin n → ℝ) ↦ μ A) heq
  simp only [hμ', Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul] at hval
  rw [hval, ← mul_assoc, ENNReal.mul_inv_cancel hBn0 hBnt, one_mul]
  refine Finset.sum_congr rfl (fun τ _ ↦ ?_)
  rw [Measure.map_apply (measurable_digitShift B τ) hA]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The gap closed: the genuine nested scramble to any depth `M = m + d ≥ m`.** For a uniform
tree `T : OwenTree b (m + d)` independent of the remainders `R ~ U[0,1)^(bᵐ)` below digit `M`,
the remainders of the scrambled net points within their depth-`m` cells, relabelled by cell,
are again `U[0,1)^(bᵐ)`. -/
theorem hasLaw_deepRemainder [NeZero b] {m d : ℕ} {mT : MeasurableSpace (OwenTree b (m + d))}
    [DiscreteMeasurableSpace (OwenTree b (m + d))] {P : Measure Ω} [IsProbabilityMeasure P]
    {T : Ω → OwenTree b (m + d)} {R : Ω → Fin (b ^ m) → ℝ} (hT : Measurable T)
    (hR : Measurable R) (hTlaw : HasLaw T (uniformOn univ) P)
    (hRlaw : HasLaw R (uniformCube (b ^ m)) P) (hind : IndepFun T R P) :
    HasLaw (fun ω ↦ deepRemainder (T ω) (R ω)) (uniformCube (b ^ m)) P := by
  have := isProbabilityMeasure_uniformIco
  have hBd0 : b ^ d ≠ 0 := pow_ne_zero d (NeZero.ne b)
  have hcomp : ∀ t : OwenTree b (m + d), deepRemainder t =
      (fun (r : Fin (b ^ m) → ℝ) j ↦ r ((deepCell t).symm j)) ∘ digitShift (b ^ d) (deepTail t) :=
    fun t ↦ rfl
  have hGm : ∀ t : OwenTree b (m + d), Measurable (deepRemainder t) := fun t ↦ by
    rw [hcomp t]
    exact (measurePreserving_comp_perm (deepCell t)).measurable.comp
      (measurable_digitShift (b ^ d) _)
  have hm := measurable_comp_of_countable hT hR hGm
  refine ⟨hm.aemeasurable, ?_⟩
  ext A hA
  set ν := uniformCube (b ^ m) with hν
  set c : ℝ≥0∞ := (Fintype.card (OwenTree b (m + d)) : ℝ≥0∞)⁻¹ with hc
  set F : Equiv.Perm (Fin (b ^ m)) × (Fin (b ^ m) → Fin (b ^ d)) → ℝ≥0∞ := fun p ↦
    ν (digitShift (b ^ d) p.2 ⁻¹' ((fun (r : Fin (b ^ m) → ℝ) j ↦ r (p.1.symm j)) ⁻¹' A)) with hF
  have hterm : ∀ t, P.map R (deepRemainder t ⁻¹' A) = F (deepKey t) := fun t ↦ by
    rw [hRlaw.map_eq, hcomp t]
    rfl
  -- group the trees by key
  set a : Equiv.Perm (Fin (b ^ m)) → ℕ := fun s ↦
    (Finset.univ.filter fun t : OwenTree b (m + d) ↦ deepKey t = (s, fun _ ↦ 0)).card with ha
  have hfib : ∀ s τ, (Finset.univ.filter fun t : OwenTree b (m + d) ↦ deepKey t = (s, τ)).card =
      a s := fun s τ ↦ card_filter_deepKey_eq s τ _
  have hpres : ∀ s : Equiv.Perm (Fin (b ^ m)),
      ν ((fun (r : Fin (b ^ m) → ℝ) j ↦ r (s.symm j)) ⁻¹' A) = ν A := fun s ↦ by
    rw [← Measure.map_apply (measurePreserving_comp_perm s).measurable hA,
      (measurePreserving_comp_perm s).map_eq]
  have hsumτ : ∀ s : Equiv.Perm (Fin (b ^ m)), ∑ τ : Fin (b ^ m) → Fin (b ^ d), F (s, τ) =
      ((Nat.cast (b ^ d) : ℝ≥0∞) ^ (b ^ m)) * ν A := fun s ↦ by
    rw [hF]
    simp only
    rw [sum_measure_preimage_digitShift hBd0
      ((measurePreserving_comp_perm s).measurable hA), hpres s]
  have htotN : ∑ s : Equiv.Perm (Fin (b ^ m)), a s * (b ^ d) ^ (b ^ m) =
      Fintype.card (OwenTree b (m + d)) := by
    rw [← sum_card_filter_deepKey (b := b) m d]
    refine Finset.sum_congr rfl (fun s _ ↦ ?_)
    rw [Finset.sum_congr rfl (fun τ _ ↦ hfib s τ), Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, smul_eq_mul, mul_comm]
  have htot : ∑ s : Equiv.Perm (Fin (b ^ m)),
      (a s : ℝ≥0∞) * ((Nat.cast (b ^ d) : ℝ≥0∞)) ^ (b ^ m) = Fintype.card (OwenTree b (m + d)) := by
    rw [← htotN, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun s _ ↦ ?_)
    rw [Nat.cast_mul, Nat.cast_pow (α := ℝ≥0∞) (b ^ d) (b ^ m)]
  rw [Measure.map_apply hm hA, measure_preimage_comp_of_indepFun hT hR hind hGm hA,
    Finset.sum_congr rfl (fun t _ ↦ by
      rw [measure_preimage_singleton_of_uniform hT hTlaw t, hterm t]),
    ← Finset.sum_fiberwise Finset.univ (fun t : OwenTree b (m + d) ↦ deepKey t)
      (fun t ↦ c * F (deepKey t))]
  have hinner : ∀ p : Equiv.Perm (Fin (b ^ m)) × (Fin (b ^ m) → Fin (b ^ d)),
      ∑ t ∈ Finset.univ with deepKey t = p, c * F (deepKey t) = (a p.1 : ℝ≥0∞) * (c * F p) := by
    intro p
    rw [Finset.sum_congr rfl (fun t ht ↦ by rw [(Finset.mem_filter.1 ht).2]), Finset.sum_const,
      nsmul_eq_mul, ← hfib p.1 p.2]
  rw [Finset.sum_congr rfl (fun p _ ↦ hinner p), Fintype.sum_prod_type]
  have hs : ∀ s : Equiv.Perm (Fin (b ^ m)),
      ∑ τ : Fin (b ^ m) → Fin (b ^ d), (a s : ℝ≥0∞) * (c * F (s, τ)) =
        ((a s : ℝ≥0∞) * (Nat.cast (b ^ d) : ℝ≥0∞) ^ (b ^ m)) * (c * ν A) := fun s ↦ by
    rw [← Finset.mul_sum, ← Finset.mul_sum, hsumτ s]
    ring
  rw [Finset.sum_congr rfl (fun s _ ↦ hs s), ← Finset.sum_mul, htot, hc, ← mul_assoc,
    ENNReal.mul_inv_cancel (Nat.cast_ne_zero.2 Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
    one_mul]

/-- **The genuine scrambled net is independent stratified sampling, at every depth**: relabelled
by depth-`m` cell, the scramble to depth `m + d` of `{k/bᵐ}` has the law `stratifiedLaw (bᵐ)`,
for every `d` (so for the full infinite-digit scramble in the projective sense). -/
theorem hasLaw_deepNetSorted [NeZero b] {m d : ℕ} {mT : MeasurableSpace (OwenTree b (m + d))}
    [DiscreteMeasurableSpace (OwenTree b (m + d))] {P : Measure Ω} [IsProbabilityMeasure P]
    {T : Ω → OwenTree b (m + d)} {R : Ω → Fin (b ^ m) → ℝ} (hT : Measurable T)
    (hR : Measurable R) (hTlaw : HasLaw T (uniformOn univ) P)
    (hRlaw : HasLaw R (uniformCube (b ^ m)) P) (hind : IndepFun T R P) :
    HasLaw (fun ω ↦ deepNetSorted (T ω) (R ω)) (stratifiedLaw (b ^ m)) P := by
  have hV := hasLaw_deepRemainder hT hR hTlaw hRlaw hind
  have hfun : (fun ω ↦ deepNetSorted (T ω) (R ω)) =
      stratPoints (b ^ m) ∘ fun ω ↦ deepRemainder (T ω) (R ω) := by
    funext ω
    rw [Function.comp_apply, deepNetSorted_eq]
  rw [hfun]
  refine ⟨(measurable_stratPoints _).comp_aemeasurable hV.aemeasurable, ?_⟩
  rw [← AEMeasurable.map_map_of_aemeasurable (measurable_stratPoints _).aemeasurable
    hV.aemeasurable, hV.map_eq]
  rfl

/-- **The variance of the genuine scrambled net** is `stratVar (bᵐ) f`, at every depth. -/
theorem variance_deepNet_eq_stratVar [NeZero b] {m d : ℕ}
    {mT : MeasurableSpace (OwenTree b (m + d))} [DiscreteMeasurableSpace (OwenTree b (m + d))]
    {f : ℝ → ℝ} (hfm : Measurable f) (hc : ContinuousOn f (Icc 0 1)) {P : Measure Ω}
    [IsProbabilityMeasure P] {T : Ω → OwenTree b (m + d)} {R : Ω → Fin (b ^ m) → ℝ}
    (hT : Measurable T) (hR : Measurable R) (hTlaw : HasLaw T (uniformOn univ) P)
    (hRlaw : HasLaw R (uniformCube (b ^ m)) P) (hind : IndepFun T R P) :
    Var[fun ω ↦ sampleMean (b ^ m) f (deepNet (T ω) (R ω)); P] = stratVar (b ^ m) f := by
  have := isProbabilityMeasure_uniformIco
  have hV := hasLaw_deepRemainder hT hR hTlaw hRlaw hind
  have hfun : (fun ω ↦ sampleMean (b ^ m) f (deepNet (T ω) (R ω))) =
      (fun v ↦ sampleMean (b ^ m) f (stratPoints (b ^ m) v)) ∘
        fun ω ↦ deepRemainder (T ω) (R ω) := by
    funext ω
    rw [Function.comp_apply, sampleMean_deepNet]
  have hg : Measurable fun v ↦ sampleMean (b ^ m) f (stratPoints (b ^ m) v) :=
    (measurable_sampleMean hfm).comp (measurable_stratPoints _)
  rw [hfun, ← variance_map (hV.map_eq ▸ hg.aemeasurable) hV.aemeasurable, hV.map_eq]
  exact variance_stratified_eq (pow_ne_zero m (NeZero.ne b)) hasLaw_eval_uniformCube
    (iIndepFun_eval_uniformCube _) (memLp_uniformIco_of_continuousOn hfm hc 2)

/-- **Post #2's CLT for the genuine Owen scramble** (one dimension): let `b ≥ 2` and, for each
`m`, let `T m` be a uniform tree of any depth `m + D m ≥ m` (e.g. `D m → ∞`), independent of the
remainders `R m ~ U[0,1)^(bᵐ)` below its last digit. For measurable `f`, `C¹` and non-constant on
`[0,1]`, the scrambled-net estimator `μ̂ₙ = (1/n) Σₖ f(deepNet (T m) (R m) k)`, `n = bᵐ`,
satisfies `(μ̂ₙ − ∫₀¹ f)/σₙ ⇒ N(0,1)`, with `σₙ² = stratVar n f = Var(μ̂ₙ)`. -/
theorem tendstoInDistribution_deepNet [NeZero b] (hb : 1 < b) (D : ℕ → ℕ)
    {mT : ∀ m, MeasurableSpace (OwenTree b (m + D m))}
    [∀ m, DiscreteMeasurableSpace (OwenTree b (m + D m))] {f f' : ℝ → ℝ} (hfm : Measurable f)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) (hnc : ∃ x ∈ Icc (0 : ℝ) 1, f x ≠ f 0)
    {P : Measure Ω} [IsProbabilityMeasure P] {T : (m : ℕ) → Ω → OwenTree b (m + D m)}
    {R : (m : ℕ) → Ω → Fin (b ^ m) → ℝ} (hT : ∀ m, Measurable (T m)) (hR : ∀ m, Measurable (R m))
    (hTlaw : ∀ m, HasLaw (T m) (uniformOn univ) P)
    (hRlaw : ∀ m, HasLaw (R m) (uniformCube (b ^ m)) P) (hind : ∀ m, IndepFun (T m) (R m) P)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun m ω ↦ (sampleMean (b ^ m) f (deepNet (T m ω) (R m ω)) -
      ∫ x, f x ∂uniformIco) / Real.sqrt (stratVar (b ^ m) f)) atTop Z (fun _ ↦ P) P' := by
  have hfun : (fun m ω ↦ (sampleMean (b ^ m) f (deepNet (T m ω) (R m ω)) -
      ∫ x, f x ∂uniformIco) / Real.sqrt (stratVar (b ^ m) f)) =
      fun m ω ↦ (sampleMean (b ^ m) f (stratPoints (b ^ m) (deepRemainder (T m ω) (R m ω))) -
        ∫ x, f x ∂uniformIco) / Real.sqrt (stratVar (b ^ m) f) := by
    funext m ω
    rw [sampleMean_deepNet]
  rw [hfun]
  exact tendstoInDistribution_stratified hfm hf hf' hnc (N := fun m ↦ b ^ m)
    (tendsto_pow_atTop_atTop_of_one_lt hb) (Ω := fun _ ↦ Ω) (P := fun _ ↦ P)
    (V := fun m ω ↦ deepRemainder (T m ω) (R m ω))
    (fun m ↦ hasLaw_deepRemainder (hT m) (hR m) (hTlaw m) (hRlaw m) (hind m)) hZ

end RQMCMarkov.OwenScrambling

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Finite product spaces: independence, moments, and a conditional Lindeberg bound

Tools for Loh's (2003) CLT for non-additive integrands (post #2). A nested scramble is a
function `ρ : Γ → P` from the nodes of a tree to the permutations of the digits, and the uniform
scramble is the uniform law on these functions, under which the node permutations are
independent. This module proves what that independence gives on a finite product space, with
the uniform average `unifAvg` in place of the expectation.

## Main results

* `unifAvg_mul_of_disjoint`: functions of disjoint sets of coordinates are uncorrelated
  (independent).
* `unifAvg_eval`, `unifAvg_prod`: one coordinate is uniform; the average of a product of
  functions of distinct coordinates is the product of the averages.
* `unifAvg_sq_sum_eq`, `unifAvg_pow_four_sum_le`: for centred terms of distinct coordinates,
  `E[(Σ X_j)²] = Σ E[X_j²]` and `E[(Σ X_j)⁴] ≤ 3 (Σ β_j²)²` when `|X_j| ≤ β_j`.
* `sum_perm_apply`: under a uniform permutation every point has a uniform image.
* `norm_unifAvg_cexp_sub_le`: the cubic bound for the characteristic function of a bounded
  centred variable on a finite uniform space.
* `sq_unifAvg_sum_mul_le`: Cauchy–Schwarz for averages of finite sums.
* `tendsto_unifAvg_cexp_nodeSum` (**conditional Lindeberg CLT, Lyapunov form**): for each `m`
  let `ξ m r γ π` be centred node terms, indexed by an outer variable `r` and the nodes `γ`, with
  `|ξ m r γ π| ≤ M m r γ`, and let `T = Σ_γ ξ m r γ (ρ γ)` with `ρ` uniform. If the conditional
  variances `V(r) = Σ_γ E_π ξ²` satisfy `E_r |V(r)/s² - 1| → 0`, `E_r Σ_γ (M/s)²` stays bounded
  and `E_r Σ_γ (M/s)⁴ → 0`, then the characteristic function of `T / s` at `τ_m → t` tends to
  `e^{-t²/2}`. This is the CLT for sums that are, conditionally on `r`, sums of independent
  terms, with a random conditional variance that concentrates.
-/

namespace RQMCMarkov.OwenScrambling

open Finset Filter Complex
open scoped Topology

/-- The uniform average `(#α)⁻¹ Σ_a F a` of a function on a finite type. -/
noncomputable def unifAvg {α : Type*} [Fintype α] {𝕜 : Type*} [DivisionRing 𝕜] (F : α → 𝕜) :
    𝕜 :=
  (Fintype.card α : 𝕜)⁻¹ * ∑ a, F a

/-- The average is additive. -/
theorem unifAvg_add {α : Type*} [Fintype α] (F G : α → ℝ) :
    unifAvg (fun a ↦ F a + G a) = unifAvg F + unifAvg G := by
  unfold unifAvg
  rw [Finset.sum_add_distrib, mul_add]

/-- The average commutes with multiplication by a constant. -/
theorem unifAvg_const_mul {α : Type*} [Fintype α] (c : ℝ) (F : α → ℝ) :
    unifAvg (fun a ↦ c * F a) = c * unifAvg F := by
  unfold unifAvg
  rw [← Finset.mul_sum]
  ring

/-- The average commutes with multiplication by a constant on the right. -/
theorem unifAvg_mul_const {α : Type*} [Fintype α] (F : α → ℝ) (c : ℝ) :
    unifAvg (fun a ↦ F a * c) = unifAvg F * c := by
  unfold unifAvg
  rw [← Finset.sum_mul]
  ring

/-- The average of a constant. -/
theorem unifAvg_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    unifAvg (fun _ : α ↦ c) = c := by
  unfold unifAvg
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  field_simp

/-- The average is monotone. -/
theorem unifAvg_mono {α : Type*} [Fintype α] {F G : α → ℝ} (h : ∀ a, F a ≤ G a) :
    unifAvg F ≤ unifAvg G := by
  unfold unifAvg
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ ↦ h a)
    (inv_nonneg.2 (Nat.cast_nonneg _))

/-- The average of a nonnegative function is nonnegative. -/
theorem unifAvg_nonneg {α : Type*} [Fintype α] {F : α → ℝ} (h : ∀ a, 0 ≤ F a) :
    0 ≤ unifAvg F := by
  unfold unifAvg
  exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (Finset.sum_nonneg fun a _ ↦ h a)

/-- The average of a finite sum of functions. -/
theorem unifAvg_sum {α ι : Type*} [Fintype α] (s : Finset ι) (F : ι → α → ℝ) :
    unifAvg (fun a ↦ ∑ i ∈ s, F i a) = ∑ i ∈ s, unifAvg (F i) := by
  unfold unifAvg
  rw [Finset.sum_comm, Finset.mul_sum]

/-- `|E F| ≤ E |F|`. -/
theorem abs_unifAvg_le {α : Type*} [Fintype α] (F : α → ℝ) :
    |unifAvg F| ≤ unifAvg fun a ↦ |F a| := by
  unfold unifAvg
  rw [abs_mul, abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
    (inv_nonneg.2 (Nat.cast_nonneg _))

/-- **Cauchy–Schwarz** for averages: `(E[F G])² ≤ E[F²] E[G²]`. -/
theorem sq_unifAvg_mul_le {α : Type*} [Fintype α] (F G : α → ℝ) :
    (unifAvg fun a ↦ F a * G a) ^ 2 ≤ (unifAvg fun a ↦ F a ^ 2) * unifAvg fun a ↦ G a ^ 2 := by
  unfold unifAvg
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ F G
  have hc : (0 : ℝ) ≤ ((Fintype.card α : ℝ)⁻¹) ^ 2 := sq_nonneg _
  calc ((Fintype.card α : ℝ)⁻¹ * ∑ a, F a * G a) ^ 2
      = ((Fintype.card α : ℝ)⁻¹) ^ 2 * (∑ a, F a * G a) ^ 2 := by ring
    _ ≤ ((Fintype.card α : ℝ)⁻¹) ^ 2 * ((∑ a, F a ^ 2) * ∑ a, G a ^ 2) :=
        mul_le_mul_of_nonneg_left h hc
    _ = _ := by ring

/-- **Jensen** for averages: `(E F)² ≤ E[F²]`. -/
theorem sq_unifAvg_le {α : Type*} [Fintype α] (F : α → ℝ) :
    (unifAvg F) ^ 2 ≤ unifAvg fun a ↦ F a ^ 2 := by
  rcases isEmpty_or_nonempty α with hα | hα
  · unfold unifAvg
    rw [Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_empty]
    simp
  have h := sq_unifAvg_mul_le F (fun _ ↦ 1)
  simp only [mul_one, one_pow] at h
  rw [unifAvg_const] at h
  linarith

/-- **Functions of disjoint sets of coordinates are independent** under the uniform law on
`Γ → P`: if `F` depends only on the coordinates in `p` and `G` only on those outside `p`, then
`E[F G] = E[F] E[G]`. -/
theorem unifAvg_mul_of_disjoint {Γ P : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype P]
    [Nonempty P]
    (p : Γ → Prop) {F G : (Γ → P) → ℝ}
    (hF : ∀ ρ ρ' : Γ → P, (∀ γ, p γ → ρ γ = ρ' γ) → F ρ = F ρ')
    (hG : ∀ ρ ρ' : Γ → P, (∀ γ, ¬ p γ → ρ γ = ρ' γ) → G ρ = G ρ') :
    unifAvg (fun ρ ↦ F ρ * G ρ) = unifAvg F * unifAvg G := by
  classical
  set e := Equiv.piEquivPiSubtypeProd p (fun _ : Γ ↦ P) with he
  obtain ⟨pm₀⟩ := ‹Nonempty P›
  set a₀ : ∀ _ : {x // p x}, P := fun _ ↦ pm₀
  set c₀ : ∀ _ : {x // ¬ p x}, P := fun _ ↦ pm₀
  have hFe : ∀ a c, F (e.symm (a, c)) = F (e.symm (a, c₀)) := fun a c ↦ hF _ _ fun γ hγ ↦ by
    simp [he, Equiv.piEquivPiSubtypeProd_symm_apply, hγ]
  have hGe : ∀ a c, G (e.symm (a, c)) = G (e.symm (a₀, c)) := fun a c ↦ hG _ _ fun γ hγ ↦ by
    simp [he, Equiv.piEquivPiSubtypeProd_symm_apply, hγ]
  have hsum : ∀ H : (Γ → P) → ℝ, ∑ ρ, H ρ = ∑ a, ∑ c, H (e.symm (a, c)) := fun H ↦ by
    rw [← Fintype.sum_prod_type (f := fun q ↦ H (e.symm q))]
    exact (Fintype.sum_equiv e.symm (fun q ↦ H (e.symm q)) H fun _ ↦ rfl).symm
  have hcard : (Fintype.card (Γ → P) : ℝ) = (Fintype.card (∀ _ : {x // p x}, P) : ℝ) *
      (Fintype.card (∀ _ : {x // ¬ p x}, P) : ℝ) := by
    rw [Fintype.card_congr e, Fintype.card_prod, Nat.cast_mul]
  set A := (Fintype.card (∀ _ : {x // p x}, P) : ℝ)
  set C := (Fintype.card (∀ _ : {x // ¬ p x}, P) : ℝ)
  have hA : A ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hC : C ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have e1 : ∑ ρ, F ρ * G ρ = (∑ a, F (e.symm (a, c₀))) * ∑ c, G (e.symm (a₀, c)) := by
    rw [hsum, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun c _ ↦ by rw [hFe, hGe]
  have e2 : ∑ ρ, F ρ = C * ∑ a, F (e.symm (a, c₀)) := by
    rw [hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Finset.sum_congr rfl fun c _ ↦ hFe a c, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  have e3 : ∑ ρ, G ρ = A * ∑ c, G (e.symm (a₀, c)) := by
    rw [hsum, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [Finset.sum_congr rfl fun a _ ↦ hGe a c, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  unfold unifAvg
  rw [e1, e2, e3, hcard]
  field_simp

/-- **One coordinate of a uniform function is uniform**: `E[h(ρ γ)] = E_π[h π]`. -/
theorem unifAvg_eval {Γ P : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype P] (γ : Γ)
    (h : P → ℝ) : unifAvg (fun ρ : Γ → P ↦ h (ρ γ)) = unifAvg h := by
  set e := Equiv.funSplitAt γ P with he
  have hs : ∑ ρ : Γ → P, h (ρ γ) = ∑ q : P × ({j // j ≠ γ} → P), h q.1 :=
    Fintype.sum_equiv e _ _ fun ρ ↦ rfl
  have hcard : (Fintype.card (Γ → P) : ℝ) =
      (Fintype.card P : ℝ) * (Fintype.card ({j // j ≠ γ} → P) : ℝ) := by
    rw [Fintype.card_congr e, Fintype.card_prod, Nat.cast_mul]
  unfold unifAvg
  rw [hs, Fintype.sum_prod_type, hcard]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  rcases isEmpty_or_nonempty ({j // j ≠ γ} → P) with hR | hR
  · rcases isEmpty_or_nonempty P with hP | hP
    · simp [Finset.univ_eq_empty]
    · exact absurd hR (not_isEmpty_of_nonempty _)
  · have : (Fintype.card ({j // j ≠ γ} → P) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    rw [mul_inv]
    field_simp

/-- **The average of a product of functions of distinct coordinates** is the product of their
averages (complex-valued). -/
theorem unifAvg_prod {Γ P : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype P] (g : Γ → P → ℂ) :
    unifAvg (fun ρ : Γ → P ↦ ∏ γ, g γ (ρ γ)) = ∏ γ, unifAvg (g γ) := by
  unfold unifAvg
  rw [Finset.prod_mul_distrib, ← Fintype.prod_sum, Finset.prod_const, Finset.card_univ,
    Fintype.card_fun, Nat.cast_pow, inv_pow]

/-- **One coordinate is independent of functions of the others**:
`E[h(ρ γ) G(ρ)] = E_π[h π] E[G]` when `G` does not depend on coordinate `γ`. -/
theorem unifAvg_mul_eval_of_forall_ne {Γ P : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype P]
    [Nonempty P] (γ : Γ) (h : P → ℝ) {G : (Γ → P) → ℝ}
    (hG : ∀ ρ ρ' : Γ → P, (∀ γ', ¬ γ' = γ → ρ γ' = ρ' γ') → G ρ = G ρ') :
    unifAvg (fun ρ ↦ h (ρ γ) * G ρ) = unifAvg h * unifAvg G := by
  rw [unifAvg_mul_of_disjoint (fun γ' ↦ γ' = γ) (F := fun ρ ↦ h (ρ γ))
    (fun ρ ρ' hρ ↦ by rw [hρ γ rfl]) hG, unifAvg_eval]

/-- A sum of terms of coordinates other than `γ` does not depend on coordinate `γ`. -/
theorem sum_eval_congr {Γ P ι : Type*} {J : Finset ι} {ν : ι → Γ} {γ : Γ}
    (hJ : ∀ j ∈ J, ν j ≠ γ) (X : ι → P → ℝ) (ρ ρ' : Γ → P)
    (h : ∀ γ', ¬ γ' = γ → ρ γ' = ρ' γ') :
    ∑ j ∈ J, X j (ρ (ν j)) = ∑ j ∈ J, X j (ρ' (ν j)) :=
  Finset.sum_congr rfl fun j hj ↦ by rw [h _ (hJ j hj)]

/-- The average of a sum of coordinate terms is the sum of their averages. -/
theorem unifAvg_sum_eval {Γ P ι : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype P]
    (J : Finset ι) (ν : ι → Γ) (X : ι → P → ℝ) :
    unifAvg (fun ρ : Γ → P ↦ ∑ j ∈ J, X j (ρ (ν j))) = ∑ j ∈ J, unifAvg (X j) := by
  rw [unifAvg_sum]
  exact Finset.sum_congr rfl fun j _ ↦ unifAvg_eval (ν j) (X j)

/-- Injectivity on `insert j₀ J` separates `ν j₀` from `ν '' J`. -/
theorem ne_of_injOn_insert {Γ ι : Type*} [DecidableEq ι] {J : Finset ι} {j₀ : ι} {ν : ι → Γ}
    (hν : Set.InjOn ν ↑(insert j₀ J)) (hj₀ : j₀ ∉ J) : ∀ j ∈ J, ν j ≠ ν j₀ := by
  intro j hj heq
  have := hν (Finset.mem_coe.2 (Finset.mem_insert_of_mem hj))
    (Finset.mem_coe.2 (Finset.mem_insert_self j₀ J)) heq
  rw [this] at hj
  exact hj₀ hj

/-- Injectivity on `insert j₀ J` gives injectivity on `J`. -/
theorem injOn_of_insert {Γ ι : Type*} [DecidableEq ι] {J : Finset ι} {j₀ : ι} {ν : ι → Γ}
    (hν : Set.InjOn ν ↑(insert j₀ J)) : Set.InjOn ν ↑J :=
  hν.mono fun _ hj ↦ Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hj))

/-- **Second moment of a sum of centred terms of distinct coordinates**:
`E[(Σ_{j ∈ J} X_j(ρ(ν j)))²] = Σ_{j ∈ J} E_π[X_j²]` when `ν` is injective on `J`. -/
theorem unifAvg_sq_sum_eq {Γ P ι : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype P] [Nonempty P]
    {J : Finset ι} {ν : ι → Γ} (hν : Set.InjOn ν ↑J) {X : ι → P → ℝ}
    (h0 : ∀ j ∈ J, unifAvg (X j) = 0) :
    unifAvg (fun ρ : Γ → P ↦ (∑ j ∈ J, X j (ρ (ν j))) ^ 2) =
      ∑ j ∈ J, unifAvg (fun pm ↦ X j pm ^ 2) := by
  classical
  induction J using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      rw [show (fun _ : Γ → P ↦ (0 : ℝ) ^ 2) = fun _ ↦ 0 from funext fun _ ↦ by ring,
        unifAvg_const]
  | insert j₀ J hj₀ ih =>
      have hne := ne_of_injOn_insert hν hj₀
      have hS0 : ∀ j ∈ J, unifAvg (X j) = 0 := fun j hj ↦ h0 j (Finset.mem_insert_of_mem hj)
      have hX0 := h0 j₀ (Finset.mem_insert_self j₀ J)
      rw [Finset.sum_insert hj₀]
      simp only [Finset.sum_insert hj₀]
      have e : (fun ρ : Γ → P ↦ (X j₀ (ρ (ν j₀)) + ∑ j ∈ J, X j (ρ (ν j))) ^ 2) =
          fun ρ ↦ (X j₀ (ρ (ν j₀)) ^ 2 + 2 * (X j₀ (ρ (ν j₀)) * ∑ j ∈ J, X j (ρ (ν j)))) +
            (∑ j ∈ J, X j (ρ (ν j))) ^ 2 := funext fun ρ ↦ by ring
      rw [e, unifAvg_add, unifAvg_add, unifAvg_const_mul,
        unifAvg_mul_eval_of_forall_ne (ν j₀) (X j₀) (sum_eval_congr hne X), hX0, zero_mul,
        mul_zero, add_zero, ih (injOn_of_insert hν) hS0,
        unifAvg_eval (ν j₀) (fun pm ↦ X j₀ pm ^ 2)]

/-- **Fourth moment of a sum of centred bounded terms of distinct coordinates**:
`E[(Σ_{j ∈ J} X_j(ρ(ν j)))⁴] ≤ 3 (Σ_{j ∈ J} β_j²)²` when `|X_j| ≤ β_j` and `ν` is injective
on `J`. -/
theorem unifAvg_pow_four_sum_le {Γ P ι : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype P]
    [Nonempty P] {J : Finset ι} {ν : ι → Γ} (hν : Set.InjOn ν ↑J) {X : ι → P → ℝ}
    (h0 : ∀ j ∈ J, unifAvg (X j) = 0) {β : ι → ℝ} (hβ : ∀ j ∈ J, ∀ pm, |X j pm| ≤ β j) :
    unifAvg (fun ρ : Γ → P ↦ (∑ j ∈ J, X j (ρ (ν j))) ^ 4) ≤ 3 * (∑ j ∈ J, β j ^ 2) ^ 2 := by
  classical
  obtain ⟨pm₀⟩ := ‹Nonempty P›
  induction J using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      rw [show (fun _ : Γ → P ↦ (0 : ℝ) ^ 4) = fun _ ↦ 0 from funext fun _ ↦ by ring,
        unifAvg_const]
      norm_num
  | insert j₀ J hj₀ ih =>
      have hne := ne_of_injOn_insert hν hj₀
      have hνJ := injOn_of_insert hν
      have hS0 : ∀ j ∈ J, unifAvg (X j) = 0 := fun j hj ↦ h0 j (Finset.mem_insert_of_mem hj)
      have hβJ : ∀ j ∈ J, ∀ pm, |X j pm| ≤ β j := fun j hj ↦ hβ j (Finset.mem_insert_of_mem hj)
      have hX0 := h0 j₀ (Finset.mem_insert_self j₀ J)
      have hβ0 := hβ j₀ (Finset.mem_insert_self j₀ J)
      set S : (Γ → P) → ℝ := fun ρ ↦ ∑ j ∈ J, X j (ρ (ν j)) with hS
      set a : (Γ → P) → ℝ := fun ρ ↦ X j₀ (ρ (ν j₀)) with ha
      set B := ∑ j ∈ J, β j ^ 2 with hB
      have hcong : ∀ k : ℕ, ∀ ρ ρ' : Γ → P, (∀ γ', ¬ γ' = ν j₀ → ρ γ' = ρ' γ') →
          S ρ ^ k = S ρ' ^ k := fun k ρ ρ' h ↦ by
        change (∑ j ∈ J, X j (ρ (ν j))) ^ k = (∑ j ∈ J, X j (ρ' (ν j))) ^ k
        rw [sum_eval_congr hne X ρ ρ' h]
      have hind : ∀ k l : ℕ, unifAvg (fun ρ ↦ a ρ ^ k * S ρ ^ l) =
          unifAvg (fun pm ↦ X j₀ pm ^ k) * unifAvg (fun ρ ↦ S ρ ^ l) := fun k l ↦
        unifAvg_mul_eval_of_forall_ne (ν j₀) (fun pm ↦ X j₀ pm ^ k) (hcong l)
      have hS1 : unifAvg S = 0 := by
        rw [hS, unifAvg_sum_eval, Finset.sum_eq_zero hS0]
      have hS2 : unifAvg (fun ρ ↦ S ρ ^ 2) ≤ B := by
        rw [hS, unifAvg_sq_sum_eq hνJ hS0, hB]
        refine Finset.sum_le_sum fun j hj ↦ ?_
        refine (unifAvg_mono fun pm ↦ ?_).trans (le_of_eq (unifAvg_const _))
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hβJ j hj pm) 2
      have hβ0nn : 0 ≤ β j₀ := (abs_nonneg _).trans (hβ0 pm₀)
      have hB0 : 0 ≤ B := Finset.sum_nonneg fun j _ ↦ sq_nonneg _
      have ha2 : unifAvg (fun pm ↦ X j₀ pm ^ 2) ≤ β j₀ ^ 2 := by
        refine (unifAvg_mono fun pm ↦ ?_).trans (le_of_eq (unifAvg_const _))
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hβ0 pm) 2
      have ha4 : unifAvg (fun pm ↦ X j₀ pm ^ 4) ≤ β j₀ ^ 4 := by
        refine (unifAvg_mono fun pm ↦ ?_).trans (le_of_eq (unifAvg_const _))
        rw [show X j₀ pm ^ 4 = |X j₀ pm| ^ 4 by rw [pow_abs, abs_of_nonneg (by positivity)]]
        exact pow_le_pow_left₀ (abs_nonneg _) (hβ0 pm) 4
      have ha2nn : 0 ≤ unifAvg (fun pm ↦ X j₀ pm ^ 2) := unifAvg_nonneg fun pm ↦ sq_nonneg _
      have hS2nn : 0 ≤ unifAvg (fun ρ ↦ S ρ ^ 2) := unifAvg_nonneg fun ρ ↦ sq_nonneg _
      have hS4 := ih hνJ hS0 hβJ
      rw [Finset.sum_insert hj₀]
      simp only [Finset.sum_insert hj₀]
      have e : (fun ρ : Γ → P ↦ (X j₀ (ρ (ν j₀)) + ∑ j ∈ J, X j (ρ (ν j))) ^ 4) =
          fun ρ ↦ (((a ρ ^ 4 * S ρ ^ 0 + 4 * (a ρ ^ 3 * S ρ ^ 1)) +
            6 * (a ρ ^ 2 * S ρ ^ 2)) + 4 * (a ρ ^ 1 * S ρ ^ 3)) + S ρ ^ 4 :=
        funext fun ρ ↦ by rw [ha, hS]; ring
      rw [e, unifAvg_add, unifAvg_add, unifAvg_add, unifAvg_add, unifAvg_const_mul,
        unifAvg_const_mul, unifAvg_const_mul, hind, hind, hind, hind]
      have h1 : unifAvg (fun ρ ↦ S ρ ^ 1) = 0 := by simpa only [pow_one] using hS1
      have h0' : unifAvg (fun pm ↦ X j₀ pm ^ 1) = 0 := by simpa only [pow_one] using hX0
      have hc0 : unifAvg (fun ρ ↦ S ρ ^ 0) = 1 := by
        simp only [pow_zero]
        exact unifAvg_const 1
      rw [h1, h0', hc0]
      have hS4' : unifAvg (fun ρ ↦ S ρ ^ 4) ≤ 3 * B ^ 2 := hS4
      have hm : unifAvg (fun pm ↦ X j₀ pm ^ 2) * unifAvg (fun ρ ↦ S ρ ^ 2) ≤ β j₀ ^ 2 * B :=
        mul_le_mul ha2 hS2 hS2nn (sq_nonneg _)
      nlinarith [sq_nonneg (β j₀), pow_nonneg hβ0nn 4, mul_nonneg (sq_nonneg (β j₀)) hB0]

/-- **Under a uniform permutation each point has a uniform image**:
`#α · Σ_π g(π c) = #Perm(α) · Σ_a g a`. -/
theorem sum_perm_apply {α : Type*} [Fintype α] [DecidableEq α] (g : α → ℝ) (c : α) :
    (Fintype.card α : ℝ) * ∑ pm : Equiv.Perm α, g (pm c) =
      (Fintype.card (Equiv.Perm α) : ℝ) * ∑ a, g a := by
  have hT : ∀ x y : α, ∑ pm : Equiv.Perm α, g (pm x) = ∑ pm : Equiv.Perm α, g (pm y) :=
    fun x y ↦ Fintype.sum_equiv (Equiv.mulRight (Equiv.swap x y)) _ _ fun pm ↦ by
      simp [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  calc (Fintype.card α : ℝ) * ∑ pm : Equiv.Perm α, g (pm c)
      = ∑ x : α, ∑ pm : Equiv.Perm α, g (pm x) := by
        rw [Finset.sum_congr rfl fun x _ ↦ hT x c, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
    _ = ∑ pm : Equiv.Perm α, ∑ x : α, g (pm x) := Finset.sum_comm
    _ = ∑ pm : Equiv.Perm α, ∑ a, g a := Finset.sum_congr rfl fun pm _ ↦ Equiv.sum_comp pm g
    _ = (Fintype.card (Equiv.Perm α) : ℝ) * ∑ a, g a := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The norm of a complex average is at most the average of the norms. -/
theorem norm_unifAvg_le {α : Type*} [Fintype α] (F : α → ℂ) :
    ‖unifAvg F‖ ≤ unifAvg fun a ↦ ‖F a‖ := by
  unfold unifAvg
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.2 (Nat.cast_nonneg _))

/-- Complex averages are additive under subtraction. -/
theorem unifAvg_sub_complex {α : Type*} [Fintype α] (F G : α → ℂ) :
    unifAvg (fun a ↦ F a - G a) = unifAvg F - unifAvg G := by
  unfold unifAvg
  rw [Finset.sum_sub_distrib, mul_sub]

/-- The average of a complex constant. -/
theorem unifAvg_const_complex {α : Type*} [Fintype α] [Nonempty α] (c : ℂ) :
    unifAvg (fun _ : α ↦ c) = c := by
  unfold unifAvg
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card α : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  field_simp

/-- The complex average of real values is the real average. -/
theorem unifAvg_ofReal {α : Type*} [Fintype α] (F : α → ℝ) :
    unifAvg (fun a ↦ (F a : ℂ)) = ((unifAvg F : ℝ) : ℂ) := by
  unfold unifAvg
  push_cast
  rfl

/-- **The characteristic function of a bounded centred variable on a finite uniform space**:
if `E X = 0`, `|X| ≤ δ` and `|t| δ ≤ 1`, then
`‖E e^{itX} - (1 - t² E[X²]/2)‖ ≤ |t|³ δ E[X²]`. -/
theorem norm_unifAvg_cexp_sub_le {P : Type*} [Fintype P] [Nonempty P] {X : P → ℝ}
    (h0 : unifAvg X = 0) {δ : ℝ} (hX : ∀ pm, |X pm| ≤ δ) {t : ℝ} (ht : |t| * δ ≤ 1) :
    ‖unifAvg (fun pm ↦ cexp (((t * X pm : ℝ) : ℂ) * I)) -
        (((1 - t ^ 2 * unifAvg (fun pm ↦ X pm ^ 2) / 2 : ℝ)) : ℂ)‖ ≤
      |t| ^ 3 * δ * unifAvg (fun pm ↦ X pm ^ 2) := by
  set q : P → ℂ := fun pm ↦ (((1 - (t * X pm) ^ 2 / 2 : ℝ)) : ℂ) + ((t * X pm : ℝ) : ℂ) * I
    with hq
  have hqa : unifAvg q = (((1 - t ^ 2 * unifAvg (fun pm ↦ X pm ^ 2) / 2 : ℝ)) : ℂ) := by
    have e1 : q = fun pm ↦ (((1 - t ^ 2 / 2 * X pm ^ 2 : ℝ)) : ℂ) + ((t * X pm : ℝ) : ℂ) * I :=
      funext fun pm ↦ by rw [hq]; push_cast; ring
    have e2 : unifAvg (fun pm ↦ (((1 - t ^ 2 / 2 * X pm ^ 2 : ℝ)) : ℂ)) =
        (((1 - t ^ 2 * unifAvg (fun pm ↦ X pm ^ 2) / 2 : ℝ)) : ℂ) := by
      rw [unifAvg_ofReal]
      congr 1
      rw [show (fun pm ↦ 1 - t ^ 2 / 2 * X pm ^ 2) = fun pm ↦ 1 + (-(t ^ 2 / 2)) * X pm ^ 2 from
        funext fun pm ↦ by ring, unifAvg_add, unifAvg_const, unifAvg_const_mul]
      ring
    have e3 : unifAvg (fun pm ↦ ((t * X pm : ℝ) : ℂ) * I) = 0 := by
      have : unifAvg (fun pm ↦ ((t * X pm : ℝ) : ℂ) * I) =
          unifAvg (fun pm ↦ ((t * X pm : ℝ) : ℂ)) * I := by
        unfold unifAvg
        rw [← Finset.sum_mul, mul_assoc]
      rw [this, unifAvg_ofReal, unifAvg_const_mul, h0, mul_zero, Complex.ofReal_zero, zero_mul]
    rw [e1]
    unfold unifAvg at e2 e3 ⊢
    rw [Finset.sum_add_distrib, mul_add, e2, e3, add_zero]
  rw [← hqa, ← unifAvg_sub_complex]
  refine (norm_unifAvg_le _).trans ?_
  rw [← unifAvg_const_mul]
  refine unifAvg_mono fun pm ↦ ?_
  have hy : |t * X pm| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hX pm) (abs_nonneg t)).trans ht
  refine (norm_cexp_mul_I_sub_le hy).trans ?_
  have h3 : |X pm| ^ 3 = |X pm| * X pm ^ 2 := by
    rw [← sq_abs (X pm)]
    ring
  rw [abs_mul, mul_pow, h3]
  calc |t| ^ 3 * (|X pm| * X pm ^ 2) ≤ |t| ^ 3 * (δ * X pm ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hX pm) (sq_nonneg _))
          (by positivity)
    _ = |t| ^ 3 * δ * X pm ^ 2 := by ring

/-- `|e^{-x} - e^{-y}| ≤ |x - y|` for `x, y ≥ 0`. -/
theorem abs_exp_neg_sub_exp_neg_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.exp (-x) - Real.exp (-y)| ≤ |x - y| := by
  have key : ∀ x y : ℝ, 0 ≤ x → x ≤ y → |Real.exp (-x) - Real.exp (-y)| ≤ |x - y| := by
    intro x y hx hxy
    have h1 : Real.exp (-y) ≤ Real.exp (-x) := Real.exp_le_exp.2 (by linarith)
    have h2 : Real.exp (-x) - Real.exp (-y) = Real.exp (-x) * (1 - Real.exp (-(y - x))) := by
      rw [mul_sub, mul_one, ← Real.exp_add]
      ring_nf
    have h3 : 1 - Real.exp (-(y - x)) ≤ y - x := by
      have := Real.add_one_le_exp (-(y - x))
      linarith
    have h4 : 0 ≤ 1 - Real.exp (-(y - x)) := by
      have : Real.exp (-(y - x)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      linarith
    have h5 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith), h2]
    calc Real.exp (-x) * (1 - Real.exp (-(y - x))) ≤ 1 * (y - x) :=
          mul_le_mul h5 h3 h4 zero_le_one
      _ = -(x - y) := by ring
  rcases le_total x y with h | h
  · exact key x y hx h
  · rw [abs_sub_comm, abs_sub_comm x y]
    exact key y x hy h

/-- The average of `e^{ix}` over real `x` has norm at most `1`. -/
theorem norm_unifAvg_cexp_le_one {α : Type*} [Fintype α] [Nonempty α] (x : α → ℝ) :
    ‖unifAvg (fun a ↦ cexp ((x a : ℂ) * I))‖ ≤ 1 := by
  refine (norm_unifAvg_le _).trans ?_
  rw [show (fun a ↦ ‖cexp ((x a : ℂ) * I)‖) = fun _ ↦ (1 : ℝ) from
    funext fun a ↦ Complex.norm_exp_ofReal_mul_I _, unifAvg_const]

/-- **Cauchy–Schwarz for an average of finite sums**:
`(E_r Σ_γ F G)² ≤ (E_r Σ_γ F²)(E_r Σ_γ G²)`. -/
theorem sq_unifAvg_sum_mul_le {R Γ : Type*} [Fintype R] [Fintype Γ] (F G : R → Γ → ℝ) :
    (unifAvg fun r ↦ ∑ γ, F r γ * G r γ) ^ 2 ≤
      (unifAvg fun r ↦ ∑ γ, F r γ ^ 2) * unifAvg fun r ↦ ∑ γ, G r γ ^ 2 := by
  unfold unifAvg
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (R × Γ))
    (fun q ↦ F q.1 q.2) (fun q ↦ G q.1 q.2)
  simp only [Fintype.sum_prod_type] at h
  have hc : (0 : ℝ) ≤ ((Fintype.card R : ℝ)⁻¹) ^ 2 := sq_nonneg _
  calc ((Fintype.card R : ℝ)⁻¹ * ∑ r, ∑ γ, F r γ * G r γ) ^ 2
      = ((Fintype.card R : ℝ)⁻¹) ^ 2 * (∑ r, ∑ γ, F r γ * G r γ) ^ 2 := by ring
    _ ≤ ((Fintype.card R : ℝ)⁻¹) ^ 2 * ((∑ r, ∑ γ, F r γ ^ 2) * ∑ r, ∑ γ, G r γ ^ 2) :=
        mul_le_mul_of_nonneg_left h hc
    _ = _ := by ring

/-- **Conditional Lindeberg CLT on finite product spaces** (Lyapunov form). For each `m`, an
outer variable `r ∈ R m` (uniform) and a uniform `ρ : Γ m → P` (independent node
permutations), let `T = Σ_γ ξ m r γ (ρ γ)` with centred node terms (`E_π ξ = 0`) bounded by
`|ξ m r γ π| ≤ M m r γ`. Suppose the conditional variances `V(r) = Σ_γ E_π ξ²` satisfy
`E_r |V(r)/s_m² - 1| → 0`, that `E_r Σ_γ (M/s_m)²` stays bounded, and that
`E_r Σ_γ (M/s_m)⁴ → 0`. Then for `τ_m → t` the characteristic function `E e^{i τ_m T/s_m}`
tends to `e^{-t²/2}`. -/
theorem tendsto_unifAvg_cexp_nodeSum {R : ℕ → Type*} [∀ m, Fintype (R m)]
    [∀ m, Nonempty (R m)] {Γ : ℕ → Type*} [∀ m, Fintype (Γ m)] [∀ m, DecidableEq (Γ m)]
    {P : Type*} [Fintype P] [Nonempty P] (ξ : (m : ℕ) → R m → Γ m → P → ℝ)
    (hcent : ∀ m r γ, unifAvg (ξ m r γ) = 0) {s : ℕ → ℝ} (hs : ∀ᶠ m in atTop, 0 < s m)
    (hV : Tendsto (fun m ↦ unifAvg fun r ↦
      |(∑ γ, unifAvg fun pm ↦ ξ m r γ pm ^ 2) / s m ^ 2 - 1|) atTop (𝓝 0))
    {M : (m : ℕ) → R m → Γ m → ℝ} (hM : ∀ m r γ pm, |ξ m r γ pm| ≤ M m r γ) {C : ℝ}
    (hM2 : ∀ᶠ m in atTop, (unifAvg fun r ↦ ∑ γ, (M m r γ / s m) ^ 2) ≤ C)
    (hM4 : Tendsto (fun m ↦ unifAvg fun r ↦ ∑ γ, (M m r γ / s m) ^ 4) atTop (𝓝 0))
    {τ : ℕ → ℝ} {t : ℝ} (hτ : Tendsto τ atTop (𝓝 t)) :
    Tendsto (fun m ↦ unifAvg fun r ↦ unifAvg fun ρ : Γ m → P ↦
      cexp ((((τ m * ∑ γ, ξ m r γ (ρ γ)) / s m : ℝ) : ℂ) * I)) atTop
      (𝓝 ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ)) := by
  obtain ⟨pm₀⟩ := ‹Nonempty P›
  set Vp : (m : ℕ) → R m → ℝ := fun m r ↦ (∑ γ, unifAvg fun pm ↦ ξ m r γ pm ^ 2) / s m ^ 2
    with hVp
  have hM0 : ∀ m r γ, 0 ≤ M m r γ := fun m r γ ↦ (abs_nonneg _).trans (hM m r γ pm₀)
  have hVp0 : ∀ m r, 0 ≤ Vp m r := fun m r ↦
    div_nonneg (Finset.sum_nonneg fun γ _ ↦ unifAvg_nonneg fun pm ↦ sq_nonneg _) (sq_nonneg _)
  -- the bound for one outer value `r`
  have hpt : ∀ m, 0 < s m → ∀ r,
      ‖unifAvg (fun ρ : Γ m → P ↦ cexp ((((τ m * ∑ γ, ξ m r γ (ρ γ)) / s m : ℝ) : ℂ) * I)) -
        ((Real.exp (-(τ m ^ 2 / 2)) : ℝ) : ℂ)‖ ≤
        |τ m| ^ 3 * ∑ γ, (M m r γ / s m) ^ 3 + 9 / 4 * τ m ^ 4 * ∑ γ, (M m r γ / s m) ^ 4 +
          τ m ^ 2 / 2 * |Vp m r - 1| := by
    intro m hsm r
    set x : Γ m → ℝ := fun γ ↦ |τ m| * (M m r γ / s m) with hx
    have hx0 : ∀ γ, 0 ≤ x γ := fun γ ↦ mul_nonneg (abs_nonneg _) (div_nonneg (hM0 m r γ) hsm.le)
    have h3 : ∑ γ, x γ ^ 3 = |τ m| ^ 3 * ∑ γ, (M m r γ / s m) ^ 3 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun γ _ ↦ by rw [hx]; ring
    have h4 : ∑ γ, x γ ^ 4 = τ m ^ 4 * ∑ γ, (M m r γ / s m) ^ 4 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun γ _ ↦ ?_
      rw [hx, mul_pow, show |τ m| ^ 4 = τ m ^ 4 by rw [pow_abs, abs_of_nonneg (by positivity)]]
    have hS3 : 0 ≤ ∑ γ, x γ ^ 3 := Finset.sum_nonneg fun γ _ ↦ pow_nonneg (hx0 γ) 3
    have hS4 : 0 ≤ ∑ γ, x γ ^ 4 := Finset.sum_nonneg fun γ _ ↦ pow_nonneg (hx0 γ) 4
    have hgauss0 : 0 ≤ τ m ^ 2 / 2 * |Vp m r - 1| := by positivity
    rw [← h3, show 9 / 4 * τ m ^ 4 * ∑ γ, (M m r γ / s m) ^ 4 = 9 / 4 * ∑ γ, x γ ^ 4 by
      rw [h4]; ring]
    by_cases hgood : ∀ γ, x γ ≤ 1
    · set X : Γ m → P → ℝ := fun γ pm ↦ ξ m r γ pm / s m with hX
      have hX0 : ∀ γ, unifAvg (X γ) = 0 := fun γ ↦ by
        change unifAvg (fun pm ↦ ξ m r γ pm / s m) = 0
        rw [show (fun pm ↦ ξ m r γ pm / s m) = fun pm ↦ (s m)⁻¹ * ξ m r γ pm from
          funext fun pm ↦ by ring, unifAvg_const_mul, hcent, mul_zero]
      have hXb : ∀ γ pm, |X γ pm| ≤ M m r γ / s m := fun γ pm ↦ by
        change |ξ m r γ pm / s m| ≤ M m r γ / s m
        rw [abs_div, abs_of_pos hsm]
        exact div_le_div_of_nonneg_right (hM m r γ pm) hsm.le
      have hτδ : ∀ γ, |τ m| * (M m r γ / s m) ≤ 1 := hgood
      have hfac : unifAvg (fun ρ : Γ m → P ↦
          cexp ((((τ m * ∑ γ, ξ m r γ (ρ γ)) / s m : ℝ) : ℂ) * I)) =
          ∏ γ, unifAvg (fun pm ↦ cexp (((τ m * X γ pm : ℝ) : ℂ) * I)) := by
        rw [← unifAvg_prod]
        congr 1
        funext ρ
        rw [← Complex.exp_sum]
        congr 1
        have e : ((τ m * ∑ γ, ξ m r γ (ρ γ)) / s m : ℝ) = ∑ γ, τ m * X γ (ρ γ) := by
          rw [Finset.mul_sum, Finset.sum_div]
          exact Finset.sum_congr rfl fun γ _ ↦ by rw [hX]; ring
        rw [e, Complex.ofReal_sum, Finset.sum_mul]
      set v : Γ m → ℝ := fun γ ↦ unifAvg (fun pm ↦ X γ pm ^ 2) with hv
      set a : Γ m → ℝ := fun γ ↦ τ m ^ 2 * v γ / 2 with ha
      have hvs : ∀ γ, v γ = (unifAvg fun pm ↦ ξ m r γ pm ^ 2) / s m ^ 2 := fun γ ↦ by
        change unifAvg (fun pm ↦ (ξ m r γ pm / s m) ^ 2) = _
        rw [show (fun pm ↦ (ξ m r γ pm / s m) ^ 2) =
          fun pm ↦ (s m ^ 2)⁻¹ * ξ m r γ pm ^ 2 from funext fun pm ↦ by ring, unifAvg_const_mul]
        ring
      have hVsum : ∑ γ, v γ = Vp m r := by
        change ∑ γ, v γ = (∑ γ, unifAvg fun pm ↦ ξ m r γ pm ^ 2) / s m ^ 2
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun γ _ ↦ hvs γ
      have hv0 : ∀ γ, 0 ≤ v γ := fun γ ↦ unifAvg_nonneg fun pm ↦ sq_nonneg _
      have hvδ : ∀ γ, v γ ≤ (M m r γ / s m) ^ 2 := fun γ ↦ by
        refine (unifAvg_mono fun pm ↦ ?_).trans (le_of_eq (unifAvg_const _))
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hXb γ pm) 2
      have ha0 : ∀ γ, 0 ≤ a γ := fun γ ↦ by
        rw [ha]
        have := hv0 γ
        positivity
      have hax : ∀ γ, a γ ≤ x γ ^ 2 / 2 := fun γ ↦ by
        rw [ha, hx, mul_pow, sq_abs]
        have := mul_le_mul_of_nonneg_left (hvδ γ) (sq_nonneg (τ m))
        linarith
      have hx1 : ∀ γ, x γ ^ 2 ≤ 1 := fun γ ↦ by
        have := hgood γ
        have := hx0 γ
        nlinarith
      have ha1 : ∀ γ, a γ ≤ 1 := fun γ ↦ by linarith [hax γ, hx1 γ]
      have hterm : ∀ γ, ‖unifAvg (fun pm ↦ cexp (((τ m * X γ pm : ℝ) : ℂ) * I)) -
          ((Real.exp (-a γ) : ℝ) : ℂ)‖ ≤ x γ ^ 3 + x γ ^ 4 / 4 := by
        intro γ
        have h1 := norm_unifAvg_cexp_sub_le (hX0 γ) (hXb γ) (hτδ γ)
        have h1' : |τ m| ^ 3 * (M m r γ / s m) * unifAvg (fun pm ↦ X γ pm ^ 2) ≤ x γ ^ 3 := by
          have hd0 : 0 ≤ M m r γ / s m := div_nonneg (hM0 m r γ) hsm.le
          calc |τ m| ^ 3 * (M m r γ / s m) * unifAvg (fun pm ↦ X γ pm ^ 2)
              ≤ |τ m| ^ 3 * (M m r γ / s m) * (M m r γ / s m) ^ 2 :=
                mul_le_mul_of_nonneg_left (hvδ γ) (by positivity)
            _ = x γ ^ 3 := by rw [hx]; ring
        have h2 : |Real.exp (-a γ) - 1 - (-a γ)| ≤ (-a γ) ^ 2 :=
          Real.abs_exp_sub_one_sub_id_le (by rw [abs_neg, abs_of_nonneg (ha0 γ)]; exact ha1 γ)
        have h3' : ‖(((1 - τ m ^ 2 * v γ / 2 : ℝ)) : ℂ) - ((Real.exp (-a γ) : ℝ) : ℂ)‖ ≤
            x γ ^ 4 / 4 := by
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          have heq : 1 - τ m ^ 2 * v γ / 2 - Real.exp (-a γ) =
              -(Real.exp (-a γ) - 1 - (-a γ)) := by
            rw [ha]
            ring
          rw [heq, abs_neg]
          refine h2.trans ?_
          rw [neg_sq]
          have := hax γ
          have := ha0 γ
          nlinarith
        calc ‖unifAvg (fun pm ↦ cexp (((τ m * X γ pm : ℝ) : ℂ) * I)) -
              ((Real.exp (-a γ) : ℝ) : ℂ)‖
            ≤ ‖unifAvg (fun pm ↦ cexp (((τ m * X γ pm : ℝ) : ℂ) * I)) -
                (((1 - τ m ^ 2 * v γ / 2 : ℝ)) : ℂ)‖ +
              ‖(((1 - τ m ^ 2 * v γ / 2 : ℝ)) : ℂ) - ((Real.exp (-a γ) : ℝ) : ℂ)‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ x γ ^ 3 + x γ ^ 4 / 4 := add_le_add (h1.trans h1') h3'
      have hprod : ‖∏ γ, unifAvg (fun pm ↦ cexp (((τ m * X γ pm : ℝ) : ℂ) * I)) -
          ∏ γ, ((Real.exp (-a γ) : ℝ) : ℂ)‖ ≤ ∑ γ, x γ ^ 3 + ∑ γ, x γ ^ 4 / 4 := by
        refine (norm_prod_sub_prod_le Finset.univ _ _
          (fun γ _ ↦ norm_unifAvg_cexp_le_one _) (fun γ _ ↦ ?_)).trans ?_
        · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
            Real.exp_le_one_iff]
          linarith [ha0 γ]
        refine (Finset.sum_le_sum fun γ _ ↦ hterm γ).trans (le_of_eq ?_)
        rw [Finset.sum_add_distrib]
      have hexp : ∏ γ, ((Real.exp (-a γ) : ℝ) : ℂ) =
          ((Real.exp (-(τ m ^ 2 * Vp m r / 2)) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_prod, ← Real.exp_sum, Finset.sum_neg_distrib]
        congr 3
        simp only [ha]
        rw [← Finset.sum_div, ← Finset.mul_sum, hVsum]
      have hgauss : ‖((Real.exp (-(τ m ^ 2 * Vp m r / 2)) : ℝ) : ℂ) -
          ((Real.exp (-(τ m ^ 2 / 2)) : ℝ) : ℂ)‖ ≤ τ m ^ 2 / 2 * |Vp m r - 1| := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        refine (abs_exp_neg_sub_exp_neg_le (by have := hVp0 m r; positivity)
          (by positivity)).trans (le_of_eq ?_)
        rw [show τ m ^ 2 * Vp m r / 2 - τ m ^ 2 / 2 = τ m ^ 2 / 2 * (Vp m r - 1) by ring,
          abs_mul, abs_of_nonneg (by positivity)]
      have h44 : ∑ γ, x γ ^ 4 / 4 ≤ 9 / 4 * ∑ γ, x γ ^ 4 := by
        rw [← Finset.sum_div]
        linarith
      rw [hfac]
      calc ‖∏ γ, unifAvg (fun pm ↦ cexp (((τ m * X γ pm : ℝ) : ℂ) * I)) -
            ((Real.exp (-(τ m ^ 2 / 2)) : ℝ) : ℂ)‖
          ≤ ‖∏ γ, unifAvg (fun pm ↦ cexp (((τ m * X γ pm : ℝ) : ℂ) * I)) -
              ∏ γ, ((Real.exp (-a γ) : ℝ) : ℂ)‖ +
            ‖∏ γ, ((Real.exp (-a γ) : ℝ) : ℂ) - ((Real.exp (-(τ m ^ 2 / 2)) : ℝ) : ℂ)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ (∑ γ, x γ ^ 3 + ∑ γ, x γ ^ 4 / 4) + τ m ^ 2 / 2 * |Vp m r - 1| :=
            add_le_add hprod (by rw [hexp]; exact hgauss)
        _ ≤ _ := by linarith
    · push Not at hgood
      obtain ⟨γ₁, hγ₁⟩ := hgood
      have h1 : 1 ≤ ∑ γ, x γ ^ 4 := by
        have h1' : 1 ≤ x γ₁ ^ 4 := one_le_pow₀ hγ₁.le
        exact h1'.trans (Finset.single_le_sum (fun γ _ ↦ pow_nonneg (hx0 γ) 4)
          (Finset.mem_univ γ₁))
      have hn1 := norm_unifAvg_cexp_le_one
        (fun ρ : Γ m → P ↦ ((τ m * ∑ γ, ξ m r γ (ρ γ)) / s m : ℝ))
      have hn2 : ‖((Real.exp (-(τ m ^ 2 / 2)) : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          Real.exp_le_one_iff]
        have := sq_nonneg (τ m)
        linarith
      calc _ ≤ ‖unifAvg (fun ρ : Γ m → P ↦
              cexp ((((τ m * ∑ γ, ξ m r γ (ρ γ)) / s m : ℝ) : ℂ) * I))‖ +
            ‖((Real.exp (-(τ m ^ 2 / 2)) : ℝ) : ℂ)‖ := norm_sub_le _ _
        _ ≤ _ := by linarith
  -- average over `r`
  set L2 : ℕ → ℝ := fun m ↦ unifAvg fun r ↦ ∑ γ, (M m r γ / s m) ^ 2 with hL2
  set L3 : ℕ → ℝ := fun m ↦ unifAvg fun r ↦ ∑ γ, (M m r γ / s m) ^ 3 with hL3
  set L4 : ℕ → ℝ := fun m ↦ unifAvg fun r ↦ ∑ γ, (M m r γ / s m) ^ 4 with hL4
  set Bd : ℕ → ℝ := fun m ↦ |τ m| ^ 3 * L3 m + 9 / 4 * τ m ^ 4 * L4 m +
    τ m ^ 2 / 2 * unifAvg (fun r ↦ |Vp m r - 1|) with hBd
  have havg : ∀ m, 0 < s m →
      ‖(unifAvg fun r ↦ unifAvg fun ρ : Γ m → P ↦
        cexp ((((τ m * ∑ γ, ξ m r γ (ρ γ)) / s m : ℝ) : ℂ) * I)) -
        ((Real.exp (-(τ m ^ 2 / 2)) : ℝ) : ℂ)‖ ≤ Bd m := by
    intro m hsm
    rw [← unifAvg_const_complex (α := R m) ((Real.exp (-(τ m ^ 2 / 2)) : ℝ) : ℂ),
      ← unifAvg_sub_complex]
    refine (norm_unifAvg_le _).trans ?_
    refine (unifAvg_mono fun r ↦ hpt m hsm r).trans (le_of_eq ?_)
    rw [unifAvg_add, unifAvg_add, unifAvg_const_mul, unifAvg_const_mul, unifAvg_const_mul]
  -- the third moments
  have hL3le : ∀ m, 0 < s m → L3 m ^ 2 ≤ L2 m * L4 m := by
    intro m hsm
    have h := sq_unifAvg_sum_mul_le (fun r γ ↦ M m r γ / s m) (fun r γ ↦ (M m r γ / s m) ^ 2)
    have e3 : L3 m = unifAvg fun r ↦ ∑ γ, M m r γ / s m * (M m r γ / s m) ^ 2 := by
      change (unifAvg fun r ↦ ∑ γ, (M m r γ / s m) ^ 3) = _
      congr 1
      funext r
      exact Finset.sum_congr rfl fun γ _ ↦ by ring
    have e4 : (unifAvg fun r ↦ ∑ γ, ((M m r γ / s m) ^ 2) ^ 2) = L4 m := by
      change _ = (unifAvg fun r ↦ ∑ γ, (M m r γ / s m) ^ 4)
      congr 1
      funext r
      exact Finset.sum_congr rfl fun γ _ ↦ by ring
    rw [e3, ← e4]
    exact h
  have hL0 : ∀ m, 0 < s m → 0 ≤ L3 m := fun m hsm ↦ unifAvg_nonneg fun r ↦
    Finset.sum_nonneg fun γ _ ↦ pow_nonneg (div_nonneg (hM0 m r γ) hsm.le) 3
  have hL4n : ∀ m, 0 ≤ L4 m := fun m ↦ unifAvg_nonneg fun r ↦
    Finset.sum_nonneg fun γ _ ↦ by positivity
  have hC0 : 0 ≤ C := by
    obtain ⟨m, hm⟩ := hM2.exists
    exact le_trans (unifAvg_nonneg fun r ↦ Finset.sum_nonneg fun γ _ ↦ sq_nonneg _) hm
  have hL3t : Tendsto L3 atTop (𝓝 0) := by
    have hsq : Tendsto (fun m ↦ Real.sqrt (C * L4 m)) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto _).comp (hM4.const_mul C)
      rwa [mul_zero, Real.sqrt_zero] at this
    refine squeeze_zero' ?_ ?_ hsq
    · filter_upwards [hs] with m hsm
      exact hL0 m hsm
    · filter_upwards [hs, hM2] with m hsm hm2
      refine Real.le_sqrt_of_sq_le ((hL3le m hsm).trans ?_)
      exact mul_le_mul_of_nonneg_right hm2 (hL4n m)
  have hBd0 : Tendsto Bd atTop (𝓝 0) := by
    have h := (((hτ.abs.pow 3).mul hL3t).add (((hτ.pow 4).const_mul (9 / 4)).mul hM4)).add
      (((hτ.pow 2).div_const 2).mul hV)
    simpa only [hBd, mul_zero, add_zero] using h
  have hgl : Tendsto (fun m ↦ ((Real.exp (-(τ m ^ 2 / 2)) : ℝ) : ℂ)) atTop
      (𝓝 ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ)) :=
    Tendsto.ofReal ((Real.continuous_exp.tendsto _).comp ((hτ.pow 2).div_const 2).neg)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  rw [tendsto_iff_norm_sub_tendsto_zero] at hgl
  refine squeeze_zero' (Eventually.of_forall fun m ↦ norm_nonneg _) ?_ (by
    simpa only [add_zero] using hBd0.add hgl)
  filter_upwards [hs] with m hsm
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add (havg m hsm) le_rfl)

end RQMCMarkov.OwenScrambling

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The product integrand on a scrambled `(0,m,2)`-net: node decomposition

Towards Loh's (2003) CLT for the non-additive integrand `f(x) = x₀ x₁` (post #2). Averaged
over the remainders, the scrambled-net estimator of `x₀ x₁` is `1/4 + S/n`, where
`S = Σ_i A₀(i) A₁(i)` and `A_j(i)` is the centred midpoint of the scrambled cell of point `i` in
coordinate `j`. Each `A_j` is a sum over the levels of the scramble of centred digits
(`scrDev`), digit `k` depending only on the level-`k` node of the tree of coordinate `j`. Given
the scramble `ρ₀` of coordinate `0`, `S` is a sum over the nodes `γ` of the tree of coordinate `1`
of terms `nodeTerm d ρ₀ γ (ρ₁ γ)`, each depending on a single node permutation and centred:
a sum of independent terms (`prodS_eq_sum_nodeTerm`, `unifAvg_nodeTerm`).

The weight of a node `γ` at level `k₁` is a sum over the points below `γ` of `A₀`. The net
property makes the levels of `A₀` above `m - k₁ - 1` cancel exactly (`sum_cdig_cellSet_eq_zero`),
and below that level distinct points use distinct nodes of the tree of coordinate `0`
(`eq_of_truncDigits_eq_cellSet`). So the weights are sums of independent centred terms of the
deep levels of `ρ₀` (`nodeW_eq_wwin`, `wwin_eq_sum`), with explicit second and fourth moment
bounds (`unifAvg_sq_wwin_le`, `unifAvg_pow_four_wwin_le`).

## Main results

* `cdig`, `sum_cdig`, `unifAvg_cdig`, `abs_cdig_le`: centred permuted digits.
* `mid_scramble`: the midpoint of a scrambled cell is `1/2 + scrDev ρ x`.
* `cellAvg_prodFn`, `sum_scrDev_net`, `integral_scrambledEstimate_prodFn`:
  `E[μ̂ | ρ] = 1/4 + S/n` for `x₀ x₁` and every `(0,m,2)`-net.
* `prodS_eq_sum_nodeTerm`, `unifAvg_nodeTerm`: the node decomposition of `S` given `ρ₀`.
* `card_agree_agree_net`, `sum_cdig_cellSet_eq_zero`, `eq_of_truncDigits_eq_cellSet`: the net
  combinatorics.
* `nodeW_eq_wwin`, `wwin_split`, `unifAvg_sq_wwin_le`, `unifAvg_pow_four_wwin_le`: the node
  weights as sums of independent terms of the deep levels, and their moments.
-/

namespace RQMCMarkov.OwenScrambling

open MeasureTheory ProbabilityTheory Finset Filter
open scoped Topology

variable {b : ℕ}

/-- The **centred digit** `π c - (b - 1)/2` of a digit `c` under a permutation `π`. -/
noncomputable def cdig (pm : Equiv.Perm (Fin b)) (c : Fin b) : ℝ :=
  ((pm c : ℕ) : ℝ) - ((b : ℝ) - 1) / 2

/-- `Σ_{c < b} c = b (b - 1)/2`. -/
theorem sum_fin_cast_eq (b : ℕ) : ∑ c : Fin b, ((c : ℕ) : ℝ) = b * (b - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ (i : ℝ)) b, sum_range_cast_id]

/-- The centred digits of a permutation sum to zero. -/
theorem sum_cdig (pm : Equiv.Perm (Fin b)) : ∑ c, cdig pm c = 0 := by
  unfold cdig
  rw [Finset.sum_sub_distrib, Equiv.sum_comp pm (fun c ↦ ((c : ℕ) : ℝ)), sum_fin_cast_eq,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **A uniformly permuted digit is centred**: `E_π[π c - (b-1)/2] = 0`. -/
theorem unifAvg_cdig (c : Fin b) : unifAvg (fun pm : Equiv.Perm (Fin b) ↦ cdig pm c) = 0 := by
  have h := sum_perm_apply (fun a : Fin b ↦ ((a : ℕ) : ℝ) - ((b : ℝ) - 1) / 2) c
  have hs : ∑ a : Fin b, (((a : ℕ) : ℝ) - ((b : ℝ) - 1) / 2) = 0 := sum_cdig (Equiv.refl _)
  rw [hs, mul_zero, Fintype.card_fin] at h
  have hb : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Fin.pos c).ne'
  have h0 : ∑ pm : Equiv.Perm (Fin b), cdig pm c = 0 := by
    rcases mul_eq_zero.1 h with h1 | h1
    · exact absurd h1 hb
    · exact h1
  unfold unifAvg
  rw [h0, mul_zero]

/-- `|π c - (b-1)/2| ≤ b/2`. -/
theorem abs_cdig_le (pm : Equiv.Perm (Fin b)) (c : Fin b) : |cdig pm c| ≤ (b : ℝ) / 2 := by
  unfold cdig
  have h1 : ((pm c : ℕ) : ℝ) + 1 ≤ b := by exact_mod_cast (pm c).isLt
  have h0 : (0 : ℝ) ≤ ((pm c : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [abs_le]
  constructor <;> linarith

/-- The weight `b^{-(k+1)}` of digit `k`. -/
noncomputable def digWt (b k : ℕ) : ℝ := ((b : ℝ) ^ (k + 1))⁻¹

/-- Digit weights are positive. -/
theorem digWt_pos (hb : 0 < b) (k : ℕ) : 0 < digWt b k :=
  inv_pos.2 (pow_pos (Nat.cast_pos.2 hb) _)

/-- **The centred midpoint of a scrambled cell**, digit by digit:
`scrDev ρ x = Σ_k (σ(x)_k - (b-1)/2) b^{-(k+1)}`, digit `k` of the scrambled string being
`ρ (k, x|k) (x k)`. -/
noncomputable def scrDev {m : ℕ} (ρ : Scramble b m) (x : Fin m → Fin b) : ℝ :=
  ∑ k : Fin m, cdig (ρ (k, truncDigits k x)) (x k) * digWt b k

/-- The midpoint of the first `r` digits, digit by digit. -/
theorem prefixVal_mid {D : ℕ} (hb : 0 < b) (x : Fin D → Fin b) (r : ℕ) :
    ((prefixVal x r : ℝ) + 1 / 2) / (b : ℝ) ^ r - 1 / 2 =
      ∑ k ∈ Finset.range r, ((digitAt x k : ℝ) - ((b : ℝ) - 1) / 2) * digWt b k := by
  have hb' : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hb.ne'
  induction r with
  | zero => simp [prefixVal]
  | succ r ih =>
      rw [Finset.sum_range_succ, ← ih]
      change (((b * prefixVal x r + digitAt x r : ℕ) : ℝ) + 1 / 2) / (b : ℝ) ^ (r + 1) - 1 / 2 =
        _
      unfold digWt
      push_cast
      field_simp
      ring

/-- **The midpoint of a scrambled cell** is `1/2 + scrDev ρ x`. -/
theorem mid_scramble (hb : 0 < b) {m : ℕ} (ρ : Scramble b m) (x : Fin m → Fin b) :
    ((cellVal (scramble ρ x) : ℝ) + 1 / 2) / (b : ℝ) ^ m = 1 / 2 + scrDev ρ x := by
  have h := prefixVal_mid hb (scramble ρ x) m
  have e : scrDev ρ x = ∑ k ∈ Finset.range m,
      ((digitAt (scramble ρ x) k : ℝ) - ((b : ℝ) - 1) / 2) * digWt b k := by
    rw [← Fin.sum_univ_eq_sum_range (fun k ↦ ((digitAt (scramble ρ x) k : ℝ) -
      ((b : ℝ) - 1) / 2) * digWt b k) m]
    unfold scrDev
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [digitAt_fin]
    rfl
  unfold cellVal
  rw [e, ← h]
  ring

/-- `∫ (cellVal x + w)/b^D dw = (cellVal x + 1/2)/b^D` over `w ~ U[0,1)`. -/
theorem integral_digitPoint {D : ℕ} (x : Fin D → Fin b) :
    ∫ w, digitPoint x w ∂uniformIco = ((cellVal x : ℝ) + 1 / 2) / (b : ℝ) ^ D := by
  have := isProbabilityMeasure_uniformIco
  have e : (fun w ↦ digitPoint x w) = fun w ↦ ((b : ℝ) ^ D)⁻¹ * ((cellVal x : ℝ) + w) :=
    funext fun w ↦ by unfold digitPoint; ring
  rw [e, integral_const_mul, integral_add (f := fun _ ↦ (cellVal x : ℝ)) (g := fun a ↦ a)
    (integrable_const _) (integrable_uniformIco_of_continuous (g := fun a ↦ a) continuous_id),
    integral_const, probReal_univ, one_smul, integral_id_uniformIco]
  ring

/-- **The cell average of `x₀ x₁`** is the product of the cell midpoints. -/
theorem cellAvg_prodFn {D : ℕ} (y : Fin 2 → Fin D → Fin b) :
    cellAvg prodFn y = (((cellVal (y 0) : ℝ) + 1 / 2) / (b : ℝ) ^ D) *
      (((cellVal (y 1) : ℝ) + 1 / 2) / (b : ℝ) ^ D) := by
  have := isProbabilityMeasure_uniformIco
  unfold cellAvg
  have e : (fun u : Fin 2 → ℝ ↦ prodFn (cellPoint y u)) =
      fun u ↦ digitPoint (y 0) (u 0) * digitPoint (y 1) (u 1) := rfl
  rw [e, ← integral_digitPoint, ← integral_digitPoint]
  exact integral_pi_eval_mul (ν := uniformIco)
    (measurable_digitPoint (y 0)).aestronglyMeasurable
    (measurable_digitPoint (y 1)).aestronglyMeasurable (by decide)

/-- `x₀ x₁` is measurable. -/
theorem measurable_prodFn : Measurable prodFn :=
  (measurable_pi_apply 0).mul (measurable_pi_apply 1)

/-- `x₀ x₁` is in `L²` of the cube. -/
theorem memLp_prodFn : MemLp prodFn 2 (uniformCube 2) := by
  have hU := isProbabilityMeasure_uniformCube 2
  refine MemLp.of_bound measurable_prodFn.aestronglyMeasurable 1 ?_
  filter_upwards [ae_mem_cube_uniformCube 2] with x hx
  rw [Real.norm_eq_abs, prodFn, abs_mul]
  have h0 : |x 0| ≤ 1 := abs_le.2 ⟨by linarith [(hx 0).1], (hx 0).2.le⟩
  have h1 : |x 1| ≤ 1 := abs_le.2 ⟨by linarith [(hx 1).1], (hx 1).2.le⟩
  nlinarith [abs_nonneg (x 0), abs_nonneg (x 1)]

/-- **The centred midpoints of a scrambled `(0,m,s)`-net sum to zero** in each coordinate (the
scrambled coordinate visits every cell once). -/
theorem sum_scrDev_net (hb : 0 < b) {m s : ℕ} {d : Fin (b ^ m) → Fin s → Fin m → Fin b}
    (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) (ρ : Fin s → Scramble b m)
    (j : Fin s) : ∑ i, scrDev (ρ j) (d i j) = 0 := by
  have hN : ((b ^ m : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.pow_pos hb).ne'
  set G : Fin (b ^ m) → ℝ := fun c ↦ ((c : ℕ) + 1 / 2) / (b : ℝ) ^ m - 1 / 2 with hG
  have e : ∀ i, scrDev (ρ j) (d i j) = G (cellFin hb (scramble (ρ j) (d i j))) := fun i ↦ by
    rw [hG]
    change _ = ((cellVal (scramble (ρ j) (d i j)) : ℝ) + 1 / 2) / (b : ℝ) ^ m - 1 / 2
    rw [mid_scramble hb]
    ring
  rw [Finset.sum_congr rfl fun i _ ↦ e i,
    (bijective_cellFin_scramble hb hnet ρ j).sum_comp G, hG]
  simp only
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib, sum_fin_cast_eq]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp
  ring

/-- `S = Σ_i A₀(i) A₁(i)`, the product of the centred scrambled midpoints. -/
noncomputable def prodS {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b)
    (ρ : Fin 2 → Scramble b m) : ℝ :=
  ∑ i, scrDev (ρ 0) (d i 0) * scrDev (ρ 1) (d i 1)

/-- **`E[μ̂ | ρ] = 1/4 + S/n` for `x₀ x₁`** on every scrambled `(0,m,2)`-net. -/
theorem integral_scrambledEstimate_prodFn (hb : 0 < b) {m : ℕ}
    {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    (ρ : Fin 2 → Scramble b m) :
    ∫ u, scrambledEstimate prodFn d ρ u ∂(remLaw 2 (b ^ m)) =
      1 / 4 + prodS d ρ / ((b ^ m : ℕ) : ℝ) := by
  have hN : ((b ^ m : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.pow_pos hb).ne'
  rw [integral_scrambledEstimate hb memLp_prodFn d ρ]
  have e : ∀ i, cellAvg prodFn (scrambleVec ρ (d i)) =
      (1 / 2 + scrDev (ρ 0) (d i 0)) * (1 / 2 + scrDev (ρ 1) (d i 1)) := fun i ↦ by
    rw [cellAvg_prodFn, ← mid_scramble hb, ← mid_scramble hb]
    rfl
  rw [Finset.sum_congr rfl fun i _ ↦ e i]
  have e2 : ∀ i, (1 / 2 + scrDev (ρ 0) (d i 0)) * (1 / 2 + scrDev (ρ 1) (d i 1)) =
      1 / 4 + scrDev (ρ 0) (d i 0) / 2 + scrDev (ρ 1) (d i 1) / 2 +
        scrDev (ρ 0) (d i 0) * scrDev (ρ 1) (d i 1) := fun i ↦ by ring
  rw [Finset.sum_congr rfl fun i _ ↦ e2 i, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.sum_div (f := fun i ↦ scrDev (ρ 0) (d i 0)),
    ← Finset.sum_div (f := fun i ↦ scrDev (ρ 1) (d i 1)), sum_scrDev_net hb hnet ρ 0,
    sum_scrDev_net hb hnet ρ 1]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold prodS
  field_simp
  ring

/-- The points below the node `γ = (k, t)` of the tree of coordinate `1`: those whose first `k`
digits in coordinate `1` are `t`. -/
def nodeSet {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b)
    (γ : Fin m × (Fin m → Option (Fin b))) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ truncDigits γ.1 (d i 1) = γ.2

/-- The points below the child `c` of the node `γ`: digit `γ.1` of coordinate `1` is `c`. -/
def cellSet {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b)
    (γ : Fin m × (Fin m → Option (Fin b))) (c : Fin b) : Finset (Fin n) :=
  (nodeSet d γ).filter fun i ↦ d i 1 γ.1 = c

/-- The **node weights** given `ρ₀`: `w_{γ,c} = Σ_{i below (γ, c)} A₀(i)`. -/
noncomputable def nodeW {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (ρ₀ : Scramble b m)
    (γ : Fin m × (Fin m → Option (Fin b))) (c : Fin b) : ℝ :=
  ∑ i ∈ cellSet d γ c, scrDev ρ₀ (d i 0)

/-- The **node term** of `S` given `ρ₀`, a function of the permutation `π` of the node `γ` of
the tree of coordinate `1`: `b^{-(k+1)} Σ_c (π c - (b-1)/2) w_{γ,c}`. -/
noncomputable def nodeTerm {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (ρ₀ : Scramble b m)
    (γ : Fin m × (Fin m → Option (Fin b))) (pm : Equiv.Perm (Fin b)) : ℝ :=
  digWt b γ.1 * ∑ c, cdig pm c * nodeW d ρ₀ γ c

/-- Regrouping a node term by points. -/
theorem sum_cdig_mul_nodeW {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (ρ₀ : Scramble b m)
    (γ : Fin m × (Fin m → Option (Fin b))) (pm : Equiv.Perm (Fin b)) :
    ∑ c, cdig pm c * nodeW d ρ₀ γ c =
      ∑ i ∈ nodeSet d γ, cdig pm (d i 1 γ.1) * scrDev ρ₀ (d i 0) := by
  unfold nodeW cellSet
  rw [← Finset.sum_fiberwise (nodeSet d γ) (fun i ↦ d i 1 γ.1)
    (fun i ↦ cdig pm (d i 1 γ.1) * scrDev ρ₀ (d i 0))]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [(Finset.mem_filter.1 hi).2]

/-- **Given `ρ₀`, `S` is a sum of node terms of `ρ₁`**: `S = Σ_γ nodeTerm d ρ₀ γ (ρ₁ γ)`, one
term for each node `γ` of the tree of coordinate `1`, depending only on its permutation. -/
theorem prodS_eq_sum_nodeTerm {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b)
    (ρ : Fin 2 → Scramble b m) : prodS d ρ = ∑ γ, nodeTerm d (ρ 0) γ (ρ 1 γ) := by
  symm
  calc ∑ γ, nodeTerm d (ρ 0) γ (ρ 1 γ)
      = ∑ γ : Fin m × (Fin m → Option (Fin b)), digWt b γ.1 *
          ∑ i ∈ nodeSet d γ, cdig (ρ 1 γ) (d i 1 γ.1) * scrDev (ρ 0) (d i 0) :=
        Finset.sum_congr rfl fun γ _ ↦ by unfold nodeTerm; rw [sum_cdig_mul_nodeW]
    _ = ∑ k : Fin m, ∑ t : Fin m → Option (Fin b), digWt b k *
          ∑ i ∈ nodeSet d (k, t), cdig (ρ 1 (k, t)) (d i 1 k) * scrDev (ρ 0) (d i 0) :=
        Fintype.sum_prod_type _
    _ = ∑ k : Fin m, digWt b k *
          ∑ i, cdig (ρ 1 (k, truncDigits k (d i 1))) (d i 1 k) * scrDev (ρ 0) (d i 0) := by
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [← Finset.mul_sum]
        congr 1
        rw [← Finset.sum_fiberwise Finset.univ (fun i ↦ truncDigits k (d i 1))
          (fun i ↦ cdig (ρ 1 (k, truncDigits k (d i 1))) (d i 1 k) * scrDev (ρ 0) (d i 0))]
        refine Finset.sum_congr rfl fun t _ ↦ Finset.sum_congr rfl fun i hi ↦ ?_
        rw [(Finset.mem_filter.1 hi).2]
    _ = prodS d ρ := by
        unfold prodS
        rw [Finset.sum_congr rfl fun k _ ↦ Finset.mul_sum _ _ _, Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [show scrDev (ρ 1) (d i 1) = ∑ k : Fin m,
          cdig (ρ 1 (k, truncDigits k (d i 1))) (d i 1 k) * digWt b k from rfl, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        ring

/-- **The node terms are centred** under a uniform permutation. -/
theorem unifAvg_nodeTerm {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (ρ₀ : Scramble b m)
    (γ : Fin m × (Fin m → Option (Fin b))) : unifAvg (nodeTerm d ρ₀ γ) = 0 := by
  unfold nodeTerm
  rw [unifAvg_const_mul, unifAvg_sum, Finset.sum_eq_zero, mul_zero]
  intro c _
  rw [show (fun pm : Equiv.Perm (Fin b) ↦ cdig pm c * nodeW d ρ₀ γ c) =
    fun pm ↦ nodeW d ρ₀ γ c * cdig pm c from funext fun pm ↦ mul_comm _ _, unifAvg_const_mul,
    unifAvg_cdig, mul_zero]

/-- **Points of a `(0,m,2)`-net in an elementary box with `r₀ + r₁ ≤ m`**, described by
prefixes `z₀, z₁`: exactly `b^{m - r₀ - r₁}`. -/
theorem card_agree_agree_net (hb : 0 < b) {m : ℕ} {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b}
    (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) {r₀ r₁ : ℕ} (hr : r₀ + r₁ ≤ m)
    (z₀ z₁ : Fin m → Fin b) :
    (Finset.univ.filter fun i ↦ Agree r₀ z₀ (d i 0) ∧ Agree r₁ z₁ (d i 1)).card =
      b ^ (m - r₀ - r₁) := by
  have hr0 : r₀ ≤ m := by omega
  have hr1 : r₁ ≤ m := by omega
  have h := card_box_net_of_le hb le_rfl hnet (r := ![r₀, r₁])
    (by rw [Fin.sum_univ_two]; simpa using hr) (a := ![prefixVal z₀ r₀, prefixVal z₁ r₁])
    (fun j ↦ by fin_cases j <;> simp [prefixVal_lt hb])
  rw [Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
  rw [show m - r₀ - r₁ = m - (r₀ + r₁) by omega, ← h]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.forall_fin_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [eq_comm, prefixVal_eq_iff_agree hb hr0, eq_comm (a := prefixVal (d i 1) r₁),
    prefixVal_eq_iff_agree hb hr1]

/-- Agreement with a string whose digit `k` is replaced by `e`. -/
theorem agree_update_succ_iff {m : ℕ} (x y : Fin m → Fin b) (k : Fin m) (e : Fin b) :
    Agree ((k : ℕ) + 1) (Function.update x k e) y ↔ Agree k x y ∧ y k = e := by
  rw [agree_succ_iff k.isLt]
  have hk : (⟨(k : ℕ), k.isLt⟩ : Fin m) = k := Fin.eta k _
  rw [hk, Function.update_self]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun l hl ↦ ?_, h2.symm⟩
    have := h1 l hl
    rwa [Function.update_of_ne (Fin.ne_of_val_ne (Nat.ne_of_lt hl))] at this
  · rintro ⟨h1, h2⟩
    refine ⟨fun l hl ↦ ?_, h2.symm⟩
    rw [Function.update_of_ne (Fin.ne_of_val_ne (Nat.ne_of_lt hl))]
    exact h1 l hl

/-- Agreement is symmetric (as an `iff`). -/
theorem agree_comm_iff {D r : ℕ} (x y : Fin D → Fin b) : Agree r x y ↔ Agree r y x :=
  ⟨agree_symm, agree_symm⟩

/-- **The shallow levels of `A₀` cancel below a node** (the net property): if
`k₀ + k₁ + 2 ≤ m`, the level-`k₀` centred digits of coordinate `0` sum to zero over the points
below any child of a level-`k₁` node of coordinate `1`, for every scramble `ρ₀`. -/
theorem sum_cdig_cellSet_eq_zero (hb : 0 < b) {m : ℕ} {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b}
    (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) {k₀ k₁ : Fin m}
    (hk : (k₀ : ℕ) + k₁ + 2 ≤ m) (t : Fin m → Option (Fin b)) (c : Fin b) (ρ₀ : Scramble b m) :
    ∑ i ∈ cellSet d (k₁, t) c, cdig (ρ₀ (k₀, truncDigits k₀ (d i 0))) (d i 0 k₀) = 0 := by
  classical
  rw [← Finset.sum_fiberwise (cellSet d (k₁, t) c) (fun i ↦ truncDigits k₀ (d i 0))]
  refine Finset.sum_eq_zero fun p _ ↦ ?_
  set G := (cellSet d (k₁, t) c).filter fun i ↦ truncDigits k₀ (d i 0) = p with hG
  rw [Finset.sum_congr rfl fun i hi ↦ by rw [(Finset.mem_filter.1 hi).2]]
  rcases G.eq_empty_or_nonempty with hG0 | ⟨i₁, hi₁⟩
  · rw [hG0, Finset.sum_empty]
  have hi₁' := hi₁
  simp only [hG, cellSet, nodeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi₁'
  have hcount : ∀ e : Fin b, (G.filter fun i ↦ d i 0 k₀ = e).card =
      b ^ (m - ((k₀ : ℕ) + 1) - ((k₁ : ℕ) + 1)) := by
    intro e
    rw [← card_agree_agree_net hb hnet (by omega) (Function.update (d i₁ 0) k₀ e) (d i₁ 1)]
    congr 1
    ext i
    simp only [hG, cellSet, nodeSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [agree_update_succ_iff, agree_succ_iff k₁.isLt, Fin.eta, ← hi₁'.1.1, ← hi₁'.1.2,
      ← hi₁'.2, truncDigits_eq_iff, truncDigits_eq_iff, agree_comm_iff (d i 1),
      agree_comm_iff (d i 0)]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      exact ⟨⟨h3, h4⟩, h1, h2.symm⟩
    · rintro ⟨⟨h3, h4⟩, h1, h2⟩
      exact ⟨⟨⟨h1, h2.symm⟩, h3⟩, h4⟩
  rw [← Finset.sum_fiberwise G (fun i ↦ d i 0 k₀)]
  calc ∑ e : Fin b, ∑ i ∈ G with d i 0 k₀ = e, cdig (ρ₀ (k₀, p)) (d i 0 k₀)
      = ∑ e : Fin b, ((b ^ (m - ((k₀ : ℕ) + 1) - ((k₁ : ℕ) + 1)) : ℕ) : ℝ) *
          cdig (ρ₀ (k₀, p)) e := by
        refine Finset.sum_congr rfl fun e _ ↦ ?_
        rw [Finset.sum_congr rfl fun i hi ↦ by rw [(Finset.mem_filter.1 hi).2],
          Finset.sum_const, hcount e, nsmul_eq_mul]
    _ = 0 := by rw [← Finset.mul_sum, sum_cdig, mul_zero]

/-- **Below a level-`k₁` node, distinct points use distinct deep nodes of coordinate `0`**: if
`k₀ + k₁ + 1 ≥ m`, two points below the same child of a level-`k₁` node with the same `k₀`-digit
prefix in coordinate `0` coincide. -/
theorem eq_of_truncDigits_eq_cellSet (hb : 0 < b) {m : ℕ}
    {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    {k₁ : Fin m} {t : Fin m → Option (Fin b)} {c : Fin b} {i i' : Fin (b ^ m)}
    (hi : i ∈ cellSet d (k₁, t) c) (hi' : i' ∈ cellSet d (k₁, t) c) {k₀ : Fin m}
    (hk : m ≤ (k₀ : ℕ) + k₁ + 1) (h : truncDigits k₀ (d i 0) = truncDigits k₀ (d i' 0)) :
    i = i' := by
  simp only [cellSet, nodeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
  have hc := card_agree_net_of_ge hb le_rfl hnet (r := ![(k₀ : ℕ), (k₁ : ℕ) + 1])
    (by rw [Fin.sum_univ_two]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]; omega) i
  have hmem : ∀ i'', Agree k₀ (d i 0) (d i'' 0) → Agree ((k₁ : ℕ) + 1) (d i 1) (d i'' 1) →
      i'' ∈ Finset.univ.filter fun i'' ↦
        ∀ j, Agree (![(k₀ : ℕ), (k₁ : ℕ) + 1] j) (d i j) (d i'' j) := by
    intro i'' h0 h1
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun j ↦ ?_⟩
    fin_cases j
    · exact h0
    · exact h1
  have h1 : Agree ((k₁ : ℕ) + 1) (d i 1) (d i' 1) := by
    rw [agree_succ_iff k₁.isLt, Fin.eta]
    exact ⟨truncDigits_eq_iff.1 (hi.1.trans hi'.1.symm), hi.2.trans hi'.2.symm⟩
  exact Finset.card_le_one.1 hc.le i (hmem i (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)) i'
    (hmem i' (truncDigits_eq_iff.1 h) h1)

/-- The levels `lo ≤ k < hi` of a tree of depth `m`. -/
def levelWin (m lo hi : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun k ↦ lo ≤ (k : ℕ) ∧ (k : ℕ) < hi

/-- The part of the node weight `w_{γ,c}` from the levels `lo ≤ k < hi` of `ρ₀`. -/
noncomputable def wwin {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (ρ₀ : Scramble b m)
    (γ : Fin m × (Fin m → Option (Fin b))) (c : Fin b) (lo hi : ℕ) : ℝ :=
  ∑ i ∈ cellSet d γ c, ∑ k ∈ levelWin m lo hi,
    cdig (ρ₀ (k, truncDigits k (d i 0))) (d i 0 k) * digWt b k

/-- **Only the deep levels contribute to the node weights**: `w_{γ,c}` is its part from the
levels `k₀ ≥ m - k₁ - 1` of `ρ₀` (`k₁` the level of `γ`). -/
theorem nodeW_eq_wwin (hb : 0 < b) {m : ℕ} {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b}
    (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) (ρ₀ : Scramble b m)
    (γ : Fin m × (Fin m → Option (Fin b))) (c : Fin b) :
    nodeW d ρ₀ γ c = wwin d ρ₀ γ c (m - γ.1 - 1) m := by
  classical
  obtain ⟨k₁, t⟩ := γ
  unfold nodeW wwin scrDev levelWin
  have hsplit : ∀ i, ∑ k : Fin m, cdig (ρ₀ (k, truncDigits k (d i 0))) (d i 0 k) * digWt b k =
      ∑ k ∈ Finset.univ.filter (fun k : Fin m ↦ m - (k₁ : ℕ) - 1 ≤ (k : ℕ) ∧ (k : ℕ) < m),
        cdig (ρ₀ (k, truncDigits k (d i 0))) (d i 0 k) * digWt b k +
      ∑ k ∈ Finset.univ.filter (fun k : Fin m ↦ ¬ (m - (k₁ : ℕ) - 1 ≤ (k : ℕ) ∧ (k : ℕ) < m)),
        cdig (ρ₀ (k, truncDigits k (d i 0))) (d i 0 k) * digWt b k := fun i ↦
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [Finset.sum_congr rfl fun i _ ↦ hsplit i, Finset.sum_add_distrib]
  have hz : ∑ i ∈ cellSet d (k₁, t) c,
      ∑ k ∈ Finset.univ.filter (fun k : Fin m ↦ ¬ (m - (k₁ : ℕ) - 1 ≤ (k : ℕ) ∧ (k : ℕ) < m)),
        cdig (ρ₀ (k, truncDigits k (d i 0))) (d i 0 k) * digWt b k = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    rw [Finset.mem_filter] at hk
    have hk' : (k : ℕ) + k₁ + 2 ≤ m := by
      have := k.isLt
      have := k₁.isLt
      omega
    rw [← Finset.sum_mul, sum_cdig_cellSet_eq_zero hb hnet hk' t c ρ₀, zero_mul]
  rw [hz, add_zero]

/-- Splitting a window of levels. -/
theorem wwin_split {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (ρ₀ : Scramble b m)
    (γ : Fin m × (Fin m → Option (Fin b))) (c : Fin b) {lo mid hi : ℕ} (h1 : lo ≤ mid)
    (h2 : mid ≤ hi) : wwin d ρ₀ γ c lo hi = wwin d ρ₀ γ c lo mid + wwin d ρ₀ γ c mid hi := by
  unfold wwin
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_filter_add_sum_filter_not (levelWin m lo hi) (fun k : Fin m ↦ (k : ℕ) < mid)]
  congr 1
  · congr 1
    ext k
    simp only [levelWin, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · congr 1
    ext k
    simp only [levelWin, Finset.mem_filter, Finset.mem_univ, true_and]
    omega

/-- The coordinate term of a node weight: digit `k` of point `i` in coordinate `0`. -/
noncomputable def wX {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (q : Fin n × Fin m)
    (pm : Equiv.Perm (Fin b)) : ℝ :=
  cdig pm (d q.1 0 q.2) * digWt b q.2

/-- The node of the tree of coordinate `0` used by digit `k` of point `i`. -/
def wν {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (q : Fin n × Fin m) :
    Fin m × (Fin m → Option (Fin b)) :=
  (q.2, truncDigits q.2 (d q.1 0))

/-- A window part of a node weight as a sum of coordinate terms. -/
theorem wwin_eq_sum {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (ρ₀ : Scramble b m)
    (γ : Fin m × (Fin m → Option (Fin b))) (c : Fin b) (lo hi : ℕ) :
    wwin d ρ₀ γ c lo hi = ∑ q ∈ cellSet d γ c ×ˢ levelWin m lo hi, wX d q (ρ₀ (wν d q)) := by
  unfold wwin
  rw [Finset.sum_product]
  rfl

/-- **Distinct coordinate terms of a deep window use distinct nodes.** -/
theorem injOn_wν (hb : 0 < b) {m : ℕ} {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b}
    (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) (γ : Fin m × (Fin m → Option (Fin b)))
    (c : Fin b) {lo hi : ℕ} (hlo : m ≤ lo + γ.1 + 1) :
    Set.InjOn (wν d) ↑(cellSet d γ c ×ˢ levelWin m lo hi) := by
  obtain ⟨k₁, t⟩ := γ
  change m ≤ lo + (k₁ : ℕ) + 1 at hlo
  intro q hq q' hq' heq
  rw [Finset.mem_coe, Finset.mem_product] at hq hq'
  unfold wν at heq
  have h2 : q.2 = q'.2 := (Prod.mk.inj heq).1
  have h3 := (Prod.mk.inj heq).2
  rw [← h2] at h3
  have hk : m ≤ (q.2 : ℕ) + k₁ + 1 := by
    have := (Finset.mem_filter.1 hq.2).2.1
    omega
  exact Prod.ext (eq_of_truncDigits_eq_cellSet hb hnet hq.1 hq'.1 hk h3) h2

/-- The coordinate terms are centred. -/
theorem unifAvg_wX {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (q : Fin n × Fin m) :
    unifAvg (wX d q) = 0 := by
  unfold wX
  rw [unifAvg_mul_const, unifAvg_cdig, zero_mul]

/-- The coordinate terms are bounded: `|wX| ≤ (b/2) b^{-(k+1)}`. -/
theorem abs_wX_le (hb : 0 < b) {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b)
    (q : Fin n × Fin m) (pm : Equiv.Perm (Fin b)) :
    |wX d q pm| ≤ (b : ℝ) / 2 * digWt b q.2 := by
  unfold wX
  rw [abs_mul, abs_of_pos (digWt_pos hb _)]
  exact mul_le_mul_of_nonneg_right (abs_cdig_le _ _) (digWt_pos hb _).le

/-- **The geometric bound** `Σ_{lo ≤ k < hi} b^{-2(k+1)} ≤ 2 b^{-2(lo+1)}` (`b ≥ 2`). -/
theorem sum_levelWin_digWt_sq_le (hb : 1 < b) (m lo hi : ℕ) :
    ∑ k ∈ levelWin m lo hi, digWt b k ^ 2 ≤ 2 * digWt b lo ^ 2 := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  set q : ℝ := ((b : ℝ) ^ 2)⁻¹ with hq
  have hq0 : 0 ≤ q := inv_nonneg.2 (sq_nonneg _)
  have hq4 : q ≤ 1 / 4 := by
    rw [hq, one_div]
    exact inv_anti₀ (by norm_num) (by nlinarith)
  have hw : ∀ k : ℕ, digWt b k ^ 2 = q * q ^ k := fun k ↦ by
    unfold digWt
    rw [hq, ← pow_succ', inv_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm (k + 1) 2]
  have hmap : ∑ k ∈ levelWin m lo hi, digWt b k ^ 2 =
      ∑ k ∈ (levelWin m lo hi).map Fin.valEmbedding, digWt b k ^ 2 := by
    rw [Finset.sum_map]
    rfl
  have hsub : (levelWin m lo hi).map Fin.valEmbedding ⊆ Finset.Ico lo (lo + m) := by
    intro k hk
    rw [Finset.mem_map] at hk
    obtain ⟨k', hk', rfl⟩ := hk
    rw [levelWin, Finset.mem_filter] at hk'
    rw [Finset.mem_Ico]
    have := k'.isLt
    simp only [Fin.valEmbedding_apply]
    omega
  rw [hmap]
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ ↦ sq_nonneg _).trans ?_
  rw [Finset.sum_congr rfl fun k _ ↦ hw k, ← Finset.mul_sum, hw lo]
  have hg := geom_sum_Ico_le_of_lt_one (m := lo) (n := lo + m) hq0 (by linarith)
  have h12 : q ^ lo / (1 - q) ≤ 2 * q ^ lo := by
    rw [div_le_iff₀ (by linarith)]
    have := pow_nonneg hq0 lo
    nlinarith
  calc q * ∑ k ∈ Finset.Ico lo (lo + m), q ^ k ≤ q * (2 * q ^ lo) :=
        mul_le_mul_of_nonneg_left (hg.trans h12) hq0
    _ = 2 * (q * q ^ lo) := by ring

/-- **Second moment of a window of a node weight**:
`E[w²] ≤ #(cell) (b/2)² · 2 b^{-2(lo+1)}` for a deep window (`lo + k₁ + 1 ≥ m`). -/
theorem unifAvg_sq_wwin_le (hb : 1 < b) {m : ℕ} {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b}
    (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) (γ : Fin m × (Fin m → Option (Fin b)))
    (c : Fin b) {lo hi : ℕ} (hlo : m ≤ lo + γ.1 + 1) :
    unifAvg (fun ρ₀ : Scramble b m ↦ wwin d ρ₀ γ c lo hi ^ 2) ≤
      (cellSet d γ c).card * (((b : ℝ) / 2) ^ 2 * (2 * digWt b lo ^ 2)) := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have : Nonempty (Equiv.Perm (Fin b)) := ⟨Equiv.refl _⟩
  rw [show (fun ρ₀ : Scramble b m ↦ wwin d ρ₀ γ c lo hi ^ 2) =
    fun ρ₀ ↦ (∑ q ∈ cellSet d γ c ×ˢ levelWin m lo hi, wX d q (ρ₀ (wν d q))) ^ 2 from
    funext fun ρ₀ ↦ by rw [wwin_eq_sum],
    unifAvg_sq_sum_eq (injOn_wν hb0 hnet γ c hlo) (fun q _ ↦ unifAvg_wX d q)]
  calc ∑ q ∈ cellSet d γ c ×ˢ levelWin m lo hi, unifAvg (fun pm ↦ wX d q pm ^ 2)
      ≤ ∑ q ∈ cellSet d γ c ×ˢ levelWin m lo hi, ((b : ℝ) / 2) ^ 2 * digWt b q.2 ^ 2 := by
        refine Finset.sum_le_sum fun q _ ↦ ?_
        refine (unifAvg_mono fun pm ↦ ?_).trans (le_of_eq (unifAvg_const _))
        rw [← mul_pow, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_wX_le hb0 d q pm) 2
    _ = (cellSet d γ c).card * (((b : ℝ) / 2) ^ 2 *
          ∑ k ∈ levelWin m lo hi, digWt b k ^ 2) := by
        rw [Finset.sum_product]
        dsimp only
        rw [Finset.sum_congr rfl fun x _ ↦ (Finset.mul_sum _ _ _).symm, Finset.sum_const,
          nsmul_eq_mul]
    _ ≤ (cellSet d γ c).card * (((b : ℝ) / 2) ^ 2 * (2 * digWt b lo ^ 2)) := by
        gcongr
        exact sum_levelWin_digWt_sq_le hb m lo hi

/-- **Fourth moment of a window of a node weight**: `E[w⁴] ≤ 3 (#(cell) (b/2)² ·
2 b^{-2(lo+1)})²` for a deep window. -/
theorem unifAvg_pow_four_wwin_le (hb : 1 < b) {m : ℕ}
    {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    (γ : Fin m × (Fin m → Option (Fin b))) (c : Fin b) {lo hi : ℕ} (hlo : m ≤ lo + γ.1 + 1) :
    unifAvg (fun ρ₀ : Scramble b m ↦ wwin d ρ₀ γ c lo hi ^ 4) ≤
      3 * ((cellSet d γ c).card * (((b : ℝ) / 2) ^ 2 * (2 * digWt b lo ^ 2))) ^ 2 := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have : Nonempty (Equiv.Perm (Fin b)) := ⟨Equiv.refl _⟩
  rw [show (fun ρ₀ : Scramble b m ↦ wwin d ρ₀ γ c lo hi ^ 4) =
    fun ρ₀ ↦ (∑ q ∈ cellSet d γ c ×ˢ levelWin m lo hi, wX d q (ρ₀ (wν d q))) ^ 4 from
    funext fun ρ₀ ↦ by rw [wwin_eq_sum]]
  refine (unifAvg_pow_four_sum_le (injOn_wν hb0 hnet γ c hlo) (fun q _ ↦ unifAvg_wX d q)
    (β := fun q ↦ (b : ℝ) / 2 * digWt b q.2) fun q _ pm ↦ abs_wX_le hb0 d q pm).trans ?_
  have hs : ∑ q ∈ cellSet d γ c ×ˢ levelWin m lo hi, ((b : ℝ) / 2 * digWt b q.2) ^ 2 ≤
      (cellSet d γ c).card * (((b : ℝ) / 2) ^ 2 * (2 * digWt b lo ^ 2)) := by
    rw [Finset.sum_product]
    dsimp only
    rw [Finset.sum_congr rfl fun x _ ↦ (Finset.sum_congr rfl fun k _ ↦ mul_pow _ _ 2).trans
      (Finset.mul_sum _ _ _).symm, Finset.sum_const, nsmul_eq_mul]
    gcongr
    exact sum_levelWin_digWt_sq_le hb m lo hi
  have h0 : 0 ≤ ∑ q ∈ cellSet d γ c ×ˢ levelWin m lo hi, ((b : ℝ) / 2 * digWt b q.2) ^ 2 :=
    Finset.sum_nonneg fun q _ ↦ sq_nonneg _
  gcongr

end RQMCMarkov.OwenScrambling

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The conditional variance of the product integrand concentrates

Towards Loh's (2003) CLT for `f(x) = x₀ x₁` on scrambled `(0,m,2)`-nets (post #2). Given the
scramble `ρ₀` of coordinate `0`, the error sum `S` is a sum of independent node terms of the
scramble of coordinate `1` (`LohGeneralProd`), with conditional variance
`V(ρ₀) = Σ_γ E_π[nodeTerm²]` (`condVar`). This module proves that `V` concentrates around its
mean: `E|V - E V| = o(E V)`. Each level `k₁` of the tree of coordinate `1` contributes a term
depending mainly on the level `m - k₁ - 1` of `ρ₀`; keeping only a window of `J` levels of `ρ₀`
below it (`condVarWin`, `levelVar`) changes `V` by `O(b^{-J} m/n)` in mean
(`unifAvg_abs_condVar_sub_le`), and the windowed levels `k₁, k₁'` with `|k₁ - k₁'| ≥ J` are
independent (`unifAvg_levelVar_mul`), so the windowed variance has variance `O(J m/n²)`
(`unifAvg_sq_condVarWin_sub_le`). Since `E V ≍ m/n`, choosing `J ≍ √m` gives the
concentration.

## Main results

* `dform`, `abs_dform_le`, `unifAvg_sq_dform_le`, `abs_unifAvg_sq_dform_sub_le`: the linear
  forms `Σ_c (π c - (b-1)/2) w_c` and their second moments.
* `unifAvg_sq_sum_le_of_sq`, `unifAvg_sq_sub_eq`, `unifAvg_sq_sum_sub_le_of_near`: moment
  bounds for sums of nonnegative terms that are independent at distance `≥ J`.
* `condVar`, `levelVar`, `condVarWin`; `unifAvg_abs_condVar_sub_le` (window truncation),
  `unifAvg_sq_levelVar_le`, `unifAvg_levelVar_mul` (independence of distant windows),
  `unifAvg_sq_condVarWin_sub_le` (variance of the windowed part), `unifAvg_abs_sub_avg_le`,
  `sq_unifAvg_abs_le` (assembling the concentration bound).
* `nodeBound`, `abs_nodeTerm_le`, `unifAvg_sum_sq_nodeBound_le`,
  `unifAvg_sum_pow_four_nodeBound_le`: the moments of the bounds
  `b^{-(k+1)} (b/2) Σ_c |w_{γ,c}|` on the node terms.
-/

namespace RQMCMarkov.OwenScrambling

open MeasureTheory ProbabilityTheory Finset Filter
open scoped Topology

variable {b : ℕ}

/-- The linear form `Σ_c (π c - (b-1)/2) w_c` of a weight vector `w`. -/
noncomputable def dform (pm : Equiv.Perm (Fin b)) (w : Fin b → ℝ) : ℝ :=
  ∑ c, cdig pm c * w c

/-- `|Σ_c (π c - (b-1)/2) w_c| ≤ (b/2) Σ_c |w_c|`. -/
theorem abs_dform_le (pm : Equiv.Perm (Fin b)) (w : Fin b → ℝ) :
    |dform pm w| ≤ (b : ℝ) / 2 * ∑ c, |w c| := by
  unfold dform
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ ↦ ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_cdig_le pm c) (abs_nonneg _)

/-- `(Σ_c |w_c|)² ≤ b Σ_c w_c²`. -/
theorem sq_sum_abs_le (w : Fin b → ℝ) : (∑ c, |w c|) ^ 2 ≤ b * ∑ c, w c ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin b))) (f := fun c ↦ |w c|)
  rw [Finset.card_univ, Fintype.card_fin] at h
  simpa only [sq_abs] using h

/-- `(Σ_c |w_c|)⁴ ≤ b³ Σ_c w_c⁴`. -/
theorem pow_four_sum_abs_le (w : Fin b → ℝ) : (∑ c, |w c|) ^ 4 ≤ (b : ℝ) ^ 3 * ∑ c, w c ^ 4 := by
  have h1 := sq_sum_abs_le w
  have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin b)))
    (f := fun c ↦ w c ^ 2)
  rw [Finset.card_univ, Fintype.card_fin] at h2
  have h0 : 0 ≤ (∑ c, |w c|) ^ 2 := sq_nonneg _
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  calc (∑ c, |w c|) ^ 4 = ((∑ c, |w c|) ^ 2) ^ 2 := by ring
    _ ≤ ((b : ℝ) * ∑ c, w c ^ 2) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = (b : ℝ) ^ 2 * (∑ c, w c ^ 2) ^ 2 := by ring
    _ ≤ (b : ℝ) ^ 2 * ((b : ℝ) * ∑ c, (w c ^ 2) ^ 2) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (b : ℝ) ^ 3 * ∑ c, w c ^ 4 := by
        rw [Finset.sum_congr rfl fun c _ ↦ (pow_mul (w c) 2 2).symm]
        ring

/-- The linear form is linear in the weights. -/
theorem dform_sub (pm : Equiv.Perm (Fin b)) (w w' : Fin b → ℝ) :
    dform pm w - dform pm w' = dform pm (fun c ↦ w c - w' c) := by
  unfold dform
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun c _ ↦ by ring

/-- The linear form is additive in the weights. -/
theorem dform_add (pm : Equiv.Perm (Fin b)) (w w' : Fin b → ℝ) :
    dform pm w + dform pm w' = dform pm (fun c ↦ w c + w' c) := by
  unfold dform
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun c _ ↦ by ring

/-- `E_π[(Σ_c (π c - (b-1)/2) w_c)²] ≤ (b/2)² b Σ_c w_c²`. -/
theorem unifAvg_sq_dform_le (hb : 0 < b) (w : Fin b → ℝ) :
    unifAvg (fun pm : Equiv.Perm (Fin b) ↦ dform pm w ^ 2) ≤
      ((b : ℝ) / 2) ^ 2 * (b * ∑ c, w c ^ 2) := by
  have : Nonempty (Equiv.Perm (Fin b)) := ⟨Equiv.refl _⟩
  refine (unifAvg_mono fun pm ↦ ?_).trans (le_of_eq (unifAvg_const _))
  have hb2 : (0 : ℝ) ≤ (b : ℝ) / 2 := by positivity
  calc dform pm w ^ 2 = |dform pm w| ^ 2 := (sq_abs _).symm
    _ ≤ ((b : ℝ) / 2 * ∑ c, |w c|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (abs_dform_le pm w) 2
    _ = ((b : ℝ) / 2) ^ 2 * (∑ c, |w c|) ^ 2 := by ring
    _ ≤ ((b : ℝ) / 2) ^ 2 * (b * ∑ c, w c ^ 2) :=
        mul_le_mul_of_nonneg_left (sq_sum_abs_le w) (sq_nonneg _)

/-- **Lipschitz bound for the second moment of the linear form**:
`|E[(dform w)²] - E[(dform w')²]| ≤ (b/2)² (Σ_c |w_c - w'_c|)(Σ_c |w_c + w'_c|)`. -/
theorem abs_unifAvg_sq_dform_sub_le (w w' : Fin b → ℝ) :
    |unifAvg (fun pm : Equiv.Perm (Fin b) ↦ dform pm w ^ 2) -
        unifAvg (fun pm : Equiv.Perm (Fin b) ↦ dform pm w' ^ 2)| ≤
      ((b : ℝ) / 2) ^ 2 * ((∑ c, |w c - w' c|) * ∑ c, |w c + w' c|) := by
  rcases isEmpty_or_nonempty (Fin b) with hb | hb
  · have : b = 0 := by
      by_contra h
      exact hb.false ⟨0, Nat.pos_of_ne_zero h⟩
    subst this
    simp [unifAvg, dform]
  have hb0 : 0 < b := Fin.pos (Classical.arbitrary (Fin b))
  have : Nonempty (Equiv.Perm (Fin b)) := ⟨Equiv.refl _⟩
  have e : unifAvg (fun pm : Equiv.Perm (Fin b) ↦ dform pm w ^ 2) -
      unifAvg (fun pm : Equiv.Perm (Fin b) ↦ dform pm w' ^ 2) =
      unifAvg (fun pm ↦ dform pm (fun c ↦ w c - w' c) * dform pm (fun c ↦ w c + w' c)) := by
    rw [sub_eq_add_neg, ← neg_one_mul, ← unifAvg_const_mul, ← unifAvg_add]
    congr 1
    funext pm
    rw [← dform_sub, ← dform_add]
    ring
  rw [e]
  refine (abs_unifAvg_le _).trans ((unifAvg_mono fun pm ↦ ?_).trans (le_of_eq (unifAvg_const _)))
  rw [abs_mul]
  have hb2 : (0 : ℝ) ≤ (b : ℝ) / 2 := by positivity
  calc |dform pm (fun c ↦ w c - w' c)| * |dform pm (fun c ↦ w c + w' c)|
      ≤ ((b : ℝ) / 2 * ∑ c, |w c - w' c|) * ((b : ℝ) / 2 * ∑ c, |w c + w' c|) :=
        mul_le_mul (abs_dform_le _ _) (abs_dform_le _ _) (abs_nonneg _)
          (mul_nonneg hb2 (Finset.sum_nonneg fun c _ ↦ abs_nonneg _))
    _ = ((b : ℝ) / 2) ^ 2 * ((∑ c, |w c - w' c|) * ∑ c, |w c + w' c|) := by ring

/-- **Second moment of a sum from second-moment bounds of its terms**: if
`E[Y_a²] ≤ u_a²` with `u_a ≥ 0`, then `E[(Σ_a Y_a)²] ≤ (Σ_a u_a)²`. -/
theorem unifAvg_sq_sum_le_of_sq {R ι : Type*} [Fintype R] (s : Finset ι) (Y : ι → R → ℝ)
    {u : ι → ℝ} (hu : ∀ a ∈ s, 0 ≤ u a)
    (hY : ∀ a ∈ s, unifAvg (fun r ↦ Y a r ^ 2) ≤ u a ^ 2) :
    unifAvg (fun r ↦ (∑ a ∈ s, Y a r) ^ 2) ≤ (∑ a ∈ s, u a) ^ 2 := by
  have e : (fun r ↦ (∑ a ∈ s, Y a r) ^ 2) = fun r ↦ ∑ a ∈ s, ∑ a' ∈ s, Y a r * Y a' r :=
    funext fun r ↦ by rw [sq, Finset.sum_mul_sum]
  rw [e, unifAvg_sum, sq, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun a ha ↦ ?_
  rw [unifAvg_sum]
  refine Finset.sum_le_sum fun a' ha' ↦ ?_
  have h := sq_unifAvg_mul_le (Y a) (Y a')
  have hprod : (unifAvg fun r ↦ Y a r ^ 2) * (unifAvg fun r ↦ Y a' r ^ 2) ≤ (u a * u a') ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul (hY a ha) (hY a' ha') (unifAvg_nonneg fun r ↦ sq_nonneg _)
      (sq_nonneg _)
  exact (le_abs_self _).trans (abs_le_of_sq_le_sq (h.trans hprod)
    (mul_nonneg (hu a ha) (hu a' ha')))

/-- The variance identity `E[(Z - E Z)²] = E[Z²] - (E Z)²`. -/
theorem unifAvg_sq_sub_eq {R : Type*} [Fintype R] [Nonempty R] (Z : R → ℝ) :
    unifAvg (fun r ↦ (Z r - unifAvg Z) ^ 2) = unifAvg (fun r ↦ Z r ^ 2) - unifAvg Z ^ 2 := by
  have e : (fun r ↦ (Z r - unifAvg Z) ^ 2) =
      fun r ↦ (Z r ^ 2 + (-2 * unifAvg Z) * Z r) + unifAvg Z ^ 2 :=
    funext fun r ↦ by ring
  rw [e, unifAvg_add, unifAvg_add, unifAvg_const_mul, unifAvg_const]
  ring

/-- **Variance of a sum of nonnegative terms independent at distance `≥ J`**: if
`E[X_k X_{k'}] = E X_k E X_{k'}` whenever `|k - k'| ≥ J` and `E[X_k²] ≤ A`, then
`E[(Σ_k X_k - E Σ_k X_k)²] ≤ 2 J m A`. -/
theorem unifAvg_sq_sum_sub_le_of_near {R : Type*} [Fintype R] [Nonempty R] {m J : ℕ}
    (X : Fin m → R → ℝ) (hX0 : ∀ k r, 0 ≤ X k r)
    (hind : ∀ k k' : Fin m, (k : ℕ) + J ≤ k' ∨ (k' : ℕ) + J ≤ k →
      unifAvg (fun r ↦ X k r * X k' r) = unifAvg (X k) * unifAvg (X k'))
    {A : ℝ} (hA : ∀ k, unifAvg (fun r ↦ X k r ^ 2) ≤ A) :
    unifAvg (fun r ↦ (∑ k, X k r - unifAvg (fun r' ↦ ∑ k, X k r')) ^ 2) ≤ 2 * J * m * A := by
  classical
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp [unifAvg]
  have hA0 : 0 ≤ A := (unifAvg_nonneg fun r ↦ sq_nonneg _).trans (hA ⟨0, hm⟩)
  rw [unifAvg_sq_sub_eq]
  have e1 : unifAvg (fun r ↦ (∑ k, X k r) ^ 2) =
      ∑ k, ∑ k', unifAvg (fun r ↦ X k r * X k' r) := by
    rw [show (fun r ↦ (∑ k, X k r) ^ 2) = fun r ↦ ∑ k, ∑ k', X k r * X k' r from
      funext fun r ↦ by rw [sq, Finset.sum_mul_sum], unifAvg_sum]
    exact Finset.sum_congr rfl fun k _ ↦ unifAvg_sum _ _
  have e2 : unifAvg (fun r' ↦ ∑ k, X k r') ^ 2 =
      ∑ k, ∑ k', unifAvg (X k) * unifAvg (X k') := by
    rw [unifAvg_sum, sq, Finset.sum_mul_sum]
  rw [e1, e2]
  simp only [← Finset.sum_sub_distrib]
  have hterm : ∀ k k' : Fin m, unifAvg (fun r ↦ X k r * X k' r) -
      unifAvg (X k) * unifAvg (X k') ≤
      if (k : ℕ) < k' + J ∧ (k' : ℕ) < k + J then A else 0 := by
    intro k k'
    split_ifs with h
    · have h1 : unifAvg (fun r ↦ X k r * X k' r) ≤ A := by
        have h3 : unifAvg (fun r ↦ X k r * X k' r) ≤
            unifAvg (fun r ↦ 1 / 2 * (X k r ^ 2 + X k' r ^ 2)) :=
          unifAvg_mono fun r ↦ by nlinarith [sq_nonneg (X k r - X k' r)]
        rw [unifAvg_const_mul, unifAvg_add] at h3
        linarith [hA k, hA k']
      have h2 : 0 ≤ unifAvg (X k) * unifAvg (X k') :=
        mul_nonneg (unifAvg_nonneg (hX0 k)) (unifAvg_nonneg (hX0 k'))
      linarith
    · rw [hind k k' (by omega), sub_self]
  have hcard : ∀ k : Fin m, (Finset.univ.filter fun k' : Fin m ↦
      (k : ℕ) < k' + J ∧ (k' : ℕ) < k + J).card ≤ 2 * J := by
    intro k
    refine (Finset.card_le_card_of_injOn (fun k' : Fin m ↦ (k' : ℕ))
      (t := Finset.Ico ((k : ℕ) + 1 - J) ((k : ℕ) + J)) (fun k' hk' ↦ ?_)
      (fun x _ y _ hxy ↦ Fin.ext hxy)).trans ?_
    · rw [Finset.mem_coe, Finset.mem_filter] at hk'
      rw [Finset.mem_coe, Finset.mem_Ico]
      dsimp only
      omega
    · rw [Nat.card_Ico]
      omega
  calc ∑ k, ∑ k', (unifAvg (fun r ↦ X k r * X k' r) - unifAvg (X k) * unifAvg (X k'))
      ≤ ∑ k : Fin m, ∑ k' : Fin m,
          (if (k : ℕ) < k' + J ∧ (k' : ℕ) < k + J then A else 0) :=
        Finset.sum_le_sum fun k _ ↦ Finset.sum_le_sum fun k' _ ↦ hterm k k'
    _ = ∑ k : Fin m, A * (Finset.univ.filter fun k' : Fin m ↦
          (k : ℕ) < k' + J ∧ (k' : ℕ) < k + J).card := by
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
          mul_comm]
    _ ≤ ∑ _k : Fin m, A * (2 * J : ℕ) := by
        refine Finset.sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_left ?_ hA0
        exact_mod_cast hcard k
    _ = 2 * J * m * A := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- `x y ≤ (λ x² + y²/λ)/2` for `λ > 0`. -/
theorem mul_le_half_add_sq {x y l : ℝ} (hl : 0 < l) : x * y ≤ (l * x ^ 2 + y ^ 2 / l) / 2 := by
  have h : l * (2 * (x * y)) ≤ l * (l * x ^ 2 + y ^ 2 / l) := by
    rw [mul_add, ← mul_assoc, mul_div_cancel₀ _ hl.ne']
    nlinarith [sq_nonneg (l * x - y)]
  have := le_of_mul_le_mul_left h hl
  linarith

/-- `Σ x_a² ≤ (Σ x_a)²` for nonnegative `x`. -/
theorem sum_sq_le_sq_sum {ι : Type*} (s : Finset ι) {x : ι → ℝ} (hx : ∀ a ∈ s, 0 ≤ x a) :
    ∑ a ∈ s, x a ^ 2 ≤ (∑ a ∈ s, x a) ^ 2 := by
  rw [sq (∑ a ∈ s, x a), Finset.sum_mul]
  refine Finset.sum_le_sum fun a ha ↦ ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_left (Finset.single_le_sum hx ha) (hx a ha)

/-- `b^{-(k+1)} b^{-(m-k)} = b^{-(m+1)}` for `k < m`. -/
theorem digWt_mul_digWt {m : ℕ} (k : Fin m) : digWt b k * digWt b (m - k - 1) = digWt b m := by
  unfold digWt
  rw [← mul_inv, ← pow_add]
  congr 2
  have := k.isLt
  omega

/-- `b^{-(l+J+1)} = b^{-(l+1)} b^{-J}`. -/
theorem digWt_add (b l J : ℕ) : digWt b (l + J) = digWt b l * ((b : ℝ) ^ J)⁻¹ := by
  unfold digWt
  rw [← mul_inv, ← pow_add]
  congr 2
  omega

/-- **The points of a level are partitioned by the nodes and their children**:
`Σ_t Σ_c #(cellSet (k, t) c) = n`. -/
theorem sum_card_cellSet {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (k : Fin m) :
    ∑ t : Fin m → Option (Fin b), ∑ c, ((cellSet d (k, t) c).card : ℝ) = n := by
  classical
  have h1 : ∀ t : Fin m → Option (Fin b),
      ∑ c, ((cellSet d (k, t) c).card : ℝ) = (nodeSet d (k, t)).card := by
    intro t
    rw [Finset.card_eq_sum_card_fiberwise (f := fun i ↦ d i 1 k) (t := Finset.univ)
      (fun _ _ ↦ Finset.mem_univ _), Nat.cast_sum]
    rfl
  rw [Finset.sum_congr rfl fun t _ ↦ h1 t]
  have h2 := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin n)))
    (f := fun i ↦ truncDigits k (d i 1)) (t := Finset.univ) (fun _ _ ↦ Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at h2
  have h3 : (∑ t : Fin m → Option (Fin b), (nodeSet d (k, t)).card) = n := h2.symm
  rw [← Nat.cast_sum, h3]

/-- The total over all nodes: `Σ_γ Σ_c #(cellSet γ c) = m n`. -/
theorem sum_card_cellSet_all {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) :
    ∑ γ : Fin m × (Fin m → Option (Fin b)), ∑ c, ((cellSet d γ c).card : ℝ) = m * n := by
  rw [Fintype.sum_prod_type]
  simp only [sum_card_cellSet d, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

/-- Splitting the top window of levels at `lo + J`. -/
theorem wwin_split_top {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (ρ₀ : Scramble b m)
    (γ : Fin m × (Fin m → Option (Fin b))) (c : Fin b) (lo J : ℕ) :
    wwin d ρ₀ γ c lo m = wwin d ρ₀ γ c lo (lo + J) + wwin d ρ₀ γ c (lo + J) m := by
  unfold wwin
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_filter_add_sum_filter_not (levelWin m lo m)
    (fun k : Fin m ↦ (k : ℕ) < lo + J)]
  congr 1
  · congr 1
    ext k
    simp only [levelWin, Finset.mem_filter, Finset.mem_univ, true_and]
    have := k.isLt
    omega
  · congr 1
    ext k
    simp only [levelWin, Finset.mem_filter, Finset.mem_univ, true_and]
    have := k.isLt
    omega

/-- A window part of a node weight depends only on the levels in the window. -/
theorem wwin_congr {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) {ρ ρ' : Scramble b m}
    (γ : Fin m × (Fin m → Option (Fin b))) (c : Fin b) {lo hi : ℕ}
    (h : ∀ k ∈ levelWin m lo hi, ∀ x, ρ (k, x) = ρ' (k, x)) :
    wwin d ρ γ c lo hi = wwin d ρ' γ c lo hi := by
  unfold wwin
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k hk ↦ by rw [h k hk]

/-- `E_π[(a · dform π w)²] = a² E_π[(dform π w)²]`. -/
theorem unifAvg_sq_mul_dform (a : ℝ) (w : Fin b → ℝ) :
    unifAvg (fun pm : Equiv.Perm (Fin b) ↦ (a * dform pm w) ^ 2) =
      a ^ 2 * unifAvg (fun pm : Equiv.Perm (Fin b) ↦ dform pm w ^ 2) := by
  rw [← unifAvg_const_mul]
  congr 1
  funext pm
  ring

/-- The conditional variance `V(ρ₀) = Σ_γ E_π[nodeTerm²]` of `S` given `ρ₀`. -/
noncomputable def condVar {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (ρ₀ : Scramble b m) :
    ℝ :=
  ∑ γ, unifAvg (fun pm ↦ nodeTerm d ρ₀ γ pm ^ 2)

/-- The level-`k` part of the windowed conditional variance: only the levels
`m - k - 1 ≤ k₀ < m - k - 1 + J` of `ρ₀` are kept in the node weights. -/
noncomputable def levelVar {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (ρ₀ : Scramble b m)
    (J : ℕ) (k : Fin m) : ℝ :=
  ∑ t : Fin m → Option (Fin b), unifAvg (fun pm : Equiv.Perm (Fin b) ↦
    (digWt b k * dform pm (fun c ↦ wwin d ρ₀ (k, t) c (m - k - 1) (m - k - 1 + J))) ^ 2)

/-- The windowed conditional variance `Σ_k levelVar`. -/
noncomputable def condVarWin {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (ρ₀ : Scramble b m)
    (J : ℕ) : ℝ :=
  ∑ k : Fin m, levelVar d ρ₀ J k

/-- **One node: the window truncation error of the conditional variance**:
`E|E_π[nodeTerm²] - E_π[windowed²]| ≤ 5 b (b/2)⁴ b^{-J} b^{-2(m+1)} #(points below γ)`. -/
theorem unifAvg_abs_nodeVar_sub_le (hb : 1 < b) {m : ℕ}
    {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    (k : Fin m) (t : Fin m → Option (Fin b)) (J : ℕ) :
    unifAvg (fun ρ₀ : Scramble b m ↦ |unifAvg (fun pm ↦ nodeTerm d ρ₀ (k, t) pm ^ 2) -
      unifAvg (fun pm : Equiv.Perm (Fin b) ↦
        (digWt b k * dform pm (fun c ↦ wwin d ρ₀ (k, t) c (m - k - 1) (m - k - 1 + J))) ^ 2)|) ≤
      5 * b * ((b : ℝ) / 2) ^ 4 * ((b : ℝ) ^ J)⁻¹ * digWt b m ^ 2 *
        ∑ c, ((cellSet d (k, t) c).card : ℝ) := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hbR : (0 : ℝ) < b := Nat.cast_pos.2 hb0
  set lo := m - (k : ℕ) - 1 with hlo
  set h := (b : ℝ) / 2 with hh
  set l : ℝ := (b : ℝ) ^ J with hl
  have hl0 : 0 < l := pow_pos hbR J
  set wk := digWt b k with hwk
  set W := digWt b lo with hW
  have hhlo : m ≤ lo + (k, t).1 + 1 := by
    change m ≤ lo + (k : ℕ) + 1
    have := k.isLt
    omega
  have hhloJ : m ≤ lo + J + (k, t).1 + 1 := by
    change m ≤ lo + J + (k : ℕ) + 1
    have := k.isLt
    omega
  set α := wk ^ 2 * h ^ 2 * (l * b) / 2 with hα
  set β := wk ^ 2 * h ^ 2 * (l⁻¹ * b) with hβ
  have hα0 : 0 ≤ α := by positivity
  have hβ0 : 0 ≤ β := by positivity
  -- the pointwise bound
  have hpt : ∀ ρ₀ : Scramble b m, |unifAvg (fun pm ↦ nodeTerm d ρ₀ (k, t) pm ^ 2) -
      unifAvg (fun pm : Equiv.Perm (Fin b) ↦
        (digWt b k * dform pm (fun c ↦ wwin d ρ₀ (k, t) c lo (lo + J))) ^ 2)| ≤
      ∑ c, (α * wwin d ρ₀ (k, t) c (lo + J) m ^ 2 + β * wwin d ρ₀ (k, t) c lo m ^ 2 +
        β * wwin d ρ₀ (k, t) c lo (lo + J) ^ 2) := by
    intro ρ₀
    set w : Fin b → ℝ := fun c ↦ wwin d ρ₀ (k, t) c lo m with hw
    set wJ : Fin b → ℝ := fun c ↦ wwin d ρ₀ (k, t) c lo (lo + J) with hwJ
    set D : Fin b → ℝ := fun c ↦ wwin d ρ₀ (k, t) c (lo + J) m with hD
    have hwD : ∀ c, w c - wJ c = D c := fun c ↦ by
      rw [hw, hwJ, hD]
      simp only
      rw [wwin_split_top d ρ₀ (k, t) c lo J]
      ring
    have hnt : ∀ pm, nodeTerm d ρ₀ (k, t) pm = wk * dform pm w := fun pm ↦ by
      change digWt b k * ∑ c, cdig pm c * nodeW d ρ₀ (k, t) c = wk * ∑ c, cdig pm c * w c
      congr 1
      refine Finset.sum_congr rfl fun c _ ↦ ?_
      rw [hw, nodeW_eq_wwin hb0 hnet]
    rw [show (fun pm ↦ nodeTerm d ρ₀ (k, t) pm ^ 2) = fun pm ↦ (wk * dform pm w) ^ 2 from
      funext fun pm ↦ by rw [hnt], unifAvg_sq_mul_dform, unifAvg_sq_mul_dform, ← mul_sub,
      abs_mul, abs_of_nonneg (sq_nonneg _)]
    have h1 := abs_unifAvg_sq_dform_sub_le w wJ
    have h2 : (∑ c, |w c - wJ c|) * (∑ c, |w c + wJ c|) ≤
        (l * (b * ∑ c, D c ^ 2) + (b * ∑ c, (2 * w c ^ 2 + 2 * wJ c ^ 2)) / l) / 2 := by
      refine (mul_le_half_add_sq hl0).trans ?_
      have hA : (∑ c, |w c - wJ c|) ^ 2 ≤ b * ∑ c, D c ^ 2 := by
        rw [Finset.sum_congr rfl fun c _ ↦ by rw [hwD c]]
        exact sq_sum_abs_le D
      have hB : (∑ c, |w c + wJ c|) ^ 2 ≤ b * ∑ c, (2 * w c ^ 2 + 2 * wJ c ^ 2) := by
        refine (sq_sum_abs_le _).trans ?_
        gcongr with c
        nlinarith [sq_nonneg (w c - wJ c)]
      have := mul_le_mul_of_nonneg_left hA hl0.le
      have := div_le_div_of_nonneg_right hB hl0.le
      linarith
    calc wk ^ 2 * |unifAvg (fun pm ↦ dform pm w ^ 2) - unifAvg (fun pm ↦ dform pm wJ ^ 2)|
        ≤ wk ^ 2 * (h ^ 2 * ((∑ c, |w c - wJ c|) * ∑ c, |w c + wJ c|)) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ ≤ wk ^ 2 * (h ^ 2 * ((l * (b * ∑ c, D c ^ 2) +
            (b * ∑ c, (2 * w c ^ 2 + 2 * wJ c ^ 2)) / l) / 2)) := by
          gcongr
      _ = ∑ c, (α * D c ^ 2 + β * w c ^ 2 + β * wJ c ^ 2) := by
          rw [hα, hβ, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum]
          field_simp
          ring
  refine (unifAvg_mono hpt).trans ?_
  rw [unifAvg_sum]
  simp only [unifAvg_add, unifAvg_const_mul]
  -- the moments
  have hD2 : ∀ c, unifAvg (fun ρ₀ : Scramble b m ↦ wwin d ρ₀ (k, t) c (lo + J) m ^ 2) ≤
      (cellSet d (k, t) c).card * (h ^ 2 * (2 * (W * l⁻¹) ^ 2)) := fun c ↦ by
    have := unifAvg_sq_wwin_le hb hnet (k, t) c (lo := lo + J) (hi := m) hhloJ
    rwa [digWt_add] at this
  have hw2 : ∀ c, unifAvg (fun ρ₀ : Scramble b m ↦ wwin d ρ₀ (k, t) c lo m ^ 2) ≤
      (cellSet d (k, t) c).card * (h ^ 2 * (2 * W ^ 2)) := fun c ↦
    unifAvg_sq_wwin_le hb hnet (k, t) c (lo := lo) (hi := m) hhlo
  have hwJ2 : ∀ c, unifAvg (fun ρ₀ : Scramble b m ↦ wwin d ρ₀ (k, t) c lo (lo + J) ^ 2) ≤
      (cellSet d (k, t) c).card * (h ^ 2 * (2 * W ^ 2)) := fun c ↦
    unifAvg_sq_wwin_le hb hnet (k, t) c (lo := lo) (hi := lo + J) hhlo
  have hWm : wk * W = digWt b m := digWt_mul_digWt k
  calc ∑ c, (α * unifAvg (fun ρ₀ : Scramble b m ↦ wwin d ρ₀ (k, t) c (lo + J) m ^ 2) +
        β * unifAvg (fun ρ₀ : Scramble b m ↦ wwin d ρ₀ (k, t) c lo m ^ 2) +
        β * unifAvg (fun ρ₀ : Scramble b m ↦ wwin d ρ₀ (k, t) c lo (lo + J) ^ 2))
      ≤ ∑ c, (α * ((cellSet d (k, t) c).card * (h ^ 2 * (2 * (W * l⁻¹) ^ 2))) +
          β * ((cellSet d (k, t) c).card * (h ^ 2 * (2 * W ^ 2))) +
          β * ((cellSet d (k, t) c).card * (h ^ 2 * (2 * W ^ 2)))) := by
        gcongr with c
        · exact hD2 c
        · exact hw2 c
        · exact hwJ2 c
    _ = 5 * b * h ^ 4 * l⁻¹ * (wk * W) ^ 2 * ∑ c, ((cellSet d (k, t) c).card : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ ↦ ?_
        rw [hα, hβ]
        field_simp
        ring
    _ = _ := by rw [hWm]

/-- **The window truncation error of the conditional variance**:
`E|V - V_J| ≤ 5 b (b/2)⁴ b^{-J} b^{-2(m+1)} m n`. -/
theorem unifAvg_abs_condVar_sub_le (hb : 1 < b) {m : ℕ}
    {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    (J : ℕ) :
    unifAvg (fun ρ₀ : Scramble b m ↦ |condVar d ρ₀ - condVarWin d ρ₀ J|) ≤
      5 * b * ((b : ℝ) / 2) ^ 4 * ((b : ℝ) ^ J)⁻¹ * digWt b m ^ 2 * (m * (b ^ m : ℕ)) := by
  have hpt : ∀ ρ₀ : Scramble b m, |condVar d ρ₀ - condVarWin d ρ₀ J| ≤
      ∑ k : Fin m, ∑ t : Fin m → Option (Fin b),
        |unifAvg (fun pm ↦ nodeTerm d ρ₀ (k, t) pm ^ 2) -
          unifAvg (fun pm : Equiv.Perm (Fin b) ↦ (digWt b k *
            dform pm (fun c ↦ wwin d ρ₀ (k, t) c (m - k - 1) (m - k - 1 + J))) ^ 2)| := by
    intro ρ₀
    unfold condVar condVarWin levelVar
    rw [Fintype.sum_prod_type, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
    rw [← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  refine (unifAvg_mono hpt).trans ?_
  rw [unifAvg_sum]
  simp only [unifAvg_sum]
  calc ∑ k : Fin m, ∑ t : Fin m → Option (Fin b), unifAvg (fun ρ₀ : Scramble b m ↦
        |unifAvg (fun pm ↦ nodeTerm d ρ₀ (k, t) pm ^ 2) -
          unifAvg (fun pm : Equiv.Perm (Fin b) ↦ (digWt b k *
            dform pm (fun c ↦ wwin d ρ₀ (k, t) c (m - k - 1) (m - k - 1 + J))) ^ 2)|)
      ≤ ∑ k : Fin m, ∑ t : Fin m → Option (Fin b),
          5 * b * ((b : ℝ) / 2) ^ 4 * ((b : ℝ) ^ J)⁻¹ * digWt b m ^ 2 *
            ∑ c, ((cellSet d (k, t) c).card : ℝ) :=
        Finset.sum_le_sum fun k _ ↦ Finset.sum_le_sum fun t _ ↦
          unifAvg_abs_nodeVar_sub_le hb hnet k t J
    _ = 5 * b * ((b : ℝ) / 2) ^ 4 * ((b : ℝ) ^ J)⁻¹ * digWt b m ^ 2 * (m * (b ^ m : ℕ)) := by
        rw [← sum_card_cellSet_all d, Fintype.sum_prod_type, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [Finset.mul_sum]

/-- The level parts of the windowed conditional variance are nonnegative. -/
theorem levelVar_nonneg {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (ρ₀ : Scramble b m)
    (J : ℕ) (k : Fin m) : 0 ≤ levelVar d ρ₀ J k :=
  Finset.sum_nonneg fun _ _ ↦ unifAvg_nonneg fun _ ↦ sq_nonneg _

/-- **The second moment of a level part**: `E[levelVar²] ≤ (4 b (b/2)⁴ b^{-2(m+1)} n)²`. -/
theorem unifAvg_sq_levelVar_le (hb : 1 < b) {m : ℕ}
    {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    (J : ℕ) (k : Fin m) :
    unifAvg (fun ρ₀ : Scramble b m ↦ levelVar d ρ₀ J k ^ 2) ≤
      (4 * b * ((b : ℝ) / 2) ^ 4 * digWt b m ^ 2 * (b ^ m : ℕ)) ^ 2 := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  set lo := m - (k : ℕ) - 1 with hlo
  set h := (b : ℝ) / 2 with hh
  set wk := digWt b k with hwk
  set W := digWt b lo with hW
  set Y : (Fin m → Option (Fin b)) × Fin b → Scramble b m → ℝ :=
    fun a ρ₀ ↦ wwin d ρ₀ (k, a.1) a.2 lo (lo + J) ^ 2 with hY
  have hhlo : ∀ t : Fin m → Option (Fin b), m ≤ lo + (k, t).1 + 1 := fun t ↦ by
    change m ≤ lo + (k : ℕ) + 1
    have := k.isLt
    omega
  have hle : ∀ ρ₀, levelVar d ρ₀ J k ≤ wk ^ 2 * (h ^ 2 * b) * ∑ a, Y a ρ₀ := by
    intro ρ₀
    unfold levelVar
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_le_sum fun t _ ↦ ?_
    rw [unifAvg_sq_mul_dform]
    refine (mul_le_mul_of_nonneg_left (unifAvg_sq_dform_le hb0 _) (sq_nonneg _)).trans
      (le_of_eq ?_)
    rw [hY, hwk, hh]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    ring
  have hpt : ∀ ρ₀, levelVar d ρ₀ J k ^ 2 ≤ (wk ^ 2 * (h ^ 2 * b)) ^ 2 * (∑ a, Y a ρ₀) ^ 2 := by
    intro ρ₀
    rw [← mul_pow]
    exact pow_le_pow_left₀ (levelVar_nonneg d ρ₀ J k) (hle ρ₀) 2
  refine (unifAvg_mono hpt).trans ?_
  rw [unifAvg_const_mul]
  set u : (Fin m → Option (Fin b)) × Fin b → ℝ :=
    fun a ↦ 2 * ((cellSet d (k, a.1) a.2).card * (h ^ 2 * (2 * W ^ 2))) with hu
  have hu0 : ∀ a ∈ (Finset.univ : Finset ((Fin m → Option (Fin b)) × Fin b)), 0 ≤ u a :=
    fun a _ ↦ by rw [hu]; positivity
  have hY2 : ∀ a ∈ (Finset.univ : Finset ((Fin m → Option (Fin b)) × Fin b)),
      unifAvg (fun ρ₀ ↦ Y a ρ₀ ^ 2) ≤ u a ^ 2 := by
    intro a _
    have h4 := unifAvg_pow_four_wwin_le hb hnet (k, a.1) a.2 (lo := lo) (hi := lo + J)
      (hhlo a.1)
    rw [hY]
    refine le_trans (le_of_eq ?_) (h4.trans ?_)
    · congr 1
      funext ρ₀
      ring
    · have e : u a = 2 * (((cellSet d (k, a.1) a.2).card : ℝ) *
          (((b : ℝ) / 2) ^ 2 * (2 * digWt b lo ^ 2))) := rfl
      rw [e]
      have : 0 ≤ (((cellSet d (k, a.1) a.2).card : ℝ) *
          (((b : ℝ) / 2) ^ 2 * (2 * digWt b lo ^ 2))) ^ 2 := sq_nonneg _
      nlinarith
  have hsum := unifAvg_sq_sum_le_of_sq Finset.univ Y hu0 hY2
  have hus : ∑ a, u a = 4 * h ^ 2 * W ^ 2 * (b ^ m : ℕ) := by
    rw [hu, Fintype.sum_prod_type]
    simp only
    rw [← sum_card_cellSet d k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ ↦ by ring
  rw [hus] at hsum
  have hWm : wk * W = digWt b m := digWt_mul_digWt k
  calc (wk ^ 2 * (h ^ 2 * b)) ^ 2 * unifAvg (fun ρ₀ ↦ (∑ a, Y a ρ₀) ^ 2)
      ≤ (wk ^ 2 * (h ^ 2 * b)) ^ 2 * (4 * h ^ 2 * W ^ 2 * (b ^ m : ℕ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = (4 * b * h ^ 4 * (wk * W) ^ 2 * (b ^ m : ℕ)) ^ 2 := by ring
    _ = _ := by rw [hWm]

/-- **Distant level parts are independent**: if `k + J ≤ k'` or `k' + J ≤ k`, the windows of
levels of `ρ₀` used by `levelVar k` and `levelVar k'` are disjoint. -/
theorem unifAvg_levelVar_mul {m : ℕ} (d : Fin (b ^ m) → Fin 2 → Fin m → Fin b) (J : ℕ)
    (k k' : Fin m) (hkk : (k : ℕ) + J ≤ k' ∨ (k' : ℕ) + J ≤ k) :
    unifAvg (fun ρ₀ : Scramble b m ↦ levelVar d ρ₀ J k * levelVar d ρ₀ J k') =
      unifAvg (fun ρ₀ : Scramble b m ↦ levelVar d ρ₀ J k) *
        unifAvg (fun ρ₀ : Scramble b m ↦ levelVar d ρ₀ J k') := by
  have : Nonempty (Equiv.Perm (Fin b)) := ⟨Equiv.refl _⟩
  have hk := k.isLt
  have hk' := k'.isLt
  refine unifAvg_mul_of_disjoint (fun γ₀ : Fin m × (Fin m → Option (Fin b)) ↦
    m - (k : ℕ) - 1 ≤ γ₀.1 ∧ (γ₀.1 : ℕ) < m - (k : ℕ) - 1 + J) (fun ρ ρ' hρ ↦ ?_)
    (fun ρ ρ' hρ ↦ ?_)
  · unfold levelVar
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [show (fun c ↦ wwin d ρ (k, t) c (m - k - 1) (m - k - 1 + J)) =
      fun c ↦ wwin d ρ' (k, t) c (m - k - 1) (m - k - 1 + J) from funext fun c ↦
        wwin_congr d (k, t) c fun k₀ hk₀ x ↦ hρ (k₀, x) (Finset.mem_filter.1 hk₀).2]
  · unfold levelVar
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [show (fun c ↦ wwin d ρ (k', t) c (m - k' - 1) (m - k' - 1 + J)) =
      fun c ↦ wwin d ρ' (k', t) c (m - k' - 1) (m - k' - 1 + J) from funext fun c ↦
        wwin_congr d (k', t) c fun k₀ hk₀ x ↦ hρ (k₀, x) (by
          have := (Finset.mem_filter.1 hk₀).2
          simp only
          omega)]

/-- **The variance of the windowed conditional variance**:
`E[(V_J - E V_J)²] ≤ 2 J m (4 b (b/2)⁴ b^{-2(m+1)} n)²`. -/
theorem unifAvg_sq_condVarWin_sub_le (hb : 1 < b) {m : ℕ}
    {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    (J : ℕ) :
    unifAvg (fun ρ₀ : Scramble b m ↦ (condVarWin d ρ₀ J -
      unifAvg (fun ρ₀' : Scramble b m ↦ condVarWin d ρ₀' J)) ^ 2) ≤
      2 * J * m * (4 * b * ((b : ℝ) / 2) ^ 4 * digWt b m ^ 2 * (b ^ m : ℕ)) ^ 2 := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have : Nonempty (Equiv.Perm (Fin b)) := ⟨Equiv.refl _⟩
  exact unifAvg_sq_sum_sub_le_of_near (fun k ρ₀ ↦ levelVar d ρ₀ J k)
    (fun k ρ₀ ↦ levelVar_nonneg d ρ₀ J k) (fun k k' hkk ↦ unifAvg_levelVar_mul d J k k' hkk)
    (fun k ↦ unifAvg_sq_levelVar_le hb hnet J k)

/-- `E|V - E V| ≤ 2 E|V - W| + E|W - E W|`. -/
theorem unifAvg_abs_sub_avg_le {R : Type*} [Fintype R] [Nonempty R] (V W : R → ℝ) :
    unifAvg (fun r ↦ |V r - unifAvg V|) ≤
      2 * unifAvg (fun r ↦ |V r - W r|) + unifAvg (fun r ↦ |W r - unifAvg W|) := by
  have hEW : |unifAvg W - unifAvg V| ≤ unifAvg (fun r ↦ |V r - W r|) := by
    have e : unifAvg W - unifAvg V = unifAvg (fun r ↦ W r - V r) := by
      rw [sub_eq_add_neg, ← neg_one_mul, ← unifAvg_const_mul, ← unifAvg_add]
      congr 1
      funext r
      ring
    rw [e]
    refine (abs_unifAvg_le _).trans (le_of_eq ?_)
    congr 1
    funext r
    rw [abs_sub_comm]
  have hpt : ∀ r, |V r - unifAvg V| ≤ |V r - W r| + |W r - unifAvg W| +
      |unifAvg W - unifAvg V| := fun r ↦ by
    calc |V r - unifAvg V| = |(V r - W r) + (W r - unifAvg W) + (unifAvg W - unifAvg V)| := by
          ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _) |>.trans
          (le_of_eq (by ring))
  have h := unifAvg_mono hpt
  rw [unifAvg_add, unifAvg_add, unifAvg_const] at h
  linarith

/-- `(E|Z|)² ≤ E[Z²]`. -/
theorem sq_unifAvg_abs_le {R : Type*} [Fintype R] (Z : R → ℝ) :
    (unifAvg fun r ↦ |Z r|) ^ 2 ≤ unifAvg fun r ↦ Z r ^ 2 := by
  refine (sq_unifAvg_le _).trans (le_of_eq ?_)
  congr 1
  funext r
  rw [sq_abs]

/-- The bound `b^{-(k+1)} (b/2) Σ_c |w_{γ,c}|` on the node term of `γ = (k, t)`. -/
noncomputable def nodeBound {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) (ρ₀ : Scramble b m)
    (γ : Fin m × (Fin m → Option (Fin b))) : ℝ :=
  digWt b γ.1 * ((b : ℝ) / 2) * ∑ c, |nodeW d ρ₀ γ c|

/-- The node terms are bounded by `nodeBound`. -/
theorem abs_nodeTerm_le (hb : 0 < b) {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b)
    (ρ₀ : Scramble b m) (γ : Fin m × (Fin m → Option (Fin b))) (pm : Equiv.Perm (Fin b)) :
    |nodeTerm d ρ₀ γ pm| ≤ nodeBound d ρ₀ γ := by
  change |digWt b γ.1 * dform pm (nodeW d ρ₀ γ)| ≤ _
  rw [abs_mul, abs_of_pos (digWt_pos hb _), nodeBound, mul_assoc]
  exact mul_le_mul_of_nonneg_left (abs_dform_le pm _) (digWt_pos hb _).le

/-- **Second moments of the node bounds**: `E Σ_γ nodeBound² ≤ 2 b (b/2)⁴ b^{-2(m+1)} m n`. -/
theorem unifAvg_sum_sq_nodeBound_le (hb : 1 < b) {m : ℕ}
    {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) :
    unifAvg (fun ρ₀ : Scramble b m ↦ ∑ γ, nodeBound d ρ₀ γ ^ 2) ≤
      2 * b * ((b : ℝ) / 2) ^ 4 * digWt b m ^ 2 * (m * (b ^ m : ℕ)) := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  rw [unifAvg_sum]
  have hγ : ∀ γ : Fin m × (Fin m → Option (Fin b)),
      unifAvg (fun ρ₀ : Scramble b m ↦ nodeBound d ρ₀ γ ^ 2) ≤
        2 * b * ((b : ℝ) / 2) ^ 4 * digWt b m ^ 2 * ∑ c, ((cellSet d γ c).card : ℝ) := by
    intro γ
    have hhlo : m ≤ (m - (γ.1 : ℕ) - 1) + γ.1 + 1 := by
      have := γ.1.isLt
      omega
    have hpt : ∀ ρ₀ : Scramble b m, nodeBound d ρ₀ γ ^ 2 ≤
        ∑ c, (digWt b γ.1 ^ 2 * ((b : ℝ) / 2) ^ 2 * b) *
          wwin d ρ₀ γ c (m - γ.1 - 1) m ^ 2 := by
      intro ρ₀
      unfold nodeBound
      rw [mul_pow, mul_pow]
      have := sq_sum_abs_le (fun c ↦ nodeW d ρ₀ γ c)
      simp only [nodeW_eq_wwin hb0 hnet] at this ⊢
      calc digWt b γ.1 ^ 2 * ((b : ℝ) / 2) ^ 2 * (∑ c, |wwin d ρ₀ γ c (m - γ.1 - 1) m|) ^ 2
          ≤ digWt b γ.1 ^ 2 * ((b : ℝ) / 2) ^ 2 *
            (b * ∑ c, wwin d ρ₀ γ c (m - γ.1 - 1) m ^ 2) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by
            rw [Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun c _ ↦ by ring
    refine (unifAvg_mono hpt).trans ?_
    rw [unifAvg_sum]
    simp only [unifAvg_const_mul]
    calc ∑ c, digWt b γ.1 ^ 2 * ((b : ℝ) / 2) ^ 2 * b *
          unifAvg (fun ρ₀ : Scramble b m ↦ wwin d ρ₀ γ c (m - γ.1 - 1) m ^ 2)
        ≤ ∑ c, digWt b γ.1 ^ 2 * ((b : ℝ) / 2) ^ 2 * b *
          ((cellSet d γ c).card * (((b : ℝ) / 2) ^ 2 * (2 * digWt b (m - γ.1 - 1) ^ 2))) := by
          gcongr with c
          exact unifAvg_sq_wwin_le hb hnet γ c hhlo
      _ = 2 * b * ((b : ℝ) / 2) ^ 4 * (digWt b γ.1 * digWt b (m - γ.1 - 1)) ^ 2 *
            ∑ c, ((cellSet d γ c).card : ℝ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun c _ ↦ by ring
      _ = _ := by rw [digWt_mul_digWt]
  refine (Finset.sum_le_sum fun γ _ ↦ hγ γ).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, sum_card_cellSet_all]

/-- **Fourth moments of the node bounds**: `E Σ_γ nodeBound⁴ ≤ 12 b³ (b/2)⁸ b^{-4(m+1)} m n²`. -/
theorem unifAvg_sum_pow_four_nodeBound_le (hb : 1 < b) {m : ℕ}
    {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) :
    unifAvg (fun ρ₀ : Scramble b m ↦ ∑ γ, nodeBound d ρ₀ γ ^ 4) ≤
      12 * (b : ℝ) ^ 3 * ((b : ℝ) / 2) ^ 8 * digWt b m ^ 4 * (m * ((b ^ m : ℕ) : ℝ) ^ 2) := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  rw [unifAvg_sum]
  have hγ : ∀ γ : Fin m × (Fin m → Option (Fin b)),
      unifAvg (fun ρ₀ : Scramble b m ↦ nodeBound d ρ₀ γ ^ 4) ≤
        12 * (b : ℝ) ^ 3 * ((b : ℝ) / 2) ^ 8 * digWt b m ^ 4 *
          ∑ c, ((cellSet d γ c).card : ℝ) ^ 2 := by
    intro γ
    have hhlo : m ≤ (m - (γ.1 : ℕ) - 1) + γ.1 + 1 := by
      have := γ.1.isLt
      omega
    have hpt : ∀ ρ₀ : Scramble b m, nodeBound d ρ₀ γ ^ 4 ≤
        ∑ c, (digWt b γ.1 ^ 4 * ((b : ℝ) / 2) ^ 4 * (b : ℝ) ^ 3) *
          wwin d ρ₀ γ c (m - γ.1 - 1) m ^ 4 := by
      intro ρ₀
      unfold nodeBound
      rw [mul_pow, mul_pow]
      have := pow_four_sum_abs_le (fun c ↦ nodeW d ρ₀ γ c)
      simp only [nodeW_eq_wwin hb0 hnet] at this ⊢
      calc digWt b γ.1 ^ 4 * ((b : ℝ) / 2) ^ 4 * (∑ c, |wwin d ρ₀ γ c (m - γ.1 - 1) m|) ^ 4
          ≤ digWt b γ.1 ^ 4 * ((b : ℝ) / 2) ^ 4 *
            ((b : ℝ) ^ 3 * ∑ c, wwin d ρ₀ γ c (m - γ.1 - 1) m ^ 4) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by
            rw [Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun c _ ↦ by ring
    refine (unifAvg_mono hpt).trans ?_
    rw [unifAvg_sum]
    simp only [unifAvg_const_mul]
    calc ∑ c, digWt b γ.1 ^ 4 * ((b : ℝ) / 2) ^ 4 * (b : ℝ) ^ 3 *
          unifAvg (fun ρ₀ : Scramble b m ↦ wwin d ρ₀ γ c (m - γ.1 - 1) m ^ 4)
        ≤ ∑ c, digWt b γ.1 ^ 4 * ((b : ℝ) / 2) ^ 4 * (b : ℝ) ^ 3 *
          (3 * ((cellSet d γ c).card * (((b : ℝ) / 2) ^ 2 *
            (2 * digWt b (m - γ.1 - 1) ^ 2))) ^ 2) := by
          gcongr with c
          exact unifAvg_pow_four_wwin_le hb hnet γ c hhlo
      _ = 12 * (b : ℝ) ^ 3 * ((b : ℝ) / 2) ^ 8 * (digWt b γ.1 * digWt b (m - γ.1 - 1)) ^ 4 *
            ∑ c, ((cellSet d γ c).card : ℝ) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun c _ ↦ by ring
      _ = _ := by rw [digWt_mul_digWt]
  refine (Finset.sum_le_sum fun γ _ ↦ hγ γ).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Fintype.sum_prod_type]
  calc ∑ k : Fin m, ∑ t : Fin m → Option (Fin b), ∑ c, ((cellSet d (k, t) c).card : ℝ) ^ 2
      ≤ ∑ _k : Fin m, ((b ^ m : ℕ) : ℝ) ^ 2 := by
        refine Finset.sum_le_sum fun k _ ↦ ?_
        rw [← sum_card_cellSet d k, ← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
        exact sum_sq_le_sq_sum _ fun a _ ↦ Nat.cast_nonneg _
    _ = m * ((b ^ m : ℕ) : ℝ) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end RQMCMarkov.OwenScrambling

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Loh's CLT for a non-additive integrand: `x₀ x₁` on scrambled `(0,m,2)`-nets (post #2)

Post #2: with a digital net and Owen's nested uniform scramble "a standard CLT applies" (Loh
2003). `LohCLT` proves this, normalised by the standard deviation, for additive integrands,
where the error is a sum of independent terms given the scramble. For non-additive integrands
almost all of the variance comes from the scramble itself (`LohVariance`,
`tendsto_avg_variance_given_scramble_div`), and that argument fails. This module proves the CLT
for the simplest non-additive integrands, `f(x) = a x₀ x₁ + g₀(x₀) + g₁(x₁)` with `a ≠ 0` and
`C¹` coordinates `g_j` (the smooth integrands whose mixed derivative `∂²f/∂x₀∂x₁ = a` is a
non-zero constant), for every sequence of `(0,m,2)`-nets in base `b ≥ 2`
(`tendstoInDistribution_scrambledLaw_bilinAdd`), in particular for `x₀ x₁`
(`tendstoInDistribution_scrambledLaw_prodFn`) and the Hammersley nets
(`tendstoInDistribution_scrambledLaw_prodFn_hammersley`).

**The argument (not Loh's).** Loh uses Stein's method. Here the scramble of coordinate `0` is
conditioned on instead. Given `ρ₀`, the remainder-averaged error `S/n` of `x₀ x₁` is a sum of
independent centred terms, one for each node of the tree of coordinate `1`
(`LohGeneralProd.prodS_eq_sum_nodeTerm`), so a conditional Lindeberg (Lyapunov) bound applies
(`LohGeneralFinite.tendsto_unifAvg_cexp_nodeSum`). Its random conditional variance `V(ρ₀)`
concentrates (`LohGeneralConc`), because it is spread over the `m` levels of the tree of
coordinate `1`, which use asymptotically independent windows of levels of `ρ₀`. The normal limit
comes from the `m ≍ log n` levels, as Loh's does. The remainders and the additive part add a
vanishing share of the variance.

## Main results

* `unifAvg_fin_two`, `unifAvg_sq_prodS`: `E[S²] = E_{ρ₀} V(ρ₀)`.
* `integral_sq_sub_eq_variance_add`, `variance_scrambledLaw_eq_of_condMean`: the law of total
  variance for the scrambled estimator.
* `unifAvg_condVar_ge`: `E V ≥ (m (b-1)⁴/(64 b⁴) - 4)/n`, from Owen's lower bound
  (`LohVariance.variance_scrambledLaw_prodFn`).
* `tendsto_unifAvg_cexp_prodS`: the CLT for `S` itself, `S/√(E S²) ⇒ N(0,1)` in characteristic
  functions.
* `tendstoInDistribution_scrambledLaw_of_condMean`: the CLT for any Lipschitz `f` whose
  remainder-averaged error is `a S/n`.
* `tendstoInDistribution_scrambledLaw_bilinAdd`, `tendstoInDistribution_scrambledLaw_prodFn`,
  `tendstoInDistribution_scrambledLaw_prodFn_hammersley`: **Loh's CLT for `a x₀ x₁ + g₀(x₀) +
  g₁(x₁)`**, `(μ̂ - μ)/√Var(μ̂) ⇒ N(0,1)`.
-/

namespace RQMCMarkov.OwenScrambling

open MeasureTheory ProbabilityTheory Finset Filter Complex
open scoped Topology

variable {b : ℕ}

/-- Averages over pairs of scrambles are iterated averages. -/
theorem unifAvg_fin_two {X : Type*} [Fintype X] {𝕜 : Type*} [Field 𝕜] (G : (Fin 2 → X) → 𝕜) :
    unifAvg G = unifAvg (fun x₀ ↦ unifAvg (fun x₁ ↦ G ![x₀, x₁])) := by
  have hs : ∑ y, G y = ∑ x₀, ∑ x₁, G ![x₀, x₁] := by
    rw [← Fintype.sum_prod_type (f := fun p : X × X ↦ G ![p.1, p.2])]
    refine Fintype.sum_equiv (finTwoArrowEquiv X) _ _ fun y ↦ ?_
    congr 1
    funext i
    fin_cases i <;> rfl
  unfold unifAvg
  rw [hs, Fintype.card_fun, Fintype.card_fin, ← Finset.mul_sum, Nat.cast_pow]
  ring

/-- **The second moment of `S` given `ρ₀` is the conditional variance**:
`E_{ρ₁}[S²] = V(ρ₀)` (the node terms are independent and centred). -/
theorem unifAvg_sq_prodS {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b)
    (ρ₀ : Scramble b m) :
    unifAvg (fun ρ₁ : Scramble b m ↦ prodS d ![ρ₀, ρ₁] ^ 2) = condVar d ρ₀ := by
  have : Nonempty (Equiv.Perm (Fin b)) := ⟨Equiv.refl _⟩
  have e : (fun ρ₁ : Scramble b m ↦ prodS d ![ρ₀, ρ₁] ^ 2) = fun ρ₁ ↦
      (∑ γ ∈ (Finset.univ : Finset (Fin m × (Fin m → Option (Fin b)))),
        nodeTerm d ρ₀ γ (ρ₁ (id γ))) ^ 2 := by
    funext ρ₁
    rw [prodS_eq_sum_nodeTerm]
    rfl
  rw [e, unifAvg_sq_sum_eq (Set.injOn_id _) (fun γ _ ↦ unifAvg_nodeTerm d ρ₀ γ)]
  rfl

/-- `E[(X - c)²] = Var X + (E X - c)²`. -/
theorem integral_sq_sub_eq_variance_add {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}
    [IsProbabilityMeasure Q] {X : Ω → ℝ} (hX : MemLp X 2 Q) (c : ℝ) :
    ∫ ω, (X ω - c) ^ 2 ∂Q = Var[X; Q] + (∫ ω, X ω ∂Q - c) ^ 2 := by
  have hX1 : Integrable X Q := hX.integrable one_le_two
  have hX2 : Integrable (fun ω ↦ X ω ^ 2) Q := hX.integrable_sq
  rw [variance_eq_sub hX]
  have e : (fun ω ↦ (X ω - c) ^ 2) = fun ω ↦ (X ω ^ 2 + (-2 * c) * X ω) + c ^ 2 :=
    funext fun ω ↦ by ring
  rw [e, integral_add (f := fun ω ↦ X ω ^ 2 + (-2 * c) * X ω) (g := fun _ ↦ c ^ 2)
    (hX2.add (hX1.const_mul _)) (integrable_const _),
    integral_add (f := fun ω ↦ X ω ^ 2) (g := fun ω ↦ (-2 * c) * X ω) hX2 (hX1.const_mul _),
    integral_const_mul, integral_const, probReal_univ, one_smul]
  change _ = ∫ ω, X ω ^ 2 ∂Q - (∫ ω, X ω ∂Q) ^ 2 + _
  ring

/-- **The law of total variance for the scrambled estimator**: if the remainder-averaged
estimator is `E[μ̂ | ρ] = μ + a S(ρ)`, then `Var(μ̂) = E_ρ[(a S)²] + E_ρ[Var(μ̂ | ρ)]`. -/
theorem variance_scrambledLaw_eq_of_condMean (hb : 0 < b) {m : ℕ}
    {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b} {f : (Fin 2 → ℝ) → ℝ} (hfm : Measurable f)
    (hf : MemLp f 2 (uniformCube 2)) {a : ℝ} {S : (Fin 2 → Scramble b m) → ℝ}
    (hmean : ∀ ρ, ∫ u, scrambledEstimate f d ρ u ∂(remLaw 2 (b ^ m)) =
      ∫ x, f x ∂(uniformCube 2) + a * S ρ) :
    Var[fun x ↦ x; scrambledLaw f d] = unifAvg (fun ρ ↦ (a * S ρ) ^ 2) +
      unifAvg (fun ρ ↦ Var[scrambledEstimate f d ρ; remLaw 2 (b ^ m)]) := by
  have hQ := isProbabilityMeasure_remLaw 2 (b ^ m)
  rw [variance_scrambledLaw_eq_sum hb (Nat.pow_pos hb).ne' hfm hf d, ← unifAvg_add]
  change unifAvg _ = _
  congr 1
  funext ρ
  rw [integral_sq_sub_eq_variance_add (memLp_scrambledEstimate hb hf d ρ), hmean ρ]
  ring

/-- **The remainders' share of the variance**: for `f` `L`-Lipschitz on the cube,
`E_ρ[Var(μ̂ | ρ)] ≤ 4 L² / n³`. -/
theorem unifAvg_variance_le (hb : 0 < b) {m : ℕ} {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b}
    {f : (Fin 2 → ℝ) → ℝ} (hf : MemLp f 2 (uniformCube 2)) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      |f x - f x'| ≤ L * ∑ j, |x j - x' j|) :
    unifAvg (fun ρ ↦ Var[scrambledEstimate f d ρ; remLaw 2 (b ^ m)]) ≤
      4 * L ^ 2 * (((b : ℝ) ^ m) ^ 3)⁻¹ := by
  have hbm : (0 : ℝ) < (b : ℝ) ^ m := pow_pos (Nat.cast_pos.2 hb) m
  have h := avg_variance_scrambledEstimate hb (Nat.pow_pos hb).ne' hf d
  have hc := cellResVar_le (D := m) hb hf hL0 hL
  unfold unifAvg
  rw [h, Nat.cast_pow]
  calc ((b : ℝ) ^ m)⁻¹ * cellResVar b m f ≤ ((b : ℝ) ^ m)⁻¹ * (L * 2 * ((b : ℝ) ^ m)⁻¹) ^ 2 :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hc) (inv_nonneg.2 hbm.le)
    _ = 4 * L ^ 2 * (((b : ℝ) ^ m) ^ 3)⁻¹ := by
        field_simp
        ring

/-- `∫ x₀ x₁ = 1/4` over the unit square. -/
theorem integral_prodFn : ∫ x, prodFn x ∂(uniformCube 2) = 1 / 4 := by
  have := isProbabilityMeasure_uniformIco
  have h := integral_pi_eval_mul (ν := uniformIco) (g := fun x : ℝ ↦ x) (h := fun x : ℝ ↦ x)
    aestronglyMeasurable_id aestronglyMeasurable_id (j := (0 : Fin 2)) (k := 1) (by decide)
  rw [integral_id_uniformIco] at h
  unfold prodFn
  rw [h]
  norm_num

/-- `x₀ x₁` is `1`-Lipschitz on the cube in the `ℓ¹` distance. -/
theorem abs_prodFn_sub_le {x x' : Fin 2 → ℝ} (hx : ∀ j, x j ∈ Set.Ico (0 : ℝ) 1)
    (hx' : ∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) :
    |prodFn x - prodFn x'| ≤ 1 * ∑ j, |x j - x' j| := by
  rw [prodFn, prodFn, Fin.sum_univ_two, one_mul]
  have e : x 0 * x 1 - x' 0 * x' 1 = x 0 * (x 1 - x' 1) + x' 1 * (x 0 - x' 0) := by ring
  rw [e]
  have h0 : |x 0| ≤ 1 := abs_le.2 ⟨by linarith [(hx 0).1], (hx 0).2.le⟩
  have h1 : |x' 1| ≤ 1 := abs_le.2 ⟨by linarith [(hx' 1).1], (hx' 1).2.le⟩
  calc |x 0 * (x 1 - x' 1) + x' 1 * (x 0 - x' 0)|
      ≤ |x 0| * |x 1 - x' 1| + |x' 1| * |x 0 - x' 0| := by
        rw [← abs_mul, ← abs_mul]
        exact abs_add_le _ _
    _ ≤ 1 * |x 1 - x' 1| + 1 * |x 0 - x' 0| := by gcongr
    _ = |x 0 - x' 0| + |x 1 - x' 1| := by ring

/-- `E_ρ[S²] = E_{ρ₀} V(ρ₀)`. -/
theorem unifAvg_sq_prodS_eq {m n : ℕ} (d : Fin n → Fin 2 → Fin m → Fin b) :
    unifAvg (fun ρ : Fin 2 → Scramble b m ↦ prodS d ρ ^ 2) =
      unifAvg (fun ρ₀ : Scramble b m ↦ condVar d ρ₀) := by
  rw [unifAvg_fin_two]
  congr 1
  funext ρ₀
  exact unifAvg_sq_prodS d ρ₀

/-- **The mean conditional variance has order `m/n`** (Owen 1997b's lower bound for `x₀ x₁`):
`E V ≥ (m (b-1)⁴/(64 b⁴) - 4)/n`. -/
theorem unifAvg_condVar_ge (hb : 1 < b) {m : ℕ} (hm : 1 ≤ m)
    {d : Fin (b ^ m) → Fin 2 → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) :
    (m * (((b : ℝ) - 1) ^ 4 / (64 * (b : ℝ) ^ 4)) - 4) * ((b : ℝ) ^ m)⁻¹ ≤
      unifAvg (fun ρ₀ : Scramble b m ↦ condVar d ρ₀) := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hN : (0 : ℝ) < (b : ℝ) ^ m := pow_pos (Nat.cast_pos.2 hb0) m
  have hvar := variance_scrambledLaw_eq_of_condMean hb0 measurable_prodFn memLp_prodFn (d := d)
    (a := 1) (S := fun ρ ↦ prodS d ρ / ((b ^ m : ℕ) : ℝ)) fun ρ ↦ by
      rw [integral_scrambledEstimate_prodFn hb0 hnet ρ, integral_prodFn, one_mul]
  have hlow := (variance_scrambledLaw_prodFn hb hm hnet).1
  have hrem := unifAvg_variance_le hb0 memLp_prodFn (d := d) zero_le_one
    fun x x' hx hx' ↦ abs_prodFn_sub_le hx hx'
  have hS : unifAvg (fun ρ : Fin 2 → Scramble b m ↦ (1 * (prodS d ρ / ((b ^ m : ℕ) : ℝ))) ^ 2) =
      ((b : ℝ) ^ m)⁻¹ ^ 2 * unifAvg (fun ρ₀ : Scramble b m ↦ condVar d ρ₀) := by
    rw [← unifAvg_sq_prodS_eq, ← unifAvg_const_mul]
    congr 1
    funext ρ
    rw [Nat.cast_pow]
    field_simp
  rw [hvar, hS] at hlow
  have h3 : (b : ℝ) ^ (3 * m) = ((b : ℝ) ^ m) ^ 3 := by rw [← pow_mul, mul_comm]
  rw [h3] at hlow
  set E := unifAvg (fun ρ₀ : Scramble b m ↦ condVar d ρ₀)
  set c := (m : ℝ) * (((b : ℝ) - 1) ^ 4 / (64 * (b : ℝ) ^ 4))
  set N := (b : ℝ) ^ m
  have hrem' : unifAvg (fun ρ ↦ Var[scrambledEstimate prodFn d ρ; remLaw 2 (b ^ m)]) ≤
      4 * (N ^ 3)⁻¹ := by simpa using hrem
  have h4 : c ≤ N ^ 3 * (N⁻¹ ^ 2 * E) + 4 := by
    have := mul_le_mul_of_nonneg_left hrem' (pow_nonneg hN.le 3)
    rw [show N ^ 3 * (4 * (N ^ 3)⁻¹) = 4 by field_simp] at this
    nlinarith
  have h5 : N ^ 3 * (N⁻¹ ^ 2 * E) = N * E := by
    field_simp
  rw [h5] at h4
  rw [show (c - 4) * N⁻¹ = (c - 4) / N by ring, div_le_iff₀ hN]
  linarith

/-- `b^{-(m+1)} b^m = b^{-1}`. -/
theorem digWt_mul_pow (hb : 0 < b) (m : ℕ) : digWt b m * (b : ℝ) ^ m = (b : ℝ)⁻¹ := by
  have : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hb.ne'
  unfold digWt
  rw [pow_succ]
  field_simp

/-- The integer square root tends to infinity. -/
theorem tendsto_sqrt_nat_atTop : Tendsto Nat.sqrt atTop atTop := by
  refine tendsto_atTop_atTop.2 fun N ↦ ⟨N * N, fun m hm ↦ ?_⟩
  exact Nat.le_sqrt.2 hm

/-- `⌊√m⌋ / m → 0`. -/
theorem tendsto_sqrt_nat_div : Tendsto (fun m : ℕ ↦ (Nat.sqrt m : ℝ) / m) atTop (𝓝 0) := by
  have h : Tendsto (fun m : ℕ ↦ ((Nat.sqrt m : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp tendsto_sqrt_nat_atTop)
  refine squeeze_zero' (Eventually.of_forall fun m ↦ by positivity) ?_ h
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hs : 0 < Nat.sqrt m := Nat.sqrt_pos.2 hm
  have hsq : Nat.sqrt m * Nat.sqrt m ≤ m := Nat.sqrt_le m
  have hs' : (0 : ℝ) < Nat.sqrt m := Nat.cast_pos.2 hs
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hsq' : (Nat.sqrt m : ℝ) * Nat.sqrt m ≤ m := by exact_mod_cast hsq
  rw [div_le_iff₀ hm', inv_mul_eq_div, le_div_iff₀ hs']
  linarith

/-- **The CLT for the remainder-averaged error `S` of `x₀ x₁`**: for every sequence of
`(0,m,2)`-nets in base `b ≥ 2` and `τ_m → t`, the characteristic function of
`S/√(E S²)` (with `E S² = E_{ρ₀} V(ρ₀)`) at `τ_m` tends to `e^{-t²/2}`. -/
theorem tendsto_unifAvg_cexp_prodS (hb : 1 < b)
    (d : (m : ℕ) → Fin (b ^ m) → Fin 2 → Fin m → Fin b)
    (hnet : ∀ m, IsNet b 0 m fun i j ↦ digitPoint (d m i j) 0) {τ : ℕ → ℝ} {t : ℝ}
    (hτ : Tendsto τ atTop (𝓝 t)) :
    Tendsto (fun m ↦ unifAvg (fun ρ : Fin 2 → Scramble b m ↦
      cexp ((((τ m * prodS (d m) ρ) /
        Real.sqrt (unifAvg (fun ρ₀ : Scramble b m ↦ condVar (d m) ρ₀)) : ℝ) : ℂ) * I)))
      atTop (𝓝 ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ)) := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hbR : (0 : ℝ) < b := Nat.cast_pos.2 hb0
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  have : Nonempty (Equiv.Perm (Fin b)) := ⟨Equiv.refl _⟩
  set c₁ : ℝ := ((b : ℝ) - 1) ^ 4 / (64 * (b : ℝ) ^ 4) with hc₁
  have hc₁ : 0 < c₁ := by positivity
  set κ : ℝ := c₁ / 2 with hκ
  have hκ0 : 0 < κ := by positivity
  set h : ℝ := (b : ℝ) / 2 with hh
  set s2 : ℕ → ℝ := fun m ↦ unifAvg (fun ρ₀ : Scramble b m ↦ condVar (d m) ρ₀) with hs2
  set N : ℕ → ℝ := fun m ↦ (b : ℝ) ^ m with hN
  have hN0 : ∀ m, 0 < N m := fun m ↦ pow_pos hbR m
  have hNnat : ∀ m, ((b ^ m : ℕ) : ℝ) = N m := fun m ↦ by rw [Nat.cast_pow]
  have hdw : ∀ m, digWt b m = (b : ℝ)⁻¹ * (N m)⁻¹ := fun m ↦ by
    change ((b : ℝ) ^ (m + 1))⁻¹ = (b : ℝ)⁻¹ * ((b : ℝ) ^ m)⁻¹
    rw [pow_succ, mul_inv, mul_comm]
  -- the lower bound on the mean conditional variance
  have hlow : ∀ᶠ m in atTop, κ * m * (N m)⁻¹ ≤ s2 m ∧ 1 ≤ m := by
    filter_upwards [eventually_ge_atTop (⌈8 / c₁⌉₊ + 1)] with m hm
    have hm1 : 1 ≤ m := le_trans (Nat.le_add_left 1 _) hm
    refine ⟨?_, hm1⟩
    have h := unifAvg_condVar_ge hb hm1 (hnet m)
    have hm8 : 8 / c₁ ≤ m := by
      have := Nat.le_ceil (8 / c₁)
      have : ((⌈8 / c₁⌉₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
      push_cast at this
      linarith
    have hmc : 8 ≤ m * c₁ := by rwa [div_le_iff₀ hc₁] at hm8
    refine le_trans ?_ h
    rw [hκ]
    have : 0 ≤ (N m)⁻¹ := inv_nonneg.2 (hN0 m).le
    change c₁ / 2 * m * (N m)⁻¹ ≤ (m * c₁ - 4) * (N m)⁻¹
    nlinarith
  have hs2pos : ∀ᶠ m in atTop, 0 < s2 m := by
    filter_upwards [hlow] with m hm
    have : 0 < κ * m * (N m)⁻¹ := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm.2
      have := inv_pos.2 (hN0 m)
      positivity
    linarith [hm.1]
  have hs2nn : ∀ m, 0 ≤ s2 m := fun m ↦ unifAvg_nonneg fun ρ₀ ↦
    Finset.sum_nonneg fun γ _ ↦ unifAvg_nonneg fun pm ↦ sq_nonneg _
  have hsq : ∀ m, Real.sqrt (s2 m) ^ 2 = s2 m := fun m ↦ Real.sq_sqrt (hs2nn m)
  -- the concentration of the conditional variance
  set J : ℕ → ℕ := Nat.sqrt with hJ
  set K1 : ℝ := 5 * h ^ 4 * (b : ℝ)⁻¹ / κ with hK1
  set K2 : ℝ := 32 * h ^ 8 * ((b : ℝ)⁻¹) ^ 2 / κ ^ 2 with hK2
  have hconc : ∀ᶠ m in atTop, unifAvg (fun ρ₀ : Scramble b m ↦
      |condVar (d m) ρ₀ / s2 m - 1|) ≤
      2 * (K1 * ((b : ℝ) ^ J m)⁻¹) + Real.sqrt (K2 * (J m / m)) := by
    filter_upwards [hlow, hs2pos] with m hm hspos
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.2
    have hmpos : (0 : ℝ) < m := by linarith
    set V : Scramble b m → ℝ := fun ρ₀ ↦ condVar (d m) ρ₀ with hV
    set W : Scramble b m → ℝ := fun ρ₀ ↦ condVarWin (d m) ρ₀ (J m) with hW
    have e1 : unifAvg (fun ρ₀ : Scramble b m ↦ |condVar (d m) ρ₀ / s2 m - 1|) =
        unifAvg (fun ρ₀ ↦ |V ρ₀ - unifAvg V|) / s2 m := by
      rw [div_eq_mul_inv, ← unifAvg_mul_const]
      congr 1
      funext ρ₀
      rw [hV]
      change _ = |condVar (d m) ρ₀ - s2 m| * (s2 m)⁻¹
      rw [← abs_of_pos (inv_pos.2 hspos), ← abs_mul, sub_mul, mul_inv_cancel₀ hspos.ne',
        div_eq_mul_inv]
    rw [e1]
    have hsplit := unifAvg_abs_sub_avg_le V W
    have hA := unifAvg_abs_condVar_sub_le hb (hnet m) (J m)
    have hB := unifAvg_sq_condVarWin_sub_le hb (hnet m) (J m)
    have hB' := (sq_unifAvg_abs_le (fun ρ₀ ↦ W ρ₀ - unifAvg W)).trans hB
    rw [hNnat, hdw] at hA hB'
    -- the first part
    have h1 : unifAvg (fun ρ₀ ↦ |V ρ₀ - W ρ₀|) / s2 m ≤ K1 * ((b : ℝ) ^ J m)⁻¹ := by
      rw [div_le_iff₀ hspos]
      refine hA.trans ?_
      have : K1 * ((b : ℝ) ^ J m)⁻¹ * (κ * m * (N m)⁻¹) ≤ K1 * ((b : ℝ) ^ J m)⁻¹ * s2 m :=
        mul_le_mul_of_nonneg_left hm.1 (by positivity)
      refine le_trans (le_of_eq ?_) this
      rw [hK1, hh]
      have : N m ≠ 0 := (hN0 m).ne'
      field_simp
    -- the second part
    have h2 : unifAvg (fun ρ₀ ↦ |W ρ₀ - unifAvg W|) / s2 m ≤ Real.sqrt (K2 * (J m / m)) := by
      refine Real.le_sqrt_of_sq_le ?_
      rw [div_pow, div_le_iff₀ (by positivity)]
      refine hB'.trans ?_
      have hs2sq : (κ * m * (N m)⁻¹) ^ 2 ≤ s2 m ^ 2 :=
        pow_le_pow_left₀ (by have := inv_pos.2 (hN0 m); positivity) hm.1 2
      have : K2 * (J m / m) * (κ * m * (N m)⁻¹) ^ 2 ≤ K2 * (J m / m) * s2 m ^ 2 :=
        mul_le_mul_of_nonneg_left hs2sq (by positivity)
      refine le_trans (le_of_eq ?_) this
      rw [hK2, hh]
      have : N m ≠ 0 := (hN0 m).ne'
      field_simp
      ring
    calc unifAvg (fun ρ₀ ↦ |V ρ₀ - unifAvg V|) / s2 m
        ≤ (2 * unifAvg (fun ρ₀ ↦ |V ρ₀ - W ρ₀|) + unifAvg (fun ρ₀ ↦ |W ρ₀ - unifAvg W|)) /
          s2 m := div_le_div_of_nonneg_right hsplit hspos.le
      _ = 2 * (unifAvg (fun ρ₀ ↦ |V ρ₀ - W ρ₀|) / s2 m) +
          unifAvg (fun ρ₀ ↦ |W ρ₀ - unifAvg W|) / s2 m := by ring
      _ ≤ 2 * (K1 * ((b : ℝ) ^ J m)⁻¹) + Real.sqrt (K2 * (J m / m)) := by linarith
  have hV : Tendsto (fun m ↦ unifAvg fun ρ₀ : Scramble b m ↦
      |(∑ γ, unifAvg fun pm ↦ nodeTerm (d m) ρ₀ γ pm ^ 2) /
        Real.sqrt (s2 m) ^ 2 - 1|) atTop (𝓝 0) := by
    have hlim : Tendsto (fun m ↦ 2 * (K1 * ((b : ℝ) ^ J m)⁻¹) + Real.sqrt (K2 * (J m / m)))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun m ↦ ((b : ℝ) ^ J m)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop_atTop_of_one_lt
          (Nat.one_lt_cast.2 hb)).comp tendsto_sqrt_nat_atTop)
      have h2 : Tendsto (fun m ↦ Real.sqrt (K2 * (J m / m))) atTop (𝓝 0) := by
        have := (Real.continuous_sqrt.tendsto _).comp (tendsto_sqrt_nat_div.const_mul K2)
        rwa [mul_zero, Real.sqrt_zero] at this
      simpa only [mul_zero, zero_add] using (h1.const_mul K1).const_mul 2 |>.add h2
    refine squeeze_zero' (Eventually.of_forall fun m ↦ unifAvg_nonneg fun ρ₀ ↦ abs_nonneg _)
      ?_ hlim
    filter_upwards [hconc] with m hm
    rw [hsq]
    exact hm
  -- the moments of the node bounds
  have hM2 : ∀ᶠ m in atTop, (unifAvg fun ρ₀ : Scramble b m ↦
      ∑ γ, (nodeBound (d m) ρ₀ γ / Real.sqrt (s2 m)) ^ 2) ≤ 2 * h ^ 4 * (b : ℝ)⁻¹ / κ := by
    filter_upwards [hlow, hs2pos] with m hm hspos
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.2
    have e : (fun ρ₀ : Scramble b m ↦ ∑ γ, (nodeBound (d m) ρ₀ γ / Real.sqrt (s2 m)) ^ 2) =
        fun ρ₀ ↦ (∑ γ, nodeBound (d m) ρ₀ γ ^ 2) * (s2 m)⁻¹ := by
      funext ρ₀
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun γ _ ↦ by rw [div_pow, hsq, div_eq_mul_inv]
    rw [e, unifAvg_mul_const, ← div_eq_mul_inv, div_le_iff₀ hspos]
    have hA := unifAvg_sum_sq_nodeBound_le hb (hnet m)
    rw [hNnat, hdw] at hA
    refine hA.trans ?_
    have : 2 * h ^ 4 * (b : ℝ)⁻¹ / κ * (κ * m * (N m)⁻¹) ≤
        2 * h ^ 4 * (b : ℝ)⁻¹ / κ * s2 m := mul_le_mul_of_nonneg_left hm.1 (by positivity)
    refine le_trans (le_of_eq ?_) this
    rw [hh]
    have : N m ≠ 0 := (hN0 m).ne'
    field_simp
  have hM4 : Tendsto (fun m ↦ unifAvg fun ρ₀ : Scramble b m ↦
      ∑ γ, (nodeBound (d m) ρ₀ γ / Real.sqrt (s2 m)) ^ 4) atTop (𝓝 0) := by
    have hlim : Tendsto (fun m : ℕ ↦ 12 * h ^ 8 * (b : ℝ)⁻¹ / κ ^ 2 * (m : ℝ)⁻¹) atTop
        (𝓝 0) := by
      have := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul
        (12 * h ^ 8 * (b : ℝ)⁻¹ / κ ^ 2)
      rw [mul_zero] at this
      exact this
    refine squeeze_zero' (Eventually.of_forall fun m ↦ unifAvg_nonneg fun ρ₀ ↦
      Finset.sum_nonneg fun γ _ ↦ by positivity) ?_ hlim
    filter_upwards [hlow, hs2pos] with m hm hspos
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.2
    have e : (fun ρ₀ : Scramble b m ↦ ∑ γ, (nodeBound (d m) ρ₀ γ / Real.sqrt (s2 m)) ^ 4) =
        fun ρ₀ ↦ (∑ γ, nodeBound (d m) ρ₀ γ ^ 4) * ((s2 m) ^ 2)⁻¹ := by
      funext ρ₀
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun γ _ ↦ ?_
      rw [div_pow, show Real.sqrt (s2 m) ^ 4 = (Real.sqrt (s2 m) ^ 2) ^ 2 by ring, hsq,
        div_eq_mul_inv]
    rw [e, unifAvg_mul_const, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    have hA := unifAvg_sum_pow_four_nodeBound_le hb (hnet m)
    rw [hNnat, hdw] at hA
    refine hA.trans ?_
    have hs2sq : (κ * m * (N m)⁻¹) ^ 2 ≤ s2 m ^ 2 :=
      pow_le_pow_left₀ (by have := inv_pos.2 (hN0 m); positivity) hm.1 2
    have : 12 * h ^ 8 * (b : ℝ)⁻¹ / κ ^ 2 * (m : ℝ)⁻¹ * (κ * m * (N m)⁻¹) ^ 2 ≤
        12 * h ^ 8 * (b : ℝ)⁻¹ / κ ^ 2 * (m : ℝ)⁻¹ * s2 m ^ 2 :=
      mul_le_mul_of_nonneg_left hs2sq (by positivity)
    refine le_trans (le_of_eq ?_) this
    rw [hh]
    have : N m ≠ 0 := (hN0 m).ne'
    have : (m : ℝ) ≠ 0 := by positivity
    field_simp
  have hsp : ∀ᶠ m in atTop, 0 < Real.sqrt (s2 m) := by
    filter_upwards [hs2pos] with m hm
    exact Real.sqrt_pos.2 hm
  have hmain := tendsto_unifAvg_cexp_nodeSum (R := fun m ↦ Scramble b m)
    (Γ := fun m ↦ Fin m × (Fin m → Option (Fin b))) (P := Equiv.Perm (Fin b))
    (fun m ↦ nodeTerm (d m)) (fun m ρ₀ γ ↦ unifAvg_nodeTerm (d m) ρ₀ γ) hsp hV
    (M := fun m ↦ nodeBound (d m)) (fun m ρ₀ γ pm ↦ abs_nodeTerm_le hb0 (d m) ρ₀ γ pm) hM2 hM4 hτ
  refine hmain.congr fun m ↦ ?_
  rw [unifAvg_fin_two]
  congr 1
  funext ρ₀
  congr 1
  funext ρ₁
  rw [prodS_eq_sum_nodeTerm]
  rfl

/-- **The lower bound on `E S²`, eventually**: `E_{ρ₀} V(ρ₀) ≥ κ m / n` with
`κ = (b-1)⁴/(128 b⁴)` for all large `m`. -/
theorem eventually_unifAvg_condVar_ge (hb : 1 < b)
    (d : (m : ℕ) → Fin (b ^ m) → Fin 2 → Fin m → Fin b)
    (hnet : ∀ m, IsNet b 0 m fun i j ↦ digitPoint (d m i j) 0) :
    ∀ᶠ m in atTop, ((b : ℝ) - 1) ^ 4 / (64 * (b : ℝ) ^ 4) / 2 * m * ((b : ℝ) ^ m)⁻¹ ≤
      unifAvg (fun ρ₀ : Scramble b m ↦ condVar (d m) ρ₀) ∧ 1 ≤ m := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hbR : (0 : ℝ) < b := Nat.cast_pos.2 hb0
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  set c₁ : ℝ := ((b : ℝ) - 1) ^ 4 / (64 * (b : ℝ) ^ 4) with hc₁
  have hc₁ : 0 < c₁ := by positivity
  filter_upwards [eventually_ge_atTop (⌈8 / c₁⌉₊ + 1)] with m hm
  have hm1 : 1 ≤ m := le_trans (Nat.le_add_left 1 _) hm
  refine ⟨?_, hm1⟩
  have h := unifAvg_condVar_ge hb hm1 (hnet m)
  have hm8 : 8 / c₁ ≤ m := by
    have := Nat.le_ceil (8 / c₁)
    have : ((⌈8 / c₁⌉₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
    push_cast at this
    linarith
  have hmc : 8 ≤ m * c₁ := by rwa [div_le_iff₀ hc₁] at hm8
  refine le_trans ?_ h
  have : 0 ≤ ((b : ℝ) ^ m)⁻¹ := inv_nonneg.2 (pow_pos hbR m).le
  nlinarith

/-- **Integrals against a mixture law, complex-valued**:
`∫ g d(mixLaw Q Φ) = E_ρ ∫ g(Φ ρ u) dQ(u)`. -/
theorem integral_mixLaw_complex {R E : Type*} [Fintype R] [MeasurableSpace E] {Q : Measure E}
    {Φ : R → E → ℝ} (hΦ : ∀ ρ, Measurable (Φ ρ)) {g : ℝ → ℂ} (hg : Continuous g)
    (hint : ∀ ρ, Integrable (fun u ↦ g (Φ ρ u)) Q) :
    ∫ x, g x ∂(mixLaw Q Φ) = unifAvg (fun ρ ↦ ∫ u, g (Φ ρ u) ∂Q) := by
  have hgi : ∀ ρ, Integrable g (Q.map (Φ ρ)) := fun ρ ↦
    (integrable_map_measure hg.aestronglyMeasurable (hΦ ρ).aemeasurable).2 (hint ρ)
  unfold mixLaw unifAvg
  rw [integral_smul_measure, integral_finsetSum_measure fun ρ _ ↦ hgi ρ, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, Complex.real_smul]
  push_cast
  congr 1
  exact Finset.sum_congr rfl fun ρ _ ↦ integral_map (hΦ ρ).aemeasurable hg.aestronglyMeasurable

/-- `‖e^{ix} - e^{iy}‖ ≤ |x - y|`. -/
theorem norm_cexp_sub_cexp_le (x y : ℝ) :
    ‖cexp ((x : ℂ) * I) - cexp ((y : ℂ) * I)‖ ≤ |x - y| := by
  have e : cexp ((x : ℂ) * I) - cexp ((y : ℂ) * I) =
      cexp ((y : ℂ) * I) * (cexp (I * ((x - y : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y)
  rwa [Real.norm_eq_abs] at this

/-- **Jensen for the absolute deviation**: `(E|X - E X|)² ≤ Var X`. -/
theorem sq_integral_abs_sub_le_variance {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}
    [IsProbabilityMeasure Q] {X : Ω → ℝ} (hX : MemLp X 2 Q) :
    (∫ ω, |X ω - ∫ ω', X ω' ∂Q| ∂Q) ^ 2 ≤ Var[X; Q] := by
  have hY : MemLp (fun ω ↦ |X ω - ∫ ω', X ω' ∂Q|) 2 Q := (hX.sub (memLp_const _)).abs
  have hv := variance_nonneg (fun ω ↦ |X ω - ∫ ω', X ω' ∂Q|) Q
  rw [variance_eq_sub hY] at hv
  rw [variance_eq_integral hX.aestronglyMeasurable.aemeasurable]
  have e : ∫ ω, ((fun ω ↦ |X ω - ∫ ω', X ω' ∂Q|) ^ 2) ω ∂Q =
      ∫ ω, (X ω - ∫ ω', X ω' ∂Q) ^ 2 ∂Q :=
    integral_congr_ae (Eventually.of_forall fun ω ↦ by simp only [Pi.pow_apply, sq_abs])
  change 0 ≤ ∫ ω, ((fun ω ↦ |X ω - ∫ ω', X ω' ∂Q|) ^ 2) ω ∂Q -
    (∫ ω, |X ω - ∫ ω', X ω' ∂Q| ∂Q) ^ 2 at hv
  rw [e] at hv
  linarith

/-- **Loh's CLT from the conditional-mean structure** (post #2, Loh 2003, `s = 2`): for every
sequence of `(0,m,2)`-nets in base `b ≥ 2` and every measurable `f ∈ L²`, Lipschitz on the
cube, whose remainder-averaged scrambled estimator is `E[μ̂ | ρ] = μ + a S(ρ)/n` with `a ≠ 0`
and `S` the error sum of `x₀ x₁`, the estimator standardised by its own standard deviation is
asymptotically normal: `(μ̂ - μ)/√Var(μ̂) ⇒ N(0,1)`. -/
theorem tendstoInDistribution_scrambledLaw_of_condMean (hb : 1 < b)
    (d : (m : ℕ) → Fin (b ^ m) → Fin 2 → Fin m → Fin b)
    (hnet : ∀ m, IsNet b 0 m fun i j ↦ digitPoint (d m i j) 0)
    {f : (Fin 2 → ℝ) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (uniformCube 2)) {L : ℝ}
    (hL0 : 0 ≤ L)
    (hL : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) → (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      |f x - f x'| ≤ L * ∑ j, |x j - x' j|) {a : ℝ} (ha : a ≠ 0)
    (hmean : ∀ m ρ, ∫ u, scrambledEstimate f (d m) ρ u ∂(remLaw 2 (b ^ m)) =
      ∫ x, f x ∂(uniformCube 2) + a * (prodS (d m) ρ / ((b ^ m : ℕ) : ℝ)))
    [∀ m, IsProbabilityMeasure (scrambledLaw f (d m))]
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun m x ↦ (x - ∫ y, f y ∂(uniformCube 2)) /
      Real.sqrt Var[fun x ↦ x; scrambledLaw f (d m)]) atTop Z
      (fun m ↦ scrambledLaw f (d m)) P' where
  forall_aemeasurable m := ((measurable_id.sub_const _).div_const _).aemeasurable
  aemeasurable_limit := hZ.aemeasurable
  tendsto := by
    have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
    have hbR : (0 : ℝ) < b := Nat.cast_pos.2 hb0
    have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
      have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
      linarith
    have hQ : ∀ m, IsProbabilityMeasure (remLaw 2 (b ^ m)) := fun m ↦
      isProbabilityMeasure_remLaw 2 _
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t ↦ ?_
    change Tendsto (fun m ↦ charFun ((scrambledLaw f (d m)).map fun x ↦
      (x - ∫ y, f y ∂(uniformCube 2)) / Real.sqrt Var[fun x ↦ x; scrambledLaw f (d m)]) t)
      atTop (𝓝 (charFun (P'.map Z) t))
    have htarget : charFun (P'.map Z) t = ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) := by
      rw [hZ.map_eq, charFun_gaussianReal, Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [htarget]
    -- notation
    set μ := ∫ y, f y ∂(uniformCube 2) with hμ
    set N : ℕ → ℝ := fun m ↦ ((b ^ m : ℕ) : ℝ) with hN
    set s2 : ℕ → ℝ := fun m ↦ unifAvg (fun ρ₀ : Scramble b m ↦ condVar (d m) ρ₀) with hs2
    set v : ℕ → ℝ := fun m ↦ unifAvg (fun ρ : Fin 2 → Scramble b m ↦
      Var[scrambledEstimate f (d m) ρ; remLaw 2 (b ^ m)]) with hv
    set A : ℕ → ℝ := fun m ↦ a ^ 2 * (N m)⁻¹ ^ 2 * s2 m with hA
    set σ : ℕ → ℝ := fun m ↦ Real.sqrt Var[fun x ↦ x; scrambledLaw f (d m)] with hσ
    have hN0 : ∀ m, 0 < N m := fun m ↦ Nat.cast_pos.2 (Nat.pow_pos hb0)
    have hNb : ∀ m, N m = (b : ℝ) ^ m := fun m ↦ by rw [hN]; push_cast; rfl
    have hvar : ∀ m, Var[fun x ↦ x; scrambledLaw f (d m)] = A m + v m := by
      intro m
      rw [variance_scrambledLaw_eq_of_condMean hb0 hfm hf (hmean m)]
      congr 1
      change _ = a ^ 2 * (N m)⁻¹ ^ 2 * unifAvg (fun ρ₀ : Scramble b m ↦ condVar (d m) ρ₀)
      rw [← unifAvg_sq_prodS_eq, ← unifAvg_const_mul]
      congr 1
      funext ρ
      rw [div_eq_mul_inv]
      ring
    have hv0 : ∀ m, 0 ≤ v m := fun m ↦ unifAvg_nonneg fun ρ ↦ variance_nonneg _ _
    have hvle : ∀ m, v m ≤ 4 * L ^ 2 * ((N m) ^ 3)⁻¹ := fun m ↦ by
      rw [hNb]
      exact unifAvg_variance_le hb0 hf hL0 hL
    set κ : ℝ := ((b : ℝ) - 1) ^ 4 / (64 * (b : ℝ) ^ 4) / 2 with hκ
    have hκ0 : 0 < κ := by positivity
    have hlow : ∀ᶠ m in atTop, κ * m * (N m)⁻¹ ≤ s2 m ∧ 1 ≤ m := by
      filter_upwards [eventually_unifAvg_condVar_ge hb d hnet] with m hm
      rw [hNb]
      exact hm
    have hApos : ∀ᶠ m in atTop, a ^ 2 * κ * m * ((N m) ^ 3)⁻¹ ≤ A m ∧ 0 < A m ∧ 1 ≤ m := by
      filter_upwards [hlow] with m hm
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.2
      have ha2 : 0 < a ^ 2 := by positivity
      have hle : a ^ 2 * κ * m * ((N m) ^ 3)⁻¹ ≤ A m := by
        have := mul_le_mul_of_nonneg_left hm.1 (by positivity : 0 ≤ a ^ 2 * (N m)⁻¹ ^ 2)
        refine le_trans (le_of_eq ?_) this
        have : N m ≠ 0 := (hN0 m).ne'
        field_simp
      refine ⟨hle, lt_of_lt_of_le ?_ hle, hm.2⟩
      have := hN0 m
      positivity
    -- the remainders' share
    have hratio : Tendsto (fun m ↦ v m / A m) atTop (𝓝 0) := by
      have hlim : Tendsto (fun m : ℕ ↦ 4 * L ^ 2 / (a ^ 2 * κ) * (m : ℝ)⁻¹) atTop (𝓝 0) := by
        have := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul
          (4 * L ^ 2 / (a ^ 2 * κ))
        rw [mul_zero] at this
        exact this
      refine squeeze_zero' ?_ ?_ hlim
      · filter_upwards [hApos] with m hm
        exact div_nonneg (hv0 m) hm.2.1.le
      · filter_upwards [hApos] with m hm
        have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.2.2
        rw [div_le_iff₀ hm.2.1]
        refine (hvle m).trans ?_
        have := mul_le_mul_of_nonneg_left hm.1
          (by positivity : 0 ≤ 4 * L ^ 2 / (a ^ 2 * κ) * (m : ℝ)⁻¹)
        refine le_trans (le_of_eq ?_) this
        have : N m ≠ 0 := (hN0 m).ne'
        have : (m : ℝ) ≠ 0 := by positivity
        field_simp
    have hσpos : ∀ᶠ m in atTop, 0 < σ m := by
      filter_upwards [hApos] with m hm
      exact Real.sqrt_pos.2 (by rw [hvar]; linarith [hv0 m, hm.2.1])
    have hs2pos : ∀ᶠ m in atTop, 0 < s2 m := by
      filter_upwards [hlow] with m hm
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm.2
      have := inv_pos.2 (hN0 m)
      have : 0 < κ * m * (N m)⁻¹ := by positivity
      linarith [hm.1]
    -- the scale factor
    set ε : ℕ → ℝ := fun m ↦ a * Real.sqrt (s2 m) / (N m * σ m) with hε
    have hεeq : ∀ᶠ m in atTop, ε m = a / |a| * Real.sqrt ((1 + v m / A m)⁻¹) := by
      filter_upwards [hApos, hs2pos] with m hm hs
      have hA0 := hm.2.1
      have hsqA : Real.sqrt (A m) = |a| * (N m)⁻¹ * Real.sqrt (s2 m) := by
        rw [hA, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs,
          Real.sqrt_sq (inv_nonneg.2 (hN0 m).le)]
      have e1 : (1 + v m / A m)⁻¹ = A m / (A m + v m) := by
        field_simp
      rw [e1, Real.sqrt_div' _ (by linarith [hv0 m]), hsqA, hε]
      change a * Real.sqrt (s2 m) / (N m * Real.sqrt Var[fun x ↦ x; scrambledLaw f (d m)]) = _
      rw [hvar]
      have : |a| ≠ 0 := abs_ne_zero.2 ha
      have : N m ≠ 0 := (hN0 m).ne'
      field_simp
    have hεlim : Tendsto ε atTop (𝓝 (a / |a|)) := by
      have h1 : Tendsto (fun m ↦ a / |a| * Real.sqrt ((1 + v m / A m)⁻¹)) atTop
          (𝓝 (a / |a| * Real.sqrt ((1 + 0)⁻¹))) :=
        ((Real.continuous_sqrt.tendsto _).comp
          ((tendsto_const_nhds.add hratio).inv₀ (by norm_num))).const_mul _
      rw [add_zero, inv_one, Real.sqrt_one, mul_one] at h1
      exact h1.congr' (hεeq.mono fun m hm ↦ hm.symm)
    -- the remainder term
    set X : ℕ → ℝ := fun m ↦ unifAvg (fun ρ : Fin 2 → Scramble b m ↦
      ∫ u, |scrambledEstimate f (d m) ρ u -
        ∫ u', scrambledEstimate f (d m) ρ u' ∂(remLaw 2 (b ^ m))| ∂(remLaw 2 (b ^ m))) / σ m
      with hX
    have hXlim : Tendsto X atTop (𝓝 0) := by
      have hsq : Tendsto (fun m ↦ Real.sqrt (v m / A m)) atTop (𝓝 0) := by
        have := (Real.continuous_sqrt.tendsto _).comp hratio
        rwa [Real.sqrt_zero] at this
      refine squeeze_zero' ?_ ?_ hsq
      · filter_upwards [hσpos] with m hm
        exact div_nonneg (unifAvg_nonneg fun ρ ↦ integral_nonneg fun u ↦ abs_nonneg _) hm.le
      · filter_upwards [hσpos, hApos] with m hσm hm
        refine Real.le_sqrt_of_sq_le ?_
        have h1 : (unifAvg (fun ρ : Fin 2 → Scramble b m ↦ ∫ u, |scrambledEstimate f (d m) ρ u -
            ∫ u', scrambledEstimate f (d m) ρ u' ∂(remLaw 2 (b ^ m))| ∂(remLaw 2 (b ^ m)))) ^ 2 ≤
            v m := (sq_unifAvg_le _).trans (unifAvg_mono fun ρ ↦
              sq_integral_abs_sub_le_variance (memLp_scrambledEstimate hb0 hf (d m) ρ))
        have hσ2 : σ m ^ 2 = A m + v m := by
          rw [hσ]
          simp only
          rw [Real.sq_sqrt (by rw [hvar]; linarith [hv0 m, hm.2.1]), hvar]
        rw [hX]
        simp only
        rw [div_pow, hσ2, div_le_div_iff₀ (by linarith [hv0 m, hm.2.1]) hm.2.1]
        have := hv0 m
        nlinarith [hm.2.1]
    -- the CLT for `S`
    have hS := tendsto_unifAvg_cexp_prodS hb d hnet (hεlim.const_mul t)
    have hsign : (t * (a / |a|)) ^ 2 = t ^ 2 := by
      rw [mul_pow, div_pow, sq_abs, div_self (by positivity), mul_one]
    rw [hsign] at hS
    -- the comparison
    have hcomp : ∀ᶠ m in atTop, ‖charFun ((scrambledLaw f (d m)).map fun x ↦
        (x - μ) / σ m) t - unifAvg (fun ρ : Fin 2 → Scramble b m ↦
          cexp ((((t * ε m * prodS (d m) ρ) / Real.sqrt (s2 m) : ℝ) : ℂ) * I))‖ ≤
        |t| * X m := by
      filter_upwards [hσpos, hs2pos] with m hσm hs
      have hYm : Measurable fun x : ℝ ↦ (x - μ) / σ m := (measurable_id.sub_const _).div_const _
      have hg : Continuous fun x : ℝ ↦ cexp (((t * ((x - μ) / σ m) : ℝ) : ℂ) * I) :=
        Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
          (continuous_const.mul ((continuous_id.sub continuous_const).div_const _))).mul
          continuous_const)
      have hint : ∀ ρ, Integrable (fun u ↦ cexp (((t * ((scrambledEstimate f (d m) ρ u - μ) /
          σ m) : ℝ) : ℂ) * I)) (remLaw 2 (b ^ m)) := fun ρ ↦ by
        refine Integrable.of_bound (hg.comp_aestronglyMeasurable
          (measurable_scrambledEstimate hfm (d m) ρ).aestronglyMeasurable) 1
          (Eventually.of_forall fun u ↦ ?_)
        rw [Complex.norm_exp_ofReal_mul_I]
      have hcf : charFun ((scrambledLaw f (d m)).map fun x ↦ (x - μ) / σ m) t =
          unifAvg (fun ρ : Fin 2 → Scramble b m ↦ ∫ u, cexp (((t * ((scrambledEstimate f (d m)
            ρ u - μ) / σ m) : ℝ) : ℂ) * I) ∂(remLaw 2 (b ^ m))) := by
        have hcont : Continuous fun y : ℝ ↦ cexp ((t : ℂ) * (y : ℂ) * I) := by fun_prop
        rw [charFun_apply_real, integral_map hYm.aemeasurable hcont.aestronglyMeasurable]
        unfold scrambledLaw
        rw [← integral_mixLaw_complex (measurable_scrambledEstimate hfm (d m)) hg hint]
        congr 1
        funext x
        push_cast
        ring_nf
      rw [hcf, ← unifAvg_sub_complex]
      refine (norm_unifAvg_le _).trans ?_
      rw [hX, show |t| * (unifAvg (fun ρ : Fin 2 → Scramble b m ↦ ∫ u,
          |scrambledEstimate f (d m) ρ u - ∫ u', scrambledEstimate f (d m) ρ u'
            ∂(remLaw 2 (b ^ m))| ∂(remLaw 2 (b ^ m))) / σ m) =
          unifAvg (fun ρ : Fin 2 → Scramble b m ↦ |t| / σ m * ∫ u,
          |scrambledEstimate f (d m) ρ u - ∫ u', scrambledEstimate f (d m) ρ u'
            ∂(remLaw 2 (b ^ m))| ∂(remLaw 2 (b ^ m))) by
        rw [unifAvg_const_mul]
        ring]
      refine unifAvg_mono fun ρ ↦ ?_
      set c : ℂ := cexp ((((t * ε m * prodS (d m) ρ) / Real.sqrt (s2 m) : ℝ) : ℂ) * I) with hc
      have hL1 : Integrable (fun u ↦ |scrambledEstimate f (d m) ρ u -
          ∫ u', scrambledEstimate f (d m) ρ u' ∂(remLaw 2 (b ^ m))|) (remLaw 2 (b ^ m)) :=
        (((memLp_scrambledEstimate hb0 hf (d m) ρ).integrable one_le_two).sub
          (integrable_const _)).abs
      rw [← integral_const_mul, show c = ∫ _u, c ∂(remLaw 2 (b ^ m)) by
        rw [integral_const, probReal_univ, one_smul], ← integral_sub (hint ρ)
        (integrable_const _)]
      refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
        (Eventually.of_forall fun u ↦ norm_nonneg _) (hL1.const_mul _)
        (Eventually.of_forall fun u ↦ ?_))
      refine (norm_cexp_sub_cexp_le _ _).trans (le_of_eq ?_)
      have hrel : t * ((scrambledEstimate f (d m) ρ u - μ) / σ m) -
          t * ε m * prodS (d m) ρ / Real.sqrt (s2 m) =
          t / σ m * (scrambledEstimate f (d m) ρ u -
            ∫ u', scrambledEstimate f (d m) ρ u' ∂(remLaw 2 (b ^ m))) := by
        rw [hmean m ρ, hε]
        have : Real.sqrt (s2 m) ≠ 0 := (Real.sqrt_pos.2 hs).ne'
        have : N m ≠ 0 := (hN0 m).ne'
        have : σ m ≠ 0 := hσm.ne'
        simp only
        field_simp
        ring
      rw [hrel, abs_mul, abs_div, abs_of_pos hσm]
    -- conclusion
    rw [tendsto_iff_norm_sub_tendsto_zero]
    rw [tendsto_iff_norm_sub_tendsto_zero] at hS
    refine squeeze_zero' (Eventually.of_forall fun m ↦ norm_nonneg _) ?_
      (by simpa only [mul_zero, zero_add] using (hXlim.const_mul |t|).add hS)
    filter_upwards [hcomp] with m hm
    refine (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hm (le_of_eq ?_))
    congr 3

/-- **Loh's CLT for `x₀ x₁`** (post #2, Loh 2003): for every sequence of `(0,m,2)`-nets in base
`b ≥ 2`, `(μ̂ - 1/4)/√Var(μ̂) ⇒ N(0,1)` for the scrambled-net estimator of `∫ x₀ x₁`. -/
theorem tendstoInDistribution_scrambledLaw_prodFn (hb : 1 < b)
    (d : (m : ℕ) → Fin (b ^ m) → Fin 2 → Fin m → Fin b)
    (hnet : ∀ m, IsNet b 0 m fun i j ↦ digitPoint (d m i j) 0)
    [∀ m, IsProbabilityMeasure (scrambledLaw prodFn (d m))]
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun m x ↦ (x - ∫ y, prodFn y ∂(uniformCube 2)) /
      Real.sqrt Var[fun x ↦ x; scrambledLaw prodFn (d m)]) atTop Z
      (fun m ↦ scrambledLaw prodFn (d m)) P' := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  exact tendstoInDistribution_scrambledLaw_of_condMean hb d hnet measurable_prodFn memLp_prodFn
    zero_le_one (fun x x' hx hx' ↦ abs_prodFn_sub_le hx hx') one_ne_zero (fun m ρ ↦ by
      rw [integral_scrambledEstimate_prodFn hb0 (hnet m) ρ, integral_prodFn, one_mul]) hZ

/-- **Loh's CLT for `x₀ x₁` on the scrambled Hammersley nets** `{(i/bᵐ, φ_b(i))}`, any base
`b ≥ 2`. -/
theorem tendstoInDistribution_scrambledLaw_prodFn_hammersley (hb : 1 < b)
    [∀ m, IsProbabilityMeasure
      (scrambledLaw prodFn (hammersleyDigits (lt_trans Nat.zero_lt_one hb) m))]
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun m x ↦ (x - ∫ y, prodFn y ∂(uniformCube 2)) /
      Real.sqrt Var[fun x ↦ x;
        scrambledLaw prodFn (hammersleyDigits (lt_trans Nat.zero_lt_one hb) m)]) atTop Z
      (fun m ↦ scrambledLaw prodFn (hammersleyDigits (lt_trans Nat.zero_lt_one hb) m)) P' :=
  tendstoInDistribution_scrambledLaw_prodFn hb _ (isNet_hammersley hb) hZ

/-- The scrambled-net estimator is linear in the integrand. -/
theorem scrambledEstimate_bilinAdd {m n : ℕ} (a : ℝ) (g : Fin 2 → ℝ → ℝ)
    (d : Fin n → Fin 2 → Fin m → Fin b) (ρ : Fin 2 → Scramble b m) (u : Fin n → Fin 2 → ℝ) :
    scrambledEstimate (fun x ↦ a * prodFn x + addFn g x) d ρ u =
      a * scrambledEstimate prodFn d ρ u + scrambledEstimate (addFn g) d ρ u := by
  unfold scrambledEstimate sampleMean
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- **The additive part is integrated exactly given the scramble**:
`E[μ̂(Σ_j g_j) | ρ] = Σ_j ∫ g_j` for every `(0,m,s)`-net and every scramble. -/
theorem integral_scrambledEstimate_addFn (hb : 0 < b) {m s : ℕ}
    {d : Fin (b ^ m) → Fin s → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    {g : Fin s → ℝ → ℝ} (hgm : ∀ j, Measurable (g j))
    (hgc : ∀ j, ContinuousOn (g j) (Set.Icc 0 1)) (ρ : Fin s → Scramble b m) :
    ∫ u, scrambledEstimate (addFn g) d ρ u ∂(remLaw s (b ^ m)) = ∑ j, ∫ x, g j x ∂uniformIco := by
  have hQ := isProbabilityMeasure_remLaw s (b ^ m)
  have hU := isProbabilityMeasure_uniformCube s
  have e : ∀ u, scrambledEstimate (addFn g) d ρ u =
      ∑ i, addTerm g d ρ i (u i) + ∑ j, ∫ x, g j x ∂uniformIco := fun u ↦ by
    rw [sum_addTerm hb hnet hgc ρ u]
    ring
  have hint : ∀ i, Integrable (fun u : Fin (b ^ m) → Fin s → ℝ ↦ addTerm g d ρ i (u i))
      (remLaw s (b ^ m)) := fun i ↦
    (memLp_remLaw_eval (memLp_addTerm hgm hgc hb ρ i) i).integrable one_le_two
  rw [integral_congr_ae (Eventually.of_forall e), integral_add (integrable_finsetSum _
    fun i _ ↦ hint i) (integrable_const _), integral_finsetSum _ fun i _ ↦ hint i,
    integral_const, probReal_univ, one_smul]
  rw [Finset.sum_eq_zero fun i _ ↦ by
    rw [integral_remLaw_eval (g := addTerm g d ρ i)
      (measurable_addTerm hgm d ρ i).aestronglyMeasurable i, integral_addTerm hgm hgc hb ρ i],
    zero_add]

/-- **Loh's CLT for the smooth integrands with a constant non-zero mixed derivative**
(post #2, Loh 2003, `s = 2`): for `f(x) = a x₀ x₁ + g₀(x₀) + g₁(x₁)` with `a ≠ 0` and each
`g_j` measurable and `C¹` on `[0,1]` (so `∂²f/∂x₀∂x₁ ≡ a`), and every sequence of
`(0,m,2)`-nets in base `b ≥ 2` scrambled by independent uniform nested scrambles with
independent uniform remainders, `(μ̂ - μ)/√Var(μ̂) ⇒ N(0,1)` as `n = bᵐ → ∞`. -/
theorem tendstoInDistribution_scrambledLaw_bilinAdd (hb : 1 < b)
    (d : (m : ℕ) → Fin (b ^ m) → Fin 2 → Fin m → Fin b)
    (hnet : ∀ m, IsNet b 0 m fun i j ↦ digitPoint (d m i j) 0) {a : ℝ} (ha : a ≠ 0)
    {g g' : Fin 2 → ℝ → ℝ} (hgm : ∀ j, Measurable (g j))
    (hg : ∀ j, ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt (g j) (g' j x) (Set.Icc 0 1) x)
    (hg' : ∀ j, ContinuousOn (g' j) (Set.Icc 0 1))
    [∀ m, IsProbabilityMeasure (scrambledLaw (fun x ↦ a * prodFn x + addFn g x) (d m))]
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun m x ↦ (x - ∫ y, (a * prodFn y + addFn g y) ∂(uniformCube 2)) /
      Real.sqrt Var[fun x ↦ x; scrambledLaw (fun x ↦ a * prodFn x + addFn g x) (d m)]) atTop Z
      (fun m ↦ scrambledLaw (fun x ↦ a * prodFn x + addFn g x) (d m)) P' := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hU := isProbabilityMeasure_uniformCube 2
  have hgc : ∀ j, ContinuousOn (g j) (Set.Icc 0 1) := fun j x hx ↦ (hg j x hx).continuousWithinAt
  choose K hK using fun j ↦ exists_lipschitz_of_C1 (hg j) (hg' j)
  have hfm : Measurable fun x ↦ a * prodFn x + addFn g x :=
    (measurable_prodFn.const_mul a).add (measurable_addFn hgm)
  have hf : MemLp (fun x ↦ a * prodFn x + addFn g x) 2 (uniformCube 2) :=
    (memLp_prodFn.const_mul a).add (memLp_addFn hgm hgc 2)
  set L : ℝ := |a| + ∑ j, max (K j) 0 with hL
  have hL0 : 0 ≤ L := add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun j _ ↦ le_max_right _ _)
  have hLip : ∀ x x' : Fin 2 → ℝ, (∀ j, x j ∈ Set.Ico (0 : ℝ) 1) →
      (∀ j, x' j ∈ Set.Ico (0 : ℝ) 1) →
      |(a * prodFn x + addFn g x) - (a * prodFn x' + addFn g x')| ≤ L * ∑ j, |x j - x' j| := by
    intro x x' hx hx'
    have h1 : |a * prodFn x - a * prodFn x'| ≤ |a| * ∑ j, |x j - x' j| := by
      rw [← mul_sub, abs_mul]
      have := abs_prodFn_sub_le hx hx'
      rw [one_mul] at this
      exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
    have h2 : |addFn g x - addFn g x'| ≤ (∑ j, max (K j) 0) * ∑ j, |x j - x' j| := by
      unfold addFn
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun j _ ↦ ?_
      have hj := hK j (x j) (Set.Ico_subset_Icc_self (hx j)) (x' j)
        (Set.Ico_subset_Icc_self (hx' j))
      have hle : |x j - x' j| ≤ ∑ k, |x k - x' k| :=
        Finset.single_le_sum (f := fun k ↦ |x k - x' k|) (fun k _ ↦ abs_nonneg _)
          (Finset.mem_univ j)
      calc |g j (x j) - g j (x' j)| ≤ K j * |x j - x' j| := hj
        _ ≤ max (K j) 0 * |x j - x' j| :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
        _ ≤ max (K j) 0 * ∑ k, |x k - x' k| :=
            mul_le_mul_of_nonneg_left hle (le_max_right _ _)
    calc |(a * prodFn x + addFn g x) - (a * prodFn x' + addFn g x')|
        = |(a * prodFn x - a * prodFn x') + (addFn g x - addFn g x')| := by ring_nf
      _ ≤ |a * prodFn x - a * prodFn x'| + |addFn g x - addFn g x'| := abs_add_le _ _
      _ ≤ |a| * ∑ j, |x j - x' j| + (∑ j, max (K j) 0) * ∑ j, |x j - x' j| := add_le_add h1 h2
      _ = L * ∑ j, |x j - x' j| := by rw [hL]; ring
  have hmeanf : ∫ y, (a * prodFn y + addFn g y) ∂(uniformCube 2) =
      a * (1 / 4) + ∑ j, ∫ x, g j x ∂uniformIco := by
    rw [integral_add ((memLp_prodFn.integrable one_le_two).const_mul a)
      ((memLp_addFn hgm hgc 2).integrable one_le_two), integral_const_mul, integral_prodFn,
      integral_addFn hgm hgc]
  refine tendstoInDistribution_scrambledLaw_of_condMean hb d hnet hfm hf hL0 hLip ha
    (fun m ρ ↦ ?_) hZ
  have hQ := isProbabilityMeasure_remLaw 2 (b ^ m)
  rw [integral_congr_ae (Eventually.of_forall fun u ↦ scrambledEstimate_bilinAdd a g (d m) ρ u),
    integral_add (((memLp_scrambledEstimate hb0 memLp_prodFn (d m) ρ).integrable
      one_le_two).const_mul a) ((memLp_scrambledEstimate hb0 (memLp_addFn hgm hgc 2) (d m)
        ρ).integrable one_le_two), integral_const_mul,
    integral_scrambledEstimate_prodFn hb0 (hnet m) ρ,
    integral_scrambledEstimate_addFn hb0 (hnet m) hgm hgc ρ, hmeanf]
  ring

end RQMCMarkov.OwenScrambling

set_option linter.style.longLine false
#print axioms RQMCMarkov.OwenScrambling.InUnitIco
#print axioms RQMCMarkov.OwenScrambling.countBelow
#print axioms RQMCMarkov.OwenScrambling.countAtMost
#print axioms RQMCMarkov.OwenScrambling.localDiscrepancy
#print axioms RQMCMarkov.OwenScrambling.starDiscrepancy
#print axioms RQMCMarkov.OwenScrambling.qmcEstimate
#print axioms RQMCMarkov.OwenScrambling.midpointRule
#print axioms RQMCMarkov.OwenScrambling.countBelow_le
#print axioms RQMCMarkov.OwenScrambling.countBelow_mono
#print axioms RQMCMarkov.OwenScrambling.countBelow_div_mem_Icc
#print axioms RQMCMarkov.OwenScrambling.localDiscrepancy_le_one
#print axioms RQMCMarkov.OwenScrambling.localDiscrepancy_eq_abs_div
#print axioms RQMCMarkov.OwenScrambling.bddAbove_localDiscrepancy
#print axioms RQMCMarkov.OwenScrambling.localDiscrepancy_le_starDiscrepancy
#print axioms RQMCMarkov.OwenScrambling.starDiscrepancy_le_of_forall
#print axioms RQMCMarkov.OwenScrambling.starDiscrepancy_nonneg
#print axioms RQMCMarkov.OwenScrambling.starDiscrepancy_le_one
#print axioms RQMCMarkov.OwenScrambling.countAtMost_div_sub_le_starDiscrepancy
#print axioms RQMCMarkov.OwenScrambling.inv_two_mul_le_starDiscrepancy
#print axioms RQMCMarkov.OwenScrambling.midpointRule_mem
#print axioms RQMCMarkov.OwenScrambling.midpointRule_lt_iff
#print axioms RQMCMarkov.OwenScrambling.countBelow_midpointRule_le
#print axioms RQMCMarkov.OwenScrambling.le_countBelow_midpointRule
#print axioms RQMCMarkov.OwenScrambling.abs_countBelow_midpointRule_sub_le
#print axioms RQMCMarkov.OwenScrambling.starDiscrepancy_midpointRule
#print axioms RQMCMarkov.OwenScrambling.starDiscrepancy_midpointRule_le
#print axioms RQMCMarkov.OwenScrambling.midpointRule_three
#print axioms RQMCMarkov.OwenScrambling.starDiscrepancy_midpointRule_three
#print axioms RQMCMarkov.OwenScrambling.uniformIco
#print axioms RQMCMarkov.OwenScrambling.isProbabilityMeasure_uniformIco
#print axioms RQMCMarkov.OwenScrambling.uniformCube
#print axioms RQMCMarkov.OwenScrambling.isProbabilityMeasure_uniformCube
#print axioms RQMCMarkov.OwenScrambling.sampleMean
#print axioms RQMCMarkov.OwenScrambling.map_le_of_sum_map_eq
#print axioms RQMCMarkov.OwenScrambling.integrable_map_of_sum_map_eq
#print axioms RQMCMarkov.OwenScrambling.memLp_map_of_sum_map_eq
#print axioms RQMCMarkov.OwenScrambling.integral_sampleMean_of_sum_map_eq
#print axioms RQMCMarkov.OwenScrambling.variance_sampleMean_of_sum_map_eq
#print axioms RQMCMarkov.OwenScrambling.variance_sampleMean_le_of_sum_map_eq
#print axioms RQMCMarkov.OwenScrambling.sum_map_eq_of_hasLaw
#print axioms RQMCMarkov.OwenScrambling.integral_sampleMean_iid
#print axioms RQMCMarkov.OwenScrambling.variance_sampleMean_iid
#print axioms RQMCMarkov.OwenScrambling.rmse_sampleMean_iid
#print axioms RQMCMarkov.OwenScrambling.tendstoInDistribution_sampleMean_iid
#print axioms RQMCMarkov.OwenScrambling.measure_all_draws_lt_tenth
#print axioms RQMCMarkov.OwenScrambling.measure_all_draws_lt_tenth_pos
#print axioms RQMCMarkov.OwenScrambling.measure_sampleMean_far_pos
#print axioms RQMCMarkov.OwenScrambling.integral_sampleMean_of_hasLaw_uniformCube
#print axioms RQMCMarkov.OwenScrambling.uniformIco_eq_restrict_Ioc
#print axioms RQMCMarkov.OwenScrambling.map_fract_restrict_Ioc
#print axioms RQMCMarkov.OwenScrambling.measurePreserving_fract_add
#print axioms RQMCMarkov.OwenScrambling.shiftMod1
#print axioms RQMCMarkov.OwenScrambling.shiftMod1_mem_cube
#print axioms RQMCMarkov.OwenScrambling.measurePreserving_shiftMod1
#print axioms RQMCMarkov.OwenScrambling.hasLaw_shiftMod1
#print axioms RQMCMarkov.OwenScrambling.integral_sampleMean_shiftMod1
#print axioms RQMCMarkov.OwenScrambling.stratum
#print axioms RQMCMarkov.OwenScrambling.measurableSet_stratum
#print axioms RQMCMarkov.OwenScrambling.stratumMap
#print axioms RQMCMarkov.OwenScrambling.measurable_stratumMap
#print axioms RQMCMarkov.OwenScrambling.stratumMap_preimage_stratum
#print axioms RQMCMarkov.OwenScrambling.map_stratumMap_uniformIco
#print axioms RQMCMarkov.OwenScrambling.iUnion_stratum
#print axioms RQMCMarkov.OwenScrambling.pairwise_disjoint_stratum
#print axioms RQMCMarkov.OwenScrambling.sum_map_stratumMap
#print axioms RQMCMarkov.OwenScrambling.sum_map_stratified
#print axioms RQMCMarkov.OwenScrambling.integral_sampleMean_stratified
#print axioms RQMCMarkov.OwenScrambling.not_hasLaw_stratumMap
#print axioms RQMCMarkov.OwenScrambling.sum_map_eq_of_integral_sampleMean_indicator
#print axioms RQMCMarkov.OwenScrambling.sampleMean_const_points
#print axioms RQMCMarkov.OwenScrambling.integral_sampleMean_of_hasLaw_const
#print axioms RQMCMarkov.OwenScrambling.variance_sampleMean_const
#print axioms RQMCMarkov.OwenScrambling.Agree
#print axioms RQMCMarkov.OwenScrambling.truncDigits
#print axioms RQMCMarkov.OwenScrambling.digitAt
#print axioms RQMCMarkov.OwenScrambling.prefixVal
#print axioms RQMCMarkov.OwenScrambling.cellVal
#print axioms RQMCMarkov.OwenScrambling.Scramble
#print axioms RQMCMarkov.OwenScrambling.scramble
#print axioms RQMCMarkov.OwenScrambling.agree_mono
#print axioms RQMCMarkov.OwenScrambling.agree_symm
#print axioms RQMCMarkov.OwenScrambling.agree_trans
#print axioms RQMCMarkov.OwenScrambling.agree_iff_eq
#print axioms RQMCMarkov.OwenScrambling.agree_succ_iff
#print axioms RQMCMarkov.OwenScrambling.truncDigits_eq_iff
#print axioms RQMCMarkov.OwenScrambling.agree_scramble_iff
#print axioms RQMCMarkov.OwenScrambling.scramble_injective
#print axioms RQMCMarkov.OwenScrambling.scramble_bijective
#print axioms RQMCMarkov.OwenScrambling.scramble_mul_apply
#print axioms RQMCMarkov.OwenScrambling.digitAt_lt
#print axioms RQMCMarkov.OwenScrambling.digitAt_fin
#print axioms RQMCMarkov.OwenScrambling.prefixVal_lt
#print axioms RQMCMarkov.OwenScrambling.prefixVal_inj_iff
#print axioms RQMCMarkov.OwenScrambling.prefixVal_eq_iff_agree
#print axioms RQMCMarkov.OwenScrambling.prefixVal_div
#print axioms RQMCMarkov.OwenScrambling.cellVal_lt
#print axioms RQMCMarkov.OwenScrambling.cellVal_injective
#print axioms RQMCMarkov.OwenScrambling.cellFin
#print axioms RQMCMarkov.OwenScrambling.cellFin_bijective
#print axioms RQMCMarkov.OwenScrambling.exists_prefixVal_eq
#print axioms RQMCMarkov.OwenScrambling.digitPoint
#print axioms RQMCMarkov.OwenScrambling.digitPoint_eq_stratumMap
#print axioms RQMCMarkov.OwenScrambling.floor_pow_mul_digitPoint
#print axioms RQMCMarkov.OwenScrambling.digitPoint_mem_Ico
#print axioms RQMCMarkov.OwenScrambling.elemBox
#print axioms RQMCMarkov.OwenScrambling.boxIndex
#print axioms RQMCMarkov.OwenScrambling.mem_elemBox_iff
#print axioms RQMCMarkov.OwenScrambling.IsNet
#print axioms RQMCMarkov.OwenScrambling.scrambledPoint
#print axioms RQMCMarkov.OwenScrambling.isNet_scrambledPoint
#print axioms RQMCMarkov.OwenScrambling.card_scramble_fiber_eq
#print axioms RQMCMarkov.OwenScrambling.card_scramble_fiber_mul
#print axioms RQMCMarkov.OwenScrambling.sum_scramble_eq
#print axioms RQMCMarkov.OwenScrambling.sum_map_digitPoint_scramble
#print axioms RQMCMarkov.OwenScrambling.mixLaw
#print axioms RQMCMarkov.OwenScrambling.measurable_digitPoint
#print axioms RQMCMarkov.OwenScrambling.measurable_scrambledPoint
#print axioms RQMCMarkov.OwenScrambling.mixLaw_scrambledPoint
#print axioms RQMCMarkov.OwenScrambling.exists_perm_pair
#print axioms RQMCMarkov.OwenScrambling.le_of_agree_of_ne
#print axioms RQMCMarkov.OwenScrambling.card_scramble_pair_le
#print axioms RQMCMarkov.OwenScrambling.card_scramble_pair_eq
#print axioms RQMCMarkov.OwenScrambling.card_scramble_pair_eq_zero
#print axioms RQMCMarkov.OwenScrambling.agree_min_iff
#print axioms RQMCMarkov.OwenScrambling.card_agree
#print axioms RQMCMarkov.OwenScrambling.commonPrefix
#print axioms RQMCMarkov.OwenScrambling.commonPrefix_le
#print axioms RQMCMarkov.OwenScrambling.agree_iff_le_commonPrefix
#print axioms RQMCMarkov.OwenScrambling.agree_commonPrefix
#print axioms RQMCMarkov.OwenScrambling.ne_at_commonPrefix
#print axioms RQMCMarkov.OwenScrambling.commonPrefix_scramble
#print axioms RQMCMarkov.OwenScrambling.agreeKernel
#print axioms RQMCMarkov.OwenScrambling.agreeKernel_comm
#print axioms RQMCMarkov.OwenScrambling.sum_agreeKernel
#print axioms RQMCMarkov.OwenScrambling.pairKernel
#print axioms RQMCMarkov.OwenScrambling.sum_pairKernel
#print axioms RQMCMarkov.OwenScrambling.pairKernel_eq_zero
#print axioms RQMCMarkov.OwenScrambling.pairKernel_eq_const
#print axioms RQMCMarkov.OwenScrambling.card_scramble_pair_of_lt
#print axioms RQMCMarkov.OwenScrambling.card_scramble_pair_diag
#print axioms RQMCMarkov.OwenScrambling.card_scramble_pair
#print axioms RQMCMarkov.OwenScrambling.sum_agreeKernel_mul_of_le
#print axioms RQMCMarkov.OwenScrambling.sum_agreeKernel_mul
#print axioms RQMCMarkov.OwenScrambling.agreeKernel_self_depth
#print axioms RQMCMarkov.OwenScrambling.agreeKernel_zero
#print axioms RQMCMarkov.OwenScrambling.agreeKernel_min
#print axioms RQMCMarkov.OwenScrambling.detailKernel
#print axioms RQMCMarkov.OwenScrambling.detailKernel_comm
#print axioms RQMCMarkov.OwenScrambling.sum_detailKernel_mul
#print axioms RQMCMarkov.OwenScrambling.sum_range_detailKernel
#print axioms RQMCMarkov.OwenScrambling.agreeKernel_eq_sum_fin
#print axioms RQMCMarkov.OwenScrambling.gainWeight
#print axioms RQMCMarkov.OwenScrambling.gainWeight_zero
#print axioms RQMCMarkov.OwenScrambling.pairKernel_eq_sum
#print axioms RQMCMarkov.OwenScrambling.haarKernel
#print axioms RQMCMarkov.OwenScrambling.sum_prod_mul_prod
#print axioms RQMCMarkov.OwenScrambling.haarKernel_comm
#print axioms RQMCMarkov.OwenScrambling.sum_haarKernel_mul
#print axioms RQMCMarkov.OwenScrambling.qform
#print axioms RQMCMarkov.OwenScrambling.qform_eq_sum_sq
#print axioms RQMCMarkov.OwenScrambling.qform_haarKernel_nonneg
#print axioms RQMCMarkov.OwenScrambling.sum_haarKernel
#print axioms RQMCMarkov.OwenScrambling.haarKernel_zero
#print axioms RQMCMarkov.OwenScrambling.prod_pairKernel_eq_sum
#print axioms RQMCMarkov.OwenScrambling.scrambleVec
#print axioms RQMCMarkov.OwenScrambling.card_scrambleVec_pair
#print axioms RQMCMarkov.OwenScrambling.sum_scrambleVec_pair
#print axioms RQMCMarkov.OwenScrambling.card_scrambleVec
#print axioms RQMCMarkov.OwenScrambling.sum_scrambleVec
#print axioms RQMCMarkov.OwenScrambling.haarVar
#print axioms RQMCMarkov.OwenScrambling.haarVar_nonneg
#print axioms RQMCMarkov.OwenScrambling.sum_haarVar
#print axioms RQMCMarkov.OwenScrambling.haarVar_zero
#print axioms RQMCMarkov.OwenScrambling.gainCoeff
#print axioms RQMCMarkov.OwenScrambling.gainCoeff_zero
#print axioms RQMCMarkov.OwenScrambling.sum_sum_sum_rotate
#print axioms RQMCMarkov.OwenScrambling.sum_pairKernel_mul_eq
#print axioms RQMCMarkov.OwenScrambling.sum_sq_sum_scrambleVec
#print axioms RQMCMarkov.OwenScrambling.card_filter_range_div
#print axioms RQMCMarkov.OwenScrambling.boxIndex_digitPoint
#print axioms RQMCMarkov.OwenScrambling.boxIndex_digitPoint_eq_iff
#print axioms RQMCMarkov.OwenScrambling.card_agree_net_eq_one
#print axioms RQMCMarkov.OwenScrambling.card_agree_net_of_le
#print axioms RQMCMarkov.OwenScrambling.exists_le_sum_eq
#print axioms RQMCMarkov.OwenScrambling.card_agree_net_of_ge
#print axioms RQMCMarkov.OwenScrambling.card_agree_net
#print axioms RQMCMarkov.OwenScrambling.gainSeq
#print axioms RQMCMarkov.OwenScrambling.gainSeq_zero_right
#print axioms RQMCMarkov.OwenScrambling.gainSeq_succ
#print axioms RQMCMarkov.OwenScrambling.gainAltSum
#print axioms RQMCMarkov.OwenScrambling.gainAltSum_succ
#print axioms RQMCMarkov.OwenScrambling.gainSeq_eq_altSum
#print axioms RQMCMarkov.OwenScrambling.gainSeq_eq_zero
#print axioms RQMCMarkov.OwenScrambling.alt_sum_mem_Icc
#print axioms RQMCMarkov.OwenScrambling.antitone_choose_div
#print axioms RQMCMarkov.OwenScrambling.gainAltSum_mem_Icc
#print axioms RQMCMarkov.OwenScrambling.gainSeq_mem_Icc
#print axioms RQMCMarkov.OwenScrambling.gainSeq_two_four_two
#print axioms RQMCMarkov.OwenScrambling.agreeInd
#print axioms RQMCMarkov.OwenScrambling.gainFactor
#print axioms RQMCMarkov.OwenScrambling.gainWeight_commonPrefix
#print axioms RQMCMarkov.OwenScrambling.partialGain
#print axioms RQMCMarkov.OwenScrambling.gainCoeff_eq_partialGain
#print axioms RQMCMarkov.OwenScrambling.partialGain_empty
#print axioms RQMCMarkov.OwenScrambling.partialGain_insert
#print axioms RQMCMarkov.OwenScrambling.card_filter_add_le_sum
#print axioms RQMCMarkov.OwenScrambling.partialGain_eq_gainSeq
#print axioms RQMCMarkov.OwenScrambling.gainCoeff_net
#print axioms RQMCMarkov.OwenScrambling.one_le_card_active
#print axioms RQMCMarkov.OwenScrambling.gainCoeff_net_eq_zero
#print axioms RQMCMarkov.OwenScrambling.gainCoeff_net_mem_Icc
#print axioms RQMCMarkov.OwenScrambling.cellPoint
#print axioms RQMCMarkov.OwenScrambling.scrambledPoint_eq_cellPoint
#print axioms RQMCMarkov.OwenScrambling.measurable_cellPoint
#print axioms RQMCMarkov.OwenScrambling.mixLaw_scrambledPoint_pair_eq
#print axioms RQMCMarkov.OwenScrambling.sum_map_digitPoint
#print axioms RQMCMarkov.OwenScrambling.sum_map_cellPoint
#print axioms RQMCMarkov.OwenScrambling.map_cellPoint_le
#print axioms RQMCMarkov.OwenScrambling.memLp_comp_cellPoint
#print axioms RQMCMarkov.OwenScrambling.sum_integral_cellPoint
#print axioms RQMCMarkov.OwenScrambling.remLaw
#print axioms RQMCMarkov.OwenScrambling.isProbabilityMeasure_remLaw
#print axioms RQMCMarkov.OwenScrambling.measurePreserving_remLaw_eval
#print axioms RQMCMarkov.OwenScrambling.integral_remLaw_eval
#print axioms RQMCMarkov.OwenScrambling.memLp_remLaw_eval
#print axioms RQMCMarkov.OwenScrambling.integral_remLaw_mul
#print axioms RQMCMarkov.OwenScrambling.cellAvg
#print axioms RQMCMarkov.OwenScrambling.cellSq
#print axioms RQMCMarkov.OwenScrambling.cellAvg_sq_le
#print axioms RQMCMarkov.OwenScrambling.scrambledEstimate
#print axioms RQMCMarkov.OwenScrambling.scrambledLaw
#print axioms RQMCMarkov.OwenScrambling.memLp_scrambledEstimate
#print axioms RQMCMarkov.OwenScrambling.measurable_scrambledEstimate
#print axioms RQMCMarkov.OwenScrambling.integral_scrambledEstimate
#print axioms RQMCMarkov.OwenScrambling.integral_sq_scrambledEstimate
#print axioms RQMCMarkov.OwenScrambling.integral_mixLaw
#print axioms RQMCMarkov.OwenScrambling.isProbabilityMeasure_mixLaw
#print axioms RQMCMarkov.OwenScrambling.memLp_id_mixLaw
#print axioms RQMCMarkov.OwenScrambling.card_scramble_pi
#print axioms RQMCMarkov.OwenScrambling.integral_scrambledLaw
#print axioms RQMCMarkov.OwenScrambling.cellResVar
#print axioms RQMCMarkov.OwenScrambling.cellResVar_nonneg
#print axioms RQMCMarkov.OwenScrambling.variance_eq_cellResVar_add
#print axioms RQMCMarkov.OwenScrambling.variance_scrambledLaw
#print axioms RQMCMarkov.OwenScrambling.pow_div_sub_one_le_exp_one
#print axioms RQMCMarkov.OwenScrambling.variance_scrambledLaw_le
#print axioms RQMCMarkov.OwenScrambling.variance_scrambledLaw_le_exp_one
#print axioms RQMCMarkov.OwenScrambling.card_box_net_of_le
#print axioms RQMCMarkov.OwenScrambling.stepFn
#print axioms RQMCMarkov.OwenScrambling.measurable_stepFn
#print axioms RQMCMarkov.OwenScrambling.memLp_stepFn
#print axioms RQMCMarkov.OwenScrambling.boxIndex_scrambledPoint
#print axioms RQMCMarkov.OwenScrambling.sum_stepFn_scrambledPoint
#print axioms RQMCMarkov.OwenScrambling.ae_mem_cube_uniformCube
#print axioms RQMCMarkov.OwenScrambling.integral_stepFn
#print axioms RQMCMarkov.OwenScrambling.ae_mem_cube_remLaw
#print axioms RQMCMarkov.OwenScrambling.sampleMean_stepFn_scrambledPoint
#print axioms RQMCMarkov.OwenScrambling.variance_scrambledLaw_eq_sum
#print axioms RQMCMarkov.OwenScrambling.variance_scrambledLaw_sub_of_exact
#print axioms RQMCMarkov.OwenScrambling.dist_corner_lt
#print axioms RQMCMarkov.OwenScrambling.exists_stepFn_approx
#print axioms RQMCMarkov.OwenScrambling.tendsto_pow_mul_variance_scrambledLaw
#print axioms RQMCMarkov.OwenScrambling.revDigits
#print axioms RQMCMarkov.OwenScrambling.cellEnum
#print axioms RQMCMarkov.OwenScrambling.hammersleyDigits
#print axioms RQMCMarkov.OwenScrambling.eq_of_agree_of_agree_rev
#print axioms RQMCMarkov.OwenScrambling.isNet_hammersley
#print axioms RQMCMarkov.OwenScrambling.continuous_stratumMap
#print axioms RQMCMarkov.OwenScrambling.stratumMap_eq_midpoint_add
#print axioms RQMCMarkov.OwenScrambling.midpoint_shift_mem
#print axioms RQMCMarkov.OwenScrambling.integral_sq_sub_half_uniformIco
#print axioms RQMCMarkov.OwenScrambling.integral_id_uniformIco
#print axioms RQMCMarkov.OwenScrambling.integrable_uniformIco_of_continuous
#print axioms RQMCMarkov.OwenScrambling.variance_le_of_lipschitz_half
#print axioms RQMCMarkov.OwenScrambling.memLp_uniformIco_of_lipschitz
#print axioms RQMCMarkov.OwenScrambling.abs_sub_stratumMap_half_le
#print axioms RQMCMarkov.OwenScrambling.variance_stratified_eq
#print axioms RQMCMarkov.OwenScrambling.variance_stratified_le_mc
#print axioms RQMCMarkov.OwenScrambling.variance_stratified_le_lipschitz
#print axioms RQMCMarkov.OwenScrambling.integral_sampleMean_commonShift
#print axioms RQMCMarkov.OwenScrambling.variance_commonShift_le_lipschitz
#print axioms RQMCMarkov.OwenScrambling.variance_uniformIco_id
#print axioms RQMCMarkov.OwenScrambling.variance_uniformIco_affine
#print axioms RQMCMarkov.OwenScrambling.variance_stratified_id
#print axioms RQMCMarkov.OwenScrambling.variance_commonShift_id
#print axioms RQMCMarkov.OwenScrambling.variance_stratified_id_lt_commonShift_id
#print axioms RQMCMarkov.OwenScrambling.sum_cond_eq_of_partition
#print axioms RQMCMarkov.OwenScrambling.variance_sampleMean_partition_le
#print axioms RQMCMarkov.OwenScrambling.DigitWord
#print axioms RQMCMarkov.OwenScrambling.wordPrefix
#print axioms RQMCMarkov.OwenScrambling.OwenTree
#print axioms RQMCMarkov.OwenScrambling.owenWord
#print axioms RQMCMarkov.OwenScrambling.wordPrefix_owenWord_eq
#print axioms RQMCMarkov.OwenScrambling.owenWord_injective
#print axioms RQMCMarkov.OwenScrambling.owenWordEquiv
#print axioms RQMCMarkov.OwenScrambling.digitEquiv
#print axioms RQMCMarkov.OwenScrambling.digitEquiv_apply_val
#print axioms RQMCMarkov.OwenScrambling.digitEquiv_symm_apply_val
#print axioms RQMCMarkov.OwenScrambling.owenCell
#print axioms RQMCMarkov.OwenScrambling.owenCell_apply
#print axioms RQMCMarkov.OwenScrambling.swapTree
#print axioms RQMCMarkov.OwenScrambling.swapTree_swapTree
#print axioms RQMCMarkov.OwenScrambling.owenWord_swapTree
#print axioms RQMCMarkov.OwenScrambling.owenWord_swapTree_eq_iff
#print axioms RQMCMarkov.OwenScrambling.card_filter_owenWord_eq
#print axioms RQMCMarkov.OwenScrambling.card_filter_owenWord
#print axioms RQMCMarkov.OwenScrambling.card_filter_owenCell
#print axioms RQMCMarkov.OwenScrambling.owenNet
#print axioms RQMCMarkov.OwenScrambling.owenNet_mem_stratum
#print axioms RQMCMarkov.OwenScrambling.owenNetSorted
#print axioms RQMCMarkov.OwenScrambling.owenNetSorted_apply
#print axioms RQMCMarkov.OwenScrambling.stratPoints
#print axioms RQMCMarkov.OwenScrambling.measurable_stratPoints
#print axioms RQMCMarkov.OwenScrambling.stratifiedLaw
#print axioms RQMCMarkov.OwenScrambling.measurePreserving_comp_perm
#print axioms RQMCMarkov.OwenScrambling.measure_preimage_comp_of_indepFun
#print axioms RQMCMarkov.OwenScrambling.measurable_comp_of_countable
#print axioms RQMCMarkov.OwenScrambling.sum_measure_preimage_singleton_eq_one
#print axioms RQMCMarkov.OwenScrambling.hasLaw_owenNetSorted
#print axioms RQMCMarkov.OwenScrambling.owenRemainder
#print axioms RQMCMarkov.OwenScrambling.owenNetSorted_eq_stratPoints
#print axioms RQMCMarkov.OwenScrambling.hasLaw_owenRemainder
#print axioms RQMCMarkov.OwenScrambling.measure_preimage_singleton_of_uniform
#print axioms RQMCMarkov.OwenScrambling.hasLaw_apply_of_hasLaw_uniformCube
#print axioms RQMCMarkov.OwenScrambling.hasLaw_owenNet
#print axioms RQMCMarkov.OwenScrambling.sampleMean_owenNet
#print axioms RQMCMarkov.OwenScrambling.measurable_sampleMean
#print axioms RQMCMarkov.OwenScrambling.map_sampleMean_owenNet
#print axioms RQMCMarkov.OwenScrambling.identDistrib_sampleMean_owenNet
#print axioms RQMCMarkov.OwenScrambling.hasLaw_eval_uniformCube
#print axioms RQMCMarkov.OwenScrambling.iIndepFun_eval_uniformCube
#print axioms RQMCMarkov.OwenScrambling.integral_sampleMean_owenNet
#print axioms RQMCMarkov.OwenScrambling.variance_sampleMean_owenNet
#print axioms RQMCMarkov.OwenScrambling.variance_sampleMean_owenNet_le_mc
#print axioms RQMCMarkov.OwenScrambling.variance_sampleMean_owenNet_le_lipschitz
#print axioms RQMCMarkov.OwenScrambling.norm_prod_sub_prod_le
#print axioms RQMCMarkov.OwenScrambling.norm_cexp_mul_I_sub_le
#print axioms RQMCMarkov.OwenScrambling.norm_charFun_sub_le_of_abs_le
#print axioms RQMCMarkov.OwenScrambling.tendstoInDistribution_sum_of_bounded
#print axioms RQMCMarkov.OwenScrambling.integral_uniformIco_eq_intervalIntegral
#print axioms RQMCMarkov.OwenScrambling.sum_range_natCast
#print axioms RQMCMarkov.OwenScrambling.scaled_error_id
#print axioms RQMCMarkov.OwenScrambling.map_sub_half_uniformIco
#print axioms RQMCMarkov.OwenScrambling.hasLaw_scaled_error_id
#print axioms RQMCMarkov.OwenScrambling.cell_error_le
#print axioms RQMCMarkov.OwenScrambling.tendsto_scaled_error
#print axioms RQMCMarkov.OwenScrambling.ae_mem_Ico_of_hasLaw
#print axioms RQMCMarkov.OwenScrambling.measurable_sampleMean_stratumMap
#print axioms RQMCMarkov.OwenScrambling.ae_tendsto_scaled_error
#print axioms RQMCMarkov.OwenScrambling.tendstoInDistribution_scaled_error
#print axioms RQMCMarkov.OwenScrambling.map_mul_sub_half_uniformIco
#print axioms RQMCMarkov.OwenScrambling.ne_gaussianReal_of_measure_Ioi_eq_zero
#print axioms RQMCMarkov.OwenScrambling.limit_law_ne_gaussianReal
#print axioms RQMCMarkov.OwenScrambling.not_tendstoInDistribution_scaled_error_gaussian
#print axioms RQMCMarkov.OwenScrambling.tendsto_sqrt_scaled_error
#print axioms RQMCMarkov.OwenScrambling.ae_tendsto_sqrt_scaled_error
#print axioms RQMCMarkov.OwenScrambling.not_tendstoInDistribution_sqrt_scaled_error_gaussian
#print axioms RQMCMarkov.OwenScrambling.stratVar
#print axioms RQMCMarkov.OwenScrambling.stratVar_nonneg
#print axioms RQMCMarkov.OwenScrambling.abs_variance_add_sub_le
#print axioms RQMCMarkov.OwenScrambling.abs_sub_sub_deriv_mul_le
#print axioms RQMCMarkov.OwenScrambling.abs_variance_cell_sub_le
#print axioms RQMCMarkov.OwenScrambling.abs_integral_sq_deriv_sub_le
#print axioms RQMCMarkov.OwenScrambling.abs_inv_mul_variance_cell_sub_le
#print axioms RQMCMarkov.OwenScrambling.tendsto_cube_mul_stratVar
#print axioms RQMCMarkov.OwenScrambling.integral_sq_deriv_pos
#print axioms RQMCMarkov.OwenScrambling.eventually_stratVar_pos
#print axioms RQMCMarkov.OwenScrambling.stratVar_const
#print axioms RQMCMarkov.OwenScrambling.cellTerm
#print axioms RQMCMarkov.OwenScrambling.stratumMap_mem_Icc
#print axioms RQMCMarkov.OwenScrambling.integrable_cell
#print axioms RQMCMarkov.OwenScrambling.inv_mul_sum_integral_cell
#print axioms RQMCMarkov.OwenScrambling.sum_cellTerm
#print axioms RQMCMarkov.OwenScrambling.iIndepFun_coords
#print axioms RQMCMarkov.OwenScrambling.abs_cellTerm_le
#print axioms RQMCMarkov.OwenScrambling.exists_lipschitz_of_C1
#print axioms RQMCMarkov.OwenScrambling.tendstoInDistribution_stratified
#print axioms RQMCMarkov.OwenScrambling.tendstoInDistribution_stratified_all_n
#print axioms RQMCMarkov.OwenScrambling.sampleMean_owenNet_eq_stratPoints
#print axioms RQMCMarkov.OwenScrambling.tendstoInDistribution_owenNet
#print axioms RQMCMarkov.OwenScrambling.memLp_uniformIco_of_continuousOn
#print axioms RQMCMarkov.OwenScrambling.variance_owenNet_eq_stratVar
#print axioms RQMCMarkov.OwenScrambling.tendsto_cube_mul_variance_owenNet
#print axioms RQMCMarkov.OwenScrambling.owenNet_normal_and_shift_not_normal
#print axioms RQMCMarkov.OwenScrambling.owenNet_exact_of_const
#print axioms RQMCMarkov.OwenScrambling.not_tendstoInDistribution_owenNet_const
#print axioms RQMCMarkov.OwenScrambling.isProbabilityMeasure_scrambledLaw
#print axioms RQMCMarkov.OwenScrambling.tendsto_scrambledLaw_sqrt_error_ge
#print axioms RQMCMarkov.OwenScrambling.not_tendstoInDistribution_sqrt_scaled_error
#print axioms RQMCMarkov.OwenScrambling.integral_pi_eval_mul
#print axioms RQMCMarkov.OwenScrambling.integral_sq_sum_pi
#print axioms RQMCMarkov.OwenScrambling.injective_coord_net
#print axioms RQMCMarkov.OwenScrambling.abs_cell_sub_integral_le
#print axioms RQMCMarkov.OwenScrambling.bijective_cellFin_scramble
#print axioms RQMCMarkov.OwenScrambling.addFn
#print axioms RQMCMarkov.OwenScrambling.addTerm
#print axioms RQMCMarkov.OwenScrambling.digitPoint_eq_stratumMap_cellFin
#print axioms RQMCMarkov.OwenScrambling.sum_addTerm
#print axioms RQMCMarkov.OwenScrambling.memLp_cell_coord
#print axioms RQMCMarkov.OwenScrambling.integral_uniformCube_eval
#print axioms RQMCMarkov.OwenScrambling.memLp_uniformCube_eval
#print axioms RQMCMarkov.OwenScrambling.integral_addTerm
#print axioms RQMCMarkov.OwenScrambling.memLp_addTerm
#print axioms RQMCMarkov.OwenScrambling.sum_integral_sq_addTerm
#print axioms RQMCMarkov.OwenScrambling.abs_addTerm_le
#print axioms RQMCMarkov.OwenScrambling.measurable_addFn
#print axioms RQMCMarkov.OwenScrambling.memLp_addFn
#print axioms RQMCMarkov.OwenScrambling.integral_addFn
#print axioms RQMCMarkov.OwenScrambling.variance_scrambledLaw_addFn
#print axioms RQMCMarkov.OwenScrambling.measurable_addTerm
#print axioms RQMCMarkov.OwenScrambling.tendstoInDistribution_scrambledEstimate_addFn
#print axioms RQMCMarkov.OwenScrambling.scrambledLaw_stepFn_ne_eq_zero
#print axioms RQMCMarkov.OwenScrambling.not_tendstoInDistribution_stepFn
#print axioms RQMCMarkov.OwenScrambling.tendsto_cube_mul_variance_scrambledLaw_addFn
#print axioms RQMCMarkov.OwenScrambling.tendsto_avg_of_forall
#print axioms RQMCMarkov.OwenScrambling.tendstoInDistribution_scrambledLaw_addFn
#print axioms RQMCMarkov.OwenScrambling.variance_scrambledLaw_hammersley_le
#print axioms RQMCMarkov.OwenScrambling.tendsto_variance_scrambledLaw_hammersley
#print axioms RQMCMarkov.OwenScrambling.tendstoInDistribution_scrambledLaw_hammersley
#print axioms RQMCMarkov.OwenScrambling.digitShiftScramble
#print axioms RQMCMarkov.OwenScrambling.scramble_digitShiftScramble
#print axioms RQMCMarkov.OwenScrambling.digitShift_ne_pair_law
#print axioms RQMCMarkov.OwenScrambling.haarProj
#print axioms RQMCMarkov.OwenScrambling.haarVar_eq_sum_sq
#print axioms RQMCMarkov.OwenScrambling.sum_detailKernel_succ
#print axioms RQMCMarkov.OwenScrambling.agreeKernel_nonneg
#print axioms RQMCMarkov.OwenScrambling.sum_abs_detailKernel_succ_le
#print axioms RQMCMarkov.OwenScrambling.agree_of_detailKernel_ne_zero
#print axioms RQMCMarkov.OwenScrambling.abs_cellVal_sub_lt
#print axioms RQMCMarkov.OwenScrambling.abs_digitPoint_sub_le
#print axioms RQMCMarkov.OwenScrambling.sum_fin_two_pi
#print axioms RQMCMarkov.OwenScrambling.haarKernel_two
#print axioms RQMCMarkov.OwenScrambling.sum_mul_mul_eq_mixed
#print axioms RQMCMarkov.OwenScrambling.mixDiff
#print axioms RQMCMarkov.OwenScrambling.cellAvg_mixed_eq
#print axioms RQMCMarkov.OwenScrambling.haarProj_cellAvg_eq
#print axioms RQMCMarkov.OwenScrambling.abs_haarProj_cellAvg_le
#print axioms RQMCMarkov.OwenScrambling.haarVar_cellAvg_le
#print axioms RQMCMarkov.OwenScrambling.sum_range_cast_id
#print axioms RQMCMarkov.OwenScrambling.sum_agreeKernel_mul_cellVal
#print axioms RQMCMarkov.OwenScrambling.sum_detailKernel_mul_cellVal
#print axioms RQMCMarkov.OwenScrambling.digitPoint_sub_digitPoint
#print axioms RQMCMarkov.OwenScrambling.abs_sub_lt_of_floor_eq
#print axioms RQMCMarkov.OwenScrambling.integrable_mixDiff_cellPoint
#print axioms RQMCMarkov.OwenScrambling.abs_haarProj_cellAvg_ge
#print axioms RQMCMarkov.OwenScrambling.card_prefixVal_eq
#print axioms RQMCMarkov.OwenScrambling.card_prefixVal_digit_eq
#print axioms RQMCMarkov.OwenScrambling.haarVar_cellAvg_ge
#print axioms RQMCMarkov.OwenScrambling.gainSeq_two_one
#print axioms RQMCMarkov.OwenScrambling.lvec2
#print axioms RQMCMarkov.OwenScrambling.lvec2_val
#print axioms RQMCMarkov.OwenScrambling.gainCoeff_lvec2
#print axioms RQMCMarkov.OwenScrambling.pow_mul_variance_scrambledLaw_two_ge
#print axioms RQMCMarkov.OwenScrambling.cellResVar_le
#print axioms RQMCMarkov.OwenScrambling.sum_range_ite_pow_le
#print axioms RQMCMarkov.OwenScrambling.pow_mul_variance_scrambledLaw_two_le
#print axioms RQMCMarkov.OwenScrambling.variance_scrambledLaw_two_asymp
#print axioms RQMCMarkov.OwenScrambling.prodFn
#print axioms RQMCMarkov.OwenScrambling.mixDiff_prodFn
#print axioms RQMCMarkov.OwenScrambling.variance_scrambledLaw_prodFn
#print axioms RQMCMarkov.OwenScrambling.avg_variance_scrambledEstimate
#print axioms RQMCMarkov.OwenScrambling.tendsto_avg_variance_given_scramble_div
#print axioms RQMCMarkov.OwenScrambling.abs_sub_sub_mul_le_of_deriv
#print axioms RQMCMarkov.OwenScrambling.abs_mixDiff_sub_le_of_deriv
#print axioms RQMCMarkov.OwenScrambling.variance_scrambledLaw_two_asymp_of_deriv
#print axioms RQMCMarkov.OwenScrambling.not_tendstoInDistribution_gaussian_of_abs_le
#print axioms RQMCMarkov.OwenScrambling.sum_range_ite_lt
#print axioms RQMCMarkov.OwenScrambling.sum_fin_ite_lt
#print axioms RQMCMarkov.OwenScrambling.abs_sum_indicator_sub_le
#print axioms RQMCMarkov.OwenScrambling.variance_indicator_uniformIco
#print axioms RQMCMarkov.OwenScrambling.two_pow_mod_three
#print axioms RQMCMarkov.OwenScrambling.indicatorThird
#print axioms RQMCMarkov.OwenScrambling.integral_indicatorThird
#print axioms RQMCMarkov.OwenScrambling.stratVar_indicator_third_ge
#print axioms RQMCMarkov.OwenScrambling.abs_normalised_error_indicator_le
#print axioms RQMCMarkov.OwenScrambling.not_tendstoInDistribution_owenNet_indicator
#print axioms RQMCMarkov.OwenScrambling.wordFirst
#print axioms RQMCMarkov.OwenScrambling.wordLast
#print axioms RQMCMarkov.OwenScrambling.digitEquiv_add_val
#print axioms RQMCMarkov.OwenScrambling.netPrefix
#print axioms RQMCMarkov.OwenScrambling.netWord
#print axioms RQMCMarkov.OwenScrambling.wordFirst_netWord
#print axioms RQMCMarkov.OwenScrambling.wordLast_netWord
#print axioms RQMCMarkov.OwenScrambling.digitEquiv_netWord_val
#print axioms RQMCMarkov.OwenScrambling.wordPrefix_netWord
#print axioms RQMCMarkov.OwenScrambling.topTree
#print axioms RQMCMarkov.OwenScrambling.wordFirst_owenWord
#print axioms RQMCMarkov.OwenScrambling.tailWord
#print axioms RQMCMarkov.OwenScrambling.wordLast_owenWord_netWord
#print axioms RQMCMarkov.OwenScrambling.deepCell
#print axioms RQMCMarkov.OwenScrambling.deepTail
#print axioms RQMCMarkov.OwenScrambling.deepNet
#print axioms RQMCMarkov.OwenScrambling.deepNet_eq
#print axioms RQMCMarkov.OwenScrambling.deepRemainder
#print axioms RQMCMarkov.OwenScrambling.deepNetSorted
#print axioms RQMCMarkov.OwenScrambling.deepNetSorted_eq
#print axioms RQMCMarkov.OwenScrambling.sampleMean_deepNet
#print axioms RQMCMarkov.OwenScrambling.kOfPrefix
#print axioms RQMCMarkov.OwenScrambling.kOfPrefix_netPrefix
#print axioms RQMCMarkov.OwenScrambling.tailLevel
#print axioms RQMCMarkov.OwenScrambling.tailLevel_natAdd
#print axioms RQMCMarkov.OwenScrambling.swapTail
#print axioms RQMCMarkov.OwenScrambling.swapTail_swapTail
#print axioms RQMCMarkov.OwenScrambling.topTree_swapTail
#print axioms RQMCMarkov.OwenScrambling.tailWord_swapTail
#print axioms RQMCMarkov.OwenScrambling.deepKey
#print axioms RQMCMarkov.OwenScrambling.deepKey_swapTail_eq_iff
#print axioms RQMCMarkov.OwenScrambling.card_filter_deepKey_eq
#print axioms RQMCMarkov.OwenScrambling.sum_card_filter_deepKey
#print axioms RQMCMarkov.OwenScrambling.digitShift
#print axioms RQMCMarkov.OwenScrambling.measurable_digitShift
#print axioms RQMCMarkov.OwenScrambling.sum_measure_preimage_digitShift
#print axioms RQMCMarkov.OwenScrambling.hasLaw_deepRemainder
#print axioms RQMCMarkov.OwenScrambling.hasLaw_deepNetSorted
#print axioms RQMCMarkov.OwenScrambling.variance_deepNet_eq_stratVar
#print axioms RQMCMarkov.OwenScrambling.tendstoInDistribution_deepNet
#print axioms RQMCMarkov.OwenScrambling.unifAvg
#print axioms RQMCMarkov.OwenScrambling.unifAvg_add
#print axioms RQMCMarkov.OwenScrambling.unifAvg_const_mul
#print axioms RQMCMarkov.OwenScrambling.unifAvg_mul_const
#print axioms RQMCMarkov.OwenScrambling.unifAvg_const
#print axioms RQMCMarkov.OwenScrambling.unifAvg_mono
#print axioms RQMCMarkov.OwenScrambling.unifAvg_nonneg
#print axioms RQMCMarkov.OwenScrambling.unifAvg_sum
#print axioms RQMCMarkov.OwenScrambling.abs_unifAvg_le
#print axioms RQMCMarkov.OwenScrambling.sq_unifAvg_mul_le
#print axioms RQMCMarkov.OwenScrambling.sq_unifAvg_le
#print axioms RQMCMarkov.OwenScrambling.unifAvg_mul_of_disjoint
#print axioms RQMCMarkov.OwenScrambling.unifAvg_eval
#print axioms RQMCMarkov.OwenScrambling.unifAvg_prod
#print axioms RQMCMarkov.OwenScrambling.unifAvg_mul_eval_of_forall_ne
#print axioms RQMCMarkov.OwenScrambling.sum_eval_congr
#print axioms RQMCMarkov.OwenScrambling.unifAvg_sum_eval
#print axioms RQMCMarkov.OwenScrambling.ne_of_injOn_insert
#print axioms RQMCMarkov.OwenScrambling.injOn_of_insert
#print axioms RQMCMarkov.OwenScrambling.unifAvg_sq_sum_eq
#print axioms RQMCMarkov.OwenScrambling.unifAvg_pow_four_sum_le
#print axioms RQMCMarkov.OwenScrambling.sum_perm_apply
#print axioms RQMCMarkov.OwenScrambling.norm_unifAvg_le
#print axioms RQMCMarkov.OwenScrambling.unifAvg_sub_complex
#print axioms RQMCMarkov.OwenScrambling.unifAvg_const_complex
#print axioms RQMCMarkov.OwenScrambling.unifAvg_ofReal
#print axioms RQMCMarkov.OwenScrambling.norm_unifAvg_cexp_sub_le
#print axioms RQMCMarkov.OwenScrambling.abs_exp_neg_sub_exp_neg_le
#print axioms RQMCMarkov.OwenScrambling.norm_unifAvg_cexp_le_one
#print axioms RQMCMarkov.OwenScrambling.sq_unifAvg_sum_mul_le
#print axioms RQMCMarkov.OwenScrambling.tendsto_unifAvg_cexp_nodeSum
#print axioms RQMCMarkov.OwenScrambling.cdig
#print axioms RQMCMarkov.OwenScrambling.sum_fin_cast_eq
#print axioms RQMCMarkov.OwenScrambling.sum_cdig
#print axioms RQMCMarkov.OwenScrambling.unifAvg_cdig
#print axioms RQMCMarkov.OwenScrambling.abs_cdig_le
#print axioms RQMCMarkov.OwenScrambling.digWt
#print axioms RQMCMarkov.OwenScrambling.digWt_pos
#print axioms RQMCMarkov.OwenScrambling.scrDev
#print axioms RQMCMarkov.OwenScrambling.prefixVal_mid
#print axioms RQMCMarkov.OwenScrambling.mid_scramble
#print axioms RQMCMarkov.OwenScrambling.integral_digitPoint
#print axioms RQMCMarkov.OwenScrambling.cellAvg_prodFn
#print axioms RQMCMarkov.OwenScrambling.measurable_prodFn
#print axioms RQMCMarkov.OwenScrambling.memLp_prodFn
#print axioms RQMCMarkov.OwenScrambling.sum_scrDev_net
#print axioms RQMCMarkov.OwenScrambling.prodS
#print axioms RQMCMarkov.OwenScrambling.integral_scrambledEstimate_prodFn
#print axioms RQMCMarkov.OwenScrambling.nodeSet
#print axioms RQMCMarkov.OwenScrambling.cellSet
#print axioms RQMCMarkov.OwenScrambling.nodeW
#print axioms RQMCMarkov.OwenScrambling.nodeTerm
#print axioms RQMCMarkov.OwenScrambling.sum_cdig_mul_nodeW
#print axioms RQMCMarkov.OwenScrambling.prodS_eq_sum_nodeTerm
#print axioms RQMCMarkov.OwenScrambling.unifAvg_nodeTerm
#print axioms RQMCMarkov.OwenScrambling.card_agree_agree_net
#print axioms RQMCMarkov.OwenScrambling.agree_update_succ_iff
#print axioms RQMCMarkov.OwenScrambling.agree_comm_iff
#print axioms RQMCMarkov.OwenScrambling.sum_cdig_cellSet_eq_zero
#print axioms RQMCMarkov.OwenScrambling.eq_of_truncDigits_eq_cellSet
#print axioms RQMCMarkov.OwenScrambling.levelWin
#print axioms RQMCMarkov.OwenScrambling.wwin
#print axioms RQMCMarkov.OwenScrambling.nodeW_eq_wwin
#print axioms RQMCMarkov.OwenScrambling.wwin_split
#print axioms RQMCMarkov.OwenScrambling.wX
#print axioms RQMCMarkov.OwenScrambling.wν
#print axioms RQMCMarkov.OwenScrambling.wwin_eq_sum
#print axioms RQMCMarkov.OwenScrambling.injOn_wν
#print axioms RQMCMarkov.OwenScrambling.unifAvg_wX
#print axioms RQMCMarkov.OwenScrambling.abs_wX_le
#print axioms RQMCMarkov.OwenScrambling.sum_levelWin_digWt_sq_le
#print axioms RQMCMarkov.OwenScrambling.unifAvg_sq_wwin_le
#print axioms RQMCMarkov.OwenScrambling.unifAvg_pow_four_wwin_le
#print axioms RQMCMarkov.OwenScrambling.dform
#print axioms RQMCMarkov.OwenScrambling.abs_dform_le
#print axioms RQMCMarkov.OwenScrambling.sq_sum_abs_le
#print axioms RQMCMarkov.OwenScrambling.pow_four_sum_abs_le
#print axioms RQMCMarkov.OwenScrambling.dform_sub
#print axioms RQMCMarkov.OwenScrambling.dform_add
#print axioms RQMCMarkov.OwenScrambling.unifAvg_sq_dform_le
#print axioms RQMCMarkov.OwenScrambling.abs_unifAvg_sq_dform_sub_le
#print axioms RQMCMarkov.OwenScrambling.unifAvg_sq_sum_le_of_sq
#print axioms RQMCMarkov.OwenScrambling.unifAvg_sq_sub_eq
#print axioms RQMCMarkov.OwenScrambling.unifAvg_sq_sum_sub_le_of_near
#print axioms RQMCMarkov.OwenScrambling.mul_le_half_add_sq
#print axioms RQMCMarkov.OwenScrambling.sum_sq_le_sq_sum
#print axioms RQMCMarkov.OwenScrambling.digWt_mul_digWt
#print axioms RQMCMarkov.OwenScrambling.digWt_add
#print axioms RQMCMarkov.OwenScrambling.sum_card_cellSet
#print axioms RQMCMarkov.OwenScrambling.sum_card_cellSet_all
#print axioms RQMCMarkov.OwenScrambling.wwin_split_top
#print axioms RQMCMarkov.OwenScrambling.wwin_congr
#print axioms RQMCMarkov.OwenScrambling.unifAvg_sq_mul_dform
#print axioms RQMCMarkov.OwenScrambling.condVar
#print axioms RQMCMarkov.OwenScrambling.levelVar
#print axioms RQMCMarkov.OwenScrambling.condVarWin
#print axioms RQMCMarkov.OwenScrambling.unifAvg_abs_nodeVar_sub_le
#print axioms RQMCMarkov.OwenScrambling.unifAvg_abs_condVar_sub_le
#print axioms RQMCMarkov.OwenScrambling.levelVar_nonneg
#print axioms RQMCMarkov.OwenScrambling.unifAvg_sq_levelVar_le
#print axioms RQMCMarkov.OwenScrambling.unifAvg_levelVar_mul
#print axioms RQMCMarkov.OwenScrambling.unifAvg_sq_condVarWin_sub_le
#print axioms RQMCMarkov.OwenScrambling.unifAvg_abs_sub_avg_le
#print axioms RQMCMarkov.OwenScrambling.sq_unifAvg_abs_le
#print axioms RQMCMarkov.OwenScrambling.nodeBound
#print axioms RQMCMarkov.OwenScrambling.abs_nodeTerm_le
#print axioms RQMCMarkov.OwenScrambling.unifAvg_sum_sq_nodeBound_le
#print axioms RQMCMarkov.OwenScrambling.unifAvg_sum_pow_four_nodeBound_le
#print axioms RQMCMarkov.OwenScrambling.unifAvg_fin_two
#print axioms RQMCMarkov.OwenScrambling.unifAvg_sq_prodS
#print axioms RQMCMarkov.OwenScrambling.integral_sq_sub_eq_variance_add
#print axioms RQMCMarkov.OwenScrambling.variance_scrambledLaw_eq_of_condMean
#print axioms RQMCMarkov.OwenScrambling.unifAvg_variance_le
#print axioms RQMCMarkov.OwenScrambling.integral_prodFn
#print axioms RQMCMarkov.OwenScrambling.abs_prodFn_sub_le
#print axioms RQMCMarkov.OwenScrambling.unifAvg_sq_prodS_eq
#print axioms RQMCMarkov.OwenScrambling.unifAvg_condVar_ge
#print axioms RQMCMarkov.OwenScrambling.digWt_mul_pow
#print axioms RQMCMarkov.OwenScrambling.tendsto_sqrt_nat_atTop
#print axioms RQMCMarkov.OwenScrambling.tendsto_sqrt_nat_div
#print axioms RQMCMarkov.OwenScrambling.tendsto_unifAvg_cexp_prodS
#print axioms RQMCMarkov.OwenScrambling.eventually_unifAvg_condVar_ge
#print axioms RQMCMarkov.OwenScrambling.integral_mixLaw_complex
#print axioms RQMCMarkov.OwenScrambling.norm_cexp_sub_cexp_le
#print axioms RQMCMarkov.OwenScrambling.sq_integral_abs_sub_le_variance
#print axioms RQMCMarkov.OwenScrambling.tendstoInDistribution_scrambledLaw_of_condMean
#print axioms RQMCMarkov.OwenScrambling.tendstoInDistribution_scrambledLaw_prodFn
#print axioms RQMCMarkov.OwenScrambling.tendstoInDistribution_scrambledLaw_prodFn_hammersley
#print axioms RQMCMarkov.OwenScrambling.scrambledEstimate_bilinAdd
#print axioms RQMCMarkov.OwenScrambling.integral_scrambledEstimate_addFn
#print axioms RQMCMarkov.OwenScrambling.tendstoInDistribution_scrambledLaw_bilinAdd
