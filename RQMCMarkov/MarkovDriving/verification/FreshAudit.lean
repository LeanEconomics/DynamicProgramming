import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Order.CompletePartialOrder
import Mathlib.Data.Int.Star
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Analysis.PSeries
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.IdentDistribIndep
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Probability.BorelCantelli
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # Uniform distribution and complete uniform distribution (CUD)

Post #3: "if the QMC method is 'completely uniformly distributed' (not a given, using Sobol
sequences would fail this) then the generated Markov simulations are consistent". This module
sets up the definitions (Weyl 1916; Knuth's definition of a random sequence; Chentsov 1967;
Owen–Tribble 2005; Chen–Dick–Owen 2011) and the one direction of Weyl's criterion that the
consistency proof needs.

**Definitions.**
* `boxInd S w = ∏ₖ 1{w k ∈ S k}`, the indicator of the product set `S 0 × ⋯ × S (d-1)`, and
  `empAvg g x N = (1/N) ∑_{n<N} g (x n)`, the empirical average.
* `IsUD x` (**uniform distribution** in `[0,1)^d`): all points lie in `[0,1)^d`, and for every
  box `∏ₖ [aₖ, bₖ)` with `0 ≤ aₖ ≤ bₖ ≤ 1` the empirical frequency tends to its volume
  `∏ₖ (bₖ - aₖ)` (`boxVolume_eq_volume`: this is its Lebesgue measure).
* `window u d t = (u t, …, u (t+d-1))`, and `IsCUD u` (**complete uniform distribution**):
  for every `d` the overlapping `d`-tuples `window u d t`, `t = 0, 1, …`, are uniformly
  distributed in `[0,1)^d`.

**Results.**
* `tendsto_empAvg_boxInd_of_isSide`: boxes with arbitrary sides — any `S` with
  `(a,b) ⊆ S` and `S ∩ [0,1) ⊆ [a,b]` (open, closed, half-open) — also have the right limiting
  frequency (sandwich between half-open boxes).
* `IsStepFn d g L`: `g` agrees on `[0,1)^d` with a finite linear combination `∑ cᵣ 1_{Bᵣ}` of
  such box indicators, with `L = ∑ cᵣ vol(Bᵣ)` (its integral). Closure under constants, sums,
  scalar multiples, finite sums and the **tensor product** `g(w₁) h(w₂)` of functions of
  disjoint blocks of coordinates (`isStepFn_append`).
* `tendsto_empAvg_of_isStepFn`: **Weyl's criterion for step functions.** If `x` is uniformly
  distributed and `g` is a step function with integral `L`, then `(1/N) ∑ g(xₙ) → L`. This is the
  direction of Weyl's criterion (box frequencies ⟹ Riemann integrals) used in
  `ChentsovConsistency`: the events of a finite chain driven through `d` steps are finite
  unions of boxes. The converse direction and the extension to Riemann-integrable `g` are not
  needed and are not formalised.
* `IsCUD.mem_Ico`, `IsCUD.isUD_window`: basic facts.
* `not_isUD_of_finite_range`, `not_isCUD_of_finite_range`: a sequence taking finitely many
  values is not even uniformly distributed in `[0,1)`, so not CUD.

**Correction (post #3, codes (c) "a CUD sequence (a full-period linear congruential
generator)").** A full-period LCG `sₙ₊₁ = (a sₙ + c) mod M`, `uₙ = sₙ/M`, is periodic with
period `M`, so it takes at most `M` values; by `not_isCUD_of_finite_range` it is **not** CUD (not
even uniformly distributed in one dimension). What holds is a triangular-array statement: along
a family of generators with `M → ∞`, used over their full period, the `d`-tuple discrepancy of
each period tends to `0` for each fixed `d` (array-CUD; Tribble–Owen 2008 construct such
families). For a fixed `M` this gives only that the `d`-tuples are nearly uniform for `d` up to
a bound depending on `M`; consistency is then an `M → ∞` statement, not a `T → ∞` one.
-/

namespace RQMCMarkov.MarkovDriving

open Filter Topology Finset

/-- A point of the half-open unit cube `[0,1)^d`. -/
def InUnitCube {d : ℕ} (w : Fin d → ℝ) : Prop := ∀ k, w k ∈ Set.Ico (0 : ℝ) 1

/-- The indicator of the product set `S 0 × ⋯ × S (d-1)`: `∏ₖ 1{w k ∈ S k}`. -/
noncomputable def boxInd {d : ℕ} (S : Fin d → Set ℝ) (w : Fin d → ℝ) : ℝ :=
  ∏ k, (S k).indicator 1 (w k)

/-- The empirical average `(1/N) ∑_{n<N} g (x n)`. -/
noncomputable def empAvg {d : ℕ} (g : (Fin d → ℝ) → ℝ) (x : ℕ → Fin d → ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ range N, g (x n)) / N

/-- **Uniform distribution** in `[0,1)^d` (Weyl): every point lies in `[0,1)^d`, and for every
box `∏ₖ [aₖ, bₖ)` with `0 ≤ aₖ ≤ bₖ ≤ 1` the fraction of the first `N` points in the box tends
to the volume `∏ₖ (bₖ - aₖ)`. -/
def IsUD {d : ℕ} (x : ℕ → Fin d → ℝ) : Prop :=
  (∀ n, InUnitCube (x n)) ∧ ∀ a b : Fin d → ℝ, (∀ k, 0 ≤ a k ∧ a k ≤ b k ∧ b k ≤ 1) →
    Tendsto (empAvg (boxInd fun k => Set.Ico (a k) (b k)) x) atTop (𝓝 (∏ k, (b k - a k)))

/-- The overlapping window `(u t, u (t+1), …, u (t+d-1))` of a sequence. -/
def window (u : ℕ → ℝ) (d t : ℕ) : Fin d → ℝ := fun k => u (t + k)

/-- **Complete uniform distribution** (Chentsov 1967; Owen–Tribble 2005): for every `d`, the
overlapping `d`-tuples `(u t, …, u (t+d-1))`, `t = 0, 1, 2, …`, are uniformly distributed in
`[0,1)^d`. -/
def IsCUD (u : ℕ → ℝ) : Prop := ∀ d, IsUD (window u d)

/-- A side `S` of a generalised box: an interval-like set between `(a,b)` and `[a,b]` (inside
`[0,1)`), with `0 ≤ a ≤ b ≤ 1`. Covers `[a,b)`, `(a,b]`, `[a,b]`, `(a,b)`. -/
def IsSide (S : Set ℝ) (a b : ℝ) : Prop :=
  0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧ Set.Ioo a b ⊆ S ∧ S ∩ Set.Ico 0 1 ⊆ Set.Icc a b

/-- `[a,b)` is a side when `0 ≤ a ≤ b ≤ 1`. -/
theorem isSide_Ico {a b : ℝ} (h0 : 0 ≤ a) (hab : a ≤ b) (h1 : b ≤ 1) :
    IsSide (Set.Ico a b) a b :=
  ⟨h0, hab, h1, Set.Ioo_subset_Ico_self, fun _ hx => ⟨hx.1.1, hx.1.2.le⟩⟩

/-- The box volume `∏ₖ (bₖ - aₖ)` is the Lebesgue measure of `∏ₖ [aₖ, bₖ)`. -/
theorem boxVolume_eq_volume {d : ℕ} {a b : Fin d → ℝ} (h : a ≤ b) :
    ∏ k, (b k - a k) = (MeasureTheory.volume (Set.univ.pi fun k => Set.Ico (a k) (b k))).toReal :=
  (Real.volume_pi_Ico_toReal h).symm

open Classical in
/-- `boxInd S w` is `1` if `w ∈ ∏ S` and `0` otherwise. -/
theorem boxInd_eq_ite {d : ℕ} (S : Fin d → Set ℝ) (w : Fin d → ℝ) :
    boxInd S w = if ∀ k, w k ∈ S k then 1 else 0 := by
  unfold boxInd
  split_ifs with h
  · exact Finset.prod_eq_one fun k _ => Set.indicator_of_mem (h k) _
  · push Not at h
    obtain ⟨k, hk⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ k) (Set.indicator_of_notMem hk _)

/-- `boxInd S w ∈ {0, 1}`: it is nonnegative. -/
theorem boxInd_nonneg {d : ℕ} (S : Fin d → Set ℝ) (w : Fin d → ℝ) : 0 ≤ boxInd S w := by
  classical
  rw [boxInd_eq_ite]
  split_ifs
  · exact zero_le_one
  · exact le_refl 0

/-- `boxInd S w ∈ {0, 1}`: it is at most one. -/
theorem boxInd_le_one {d : ℕ} (S : Fin d → Set ℝ) (w : Fin d → ℝ) : boxInd S w ≤ 1 := by
  classical
  rw [boxInd_eq_ite]
  split_ifs
  · exact le_refl 1
  · exact zero_le_one

/-- `boxInd S w = 1` iff `w ∈ ∏ S`. -/
theorem boxInd_eq_one_iff {d : ℕ} (S : Fin d → Set ℝ) (w : Fin d → ℝ) :
    boxInd S w = 1 ↔ ∀ k, w k ∈ S k := by
  classical
  rw [boxInd_eq_ite]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h0 => absurd h0 zero_ne_one, fun h' => absurd h' h⟩

/-- Monotonicity of box indicators in the box. -/
theorem boxInd_le_boxInd {d : ℕ} {S S' : Fin d → Set ℝ} {w : Fin d → ℝ}
    (h : (∀ k, w k ∈ S k) → ∀ k, w k ∈ S' k) : boxInd S w ≤ boxInd S' w := by
  classical
  rw [boxInd_eq_ite, boxInd_eq_ite]
  split_ifs with h1 h2
  · exact le_refl 1
  · exact absurd (h h1) h2
  · exact zero_le_one
  · exact le_refl 0

/-- Monotonicity of empirical averages. -/
theorem empAvg_le_empAvg {d : ℕ} {g g' : (Fin d → ℝ) → ℝ} {x : ℕ → Fin d → ℝ}
    (h : ∀ n, g (x n) ≤ g' (x n)) (N : ℕ) : empAvg g x N ≤ empAvg g' x N :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun n _ => h n) (Nat.cast_nonneg N)

/-- **General boxes.** If `x` is uniformly distributed then every box whose sides `S k` lie
between `(aₖ, bₖ)` and `[aₖ, bₖ]` has limiting frequency `∏ₖ (bₖ - aₖ)`. -/
theorem tendsto_empAvg_boxInd_of_isSide {d : ℕ} {x : ℕ → Fin d → ℝ} (hx : IsUD x)
    {S : Fin d → Set ℝ} {a b : Fin d → ℝ} (hS : ∀ k, IsSide (S k) (a k) (b k)) :
    Tendsto (empAvg (boxInd S) x) atTop (𝓝 (∏ k, (b k - a k))) := by
  set lo : ℝ → Fin d → ℝ := fun ε k => min (a k + ε) (b k) with hlo
  set hi : ℝ → Fin d → ℝ := fun ε k => min (b k + ε) 1 with hhi
  have hlo' : ∀ ε k, lo ε k = min (a k + ε) (b k) := fun _ _ => rfl
  have hhi' : ∀ ε k, hi ε k = min (b k + ε) 1 := fun _ _ => rfl
  have hLc : Continuous fun ε => ∏ k, (b k - lo ε k) := by
    rw [hlo]
    fun_prop
  have hUc : Continuous fun ε => ∏ k, (hi ε k - a k) := by
    rw [hhi]
    fun_prop
  have hL0 : ∏ k, (b k - lo 0 k) = ∏ k, (b k - a k) := by
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hlo', add_zero, min_eq_left (hS k).2.1]
  have hU0 : ∏ k, (hi 0 k - a k) = ∏ k, (b k - a k) := by
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hhi', add_zero, min_eq_left (hS k).2.2.1]
  -- the lower and upper boxes are valid boxes and sandwich `S`
  have hlo_valid : ∀ ε, 0 < ε → ∀ k, 0 ≤ lo ε k ∧ lo ε k ≤ b k ∧ b k ≤ 1 := fun ε hε k =>
    ⟨le_min (by linarith [(hS k).1]) ((hS k).1.trans (hS k).2.1), min_le_right _ _,
      (hS k).2.2.1⟩
  have hhi_valid : ∀ ε, 0 < ε → ∀ k, 0 ≤ a k ∧ a k ≤ hi ε k ∧ hi ε k ≤ 1 := fun ε hε k =>
    ⟨(hS k).1, le_min (by linarith [(hS k).2.1]) ((hS k).2.1.trans (hS k).2.2.1),
      min_le_right _ _⟩
  have hlow : ∀ ε, 0 < ε → ∀ N, empAvg (boxInd fun k => Set.Ico (lo ε k) (b k)) x N ≤
      empAvg (boxInd S) x N := by
    intro ε hε N
    refine empAvg_le_empAvg (fun n => boxInd_le_boxInd fun h k => ?_) N
    refine (hS k).2.2.2.1 ⟨?_, (h k).2⟩
    have h1 := (h k).1
    have h2 := (h k).2
    rcases le_total (a k + ε) (b k) with hab | hab
    · rw [hlo' ε k, min_eq_left hab] at h1
      linarith
    · rw [hlo' ε k, min_eq_right hab] at h1
      linarith
  have hupp : ∀ ε, 0 < ε → ∀ N, empAvg (boxInd S) x N ≤
      empAvg (boxInd fun k => Set.Ico (a k) (hi ε k)) x N := by
    intro ε hε N
    refine empAvg_le_empAvg (fun n => boxInd_le_boxInd fun h k => ?_) N
    have hmem := (hS k).2.2.2.2 ⟨h k, hx.1 n k⟩
    refine ⟨hmem.1, ?_⟩
    rcases le_total (b k + ε) 1 with hb | hb
    · rw [hhi' ε k, min_eq_left hb]
      linarith [hmem.2]
    · rw [hhi' ε k, min_eq_right hb]
      exact (hx.1 n k).2
  refine tendsto_order.2 ⟨fun c hc => ?_, fun c hc => ?_⟩
  · have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), c < ∏ k, (b k - lo ε k) :=
      continuousAt_const.eventually_lt hLc.continuousAt (by rw [hL0]; exact hc)
    obtain ⟨δ, hδ, hδc⟩ := Metric.eventually_nhds_iff.1 hev
    have hε : (0 : ℝ) < δ / 2 := half_pos hδ
    have hcε : c < ∏ k, (b k - lo (δ / 2) k) := hδc (by
      rw [Real.dist_eq, sub_zero, abs_of_pos hε]
      exact half_lt_self hδ)
    filter_upwards [(hx.2 _ _ (hlo_valid _ hε)).eventually (lt_mem_nhds hcε)] with N hN
    exact hN.trans_le (hlow _ hε N)
  · have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), ∏ k, (hi ε k - a k) < c :=
      hUc.continuousAt.eventually_lt continuousAt_const (by rw [hU0]; exact hc)
    obtain ⟨δ, hδ, hδc⟩ := Metric.eventually_nhds_iff.1 hev
    have hε : (0 : ℝ) < δ / 2 := half_pos hδ
    have hcε : ∏ k, (hi (δ / 2) k - a k) < c := hδc (by
      rw [Real.dist_eq, sub_zero, abs_of_pos hε]
      exact half_lt_self hδ)
    filter_upwards [(hx.2 _ _ (hhi_valid _ hε)).eventually (gt_mem_nhds hcε)] with N hN
    exact (hupp _ hε N).trans_lt hN

/-- **Step functions on `[0,1)^d`.** `IsStepFn d g L`: on `[0,1)^d`, `g` is a finite linear
combination `∑ᵣ cᵣ 1_{Bᵣ}` of indicators of generalised boxes `Bᵣ = ∏ₖ Sᵣₖ` (`IsSide`), and
`L = ∑ᵣ cᵣ ∏ₖ (bᵣₖ - aᵣₖ)` is the corresponding integral. -/
def IsStepFn (d : ℕ) (g : (Fin d → ℝ) → ℝ) (L : ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℝ) (S : ι → Fin d → Set ℝ) (a b : ι → Fin d → ℝ),
    (∀ r k, IsSide (S r k) (a r k) (b r k)) ∧
    (∀ w, InUnitCube w → g w = ∑ r, c r * boxInd (S r) w) ∧
    L = ∑ r, c r * ∏ k, (b r k - a r k)

/-- **Weyl's criterion for step functions.** If `x` is uniformly distributed in `[0,1)^d` and
`g` is a step function with integral `L`, the empirical averages of `g` tend to `L`. -/
theorem tendsto_empAvg_of_isStepFn {d : ℕ} {x : ℕ → Fin d → ℝ} (hx : IsUD x)
    {g : (Fin d → ℝ) → ℝ} {L : ℝ} (hg : IsStepFn d g L) :
    Tendsto (empAvg g x) atTop (𝓝 L) := by
  obtain ⟨ι, _, c, S, a, b, hS, hrep, hL⟩ := hg
  have heq : empAvg g x = fun N => ∑ r, c r * empAvg (boxInd (S r)) x N := by
    funext N
    unfold empAvg
    rw [Finset.sum_congr rfl fun n _ => hrep (x n) (hx.1 n), Finset.sum_comm, Finset.sum_div]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Finset.mul_sum, mul_div_assoc]
  rw [heq, hL]
  exact tendsto_finsetSum _ fun r _ =>
    (tendsto_empAvg_boxInd_of_isSide hx (hS r)).const_mul (c r)

/-- Step functions can be changed off `[0,1)^d`. -/
theorem IsStepFn.congr {d : ℕ} {g g' : (Fin d → ℝ) → ℝ} {L : ℝ} (hg : IsStepFn d g L)
    (h : ∀ w, InUnitCube w → g w = g' w) : IsStepFn d g' L := by
  obtain ⟨ι, hι, c, S, a, b, hS, hrep, hL⟩ := hg
  exact ⟨ι, hι, c, S, a, b, hS, fun w hw => (h w hw).symm.trans (hrep w hw), hL⟩

/-- The integral of a step function can be rewritten. -/
theorem IsStepFn.of_eq {d : ℕ} {g : (Fin d → ℝ) → ℝ} {L L' : ℝ} (hg : IsStepFn d g L)
    (h : L = L') : IsStepFn d g L' := h ▸ hg

/-- A single generalised box is a step function with integral its volume. -/
theorem isStepFn_boxInd {d : ℕ} {S : Fin d → Set ℝ} {a b : Fin d → ℝ}
    (hS : ∀ k, IsSide (S k) (a k) (b k)) : IsStepFn d (boxInd S) (∏ k, (b k - a k)) :=
  ⟨Unit, inferInstance, fun _ => 1, fun _ => S, fun _ => a, fun _ => b, fun _ => hS,
    fun w _ => by rw [Fintype.sum_unique, one_mul],
    by rw [Fintype.sum_unique, one_mul]⟩

/-- Constants are step functions. -/
theorem isStepFn_const (d : ℕ) (c : ℝ) : IsStepFn d (fun _ => c) c := by
  refine ⟨Unit, inferInstance, fun _ => c, fun _ _ => Set.Ico 0 1, fun _ _ => 0, fun _ _ => 1,
    fun _ _ => isSide_Ico (le_refl 0) zero_le_one (le_refl 1), fun w hw => ?_, ?_⟩
  · rw [Fintype.sum_unique, (boxInd_eq_one_iff _ w).2 hw, mul_one]
  · rw [Fintype.sum_unique, Finset.prod_eq_one fun k _ => sub_zero 1, mul_one]

/-- Sums of step functions are step functions. -/
theorem IsStepFn.add {d : ℕ} {g h : (Fin d → ℝ) → ℝ} {L M : ℝ} (hg : IsStepFn d g L)
    (hh : IsStepFn d h M) : IsStepFn d (fun w => g w + h w) (L + M) := by
  obtain ⟨ι, hι, c, S, a, b, hS, hrep, hL⟩ := hg
  obtain ⟨κ, hκ, c', S', a', b', hS', hrep', hM⟩ := hh
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim c c', Sum.elim S S', Sum.elim a a', Sum.elim b b',
    fun r k => ?_, fun w hw => ?_, ?_⟩
  · rcases r with r | r
    · exact hS r k
    · exact hS' r k
  · dsimp only
    rw [Fintype.sum_sum_type, hrep w hw, hrep' w hw]
    rfl
  · rw [Fintype.sum_sum_type, hL, hM]
    rfl

/-- Scalar multiples of step functions are step functions. -/
theorem IsStepFn.const_mul {d : ℕ} {g : (Fin d → ℝ) → ℝ} {L : ℝ} (hg : IsStepFn d g L)
    (e : ℝ) : IsStepFn d (fun w => e * g w) (e * L) := by
  obtain ⟨ι, hι, c, S, a, b, hS, hrep, hL⟩ := hg
  refine ⟨ι, hι, fun r => e * c r, S, a, b, hS, fun w hw => ?_, ?_⟩
  · dsimp only
    rw [hrep w hw, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => (mul_assoc _ _ _).symm
  · rw [hL, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => (mul_assoc _ _ _).symm

/-- Differences of step functions are step functions. -/
theorem IsStepFn.sub {d : ℕ} {g h : (Fin d → ℝ) → ℝ} {L M : ℝ} (hg : IsStepFn d g L)
    (hh : IsStepFn d h M) : IsStepFn d (fun w => g w - h w) (L - M) := by
  refine ((hg.add (hh.const_mul (-1))).congr fun w _ => ?_).of_eq ?_
  · ring
  · ring

/-- Finite sums of step functions are step functions. -/
theorem isStepFn_finset_sum {d : ℕ} {α : Type*} (s : Finset α) {g : α → (Fin d → ℝ) → ℝ}
    {L : α → ℝ} (h : ∀ i ∈ s, IsStepFn d (g i) (L i)) :
    IsStepFn d (fun w => ∑ i ∈ s, g i w) (∑ i ∈ s, L i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ((isStepFn_const d 0).congr fun w _ => ?_).of_eq ?_
    · rw [Finset.sum_empty]
    · rw [Finset.sum_empty]
  | insert i s hi ih =>
    have hs := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    refine (((h i (Finset.mem_insert_self i s)).add hs).congr fun w _ => ?_).of_eq ?_
    · rw [Finset.sum_insert hi]
    · rw [Finset.sum_insert hi]

/-- The box indicator of an appended box factorises over the two blocks of coordinates. -/
theorem boxInd_append {m m' : ℕ} (S : Fin m → Set ℝ) (S' : Fin m' → Set ℝ)
    (w : Fin (m + m') → ℝ) :
    boxInd (Fin.append S S') w =
      boxInd S (fun k => w (Fin.castAdd m' k)) * boxInd S' (fun k => w (Fin.natAdd m k)) := by
  unfold boxInd
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- **Tensor products.** If `g` is a step function on `[0,1)^m` and `h` one on `[0,1)^{m'}`,
then `w ↦ g(w₀, …, w_{m-1}) h(w_m, …, w_{m+m'-1})` is a step function on `[0,1)^{m+m'}`, with
integral the product of the integrals. -/
theorem IsStepFn.append {m m' : ℕ} {g : (Fin m → ℝ) → ℝ} {h : (Fin m' → ℝ) → ℝ} {L M : ℝ}
    (hg : IsStepFn m g L) (hh : IsStepFn m' h M) :
    IsStepFn (m + m')
      (fun w => g (fun k => w (Fin.castAdd m' k)) * h (fun k => w (Fin.natAdd m k))) (L * M) := by
  obtain ⟨ι, hι, c, S, a, b, hS, hrep, hL⟩ := hg
  obtain ⟨κ, hκ, c', S', a', b', hS', hrep', hM⟩ := hh
  refine ⟨ι × κ, inferInstance, fun p => c p.1 * c' p.2, fun p => Fin.append (S p.1) (S' p.2),
    fun p => Fin.append (a p.1) (a' p.2), fun p => Fin.append (b p.1) (b' p.2),
    fun p k => ?_, fun w hw => ?_, ?_⟩
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) k
    · dsimp only
      rw [Fin.append_left, Fin.append_left, Fin.append_left]
      exact hS p.1 k
    · dsimp only
      rw [Fin.append_right, Fin.append_right, Fin.append_right]
      exact hS' p.2 k
  · dsimp only
    rw [hrep _ fun k => hw _, hrep' _ fun k => hw _, Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => ?_
    rw [boxInd_append]
    ring
  · rw [hL, hM, Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => ?_
    rw [Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    ring

/-- A CUD sequence takes values in `[0,1)`. -/
theorem IsCUD.mem_Ico {u : ℕ → ℝ} (hu : IsCUD u) (t : ℕ) : u t ∈ Set.Ico (0 : ℝ) 1 :=
  (hu 1).1 t 0

/-- For a CUD sequence, the windows of each length are uniformly distributed. -/
theorem IsCUD.isUD_window {u : ℕ → ℝ} (hu : IsCUD u) (d : ℕ) : IsUD (window u d) := hu d

/-- Windows of a sequence in `[0,1)` lie in the unit cube. -/
theorem window_mem {u : ℕ → ℝ} (hu : ∀ t, u t ∈ Set.Ico (0 : ℝ) 1) (d t : ℕ) :
    InUnitCube (window u d t) := fun k => hu (t + k)

/-- **Finitely many values are not uniformly distributed.** If `u` takes only finitely many
values then the one-dimensional sequence `u` is not uniformly distributed in `[0,1)`: of the
`M + 1` intervals `[k/(M+1), (k+1)/(M+1))` (`M` the number of values), one contains no value,
so its frequency is `0`, not `1/(M+1)`. -/
theorem not_isUD_of_finite_range {u : ℕ → ℝ} (hfin : (Set.range u).Finite) :
    ¬ IsUD (window u 1) := by
  intro hUD
  set F := hfin.toFinset with hF
  set M := F.card with hM
  have hMpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  -- every interval `I k` contains a value of `u`
  have hhit : ∀ k : Fin (M + 1),
      ∃ t, u t ∈ Set.Ico ((k : ℝ) / (M + 1)) (((k : ℝ) + 1) / (M + 1)) := by
    intro k
    by_contra hnone
    push Not at hnone
    have hk1 : (k : ℝ) + 1 ≤ (M : ℝ) + 1 := by
      have := k.isLt
      have : ((k : ℕ) : ℝ) + 1 ≤ ((M : ℕ) : ℝ) + 1 := by exact_mod_cast this
      exact this
    have hval : ∀ _ : Fin 1, 0 ≤ (k : ℝ) / (M + 1) ∧ (k : ℝ) / (M + 1) ≤ ((k : ℝ) + 1) / (M + 1) ∧
        ((k : ℝ) + 1) / (M + 1) ≤ 1 := fun _ =>
      ⟨by positivity, div_le_div_of_nonneg_right (by linarith) hMpos.le,
        (div_le_one hMpos).2 hk1⟩
    have hlim := hUD.2 (fun _ => (k : ℝ) / (M + 1)) (fun _ => ((k : ℝ) + 1) / (M + 1)) hval
    have hzero : empAvg (boxInd fun _ => Set.Ico ((k : ℝ) / (M + 1)) (((k : ℝ) + 1) / (M + 1)))
        (window u 1) = fun _ => 0 := by
      funext N
      unfold empAvg
      rw [Finset.sum_eq_zero fun t _ => ?_, zero_div]
      classical
      rw [boxInd_eq_ite]
      split_ifs with hall
      · exact absurd (hall 0) (hnone t)
      · rfl
    rw [hzero] at hlim
    have h0 := tendsto_nhds_unique tendsto_const_nhds hlim
    rw [Fin.prod_univ_one, ← sub_div, add_sub_cancel_left] at h0
    exact absurd h0.symm (one_div_pos.2 hMpos).ne'
  choose t ht using hhit
  have hmaps : Set.MapsTo (fun k : Fin (M + 1) => u (t k)) (Finset.univ : Finset (Fin (M + 1)))
      (F : Set ℝ) := fun k _ => by
    rw [hF, Set.Finite.coe_toFinset]
    exact ⟨t k, rfl⟩
  have hinj : Set.InjOn (fun k : Fin (M + 1) => u (t k)) (Finset.univ : Finset (Fin (M + 1))) := by
    intro k _ k' _ hkk'
    have h1 := ht k
    have h2 := ht k'
    change u (t k) = u (t k') at hkk'
    rw [hkk'] at h1
    rw [Set.mem_Ico, div_le_iff₀ hMpos, lt_div_iff₀ hMpos] at h1 h2
    have hlt1 : ((k : ℕ) : ℝ) < ((k' : ℕ) : ℝ) + 1 := by linarith
    have hlt2 : ((k' : ℕ) : ℝ) < ((k : ℕ) : ℝ) + 1 := by linarith
    have hn1 : (k : ℕ) < (k' : ℕ) + 1 := by exact_mod_cast hlt1
    have hn2 : (k' : ℕ) < (k : ℕ) + 1 := by exact_mod_cast hlt2
    exact Fin.ext (by omega)
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  omega

/-- **Finitely many values are not CUD** (post #3, codes (c)): in particular a periodic
sequence such as a full-period linear congruential generator `uₙ = sₙ/M` is not CUD. -/
theorem not_isCUD_of_finite_range {u : ℕ → ℝ} (hfin : (Set.range u).Finite) : ¬ IsCUD u :=
  fun hu => not_isUD_of_finite_range hfin (hu 1)

/-- A periodic sequence takes finitely many values, so it is not CUD. -/
theorem not_isCUD_of_periodic {u : ℕ → ℝ} {M : ℕ} (hM : 0 < M) (hper : ∀ t, u (t + M) = u t) :
    ¬ IsCUD u := by
  refine not_isCUD_of_finite_range ((Set.finite_range fun r : Fin M => u r).subset ?_)
  rintro _ ⟨t, rfl⟩
  refine ⟨⟨t % M, Nat.mod_lt t hM⟩, ?_⟩
  change u (t % M) = u t
  have key : ∀ q r, u (r + M * q) = u r := by
    intro q r
    induction q with
    | zero => rw [mul_zero, add_zero]
    | succ q ih => rw [mul_add, mul_one, ← add_assoc, hper, ih]
  conv_rhs => rw [← Nat.mod_add_div t M]
  exact (key _ _).symm

end RQMCMarkov.MarkovDriving

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

namespace RQMCMarkov.MarkovDriving

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

end RQMCMarkov.MarkovDriving

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

namespace RQMCMarkov.MarkovDriving

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

end RQMCMarkov.MarkovDriving

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Driving a finite Markov chain by uniforms: inverse CDF, paths, stacks, counts (post #3)

Post #3 simulates a chain with `n` states and transition matrix `P` by the inverse-CDF rule: from
state `i` with a uniform `u`, go to the smallest `j` with `u ≤ cs_{ij} = Σ_{k ≤ j} p_{ik}`. A
uniform sequence `u¹, u², …` then "drives" the chain; in the stack representation each state has
its own sequence, and the `k`-th departure from `i` uses point `k` of stack `i`.

**Conventions.** States are `Fin n`, `0`-indexed (post #3's `x_j` is `j - 1 : Fin n`); a
stochastic matrix is `P : Fin n → Fin n → ℝ` with `IsStochastic P` (nonnegative rows summing to
one). Time starts at `0`: a path is `x : ℕ → S` with `x 0 = x₀`, and `u t` drives the
transition `t → t + 1` (post #3's `u^t` and `x^{t+1}`). Counts over the horizon `T` use the
times `t < T` (occupation) and the transitions `t → t + 1`, `t < T`.

## Main definitions

* `IsStochastic P`; `cumProb P i m = Σ_{k < m} P i k` (post #3's `cs_{ij}` is `cumProb P i j`);
  `step P i u`, the inverse-CDF update, total (the last state when no `j` qualifies, `u > 1`).
* `drive G x₀ u` (any update rule `G : S → α → S`) and `drivenPath P x₀ u = drive (step P) x₀ u`.
* `stackDrive G x₀ v` (per-state stacks `v : S → ℕ → α`), `stackPath P x₀ v`, and the
  `departureIndex path t = #{t' < t : path t' = path t}`.
* `occCount path i T` (the visit counter) and `transCount path i j T`.
* `IsSpellStart`, `runLength path t T` (censored at `T`), `spellCount path i T`.

## Main results

* `step_eq_iff`: for `u ∈ (0, 1]`, `step P i u = j ↔ cs_{i,j-1} < u ≤ cs_{ij}`;
  `step_preimage_inter_Ioc`, `step_mono`, `measurable_step`; `step_zero` (precision: at `u = 0`
  the rule picks the first state even if `p_{i1} = 0`, a null event).
* `uniformIco_step_eq`, `volume_step_eq`: `volume {u ∈ [0,1) : step P i u = j} = P i j`
  (post #3, "the probability that it falls in the interval … is exactly … `p_{2j}`").
* `step_post3_example`: post #3's `n = 3` example (`u = 0.79` goes to the second state).
* `drive_eq_iff`, `stackDrive_eq_iff`: pathwise descriptions (the path equals `s` up to `T` iff
  `s` starts at `x₀` and each transition of `s` is produced by the corresponding uniform);
  `stackDrive_succ` ("the `k`-th visit to state `i` uses point `k` of stack `i`");
  `departureIndex_injective`: the stack entries used at different times are different.
* Counts: `occCount_succ`, `transCount_succ`, `occCount_add`, `transCount_add`,
  `sum_occCount` (`Σ_i N_i(T) = T`), `sum_transCount_right` (`Σ_j N_ij(T) = N_i(T)`),
  `sum_transCount_left`, `flowBalance`, `abs_flowBalance_le` (post #3, "every state is entered as
  often as it is left (allowing for the first and last states)").
* Spells: `runLength_eq_iff`, `spellCount_succ_eq` (spells of `i` = start + entries into `i`).
-/

namespace RQMCMarkov.MarkovDriving

open MeasureTheory Finset

/-- A **stochastic matrix** on a finite state space: nonnegative rows summing to one. -/
structure IsStochastic {S : Type*} [Fintype S] (P : S → S → ℝ) : Prop where
  /-- Every transition probability is nonnegative. -/
  nonneg : ∀ i j, 0 ≤ P i j
  /-- Every row sums to one. -/
  sum_eq_one : ∀ i, ∑ j, P i j = 1

variable {n : ℕ}

/-- The cumulative row sum `cumProb P i m = Σ_{k < m} P i k` (states `Fin n`, `0`-indexed).
Post #3's `cs_{ij} = Σ_{k=1}^{j} p_{ik}` (`1`-indexed) is `cumProb P i j`; for a state
`j : Fin n` the post's interval `(cs_{i,j-1}, cs_{ij}]` is `(cumProb P i j, cumProb P i (j+1)]`. -/
noncomputable def cumProb (P : Fin n → Fin n → ℝ) (i : Fin n) (m : ℕ) : ℝ :=
  ∑ k ∈ univ.filter (fun k : Fin n ↦ (k : ℕ) < m), P i k

/-- The last state `n - 1` of `Fin n` (`Fin n` is nonempty since it contains `i`). -/
def lastState (i : Fin n) : Fin n := ⟨n - 1, by have := i.isLt; omega⟩

/-- **The inverse-CDF update** (post #3): from state `i` with uniform `u`, go to the smallest
`j` with `u ≤ cs_{ij}`, i.e. `u ≤ cumProb P i (j + 1)`. Total: if no such `j` exists (only when
`u > 1`), go to the last state. -/
noncomputable def step (P : Fin n → Fin n → ℝ) (i : Fin n) (u : ℝ) : Fin n :=
  (insert (lastState i) (univ.filter fun j : Fin n ↦ u ≤ cumProb P i (j + 1))).min'
    (insert_nonempty _ _)

/-- `cumProb P i 0 = 0`. -/
theorem cumProb_zero (P : Fin n → Fin n → ℝ) (i : Fin n) : cumProb P i 0 = 0 := by
  unfold cumProb
  rw [Finset.sum_eq_zero]
  intro k hk
  exact absurd (Finset.mem_filter.1 hk).2 (Nat.not_lt_zero _)

/-- `cumProb P i (j + 1) = cumProb P i j + P i j`. -/
theorem cumProb_succ (P : Fin n → Fin n → ℝ) (i j : Fin n) :
    cumProb P i (j + 1) = cumProb P i j + P i j := by
  unfold cumProb
  have h : univ.filter (fun k : Fin n ↦ (k : ℕ) < j + 1) =
      insert j (univ.filter (fun k : Fin n ↦ (k : ℕ) < j)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    rw [Nat.lt_succ_iff, Nat.le_iff_lt_or_eq, Fin.ext_iff]
    tauto
  rw [h, Finset.sum_insert, add_comm]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, lt_irrefl, not_false_eq_true]

/-- For `m ≥ n`, `cumProb P i m` is the whole row sum. -/
theorem cumProb_of_le (P : Fin n → Fin n → ℝ) (i : Fin n) {m : ℕ} (hm : n ≤ m) :
    cumProb P i m = ∑ k, P i k := by
  unfold cumProb
  rw [Finset.filter_true_of_mem]
  intro k _
  exact lt_of_lt_of_le k.isLt hm

/-- The cumulative sums of a nonnegative row are monotone. -/
theorem cumProb_mono {P : Fin n → Fin n → ℝ} (hP : ∀ i j, 0 ≤ P i j) (i : Fin n) :
    Monotone (cumProb P i) := by
  intro a b hab
  unfold cumProb
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ ↦ hP i k)
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  omega

/-- The cumulative sums of a stochastic row lie in `[0, 1]`. -/
theorem cumProb_mem_Icc {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n) (m : ℕ) :
    cumProb P i m ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · rw [← cumProb_zero P i]
    exact cumProb_mono hP.nonneg i (Nat.zero_le m)
  · rw [← hP.sum_eq_one i, ← cumProb_of_le P i (le_max_left n m)]
    exact cumProb_mono hP.nonneg i (le_max_right n m)

/-- **The inverse-CDF rule** (post #3): for `u ∈ (0, 1]`, `step P i u = j` iff
`cs_{i,j-1} < u ≤ cs_{ij}`, i.e. `cumProb P i j < u ≤ cumProb P i (j + 1)`. -/
theorem step_eq_iff {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i j : Fin n) {u : ℝ}
    (hu : u ∈ Set.Ioc (0 : ℝ) 1) :
    step P i u = j ↔ cumProb P i j < u ∧ u ≤ cumProb P i (j + 1) := by
  have hlast : cumProb P i ((lastState i : ℕ) + 1) = 1 := by
    rw [cumProb_of_le P i (by simp only [lastState]; omega), hP.sum_eq_one i]
  constructor
  · intro h
    have hj : j ∈ insert (lastState i) (univ.filter fun j : Fin n ↦ u ≤ cumProb P i (j + 1)) :=
      h ▸ Finset.min'_mem _ _
    refine ⟨?_, ?_⟩
    · by_cases hj0 : (j : ℕ) = 0
      · rw [hj0, cumProb_zero]
        exact hu.1
      · by_contra hcon
        have hk : (⟨j - 1, by omega⟩ : Fin n) ∈
            insert (lastState i) (univ.filter fun j : Fin n ↦ u ≤ cumProb P i (j + 1)) := by
          refine Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩)
          have : (j : ℕ) - 1 + 1 = j := by omega
          change u ≤ cumProb P i ((j : ℕ) - 1 + 1)
          rw [this]
          exact le_of_not_gt hcon
        have hle : step P i u ≤ ⟨j - 1, by omega⟩ := Finset.min'_le _ _ hk
        rw [h, Fin.le_def] at hle
        change (j : ℕ) ≤ j - 1 at hle
        omega
    · rcases Finset.mem_insert.1 hj with hj | hj
      · rw [hj, hlast]
        exact hu.2
      · exact (Finset.mem_filter.1 hj).2
  · rintro ⟨h1, h2⟩
    have hj : j ∈ insert (lastState i) (univ.filter fun j : Fin n ↦ u ≤ cumProb P i (j + 1)) :=
      Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩)
    refine le_antisymm (Finset.min'_le _ _ hj) (Finset.le_min' _ _ _ ?_)
    intro y hy
    rcases Finset.mem_insert.1 hy with hy | hy
    · rw [hy, Fin.le_def]
      simp only [lastState]
      omega
    · have hy' := (Finset.mem_filter.1 hy).2
      by_contra hlt
      rw [not_le, Fin.lt_def] at hlt
      have := cumProb_mono hP.nonneg i (show (y : ℕ) + 1 ≤ j by omega)
      linarith

/-- The inverse-CDF update is monotone in the uniform. -/
theorem step_mono (P : Fin n → Fin n → ℝ) (i : Fin n) : Monotone (step P i) := by
  intro u u' huu'
  refine Finset.min'_subset _ ?_
  intro j hj
  rcases Finset.mem_insert.1 hj with hj | hj
  · exact hj ▸ Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_filter.2
      ⟨Finset.mem_univ _, le_trans huu' (Finset.mem_filter.1 hj).2⟩)

/-- **Precision on post #3's rule at `u = 0`**: "the smallest index such that `u ≤ cs`" sends
`u = 0` to the first state even when `p_{i1} = 0`; this is why `step_eq_iff` takes
`u ∈ (0, 1]`. The event `u = 0` has probability zero, so the law is unaffected. -/
theorem step_zero {P : Fin n → Fin n → ℝ} (hP : ∀ i j, 0 ≤ P i j) (i : Fin n) :
    (step P i 0 : ℕ) = 0 := by
  have h0 : (⟨0, by have := i.isLt; omega⟩ : Fin n) ∈
      insert (lastState i) (univ.filter fun j : Fin n ↦ (0 : ℝ) ≤ cumProb P i (j + 1)) := by
    refine Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩)
    rw [← cumProb_zero P i]
    exact cumProb_mono hP i (Nat.zero_le _)
  have hle : step P i 0 ≤ ⟨0, by have := i.isLt; omega⟩ := Finset.min'_le _ _ h0
  rw [Fin.le_def] at hle
  exact Nat.le_zero.1 hle

/-- The inverse-CDF update is measurable in the uniform. -/
theorem measurable_step (P : Fin n → Fin n → ℝ) (i : Fin n) : Measurable (step P i) := by
  refine measurable_to_countable' fun j ↦ ?_
  refine Set.OrdConnected.measurableSet ⟨fun a ha b hb x hx ↦ ?_⟩
  have ha' : step P i a = j := ha
  have hb' : step P i b = j := hb
  change step P i x = j
  exact le_antisymm (hb' ▸ step_mono P i hx.2) (ha' ▸ step_mono P i hx.1)

/-- The preimage of `j` within `(0, 1]` is post #3's interval `(cs_{i,j-1}, cs_{ij}]`. -/
theorem step_preimage_inter_Ioc {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i j : Fin n) :
    {u | step P i u = j} ∩ Set.Ioc 0 1 = Set.Ioc (cumProb P i j) (cumProb P i (j + 1)) := by
  ext u
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioc]
  constructor
  · rintro ⟨h, hu⟩
    exact (step_eq_iff hP i j hu).1 h
  · rintro ⟨h1, h2⟩
    have hu : u ∈ Set.Ioc (0 : ℝ) 1 :=
      ⟨lt_of_le_of_lt (cumProb_mem_Icc hP i j).1 h1, h2.trans (cumProb_mem_Icc hP i _).2⟩
    exact ⟨(step_eq_iff hP i j hu).2 ⟨h1, h2⟩, hu⟩

/-- **Key fact** (post #3): "the probability that [the uniform] falls in the interval
`(cs_{2,j-1}, cs_{2j}]` is exactly `p_{2j}`": `U[0,1){u : step P i u = j} = P i j`. -/
theorem uniformIco_step_eq {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i j : Fin n) :
    uniformIco {u | step P i u = j} = ENNReal.ofReal (P i j) := by
  rw [uniformIco_eq_restrict_Ioc, Measure.restrict_apply' measurableSet_Ioc,
    step_preimage_inter_Ioc hP, Real.volume_Ioc, cumProb_succ, add_sub_cancel_left]

/-- **Key fact**, Lebesgue form: `volume {u ∈ [0,1) : step P i u = j} = P i j`. -/
theorem volume_step_eq {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i j : Fin n) :
    volume ({u | step P i u = j} ∩ Set.Ico 0 1) = ENNReal.ofReal (P i j) := by
  rw [← uniformIco_step_eq hP i j, Measure.restrict_apply' measurableSet_Ico]

/-- **Post #3's worked example**: with `n = 3` and row `[0.2, 0.6, 0.2]` from the second state
(`1 : Fin 3`), the draw `u = 0.79` sends the chain to the second state, "because this is above
0.2 and below 0.8"; draws in `(0, 0.2]` go to the first state and draws in `(0.8, 1]` to the
third. -/
theorem step_post3_example {P : Fin 3 → Fin 3 → ℝ} (hP : IsStochastic P) (h0 : P 1 0 = 0.2)
    (h1 : P 1 1 = 0.6) (h2 : P 1 2 = 0.2) :
    step P 1 0.79 = 1 ∧ (∀ u ∈ Set.Ioc (0 : ℝ) 0.2, step P 1 u = 0) ∧
      (∀ u ∈ Set.Ioc (0.8 : ℝ) 1, step P 1 u = 2) := by
  have c0 : cumProb P 1 0 = 0 := cumProb_zero P 1
  have c1 : cumProb P 1 1 = 0.2 := by
    have : cumProb P 1 1 = cumProb P 1 0 + P 1 0 := cumProb_succ P 1 0
    change cumProb P 1 1 = 0.2
    rw [this, c0, h0, zero_add]
  have c2 : cumProb P 1 2 = 0.8 := by
    have : cumProb P 1 2 = cumProb P 1 1 + P 1 1 := cumProb_succ P 1 1
    change cumProb P 1 2 = 0.8
    rw [this, c1, h1]
    norm_num
  have c3 : cumProb P 1 3 = 1 := by
    have : cumProb P 1 3 = cumProb P 1 2 + P 1 2 := cumProb_succ P 1 2
    change cumProb P 1 3 = 1
    rw [this, c2, h2]
    norm_num
  refine ⟨?_, fun u hu ↦ ?_, fun u hu ↦ ?_⟩
  · rw [step_eq_iff hP 1 1 ⟨by norm_num, by norm_num⟩]
    change cumProb P 1 1 < 0.79 ∧ 0.79 ≤ cumProb P 1 (1 + 1)
    rw [c1, c2]
    norm_num
  · rw [step_eq_iff hP 1 0 ⟨hu.1, hu.2.trans (by norm_num)⟩]
    change cumProb P 1 0 < u ∧ u ≤ cumProb P 1 (0 + 1)
    rw [c0, c1]
    exact hu
  · rw [step_eq_iff hP 1 2 ⟨lt_trans (by norm_num) hu.1, hu.2⟩]
    change cumProb P 1 2 < u ∧ u ≤ cumProb P 1 (2 + 1)
    rw [c2, c3]
    exact hu

/-! ### Paths driven by a sequence -/

variable {S : Type*}

/-- The path driven by a sequence `u` through an update rule `G` (post #3, "this sequence of
uniform random numbers 'driving' the Markov chain"): `x 0 = x₀`, `x (t+1) = G (x t) (u t)`. So
`u t` drives the transition from time `t` to `t + 1` (post #3's `u^t`, `x^{t+1}`, shifted to
start at `0`). -/
def drive {α : Type*} (G : S → α → S) (x₀ : S) (u : ℕ → α) : ℕ → S
  | 0 => x₀
  | t + 1 => G (drive G x₀ u t) (u t)

/-- The path driven by `u` from `x₀` with the inverse-CDF update `step P` (post #3's MC/QMC
simulation of the chain, depending on what `u` is). -/
noncomputable abbrev drivenPath (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (u : ℕ → ℝ) : ℕ → Fin n :=
  drive (step P) x₀ u

/-- `drive` starts at `x₀`. -/
theorem drive_zero {α : Type*} (G : S → α → S) (x₀ : S) (u : ℕ → α) : drive G x₀ u 0 = x₀ :=
  rfl

/-- The recursion of `drive`. -/
theorem drive_succ {α : Type*} (G : S → α → S) (x₀ : S) (u : ℕ → α) (t : ℕ) :
    drive G x₀ u (t + 1) = G (drive G x₀ u t) (u t) :=
  rfl

/-- **Pathwise description of `drive`**: the driven path equals `s` at times `0, …, T` iff
`s 0 = x₀` and every transition `s t → s (t+1)`, `t < T`, is the update of `s t` by `u t`. -/
theorem drive_eq_iff {α : Type*} (G : S → α → S) (x₀ : S) (u : ℕ → α) (s : ℕ → S) (T : ℕ) :
    (∀ t ≤ T, drive G x₀ u t = s t) ↔ s 0 = x₀ ∧ ∀ t < T, G (s t) (u t) = s (t + 1) := by
  induction T with
  | zero =>
    constructor
    · intro h
      exact ⟨(h 0 le_rfl).symm, fun t ht ↦ absurd ht (Nat.not_lt_zero t)⟩
    · rintro ⟨h0, -⟩ t ht
      rw [Nat.le_zero.1 ht]
      exact h0.symm
  | succ T ih =>
    constructor
    · intro h
      have hT := ih.1 fun t ht ↦ h t (ht.trans (Nat.le_succ T))
      refine ⟨hT.1, fun t ht ↦ ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | ht
      · exact hT.2 t ht
      · rw [ht, ← h T (Nat.le_succ T), ← h (T + 1) le_rfl, drive_succ]
    · rintro ⟨h0, hs⟩ t ht
      have hT := ih.2 ⟨h0, fun t ht ↦ hs t (ht.trans (Nat.lt_succ_self T))⟩
      rcases Nat.le_succ_iff.1 ht with ht | ht
      · exact hT t ht
      · rw [ht, drive_succ, hT T le_rfl, hs T (Nat.lt_succ_self T)]

/-! ### Counts -/

variable [DecidableEq S]

/-- **Occupation count** (the visit counter): `occCount path i T = #{t < T : path t = i}`, the
number of visits to `i` strictly before time `T` (times `0, …, T - 1`). -/
def occCount (path : ℕ → S) (i : S) (T : ℕ) : ℕ :=
  ((range T).filter fun t ↦ path t = i).card

/-- **Transition count** `transCount path i j T = #{t < T : path t = i ∧ path (t+1) = j}`, the
number of transitions `i → j` among the first `T` transitions (times `0 → 1, …, T-1 → T`). -/
def transCount (path : ℕ → S) (i j : S) (T : ℕ) : ℕ :=
  ((range T).filter fun t ↦ path t = i ∧ path (t + 1) = j).card

/-- No visits before time `0`. -/
theorem occCount_zero (path : ℕ → S) (i : S) : occCount path i 0 = 0 := rfl

/-- No transitions before time `0`. -/
theorem transCount_zero (path : ℕ → S) (i j : S) : transCount path i j 0 = 0 := rfl

/-- One more period adds one visit iff the path is in `i` at time `T`. -/
theorem occCount_succ (path : ℕ → S) (i : S) (T : ℕ) :
    occCount path i (T + 1) = occCount path i T + if path T = i then 1 else 0 := by
  unfold occCount
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : path T = i
  · simp only [h, ↓reduceIte]
    rw [Finset.card_insert_of_notMem]
    intro hT
    exact lt_irrefl T (Finset.mem_range.1 (Finset.mem_filter.1 hT).1)
  · simp only [h, ↓reduceIte, add_zero]

/-- One more transition adds one to `transCount i j` iff it is `i → j`. -/
theorem transCount_succ (path : ℕ → S) (i j : S) (T : ℕ) :
    transCount path i j (T + 1) =
      transCount path i j T + if path T = i ∧ path (T + 1) = j then 1 else 0 := by
  unfold transCount
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : path T = i ∧ path (T + 1) = j
  · simp only [h, and_self, ↓reduceIte]
    rw [Finset.card_insert_of_notMem]
    intro hT
    exact lt_irrefl T (Finset.mem_range.1 (Finset.mem_filter.1 hT).1)
  · simp only [h, ↓reduceIte, add_zero]

/-- At most `T` visits before time `T`. -/
theorem occCount_le (path : ℕ → S) (i : S) (T : ℕ) : occCount path i T ≤ T :=
  (Finset.card_filter_le _ _).trans (Finset.card_range T).le

/-- The occupation count is monotone in the horizon. -/
theorem occCount_mono (path : ℕ → S) (i : S) {T T' : ℕ} (h : T ≤ T') :
    occCount path i T ≤ occCount path i T' :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.2 h))

/-- `transCount i j ≤ occCount i`. -/
theorem transCount_le_occCount (path : ℕ → S) (i j : S) (T : ℕ) :
    transCount path i j T ≤ occCount path i T :=
  Finset.card_le_card fun t ht ↦ by
    rw [Finset.mem_filter] at ht ⊢
    exact ⟨ht.1, ht.2.1⟩

/-- The occupation count before `T` depends only on the path before `T`. -/
theorem occCount_congr {p q : ℕ → S} {T : ℕ} (h : ∀ t < T, p t = q t) (i : S) :
    occCount p i T = occCount q i T := by
  unfold occCount
  rw [Finset.filter_congr fun t ht ↦ by rw [h t (Finset.mem_range.1 ht)]]

/-- The first `T` transition counts depend only on the path up to time `T`. -/
theorem transCount_congr {p q : ℕ → S} {T : ℕ} (h : ∀ t ≤ T, p t = q t) (i j : S) :
    transCount p i j T = transCount q i j T := by
  unfold transCount
  refine congrArg _ (Finset.filter_congr fun t ht ↦ ?_)
  have ht' := Finset.mem_range.1 ht
  rw [h t ht'.le, h (t + 1) ht']

/-- Splitting the horizon: visits before `a + b` are those before `a` plus those of the shifted
path `t ↦ path (a + t)` before `b`. -/
theorem occCount_add (path : ℕ → S) (i : S) (a b : ℕ) :
    occCount path i (a + b) = occCount path i a + occCount (fun t ↦ path (a + t)) i b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [← add_assoc, occCount_succ, ih, occCount_succ, add_assoc]

/-- Splitting the horizon for transition counts. -/
theorem transCount_add (path : ℕ → S) (i j : S) (a b : ℕ) :
    transCount path i j (a + b) =
      transCount path i j a + transCount (fun t ↦ path (a + t)) i j b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [← add_assoc, transCount_succ, ih, transCount_succ, add_assoc]
    rfl

/-! ### Per-state stacks -/

/-- The **departure index** at time `t`: the number of earlier visits to the current state,
`#{t' < t : path t' = path t}`. The departure from `path t` at time `t` is the
`departureIndex`-th departure (counting from `0`) from that state. -/
def departureIndex (path : ℕ → S) (t : ℕ) : ℕ := occCount path (path t) t

/-- The departure index at time `t` depends only on the path up to time `t`. -/
theorem departureIndex_congr {p q : ℕ → S} {t : ℕ} (h : ∀ t' ≤ t, p t' = q t') :
    departureIndex p t = departureIndex q t := by
  unfold departureIndex
  rw [h t le_rfl]
  exact occCount_congr (fun t' ht' ↦ h t' ht'.le) _

/-- Later visits to the same state have larger departure indices; so the pairs
`(path t, departureIndex path t)` are distinct for distinct `t`. -/
theorem departureIndex_lt {path : ℕ → S} {t t' : ℕ} (htt' : t < t') (h : path t = path t') :
    departureIndex path t < departureIndex path t' := by
  unfold departureIndex
  rw [← h]
  have h1 := occCount_succ path (path t) t
  simp only [eq_self, ↓reduceIte] at h1
  have h2 := occCount_mono path (path t) (show t + 1 ≤ t' from htt')
  omega

/-- Injectivity of `t ↦ (path t, departureIndex path t)`. -/
theorem departureIndex_injective (path : ℕ → S) :
    Function.Injective fun t ↦ (path t, departureIndex path t) := by
  intro t t' h
  simp only [Prod.mk.injEq] at h
  rcases lt_trichotomy t t' with htt' | htt' | htt'
  · exact absurd h.2 (departureIndex_lt htt' h.1).ne
  · exact htt'
  · exact absurd h.2 (departureIndex_lt htt' h.1.symm).ne'

/-- The state and the per-state departure counters of the stack representation. -/
def stackState {α : Type*} (G : S → α → S) (x₀ : S) (v : S → ℕ → α) : ℕ → S × (S → ℕ)
  | 0 => (x₀, fun _ ↦ 0)
  | t + 1 =>
    let p := stackState G x₀ v t
    (G p.1 (v p.1 (p.2 p.1)), Function.update p.2 p.1 (p.2 p.1 + 1))

/-- **The stack representation** (post #3, "each state has its own stack … the `k`-th visit to
state `i` uses point `k` of stack `i`"): each state `i` has its own sequence `v i`, and the
`k`-th departure from `i` (`k = 0, 1, …`) is driven by `v i k` through the update `G`. -/
def stackDrive {α : Type*} (G : S → α → S) (x₀ : S) (v : S → ℕ → α) (t : ℕ) : S :=
  (stackState G x₀ v t).1

/-- The stack-driven chain with the inverse-CDF update. -/
noncomputable abbrev stackPath (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (v : Fin n → ℕ → ℝ) :
    ℕ → Fin n :=
  stackDrive (step P) x₀ v

/-- The counters of `stackState` are the visit counts of the stack path. -/
theorem stackState_snd {α : Type*} (G : S → α → S) (x₀ : S) (v : S → ℕ → α) (t : ℕ) (i : S) :
    (stackState G x₀ v t).2 i = occCount (stackDrive G x₀ v) i t := by
  induction t generalizing i with
  | zero => rfl
  | succ t ih =>
    rw [occCount_succ, ← ih]
    change Function.update (stackState G x₀ v t).2 (stackState G x₀ v t).1
      ((stackState G x₀ v t).2 (stackState G x₀ v t).1 + 1) i = _
    unfold stackDrive
    by_cases h : (stackState G x₀ v t).1 = i
    · subst h
      rw [Function.update_self]
      simp only [eq_self, ↓reduceIte]
    · rw [Function.update_of_ne (Ne.symm h)]
      simp only [h, ↓reduceIte, add_zero]

/-- `stackDrive` starts at `x₀`. -/
theorem stackDrive_zero {α : Type*} (G : S → α → S) (x₀ : S) (v : S → ℕ → α) :
    stackDrive G x₀ v 0 = x₀ :=
  rfl

/-- **The stack recursion**: the transition at time `t` uses entry `departureIndex t` of the
stack of the current state. -/
theorem stackDrive_succ {α : Type*} (G : S → α → S) (x₀ : S) (v : S → ℕ → α) (t : ℕ) :
    stackDrive G x₀ v (t + 1) = G (stackDrive G x₀ v t)
      (v (stackDrive G x₀ v t) (departureIndex (stackDrive G x₀ v) t)) := by
  unfold departureIndex
  rw [← stackState_snd]
  rfl

/-- **Pathwise description of the stack representation**: the stack path equals `s` at times
`0, …, T` iff `s 0 = x₀` and each transition `s t → s (t+1)`, `t < T`, is the update of `s t`
by entry `departureIndex s t` of stack `s t`. -/
theorem stackDrive_eq_iff {α : Type*} (G : S → α → S) (x₀ : S) (v : S → ℕ → α) (s : ℕ → S)
    (T : ℕ) : (∀ t ≤ T, stackDrive G x₀ v t = s t) ↔
      s 0 = x₀ ∧ ∀ t < T, G (s t) (v (s t) (departureIndex s t)) = s (t + 1) := by
  induction T with
  | zero =>
    constructor
    · intro h
      exact ⟨(h 0 le_rfl).symm, fun t ht ↦ absurd ht (Nat.not_lt_zero t)⟩
    · rintro ⟨h0, -⟩ t ht
      rw [Nat.le_zero.1 ht]
      exact h0.symm
  | succ T ih =>
    constructor
    · intro h
      have hT := ih.1 fun t ht ↦ h t (ht.trans (Nat.le_succ T))
      refine ⟨hT.1, fun t ht ↦ ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | ht
      · exact hT.2 t ht
      · rw [ht, ← h T (Nat.le_succ T), ← h (T + 1) le_rfl, stackDrive_succ,
          departureIndex_congr fun t' ht' ↦ h t' (ht'.trans (Nat.le_succ T))]
    · rintro ⟨h0, hs⟩ t ht
      have hT := ih.2 ⟨h0, fun t ht ↦ hs t (ht.trans (Nat.lt_succ_self T))⟩
      rcases Nat.le_succ_iff.1 ht with ht | ht
      · exact hT t ht
      · rw [ht, stackDrive_succ, hT T le_rfl, departureIndex_congr hT,
          hs T (Nat.lt_succ_self T)]

/-! ### Spells -/

/-- A **spell** (maximal run of equal states) starts at time `t` iff `t = 0` or the state
changes at `t`. -/
abbrev IsSpellStart (path : ℕ → S) (t : ℕ) : Prop := t = 0 ∨ path (t - 1) ≠ path t

/-- The **length of the run starting at `t`**, censored at the horizon `T`: the number of
`k < T - t` such that the path stays in `path t` throughout times `t, …, t + k`. For a spell
start `t`, this is the length of that spell (or of its part before `T`). -/
def runLength (path : ℕ → S) (t T : ℕ) : ℕ :=
  ((range (T - t)).filter fun k ↦ ∀ m ≤ k, path (t + m) = path t).card

/-- The number of spells in state `i` that start before `T`. -/
def spellCount (path : ℕ → S) (i : S) (T : ℕ) : ℕ :=
  ((range T).filter fun t ↦ IsSpellStart path t ∧ path t = i).card

/-- A run that stays exactly `k` periods and then leaves, before the horizon, has length `k`. -/
theorem runLength_eq_of_exit {path : ℕ → S} {t T k : ℕ} (hk : t + k < T)
    (hstay : ∀ m < k, path (t + m) = path t) (hexit : path (t + k) ≠ path t) :
    runLength path t T = k := by
  unfold runLength
  have : (range (T - t)).filter (fun k ↦ ∀ m ≤ k, path (t + m) = path t) = range k := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨-, hm⟩
      by_contra hmk
      exact hexit (hm k (not_lt.1 hmk))
    · intro hmk
      exact ⟨by omega, fun m' hm' ↦ hstay m' (lt_of_le_of_lt hm' hmk)⟩
  rw [this, Finset.card_range]

/-- **Run lengths**: for `t + k < T`, the run starting at `t` has length `k` iff the path stays
in `path t` for times `t, …, t + k - 1` and leaves at `t + k`. -/
theorem runLength_eq_iff {path : ℕ → S} {t T k : ℕ} (hk : t + k < T) :
    runLength path t T = k ↔
      (∀ m < k, path (t + m) = path t) ∧ path (t + k) ≠ path t := by
  constructor
  · intro h
    by_cases hall : ∀ m ≤ k, path (t + m) = path t
    · exfalso
      have hsub : range (k + 1) ⊆
          (range (T - t)).filter (fun k ↦ ∀ m ≤ k, path (t + m) = path t) := by
        intro m hm
        rw [Finset.mem_range] at hm
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, fun m' hm' ↦ hall m' (by omega)⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_range] at this
      unfold runLength at h
      omega
    · have hex : ∃ m, m ≤ k ∧ path (t + m) ≠ path t := by
        by_contra hne
        exact hall fun m hm ↦ by
          by_contra hm'
          exact hne ⟨m, hm, hm'⟩
      classical
      let m0 := Nat.find hex
      have hm0 : m0 ≤ k ∧ path (t + m0) ≠ path t := Nat.find_spec hex
      have hstay : ∀ m < m0, path (t + m) = path t := fun m hm ↦ by
        by_contra hne
        exact Nat.find_min hex hm ⟨by omega, hne⟩
      have := runLength_eq_of_exit (show t + m0 < T by omega) hstay hm0.2
      rw [h] at this
      rw [this]
      exact ⟨hstay, hm0.2⟩
  · rintro ⟨hstay, hexit⟩
    exact runLength_eq_of_exit hk hstay hexit

/-- One more period adds one spell of `i` iff a spell of `i` starts at time `T`. -/
theorem spellCount_succ (path : ℕ → S) (i : S) (T : ℕ) :
    spellCount path i (T + 1) =
      spellCount path i T + if IsSpellStart path T ∧ path T = i then 1 else 0 := by
  unfold spellCount
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : IsSpellStart path T ∧ path T = i
  · simp only [h, and_self, ↓reduceIte]
    rw [Finset.card_insert_of_notMem]
    intro hT
    exact lt_irrefl T (Finset.mem_range.1 (Finset.mem_filter.1 hT).1)
  · simp only [h, ↓reduceIte, add_zero]

variable [Fintype S]

/-- The occupation counts before `T` add up to `T`. -/
theorem sum_occCount (path : ℕ → S) (T : ℕ) : ∑ i, occCount path i T = T := by
  induction T with
  | zero => exact Finset.sum_const_zero
  | succ T ih =>
    simp only [occCount_succ]
    rw [Finset.sum_add_distrib, ih, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ↓reduceIte]

/-- **Departures**: `Σ_j transCount i j T = occCount i T` (each visit before `T` is followed by
exactly one transition among the first `T`). -/
theorem sum_transCount_right (path : ℕ → S) (i : S) (T : ℕ) :
    ∑ j, transCount path i j T = occCount path i T := by
  unfold transCount occCount
  rw [Finset.card_eq_sum_card_fiberwise (f := fun t ↦ path (t + 1)) (t := univ)
    (fun _ _ ↦ Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.filter_filter]

/-- **Arrivals**: `Σ_j transCount j i T + 1{path 0 = i} = occCount i T + 1{path T = i}`. -/
theorem sum_transCount_left (path : ℕ → S) (i : S) (T : ℕ) :
    ∑ j, transCount path j i T + (if path 0 = i then 1 else 0) =
      occCount path i T + if path T = i then 1 else 0 := by
  induction T with
  | zero => rw [Finset.sum_eq_zero fun j _ ↦ transCount_zero path j i, occCount_zero]
  | succ T ih =>
    simp only [transCount_succ]
    rw [Finset.sum_add_distrib, occCount_succ]
    have h1 : ∑ j, (if path T = j ∧ path (T + 1) = i then 1 else 0) =
        if path (T + 1) = i then 1 else 0 := by
      simp only [ite_and]
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_univ, ↓reduceIte]
    rw [h1]
    omega

/-- **Flow balance** (post #3, "every state is entered as often as it is left (allowing for
the first and last states)"): out-count minus in-count is `1{path 0 = i} − 1{path T = i}`. -/
theorem flowBalance (path : ℕ → S) (i : S) (T : ℕ) :
    (∑ j, transCount path i j T : ℤ) - ∑ j, transCount path j i T =
      (if path 0 = i then 1 else 0) - if path T = i then 1 else 0 := by
  have h1 := sum_transCount_right path i T
  have h2 := sum_transCount_left path i T
  have h1' : (∑ j, transCount path i j T : ℤ) = occCount path i T := by exact_mod_cast h1
  have h2' : (∑ j, transCount path j i T : ℤ) + (if path 0 = i then 1 else 0) =
      occCount path i T + if path T = i then 1 else 0 := by
    have := congrArg (fun m : ℕ ↦ (m : ℤ)) h2
    push_cast [apply_ite (fun m : ℕ ↦ (m : ℤ))] at this
    exact this
  push_cast
  linarith

/-- **Flow balance**, bound form: `|Σ_j transCount i j − Σ_j transCount j i| ≤ 1`. -/
theorem abs_flowBalance_le (path : ℕ → S) (i : S) (T : ℕ) :
    |(∑ j, transCount path i j T : ℤ) - ∑ j, transCount path j i T| ≤ 1 := by
  rw [flowBalance]
  split_ifs <;> norm_num

/-- All transition counts add up to the number of transitions `T`. -/
theorem sum_sum_transCount (path : ℕ → S) (T : ℕ) : ∑ i, ∑ j, transCount path i j T = T := by
  simp only [sum_transCount_right]
  exact sum_occCount path T

/-- **Spells are entries**: the spells of `i` starting at times `0, …, T` are the start (if
`path 0 = i`) plus the entries `j → i`, `j ≠ i`, among the first `T` transitions. -/
theorem spellCount_succ_eq (path : ℕ → S) (i : S) (T : ℕ) :
    spellCount path i (T + 1) =
      (if path 0 = i then 1 else 0) + ∑ j ∈ univ.erase i, transCount path j i T := by
  induction T with
  | zero =>
    rw [spellCount_succ, Finset.sum_eq_zero fun j _ ↦ transCount_zero path j i]
    have h0 : IsSpellStart path 0 := Or.inl rfl
    simp only [h0, true_and]
    change 0 + _ = _ + 0
    rw [zero_add, add_zero]
  | succ T ih =>
    rw [spellCount_succ, ih]
    simp only [transCount_succ]
    rw [Finset.sum_add_distrib]
    have h1 : ∑ j ∈ univ.erase i, (if path T = j ∧ path (T + 1) = i then 1 else 0) =
        if path T ≠ i ∧ path (T + 1) = i then 1 else 0 := by
      simp only [ite_and]
      rw [Finset.sum_ite_eq]
      by_cases h : path T = i
      · simp only [h, Finset.mem_erase, ne_eq, not_true_eq_false, false_and, ↓reduceIte]
      · simp only [h, Finset.mem_erase, ne_eq, not_false_eq_true, Finset.mem_univ, and_self,
          ↓reduceIte]
    rw [h1]
    have h2 : (IsSpellStart path (T + 1) ∧ path (T + 1) = i) ↔
        (path T ≠ i ∧ path (T + 1) = i) := by
      unfold IsSpellStart
      rw [Nat.add_sub_cancel]
      constructor
      · rintro ⟨h | h, hi⟩
        · exact absurd h (Nat.succ_ne_zero T)
        · exact ⟨hi ▸ h, hi⟩
      · rintro ⟨h, hi⟩
        exact ⟨Or.inr (hi ▸ h), hi⟩
    rw [if_congr h2 rfl rfl]
    omega

end RQMCMarkov.MarkovDriving

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# I.i.d. uniform driving gives the Markov chain, for one sequence and for stacks (post #3)

Post #3: with the inverse-CDF update, "because `u¹` is uniform, the probability that it falls in
the interval … is exactly … `p_{2j}`, so `x²` has the correct conditional distribution. We then
repeat … with a new independent draw". Reading: under the i.i.d. product `iidUniform ℕ`
(Mathlib's `Measure.infinitePi` of `uniformIco`), the finite-dimensional laws of `drivenPath P x₀`
are those of the Markov chain with matrix `P` started at `x₀`:
`P(x_0 = s_0, …, x_T = s_T) = 1{s_0 = x₀} ∏_{t<T} P s_t s_{t+1}`. The same holds for the stack
representation with all stack entries i.i.d. uniform, so both representations of MC have the
same path law. (Identification with Mathlib's `Kernel.traj` is not done: the finite-dimensional
formula is what the later modules use.)

## Main results

* `iidUniform ι`, `isProbabilityMeasure_iidUniform`: the i.i.d. `U[0,1)` measure on `ι → ℝ`.
* `infinitePi_setOf_forall_mem`, `measurableSet_setOf_forall_mem`: an i.i.d. product gives
  `∏_{t<T} ν (B t)` to `{w : w (c t) ∈ B t, t < T}` when the coordinates `c t` are distinct.
* `infinitePi_drive_cylinder`, `infinitePi_stackDrive_cylinder`: for any update rule `G` and
  i.i.d. inputs with law `ν`, both the driven path and the stack path have the cylinder
  probabilities `1{s_0 = x₀} ∏_{t<T} ν{r : G s_t r = s_{t+1}}`.
* `pathProb P x₀ s T = 1{s 0 = x₀} ∏_{t<T} P (s t) (s (t+1))`, `pathProb_nonneg`,
  `pathProb_succ`.
* `iidUniform_drivenPath_cylinder`, `iidUniform_stackPath_cylinder` (post #3, "inverse-CDF
  with i.i.d. uniforms gives the right chain"): both cylinder probabilities equal `pathProb`.
* `map_drivenPath_singleton`, `map_stackPath_singleton`, `map_drivenPath_eq_map_stackPath`:
  the laws of `(x_0, …, x_T)` under the two representations agree.
-/

namespace RQMCMarkov.MarkovDriving

open MeasureTheory Finset

/-- **The i.i.d. `U[0,1)` driving measure** on `ι → ℝ`: the product (Mathlib's
`Measure.infinitePi`) of copies of `uniformIco`. With `ι = ℕ` it drives `drivenPath` (MC of the
chain); with `ι = Fin n × ℕ` it gives independent i.i.d. stacks for `stackPath` (through
`Function.curry`). -/
noncomputable def iidUniform (ι : Type*) : Measure (ι → ℝ) :=
  haveI := isProbabilityMeasure_uniformIco
  Measure.infinitePi fun _ : ι ↦ uniformIco

/-- `iidUniform ι` is a probability measure. -/
theorem isProbabilityMeasure_iidUniform (ι : Type*) : IsProbabilityMeasure (iidUniform ι) := by
  have := isProbabilityMeasure_uniformIco
  unfold iidUniform
  infer_instance

/-- **Cylinder sets of an i.i.d. product**: for an injective choice `c` of coordinates,
`P(w (c t) ∈ B t for all t < T) = ∏_{t < T} ν (B t)`. -/
theorem infinitePi_setOf_forall_mem {ι α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {c : ℕ → ι} (hc : Function.Injective c) {B : ℕ → Set α}
    (hB : ∀ t, MeasurableSet (B t)) (T : ℕ) :
    Measure.infinitePi (fun _ : ι ↦ ν) {w | ∀ t < T, w (c t) ∈ B t} = ∏ t ∈ range T, ν (B t) := by
  classical
  set B' : ι → Set α := fun p ↦ {a | ∀ t < T, c t = p → a ∈ B t} with hB'def
  have hset : {w : ι → α | ∀ t < T, w (c t) ∈ B t} = Set.pi ↑((range T).image c) B' := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Finset.coe_image, Set.mem_image,
      Finset.mem_coe, Finset.mem_range, hB'def]
    constructor
    · rintro h p ⟨t', ht', rfl⟩ t ht hct
      rw [← hc hct] at ht' ⊢
      exact h t ht
    · intro h t ht
      exact h (c t) ⟨t, ht, rfl⟩ t ht rfl
  have hB'c : ∀ t < T, B' (c t) = B t := by
    intro t ht
    ext a
    simp only [hB'def, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact h t ht rfl
    · intro h t' _ hct
      rw [hc hct]
      exact h
  have hmeas : ∀ p, MeasurableSet (B' p) := by
    intro p
    have : B' p = ⋂ (t : ℕ) (_ : t < T) (_ : c t = p), B t := by
      ext a
      simp only [hB'def, Set.mem_ofPred_eq, Set.mem_iInter]
    rw [this]
    exact MeasurableSet.iInter fun t ↦ .iInter fun _ ↦ .iInter fun _ ↦ hB t
  rw [hset, Measure.infinitePi_pi (fun _ : ι ↦ ν) fun p _ ↦ hmeas p,
    Finset.prod_image fun a _ b _ h ↦ hc h]
  exact Finset.prod_congr rfl fun t ht ↦ by rw [hB'c t (Finset.mem_range.1 ht)]

/-- Cylinder sets are measurable. -/
theorem measurableSet_setOf_forall_mem {ι α : Type*} [MeasurableSpace α] (c : ℕ → ι)
    {B : ℕ → Set α} (hB : ∀ t, MeasurableSet (B t)) (T : ℕ) :
    MeasurableSet {w : ι → α | ∀ t < T, w (c t) ∈ B t} := by
  have : {w : ι → α | ∀ t < T, w (c t) ∈ B t} =
      ⋂ (t : ℕ) (_ : t < T), (fun w : ι → α ↦ w (c t)) ⁻¹' B t := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  exact MeasurableSet.iInter fun t ↦ .iInter fun _ ↦ measurable_pi_apply (c t) (hB t)

variable {S : Type*}

/-- The driven path matches `s` up to `T` iff `s` starts at `x₀` and the uniforms produce the
transitions of `s` (set form of `drive_eq_iff`). -/
theorem setOf_drive_eq {α : Type*} (G : S → α → S) (x₀ : S) (s : ℕ → S) (T : ℕ) :
    {u : ℕ → α | ∀ t ≤ T, drive G x₀ u t = s t} =
      {u | s 0 = x₀ ∧ ∀ t < T, u (id t) ∈ {r | G (s t) r = s (t + 1)}} := by
  ext u
  exact drive_eq_iff G x₀ u s T

/-- The cylinder events of a driven path are measurable. -/
theorem measurableSet_drive_cylinder {α : Type*} [MeasurableSpace α] (G : S → α → S)
    (hG : ∀ x y, MeasurableSet {r | G x r = y}) (x₀ : S) (s : ℕ → S) (T : ℕ) :
    MeasurableSet {u : ℕ → α | ∀ t ≤ T, drive G x₀ u t = s t} := by
  rw [setOf_drive_eq]
  by_cases h0 : s 0 = x₀
  · simp only [h0, true_and]
    exact measurableSet_setOf_forall_mem id (fun t ↦ hG (s t) (s (t + 1))) T
  · simp only [h0, false_and, Set.ofPred_false, MeasurableSet.empty]

variable [DecidableEq S]

/-- **I.i.d. driving gives the Markov chain** (post #3, generic update): driven by i.i.d.
draws with law `ν`, `P(x₀ = s₀, …, x_T = s_T) = 1{s₀ = x₀} ∏_{t<T} ν{r : G s_t r = s_{t+1}}`. -/
theorem infinitePi_drive_cylinder {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (G : S → α → S) (hG : ∀ x y, MeasurableSet {r | G x r = y})
    (x₀ : S) (s : ℕ → S) (T : ℕ) :
    Measure.infinitePi (fun _ : ℕ ↦ ν) {u | ∀ t ≤ T, drive G x₀ u t = s t} =
      if s 0 = x₀ then ∏ t ∈ range T, ν {r | G (s t) r = s (t + 1)} else 0 := by
  rw [setOf_drive_eq]
  by_cases h0 : s 0 = x₀
  · simp only [h0, true_and, ↓reduceIte]
    exact infinitePi_setOf_forall_mem ν Function.injective_id (fun t ↦ hG (s t) (s (t + 1))) T
  · simp only [h0, false_and, Set.ofPred_false, measure_empty, ↓reduceIte]

/-- The stack path matches `s` up to `T` iff `s` starts at `x₀` and the stack entries
`w (s t, departureIndex s t)` produce the transitions of `s`. -/
theorem setOf_stackDrive_eq {α : Type*} (G : S → α → S) (x₀ : S) (s : ℕ → S) (T : ℕ) :
    {w : S × ℕ → α | ∀ t ≤ T, stackDrive G x₀ (Function.curry w) t = s t} =
      {w | s 0 = x₀ ∧ ∀ t < T, w ((fun t ↦ (s t, departureIndex s t)) t) ∈
        {r | G (s t) r = s (t + 1)}} := by
  ext w
  exact stackDrive_eq_iff G x₀ (Function.curry w) s T

/-- The cylinder events of a stack path are measurable. -/
theorem measurableSet_stackDrive_cylinder {α : Type*} [MeasurableSpace α] (G : S → α → S)
    (hG : ∀ x y, MeasurableSet {r | G x r = y}) (x₀ : S) (s : ℕ → S) (T : ℕ) :
    MeasurableSet {w : S × ℕ → α | ∀ t ≤ T, stackDrive G x₀ (Function.curry w) t = s t} := by
  rw [setOf_stackDrive_eq]
  by_cases h0 : s 0 = x₀
  · simp only [h0, true_and]
    exact measurableSet_setOf_forall_mem _ (fun t ↦ hG (s t) (s (t + 1))) T
  · simp only [h0, false_and, Set.ofPred_false, MeasurableSet.empty]

/-- **I.i.d. stacks give the Markov chain** (post #3, generic update): with all stack entries
`w (i, k)` i.i.d. with law `ν`, the stack path has the same finite-dimensional laws as the
path driven by one i.i.d. sequence: `1{s₀ = x₀} ∏_{t<T} ν{r : G s_t r = s_{t+1}}`. The point:
on the event that the path is `s`, the entries used are `(s t, departureIndex s t)`, `t < T`,
which are distinct (`departureIndex_injective`). -/
theorem infinitePi_stackDrive_cylinder {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (G : S → α → S) (hG : ∀ x y, MeasurableSet {r | G x r = y})
    (x₀ : S) (s : ℕ → S) (T : ℕ) :
    Measure.infinitePi (fun _ : S × ℕ ↦ ν)
        {w | ∀ t ≤ T, stackDrive G x₀ (Function.curry w) t = s t} =
      if s 0 = x₀ then ∏ t ∈ range T, ν {r | G (s t) r = s (t + 1)} else 0 := by
  rw [setOf_stackDrive_eq]
  by_cases h0 : s 0 = x₀
  · simp only [h0, true_and, ↓reduceIte]
    exact infinitePi_setOf_forall_mem ν (departureIndex_injective s)
      (fun t ↦ hG (s t) (s (t + 1))) T
  · simp only [h0, false_and, Set.ofPred_false, measure_empty, ↓reduceIte]

/-! ### The inverse-CDF update with uniforms -/

/-- The **path probability** of the Markov chain with matrix `P` from `x₀`:
`pathProb P x₀ s T = 1{s 0 = x₀} ∏_{t<T} P (s t) (s (t+1))`. -/
noncomputable def pathProb (P : S → S → ℝ) (x₀ : S) (s : ℕ → S) (T : ℕ) : ℝ :=
  if s 0 = x₀ then ∏ t ∈ range T, P (s t) (s (t + 1)) else 0

/-- Path probabilities are nonnegative. -/
theorem pathProb_nonneg {P : S → S → ℝ} (hP : ∀ i j, 0 ≤ P i j) (x₀ : S)
    (s : ℕ → S) (T : ℕ) : 0 ≤ pathProb P x₀ s T := by
  unfold pathProb
  split_ifs
  · exact Finset.prod_nonneg fun t _ ↦ hP _ _
  · exact le_rfl

/-- The Markov recursion for path probabilities. -/
theorem pathProb_succ (P : S → S → ℝ) (x₀ : S) (s : ℕ → S) (T : ℕ) :
    pathProb P x₀ s (T + 1) = pathProb P x₀ s T * P (s T) (s (T + 1)) := by
  unfold pathProb
  split_ifs
  · rw [Finset.prod_range_succ]
  · rw [zero_mul]

variable {n : ℕ}

/-- The inverse-CDF update has measurable fibres. -/
theorem measurableSet_step_eq (P : Fin n → Fin n → ℝ) (x y : Fin n) :
    MeasurableSet {r | step P x r = y} :=
  measurable_step P x (measurableSet_singleton y)

/-- The `ENNReal` product of the transition probabilities along `s`. -/
theorem prod_uniformIco_step_eq {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (s : ℕ → Fin n)
    (T : ℕ) : ∏ t ∈ range T, uniformIco {r | step P (s t) r = s (t + 1)} =
      ENNReal.ofReal (∏ t ∈ range T, P (s t) (s (t + 1))) := by
  rw [ENNReal.ofReal_prod_of_nonneg fun t _ ↦ hP.nonneg _ _]
  exact Finset.prod_congr rfl fun t _ ↦ uniformIco_step_eq hP _ _

/-- **Inverse-CDF with i.i.d. uniforms gives the right chain** (post #3): under
`iidUniform ℕ`, `P(x₀ = s₀, …, x_T = s_T) = 1{s₀ = x₀} ∏_{t<T} P s_t s_{t+1}` for
`drivenPath P x₀`. -/
theorem iidUniform_drivenPath_cylinder {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ : Fin n) (s : ℕ → Fin n) (T : ℕ) :
    iidUniform ℕ {u | ∀ t ≤ T, drivenPath P x₀ u t = s t} =
      ENNReal.ofReal (pathProb P x₀ s T) := by
  have := isProbabilityMeasure_uniformIco
  unfold iidUniform
  rw [infinitePi_drive_cylinder uniformIco (step P) (measurableSet_step_eq P) x₀ s T]
  unfold pathProb
  split_ifs
  · exact prod_uniformIco_step_eq hP s T
  · exact ENNReal.ofReal_zero.symm

/-- **I.i.d. uniform stacks give the right chain** (post #3): under `iidUniform (Fin n × ℕ)`
(all stack entries i.i.d. `U[0,1)`), `stackPath` has the same finite-dimensional laws,
`1{s₀ = x₀} ∏_{t<T} P s_t s_{t+1}`. -/
theorem iidUniform_stackPath_cylinder {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ : Fin n) (s : ℕ → Fin n) (T : ℕ) :
    iidUniform (Fin n × ℕ) {w | ∀ t ≤ T, stackPath P x₀ (Function.curry w) t = s t} =
      ENNReal.ofReal (pathProb P x₀ s T) := by
  have := isProbabilityMeasure_uniformIco
  unfold iidUniform
  rw [infinitePi_stackDrive_cylinder uniformIco (step P) (measurableSet_step_eq P) x₀ s T]
  unfold pathProb
  split_ifs
  · exact prod_uniformIco_step_eq hP s T
  · exact ENNReal.ofReal_zero.symm

/-! ### The law of the first `T + 1` states -/

omit [DecidableEq S] in
/-- Extend a finite path `s : Fin (T+1) → S` to `ℕ → S` (constant after `T`). -/
def extendPath {T : ℕ} (s : Fin (T + 1) → S) (t : ℕ) : S :=
  s ⟨min t T, Nat.lt_succ_of_le (min_le_right t T)⟩

omit [DecidableEq S] in
/-- A path agrees with `s : Fin (T+1) → S` iff it agrees with `extendPath s` up to `T`. -/
theorem extendPath_eq_iff {T : ℕ} (f : ℕ → S) (s : Fin (T + 1) → S) :
    (fun t : Fin (T + 1) ↦ f t) = s ↔ ∀ t ≤ T, f t = extendPath s t := by
  constructor
  · rintro rfl t ht
    change f t = f (min t T)
    rw [min_eq_left ht]
  · intro h
    funext t
    rw [h t (Nat.lt_succ_iff.1 t.isLt)]
    unfold extendPath
    congr 1
    exact Fin.ext (min_eq_left (Nat.lt_succ_iff.1 t.isLt))

/-- The first `T + 1` states of `drivenPath`, as a random vector. -/
theorem measurable_drivenPath_restrict (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (T : ℕ) :
    Measurable fun u : ℕ → ℝ ↦ fun t : Fin (T + 1) ↦ drivenPath P x₀ u t := by
  refine measurable_to_countable' fun s ↦ ?_
  have : (fun u : ℕ → ℝ ↦ fun t : Fin (T + 1) ↦ drivenPath P x₀ u t) ⁻¹' {s} =
      {u | ∀ t ≤ T, drivenPath P x₀ u t = extendPath s t} := by
    ext u
    exact extendPath_eq_iff _ s
  rw [this]
  exact measurableSet_drive_cylinder _ (measurableSet_step_eq P) x₀ _ T

/-- The first `T + 1` states of `stackPath`, as a random vector. -/
theorem measurable_stackPath_restrict (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (T : ℕ) :
    Measurable fun w : Fin n × ℕ → ℝ ↦
      fun t : Fin (T + 1) ↦ stackPath P x₀ (Function.curry w) t := by
  refine measurable_to_countable' fun s ↦ ?_
  have : (fun w : Fin n × ℕ → ℝ ↦ fun t : Fin (T + 1) ↦ stackPath P x₀ (Function.curry w) t) ⁻¹'
      {s} = {w | ∀ t ≤ T, stackPath P x₀ (Function.curry w) t = extendPath s t} := by
    ext w
    exact extendPath_eq_iff _ s
  rw [this]
  exact measurableSet_stackDrive_cylinder _ (measurableSet_step_eq P) x₀ _ T

/-- **The law of the first `T + 1` states of MC** (post #3): the probability of each finite
path `s` is `1{s₀ = x₀} ∏_{t<T} P s_t s_{t+1}`. -/
theorem map_drivenPath_singleton {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (x₀ : Fin n)
    (T : ℕ) (s : Fin (T + 1) → Fin n) :
    (iidUniform ℕ).map (fun u t ↦ drivenPath P x₀ u (t : Fin (T + 1))) {s} =
      ENNReal.ofReal (pathProb P x₀ (extendPath s) T) := by
  rw [Measure.map_apply (measurable_drivenPath_restrict P x₀ T) (measurableSet_singleton s),
    ← iidUniform_drivenPath_cylinder hP x₀ (extendPath s) T]
  congr 1
  ext u
  exact extendPath_eq_iff _ s

/-- The law of the first `T + 1` states of the stack path. -/
theorem map_stackPath_singleton {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (x₀ : Fin n)
    (T : ℕ) (s : Fin (T + 1) → Fin n) :
    (iidUniform (Fin n × ℕ)).map
        (fun w t ↦ stackPath P x₀ (Function.curry w) (t : Fin (T + 1))) {s} =
      ENNReal.ofReal (pathProb P x₀ (extendPath s) T) := by
  rw [Measure.map_apply (measurable_stackPath_restrict P x₀ T) (measurableSet_singleton s),
    ← iidUniform_stackPath_cylinder hP x₀ (extendPath s) T]
  congr 1
  ext w
  exact extendPath_eq_iff _ s

/-- **The two representations have the same path law** (post #3): driving the chain by one
i.i.d. uniform sequence or by i.i.d. per-state stacks gives the same law of
`(x₀, …, x_T)`, for every `T`. -/
theorem map_drivenPath_eq_map_stackPath {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ : Fin n) (T : ℕ) :
    (iidUniform ℕ).map (fun u t ↦ drivenPath P x₀ u (t : Fin (T + 1))) =
      (iidUniform (Fin n × ℕ)).map
        (fun w t ↦ stackPath P x₀ (Function.curry w) (t : Fin (T + 1))) :=
  Measure.ext_of_singleton fun s ↦ by
    rw [map_drivenPath_singleton hP, map_stackPath_singleton hP]

end RQMCMarkov.MarkovDriving

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # CUD sequences exist: an i.i.d. uniform sequence is CUD almost surely

The Chentsov theorems (`ChentsovConsistency`) assume a CUD driving sequence. This module shows
the assumption is not vacuous: under the i.i.d. `U[0,1)` measure `iidUniform ℕ`
(`MarkovDriving.DrivingMC`), almost every sequence is completely uniformly distributed
(Knuth's definition of a random sequence; Owen–Tribble 2005).

**Proof.** Fix `d` and a box `B ⊆ [0,1)^d`. The indicators `Y_t = 1{(u_t, …, u_{t+d-1}) ∈ B}`
are identically distributed (shift invariance of the product measure) with mean `vol B`, and
`d`-dependent. For each residue `r < d` the subsequence `q ↦ Y_{dq+r}` uses disjoint blocks of
coordinates, so it is pairwise independent, and Etemadi's strong law (`strong_law_ae_real`)
gives `(1/Q) ∑_{q<Q} Y_{dq+r} → vol B` a.s.; interleaving the `d` subsequences gives the box
frequency (`tendsto_avg_of_interleaved`). Countably many grid boxes `∏ₖ [iₖ/M, jₖ/M)` then
give every box (`isUD_of_grid`, a sandwich with error `2d/M`), and there are countably many `d`.

**Results.**
* `isUD_fin_zero`: in dimension `0` every sequence is uniformly distributed.
* `tendsto_avg_of_interleaved`: averages along the `d` interleaved subsequences determine the
  average of a bounded sequence.
* `abs_prod_sub_prod_le`: `|∏ xₖ - ∏ yₖ| ≤ ∑ |xₖ - yₖ|` on `[0,1]`.
* `isUD_of_grid`: uniform distribution follows from the grid boxes.
* `ae_tendsto_empAvg_box`: for a fixed box, the window frequencies of an i.i.d. uniform
  sequence converge a.s. to the volume.
* `ae_isCUD_iidUniform`: **an i.i.d. `U[0,1)` sequence is CUD almost surely**, and
  `exists_isCUD`: CUD sequences exist.
-/

namespace RQMCMarkov.MarkovDriving

open Filter Topology Finset MeasureTheory ProbabilityTheory

/-- In dimension `0` every sequence is uniformly distributed. -/
theorem isUD_fin_zero (x : ℕ → Fin 0 → ℝ) : IsUD x := by
  refine ⟨fun n k => k.elim0, fun a b _ => ?_⟩
  rw [Fin.prod_univ_zero]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  unfold empAvg boxInd
  simp only [Fin.prod_univ_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [div_self (by exact_mod_cast hN.ne')]

/-- Summing over `t < d Q` is summing over the `d` interleaved subsequences. -/
theorem sum_range_mul_eq_sum_interleaved (f : ℕ → ℝ) (d Q : ℕ) :
    ∑ t ∈ range (d * Q), f t = ∑ r ∈ range d, ∑ q ∈ range Q, f (d * q + r) := by
  induction Q with
  | zero =>
    rw [mul_zero, Finset.sum_range_zero]
    exact (Finset.sum_eq_zero fun r _ => Finset.sum_range_zero _).symm
  | succ Q ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => (Finset.sum_range_succ _ _).symm

/-- **Interleaving.** If `0 ≤ f ≤ 1` and along each of the `d ≥ 1` interleaved subsequences
`q ↦ f (d q + r)` the averages tend to `L`, then the averages of `f` tend to `L`. -/
theorem tendsto_avg_of_interleaved {f : ℕ → ℝ} (hf0 : ∀ t, 0 ≤ f t) (hf1 : ∀ t, f t ≤ 1)
    {d : ℕ} (hd : 0 < d) {L : ℝ}
    (h : ∀ r < d, Tendsto (fun Q => (∑ q ∈ range Q, f (d * q + r)) / Q) atTop (𝓝 L)) :
    Tendsto (fun N => (∑ t ∈ range N, f t) / N) atTop (𝓝 L) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  -- block averages
  have hg : Tendsto (fun Q => (∑ t ∈ range (d * Q), f t) / Q) atTop (𝓝 (d * L)) := by
    have := tendsto_finsetSum (range d) fun r hr => h r (Finset.mem_range.1 hr)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    refine this.congr fun Q => ?_
    rw [sum_range_mul_eq_sum_interleaved, Finset.sum_div]
  have hgN := hg.comp (Nat.tendsto_div_const_atTop hd.ne')
  -- the ratio `(N / d) / N → 1 / d`
  have hratio : Tendsto (fun N : ℕ => ((N / d : ℕ) : ℝ) / N) atTop (𝓝 (1 / d)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop : Tendsto
        (fun N : ℕ => (1 : ℝ) / N) atTop (𝓝 0))
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have h1 : ((d * (N / d) : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.mul_div_le N d
    have h2 : (N : ℝ) < d * ((N / d : ℕ) : ℝ) + d := by
      have : N < d * (N / d) + d := by
        have := Nat.lt_div_mul_add (a := N) hd
        rw [mul_comm]
        exact this
      exact_mod_cast this
    rw [Nat.cast_mul] at h1
    rw [Real.norm_eq_abs, div_sub_div _ _ hNR.ne' hdR.ne', abs_div,
      abs_of_pos (mul_pos hNR hdR), div_le_div_iff₀ (mul_pos hNR hdR) hNR]
    have habs : |((N / d : ℕ) : ℝ) * d - N * 1| ≤ d := abs_le.2 ⟨by linarith, by linarith⟩
    nlinarith [abs_nonneg (((N / d : ℕ) : ℝ) * d - N * 1)]
  -- the remainder
  have hrem : Tendsto (fun N : ℕ => ((∑ t ∈ range N, f t) - ∑ t ∈ range (d * (N / d)), f t) / N)
      atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop : Tendsto
        (fun N : ℕ => (d : ℝ) / N) atTop (𝓝 0))
    · filter_upwards [eventually_gt_atTop 0] with N hN
      have hsplit := Finset.sum_range_add f (d * (N / d)) (N - d * (N / d))
      rw [Nat.add_sub_cancel' (Nat.mul_div_le N d)] at hsplit
      rw [hsplit, add_sub_cancel_left]
      exact div_nonneg (Finset.sum_nonneg fun t _ => hf0 _) (Nat.cast_nonneg N)
    · filter_upwards [eventually_gt_atTop 0] with N hN
      have hNR : (0 : ℝ) < N := by exact_mod_cast hN
      have hsplit := Finset.sum_range_add f (d * (N / d)) (N - d * (N / d))
      rw [Nat.add_sub_cancel' (Nat.mul_div_le N d)] at hsplit
      rw [hsplit, add_sub_cancel_left]
      refine div_le_div_of_nonneg_right ?_ hNR.le
      have hlt : N - d * (N / d) ≤ d := by
        have := Nat.lt_div_mul_add (a := N) hd
        rw [mul_comm] at this
        omega
      calc ∑ t ∈ range (N - d * (N / d)), f (d * (N / d) + t)
          ≤ ∑ t ∈ range (N - d * (N / d)), (1 : ℝ) := Finset.sum_le_sum fun t _ => hf1 _
        _ = ((N - d * (N / d) : ℕ) : ℝ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        _ ≤ d := by exact_mod_cast hlt
  have hlim := (hgN.mul hratio).add hrem
  rw [mul_one_div, mul_div_cancel_left₀ L hdR.ne', add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [Function.comp_apply]
  by_cases hQ : N / d = 0
  · rw [hQ, Nat.cast_zero, zero_div, div_zero, zero_mul, zero_add, mul_zero,
      Finset.sum_range_zero, sub_zero]
  · have hQR : ((N / d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hQ
    rw [div_mul_div_comm, mul_comm ((N / d : ℕ) : ℝ) (N : ℝ), ← div_mul_div_comm,
      div_self hQR, mul_one, ← add_div, add_sub_cancel]

/-- `|∏ xₖ - ∏ yₖ| ≤ ∑ |xₖ - yₖ|` for factors in `[0,1]`. -/
theorem abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) {x y : ι → ℝ}
    (hx : ∀ k, x k ∈ Set.Icc (0 : ℝ) 1) (hy : ∀ k, y k ∈ Set.Icc (0 : ℝ) 1) :
    |∏ k ∈ s, x k - ∏ k ∈ s, y k| ≤ ∑ k ∈ s, |x k - y k| := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, sub_self, abs_zero, Finset.sum_empty]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hpy : ∏ k ∈ s, y k ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨Finset.prod_nonneg fun k _ => (hy k).1,
        Finset.prod_le_one₀ (fun k _ => (hy k).1) fun k _ => (hy k).2⟩
    have e : x a * ∏ k ∈ s, x k - y a * ∏ k ∈ s, y k =
        x a * (∏ k ∈ s, x k - ∏ k ∈ s, y k) + (x a - y a) * ∏ k ∈ s, y k := by ring
    rw [e]
    calc _ ≤ |x a * (∏ k ∈ s, x k - ∏ k ∈ s, y k)| + |(x a - y a) * ∏ k ∈ s, y k| :=
          abs_add_le _ _
      _ ≤ 1 * |∏ k ∈ s, x k - ∏ k ∈ s, y k| + |x a - y a| * 1 := by
          rw [abs_mul, abs_mul, abs_of_nonneg (hx a).1, abs_of_nonneg hpy.1]
          exact add_le_add (mul_le_mul_of_nonneg_right (hx a).2 (abs_nonneg _))
            (mul_le_mul_of_nonneg_left hpy.2 (abs_nonneg _))
      _ ≤ _ := by linarith

/-- If `M c - e ≤ D ≤ M c + e` with `M > 0`, then `|D/M - c| ≤ e/M`. -/
theorem abs_div_sub_le {D c M e : ℝ} (hM : 0 < M) (h1 : M * c - e ≤ D) (h2 : D ≤ M * c + e) :
    |D / M - c| ≤ e / M := by
  calc |D / M - c| = |D / M - M * c / M| := by rw [mul_div_cancel_left₀ _ hM.ne']
    _ = |D - M * c| / M := by rw [← sub_div, abs_div, abs_of_pos hM]
    _ ≤ e / M := div_le_div_of_nonneg_right (abs_le.2 ⟨by linarith, by linarith⟩) hM.le

/-- **Uniform distribution from grid boxes.** If the points lie in `[0,1)^d` and every grid box
`∏ₖ [iₖ/M, jₖ/M)` (`iₖ ≤ jₖ ≤ M`, `M ≥ 1`) has limiting frequency `∏ₖ (jₖ - iₖ)/M`, then the
sequence is uniformly distributed. -/
theorem isUD_of_grid {d : ℕ} {x : ℕ → Fin d → ℝ} (hx : ∀ n, InUnitCube (x n))
    (hgrid : ∀ M : ℕ, 0 < M → ∀ i j : Fin d → ℕ, (∀ k, i k ≤ j k ∧ j k ≤ M) →
      Tendsto (empAvg (boxInd fun k => Set.Ico ((i k : ℝ) / M) ((j k : ℝ) / M)) x) atTop
        (𝓝 (∏ k, ((j k : ℝ) / M - (i k : ℝ) / M)))) :
    IsUD x := by
  refine ⟨hx, fun a b hab => ?_⟩
  -- for each `M`, a lower and an upper grid box, within `2/M` per side
  have hbox : ∀ M : ℕ, 0 < M →
      (∃ i j : Fin d → ℕ, (∀ k, i k ≤ j k ∧ j k ≤ M) ∧
        (∀ w : Fin d → ℝ, (∀ k, w k ∈ Set.Ico ((i k : ℝ) / M) ((j k : ℝ) / M)) →
          ∀ k, w k ∈ Set.Ico (a k) (b k)) ∧
        |∏ k, ((j k : ℝ) / M - (i k : ℝ) / M) - ∏ k, (b k - a k)| ≤ 2 * d / M) ∧
      (∃ i j : Fin d → ℕ, (∀ k, i k ≤ j k ∧ j k ≤ M) ∧
        (∀ w : Fin d → ℝ, InUnitCube w → (∀ k, w k ∈ Set.Ico (a k) (b k)) →
          ∀ k, w k ∈ Set.Ico ((i k : ℝ) / M) ((j k : ℝ) / M)) ∧
        |∏ k, ((j k : ℝ) / M - (i k : ℝ) / M) - ∏ k, (b k - a k)| ≤ 2 * d / M) := by
    intro M hM
    have hMR : (0 : ℝ) < M := by exact_mod_cast hM
    have hsum : ∑ _k : Fin d, (2 : ℝ) / M = 2 * d / M := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hba : ∀ k, b k - a k ∈ Set.Icc (0 : ℝ) 1 := fun k =>
      ⟨sub_nonneg.2 (hab k).2.1, by linarith [(hab k).1, (hab k).2.2]⟩
    constructor
    · -- lower box: `[⌈M a⌉/M, max(⌈M a⌉, ⌊M b⌋)/M)`
      set i : Fin d → ℕ := fun k => ⌈(M : ℝ) * a k⌉₊ with hi
      set j : Fin d → ℕ := fun k => max (i k) ⌊(M : ℝ) * b k⌋₊ with hj
      have hiM : ∀ k, i k ≤ M := fun k => by
        rw [hi]
        apply Nat.ceil_le.2
        have := mul_le_mul_of_nonneg_left ((hab k).2.1.trans (hab k).2.2) hMR.le
        linarith
      have hfloorM : ∀ k, ⌊(M : ℝ) * b k⌋₊ ≤ M := fun k => by
        apply Nat.floor_le_of_le
        have := mul_le_mul_of_nonneg_left (hab k).2.2 hMR.le
        linarith
      refine ⟨i, j, fun k => ⟨le_max_left _ _, max_le (hiM k) (hfloorM k)⟩, ?_, ?_⟩
      · intro w hw k
        have h1 := (hw k).1
        have h2 := (hw k).2
        have hia : a k ≤ (i k : ℝ) / M := by
          rw [le_div_iff₀ hMR]
          linarith [Nat.le_ceil ((M : ℝ) * a k)]
        refine ⟨hia.trans h1, ?_⟩
        have hij : i k < j k := by
          have : (i k : ℝ) < j k := by
            have := lt_of_le_of_lt h1 h2
            rwa [div_lt_div_iff_of_pos_right hMR] at this
          exact_mod_cast this
        have hjk : j k = max (i k) ⌊(M : ℝ) * b k⌋₊ := rfl
        have hjf : j k = ⌊(M : ℝ) * b k⌋₊ := by
          rw [hjk] at hij ⊢
          exact max_eq_right (le_of_lt ((lt_max_iff.1 hij).resolve_left (lt_irrefl _)))
        calc w k < (j k : ℝ) / M := h2
          _ ≤ b k := by
            rw [div_le_iff₀ hMR, hjf]
            linarith [Nat.floor_le (mul_nonneg hMR.le ((hab k).1.trans (hab k).2.1))]
      · have hside : ∀ k, |((j k : ℝ) / M - (i k : ℝ) / M) - (b k - a k)| ≤ 2 / M := by
          intro k
          have hc1 := Nat.le_ceil ((M : ℝ) * a k)
          have hc2 := Nat.ceil_lt_add_one (mul_nonneg hMR.le (hab k).1)
          have hf1 := Nat.floor_le (mul_nonneg hMR.le ((hab k).1.trans (hab k).2.1))
          have hf2 := Nat.lt_floor_add_one ((M : ℝ) * b k)
          have hjmax : (j k : ℝ) = max (i k : ℝ) (⌊(M : ℝ) * b k⌋₊ : ℝ) := by
            rw [show j k = max (i k) ⌊(M : ℝ) * b k⌋₊ from rfl, Nat.cast_max]
          rw [← sub_div]
          have hab' := mul_le_mul_of_nonneg_left (hab k).2.1 hMR.le
          refine abs_div_sub_le hMR ?_ ?_
          · rcases le_total (i k : ℝ) (⌊(M : ℝ) * b k⌋₊ : ℝ) with hle | hle
            · rw [hjmax, max_eq_right hle]
              nlinarith
            · rw [hjmax, max_eq_left hle]
              nlinarith
          · rcases le_total (i k : ℝ) (⌊(M : ℝ) * b k⌋₊ : ℝ) with hle | hle
            · rw [hjmax, max_eq_right hle]
              nlinarith
            · rw [hjmax, max_eq_left hle]
              nlinarith
        refine (abs_prod_sub_prod_le _ (fun k => ?_) hba).trans ?_
        · have hdiff := hside k
          have hnn : (i k : ℝ) / M ≤ (j k : ℝ) / M :=
            div_le_div_of_nonneg_right (by exact_mod_cast le_max_left _ _) hMR.le
          have hjM : (j k : ℝ) / M ≤ 1 := by
            rw [div_le_one hMR]
            exact_mod_cast max_le (hiM k) (hfloorM k)
          have hi0 : 0 ≤ (i k : ℝ) / M := by positivity
          exact ⟨sub_nonneg.2 hnn, by linarith⟩
        · rw [← hsum]
          exact Finset.sum_le_sum fun k _ => hside k
    · -- upper box: `[⌊M a⌋/M, min(⌈M b⌉, M)/M)`
      set i : Fin d → ℕ := fun k => ⌊(M : ℝ) * a k⌋₊ with hi
      set j : Fin d → ℕ := fun k => min ⌈(M : ℝ) * b k⌉₊ M with hj
      have hij : ∀ k, i k ≤ j k := fun k => by
        rw [hi, hj]
        refine le_min ?_ ?_
        · have h1 := Nat.floor_le (mul_nonneg hMR.le (hab k).1)
          have h2 := Nat.le_ceil ((M : ℝ) * b k)
          have h3 := mul_le_mul_of_nonneg_left (hab k).2.1 hMR.le
          have : (⌊(M : ℝ) * a k⌋₊ : ℝ) ≤ ⌈(M : ℝ) * b k⌉₊ := by linarith
          exact_mod_cast this
        · apply Nat.floor_le_of_le
          have := mul_le_mul_of_nonneg_left ((hab k).2.1.trans (hab k).2.2) hMR.le
          linarith
      refine ⟨i, j, fun k => ⟨hij k, min_le_right _ _⟩, ?_, ?_⟩
      · intro w hw hwab k
        have ha0 : 0 ≤ (M : ℝ) * a k := mul_nonneg hMR.le (hab k).1
        refine ⟨?_, ?_⟩
        · calc (i k : ℝ) / M ≤ a k := by
                rw [div_le_iff₀ hMR]
                linarith [Nat.floor_le ha0]
            _ ≤ w k := (hwab k).1
        · have hjmin : (j k : ℝ) = min (⌈(M : ℝ) * b k⌉₊ : ℝ) (M : ℝ) := by
            rw [show j k = min ⌈(M : ℝ) * b k⌉₊ M from rfl, Nat.cast_min]
          rw [lt_div_iff₀ hMR, hjmin, lt_min_iff]
          constructor
          · calc w k * M < b k * M := mul_lt_mul_of_pos_right (hwab k).2 hMR
              _ ≤ _ := by linarith [Nat.le_ceil ((M : ℝ) * b k)]
          · calc w k * M < 1 * M := mul_lt_mul_of_pos_right (hw k).2 hMR
              _ = M := one_mul _
      · have hside : ∀ k, |((j k : ℝ) / M - (i k : ℝ) / M) - (b k - a k)| ≤ 2 / M := by
          intro k
          have ha0 : 0 ≤ (M : ℝ) * a k := mul_nonneg hMR.le (hab k).1
          have hf1 := Nat.floor_le ha0
          have hf2 := Nat.lt_floor_add_one ((M : ℝ) * a k)
          have hc1 := Nat.le_ceil ((M : ℝ) * b k)
          have hc2 := Nat.ceil_lt_add_one (mul_nonneg hMR.le ((hab k).1.trans (hab k).2.1))
          have hjmin : (j k : ℝ) = min (⌈(M : ℝ) * b k⌉₊ : ℝ) (M : ℝ) := by
            rw [show j k = min ⌈(M : ℝ) * b k⌉₊ M from rfl, Nat.cast_min]
          have hMb : (M : ℝ) * b k ≤ M := by
            have := mul_le_mul_of_nonneg_left (hab k).2.2 hMR.le
            linarith
          rw [← sub_div]
          refine abs_div_sub_le hMR ?_ ?_
          · rcases le_total (⌈(M : ℝ) * b k⌉₊ : ℝ) (M : ℝ) with hle | hle
            · rw [hjmin, min_eq_left hle]
              nlinarith
            · rw [hjmin, min_eq_right hle]
              nlinarith
          · rcases le_total (⌈(M : ℝ) * b k⌉₊ : ℝ) (M : ℝ) with hle | hle
            · rw [hjmin, min_eq_left hle]
              nlinarith
            · rw [hjmin, min_eq_right hle]
              nlinarith
        refine (abs_prod_sub_prod_le _ (fun k => ?_) hba).trans ?_
        · have hnn : (i k : ℝ) / M ≤ (j k : ℝ) / M :=
            div_le_div_of_nonneg_right (by exact_mod_cast hij k) hMR.le
          have hjM : (j k : ℝ) / M ≤ 1 := by
            rw [div_le_one hMR]
            exact_mod_cast min_le_right _ _
          have hi0 : 0 ≤ (i k : ℝ) / M := by positivity
          exact ⟨sub_nonneg.2 hnn, by linarith⟩
        · rw [← hsum]
          exact Finset.sum_le_sum fun k _ => hside k
  -- the error `2d/M` tends to `0`
  have herr : Tendsto (fun M : ℕ => 2 * (d : ℝ) / M) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine tendsto_order.2 ⟨fun c hc => ?_, fun c hc => ?_⟩
  · obtain ⟨M, hMc, hM⟩ := ((herr.eventually (gt_mem_nhds (sub_pos.2 hc))).and
      (eventually_gt_atTop 0)).exists
    obtain ⟨⟨i, j, hij, hsub, herrb⟩, _⟩ := hbox M hM
    have hlim := hgrid M hM i j hij
    have hc' : c < ∏ k, ((j k : ℝ) / M - (i k : ℝ) / M) := by
      have := (abs_le.1 herrb).1
      linarith
    filter_upwards [hlim.eventually (lt_mem_nhds hc')] with N hN
    refine hN.trans_le (empAvg_le_empAvg (fun n => boxInd_le_boxInd fun h => hsub _ h) N)
  · obtain ⟨M, hMc, hM⟩ := ((herr.eventually (gt_mem_nhds (sub_pos.2 hc))).and
      (eventually_gt_atTop 0)).exists
    obtain ⟨_, ⟨i, j, hij, hsup, herrb⟩⟩ := hbox M hM
    have hlim := hgrid M hM i j hij
    have hc' : ∏ k, ((j k : ℝ) / M - (i k : ℝ) / M) < c := by
      have := (abs_le.1 herrb).2
      linarith
    filter_upwards [hlim.eventually (gt_mem_nhds hc')] with N hN
    exact (empAvg_le_empAvg (fun n => boxInd_le_boxInd fun h => hsup _ (hx n) h) N).trans_lt hN

/-- Box indicators of measurable sides are measurable. -/
theorem measurable_boxInd {d : ℕ} {S : Fin d → Set ℝ} (hS : ∀ k, MeasurableSet (S k)) :
    Measurable (boxInd S) := by
  unfold boxInd
  exact Finset.measurable_prod _ fun k _ =>
    (measurable_const.indicator (hS k)).comp (measurable_pi_apply k)

/-- Under the i.i.d. measure, the window indicator at time `t` has the law of the one at time
`0` (shift invariance). -/
theorem identDistrib_window_boxInd {d : ℕ} {S : Fin d → Set ℝ} (hS : ∀ k, MeasurableSet (S k))
    (t : ℕ) :
    IdentDistrib (fun ω : ℕ → ℝ => boxInd S (window ω d t))
      (fun ω : ℕ → ℝ => boxInd S fun k : Fin d => ω k) (iidUniform ℕ) (iidUniform ℕ) := by
  have hmeas : Measurable fun ω : ℕ → ℝ => boxInd S fun k : Fin d => ω k :=
    (measurable_boxInd hS).comp (measurable_pi_iff.2 fun k => measurable_pi_apply _)
  have hshift : Measurable fun ω : ℕ → ℝ => fun i : ℕ => ω (t + i) :=
    measurable_pi_iff.2 fun i => measurable_pi_apply _
  refine ⟨(hmeas.comp hshift).aemeasurable, hmeas.aemeasurable, ?_⟩
  have hmap : (iidUniform ℕ).map (fun ω : ℕ → ℝ => fun i : ℕ => ω (t + i)) = iidUniform ℕ := by
    have := isProbabilityMeasure_uniformIco
    unfold iidUniform
    exact Measure.map_infinitePi_infinitePi_of_inj (add_right_injective t)
  change (iidUniform ℕ).map ((fun ω : ℕ → ℝ => boxInd S fun k : Fin d => ω k) ∘
    fun ω i => ω (t + i)) = _
  rw [← Measure.map_map hmeas hshift, hmap]

/-- Window indicators at times at least `d` apart are independent under the i.i.d. measure. -/
theorem indepFun_window_boxInd {d : ℕ} {S : Fin d → Set ℝ} (hS : ∀ k, MeasurableSet (S k))
    {s t : ℕ} (hst : s + d ≤ t ∨ t + d ≤ s) :
    IndepFun (fun ω : ℕ → ℝ => boxInd S (window ω d s))
      (fun ω : ℕ → ℝ => boxInd S (window ω d t)) (iidUniform ℕ) := by
  have hind : iIndepFun (fun i (ω : ℕ → ℝ) => ω i) (iidUniform ℕ) := by
    have := isProbabilityMeasure_uniformIco
    unfold iidUniform
    exact iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id
  have hdisj : Disjoint (Finset.Ico s (s + d)) (Finset.Ico t (t + d)) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    rw [Finset.mem_Ico] at hi hi'
    omega
  have h := hind.indepFun_finset _ _ hdisj fun i => measurable_pi_apply i
  have hφ : ∀ v : ℕ, Measurable fun z : (Finset.Ico v (v + d)) → ℝ =>
      boxInd S fun k : Fin d => z ⟨v + k, Finset.mem_Ico.2 ⟨Nat.le_add_right _ _, by omega⟩⟩ :=
    fun v => (measurable_boxInd hS).comp (measurable_pi_iff.2 fun k => measurable_pi_apply _)
  exact h.comp (hφ s) (hφ t)

/-- The mean of a box indicator under the i.i.d. measure is the volume of the box. -/
theorem integral_boxInd_iidUniform {d : ℕ} {a b : Fin d → ℝ}
    (hab : ∀ k, 0 ≤ a k ∧ a k ≤ b k ∧ b k ≤ 1) :
    ∫ ω, boxInd (fun k => Set.Ico (a k) (b k)) (fun k : Fin d => ω k) ∂(iidUniform ℕ) =
      ∏ k, (b k - a k) := by
  classical
  have := isProbabilityMeasure_uniformIco
  set T : ℕ → Set ℝ := fun i => if h : i < d then Set.Ico (a ⟨i, h⟩) (b ⟨i, h⟩) else Set.univ
    with hT
  set E : Set (ℕ → ℝ) := Set.pi (↑(range d)) T with hE
  have hTm : ∀ i ∈ range d, MeasurableSet (T i) := fun i _ => by
    rw [hT]
    dsimp only
    split_ifs
    · exact measurableSet_Ico
    · exact MeasurableSet.univ
  have hEm : MeasurableSet E := MeasurableSet.pi (Finset.countable_toSet _) hTm
  have hfun : (fun ω : ℕ → ℝ => boxInd (fun k => Set.Ico (a k) (b k)) fun k : Fin d => ω k) =
      E.indicator 1 := by
    funext ω
    rw [boxInd_eq_ite, Set.indicator_apply]
    have hiff : (∀ k : Fin d, ω k ∈ Set.Ico (a k) (b k)) ↔ ω ∈ E := by
      rw [hE, Set.mem_pi]
      constructor
      · intro h i hi
        have hi' : i < d := Finset.mem_range.1 hi
        rw [hT]
        simp only [hi', ↓reduceDIte]
        exact h ⟨i, hi'⟩
      · intro h k
        have := h k (Finset.mem_coe.2 (Finset.mem_range.2 k.isLt))
        rw [hT] at this
        simp only [k.isLt, ↓reduceDIte] at this
        exact this
    by_cases h : ∀ k : Fin d, ω k ∈ Set.Ico (a k) (b k)
    · simp only [h, hiff.1 h, implies_true, ↓reduceIte, Pi.one_apply]
    · simp only [h, mt hiff.2 h, ↓reduceIte]
  rw [hfun, integral_indicator_one hEm, Measure.real, hE]
  unfold iidUniform
  rw [Measure.infinitePi_pi (μ := fun _ : ℕ => uniformIco) hTm, ENNReal.toReal_prod,
    ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hTk : T k = Set.Ico (a k) (b k) := by
    rw [hT]
    simp only [k.isLt, ↓reduceDIte]
  rw [hTk, Measure.restrict_apply measurableSet_Ico,
    Set.inter_eq_left.2 (Set.Ico_subset_Ico (hab k).1 (hab k).2.2), Real.volume_Ico,
    ENNReal.toReal_ofReal (sub_nonneg.2 (hab k).2.1)]

/-- **Box frequencies of an i.i.d. sequence.** For a fixed box `∏ₖ [aₖ, bₖ)`, almost every
i.i.d. `U[0,1)` sequence has window frequencies tending to the volume. -/
theorem ae_tendsto_empAvg_box (d : ℕ) {a b : Fin d → ℝ}
    (hab : ∀ k, 0 ≤ a k ∧ a k ≤ b k ∧ b k ≤ 1) :
    ∀ᵐ ω ∂(iidUniform ℕ), Tendsto (empAvg (boxInd fun k => Set.Ico (a k) (b k)) (window ω d))
      atTop (𝓝 (∏ k, (b k - a k))) := by
  have := isProbabilityMeasure_iidUniform ℕ
  have hS : ∀ k, MeasurableSet (Set.Ico (a k) (b k)) := fun k => measurableSet_Ico
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact Eventually.of_forall fun ω => (isUD_fin_zero _).2 a b hab
  have hr : ∀ r : Fin d, ∀ᵐ ω ∂(iidUniform ℕ), Tendsto (fun Q =>
      (∑ q ∈ range Q, boxInd (fun k => Set.Ico (a k) (b k)) (window ω d (d * q + r))) / Q)
      atTop (𝓝 (∏ k, (b k - a k))) := by
    intro r
    set X : ℕ → (ℕ → ℝ) → ℝ := fun q ω =>
      boxInd (fun k => Set.Ico (a k) (b k)) (window ω d (d * q + r)) with hX
    have hident : ∀ q, IdentDistrib (X q) (X 0) (iidUniform ℕ) (iidUniform ℕ) := fun q =>
      (identDistrib_window_boxInd hS _).trans (identDistrib_window_boxInd hS _).symm
    have hindep : Pairwise fun q q' => IndepFun (X q) (X q') (iidUniform ℕ) := by
      intro q q' hqq'
      refine indepFun_window_boxInd hS ?_
      rcases lt_or_gt_of_ne hqq' with h | h
      · left
        have := Nat.mul_le_mul_left d (Nat.succ_le_of_lt h)
        rw [Nat.mul_succ] at this
        omega
      · right
        have := Nat.mul_le_mul_left d (Nat.succ_le_of_lt h)
        rw [Nat.mul_succ] at this
        omega
    have hmeas0 : Measurable (X 0) :=
      (measurable_boxInd hS).comp (measurable_pi_iff.2 fun k => measurable_pi_apply _)
    have hint : Integrable (X 0) (iidUniform ℕ) := by
      refine Integrable.of_bound hmeas0.aestronglyMeasurable 1 (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (boxInd_nonneg _ _)]
      exact boxInd_le_one _ _
    have hmean : (iidUniform ℕ)[X 0] = ∏ k, (b k - a k) := by
      rw [(identDistrib_window_boxInd hS _).integral_eq]
      exact integral_boxInd_iidUniform hab
    have hlaw := strong_law_ae_real X hint hindep hident
    rw [hmean] at hlaw
    exact hlaw
  filter_upwards [ae_all_iff.2 hr] with ω hω
  exact tendsto_avg_of_interleaved (f := fun t => boxInd (fun k => Set.Ico (a k) (b k))
    (window ω d t)) (fun t => boxInd_nonneg _ _) (fun t => boxInd_le_one _ _) hd
    fun r hr' => hω ⟨r, hr'⟩

/-- **Existence of CUD sequences.** Almost every i.i.d. `U[0,1)` sequence is completely uniformly
distributed. -/
theorem ae_isCUD_iidUniform : ∀ᵐ u ∂(iidUniform ℕ), IsCUD u := by
  have := isProbabilityMeasure_iidUniform ℕ
  have hcube : ∀ᵐ u ∂(iidUniform ℕ), ∀ t, u t ∈ Set.Ico (0 : ℝ) 1 := by
    rw [ae_all_iff]
    intro t
    have hmp : (iidUniform ℕ).map (fun u => u t) = uniformIco := by
      have := isProbabilityMeasure_uniformIco
      unfold iidUniform
      exact Measure.infinitePi_map_eval _ t
    have h1 : ∀ᵐ x ∂uniformIco, x ∈ Set.Ico (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ico
    rw [← hmp] at h1
    exact ae_of_ae_map (measurable_pi_apply t).aemeasurable h1
  have hgrid : ∀ d : ℕ, ∀ᵐ u ∂(iidUniform ℕ), ∀ p : ℕ × (Fin d → ℕ) × (Fin d → ℕ),
      0 < p.1 → (∀ k, p.2.1 k ≤ p.2.2 k ∧ p.2.2 k ≤ p.1) →
        Tendsto (empAvg (boxInd fun k => Set.Ico ((p.2.1 k : ℝ) / p.1) ((p.2.2 k : ℝ) / p.1))
          (window u d)) atTop (𝓝 (∏ k, ((p.2.2 k : ℝ) / p.1 - (p.2.1 k : ℝ) / p.1))) := by
    intro d
    rw [ae_all_iff]
    rintro ⟨M, i, j⟩
    by_cases hv : 0 < M ∧ ∀ k, i k ≤ j k ∧ j k ≤ M
    · have hMR : (0 : ℝ) < M := by exact_mod_cast hv.1
      have hab : ∀ k, 0 ≤ (i k : ℝ) / M ∧ (i k : ℝ) / M ≤ (j k : ℝ) / M ∧ (j k : ℝ) / M ≤ 1 :=
        fun k => ⟨by positivity, div_le_div_of_nonneg_right (by exact_mod_cast (hv.2 k).1)
          hMR.le, (div_le_one hMR).2 (by exact_mod_cast (hv.2 k).2)⟩
      filter_upwards [ae_tendsto_empAvg_box d hab] with u hu _ _
      exact hu
    · exact Eventually.of_forall fun u h1 h2 => absurd ⟨h1, h2⟩ hv
  change ∀ᵐ u ∂(iidUniform ℕ), ∀ d, IsUD (window u d)
  rw [ae_all_iff]
  intro d
  filter_upwards [hcube, hgrid d] with u hu hg
  exact isUD_of_grid (window_mem hu d) fun M hM i j hij => hg (M, i, j) hM hij

/-- **CUD sequences exist**, so the Chentsov theorems of `ChentsovConsistency` are not
vacuous. -/
theorem exists_isCUD : ∃ u : ℕ → ℝ, IsCUD u := by
  have := isProbabilityMeasure_iidUniform ℕ
  have : (ae (iidUniform ℕ)).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero _)
  exact ae_isCUD_iidUniform.exists

end RQMCMarkov.MarkovDriving

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # Chentsov's theorem: CUD driving gives consistent occupation frequencies

Post #3: "if the QMC method we use is 'completely uniformly distributed' … then the generated
Markov simulations are consistent for the empirical state frequencies and time averages
(Chentsov, 1967)". We prove this for a finite chain simulated by the inverse-CDF update
`step P` (`MarkovDriving.Driving`), under a **coupling-region** hypothesis, following the
coupling argument of Chentsov (1967) as presented by Owen–Tribble (2005) and Chen–Dick–Owen
(2011, Definition 6, where `d = 1`).

**Definitions.**
* `windowMap P m i w`: the state reached from `i` after `m` inverse-CDF steps driven by the
  uniforms `w 0, …, w (m-1)`; `drivenPath P x₀ u (t + m) = windowMap P m (x_t) (window u m t)`
  (`drive_add_eq_windowMap`).
* `multiStep P m i j`: the `m`-step transition probability (`multiStep_eq_pow`: it is `(Pᵐ) i j`).
* `HasCouplingBox P d`: there is a box `B ⊆ [0,1)^d` of positive volume (sides open, closed or
  half-open) and a state `j₀` such that `windowMap P d i w = j₀` for **every** start `i` whenever
  `w ∈ B`: `d` steps driven by uniforms in `B` forget the starting state.

**Results.**
* `isStepFn_windowMap`: `w ↦ 1{windowMap P m i w = j}` is a step function on `[0,1)^m` (a finite
  union of boxes, one per path `i → ⋯ → j`) with integral `multiStep P m i j`.
* `tendsto_occFreq_of_isCUD`: **Chentsov's theorem (coupling form).** If `u` is CUD, `P` is
  stochastic and has a coupling box, and `π` is a stationary distribution, then for every start
  `x₀` and state `j`, `N_j(T)/T → π_j` (`N_j(T) = occCount`, visits before `T`).
* `tendsto_timeAvg_of_isCUD`: time averages `(1/T) ∑_{t<T} g(x_t) → ∑_j π_j g(j)`.
* `hasCouplingBox_of_common_interval`, `hasCouplingBox_of_col_pos`, `hasCouplingBox_of_pos`: a
  one-step coupling box exists when the intervals of some state `j₀` in all rows share a
  subinterval; in particular when the column of the first state is bounded below by `c > 0` (a
  Doeblin condition realised by a common interval of uniforms), e.g. when all entries are
  positive.
* `tendsto_occFreq_of_isCUD_of_col_pos`: the theorem under that condition.
* `not_tendsto_occFreq_identity`: counterexample for a reducible chain (see **Correction**).
* `multiStep_fourState_two`, `not_hasCouplingBox_fourState`: a perfectly mixing chain
  (`P² = (1/4)·𝟙`) without any coupling box (see **Correction**).

**The proof.** With `m = d k`, `x_{t+m} = windowMap P m (x_t) (window u m t)`. If none of the `k`
aligned blocks of the window lies in the coupling box (`noCouple`, a step function with
integral `(1-δ)^k`, `δ = vol B`), the window may remember `x_t`; otherwise `x_{t+m}` equals
`windowMap P m r (window u m t)` for any fixed `r`. CUD gives the frequencies of both events, so
`N_j(T)/T` is eventually within `2(1-δ)^k + ε` of `π_j`; the bound `|Pᵐ(r,j) - π_j| ≤ (1-δ)^k`
(`abs_multiStep_sub_le`) comes from the same coupling read through the CUD frequencies.

**Correction (post #3).** The claim is stated without conditions on the chain. Some condition is
needed: for a reducible chain the frequencies depend on the start whatever the driving sequence,
e.g. the identity matrix on two states, where every driven path is constant
(`not_tendsto_occFreq_identity`: the frequency of state `0` from state `0` is `1`, while the
uniform vector is stationary). We prove the theorem under the coupling-box hypothesis. This is
**not** implied by irreducibility and aperiodicity, nor by a Doeblin minorisation of `P` alone:
`fourState` is a doubly stochastic chain with `P² = (1/4)·𝟙` (perfect mixing in two steps) whose
inverse-CDF grand coupling never coalesces (`not_hasCouplingBox_fourState`), because each update
sends the blocks `{0,2}` and `{1,3}` to different blocks. The coupling hypothesis is only a
convenience of this proof: `ChentsovGeneral` proves the theorem for **every** finite chain with a
unique stationary distribution (`tendsto_occFreq_of_isCUD_general`, by an entropy argument,
`ChentsovEntropy`), so `fourState` is consistent too (`tendsto_occFreq_fourState_of_isCUD`). The
corrected claim of post #3 is: *with the inverse-CDF update, driving a finite chain by a CUD
sequence gives occupation frequencies and time averages converging to `π` whenever the stationary
distribution `π` is unique* (e.g. irreducible `P`; aperiodicity is not needed). Periodic chains do
not refute the claim: the deterministic two-cycle is consistent for every driving sequence.
CUD sequences exist (`CUDExistence.exists_isCUD`: i.i.d. uniforms are CUD almost surely).
-/

namespace RQMCMarkov.MarkovDriving

open Filter Topology Finset

variable {n : ℕ}

/-- The state reached from `i` after `m` inverse-CDF steps driven by `w 0, …, w (m-1)`. -/
noncomputable def windowMap (P : Fin n → Fin n → ℝ) : (m : ℕ) → Fin n → (Fin m → ℝ) → Fin n
  | 0, i, _ => i
  | m + 1, i, w => step P (windowMap P m i fun k => w (Fin.castSucc k)) (w (Fin.last m))

/-- One step of `windowMap`. -/
theorem windowMap_succ (P : Fin n → Fin n → ℝ) (m : ℕ) (i : Fin n) (w : Fin (m + 1) → ℝ) :
    windowMap P (m + 1) i w =
      step P (windowMap P m i fun k => w (Fin.castSucc k)) (w (Fin.last m)) :=
  rfl

/-- **Composition.** Driving `m + m'` steps is driving `m` steps and then `m'` steps. -/
theorem windowMap_add (P : Fin n → Fin n → ℝ) (m m' : ℕ) (i : Fin n) (w : Fin (m + m') → ℝ) :
    windowMap P (m + m') i w = windowMap P m' (windowMap P m i fun k => w (Fin.castAdd m' k))
      (fun k => w (Fin.natAdd m k)) := by
  induction m' generalizing i with
  | zero => rfl
  | succ m' ih =>
    change step P (windowMap P (m + m') i fun k => w (Fin.castSucc k)) (w (Fin.last (m + m'))) =
      step P (windowMap P m' (windowMap P m i fun k => w (Fin.castAdd (m' + 1) k))
        fun k => w (Fin.natAdd m (Fin.castSucc k))) (w (Fin.natAdd m (Fin.last m')))
    rw [ih]
    rfl

/-- The driven path after `m` more steps is `windowMap` of the window of uniforms. -/
theorem drive_add_eq_windowMap (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (u : ℕ → ℝ) (t m : ℕ) :
    drivenPath P x₀ u (t + m) = windowMap P m (drivenPath P x₀ u t) (window u m t) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change step P (drivenPath P x₀ u (t + m)) (u (t + m)) = _
    rw [ih]
    rfl

/-- The `m`-step transition probabilities, by the Chapman–Kolmogorov recursion
`Pᵐ⁺¹(i,j) = ∑ₖ Pᵐ(i,k) P(k,j)`. -/
noncomputable def multiStep (P : Fin n → Fin n → ℝ) : ℕ → Fin n → Fin n → ℝ
  | 0, i, j => if i = j then 1 else 0
  | m + 1, i, j => ∑ k, multiStep P m i k * P k j

/-- `multiStep P m` is the matrix power `Pᵐ`. -/
theorem multiStep_eq_pow (P : Fin n → Fin n → ℝ) (m : ℕ) (i j : Fin n) :
    multiStep P m i j = (Matrix.of P ^ m) i j := by
  induction m generalizing j with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    rfl
  | succ m ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [ih, Matrix.of_apply]

/-- A stationary vector is stationary for every `Pᵐ`. -/
theorem sum_mul_multiStep {P : Fin n → Fin n → ℝ} {π : Fin n → ℝ}
    (hπ : ∀ j, ∑ i, π i * P i j = π j) (m : ℕ) (j : Fin n) :
    ∑ i, π i * multiStep P m i j = π j := by
  induction m generalizing j with
  | zero =>
    change ∑ i, π i * (if i = j then 1 else 0) = π j
    rw [Finset.sum_eq_single j (fun i _ hij => by simp only [hij, ↓reduceIte, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h)]
    simp only [↓reduceIte, mul_one]
  | succ m ih =>
    change ∑ i, π i * ∑ k, multiStep P m i k * P k j = π j
    calc ∑ i, π i * ∑ k, multiStep P m i k * P k j
        = ∑ k, (∑ i, π i * multiStep P m i k) * P k j := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
      _ = π j := by
          rw [← hπ j]
          exact Finset.sum_congr rfl fun k _ => by rw [ih k]

/-- At `u = 0` the inverse-CDF update goes to the first state. -/
theorem val_step_zero (P : Fin n → Fin n → ℝ) (hP : IsStochastic P) (i : Fin n) :
    ((step P i 0 : Fin n) : ℕ) = 0 := by
  have h0 : (⟨0, by have := i.isLt; omega⟩ : Fin n) ∈
      insert (lastState i) (univ.filter fun j : Fin n ↦ (0 : ℝ) ≤ cumProb P i (j + 1)) :=
    Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ _,
      (cumProb_mem_Icc hP i _).1⟩)
  have hle := Finset.min'_le _ _ h0
  have : step P i 0 ≤ (⟨0, by have := i.isLt; omega⟩ : Fin n) := hle
  rw [Fin.le_def] at this
  exact Nat.le_zero.1 this

/-- The set `{u : step P i u = j}` is a side between `cs_{i,j}` and `cs_{i,j+1}`. -/
theorem isSide_step {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i j : Fin n) :
    IsSide {u | step P i u = j} (cumProb P i j) (cumProb P i (j + 1)) := by
  refine ⟨(cumProb_mem_Icc hP i _).1, cumProb_mono hP.nonneg i (Nat.le_succ _),
    (cumProb_mem_Icc hP i _).2, fun u hu => ?_, fun u hu => ?_⟩
  · have hu' : u ∈ Set.Ioc (0 : ℝ) 1 :=
      ⟨lt_of_le_of_lt (cumProb_mem_Icc hP i j).1 hu.1, hu.2.le.trans (cumProb_mem_Icc hP i _).2⟩
    exact (step_eq_iff hP i j hu').2 ⟨hu.1, hu.2.le⟩
  · rcases hu with ⟨hstep, hu0, hu1⟩
    rcases hu0.lt_or_eq with hpos | hzero
    · have h := (step_eq_iff hP i j ⟨hpos, hu1.le⟩).1 hstep
      exact ⟨h.1.le, h.2⟩
    · subst hzero
      have hj : (j : ℕ) = 0 := by
        rw [← hstep]
        exact val_step_zero P hP i
      refine ⟨?_, (cumProb_mem_Icc hP i _).1⟩
      rw [hj, cumProb_zero]

/-- One step: `v ↦ 1{step P i (v 0) = j}` is a step function on `[0,1)` with integral `P i j`. -/
theorem isStepFn_step {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i j : Fin n) :
    IsStepFn 1 (fun v => if step P i (v 0) = j then 1 else 0) (P i j) := by
  refine ((isStepFn_boxInd (S := fun _ => {u | step P i u = j})
    (a := fun _ => cumProb P i j) (b := fun _ => cumProb P i (j + 1))
    fun _ => isSide_step hP i j).congr fun v _ => ?_).of_eq ?_
  · classical
    rw [boxInd_eq_ite]
    by_cases h : step P i (v 0) = j
    · have h' : ∀ k : Fin 1, v k ∈ {u | step P i u = j} := fun k => by
        rw [Fin.fin_one_eq_zero k]; exact h
      simp only [h, h', ↓reduceIte, implies_true]
    · have h' : ¬ ∀ k : Fin 1, v k ∈ {u | step P i u = j} := fun hk => h (hk 0)
      simp only [h, h', ↓reduceIte]
  · rw [Fin.prod_univ_one, cumProb_succ, add_sub_cancel_left]

/-- **The `m`-step event is a finite union of boxes.** `w ↦ 1{windowMap P m i w = j}` is a step
function on `[0,1)^m` with integral `Pᵐ(i,j)`. -/
theorem isStepFn_windowMap {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (m : ℕ)
    (i j : Fin n) :
    IsStepFn m (fun w => if windowMap P m i w = j then 1 else 0) (multiStep P m i j) := by
  induction m generalizing j with
  | zero => exact isStepFn_const 0 (if i = j then 1 else 0)
  | succ m ih =>
    have hsum := isStepFn_finset_sum (Finset.univ : Finset (Fin n))
      (fun k _ => (ih k).append (isStepFn_step hP k j))
    refine (hsum.congr fun w _ => ?_).of_eq rfl
    change ∑ k, (if windowMap P m i (fun r => w (Fin.castSucc r)) = k then (1 : ℝ) else 0) *
        (if step P k (w (Fin.last m)) = j then 1 else 0) =
      if step P (windowMap P m i fun r => w (Fin.castSucc r)) (w (Fin.last m)) = j then 1 else 0
    rw [Finset.sum_eq_single (windowMap P m i fun r => w (Fin.castSucc r))
      (fun k _ hk => by simp only [Ne.symm hk, ↓reduceIte, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp only [↓reduceIte, one_mul]

/-- **Coupling box** (Owen–Tribble 2005; Chen–Dick–Owen 2011, Definition 6, for `d = 1`): a box
`B = ∏ₖ Sₖ ⊆ [0,1)^d` of positive volume and a state `j₀` such that `d` inverse-CDF steps driven
by any `w ∈ B` end in `j₀` from every starting state. -/
def HasCouplingBox (P : Fin n → Fin n → ℝ) (d : ℕ) : Prop :=
  ∃ (S : Fin d → Set ℝ) (a b : Fin d → ℝ) (j₀ : Fin n),
    (∀ k, IsSide (S k) (a k) (b k)) ∧ 0 < ∏ k, (b k - a k) ∧
    ∀ w, InUnitCube w → (∀ k, w k ∈ S k) → ∀ i, windowMap P d i w = j₀

/-- The indicator that none of the `k` aligned blocks of length `d` of `w` lies in the box
`∏ S`. -/
noncomputable def noCouple {d : ℕ} (S : Fin d → Set ℝ) : (k : ℕ) → (Fin (d * k) → ℝ) → ℝ
  | 0, _ => 1
  | k + 1, w => noCouple S k (fun r => w (Fin.castAdd d r)) *
      (1 - boxInd S fun r => w (Fin.natAdd (d * k) r))

/-- `noCouple` is a step function with integral `(1 - vol B)^k`. -/
theorem isStepFn_noCouple {d : ℕ} {S : Fin d → Set ℝ} {a b : Fin d → ℝ}
    (hS : ∀ k, IsSide (S k) (a k) (b k)) (k : ℕ) :
    IsStepFn (d * k) (noCouple S k) ((1 - ∏ r, (b r - a r)) ^ k) := by
  induction k with
  | zero => exact (isStepFn_const 0 1).of_eq (pow_zero _).symm
  | succ k ih =>
    exact (ih.append ((isStepFn_const d 1).sub (isStepFn_boxInd hS))).of_eq (pow_succ _ _).symm

/-- `noCouple` takes the values `0` and `1`. -/
theorem noCouple_eq_zero_or_one {d : ℕ} (S : Fin d → Set ℝ) (k : ℕ) (w : Fin (d * k) → ℝ) :
    noCouple S k w = 0 ∨ noCouple S k w = 1 := by
  induction k with
  | zero => exact Or.inr rfl
  | succ k ih =>
    have hdef : noCouple S (k + 1) w = noCouple S k (fun r => w (Fin.castAdd d r)) *
        (1 - boxInd S fun r => w (Fin.natAdd (d * k) r)) := rfl
    rw [hdef]
    classical
    rw [boxInd_eq_ite]
    rcases ih (fun r => w (Fin.castAdd d r)) with h | h <;> rw [h] <;> split_ifs <;> norm_num

/-- If some aligned block of `w` lies in the coupling box (`noCouple = 0`), then `d k` steps
driven by `w` end in the same state from every start. -/
theorem windowMap_eq_of_noCouple_eq_zero {P : Fin n → Fin n → ℝ} {d : ℕ} {S : Fin d → Set ℝ}
    {j₀ : Fin n} (hC : ∀ w, InUnitCube w → (∀ k, w k ∈ S k) → ∀ i, windowMap P d i w = j₀)
    (k : ℕ) (w : Fin (d * k) → ℝ) (hw : InUnitCube w) (h0 : noCouple S k w = 0) (i i' : Fin n) :
    windowMap P (d * k) i w = windowMap P (d * k) i' w := by
  induction k with
  | zero => exact absurd h0 one_ne_zero
  | succ k ih =>
    change windowMap P (d * k + d) i w = windowMap P (d * k + d) i' w
    rw [windowMap_add, windowMap_add]
    change noCouple S k (fun r => w (Fin.castAdd d r)) *
      (1 - boxInd S fun r => w (Fin.natAdd (d * k) r)) = 0 at h0
    rcases mul_eq_zero.1 h0 with h | h
    · rw [ih (fun r => w (Fin.castAdd d r)) (fun r => hw _) h]
    · have hbox := (boxInd_eq_one_iff S _).1 (sub_eq_zero.1 h).symm
      rw [hC _ (fun r => hw _) hbox, hC _ (fun r => hw _) hbox]

/-- The two event indicators differ by at most `noCouple`. -/
theorem abs_ind_sub_le_noCouple {P : Fin n → Fin n → ℝ} {d : ℕ} {S : Fin d → Set ℝ}
    {j₀ : Fin n} (hC : ∀ w, InUnitCube w → (∀ k, w k ∈ S k) → ∀ i, windowMap P d i w = j₀)
    (k : ℕ) (w : Fin (d * k) → ℝ) (hw : InUnitCube w) (i i' j : Fin n) :
    |(if windowMap P (d * k) i w = j then (1 : ℝ) else 0) -
      (if windowMap P (d * k) i' w = j then 1 else 0)| ≤ noCouple S k w := by
  rcases noCouple_eq_zero_or_one S k w with h | h
  · rw [windowMap_eq_of_noCouple_eq_zero hC k w hw h i i', sub_self, abs_zero, h]
  · rw [h]
    split_ifs <;> norm_num

/-- **Coupling bound for `Pᵐ`.** Read through the frequencies of a CUD sequence, the coupling
gives `|Pᵈᵏ(i,j) - Pᵈᵏ(i',j)| ≤ (1 - vol B)^k`. -/
theorem abs_multiStep_sub_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) {u : ℕ → ℝ}
    (hu : IsCUD u) {d : ℕ} {S : Fin d → Set ℝ} {a b : Fin d → ℝ} {j₀ : Fin n}
    (hS : ∀ k, IsSide (S k) (a k) (b k))
    (hC : ∀ w, InUnitCube w → (∀ k, w k ∈ S k) → ∀ i, windowMap P d i w = j₀)
    (k : ℕ) (i i' j : Fin n) :
    |multiStep P (d * k) i j - multiStep P (d * k) i' j| ≤ (1 - ∏ r, (b r - a r)) ^ k := by
  have hW := hu.isUD_window (d * k)
  have h1 := tendsto_empAvg_of_isStepFn hW (isStepFn_windowMap hP (d * k) i j)
  have h2 := tendsto_empAvg_of_isStepFn hW (isStepFn_windowMap hP (d * k) i' j)
  have h3 := tendsto_empAvg_of_isStepFn hW (isStepFn_noCouple hS k)
  refine le_of_tendsto_of_tendsto' (h1.sub h2).abs h3 fun N => ?_
  unfold empAvg
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, Nat.abs_cast]
  refine div_le_div_of_nonneg_right ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun t _ => ?_)) (Nat.cast_nonneg N)
  exact abs_ind_sub_le_noCouple hC k _ (hW.1 t) i i' j

/-- The occupation count as a sum of indicators. -/
theorem occCount_eq_sum (path : ℕ → Fin n) (j : Fin n) (T : ℕ) :
    (occCount path j T : ℝ) = ∑ t ∈ range T, if path t = j then (1 : ℝ) else 0 := by
  unfold occCount
  rw [Finset.card_filter, Nat.cast_sum]
  exact Finset.sum_congr rfl fun t _ => by
    split_ifs
    · exact Nat.cast_one
    · exact Nat.cast_zero

/-- Shifting a `[0,1]`-valued sum by `m` changes it by at most `m`. -/
theorem abs_sum_shift_sub_le (g : ℕ → ℝ) (hg0 : ∀ t, 0 ≤ g t) (hg1 : ∀ t, g t ≤ 1) (N m : ℕ) :
    |∑ t ∈ range N, g (t + m) - ∑ t ∈ range N, g t| ≤ m := by
  have h1 := Finset.sum_range_add g m N
  have h2 := Finset.sum_range_add g N m
  rw [add_comm m N] at h1
  have heq : ∑ t ∈ range N, g (t + m) = ∑ t ∈ range N, g (m + t) :=
    Finset.sum_congr rfl fun t _ => by rw [add_comm]
  have hA : 0 ≤ ∑ t ∈ range m, g (N + t) := Finset.sum_nonneg fun t _ => hg0 _
  have hB : 0 ≤ ∑ t ∈ range m, g t := Finset.sum_nonneg fun t _ => hg0 _
  have hA' : ∑ t ∈ range m, g (N + t) ≤ m := by
    have := Finset.sum_le_sum fun t (_ : t ∈ range m) => hg1 (N + t)
    rwa [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at this
  have hB' : ∑ t ∈ range m, g t ≤ m := by
    have := Finset.sum_le_sum fun t (_ : t ∈ range m) => hg1 t
    rwa [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at this
  rw [heq, abs_le]
  constructor <;> linarith

/-- **Chentsov's theorem, coupling form** (post #3; Chentsov 1967; Owen–Tribble 2005). Let `P`
be a stochastic matrix on `Fin n` with a coupling box for the inverse-CDF update, `π` a
stationary distribution, and `u` a CUD sequence. Then the path driven by `u` from any start
`x₀` has occupation frequencies `N_j(T)/T → π_j`. -/
theorem tendsto_occFreq_of_isCUD {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) {u : ℕ → ℝ}
    (hu : IsCUD u) {d : ℕ} (hC : HasCouplingBox P d) {π : Fin n → ℝ}
    (hπ : ∀ j, ∑ i, π i * P i j = π j) (hπ0 : ∀ i, 0 ≤ π i) (hπ1 : ∑ i, π i = 1)
    (x₀ j : Fin n) :
    Tendsto (fun T => (occCount (drivenPath P x₀ u) j T : ℝ) / T) atTop (𝓝 (π j)) := by
  obtain ⟨S, a, b, j₀, hS, hδ, hcpl⟩ := hC
  set δ := ∏ r, (b r - a r) with hδdef
  have hδ1 : δ ≤ 1 := Finset.prod_le_one₀ (fun r _ => sub_nonneg.2 (hS r).2.1)
    fun r _ => by linarith [(hS r).1, (hS r).2.2.1]
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 8 by positivity)
    (show 1 - δ < 1 by linarith)
  set m := d * k with hm
  have hW := hu.isUD_window m
  -- the comparison chain started at `x₀` and the no-coupling indicator
  have hf := tendsto_empAvg_of_isStepFn hW (isStepFn_windowMap hP m x₀ j)
  have hc := tendsto_empAvg_of_isStepFn hW (isStepFn_noCouple hS k)
  rw [← hδdef] at hc
  -- `|Pᵐ(x₀, j) - π j| ≤ (1 - δ)^k`
  have hstat : |multiStep P m x₀ j - π j| ≤ (1 - δ) ^ k := by
    have hsum : multiStep P m x₀ j - π j =
        ∑ i, π i * (multiStep P m x₀ j - multiStep P m i j) := by
      simp only [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hπ1, one_mul, sum_mul_multiStep hπ]
    rw [hsum]
    calc |∑ i, π i * (multiStep P m x₀ j - multiStep P m i j)|
        ≤ ∑ i, π i * (1 - δ) ^ k := (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => by
            rw [abs_mul, abs_of_nonneg (hπ0 i)]
            exact mul_le_mul_of_nonneg_left
              (abs_multiStep_sub_le hP hu hS hcpl k x₀ i j) (hπ0 i))
      _ = (1 - δ) ^ k := by rw [← Finset.sum_mul, hπ1, one_mul]
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 hf (ε / 8) (by positivity)
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 hc (ε / 8) (by positivity)
  obtain ⟨N₃, hN₃⟩ := exists_nat_gt (8 * m / ε)
  refine ⟨max (max N₁ N₂) (N₃ + 1), fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : N₃ + 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast le_trans (Nat.le_add_left 1 N₃) hN3
    linarith
  have hmN : (m : ℝ) / N < ε / 8 := by
    have hN3' : 8 * (m : ℝ) / ε < N := by
      have : (N₃ : ℝ) + 1 ≤ N := by exact_mod_cast hN3
      linarith
    rw [div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hε] at hN3'
    linarith
  have e1 := hN₁ N hN1
  have e2 := hN₂ N hN2
  rw [Real.dist_eq] at e1 e2 ⊢
  -- the three comparisons
  set x := drivenPath P x₀ u with hx
  set ind : ℕ → ℝ := fun t => if x t = j then 1 else 0 with hind
  have hshift := abs_sum_shift_sub_le ind
    (fun t => by rw [hind]; dsimp only; split_ifs <;> norm_num)
    (fun t => by rw [hind]; dsimp only; split_ifs <;> norm_num) N m
  have hcoup : |∑ t ∈ range N, ind (t + m) -
      ∑ t ∈ range N, (if windowMap P m x₀ (window u m t) = j then (1 : ℝ) else 0)| ≤
      ∑ t ∈ range N, noCouple S k (window u m t) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => ?_)
    rw [hind]
    dsimp only
    rw [hx, drive_add_eq_windowMap]
    exact abs_ind_sub_le_noCouple hcpl k _ (hW.1 t) _ x₀ j
  have hocc : (occCount x j N : ℝ) = ∑ t ∈ range N, ind t := occCount_eq_sum x j N
  have hfavg : empAvg (fun w => if windowMap P m x₀ w = j then 1 else 0) (window u m) N =
      (∑ t ∈ range N, (if windowMap P m x₀ (window u m t) = j then (1 : ℝ) else 0)) / N := rfl
  have hcavg : empAvg (noCouple S k) (window u m) N =
      (∑ t ∈ range N, noCouple S k (window u m t)) / N := rfl
  rw [hfavg] at e1
  rw [hcavg] at e2
  rw [hocc]
  set A := ∑ t ∈ range N, ind t
  set B := ∑ t ∈ range N, ind (t + m)
  set F := ∑ t ∈ range N, (if windowMap P m x₀ (window u m t) = j then (1 : ℝ) else 0)
  set C := ∑ t ∈ range N, noCouple S k (window u m t)
  have hAB : |A / N - B / N| ≤ m / N := by
    rw [← sub_div, abs_div, abs_of_pos hNpos]
    exact div_le_div_of_nonneg_right (by rw [abs_sub_comm]; exact hshift) hNpos.le
  have hBF : |B / N - F / N| ≤ C / N := by
    rw [← sub_div, abs_div, abs_of_pos hNpos]
    exact div_le_div_of_nonneg_right hcoup hNpos.le
  have hC2 : C / N < (1 - δ) ^ k + ε / 8 := by
    have := (abs_lt.1 e2).2
    linarith
  calc |A / N - π j|
      ≤ |A / N - B / N| + |B / N - F / N| + |F / N - multiStep P m x₀ j| +
          |multiStep P m x₀ j - π j| := by
        have := abs_sub_le (A / N) (B / N) (π j)
        have := abs_sub_le (B / N) (F / N) (π j)
        have := abs_sub_le (F / N) (multiStep P m x₀ j) (π j)
        linarith
    _ < ε / 8 + ((1 - δ) ^ k + ε / 8) + ε / 8 + (1 - δ) ^ k := by
        have := hAB.trans_lt hmN
        have := hBF.trans_lt hC2
        linarith
    _ < ε := by linarith

/-- **Time averages** (post #3): under the hypotheses of `tendsto_occFreq_of_isCUD`,
`(1/T) ∑_{t<T} g(x_t) → ∑_j π_j g(j)` for every function `g` of the state. -/
theorem tendsto_timeAvg_of_isCUD {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) {u : ℕ → ℝ}
    (hu : IsCUD u) {d : ℕ} (hC : HasCouplingBox P d) {π : Fin n → ℝ}
    (hπ : ∀ j, ∑ i, π i * P i j = π j) (hπ0 : ∀ i, 0 ≤ π i) (hπ1 : ∑ i, π i = 1)
    (x₀ : Fin n) (g : Fin n → ℝ) :
    Tendsto (fun T => (∑ t ∈ range T, g (drivenPath P x₀ u t)) / T) atTop
      (𝓝 (∑ j, π j * g j)) := by
  have h := tendsto_finsetSum (Finset.univ : Finset (Fin n)) fun j _ =>
    (tendsto_occFreq_of_isCUD hP hu hC hπ hπ0 hπ1 x₀ j).mul_const (g j)
  refine h.congr fun T => ?_
  have hfib : ∀ t, g (drivenPath P x₀ u t) =
      ∑ j, (if drivenPath P x₀ u t = j then (1 : ℝ) else 0) * g j := fun t => by
    rw [Finset.sum_eq_single (drivenPath P x₀ u t)
      (fun k _ hk => by simp only [Ne.symm hk, ↓reduceIte, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp only [↓reduceIte, one_mul]
  rw [Finset.sum_congr rfl fun t _ => hfib t, Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [occCount_eq_sum, ← Finset.sum_mul, div_mul_eq_mul_div]

/-- **One-step coupling from a common interval.** If the inverse-CDF intervals
`(cs_{i,j₀}, cs_{i,j₀+1}]` of a state `j₀` in all rows contain a common interval `(α, β)` with
`α < β`, then `(α, β)` is a coupling box of length `1`. -/
theorem hasCouplingBox_of_common_interval {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (j₀ : Fin n) {α β : ℝ} (hα : 0 ≤ α) (hαβ : α < β) (hβ : β ≤ 1)
    (hrow : ∀ i, cumProb P i j₀ ≤ α ∧ β ≤ cumProb P i (j₀ + 1)) : HasCouplingBox P 1 := by
  refine ⟨fun _ => Set.Ioo α β, fun _ => α, fun _ => β, j₀,
    fun _ => ⟨hα, hαβ.le, hβ, subset_rfl, fun v hv => ⟨hv.1.1.le, hv.1.2.le⟩⟩, ?_, ?_⟩
  · rw [Fin.prod_univ_one]
    linarith
  · intro w _ hw i
    have hv := hw 0
    change step P i (w (Fin.last 0)) = j₀
    have hlast : w (Fin.last 0) = w 0 := rfl
    rw [hlast]
    exact (step_eq_iff hP i j₀ ⟨by linarith [hv.1], by linarith [hv.2]⟩).2
      ⟨lt_of_le_of_lt (hrow i).1 hv.1, le_trans hv.2.le (hrow i).2⟩

/-- **Doeblin condition by a common interval.** If the column of the first state `j₀`
(`(j₀ : ℕ) = 0`) is bounded below by `c > 0`, then `(0, c)` is a coupling box of length `1`.
This covers every `P` with all entries positive. -/
theorem hasCouplingBox_of_col_pos {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (j₀ : Fin n)
    (hj₀ : (j₀ : ℕ) = 0) {c : ℝ} (hc : 0 < c) (hcol : ∀ i, c ≤ P i j₀) :
    HasCouplingBox P 1 := by
  have hc1 : c ≤ 1 := by
    have h := hP.sum_eq_one j₀
    have hle : P j₀ j₀ ≤ ∑ j, P j₀ j :=
      Finset.single_le_sum (fun j _ => hP.nonneg j₀ j) (Finset.mem_univ j₀)
    linarith [hcol j₀]
  refine hasCouplingBox_of_common_interval hP j₀ (le_refl 0) hc hc1 fun i => ⟨?_, ?_⟩
  · rw [hj₀, cumProb_zero]
  · rw [cumProb_succ, hj₀, cumProb_zero, zero_add]
    exact hcol i

/-- **All entries positive** (the classical ergodic case): then `(0, minᵢ P i 0)` is a coupling
box of length `1`. -/
theorem hasCouplingBox_of_pos {P : Fin (n + 1) → Fin (n + 1) → ℝ} (hP : IsStochastic P)
    (hpos : ∀ i j, 0 < P i j) : HasCouplingBox P 1 :=
  hasCouplingBox_of_col_pos hP 0 rfl (c := Finset.univ.inf' Finset.univ_nonempty fun i => P i 0)
    ((Finset.lt_inf'_iff _).2 fun i _ => hpos i 0) fun i => Finset.inf'_le _ (Finset.mem_univ i)

/-- **Chentsov's theorem under a Doeblin condition** (in particular for every `P` with all
entries positive): if the column of the first state is bounded below by `c > 0` and `u` is CUD,
the occupation frequencies converge to the stationary distribution. -/
theorem tendsto_occFreq_of_isCUD_of_col_pos {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {u : ℕ → ℝ} (hu : IsCUD u) (j₀ : Fin n) (hj₀ : (j₀ : ℕ) = 0) {c : ℝ} (hc : 0 < c)
    (hcol : ∀ i, c ≤ P i j₀) {π : Fin n → ℝ} (hπ : ∀ j, ∑ i, π i * P i j = π j)
    (hπ0 : ∀ i, 0 ≤ π i) (hπ1 : ∑ i, π i = 1) (x₀ j : Fin n) :
    Tendsto (fun T => (occCount (drivenPath P x₀ u) j T : ℝ) / T) atTop (𝓝 (π j)) :=
  tendsto_occFreq_of_isCUD hP hu (hasCouplingBox_of_col_pos hP j₀ hj₀ hc hcol) hπ hπ0 hπ1 x₀ j

/-- The identity matrix on two states: a reducible chain in which every state is absorbing. -/
noncomputable def identityTwo : Fin 2 → Fin 2 → ℝ := fun i j => if i = j then 1 else 0

/-- The identity matrix is stochastic. -/
theorem isStochastic_identityTwo : IsStochastic identityTwo := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · unfold identityTwo
    split_ifs <;> norm_num
  · rw [Fin.sum_univ_two]
    fin_cases i <;> norm_num [identityTwo]

/-- The uniform vector `(1/2, 1/2)` is stationary for the identity matrix. -/
theorem identityTwo_stationary (j : Fin 2) : ∑ i, (1 / 2 : ℝ) * identityTwo i j = 1 / 2 := by
  rw [Fin.sum_univ_two]
  fin_cases j <;> norm_num [identityTwo]

/-- Under the identity matrix, every uniform in `[0,1)` keeps the chain in state `0`. -/
theorem step_identityTwo_zero {u : ℝ} (hu : u ∈ Set.Ico (0 : ℝ) 1) :
    step identityTwo 0 u = 0 := by
  rcases hu.1.lt_or_eq with hpos | hzero
  · refine (step_eq_iff isStochastic_identityTwo 0 0 ⟨hpos, hu.2.le⟩).2 ⟨?_, ?_⟩
    · rw [Fin.val_zero, cumProb_zero]
      exact hpos
    · rw [cumProb_succ, Fin.val_zero, cumProb_zero, zero_add]
      unfold identityTwo
      norm_num
      exact hu.2.le
  · subst hzero
    exact Fin.ext (val_step_zero _ isStochastic_identityTwo 0)

/-- The path of the identity chain from state `0` is constant, whatever the driving sequence
in `[0,1)`. -/
theorem drivenPath_identityTwo {u : ℕ → ℝ} (hu : ∀ t, u t ∈ Set.Ico (0 : ℝ) 1) (t : ℕ) :
    drivenPath identityTwo 0 u t = 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change step identityTwo (drivenPath identityTwo 0 u t) (u t) = 0
    rw [ih]
    exact step_identityTwo_zero (hu t)

/-- **Counterexample (post #3, consistency needs a condition on the chain).** For the identity
chain on two states, driven from state `0` by any sequence in `[0,1)` — in particular by every
CUD sequence — the frequency of state `0` tends to `1`, not to the value `1/2` of the
stationary distribution `(1/2, 1/2)` (`identityTwo_stationary`). -/
theorem not_tendsto_occFreq_identity {u : ℕ → ℝ} (hu : ∀ t, u t ∈ Set.Ico (0 : ℝ) 1) :
    ¬ Tendsto (fun T => (occCount (drivenPath identityTwo 0 u) 0 T : ℝ) / T) atTop
      (𝓝 (1 / 2)) := by
  intro h
  have h1 : Tendsto (fun T => (occCount (drivenPath identityTwo 0 u) 0 T : ℝ) / T) atTop
      (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    have hocc : occCount (drivenPath identityTwo 0 u) 0 T = T := by
      unfold occCount
      rw [Finset.filter_true_of_mem fun t _ => drivenPath_identityTwo hu t, Finset.card_range]
    rw [hocc, div_self (by exact_mod_cast hT.ne')]
  have := tendsto_nhds_unique h h1
  norm_num at this

/-- The four-state chain with rows `(1/2, 0, 0, 1/2)` (states `0`, `2`) and `(0, 1/2, 1/2, 0)`
(states `1`, `3`): irreducible, aperiodic and doubly stochastic, with `P² = (1/4)·𝟙`. -/
noncomputable def fourState : Fin 4 → Fin 4 → ℝ := fun i j =>
  if (i : ℕ) % 2 = 0 then (if (j : ℕ) = 0 ∨ (j : ℕ) = 3 then 1 / 2 else 0)
  else (if (j : ℕ) = 1 ∨ (j : ℕ) = 2 then 1 / 2 else 0)

/-- `fourState` is stochastic. -/
theorem isStochastic_fourState : IsStochastic fourState := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · unfold fourState
    split_ifs <;> norm_num
  · rw [Fin.sum_univ_four]
    fin_cases i <;> norm_num [fourState]

/-- **Perfect mixing in two steps:** `P²(i,j) = 1/4` for all `i, j`, so `P²` is the matrix of the
uniform stationary distribution (the strongest Doeblin minorisation). -/
theorem multiStep_fourState_two (i j : Fin 4) : multiStep fourState 2 i j = 1 / 4 := by
  change ∑ k, (∑ l, (if i = l then (1 : ℝ) else 0) * fourState l k) * fourState k j = 1 / 4
  simp only [Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> norm_num [fourState]

/-- The uniform distribution is stationary for `fourState`. -/
theorem fourState_stationary (j : Fin 4) : ∑ i, (1 / 4 : ℝ) * fourState i j = 1 / 4 := by
  rw [Fin.sum_univ_four]
  fin_cases j <;> norm_num [fourState]

/-- For a uniform in `(0,1)`, the `fourState` update keeps the block (`{0,2}` or `{1,3}`, the
parity of the state) when `u ≤ 1/2` and switches it when `u > 1/2`. -/
theorem step_fourState_parity (i : Fin 4) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    ((step fourState i u : ℕ) % 2 = (i : ℕ) % 2) ↔ u ≤ 1 / 2 := by
  have hP := isStochastic_fourState
  have hu' : u ∈ Set.Ioc (0 : ℝ) 1 := ⟨hu.1, hu.2.le⟩
  by_cases h2 : u ≤ 1 / 2
  · rw [iff_true_intro h2, iff_true]
    fin_cases i
    · have h : step fourState 0 u = 0 := (step_eq_iff hP 0 0 hu').2 (by
        unfold cumProb
        rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_four, Fin.sum_univ_four]
        norm_num [fourState]
        exact ⟨hu.1, h2⟩)
      change (step fourState 0 u : ℕ) % 2 = (((0 : Fin 4) : ℕ) % 2)
      rw [h]
    · have h : step fourState 1 u = 1 := (step_eq_iff hP 1 1 hu').2 (by
        unfold cumProb
        rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_four, Fin.sum_univ_four]
        norm_num [fourState]
        exact ⟨hu.1, h2⟩)
      change (step fourState 1 u : ℕ) % 2 = (((1 : Fin 4) : ℕ) % 2)
      rw [h]
    · have h : step fourState 2 u = 0 := (step_eq_iff hP 2 0 hu').2 (by
        unfold cumProb
        rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_four, Fin.sum_univ_four]
        norm_num [fourState]
        exact ⟨hu.1, h2⟩)
      change (step fourState 2 u : ℕ) % 2 = (((2 : Fin 4) : ℕ) % 2)
      rw [h]
      rfl
    · have h : step fourState 3 u = 1 := (step_eq_iff hP 3 1 hu').2 (by
        unfold cumProb
        rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_four, Fin.sum_univ_four]
        norm_num [fourState]
        exact ⟨hu.1, h2⟩)
      change (step fourState 3 u : ℕ) % 2 = (((3 : Fin 4) : ℕ) % 2)
      rw [h]
      rfl
  · rw [iff_false_intro h2, iff_false]
    have h2' : 1 / 2 < u := lt_of_not_ge h2
    fin_cases i
    · have h : step fourState 0 u = 3 := (step_eq_iff hP 0 3 hu').2 (by
        unfold cumProb
        rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_four, Fin.sum_univ_four]
        norm_num [fourState]
        exact ⟨h2', hu.2.le⟩)
      change ¬ ((step fourState 0 u : ℕ) % 2 = (((0 : Fin 4) : ℕ) % 2))
      rw [h]
      decide
    · have h : step fourState 1 u = 2 := (step_eq_iff hP 1 2 hu').2 (by
        unfold cumProb
        rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_four, Fin.sum_univ_four]
        norm_num [fourState]
        exact ⟨h2', hu.2.le⟩)
      change ¬ ((step fourState 1 u : ℕ) % 2 = (((1 : Fin 4) : ℕ) % 2))
      rw [h]
      decide
    · have h : step fourState 2 u = 3 := (step_eq_iff hP 2 3 hu').2 (by
        unfold cumProb
        rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_four, Fin.sum_univ_four]
        norm_num [fourState]
        exact ⟨h2', hu.2.le⟩)
      change ¬ ((step fourState 2 u : ℕ) % 2 = (((2 : Fin 4) : ℕ) % 2))
      rw [h]
      decide
    · have h : step fourState 3 u = 2 := (step_eq_iff hP 3 2 hu').2 (by
        unfold cumProb
        rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_four, Fin.sum_univ_four]
        norm_num [fourState]
        exact ⟨h2', hu.2.le⟩)
      change ¬ ((step fourState 3 u : ℕ) % 2 = (((3 : Fin 4) : ℕ) % 2))
      rw [h]
      decide

/-- Paths of `fourState` started in different blocks, driven by the same uniforms in `(0,1)`,
stay in different blocks forever: the inverse-CDF grand coupling never coalesces. -/
theorem windowMap_fourState_parity_ne (m : ℕ) (w : Fin m → ℝ)
    (hw : ∀ k, w k ∈ Set.Ioo (0 : ℝ) 1) {i i' : Fin 4} (hii' : (i : ℕ) % 2 ≠ (i' : ℕ) % 2) :
    (windowMap fourState m i w : ℕ) % 2 ≠ (windowMap fourState m i' w : ℕ) % 2 := by
  induction m with
  | zero => exact hii'
  | succ m ih =>
    rw [windowMap_succ, windowMap_succ]
    have hih := ih (fun k => w (Fin.castSucc k)) fun k => hw _
    have hA := step_fourState_parity (windowMap fourState m i fun k => w (Fin.castSucc k))
      (hw (Fin.last m))
    have hB := step_fourState_parity (windowMap fourState m i' fun k => w (Fin.castSucc k))
      (hw (Fin.last m))
    have hpl : (windowMap fourState m i fun k => w (Fin.castSucc k) : ℕ) % 2 < 2 :=
      Nat.mod_lt _ (by norm_num)
    have hql : (windowMap fourState m i' fun k => w (Fin.castSucc k) : ℕ) % 2 < 2 :=
      Nat.mod_lt _ (by norm_num)
    generalize (windowMap fourState m i fun k => w (Fin.castSucc k) : ℕ) % 2 = p at hA hih hpl
    generalize (windowMap fourState m i' fun k => w (Fin.castSucc k) : ℕ) % 2 = q at hB hih hql
    have hp : ((step fourState (windowMap fourState m i fun k => w (Fin.castSucc k))
      (w (Fin.last m)) : ℕ) % 2) < 2 := Nat.mod_lt _ (by norm_num)
    have hq : ((step fourState (windowMap fourState m i' fun k => w (Fin.castSucc k))
      (w (Fin.last m)) : ℕ) % 2) < 2 := Nat.mod_lt _ (by norm_num)
    by_cases h : w (Fin.last m) ≤ 1 / 2
    · rw [hA.2 h, hB.2 h]
      exact hih
    · have h1 := mt hA.1 h
      have h2 := mt hB.1 h
      omega

/-- **The coupling hypothesis is not implied by irreducibility + aperiodicity + Doeblin.**
`fourState` (which has `P² = (1/4)·𝟙`, `multiStep_fourState_two`) has no coupling box of any
length `d`: every box of positive volume contains a window in `(0,1)^d`, and along it the paths
from `0` and from `1` never meet. -/
theorem not_hasCouplingBox_fourState (d : ℕ) : ¬ HasCouplingBox fourState d := by
  rintro ⟨S, a, b, j₀, hS, hvol, hC⟩
  have hab : ∀ k, a k < b k := by
    intro k
    rcases (hS k).2.1.lt_or_eq with h | h
    · exact h
    · exact absurd (Finset.prod_eq_zero (Finset.mem_univ k) (by rw [h, sub_self])) hvol.ne'
  set w : Fin d → ℝ := fun k => (a k + b k) / 2 with hw
  have hwI : ∀ k, w k ∈ Set.Ioo (a k) (b k) := fun k => by
    rw [hw]
    constructor <;> linarith [hab k]
  have hw01 : ∀ k, w k ∈ Set.Ioo (0 : ℝ) 1 := fun k =>
    ⟨lt_of_le_of_lt (hS k).1 (hwI k).1, lt_of_lt_of_le (hwI k).2 (hS k).2.2.1⟩
  have hcube : InUnitCube w := fun k => ⟨(hw01 k).1.le, (hw01 k).2⟩
  have hmem : ∀ k, w k ∈ S k := fun k => (hS k).2.2.2.1 (hwI k)
  have h0 := hC w hcube hmem 0
  have h1 := hC w hcube hmem 1
  exact windowMap_fourState_parity_ne d w hw01 (i := 0) (i' := 1) (by decide)
    (by rw [h0, h1])

end RQMCMarkov.MarkovDriving

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # The van der Corput sequence

Copied from `RQMCMarkov/PointSets` (namespace and imports renamed); see that project for
its documentation.

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

namespace RQMCMarkov.MarkovDriving

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

end RQMCMarkov.MarkovDriving

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # The van der Corput sequence is uniformly distributed but not CUD

Post #3: "if the QMC method we use is 'completely uniformly distributed' (not a given, using
Sobol sequences would fail this)", and codes (a): "just swapping the random numbers for a Sobol
sequence … fails badly". In one dimension the Sobol sequence is the base-2 van der Corput
sequence `φ` (`MarkovDriving.VanDerCorput`).

**Results.**
* `isUD_of_tendsto_starDiscrepancy`: in one dimension, star discrepancy `D*_N → 0` implies
  uniform distribution (boxes `[a, b)` as differences of anchored boxes `[0, t)`).
* `isUD_vanDerCorput`: `φ` is uniformly distributed in `[0,1)` (`D*_N ≤ 2 (log N + 1)/N`).
* `vanDerCorput_two_mul_add_one`: `φ(2k+1) = φ(2k) + 1/2`, and `vanDerCorput_lt_half_iff`:
  `φ(k) < 1/2 ↔ k` even. Hence consecutive terms alternate between `[0,1/2)` and `[1/2,1)`
  (`vanDerCorput_succ_lt_half_iff`): the pairs `(φ(t), φ(t+1))` avoid `[0,1/2)² ∪ [1/2,1)²`, a set
  of area `1/2`.
* `not_isUD_window_two_vanDerCorput`, `not_isCUD_vanDerCorput`: the pairs are not uniformly
  distributed in `[0,1)²` (no pair lies in `[0,1/2)²`), so `φ` is **not CUD**.
* **Counterexample (codes (a)).** `twoState` has rows `(1/2, 1/2)` and `(1, 0)` (stay
  probability `1/2` in state `0`), stationary distribution `π = (2/3, 1/3)`
  (`twoState_stationary`). Driven by `φ` from any start, the path alternates `0, 1, 0, 1, …` from
  time `3` on (`drivenPath_twoState_vanDerCorput`), so the frequency of state `1` tends to `1/2`
  (`tendsto_occFreq_twoState_vanDerCorput`), not `π₁ = 1/3`
  (`not_tendsto_occFreq_twoState_vanDerCorput`). The chain has a coupling box (column `0` is
  `≥ 1/2`), so for every CUD driving sequence the frequency does tend to `1/3`
  (`tendsto_occFreq_twoState_of_isCUD`): the failure is due to `φ` not being CUD, and one-
  dimensional uniformity, even with discrepancy `O(log N / N)`, is not enough.
-/

namespace RQMCMarkov.MarkovDriving

open Filter Topology Finset

/-- In one dimension the empirical box frequency of `[a, b)` is a difference of two anchored
counts. -/
theorem empAvg_window_one_eq (x : ℕ → ℝ) (a b : Fin 1 → ℝ) (hab : a 0 ≤ b 0) (N : ℕ) :
    empAvg (boxInd fun k => Set.Ico (a k) (b k)) (window x 1) N =
      (countBelow x N (b 0) : ℝ) / N - (countBelow x N (a 0) : ℝ) / N := by
  have hcount : ∀ t, (countBelow x N t : ℝ) = ∑ n ∈ range N, if x n < t then (1 : ℝ) else 0 := by
    intro t
    unfold countBelow
    rw [Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_congr rfl fun n _ => by
      split_ifs
      · exact Nat.cast_one
      · exact Nat.cast_zero
  unfold empAvg
  rw [hcount, hcount, ← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  classical
  rw [boxInd_eq_ite]
  have hw : ∀ k : Fin 1, window x 1 n k = x n := fun k => by
    rw [Fin.fin_one_eq_zero k]
    rfl
  by_cases h1 : x n < a 0
  · have hn : ¬ ∀ k : Fin 1, window x 1 n k ∈ Set.Ico (a k) (b k) := fun h => by
      have := (h 0).1
      rw [hw 0] at this
      linarith
    have h2 : x n < b 0 := lt_of_lt_of_le h1 hab
    simp only [hn, h1, h2, ↓reduceIte, sub_self]
  · by_cases h2 : x n < b 0
    · have hy : ∀ k : Fin 1, window x 1 n k ∈ Set.Ico (a k) (b k) := fun k => by
        rw [hw k, Fin.fin_one_eq_zero k]
        exact ⟨not_lt.1 h1, h2⟩
      simp only [hy, h1, h2, ↓reduceIte, implies_true, sub_zero]
    · have hn : ¬ ∀ k : Fin 1, window x 1 n k ∈ Set.Ico (a k) (b k) := fun h => by
        have := (h 0).2
        rw [hw 0] at this
        exact h2 this
      simp only [hn, h1, h2, ↓reduceIte, sub_self]

/-- **One-dimensional uniform distribution from discrepancy.** If `x` lies in `[0,1)` and its
star discrepancy tends to `0`, then `x` is uniformly distributed in `[0,1)`. -/
theorem isUD_of_tendsto_starDiscrepancy {x : ℕ → ℝ} (hx : ∀ n, x n ∈ Set.Ico (0 : ℝ) 1)
    (hD : Tendsto (starDiscrepancy x) atTop (𝓝 0)) : IsUD (window x 1) := by
  refine ⟨fun n k => hx (n + k), fun a b hab => ?_⟩
  rw [Fin.prod_univ_one]
  have hb : b 0 ∈ Set.Icc (0 : ℝ) 1 := ⟨(hab 0).1.trans (hab 0).2.1, (hab 0).2.2⟩
  have ha : a 0 ∈ Set.Icc (0 : ℝ) 1 := ⟨(hab 0).1, (hab 0).2.1.trans (hab 0).2.2⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h2 : Tendsto (fun N => 2 * starDiscrepancy x N) atTop (𝓝 0) := by
    have := hD.const_mul 2
    rwa [mul_zero] at this
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) h2
  rw [empAvg_window_one_eq x a b (hab 0).2.1 N, Real.norm_eq_abs]
  have hbD := localDiscrepancy_le_starDiscrepancy x N hb
  have haD := localDiscrepancy_le_starDiscrepancy x N ha
  unfold localDiscrepancy at hbD haD
  have e : (countBelow x N (b 0) : ℝ) / N - (countBelow x N (a 0) : ℝ) / N - (b 0 - a 0) =
      ((countBelow x N (b 0) : ℝ) / N - b 0) - ((countBelow x N (a 0) : ℝ) / N - a 0) := by ring
  rw [e]
  calc _ ≤ |(countBelow x N (b 0) : ℝ) / N - b 0| + |(countBelow x N (a 0) : ℝ) / N - a 0| :=
        abs_sub _ _
    _ ≤ _ := by linarith

/-- **The van der Corput sequence is uniformly distributed** in `[0,1)`. -/
theorem isUD_vanDerCorput : IsUD (window vanDerCorput 1) := by
  refine isUD_of_tendsto_starDiscrepancy vanDerCorput_mem_Ico ?_
  have hb : Tendsto (fun n : ℕ => 2 * (Real.log n + 1) / n) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ tendsto_sqrt_mul_vanDerCorput_bound
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hl : 0 ≤ Real.log n := Real.log_nonneg this
      positivity
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hl : 0 ≤ Real.log n := Real.log_nonneg h1
      have hs : 1 ≤ Real.sqrt n := by rw [Real.one_le_sqrt]; exact h1
      have hnn : 0 ≤ 2 * (Real.log n + 1) / n := by positivity
      calc 2 * (Real.log n + 1) / n = 1 * (2 * (Real.log n + 1) / n) := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hs hnn
  refine squeeze_zero' (Eventually.of_forall fun n => starDiscrepancy_nonneg _ _) ?_ hb
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact starDiscrepancy_vanDerCorput_le_log hn

/-- `φ(2k+1) = φ(2k) + 1/2`: the term after an even-indexed term is shifted by exactly `1/2`. -/
theorem vanDerCorput_two_mul_add_one (k : ℕ) :
    vanDerCorput (2 * k + 1) = vanDerCorput (2 * k) + 1 / 2 := by
  have h1 := vanDerCorput_two_mul_add k 1 (by norm_num)
  have h0 := vanDerCorput_two_mul_add k 0 (by norm_num)
  rw [add_zero] at h0
  rw [h1, h0]
  push_cast
  ring

/-- `φ(k) < 1/2` exactly for even `k`. -/
theorem vanDerCorput_lt_half_iff (k : ℕ) : vanDerCorput k < 1 / 2 ↔ k % 2 = 0 := by
  have h := vanDerCorput_mem_Ico (k / 2)
  rw [vanDerCorput_eq k]
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · rw [hk, Nat.cast_zero]
    exact ⟨fun _ => rfl, fun _ => by linarith [h.2]⟩
  · rw [hk, Nat.cast_one]
    exact ⟨fun h' => by linarith [h.1], fun h' => absurd h' (by norm_num)⟩

/-- **Consecutive terms alternate halves:** `φ(t+1) < 1/2 ↔ ¬ φ(t) < 1/2`. -/
theorem vanDerCorput_succ_lt_half_iff (t : ℕ) :
    vanDerCorput (t + 1) < 1 / 2 ↔ ¬ vanDerCorput t < 1 / 2 := by
  rw [vanDerCorput_lt_half_iff, vanDerCorput_lt_half_iff]
  omega

/-- **The van der Corput pairs are not uniformly distributed** in `[0,1)²`: no pair
`(φ(t), φ(t+1))` lies in `[0,1/2)²`, whose area is `1/4`. -/
theorem not_isUD_window_two_vanDerCorput : ¬ IsUD (window vanDerCorput 2) := by
  intro hUD
  have hlim := hUD.2 (fun _ => 0) (fun _ => 1 / 2) fun _ => ⟨le_refl 0, by norm_num, by norm_num⟩
  have hzero : empAvg (boxInd fun _ => Set.Ico (0 : ℝ) (1 / 2)) (window vanDerCorput 2) =
      fun _ => 0 := by
    funext N
    unfold empAvg
    rw [Finset.sum_eq_zero fun t _ => ?_, zero_div]
    classical
    rw [boxInd_eq_ite]
    split_ifs with hall
    · have h0 : vanDerCorput t < 1 / 2 := (hall 0).2
      have h1 : vanDerCorput (t + 1) < 1 / 2 := (hall 1).2
      exact absurd h0 ((vanDerCorput_succ_lt_half_iff t).1 h1)
    · rfl
  rw [hzero] at hlim
  have := tendsto_nhds_unique tendsto_const_nhds hlim
  rw [Fin.prod_univ_two] at this
  norm_num at this

/-- **The van der Corput sequence is not CUD** (post #3: "using Sobol sequences would fail
this"). -/
theorem not_isCUD_vanDerCorput : ¬ IsCUD vanDerCorput :=
  fun h => not_isUD_window_two_vanDerCorput (h 2)

/-- `φ(k) > 0` for `k ≥ 1`. -/
theorem vanDerCorput_pos {k : ℕ} (hk : 0 < k) : 0 < vanDerCorput k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [vanDerCorput_eq k]
    have h0 := (vanDerCorput_mem_Ico (k / 2)).1
    rcases Nat.mod_two_eq_zero_or_one k with hm | hm
    · have hpos := ih (k / 2) (Nat.div_lt_self hk (by norm_num)) (by omega)
      rw [hm, Nat.cast_zero]
      linarith
    · rw [hm, Nat.cast_one]
      linarith

/-- The two-state chain with rows `(1/2, 1/2)` and `(1, 0)`: from state `0` stay or move with
probability `1/2`; from state `1` always return to `0`. -/
noncomputable def twoState : Fin 2 → Fin 2 → ℝ := fun i j =>
  if (i : ℕ) = 0 then 1 / 2 else if (j : ℕ) = 0 then 1 else 0

/-- `twoState` is stochastic. -/
theorem isStochastic_twoState : IsStochastic twoState := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · unfold twoState
    split_ifs <;> norm_num
  · rw [Fin.sum_univ_two]
    fin_cases i <;> norm_num [twoState]

/-- The stationary distribution of `twoState` is `(2/3, 1/3)`. -/
theorem twoState_stationary (j : Fin 2) :
    ∑ i, (![2 / 3, 1 / 3] : Fin 2 → ℝ) i * twoState i j = (![2 / 3, 1 / 3] : Fin 2 → ℝ) j := by
  rw [Fin.sum_univ_two]
  fin_cases j <;> norm_num [twoState]

/-- From state `1` every uniform in `(0,1]` leads to state `0`. -/
theorem step_twoState_one {u : ℝ} (hu : u ∈ Set.Ioc (0 : ℝ) 1) : step twoState 1 u = 0 :=
  (step_eq_iff isStochastic_twoState 1 0 hu).2 (by
    unfold cumProb
    rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_two]
    norm_num [twoState]
    exact ⟨hu.1, hu.2⟩)

/-- From state `0` a uniform in `(0, 1/2]` leads to state `0`. -/
theorem step_twoState_zero_low {u : ℝ} (hu : u ∈ Set.Ioc (0 : ℝ) (1 / 2)) :
    step twoState 0 u = 0 :=
  (step_eq_iff isStochastic_twoState 0 0 ⟨hu.1, by linarith [hu.2]⟩).2 (by
    unfold cumProb
    rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_two]
    norm_num [twoState]
    exact ⟨hu.1, hu.2⟩)

/-- From state `0` a uniform in `(1/2, 1]` leads to state `1`. -/
theorem step_twoState_zero_high {u : ℝ} (hu : u ∈ Set.Ioc (1 / 2 : ℝ) 1) :
    step twoState 0 u = 1 :=
  (step_eq_iff isStochastic_twoState 0 1 ⟨by linarith [hu.1], hu.2⟩).2 (by
    unfold cumProb
    rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_two]
    norm_num [twoState]
    exact ⟨hu.1, hu.2⟩)

/-- **The van der Corput–driven path alternates.** From any start, the path of `twoState`
driven by `φ` is in state `1` at even times and in state `0` at odd times, from time `3` on. -/
theorem drivenPath_twoState_vanDerCorput (x₀ : Fin 2) (t : ℕ) :
    drivenPath twoState x₀ vanDerCorput (t + 3) = if (t + 3) % 2 = 0 then 1 else 0 := by
  induction t with
  | zero =>
    change step twoState (drivenPath twoState x₀ vanDerCorput 2) (vanDerCorput 2) = _
    have h2 : vanDerCorput 2 = 1 / 4 := vanDerCorput_one_two_three.2.1
    rw [h2]
    have hlow : (1 / 4 : ℝ) ∈ Set.Ioc 0 (1 / 2) := ⟨by norm_num, by norm_num⟩
    have hone : (1 / 4 : ℝ) ∈ Set.Ioc 0 1 := ⟨by norm_num, by norm_num⟩
    have hval : (if (0 + 3) % 2 = 0 then (1 : Fin 2) else 0) = 0 := rfl
    rw [hval]
    generalize drivenPath twoState x₀ vanDerCorput 2 = s
    fin_cases s
    · exact step_twoState_zero_low hlow
    · exact step_twoState_one hone
  | succ t ih =>
    change step twoState (drivenPath twoState x₀ vanDerCorput (t + 3)) (vanDerCorput (t + 3)) = _
    rw [ih]
    have hpos := vanDerCorput_pos (show 0 < t + 3 by omega)
    have hlt := (vanDerCorput_mem_Ico (t + 3)).2
    rcases Nat.mod_two_eq_zero_or_one (t + 3) with hm | hm
    · have h1 : (t + 1 + 3) % 2 = 1 := by omega
      simp only [hm, h1, ↓reduceIte, one_ne_zero]
      exact step_twoState_one ⟨hpos, hlt.le⟩
    · have h1 : (t + 1 + 3) % 2 = 0 := by omega
      simp only [hm, h1, ↓reduceIte, one_ne_zero]
      refine step_twoState_zero_high ⟨?_, hlt.le⟩
      have hodd : ¬ vanDerCorput (t + 3) < 1 / 2 := by
        rw [vanDerCorput_lt_half_iff]
        omega
      have h2 : t + 3 = 2 * ((t + 3) / 2) + 1 := by omega
      have hq : 0 < vanDerCorput ((t + 3) / 2) := vanDerCorput_pos (by omega)
      rw [h2, vanDerCorput_two_mul_add_one]
      have h0 := vanDerCorput_two_mul_add ((t + 3) / 2) 0 (by norm_num)
      rw [add_zero, Nat.cast_zero, zero_div, zero_add] at h0
      rw [h0]
      linarith

/-- The number of even times below `T` is `⌊(T+1)/2⌋`. -/
theorem sum_range_even_indicator (T : ℕ) :
    (∑ t ∈ range T, if t % 2 = 0 then (1 : ℝ) else 0) = (((T + 1) / 2 : ℕ) : ℝ) := by
  induction T with
  | zero =>
    rw [Finset.sum_range_zero]
    norm_num
  | succ T ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.mod_two_eq_zero_or_one T with h | h
    · have e : (T + 1 + 1) / 2 = (T + 1) / 2 + 1 := by omega
      simp only [h, ↓reduceIte, e, Nat.cast_add, Nat.cast_one]
    · have e : (T + 1 + 1) / 2 = (T + 1) / 2 := by omega
      have h' : T % 2 ≠ 0 := by omega
      simp only [h', ↓reduceIte, e, add_zero]

/-- **Codes (a) "fails badly".** Driven by the van der Corput sequence, the frequency of state
`1` of `twoState` tends to `1/2`. -/
theorem tendsto_occFreq_twoState_vanDerCorput (x₀ : Fin 2) :
    Tendsto (fun T => (occCount (drivenPath twoState x₀ vanDerCorput) 1 T : ℝ) / T) atTop
      (𝓝 (1 / 2)) := by
  set x := drivenPath twoState x₀ vanDerCorput with hx
  set E : ℕ → ℝ := fun T => ∑ t ∈ range T, if t % 2 = 0 then (1 : ℝ) else 0 with hE
  -- the occupation count differs from the even count by at most `3`
  have hdiff : ∀ T, |(occCount x 1 T : ℝ) - E T| ≤ 3 := by
    intro T
    rw [occCount_eq_sum, hE]
    dsimp only
    rw [← Finset.sum_sub_distrib]
    set dlt : ℕ → ℝ := fun t => (if x t = 1 then (1 : ℝ) else 0) - if t % 2 = 0 then 1 else 0
    have hvan : ∀ t, 3 ≤ t → dlt t = 0 := by
      intro t ht
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 3 := ⟨t - 3, by omega⟩
      change (if x (s + 3) = 1 then (1 : ℝ) else 0) - (if (s + 3) % 2 = 0 then 1 else 0) = 0
      rw [hx, drivenPath_twoState_vanDerCorput]
      rcases Nat.mod_two_eq_zero_or_one (s + 3) with hm | hm
      · simp only [hm, ↓reduceIte, sub_self]
      · simp only [hm, ↓reduceIte, one_ne_zero, zero_ne_one, sub_self]
    have hb : ∀ t, |dlt t| ≤ 1 := fun t => by
      change |(if x t = 1 then (1 : ℝ) else 0) - if t % 2 = 0 then 1 else 0| ≤ 1
      split_ifs <;> norm_num
    calc |∑ t ∈ range T, dlt t| ≤ ∑ t ∈ range T, |dlt t| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ range T, if t < 3 then (1 : ℝ) else 0 := Finset.sum_le_sum fun t _ => by
          split_ifs with h
          · exact hb t
          · rw [hvan t (not_lt.1 h), abs_zero]
      _ ≤ ∑ t ∈ range 3, (1 : ℝ) := by
          rw [← Finset.sum_filter]
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun t ht => ?_) fun _ _ _ => zero_le_one
          rw [Finset.mem_filter] at ht
          exact Finset.mem_range.2 ht.2
      _ = 3 := by norm_num
  have hEb : ∀ T : ℕ, 0 < T → |E T / T - 1 / 2| ≤ 1 / T := by
    intro T hT
    have hTR : (0 : ℝ) < T := by exact_mod_cast hT
    rw [hE]
    dsimp only
    rw [sum_range_even_indicator]
    have h1 : (T : ℝ) ≤ 2 * (((T + 1) / 2 : ℕ) : ℝ) := by
      have : T ≤ 2 * ((T + 1) / 2) := by omega
      exact_mod_cast this
    have h2 : 2 * (((T + 1) / 2 : ℕ) : ℝ) ≤ T + 1 := by
      have : 2 * ((T + 1) / 2) ≤ T + 1 := by omega
      exact_mod_cast this
    set c : ℝ := (((T + 1) / 2 : ℕ) : ℝ) with hc
    have key : c / T - 1 / 2 = (2 * c - T) / (2 * T) := by
      rw [div_sub_div _ _ hTR.ne' two_ne_zero]
      congr 1 <;> ring
    rw [key, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * T),
      div_le_div_iff₀ (by positivity) hTR]
    have hab : |2 * c - T| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    nlinarith [abs_nonneg (2 * c - T)]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h4 : Tendsto (fun T : ℕ => 4 / (T : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ h4
  filter_upwards [eventually_gt_atTop 0] with T hT
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  rw [Real.norm_eq_abs]
  have hd : |(occCount x 1 T : ℝ) / T - E T / T| ≤ 3 / T := by
    rw [← sub_div, abs_div, abs_of_pos hTR]
    exact div_le_div_of_nonneg_right (hdiff T) hTR.le
  calc |(occCount x 1 T : ℝ) / T - 1 / 2|
      ≤ |(occCount x 1 T : ℝ) / T - E T / T| + |E T / T - 1 / 2| := abs_sub_le _ _ _
    _ ≤ 3 / T + 1 / T := add_le_add hd (hEb T hT)
    _ = 4 / T := by ring

/-- **Counterexample (post #3 / codes (a)).** Driven by the van der Corput sequence (the
one-dimensional Sobol sequence), the occupation frequency of state `1` of `twoState` does not
converge to its stationary probability `π₁ = 1/3`. -/
theorem not_tendsto_occFreq_twoState_vanDerCorput (x₀ : Fin 2) :
    ¬ Tendsto (fun T => (occCount (drivenPath twoState x₀ vanDerCorput) 1 T : ℝ) / T) atTop
      (𝓝 (1 / 3)) := fun h => by
  have := tendsto_nhds_unique h (tendsto_occFreq_twoState_vanDerCorput x₀)
  norm_num at this

/-- **Contrast: CUD driving is consistent for `twoState`** (Chentsov's theorem, coupling form;
column `0` is bounded below by `1/2`): the frequency of state `1` tends to `π₁ = 1/3`. -/
theorem tendsto_occFreq_twoState_of_isCUD {u : ℕ → ℝ} (hu : IsCUD u) (x₀ : Fin 2) :
    Tendsto (fun T => (occCount (drivenPath twoState x₀ u) 1 T : ℝ) / T) atTop (𝓝 (1 / 3)) := by
  have h := tendsto_occFreq_of_isCUD_of_col_pos isStochastic_twoState hu 0 rfl
    (c := 1 / 2) (by norm_num) (fun i => by fin_cases i <;> norm_num [twoState])
    (π := ![2 / 3, 1 / 3]) twoState_stationary (fun i => by fin_cases i <;> norm_num)
    (by rw [Fin.sum_univ_two]; norm_num) x₀ 1
  exact h

end RQMCMarkov.MarkovDriving

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # An entropy lemma: a stationary chain driven by i.i.d. inputs is independent of them

The general (coupling-free) Chentsov theorem (`ChentsovGeneral`) reduces to a statement about
finite distributions. Let `X` and `C` be finite, `F : X → C → X`, and `c` a law on `C`. Suppose
`q m` is a joint law of `(X₀, Z₀, …, Z_{m-1})` for every `m`, with `Z₀, …, Z_{m-1}` i.i.d. `c`,
with consistent marginals, and **stationary** for `X_{t+1} = F X_t Z_t`: the law of
`(X₁, Z₁, …, Z_m)` is again `q m`. No independence of `X₀` from the `Z`'s is assumed (in the
application `X₀` may depend on the "future" inputs). Then `X₀` **is** independent of `Z₀`
(`chentsov_entropy_core`), so its law `ρ` is stationary for the Markov matrix
`P x j = c {a : F x a = j}` (`chentsov_entropy_stationary`).

**Proof (information theory).** Let `I m` be the mutual information of `X₀` and
`(Z₀, …, Z_{m-1})`. Data processing for the map `(X₀, Z₀) ↦ X₁ = F X₀ Z₀`, stationarity, and
the chain rule (with `Z₀` independent of `(Z₁, …)`) give `I (m+1) ≥ I m + I 1`, so
`I m ≥ m · I 1`; but `I m ≤ H(X₀) < ∞`. Hence `I 1 = 0`, i.e. `X₀` and `Z₀` are independent
(Gibbs' inequality with its equality case). The entropy is finite because `X` is finite; this is
where the finite state space is used.

**Results.**
* `sub_le_mul_log_div`, `sub_lt_mul_log_div`: `a - b ≤ a log (a/b)`, strictly unless `a = b`.
* `eq_of_klSum_le`: Gibbs' inequality, equality case.
* `logSum_le`: the log-sum inequality; `klSum_pushSum_le`: data processing for the
  Kullback–Leibler sum `klSum p q = ∑ p log (p/q)` under a map.
* `chentsov_entropy_core`, `chentsov_entropy_stationary`.
-/

namespace RQMCMarkov.MarkovDriving

open Finset Real

/-- The Kullback–Leibler sum `∑ₓ p x log (p x / q x)` (with `log 0 = 0`). -/
noncomputable def klSum {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ x, p x * Real.log (p x / q x)

/-- **Per-term Gibbs inequality:** `a - b ≤ a log (a/b)` for `a, b ≥ 0` with `b = 0 → a = 0`. -/
theorem sub_le_mul_log_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b = 0 → a = 0) :
    a - b ≤ a * Real.log (a / b) := by
  rcases ha.eq_or_lt with h0 | hapos
  · rw [← h0, zero_mul]
    linarith
  have hbpos : 0 < b := lt_of_le_of_ne hb fun h => hapos.ne' (hab h.symm)
  have hl := Real.log_le_sub_one_of_pos (div_pos hbpos hapos)
  have hinv : a / b = (b / a)⁻¹ := (inv_div b a).symm
  rw [hinv, Real.log_inv]
  have : a * (b / a) = b := mul_div_cancel₀ b hapos.ne'
  nlinarith

/-- **Strict per-term Gibbs inequality:** `a - b < a log (a/b)` when moreover `a ≠ b`. -/
theorem sub_lt_mul_log_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b = 0 → a = 0)
    (hne : a ≠ b) : a - b < a * Real.log (a / b) := by
  rcases ha.eq_or_lt with h0 | hapos
  · rw [← h0, zero_mul]
    have : 0 < b := lt_of_le_of_ne hb (fun h => hne (h0.symm.trans h))
    linarith
  have hbpos : 0 < b := lt_of_le_of_ne hb fun h => hapos.ne' (hab h.symm)
  have hne' : b / a ≠ 1 := fun h => hne ((div_eq_one_iff_eq hapos.ne').1 h).symm
  have hl := Real.log_lt_sub_one_of_pos (div_pos hbpos hapos) hne'
  have hinv : a / b = (b / a)⁻¹ := (inv_div b a).symm
  rw [hinv, Real.log_inv]
  have : a * (b / a) = b := mul_div_cancel₀ b hapos.ne'
  nlinarith

/-- **Gibbs' inequality:** `∑ p - ∑ q ≤ klSum p q`. -/
theorem sum_sub_sum_le_klSum {α : Type*} [Fintype α] {p q : α → ℝ} (hp : ∀ x, 0 ≤ p x)
    (hq : ∀ x, 0 ≤ q x) (hpq : ∀ x, q x = 0 → p x = 0) : ∑ x, p x - ∑ x, q x ≤ klSum p q := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun x _ => sub_le_mul_log_div (hp x) (hq x) (hpq x)

/-- **Gibbs' inequality, equality case:** if `∑ p = ∑ q` and `klSum p q ≤ 0` then `p = q`. -/
theorem eq_of_klSum_le {α : Type*} [Fintype α] {p q : α → ℝ} (hp : ∀ x, 0 ≤ p x)
    (hq : ∀ x, 0 ≤ q x) (hpq : ∀ x, q x = 0 → p x = 0) (hsum : ∑ x, p x = ∑ x, q x)
    (hkl : klSum p q ≤ 0) : p = q := by
  funext x
  by_contra hne
  have hlt : ∑ y, (p y - q y) < klSum p q := by
    unfold klSum
    exact Finset.sum_lt_sum (fun y _ => sub_le_mul_log_div (hp y) (hq y) (hpq y))
      ⟨x, Finset.mem_univ x, sub_lt_mul_log_div (hp x) (hq x) (hpq x) hne⟩
  rw [Finset.sum_sub_distrib, hsum, sub_self] at hlt
  linarith

/-- **The log-sum inequality:** `(∑ a) log (∑ a / ∑ b) ≤ ∑ a log (a/b)` for `a, b ≥ 0` with
`b = 0 → a = 0`. -/
theorem logSum_le {ι : Type*} (s : Finset ι) {a b : ι → ℝ} (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, 0 ≤ b i) (hab : ∀ i, b i = 0 → a i = 0) :
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / ∑ i ∈ s, b i) ≤
      ∑ i ∈ s, a i * Real.log (a i / b i) := by
  set A := ∑ i ∈ s, a i with hA
  set B := ∑ i ∈ s, b i with hB
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => ha i
  rcases hA0.eq_or_lt with hA0' | hApos
  · have hai : ∀ i ∈ s, a i = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => ha i).1 hA0'.symm
    rw [← hA0', zero_mul, Finset.sum_eq_zero fun i hi => by rw [hai i hi, zero_mul]]
  have hBpos : 0 < B := by
    rcases (Finset.sum_nonneg fun i (_ : i ∈ s) => hb i).eq_or_lt with h | h
    · have hbi : ∀ i ∈ s, b i = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hb i).1 h.symm
      have : A = 0 := Finset.sum_eq_zero fun i hi => hab i (hbi i hi)
      linarith
    · exact h
  set κ := A / B with hκ
  have hκpos : 0 < κ := div_pos hApos hBpos
  have hterm : ∀ i ∈ s, a i - b i * κ ≤ a i * Real.log (a i / b i) - a i * Real.log κ := by
    intro i _
    have h := sub_le_mul_log_div (ha i) (mul_nonneg (hb i) hκpos.le) fun h0 =>
      hab i ((mul_eq_zero.1 h0).resolve_right hκpos.ne')
    rcases (ha i).eq_or_lt with h0 | hpos
    · rw [← h0, zero_mul, zero_mul, sub_zero]
      rw [← h0] at h
      linarith
    · have hbpos : 0 < b i := lt_of_le_of_ne (hb i) fun h' => hpos.ne' (hab i h'.symm)
      have hlog : Real.log (a i / (b i * κ)) = Real.log (a i / b i) - Real.log κ := by
        rw [← div_div, Real.log_div (div_pos hpos hbpos).ne' hκpos.ne']
      rw [hlog, mul_sub] at h
      exact h
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul] at hsum
  rw [← hA, ← hB, hκ, mul_div_cancel₀ A hBpos.ne', sub_self] at hsum
  linarith

/-- The push-forward of a function `p : α → ℝ` along `φ : α → β`: fibre sums. -/
noncomputable def pushSum {α β : Type*} [Fintype α] [DecidableEq β] (φ : α → β) (p : α → ℝ)
    (y : β) : ℝ :=
  ∑ x ∈ univ.filter (fun x => φ x = y), p x

/-- **Data processing** for the Kullback–Leibler sum: pushing both arguments forward along a
map can only decrease it. -/
theorem klSum_pushSum_le {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (φ : α → β)
    {p q : α → ℝ} (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) (hpq : ∀ x, q x = 0 → p x = 0) :
    klSum (pushSum φ p) (pushSum φ q) ≤ klSum p q := by
  unfold klSum
  rw [← Finset.sum_fiberwise Finset.univ φ fun x => p x * Real.log (p x / q x)]
  exact Finset.sum_le_sum fun y _ => logSum_le _ hp hq hpq

/-- Sums over `Fin (L+1) → C` split as a sum over the head and the tail. -/
theorem sum_fin_succ_fun {C : Type*} [Fintype C] {L : ℕ}
    (f : (Fin (L + 1) → C) → ℝ) : ∑ z, f z = ∑ a, ∑ z', f (Fin.cons a z') := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => C) _ _ fun _ => rfl).symm

/-- The value of a sum over `Fin 0 → C`. -/
theorem sum_fin_zero_fun {C : Type*} [Fintype C] (f : (Fin 0 → C) → ℝ) :
    ∑ z, f z = f Fin.elim0 := by
  rw [Fintype.sum_unique]
  exact congrArg f (Subsingleton.elim _ _)

variable {X C : Type*} [Fintype X] [DecidableEq X] [Fintype C]

/-- **The entropy core of Chentsov's theorem.** Let `q m x z` be a joint law of `X₀ = x` and the
inputs `(Z₀, …, Z_{m-1}) = z`, whose input marginal is the i.i.d. product of `c`, whose `X₀`
marginal is `ρ` (a probability vector), whose `(X₀, Z₀)` marginal is `r`, and which is
stationary for `X₁ = F X₀ Z₀`. Then `X₀` and `Z₀` are independent: `r x a = ρ x · c a`. -/
theorem chentsov_entropy_core (F : X → C → X) (c : C → ℝ) (ρ : X → ℝ) (r : X → C → ℝ)
    (q : (m : ℕ) → X → (Fin m → C) → ℝ) (hq0 : ∀ m x z, 0 ≤ q m x z)
    (hZ : ∀ m z, ∑ x, q m x z = ∏ k, c (z k)) (hX : ∀ m x, ∑ z, q m x z = ρ x)
    (hr : ∀ L x a, ∑ z', q (L + 1) x (Fin.cons a z') = r x a)
    (hstat : ∀ L j z', ∑ x, ∑ a, (if F x a = j then q (L + 1) x (Fin.cons a z') else 0) =
      q L j z')
    (hρ1 : ∑ x, ρ x = 1) (x : X) (a : C) : r x a = ρ x * c a := by
  classical
  -- basic facts
  have hr0 : ∀ x a, 0 ≤ r x a := fun x a => by
    rw [← hr 0]
    exact Finset.sum_nonneg fun _ _ => hq0 _ _ _
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => by
    rw [← hX 0]
    exact Finset.sum_nonneg fun _ _ => hq0 _ _ _
  have hrX : ∀ x, ∑ a, r x a = ρ x := fun x => by
    rw [← hX 1 x, sum_fin_succ_fun]
    exact Finset.sum_congr rfl fun a _ => (hr 0 x a).symm
  have hrC : ∀ a, ∑ x, r x a = c a := fun a => by
    have h := hZ 1 (Fin.cons a Fin.elim0)
    rw [Fin.prod_univ_one, Fin.cons_zero] at h
    rw [← h]
    exact Finset.sum_congr rfl fun x _ => by rw [← hr 0 x a, sum_fin_zero_fun]
  have hc0 : ∀ a, 0 ≤ c a := fun a => by
    rw [← hrC a]
    exact Finset.sum_nonneg fun x _ => hr0 x a
  have hc1 : ∑ a, c a = 1 := by
    simp only [← hrC]
    rw [Finset.sum_comm]
    simp only [hrX]
    exact hρ1
  have hrle : ∀ x a, r x a ≤ ρ x ∧ r x a ≤ c a := fun x a =>
    ⟨(hrX x) ▸ Finset.single_le_sum (fun a _ => hr0 x a) (Finset.mem_univ a),
      (hrC a) ▸ Finset.single_le_sum (fun x _ => hr0 x a) (Finset.mem_univ x)⟩
  have hqle : ∀ m x z, q m x z ≤ ∏ k, c (z k) := fun m x z =>
    (hZ m z) ▸ Finset.single_le_sum (fun x _ => hq0 m x z) (Finset.mem_univ x)
  have hqr : ∀ L x a z', q (L + 1) x (Fin.cons a z') ≤ r x a := fun L x a z' =>
    (hr L x a) ▸ Finset.single_le_sum (fun z _ => hq0 (L + 1) x (Fin.cons a z))
      (Finset.mem_univ z')
  have hpushr : ∀ j, ∑ x, ∑ a, (if F x a = j then r x a else 0) = ρ j := fun j => by
    rw [← hX 0 j, sum_fin_zero_fun, ← hstat 0 j Fin.elim0]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun a _ => ?_
    rw [← hr 0 x a, sum_fin_zero_fun]
  -- the mutual informations
  set I : ℕ → ℝ := fun m => ∑ x, ∑ z, q m x z * Real.log (q m x z / (ρ x * ∏ k, c (z k)))
    with hI
  set I1 : ℝ := ∑ x, ∑ a, r x a * Real.log (r x a / (ρ x * c a)) with hI1
  -- `I 0 = 0`
  have hI0 : I 0 = 0 := by
    rw [hI]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [sum_fin_zero_fun, Fin.prod_univ_zero, mul_one]
    have hq00 : q 0 x Fin.elim0 = ρ x := by rw [← hX 0 x, sum_fin_zero_fun]
    rw [hq00]
    rcases (hρ0 x).eq_or_lt with h | h
    · rw [← h, zero_mul]
    · rw [div_self h.ne', Real.log_one, mul_zero]
  -- `I m ≤ H(ρ)`
  have hIle : ∀ m, I m ≤ ∑ x, ρ x * Real.log (1 / ρ x) := by
    intro m
    rw [hI]
    refine Finset.sum_le_sum fun x _ => ?_
    refine (Finset.sum_le_sum fun z _ => ?_).trans_eq
      (by rw [← Finset.sum_mul, hX m x] : ∑ z, q m x z * Real.log (1 / ρ x) = _)
    rcases (hq0 m x z).eq_or_lt with h | h
    · rw [← h, zero_mul, zero_mul]
    · have hcz : 0 < ∏ k, c (z k) := lt_of_lt_of_le h (hqle m x z)
      have hρx : 0 < ρ x := by
        rcases (hρ0 x).eq_or_lt with h' | h'
        · exfalso
          have : q m x z ≤ ρ x := (hX m x) ▸ Finset.single_le_sum (fun z _ => hq0 m x z)
            (Finset.mem_univ z)
          linarith
        · exact h'
      refine mul_le_mul_of_nonneg_left (Real.log_le_log (div_pos h (mul_pos hρx hcz)) ?_) h.le
      rw [div_le_div_iff₀ (mul_pos hρx hcz) hρx]
      nlinarith [hqle m x z]
  -- `I 1 ≥ 0`
  have hI1nn : 0 ≤ I1 := by
    have h := sum_sub_sum_le_klSum (α := X × C) (p := fun xa => r xa.1 xa.2)
      (q := fun xa => ρ xa.1 * c xa.2) (fun xa => hr0 _ _)
      (fun xa => mul_nonneg (hρ0 _) (hc0 _)) fun xa h0 => by
        rcases mul_eq_zero.1 h0 with h | h
        · exact le_antisymm (h ▸ (hrle _ _).1) (hr0 _ _)
        · exact le_antisymm (h ▸ (hrle _ _).2) (hr0 _ _)
    unfold klSum at h
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type] at h
    simp only [hrX, ← Finset.mul_sum, hc1, mul_one, hρ1, sub_self] at h
    exact h
  -- superadditivity `I (L+1) ≥ I L + I 1`
  have hsuper : ∀ L, I L + I1 ≤ I (L + 1) := by
    intro L
    -- split each term of `I (L+1)`
    have hsplit : I (L + 1) = (∑ x, ∑ a, ∑ z', q (L + 1) x (Fin.cons a z') *
        Real.log (q (L + 1) x (Fin.cons a z') / (r x a * ∏ k, c (z' k)))) + I1 := by
      rw [hI, hI1]
      dsimp only
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [sum_fin_succ_fun, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      have e : r x a * Real.log (r x a / (ρ x * c a)) = ∑ z', q (L + 1) x (Fin.cons a z') *
          Real.log (r x a / (ρ x * c a)) := by rw [← Finset.sum_mul, hr L x a]
      rw [e, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun z' _ => ?_
      rw [Fin.prod_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ]
      set Q := q (L + 1) x (Fin.cons a z')
      rcases (hq0 (L + 1) x (Fin.cons a z')).eq_or_lt with h | h
      · have hQ : Q = 0 := h.symm
        rw [hQ, zero_mul, zero_mul, zero_mul, add_zero]
      · have hR : 0 < r x a := lt_of_lt_of_le h (hqr L x a z')
        have hρx : 0 < ρ x := lt_of_lt_of_le hR (hrle x a).1
        have hca : 0 < c a := lt_of_lt_of_le hR (hrle x a).2
        have hcz : 0 < ∏ k, c (z' k) := by
          have h1 := hqle (L + 1) x (Fin.cons a z')
          rw [Fin.prod_univ_succ, Fin.cons_zero] at h1
          simp only [Fin.cons_succ] at h1
          exact pos_of_mul_pos_right (lt_of_lt_of_le h h1) (hc0 a)
        rw [← mul_add, Real.log_div h.ne' (by positivity), Real.log_div h.ne' (by positivity),
          Real.log_div hR.ne' (by positivity), Real.log_mul hρx.ne' (by positivity),
          Real.log_mul hca.ne' hcz.ne', Real.log_mul hR.ne' hcz.ne',
          Real.log_mul hρx.ne' hca.ne']
        ring
    rw [hsplit]
    -- data processing for `((x, a), z') ↦ (F x a, z')`
    have hdp := klSum_pushSum_le (α := (X × C) × (Fin L → C)) (β := X × (Fin L → C))
      (fun p => (F p.1.1 p.1.2, p.2)) (p := fun p => q (L + 1) p.1.1 (Fin.cons p.1.2 p.2))
      (q := fun p => r p.1.1 p.1.2 * ∏ k, c (p.2 k)) (fun p => hq0 _ _ _)
      (fun p => mul_nonneg (hr0 _ _) (Finset.prod_nonneg fun k _ => hc0 _)) fun p h0 => by
        rcases mul_eq_zero.1 h0 with h | h
        · exact le_antisymm (h ▸ hqr L _ _ _) (hq0 _ _ _)
        · have h1 := hqle (L + 1) p.1.1 (Fin.cons p.1.2 p.2)
          rw [Fin.prod_univ_succ, Fin.cons_zero] at h1
          simp only [Fin.cons_succ] at h1
          rw [h, mul_zero] at h1
          exact le_antisymm h1 (hq0 _ _ _)
    have hpush1 : ∀ j z', pushSum (fun p : (X × C) × (Fin L → C) => (F p.1.1 p.1.2, p.2))
        (fun p => q (L + 1) p.1.1 (Fin.cons p.1.2 p.2)) (j, z') = q L j z' := by
      intro j z'
      unfold pushSum
      rw [Finset.sum_filter, ← hstat L j z', Fintype.sum_prod_type, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_eq_single z']
      · simp only [Prod.mk.injEq, and_true]
      · intro z'' _ hz''
        simp only [Prod.mk.injEq, hz'', and_false, ↓reduceIte]
      · exact fun h => absurd (Finset.mem_univ _) h
    have hpush2 : ∀ j z', pushSum (fun p : (X × C) × (Fin L → C) => (F p.1.1 p.1.2, p.2))
        (fun p => r p.1.1 p.1.2 * ∏ k, c (p.2 k)) (j, z') = ρ j * ∏ k, c (z' k) := by
      intro j z'
      unfold pushSum
      rw [Finset.sum_filter, ← hpushr j, Finset.sum_mul, Fintype.sum_prod_type,
        Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_eq_single z']
      · by_cases hF : F x a = j
        · simp only [hF, ↓reduceIte]
        · simp only [Prod.mk.injEq, hF, false_and, ↓reduceIte, zero_mul]
      · intro z'' _ hz''
        simp only [Prod.mk.injEq, hz'', and_false, ↓reduceIte]
      · exact fun h => absurd (Finset.mem_univ _) h
    have hleft : klSum (pushSum (fun p : (X × C) × (Fin L → C) => (F p.1.1 p.1.2, p.2))
        (fun p => q (L + 1) p.1.1 (Fin.cons p.1.2 p.2)))
        (pushSum (fun p : (X × C) × (Fin L → C) => (F p.1.1 p.1.2, p.2))
          (fun p => r p.1.1 p.1.2 * ∏ k, c (p.2 k))) = I L := by
      unfold klSum
      rw [Fintype.sum_prod_type, hI]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun z' _ => by
        rw [hpush1, hpush2]
    have hright : klSum (fun p : (X × C) × (Fin L → C) => q (L + 1) p.1.1 (Fin.cons p.1.2 p.2))
        (fun p => r p.1.1 p.1.2 * ∏ k, c (p.2 k)) = ∑ x, ∑ a, ∑ z', q (L + 1) x (Fin.cons a z') *
          Real.log (q (L + 1) x (Fin.cons a z') / (r x a * ∏ k, c (z' k))) := by
      unfold klSum
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    rw [hleft, hright] at hdp
    linarith
  -- conclude `I 1 = 0`
  have hlin : ∀ m : ℕ, (m : ℝ) * I1 ≤ I m := by
    intro m
    induction m with
    | zero => rw [Nat.cast_zero, zero_mul, hI0]
    | succ m ih =>
      have := hsuper m
      push_cast
      linarith
  have hI1zero : I1 ≤ 0 := by
    by_contra hpos
    push Not at hpos
    obtain ⟨m, hm⟩ := exists_nat_gt ((∑ x, ρ x * Real.log (1 / ρ x)) / I1)
    have h1 := hlin m
    have h2 := hIle m
    rw [div_lt_iff₀ hpos] at hm
    linarith
  -- Gibbs equality
  have heq := eq_of_klSum_le (α := X × C) (p := fun xa => r xa.1 xa.2)
    (q := fun xa => ρ xa.1 * c xa.2) (fun xa => hr0 _ _) (fun xa => mul_nonneg (hρ0 _) (hc0 _))
    (fun xa h0 => by
      rcases mul_eq_zero.1 h0 with h | h
      · exact le_antisymm (h ▸ (hrle _ _).1) (hr0 _ _)
      · exact le_antisymm (h ▸ (hrle _ _).2) (hr0 _ _))
    (by
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      simp only [hrX, ← Finset.mul_sum, hc1, mul_one, hρ1])
    (by
      unfold klSum
      rw [Fintype.sum_prod_type]
      exact hI1zero)
  exact congrFun heq (x, a)

/-- **Consequence:** the law `ρ` of `X₀` is stationary for `P x j = ∑_{a : F x a = j} c a`. -/
theorem chentsov_entropy_stationary (F : X → C → X) (c : C → ℝ) (ρ : X → ℝ) (r : X → C → ℝ)
    (q : (m : ℕ) → X → (Fin m → C) → ℝ) (hq0 : ∀ m x z, 0 ≤ q m x z)
    (hZ : ∀ m z, ∑ x, q m x z = ∏ k, c (z k)) (hX : ∀ m x, ∑ z, q m x z = ρ x)
    (hr : ∀ L x a, ∑ z', q (L + 1) x (Fin.cons a z') = r x a)
    (hstat : ∀ L j z', ∑ x, ∑ a, (if F x a = j then q (L + 1) x (Fin.cons a z') else 0) =
      q L j z')
    (hρ1 : ∑ x, ρ x = 1) (j : X) :
    ∑ x, ρ x * (∑ a, if F x a = j then c a else 0) = ρ j := by
  have hind := chentsov_entropy_core F c ρ r q hq0 hZ hX hr hstat hρ1
  rw [← hX 0 j, sum_fin_zero_fun, ← hstat 0 j Fin.elim0]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hra : q (0 + 1) x (Fin.cons a Fin.elim0) = r x a := by
    rw [← hr 0 x a, sum_fin_zero_fun]
  rw [hra, hind x a]
  split_ifs <;> simp only [mul_zero]

end RQMCMarkov.MarkovDriving

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # Chentsov's theorem in general: CUD driving is consistent for every finite chain

Post #3: "if the QMC method we use is 'completely uniformly distributed' … then the generated
Markov simulations are consistent for the empirical state frequencies and time averages
(Chentsov, 1967)". `ChentsovConsistency` proves this under a coupling hypothesis. Here we remove
it: **for every stochastic matrix `P` on a finite state space with a unique stationary
distribution `π`** (e.g. every irreducible `P`, periodic or not), the path driven through the
inverse-CDF update by any CUD sequence has occupation frequencies converging to `π`
(`tendsto_occFreq_of_isCUD_general`) and time averages converging to `π(g)`
(`tendsto_timeAvg_of_isCUD_general`). In particular the chain `fourState`, which has no
coupling box, is consistent (`tendsto_occFreq_fourState_of_isCUD`). Uniqueness of `π` cannot be
dropped (`not_tendsto_occFreq_identity`). The full post #3 claim therefore holds for every
finite chain with a unique stationary distribution.

**Proof.** Write `Z_t = (step P i u_t)ᵢ` for the update map used at time `t` (a finite "cell" of
`u_t`), so `x_{t+1} = Z_t x_t`. For each pattern length `m`, the empirical joint frequencies of
`(x_t, Z_t, …, Z_{t+m-1})` lie in `[0,1]`. If `N_j(T)/T` did not tend to `π_j`, there would be an
ultrafilter `𝒰 ≥ atTop` along which it stays `ε` away; along `𝒰` all these frequencies
converge, to a family `q m` of joint laws. CUD gives that the `Z`-patterns have the i.i.d.
frequencies `∏ c(z_k)` (`isStepFn_pattern`); the time shift `t ↦ t+1` gives exact stationarity;
the marginals are consistent. The entropy lemma `chentsov_entropy_stationary` then shows that
the limit `ρ` of `N(T)/T` along `𝒰` is stationary for `P`, so `ρ = π`, a contradiction.

**Results.**
* `IsSide.inter`, `boxInd_inter`, `IsStepFn.mul`, `isStepFn_finset_prod`: products of step
  functions on the same coordinates are step functions.
* `cellInd`, `cellProb`, `isStepFn_cellInd`, `isStepFn_pattern`, `sum_cellProb_eq`: the cells of
  the inverse-CDF update and their probabilities `∑_{a : a i = j} c a = P i j`.
* `tendsto_occFreq_of_isCUD_general`, `tendsto_timeAvg_of_isCUD_general`: Chentsov's theorem.
* `tendsto_occFreq_fourState_of_isCUD`: the chain without coupling box is consistent.
-/

namespace RQMCMarkov.MarkovDriving

open Filter Topology Finset

/-- The intersection of two sides is a side. -/
theorem IsSide.inter {S S' : Set ℝ} {a b a' b' : ℝ} (h : IsSide S a b) (h' : IsSide S' a' b') :
    IsSide (S ∩ S') (max a a') (max (max a a') (min b b')) := by
  refine ⟨le_max_of_le_left h.1, le_max_left _ _,
    max_le (max_le (h.2.1.trans h.2.2.1) (h'.2.1.trans h'.2.2.1))
      ((min_le_left _ _).trans h.2.2.1), fun y hy => ?_, fun y hy => ?_⟩
  · have h1 : max a a' < y := hy.1
    have h2 : y < max (max a a') (min b b') := hy.2
    have h3 : y < min b b' := by
      rcases lt_max_iff.1 h2 with h4 | h4
      · exact absurd h1 (not_lt.2 h4.le)
      · exact h4
    exact ⟨h.2.2.2.1 ⟨(max_lt_iff.1 h1).1, (lt_min_iff.1 h3).1⟩,
      h'.2.2.2.1 ⟨(max_lt_iff.1 h1).2, (lt_min_iff.1 h3).2⟩⟩
  · have h1 := h.2.2.2.2 ⟨hy.1.1, hy.2⟩
    have h2 := h'.2.2.2.2 ⟨hy.1.2, hy.2⟩
    exact ⟨max_le h1.1 h2.1, (le_min h1.2 h2.2).trans (le_max_right _ _)⟩

/-- The product of two box indicators is the indicator of the intersection. -/
theorem boxInd_inter {d : ℕ} (S S' : Fin d → Set ℝ) (w : Fin d → ℝ) :
    boxInd S w * boxInd S' w = boxInd (fun k => S k ∩ S' k) w := by
  unfold boxInd
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Set.inter_indicator_one]
  rfl

/-- **Products of step functions** on the same coordinates are step functions. -/
theorem IsStepFn.mul {d : ℕ} {g h : (Fin d → ℝ) → ℝ} {L M : ℝ} (hg : IsStepFn d g L)
    (hh : IsStepFn d h M) : ∃ K, IsStepFn d (fun w => g w * h w) K := by
  obtain ⟨ι, hι, c, S, a, b, hS, hrep, -⟩ := hg
  obtain ⟨κ, hκ, c', S', a', b', hS', hrep', -⟩ := hh
  refine ⟨_, ι × κ, inferInstance, fun p => c p.1 * c' p.2,
    fun p k => S p.1 k ∩ S' p.2 k, fun p k => max (a p.1 k) (a' p.2 k),
    fun p k => max (max (a p.1 k) (a' p.2 k)) (min (b p.1 k) (b' p.2 k)),
    fun p k => (hS p.1 k).inter (hS' p.2 k), fun w hw => ?_, rfl⟩
  dsimp only
  rw [hrep w hw, hrep' w hw, Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  rw [← boxInd_inter]
  ring

/-- Finite products of step functions are step functions. -/
theorem isStepFn_finset_prod {d : ℕ} {α : Type*} (s : Finset α) {g : α → (Fin d → ℝ) → ℝ}
    (h : ∀ i ∈ s, ∃ L, IsStepFn d (g i) L) : ∃ L, IsStepFn d (fun w => ∏ i ∈ s, g i w) L := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, (isStepFn_const d 1).congr fun w _ => (Finset.prod_empty).symm⟩
  | insert i s hi ih =>
    obtain ⟨L, hL⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    obtain ⟨M, hM⟩ := h i (Finset.mem_insert_self i s)
    obtain ⟨K, hK⟩ := hM.mul hL
    exact ⟨K, hK.congr fun w _ => (Finset.prod_insert hi (f := fun j => g j w)).symm⟩

/-- Two step-function representations of the same function have the same integral (when some
uniformly distributed sequence exists in that dimension). -/
theorem IsStepFn.unique {d : ℕ} {x : ℕ → Fin d → ℝ} (hx : IsUD x) {g : (Fin d → ℝ) → ℝ}
    {L M : ℝ} (h1 : IsStepFn d g L) (h2 : IsStepFn d g M) : L = M :=
  tendsto_nhds_unique (tendsto_empAvg_of_isStepFn hx h1) (tendsto_empAvg_of_isStepFn hx h2)

variable {n : ℕ}

/-- The **cell** indicator: `1` if the inverse-CDF update map at `v` is `y`, i.e.
`step P i v = y i` for every state `i`. -/
noncomputable def cellInd (P : Fin n → Fin n → ℝ) (y : Fin n → Fin n) (v : ℝ) : ℝ :=
  if (fun i => step P i v) = y then 1 else 0

/-- The cell indicator is the product of the one-state indicators. -/
theorem cellInd_eq_prod (P : Fin n → Fin n → ℝ) (y : Fin n → Fin n) (v : ℝ) :
    cellInd P y v = ∏ i, (if step P i v = y i then (1 : ℝ) else 0) := by
  unfold cellInd
  by_cases h : (fun i => step P i v) = y
  · simp only [h, ↓reduceIte]
    exact (Finset.prod_eq_one fun i _ => by simp only [congrFun h i, ↓reduceIte]).symm
  · simp only [h, ↓reduceIte]
    have : ∃ i, step P i v ≠ y i := by
      by_contra hall
      push Not at hall
      exact h (funext hall)
    obtain ⟨i, hi⟩ := this
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [hi, ↓reduceIte])).symm

/-- Cells are step functions of one uniform. -/
theorem exists_isStepFn_cellInd {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (y : Fin n → Fin n) : ∃ L, IsStepFn 1 (fun v => cellInd P y (v 0)) L := by
  obtain ⟨L, hL⟩ := isStepFn_finset_prod (d := 1) (Finset.univ : Finset (Fin n))
    (g := fun i v => if step P i (v 0) = y i then (1 : ℝ) else 0)
    fun i _ => ⟨_, isStepFn_step hP i (y i)⟩
  exact ⟨L, hL.congr fun v _ => (cellInd_eq_prod P y (v 0)).symm⟩

/-- The probability of a cell. -/
noncomputable def cellProb {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (y : Fin n → Fin n) :
    ℝ :=
  Classical.choose (exists_isStepFn_cellInd hP y)

/-- The cell indicator is a step function with integral `cellProb`. -/
theorem isStepFn_cellInd {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (y : Fin n → Fin n) :
    IsStepFn 1 (fun v => cellInd P y (v 0)) (cellProb hP y) :=
  Classical.choose_spec (exists_isStepFn_cellInd hP y)

/-- **Patterns of cells** are step functions on windows, with the i.i.d. product
probabilities. -/
theorem isStepFn_pattern {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (m : ℕ)
    (z : Fin m → Fin n → Fin n) :
    IsStepFn m (fun w => ∏ k, cellInd P (z k) (w k)) (∏ k, cellProb hP (z k)) := by
  induction m with
  | zero =>
    refine ((isStepFn_const 0 1).congr fun w _ => (Fin.prod_univ_zero _).symm).of_eq ?_
    rw [Fin.prod_univ_zero]
  | succ m ih =>
    refine (((ih fun k => z (Fin.castSucc k)).append (isStepFn_cellInd hP (z (Fin.last m)))).congr
      fun w _ => ?_).of_eq ?_
    · rw [Fin.prod_univ_castSucc]
      rfl
    · rw [Fin.prod_univ_castSucc]

/-- The cells refine the inverse-CDF intervals: `∑_{a : a i = j} cellProb a = P i j`. -/
theorem sum_cellProb_eq {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) {x : ℕ → Fin 1 → ℝ}
    (hx : IsUD x) (i j : Fin n) :
    ∑ a : Fin n → Fin n, (if a i = j then cellProb hP a else 0) = P i j := by
  classical
  have h1 : IsStepFn 1 (fun v => ∑ a : Fin n → Fin n, if a i = j then cellInd P a (v 0) else 0)
      (∑ a : Fin n → Fin n, if a i = j then cellProb hP a else 0) := by
    refine isStepFn_finset_sum _ fun a _ => ?_
    by_cases ha : a i = j
    · simp only [ha, ↓reduceIte]
      exact isStepFn_cellInd hP a
    · simp only [ha, ↓reduceIte]
      exact isStepFn_const 1 0
  have h2 := (isStepFn_step hP i j).congr (g' := fun v =>
      ∑ a : Fin n → Fin n, if a i = j then cellInd P a (v 0) else 0) fun v _ => by
    unfold cellInd
    rw [Finset.sum_eq_single (fun k => step P k (v 0))]
    · simp only [↓reduceIte]
    · intro b _ hb
      simp only [Ne.symm hb, ↓reduceIte, ite_self]
    · exact fun h => absurd (Finset.mem_univ _) h
  exact h1.unique hx h2

/-- Sums over all patterns of indicators of a fixed sequence equal `1`. -/
theorem sum_prod_ite_eq_one {C : Type*} [Fintype C] [DecidableEq C] (Z : ℕ → C) (t m : ℕ) :
    ∑ z : Fin m → C, ∏ k : Fin m, (if Z (t + k) = z k then (1 : ℝ) else 0) = 1 := by
  have h := Finset.prod_univ_sum (fun _ : Fin m => (Finset.univ : Finset C))
    fun k y => if Z (t + k) = y then (1 : ℝ) else 0
  rw [Fintype.piFinset_univ] at h
  rw [← h]
  exact Finset.prod_eq_one fun k _ => by
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- Limits along an ultrafilter of `[0,1]`-valued sequences exist. -/
theorem exists_tendsto_ultrafilter (𝒰 : Ultrafilter ℕ) {g : ℕ → ℝ}
    (hg : ∀ N, g N ∈ Set.Icc (0 : ℝ) 1) : ∃ a ∈ Set.Icc (0 : ℝ) 1, Tendsto g 𝒰 (𝓝 a) := by
  obtain ⟨a, ha, hle⟩ := isCompact_Icc.ultrafilter_le_nhds (𝒰.map g)
    (by
      rw [Ultrafilter.coe_map, le_principal_iff, Filter.mem_map]
      exact Filter.univ_mem' hg)
  rw [Ultrafilter.coe_map] at hle
  exact ⟨a, ha, hle⟩

/-- An average of `[0,1]`-valued terms lies in `[0,1]`. -/
theorem div_mem_Icc_of_sum {N : ℕ} {g : ℕ → ℝ} (h0 : ∀ t, 0 ≤ g t) (h1 : ∀ t, g t ≤ 1) :
    (∑ t ∈ range N, g t) / N ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨div_nonneg (Finset.sum_nonneg fun t _ => h0 t) (Nat.cast_nonneg N), ?_⟩
  rcases Nat.eq_zero_or_pos N with h | h
  · rw [h, Nat.cast_zero, div_zero]
    exact zero_le_one
  · rw [div_le_one (by exact_mod_cast h)]
    calc ∑ t ∈ range N, g t ≤ ∑ t ∈ range N, (1 : ℝ) := Finset.sum_le_sum fun t _ => h1 t
      _ = N := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/-- **Chentsov's theorem, general form** (post #3; Chentsov 1967). Let `P` be a stochastic
matrix on `Fin n` whose stationary distribution `π` is unique, and `u` a CUD sequence. Then for
every start `x₀` the path driven by `u` through the inverse-CDF update has occupation
frequencies `N_j(T)/T → π_j`. No coupling or aperiodicity hypothesis is needed. -/
theorem tendsto_occFreq_of_isCUD_general {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {u : ℕ → ℝ} (hu : IsCUD u) {π : Fin n → ℝ}
    (huniq : ∀ ρ : Fin n → ℝ, (∀ j, ∑ i, ρ i * P i j = ρ j) → (∀ i, 0 ≤ ρ i) →
      ∑ i, ρ i = 1 → ρ = π)
    (x₀ j : Fin n) :
    Tendsto (fun T => (occCount (drivenPath P x₀ u) j T : ℝ) / T) atTop (𝓝 (π j)) := by
  classical
  set x := drivenPath P x₀ u with hx
  set Z : ℕ → Fin n → Fin n := fun t i => step P i (u t) with hZdef
  have hxZ : ∀ t, x (t + 1) = Z t (x t) := fun t => rfl
  -- the empirical quantities
  set e : ℕ → (m : ℕ) → Fin n → (Fin m → Fin n → Fin n) → ℝ := fun N m y z =>
    (∑ t ∈ range N, (if x t = y then (1 : ℝ) else 0) *
      ∏ k : Fin m, (if Z (t + k) = z k then (1 : ℝ) else 0)) / N with he
  set f : ℕ → Fin n → ℝ := fun N y => (occCount x y N : ℝ) / N with hf
  set er : ℕ → Fin n → (Fin n → Fin n) → ℝ := fun N y a =>
    (∑ t ∈ range N, (if x t = y then (1 : ℝ) else 0) * (if Z t = a then (1 : ℝ) else 0)) / N
    with her
  have hind01 : ∀ (p : Prop) [Decidable p], (0 : ℝ) ≤ (if p then 1 else 0) ∧
      (if p then (1 : ℝ) else 0) ≤ 1 := fun p _ => by
    split_ifs
    · exact ⟨zero_le_one, le_refl 1⟩
    · exact ⟨le_refl 0, zero_le_one⟩
  have hprod01 : ∀ (t m : ℕ) (z : Fin m → Fin n → Fin n),
      0 ≤ ∏ k : Fin m, (if Z (t + k) = z k then (1 : ℝ) else 0) ∧
        ∏ k : Fin m, (if Z (t + k) = z k then (1 : ℝ) else 0) ≤ 1 := fun t m z =>
    ⟨Finset.prod_nonneg fun k _ => (hind01 _).1,
      Finset.prod_le_one₀ (fun k _ => (hind01 _).1) fun k _ => (hind01 _).2⟩
  have he01 : ∀ N m y z, e N m y z ∈ Set.Icc (0 : ℝ) 1 := fun N m y z =>
    div_mem_Icc_of_sum (fun t => mul_nonneg (hind01 _).1 (hprod01 t m z).1)
      fun t => (mul_le_of_le_one_left (hprod01 t m z).1 (hind01 _).2).trans (hprod01 t m z).2
  have hf01 : ∀ N y, f N y ∈ Set.Icc (0 : ℝ) 1 := fun N y => by
    rw [hf]
    dsimp only
    rw [occCount_eq_sum]
    exact div_mem_Icc_of_sum (fun t => (hind01 _).1) fun t => (hind01 _).2
  have her01 : ∀ N y a, er N y a ∈ Set.Icc (0 : ℝ) 1 := fun N y a =>
    div_mem_Icc_of_sum (fun t => mul_nonneg (hind01 _).1 (hind01 _).1)
      fun t => (mul_le_of_le_one_left (hind01 _).1 (hind01 _).2).trans (hind01 _).2
  -- exact identities at finite `N`
  have hXN : ∀ N m y, ∑ z, e N m y z = f N y := by
    intro N m y
    rw [he, hf]
    dsimp only
    rw [← Finset.sum_div, Finset.sum_comm, occCount_eq_sum]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.mul_sum, sum_prod_ite_eq_one Z t m, mul_one]
  have hsplit : ∀ (t L : ℕ) (a : Fin n → Fin n) (z' : Fin L → Fin n → Fin n),
      ∏ k : Fin (L + 1), (if Z (t + k) = (Fin.cons a z' : Fin (L + 1) → Fin n → Fin n) k
        then (1 : ℝ) else 0) =
      (if Z t = a then (1 : ℝ) else 0) *
        ∏ k : Fin L, (if Z (t + 1 + k) = z' k then (1 : ℝ) else 0) := by
    intro t L a z'
    rw [Fin.prod_univ_succ]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Fin.cons_succ, Fin.val_succ, show t + (k + 1) = t + 1 + k by omega]
  have hrN : ∀ N L y a, ∑ z', e N (L + 1) y (Fin.cons a z') = er N y a := by
    intro N L y a
    rw [he, her]
    dsimp only
    rw [← Finset.sum_div, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [hsplit]
    rw [← Finset.mul_sum, ← Finset.mul_sum, sum_prod_ite_eq_one Z (t + 1) L, mul_one]
  have hstatN : ∀ N L j z', 0 < N → |∑ y, ∑ a, (if a y = j then e N (L + 1) y (Fin.cons a z')
      else 0) - e N L j z'| ≤ 1 / N := by
    intro N L j z' hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    set g : ℕ → ℝ := fun t => (if x t = j then (1 : ℝ) else 0) *
      ∏ k : Fin L, (if Z (t + k) = z' k then (1 : ℝ) else 0) with hg
    have step1 : ∀ y a, (if a y = j then e N (L + 1) y (Fin.cons a z') else 0) =
        (∑ t ∈ range N, (if a y = j then (if x t = y then (1 : ℝ) else 0) *
          ((if Z t = a then (1 : ℝ) else 0) *
            ∏ k : Fin L, (if Z (t + 1 + k) = z' k then (1 : ℝ) else 0)) else 0)) / N := by
      intro y a
      rw [he]
      dsimp only
      by_cases h : a y = j
      · simp only [h, ↓reduceIte, hsplit]
      · simp only [h, ↓reduceIte, Finset.sum_const_zero, zero_div]
    have hlhs : ∑ y, ∑ a, (if a y = j then e N (L + 1) y (Fin.cons a z') else 0) =
        (∑ t ∈ range N, g (t + 1)) / N := by
      simp only [step1]
      simp only [← Finset.sum_div]
      congr 1
      refine (Finset.sum_congr rfl fun y _ => Finset.sum_comm).trans ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Finset.sum_eq_single (x t)]
      · rw [Finset.sum_eq_single (Z t)]
        · rw [hg]
          dsimp only
          rw [hxZ]
          by_cases h : Z t (x t) = j
          · simp only [h, ↓reduceIte, one_mul]
          · simp only [h, ↓reduceIte]
            ring
        · intro a _ ha
          by_cases h : a (x t) = j
          · simp only [h, ↓reduceIte, Ne.symm ha, zero_mul, mul_zero]
          · simp only [h, ↓reduceIte]
        · exact fun h => absurd (Finset.mem_univ _) h
      · intro y _ hy
        refine Finset.sum_eq_zero fun a _ => ?_
        by_cases h : a y = j
        · simp only [h, ↓reduceIte, Ne.symm hy, zero_mul]
        · simp only [h, ↓reduceIte]
      · exact fun h => absurd (Finset.mem_univ _) h
    have hrhs : e N L j z' = (∑ t ∈ range N, g t) / N := rfl
    rw [hlhs, hrhs, ← sub_div, abs_div, abs_of_pos hNR]
    refine div_le_div_of_nonneg_right ?_ hNR.le
    have h1 := Finset.sum_range_succ' g N
    have h2 := Finset.sum_range_succ g N
    have hgN : 0 ≤ g N ∧ g N ≤ 1 := ⟨mul_nonneg (hind01 _).1 (hprod01 N L z').1,
      (mul_le_of_le_one_left (hprod01 N L z').1 (hind01 _).2).trans (hprod01 N L z').2⟩
    have hg0 : 0 ≤ g 0 ∧ g 0 ≤ 1 := ⟨mul_nonneg (hind01 _).1 (hprod01 0 L z').1,
      (mul_le_of_le_one_left (hprod01 0 L z').1 (hind01 _).2).trans (hprod01 0 L z').2⟩
    rw [abs_le]
    constructor <;> linarith
  -- the bad event
  by_contra hnot
  obtain ⟨ε, hε, hfr⟩ : ∃ ε > 0, ∃ᶠ N in atTop, ε ≤ |f N j - π j| := by
    rw [Metric.tendsto_atTop] at hnot
    push Not at hnot
    obtain ⟨ε, hε, h⟩ := hnot
    refine ⟨ε, hε, Filter.frequently_atTop.2 fun N0 => ?_⟩
    obtain ⟨N, hN, hd⟩ := h N0
    exact ⟨N, hN, by rwa [Real.dist_eq] at hd⟩
  have hne := Filter.frequently_iff_neBot.1 hfr
  set 𝒰 : Ultrafilter ℕ := Ultrafilter.of (atTop ⊓ 𝓟 {N | ε ≤ |f N j - π j|}) with h𝒰
  have h𝒰le : (𝒰 : Filter ℕ) ≤ atTop ⊓ 𝓟 {N | ε ≤ |f N j - π j|} := Ultrafilter.of_le _
  have h𝒰top : (𝒰 : Filter ℕ) ≤ atTop := h𝒰le.trans inf_le_left
  have h𝒰bad : ∀ᶠ N in (𝒰 : Filter ℕ), ε ≤ |f N j - π j| :=
    le_principal_iff.1 (h𝒰le.trans inf_le_right)
  -- limits along the ultrafilter
  choose q hq01 hq using fun m y z => exists_tendsto_ultrafilter 𝒰 fun N => he01 N m y z
  choose ρ hρ01 hρ using fun y => exists_tendsto_ultrafilter 𝒰 fun N => hf01 N y
  choose r hr01 hrlim using fun y a => exists_tendsto_ultrafilter 𝒰 fun N => her01 N y a
  have hinv : Tendsto (fun N : ℕ => (1 : ℝ) / N) (𝒰 : Filter ℕ) (𝓝 0) :=
    (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).mono_left h𝒰top
  have hpos : ∀ᶠ N in (𝒰 : Filter ℕ), 0 < N := h𝒰top (eventually_gt_atTop 0)
  -- the hypotheses of the entropy lemma
  have hZ' : ∀ m z, ∑ y, q m y z = ∏ k, cellProb hP (z k) := by
    intro m z
    refine tendsto_nhds_unique (tendsto_finsetSum _ fun y _ => hq m y z) ?_
    have hpat := (tendsto_empAvg_of_isStepFn (hu m) (isStepFn_pattern hP m z)).mono_left h𝒰top
    refine hpat.congr fun N => ?_
    rw [he]
    dsimp only
    rw [← Finset.sum_div, Finset.sum_comm]
    unfold empAvg
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.sum_mul]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, one_mul]
    rfl
  have hX' : ∀ m y, ∑ z, q m y z = ρ y := fun m y =>
    tendsto_nhds_unique (tendsto_finsetSum _ fun z _ => hq m y z)
      ((hρ y).congr fun N => (hXN N m y).symm)
  have hr' : ∀ L y a, ∑ z', q (L + 1) y (Fin.cons a z') = r y a := fun L y a =>
    tendsto_nhds_unique (tendsto_finsetSum _ fun z' _ => hq (L + 1) y _)
      ((hrlim y a).congr fun N => (hrN N L y a).symm)
  have hstat' : ∀ L j' z', ∑ y, ∑ a, (if a y = j' then q (L + 1) y (Fin.cons a z') else 0) =
      q L j' z' := by
    intro L j' z'
    have h1 : Tendsto (fun N => ∑ y, ∑ a, (if a y = j' then e N (L + 1) y (Fin.cons a z')
        else 0)) (𝒰 : Filter ℕ)
        (𝓝 (∑ y, ∑ a, (if a y = j' then q (L + 1) y (Fin.cons a z') else 0))) :=
      tendsto_finsetSum _ fun y _ => tendsto_finsetSum _ fun a _ => by
        by_cases h : a y = j'
        · simp only [h, ↓reduceIte]
          exact hq _ _ _
        · simp only [h, ↓reduceIte]
          exact tendsto_const_nhds
    have h2 : Tendsto (fun N => ∑ y, ∑ a, (if a y = j' then e N (L + 1) y (Fin.cons a z')
        else 0)) (𝒰 : Filter ℕ) (𝓝 (q L j' z')) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h3 := hinv.add (tendsto_iff_norm_sub_tendsto_zero.1 (hq L j' z'))
      rw [add_zero] at h3
      refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ h3
      filter_upwards [hpos] with N hN
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      calc _ ≤ |∑ y, ∑ a, (if a y = j' then e N (L + 1) y (Fin.cons a z') else 0) -
            e N L j' z'| + |e N L j' z' - q L j' z'| := abs_sub_le _ _ _
        _ ≤ _ := add_le_add_left (hstatN N L j' z' hN) _
    exact tendsto_nhds_unique h1 h2
  have hρ1 : ∑ y, ρ y = 1 := by
    refine tendsto_nhds_unique (tendsto_finsetSum _ fun y _ => hρ y)
      (tendsto_const_nhds.congr' ?_)
    filter_upwards [hpos] with N hN
    rw [hf]
    dsimp only
    rw [← Finset.sum_div, ← Nat.cast_sum, sum_occCount, div_self (by exact_mod_cast hN.ne')]
  have hstatρ := chentsov_entropy_stationary (X := Fin n) (C := Fin n → Fin n)
    (fun y a => a y) (cellProb hP) ρ r q (fun m y z => (hq01 m y z).1) hZ' hX' hr' hstat' hρ1
  have hρP : ∀ j', ∑ i, ρ i * P i j' = ρ j' := fun j' => by
    rw [← hstatρ j']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_cellProb_eq hP (hu 1) i j']
  have hρπ := huniq ρ hρP (fun i => (hρ01 i).1) hρ1
  have hlimj := hρ j
  rw [hρπ] at hlimj
  obtain ⟨N, hN1, hN2⟩ := ((Metric.tendsto_nhds.1 hlimj ε hε).and h𝒰bad).exists
  rw [Real.dist_eq] at hN1
  linarith

/-- **Time averages, general form** (post #3): under the hypotheses of
`tendsto_occFreq_of_isCUD_general`, `(1/T) ∑_{t<T} g(x_t) → ∑_j π_j g(j)`. -/
theorem tendsto_timeAvg_of_isCUD_general {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {u : ℕ → ℝ} (hu : IsCUD u) {π : Fin n → ℝ}
    (huniq : ∀ ρ : Fin n → ℝ, (∀ j, ∑ i, ρ i * P i j = ρ j) → (∀ i, 0 ≤ ρ i) →
      ∑ i, ρ i = 1 → ρ = π)
    (x₀ : Fin n) (g : Fin n → ℝ) :
    Tendsto (fun T => (∑ t ∈ range T, g (drivenPath P x₀ u t)) / T) atTop
      (𝓝 (∑ j, π j * g j)) := by
  have h := tendsto_finsetSum (Finset.univ : Finset (Fin n)) fun j _ =>
    (tendsto_occFreq_of_isCUD_general hP hu huniq x₀ j).mul_const (g j)
  refine h.congr fun T => ?_
  have hfib : ∀ t, g (drivenPath P x₀ u t) =
      ∑ j, (if drivenPath P x₀ u t = j then (1 : ℝ) else 0) * g j := fun t => by
    rw [Finset.sum_eq_single (drivenPath P x₀ u t)
      (fun k _ hk => by simp only [Ne.symm hk, ↓reduceIte, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp only [↓reduceIte, one_mul]
  rw [Finset.sum_congr rfl fun t _ => hfib t, Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [occCount_eq_sum, ← Finset.sum_mul, div_mul_eq_mul_div]

/-- **The chain without a coupling box is consistent.** For `fourState` (no coupling box of
any length, `not_hasCouplingBox_fourState`) and every CUD driving sequence, every state has
limiting frequency `1/4`. -/
theorem tendsto_occFreq_fourState_of_isCUD {u : ℕ → ℝ} (hu : IsCUD u) (x₀ j : Fin 4) :
    Tendsto (fun T => (occCount (drivenPath fourState x₀ u) j T : ℝ) / T) atTop
      (𝓝 (1 / 4)) := by
  refine tendsto_occFreq_of_isCUD_general (π := fun _ => 1 / 4) isStochastic_fourState hu
    (fun ρ hρ _ hρ1 => funext fun j' => ?_) x₀ j
  rw [← sum_mul_multiStep hρ 2 j']
  simp only [multiStep_fourState_two]
  rw [← Finset.sum_mul, hρ1, one_mul]

end RQMCMarkov.MarkovDriving

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # Stationary distribution and Poisson's equation for a finite irreducible chain

Post #3 measures the quality of a simulated path by its occupation frequencies and its empirical
transition matrix, compared with the stationary distribution `π` of the transition matrix `P`. The
convergence-speed claims of post #3 (`OccupationDiscrepancy`, `StackBound`, `RotorRouter`,
`MCRate`) all go through **Poisson's equation** `h − Ph = f − π(f)` (Meyn and Tweedie, Ch. 17;
Kemeny and Snell's fundamental matrix). This module proves what they need, for a finite
irreducible stochastic matrix; aperiodicity is **not** assumed.

Irreducibility is `∀ i j, ∃ k, 0 < (Pᵏ) i j` (the `k = 0` form; `k = 0` only helps for `i = j`).

**Results.**
* `pow_apply_nonneg_of_nonneg`, `sum_pow_apply_eq_one`: `Pᵏ` is stochastic.
* `eq_of_mulVec_eq_self_of_irreducible`: **maximum principle**: a harmonic function (`Ph = h`) of
  an irreducible chain is constant.
* `exists_isStationaryDistribution`: a stationary distribution exists (for any stochastic `P` on a
  nonempty finite set; the proof takes a left null vector `μ` of `I − P`, which exists by
  rank–nullity, and shows that `|μ|` is stationary).
* `IsStationaryDistribution.pos`: under irreducibility every `π_i > 0`.
* `exists_poisson`: **Poisson's equation** `h − Ph = f − π(f)` has a solution for every `f`. The
  range of `I − P` is the hyperplane `{g : π(g) = 0}`: it is contained in it, and has dimension
  `|S| − 1` because the kernel of `I − P` is the constants (maximum principle).
* `poisson_const_eq` : conversely, if `h − Ph = f − c` then `c = π(f)`.
* `eq_of_vecMul_eq_self` / `existsUnique_isStationaryDistribution`: the stationary distribution
  is unique (indeed any signed `ν` with `νP = ν` and `Σν = 1` equals `π`).
* `poisson_sub_eq`: the solution of Poisson's equation is unique up to an additive constant.
* `exists_poisson_normalized`: it can be normalised to `π(h) = 0`.
-/

namespace RQMCMarkov.MarkovDriving

open Matrix Finset Module

variable {S : Type*} [Fintype S]

/-- A stationary distribution of the transition matrix `P`: a probability vector with `μP = μ`. -/
structure IsStationaryDistribution (P : Matrix S S ℝ) (μ : S → ℝ) : Prop where
  vecMul_eq : μ ᵥ* P = μ
  nonneg : ∀ i, 0 ≤ μ i
  sum_eq_one : ∑ i, μ i = 1

/-- The entries of `Pᵏ` are nonnegative when those of `P` are. -/
theorem pow_apply_nonneg_of_nonneg [DecidableEq S] {P : Matrix S S ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    (k : ℕ) (i j : S) : 0 ≤ (P ^ k) i j := by
  induction k generalizing i j with
  | zero =>
    rw [pow_zero, one_apply]
    split_ifs
    · exact zero_le_one
    · exact le_rfl
  | succ k ih =>
    rw [pow_succ, mul_apply]
    exact sum_nonneg fun l _ => mul_nonneg (ih i l) (hP0 l j)

/-- The row sums of `Pᵏ` are one when those of `P` are. -/
theorem sum_pow_apply_eq_one [DecidableEq S] {P : Matrix S S ℝ} (hP1 : ∀ i, ∑ j, P i j = 1)
    (k : ℕ) (i : S) :
    ∑ j, (P ^ k) i j = 1 := by
  induction k generalizing i with
  | zero =>
    rw [pow_zero]
    simp only [one_apply, Finset.sum_ite_eq, mem_univ, ite_true]
  | succ k ih =>
    rw [pow_succ]
    simp only [mul_apply]
    rw [Finset.sum_comm]
    calc ∑ l, ∑ j, (P ^ k) i l * P l j = ∑ l, (P ^ k) i l := by
          refine sum_congr rfl fun l _ => ?_
          rw [← mul_sum, hP1 l, mul_one]
      _ = 1 := ih i

/-- `P 1 = 1`: a stochastic matrix fixes the constant function one. -/
theorem mulVec_const_one {P : Matrix S S ℝ} (hP1 : ∀ i, ∑ j, P i j = 1) :
    P *ᵥ (fun _ => (1 : ℝ)) = fun _ => 1 := by
  funext i
  simp only [mulVec, dotProduct, mul_one]
  exact hP1 i

/-- One step of the maximum principle: for a stochastic `Q`, if `h` is maximal at `x` and
`(Qh)(x) = h(x)`, then `h y = h x` whenever `Q x y > 0`. -/
theorem eq_of_isMax_of_mulVec_eq {Q : Matrix S S ℝ} (hQ0 : ∀ i j, 0 ≤ Q i j)
    (hQ1 : ∀ i, ∑ j, Q i j = 1) {h : S → ℝ} {x : S} (hmax : ∀ y, h y ≤ h x)
    (hx : (Q *ᵥ h) x = h x) {y : S} (hy : 0 < Q x y) : h y = h x := by
  have hsum : ∑ z, Q x z * (h x - h z) = 0 := by
    have e : ∑ z, Q x z * (h x - h z) = h x * ∑ z, Q x z - (Q *ᵥ h) x := by
      simp only [mul_sub, sum_sub_distrib, mulVec, dotProduct, mul_sum]
      congr 1
      exact sum_congr rfl fun z _ => mul_comm _ _
    rw [e, hQ1, mul_one, hx, sub_self]
  have hterm := (sum_eq_zero_iff_of_nonneg
    (fun z _ => mul_nonneg (hQ0 x z) (sub_nonneg.2 (hmax z)))).1 hsum y (mem_univ y)
  rcases mul_eq_zero.1 hterm with h1 | h1
  · exact absurd h1 hy.ne'
  · linarith

/-- **Maximum principle.** For an irreducible stochastic matrix, a function with `Ph = h` is
constant. -/
theorem eq_of_mulVec_eq_self_of_irreducible [DecidableEq S] {P : Matrix S S ℝ}
    (hP0 : ∀ i j, 0 ≤ P i j) (hP1 : ∀ i, ∑ j, P i j = 1) (hirr : ∀ i j, ∃ k, 0 < (P ^ k) i j)
    {h : S → ℝ} (hh : P *ᵥ h = h) (y z : S) : h y = h z := by
  obtain ⟨x, -, hx⟩ := Finset.exists_max_image univ h ⟨y, mem_univ y⟩
  have hk : ∀ k : ℕ, (P ^ k) *ᵥ h = h := by
    intro k
    induction k with
    | zero => rw [pow_zero, one_mulVec]
    | succ k ih => rw [pow_succ, ← mulVec_mulVec, hh, ih]
  have key : ∀ w, h w = h x := fun w => by
    obtain ⟨k, hkpos⟩ := hirr x w
    exact eq_of_isMax_of_mulVec_eq (pow_apply_nonneg_of_nonneg hP0 k) (sum_pow_apply_eq_one hP1 k)
      (fun v => hx v (mem_univ v)) (congrFun (hk k) x) hkpos
  rw [key y, key z]

/-- `μ (I − P) = 0` iff `μ P = μ`. -/
theorem vecMul_one_sub_eq_zero_iff [DecidableEq S] {P : Matrix S S ℝ} {μ : S → ℝ} :
    μ ᵥ* (1 - P) = 0 ↔ μ ᵥ* P = μ := by
  rw [vecMul_sub, vecMul_one, sub_eq_zero, eq_comm]

/-- `(I − P) h = h − P h`. -/
theorem one_sub_mulVec [DecidableEq S] (P : Matrix S S ℝ) (h : S → ℝ) :
    (1 - P) *ᵥ h = h - P *ᵥ h := by
  rw [sub_mulVec, one_mulVec]

/-- The constant function one is a nonzero vector in the kernel of `I − P`. -/
theorem const_one_mem_ker [DecidableEq S] {P : Matrix S S ℝ} (hP1 : ∀ i, ∑ j, P i j = 1) :
    (fun _ => (1 : ℝ)) ∈ LinearMap.ker (1 - P).mulVecLin := by
  rw [LinearMap.mem_ker, mulVecLin_apply, one_sub_mulVec, mulVec_const_one hP1, sub_self]

/-- The constant function one is nonzero on a nonempty type. -/
theorem const_one_ne_zero {T : Type*} [Nonempty T] : (fun _ => (1 : ℝ)) ≠ (0 : T → ℝ) := by
  intro h
  have := congrFun h (Classical.arbitrary T)
  exact one_ne_zero this

/-- The rank of `I − P` is less than `|S|`, since its kernel contains the constants. -/
theorem rank_one_sub_lt [Nonempty S] [DecidableEq S] {P : Matrix S S ℝ}
    (hP1 : ∀ i, ∑ j, P i j = 1) :
    (1 - P).rank < Fintype.card S := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (1 - P).mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  have hker : 0 < finrank ℝ (LinearMap.ker (1 - P).mulVecLin) := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have hbot := Submodule.finrank_eq_zero.1 h0
    have hmem := const_one_mem_ker hP1
    rw [hbot, Submodule.mem_bot] at hmem
    exact const_one_ne_zero hmem
  unfold Matrix.rank
  omega

/-- **Existence of a stationary distribution**, for any stochastic matrix on a nonempty finite
set: a left null vector `μ ≠ 0` of `I − P` exists by rank–nullity (`rank (I − P)ᵀ = rank (I − P)
< |S|`), and `|μ|`, normalised, is stationary because `|μ| ≤ |μ| P` entrywise with equal sums. -/
theorem exists_isStationaryDistribution [Nonempty S] {P : Matrix S S ℝ}
    (hP0 : ∀ i j, 0 ≤ P i j) (hP1 : ∀ i, ∑ j, P i j = 1) :
    ∃ μ, IsStationaryDistribution P μ := by
  classical
  -- a nonzero left null vector of `I − P`
  have hrn := LinearMap.finrank_range_add_finrank_ker (1 - P)ᵀ.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  have hrk : finrank ℝ (LinearMap.range (1 - P)ᵀ.mulVecLin) < Fintype.card S := by
    have h1 := rank_transpose (1 - P)
    have h2 := rank_one_sub_lt hP1
    unfold Matrix.rank at h1 h2
    omega
  have hne : LinearMap.ker (1 - P)ᵀ.mulVecLin ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hrn
    omega
  obtain ⟨μ, hμker, hμ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [LinearMap.mem_ker, mulVecLin_apply, mulVec_transpose, vecMul_one_sub_eq_zero_iff] at hμker
  -- `ν = |μ|` is a nonnegative fixed vector
  set ν : S → ℝ := fun i => |μ i| with hν
  have hle : ∀ j, ν j ≤ (ν ᵥ* P) j := by
    intro j
    have e : μ j = ∑ i, μ i * P i j := by
      conv_lhs => rw [← hμker]
      rfl
    change |μ j| ≤ ∑ i, |μ i| * P i j
    rw [e]
    refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun i _ => ?_))
    rw [abs_mul, abs_of_nonneg (hP0 i j)]
  have hsumeq : ∑ j, (ν ᵥ* P) j = ∑ j, ν j := by
    change ∑ j, ∑ i, ν i * P i j = ∑ j, ν j
    rw [Finset.sum_comm]
    exact sum_congr rfl fun i _ => by rw [← mul_sum, hP1 i, mul_one]
  have hfix : ν ᵥ* P = ν := by
    have h0 : ∑ j, ((ν ᵥ* P) j - ν j) = 0 := by rw [sum_sub_distrib, hsumeq, sub_self]
    funext j
    have := (sum_eq_zero_iff_of_nonneg (fun j _ => sub_nonneg.2 (hle j))).1 h0 j (mem_univ j)
    linarith
  have hpos : 0 < ∑ i, ν i := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hμ0
    exact lt_of_lt_of_le (abs_pos.2 hi) (single_le_sum (fun j _ => abs_nonneg (μ j)) (mem_univ i))
  refine ⟨fun i => ν i / ∑ k, ν k, ⟨?_, fun i => div_nonneg (abs_nonneg _) hpos.le, ?_⟩⟩
  · funext j
    change ∑ i, ν i / (∑ k, ν k) * P i j = ν j / ∑ k, ν k
    have e : ∑ i, ν i / (∑ k, ν k) * P i j = (∑ i, ν i * P i j) / ∑ k, ν k := by
      rw [Finset.sum_div]
      exact sum_congr rfl fun i _ => by ring
    rw [e]
    congr 1
    exact congrFun hfix j
  · rw [← Finset.sum_div, div_self hpos.ne']

/-- A stationary distribution is invariant under every power of `P`. -/
theorem IsStationaryDistribution.vecMul_pow [DecidableEq S] {P : Matrix S S ℝ} {μ : S → ℝ}
    (hμ : IsStationaryDistribution P μ) (k : ℕ) : μ ᵥ* P ^ k = μ := by
  induction k with
  | zero => rw [pow_zero, vecMul_one]
  | succ k ih => rw [pow_succ, ← vecMul_vecMul, ih, hμ.vecMul_eq]

/-- Under irreducibility the stationary distribution charges every state. -/
theorem IsStationaryDistribution.pos [DecidableEq S] {P : Matrix S S ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    (hirr : ∀ i j, ∃ k, 0 < (P ^ k) i j) {μ : S → ℝ} (hμ : IsStationaryDistribution P μ)
    (j : S) : 0 < μ j := by
  obtain ⟨x, hx⟩ : ∃ x, 0 < μ x := by
    by_contra hcon
    push Not at hcon
    have h0 : ∑ i, μ i = 0 :=
      sum_eq_zero fun i _ => le_antisymm (hcon i) (hμ.nonneg i)
    rw [hμ.sum_eq_one] at h0
    exact one_ne_zero h0
  obtain ⟨k, hk⟩ := hirr x j
  have e : μ j = ∑ i, μ i * (P ^ k) i j := by
    conv_lhs => rw [← hμ.vecMul_pow k]
    rfl
  rw [e]
  exact lt_of_lt_of_le (mul_pos hx hk)
    (single_le_sum (fun i _ => mul_nonneg (hμ.nonneg i) (pow_apply_nonneg_of_nonneg hP0 k i j))
      (mem_univ x))

/-- `ν(g − c) = ν(g) − c Σ ν`. -/
theorem dotProduct_sub_const (ν g : S → ℝ) (c : ℝ) :
    ν ⬝ᵥ (fun i => g i - c) = ν ⬝ᵥ g - c * ∑ i, ν i := by
  simp only [dotProduct, mul_sub, sum_sub_distrib, mul_sum]
  congr 1
  exact sum_congr rfl fun i _ => mul_comm _ _

/-- A left fixed vector annihilates the range of `I − P`: `ν(h − Ph) = 0` when `νP = ν`. -/
theorem dotProduct_sub_mulVec_eq_zero {P : Matrix S S ℝ} {ν : S → ℝ} (hν : ν ᵥ* P = ν)
    (h : S → ℝ) : ν ⬝ᵥ (h - P *ᵥ h) = 0 := by
  rw [dotProduct_sub, dotProduct_mulVec, hν, sub_self]

/-- **Poisson's equation.** For a finite irreducible stochastic matrix `P` with stationary
distribution `μ` (aperiodicity is not needed), for every `f` there is `h` with
`h − Ph = f − μ(f)`. -/
theorem exists_poisson [Nonempty S] [DecidableEq S] {P : Matrix S S ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    (hP1 : ∀ i, ∑ j, P i j = 1) (hirr : ∀ i j, ∃ k, 0 < (P ^ k) i j) {μ : S → ℝ}
    (hμ : IsStationaryDistribution P μ) (f : S → ℝ) :
    ∃ h : S → ℝ, ∀ i, h i - (P *ᵥ h) i = f i - μ ⬝ᵥ f := by
  -- the hyperplane `W = {g : μ(g) = 0}`
  let φ : (S → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun g => μ ⬝ᵥ g
      map_add' := fun a b => dotProduct_add μ a b
      map_smul' := fun c a => dotProduct_smul c μ a }
  have hφ : ∀ g, φ g = μ ⬝ᵥ g := fun _ => rfl
  set A : Matrix S S ℝ := 1 - P with hA
  have hle : LinearMap.range A.mulVecLin ≤ LinearMap.ker φ := by
    rintro g ⟨h, rfl⟩
    rw [LinearMap.mem_ker, hφ, mulVecLin_apply, hA, one_sub_mulVec]
    exact dotProduct_sub_mulVec_eq_zero hμ.vecMul_eq h
  -- `dim W < |S|`
  have hW : finrank ℝ (LinearMap.ker φ) < Fintype.card S := by
    rw [← Module.finrank_fintype_fun_eq_card (R := ℝ)]
    refine Submodule.finrank_lt fun htop => ?_
    have hmem : (fun _ => (1 : ℝ)) ∈ LinearMap.ker φ := by rw [htop]; exact Submodule.mem_top
    rw [LinearMap.mem_ker, hφ, dotProduct_comm] at hmem
    have e : (fun _ => (1 : ℝ)) ⬝ᵥ μ = ∑ i, μ i := by
      simp only [dotProduct, one_mul]
    rw [e, hμ.sum_eq_one] at hmem
    exact one_ne_zero hmem
  -- `dim ker A ≤ 1`, since the kernel is the constants
  have hker : finrank ℝ (LinearMap.ker A.mulVecLin) ≤ 1 := by
    have hsub : LinearMap.ker A.mulVecLin ≤ ℝ ∙ (fun _ => (1 : ℝ)) := by
      intro v hv
      rw [LinearMap.mem_ker, mulVecLin_apply, hA, one_sub_mulVec, sub_eq_zero] at hv
      obtain ⟨x⟩ := (inferInstance : Nonempty S)
      rw [Submodule.mem_span_singleton]
      refine ⟨v x, funext fun y => ?_⟩
      change v x * 1 = v y
      rw [mul_one]
      exact eq_of_mulVec_eq_self_of_irreducible hP0 hP1 hirr hv.symm x y
    calc finrank ℝ (LinearMap.ker A.mulVecLin) ≤ finrank ℝ (ℝ ∙ (fun _ => (1 : ℝ))) :=
          Submodule.finrank_mono hsub
      _ = 1 := finrank_span_singleton const_one_ne_zero
  have hrn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  have heq : LinearMap.range A.mulVecLin = LinearMap.ker φ :=
    Submodule.eq_of_le_of_finrank_le hle (by omega)
  -- the centred `f` lies in `W`, hence in the range of `I − P`
  have hg : (fun i => f i - μ ⬝ᵥ f) ∈ LinearMap.ker φ := by
    rw [LinearMap.mem_ker, hφ]
    rw [dotProduct_sub_const, hμ.sum_eq_one, mul_one, sub_self]
  rw [← heq] at hg
  obtain ⟨h, hh⟩ := hg
  refine ⟨h, fun i => ?_⟩
  have := congrFun hh i
  rw [mulVecLin_apply, hA, one_sub_mulVec] at this
  exact this

/-- The centring constant in Poisson's equation is forced: if `h − Ph = f − c` then
`c = ν(f)` for every (even signed) `ν` with `νP = ν` and `Σ ν = 1`. -/
theorem poisson_const_eq {P : Matrix S S ℝ} {ν : S → ℝ} (hν : ν ᵥ* P = ν)
    (hν1 : ∑ i, ν i = 1) {f h : S → ℝ} {c : ℝ} (hh : ∀ i, h i - (P *ᵥ h) i = f i - c) :
    c = ν ⬝ᵥ f := by
  have h0 := dotProduct_sub_mulVec_eq_zero hν h
  have e : h - P *ᵥ h = fun i => f i - c := funext hh
  rw [e] at h0
  rw [dotProduct_sub_const, hν1, mul_one] at h0
  linarith

/-- **Uniqueness of the stationary distribution**: any (even signed) `ν` with `νP = ν` and
`Σ ν = 1` equals the stationary distribution `μ`. Tested against the Poisson solutions for the
indicators `f = 1_{s}`. -/
theorem IsStationaryDistribution.eq_of_vecMul_eq_self [Nonempty S] [DecidableEq S]
    {P : Matrix S S ℝ} (hP0 : ∀ i j, 0 ≤ P i j) (hP1 : ∀ i, ∑ j, P i j = 1)
    (hirr : ∀ i j, ∃ k, 0 < (P ^ k) i j)
    {μ : S → ℝ} (hμ : IsStationaryDistribution P μ) {ν : S → ℝ} (hν : ν ᵥ* P = ν)
    (hν1 : ∑ i, ν i = 1) : ν = μ := by
  funext s
  obtain ⟨h, hh⟩ := exists_poisson hP0 hP1 hirr hμ (fun i => if i = s then 1 else 0)
  have hc := poisson_const_eq hν hν1 hh
  have e : ∀ w : S → ℝ, w ⬝ᵥ (fun i => if i = s then (1 : ℝ) else 0) = w s := fun w => by
    simp only [dotProduct, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', mem_univ, ite_true]
  rw [e, e] at hc
  exact hc.symm

/-- **Existence and uniqueness** of the stationary distribution of a finite irreducible
stochastic matrix. -/
theorem existsUnique_isStationaryDistribution [Nonempty S] [DecidableEq S] {P : Matrix S S ℝ}
    (hP0 : ∀ i j, 0 ≤ P i j) (hP1 : ∀ i, ∑ j, P i j = 1) (hirr : ∀ i j, ∃ k, 0 < (P ^ k) i j) :
    ∃! μ, IsStationaryDistribution P μ := by
  obtain ⟨μ, hμ⟩ := exists_isStationaryDistribution hP0 hP1
  exact ⟨μ, hμ, fun ν hν =>
    hμ.eq_of_vecMul_eq_self hP0 hP1 hirr hν.vecMul_eq hν.sum_eq_one⟩

/-- The solution of Poisson's equation is unique up to an additive constant: two solutions of
`h − Ph = g` differ by a constant. -/
theorem poisson_sub_eq [DecidableEq S] {P : Matrix S S ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    (hP1 : ∀ i, ∑ j, P i j = 1) (hirr : ∀ i j, ∃ k, 0 < (P ^ k) i j) {g h h' : S → ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = g i) (hh' : ∀ i, h' i - (P *ᵥ h') i = g i) (y z : S) :
    h y - h' y = h z - h' z := by
  have hd : P *ᵥ (h - h') = h - h' := by
    funext i
    simp only [mulVec_sub, Pi.sub_apply]
    have := hh i
    have := hh' i
    linarith
  have := eq_of_mulVec_eq_self_of_irreducible hP0 hP1 hirr hd y z
  simpa only [Pi.sub_apply] using this

/-- Poisson's equation has a solution normalised by `μ(h) = 0`. -/
theorem exists_poisson_normalized [Nonempty S] [DecidableEq S] {P : Matrix S S ℝ}
    (hP0 : ∀ i j, 0 ≤ P i j) (hP1 : ∀ i, ∑ j, P i j = 1) (hirr : ∀ i j, ∃ k, 0 < (P ^ k) i j)
    {μ : S → ℝ} (hμ : IsStationaryDistribution P μ) (f : S → ℝ) :
    ∃ h : S → ℝ, (∀ i, h i - (P *ᵥ h) i = f i - μ ⬝ᵥ f) ∧ μ ⬝ᵥ h = 0 := by
  obtain ⟨h, hh⟩ := exists_poisson hP0 hP1 hirr hμ f
  refine ⟨fun i => h i - μ ⬝ᵥ h, fun i => ?_, ?_⟩
  · have e : P *ᵥ (fun i => h i - μ ⬝ᵥ h) = P *ᵥ h - fun _ => μ ⬝ᵥ h := by
      have e1 : (fun i => h i - μ ⬝ᵥ h) = h - (μ ⬝ᵥ h) • fun _ => (1 : ℝ) := by
        funext i
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one]
      rw [e1, mulVec_sub, mulVec_smul, mulVec_const_one hP1]
      funext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    rw [e, Pi.sub_apply]
    have := hh i
    linarith
  · rw [dotProduct_sub_const, hμ.sum_eq_one, mul_one, sub_self]

end RQMCMarkov.MarkovDriving

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # Chentsov's theorem for irreducible chains (post #3)

Post #3: "if the QMC method we use is 'completely uniformly distributed' … then the generated
Markov simulations are consistent for the empirical state frequencies and time averages
(Chentsov, 1967)". In the post's terms, for an **irreducible** chain (`∀ i j, ∃ k, Pᵏ(i,j) > 0`,
periodic chains allowed) the stationary distribution `π` is unique (`OccupationPoisson`), so
`ChentsovGeneral` applies.

**Results.**
* `stationary_unique_of_irreducible`: every stationary probability vector of an irreducible `P`
  is `π` (the uniqueness hypothesis of `ChentsovGeneral`).
* `tendsto_occFreq_of_isCUD_irreducible`: `N_j(T)/T → π_j` for every start and every CUD `u`.
* `tendsto_timeAvg_of_isCUD_irreducible`: `(1/T) ∑_{t<T} g(x_t) → ∑_j π_j g(j)`.
* `ae_tendsto_occFreq_iidUniform_irreducible`: since i.i.d. uniform sequences are CUD almost
  surely (`ae_isCUD_iidUniform`), the same holds for almost every MC driving sequence — the
  theorem is not vacuous, and it contains the MC ergodic theorem for the inverse-CDF chain.
-/

namespace RQMCMarkov.MarkovDriving

open Filter Topology Finset

variable {n : ℕ}

/-- For an irreducible stochastic matrix, every stationary probability vector (in sum form) is
the stationary distribution `π`. -/
theorem stationary_unique_of_irreducible {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsStochastic P)
    (hirr : ∀ i j, ∃ k, 0 < (P ^ k) i j) {π : Fin n → ℝ} (hπ : IsStationaryDistribution P π)
    (x₀ : Fin n) (ρ : Fin n → ℝ) (hρ : ∀ j, ∑ i, ρ i * P i j = ρ j) (_hρ0 : ∀ i, 0 ≤ ρ i)
    (hρ1 : ∑ i, ρ i = 1) : ρ = π := by
  have : Nonempty (Fin n) := ⟨x₀⟩
  exact hπ.eq_of_vecMul_eq_self hP.nonneg hP.sum_eq_one hirr (funext hρ) hρ1

/-- **Chentsov's theorem for irreducible chains** (post #3). For an irreducible stochastic
matrix `P` (periodic allowed) with stationary distribution `π` and any CUD sequence `u`, the
path driven by `u` through the inverse-CDF update has `N_j(T)/T → π_j`, from every start. -/
theorem tendsto_occFreq_of_isCUD_irreducible {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : IsStochastic P) (hirr : ∀ i j, ∃ k, 0 < (P ^ k) i j) {π : Fin n → ℝ}
    (hπ : IsStationaryDistribution P π) {u : ℕ → ℝ} (hu : IsCUD u) (x₀ j : Fin n) :
    Tendsto (fun T => (occCount (drivenPath P x₀ u) j T : ℝ) / T) atTop (𝓝 (π j)) :=
  tendsto_occFreq_of_isCUD_general hP hu (stationary_unique_of_irreducible hP hirr hπ x₀) x₀ j

/-- **Time averages for irreducible chains** (post #3): `(1/T) ∑_{t<T} g(x_t) → ∑_j π_j g(j)`. -/
theorem tendsto_timeAvg_of_isCUD_irreducible {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : IsStochastic P) (hirr : ∀ i j, ∃ k, 0 < (P ^ k) i j) {π : Fin n → ℝ}
    (hπ : IsStationaryDistribution P π) {u : ℕ → ℝ} (hu : IsCUD u) (x₀ : Fin n)
    (g : Fin n → ℝ) :
    Tendsto (fun T => (∑ t ∈ range T, g (drivenPath P x₀ u t)) / T) atTop
      (𝓝 (∑ j, π j * g j)) :=
  tendsto_timeAvg_of_isCUD_general hP hu (stationary_unique_of_irreducible hP hirr hπ x₀) x₀ g

/-- **Not vacuous:** for almost every i.i.d. `U[0,1)` driving sequence (which is CUD a.s.), the
occupation frequencies of an irreducible chain converge to `π`, for every start and state. -/
theorem ae_tendsto_occFreq_iidUniform_irreducible {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : IsStochastic P) (hirr : ∀ i j, ∃ k, 0 < (P ^ k) i j) {π : Fin n → ℝ}
    (hπ : IsStationaryDistribution P π) :
    ∀ᵐ u ∂(iidUniform ℕ), ∀ x₀ j : Fin n,
      Tendsto (fun T => (occCount (drivenPath P x₀ u) j T : ℝ) / T) atTop (𝓝 (π j)) := by
  filter_upwards [ae_isCUD_iidUniform] with u hu x₀ j
  exact tendsto_occFreq_of_isCUD_irreducible hP hirr hπ hu x₀ j

end RQMCMarkov.MarkovDriving

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Conditional MC: given its transition counts, the MC path is uniform (post #3)

Post #3's "conditional MC" fixes the transition counts `n_ij` and samples "uniformly among all
paths with those counts", noting that "these paths are Eulerian trails"; its approach (v), a
uniformly random path with the counts of the rotor path, "is exactly MC conditional on the
counts". Reading: for MC from a fixed start `x₀`, conditioning the law of `(x_0, …, x_T)` on the
event "transition counts equal `N`" gives the uniform distribution on the paths that start at
`x₀` and have counts `N` (the start is part of the conditioning: the counts determine the end
state but, for a circulation, not the start).

## Main results

* `prod_eq_prod_pow_transCount`, `pathProb_eq_prod_pow`, `pathProb_eq_of_transCount_eq`: a
  path's MC probability is `1{s_0 = x₀} ∏_{i,j} P i j ^ transCount s i j T`, so it depends only
  on the start and the transition counts.
* `countClass x₀ N T`, `mem_countClass`: the finite paths with start `x₀` and counts `N`;
  `mcLaw P x₀ T`, the MC law of `(x_0, …, x_T)`; `mcLaw_singleton_of_mem`.
* `cond_mcLaw_countClass`: **MC conditional on the counts is uniform**,
  `(mcLaw P x₀ T)[| countClass x₀ N T] = uniformOn (countClass x₀ N T)` whenever the conditioning
  event has positive probability. (By `map_drivenPath_eq_map_stackPath` the same holds for i.i.d.
  stacks.)
* `BalancedCounts N a b` (out-count − in-count `= 1{a = i} − 1{b = i}`), `balanced_transCount`.
* `exists_path_of_balanced`: **Euler's theorem** for directed multigraphs — balanced counts
  whose support is reachable from `x₀` are the transition counts of some path from `x₀` to `b`
  of length `Σ N` (an Eulerian trail). Proof: a longest trail ends at `b` and leaves a
  circulation (`IsCountTrail.end_eq`); if anything is unused, a closed trail of the circulation
  (`exists_closed_trail`) can be spliced in at a visited state (`transCount_splice`),
  contradicting maximality.
* `reachable_of_transCount_ne_zero`, `exists_path_iff`: conversely, the counts of any path are
  balanced and connected, so these conditions characterise the realisable count matrices.

Not formalised: the BEST theorem (counting Eulerian trails via spanning trees) and the exact
sampler built on it (post #3: "the BEST theorem with a random spanning tree gives an exact
sampler"). The rounding of `T π_i p_ij` to balanced integer counts is in `ConditionalMCRounding`
and `ConditionalMCRoundingOpen`.
-/

namespace RQMCMarkov.MarkovDriving

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

variable {S : Type*} [DecidableEq S] [Fintype S]

/-- One transition, as a product of powers: `∏_{i,j} f i j ^ 1{a = i ∧ b = j} = f a b`. -/
theorem prod_prod_pow_ite_eq (f : S → S → ℝ) (a b : S) :
    ∏ i, ∏ j, f i j ^ (if a = i ∧ b = j then 1 else 0) = f a b := by
  rw [Fintype.prod_eq_single a fun i hi ↦ Finset.prod_eq_one fun j _ ↦ by
    simp only [Ne.symm hi, false_and, ↓reduceIte, pow_zero]]
  rw [Fintype.prod_eq_single b fun j hj ↦ by simp only [Ne.symm hj, and_false, ↓reduceIte,
    pow_zero]]
  simp only [and_self, ↓reduceIte, pow_one]

/-- **The path probability depends only on the transition counts** (post #3, conditional MC):
`∏_{t<T} P (s t) (s (t+1)) = ∏_{i,j} P i j ^ transCount s i j T`. -/
theorem prod_eq_prod_pow_transCount (P : S → S → ℝ) (s : ℕ → S) (T : ℕ) :
    ∏ t ∈ range T, P (s t) (s (t + 1)) = ∏ i, ∏ j, P i j ^ transCount s i j T := by
  induction T with
  | zero =>
    rw [Finset.prod_range_zero]
    exact (Finset.prod_eq_one fun i _ ↦ Finset.prod_eq_one fun j _ ↦ pow_zero _).symm
  | succ T ih =>
    rw [Finset.prod_range_succ, ih]
    simp only [transCount_succ, pow_add]
    rw [← prod_prod_pow_ite_eq P (s T) (s (T + 1)), ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ ↦ (Finset.prod_mul_distrib).symm

/-- `pathProb` through the transition counts. -/
theorem pathProb_eq_prod_pow (P : S → S → ℝ) (x₀ : S) (s : ℕ → S) (T : ℕ) :
    pathProb P x₀ s T = if s 0 = x₀ then ∏ i, ∏ j, P i j ^ transCount s i j T else 0 := by
  unfold pathProb
  rw [prod_eq_prod_pow_transCount]

omit [Fintype S] in
/-- Two paths with the same start and the same transition counts have the same probability
under MC. -/
theorem pathProb_eq_of_transCount_eq [Finite S] (P : S → S → ℝ) (x₀ : S) {s s' : ℕ → S}
    {T : ℕ} (h0 : s 0 = s' 0) (hN : ∀ i j, transCount s i j T = transCount s' i j T) :
    pathProb P x₀ s T = pathProb P x₀ s' T := by
  have := Fintype.ofFinite S
  rw [pathProb_eq_prod_pow, pathProb_eq_prod_pow, h0]
  simp only [hN]

/-- The finite paths `(s_0, …, s_T)` that start at `x₀` and have transition counts `N`. -/
noncomputable def countClass (x₀ : S) (N : S → S → ℕ) (T : ℕ) : Finset (Fin (T + 1) → S) :=
  univ.filter fun s ↦ extendPath s 0 = x₀ ∧ ∀ i j, transCount (extendPath s) i j T = N i j

/-- Membership in `countClass`. -/
theorem mem_countClass {x₀ : S} {N : S → S → ℕ} {T : ℕ} {s : Fin (T + 1) → S} :
    s ∈ countClass x₀ N T ↔
      extendPath s 0 = x₀ ∧ ∀ i j, transCount (extendPath s) i j T = N i j := by
  unfold countClass
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ s)

variable {n : ℕ}

/-- The law of the first `T + 1` states of MC: `drivenPath` under i.i.d. uniforms. -/
noncomputable def mcLaw (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (T : ℕ) :
    Measure (Fin (T + 1) → Fin n) :=
  (iidUniform ℕ).map fun u t ↦ drivenPath P x₀ u (t : Fin (T + 1))

/-- Under MC, every path of `countClass x₀ N T` has probability `∏_{i,j} P i j ^ N i j`. -/
theorem mcLaw_singleton_of_mem {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (x₀ : Fin n)
    (N : Fin n → Fin n → ℕ) (T : ℕ) {s : Fin (T + 1) → Fin n} (hs : s ∈ countClass x₀ N T) :
    mcLaw P x₀ T {s} = ENNReal.ofReal (∏ i, ∏ j, P i j ^ N i j) := by
  unfold mcLaw
  rw [map_drivenPath_singleton hP, pathProb_eq_prod_pow]
  rw [mem_countClass] at hs
  simp only [hs.1, hs.2, ↓reduceIte]

/-- **MC conditional on the counts is uniform** (post #3: the uniformly random path with fixed
counts "is exactly MC conditional on the counts"): conditioned on starting at `x₀` and having
transition counts `N` (an event of positive probability), the law of the MC path
`(x_0, …, x_T)` is the uniform distribution on the paths with those counts. -/
theorem cond_mcLaw_countClass {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (x₀ : Fin n)
    (N : Fin n → Fin n → ℕ) (T : ℕ) (hC : mcLaw P x₀ T (countClass x₀ N T : Set _) ≠ 0) :
    (mcLaw P x₀ T)[|(countClass x₀ N T : Set _)] = uniformOn (countClass x₀ N T : Set _) := by
  set C := countClass x₀ N T with hCdef
  set m := ENNReal.ofReal (∏ i, ∏ j, P i j ^ N i j) with hm
  have hμC : mcLaw P x₀ T (C : Set _) = (C.card : ℝ≥0∞) * m := by
    rw [← sum_measure_singleton, Finset.sum_congr rfl fun s hs ↦
      mcLaw_singleton_of_mem hP x₀ N T hs, Finset.sum_const, nsmul_eq_mul]
  have hm0 : m ≠ 0 := by
    intro h
    rw [hμC, h, mul_zero] at hC
    exact hC rfl
  have hk0 : (C.card : ℝ≥0∞) ≠ 0 := by
    intro h
    rw [hμC, h, zero_mul] at hC
    exact hC rfl
  refine Measure.ext_of_singleton fun s ↦ ?_
  rw [cond_apply C.measurableSet, ← Finset.coe_singleton, uniformOn_apply_finset]
  by_cases hs : s ∈ C
  · rw [Finset.inter_singleton_of_mem hs, Finset.coe_singleton, Set.inter_eq_right.2
      (Set.singleton_subset_iff.2 hs), mcLaw_singleton_of_mem hP x₀ N T hs, hμC, ← hm,
      Finset.card_singleton, Nat.cast_one, one_div,
      ENNReal.mul_inv (Or.inl hk0) (Or.inr hm0), mul_assoc,
      ENNReal.inv_mul_cancel hm0 ENNReal.ofReal_ne_top, mul_one]
  · rw [Finset.inter_singleton_of_notMem hs, Finset.card_empty, Nat.cast_zero, ENNReal.zero_div,
      Finset.coe_singleton, Set.inter_singleton_eq_empty.2 hs, measure_empty, mul_zero]

/-! ### Euler's theorem for count matrices -/

/-- A count matrix `N` is **balanced from `a` to `b`**: at every state, out-count minus
in-count is `1{a = i} − 1{b = i}` (post #3, "every state is entered as often as it is left
(allowing for the first and last states)"). With `a = b` this is a circulation. -/
def BalancedCounts (N : S → S → ℕ) (a b : S) : Prop :=
  ∀ i, (∑ j, (N i j : ℤ)) - ∑ j, (N j i : ℤ) = (if a = i then 1 else 0) - if b = i then 1 else 0

/-- The transition counts of any path are balanced from its start to its end. -/
theorem balanced_transCount (s : ℕ → S) (T : ℕ) :
    BalancedCounts (fun i j ↦ transCount s i j T) (s 0) (s T) := by
  intro i
  have := flowBalance s i T
  push_cast at this
  exact this

omit [Fintype S] in
/-- A **trail** of length `L` from `x₀` in the count matrix `N`: a path from `x₀` whose first
`L` transitions use each `i → j` at most `N i j` times. -/
def IsCountTrail (N : S → S → ℕ) (x₀ : S) (s : ℕ → S) (L : ℕ) : Prop :=
  s 0 = x₀ ∧ ∀ i j, transCount s i j L ≤ N i j

omit [Fintype S] in
/-- The empty trail. -/
theorem isCountTrail_zero (N : S → S → ℕ) (x₀ : S) : IsCountTrail N x₀ (fun _ ↦ x₀) 0 :=
  ⟨rfl, fun i j ↦ (transCount_zero _ i j).symm ▸ Nat.zero_le _⟩

/-- A trail is no longer than the total count. -/
theorem IsCountTrail.le_sum {N : S → S → ℕ} {x₀ : S} {s : ℕ → S} {L : ℕ}
    (h : IsCountTrail N x₀ s L) : L ≤ ∑ i, ∑ j, N i j := by
  rw [← sum_sum_transCount s L]
  exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ h.2 i j

omit [Fintype S] in
/-- A trail can be extended by any unused transition out of its endpoint. -/
theorem IsCountTrail.extend {N : S → S → ℕ} {x₀ : S} {s : ℕ → S} {L : ℕ} (h : IsCountTrail N x₀ s L)
    (z : S) (hz : transCount s (s L) z L < N (s L) z) :
    IsCountTrail N x₀ (Function.update s (L + 1) z) (L + 1) := by
  have hagree : ∀ t ≤ L, Function.update s (L + 1) z t = s t := fun t ht ↦
    Function.update_of_ne (by omega) _ _
  refine ⟨?_, fun i j ↦ ?_⟩
  · rw [hagree 0 (Nat.zero_le L)]
    exact h.1
  · rw [transCount_succ, transCount_congr hagree, hagree L le_rfl, Function.update_self]
    by_cases hij : s L = i ∧ z = j
    · obtain ⟨rfl, rfl⟩ := hij
      simp only [and_self, ↓reduceIte]
      omega
    · simp only [hij, ↓reduceIte, add_zero]
      exact h.2 i j

omit [Fintype S] in
/-- A trail of maximal length exists (finite state space). -/
theorem exists_maximal_trail [Finite S] (N : S → S → ℕ) (x₀ : S) :
    ∃ L s, IsCountTrail N x₀ s L ∧ ∀ L' s', IsCountTrail N x₀ s' L' → L' ≤ L := by
  classical
  have := Fintype.ofFinite S
  let Q : ℕ → Prop := fun L ↦ ∃ s, IsCountTrail N x₀ s L
  have hQ0 : Q 0 := ⟨_, isCountTrail_zero N x₀⟩
  obtain ⟨s, hs⟩ := Nat.findGreatest_spec (P := Q) (Nat.zero_le (∑ i, ∑ j, N i j)) hQ0
  exact ⟨_, s, hs, fun L' s' h' ↦ Nat.le_findGreatest h'.le_sum ⟨s', h'⟩⟩

/-- **A trail that cannot be extended ends at `b`**, for counts balanced from `a` to `b`, and
the unused counts form a circulation. -/
theorem IsCountTrail.end_eq {N : S → S → ℕ} {x₀ y : S} (hbal : BalancedCounts N x₀ y) {s : ℕ → S}
    {L : ℕ} (h : IsCountTrail N x₀ s L) (hmax : ∀ z, N (s L) z ≤ transCount s (s L) z L) :
    s L = y ∧ ∀ a, BalancedCounts (fun i j ↦ N i j - transCount s i j L) a a := by
  have hcast : ∀ i j, ((N i j - transCount s i j L : ℕ) : ℤ) = N i j - transCount s i j L :=
    fun i j ↦ Nat.cast_sub (h.2 i j)
  have hdiff : ∀ v, (∑ j, ((N v j - transCount s v j L : ℕ) : ℤ)) -
      ∑ j, ((N j v - transCount s j v L : ℕ) : ℤ) =
        (if s L = v then 1 else 0) - if y = v then 1 else 0 := by
    intro v
    simp only [hcast, Finset.sum_sub_distrib]
    have h1 := hbal v
    have h2 := balanced_transCount s L v
    rw [h.1] at h2
    linarith
  have hout : ∑ j, ((N (s L) j - transCount s (s L) j L : ℕ) : ℤ) = 0 :=
    Finset.sum_eq_zero fun j _ ↦ by rw [Nat.sub_eq_zero_of_le (hmax j), Nat.cast_zero]
  have hin : 0 ≤ ∑ j, ((N j (s L) - transCount s j (s L) L : ℕ) : ℤ) :=
    Finset.sum_nonneg fun j _ ↦ Nat.cast_nonneg _
  have hend : s L = y := by
    by_contra hne
    have := hdiff (s L)
    rw [hout] at this
    simp only [↓reduceIte, Ne.symm hne] at this
    linarith
  refine ⟨hend, fun a v ↦ ?_⟩
  rw [hdiff v, hend, sub_self, sub_self]

/-- **A circulation with an edge out of `v` contains a closed trail at `v`.** -/
theorem exists_closed_trail {R : S → S → ℕ} {v : S} (hbal : BalancedCounts R v v) {j : S}
    (hj : R v j ≠ 0) : ∃ K c, 1 ≤ K ∧ IsCountTrail R v c K ∧ c K = v := by
  obtain ⟨L, c, hc, hmax⟩ := exists_maximal_trail R v
  have hnext : ∀ z, R (c L) z ≤ transCount c (c L) z L := fun z ↦ by
    by_contra hz
    have := hmax _ _ (hc.extend z (not_le.1 hz))
    omega
  have h1 : 1 ≤ L := hmax 1 _ ((isCountTrail_zero R v).extend j (by
    rw [transCount_zero]
    exact Nat.pos_of_ne_zero hj))
  exact ⟨L, c, h1, hc, (hc.end_eq hbal hnext).1⟩

omit [Fintype S] in
/-- **Splicing** a path `c` into `s` at time `t₀`: follow `s` up to `t₀`, then `c` for `K`
steps, then the rest of `s`. -/
def splice (s c : ℕ → S) (t₀ K : ℕ) (t : ℕ) : S :=
  if t ≤ t₀ then s t else if t ≤ t₀ + K then c (t - t₀) else s (t - K)

omit [Fintype S] in
/-- Splicing a closed path `c` at a visit of `s` to its base point adds the counts. -/
theorem transCount_splice {s c : ℕ → S} {t₀ K L : ℕ} (hc0 : c 0 = s t₀) (hcK : c K = s t₀)
    (ht₀ : t₀ ≤ L) (i j : S) :
    transCount (splice s c t₀ K) i j (L + K) = transCount s i j L + transCount c i j K := by
  have hL : L + K = t₀ + (K + (L - t₀)) := by omega
  have h1 : transCount (splice s c t₀ K) i j t₀ = transCount s i j t₀ :=
    transCount_congr (fun t ht ↦ by simp only [splice, ht, ↓reduceIte]) i j
  have h2 : transCount (fun t ↦ splice s c t₀ K (t₀ + t)) i j K = transCount c i j K := by
    refine transCount_congr (fun t ht ↦ ?_) i j
    unfold splice
    split_ifs with h h'
    · rw [show t = 0 by omega, add_zero, hc0]
    · rw [Nat.add_sub_cancel_left]
    · omega
  have h3 : transCount (fun t ↦ splice s c t₀ K (t₀ + (K + t))) i j (L - t₀) =
      transCount (fun t ↦ s (t₀ + t)) i j (L - t₀) := by
    refine transCount_congr (fun t _ ↦ ?_) i j
    unfold splice
    split_ifs with h h'
    · rw [show t = 0 by omega, show K = 0 by omega]
    · rw [show t = 0 by omega, add_zero, Nat.add_sub_cancel_left, hcK, add_zero]
    · congr 1
      omega
  have h4 := transCount_add s i j t₀ (L - t₀)
  rw [Nat.add_sub_cancel' ht₀] at h4
  rw [hL, transCount_add, transCount_add (fun t ↦ splice s c t₀ K (t₀ + t)), h1, h2, h3, h4]
  ring

/-- **Euler's theorem for directed multigraphs** (post #3: "these paths are Eulerian trails"):
if the count matrix `N` is balanced from `x₀` to `y` and every state with an outgoing count is
reachable from `x₀` through positive counts, then some path from `x₀` to `y` of length
`T = Σ N` realises exactly the counts `N`. -/
theorem exists_path_of_balanced {N : S → S → ℕ} {x₀ y : S} (hbal : BalancedCounts N x₀ y)
    (hconn : ∀ i j, N i j ≠ 0 → Relation.ReflTransGen (fun a b ↦ N a b ≠ 0) x₀ i) :
    ∃ s : ℕ → S, s 0 = x₀ ∧ s (∑ i, ∑ j, N i j) = y ∧
      ∀ i j, transCount s i j (∑ i, ∑ j, N i j) = N i j := by
  obtain ⟨L, s, hs, hmax⟩ := exists_maximal_trail N x₀
  have hnext : ∀ z, N (s L) z ≤ transCount s (s L) z L := fun z ↦ by
    by_contra hz
    have := hmax _ _ (hs.extend z (not_le.1 hz))
    omega
  obtain ⟨hend, hR⟩ := hs.end_eq hbal hnext
  by_cases hzero : ∀ i j, N i j - transCount s i j L = 0
  · have hC : ∀ i j, transCount s i j L = N i j := fun i j ↦
      le_antisymm (hs.2 i j) (Nat.sub_eq_zero_iff_le.1 (hzero i j))
    have hLT : L = ∑ i, ∑ j, N i j := by
      rw [← sum_sum_transCount s L]
      exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ hC i j
    rw [← hLT]
    exact ⟨s, hs.1, hend, hC⟩
  · exfalso
    push Not at hzero
    obtain ⟨a, b, hab⟩ := hzero
    have hon : ∃ t₀ ≤ L, ∃ j, N (s t₀) j - transCount s (s t₀) j L ≠ 0 := by
      by_contra hno
      push Not at hno
      have key : ∀ v, Relation.ReflTransGen (fun a b ↦ N a b ≠ 0) x₀ v → ∃ t ≤ L, s t = v := by
        intro v hv
        induction hv with
        | refl => exact ⟨0, Nat.zero_le L, hs.1⟩
        | @tail b' c' _ hbc ih =>
          obtain ⟨t, ht, rfl⟩ := ih
          have hpos : transCount s (s t) c' L ≠ 0 := by
            have := hno t ht c'
            omega
          obtain ⟨t', ht'⟩ := Finset.card_ne_zero.1 hpos
          rw [Finset.mem_filter, Finset.mem_range] at ht'
          exact ⟨t' + 1, ht'.1, ht'.2.2⟩
      obtain ⟨t, ht, hst⟩ := key a (hconn a b (by omega))
      exact hab (hst ▸ hno t ht b)
    obtain ⟨t₀, ht₀, j, hj⟩ := hon
    obtain ⟨K, c, hK, hc, hcK⟩ := exists_closed_trail (hR (s t₀)) hj
    have htrail : IsCountTrail N x₀ (splice s c t₀ K) (L + K) := by
      refine ⟨by simp only [splice, Nat.zero_le, ↓reduceIte, hs.1], fun i j ↦ ?_⟩
      rw [transCount_splice hc.1 hcK ht₀]
      have h1 := hc.2 i j
      have h2 := hs.2 i j
      beta_reduce at h1
      omega
    have := hmax _ _ htrail
    omega

omit [Fintype S] in
/-- **Converse of Euler's theorem**: the support of the transition counts of a path is
reachable from its start. -/
theorem reachable_of_transCount_ne_zero (s : ℕ → S) (T : ℕ) {i j : S}
    (h : transCount s i j T ≠ 0) :
    Relation.ReflTransGen (fun a b ↦ transCount s a b T ≠ 0) (s 0) i := by
  obtain ⟨t, ht⟩ := Finset.card_ne_zero.1 h
  rw [Finset.mem_filter, Finset.mem_range] at ht
  rw [← ht.2.1]
  have key : ∀ t' ≤ t, Relation.ReflTransGen (fun a b ↦ transCount s a b T ≠ 0) (s 0) (s t') := by
    intro t' ht'
    induction t' with
    | zero => exact Relation.ReflTransGen.refl
    | succ t' ih =>
      refine (ih (by omega)).tail ?_
      refine Finset.card_ne_zero.2 ⟨t', ?_⟩
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, rfl, rfl⟩
  exact key t le_rfl

/-- **Paths with given counts exist iff the counts are balanced and connected**: there is a
path of length `T = Σ N` from `x₀` to `y` with transition counts exactly `N` iff `N` is
balanced from `x₀` to `y` and its support is reachable from `x₀`. -/
theorem exists_path_iff {N : S → S → ℕ} {x₀ y : S} :
    (∃ s : ℕ → S, s 0 = x₀ ∧ s (∑ i, ∑ j, N i j) = y ∧
      ∀ i j, transCount s i j (∑ i, ∑ j, N i j) = N i j) ↔
    BalancedCounts N x₀ y ∧
      ∀ i j, N i j ≠ 0 → Relation.ReflTransGen (fun a b ↦ N a b ≠ 0) x₀ i := by
  constructor
  · rintro ⟨s, h0, hT, hN⟩
    have hfun : N = fun i j ↦ transCount s i j (∑ i, ∑ j, N i j) :=
      funext fun i ↦ funext fun j ↦ (hN i j).symm
    constructor
    · have := balanced_transCount s (∑ i, ∑ j, N i j)
      rw [h0, hT, ← hfun] at this
      exact this
    · intro i j hij
      have := reachable_of_transCount_ne_zero s (∑ i, ∑ j, N i j) (i := i) (j := j)
        (by rw [hN]; exact hij)
      have hr : (fun a b ↦ transCount s a b (∑ i, ∑ j, N i j) ≠ 0) = fun a b ↦ N a b ≠ 0 := by
        funext a b
        rw [hN]
      rw [h0, hr] at this
      exact this
  · rintro ⟨hbal, hconn⟩
    exact exists_path_of_balanced hbal hconn

end RQMCMarkov.MarkovDriving

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Rounding the expected transition counts to balanced integer counts (post #3)

Post #3's conditional MC: "we want to get counts `n_ij = T π_i p_ij`, rounded so that every state
is entered as often as it is left (allowing for the first and last states)", then sample a path
with those counts. Reading: `π` is a stationary distribution of the stochastic matrix `P`, the
real matrix `x_ij = T π_i p_ij` (`expectedCounts`) is to be rounded entrywise (`⌊x_ij⌋ ≤ n_ij ≤
⌈x_ij⌉`) to an integer matrix with equal row and column sums (a circulation), and a path is
then a closed path realising `n`.

## Main results

* `IsCirculation`, `netFlow`, `sum_netFlow_eq_cut` (the cut identity).
* `isCirculation_expectedCounts`, `sum_expectedCounts`: `x_ij = T π_i p_ij` is a circulation
  (row `i` and column `i` both sum to `T π_i`) with total `T`.
* `exists_cycle_direction`: a fractional entry of a real circulation lies on a cycle of
  fractional entries (proved by a cut argument on the states reachable through fractional arcs).
* `exists_int_circulation_rounding`: **circulation rounding** — every real circulation has an
  integer circulation rounding `⌊x_ij⌋ ≤ n_ij ≤ ⌈x_ij⌉` (cycle cancelling on the fractional
  entries).
* `exists_rounding_expectedCounts`: post #3's rounding exists, with `|n_ij − T π_i p_ij| < 1` and
  `Σ ⌊x_ij⌋ ≤ Σ n_ij ≤ Σ ⌈x_ij⌉`.
* `exists_closed_path_of_rounding`: for irreducible `P` and `T π_i p_ij ≥ 1` on the support of
  `P`, the rounded counts have the support of `P`, are balanced at every state, and are realised
  by a closed path from any `x₀` (Euler, `exists_path_of_balanced`).
* `conditionalMC_wellDefined`: the conditioning event of post #3's conditional MC then has
  positive MC probability, and the conditional law is uniform over the paths with the counts.

**Correction.** The total of the rounded circulation cannot always be made `⌊T⌋` or `⌈T⌉`, so the
balanced path may have to have length `Σ n ≠ T`: `not_exists_rounding_flipChain_total_three`
(the flip chain `[[0,1],[1,0]]`, `π = (1/2, 1/2)`, `T = 3`: every integer circulation has
`n_01 = n_10`, so an even total). The post's "allowing for the first and last states" (open
paths, counts balanced from the first to the last state) is what can repair the length; that
version is `ConditionalMCRoundingOpen`. The BEST count of the paths is not formalised.
-/

namespace RQMCMarkov.MarkovDriving

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

variable {S : Type*} [Fintype S]

/-! ### Circulations -/

/-- Net outflow `Σ_j z v j − Σ_j z j v` of a real matrix at the state `v`. -/
def netFlow (z : S → S → ℝ) (v : S) : ℝ := ∑ j, z v j - ∑ j, z j v

/-- A real matrix is a **circulation** when every row sum equals the column sum ("every state is
entered as often as it is left"). -/
def IsCirculation (z : S → S → ℝ) : Prop := ∀ v, ∑ j, z v j = ∑ j, z j v

/-- Circulations are the matrices with zero net outflow everywhere. -/
theorem isCirculation_iff_netFlow (z : S → S → ℝ) : IsCirculation z ↔ ∀ v, netFlow z v = 0 :=
  forall_congr' fun _ ↦ sub_eq_zero.symm

/-- `netFlow` is additive. -/
theorem netFlow_add (z z' : S → S → ℝ) (v : S) :
    netFlow (fun i j ↦ z i j + z' i j) v = netFlow z v + netFlow z' v := by
  unfold netFlow
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

/-- `netFlow` is subtractive. -/
theorem netFlow_sub (z z' : S → S → ℝ) (v : S) :
    netFlow (fun i j ↦ z i j - z' i j) v = netFlow z v - netFlow z' v := by
  unfold netFlow
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  ring

/-- `netFlow` is homogeneous. -/
theorem netFlow_mul (t : ℝ) (z : S → S → ℝ) (v : S) :
    netFlow (fun i j ↦ t * z i j) v = t * netFlow z v := by
  unfold netFlow
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

variable [DecidableEq S]

/-- The net outflow of a single arc `a → b` carrying `c`. -/
theorem netFlow_single (a b : S) (c : ℝ) (v : S) :
    netFlow (fun i j ↦ if i = a ∧ j = b then c else 0) v =
      (if v = a then c else 0) - if v = b then c else 0 := by
  unfold netFlow
  congr 1
  · by_cases hva : v = a
    · simp only [hva, true_and, ↓reduceIte]
      rw [Finset.sum_ite_eq']
      simp only [Finset.mem_univ, ↓reduceIte]
    · simp only [hva, false_and, ↓reduceIte, Finset.sum_const_zero]
  · by_cases hvb : v = b
    · simp only [hvb, and_true, ↓reduceIte]
      rw [Finset.sum_ite_eq']
      simp only [Finset.mem_univ, ↓reduceIte]
    · simp only [hvb, and_false, ↓reduceIte, Finset.sum_const_zero]

/-- **The cut identity**: the total net outflow of a set `R` of states is the flow on arcs
leaving `R` minus the flow on arcs entering `R`. -/
theorem sum_netFlow_eq_cut (z : S → S → ℝ) (R : Finset S) :
    ∑ v ∈ R, netFlow z v = ∑ v ∈ R, ∑ j ∈ Rᶜ, z v j - ∑ v ∈ R, ∑ j ∈ Rᶜ, z j v := by
  unfold netFlow
  rw [Finset.sum_sub_distrib]
  have h1 : ∀ v, ∑ j, z v j = ∑ j ∈ R, z v j + ∑ j ∈ Rᶜ, z v j := fun v ↦
    (Finset.sum_add_sum_compl R _).symm
  have h2 : ∀ v, ∑ j, z j v = ∑ j ∈ R, z j v + ∑ j ∈ Rᶜ, z j v := fun v ↦
    (Finset.sum_add_sum_compl R _).symm
  simp only [h1, h2, Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := R) (t := R) (f := fun v j ↦ z v j)]
  ring

/-! ### Integer points and the fractional-arc graph -/

/-- The integers inside `ℝ`, as an additive subgroup. -/
noncomputable abbrev intLattice : AddSubgroup ℝ := (Int.castAddHom ℝ).range

/-- Membership in `intLattice`. -/
theorem mem_intLattice {z : ℝ} : z ∈ intLattice ↔ ∃ k : ℤ, (k : ℝ) = z := by
  rw [AddMonoidHom.mem_range]
  rfl

/-- Integers lie in `intLattice`. -/
theorem intCast_mem_intLattice (k : ℤ) : (k : ℝ) ∈ intLattice := mem_intLattice.2 ⟨k, rfl⟩

/-- Adjacency through **fractional arcs other than `e`**, in either direction. -/
def fracAdj (y : S → S → ℝ) (e : S × S) (u v : S) : Prop :=
  ((u, v) ≠ e ∧ y u v ∉ intLattice) ∨ ((v, u) ≠ e ∧ y v u ∉ intLattice)

/-- A chain of fractional arcs from `u` to `w` carries a flow with net outflow `1{u} − 1{w}`,
supported on fractional arcs other than `e`. -/
theorem exists_pathFlow (y : S → S → ℝ) (e : S × S) {u w : S}
    (h : Relation.ReflTransGen (fracAdj y e) u w) :
    ∃ d : S → S → ℝ, (∀ v, netFlow d v = (if v = u then 1 else 0) - if v = w then 1 else 0) ∧
      ∀ i j, d i j ≠ 0 → (i, j) ≠ e ∧ y i j ∉ intLattice := by
  induction h with
  | refl =>
    refine ⟨fun _ _ ↦ 0, fun v ↦ ?_, fun i j h ↦ (h rfl).elim⟩
    unfold netFlow
    rw [Finset.sum_const_zero, sub_self, sub_self]
  | @tail v w _ hvw ih =>
    obtain ⟨d, hd, hs⟩ := ih
    rcases hvw with ⟨hne, hfr⟩ | ⟨hne, hfr⟩
    · refine ⟨fun i j ↦ d i j + if i = v ∧ j = w then 1 else 0, fun z ↦ ?_, fun i j h ↦ ?_⟩
      · rw [netFlow_add, hd, netFlow_single]
        ring
      · by_cases hij : i = v ∧ j = w
        · obtain ⟨rfl, rfl⟩ := hij
          exact ⟨hne, hfr⟩
        · simp only [hij, ↓reduceIte, add_zero] at h
          exact hs i j h
    · refine ⟨fun i j ↦ d i j - if i = w ∧ j = v then 1 else 0, fun z ↦ ?_, fun i j h ↦ ?_⟩
      · rw [netFlow_sub, hd, netFlow_single]
        ring
      · by_cases hij : i = w ∧ j = v
        · obtain ⟨rfl, rfl⟩ := hij
          exact ⟨hne, hfr⟩
        · simp only [hij, ↓reduceIte, sub_zero] at h
          exact hs i j h

omit [DecidableEq S] in
/-- **The cut argument**: for a fractional arc `a → b` of a circulation, `a` is reachable from `b`
through fractional arcs other than `a → b` (otherwise the net outflow of the reachable set would
be an integer minus `y a b`, yet it is `0`). -/
theorem reflTransGen_fracAdj_of_notMem {y : S → S → ℝ} (hy : IsCirculation y) {a b : S}
    (he : y a b ∉ intLattice) : Relation.ReflTransGen (fracAdj y (a, b)) b a := by
  classical
  by_contra hna
  set R := univ.filter fun v ↦ Relation.ReflTransGen (fracAdj y (a, b)) b v with hR
  have hbR : b ∈ R := Finset.mem_filter.2 ⟨Finset.mem_univ _, Relation.ReflTransGen.refl⟩
  have haR : a ∉ R := fun h ↦ hna (Finset.mem_filter.1 h).2
  have hreachR : ∀ {v j}, v ∈ R → fracAdj y (a, b) v j → j ∈ R := fun hv hvj ↦
    Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hv).2.tail hvj⟩
  set z : S → S → ℝ := fun i j ↦ y i j - if i = a ∧ j = b then y a b else 0 with hz
  have hnet : ∀ v,
      netFlow z v = 0 - ((if v = a then y a b else 0) - if v = b then y a b else 0) := fun v ↦ by
      rw [hz, netFlow_sub, netFlow_single, (isCirculation_iff_netFlow y).1 hy v]
  have hsum : ∑ v ∈ R, netFlow z v = y a b := by
    simp only [hnet, Finset.sum_sub_distrib, Finset.sum_const_zero, Finset.sum_ite_eq',
      haR, hbR, ↓reduceIte]
    ring
  have hzint : ∀ i j, ¬ (i = a ∧ j = b) → z i j = y i j := fun i j h ↦ by
    simp only [hz, h, ↓reduceIte, sub_zero]
  have hmem : ∑ v ∈ R, ∑ j ∈ Rᶜ, z v j - ∑ v ∈ R, ∑ j ∈ Rᶜ, z j v ∈ intLattice := by
    refine sub_mem (sum_mem fun v hv ↦ sum_mem fun j hj ↦ ?_)
      (sum_mem fun v hv ↦ sum_mem fun j hj ↦ ?_)
    · have hjR : j ∉ R := Finset.mem_compl.1 hj
      have hab : ¬ (v = a ∧ j = b) := fun h ↦ haR (h.1 ▸ hv)
      rw [hzint v j hab]
      by_contra hfr
      exact hjR (hreachR hv (Or.inl ⟨fun h ↦ hab (Prod.mk.inj h), hfr⟩))
    · have hjR : j ∉ R := Finset.mem_compl.1 hj
      by_cases hab : j = a ∧ v = b
      · simp only [hz, hab, and_self, ↓reduceIte, sub_self]
        exact zero_mem _
      · rw [hzint j v hab]
        by_contra hfr
        exact hjR (hreachR hv (Or.inr ⟨fun h ↦ hab (Prod.mk.inj h), hfr⟩))
  rw [← sum_netFlow_eq_cut, hsum] at hmem
  exact he hmem

omit [DecidableEq S] in
/-- **A fractional arc of a circulation lies on a cycle of fractional arcs**: there is a
circulation `D` with `D a b = 1`, supported on the fractional arcs of `y`. (Cut argument: if `a`
were not reachable from `b` through fractional arcs avoiding `a → b`, the net outflow of the
reachable set would be an integer minus `y a b`, yet it is `0`.) -/
theorem exists_cycle_direction {y : S → S → ℝ} (hy : IsCirculation y) {a b : S}
    (he : y a b ∉ intLattice) :
    ∃ D : S → S → ℝ, IsCirculation D ∧ D a b = 1 ∧ ∀ i j, D i j ≠ 0 → y i j ∉ intLattice := by
  classical
  have hreach := reflTransGen_fracAdj_of_notMem hy he
  obtain ⟨d, hd, hs⟩ := exists_pathFlow y (a, b) hreach
  have hdab : d a b = 0 := by
    by_contra h
    exact (hs a b h).1 rfl
  refine ⟨fun i j ↦ d i j + if i = a ∧ j = b then 1 else 0, ?_, ?_, fun i j h ↦ ?_⟩
  · rw [isCirculation_iff_netFlow]
    intro v
    rw [netFlow_add, hd, netFlow_single]
    ring
  · simp only [and_self, ↓reduceIte, hdab, zero_add]
  · by_cases hij : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := hij
      exact he
    · simp only [hij, ↓reduceIte, add_zero] at h
      exact (hs i j h).2

/-! ### The circulation-rounding theorem -/

omit [DecidableEq S] in
/-- A non-integer real lies strictly between its floor and its ceiling. -/
theorem floor_lt_lt_ceil_of_notMem {z : ℝ} (hz : z ∉ intLattice) :
    (⌊z⌋ : ℝ) < z ∧ z < ⌈z⌉ := by
  refine ⟨lt_of_le_of_ne (Int.floor_le z) fun h ↦ hz (h ▸ intCast_mem_intLattice _),
    lt_of_le_of_ne (Int.le_ceil z) fun h ↦ hz (h ▸ intCast_mem_intLattice _)⟩

omit [DecidableEq S] in
/-- **Circulation rounding**: every real circulation `x` has an integer rounding
`⌊x_ij⌋ ≤ n_ij ≤ ⌈x_ij⌉` that is again a circulation. Proof by cycle cancelling: while some
entry is fractional, push along a cycle of fractional arcs (`exists_cycle_direction`) until one
more entry becomes an integer; floors and ceilings of the entries are respected throughout. -/
theorem exists_int_circulation_rounding {x : S → S → ℝ} (hx : IsCirculation x) :
    ∃ n : S → S → ℤ, IsCirculation (fun i j ↦ (n i j : ℝ)) ∧
      ∀ i j, ⌊x i j⌋ ≤ n i j ∧ n i j ≤ ⌈x i j⌉ := by
  classical
  let Inv : (S → S → ℝ) → Prop := fun y ↦
    IsCirculation y ∧ ∀ i j, (⌊x i j⌋ : ℝ) ≤ y i j ∧ y i j ≤ ⌈x i j⌉
  let F : (S → S → ℝ) → Finset (S × S) := fun y ↦ univ.filter fun q ↦ y q.1 q.2 ∉ intLattice
  have key : ∀ k, ∀ y, Inv y → (F y).card = k → ∃ n : S → S → ℤ,
      IsCirculation (fun i j ↦ (n i j : ℝ)) ∧ ∀ i j, ⌊x i j⌋ ≤ n i j ∧ n i j ≤ ⌈x i j⌉ := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro y hy hk
    by_cases hF : F y = ∅
    · have hint : ∀ i j, (⌊y i j⌋ : ℝ) = y i j := fun i j ↦ by
        have : y i j ∈ intLattice := by
          by_contra h
          have hm : (i, j) ∈ F y := Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩
          rw [hF] at hm
          exact Finset.notMem_empty _ hm
        obtain ⟨m, hm⟩ := mem_intLattice.1 this
        rw [← hm, Int.floor_intCast]
      refine ⟨fun i j ↦ ⌊y i j⌋, fun v ↦ ?_, fun i j ↦ ⟨?_, ?_⟩⟩
      · simp only [hint]
        exact hy.1 v
      · exact Int.le_floor.2 (hy.2 i j).1
      · have h := (hy.2 i j).2
        rw [← hint i j] at h
        exact_mod_cast h
    · obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.2 hF
      have hpfr : y p.1 p.2 ∉ intLattice := (Finset.mem_filter.1 hp).2
      obtain ⟨D, hDc, hDab, hDs⟩ := exists_cycle_direction hy.1 hpfr
      set A := univ.filter fun q : S × S ↦ D q.1 q.2 ≠ 0 with hA
      have hpA : p ∈ A := Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [hDab]; exact one_ne_zero⟩
      let r : S × S → ℝ := fun q ↦ if 0 < D q.1 q.2 then (⌈y q.1 q.2⌉ - y q.1 q.2) / D q.1 q.2
        else (y q.1 q.2 - ⌊y q.1 q.2⌋) / (-D q.1 q.2)
      obtain ⟨q₀, hq₀A, hmin⟩ := Finset.exists_min_image A r ⟨p, hpA⟩
      set t := r q₀ with ht
      have hDne : ∀ q ∈ A, D q.1 q.2 ≠ 0 := fun q hq ↦ (Finset.mem_filter.1 hq).2
      have ht0 : 0 ≤ t := by
        have hfr := floor_lt_lt_ceil_of_notMem (hDs _ _ (hDne q₀ hq₀A))
        simp only [ht, r]
        split_ifs with hpos
        · exact div_nonneg (by linarith) hpos.le
        · have : D q₀.1 q₀.2 < 0 := lt_of_le_of_ne (not_lt.1 hpos) (hDne q₀ hq₀A)
          exact div_nonneg (by linarith) (by linarith)
      set y' : S → S → ℝ := fun i j ↦ y i j + t * D i j with hy'
      have hbox : ∀ i j, (⌊y i j⌋ : ℝ) ≤ y' i j ∧ y' i j ≤ ⌈y i j⌉ := by
        intro i j
        by_cases hD : D i j = 0
        · simp only [hy', hD, mul_zero, add_zero]
          exact ⟨Int.floor_le _, Int.le_ceil _⟩
        · have hq : (i, j) ∈ A := Finset.mem_filter.2 ⟨Finset.mem_univ _, hD⟩
          have hfr := floor_lt_lt_ceil_of_notMem (hDs i j hD)
          have hle : t ≤ r (i, j) := hmin (i, j) hq
          simp only [r] at hle
          simp only [hy']
          split_ifs at hle with hpos
          · rw [le_div_iff₀ hpos] at hle
            constructor <;> nlinarith
          · have hneg : D i j < 0 := lt_of_le_of_ne (not_lt.1 hpos) hD
            rw [le_div_iff₀ (by linarith)] at hle
            constructor <;> nlinarith
      have hInv : Inv y' := by
        refine ⟨(isCirculation_iff_netFlow _).2 fun v ↦ ?_, fun i j ↦ ⟨?_, ?_⟩⟩
        · rw [hy', netFlow_add, netFlow_mul, (isCirculation_iff_netFlow _).1 hy.1 v,
            (isCirculation_iff_netFlow _).1 hDc v, mul_zero, add_zero]
        · have h1 : (⌊x i j⌋ : ℝ) ≤ ⌊y i j⌋ := by exact_mod_cast Int.le_floor.2 (hy.2 i j).1
          linarith [(hbox i j).1]
        · have h1 : (⌈y i j⌉ : ℝ) ≤ ⌈x i j⌉ := by exact_mod_cast Int.ceil_le.2 (hy.2 i j).2
          linarith [(hbox i j).2]
      have hsub : F y' ⊆ (F y).erase q₀ := by
        intro q hq
        have hq' := (Finset.mem_filter.1 hq).2
        have hqF : q ∈ F y := by
          refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun hyq ↦ hq' ?_⟩
          have hD : D q.1 q.2 = 0 := by
            by_contra hD
            exact hDs _ _ hD hyq
          simp only [hy', hD, mul_zero, add_zero]
          exact hyq
        refine Finset.mem_erase.2 ⟨fun hqq ↦ hq' ?_, hqF⟩
        subst hqq
        have hD := hDne q hq₀A
        simp only [hy', ht, r]
        split_ifs with hpos
        · rw [div_mul_cancel₀ _ hD, add_sub_cancel]
          exact intCast_mem_intLattice _
        · have h : y q.1 q.2 + (y q.1 q.2 - ⌊y q.1 q.2⌋) / -D q.1 q.2 * D q.1 q.2 =
              ⌊y q.1 q.2⌋ := by
            field_simp
            ring
          rw [h]
          exact intCast_mem_intLattice _
      have hlt : (F y').card < k := by
        rw [← hk]
        exact lt_of_le_of_lt (Finset.card_le_card hsub) (Finset.card_erase_lt_of_mem
          (Finset.mem_filter.2 ⟨Finset.mem_univ _, hDs _ _ (hDne q₀ hq₀A)⟩))
      exact ih _ hlt y' hInv rfl
  exact key _ x ⟨hx, fun i j ↦ ⟨Int.floor_le _, Int.le_ceil _⟩⟩ rfl

omit [DecidableEq S] in
/-- An integer between `⌊z⌋` and `⌈z⌉` is within `1` of `z`. -/
theorem abs_sub_lt_one_of_floor_le_le_ceil {z : ℝ} {k : ℤ} (h1 : ⌊z⌋ ≤ k) (h2 : k ≤ ⌈z⌉) :
    |(k : ℝ) - z| < 1 := by
  have h1' : (⌊z⌋ : ℝ) ≤ k := by exact_mod_cast h1
  have h2' : (k : ℝ) ≤ ⌈z⌉ := by exact_mod_cast h2
  have h3 := Int.ceil_lt_add_one z
  have h4 := Int.lt_floor_add_one z
  rw [abs_sub_lt_iff]
  constructor <;> linarith

/-! ### The expected counts `T π_i p_ij` -/

/-- `w` is a **stationary distribution** of `P` (as a row vector): `Σ_i w_i P i j = w_j`. -/
def IsStationaryRow (P : S → S → ℝ) (w : S → ℝ) : Prop := ∀ j, ∑ i, w i * P i j = w j

/-- Post #3's **expected transition counts** `x_ij = T π_i p_ij`. -/
def expectedCounts (P : S → S → ℝ) (w : S → ℝ) (T : ℝ) (i j : S) : ℝ := T * w i * P i j

omit [DecidableEq S] in
/-- **The expected counts form a circulation**: row `i` and column `i` both sum to `T π_i`. -/
theorem isCirculation_expectedCounts {P : S → S → ℝ} (hP : IsStochastic P) {w : S → ℝ}
    (hw : IsStationaryRow P w) (T : ℝ) : IsCirculation (expectedCounts P w T) := by
  intro v
  unfold expectedCounts
  rw [← Finset.mul_sum, hP.sum_eq_one v, mul_one]
  simp only [mul_assoc]
  rw [← Finset.mul_sum, hw v]

omit [DecidableEq S] in
/-- The expected counts add up to `T` (for a probability vector `w`). -/
theorem sum_expectedCounts {P : S → S → ℝ} (hP : IsStochastic P) {w : S → ℝ}
    (hw1 : ∑ i, w i = 1) (T : ℝ) : ∑ i, ∑ j, expectedCounts P w T i j = T := by
  unfold expectedCounts
  simp only [← Finset.mul_sum, hP.sum_eq_one, mul_one]
  rw [hw1, mul_one]

omit [DecidableEq S] in
/-- **Post #3's rounding exists** ("counts `n_ij = T π_i p_ij`, rounded so that every state is
entered as often as it is left"): there is an integer circulation `n` with
`⌊T π_i p_ij⌋ ≤ n_ij ≤ ⌈T π_i p_ij⌉`, hence `|n_ij − T π_i p_ij| < 1`, and with total between
`Σ ⌊T π_i p_ij⌋` and `Σ ⌈T π_i p_ij⌉`. -/
theorem exists_rounding_expectedCounts {P : S → S → ℝ} (hP : IsStochastic P) {w : S → ℝ}
    (hw : IsStationaryRow P w) (T : ℝ) :
    ∃ n : S → S → ℤ, IsCirculation (fun i j ↦ (n i j : ℝ)) ∧
      (∀ i j, ⌊expectedCounts P w T i j⌋ ≤ n i j ∧ n i j ≤ ⌈expectedCounts P w T i j⌉) ∧
      (∀ i j, |(n i j : ℝ) - expectedCounts P w T i j| < 1) ∧
      ∑ i, ∑ j, ⌊expectedCounts P w T i j⌋ ≤ ∑ i, ∑ j, n i j ∧
      ∑ i, ∑ j, n i j ≤ ∑ i, ∑ j, ⌈expectedCounts P w T i j⌉ := by
  obtain ⟨n, hc, hb⟩ := exists_int_circulation_rounding (isCirculation_expectedCounts hP hw T)
  exact ⟨n, hc, hb, fun i j ↦ abs_sub_lt_one_of_floor_le_le_ceil (hb i j).1 (hb i j).2,
    Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ (hb i j).1,
    Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ (hb i j).2⟩

/-! ### Correction: the total cannot always be rounded to `T` -/

/-- The two-state flip chain `P = [[0, 1], [1, 0]]`. -/
def flipChain (i j : Fin 2) : ℝ := if i = j then 0 else 1

/-- The flip chain is stochastic. -/
theorem isStochastic_flipChain : IsStochastic flipChain := by
  refine ⟨fun i j ↦ ?_, fun i ↦ ?_⟩
  · unfold flipChain
    split_ifs <;> norm_num
  · rw [Fin.sum_univ_two]
    unfold flipChain
    fin_cases i <;> norm_num

/-- `(1/2, 1/2)` is stationary for the flip chain. -/
theorem isStationaryRow_flipChain : IsStationaryRow flipChain fun _ ↦ 1 / 2 := by
  intro j
  rw [Fin.sum_univ_two]
  unfold flipChain
  fin_cases j <;> norm_num

/-- **Correction** (post #3, conditional MC): the rounded counts cannot always have total `T`.
For the flip chain with `π = (1/2, 1/2)` and `T = 3`, `x_01 = x_10 = 3/2` and `x_00 = x_11 = 0`,
and no integer circulation with `⌊x⌋ ≤ n ≤ ⌈x⌉` has total `3` (a circulation has
`n_01 = n_10`, so its total is even). So a path with exactly balanced counts may have to have
length `Σ n ≠ T`; `exists_rounding_expectedCounts` gives the correct statement, total between
`Σ ⌊x⌋` and `Σ ⌈x⌉`. (With "allowing for the first and last states", i.e. open paths, the length
`3` path `0 → 1 → 0 → 1` does exist here.) -/
theorem not_exists_rounding_flipChain_total_three :
    ¬ ∃ n : Fin 2 → Fin 2 → ℤ, IsCirculation (fun i j ↦ (n i j : ℝ)) ∧
      (∀ i j, ⌊expectedCounts flipChain (fun _ ↦ 1 / 2) 3 i j⌋ ≤ n i j ∧
        n i j ≤ ⌈expectedCounts flipChain (fun _ ↦ 1 / 2) 3 i j⌉) ∧
      ∑ i, ∑ j, n i j = 3 := by
  rintro ⟨n, hc, hb, hs⟩
  have hdiag : ∀ i, expectedCounts flipChain (fun _ ↦ 1 / 2) 3 i i = 0 := fun i ↦ by
    simp only [expectedCounts, flipChain, eq_self, ↓reduceIte, mul_zero]
  have h00 := hb 0 0
  have h11 := hb 1 1
  rw [hdiag, Int.floor_zero, Int.ceil_zero] at h00 h11
  have h0 := hc 0
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at h0
  beta_reduce at h0
  have h0' : n 0 0 + n 0 1 = n 0 0 + n 1 0 := by exact_mod_cast h0
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two] at hs
  omega

/-! ### The conditional MC of post #3 is well defined -/

omit [DecidableEq S] in
/-- **A closed path realising the rounded counts**: for an irreducible stochastic `P` with
stationary `π` and a horizon `T` large enough that `T π_i p_ij ≥ 1` on the support of `P`, there
are counts `N` within `1` of `T π_i p_ij`, with the same support as `P`, balanced at every state,
and a closed path from any `x₀` of length `Σ N` with exactly these transition counts (Euler,
`exists_path_of_balanced`). -/
theorem exists_closed_path_of_rounding [DecidableEq S] {P : S → S → ℝ} (hP : IsStochastic P)
    {w : S → ℝ} (hw : IsStationaryRow P w) {T : ℝ}
    (hT : ∀ i j, 0 < P i j → 1 ≤ expectedCounts P w T i j)
    (hirr : ∀ i j, Relation.ReflTransGen (fun a b ↦ 0 < P a b) i j) (x₀ : S) :
    ∃ N : S → S → ℕ, (∀ i j, |(N i j : ℝ) - expectedCounts P w T i j| < 1) ∧
      (∀ i j, N i j ≠ 0 ↔ 0 < P i j) ∧ BalancedCounts N x₀ x₀ ∧
      ∃ s : ℕ → S, s 0 = x₀ ∧ s (∑ i, ∑ j, N i j) = x₀ ∧
        ∀ i j, transCount s i j (∑ i, ∑ j, N i j) = N i j := by
  obtain ⟨n, hc, hb, habs, -⟩ := exists_rounding_expectedCounts hP hw T
  have hzero : ∀ i j, P i j = 0 → expectedCounts P w T i j = 0 := fun i j h ↦ by
    rw [expectedCounts, h, mul_zero]
  have hn0 : ∀ i j, 0 ≤ n i j := fun i j ↦ by
    rcases (hP.nonneg i j).lt_or_eq with h | h
    · exact le_trans (Int.floor_nonneg.2 (le_trans zero_le_one (hT i j h))) (hb i j).1
    · exact le_trans (by rw [hzero i j h.symm, Int.floor_zero]) (hb i j).1
  set N : S → S → ℕ := fun i j ↦ (n i j).toNat with hN
  have hNz : ∀ i j, ((N i j : ℕ) : ℤ) = n i j := fun i j ↦ Int.toNat_of_nonneg (hn0 i j)
  have hNr : ∀ i j, ((N i j : ℕ) : ℝ) = n i j := fun i j ↦ by
    rw [← Int.cast_natCast, hNz]
  have hsupp : ∀ i j, N i j ≠ 0 ↔ 0 < P i j := by
    intro i j
    constructor
    · intro h
      rcases (hP.nonneg i j).lt_or_eq with hp | hp
      · exact hp
      · exfalso
        have := hb i j
        rw [hzero i j hp.symm, Int.floor_zero, Int.ceil_zero] at this
        have h' := hNz i j
        omega
    · intro hp
      have h1 : 1 ≤ n i j := le_trans (Int.le_floor.2 (by exact_mod_cast hT i j hp)) (hb i j).1
      have h' := hNz i j
      omega
  have hbal : BalancedCounts N x₀ x₀ := by
    intro i
    have hci : ∑ j, n i j = ∑ j, n j i := by
      have := hc i
      beta_reduce at this
      exact_mod_cast this
    simp only [hNz]
    rw [hci, sub_self, sub_self]
  have hconn : ∀ i j, N i j ≠ 0 → Relation.ReflTransGen (fun a b ↦ N a b ≠ 0) x₀ i :=
    fun i _ _ ↦ Relation.ReflTransGen.mono (fun a b h ↦ (hsupp a b).2 h) x₀ i (hirr x₀ i)
  obtain ⟨s, hs0, hsT, hsN⟩ := exists_path_of_balanced hbal hconn
  exact ⟨N, fun i j ↦ by rw [hNr]; exact habs i j, hsupp, hbal, s, hs0, hsT, hsN⟩

/-- **Post #3's conditional MC is well defined**: with the rounded counts `N` of
`exists_closed_path_of_rounding` and `L = Σ N`, the event "MC from `x₀` has transition counts
`N` over `L` steps" has positive probability, and conditionally on it the MC path is uniform
over the paths with these counts (`cond_mcLaw_countClass`). -/
theorem conditionalMC_wellDefined {m : ℕ} {P : Fin m → Fin m → ℝ} (hP : IsStochastic P)
    {w : Fin m → ℝ} (hw : IsStationaryRow P w) {T : ℝ}
    (hT : ∀ i j, 0 < P i j → 1 ≤ expectedCounts P w T i j)
    (hirr : ∀ i j, Relation.ReflTransGen (fun a b ↦ 0 < P a b) i j) (x₀ : Fin m) :
    ∃ N : Fin m → Fin m → ℕ, (∀ i j, |(N i j : ℝ) - expectedCounts P w T i j| < 1) ∧
      BalancedCounts N x₀ x₀ ∧
      mcLaw P x₀ (∑ i, ∑ j, N i j) (countClass x₀ N (∑ i, ∑ j, N i j) : Set _) ≠ 0 ∧
      (mcLaw P x₀ (∑ i, ∑ j, N i j))[|(countClass x₀ N (∑ i, ∑ j, N i j) : Set _)] =
        uniformOn (countClass x₀ N (∑ i, ∑ j, N i j) : Set _) := by
  obtain ⟨N, habs, hsupp, hbal, s, hs0, -, hsN⟩ := exists_closed_path_of_rounding hP hw hT hirr x₀
  set L := ∑ i, ∑ j, N i j with hL
  set sv : Fin (L + 1) → Fin m := fun t ↦ s t with hsv
  have hagree : ∀ t ≤ L, s t = extendPath sv t := (extendPath_eq_iff s sv).1 rfl
  have hmem : sv ∈ countClass x₀ N L := by
    rw [mem_countClass]
    refine ⟨(hagree 0 (Nat.zero_le L)).symm.trans hs0, fun i j ↦ ?_⟩
    rw [← transCount_congr hagree i j]
    exact hsN i j
  have hpos : 0 < mcLaw P x₀ L {sv} := by
    rw [mcLaw_singleton_of_mem hP x₀ N L hmem, ENNReal.ofReal_pos]
    refine Finset.prod_pos fun i _ ↦ Finset.prod_pos fun j _ ↦ ?_
    by_cases h : N i j = 0
    · rw [h, pow_zero]
      exact one_pos
    · exact pow_pos ((hsupp i j).1 h) _
  have hC : mcLaw P x₀ L (countClass x₀ N L : Set _) ≠ 0 :=
    (lt_of_lt_of_le hpos (measure_mono (Set.singleton_subset_iff.2 (Finset.mem_coe.2 hmem)))).ne'
  exact ⟨N, habs, hbal, hC, cond_mcLaw_countClass hP x₀ N L hC⟩

end RQMCMarkov.MarkovDriving

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Rounding with exactly `T` transitions, allowing for the first and last states (post #3)

Post #3 asks for counts `n_ij = T π_i p_ij`, "rounded so that every state is entered as often as
it is left (allowing for the first and last states)". Reading: integer counts `N` with total
exactly `T` (a path of `T` transitions), entrywise roundings `⌊T π_i p_ij⌋ ≤ N_ij ≤
⌈T π_i p_ij⌉` (so `|N_ij − T π_i p_ij| < 1`, the strict bound — no weakening needed), and
balanced except at a first state `a` and a last state `b`: out-count minus in-count equals
`1{a} − 1{b}`. `ConditionalMCRounding` shows that closed (circulation) roundings cannot always
have total `T`; open ones always can.

## Main results

* `exists_walk_of_reflTransGen`, `exists_injOn_walk`: chains are walks, and can be taken
  without repeated states.
* `prefCount`, `netFlow_prefCount`, `sum_prefCount`, `prefCount_ne_zero`: flows of the prefixes
  of a walk with distinct arcs.
* `exists_simple_cycle`: every fractional arc of a real circulation lies on a simple cycle of
  fractional arcs (walk of distinct states closing through the arc).
* `fracSet`, `exists_push`: pushing along a circulation supported on the fractional entries
  makes one more entry an integer (inside the box `[⌊x⌋, ⌈x⌉]`).
* `exists_eq_of_unit_steps`: the discrete intermediate value theorem.
* `exists_open_rounding`: **open rounding with exact total** — a real circulation with integer
  total `T` has an integer rounding `⌊x⌋ ≤ N ≤ ⌈x⌉` with total `T` balanced from some `a` to some
  `b`.
* `exists_path_exact_length`: for irreducible `P`, stationary probability `π`, and integer `T`
  with `T π_i p_ij ≥ 1` on the support of `P`: counts within `1` of `T π_i p_ij` with total `T`,
  the support of `P`, balanced from `a` to `b`, and a path `a = s_0, …, s_T = b` with exactly
  these counts.
* `conditionalMC_exact_wellDefined`: post #3's conditional MC with exactly `T` transitions is
  well defined (positive conditioning probability; conditional law uniform on the paths).
* `flipChain_open_path_three`: the open path `0 → 1 → 0 → 1` for the flip chain at `T = 3`.

The start and end states `a`, `b` are produced by the rounding, not prescribed.
-/

namespace RQMCMarkov.MarkovDriving

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

variable {S : Type*}

/-! ### Walks without repeated states -/

/-- A chain `u →* v` of a relation is a walk `W 0 = u, …, W k = v`. -/
theorem exists_walk_of_reflTransGen {r : S → S → Prop} {u v : S}
    (h : Relation.ReflTransGen r u v) :
    ∃ W : ℕ → S, ∃ k, W 0 = u ∧ W k = v ∧ ∀ s < k, r (W s) (W (s + 1)) := by
  induction h with
  | refl => exact ⟨fun _ ↦ u, 0, rfl, rfl, fun s hs ↦ absurd hs (Nat.not_lt_zero s)⟩
  | @tail b c _ hbc ih =>
    obtain ⟨W, k, h0, hk, hs⟩ := ih
    refine ⟨Function.update W (k + 1) c, k + 1, ?_, Function.update_self _ _ _, fun s hs' ↦ ?_⟩
    · rw [Function.update_of_ne (by omega)]
      exact h0
    · rw [Function.update_of_ne (by omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs' with hs' | rfl
      · rw [Function.update_of_ne (by omega)]
        exact hs s hs'
      · rw [Function.update_self, hk]
        exact hbc

/-- A chain `u →* v` is realised by a walk **without repeated states**. -/
theorem exists_injOn_walk {r : S → S → Prop} {u v : S} (h : Relation.ReflTransGen r u v) :
    ∃ W : ℕ → S, ∃ k, W 0 = u ∧ W k = v ∧ (∀ s < k, r (W s) (W (s + 1))) ∧
      ∀ i ≤ k, ∀ j ≤ k, W i = W j → i = j := by
  classical
  have hQ : ∃ k, ∃ W : ℕ → S, W 0 = u ∧ W k = v ∧ ∀ s < k, r (W s) (W (s + 1)) := by
    obtain ⟨W, k, h0, hk, hs⟩ := exists_walk_of_reflTransGen h
    exact ⟨k, W, h0, hk, hs⟩
  obtain ⟨W, h0, hk, hs⟩ := Nat.find_spec hQ
  set k := Nat.find hQ with hkdef
  have hshort : ∀ i j, i < j → j ≤ k → W i = W j → False := by
    intro i j hij hjk hW
    set W' : ℕ → S := fun t ↦ if t ≤ i then W t else W (t + (j - i)) with hW'
    have hlt : k - (j - i) < k := by omega
    refine Nat.find_min hQ hlt ⟨W', ?_, ?_, fun t ht ↦ ?_⟩
    · simp only [hW', Nat.zero_le, ↓reduceIte]
      exact h0
    · by_cases hki : k - (j - i) ≤ i
      · simp only [hW', hki, ↓reduceIte]
        rw [show k - (j - i) = i by omega, hW, show j = k by omega]
        exact hk
      · simp only [hW', hki, ↓reduceIte]
        rw [show k - (j - i) + (j - i) = k by omega]
        exact hk
    · by_cases h1 : t + 1 ≤ i
      · simp only [hW', h1, show t ≤ i by omega, ↓reduceIte]
        exact hs t (by omega)
      · by_cases h2 : t ≤ i
        · simp only [hW', h1, h2, ↓reduceIte]
          rw [show t = i by omega, hW, show i + 1 + (j - i) = j + 1 by omega]
          exact hs j (by omega)
        · simp only [hW', h1, h2, ↓reduceIte]
          rw [show t + 1 + (j - i) = t + (j - i) + 1 by omega]
          exact hs (t + (j - i)) (by omega)
  refine ⟨W, k, h0, hk, hs, fun i hi j hj hW ↦ ?_⟩
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (hshort i j hij hj hW).elim
  · exact hij
  · exact (hshort j i hij hi hW.symm).elim

/-! ### Prefix flows of a cycle -/

variable [DecidableEq S]

/-- The integer flow of the first `m` steps of a walk with arcs `arc s` and signs `sg s`
(`+1` for a step along its arc, `−1` against it). -/
def prefCount (arc : ℕ → S × S) (sg : ℕ → ℤ) (m : ℕ) (i j : S) : ℤ :=
  ∑ s ∈ range m, if arc s = (i, j) then sg s else 0

omit [DecidableEq S] in
/-- Rewriting an arc indicator. -/
theorem ite_prod_eq [DecidableEq S] (p : S × S) (i j : S) (c : ℝ) :
    (if p = (i, j) then c else 0) = if i = p.1 ∧ j = p.2 then c else 0 := by
  obtain ⟨p1, p2⟩ := p
  by_cases h : i = p1 ∧ j = p2
  · obtain ⟨rfl, rfl⟩ := h
    simp only [and_self, ↓reduceIte]
  · have h' : (p1, p2) ≠ (i, j) := fun hh ↦ h ⟨(Prod.mk.inj hh).1.symm, (Prod.mk.inj hh).2.symm⟩
    simp only [h, h', ↓reduceIte]

variable [Fintype S]

/-- **Net outflow of a prefix flow**: `1{v = C 0} − 1{v = C m}`, whatever the orientations. -/
theorem netFlow_prefCount {L : ℕ} {C : ℕ → S} {arc : ℕ → S × S} {sg : ℕ → ℤ}
    (h2 : ∀ s < L, (sg s = 1 ∧ arc s = (C s, C (s + 1))) ∨
      (sg s = -1 ∧ arc s = (C (s + 1), C s))) {m : ℕ} (hm : m ≤ L) (v : S) :
    netFlow (fun i j ↦ (prefCount arc sg m i j : ℝ)) v =
      (if v = C 0 then 1 else 0) - if v = C m then 1 else 0 := by
  induction m with
  | zero =>
    unfold netFlow prefCount
    simp only [Finset.range_zero, Finset.sum_empty, Int.cast_zero, Finset.sum_const_zero,
      sub_self]
  | succ m ih =>
    have hf : (fun i j ↦ (prefCount arc sg (m + 1) i j : ℝ)) = fun i j ↦
        (prefCount arc sg m i j : ℝ) + if i = (arc m).1 ∧ j = (arc m).2 then (sg m : ℝ) else 0 := by
      funext i j
      unfold prefCount
      rw [Finset.sum_range_succ, Int.cast_add, ← ite_prod_eq]
      push_cast
      rfl
    rw [hf, netFlow_add, ih (by omega), netFlow_single]
    rcases h2 m (by omega) with ⟨hs, ha⟩ | ⟨hs, ha⟩
    · rw [hs, ha]
      push_cast
      ring
    · rw [hs, ha]
      push_cast
      split_ifs <;> ring

/-- The total of a prefix flow is the sum of the signs. -/
theorem sum_prefCount (arc : ℕ → S × S) (sg : ℕ → ℤ) (m : ℕ) :
    ∑ i, ∑ j, prefCount arc sg m i j = ∑ s ∈ range m, sg s := by
  unfold prefCount
  calc ∑ i, ∑ j, ∑ s ∈ range m, (if arc s = (i, j) then sg s else 0)
      = ∑ i, ∑ s ∈ range m, ∑ j, (if arc s = (i, j) then sg s else 0) :=
        Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm
    _ = ∑ s ∈ range m, ∑ i, ∑ j, (if arc s = (i, j) then sg s else 0) := Finset.sum_comm
    _ = ∑ s ∈ range m, sg s := by
        refine Finset.sum_congr rfl fun s _ ↦ ?_
        rw [← Fintype.sum_prod_type' (f := fun i j ↦ if arc s = (i, j) then sg s else 0)]
        simp only [Prod.mk.eta]
        rw [Finset.sum_ite_eq]
        simp only [Finset.mem_univ, ↓reduceIte]

omit [Fintype S] in
/-- With distinct arcs, a nonzero entry of a prefix flow is the sign of the unique step using
that arc, and equals the entry of the full flow. -/
theorem prefCount_ne_zero {L : ℕ} {arc : ℕ → S × S} {sg : ℕ → ℤ}
    (h4 : ∀ s < L, ∀ s' < L, arc s = arc s' → s = s') {m : ℕ} (hm : m ≤ L) {i j : S}
    (h : prefCount arc sg m i j ≠ 0) :
    ∃ s₀ < m, arc s₀ = (i, j) ∧ prefCount arc sg m i j = sg s₀ ∧
      prefCount arc sg L i j = sg s₀ := by
  obtain ⟨s₀, hs₀, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hs₀m := Finset.mem_range.1 hs₀
  have harc : arc s₀ = (i, j) := by
    by_contra hc
    simp only [hc, ↓reduceIte, ne_eq, not_true_eq_false] at hne
  have hsum : ∀ M, s₀ < M → M ≤ L → prefCount arc sg M i j = sg s₀ := fun M hM hML ↦ by
    unfold prefCount
    rw [Finset.sum_eq_single_of_mem s₀ (Finset.mem_range.2 hM)]
    · simp only [harc, ↓reduceIte]
    · intro s hs hss
      have : arc s ≠ (i, j) := fun has ↦
        hss (h4 s (by have := Finset.mem_range.1 hs; omega) s₀ (by omega) (has.trans harc.symm))
      simp only [this, ↓reduceIte]
  exact ⟨s₀, hs₀m, harc, hsum m hs₀m hm, hsum L (by omega) le_rfl⟩

/-! ### A simple cycle through a fractional arc -/

omit [DecidableEq S] in
/-- **A fractional arc of a circulation lies on a simple cycle of fractional arcs**: a closed
walk `C 0 = a, C 1 = b, …, C L = a` whose steps use distinct fractional arcs `arc s`, the first
being `a → b`, each traversed along (`sg s = 1`) or against (`sg s = −1`) its direction. -/
theorem exists_simple_cycle {y : S → S → ℝ} (hy : IsCirculation y) {a b : S}
    (he : y a b ∉ intLattice) :
    ∃ L : ℕ, ∃ C : ℕ → S, ∃ arc : ℕ → S × S, ∃ sg : ℕ → ℤ, 1 ≤ L ∧ C 0 = a ∧ C L = a ∧
      (∀ s < L, (sg s = 1 ∧ arc s = (C s, C (s + 1))) ∨
        (sg s = -1 ∧ arc s = (C (s + 1), C s))) ∧
      (∀ s < L, y (arc s).1 (arc s).2 ∉ intLattice) ∧
      (∀ s < L, ∀ s' < L, arc s = arc s' → s = s') ∧ arc 0 = (a, b) ∧ sg 0 = 1 := by
  classical
  obtain ⟨W, k, hW0, hWk, hWs, hWinj⟩ := exists_injOn_walk (reflTransGen_fracAdj_of_notMem hy he)
  let fwd : ℕ → Prop := fun i ↦ (W i, W (i + 1)) ≠ (a, b) ∧ y (W i) (W (i + 1)) ∉ intLattice
  let C : ℕ → S := fun t ↦ if t = 0 then a else W (t - 1)
  let arc : ℕ → S × S := fun s ↦ if s = 0 then (a, b) else
    if fwd (s - 1) then (W (s - 1), W s) else (W s, W (s - 1))
  let sg : ℕ → ℤ := fun s ↦ if s = 0 then 1 else if fwd (s - 1) then 1 else -1
  have hC : ∀ i, C (i + 1) = W i := fun i ↦ by
    simp only [C, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
  -- the arc of step `i + 1` and its properties
  have harc : ∀ i < k, (arc (i + 1) = (W i, W (i + 1)) ∨ arc (i + 1) = (W (i + 1), W i)) ∧
      arc (i + 1) ≠ (a, b) ∧ y (arc (i + 1)).1 (arc (i + 1)).2 ∉ intLattice ∧
      ((sg (i + 1) = 1 ∧ arc (i + 1) = (C (i + 1), C (i + 1 + 1))) ∨
        (sg (i + 1) = -1 ∧ arc (i + 1) = (C (i + 1 + 1), C (i + 1)))) := by
    intro i hi
    have hadj := hWs i hi
    by_cases hf : fwd i
    · have e1 : arc (i + 1) = (W i, W (i + 1)) := by
        simp only [arc, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, hf]
      have e2 : sg (i + 1) = 1 := by
        simp only [sg, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, hf]
      refine ⟨Or.inl e1, e1 ▸ hf.1, e1 ▸ hf.2, Or.inl ⟨e2, ?_⟩⟩
      rw [e1, hC, hC]
    · have e1 : arc (i + 1) = (W (i + 1), W i) := by
        simp only [arc, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, hf]
      have e2 : sg (i + 1) = -1 := by
        simp only [sg, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, hf]
      have hb : (W (i + 1), W i) ≠ (a, b) ∧ y (W (i + 1)) (W i) ∉ intLattice := by
        rcases hadj with hl | hr
        · exact absurd hl hf
        · exact hr
      refine ⟨Or.inr e1, e1 ▸ hb.1, e1 ▸ hb.2, Or.inr ⟨e2, ?_⟩⟩
      rw [e1, hC, hC]
  have harc0 : arc 0 = (a, b) := by simp only [arc, ↓reduceIte]
  have hsg0 : sg 0 = 1 := by simp only [sg, ↓reduceIte]
  have hC0 : C 0 = a := by simp only [C, ↓reduceIte]
  refine ⟨k + 1, C, arc, sg, by omega, hC0, by rw [hC, hWk], fun s hs ↦ ?_, fun s hs ↦ ?_,
    fun s hs s' hs' hss ↦ ?_, harc0, hsg0⟩
  · rcases s with _ | i
    · left
      rw [hsg0, harc0, hC0, hC, hW0]
      exact ⟨rfl, rfl⟩
    · exact (harc i (by omega)).2.2.2
  · rcases s with _ | i
    · rw [harc0]
      exact he
    · exact (harc i (by omega)).2.2.1
  · rcases s with _ | i <;> rcases s' with _ | i'
    · rfl
    · exact absurd (hss.symm.trans harc0) (harc i' (by omega)).2.1
    · exact absurd (hss.trans harc0) (harc i (by omega)).2.1
    · have h1 := (harc i (by omega)).1
      have h2 := (harc i' (by omega)).1
      have key : i = i' := by
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] at hss <;>
          obtain ⟨hp1, hp2⟩ := Prod.mk.inj hss
        · exact hWinj i (by omega) i' (by omega) hp1
        · have := hWinj i (by omega) (i' + 1) (by omega) hp1
          have := hWinj (i + 1) (by omega) i' (by omega) hp2
          omega
        · have := hWinj (i + 1) (by omega) i' (by omega) hp1
          have := hWinj i (by omega) (i' + 1) (by omega) hp2
          omega
        · exact hWinj i (by omega) i' (by omega) hp2
      rw [key]

/-! ### The push step -/

omit [DecidableEq S] in
/-- The fractional entries of a real matrix. -/
noncomputable def fracSet (y : S → S → ℝ) : Finset (S × S) := by
  classical
  exact univ.filter fun q ↦ y q.1 q.2 ∉ intLattice

omit [DecidableEq S] in
/-- Membership in `fracSet`. -/
theorem mem_fracSet {y : S → S → ℝ} {q : S × S} : q ∈ fracSet y ↔ y q.1 q.2 ∉ intLattice := by
  classical
  unfold fracSet
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ q)

omit [DecidableEq S] in
/-- **Push step**: moving a circulation `y` (inside the box `[⌊x⌋, ⌈x⌉]`) along a nonzero
circulation `D` supported on its fractional entries, as far as the box `[⌊y⌋, ⌈y⌉]` allows,
keeps it a circulation inside the box and makes at least one more entry an integer. -/
theorem exists_push {x y D : S → S → ℝ} (hyc : IsCirculation y)
    (hyb : ∀ i j, (⌊x i j⌋ : ℝ) ≤ y i j ∧ y i j ≤ ⌈x i j⌉) (hDc : IsCirculation D)
    {p : S × S} (hp : D p.1 p.2 ≠ 0) (hDs : ∀ i j, D i j ≠ 0 → y i j ∉ intLattice) :
    ∃ t : ℝ, IsCirculation (fun i j ↦ y i j + t * D i j) ∧
      (∀ i j, (⌊x i j⌋ : ℝ) ≤ y i j + t * D i j ∧ y i j + t * D i j ≤ ⌈x i j⌉) ∧
      (fracSet fun i j ↦ y i j + t * D i j).card < (fracSet y).card := by
  classical
  set A := univ.filter fun q : S × S ↦ D q.1 q.2 ≠ 0 with hA
  have hpA : p ∈ A := Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩
  let r : S × S → ℝ := fun q ↦ if 0 < D q.1 q.2 then (⌈y q.1 q.2⌉ - y q.1 q.2) / D q.1 q.2
    else (y q.1 q.2 - ⌊y q.1 q.2⌋) / (-D q.1 q.2)
  obtain ⟨q₀, hq₀A, hmin⟩ := Finset.exists_min_image A r ⟨p, hpA⟩
  set t := r q₀ with ht
  have hDne : ∀ q ∈ A, D q.1 q.2 ≠ 0 := fun q hq ↦ (Finset.mem_filter.1 hq).2
  set y' : S → S → ℝ := fun i j ↦ y i j + t * D i j with hy'
  have hbox : ∀ i j, (⌊y i j⌋ : ℝ) ≤ y' i j ∧ y' i j ≤ ⌈y i j⌉ := by
    intro i j
    by_cases hD : D i j = 0
    · simp only [hy', hD, mul_zero, add_zero]
      exact ⟨Int.floor_le _, Int.le_ceil _⟩
    · have hq : (i, j) ∈ A := Finset.mem_filter.2 ⟨Finset.mem_univ _, hD⟩
      have hfr := floor_lt_lt_ceil_of_notMem (hDs i j hD)
      have hle : t ≤ r (i, j) := hmin (i, j) hq
      have ht0 : 0 ≤ t := by
        have hfr0 := floor_lt_lt_ceil_of_notMem (hDs _ _ (hDne q₀ hq₀A))
        simp only [ht, r]
        split_ifs with hpos
        · exact div_nonneg (by linarith) hpos.le
        · have : D q₀.1 q₀.2 < 0 := lt_of_le_of_ne (not_lt.1 hpos) (hDne q₀ hq₀A)
          exact div_nonneg (by linarith) (by linarith)
      simp only [r] at hle
      simp only [hy']
      split_ifs at hle with hpos
      · rw [le_div_iff₀ hpos] at hle
        constructor <;> nlinarith
      · have hneg : D i j < 0 := lt_of_le_of_ne (not_lt.1 hpos) hD
        rw [le_div_iff₀ (by linarith)] at hle
        constructor <;> nlinarith
  refine ⟨t, (isCirculation_iff_netFlow _).2 fun v ↦ ?_, fun i j ↦ ⟨?_, ?_⟩, ?_⟩
  · rw [netFlow_add, netFlow_mul, (isCirculation_iff_netFlow _).1 hyc v,
      (isCirculation_iff_netFlow _).1 hDc v, mul_zero, add_zero]
  · have h1 : (⌊x i j⌋ : ℝ) ≤ ⌊y i j⌋ := by exact_mod_cast Int.le_floor.2 (hyb i j).1
    linarith [(hbox i j).1]
  · have h1 : (⌈y i j⌉ : ℝ) ≤ ⌈x i j⌉ := by exact_mod_cast Int.ceil_le.2 (hyb i j).2
    linarith [(hbox i j).2]
  · have hsub : fracSet y' ⊆ (fracSet y).erase q₀ := by
      intro q hq
      have hq' := mem_fracSet.1 hq
      have hqF : q ∈ fracSet y := by
        refine mem_fracSet.2 fun hyq ↦ hq' ?_
        have hD : D q.1 q.2 = 0 := by
          by_contra hD
          exact hDs _ _ hD hyq
        simp only [hy', hD, mul_zero, add_zero]
        exact hyq
      refine Finset.mem_erase.2 ⟨fun hqq ↦ hq' ?_, hqF⟩
      subst hqq
      have hD := hDne q hq₀A
      simp only [hy', ht, r]
      split_ifs with hpos
      · rw [div_mul_cancel₀ _ hD, add_sub_cancel]
        exact intCast_mem_intLattice _
      · have h : y q.1 q.2 + (y q.1 q.2 - ⌊y q.1 q.2⌋) / -D q.1 q.2 * D q.1 q.2 =
            ⌊y q.1 q.2⌋ := by
          field_simp
          ring
        rw [h]
        exact intCast_mem_intLattice _
    exact lt_of_le_of_lt (Finset.card_le_card hsub) (Finset.card_erase_lt_of_mem
      (mem_fracSet.2 (hDs _ _ (hDne q₀ hq₀A))))

/-! ### Rounding with an exact total, open at the ends -/

omit [DecidableEq S] [Fintype S] in
/-- **Discrete intermediate value theorem**: a walk on `ℤ` with unit steps hits every integer
between its endpoints. -/
theorem exists_eq_of_unit_steps (f : ℕ → ℤ) (L : ℕ)
    (hstep : ∀ m < L, f (m + 1) = f m + 1 ∨ f (m + 1) = f m - 1) (z : ℤ)
    (hz : (f 0 ≤ z ∧ z ≤ f L) ∨ (f L ≤ z ∧ z ≤ f 0)) : ∃ m ≤ L, f m = z := by
  induction L with
  | zero => exact ⟨0, le_rfl, by omega⟩
  | succ L ih =>
    by_cases h : (f 0 ≤ z ∧ z ≤ f L) ∨ (f L ≤ z ∧ z ≤ f 0)
    · obtain ⟨m, hm, hfm⟩ := ih (fun m hm ↦ hstep m (by omega)) h
      exact ⟨m, by omega, hfm⟩
    · refine ⟨L + 1, le_rfl, ?_⟩
      have := hstep L (by omega)
      omega

/-- **Open rounding with an exact total** (post #3's rounding "allowing for the first and last
states"): a real circulation `x` with integer total `T` has an integer rounding
`⌊x_ij⌋ ≤ N_ij ≤ ⌈x_ij⌉` with total exactly `T` that is balanced from some state `a` to some
state `b` (net outflow `1{a} − 1{b}`; `a = b` allowed).

Proof by induction on the number of fractional entries of `y` (a circulation in the box with
total `T`): take a simple cycle `D` of fractional arcs (`exists_simple_cycle`) and a circulation
rounding `n` of `y`. If `Σ D = 0`, or `y − n` is not a multiple of `D`, a total-preserving push
(`exists_push`) removes a fractional entry. Otherwise `y = n + θ D`, and adding `± 1` along the
first `m` arcs of the cycle, with `m` chosen by the discrete intermediate value theorem so that
the total becomes `T`, gives the rounding. -/
theorem exists_open_rounding [Nonempty S] {x : S → S → ℝ} (hx : IsCirculation x) {T : ℤ}
    (hT : ∑ i, ∑ j, x i j = T) :
    ∃ N : S → S → ℤ, ∃ a b : S,
      (∀ v, netFlow (fun i j ↦ (N i j : ℝ)) v = (if v = a then 1 else 0) - if v = b then 1 else 0) ∧
      (∀ i j, ⌊x i j⌋ ≤ N i j ∧ N i j ≤ ⌈x i j⌉) ∧ ∑ i, ∑ j, N i j = T := by
  classical
  have key : ∀ k, ∀ y : S → S → ℝ, IsCirculation y →
      (∀ i j, (⌊x i j⌋ : ℝ) ≤ y i j ∧ y i j ≤ ⌈x i j⌉) → ∑ i, ∑ j, y i j = T →
      (fracSet y).card = k → ∃ N : S → S → ℤ, ∃ a b : S,
      (∀ v, netFlow (fun i j ↦ (N i j : ℝ)) v = (if v = a then 1 else 0) - if v = b then 1 else 0) ∧
      (∀ i j, ⌊x i j⌋ ≤ N i j ∧ N i j ≤ ⌈x i j⌉) ∧ ∑ i, ∑ j, N i j = T := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro y hyc hyb hyT hk
    have hfloor : ∀ i j, ⌊x i j⌋ ≤ ⌊y i j⌋ := fun i j ↦ Int.le_floor.2 (hyb i j).1
    have hceil : ∀ i j, ⌈y i j⌉ ≤ ⌈x i j⌉ := fun i j ↦ Int.ceil_le.2 (hyb i j).2
    by_cases hF : fracSet y = ∅
    · have hint : ∀ i j, (⌊y i j⌋ : ℝ) = y i j := fun i j ↦ by
        have : y i j ∈ intLattice := by
          by_contra h
          have hm : (i, j) ∈ fracSet y := mem_fracSet.2 h
          rw [hF] at hm
          exact Finset.notMem_empty _ hm
        obtain ⟨m, hm⟩ := mem_intLattice.1 this
        rw [← hm, Int.floor_intCast]
      obtain ⟨a⟩ := ‹Nonempty S›
      refine ⟨fun i j ↦ ⌊y i j⌋, a, a, fun v ↦ ?_, fun i j ↦ ⟨hfloor i j, ?_⟩, ?_⟩
      · simp only [hint]
        rw [(isCirculation_iff_netFlow y).1 hyc v, sub_self]
      · have h := (hyb i j).2
        rw [← hint i j] at h
        exact_mod_cast h
      · have : ((∑ i, ∑ j, ⌊y i j⌋ : ℤ) : ℝ) = T := by
          push_cast
          simp only [hint]
          exact hyT
        exact_mod_cast this
    obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.2 hF
    obtain ⟨n, hnc, hnb⟩ := exists_int_circulation_rounding hyc
    obtain ⟨L, C, arc, sg, hL1, hC0, hCL, h2, h3, h4, harc0, hsg0⟩ :=
      exists_simple_cycle hyc (mem_fracSet.1 hp)
    set D : S → S → ℝ := fun i j ↦ (prefCount arc sg L i j : ℝ) with hD
    have hDc : IsCirculation D := (isCirculation_iff_netFlow D).2 fun v ↦ by
      rw [hD, netFlow_prefCount h2 le_rfl v, hC0, hCL, sub_self]
    have hDs : ∀ i j, D i j ≠ 0 → y i j ∉ intLattice := fun i j h ↦ by
      have h' : prefCount arc sg L i j ≠ 0 := fun h0 ↦ h (by rw [hD]; simp only [h0, Int.cast_zero])
      obtain ⟨s₀, hs₀, harc, -, -⟩ := prefCount_ne_zero h4 le_rfl h'
      have := h3 s₀ hs₀
      rw [harc] at this
      exact this
    have hDab : prefCount arc sg L p.1 p.2 = 1 := by
      unfold prefCount
      rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 hL1)]
      · simp only [harc0, ↓reduceIte, hsg0]
      · intro s hs hs0
        have : arc s ≠ (p.1, p.2) := fun has ↦
          hs0 (h4 s (Finset.mem_range.1 hs) 0 hL1 (has.trans harc0.symm))
        simp only [this, ↓reduceIte]
    have hDp : D p.1 p.2 ≠ 0 := by
      rw [hD]
      simp only [hDab, Int.cast_one]
      exact one_ne_zero
    set σ : ℤ := ∑ s ∈ range L, sg s with hσ
    have hDsum : ∑ i, ∑ j, D i j = σ := by
      rw [hD]
      have := sum_prefCount arc sg L
      rw [← hσ] at this
      rw [← this]
      push_cast
      rfl
    -- push along a total-preserving direction and recurse
    have hpush : ∀ E : S → S → ℝ, IsCirculation E → ∀ q : S × S, E q.1 q.2 ≠ 0 →
        (∀ i j, E i j ≠ 0 → y i j ∉ intLattice) → ∑ i, ∑ j, E i j = 0 →
        ∃ N : S → S → ℤ, ∃ a b : S,
        (∀ v, netFlow (fun i j ↦ (N i j : ℝ)) v =
          (if v = a then 1 else 0) - if v = b then 1 else 0) ∧
        (∀ i j, ⌊x i j⌋ ≤ N i j ∧ N i j ≤ ⌈x i j⌉) ∧ ∑ i, ∑ j, N i j = T := by
      intro E hEc q hq hEs hEsum
      obtain ⟨t, htc, htb, htcard⟩ := exists_push hyc hyb hEc hq hEs
      refine ih _ (hk ▸ htcard) _ htc htb ?_ rfl
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hEsum, mul_zero, add_zero]
      exact hyT
    by_cases hσ0 : σ = 0
    · exact hpush D hDc p hDp hDs (by rw [hDsum, hσ0, Int.cast_zero])
    set Δ : S → S → ℝ := fun i j ↦ y i j - n i j with hΔ
    have hΔc : IsCirculation Δ := (isCirculation_iff_netFlow Δ).2 fun v ↦ by
      rw [hΔ, netFlow_sub, (isCirculation_iff_netFlow y).1 hyc v,
        (isCirculation_iff_netFlow _).1 hnc v, sub_self]
    have hΔint : ∀ i j, y i j ∈ intLattice → Δ i j = 0 := fun i j hy ↦ by
      obtain ⟨m, hm⟩ := mem_intLattice.1 hy
      have h1 := (hnb i j).1
      have h2 := (hnb i j).2
      rw [← hm, Int.floor_intCast] at h1
      rw [← hm, Int.ceil_intCast] at h2
      have : n i j = m := le_antisymm h2 h1
      simp only [hΔ, ← hm, this, sub_self]
    have hΔs : ∀ i j, Δ i j ≠ 0 → y i j ∉ intLattice := fun i j h hy ↦ h (hΔint i j hy)
    set δ : ℤ := T - ∑ i, ∑ j, n i j with hδ
    have hΔsum : ∑ i, ∑ j, Δ i j = δ := by
      simp only [hΔ, Finset.sum_sub_distrib, hyT, hδ]
      push_cast
      rfl
    by_cases hmult : ∃ θ : ℝ, ∀ i j, Δ i j = θ * D i j
    · -- the finishing step: round along a prefix of the cycle
      obtain ⟨θ, hθ⟩ := hmult
      have hθp : Δ p.1 p.2 = θ := by
        rw [hθ, hD]
        simp only [hDab, Int.cast_one, mul_one]
      have hθ0 : θ ≠ 0 := by
        rw [← hθp]
        intro h0
        have hy := mem_fracSet.1 hp
        apply hy
        have : y p.1 p.2 = n p.1 p.2 := by
          have := h0
          simp only [hΔ, sub_eq_zero] at this
          exact this
        rw [this]
        exact intCast_mem_intLattice _
      have hθ1 : |θ| < 1 := by
        rw [← hθp]
        have := abs_sub_lt_one_of_floor_le_le_ceil (hnb p.1 p.2).1 (hnb p.1 p.2).2
        rw [abs_sub_comm] at this
        exact this
      have hδθ : (δ : ℝ) = θ * σ := by
        rw [← hΔsum, ← hDsum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ ↦ hθ i j
      set ε : ℤ := if 0 < θ then 1 else -1 with hε
      have hεθ : 0 < (ε : ℝ) * θ := by
        rw [hε]
        split_ifs with h
        · push_cast
          linarith
        · push_cast
          have : θ < 0 := lt_of_le_of_ne (not_lt.1 h) hθ0
          linarith
      have hεθ1 : (ε : ℝ) * θ < 1 := by
        rw [hε]
        split_ifs with h
        · push_cast
          linarith [abs_lt.1 hθ1]
        · push_cast
          linarith [abs_lt.1 hθ1]
      have hε2 : ε * ε = 1 := by
        rw [hε]
        split_ifs <;> norm_num
      -- the walk of partial sums
      let f : ℕ → ℤ := fun m ↦ ∑ s ∈ range m, sg s
      have hfstep : ∀ m < L, f (m + 1) = f m + 1 ∨ f (m + 1) = f m - 1 := fun m hm ↦ by
        simp only [f, Finset.sum_range_succ]
        rcases h2 m hm with ⟨hs, -⟩ | ⟨hs, -⟩
        · left
          rw [hs]
        · right
          rw [hs]
          ring
      have hεδ : ((ε * δ : ℤ) : ℝ) = ((ε : ℝ) * θ) * σ := by
        push_cast
        rw [hδθ]
        ring
      have hz : (f 0 ≤ ε * δ ∧ ε * δ ≤ f L) ∨ (f L ≤ ε * δ ∧ ε * δ ≤ f 0) := by
        have hf0 : f 0 = 0 := by simp only [f, Finset.range_zero, Finset.sum_empty]
        have hfL : f L = σ := rfl
        rw [hf0, hfL]
        rcases lt_or_gt_of_ne hσ0 with hneg | hpos
        · right
          have hσr : (σ : ℝ) < 0 := by exact_mod_cast hneg
          constructor
          · have : (σ : ℝ) ≤ ((ε * δ : ℤ) : ℝ) := by rw [hεδ]; nlinarith
            exact_mod_cast this
          · have : ((ε * δ : ℤ) : ℝ) ≤ 0 := by rw [hεδ]; nlinarith
            exact_mod_cast this
        · left
          have hσr : (0 : ℝ) < σ := by exact_mod_cast hpos
          constructor
          · have : (0 : ℝ) ≤ ((ε * δ : ℤ) : ℝ) := by rw [hεδ]; nlinarith
            exact_mod_cast this
          · have : ((ε * δ : ℤ) : ℝ) ≤ σ := by rw [hεδ]; nlinarith
            exact_mod_cast this
      obtain ⟨m, hmL, hfm⟩ := exists_eq_of_unit_steps f L hfstep (ε * δ) hz
      set N : S → S → ℤ := fun i j ↦ n i j + ε * prefCount arc sg m i j with hN
      have hnet : ∀ v, netFlow (fun i j ↦ (N i j : ℝ)) v =
          (ε : ℝ) * ((if v = C 0 then 1 else 0) - if v = C m then 1 else 0) := fun v ↦ by
        have hfun : (fun i j ↦ (N i j : ℝ)) = fun i j ↦
            (n i j : ℝ) + (ε : ℝ) * (prefCount arc sg m i j : ℝ) := by
          funext i j
          simp only [hN]
          push_cast
          rfl
        rw [hfun, netFlow_add, netFlow_mul, (isCirculation_iff_netFlow _).1 hnc v,
          netFlow_prefCount h2 hmL v, zero_add]
      have hbox : ∀ i j, ⌊x i j⌋ ≤ N i j ∧ N i j ≤ ⌈x i j⌉ := by
        intro i j
        by_cases h0 : prefCount arc sg m i j = 0
        · simp only [hN, h0, mul_zero, add_zero]
          exact ⟨le_trans (hfloor i j) (hnb i j).1, le_trans (hnb i j).2 (hceil i j)⟩
        · obtain ⟨s₀, hs₀, -, hm₀, hL₀⟩ := prefCount_ne_zero h4 hmL h0
          have hsg : sg s₀ = 1 ∨ sg s₀ = -1 := by
            rcases h2 s₀ (by omega) with ⟨hs, -⟩ | ⟨hs, -⟩
            · exact Or.inl hs
            · exact Or.inr hs
          have hΔij : Δ i j = θ * sg s₀ := by
            rw [hθ i j, hD]
            simp only [hL₀]
          have hNij : N i j = n i j + ε * sg s₀ := by simp only [hN, hm₀]
          have hc : (ε * sg s₀ = 1 ∧ 0 < Δ i j) ∨ (ε * sg s₀ = -1 ∧ Δ i j < 0) := by
            rw [hΔij]
            rcases hsg with hs | hs <;> rw [hs] <;>
              rcases (show ε = 1 ∨ ε = -1 by rw [hε]; split_ifs <;> simp only [true_or, or_true])
                with he | he <;> rw [he] at hεθ ⊢ <;> push_cast at hεθ ⊢
            · left; exact ⟨by norm_num, by linarith⟩
            · right; exact ⟨by norm_num, by linarith⟩
            · right; exact ⟨by norm_num, by linarith⟩
            · left; exact ⟨by norm_num, by linarith⟩
          rcases hc with ⟨hc1, hpos⟩ | ⟨hc1, hneg⟩
          · rw [hNij, hc1]
            have hlt : (n i j : ℝ) < y i j := by
              have := hpos
              simp only [hΔ, sub_pos] at this
              exact this
            have h1 : n i j < ⌈y i j⌉ := Int.lt_ceil.2 hlt
            constructor
            · have := le_trans (hfloor i j) (hnb i j).1
              omega
            · have := hceil i j
              omega
          · rw [hNij, hc1]
            have hlt : y i j < n i j := by
              have := hneg
              simp only [hΔ, sub_neg] at this
              exact this
            have h1 : ⌊y i j⌋ < n i j := Int.floor_lt.2 hlt
            constructor
            · have := hfloor i j
              omega
            · have := le_trans (hnb i j).2 (hceil i j)
              omega
      have htot : ∑ i, ∑ j, N i j = T := by
        simp only [hN, Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [sum_prefCount, show (∑ s ∈ range m, sg s) = f m from rfl, hfm, ← mul_assoc, hε2,
          one_mul, hδ]
        ring
      rcases (show ε = 1 ∨ ε = -1 by rw [hε]; split_ifs <;> simp only [true_or, or_true])
        with he | he
      · refine ⟨N, C 0, C m, fun v ↦ ?_, hbox, htot⟩
        rw [hnet, he]
        push_cast
        ring
      · refine ⟨N, C m, C 0, fun v ↦ ?_, hbox, htot⟩
        rw [hnet, he]
        push_cast
        ring
    · -- two independent directions: combine them into a total-preserving one
      push Not at hmult
      set E : S → S → ℝ := fun i j ↦ (σ : ℝ) * Δ i j - (δ : ℝ) * D i j with hE
      have hEc : IsCirculation E := (isCirculation_iff_netFlow E).2 fun v ↦ by
        rw [hE, netFlow_sub, netFlow_mul, netFlow_mul, (isCirculation_iff_netFlow _).1 hΔc v,
          (isCirculation_iff_netFlow _).1 hDc v, mul_zero, mul_zero, sub_self]
      have hEs : ∀ i j, E i j ≠ 0 → y i j ∉ intLattice := fun i j h ↦ by
        by_contra hy
        apply h
        have h1 := hΔint i j hy
        have h2 : D i j = 0 := by
          by_contra hd
          exact hDs i j hd hy
        simp only [hE, h1, h2, mul_zero, sub_zero]
      have hEsum : ∑ i, ∑ j, E i j = 0 := by
        simp only [hE, Finset.sum_sub_distrib, ← Finset.mul_sum, hΔsum, hDsum]
        ring
      have hσr : (σ : ℝ) ≠ 0 := by exact_mod_cast hσ0
      obtain ⟨i, j, hij⟩ := hmult ((δ : ℝ) / σ)
      have hEij : E i j ≠ 0 := by
        intro h0
        apply hij
        simp only [hE, sub_eq_zero] at h0
        field_simp
        linarith
      exact hpush E hEc (i, j) hEij hEs hEsum
  exact key _ x hx (fun i j ↦ ⟨Int.floor_le _, Int.le_ceil _⟩) hT rfl

/-! ### Exactly `T` transitions: post #3's conditional MC -/

omit [Fintype S] in
/-- `if v = a` versus `if a = v`, cast from `ℤ`. -/
theorem ite_eq_intCast_ite (v a : S) :
    (if v = a then (1 : ℝ) else 0) = ((if a = v then (1 : ℤ) else 0 : ℤ) : ℝ) := by
  by_cases h : v = a
  · subst h
    simp only [↓reduceIte, Int.cast_one]
  · simp only [h, Ne.symm h, ↓reduceIte, Int.cast_zero]

/-- Net outflows `1{a} − 1{b}` of an integer matrix are `BalancedCounts` from `a` to `b`. -/
theorem balancedCounts_of_netFlow {N₀ : S → S → ℤ} {N : S → S → ℕ}
    (hNz : ∀ i j, ((N i j : ℕ) : ℤ) = N₀ i j) {a b : S}
    (h : ∀ v, netFlow (fun i j ↦ (N₀ i j : ℝ)) v =
      (if v = a then 1 else 0) - if v = b then 1 else 0) :
    BalancedCounts N a b := by
  intro i
  simp only [hNz]
  have hi := h i
  unfold netFlow at hi
  beta_reduce at hi
  rw [ite_eq_intCast_ite, ite_eq_intCast_ite] at hi
  have hz : (∑ j, N₀ i j) - ∑ j, N₀ j i =
      (if a = i then (1 : ℤ) else 0) - if b = i then 1 else 0 := by
    exact_mod_cast hi
  rw [hz]

/-- **A path with exactly `T` transitions realising rounded counts** (post #3, conditional MC,
"allowing for the first and last states"): for an irreducible stochastic `P` with stationary
probability vector `π`, an integer `T` with `T π_i p_ij ≥ 1` on the support of `P`, there are
states `a`, `b` and counts `N` with `|N_ij − T π_i p_ij| < 1`, the support of `P`, total exactly
`T`, balanced from `a` to `b`, and a path `a = s_0, …, s_T = b` with exactly these transition
counts. -/
theorem exists_path_exact_length [Nonempty S] {P : S → S → ℝ} (hP : IsStochastic P)
    {w : S → ℝ} (hw : IsStationaryRow P w) (hw1 : ∑ i, w i = 1) {T : ℕ}
    (hT : ∀ i j, 0 < P i j → 1 ≤ expectedCounts P w T i j)
    (hirr : ∀ i j, Relation.ReflTransGen (fun a b ↦ 0 < P a b) i j) :
    ∃ N : S → S → ℕ, ∃ a b : S, (∀ i j, |(N i j : ℝ) - expectedCounts P w T i j| < 1) ∧
      (∀ i j, N i j ≠ 0 ↔ 0 < P i j) ∧ BalancedCounts N a b ∧ ∑ i, ∑ j, N i j = T ∧
      ∃ s : ℕ → S, s 0 = a ∧ s T = b ∧ ∀ i j, transCount s i j T = N i j := by
  have hsum : ∑ i, ∑ j, expectedCounts P w T i j = ((T : ℤ) : ℝ) := by
    rw [sum_expectedCounts hP hw1, Int.cast_natCast]
  obtain ⟨N₀, a, b, hnet, hb, htot⟩ :=
    exists_open_rounding (isCirculation_expectedCounts hP hw T) hsum
  have hzero : ∀ i j, P i j = 0 → expectedCounts P w T i j = 0 := fun i j h ↦ by
    rw [expectedCounts, h, mul_zero]
  have hn0 : ∀ i j, 0 ≤ N₀ i j := fun i j ↦ by
    rcases (hP.nonneg i j).lt_or_eq with h | h
    · exact le_trans (Int.floor_nonneg.2 (le_trans zero_le_one (hT i j h))) (hb i j).1
    · exact le_trans (by rw [hzero i j h.symm, Int.floor_zero]) (hb i j).1
  set N : S → S → ℕ := fun i j ↦ (N₀ i j).toNat with hN
  have hNz : ∀ i j, ((N i j : ℕ) : ℤ) = N₀ i j := fun i j ↦ Int.toNat_of_nonneg (hn0 i j)
  have hNr : ∀ i j, ((N i j : ℕ) : ℝ) = N₀ i j := fun i j ↦ by
    rw [← Int.cast_natCast, hNz]
  have hsupp : ∀ i j, N i j ≠ 0 ↔ 0 < P i j := by
    intro i j
    constructor
    · intro h
      rcases (hP.nonneg i j).lt_or_eq with hp | hp
      · exact hp
      · exfalso
        have := hb i j
        rw [hzero i j hp.symm, Int.floor_zero, Int.ceil_zero] at this
        have h' := hNz i j
        omega
    · intro hp
      have h1 : 1 ≤ N₀ i j := le_trans (Int.le_floor.2 (by exact_mod_cast hT i j hp)) (hb i j).1
      have h' := hNz i j
      omega
  have hbal : BalancedCounts N a b := balancedCounts_of_netFlow hNz hnet
  have hNT : ∑ i, ∑ j, N i j = T := by
    have : ((∑ i, ∑ j, N i j : ℕ) : ℤ) = (T : ℤ) := by
      push_cast
      simp only [hNz]
      exact htot
    exact_mod_cast this
  have hconn : ∀ i j, N i j ≠ 0 → Relation.ReflTransGen (fun a b ↦ N a b ≠ 0) a i :=
    fun i _ _ ↦ Relation.ReflTransGen.mono (fun a b h ↦ (hsupp a b).2 h) a i (hirr a i)
  obtain ⟨s, hs0, hsT, hsN⟩ := exists_path_of_balanced hbal hconn
  rw [hNT] at hsT hsN
  have habs : ∀ i j, |(N i j : ℝ) - expectedCounts P w T i j| < 1 := fun i j ↦ by
    rw [hNr]
    exact abs_sub_lt_one_of_floor_le_le_ceil (hb i j).1 (hb i j).2
  exact ⟨N, a, b, habs, hsupp, hbal, hNT, s, hs0, hsT, hsN⟩

/-- **Post #3's conditional MC with exactly `T` transitions is well defined**: with the counts
`N` and start `a` of `exists_path_exact_length`, the event "MC from `a` has transition counts `N`
over `T` steps" has positive probability, and conditionally on it the MC path is uniform over
the paths with these counts. -/
theorem conditionalMC_exact_wellDefined {m : ℕ} [Nonempty (Fin m)] {P : Fin m → Fin m → ℝ}
    (hP : IsStochastic P) {w : Fin m → ℝ} (hw : IsStationaryRow P w) (hw1 : ∑ i, w i = 1)
    {T : ℕ} (hT : ∀ i j, 0 < P i j → 1 ≤ expectedCounts P w T i j)
    (hirr : ∀ i j, Relation.ReflTransGen (fun a b ↦ 0 < P a b) i j) :
    ∃ N : Fin m → Fin m → ℕ, ∃ a b : Fin m,
      (∀ i j, |(N i j : ℝ) - expectedCounts P w T i j| < 1) ∧ BalancedCounts N a b ∧
      ∑ i, ∑ j, N i j = T ∧ mcLaw P a T (countClass a N T : Set _) ≠ 0 ∧
      (mcLaw P a T)[|(countClass a N T : Set _)] = uniformOn (countClass a N T : Set _) := by
  obtain ⟨N, a, b, habs, hsupp, hbal, hNT, s, hs0, -, hsN⟩ :=
    exists_path_exact_length hP hw hw1 hT hirr
  set sv : Fin (T + 1) → Fin m := fun t ↦ s t with hsv
  have hagree : ∀ t ≤ T, s t = extendPath sv t := (extendPath_eq_iff s sv).1 rfl
  have hmem : sv ∈ countClass a N T := by
    rw [mem_countClass]
    refine ⟨(hagree 0 (Nat.zero_le T)).symm.trans hs0, fun i j ↦ ?_⟩
    rw [← transCount_congr hagree i j]
    exact hsN i j
  have hpos : 0 < mcLaw P a T {sv} := by
    rw [mcLaw_singleton_of_mem hP a N T hmem, ENNReal.ofReal_pos]
    refine Finset.prod_pos fun i _ ↦ Finset.prod_pos fun j _ ↦ ?_
    by_cases h : N i j = 0
    · rw [h, pow_zero]
      exact one_pos
    · exact pow_pos ((hsupp i j).1 h) _
  have hC : mcLaw P a T (countClass a N T : Set _) ≠ 0 :=
    (lt_of_lt_of_le hpos (measure_mono (Set.singleton_subset_iff.2 (Finset.mem_coe.2 hmem)))).ne'
  exact ⟨N, a, b, habs, hbal, hNT, hC, cond_mcLaw_countClass hP a N T hC⟩

/-- The flip chain at `T = 3`: the open path `0 → 1 → 0 → 1` has the counts `n_01 = 2`,
`n_10 = 1`, within `1` of `x_01 = x_10 = 3/2`, total `3`, balanced from `0` to `1` (the open
rounding of `exists_open_rounding` that the closed one of
`not_exists_rounding_flipChain_total_three` cannot provide). -/
theorem flipChain_open_path_three :
    let s : ℕ → Fin 2 := fun t ↦ if t % 2 = 0 then 0 else 1
    transCount s 0 1 3 = 2 ∧ transCount s 1 0 3 = 1 ∧ transCount s 0 0 3 = 0 ∧
      transCount s 1 1 3 = 0 := by
  intro s
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

end RQMCMarkov.MarkovDriving

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/


/-!
# Real analysis for the law of the iterated logarithm

Copied from the `StochasticStability/LimitTheorems` project (module `LimitTheorems.LILAnalysis`),
with the namespace renamed `MeynTweedie.LimitTheorems` → `RQMCMarkov.MarkovDriving` and the
generic lemma names prefixed `lil_` to avoid clashes; used by `MCRate` for the MC baseline.

Deterministic tools for the Hartman–Wintner LIL (`IIDLIL`), used in the LIL parts of
MT Theorems 17.2.2 and 17.3.6 (pp. 430, 441) and Theorem 17.0.1 (iv) (p. 422).

* `lilScale n = √(2 n log log n)`, the normaliser of the LIL (MT p. 422), with
  `lilScale_mono`, `lilScale_sq`, `sqrt_le_lilScale`, `tendsto_lilScale`, and the ratio limit
  `tendsto_lilScale_div` (`mₙ/n → c > 0` gives `lilScale mₙ / lilScale n → √c`).
* `loglog_increment`, `lilPhi_increment`, `sqrt_lilPhi_increment`: increments of `log log x` and
  of `φ(x) = x / log log x`.
* **Kronecker's lemma** for non-negative terms (`lil_tendsto_sum_div_of_summable`).
* Geometric index sequences: `lil_eventually_floor_pow_succ_le`,
  `summable_exp_neg_mul_loglog_floor_pow` (`Σₖ (log ⌊θᵏ⌋)^{−p} < ∞` for `p > 1`) and
  `not_summable_exp_neg_mul_loglog_pow` (`Σₖ (log mᵏ)^{−p} = ∞` for `p ≤ 1`).
* The truncation levels `lilTruncLevel δ j₀ j = δ √φ(max j j₀)` and weights
  `lilWeight j₀ j = √(J log log J)`, `J = max j j₀`, with the counting estimate
  `sum_inv_lilWeight_le`: `Σ_{j : τⱼ < y} 1/wⱼ ≤ j₀/w_{j₀} + 8 (y/δ + 1)`.
-/

namespace RQMCMarkov.MarkovDriving

open Filter Topology

/-- The LIL normaliser `√(2 n log log n)`. -/
noncomputable def lilScale (n : ℕ) : ℝ := √(2 * n * Real.log (Real.log n))

/-- `log log x ≥ 1` once `log x ≥ 3`. -/
theorem one_le_loglog {x : ℝ} (hx : 3 ≤ Real.log x) : 1 ≤ Real.log (Real.log x) := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-- Eventually `log n ≥ c`. -/
theorem lil_eventually_le_log (c : ℝ) : ∀ᶠ n : ℕ in atTop, c ≤ Real.log n :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop c

/-- `log (x + 1) − log x ≤ 1/x` for `x > 0`. -/
theorem lil_log_add_one_sub_log_le {x : ℝ} (hx : 0 < x) :
    Real.log (x + 1) - Real.log x ≤ 1 / x := by
  rw [← Real.log_div (by linarith) hx.ne']
  have := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
  have e : (x + 1) / x - 1 = 1 / x := by field_simp; ring
  linarith

/-- The increment of `log log`: for `log x ≥ 3`,
`0 ≤ log log (x + 1) − log log x ≤ 1/(x log x)`. -/
theorem loglog_increment {x : ℝ} (hx : 1 ≤ x) (hl : 3 ≤ Real.log x) :
    0 ≤ Real.log (Real.log (x + 1)) - Real.log (Real.log x) ∧
      Real.log (Real.log (x + 1)) - Real.log (Real.log x) ≤ 1 / (x * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := by linarith
  have hle : Real.log x ≤ Real.log (x + 1) := Real.log_le_log hx0 (by linarith)
  have hlx1 : 0 < Real.log (x + 1) := by linarith
  constructor
  · have := Real.log_le_log hlx hle
    linarith
  · rw [← Real.log_div hlx1.ne' hlx.ne']
    have h1 := Real.log_le_sub_one_of_pos (show 0 < Real.log (x + 1) / Real.log x by positivity)
    have h2 := lil_log_add_one_sub_log_le hx0
    have e : Real.log (x + 1) / Real.log x - 1 = (Real.log (x + 1) - Real.log x) / Real.log x := by
      field_simp
    have h3 : (Real.log (x + 1) - Real.log x) / Real.log x ≤ (1 / x) / Real.log x :=
      div_le_div_of_nonneg_right h2 hlx.le
    have e2 : (1 / x) / Real.log x = 1 / (x * Real.log x) := by field_simp
    linarith

/-- `φ(x) = x / log log x`, the square of the truncation level of the LIL (up to a constant). -/
noncomputable def lilPhi (x : ℝ) : ℝ := x / Real.log (Real.log x)

/-- The increments of `φ(x) = x / log log x` for `log x ≥ 3`:
`φ(x) + 1/(2 log log (x+1)) ≤ φ(x + 1) ≤ φ(x) + 1`. -/
theorem lilPhi_increment {x : ℝ} (hx : 1 ≤ x) (hl : 3 ≤ Real.log x) :
    lilPhi x + 1 / (2 * Real.log (Real.log (x + 1))) ≤ lilPhi (x + 1) ∧
      lilPhi (x + 1) ≤ lilPhi x + 1 := by
  obtain ⟨hd0, hd1⟩ := loglog_increment hx hl
  set A := Real.log (Real.log x) with hA
  set A' := Real.log (Real.log (x + 1)) with hA'
  have hA1 : 1 ≤ A := one_le_loglog hl
  have hA'1 : A ≤ A' := by linarith
  have hx0 : 0 < x := by linarith
  have hjd : x * (A' - A) ≤ 1 / 3 := by
    have h1 : x * (A' - A) ≤ x * (1 / (x * Real.log x)) :=
      mul_le_mul_of_nonneg_left hd1 hx0.le
    have h2 : x * (1 / (x * Real.log x)) = 1 / Real.log x := by
      field_simp
    have h3 : 1 / Real.log x ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hl
    linarith
  have hA0 : 0 < A := by linarith
  have hA'0 : 0 < A' := by linarith
  simp only [lilPhi]
  rw [← hA, ← hA']
  constructor
  · rw [div_add_div _ _ hA0.ne' (by positivity), div_le_div_iff₀ (by positivity) hA'0]
    nlinarith
  · rw [div_add_one hA0.ne', div_le_div_iff₀ hA'0 hA0]
    nlinarith

/-- The increments of `√φ`: for `log x ≥ 3`, `1/(8 √(x log log x)) ≤ √φ(x + 1) − √φ(x)`. -/
theorem sqrt_lilPhi_increment {x : ℝ} (hx : 1 ≤ x) (hl : 3 ≤ Real.log x) :
    1 / (8 * √(x * Real.log (Real.log x))) ≤ √(lilPhi (x + 1)) - √(lilPhi x) := by
  obtain ⟨h1, -⟩ := lilPhi_increment hx hl
  obtain ⟨hd0, hd1⟩ := loglog_increment hx hl
  set A := Real.log (Real.log x) with hA
  set A' := Real.log (Real.log (x + 1)) with hA'
  have hA1 : 1 ≤ A := one_le_loglog hl
  have hx0 : 0 < x := by linarith
  have hA0 : 0 < A := by linarith
  have hA'0 : 0 < A' := by linarith
  have hlx : 0 < Real.log x := by linarith
  -- `A' ≤ 2 A`
  have hA'2 : A' ≤ 2 * A := by
    have : 1 / (x * Real.log x) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    linarith
  set u := √(lilPhi (x + 1)) with hu
  set v := √(lilPhi x) with hv
  have hφ0 : 0 ≤ lilPhi x := div_nonneg hx0.le hA0.le
  have hφ1 : 0 < lilPhi (x + 1) := div_pos (by linarith) hA'0
  have hu0 : 0 < u := Real.sqrt_pos.2 hφ1
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hpos' : 0 < 1 / (2 * A') := by positivity
  have hvu : v ≤ u := Real.sqrt_le_sqrt (by linarith)
  have hu2 : u ^ 2 = lilPhi (x + 1) := Real.sq_sqrt hφ1.le
  have hv2 : v ^ 2 = lilPhi x := Real.sq_sqrt hφ0
  -- `u − v ≥ (u² − v²)/(2u) ≥ 1/(4 A' u)`
  have hdiff : 1 / (2 * A') ≤ u ^ 2 - v ^ 2 := by rw [hu2, hv2]; linarith
  have huv : 1 / (4 * A' * u) ≤ u - v := by
    have e : u - v = (u ^ 2 - v ^ 2) / (u + v) := by
      field_simp [show u + v ≠ 0 by linarith]
      ring
    rw [e, div_le_div_iff₀ (by positivity) (by linarith)]
    have h4 := mul_le_mul_of_nonneg_right hdiff (show 0 ≤ 4 * A' * u by positivity)
    have h5 : 1 / (2 * A') * (4 * A' * u) = 2 * u := by field_simp; ring
    linarith
  -- `A' u = √(A' (x + 1))` and `A' (x + 1) ≤ 4 x A`
  have hAu : A' * u = √(A' * (x + 1)) := by
    have e1 : A' * u = √(A' ^ 2 * lilPhi (x + 1)) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hA'0.le]
    rw [e1, lilPhi, ← hA']
    congr 1
    field_simp
  have hsq : √(A' * (x + 1)) ≤ 2 * √(x * A) := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
      ← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    nlinarith
  have hpos : 0 < √(x * A) := Real.sqrt_pos.2 (by positivity)
  calc 1 / (8 * √(x * A)) ≤ 1 / (4 * √(A' * (x + 1))) := by
        apply one_div_le_one_div_of_le (by positivity)
        linarith
    _ = 1 / (4 * A' * u) := by rw [mul_assoc, hAu]
    _ ≤ u - v := huv

/-! ### Kronecker's lemma for non-negative terms -/

/-- **Kronecker's lemma** for non-negative terms: if `aⱼ ≥ 0`, `0 < wⱼ` increases to `∞` and
`Σ aⱼ/wⱼ < ∞`, then `(Σ_{j<n} aⱼ)/wₙ → 0`. -/
theorem lil_tendsto_sum_div_of_summable {a w : ℕ → ℝ} (ha : ∀ j, 0 ≤ a j) (hw : ∀ j, 0 < w j)
    (hmono : Monotone w) (hwt : Tendsto w atTop atTop) (hs : Summable fun j => a j / w j) :
    Tendsto (fun n => (∑ j ∈ Finset.range n, a j) / w n) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have htail := tendsto_sum_nat_add fun j => a j / w j
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 htail) (ε / 2) (by positivity)
  have hK' := hK K le_rfl
  have hT0 : 0 ≤ ∑' i, a (i + K) / w (i + K) :=
    tsum_nonneg fun i => div_nonneg (ha _) (hw _).le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hT0] at hK'
  set C := ∑ j ∈ Finset.range K, a j with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun j _ => ha j
  have hCw : Tendsto (fun n => C / w n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hwt
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hCw) (ε / 2) (by positivity)
  refine ⟨max K N, fun n hn => ?_⟩
  have hKn : K ≤ n := le_of_max_le_left hn
  have hNn : N ≤ n := le_of_max_le_right hn
  have hCn := hN n hNn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hC0 (hw n).le)] at hCn
  have hsum0 : 0 ≤ ∑ j ∈ Finset.range n, a j := Finset.sum_nonneg fun j _ => ha j
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hsum0 (hw n).le)]
  -- the sum over `[K, n)`
  have hIco : ∑ j ∈ Finset.Ico K n, a j ≤ w n * ∑' i, a (i + K) / w (i + K) := by
    have h1 : ∑ j ∈ Finset.Ico K n, a j ≤ ∑ j ∈ Finset.Ico K n, w n * (a j / w j) :=
      Finset.sum_le_sum fun j hj => by
        have hjn : j ≤ n := (Finset.mem_Ico.1 hj).2.le
        rw [mul_div_assoc', le_div_iff₀ (hw j)]
        rw [mul_comm (w n)]
        exact mul_le_mul_of_nonneg_left (hmono hjn) (ha j)
    have h2 : ∑ j ∈ Finset.Ico K n, a j / w j ≤ ∑' i, a (i + K) / w (i + K) := by
      rw [Finset.sum_Ico_eq_sum_range]
      have hsK : Summable fun i => a (i + K) / w (i + K) := (summable_nat_add_iff K).2 hs
      calc ∑ i ∈ Finset.range (n - K), a (K + i) / w (K + i)
          = ∑ i ∈ Finset.range (n - K), a (i + K) / w (i + K) := by
            simp_rw [add_comm K]
        _ ≤ _ := hsK.sum_le_tsum _ fun i _ => div_nonneg (ha _) (hw _).le
    rw [← Finset.mul_sum] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (hw n).le)
  have hsplit : ∑ j ∈ Finset.range n, a j = C + ∑ j ∈ Finset.Ico K n, a j :=
    (Finset.sum_range_add_sum_Ico _ hKn).symm
  rw [hsplit, add_div]
  have h3 : (∑ j ∈ Finset.Ico K n, a j) / w n ≤ ∑' i, a (i + K) / w (i + K) := by
    rw [div_le_iff₀ (hw n)]; linarith
  linarith

/-! ### The LIL normaliser -/

/-- `lilScale n ≥ 0`. -/
theorem lilScale_nonneg (n : ℕ) : 0 ≤ lilScale n := Real.sqrt_nonneg _

/-- `lilScale n² = 2 n log log n` when `log n ≥ 3`. -/
theorem lilScale_sq {n : ℕ} (h : 3 ≤ Real.log n) :
    lilScale n ^ 2 = 2 * n * Real.log (Real.log n) := by
  have := one_le_loglog h
  rw [lilScale, Real.sq_sqrt (by positivity)]

/-- `lilScale` is monotone beyond `log n ≥ 3`. -/
theorem lilScale_mono {m n : ℕ} (hm : 3 ≤ Real.log m) (hmn : m ≤ n) :
    lilScale m ≤ lilScale n := by
  have h1 := one_le_loglog hm
  have hm0 : (0 : ℝ) < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · simp [h] at hm; linarith
    · exact_mod_cast h
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hl : Real.log m ≤ Real.log n := Real.log_le_log hm0 hmn'
  have hll : Real.log (Real.log m) ≤ Real.log (Real.log n) :=
    Real.log_le_log (by linarith) hl
  apply Real.sqrt_le_sqrt
  have : (0 : ℝ) ≤ m := hm0.le
  nlinarith

/-- `√n ≤ lilScale n` when `log n ≥ 3`. -/
theorem sqrt_le_lilScale {n : ℕ} (h : 3 ≤ Real.log n) : √(n : ℝ) ≤ lilScale n := by
  have := one_le_loglog h
  apply Real.sqrt_le_sqrt
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- `lilScale n → ∞`. -/
theorem tendsto_lilScale : Tendsto lilScale atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [lil_eventually_le_log 3] with n hn
  exact sqrt_le_lilScale hn

/-- `lilScale n > 0` when `log n ≥ 3`. -/
theorem lilScale_pos {n : ℕ} (h : 3 ≤ Real.log n) : 0 < lilScale n := by
  have := one_le_loglog h
  have hn : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · simp [h0] at h; linarith
    · exact_mod_cast h0
  exact Real.sqrt_pos.2 (by positivity)

/-! ### Geometric index sequences -/

/-- For `θ > 1`, eventually `⌊θ^(k+1)⌋ ≤ θ² ⌊θ^k⌋`. -/
theorem lil_eventually_floor_pow_succ_le {θ : ℝ} (hθ : 1 < θ) :
    ∀ᶠ k : ℕ in atTop, (⌊θ ^ (k + 1)⌋₊ : ℝ) ≤ θ ^ 2 * ⌊θ ^ k⌋₊ := by
  have ht : Tendsto (fun k : ℕ => θ ^ k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hθ
  filter_upwards [ht.eventually_ge_atTop (θ ^ 2 / (θ - 1))] with k hk
  have hθ1 : 0 < θ - 1 := by linarith
  have hθ0 : 0 < θ := by linarith
  have hpk : 0 < θ ^ k := by positivity
  have h1 : (⌊θ ^ (k + 1)⌋₊ : ℝ) ≤ θ ^ (k + 1) := Nat.floor_le (by positivity)
  have h2 : θ ^ k - 1 ≤ (⌊θ ^ k⌋₊ : ℝ) := by have := Nat.lt_floor_add_one (θ ^ k); linarith
  have h3 : θ ^ 2 ≤ θ ^ k * (θ - 1) := by rwa [div_le_iff₀ hθ1] at hk
  have h4 : θ ^ (k + 1) ≤ θ ^ 2 * (θ ^ k - 1) := by
    have e : θ ^ (k + 1) = θ ^ k * θ := pow_succ θ k
    have h5 : 0 ≤ θ ^ k * (θ - 1) ^ 2 := by positivity
    nlinarith
  have h6 : θ ^ 2 * (θ ^ k - 1) ≤ θ ^ 2 * ⌊θ ^ k⌋₊ :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  linarith

/-- For `θ > 1` and `p > 1`, `Σₖ exp(−p log log ⌊θ^k⌋) < ∞`. -/
theorem summable_exp_neg_mul_loglog_floor_pow {θ p : ℝ} (hθ : 1 < θ) (hp : 1 < p) :
    Summable fun k : ℕ => Real.exp (-(p * Real.log (Real.log (⌊θ ^ k⌋₊ : ℝ)))) := by
  have hlθ : 0 < Real.log θ := Real.log_pos hθ
  set c := Real.log θ / 2 with hc
  have hc0 : 0 < c := by positivity
  have hg : Summable fun k : ℕ => c ^ (-p) * (k : ℝ) ^ (-p) :=
    (Real.summable_nat_rpow.2 (by linarith)).mul_left _
  refine hg.of_norm_bounded_eventually_nat ?_
  have ht : Tendsto (fun k : ℕ => θ ^ k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hθ
  have ht2 : Tendsto (fun k : ℕ => (k : ℝ) * Real.log θ) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hlθ
  filter_upwards [ht.eventually_ge_atTop 2, ht2.eventually_ge_atTop (2 * Real.log 2),
    eventually_ge_atTop 1] with k hk1 hk2 hk3
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk3
  have hfl : θ ^ k / 2 ≤ (⌊θ ^ k⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (θ ^ k); linarith
  have hlog : c * k ≤ Real.log (⌊θ ^ k⌋₊ : ℝ) := by
    have h1 : Real.log (θ ^ k / 2) ≤ Real.log (⌊θ ^ k⌋₊ : ℝ) :=
      Real.log_le_log (by positivity) hfl
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at h1
    have : c * k = k * Real.log θ / 2 := by rw [hc]; ring
    linarith
  have hll : Real.log (c * k) ≤ Real.log (Real.log (⌊θ ^ k⌋₊ : ℝ)) :=
    Real.log_le_log (by positivity) hlog
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-(p * Real.log (Real.log (⌊θ ^ k⌋₊ : ℝ))))
      ≤ Real.exp (Real.log (c * k) * (-p)) := by
        apply Real.exp_le_exp.2; nlinarith
    _ = (c * k) ^ (-p) := (Real.rpow_def_of_pos (by positivity) _).symm
    _ = c ^ (-p) * (k : ℝ) ^ (-p) := Real.mul_rpow hc0.le (by positivity)

/-- For an integer `m ≥ 2`, `C > 0` and `p ≤ 1`, `Σₖ C exp(−p log log mᵏ) = ∞`. -/
theorem not_summable_exp_neg_mul_loglog_pow {m : ℕ} (hm : 2 ≤ m) {p : ℝ} (hp : p ≤ 1)
    {C : ℝ} (hC : 0 < C) :
    ¬ Summable fun k : ℕ => C * Real.exp (-(p * Real.log (Real.log ((m : ℝ) ^ k)))) := by
  intro h
  have hm1 : (1 : ℝ) < m := by exact_mod_cast hm
  have hlm : 0 < Real.log m := Real.log_pos hm1
  have h2 := (summable_nat_add_iff 1).2 h
  have h3 : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (-p) := by
    refine (h2.mul_left (C⁻¹ * Real.log m ^ p)).congr fun k => ?_
    set K : ℝ := ((k + 1 : ℕ) : ℝ) with hK
    have hK0 : 0 < K := by positivity
    have e1 : Real.log (Real.log ((m : ℝ) ^ (k + 1))) = Real.log K + Real.log (Real.log m) := by
      rw [Real.log_pow, Real.log_mul hK0.ne' hlm.ne']
    have e2 : Real.exp (-(p * (Real.log K + Real.log (Real.log m)))) =
        K ^ (-p) * Real.log m ^ (-p) := by
      rw [Real.rpow_def_of_pos hK0, Real.rpow_def_of_pos hlm, ← Real.exp_add]
      ring_nf
    have e3 : Real.log m ^ p * Real.log m ^ (-p) = 1 := by
      rw [← Real.rpow_add hlm, add_neg_cancel, Real.rpow_zero]
    rw [e1, e2]
    calc C⁻¹ * Real.log m ^ p * (C * (K ^ (-p) * Real.log m ^ (-p)))
        = (C⁻¹ * C) * (Real.log m ^ p * Real.log m ^ (-p)) * K ^ (-p) := by ring
      _ = K ^ (-p) := by rw [inv_mul_cancel₀ hC.ne', e3]; ring
  exact absurd (Real.summable_nat_rpow.1 ((summable_nat_add_iff 1).1 h3)) (by linarith)

/-! ### Ratios of the normaliser -/

/-- If `mₙ/n → c > 0` then `log log mₙ / log log n → 1`. -/
theorem tendsto_loglog_div {m : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hm : Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 c)) :
    Tendsto (fun n => Real.log (Real.log (m n)) / Real.log (Real.log n)) atTop (𝓝 1) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  -- `mₙ → ∞`
  have hmt : Tendsto (fun n => (m n : ℝ)) atTop atTop := by
    refine (hm.pos_mul_atTop hc hn).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn1
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  have hlog := Real.tendsto_log_atTop.comp hn
  have hlogm := Real.tendsto_log_atTop.comp hmt
  -- `log mₙ − log n → log c`
  have h1 : Tendsto (fun n => Real.log (m n) - Real.log n) atTop (𝓝 (Real.log c)) := by
    refine ((Real.continuousAt_log hc.ne').tendsto.comp hm).congr' ?_
    filter_upwards [eventually_ge_atTop 1, hmt.eventually_gt_atTop 0] with n hn1 hm0
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    simp only [Function.comp_apply]
    rw [Real.log_div hm0.ne' this]
  -- `log mₙ / log n → 1`
  have h2 : Tendsto (fun n => Real.log (m n) / Real.log n) atTop (𝓝 1) := by
    have := tendsto_const_nhds (x := (1 : ℝ)).add (h1.div_atTop hlog)
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [hlog.eventually_gt_atTop 0] with n hn0
    simp only [Function.comp_apply] at hn0 ⊢
    field_simp
    ring
  -- `log log mₙ − log log n → 0`
  have h3 : Tendsto (fun n => Real.log (Real.log (m n)) - Real.log (Real.log n)) atTop
      (𝓝 0) := by
    have := (Real.continuousAt_log one_ne_zero).tendsto.comp h2
    rw [Real.log_one] at this
    refine this.congr' ?_
    filter_upwards [hlog.eventually_gt_atTop 0, hlogm.eventually_gt_atTop 0] with n hn0 hm0
    simp only [Function.comp_apply] at hn0 hm0 ⊢
    rw [Real.log_div hm0.ne' hn0.ne']
  have hll := Real.tendsto_log_atTop.comp hlog
  have := tendsto_const_nhds (x := (1 : ℝ)).add (h3.div_atTop hll)
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [hll.eventually_gt_atTop 0] with n hn0
  simp only [Function.comp_apply] at hn0 ⊢
  field_simp
  ring

/-- If `mₙ/n → c > 0` then `lilScale mₙ / lilScale n → √c`. -/
theorem tendsto_lilScale_div {m : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hm : Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 c)) :
    Tendsto (fun n => lilScale (m n) / lilScale n) atTop (𝓝 √c) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hmt : Tendsto (fun n => (m n : ℝ)) atTop atTop := by
    refine (hm.pos_mul_atTop hc hn).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn1
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  have hl := tendsto_loglog_div hc hm
  have hprod := hm.mul hl
  rw [mul_one] at hprod
  have hs := (Real.continuous_sqrt.tendsto c).comp hprod
  refine hs.congr' ?_
  have hm3 : ∀ᶠ n in atTop, 3 ≤ Real.log (m n) :=
    (Real.tendsto_log_atTop.comp hmt).eventually_ge_atTop 3
  filter_upwards [hm3, lil_eventually_le_log 3] with n hm3 hn3
  have h1 := one_le_loglog hm3
  have h2 := one_le_loglog hn3
  have hn0 : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · simp [h0] at hn3; linarith
    · exact_mod_cast h0
  simp only [Function.comp_apply, lilScale]
  rw [← Real.sqrt_div' _ (by positivity)]
  congr 1
  field_simp

/-! ### Truncation levels and weights for the upper half -/

/-- The truncation level `δ √φ(max j j₀)` of the upper half of the LIL. -/
noncomputable def lilTruncLevel (δ : ℝ) (j₀ j : ℕ) : ℝ := δ * √(lilPhi (max j j₀ : ℕ))

/-- The Kronecker weight `√(J log log J)`, `J = max j j₀`. -/
noncomputable def lilWeight (j₀ j : ℕ) : ℝ :=
  √((max j j₀ : ℕ) * Real.log (Real.log (max j j₀ : ℕ)))

/-- `log j ≥ 3` for every `j ≥ j₀` once `log j₀ ≥ 3`. -/
theorem lil_three_le_log_of_le {j₀ j : ℕ} (hj₀ : 3 ≤ Real.log j₀) (hj : j₀ ≤ j) :
    3 ≤ Real.log j := by
  have h0 : (0 : ℝ) < j₀ := by
    rcases Nat.eq_zero_or_pos j₀ with h | h
    · simp [h] at hj₀; linarith
    · exact_mod_cast h
  exact hj₀.trans (Real.log_le_log h0 (by exact_mod_cast hj))

/-- `1 ≤ x` when `3 ≤ log x` and `0 ≤ x`. -/
theorem lil_one_le_of_three_le_log {x : ℝ} (hx0 : 0 ≤ x) (h : 3 ≤ Real.log x) : 1 ≤ x := by
  by_contra hx
  push Not at hx
  have := Real.log_nonpos hx0 hx.le
  linarith

/-- The weights are positive when `log j₀ ≥ 3`. -/
theorem lilWeight_pos {j₀ : ℕ} (hj₀ : 3 ≤ Real.log j₀) (j : ℕ) : 0 < lilWeight j₀ j := by
  have h3 := lil_three_le_log_of_le hj₀ (le_max_right j j₀)
  have := one_le_loglog h3
  have := lil_one_le_of_three_le_log (Nat.cast_nonneg _) h3
  exact Real.sqrt_pos.2 (by positivity)

/-- The weights are monotone. -/
theorem lilWeight_mono {j₀ : ℕ} (hj₀ : 3 ≤ Real.log j₀) : Monotone (lilWeight j₀) := by
  intro i j hij
  have hi := lil_three_le_log_of_le hj₀ (le_max_right i j₀)
  have hj := lil_three_le_log_of_le hj₀ (le_max_right j j₀)
  have h1 := one_le_loglog hi
  have hi1 := lil_one_le_of_three_le_log (Nat.cast_nonneg _) hi
  have hmax : ((max i j₀ : ℕ) : ℝ) ≤ (max j j₀ : ℕ) := by
    exact_mod_cast max_le_max hij le_rfl
  have hl : Real.log (max i j₀ : ℕ) ≤ Real.log (max j j₀ : ℕ) :=
    Real.log_le_log (by linarith) hmax
  have hll : Real.log (Real.log (max i j₀ : ℕ)) ≤ Real.log (Real.log (max j j₀ : ℕ)) :=
    Real.log_le_log (by linarith) hl
  apply Real.sqrt_le_sqrt
  nlinarith

/-- The weights tend to infinity. -/
theorem tendsto_lilWeight {j₀ : ℕ} : Tendsto (lilWeight j₀) atTop atTop := by
  refine (tendsto_lilScale.const_mul_atTop (show (0 : ℝ) < (√2)⁻¹ by positivity)).congr' ?_
  filter_upwards [eventually_ge_atTop j₀] with j hj
  rw [lilWeight, lilScale, max_eq_left hj, mul_assoc, Real.sqrt_mul (by norm_num),
    ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- `lilScale j = √2 · lilWeight j₀ j` for `j ≥ j₀`. -/
theorem lilScale_eq_lilWeight {j₀ j : ℕ} (hj : j₀ ≤ j) :
    lilScale j = √2 * lilWeight j₀ j := by
  rw [lilWeight, lilScale, max_eq_left hj, mul_assoc, Real.sqrt_mul (by norm_num)]

/-- `√(a + 1) ≤ √a + 1` for `a ≥ 0`. -/
theorem lil_sqrt_add_one_le (a : ℝ) (ha : 0 ≤ a) : √(a + 1) ≤ √a + 1 := by
  rw [Real.sqrt_le_left (by positivity)]
  have := Real.sq_sqrt ha
  have := Real.sqrt_nonneg a
  nlinarith

/-- **The counting estimate for the truncated tails**: for `δ > 0` and `y ≥ 0`,
`Σ_{j<n, τⱼ < y} 1/wⱼ ≤ j₀/w_{j₀} + 8 (y/δ + 1)`, where `τⱼ = lilTruncLevel δ j₀ j` and
`wⱼ = lilWeight j₀ j`. -/
theorem sum_inv_lilWeight_le {δ : ℝ} (hδ : 0 < δ) {j₀ : ℕ} (hj₀ : 3 ≤ Real.log j₀)
    {y : ℝ} (hy : 0 ≤ y) (n : ℕ) :
    ∑ j ∈ Finset.range n, (if lilTruncLevel δ j₀ j < y then 1 / lilWeight j₀ j else 0) ≤
      j₀ / lilWeight j₀ j₀ + 8 * (y / δ + 1) := by
  set f : ℕ → ℝ := fun j => if lilTruncLevel δ j₀ j < y then 1 / lilWeight j₀ j else 0
    with hf
  have hf0 : ∀ j, 0 ≤ f j := fun j => by
    simp only [hf]
    split_ifs
    · exact (one_div_pos.2 (lilWeight_pos hj₀ j)).le
    · exact le_rfl
  have hfle : ∀ j, f j ≤ 1 / lilWeight j₀ j := fun j => by
    simp only [hf]
    split_ifs
    · exact le_rfl
    · exact (one_div_pos.2 (lilWeight_pos hj₀ j)).le
  -- the values of `φ` beyond `j₀`
  set g : ℕ → ℝ := fun N => √(lilPhi (N : ℝ)) with hg
  have hstep : ∀ N, j₀ ≤ N → 1 / lilWeight j₀ N ≤ 8 * (g (N + 1) - g N) ∧ g N ≤ g (N + 1) ∧
      g (N + 1) ≤ g N + 1 := by
    intro N hN
    have h3 := lil_three_le_log_of_le hj₀ hN
    have h1 := lil_one_le_of_three_le_log (Nat.cast_nonneg _) h3
    obtain ⟨hi1, hi2⟩ := lilPhi_increment h1 h3
    have hinc := sqrt_lilPhi_increment h1 h3
    have hA := one_le_loglog h3
    have hA' : 0 < Real.log (Real.log ((N : ℝ) + 1)) := by
      have := (loglog_increment h1 h3).1; linarith
    have hφ0 : 0 ≤ lilPhi N := div_nonneg (by linarith) (by linarith)
    have hw : lilWeight j₀ N = √((N : ℝ) * Real.log (Real.log N)) := by
      rw [lilWeight, max_eq_left hN]
    simp only [hg]
    push_cast
    have hpos : 0 < 1 / (2 * Real.log (Real.log ((N : ℝ) + 1))) := by positivity
    have hmono : √(lilPhi N) ≤ √(lilPhi ((N : ℝ) + 1)) := Real.sqrt_le_sqrt (by linarith)
    refine ⟨?_, hmono, (Real.sqrt_le_sqrt hi2).trans (lil_sqrt_add_one_le _ hφ0)⟩
    rw [hw]
    have : 1 / √((N : ℝ) * Real.log (Real.log N)) =
        8 * (1 / (8 * √((N : ℝ) * Real.log (Real.log N)))) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hinc (by norm_num)
  -- induction beyond `j₀`
  have hind : ∀ N, j₀ ≤ N → ∑ j ∈ Finset.Ico j₀ N, f j ≤ 8 * min (g N) (y / δ + 1) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      simp only [Finset.Ico_self, Finset.sum_empty]
      have : 0 ≤ g j₀ := Real.sqrt_nonneg _
      have : 0 ≤ y / δ + 1 := by positivity
      positivity
    | succ N hN ih =>
      rw [Finset.sum_Ico_succ_top hN]
      obtain ⟨hs1, hs2, hs3⟩ := hstep N hN
      by_cases hlt : lilTruncLevel δ j₀ N < y
      · have hfN : f N = 1 / lilWeight j₀ N := by simp only [hf, hlt, ite_true]
        have hgN : g N < y / δ := by
          rw [lilTruncLevel, max_eq_left hN] at hlt
          rw [lt_div_iff₀ hδ]
          simp only [hg]
          linarith
        have hmin1 : min (g N) (y / δ + 1) ≤ g N := min_le_left _ _
        have hmin2 : min (g (N + 1)) (y / δ + 1) = g (N + 1) :=
          min_eq_left (by linarith)
        rw [hfN, hmin2]
        linarith
      · have hfN : f N = 0 := by simp only [hf, hlt, ite_false]
        rw [hfN, add_zero]
        exact ih.trans (mul_le_mul_of_nonneg_left (min_le_min hs2 le_rfl) (by norm_num))
  -- the first `j₀` terms
  have hfirst : ∑ j ∈ Finset.range j₀, f j ≤ j₀ / lilWeight j₀ j₀ := by
    calc ∑ j ∈ Finset.range j₀, f j ≤ ∑ _j ∈ Finset.range j₀, 1 / lilWeight j₀ j₀ :=
          Finset.sum_le_sum fun j hj => by
            have : lilWeight j₀ j = lilWeight j₀ j₀ := by
              rw [lilWeight, lilWeight, max_eq_right (Finset.mem_range.1 hj).le, max_self]
            rw [← this]; exact hfle j
      _ = j₀ / lilWeight j₀ j₀ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one_div]
  calc ∑ j ∈ Finset.range n, f j ≤ ∑ j ∈ Finset.range (max n j₀), f j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (le_max_left _ _))
          fun j _ _ => hf0 j
    _ = ∑ j ∈ Finset.range j₀, f j + ∑ j ∈ Finset.Ico j₀ (max n j₀), f j :=
        (Finset.sum_range_add_sum_Ico _ (le_max_right _ _)).symm
    _ ≤ j₀ / lilWeight j₀ j₀ + 8 * min (g (max n j₀)) (y / δ + 1) :=
        add_le_add hfirst (hind _ (le_max_right _ _))
    _ ≤ j₀ / lilWeight j₀ j₀ + 8 * (y / δ + 1) := by
        have := min_le_right (g (max n j₀)) (y / δ + 1)
        linarith

end RQMCMarkov.MarkovDriving

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Kolmogorov's inequality and a random-index CLT step (MT Theorem D.6.3, §17.2.2)

Copied from the `StochasticStability/LimitTheorems` project
(module `LimitTheorems.KolmogorovAnscombe`),
with the namespace renamed `MeynTweedie.LimitTheorems` → `RQMCMarkov.MarkovDriving` and the
generic lemma names prefixed `lil_` to avoid clashes; used by `MCRate` for the MC baseline.

The proof of Theorem 17.2.2 (p. 431) replaces the random number `ℓₙ` of completed cycles by the
deterministic `n* = ⌊π(α) n⌋` using Kolmogorov's inequality (Theorem D.6.3). Mathlib has Doob's
maximal inequality but not Kolmogorov's in this form, so both are proved here for independent
real random variables on a probability space.

* `lil_integral_sq_sum_range`: for independent centred `Yⱼ ∈ L²`,
  `E[(Σ_{j<N} Yⱼ)²] = Σ_{j<N} E[Yⱼ²]`.
* **Kolmogorov's inequality** (`lil_kolmogorov_ineq`, MT Theorem D.6.3):
  `t² P(max_{k ≤ N} |Sₖ| ≥ t) ≤ Σ_{j<N} E[Yⱼ²]`.
* `lil_kolmogorov_ineq_shift`: the same for the sums `Σ_{j<k} Y_{a+j}` started at `a`.
* **The random-index step** (`lil_tendstoInMeasure_anscombe`, the argument (17.19)–(17.20)): for
  i.i.d. centred `Yⱼ ∈ L²` and random indices `Kₙ` with `Kₙ/n → c > 0` almost surely,
  `(S_{Kₙ} − S_{⌊cn⌋})/√n → 0` in probability.
-/

namespace RQMCMarkov.MarkovDriving

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

/-! ### Orthogonality of sums -/

/-- For independent centred `Yⱼ ∈ L²`, `E[(Σ_{j<N} Yⱼ)²] = Σ_{j<N} E[Yⱼ²]`. -/
theorem lil_integral_sq_sum_range {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {Y : ℕ → Ω → ℝ} (hind : iIndepFun Y Q) (hm : ∀ j, Measurable (Y j))
    (hL2 : ∀ j, MemLp (Y j) 2 Q) (h0 : ∀ j, ∫ ω, Y j ω ∂Q = 0) (N : ℕ) :
    ∫ ω, (∑ j ∈ Finset.range N, Y j ω) ^ 2 ∂Q = ∑ j ∈ Finset.range N, ∫ ω, Y j ω ^ 2 ∂Q := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hS2 : MemLp (fun ω => ∑ j ∈ Finset.range N, Y j ω) 2 Q :=
      memLp_finsetSum _ fun j _ => hL2 j
    have hind' : IndepFun (fun ω => ∑ j ∈ Finset.range N, Y j ω) (Y N) Q := by
      have := hind.indepFun_sum_range_succ hm N
      convert this using 1
      ext ω; simp [Finset.sum_apply]
    have hcross : ∫ ω, (∑ j ∈ Finset.range N, Y j ω) * Y N ω ∂Q = 0 := by
      rw [hind'.integral_fun_mul_eq_mul_integral hS2.aestronglyMeasurable
        (hL2 N).aestronglyMeasurable, h0 N, mul_zero]
    have hexp : (fun ω => (∑ j ∈ Finset.range (N + 1), Y j ω) ^ 2) = fun ω =>
        (∑ j ∈ Finset.range N, Y j ω) ^ 2 + 2 * ((∑ j ∈ Finset.range N, Y j ω) * Y N ω) +
          Y N ω ^ 2 := by
      ext ω; rw [Finset.sum_range_succ]; ring
    have hi1 : Integrable (fun ω => (∑ j ∈ Finset.range N, Y j ω) ^ 2) Q := hS2.integrable_sq
    have hi2 : Integrable (fun ω => 2 * ((∑ j ∈ Finset.range N, Y j ω) * Y N ω)) Q :=
      (hS2.integrable_mul (hL2 N)).const_mul 2
    have hi3 : Integrable (fun ω => Y N ω ^ 2) Q := (hL2 N).integrable_sq
    have e1 := integral_add (hi1.add hi2) hi3
    have e2 := integral_add hi1 hi2
    have e3 : ∫ ω, 2 * ((∑ j ∈ Finset.range N, Y j ω) * Y N ω) ∂Q = 0 := by
      rw [integral_const_mul, hcross, mul_zero]
    simp only [Pi.add_apply] at e1 e2
    rw [hexp, e1, e2, e3, ih, Finset.sum_range_succ]
    ring

/-! ### Kolmogorov's inequality -/

/-- The partial sum over `range i` of a vector indexed by `range k`, for `i ≤ k`. -/
theorem lil_sum_coe_sort_ite_lt {Ω : Type*} (Y : ℕ → Ω → ℝ) {i k : ℕ} (hik : i ≤ k) (ω : Ω) :
    ∑ j : Finset.range k, (if (j : ℕ) < i then Y j ω else 0) = ∑ j ∈ Finset.range i, Y j ω := by
  rw [Finset.sum_coe_sort (Finset.range k) (fun j => if j < i then Y j ω else 0),
    ← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- **Kolmogorov's inequality** (MT Theorem D.6.3): for independent centred `Yⱼ ∈ L²` and
`t > 0`, `t² P(max_{k ≤ N} |Σ_{j<k} Yⱼ| ≥ t) ≤ Σ_{j<N} E[Yⱼ²]`. -/
theorem lil_kolmogorov_ineq {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {Y : ℕ → Ω → ℝ} (hind : iIndepFun Y Q) (hm : ∀ j, Measurable (Y j))
    (hL2 : ∀ j, MemLp (Y j) 2 Q) (h0 : ∀ j, ∫ ω, Y j ω ∂Q = 0) (N : ℕ) {t : ℝ} (ht : 0 < t) :
    t ^ 2 * Q.real {ω | ∃ k ≤ N, t ≤ |∑ j ∈ Finset.range k, Y j ω|} ≤
      ∑ j ∈ Finset.range N, ∫ ω, Y j ω ^ 2 ∂Q := by
  classical
  set S : ℕ → Ω → ℝ := fun k ω => ∑ j ∈ Finset.range k, Y j ω with hS
  have hSm : ∀ k, Measurable (S k) := fun k => Finset.measurable_sum _ fun j _ => hm j
  have hS2 : ∀ k, MemLp (S k) 2 Q := fun k => memLp_finsetSum _ fun j _ => hL2 j
  -- the first-passage events
  set A : ℕ → Set Ω := fun k => {ω | t ≤ |S k ω|} ∩ ⋂ i ∈ Finset.range k, {ω | |S i ω| < t}
    with hA
  have hAm : ∀ k, MeasurableSet (A k) := fun k =>
    (measurableSet_le measurable_const (continuous_abs.measurable.comp (hSm k))).inter
      (Finset.measurableSet_biInter _ fun i _ =>
        measurableSet_lt (continuous_abs.measurable.comp (hSm i)) measurable_const)
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (N + 1))) A := by
    intro k _ l _ hkl
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2
    rcases lt_or_gt_of_ne hkl with h | h
    · have h3 : |S k ω| < t := mem_iInter₂.1 h2.2 k (Finset.mem_range.2 h)
      have h4 : t ≤ |S k ω| := h1.1
      linarith
    · have h3 : |S l ω| < t := mem_iInter₂.1 h1.2 l (Finset.mem_range.2 h)
      have h4 : t ≤ |S l ω| := h2.1
      linarith
  have hE : {ω | ∃ k ≤ N, t ≤ |S k ω|} = ⋃ k ∈ Finset.range (N + 1), A k := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, Finset.mem_range, exists_prop]
    constructor
    · rintro ⟨k, hk, hkt⟩
      have hex : ∃ k, t ≤ |S k ω| := ⟨k, hkt⟩
      refine ⟨Nat.find hex, by have := Nat.find_min' hex hkt; omega, Nat.find_spec hex, ?_⟩
      refine mem_iInter₂.2 fun i hi => ?_
      have := Nat.find_min hex (Finset.mem_range.1 hi)
      exact not_le.1 this
    · rintro ⟨k, hk, h1, -⟩
      exact ⟨k, by omega, h1⟩
  -- on `A k`, `E[S_N² ; A k] ≥ E[S_k² ; A k] ≥ t² P(A k)`
  have hkey : ∀ k ≤ N, t ^ 2 * Q.real (A k) ≤ ∫ ω in A k, S N ω ^ 2 ∂Q := by
    intro k hk
    have hlow : t ^ 2 * Q.real (A k) ≤ ∫ ω in A k, S k ω ^ 2 ∂Q := by
      have hc : ∫ _ω in A k, t ^ 2 ∂Q = t ^ 2 * Q.real (A k) := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]
      rw [← hc]
      refine setIntegral_mono_on (integrable_const _).integrableOn
        (hS2 k).integrable_sq.integrableOn
        (hAm k) fun ω hω => ?_
      have h1 : t ≤ |S k ω| := hω.1
      have : t ^ 2 ≤ |S k ω| ^ 2 := pow_le_pow_left₀ ht.le h1 2
      rwa [sq_abs] at this
    -- the remainder `R = S_N − S_k` is independent of `1_{A k} S_k`
    set R : Ω → ℝ := fun ω => ∑ j ∈ Finset.Ico k N, Y j ω with hR
    have hR2 : MemLp R 2 Q := memLp_finsetSum _ fun j _ => hL2 j
    have hR0 : ∫ ω, R ω ∂Q = 0 := by
      rw [hR, integral_finsetSum _ fun j _ => (hL2 j).integrable one_le_two]
      exact Finset.sum_eq_zero fun j _ => h0 j
    have hSN : ∀ ω, S N ω = S k ω + R ω := fun ω => by
      simp only [hS, hR]
      rw [Finset.sum_range_add_sum_Ico _ hk]
    set U : Ω → ℝ := (A k).indicator (S k) with hU
    have hU2 : MemLp U 2 Q := (hS2 k).indicator (hAm k)
    have hind' : IndepFun U R Q := by
      have hV := hind.indepFun_finset (Finset.range k) (Finset.Ico k N)
        (by rw [Finset.disjoint_left]; intro j hj1 hj2
            simp only [Finset.mem_range, Finset.mem_Ico] at hj1 hj2; omega) hm
      set F : (Finset.range k → ℝ) → ℝ := fun v =>
        ({v | t ≤ |∑ j : Finset.range k, v j|} ∩ ⋂ i ∈ Finset.range k,
          {v | |∑ j : Finset.range k, (if (j : ℕ) < i then v j else 0)| < t}).indicator
          (fun v => ∑ j : Finset.range k, v j) v with hF
      have hFm : Measurable F := by
        refine Measurable.indicator (Finset.measurable_sum _ fun j _ => measurable_pi_apply j)
          ((measurableSet_le measurable_const (continuous_abs.measurable.comp
            (Finset.measurable_sum _ fun j _ => measurable_pi_apply j))).inter
          (Finset.measurableSet_biInter _ fun i _ => measurableSet_lt
            (continuous_abs.measurable.comp
            (Finset.measurable_sum _ fun j _ => by
              by_cases hj : (j : ℕ) < i
              · simp only [hj, ite_true]; exact measurable_pi_apply j
              · simp only [hj, ite_false]; exact measurable_const)) measurable_const))
      have hGm : Measurable fun w : Finset.Ico k N → ℝ => ∑ j : Finset.Ico k N, w j :=
        Finset.measurable_sum _ fun j _ => measurable_pi_apply j
      have hc := hV.comp hFm hGm
      convert hc using 1
      · ext ω
        simp only [hU, hF, Function.comp_apply]
        have hsk : ∑ j : Finset.range k, Y j ω = S k ω := by
          rw [Finset.sum_coe_sort (Finset.range k) (fun j => Y j ω)]
        have hsi : ∀ i ∈ Finset.range k,
            ∑ j : Finset.range k, (if (j : ℕ) < i then Y j ω else 0) = S i ω := fun i hi =>
          lil_sum_coe_sort_ite_lt Y (Finset.mem_range.1 hi).le ω
        by_cases hω : ω ∈ A k
        · rw [indicator_of_mem hω, indicator_of_mem]
          · exact hsk.symm
          · refine ⟨by simp only [mem_ofPred_eq, hsk]; exact hω.1, mem_iInter₂.2 fun i hi => ?_⟩
            simp only [mem_ofPred_eq, hsi i hi]
            exact mem_iInter₂.1 hω.2 i hi
        · rw [indicator_of_notMem hω, indicator_of_notMem]
          rintro ⟨h1, h2⟩
          refine hω ⟨by simp only [mem_ofPred_eq, ← hsk]; exact h1, mem_iInter₂.2 fun i hi => ?_⟩
          have := mem_iInter₂.1 h2 i hi
          simp only [mem_ofPred_eq, hsi i hi] at this
          exact this
      · ext ω
        simp only [hR, Function.comp_apply]
        rw [Finset.sum_coe_sort (Finset.Ico k N) (fun j => Y j ω)]
    have hcross : ∫ ω, U ω * R ω ∂Q = 0 := by
      rw [hind'.integral_fun_mul_eq_mul_integral hU2.aestronglyMeasurable
        hR2.aestronglyMeasurable, hR0, mul_zero]
    have hup : ∫ ω in A k, S k ω ^ 2 ∂Q ≤ ∫ ω in A k, S N ω ^ 2 ∂Q := by
      rw [← integral_indicator (hAm k), ← integral_indicator (hAm k)]
      have hdec : (A k).indicator (fun ω => S N ω ^ 2) = fun ω =>
          (A k).indicator (fun ω => S k ω ^ 2) ω + 2 * (U ω * R ω) +
            (A k).indicator (fun ω => R ω ^ 2) ω := by
        ext ω
        by_cases hω : ω ∈ A k
        · simp only [indicator_of_mem hω, hU, hSN]; ring
        · simp only [indicator_of_notMem hω, hU]; ring
      have hi1 : Integrable ((A k).indicator fun ω => S k ω ^ 2) Q :=
        (hS2 k).integrable_sq.indicator (hAm k)
      have hi2 : Integrable (fun ω => 2 * (U ω * R ω)) Q :=
        (hU2.integrable_mul hR2).const_mul 2
      have hi3 : Integrable ((A k).indicator fun ω => R ω ^ 2) Q :=
        hR2.integrable_sq.indicator (hAm k)
      have e1 := integral_add (hi1.add hi2) hi3
      have e2 := integral_add hi1 hi2
      have e3 : ∫ ω, 2 * (U ω * R ω) ∂Q = 0 := by rw [integral_const_mul, hcross, mul_zero]
      simp only [Pi.add_apply] at e1 e2
      rw [hdec, e1, e2, e3]
      have : 0 ≤ ∫ ω, (A k).indicator (fun ω => R ω ^ 2) ω ∂Q :=
        integral_nonneg fun ω => indicator_nonneg (fun ω _ => sq_nonneg _) ω
      linarith
    exact hlow.trans hup
  -- sum over `k`
  have hsum : t ^ 2 * Q.real {ω | ∃ k ≤ N, t ≤ |S k ω|} ≤ ∫ ω, S N ω ^ 2 ∂Q := by
    rw [hE, measureReal_biUnion_finset hdisj fun k _ => hAm k, Finset.mul_sum]
    calc ∑ k ∈ Finset.range (N + 1), t ^ 2 * Q.real (A k)
        ≤ ∑ k ∈ Finset.range (N + 1), ∫ ω in A k, S N ω ^ 2 ∂Q :=
          Finset.sum_le_sum fun k hk => hkey k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
      _ = ∫ ω in ⋃ k ∈ Finset.range (N + 1), A k, S N ω ^ 2 ∂Q :=
          (integral_biUnion_finset _ (fun k _ => hAm k) hdisj
            fun k _ => (hS2 N).integrable_sq.integrableOn).symm
      _ ≤ ∫ ω, S N ω ^ 2 ∂Q :=
          setIntegral_le_integral (hS2 N).integrable_sq
            (Eventually.of_forall fun ω => sq_nonneg _)
  calc t ^ 2 * Q.real {ω | ∃ k ≤ N, t ≤ |∑ j ∈ Finset.range k, Y j ω|}
      = t ^ 2 * Q.real {ω | ∃ k ≤ N, t ≤ |S k ω|} := rfl
    _ ≤ ∫ ω, S N ω ^ 2 ∂Q := hsum
    _ = ∑ j ∈ Finset.range N, ∫ ω, Y j ω ^ 2 ∂Q := lil_integral_sq_sum_range hind hm hL2 h0 N

/-- Kolmogorov's inequality for the sums `Σ_{j<k} Y_{a+j}` started at index `a`. -/
theorem lil_kolmogorov_ineq_shift {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {Y : ℕ → Ω → ℝ} (hind : iIndepFun Y Q) (hm : ∀ j, Measurable (Y j))
    (hL2 : ∀ j, MemLp (Y j) 2 Q) (h0 : ∀ j, ∫ ω, Y j ω ∂Q = 0) (a N : ℕ) {t : ℝ} (ht : 0 < t) :
    t ^ 2 * Q.real {ω | ∃ k ≤ N, t ≤ |∑ j ∈ Finset.range k, Y (a + j) ω|} ≤
      ∑ j ∈ Finset.range N, ∫ ω, Y (a + j) ω ^ 2 ∂Q :=
  lil_kolmogorov_ineq (Y := fun j => Y (a + j))
    (hind.precomp (g := fun j => a + j) fun i j h => by simpa using h)
    (fun j => hm _) (fun j => hL2 _) (fun j => h0 _) N ht

/-! ### The random-index step -/

/-- Two indices within `W` of each other lie in the window `[N − W, N − W + 2W]`, and the
difference of the partial sums up to them is a difference of sums inside the window. -/
theorem lil_sum_range_sub_eq_window (y : ℕ → ℝ) {K N W : ℕ} (h1 : K ≤ N + W) (h2 : N ≤ K + W) :
    N - W ≤ K ∧ K - (N - W) ≤ 2 * W ∧ N - (N - W) ≤ 2 * W ∧
      ∑ j ∈ Finset.range K, y j - ∑ j ∈ Finset.range N, y j =
        ∑ j ∈ Finset.range (K - (N - W)), y (N - W + j) -
          ∑ j ∈ Finset.range (N - (N - W)), y (N - W + j) := by
  set a := N - W with ha
  have hK : a ≤ K := by omega
  have hN : a ≤ N := by omega
  refine ⟨hK, by omega, by omega, ?_⟩
  have eK : ∑ j ∈ Finset.range K, y j =
      ∑ j ∈ Finset.range a, y j + ∑ j ∈ Finset.range (K - a), y (a + j) := by
    rw [← Finset.sum_range_add, Nat.add_sub_cancel' hK]
  have eN : ∑ j ∈ Finset.range N, y j =
      ∑ j ∈ Finset.range a, y j + ∑ j ∈ Finset.range (N - a), y (a + j) := by
    rw [← Finset.sum_range_add, Nat.add_sub_cancel' hN]
  rw [eK, eN]; ring

/-- **The random-index step** (MT p. 431, (17.19)–(17.20)): for i.i.d. centred `Yⱼ ∈ L²` and
random indices `Kₙ` with `Kₙ/n → c > 0` almost surely, `(S_{Kₙ} − S_{⌊cn⌋})/√n → 0` in
probability. The proof is the book's, through Kolmogorov's inequality on a window around
`⌊cn⌋`. -/
theorem lil_tendstoInMeasure_anscombe {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {Y : ℕ → Ω → ℝ} (hind : iIndepFun Y Q) (hm : ∀ j, Measurable (Y j))
    (hident : ∀ j, IdentDistrib (Y j) (Y 0) Q Q) (hL2 : MemLp (Y 0) 2 Q)
    (h0 : ∫ ω, Y 0 ω ∂Q = 0) {K : ℕ → Ω → ℕ} (hKm : ∀ n, Measurable (K n)) {c : ℝ}
    (hc : 0 < c) (hK : ∀ᵐ ω ∂Q, Tendsto (fun n => (K n ω : ℝ) / n) atTop (𝓝 c)) :
    TendstoInMeasure Q (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * (∑ j ∈ Finset.range (K n ω), Y j ω -
      ∑ j ∈ Finset.range ⌊c * n⌋₊, Y j ω)) atTop (fun _ => 0) := by
  have hL2j : ∀ j, MemLp (Y j) 2 Q := fun j => (hident j).memLp_iff.2 hL2
  have h0j : ∀ j, ∫ ω, Y j ω ∂Q = 0 := fun j => (hident j).integral_eq.trans h0
  set σ2 := ∫ ω, Y 0 ω ^ 2 ∂Q with hσ2
  have hσ2j : ∀ j, ∫ ω, Y j ω ^ 2 ∂Q = σ2 := fun j =>
    ((hident j).comp (measurable_id.pow_const 2)).integral_eq
  have hσ0 : 0 ≤ σ2 := integral_nonneg fun ω => sq_nonneg _
  -- `Kₙ/n → c` in probability
  have hKp : TendstoInMeasure Q (fun n ω => (K n ω : ℝ) / n) atTop (fun _ => c) :=
    tendstoInMeasure_of_tendsto_ae (fun (n : ℕ) =>
      (((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp (hKm n)).div_const
        (n : ℝ)).aestronglyMeasurable) hK
  rw [tendstoInMeasure_iff_dist] at hKp ⊢
  intro ε hε
  -- it suffices to bound the real probabilities
  suffices hreal : Tendsto (fun n : ℕ => Q.real {ω | ε ≤ dist ((√(n : ℝ))⁻¹ *
      (∑ j ∈ Finset.range (K n ω), Y j ω - ∑ j ∈ Finset.range ⌊c * n⌋₊, Y j ω)) 0}) atTop
      (𝓝 0) by
    have := (ENNReal.tendsto_ofReal hreal)
    rw [ENNReal.ofReal_zero] at this
    exact this.congr fun n => ofReal_measureReal
  rw [Metric.tendsto_atTop]
  intro η hη
  -- choose the window size `δ`
  set δ : ℝ := min 1 (η * ε ^ 2 / (48 * (σ2 + 1))) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hδle : 16 * δ * σ2 / ε ^ 2 ≤ η / 3 := by
    have h1 : δ ≤ η * ε ^ 2 / (48 * (σ2 + 1)) := min_le_right _ _
    have h2 : 16 * δ * σ2 ≤ 16 * (η * ε ^ 2 / (48 * (σ2 + 1))) * (σ2 + 1) := by
      have : 16 * δ * σ2 ≤ 16 * δ * (σ2 + 1) := by nlinarith
      nlinarith
    rw [div_le_iff₀ (by positivity)]
    calc 16 * δ * σ2 ≤ 16 * (η * ε ^ 2 / (48 * (σ2 + 1))) * (σ2 + 1) := h2
      _ = η / 3 * ε ^ 2 := by field_simp; ring
  -- `P(|Kₙ/n − c| ≥ δ) → 0`
  have hB := hKp δ hδpos
  have hB' : Tendsto (fun n : ℕ => Q.real {ω | δ ≤ dist ((K n ω : ℝ) / n) c}) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hB
    rw [ENNReal.toReal_zero] at this
    exact this
  rw [Metric.tendsto_atTop] at hB'
  obtain ⟨n₁, hn₁⟩ := hB' (η / 3) (by positivity)
  obtain ⟨n₂, hn₂⟩ := exists_nat_gt (48 * σ2 / (η * ε ^ 2) + 2 / δ)
  refine ⟨max 1 (max n₁ n₂), fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_of_max_le_left hn
  have hnn₁ : n₁ ≤ n := le_of_max_le_left (le_of_max_le_right hn)
  have hnn₂ : n₂ ≤ n := le_of_max_le_right (le_of_max_le_right hn)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  -- the window
  set N := ⌊c * n⌋₊ with hN
  set W := ⌈δ * n⌉₊ + 1 with hW
  set a := N - W with ha
  set D : Ω → ℝ := fun ω => (√(n : ℝ))⁻¹ *
    (∑ j ∈ Finset.range (K n ω), Y j ω - ∑ j ∈ Finset.range N, Y j ω) with hD
  set B := {ω | δ ≤ dist ((K n ω : ℝ) / n) c} with hBdef
  set M := {ω | ∃ l ≤ 2 * W, ε * √(n : ℝ) / 2 ≤ |∑ j ∈ Finset.range l, Y (a + j) ω|} with hM
  have hsub : {ω | ε ≤ dist (D ω) 0} ⊆ B ∪ M := by
    intro ω hω
    by_cases hωB : ω ∈ B
    · exact Or.inl hωB
    right
    simp only [hBdef, mem_ofPred_eq, not_le, Real.dist_eq] at hωB
    -- `|Kₙ − N| ≤ W`
    have hKn : |(K n ω : ℝ) - c * n| < δ * n := by
      have : |(K n ω : ℝ) / n - c| * n < δ * n := mul_lt_mul_of_pos_right hωB hnpos
      rwa [← abs_of_pos hnpos, ← abs_mul, abs_of_pos hnpos, sub_mul,
        div_mul_cancel₀ _ hnpos.ne'] at this
    have hN1 : (N : ℝ) ≤ c * n := Nat.floor_le (by positivity)
    have hN2 : c * n < N + 1 := Nat.lt_floor_add_one _
    have hW1 : δ * n ≤ ⌈δ * n⌉₊ := Nat.le_ceil _
    rw [abs_lt] at hKn
    have hk1 : K n ω ≤ N + W := by
      have : (K n ω : ℝ) < N + W := by push_cast [hW]; linarith
      exact_mod_cast this.le
    have hk2 : N ≤ K n ω + W := by
      have : (N : ℝ) < K n ω + W := by push_cast [hW]; linarith
      exact_mod_cast this.le
    obtain ⟨-, hl1, hl2, heq⟩ := lil_sum_range_sub_eq_window (fun j => Y j ω) hk1 hk2
    -- one of the two window sums is large
    have hDω : ε ≤ |D ω| := by simpa [Real.dist_eq] using hω
    have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 hnpos
    have hbig : ε * √(n : ℝ) ≤ |∑ j ∈ Finset.range (K n ω), Y j ω -
        ∑ j ∈ Finset.range N, Y j ω| := by
      have : |D ω| = (√(n : ℝ))⁻¹ * |∑ j ∈ Finset.range (K n ω), Y j ω -
          ∑ j ∈ Finset.range N, Y j ω| := by
        rw [hD, abs_mul, abs_of_pos (inv_pos.2 hsq)]
      rw [this, inv_mul_eq_div, le_div_iff₀ hsq] at hDω
      exact hDω
    simp only [heq] at hbig
    by_contra hnot
    simp only [hM, mem_ofPred_eq, not_exists, not_and, not_le] at hnot
    have h1 := hnot _ hl1
    have h2 := hnot _ hl2
    have := abs_sub (∑ j ∈ Finset.range (K n ω - a), Y (a + j) ω)
      (∑ j ∈ Finset.range (N - a), Y (a + j) ω)
    linarith
  -- Kolmogorov on the window
  have hMbound : Q.real M ≤ 8 * δ * σ2 / ε ^ 2 + 16 * σ2 / (ε ^ 2 * n) := by
    have hk := lil_kolmogorov_ineq_shift hind hm hL2j h0j a (2 * W) (t := ε * √(n : ℝ) / 2)
      (by positivity)
    simp_rw [hσ2j, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hk
    have hsq : (ε * √(n : ℝ) / 2) ^ 2 = ε ^ 2 * n / 4 := by
      rw [div_pow, mul_pow, Real.sq_sqrt hnpos.le]; ring
    rw [hsq] at hk
    have hWle : ((2 * W : ℕ) : ℝ) ≤ 2 * (δ * n + 2) := by
      have : (⌈δ * n⌉₊ : ℝ) < δ * n + 1 := Nat.ceil_lt_add_one (by positivity)
      push_cast [hW]; linarith
    have hpos : 0 < ε ^ 2 * n / 4 := by positivity
    have hM' : Q.real M ≤ ((2 * W : ℕ) : ℝ) * σ2 / (ε ^ 2 * n / 4) := by
      rw [le_div_iff₀ hpos, mul_comm]; exact hk
    calc Q.real M ≤ ((2 * W : ℕ) : ℝ) * σ2 / (ε ^ 2 * n / 4) := hM'
      _ ≤ 2 * (δ * n + 2) * σ2 / (ε ^ 2 * n / 4) := by gcongr
      _ = 8 * δ * σ2 / ε ^ 2 + 16 * σ2 / (ε ^ 2 * n) := by field_simp; ring
  have htail : 16 * σ2 / (ε ^ 2 * n) ≤ η / 3 := by
    have h1 : 48 * σ2 / (η * ε ^ 2) < n := by
      have : (n₂ : ℝ) ≤ n := by exact_mod_cast hnn₂
      have h3 : 48 * σ2 / (η * ε ^ 2) + 2 / δ < n := hn₂.trans_le this
      have : 0 ≤ 2 / δ := by positivity
      linarith
    rw [div_lt_iff₀ (by positivity)] at h1
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h816 : 8 * δ * σ2 / ε ^ 2 ≤ 16 * δ * σ2 / ε ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [mul_nonneg hδpos.le hσ0]
  have hBn := hn₁ n hnn₁
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at hBn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  calc Q.real {ω | ε ≤ dist (D ω) 0} ≤ Q.real (B ∪ M) := measureReal_mono hsub
    _ ≤ Q.real B + Q.real M := measureReal_union_le _ _
    _ < η / 3 + (η / 3 + η / 3) := by linarith
    _ = η := by ring

end RQMCMarkov.MarkovDriving

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exponential inequalities and block independence for the LIL

Copied from the `StochasticStability/LimitTheorems` project (module `LimitTheorems.LILExponential`),
with the namespace renamed `MeynTweedie.LimitTheorems` → `RQMCMarkov.MarkovDriving` and the
generic lemma names prefixed `lil_` to avoid clashes; used by `MCRate` for the MC baseline.

Probabilistic tools for the upper half of the Hartman–Wintner LIL (`LILUpper`) and the blocking
arguments of the lower half (`LILLower`) and of MT (17.36), p. 442.

* `lil_exp_le_one_add_add_sq`: `eˣ ≤ 1 + x + x²(1 + |x|)/2` for `|x| ≤ 1`.
* `lil_integral_exp_le_of_abs_le`: Kolmogorov's upper exponential bound
  `E[e^{λY}] ≤ exp(λ² E[Y²](1 + λc)/2)` for `|Y| ≤ c`, `E[Y] = 0`, `0 ≤ λ`, `λc ≤ 1`;
  `lil_integral_exp_sum_le`: the same for sums of independent variables.
* **The exponential maximal inequality** (`lil_exp_maximal_ineq`):
  `e^{λt} P(max_{k ≤ N} Sₖ ≥ t) ≤ E[e^{λ S_N}]` for independent centred bounded summands (the
  first-passage argument of Kolmogorov's inequality, MT Theorem D.6.3, applied to `e^{λSₖ}`).
* `lil_iIndep_iSup_blocks`: independent σ-algebras grouped along pairwise disjoint index sets are
  independent.
* `lil_identDistrib_shift`, `lil_identDistrib_shift_sum`: shifts of an i.i.d. sequence, and their
  partial sums, have the law of the sequence.
-/

namespace RQMCMarkov.MarkovDriving

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

/-! ### An exponential bound -/

/-- `eˣ ≤ 1 + x + x²(1 + |x|)/2` for `|x| ≤ 1`. -/
theorem lil_exp_le_one_add_add_sq {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 * (1 + |x|) / 2 := by
  have h := Real.exp_bound hx (n := 3) (by norm_num)
  have e : ∑ m ∈ Finset.range 3, x ^ m / (m.factorial : ℝ) = 1 + x + x ^ 2 / 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    push_cast
    ring
  rw [e] at h
  have h2 : |x| ^ 3 * ((Nat.succ 3 : ℕ) / ((Nat.factorial 3 : ℕ) * (3 : ℕ)) : ℝ) =
      |x| ^ 3 * (2 / 9) := by
    norm_num [Nat.factorial]
  rw [h2] at h
  have h3 : |x| ^ 3 = x ^ 2 * |x| := by
    rw [pow_succ, ← sq_abs x]
  have h4 := (abs_le.1 h).2
  have h5 : 0 ≤ x ^ 2 * |x| := by positivity
  nlinarith

/-- **The moment generating function of a bounded centred variable**: if `|Y| ≤ c`,
`E[Y] = 0`, `λ ≥ 0` and `λc ≤ 1`, then `E[e^{λY}] ≤ exp(λ² E[Y²] (1 + λc)/2)`. -/
theorem lil_integral_exp_le_of_abs_le {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {Y : Ω → ℝ} (hm : Measurable Y) {c l : ℝ}
    (hb : ∀ ω, |Y ω| ≤ c) (h0 : ∫ ω, Y ω ∂Q = 0) (hl : 0 ≤ l) (hlc : l * c ≤ 1) :
    ∫ ω, Real.exp (l * Y ω) ∂Q ≤
      Real.exp (l ^ 2 * (∫ ω, Y ω ^ 2 ∂Q) * (1 + l * c) / 2) := by
  have hYi : Integrable Y Q :=
    Integrable.of_bound hm.aestronglyMeasurable c (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hb ω)
  have hY2i : Integrable (fun ω => Y ω ^ 2) Q :=
    Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable (c ^ 2)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hb ω) 2)
  have hpt : ∀ ω, Real.exp (l * Y ω) ≤
      1 + l * Y ω + (l ^ 2 * (1 + l * c) / 2) * Y ω ^ 2 := fun ω => by
    have habs : |l * Y ω| ≤ l * c := by
      rw [abs_mul, abs_of_nonneg hl]; exact mul_le_mul_of_nonneg_left (hb ω) hl
    have h1 := lil_exp_le_one_add_add_sq (habs.trans hlc)
    have h2 : (l * Y ω) ^ 2 * (1 + |l * Y ω|) / 2 ≤ (l * Y ω) ^ 2 * (1 + l * c) / 2 := by
      have := sq_nonneg (l * Y ω)
      nlinarith
    nlinarith
  have hrhs : Integrable (fun ω => 1 + l * Y ω + (l ^ 2 * (1 + l * c) / 2) * Y ω ^ 2) Q :=
    ((integrable_const 1).add (hYi.const_mul l)).add (hY2i.const_mul _)
  have hexpi : Integrable (fun ω => Real.exp (l * Y ω)) Q := by
    refine Integrable.of_bound (Real.continuous_exp.measurable.comp
      (hm.const_mul l)).aestronglyMeasurable (Real.exp (l * c))
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.2
    have := (abs_le.1 (hb ω)).2
    exact mul_le_mul_of_nonneg_left this hl
  have h1 := integral_mono hexpi hrhs hpt
  set K := l ^ 2 * (1 + l * c) / 2 with hK
  have hA : Integrable (fun ω => 1 + l * Y ω) Q := (integrable_const 1).add (hYi.const_mul l)
  have hB : Integrable (fun ω => K * Y ω ^ 2) Q := hY2i.const_mul K
  have hI : ∫ ω, (1 + l * Y ω + K * Y ω ^ 2) ∂Q = 1 + K * ∫ ω, Y ω ^ 2 ∂Q := by
    rw [integral_add hA hB, integral_add (integrable_const 1) (hYi.const_mul l),
      integral_const_mul, integral_const_mul, h0]
    simp
  rw [hI] at h1
  refine h1.trans ?_
  have := Real.add_one_le_exp (l ^ 2 * (∫ ω, Y ω ^ 2 ∂Q) * (1 + l * c) / 2)
  have e : K * ∫ ω, Y ω ^ 2 ∂Q = l ^ 2 * (∫ ω, Y ω ^ 2 ∂Q) * (1 + l * c) / 2 := by
    rw [hK]; ring
  linarith

/-! ### The exponential maximal inequality -/

/-- A sum of variables with `|Yⱼ| ≤ cⱼ` is bounded by `Σ cⱼ`. -/
theorem lil_abs_sum_le_of_abs_le {Ω : Type*} {Y : ℕ → Ω → ℝ} {c : ℕ → ℝ}
    (hb : ∀ j ω, |Y j ω| ≤ c j) (s : Finset ℕ) (ω : Ω) :
    |∑ j ∈ s, Y j ω| ≤ ∑ j ∈ s, c j :=
  (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hb j ω)

/-- **The exponential maximal inequality**: for independent centred bounded `Yⱼ`, `λ ≥ 0` and
any `t`, `e^{λt} P(max_{k ≤ N} Σ_{j<k} Yⱼ ≥ t) ≤ E[exp(λ Σ_{j<N} Yⱼ)]` (Doob's inequality for
the submartingale `exp(λ Sₖ)`, proved through the first-passage decomposition). -/
theorem lil_exp_maximal_ineq {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q]
    {Y : ℕ → Ω → ℝ} (hind : iIndepFun Y Q) (hm : ∀ j, Measurable (Y j)) {c : ℕ → ℝ}
    (hb : ∀ j ω, |Y j ω| ≤ c j) (h0 : ∀ j, ∫ ω, Y j ω ∂Q = 0) (N : ℕ) {l t : ℝ}
    (hl : 0 ≤ l) :
    Real.exp (l * t) * Q.real {ω | ∃ k ≤ N, t ≤ ∑ j ∈ Finset.range k, Y j ω} ≤
      ∫ ω, Real.exp (l * ∑ j ∈ Finset.range N, Y j ω) ∂Q := by
  classical
  set S : ℕ → Ω → ℝ := fun k ω => ∑ j ∈ Finset.range k, Y j ω with hS
  have hSm : ∀ k, Measurable (S k) := fun k => Finset.measurable_sum _ fun j _ => hm j
  -- bounded variables are integrable
  have hbd : ∀ (s : Finset ℕ), Integrable (fun ω => Real.exp (l * ∑ j ∈ s, Y j ω)) Q := by
    intro s
    refine Integrable.of_bound (Real.continuous_exp.measurable.comp
      ((Finset.measurable_sum _ fun j _ => hm j).const_mul l)).aestronglyMeasurable
      (Real.exp (l * ∑ j ∈ s, c j)) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.2
    exact mul_le_mul_of_nonneg_left ((abs_le.1 (lil_abs_sum_le_of_abs_le hb s ω)).2) hl
  have hYi : ∀ j, Integrable (Y j) Q := fun j =>
    Integrable.of_bound (hm j).aestronglyMeasurable (c j) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hb j ω)
  -- the first-passage events
  set A : ℕ → Set Ω := fun k => {ω | t ≤ S k ω} ∩ ⋂ i ∈ Finset.range k, {ω | S i ω < t}
    with hA
  have hAm : ∀ k, MeasurableSet (A k) := fun k =>
    (measurableSet_le measurable_const (hSm k)).inter
      (Finset.measurableSet_biInter _ fun i _ => measurableSet_lt (hSm i) measurable_const)
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (N + 1))) A := by
    intro k _ l' _ hkl
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2
    rcases lt_or_gt_of_ne hkl with h | h
    · have h3 : S k ω < t := mem_iInter₂.1 h2.2 k (Finset.mem_range.2 h)
      have h4 : t ≤ S k ω := h1.1
      linarith
    · have h3 : S l' ω < t := mem_iInter₂.1 h1.2 l' (Finset.mem_range.2 h)
      have h4 : t ≤ S l' ω := h2.1
      linarith
  have hE : {ω | ∃ k ≤ N, t ≤ S k ω} = ⋃ k ∈ Finset.range (N + 1), A k := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, Finset.mem_range, exists_prop]
    constructor
    · rintro ⟨k, hk, hkt⟩
      have hex : ∃ k, t ≤ S k ω := ⟨k, hkt⟩
      refine ⟨Nat.find hex, by have := Nat.find_min' hex hkt; omega, Nat.find_spec hex, ?_⟩
      refine mem_iInter₂.2 fun i hi => ?_
      have := Nat.find_min hex (Finset.mem_range.1 hi)
      exact not_le.1 this
    · rintro ⟨k, hk, h1, -⟩
      exact ⟨k, by omega, h1⟩
  -- on `A k`, `E[e^{λ S_N} ; A k] ≥ E[e^{λ S_k} ; A k] ≥ e^{λ t} P(A k)`
  have hkey : ∀ k ≤ N, Real.exp (l * t) * Q.real (A k) ≤
      ∫ ω in A k, Real.exp (l * S N ω) ∂Q := by
    intro k hk
    set R : Ω → ℝ := fun ω => ∑ j ∈ Finset.Ico k N, Y j ω with hR
    have hSN : ∀ ω, S N ω = S k ω + R ω := fun ω => by
      simp only [hS, hR]
      rw [Finset.sum_range_add_sum_Ico _ hk]
    set U : Ω → ℝ := (A k).indicator (fun ω => Real.exp (l * S k ω)) with hU
    set V : Ω → ℝ := fun ω => Real.exp (l * R ω) with hV
    have hUi : Integrable U Q := (hbd (Finset.range k)).indicator (hAm k)
    have hVi : Integrable V Q := hbd (Finset.Ico k N)
    have hind' : IndepFun U V Q := by
      have hW := hind.indepFun_finset (Finset.range k) (Finset.Ico k N)
        (by rw [Finset.disjoint_left]; intro j hj1 hj2
            simp only [Finset.mem_range, Finset.mem_Ico] at hj1 hj2; omega) hm
      set F : (Finset.range k → ℝ) → ℝ := fun v =>
        ({v | t ≤ ∑ j : Finset.range k, v j} ∩ ⋂ i ∈ Finset.range k,
          {v | ∑ j : Finset.range k, (if (j : ℕ) < i then v j else 0) < t}).indicator
          (fun v => Real.exp (l * ∑ j : Finset.range k, v j)) v with hF
      have hFm : Measurable F := by
        refine Measurable.indicator (Real.continuous_exp.measurable.comp
          ((Finset.measurable_sum _ fun j _ => measurable_pi_apply j).const_mul l))
          ((measurableSet_le measurable_const
            (Finset.measurable_sum _ fun j _ => measurable_pi_apply j)).inter
          (Finset.measurableSet_biInter _ fun i _ => measurableSet_lt
            (Finset.measurable_sum _ fun j _ => by
              by_cases hj : (j : ℕ) < i
              · simp only [hj, ite_true]; exact measurable_pi_apply j
              · simp only [hj, ite_false]; exact measurable_const) measurable_const))
      have hGm : Measurable fun w : Finset.Ico k N → ℝ =>
          Real.exp (l * ∑ j : Finset.Ico k N, w j) :=
        Real.continuous_exp.measurable.comp
          ((Finset.measurable_sum _ fun j _ => measurable_pi_apply j).const_mul l)
      have hc := hW.comp hFm hGm
      convert hc using 1
      · ext ω
        simp only [hU, hF, Function.comp_apply]
        have hsk : ∑ j : Finset.range k, Y j ω = S k ω := by
          rw [Finset.sum_coe_sort (Finset.range k) (fun j => Y j ω)]
        have hsi : ∀ i ∈ Finset.range k,
            ∑ j : Finset.range k, (if (j : ℕ) < i then Y j ω else 0) = S i ω := fun i hi =>
          lil_sum_coe_sort_ite_lt Y (Finset.mem_range.1 hi).le ω
        by_cases hω : ω ∈ A k
        · rw [indicator_of_mem hω, indicator_of_mem]
          · rw [hsk]
          · refine ⟨by simp only [mem_ofPred_eq, hsk]; exact hω.1, mem_iInter₂.2 fun i hi => ?_⟩
            simp only [mem_ofPred_eq, hsi i hi]
            exact mem_iInter₂.1 hω.2 i hi
        · rw [indicator_of_notMem hω, indicator_of_notMem]
          rintro ⟨h1, h2⟩
          refine hω ⟨by simp only [mem_ofPred_eq, ← hsk]; exact h1, mem_iInter₂.2 fun i hi => ?_⟩
          have := mem_iInter₂.1 h2 i hi
          simp only [mem_ofPred_eq, hsi i hi] at this
          exact this
      · ext ω
        simp only [hV, hR, Function.comp_apply]
        rw [Finset.sum_coe_sort (Finset.Ico k N) (fun j => Y j ω)]
    -- `E[e^{λR}] ≥ 1`
    have hV1 : 1 ≤ ∫ ω, V ω ∂Q := by
      have hRi : Integrable R Q := integrable_finsetSum _ fun j _ => hYi j
      have hR0 : ∫ ω, R ω ∂Q = 0 := by
        rw [hR, integral_finsetSum _ fun j _ => hYi j]
        exact Finset.sum_eq_zero fun j _ => h0 j
      have h1 : ∫ ω, (1 + l * R ω) ∂Q ≤ ∫ ω, V ω ∂Q :=
        integral_mono ((integrable_const 1).add (hRi.const_mul l)) hVi fun ω => by
          have := Real.add_one_le_exp (l * R ω)
          simp only [hV]; linarith
      rw [integral_add (integrable_const 1) (hRi.const_mul l), integral_const_mul, hR0] at h1
      simpa using h1
    have hU0 : 0 ≤ ∫ ω, U ω ∂Q :=
      integral_nonneg fun ω => indicator_nonneg (fun ω _ => (Real.exp_pos _).le) ω
    have hlow : Real.exp (l * t) * Q.real (A k) ≤ ∫ ω, U ω ∂Q := by
      rw [hU, integral_indicator (hAm k)]
      have hc : ∫ _ω in A k, Real.exp (l * t) ∂Q = Real.exp (l * t) * Q.real (A k) := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]
      rw [← hc]
      refine setIntegral_mono_on (integrable_const _).integrableOn
        (hbd (Finset.range k)).integrableOn (hAm k) fun ω hω => ?_
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hω.1 hl)
    have hprod : ∫ ω in A k, Real.exp (l * S N ω) ∂Q = (∫ ω, U ω ∂Q) * ∫ ω, V ω ∂Q := by
      rw [← hind'.integral_fun_mul_eq_mul_integral hUi.aestronglyMeasurable
        hVi.aestronglyMeasurable, ← integral_indicator (hAm k)]
      congr 1
      ext ω
      by_cases hω : ω ∈ A k
      · simp only [indicator_of_mem hω, hU, hV, hSN, mul_add, Real.exp_add]
      · simp only [indicator_of_notMem hω, hU, zero_mul]
    rw [hprod]
    nlinarith
  -- sum over `k`
  calc Real.exp (l * t) * Q.real {ω | ∃ k ≤ N, t ≤ ∑ j ∈ Finset.range k, Y j ω}
      = Real.exp (l * t) * Q.real {ω | ∃ k ≤ N, t ≤ S k ω} := rfl
    _ = ∑ k ∈ Finset.range (N + 1), Real.exp (l * t) * Q.real (A k) := by
        rw [hE, measureReal_biUnion_finset hdisj fun k _ => hAm k, Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.range (N + 1), ∫ ω in A k, Real.exp (l * S N ω) ∂Q :=
        Finset.sum_le_sum fun k hk => hkey k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
    _ = ∫ ω in ⋃ k ∈ Finset.range (N + 1), A k, Real.exp (l * S N ω) ∂Q :=
        (integral_biUnion_finset _ (fun k _ => hAm k) hdisj
          fun k _ => (hbd (Finset.range N)).integrableOn).symm
    _ ≤ ∫ ω, Real.exp (l * S N ω) ∂Q :=
        setIntegral_le_integral (hbd (Finset.range N))
          (Eventually.of_forall fun ω => (Real.exp_pos _).le)

/-- The moment generating function of a sum of independent centred bounded variables:
if `|Yⱼ| ≤ C` and `E[Yⱼ²] ≤ s²` for `j < N`, `λ ≥ 0` and `λC ≤ 1`, then
`E[exp(λ Σ_{j<N} Yⱼ)] ≤ exp(N λ² s² (1 + λC)/2)`. -/
theorem lil_integral_exp_sum_le {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {Y : ℕ → Ω → ℝ} (hind : iIndepFun Y Q) (hm : ∀ j, Measurable (Y j))
    {c : ℕ → ℝ} (hb : ∀ j ω, |Y j ω| ≤ c j) (h0 : ∀ j, ∫ ω, Y j ω ∂Q = 0) (N : ℕ)
    {l C s2 : ℝ} (hl : 0 ≤ l) (hcC : ∀ j < N, c j ≤ C) (hlC : l * C ≤ 1)
    (hs2 : ∀ j < N, ∫ ω, Y j ω ^ 2 ∂Q ≤ s2) :
    ∫ ω, Real.exp (l * ∑ j ∈ Finset.range N, Y j ω) ∂Q ≤
      Real.exp (N * (l ^ 2 * s2 * (1 + l * C) / 2)) := by
  have h := hind.mgf_sum hm (Finset.range N) (t := l)
  unfold mgf at h
  have e : (fun ω => Real.exp (l * (∑ i ∈ Finset.range N, Y i) ω)) =
      fun ω => Real.exp (l * ∑ j ∈ Finset.range N, Y j ω) := by
    ext ω; rw [Finset.sum_apply]
  rw [e] at h
  rw [h]
  obtain ⟨ω₀, -⟩ := nonempty_of_measure_ne_zero (μ := Q) (s := univ)
    (by rw [measure_univ]; exact one_ne_zero)
  have hC0 : ∀ j < N, 0 ≤ c j := fun j _ => (abs_nonneg _).trans (hb j ω₀)
  calc ∏ j ∈ Finset.range N, ∫ ω, Real.exp (l * Y j ω) ∂Q
      ≤ ∏ _j ∈ Finset.range N, Real.exp (l ^ 2 * s2 * (1 + l * C) / 2) := by
        refine Finset.prod_le_prod₀ (fun j _ => integral_nonneg fun ω => (Real.exp_pos _).le)
          fun j hj => ?_
        have hjN := Finset.mem_range.1 hj
        have hlc : l * c j ≤ 1 := (mul_le_mul_of_nonneg_left (hcC j hjN) hl).trans hlC
        refine (lil_integral_exp_le_of_abs_le (hm j) (hb j) (h0 j) hl hlc).trans ?_
        apply Real.exp_le_exp.2
        have h1 : 1 + l * c j ≤ 1 + l * C := by
          have := mul_le_mul_of_nonneg_left (hcC j hjN) hl; linarith
        have h2 : 0 ≤ ∫ ω, Y j ω ^ 2 ∂Q := integral_nonneg fun ω => sq_nonneg _
        have h3 : 0 ≤ 1 + l * c j := by have := mul_nonneg hl (hC0 j hjN); linarith
        have h4 := hs2 j hjN
        have h5 : 0 ≤ l ^ 2 := sq_nonneg l
        have h6 : (∫ ω, Y j ω ^ 2 ∂Q) * (1 + l * c j) ≤ s2 * (1 + l * C) :=
          mul_le_mul h4 h1 h3 (h2.trans h4)
        have := mul_le_mul_of_nonneg_left h6 h5
        nlinarith
    _ = Real.exp (N * (l ^ 2 * s2 * (1 + l * C) / 2)) := by
        rw [Finset.prod_const, Finset.card_range, ← Real.exp_nat_mul]

/-! ### Independence of blocks and shifts of i.i.d. sequences -/

/-- Independent σ-algebras grouped along pairwise disjoint index sets give independent
σ-algebras: `(⨆_{i ∈ I k} mᵢ)ₖ` is independent when `(mᵢ)` is and the `I k` are disjoint. -/
theorem lil_iIndep_iSup_blocks {Ω ι κ : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω}
    {m : ι → MeasurableSpace Ω} (h_le : ∀ i, m i ≤ mΩ) (hind : iIndep m Q) {I : κ → Set ι}
    (hI : Pairwise (Function.onFun Disjoint I)) :
    iIndep (fun k => ⨆ i ∈ I k, m i) Q := by
  classical
  have := hind.isProbabilityMeasure
  rw [iIndep_iff]
  intro s
  induction s using Finset.induction_on with
  | empty => intro f _; simp
  | insert a s has ih =>
    intro f hf
    rw [Finset.set_biInter_insert, Finset.prod_insert has]
    have hT : Disjoint (I a) (⋃ k ∈ s, I k) := by
      rw [Set.disjoint_iUnion₂_right]
      intro k hk
      exact hI (fun h => has (h ▸ hk))
    have hindT := indep_iSup_of_disjoint h_le hind hT
    have hle : ∀ k ∈ s, (⨆ i ∈ I k, m i) ≤ ⨆ i ∈ ⋃ k ∈ s, I k, m i := fun k hk =>
      iSup₂_le fun i hi => le_iSup₂ (f := fun i (_ : i ∈ ⋃ k ∈ s, I k) => m i) i
        (mem_iUnion₂.2 ⟨k, hk, hi⟩)
    have hmeas : MeasurableSet[⨆ i ∈ ⋃ k ∈ s, I k, m i] (⋂ k ∈ s, f k) :=
      Finset.measurableSet_biInter (m := ⨆ i ∈ ⋃ k ∈ s, I k, m i) s fun k hk =>
        hle k hk _ (hf k (Finset.mem_insert_of_mem hk))
    rw [(Indep_iff _ _ Q).1 hindT _ _ (hf a (Finset.mem_insert_self a s)) hmeas,
      ih fun k hk => hf k (Finset.mem_insert_of_mem hk)]

/-- For i.i.d. `Xⱼ`, the shifted sequence `(X_{c+j})ⱼ` has the law of `(Xⱼ)ⱼ`. -/
theorem lil_identDistrib_shift {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {X : ℕ → Ω → ℝ} (hind : iIndepFun X Q) (hident : ∀ j, IdentDistrib (X j) (X 0) Q Q)
    (c : ℕ) :
    IdentDistrib (fun ω j => X (c + j) ω) (fun ω j => X j ω) Q Q :=
  IdentDistrib.pi (fun j => (hident (c + j)).trans (hident j).symm)
    (hind.precomp (add_right_injective c)) hind

/-- For i.i.d. `Xⱼ`, the shifted partial sums `Σ_{j<ℓ} X_{c+j}` have the law of `Σ_{j<ℓ} Xⱼ`. -/
theorem lil_identDistrib_shift_sum {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {X : ℕ → Ω → ℝ} (hind : iIndepFun X Q) (hident : ∀ j, IdentDistrib (X j) (X 0) Q Q)
    (c ℓ : ℕ) :
    IdentDistrib (fun ω => ∑ j ∈ Finset.range ℓ, X (c + j) ω)
      (fun ω => ∑ j ∈ Finset.range ℓ, X j ω) Q Q :=
  (lil_identDistrib_shift hind hident c).comp
    (u := fun v : ℕ → ℝ => ∑ j ∈ Finset.range ℓ, v j)
    (Finset.measurable_sum _ fun j _ => measurable_pi_apply j)

end RQMCMarkov.MarkovDriving

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/


/-!
# The upper half of the Hartman–Wintner LIL

Copied from the `StochasticStability/LimitTheorems` project (module `LimitTheorems.LILUpper`),
with the namespace renamed `MeynTweedie.LimitTheorems` → `RQMCMarkov.MarkovDriving` and the
generic lemma names prefixed `lil_` to avoid clashes; used by `MCRate` for the MC baseline.

For i.i.d. centred `Xⱼ ∈ L²` with `σ² = E[X₀²]`, almost surely `Sₙ ≤ (σ + ε) √(2 n log log n)`
eventually, for every `ε > 0` (`lil_upper`). This is the upper half of the i.i.d. LIL used for the
LIL parts of MT Theorems 17.2.2 and 17.3.6 (pp. 430, 441).

The proof is the classical truncation argument. The summands are truncated at
`τⱼ = δ √(j / log log j)` (`lilTrunc`, `lilTruncLevel`): the centred truncated parts are bounded,
and along the geometric blocks `n_k = ⌊θᵏ⌋` the exponential maximal inequality
(`lil_exp_maximal_ineq`, `lil_integral_exp_sum_le`) gives
`P(max_{n ≤ n_{k+1}} S'ₙ ≥ a √(2 n_k log log n_k)) ≤ (log n_k)^{−p}` with `p > 1`
(`lil_exponent_bound`), which is summable (Borel–Cantelli). The tails `X 1{|X| > τⱼ}` are
`o(√(n log log n))` a.s. by Kronecker's lemma, since
`Σⱼ E[|X| 1{|X| > τⱼ}]/√(j log log j) ≤ C E[X²] < ∞` (`summable_tail_div_lilWeight`).

* `lilTrunc`, `measurable_lilTrunc`, `abs_lilTrunc_le`, `lilTrunc_sq_le`, `abs_sub_lilTrunc`.
* `lilPhi_mono_nat`, `lilTruncLevel_nonneg`, `lilTruncLevel_mono`.
* `lil_ae_summable_of_summable_integral`: non-negative series with summable means converge a.s.
* `lil_tsum_measure_ne_top_of_summable`.
-/

namespace RQMCMarkov.MarkovDriving

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

/-! ### Truncation -/

/-- The truncation `x ↦ x 1{|x| ≤ b}`. -/
noncomputable def lilTrunc (b x : ℝ) : ℝ := if |x| ≤ b then x else 0

/-- The truncation is measurable. -/
theorem measurable_lilTrunc (b : ℝ) : Measurable (lilTrunc b) :=
  Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const) measurable_id
    measurable_const

/-- `|x 1{|x| ≤ b}| ≤ b` for `b ≥ 0`. -/
theorem abs_lilTrunc_le {b : ℝ} (hb : 0 ≤ b) (x : ℝ) : |lilTrunc b x| ≤ b := by
  unfold lilTrunc
  split_ifs with h
  · exact h
  · rw [abs_zero]; exact hb

/-- `(x 1{|x| ≤ b})² ≤ x²`. -/
theorem lilTrunc_sq_le (b x : ℝ) : lilTrunc b x ^ 2 ≤ x ^ 2 := by
  unfold lilTrunc
  split_ifs
  · exact le_rfl
  · rw [sq (0 : ℝ), mul_zero]; exact sq_nonneg x

/-- `|x − x 1{|x| ≤ b}| = |x| 1{|x| > b}`. -/
theorem abs_sub_lilTrunc (b x : ℝ) :
    |x - lilTrunc b x| = if b < |x| then |x| else 0 := by
  unfold lilTrunc
  by_cases h : |x| ≤ b
  · simp only [h, ite_true, not_lt.2 h, ite_false, sub_self, abs_zero]
  · simp only [h, ite_false, not_le.1 h, ite_true, sub_zero]

/-! ### Monotonicity of the truncation levels -/

/-- `φ` is monotone on the integers beyond `j₀` when `log j₀ ≥ 3`. -/
theorem lilPhi_mono_nat {j₀ : ℕ} (hj₀ : 3 ≤ Real.log j₀) {i j : ℕ} (hi : j₀ ≤ i)
    (hij : i ≤ j) : lilPhi i ≤ lilPhi j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    have h3 := lil_three_le_log_of_le hj₀ (hi.trans hij)
    have h1 := lil_one_le_of_three_le_log (Nat.cast_nonneg _) h3
    obtain ⟨h4, -⟩ := lilPhi_increment h1 h3
    have h5 : 0 < Real.log (Real.log ((j : ℝ) + 1)) := by
      have := (loglog_increment h1 h3).1
      have := one_le_loglog h3
      linarith
    have h6 : 0 < 1 / (2 * Real.log (Real.log ((j : ℝ) + 1))) := by positivity
    push_cast
    linarith

/-- The truncation levels are non-negative. -/
theorem lilTruncLevel_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (j₀ j : ℕ) : 0 ≤ lilTruncLevel δ j₀ j :=
  mul_nonneg hδ (Real.sqrt_nonneg _)

/-- The truncation levels are monotone. -/
theorem lilTruncLevel_mono {δ : ℝ} (hδ : 0 ≤ δ) {j₀ : ℕ} (hj₀ : 3 ≤ Real.log j₀) :
    Monotone (lilTruncLevel δ j₀) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (lilPhi_mono_nat hj₀ (le_max_right i j₀)
    (max_le_max hij le_rfl))) hδ

/-! ### The exponent of the block estimate -/

/-- The exponent in the block estimate of the upper half: with `t = a √(2 M L_M)`,
`λ = t/(N s²)` and `C = 2 δ √(N/L_N)`, `λ C ≤ 2√2 a δ/s²`, and when this is at most `1`,
`−λt + N λ² s² (1 + λC)/2 ≤ −(a²/(θ²s²)) (1 − 2√2 aδ/s²) L_M` for `M ≤ N ≤ θ² M` and
`1 ≤ L_M ≤ L_N`. -/
theorem lil_exponent_bound {a s δ θ M N LM LN : ℝ} (ha : 0 < a) (hs : 0 < s) (hδ : 0 < δ)
    (hθ : 0 < θ) (hM : 0 < M) (hMN : M ≤ N) (hNM : N ≤ θ ^ 2 * M) (hLM : 1 ≤ LM)
    (hLN : LM ≤ LN) :
    (a * √(2 * M * LM) / (N * s ^ 2)) * (2 * (δ * √(N / LN))) ≤ 2 * √2 * a * δ / s ^ 2 ∧
      (2 * √2 * a * δ / s ^ 2 ≤ 1 →
        -((a * √(2 * M * LM) / (N * s ^ 2)) * (a * √(2 * M * LM))) +
          N * ((a * √(2 * M * LM) / (N * s ^ 2)) ^ 2 * s ^ 2 *
            (1 + (a * √(2 * M * LM) / (N * s ^ 2)) * (2 * (δ * √(N / LN)))) / 2) ≤
          -((a ^ 2 / (θ ^ 2 * s ^ 2)) * (1 - 2 * √2 * a * δ / s ^ 2) * LM)) := by
  have hN : 0 < N := hM.trans_le hMN
  have hLN0 : 0 < LN := by linarith
  set t := a * √(2 * M * LM) with ht
  set l := t / (N * s ^ 2) with hl
  set C := 2 * (δ * √(N / LN)) with hC
  set η := 2 * √2 * a * δ / s ^ 2 with hη
  have ht0 : 0 ≤ t := by positivity
  have hl0 : 0 ≤ l := by positivity
  -- `λC ≤ η`
  have hlC : l * C ≤ η := by
    have hsq : √(2 * M * LM) * √(N / LN) ≤ √2 * N := by
      rw [← Real.sqrt_mul (by positivity)]
      have h1 : 2 * M * LM * (N / LN) ≤ 2 * N ^ 2 := by
        have h2 : LM / LN ≤ 1 := (div_le_one hLN0).2 hLN
        have h3 : M * (LM / LN) ≤ N := by
          calc M * (LM / LN) ≤ M * 1 := mul_le_mul_of_nonneg_left h2 hM.le
            _ ≤ N := by linarith
        have e : 2 * M * LM * (N / LN) = 2 * N * (M * (LM / LN)) := by ring
        rw [e]
        nlinarith
      calc √(2 * M * LM * (N / LN)) ≤ √(2 * N ^ 2) := Real.sqrt_le_sqrt h1
        _ = √2 * N := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hN.le]
    have e : l * C = 2 * a * δ / (N * s ^ 2) * (√(2 * M * LM) * √(N / LN)) := by
      rw [hl, hC, ht]; ring
    rw [e, hη]
    calc 2 * a * δ / (N * s ^ 2) * (√(2 * M * LM) * √(N / LN))
        ≤ 2 * a * δ / (N * s ^ 2) * (√2 * N) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = 2 * √2 * a * δ / s ^ 2 := by field_simp
  refine ⟨hlC, fun hη1 => ?_⟩
  -- `λ t = N λ² s² = q`
  set q := t ^ 2 / (N * s ^ 2) with hq
  have e1 : l * t = q := by rw [hl, hq]; ring
  have e2 : N * (l ^ 2 * s ^ 2) = q := by rw [hl, hq]; field_simp
  have e3 : -(l * t) + N * (l ^ 2 * s ^ 2 * (1 + l * C) / 2) = -(q * (1 - l * C) / 2) := by
    have : N * (l ^ 2 * s ^ 2 * (1 + l * C) / 2) = N * (l ^ 2 * s ^ 2) * (1 + l * C) / 2 := by
      ring
    rw [this, e1, e2]; ring
  rw [e3]
  have ht2 : t ^ 2 = a ^ 2 * (2 * M * LM) := by
    rw [ht, mul_pow, Real.sq_sqrt (by positivity)]
  have hq2 : a ^ 2 * LM / (θ ^ 2 * s ^ 2) ≤ q / 2 := by
    have e4 : q / 2 = a ^ 2 * M * LM / (N * s ^ 2) := by rw [hq, ht2]; ring
    rw [e4, div_le_div_iff₀ (by positivity) (by positivity)]
    have h5 : 0 ≤ a ^ 2 * LM * s ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hNM h5
    nlinarith
  have h6 : 0 ≤ 1 - η := by linarith
  have h7 : 1 - η ≤ 1 - l * C := by linarith
  have h8 : 0 ≤ a ^ 2 * LM / (θ ^ 2 * s ^ 2) := by positivity
  have h9 := mul_le_mul hq2 h7 h6 (h8.trans hq2)
  have e5 : a ^ 2 / (θ ^ 2 * s ^ 2) * (1 - η) * LM = a ^ 2 * LM / (θ ^ 2 * s ^ 2) * (1 - η) := by
    ring
  rw [e5]
  linarith

/-! ### Summability of the truncated tails -/

/-- The truncated tails are summable against the weights: for `X ∈ L²`,
`Σⱼ E[|X| 1{|X| > τⱼ}]/wⱼ < ∞`. -/
theorem summable_tail_div_lilWeight {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {Z : Ω → ℝ} (hZm : Measurable Z) (hZ2 : MemLp Z 2 Q) {δ : ℝ}
    (hδ : 0 < δ) {j₀ : ℕ} (hj₀ : 3 ≤ Real.log j₀) :
    Summable fun j => (∫ ω, |Z ω - lilTrunc (lilTruncLevel δ j₀ j) (Z ω)| ∂Q) / lilWeight j₀ j := by
  set K := (j₀ : ℝ) / lilWeight j₀ j₀ with hK
  have hZi : Integrable Z Q := hZ2.integrable one_le_two
  have hZ2i : Integrable (fun ω => Z ω ^ 2) Q := hZ2.integrable_sq
  have hbdi : Integrable (fun ω => |Z ω| * (K + 8 * (|Z ω| / δ + 1))) Q := by
    have e : (fun ω => |Z ω| * (K + 8 * (|Z ω| / δ + 1))) =
        fun ω => (K + 8) * |Z ω| + (8 / δ) * Z ω ^ 2 := by
      ext ω; rw [← sq_abs (Z ω)]; field_simp; ring
    rw [e]
    exact (hZi.abs.const_mul _).add (hZ2i.const_mul _)
  have hti : ∀ j, Integrable (fun ω => |Z ω - lilTrunc (lilTruncLevel δ j₀ j) (Z ω)|) Q :=
    fun j => (hZi.sub (Integrable.of_bound ((measurable_lilTrunc _).comp hZm).aestronglyMeasurable
      (lilTruncLevel δ j₀ j) (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]
        exact abs_lilTrunc_le (lilTruncLevel_nonneg hδ.le j₀ j) _))).abs
  refine summable_of_sum_range_le (c := ∫ ω, |Z ω| * (K + 8 * (|Z ω| / δ + 1)) ∂Q)
    (fun j => div_nonneg (integral_nonneg fun ω => abs_nonneg _) (lilWeight_pos hj₀ j).le)
    fun n => ?_
  have e1 : ∑ j ∈ Finset.range n,
      (∫ ω, |Z ω - lilTrunc (lilTruncLevel δ j₀ j) (Z ω)| ∂Q) / lilWeight j₀ j =
      ∫ ω, ∑ j ∈ Finset.range n,
        |Z ω - lilTrunc (lilTruncLevel δ j₀ j) (Z ω)| / lilWeight j₀ j ∂Q := by
    rw [integral_finsetSum _ fun j _ => (hti j).div_const _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_div]
  rw [e1]
  refine integral_mono (integrable_finsetSum _ fun j _ => (hti j).div_const _) hbdi
    fun ω => ?_
  have hpt : ∀ j, |Z ω - lilTrunc (lilTruncLevel δ j₀ j) (Z ω)| / lilWeight j₀ j =
      |Z ω| * (if lilTruncLevel δ j₀ j < |Z ω| then 1 / lilWeight j₀ j else 0) := fun j => by
    rw [abs_sub_lilTrunc]
    split_ifs
    · ring
    · rw [zero_div, mul_zero]
  simp only
  simp_rw [hpt]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_inv_lilWeight_le hδ hj₀ (abs_nonneg _) n)
    (abs_nonneg _)

/-- Non-negative random series with summable means converge almost surely. -/
theorem lil_ae_summable_of_summable_integral {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {f : ℕ → Ω → ℝ} (hm : ∀ j, Measurable (f j)) (h0 : ∀ j ω, 0 ≤ f j ω)
    (hi : ∀ j, Integrable (f j) Q) (hs : Summable fun j => ∫ ω, f j ω ∂Q) :
    ∀ᵐ ω ∂Q, Summable fun j => f j ω := by
  have h1 : ∫⁻ ω, ∑' j, ENNReal.ofReal (f j ω) ∂Q = ∑' j, ENNReal.ofReal (∫ ω, f j ω ∂Q) := by
    rw [lintegral_tsum fun j => (hm j).ennreal_ofReal.aemeasurable]
    congr 1
    ext j
    rw [ofReal_integral_eq_lintegral_ofReal (hi j) (ae_of_all _ (h0 j))]
  have h2 : ∑' j, ENNReal.ofReal (∫ ω, f j ω ∂Q) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => integral_nonneg (h0 j)) hs]
    exact ENNReal.ofReal_ne_top
  have h3 := ae_lt_top' (AEMeasurable.tsum fun j => (hm j).ennreal_ofReal.aemeasurable)
    (h1 ▸ h2)
  filter_upwards [h3] with ω hω
  exact (ENNReal.summable_toReal hω.ne).congr fun j => ENNReal.toReal_ofReal (h0 j ω)

/-- For a finite measure, summable real measures have finite `ENNReal` sum. -/
theorem lil_tsum_measure_ne_top_of_summable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsFiniteMeasure Q] {B : ℕ → Set Ω} (h : Summable fun k => Q.real (B k)) :
    ∑' k, Q (B k) ≠ ∞ := by
  have e : ∀ k, Q (B k) = ENNReal.ofReal (Q.real (B k)) := fun k =>
    (ofReal_measureReal (μ := Q) (s := B k)).symm
  simp_rw [e]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => measureReal_nonneg) h]
  exact ENNReal.ofReal_ne_top

/-! ### The upper half of the LIL -/

/-- **The upper half of the Hartman–Wintner LIL**: for i.i.d. centred `Xⱼ ∈ L²` with
`σ² = E[X₀²]` and every `ε > 0`, almost surely `Sₙ ≤ (σ + ε) √(2 n log log n)` eventually. -/
theorem lil_upper {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {X : ℕ → Ω → ℝ} (hind : iIndepFun X Q) (hm : ∀ j, Measurable (X j))
    (hident : ∀ j, IdentDistrib (X j) (X 0) Q Q) (hL2 : MemLp (X 0) 2 Q)
    (h0 : ∫ ω, X 0 ω ∂Q = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂Q, ∀ᶠ n in atTop,
      ∑ j ∈ Finset.range n, X j ω ≤ (√(∫ ω, X 0 ω ^ 2 ∂Q) + ε) * lilScale n := by
  set σ := √(∫ ω, X 0 ω ^ 2 ∂Q) with hσ
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hσ2 : σ ^ 2 = ∫ ω, X 0 ω ^ 2 ∂Q :=
    Real.sq_sqrt (integral_nonneg fun ω => sq_nonneg _)
  -- the constants
  set s := σ + ε / 2 with hs
  set a := σ + 3 * ε / 4 with ha
  have hs0 : 0 < s := by positivity
  have ha0 : 0 < a := by positivity
  set ρ := a / s with hρ
  have hρ1 : 1 < ρ := by rw [hρ, one_lt_div hs0]; linarith
  have has : a = ρ * s := by rw [hρ]; field_simp
  set θ := √ρ with hθ
  have hθ1 : 1 < θ := by
    rw [hθ, show (1 : ℝ) = √1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt zero_le_one hρ1
  have hθ0 : 0 < θ := by linarith
  have hθ2 : θ ^ 2 = ρ := Real.sq_sqrt (by linarith)
  set η := (1 - 1 / ρ) / 2 with hη
  have hρinv : 1 / ρ < 1 := by rw [div_lt_one (by linarith)]; exact hρ1
  have hρinv0 : 0 < 1 / ρ := by positivity
  have hη0 : 0 < η := by rw [hη]; linarith
  have hη1 : η ≤ 1 := by rw [hη]; linarith
  set p := ρ * (1 - η) with hp
  have hp1 : 1 < p := by
    have e : p = (ρ + 1) / 2 := by rw [hp, hη]; field_simp; ring
    rw [e]; linarith
  set δ := η * s ^ 2 / (2 * √2 * a) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδη : 2 * √2 * a * δ / s ^ 2 = η := by rw [hδ]; field_simp
  have hpeq : a ^ 2 / (θ ^ 2 * s ^ 2) * (1 - η) = p := by
    rw [hθ2, has, hp]; field_simp
  -- the truncation
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : ℕ, 3 ≤ Real.log j₀ := (lil_eventually_le_log 3).exists
  set β : ℕ → ℝ := lilTruncLevel δ j₀ with hβ
  have hβ0 : ∀ j, 0 ≤ β j := lilTruncLevel_nonneg hδ0.le j₀
  have hβm : Monotone β := lilTruncLevel_mono hδ0.le hj₀
  have hXL2 : ∀ j, MemLp (X j) 2 Q := fun j => (hident j).memLp_iff.2 hL2
  have hXi : ∀ j, Integrable (X j) Q := fun j => (hXL2 j).integrable one_le_two
  have hTi : ∀ j i, Integrable (fun ω => lilTrunc (β j) (X i ω)) Q := fun j i =>
    Integrable.of_bound ((measurable_lilTrunc _).comp (hm i)).aestronglyMeasurable (β j)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact abs_lilTrunc_le (hβ0 j) _)
  have hTeq : ∀ j, ∫ ω, lilTrunc (β j) (X j ω) ∂Q = ∫ ω, lilTrunc (β j) (X 0 ω) ∂Q := fun j =>
    ((hident j).comp (measurable_lilTrunc (β j))).integral_eq
  set μt : ℕ → ℝ := fun j => ∫ ω, lilTrunc (β j) (X 0 ω) ∂Q with hμt
  set Y : ℕ → Ω → ℝ := fun j ω => lilTrunc (β j) (X j ω) - μt j with hY
  have hYm : ∀ j, Measurable (Y j) := fun j => ((measurable_lilTrunc _).comp (hm j)).sub_const _
  have hYind : iIndepFun Y Q :=
    hind.comp (fun j x => lilTrunc (β j) x - μt j) fun j => (measurable_lilTrunc _).sub_const _
  have hμb : ∀ j, |μt j| ≤ β j := fun j => by
    calc |μt j| ≤ ∫ ω, |lilTrunc (β j) (X 0 ω)| ∂Q := abs_integral_le_integral_abs
      _ ≤ ∫ _ω, β j ∂Q := integral_mono (hTi j 0).abs (integrable_const _) fun ω =>
          abs_lilTrunc_le (hβ0 j) _
      _ = β j := by simp
  have hYb : ∀ j ω, |Y j ω| ≤ 2 * β j := fun j ω => by
    have h1 := abs_lilTrunc_le (hβ0 j) (X j ω)
    have h2 := hμb j
    calc |Y j ω| ≤ |lilTrunc (β j) (X j ω)| + |μt j| := abs_sub _ _
      _ ≤ 2 * β j := by linarith
  have hY0 : ∀ j, ∫ ω, Y j ω ∂Q = 0 := fun j => by
    simp only [hY]
    rw [integral_sub (hTi j j) (integrable_const _), integral_const, probReal_univ, one_smul,
      hTeq j, sub_self]
  have hY2 : ∀ j, ∫ ω, Y j ω ^ 2 ∂Q ≤ s ^ 2 := fun j => by
    have hT2i : Integrable (fun ω => lilTrunc (β j) (X j ω) ^ 2) Q :=
      Integrable.of_bound (((measurable_lilTrunc _).comp (hm j)).pow_const 2).aestronglyMeasurable
        (β j ^ 2) (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (abs_lilTrunc_le (hβ0 j) _) 2)
    have hexp : ∫ ω, Y j ω ^ 2 ∂Q = ∫ ω, lilTrunc (β j) (X j ω) ^ 2 ∂Q - μt j ^ 2 := by
      have e : (fun ω => Y j ω ^ 2) = fun ω => lilTrunc (β j) (X j ω) ^ 2 +
          (-(2 * μt j) * lilTrunc (β j) (X j ω) + μt j ^ 2) := by
        ext ω; simp only [hY]; ring
      have hA : Integrable (fun ω => -(2 * μt j) * lilTrunc (β j) (X j ω) + μt j ^ 2) Q :=
        ((hTi j j).const_mul _).add (integrable_const _)
      rw [e, integral_add hT2i hA,
        integral_add ((hTi j j).const_mul _) (integrable_const _), integral_const_mul,
        integral_const, probReal_univ, one_smul, hTeq j]
      ring
    have h1 : ∫ ω, lilTrunc (β j) (X j ω) ^ 2 ∂Q ≤ ∫ ω, X j ω ^ 2 ∂Q :=
      integral_mono hT2i (hXL2 j).integrable_sq fun ω => lilTrunc_sq_le _ _
    have h2 : ∫ ω, X j ω ^ 2 ∂Q = σ ^ 2 := by
      rw [hσ2]; exact ((hident j).comp (measurable_id.pow_const 2)).integral_eq
    have h3 : σ ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hσ0 (by linarith) 2
    nlinarith [sq_nonneg (μt j)]
  -- the geometric blocks
  set nk : ℕ → ℕ := fun k => ⌊θ ^ k⌋₊ with hnk
  have hnk_mono : Monotone nk := fun i j hij =>
    Nat.floor_mono (pow_le_pow_right₀ hθ1.le hij)
  have hnk_t : Tendsto nk atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_pow_atTop_atTop_of_one_lt hθ1)
  set B : ℕ → Set Ω := fun k =>
    {ω | ∃ n ≤ nk (k + 1), a * lilScale (nk k) ≤ ∑ j ∈ Finset.range n, Y j ω} with hB
  have hBbound : ∀ᶠ k in atTop, Q.real (B k) ≤
      Real.exp (-(p * Real.log (Real.log (nk k : ℝ)))) := by
    filter_upwards [hnk_t.eventually (lil_eventually_le_log 3),
      lil_eventually_floor_pow_succ_le hθ1, hnk_t.eventually_ge_atTop j₀] with k hk3 hkθ hkj
    set M := nk k with hM
    set N := nk (k + 1) with hN
    have hMN : M ≤ N := hnk_mono (Nat.le_succ k)
    have hN3 : 3 ≤ Real.log N := lil_three_le_log_of_le hk3 hMN
    have hM0 : (0 : ℝ) < M := by
      have := lil_one_le_of_three_le_log (Nat.cast_nonneg _) hk3; linarith
    have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
    have hLM := one_le_loglog hk3
    have hLN : Real.log (Real.log M) ≤ Real.log (Real.log N) :=
      Real.log_le_log (by linarith) (Real.log_le_log hM0 hMN')
    obtain ⟨hlC, hexp⟩ := lil_exponent_bound (a := a) (s := s) (δ := δ) (θ := θ)
      (M := M) (N := N) (LM := Real.log (Real.log M)) (LN := Real.log (Real.log N))
      ha0 hs0 hδ0 hθ0 hM0 hMN' (by rw [hθ2] at hkθ ⊢; exact hkθ) hLM hLN
    rw [hδη] at hlC hexp
    have hexp' := hexp hη1
    rw [hpeq] at hexp'
    set t := a * √(2 * M * Real.log (Real.log M)) with ht
    set l := t / (N * s ^ 2) with hl
    have hl0 : 0 ≤ l := by positivity
    have htl : a * lilScale M = t := rfl
    have hβN : 2 * β N = 2 * (δ * √(N / Real.log (Real.log N))) := by
      rw [hβ, lilTruncLevel, max_eq_left (hkj.trans hMN), lilPhi]
    have hmax := lil_exp_maximal_ineq hYind hYm hYb hY0 N (l := l) (t := t) hl0
    have hsum := lil_integral_exp_sum_le hYind hYm hYb hY0 N (l := l) (C := 2 * β N)
      (s2 := s ^ 2) hl0 (fun j hj => by have := hβm hj.le; linarith)
      (by rw [hβN]; linarith) (fun j _ => hY2 j)
    have h1 : Real.exp (l * t) * Q.real (B k) ≤
        Real.exp (N * (l ^ 2 * s ^ 2 * (1 + l * (2 * β N)) / 2)) := by
      refine le_trans (le_of_eq ?_) (hmax.trans hsum)
      rfl
    rw [hβN] at h1
    have h2 : Q.real (B k) ≤ Real.exp (-(l * t) + N * (l ^ 2 * s ^ 2 *
        (1 + l * (2 * (δ * √(N / Real.log (Real.log N))))) / 2)) := by
      rw [Real.exp_add, Real.exp_neg, ← div_eq_inv_mul, le_div_iff₀ (Real.exp_pos _),
        mul_comm]
      exact h1
    exact h2.trans (Real.exp_le_exp.2 hexp')
  -- Borel–Cantelli
  have hsumB : Summable fun k => Q.real (B k) :=
    (summable_exp_neg_mul_loglog_floor_pow hθ1 hp1).of_norm_bounded_eventually_nat (by
      filter_upwards [hBbound] with k hk
      rwa [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg])
  have hBC : ∀ᵐ ω ∂Q, ∀ᶠ k in atTop, ω ∉ B k :=
    ae_eventually_notMem (lil_tsum_measure_ne_top_of_summable hsumB)
  -- the tails and Kronecker's lemma
  set w : ℕ → ℝ := lilWeight j₀ with hw
  set e : ℕ → ℝ := fun j => ∫ ω, |X 0 ω - lilTrunc (β j) (X 0 ω)| ∂Q with he
  set A : ℕ → Ω → ℝ := fun j ω => |X j ω - lilTrunc (β j) (X j ω)| + e j with hA
  have hDi : ∀ j i, Integrable (fun ω => |X i ω - lilTrunc (β j) (X i ω)|) Q := fun j i =>
    ((hXi i).sub (hTi j i)).abs
  have hDeq : ∀ j, ∫ ω, |X j ω - lilTrunc (β j) (X j ω)| ∂Q = e j := fun j =>
    ((hident j).comp (u := fun x => |x - lilTrunc (β j) x|)
      (continuous_abs.measurable.comp (measurable_id.sub (measurable_lilTrunc _)))).integral_eq
  have he0 : ∀ j, 0 ≤ e j := fun j => integral_nonneg fun ω => abs_nonneg _
  have hsumA : Summable fun j => ∫ ω, A j ω / w j ∂Q := by
    have := (summable_tail_div_lilWeight (hm 0) hL2 hδ0 hj₀).mul_left 2
    refine this.congr fun j => ?_
    rw [integral_div, hA]
    simp only
    rw [integral_add (hDi j j) (integrable_const _), hDeq, integral_const, probReal_univ,
      one_smul]
    ring
  have hAm : ∀ j, Measurable fun ω => A j ω / w j := fun j =>
    ((continuous_abs.measurable.comp ((hm j).sub ((measurable_lilTrunc _).comp
      (hm j)))).add_const _).div_const _
  have hA0 : ∀ j ω, 0 ≤ A j ω / w j := fun j ω =>
    div_nonneg (add_nonneg (abs_nonneg _) (he0 j)) (lilWeight_pos hj₀ j).le
  have hAi : ∀ j, Integrable (fun ω => A j ω / w j) Q := fun j =>
    ((hDi j j).add (integrable_const _)).div_const _
  have hKr := lil_ae_summable_of_summable_integral hAm hA0 hAi hsumA
  have hμe : ∀ j, |μt j| ≤ e j := fun j => by
    have e1 : μt j = -∫ ω, (X 0 ω - lilTrunc (β j) (X 0 ω)) ∂Q := by
      rw [integral_sub (hXi 0) (hTi j 0), h0]; simp [hμt]
    rw [e1, abs_neg]
    exact abs_integral_le_integral_abs
  filter_upwards [hBC, hKr] with ω hωB hωK
  have hW := lil_tendsto_sum_div_of_summable (a := fun j => A j ω) (w := w)
    (fun j => add_nonneg (abs_nonneg _) (he0 j)) (lilWeight_pos hj₀) (lilWeight_mono hj₀)
    tendsto_lilWeight hωK
  have hW' : ∀ᶠ n in atTop, ∑ j ∈ Finset.range n, A j ω ≤ ε / 4 * w n := by
    filter_upwards [hW.eventually (eventually_le_nhds (show (0 : ℝ) < ε / 4 by positivity))]
      with n hn
    rwa [div_le_iff₀ (lilWeight_pos hj₀ n)] at hn
  obtain ⟨K1, hK1⟩ := eventually_atTop.1 hωB
  obtain ⟨K2, hK2⟩ := eventually_atTop.1 ((hnk_t.eventually (lil_eventually_le_log 3)).and
    (eventually_ge_atTop (K1 + 1)))
  filter_upwards [hW', eventually_gt_atTop (nk K2), eventually_ge_atTop j₀] with n hnW hnK hnj
  classical
  have hex : ∃ k, n ≤ nk (k + 1) := by
    obtain ⟨k, hk⟩ := (hnk_t.eventually_ge_atTop n).exists
    exact ⟨k, hk.trans (hnk_mono (Nat.le_succ k))⟩
  set k := Nat.find hex with hkdef
  have hkn : n ≤ nk (k + 1) := Nat.find_spec hex
  have hkK : K2 ≤ k := by
    by_contra h
    push Not at h
    have := hnk_mono (show k + 1 ≤ K2 by omega)
    omega
  have hK1k : K1 + 1 ≤ k := (hK2 K2 le_rfl).2.trans hkK
  have hnk_lt : nk k < n := by
    have h := Nat.find_min hex (show k - 1 < k by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at h
    omega
  have h3 : 3 ≤ Real.log (nk k : ℝ) := (hK2 k hkK).1
  -- the truncated part
  have hYbound : ∑ j ∈ Finset.range n, Y j ω < a * lilScale (nk k) := by
    have h := hK1 k (by omega)
    simp only [hB, mem_ofPred_eq, not_exists, not_and, not_le] at h
    exact h n hkn
  have hlil : lilScale (nk k) ≤ lilScale n := lilScale_mono h3 hnk_lt.le
  -- the tails
  have hdiff : ∑ j ∈ Finset.range n, X j ω - ∑ j ∈ Finset.range n, Y j ω ≤
      ∑ j ∈ Finset.range n, A j ω := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have e1 : X j ω - Y j ω = (X j ω - lilTrunc (β j) (X j ω)) + μt j := by
      simp only [hY]; ring
    rw [e1]
    have := le_abs_self (X j ω - lilTrunc (β j) (X j ω))
    have := (abs_le.1 (hμe j)).2
    simp only [hA]
    linarith
  have hwl : w n ≤ lilScale n := by
    rw [lilScale_eq_lilWeight hnj]
    have h1 : (1 : ℝ) ≤ √2 := by
      rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    have h2 := (lilWeight_pos hj₀ n).le
    nlinarith
  have hfin : a * lilScale n + ε / 4 * lilScale n = (σ + ε) * lilScale n := by
    rw [ha]; ring
  have h4 : ε / 4 * w n ≤ ε / 4 * lilScale n :=
    mul_le_mul_of_nonneg_left hwl (by positivity)
  have h5 : a * lilScale (nk k) ≤ a * lilScale n := mul_le_mul_of_nonneg_left hlil ha0.le
  linarith

end RQMCMarkov.MarkovDriving

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/


/-!
# The lower half of the Hartman–Wintner LIL

Copied from the `StochasticStability/LimitTheorems` project (module `LimitTheorems.LILLower`),
with the namespace renamed `MeynTweedie.LimitTheorems` → `RQMCMarkov.MarkovDriving` and the
generic lemma names prefixed `lil_` to avoid clashes; used by `MCRate` for the MC baseline.

For i.i.d. `Xⱼ` with mean `0` and variance `1` and `0 < ε ≤ 1`, almost surely
`Sₙ ≥ (1 − ε) √(2 n log log n)` for infinitely many `n` (`lil_lower_normalized`). With
`lil_upper` this gives the i.i.d. LIL (`IIDLIL`) used for MT Theorems 17.2.2 and 17.3.6.

The proof uses the central limit theorem (Mathlib's `tendstoInDistribution_inv_sqrt_mul_sum`)
instead of Kolmogorov's lower exponential inequality, by a blocking argument in the spirit of
de Acosta (*Ann. Probab.* 11 (1983)). Along `n_k = mᵏ`, the block `[mᵏ, mᵏ⁺¹)` of
`N = mᵏ⁺¹ − mᵏ` summands is cut into `r ≈ 2γ² log log mᵏ⁺¹/A²` sub-blocks of length `ℓ = N/r`;
by the CLT each sub-block sum exceeds `(A + 2)√ℓ` with probability at least `e^{−κ}`,
`κ = (A + 3)²/2 + 2` (`lil_gaussianReal_Ioi_ge`, `lil_eventually_lt_measure_clt`), so the block sum
exceeds `(1 − ε/2) √(2 mᵏ⁺¹ log log mᵏ⁺¹)` with probability at least
`(e^{−κ}/2) (log mᵏ⁺¹)^{−p'}`, `p' = 2γ²κ/A² ≤ 1` (`block_lower_bound`,
`lil_lower_block_estimate`). These probabilities are not summable and the blocks are
independent (`lil_iIndepFun_blockSum`, `lil_iIndepSet_preimage`), so the second Borel–Cantelli lemma
applies; the start `S_{mᵏ}` of the block is controlled by the upper half.

* `lil_gaussianReal_Ioi_ge`: `P(Z > b) ≥ e^{−(b+1)²/2}/√(2π)`; `lil_two_mul_sqrt_two_pi_le_exp_two`.
* `lil_sum_range_mul_eq`, `le_block_level`, `lil_eventually_mul_sq_le_pow`,
  `exists_lil_lower_ratio`, `exists_lil_lower_level`: arithmetic of the blocks.
-/

namespace RQMCMarkov.MarkovDriving

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

/-! ### A Gaussian tail bound -/

/-- `P(Z > b) ≥ e^{−(b+1)²/2}/√(2π)` for a standard normal `Z` and `b ≥ 0`. -/
theorem lil_gaussianReal_Ioi_ge {b : ℝ} (hb : 0 ≤ b) :
    Real.exp (-((b + 1) ^ 2 / 2)) / √(2 * Real.pi) ≤ (gaussianReal 0 1).real (Ioi b) := by
  set c := Real.exp (-((b + 1) ^ 2 / 2)) / √(2 * Real.pi) with hc
  have hc0 : 0 ≤ c := by positivity
  have h1 : ENNReal.ofReal c ≤ gaussianReal 0 1 (Ioi b) := by
    rw [gaussianReal_apply 0 one_ne_zero]
    calc ENNReal.ofReal c = ∫⁻ _x in Ioo b (b + 1), ENNReal.ofReal c := by
          rw [setLIntegral_const, Real.volume_Ioo, add_sub_cancel_left, ENNReal.ofReal_one,
            mul_one]
      _ ≤ ∫⁻ x in Ioo b (b + 1), gaussianPDF 0 1 x :=
          setLIntegral_mono (measurable_gaussianPDF 0 1) fun x hx => by
            rw [gaussianPDF]
            apply ENNReal.ofReal_le_ofReal
            rw [gaussianPDFReal, hc]
            simp only [NNReal.coe_one, mul_one, sub_zero]
            rw [div_eq_inv_mul]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Real.exp_le_exp.2
            have hx1 : b < x := hx.1
            have hx2 : x < b + 1 := hx.2
            have : x ^ 2 ≤ (b + 1) ^ 2 := by nlinarith
            linarith
      _ ≤ ∫⁻ x in Ioi b, gaussianPDF 0 1 x :=
          lintegral_mono_set Ioo_subset_Ioi_self
  have h2 := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 h1
  exact h2

/-- `2 √(2π) ≤ e²`. -/
theorem lil_two_mul_sqrt_two_pi_le_exp_two : 2 * √(2 * Real.pi) ≤ Real.exp 2 := by
  have hpi := Real.pi_lt_d2
  have h1 : √(2 * Real.pi) ≤ 2.6 := by
    rw [Real.sqrt_le_left (by norm_num)]
    linarith
  have h2 := Real.exp_one_gt_d9
  have h3 : Real.exp 2 = Real.exp 1 ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h3]
  nlinarith

/-! ### The CLT on half lines -/

/-- From the CLT: for i.i.d. `Xⱼ` with mean `0` and variance `1`, every `b` and every
`q < P(Z > b)`, eventually `P(Σ_{j<ℓ} Xⱼ > b √ℓ) > q`. -/
theorem lil_eventually_lt_measure_clt {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {X : ℕ → Ω → ℝ} (hind : iIndepFun X Q)
    (hm : ∀ j, Measurable (X j)) (hident : ∀ j, IdentDistrib (X j) (X 0) Q Q)
    (h0 : ∫ ω, X 0 ω ∂Q = 0) (h1 : ∫ ω, X 0 ω ^ 2 ∂Q = 1) (b : ℝ) {q : ℝ≥0∞}
    (hq : q < gaussianReal 0 1 (Ioi b)) :
    ∀ᶠ ℓ : ℕ in atTop, q < Q {ω | b * √(ℓ : ℝ) < ∑ j ∈ Finset.range ℓ, X j ω} := by
  have h1' : Q[X 0 ^ 2] = 1 := by simpa [Pi.pow_apply] using h1
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum (P' := gaussianReal 0 1) (Y := id)
    HasLaw.id h0 h1' hind hident
  have hlim := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hclt.tendsto
    (isOpen_Ioi (a := b))
  simp only [ProbabilityMeasure.coe_mk, Measure.map_id] at hlim
  have hev := eventually_lt_of_lt_liminf (hq.trans_le hlim)
  filter_upwards [hev, eventually_ge_atTop 1] with ℓ hℓ hℓ1
  have hWm : Measurable fun ω => (√(ℓ : ℝ))⁻¹ * ∑ k ∈ Finset.range ℓ, X k ω :=
    measurable_const.mul (Finset.measurable_sum _ fun j _ => hm j)
  rw [Measure.map_apply hWm measurableSet_Ioi] at hℓ
  convert hℓ using 2
  ext ω
  have hs : 0 < √(ℓ : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hℓ1)
  simp only [mem_ofPred_eq, mem_preimage, mem_Ioi]
  rw [inv_mul_eq_div, lt_div_iff₀ hs]

/-! ### Independence of block sums -/

/-- Sums of independent variables over pairwise disjoint finite index sets are independent. -/
theorem lil_iIndepFun_blockSum {Ω κ : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {X : ℕ → Ω → ℝ} (hind : iIndepFun X Q) (hm : ∀ j, Measurable (X j)) {I : κ → Finset ℕ}
    (hI : Pairwise (Function.onFun Disjoint fun k => (I k : Set ℕ))) :
    iIndepFun (fun k ω => ∑ j ∈ I k, X j ω) Q := by
  have h1 : iIndep (fun j => MeasurableSpace.comap (X j) inferInstance) Q :=
    (iIndepFun_iff_iIndep _ _ _).1 hind
  have h2 := lil_iIndep_iSup_blocks (fun j => (hm j).comap_le) h1 hI
  rw [iIndepFun_iff_iIndep]
  refine iIndep_of_iIndep_of_le h2 fun k => ?_
  apply Measurable.comap_le
  refine Finset.measurable_sum (I k) fun j hj => ?_
  exact Measurable.mono (comap_measurable (X j))
    (le_iSup₂ (f := fun j (_ : j ∈ (I k : Set ℕ)) => MeasurableSpace.comap (X j) inferInstance)
      j hj) le_rfl

/-- Preimages of measurable sets under independent variables are independent events. -/
theorem lil_iIndepSet_preimage {Ω κ β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {Q : Measure Ω} {Z : κ → Ω → β} (h : iIndepFun Z Q) {A : κ → Set β}
    (hA : ∀ k, MeasurableSet (A k)) : iIndepSet (fun k => Z k ⁻¹' A k) Q := by
  rw [iIndepSet_iff_iIndep]
  refine iIndep_of_iIndep_of_le ((iIndepFun_iff_iIndep _ _ _).1 h) fun k => ?_
  refine MeasurableSpace.generateFrom_le fun t ht => ?_
  rw [mem_singleton_iff.1 ht]
  exact ⟨A k, hA k, rfl⟩

/-- `Σ_{j < r ℓ} f j = Σ_{i<r} Σ_{j<ℓ} f (i ℓ + j)`. -/
theorem lil_sum_range_mul_eq (f : ℕ → ℝ) (r ℓ : ℕ) :
    ∑ j ∈ Finset.range (r * ℓ), f j =
      ∑ i ∈ Finset.range r, ∑ j ∈ Finset.range ℓ, f (i * ℓ + j) := by
  induction r with
  | zero => simp
  | succ r ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-! ### The probability of a large block sum -/

/-- **A large block sum from many moderately large sub-blocks**: for i.i.d. centred `Xⱼ` with
`E[X₀²] = 1`, a block of `r ℓ + e` consecutive summands starting at `c` satisfies
`P(Σ ≥ (r b − 1) √ℓ) ≥ P(S_ℓ > b √ℓ)^r (1 − e/ℓ)`: all `r` sub-blocks of length `ℓ` exceed
`b √ℓ` (independently) and the remainder of `e` terms is at least `−√ℓ` (Kolmogorov). -/
theorem block_lower_bound {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {X : ℕ → Ω → ℝ} (hind : iIndepFun X Q)
    (hm : ∀ j, Measurable (X j)) (hident : ∀ j, IdentDistrib (X j) (X 0) Q Q)
    (hL2 : MemLp (X 0) 2 Q) (h0 : ∫ ω, X 0 ω ∂Q = 0) (h1 : ∫ ω, X 0 ω ^ 2 ∂Q = 1)
    (c r ℓ e : ℕ) (b : ℝ) (hℓ : 0 < ℓ) :
    Q.real {ω | b * √(ℓ : ℝ) < ∑ j ∈ Finset.range ℓ, X j ω} ^ r * (1 - e / ℓ) ≤
      Q.real {ω | (r * b - 1) * √(ℓ : ℝ) ≤ ∑ j ∈ Finset.range (r * ℓ + e), X (c + j) ω} := by
  classical
  set L : ℕ → ℕ := fun i => if i < r then ℓ else if i = r then e else 0 with hL
  set I : ℕ → Finset ℕ := fun i => Finset.Ico (c + i * ℓ) (c + i * ℓ + L i) with hI
  have hLle : ∀ i, i < r → L i = ℓ := fun i hi => by simp only [hL, hi, ite_true]
  have hLr : L r = e := by simp only [hL, lt_irrefl, ite_false, ite_true]
  have hLgt : ∀ i, r < i → L i = 0 := fun i hi => by
    simp only [hL, show ¬ i < r by omega, show i ≠ r by omega, ite_false]
  have hcase : ∀ i i', i < i' → L i' = 0 ∨ L i = ℓ := fun i i' h => by
    by_cases h1 : r < i'
    · exact Or.inl (hLgt i' h1)
    · exact Or.inr (hLle i (by omega))
  have hdisj1 : ∀ i i', i < i' → Disjoint (I i : Set ℕ) (I i') := fun i i' h => by
    simp only [Finset.coe_Ico, hI]
    rw [Set.Ico_disjoint_Ico]
    have hm1 : i * ℓ + ℓ ≤ i' * ℓ := by
      have := Nat.mul_le_mul_right ℓ h; rwa [Nat.succ_mul] at this
    generalize i * ℓ = u at hm1 ⊢
    generalize i' * ℓ = v at hm1 ⊢
    rcases hcase i i' h with h2 | h2 <;> rw [h2] <;> omega
  have hdisj : Pairwise (Function.onFun Disjoint fun i => (I i : Set ℕ)) := by
    intro i i' hii'
    rcases lt_or_gt_of_ne hii' with h | h
    · exact hdisj1 i i' h
    · exact (hdisj1 i' i h).symm
  -- the block sums
  set Z : ℕ → Ω → ℝ := fun i ω => ∑ j ∈ I i, X j ω with hZ
  have hZind : iIndepFun Z Q := lil_iIndepFun_blockSum hind hm hdisj
  have hZeq : ∀ i ω, Z i ω = ∑ j ∈ Finset.range (L i), X (c + i * ℓ + j) ω := fun i ω => by
    simp only [hZ, hI]
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  set A : ℕ → Set ℝ := fun i => if i < r then Ioi (b * √(ℓ : ℝ)) else Ici (-√(ℓ : ℝ)) with hA
  have hAm : ∀ i, MeasurableSet (A i) := fun i => by
    simp only [hA]; split_ifs
    · exact measurableSet_Ioi
    · exact measurableSet_Ici
  set E := ⋂ i ∈ Finset.range (r + 1), Z i ⁻¹' A i with hE
  have hZm : ∀ i, Measurable (Z i) := fun i => Finset.measurable_sum _ fun j _ => hm j
  have hprod : Q.real E = ∏ i ∈ Finset.range (r + 1), Q.real (Z i ⁻¹' A i) := by
    have h := hZind.meas_biInter (S := Finset.range (r + 1))
      (s := fun i => Z i ⁻¹' A i) fun i _ => ⟨A i, hAm i, rfl⟩
    rw [measureReal_def, hE, h, ENNReal.toReal_prod]
    rfl
  -- the sub-blocks of length `ℓ`
  have hsub : ∀ i < r, Q.real (Z i ⁻¹' A i) =
      Q.real {ω | b * √(ℓ : ℝ) < ∑ j ∈ Finset.range ℓ, X j ω} := fun i hi => by
    have hsh := lil_identDistrib_shift_sum hind hident (c + i * ℓ) ℓ
    have e1 : Z i ⁻¹' A i =
        (fun ω => ∑ j ∈ Finset.range ℓ, X (c + i * ℓ + j) ω) ⁻¹' Ioi (b * √(ℓ : ℝ)) := by
      ext ω
      simp only [mem_preimage, hA, hi, ite_true, hZeq i ω, hLle i hi]
    rw [e1, measureReal_def, measureReal_def, hsh.measure_mem_eq measurableSet_Ioi]
    rfl
  -- the remainder
  have hrem : 1 - e / ℓ ≤ Q.real (Z r ⁻¹' A r) := by
    have hL2j : ∀ j, MemLp (X j) 2 Q := fun j => (hident j).memLp_iff.2 hL2
    have h0j : ∀ j, ∫ ω, X j ω ∂Q = 0 := fun j => (hident j).integral_eq.trans h0
    have hσj : ∀ j, ∫ ω, X j ω ^ 2 ∂Q = 1 := fun j =>
      (((hident j).comp (measurable_id.pow_const 2)).integral_eq).trans h1
    have hk := lil_kolmogorov_ineq_shift hind hm hL2j h0j (c + r * ℓ) e
      (t := √(ℓ : ℝ)) (Real.sqrt_pos.2 (by exact_mod_cast hℓ))
    simp_rw [hσj, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hk
    rw [Real.sq_sqrt (Nat.cast_nonneg _)] at hk
    have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
    have hbad : Q.real {ω | ∃ k ≤ e, √(ℓ : ℝ) ≤
        |∑ j ∈ Finset.range k, X (c + r * ℓ + j) ω|} ≤ e / ℓ := by
      rw [le_div_iff₀ hℓ', mul_comm]; exact hk
    have hsub2 : (Z r ⁻¹' A r)ᶜ ⊆ {ω | ∃ k ≤ e, √(ℓ : ℝ) ≤
        |∑ j ∈ Finset.range k, X (c + r * ℓ + j) ω|} := by
      intro ω hω
      simp only [mem_compl_iff, mem_preimage, hA, lt_irrefl, ite_false, mem_Ici, not_le,
        hZeq r ω, hLr] at hω
      refine ⟨e, le_rfl, ?_⟩
      rw [abs_of_neg (by linarith [Real.sqrt_nonneg (ℓ : ℝ)])]
      linarith
    have hmeas : MeasurableSet (Z r ⁻¹' A r) := (hZm r) (hAm r)
    have hc := measureReal_compl hmeas (μ := Q)
    rw [probReal_univ] at hc
    have := measureReal_mono hsub2 (μ := Q)
    linarith
  -- the event `E` forces a large sum
  have hEsub : E ⊆ {ω | (r * b - 1) * √(ℓ : ℝ) ≤
      ∑ j ∈ Finset.range (r * ℓ + e), X (c + j) ω} := by
    intro ω hω
    simp only [hE, mem_iInter, mem_preimage, Finset.mem_range] at hω
    simp only [mem_ofPred_eq]
    rw [Finset.sum_range_add, lil_sum_range_mul_eq (fun j => X (c + j) ω)]
    have hi : ∀ i < r, b * √(ℓ : ℝ) < ∑ j ∈ Finset.range ℓ, X (c + (i * ℓ + j)) ω := by
      intro i hir
      have := hω i (by omega)
      simp only [hA, hir, ite_true, mem_Ioi, hZeq i ω, hLle i hir] at this
      simpa only [add_assoc] using this
    have hr : -√(ℓ : ℝ) ≤ ∑ j ∈ Finset.range e, X (c + (r * ℓ + j)) ω := by
      have := hω r (by omega)
      simp only [hA, lt_irrefl, ite_false, mem_Ici, hZeq r ω, hLr] at this
      simpa only [add_assoc] using this
    have hsum : ∑ i ∈ Finset.range r, b * √(ℓ : ℝ) ≤
        ∑ i ∈ Finset.range r, ∑ j ∈ Finset.range ℓ, X (c + (i * ℓ + j)) ω :=
      Finset.sum_le_sum fun i hi' => (hi i (Finset.mem_range.1 hi')).le
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    nlinarith
  -- combine
  have hP0 : 0 ≤ Q.real {ω | b * √(ℓ : ℝ) < ∑ j ∈ Finset.range ℓ, X j ω} := measureReal_nonneg
  calc Q.real {ω | b * √(ℓ : ℝ) < ∑ j ∈ Finset.range ℓ, X j ω} ^ r * (1 - e / ℓ)
      ≤ Q.real {ω | b * √(ℓ : ℝ) < ∑ j ∈ Finset.range ℓ, X j ω} ^ r *
          Q.real (Z r ⁻¹' A r) := mul_le_mul_of_nonneg_left hrem (pow_nonneg hP0 r)
    _ = Q.real E := by
        rw [hprod, Finset.prod_range_succ, Finset.prod_congr rfl fun i hi =>
          hsub i (Finset.mem_range.1 hi), Finset.prod_const, Finset.card_range]
    _ ≤ _ := measureReal_mono hEsub

/-! ### Choice of the constants -/

/-- The geometric ratio of the lower half: for `0 < ε ≤ 1` there is an integer `m ≥ 2` with
`(1 − ε/2)² m/(m − 1) < 1` and `2/√m ≤ ε/2`. -/
theorem exists_lil_lower_ratio {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ m : ℕ, 2 ≤ m ∧ (1 - ε / 2) ^ 2 * ((m : ℝ) / ((m : ℝ) - 1)) < 1 ∧
      2 / √(m : ℝ) ≤ ε / 2 := by
  refine ⟨⌈16 / ε ^ 2⌉₊ + 2, by omega, ?_, ?_⟩
  · set m : ℝ := ((⌈16 / ε ^ 2⌉₊ + 2 : ℕ) : ℝ) with hm
    have hm1 : 16 / ε ^ 2 ≤ m - 2 := by
      have := Nat.le_ceil (16 / ε ^ 2); rw [hm]; push_cast; linarith
    have hm2 : 16 ≤ m * ε ^ 2 := by
      rw [div_le_iff₀ (by positivity)] at hm1; nlinarith [sq_nonneg ε]
    have hm3 : (1 : ℝ) < m - 1 := by
      have : 0 < 16 / ε ^ 2 := by positivity
      linarith
    rw [mul_div_assoc', div_lt_one (by linarith)]
    have h4 : m * ε ^ 2 ≤ m * ε := by
      have : ε ^ 2 ≤ ε := by nlinarith
      exact mul_le_mul_of_nonneg_left this (by linarith)
    nlinarith
  · set m : ℝ := ((⌈16 / ε ^ 2⌉₊ + 2 : ℕ) : ℝ) with hm
    have hm1 : 16 / ε ^ 2 ≤ m := by
      have := Nat.le_ceil (16 / ε ^ 2); rw [hm]; push_cast; linarith
    have hm0 : 0 < m := by positivity
    have hs : 0 < √m := Real.sqrt_pos.2 hm0
    rw [div_le_iff₀ hs]
    have h2 : 4 / ε ≤ √m := by
      rw [show 4 / ε = √((4 / ε) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
      apply Real.sqrt_le_sqrt
      rw [div_pow]; norm_num; exact hm1
    have := mul_le_mul_of_nonneg_left h2 (show 0 ≤ ε / 2 by positivity)
    have e : ε / 2 * (4 / ε) = 2 := by field_simp; norm_num
    linarith

/-- The sub-block level of the lower half: for `γ² < 1` there is an integer `A ≥ 1` with
`γ² ((A + 3)² + 4)/A² < 1`. -/
theorem exists_lil_lower_level {γ2 : ℝ} (hγ : γ2 < 1) :
    ∃ A : ℕ, 1 ≤ A ∧ γ2 * (((A : ℝ) + 3) ^ 2 + 4) / (A : ℝ) ^ 2 < 1 := by
  have ht : Tendsto (fun A : ℕ => γ2 * ((1 + 3 * (1 / (A : ℝ))) ^ 2 + 4 * (1 / (A : ℝ)) ^ 2))
      atTop (𝓝 (γ2 * ((1 + 3 * 0) ^ 2 + 4 * 0 ^ 2))) :=
    tendsto_const_nhds.mul (((tendsto_const_nhds.add
      (tendsto_one_div_atTop_nhds_zero_nat.const_mul 3)).pow 2).add
      ((tendsto_one_div_atTop_nhds_zero_nat.pow 2).const_mul 4))
  norm_num at ht
  obtain ⟨A, hA⟩ := ((ht.eventually (gt_mem_nhds hγ)).and (eventually_ge_atTop 1)).exists
  refine ⟨A, hA.2, ?_⟩
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA.2
  have e : γ2 * (((A : ℝ) + 3) ^ 2 + 4) / (A : ℝ) ^ 2 =
      γ2 * ((1 + 3 * (1 / (A : ℝ))) ^ 2 + 4 * (1 / (A : ℝ)) ^ 2) := by
    field_simp
  rw [e]
  have := hA.1
  simpa using this

/-- The deterministic block inequality: if `N = r ℓ + e` with `e < r`, `1 ≤ r`, `1 ≤ A ≤ ℓ` and
`T² ≤ A² N r` with `T ≥ 0`, then `T ≤ (r (A + 2) − 1) √ℓ`. -/
theorem le_block_level {T A : ℝ} (hT : 0 ≤ T) (hA : 1 ≤ A) {r ℓ e : ℕ} (her : e < r)
    (hr : 1 ≤ r) (hAℓ : A ≤ ℓ) (hTN : T ^ 2 ≤ A ^ 2 * ((r * ℓ + e : ℕ) : ℝ) * r) :
    T ≤ (r * (A + 2) - 1) * √(ℓ : ℝ) := by
  have hℓ : (1 : ℝ) ≤ ℓ := hA.trans hAℓ
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have her' : (e : ℝ) + 1 ≤ r := by exact_mod_cast her
  -- `N ≤ r (ℓ + 1) ≤ r ℓ (1 + 1/A)²`
  have hN : ((r * ℓ + e : ℕ) : ℝ) ≤ r * ℓ * (1 + 1 / A) ^ 2 := by
    push_cast
    have h1 : (ℓ : ℝ) + 1 ≤ ℓ * (1 + 1 / A) ^ 2 := by
      have h2 : (1 : ℝ) ≤ ℓ * (1 / A) := by
        rw [mul_one_div, le_div_iff₀ (by linarith)]; linarith
      have h3 : 0 ≤ (ℓ : ℝ) * (1 / A) ^ 2 := by positivity
      nlinarith
    nlinarith
  have hsq : T ^ 2 ≤ (r * (A + 1) * √(ℓ : ℝ)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith)]
    have h4 : A ^ 2 * ((r * ℓ + e : ℕ) : ℝ) * r ≤ A ^ 2 * (r * ℓ * (1 + 1 / A) ^ 2) * r := by
      have := mul_le_mul_of_nonneg_left hN (sq_nonneg A)
      nlinarith
    have e1 : A ^ 2 * (r * ℓ * (1 + 1 / A) ^ 2) * r = r ^ 2 * (A + 1) ^ 2 * ℓ := by
      field_simp
    nlinarith
  have h5 : T ≤ r * (A + 1) * √(ℓ : ℝ) :=
    (pow_le_pow_iff_left₀ hT (by positivity) two_ne_zero).1 hsq
  have h6 : r * (A + 1) ≤ r * (A + 2) - 1 := by nlinarith
  have := mul_le_mul_of_nonneg_right h6 (Real.sqrt_nonneg (ℓ : ℝ))
  linarith

/-- Exponential growth beats quadratic growth: for `m ≥ 2` and any `C`, eventually
`C (k + 1)² ≤ mᵏ`. -/
theorem lil_eventually_mul_sq_le_pow {m : ℕ} (hm : 2 ≤ m) (C : ℝ) :
    ∀ᶠ k : ℕ in atTop, C * ((k : ℝ) + 1) ^ 2 ≤ (m : ℝ) ^ k := by
  have hm1 : (1 : ℝ) < m := by exact_mod_cast hm
  have ht := tendsto_pow_const_div_const_pow_of_one_lt 2 hm1
  have hC : 0 < 4 * (|C| + 1) := by positivity
  filter_upwards [ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (4 * (|C| + 1)) by positivity)),
    eventually_ge_atTop 1] with k hk hk1
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hpos : (0 : ℝ) < (m : ℝ) ^ k := by positivity
  rw [div_lt_div_iff₀ hpos hC, one_mul] at hk
  have h1 : C * ((k : ℝ) + 1) ^ 2 ≤ (|C| + 1) * (4 * (k : ℝ) ^ 2) := by
    have h2 : ((k : ℝ) + 1) ^ 2 ≤ 4 * (k : ℝ) ^ 2 := by nlinarith
    have h3 : C ≤ |C| + 1 := by have := le_abs_self C; linarith
    have h4 : 0 ≤ ((k : ℝ) + 1) ^ 2 := sq_nonneg _
    calc C * ((k : ℝ) + 1) ^ 2 ≤ (|C| + 1) * ((k : ℝ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_right h3 h4
      _ ≤ (|C| + 1) * (4 * (k : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
  nlinarith

/-! ### The block estimate of the lower half -/

/-- **The block estimate of the lower half of the LIL**: for i.i.d. `Xⱼ` with mean `0` and
variance `1`, integers `m ≥ 2`, `A ≥ 1`, `b = A + 2`, `κ = (b + 1)²/2 + 2`, if
`P(S_ℓ > b √ℓ) ≥ e^{−κ}` for `ℓ ≥ ℓ₀`, then for every `k` with `log m^{k+1} ≥ 3` and
`C (k + 1)² ≤ mᵏ` (`C = (4m + 1)(ℓ₀ + A + 1 + 2(4m + 1))`) the block `[mᵏ, mᵏ⁺¹)` has
`P(Σ_{mᵏ ≤ j < mᵏ⁺¹} Xⱼ ≥ (1 − ε/2) √(2 M log log M)) ≥ (e^{−κ}/2) (log M)^{−p'}`, `M = mᵏ⁺¹`,
`p' = 2γ²κ/A²`, `γ² = (1 − ε/2)² m/(m − 1)`. -/
theorem lil_lower_block_estimate {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {X : ℕ → Ω → ℝ} (hind : iIndepFun X Q)
    (hm : ∀ j, Measurable (X j)) (hident : ∀ j, IdentDistrib (X j) (X 0) Q Q)
    (hL2 : MemLp (X 0) 2 Q) (h0 : ∫ ω, X 0 ω ∂Q = 0) (h1 : ∫ ω, X 0 ω ^ 2 ∂Q = 1) {ε : ℝ}
    (hε1 : ε ≤ 1) {m A ℓ₀ : ℕ} (hm2 : 2 ≤ m) (hA1 : 1 ≤ A)
    (hγ : (1 - ε / 2) ^ 2 * ((m : ℝ) / ((m : ℝ) - 1)) ≤ 1)
    (hP1 : ∀ ℓ ≥ ℓ₀, Real.exp (-((((A : ℝ) + 2) + 1) ^ 2 / 2 + 2)) ≤
      Q.real {ω | ((A : ℝ) + 2) * √(ℓ : ℝ) < ∑ j ∈ Finset.range ℓ, X j ω})
    {k : ℕ} (hk3 : 3 ≤ Real.log ((m : ℝ) ^ (k + 1)))
    (hkC : (4 * m + 1) * ((ℓ₀ + A + 1 : ℕ) + 2 * (4 * m + 1)) * ((k : ℝ) + 1) ^ 2 ≤
      (m : ℝ) ^ k) :
    Real.exp (-((((A : ℝ) + 2) + 1) ^ 2 / 2 + 2)) / 2 *
      Real.exp (-(2 * ((1 - ε / 2) ^ 2 * ((m : ℝ) / ((m : ℝ) - 1))) *
        ((((A : ℝ) + 2) + 1) ^ 2 / 2 + 2) / (A : ℝ) ^ 2 *
        Real.log (Real.log ((m : ℝ) ^ (k + 1))))) ≤
      Q.real {ω | (1 - ε / 2) * lilScale (m ^ (k + 1)) ≤
        ∑ j ∈ Finset.Ico (m ^ k) (m ^ (k + 1)), X j ω} := by
  set γ2 := (1 - ε / 2) ^ 2 * ((m : ℝ) / ((m : ℝ) - 1)) with hγ2
  set b : ℝ := A + 2 with hb
  set κ : ℝ := (b + 1) ^ 2 / 2 + 2 with hκ
  set p' : ℝ := 2 * γ2 * κ / (A : ℝ) ^ 2 with hp'def
  set Lstar : ℕ := ℓ₀ + A + 1 with hLstar
  have hA1' : (1 : ℝ) ≤ A := by exact_mod_cast hA1
  have hm1 : (1 : ℝ) < m := by exact_mod_cast hm2
  have hpow_le : m ^ k ≤ m ^ (k + 1) := Nat.pow_le_pow_right (by omega) (Nat.le_succ k)
  set N : ℕ := m ^ (k + 1) - m ^ k with hN
  set T : ℝ := (1 - ε / 2) * lilScale (m ^ (k + 1)) with hT
  set r : ℕ := ⌊T ^ 2 / ((A : ℝ) ^ 2 * N)⌋₊ + 1 with hr
  set ℓ : ℕ := N / r with hℓ
  set e : ℕ := N % r with he
  have hNcast : (N : ℝ) = (m : ℝ) ^ k * ((m : ℝ) - 1) := by
    rw [hN, Nat.cast_sub hpow_le]
    push_cast; ring
  have hNeq : r * ℓ + e = N := Nat.div_add_mod N r
  set M : ℕ := m ^ (k + 1) with hM
  have hMc : (M : ℝ) = (m : ℝ) ^ (k + 1) := by rw [hM]; push_cast; ring
  have hk3' : 3 ≤ Real.log (M : ℝ) := by rw [hMc]; exact hk3
  clear_value γ2 b κ p' Lstar N T r ℓ e M
  have hLL := one_le_loglog hk3'
  have hmk0 : (0 : ℝ) < (m : ℝ) ^ k := by positivity
  have hN0 : (0 : ℝ) < N := by rw [hNcast]; exact mul_pos hmk0 (by linarith)
  -- `T² /(A² N) = 2 γ² log log M`
  have hT2 : T ^ 2 = (1 - ε / 2) ^ 2 * (2 * M * Real.log (Real.log M)) := by
    rw [hT, mul_pow, lilScale_sq hk3']
  have hTN : T ^ 2 / ((A : ℝ) ^ 2 * N) = 2 * γ2 * Real.log (Real.log M) / (A : ℝ) ^ 2 := by
    rw [hT2, hNcast, hMc, hγ2]
    have : (m : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  have hTN0 : 0 ≤ T ^ 2 / ((A : ℝ) ^ 2 * N) := by positivity
  have hγ0 : 0 ≤ γ2 := by
    rw [hγ2]
    have : (0 : ℝ) < m - 1 := by linarith
    positivity
  -- `r ≤ (4m + 1)(k + 1)`
  have hlogM : Real.log (Real.log M) ≤ ((k : ℝ) + 1) * m := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < Real.log (M : ℝ) by linarith)
    have h2 : Real.log (M : ℝ) = ((k : ℝ) + 1) * Real.log m := by
      rw [hMc, Real.log_pow]; push_cast; ring
    have h3 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < m by linarith)
    have h4 : ((k : ℝ) + 1) * Real.log m ≤ ((k : ℝ) + 1) * m :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hrR : r ≤ (4 * m + 1) * (k + 1) := by
    have h1 : T ^ 2 / ((A : ℝ) ^ 2 * N) ≤ 4 * (((k : ℝ) + 1) * m) := by
      rw [hTN, div_le_iff₀ (by positivity)]
      have hL0 : 0 ≤ Real.log (Real.log M) := by linarith
      have hkm : 0 ≤ ((k : ℝ) + 1) * m := by positivity
      calc 2 * γ2 * Real.log (Real.log M) ≤ 2 * 1 * Real.log (Real.log M) :=
            mul_le_mul_of_nonneg_right (by linarith) hL0
        _ ≤ 2 * (((k : ℝ) + 1) * m) := by linarith
        _ ≤ 4 * (((k : ℝ) + 1) * m) * (A : ℝ) ^ 2 := by
            have : (1 : ℝ) ≤ (A : ℝ) ^ 2 := by nlinarith
            nlinarith
    have h2 : ⌊T ^ 2 / ((A : ℝ) ^ 2 * N)⌋₊ ≤ 4 * ((k + 1) * m) := by
      apply Nat.floor_le_of_le; push_cast; linarith
    have e1 : (4 * m + 1) * (k + 1) = 4 * ((k + 1) * m) + (k + 1) := by ring
    rw [hr, e1]
    omega
  have hr1 : 1 ≤ r := by rw [hr]; omega
  -- `ℓ ≥ L* + 2 (4m + 1)(k + 1)`
  have hNk : m ^ k ≤ N := by
    have hM' : M = m ^ k * m := by rw [hM, pow_succ]
    have : m ^ k * 2 ≤ m ^ k * m := Nat.mul_le_mul_left _ hm2
    omega
  have hbig : (4 * m + 1) * (k + 1) * (Lstar + 2 * ((4 * m + 1) * (k + 1))) ≤ m ^ k := by
    have hkC' : (4 * m + 1) * (Lstar + 2 * (4 * m + 1)) * (k + 1) ^ 2 ≤ m ^ k := by
      exact_mod_cast hkC
    have hLK : Lstar ≤ Lstar * (k + 1) := Nat.le_mul_of_pos_right _ (by omega)
    calc (4 * m + 1) * (k + 1) * (Lstar + 2 * ((4 * m + 1) * (k + 1)))
        ≤ (4 * m + 1) * (k + 1) * (Lstar * (k + 1) + 2 * ((4 * m + 1) * (k + 1))) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add_right hLK _)
      _ = (4 * m + 1) * (Lstar + 2 * (4 * m + 1)) * (k + 1) ^ 2 := by ring
      _ ≤ m ^ k := hkC'
  have hℓbig : Lstar + 2 * ((4 * m + 1) * (k + 1)) ≤ ℓ := by
    calc Lstar + 2 * ((4 * m + 1) * (k + 1))
        ≤ N / ((4 * m + 1) * (k + 1)) := by
          rw [Nat.le_div_iff_mul_le (by positivity)]
          calc (Lstar + 2 * ((4 * m + 1) * (k + 1))) * ((4 * m + 1) * (k + 1))
              = (4 * m + 1) * (k + 1) * (Lstar + 2 * ((4 * m + 1) * (k + 1))) := by ring
            _ ≤ m ^ k := hbig
            _ ≤ N := hNk
      _ ≤ N / r := Nat.div_le_div_left hrR (by omega)
      _ = ℓ := hℓ.symm
  have hℓ₀ : ℓ₀ ≤ ℓ := by omega
  have hAℓ : (A : ℝ) ≤ ℓ := by exact_mod_cast (show A ≤ ℓ by omega)
  have h2r : 2 * r ≤ ℓ := by omega
  have hℓ0 : 0 < ℓ := by omega
  have her : e < r := by rw [he]; exact Nat.mod_lt _ (by omega)
  have hsubset : {ω | (r * b - 1) * √(ℓ : ℝ) ≤
      ∑ j ∈ Finset.range (r * ℓ + e), X (m ^ k + j) ω} ⊆
      {ω | T ≤ ∑ j ∈ Finset.Ico (m ^ k) M, X j ω} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    rw [Finset.sum_Ico_eq_sum_range, ← hN, ← hNeq]
    have hT0 : 0 ≤ T :=
      le_of_le_of_eq (mul_nonneg (by linarith only [hε1]) (lilScale_nonneg _)) hT.symm
    have hTle : T ≤ (r * ((A : ℝ) + 2) - 1) * √(ℓ : ℝ) := by
      refine le_block_level hT0 hA1' her hr1 hAℓ ?_
      have hfl : T ^ 2 / ((A : ℝ) ^ 2 * N) ≤ r := by
        rw [hr]; push_cast
        exact (Nat.lt_floor_add_one _).le
      rw [hNeq]
      rw [div_le_iff₀ (by positivity)] at hfl
      linarith only [hfl]
    rw [hb] at hω
    linarith only [hω, hTle]
  have hhalf : (1 : ℝ) / 2 ≤ 1 - e / ℓ := by
    have : (e : ℝ) / ℓ ≤ 1 / 2 := by
      rw [div_le_iff₀ (by exact_mod_cast hℓ0)]
      have h2e : (2 * e : ℝ) ≤ ℓ := by exact_mod_cast (show 2 * e ≤ ℓ by omega)
      linarith only [h2e]
    linarith only [this]
  have hr_le : (r : ℝ) ≤ T ^ 2 / ((A : ℝ) ^ 2 * N) + 1 := by
    rw [hr]; push_cast
    have := Nat.floor_le hTN0
    linarith only [this]
  have hexp_r : Real.exp (-κ) * Real.exp (-(p' * Real.log (Real.log M))) ≤
      Real.exp (-κ * r) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have hκ0 : 0 ≤ κ := le_of_le_of_eq (by positivity) hκ.symm
    have h7 : κ * r ≤ κ * (T ^ 2 / ((A : ℝ) ^ 2 * N) + 1) :=
      mul_le_mul_of_nonneg_left hr_le hκ0
    rw [hTN] at h7
    have e2 : κ * (2 * γ2 * Real.log (Real.log M) / (A : ℝ) ^ 2 + 1) =
        p' * Real.log (Real.log M) + κ := by rw [hp'def]; ring
    linarith only [h7, e2]
  -- the block bound
  have hblk := block_lower_bound hind hm hident hL2 h0 h1 (m ^ k) r ℓ e b hℓ0
  have hP := hP1 ℓ hℓ₀
  have hpowr : Real.exp (-κ * r) ≤
      Q.real {ω | b * √(ℓ : ℝ) < ∑ j ∈ Finset.range ℓ, X j ω} ^ r := by
    rw [show -κ * r = r * (-κ) by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le hP _
  have hfin := (mul_le_mul hpowr hhalf (by norm_num) (pow_nonneg measureReal_nonneg _)).trans
    (hblk.trans (measureReal_mono hsubset))
  rw [← hMc]
  have hpos := Real.exp_pos (-κ * r)
  have e3 : Real.exp (-κ) / 2 * Real.exp (-(p' * Real.log (Real.log M))) =
      Real.exp (-κ) * Real.exp (-(p' * Real.log (Real.log M))) * (1 / 2) := by ring
  rw [e3]
  calc Real.exp (-κ) * Real.exp (-(p' * Real.log (Real.log M))) * (1 / 2)
      ≤ Real.exp (-κ * r) * (1 / 2) := mul_le_mul_of_nonneg_right hexp_r (by norm_num)
    _ ≤ _ := hfin

/-! ### The lower half of the LIL -/

/-- **The lower half of the Hartman–Wintner LIL**, normalised: for i.i.d. `Xⱼ` with mean `0`
and variance `1` and `0 < ε ≤ 1`, almost surely `Sₙ ≥ (1 − ε) √(2 n log log n)` for infinitely
many `n`. -/
theorem lil_lower_normalized {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {X : ℕ → Ω → ℝ} (hind : iIndepFun X Q)
    (hm : ∀ j, Measurable (X j)) (hident : ∀ j, IdentDistrib (X j) (X 0) Q Q)
    (hL2 : MemLp (X 0) 2 Q) (h0 : ∫ ω, X 0 ω ∂Q = 0) (h1 : ∫ ω, X 0 ω ^ 2 ∂Q = 1) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᵐ ω ∂Q, ∃ᶠ n in atTop, (1 - ε) * lilScale n ≤ ∑ j ∈ Finset.range n, X j ω := by
  obtain ⟨m, hm2, hγ, hmε⟩ := exists_lil_lower_ratio hε hε1
  set γ2 := (1 - ε / 2) ^ 2 * ((m : ℝ) / ((m : ℝ) - 1)) with hγ2
  obtain ⟨A, hA1, hp'⟩ := exists_lil_lower_level hγ
  have hA1' : (1 : ℝ) ≤ A := by exact_mod_cast hA1
  have hm1 : (1 : ℝ) < m := by exact_mod_cast hm2
  set b : ℝ := A + 2 with hb
  set κ : ℝ := (b + 1) ^ 2 / 2 + 2 with hκ
  set p' : ℝ := 2 * γ2 * κ / (A : ℝ) ^ 2 with hp'def
  have hp'1 : p' ≤ 1 := by
    have e : p' = γ2 * (((A : ℝ) + 3) ^ 2 + 4) / (A : ℝ) ^ 2 := by rw [hp'def, hκ, hb]; ring
    rw [e]; exact hp'.le
  -- the CLT for the sub-blocks
  have hb0 : 0 ≤ b := by positivity
  have hG := lil_gaussianReal_Ioi_ge hb0
  set g := gaussianReal 0 1 (Ioi b) with hg
  have hc0 : 0 < Real.exp (-((b + 1) ^ 2 / 2)) / √(2 * Real.pi) := by positivity
  have hgpos : g ≠ 0 := by
    intro h0'
    have : (gaussianReal 0 1).real (Ioi b) = 0 := by rw [measureReal_def, ← hg, h0']; rfl
    linarith
  have hq : g / 2 < g := ENNReal.half_lt_self hgpos (measure_ne_top _ _)
  obtain ⟨ℓ₀, hℓ₀⟩ := eventually_atTop.1 (lil_eventually_lt_measure_clt hind hm hident h0 h1 b hq)
  have hP1 : ∀ ℓ ≥ ℓ₀, Real.exp (-κ) ≤
      Q.real {ω | b * √(ℓ : ℝ) < ∑ j ∈ Finset.range ℓ, X j ω} := by
    intro ℓ hℓ
    have h2 : (g / 2).toReal ≤ Q.real {ω | b * √(ℓ : ℝ) < ∑ j ∈ Finset.range ℓ, X j ω} :=
      ENNReal.toReal_mono (measure_ne_top _ _) (hℓ₀ ℓ hℓ).le
    rw [ENNReal.toReal_div, ENNReal.toReal_ofNat] at h2
    have h3 : Real.exp (-κ) ≤ Real.exp (-((b + 1) ^ 2 / 2)) / √(2 * Real.pi) / 2 := by
      have e1 : Real.exp (-κ) = Real.exp (-((b + 1) ^ 2 / 2)) * Real.exp (-2) := by
        rw [← Real.exp_add, hκ]; ring_nf
      have h4 := lil_two_mul_sqrt_two_pi_le_exp_two
      have h5 : Real.exp (-2) ≤ 1 / (2 * √(2 * Real.pi)) := by
        rw [Real.exp_neg, ← one_div]
        exact one_div_le_one_div_of_le (by positivity) h4
      rw [e1, div_div, mul_comm (√(2 * Real.pi)) 2]
      calc Real.exp (-((b + 1) ^ 2 / 2)) * Real.exp (-2)
          ≤ Real.exp (-((b + 1) ^ 2 / 2)) * (1 / (2 * √(2 * Real.pi))) :=
            mul_le_mul_of_nonneg_left h5 (Real.exp_pos _).le
        _ = Real.exp (-((b + 1) ^ 2 / 2)) / (2 * √(2 * Real.pi)) := by rw [mul_one_div]
    have h6 : (gaussianReal 0 1).real (Ioi b) = g.toReal := rfl
    linarith
  -- the independent block events
  set Z : ℕ → Ω → ℝ := fun k ω => ∑ j ∈ Finset.Ico (m ^ k) (m ^ (k + 1)), X j ω with hZ
  set T : ℕ → ℝ := fun k => (1 - ε / 2) * lilScale (m ^ (k + 1)) with hT
  set G : ℕ → Set Ω := fun k => Z k ⁻¹' Ici (T k) with hG
  have hpowmono : ∀ i j, i ≤ j → m ^ i ≤ m ^ j := fun i j h =>
    Nat.pow_le_pow_right (by omega) h
  have hdisj : Pairwise (Function.onFun Disjoint
      fun k => ((Finset.Ico (m ^ k) (m ^ (k + 1)) : Finset ℕ) : Set ℕ)) := by
    have key : ∀ i i', i < i' → Disjoint ((Finset.Ico (m ^ i) (m ^ (i + 1)) : Finset ℕ) : Set ℕ)
        ((Finset.Ico (m ^ i') (m ^ (i' + 1)) : Finset ℕ) : Set ℕ) := fun i i' h => by
      simp only [Finset.coe_Ico]
      rw [Set.Ico_disjoint_Ico]
      have h1 := hpowmono (i + 1) i' h
      have h2 := hpowmono i' (i' + 1) (Nat.le_succ i')
      omega
    intro i i' hii'
    rcases lt_or_gt_of_ne hii' with h | h
    · exact key i i' h
    · exact (key i' i h).symm
  have hZm : ∀ k, Measurable (Z k) := fun k => Finset.measurable_sum _ fun j _ => hm j
  have hGind : iIndepSet G Q :=
    lil_iIndepSet_preimage (lil_iIndepFun_blockSum hind hm hdisj) fun k => measurableSet_Ici
  have hGm : ∀ k, MeasurableSet (G k) := fun k => hZm k measurableSet_Ici
  -- the probabilities of the block events diverge
  set Cst : ℝ := (4 * m + 1) * ((ℓ₀ + A + 1 : ℕ) + 2 * (4 * m + 1)) with hCst
  have hlogt : Tendsto (fun k : ℕ => Real.log ((m : ℝ) ^ (k + 1))) atTop atTop := by
    have : (fun k : ℕ => Real.log ((m : ℝ) ^ (k + 1))) =
        fun k : ℕ => ((k : ℝ) + 1) * Real.log m := by
      ext k; rw [Real.log_pow]; push_cast; ring
    rw [this]
    exact (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_mul_const
      (Real.log_pos hm1)
  have hprob : ∀ᶠ k in atTop, Real.exp (-κ) / 2 *
      Real.exp (-(p' * Real.log (Real.log ((m : ℝ) ^ (k + 1))))) ≤ Q.real (G k) := by
    filter_upwards [hlogt.eventually_ge_atTop 3, lil_eventually_mul_sq_le_pow hm2 Cst]
      with k hk3 hkC
    exact lil_lower_block_estimate hind hm hident hL2 h0 h1 hε1 hm2 hA1 hγ.le hP1 hk3 hkC
  have hC0 : 0 < Real.exp (-κ) / 2 := by positivity
  have hdiv : ∑' k, Q (G k) = ∞ := by
    by_contra hne
    have hs : Summable fun k => Q.real (G k) := ENNReal.summable_toReal hne
    have hs2 : Summable fun k => Real.exp (-κ) / 2 *
        Real.exp (-(p' * Real.log (Real.log ((m : ℝ) ^ (k + 1))))) := by
      refine hs.of_norm_bounded_eventually_nat ?_
      filter_upwards [hprob] with k hk
      rwa [Real.norm_eq_abs, abs_of_pos (mul_pos hC0 (Real.exp_pos _))]
    exact not_summable_exp_neg_mul_loglog_pow hm2 hp'1 hC0 ((summable_nat_add_iff 1).1 hs2)
  have hlim := measure_limsup_eq_one hGm hGind hdiv
  have hae : ∀ᵐ ω ∂Q, ∃ᶠ k in atTop, ω ∈ G k := by
    have hm' : MeasurableSet (limsup G atTop) := MeasurableSet.measurableSet_limsup hGm
    have h2 : ∀ᵐ ω ∂Q, ω ∈ limsup G atTop := by
      rw [ae_iff]
      exact (prob_compl_eq_zero_iff hm').2 hlim
    filter_upwards [h2] with ω hω
    exact mem_limsup_iff_frequently_mem.1 hω
  -- the upper half for `−X` controls the start of the blocks
  have hneg := lil_upper (X := fun j ω => -X j ω)
    (hind.comp (fun _ x => -x) fun _ => measurable_neg) (fun j => (hm j).neg)
    (fun j => (hident j).comp measurable_neg) hL2.neg
    (by rw [integral_neg, h0, neg_zero]) one_pos
  have hsq : √(∫ ω, (-X 0 ω) ^ 2 ∂Q) = 1 := by
    simp_rw [neg_sq]; rw [h1, Real.sqrt_one]
  simp only [hsq] at hneg
  filter_upwards [hae, hneg] with ω hωG hωU
  rw [Filter.frequently_atTop]
  intro n₀
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 hωU
  have hlogk : Tendsto (fun k : ℕ => Real.log ((m ^ k : ℕ) : ℝ)) atTop atTop := by
    have : (fun k : ℕ => Real.log ((m ^ k : ℕ) : ℝ)) = fun k : ℕ => (k : ℝ) * Real.log m := by
      ext k; push_cast; rw [Real.log_pow]
    rw [this]
    exact tendsto_natCast_atTop_atTop.atTop_mul_const (Real.log_pos hm1)
  obtain ⟨k, hkG, hk⟩ := (hωG.and_eventually ((eventually_ge_atTop (n₀ + N1)).and
    (hlogk.eventually_ge_atTop 3))).exists
  have hk1 : n₀ + N1 ≤ k := hk.1
  have hk3 : 3 ≤ Real.log ((m ^ k : ℕ) : ℝ) := hk.2
  have hk3' : 3 ≤ Real.log ((m ^ (k + 1) : ℕ) : ℝ) :=
    lil_three_le_log_of_le hk3 (hpowmono k (k + 1) (Nat.le_succ k))
  have hkm : k < m ^ k := Nat.lt_pow_self (by omega)
  refine ⟨m ^ (k + 1), ?_, ?_⟩
  · have := Nat.lt_pow_self (n := k + 1) (show 1 < m by omega)
    omega
  have hsplit : ∑ j ∈ Finset.range (m ^ (k + 1)), X j ω =
      ∑ j ∈ Finset.range (m ^ k), X j ω + Z k ω :=
    (Finset.sum_range_add_sum_Ico _ (hpowmono k (k + 1) (Nat.le_succ k))).symm
  have hU : ∑ j ∈ Finset.range (m ^ k), -X j ω ≤ (1 + 1) * lilScale (m ^ k) :=
    hN1 (m ^ k) (by omega)
  rw [Finset.sum_neg_distrib] at hU
  have hGk : T k ≤ Z k ω := hkG
  -- `√m lilScale mᵏ ≤ lilScale mᵏ⁺¹`
  have hlil : √(m : ℝ) * lilScale (m ^ k) ≤ lilScale (m ^ (k + 1)) := by
    have h1' := lilScale_sq hk3
    have h2' := lilScale_sq hk3'
    have hll : Real.log (Real.log ((m ^ k : ℕ) : ℝ)) ≤
        Real.log (Real.log ((m ^ (k + 1) : ℕ) : ℝ)) := by
      have hp0 : (0 : ℝ) < ((m ^ k : ℕ) : ℝ) := by exact_mod_cast pow_pos (show 0 < m by omega) k
      exact Real.log_le_log (by linarith) (Real.log_le_log hp0
        (by exact_mod_cast hpowmono k (k + 1) (Nat.le_succ k)))
    have hsq2 : (√(m : ℝ) * lilScale (m ^ k)) ^ 2 ≤ lilScale (m ^ (k + 1)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), h1', h2']
      have e1 : ((m ^ (k + 1) : ℕ) : ℝ) = m * ((m ^ k : ℕ) : ℝ) := by push_cast; ring
      have hp1 : (0 : ℝ) ≤ 2 * (m * ((m ^ k : ℕ) : ℝ)) := by positivity
      calc (m : ℝ) * (2 * ((m ^ k : ℕ) : ℝ) * Real.log (Real.log ((m ^ k : ℕ) : ℝ)))
          = 2 * (m * ((m ^ k : ℕ) : ℝ)) * Real.log (Real.log ((m ^ k : ℕ) : ℝ)) := by ring
        _ ≤ 2 * (m * ((m ^ k : ℕ) : ℝ)) * Real.log (Real.log ((m ^ (k + 1) : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hll hp1
        _ = 2 * ((m ^ (k + 1) : ℕ) : ℝ) * Real.log (Real.log ((m ^ (k + 1) : ℕ) : ℝ)) := by
            rw [e1]
    exact (pow_le_pow_iff_left₀ (mul_nonneg (Real.sqrt_nonneg _) (lilScale_nonneg _))
      (lilScale_nonneg _) two_ne_zero).1 hsq2
  have hsm : 0 < √(m : ℝ) := Real.sqrt_pos.2 (by linarith)
  have h2lil : 2 * lilScale (m ^ k) ≤ ε / 2 * lilScale (m ^ (k + 1)) := by
    have e2 : 2 * lilScale (m ^ k) = 2 / √(m : ℝ) * (√(m : ℝ) * lilScale (m ^ k)) := by
      field_simp
    rw [e2]
    calc 2 / √(m : ℝ) * (√(m : ℝ) * lilScale (m ^ k))
        ≤ 2 / √(m : ℝ) * lilScale (m ^ (k + 1)) :=
          mul_le_mul_of_nonneg_left hlil (by positivity)
      _ ≤ ε / 2 * lilScale (m ^ (k + 1)) :=
          mul_le_mul_of_nonneg_right hmε (lilScale_nonneg _)
  rw [hsplit]
  simp only [hT] at hGk
  linarith

end RQMCMarkov.MarkovDriving

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The law of the iterated logarithm for i.i.d. sequences (Hartman–Wintner)

Copied from the `StochasticStability/LimitTheorems` project (module `LimitTheorems.IIDLIL`),
with the namespace renamed `MeynTweedie.LimitTheorems` → `RQMCMarkov.MarkovDriving` and the
generic lemma names prefixed `lil_` to avoid clashes; used by `MCRate` for the MC baseline.

The LIL of MT p. 422: a real sequence `sₙ` obeys the LIL with constant `γ ≥ 0` when the limit
superior of `sₙ/√(2 n log log n)` is `γ` and the limit inferior is `−γ`. It is stated here in the
`ε`-form, which needs no boundedness side conditions (`LILBound`, `HasLIL`): for every `ε > 0`,
eventually `sₙ ≤ (γ + ε) √(2 n log log n)` and frequently `sₙ ≥ (γ − ε) √(2 n log log n)`, and the
same for `−sₙ`. The book normalises by `√(2 γ² n log log n)` and asks the limits `±1`, which is the
same statement when `γ > 0`.

* **The Hartman–Wintner LIL** (`hasLIL_iid`): for i.i.d. centred `Xⱼ ∈ L²` with `σ² = E[X₀²]`,
  almost surely `Sₙ = Σ_{j<n} Xⱼ` obeys the LIL with constant `σ` (including `σ = 0`). This is the
  i.i.d. LIL that MT uses (via the cycle sums) for Theorems 17.2.2 and 17.3.6.
* `lilBound_iid`: one half, `LILBound S σ` almost surely.
* `HasLIL.limsup_eq`, `HasLIL.liminf_eq`: the `Filter.limsup`/`Filter.liminf` form of `HasLIL`;
  `limsup_liminf_iid`: almost surely `limsup Sₙ/√(2 n log log n) = σ` and `liminf = −σ`.

The upper half is `lil_upper` (`LILUpper`), the lower half `lil_lower_normalized` (`LILLower`).
-/

namespace RQMCMarkov.MarkovDriving

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

/-- One half of the LIL with constant `γ`: for every `ε > 0`, eventually
`sₙ ≤ (γ + ε) √(2 n log log n)`, and frequently `sₙ ≥ (γ − ε) √(2 n log log n)`. -/
def LILBound (s : ℕ → ℝ) (γ : ℝ) : Prop :=
  ∀ ε > 0, (∀ᶠ n in atTop, s n ≤ (γ + ε) * lilScale n) ∧
    ∃ᶠ n in atTop, (γ - ε) * lilScale n ≤ s n

/-- **The LIL** with constant `γ` (MT p. 422, in `ε`-form): `LILBound s γ` and
`LILBound (−s) γ`, that is `limsup sₙ/√(2 n log log n) = γ` and `liminf = −γ`. -/
def HasLIL (s : ℕ → ℝ) (γ : ℝ) : Prop :=
  LILBound s γ ∧ LILBound (fun n => -s n) γ

/-- `LILBound` follows from its instances along `ε = 1/(k + 1)`. -/
theorem lilBound_of_nat {s : ℕ → ℝ} {γ : ℝ}
    (h : ∀ k : ℕ, (∀ᶠ n in atTop, s n ≤ (γ + 1 / ((k : ℝ) + 1)) * lilScale n) ∧
      ∃ᶠ n in atTop, (γ - 1 / ((k : ℝ) + 1)) * lilScale n ≤ s n) :
    LILBound s γ := by
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨h1, h2⟩ := h k
  refine ⟨h1.mono fun n hn => hn.trans ?_, h2.mono fun n hn => le_trans ?_ hn⟩
  · exact mul_le_mul_of_nonneg_right (by linarith) (lilScale_nonneg n)
  · exact mul_le_mul_of_nonneg_right (by linarith) (lilScale_nonneg n)

/-- **One half of the Hartman–Wintner LIL**: for i.i.d. centred `Xⱼ ∈ L²` with
`σ = √(E[X₀²])`, almost surely `Sₙ = Σ_{j<n} Xⱼ` satisfies `LILBound S σ`. -/
theorem lilBound_iid {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {X : ℕ → Ω → ℝ} (hind : iIndepFun X Q) (hm : ∀ j, Measurable (X j))
    (hident : ∀ j, IdentDistrib (X j) (X 0) Q Q) (hL2 : MemLp (X 0) 2 Q)
    (h0 : ∫ ω, X 0 ω ∂Q = 0) :
    ∀ᵐ ω ∂Q, LILBound (fun n => ∑ j ∈ Finset.range n, X j ω) (√(∫ ω, X 0 ω ^ 2 ∂Q)) := by
  set σ := √(∫ ω, X 0 ω ^ 2 ∂Q) with hσ
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hσ2 : σ ^ 2 = ∫ ω, X 0 ω ^ 2 ∂Q := Real.sq_sqrt (integral_nonneg fun ω => sq_nonneg _)
  -- the upper halves for `X` and `−X`
  have hup : ∀ᵐ ω ∂Q, ∀ k : ℕ, ∀ᶠ n in atTop,
      ∑ j ∈ Finset.range n, X j ω ≤ (σ + 1 / ((k : ℝ) + 1)) * lilScale n :=
    ae_all_iff.2 fun k => lil_upper hind hm hident hL2 h0 (by positivity)
  have hind' : iIndepFun (fun j ω => -X j ω) Q := hind.comp (fun _ x => -x) fun _ => measurable_neg
  have hident' : ∀ j, IdentDistrib (fun ω => -X j ω) (fun ω => -X 0 ω) Q Q := fun j =>
    (hident j).comp measurable_neg
  have h0' : ∫ ω, -X 0 ω ∂Q = 0 := by rw [integral_neg, h0, neg_zero]
  have hsq : √(∫ ω, (-X 0 ω) ^ 2 ∂Q) = σ := by simp_rw [neg_sq]; exact hσ.symm
  have hupneg : ∀ᵐ ω ∂Q, ∀ k : ℕ, ∀ᶠ n in atTop,
      ∑ j ∈ Finset.range n, -X j ω ≤ (σ + 1 / ((k : ℝ) + 1)) * lilScale n := by
    refine ae_all_iff.2 fun k => ?_
    have h := lil_upper (X := fun j ω => -X j ω) hind' (fun j => (hm j).neg) hident' hL2.neg h0'
      (ε := 1 / ((k : ℝ) + 1)) (by positivity)
    rwa [hsq] at h
  rcases eq_or_lt_of_le hσ0 with hσz | hσpos
  · -- `σ = 0`: the upper half for `−X` gives the lower half
    filter_upwards [hup, hupneg] with ω hω1 hω2
    refine lilBound_of_nat fun k => ⟨hω1 k, ?_⟩
    refine ((hω2 k).mono fun n hn => ?_).frequently
    rw [Finset.sum_neg_distrib] at hn
    rw [← hσz] at hn ⊢
    have : (0 - 1 / ((k : ℝ) + 1)) * lilScale n = -((0 + 1 / ((k : ℝ) + 1)) * lilScale n) := by
      ring
    rw [this]
    linarith
  · -- `σ > 0`: the lower half for `X/σ`
    set Y : ℕ → Ω → ℝ := fun j ω => σ⁻¹ * X j ω with hY
    have hYind : iIndepFun Y Q :=
      hind.comp (fun _ x => σ⁻¹ * x) fun _ => measurable_id.const_mul σ⁻¹
    have hYm : ∀ j, Measurable (Y j) := fun j => (hm j).const_mul σ⁻¹
    have hYident : ∀ j, IdentDistrib (Y j) (Y 0) Q Q := fun j =>
      (hident j).comp (measurable_id.const_mul σ⁻¹)
    have hY0 : ∫ ω, Y 0 ω ∂Q = 0 := by
      simp only [hY]; rw [integral_const_mul, h0, mul_zero]
    have hY1 : ∫ ω, Y 0 ω ^ 2 ∂Q = 1 := by
      simp only [hY, mul_pow]
      rw [integral_const_mul, ← hσ2, inv_pow, inv_mul_cancel₀ (by positivity)]
    have hlow : ∀ᵐ ω ∂Q, ∀ k : ℕ, ∃ᶠ n in atTop,
        (1 - 1 / ((k : ℝ) + 2)) * lilScale n ≤ ∑ j ∈ Finset.range n, Y j ω := by
      refine ae_all_iff.2 fun k => ?_
      have hk : 1 / ((k : ℝ) + 2) ≤ 1 := by
        rw [div_le_one (by positivity)]; have := Nat.cast_nonneg (α := ℝ) k; linarith
      exact lil_lower_normalized hYind hYm hYident (hL2.const_mul σ⁻¹) hY0 hY1 (by positivity) hk
    filter_upwards [hup, hlow] with ω hω1 hω2
    intro ε hε
    refine ⟨?_, ?_⟩
    · obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      refine (hω1 k).mono fun n hn => hn.trans ?_
      exact mul_le_mul_of_nonneg_right (by linarith) (lilScale_nonneg n)
    · obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < ε / σ by positivity)
      refine (hω2 k).mono fun n hn => ?_
      have hsum : ∑ j ∈ Finset.range n, X j ω = σ * ∑ j ∈ Finset.range n, Y j ω := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hY]; field_simp
      change (σ - ε) * lilScale n ≤ ∑ j ∈ Finset.range n, X j ω
      rw [hsum]
      have h1 : σ * (1 / ((k : ℝ) + 2)) ≤ ε := by
        have h2 : 1 / ((k : ℝ) + 2) ≤ 1 / ((k : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
        have h3 : 1 / ((k : ℝ) + 1) < ε / σ := hk
        rw [lt_div_iff₀ hσpos] at h3
        nlinarith
      calc (σ - ε) * lilScale n ≤ σ * ((1 - 1 / ((k : ℝ) + 2)) * lilScale n) := by
            have := lilScale_nonneg n
            nlinarith
        _ ≤ σ * ∑ j ∈ Finset.range n, Y j ω := mul_le_mul_of_nonneg_left hn hσpos.le

/-- **The Hartman–Wintner law of the iterated logarithm**: for i.i.d. centred `Xⱼ ∈ L²` with
`σ² = E[X₀²]`, almost surely `limsup Sₙ/√(2 n log log n) = σ` and `liminf = −σ`
(in `ε`-form, `HasLIL`). -/
theorem hasLIL_iid {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {X : ℕ → Ω → ℝ} (hind : iIndepFun X Q) (hm : ∀ j, Measurable (X j))
    (hident : ∀ j, IdentDistrib (X j) (X 0) Q Q) (hL2 : MemLp (X 0) 2 Q)
    (h0 : ∫ ω, X 0 ω ∂Q = 0) :
    ∀ᵐ ω ∂Q, HasLIL (fun n => ∑ j ∈ Finset.range n, X j ω) (√(∫ ω, X 0 ω ^ 2 ∂Q)) := by
  have h1 := lilBound_iid hind hm hident hL2 h0
  have h2 := lilBound_iid (X := fun j ω => -X j ω)
    (hind.comp (fun _ x => -x) fun _ => measurable_neg) (fun j => (hm j).neg)
    (fun j => (hident j).comp measurable_neg) hL2.neg (by rw [integral_neg, h0, neg_zero])
  have hsq : √(∫ ω, (-X 0 ω) ^ 2 ∂Q) = √(∫ ω, X 0 ω ^ 2 ∂Q) := by simp_rw [neg_sq]
  rw [hsq] at h2
  filter_upwards [h1, h2] with ω hω1 hω2
  refine ⟨hω1, ?_⟩
  simpa only [Finset.sum_neg_distrib] using hω2

/-! ### The `limsup`/`liminf` form -/

/-- Under `LILBound s γ`, eventually `sₙ/√(2 n log log n) ≤ γ + ε`, and frequently
`sₙ/√(2 n log log n) ≥ γ − ε`. -/
theorem LILBound.div {s : ℕ → ℝ} {γ : ℝ} (h : LILBound s γ) {ε : ℝ} (hε : 0 < ε) :
    (∀ᶠ n in atTop, s n / lilScale n ≤ γ + ε) ∧ ∃ᶠ n in atTop, γ - ε ≤ s n / lilScale n := by
  obtain ⟨h1, h2⟩ := h ε hε
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < lilScale n := by
    filter_upwards [lil_eventually_le_log 3] with n hn using lilScale_pos hn
  refine ⟨?_, ?_⟩
  · filter_upwards [h1, hpos] with n hn hp
    rwa [div_le_iff₀ hp]
  · refine (h2.and_eventually hpos).mono fun n hn => ?_
    rw [le_div_iff₀ hn.2]; exact hn.1

/-- **The LIL in `limsup` form**: under `HasLIL s γ`, `limsup sₙ/√(2 n log log n) = γ`. -/
theorem HasLIL.limsup_eq {s : ℕ → ℝ} {γ : ℝ} (h : HasLIL s γ) :
    limsup (fun n => s n / lilScale n) atTop = γ := by
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun n => s n / lilScale n) :=
    isBoundedUnder_of_eventually_le (h.1.div one_pos).1
  have hcb : IsCoboundedUnder (· ≤ ·) atTop (fun n => s n / lilScale n) := by
    refine IsBoundedUnder.isCoboundedUnder_le (isBoundedUnder_of_eventually_ge
      (a := -(γ + 1)) ?_)
    filter_upwards [(h.2.div one_pos).1] with n hn
    rw [neg_div] at hn
    linarith
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_)
    (le_of_forall_pos_le_add fun ε hε => ?_)
  · exact limsup_le_of_le hcb (h.1.div hε).1
  · have := le_limsup_of_frequently_le (h.1.div hε).2 hb
    linarith

/-- **The LIL in `liminf` form**: under `HasLIL s γ`, `liminf sₙ/√(2 n log log n) = −γ`. -/
theorem HasLIL.liminf_eq {s : ℕ → ℝ} {γ : ℝ} (h : HasLIL s γ) :
    liminf (fun n => s n / lilScale n) atTop = -γ := by
  have hlow : ∀ ε > 0, ∀ᶠ n in atTop, -γ - ε ≤ s n / lilScale n := fun ε hε => by
    filter_upwards [(h.2.div hε).1] with n hn
    rw [neg_div] at hn
    linarith
  have hfr : ∀ ε > 0, ∃ᶠ n in atTop, s n / lilScale n ≤ -γ + ε := fun ε hε =>
    (h.2.div hε).2.mono fun n hn => by
      rw [neg_div] at hn
      linarith
  have hb : IsBoundedUnder (· ≥ ·) atTop (fun n => s n / lilScale n) :=
    isBoundedUnder_of_eventually_ge (hlow 1 one_pos)
  have hcb : IsCoboundedUnder (· ≥ ·) atTop (fun n => s n / lilScale n) :=
    IsBoundedUnder.isCoboundedUnder_ge (isBoundedUnder_of_eventually_le (h.1.div one_pos).1)
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_)
    (le_of_forall_pos_le_add fun ε hε => ?_)
  · exact liminf_le_of_frequently_le (hfr ε hε) hb
  · have := le_liminf_of_le hcb (hlow ε hε)
    linarith

/-- **The Hartman–Wintner LIL in `limsup`/`liminf` form**: for i.i.d. centred `Xⱼ ∈ L²` with
`σ² = E[X₀²]`, almost surely `limsup Sₙ/√(2 n log log n) = σ` and
`liminf Sₙ/√(2 n log log n) = −σ`. -/
theorem limsup_liminf_iid {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {X : ℕ → Ω → ℝ} (hind : iIndepFun X Q)
    (hm : ∀ j, Measurable (X j)) (hident : ∀ j, IdentDistrib (X j) (X 0) Q Q)
    (hL2 : MemLp (X 0) 2 Q) (h0 : ∫ ω, X 0 ω ∂Q = 0) :
    ∀ᵐ ω ∂Q, limsup (fun n => (∑ j ∈ Finset.range n, X j ω) / lilScale n) atTop =
        √(∫ ω, X 0 ω ^ 2 ∂Q) ∧
      liminf (fun n => (∑ j ∈ Finset.range n, X j ω) / lilScale n) atTop =
        -√(∫ ω, X 0 ω ^ 2 ∂Q) := by
  filter_upwards [hasLIL_iid hind hm hident hL2 h0] with ω hω
  exact ⟨hω.limsup_eq, hω.liminf_eq⟩

end RQMCMarkov.MarkovDriving

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # The discrepancy-to-occupation inequality (post #3)

Post #3 ranks the ways of driving a chain by how fast the occupation frequencies `N_s(T)/T` and
the empirical transition matrix converge: MC at `O(1/√T)`, per-state low-discrepancy stacks
"faster than `O(1/√T)`" (`O(log T / T)`), rotors at `O(1/T)`. All three rates come from one
**deterministic** inequality, valid for *any* path `x : ℕ → S`, proved here by telescoping
Poisson's equation (Meyn and Tweedie, Ch. 17; Holroyd and Propp 2010 use the same device).

For a test function `g`, the **departure discrepancy** of state `i` up to time `T` is
`D_i(g, T) = Σ_{t < T, x t = i} (g(x_{t+1}) − (Pg)(i))`: the error of the departures from `i`
as a sample of the row `P(i, ·)`. If `h − Ph = f − c` then

`Σ_{t<T} f(x_t) − T c = h(x_0) − h(x_T) + Σ_i D_i(h, T)`        (`sum_sub_eq_boundary_add`),

so for `f = 1_{s}` and `c = π_s` (`occCount_sub_eq_boundary_add`, `abs_occCount_sub_le`):

`|N_s(T) − T π_s| ≤ 2‖h‖∞ + Σ_i |D_i(h, T)|`  (occupation error ≤ boundary + departure
discrepancies).

The transition counts satisfy the exact identity `N_ij(T) − p_ij N_i(T) = D_i(1_{j}, T)`
(`transCount_sub_eq_departureDiscrepancy`), and hence (`abs_transCount_sub_le`)
`|N_ij(T) − T π_i p_ij| ≤ |D_i(1_{j}, T)| + p_ij (2‖h‖∞ + Σ_k |D_k(h, T)|)`.

For a path built from per-state stacks (`stackDrive`, which covers the QMC stacks of post #3
and the rotor-router), the departures from `i` are the first `N_i(T)` entries of stack `i`
(`sum_filter_occCount_eq`, `departureDiscrepancy_stackDrive`, `transCount_stackDrive`), so the
departure discrepancy is an ordinary one-dimensional sampling error, bounded in `StackBound`
(van der Corput stacks), `RotorRouter` (rotors) and `MCRate` (i.i.d. stacks).

The sup-norm `‖h‖∞` enters through any bound `M` with `∀ i, |h i| ≤ M`.
-/

namespace RQMCMarkov.MarkovDriving

open Finset Matrix

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The **departure discrepancy** of state `i` for the test function `g` up to time `T`:
`Σ_{t < T, x t = i} (g (x (t+1)) − (Pg)(i))`. -/
noncomputable def departureDiscrepancy (P : Matrix S S ℝ) (g : S → ℝ) (x : ℕ → S) (i : S)
    (T : ℕ) : ℝ :=
  ∑ t ∈ (range T).filter (fun t => x t = i), (g (x (t + 1)) - (P *ᵥ g) i)

/-- **The telescoping identity.** If `h − Ph = f − c`, then along any path
`Σ_{t<T} f(x_t) − T c = h(x_0) − h(x_T) + Σ_i D_i(h, T)`. -/
theorem sum_sub_eq_boundary_add (P : Matrix S S ℝ) {f h : S → ℝ} {c : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = f i - c) (x : ℕ → S) (T : ℕ) :
    ∑ t ∈ range T, f (x t) - T * c =
      h (x 0) - h (x T) + ∑ i, departureDiscrepancy P h x i T := by
  have e1 : ∑ t ∈ range T, f (x t) - T * c = ∑ t ∈ range T, (h (x t) - (P *ᵥ h) (x t)) := by
    rw [← card_range T, ← nsmul_eq_mul, ← sum_const, card_range, ← sum_sub_distrib]
    exact sum_congr rfl fun t _ => (hh (x t)).symm
  have e2 : ∑ t ∈ range T, (h (x t) - (P *ᵥ h) (x t)) =
      ∑ t ∈ range T, (h (x t) - h (x (t + 1))) +
        ∑ t ∈ range T, (h (x (t + 1)) - (P *ᵥ h) (x t)) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun t _ => by ring
  have e3 : ∑ t ∈ range T, (h (x (t + 1)) - (P *ᵥ h) (x t)) =
      ∑ i, departureDiscrepancy P h x i T := by
    rw [← sum_fiberwise (range T) x]
    refine sum_congr rfl fun i _ => sum_congr rfl fun t ht => ?_
    rw [(mem_filter.1 ht).2]
  rw [e1, e2, e3, sum_range_sub' (fun t => h (x t)) T]

omit [Fintype S] in
/-- `Σ_{t<T} 1_{s}(x_t) = N_s(T)`. -/
theorem sum_indicator_eq_occCount (x : ℕ → S) (s : S) (T : ℕ) :
    ∑ t ∈ range T, (if x t = s then (1 : ℝ) else 0) = occCount x s T := by
  rw [sum_boole]
  rfl

/-- **Occupation identity.** If `h − Ph = 1_{s} − c` (Poisson's equation, with `c = π_s`), then
along any path `N_s(T) − T c = h(x_0) − h(x_T) + Σ_i D_i(h, T)`. -/
theorem occCount_sub_eq_boundary_add (P : Matrix S S ℝ) {h : S → ℝ} {s : S} {c : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (x : ℕ → S) (T : ℕ) :
    (occCount x s T : ℝ) - T * c = h (x 0) - h (x T) + ∑ i, departureDiscrepancy P h x i T := by
  rw [← sum_indicator_eq_occCount]
  exact sum_sub_eq_boundary_add P hh x T

/-- **The discrepancy-to-occupation inequality** (the backbone of post #3's rates): for any path,
`|N_s(T) − T c| ≤ 2M + Σ_i |D_i(h, T)|`, where `h − Ph = 1_{s} − c` and `|h| ≤ M`. -/
theorem abs_occCount_sub_le (P : Matrix S S ℝ) {h : S → ℝ} {s : S} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M)
    (x : ℕ → S) (T : ℕ) :
    |(occCount x s T : ℝ) - T * c| ≤ 2 * M + ∑ i, |departureDiscrepancy P h x i T| := by
  rw [occCount_sub_eq_boundary_add P hh x T]
  have hb : |h (x 0) - h (x T)| ≤ 2 * M := by
    have := abs_sub (h (x 0)) (h (x T))
    linarith [hM (x 0), hM (x T)]
  calc |h (x 0) - h (x T) + ∑ i, departureDiscrepancy P h x i T|
      ≤ |h (x 0) - h (x T)| + |∑ i, departureDiscrepancy P h x i T| := abs_add_le _ _
    _ ≤ 2 * M + ∑ i, |departureDiscrepancy P h x i T| :=
        add_le_add hb (abs_sum_le_sum_abs _ _)

/-- `(P 1_{j})(i) = P i j`. -/
theorem mulVec_indicator (P : Matrix S S ℝ) (i j : S) :
    (P *ᵥ fun k => if k = j then (1 : ℝ) else 0) i = P i j := by
  simp only [mulVec, dotProduct, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', mem_univ,
    ite_true]

/-- **Transition identity.** `N_ij(T) − p_ij N_i(T)` is exactly the departure discrepancy of `i`
for the indicator `1_{j}`. -/
theorem transCount_sub_eq_departureDiscrepancy (P : Matrix S S ℝ) (x : ℕ → S) (i j : S)
    (T : ℕ) : (transCount x i j T : ℝ) - P i j * occCount x i T =
      departureDiscrepancy P (fun k => if k = j then 1 else 0) x i T := by
  unfold departureDiscrepancy
  rw [mulVec_indicator, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_comm (P i j), sum_boole,
    filter_filter]
  rfl

/-- **Transition counts against the target `T π_i p_ij`** (post #3's "number of each
transition"): `|N_ij(T) − T c p_ij| ≤ |D_i(1_{j}, T)| + p_ij (2M + Σ_k |D_k(h, T)|)`, where
`h − Ph = 1_{i} − c` and `|h| ≤ M`. -/
theorem abs_transCount_sub_le (P : Matrix S S ℝ) (hP0 : ∀ i j, 0 ≤ P i j) {h : S → ℝ} {i : S}
    {c M : ℝ} (hh : ∀ k, h k - (P *ᵥ h) k = (if k = i then 1 else 0) - c) (hM : ∀ k, |h k| ≤ M)
    (x : ℕ → S) (j : S) (T : ℕ) :
    |(transCount x i j T : ℝ) - T * c * P i j| ≤
      |departureDiscrepancy P (fun k => if k = j then 1 else 0) x i T| +
        P i j * (2 * M + ∑ k, |departureDiscrepancy P h x k T|) := by
  have e : (transCount x i j T : ℝ) - T * c * P i j =
      departureDiscrepancy P (fun k => if k = j then 1 else 0) x i T +
        P i j * ((occCount x i T : ℝ) - T * c) := by
    rw [← transCount_sub_eq_departureDiscrepancy]
    ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [abs_mul, abs_of_nonneg (hP0 i j)]
  exact mul_le_mul_of_nonneg_left (abs_occCount_sub_le P hh hM x T) (hP0 i j)

omit [Fintype S] in
/-- **Departures are read off in order.** Summing over the visits `t < T` to `i` a function of
the visit index `N_i(t)` is summing over the first `N_i(T)` indices. -/
theorem sum_filter_occCount_eq {R : Type*} [AddCommMonoid R] (x : ℕ → S) (i : S) (φ : ℕ → R)
    (T : ℕ) : ∑ t ∈ (range T).filter (fun t => x t = i), φ (occCount x i t) =
      ∑ k ∈ range (occCount x i T), φ k := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [range_add_one, filter_insert, occCount_succ]
    by_cases hT : x T = i
    · have hnot : T ∉ (range T).filter (fun t => x t = i) := fun hm =>
        lt_irrefl T (mem_range.1 (mem_filter.1 hm).1)
      simp only [hT, ite_true]
      rw [sum_insert hnot, ih, sum_range_succ, add_comm]
    · simp only [hT, ite_false, add_zero]
      exact ih

omit [Fintype S] in
/-- In a stack path, the `t`-th transition out of `i` uses entry `N_i(t)` of stack `i`. -/
theorem stackDrive_succ_of_eq {α : Type*} (G : S → α → S) (x₀ : S) (v : S → ℕ → α) {i : S}
    {t : ℕ} (ht : stackDrive G x₀ v t = i) :
    stackDrive G x₀ v (t + 1) = G i (v i (occCount (stackDrive G x₀ v) i t)) := by
  rw [stackDrive_succ]
  unfold departureIndex
  rw [ht]

/-- **Departure discrepancy of a stack path**: the departures from `i` up to `T` are
`G i (v i k)`, `k < N_i(T)`, so `D_i(g, T) = Σ_{k < N_i(T)} (g(G i (v i k)) − (Pg)(i))`. -/
theorem departureDiscrepancy_stackDrive {α : Type*} (P : Matrix S S ℝ) (g : S → ℝ)
    (G : S → α → S) (x₀ : S) (v : S → ℕ → α) (i : S) (T : ℕ) :
    departureDiscrepancy P g (stackDrive G x₀ v) i T =
      ∑ k ∈ range (occCount (stackDrive G x₀ v) i T), (g (G i (v i k)) - (P *ᵥ g) i) := by
  unfold departureDiscrepancy
  rw [← sum_filter_occCount_eq (stackDrive G x₀ v) i
    (fun k => g (G i (v i k)) - (P *ᵥ g) i) T]
  refine sum_congr rfl fun t ht => ?_
  rw [stackDrive_succ_of_eq G x₀ v (mem_filter.1 ht).2]

omit [Fintype S] in
/-- **Transition counts of a stack path**: `N_ij(T) = #{k < N_i(T) : G i (v i k) = j}`. -/
theorem transCount_stackDrive {α : Type*} (G : S → α → S) (x₀ : S) (v : S → ℕ → α) (i j : S)
    (T : ℕ) : transCount (stackDrive G x₀ v) i j T =
      ((range (occCount (stackDrive G x₀ v) i T)).filter fun k => G i (v i k) = j).card := by
  have h1 := sum_filter_occCount_eq (stackDrive G x₀ v) i
    (fun k => if G i (v i k) = j then 1 else 0) T
  simp only [sum_boole, Nat.cast_id] at h1
  have h2 : ∑ t ∈ (range T).filter (fun t => stackDrive G x₀ v t = i),
      (if G i (v i (occCount (stackDrive G x₀ v) i t)) = j then 1 else 0) =
      ∑ t ∈ (range T).filter (fun t => stackDrive G x₀ v t = i),
      (if stackDrive G x₀ v (t + 1) = j then (1 : ℕ) else 0) :=
    sum_congr rfl fun t ht => by rw [stackDrive_succ_of_eq G x₀ v (mem_filter.1 ht).2]
  simp only [sum_boole, Nat.cast_id, filter_filter] at h2
  unfold transCount
  rw [← h1, ← h2, filter_filter]

end RQMCMarkov.MarkovDriving

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # Rotor-router walks: `O(1/T)` occupation error (post #3; Holroyd and Propp 2010)

Post #3: "A rotor is a per-state stack, but instead of a low-discrepancy sequence, each state's
stack is a fixed cycle of next states … The `k`-th departure from state `i` goes to entry `k` of
`i`'s cycle … the error in occupation frequencies is `O(1/T)`, better than QMC's
`O(log T / T)` (Holroyd and Propp, 2010)."

**Setting.** Each state `i` has a cycle of length `L i > 0`, given by its entries
`c i 0, …, c i (L i − 1)`, in which `j` appears exactly `p_ij L i` times (`IsRotorCycle`; this
needs rational `P`, and is a hypothesis). The rotor walk with offsets `θ` (`rotorWalk`) sends
the `k`-th departure from `i` to `c i ((θ i + k) mod L i)`; `θ = 0` is the deterministic rotor
of post #3, a random `θ` is its "randomized rotor-router (each state starts at a random point
of its cycle)". The walk is the stack representation with stacks of next states
(`stackDrive (fun _ j ↦ j)`). The balance of every *stretch* of the cycle, mentioned in post
#3, is not needed for the bounds below: only the counts over a full cycle are used.

**Results.**
* `rotorWalk_succ`, `rotorWalk_shift` (the walk after time `τ` is the rotor walk started from
  the current rotor state: the future depends only on the current state and rotor positions),
  `rotorWalk_congr_mod`.
* `sum_range_eq_sum_range_mod`: partial sums of a periodic sequence with zero full-period sum
  reduce to the last partial cycle; `sum_cycle_eq` (a full cycle samples `P(i, ·)` exactly).
* `departureDiscrepancy_rotorWalk_eq`: `D_i(g, T)` is the sum over the last, incomplete cycle;
  `abs_departureDiscrepancy_rotorWalk_le`, `abs_departureDiscrepancy_rotorWalk_le_two_mul`:
  `|D_i(g, T)| ≤ 2 (L i − 1) ‖g‖∞`, bounded in `T`.
* `abs_transCount_rotorWalk_sub_le`: `|N_ij(T) − p_ij N_i(T)| ≤ L i − 1 < L i`;
  `transCount_rotorWalk_eq_of_dvd`: **exact** counts `N_ij(T) = p_ij N_i(T)` at the end of
  every full cycle of `i` (`L i ∣ N_i(T)`).
* **Holroyd–Propp** (`abs_occCount_rotorWalk_sub_le`): `|N_s(T) − T π_s| ≤
  2 M (1 + Σ_i (L i − 1))` with `|h| ≤ M` (`h` the Poisson solution for `1_{s}`), independent
  of `T`; `abs_occFreq_rotorWalk_sub_le`, `occFreq_rotorWalk_isBigO`: frequency error `O(1/T)`.
* `abs_transCount_rotorWalk_sub_target_le`: `|N_ij(T) − T π_i p_ij| ≤ (L i − 1) + p_ij C_i`.

**Correction** (post #3: "a by-product of rotors is that we achieve the same exact expected
number of transitions that we did by conditional MC"). The rotor counts are within a constant
(independent of `T`) of conditional MC's targets `T π_i p_ij`, and are exactly `p_ij N_i(T)`
whenever `N_i(T)` is a multiple of `L i`; they cannot be *exactly* `T π_i p_ij` in general,
since that number need not be an integer: `not_transCount_eq_target` (two-state chain with
`p_ii = 7/8`, `π = (1/2, 1/2)`: `N_00(T) = 7T/16` is impossible unless `16 ∣ T`).

**Correction** (randomized rotor). Each single departure of the randomized rotor has the right
law (`card_offset_eq`: for a uniform offset, the `k`-th departure from `i` goes to `j` with
probability exactly `p_ij`), and the pathwise bound gives `|E N_s(T) − T π_s| ≤ C` for any
law of the start and offsets (`abs_expected_occCount_rotorWalk_sub_le`). But the expected
occupation is **not** exactly `T π_s`, even with a stationary start, because successive
departures from a state are dependent: `expected_occCount_ne` is an irreducible two-state chain
(`P = [[1/2, 1/2], [1, 0]]`, `π = (2/3, 1/3)`) with `E N_0(3) = 11/6 ≠ 2 = 3 π_0`.
-/

namespace RQMCMarkov.MarkovDriving

open Finset Matrix Filter Asymptotics

variable {S : Type*} [DecidableEq S]

/-- **The rotor walk**: from `x₀`, the `k`-th departure (`k = 0, 1, …`) from state `i` goes to
`c i ((θ i + k) mod L i)`, entry `k` of `i`'s cycle started at offset `θ i`. -/
def rotorWalk (L : S → ℕ) (c : S → ℕ → S) (θ : S → ℕ) (x₀ : S) : ℕ → S :=
  stackDrive (fun _ j => j) x₀ (fun i k => c i ((θ i + k) % L i))

/-- The rotor recursion: `x (t+1) = c (x t) ((θ (x t) + N_{x t}(t)) mod L (x t))`. -/
theorem rotorWalk_succ (L : S → ℕ) (c : S → ℕ → S) (θ : S → ℕ) (x₀ : S) (t : ℕ) :
    rotorWalk L c θ x₀ (t + 1) = c (rotorWalk L c θ x₀ t)
      ((θ (rotorWalk L c θ x₀ t) + occCount (rotorWalk L c θ x₀) (rotorWalk L c θ x₀ t) t) %
        L (rotorWalk L c θ x₀ t)) :=
  stackDrive_succ _ _ _ t

/-- The rotor walk starts at `x₀`. -/
theorem rotorWalk_zero (L : S → ℕ) (c : S → ℕ → S) (θ : S → ℕ) (x₀ : S) :
    rotorWalk L c θ x₀ 0 = x₀ :=
  rfl

/-- **The rotor walk is a function of the current rotor state**: after time `τ` it is the rotor
walk started at `x τ` with offsets `θ i + N_i(τ)`. -/
theorem rotorWalk_shift (L : S → ℕ) (c : S → ℕ → S) (θ : S → ℕ) (x₀ : S) (τ t : ℕ) :
    rotorWalk L c θ x₀ (τ + t) = rotorWalk L c (fun i => θ i + occCount (rotorWalk L c θ x₀) i τ)
      (rotorWalk L c θ x₀ τ) t := by
  set x := rotorWalk L c θ x₀ with hx
  have key := (stackDrive_eq_iff (fun _ j => j) (x τ)
    (fun i k => c i ((θ i + occCount x i τ + k) % L i)) (fun t => x (τ + t)) t).2
    ⟨rfl, fun t' _ => ?_⟩
  · exact (key t le_rfl).symm
  · change c (x (τ + t')) ((θ (x (τ + t')) + occCount x (x (τ + t')) τ +
      occCount (fun t => x (τ + t)) (x (τ + t')) t') % L (x (τ + t'))) = x (τ + (t' + 1))
    rw [add_assoc (θ _), ← occCount_add, ← add_assoc τ, hx, rotorWalk_succ]

/-- The rotor walk depends on the offsets only modulo the cycle lengths. -/
theorem rotorWalk_congr_mod (L : S → ℕ) (c : S → ℕ → S) {θ θ' : S → ℕ}
    (h : ∀ i, θ i % L i = θ' i % L i) (x₀ : S) : rotorWalk L c θ x₀ = rotorWalk L c θ' x₀ := by
  funext t
  have key := (stackDrive_eq_iff (fun _ j => j) x₀ (fun i k => c i ((θ i + k) % L i))
    (rotorWalk L c θ' x₀) t).2 ⟨rfl, fun t' _ => ?_⟩
  · exact key t le_rfl
  · change c _ ((θ _ + occCount _ _ t') % L _) = _
    rw [rotorWalk_succ, Nat.add_mod, h, ← Nat.add_mod]

/-- A shift of the summation window of a periodic sequence over one period leaves the sum
unchanged. -/
theorem sum_range_add_periodic {M : Type*} [AddCommGroup M] {F : ℕ → M} {L : ℕ}
    (hF : ∀ k, F (k + L) = F k) (a : ℕ) : ∑ m ∈ range L, F (a + m) = ∑ m ∈ range L, F m := by
  induction a with
  | zero => simp only [zero_add]
  | succ a ih =>
    have h1 := sum_range_succ (fun m => F (a + m)) L
    have h2 := sum_range_succ' (fun m => F (a + m)) L
    beta_reduce at h1 h2
    rw [hF a] at h1
    rw [add_zero] at h2
    have e : ∑ m ∈ range L, F (a + 1 + m) = ∑ m ∈ range L, F (a + (m + 1)) :=
      sum_congr rfl fun m _ => by rw [add_assoc, add_comm 1 m]
    rw [e, ← ih]
    exact (add_right_cancel (h1.symm.trans h2)).symm

/-- **Partial sums of a periodic sequence with zero full-period sum** reduce to the last
incomplete period: `Σ_{k < N} F k = Σ_{k < N mod L} F k`. -/
theorem sum_range_eq_sum_range_mod {M : Type*} [AddCommMonoid M] {F : ℕ → M} {L : ℕ}
    (hF : ∀ k, F (k + L) = F k) (h0 : ∑ m ∈ range L, F m = 0) (N : ℕ) :
    ∑ k ∈ range N, F k = ∑ k ∈ range (N % L), F k := by
  have key : ∀ q r, ∑ k ∈ range (L * q + r), F k = ∑ k ∈ range r, F k := by
    intro q r
    induction q with
    | zero => rw [mul_zero, zero_add]
    | succ q ih =>
      rw [show L * (q + 1) + r = L + (L * q + r) by ring, sum_range_add, h0, zero_add, ← ih]
      exact sum_congr rfl fun k _ => by rw [add_comm L k, hF]
  conv_lhs => rw [← Nat.div_add_mod N L]
  exact key _ _

variable [Fintype S]

/-- **Balanced cycles** (post #3's rotors; needs rational `P`): every cycle has positive length,
and `j` appears exactly `p_ij L i` times in the cycle of `i`. -/
structure IsRotorCycle (P : Matrix S S ℝ) (L : S → ℕ) (c : S → ℕ → S) : Prop where
  len_pos : ∀ i, 0 < L i
  card_eq : ∀ i j, (((range (L i)).filter fun m => c i m = j).card : ℝ) = P i j * L i

/-- **A full cycle samples the row exactly**: `Σ_{m < L i} g (c i m) = L i (Pg)(i)`. -/
theorem sum_cycle_eq {P : Matrix S S ℝ} {L : S → ℕ} {c : S → ℕ → S} (hc : IsRotorCycle P L c)
    (g : S → ℝ) (i : S) : ∑ m ∈ range (L i), g (c i m) = L i * (P *ᵥ g) i := by
  rw [← sum_fiberwise (range (L i)) (c i)]
  have e : ∀ j, ∑ m ∈ (range (L i)).filter (fun m => c i m = j), g (c i m) =
      g j * (((range (L i)).filter fun m => c i m = j).card : ℝ) := fun j => by
    rw [sum_congr rfl fun m hm => by rw [(mem_filter.1 hm).2], sum_const, nsmul_eq_mul,
      mul_comm]
  rw [sum_congr rfl fun j _ => e j]
  simp only [hc.card_eq, mulVec, dotProduct, mul_sum]
  exact sum_congr rfl fun j _ => by ring

/-- The **departure sequence** of the rotor at `i`, centred: `F k = g(c i ((θ + k) mod L)) −
(Pg)(i)`. It is `L i`-periodic with zero sum over a period. -/
theorem sum_range_rotor_centred_eq_zero {P : Matrix S S ℝ} {L : S → ℕ} {c : S → ℕ → S}
    (hc : IsRotorCycle P L c) (g : S → ℝ) (i : S) (a : ℕ) :
    ∑ m ∈ range (L i), (g (c i ((a + m) % L i)) - (P *ᵥ g) i) = 0 := by
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  have hper : ∀ k, g (c i ((k + L i) % L i)) = g (c i (k % L i)) := fun k => by
    rw [Nat.add_mod_right]
  rw [sum_range_add_periodic (F := fun m => g (c i (m % L i))) hper a]
  have e : ∑ m ∈ range (L i), g (c i (m % L i)) = ∑ m ∈ range (L i), g (c i m) :=
    sum_congr rfl fun m hm => by rw [Nat.mod_eq_of_lt (mem_range.1 hm)]
  rw [e, sum_cycle_eq hc g i, sub_self]

/-- The departure discrepancy of a rotor walk is the sum over the last, incomplete cycle:
`D_i(g, T) = Σ_{k < N_i(T) mod L i} (g(c i ((θ i + k) mod L i)) − (Pg)(i))`. -/
theorem departureDiscrepancy_rotorWalk_eq {P : Matrix S S ℝ} {L : S → ℕ} {c : S → ℕ → S}
    (hc : IsRotorCycle P L c) (θ : S → ℕ) (x₀ : S) (g : S → ℝ) (i : S) (T : ℕ) :
    departureDiscrepancy P g (rotorWalk L c θ x₀) i T =
      ∑ k ∈ range (occCount (rotorWalk L c θ x₀) i T % L i),
        (g (c i ((θ i + k) % L i)) - (P *ᵥ g) i) := by
  unfold rotorWalk
  rw [departureDiscrepancy_stackDrive]
  refine sum_range_eq_sum_range_mod (fun k => ?_) (sum_range_rotor_centred_eq_zero hc g i _) _
  rw [← add_assoc, Nat.add_mod_right]

/-- A sum of `r` terms bounded by `B`, with `r < L`, is at most `(L − 1) B`. -/
theorem abs_sum_range_le_of_lt {F : ℕ → ℝ} {B : ℝ} (hB : ∀ k, |F k| ≤ B) {r L : ℕ}
    (hr : r < L) : |∑ k ∈ range r, F k| ≤ (L - 1 : ℕ) * B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  calc |∑ k ∈ range r, F k| ≤ ∑ k ∈ range r, |F k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ range r, B := sum_le_sum fun k _ => hB k
    _ = r * B := by rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ (L - 1 : ℕ) * B := mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega)) hB0

/-- **Rotor departure discrepancies are bounded**: if every centred departure value
`g(c i m) − (Pg)(i)` is at most `B` in absolute value, then `|D_i(g, T)| ≤ (L i − 1) B` for
every `T`. -/
theorem abs_departureDiscrepancy_rotorWalk_le {P : Matrix S S ℝ} {L : S → ℕ} {c : S → ℕ → S}
    (hc : IsRotorCycle P L c) (θ : S → ℕ) (x₀ : S) {g : S → ℝ} {i : S} {B : ℝ}
    (hB : ∀ m, |g (c i m) - (P *ᵥ g) i| ≤ B) (T : ℕ) :
    |departureDiscrepancy P g (rotorWalk L c θ x₀) i T| ≤ (L i - 1 : ℕ) * B := by
  rw [departureDiscrepancy_rotorWalk_eq hc]
  exact abs_sum_range_le_of_lt (fun k => hB _) (Nat.mod_lt _ (hc.len_pos i))

omit [DecidableEq S] in
/-- For a stochastic `P`, `|g(j) − (Pg)(i)| ≤ 2M` when `|g| ≤ M`. -/
theorem abs_sub_mulVec_le {P : Matrix S S ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    (hP1 : ∀ i, ∑ j, P i j = 1) {g : S → ℝ} {M : ℝ} (hM : ∀ j, |g j| ≤ M) (i j : S) :
    |g j - (P *ᵥ g) i| ≤ 2 * M := by
  have hPg : |(P *ᵥ g) i| ≤ M := by
    calc |(P *ᵥ g) i| = |∑ k, P i k * g k| := rfl
      _ ≤ ∑ k, |P i k * g k| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, P i k * M := sum_le_sum fun k _ => by
          rw [abs_mul, abs_of_nonneg (hP0 i k)]
          exact mul_le_mul_of_nonneg_left (hM k) (hP0 i k)
      _ = M := by rw [← sum_mul, hP1 i, one_mul]
  have := abs_sub (g j) ((P *ᵥ g) i)
  linarith [hM j]

/-- **Rotor departure discrepancy, explicit**: `|D_i(g, T)| ≤ 2 (L i − 1) M` when `|g| ≤ M`. -/
theorem abs_departureDiscrepancy_rotorWalk_le_two_mul {P : Matrix S S ℝ}
    (hP0 : ∀ i j, 0 ≤ P i j) (hP1 : ∀ i, ∑ j, P i j = 1) {L : S → ℕ} {c : S → ℕ → S}
    (hc : IsRotorCycle P L c) (θ : S → ℕ) (x₀ : S) {g : S → ℝ} {M : ℝ}
    (hM : ∀ j, |g j| ≤ M) (i : S) (T : ℕ) :
    |departureDiscrepancy P g (rotorWalk L c θ x₀) i T| ≤ (L i - 1 : ℕ) * (2 * M) :=
  abs_departureDiscrepancy_rotorWalk_le hc θ x₀ (fun _ => abs_sub_mulVec_le hP0 hP1 hM i _) T

/-- **Rotor transition counts are within one cycle**: `|N_ij(T) − p_ij N_i(T)| ≤ L i − 1`. -/
theorem abs_transCount_rotorWalk_sub_le {P : Matrix S S ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    (hP1 : ∀ i, ∑ j, P i j = 1) {L : S → ℕ} {c : S → ℕ → S} (hc : IsRotorCycle P L c)
    (θ : S → ℕ) (x₀ : S) (i j : S) (T : ℕ) :
    |(transCount (rotorWalk L c θ x₀) i j T : ℝ) - P i j * occCount (rotorWalk L c θ x₀) i T| ≤
      (L i - 1 : ℕ) := by
  rw [transCount_sub_eq_departureDiscrepancy, ← mul_one ((L i - 1 : ℕ) : ℝ)]
  refine abs_departureDiscrepancy_rotorWalk_le hc θ x₀ (fun m => ?_) T
  rw [mulVec_indicator]
  have hle : P i j ≤ 1 := by
    rw [← hP1 i]
    exact single_le_sum (fun k _ => hP0 i k) (mem_univ j)
  split_ifs
  · rw [abs_of_nonneg (by linarith)]
    linarith [hP0 i j]
  · rw [zero_sub, abs_neg, abs_of_nonneg (hP0 i j)]
    exact hle

omit [Fintype S] in
/-- **Exact counts at full cycles**: if `L i ∣ N_i(T)` then `N_ij(T) = p_ij N_i(T)` exactly, and
every departure discrepancy of `i` vanishes. -/
theorem transCount_rotorWalk_eq_of_dvd [Finite S] {P : Matrix S S ℝ} {L : S → ℕ}
    {c : S → ℕ → S} (hc : IsRotorCycle P L c) (θ : S → ℕ) (x₀ : S) {i : S} {T : ℕ}
    (hdvd : L i ∣ occCount (rotorWalk L c θ x₀) i T) (j : S) :
    (transCount (rotorWalk L c θ x₀) i j T : ℝ) = P i j * occCount (rotorWalk L c θ x₀) i T := by
  have := Fintype.ofFinite S
  rw [← sub_eq_zero, transCount_sub_eq_departureDiscrepancy,
    departureDiscrepancy_rotorWalk_eq hc, Nat.mod_eq_zero_of_dvd hdvd, range_zero, sum_empty]

/-- **Holroyd–Propp occupation bound** (post #3, "the error in occupation frequencies is
`O(1/T)`"): `|N_s(T) − T π_s| ≤ 2M (1 + Σ_i (L i − 1))` for every `T`, where `h − Ph = 1_{s} −
π_s` and `|h| ≤ M`. -/
theorem abs_occCount_rotorWalk_sub_le {P : Matrix S S ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    (hP1 : ∀ i, ∑ j, P i j = 1) {L : S → ℕ} {c : S → ℕ → S} (hc : IsRotorCycle P L c)
    (θ : S → ℕ) (x₀ : S) {h : S → ℝ} {s : S} {μs M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - μs) (hM : ∀ i, |h i| ≤ M)
    (T : ℕ) : |(occCount (rotorWalk L c θ x₀) s T : ℝ) - T * μs| ≤
      2 * M * (1 + ∑ i, ((L i - 1 : ℕ) : ℝ)) := by
  refine (abs_occCount_sub_le P hh hM _ T).trans ?_
  have hs := sum_le_sum fun i (_ : i ∈ univ) =>
    abs_departureDiscrepancy_rotorWalk_le_two_mul hP0 hP1 hc θ x₀ hM i T
  rw [← sum_mul] at hs
  have e : 2 * M * (1 + ∑ i, ((L i - 1 : ℕ) : ℝ)) = 2 * M + (∑ i, ((L i - 1 : ℕ) : ℝ)) * (2 * M) :=
    by ring
  rw [e]
  exact add_le_add le_rfl hs

/-- **Rotor occupation frequencies converge at `O(1/T)`**: `|N_s(T)/T − π_s| ≤ C / T`. -/
theorem abs_occFreq_rotorWalk_sub_le {P : Matrix S S ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    (hP1 : ∀ i, ∑ j, P i j = 1) {L : S → ℕ} {c : S → ℕ → S} (hc : IsRotorCycle P L c)
    (θ : S → ℕ) (x₀ : S) {h : S → ℝ} {s : S} {μs M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - μs) (hM : ∀ i, |h i| ≤ M)
    {T : ℕ} (hT : 0 < T) : |(occCount (rotorWalk L c θ x₀) s T : ℝ) / T - μs| ≤
      2 * M * (1 + ∑ i, ((L i - 1 : ℕ) : ℝ)) / T := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  rw [le_div_iff₀ hTpos, ← abs_of_pos hTpos, ← abs_mul, abs_of_pos hTpos, sub_mul,
    div_mul_cancel₀ _ hTpos.ne', mul_comm μs]
  exact abs_occCount_rotorWalk_sub_le hP0 hP1 hc θ x₀ hh hM T

/-- **Rotor occupation frequencies are `O(1/T)`** (Holroyd and Propp 2010). -/
theorem occFreq_rotorWalk_isBigO {P : Matrix S S ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    (hP1 : ∀ i, ∑ j, P i j = 1) {L : S → ℕ} {c : S → ℕ → S} (hc : IsRotorCycle P L c)
    (θ : S → ℕ) (x₀ : S) {h : S → ℝ} {s : S} {μs M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - μs) (hM : ∀ i, |h i| ≤ M) :
    (fun T : ℕ => (occCount (rotorWalk L c θ x₀) s T : ℝ) / T - μs) =O[atTop]
      fun T : ℕ => (1 : ℝ) / T := by
  refine IsBigO.of_bound (2 * M * (1 + ∑ i, ((L i - 1 : ℕ) : ℝ))) ?_
  filter_upwards [eventually_ge_atTop 1] with T hT
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ 1 / T by positivity),
    mul_one_div]
  exact abs_occFreq_rotorWalk_sub_le hP0 hP1 hc θ x₀ hh hM hT

/-- **Rotor transition counts against conditional MC's targets**: `|N_ij(T) − T π_i p_ij| ≤
(L i − 1) + p_ij · 2M (1 + Σ_k (L k − 1))`, bounded in `T` (post #3: rotors give the counts of
conditional MC "as an output"). -/
theorem abs_transCount_rotorWalk_sub_target_le {P : Matrix S S ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    (hP1 : ∀ i, ∑ j, P i j = 1) {L : S → ℕ} {c : S → ℕ → S} (hc : IsRotorCycle P L c)
    (θ : S → ℕ) (x₀ : S) {h : S → ℝ} {i : S} {μi M : ℝ}
    (hh : ∀ k, h k - (P *ᵥ h) k = (if k = i then 1 else 0) - μi) (hM : ∀ k, |h k| ≤ M)
    (j : S) (T : ℕ) : |(transCount (rotorWalk L c θ x₀) i j T : ℝ) - T * μi * P i j| ≤
      (L i - 1 : ℕ) + P i j * (2 * M * (1 + ∑ k, ((L k - 1 : ℕ) : ℝ))) := by
  have e : (transCount (rotorWalk L c θ x₀) i j T : ℝ) - T * μi * P i j =
      ((transCount (rotorWalk L c θ x₀) i j T : ℝ) - P i j * occCount (rotorWalk L c θ x₀) i T) +
        P i j * ((occCount (rotorWalk L c θ x₀) i T : ℝ) - T * μi) := by ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add (abs_transCount_rotorWalk_sub_le hP0 hP1 hc θ x₀ i j T)
    ?_)
  rw [abs_mul, abs_of_nonneg (hP0 i j)]
  exact mul_le_mul_of_nonneg_left (abs_occCount_rotorWalk_sub_le hP0 hP1 hc θ x₀ hh hM T)
    (hP0 i j)

omit [Fintype S] in
/-- **The randomized rotor: each departure has the right law.** For an offset uniform on
`{0, …, L i − 1}`, the `k`-th departure from `i` goes to `j` for exactly `p_ij L i` of the `L i`
offsets, i.e. with probability `p_ij`. -/
theorem card_offset_eq {P : Matrix S S ℝ} {L : S → ℕ} {c : S → ℕ → S} (hc : IsRotorCycle P L c)
    (i j : S) (k : ℕ) :
    (((range (L i)).filter fun a => c i ((a + k) % L i) = j).card : ℝ) = P i j * L i := by
  have h := sum_range_add_periodic (F := fun m => if c i (m % L i) = j then (1 : ℝ) else 0)
    (L := L i) (fun m => by simp only [Nat.add_mod_right]) k
  rw [← hc.card_eq, ← sum_boole, ← sum_boole]
  have e1 : ∑ a ∈ range (L i), (if c i ((a + k) % L i) = j then (1 : ℝ) else 0) =
      ∑ m ∈ range (L i), (if c i ((k + m) % L i) = j then (1 : ℝ) else 0) :=
    sum_congr rfl fun a _ => by rw [add_comm a k]
  have e2 : ∑ m ∈ range (L i), (if c i (m % L i) = j then (1 : ℝ) else 0) =
      ∑ m ∈ range (L i), (if c i m = j then (1 : ℝ) else 0) :=
    sum_congr rfl fun m hm => by rw [Nat.mod_eq_of_lt (mem_range.1 hm)]
  rw [e1, h, e2]

/-- **Expected occupation under any randomization** of the start and the offsets is within the
Holroyd–Propp constant of `T π_s`: for weights `w ≥ 0` summing to one over finitely many
configurations `(θ, x₀)`, `|Σ w N_s(T) − T π_s| ≤ 2M (1 + Σ_i (L i − 1))`. -/
theorem abs_expected_occCount_rotorWalk_sub_le {P : Matrix S S ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    (hP1 : ∀ i, ∑ j, P i j = 1) {L : S → ℕ} {c : S → ℕ → S} (hc : IsRotorCycle P L c)
    {ι : Type*} (A : Finset ι) (w : ι → ℝ) (hw0 : ∀ a ∈ A, 0 ≤ w a) (hw1 : ∑ a ∈ A, w a = 1)
    (θ : ι → S → ℕ) (x₀ : ι → S) {h : S → ℝ} {s : S} {μs M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - μs) (hM : ∀ i, |h i| ≤ M)
    (T : ℕ) : |∑ a ∈ A, w a * (occCount (rotorWalk L c (θ a) (x₀ a)) s T : ℝ) - T * μs| ≤
      2 * M * (1 + ∑ i, ((L i - 1 : ℕ) : ℝ)) := by
  have e : ∑ a ∈ A, w a * ((occCount (rotorWalk L c (θ a) (x₀ a)) s T : ℝ) - T * μs) =
      ∑ a ∈ A, w a * (occCount (rotorWalk L c (θ a) (x₀ a)) s T : ℝ) -
        (∑ a ∈ A, w a) * (T * μs) := by
    rw [sum_mul, ← sum_sub_distrib]
    exact sum_congr rfl fun a _ => by ring
  rw [hw1, one_mul] at e
  rw [← e]
  calc |∑ a ∈ A, w a * ((occCount (rotorWalk L c (θ a) (x₀ a)) s T : ℝ) - T * μs)|
      ≤ ∑ a ∈ A, |w a * ((occCount (rotorWalk L c (θ a) (x₀ a)) s T : ℝ) - T * μs)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ A, w a * (2 * M * (1 + ∑ i, ((L i - 1 : ℕ) : ℝ))) := sum_le_sum fun a ha => by
        rw [abs_mul, abs_of_nonneg (hw0 a ha)]
        exact mul_le_mul_of_nonneg_left
          (abs_occCount_rotorWalk_sub_le hP0 hP1 hc (θ a) (x₀ a) hh hM T) (hw0 a ha)
    _ = 2 * M * (1 + ∑ i, ((L i - 1 : ℕ) : ℝ)) := by rw [← sum_mul, hw1, one_mul]

/-! ### Counterexamples -/

/-- The two-state chain of post #3 with stay probabilities `7/8` (mean spell length `8`). -/
noncomputable def twoStateStay78 : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = j then 7 / 8 else 1 / 8

/-- Its stationary distribution is `(1/2, 1/2)`. -/
theorem isStationaryDistribution_twoStateStay78 :
    IsStationaryDistribution twoStateStay78 (fun _ => 1 / 2) := by
  refine ⟨funext fun j => ?_, fun _ => by norm_num, ?_⟩
  · change ∑ i, (1 / 2 : ℝ) * twoStateStay78 i j = 1 / 2
    rw [Fin.sum_univ_two]
    fin_cases j <;> simp only [twoStateStay78] <;> norm_num
  · rw [Fin.sum_univ_two]
    norm_num

/-- **Correction: rotor counts are not exactly conditional MC's targets.** In the
`7/8`-chain, `T π_0 p_00 = 7T/16`, which no path can match when `16 ∤ T` (transition counts
are integers). -/
theorem not_transCount_eq_target (x : ℕ → Fin 2) {T : ℕ} (hT : ¬ 16 ∣ T) :
    (transCount x 0 0 T : ℝ) ≠ T * (1 / 2) * twoStateStay78 0 0 := by
  intro h
  have h00 : twoStateStay78 0 0 = 7 / 8 := by simp only [twoStateStay78, ite_true]
  rw [h00] at h
  have hR : (16 * transCount x 0 0 T : ℝ) = 7 * T := by linarith
  have hN : 16 * transCount x 0 0 T = 7 * T := by exact_mod_cast hR
  have hdvd : 16 ∣ 7 * T := ⟨_, hN.symm⟩
  exact hT ((Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) hdvd))

/-- The chain of the randomized-rotor counterexample: from state `0` go to `0` or `1` with
probability `1/2`; from state `1` go to `0`. -/
noncomputable def rotorCounterexampleChain : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = 0 then 1 / 2 else if j = 0 then 1 else 0

/-- Its stationary distribution `(2/3, 1/3)`. -/
noncomputable def rotorCounterexampleStationary : Fin 2 → ℝ :=
  fun i => if i = 0 then 2 / 3 else 1 / 3

/-- The cycle lengths of the counterexample: `2` at state `0`, `1` at state `1`. -/
def rotorCounterexampleLen : Fin 2 → ℕ := fun i => if i = 0 then 2 else 1

/-- The cycles of the counterexample: `(0, 1)` at state `0`, `(0)` at state `1`. -/
def rotorCounterexampleCycle : Fin 2 → ℕ → Fin 2 :=
  fun i m => if i = 0 then (if m % 2 = 0 then 0 else 1) else 0

/-- The offsets of the counterexample: `a` at state `0` (uniform on `{0, 1}`), `0` at state `1`
(whose cycle has length one). -/
def rotorCounterexampleOffset (a : ℕ) : Fin 2 → ℕ := fun i => if i = 0 then a else 0

/-- **Correction: the randomized rotor is not exactly unbiased for the occupation.** For the
irreducible chain `P = [[1/2, 1/2], [1, 0]]` with stationary distribution `π = (2/3, 1/3)` and
balanced cycles `(0, 1)`, `(0)`, a stationary start `x₀ ∼ π` and an offset uniform on `{0, 1}`
(independent) give `E N_0(3) = 11/6`, not `3 π_0 = 2`. -/
theorem expected_occCount_ne :
    IsStationaryDistribution rotorCounterexampleChain rotorCounterexampleStationary ∧
    (∀ i j, ∃ k, 0 < (rotorCounterexampleChain ^ k) i j) ∧
    IsRotorCycle rotorCounterexampleChain rotorCounterexampleLen rotorCounterexampleCycle ∧
    ∑ x₀ : Fin 2, ∑ a ∈ range 2, rotorCounterexampleStationary x₀ * (1 / 2) *
      (occCount (rotorWalk rotorCounterexampleLen rotorCounterexampleCycle
        (rotorCounterexampleOffset a) x₀) 0 3 : ℝ) = 11 / 6 ∧
    (11 / 6 : ℝ) ≠ 3 * rotorCounterexampleStationary 0 := by
  refine ⟨⟨funext fun j => ?_, fun i => ?_, ?_⟩, fun i j => ?_, ⟨fun i => ?_, fun i j => ?_⟩, ?_,
    ?_⟩
  · change ∑ i, rotorCounterexampleStationary i * rotorCounterexampleChain i j = _
    rw [Fin.sum_univ_two]
    fin_cases j <;>
      simp only [rotorCounterexampleStationary, rotorCounterexampleChain] <;> norm_num
  · fin_cases i <;> simp only [rotorCounterexampleStationary] <;> norm_num
  · rw [Fin.sum_univ_two]
    simp only [rotorCounterexampleStationary]
    norm_num
  · by_cases hij : i = j
    · refine ⟨0, ?_⟩
      subst hij
      rw [pow_zero, one_apply_eq]
      exact one_pos
    · refine ⟨1, ?_⟩
      rw [pow_one]
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · simp only [rotorCounterexampleChain]
        norm_num
      · simp only [rotorCounterexampleChain]
        norm_num
      · exact absurd rfl hij
  · fin_cases i <;> decide
  · fin_cases i <;> fin_cases j <;>
      simp only [rotorCounterexampleLen, rotorCounterexampleChain] <;> norm_num <;> decide +kernel
  · have h00 : occCount (rotorWalk rotorCounterexampleLen rotorCounterexampleCycle
        (rotorCounterexampleOffset 0) 0) 0 3 = 2 := by decide +kernel
    have h01 : occCount (rotorWalk rotorCounterexampleLen rotorCounterexampleCycle
        (rotorCounterexampleOffset 1) 0) 0 3 = 2 := by decide +kernel
    have h10 : occCount (rotorWalk rotorCounterexampleLen rotorCounterexampleCycle
        (rotorCounterexampleOffset 0) 1) 0 3 = 2 := by decide +kernel
    have h11 : occCount (rotorWalk rotorCounterexampleLen rotorCounterexampleCycle
        (rotorCounterexampleOffset 1) 1) 0 3 = 1 := by decide +kernel
    simp only [Fin.sum_univ_two, sum_range_succ, sum_range_zero, zero_add, h00, h01, h10, h11]
    simp only [rotorCounterexampleStationary]
    norm_num
  · simp only [rotorCounterexampleStationary]
    norm_num

end RQMCMarkov.MarkovDriving

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # Per-state stacks: departures are balanced (post #3)

Post #3: "with a separate QMC-generated uniform sequence used for the transitions out of each
state … the departures from each state are balanced, so the empirical transition matrix
converges faster than `O(1/√T)`". In the stack representation (`stackPath P x₀ v`) the `k`-th
departure from `i` goes to `step P i (v i k)`, and that departure goes to `j` iff
`v i k ∈ (cs_{i,j−1}, cs_{ij}]` (`step_lt_iff`: `step P i u < m ↔ u ≤ cs_{i,m}`, valid also at
`u = 0`). So the departures from `i` are a one-dimensional QMC sample of the row `P(i, ·)`, and
their error is controlled by the star discrepancy `D*_N` of the first `N = N_i(T)` points of
stack `i` (Niederreiter 1992, Ch. 2; L'Ecuyer 2016).

**Results** (`N = N_i(T)` departures from `i`, stack points in `[0,1)`).
* `abs_card_step_eq_sub_le`, `abs_transCount_stackPath_sub_le`:
  `|N_ij(T) − p_ij N_i(T)| ≤ 2 N D*_N(v i)`.
* `abs_sum_step_sub_le` (discrete Koksma inequality, by summation by parts),
  `abs_departureDiscrepancy_stackPath_le`: `|D_i(g, T)| ≤ V(g) · N · D*_N(v i)`, where
  `V(g) = stateVariation g = Σ_{j < n−1} |g(j+1) − g(j)|` bounds the total variation of the
  step function `u ↦ g(step P i u)` on `[0,1]` (equal to it when every `p_ij > 0`), and
  `stateVariation_le`: `V(g) ≤ 2 (n − 1) ‖g‖∞`.
* `abs_occCount_stackPath_sub_le`: `|N_s(T) − T π_s| ≤ 2‖h‖∞ + Σ_i V(h) N_i D*_{N_i}(v i)`.
* **Van der Corput stacks** (one copy of the van der Corput sequence, the one-dimensional Sobol
  sequence, for each state): with `L = ⌊log₂ T⌋ + 1`,
  - `abs_transCount_vdc_sub_le`: `|N_ij(T) − p_ij N_i(T)| ≤ 2L`;
  - `abs_occCount_vdc_sub_le`: `|N_s(T) − T π_s| ≤ 2M + n V(h) L ≤ 2M + 2n(n−1) M L`;
  - `abs_occFreq_vdc_sub_le`: occupation frequency error `≤ (2M + n V(h) L)/T`, i.e.
    `O(log T / T)` (`occFreq_vdc_isBigO`);
  - `abs_empiricalTrans_vdc_sub_le`: empirical transition matrix error
    `|N_ij/N_i − p_ij| ≤ 2(⌊log₂ N_i⌋ + 1)/N_i`, and `empiricalTrans_vdc_isBigO`: it is
    `O(log T / T)` for an irreducible chain (`N_i(T) ≥ T π_i / 2` eventually).
  This is the precise form of "faster than `O(1/√T)`" and "QMC's `O(log T / T)`" (post #3).
-/

namespace RQMCMarkov.MarkovDriving

open Finset Matrix Filter Asymptotics

variable {n : ℕ}

/-- **The inverse-CDF rule as a threshold**: for `u ≤ 1` and `m ≥ 1`,
`step P i u < m ↔ u ≤ cumProb P i m` (post #3's `u ≤ cs_{i,m}`). This also covers `u = 0`. -/
theorem step_lt_iff {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n) {u : ℝ}
    (hu : u ≤ 1) {m : ℕ} (hm : 1 ≤ m) : (step P i u : ℕ) < m ↔ u ≤ cumProb P i m := by
  have hstep : step P i u = (insert (lastState i)
      (univ.filter fun j : Fin n ↦ u ≤ cumProb P i (j + 1))).min' (insert_nonempty _ _) := rfl
  constructor
  · intro h
    have hmem := Finset.min'_mem (insert (lastState i)
      (univ.filter fun j : Fin n ↦ u ≤ cumProb P i (j + 1))) (insert_nonempty _ _)
    rw [← hstep] at hmem
    rcases mem_insert.1 hmem with hl | hf
    · have hnm : n ≤ m := by
        rw [hl] at h
        simp only [lastState] at h
        omega
      rw [cumProb_of_le P i hnm, hP.sum_eq_one i]
      exact hu
    · exact (mem_filter.1 hf).2.trans (cumProb_mono hP.nonneg i (by omega))
  · intro h
    by_cases hmn : m ≤ n
    · have hj : (⟨m - 1, by omega⟩ : Fin n) ∈ insert (lastState i)
          (univ.filter fun j : Fin n ↦ u ≤ cumProb P i (j + 1)) := by
        refine mem_insert_of_mem (mem_filter.2 ⟨mem_univ _, ?_⟩)
        have e : ((⟨m - 1, by omega⟩ : Fin n) : ℕ) + 1 = m := by
          change m - 1 + 1 = m
          omega
        rw [e]
        exact h
      have hle := Finset.min'_le _ _ hj
      rw [← hstep] at hle
      have hle' : (step P i u : ℕ) ≤ m - 1 := hle
      omega
    · exact lt_of_lt_of_le (step P i u).isLt (by omega)

/-- The number of the first `N` points of `v` whose departure from `i` goes to a state `< m`. -/
noncomputable def departuresBelow (P : Fin n → Fin n → ℝ) (i : Fin n) (v : ℕ → ℝ) (N m : ℕ) :
    ℕ :=
  ((range N).filter fun k => (step P i (v k) : ℕ) < m).card

/-- For `m ≥ 1` and points in `[0,1)`, `departuresBelow` is the counting function
`#{k < N : v k ≤ cs_{i,m}}`. -/
theorem departuresBelow_eq_countAtMost {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n)
    {v : ℕ → ℝ} {N : ℕ} (hv : InUnitIco v N) {m : ℕ} (hm : 1 ≤ m) :
    departuresBelow P i v N m = countAtMost v N (cumProb P i m) := by
  unfold departuresBelow countAtMost
  congr 1
  refine filter_congr fun k hk => ?_
  exact step_lt_iff hP i (hv k (mem_range.1 hk)).2.le hm

/-- **One threshold**: `|#{k < N : step(v k) < m} − N cs_{i,m}| ≤ N D*_N`. -/
theorem abs_departuresBelow_sub_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n)
    {v : ℕ → ℝ} {N : ℕ} (hv : InUnitIco v N) (m : ℕ) :
    |(departuresBelow P i v N m : ℝ) - N * cumProb P i m| ≤ N * starDiscrepancy v N := by
  have hD := starDiscrepancy_nonneg v N
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h0 : departuresBelow P i v N 0 = 0 := by
      unfold departuresBelow
      rw [card_eq_zero, filter_eq_empty_iff]
      intro k _ hk
      exact Nat.not_lt_zero _ hk
    rw [h0, cumProb_zero, Nat.cast_zero, mul_zero, sub_zero, abs_zero]
    positivity
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h0 : departuresBelow P i v 0 m = 0 := by
      unfold departuresBelow
      rw [range_zero, filter_empty, card_empty]
    rw [h0]
    simp only [Nat.cast_zero, zero_mul, sub_zero, abs_zero, le_refl]
  rw [departuresBelow_eq_countAtMost hP i hv hm]
  have ha := cumProb_mem_Icc hP i m
  set a := cumProb P i m with ha_def
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rcases lt_or_eq_of_le ha.2 with ha1 | ha1
  · have hup := countAtMost_div_sub_le_starDiscrepancy v N ha.1 ha1
    have hbelow : countBelow v N a ≤ countAtMost v N a := by
      apply Finset.card_le_card
      intro k hk
      rw [mem_filter] at hk ⊢
      exact ⟨hk.1, hk.2.le⟩
    have hloc := localDiscrepancy_le_starDiscrepancy v N ha
    unfold localDiscrepancy at hloc
    have hlow : a - (countBelow v N a : ℝ) / N ≤ starDiscrepancy v N :=
      (neg_le_abs _).trans' (by linarith) |>.trans hloc
    have hb : (countBelow v N a : ℝ) ≤ countAtMost v N a := by exact_mod_cast hbelow
    rw [abs_le]
    constructor
    · have : a - (countAtMost v N a : ℝ) / N ≤ starDiscrepancy v N := by
        have : (countBelow v N a : ℝ) / N ≤ (countAtMost v N a : ℝ) / N :=
          div_le_div_of_nonneg_right hb hNpos.le
        linarith
      have h2 : (N : ℝ) * (a - (countAtMost v N a : ℝ) / N) ≤ N * starDiscrepancy v N :=
        mul_le_mul_of_nonneg_left this hNpos.le
      rw [mul_sub, mul_div_cancel₀ _ hNpos.ne'] at h2
      linarith
    · have h2 : (N : ℝ) * ((countAtMost v N a : ℝ) / N - a) ≤ N * starDiscrepancy v N :=
        mul_le_mul_of_nonneg_left hup hNpos.le
      rw [mul_sub, mul_div_cancel₀ _ hNpos.ne'] at h2
      linarith
  · have hall : countAtMost v N a = N := by
      unfold countAtMost
      rw [filter_true_of_mem fun k hk => ?_, card_range]
      rw [ha1]
      exact (hv k (mem_range.1 hk)).2.le
    rw [hall, ha1, mul_one, sub_self, abs_zero]
    positivity

/-- The count of departures to `j` is a difference of two thresholds. -/
theorem card_step_eq_eq_sub (P : Fin n → Fin n → ℝ) (i : Fin n) (v : ℕ → ℝ) (N : ℕ) (j : Fin n) :
    (((range N).filter fun k => step P i (v k) = j).card : ℝ) =
      departuresBelow P i v N (j + 1) - departuresBelow P i v N j := by
  unfold departuresBelow
  rw [eq_sub_iff_add_eq, ← sum_boole, ← sum_boole, ← sum_boole, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  by_cases h1 : step P i (v k) = j
  · rw [h1]
    simp only [lt_irrefl, Nat.lt_add_one, ite_true, ite_false, add_zero]
  · have h1' : (step P i (v k) : ℕ) ≠ j := fun h => h1 (Fin.ext h)
    by_cases h2 : (step P i (v k) : ℕ) < j
    · have h3 : (step P i (v k) : ℕ) < j + 1 := by omega
      simp only [h1, h2, h3, ite_true, ite_false, zero_add]
    · have h3 : ¬ ((step P i (v k) : ℕ) < j + 1) := by omega
      simp only [h1, h2, h3, ite_false, add_zero]

/-- **Balanced departures from one stack**: `|#{k < N : step(v k) = j} − N p_ij| ≤ 2 N D*_N`. -/
theorem abs_card_step_eq_sub_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n)
    {v : ℕ → ℝ} {N : ℕ} (hv : InUnitIco v N) (j : Fin n) :
    |(((range N).filter fun k => step P i (v k) = j).card : ℝ) - P i j * N| ≤
      2 * (N * starDiscrepancy v N) := by
  rw [card_step_eq_eq_sub]
  have e : (departuresBelow P i v N (j + 1) : ℝ) - departuresBelow P i v N j - P i j * N =
      ((departuresBelow P i v N (j + 1) : ℝ) - N * cumProb P i (j + 1)) -
        ((departuresBelow P i v N j : ℝ) - N * cumProb P i j) := by
    rw [cumProb_succ]
    ring
  rw [e]
  have h1 := abs_departuresBelow_sub_le hP i hv (j + 1)
  have h2 := abs_departuresBelow_sub_le hP i hv j
  calc _ ≤ |(departuresBelow P i v N (j + 1) : ℝ) - N * cumProb P i (j + 1)| +
        |(departuresBelow P i v N j : ℝ) - N * cumProb P i j| := abs_sub _ _
    _ ≤ _ := by linarith

/-- A function on the states `Fin n`, extended by `0` to `ℕ`. -/
noncomputable def extendNat (g : Fin n → ℝ) (j : ℕ) : ℝ := if h : j < n then g ⟨j, h⟩ else 0

/-- The **variation of `g` along the state order** `V(g) = Σ_{j < n−1} |g(j+1) − g(j)|`; it
bounds the total variation on `[0,1]` of the step function `u ↦ g(step P i u)` (with equality
when every `p_ij > 0`). -/
noncomputable def stateVariation (g : Fin n → ℝ) : ℝ :=
  ∑ j ∈ range (n - 1), |extendNat g (j + 1) - extendNat g j|

/-- `0 ≤ V(g)`. -/
theorem stateVariation_nonneg (g : Fin n → ℝ) : 0 ≤ stateVariation g :=
  sum_nonneg fun _ _ => abs_nonneg _

/-- `V(g) ≤ 2 (n − 1) M` when `|g| ≤ M`. -/
theorem stateVariation_le {g : Fin n → ℝ} {M : ℝ} (hM : ∀ j, |g j| ≤ M) :
    stateVariation g ≤ 2 * (n - 1 : ℕ) * M := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    unfold stateVariation
    rw [Nat.zero_sub, range_zero, sum_empty, Nat.cast_zero, mul_zero, zero_mul]
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM ⟨0, hn⟩)
  have hext : ∀ j, |extendNat g j| ≤ M := by
    intro j
    unfold extendNat
    split_ifs with h
    · exact hM _
    · rw [abs_zero]
      exact hM0
  unfold stateVariation
  calc ∑ j ∈ range (n - 1), |extendNat g (j + 1) - extendNat g j|
      ≤ ∑ _j ∈ range (n - 1), 2 * M := sum_le_sum fun j _ => by
        have := abs_sub (extendNat g (j + 1)) (extendNat g j)
        linarith [hext (j + 1), hext j]
    _ = 2 * (n - 1 : ℕ) * M := by rw [sum_const, card_range, nsmul_eq_mul]; ring

/-- **Summation by parts.** If `B 0 = 0` then
`Σ_{j ≤ m} f_j (B_{j+1} − B_j) = f_m B_{m+1} − Σ_{j < m} (f_{j+1} − f_j) B_{j+1}`. -/
theorem sum_mul_sub_eq_abel (f B : ℕ → ℝ) (hB : B 0 = 0) (m : ℕ) :
    ∑ j ∈ range (m + 1), f j * (B (j + 1) - B j) =
      f m * B (m + 1) - ∑ j ∈ range m, (f (j + 1) - f j) * B (j + 1) := by
  induction m with
  | zero => rw [sum_range_one, range_zero, sum_empty, hB, sub_zero, sub_zero]
  | succ m ih =>
    rw [sum_range_succ, ih, sum_range_succ]
    ring

/-- **Discrete Koksma inequality for one stack**:
`|Σ_{k<N} g(step P i (v k)) − N (Pg)(i)| ≤ V(g) · N · D*_N`. -/
theorem abs_sum_step_sub_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n)
    {v : ℕ → ℝ} {N : ℕ} (hv : InUnitIco v N) (g : Fin n → ℝ) :
    |∑ k ∈ range N, (g (step P i (v k)) - (P *ᵥ g) i)| ≤
      stateVariation g * (N * starDiscrepancy v N) := by
  -- `B m = #{step < m} − N cs_m`
  set B : ℕ → ℝ := fun m => (departuresBelow P i v N m : ℝ) - N * cumProb P i m with hBdef
  have hB0 : B 0 = 0 := by
    have h0 : departuresBelow P i v N 0 = 0 := by
      unfold departuresBelow
      rw [card_eq_zero, filter_eq_empty_iff]
      intro k _ hk
      exact Nat.not_lt_zero _ hk
    simp only [hBdef, h0, cumProb_zero, Nat.cast_zero, mul_zero, sub_zero]
  have hBn : B n = 0 := by
    have hn : departuresBelow P i v N n = N := by
      unfold departuresBelow
      rw [filter_true_of_mem fun k _ => (step P i (v k)).isLt, card_range]
    simp only [hBdef, hn, cumProb_of_le P i le_rfl, hP.sum_eq_one i, mul_one, sub_self]
  have hBb : ∀ m, |B m| ≤ N * starDiscrepancy v N := abs_departuresBelow_sub_le hP i hv
  -- the sum as `Σ_j g_j (B(j+1) − B(j))`
  have e1 : ∑ k ∈ range N, (g (step P i (v k)) - (P *ᵥ g) i) =
      ∑ j : Fin n, g j * (B (j + 1) - B j) := by
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    rw [← sum_fiberwise (range N) (fun k => step P i (v k))]
    have e2 : ∀ j : Fin n, ∑ k ∈ (range N).filter (fun k => step P i (v k) = j),
        g (step P i (v k)) = g j * (((range N).filter fun k => step P i (v k) = j).card : ℝ) :=
      fun j => by
        rw [sum_congr rfl fun k hk => by rw [(mem_filter.1 hk).2], sum_const, nsmul_eq_mul,
          mul_comm]
    rw [sum_congr rfl fun j _ => e2 j]
    have e3 : (N : ℝ) * (P *ᵥ g) i = ∑ j : Fin n, g j * (P i j * N) := by
      simp only [mulVec, dotProduct, mul_sum]
      exact sum_congr rfl fun j _ => by ring
    rw [e3, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [← mul_sub, card_step_eq_eq_sub]
    congr 1
    simp only [hBdef]
    rw [cumProb_succ]
    ring
  rw [e1]
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    rw [Finset.univ_eq_empty, sum_empty, abs_zero]
    exact mul_nonneg (stateVariation_nonneg g)
      (mul_nonneg (Nat.cast_nonneg _) (starDiscrepancy_nonneg v N))
  -- to `ℕ`-indexed sums, then summation by parts
  have e4 : ∑ j : Fin n, g j * (B (j + 1) - B j) =
      ∑ j ∈ range n, extendNat g j * (B (j + 1) - B j) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => extendNat g j * (B (j + 1) - B j)) n]
    refine sum_congr rfl fun j _ => ?_
    simp only [extendNat, j.isLt, ↓reduceDIte, Fin.eta]
  rw [e4]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [sum_mul_sub_eq_abel _ B hB0 m, hBn, mul_zero, zero_sub, abs_neg]
  unfold stateVariation
  rw [Nat.add_sub_cancel, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hBb (j + 1)) (abs_nonneg _)

variable {P : Fin n → Fin n → ℝ}

/-- **Stacks balance the transitions** (post #3): in a stack path with stack points in `[0,1)`,
`|N_ij(T) − p_ij N_i(T)| ≤ 2 N D*_N(v i)`, `N = N_i(T)`. -/
theorem abs_transCount_stackPath_sub_le (hP : IsStochastic P) (x₀ : Fin n) {v : Fin n → ℕ → ℝ}
    (hv : ∀ i k, v i k ∈ Set.Ico (0 : ℝ) 1) (i j : Fin n) (T : ℕ) :
    |(transCount (stackPath P x₀ v) i j T : ℝ) - P i j * occCount (stackPath P x₀ v) i T| ≤
      2 * (occCount (stackPath P x₀ v) i T *
        starDiscrepancy (v i) (occCount (stackPath P x₀ v) i T)) := by
  rw [transCount_stackDrive]
  exact abs_card_step_eq_sub_le hP i (fun k _ => hv i k) j

/-- **Departure discrepancy of a stack path**: `|D_i(g, T)| ≤ V(g) · N · D*_N(v i)`. -/
theorem abs_departureDiscrepancy_stackPath_le (hP : IsStochastic P) (x₀ : Fin n)
    {v : Fin n → ℕ → ℝ} (hv : ∀ i k, v i k ∈ Set.Ico (0 : ℝ) 1) (g : Fin n → ℝ) (i : Fin n)
    (T : ℕ) : |departureDiscrepancy P g (stackPath P x₀ v) i T| ≤
      stateVariation g * (occCount (stackPath P x₀ v) i T *
        starDiscrepancy (v i) (occCount (stackPath P x₀ v) i T)) := by
  exact (congrArg abs (departureDiscrepancy_stackDrive P g (step P) x₀ v i T)).trans_le
    (abs_sum_step_sub_le hP i (fun k _ => hv i k) g)

/-- **Occupation error of a stack path**: `|N_s(T) − T π_s| ≤ 2M + Σ_i V(h) N_i D*_{N_i}(v i)`,
for `h − Ph = 1_{s} − π_s`, `|h| ≤ M`. -/
theorem abs_occCount_stackPath_sub_le (hP : IsStochastic P) (x₀ : Fin n) {v : Fin n → ℕ → ℝ}
    (hv : ∀ i k, v i k ∈ Set.Ico (0 : ℝ) 1) {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M)
    (T : ℕ) : |(occCount (stackPath P x₀ v) s T : ℝ) - T * c| ≤
      2 * M + ∑ i, stateVariation h * (occCount (stackPath P x₀ v) i T *
        starDiscrepancy (v i) (occCount (stackPath P x₀ v) i T)) :=
  (abs_occCount_sub_le P hh hM _ T).trans (add_le_add le_rfl
    (sum_le_sum fun i _ => abs_departureDiscrepancy_stackPath_le hP x₀ hv h i T))

/-- `N D*_N(φ) ≤ ⌊log₂ T⌋ + 1` for the van der Corput sequence `φ` and `N ≤ T`. -/
theorem mul_starDiscrepancy_vdc_le {N T : ℕ} (hNT : N ≤ T) :
    N * starDiscrepancy vanDerCorput N ≤ (Nat.log 2 T : ℝ) + 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [Nat.cast_zero, zero_mul]
    positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := starDiscrepancy_vanDerCorput_le hN
  have h2 : (N : ℝ) * starDiscrepancy vanDerCorput N ≤ (Nat.log 2 N : ℝ) + 1 := by
    rw [le_div_iff₀ hNpos] at h1
    linarith
  have h3 : (Nat.log 2 N : ℝ) ≤ Nat.log 2 T := by exact_mod_cast Nat.log_mono_right hNT
  linarith

/-- **Van der Corput stacks balance the transitions**: `|N_ij(T) − p_ij N_i(T)| ≤
2 (⌊log₂ T⌋ + 1)`. -/
theorem abs_transCount_vdc_sub_le (hP : IsStochastic P) (x₀ : Fin n) (i j : Fin n) (T : ℕ) :
    |(transCount (stackPath P x₀ fun _ => vanDerCorput) i j T : ℝ) -
        P i j * occCount (stackPath P x₀ fun _ => vanDerCorput) i T| ≤
      2 * ((Nat.log 2 T : ℝ) + 1) :=
  (abs_transCount_stackPath_sub_le hP x₀ (fun _ k => vanDerCorput_mem_Ico k) i j T).trans
    (mul_le_mul_of_nonneg_left (mul_starDiscrepancy_vdc_le (occCount_le _ _ _)) zero_le_two)

/-- **Van der Corput stacks: occupation error `O(log T)`**:
`|N_s(T) − T π_s| ≤ 2M + n V(h) (⌊log₂ T⌋ + 1)`. -/
theorem abs_occCount_vdc_sub_le (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n}
    {c M : ℝ} (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c)
    (hM : ∀ i, |h i| ≤ M) (T : ℕ) :
    |(occCount (stackPath P x₀ fun _ => vanDerCorput) s T : ℝ) - T * c| ≤
      2 * M + n * stateVariation h * ((Nat.log 2 T : ℝ) + 1) := by
  refine (abs_occCount_stackPath_sub_le hP x₀ (fun _ k => vanDerCorput_mem_Ico k) hh hM T).trans
    (add_le_add le_rfl ?_)
  calc ∑ i, stateVariation h * (occCount (stackPath P x₀ fun _ => vanDerCorput) i T *
        starDiscrepancy vanDerCorput (occCount (stackPath P x₀ fun _ => vanDerCorput) i T))
      ≤ ∑ _i : Fin n, stateVariation h * ((Nat.log 2 T : ℝ) + 1) :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (mul_starDiscrepancy_vdc_le (occCount_le _ _ _)) (stateVariation_nonneg h)
    _ = n * stateVariation h * ((Nat.log 2 T : ℝ) + 1) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **Van der Corput stacks: occupation frequency error `O(log T / T)`** (post #3, "QMC's
`O(log T / T)`"): `|N_s(T)/T − π_s| ≤ (2M + n V(h) (⌊log₂ T⌋ + 1))/T`. -/
theorem abs_occFreq_vdc_sub_le (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n}
    {c M : ℝ} (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c)
    (hM : ∀ i, |h i| ≤ M) {T : ℕ} (hT : 0 < T) :
    |(occCount (stackPath P x₀ fun _ => vanDerCorput) s T : ℝ) / T - c| ≤
      (2 * M + n * stateVariation h * ((Nat.log 2 T : ℝ) + 1)) / T := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  rw [le_div_iff₀ hTpos, ← abs_of_pos hTpos, ← abs_mul, abs_of_pos hTpos, sub_mul,
    div_mul_cancel₀ _ hTpos.ne', mul_comm c]
  exact abs_occCount_vdc_sub_le hP x₀ hh hM T

/-- **Van der Corput stacks: empirical transition matrix error**:
`|N_ij(T)/N_i(T) − p_ij| ≤ 2 (⌊log₂ T⌋ + 1)/N_i(T)` whenever `N_i(T) > 0`. -/
theorem abs_empiricalTrans_vdc_sub_le (hP : IsStochastic P) (x₀ : Fin n) (i j : Fin n) {T : ℕ}
    (hN : 0 < occCount (stackPath P x₀ fun _ => vanDerCorput) i T) :
    |(transCount (stackPath P x₀ fun _ => vanDerCorput) i j T : ℝ) /
        occCount (stackPath P x₀ fun _ => vanDerCorput) i T - P i j| ≤
      2 * ((Nat.log 2 T : ℝ) + 1) / occCount (stackPath P x₀ fun _ => vanDerCorput) i T := by
  set N := occCount (stackPath P x₀ fun _ => vanDerCorput) i T
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [le_div_iff₀ hNpos, ← abs_of_pos hNpos, ← abs_mul, abs_of_pos hNpos, sub_mul,
    div_mul_cancel₀ _ hNpos.ne']
  exact abs_transCount_vdc_sub_le hP x₀ i j T

/-- `1 ≤ log x` for `x ≥ 3`. -/
theorem one_le_log_of_three_le {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-- `(⌊log₂ T⌋ + 1) / T`-type bounds are `O(log T / T)`: if `|e T| ≤ (A + B (⌊log₂ T⌋ + 1))/T`
for `T > 0`, with `A, B ≥ 0`, then `e = O(log T / T)`. -/
theorem isBigO_log_div_of_le {e : ℕ → ℝ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (he : ∀ T : ℕ, 0 < T → |e T| ≤ (A + B * ((Nat.log 2 T : ℝ) + 1)) / T) :
    e =O[atTop] fun T : ℕ => Real.log T / T := by
  refine IsBigO.of_bound (A + 4 * B) ?_
  filter_upwards [eventually_ge_atTop 3] with T hT
  have hTpos : 0 < T := by omega
  have hTR : (3 : ℝ) ≤ T := by exact_mod_cast hT
  have hlog := one_le_log_of_three_le hTR
  have h2 := natLog_two_add_one_le hTpos
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (by linarith : (0 : ℝ) ≤ Real.log T) (Nat.cast_nonneg T)),
    mul_div_assoc']
  refine (he T hTpos).trans (div_le_div_of_nonneg_right ?_ (by positivity))
  have h3 : B * ((Nat.log 2 T : ℝ) + 1) ≤ B * (2 * (Real.log T + 1)) :=
    mul_le_mul_of_nonneg_left h2 hB
  nlinarith [mul_le_mul_of_nonneg_left hlog hA, mul_le_mul_of_nonneg_left hlog hB]

/-- **Van der Corput stacks: the occupation frequencies converge at `O(log T / T)`**
(post #3's "QMC's `O(log T / T)`"). -/
theorem occFreq_vdc_isBigO (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n}
    {c M : ℝ} (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c)
    (hM : ∀ i, |h i| ≤ M) :
    (fun T : ℕ => (occCount (stackPath P x₀ fun _ => vanDerCorput) s T : ℝ) / T - c) =O[atTop]
      fun T : ℕ => Real.log T / T :=
  isBigO_log_div_of_le (by linarith [(abs_nonneg _).trans (hM s)])
    (mul_nonneg (Nat.cast_nonneg n) (stateVariation_nonneg h))
    fun _ hT => abs_occFreq_vdc_sub_le hP x₀ hh hM hT

/-- **Van der Corput stacks: the empirical transition matrix converges at `O(log T / T)`**, for
a state `i` with `π_i = c > 0` (post #3, "faster than `O(1/√T)`"). The number of departures
`N_i(T)` is at least `T c / 2` eventually, by the occupation bound. -/
theorem empiricalTrans_vdc_isBigO (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ}
    {i : Fin n} {c M : ℝ} (hh : ∀ k, h k - (P *ᵥ h) k = (if k = i then 1 else 0) - c)
    (hM : ∀ k, |h k| ≤ M) (hc : 0 < c) (j : Fin n) :
    (fun T : ℕ => (transCount (stackPath P x₀ fun _ => vanDerCorput) i j T : ℝ) /
        occCount (stackPath P x₀ fun _ => vanDerCorput) i T - P i j) =O[atTop]
      fun T : ℕ => Real.log T / T := by
  set x := stackPath P x₀ fun _ => vanDerCorput with hx
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM i)
  set V := stateVariation h
  have hV0 : 0 ≤ (n : ℝ) * V := mul_nonneg (Nat.cast_nonneg n) (stateVariation_nonneg h)
  -- eventually `log T ≤ (c / (8 (n V + 1))) T` and `2M + 2nV ≤ T c / 4`
  have hlogo := (Real.isLittleO_log_id_atTop.bound (c := c / (8 * ((n : ℝ) * V + 1)))
    (by positivity))
  have hlogN : ∀ᶠ T : ℕ in atTop,
      Real.log T ≤ c / (8 * ((n : ℝ) * V + 1)) * T := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hlogo, eventually_ge_atTop 1]
      with T hT hT1
    have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT1
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_nonneg (Real.log_nonneg hTR),
      abs_of_nonneg (by linarith)] at hT
  have hbig : ∀ᶠ T : ℕ in atTop, 4 * (2 * M + 2 * ((n : ℝ) * V)) / c ≤ T :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  refine IsBigO.of_bound (16 / c) ?_
  filter_upwards [hlogN, hbig, eventually_ge_atTop 3] with T hlogT hbigT hT3
  have hTpos : 0 < T := by omega
  have hTR : (3 : ℝ) ≤ T := by exact_mod_cast hT3
  have hTR0 : (0 : ℝ) < T := by linarith
  have hlog1 := one_le_log_of_three_le hTR
  have h2 := natLog_two_add_one_le hTpos
  -- the occupation bound gives `N_i(T) ≥ T c / 2`
  have hocc := abs_occCount_vdc_sub_le hP x₀ hh hM T
  have hNlow : T * c / 2 ≤ (occCount x i T : ℝ) := by
    have h4 : (n : ℝ) * V * ((Nat.log 2 T : ℝ) + 1) ≤ (n : ℝ) * V * (2 * (Real.log T + 1)) :=
      mul_le_mul_of_nonneg_left h2 hV0
    have h5 : (n : ℝ) * V * (2 * Real.log T) ≤ T * c / 4 := by
      have h6 : (n : ℝ) * V * Real.log T ≤ ((n : ℝ) * V + 1) * Real.log T :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      have h7 : ((n : ℝ) * V + 1) * Real.log T ≤
          ((n : ℝ) * V + 1) * (c / (8 * ((n : ℝ) * V + 1)) * T) :=
        mul_le_mul_of_nonneg_left hlogT (by linarith)
      have h8 : ((n : ℝ) * V + 1) * (c / (8 * ((n : ℝ) * V + 1)) * T) = T * c / 8 := by
        field_simp
      linarith
    have h9 : 2 * M + 2 * ((n : ℝ) * V) ≤ T * c / 4 := by
      rw [div_le_iff₀ hc] at hbigT
      linarith
    have := (abs_le.1 hocc).1
    nlinarith
  have hNpos' : (0 : ℝ) < occCount x i T := lt_of_lt_of_le (by positivity) hNlow
  have hNpos : 0 < occCount x i T := by exact_mod_cast hNpos'
  have hb := abs_empiricalTrans_vdc_sub_le hP x₀ i j hNpos
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (by linarith) hTR0.le)]
  refine hb.trans ?_
  rw [div_le_iff₀ hNpos']
  have h10 : 2 * ((Nat.log 2 T : ℝ) + 1) ≤ 8 * Real.log T := by linarith
  have h11 : 16 / c * (Real.log T / T) * (T * c / 2) = 8 * Real.log T := by
    field_simp
    ring
  have h12 : 0 ≤ 16 / c * (Real.log T / T) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hNlow h12]

end RQMCMarkov.MarkovDriving

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # The Monte Carlo baseline: the law of the iterated logarithm rate (post #3)

Post #3: "With MC of a Markov Chain the empirical transition matrix converges at `O(1/√T)`
(Meyn & Tweedie, Chpt 17)." In the stack representation with **i.i.d. uniform stacks**
(`IsIIDStacks`; by `DrivingMC` this is the law of MC driving by one i.i.d. sequence), the
departures from `i` are i.i.d. draws from the row `P(i, ·)`, so for a test function `g` the
departure discrepancy is a random-index partial sum `D_i(g, T) = S_{N_i(T)}` of the i.i.d.
centred bounded variables `ξ_k = g(step P i (V i k)) − (Pg)(i)`, with variance
`σ_i²(g) = Σ_j p_ij (g_j − (Pg)(i))²` (`rowVariance`; `= p_ij (1 − p_ij)` for `g = 1_{j}`,
`rowVariance_indicator`). The Hartman–Wintner LIL (copied from `StochasticStability`) gives the
precise almost-sure rate, with `lilScale m = √(2 m log log m)`:

* `hasLIL_mcDepartureSum`: a.s. `limsup S_m / √(2 m log log m) = σ_i(g)`, `liminf = −σ_i(g)`.
* `ae_abs_transCount_mc_le` (**upper rate**): a.s. for every `ε > 0` there is `K` with
  `|N_ij(T) − p_ij N_i(T)| ≤ K + (√(p_ij(1 − p_ij)) + ε) √(2 T log log T)` for all `T`
  (using the random index `N_i(T) ≤ T`); so the empirical transition matrix error is
  `O(√(log log T / T))` a.s.
* `ae_abs_occCount_mc_le`: the occupation error is a.s. `≤ K + C √(2 T log log T)`, with
  `C = Σ_i (σ_i(h) + 1)`; `ae_abs_occCount_mc_le_mul`: the occupation SLLN (`≤ K + ε T` for every
  `ε > 0`), and `ae_tendsto_occCount_mc`: every state with `π_i > 0` is visited infinitely
  often.
* `ae_frequently_transCount_mc_ge` (**lower rate**): if moreover `π_i > 0`, a.s. for every
  `ε > 0`, infinitely often `N_ij(T) − p_ij N_i(T) ≥ (σ − ε) √(2 N log log N)` and infinitely
  often `≤ −(σ − ε) √(2 N log log N)`, with `N = N_i(T)` and `σ = √(p_ij(1 − p_ij))`. So for
  `0 < p_ij < 1` the MC error is not `o(√(N log log N))` (`ae_not_tendsto_transCount_mc`), and MC
  is genuinely slower than the stacks' `O(log T)` and the rotors' `O(1)`.

**Reading of "`O(1/√T)`".** The a.s. error of the empirical transition matrix is of exact
order `√(log log T / T)` (LIL), slightly larger than `1/√T`; `1/√T` is the scale of the CLT
(the root-mean-square error), not an almost-sure bound.

**The unifying statement** (`occupation_error_ranking`, `departureDiscrepancy_ranking`): along
every path, occupation error `≤ 2‖h‖∞ + Σ_i |D_i(h, T)|`; the departure discrepancies are
`O(√(T log log T))` a.s. for MC, `O(log T)` for van der Corput stacks, and `O(1)` for rotors.

`isIIDStacks_iidUniform`: the canonical stack model (`iidUniform (Fin n × ℕ)`) satisfies
`IsIIDStacks`. The LIL itself is the `StochasticStability/LimitTheorems` closure, copied into
the `MCRate*` modules.
-/

namespace RQMCMarkov.MarkovDriving

open MeasureTheory ProbabilityTheory Filter Finset Matrix

/-! ### Deterministic lemmas: random indices -/

/-- **Random index bound.** If eventually `|s m| ≤ f m` with `f ≥ 0` eventually monotone, then
there is `K ≥ 0` with `|s N| ≤ K + f T` whenever `N ≤ T`. -/
theorem exists_abs_le_add_of_eventually {s f : ℕ → ℝ} (hf0 : ∀ m, 0 ≤ f m)
    (h : ∀ᶠ m in atTop, |s m| ≤ f m ∧ ∀ m', m ≤ m' → f m ≤ f m') :
    ∃ K, 0 ≤ K ∧ ∀ T N, N ≤ T → |s N| ≤ K + f T := by
  obtain ⟨m0, hm0⟩ := eventually_atTop.1 h
  have hK := sum_nonneg fun m (_ : m ∈ range m0) => abs_nonneg (s m)
  refine ⟨∑ m ∈ range m0, |s m|, hK, fun T N hNT => ?_⟩
  by_cases hN : N < m0
  · have := single_le_sum (fun m _ => abs_nonneg (s m)) (mem_range.2 hN)
    linarith [hf0 T]
  · obtain ⟨h1, h2⟩ := hm0 N (not_lt.1 hN)
    have := h2 T hNT
    linarith

/-- `√(2 m log log m)` is eventually monotone. -/
theorem eventually_lilScale_mono :
    ∀ᶠ m : ℕ in atTop, ∀ m', m ≤ m' → lilScale m ≤ lilScale m' := by
  filter_upwards [lil_eventually_le_log 3] with m hm m' hmm' using lilScale_mono hm hmm'

/-- `√(2 m log log m) = o(m)`: eventually `lilScale m ≤ ε m`. -/
theorem eventually_lilScale_le_mul {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, lilScale m ≤ ε * m := by
  have hlogo := Real.isLittleO_log_id_atTop.bound (c := ε ^ 2 / 2) (by positivity)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hlogo, eventually_ge_atTop 3]
    with m hm hm3
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm3
  have hlogpos : 0 < Real.log m := Real.log_pos (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_pos hlogpos,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ m)] at hm
  have hll : Real.log (Real.log m) ≤ Real.log m :=
    (Real.log_le_sub_one_of_pos hlogpos).trans (by linarith)
  unfold lilScale
  rw [show ε * (m : ℝ) = √((ε * m) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
  apply Real.sqrt_le_sqrt
  have h1 : 2 * (m : ℝ) * Real.log (Real.log m) ≤ 2 * m * Real.log m :=
    mul_le_mul_of_nonneg_left hll (by positivity)
  have h2 : 2 * (m : ℝ) * Real.log m ≤ 2 * m * (ε ^ 2 / 2 * m) :=
    mul_le_mul_of_nonneg_left hm (by positivity)
  nlinarith

/-- **Discrete intermediate values**: a counter with unit up-steps takes every value between
`N a` and `N b`. -/
theorem exists_eq_of_le_of_le {N : ℕ → ℕ} (hN : ∀ T, N (T + 1) ≤ N T + 1) {a b v : ℕ}
    (hab : a ≤ b) (ha : N a ≤ v) (hb : v ≤ N b) : ∃ T, a ≤ T ∧ T ≤ b ∧ N T = v := by
  induction b, hab using Nat.le_induction with
  | base => exact ⟨a, le_rfl, le_rfl, le_antisymm ha hb⟩
  | succ b hab ih =>
    by_cases hv : v ≤ N b
    · obtain ⟨T, h1, h2, h3⟩ := ih hv
      exact ⟨T, h1, by omega, h3⟩
    · exact ⟨b + 1, by omega, le_rfl, by have := hN b; omega⟩

/-- **Transfer of "infinitely often" through a random index**: if `N` is monotone with unit
up-steps and unbounded, and `p m` holds for infinitely many `m`, then `p (N T)` holds for
infinitely many `T`. -/
theorem frequently_comp_of_unbounded {N : ℕ → ℕ} (hmono : Monotone N)
    (hN : ∀ T, N (T + 1) ≤ N T + 1) (hunb : ∀ v, ∃ T, v ≤ N T) {p : ℕ → Prop}
    (hp : ∃ᶠ m in atTop, p m) : ∃ᶠ T in atTop, p (N T) := by
  rw [frequently_atTop] at hp ⊢
  intro T0
  obtain ⟨m, hm, hpm⟩ := hp (N T0)
  obtain ⟨T1, hT1⟩ := hunb m
  obtain ⟨T, h1, -, h3⟩ := exists_eq_of_le_of_le hN (le_max_left T0 T1) hm
    (hT1.trans (hmono (le_max_right T0 T1)))
  exact ⟨T, h1, h3 ▸ hpm⟩

/-! ### i.i.d. stacks -/

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

/-- **i.i.d. uniform stacks**: for each state `i`, the stack `k ↦ V i k` is an i.i.d. sequence
of uniforms on `[0,1)` (independence across states is not needed below). -/
structure IsIIDStacks (Q : Measure Ω) (V : Ω → Fin n → ℕ → ℝ) : Prop where
  measurable : ∀ i k, Measurable fun ω => V ω i k
  indep : ∀ i, iIndepFun (fun k ω => V ω i k) Q
  law : ∀ i k, Q.map (fun ω => V ω i k) = uniformIco

/-- **The canonical i.i.d. stacks** of `DrivingMC`: under `iidUniform (Fin n × ℕ)`, the stacks
`V w i k = w (i, k)` are i.i.d. uniform, so every result below applies to the stack model
`stackPath P x₀ (Function.curry w)` (whose finite-horizon path laws are those of MC driving by a
single i.i.d. sequence, `map_drivenPath_eq_map_stackPath`). -/
theorem isIIDStacks_iidUniform :
    IsIIDStacks (iidUniform (Fin n × ℕ)) (fun w => Function.curry w) := by
  have := isProbabilityMeasure_uniformIco
  refine ⟨fun i k => measurable_pi_apply (i, k), fun i => ?_, fun i k => ?_⟩
  · have h := iIndepFun_infinitePi (P := fun _ : Fin n × ℕ => uniformIco)
      (X := fun _ x => x) (fun _ => measurable_id)
    exact h.precomp (g := fun k => (i, k)) fun a b hab => (Prod.mk.inj hab).2
  · exact Measure.infinitePi_map_eval (μ := fun _ : Fin n × ℕ => uniformIco) (i, k)

/-- The **MC departure process** of state `i`: `S_m = Σ_{k < m} (g(step P i (V i k)) − (Pg)(i))`.
-/
noncomputable def mcDepartureSum (P : Fin n → Fin n → ℝ) (g : Fin n → ℝ)
    (V : Ω → Fin n → ℕ → ℝ) (i : Fin n) (ω : Ω) (m : ℕ) : ℝ :=
  ∑ k ∈ range m, (g (step P i (V ω i k)) - (P *ᵥ g) i)

/-- The variance of `g` under the row `P(i, ·)`: `σ_i²(g) = Σ_j p_ij (g_j − (Pg)(i))²`. -/
noncomputable def rowVariance (P : Fin n → Fin n → ℝ) (g : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j, P i j * (g j - (P *ᵥ g) i) ^ 2

/-- For an indicator, `σ_i²(1_{j}) = p_ij (1 − p_ij)`. -/
theorem rowVariance_indicator {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i j : Fin n) :
    rowVariance P (fun k => if k = j then 1 else 0) i = P i j * (1 - P i j) := by
  unfold rowVariance
  rw [mulVec_indicator (P : Matrix (Fin n) (Fin n) ℝ) i j]
  have e : ∀ k, P i k * ((if k = j then (1 : ℝ) else 0) - P i j) ^ 2 =
      (1 - 2 * P i j) * (P i k * if k = j then 1 else 0) + P i j ^ 2 * P i k := fun k => by
    split_ifs <;> ring
  rw [sum_congr rfl fun k _ => e k, sum_add_distrib, ← mul_sum, ← mul_sum, hP.sum_eq_one i]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', mem_univ, ite_true]
  ring

/-- **The law of one departure**: `E φ(step P i (V i k)) = Σ_j p_ij φ_j`. -/
theorem integral_comp_step {Q : Measure Ω} [IsProbabilityMeasure Q] {V : Ω → Fin n → ℕ → ℝ}
    (hV : IsIIDStacks Q V) {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n) (k : ℕ)
    (φ : Fin n → ℝ) : ∫ ω, φ (step P i (V ω i k)) ∂Q = ∑ j, P i j * φ j := by
  have hmeas : Measurable fun ω => step P i (V ω i k) :=
    (measurable_step P i).comp (hV.measurable i k)
  rw [← integral_map hmeas.aemeasurable (measurable_of_finite φ).aestronglyMeasurable]
  rw [integral_fintype Integrable.of_finite]
  refine sum_congr rfl fun j _ => ?_
  rw [smul_eq_mul, measureReal_def, Measure.map_apply hmeas (measurableSet_singleton j)]
  have e : (fun ω => step P i (V ω i k)) ⁻¹' {j} =
      (fun ω => V ω i k) ⁻¹' {u | step P i u = j} := rfl
  have hms : MeasurableSet {u | step P i u = j} :=
    (measurable_step P i) (measurableSet_singleton j)
  rw [e, ← Measure.map_apply (hV.measurable i k) hms, hV.law i k, uniformIco_step_eq hP i j,
    ENNReal.toReal_ofReal (hP.nonneg i j)]

/-- **The LIL for the MC departures**: almost surely the departure process of `i` obeys the LIL
with constant `σ_i(g) = √(rowVariance P g i)`. -/
theorem hasLIL_mcDepartureSum {Q : Measure Ω} [IsProbabilityMeasure Q]
    {V : Ω → Fin n → ℕ → ℝ} (hV : IsIIDStacks Q V) {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (g : Fin n → ℝ) (i : Fin n) :
    ∀ᵐ ω ∂Q, HasLIL (mcDepartureSum P g V i ω) (√(rowVariance P g i)) := by
  set c := (P *ᵥ g) i with hc
  set ψ : ℝ → ℝ := fun u => g (step P i u) - c with hψdef
  have hψ : Measurable ψ := (measurable_of_finite fun j => g j - c).comp (measurable_step P i)
  set X : ℕ → Ω → ℝ := fun k ω => ψ (V ω i k) with hX
  have hind : iIndepFun X Q := (hV.indep i).comp (fun _ => ψ) fun _ => hψ
  have hm : ∀ k, Measurable (X k) := fun k => hψ.comp (hV.measurable i k)
  have hident : ∀ k, IdentDistrib (X k) (X 0) Q Q := fun k =>
    (IdentDistrib.mk (hV.measurable i k).aemeasurable (hV.measurable i 0).aemeasurable
      (by rw [hV.law i k, hV.law i 0])).comp hψ
  have hL2 : MemLp (X 0) 2 Q := by
    refine MemLp.of_bound (hm 0).aestronglyMeasurable (∑ j, |g j - c|)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact single_le_sum (f := fun j => |g j - c|) (fun j _ => abs_nonneg _) (mem_univ _)
  have h0 : ∫ ω, X 0 ω ∂Q = 0 := by
    rw [integral_comp_step hV hP i 0 (fun j => g j - c)]
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hP.sum_eq_one i, one_mul]
    rw [hc]
    simp only [mulVec, dotProduct]
    exact sub_self _
  have hvar : ∫ ω, X 0 ω ^ 2 ∂Q = rowVariance P g i :=
    integral_comp_step hV hP i 0 (fun j => (g j - c) ^ 2)
  have hlil := hasLIL_iid hind hm hident hL2 h0
  rw [hvar] at hlil
  exact hlil

omit [MeasurableSpace Ω] in
/-- The departure discrepancy of the MC stack path is the departure process at the random
index `N_i(T)`. -/
theorem departureDiscrepancy_mc_eq (P : Fin n → Fin n → ℝ) (x₀ : Fin n)
    (V : Ω → Fin n → ℕ → ℝ) (g : Fin n → ℝ) (i : Fin n) (ω : Ω) (T : ℕ) :
    departureDiscrepancy P g (stackPath P x₀ (V ω)) i T =
      mcDepartureSum P g V i ω (occCount (stackPath P x₀ (V ω)) i T) :=
  departureDiscrepancy_stackDrive P g (step P) x₀ (V ω) i T

/-- Under the LIL with constant `σ`, eventually `|s m| ≤ (σ + ε) √(2 m log log m)`. -/
theorem HasLIL.eventually_abs_le {s : ℕ → ℝ} {σ : ℝ} (h : HasLIL s σ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m in atTop, |s m| ≤ (σ + ε) * lilScale m := by
  filter_upwards [(h.1 ε hε).1, (h.2 ε hε).1] with m h1 h2
  exact abs_le.2 ⟨by linarith, h1⟩

/-- **MC departure discrepancies are `O(√(T log log T))` a.s.**: for every `ε > 0` there is `K`
with `|D_i(g, T)| ≤ K + (σ_i(g) + ε) √(2 T log log T)` for all `T`. -/
theorem ae_abs_departureDiscrepancy_mc_le {Q : Measure Ω} [IsProbabilityMeasure Q]
    {V : Ω → Fin n → ℕ → ℝ} (hV : IsIIDStacks Q V) {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (x₀ : Fin n) (g : Fin n → ℝ) (i : Fin n) :
    ∀ᵐ ω ∂Q, ∀ ε > 0, ∃ K, ∀ T, |departureDiscrepancy P g (stackPath P x₀ (V ω)) i T| ≤
      K + (√(rowVariance P g i) + ε) * lilScale T := by
  filter_upwards [hasLIL_mcDepartureSum hV hP g i] with ω hω ε hε
  have hσε : 0 ≤ √(rowVariance P g i) + ε := by positivity
  obtain ⟨K, -, hK⟩ := exists_abs_le_add_of_eventually
    (f := fun m => (√(rowVariance P g i) + ε) * lilScale m)
    (fun m => mul_nonneg hσε (lilScale_nonneg m))
    ((hω.eventually_abs_le hε).and (eventually_lilScale_mono.mono fun m hm m' hmm' =>
      mul_le_mul_of_nonneg_left (hm m' hmm') hσε))
  exact ⟨K, fun T => by
    rw [departureDiscrepancy_mc_eq]
    exact hK T _ (occCount_le _ _ _)⟩

/-- **MC departure discrepancies are `o(T)` a.s.**: for every `ε > 0` there is `K` with
`|D_i(g, T)| ≤ K + ε T` for all `T`. -/
theorem ae_abs_departureDiscrepancy_mc_le_mul {Q : Measure Ω} [IsProbabilityMeasure Q]
    {V : Ω → Fin n → ℕ → ℝ} (hV : IsIIDStacks Q V) {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (x₀ : Fin n) (g : Fin n → ℝ) (i : Fin n) :
    ∀ᵐ ω ∂Q, ∀ ε > 0, ∃ K, ∀ T, |departureDiscrepancy P g (stackPath P x₀ (V ω)) i T| ≤
      K + ε * T := by
  filter_upwards [hasLIL_mcDepartureSum hV hP g i] with ω hω ε hε
  set σ := √(rowVariance P g i)
  have hσ : 0 ≤ σ := Real.sqrt_nonneg _
  have hev : ∀ᶠ m in atTop, |mcDepartureSum P g V i ω m| ≤ ε * m := by
    filter_upwards [hω.eventually_abs_le one_pos,
      eventually_lilScale_le_mul (ε := ε / (σ + 1)) (by positivity)] with m h1 h2
    have h3 : (σ + 1) * lilScale m ≤ (σ + 1) * (ε / (σ + 1) * m) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : (σ + 1) * (ε / (σ + 1) * m) = ε * m := by field_simp
    linarith
  obtain ⟨K, -, hK⟩ := exists_abs_le_add_of_eventually (f := fun m => ε * m)
    (fun m => mul_nonneg hε.le (Nat.cast_nonneg m))
    (hev.mono fun m hm => ⟨hm, fun m' hmm' => mul_le_mul_of_nonneg_left
      (by exact_mod_cast hmm') hε.le⟩)
  exact ⟨K, fun T => by
    rw [departureDiscrepancy_mc_eq]
    exact hK T _ (occCount_le _ _ _)⟩

/-- **MC transition counts, upper LIL rate** (post #3's "`O(1/√T)`", made precise): a.s., for
every `ε > 0` there is `K` with `|N_ij(T) − p_ij N_i(T)| ≤ K + (√(p_ij (1 − p_ij)) + ε)
√(2 T log log T)` for all `T`. -/
theorem ae_abs_transCount_mc_le {Q : Measure Ω} [IsProbabilityMeasure Q]
    {V : Ω → Fin n → ℕ → ℝ} (hV : IsIIDStacks Q V) {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (x₀ : Fin n) (i j : Fin n) :
    ∀ᵐ ω ∂Q, ∀ ε > 0, ∃ K, ∀ T,
      |(transCount (stackPath P x₀ (V ω)) i j T : ℝ) - P i j * occCount (stackPath P x₀ (V ω)) i T|
        ≤ K + (√(P i j * (1 - P i j)) + ε) * lilScale T := by
  filter_upwards [ae_abs_departureDiscrepancy_mc_le hV hP x₀ (fun k => if k = j then 1 else 0) i]
    with ω hω ε hε
  obtain ⟨K, hK⟩ := hω ε hε
  refine ⟨K, fun T => ?_⟩
  rw [transCount_sub_eq_departureDiscrepancy (P : Matrix (Fin n) (Fin n) ℝ) _ i j T,
    ← rowVariance_indicator hP i j]
  exact hK T

/-- **MC occupation error, LIL rate**: a.s. `|N_s(T) − T π_s| ≤ K + C √(2 T log log T)` for all
`T`, with `C = Σ_i (σ_i(h) + 1)`, where `h − Ph = 1_{s} − π_s` and `|h| ≤ M`. -/
theorem ae_abs_occCount_mc_le {Q : Measure Ω} [IsProbabilityMeasure Q]
    {V : Ω → Fin n → ℕ → ℝ} (hV : IsIIDStacks Q V) {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n} {μs M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - μs) (hM : ∀ i, |h i| ≤ M) :
    ∀ᵐ ω ∂Q, ∃ K, ∀ T, |(occCount (stackPath P x₀ (V ω)) s T : ℝ) - T * μs| ≤
      K + (∑ i, (√(rowVariance P h i) + 1)) * lilScale T := by
  have hall := ae_all_iff.2 fun i => ae_abs_departureDiscrepancy_mc_le hV hP x₀ h i
  filter_upwards [hall] with ω hω
  choose K hK using fun i => hω i 1 one_pos
  refine ⟨2 * M + ∑ i, K i, fun T => ?_⟩
  refine (abs_occCount_sub_le P hh hM _ T).trans ?_
  have := sum_le_sum fun i (_ : i ∈ univ) => hK i T
  rw [sum_add_distrib, ← sum_mul] at this
  linarith

/-- **MC occupation SLLN**: a.s., for every `ε > 0` there is `K` with
`|N_s(T) − T π_s| ≤ K + ε T` for all `T`. -/
theorem ae_abs_occCount_mc_le_mul {Q : Measure Ω} [IsProbabilityMeasure Q]
    {V : Ω → Fin n → ℕ → ℝ} (hV : IsIIDStacks Q V) {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n} {μs M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - μs) (hM : ∀ i, |h i| ≤ M) :
    ∀ᵐ ω ∂Q, ∀ ε > 0, ∃ K, ∀ T, |(occCount (stackPath P x₀ (V ω)) s T : ℝ) - T * μs| ≤
      K + ε * T := by
  have hall := ae_all_iff.2 fun i => ae_abs_departureDiscrepancy_mc_le_mul hV hP x₀ h i
  filter_upwards [hall] with ω hω ε hε
  choose K hK using fun i => hω i (ε / (n + 1)) (by positivity)
  refine ⟨2 * M + ∑ i, K i, fun T => ?_⟩
  refine (abs_occCount_sub_le P hh hM _ T).trans ?_
  have := sum_le_sum fun i (_ : i ∈ univ) => hK i T
  rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  have hle : (n : ℝ) * (ε / (n + 1) * T) ≤ ε * T := by
    have hn1 : (n : ℝ) / (n + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have : (n : ℝ) * (ε / (n + 1) * T) = (n / (n + 1)) * (ε * T) := by ring
    rw [this]
    exact mul_le_of_le_one_left (by positivity) hn1
  linarith

/-- **MC visits every charged state infinitely often** (a.s.): if `π_s > 0` then
`N_s(T) → ∞`. -/
theorem ae_tendsto_occCount_mc {Q : Measure Ω} [IsProbabilityMeasure Q]
    {V : Ω → Fin n → ℕ → ℝ} (hV : IsIIDStacks Q V) {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n} {μs M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - μs) (hM : ∀ i, |h i| ≤ M)
    (hμ : 0 < μs) :
    ∀ᵐ ω ∂Q, ∀ v : ℕ, ∃ T, v ≤ occCount (stackPath P x₀ (V ω)) s T := by
  filter_upwards [ae_abs_occCount_mc_le_mul hV hP x₀ hh hM] with ω hω v
  obtain ⟨K, hK⟩ := hω (μs / 2) (by positivity)
  obtain ⟨T, hT⟩ := exists_nat_gt (2 * (K + v) / μs)
  refine ⟨T, ?_⟩
  have h1 := (abs_le.1 (hK T)).1
  have h2 : 2 * (K + v) < T * μs := by rwa [div_lt_iff₀ hμ] at hT
  have : (v : ℝ) ≤ occCount (stackPath P x₀ (V ω)) s T := by nlinarith
  exact_mod_cast this

/-- **MC transition counts, lower LIL rate**: if `π_i > 0` (e.g. `P` irreducible), a.s. for
every `ε > 0`, infinitely often `N_ij(T) − p_ij N_i(T) ≥ (σ − ε) √(2 N log log N)`, and
infinitely often `N_ij(T) − p_ij N_i(T) ≤ −(σ − ε) √(2 N log log N)`, where `N = N_i(T)` and
`σ = √(p_ij (1 − p_ij))`. -/
theorem ae_frequently_transCount_mc_ge {Q : Measure Ω} [IsProbabilityMeasure Q]
    {V : Ω → Fin n → ℕ → ℝ} (hV : IsIIDStacks Q V) {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ} {i : Fin n} {μi M : ℝ}
    (hh : ∀ k, h k - (P *ᵥ h) k = (if k = i then 1 else 0) - μi) (hM : ∀ k, |h k| ≤ M)
    (hμ : 0 < μi) (j : Fin n) :
    ∀ᵐ ω ∂Q, ∀ ε > 0,
      (∃ᶠ T in atTop, (√(P i j * (1 - P i j)) - ε) *
          lilScale (occCount (stackPath P x₀ (V ω)) i T) ≤
        (transCount (stackPath P x₀ (V ω)) i j T : ℝ) -
          P i j * occCount (stackPath P x₀ (V ω)) i T) ∧
      ∃ᶠ T in atTop, (transCount (stackPath P x₀ (V ω)) i j T : ℝ) -
          P i j * occCount (stackPath P x₀ (V ω)) i T ≤
        -((√(P i j * (1 - P i j)) - ε) * lilScale (occCount (stackPath P x₀ (V ω)) i T)) := by
  filter_upwards [hasLIL_mcDepartureSum hV hP (fun k => if k = j then 1 else 0) i,
    ae_tendsto_occCount_mc hV hP x₀ hh hM hμ] with ω hω hunb ε hε
  rw [rowVariance_indicator hP i j] at hω
  set x := stackPath P x₀ (V ω)
  have hmono : Monotone fun T => occCount x i T := fun _ _ hab => occCount_mono x i hab
  have hstep : ∀ T, occCount x i (T + 1) ≤ occCount x i T + 1 := fun T => by
    rw [occCount_succ]
    split_ifs <;> omega
  have e : ∀ T, (transCount x i j T : ℝ) - P i j * occCount x i T =
      mcDepartureSum P (fun k => if k = j then 1 else 0) V i ω (occCount x i T) := fun T => by
    rw [transCount_sub_eq_departureDiscrepancy (P : Matrix (Fin n) (Fin n) ℝ) x i j T,
      departureDiscrepancy_mc_eq]
  refine ⟨?_, ?_⟩
  · refine (frequently_comp_of_unbounded hmono hstep hunb (hω.1 ε hε).2).mono fun T hT => ?_
    rw [e T]
    exact hT
  · refine (frequently_comp_of_unbounded hmono hstep hunb (hω.2 ε hε).2).mono fun T hT => ?_
    rw [e T]
    linarith

/-- **MC is not `o(√(N log log N))`-accurate**: for `0 < p_ij < 1` and `π_i > 0`, almost surely
`(N_ij(T) − p_ij N_i(T)) / √(2 N_i(T) log log N_i(T))` does not tend to `0`. -/
theorem ae_not_tendsto_transCount_mc {Q : Measure Ω} [IsProbabilityMeasure Q]
    {V : Ω → Fin n → ℕ → ℝ} (hV : IsIIDStacks Q V) {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ} {i : Fin n} {μi M : ℝ}
    (hh : ∀ k, h k - (P *ᵥ h) k = (if k = i then 1 else 0) - μi) (hM : ∀ k, |h k| ≤ M)
    (hμ : 0 < μi) {j : Fin n} (hp0 : 0 < P i j) (hp1 : P i j < 1) :
    ∀ᵐ ω ∂Q, ¬ Tendsto (fun T => ((transCount (stackPath P x₀ (V ω)) i j T : ℝ) -
        P i j * occCount (stackPath P x₀ (V ω)) i T) /
          lilScale (occCount (stackPath P x₀ (V ω)) i T)) atTop (nhds 0) := by
  filter_upwards [ae_frequently_transCount_mc_ge hV hP x₀ hh hM hμ j,
    ae_tendsto_occCount_mc hV hP x₀ hh hM hμ] with ω hω hunb htend
  set x := stackPath P x₀ (V ω)
  set σ := √(P i j * (1 - P i j))
  have hσ : 0 < σ := Real.sqrt_pos.2 (mul_pos hp0 (by linarith))
  obtain ⟨hfr, -⟩ := hω (σ / 2) (by positivity)
  have hsmall := htend.eventually (gt_mem_nhds (show (0 : ℝ) < σ / 2 by positivity))
  have htop : Tendsto (fun T => occCount x i T) atTop atTop :=
    tendsto_atTop_atTop_of_monotone (fun _ _ hab => occCount_mono x i hab) hunb
  have hpos : ∀ᶠ T in atTop, 0 < lilScale (occCount x i T) :=
    (htop.eventually (lil_eventually_le_log 3)).mono fun T hT => lilScale_pos hT
  obtain ⟨T, hT1, hT2, hT3⟩ := (hfr.and_eventually (hsmall.and hpos)).exists
  have h2 := hT2
  rw [div_lt_iff₀ hT3] at h2
  nlinarith

/-! ### The unifying statement -/

/-- **The ranking of post #3, for the departure discrepancies.** For a stochastic `P` and a test
function `g` with `|g| ≤ M`:
1. van der Corput stacks: `|D_i(g, T)| ≤ V(g) (⌊log₂ T⌋ + 1)`, i.e. `O(log T)`;
2. rotors (balanced cycles of lengths `L`): `|D_i(g, T)| ≤ 2 (L i − 1) M`, i.e. `O(1)`;
3. MC (i.i.d. uniform stacks): a.s., for every `ε > 0`, `|D_i(g, T)| ≤ K + (σ_i(g) + ε)
   √(2 T log log T)`, i.e. `O(√(T log log T))`. -/
theorem departureDiscrepancy_ranking {Q : Measure Ω} [IsProbabilityMeasure Q]
    {V : Ω → Fin n → ℕ → ℝ} {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (x₀ : Fin n)
    {g : Fin n → ℝ} {M : ℝ} (hM : ∀ j, |g j| ≤ M) (i : Fin n) :
    (∀ T, |departureDiscrepancy P g (stackPath P x₀ fun _ => vanDerCorput) i T| ≤
        stateVariation g * ((Nat.log 2 T : ℝ) + 1)) ∧
      (∀ (L : Fin n → ℕ) (c : Fin n → ℕ → Fin n), IsRotorCycle P L c → ∀ θ T,
        |departureDiscrepancy P g (rotorWalk L c θ x₀) i T| ≤ (L i - 1 : ℕ) * (2 * M)) ∧
      (IsIIDStacks Q V → ∀ᵐ ω ∂Q, ∀ ε > 0, ∃ K, ∀ T,
        |departureDiscrepancy P g (stackPath P x₀ (V ω)) i T| ≤
          K + (√(rowVariance P g i) + ε) * lilScale T) := by
  refine ⟨fun T => ?_, fun L c hc θ T => ?_,
    fun hV => ae_abs_departureDiscrepancy_mc_le hV hP x₀ g i⟩
  · exact (abs_departureDiscrepancy_stackPath_le hP x₀ (fun _ k => vanDerCorput_mem_Ico k) g i
      T).trans (mul_le_mul_of_nonneg_left (mul_starDiscrepancy_vdc_le (occCount_le _ _ _))
        (stateVariation_nonneg g))
  · exact abs_departureDiscrepancy_rotorWalk_le_two_mul hP.nonneg hP.sum_eq_one hc θ x₀ hM i T

/-- **The unifying theorem** (post #3's ranking of MC, QMC stacks and rotors). Let `h` solve
Poisson's equation `h − Ph = 1_{s} − π_s` with `|h| ≤ M`. Then:
0. along **every** path, `|N_s(T) − T π_s| ≤ 2M + Σ_i |D_i(h, T)|` (boundary + departure
   discrepancies);
1. van der Corput stacks: `|N_s(T) − T π_s| ≤ 2M + n V(h) (⌊log₂ T⌋ + 1)` (`O(log T)`);
2. rotors: `|N_s(T) − T π_s| ≤ 2M (1 + Σ_i (L i − 1))` (`O(1)`, Holroyd–Propp);
3. MC: a.s. `|N_s(T) − T π_s| ≤ K + C √(2 T log log T)` (`O(√(T log log T))`). -/
theorem occupation_error_ranking {Q : Measure Ω} [IsProbabilityMeasure Q]
    {V : Ω → Fin n → ℕ → ℝ} {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (x₀ : Fin n)
    {h : Fin n → ℝ} {s : Fin n} {μs M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - μs) (hM : ∀ i, |h i| ≤ M) :
    (∀ (x : ℕ → Fin n) T, |(occCount x s T : ℝ) - T * μs| ≤
        2 * M + ∑ i, |departureDiscrepancy P h x i T|) ∧
      (∀ T, |(occCount (stackPath P x₀ fun _ => vanDerCorput) s T : ℝ) - T * μs| ≤
        2 * M + n * stateVariation h * ((Nat.log 2 T : ℝ) + 1)) ∧
      (∀ (L : Fin n → ℕ) (c : Fin n → ℕ → Fin n), IsRotorCycle P L c → ∀ θ T,
        |(occCount (rotorWalk L c θ x₀) s T : ℝ) - T * μs| ≤
          2 * M * (1 + ∑ i, ((L i - 1 : ℕ) : ℝ))) ∧
      (IsIIDStacks Q V → ∀ᵐ ω ∂Q, ∃ K, ∀ T,
        |(occCount (stackPath P x₀ (V ω)) s T : ℝ) - T * μs| ≤
          K + (∑ i, (√(rowVariance P h i) + 1)) * lilScale T) :=
  ⟨fun x T => abs_occCount_sub_le P hh hM x T, fun T => abs_occCount_vdc_sub_le hP x₀ hh hM T,
    fun _ _ hc θ T => abs_occCount_rotorWalk_sub_le hP.nonneg hP.sum_eq_one hc θ x₀ hh hM T,
    fun hV => ae_abs_occCount_mc_le hV hP x₀ hh hM⟩

end RQMCMarkov.MarkovDriving

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # The MC rate for the post's MC construction: one i.i.d. sequence driving the chain

Post #3's MC simulation drives the chain by a *single* i.i.d. uniform sequence
(`drivenPath P x₀ u`, `u ∼ iidUniform ℕ`). `MCRate` proves the almost-sure rates for the stack
representation with i.i.d. stacks (`stackPath P x₀ (Function.curry w)`,
`w ∼ iidUniform (Fin n × ℕ)`). This module transfers them.

* `map_drivenPath_eq_map_stackPath_path`: the two **path laws** on `ℕ → Fin n` (product
  σ-algebra) are equal. They agree on every finite-horizon marginal
  (`map_drivenPath_eq_map_stackPath`), hence on all cylinders, and the projective limit of finite
  measures is unique (`IsProjectiveLimit.unique`, cylinders being a generating π-system).
* `ae_drivenPath_of_ae_stackPath`: any **measurable** path event that holds a.s. for the
  i.i.d.-stack path holds a.s. for the driven path. `measurable_occCount_real`,
  `measurable_transCount_real`, `measurable_lilScale_occCount` make the events of `MCRate`
  measurable once their real quantifiers are made countable (`ε = 1/(k+1)`, `K ∈ ℕ`; the
  equivalences are `forall_exists_le_iff_nat`, `exists_le_iff_nat`).
* Transferred results, for `u ∼ iidUniform ℕ`:
  `ae_abs_transCount_driven_le` (upper LIL rate for the transition counts),
  `ae_abs_occCount_driven_le` (occupation error `≤ K + C √(2 T log log T)`),
  `ae_unbounded_occCount_driven` (charged states are visited infinitely often),
  `ae_frequently_transCount_driven_ge` (lower LIL half), `ae_not_tendsto_transCount_driven`,
  and `occupation_error_ranking_driven`, the ranking theorem with MC driving.
-/

namespace RQMCMarkov.MarkovDriving

open MeasureTheory ProbabilityTheory Filter Finset Matrix

variable {n : ℕ}

/-! ### Measurability of path functionals -/

/-- `x ↦ N_i(x, T)` (as a real number) is measurable on the path space. -/
theorem measurable_occCount_real (i : Fin n) (T : ℕ) :
    Measurable fun x : ℕ → Fin n => (occCount x i T : ℝ) := by
  have e : (fun x : ℕ → Fin n => (occCount x i T : ℝ)) =
      fun x => ∑ t ∈ range T, (if x t = i then (1 : ℝ) else 0) :=
    funext fun x => (sum_indicator_eq_occCount x i T).symm
  rw [e]
  exact Finset.measurable_sum _ fun t _ =>
    Measurable.ite (show MeasurableSet {x : ℕ → Fin n | x t = i} from
      (measurable_pi_apply (X := fun _ : ℕ => Fin n) t) (measurableSet_singleton i))
      measurable_const measurable_const

/-- `x ↦ N_ij(x, T)` (as a real number) is measurable on the path space. -/
theorem measurable_transCount_real (i j : Fin n) (T : ℕ) :
    Measurable fun x : ℕ → Fin n => (transCount x i j T : ℝ) := by
  have e : (fun x : ℕ → Fin n => (transCount x i j T : ℝ)) =
      fun x => ∑ t ∈ range T, (if x t = i ∧ x (t + 1) = j then (1 : ℝ) else 0) := by
    funext x
    rw [sum_boole]
    rfl
  rw [e]
  exact Finset.measurable_sum _ fun t _ =>
    Measurable.ite (show MeasurableSet {x : ℕ → Fin n | x t = i ∧ x (t + 1) = j} from
      ((measurable_pi_apply (X := fun _ : ℕ => Fin n) t) (measurableSet_singleton i)).inter
        ((measurable_pi_apply (X := fun _ : ℕ => Fin n) (t + 1))
          (measurableSet_singleton j))) measurable_const
      measurable_const

/-- `x ↦ √(2 N log log N)` with `N = N_i(x, T)` is measurable on the path space. -/
theorem measurable_lilScale_occCount (i : Fin n) (T : ℕ) :
    Measurable fun x : ℕ → Fin n => lilScale (occCount x i T) := by
  have hg : Measurable fun r : ℝ => √(2 * r * Real.log (Real.log r)) := by fun_prop
  exact hg.comp (measurable_occCount_real i T)

/-- A comparison of measurable real functions is a measurable predicate. -/
theorem measurable_le_prop {α : Type*} [MeasurableSpace α] {f g : α → ℝ} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun a => f a ≤ g a :=
  measurableSet_setOfPred.1 (measurableSet_le hf hg)

/-! ### Equality of the path laws -/

/-- The driven path is a measurable map into the path space. -/
theorem measurable_drivenPath (P : Fin n → Fin n → ℝ) (x₀ : Fin n) :
    Measurable (drivenPath P x₀) :=
  measurable_pi_iff.2 fun t =>
    (measurable_pi_apply (⟨t, Nat.lt_succ_self t⟩ : Fin (t + 1))).comp
      (measurable_drivenPath_restrict P x₀ t)

/-- The stack path is a measurable map into the path space. -/
theorem measurable_stackPath (P : Fin n → Fin n → ℝ) (x₀ : Fin n) :
    Measurable fun w : Fin n × ℕ → ℝ => stackPath P x₀ (Function.curry w) :=
  measurable_pi_iff.2 fun t =>
    (measurable_pi_apply (⟨t, Nat.lt_succ_self t⟩ : Fin (t + 1))).comp
      (measurable_stackPath_restrict P x₀ t)

/-- **Equality of the path laws** of MC driving by one i.i.d. sequence and of i.i.d. stacks, as
measures on `ℕ → Fin n`. -/
theorem map_drivenPath_eq_map_stackPath_path {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ : Fin n) : (iidUniform ℕ).map (drivenPath P x₀) =
      (iidUniform (Fin n × ℕ)).map fun w => stackPath P x₀ (Function.curry w) := by
  have := isProbabilityMeasure_iidUniform ℕ
  have := isProbabilityMeasure_iidUniform (Fin n × ℕ)
  set μ := (iidUniform ℕ).map (drivenPath P x₀) with hμ
  set ν := (iidUniform (Fin n × ℕ)).map fun w => stackPath P x₀ (Function.curry w) with hν
  have hμP : IsProjectiveLimit μ fun I => μ.map I.restrict := fun _ => rfl
  refine hμP.unique fun I => ?_
  -- restrict through a finite horizon `T ≥ max I`
  set T := I.sup id
  let ρ : (ℕ → Fin n) → (Fin (T + 1) → Fin n) := fun x t => x t
  let φ : (Fin (T + 1) → Fin n) → (I → Fin n) := fun y i =>
    y ⟨i, Nat.lt_succ_of_le (Finset.le_sup (f := id) i.2)⟩
  have hρ : Measurable ρ := measurable_pi_iff.2 fun t => measurable_pi_apply _
  have hφ : Measurable φ := measurable_pi_iff.2 fun i => measurable_pi_apply _
  have hres : (I.restrict : (ℕ → Fin n) → (I → Fin n)) = φ ∘ ρ := rfl
  have hd := measurable_drivenPath P x₀
  have hs := measurable_stackPath P x₀
  have key : ν.map ρ = μ.map ρ := by
    rw [hμ, hν, Measure.map_map hρ hd, Measure.map_map hρ hs]
    exact (map_drivenPath_eq_map_stackPath hP x₀ T).symm
  change ν.map I.restrict = μ.map I.restrict
  rw [hres, ← Measure.map_map hφ hρ, ← Measure.map_map hφ hρ, key]

/-- **Transfer**: a measurable path event that holds almost surely for the i.i.d.-stack path holds
almost surely for the path driven by one i.i.d. sequence. -/
theorem ae_drivenPath_of_ae_stackPath {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ : Fin n) {p : (ℕ → Fin n) → Prop} (hp : MeasurableSet {x | p x})
    (h : ∀ᵐ w ∂iidUniform (Fin n × ℕ), p (stackPath P x₀ (Function.curry w))) :
    ∀ᵐ u ∂iidUniform ℕ, p (drivenPath P x₀ u) := by
  have h1 : ∀ᵐ x ∂(iidUniform (Fin n × ℕ)).map fun w => stackPath P x₀ (Function.curry w),
      p x := (ae_map_iff (measurable_stackPath P x₀).aemeasurable hp).2 h
  rw [← map_drivenPath_eq_map_stackPath_path hP x₀] at h1
  exact ae_of_ae_map (measurable_drivenPath P x₀).aemeasurable h1

/-! ### Countable reformulations -/

/-- `∀ ε > 0, ∃ K, ∀ T, |e T| ≤ K + (σ + ε) L T` iff the same with `ε = 1/(k+1)`, `K ∈ ℕ`
(for `L ≥ 0`). -/
theorem forall_exists_le_iff_nat {e L : ℕ → ℝ} (hL : ∀ T, 0 ≤ L T) (σ : ℝ) :
    (∀ ε > 0, ∃ K : ℝ, ∀ T, |e T| ≤ K + (σ + ε) * L T) ↔
      ∀ k : ℕ, ∃ K : ℕ, ∀ T, |e T| ≤ K + (σ + 1 / ((k : ℝ) + 1)) * L T := by
  constructor
  · intro h k
    obtain ⟨K, hK⟩ := h (1 / ((k : ℝ) + 1)) (by positivity)
    exact ⟨⌈K⌉₊, fun T => (hK T).trans (by linarith [Nat.le_ceil K])⟩
  · intro h ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    obtain ⟨K, hK⟩ := h k
    refine ⟨K, fun T => (hK T).trans ?_⟩
    have := mul_le_mul_of_nonneg_right (by linarith : σ + 1 / ((k : ℝ) + 1) ≤ σ + ε) (hL T)
    linarith

/-- `∃ K, ∀ T, |e T| ≤ K + c T` iff the same with `K ∈ ℕ`. -/
theorem exists_le_iff_nat {e c : ℕ → ℝ} :
    (∃ K : ℝ, ∀ T, |e T| ≤ K + c T) ↔ ∃ K : ℕ, ∀ T, |e T| ≤ K + c T := by
  constructor
  · rintro ⟨K, hK⟩
    exact ⟨⌈K⌉₊, fun T => (hK T).trans (by linarith [Nat.le_ceil K])⟩
  · rintro ⟨K, hK⟩
    exact ⟨K, hK⟩

variable {P : Fin n → Fin n → ℝ}

/-- The countable form of the upper transition event is measurable. -/
theorem measurableSet_transUpper (i j : Fin n) (σ : ℝ) :
    MeasurableSet {x : ℕ → Fin n | ∀ k : ℕ, ∃ K : ℕ, ∀ T,
      |(transCount x i j T : ℝ) - P i j * occCount x i T| ≤
        K + (σ + 1 / ((k : ℝ) + 1)) * lilScale T} := by
  refine measurableSet_setOfPred.2 (Measurable.forall fun k => Measurable.exists fun K =>
    Measurable.forall fun T => measurable_le_prop ?_ measurable_const)
  exact continuous_abs.measurable.comp ((measurable_transCount_real i j T).sub
    ((measurable_occCount_real i T).const_mul (P i j)))

/-- **MC driving, upper LIL rate for the transition counts**: for `u ∼ iidUniform ℕ`, a.s.,
for every `ε > 0` there is `K` with
`|N_ij(T) − p_ij N_i(T)| ≤ K + (√(p_ij (1 − p_ij)) + ε) √(2 T log log T)` for all `T`. -/
theorem ae_abs_transCount_driven_le (hP : IsStochastic P) (x₀ i j : Fin n) :
    ∀ᵐ u ∂iidUniform ℕ, ∀ ε > 0, ∃ K, ∀ T,
      |(transCount (drivenPath P x₀ u) i j T : ℝ) - P i j * occCount (drivenPath P x₀ u) i T|
        ≤ K + (√(P i j * (1 - P i j)) + ε) * lilScale T := by
  have := isProbabilityMeasure_iidUniform (Fin n × ℕ)
  have hst := ae_abs_transCount_mc_le (isIIDStacks_iidUniform (n := n)) hP x₀ i j
  have hdr := ae_drivenPath_of_ae_stackPath hP x₀ (measurableSet_transUpper (P := P) i j
    (√(P i j * (1 - P i j)))) (hst.mono fun w hw =>
      (forall_exists_le_iff_nat (fun T => lilScale_nonneg T) _).1 hw)
  exact hdr.mono fun u hu => (forall_exists_le_iff_nat (fun T => lilScale_nonneg T) _).2 hu

/-- **MC driving, occupation error at the LIL rate**: for `u ∼ iidUniform ℕ`, a.s.
`|N_s(T) − T π_s| ≤ K + C √(2 T log log T)` for all `T`, with `C = Σ_i (σ_i(h) + 1)`. -/
theorem ae_abs_occCount_driven_le (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ}
    {s : Fin n} {μs M : ℝ} (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - μs)
    (hM : ∀ i, |h i| ≤ M) :
    ∀ᵐ u ∂iidUniform ℕ, ∃ K, ∀ T, |(occCount (drivenPath P x₀ u) s T : ℝ) - T * μs| ≤
      K + (∑ i, (√(rowVariance P h i) + 1)) * lilScale T := by
  have := isProbabilityMeasure_iidUniform (Fin n × ℕ)
  set C := ∑ i, (√(rowVariance P h i) + 1)
  have hst := ae_abs_occCount_mc_le (isIIDStacks_iidUniform (n := n)) hP x₀ hh hM
  have hmeas : MeasurableSet {x : ℕ → Fin n | ∃ K : ℕ, ∀ T,
      |(occCount x s T : ℝ) - T * μs| ≤ K + C * lilScale T} := by
    refine measurableSet_setOfPred.2 (Measurable.exists fun K =>
      Measurable.forall fun T => measurable_le_prop ?_ measurable_const)
    exact continuous_abs.measurable.comp ((measurable_occCount_real s T).sub measurable_const)
  have hdr := ae_drivenPath_of_ae_stackPath hP x₀ hmeas
    (hst.mono fun w hw => exists_le_iff_nat.1 hw)
  exact hdr.mono fun u hu => exists_le_iff_nat.2 hu

/-- **MC driving visits every charged state infinitely often** (a.s.). -/
theorem ae_unbounded_occCount_driven (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ}
    {s : Fin n} {μs M : ℝ} (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - μs)
    (hM : ∀ i, |h i| ≤ M) (hμ : 0 < μs) :
    ∀ᵐ u ∂iidUniform ℕ, ∀ v : ℕ, ∃ T, v ≤ occCount (drivenPath P x₀ u) s T := by
  have := isProbabilityMeasure_iidUniform (Fin n × ℕ)
  have hst := ae_tendsto_occCount_mc (isIIDStacks_iidUniform (n := n)) hP x₀ hh hM hμ
  have hmeas : MeasurableSet {x : ℕ → Fin n | ∀ v : ℕ, ∃ T, (v : ℝ) ≤ occCount x s T} :=
    measurableSet_setOfPred.2 (Measurable.forall fun v => Measurable.exists fun T =>
      measurable_le_prop measurable_const (measurable_occCount_real s T))
  have hdr := ae_drivenPath_of_ae_stackPath hP x₀ hmeas
    (hst.mono fun w hw v => (hw v).imp fun T hT => by exact_mod_cast hT)
  exact hdr.mono fun u hu v => (hu v).imp fun T hT => by exact_mod_cast hT

/-- **MC driving, lower LIL half**: if `π_i > 0`, then for `u ∼ iidUniform ℕ`, a.s. for every
`ε > 0`, infinitely often `N_ij(T) − p_ij N_i(T) ≥ (σ − ε) √(2 N log log N)` and infinitely
often `≤ −(σ − ε) √(2 N log log N)`, with `N = N_i(T)`, `σ = √(p_ij (1 − p_ij))`. -/
theorem ae_frequently_transCount_driven_ge (hP : IsStochastic P) (x₀ : Fin n)
    {h : Fin n → ℝ} {i : Fin n} {μi M : ℝ}
    (hh : ∀ k, h k - (P *ᵥ h) k = (if k = i then 1 else 0) - μi) (hM : ∀ k, |h k| ≤ M)
    (hμ : 0 < μi) (j : Fin n) :
    ∀ᵐ u ∂iidUniform ℕ, ∀ ε > 0,
      (∃ᶠ T in atTop, (√(P i j * (1 - P i j)) - ε) *
          lilScale (occCount (drivenPath P x₀ u) i T) ≤
        (transCount (drivenPath P x₀ u) i j T : ℝ) -
          P i j * occCount (drivenPath P x₀ u) i T) ∧
      ∃ᶠ T in atTop, (transCount (drivenPath P x₀ u) i j T : ℝ) -
          P i j * occCount (drivenPath P x₀ u) i T ≤
        -((√(P i j * (1 - P i j)) - ε) * lilScale (occCount (drivenPath P x₀ u) i T)) := by
  have := isProbabilityMeasure_iidUniform (Fin n × ℕ)
  set σ := √(P i j * (1 - P i j))
  -- the countable event
  let E : (ℕ → Fin n) → ℕ → ℝ := fun x T =>
    (transCount x i j T : ℝ) - P i j * occCount x i T
  have hE : ∀ T, Measurable fun x => E x T := fun T =>
    (measurable_transCount_real i j T).sub ((measurable_occCount_real i T).const_mul (P i j))
  have hmeas : MeasurableSet {x : ℕ → Fin n | ∀ k : ℕ,
      (∀ T₀ : ℕ, ∃ T, T₀ ≤ T ∧ (σ - 1 / ((k : ℝ) + 1)) * lilScale (occCount x i T) ≤ E x T) ∧
      ∀ T₀ : ℕ, ∃ T, T₀ ≤ T ∧ E x T ≤ -((σ - 1 / ((k : ℝ) + 1)) *
        lilScale (occCount x i T))} := by
    refine measurableSet_setOfPred.2 (Measurable.forall fun k => Measurable.and
      (Measurable.forall fun T₀ => Measurable.exists fun T => Measurable.and measurable_const
        (measurable_le_prop ((measurable_lilScale_occCount i T).const_mul _) (hE T)))
      (Measurable.forall fun T₀ => Measurable.exists fun T => Measurable.and measurable_const
        (measurable_le_prop (hE T) ((measurable_lilScale_occCount i T).const_mul _).neg)))
  have hst := ae_frequently_transCount_mc_ge (isIIDStacks_iidUniform (n := n)) hP x₀ hh hM hμ j
  have hdr := ae_drivenPath_of_ae_stackPath hP x₀ hmeas (hst.mono fun w hw k => by
    obtain ⟨h1, h2⟩ := hw (1 / ((k : ℝ) + 1)) (by positivity)
    exact ⟨fun T₀ => (frequently_atTop.1 h1 T₀).imp fun T hT => ⟨hT.1, hT.2⟩,
      fun T₀ => (frequently_atTop.1 h2 T₀).imp fun T hT => ⟨hT.1, hT.2⟩⟩)
  filter_upwards [hdr] with u hu ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨h1, h2⟩ := hu k
  refine ⟨frequently_atTop.2 fun T₀ => (h1 T₀).imp fun T hT => ⟨hT.1, ?_⟩,
    frequently_atTop.2 fun T₀ => (h2 T₀).imp fun T hT => ⟨hT.1, ?_⟩⟩
  · have hL := lilScale_nonneg (occCount (drivenPath P x₀ u) i T)
    have := mul_le_mul_of_nonneg_right (by linarith : σ - ε ≤ σ - 1 / ((k : ℝ) + 1)) hL
    exact this.trans hT.2
  · have hL := lilScale_nonneg (occCount (drivenPath P x₀ u) i T)
    have := mul_le_mul_of_nonneg_right (by linarith : σ - ε ≤ σ - 1 / ((k : ℝ) + 1)) hL
    exact hT.2.trans (by linarith)

/-- **MC driving is not `o(√(N log log N))`-accurate**: for `0 < p_ij < 1` and `π_i > 0`,
for `u ∼ iidUniform ℕ`, almost surely `(N_ij(T) − p_ij N_i(T)) / √(2 N_i(T) log log N_i(T))`
does not tend to `0`. -/
theorem ae_not_tendsto_transCount_driven (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ}
    {i : Fin n} {μi M : ℝ} (hh : ∀ k, h k - (P *ᵥ h) k = (if k = i then 1 else 0) - μi)
    (hM : ∀ k, |h k| ≤ M) (hμ : 0 < μi) {j : Fin n} (hp0 : 0 < P i j) (hp1 : P i j < 1) :
    ∀ᵐ u ∂iidUniform ℕ, ¬ Tendsto (fun T => ((transCount (drivenPath P x₀ u) i j T : ℝ) -
        P i j * occCount (drivenPath P x₀ u) i T) /
          lilScale (occCount (drivenPath P x₀ u) i T)) atTop (nhds 0) := by
  filter_upwards [ae_frequently_transCount_driven_ge hP x₀ hh hM hμ j,
    ae_unbounded_occCount_driven hP x₀ hh hM hμ] with u hω hunb htend
  set x := drivenPath P x₀ u
  set σ := √(P i j * (1 - P i j))
  have hσ : 0 < σ := Real.sqrt_pos.2 (mul_pos hp0 (by linarith))
  obtain ⟨hfr, -⟩ := hω (σ / 2) (by positivity)
  have hsmall := htend.eventually (gt_mem_nhds (show (0 : ℝ) < σ / 2 by positivity))
  have htop : Tendsto (fun T => occCount x i T) atTop atTop :=
    tendsto_atTop_atTop_of_monotone (fun _ _ hab => occCount_mono x i hab) hunb
  have hpos : ∀ᶠ T in atTop, 0 < lilScale (occCount x i T) :=
    (htop.eventually (lil_eventually_le_log 3)).mono fun T hT => lilScale_pos hT
  obtain ⟨T, hT1, hT2, hT3⟩ := (hfr.and_eventually (hsmall.and hpos)).exists
  have h2 := hT2
  rw [div_lt_iff₀ hT3] at h2
  nlinarith

/-- **The ranking theorem for the post's MC construction.** Let `h − Ph = 1_{s} − π_s`,
`|h| ≤ M`. Then:
1. van der Corput stacks: `|N_s(T) − T π_s| ≤ 2M + n V(h) (⌊log₂ T⌋ + 1)` (`O(log T)`);
2. rotors: `|N_s(T) − T π_s| ≤ 2M (1 + Σ_i (L i − 1))` (`O(1)`);
3. MC driving by one i.i.d. uniform sequence: a.s. `|N_s(T) − T π_s| ≤ K + C √(2 T log log T)`
   (`O(√(T log log T))`), and if `π_s > 0` this order is attained for the transition counts
   (`ae_frequently_transCount_driven_ge`). -/
theorem occupation_error_ranking_driven (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ}
    {s : Fin n} {μs M : ℝ} (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - μs)
    (hM : ∀ i, |h i| ≤ M) :
    (∀ T, |(occCount (stackPath P x₀ fun _ => vanDerCorput) s T : ℝ) - T * μs| ≤
        2 * M + n * stateVariation h * ((Nat.log 2 T : ℝ) + 1)) ∧
      (∀ (L : Fin n → ℕ) (c : Fin n → ℕ → Fin n), IsRotorCycle P L c → ∀ θ T,
        |(occCount (rotorWalk L c θ x₀) s T : ℝ) - T * μs| ≤
          2 * M * (1 + ∑ i, ((L i - 1 : ℕ) : ℝ))) ∧
      (∀ᵐ u ∂iidUniform ℕ, ∃ K, ∀ T,
        |(occCount (drivenPath P x₀ u) s T : ℝ) - T * μs| ≤
          K + (∑ i, (√(rowVariance P h i) + 1)) * lilScale T) :=
  ⟨fun T => abs_occCount_vdc_sub_le hP x₀ hh hM T,
    fun _ _ hc θ T => abs_occCount_rotorWalk_sub_le hP.nonneg hP.sum_eq_one hc θ x₀ hh hM T,
    ae_abs_occCount_driven_le hP x₀ hh hM⟩

end RQMCMarkov.MarkovDriving

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # The root-mean-square rate of plain MC (post #3)

Post #3: "With MC of a Markov Chain the empirical transition matrix converges at `O(1/√T)`
(Meyn & Tweedie, Chpt 17)." `MCRate` and `MCRateDriven` show that **almost surely** this is
false: the error of `N_ij(T) − p_ij N_i(T)` is of exact order `√(T log log T)` (LIL), so the
empirical transition matrix converges at `√(log log T / T)`, not `O(1/√T)`
(`ae_frequently_transCount_driven_ge`, `ae_not_tendsto_transCount_driven`). This module proves
that the post's `O(1/√T)` is **right at the root-mean-square (RMSE) scale**, for the post's MC
construction: one i.i.d. uniform sequence `u ∼ iidUniform ℕ` driving `drivenPath P x₀ u`, any
stochastic `P`, any start `x₀`, every horizon `T`.

**Method.** `N_ij(T) − p_ij N_i(T) = Σ_{t<T} 1{x_t = i}(1{x_{t+1} = j} − p_ij)` is a sum of
martingale increments for the time filtration: the input `u T` is independent of the past
`(u 0, …, u (T−1))` (`indepFun_past_iidUniform`), which determines `x_0, …, x_T`
(`drivenPath_padPast`), and `x_{T+1} = step P x_T (u T)`. Hence
`E[G(x) F(x_T, x_{T+1})] = E[G(x) Σ_j p_{x_T j} F(x_T, j)]` for every bounded functional `G` of
`x_0, …, x_T` (`integral_mul_step_driven`): the increments are orthogonal, with conditional
variance `Σ_j p_{x_t j} f(x_t, j)²` (`integral_sq_incrementSum_driven`).

## Main results

* `integral_sq_transCount_sub_driven` (**exact**): `E[(N_ij(T) − p_ij N_i(T))²] =
  p_ij (1 − p_ij) E N_i(T)`; `integral_sq_transCount_sub_driven_le`: `≤ p_ij (1 − p_ij) T`;
  `integral_sq_transFreq_sub_driven_le`: `E[((N_ij − p_ij N_i)/T)²] ≤ p_ij (1 − p_ij)/T`.
* `integral_sq_departureDiscrepancy_driven`: `E[D_i(g, T)²] = σ_i²(g) E N_i(T)` and
  `integral_sq_sum_departureDiscrepancy_driven`: `E[(Σ_i D_i(g, T))²] = Σ_i σ_i²(g) E N_i(T)`,
  with `σ_i²(g) = rowVariance P g i` (`D_i` is `departureDiscrepancy`).
* Occupation error, with Poisson's `h − Ph = 1_{s} − c`, `|h| ≤ M` (as in
  `abs_occCount_sub_le`): `integral_sq_occCount_sub_driven_mem` (two-sided bounds through
  `V(T) = Σ_i σ_i²(h) E N_i(T)`), `integral_sq_occCount_sub_driven_le`:
  `E[(N_s(T) − T c)²] ≤ (2M + √(T Σ_i σ_i²(h)))²`, and `integral_sq_occFreq_sub_driven_le`:
  the RMSE of the frequency `N_s(T)/T` is `O(1/√T)`.
* `tendsto_integral_occCount_div_driven`: `E N_s(T)/T → c` (a consequence of the RMSE bound;
  no almost-sure law or dominated convergence is needed).
* **Lower bound** `eventually_integral_sq_occCount_sub_driven_ge`: if `E N_i(T)/T → w_i` and
  `Σ_i w_i σ_i²(h) > 0`, then `E[(N_s(T) − T c)²] ≥ κ T` eventually, for some `κ > 0`;
  `eventually_integral_sq_occCount_sub_driven_ge_of_irreducible`: the same for irreducible `P`
  with stationary `π`, under `Σ_i π_i σ_i²(h) > 0`. So the RMSE of the frequency is of exact
  order `1/√T`.
* `occCount_mse_twoStateStay78`: for the two-state chain with stay probability `7/8`
  (`twoStateStay78`), `h = (2, −2)`, `σ_0² = σ_1² = 7/4` (`rowVariance_twoStateStay78`), so
  `Σ_i π_i σ_i²(h) = 7/4 > 0`: both bounds hold and the lower bound is not vacuous.

**Correction** (post #3, "converges at `O(1/√T)`"). Read almost surely, the claim is false:
`ae_not_tendsto_transCount_driven` (`MCRateDriven`) shows the a.s. error is not
`o(√(N log log N))`. Read in root mean square, it is true and sharp: the RMSE of
`(N_ij(T) − p_ij N_i(T))/T` is `√(p_ij (1 − p_ij) E N_i(T))/T ≤ √(p_ij(1 − p_ij)/T)`
(`integral_sq_transCount_sub_driven`), and the RMSE of `N_s(T)/T` is of exact order `1/√T`
(`integral_sq_occFreq_sub_driven_le`, `eventually_integral_sq_occCount_sub_driven_ge`). The
`√T` scale is the CLT scale (`MCRateCLT`).
-/

namespace RQMCMarkov.MarkovDriving

open MeasureTheory ProbabilityTheory Filter Finset Matrix Topology

variable {n : ℕ}

/-- A measurable function bounded by `C` is integrable for a probability measure. -/
theorem integrable_of_abs_le {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {g : Ω → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ ω, |g ω| ≤ C) :
    Integrable g Q :=
  Integrable.of_bound hg.aestronglyMeasurable C (Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]
    exact hC ω)

/-- `|F a b| ≤ Σ_a Σ_b |F a b|`. -/
theorem abs_le_sum_sum_abs (F : Fin n → Fin n → ℝ) (a b : Fin n) :
    |F a b| ≤ ∑ a, ∑ b, |F a b| :=
  (single_le_sum (f := fun b => |F a b|) (fun _ _ => abs_nonneg _) (mem_univ b)).trans
    (single_le_sum (f := fun a => ∑ b, |F a b|) (fun _ _ => sum_nonneg fun _ _ =>
      abs_nonneg _) (mem_univ a))

/-- **The law of one step from a uniform input**: if `W ∼ U[0,1)`, then
`E φ(step P i W) = Σ_j p_ij φ_j`. -/
theorem integral_comp_step_of_map {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {W : Ω → ℝ} (hW : Measurable W) (hlaw : Q.map W = uniformIco)
    {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n) (φ : Fin n → ℝ) :
    ∫ ω, φ (step P i (W ω)) ∂Q = ∑ j, P i j * φ j := by
  have hmeas : Measurable fun ω => step P i (W ω) := (measurable_step P i).comp hW
  rw [← integral_map hmeas.aemeasurable (measurable_of_finite φ).aestronglyMeasurable]
  rw [integral_fintype Integrable.of_finite]
  refine sum_congr rfl fun j _ => ?_
  rw [smul_eq_mul, measureReal_def, Measure.map_apply hmeas (measurableSet_singleton j)]
  have e : (fun ω => step P i (W ω)) ⁻¹' {j} = W ⁻¹' {u | step P i u = j} := rfl
  have hms : MeasurableSet {u | step P i u = j} :=
    (measurable_step P i) (measurableSet_singleton j)
  rw [e, ← Measure.map_apply hW hms, hlaw, uniformIco_step_eq hP i j,
    ENNReal.toReal_ofReal (hP.nonneg i j), mul_comm]

/-- **One step against an independent past.** If `W ∼ U[0,1)` is independent of `Z`, then for
bounded measurable `A` and any `a`, `F`:
`E[A(Z) F(a(Z), step P (a Z) W)] = E[A(Z) Σ_j p_{a(Z) j} F(a(Z), j)]`. -/
theorem integral_mul_comp_step_of_indepFun {Ω β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace β] {Q : Measure Ω} [IsProbabilityMeasure Q] {Z : Ω → β} {W : Ω → ℝ}
    (hZ : Measurable Z) (hW : Measurable W) (hind : IndepFun Z W Q)
    (hlaw : Q.map W = uniformIco) {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {A : β → ℝ} (hA : Measurable A) {C : ℝ} (hAC : ∀ b, |A b| ≤ C) {a : β → Fin n}
    (ha : Measurable a) (F : Fin n → Fin n → ℝ) :
    ∫ ω, A (Z ω) * F (a (Z ω)) (step P (a (Z ω)) (W ω)) ∂Q =
      ∫ ω, A (Z ω) * ∑ j, P (a (Z ω)) j * F (a (Z ω)) j ∂Q := by
  set CF := ∑ a, ∑ b, |F a b|
  set φ : Fin n → β → ℝ := fun b z => A z * if a z = b then 1 else 0 with hφ
  have hφm : ∀ b, Measurable (φ b) := fun b =>
    hA.mul (Measurable.ite (ha (measurableSet_singleton b)) measurable_const measurable_const)
  have hφb : ∀ b z, |φ b z| ≤ C := fun b z => by
    simp only [hφ]
    split_ifs
    · rw [mul_one]
      exact hAC z
    · rw [mul_zero, abs_zero]
      exact (abs_nonneg _).trans (hAC z)
  have e1 : ∀ ω, A (Z ω) * F (a (Z ω)) (step P (a (Z ω)) (W ω)) =
      ∑ b, φ b (Z ω) * F b (step P b (W ω)) := fun ω => by
    simp only [hφ, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp only [mem_univ, ite_true]
  have e2 : ∀ ω, A (Z ω) * ∑ j, P (a (Z ω)) j * F (a (Z ω)) j =
      ∑ b, φ b (Z ω) * ∑ j, P b j * F b j := fun ω => by
    simp only [hφ, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp only [mem_univ, ite_true]
  have hFm : ∀ b, Measurable fun ω => F b (step P b (W ω)) := fun b =>
    (measurable_of_finite (F b)).comp ((measurable_step P b).comp hW)
  have hint1 : ∀ b ∈ univ, Integrable (fun ω => φ b (Z ω) * F b (step P b (W ω))) Q :=
    fun b _ => integrable_of_abs_le (((hφm b).comp hZ).mul (hFm b)) (C := C * CF)
      fun ω => by
        rw [abs_mul]
        exact mul_le_mul (hφb b _) (abs_le_sum_sum_abs F _ _) (abs_nonneg _)
          ((abs_nonneg _).trans (hφb b (Z ω)))
  have hint2 : ∀ b ∈ univ, Integrable (fun ω => φ b (Z ω) * ∑ j, P b j * F b j) Q :=
    fun b _ => (integrable_of_abs_le ((hφm b).comp hZ) fun ω => hφb b (Z ω)).mul_const _
  rw [integral_congr_ae (Eventually.of_forall e1), integral_congr_ae (Eventually.of_forall e2),
    integral_finsetSum _ hint1, integral_finsetSum _ hint2]
  refine sum_congr rfl fun b _ => ?_
  have hindb : IndepFun (fun ω => φ b (Z ω)) (fun ω => F b (step P b (W ω))) Q :=
    hind.comp (hφm b) ((measurable_of_finite (F b)).comp (measurable_step P b))
  rw [hindb.integral_fun_mul_eq_mul_integral ((hφm b).comp hZ).aestronglyMeasurable
    (hFm b).aestronglyMeasurable, integral_mul_const, integral_comp_step_of_map hW hlaw hP b]

/-! ### The past of the driving sequence -/

/-- The first `T` driving inputs, padded with zeros: `padPast T p s = p s` for `s < T`. -/
noncomputable def padPast (T : ℕ) (p : range T → ℝ) : ℕ → ℝ :=
  fun s => if h : s ∈ range T then p ⟨s, h⟩ else 0

/-- `padPast T` is measurable. -/
theorem measurable_padPast (T : ℕ) : Measurable (padPast T) := by
  refine measurable_pi_iff.2 fun s => ?_
  by_cases h : s ∈ range T
  · simp only [padPast, h, dite_true]
    exact measurable_pi_apply _
  · simp only [padPast, h, dite_false]
    exact measurable_const

/-- **The path up to time `T` depends only on the first `T` inputs.** -/
theorem drivenPath_padPast (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (u : ℕ → ℝ) {T t : ℕ}
    (ht : t ≤ T) :
    drivenPath P x₀ (padPast T fun s : range T => u s) t = drivenPath P x₀ u t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change step P (drivenPath P x₀ (padPast T fun s : range T => u s) t)
        (padPast T (fun s : range T => u s) t) = step P (drivenPath P x₀ u t) (u t)
    rw [ih (by omega)]
    have hs : t ∈ range T := mem_range.2 (by omega)
    simp only [padPast, hs, dite_true]

/-- Under `iidUniform ℕ`, the first `T` inputs are independent of the input `u T`. -/
theorem indepFun_past_iidUniform (T : ℕ) :
    IndepFun (fun (u : ℕ → ℝ) (s : range T) => u s) (fun u : ℕ → ℝ => u T)
      (iidUniform ℕ) := by
  have := isProbabilityMeasure_uniformIco
  have h := iIndepFun_infinitePi (P := fun _ : ℕ => uniformIco) (X := fun _ x => x)
    (fun _ => measurable_id)
  have h2 := h.indepFun_finset (range T) {T} (by simp) (fun t => measurable_pi_apply t)
  exact h2.comp measurable_id (measurable_pi_apply (⟨T, mem_singleton_self T⟩ : ({T} : Finset ℕ)))

/-- Each input of `iidUniform ℕ` is uniform on `[0,1)`. -/
theorem map_eval_iidUniform (T : ℕ) :
    (iidUniform ℕ).map (fun u : ℕ → ℝ => u T) = uniformIco := by
  have := isProbabilityMeasure_uniformIco
  exact Measure.infinitePi_map_eval (μ := fun _ : ℕ => uniformIco) T

/-- The state at time `t` is a measurable function of the input sequence. -/
theorem measurable_drivenPath_apply (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (t : ℕ) :
    Measurable fun u => drivenPath P x₀ u t :=
  (measurable_pi_apply t).comp (measurable_drivenPath P x₀)

/-- **The one-step identity for MC driving.** If `G` is a bounded measurable path functional
that depends only on `x_0, …, x_T`, then
`E[G(x) F(x_T, x_{T+1})] = E[G(x) Σ_j p_{x_T j} F(x_T, j)]`. -/
theorem integral_mul_step_driven {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (x₀ : Fin n)
    (T : ℕ) {G : (ℕ → Fin n) → ℝ} (hG : Measurable G) {C : ℝ} (hGC : ∀ x, |G x| ≤ C)
    (hGT : ∀ x y : ℕ → Fin n, (∀ t ≤ T, x t = y t) → G x = G y) (F : Fin n → Fin n → ℝ) :
    ∫ u, G (drivenPath P x₀ u) * F (drivenPath P x₀ u T) (drivenPath P x₀ u (T + 1))
        ∂iidUniform ℕ =
      ∫ u, G (drivenPath P x₀ u) *
        ∑ j, P (drivenPath P x₀ u T) j * F (drivenPath P x₀ u T) j ∂iidUniform ℕ := by
  have := isProbabilityMeasure_iidUniform ℕ
  set Z : (ℕ → ℝ) → (range T → ℝ) := fun u s => u s
  have hZ : Measurable Z := measurable_pi_iff.2 fun s => measurable_pi_apply _
  set A : (range T → ℝ) → ℝ := fun p => G (drivenPath P x₀ (padPast T p))
  set a : (range T → ℝ) → Fin n := fun p => drivenPath P x₀ (padPast T p) T
  have hA : Measurable A := hG.comp ((measurable_drivenPath P x₀).comp (measurable_padPast T))
  have ha : Measurable a := (measurable_drivenPath_apply P x₀ T).comp (measurable_padPast T)
  have eA : ∀ u, G (drivenPath P x₀ u) = A (Z u) := fun u =>
    hGT _ _ fun t ht => (drivenPath_padPast P x₀ u ht).symm
  have ea : ∀ u, drivenPath P x₀ u T = a (Z u) := fun u =>
    (drivenPath_padPast P x₀ u le_rfl).symm
  have hkey := integral_mul_comp_step_of_indepFun hZ (measurable_pi_apply T)
    (indepFun_past_iidUniform T) (map_eval_iidUniform T) hP hA (fun p => hGC _) ha F
  have e1 : ∀ u, G (drivenPath P x₀ u) * F (drivenPath P x₀ u T) (drivenPath P x₀ u (T + 1)) =
      A (Z u) * F (a (Z u)) (step P (a (Z u)) (u T)) := fun u => by
    rw [eA, show drivenPath P x₀ u (T + 1) = step P (drivenPath P x₀ u T) (u T) from rfl,
      ← ea]
  have e2 : ∀ u, G (drivenPath P x₀ u) *
      ∑ j, P (drivenPath P x₀ u T) j * F (drivenPath P x₀ u T) j =
      A (Z u) * ∑ j, P (a (Z u)) j * F (a (Z u)) j := fun u => by
    rw [eA, ← ea]
  simp only [e1, e2]
  exact hkey

/-! ### The martingale of increments -/

/-- The **increment sum** `Σ_{t<T} f(x_t, x_{t+1})` along a path. When every row average
`Σ_j p_aj f(a, j)` vanishes, it is a martingale for MC (`integral_sq_incrementSum_driven`). -/
noncomputable def incrementSum (f : Fin n → Fin n → ℝ) (x : ℕ → Fin n) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, f (x t) (x (t + 1))

/-- `x ↦ f(x_t, x_{t+1})` is measurable on the path space. -/
theorem measurable_pair_apply (f : Fin n → Fin n → ℝ) (t : ℕ) :
    Measurable fun x : ℕ → Fin n => f (x t) (x (t + 1)) := by
  have h := (measurable_of_finite fun p : Fin n × Fin n => f p.1 p.2).comp
    ((measurable_pi_apply (X := fun _ : ℕ => Fin n) t).prodMk (measurable_pi_apply (t + 1)))
  exact h

/-- The increment sum is measurable on the path space. -/
theorem measurable_incrementSum (f : Fin n → Fin n → ℝ) (T : ℕ) :
    Measurable fun x : ℕ → Fin n => incrementSum f x T :=
  Finset.measurable_sum _ fun t _ => measurable_pair_apply f t

/-- `|Σ_{t<T} f(x_t, x_{t+1})| ≤ T Σ_{a,b} |f a b|`. -/
theorem abs_incrementSum_le (f : Fin n → Fin n → ℝ) (x : ℕ → Fin n) (T : ℕ) :
    |incrementSum f x T| ≤ T * ∑ a, ∑ b, |f a b| := by
  unfold incrementSum
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have := sum_le_sum fun t (_ : t ∈ range T) => abs_le_sum_sum_abs f (x t) (x (t + 1))
  rwa [sum_const, card_range, nsmul_eq_mul] at this

/-- The increment sum up to `T` depends only on `x_0, …, x_T`. -/
theorem incrementSum_congr (f : Fin n → Fin n → ℝ) {x y : ℕ → Fin n} {T : ℕ}
    (h : ∀ t ≤ T, x t = y t) : incrementSum f x T = incrementSum f y T :=
  sum_congr rfl fun t ht => by
    have := mem_range.1 ht
    rw [h t (by omega), h (t + 1) (by omega)]

/-- **Orthogonality of martingale increments** (exact second moment). If every row average of
`f` vanishes, `Σ_j p_aj f(a, j) = 0`, then for MC driving
`E[(Σ_{t<T} f(x_t, x_{t+1}))²] = Σ_{t<T} E[Σ_j p_{x_t j} f(x_t, j)²]`. -/
theorem integral_sq_incrementSum_driven {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ : Fin n) {f : Fin n → Fin n → ℝ} (hf : ∀ a, ∑ j, P a j * f a j = 0) (T : ℕ) :
    ∫ u, incrementSum f (drivenPath P x₀ u) T ^ 2 ∂iidUniform ℕ =
      ∑ t ∈ range T, ∫ u, ∑ j, P (drivenPath P x₀ u t) j * f (drivenPath P x₀ u t) j ^ 2
        ∂iidUniform ℕ := by
  have := isProbabilityMeasure_iidUniform ℕ
  set Cf := ∑ a, ∑ b, |f a b|
  have hCf : 0 ≤ Cf := sum_nonneg fun a _ => sum_nonneg fun b _ => abs_nonneg _
  induction T with
  | zero =>
    simp only [incrementSum, range_zero, sum_empty, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, integral_zero]
  | succ T ih =>
    set M : (ℕ → ℝ) → ℝ := fun u => incrementSum f (drivenPath P x₀ u) T
    set d : (ℕ → ℝ) → ℝ := fun u => f (drivenPath P x₀ u T) (drivenPath P x₀ u (T + 1))
    have hMm : Measurable M := (measurable_incrementSum f T).comp (measurable_drivenPath P x₀)
    have hdm : Measurable d := (measurable_pair_apply f T).comp (measurable_drivenPath P x₀)
    have hMb : ∀ u, |M u| ≤ T * Cf := fun u => abs_incrementSum_le f _ T
    have hdb : ∀ u, |d u| ≤ Cf := fun u => abs_le_sum_sum_abs f _ _
    have e : ∀ u, incrementSum f (drivenPath P x₀ u) (T + 1) ^ 2 =
        M u ^ 2 + 2 * (M u * d u) + d u ^ 2 := fun u => by
      simp only [M, d, incrementSum, sum_range_succ]
      ring
    have hi1 : Integrable (fun u => M u ^ 2) (iidUniform ℕ) :=
      integrable_of_abs_le (hMm.pow_const 2) (C := (T * Cf) ^ 2) fun u => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hMb u) 2
    have hi2 : Integrable (fun u => 2 * (M u * d u)) (iidUniform ℕ) :=
      (integrable_of_abs_le (g := fun u => M u * d u) (hMm.mul hdm) (C := T * Cf * Cf) fun u => by
        rw [abs_mul]
        exact mul_le_mul (hMb u) (hdb u) (abs_nonneg _) (by positivity)).const_mul 2
    have hi3 : Integrable (fun u => d u ^ 2) (iidUniform ℕ) :=
      integrable_of_abs_le (hdm.pow_const 2) (C := Cf ^ 2) fun u => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hdb u) 2
    have hcross : ∫ u, M u * d u ∂iidUniform ℕ = 0 := by
      have h1 := integral_mul_step_driven hP x₀ T (measurable_incrementSum f T)
        (fun x => abs_incrementSum_le f x T) (fun x y hxy => incrementSum_congr f
          fun t ht => hxy t ht) f
      change ∫ u, M u * d u ∂iidUniform ℕ = _ at h1
      rw [h1]
      simp only [hf, mul_zero, integral_zero]
    have hsq : ∫ u, d u ^ 2 ∂iidUniform ℕ = ∫ u, ∑ j, P (drivenPath P x₀ u T) j *
        f (drivenPath P x₀ u T) j ^ 2 ∂iidUniform ℕ := by
      have h1 := integral_mul_step_driven hP x₀ T (G := fun _ => (1 : ℝ)) measurable_const
        (C := 1) (fun _ => by rw [abs_one]) (fun _ _ _ => rfl) (fun a b => f a b ^ 2)
      simp only [one_mul] at h1
      exact h1
    have hi12 : Integrable (fun u => M u ^ 2 + 2 * (M u * d u)) (iidUniform ℕ) := hi1.add hi2
    rw [integral_congr_ae (Eventually.of_forall e), integral_add hi12 hi3,
      integral_add hi1 hi2, integral_const_mul, hcross, hsq, ih, sum_range_succ]
    ring

/-! ### Exact second moments of the departure discrepancies -/

/-- The departure discrepancy of `i` is the increment sum of
`f(a, b) = 1{a = i} (g b − (Pg)(i))`. -/
theorem departureDiscrepancy_eq_incrementSum (P : Fin n → Fin n → ℝ) (g : Fin n → ℝ)
    (x : ℕ → Fin n) (i : Fin n) (T : ℕ) :
    departureDiscrepancy P g x i T =
      incrementSum (fun a b => if a = i then g b - (P *ᵥ g) i else 0) x T := by
  unfold departureDiscrepancy incrementSum
  rw [sum_filter]

/-- The total departure discrepancy `Σ_i D_i(g, T)` is the increment sum of
`f(a, b) = g b − (Pg)(a)`. -/
theorem sum_departureDiscrepancy_eq_incrementSum (P : Fin n → Fin n → ℝ) (g : Fin n → ℝ)
    (x : ℕ → Fin n) (T : ℕ) :
    ∑ i, departureDiscrepancy P g x i T = incrementSum (fun a b => g b - (P *ᵥ g) a) x T := by
  simp only [departureDiscrepancy_eq_incrementSum, incrementSum]
  rw [sum_comm]
  refine sum_congr rfl fun t _ => ?_
  rw [Finset.sum_ite_eq]
  simp only [mem_univ, ite_true]

/-- `Σ_j p_ij (g_j − (Pg)(i)) = 0` for stochastic `P`. -/
theorem sum_mul_sub_mulVec_eq_zero {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (g : Fin n → ℝ) (i : Fin n) : ∑ j, P i j * (g j - (P *ᵥ g) i) = 0 := by
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, hP.sum_eq_one i, one_mul]
  rw [sub_eq_zero]
  rfl

/-- **Occupation counts in mean**: for MC driving, `Σ_{t<T} E φ(x_t) = Σ_i φ_i E N_i(T)`. -/
theorem sum_integral_comp_driven (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (φ : Fin n → ℝ)
    (T : ℕ) : ∑ t ∈ range T, ∫ u, φ (drivenPath P x₀ u t) ∂iidUniform ℕ =
      ∑ i, φ i * ∫ u, (occCount (drivenPath P x₀ u) i T : ℝ) ∂iidUniform ℕ := by
  have := isProbabilityMeasure_iidUniform ℕ
  have hint : ∀ t ∈ range T, Integrable (fun u => φ (drivenPath P x₀ u t)) (iidUniform ℕ) :=
    fun t _ => integrable_of_abs_le ((measurable_of_finite φ).comp
      (measurable_drivenPath_apply P x₀ t)) (C := ∑ i, |φ i|) fun u =>
        single_le_sum (f := fun i => |φ i|) (fun _ _ => abs_nonneg _) (mem_univ _)
  have hintN : ∀ i ∈ univ, Integrable (fun u => φ i *
      (occCount (drivenPath P x₀ u) i T : ℝ)) (iidUniform ℕ) := fun i _ =>
    (integrable_of_abs_le ((measurable_occCount_real i T).comp (measurable_drivenPath P x₀))
      (C := T) fun u => by
        change |(occCount (drivenPath P x₀ u) i T : ℝ)| ≤ T
        rw [Nat.abs_cast]
        exact_mod_cast occCount_le _ i T).const_mul _
  have e : ∀ u, ∑ t ∈ range T, φ (drivenPath P x₀ u t) =
      ∑ i, φ i * (occCount (drivenPath P x₀ u) i T : ℝ) := fun u => by
    simp only [← sum_indicator_eq_occCount, mul_sum, mul_ite, mul_one, mul_zero]
    rw [sum_comm]
    refine sum_congr rfl fun t _ => ?_
    rw [Finset.sum_ite_eq]
    simp only [mem_univ, ite_true]
  rw [← integral_finsetSum _ hint, integral_congr_ae (Eventually.of_forall e),
    integral_finsetSum _ hintN]
  simp only [integral_const_mul]

/-- **Exact MSE of the total departure discrepancy** (MC driving, any start, every `T`):
`E[(Σ_i D_i(g, T))²] = Σ_i σ_i²(g) E N_i(T)`, with `σ_i²(g) = rowVariance P g i`. -/
theorem integral_sq_sum_departureDiscrepancy_driven {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (x₀ : Fin n) (g : Fin n → ℝ) (T : ℕ) :
    ∫ u, (∑ i, departureDiscrepancy P g (drivenPath P x₀ u) i T) ^ 2 ∂iidUniform ℕ =
      ∑ i, rowVariance P g i * ∫ u, (occCount (drivenPath P x₀ u) i T : ℝ) ∂iidUniform ℕ := by
  simp only [sum_departureDiscrepancy_eq_incrementSum]
  rw [integral_sq_incrementSum_driven hP x₀ (fun a => sum_mul_sub_mulVec_eq_zero hP g a) T]
  exact sum_integral_comp_driven P x₀ (rowVariance P g) T

/-- **Exact MSE of one departure discrepancy**: `E[D_i(g, T)²] = σ_i²(g) E N_i(T)`. -/
theorem integral_sq_departureDiscrepancy_driven {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (x₀ : Fin n) (g : Fin n → ℝ) (i : Fin n) (T : ℕ) :
    ∫ u, departureDiscrepancy P g (drivenPath P x₀ u) i T ^ 2 ∂iidUniform ℕ =
      rowVariance P g i * ∫ u, (occCount (drivenPath P x₀ u) i T : ℝ) ∂iidUniform ℕ := by
  simp only [departureDiscrepancy_eq_incrementSum]
  have hf : ∀ a, ∑ j, P a j * (if a = i then g j - (P *ᵥ g) i else 0) = 0 := fun a => by
    by_cases ha : a = i
    · subst ha
      simp only [ite_true]
      exact sum_mul_sub_mulVec_eq_zero hP g a
    · simp only [ha, ite_false, mul_zero, sum_const_zero]
  rw [integral_sq_incrementSum_driven hP x₀ hf T]
  have e : ∀ a, ∑ j, P a j * (if a = i then g j - (P *ᵥ g) i else 0) ^ 2 =
      if a = i then rowVariance P g i else 0 := fun a => by
    by_cases ha : a = i
    · subst ha
      simp only [ite_true]
      rfl
    · simp only [ha, ite_false, mul_zero, sum_const_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow]
  simp only [e]
  rw [sum_integral_comp_driven P x₀ (fun a => if a = i then rowVariance P g i else 0) T]
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [mem_univ, ite_true]

/-- **Exact MSE of the MC transition counts** (post #3's empirical transition matrix, at the
RMSE scale): for stochastic `P`, any start and every `T`,
`E[(N_ij(T) − p_ij N_i(T))²] = p_ij (1 − p_ij) E N_i(T)`. -/
theorem integral_sq_transCount_sub_driven {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ i j : Fin n) (T : ℕ) :
    ∫ u, ((transCount (drivenPath P x₀ u) i j T : ℝ) -
        P i j * occCount (drivenPath P x₀ u) i T) ^ 2 ∂iidUniform ℕ =
      P i j * (1 - P i j) * ∫ u, (occCount (drivenPath P x₀ u) i T : ℝ) ∂iidUniform ℕ := by
  simp only [transCount_sub_eq_departureDiscrepancy (P : Matrix (Fin n) (Fin n) ℝ)]
  rw [integral_sq_departureDiscrepancy_driven hP x₀ _ i T, rowVariance_indicator hP i j]

/-- `0 ≤ E N_i(T) ≤ T`. -/
theorem integral_occCount_driven_mem_Icc (P : Fin n → Fin n → ℝ) (x₀ i : Fin n) (T : ℕ) :
    ∫ u, (occCount (drivenPath P x₀ u) i T : ℝ) ∂iidUniform ℕ ∈ Set.Icc (0 : ℝ) T := by
  have := isProbabilityMeasure_iidUniform ℕ
  refine ⟨integral_nonneg fun u => Nat.cast_nonneg _, ?_⟩
  have h := integral_mono_of_nonneg (μ := iidUniform ℕ)
    (f := fun u => (occCount (drivenPath P x₀ u) i T : ℝ)) (g := fun _ => (T : ℝ))
    (Eventually.of_forall fun u => Nat.cast_nonneg _) (integrable_const _)
    (Eventually.of_forall fun u => by
      change (occCount (drivenPath P x₀ u) i T : ℝ) ≤ T
      exact_mod_cast occCount_le _ i T)
  rwa [integral_const, probReal_univ, one_smul] at h

/-- **The `O(1/√T)` RMSE of the MC transition counts**:
`E[(N_ij(T) − p_ij N_i(T))²] ≤ p_ij (1 − p_ij) T`. -/
theorem integral_sq_transCount_sub_driven_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ i j : Fin n) (T : ℕ) :
    ∫ u, ((transCount (drivenPath P x₀ u) i j T : ℝ) -
        P i j * occCount (drivenPath P x₀ u) i T) ^ 2 ∂iidUniform ℕ ≤
      P i j * (1 - P i j) * T := by
  rw [integral_sq_transCount_sub_driven hP x₀ i j T]
  have h1 : 0 ≤ P i j * (1 - P i j) := by
    have := rowVariance_indicator hP i j
    rw [← this]
    exact sum_nonneg fun k _ => mul_nonneg (hP.nonneg i k) (sq_nonneg _)
  exact mul_le_mul_of_nonneg_left (integral_occCount_driven_mem_Icc P x₀ i T).2 h1

/-! ### The occupation error at the RMSE scale -/

/-- **Jensen for `|X|`**: `E|X| ≤ √(E X²)` for a bounded measurable `X`. -/
theorem integral_abs_le_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {X : Ω → ℝ} (hX : Measurable X) {C : ℝ} (hC : ∀ ω, |X ω| ≤ C) :
    ∫ ω, |X ω| ∂Q ≤ √(∫ ω, X ω ^ 2 ∂Q) := by
  set m := ∫ ω, |X ω| ∂Q
  have hm : 0 ≤ m := integral_nonneg fun ω => abs_nonneg _
  have hiA : Integrable (fun ω => |X ω|) Q :=
    integrable_of_abs_le (continuous_abs.measurable.comp hX) (C := C) fun ω => by
      rw [abs_abs]
      exact hC ω
  have hi2 : Integrable (fun ω => X ω ^ 2) Q :=
    integrable_of_abs_le (hX.pow_const 2) (C := C ^ 2) fun ω => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hC ω) 2
  have h0 : 0 ≤ ∫ ω, (|X ω| - m) ^ 2 ∂Q := integral_nonneg fun ω => sq_nonneg _
  have e : ∀ ω, (|X ω| - m) ^ 2 = X ω ^ 2 + (-(2 * m) * |X ω| + m ^ 2) := fun ω => by
    rw [sub_sq, sq_abs]
    ring
  have hi3 : Integrable (fun ω => -(2 * m) * |X ω| + m ^ 2) Q :=
    (hiA.const_mul _).add (integrable_const _)
  rw [integral_congr_ae (Eventually.of_forall e), integral_add hi2 hi3,
    integral_add (hiA.const_mul _) (integrable_const _),
    integral_const_mul, integral_const, probReal_univ, one_smul] at h0
  refine Real.le_sqrt_of_sq_le ?_
  nlinarith

/-- The occupation error is measurable. -/
theorem measurable_occCount_sub_driven (P : Fin n → Fin n → ℝ) (x₀ s : Fin n) (c : ℝ)
    (T : ℕ) : Measurable fun u => (occCount (drivenPath P x₀ u) s T : ℝ) - T * c :=
  ((measurable_occCount_real s T).comp (measurable_drivenPath P x₀)).sub measurable_const

/-- **Two-sided MSE bounds for the occupation error.** Let `h − Ph = 1_{s} − c`, `|h| ≤ M`, and
`V(T) = Σ_i σ_i²(h) E N_i(T)` (the exact MSE of `Σ_i D_i(h, T)`). Then for MC driving
`√V (√V − 4M) ≤ E[(N_s(T) − T c)²] ≤ (2M + √V)²`. -/
theorem integral_sq_occCount_sub_driven_mem {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M)
    (T : ℕ) :
    √(∑ i, rowVariance P h i * ∫ u, (occCount (drivenPath P x₀ u) i T : ℝ) ∂iidUniform ℕ) *
        (√(∑ i, rowVariance P h i * ∫ u, (occCount (drivenPath P x₀ u) i T : ℝ)
          ∂iidUniform ℕ) - 4 * M) ≤
      ∫ u, ((occCount (drivenPath P x₀ u) s T : ℝ) - T * c) ^ 2 ∂iidUniform ℕ ∧
    ∫ u, ((occCount (drivenPath P x₀ u) s T : ℝ) - T * c) ^ 2 ∂iidUniform ℕ ≤
      (2 * M + √(∑ i, rowVariance P h i * ∫ u, (occCount (drivenPath P x₀ u) i T : ℝ)
        ∂iidUniform ℕ)) ^ 2 := by
  have := isProbabilityMeasure_iidUniform ℕ
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM s)
  set V := ∑ i, rowVariance P h i * ∫ u, (occCount (drivenPath P x₀ u) i T : ℝ) ∂iidUniform ℕ
  set D : (ℕ → ℝ) → ℝ := fun u => ∑ i, departureDiscrepancy P h (drivenPath P x₀ u) i T
  set E : (ℕ → ℝ) → ℝ := fun u => (occCount (drivenPath P x₀ u) s T : ℝ) - T * c
  set Ch := ∑ a, ∑ b, |(fun a b => h b - (P *ᵥ h) a) a b|
  have hDm : Measurable D := by
    have e : D = fun u => incrementSum (fun a b => h b - (P *ᵥ h) a) (drivenPath P x₀ u) T :=
      funext fun u => sum_departureDiscrepancy_eq_incrementSum P h _ T
    rw [e]
    have h1 := (measurable_incrementSum (fun a b => h b - (P *ᵥ h) a) T).comp
      (measurable_drivenPath P x₀)
    exact h1
  have hDb : ∀ u, |D u| ≤ T * Ch := fun u => by
    simp only [D, sum_departureDiscrepancy_eq_incrementSum]
    exact abs_incrementSum_le _ _ T
  have hEm : Measurable E := measurable_occCount_sub_driven P x₀ s c T
  have hED : ∀ u, ∃ B, |B| ≤ 2 * M ∧ E u = B + D u := fun u => by
    refine ⟨h (drivenPath P x₀ u 0) - h (drivenPath P x₀ u T), ?_,
      occCount_sub_eq_boundary_add P hh _ T⟩
    have := abs_sub (h (drivenPath P x₀ u 0)) (h (drivenPath P x₀ u T))
    linarith [hM (drivenPath P x₀ u 0), hM (drivenPath P x₀ u T)]
  have hEb : ∀ u, |E u| ≤ 2 * M + T * Ch := fun u => by
    obtain ⟨B, hB, hE⟩ := hED u
    rw [hE]
    exact (abs_add_le _ _).trans (add_le_add hB (hDb u))
  have hiE : Integrable (fun u => E u ^ 2) (iidUniform ℕ) :=
    integrable_of_abs_le (hEm.pow_const 2) (C := (2 * M + T * Ch) ^ 2) fun u => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hEb u) 2
  have hiD2 : Integrable (fun u => D u ^ 2) (iidUniform ℕ) :=
    integrable_of_abs_le (hDm.pow_const 2) (C := (T * Ch) ^ 2) fun u => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hDb u) 2
  have hiDa : Integrable (fun u => |D u|) (iidUniform ℕ) :=
    integrable_of_abs_le (continuous_abs.measurable.comp hDm) (C := T * Ch) fun u => by
      rw [abs_abs]
      exact hDb u
  have hD2 : ∫ u, D u ^ 2 ∂iidUniform ℕ = V :=
    integral_sq_sum_departureDiscrepancy_driven hP x₀ h T
  have hJ : ∫ u, |D u| ∂iidUniform ℕ ≤ √V := by
    rw [← hD2]
    exact integral_abs_le_sqrt_integral_sq hDm hDb
  have hV0 : 0 ≤ V := by
    rw [← hD2]
    exact integral_nonneg fun u => sq_nonneg _
  have hsqV : √V ^ 2 = V := Real.sq_sqrt hV0
  have hJ0 : 0 ≤ ∫ u, |D u| ∂iidUniform ℕ := integral_nonneg fun u => abs_nonneg _
  constructor
  · -- pointwise `E² ≥ D² − 4M|D|`
    have hle : ∀ u, D u ^ 2 + -(4 * M) * |D u| ≤ E u ^ 2 := fun u => by
      obtain ⟨B, hB, hE⟩ := hED u
      rw [hE]
      have h1 : -(2 * B * D u) ≤ 2 * (2 * M) * |D u| := by
        have := neg_abs_le (2 * B * D u)
        rw [abs_mul, abs_mul, abs_two] at this
        nlinarith [abs_nonneg (D u), abs_nonneg B]
      nlinarith [sq_nonneg B]
    have hi4 : Integrable (fun u => D u ^ 2 + -(4 * M) * |D u|) (iidUniform ℕ) :=
      hiD2.add (hiDa.const_mul _)
    have := integral_mono hi4 hiE hle
    rw [integral_add hiD2 (hiDa.const_mul _), integral_const_mul, hD2] at this
    nlinarith [Real.sqrt_nonneg V]
  · -- pointwise `E² ≤ 4M² + 4M|D| + D²`
    have hle : ∀ u, E u ^ 2 ≤ (2 * M) ^ 2 + (4 * M * |D u| + D u ^ 2) := fun u => by
      obtain ⟨B, hB, hE⟩ := hED u
      rw [hE]
      have h1 : 2 * B * D u ≤ 2 * (2 * M) * |D u| := by
        have := le_abs_self (2 * B * D u)
        rw [abs_mul, abs_mul, abs_two] at this
        nlinarith [abs_nonneg (D u), abs_nonneg B]
      have h2 : B ^ 2 ≤ (2 * M) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hB 2
      nlinarith
    have hi5 : Integrable (fun u => 4 * M * |D u| + D u ^ 2) (iidUniform ℕ) :=
      (hiDa.const_mul _).add hiD2
    have hi6 : Integrable (fun u => (2 * M) ^ 2 + (4 * M * |D u| + D u ^ 2)) (iidUniform ℕ) :=
      (integrable_const _).add hi5
    have := integral_mono hiE hi6 hle
    rw [integral_add (integrable_const _) hi5,
      integral_add (hiDa.const_mul _) hiD2, integral_const_mul, hD2, integral_const,
      probReal_univ, one_smul] at this
    nlinarith [Real.sqrt_nonneg V]

/-- **The RMSE of the MC occupation frequency is `O(1/√T)`** (post #3's rate, at the RMSE
scale): with `h − Ph = 1_{s} − c`, `|h| ≤ M`,
`E[(N_s(T) − T c)²] ≤ (2M + √(T Σ_i σ_i²(h)))²`. -/
theorem integral_sq_occCount_sub_driven_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M)
    (T : ℕ) :
    ∫ u, ((occCount (drivenPath P x₀ u) s T : ℝ) - T * c) ^ 2 ∂iidUniform ℕ ≤
      (2 * M + √(T * ∑ i, rowVariance P h i)) ^ 2 := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM s)
  refine (integral_sq_occCount_sub_driven_mem hP x₀ hh hM T).2.trans ?_
  have hrv : ∀ i, 0 ≤ rowVariance P h i := fun i =>
    sum_nonneg fun k _ => mul_nonneg (hP.nonneg i k) (sq_nonneg _)
  have hV : ∑ i, rowVariance P h i * ∫ u, (occCount (drivenPath P x₀ u) i T : ℝ)
      ∂iidUniform ℕ ≤ T * ∑ i, rowVariance P h i := by
    rw [mul_sum]
    refine sum_le_sum fun i _ => ?_
    rw [mul_comm (T : ℝ)]
    exact mul_le_mul_of_nonneg_left (integral_occCount_driven_mem_Icc P x₀ i T).2 (hrv i)
  have := Real.sqrt_le_sqrt hV
  exact pow_le_pow_left₀ (by positivity) (by linarith) 2

/-- **The mean occupation frequency converges**: with `h − Ph = 1_{s} − c`, `|h| ≤ M`,
`|E N_s(T) − T c| ≤ 2M + √(T Σ_i σ_i²(h))` (from the RMSE bound), hence `E N_s(T)/T → c`. -/
theorem abs_integral_occCount_sub_driven_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M)
    (T : ℕ) :
    |∫ u, (occCount (drivenPath P x₀ u) s T : ℝ) ∂iidUniform ℕ - T * c| ≤
      2 * M + √(T * ∑ i, rowVariance P h i) := by
  have := isProbabilityMeasure_iidUniform ℕ
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM s)
  have hEm := measurable_occCount_sub_driven P x₀ s c T
  have hEb : ∀ u, |(occCount (drivenPath P x₀ u) s T : ℝ) - T * c| ≤ T + T * |c| := fun u => by
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [Nat.abs_cast]
      exact_mod_cast occCount_le _ s T
    · rw [abs_mul, Nat.abs_cast]
  have hiN : Integrable (fun u => (occCount (drivenPath P x₀ u) s T : ℝ)) (iidUniform ℕ) :=
    integrable_of_abs_le ((measurable_occCount_real s T).comp (measurable_drivenPath P x₀))
      (C := T) fun u => by
        rw [Nat.abs_cast]
        exact_mod_cast occCount_le _ s T
  have e : ∫ u, (occCount (drivenPath P x₀ u) s T : ℝ) ∂iidUniform ℕ - T * c =
      ∫ u, ((occCount (drivenPath P x₀ u) s T : ℝ) - T * c) ∂iidUniform ℕ := by
    rw [integral_sub hiN (integrable_const _), integral_const, probReal_univ, one_smul]
  rw [e]
  refine (abs_integral_le_integral_abs).trans ((integral_abs_le_sqrt_integral_sq hEm hEb).trans ?_)
  calc √(∫ u, ((occCount (drivenPath P x₀ u) s T : ℝ) - T * c) ^ 2 ∂iidUniform ℕ)
      ≤ √((2 * M + √(T * ∑ i, rowVariance P h i)) ^ 2) :=
        Real.sqrt_le_sqrt (integral_sq_occCount_sub_driven_le hP x₀ hh hM T)
    _ = 2 * M + √(T * ∑ i, rowVariance P h i) := Real.sqrt_sq (by positivity)

/-- **The mean occupation frequency converges**: `E N_s(T)/T → c` for MC driving, whenever
Poisson's equation `h − Ph = 1_{s} − c` has a bounded solution. -/
theorem tendsto_integral_occCount_div_driven {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M) :
    Tendsto (fun T : ℕ => (∫ u, (occCount (drivenPath P x₀ u) s T : ℝ) ∂iidUniform ℕ) / T)
      atTop (𝓝 c) := by
  set R := ∑ i, rowVariance P h i
  have hR : 0 ≤ R := sum_nonneg fun i _ =>
    sum_nonneg fun k _ => mul_nonneg (hP.nonneg i k) (sq_nonneg _)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hg : Tendsto (fun T : ℕ => 2 * M * (T : ℝ)⁻¹ + √R * (√(T : ℝ))⁻¹) atTop (𝓝 0) := by
    have h1 := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul
      (2 * M)
    have h2 := (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))).const_mul √R
    have := h1.add h2
    rw [mul_zero, mul_zero, add_zero] at this
    exact this
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hg
  filter_upwards [eventually_ge_atTop 1] with T hT
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have key := abs_integral_occCount_sub_driven_le hP x₀ hh hM T
  rw [Real.norm_eq_abs]
  have e : (∫ u, (occCount (drivenPath P x₀ u) s T : ℝ) ∂iidUniform ℕ) / T - c =
      (∫ u, (occCount (drivenPath P x₀ u) s T : ℝ) ∂iidUniform ℕ - T * c) / T := by
    field_simp
  rw [e, abs_div, abs_of_pos hT0, div_le_iff₀ hT0]
  have hsq : √(T * R) = √(T : ℝ) * √R := Real.sqrt_mul hT0.le R
  have hsT : √(T : ℝ) * √(T : ℝ) = T := Real.mul_self_sqrt hT0.le
  have hsT0 : 0 < √(T : ℝ) := Real.sqrt_pos.2 hT0
  have e2 : (2 * M * (T : ℝ)⁻¹ + √R * (√(T : ℝ))⁻¹) * T = 2 * M + √(T * R) := by
    have h1 : (√(T : ℝ))⁻¹ * T = √(T : ℝ) := by
      rw [inv_mul_eq_div, div_eq_iff hsT0.ne']
      exact hsT.symm
    rw [hsq, add_mul, mul_assoc (2 * M), inv_mul_cancel₀ hT0.ne', mul_assoc √R, h1]
    ring
  rw [e2]
  exact key

/-- **The RMSE of the MC occupation frequency is of exact order `1/√T`** (lower bound). Let
`h − Ph = 1_{s} − c`, `|h| ≤ M`, suppose the mean frequencies converge, `E N_i(T)/T → w_i`,
and the **nondegeneracy** `Σ_i w_i σ_i²(h) > 0` (the asymptotic variance of `N_s`). Then
there is `κ > 0` with `E[(N_s(T) − T c)²] ≥ κ T` for all large `T`. -/
theorem eventually_integral_sq_occCount_sub_driven_ge {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M)
    {w : Fin n → ℝ}
    (hfreq : ∀ i, Tendsto (fun T : ℕ =>
      (∫ u, (occCount (drivenPath P x₀ u) i T : ℝ) ∂iidUniform ℕ) / T) atTop (𝓝 (w i)))
    (hpos : 0 < ∑ i, w i * rowVariance P h i) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ T : ℕ in atTop,
      κ * T ≤ ∫ u, ((occCount (drivenPath P x₀ u) s T : ℝ) - T * c) ^ 2 ∂iidUniform ℕ := by
  set σ2 := ∑ i, w i * rowVariance P h i
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM s)
  set V : ℕ → ℝ := fun T => ∑ i, rowVariance P h i *
    ∫ u, (occCount (drivenPath P x₀ u) i T : ℝ) ∂iidUniform ℕ
  have hVt : Tendsto (fun T : ℕ => V T / T) atTop (𝓝 σ2) := by
    have e : ∀ T : ℕ, V T / T = ∑ i, rowVariance P h i *
        ((∫ u, (occCount (drivenPath P x₀ u) i T : ℝ) ∂iidUniform ℕ) / T) := fun T => by
      simp only [V, sum_div, mul_div_assoc]
    simp only [e]
    have := tendsto_finsetSum (univ : Finset (Fin n)) fun i _ => (hfreq i).const_mul
      (rowVariance P h i)
    simp only [σ2, mul_comm (w _)]
    exact this
  refine ⟨σ2 / 4, by positivity, ?_⟩
  filter_upwards [hVt.eventually (lt_mem_nhds (show σ2 / 2 < σ2 by linarith)),
    eventually_ge_atTop (⌈128 * M ^ 2 / σ2⌉₊ + 1)] with T hV hT
  have hT1 : (⌈128 * M ^ 2 / σ2⌉₊ : ℝ) + 1 ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := by linarith [Nat.cast_nonneg (α := ℝ) ⌈128 * M ^ 2 / σ2⌉₊]
  have hTM : 128 * M ^ 2 / σ2 ≤ T := by linarith [Nat.le_ceil (128 * M ^ 2 / σ2)]
  have hVT : σ2 / 2 * T < V T := by rwa [lt_div_iff₀ hT0] at hV
  have hV64 : 64 * M ^ 2 ≤ V T := by
    have : 128 * M ^ 2 ≤ σ2 * T := by
      rw [div_le_iff₀ hpos] at hTM
      linarith
    nlinarith
  have hV0 : 0 ≤ V T := le_trans (by positivity) hV64
  have hs8 : 8 * M ≤ √(V T) := by
    rw [show 8 * M = √((8 * M) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hsq : √(V T) * √(V T) = V T := Real.mul_self_sqrt hV0
  have hlow := (integral_sq_occCount_sub_driven_mem hP x₀ hh hM T).1
  change √(V T) * (√(V T) - 4 * M) ≤ _ at hlow
  nlinarith

/-- **The RMSE of the MC occupation frequency** in frequency units: for `T > 0`,
`E[(N_s(T)/T − c)²] ≤ (2M + √(T Σ_i σ_i²(h)))² / T²`, i.e. `RMSE = O(1/√T)`. -/
theorem integral_sq_occFreq_sub_driven_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M)
    {T : ℕ} (hT : 0 < T) :
    ∫ u, ((occCount (drivenPath P x₀ u) s T : ℝ) / T - c) ^ 2 ∂iidUniform ℕ ≤
      (2 * M + √(T * ∑ i, rowVariance P h i)) ^ 2 / T ^ 2 := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have e : ∀ u, ((occCount (drivenPath P x₀ u) s T : ℝ) / T - c) ^ 2 =
      ((occCount (drivenPath P x₀ u) s T : ℝ) - T * c) ^ 2 / T ^ 2 := fun u => by
    field_simp
  rw [integral_congr_ae (Eventually.of_forall e), integral_div]
  exact div_le_div_of_nonneg_right (integral_sq_occCount_sub_driven_le hP x₀ hh hM T)
    (by positivity)

/-- **The RMSE of the MC transition counts** in frequency units:
`E[((N_ij(T) − p_ij N_i(T))/T)²] ≤ p_ij (1 − p_ij)/T`. -/
theorem integral_sq_transFreq_sub_driven_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ i j : Fin n) {T : ℕ} (hT : 0 < T) :
    ∫ u, (((transCount (drivenPath P x₀ u) i j T : ℝ) -
        P i j * occCount (drivenPath P x₀ u) i T) / T) ^ 2 ∂iidUniform ℕ ≤
      P i j * (1 - P i j) / T := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  simp only [div_pow]
  rw [integral_div, div_le_div_iff₀ (by positivity) hT0]
  have := integral_sq_transCount_sub_driven_le hP x₀ i j T
  have e : P i j * (1 - P i j) * (T : ℝ) ^ 2 = P i j * (1 - P i j) * T * T := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_right this hT0.le

/-- `μ ⬝ᵥ 1_{k} = μ k`. -/
theorem dotProduct_indicator (μ : Fin n → ℝ) (k : Fin n) :
    μ ⬝ᵥ (fun i => if i = k then (1 : ℝ) else 0) = μ k := by
  simp only [dotProduct, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [mem_univ, ite_true]

/-- **Exact order `1/√T` for irreducible chains.** For an irreducible stochastic `P` with
stationary distribution `π`, the mean frequencies converge, `E N_i(T)/T → π_i`
(`tendsto_integral_occCount_div_driven` with the Poisson solutions of `exists_poisson`), so
under the nondegeneracy `Σ_i π_i σ_i²(h) > 0` there is `κ > 0` with
`E[(N_s(T) − T c)²] ≥ κ T` for all large `T`. -/
theorem eventually_integral_sq_occCount_sub_driven_ge_of_irreducible
    {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsStochastic P) (hirr : ∀ i j, ∃ k, 0 < (P ^ k) i j)
    {μ : Fin n → ℝ} (hμ : IsStationaryDistribution P μ) (x₀ : Fin n) {h : Fin n → ℝ}
    {s : Fin n} {c M : ℝ} (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c)
    (hM : ∀ i, |h i| ≤ M) (hpos : 0 < ∑ i, μ i * rowVariance P h i) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ T : ℕ in atTop,
      κ * T ≤ ∫ u, ((occCount (drivenPath P x₀ u) s T : ℝ) - T * c) ^ 2 ∂iidUniform ℕ := by
  have : Nonempty (Fin n) := ⟨x₀⟩
  refine eventually_integral_sq_occCount_sub_driven_ge hP x₀ hh hM (fun i => ?_) hpos
  obtain ⟨hi, hhi⟩ := exists_poisson hP.nonneg hP.sum_eq_one hirr hμ
    (fun k => if k = i then (1 : ℝ) else 0)
  rw [dotProduct_indicator] at hhi
  exact tendsto_integral_occCount_div_driven hP x₀ hhi (M := ∑ k, |hi k|) fun k =>
    single_le_sum (f := fun k => |hi k|) (fun _ _ => abs_nonneg _) (mem_univ k)

/-! ### A non-degenerate instance: the two-state chain with stay probability `7/8` -/

/-- The `7/8`-chain is stochastic. -/
theorem isStochastic_twoStateStay78 : IsStochastic twoStateStay78 := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · simp only [twoStateStay78]
    split_ifs <;> norm_num
  · rw [Fin.sum_univ_two]
    fin_cases i <;> simp only [twoStateStay78] <;> norm_num

/-- The `7/8`-chain is irreducible (all entries are positive). -/
theorem irreducible_twoStateStay78 : ∀ i j, ∃ k, 0 < (twoStateStay78 ^ k) i j := fun i j =>
  ⟨1, by
    rw [pow_one]
    simp only [twoStateStay78]
    split_ifs <;> norm_num⟩

/-- Poisson's equation for the `7/8`-chain and `s = 0`: `h = (2, −2)` solves
`h − Ph = 1_{0} − 1/2`. -/
theorem poisson_twoStateStay78 (i : Fin 2) :
    (fun k : Fin 2 => if k = 0 then (2 : ℝ) else -2) i -
        (twoStateStay78 *ᵥ fun k : Fin 2 => if k = 0 then (2 : ℝ) else -2) i =
      (if i = 0 then 1 else 0) - 1 / 2 := by
  simp only [mulVec, dotProduct, Fin.sum_univ_two]
  fin_cases i <;> simp only [twoStateStay78] <;> norm_num

/-- For the `7/8`-chain and `h = (2, −2)`, both row variances are `σ_i²(h) = 7/4`. -/
theorem rowVariance_twoStateStay78 (i : Fin 2) :
    rowVariance twoStateStay78 (fun k : Fin 2 => if k = 0 then (2 : ℝ) else -2) i = 7 / 4 := by
  simp only [rowVariance, mulVec, dotProduct, Fin.sum_univ_two]
  fin_cases i <;> simp only [twoStateStay78] <;> norm_num

/-- **The lower bound is not vacuous** (two-state chain, stay probability `7/8`, any start).
The MC occupation error of state `0` satisfies, for every `T`,
`E[(N_0(T) − T/2)²] ≤ (4 + √(7T/2))²`, and `E[(N_0(T) − T/2)²] ≥ κ T` for all large `T`, for
some `κ > 0`: the RMSE of the frequency `N_0(T)/T` is of exact order `1/√T`. -/
theorem occCount_mse_twoStateStay78 (x₀ : Fin 2) :
    (∀ T : ℕ, ∫ u, ((occCount (drivenPath twoStateStay78 x₀ u) 0 T : ℝ) - T * (1 / 2)) ^ 2
        ∂iidUniform ℕ ≤ (4 + √(7 * T / 2)) ^ 2) ∧
      ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ T : ℕ in atTop,
        κ * T ≤ ∫ u, ((occCount (drivenPath twoStateStay78 x₀ u) 0 T : ℝ) - T * (1 / 2)) ^ 2
          ∂iidUniform ℕ := by
  have hM : ∀ i : Fin 2, |(fun k : Fin 2 => if k = 0 then (2 : ℝ) else -2) i| ≤ 2 := fun i => by
    fin_cases i <;> norm_num
  have hrv : ∑ i, rowVariance twoStateStay78 (fun k : Fin 2 => if k = 0 then (2 : ℝ) else -2) i
      = 7 / 2 := by
    rw [Fin.sum_univ_two, rowVariance_twoStateStay78, rowVariance_twoStateStay78]
    norm_num
  refine ⟨fun T => ?_, eventually_integral_sq_occCount_sub_driven_ge_of_irreducible
    isStochastic_twoStateStay78 irreducible_twoStateStay78
    isStationaryDistribution_twoStateStay78 x₀ poisson_twoStateStay78 hM ?_⟩
  · have := integral_sq_occCount_sub_driven_le isStochastic_twoStateStay78 x₀
      poisson_twoStateStay78 hM T
    rw [hrv] at this
    convert this using 3
    · norm_num
    · ring_nf
  · rw [Fin.sum_univ_two, rowVariance_twoStateStay78, rowVariance_twoStateStay78]
    norm_num

end RQMCMarkov.MarkovDriving

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # The √T central limit theorem for plain MC (post #3)

Post #3: "With MC of a Markov Chain the empirical transition matrix converges at `O(1/√T)`
(Meyn & Tweedie, Chpt 17)." Almost surely the error is of the larger order
`√(log log T / T)` (`MCRate`, `MCRateDriven`); `MCRateRMSE` proves `O(1/√T)` for the
root-mean-square error. This module proves the distributional form of the same scale, the
**central limit theorem**: for the post's MC (one i.i.d. sequence `u ∼ iidUniform ℕ` driving
`drivenPath P x₀ u`), from any start,

`(N_ij(T) − p_ij N_i(T))/√T ⇒ N(0, π_i p_ij (1 − p_ij))`,

whenever `N_i(T)/T → π_i > 0` (here: Poisson's equation `h − Ph = 1_{i} − π_i` has a bounded
solution, the hypothesis of `ae_tendsto_occCount_mc`; e.g. `P` irreducible).

**Route** (Meyn and Tweedie, §17.2, through the stack representation):
1. `departureIncrement_iid`: in the i.i.d.-stack model the departures from `i` are i.i.d.
   `ξ_k = g(step P i (V i k)) − (Pg)(i)`, centred, bounded, with variance `σ_i²(g)`
   (`rowVariance`), and `D_i(g, T) = Σ_{k < N_i(T)} ξ_k` (`departureDiscrepancy_mc_eq`).
2. `tendstoInDistribution_sum_floor_mul`: Mathlib's i.i.d. CLT
   (`tendstoInDistribution_inv_sqrt_mul_sum_sub`) along the deterministic index `⌊cT⌋`
   (`tendstoInDistribution_comp_of_tendsto`), rescaled by `√⌊cT⌋/√T → √c` with Slutsky
   (`TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const`):
   `(1/√T) Σ_{k<⌊cT⌋} ξ_k ⇒ N(0, c v)`.
3. The random index: `N_i(T)/T → c` a.s. (`ae_abs_occCount_mc_le_mul`,
   `tendsto_div_of_forall_abs_sub_le`), so `(S_{N_i(T)} − S_{⌊cT⌋})/√T → 0` in probability
   (`lil_tendstoInMeasure_anscombe`, Kolmogorov's inequality), and the limit is unchanged
   (`tendstoInDistribution_of_tendstoInMeasure_sub`):
   `tendstoInDistribution_departureDiscrepancy_stack`.
4. Transfer to the driven path: the statistic is a measurable path functional
   (`measurable_departureDiscrepancy_div`) and the path laws agree
   (`map_drivenPath_eq_map_stackPath_path`): `tendstoInDistribution_departureDiscrepancy_driven`.

## Main results

* `tendstoInDistribution_departureDiscrepancy_driven`: `D_i(g, T)/√T ⇒ N(0, π_i σ_i²(g))`.
* `tendstoInDistribution_transCount_driven`: `(N_ij(T) − p_ij N_i(T))/√T ⇒
  N(0, π_i p_ij (1 − p_ij))`; `tendstoInDistribution_transCount_driven_of_irreducible`: the same
  for irreducible `P` with stationary `π`.
* `tendstoInDistribution_transCount_twoStateStay78`: for the `7/8`-chain,
  `(N_00(T) − (7/8) N_0(T))/√T ⇒ N(0, 7/128)`.

**Correction** (post #3, "converges at `O(1/√T)`"). The `1/√T` rate is the CLT (and RMSE)
scale: `√T (N_ij(T)/T − p_ij N_i(T)/T)` has a non-degenerate Gaussian limit when
`0 < p_ij < 1`, so the fluctuations of the empirical transition counts are of exact order
`1/√T` *in distribution*; almost surely they are not `O(1/√T)` (LIL,
`ae_not_tendsto_transCount_driven`).
-/

namespace RQMCMarkov.MarkovDriving

open MeasureTheory ProbabilityTheory Filter Finset Matrix Topology

variable {n : ℕ}

/-- The `k`-th **MC departure increment** of state `i` in the stack model:
`ξ_k = g(step P i (V i k)) − (Pg)(i)`. -/
noncomputable def departureIncrement (P : Fin n → Fin n → ℝ) (g : Fin n → ℝ) {Ω : Type*}
    (V : Ω → Fin n → ℕ → ℝ) (i : Fin n) (k : ℕ) (ω : Ω) : ℝ :=
  g (step P i (V ω i k)) - (P *ᵥ g) i

/-- **The departure increments of one stack are i.i.d.**, centred, square integrable, with
variance `σ_i²(g)`. -/
theorem departureIncrement_iid {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {V : Ω → Fin n → ℕ → ℝ} (hV : IsIIDStacks Q V)
    {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (g : Fin n → ℝ) (i : Fin n) :
    iIndepFun (departureIncrement P g V i) Q ∧
      (∀ k, Measurable (departureIncrement P g V i k)) ∧
      (∀ k, IdentDistrib (departureIncrement P g V i k) (departureIncrement P g V i 0) Q Q) ∧
      MemLp (departureIncrement P g V i 0) 2 Q ∧
      ∫ ω, departureIncrement P g V i 0 ω ∂Q = 0 ∧
      Var[departureIncrement P g V i 0; Q] = rowVariance P g i := by
  set c := (P *ᵥ g) i with hc
  set ψ : ℝ → ℝ := fun u => g (step P i u) - c with hψdef
  have hψ : Measurable ψ := (measurable_of_finite fun j => g j - c).comp (measurable_step P i)
  have hind : iIndepFun (departureIncrement P g V i) Q :=
    (hV.indep i).comp (fun _ => ψ) fun _ => hψ
  have hm : ∀ k, Measurable (departureIncrement P g V i k) := fun k =>
    hψ.comp (hV.measurable i k)
  have hident : ∀ k, IdentDistrib (departureIncrement P g V i k)
      (departureIncrement P g V i 0) Q Q := fun k =>
    (IdentDistrib.mk (hV.measurable i k).aemeasurable (hV.measurable i 0).aemeasurable
      (by rw [hV.law i k, hV.law i 0])).comp hψ
  have hL2 : MemLp (departureIncrement P g V i 0) 2 Q := by
    refine MemLp.of_bound (hm 0).aestronglyMeasurable (∑ j, |g j - c|)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact single_le_sum (f := fun j => |g j - c|) (fun j _ => abs_nonneg _) (mem_univ _)
  have h0 : ∫ ω, departureIncrement P g V i 0 ω ∂Q = 0 := by
    rw [show (fun ω => departureIncrement P g V i 0 ω) = fun ω =>
      (fun j => g j - c) (step P i (V ω i 0)) from rfl,
      integral_comp_step hV hP i 0 (fun j => g j - c)]
    exact sum_mul_sub_mulVec_eq_zero hP g i
  have hvar : ∫ ω, departureIncrement P g V i 0 ω ^ 2 ∂Q = rowVariance P g i :=
    integral_comp_step hV hP i 0 (fun j => (g j - c) ^ 2)
  refine ⟨hind, hm, hident, hL2, h0, ?_⟩
  rw [variance_of_integral_eq_zero (hm 0).aemeasurable h0]
  exact hvar

/-- **Convergence in distribution along a subsequence**: if `X_m ⇒ Z` and `f T → ∞`, then
`X_{f T} ⇒ Z`. -/
theorem tendstoInDistribution_comp_of_tendsto {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {Q : Measure Ω} [IsProbabilityMeasure Q] {Q' : Measure Ω'}
    [IsProbabilityMeasure Q'] {X : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (h : TendstoInDistribution X atTop Z (fun _ => Q) Q') {f : ℕ → ℕ}
    (hf : Tendsto f atTop atTop) :
    TendstoInDistribution (fun T => X (f T)) atTop Z (fun _ => Q) Q' :=
  ⟨fun T => h.forall_aemeasurable (f T), h.aemeasurable_limit, h.tendsto.comp hf⟩

/-- **The deterministic-index CLT, rescaled**: for i.i.d. centred `ξ_k ∈ L²` with variance
`v` and `c > 0`, `(1/√T) Σ_{k < ⌊cT⌋} ξ_k ⇒ N(0, c v)`. -/
theorem tendstoInDistribution_sum_floor_mul {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {Q : Measure Ω} [IsProbabilityMeasure Q] {Q' : Measure Ω'}
    [IsProbabilityMeasure Q'] {X : ℕ → Ω → ℝ} (hind : iIndepFun X Q)
    (hident : ∀ k, IdentDistrib (X k) (X 0) Q Q) (hL2 : MemLp (X 0) 2 Q)
    (h0 : ∫ ω, X 0 ω ∂Q = 0) {c : ℝ} (hc : 0 < c) {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 (c * Var[X 0; Q]).toNNReal) Q') :
    TendstoInDistribution (fun (T : ℕ) ω => (√(T : ℝ))⁻¹ * ∑ k ∈ range ⌊c * T⌋₊, X k ω) atTop
      Z (fun _ => Q) Q' := by
  have hsc : 0 < √c := Real.sqrt_pos.2 hc
  have hvar0 : 0 ≤ Var[X 0; Q] := variance_nonneg _ _
  -- the standardised limit `Z / √c ∼ N(0, v)`
  have hZ1 : HasLaw (fun ω => Z ω / √c) (gaussianReal 0 Var[X 0; Q].toNNReal) Q' := by
    have := gaussianReal_div_const hZ (√c)
    rw [zero_div] at this
    convert this using 2
    ext
    rw [NNReal.coe_div, Real.coe_toNNReal _ hvar0, Real.coe_toNNReal _ (by positivity),
      NNReal.coe_mk, Real.sq_sqrt hc.le]
    field_simp
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub hZ1 hL2 hind hident
  rw [h0] at hclt
  simp only [mul_zero, sub_zero] at hclt
  set m : ℕ → ℕ := fun T => ⌊c * T⌋₊ with hm
  have hmt : Tendsto m atTop atTop :=
    tendsto_nat_floor_atTop.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hc)
  have hX := tendstoInDistribution_comp_of_tendsto hclt hmt
  -- the deterministic scale `√(m T) / √T → √c`
  have hmdiv : Tendsto (fun T : ℕ => (m T : ℝ) / T) atTop (𝓝 c) :=
    (tendsto_nat_floor_mul_div_atTop hc.le).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ha : Tendsto (fun T : ℕ => √(m T : ℝ) / √(T : ℝ)) atTop (𝓝 √c) := by
    have := (Real.continuous_sqrt.tendsto c).comp hmdiv
    refine this.congr fun T => ?_
    simp only [Function.comp_apply]
    exact Real.sqrt_div (Nat.cast_nonneg _) _
  have haM : TendstoInMeasure Q (fun (T : ℕ) (_ : Ω) => √(m T : ℝ) / √(T : ℝ)) atTop
      (fun _ => √c) :=
    tendstoInMeasure_of_tendsto_ae (fun T => aestronglyMeasurable_const)
      (Eventually.of_forall fun _ => ha)
  have hS := hX.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : ℝ × ℝ => p.2 * p.1) (by fun_prop) haM (fun T => aemeasurable_const)
  convert hS using 1
  · funext T ω
    change (√(T : ℝ))⁻¹ * ∑ k ∈ range (m T), X k ω =
      √(m T : ℝ) / √(T : ℝ) * ((√(m T : ℝ))⁻¹ * ∑ k ∈ range (m T), X k ω)
    by_cases hT : m T = 0
    · rw [hT, range_zero, sum_empty, mul_zero, mul_zero, mul_zero]
    · have hs : 0 < √(m T : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hT)
      field_simp
  · funext ω
    field_simp

/-- **Linear growth from a uniform `o(T)` bound**: if for every `ε > 0` there is `K` with
`|a T − T c| ≤ K + ε T` for all `T`, then `a T / T → c`. -/
theorem tendsto_div_of_forall_abs_sub_le {a : ℕ → ℝ} {c : ℝ}
    (h : ∀ ε > 0, ∃ K, ∀ T : ℕ, |a T - T * c| ≤ K + ε * T) :
    Tendsto (fun T : ℕ => a T / T) atTop (𝓝 c) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := h (ε / 2) (by positivity)
  obtain ⟨T0, hT0⟩ := exists_nat_gt (2 * |K| / ε)
  refine ⟨T0 + 1, fun T hT => ?_⟩
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hTge : (T0 : ℝ) + 1 ≤ T := by exact_mod_cast hT
  rw [Real.dist_eq]
  have e : a T / T - c = (a T - T * c) / T := by field_simp
  rw [e, abs_div, abs_of_pos hTpos, div_lt_iff₀ hTpos]
  have h1 := hK T
  have h2 : 2 * |K| < ε * T := by
    rw [div_lt_iff₀ hε] at hT0
    nlinarith
  linarith [le_abs_self K]

/-- `x ↦ N_i(x, T)` is measurable on the path space (as a natural number). -/
theorem measurable_occCount_nat (i : Fin n) (T : ℕ) :
    Measurable fun x : ℕ → Fin n => occCount x i T :=
  measurable_to_countable' fun k => by
    have := measurable_occCount_real i T (measurableSet_singleton (k : ℝ))
    convert this using 1
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Nat.cast_inj]

/-- `x ↦ (1/√T) D_i(g, T)` is measurable on the path space. -/
theorem measurable_departureDiscrepancy_div (P : Fin n → Fin n → ℝ) (g : Fin n → ℝ) (i : Fin n)
    (T : ℕ) : Measurable fun x : ℕ → Fin n => (√(T : ℝ))⁻¹ * departureDiscrepancy P g x i T := by
  have e : (fun x : ℕ → Fin n => (√(T : ℝ))⁻¹ * departureDiscrepancy P g x i T) = fun x =>
      (√(T : ℝ))⁻¹ * incrementSum (fun a b => if a = i then g b - (P *ᵥ g) i else 0) x T :=
    funext fun x => by rw [departureDiscrepancy_eq_incrementSum]
  rw [e]
  exact (measurable_incrementSum _ T).const_mul _

/-- **The √T CLT for the MC departure discrepancies, i.i.d. stacks.** If Poisson's equation
`h − Ph = 1_{i} − c` has a bounded solution and `c > 0` (so `N_i(T)/T → c` a.s.), then for
the i.i.d.-stack path `(1/√T) D_i(g, T) ⇒ N(0, c σ_i²(g))`. -/
theorem tendstoInDistribution_departureDiscrepancy_stack {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ} {i : Fin n} {c M : ℝ}
    (hh : ∀ k, h k - (P *ᵥ h) k = (if k = i then 1 else 0) - c) (hM : ∀ k, |h k| ≤ M)
    (hc : 0 < c) (g : Fin n → ℝ) {Ω' : Type*} [MeasurableSpace Ω'] {Q' : Measure Ω'}
    [IsProbabilityMeasure Q'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 (c * rowVariance P g i).toNNReal) Q') :
    haveI := isProbabilityMeasure_iidUniform (Fin n × ℕ)
    TendstoInDistribution (fun (T : ℕ) (w : Fin n × ℕ → ℝ) => (√(T : ℝ))⁻¹ *
      departureDiscrepancy P g (stackPath P x₀ (Function.curry w)) i T) atTop Z
      (fun _ => iidUniform (Fin n × ℕ)) Q' := by
  have := isProbabilityMeasure_iidUniform (Fin n × ℕ)
  have hV := isIIDStacks_iidUniform (n := n)
  obtain ⟨hind, hm, hident, hL2, h0, hvar⟩ := departureIncrement_iid hV hP g i
  set Y := departureIncrement P g (fun w : Fin n × ℕ → ℝ => Function.curry w) i
  rw [← hvar] at hZ
  have hdet := tendstoInDistribution_sum_floor_mul hind hident hL2 h0 hc hZ
  set K : ℕ → (Fin n × ℕ → ℝ) → ℕ := fun T w => occCount (stackPath P x₀ (Function.curry w)) i T
  have hKm : ∀ T, Measurable (K T) := fun T =>
    (measurable_occCount_nat i T).comp (measurable_stackPath P x₀)
  have hK : ∀ᵐ w ∂iidUniform (Fin n × ℕ), Tendsto (fun T => (K T w : ℝ) / T) atTop (𝓝 c) := by
    filter_upwards [ae_abs_occCount_mc_le_mul hV hP x₀ hh hM] with w hw
    exact tendsto_div_of_forall_abs_sub_le hw
  have hans := lil_tendstoInMeasure_anscombe hind hm hident hL2 h0 hKm hc hK
  have e : (fun (T : ℕ) (w : Fin n × ℕ → ℝ) => (√(T : ℝ))⁻¹ *
      departureDiscrepancy P g (stackPath P x₀ (Function.curry w)) i T) =
      fun (T : ℕ) (w : Fin n × ℕ → ℝ) => (√(T : ℝ))⁻¹ * ∑ k ∈ range (K T w), Y k w :=
    funext fun T => funext fun w => by
      rw [departureDiscrepancy_mc_eq P x₀ (fun w : Fin n × ℕ → ℝ => Function.curry w) g i w T]
      rfl
  have hmeas : ∀ T : ℕ, AEMeasurable (fun w => (√(T : ℝ))⁻¹ * ∑ k ∈ range (K T w), Y k w)
      (iidUniform (Fin n × ℕ)) := fun T => by
    have := ((measurable_departureDiscrepancy_div P g i T).comp
      (measurable_stackPath P x₀)).aemeasurable (μ := iidUniform (Fin n × ℕ))
    rw [show ((fun x : ℕ → Fin n => (√(T : ℝ))⁻¹ * departureDiscrepancy P g x i T) ∘
      fun w : Fin n × ℕ → ℝ => stackPath P x₀ (Function.curry w)) =
      fun w => (√(T : ℝ))⁻¹ * ∑ k ∈ range (K T w), Y k w from congrFun e T] at this
    exact this
  rw [e]
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ Z hdet ?_ hmeas
  convert hans using 1
  funext T w
  simp only [Pi.sub_apply]
  ring

/-- **The √T CLT for the MC departure discrepancies, MC driving** (one i.i.d. sequence, post
#3's construction). Under the hypotheses of `tendstoInDistribution_departureDiscrepancy_stack`,
for `u ∼ iidUniform ℕ`, `(1/√T) D_i(g, T) ⇒ N(0, c σ_i²(g))`. The two path laws agree
(`map_drivenPath_eq_map_stackPath_path`), so the laws of the statistic agree for every `T`. -/
theorem tendstoInDistribution_departureDiscrepancy_driven {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ} {i : Fin n} {c M : ℝ}
    (hh : ∀ k, h k - (P *ᵥ h) k = (if k = i then 1 else 0) - c) (hM : ∀ k, |h k| ≤ M)
    (hc : 0 < c) (g : Fin n → ℝ) {Ω' : Type*} [MeasurableSpace Ω'] {Q' : Measure Ω'}
    [IsProbabilityMeasure Q'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 (c * rowVariance P g i).toNNReal) Q') :
    haveI := isProbabilityMeasure_iidUniform ℕ
    TendstoInDistribution (fun (T : ℕ) (u : ℕ → ℝ) => (√(T : ℝ))⁻¹ *
      departureDiscrepancy P g (drivenPath P x₀ u) i T) atTop Z (fun _ => iidUniform ℕ) Q' := by
  have := isProbabilityMeasure_iidUniform ℕ
  have := isProbabilityMeasure_iidUniform (Fin n × ℕ)
  have hst := tendstoInDistribution_departureDiscrepancy_stack hP x₀ hh hM hc g hZ
  have hF := measurable_departureDiscrepancy_div P g i
  have hlaw : ∀ T : ℕ, (iidUniform (Fin n × ℕ)).map (fun w =>
      (√(T : ℝ))⁻¹ * departureDiscrepancy P g (stackPath P x₀ (Function.curry w)) i T) =
      (iidUniform ℕ).map (fun u =>
        (√(T : ℝ))⁻¹ * departureDiscrepancy P g (drivenPath P x₀ u) i T) := fun T => by
    have e1 := Measure.map_map (μ := iidUniform ℕ) (hF T) (measurable_drivenPath P x₀)
    have e2 := Measure.map_map (μ := iidUniform (Fin n × ℕ)) (hF T) (measurable_stackPath P x₀)
    rw [map_drivenPath_eq_map_stackPath_path hP x₀] at e1
    exact e2.symm.trans e1
  exact ⟨fun T => ((hF T).comp (measurable_drivenPath P x₀)).aemeasurable,
    hst.aemeasurable_limit, hst.tendsto.congr fun T => Subtype.ext (hlaw T)⟩

/-- **The √T CLT for the MC transition counts** (post #3's empirical transition matrix, at the
CLT scale). If Poisson's equation `h − Ph = 1_{i} − c` has a bounded solution and `c > 0`
(`c = π_i`), then for MC driving by one i.i.d. sequence, from any start,
`(N_ij(T) − p_ij N_i(T))/√T ⇒ N(0, π_i p_ij (1 − p_ij))`. -/
theorem tendstoInDistribution_transCount_driven {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ} {i : Fin n} {c M : ℝ}
    (hh : ∀ k, h k - (P *ᵥ h) k = (if k = i then 1 else 0) - c) (hM : ∀ k, |h k| ≤ M)
    (hc : 0 < c) (j : Fin n) {Ω' : Type*} [MeasurableSpace Ω'] {Q' : Measure Ω'}
    [IsProbabilityMeasure Q'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 (c * (P i j * (1 - P i j))).toNNReal) Q') :
    haveI := isProbabilityMeasure_iidUniform ℕ
    TendstoInDistribution (fun (T : ℕ) (u : ℕ → ℝ) => (√(T : ℝ))⁻¹ *
      ((transCount (drivenPath P x₀ u) i j T : ℝ) - P i j * occCount (drivenPath P x₀ u) i T))
      atTop Z (fun _ => iidUniform ℕ) Q' := by
  rw [← rowVariance_indicator hP i j] at hZ
  have e : (fun (T : ℕ) (u : ℕ → ℝ) => (√(T : ℝ))⁻¹ *
      ((transCount (drivenPath P x₀ u) i j T : ℝ) - P i j * occCount (drivenPath P x₀ u) i T)) =
      fun (T : ℕ) (u : ℕ → ℝ) => (√(T : ℝ))⁻¹ * departureDiscrepancy P
        (fun k => if k = j then 1 else 0) (drivenPath P x₀ u) i T :=
    funext fun T => funext fun u => by
      rw [transCount_sub_eq_departureDiscrepancy (P : Matrix (Fin n) (Fin n) ℝ)]
  rw [e]
  exact tendstoInDistribution_departureDiscrepancy_driven hP x₀ hh hM hc _ hZ

/-- **The √T CLT for irreducible chains.** For an irreducible stochastic `P` with stationary
distribution `π` (so `π_i > 0`), MC driving gives
`(N_ij(T) − p_ij N_i(T))/√T ⇒ N(0, π_i p_ij (1 − p_ij))` from any start. -/
theorem tendstoInDistribution_transCount_driven_of_irreducible
    {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsStochastic P) (hirr : ∀ i j, ∃ k, 0 < (P ^ k) i j)
    {μ : Fin n → ℝ} (hμ : IsStationaryDistribution P μ) (x₀ i j : Fin n) {Ω' : Type*}
    [MeasurableSpace Ω'] {Q' : Measure Ω'} [IsProbabilityMeasure Q'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 (μ i * (P i j * (1 - P i j))).toNNReal) Q') :
    haveI := isProbabilityMeasure_iidUniform ℕ
    TendstoInDistribution (fun (T : ℕ) (u : ℕ → ℝ) => (√(T : ℝ))⁻¹ *
      ((transCount (drivenPath P x₀ u) i j T : ℝ) - P i j * occCount (drivenPath P x₀ u) i T))
      atTop Z (fun _ => iidUniform ℕ) Q' := by
  have : Nonempty (Fin n) := ⟨x₀⟩
  obtain ⟨h, hh⟩ := exists_poisson hP.nonneg hP.sum_eq_one hirr hμ
    (fun k => if k = i then (1 : ℝ) else 0)
  rw [dotProduct_indicator] at hh
  exact tendstoInDistribution_transCount_driven hP x₀ hh (M := ∑ k, |h k|)
    (fun k => single_le_sum (f := fun k => |h k|) (fun _ _ => abs_nonneg _) (mem_univ k))
    (hμ.pos hP.nonneg hirr i) j hZ

/-- **A concrete instance** (two-state chain with stay probability `7/8`, `π = (1/2, 1/2)`):
for MC driving from any start, `(N_00(T) − (7/8) N_0(T))/√T ⇒ N(0, 7/128)`, realised by the
identity on `(ℝ, N(0, 7/128))`. -/
theorem tendstoInDistribution_transCount_twoStateStay78 (x₀ : Fin 2) :
    haveI := isProbabilityMeasure_iidUniform ℕ
    TendstoInDistribution (fun (T : ℕ) (u : ℕ → ℝ) => (√(T : ℝ))⁻¹ *
      ((transCount (drivenPath twoStateStay78 x₀ u) 0 0 T : ℝ) -
        7 / 8 * occCount (drivenPath twoStateStay78 x₀ u) 0 T))
      atTop id (fun _ => iidUniform ℕ) (gaussianReal 0 (7 / 128 : ℝ).toNNReal) := by
  have h00 : twoStateStay78 0 0 = 7 / 8 := by simp only [twoStateStay78, ite_true]
  have hv : (1 / 2 : ℝ) * (twoStateStay78 0 0 * (1 - twoStateStay78 0 0)) = 7 / 128 := by
    rw [h00]
    norm_num
  have hZ : HasLaw id (gaussianReal 0 ((1 / 2 : ℝ) * (twoStateStay78 0 0 *
      (1 - twoStateStay78 0 0))).toNNReal) (gaussianReal 0 (7 / 128 : ℝ).toNNReal) := by
    rw [hv]
    exact HasLaw.id
  have := tendstoInDistribution_transCount_driven_of_irreducible isStochastic_twoStateStay78
    irreducible_twoStateStay78 isStationaryDistribution_twoStateStay78 x₀ 0 0 hZ
  rw [h00] at this
  exact this

end RQMCMarkov.MarkovDriving

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # Rotor walks have too-regular spells (post #3)

Post #3: "Rotors perform poorly in terms of spell lengths because their balanced ordering makes
the path too regular … Under the Markov chain spell lengths in state `i` are geometric with stay
probability `p_ii` … in the two-state chain every spell lasts exactly 8 periods, rather than
being geometric with mean 8."

**General facts.**
* `occCount_add_of_stay`: while the path stays in `i`, each period is one more departure.
* `rotorWalk_shift` (in `RotorRouter`): the rotor walk after any time is the rotor walk started
  from the current state and rotor positions, so a spell's length is a deterministic function
  of the rotor position at its start.
* `rotorWalk_not_stay`, `runLength_rotorWalk_le`: if the cycle of `i` contains an entry
  `≠ i` (e.g. `p_ii < 1` for a balanced cycle, `exists_ne_of_lt_one`), the walk never spends
  more than `L i` consecutive periods in `i`: every spell in `i` has length `≤ L i`.
* `sum_geomPMF`: under the Markov chain, the spell length is geometric,
  `P(len = k) = p^{k−1}(1 − p)` (`geomPMF`), and `P(len > L) = p^L > 0`. So the empirical
  distribution of rotor spell lengths, which puts no mass above `L i`, stays at distance
  `≥ p_ii^{L i}` from the geometric law for every `T` (`rotor_spells_not_geometric`).

**The two-state chain with `p_ii = 7/8`** (`twoStateStay78`, balanced cycle `cycle78`: seven
stays then a switch, length `8`):
* `rotorWalk78_canonical`: with zero offsets the walk is `x_t = x₀` for `⌊t/8⌋` even and the
  other state for `⌊t/8⌋` odd: every spell, including the first, lasts exactly `8` periods.
* `rotorWalk78_eventually_canonical`, `runLength_rotorWalk78`: for **any** offsets (in
  particular for the randomized rotor) there is `τ ≤ 16` after which the walk is the canonical
  one: after the first spell in each state, every spell lasts exactly `8` periods, and the spell
  starts after `τ` are exactly `τ + 8k`.
* `rotor78_spells_not_geometric`: at most `16` spells ever have a length other than `8`, while
  the geometric law gives `P(len = 8) = (7/8)^7/8 < 1/16`.

**Reading.** "Every spell lasts exactly 8 periods" is exact for the rotor started at the
beginning of both cycles, and holds after the first spell in each state for arbitrary starting
points of the cycles.
-/

namespace RQMCMarkov.MarkovDriving

open Finset

variable {S : Type*} [DecidableEq S]

/-- While the path stays in `i` during `t, …, t + m − 1`, the visit count grows by one per
period. -/
theorem occCount_add_of_stay {x : ℕ → S} {i : S} {t m : ℕ} (h : ∀ k < m, x (t + k) = i) :
    occCount x i (t + m) = occCount x i t + m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← add_assoc, occCount_succ, ih fun k hk => h k (by omega), h m (by omega)]
    simp only [ite_true]
    ring

/-- **No overlong stays in a rotor walk**: if the cycle of `i` has an entry `≠ i`, the walk
never spends `L i + 1` consecutive periods in `i`. -/
theorem rotorWalk_not_stay {L : S → ℕ} {c : S → ℕ → S} (θ : S → ℕ) (x₀ : S) {i : S}
    (hne : ∃ m < L i, c i m ≠ i) (t : ℕ) : ∃ m ≤ L i, rotorWalk L c θ x₀ (t + m) ≠ i := by
  by_contra hcon
  push Not at hcon
  set x := rotorWalk L c θ x₀ with hx
  set a := θ i + occCount x i t with ha
  -- every departure in the window stays in `i`
  have hstay : ∀ m < L i, c i ((a + m) % L i) = i := by
    intro m hm
    have h1 := rotorWalk_succ L c θ x₀ (t + m)
    rw [← hx, hcon m hm.le, occCount_add_of_stay fun k hk => hcon k (by omega)] at h1
    rw [ha, add_assoc, ← h1, add_assoc]
    exact hcon (m + 1) hm
  obtain ⟨m₀, hm₀, hcm₀⟩ := hne
  have hper : ∀ k, (fun m => if c i (m % L i) = i then (0 : ℤ) else 1) (k + L i) =
      (fun m => if c i (m % L i) = i then (0 : ℤ) else 1) k := fun k => by
    simp only [Nat.add_mod_right]
  have hsum := sum_range_add_periodic
    (F := fun m => if c i (m % L i) = i then (0 : ℤ) else 1) (L := L i) hper a
  have hleft : ∑ m ∈ range (L i), (fun m => if c i (m % L i) = i then (0 : ℤ) else 1) (a + m) =
      0 := sum_eq_zero fun m hm => by simp only [hstay m (mem_range.1 hm), ite_true]
  have hright : (1 : ℤ) ≤
      ∑ m ∈ range (L i), (fun m => if c i (m % L i) = i then (0 : ℤ) else 1) m := by
    refine le_trans ?_ (single_le_sum (f := fun m => if c i (m % L i) = i then (0 : ℤ) else 1)
      (fun m _ => by split_ifs <;> norm_num) (mem_range.2 hm₀))
    simp only [Nat.mod_eq_of_lt hm₀, hcm₀, ite_false, le_refl]
  beta_reduce at hsum hleft hright
  rw [hleft] at hsum
  rw [← hsum] at hright
  exact absurd hright (by norm_num)

/-- **Rotor spells are bounded**: if the cycle of `i` has an entry `≠ i`, every run of the rotor
walk in state `i` has length at most `L i` (whatever the horizon). -/
theorem runLength_rotorWalk_le {L : S → ℕ} {c : S → ℕ → S} (θ : S → ℕ) (x₀ : S) {i : S}
    (hne : ∃ m < L i, c i m ≠ i) {t : ℕ} (ht : rotorWalk L c θ x₀ t = i) (T : ℕ) :
    runLength (rotorWalk L c θ x₀) t T ≤ L i := by
  unfold runLength
  obtain ⟨m, hm, hmne⟩ := rotorWalk_not_stay θ x₀ hne t
  calc ((range (T - t)).filter fun k => ∀ m ≤ k,
        rotorWalk L c θ x₀ (t + m) = rotorWalk L c θ x₀ t).card ≤ (range (L i)).card := by
        refine card_le_card fun k hk => ?_
        rw [mem_filter] at hk
        rw [mem_range]
        by_contra hkL
        exact hmne ((hk.2 m (by omega)).trans ht)
    _ = L i := card_range _

/-- For a balanced cycle (`IsRotorCycle`) and `p_ii < 1`, the cycle of `i` has an entry `≠ i`. -/
theorem exists_ne_of_lt_one {P : Matrix S S ℝ} {L : S → ℕ} {c : S → ℕ → S}
    (hc : IsRotorCycle P L c) {i : S} (hlt : P i i < 1) : ∃ m < L i, c i m ≠ i := by
  by_contra hcon
  push Not at hcon
  have hall : (range (L i)).filter (fun m => c i m = i) = range (L i) :=
    filter_true_of_mem fun m hm => hcon m (mem_range.1 hm)
  have h := hc.card_eq i i
  rw [hall, card_range] at h
  have hL : (0 : ℝ) < L i := by exact_mod_cast hc.len_pos i
  nlinarith

/-- The **geometric law of spell lengths** under the Markov chain with stay probability `p`:
`P(len = k) = p^{k−1} (1 − p)` for `k ≥ 1`. -/
noncomputable def geomPMF (p : ℝ) (k : ℕ) : ℝ := if k = 0 then 0 else p ^ (k - 1) * (1 - p)

/-- `P(len ≤ L) = 1 − p^L`, i.e. the geometric tail is `P(len > L) = p^L`. -/
theorem sum_geomPMF (p : ℝ) (L : ℕ) : ∑ k ∈ range (L + 1), geomPMF p k = 1 - p ^ L := by
  induction L with
  | zero => simp only [zero_add, sum_range_one, geomPMF, ite_true, pow_zero, sub_self]
  | succ L ih =>
    rw [sum_range_succ, ih]
    simp only [geomPMF, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    ring

/-- **Correction: rotor paths are not representative in spell lengths.** If `0 < p_ii` and the
cycle of `i` has an entry `≠ i`, every rotor spell in `i` has length `≤ L i`, whereas the
geometric law gives positive probability `p_ii^{L i}` to longer spells: the empirical spell
length distribution of the rotor walk never comes closer than `p_ii^{L i}` to the geometric
law. -/
theorem rotor_spells_not_geometric {L : S → ℕ} {c : S → ℕ → S} (θ : S → ℕ) (x₀ : S) {i : S}
    (hne : ∃ m < L i, c i m ≠ i) {p : ℝ} (hp : 0 < p) :
    (∀ t T, rotorWalk L c θ x₀ t = i → runLength (rotorWalk L c θ x₀) t T ≤ L i) ∧
      0 < 1 - ∑ k ∈ range (L i + 1), geomPMF p k := by
  refine ⟨fun t T ht => runLength_rotorWalk_le θ x₀ hne ht T, ?_⟩
  rw [sum_geomPMF, sub_sub_cancel]
  exact pow_pos hp _

/-! ### The two-state chain with stay probability `7/8` -/

/-- The cycle length `8` of the `7/8` chain. -/
def len78 : Fin 2 → ℕ := fun _ => 8

/-- The balanced cycle of the `7/8` chain: seven stays, then a switch. -/
def cycle78 : Fin 2 → ℕ → Fin 2 :=
  fun i m => if m % 8 = 7 then (if i = 0 then 1 else 0) else i

/-- The other state of a two-state chain. -/
def otherState (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

/-- `cycle78` is a balanced cycle for `twoStateStay78`: `7` stays and `1` switch out of `8`. -/
theorem isRotorCycle78 : IsRotorCycle twoStateStay78 len78 cycle78 := by
  have hcard : ∀ i j : Fin 2, ((range 8).filter fun m => cycle78 i m = j).card =
      if i = j then 7 else 1 := by decide +kernel
  refine ⟨fun _ => Nat.succ_pos 7, fun i j => ?_⟩
  change (((range 8).filter fun m => cycle78 i m = j).card : ℝ) = twoStateStay78 i j * (8 : ℕ)
  rw [hcard i j]
  simp only [twoStateStay78]
  split_ifs <;> norm_num

/-- The canonical walk on its first two spells (checked by evaluation). -/
theorem rotorWalk78_lt_sixteen :
    ∀ x₀ : Fin 2, ∀ t < 16, rotorWalk len78 cycle78 (fun _ => 0) x₀ t =
      if t / 8 % 2 = 0 then x₀ else otherState x₀ := by
  decide +kernel

/-- After `16` periods the canonical walk is back at its start, with both rotors at the start of
their cycles. -/
theorem rotorWalk78_sixteen :
    ∀ x₀ : Fin 2, rotorWalk len78 cycle78 (fun _ => 0) x₀ 16 = x₀ ∧
      ∀ i : Fin 2, occCount (rotorWalk len78 cycle78 (fun _ => 0) x₀) i 16 = 8 := by
  decide +kernel

/-- **Every spell lasts exactly 8 periods** (post #3), for the rotor started at the beginning of
both cycles: `x_t = x₀` when `⌊t/8⌋` is even and the other state when it is odd. -/
theorem rotorWalk78_canonical (x₀ : Fin 2) (t : ℕ) :
    rotorWalk len78 cycle78 (fun _ => 0) x₀ t = if t / 8 % 2 = 0 then x₀ else otherState x₀ := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < 16
    · exact rotorWalk78_lt_sixteen x₀ t ht
    · obtain ⟨t', rfl⟩ : ∃ t', t = 16 + t' := ⟨t - 16, by omega⟩
      obtain ⟨h16, hocc⟩ := rotorWalk78_sixteen x₀
      rw [rotorWalk_shift, h16]
      have hmod : rotorWalk len78 cycle78 (fun i => 0 +
          occCount (rotorWalk len78 cycle78 (fun _ => 0) x₀) i 16) x₀ =
          rotorWalk len78 cycle78 (fun _ => 0) x₀ :=
        rotorWalk_congr_mod len78 cycle78 (fun i => by
          rw [hocc i]
          simp only [len78, Nat.zero_add, Nat.mod_self, Nat.zero_mod]) x₀
      rw [hmod, ih t' (by omega)]
      have e : (16 + t') / 8 % 2 = t' / 8 % 2 := by omega
      rw [e]

/-- Offsets reduced modulo `8`. -/
def offsets78 (a b : ℕ) : Fin 2 → ℕ := fun i => if i = 0 then a else b

/-- From offsets `(a, b)`, the walk reaches its start with both rotors at the start of their
cycles at time `16 − a − b` (checked by evaluation for all `a, b < 8`). -/
theorem rotorWalk78_return :
    ∀ a < 8, ∀ b < 8, ∀ x₀ : Fin 2,
      rotorWalk len78 cycle78 (offsets78 a b) x₀ (16 - a - b) = x₀ ∧
      ∀ i : Fin 2, (offsets78 a b i +
        occCount (rotorWalk len78 cycle78 (offsets78 a b) x₀) i (16 - a - b)) % len78 i = 0 := by
  decide +kernel

/-- **For any starting points of the cycles** (e.g. the randomized rotor), the `7/8` rotor walk
is the canonical walk after some time `τ ≤ 16`, i.e. after the first spell in each state. -/
theorem rotorWalk78_eventually_canonical (θ : Fin 2 → ℕ) (x₀ : Fin 2) :
    ∃ τ ≤ 16, ∀ t, rotorWalk len78 cycle78 θ x₀ (τ + t) =
      if t / 8 % 2 = 0 then x₀ else otherState x₀ := by
  have hθ : rotorWalk len78 cycle78 θ x₀ =
      rotorWalk len78 cycle78 (offsets78 (θ 0 % 8) (θ 1 % 8)) x₀ :=
    rotorWalk_congr_mod len78 cycle78 (fun i => by
      fin_cases i
      · exact (Nat.mod_mod (θ 0) 8).symm
      · exact (Nat.mod_mod (θ 1) 8).symm) x₀
  obtain ⟨hret, hpos⟩ := rotorWalk78_return (θ 0 % 8) (Nat.mod_lt _ (by norm_num))
    (θ 1 % 8) (Nat.mod_lt _ (by norm_num)) x₀
  refine ⟨16 - θ 0 % 8 - θ 1 % 8, by omega, fun t => ?_⟩
  rw [hθ, rotorWalk_shift, hret]
  rw [rotorWalk_congr_mod len78 cycle78 (θ' := fun _ => 0) (fun i => by
    rw [hpos i, Nat.zero_mod]) x₀]
  exact rotorWalk78_canonical x₀ t

/-- The other state differs. -/
theorem otherState_ne (i : Fin 2) : otherState i ≠ i := by
  fin_cases i <;> decide

/-- **Spells of the `7/8` rotor walk**: for any offsets there is `τ ≤ 16` such that the spells
starting at `τ + 8k` last exactly `8` periods (`k = 0, 1, …`), and no other spell starts after
`τ`. -/
theorem runLength_rotorWalk78 (θ : Fin 2 → ℕ) (x₀ : Fin 2) :
    ∃ τ ≤ 16, (∀ k T, τ + 8 * k + 8 < T →
        runLength (rotorWalk len78 cycle78 θ x₀) (τ + 8 * k) T = 8) ∧
      ∀ t, τ < t → IsSpellStart (rotorWalk len78 cycle78 θ x₀) t → ∃ k, t = τ + 8 * k := by
  obtain ⟨τ, hτ, hx⟩ := rotorWalk78_eventually_canonical θ x₀
  set x := rotorWalk len78 cycle78 θ x₀
  refine ⟨τ, hτ, fun k T hT => ?_, fun t ht hs => ?_⟩
  · refine runLength_eq_of_exit hT (fun m hm => ?_) ?_
    · rw [add_assoc, hx, hx]
      have e : (8 * k + m) / 8 = 8 * k / 8 := by omega
      rw [e]
    · rw [add_assoc, hx, hx]
      by_cases h0 : 8 * k / 8 % 2 = 0
      · have h1 : ¬ ((8 * k + 8) / 8 % 2 = 0) := by omega
        simp only [h0, h1, ite_true, ite_false]
        exact otherState_ne x₀
      · have h1 : (8 * k + 8) / 8 % 2 = 0 := by omega
        simp only [h0, h1, ite_true, ite_false]
        exact (otherState_ne x₀).symm
  · rcases hs with h0 | hne
    · omega
    obtain ⟨s, rfl⟩ : ∃ s, t = τ + (s + 1) := ⟨t - τ - 1, by omega⟩
    have e1 : τ + (s + 1) - 1 = τ + s := by omega
    rw [e1, hx, hx] at hne
    refine ⟨(s + 1) / 8, ?_⟩
    by_contra hcon
    have hdiv : s / 8 = (s + 1) / 8 := by omega
    rw [hdiv] at hne
    exact hne rfl

/-- **The `7/8` rotor walk is not representative in spell lengths** (post #3): for any offsets,
at most `16` spells ever have a length other than `8` (counting the spells that end before
the horizon), whereas under the Markov chain a spell has length `8` with probability only
`(7/8)^7 (1/8) < 1/16`. -/
theorem rotor78_spells_not_geometric (θ : Fin 2 → ℕ) (x₀ : Fin 2) :
    (∀ T, ((range T).filter fun t => IsSpellStart (rotorWalk len78 cycle78 θ x₀) t ∧
        t + 8 < T ∧ runLength (rotorWalk len78 cycle78 θ x₀) t T ≠ 8).card ≤ 16) ∧
      geomPMF (7 / 8) 8 < 1 / 16 := by
  refine ⟨fun T => ?_, ?_⟩
  · obtain ⟨τ, hτ, hlen, hstart⟩ := runLength_rotorWalk78 θ x₀
    calc _ ≤ (range τ).card := by
          refine card_le_card fun t ht => ?_
          rw [mem_filter] at ht
          rw [mem_range]
          by_contra hτt
          rcases lt_or_eq_of_le (not_lt.1 hτt) with hlt | heq
          · obtain ⟨k, rfl⟩ := hstart t hlt ht.2.1
            exact ht.2.2.2 (hlen k T (by omega))
          · subst heq
            exact ht.2.2.2 (by simpa only [mul_zero, add_zero] using hlen 0 T (by omega))
      _ ≤ 16 := by rw [card_range]; exact hτ
  · simp only [geomPMF]
    norm_num

end RQMCMarkov.MarkovDriving

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Spell lengths: geometric under MC, and stratified sampling of them (post #3, approach (vii))

Post #3: "a path can also be seen as a sequence of spells … Under the Markov chain spell lengths in
state `i` are geometric with stay probability `p_ii`", and approach (vii) draws "the spell lengths
in each state by stratified sampling from the geometric distribution (one draw in each of `K`
equal intervals, where `K` is the number of spells in that state) rather than at random,
adjusting them slightly so they add up to the total time spent in that state".

**Readings.** (1) "Geometric": for MC from `x₀`, after any history `s_0, …, s_t` with `s_t = i`,
the event "exactly `k − 1` further periods in `i`, then an exit" has probability
`P(history) · p_ii^{k−1}(1 − p_ii)`, so conditionally on the past at the start of a stay in `i`
the length of the stay is geometric on `{1, 2, …}`; in particular the first spell of a chain
started in `i` (`runLength` from time `0`) has this law. (2) "Stratified sampling from the
geometric distribution": `L_k = G((k + V_k)/K)`, `k < K`, with `V_k` i.i.d. `U[0,1)` and `G` the
geometric inverse CDF `geomQuantile p` (`G(u)` = least `k ≥ 1` with `u < 1 − p^k`; using `<`
rather than post #3's `≤` changes `G` only on a null set). "Better than at random" is read as:
unbiased for the mean spell length, with variance at most that of `K` i.i.d. draws.

## Main results

* `iidUniform_spell_after_history`, `iidUniform_firstSpell`, `iidUniform_runLength_eq`: MC spell
  lengths are geometric with stay probability `p_ii` (`pathProb_extend_stay`,
  `uniformIco_step_ne` are the steps).
* `geomQuantile`, `geomQuantile_eq_succ_iff`, `geomQuantile_eq_zero_iff`,
  `measurable_geomQuantile`, `geomQuantile_preimage_inter_Ico`; `uniformIco_geomQuantile_eq_succ`
  (`P(G(U) = k + 1) = p^k (1 − p)`) and `uniformIco_geomQuantile_eq_firstSpell` (the law of
  `G(U)` is the MC spell-length law).
* `lintegral_geomQuantile`, `integral_geomQuantile`, `memLp_geomQuantile`;
  `integral_geomQuantile_id` (`E[L] = 1/(1 − p)`, e.g. `8` for post #3's `p = 7/8`),
  `integral_geomQuantile_sq`, `variance_geomQuantile` (`Var(L) = p/(1 − p)²`).
* `variance_stratified_le_div`: generic — stratified inverse-CDF sampling of any `f ∈ L²` has
  variance at most `Var(f(U))/K`.
* `integral_stratifiedSpell`: the stratified spell lengths are unbiased for `1/(1 − p)`;
  `variance_stratifiedSpell_le_iid`: their mean has variance at most that of `K` i.i.d. spell
  lengths; `variance_stratifiedSpell_le`: explicitly `≤ p/((1 − p)² K)`.

**Not formalised.** The "adjusting them slightly so they add up to the total time spent in that
state" step is a heuristic (it changes the joint law in an unspecified way) and is not
formalised; neither is the random ordering of the spells, nor the "three to four times more
accurate" simulation finding.
-/

namespace RQMCMarkov.MarkovDriving

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

variable {n : ℕ}

/-- Extending a history `s` (up to time `t`, with `s t = i`) by staying in `i` multiplies its
path probability by `P i i` per period. -/
theorem pathProb_extend_stay (P : Fin n → Fin n → ℝ) (x₀ i : Fin n) (s : ℕ → Fin n) {t : ℕ}
    (hst : s t = i) (j : ℕ) :
    pathProb P x₀ (fun m ↦ if m ≤ t then s m else i) (t + j) = pathProb P x₀ s t * P i i ^ j := by
  induction j with
  | zero =>
    rw [add_zero, pow_zero, mul_one]
    unfold pathProb
    simp only [Nat.zero_le, ↓reduceIte]
    congr 1
    refine Finset.prod_congr rfl fun m hm ↦ ?_
    have hm' := Finset.mem_range.1 hm
    simp only [hm'.le, show m + 1 ≤ t by omega, ↓reduceIte]
  | succ j ih =>
    rw [← add_assoc, pathProb_succ, ih, pow_succ, mul_assoc]
    have e1 : (if t + j ≤ t then s (t + j) else i) = i := by
      split_ifs with hj
      · rw [show t + j = t by omega, hst]
      · rfl
    have e2 : (if t + j + 1 ≤ t then s (t + j + 1) else i) = i := by
      split_ifs with hj
      · omega
      · rfl
    rw [e1, e2]

/-- `uniformIco {r : step P i r ≠ i} = 1 − P i i`. -/
theorem uniformIco_step_ne {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n) :
    uniformIco {r | step P i r ≠ i} = ENNReal.ofReal (1 - P i i) := by
  have := isProbabilityMeasure_uniformIco
  have hc : {r | step P i r ≠ i} = {r | step P i r = i}ᶜ := rfl
  rw [hc, prob_compl_eq_one_sub (measurableSet_step_eq P i i), uniformIco_step_eq hP,
    ENNReal.ofReal_sub _ (hP.nonneg i i), ENNReal.ofReal_one]

/-- **Spell lengths are geometric, after any history** (post #3: "under the Markov chain spell
lengths in state `i` are geometric with stay probability `p_ii`"): for MC from `x₀`, any history
`s_0, …, s_t` ending in `s_t = i`, and `k ≥ 1`, the probability of that history followed by
exactly `k − 1` further periods in `i` and then an exit is
`P(history) · p_ii^{k−1} (1 − p_ii)`. So, conditional on the past up to the start of a stay in `i`
(e.g. a spell start), the remaining length of the stay is geometric. -/
theorem iidUniform_spell_after_history {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ i : Fin n) (s : ℕ → Fin n) {t k : ℕ} (hst : s t = i) (hk : 1 ≤ k) :
    iidUniform ℕ {u | (∀ m ≤ t, drivenPath P x₀ u m = s m) ∧
        (∀ m < k, drivenPath P x₀ u (t + m) = i) ∧ drivenPath P x₀ u (t + k) ≠ i} =
      ENNReal.ofReal (pathProb P x₀ s t * (P i i ^ (k - 1) * (1 - P i i))) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  set s' : ℕ → Fin n := fun m ↦ if m ≤ t then s m else i with hs'
  set B : ℕ → Set ℝ := fun m ↦
    if m < t + j then {r | step P (s' m) r = s' (m + 1)} else {r | step P i r ≠ i} with hB
  have hs'i : ∀ m, t ≤ m → s' m = i := fun m hm ↦ by
    by_cases hmt : m ≤ t
    · simp only [hs', hmt, ↓reduceIte]
      rw [show m = t by omega, hst]
    · simp only [hs', hmt, ↓reduceIte]
  have hset : {u | (∀ m ≤ t, drivenPath P x₀ u m = s m) ∧
      (∀ m < j + 1, drivenPath P x₀ u (t + m) = i) ∧ drivenPath P x₀ u (t + (j + 1)) ≠ i} =
      {u | s' 0 = x₀ ∧ ∀ m < t + j + 1, u (id m) ∈ B m} := by
    ext u
    simp only [Set.mem_ofPred_eq, id, drivenPath]
    constructor
    · rintro ⟨hA, hBu, hC⟩
      have hD : ∀ m ≤ t + j, drive (step P) x₀ u m = s' m := fun m hm ↦ by
        by_cases hmt : m ≤ t
        · simp only [hs', hmt, ↓reduceIte]
          exact hA m hmt
        · have := hBu (m - t) (by omega)
          rw [show t + (m - t) = m by omega] at this
          rw [this, hs'i m (by omega)]
      obtain ⟨h0, hstep⟩ := (drive_eq_iff (step P) x₀ u s' (t + j)).1 hD
      refine ⟨h0, fun m hm ↦ ?_⟩
      by_cases hmj : m < t + j
      · simp only [hB, hmj, ↓reduceIte, Set.mem_ofPred_eq]
        exact hstep m hmj
      · simp only [hB, hmj, ↓reduceIte, Set.mem_ofPred_eq]
        rw [show m = t + j by omega]
        have h1 : drive (step P) x₀ u (t + (j + 1)) =
            step P (drive (step P) x₀ u (t + j)) (u (t + j)) := rfl
        rw [h1, hBu j (Nat.lt_succ_self j)] at hC
        exact hC
    · rintro ⟨h0, hm⟩
      have hstep : ∀ m < t + j, step P (s' m) (u m) = s' (m + 1) := fun m hmj ↦ by
        have := hm m (by omega)
        simp only [hB, hmj, ↓reduceIte, Set.mem_ofPred_eq] at this
        exact this
      have hD := (drive_eq_iff (step P) x₀ u s' (t + j)).2 ⟨h0, hstep⟩
      have hend : drive (step P) x₀ u (t + j) = i := by
        rw [hD (t + j) le_rfl, hs'i (t + j) (by omega)]
      refine ⟨fun m hm' ↦ ?_, fun m hm' ↦ ?_, ?_⟩
      · rw [hD m (by omega)]
        simp only [hs', hm', ↓reduceIte]
      · rw [hD (t + m) (by omega), hs'i (t + m) (by omega)]
      · have h1 : drive (step P) x₀ u (t + (j + 1)) =
            step P (drive (step P) x₀ u (t + j)) (u (t + j)) := rfl
        have := hm (t + j) (by omega)
        simp only [hB, lt_irrefl, ↓reduceIte, Set.mem_ofPred_eq] at this
        rw [h1, hend]
        exact this
  have hBm : ∀ m, MeasurableSet (B m) := fun m ↦ by
    simp only [hB]
    split_ifs
    · exact measurableSet_step_eq P _ _
    · exact (measurableSet_step_eq P i i).compl
  have := isProbabilityMeasure_uniformIco
  unfold iidUniform
  rw [hset]
  have hs0 : s' 0 = s 0 := by simp only [hs', Nat.zero_le, ↓reduceIte]
  by_cases h0 : s' 0 = x₀
  · simp only [h0, true_and]
    rw [infinitePi_setOf_forall_mem uniformIco Function.injective_id hBm, Finset.prod_range_succ]
    have hpre : ∏ m ∈ range (t + j), uniformIco (B m) =
        ∏ m ∈ range (t + j), uniformIco {r | step P (s' m) r = s' (m + 1)} :=
      Finset.prod_congr rfl fun m hm ↦ by
        simp only [hB, Finset.mem_range.1 hm, ↓reduceIte]
    have hlast : B (t + j) = {r | step P i r ≠ i} := by
      simp only [hB, lt_irrefl, ↓reduceIte]
    rw [hpre, hlast, prod_uniformIco_step_eq hP s' (t + j), uniformIco_step_ne hP,
      ← ENNReal.ofReal_mul (Finset.prod_nonneg fun m _ ↦ hP.nonneg _ _)]
    congr 1
    have hext : pathProb P x₀ s' (t + j) = pathProb P x₀ s t * P i i ^ j :=
      pathProb_extend_stay P x₀ i s hst j
    have hprod : ∏ m ∈ range (t + j), P (s' m) (s' (m + 1)) = pathProb P x₀ s' (t + j) := by
      unfold pathProb
      exact (ite_eq_left_of_eq_true _ _ (eq_true h0)).symm
    rw [hprod, hext, mul_assoc]
  · simp only [h0, false_and, Set.ofPred_false, measure_empty]
    unfold pathProb
    rw [← hs0]
    simp only [h0, ↓reduceIte, zero_mul, ENNReal.ofReal_zero]

/-- **The first spell is geometric** (post #3): for MC started in `i` and `k ≥ 1`,
`P(x_1 = … = x_{k−1} = i, x_k ≠ i) = p_ii^{k−1} (1 − p_ii)`. -/
theorem iidUniform_firstSpell {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n) {k : ℕ}
    (hk : 1 ≤ k) :
    iidUniform ℕ {u | (∀ m < k, drivenPath P i u m = i) ∧ drivenPath P i u k ≠ i} =
      ENNReal.ofReal (P i i ^ (k - 1) * (1 - P i i)) := by
  have h := iidUniform_spell_after_history hP i i (fun _ ↦ i) (t := 0) rfl hk
  have hp : pathProb P i (fun _ ↦ i) 0 = 1 := by
    unfold pathProb
    simp only [↓reduceIte, Finset.range_zero, Finset.prod_empty]
  rw [hp, one_mul] at h
  rw [← h]
  congr 1
  ext u
  simp only [Set.mem_ofPred_eq, zero_add]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun m hm ↦ ?_, h1, h2⟩
    rw [Nat.le_zero.1 hm]
    rfl
  · rintro ⟨-, h1, h2⟩
    exact ⟨h1, h2⟩

/-- **The first spell length, as `runLength`** (post #3): for MC started in `i`, `1 ≤ k < T`,
`P(runLength = k) = p_ii^{k−1} (1 − p_ii)`, the geometric law with stay probability `p_ii`. -/
theorem iidUniform_runLength_eq {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n)
    {k T : ℕ} (hk : 1 ≤ k) (hkT : k < T) :
    iidUniform ℕ {u | runLength (drivenPath P i u) 0 T = k} =
      ENNReal.ofReal (P i i ^ (k - 1) * (1 - P i i)) := by
  rw [← iidUniform_firstSpell hP i hk]
  congr 1
  ext u
  simp only [Set.mem_ofPred_eq]
  rw [runLength_eq_iff (by omega)]
  simp only [zero_add]
  rfl

/-! ### The geometric inverse CDF and stratified spell lengths -/

/-- **The geometric inverse CDF** with stay probability `p`: `geomQuantile p u` is the smallest
`k ≥ 1` with `u < 1 − p^k` (`P(L ≤ k) = 1 − p^k` for a spell length `L`), and `0` if there is
none (only for `u ≥ 1`, or `p ≥ 1`). -/
noncomputable def geomQuantile (p u : ℝ) : ℕ := by
  classical
  exact if h : ∃ k : ℕ, u < 1 - p ^ (k + 1) then Nat.find h + 1 else 0

/-- The fibres of `geomQuantile` above `k + 1`. -/
theorem geomQuantile_eq_succ_iff (p u : ℝ) (k : ℕ) :
    geomQuantile p u = k + 1 ↔ u < 1 - p ^ (k + 1) ∧ ∀ m < k, 1 - p ^ (m + 1) ≤ u := by
  classical
  unfold geomQuantile
  split_ifs with h
  · rw [Nat.add_right_cancel_iff, Nat.find_eq_iff]
    simp only [not_lt]
  · constructor
    · intro h'
      exact h'.elim
    · rintro ⟨h1, -⟩
      exact absurd ⟨k, h1⟩ h

/-- The fibre of `geomQuantile` above `0`. -/
theorem geomQuantile_eq_zero_iff (p u : ℝ) :
    geomQuantile p u = 0 ↔ ∀ k : ℕ, 1 - p ^ (k + 1) ≤ u := by
  classical
  unfold geomQuantile
  split_ifs with h
  · constructor
    · intro h'
      exact h'.elim
    · intro h'
      obtain ⟨k, hk⟩ := h
      exact absurd (h' k) (not_le.2 hk)
  · push Not at h
    exact ⟨fun _ ↦ h, fun _ ↦ rfl⟩

/-- `geomQuantile p` is measurable. -/
theorem measurable_geomQuantile (p : ℝ) : Measurable (geomQuantile p) := by
  refine measurable_to_countable' fun k ↦ ?_
  rcases k with _ | k
  · have : geomQuantile p ⁻¹' {0} = ⋂ k : ℕ, Set.Ici (1 - p ^ (k + 1)) := by
      ext u
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_Ici]
      exact geomQuantile_eq_zero_iff p u
    rw [this]
    exact MeasurableSet.iInter fun _ ↦ measurableSet_Ici
  · have : geomQuantile p ⁻¹' {k + 1} =
        Set.Iio (1 - p ^ (k + 1)) ∩ ⋂ (m : ℕ) (_ : m < k), Set.Ici (1 - p ^ (m + 1)) := by
      ext u
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_Iio,
        Set.mem_iInter, Set.mem_Ici]
      exact geomQuantile_eq_succ_iff p u k
    rw [this]
    exact measurableSet_Iio.inter (MeasurableSet.iInter fun _ ↦ .iInter fun _ ↦ measurableSet_Ici)

variable {p : ℝ}

/-- On `[0,1)`, the fibre of `geomQuantile p` above `k + 1` is `[1 − p^k, 1 − p^{k+1})`. -/
theorem geomQuantile_preimage_inter_Ico (hp0 : 0 ≤ p) (hp1 : p < 1) (k : ℕ) :
    {u | geomQuantile p u = k + 1} ∩ Set.Ico 0 1 = Set.Ico (1 - p ^ k) (1 - p ^ (k + 1)) := by
  ext u
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ico, geomQuantile_eq_succ_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, hu0, -⟩
    refine ⟨?_, h1⟩
    rcases k with _ | k
    · rw [pow_zero, sub_self]
      exact hu0
    · exact h2 k (Nat.lt_succ_self k)
  · rintro ⟨h1, h2⟩
    have hpk : p ^ k ≤ 1 := pow_le_one₀ hp0 hp1.le
    have hpk1 : 0 ≤ p ^ (k + 1) := pow_nonneg hp0 _
    refine ⟨⟨h2, fun m hm ↦ le_trans ?_ h1⟩, by linarith, by linarith⟩
    have := pow_le_pow_of_le_one hp0 hp1.le (show m + 1 ≤ k by omega)
    linarith

/-- **The stratification target is the spell-length law**: under `U[0,1)`,
`P(geomQuantile p U = k + 1) = p^k (1 − p)`, the geometric law of the MC spell lengths
(`iidUniform_firstSpell`). -/
theorem uniformIco_geomQuantile_eq_succ (hp0 : 0 ≤ p) (hp1 : p < 1) (k : ℕ) :
    uniformIco {u | geomQuantile p u = k + 1} = ENNReal.ofReal (p ^ k * (1 - p)) := by
  rw [Measure.restrict_apply' measurableSet_Ico, geomQuantile_preimage_inter_Ico hp0 hp1,
    Real.volume_Ico]
  congr 1
  ring

/-- `geomQuantile p U ≥ 1` almost surely. -/
theorem uniformIco_geomQuantile_eq_zero (hp0 : 0 ≤ p) (hp1 : p < 1) :
    uniformIco {u | geomQuantile p u = 0} = 0 := by
  rw [Measure.restrict_apply' measurableSet_Ico]
  convert measure_empty (μ := (volume : Measure ℝ))
  ext u
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ico, geomQuantile_eq_zero_iff,
    Set.mem_empty_iff_false, iff_false, not_and]
  intro hall _ hu1
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < 1 - u by linarith) hp1
  have := hall N
  have := pow_le_pow_of_le_one hp0 hp1.le (show N ≤ N + 1 by omega)
  linarith

/-- **The stratified draws have the MC spell-length law**: for `k ≥ 1` and `p = P i i < 1`,
`P(geomQuantile p U = k)` equals the MC probability that the first spell in `i` lasts `k`. -/
theorem uniformIco_geomQuantile_eq_firstSpell {P : Fin n → Fin n → ℝ}
    (hP : IsStochastic P) (i : Fin n) (hp1 : P i i < 1) {k : ℕ} (hk : 1 ≤ k) :
    uniformIco {u | geomQuantile (P i i) u = k} =
      iidUniform ℕ {u | (∀ m < k, drivenPath P i u m = i) ∧ drivenPath P i u k ≠ i} := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [iidUniform_firstSpell hP i hk, Nat.add_sub_cancel,
    uniformIco_geomQuantile_eq_succ (hP.nonneg i i) hp1]

/-- Lebesgue integrals of functions of the geometric draw:
`∫⁻ g (geomQuantile p u) du = Σ_m g (m + 1) p^m (1 − p)`. -/
theorem lintegral_geomQuantile (hp0 : 0 ≤ p) (hp1 : p < 1) (g : ℕ → ℝ≥0∞) :
    ∫⁻ u, g (geomQuantile p u) ∂uniformIco =
      ∑' m : ℕ, g (m + 1) * ENNReal.ofReal (p ^ m * (1 - p)) := by
  rw [← lintegral_map measurable_from_nat (measurable_geomQuantile p), lintegral_countable',
    tsum_eq_zero_add' ENNReal.summable]
  have hmap : ∀ k, uniformIco.map (geomQuantile p) {k} = uniformIco {u | geomQuantile p u = k} :=
    fun k ↦ Measure.map_apply (measurable_geomQuantile p) (measurableSet_singleton k)
  rw [hmap, uniformIco_geomQuantile_eq_zero hp0 hp1, mul_zero, zero_add]
  exact tsum_congr fun m ↦ by rw [hmap, uniformIco_geomQuantile_eq_succ hp0 hp1]

/-- Summability of `(m + 1)^2 p^m (1 − p)`. -/
theorem summable_succ_sq_mul_geometric (hp0 : 0 ≤ p) (hp1 : p < 1) :
    Summable fun m : ℕ ↦ ((m : ℝ) + 1) ^ 2 * (p ^ m * (1 - p)) := by
  have hpn : ‖p‖ < 1 := by rwa [Real.norm_of_nonneg hp0]
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hpn
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hpn
  have h0 := summable_geometric_of_lt_one hp0 hp1
  refine (((h2.add (h1.mul_left 2)).add h0).mul_right (1 - p)).congr fun m ↦ ?_
  ring

/-- Summability of `(m + 1) p^m (1 − p)`. -/
theorem summable_succ_mul_geometric (hp0 : 0 ≤ p) (hp1 : p < 1) :
    Summable fun m : ℕ ↦ ((m : ℝ) + 1) * (p ^ m * (1 - p)) := by
  have hpn : ‖p‖ < 1 := by rwa [Real.norm_of_nonneg hp0]
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hpn
  have h0 := summable_geometric_of_lt_one hp0 hp1
  refine ((h1.add h0).mul_right (1 - p)).congr fun m ↦ ?_
  ring

/-- `∫ g ∘ geomQuantile = Σ_m g (m + 1) p^m (1 − p)` for nonnegative real `g`. -/
theorem integral_geomQuantile {g : ℕ → ℝ} (hg : ∀ k, 0 ≤ g k) (hp0 : 0 ≤ p) (hp1 : p < 1)
    (hs : Summable fun m : ℕ ↦ g (m + 1) * (p ^ m * (1 - p))) :
    ∫ u, g (geomQuantile p u) ∂uniformIco = ∑' m : ℕ, g (m + 1) * (p ^ m * (1 - p)) := by
  have hnn : ∀ m : ℕ, 0 ≤ g (m + 1) * (p ^ m * (1 - p)) := fun m ↦
    mul_nonneg (hg _) (mul_nonneg (pow_nonneg hp0 _) (by linarith))
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun u ↦ hg _)
    (measurable_from_nat.comp (measurable_geomQuantile p)).aestronglyMeasurable,
    lintegral_geomQuantile hp0 hp1 (fun k ↦ ENNReal.ofReal (g k))]
  have : ∀ m : ℕ, ENNReal.ofReal (g (m + 1)) * ENNReal.ofReal (p ^ m * (1 - p)) =
      ENNReal.ofReal (g (m + 1) * (p ^ m * (1 - p))) := fun m ↦
    (ENNReal.ofReal_mul (hg _)).symm
  rw [tsum_congr this, ← ENNReal.ofReal_tsum_of_nonneg hnn hs,
    ENNReal.toReal_ofReal (tsum_nonneg hnn)]

/-- The geometric draw has a finite second moment. -/
theorem memLp_geomQuantile (hp0 : 0 ≤ p) (hp1 : p < 1) :
    MemLp (fun u ↦ (geomQuantile p u : ℝ)) 2 uniformIco := by
  have hm : AEStronglyMeasurable (fun u ↦ (geomQuantile p u : ℝ)) uniformIco :=
    (measurable_from_nat.comp (measurable_geomQuantile p)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hm]
  refine ⟨hm.pow 2, ?_⟩
  change ∫⁻ u, ‖(geomQuantile p u : ℝ) ^ 2‖ₑ ∂uniformIco < ∞
  have he : ∀ u, ‖(geomQuantile p u : ℝ) ^ 2‖ₑ =
      ENNReal.ofReal (((geomQuantile p u : ℕ) : ℝ) ^ 2) := fun u ↦
    Real.enorm_eq_ofReal (sq_nonneg _)
  have hnn : ∀ m : ℕ, 0 ≤ ((m : ℝ) + 1) ^ 2 * (p ^ m * (1 - p)) := fun m ↦
    mul_nonneg (sq_nonneg _) (mul_nonneg (pow_nonneg hp0 _) (by linarith))
  rw [lintegral_congr fun u ↦ he u,
    lintegral_geomQuantile hp0 hp1 (fun k : ℕ ↦ ENNReal.ofReal ((k : ℝ) ^ 2))]
  have : ∀ m : ℕ, ENNReal.ofReal (((m + 1 : ℕ) : ℝ) ^ 2) * ENNReal.ofReal (p ^ m * (1 - p)) =
      ENNReal.ofReal (((m : ℝ) + 1) ^ 2 * (p ^ m * (1 - p))) := fun m ↦ by
    rw [← ENNReal.ofReal_mul (sq_nonneg _), Nat.cast_succ]
  rw [tsum_congr this, ← ENNReal.ofReal_tsum_of_nonneg hnn
    (summable_succ_sq_mul_geometric hp0 hp1)]
  exact ENNReal.ofReal_lt_top

/-- **Mean spell length** `E[L] = 1/(1 − p)` (post #3's two-state chain: `p = 7/8`, mean `8`). -/
theorem integral_geomQuantile_id (hp0 : 0 ≤ p) (hp1 : p < 1) :
    ∫ u, (geomQuantile p u : ℝ) ∂uniformIco = 1 / (1 - p) := by
  have hpn : ‖p‖ < 1 := by rwa [Real.norm_of_nonneg hp0]
  have hs := summable_succ_mul_geometric hp0 hp1
  have h := integral_geomQuantile (g := fun k ↦ (k : ℝ)) (fun k ↦ Nat.cast_nonneg k) hp0 hp1
    (by
      refine hs.congr fun m ↦ ?_
      rw [Nat.cast_succ])
  rw [h]
  have h1 : Summable fun m : ℕ ↦ (m : ℝ) * p ^ m :=
    (summable_pow_mul_geometric_of_norm_lt_one 1 hpn).congr fun m ↦ by rw [pow_one]
  have h0 := summable_geometric_of_lt_one hp0 hp1
  have hsplit : ∀ m : ℕ, ((m + 1 : ℕ) : ℝ) * (p ^ m * (1 - p)) =
      ((m : ℝ) * p ^ m + p ^ m) * (1 - p) := fun m ↦ by
    rw [Nat.cast_succ]
    ring
  rw [tsum_congr hsplit, tsum_mul_right, h1.tsum_add h0, tsum_coe_mul_geometric_of_norm_lt_one hpn,
    tsum_geometric_of_lt_one hp0 hp1]
  have hp' : (1 - p) ≠ 0 := by linarith
  field_simp
  ring

/-- `E[L²] = (1 + p)/(1 − p)²`. -/
theorem integral_geomQuantile_sq (hp0 : 0 ≤ p) (hp1 : p < 1) :
    ∫ u, (geomQuantile p u : ℝ) ^ 2 ∂uniformIco = (1 + p) / (1 - p) ^ 2 := by
  have hpn : ‖p‖ < 1 := by rwa [Real.norm_of_nonneg hp0]
  have h := integral_geomQuantile (g := fun k ↦ (k : ℝ) ^ 2) (fun k ↦ sq_nonneg _) hp0 hp1
    ((summable_succ_sq_mul_geometric hp0 hp1).congr fun m ↦ by rw [Nat.cast_succ])
  rw [h]
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hpn
  have h1 : Summable fun m : ℕ ↦ (m : ℝ) * p ^ m :=
    (summable_pow_mul_geometric_of_norm_lt_one 1 hpn).congr fun m ↦ by rw [pow_one]
  have h0 := summable_geometric_of_lt_one hp0 hp1
  have hsplit : ∀ m : ℕ, (((m + 1 : ℕ) : ℝ)) ^ 2 * (p ^ m * (1 - p)) =
      ((m : ℝ) ^ 2 * p ^ m + 2 * ((m : ℝ) * p ^ m) + p ^ m) * (1 - p) := fun m ↦ by
    rw [Nat.cast_succ]
    ring
  rw [tsum_congr hsplit, tsum_mul_right, (h2.add (h1.mul_left 2)).tsum_add h0,
    h2.tsum_add (h1.mul_left 2), tsum_mul_left, tsum_sq_mul_geometric_of_norm_lt_one hpn,
    tsum_coe_mul_geometric_of_norm_lt_one hpn, tsum_geometric_of_lt_one hp0 hp1]
  have hp' : (1 - p) ≠ 0 := by linarith
  field_simp
  ring

/-- **Variance of the spell length**: `Var(L) = p/(1 − p)²`. -/
theorem variance_geomQuantile (hp0 : 0 ≤ p) (hp1 : p < 1) :
    Var[fun u ↦ (geomQuantile p u : ℝ); uniformIco] = p / (1 - p) ^ 2 := by
  have := isProbabilityMeasure_uniformIco
  rw [variance_eq_sub (memLp_geomQuantile hp0 hp1)]
  have hsq : ∫ u, ((fun u ↦ (geomQuantile p u : ℝ)) ^ 2) u ∂uniformIco =
      ∫ u, (geomQuantile p u : ℝ) ^ 2 ∂uniformIco := rfl
  rw [hsq, integral_geomQuantile_sq hp0 hp1, integral_geomQuantile_id hp0 hp1]
  have hp' : (1 - p) ≠ 0 := by linarith
  field_simp
  ring

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Stratified inverse-CDF sampling never does worse than i.i.d. sampling** (generic form,
post #3's "one draw in each of `K` equal intervals"): for `V₀, …, V_{K−1}` i.i.d. `U[0,1)` and
any `f ∈ L²(U[0,1))` (e.g. an inverse CDF), the stratified mean `(1/K) Σ_k f((k + V_k)/K)` has
variance at most `Var(f(U))/K`, the variance of the mean of `K` i.i.d. draws. -/
theorem variance_stratified_le_div {K : ℕ} (hK : K ≠ 0) {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Fin K → Ω → ℝ} (hV : ∀ k, HasLaw (V k) uniformIco P) (hind : iIndepFun V P)
    {f : ℝ → ℝ} (hf : MemLp f 2 uniformIco) :
    Var[fun ω ↦ sampleMean K f (fun k ↦ stratumMap K k (V k ω)); P] ≤ Var[f; uniformIco] / K :=
  variance_sampleMean_le_of_sum_map_eq hK
    (fun k ↦ (measurable_stratumMap K k).comp_aemeasurable (hV k).aemeasurable)
    (hind.comp (fun k ↦ stratumMap K k) (fun k ↦ measurable_stratumMap K k))
    (sum_map_stratified hK hV) hf

/-- **Stratified spell lengths are unbiased for the mean spell length** (post #3, approach
(vii)): with `K` draws `L_k = geomQuantile p ((k + V_k)/K)`, one in each of `K` equal intervals,
`E[(1/K) Σ_k L_k] = 1/(1 − p)`. -/
theorem integral_stratifiedSpell {K : ℕ} (hK : K ≠ 0) (hp0 : 0 ≤ p) (hp1 : p < 1)
    {P : Measure Ω} {V : Fin K → Ω → ℝ} (hV : ∀ k, HasLaw (V k) uniformIco P) :
    ∫ ω, sampleMean K (fun u ↦ (geomQuantile p u : ℝ)) (fun k ↦ stratumMap K k (V k ω)) ∂P =
      1 / (1 - p) := by
  have := isProbabilityMeasure_uniformIco
  rw [integral_sampleMean_stratified hK hV ((memLp_geomQuantile hp0 hp1).integrable one_le_two),
    integral_geomQuantile_id hp0 hp1]

/-- **Stratified spell lengths: variance at most that of `K` i.i.d. draws** (post #3, approach
(vii)): `Var((1/K) Σ_k L_k) ≤ Var((1/K) Σ_k L'_k)` where the `L'_k = geomQuantile p W_k` are
i.i.d. with the MC spell-length law (`uniformIco_geomQuantile_eq_firstSpell`). -/
theorem variance_stratifiedSpell_le_iid {K : ℕ} (hK : K ≠ 0) (hp0 : 0 ≤ p) (hp1 : p < 1)
    {P : Measure Ω} [IsProbabilityMeasure P] {V W : Fin K → Ω → ℝ}
    (hV : ∀ k, HasLaw (V k) uniformIco P) (hind : iIndepFun V P)
    (hW : ∀ k, HasLaw (W k) uniformIco P) (hindW : iIndepFun W P) :
    Var[fun ω ↦ sampleMean K (fun u ↦ (geomQuantile p u : ℝ))
        (fun k ↦ stratumMap K k (V k ω)); P] ≤
      Var[fun ω ↦ sampleMean K (fun u ↦ (geomQuantile p u : ℝ)) (fun k ↦ W k ω); P] := by
  rw [variance_sampleMean_iid hW hindW (memLp_geomQuantile hp0 hp1)]
  exact variance_stratified_le_div hK hV hind (memLp_geomQuantile hp0 hp1)

/-- **Stratified spell lengths, explicit bound**: `Var((1/K) Σ_k L_k) ≤ p / ((1 − p)² K)`, the
i.i.d. variance `Var(L)/K` with `Var(L) = p/(1 − p)²`. -/
theorem variance_stratifiedSpell_le {K : ℕ} (hK : K ≠ 0) (hp0 : 0 ≤ p) (hp1 : p < 1)
    {P : Measure Ω} [IsProbabilityMeasure P] {V : Fin K → Ω → ℝ}
    (hV : ∀ k, HasLaw (V k) uniformIco P) (hind : iIndepFun V P) :
    Var[fun ω ↦ sampleMean K (fun u ↦ (geomQuantile p u : ℝ))
        (fun k ↦ stratumMap K k (V k ω)); P] ≤ p / ((1 - p) ^ 2 * K) := by
  have h := variance_stratified_le_div hK hV hind (memLp_geomQuantile hp0 hp1)
  rwa [variance_geomQuantile hp0 hp1, div_div] at h

end RQMCMarkov.MarkovDriving

set_option linter.style.longLine false
#print axioms RQMCMarkov.MarkovDriving.InUnitCube
#print axioms RQMCMarkov.MarkovDriving.boxInd
#print axioms RQMCMarkov.MarkovDriving.empAvg
#print axioms RQMCMarkov.MarkovDriving.IsUD
#print axioms RQMCMarkov.MarkovDriving.window
#print axioms RQMCMarkov.MarkovDriving.IsCUD
#print axioms RQMCMarkov.MarkovDriving.IsSide
#print axioms RQMCMarkov.MarkovDriving.isSide_Ico
#print axioms RQMCMarkov.MarkovDriving.boxVolume_eq_volume
#print axioms RQMCMarkov.MarkovDriving.boxInd_eq_ite
#print axioms RQMCMarkov.MarkovDriving.boxInd_nonneg
#print axioms RQMCMarkov.MarkovDriving.boxInd_le_one
#print axioms RQMCMarkov.MarkovDriving.boxInd_eq_one_iff
#print axioms RQMCMarkov.MarkovDriving.boxInd_le_boxInd
#print axioms RQMCMarkov.MarkovDriving.empAvg_le_empAvg
#print axioms RQMCMarkov.MarkovDriving.tendsto_empAvg_boxInd_of_isSide
#print axioms RQMCMarkov.MarkovDriving.IsStepFn
#print axioms RQMCMarkov.MarkovDriving.tendsto_empAvg_of_isStepFn
#print axioms RQMCMarkov.MarkovDriving.IsStepFn.congr
#print axioms RQMCMarkov.MarkovDriving.IsStepFn.of_eq
#print axioms RQMCMarkov.MarkovDriving.isStepFn_boxInd
#print axioms RQMCMarkov.MarkovDriving.isStepFn_const
#print axioms RQMCMarkov.MarkovDriving.IsStepFn.add
#print axioms RQMCMarkov.MarkovDriving.IsStepFn.const_mul
#print axioms RQMCMarkov.MarkovDriving.IsStepFn.sub
#print axioms RQMCMarkov.MarkovDriving.isStepFn_finset_sum
#print axioms RQMCMarkov.MarkovDriving.boxInd_append
#print axioms RQMCMarkov.MarkovDriving.IsStepFn.append
#print axioms RQMCMarkov.MarkovDriving.IsCUD.mem_Ico
#print axioms RQMCMarkov.MarkovDriving.IsCUD.isUD_window
#print axioms RQMCMarkov.MarkovDriving.window_mem
#print axioms RQMCMarkov.MarkovDriving.not_isUD_of_finite_range
#print axioms RQMCMarkov.MarkovDriving.not_isCUD_of_finite_range
#print axioms RQMCMarkov.MarkovDriving.not_isCUD_of_periodic
#print axioms RQMCMarkov.MarkovDriving.uniformIco
#print axioms RQMCMarkov.MarkovDriving.isProbabilityMeasure_uniformIco
#print axioms RQMCMarkov.MarkovDriving.uniformCube
#print axioms RQMCMarkov.MarkovDriving.isProbabilityMeasure_uniformCube
#print axioms RQMCMarkov.MarkovDriving.sampleMean
#print axioms RQMCMarkov.MarkovDriving.map_le_of_sum_map_eq
#print axioms RQMCMarkov.MarkovDriving.integrable_map_of_sum_map_eq
#print axioms RQMCMarkov.MarkovDriving.memLp_map_of_sum_map_eq
#print axioms RQMCMarkov.MarkovDriving.integral_sampleMean_of_sum_map_eq
#print axioms RQMCMarkov.MarkovDriving.variance_sampleMean_of_sum_map_eq
#print axioms RQMCMarkov.MarkovDriving.variance_sampleMean_le_of_sum_map_eq
#print axioms RQMCMarkov.MarkovDriving.sum_map_eq_of_hasLaw
#print axioms RQMCMarkov.MarkovDriving.integral_sampleMean_iid
#print axioms RQMCMarkov.MarkovDriving.variance_sampleMean_iid
#print axioms RQMCMarkov.MarkovDriving.rmse_sampleMean_iid
#print axioms RQMCMarkov.MarkovDriving.tendstoInDistribution_sampleMean_iid
#print axioms RQMCMarkov.MarkovDriving.measure_all_draws_lt_tenth
#print axioms RQMCMarkov.MarkovDriving.measure_all_draws_lt_tenth_pos
#print axioms RQMCMarkov.MarkovDriving.measure_sampleMean_far_pos
#print axioms RQMCMarkov.MarkovDriving.integral_sampleMean_of_hasLaw_uniformCube
#print axioms RQMCMarkov.MarkovDriving.uniformIco_eq_restrict_Ioc
#print axioms RQMCMarkov.MarkovDriving.map_fract_restrict_Ioc
#print axioms RQMCMarkov.MarkovDriving.measurePreserving_fract_add
#print axioms RQMCMarkov.MarkovDriving.shiftMod1
#print axioms RQMCMarkov.MarkovDriving.shiftMod1_mem_cube
#print axioms RQMCMarkov.MarkovDriving.measurePreserving_shiftMod1
#print axioms RQMCMarkov.MarkovDriving.hasLaw_shiftMod1
#print axioms RQMCMarkov.MarkovDriving.integral_sampleMean_shiftMod1
#print axioms RQMCMarkov.MarkovDriving.stratum
#print axioms RQMCMarkov.MarkovDriving.measurableSet_stratum
#print axioms RQMCMarkov.MarkovDriving.stratumMap
#print axioms RQMCMarkov.MarkovDriving.measurable_stratumMap
#print axioms RQMCMarkov.MarkovDriving.stratumMap_preimage_stratum
#print axioms RQMCMarkov.MarkovDriving.map_stratumMap_uniformIco
#print axioms RQMCMarkov.MarkovDriving.iUnion_stratum
#print axioms RQMCMarkov.MarkovDriving.pairwise_disjoint_stratum
#print axioms RQMCMarkov.MarkovDriving.sum_map_stratumMap
#print axioms RQMCMarkov.MarkovDriving.sum_map_stratified
#print axioms RQMCMarkov.MarkovDriving.integral_sampleMean_stratified
#print axioms RQMCMarkov.MarkovDriving.not_hasLaw_stratumMap
#print axioms RQMCMarkov.MarkovDriving.sum_map_eq_of_integral_sampleMean_indicator
#print axioms RQMCMarkov.MarkovDriving.sampleMean_const_points
#print axioms RQMCMarkov.MarkovDriving.integral_sampleMean_of_hasLaw_const
#print axioms RQMCMarkov.MarkovDriving.variance_sampleMean_const
#print axioms RQMCMarkov.MarkovDriving.IsStochastic
#print axioms RQMCMarkov.MarkovDriving.IsStochastic.mk
#print axioms RQMCMarkov.MarkovDriving.IsStochastic.nonneg
#print axioms RQMCMarkov.MarkovDriving.IsStochastic.sum_eq_one
#print axioms RQMCMarkov.MarkovDriving.cumProb
#print axioms RQMCMarkov.MarkovDriving.lastState
#print axioms RQMCMarkov.MarkovDriving.step
#print axioms RQMCMarkov.MarkovDriving.cumProb_zero
#print axioms RQMCMarkov.MarkovDriving.cumProb_succ
#print axioms RQMCMarkov.MarkovDriving.cumProb_of_le
#print axioms RQMCMarkov.MarkovDriving.cumProb_mono
#print axioms RQMCMarkov.MarkovDriving.cumProb_mem_Icc
#print axioms RQMCMarkov.MarkovDriving.step_eq_iff
#print axioms RQMCMarkov.MarkovDriving.step_mono
#print axioms RQMCMarkov.MarkovDriving.step_zero
#print axioms RQMCMarkov.MarkovDriving.measurable_step
#print axioms RQMCMarkov.MarkovDriving.step_preimage_inter_Ioc
#print axioms RQMCMarkov.MarkovDriving.uniformIco_step_eq
#print axioms RQMCMarkov.MarkovDriving.volume_step_eq
#print axioms RQMCMarkov.MarkovDriving.step_post3_example
#print axioms RQMCMarkov.MarkovDriving.drive
#print axioms RQMCMarkov.MarkovDriving.drivenPath
#print axioms RQMCMarkov.MarkovDriving.drive_zero
#print axioms RQMCMarkov.MarkovDriving.drive_succ
#print axioms RQMCMarkov.MarkovDriving.drive_eq_iff
#print axioms RQMCMarkov.MarkovDriving.occCount
#print axioms RQMCMarkov.MarkovDriving.transCount
#print axioms RQMCMarkov.MarkovDriving.occCount_zero
#print axioms RQMCMarkov.MarkovDriving.transCount_zero
#print axioms RQMCMarkov.MarkovDriving.occCount_succ
#print axioms RQMCMarkov.MarkovDriving.transCount_succ
#print axioms RQMCMarkov.MarkovDriving.occCount_le
#print axioms RQMCMarkov.MarkovDriving.occCount_mono
#print axioms RQMCMarkov.MarkovDriving.transCount_le_occCount
#print axioms RQMCMarkov.MarkovDriving.occCount_congr
#print axioms RQMCMarkov.MarkovDriving.transCount_congr
#print axioms RQMCMarkov.MarkovDriving.occCount_add
#print axioms RQMCMarkov.MarkovDriving.transCount_add
#print axioms RQMCMarkov.MarkovDriving.departureIndex
#print axioms RQMCMarkov.MarkovDriving.departureIndex_congr
#print axioms RQMCMarkov.MarkovDriving.departureIndex_lt
#print axioms RQMCMarkov.MarkovDriving.departureIndex_injective
#print axioms RQMCMarkov.MarkovDriving.stackState
#print axioms RQMCMarkov.MarkovDriving.stackDrive
#print axioms RQMCMarkov.MarkovDriving.stackPath
#print axioms RQMCMarkov.MarkovDriving.stackState_snd
#print axioms RQMCMarkov.MarkovDriving.stackDrive_zero
#print axioms RQMCMarkov.MarkovDriving.stackDrive_succ
#print axioms RQMCMarkov.MarkovDriving.stackDrive_eq_iff
#print axioms RQMCMarkov.MarkovDriving.IsSpellStart
#print axioms RQMCMarkov.MarkovDriving.runLength
#print axioms RQMCMarkov.MarkovDriving.spellCount
#print axioms RQMCMarkov.MarkovDriving.runLength_eq_of_exit
#print axioms RQMCMarkov.MarkovDriving.runLength_eq_iff
#print axioms RQMCMarkov.MarkovDriving.spellCount_succ
#print axioms RQMCMarkov.MarkovDriving.sum_occCount
#print axioms RQMCMarkov.MarkovDriving.sum_transCount_right
#print axioms RQMCMarkov.MarkovDriving.sum_transCount_left
#print axioms RQMCMarkov.MarkovDriving.flowBalance
#print axioms RQMCMarkov.MarkovDriving.abs_flowBalance_le
#print axioms RQMCMarkov.MarkovDriving.sum_sum_transCount
#print axioms RQMCMarkov.MarkovDriving.spellCount_succ_eq
#print axioms RQMCMarkov.MarkovDriving.iidUniform
#print axioms RQMCMarkov.MarkovDriving.isProbabilityMeasure_iidUniform
#print axioms RQMCMarkov.MarkovDriving.infinitePi_setOf_forall_mem
#print axioms RQMCMarkov.MarkovDriving.measurableSet_setOf_forall_mem
#print axioms RQMCMarkov.MarkovDriving.setOf_drive_eq
#print axioms RQMCMarkov.MarkovDriving.measurableSet_drive_cylinder
#print axioms RQMCMarkov.MarkovDriving.infinitePi_drive_cylinder
#print axioms RQMCMarkov.MarkovDriving.setOf_stackDrive_eq
#print axioms RQMCMarkov.MarkovDriving.measurableSet_stackDrive_cylinder
#print axioms RQMCMarkov.MarkovDriving.infinitePi_stackDrive_cylinder
#print axioms RQMCMarkov.MarkovDriving.pathProb
#print axioms RQMCMarkov.MarkovDriving.pathProb_nonneg
#print axioms RQMCMarkov.MarkovDriving.pathProb_succ
#print axioms RQMCMarkov.MarkovDriving.measurableSet_step_eq
#print axioms RQMCMarkov.MarkovDriving.prod_uniformIco_step_eq
#print axioms RQMCMarkov.MarkovDriving.iidUniform_drivenPath_cylinder
#print axioms RQMCMarkov.MarkovDriving.iidUniform_stackPath_cylinder
#print axioms RQMCMarkov.MarkovDriving.extendPath
#print axioms RQMCMarkov.MarkovDriving.extendPath_eq_iff
#print axioms RQMCMarkov.MarkovDriving.measurable_drivenPath_restrict
#print axioms RQMCMarkov.MarkovDriving.measurable_stackPath_restrict
#print axioms RQMCMarkov.MarkovDriving.map_drivenPath_singleton
#print axioms RQMCMarkov.MarkovDriving.map_stackPath_singleton
#print axioms RQMCMarkov.MarkovDriving.map_drivenPath_eq_map_stackPath
#print axioms RQMCMarkov.MarkovDriving.isUD_fin_zero
#print axioms RQMCMarkov.MarkovDriving.sum_range_mul_eq_sum_interleaved
#print axioms RQMCMarkov.MarkovDriving.tendsto_avg_of_interleaved
#print axioms RQMCMarkov.MarkovDriving.abs_prod_sub_prod_le
#print axioms RQMCMarkov.MarkovDriving.abs_div_sub_le
#print axioms RQMCMarkov.MarkovDriving.isUD_of_grid
#print axioms RQMCMarkov.MarkovDriving.measurable_boxInd
#print axioms RQMCMarkov.MarkovDriving.identDistrib_window_boxInd
#print axioms RQMCMarkov.MarkovDriving.indepFun_window_boxInd
#print axioms RQMCMarkov.MarkovDriving.integral_boxInd_iidUniform
#print axioms RQMCMarkov.MarkovDriving.ae_tendsto_empAvg_box
#print axioms RQMCMarkov.MarkovDriving.ae_isCUD_iidUniform
#print axioms RQMCMarkov.MarkovDriving.exists_isCUD
#print axioms RQMCMarkov.MarkovDriving.windowMap
#print axioms RQMCMarkov.MarkovDriving.windowMap_succ
#print axioms RQMCMarkov.MarkovDriving.windowMap_add
#print axioms RQMCMarkov.MarkovDriving.drive_add_eq_windowMap
#print axioms RQMCMarkov.MarkovDriving.multiStep
#print axioms RQMCMarkov.MarkovDriving.multiStep_eq_pow
#print axioms RQMCMarkov.MarkovDriving.sum_mul_multiStep
#print axioms RQMCMarkov.MarkovDriving.val_step_zero
#print axioms RQMCMarkov.MarkovDriving.isSide_step
#print axioms RQMCMarkov.MarkovDriving.isStepFn_step
#print axioms RQMCMarkov.MarkovDriving.isStepFn_windowMap
#print axioms RQMCMarkov.MarkovDriving.HasCouplingBox
#print axioms RQMCMarkov.MarkovDriving.noCouple
#print axioms RQMCMarkov.MarkovDriving.isStepFn_noCouple
#print axioms RQMCMarkov.MarkovDriving.noCouple_eq_zero_or_one
#print axioms RQMCMarkov.MarkovDriving.windowMap_eq_of_noCouple_eq_zero
#print axioms RQMCMarkov.MarkovDriving.abs_ind_sub_le_noCouple
#print axioms RQMCMarkov.MarkovDriving.abs_multiStep_sub_le
#print axioms RQMCMarkov.MarkovDriving.occCount_eq_sum
#print axioms RQMCMarkov.MarkovDriving.abs_sum_shift_sub_le
#print axioms RQMCMarkov.MarkovDriving.tendsto_occFreq_of_isCUD
#print axioms RQMCMarkov.MarkovDriving.tendsto_timeAvg_of_isCUD
#print axioms RQMCMarkov.MarkovDriving.hasCouplingBox_of_common_interval
#print axioms RQMCMarkov.MarkovDriving.hasCouplingBox_of_col_pos
#print axioms RQMCMarkov.MarkovDriving.hasCouplingBox_of_pos
#print axioms RQMCMarkov.MarkovDriving.tendsto_occFreq_of_isCUD_of_col_pos
#print axioms RQMCMarkov.MarkovDriving.identityTwo
#print axioms RQMCMarkov.MarkovDriving.isStochastic_identityTwo
#print axioms RQMCMarkov.MarkovDriving.identityTwo_stationary
#print axioms RQMCMarkov.MarkovDriving.step_identityTwo_zero
#print axioms RQMCMarkov.MarkovDriving.drivenPath_identityTwo
#print axioms RQMCMarkov.MarkovDriving.not_tendsto_occFreq_identity
#print axioms RQMCMarkov.MarkovDriving.fourState
#print axioms RQMCMarkov.MarkovDriving.isStochastic_fourState
#print axioms RQMCMarkov.MarkovDriving.multiStep_fourState_two
#print axioms RQMCMarkov.MarkovDriving.fourState_stationary
#print axioms RQMCMarkov.MarkovDriving.step_fourState_parity
#print axioms RQMCMarkov.MarkovDriving.windowMap_fourState_parity_ne
#print axioms RQMCMarkov.MarkovDriving.not_hasCouplingBox_fourState
#print axioms RQMCMarkov.MarkovDriving.InUnitIco
#print axioms RQMCMarkov.MarkovDriving.countBelow
#print axioms RQMCMarkov.MarkovDriving.countAtMost
#print axioms RQMCMarkov.MarkovDriving.localDiscrepancy
#print axioms RQMCMarkov.MarkovDriving.starDiscrepancy
#print axioms RQMCMarkov.MarkovDriving.qmcEstimate
#print axioms RQMCMarkov.MarkovDriving.midpointRule
#print axioms RQMCMarkov.MarkovDriving.countBelow_le
#print axioms RQMCMarkov.MarkovDriving.countBelow_mono
#print axioms RQMCMarkov.MarkovDriving.countBelow_div_mem_Icc
#print axioms RQMCMarkov.MarkovDriving.localDiscrepancy_le_one
#print axioms RQMCMarkov.MarkovDriving.localDiscrepancy_eq_abs_div
#print axioms RQMCMarkov.MarkovDriving.bddAbove_localDiscrepancy
#print axioms RQMCMarkov.MarkovDriving.localDiscrepancy_le_starDiscrepancy
#print axioms RQMCMarkov.MarkovDriving.starDiscrepancy_le_of_forall
#print axioms RQMCMarkov.MarkovDriving.starDiscrepancy_nonneg
#print axioms RQMCMarkov.MarkovDriving.starDiscrepancy_le_one
#print axioms RQMCMarkov.MarkovDriving.countAtMost_div_sub_le_starDiscrepancy
#print axioms RQMCMarkov.MarkovDriving.inv_two_mul_le_starDiscrepancy
#print axioms RQMCMarkov.MarkovDriving.midpointRule_mem
#print axioms RQMCMarkov.MarkovDriving.midpointRule_lt_iff
#print axioms RQMCMarkov.MarkovDriving.countBelow_midpointRule_le
#print axioms RQMCMarkov.MarkovDriving.le_countBelow_midpointRule
#print axioms RQMCMarkov.MarkovDriving.abs_countBelow_midpointRule_sub_le
#print axioms RQMCMarkov.MarkovDriving.starDiscrepancy_midpointRule
#print axioms RQMCMarkov.MarkovDriving.starDiscrepancy_midpointRule_le
#print axioms RQMCMarkov.MarkovDriving.midpointRule_three
#print axioms RQMCMarkov.MarkovDriving.starDiscrepancy_midpointRule_three
#print axioms RQMCMarkov.MarkovDriving.totalVariation
#print axioms RQMCMarkov.MarkovDriving.countBelow_eq_sum_indicator
#print axioms RQMCMarkov.MarkovDriving.countAtMost_eq_sum_indicator
#print axioms RQMCMarkov.MarkovDriving.countAtMost_le
#print axioms RQMCMarkov.MarkovDriving.countAtMost_div_sub_le_starDiscrepancy_of_mem
#print axioms RQMCMarkov.MarkovDriving.indicator_one_mem_Icc
#print axioms RQMCMarkov.MarkovDriving.abs_sum_indicator_upperSet_sub_le
#print axioms RQMCMarkov.MarkovDriving.antitone_indicator_Iic
#print axioms RQMCMarkov.MarkovDriving.integral_indicator_Iic_one
#print axioms RQMCMarkov.MarkovDriving.sum_div_eq_integral_indicator
#print axioms RQMCMarkov.MarkovDriving.integral_sub_eq_integral_measureReal
#print axioms RQMCMarkov.MarkovDriving.koksma_monotone
#print axioms RQMCMarkov.MarkovDriving.monotone_comp_projIcc
#print axioms RQMCMarkov.MarkovDriving.comp_projIcc_eq
#print axioms RQMCMarkov.MarkovDriving.qmcError_congr
#print axioms RQMCMarkov.MarkovDriving.koksma_monotoneOn
#print axioms RQMCMarkov.MarkovDriving.koksma_sub_monotoneOn
#print axioms RQMCMarkov.MarkovDriving.koksma_boundedVariationOn
#print axioms RQMCMarkov.MarkovDriving.koksma_hasDerivAt
#print axioms RQMCMarkov.MarkovDriving.eVariationOn_le_integral_abs_deriv
#print axioms RQMCMarkov.MarkovDriving.boundedVariationOn_of_hasDerivAt
#print axioms RQMCMarkov.MarkovDriving.totalVariation_le_integral_abs_deriv
#print axioms RQMCMarkov.MarkovDriving.vanDerCorput
#print axioms RQMCMarkov.MarkovDriving.vanDerCorput_eq
#print axioms RQMCMarkov.MarkovDriving.vanDerCorput_two_mul_add
#print axioms RQMCMarkov.MarkovDriving.vanDerCorput_one_two_three
#print axioms RQMCMarkov.MarkovDriving.vanDerCorput_mem_Ico
#print axioms RQMCMarkov.MarkovDriving.vanDerCorput_inUnitIco
#print axioms RQMCMarkov.MarkovDriving.floor_two_pow_mul_vanDerCorput_lt
#print axioms RQMCMarkov.MarkovDriving.floor_two_pow_succ_mul_vanDerCorput
#print axioms RQMCMarkov.MarkovDriving.mod_eq_of_floor_vanDerCorput_eq
#print axioms RQMCMarkov.MarkovDriving.floor_vanDerCorput_injOn
#print axioms RQMCMarkov.MarkovDriving.mem_dyadic_iff_floor
#print axioms RQMCMarkov.MarkovDriving.card_vanDerCorput_mem_dyadic
#print axioms RQMCMarkov.MarkovDriving.card_vanDerCorput_mem_dyadic_aligned
#print axioms RQMCMarkov.MarkovDriving.abs_card_block_vanDerCorput_sub_le
#print axioms RQMCMarkov.MarkovDriving.countBelow_add
#print axioms RQMCMarkov.MarkovDriving.abs_countBelow_vanDerCorput_sub_le
#print axioms RQMCMarkov.MarkovDriving.starDiscrepancy_vanDerCorput_le
#print axioms RQMCMarkov.MarkovDriving.natLog_two_add_one_le
#print axioms RQMCMarkov.MarkovDriving.starDiscrepancy_vanDerCorput_le_log
#print axioms RQMCMarkov.MarkovDriving.abs_qmcError_vanDerCorput_le
#print axioms RQMCMarkov.MarkovDriving.tendsto_log_add_one_div_sqrt
#print axioms RQMCMarkov.MarkovDriving.tendsto_sqrt_mul_vanDerCorput_bound
#print axioms RQMCMarkov.MarkovDriving.tendsto_sqrt_mul_qmcError_vanDerCorput
#print axioms RQMCMarkov.MarkovDriving.empAvg_window_one_eq
#print axioms RQMCMarkov.MarkovDriving.isUD_of_tendsto_starDiscrepancy
#print axioms RQMCMarkov.MarkovDriving.isUD_vanDerCorput
#print axioms RQMCMarkov.MarkovDriving.vanDerCorput_two_mul_add_one
#print axioms RQMCMarkov.MarkovDriving.vanDerCorput_lt_half_iff
#print axioms RQMCMarkov.MarkovDriving.vanDerCorput_succ_lt_half_iff
#print axioms RQMCMarkov.MarkovDriving.not_isUD_window_two_vanDerCorput
#print axioms RQMCMarkov.MarkovDriving.not_isCUD_vanDerCorput
#print axioms RQMCMarkov.MarkovDriving.vanDerCorput_pos
#print axioms RQMCMarkov.MarkovDriving.twoState
#print axioms RQMCMarkov.MarkovDriving.isStochastic_twoState
#print axioms RQMCMarkov.MarkovDriving.twoState_stationary
#print axioms RQMCMarkov.MarkovDriving.step_twoState_one
#print axioms RQMCMarkov.MarkovDriving.step_twoState_zero_low
#print axioms RQMCMarkov.MarkovDriving.step_twoState_zero_high
#print axioms RQMCMarkov.MarkovDriving.drivenPath_twoState_vanDerCorput
#print axioms RQMCMarkov.MarkovDriving.sum_range_even_indicator
#print axioms RQMCMarkov.MarkovDriving.tendsto_occFreq_twoState_vanDerCorput
#print axioms RQMCMarkov.MarkovDriving.not_tendsto_occFreq_twoState_vanDerCorput
#print axioms RQMCMarkov.MarkovDriving.tendsto_occFreq_twoState_of_isCUD
#print axioms RQMCMarkov.MarkovDriving.klSum
#print axioms RQMCMarkov.MarkovDriving.sub_le_mul_log_div
#print axioms RQMCMarkov.MarkovDriving.sub_lt_mul_log_div
#print axioms RQMCMarkov.MarkovDriving.sum_sub_sum_le_klSum
#print axioms RQMCMarkov.MarkovDriving.eq_of_klSum_le
#print axioms RQMCMarkov.MarkovDriving.logSum_le
#print axioms RQMCMarkov.MarkovDriving.pushSum
#print axioms RQMCMarkov.MarkovDriving.klSum_pushSum_le
#print axioms RQMCMarkov.MarkovDriving.sum_fin_succ_fun
#print axioms RQMCMarkov.MarkovDriving.sum_fin_zero_fun
#print axioms RQMCMarkov.MarkovDriving.chentsov_entropy_core
#print axioms RQMCMarkov.MarkovDriving.chentsov_entropy_stationary
#print axioms RQMCMarkov.MarkovDriving.IsSide.inter
#print axioms RQMCMarkov.MarkovDriving.boxInd_inter
#print axioms RQMCMarkov.MarkovDriving.IsStepFn.mul
#print axioms RQMCMarkov.MarkovDriving.isStepFn_finset_prod
#print axioms RQMCMarkov.MarkovDriving.IsStepFn.unique
#print axioms RQMCMarkov.MarkovDriving.cellInd
#print axioms RQMCMarkov.MarkovDriving.cellInd_eq_prod
#print axioms RQMCMarkov.MarkovDriving.exists_isStepFn_cellInd
#print axioms RQMCMarkov.MarkovDriving.cellProb
#print axioms RQMCMarkov.MarkovDriving.isStepFn_cellInd
#print axioms RQMCMarkov.MarkovDriving.isStepFn_pattern
#print axioms RQMCMarkov.MarkovDriving.sum_cellProb_eq
#print axioms RQMCMarkov.MarkovDriving.sum_prod_ite_eq_one
#print axioms RQMCMarkov.MarkovDriving.exists_tendsto_ultrafilter
#print axioms RQMCMarkov.MarkovDriving.div_mem_Icc_of_sum
#print axioms RQMCMarkov.MarkovDriving.tendsto_occFreq_of_isCUD_general
#print axioms RQMCMarkov.MarkovDriving.tendsto_timeAvg_of_isCUD_general
#print axioms RQMCMarkov.MarkovDriving.tendsto_occFreq_fourState_of_isCUD
#print axioms RQMCMarkov.MarkovDriving.IsStationaryDistribution
#print axioms RQMCMarkov.MarkovDriving.IsStationaryDistribution.mk
#print axioms RQMCMarkov.MarkovDriving.IsStationaryDistribution.vecMul_eq
#print axioms RQMCMarkov.MarkovDriving.IsStationaryDistribution.nonneg
#print axioms RQMCMarkov.MarkovDriving.IsStationaryDistribution.sum_eq_one
#print axioms RQMCMarkov.MarkovDriving.pow_apply_nonneg_of_nonneg
#print axioms RQMCMarkov.MarkovDriving.sum_pow_apply_eq_one
#print axioms RQMCMarkov.MarkovDriving.mulVec_const_one
#print axioms RQMCMarkov.MarkovDriving.eq_of_isMax_of_mulVec_eq
#print axioms RQMCMarkov.MarkovDriving.eq_of_mulVec_eq_self_of_irreducible
#print axioms RQMCMarkov.MarkovDriving.vecMul_one_sub_eq_zero_iff
#print axioms RQMCMarkov.MarkovDriving.one_sub_mulVec
#print axioms RQMCMarkov.MarkovDriving.const_one_mem_ker
#print axioms RQMCMarkov.MarkovDriving.const_one_ne_zero
#print axioms RQMCMarkov.MarkovDriving.rank_one_sub_lt
#print axioms RQMCMarkov.MarkovDriving.exists_isStationaryDistribution
#print axioms RQMCMarkov.MarkovDriving.IsStationaryDistribution.vecMul_pow
#print axioms RQMCMarkov.MarkovDriving.IsStationaryDistribution.pos
#print axioms RQMCMarkov.MarkovDriving.dotProduct_sub_const
#print axioms RQMCMarkov.MarkovDriving.dotProduct_sub_mulVec_eq_zero
#print axioms RQMCMarkov.MarkovDriving.exists_poisson
#print axioms RQMCMarkov.MarkovDriving.poisson_const_eq
#print axioms RQMCMarkov.MarkovDriving.IsStationaryDistribution.eq_of_vecMul_eq_self
#print axioms RQMCMarkov.MarkovDriving.existsUnique_isStationaryDistribution
#print axioms RQMCMarkov.MarkovDriving.poisson_sub_eq
#print axioms RQMCMarkov.MarkovDriving.exists_poisson_normalized
#print axioms RQMCMarkov.MarkovDriving.stationary_unique_of_irreducible
#print axioms RQMCMarkov.MarkovDriving.tendsto_occFreq_of_isCUD_irreducible
#print axioms RQMCMarkov.MarkovDriving.tendsto_timeAvg_of_isCUD_irreducible
#print axioms RQMCMarkov.MarkovDriving.ae_tendsto_occFreq_iidUniform_irreducible
#print axioms RQMCMarkov.MarkovDriving.prod_prod_pow_ite_eq
#print axioms RQMCMarkov.MarkovDriving.prod_eq_prod_pow_transCount
#print axioms RQMCMarkov.MarkovDriving.pathProb_eq_prod_pow
#print axioms RQMCMarkov.MarkovDriving.pathProb_eq_of_transCount_eq
#print axioms RQMCMarkov.MarkovDriving.countClass
#print axioms RQMCMarkov.MarkovDriving.mem_countClass
#print axioms RQMCMarkov.MarkovDriving.mcLaw
#print axioms RQMCMarkov.MarkovDriving.mcLaw_singleton_of_mem
#print axioms RQMCMarkov.MarkovDriving.cond_mcLaw_countClass
#print axioms RQMCMarkov.MarkovDriving.BalancedCounts
#print axioms RQMCMarkov.MarkovDriving.balanced_transCount
#print axioms RQMCMarkov.MarkovDriving.IsCountTrail
#print axioms RQMCMarkov.MarkovDriving.isCountTrail_zero
#print axioms RQMCMarkov.MarkovDriving.IsCountTrail.le_sum
#print axioms RQMCMarkov.MarkovDriving.IsCountTrail.extend
#print axioms RQMCMarkov.MarkovDriving.exists_maximal_trail
#print axioms RQMCMarkov.MarkovDriving.IsCountTrail.end_eq
#print axioms RQMCMarkov.MarkovDriving.exists_closed_trail
#print axioms RQMCMarkov.MarkovDriving.splice
#print axioms RQMCMarkov.MarkovDriving.transCount_splice
#print axioms RQMCMarkov.MarkovDriving.exists_path_of_balanced
#print axioms RQMCMarkov.MarkovDriving.reachable_of_transCount_ne_zero
#print axioms RQMCMarkov.MarkovDriving.exists_path_iff
#print axioms RQMCMarkov.MarkovDriving.netFlow
#print axioms RQMCMarkov.MarkovDriving.IsCirculation
#print axioms RQMCMarkov.MarkovDriving.isCirculation_iff_netFlow
#print axioms RQMCMarkov.MarkovDriving.netFlow_add
#print axioms RQMCMarkov.MarkovDriving.netFlow_sub
#print axioms RQMCMarkov.MarkovDriving.netFlow_mul
#print axioms RQMCMarkov.MarkovDriving.netFlow_single
#print axioms RQMCMarkov.MarkovDriving.sum_netFlow_eq_cut
#print axioms RQMCMarkov.MarkovDriving.intLattice
#print axioms RQMCMarkov.MarkovDriving.mem_intLattice
#print axioms RQMCMarkov.MarkovDriving.intCast_mem_intLattice
#print axioms RQMCMarkov.MarkovDriving.fracAdj
#print axioms RQMCMarkov.MarkovDriving.exists_pathFlow
#print axioms RQMCMarkov.MarkovDriving.reflTransGen_fracAdj_of_notMem
#print axioms RQMCMarkov.MarkovDriving.exists_cycle_direction
#print axioms RQMCMarkov.MarkovDriving.floor_lt_lt_ceil_of_notMem
#print axioms RQMCMarkov.MarkovDriving.exists_int_circulation_rounding
#print axioms RQMCMarkov.MarkovDriving.abs_sub_lt_one_of_floor_le_le_ceil
#print axioms RQMCMarkov.MarkovDriving.IsStationaryRow
#print axioms RQMCMarkov.MarkovDriving.expectedCounts
#print axioms RQMCMarkov.MarkovDriving.isCirculation_expectedCounts
#print axioms RQMCMarkov.MarkovDriving.sum_expectedCounts
#print axioms RQMCMarkov.MarkovDriving.exists_rounding_expectedCounts
#print axioms RQMCMarkov.MarkovDriving.flipChain
#print axioms RQMCMarkov.MarkovDriving.isStochastic_flipChain
#print axioms RQMCMarkov.MarkovDriving.isStationaryRow_flipChain
#print axioms RQMCMarkov.MarkovDriving.not_exists_rounding_flipChain_total_three
#print axioms RQMCMarkov.MarkovDriving.exists_closed_path_of_rounding
#print axioms RQMCMarkov.MarkovDriving.conditionalMC_wellDefined
#print axioms RQMCMarkov.MarkovDriving.exists_walk_of_reflTransGen
#print axioms RQMCMarkov.MarkovDriving.exists_injOn_walk
#print axioms RQMCMarkov.MarkovDriving.prefCount
#print axioms RQMCMarkov.MarkovDriving.ite_prod_eq
#print axioms RQMCMarkov.MarkovDriving.netFlow_prefCount
#print axioms RQMCMarkov.MarkovDriving.sum_prefCount
#print axioms RQMCMarkov.MarkovDriving.prefCount_ne_zero
#print axioms RQMCMarkov.MarkovDriving.exists_simple_cycle
#print axioms RQMCMarkov.MarkovDriving.fracSet
#print axioms RQMCMarkov.MarkovDriving.mem_fracSet
#print axioms RQMCMarkov.MarkovDriving.exists_push
#print axioms RQMCMarkov.MarkovDriving.exists_eq_of_unit_steps
#print axioms RQMCMarkov.MarkovDriving.exists_open_rounding
#print axioms RQMCMarkov.MarkovDriving.ite_eq_intCast_ite
#print axioms RQMCMarkov.MarkovDriving.balancedCounts_of_netFlow
#print axioms RQMCMarkov.MarkovDriving.exists_path_exact_length
#print axioms RQMCMarkov.MarkovDriving.conditionalMC_exact_wellDefined
#print axioms RQMCMarkov.MarkovDriving.flipChain_open_path_three
#print axioms RQMCMarkov.MarkovDriving.lilScale
#print axioms RQMCMarkov.MarkovDriving.one_le_loglog
#print axioms RQMCMarkov.MarkovDriving.lil_eventually_le_log
#print axioms RQMCMarkov.MarkovDriving.lil_log_add_one_sub_log_le
#print axioms RQMCMarkov.MarkovDriving.loglog_increment
#print axioms RQMCMarkov.MarkovDriving.lilPhi
#print axioms RQMCMarkov.MarkovDriving.lilPhi_increment
#print axioms RQMCMarkov.MarkovDriving.sqrt_lilPhi_increment
#print axioms RQMCMarkov.MarkovDriving.lil_tendsto_sum_div_of_summable
#print axioms RQMCMarkov.MarkovDriving.lilScale_nonneg
#print axioms RQMCMarkov.MarkovDriving.lilScale_sq
#print axioms RQMCMarkov.MarkovDriving.lilScale_mono
#print axioms RQMCMarkov.MarkovDriving.sqrt_le_lilScale
#print axioms RQMCMarkov.MarkovDriving.tendsto_lilScale
#print axioms RQMCMarkov.MarkovDriving.lilScale_pos
#print axioms RQMCMarkov.MarkovDriving.lil_eventually_floor_pow_succ_le
#print axioms RQMCMarkov.MarkovDriving.summable_exp_neg_mul_loglog_floor_pow
#print axioms RQMCMarkov.MarkovDriving.not_summable_exp_neg_mul_loglog_pow
#print axioms RQMCMarkov.MarkovDriving.tendsto_loglog_div
#print axioms RQMCMarkov.MarkovDriving.tendsto_lilScale_div
#print axioms RQMCMarkov.MarkovDriving.lilTruncLevel
#print axioms RQMCMarkov.MarkovDriving.lilWeight
#print axioms RQMCMarkov.MarkovDriving.lil_three_le_log_of_le
#print axioms RQMCMarkov.MarkovDriving.lil_one_le_of_three_le_log
#print axioms RQMCMarkov.MarkovDriving.lilWeight_pos
#print axioms RQMCMarkov.MarkovDriving.lilWeight_mono
#print axioms RQMCMarkov.MarkovDriving.tendsto_lilWeight
#print axioms RQMCMarkov.MarkovDriving.lilScale_eq_lilWeight
#print axioms RQMCMarkov.MarkovDriving.lil_sqrt_add_one_le
#print axioms RQMCMarkov.MarkovDriving.sum_inv_lilWeight_le
#print axioms RQMCMarkov.MarkovDriving.lil_integral_sq_sum_range
#print axioms RQMCMarkov.MarkovDriving.lil_sum_coe_sort_ite_lt
#print axioms RQMCMarkov.MarkovDriving.lil_kolmogorov_ineq
#print axioms RQMCMarkov.MarkovDriving.lil_kolmogorov_ineq_shift
#print axioms RQMCMarkov.MarkovDriving.lil_sum_range_sub_eq_window
#print axioms RQMCMarkov.MarkovDriving.lil_tendstoInMeasure_anscombe
#print axioms RQMCMarkov.MarkovDriving.lil_exp_le_one_add_add_sq
#print axioms RQMCMarkov.MarkovDriving.lil_integral_exp_le_of_abs_le
#print axioms RQMCMarkov.MarkovDriving.lil_abs_sum_le_of_abs_le
#print axioms RQMCMarkov.MarkovDriving.lil_exp_maximal_ineq
#print axioms RQMCMarkov.MarkovDriving.lil_integral_exp_sum_le
#print axioms RQMCMarkov.MarkovDriving.lil_iIndep_iSup_blocks
#print axioms RQMCMarkov.MarkovDriving.lil_identDistrib_shift
#print axioms RQMCMarkov.MarkovDriving.lil_identDistrib_shift_sum
#print axioms RQMCMarkov.MarkovDriving.lilTrunc
#print axioms RQMCMarkov.MarkovDriving.measurable_lilTrunc
#print axioms RQMCMarkov.MarkovDriving.abs_lilTrunc_le
#print axioms RQMCMarkov.MarkovDriving.lilTrunc_sq_le
#print axioms RQMCMarkov.MarkovDriving.abs_sub_lilTrunc
#print axioms RQMCMarkov.MarkovDriving.lilPhi_mono_nat
#print axioms RQMCMarkov.MarkovDriving.lilTruncLevel_nonneg
#print axioms RQMCMarkov.MarkovDriving.lilTruncLevel_mono
#print axioms RQMCMarkov.MarkovDriving.lil_exponent_bound
#print axioms RQMCMarkov.MarkovDriving.summable_tail_div_lilWeight
#print axioms RQMCMarkov.MarkovDriving.lil_ae_summable_of_summable_integral
#print axioms RQMCMarkov.MarkovDriving.lil_tsum_measure_ne_top_of_summable
#print axioms RQMCMarkov.MarkovDriving.lil_upper
#print axioms RQMCMarkov.MarkovDriving.lil_gaussianReal_Ioi_ge
#print axioms RQMCMarkov.MarkovDriving.lil_two_mul_sqrt_two_pi_le_exp_two
#print axioms RQMCMarkov.MarkovDriving.lil_eventually_lt_measure_clt
#print axioms RQMCMarkov.MarkovDriving.lil_iIndepFun_blockSum
#print axioms RQMCMarkov.MarkovDriving.lil_iIndepSet_preimage
#print axioms RQMCMarkov.MarkovDriving.lil_sum_range_mul_eq
#print axioms RQMCMarkov.MarkovDriving.block_lower_bound
#print axioms RQMCMarkov.MarkovDriving.exists_lil_lower_ratio
#print axioms RQMCMarkov.MarkovDriving.exists_lil_lower_level
#print axioms RQMCMarkov.MarkovDriving.le_block_level
#print axioms RQMCMarkov.MarkovDriving.lil_eventually_mul_sq_le_pow
#print axioms RQMCMarkov.MarkovDriving.lil_lower_block_estimate
#print axioms RQMCMarkov.MarkovDriving.lil_lower_normalized
#print axioms RQMCMarkov.MarkovDriving.LILBound
#print axioms RQMCMarkov.MarkovDriving.HasLIL
#print axioms RQMCMarkov.MarkovDriving.lilBound_of_nat
#print axioms RQMCMarkov.MarkovDriving.lilBound_iid
#print axioms RQMCMarkov.MarkovDriving.hasLIL_iid
#print axioms RQMCMarkov.MarkovDriving.LILBound.div
#print axioms RQMCMarkov.MarkovDriving.HasLIL.limsup_eq
#print axioms RQMCMarkov.MarkovDriving.HasLIL.liminf_eq
#print axioms RQMCMarkov.MarkovDriving.limsup_liminf_iid
#print axioms RQMCMarkov.MarkovDriving.departureDiscrepancy
#print axioms RQMCMarkov.MarkovDriving.sum_sub_eq_boundary_add
#print axioms RQMCMarkov.MarkovDriving.sum_indicator_eq_occCount
#print axioms RQMCMarkov.MarkovDriving.occCount_sub_eq_boundary_add
#print axioms RQMCMarkov.MarkovDriving.abs_occCount_sub_le
#print axioms RQMCMarkov.MarkovDriving.mulVec_indicator
#print axioms RQMCMarkov.MarkovDriving.transCount_sub_eq_departureDiscrepancy
#print axioms RQMCMarkov.MarkovDriving.abs_transCount_sub_le
#print axioms RQMCMarkov.MarkovDriving.sum_filter_occCount_eq
#print axioms RQMCMarkov.MarkovDriving.stackDrive_succ_of_eq
#print axioms RQMCMarkov.MarkovDriving.departureDiscrepancy_stackDrive
#print axioms RQMCMarkov.MarkovDriving.transCount_stackDrive
#print axioms RQMCMarkov.MarkovDriving.rotorWalk
#print axioms RQMCMarkov.MarkovDriving.rotorWalk_succ
#print axioms RQMCMarkov.MarkovDriving.rotorWalk_zero
#print axioms RQMCMarkov.MarkovDriving.rotorWalk_shift
#print axioms RQMCMarkov.MarkovDriving.rotorWalk_congr_mod
#print axioms RQMCMarkov.MarkovDriving.sum_range_add_periodic
#print axioms RQMCMarkov.MarkovDriving.sum_range_eq_sum_range_mod
#print axioms RQMCMarkov.MarkovDriving.IsRotorCycle
#print axioms RQMCMarkov.MarkovDriving.IsRotorCycle.mk
#print axioms RQMCMarkov.MarkovDriving.IsRotorCycle.len_pos
#print axioms RQMCMarkov.MarkovDriving.IsRotorCycle.card_eq
#print axioms RQMCMarkov.MarkovDriving.sum_cycle_eq
#print axioms RQMCMarkov.MarkovDriving.sum_range_rotor_centred_eq_zero
#print axioms RQMCMarkov.MarkovDriving.departureDiscrepancy_rotorWalk_eq
#print axioms RQMCMarkov.MarkovDriving.abs_sum_range_le_of_lt
#print axioms RQMCMarkov.MarkovDriving.abs_departureDiscrepancy_rotorWalk_le
#print axioms RQMCMarkov.MarkovDriving.abs_sub_mulVec_le
#print axioms RQMCMarkov.MarkovDriving.abs_departureDiscrepancy_rotorWalk_le_two_mul
#print axioms RQMCMarkov.MarkovDriving.abs_transCount_rotorWalk_sub_le
#print axioms RQMCMarkov.MarkovDriving.transCount_rotorWalk_eq_of_dvd
#print axioms RQMCMarkov.MarkovDriving.abs_occCount_rotorWalk_sub_le
#print axioms RQMCMarkov.MarkovDriving.abs_occFreq_rotorWalk_sub_le
#print axioms RQMCMarkov.MarkovDriving.occFreq_rotorWalk_isBigO
#print axioms RQMCMarkov.MarkovDriving.abs_transCount_rotorWalk_sub_target_le
#print axioms RQMCMarkov.MarkovDriving.card_offset_eq
#print axioms RQMCMarkov.MarkovDriving.abs_expected_occCount_rotorWalk_sub_le
#print axioms RQMCMarkov.MarkovDriving.twoStateStay78
#print axioms RQMCMarkov.MarkovDriving.isStationaryDistribution_twoStateStay78
#print axioms RQMCMarkov.MarkovDriving.not_transCount_eq_target
#print axioms RQMCMarkov.MarkovDriving.rotorCounterexampleChain
#print axioms RQMCMarkov.MarkovDriving.rotorCounterexampleStationary
#print axioms RQMCMarkov.MarkovDriving.rotorCounterexampleLen
#print axioms RQMCMarkov.MarkovDriving.rotorCounterexampleCycle
#print axioms RQMCMarkov.MarkovDriving.rotorCounterexampleOffset
#print axioms RQMCMarkov.MarkovDriving.expected_occCount_ne
#print axioms RQMCMarkov.MarkovDriving.step_lt_iff
#print axioms RQMCMarkov.MarkovDriving.departuresBelow
#print axioms RQMCMarkov.MarkovDriving.departuresBelow_eq_countAtMost
#print axioms RQMCMarkov.MarkovDriving.abs_departuresBelow_sub_le
#print axioms RQMCMarkov.MarkovDriving.card_step_eq_eq_sub
#print axioms RQMCMarkov.MarkovDriving.abs_card_step_eq_sub_le
#print axioms RQMCMarkov.MarkovDriving.extendNat
#print axioms RQMCMarkov.MarkovDriving.stateVariation
#print axioms RQMCMarkov.MarkovDriving.stateVariation_nonneg
#print axioms RQMCMarkov.MarkovDriving.stateVariation_le
#print axioms RQMCMarkov.MarkovDriving.sum_mul_sub_eq_abel
#print axioms RQMCMarkov.MarkovDriving.abs_sum_step_sub_le
#print axioms RQMCMarkov.MarkovDriving.abs_transCount_stackPath_sub_le
#print axioms RQMCMarkov.MarkovDriving.abs_departureDiscrepancy_stackPath_le
#print axioms RQMCMarkov.MarkovDriving.abs_occCount_stackPath_sub_le
#print axioms RQMCMarkov.MarkovDriving.mul_starDiscrepancy_vdc_le
#print axioms RQMCMarkov.MarkovDriving.abs_transCount_vdc_sub_le
#print axioms RQMCMarkov.MarkovDriving.abs_occCount_vdc_sub_le
#print axioms RQMCMarkov.MarkovDriving.abs_occFreq_vdc_sub_le
#print axioms RQMCMarkov.MarkovDriving.abs_empiricalTrans_vdc_sub_le
#print axioms RQMCMarkov.MarkovDriving.one_le_log_of_three_le
#print axioms RQMCMarkov.MarkovDriving.isBigO_log_div_of_le
#print axioms RQMCMarkov.MarkovDriving.occFreq_vdc_isBigO
#print axioms RQMCMarkov.MarkovDriving.empiricalTrans_vdc_isBigO
#print axioms RQMCMarkov.MarkovDriving.exists_abs_le_add_of_eventually
#print axioms RQMCMarkov.MarkovDriving.eventually_lilScale_mono
#print axioms RQMCMarkov.MarkovDriving.eventually_lilScale_le_mul
#print axioms RQMCMarkov.MarkovDriving.exists_eq_of_le_of_le
#print axioms RQMCMarkov.MarkovDriving.frequently_comp_of_unbounded
#print axioms RQMCMarkov.MarkovDriving.IsIIDStacks
#print axioms RQMCMarkov.MarkovDriving.IsIIDStacks.mk
#print axioms RQMCMarkov.MarkovDriving.IsIIDStacks.measurable
#print axioms RQMCMarkov.MarkovDriving.IsIIDStacks.indep
#print axioms RQMCMarkov.MarkovDriving.IsIIDStacks.law
#print axioms RQMCMarkov.MarkovDriving.isIIDStacks_iidUniform
#print axioms RQMCMarkov.MarkovDriving.mcDepartureSum
#print axioms RQMCMarkov.MarkovDriving.rowVariance
#print axioms RQMCMarkov.MarkovDriving.rowVariance_indicator
#print axioms RQMCMarkov.MarkovDriving.integral_comp_step
#print axioms RQMCMarkov.MarkovDriving.hasLIL_mcDepartureSum
#print axioms RQMCMarkov.MarkovDriving.departureDiscrepancy_mc_eq
#print axioms RQMCMarkov.MarkovDriving.HasLIL.eventually_abs_le
#print axioms RQMCMarkov.MarkovDriving.ae_abs_departureDiscrepancy_mc_le
#print axioms RQMCMarkov.MarkovDriving.ae_abs_departureDiscrepancy_mc_le_mul
#print axioms RQMCMarkov.MarkovDriving.ae_abs_transCount_mc_le
#print axioms RQMCMarkov.MarkovDriving.ae_abs_occCount_mc_le
#print axioms RQMCMarkov.MarkovDriving.ae_abs_occCount_mc_le_mul
#print axioms RQMCMarkov.MarkovDriving.ae_tendsto_occCount_mc
#print axioms RQMCMarkov.MarkovDriving.ae_frequently_transCount_mc_ge
#print axioms RQMCMarkov.MarkovDriving.ae_not_tendsto_transCount_mc
#print axioms RQMCMarkov.MarkovDriving.departureDiscrepancy_ranking
#print axioms RQMCMarkov.MarkovDriving.occupation_error_ranking
#print axioms RQMCMarkov.MarkovDriving.measurable_occCount_real
#print axioms RQMCMarkov.MarkovDriving.measurable_transCount_real
#print axioms RQMCMarkov.MarkovDriving.measurable_lilScale_occCount
#print axioms RQMCMarkov.MarkovDriving.measurable_le_prop
#print axioms RQMCMarkov.MarkovDriving.measurable_drivenPath
#print axioms RQMCMarkov.MarkovDriving.measurable_stackPath
#print axioms RQMCMarkov.MarkovDriving.map_drivenPath_eq_map_stackPath_path
#print axioms RQMCMarkov.MarkovDriving.ae_drivenPath_of_ae_stackPath
#print axioms RQMCMarkov.MarkovDriving.forall_exists_le_iff_nat
#print axioms RQMCMarkov.MarkovDriving.exists_le_iff_nat
#print axioms RQMCMarkov.MarkovDriving.measurableSet_transUpper
#print axioms RQMCMarkov.MarkovDriving.ae_abs_transCount_driven_le
#print axioms RQMCMarkov.MarkovDriving.ae_abs_occCount_driven_le
#print axioms RQMCMarkov.MarkovDriving.ae_unbounded_occCount_driven
#print axioms RQMCMarkov.MarkovDriving.ae_frequently_transCount_driven_ge
#print axioms RQMCMarkov.MarkovDriving.ae_not_tendsto_transCount_driven
#print axioms RQMCMarkov.MarkovDriving.occupation_error_ranking_driven
#print axioms RQMCMarkov.MarkovDriving.integrable_of_abs_le
#print axioms RQMCMarkov.MarkovDriving.abs_le_sum_sum_abs
#print axioms RQMCMarkov.MarkovDriving.integral_comp_step_of_map
#print axioms RQMCMarkov.MarkovDriving.integral_mul_comp_step_of_indepFun
#print axioms RQMCMarkov.MarkovDriving.padPast
#print axioms RQMCMarkov.MarkovDriving.measurable_padPast
#print axioms RQMCMarkov.MarkovDriving.drivenPath_padPast
#print axioms RQMCMarkov.MarkovDriving.indepFun_past_iidUniform
#print axioms RQMCMarkov.MarkovDriving.map_eval_iidUniform
#print axioms RQMCMarkov.MarkovDriving.measurable_drivenPath_apply
#print axioms RQMCMarkov.MarkovDriving.integral_mul_step_driven
#print axioms RQMCMarkov.MarkovDriving.incrementSum
#print axioms RQMCMarkov.MarkovDriving.measurable_pair_apply
#print axioms RQMCMarkov.MarkovDriving.measurable_incrementSum
#print axioms RQMCMarkov.MarkovDriving.abs_incrementSum_le
#print axioms RQMCMarkov.MarkovDriving.incrementSum_congr
#print axioms RQMCMarkov.MarkovDriving.integral_sq_incrementSum_driven
#print axioms RQMCMarkov.MarkovDriving.departureDiscrepancy_eq_incrementSum
#print axioms RQMCMarkov.MarkovDriving.sum_departureDiscrepancy_eq_incrementSum
#print axioms RQMCMarkov.MarkovDriving.sum_mul_sub_mulVec_eq_zero
#print axioms RQMCMarkov.MarkovDriving.sum_integral_comp_driven
#print axioms RQMCMarkov.MarkovDriving.integral_sq_sum_departureDiscrepancy_driven
#print axioms RQMCMarkov.MarkovDriving.integral_sq_departureDiscrepancy_driven
#print axioms RQMCMarkov.MarkovDriving.integral_sq_transCount_sub_driven
#print axioms RQMCMarkov.MarkovDriving.integral_occCount_driven_mem_Icc
#print axioms RQMCMarkov.MarkovDriving.integral_sq_transCount_sub_driven_le
#print axioms RQMCMarkov.MarkovDriving.integral_abs_le_sqrt_integral_sq
#print axioms RQMCMarkov.MarkovDriving.measurable_occCount_sub_driven
#print axioms RQMCMarkov.MarkovDriving.integral_sq_occCount_sub_driven_mem
#print axioms RQMCMarkov.MarkovDriving.integral_sq_occCount_sub_driven_le
#print axioms RQMCMarkov.MarkovDriving.abs_integral_occCount_sub_driven_le
#print axioms RQMCMarkov.MarkovDriving.tendsto_integral_occCount_div_driven
#print axioms RQMCMarkov.MarkovDriving.eventually_integral_sq_occCount_sub_driven_ge
#print axioms RQMCMarkov.MarkovDriving.integral_sq_occFreq_sub_driven_le
#print axioms RQMCMarkov.MarkovDriving.integral_sq_transFreq_sub_driven_le
#print axioms RQMCMarkov.MarkovDriving.dotProduct_indicator
#print axioms RQMCMarkov.MarkovDriving.eventually_integral_sq_occCount_sub_driven_ge_of_irreducible
#print axioms RQMCMarkov.MarkovDriving.isStochastic_twoStateStay78
#print axioms RQMCMarkov.MarkovDriving.irreducible_twoStateStay78
#print axioms RQMCMarkov.MarkovDriving.poisson_twoStateStay78
#print axioms RQMCMarkov.MarkovDriving.rowVariance_twoStateStay78
#print axioms RQMCMarkov.MarkovDriving.occCount_mse_twoStateStay78
#print axioms RQMCMarkov.MarkovDriving.departureIncrement
#print axioms RQMCMarkov.MarkovDriving.departureIncrement_iid
#print axioms RQMCMarkov.MarkovDriving.tendstoInDistribution_comp_of_tendsto
#print axioms RQMCMarkov.MarkovDriving.tendstoInDistribution_sum_floor_mul
#print axioms RQMCMarkov.MarkovDriving.tendsto_div_of_forall_abs_sub_le
#print axioms RQMCMarkov.MarkovDriving.measurable_occCount_nat
#print axioms RQMCMarkov.MarkovDriving.measurable_departureDiscrepancy_div
#print axioms RQMCMarkov.MarkovDriving.tendstoInDistribution_departureDiscrepancy_stack
#print axioms RQMCMarkov.MarkovDriving.tendstoInDistribution_departureDiscrepancy_driven
#print axioms RQMCMarkov.MarkovDriving.tendstoInDistribution_transCount_driven
#print axioms RQMCMarkov.MarkovDriving.tendstoInDistribution_transCount_driven_of_irreducible
#print axioms RQMCMarkov.MarkovDriving.tendstoInDistribution_transCount_twoStateStay78
#print axioms RQMCMarkov.MarkovDriving.occCount_add_of_stay
#print axioms RQMCMarkov.MarkovDriving.rotorWalk_not_stay
#print axioms RQMCMarkov.MarkovDriving.runLength_rotorWalk_le
#print axioms RQMCMarkov.MarkovDriving.exists_ne_of_lt_one
#print axioms RQMCMarkov.MarkovDriving.geomPMF
#print axioms RQMCMarkov.MarkovDriving.sum_geomPMF
#print axioms RQMCMarkov.MarkovDriving.rotor_spells_not_geometric
#print axioms RQMCMarkov.MarkovDriving.len78
#print axioms RQMCMarkov.MarkovDriving.cycle78
#print axioms RQMCMarkov.MarkovDriving.otherState
#print axioms RQMCMarkov.MarkovDriving.isRotorCycle78
#print axioms RQMCMarkov.MarkovDriving.rotorWalk78_lt_sixteen
#print axioms RQMCMarkov.MarkovDriving.rotorWalk78_sixteen
#print axioms RQMCMarkov.MarkovDriving.rotorWalk78_canonical
#print axioms RQMCMarkov.MarkovDriving.offsets78
#print axioms RQMCMarkov.MarkovDriving.rotorWalk78_return
#print axioms RQMCMarkov.MarkovDriving.rotorWalk78_eventually_canonical
#print axioms RQMCMarkov.MarkovDriving.otherState_ne
#print axioms RQMCMarkov.MarkovDriving.runLength_rotorWalk78
#print axioms RQMCMarkov.MarkovDriving.rotor78_spells_not_geometric
#print axioms RQMCMarkov.MarkovDriving.pathProb_extend_stay
#print axioms RQMCMarkov.MarkovDriving.uniformIco_step_ne
#print axioms RQMCMarkov.MarkovDriving.iidUniform_spell_after_history
#print axioms RQMCMarkov.MarkovDriving.iidUniform_firstSpell
#print axioms RQMCMarkov.MarkovDriving.iidUniform_runLength_eq
#print axioms RQMCMarkov.MarkovDriving.geomQuantile
#print axioms RQMCMarkov.MarkovDriving.geomQuantile_eq_succ_iff
#print axioms RQMCMarkov.MarkovDriving.geomQuantile_eq_zero_iff
#print axioms RQMCMarkov.MarkovDriving.measurable_geomQuantile
#print axioms RQMCMarkov.MarkovDriving.geomQuantile_preimage_inter_Ico
#print axioms RQMCMarkov.MarkovDriving.uniformIco_geomQuantile_eq_succ
#print axioms RQMCMarkov.MarkovDriving.uniformIco_geomQuantile_eq_zero
#print axioms RQMCMarkov.MarkovDriving.uniformIco_geomQuantile_eq_firstSpell
#print axioms RQMCMarkov.MarkovDriving.lintegral_geomQuantile
#print axioms RQMCMarkov.MarkovDriving.summable_succ_sq_mul_geometric
#print axioms RQMCMarkov.MarkovDriving.summable_succ_mul_geometric
#print axioms RQMCMarkov.MarkovDriving.integral_geomQuantile
#print axioms RQMCMarkov.MarkovDriving.memLp_geomQuantile
#print axioms RQMCMarkov.MarkovDriving.integral_geomQuantile_id
#print axioms RQMCMarkov.MarkovDriving.integral_geomQuantile_sq
#print axioms RQMCMarkov.MarkovDriving.variance_geomQuantile
#print axioms RQMCMarkov.MarkovDriving.variance_stratified_le_div
#print axioms RQMCMarkov.MarkovDriving.integral_stratifiedSpell
#print axioms RQMCMarkov.MarkovDriving.variance_stratifiedSpell_le_iid
#print axioms RQMCMarkov.MarkovDriving.variance_stratifiedSpell_le
