/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

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
