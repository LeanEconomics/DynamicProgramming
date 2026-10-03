import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Constructions
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.Order.Field
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Max, min and pointwise operations on functions

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §1.2.1.1 (p. 12),
Exercise 1.2.1 (p. 13), §1.2.4.1 (pp. 29–30), and the bound (1.28) with
Exercise 1.3.1 (p. 34) that the contraction proof for job search rests on.

The book writes `a ∨ b` for `max a b` and `a ∧ b` for `min a b`, and defines
`|a| := a ∨ (−a)`. Functions in `ℝ^X` are combined pointwise, (1.20)–(1.22).
In Lean these are Mathlib's `Pi` instances; the lemmas here record that they
compute as the book says.
-/

namespace SargentStachurski.JobSearch

/-- The book's definition of the absolute value, `|a| = a ∨ (−a)` (p. 12). -/
theorem abs_eq_max_neg' (a : ℝ) : |a| = max a (-a) := abs_eq_max_neg

/-- Exercise 1.2.1 (p. 13): `α ∨ (s + t) ≤ s + α ∨ t` whenever `s ≥ 0`. -/
theorem max_add_le_add_max {α s t : ℝ} (hs : 0 ≤ s) : max α (s + t) ≤ s + max α t := by
  rcases le_total α (s + t) with h | h
  · rw [max_eq_right h]
    linarith [le_max_right α t]
  · rw [max_eq_left h]
    calc α ≤ max α t := le_max_left _ _
      _ ≤ s + max α t := le_add_of_nonneg_left hs

/-- One half of (1.28), derived from Exercise 1.2.1 as the book's solution to
Exercise 1.3.1 does: `α ∨ x ≤ |x − y| + α ∨ y`. -/
theorem max_le_abs_sub_add_max (α x y : ℝ) : max α x ≤ |x - y| + max α y := by
  have hx : x ≤ |x - y| + y := by
    have := le_abs_self (x - y)
    linarith
  calc max α x ≤ max α (|x - y| + y) := max_le_max_left α hx
    _ ≤ |x - y| + max α y := max_add_le_add_max (abs_nonneg _)

/-- The bound (1.28), Exercise 1.3.1 (p. 34): `|α ∨ x − α ∨ y| ≤ |x − y|`. -/
theorem abs_max_sub_max_le (α x y : ℝ) : |max α x - max α y| ≤ |x - y| := by
  rw [abs_sub_le_iff]
  constructor
  · have := max_le_abs_sub_add_max α x y
    linarith
  · have := max_le_abs_sub_add_max α y x
    rw [abs_sub_comm y x] at this
    linarith

/-- The `min` twin of (1.28): `|α ∧ x − α ∧ y| ≤ |x − y|`, used when the book takes a
minimum rather than a maximum (p. 12, `a ∧ b := min{a, b}`). -/
theorem abs_min_sub_min_le (α x y : ℝ) : |min α x - min α y| ≤ |x - y| := by
  have h := abs_max_sub_max_le (-α) (-x) (-y)
  rw [max_neg_neg, max_neg_neg, neg_sub_neg, neg_sub_neg, abs_sub_comm (min α y),
    abs_sub_comm y] at h
  exact h

/-- `x ↦ α ∨ x` is order preserving, the fact behind the greedy comparison in (1.29). -/
theorem max_le_max_of_le (α : ℝ) {x y : ℝ} (h : x ≤ y) : max α x ≤ max α y :=
  max_le_max_left α h

variable {X : Type*} (u v : X → ℝ) (α β : ℝ) (x : X)

/-- (1.20), p. 29: `(αu + βv)(x) = αu(x) + βv(x)`. -/
theorem smul_add_smul_apply : (α • u + β • v) x = α * u x + β * v x := by
  simp

/-- (1.20), p. 29: `(uv)(x) = u(x)v(x)`. -/
theorem mul_apply' : (u * v) x = u x * v x := rfl

/-- (1.21), p. 29: `|u|(x) = |u(x)|`. -/
theorem abs_apply' : |u| x = |u x| := rfl

/-- (1.21), p. 29: `(u ∨ v)(x) = u(x) ∨ v(x)`. -/
theorem sup_apply' : (u ⊔ v) x = max (u x) (v x) := rfl

/-- (1.21), p. 29: `(u ∧ v)(x) = u(x) ∧ v(x)`. -/
theorem inf_apply' : (u ⊓ v) x = min (u x) (v x) := rfl

end SargentStachurski.JobSearch

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Fixed points and global stability

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §1.2.2.1–§1.2.2.2
(pp. 20–22). A self-map `T` on a set `U` is a function `U → U`; a fixed point
is a `u` with `Tu = u` (Mathlib's `Function.IsFixedPt`); `T` is globally
stable on `U` if it has a unique fixed point `u*` and `Tᵏu → u*` for every
`u ∈ U`. The set `U` is a type here, so "`T` is a self-map on `U`" is
`T : U → U` and no separate definition is needed.

The exercises of the section are proved: Exercise 1.2.15 (eventually constant
iterates), Exercise 1.2.16 (a limit of iterates at which `T` is continuous is
a fixed point) and Exercise 1.2.18 (the fixed point of a globally stable map
lies in every nonempty closed invariant set). Example 1.2.2 (the affine map
`u ↦ Au + b`) is in `NeumannSeries`.
-/

open Filter Topology Function

namespace SargentStachurski.JobSearch

variable {U : Type*}

/-- Global stability (p. 22): `T` has a unique fixed point `u*` in `U`, and the iterates
`Tᵏu` converge to `u*` from every `u ∈ U`. -/
def GloballyStable [TopologicalSpace U] (T : U → U) : Prop :=
  ∃ u' : U, IsFixedPt T u' ∧ (∀ v, IsFixedPt T v → v = u') ∧
    ∀ u, Tendsto (fun k : ℕ => T^[k] u) atTop (𝓝 u')

/-- Example 1.2.3 (p. 20): every point is fixed under the identity map. -/
theorem isFixedPt_id (u : U) : IsFixedPt (id : U → U) u := rfl

/-- Example 1.2.4 (p. 20): `u ↦ u + 1` on `ℕ` has no fixed point. -/
theorem not_isFixedPt_succ (u : ℕ) : ¬ IsFixedPt Nat.succ u := Nat.succ_ne_self u

/-- Exercise 1.2.15 (p. 21), existence: if `Tᵏu = ū` for all `u` and all `k ≥ m`, then
`ū` is a fixed point of `T`. -/
theorem isFixedPt_of_iterate_eventually_const {T : U → U} {u' : U} {m : ℕ}
    (h : ∀ u, ∀ k, m ≤ k → T^[k] u = u') : IsFixedPt T u' := by
  have h1 : T^[m + 1] u' = u' := h u' (m + 1) (Nat.le_succ m)
  have h2 : T^[m] u' = u' := h u' m le_rfl
  calc T u' = T (T^[m] u') := by rw [h2]
    _ = T^[m + 1] u' := (iterate_succ_apply' T m u').symm
    _ = u' := h1

/-- Exercise 1.2.15 (p. 21), uniqueness: under the same hypothesis every fixed point equals
`ū`. -/
theorem eq_of_isFixedPt_of_iterate_eventually_const {T : U → U} {u' : U} {m : ℕ}
    (h : ∀ u, ∀ k, m ≤ k → T^[k] u = u') {v : U} (hv : IsFixedPt T v) : v = u' := by
  rw [← Function.IsFixedPt.iterate hv m, h v m le_rfl]

/-- Exercise 1.2.16 (p. 21): if `Tᵐu → u*` and `T` is continuous at `u*`, then `u*` is a
fixed point of `T`. -/
theorem isFixedPt_of_tendsto_iterate [TopologicalSpace U] [T2Space U] {T : U → U} {u u' : U}
    (hlim : Tendsto (fun m : ℕ => T^[m] u) atTop (𝓝 u')) (hcont : ContinuousAt T u') :
    IsFixedPt T u' := by
  have h1 : Tendsto (fun m : ℕ => T (T^[m] u)) atTop (𝓝 (T u')) := hcont.tendsto.comp hlim
  have h2 : Tendsto (fun m : ℕ => T (T^[m] u)) atTop (𝓝 u') := by
    have := (tendsto_add_atTop_iff_nat 1).2 hlim
    simpa only [iterate_succ_apply'] using this
  exact (tendsto_nhds_unique h1 h2 : T u' = u')

/-- The fixed point of a globally stable map, as the unique witness. -/
theorem GloballyStable.exists_unique [TopologicalSpace U] {T : U → U} (h : GloballyStable T) :
    ∃! u', IsFixedPt T u' := by
  obtain ⟨u', hfix, huniq, -⟩ := h
  exact ⟨u', hfix, huniq⟩

/-- In a Hausdorff space uniqueness of the fixed point is automatic: a fixed point `v` has
constant iterates `Tᵏv = v`, which must converge to `u*`. So global stability needs only a
fixed point to which every orbit converges. -/
theorem globallyStable_of_tendsto [TopologicalSpace U] [T2Space U] {T : U → U} {u' : U}
    (hfix : IsFixedPt T u') (hlim : ∀ u, Tendsto (fun k : ℕ => T^[k] u) atTop (𝓝 u')) :
    GloballyStable T := by
  refine ⟨u', hfix, fun v hv => ?_, hlim⟩
  have hconst : Tendsto (fun k : ℕ => T^[k] v) atTop (𝓝 v) := by
    have : (fun k : ℕ => T^[k] v) = fun _ => v := funext fun k => Function.IsFixedPt.iterate hv k
    rw [this]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hconst (hlim v)

/-- `T` is invariant on `C` (p. 22): `u ∈ C` implies `Tu ∈ C`. This is Mathlib's `Set.MapsTo`. -/
theorem iterate_mem_of_mapsTo {T : U → U} {C : Set U} (hC : Set.MapsTo T C C) {u : U}
    (hu : u ∈ C) (k : ℕ) : T^[k] u ∈ C := by
  induction k with
  | zero => simpa using hu
  | succ k ih => rw [iterate_succ_apply']; exact hC ih

/-- Exercise 1.2.18 (p. 22): the fixed point of a globally stable map lies in every closed
invariant set `C`. The book omits that `C` must be nonempty; the empty set is closed and
invariant and contains no fixed point. -/
theorem GloballyStable.fixedPt_mem_of_isClosed [TopologicalSpace U] {T : U → U}
    (h : GloballyStable T) {u' : U} (hu' : IsFixedPt T u') {C : Set U} (hCne : C.Nonempty)
    (hclosed : IsClosed C) (hinv : Set.MapsTo T C C) : u' ∈ C := by
  obtain ⟨u₀, hfix₀, huniq, hlim⟩ := h
  obtain ⟨u, hu⟩ := hCne
  have hmem : ∀ k : ℕ, T^[k] u ∈ C := iterate_mem_of_mapsTo hinv hu
  have h₀ : u₀ ∈ C := hclosed.mem_of_tendsto (hlim u) (Eventually.of_forall hmem)
  rwa [huniq u' hu']

end SargentStachurski.JobSearch

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Contractions and Banach's fixed-point theorem

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §1.2.2.3 (pp. 22–23)
and the restatement for the function space `ℝ^X` (p. 31).

A self-map `T` on a nonempty `U ⊆ ℝⁿ` is a contraction of modulus `λ` with
respect to a norm if `‖Tu − Tv‖ ≤ λ‖u − v‖` on `U` with `λ < 1`, (1.17).
Theorem 1.2.3 (Banach): if `U` is closed, `T` has a unique fixed point `u*` in
`U` and `‖Tᵏu − u*‖ ≤ λᵏ‖u − u*‖`, (1.18); in particular `T` is globally
stable on `U`.

The book proves the theorem through Exercises 1.2.19 and 1.2.21–1.2.23, and
that is the route taken here: the iterates `uₘ = Tᵐu₀` satisfy the geometric
bound of Exercise 1.2.21, so they are Cauchy (Exercise 1.2.22), converge in
the complete space, and the limit lies in the closed set `U` (Exercise
1.2.23) and is fixed (Exercise 1.2.16 with the continuity of Exercise 1.2.19).

The ambient space is any complete normed group `E`, which covers `ℝⁿ` under
every norm (§1.2.1.3: all norms on `ℝⁿ` are equivalent, so "closed" and
"converges" do not depend on the norm, but the contraction modulus does).
Exercise 1.2.24 (damped iteration) closes the section.
-/

open Filter Topology Function Set

namespace SargentStachurski.JobSearch

variable {E : Type*} [NormedAddCommGroup E]

/-- `T` is a contraction of modulus `L` on `U` with respect to the norm of `E`, (1.17), p. 22.
The book writes the modulus `λ`; it lies in `[0, 1)` (p. 31). -/
structure IsContractionOn (T : E → E) (U : Set E) (L : ℝ) : Prop where
  mapsTo : MapsTo T U U
  nonneg : 0 ≤ L
  lt_one : L < 1
  norm_sub_le : ∀ u ∈ U, ∀ v ∈ U, ‖T u - T v‖ ≤ L * ‖u - v‖

namespace IsContractionOn

variable {T : E → E} {U : Set E} {L : ℝ}

/-- Exercise 1.2.19 (p. 22), first part: a contraction is continuous on `U`. -/
theorem continuousOn (h : IsContractionOn T U L) : ContinuousOn T U := by
  have hlip : LipschitzOnWith ⟨L, h.nonneg⟩ T U := by
    refine lipschitzOnWith_iff_dist_le_mul.2 fun u hu v hv => ?_
    rw [dist_eq_norm, dist_eq_norm]
    exact h.norm_sub_le u hu v hv
  exact hlip.continuousOn

/-- Exercise 1.2.19 (p. 22), second part: a contraction has at most one fixed point in `U`. -/
theorem fixedPt_unique (h : IsContractionOn T U L) {u v : E} (hu : u ∈ U) (hv : v ∈ U)
    (hfu : IsFixedPt T u) (hfv : IsFixedPt T v) : u = v := by
  have hb := h.norm_sub_le u hu v hv
  rw [hfu.eq, hfv.eq] at hb
  have hnn : 0 ≤ ‖u - v‖ := norm_nonneg _
  have : ‖u - v‖ * (1 - L) ≤ 0 := by nlinarith
  have hpos : 0 < 1 - L := by linarith [h.lt_one]
  have : ‖u - v‖ ≤ 0 := by nlinarith
  exact sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm this hnn))

/-- The iterates of a contraction stay in `U`. -/
theorem iterate_mem (h : IsContractionOn T U L) {u : E} (hu : u ∈ U) (k : ℕ) : T^[k] u ∈ U :=
  iterate_mem_of_mapsTo h.mapsTo hu k

/-- Consecutive iterates: `‖uᵢ − uᵢ₊₁‖ ≤ λⁱ ‖u₀ − u₁‖`, the step behind Exercise 1.2.21. -/
theorem norm_iterate_sub_iterate_succ_le (h : IsContractionOn T U L) {u : E} (hu : u ∈ U)
    (i : ℕ) : ‖T^[i] u - T^[i + 1] u‖ ≤ L ^ i * ‖u - T u‖ := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [iterate_succ_apply', iterate_succ_apply' T (i + 1)]
    calc ‖T (T^[i] u) - T (T^[i + 1] u)‖
        ≤ L * ‖T^[i] u - T^[i + 1] u‖ :=
          h.norm_sub_le _ (h.iterate_mem hu i) _ (h.iterate_mem hu (i + 1))
      _ ≤ L * (L ^ i * ‖u - T u‖) := mul_le_mul_of_nonneg_left ih h.nonneg
      _ = L ^ (i + 1) * ‖u - T u‖ := by ring

/-- Exercise 1.2.21 (p. 23): for `m < k`, `‖uₘ − uₖ‖ ≤ ∑_{i=m}^{k−1} λⁱ ‖u₀ − u₁‖`, where
`uₘ = Tᵐu₀`. -/
theorem norm_iterate_sub_iterate_le_sum (h : IsContractionOn T U L) {u : E} (hu : u ∈ U)
    {m k : ℕ} (hmk : m ≤ k) :
    ‖T^[m] u - T^[k] u‖ ≤ ∑ i ∈ Finset.Ico m k, L ^ i * ‖u - T u‖ := by
  have := dist_le_Ico_sum_dist (fun i => T^[i] u) hmk
  simp only [dist_eq_norm] at this
  refine this.trans (Finset.sum_le_sum fun i _ => ?_)
  exact h.norm_iterate_sub_iterate_succ_le hu i

/-- The closed form of the bound in Exercise 1.2.21, as in the book's solution to
Exercise 1.2.22: `‖uₘ − uₖ‖ ≤ (λᵐ − λᵏ)/(1 − λ) ‖u₀ − u₁‖`. -/
theorem norm_iterate_sub_iterate_le (h : IsContractionOn T U L) {u : E} (hu : u ∈ U)
    {m k : ℕ} (hmk : m ≤ k) :
    ‖T^[m] u - T^[k] u‖ ≤ (L ^ m - L ^ k) / (1 - L) * ‖u - T u‖ := by
  refine (h.norm_iterate_sub_iterate_le_sum hu hmk).trans (le_of_eq ?_)
  rw [← Finset.sum_mul, geom_sum_Ico h.lt_one.ne hmk]
  have h1 : (1 : ℝ) - L ≠ 0 := by linarith [h.lt_one]
  have h2 : L - 1 ≠ 0 := by linarith [h.lt_one]
  field_simp
  ring

/-- Exercise 1.2.22 (p. 23): the iterates form a Cauchy sequence. -/
theorem cauchySeq_iterate (h : IsContractionOn T U L) {u : E} (hu : u ∈ U) :
    CauchySeq fun m : ℕ => T^[m] u := by
  refine cauchySeq_of_le_geometric L ‖u - T u‖ h.lt_one fun n => ?_
  rw [dist_eq_norm]
  have := h.norm_iterate_sub_iterate_succ_le hu n
  linarith [mul_comm (L ^ n) ‖u - T u‖]

/-- Exercise 1.2.23 (p. 23): when `U` is closed, the limit of the iterates lies in `U`. -/
theorem limit_mem (h : IsContractionOn T U L) (hU : IsClosed U) {u u' : E} (hu : u ∈ U)
    (hlim : Tendsto (fun m : ℕ => T^[m] u) atTop (𝓝 u')) : u' ∈ U :=
  hU.mem_of_tendsto hlim (Eventually.of_forall (h.iterate_mem hu))

/-- The limit of the iterates, if it lies in `U`, is a fixed point: the step in the book's
proof of Theorem 1.2.3 that invokes Exercises 1.2.16 and 1.2.19. Only continuity within `U`
is available, so the argument is made directly from the contraction inequality. -/
theorem isFixedPt_of_tendsto (h : IsContractionOn T U L) {u u' : E} (hu : u ∈ U) (hu' : u' ∈ U)
    (hlim : Tendsto (fun m : ℕ => T^[m] u) atTop (𝓝 u')) : IsFixedPt T u' := by
  have h1 : Tendsto (fun m : ℕ => T (T^[m] u)) atTop (𝓝 u') := by
    have := (tendsto_add_atTop_iff_nat 1).2 hlim
    simpa only [iterate_succ_apply'] using this
  have h2 : Tendsto (fun m : ℕ => T (T^[m] u)) atTop (𝓝 (T u')) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simp only [dist_eq_norm]
    refine squeeze_zero (fun _ => norm_nonneg _)
      (fun m => h.norm_sub_le _ (h.iterate_mem hu m) _ hu') ?_
    have := (tendsto_iff_dist_tendsto_zero.1 hlim).const_mul L
    simpa [dist_eq_norm] using this
  exact (tendsto_nhds_unique h2 h1 : T u' = u')

/-- The rate (1.18), p. 23: `‖Tᵏu − u*‖ ≤ λᵏ ‖u − u*‖` for a fixed point `u*` in `U`. -/
theorem norm_iterate_sub_fixedPt_le (h : IsContractionOn T U L) {u u' : E} (hu : u ∈ U)
    (hu' : u' ∈ U) (hfix : IsFixedPt T u') (k : ℕ) :
    ‖T^[k] u - u'‖ ≤ L ^ k * ‖u - u'‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply']
    calc ‖T (T^[k] u) - u'‖ = ‖T (T^[k] u) - T u'‖ := by rw [hfix.eq]
      _ ≤ L * ‖T^[k] u - u'‖ := h.norm_sub_le _ (h.iterate_mem hu k) _ hu'
      _ ≤ L * (L ^ k * ‖u - u'‖) := mul_le_mul_of_nonneg_left ih h.nonneg
      _ = L ^ (k + 1) * ‖u - u'‖ := by ring

/-- The iterates converge to any fixed point in `U`, by (1.18). -/
theorem tendsto_iterate_fixedPt (h : IsContractionOn T U L) {u u' : E} (hu : u ∈ U)
    (hu' : u' ∈ U) (hfix : IsFixedPt T u') :
    Tendsto (fun k : ℕ => T^[k] u) atTop (𝓝 u') := by
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [dist_eq_norm]
  refine squeeze_zero (fun _ => norm_nonneg _) (h.norm_iterate_sub_fixedPt_le hu hu' hfix) ?_
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one h.nonneg h.lt_one).mul_const ‖u - u'‖
  simpa using this

variable [CompleteSpace E]

/-- Theorem 1.2.3 (Banach's contraction mapping theorem, p. 23), existence: a contraction on
a nonempty closed `U` has a fixed point in `U`. -/
theorem exists_fixedPt (h : IsContractionOn T U L) (hU : IsClosed U) (hne : U.Nonempty) :
    ∃ u' ∈ U, IsFixedPt T u' := by
  obtain ⟨u, hu⟩ := hne
  obtain ⟨u', hlim⟩ := cauchySeq_tendsto_of_complete (h.cauchySeq_iterate hu)
  have hu' := h.limit_mem hU hu hlim
  exact ⟨u', hu', h.isFixedPt_of_tendsto hu hu' hlim⟩

/-- Theorem 1.2.3 (p. 23), in one statement: a contraction on a nonempty closed `U` has a
unique fixed point `u*` in `U`, and `‖Tᵏu − u*‖ ≤ λᵏ‖u − u*‖` for every `u ∈ U` and `k`. -/
theorem banach (h : IsContractionOn T U L) (hU : IsClosed U) (hne : U.Nonempty) :
    ∃ u' ∈ U, IsFixedPt T u' ∧ (∀ v ∈ U, IsFixedPt T v → v = u') ∧
      ∀ u ∈ U, ∀ k : ℕ, ‖T^[k] u - u'‖ ≤ L ^ k * ‖u - u'‖ := by
  obtain ⟨u', hu', hfix⟩ := h.exists_fixedPt hU hne
  exact ⟨u', hu', hfix, fun v hv hfv => h.fixedPt_unique hv hu' hfv hfix,
    fun u hu k => h.norm_iterate_sub_fixedPt_le hu hu' hfix k⟩

/-- Theorem 1.2.3 (p. 23), "in particular `T` is globally stable on `U`": as a self-map of
the subtype `↥U`. -/
theorem globallyStable (h : IsContractionOn T U L) (hU : IsClosed U) (hne : U.Nonempty) :
    GloballyStable (h.mapsTo.restrict T U U) := by
  obtain ⟨u', hu', hfix, -, -⟩ := h.banach hU hne
  have hiter : ∀ (u : U) (k : ℕ), ((h.mapsTo.restrict T U U)^[k] u : E) = T^[k] u := by
    intro u k
    rw [MapsTo.iterate_restrict]
    rfl
  refine globallyStable_of_tendsto (u' := ⟨u', hu'⟩) ?_ fun u => ?_
  · exact Subtype.ext (by simpa [MapsTo.val_restrict_apply] using hfix.eq)
  · rw [tendsto_subtype_rng]
    simp only [hiter]
    exact h.tendsto_iterate_fixedPt u.2 hu' hfix

end IsContractionOn

/-- Exercise 1.2.24 (p. 23): if `T` is a contraction of modulus `β` on all of `E`, then the
damped map `F u = (1 − α)u + αTu` with `0 < α ≤ 1` is a contraction of modulus
`1 − α + αβ < 1`. -/
theorem isContractionOn_damped {T : E → E} {β : ℝ} [NormedSpace ℝ E]
    (h : IsContractionOn T univ β) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    IsContractionOn (fun u => (1 - α) • u + α • T u) univ (1 - α + α * β) := by
  refine ⟨mapsTo_univ _ _, ?_, ?_, fun u _ v _ => ?_⟩
  · nlinarith [h.nonneg]
  · nlinarith [h.lt_one]
  · have hb := h.norm_sub_le u trivial v trivial
    calc ‖(1 - α) • u + α • T u - ((1 - α) • v + α • T v)‖
        = ‖(1 - α) • (u - v) + α • (T u - T v)‖ := by
          congr 1
          simp only [smul_sub]
          abel
      _ ≤ ‖(1 - α) • (u - v)‖ + ‖α • (T u - T v)‖ := norm_add_le _ _
      _ = (1 - α) * ‖u - v‖ + α * ‖T u - T v‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith),
            Real.norm_of_nonneg hα0.le]
      _ ≤ (1 - α) * ‖u - v‖ + α * (β * ‖u - v‖) := by gcongr
      _ = (1 - α + α * β) * ‖u - v‖ := by ring

/-- Exercise 1.2.24 (p. 23), continued: the damped map has the same fixed points as `T`. -/
theorem isFixedPt_damped_iff {T : E → E} [NormedSpace ℝ E] {α : ℝ} (hα0 : 0 < α) (u : E) :
    IsFixedPt (fun u => (1 - α) • u + α • T u) u ↔ IsFixedPt T u := by
  simp only [IsFixedPt]
  constructor
  · intro h
    have : α • T u = α • u := by
      have h' : (1 - α) • u + α • T u = u := h
      rw [eq_sub_of_add_eq' h', sub_smul, one_smul, sub_sub_cancel]
    exact smul_right_injective E hα0.ne' this
  · intro h
    show (1 - α) • u + α • T u = u
    rw [h, sub_smul, one_smul]
    abel

/-- Exercise 1.2.24 (p. 23), conclusion: damped iterates converge to the fixed point of `T`
from any starting point, for `0 < α ≤ 1`. -/
theorem tendsto_damped_iterate [CompleteSpace E] [NormedSpace ℝ E] {T : E → E} {β : ℝ}
    (h : IsContractionOn T univ β) {u' : E} (hfix : IsFixedPt T u') {α : ℝ} (hα0 : 0 < α)
    (hα1 : α ≤ 1) (u : E) :
    Tendsto (fun k : ℕ => (fun u => (1 - α) • u + α • T u)^[k] u) atTop (𝓝 u') :=
  (isContractionOn_damped h hα0 hα1).tendsto_iterate_fixedPt trivial trivial
    ((isFixedPt_damped_iff hα0 u').2 hfix)

/-- Banach's theorem on the function space `ℝ^X` for finite `X` (p. 31): with the supremum
norm `‖f‖ = max_x |f(x)|`, a contraction on a nonempty closed `C ⊆ ℝ^X` has a unique fixed
point `f*` in `C` with `‖Tⁿf − f*‖ ≤ λⁿ‖f − f*‖`. This is Theorem 1.2.3 for `E = X → ℝ`. -/
theorem IsContractionOn.banach_pi {X : Type*} [Fintype X] {T : (X → ℝ) → (X → ℝ)}
    {C : Set (X → ℝ)} {L : ℝ} (h : IsContractionOn T C L) (hC : IsClosed C)
    (hne : C.Nonempty) :
    ∃ f' ∈ C, IsFixedPt T f' ∧ (∀ g ∈ C, IsFixedPt T g → g = f') ∧
      ∀ f ∈ C, ∀ n : ℕ, ‖T^[n] f - f'‖ ≤ L ^ n * ‖f - f'‖ :=
  h.banach hC hne

end SargentStachurski.JobSearch

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Norms on `ℝⁿ` and on matrices

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §1.2.1.2–§1.2.1.4
(pp. 13–17): the ℓ¹, weighted ℓ¹ and supremum norms on `ℝⁿ`, the four norm
axioms, equivalence of norms, pointwise versus norm convergence, and matrix
norms with the submultiplicative property.

A norm on `ℝⁿ` is a function `N : (Fin n → ℝ) → ℝ` with the four properties of
p. 13: nonnegativity, positive definiteness, absolute homogeneity and the
triangle inequality. The exercises ask for the axioms to be checked for the
explicit functions, so `IsNorm` packages the four axioms and each exercise
proves them for its function. Mathlib's own normed-group instance on
`Fin n → ℝ` is the supremum norm, and the lemmas of §1.2.1.3 and §1.2.4.2 that
the book states in terms of "any norm" are proved for it.
-/

open Finset

namespace SargentStachurski.JobSearch

/-- The four norm axioms of p. 13 for a function `N` on a real vector space. -/
structure IsNorm {V : Type*} [AddCommGroup V] [Module ℝ V] (N : V → ℝ) : Prop where
  nonneg : ∀ u, 0 ≤ N u
  eq_zero_iff : ∀ u, N u = 0 ↔ u = 0
  smul : ∀ (α : ℝ) u, N (α • u) = |α| * N u
  add_le : ∀ u v, N (u + v) ≤ N u + N v

variable {n : ℕ}

/-- The ℓ¹ norm (1.9), p. 13: `‖u‖₁ = ∑ᵢ |uᵢ|`. -/
def l1Norm (u : Fin n → ℝ) : ℝ := ∑ i, |u i|

/-- The weighted ℓ¹ norm of Exercise 1.2.3, p. 14: `‖u‖_{1,p} = ∑ᵢ |uᵢ| pᵢ`. -/
def weightedL1Norm (p : Fin n → ℝ) (u : Fin n → ℝ) : ℝ := ∑ i, |u i| * p i

/-- The supremum norm of Exercise 1.2.4, p. 14: `‖u‖_∞ = maxᵢ |uᵢ|`. -/
def supNorm (u : Fin n → ℝ) : ℝ := ‖u‖

/-- The ℓ⁰ "norm" of Exercise 1.2.5, p. 14: the number of nonzero coordinates. -/
noncomputable def l0Norm (u : Fin n → ℝ) : ℝ := ∑ i, if u i ≠ 0 then 1 else 0

/-- Exercise 1.2.2 (p. 14): the ℓ¹ norm is a norm. -/
theorem isNorm_l1Norm : IsNorm (l1Norm (n := n)) where
  nonneg u := sum_nonneg fun i _ => abs_nonneg (u i)
  eq_zero_iff u := by
    constructor
    · intro h
      have h0 := (sum_eq_zero_iff_of_nonneg fun i _ => abs_nonneg (u i)).1 h
      funext i
      exact abs_eq_zero.1 (h0 i (mem_univ i))
    · rintro rfl
      simp [l1Norm]
  smul α u := by
    simp only [l1Norm, Pi.smul_apply, smul_eq_mul, abs_mul, mul_sum]
  add_le u v := by
    simp only [l1Norm, Pi.add_apply, ← sum_add_distrib]
    exact sum_le_sum fun i _ => abs_add_le (u i) (v i)

/-- Exercise 1.2.3 (p. 14): with strictly positive weights `p`, the weighted ℓ¹ function is a
norm. The book also asks that `∑ pᵢ = 1`; that normalisation is not needed for the axioms. -/
theorem isNorm_weightedL1Norm {p : Fin n → ℝ} (hp : ∀ i, 0 < p i) :
    IsNorm (weightedL1Norm p) where
  nonneg u := sum_nonneg fun i _ => mul_nonneg (abs_nonneg (u i)) (hp i).le
  eq_zero_iff u := by
    constructor
    · intro h
      have h0 := (sum_eq_zero_iff_of_nonneg
        fun i _ => mul_nonneg (abs_nonneg (u i)) (hp i).le).1 h
      funext i
      have := h0 i (mem_univ i)
      rcases mul_eq_zero.1 this with h1 | h1
      · exact abs_eq_zero.1 h1
      · exact absurd h1 (hp i).ne'
    · rintro rfl
      simp [weightedL1Norm]
  smul α u := by
    simp only [weightedL1Norm, Pi.smul_apply, smul_eq_mul, abs_mul, mul_sum, mul_assoc]
  add_le u v := by
    simp only [weightedL1Norm, Pi.add_apply, ← sum_add_distrib]
    refine sum_le_sum fun i _ => ?_
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (abs_add_le (u i) (v i)) (hp i).le

/-- Exercise 1.2.4 (p. 14): the supremum norm is a norm. It is Mathlib's norm on `Fin n → ℝ`,
so the axioms are Mathlib's. -/
theorem isNorm_supNorm : IsNorm (supNorm (n := n)) where
  nonneg u := norm_nonneg u
  eq_zero_iff u := norm_eq_zero
  smul α u := by simp only [supNorm, norm_smul, Real.norm_eq_abs]
  add_le u v := norm_add_le u v

/-- The supremum norm is the maximum of the coordinate absolute values: `‖u‖ ≤ r ↔ ∀ i, |uᵢ| ≤ r`
for `r ≥ 0` (Exercise 1.2.4, p. 14). -/
theorem supNorm_le_iff {u : Fin n → ℝ} {r : ℝ} (hr : 0 ≤ r) : supNorm u ≤ r ↔ ∀ i, |u i| ≤ r := by
  simp only [supNorm, pi_norm_le_iff_of_nonneg hr, Real.norm_eq_abs]

/-- Each coordinate is bounded by the supremum norm, `|uᵢ| ≤ ‖u‖_∞`. -/
theorem abs_le_supNorm (u : Fin n → ℝ) (i : Fin n) : |u i| ≤ supNorm u := by
  have := norm_le_pi_norm u i
  simpa [supNorm, Real.norm_eq_abs] using this

/-- Exercise 1.2.5 (p. 14): the ℓ⁰ function is not a norm on `ℝⁿ` for `n ≥ 1`, because it fails
absolute homogeneity: `‖2u‖₀ = ‖u‖₀ ≠ 2‖u‖₀` for `u ≠ 0`. -/
theorem not_isNorm_l0Norm (hn : 0 < n) : ¬ IsNorm (l0Norm (n := n)) := by
  intro h
  set u : Fin n → ℝ := fun _ => 1 with hu
  have h1 : l0Norm u = n := by simp [l0Norm, hu]
  have h2 : l0Norm ((2 : ℝ) • u) = n := by simp [l0Norm, hu]
  have h3 := h.smul 2 u
  rw [h2, h1] at h3
  have : (n : ℝ) > 0 := by exact_mod_cast hn
  norm_num at h3
  linarith

/-- Two norms are equivalent, (1.11) p. 15: `M‖u‖ₐ ≤ ‖u‖_b ≤ N‖u‖ₐ` for some `M, N > 0`. -/
def NormEquiv {V : Type*} (Na Nb : V → ℝ) : Prop :=
  ∃ M N : ℝ, 0 < M ∧ 0 < N ∧ ∀ u, M * Na u ≤ Nb u ∧ Nb u ≤ N * Na u

/-- Exercise 1.2.6 (p. 15): equivalence of norms is reflexive. -/
theorem normEquiv_refl {V : Type*} (N : V → ℝ) : NormEquiv N N :=
  ⟨1, 1, one_pos, one_pos, fun u => ⟨by simp, by simp⟩⟩

/-- Exercise 1.2.6 (p. 15): equivalence of norms is symmetric. -/
theorem normEquiv_symm {V : Type*} {Na Nb : V → ℝ} (h : NormEquiv Na Nb) : NormEquiv Nb Na := by
  obtain ⟨M, N, hM, hN, h⟩ := h
  refine ⟨N⁻¹, M⁻¹, inv_pos.2 hN, inv_pos.2 hM, fun u => ⟨?_, ?_⟩⟩
  · rw [inv_mul_le_iff₀ hN]
    exact (h u).2
  · rw [le_inv_mul_iff₀ hM]
    exact (h u).1

/-- Exercise 1.2.6 (p. 15): equivalence of norms is transitive. -/
theorem normEquiv_trans {V : Type*} {Na Nb Nc : V → ℝ} (hab : NormEquiv Na Nb)
    (hbc : NormEquiv Nb Nc) : NormEquiv Na Nc := by
  obtain ⟨M₁, N₁, hM₁, hN₁, h₁⟩ := hab
  obtain ⟨M₂, N₂, hM₂, hN₂, h₂⟩ := hbc
  refine ⟨M₂ * M₁, N₂ * N₁, mul_pos hM₂ hM₁, mul_pos hN₂ hN₁, fun u => ⟨?_, ?_⟩⟩
  · calc M₂ * M₁ * Na u = M₂ * (M₁ * Na u) := by ring
      _ ≤ M₂ * Nb u := mul_le_mul_of_nonneg_left (h₁ u).1 hM₂.le
      _ ≤ Nc u := (h₂ u).1
  · calc Nc u ≤ N₂ * Nb u := (h₂ u).2
      _ ≤ N₂ * (N₁ * Na u) := mul_le_mul_of_nonneg_left (h₁ u).2 hN₂.le
      _ = N₂ * N₁ * Na u := by ring

/-- Exercise 1.2.6 (p. 15), in Mathlib's packaging: `NormEquiv` is an equivalence relation. -/
theorem normEquiv_equivalence (V : Type*) : Equivalence (NormEquiv (V := V)) :=
  ⟨normEquiv_refl, normEquiv_symm, normEquiv_trans⟩

/-- Exercise 1.2.7 (p. 15): if the norms are equivalent, `‖uₘ − u‖ₐ → 0` implies
`‖uₘ − u‖_b → 0`. -/
theorem tendsto_of_normEquiv {V : Type*} [AddCommGroup V] {Na Nb : V → ℝ} (hNa : ∀ v, 0 ≤ Na v)
    (h : NormEquiv Na Nb) {u : ℕ → V} {u₀ : V}
    (hlim : Filter.Tendsto (fun m => Na (u m - u₀)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun m => Nb (u m - u₀)) Filter.atTop (nhds 0) := by
  obtain ⟨M, N, hM, hN, hMN⟩ := h
  refine squeeze_zero (fun m => ?_) (fun m => (hMN (u m - u₀)).2) ?_
  · exact le_trans (mul_nonneg hM.le (hNa _)) (hMN (u m - u₀)).1
  · simpa using hlim.const_mul N

/-- Exercise 1.2.8 (p. 15): pointwise convergence and norm convergence coincide in `ℝⁿ`, here for
the supremum norm (every other norm is equivalent to it). -/
theorem tendsto_pi_iff_tendsto_supNorm {u : ℕ → Fin n → ℝ} {u₀ : Fin n → ℝ} :
    (∀ i, Filter.Tendsto (fun m => u m i) Filter.atTop (nhds (u₀ i))) ↔
      Filter.Tendsto (fun m => supNorm (u m - u₀)) Filter.atTop (nhds 0) := by
  rw [← tendsto_pi_nhds, tendsto_iff_norm_sub_tendsto_zero]
  rfl

/-- The entrywise supremum norm of a matrix, (1.13) p. 16: `‖B‖_∞ = max_{i,j} |b_{ij}|`.
This is Mathlib's elementwise matrix norm. -/
noncomputable def matrixSupNorm (B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  letI := Matrix.normedAddCommGroup (m := Fin n) (n := Fin n) (α := ℝ)
  ‖B‖

/-- The operator norm (1.12), p. 16, computed in the ℓ∞ vector norm: `‖B‖ = max_{‖u‖=1} ‖Bu‖`,
which for the supremum norm on `ℝⁿ` is the maximum absolute row sum. This is Mathlib's
`linfty` operator norm. -/
noncomputable def opNorm (B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℝ)
  ‖B‖

/-- Exercise 1.2.9 (p. 17), first part: the operator norm is submultiplicative. -/
theorem opNorm_mul (A B : Matrix (Fin n) (Fin n) ℝ) : opNorm (A * B) ≤ opNorm A * opNorm B :=
  let _ := Matrix.linftyOpNormedRing (n := Fin n) (α := ℝ)
  Matrix.linfty_opNorm_mul A B

/-- The operator norm bounds `‖Bu‖ ≤ ‖B‖ ‖u‖` in the supremum norm: the defining property of
(1.12), p. 16, used in Exercise 1.2.20. -/
theorem supNorm_mulVec_le (B : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) :
    supNorm (B.mulVec u) ≤ opNorm B * supNorm u :=
  let _ := Matrix.linftyOpNormedRing (n := Fin n) (α := ℝ)
  Matrix.linfty_opNorm_mulVec B u

/-- Exercise 1.2.9 (p. 17), second part: the entrywise supremum norm (1.13) is not
submultiplicative. For the `2 × 2` matrix of ones, `‖A‖_∞ = 1` but `‖A²‖_∞ = 2`. -/
theorem not_matrixSupNorm_submultiplicative :
    ¬ ∀ A B : Matrix (Fin 2) (Fin 2) ℝ,
      matrixSupNorm (A * B) ≤ matrixSupNorm A * matrixSupNorm B := by
  let _ := Matrix.normedAddCommGroup (m := Fin 2) (n := Fin 2) (α := ℝ)
  intro h
  set A : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun _ _ => 1 with hA
  have hA1 : matrixSupNorm A ≤ 1 := by
    change ‖A‖ ≤ 1
    rw [Matrix.norm_le_iff zero_le_one]
    intro i j
    simp [hA]
  have hAA : (2 : ℝ) ≤ matrixSupNorm (A * A) := by
    change (2 : ℝ) ≤ ‖A * A‖
    have h00 : (A * A) 0 0 = 2 := by
      simp [hA, Matrix.mul_apply]
    have := Matrix.norm_entry_le_entrywise_sup_norm (A * A) (i := 0) (j := 0)
    rw [h00, Real.norm_eq_abs, abs_two] at this
    exact this
  have hnn : 0 ≤ matrixSupNorm A := norm_nonneg A
  have := h A A
  nlinarith

end SargentStachurski.JobSearch

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The spectral radius and the Neumann series lemma

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §1.2.1.4 (pp. 16–19),
with Example 1.2.2 (p. 20), Exercise 1.2.17 (p. 22) and Exercise 1.2.20 (p. 22).

For a real `n × n` matrix `A`, the spectral radius (1.15) is
`ρ(A) = max{|λ| : λ an eigenvalue of A}`, the eigenvalues being complex. Here
`ρ(A)` is Mathlib's `spectralRadius ℂ` of the complexification of `A`, made
real-valued; `mem_spectrum_iff_eigenpair` confirms that the spectrum is the set
of eigenvalues in the book's sense.

* Theorem 1.2.1 (Neumann series lemma): `ρ(A) < 1` implies `I − A` is
  invertible and `(I − A)⁻¹ = ∑ₖ Aᵏ`.
* Lemma 1.2.2: `ρ(B)ᵏ ≤ ‖Bᵏ‖` and `‖Bᵏ‖^{1/k} → ρ(B)` (Gelfand's formula).
  The book quotes this from Bollobás; here the second part is Mathlib's
  `spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius`, transported to
  real matrices, and the first follows from Mathlib's bound on the spectral
  radius by `‖aᵏ‖^{1/k}`.
* Exercises 1.2.10–1.2.14, 1.2.17 and 1.2.20.

Matrix norms are the ℓ∞ operator norm of `Norms.lean` (`opNorm`, the maximum
absolute row sum), installed as a local instance so that `‖A‖` means `opNorm A`.
Statements about the spectral radius assume `n ≥ 1`, so that the spectrum is
nonempty and `‖I‖ = 1`.
-/

open Filter Topology Matrix

namespace SargentStachurski.JobSearch

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

/-- Under the local ℓ∞ operator norm instance, `‖A‖` is `opNorm A` of `Norms.lean`. -/
theorem opNorm_eq_norm (A : Matrix (Fin n) (Fin n) ℝ) : opNorm A = ‖A‖ := rfl

/-- The complexification of a real matrix, so that complex eigenvalues can be spoken of. -/
def complexify (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  A.map Complex.ofReal

theorem complexify_apply (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    complexify A i j = (A i j : ℂ) := rfl

/-- Complexification is a ring homomorphism, so it commutes with powers. -/
theorem complexify_pow (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    complexify (A ^ k) = complexify A ^ k :=
  map_pow (Complex.ofRealHom.mapMatrix (m := Fin n)) A k

theorem complexify_smul (α : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    complexify (α • A) = (α : ℂ) • complexify A := by
  ext i j
  simp [complexify_apply]

/-- The ℓ∞ operator norm is unchanged by complexification. -/
theorem nnnorm_complexify (A : Matrix (Fin n) (Fin n) ℝ) : ‖complexify A‖₊ = ‖A‖₊ := by
  simp only [Matrix.linfty_opNNNorm_def, complexify_apply, Complex.nnnorm_real]

theorem norm_complexify (A : Matrix (Fin n) (Fin n) ℝ) : ‖complexify A‖ = ‖A‖ :=
  congrArg NNReal.toReal (nnnorm_complexify A)

/-- The spectral radius (1.15), p. 18: the largest modulus of a (complex) eigenvalue of `A`. -/
noncomputable def specRad (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (spectralRadius ℂ (complexify A)).toReal

theorem spectralRadius_complexify_ne_top [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) :
    spectralRadius ℂ (complexify A) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.coe_ne_top (spectralRadius_le_nnnorm (complexify A))

theorem specRad_nonneg (A : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ specRad A := ENNReal.toReal_nonneg

/-- The spectrum of the complexification is the set of eigenvalues in the book's sense (p. 17):
`λ` is an eigenvalue iff `Ae = λe` for some nonzero complex vector `e`. -/
theorem mem_spectrum_iff_eigenpair (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℂ) :
    μ ∈ spectrum ℂ (complexify A) ↔ ∃ e : Fin n → ℂ, e ≠ 0 ∧ complexify A *ᵥ e = μ • e := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    ← Matrix.exists_mulVec_eq_zero_iff, Algebra.algebraMap_eq_smul_one]
  constructor
  · rintro ⟨v, hv, h⟩
    refine ⟨v, hv, ?_⟩
    rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at h
    exact h.symm
  · rintro ⟨e, he, h⟩
    refine ⟨e, he, ?_⟩
    rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero]
    exact h.symm

/-- Lemma 1.2.2 (p. 19), second part, Gelfand's formula: `‖Bᵏ‖^{1/k} → ρ(B)`. -/
theorem tendsto_norm_pow_rpow [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (fun k : ℕ => ‖A ^ k‖ ^ (1 / (k : ℝ))) atTop (𝓝 (specRad A)) := by
  have : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  have h := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius (complexify A)
  have h2 := (ENNReal.tendsto_toReal (spectralRadius_complexify_ne_top A)).comp h
  refine h2.congr fun k => ?_
  simp only [Function.comp, ← complexify_pow, norm_complexify]
  exact ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)

/-- Lemma 1.2.2 (p. 19), first part: `ρ(B)ᵏ ≤ ‖Bᵏ‖` for every `k`. -/
theorem specRad_pow_le_norm_pow [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    specRad A ^ k ≤ ‖A ^ k‖ := by
  have : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have h := spectrum.spectralRadius_le_pow_nnnorm_pow_one_div ℂ (complexify A) m
    rw [nnnorm_one, ENNReal.coe_one, ENNReal.one_rpow, mul_one] at h
    -- raise both sides to the power `m + 1`
    have hexp : (1 / ((m : ℝ) + 1)) * ((m + 1 : ℕ) : ℝ) = 1 := by
      push_cast
      field_simp
    have h' : spectralRadius ℂ (complexify A) ^ (m + 1) ≤ ‖complexify A ^ (m + 1)‖₊ := by
      have := ENNReal.rpow_le_rpow h (Nat.cast_nonneg (m + 1))
      rwa [← ENNReal.rpow_mul, hexp, ENNReal.rpow_one, ENNReal.rpow_natCast] at this
    have h'' := ENNReal.toReal_mono ENNReal.coe_ne_top h'
    rw [ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm, ← complexify_pow,
      norm_complexify] at h''
    exact h''

/-- If `ρ(A) < r` then `‖Aᵏ‖ ≤ rᵏ` for all large `k`: the quantitative content of Gelfand's
formula used throughout the section. -/
theorem eventually_norm_pow_le [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) {r : ℝ}
    (hr : specRad A < r) : ∀ᶠ k : ℕ in atTop, ‖A ^ k‖ ≤ r ^ k := by
  have hev : ∀ᶠ k : ℕ in atTop, ‖A ^ k‖ ^ (1 / (k : ℝ)) < r :=
    (tendsto_norm_pow_rpow A).eventually (gt_mem_nhds hr)
  filter_upwards [hev, eventually_gt_atTop 0] with k hk hk0
  have hnn : 0 ≤ ‖A ^ k‖ := norm_nonneg _
  have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
  have := Real.rpow_le_rpow (Real.rpow_nonneg hnn _) hk.le (Nat.cast_nonneg k)
  rwa [← Real.rpow_mul hnn, one_div_mul_cancel hkr, Real.rpow_one, Real.rpow_natCast] at this

/-- Exercise 1.2.11 (i), p. 19, the "if" direction: `ρ(A) < 1` implies `‖Aᵏ‖ → 0`. -/
theorem tendsto_norm_pow_zero [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hρ : specRad A < 1) :
    Tendsto (fun k : ℕ => ‖A ^ k‖) atTop (𝓝 0) := by
  obtain ⟨r, hr1, hr2⟩ := exists_between hρ
  have hr0 : 0 ≤ r := (specRad_nonneg A).trans hr1.le
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) (eventually_norm_pow_le A hr1)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr2)

/-- `ρ(A) < 1` implies `Aᵏ → 0`. -/
theorem tendsto_pow_zero [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hρ : specRad A < 1) :
    Tendsto (fun k : ℕ => A ^ k) atTop (𝓝 0) :=
  tendsto_zero_iff_norm_tendsto_zero.2 (tendsto_norm_pow_zero A hρ)

/-- Exercise 1.2.11 (i), p. 19, the "only if" direction: if `‖Bᵏ‖ → 0` then `ρ(B) < 1`. -/
theorem specRad_lt_one_of_tendsto [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ)
    (h : Tendsto (fun k : ℕ => ‖A ^ k‖) atTop (𝓝 0)) : specRad A < 1 := by
  by_contra hge
  have hge' : 1 ≤ specRad A := not_lt.1 hge
  have hev : ∀ᶠ k : ℕ in atTop, ‖A ^ k‖ < 1 := h.eventually (gt_mem_nhds one_pos)
  obtain ⟨k, hk⟩ := hev.exists
  have : 1 ≤ ‖A ^ k‖ := (one_le_pow₀ hge').trans (specRad_pow_le_norm_pow A k)
  linarith

/-- Exercise 1.2.11 (ii), p. 19: `ρ(B) > 1` implies `‖Bᵏ‖ → ∞`. -/
theorem tendsto_norm_pow_atTop [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hρ : 1 < specRad A) :
    Tendsto (fun k : ℕ => ‖A ^ k‖) atTop atTop :=
  tendsto_atTop_mono (specRad_pow_le_norm_pow A) (tendsto_pow_atTop_atTop_of_one_lt hρ)

/-- Exercise 1.2.10 (p. 18): `ρ(αB) = |α| ρ(B)`, proved from Gelfand's formula. -/
theorem specRad_smul [NeZero n] (α : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    specRad (α • A) = |α| * specRad A := by
  have h1 := tendsto_norm_pow_rpow (α • A)
  have h2 := (tendsto_norm_pow_rpow A).const_mul |α|
  refine tendsto_nhds_unique h1 (h2.congr' ?_)
  filter_upwards [eventually_gt_atTop 0] with k hk
  rw [smul_pow, norm_smul, Real.norm_eq_abs, abs_pow,
    Real.mul_rpow (pow_nonneg (abs_nonneg α) k) (norm_nonneg _), one_div,
    Real.pow_rpow_inv_natCast (abs_nonneg α) hk.ne']

/-- Exercise 1.2.12 (p. 19): if `A` and `B` commute then `ρ(AB) ≤ ρ(A) ρ(B)`, via Gelfand's
formula applied to `(AB)ᵏ = AᵏBᵏ`. -/
theorem specRad_mul_le [NeZero n] (A B : Matrix (Fin n) (Fin n) ℝ) (hAB : Commute A B) :
    specRad (A * B) ≤ specRad A * specRad B := by
  refine le_of_tendsto_of_tendsto' (tendsto_norm_pow_rpow (A * B))
    ((tendsto_norm_pow_rpow A).mul (tendsto_norm_pow_rpow B)) fun k => ?_
  rw [hAB.mul_pow, ← Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  exact Real.rpow_le_rpow (norm_nonneg _) (norm_mul_le _ _) (by positivity)

/-- Exercise 1.2.13 (p. 19): `ρ(A) < 1` implies `∑ₖ Aᵏ` converges. -/
theorem summable_pow [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hρ : specRad A < 1) :
    Summable fun k : ℕ => A ^ k := by
  have : CompleteSpace (Matrix (Fin n) (Fin n) ℝ) := FiniteDimensional.complete ℝ _
  obtain ⟨r, hr1, hr2⟩ := exists_between hρ
  have hr0 : 0 ≤ r := (specRad_nonneg A).trans hr1.le
  exact Summable.of_norm_bounded_eventually_nat (summable_geometric_of_lt_one hr0 hr2)
    (eventually_norm_pow_le A hr1)

/-- Exercise 1.2.14 (p. 19): when `S = ∑ₖ Aᵏ` exists, `(I − A) S = I`. The informal argument
`I + AS = S` of p. 18 made rigorous: the partial sums telescope, `(I − A) ∑_{k<K} Aᵏ = I − Aᴷ`,
and `Aᴷ → 0` because the series converges. -/
theorem one_sub_mul_tsum (A : Matrix (Fin n) (Fin n) ℝ) (hs : Summable fun k : ℕ => A ^ k) :
    (1 - A) * ∑' k : ℕ, A ^ k = 1 := by
  have h1 : Tendsto (fun K : ℕ => (1 - A) * ∑ k ∈ Finset.range K, A ^ k) atTop
      (𝓝 ((1 - A) * ∑' k : ℕ, A ^ k)) :=
    hs.hasSum.tendsto_sum_nat.const_mul (1 - A)
  have h2 : Tendsto (fun K : ℕ => (1 - A) * ∑ k ∈ Finset.range K, A ^ k) atTop (𝓝 1) := by
    simp_rw [mul_neg_geom_sum]
    simpa using tendsto_const_nhds.sub hs.tendsto_atTop_zero
  exact tendsto_nhds_unique h1 h2

/-- Exercise 1.2.14 (p. 19), the other side: `S (I − A) = I`. -/
theorem tsum_mul_one_sub (A : Matrix (Fin n) (Fin n) ℝ) (hs : Summable fun k : ℕ => A ^ k) :
    (∑' k : ℕ, A ^ k) * (1 - A) = 1 := by
  have h1 : Tendsto (fun K : ℕ => (∑ k ∈ Finset.range K, A ^ k) * (1 - A)) atTop
      (𝓝 ((∑' k : ℕ, A ^ k) * (1 - A))) :=
    hs.hasSum.tendsto_sum_nat.mul_const (1 - A)
  have h2 : Tendsto (fun K : ℕ => (∑ k ∈ Finset.range K, A ^ k) * (1 - A)) atTop (𝓝 1) := by
    simp_rw [geom_sum_mul_neg]
    simpa using tendsto_const_nhds.sub hs.tendsto_atTop_zero
  exact tendsto_nhds_unique h1 h2

/-- Exercise 1.2.14 (p. 19), conclusion: when `∑ₖ Aᵏ` exists, `I − A` is invertible with
inverse `∑ₖ Aᵏ`. -/
theorem isUnit_one_sub_of_summable (A : Matrix (Fin n) (Fin n) ℝ)
    (hs : Summable fun k : ℕ => A ^ k) : IsUnit (1 - A) :=
  ⟨⟨1 - A, ∑' k : ℕ, A ^ k, one_sub_mul_tsum A hs, tsum_mul_one_sub A hs⟩, rfl⟩

theorem inv_one_sub_of_summable (A : Matrix (Fin n) (Fin n) ℝ)
    (hs : Summable fun k : ℕ => A ^ k) : (1 - A)⁻¹ = ∑' k : ℕ, A ^ k :=
  Matrix.inv_eq_right_inv (one_sub_mul_tsum A hs)

/-- Theorem 1.2.1 (Neumann series lemma, p. 18): if `ρ(A) < 1` then `I − A` is nonsingular and
`(I − A)⁻¹ = ∑ₖ Aᵏ`. -/
theorem neumann_series [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hρ : specRad A < 1) :
    IsUnit (1 - A) ∧ (1 - A)⁻¹ = ∑' k : ℕ, A ^ k :=
  ⟨isUnit_one_sub_of_summable A (summable_pow A hρ),
    inv_one_sub_of_summable A (summable_pow A hρ)⟩

/-- `(I − A)⁻¹ (I − A) = I` when `ρ(A) < 1`. -/
theorem inv_one_sub_mul [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hρ : specRad A < 1) :
    (1 - A)⁻¹ * (1 - A) = 1 := by
  rw [(neumann_series A hρ).2]
  exact tsum_mul_one_sub A (summable_pow A hρ)

/-- `(I − A)(I − A)⁻¹ = I` when `ρ(A) < 1`. -/
theorem mul_inv_one_sub [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hρ : specRad A < 1) :
    (1 - A) * (1 - A)⁻¹ = 1 := by
  rw [(neumann_series A hρ).2]
  exact one_sub_mul_tsum A (summable_pow A hρ)

/-- The affine map `Tu = Au + b` of Example 1.2.2 (p. 20). -/
def affine (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (u : Fin n → ℝ) : Fin n → ℝ :=
  A *ᵥ u + b

/-- Example 1.2.2 (p. 20): `u` is a fixed point of `Tu = Au + b` iff `u = Au + b`. -/
theorem isFixedPt_affine_iff (A : Matrix (Fin n) (Fin n) ℝ) (b u : Fin n → ℝ) :
    Function.IsFixedPt (affine A b) u ↔ u = A *ᵥ u + b :=
  ⟨fun h => h.eq.symm, fun h => h.symm⟩

/-- The system `u = Au + b` (p. 18) has the solution `u* = (I − A)⁻¹ b` when `ρ(A) < 1`. -/
theorem isFixedPt_affine_inv [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hρ : specRad A < 1)
    (b : Fin n → ℝ) : Function.IsFixedPt (affine A b) ((1 - A)⁻¹ *ᵥ b) := by
  change A *ᵥ ((1 - A)⁻¹ *ᵥ b) + b = (1 - A)⁻¹ *ᵥ b
  have h2 := mul_inv_one_sub A hρ
  have hAB : A * (1 - A)⁻¹ = (1 - A)⁻¹ - 1 := by
    have h3 : (1 - A) * (1 - A)⁻¹ = (1 - A)⁻¹ - A * (1 - A)⁻¹ := by rw [sub_mul, one_mul]
    rw [h3] at h2
    calc A * (1 - A)⁻¹ = (1 - A)⁻¹ - ((1 - A)⁻¹ - A * (1 - A)⁻¹) := by abel
      _ = (1 - A)⁻¹ - 1 := by rw [h2]
  rw [mulVec_mulVec, hAB, sub_mulVec, one_mulVec]
  abel

/-- Theorem 1.2.1's corollary (p. 18) and Example 1.2.2: when `ρ(A) < 1`, `u = Au + b` has
exactly one solution, `u* = (I − A)⁻¹ b`. -/
theorem affine_fixedPt_unique [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hρ : specRad A < 1)
    (b u : Fin n → ℝ) (hu : Function.IsFixedPt (affine A b) u) : u = (1 - A)⁻¹ *ᵥ b := by
  have hu' : A *ᵥ u + b = u := hu.eq
  have h : (1 - A) *ᵥ u = b := by
    rw [sub_mulVec, one_mulVec]
    calc u - A *ᵥ u = (A *ᵥ u + b) - A *ᵥ u := by rw [hu']
      _ = b := by abel
  rw [← h, mulVec_mulVec, inv_one_sub_mul A hρ, one_mulVec]

/-- Exercise 1.2.17 (p. 22), the formula (1.16): `Tᵏu = Aᵏu + Aᵏ⁻¹b + ⋯ + Ab + b`. -/
theorem affine_iterate (A : Matrix (Fin n) (Fin n) ℝ) (b u : Fin n → ℝ) (k : ℕ) :
    (affine A b)^[k] u = A ^ k *ᵥ u + ∑ i ∈ Finset.range k, A ^ i *ᵥ b := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Finset.sum_range_succ']
    simp only [affine, mulVec_add, mulVec_mulVec, pow_zero, one_mulVec, Matrix.mulVec_sum,
      ← pow_succ']
    abel

/-- Exercise 1.2.17 (p. 22), continued: the iterates converge to `u* = (I − A)⁻¹ b`, because
`Tᵏu − u* = Aᵏ(u − u*)` and `Aᵏ → 0`. -/
theorem tendsto_affine_iterate [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hρ : specRad A < 1)
    (b u : Fin n → ℝ) :
    Tendsto (fun k : ℕ => (affine A b)^[k] u) atTop (𝓝 ((1 - A)⁻¹ *ᵥ b)) := by
  set u' := (1 - A)⁻¹ *ᵥ b with hu'
  have hfix : Function.IsFixedPt (affine A b) u' := isFixedPt_affine_inv A hρ b
  have hdiff : ∀ k : ℕ, (affine A b)^[k] u - u' = A ^ k *ᵥ (u - u') := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', pow_succ', ← mulVec_mulVec, ← ih]
      conv_lhs => rw [← hfix.eq]
      simp only [affine, mulVec_sub]
      abel
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [dist_eq_norm, hdiff]
  refine squeeze_zero (fun _ => norm_nonneg _)
    (fun k => Matrix.linfty_opNorm_mulVec (A ^ k) (u - u')) ?_
  simpa using (tendsto_norm_pow_zero A hρ).mul_const ‖u - u'‖

/-- Exercise 1.2.17 (p. 22), conclusion: `Tu = Au + b` is globally stable on `ℝⁿ` whenever
`ρ(A) < 1`. -/
theorem globallyStable_affine [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hρ : specRad A < 1)
    (b : Fin n → ℝ) : GloballyStable (affine A b) :=
  globallyStable_of_tendsto (isFixedPt_affine_inv A hρ b) (tendsto_affine_iterate A hρ b)

/-- Exercise 1.2.20 (p. 22): if `‖A‖ < 1` then `Tu = Au + b` is a contraction of modulus `‖A‖`
on `ℝⁿ`, in the supremum norm. -/
theorem isContractionOn_affine (A : Matrix (Fin n) (Fin n) ℝ) (hA : ‖A‖ < 1) (b : Fin n → ℝ) :
    IsContractionOn (affine A b) Set.univ ‖A‖ := by
  refine ⟨Set.mapsTo_univ _ _, norm_nonneg A, hA, fun u _ v _ => ?_⟩
  simp only [affine]
  rw [add_sub_add_right_eq_sub, ← mulVec_sub]
  exact Matrix.linfty_opNorm_mulVec A (u - v)

/-- The scalar case (1.14), p. 17: `|a| < 1` gives `u* = b/(1 − a) = ∑ₖ aᵏ b`. -/
theorem scalar_neumann {a b : ℝ} (ha : |a| < 1) :
    ∑' k : ℕ, a ^ k * b = b / (1 - a) ∧ b / (1 - a) = a * (b / (1 - a)) + b := by
  have h1 : (1 : ℝ) - a ≠ 0 := by
    have := abs_lt.1 ha
    linarith
  constructor
  · rw [tsum_mul_right, tsum_geometric_of_abs_lt_one ha]
    ring
  · field_simp
    ring

end SargentStachurski.JobSearch

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Successive approximation and the Solow–Swan example

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §1.2.3 (pp. 24–28).

Successive approximation (p. 24) computes the fixed point of a globally
stable map by iterating it; the convergence claim *is* global stability, so
the theorem here only unpacks the definition. The substance of the section is
the Solow–Swan example (1.19), `k' = s f(k) + (1 − δ)k` with `f(k) = A kᵅ`:
Exercise 1.2.25 shows the map `g` is a self-map of `U = (0, ∞)` but *not* a
contraction there (its slope is unbounded near `0`), and Exercise 1.2.26 shows
it is nonetheless globally stable, with fixed point `k* = (sA/δ)^{1/(1−α)}`,
because `g` moves every `k` monotonically towards `k*`.
-/

open Filter Topology Function Set

namespace SargentStachurski.JobSearch

/-- Successive approximation (p. 24): under global stability the iterates converge to the fixed
point from any starting point. -/
theorem GloballyStable.tendsto_iterate {U : Type*} [TopologicalSpace U] {T : U → U}
    (h : GloballyStable T) {u' : U} (hu' : IsFixedPt T u') (u : U) :
    Tendsto (fun k : ℕ => T^[k] u) atTop (𝓝 u') := by
  obtain ⟨u₀, -, huniq, hlim⟩ := h
  rw [huniq u' hu']
  exact hlim u

/-- The Solow–Swan model with Cobb–Douglas production, Exercise 1.2.25 (p. 27):
`f(k) = A kᵅ`, saving rate `s`, depreciation `δ`. -/
structure Solow where
  A : ℝ
  s : ℝ
  δ : ℝ
  α : ℝ
  A_pos : 0 < A
  s_pos : 0 < s
  δ_pos : 0 < δ
  δ_lt_one : δ < 1
  α_pos : 0 < α
  α_lt_one : α < 1

namespace Solow

variable (m : Solow)

/-- The Solow–Swan map (1.19), p. 27: `g(k) = s A kᵅ + (1 − δ)k`. -/
noncomputable def g (k : ℝ) : ℝ := m.s * m.A * k ^ m.α + (1 - m.δ) * k

/-- The steady state of Exercise 1.2.26 (p. 27): `k* = (sA/δ)^{1/(1−α)}`. -/
noncomputable def kstar : ℝ := (m.s * m.A / m.δ) ^ (1 / (1 - m.α))

theorem one_sub_α_pos : 0 < 1 - m.α := by linarith [m.α_lt_one]

theorem one_sub_δ_pos : 0 < 1 - m.δ := by linarith [m.δ_lt_one]

theorem sA_pos : 0 < m.s * m.A := mul_pos m.s_pos m.A_pos

theorem kstar_pos : 0 < m.kstar :=
  Real.rpow_pos_of_pos (div_pos m.sA_pos m.δ_pos) _

/-- `δ (sA/δ) = sA`. -/
theorem δ_mul_div : m.δ * (m.s * m.A / m.δ) = m.s * m.A := by
  have hδ := m.δ_pos.ne'
  rw [mul_div_assoc', mul_comm m.δ, mul_div_assoc, div_self hδ, mul_one]

/-- `(k*)^{1−α} = sA/δ`. -/
theorem kstar_rpow : m.kstar ^ (1 - m.α) = m.s * m.A / m.δ := by
  unfold kstar
  rw [← Real.rpow_mul (div_pos m.sA_pos m.δ_pos).le, one_div_mul_cancel m.one_sub_α_pos.ne',
    Real.rpow_one]

/-- `kᵅ k^{1−α} = k` for `k > 0`. -/
theorem rpow_mul_rpow {k : ℝ} (hk : 0 < k) : k ^ m.α * k ^ (1 - m.α) = k := by
  rw [← Real.rpow_add hk]
  simp

/-- Exercise 1.2.25 (p. 27), first part: `g` sends `U = (0, ∞)` into itself. -/
theorem g_pos {k : ℝ} (hk : 0 < k) : 0 < m.g k := by
  unfold g
  have h1 := mul_pos m.sA_pos (Real.rpow_pos_of_pos hk m.α)
  have h2 := mul_pos m.one_sub_δ_pos hk
  linarith

/-- `g` maps `(0, ∞)` to itself, as a `MapsTo`. -/
theorem mapsTo_g : MapsTo m.g (Ioi 0) (Ioi 0) := fun _ hk => m.g_pos hk

/-- `g` is strictly increasing on `(0, ∞)`. -/
theorem g_strictMonoOn : StrictMonoOn m.g (Ioi 0) := by
  intro x hx y hy hxy
  unfold g
  have h1 : x ^ m.α < y ^ m.α := Real.rpow_lt_rpow (le_of_lt hx) hxy m.α_pos
  have h2 := m.one_sub_δ_pos
  have h3 := m.sA_pos
  nlinarith

/-- `g` is continuous. -/
theorem continuous_g : Continuous m.g := by
  unfold g
  have := Real.continuous_rpow_const m.α_pos.le
  fun_prop

/-- Exercise 1.2.25 (p. 27), second part: `g` is not a contraction on `(0, ∞)` for any modulus.
The book's hint is the derivative `g'(k) → ∞` as `k → 0`; here the chord from `k/2` to `k` is
compared with its length directly. -/
theorem not_isContractionOn_g (L : ℝ) : ¬ IsContractionOn m.g (Ioi 0) L := by
  intro h
  -- the contraction inequality on the pair `(x, x/2)` gives `sA xᵅ (1 − 2^{−α}) < δ x / 2`
  have key : ∀ x : ℝ, 0 < x → m.s * m.A * x ^ m.α * (1 - (2 : ℝ) ^ (-m.α)) < m.δ * x / 2 := by
    intro x hx
    have hx2 : 0 < x / 2 := by positivity
    have hb := h.norm_sub_le x hx (x / 2) hx2
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hb
    have hmono : m.g (x / 2) < m.g x := m.g_strictMonoOn hx2 hx (by linarith)
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)] at hb
    have hL : L * (x - x / 2) < x - x / 2 := by
      have := h.lt_one
      nlinarith
    have hhalf : (x / 2) ^ m.α = x ^ m.α * (2 : ℝ) ^ (-m.α) := by
      rw [Real.div_rpow hx.le (by norm_num), Real.rpow_neg (by norm_num), div_eq_mul_inv]
    unfold g at hb hmono
    rw [hhalf] at hb
    nlinarith [hb, hL]
  have h2 : 0 < 1 - (2 : ℝ) ^ (-m.α) := by
    have : (2 : ℝ) ^ (-m.α) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [m.α_pos])
    linarith
  -- choose `x` with `x^{1−α} = 2 sA (1 − 2^{−α}) / δ`, which turns the strict inequality into
  -- an equality
  set c : ℝ := 2 * (m.s * m.A) * (1 - (2 : ℝ) ^ (-m.α)) / m.δ with hc
  have hcpos : 0 < c := by have := m.sA_pos; have := m.δ_pos; positivity
  have hcδ : c * m.δ = 2 * (m.s * m.A) * (1 - (2 : ℝ) ^ (-m.α)) := by
    rw [hc]
    exact div_mul_cancel₀ _ m.δ_pos.ne'
  set x : ℝ := c ^ (1 / (1 - m.α)) with hxdef
  have hxpos : 0 < x := Real.rpow_pos_of_pos hcpos _
  have hxc : x ^ (1 - m.α) = c := by
    rw [hxdef, ← Real.rpow_mul hcpos.le, one_div_mul_cancel m.one_sub_α_pos.ne', Real.rpow_one]
  have hx_eq : x = x ^ m.α * c := by
    rw [← hxc]
    exact (m.rpow_mul_rpow hxpos).symm
  have hk := key x hxpos
  -- `δ x / 2 = δ xᵅ c / 2 = sA xᵅ (1 − 2^{−α})`, so the strict inequality reads `t < t`
  have e : m.δ * x / 2 = m.s * m.A * x ^ m.α * (1 - (2 : ℝ) ^ (-m.α)) := by
    calc m.δ * x / 2 = m.δ * (x ^ m.α * c) / 2 := by rw [← hx_eq]
      _ = m.s * m.A * x ^ m.α * (1 - (2 : ℝ) ^ (-m.α)) := by
        linear_combination (x ^ m.α / 2) * hcδ
  linarith

/-- Exercise 1.2.26 (p. 27): `k*` is a fixed point of `g`. -/
theorem isFixedPt_kstar : IsFixedPt m.g m.kstar := by
  change m.g m.kstar = m.kstar
  have h2 : m.δ * m.kstar ^ (1 - m.α) = m.s * m.A := by
    rw [m.kstar_rpow]
    exact m.δ_mul_div
  have h1 : m.s * m.A * m.kstar ^ m.α = m.δ * m.kstar := by
    calc m.s * m.A * m.kstar ^ m.α = m.kstar ^ m.α * (m.δ * m.kstar ^ (1 - m.α)) := by
          rw [h2]; ring
      _ = m.δ * (m.kstar ^ m.α * m.kstar ^ (1 - m.α)) := by ring
      _ = m.δ * m.kstar := by rw [m.rpow_mul_rpow m.kstar_pos]
  unfold g
  rw [h1]
  ring

/-- The sign of `g(k) − k` on `(0, ∞)`: `g(k) − k = kᵅ (sA − δ k^{1−α})`. -/
theorem g_sub_self {k : ℝ} (hk : 0 < k) :
    m.g k - k = k ^ m.α * (m.s * m.A - m.δ * k ^ (1 - m.α)) := by
  unfold g
  calc m.s * m.A * k ^ m.α + (1 - m.δ) * k - k
      = m.s * m.A * k ^ m.α - m.δ * (k ^ m.α * k ^ (1 - m.α)) := by
        rw [m.rpow_mul_rpow hk]; ring
    _ = k ^ m.α * (m.s * m.A - m.δ * k ^ (1 - m.α)) := by ring

/-- Exercise 1.2.26 (i), p. 27: if `0 < k ≤ k*` then `k ≤ g(k) ≤ k*`. -/
theorem le_g_le_of_le_kstar {k : ℝ} (hk : 0 < k) (hle : k ≤ m.kstar) :
    k ≤ m.g k ∧ m.g k ≤ m.kstar := by
  constructor
  · have h1 : k ^ (1 - m.α) ≤ m.kstar ^ (1 - m.α) :=
      Real.rpow_le_rpow hk.le hle m.one_sub_α_pos.le
    rw [m.kstar_rpow] at h1
    have h2 : m.δ * k ^ (1 - m.α) ≤ m.s * m.A := by
      calc m.δ * k ^ (1 - m.α) ≤ m.δ * (m.s * m.A / m.δ) :=
            mul_le_mul_of_nonneg_left h1 m.δ_pos.le
        _ = m.s * m.A := m.δ_mul_div
    have h3 : 0 ≤ k ^ m.α := (Real.rpow_pos_of_pos hk _).le
    have := m.g_sub_self hk
    nlinarith
  · calc m.g k ≤ m.g m.kstar := m.g_strictMonoOn.monotoneOn hk m.kstar_pos hle
      _ = m.kstar := m.isFixedPt_kstar

/-- Exercise 1.2.26 (ii), p. 27: if `k* ≤ k` then `k* ≤ g(k) ≤ k`. -/
theorem kstar_le_g_le_of_kstar_le {k : ℝ} (hle : m.kstar ≤ k) :
    m.kstar ≤ m.g k ∧ m.g k ≤ k := by
  have hk : 0 < k := lt_of_lt_of_le m.kstar_pos hle
  constructor
  · calc m.kstar = m.g m.kstar := m.isFixedPt_kstar.eq.symm
      _ ≤ m.g k := m.g_strictMonoOn.monotoneOn m.kstar_pos hk hle
  · have h1 : m.kstar ^ (1 - m.α) ≤ k ^ (1 - m.α) :=
      Real.rpow_le_rpow m.kstar_pos.le hle m.one_sub_α_pos.le
    rw [m.kstar_rpow] at h1
    have h2 : m.s * m.A ≤ m.δ * k ^ (1 - m.α) := by
      calc m.s * m.A = m.δ * (m.s * m.A / m.δ) := m.δ_mul_div.symm
        _ ≤ m.δ * k ^ (1 - m.α) := mul_le_mul_of_nonneg_left h1 m.δ_pos.le
    have h3 : 0 ≤ k ^ m.α := (Real.rpow_pos_of_pos hk _).le
    have := m.g_sub_self hk
    nlinarith

/-- Exercise 1.2.26 (p. 27): `k*` is the unique fixed point of `g` in `(0, ∞)`. -/
theorem eq_kstar_of_isFixedPt {k : ℝ} (hk : 0 < k) (hfix : IsFixedPt m.g k) : k = m.kstar := by
  have h0 := m.g_sub_self hk
  rw [hfix.eq, sub_self] at h0
  have h3 : 0 < k ^ m.α := Real.rpow_pos_of_pos hk _
  have h4 : m.δ * k ^ (1 - m.α) = m.s * m.A := by
    have := mul_eq_zero.1 h0.symm
    rcases this with h | h
    · exact absurd h h3.ne'
    · linarith
  rcases lt_trichotomy k m.kstar with hlt | heq | hgt
  · exfalso
    have h1 : k ^ (1 - m.α) < m.kstar ^ (1 - m.α) :=
      Real.rpow_lt_rpow hk.le hlt m.one_sub_α_pos
    rw [m.kstar_rpow] at h1
    have h2 : m.δ * k ^ (1 - m.α) < m.s * m.A := by
      calc m.δ * k ^ (1 - m.α) < m.δ * (m.s * m.A / m.δ) :=
            mul_lt_mul_of_pos_left h1 m.δ_pos
        _ = m.s * m.A := m.δ_mul_div
    linarith
  · exact heq
  · exfalso
    have h1 : m.kstar ^ (1 - m.α) < k ^ (1 - m.α) :=
      Real.rpow_lt_rpow m.kstar_pos.le hgt m.one_sub_α_pos
    rw [m.kstar_rpow] at h1
    have h2 : m.s * m.A < m.δ * k ^ (1 - m.α) := by
      calc m.s * m.A = m.δ * (m.s * m.A / m.δ) := m.δ_mul_div.symm
        _ < m.δ * k ^ (1 - m.α) := mul_lt_mul_of_pos_left h1 m.δ_pos
    linarith

/-- The iterates stay positive. -/
theorem iterate_g_pos {k : ℝ} (hk : 0 < k) (j : ℕ) : 0 < m.g^[j] k :=
  iterate_mem_of_mapsTo m.mapsTo_g hk j

/-- From `0 < k₀ ≤ k*` the iterates stay below `k*`. -/
theorem iterate_le_kstar {k : ℝ} (hk : 0 < k) (hle : k ≤ m.kstar) (j : ℕ) :
    m.g^[j] k ≤ m.kstar := by
  induction j with
  | zero => simpa using hle
  | succ j ih =>
    rw [iterate_succ_apply']
    exact (m.le_g_le_of_le_kstar (m.iterate_g_pos hk j) ih).2

/-- From `k* ≤ k₀` the iterates stay above `k*`. -/
theorem kstar_le_iterate {k : ℝ} (hle : m.kstar ≤ k) (j : ℕ) : m.kstar ≤ m.g^[j] k := by
  induction j with
  | zero => simpa using hle
  | succ j ih =>
    rw [iterate_succ_apply']
    exact (m.kstar_le_g_le_of_kstar_le ih).1

/-- Exercise 1.2.26 (p. 27), conclusion: from every `k₀ > 0` the Solow–Swan iterates converge to
`k*`. The sequence is monotone and bounded by (i) or (ii), so it converges; its limit is a
positive fixed point by continuity (Exercise 1.2.16), hence `k*`. -/
theorem tendsto_iterate_kstar {k : ℝ} (hk : 0 < k) :
    Tendsto (fun j : ℕ => m.g^[j] k) atTop (𝓝 m.kstar) := by
  rcases le_total k m.kstar with hle | hle
  · -- increasing, bounded above by `k*`
    have hmono : Monotone fun j : ℕ => m.g^[j] k := by
      refine monotone_nat_of_le_succ fun j => ?_
      rw [iterate_succ_apply']
      exact (m.le_g_le_of_le_kstar (m.iterate_g_pos hk j) (m.iterate_le_kstar hk hle j)).1
    have hbdd : BddAbove (range fun j : ℕ => m.g^[j] k) :=
      ⟨m.kstar, by rintro _ ⟨j, rfl⟩; exact m.iterate_le_kstar hk hle j⟩
    have hlim := tendsto_atTop_ciSup hmono hbdd
    have hℓpos : 0 < ⨆ j : ℕ, m.g^[j] k :=
      lt_of_lt_of_le hk (by simpa using le_ciSup hbdd 0)
    have hfix : IsFixedPt m.g (⨆ j : ℕ, m.g^[j] k) :=
      isFixedPt_of_tendsto_iterate hlim m.continuous_g.continuousAt
    rwa [m.eq_kstar_of_isFixedPt hℓpos hfix] at hlim
  · -- decreasing, bounded below by `k*`
    have hanti : Antitone fun j : ℕ => m.g^[j] k := by
      refine antitone_nat_of_succ_le fun j => ?_
      rw [iterate_succ_apply']
      exact (m.kstar_le_g_le_of_kstar_le (m.kstar_le_iterate hle j)).2
    have hbdd : BddBelow (range fun j : ℕ => m.g^[j] k) :=
      ⟨m.kstar, by rintro _ ⟨j, rfl⟩; exact m.kstar_le_iterate hle j⟩
    have hlim := tendsto_atTop_ciInf hanti hbdd
    have hℓpos : 0 < ⨅ j : ℕ, m.g^[j] k :=
      lt_of_lt_of_le m.kstar_pos (le_ciInf fun j => m.kstar_le_iterate hle j)
    have hfix : IsFixedPt m.g (⨅ j : ℕ, m.g^[j] k) :=
      isFixedPt_of_tendsto_iterate hlim m.continuous_g.continuousAt
    rwa [m.eq_kstar_of_isFixedPt hℓpos hfix] at hlim

/-- Exercise 1.2.26 (p. 27): `g` is globally stable on `U = (0, ∞)`, as a self-map of the
subtype. The "why?" of the exercise: monotone bounded sequences converge, limits of iterates
of a continuous map are fixed points, and the fixed point is unique. -/
theorem globallyStable_g : GloballyStable (m.mapsTo_g.restrict m.g (Ioi 0) (Ioi 0)) := by
  have hiter : ∀ (u : Ioi (0 : ℝ)) (j : ℕ),
      ((m.mapsTo_g.restrict m.g (Ioi 0) (Ioi 0))^[j] u : ℝ) = m.g^[j] u := by
    intro u j
    rw [MapsTo.iterate_restrict]
    rfl
  refine globallyStable_of_tendsto (u' := ⟨m.kstar, m.kstar_pos⟩) ?_ fun u => ?_
  · exact Subtype.ext (by simpa [MapsTo.val_restrict_apply] using m.isFixedPt_kstar.eq)
  · rw [tendsto_subtype_rng]
    simp only [hiter]
    exact m.tendsto_iterate_kstar u.2

end Solow

end SargentStachurski.JobSearch

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The finite-dimensional function space `ℝ^X`

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §1.2.4.2–§1.2.4.3
(pp. 30–32): Lemma 1.2.4 identifying `ℝ^X` with `ℝⁿ`, distributions on a
finite set, expectations as inner products, Exercise 1.2.27 on maximising a
linear functional over the simplex, and cumulative distribution functions and
quantiles on a finite subset of the line with Example 1.2.5 and Exercise 1.2.28.
-/

open Finset

namespace SargentStachurski.JobSearch

variable {X : Type*} [Fintype X]

/-- Lemma 1.2.4 (p. 30): `ℝ^X ∋ u ↔ (u(x₁), …, u(xₙ)) ∈ ℝⁿ` is a one-to-one correspondence,
indeed a linear equivalence, once `X` is enumerated as `x₁, …, xₙ`. -/
noncomputable def toVector : (X → ℝ) ≃ₗ[ℝ] (Fin (Fintype.card X) → ℝ) :=
  LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin X).symm

theorem toVector_apply (u : X → ℝ) (i : Fin (Fintype.card X)) :
    toVector u i = u ((Fintype.equivFin X).symm i) := rfl

theorem toVector_symm_apply (v : Fin (Fintype.card X) → ℝ) (x : X) :
    toVector.symm v x = v (Fintype.equivFin X x) := rfl

/-- The supremum norm extends to `ℝ^X` through the identification (p. 30): `‖u‖ = ‖(u(xᵢ))ᵢ‖`. -/
theorem norm_toVector (u : X → ℝ) : ‖toVector u‖ = ‖u‖ := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro i
    rw [toVector_apply]
    exact norm_le_pi_norm u _
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro x
    have := norm_le_pi_norm (toVector u) (Fintype.equivFin X x)
    rwa [toVector_apply, Equiv.symm_apply_apply] at this

/-- A distribution on the finite set `X` (p. 31): `φ ∈ ℝ^X₊` with `∑ φ(x) = 1`. -/
structure IsDistribution (φ : X → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ φ x
  sum_eq_one : ∑ x, φ x = 1

/-- `φ` is supported on `S` (p. 31): `φ(x) > 0` implies `x ∈ S`. -/
def SupportedOn (φ : X → ℝ) (S : Set X) : Prop := ∀ x, 0 < φ x → x ∈ S

/-- The expectation `E h(X) = ∑ h(x) φ(x) = ⟨h, φ⟩` (p. 31). -/
def expectation (h φ : X → ℝ) : ℝ := ∑ x, h x * φ x

/-- The point mass at `x₀` is a distribution. -/
theorem isDistribution_pointMass [DecidableEq X] (x₀ : X) :
    IsDistribution (fun x => if x = x₀ then (1 : ℝ) else 0) where
  nonneg x := by split_ifs <;> norm_num
  sum_eq_one := by simp

/-- The expectation under a point mass is the value at the point. -/
theorem expectation_pointMass [DecidableEq X] (h : X → ℝ) (x₀ : X) :
    expectation h (fun x => if x = x₀ then (1 : ℝ) else 0) = h x₀ := by
  simp [expectation]

/-- An expectation is bounded by a pointwise bound. -/
theorem expectation_le {h φ : X → ℝ} (hφ : IsDistribution φ) {M : ℝ} (hM : ∀ x, h x ≤ M) :
    expectation h φ ≤ M := by
  calc expectation h φ ≤ ∑ x, M * φ x :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (hM x) (hφ.nonneg x)
    _ = M := by rw [← Finset.mul_sum, hφ.sum_eq_one, mul_one]

/-- A distribution supported where `h` attains its maximum `M` has expectation `M`. -/
theorem expectation_eq_of_supportedOn {h φ : X → ℝ} (hφ : IsDistribution φ) {M : ℝ}
    (hsupp : SupportedOn φ {x | h x = M}) : expectation h φ = M := by
  calc expectation h φ = ∑ x, M * φ x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rcases (hφ.nonneg x).lt_or_eq with hpos | hzero
        · rw [hsupp x hpos]
        · rw [← hzero]
          simp
    _ = M := by rw [← Finset.mul_sum, hφ.sum_eq_one, mul_one]

/-- A distribution not supported where `h` attains its maximum `M` has expectation below `M`. -/
theorem expectation_lt_of_not_supportedOn {h φ : X → ℝ} (hφ : IsDistribution φ) {M : ℝ}
    (hM : ∀ x, h x ≤ M) (hsupp : ¬ SupportedOn φ {x | h x = M}) : expectation h φ < M := by
  simp only [SupportedOn, Set.mem_ofPred_eq, not_forall] at hsupp
  obtain ⟨x₁, hpos, hne⟩ := hsupp
  have hlt : h x₁ < M := lt_of_le_of_ne (hM x₁) hne
  calc expectation h φ < ∑ x, M * φ x := by
        refine Finset.sum_lt_sum (fun x _ => mul_le_mul_of_nonneg_right (hM x) (hφ.nonneg x))
          ⟨x₁, Finset.mem_univ _, ?_⟩
        exact mul_lt_mul_of_pos_right hlt hpos
    _ = M := by rw [← Finset.mul_sum, hφ.sum_eq_one, mul_one]

/-- Exercise 1.2.27 (p. 31): `φ*` maximises `⟨h, φ⟩` over `D(X)` iff `φ*` is supported on
`argmax_x h(x)`. -/
theorem expectation_maximiser_iff [Nonempty X] (h : X → ℝ) {φ' : X → ℝ}
    (hφ' : IsDistribution φ') :
    (∀ φ, IsDistribution φ → expectation h φ ≤ expectation h φ') ↔
      SupportedOn φ' {x | ∀ y, h y ≤ h x} := by
  classical
  obtain ⟨x₀, -, hx₀⟩ := Finset.exists_max_image univ h Finset.univ_nonempty
  have hM : ∀ x, h x ≤ h x₀ := fun x => hx₀ x (Finset.mem_univ x)
  have hset : {x | ∀ y, h y ≤ h x} = {x | h x = h x₀} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hx
      exact le_antisymm (hM x) (hx x₀)
    · intro hx y
      rw [hx]
      exact hM y
  rw [hset]
  constructor
  · intro hmax
    by_contra hnot
    have h1 := expectation_lt_of_not_supportedOn hφ' hM hnot
    have h2 := hmax _ (isDistribution_pointMass x₀)
    rw [expectation_pointMass] at h2
    linarith
  · intro hsupp φ hφ
    rw [expectation_eq_of_supportedOn hφ' hsupp]
    exact expectation_le hφ hM

/-! ### Distributions on a finite subset of the line, CDFs and quantiles (p. 32) -/

/-- A distribution on the finite set `X ⊂ ℝ`, as a function on `ℝ`: nonnegative on `X` and
summing to one over `X`. -/
structure IsDistributionOn (X : Finset ℝ) (φ : ℝ → ℝ) : Prop where
  nonneg : ∀ x ∈ X, 0 ≤ φ x
  sum_eq_one : ∑ x ∈ X, φ x = 1

/-- The cumulative distribution function `Φ(x) = P{X ≤ x} = ∑ 1{x' ≤ x} φ(x')` (p. 32). -/
noncomputable def cdf (X : Finset ℝ) (φ : ℝ → ℝ) (x : ℝ) : ℝ := ∑ x' ∈ X, if x' ≤ x then φ x' else 0

/-- The CDF is monotone. -/
theorem cdf_mono {X : Finset ℝ} {φ : ℝ → ℝ} (hφ : IsDistributionOn X φ) : Monotone (cdf X φ) := by
  intro x y hxy
  refine Finset.sum_le_sum fun x' hx' => ?_
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (h1.trans hxy) h2
  · exact hφ.nonneg x' hx'
  · exact le_rfl

/-- The CDF equals one at the largest point of `X`. -/
theorem cdf_max' {X : Finset ℝ} {φ : ℝ → ℝ} (hX : X.Nonempty) (hφ : IsDistributionOn X φ) :
    cdf X φ (X.max' hX) = 1 := by
  rw [cdf, ← hφ.sum_eq_one]
  exact Finset.sum_congr rfl fun x hx => by simp [Finset.le_max' X x hx]

/-- The set `{x ∈ X : Φ(x) ≥ τ}` whose minimum is the `τ`-quantile. -/
noncomputable def quantileSet (X : Finset ℝ) (φ : ℝ → ℝ) (τ : ℝ) : Finset ℝ :=
  X.filter fun x => τ ≤ cdf X φ x

theorem quantileSet_subset (X : Finset ℝ) (φ : ℝ → ℝ) (τ : ℝ) : quantileSet X φ τ ⊆ X :=
  Finset.filter_subset _ _

theorem mem_quantileSet {X : Finset ℝ} {φ : ℝ → ℝ} {τ x : ℝ} :
    x ∈ quantileSet X φ τ ↔ x ∈ X ∧ τ ≤ cdf X φ x := Finset.mem_filter

/-- For `τ ≤ 1` the quantile set is nonempty: it contains the largest point of `X`. -/
theorem quantileSet_nonempty {X : Finset ℝ} {φ : ℝ → ℝ} (hX : X.Nonempty)
    (hφ : IsDistributionOn X φ) {τ : ℝ} (hτ : τ ≤ 1) : (quantileSet X φ τ).Nonempty :=
  ⟨X.max' hX, mem_quantileSet.2 ⟨Finset.max'_mem X hX, by rw [cdf_max' hX hφ]; exact hτ⟩⟩

/-- The `τ`-quantile (1.24), p. 32: `Q_τ X = min{x ∈ X : Φ(x) ≥ τ}`. -/
noncomputable def quantile (X : Finset ℝ) (φ : ℝ → ℝ) (τ : ℝ)
    (h : (quantileSet X φ τ).Nonempty) : ℝ :=
  (quantileSet X φ τ).min' h

/-- The quantile lies in `X` and its CDF value is at least `τ`. -/
theorem quantile_mem {X : Finset ℝ} {φ : ℝ → ℝ} {τ : ℝ} (h : (quantileSet X φ τ).Nonempty) :
    quantile X φ τ h ∈ X ∧ τ ≤ cdf X φ (quantile X φ τ h) :=
  mem_quantileSet.1 (Finset.min'_mem _ h)

/-- The quantile is the least point of `X` at which the CDF reaches `τ`. -/
theorem quantile_le {X : Finset ℝ} {φ : ℝ → ℝ} {τ : ℝ} (h : (quantileSet X φ τ).Nonempty) {x : ℝ}
    (hx : x ∈ X) (hτ : τ ≤ cdf X φ x) : quantile X φ τ h ≤ x :=
  Finset.min'_le _ _ (mem_quantileSet.2 ⟨hx, hτ⟩)

/-- Example 1.2.5 (p. 32): on `X = {1, 2, 3}` with `φ = (0.5, 0, 0.5)`, the CDF is
`(0.5, 0.5, 1)`. -/
theorem example_1_2_5_cdf :
    let φ : ℝ → ℝ := fun x => if x = 1 then 1 / 2 else if x = 3 then 1 / 2 else 0
    cdf {1, 2, 3} φ 1 = 1 / 2 ∧ cdf {1, 2, 3} φ 2 = 1 / 2 ∧ cdf {1, 2, 3} φ 3 = 1 := by
  intro φ
  simp only [cdf, φ]
  norm_num [Finset.sum_insert, Finset.sum_singleton]

/-- Example 1.2.5 (p. 32), continued: the median is `x₁ = 1`; the `min` in (1.24) selects it
although `2` would be another reasonable median. -/
theorem example_1_2_5_median
    (h : (quantileSet {1, 2, 3} (fun x : ℝ => if x = 1 then 1 / 2 else if x = 3 then 1 / 2
      else (0 : ℝ)) (1 / 2)).Nonempty) :
    quantile {1, 2, 3} (fun x : ℝ => if x = 1 then 1 / 2 else if x = 3 then 1 / 2 else 0)
      (1 / 2) h = 1 := by
  apply le_antisymm
  · refine quantile_le h (by simp) ?_
    simp only [cdf]
    norm_num [Finset.sum_insert, Finset.sum_singleton]
  · refine Finset.le_min' _ _ _ fun y hy => ?_
    have hyX := (quantileSet_subset _ _ _) hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyX
    rcases hyX with rfl | rfl | rfl <;> norm_num

/-- Shifting the distribution by `α`: the support moves to `X + α` and the mass function to
`y ↦ φ(y − α)` (Exercise 1.2.28, p. 32). -/
theorem isDistributionOn_shift {X : Finset ℝ} {φ : ℝ → ℝ} (hφ : IsDistributionOn X φ) (α : ℝ) :
    IsDistributionOn (X.image (· + α)) (fun y => φ (y - α)) where
  nonneg y hy := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    simpa using hφ.nonneg x hx
  sum_eq_one := by
    rw [Finset.sum_image fun _ _ _ _ h => add_right_cancel h]
    simpa using hφ.sum_eq_one

/-- The CDF of the shifted distribution: `Φ_Y(x + α) = Φ_X(x)`. -/
theorem cdf_shift (X : Finset ℝ) (φ : ℝ → ℝ) (α x : ℝ) :
    cdf (X.image (· + α)) (fun y => φ (y - α)) (x + α) = cdf X φ x := by
  unfold cdf
  rw [Finset.sum_image fun _ _ _ _ h => add_right_cancel h]
  refine Finset.sum_congr rfl fun x' _ => ?_
  simp only [add_le_add_iff_right, add_sub_cancel_right]

/-- The quantile set of the shifted distribution is the shifted quantile set. -/
theorem quantileSet_shift (X : Finset ℝ) (φ : ℝ → ℝ) (α τ : ℝ) :
    quantileSet (X.image (· + α)) (fun y => φ (y - α)) τ = (quantileSet X φ τ).image (· + α) := by
  ext y
  simp only [mem_quantileSet, Finset.mem_image]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hτ⟩
    exact ⟨x, ⟨hx, by rwa [cdf_shift] at hτ⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hτ⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, by rwa [cdf_shift]⟩

/-- Exercise 1.2.28 (p. 32): quantiles are additive over constants, `Q_τ(X + α) = Q_τ(X) + α`. -/
theorem quantile_shift (X : Finset ℝ) (φ : ℝ → ℝ) (α τ : ℝ) (h : (quantileSet X φ τ).Nonempty)
    (h' : (quantileSet (X.image (· + α)) (fun y => φ (y - α)) τ).Nonempty) :
    quantile (X.image (· + α)) (fun y => φ (y - α)) τ h' = quantile X φ τ h + α := by
  apply le_antisymm
  · -- `Q_τ(X) + α` lies in the shifted quantile set
    refine Finset.min'_le _ _ ?_
    rw [quantileSet_shift]
    exact Finset.mem_image.2 ⟨_, Finset.min'_mem _ h, rfl⟩
  · -- every point of the shifted quantile set is `x + α` with `x` in the original one
    refine Finset.le_min' _ _ _ fun y hy => ?_
    rw [quantileSet_shift] at hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    have := Finset.min'_le (quantileSet X φ τ) x hx
    unfold quantile
    linarith

end SargentStachurski.JobSearch

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The McCall job search model

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §1.1.1.1 (pp. 3–4)
and Assumption 1.1.1 (p. 11). An unemployed worker draws a wage offer each
period from a finite set `W ⊂ ℝ₊` with distribution `φ`; accepting means
working at that wage forever, rejecting means receiving compensation `c` and
drawing again. The discount factor is `β ∈ (0, 1)`.

`Model W` packages these primitives: the wage outcomes are the values of
`wage : W → ℝ` on a finite index type `W`, so that value functions are
functions `W → ℝ`. The expectation `E h = ∑ h(w) φ(w)` of §1.2.4.3 (p. 31) is
defined here with the facts the chapter uses about it: it preserves constants,
it is monotone, and it is 1-Lipschitz in the supremum norm.
-/

open Finset

namespace SargentStachurski.JobSearch

/-- The job search primitives (Assumption 1.1.1, p. 11): a finite set of nonnegative wage
offers with a probability distribution `φ`, compensation `c > 0`, and `β ∈ (0, 1)`. -/
structure Model (W : Type*) [Fintype W] where
  wage : W → ℝ
  wage_nonneg : ∀ w, 0 ≤ wage w
  φ : W → ℝ
  φ_nonneg : ∀ w, 0 ≤ φ w
  φ_sum : ∑ w, φ w = 1
  c : ℝ
  c_pos : 0 < c
  β : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1

namespace Model

variable {W : Type*} [Fintype W] (m : Model W)

theorem one_sub_β_pos : 0 < 1 - m.β := by linarith [m.β_lt_one]

theorem β_nonneg : 0 ≤ m.β := m.β_pos.le

/-- The expectation of `h(W)` under `φ`, `E h(W) = ∑ h(w) φ(w) = ⟨h, φ⟩` (p. 31). -/
def E (h : W → ℝ) : ℝ := ∑ w, h w * m.φ w

/-- The expectation of a constant is the constant. -/
theorem E_const (a : ℝ) : m.E (fun _ => a) = a := by
  simp only [E, ← mul_sum, m.φ_sum, mul_one]

/-- Expectation is monotone. -/
theorem E_mono {f g : W → ℝ} (h : ∀ w, f w ≤ g w) : m.E f ≤ m.E g :=
  sum_le_sum fun w _ => mul_le_mul_of_nonneg_right (h w) (m.φ_nonneg w)

/-- A pointwise upper bound bounds the expectation. -/
theorem E_le_of_le {f : W → ℝ} {a : ℝ} (h : ∀ w, f w ≤ a) : m.E f ≤ a := by
  calc m.E f ≤ m.E (fun _ => a) := m.E_mono h
    _ = a := m.E_const a

/-- A pointwise lower bound bounds the expectation. -/
theorem le_E_of_le {f : W → ℝ} {a : ℝ} (h : ∀ w, a ≤ f w) : a ≤ m.E f := by
  calc a = m.E (fun _ => a) := (m.E_const a).symm
    _ ≤ m.E f := m.E_mono h

/-- The expectation of a nonnegative function is nonnegative. -/
theorem E_nonneg {f : W → ℝ} (h : ∀ w, 0 ≤ f w) : 0 ≤ m.E f := m.le_E_of_le h

/-- Expectation is additive. -/
theorem E_add (f g : W → ℝ) : m.E (f + g) = m.E f + m.E g := by
  simp only [E, Pi.add_apply, add_mul, sum_add_distrib]

/-- Expectation commutes with scaling. -/
theorem E_mul (a : ℝ) (f : W → ℝ) : m.E (fun w => a * f w) = a * m.E f := by
  simp only [E, mul_assoc, ← mul_sum]

/-- Expectation is 1-Lipschitz in the supremum norm: `|E f − E g| ≤ ‖f − g‖_∞`. This is the
triangle-inequality step in the proof of Proposition 1.3.1 (p. 34). -/
theorem abs_E_sub_E_le (f g : W → ℝ) : |m.E f - m.E g| ≤ ‖f - g‖ := by
  have hle : ∀ w, |f w - g w| ≤ ‖f - g‖ := fun w => by
    have := norm_le_pi_norm (f - g) w
    simpa [Real.norm_eq_abs] using this
  calc |m.E f - m.E g| = |∑ w, (f w - g w) * m.φ w| := by
        simp only [E, ← sum_sub_distrib, sub_mul]
    _ ≤ ∑ w, |(f w - g w) * m.φ w| := abs_sum_le_sum_abs _ _
    _ = ∑ w, |f w - g w| * m.φ w := by
        refine sum_congr rfl fun w _ => ?_
        rw [abs_mul, abs_of_nonneg (m.φ_nonneg w)]
    _ ≤ ∑ w, ‖f - g‖ * m.φ w :=
        sum_le_sum fun w _ => mul_le_mul_of_nonneg_right (hle w) (m.φ_nonneg w)
    _ = ‖f - g‖ := by rw [← mul_sum, m.φ_sum, mul_one]

end Model

end SargentStachurski.JobSearch

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Finite-horizon job search by backward induction

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §1.1.1 (pp. 3–10):
the two-period problem (1.2)–(1.4), the three-period problem (1.5), and
Exercises 1.1.2–1.1.3.

Backward induction is organised by the number `j` of periods remaining after
the current one. With `j = 0` the worker takes `max{c, w}`, (1.2); with
`j + 1` remaining the stopping value is `w(1 + β + ⋯ + β^{j+1})` and the
continuation value is `c + β E v_j(W')`, so `v_{j+1}(w)` is their maximum,
(1.3) and (1.5). The reservation wage `w*_{j+1}` is the continuation value
divided by `1 + β + ⋯ + β^{j+1}`, (1.4) and Exercise 1.1.2, and the worker
accepts iff the offer is at least the reservation wage. Exercise 1.1.3's
`T`-period extension is the general `j`.

The two-period model's `v₂, v₁, h₁, w₁*` are `value 0`, `value 1`,
`contValue 0`, `resWage 1`; the three-period `v₀, w₀*` are `value 2`,
`resWage 2`. The comparative static of p. 7, that higher compensation raises
the continuation value and the reservation wage, is proved for every horizon.
-/

open Finset

namespace SargentStachurski.JobSearch

namespace Model

variable {W : Type*} [Fintype W] (m : Model W)

/-- The discounted sum `1 + β + ⋯ + βʲ` of `j + 1` wage payments. -/
def annuity (j : ℕ) : ℝ := ∑ s ∈ range (j + 1), m.β ^ s

/-- The stopping value with `j` periods remaining after this one: the offer `w` paid now and
in each of the `j` remaining periods, `w(1 + β + ⋯ + βʲ)` (p. 4, p. 7). -/
def stopValue (j : ℕ) (w : W) : ℝ := m.wage w * m.annuity j

/-- The value functions by backward induction: `v` with `0` periods remaining is `max{c, w}`
(1.2); with `j + 1` remaining it is the larger of stopping and continuing, (1.3), (1.5). -/
noncomputable def value : ℕ → W → ℝ
  | 0 => fun w => max m.c (m.wage w)
  | j + 1 => fun w => max (m.stopValue (j + 1) w) (m.c + m.β * m.E (value j))

/-- The continuation value when `j + 1` periods remain: reject, receive `c`, and behave
optimally with `j` remaining: `c + β ∑ v_j(w') φ(w')`, (1.2). -/
noncomputable def contValue (j : ℕ) : ℝ := m.c + m.β * m.E (m.value j)

/-- The reservation wage: with no periods remaining it is `c`; with `j + 1` remaining it is the
continuation value divided by the annuity factor, (1.4) and Exercise 1.1.2. -/
noncomputable def resWage : ℕ → ℝ
  | 0 => m.c
  | j + 1 => m.contValue j / m.annuity (j + 1)

theorem annuity_pos (j : ℕ) : 0 < m.annuity j := by
  unfold annuity
  rw [sum_range_succ']
  have : 0 ≤ ∑ s ∈ range j, m.β ^ (s + 1) := sum_nonneg fun s _ => pow_nonneg m.β_nonneg _
  simp only [pow_zero]
  linarith

theorem annuity_zero : m.annuity 0 = 1 := by simp [annuity]

theorem annuity_one : m.annuity 1 = 1 + m.β := by simp [annuity, sum_range_succ]

theorem annuity_two : m.annuity 2 = 1 + m.β + m.β ^ 2 := by
  simp [annuity, sum_range_succ]

/-- (1.2), p. 4: the last-period value is `v₂(w) = max{c, w}`. -/
theorem value_zero (w : W) : m.value 0 w = max m.c (m.wage w) := rfl

/-- (1.2), p. 4: `h₁ = c + β ∑ v₂(w') φ(w')`. -/
theorem contValue_zero : m.contValue 0 = m.c + m.β * m.E (fun w => max m.c (m.wage w)) := rfl

/-- (1.3), p. 6: `v₁(w) = max{w + βw, h₁}`. -/
theorem value_one (w : W) : m.value 1 w = max (m.wage w + m.β * m.wage w) (m.contValue 0) := by
  change max (m.stopValue 1 w) (m.contValue 0) = _
  rw [stopValue, annuity_one]
  ring_nf

/-- (1.4), p. 6: the two-period reservation wage `w₁* = h₁/(1 + β)`. -/
theorem resWage_one : m.resWage 1 = m.contValue 0 / (1 + m.β) := by
  change m.contValue 0 / m.annuity 1 = _
  rw [annuity_one]

/-- (1.5), p. 7: `v₀(w) = max{w + βw + β²w, c + β ∑ v₁(w') φ(w')}`. -/
theorem value_two (w : W) :
    m.value 2 w = max (m.wage w + m.β * m.wage w + m.β ^ 2 * m.wage w) (m.contValue 1) := by
  change max (m.stopValue 2 w) (m.contValue 1) = _
  rw [stopValue, annuity_two]
  ring_nf

/-- Exercise 1.1.2, p. 10: the time-zero reservation wage `w₀* = h₀/(1 + β + β²)`. -/
theorem resWage_two : m.resWage 2 = m.contValue 1 / (1 + m.β + m.β ^ 2) := by
  change m.contValue 1 / m.annuity 2 = _
  rw [annuity_two]

/-- With `j + 1` periods remaining the value is the larger of stopping and continuing. -/
theorem value_succ (j : ℕ) (w : W) :
    m.value (j + 1) w = max (m.stopValue (j + 1) w) (m.contValue j) := rfl

/-- The optimal choice (p. 7, Exercise 1.1.3): stopping is at least as good as continuing iff the
offer is at least the reservation wage. -/
theorem contValue_le_stopValue_iff (j : ℕ) (w : W) :
    m.contValue j ≤ m.stopValue (j + 1) w ↔ m.resWage (j + 1) ≤ m.wage w := by
  change m.contValue j ≤ m.wage w * m.annuity (j + 1) ↔ m.contValue j / m.annuity (j + 1) ≤ _
  rw [div_le_iff₀ (m.annuity_pos (j + 1))]

/-- The value equals the stopping value iff the offer is at least the reservation wage: the
worker accepts. -/
theorem value_succ_eq_stopValue_iff (j : ℕ) (w : W) :
    m.value (j + 1) w = m.stopValue (j + 1) w ↔ m.resWage (j + 1) ≤ m.wage w := by
  rw [value_succ, max_eq_left_iff, contValue_le_stopValue_iff]

/-- The value equals the continuation value iff the offer is at most the reservation wage: the
worker rejects. -/
theorem value_succ_eq_contValue_iff (j : ℕ) (w : W) :
    m.value (j + 1) w = m.contValue j ↔ m.wage w ≤ m.resWage (j + 1) := by
  rw [value_succ, max_eq_right_iff]
  change m.wage w * m.annuity (j + 1) ≤ m.contValue j ↔ _ ≤ m.contValue j / m.annuity (j + 1)
  rw [le_div_iff₀ (m.annuity_pos (j + 1))]

/-- In the last period the worker accepts iff `w ≥ c = w*₀`. -/
theorem value_zero_eq_wage_iff (w : W) : m.value 0 w = m.wage w ↔ m.resWage 0 ≤ m.wage w := by
  change max m.c (m.wage w) = m.wage w ↔ m.c ≤ m.wage w
  exact max_eq_right_iff

/-- Values are bounded below by the compensation `c`. -/
theorem c_le_value (j : ℕ) (w : W) : m.c ≤ m.value j w := by
  induction j generalizing w with
  | zero => exact le_max_left _ _
  | succ j ih =>
    rw [value_succ]
    refine le_trans ?_ (le_max_right _ _)
    unfold contValue
    have : 0 ≤ m.E (m.value j) := m.E_nonneg fun w => m.c_pos.le.trans (ih w)
    nlinarith [m.β_pos]

/-- Values are nonnegative. -/
theorem value_nonneg (j : ℕ) (w : W) : 0 ≤ m.value j w := m.c_pos.le.trans (m.c_le_value j w)

/-- Reservation wages are positive. -/
theorem resWage_pos (j : ℕ) : 0 < m.resWage j := by
  cases j with
  | zero => exact m.c_pos
  | succ j =>
    change 0 < m.contValue j / m.annuity (j + 1)
    refine div_pos ?_ (m.annuity_pos _)
    unfold contValue
    have : 0 ≤ m.E (m.value j) := m.E_nonneg (m.value_nonneg j)
    nlinarith [m.β_pos, m.c_pos]

/-! ### Higher compensation raises the reservation wage (p. 7)

Two models that share wages, distribution and discount factor but differ in compensation.
-/

/-- Values are increasing in the compensation `c`, horizon by horizon. -/
theorem value_le_value_of_c_le (m' : Model W) (hw : m.wage = m'.wage) (hφ : m.φ = m'.φ)
    (hβ : m.β = m'.β) (hc : m.c ≤ m'.c) (j : ℕ) (w : W) : m.value j w ≤ m'.value j w := by
  induction j generalizing w with
  | zero =>
    change max m.c (m.wage w) ≤ max m'.c (m'.wage w)
    rw [hw]
    exact max_le_max_right _ hc
  | succ j ih =>
    rw [value_succ, value_succ]
    have hs : m.stopValue (j + 1) w = m'.stopValue (j + 1) w := by
      simp only [stopValue, annuity, hw, hβ]
    have hE : m.E (m.value j) ≤ m'.E (m'.value j) := by
      calc m.E (m.value j) ≤ m.E (m'.value j) := m.E_mono (ih)
        _ = m'.E (m'.value j) := by simp only [E, hφ]
    have hcont : m.contValue j ≤ m'.contValue j := by
      unfold contValue
      rw [hβ]
      nlinarith [m'.β_pos]
    rw [hs]
    exact max_le_max_left _ hcont

/-- The continuation value is increasing in `c` (p. 7: "higher unemployment compensation `c`
shifts up the continuation value `h₁`"). -/
theorem contValue_le_contValue_of_c_le (m' : Model W) (hw : m.wage = m'.wage) (hφ : m.φ = m'.φ)
    (hβ : m.β = m'.β) (hc : m.c ≤ m'.c) (j : ℕ) : m.contValue j ≤ m'.contValue j := by
  unfold contValue
  have hE : m.E (m.value j) ≤ m'.E (m'.value j) := by
    calc m.E (m.value j) ≤ m.E (m'.value j) :=
          m.E_mono (m.value_le_value_of_c_le m' hw hφ hβ hc j)
      _ = m'.E (m'.value j) := by simp only [E, hφ]
  rw [hβ]
  nlinarith [m'.β_pos]

/-- The reservation wage is increasing in `c` at every horizon (p. 7: "... and increases the
reservation wage"). -/
theorem resWage_le_resWage_of_c_le (m' : Model W) (hw : m.wage = m'.wage) (hφ : m.φ = m'.φ)
    (hβ : m.β = m'.β) (hc : m.c ≤ m'.c) (j : ℕ) : m.resWage j ≤ m'.resWage j := by
  cases j with
  | zero => exact hc
  | succ j =>
    change m.contValue j / m.annuity (j + 1) ≤ m'.contValue j / m'.annuity (j + 1)
    have ha : m.annuity (j + 1) = m'.annuity (j + 1) := by simp only [annuity, hβ]
    rw [ha]
    exact div_le_div_of_nonneg_right (m.contValue_le_contValue_of_c_le m' hw hφ hβ hc j)
      (m'.annuity_pos _).le

end Model

end SargentStachurski.JobSearch

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Bellman operator for infinite-horizon job search

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §1.1.2 (pp. 10–12)
and §1.3.1 (pp. 32–36).

The worker maximises `E ∑ βᵗ Rₜ`, (1.6). Accepting `w` yields `w/(1 − β)`,
(1.7); the value function `v*` satisfies the Bellman equation (1.8) = (1.25).
The Bellman operator (1.27),

  `(Tv)(w) = max{ w/(1 − β), c + β ∑ v(w') φ(w') }`,

is a contraction of modulus `β` on `V = ℝ^W₊` in the supremum norm,
Proposition 1.3.1 (p. 33), so by Theorem 1.2.3 it has a unique fixed point
`v*` in `V`, and value function iteration `Tᵏv → v*` converges from every
`v ∈ V` at rate `βᵏ` (§1.3.2.1). The continuation value `h*`, (1.26), the
`v`-greedy policies, (1.29), and the reservation wage `w* = (1 − β)h*`,
(1.30), complete the section. The principle of optimality, that a `v*`-greedy
policy is optimal for (1.6), is stated in the book without proof here ("later
we prove it in a general setting", p. 12) and is not claimed.
-/

open Filter Topology Function Set Finset

namespace SargentStachurski.JobSearch

/-- The candidate space `V = ℝ^W₊` of nonnegative functions (p. 33). -/
def V (W : Type*) : Set (W → ℝ) := {v | ∀ w, 0 ≤ v w}

theorem V_nonempty (W : Type*) : (V W).Nonempty := ⟨0, fun _ => le_rfl⟩

theorem isClosed_V (W : Type*) : IsClosed (V W) := by
  have : V W = ⋂ w, {v : W → ℝ | 0 ≤ v w} := by
    ext v
    simp [V]
  rw [this]
  exact isClosed_iInter fun w => isClosed_le continuous_const (continuous_apply w)

namespace Model

variable {W : Type*} [Fintype W] (m : Model W)

/-- (1.7), p. 11: the lifetime payoff of a permanent job at wage `w` is
`w + βw + β²w + ⋯ = w/(1 − β)`. -/
theorem tsum_geometric_wage (w : W) : ∑' t : ℕ, m.β ^ t * m.wage w = m.wage w / (1 - m.β) := by
  rw [tsum_mul_right, tsum_geometric_of_lt_one m.β_nonneg m.β_lt_one, div_eq_inv_mul]

/-- The stopping value `w/(1 − β)` of accepting the current offer. -/
noncomputable def stop (w : W) : ℝ := m.wage w / (1 - m.β)

theorem stop_nonneg (w : W) : 0 ≤ m.stop w := div_nonneg (m.wage_nonneg w) m.one_sub_β_pos.le

/-- The Bellman operator (1.27), p. 33: `(Tv)(w) = max{w/(1 − β), c + β ∑ v(w') φ(w')}`. -/
noncomputable def T (v : W → ℝ) : W → ℝ := fun w => max (m.stop w) (m.c + m.β * m.E v)

/-- `T` maps `V` into `V`: `Tv ≥ w/(1 − β) ≥ 0`. -/
theorem mapsTo_T : MapsTo m.T (V W) (V W) :=
  fun _ _ w => (m.stop_nonneg w).trans (le_max_left _ _)

/-- The pointwise estimate in the proof of Proposition 1.3.1 (p. 34):
`|(Tf)(w) − (Tg)(w)| ≤ β ∑ |f(w') − g(w')| φ(w') ≤ β‖f − g‖_∞`. -/
theorem abs_T_sub_T_le (f g : W → ℝ) (w : W) : |m.T f w - m.T g w| ≤ m.β * ‖f - g‖ := by
  calc |m.T f w - m.T g w| ≤ |(m.c + m.β * m.E f) - (m.c + m.β * m.E g)| :=
        abs_max_sub_max_le _ _ _
    _ = m.β * |m.E f - m.E g| := by
        rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_pos m.β_pos]
    _ ≤ m.β * ‖f - g‖ := mul_le_mul_of_nonneg_left (m.abs_E_sub_E_le f g) m.β_nonneg

/-- Proposition 1.3.1 (p. 33), the norm inequality: `‖Tf − Tg‖_∞ ≤ β‖f − g‖_∞`. -/
theorem norm_T_sub_T_le (f g : W → ℝ) : ‖m.T f - m.T g‖ ≤ m.β * ‖f - g‖ := by
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg m.β_nonneg (norm_nonneg _))]
  intro w
  rw [Pi.sub_apply, Real.norm_eq_abs]
  exact m.abs_T_sub_T_le f g w

/-- Proposition 1.3.1 (p. 33): `T` is a contraction of modulus `β` on `V`. -/
theorem isContractionOn_T : IsContractionOn m.T (V W) m.β :=
  ⟨m.mapsTo_T, m.β_nonneg, m.β_lt_one, fun f _ g _ => m.norm_T_sub_T_le f g⟩

/-- `T` is in fact a contraction of modulus `β` on all of `ℝ^W`. -/
theorem isContractionOn_T_univ : IsContractionOn m.T univ m.β :=
  ⟨mapsTo_univ _ _, m.β_nonneg, m.β_lt_one, fun f _ g _ => m.norm_T_sub_T_le f g⟩

/-- The value function `v*` (p. 11, p. 33): the fixed point of `T` in `V` delivered by Theorem
1.2.3. -/
noncomputable def vstar : W → ℝ :=
  (m.isContractionOn_T.exists_fixedPt (isClosed_V W) (V_nonempty W)).choose

theorem vstar_mem_V : m.vstar ∈ V W :=
  (m.isContractionOn_T.exists_fixedPt (isClosed_V W) (V_nonempty W)).choose_spec.1

theorem vstar_nonneg (w : W) : 0 ≤ m.vstar w := m.vstar_mem_V w

theorem isFixedPt_vstar : IsFixedPt m.T m.vstar :=
  (m.isContractionOn_T.exists_fixedPt (isClosed_V W) (V_nonempty W)).choose_spec.2

/-- The Bellman equation (1.8), (1.25): `v*(w) = max{w/(1 − β), c + β ∑ v*(w') φ(w')}`. -/
theorem bellman_equation (w : W) :
    m.vstar w = max (m.wage w / (1 - m.β)) (m.c + m.β * m.E m.vstar) :=
  (congrFun m.isFixedPt_vstar.eq w).symm

/-- Any solution of the Bellman equation in `ℝ^W` is `v*`: uniqueness, from the contraction
property on all of `ℝ^W`. -/
theorem eq_vstar_of_isFixedPt {v : W → ℝ} (hv : IsFixedPt m.T v) : v = m.vstar :=
  m.isContractionOn_T_univ.fixedPt_unique trivial trivial hv m.isFixedPt_vstar

/-- `v*` is the unique fixed point of `T`. -/
theorem existsUnique_fixedPt : ∃! v : W → ℝ, IsFixedPt m.T v :=
  ⟨m.vstar, m.isFixedPt_vstar, fun _ hv => m.eq_vstar_of_isFixedPt hv⟩

/-- Value function iteration (§1.3.2.1, Algorithm 1.1): `Tᵏv → v*` from every `v ∈ ℝ^W`, in
particular from every `v ∈ V` as the book states after Proposition 1.3.1 (p. 33). -/
theorem tendsto_iterate_T (v : W → ℝ) : Tendsto (fun k : ℕ => m.T^[k] v) atTop (𝓝 m.vstar) :=
  m.isContractionOn_T_univ.tendsto_iterate_fixedPt trivial trivial m.isFixedPt_vstar

/-- The rate of value function iteration, (1.18) for `T`: `‖Tᵏv − v*‖ ≤ βᵏ‖v − v*‖`. -/
theorem norm_iterate_T_sub_vstar_le (v : W → ℝ) (k : ℕ) :
    ‖m.T^[k] v - m.vstar‖ ≤ m.β ^ k * ‖v - m.vstar‖ :=
  m.isContractionOn_T_univ.norm_iterate_sub_fixedPt_le trivial trivial m.isFixedPt_vstar k

/-- `T` is globally stable on `ℝ^W`. -/
theorem globallyStable_T : GloballyStable m.T :=
  globallyStable_of_tendsto m.isFixedPt_vstar m.tendsto_iterate_T

/-- The continuation value (1.26), p. 33: `h* = c + β ∑ v*(w') φ(w')`. -/
noncomputable def hstar : ℝ := m.c + m.β * m.E m.vstar

/-- The value function in terms of the continuation value: `v*(w) = max{w/(1 − β), h*}`
(p. 39). -/
theorem vstar_eq_max (w : W) : m.vstar w = max (m.wage w / (1 - m.β)) m.hstar :=
  m.bellman_equation w

/-- A policy (p. 35): a map from wage offers to `{accept, reject}`, here `Bool` with `true` for
accept (the book's `1`). -/
abbrev Policy (W : Type*) := W → Bool

/-- A `v`-greedy policy (1.29), p. 35: accept iff `w/(1 − β) ≥ c + β ∑ v(w') φ(w')`. -/
def IsGreedy (v : W → ℝ) (σ : Policy W) : Prop :=
  ∀ w, σ w = true ↔ m.c + m.β * m.E v ≤ m.stop w

/-- Every `v` has a greedy policy. -/
theorem exists_isGreedy (v : W → ℝ) : ∃ σ : Policy W, m.IsGreedy v σ := by
  classical
  exact ⟨fun w => decide (m.c + m.β * m.E v ≤ m.stop w), fun w => by simp⟩

/-- The reservation wage (1.30), p. 36: `w* = (1 − β) h*`. -/
noncomputable def reservationWage : ℝ := (1 - m.β) * m.hstar

/-- The optimal choice of §1.3.1.1 (p. 33): accept iff `w/(1 − β) ≥ h*`, equivalently iff
`w ≥ w*`. -/
theorem hstar_le_stop_iff (w : W) : m.hstar ≤ m.stop w ↔ m.reservationWage ≤ m.wage w := by
  rw [stop, reservationWage, le_div_iff₀ m.one_sub_β_pos, mul_comm]

/-- (1.30), p. 36: a policy is `v*`-greedy iff it accepts exactly the offers at or above the
reservation wage, `σ*(w) = 1{w ≥ w*}`. -/
theorem isGreedy_vstar_iff (σ : Policy W) :
    m.IsGreedy m.vstar σ ↔ ∀ w, σ w = true ↔ m.reservationWage ≤ m.wage w := by
  unfold IsGreedy
  refine forall_congr' fun w => ?_
  change (σ w = true ↔ m.hstar ≤ m.stop w) ↔ _
  rw [hstar_le_stop_iff]

end Model

end SargentStachurski.JobSearch

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Computing the continuation value directly

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §1.3.2.2 (pp. 39–41).

Substituting `v*(w') = max{w'/(1 − β), h*}` into the definition of the
continuation value gives the scalar equation (1.32),

  `h* = c + β ∑ max{w'/(1 − β), h*} φ(w')`,

so `h*` is the fixed point of the map `g : ℝ₊ → ℝ₊` of (1.33). Exercise 1.3.2
shows `g` is a contraction and `h*` its unique fixed point in `ℝ₊`; iterating
`g` from any `h ≥ 0` converges to `h*`, a one-dimensional computation in place
of value function iteration in `ℝⁿ`. Exercise 1.3.3's identity
`v*(w) = max{w/(1 − β), h*}` and the policy characterisation (1.34) follow.

The comparative static of p. 7 is proved for the infinite horizon as well:
higher compensation raises `h*` and the reservation wage.
-/

open Filter Topology Function Set Finset

namespace SargentStachurski.JobSearch

namespace Model

variable {W : Type*} [Fintype W] (m : Model W)

/-- The map `g` of (1.33), p. 40: `g(h) = c + β ∑ max{w'/(1 − β), h} φ(w')`. -/
noncomputable def g (h : ℝ) : ℝ := m.c + m.β * m.E (fun w => max (m.stop w) h)

/-- (1.32), p. 40: `h*` solves `h = g(h)`. -/
theorem isFixedPt_g_hstar : IsFixedPt m.g m.hstar := by
  change m.g m.hstar = m.hstar
  unfold g
  have : (fun w => max (m.stop w) m.hstar) = m.vstar := by
    funext w
    exact (m.vstar_eq_max w).symm
  rw [this]
  rfl

/-- `g` maps `ℝ₊` into `ℝ₊` (indeed `g(h) ≥ c > 0`). -/
theorem g_nonneg (h : ℝ) : 0 ≤ m.g h := by
  unfold g
  have : 0 ≤ m.E (fun w => max (m.stop w) h) :=
    m.E_nonneg fun w => (m.stop_nonneg w).trans (le_max_left _ _)
  nlinarith [m.c_pos, m.β_pos]

theorem mapsTo_g : MapsTo m.g (Ici 0) (Ici 0) := fun h _ => m.g_nonneg h

/-- `|g(h) − g(h')| ≤ β|h − h'|`, by the bound (1.28) inside the expectation. -/
theorem abs_g_sub_g_le (h h' : ℝ) : |m.g h - m.g h'| ≤ m.β * |h - h'| := by
  unfold g
  rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_pos m.β_pos]
  refine mul_le_mul_of_nonneg_left ?_ m.β_nonneg
  rw [E, E, ← sum_sub_distrib]
  calc |∑ w, (max (m.stop w) h * m.φ w - max (m.stop w) h' * m.φ w)|
      ≤ ∑ w, |max (m.stop w) h * m.φ w - max (m.stop w) h' * m.φ w| := abs_sum_le_sum_abs _ _
    _ = ∑ w, |max (m.stop w) h - max (m.stop w) h'| * m.φ w := by
        refine sum_congr rfl fun w _ => ?_
        rw [← sub_mul, abs_mul, abs_of_nonneg (m.φ_nonneg w)]
    _ ≤ ∑ w, |h - h'| * m.φ w :=
        sum_le_sum fun w _ =>
          mul_le_mul_of_nonneg_right (abs_max_sub_max_le _ _ _) (m.φ_nonneg w)
    _ = |h - h'| := by rw [← mul_sum, m.φ_sum, mul_one]

/-- Exercise 1.3.2 (p. 40): `g` is a contraction of modulus `β` on `ℝ₊`. -/
theorem isContractionOn_g : IsContractionOn m.g (Ici 0) m.β :=
  ⟨m.mapsTo_g, m.β_nonneg, m.β_lt_one, fun h _ h' _ => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact m.abs_g_sub_g_le h h'⟩

/-- `g` is a contraction of modulus `β` on all of `ℝ`. -/
theorem isContractionOn_g_univ : IsContractionOn m.g univ m.β :=
  ⟨mapsTo_univ _ _, m.β_nonneg, m.β_lt_one, fun h _ h' _ => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact m.abs_g_sub_g_le h h'⟩

/-- `h* ≥ 0`, so `h*` lies in the domain `ℝ₊` of (1.33). -/
theorem hstar_nonneg : 0 ≤ m.hstar := by
  rw [← m.isFixedPt_g_hstar.eq]
  exact m.g_nonneg _

/-- Exercise 1.3.2 (p. 40), conclusion: `h*` is the unique fixed point of `g` in `ℝ₊`. -/
theorem eq_hstar_of_isFixedPt_g {h : ℝ} (hh : IsFixedPt m.g h) : h = m.hstar :=
  m.isContractionOn_g_univ.fixedPt_unique trivial trivial hh m.isFixedPt_g_hstar

/-- Iterating `g` from any `h` converges to `h*` (p. 40): the one-dimensional computation of
the continuation value. -/
theorem tendsto_iterate_g (h : ℝ) : Tendsto (fun k : ℕ => m.g^[k] h) atTop (𝓝 m.hstar) :=
  m.isContractionOn_g_univ.tendsto_iterate_fixedPt trivial trivial m.isFixedPt_g_hstar

/-- The rate: `|gᵏ(h) − h*| ≤ βᵏ|h − h*|`. -/
theorem abs_iterate_g_sub_hstar_le (h : ℝ) (k : ℕ) :
    |m.g^[k] h - m.hstar| ≤ m.β ^ k * |h - m.hstar| := by
  have := m.isContractionOn_g_univ.norm_iterate_sub_fixedPt_le trivial trivial
    m.isFixedPt_g_hstar (u := h) k
  simpa [Real.norm_eq_abs] using this

/-- Exercise 1.3.3 (p. 41): with `h*` in hand, `v*(w) = max{w/(1 − β), h*}`, so the value
function computed from `h*` agrees with the one from value function iteration. -/
theorem vstar_eq_max_hstar (w : W) : m.vstar w = max (m.wage w / (1 - m.β)) m.hstar :=
  m.vstar_eq_max w

/-- (1.34), p. 41: a policy is `v*`-greedy iff it accepts exactly when `w/(1 − β) ≥ h*`. -/
theorem isGreedy_vstar_iff_hstar (σ : Policy W) :
    m.IsGreedy m.vstar σ ↔ ∀ w, σ w = true ↔ m.hstar ≤ m.stop w :=
  Iff.rfl

/-! ### Higher compensation raises the continuation value and the reservation wage

The two-period comparative static of p. 7, for the infinite horizon: if `c ≤ c'` with the same
wages, distribution and discount factor, then `h* ≤ h*'` and `w* ≤ w*'`. The argument is the
scalar case of Proposition 2.2.7 (Chapter 2): `g ≤ g'` pointwise, `g'` is order preserving, and
both are contractions, so the fixed points are ordered. -/

/-- `g` is order preserving. -/
theorem g_mono : Monotone m.g := by
  intro h h' hh
  unfold g
  have : m.E (fun w => max (m.stop w) h) ≤ m.E (fun w => max (m.stop w) h') :=
    m.E_mono fun w => max_le_max_left _ hh
  nlinarith [m.β_pos]

/-- `g ≤ g'` pointwise when `c ≤ c'`. -/
theorem g_le_g_of_c_le (m' : Model W) (hw : m.wage = m'.wage) (hφ : m.φ = m'.φ) (hβ : m.β = m'.β)
    (hc : m.c ≤ m'.c) (h : ℝ) : m.g h ≤ m'.g h := by
  unfold g
  have : m.E (fun w => max (m.stop w) h) = m'.E (fun w => max (m'.stop w) h) := by
    simp only [E, stop, hw, hφ, hβ]
  rw [this, hβ]
  linarith

/-- The continuation value is increasing in `c`. -/
theorem hstar_le_hstar_of_c_le (m' : Model W) (hw : m.wage = m'.wage) (hφ : m.φ = m'.φ)
    (hβ : m.β = m'.β) (hc : m.c ≤ m'.c) : m.hstar ≤ m'.hstar := by
  by_contra hlt
  have hlt' : m'.hstar < m.hstar := not_le.1 hlt
  -- `h*' = g'(h*') ≥ g(h*')` and `g(h*) − g(h*') ≤ β(h* − h*')`, so `(1 − β)(h* − h*') ≤ 0`
  have h1 : m.g m'.hstar ≤ m'.hstar := by
    calc m.g m'.hstar ≤ m'.g m'.hstar := m.g_le_g_of_c_le m' hw hφ hβ hc _
      _ = m'.hstar := m'.isFixedPt_g_hstar
  have h2 : m.hstar - m.g m'.hstar ≤ m.β * (m.hstar - m'.hstar) := by
    have := m.abs_g_sub_g_le m.hstar m'.hstar
    rw [m.isFixedPt_g_hstar.eq] at this
    have hpos : 0 < m.hstar - m'.hstar := by linarith
    rw [abs_of_pos hpos] at this
    exact (le_abs_self _).trans this
  have h3 := m.β_lt_one
  nlinarith

/-- The reservation wage is increasing in `c`. -/
theorem reservationWage_le_of_c_le (m' : Model W) (hw : m.wage = m'.wage) (hφ : m.φ = m'.φ)
    (hβ : m.β = m'.β) (hc : m.c ≤ m'.c) : m.reservationWage ≤ m'.reservationWage := by
  unfold reservationWage
  rw [hβ]
  exact mul_le_mul_of_nonneg_left (m.hstar_le_hstar_of_c_le m' hw hφ hβ hc) m'.one_sub_β_pos.le

end Model

end SargentStachurski.JobSearch

set_option linter.style.longLine false
#print axioms SargentStachurski.JobSearch.abs_eq_max_neg'
#print axioms SargentStachurski.JobSearch.max_add_le_add_max
#print axioms SargentStachurski.JobSearch.max_le_abs_sub_add_max
#print axioms SargentStachurski.JobSearch.abs_max_sub_max_le
#print axioms SargentStachurski.JobSearch.abs_min_sub_min_le
#print axioms SargentStachurski.JobSearch.max_le_max_of_le
#print axioms SargentStachurski.JobSearch.smul_add_smul_apply
#print axioms SargentStachurski.JobSearch.mul_apply'
#print axioms SargentStachurski.JobSearch.abs_apply'
#print axioms SargentStachurski.JobSearch.sup_apply'
#print axioms SargentStachurski.JobSearch.inf_apply'
#print axioms SargentStachurski.JobSearch.GloballyStable
#print axioms SargentStachurski.JobSearch.isFixedPt_id
#print axioms SargentStachurski.JobSearch.not_isFixedPt_succ
#print axioms SargentStachurski.JobSearch.isFixedPt_of_iterate_eventually_const
#print axioms SargentStachurski.JobSearch.eq_of_isFixedPt_of_iterate_eventually_const
#print axioms SargentStachurski.JobSearch.isFixedPt_of_tendsto_iterate
#print axioms SargentStachurski.JobSearch.GloballyStable.exists_unique
#print axioms SargentStachurski.JobSearch.globallyStable_of_tendsto
#print axioms SargentStachurski.JobSearch.iterate_mem_of_mapsTo
#print axioms SargentStachurski.JobSearch.GloballyStable.fixedPt_mem_of_isClosed
#print axioms SargentStachurski.JobSearch.IsContractionOn
#print axioms SargentStachurski.JobSearch.IsContractionOn.mk
#print axioms SargentStachurski.JobSearch.IsContractionOn.mapsTo
#print axioms SargentStachurski.JobSearch.IsContractionOn.nonneg
#print axioms SargentStachurski.JobSearch.IsContractionOn.lt_one
#print axioms SargentStachurski.JobSearch.IsContractionOn.norm_sub_le
#print axioms SargentStachurski.JobSearch.IsContractionOn.continuousOn
#print axioms SargentStachurski.JobSearch.IsContractionOn.fixedPt_unique
#print axioms SargentStachurski.JobSearch.IsContractionOn.iterate_mem
#print axioms SargentStachurski.JobSearch.IsContractionOn.norm_iterate_sub_iterate_succ_le
#print axioms SargentStachurski.JobSearch.IsContractionOn.norm_iterate_sub_iterate_le_sum
#print axioms SargentStachurski.JobSearch.IsContractionOn.norm_iterate_sub_iterate_le
#print axioms SargentStachurski.JobSearch.IsContractionOn.cauchySeq_iterate
#print axioms SargentStachurski.JobSearch.IsContractionOn.limit_mem
#print axioms SargentStachurski.JobSearch.IsContractionOn.isFixedPt_of_tendsto
#print axioms SargentStachurski.JobSearch.IsContractionOn.norm_iterate_sub_fixedPt_le
#print axioms SargentStachurski.JobSearch.IsContractionOn.tendsto_iterate_fixedPt
#print axioms SargentStachurski.JobSearch.IsContractionOn.exists_fixedPt
#print axioms SargentStachurski.JobSearch.IsContractionOn.banach
#print axioms SargentStachurski.JobSearch.IsContractionOn.globallyStable
#print axioms SargentStachurski.JobSearch.isContractionOn_damped
#print axioms SargentStachurski.JobSearch.isFixedPt_damped_iff
#print axioms SargentStachurski.JobSearch.tendsto_damped_iterate
#print axioms SargentStachurski.JobSearch.IsContractionOn.banach_pi
#print axioms SargentStachurski.JobSearch.IsNorm
#print axioms SargentStachurski.JobSearch.IsNorm.mk
#print axioms SargentStachurski.JobSearch.IsNorm.nonneg
#print axioms SargentStachurski.JobSearch.IsNorm.eq_zero_iff
#print axioms SargentStachurski.JobSearch.IsNorm.smul
#print axioms SargentStachurski.JobSearch.IsNorm.add_le
#print axioms SargentStachurski.JobSearch.l1Norm
#print axioms SargentStachurski.JobSearch.weightedL1Norm
#print axioms SargentStachurski.JobSearch.supNorm
#print axioms SargentStachurski.JobSearch.l0Norm
#print axioms SargentStachurski.JobSearch.isNorm_l1Norm
#print axioms SargentStachurski.JobSearch.isNorm_weightedL1Norm
#print axioms SargentStachurski.JobSearch.isNorm_supNorm
#print axioms SargentStachurski.JobSearch.supNorm_le_iff
#print axioms SargentStachurski.JobSearch.abs_le_supNorm
#print axioms SargentStachurski.JobSearch.not_isNorm_l0Norm
#print axioms SargentStachurski.JobSearch.NormEquiv
#print axioms SargentStachurski.JobSearch.normEquiv_refl
#print axioms SargentStachurski.JobSearch.normEquiv_symm
#print axioms SargentStachurski.JobSearch.normEquiv_trans
#print axioms SargentStachurski.JobSearch.normEquiv_equivalence
#print axioms SargentStachurski.JobSearch.tendsto_of_normEquiv
#print axioms SargentStachurski.JobSearch.tendsto_pi_iff_tendsto_supNorm
#print axioms SargentStachurski.JobSearch.matrixSupNorm
#print axioms SargentStachurski.JobSearch.opNorm
#print axioms SargentStachurski.JobSearch.opNorm_mul
#print axioms SargentStachurski.JobSearch.supNorm_mulVec_le
#print axioms SargentStachurski.JobSearch.not_matrixSupNorm_submultiplicative
#print axioms SargentStachurski.JobSearch.opNorm_eq_norm
#print axioms SargentStachurski.JobSearch.complexify
#print axioms SargentStachurski.JobSearch.complexify_apply
#print axioms SargentStachurski.JobSearch.complexify_pow
#print axioms SargentStachurski.JobSearch.complexify_smul
#print axioms SargentStachurski.JobSearch.nnnorm_complexify
#print axioms SargentStachurski.JobSearch.norm_complexify
#print axioms SargentStachurski.JobSearch.specRad
#print axioms SargentStachurski.JobSearch.spectralRadius_complexify_ne_top
#print axioms SargentStachurski.JobSearch.specRad_nonneg
#print axioms SargentStachurski.JobSearch.mem_spectrum_iff_eigenpair
#print axioms SargentStachurski.JobSearch.tendsto_norm_pow_rpow
#print axioms SargentStachurski.JobSearch.specRad_pow_le_norm_pow
#print axioms SargentStachurski.JobSearch.eventually_norm_pow_le
#print axioms SargentStachurski.JobSearch.tendsto_norm_pow_zero
#print axioms SargentStachurski.JobSearch.tendsto_pow_zero
#print axioms SargentStachurski.JobSearch.specRad_lt_one_of_tendsto
#print axioms SargentStachurski.JobSearch.tendsto_norm_pow_atTop
#print axioms SargentStachurski.JobSearch.specRad_smul
#print axioms SargentStachurski.JobSearch.specRad_mul_le
#print axioms SargentStachurski.JobSearch.summable_pow
#print axioms SargentStachurski.JobSearch.one_sub_mul_tsum
#print axioms SargentStachurski.JobSearch.tsum_mul_one_sub
#print axioms SargentStachurski.JobSearch.isUnit_one_sub_of_summable
#print axioms SargentStachurski.JobSearch.inv_one_sub_of_summable
#print axioms SargentStachurski.JobSearch.neumann_series
#print axioms SargentStachurski.JobSearch.inv_one_sub_mul
#print axioms SargentStachurski.JobSearch.mul_inv_one_sub
#print axioms SargentStachurski.JobSearch.affine
#print axioms SargentStachurski.JobSearch.isFixedPt_affine_iff
#print axioms SargentStachurski.JobSearch.isFixedPt_affine_inv
#print axioms SargentStachurski.JobSearch.affine_fixedPt_unique
#print axioms SargentStachurski.JobSearch.affine_iterate
#print axioms SargentStachurski.JobSearch.tendsto_affine_iterate
#print axioms SargentStachurski.JobSearch.globallyStable_affine
#print axioms SargentStachurski.JobSearch.isContractionOn_affine
#print axioms SargentStachurski.JobSearch.scalar_neumann
#print axioms SargentStachurski.JobSearch.GloballyStable.tendsto_iterate
#print axioms SargentStachurski.JobSearch.Solow
#print axioms SargentStachurski.JobSearch.Solow.mk
#print axioms SargentStachurski.JobSearch.Solow.A
#print axioms SargentStachurski.JobSearch.Solow.s
#print axioms SargentStachurski.JobSearch.Solow.δ
#print axioms SargentStachurski.JobSearch.Solow.α
#print axioms SargentStachurski.JobSearch.Solow.A_pos
#print axioms SargentStachurski.JobSearch.Solow.s_pos
#print axioms SargentStachurski.JobSearch.Solow.δ_pos
#print axioms SargentStachurski.JobSearch.Solow.δ_lt_one
#print axioms SargentStachurski.JobSearch.Solow.α_pos
#print axioms SargentStachurski.JobSearch.Solow.α_lt_one
#print axioms SargentStachurski.JobSearch.Solow.g
#print axioms SargentStachurski.JobSearch.Solow.kstar
#print axioms SargentStachurski.JobSearch.Solow.one_sub_α_pos
#print axioms SargentStachurski.JobSearch.Solow.one_sub_δ_pos
#print axioms SargentStachurski.JobSearch.Solow.sA_pos
#print axioms SargentStachurski.JobSearch.Solow.kstar_pos
#print axioms SargentStachurski.JobSearch.Solow.δ_mul_div
#print axioms SargentStachurski.JobSearch.Solow.kstar_rpow
#print axioms SargentStachurski.JobSearch.Solow.rpow_mul_rpow
#print axioms SargentStachurski.JobSearch.Solow.g_pos
#print axioms SargentStachurski.JobSearch.Solow.mapsTo_g
#print axioms SargentStachurski.JobSearch.Solow.g_strictMonoOn
#print axioms SargentStachurski.JobSearch.Solow.continuous_g
#print axioms SargentStachurski.JobSearch.Solow.not_isContractionOn_g
#print axioms SargentStachurski.JobSearch.Solow.isFixedPt_kstar
#print axioms SargentStachurski.JobSearch.Solow.g_sub_self
#print axioms SargentStachurski.JobSearch.Solow.le_g_le_of_le_kstar
#print axioms SargentStachurski.JobSearch.Solow.kstar_le_g_le_of_kstar_le
#print axioms SargentStachurski.JobSearch.Solow.eq_kstar_of_isFixedPt
#print axioms SargentStachurski.JobSearch.Solow.iterate_g_pos
#print axioms SargentStachurski.JobSearch.Solow.iterate_le_kstar
#print axioms SargentStachurski.JobSearch.Solow.kstar_le_iterate
#print axioms SargentStachurski.JobSearch.Solow.tendsto_iterate_kstar
#print axioms SargentStachurski.JobSearch.Solow.globallyStable_g
#print axioms SargentStachurski.JobSearch.toVector
#print axioms SargentStachurski.JobSearch.toVector_apply
#print axioms SargentStachurski.JobSearch.toVector_symm_apply
#print axioms SargentStachurski.JobSearch.norm_toVector
#print axioms SargentStachurski.JobSearch.IsDistribution
#print axioms SargentStachurski.JobSearch.IsDistribution.mk
#print axioms SargentStachurski.JobSearch.IsDistribution.nonneg
#print axioms SargentStachurski.JobSearch.IsDistribution.sum_eq_one
#print axioms SargentStachurski.JobSearch.SupportedOn
#print axioms SargentStachurski.JobSearch.expectation
#print axioms SargentStachurski.JobSearch.isDistribution_pointMass
#print axioms SargentStachurski.JobSearch.expectation_pointMass
#print axioms SargentStachurski.JobSearch.expectation_le
#print axioms SargentStachurski.JobSearch.expectation_eq_of_supportedOn
#print axioms SargentStachurski.JobSearch.expectation_lt_of_not_supportedOn
#print axioms SargentStachurski.JobSearch.expectation_maximiser_iff
#print axioms SargentStachurski.JobSearch.IsDistributionOn
#print axioms SargentStachurski.JobSearch.IsDistributionOn.mk
#print axioms SargentStachurski.JobSearch.IsDistributionOn.nonneg
#print axioms SargentStachurski.JobSearch.IsDistributionOn.sum_eq_one
#print axioms SargentStachurski.JobSearch.cdf
#print axioms SargentStachurski.JobSearch.cdf_mono
#print axioms SargentStachurski.JobSearch.cdf_max'
#print axioms SargentStachurski.JobSearch.quantileSet
#print axioms SargentStachurski.JobSearch.quantileSet_subset
#print axioms SargentStachurski.JobSearch.mem_quantileSet
#print axioms SargentStachurski.JobSearch.quantileSet_nonempty
#print axioms SargentStachurski.JobSearch.quantile
#print axioms SargentStachurski.JobSearch.quantile_mem
#print axioms SargentStachurski.JobSearch.quantile_le
#print axioms SargentStachurski.JobSearch.example_1_2_5_cdf
#print axioms SargentStachurski.JobSearch.example_1_2_5_median
#print axioms SargentStachurski.JobSearch.isDistributionOn_shift
#print axioms SargentStachurski.JobSearch.cdf_shift
#print axioms SargentStachurski.JobSearch.quantileSet_shift
#print axioms SargentStachurski.JobSearch.quantile_shift
#print axioms SargentStachurski.JobSearch.Model
#print axioms SargentStachurski.JobSearch.Model.mk
#print axioms SargentStachurski.JobSearch.Model.wage
#print axioms SargentStachurski.JobSearch.Model.wage_nonneg
#print axioms SargentStachurski.JobSearch.Model.φ
#print axioms SargentStachurski.JobSearch.Model.φ_nonneg
#print axioms SargentStachurski.JobSearch.Model.φ_sum
#print axioms SargentStachurski.JobSearch.Model.c
#print axioms SargentStachurski.JobSearch.Model.c_pos
#print axioms SargentStachurski.JobSearch.Model.β
#print axioms SargentStachurski.JobSearch.Model.β_pos
#print axioms SargentStachurski.JobSearch.Model.β_lt_one
#print axioms SargentStachurski.JobSearch.Model.one_sub_β_pos
#print axioms SargentStachurski.JobSearch.Model.β_nonneg
#print axioms SargentStachurski.JobSearch.Model.E
#print axioms SargentStachurski.JobSearch.Model.E_const
#print axioms SargentStachurski.JobSearch.Model.E_mono
#print axioms SargentStachurski.JobSearch.Model.E_le_of_le
#print axioms SargentStachurski.JobSearch.Model.le_E_of_le
#print axioms SargentStachurski.JobSearch.Model.E_nonneg
#print axioms SargentStachurski.JobSearch.Model.E_add
#print axioms SargentStachurski.JobSearch.Model.E_mul
#print axioms SargentStachurski.JobSearch.Model.abs_E_sub_E_le
#print axioms SargentStachurski.JobSearch.Model.annuity
#print axioms SargentStachurski.JobSearch.Model.stopValue
#print axioms SargentStachurski.JobSearch.Model.value
#print axioms SargentStachurski.JobSearch.Model.contValue
#print axioms SargentStachurski.JobSearch.Model.resWage
#print axioms SargentStachurski.JobSearch.Model.annuity_pos
#print axioms SargentStachurski.JobSearch.Model.annuity_zero
#print axioms SargentStachurski.JobSearch.Model.annuity_one
#print axioms SargentStachurski.JobSearch.Model.annuity_two
#print axioms SargentStachurski.JobSearch.Model.value_zero
#print axioms SargentStachurski.JobSearch.Model.contValue_zero
#print axioms SargentStachurski.JobSearch.Model.value_one
#print axioms SargentStachurski.JobSearch.Model.resWage_one
#print axioms SargentStachurski.JobSearch.Model.value_two
#print axioms SargentStachurski.JobSearch.Model.resWage_two
#print axioms SargentStachurski.JobSearch.Model.value_succ
#print axioms SargentStachurski.JobSearch.Model.contValue_le_stopValue_iff
#print axioms SargentStachurski.JobSearch.Model.value_succ_eq_stopValue_iff
#print axioms SargentStachurski.JobSearch.Model.value_succ_eq_contValue_iff
#print axioms SargentStachurski.JobSearch.Model.value_zero_eq_wage_iff
#print axioms SargentStachurski.JobSearch.Model.c_le_value
#print axioms SargentStachurski.JobSearch.Model.value_nonneg
#print axioms SargentStachurski.JobSearch.Model.resWage_pos
#print axioms SargentStachurski.JobSearch.Model.value_le_value_of_c_le
#print axioms SargentStachurski.JobSearch.Model.contValue_le_contValue_of_c_le
#print axioms SargentStachurski.JobSearch.Model.resWage_le_resWage_of_c_le
#print axioms SargentStachurski.JobSearch.V
#print axioms SargentStachurski.JobSearch.V_nonempty
#print axioms SargentStachurski.JobSearch.isClosed_V
#print axioms SargentStachurski.JobSearch.Model.tsum_geometric_wage
#print axioms SargentStachurski.JobSearch.Model.stop
#print axioms SargentStachurski.JobSearch.Model.stop_nonneg
#print axioms SargentStachurski.JobSearch.Model.T
#print axioms SargentStachurski.JobSearch.Model.mapsTo_T
#print axioms SargentStachurski.JobSearch.Model.abs_T_sub_T_le
#print axioms SargentStachurski.JobSearch.Model.norm_T_sub_T_le
#print axioms SargentStachurski.JobSearch.Model.isContractionOn_T
#print axioms SargentStachurski.JobSearch.Model.isContractionOn_T_univ
#print axioms SargentStachurski.JobSearch.Model.vstar
#print axioms SargentStachurski.JobSearch.Model.vstar_mem_V
#print axioms SargentStachurski.JobSearch.Model.vstar_nonneg
#print axioms SargentStachurski.JobSearch.Model.isFixedPt_vstar
#print axioms SargentStachurski.JobSearch.Model.bellman_equation
#print axioms SargentStachurski.JobSearch.Model.eq_vstar_of_isFixedPt
#print axioms SargentStachurski.JobSearch.Model.existsUnique_fixedPt
#print axioms SargentStachurski.JobSearch.Model.tendsto_iterate_T
#print axioms SargentStachurski.JobSearch.Model.norm_iterate_T_sub_vstar_le
#print axioms SargentStachurski.JobSearch.Model.globallyStable_T
#print axioms SargentStachurski.JobSearch.Model.hstar
#print axioms SargentStachurski.JobSearch.Model.vstar_eq_max
#print axioms SargentStachurski.JobSearch.Model.Policy
#print axioms SargentStachurski.JobSearch.Model.IsGreedy
#print axioms SargentStachurski.JobSearch.Model.exists_isGreedy
#print axioms SargentStachurski.JobSearch.Model.reservationWage
#print axioms SargentStachurski.JobSearch.Model.hstar_le_stop_iff
#print axioms SargentStachurski.JobSearch.Model.isGreedy_vstar_iff
#print axioms SargentStachurski.JobSearch.Model.g
#print axioms SargentStachurski.JobSearch.Model.isFixedPt_g_hstar
#print axioms SargentStachurski.JobSearch.Model.g_nonneg
#print axioms SargentStachurski.JobSearch.Model.mapsTo_g
#print axioms SargentStachurski.JobSearch.Model.abs_g_sub_g_le
#print axioms SargentStachurski.JobSearch.Model.isContractionOn_g
#print axioms SargentStachurski.JobSearch.Model.isContractionOn_g_univ
#print axioms SargentStachurski.JobSearch.Model.hstar_nonneg
#print axioms SargentStachurski.JobSearch.Model.eq_hstar_of_isFixedPt_g
#print axioms SargentStachurski.JobSearch.Model.tendsto_iterate_g
#print axioms SargentStachurski.JobSearch.Model.abs_iterate_g_sub_hstar_le
#print axioms SargentStachurski.JobSearch.Model.vstar_eq_max_hstar
#print axioms SargentStachurski.JobSearch.Model.isGreedy_vstar_iff_hstar
#print axioms SargentStachurski.JobSearch.Model.g_mono
#print axioms SargentStachurski.JobSearch.Model.g_le_g_of_c_le
#print axioms SargentStachurski.JobSearch.Model.hstar_le_hstar_of_c_le
#print axioms SargentStachurski.JobSearch.Model.reservationWage_le_of_c_le
