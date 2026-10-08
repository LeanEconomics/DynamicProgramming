/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import JobSearch.FixedPoints
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic

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
