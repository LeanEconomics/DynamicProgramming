/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Separation.Hausdorff

/-!
# Fixed points, global stability and contractions: the Chapter 1 facts used here

Sargent and Stachurski, *Dynamic Programming*, Volume 1, Chapter 2 builds on
the fixed-point vocabulary of §1.2.2: global stability (p. 22), contractions
(1.17) and Banach's theorem (Theorem 1.2.3). Each chapter project is
self-contained, so the definitions are restated here with the facts the
chapter uses, proved afresh from Mathlib (`ContractingWith`) rather than along
the book's exercise route, which is the `FiniteStates/JobSearch` project's job.
-/

open Filter Topology Function Set

namespace SargentStachurski.OperatorsFixedPoints

variable {U : Type*}

/-- Global stability (Vol. 1, p. 22): a unique fixed point `u*` to which every orbit converges. -/
def GloballyStable [TopologicalSpace U] (T : U → U) : Prop :=
  ∃ u' : U, IsFixedPt T u' ∧ (∀ v, IsFixedPt T v → v = u') ∧
    ∀ u, Tendsto (fun k : ℕ => T^[k] u) atTop (𝓝 u')

/-- In a Hausdorff space uniqueness follows from convergence of every orbit. -/
theorem globallyStable_of_tendsto [TopologicalSpace U] [T2Space U] {T : U → U} {u' : U}
    (hfix : IsFixedPt T u') (hlim : ∀ u, Tendsto (fun k : ℕ => T^[k] u) atTop (𝓝 u')) :
    GloballyStable T := by
  refine ⟨u', hfix, fun v hv => ?_, hlim⟩
  have hconst : Tendsto (fun k : ℕ => T^[k] v) atTop (𝓝 v) := by
    have : (fun k : ℕ => T^[k] v) = fun _ => v := funext fun k => IsFixedPt.iterate hv k
    rw [this]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hconst (hlim v)

/-- The orbit of a globally stable map converges to its fixed point. -/
theorem GloballyStable.tendsto_iterate [TopologicalSpace U] {T : U → U} (h : GloballyStable T)
    {u' : U} (hu' : IsFixedPt T u') (u : U) : Tendsto (fun k : ℕ => T^[k] u) atTop (𝓝 u') := by
  obtain ⟨u₀, -, huniq, hlim⟩ := h
  rw [huniq u' hu']
  exact hlim u

/-- A globally stable map has a fixed point. -/
theorem GloballyStable.exists_fixedPt [TopologicalSpace U] {T : U → U} (h : GloballyStable T) :
    ∃ u', IsFixedPt T u' := by
  obtain ⟨u', hfix, -, -⟩ := h
  exact ⟨u', hfix⟩

/-- Fixed points of a globally stable map are unique. -/
theorem GloballyStable.fixedPt_unique [TopologicalSpace U] {T : U → U} (h : GloballyStable T)
    {u v : U} (hu : IsFixedPt T u) (hv : IsFixedPt T v) : u = v := by
  obtain ⟨u', -, huniq, -⟩ := h
  rw [huniq u hu, huniq v hv]

variable {E : Type*} [NormedAddCommGroup E]

/-- A contraction of modulus `L` on `U` in the norm of `E`, Vol. 1 (1.17), p. 22. -/
structure IsContractionOn (T : E → E) (U : Set E) (L : ℝ) : Prop where
  mapsTo : MapsTo T U U
  nonneg : 0 ≤ L
  lt_one : L < 1
  norm_sub_le : ∀ u ∈ U, ∀ v ∈ U, ‖T u - T v‖ ≤ L * ‖u - v‖

namespace IsContractionOn

variable {T : E → E} {U : Set E} {L : ℝ}

/-- At most one fixed point in `U` (Vol. 1, Ex 1.2.19). -/
theorem fixedPt_unique (h : IsContractionOn T U L) {u v : E} (hu : u ∈ U) (hv : v ∈ U)
    (hfu : IsFixedPt T u) (hfv : IsFixedPt T v) : u = v := by
  have hb := h.norm_sub_le u hu v hv
  rw [hfu.eq, hfv.eq] at hb
  have hnn : 0 ≤ ‖u - v‖ := norm_nonneg _
  have hpos : 0 < 1 - L := by linarith [h.lt_one]
  have : ‖u - v‖ ≤ 0 := by nlinarith
  exact sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm this hnn))

theorem iterate_mem (h : IsContractionOn T U L) {u : E} (hu : u ∈ U) (k : ℕ) : T^[k] u ∈ U := by
  induction k with
  | zero => simpa using hu
  | succ k ih => rw [iterate_succ_apply']; exact h.mapsTo ih

/-- The rate (1.18): `‖Tᵏu − u*‖ ≤ Lᵏ‖u − u*‖` for a fixed point `u*` in `U`. -/
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

/-- Orbits converge to a fixed point in `U`. -/
theorem tendsto_iterate_fixedPt (h : IsContractionOn T U L) {u u' : E} (hu : u ∈ U) (hu' : u' ∈ U)
    (hfix : IsFixedPt T u') : Tendsto (fun k : ℕ => T^[k] u) atTop (𝓝 u') := by
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [dist_eq_norm]
  refine squeeze_zero (fun _ => norm_nonneg _) (h.norm_iterate_sub_fixedPt_le hu hu' hfix) ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h.nonneg h.lt_one).mul_const ‖u - u'‖

/-- Banach's theorem (Vol. 1, Theorem 1.2.3), existence, from Mathlib's `ContractingWith` on the
closed subtype. -/
theorem exists_fixedPt [CompleteSpace E] (h : IsContractionOn T U L) (hU : IsClosed U)
    (hne : U.Nonempty) : ∃ u' ∈ U, IsFixedPt T u' := by
  have : CompleteSpace U := hU.completeSpace_coe
  have : Nonempty U := hne.to_subtype
  let T' : U → U := h.mapsTo.restrict T U U
  have hT' : ContractingWith ⟨L, h.nonneg⟩ T' := by
    refine ⟨by exact_mod_cast h.lt_one, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [T', MapsTo.val_restrict_apply, Subtype.dist_eq, dist_eq_norm]
    exact h.norm_sub_le x x.2 y y.2
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : U, IsFixedPt T' u₀ := ⟨_, hT'.fixedPoint_isFixedPt⟩
  exact ⟨u₀.1, u₀.2, congrArg Subtype.val hu₀⟩

/-- Banach's theorem: a contraction on a nonempty closed set is globally stable there, as a
self-map of the subtype. -/
theorem globallyStable [CompleteSpace E] (h : IsContractionOn T U L) (hU : IsClosed U)
    (hne : U.Nonempty) : GloballyStable (h.mapsTo.restrict T U U) := by
  obtain ⟨u', hu', hfix⟩ := h.exists_fixedPt hU hne
  have hiter : ∀ (u : U) (k : ℕ), ((h.mapsTo.restrict T U U)^[k] u : E) = T^[k] u := by
    intro u k
    rw [MapsTo.iterate_restrict]
    rfl
  refine globallyStable_of_tendsto (u' := ⟨u', hu'⟩) ?_ fun u => ?_
  · exact Subtype.ext (by simpa [MapsTo.val_restrict_apply] using hfix.eq)
  · rw [tendsto_subtype_rng]
    simp only [hiter]
    exact h.tendsto_iterate_fixedPt u.2 hu' hfix

/-- A contraction on the whole space is globally stable. -/
theorem globallyStable_univ [CompleteSpace E] (h : IsContractionOn T univ L) :
    GloballyStable T := by
  obtain ⟨u', -, hfix⟩ := h.exists_fixedPt isClosed_univ univ_nonempty
  exact globallyStable_of_tendsto hfix fun u => h.tendsto_iterate_fixedPt trivial trivial hfix

end IsContractionOn

/-- Local stability (§2.1.2, p. 45): some open set `O ∋ u*` lies in the domain of attraction. -/
def LocallyStable [TopologicalSpace U] (T : U → U) (u' : U) : Prop :=
  ∃ O : Set U, IsOpen O ∧ u' ∈ O ∧ ∀ u ∈ O, Tendsto (fun k : ℕ => T^[k] u) atTop (𝓝 u')

/-- A globally stable map's fixed point is locally stable. -/
theorem GloballyStable.locallyStable [TopologicalSpace U] {T : U → U} (h : GloballyStable T)
    {u' : U} (hu' : IsFixedPt T u') : LocallyStable T u' :=
  ⟨univ, isOpen_univ, trivial, fun u _ => h.tendsto_iterate hu' u⟩

end SargentStachurski.OperatorsFixedPoints
