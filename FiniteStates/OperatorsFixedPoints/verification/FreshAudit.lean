import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.RelClasses
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Lattice
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Bounds.Image
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.WellFounded
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.LinearAlgebra.Matrix.Notation
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Conjugate maps and local stability

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §2.1.1–§2.1.2
(pp. 42–46).

A dynamical system is a set with a self-map; `(U, T)` and `(Û, T̂)` are
conjugate under a bijection `Φ : U → Û` if `T = Φ⁻¹ ∘ T̂ ∘ Φ`. Conjugacy
transports fixed points (Exercise 2.1.1, Proposition 2.1.1); topological
conjugacy, where `Φ` is a homeomorphism, also transports convergence of
orbits (Exercise 2.1.4), global stability (Proposition 2.1.2) and local
stability (Exercise 2.1.6), and is an equivalence relation (Exercise 2.1.5).

Local stability is defined in `Basics`. Example 2.1.4 treats `g(x) = x²`, and
the one-dimensional derivative criterion that the book sketches on p. 45
(`|g'(x*)| < 1` implies local stability) is proved by the mean value theorem.
The Hartman–Grobman theorem (Theorem 2.1.3) and its Corollary 2.1.4 are
quoted by the book without proof and are not claimed here.
-/

open Filter Topology Function Set Matrix

universe u v w

namespace SargentStachurski.OperatorsFixedPoints

variable {U : Type u} {V : Type v} {W : Type w}

/-- `(U, T)` and `(V, T')` are conjugate under the bijection `Φ` (p. 43): `T = Φ⁻¹ ∘ T' ∘ Φ`. -/
def IsConjugate (T : U → U) (T' : V → V) (Φ : U ≃ V) : Prop :=
  ∀ u, T u = Φ.symm (T' (Φ u))

namespace IsConjugate

variable {T : U → U} {T' : V → V} {Φ : U ≃ V}

/-- Conjugacy as the commuting square `Φ ∘ T = T' ∘ Φ`. -/
theorem comm (h : IsConjugate T T' Φ) (u : U) : Φ (T u) = T' (Φ u) := by
  rw [h u, Equiv.apply_symm_apply]

theorem of_comm (h : ∀ u, Φ (T u) = T' (Φ u)) : IsConjugate T T' Φ := fun u => by
  rw [← h u, Equiv.symm_apply_apply]

/-- Conjugacy is symmetric: `(V, T')` is conjugate to `(U, T)` under `Φ⁻¹`. -/
theorem symm (h : IsConjugate T T' Φ) : IsConjugate T' T Φ.symm :=
  of_comm fun v => by
    rw [h (Φ.symm v), Equiv.apply_symm_apply]

/-- Conjugacy is transitive. -/
theorem trans {T'' : W → W} {Ψ : V ≃ W} (h₁ : IsConjugate T T' Φ) (h₂ : IsConjugate T' T'' Ψ) :
    IsConjugate T T'' (Φ.trans Ψ) :=
  of_comm fun u => by
    simp only [Equiv.trans_apply]
    rw [h₁.comm, h₂.comm]

/-- Conjugacy is reflexive. -/
theorem refl (T : U → U) : IsConjugate T T (Equiv.refl U) := fun _ => rfl

/-- The square commutes for iterates: `Φ ∘ Tᵏ = T'ᵏ ∘ Φ` (the step in the solution to
Exercise 2.1.4). -/
theorem iterate_comm (h : IsConjugate T T' Φ) (k : ℕ) (u : U) : Φ (T^[k] u) = T'^[k] (Φ u) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ_apply', iterate_succ_apply', h.comm, ih]

/-- Exercise 2.1.1 (p. 43): `u` is a fixed point of `T` iff `Φu` is a fixed point of `T'`. -/
theorem isFixedPt_iff (h : IsConjugate T T' Φ) (u : U) : IsFixedPt T u ↔ IsFixedPt T' (Φ u) := by
  simp only [IsFixedPt]
  rw [h u, Equiv.symm_apply_eq]

/-- Proposition 2.1.1 (ii), p. 44: `v` is a fixed point of `T'` iff `Φ⁻¹v` is a fixed point of
`T`. -/
theorem isFixedPt_symm_iff (h : IsConjugate T T' Φ) (v : V) :
    IsFixedPt T' v ↔ IsFixedPt T (Φ.symm v) := by
  rw [h.isFixedPt_iff, Equiv.apply_symm_apply]

/-- Exercise 2.1.2 (p. 43): `Φ` restricts to a bijection from `fix(T)` to `fix(T')`. -/
def fixedPointsEquiv (h : IsConjugate T T' Φ) : fixedPoints T ≃ fixedPoints T' where
  toFun u := ⟨Φ u, (h.isFixedPt_iff u).1 u.2⟩
  invFun v := ⟨Φ.symm v, (h.isFixedPt_symm_iff v).1 v.2⟩
  left_inv u := Subtype.ext (Equiv.symm_apply_apply Φ u)
  right_inv v := Subtype.ext (Equiv.apply_symm_apply Φ v)

/-- Proposition 2.1.1 (iii), p. 44: the fixed-point sets have the same cardinality. -/
theorem cardinal_fixedPoints_eq (h : IsConjugate T T' Φ) :
    Cardinal.lift.{v} (Cardinal.mk (fixedPoints T)) =
      Cardinal.lift.{u} (Cardinal.mk (fixedPoints T')) :=
  Cardinal.lift_mk_eq'.2 ⟨h.fixedPointsEquiv⟩

/-- Proposition 2.1.1, "in particular" (p. 44): `T` has a unique fixed point iff `T'` does. -/
theorem existsUnique_fixedPt_iff (h : IsConjugate T T' Φ) :
    (∃! u, IsFixedPt T u) ↔ ∃! v, IsFixedPt T' v := by
  constructor
  · rintro ⟨u, hu, huniq⟩
    refine ⟨Φ u, (h.isFixedPt_iff u).1 hu, fun v hv => ?_⟩
    rw [← huniq (Φ.symm v) ((h.isFixedPt_symm_iff v).1 hv), Equiv.apply_symm_apply]
  · rintro ⟨v, hv, hvuniq⟩
    refine ⟨Φ.symm v, (h.isFixedPt_symm_iff v).1 hv, fun u hu => ?_⟩
    rw [← hvuniq (Φ u) ((h.isFixedPt_iff u).1 hu), Equiv.symm_apply_apply]

end IsConjugate

/-- Example 2.1.1 (p. 43): if `A = P⁻¹ D P` with `P` invertible, then `u ↦ Au` on `ℝⁿ` is
conjugate to `v ↦ Dv` under `Φ = P`. The book takes `D` diagonal (and complex); the conjugacy
needs neither. -/
theorem isConjugate_similar {n : ℕ} (P D : Matrix (Fin n) (Fin n) ℝ) (hP : IsUnit P.det) :
    IsConjugate (fun u => (P⁻¹ * D * P) *ᵥ u) (fun v => D *ᵥ v)
      ⟨fun u => P *ᵥ u, fun v => P⁻¹ *ᵥ v,
        fun u => by
          change P⁻¹ *ᵥ (P *ᵥ u) = u
          rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul P hP, Matrix.one_mulVec],
        fun v => by
          change P *ᵥ (P⁻¹ *ᵥ v) = v
          rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hP, Matrix.one_mulVec]⟩ :=
  IsConjugate.of_comm fun u => by
    simp only [Equiv.coe_fn_mk]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv P hP, Matrix.one_mul]

/-! ### Topological conjugacy (§2.1.1.2, p. 44) -/

/-- `(U, T)` and `(V, T')` are topologically conjugate under the homeomorphism `Φ`. -/
def IsTopConjugate [TopologicalSpace U] [TopologicalSpace V] (T : U → U) (T' : V → V)
    (Φ : U ≃ₜ V) : Prop :=
  IsConjugate T T' Φ.toEquiv

namespace IsTopConjugate

variable [TopologicalSpace U] [TopologicalSpace V] [TopologicalSpace W] {T : U → U} {T' : V → V}
  {Φ : U ≃ₜ V}

/-- Exercise 2.1.5 (p. 44): topological conjugacy is reflexive. -/
theorem refl (T : U → U) : IsTopConjugate T T (Homeomorph.refl U) := fun _ => rfl

/-- Exercise 2.1.5 (p. 44): topological conjugacy is symmetric. -/
theorem symm (h : IsTopConjugate T T' Φ) : IsTopConjugate T' T Φ.symm :=
  IsConjugate.symm h

/-- Exercise 2.1.5 (p. 44): topological conjugacy is transitive. -/
theorem trans {T'' : W → W} {Ψ : V ≃ₜ W} (h₁ : IsTopConjugate T T' Φ)
    (h₂ : IsTopConjugate T' T'' Ψ) : IsTopConjugate T T'' (Φ.trans Ψ) :=
  IsConjugate.trans h₁ h₂

/-- Exercise 2.1.4 (p. 44): `Tᵏu → u*` iff `T'ᵏ(Φu) → Φu*`. -/
theorem tendsto_iterate_iff (h : IsTopConjugate T T' Φ) (u u' : U) :
    Tendsto (fun k : ℕ => T^[k] u) atTop (𝓝 u') ↔
      Tendsto (fun k : ℕ => T'^[k] (Φ u)) atTop (𝓝 (Φ u')) := by
  have : (fun k : ℕ => T'^[k] (Φ u)) = Φ ∘ fun k : ℕ => T^[k] u := by
    funext k
    exact (IsConjugate.iterate_comm h k u).symm
  rw [this, Φ.isInducing.tendsto_nhds_iff]

/-- Proposition 2.1.2 (p. 45): `T` is globally stable on `U` iff `T'` is globally stable on
`V`, and the fixed points correspond under `Φ`. -/
theorem globallyStable_iff (h : IsTopConjugate T T' Φ) : GloballyStable T ↔ GloballyStable T' := by
  constructor
  · rintro ⟨u', hfix, huniq, hlim⟩
    refine ⟨Φ u', (IsConjugate.isFixedPt_iff h u').1 hfix, fun v hv => ?_, fun v => ?_⟩
    · rw [← huniq (Φ.symm v) ((IsConjugate.isFixedPt_symm_iff h v).1 hv),
        Homeomorph.apply_symm_apply]
    · have := (h.tendsto_iterate_iff (Φ.symm v) u').1 (hlim _)
      simpa using this
  · rintro ⟨v', hfix, huniq, hlim⟩
    have h'' : IsTopConjugate T' T Φ.symm := h.symm
    refine ⟨Φ.symm v', (IsConjugate.isFixedPt_symm_iff h v').1 hfix, fun u hu => ?_, fun u => ?_⟩
    · rw [← huniq (Φ u) ((IsConjugate.isFixedPt_iff h u).1 hu), Homeomorph.symm_apply_apply]
    · have := (h''.tendsto_iterate_iff (Φ u) v').1 (hlim _)
      simpa using this

/-- Proposition 2.1.2 (ii), p. 45: the unique fixed points satisfy `û* = Φu*`. -/
theorem fixedPt_map (h : IsTopConjugate T T' Φ) {u' : U} (hu : IsFixedPt T u') :
    IsFixedPt T' (Φ u') :=
  (IsConjugate.isFixedPt_iff h u').1 hu

/-- Exercise 2.1.6 (p. 45): `u*` is locally stable for `(U, T)` iff `Φu*` is locally stable for
`(V, T')`. -/
theorem locallyStable_iff (h : IsTopConjugate T T' Φ) (u' : U) :
    LocallyStable T u' ↔ LocallyStable T' (Φ u') := by
  constructor
  · rintro ⟨O, hO, hu', hconv⟩
    refine ⟨Φ '' O, Φ.isOpenMap O hO, ⟨u', hu', rfl⟩, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    exact (h.tendsto_iterate_iff u u').1 (hconv u hu)
  · rintro ⟨O, hO, hu', hconv⟩
    refine ⟨Φ ⁻¹' O, hO.preimage Φ.continuous, hu', fun u hu => ?_⟩
    exact (h.tendsto_iterate_iff u u').2 (hconv (Φ u) hu)

end IsTopConjugate

/-- Example 2.1.2 (p. 44): `ln : (0, ∞) → ℝ` is a homeomorphism with inverse `exp`. -/
noncomputable def logHomeomorph : Ioi (0 : ℝ) ≃ₜ ℝ :=
  Real.expOrderIso.toHomeomorph.symm

theorem logHomeomorph_apply (u : Ioi (0 : ℝ)) : logHomeomorph u = Real.log u := by
  change Real.expOrderIso.symm u = Real.log u
  rw [OrderIso.symm_apply_eq]
  exact Subtype.ext (by rw [Real.coe_expOrderIso_apply, Real.exp_log u.2])

theorem logHomeomorph_symm_apply (y : ℝ) : (logHomeomorph.symm y : ℝ) = Real.exp y := by
  change ((Real.expOrderIso y : Ioi (0 : ℝ)) : ℝ) = Real.exp y
  exact Real.coe_expOrderIso_apply y

/-- Example 2.1.3 (p. 44), one direction: a nonsingular matrix `Φ` acts as a homeomorphism of
`ℝⁿ`. -/
noncomputable def matrixHomeomorph {n : ℕ} (Φ : Matrix (Fin n) (Fin n) ℝ) (hΦ : IsUnit Φ.det) :
    (Fin n → ℝ) ≃ₜ (Fin n → ℝ) where
  toFun u := Φ *ᵥ u
  invFun v := Φ⁻¹ *ᵥ v
  left_inv u := by
    change Φ⁻¹ *ᵥ (Φ *ᵥ u) = u
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul Φ hΦ, Matrix.one_mulVec]
  right_inv v := by
    change Φ *ᵥ (Φ⁻¹ *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Φ hΦ, Matrix.one_mulVec]
  continuous_toFun := (Matrix.mulVecLin Φ).continuous_of_finiteDimensional
  continuous_invFun := (Matrix.mulVecLin Φ⁻¹).continuous_of_finiteDimensional

/-- Example 2.1.3 (p. 44), the other direction: if `u ↦ Φu` is a bijection of `ℝⁿ` then `Φ`
is nonsingular (a singular matrix has a nonzero null vector). -/
theorem det_ne_zero_of_mulVec_injective {n : ℕ} (Φ : Matrix (Fin n) (Fin n) ℝ)
    (h : Injective fun u : Fin n → ℝ => Φ *ᵥ u) :
    Φ.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hΦv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  apply hv
  apply h
  simp only [hΦv, Matrix.mulVec_zero]

/-- Exercise 2.1.3 (p. 44): `Tu = Auᵅ` on `(0, ∞)` is topologically conjugate to
`T̂v = ln A + αv` on `ℝ` under `Φ = ln`. -/
theorem isTopConjugate_power {A α : ℝ} (hA : 0 < A) :
    IsTopConjugate
      (fun u : Ioi (0 : ℝ) => ⟨A * (u : ℝ) ^ α, mul_pos hA (Real.rpow_pos_of_pos u.2 α)⟩)
      (fun v : ℝ => Real.log A + α * v) logHomeomorph :=
  IsConjugate.of_comm fun u => by
    simp only [Homeomorph.coe_toEquiv, logHomeomorph_apply]
    rw [Real.log_mul hA.ne' (Real.rpow_pos_of_pos u.2 α).ne', Real.log_rpow u.2]

/-! ### Local stability (§2.1.2, p. 45) -/

/-- The iterates of `g(x) = x²` are `x^(2ᵏ)`. -/
theorem iterate_sq (x : ℝ) (k : ℕ) : (fun y : ℝ => y ^ 2)^[k] x = x ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [iterate_succ_apply', ih, ← pow_mul, pow_succ]

/-- Example 2.1.4 (p. 45): `0` is a locally stable fixed point of `g(x) = x²`, since `|x| < 1`
implies `gᵗ(x) → 0`. -/
theorem locallyStable_sq_zero : LocallyStable (fun y : ℝ => y ^ 2) 0 := by
  refine ⟨Ioo (-1) 1, isOpen_Ioo, by norm_num, fun x hx => ?_⟩
  simp only [iterate_sq]
  have habs : |x| < 1 := abs_lt.2 ⟨hx.1, hx.2⟩
  have h1 : Tendsto (fun k : ℕ => |x| ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg x) habs
  have h2 : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have h3 : Tendsto (fun k : ℕ => |x| ^ (2 ^ k)) atTop (𝓝 0) := h1.comp h2
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [Real.norm_eq_abs, abs_pow] using h3

/-- Example 2.1.4 (p. 45): `1` is a fixed point of `g(x) = x²` that is not locally stable, since
`gᵗ(x) → ∞` for every `x > 1`. -/
theorem not_locallyStable_sq_one : ¬ LocallyStable (fun y : ℝ => y ^ 2) 1 := by
  rintro ⟨O, hO, h1, hconv⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO 1 h1
  set x : ℝ := 1 + ε / 2 with hx
  have hxO : x ∈ O := hball (by
    rw [Metric.mem_ball, Real.dist_eq, hx]
    rw [show (1 + ε / 2 - 1) = ε / 2 by ring, abs_of_pos (by linarith)]
    linarith)
  have hlim := hconv x hxO
  simp only [iterate_sq] at hlim
  have hgt : 1 < x := by rw [hx]; linarith
  have hdiv : Tendsto (fun k : ℕ => x ^ (2 ^ k)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hgt).comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  exact not_tendsto_atTop_of_tendsto_nhds hlim hdiv

/-- The derivative criterion sketched on p. 45: if `g` is differentiable with continuous
derivative at a fixed point `x*` and `|g'(x*)| < 1`, then `x*` is locally stable. The proof is the
one the book describes: near `x*`, `g` is a contraction of modulus `λ ∈ (|g'(x*)|, 1)`, by the
mean value theorem. -/
theorem locallyStable_of_abs_deriv_lt_one {g g' : ℝ → ℝ} {x' : ℝ}
    (hg : ∀ x, HasDerivAt g (g' x) x) (hcont : ContinuousAt g' x') (hfix : g x' = x')
    (hlt : |g' x'| < 1) : LocallyStable g x' := by
  obtain ⟨L, hL1, hL2⟩ := exists_between hlt
  have hL0 : 0 ≤ L := (abs_nonneg _).trans hL1.le
  -- a ball on which `|g'| ≤ L`
  have hev : ∀ᶠ x in 𝓝 x', |g' x| < L := hcont.abs.eventually (gt_mem_nhds hL1)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hbound : ∀ x ∈ Metric.ball x' δ, ‖g' x‖ ≤ L := fun x hx => (hball (Metric.mem_ball.1 hx)).le
  have hderiv : ∀ x ∈ Metric.ball x' δ, HasDerivWithinAt g (g' x) (Metric.ball x' δ) x :=
    fun x _ => (hg x).hasDerivWithinAt
  -- `g` is `L`-Lipschitz on the ball, and fixes `x'`
  have hlip : ∀ x ∈ Metric.ball x' δ, |g x - x'| ≤ L * |x - x'| := by
    intro x hx
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound (convex_ball x' δ)
      (Metric.mem_ball_self hδ) hx
    rwa [hfix, Real.norm_eq_abs, Real.norm_eq_abs] at this
  have hmaps : ∀ x ∈ Metric.ball x' δ, g x ∈ Metric.ball x' δ := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq] at hx ⊢
    calc |g x - x'| ≤ L * |x - x'| := hlip x hx
      _ ≤ 1 * |x - x'| := mul_le_mul_of_nonneg_right hL2.le (abs_nonneg _)
      _ < δ := by linarith
  have hiter : ∀ x ∈ Metric.ball x' δ, ∀ k : ℕ,
      g^[k] x ∈ Metric.ball x' δ ∧ |g^[k] x - x'| ≤ L ^ k * |x - x'| := by
    intro x hx k
    induction k with
    | zero => exact ⟨by simpa using hx, by simp⟩
    | succ k ih =>
      rw [iterate_succ_apply']
      refine ⟨hmaps _ ih.1, ?_⟩
      calc |g (g^[k] x) - x'| ≤ L * |g^[k] x - x'| := hlip _ ih.1
        _ ≤ L * (L ^ k * |x - x'|) := mul_le_mul_of_nonneg_left ih.2 hL0
        _ = L ^ (k + 1) * |x - x'| := by ring
  refine ⟨Metric.ball x' δ, Metric.isOpen_ball, Metric.mem_ball_self hδ, fun x hx => ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [Real.dist_eq]
  refine squeeze_zero (fun _ => abs_nonneg _) (fun k => (hiter x hx k).2) ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hL0 hL2).mul_const |x - x'|

end SargentStachurski.OperatorsFixedPoints

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Convergence rates and Newton's fixed-point iteration

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §2.1.3–§2.1.4
(pp. 46–51).

A sequence converges to `u*` at rate at least `q` if `eₖ₊₁ ≤ β eₖ^q`
eventually, where `eₖ = ‖uₖ − u*‖`; `q = 1` with `β < 1` is linear
convergence, `q = 2` quadratic. Example 2.1.5: the orbit of a contraction
converges at least linearly. Exercise 2.1.7: for a differentiable self-map of
an interval, the ratio `eₖ₊₁/eₖ` converges to `|T'(u*)|`, so the rate is
linear when `0 < |T'(u*)| < 1`. The book assumes `T` twice continuously
differentiable and uses a second-order Taylor expansion; a continuous first
derivative suffices, and that is what is assumed here.

Newton's fixed-point iteration (2.2) is defined in one dimension, where the
Jacobian is the derivative, and shown to have the same fixed points as `T`.
Its quadratic convergence, which the book cites from Atkinson and Han (2005),
is not claimed.
-/

open Filter Topology Function Set

namespace SargentStachurski.OperatorsFixedPoints

variable {E : Type*} [NormedAddCommGroup E]

/-- Convergence of `(uₖ)` to `u*` at rate at least `q` (p. 46): `q ≥ 1` and, for some `β > 0`,
`eₖ₊₁ ≤ β eₖ^q` for all large `k`, where `eₖ = ‖uₖ − u*‖`. -/
def ConvergesAtRateAtLeast (u : ℕ → E) (u' : E) (q β : ℝ) : Prop :=
  1 ≤ q ∧ 0 < β ∧ ∃ N : ℕ, ∀ k ≥ N, ‖u (k + 1) - u'‖ ≤ β * ‖u k - u'‖ ^ q

/-- Linear convergence (p. 46): rate at least `1` with `β < 1`. -/
def ConvergesLinearly (u : ℕ → E) (u' : E) : Prop :=
  ∃ β : ℝ, β < 1 ∧ ConvergesAtRateAtLeast u u' 1 β

/-- Quadratic convergence (p. 46): rate at least `2`. -/
def ConvergesQuadratically (u : ℕ → E) (u' : E) : Prop :=
  ∃ β : ℝ, ConvergesAtRateAtLeast u u' 2 β

/-- Example 2.1.5 (p. 46): the orbit of a contraction of modulus `λ ∈ (0, 1)` converges to the
fixed point at least linearly, since `eₖ₊₁ = ‖Tuₖ − Tu*‖ ≤ λeₖ`. -/
theorem IsContractionOn.convergesAtRateAtLeast {T : E → E} {U : Set E} {L : ℝ}
    (h : IsContractionOn T U L) (hL : 0 < L) {u₀ u' : E} (hu₀ : u₀ ∈ U) (hu' : u' ∈ U)
    (hfix : IsFixedPt T u') : ConvergesAtRateAtLeast (fun k => T^[k] u₀) u' 1 L := by
  refine ⟨le_rfl, hL, 0, fun k _ => ?_⟩
  change ‖T^[k + 1] u₀ - u'‖ ≤ L * ‖T^[k] u₀ - u'‖ ^ (1 : ℝ)
  rw [Real.rpow_one, iterate_succ_apply']
  calc ‖T (T^[k] u₀) - u'‖ = ‖T (T^[k] u₀) - T u'‖ := by rw [hfix.eq]
    _ ≤ L * ‖T^[k] u₀ - u'‖ := h.norm_sub_le _ (h.iterate_mem hu₀ k) _ hu'

theorem IsContractionOn.convergesLinearly {T : E → E} {U : Set E} {L : ℝ}
    (h : IsContractionOn T U L) (hL : 0 < L) {u₀ u' : E} (hu₀ : u₀ ∈ U) (hu' : u' ∈ U)
    (hfix : IsFixedPt T u') : ConvergesLinearly (fun k => T^[k] u₀) u' :=
  ⟨L, h.lt_one, h.convergesAtRateAtLeast hL hu₀ hu' hfix⟩

/-- The one-dimensional estimate behind Exercise 2.1.7: near a fixed point `u*` of a
differentiable `T` whose derivative is continuous at `u*`, the error ratio is within `ε` of
`|T'(u*)|`. The proof applies the mean value inequality to `x ↦ Tx − T'(u*)x`, whose derivative
is small near `u*`. -/
theorem error_ratio_near {T T' : ℝ → ℝ} {u' : ℝ} (hT : ∀ x, HasDerivAt T (T' x) x)
    (hcont : ContinuousAt T' u') (hfix : T u' = u') {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x, |x - u'| < δ →
      |T' u'| * |x - u'| - ε * |x - u'| ≤ |T x - u'| ∧
        |T x - u'| ≤ |T' u'| * |x - u'| + ε * |x - u'| := by
  have hev : ∀ᶠ x in 𝓝 u', |T' x - T' u'| < ε := by
    have := Metric.tendsto_nhds.1 hcont ε hε
    simpa [Real.dist_eq] using this
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨δ, hδ, fun x hx => ?_⟩
  set B := Metric.ball u' δ with hB
  have hxB : x ∈ B := by rwa [hB, Metric.mem_ball, Real.dist_eq]
  have hu'B : u' ∈ B := Metric.mem_ball_self hδ
  -- the auxiliary map `F x = T x − T'(u*) x` has derivative `T' x − T'(u*)`, of size `< ε` on `B`
  have hF : ∀ y ∈ B, HasDerivWithinAt (fun y => T y - T' u' * y) (T' y - T' u') B y :=
    fun y _ => ((hT y).sub ((hasDerivAt_id y).const_mul (T' u'))).hasDerivWithinAt |>.congr_deriv
      (by ring)
  have hbound : ∀ y ∈ B, ‖T' y - T' u'‖ ≤ ε := fun y hy =>
    (hball (by rwa [← Metric.mem_ball])).le
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hF hbound (convex_ball u' δ)
    hu'B hxB
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  -- `|T x − u* − T'(u*)(x − u*)| ≤ ε|x − u*|`
  have hlin : |T x - u' - T' u' * (x - u')| ≤ ε * |x - u'| := by
    have : T x - T' u' * x - (T u' - T' u' * u') = T x - u' - T' u' * (x - u') := by
      rw [hfix]; ring
    rwa [this] at hmvt
  constructor
  · have := abs_sub_abs_le_abs_sub (T' u' * (x - u')) (T x - u')
    rw [abs_mul, abs_sub_comm (T' u' * (x - u'))] at this
    linarith
  · have := abs_sub_abs_le_abs_sub (T x - u') (T' u' * (x - u'))
    rw [abs_mul] at this
    linarith

/-- Exercise 2.1.7 (p. 47): if `uₖ → u*` with `uₖ ≠ u*` for all `k`, then `eₖ₊₁/eₖ → |T'(u*)|`. -/
theorem tendsto_error_ratio {T T' : ℝ → ℝ} {u' : ℝ} (hT : ∀ x, HasDerivAt T (T' x) x)
    (hcont : ContinuousAt T' u') (hfix : T u' = u') {u : ℕ → ℝ} (hu : ∀ k, u (k + 1) = T (u k))
    (hne : ∀ k, u k ≠ u') (hlim : Tendsto u atTop (𝓝 u')) :
    Tendsto (fun k => |u (k + 1) - u'| / |u k - u'|) atTop (𝓝 |T' u'|) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := error_ratio_near hT hcont hfix (half_pos hε)
  have hev : ∀ᶠ k in atTop, |u k - u'| < δ := by
    have := Metric.tendsto_atTop.1 hlim δ hδ
    simpa [Real.dist_eq] using this
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun k hk => ?_⟩
  have hpos : 0 < |u k - u'| := abs_pos.2 (sub_ne_zero.2 (hne k))
  obtain ⟨h1, h2⟩ := hδε (u k) (hN k hk)
  rw [hu k] at *
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor
  · rw [div_sub' hpos.ne', div_lt_iff₀ hpos]
    nlinarith
  · rw [sub_div' hpos.ne', div_lt_iff₀ hpos]
    nlinarith

/-- Exercise 2.1.7 (p. 47), conclusion: when `0 < |T'(u*)| < 1` the convergence is linear, with
any `β ∈ (|T'(u*)|, 1)` as the constant. -/
theorem convergesLinearly_of_abs_deriv_lt_one {T T' : ℝ → ℝ} {u' : ℝ}
    (hT : ∀ x, HasDerivAt T (T' x) x) (hcont : ContinuousAt T' u') (hfix : T u' = u')
    {u : ℕ → ℝ} (hu : ∀ k, u (k + 1) = T (u k)) (hne : ∀ k, u k ≠ u')
    (hlim : Tendsto u atTop (𝓝 u')) (hlt : |T' u'| < 1) : ConvergesLinearly u u' := by
  obtain ⟨β, hβ1, hβ2⟩ := exists_between hlt
  have hβ0 : 0 < β := (abs_nonneg _).trans_lt hβ1
  refine ⟨β, hβ2, le_rfl, hβ0, ?_⟩
  have hev : ∀ᶠ k in atTop, |u (k + 1) - u'| / |u k - u'| < β :=
    (tendsto_error_ratio hT hcont hfix hu hne hlim).eventually (gt_mem_nhds hβ1)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun k hk => ?_⟩
  have hpos : 0 < |u k - u'| := abs_pos.2 (sub_ne_zero.2 (hne k))
  have := hN k hk
  rw [div_lt_iff₀ hpos] at this
  rw [Real.rpow_one, Real.norm_eq_abs, Real.norm_eq_abs]
  exact this.le

/-! ### Newton's fixed-point iteration (§2.1.4.1), one dimension -/

/-- The Newton map (2.2) in one dimension: the fixed point of the first-order approximation
`T̂v = Tu + T'(u)(v − u)`, namely `Qu = (Tu − T'(u)u)/(1 − T'(u))`. -/
noncomputable def newtonMap (T T' : ℝ → ℝ) (u : ℝ) : ℝ := (T u - T' u * u) / (1 - T' u)

/-- `Qu` is the fixed point of the linearisation of `T` at `u` (p. 47–48). -/
theorem newtonMap_fixedPt_linearisation (T T' : ℝ → ℝ) {u : ℝ} (hT' : T' u ≠ 1) (v : ℝ) :
    T u + T' u * (v - u) = v ↔ v = newtonMap T T' u := by
  have h : 1 - T' u ≠ 0 := sub_ne_zero.2 (Ne.symm hT')
  rw [newtonMap, eq_div_iff h]
  constructor <;> intro hv <;> linarith

/-- Fixed points of `T` with `T'(u) ≠ 1` are exactly the fixed points of the Newton map `Q`. -/
theorem isFixedPt_newtonMap_iff (T T' : ℝ → ℝ) {u : ℝ} (hT' : T' u ≠ 1) :
    IsFixedPt (newtonMap T T') u ↔ IsFixedPt T u := by
  simp only [IsFixedPt]
  have h : 1 - T' u ≠ 0 := sub_ne_zero.2 (Ne.symm hT')
  rw [newtonMap, div_eq_iff h]
  constructor <;> intro hu <;> linarith

end SargentStachurski.OperatorsFixedPoints

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Partial orders, greatest elements, suprema and infima

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §2.2.1 (pp. 51–55).

Partial orders are Mathlib's `PartialOrder`; the pointwise order on `ℝ^X` is
the `Pi` instance; greatest and least elements are `IsGreatest`/`IsLeast`;
suprema and infima are `IsLUB`/`IsGLB`. The exercises of the section are
proved in that vocabulary: Exercises 2.2.1–2.2.17, with the matrix inequalities
of Exercises 2.2.7–2.2.8 that later sections use.
-/

open Finset Set Matrix

namespace SargentStachurski.OperatorsFixedPoints

/-! ### Partially ordered sets (§2.2.1.1) -/

/-- Example 2.2.1 (p. 51): `≤` on `ℝ` is a partial order; antisymmetry says `a ≤ b` and `b ≤ a`
imply `a = b`. -/
theorem real_le_isPartialOrder : IsPartialOrder ℝ (· ≤ ·) := inferInstance

theorem real_le_antisymm {a b : ℝ} (hab : a ≤ b) (hba : b ≤ a) : a = b := le_antisymm hab hba

/-- Exercise 2.2.1 (p. 51): equality is a partial order on any set. -/
theorem eq_isPartialOrder (P : Type*) : IsPartialOrder P (· = ·) where
  refl _ := rfl
  trans _ _ _ h₁ h₂ := h₁.trans h₂
  antisymm _ _ h _ := h

/-- Exercise 2.2.2 (p. 51): set inclusion is a partial order on `℘(M)`. -/
theorem subset_isPartialOrder (M : Type*) : IsPartialOrder (Set M) (· ⊆ ·) := inferInstance

/-- Example 2.2.2 and Exercise 2.2.3 (p. 52): the pointwise order `u ≤ v ↔ ∀ x, u x ≤ v x` is a
partial order on `ℝ^X`. -/
theorem pointwise_isPartialOrder (X : Type*) : IsPartialOrder (X → ℝ) (· ≤ ·) := inferInstance

theorem pointwise_le_def {X : Type*} (u v : X → ℝ) : u ≤ v ↔ ∀ x, u x ≤ v x := Pi.le_def

/-- The strict pointwise relation `u ≪ v` of p. 52: `u(x) < v(x)` for all `x`. -/
def StrictLt {X : Type*} (u v : X → ℝ) : Prop := ∀ x, u x < v x

/-- Exercise 2.2.4 (p. 52): `≪` is not a partial order on `ℝ^X` for nonempty `X`, since it is not
reflexive. -/
theorem not_strictLt_refl {X : Type*} [Nonempty X] (u : X → ℝ) : ¬ StrictLt u u :=
  fun h => lt_irrefl _ (h (Classical.arbitrary X))

theorem strictLt_not_isPartialOrder {X : Type*} [Nonempty X] :
    ¬ IsPartialOrder (X → ℝ) StrictLt :=
  fun h => not_strictLt_refl (fun _ : X => (0 : ℝ)) (h.refl _)

/-- Exercise 2.2.5 (p. 52): limits preserve weak inequalities in `ℝⁿ`: if `a ≤ uₖ ≤ b` for all
`k` and `uₖ → u`, then `a ≤ u ≤ b`. -/
theorem le_of_tendsto_pi {n : ℕ} {a b u : Fin n → ℝ} {u' : ℕ → Fin n → ℝ}
    (hab : ∀ k, a ≤ u' k ∧ u' k ≤ b) (hlim : Filter.Tendsto u' Filter.atTop (nhds u)) :
    a ≤ u ∧ u ≤ b := by
  have hmem : ∀ k, u' k ∈ Icc a b := fun k => hab k
  have := isClosed_Icc.mem_of_tendsto hlim (Filter.Eventually.of_forall hmem)
  exact this

/-- Example 2.2.3 and Exercise 2.2.6 (pp. 52–53): the pointwise order on `n × k` matrices is the
pointwise order on functions on `X = [n] × [k]`. -/
theorem matrix_le_iff_uncurry {m k : Type*} (A B : Matrix m k ℝ) :
    (∀ i j, A i j ≤ B i j) ↔ ∀ p : m × k, A p.1 p.2 ≤ B p.1 p.2 :=
  ⟨fun h p => h p.1 p.2, fun h i j => h (i, j)⟩

/-- A nonnegative matrix preserves `≤` on vectors: the step behind Exercise 2.2.7 (ii) and
Exercise 2.2.27. -/
theorem mulVec_le_mulVec {m k : Type*} [Fintype k] {A : Matrix m k ℝ} (hA : ∀ i j, 0 ≤ A i j)
    {u v : k → ℝ} (huv : u ≤ v) : A *ᵥ u ≤ A *ᵥ v := fun i =>
  sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (huv j) (hA i j)

/-- Exercise 2.2.7 (i), p. 53: if `B ≥ 0` then `|Bu| ≤ B|u|` pointwise. -/
theorem abs_mulVec_le {m k : Type*} [Fintype k] {B : Matrix m k ℝ} (hB : ∀ i j, 0 ≤ B i j)
    (u : k → ℝ) (i : m) : |(B *ᵥ u) i| ≤ (B *ᵥ fun j => |u j|) i := by
  simp only [Matrix.mulVec, dotProduct]
  calc |∑ j, B i j * u j| ≤ ∑ j, |B i j * u j| := abs_sum_le_sum_abs _ _
    _ = ∑ j, B i j * |u j| := sum_congr rfl fun j _ => by
        rw [abs_mul, abs_of_nonneg (hB i j)]

/-- Exercise 2.2.7 (ii), p. 53: if `A ≥ 0` and `uₖ₊₁ ≤ Auₖ` for all `k`, then `uₖ ≤ Aᵏu₀`. -/
theorem le_pow_mulVec_of_le {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 ≤ A i j)
    {u : ℕ → Fin n → ℝ} (h : ∀ k, u (k + 1) ≤ A *ᵥ u k) (k : ℕ) : u k ≤ A ^ k *ᵥ u 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc u (k + 1) ≤ A *ᵥ u k := h k
      _ ≤ A *ᵥ (A ^ k *ᵥ u 0) := mulVec_le_mulVec hA ih
      _ = A ^ (k + 1) *ᵥ u 0 := by rw [Matrix.mulVec_mulVec, pow_succ']

/-- Exercise 2.2.8 (p. 53): if `A ≫ 0`, `u ≤ v` and `u ≠ v`, then `Au ≪ Av`. -/
theorem strictLt_mulVec {m k : Type*} [Fintype k] {A : Matrix m k ℝ} (hA : ∀ i j, 0 < A i j)
    {u v : k → ℝ} (huv : u ≤ v) (hne : u ≠ v) : StrictLt (A *ᵥ u) (A *ᵥ v) := by
  intro i
  obtain ⟨j₀, hj₀⟩ : ∃ j, u j < v j := by
    by_contra hcon
    have hcon' : ∀ j, v j ≤ u j := fun j => le_of_not_gt fun h => hcon ⟨j, h⟩
    exact hne (funext fun j => le_antisymm (huv j) (hcon' j))
  simp only [Matrix.mulVec, dotProduct]
  exact sum_lt_sum (fun j _ => mul_le_mul_of_nonneg_left (huv j) (hA i j).le)
    ⟨j₀, mem_univ _, mul_lt_mul_of_pos_left hj₀ (hA i j₀)⟩

/-- Example 2.2.4 (p. 53): `≤` is a total order on `ℝ` and on `ℕ`. -/
theorem real_le_total (a b : ℝ) : a ≤ b ∨ b ≤ a := le_total a b

theorem nat_le_total (a b : ℕ) : a ≤ b ∨ b ≤ a := le_total a b

/-- Example 2.2.5 (p. 53): the pointwise order on `ℝ²` is not total: `(0, 1)` and `(1, 0)` are
incomparable. -/
theorem pointwise_not_total :
    ¬ ((![0, 1] : Fin 2 → ℝ) ≤ ![1, 0] ∨ (![1, 0] : Fin 2 → ℝ) ≤ ![0, 1]) := by
  rintro (h | h)
  · have := h 1
    norm_num at this
  · have := h 0
    norm_num at this

/-- Exercise 2.2.9 (p. 53): inclusion on `℘({1, 2})` is not total: `{1}` and `{2}` are
incomparable. -/
theorem subset_not_total : ¬ (({0} : Set (Fin 2)) ⊆ {1} ∨ ({1} : Set (Fin 2)) ⊆ {0}) := by
  rintro (h | h)
  · have := h (mem_singleton 0)
    simp at this
  · have := h (mem_singleton 1)
    simp at this

/-! ### Least and greatest elements (§2.2.1.2) -/

/-- Exercise 2.2.10 (p. 54): a subset of a partially ordered set has at most one greatest
element. -/
theorem isGreatest_unique {P : Type*} [PartialOrder P] {A : Set P} {g g' : P} (hg : IsGreatest A g)
    (hg' : IsGreatest A g') : g = g' :=
  hg.unique hg'

/-- Exercise 2.2.10 (p. 54): ... and at most one least element. -/
theorem isLeast_unique {P : Type*} [PartialOrder P] {A : Set P} {l l' : P} (hl : IsLeast A l)
    (hl' : IsLeast A l') : l = l' :=
  hl.unique hl'

/-- Exercise 2.2.11 (p. 54): `⋃ᵢ Aᵢ` is the greatest element of `{Aᵢ}` iff it is one of the
`Aᵢ`. -/
theorem isGreatest_iUnion_iff {M ι : Type*} (A : ι → Set M) :
    IsGreatest (range A) (⋃ i, A i) ↔ (⋃ i, A i) ∈ range A := by
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, by rintro _ ⟨i, rfl⟩; exact subset_iUnion A i⟩

/-- Exercise 2.2.12 (p. 54): the bounded subsets of `ℝⁿ` (`n ≥ 1`) have no greatest element
under inclusion: a greatest one would contain every singleton, hence be all of `ℝⁿ`, which is
unbounded. -/
theorem not_exists_isGreatest_bounded {n : ℕ} [NeZero n] :
    ¬ ∃ G, IsGreatest {A : Set (Fin n → ℝ) | Bornology.IsBounded A} G := by
  rintro ⟨G, hG, hmax⟩
  have huniv : G = univ := by
    refine eq_univ_of_forall fun x => ?_
    have := hmax (Bornology.isBounded_singleton (x := x))
    exact this (mem_singleton x)
  rw [huniv] at hG
  exact NormedSpace.unbounded_univ ℝ (Fin n → ℝ) hG

/-! ### Suprema and infima (§2.2.1.3) -/

/-- Exercise 2.2.13 (p. 54): a subset has at most one supremum. -/
theorem isLUB_unique {P : Type*} [PartialOrder P] {A : Set P} {s s' : P} (hs : IsLUB A s)
    (hs' : IsLUB A s') : s = s' :=
  hs.unique hs'

/-- Exercise 2.2.14 (i), p. 55: a supremum that belongs to `A` is a greatest element. -/
theorem isGreatest_of_isLUB_mem {P : Type*} [Preorder P] {A : Set P} {a : P} (h : IsLUB A a)
    (ha : a ∈ A) : IsGreatest A a :=
  ⟨ha, h.1⟩

/-- Exercise 2.2.14 (ii), p. 55: a greatest element is the supremum. -/
theorem IsGreatest.isLUB' {P : Type*} [Preorder P] {A : Set P} {a : P} (h : IsGreatest A a) :
    IsLUB A a :=
  h.isLUB

/-- Exercise 2.2.15 (p. 55): a least element is the infimum. -/
theorem IsLeast.isGLB' {P : Type*} [Preorder P] {A : Set P} {l : P} (h : IsLeast A l) :
    IsGLB A l :=
  h.isGLB

/-- Exercise 2.2.16 (p. 55): in `℘(M)`, `⋁ᵢ Aᵢ = ⋃ᵢ Aᵢ`. -/
theorem isLUB_iUnion {M ι : Type*} (A : ι → Set M) : IsLUB (range A) (⋃ i, A i) :=
  isLUB_iSup

/-- Exercise 2.2.16 (p. 55): in `℘(M)`, `⋀ᵢ Aᵢ = ⋂ᵢ Aᵢ`. -/
theorem isGLB_iInter {M ι : Type*} (A : ι → Set M) : IsGLB (range A) (⋂ i, A i) :=
  isGLB_iInf

/-- Exercise 2.2.17 (p. 55): a totally ordered set in which a subset has no supremum. In
`P = (0, 1)` the subset `A = [1/2, 1)` has no upper bound in `P`, hence no supremum. -/
theorem not_exists_isLUB_Ioo :
    ¬ ∃ s : Ioo (0 : ℝ) 1, IsLUB {a : Ioo (0 : ℝ) 1 | 1 / 2 ≤ (a : ℝ)} s := by
  rintro ⟨s, hs, -⟩
  have hs1 : (s : ℝ) < 1 := s.2.2
  -- the point `(s + 1)/2` lies in `A` and exceeds `s`
  have hmem : (1 / 2 : ℝ) ≤ ((s : ℝ) + 1) / 2 := by linarith [s.2.1]
  have hin : ((s : ℝ) + 1) / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [s.2.1], by linarith⟩
  have := hs (show (⟨((s : ℝ) + 1) / 2, hin⟩ : Ioo (0 : ℝ) 1) ∈
    {a : Ioo (0 : ℝ) 1 | 1 / 2 ≤ (a : ℝ)} from hmem)
  have h' : ((s : ℝ) + 1) / 2 ≤ s := this
  linarith

end SargentStachurski.OperatorsFixedPoints

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The pointwise order on `ℝ^X`

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §2.2.2 (pp. 55–59).

Under the pointwise order the infimum and supremum of `{u, v}` are the
pointwise minimum and maximum, and the same holds for finite families
(Exercises 2.2.18–2.2.19). Sublattices are closed under finite suprema and
infima (Exercise 2.2.20); a finite family has a greatest element iff its
pointwise maximum belongs to it (Example 2.2.7, Exercise 2.2.21); order
intervals in a sublattice intersect in order intervals (Exercise 2.2.22).

Lemma 2.2.1 lists the lattice inequalities and identities, Exercise 2.2.23
the `∧ c` bound, Lemma 2.2.2 the key estimate `|max f − max g| ≤ max |f − g|`
with its `min` twin (Exercise 2.2.24), and Lemma 2.2.3 shows the upper envelope
of finitely many contractions is a contraction.
-/

open Finset Set

namespace SargentStachurski.OperatorsFixedPoints

variable {X : Type*}

/-! ### Suprema and infima under the pointwise order (§2.2.2.1) -/

/-- p. 56: the pointwise minimum is the infimum of `{u, v}` in `(ℝ^X, ≤)`. -/
theorem isGLB_pair_pointwise (u v : X → ℝ) : IsGLB {u, v} (fun x => min (u x) (v x)) := by
  have : (fun x => min (u x) (v x)) = u ⊓ v := rfl
  rw [this]
  exact isGLB_pair

/-- Exercise 2.2.18 (p. 56): the pointwise maximum is the supremum of `{u, v}`. -/
theorem isLUB_pair_pointwise (u v : X → ℝ) : IsLUB {u, v} (fun x => max (u x) (v x)) := by
  have : (fun x => max (u x) (v x)) = u ⊔ v := rfl
  rw [this]
  exact isLUB_pair

/-- A sublattice of `ℝ^X` (p. 56): closed under `∨` and `∧`. -/
def IsSublattice (V : Set (X → ℝ)) : Prop := ∀ u ∈ V, ∀ v ∈ V, u ⊔ v ∈ V ∧ u ⊓ v ∈ V

/-- Example 2.2.6 (p. 56): `V₁ = {f ≥ 0}` is a sublattice. -/
theorem isSublattice_nonneg : IsSublattice {f : X → ℝ | ∀ x, 0 ≤ f x} := fun _ hu _ hv =>
  ⟨fun x => le_trans (hu x) (le_max_left _ _), fun x => le_min (hu x) (hv x)⟩

/-- Example 2.2.6 (p. 56): `V₂ = {f ≫ 0}` is a sublattice. -/
theorem isSublattice_pos : IsSublattice {f : X → ℝ | ∀ x, 0 < f x} := fun _ hu _ hv =>
  ⟨fun x => lt_of_lt_of_le (hu x) (le_max_left _ _), fun x => lt_min (hu x) (hv x)⟩

/-- Example 2.2.6 (p. 56): `V₃ = {|f| ≤ 1}` is a sublattice. -/
theorem isSublattice_abs_le_one : IsSublattice {f : X → ℝ | ∀ x, |f x| ≤ 1} := fun u hu v hv =>
  ⟨fun x => by
    rcases le_total (u x) (v x) with h | h
    · simpa [Pi.sup_apply, max_eq_right h] using hv x
    · simpa [Pi.sup_apply, max_eq_left h] using hu x,
  fun x => by
    rcases le_total (u x) (v x) with h | h
    · simpa [Pi.inf_apply, min_eq_left h] using hu x
    · simpa [Pi.inf_apply, min_eq_right h] using hv x⟩

/-- Exercise 2.2.19 (p. 56): the supremum of a finite family is its pointwise maximum, and the
infimum its pointwise minimum. -/
theorem sup'_apply_pointwise {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (v : ι → X → ℝ) (x : X) :
    s.sup' hs v x = s.sup' hs fun i => v i x :=
  Finset.sup'_apply hs v x

theorem inf'_apply_pointwise {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (v : ι → X → ℝ) (x : X) :
    s.inf' hs v x = s.inf' hs fun i => v i x :=
  Finset.inf'_apply hs v x

/-- Exercise 2.2.19 (p. 56): the finite supremum is the least upper bound of the family. -/
theorem isLUB_sup'_image {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (v : ι → X → ℝ) :
    IsLUB (v '' s) (s.sup' hs v) := by
  constructor
  · rintro _ ⟨i, hi, rfl⟩
    exact Finset.le_sup' v hi
  · intro g hg
    exact Finset.sup'_le hs v fun i hi => hg ⟨i, hi, rfl⟩

theorem isGLB_inf'_image {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (v : ι → X → ℝ) :
    IsGLB (v '' s) (s.inf' hs v) := by
  constructor
  · rintro _ ⟨i, hi, rfl⟩
    exact Finset.inf'_le v hi
  · intro g hg
    exact Finset.le_inf' hs v fun i hi => hg ⟨i, hi, rfl⟩

/-- Exercise 2.2.20 (p. 56): a sublattice contains the suprema and infima of its finite subsets. -/
theorem IsSublattice.sup'_mem {V : Set (X → ℝ)} (hV : IsSublattice V) {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {v : ι → X → ℝ} (hv : ∀ i ∈ s, v i ∈ V) : s.sup' hs v ∈ V :=
  Finset.sup'_mem V (fun u hu w hw => (hV u hu w hw).1) s hs v hv

theorem IsSublattice.inf'_mem {V : Set (X → ℝ)} (hV : IsSublattice V) {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {v : ι → X → ℝ} (hv : ∀ i ∈ s, v i ∈ V) : s.inf' hs v ∈ V :=
  Finset.inf'_mem V (fun u hu w hw => (hV u hu w hw).2) s hs v hv

/-- Example 2.2.7 and Exercise 2.2.21 (p. 57), first claim: if the pointwise maximum `v*` of a
finite family belongs to the family, it is the greatest element. -/
theorem isGreatest_of_sup'_mem {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (v : ι → X → ℝ)
    (h : s.sup' hs v ∈ v '' s) : IsGreatest (v '' s) (s.sup' hs v) :=
  ⟨h, (isLUB_sup'_image hs v).1⟩

/-- Example 2.2.7 and Exercise 2.2.21 (p. 57), second claim: if `v*` is not in the family, the
family has no greatest element. -/
theorem not_exists_isGreatest_of_sup'_notMem {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (v : ι → X → ℝ) (h : s.sup' hs v ∉ v '' s) : ¬ ∃ g, IsGreatest (v '' s) g := by
  rintro ⟨g, hg⟩
  have h1 : g = s.sup' hs v := hg.isLUB.unique (isLUB_sup'_image hs v)
  exact h (h1 ▸ hg.1)

/-- Exercise 2.2.22 (p. 57): the intersection of two order intervals of a sublattice is an order
interval of the sublattice, `[a₁, a₂] ∩ [b₁, b₂] = [a₁ ∨ b₁, a₂ ∧ b₂]`. -/
theorem Icc_inter_Icc_sublattice {V : Set (X → ℝ)} (hV : IsSublattice V) {a₁ a₂ b₁ b₂ : X → ℝ}
    (ha₁ : a₁ ∈ V) (ha₂ : a₂ ∈ V) (hb₁ : b₁ ∈ V) (hb₂ : b₂ ∈ V) :
    Icc a₁ a₂ ∩ Icc b₁ b₂ = Icc (a₁ ⊔ b₁) (a₂ ⊓ b₂) ∧ a₁ ⊔ b₁ ∈ V ∧ a₂ ⊓ b₂ ∈ V :=
  ⟨Icc_inter_Icc, (hV a₁ ha₁ b₁ hb₁).1, (hV a₂ ha₂ b₂ hb₂).2⟩

/-! ### Inequalities and identities (§2.2.2.2) -/

/-- Lemma 2.2.1 (i), p. 58: `|f + g| ≤ |f| + |g|`. -/
theorem abs_add_le_pointwise (f g : X → ℝ) : |f + g| ≤ |f| + |g| := fun x => abs_add_le (f x) (g x)

/-- Lemma 2.2.1 (ii), p. 58: `(f ∧ g) + h = (f + h) ∧ (g + h)`. -/
theorem inf_add_pointwise (f g h : X → ℝ) : (f ⊓ g) + h = (f + h) ⊓ (g + h) := by
  funext x
  simp only [Pi.add_apply, Pi.inf_apply]
  exact (min_add_add_right (f x) (g x) (h x)).symm

/-- Lemma 2.2.1 (ii), p. 58: `(f ∨ g) + h = (f + h) ∨ (g + h)`. -/
theorem sup_add_pointwise (f g h : X → ℝ) : (f ⊔ g) + h = (f + h) ⊔ (g + h) := by
  funext x
  simp only [Pi.add_apply, Pi.sup_apply]
  exact (max_add_add_right (f x) (g x) (h x)).symm

/-- Lemma 2.2.1 (iii), p. 58: `(f ∨ g) ∧ h = (f ∧ h) ∨ (g ∧ h)`. -/
theorem sup_inf_pointwise (f g h : X → ℝ) : (f ⊔ g) ⊓ h = (f ⊓ h) ⊔ (g ⊓ h) := inf_sup_right _ _ _

/-- Lemma 2.2.1 (iii), p. 58: `(f ∧ g) ∨ h = (f ∨ h) ∧ (g ∨ h)`. -/
theorem inf_sup_pointwise (f g h : X → ℝ) : (f ⊓ g) ⊔ h = (f ⊔ h) ⊓ (g ⊔ h) := sup_inf_right _ _ _

/-- The `min` form of Mathlib's `abs_max_sub_max_le_abs`: `|min a c − min b c| ≤ |a − b|`. -/
theorem abs_min_sub_min_le_abs' (a b c : ℝ) : |min a c - min b c| ≤ |a - b| := by
  have h := abs_max_sub_max_le_abs (-a) (-b) (-c)
  rw [max_neg_neg, max_neg_neg, neg_sub_neg, neg_sub_neg, abs_sub_comm (min b c),
    abs_sub_comm b] at h
  exact h

/-- Lemma 2.2.1 (iv), p. 58: `|f ∧ h − g ∧ h| ≤ |f − g|`. -/
theorem abs_inf_sub_inf_le_pointwise (f g h : X → ℝ) : |f ⊓ h - g ⊓ h| ≤ |f - g| := fun x =>
  abs_min_sub_min_le_abs' (f x) (g x) (h x)

/-- Lemma 2.2.1 (v), p. 58: `|f ∨ h − g ∨ h| ≤ |f − g|`. -/
theorem abs_sup_sub_sup_le_pointwise (f g h : X → ℝ) : |f ⊔ h - g ⊔ h| ≤ |f - g| := fun x =>
  abs_max_sub_max_le_abs (f x) (g x) (h x)

/-- The scalar case of (2.3): for `a, b, c ≥ 0`, `(a + b) ∧ c ≤ a ∧ c + b ∧ c`. -/
theorem min_add_le_min_add_min {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    min (a + b) c ≤ min a c + min b c := by
  rcases le_total a c with hac | hac <;> rcases le_total b c with hbc | hbc
  · rw [min_eq_left hac, min_eq_left hbc]
    exact min_le_left _ _
  · rw [min_eq_left hac, min_eq_right hbc]
    exact (min_le_right _ _).trans (by linarith)
  · rw [min_eq_right hac, min_eq_left hbc]
    exact (min_le_right _ _).trans (by linarith)
  · rw [min_eq_right hac, min_eq_right hbc]
    exact (min_le_right _ _).trans (by linarith)

/-- (2.3), p. 58: for `f, g, h ∈ ℝ^X₊`, `(f + g) ∧ h ≤ (f ∧ h) + (g ∧ h)`. -/
theorem inf_add_le_pointwise {f g h : X → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hh : ∀ x, 0 ≤ h x) : (f + g) ⊓ h ≤ f ⊓ h + g ⊓ h := fun x =>
  min_add_le_min_add_min (hf x) (hg x) (hh x)

/-- Exercise 2.2.23 (p. 58): for `a, b, c ≥ 0`, `|a ∧ c − b ∧ c| ≤ |a − b| ∧ c`. -/
theorem abs_min_sub_min_le_min {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    |min a c - min b c| ≤ min |a - b| c := by
  refine le_min (abs_min_sub_min_le_abs' a b c) ?_
  rw [abs_sub_le_iff]
  constructor
  · linarith [min_le_right a c, le_min hb hc]
  · linarith [min_le_right b c, le_min ha hc]

/-- Lemma 2.2.2 (p. 58): for finite nonempty `D`, `|max f − max g| ≤ max |f − g|`. -/
theorem abs_sup'_sub_sup'_le {D : Type*} [Fintype D] (hD : (univ : Finset D).Nonempty)
    (f g : D → ℝ) :
    |univ.sup' hD f - univ.sup' hD g| ≤ univ.sup' hD fun z => |f z - g z| := by
  -- `max f − max g ≤ max |f − g|`, then swap the roles
  have key : ∀ f g : D → ℝ,
      univ.sup' hD f - univ.sup' hD g ≤ univ.sup' hD fun z => |f z - g z| := by
    intro f g
    rw [sub_le_iff_le_add]
    refine Finset.sup'_le hD f fun z _ => ?_
    calc f z = (f z - g z) + g z := by ring
      _ ≤ |f z - g z| + g z := add_le_add (le_abs_self _) le_rfl
      _ ≤ (univ.sup' hD fun z => |f z - g z|) + univ.sup' hD g :=
          add_le_add (Finset.le_sup' (fun z => |f z - g z|) (mem_univ z))
            (Finset.le_sup' g (mem_univ z))
  rw [abs_sub_le_iff]
  refine ⟨key f g, ?_⟩
  have := key g f
  simpa [abs_sub_comm] using this

/-- Exercise 2.2.24 (p. 59): `|min f − min g| ≤ max |f − g|`. -/
theorem abs_inf'_sub_inf'_le {D : Type*} [Fintype D] (hD : (univ : Finset D).Nonempty)
    (f g : D → ℝ) :
    |univ.inf' hD f - univ.inf' hD g| ≤ univ.sup' hD fun z => |f z - g z| := by
  -- `min f = −max(−f)`, as in the book's solution
  have h1 : ∀ f : D → ℝ, univ.inf' hD f = -univ.sup' hD fun z => -f z := by
    intro f
    apply le_antisymm
    · rw [le_neg]
      exact Finset.sup'_le hD _ fun z _ => neg_le_neg (Finset.inf'_le f (mem_univ z))
    · refine Finset.le_inf' hD f fun z _ => ?_
      have := Finset.le_sup' (fun z => -f z) (mem_univ z)
      linarith
  rw [h1 f, h1 g, neg_sub_neg]
  have := abs_sup'_sub_sup'_le hD (fun z => -g z) (fun z => -f z)
  simpa only [neg_sub_neg] using this

/-! ### Upper envelopes (p. 59) -/

/-- The upper envelope `Tv = ⋁_σ T_σ v` of a finite family of self-maps (p. 59). -/
noncomputable def upperEnvelope {S : Type*} [Fintype S] (hS : (univ : Finset S).Nonempty)
    (T : S → (X → ℝ) → (X → ℝ)) (v : X → ℝ) : X → ℝ :=
  univ.sup' hS fun σ => T σ v

/-- The upper envelope of self-maps of a sublattice is a self-map of the sublattice (p. 59). -/
theorem upperEnvelope_mapsTo {S : Type*} [Fintype S] (hS : (univ : Finset S).Nonempty)
    {T : S → (X → ℝ) → (X → ℝ)} {V : Set (X → ℝ)} (hV : IsSublattice V)
    (hT : ∀ σ, MapsTo (T σ) V V) : MapsTo (upperEnvelope hS T) V V := fun _ hv =>
  hV.sup'_mem hS fun σ _ => hT σ hv

/-- Lemma 2.2.3 (p. 59): if each `T_σ` is a contraction of modulus `λ_σ` on a sublattice `V` in
the supremum norm, then the upper envelope is a contraction of modulus `max_σ λ_σ`. -/
theorem isContractionOn_upperEnvelope [Fintype X] {S : Type*} [Fintype S]
    (hS : (univ : Finset S).Nonempty) {T : S → (X → ℝ) → (X → ℝ)} {V : Set (X → ℝ)}
    (hV : IsSublattice V) {L : S → ℝ} (hT : ∀ σ, IsContractionOn (T σ) V (L σ)) :
    IsContractionOn (upperEnvelope hS T) V (univ.sup' hS L) := by
  have hL0 : 0 ≤ univ.sup' hS L := by
    obtain ⟨σ, -⟩ := hS
    exact (hT σ).nonneg.trans (Finset.le_sup' L (mem_univ σ))
  refine ⟨upperEnvelope_mapsTo hS hV fun σ => (hT σ).mapsTo, hL0, ?_, fun u hu v hv => ?_⟩
  · exact (Finset.sup'_lt_iff hS).2 fun σ _ => (hT σ).lt_one
  · rw [pi_norm_le_iff_of_nonneg (mul_nonneg hL0 (norm_nonneg _))]
    intro x
    rw [Pi.sub_apply, Real.norm_eq_abs]
    simp only [upperEnvelope, Finset.sup'_apply]
    calc |(univ.sup' hS fun σ => T σ u x) - univ.sup' hS fun σ => T σ v x|
        ≤ univ.sup' hS fun σ => |T σ u x - T σ v x| := abs_sup'_sub_sup'_le hS _ _
      _ ≤ univ.sup' hS fun σ => L σ * ‖u - v‖ := by
          refine Finset.sup'_mono_fun fun σ _ => ?_
          have h1 := (hT σ).norm_sub_le u hu v hv
          have h2 : |T σ u x - T σ v x| ≤ ‖T σ u - T σ v‖ := by
            have := norm_le_pi_norm (T σ u - T σ v) x
            simpa [Real.norm_eq_abs] using this
          exact h2.trans h1
      _ ≤ (univ.sup' hS L) * ‖u - v‖ :=
          Finset.sup'_le hS _ fun σ _ =>
            mul_le_mul_of_nonneg_right (Finset.le_sup' L (mem_univ σ)) (norm_nonneg _)

end SargentStachurski.OperatorsFixedPoints

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Order-preserving maps, increasing functions and Blackwell's condition

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §2.2.3 (pp. 59–62).

Order-preserving maps are Mathlib's `Monotone`, order-reversing `Antitone`;
for real-valued functions on a partially ordered set the book says
"increasing" and "decreasing". Examples 2.2.8–2.2.10 and Exercises
2.2.25–2.2.32 are proved here, except the spectral-radius half of Exercise
2.2.28, which is in `SpectralRadius`. Blackwell's condition (Lemma 2.2.4):
an order-preserving self-map that discounts constants is a contraction in the
supremum norm.
-/

open Finset Set Filter Topology Matrix

namespace SargentStachurski.OperatorsFixedPoints

/-! ### Order-preserving maps (§2.2.3.1) -/

/-- Example 2.2.8 (p. 60): for `A ≥ 0`, `u ↦ Au + b` is order preserving on `ℝⁿ`. -/
theorem monotone_affine_of_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (b : Fin n → ℝ) : Monotone fun u => A *ᵥ u + b := fun u v huv => by
  change A *ᵥ u + b ≤ A *ᵥ v + b
  exact add_le_add (mulVec_le_mulVec hA huv) le_rfl

/-- Example 2.2.9 (p. 60): integration over `[a, b]` is order preserving on continuous functions
under the pointwise order. -/
theorem integral_mono_of_le {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hg : ContinuousOn g (Icc a b)) (hfg : ∀ x ∈ Icc a b, f x ≤ g x) :
    ∫ x in a..b, f x ≤ ∫ x in a..b, g x :=
  intervalIntegral.integral_mono_on hab (hf.intervalIntegrable_of_Icc hab)
    (hg.intervalIntegrable_of_Icc hab) hfg

/-- Exercise 2.2.25 (p. 60): an order-preserving `F` maps a greatest element to the greatest
element of the image, which is therefore the supremum of the image: `F(⋁ uᵢ) = ⋁ Fuᵢ`. -/
theorem isLUB_image_of_isGreatest {P Q : Type*} [Preorder P] [Preorder Q] {F : P → Q}
    (hF : Monotone F) {s : Set P} {u : P} (hu : IsGreatest s u) : IsLUB (F '' s) (F u) :=
  (hF.map_isGreatest hu).isLUB

/-- Exercise 2.2.25 (p. 60), the infimum half: `F(⋀ uᵢ) = ⋀ Fuᵢ`. -/
theorem isGLB_image_of_isLeast {P Q : Type*} [Preorder P] [Preorder Q] {F : P → Q}
    (hF : Monotone F) {s : Set P} {l : P} (hl : IsLeast s l) : IsGLB (F '' s) (F l) :=
  (hF.map_isLeast hl).isGLB

/-- Exercise 2.2.26 (p. 60): powers of an order-preserving self-map are order preserving. -/
theorem monotone_iterate {P : Type*} [Preorder P] {A : P → P} (hA : Monotone A) (k : ℕ) :
    Monotone A^[k] :=
  hA.iterate k

/-- Exercise 2.2.27 (p. 60): for `A ≥ 0` the map `u ↦ Au` is order preserving. -/
theorem monotone_mulVec_of_nonneg {m k : Type*} [Fintype k] {A : Matrix m k ℝ}
    (hA : ∀ i j, 0 ≤ A i j) : Monotone fun u : k → ℝ => A *ᵥ u := fun _ _ huv =>
  mulVec_le_mulVec hA huv

/-- Products of nonnegative matrices are monotone in each factor. -/
theorem mul_le_mul_of_nonneg {n : ℕ} {A B C D : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hAB : ∀ i j, A i j ≤ B i j) (hC : ∀ i j, 0 ≤ C i j)
    (hCD : ∀ i j, C i j ≤ D i j) (i j : Fin n) : (A * C) i j ≤ (B * D) i j := by
  simp only [Matrix.mul_apply]
  refine sum_le_sum fun l _ => ?_
  calc A i l * C l j ≤ A i l * D l j := mul_le_mul_of_nonneg_left (hCD l j) (hA i l)
    _ ≤ B i l * D l j := mul_le_mul_of_nonneg_right (hAB i l) ((hC l j).trans (hCD l j))

/-- Powers of a nonnegative matrix are nonnegative. -/
theorem pow_nonneg_entries {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 ≤ A i j) (k : ℕ)
    (i j : Fin n) : 0 ≤ (A ^ k) i j := by
  induction k generalizing i j with
  | zero => simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    exact sum_nonneg fun l _ => mul_nonneg (hA i l) (ih l j)

/-- Exercise 2.2.28 (p. 60), first part: `0 ≤ A ≤ B` implies `Aᵏ ≤ Bᵏ` for all `k`. -/
theorem pow_le_pow_entries {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (hAB : ∀ i j, A i j ≤ B i j) (k : ℕ) (i j : Fin n) : (A ^ k) i j ≤ (B ^ k) i j := by
  induction k generalizing i j with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ']
    exact mul_le_mul_of_nonneg hA hAB (pow_nonneg_entries hA k) ih i j

/-! ### Increasing and decreasing functions (§2.2.3.2) -/

/-- The increasing functions `iℝ^P` on a partially ordered set (p. 61). -/
def increasingFns (P : Type*) [Preorder P] : Set (P → ℝ) := {h | Monotone h}

/-- Example 2.2.10 (p. 61) on `P = {1, …, n}`: `x ↦ 2x` is increasing. -/
theorem monotone_two_mul {n : ℕ} : Monotone fun x : Fin n => (2 : ℝ) * x := fun x y hxy => by
  have : (x : ℝ) ≤ y := by exact_mod_cast hxy
  linarith

/-- Example 2.2.10 (p. 61): `x ↦ 1{2 ≤ x}` is increasing. -/
theorem monotone_indicator_ge {n : ℕ} :
    Monotone fun x : Fin n => if 2 ≤ (x : ℕ) then (1 : ℝ) else 0 := fun x y hxy => by
  dsimp only
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (h1.trans (Fin.le_def.1 hxy)) h2
  · norm_num
  · exact le_rfl

/-- Example 2.2.10 (p. 61): `x ↦ −x` is not increasing on `{1, …, n}` with `n ≥ 2`. -/
theorem not_monotone_neg : ¬ Monotone fun x : Fin 5 => -((x : ℕ) : ℝ) := by
  intro h
  have := h (show (0 : Fin 5) ≤ 1 by decide)
  norm_num at this

/-- Example 2.2.10 (p. 61): `x ↦ 1{x ≤ 2}` is not increasing. -/
theorem not_monotone_indicator_le :
    ¬ Monotone fun x : Fin 5 => if (x : ℕ) ≤ 2 then (1 : ℝ) else 0 := by
  intro h
  have := h (show (2 : Fin 5) ≤ 3 by decide)
  norm_num at this

/-- Exercise 2.2.29 (i), p. 61: `αf + βg` is increasing for `α, β ≥ 0`. -/
theorem monotone_smul_add {P : Type*} [Preorder P] {f g : P → ℝ} (hf : Monotone f)
    (hg : Monotone g) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) : Monotone fun p => α * f p + β * g p :=
  (hf.const_mul hα).add (hg.const_mul hβ)

/-- Exercise 2.2.29 (ii), p. 61: `f ∨ g` and `f ∧ g` are increasing. -/
theorem monotone_sup_inf {P : Type*} [Preorder P] {f g : P → ℝ} (hf : Monotone f)
    (hg : Monotone g) : Monotone (f ⊔ g) ∧ Monotone (f ⊓ g) :=
  ⟨hf.sup hg, hf.inf hg⟩

/-- Exercise 2.2.30 (p. 61): `iℝ^P` is a closed subset of `ℝ^P`. -/
theorem isClosed_increasingFns (P : Type*) [Preorder P] : IsClosed (increasingFns P) := by
  have : increasingFns P = ⋂ (p : P) (q : P) (_ : p ≤ q), {h : P → ℝ | h p ≤ h q} := by
    ext h
    simp only [increasingFns, Set.mem_ofPred_eq, mem_iInter]
    exact ⟨fun hm p q hpq => hm hpq, fun hm p q hpq => hm p q hpq⟩
  rw [this]
  exact isClosed_iInter fun p => isClosed_iInter fun q => isClosed_iInter fun _ =>
    isClosed_le (continuous_apply p) (continuous_apply q)

/-- Exercise 2.2.31 (p. 61): `h ↦ E h(X) = ∑ h(x) φ(x)` is increasing on `ℝ^X` for a
distribution `φ`. -/
theorem monotone_expectation {X : Type*} [Fintype X] {φ : X → ℝ} (hφ : ∀ x, 0 ≤ φ x) :
    Monotone fun h : X → ℝ => ∑ x, h x * φ x := fun _ _ hfg =>
  sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (hfg x) (hφ x)

/-- Exercise 2.2.32 (p. 61): on the totally ordered set `X = {0, …, n − 1}`, every increasing
nonnegative `u` is a nonnegative combination of the increasing indicators `1{x ≥ k}`:
`u(x) = ∑ₖ sₖ 1{x ≥ k}` with `s₀ = u(0)` and `sₖ = u(k) − u(k − 1)`. -/
theorem exists_indicator_decomposition {n : ℕ} {u : ℕ → ℝ} (hu : Monotone u) (hu0 : 0 ≤ u 0) :
    ∃ s : ℕ → ℝ, (∀ k, 0 ≤ s k) ∧
      ∀ x < n, u x = ∑ k ∈ range n, s k * (if k ≤ x then 1 else 0) := by
  refine ⟨fun k => if k = 0 then u 0 else u k - u (k - 1), fun k => ?_, fun x hx => ?_⟩
  · dsimp only
    split_ifs with hk
    · exact hu0
    · exact sub_nonneg.2 (hu (Nat.sub_le k 1))
  · -- the sum over `k ≤ x` telescopes to `u x`
    have htel : ∀ m, ∑ k ∈ range (m + 1), (if k = 0 then u 0 else u k - u (k - 1)) = u m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [sum_range_succ, ih]
        have : (if m + 1 = 0 then u 0 else u (m + 1) - u (m + 1 - 1)) = u (m + 1) - u m := by
          simp
        rw [this]
        ring
    have hfilter : (range n).filter (fun k => k ≤ x) = range (x + 1) := by
      ext k
      simp only [mem_filter, Finset.mem_range]
      omega
    calc u x = ∑ k ∈ range (x + 1), (if k = 0 then u 0 else u k - u (k - 1)) := (htel x).symm
      _ = ∑ k ∈ (range n).filter (fun k => k ≤ x), (if k = 0 then u 0 else u k - u (k - 1)) := by
          rw [hfilter]
      _ = ∑ k ∈ range n, (if k = 0 then u 0 else u k - u (k - 1)) * (if k ≤ x then 1 else 0) := by
          rw [sum_filter]
          refine sum_congr rfl fun k _ => ?_
          split_ifs <;> simp

/-! ### Blackwell's condition (§2.2.3.3) -/

/-- Lemma 2.2.4 (Blackwell, p. 62): on `U ⊆ ℝ^X` closed under adding nonnegative constants, an
order-preserving self-map `T` with `T(u + c) ≤ Tu + βc` for all `u ∈ U`, `c ≥ 0` and some
`β ∈ [0, 1)` is a contraction of modulus `β` in the supremum norm. -/
theorem isContractionOn_of_blackwell {X : Type*} [Fintype X] {U : Set (X → ℝ)}
    {T : (X → ℝ) → (X → ℝ)} {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hU : ∀ u ∈ U, ∀ c : ℝ, 0 ≤ c → (u + fun _ : X => c) ∈ U) (hmaps : MapsTo T U U)
    (hmono : ∀ u ∈ U, ∀ v ∈ U, u ≤ v → T u ≤ T v)
    (hdisc : ∀ u ∈ U, ∀ c : ℝ, 0 ≤ c → T (u + fun _ : X => c) ≤ T u + fun _ : X => β * c) :
    IsContractionOn T U β := by
  refine ⟨hmaps, hβ0, hβ1, fun u hu v hv => ?_⟩
  -- `Tu ≤ Tv + β‖u − v‖` pointwise, by monotonicity and discounting
  have key : ∀ u ∈ U, ∀ v ∈ U, ∀ x : X, T u x - T v x ≤ β * ‖u - v‖ := by
    intro u hu v hv x
    have hle : u ≤ v + fun _ : X => ‖u - v‖ := fun y => by
      have := norm_le_pi_norm (u - v) y
      rw [Pi.sub_apply, Real.norm_eq_abs] at this
      simp only [Pi.add_apply]
      linarith [le_abs_self (u y - v y)]
    have h1 := hmono u hu _ (hU v hv ‖u - v‖ (norm_nonneg _)) hle x
    have h2 := hdisc v hv ‖u - v‖ (norm_nonneg _) x
    simp only [Pi.add_apply] at h1 h2
    linarith
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg hβ0 (norm_nonneg _))]
  intro x
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_sub_le_iff]
  refine ⟨key u hu v hv x, ?_⟩
  have := key v hv u hu x
  rwa [norm_sub_rev] at this

end SargentStachurski.OperatorsFixedPoints

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Stochastic dominance

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §2.2.4 (pp. 62–64).

For distributions `φ, ψ` on a finite partially ordered set `X`, `ψ`
stochastically dominates `φ`, `φ ≼_F ψ`, if `∑ u φ ≤ ∑ u ψ` for every
increasing `u`, (2.9). Example 2.2.11 is proved in its general form: if two
random variables on a finite probability space satisfy `X ≤ Y` pointwise then
the law of `Y` dominates the law of `X`. Exercise 2.2.33 treats `X = {1, 2}`;
Lemma 2.2.5 relates dominance to the counter-CDFs, with the converse on totally
ordered sets proved by Abel summation (the book's proof is in its Appendix B);
Lemma 2.2.6 shows `≼_F` is a partial order, antisymmetry by induction along the
well-founded order on the finite set; Exercise 2.2.35 orders quantiles.
-/

open Finset

namespace SargentStachurski.OperatorsFixedPoints

variable {X : Type*} [Fintype X]

/-- A distribution on the finite set `X`. -/
structure IsDistribution (φ : X → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ φ x
  sum_eq_one : ∑ x, φ x = 1

/-- The law of a random variable `Z : Ω → X` on a finite probability space `(Ω, p)`. -/
def law {Ω : Type*} [Fintype Ω] [DecidableEq X] (p : Ω → ℝ) (Z : Ω → X) (x : X) : ℝ :=
  ∑ ω ∈ univ.filter (fun ω => Z ω = x), p ω

theorem law_isDistribution {Ω : Type*} [Fintype Ω] [DecidableEq X] {p : Ω → ℝ}
    (hp : IsDistribution p) (Z : Ω → X) : IsDistribution (law p Z) where
  nonneg x := sum_nonneg fun ω _ => hp.nonneg ω
  sum_eq_one := by
    rw [← hp.sum_eq_one]
    exact (sum_fiberwise univ Z p)

/-- `∑ u(x) law(x) = ∑_ω u(Z ω) p(ω)`. -/
theorem sum_mul_law {Ω : Type*} [Fintype Ω] [DecidableEq X] (p : Ω → ℝ) (Z : Ω → X) (u : X → ℝ) :
    ∑ x, u x * law p Z x = ∑ ω, u (Z ω) * p ω := by
  rw [← sum_fiberwise univ Z fun ω => u (Z ω) * p ω]
  refine sum_congr rfl fun x _ => ?_
  rw [law, mul_sum]
  refine sum_congr rfl fun ω hω => ?_
  rw [(Finset.mem_filter.1 hω).2]

-- Partially ordered state spaces
variable [PartialOrder X]

/-- First-order stochastic dominance (2.9), p. 62: `φ ≼_F ψ` iff `∑ u(x)φ(x) ≤ ∑ u(x)ψ(x)`
for every increasing `u`. -/
def FOSD (φ ψ : X → ℝ) : Prop := ∀ u : X → ℝ, Monotone u → ∑ x, u x * φ x ≤ ∑ x, u x * ψ x

/-- Example 2.2.11 (p. 63), in general: if `X ≤ Y` pointwise on a finite probability space, then
the law of `Y` stochastically dominates the law of `X`, since `u(X) ≤ u(Y)` pointwise for every
increasing `u`. The binomial case is `X = W₁ + ⋯ + W₁₀ ≤ W₁ + ⋯ + W₁₈ = Y`. -/
theorem fosd_law_of_le {Ω : Type*} [Fintype Ω] [DecidableEq X] {p : Ω → ℝ} (hp : IsDistribution p)
    {Z Z' : Ω → X} (hZ : ∀ ω, Z ω ≤ Z' ω) : FOSD (law p Z) (law p Z') := by
  unfold FOSD
  intro u hu
  rw [sum_mul_law, sum_mul_law]
  exact sum_le_sum fun ω _ => mul_le_mul_of_nonneg_right (hu (hZ ω)) (hp.nonneg ω)

open Classical in
/-- The counter-CDF `G_φ(y) = ∑_{x ≥ y} φ(x)` (p. 64). -/
noncomputable def ccdf (φ : X → ℝ) (y : X) : ℝ := ∑ x ∈ univ.filter (fun x => y ≤ x), φ x

omit [Fintype X] in
open Classical in
/-- The indicator of the upper set `{x : y ≤ x}` is increasing. -/
theorem monotone_upper_indicator (y : X) :
    Monotone fun x : X => if y ≤ x then (1 : ℝ) else 0 := fun a b hab => by
  dsimp only
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (h1.trans hab) h2
  · norm_num
  · exact le_rfl

open Classical in
/-- `∑ 1{y ≤ x} φ(x) = G_φ(y)`. -/
theorem sum_upper_indicator_mul (φ : X → ℝ) (y : X) :
    ∑ x, (if y ≤ x then (1 : ℝ) else 0) * φ x = ccdf φ y := by
  rw [ccdf, sum_filter]
  refine sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

/-- Lemma 2.2.5 (i), p. 64: `φ ≼_F ψ` implies `G_φ ≤ G_ψ`. -/
theorem ccdf_le_of_fosd {φ ψ : X → ℝ} (h : FOSD φ ψ) (y : X) : ccdf φ y ≤ ccdf ψ y := by
  rw [← sum_upper_indicator_mul, ← sum_upper_indicator_mul]
  exact h _ (monotone_upper_indicator y)

/-- Lemma 2.2.6 (p. 64): `≼_F` is reflexive. -/
theorem fosd_refl (φ : X → ℝ) : FOSD φ φ := fun _ _ => le_rfl

/-- Exercise 2.2.34 (p. 64): `≼_F` is transitive. -/
theorem fosd_trans {φ ψ χ : X → ℝ} (h₁ : FOSD φ ψ) (h₂ : FOSD ψ χ) : FOSD φ χ := fun u hu =>
  (h₁ u hu).trans (h₂ u hu)

open Classical in
/-- A function on a finite poset is determined by its upper-set sums, by induction along the
well-founded order `>`: `φ(y) = G_φ(y) − ∑_{x > y} φ(x)`. -/
theorem eq_of_ccdf_eq {φ ψ : X → ℝ} (h : ∀ y, ccdf φ y = ccdf ψ y) : φ = ψ := by
  funext y
  induction y using WellFoundedGT.induction with
  | _ y ih =>
    have hsplit : ∀ χ : X → ℝ, ccdf χ y = χ y + ∑ x ∈ univ.filter (fun x => y < x), χ x := by
      intro χ
      rw [ccdf]
      have : univ.filter (fun x => y ≤ x) = insert y (univ.filter (fun x => y < x)) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro hx
          rcases hx.lt_or_eq with hlt | heq
          · exact Or.inr hlt
          · exact Or.inl heq.symm
        · rintro (rfl | hlt)
          · exact le_rfl
          · exact hlt.le
      rw [this, Finset.sum_insert]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, lt_self_iff_false, not_false_eq_true]
    have htail : ∑ x ∈ univ.filter (fun x => y < x), φ x =
        ∑ x ∈ univ.filter (fun x => y < x), ψ x :=
      sum_congr rfl fun x hx => ih x (Finset.mem_filter.1 hx).2
    have := h y
    rw [hsplit φ, hsplit ψ, htail] at this
    linarith

/-- Lemma 2.2.6 (p. 64): `≼_F` is antisymmetric, hence a partial order. -/
theorem fosd_antisymm {φ ψ : X → ℝ} (h₁ : FOSD φ ψ) (h₂ : FOSD ψ φ) : φ = ψ :=
  eq_of_ccdf_eq fun y => le_antisymm (ccdf_le_of_fosd h₁ y) (ccdf_le_of_fosd h₂ y)

-- Totally ordered state spaces
variable {Y : Type*} [Fintype Y] [LinearOrder Y]

/-- Abel summation on `Fin n`: if `u` is increasing and nonnegative and every tail sum of `d`
is nonnegative, then `∑ u d ≥ 0`. -/
theorem sum_mul_nonneg_of_tails_nonneg : ∀ (n : ℕ) (u d : Fin n → ℝ), Monotone u →
    (∀ i, 0 ≤ u i) → (∀ i, 0 ≤ ∑ j ∈ univ.filter (fun j => i ≤ j), d j) →
    0 ≤ ∑ i, u i * d i := by
  intro n
  induction n with
  | zero => intro u d _ _ _; simp
  | succ n ih =>
    intro u d hu hu0 htail
    -- `∑ u d = u 0 · D(0) + ∑_{i ≥ 1} (u i − u 0) d i`
    have hD0 : ∑ j, d j = ∑ j ∈ univ.filter (fun j => (0 : Fin (n + 1)) ≤ j), d j := by
      congr 1
      ext j
      simp
    have hsplit : ∑ i, u i * d i =
        u 0 * ∑ j, d j + ∑ i : Fin n, (u i.succ - u 0) * d i.succ := by
      simp only [Fin.sum_univ_succ, sub_mul, sum_sub_distrib, mul_sum, mul_add]
      ring
    rw [hsplit]
    refine add_nonneg (mul_nonneg (hu0 0) (hD0 ▸ htail 0)) ?_
    refine ih (fun i => u i.succ - u 0) (fun i => d i.succ) ?_ ?_ ?_
    · intro i j hij
      exact sub_le_sub_right (hu (Fin.succ_le_succ_iff.2 hij)) _
    · intro i
      exact sub_nonneg.2 (hu (Fin.zero_le _))
    · intro i
      have := htail i.succ
      -- the tail of `d ∘ succ` from `i` is the tail of `d` from `succ i`
      have hreindex : ∑ j ∈ univ.filter (fun j : Fin (n + 1) => i.succ ≤ j), d j =
          ∑ j ∈ univ.filter (fun j : Fin n => i ≤ j), d j.succ := by
        refine (Finset.sum_bij (fun j _ => j.succ) ?_ ?_ ?_ ?_).symm
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
          exact Fin.succ_le_succ_iff.2 hj
        · intro a _ b _ hab
          exact Fin.succ_injective _ hab
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          refine ⟨j.pred (Fin.pos_iff_ne_zero.1 (lt_of_lt_of_le (Fin.succ_pos i) hj)), ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rw [← Fin.succ_le_succ_iff, Fin.succ_pred]
            exact hj
          · exact Fin.succ_pred _ _
        · intro j _
          rfl
      rwa [hreindex] at this

open Classical in
/-- The counter-CDF is additive: `G_{ψ − φ} = G_ψ − G_φ`. -/
theorem ccdf_sub (φ ψ : Y → ℝ) (y : Y) : ccdf (fun x => ψ x - φ x) y = ccdf ψ y - ccdf φ y := by
  simp only [ccdf, sum_sub_distrib]

open Classical in
/-- Reindexing the counter-CDF through an order isomorphism with `Fin n`. -/
theorem ccdf_reindex (χ : Y → ℝ) (e : Fin (Fintype.card Y) ≃o Y) (i : Fin (Fintype.card Y)) :
    ccdf χ (e i) = ∑ j ∈ univ.filter (fun j => i ≤ j), χ (e j) := by
  unfold ccdf
  exact (Finset.sum_equiv e.toEquiv (fun j => by simp [Finset.mem_filter, e.le_iff_le])
    (fun _ _ => rfl)).symm

/-- Lemma 2.2.5 (ii), p. 64: on a totally ordered finite set, `G_φ ≤ G_ψ` implies `φ ≼_F ψ`,
for distributions `φ, ψ`. The increasing `u` is shifted by its minimum to be nonnegative, and
`d = ψ − φ` has nonnegative tail sums and total `0`. -/
theorem fosd_of_ccdf_le {φ ψ : Y → ℝ} (hφ : IsDistribution φ) (hψ : IsDistribution ψ)
    (h : ∀ y, ccdf φ y ≤ ccdf ψ y) : FOSD φ ψ := by
  unfold FOSD
  intro u hu
  rcases isEmpty_or_nonempty Y with hX | hX
  · simp
  -- transport to `Fin n`
  let e : Fin (Fintype.card Y) ≃o Y := Fintype.orderIsoFinOfCardEq Y rfl
  set m : Y := e 0 with hm
  have hmin : ∀ x, m ≤ x := fun x => by
    rw [hm, ← e.apply_symm_apply x, e.le_iff_le]
    exact Fin.zero_le _
  have hsum : ∑ x, (ψ x - φ x) = 0 := by
    rw [sum_sub_distrib, hψ.sum_eq_one, hφ.sum_eq_one, sub_self]
  -- `∑ (u − u m)(ψ − φ) ≥ 0`
  have key : 0 ≤ ∑ x, (u x - u m) * (ψ x - φ x) := by
    rw [← e.toEquiv.sum_comp]
    refine sum_mul_nonneg_of_tails_nonneg _ (fun i => u (e i) - u m) (fun i => ψ (e i) - φ (e i))
      ?_ ?_ ?_
    · intro i j hij
      exact sub_le_sub_right (hu (e.le_iff_le.2 hij)) _
    · intro i
      exact sub_nonneg.2 (hu (hmin _))
    · intro i
      have h1 := ccdf_reindex (fun x => ψ x - φ x) e i
      rw [ccdf_sub] at h1
      have h2 : 0 ≤ ccdf ψ (e i) - ccdf φ (e i) := sub_nonneg.2 (h (e i))
      rw [h1] at h2
      simpa using h2
  have hexpand : ∑ x, (u x - u m) * (ψ x - φ x) = ∑ x, u x * ψ x - ∑ x, u x * φ x := by
    have h1 : ∑ x, (u x - u m) * (ψ x - φ x) =
        ∑ x, u x * (ψ x - φ x) - u m * ∑ x, (ψ x - φ x) := by
      rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun x _ => by ring
    rw [h1, hsum, mul_zero, sub_zero, ← sum_sub_distrib]
    exact sum_congr rfl fun x _ => by ring
  linarith

/-- The CDF `F_φ(x) = ∑_{x' ≤ x} φ(x')` on a totally ordered finite set (Vol. 1, p. 32). -/
noncomputable def cdf (φ : Y → ℝ) (x : Y) : ℝ := ∑ x' ∈ univ.filter (fun x' => x' ≤ x), φ x'

/-- Dominance reverses CDFs: `φ ≼_F ψ` implies `F_ψ ≤ F_φ`, since `−1{x' ≤ x}` is increasing. -/
theorem cdf_le_of_fosd {φ ψ : Y → ℝ} (h : FOSD φ ψ) (x : Y) : cdf ψ x ≤ cdf φ x := by
  have hmono : Monotone fun x' : Y => -(if x' ≤ x then (1 : ℝ) else 0) := fun a b hab => by
    dsimp only
    split_ifs with h1 h2 h2
    · exact le_rfl
    · norm_num
    · exact absurd (hab.trans h2) h1
    · exact le_rfl
  have := h _ hmono
  simp only [neg_mul, sum_neg_distrib, neg_le_neg_iff] at this
  have hc : ∀ χ : Y → ℝ, ∑ x', (if x' ≤ x then (1 : ℝ) else 0) * χ x' = cdf χ x := by
    intro χ
    rw [cdf, sum_filter]
    refine sum_congr rfl fun x' _ => ?_
    split_ifs <;> simp
  rwa [hc, hc] at this

/-- The `τ`-quantile set `{x : τ ≤ F_φ(x)}`. -/
noncomputable def quantileSet (φ : Y → ℝ) (τ : ℝ) : Finset Y := univ.filter fun x => τ ≤ cdf φ x

/-- The `τ`-quantile `Q_τ = min{x : F_φ(x) ≥ τ}` (Vol. 1, (1.24)), given the set is nonempty. -/
noncomputable def quantile (φ : Y → ℝ) (τ : ℝ) (h : (quantileSet φ τ).Nonempty) : Y :=
  (quantileSet φ τ).min' h

/-- Exercise 2.2.35 (p. 64): `φ ≼_F ψ` implies `Q_τ(Y) ≤ Q_τ(Y)`, since `F_ψ ≤ F_φ` makes
`ψ`'s quantile set a subset of `φ`'s. -/
theorem quantile_le_of_fosd {φ ψ : Y → ℝ} (h : FOSD φ ψ) {τ : ℝ} (hφ : (quantileSet φ τ).Nonempty)
    (hψ : (quantileSet ψ τ).Nonempty) : quantile φ τ hφ ≤ quantile ψ τ hψ := by
  have hsub : quantileSet ψ τ ⊆ quantileSet φ τ := by
    intro x hx
    simp only [quantileSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.trans (cdf_le_of_fosd h x)
  exact Finset.min'_subset hψ hsub

/-- Exercise 2.2.33 (p. 64): on `Y = {1, 2}`, `φ ≼_F ψ ↔ ψ(1) ≤ φ(1) ↔ φ(2) ≤ ψ(2)`, for
distributions. Here `Y = Fin 2` with `0 < 1` playing the roles of `1 < 2`. -/
theorem fosd_fin_two_iff {φ ψ : Fin 2 → ℝ} (hφ : IsDistribution φ) (hψ : IsDistribution ψ) :
    (FOSD φ ψ ↔ ψ 0 ≤ φ 0) ∧ (ψ 0 ≤ φ 0 ↔ φ 1 ≤ ψ 1) := by
  have hφs : φ 0 + φ 1 = 1 := by simpa [Fin.sum_univ_two] using hφ.sum_eq_one
  have hψs : ψ 0 + ψ 1 = 1 := by simpa [Fin.sum_univ_two] using hψ.sum_eq_one
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, by constructor <;> intro <;> linarith⟩
  · -- take `u = 1{x = 1}`, increasing
    have hu : Monotone fun x : Fin 2 => if x = 1 then (1 : ℝ) else 0 := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
    have := h _ hu
    simp at this
    linarith
  · unfold FOSD
    intro u hu
    have h01 : u 0 ≤ u 1 := hu (by decide)
    have e1 : φ 1 = 1 - φ 0 := by linarith
    have e2 : ψ 1 = 1 - ψ 0 := by linarith
    have key := mul_nonneg (sub_nonneg.2 h01) (sub_nonneg.2 h)
    simp only [Fin.sum_univ_two]
    rw [e1, e2]
    nlinarith [key]


end SargentStachurski.OperatorsFixedPoints

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Parametric monotonicity

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §2.2.5 (pp. 64–68).

`T` dominates `S` on `P` if `Su ≤ Tu` for all `u`; this is the pointwise order
on self-maps (Exercise 2.2.37). Proposition 2.2.7: if `T` dominates `S`, is
order preserving and globally stable, then its fixed point dominates every
fixed point of `S`. The ambient space is any partially ordered topological
space in which the order is closed, which covers `M ⊆ ℝⁿ` under the pointwise
order.

Exercise 2.2.38 applies the proposition to the Solow–Swan steady state and
Exercise 2.2.39 to the job-search continuation value: both are proved from
the proposition alone, without the closed forms of Chapter 1. The global
stability of the Solow–Swan map is Chapter 1's Exercise 1.2.26 and enters as a
hypothesis; the contraction property of the continuation-value map is proved
here.
-/

open Filter Topology Function Set Finset Matrix

namespace SargentStachurski.OperatorsFixedPoints

variable {P : Type*}

/-- Example 2.2.12 (p. 65): for `0 ≤ A ≤ B` and `u ≥ 0`, `Au + b ≤ Bu + b`, so `u ↦ Bu + b`
dominates `u ↦ Au + b` on `ℝⁿ₊`. -/
theorem affine_dominates {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ} (hAB : ∀ i j, A i j ≤ B i j)
    (b : Fin n → ℝ) {u : Fin n → ℝ} (hu : 0 ≤ u) : A *ᵥ u + b ≤ B *ᵥ u + b := fun i => by
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct]
  exact add_le_add (sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hAB i j) (hu j)) le_rfl

/-- Exercise 2.2.36 (p. 65): if `S ≤ T` are order-preserving self-maps, then `Sᵏ ≤ Tᵏ`. -/
theorem iterate_le_iterate [Preorder P] {S T : P → P} (hS : Monotone S) (hST : S ≤ T) (k : ℕ) :
    S^[k] ≤ T^[k] := by
  intro u
  induction k generalizing u with
  | zero => exact le_rfl
  | succ k ih =>
    rw [iterate_succ_apply, iterate_succ_apply]
    calc S^[k] (S u) ≤ S^[k] (T u) := (hS.iterate k) (hST u)
      _ ≤ T^[k] (T u) := ih (T u)

/-- Exercise 2.2.37 (p. 65): dominance is a partial order on the self-maps of `P`. -/
theorem dominance_isPartialOrder [PartialOrder P] : IsPartialOrder (P → P) (· ≤ ·) :=
  inferInstance

/-- Proposition 2.2.7 (p. 67): if `T` dominates `S`, and `T` is order preserving and globally
stable with fixed point `u_T`, then `u_S ≤ u_T` for every fixed point `u_S` of `S`. The proof is
the book's: `u_S = Su_S ≤ Tu_S`, so by monotonicity `u_S ≤ Tᵏu_S` for all `k`, and the order is
closed under limits. -/
theorem fixedPt_le_of_dominates [PartialOrder P] [TopologicalSpace P] [OrderClosedTopology P]
    {S T : P → P} (hST : S ≤ T) (hT : Monotone T) (hstab : GloballyStable T) {uS uT : P}
    (huS : IsFixedPt S uS) (huT : IsFixedPt T uT) : uS ≤ uT := by
  have hle : ∀ k : ℕ, uS ≤ T^[k] uS := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      calc uS = S uS := huS.eq.symm
        _ ≤ T uS := hST uS
        _ ≤ T (T^[k] uS) := hT ih
        _ = T^[k + 1] uS := (iterate_succ_apply' T k uS).symm
  exact ge_of_tendsto' (hstab.tendsto_iterate huT uS) hle

/-! ### Exercise 2.2.38: the Solow–Swan steady state -/

/-- The Solow–Swan map `g(k) = sAkᵅ + (1 − δ)k` as a self-map of `(0, ∞)`, Exercise 2.2.38
(p. 67), for `s, A > 0`, `α ∈ (0, 1)`, `δ ∈ (0, 1]`. -/
noncomputable def solowMap (s A α δ : ℝ) (hs : 0 < s) (hA : 0 < A) (hδ : δ ≤ 1) :
    Ioi (0 : ℝ) → Ioi (0 : ℝ) := fun k =>
  ⟨s * A * (k : ℝ) ^ α + (1 - δ) * k, by
    have h1 := mul_pos (mul_pos hs hA) (Real.rpow_pos_of_pos k.2 α)
    have h2 : 0 ≤ (1 - δ) * (k : ℝ) := mul_nonneg (by linarith) k.2.le
    exact Set.mem_Ioi.2 (by linarith)⟩

/-- `g` is order preserving on `(0, ∞)` for `α > 0`. -/
theorem solowMap_monotone {s A α δ : ℝ} (hs : 0 < s) (hA : 0 < A) (hα : 0 < α) (hδ : δ ≤ 1) :
    Monotone (solowMap s A α δ hs hA hδ) := by
  intro k k' hkk'
  have hk : (k : ℝ) ≤ k' := hkk'
  change s * A * (k : ℝ) ^ α + (1 - δ) * k ≤ s * A * (k' : ℝ) ^ α + (1 - δ) * k'
  have h1 : (k : ℝ) ^ α ≤ (k' : ℝ) ^ α := Real.rpow_le_rpow k.2.le hk hα.le
  have h2 : (1 - δ) * (k : ℝ) ≤ (1 - δ) * k' := mul_le_mul_of_nonneg_left hk (by linarith)
  nlinarith [mul_pos hs hA]

/-- Exercise 2.2.38 (p. 67): raising `s` or `A`, or lowering `δ`, shifts `g` up everywhere. -/
theorem solowMap_le {s A δ s' A' δ' α : ℝ} (hs : 0 < s) (hA : 0 < A) (hδ : δ ≤ 1) (hs' : 0 < s')
    (hA' : 0 < A') (hδ' : δ' ≤ 1) (hss : s ≤ s') (hAA : A ≤ A') (hδδ : δ' ≤ δ) :
    solowMap s A α δ hs hA hδ ≤ solowMap s' A' α δ' hs' hA' hδ' := by
  intro k
  change s * A * (k : ℝ) ^ α + (1 - δ) * k ≤ s' * A' * (k : ℝ) ^ α + (1 - δ') * k
  have hk := k.2
  have hpow : 0 < (k : ℝ) ^ α := Real.rpow_pos_of_pos hk α
  have h1 : s * A ≤ s' * A' := mul_le_mul hss hAA hA.le hs'.le
  have h2 : (1 - δ) * (k : ℝ) ≤ (1 - δ') * k := mul_le_mul_of_nonneg_right (by linarith) hk.le
  nlinarith

/-- Exercise 2.2.38 (p. 67): the steady state `k*` is increasing in `s` and `A` and decreasing in
`δ`, by Proposition 2.2.7. Global stability of the Solow–Swan map on `(0, ∞)` is Chapter 1's
Exercise 1.2.26 and is a hypothesis here (`hstab`); the closed form for `k*` is not used. -/
theorem solow_fixedPt_le {s A δ s' A' δ' α : ℝ} (hs : 0 < s) (hA : 0 < A) (hδ : δ ≤ 1)
    (hs' : 0 < s') (hA' : 0 < A') (hδ' : δ' ≤ 1) (hα : 0 < α) (hss : s ≤ s') (hAA : A ≤ A')
    (hδδ : δ' ≤ δ) (hstab : GloballyStable (solowMap s' A' α δ' hs' hA' hδ'))
    {k k' : Ioi (0 : ℝ)} (hk : IsFixedPt (solowMap s A α δ hs hA hδ) k)
    (hk' : IsFixedPt (solowMap s' A' α δ' hs' hA' hδ') k') : k ≤ k' :=
  fixedPt_le_of_dominates (solowMap_le hs hA hδ hs' hA' hδ' hss hAA hδδ)
    (solowMap_monotone hs' hA' hα hδ') hstab hk hk'

/-! ### Exercise 2.2.39: the continuation value is increasing in `β` -/

/-- The job-search continuation-value map of Vol. 1 (1.33),
`gᵦ(h) = c + β ∑ max{w/(1 − β), h} φ(w)`, for a finite set of wage offers `W`. -/
noncomputable def contMap {W : Type*} [Fintype W] (wage φ : W → ℝ) (c β : ℝ) (h : ℝ) : ℝ :=
  c + β * ∑ w, max (wage w / (1 - β)) h * φ w

/-- `gᵦ` is order preserving for `β ≥ 0` and `φ ≥ 0`. -/
theorem contMap_monotone {W : Type*} [Fintype W] {wage φ : W → ℝ} (hφ : ∀ w, 0 ≤ φ w) {c β : ℝ}
    (hβ : 0 ≤ β) : Monotone (contMap wage φ c β) := by
  intro h h' hh
  unfold contMap
  have : ∑ w, max (wage w / (1 - β)) h * φ w ≤ ∑ w, max (wage w / (1 - β)) h' * φ w :=
    sum_le_sum fun w _ => mul_le_mul_of_nonneg_right (max_le_max_left _ hh) (hφ w)
  nlinarith

/-- `gᵦ` is a contraction of modulus `β` on `ℝ`, by (1.28) and `∑ φ = 1`. -/
theorem contMap_isContractionOn {W : Type*} [Fintype W] {wage φ : W → ℝ} (hφ : ∀ w, 0 ≤ φ w)
    (hsum : ∑ w, φ w = 1) {c β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    IsContractionOn (contMap wage φ c β) univ β := by
  refine ⟨mapsTo_univ _ _, hβ0, hβ1, fun h _ h' _ => ?_⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  unfold contMap
  rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg hβ0, ← sum_sub_distrib]
  refine mul_le_mul_of_nonneg_left ?_ hβ0
  calc |∑ w, (max (wage w / (1 - β)) h * φ w - max (wage w / (1 - β)) h' * φ w)|
      ≤ ∑ w, |max (wage w / (1 - β)) h * φ w - max (wage w / (1 - β)) h' * φ w| :=
        abs_sum_le_sum_abs _ _
    _ = ∑ w, |max (wage w / (1 - β)) h - max (wage w / (1 - β)) h'| * φ w := by
        refine sum_congr rfl fun w _ => ?_
        rw [← sub_mul, abs_mul, abs_of_nonneg (hφ w)]
    _ ≤ ∑ w, |h - h'| * φ w :=
        sum_le_sum fun w _ => mul_le_mul_of_nonneg_right (by
          rw [max_comm _ h, max_comm _ h']
          exact abs_max_sub_max_le_abs _ _ _) (hφ w)
    _ = |h - h'| := by rw [← mul_sum, hsum, mul_one]

/-- `β₁ ≤ β₂` shifts `g` up everywhere on `ℝ₊`, for nonnegative wages. -/
theorem contMap_le {W : Type*} [Fintype W] {wage φ : W → ℝ} (hw : ∀ w, 0 ≤ wage w)
    (hφ : ∀ w, 0 ≤ φ w) {c β₁ β₂ : ℝ} (hβ₁ : 0 ≤ β₁) (hβ₂ : β₂ < 1) (hββ : β₁ ≤ β₂) {h : ℝ}
    (hh : 0 ≤ h) : contMap wage φ c β₁ h ≤ contMap wage φ c β₂ h := by
  unfold contMap
  have h1 : ∀ w, max (wage w / (1 - β₁)) h ≤ max (wage w / (1 - β₂)) h := fun w => by
    have hβ₂' : 0 < 1 - β₂ := by linarith
    exact max_le_max (div_le_div_of_nonneg_left (hw w) hβ₂' (by linarith)) le_rfl
  have h2 : 0 ≤ ∑ w, max (wage w / (1 - β₁)) h * φ w :=
    sum_nonneg fun w _ => mul_nonneg (le_trans hh (le_max_right _ _)) (hφ w)
  have h3 : ∑ w, max (wage w / (1 - β₁)) h * φ w ≤ ∑ w, max (wage w / (1 - β₂)) h * φ w :=
    sum_le_sum fun w _ => mul_le_mul_of_nonneg_right (h1 w) (hφ w)
  nlinarith

/-- Exercise 2.2.39 (p. 67): the continuation value `h*` is increasing in `β`. With `β₁ ≤ β₂`,
`g₁ ≤ g₂` on `ℝ₊`, `g₂` is order preserving and (being a contraction) globally stable, so
Proposition 2.2.7 gives `h₁* ≤ h₂*`. The fixed points are taken in `ℝ₊` (`g` maps into
`[c, ∞)` when `c > 0`, so every fixed point is positive). -/
theorem contMap_fixedPt_le {W : Type*} [Fintype W] {wage φ : W → ℝ} (hw : ∀ w, 0 ≤ wage w)
    (hφ : ∀ w, 0 ≤ φ w) (hsum : ∑ w, φ w = 1) {c β₁ β₂ : ℝ} (hβ₁ : 0 ≤ β₁) (hβ₂ : β₂ < 1)
    (hββ : β₁ ≤ β₂) {h₁ h₂ : ℝ} (hh₁ : IsFixedPt (contMap wage φ c β₁) h₁)
    (hh₂ : IsFixedPt (contMap wage φ c β₂) h₂) (hh₁0 : 0 ≤ h₁) : h₁ ≤ h₂ := by
  -- Proposition 2.2.7 on the subtype `ℝ₊ = Ici 0` would need `g₂` to map it to itself; the
  -- scalar argument of the proposition is reproduced directly instead.
  have hβ₂0 : 0 ≤ β₂ := hβ₁.trans hββ
  have hstab :=
    (contMap_isContractionOn (wage := wage) (c := c) hφ hsum hβ₂0 hβ₂).globallyStable_univ
  have hmono := contMap_monotone hφ hβ₂0 (W := W) (wage := wage) (c := c)
  -- `h₁ ≤ g₂ᵏ h₁` for all `k`
  have hle : ∀ k : ℕ, h₁ ≤ (contMap wage φ c β₂)^[k] h₁ := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      calc h₁ = contMap wage φ c β₁ h₁ := hh₁.eq.symm
        _ ≤ contMap wage φ c β₂ h₁ := contMap_le hw hφ hβ₁ hβ₂ hββ hh₁0
        _ ≤ contMap wage φ c β₂ ((contMap wage φ c β₂)^[k] h₁) := hmono ih
        _ = (contMap wage φ c β₂)^[k + 1] h₁ := (iterate_succ_apply' _ k h₁).symm
  exact ge_of_tendsto' (hstab.tendsto_iterate hh₂ h₁) hle

end SargentStachurski.OperatorsFixedPoints

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The spectral radius of a real matrix

The spectral radius `ρ(A) = max{|λ| : λ an eigenvalue}` of Vol. 1 (1.15) and
the facts about it that Chapter 2 uses: Gelfand's formula (Lemma 1.2.2), the
eventual bound `‖Aᵏ‖ ≤ rᵏ` for `r > ρ(A)`, the Neumann series (Theorem 1.2.1),
and invariance under transposition. These are restated here from the
`FiniteStates/JobSearch` project so that this project is self-contained.

New in this chapter: the ℓ∞ operator norm is monotone in the entries, so for
`0 ≤ A ≤ B` Gelfand's formula gives `ρ(A) ≤ ρ(B)`, the second half of
Exercise 2.2.28 (p. 60).
-/

open Filter Topology Matrix Finset

namespace SargentStachurski.OperatorsFixedPoints

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

/-- The complexification of a real matrix. -/
def complexify (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  A.map Complex.ofReal

theorem complexify_apply (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    complexify A i j = (A i j : ℂ) := rfl

theorem complexify_pow (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    complexify (A ^ k) = complexify A ^ k :=
  map_pow (Complex.ofRealHom.mapMatrix (m := Fin n)) A k

theorem complexify_transpose (A : Matrix (Fin n) (Fin n) ℝ) :
    complexify Aᵀ = (complexify A)ᵀ := by
  ext i j
  rfl

theorem nnnorm_complexify (A : Matrix (Fin n) (Fin n) ℝ) : ‖complexify A‖₊ = ‖A‖₊ := by
  simp only [Matrix.linfty_opNNNorm_def, complexify_apply, Complex.nnnorm_real]

theorem norm_complexify (A : Matrix (Fin n) (Fin n) ℝ) : ‖complexify A‖ = ‖A‖ :=
  congrArg NNReal.toReal (nnnorm_complexify A)

/-- The spectral radius (Vol. 1, (1.15)): the largest modulus of a complex eigenvalue. -/
noncomputable def specRad (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (spectralRadius ℂ (complexify A)).toReal

theorem spectralRadius_complexify_ne_top [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) :
    spectralRadius ℂ (complexify A) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.coe_ne_top (spectralRadius_le_nnnorm (complexify A))

theorem specRad_nonneg (A : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ specRad A := ENNReal.toReal_nonneg

/-- The spectrum of the complexification is the set of eigenvalues. -/
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

/-- Gelfand's formula (Vol. 1, Lemma 1.2.2) for real matrices: `‖Aᵏ‖^{1/k} → ρ(A)`. -/
theorem tendsto_norm_pow_rpow [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (fun k : ℕ => ‖A ^ k‖ ^ (1 / (k : ℝ))) atTop (𝓝 (specRad A)) := by
  have : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  have h := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius (complexify A)
  have h2 := (ENNReal.tendsto_toReal (spectralRadius_complexify_ne_top A)).comp h
  refine h2.congr fun k => ?_
  simp only [Function.comp, ← complexify_pow, norm_complexify]
  exact ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)

/-- If `ρ(A) < r` then `‖Aᵏ‖ ≤ rᵏ` for all large `k`. -/
theorem eventually_norm_pow_le [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) {r : ℝ}
    (hr : specRad A < r) : ∀ᶠ k : ℕ in atTop, ‖A ^ k‖ ≤ r ^ k := by
  have hev : ∀ᶠ k : ℕ in atTop, ‖A ^ k‖ ^ (1 / (k : ℝ)) < r :=
    (tendsto_norm_pow_rpow A).eventually (gt_mem_nhds hr)
  filter_upwards [hev, eventually_gt_atTop 0] with k hk hk0
  have hnn : 0 ≤ ‖A ^ k‖ := norm_nonneg _
  have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
  have := Real.rpow_le_rpow (Real.rpow_nonneg hnn _) hk.le (Nat.cast_nonneg k)
  rwa [← Real.rpow_mul hnn, one_div_mul_cancel hkr, Real.rpow_one, Real.rpow_natCast] at this

/-- `ρ(A) < 1` implies `‖Aᵏ‖ → 0`. -/
theorem tendsto_norm_pow_zero [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hρ : specRad A < 1) :
    Tendsto (fun k : ℕ => ‖A ^ k‖) atTop (𝓝 0) := by
  obtain ⟨r, hr1, hr2⟩ := exists_between hρ
  have hr0 : 0 ≤ r := (specRad_nonneg A).trans hr1.le
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) (eventually_norm_pow_le A hr1)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr2)

/-- `ρ(A) < 1` implies `∑ₖ Aᵏ` converges. -/
theorem summable_pow [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hρ : specRad A < 1) :
    Summable fun k : ℕ => A ^ k := by
  have : CompleteSpace (Matrix (Fin n) (Fin n) ℝ) := FiniteDimensional.complete ℝ _
  obtain ⟨r, hr1, hr2⟩ := exists_between hρ
  have hr0 : 0 ≤ r := (specRad_nonneg A).trans hr1.le
  exact Summable.of_norm_bounded_eventually_nat (summable_geometric_of_lt_one hr0 hr2)
    (eventually_norm_pow_le A hr1)

/-- `(I − A) ∑ₖ Aᵏ = I` when the series converges. -/
theorem one_sub_mul_tsum (A : Matrix (Fin n) (Fin n) ℝ) (hs : Summable fun k : ℕ => A ^ k) :
    (1 - A) * ∑' k : ℕ, A ^ k = 1 := by
  have h1 : Tendsto (fun K : ℕ => (1 - A) * ∑ k ∈ range K, A ^ k) atTop
      (𝓝 ((1 - A) * ∑' k : ℕ, A ^ k)) :=
    hs.hasSum.tendsto_sum_nat.const_mul (1 - A)
  have h2 : Tendsto (fun K : ℕ => (1 - A) * ∑ k ∈ range K, A ^ k) atTop (𝓝 1) := by
    simp_rw [mul_neg_geom_sum]
    simpa using tendsto_const_nhds.sub hs.tendsto_atTop_zero
  exact tendsto_nhds_unique h1 h2

theorem tsum_mul_one_sub (A : Matrix (Fin n) (Fin n) ℝ) (hs : Summable fun k : ℕ => A ^ k) :
    (∑' k : ℕ, A ^ k) * (1 - A) = 1 := by
  have h1 : Tendsto (fun K : ℕ => (∑ k ∈ range K, A ^ k) * (1 - A)) atTop
      (𝓝 ((∑' k : ℕ, A ^ k) * (1 - A))) :=
    hs.hasSum.tendsto_sum_nat.mul_const (1 - A)
  have h2 : Tendsto (fun K : ℕ => (∑ k ∈ range K, A ^ k) * (1 - A)) atTop (𝓝 1) := by
    simp_rw [geom_sum_mul_neg]
    simpa using tendsto_const_nhds.sub hs.tendsto_atTop_zero
  exact tendsto_nhds_unique h1 h2

/-- The Neumann series lemma (Vol. 1, Theorem 1.2.1): `ρ(A) < 1` implies `I − A` is invertible with
inverse `∑ₖ Aᵏ`. -/
theorem neumann_series [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hρ : specRad A < 1) :
    IsUnit (1 - A) ∧ (1 - A)⁻¹ = ∑' k : ℕ, A ^ k :=
  ⟨⟨⟨1 - A, ∑' k : ℕ, A ^ k, one_sub_mul_tsum A (summable_pow A hρ),
    tsum_mul_one_sub A (summable_pow A hρ)⟩, rfl⟩,
    Matrix.inv_eq_right_inv (one_sub_mul_tsum A (summable_pow A hρ))⟩

/-- `ρ(Aᵀ) = ρ(A)`. -/
theorem specRad_transpose (A : Matrix (Fin n) (Fin n) ℝ) : specRad Aᵀ = specRad A := by
  unfold specRad
  rw [complexify_transpose, Matrix.spectralRadius_transpose]

/-- The ℓ∞ operator norm is monotone in the absolute values of the entries. -/
theorem norm_le_norm_of_abs_le {A B : Matrix (Fin n) (Fin n) ℝ} (h : ∀ i j, |A i j| ≤ |B i j|) :
    ‖A‖ ≤ ‖B‖ := by
  rw [Matrix.linfty_opNorm_def, Matrix.linfty_opNorm_def]
  norm_cast
  refine Finset.sup_mono_fun fun i _ => sum_le_sum fun j _ => ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, Real.norm_eq_abs, Real.norm_eq_abs]
  exact h i j

/-- Exercise 2.2.28 (p. 60), second half: `0 ≤ A ≤ B` implies `ρ(A) ≤ ρ(B)`, by Gelfand's
formula and `‖Aᵏ‖ ≤ ‖Bᵏ‖`. -/
theorem specRad_le_of_le [NeZero n] {A B : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (hAB : ∀ i j, A i j ≤ B i j) : specRad A ≤ specRad B := by
  refine le_of_tendsto_of_tendsto' (tendsto_norm_pow_rpow A) (tendsto_norm_pow_rpow B) fun k => ?_
  refine Real.rpow_le_rpow (norm_nonneg _) ?_ (by positivity)
  refine norm_le_norm_of_abs_le fun i j => ?_
  have hAk := pow_nonneg_entries hA k i j
  have hBk := (pow_nonneg_entries hA k i j).trans (pow_le_pow_entries hA hAB k i j)
  rw [abs_of_nonneg hAk, abs_of_nonneg hBk]
  exact pow_le_pow_entries hA hAB k i j

/-- Row sums of absolute values are bounded by the ℓ∞ operator norm. -/
theorem rowsum_abs_le_norm (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ∑ j, |A i j| ≤ ‖A‖ := by
  rw [Matrix.linfty_opNorm_def]
  have : (∑ j, ‖A i j‖₊ : NNReal) ≤ univ.sup fun i => ∑ j, ‖A i j‖₊ :=
    Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (mem_univ i)
  have h := NNReal.coe_le_coe.2 this
  simpa [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs] using h

/-- The ℓ∞ operator norm is bounded by a bound on the row sums of absolute values. -/
theorem norm_le_of_rowsum_abs_le (A : Matrix (Fin n) (Fin n) ℝ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, ∑ j, |A i j| ≤ c) : ‖A‖ ≤ c := by
  rw [Matrix.linfty_opNorm_def]
  have : (univ.sup fun i => ∑ j, ‖A i j‖₊) ≤ c.toNNReal := by
    refine Finset.sup_le fun i _ => ?_
    have hi := h i
    exact (NNReal.coe_le_coe (r₁ := ∑ j, ‖A i j‖₊) (r₂ := c.toNNReal)).1
      (by simpa [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal c hc] using hi)
  have h2 := NNReal.coe_le_coe.2 this
  rwa [Real.coe_toNNReal c hc] at h2

/-- Each entry is bounded in absolute value by the ℓ∞ operator norm. -/
theorem abs_entry_le_norm (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : |A i j| ≤ ‖A‖ :=
  (Finset.single_le_sum (fun j _ => abs_nonneg (A i j)) (mem_univ j)).trans (rowsum_abs_le_norm A i)

/-- For `A ≥ 0` with all row sums equal to `c`, `‖A‖ = c`. -/
theorem norm_eq_of_rowsum_eq [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ i, ∑ j, A i j = c) : ‖A‖ = c := by
  have habs : ∀ i, ∑ j, |A i j| = c := fun i => by
    rw [← h i]
    exact sum_congr rfl fun j _ => abs_of_nonneg (hA i j)
  refine le_antisymm (norm_le_of_rowsum_abs_le A hc fun i => (habs i).le) ?_
  obtain ⟨i⟩ : Nonempty (Fin n) := inferInstance
  exact (habs i).symm.le.trans (rowsum_abs_le_norm A i)

/-- `ρ(A) ≤ ‖A‖`. -/
theorem specRad_le_norm [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) : specRad A ≤ ‖A‖ := by
  have := ENNReal.toReal_mono ENNReal.coe_ne_top
    (spectralRadius_le_nnnorm (𝕜 := ℂ) (complexify A))
  rwa [ENNReal.coe_toReal, coe_nnnorm, norm_complexify] at this

/-- Every eigenvalue is bounded in modulus by the spectral radius. -/
theorem norm_le_specRad_of_mem_spectrum [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (complexify A)) : ‖μ‖ ≤ specRad A := by
  have : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  have h1 : (‖μ‖₊ : ENNReal) ≤ spectralRadius ℂ (complexify A) := by
    rw [spectralRadius_eq_of_unital (𝕜 := ℂ) (complexify A)]
    exact le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ (complexify A)) => (‖k‖₊ : ENNReal)) μ hμ
  have := ENNReal.toReal_mono (spectralRadius_complexify_ne_top A) h1
  rwa [ENNReal.coe_toReal, coe_nnnorm] at this

/-- For `A ≥ 0` with all row sums equal to `c`, `ρ(A) = c`: the constant vector is an eigenvector
with eigenvalue `c`, and `‖A‖ = c`. -/
theorem specRad_eq_of_rowsum_eq [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    {c : ℝ} (hc : 0 ≤ c) (h : ∀ i, ∑ j, A i j = c) : specRad A = c := by
  refine le_antisymm ((specRad_le_norm A).trans (norm_eq_of_rowsum_eq A hA hc h).le) ?_
  have hmem : (c : ℂ) ∈ spectrum ℂ (complexify A) := by
    rw [mem_spectrum_iff_eigenpair]
    refine ⟨fun _ => 1, ?_, ?_⟩
    · intro h0
      have := congrFun h0 ⟨0, NeZero.pos n⟩
      simp at this
    · funext i
      simp only [mulVec, dotProduct, complexify_apply, mul_one, Pi.smul_apply, smul_eq_mul]
      rw [← Complex.ofReal_sum, h i]
  have := norm_le_specRad_of_mem_spectrum A hmem
  rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc] at this

/-- For `A ≥ 0` with all column sums equal to `c`, `ρ(A) = c`, by transposition. -/
theorem specRad_eq_of_colsum_eq [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    {c : ℝ} (hc : 0 ≤ c) (h : ∀ j, ∑ i, A i j = c) : specRad A = c := by
  rw [← specRad_transpose]
  exact specRad_eq_of_rowsum_eq Aᵀ (fun i j => hA j i) hc h

/-- Entrywise Gelfand bound: for `r > ρ(A)`, `|(Aᵏ)ᵢⱼ| ≤ rᵏ` for all large `k`. -/
theorem eventually_abs_entry_pow_le [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) {r : ℝ}
    (hr : specRad A < r) (i j : Fin n) : ∀ᶠ k : ℕ in atTop, |(A ^ k) i j| ≤ r ^ k :=
  (eventually_norm_pow_le A hr).mono fun k hk => (abs_entry_le_norm (A ^ k) i j).trans hk

end SargentStachurski.OperatorsFixedPoints

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Linear operators, positive operators and Markov operators

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §2.3.3 (pp. 75–80).

A linear operator on `ℝ^X` is a linear map `(X → ℝ) →ₗ[ℝ] (X → ℝ)`; every
matrix gives one by `u ↦ Au` and every linear operator comes from a matrix
(Theorem 2.3.4, Mathlib's `LinearMap.toMatrix'`). The kernel representation
(2.16), the product-space operator (2.17), positive operators (2.18) and
Markov operators are treated, with Lemma 2.3.6 and Exercises 2.3.8–2.3.14.
-/

open Finset Set Matrix

namespace SargentStachurski.OperatorsFixedPoints

variable {X : Type*} [Fintype X]

/-- Theorem 2.3.4 (p. 76), one direction: a matrix acts as a linear operator, (2.15). -/
theorem mulVec_linear (A : Matrix X X ℝ) (α β : ℝ) (u v : X → ℝ) :
    A *ᵥ (α • u + β • v) = α • (A *ᵥ u) + β • (A *ᵥ v) := by
  rw [mulVec_add, mulVec_smul, mulVec_smul]

/-- Theorem 2.3.4 (p. 76): every linear operator on `ℝⁿ` is given by a matrix, `Lu = Au`. -/
theorem exists_matrix_of_linear (L : (X → ℝ) →ₗ[ℝ] (X → ℝ)) :
    ∃ A : Matrix X X ℝ, ∀ u, L u = A *ᵥ u := by
  classical
  exact ⟨LinearMap.toMatrix' L, fun u => by rw [LinearMap.toMatrix'_mulVec]⟩

/-- Lemma 2.3.5 (p. 77), (a) ↔ (b): matrices and linear operators on `ℝ^X` correspond
one-to-one. -/
noncomputable def matrixLinearEquiv [DecidableEq X] :
    Matrix X X ℝ ≃ₗ[ℝ] ((X → ℝ) →ₗ[ℝ] (X → ℝ)) :=
  Matrix.toLin'

theorem matrixLinearEquiv_apply [DecidableEq X] (A : Matrix X X ℝ) (u : X → ℝ) :
    matrixLinearEquiv A u = A *ᵥ u :=
  Matrix.toLin'_apply A u

/-- Lemma 2.3.5 (p. 77), (a) ↔ (d): matrices and functions `X × X → ℝ` correspond one-to-one. -/
def matrixFunEquiv : Matrix X X ℝ ≃ (X × X → ℝ) where
  toFun A p := A p.1 p.2
  invFun f := Matrix.of fun i j => f (i, j)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The operator induced by a kernel `L : X × X → ℝ`, (2.16): `(Lu)(x) = ∑ L(x, x') u(x')`. -/
def kernelOp (L : X → X → ℝ) (u : X → ℝ) : X → ℝ := fun x => ∑ x', L x x' * u x'

/-- Exercise 2.3.8 (p. 77): the kernel operator is linear; indeed it is `u ↦ Lu` for the matrix
with entries `L(x, x')`. -/
theorem kernelOp_eq_mulVec (L : X → X → ℝ) (u : X → ℝ) : kernelOp L u = Matrix.of L *ᵥ u := rfl

theorem kernelOp_linear (L : X → X → ℝ) (α β : ℝ) (u v : X → ℝ) :
    kernelOp L (α • u + β • v) = α • kernelOp L u + β • kernelOp L v := by
  rw [kernelOp_eq_mulVec, kernelOp_eq_mulVec, kernelOp_eq_mulVec, mulVec_linear]

/-- The product-space operator (2.17): on `X = Y × Z`, `(Lu)(y, z) = ∑_{z'} u(y, z') Q(z, z')`. -/
def productOp {Y Z : Type*} [Fintype Z] (Q : Z → Z → ℝ) (u : Y × Z → ℝ) : Y × Z → ℝ :=
  fun p => ∑ z', u (p.1, z') * Q p.2 z'

/-- Exercise 2.3.9 (p. 78): the product-space operator is linear. -/
theorem productOp_linear {Y Z : Type*} [Fintype Z] (Q : Z → Z → ℝ) (α β : ℝ) (u v : Y × Z → ℝ) :
    productOp Q (α • u + β • v) = α • productOp Q u + β • productOp Q v := by
  funext p
  simp only [productOp, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, sum_add_distrib,
    mul_assoc, ← mul_sum]

/-! ### Positive operators and Markov operators (§2.3.3.4) -/

/-- A linear operator is positive (2.18), p. 79, if it maps the positive cone `ℝ^X₊` into itself. -/
def IsPositiveOp (L : (X → ℝ) → (X → ℝ)) : Prop := ∀ u : X → ℝ, 0 ≤ u → 0 ≤ L u

/-- Example 2.3.1 (p. 79): the product-space operator is positive when `Q ≥ 0`. -/
theorem isPositiveOp_productOp {Y Z : Type*} [Fintype Z] {Q : Z → Z → ℝ} (hQ : ∀ z z', 0 ≤ Q z z') :
    IsPositiveOp (productOp Q (Y := Y)) := fun _ hu p =>
  sum_nonneg fun z' _ => mul_nonneg (hu (p.1, z')) (hQ p.2 z')

/-- Lemma 2.3.6 (p. 79) and Exercise 2.3.10: `u ↦ Au` is positive iff `A ≥ 0`. -/
theorem isPositiveOp_mulVec_iff (A : Matrix X X ℝ) :
    IsPositiveOp (fun u => A *ᵥ u) ↔ ∀ i j, 0 ≤ A i j := by
  classical
  constructor
  · intro h i j
    -- test against the indicator of `j`
    have := h (Pi.single j 1) (fun k => by
      by_cases hk : k = j
      · subst hk; simp
      · simp [hk]) i
    simpa [mulVec, dotProduct, Pi.single_apply] using this
  · intro h u hu i
    exact sum_nonneg fun j _ => mul_nonneg (h i j) (hu j)

omit [Fintype X] in
/-- Exercise 2.3.11 (p. 79): a linear operator is positive iff it is order preserving. -/
theorem isPositiveOp_iff_monotone (L : (X → ℝ) →ₗ[ℝ] (X → ℝ)) :
    IsPositiveOp L ↔ Monotone L := by
  constructor
  · intro h u v huv
    have := h (v - u) (fun x => by simpa using huv x)
    rw [map_sub] at this
    intro x
    have := this x
    simp only [Pi.sub_apply, Pi.zero_apply] at this
    linarith
  · intro h u hu
    have := h hu
    rwa [map_zero] at this

/-- A Markov operator (p. 79): positive and fixing the constant function `1`. -/
def IsMarkovOp (L : (X → ℝ) → (X → ℝ)) : Prop := IsPositiveOp L ∧ L (fun _ => 1) = fun _ => 1

/-- Exercise 2.3.12 (p. 80): `u ↦ Pu` is a Markov operator iff `P ≥ 0` and every row sums to one. -/
theorem isMarkovOp_mulVec_iff (P : Matrix X X ℝ) :
    IsMarkovOp (fun u => P *ᵥ u) ↔ (∀ i j, 0 ≤ P i j) ∧ ∀ i, ∑ j, P i j = 1 := by
  rw [IsMarkovOp, isPositiveOp_mulVec_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i => ?_⟩
    have := congrFun h2 i
    simpa [mulVec, dotProduct] using this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, funext fun i => ?_⟩
    simpa [mulVec, dotProduct] using h2 i

/-- Exercise 2.3.13 (p. 80): a Markov matrix maps everywhere-positive vectors to
everywhere-positive vectors. -/
theorem mulVec_pos_of_markov {P : Matrix X X ℝ} (hP : ∀ i j, 0 ≤ P i j) (hrow : ∀ i, ∑ j, P i j = 1)
    {v : X → ℝ} (hv : ∀ j, 0 < v j) (i : X) : 0 < (P *ᵥ v) i := by
  simp only [mulVec, dotProduct]
  have hne : ∃ j, 0 < P i j := by
    by_contra hcon
    have hz : ∀ j, P i j = 0 := fun j => le_antisymm (le_of_not_gt fun h => hcon ⟨j, h⟩) (hP i j)
    have := hrow i
    simp [hz] at this
  obtain ⟨j₀, hj₀⟩ := hne
  exact sum_pos' (fun j _ => mul_nonneg (hP i j) (hv j).le)
    ⟨j₀, mem_univ _, mul_pos hj₀ (hv j₀)⟩

/-- The row-vector action `φ ↦ φP`, (2.19): `(φP)(x') = ∑ P(x, x') φ(x)`. -/
def vecMulOp (P : Matrix X X ℝ) (φ : X → ℝ) : X → ℝ := fun x' => ∑ x, P x x' * φ x

theorem vecMulOp_eq_vecMul (P : Matrix X X ℝ) (φ : X → ℝ) : vecMulOp P φ = φ ᵥ* P := by
  funext x'
  simp only [vecMulOp, vecMul, dotProduct, mul_comm]

/-- Exercise 2.3.14 (p. 80): `u ↦ Pu` is a Markov operator iff `φ ↦ φP` maps distributions to
distributions. -/
theorem isMarkovOp_iff_vecMulOp_distribution (P : Matrix X X ℝ) :
    IsMarkovOp (fun u => P *ᵥ u) ↔
      ∀ φ : X → ℝ, (∀ x, 0 ≤ φ x) → ∑ x, φ x = 1 →
        (∀ x', 0 ≤ vecMulOp P φ x') ∧ ∑ x', vecMulOp P φ x' = 1 := by
  classical
  rw [isMarkovOp_mulVec_iff]
  constructor
  · rintro ⟨hP, hrow⟩ φ hφ hsum
    refine ⟨fun x' => sum_nonneg fun x _ => mul_nonneg (hP x x') (hφ x), ?_⟩
    simp only [vecMulOp]
    rw [sum_comm]
    simp only [← sum_mul, hrow, one_mul, hsum]
  · intro h
    -- test against point masses
    have hpoint : ∀ x, (∀ x', 0 ≤ vecMulOp P (Pi.single x 1) x') ∧
        ∑ x', vecMulOp P (Pi.single x 1) x' = 1 := fun x =>
      h _ (fun k => by
        by_cases hk : k = x
        · subst hk; simp
        · simp [hk]) (by simp)
    refine ⟨fun x x' => ?_, fun x => ?_⟩
    · have := (hpoint x).1 x'
      simpa [vecMulOp, Pi.single_apply] using this
    · have := (hpoint x).2
      simpa [vecMulOp, Pi.single_apply] using this

end SargentStachurski.OperatorsFixedPoints

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The resolvent series, entrywise

For a square matrix `M` over `ℝ` or `ℂ` and a scalar `z` with `|z|` larger than
a bound `r` on the growth of the entries of `Mᵏ`, the series
`∑ₖ z^{−(k+1)} Mᵏ` converges entry by entry to a two-sided inverse of `zI − M`.
This is the Neumann series of Vol. 1, Theorem 1.2.1, written out at the level
of entries so that no topology on the matrix space is needed: partial sums
telescope, `(zI − M) ∑_{k<K} z^{−(k+1)} Mᵏ = I − z^{−K} Mᴷ`, and the correction
term vanishes entrywise.

The Perron–Frobenius argument of `PerronFrobenius` applies this to a
nonnegative real matrix `A` at a real `t > ρ(A)`, where the entries of the
resolvent are nonnegative, and to its complexification at a complex `z` with
`|z| = t`, where they are dominated by the real ones.
-/

open Matrix Finset Filter Topology

namespace SargentStachurski.OperatorsFixedPoints

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-- The partial sums `∑_{k<K} z^{−(k+1)} Mᵏ` of the resolvent series. -/
def resPartial (M : Matrix (Fin n) (Fin n) 𝕜) (z : 𝕜) (K : ℕ) : Matrix (Fin n) (Fin n) 𝕜 :=
  ∑ k ∈ range K, (z⁻¹) ^ (k + 1) • M ^ k

/-- The resolvent series, entry by entry: `R(z)ᵢⱼ = ∑ₖ z^{−(k+1)} (Mᵏ)ᵢⱼ`. -/
noncomputable def res (M : Matrix (Fin n) (Fin n) 𝕜) (z : 𝕜) : Matrix (Fin n) (Fin n) 𝕜 :=
  Matrix.of fun i j => ∑' k : ℕ, (z⁻¹) ^ (k + 1) * (M ^ k) i j

theorem res_apply (M : Matrix (Fin n) (Fin n) 𝕜) (z : 𝕜) (i j : Fin n) :
    res M z i j = ∑' k : ℕ, (z⁻¹) ^ (k + 1) * (M ^ k) i j := rfl

/-- Telescoping: `(zI − M) ∑_{k<K} z^{−(k+1)} Mᵏ = I − z^{−K} Mᴷ`. -/
theorem smul_one_sub_mul_resPartial (M : Matrix (Fin n) (Fin n) 𝕜) {z : 𝕜} (hz : z ≠ 0) (K : ℕ) :
    (z • (1 : Matrix (Fin n) (Fin n) 𝕜) - M) * resPartial M z K = 1 - (z⁻¹) ^ K • M ^ K := by
  induction K with
  | zero => simp [resPartial]
  | succ K ih =>
    have hc : (z⁻¹) ^ (K + 1) • (z • M ^ K) = (z⁻¹) ^ K • M ^ K := by
      rw [smul_smul, pow_succ, mul_assoc, inv_mul_cancel₀ hz, mul_one]
    rw [resPartial, sum_range_succ, ← resPartial, mul_add, ih, Matrix.mul_smul, sub_mul,
      Matrix.smul_mul, one_mul, ← pow_succ', smul_sub, hc]
    abel

/-- Telescoping on the other side: `(∑_{k<K} z^{−(k+1)} Mᵏ)(zI − M) = I − z^{−K} Mᴷ`. -/
theorem resPartial_mul_smul_one_sub (M : Matrix (Fin n) (Fin n) 𝕜) {z : 𝕜} (hz : z ≠ 0) (K : ℕ) :
    resPartial M z K * (z • (1 : Matrix (Fin n) (Fin n) 𝕜) - M) = 1 - (z⁻¹) ^ K • M ^ K := by
  induction K with
  | zero => simp [resPartial]
  | succ K ih =>
    have hc : (z⁻¹) ^ (K + 1) • (z • M ^ K) = (z⁻¹) ^ K • M ^ K := by
      rw [smul_smul, pow_succ, mul_assoc, inv_mul_cancel₀ hz, mul_one]
    rw [resPartial, sum_range_succ, ← resPartial, add_mul, ih, Matrix.smul_mul, mul_sub,
      Matrix.mul_smul, mul_one, ← pow_succ, smul_sub, hc]
    abel

/-- The entry of a partial sum is the partial sum of the entries. -/
theorem resPartial_apply (M : Matrix (Fin n) (Fin n) 𝕜) (z : 𝕜) (K : ℕ) (i j : Fin n) :
    resPartial M z K i j = ∑ k ∈ range K, (z⁻¹) ^ (k + 1) * (M ^ k) i j := by
  simp [resPartial, Matrix.sum_apply]

/-- Under an eventual bound `‖(Mᵏ)ᵢⱼ‖ ≤ rᵏ` with `r < |z|`, the entry series is summable. -/
theorem summable_res_entry (M : Matrix (Fin n) (Fin n) 𝕜) {z : 𝕜} {r : ℝ} (hr : 0 ≤ r)
    (hz : r < ‖z‖) (i j : Fin n) (hM : ∀ᶠ k : ℕ in atTop, ‖(M ^ k) i j‖ ≤ r ^ k) :
    Summable fun k : ℕ => (z⁻¹) ^ (k + 1) * (M ^ k) i j := by
  have hz0 : 0 < ‖z‖ := hr.trans_lt hz
  have hq : r / ‖z‖ < 1 := (div_lt_one hz0).2 hz
  have hq0 : 0 ≤ r / ‖z‖ := div_nonneg hr hz0.le
  refine Summable.of_norm_bounded_eventually_nat
    ((summable_geometric_of_lt_one hq0 hq).mul_left ‖z‖⁻¹) (hM.mono fun k hk => ?_)
  rw [norm_mul, norm_pow, norm_inv, div_pow, pow_succ, ← div_eq_mul_inv]
  calc ‖z‖⁻¹ ^ k * ‖z‖⁻¹ * ‖(M ^ k) i j‖ ≤ ‖z‖⁻¹ ^ k * ‖z‖⁻¹ * r ^ k := by gcongr
    _ = ‖z‖⁻¹ * (r ^ k / ‖z‖ ^ k) := by
        rw [div_eq_mul_inv, ← inv_pow]
        ring

/-- The partial sums converge entrywise to the resolvent series. -/
theorem tendsto_resPartial_apply (M : Matrix (Fin n) (Fin n) 𝕜) {z : 𝕜} {r : ℝ} (hr : 0 ≤ r)
    (hz : r < ‖z‖) (i j : Fin n) (hM : ∀ᶠ k : ℕ in atTop, ‖(M ^ k) i j‖ ≤ r ^ k) :
    Tendsto (fun K => resPartial M z K i j) atTop (𝓝 (res M z i j)) := by
  simp only [resPartial_apply, res_apply]
  exact (summable_res_entry M hr hz i j hM).hasSum.tendsto_sum_nat

/-- The correction term `z^{−K} (Mᴷ)ᵢⱼ` vanishes. -/
theorem tendsto_inv_pow_mul_apply (M : Matrix (Fin n) (Fin n) 𝕜) {z : 𝕜} {r : ℝ} (hr : 0 ≤ r)
    (hz : r < ‖z‖) (i j : Fin n) (hM : ∀ᶠ k : ℕ in atTop, ‖(M ^ k) i j‖ ≤ r ^ k) :
    Tendsto (fun K : ℕ => (z⁻¹) ^ K * (M ^ K) i j) atTop (𝓝 0) := by
  have hz0 : 0 < ‖z‖ := hr.trans_lt hz
  have hq : r / ‖z‖ < 1 := (div_lt_one hz0).2 hz
  have hq0 : 0 ≤ r / ‖z‖ := div_nonneg hr hz0.le
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) (hM.mono fun K hK => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq)
  rw [norm_mul, norm_pow, norm_inv, div_pow, div_eq_mul_inv, ← inv_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right hK (by positivity)

/-- The resolvent series is a right inverse: `(zI − M) R(z) = I`. -/
theorem smul_one_sub_mul_res (M : Matrix (Fin n) (Fin n) 𝕜) {z : 𝕜} {r : ℝ} (hr : 0 ≤ r)
    (hz : r < ‖z‖) (hM : ∀ i j, ∀ᶠ k : ℕ in atTop, ‖(M ^ k) i j‖ ≤ r ^ k) :
    (z • (1 : Matrix (Fin n) (Fin n) 𝕜) - M) * res M z = 1 := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    exact absurd hz (not_lt.2 hr)
  ext i j
  -- the partial products converge to both sides
  have h1 : Tendsto (fun K => ((z • (1 : Matrix (Fin n) (Fin n) 𝕜) - M) * resPartial M z K) i j)
      atTop (𝓝 (((z • (1 : Matrix (Fin n) (Fin n) 𝕜) - M) * res M z) i j)) := by
    simp only [Matrix.mul_apply]
    exact tendsto_finsetSum _ fun l _ =>
      tendsto_const_nhds.mul (tendsto_resPartial_apply M hr hz l j (hM l j))
  have h2 : Tendsto (fun K => ((z • (1 : Matrix (Fin n) (Fin n) 𝕜) - M) * resPartial M z K) i j)
      atTop (𝓝 ((1 : Matrix (Fin n) (Fin n) 𝕜) i j)) := by
    simp only [smul_one_sub_mul_resPartial M hz0, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul]
    simpa using tendsto_const_nhds.sub (tendsto_inv_pow_mul_apply M hr hz i j (hM i j))
  exact tendsto_nhds_unique h1 h2

/-- The resolvent series is a left inverse: `R(z)(zI − M) = I`. -/
theorem res_mul_smul_one_sub (M : Matrix (Fin n) (Fin n) 𝕜) {z : 𝕜} {r : ℝ} (hr : 0 ≤ r)
    (hz : r < ‖z‖) (hM : ∀ i j, ∀ᶠ k : ℕ in atTop, ‖(M ^ k) i j‖ ≤ r ^ k) :
    res M z * (z • (1 : Matrix (Fin n) (Fin n) 𝕜) - M) = 1 := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    exact absurd hz (not_lt.2 hr)
  ext i j
  have h1 : Tendsto (fun K => (resPartial M z K * (z • (1 : Matrix (Fin n) (Fin n) 𝕜) - M)) i j)
      atTop (𝓝 ((res M z * (z • (1 : Matrix (Fin n) (Fin n) 𝕜) - M)) i j)) := by
    simp only [Matrix.mul_apply]
    exact tendsto_finsetSum _ fun l _ =>
      (tendsto_resPartial_apply M hr hz i l (hM i l)).mul tendsto_const_nhds
  have h2 : Tendsto (fun K => (resPartial M z K * (z • (1 : Matrix (Fin n) (Fin n) 𝕜) - M)) i j)
      atTop (𝓝 ((1 : Matrix (Fin n) (Fin n) 𝕜) i j)) := by
    simp only [resPartial_mul_smul_one_sub M hz0, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul]
    simpa using tendsto_const_nhds.sub (tendsto_inv_pow_mul_apply M hr hz i j (hM i j))
  exact tendsto_nhds_unique h1 h2

/-! ### The real resolvent of a nonnegative matrix -/

/-- For `A ≥ 0` and `t > 0`, the entries of the resolvent series are nonnegative. -/
theorem res_nonneg {A : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 ≤ A i j) {t : ℝ} (ht : 0 < t)
    (i j : Fin n) : 0 ≤ res A t i j :=
  tsum_nonneg fun k => mul_nonneg (pow_nonneg (inv_nonneg.2 ht.le) _) (pow_nonneg_entries hA k i j)

/-- For `A ≥ 0` and `t > 0`, each entry of the resolvent dominates the first term `1/t` of the
diagonal series: `R(t)ᵢᵢ ≥ 1/t`. -/
theorem inv_le_res_diag [NeZero n] {A : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 ≤ A i j) {t r : ℝ}
    (hr : 0 ≤ r) (ht : r < t) (hM : ∀ i j, ∀ᶠ k : ℕ in atTop, ‖(A ^ k) i j‖ ≤ r ^ k) (i : Fin n) :
    t⁻¹ ≤ res A t i i := by
  have ht0 : 0 < t := hr.trans_lt ht
  have hs := summable_res_entry A hr (by rwa [Real.norm_eq_abs, abs_of_pos ht0]) i i (hM i i)
  rw [res_apply]
  have h0 : (t⁻¹) ^ (0 + 1) * (A ^ 0) i i = t⁻¹ := by simp
  calc t⁻¹ = (t⁻¹) ^ (0 + 1) * (A ^ 0) i i := h0.symm
    _ ≤ ∑' k : ℕ, (t⁻¹) ^ (k + 1) * (A ^ k) i i :=
        hs.le_tsum 0 fun k _ =>
          mul_nonneg (pow_nonneg (inv_nonneg.2 ht0.le) _) (pow_nonneg_entries hA k i i)

end SargentStachurski.OperatorsFixedPoints

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Perron–Frobenius theorem for nonnegative matrices

Sargent and Stachurski, *Dynamic Programming*, Volume 1, Theorem 2.3.1
(p. 69), the part for nonnegative matrices: if `A ≥ 0` then `ρ(A)` is an
eigenvalue of `A` with a nonnegative, nonzero right eigenvector `e` and a
nonnegative, nonzero left eigenvector `ε`. The book quotes the theorem from
Meyer (2000); the proof here is through the resolvent.

* A complex eigenvalue `μ` of modulus `ρ(A)` exists, since the spectrum is
  finite and nonempty.
* For `|z| = t > ρ(A)` the complex resolvent `(zI − A)⁻¹ = ∑ z^{−(k+1)}Aᵏ` is
  dominated entrywise by the real resolvent `(tI − A)⁻¹ ≥ 0`.
* If the real resolvent stayed bounded on `(ρ, ρ + δ)`, then along `z = (1+s)μ`
  the complex resolvent would stay bounded while `z → μ`, and a Neumann-series
  perturbation would make `μI − A` invertible: `μ` could not be in the
  spectrum. Hence the real resolvent is unbounded near `ρ`.
* Normalising `(tI − A)⁻¹𝟙` to the simplex and letting `t ↓ ρ` along a sequence
  where the entries blow up, compactness of the simplex yields a limit `e ≥ 0`
  with `∑ e = 1` and `(ρI − A)e = 0`.

The statements for irreducible and everywhere-positive matrices (positivity and
uniqueness of the eigenvectors, the convergence (2.11)) are not claimed here;
the plan is to prove them with Chapter 6.
-/

open Matrix Finset Filter Topology

namespace SargentStachurski.OperatorsFixedPoints

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} [NeZero n]

/-- A complex eigenvalue of maximal modulus exists: `‖μ‖ = ρ(A)` for some `μ` in the spectrum. -/
theorem exists_mem_spectrum_norm_eq (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ μ ∈ spectrum ℂ (complexify A), ‖μ‖ = specRad A := by
  have : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  have hne : (spectrum ℂ (complexify A)).Nonempty := spectrum.nonempty _
  have hfin : (spectrum ℂ (complexify A)).Finite := Matrix.finite_spectrum _
  obtain ⟨μ₀, hμ₀⟩ := hne
  obtain ⟨μ, hμ, hmax⟩ := hfin.toFinset.exists_max_image (fun z => ‖z‖)
    ⟨μ₀, hfin.mem_toFinset.2 hμ₀⟩
  have hμ' : μ ∈ spectrum ℂ (complexify A) := hfin.mem_toFinset.1 hμ
  refine ⟨μ, hμ', le_antisymm (norm_le_specRad_of_mem_spectrum A hμ') ?_⟩
  have h1 : spectralRadius ℂ (complexify A) ≤ (‖μ‖₊ : ENNReal) := by
    rw [spectralRadius_eq_of_unital (𝕜 := ℂ) (complexify A)]
    refine iSup₂_le fun z hz => ?_
    exact_mod_cast hmax z (hfin.mem_toFinset.2 hz)
  have := ENNReal.toReal_mono ENNReal.coe_ne_top h1
  rwa [ENNReal.coe_toReal, coe_nnnorm] at this

/-- Entrywise Gelfand bound for the complexification. -/
theorem eventually_norm_entry_pow_complexify_le (A : Matrix (Fin n) (Fin n) ℝ) {r : ℝ}
    (hr : specRad A < r) (i j : Fin n) :
    ∀ᶠ k : ℕ in atTop, ‖((complexify A) ^ k) i j‖ ≤ r ^ k :=
  (eventually_abs_entry_pow_le A hr i j).mono fun k hk => by
    rw [← complexify_pow, complexify_apply, Complex.norm_real, Real.norm_eq_abs]
    exact hk

/-- The real resolvent series at `t > ρ(A)` is a two-sided inverse of `tI − A`. -/
theorem smul_one_sub_mul_res_real (A : Matrix (Fin n) (Fin n) ℝ) {t : ℝ} (hρ : specRad A < t) :
    (t • (1 : Matrix (Fin n) (Fin n) ℝ) - A) * res A t = 1 ∧
      res A t * (t • (1 : Matrix (Fin n) (Fin n) ℝ) - A) = 1 := by
  obtain ⟨r, hr1, hr2⟩ := exists_between hρ
  have hr0 : 0 ≤ r := (specRad_nonneg A).trans hr1.le
  have hrt : r < ‖t‖ := by rwa [Real.norm_eq_abs, abs_of_pos (hr0.trans_lt hr2)]
  have hM : ∀ i j, ∀ᶠ k : ℕ in atTop, ‖(A ^ k) i j‖ ≤ r ^ k := fun i j =>
    (eventually_abs_entry_pow_le A hr1 i j).mono fun k hk => by rwa [Real.norm_eq_abs]
  exact ⟨smul_one_sub_mul_res A hr0 hrt hM, res_mul_smul_one_sub A hr0 hrt hM⟩

/-- Domination: for `|z| = t > ρ(A)`, `|R_ℂ(z)ᵢⱼ| ≤ R_ℝ(t)ᵢⱼ`. -/
theorem norm_res_complexify_le (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j) {z : ℂ}
    {t : ℝ} (hzt : ‖z‖ = t) (hρ : specRad A < t) (i j : Fin n) :
    ‖res (complexify A) z i j‖ ≤ res A t i j := by
  obtain ⟨r, hr1, hr2⟩ := exists_between hρ
  have hr0 : 0 ≤ r := (specRad_nonneg A).trans hr1.le
  have ht0 : 0 < t := hr0.trans_lt hr2
  have hterm : ∀ k : ℕ, ‖(z⁻¹) ^ (k + 1) * ((complexify A) ^ k) i j‖ =
      (t⁻¹) ^ (k + 1) * (A ^ k) i j := by
    intro k
    rw [norm_mul, norm_pow, norm_inv, hzt, ← complexify_pow, complexify_apply, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (pow_nonneg_entries hA k i j)]
  have hreal : Summable fun k : ℕ => (t⁻¹) ^ (k + 1) * (A ^ k) i j :=
    summable_res_entry A hr0 (by rwa [Real.norm_eq_abs, abs_of_pos ht0]) i j
      ((eventually_abs_entry_pow_le A hr1 i j).mono fun k hk => by rwa [Real.norm_eq_abs])
  have hnorm : Summable fun k : ℕ => ‖(z⁻¹) ^ (k + 1) * ((complexify A) ^ k) i j‖ := by
    simp_rw [hterm]
    exact hreal
  rw [res_apply, res_apply]
  refine (norm_tsum_le_tsum_norm hnorm).trans (le_of_eq ?_)
  exact tsum_congr hterm

omit [NeZero n] in
/-- The ℓ∞ operator norm of a complex matrix is bounded by `n` times a bound on its entries. -/
theorem norm_le_card_mul_of_entry_norm_le (X : Matrix (Fin n) (Fin n) ℂ) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ i j, ‖X i j‖ ≤ M) : ‖X‖ ≤ n * M := by
  rw [Matrix.linfty_opNorm_def]
  have hnM : (0 : ℝ) ≤ n * M := by positivity
  have hrow : ∀ i, (∑ j, ‖X i j‖₊ : NNReal) ≤ (n * M).toNNReal := by
    intro i
    refine (NNReal.coe_le_coe (r₁ := ∑ j, ‖X i j‖₊) (r₂ := (n * M).toNNReal)).1 ?_
    rw [NNReal.coe_sum, Real.coe_toNNReal _ hnM]
    simp only [coe_nnnorm]
    calc ∑ j, ‖X i j‖ ≤ ∑ _j : Fin n, M := sum_le_sum fun j _ => h i j
      _ = n * M := by simp
  have hsup : (univ.sup fun i => ∑ j, ‖X i j‖₊) ≤ (n * M).toNNReal :=
    Finset.sup_le fun i _ => hrow i
  have := NNReal.coe_le_coe.2 hsup
  rwa [Real.coe_toNNReal _ hnM] at this

/-- If the real resolvent were bounded on `(ρ, ρ + δ)`, no complex number of modulus `ρ > 0`
could be in the spectrum: along `z = (1 + s)μ → μ` the complex resolvent stays bounded, and a
Neumann perturbation makes `μI − A` invertible. -/
theorem notMem_spectrum_of_res_bounded (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hρpos : 0 < specRad A) {μ : ℂ} (hμ : ‖μ‖ = specRad A) {M δ : ℝ} (hδ : 0 < δ) (hM0 : 0 ≤ M)
    (hM : ∀ t, specRad A < t → t < specRad A + δ → ∀ i j, res A t i j ≤ M) :
    μ ∉ spectrum ℂ (complexify A) := by
  set ρ := specRad A with hρ
  set C : ℝ := n * M + 1 with hC
  have hCpos : 0 < C := by positivity
  -- the step `s`
  set ε : ℝ := min δ (1 / C) with hε
  have hεpos : 0 < ε := lt_min hδ (by positivity)
  set s : ℝ := ε / (2 * ρ) with hs
  have hspos : 0 < s := by positivity
  have hsρ : s * ρ = ε / 2 := by rw [hs]; field_simp
  have hsρδ : s * ρ < δ := by rw [hsρ]; linarith [min_le_left δ (1 / C)]
  have hsρC : s * ρ * C < 1 := by
    rw [hsρ]
    have : ε ≤ 1 / C := min_le_right _ _
    have : ε * C ≤ 1 := by rwa [le_div_iff₀ hCpos] at this
    linarith
  -- the point `z = (1 + s) μ`, of modulus `t = (1 + s) ρ`
  set z : ℂ := ((1 + s : ℝ) : ℂ) * μ with hz
  set t : ℝ := (1 + s) * ρ with ht
  have hzt : ‖z‖ = t := by
    rw [hz, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith), hμ]
  have hρt : ρ < t := by rw [ht]; nlinarith
  have htδ : t < ρ + δ := by rw [ht]; nlinarith
  -- the complex resolvent at `z` is a two-sided inverse and is bounded
  obtain ⟨r, hr1, hr2⟩ := exists_between hρt
  have hr0 : 0 ≤ r := (specRad_nonneg A).trans hr1.le
  have hrz : r < ‖z‖ := by rw [hzt]; exact hr2
  have hMc : ∀ i j, ∀ᶠ k : ℕ in atTop, ‖((complexify A) ^ k) i j‖ ≤ r ^ k := fun i j =>
    eventually_norm_entry_pow_complexify_le A hr1 i j
  set R := res (complexify A) z with hR
  have hR1 : (z • (1 : Matrix (Fin n) (Fin n) ℂ) - complexify A) * R = 1 :=
    smul_one_sub_mul_res (complexify A) hr0 hrz hMc
  have hR2 : R * (z • (1 : Matrix (Fin n) (Fin n) ℂ) - complexify A) = 1 :=
    res_mul_smul_one_sub (complexify A) hr0 hrz hMc
  have hRnorm : ‖R‖ ≤ n * M :=
    norm_le_card_mul_of_entry_norm_le R hM0 fun i j =>
      (norm_res_complexify_le A hA hzt hρt i j).trans (hM t hρt htδ i j)
  -- the perturbation `(z − μ) • R` has norm `< 1`
  have hzμ : z - μ = ((s : ℝ) : ℂ) * μ := by rw [hz]; push_cast; ring
  have hpert : ‖(z - μ) • R‖ < 1 := by
    rw [norm_smul, hzμ, norm_mul, Complex.norm_real, Real.norm_of_nonneg hspos.le, hμ]
    calc s * ρ * ‖R‖ ≤ s * ρ * (n * M) := by gcongr
      _ < s * ρ * C := by rw [hC]; nlinarith
      _ < 1 := hsρC
  -- `μI − A = (zI − A)(I − (z − μ)R)`, a product of units
  have hfactor : (z • (1 : Matrix (Fin n) (Fin n) ℂ) - complexify A) * (1 - (z - μ) • R) =
      μ • (1 : Matrix (Fin n) (Fin n) ℂ) - complexify A := by
    calc (z • (1 : Matrix (Fin n) (Fin n) ℂ) - complexify A) * (1 - (z - μ) • R)
        = (z • (1 : Matrix (Fin n) (Fin n) ℂ) - complexify A) -
            (z - μ) • ((z • (1 : Matrix (Fin n) (Fin n) ℂ) - complexify A) * R) := by
          rw [mul_sub, mul_one, Matrix.mul_smul]
      _ = (z • (1 : Matrix (Fin n) (Fin n) ℂ) - complexify A) -
            (z - μ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by rw [hR1]
      _ = μ • (1 : Matrix (Fin n) (Fin n) ℂ) - complexify A := by
          rw [sub_smul]
          abel
  have hunit1 : IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ) - complexify A) :=
    ⟨⟨z • 1 - complexify A, R, hR1, hR2⟩, rfl⟩
  have hunit2 : IsUnit (1 - (z - μ) • R) := (Units.oneSub ((z - μ) • R) hpert).isUnit
  rw [spectrum.notMem_iff, Algebra.algebraMap_eq_smul_one, ← hfactor]
  exact hunit1.mul hunit2

/-- The real resolvent is unbounded as `t ↓ ρ(A)`: for every bound `M` and every `δ > 0` some
entry of `R(t)` exceeds `M` at some `t ∈ (ρ, ρ + δ)`. -/
theorem exists_res_entry_gt (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j) (M : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ t, specRad A < t ∧ t < specRad A + δ ∧ ∃ i j, M < res A t i j := by
  rcases (specRad_nonneg A).lt_or_eq with hρpos | hρ0
  · by_contra hcon
    have hM : ∀ t, specRad A < t → t < specRad A + δ → ∀ i j, res A t i j ≤ M :=
      fun t h1 h2 i j => le_of_not_gt fun hgt => hcon ⟨t, h1, h2, i, j, hgt⟩
    have hM0 : 0 ≤ M := by
      have h1 : specRad A < specRad A + δ / 2 := by linarith
      have h2 : specRad A + δ / 2 < specRad A + δ := by linarith
      exact (res_nonneg hA (hρpos.trans h1) ⟨0, NeZero.pos n⟩ ⟨0, NeZero.pos n⟩).trans
        (hM _ h1 h2 _ _)
    obtain ⟨μ, hμmem, hμ⟩ := exists_mem_spectrum_norm_eq A
    exact notMem_spectrum_of_res_bounded A hA hρpos hμ hδ hM0 hM hμmem
  · -- `ρ = 0`: the diagonal entries are at least `1/t`
    have hρ : specRad A = 0 := hρ0.symm
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = min (δ / 2) (1 / (2 * (|M| + 1))) := ⟨_, rfl⟩
    have htpos : 0 < t := by rw [ht]; exact lt_min (by linarith) (by positivity)
    have htδ : t < δ := by rw [ht]; exact (min_le_left _ _).trans_lt (by linarith)
    have htM : t ≤ 1 / (2 * (|M| + 1)) := by rw [ht]; exact min_le_right _ _
    refine ⟨t, by rw [hρ]; exact htpos, by rw [hρ]; linarith, ⟨0, NeZero.pos n⟩,
      ⟨0, NeZero.pos n⟩, ?_⟩
    have hbound : ∀ i j, ∀ᶠ k : ℕ in atTop, ‖(A ^ k) i j‖ ≤ (t / 2) ^ k := fun i j =>
      (eventually_abs_entry_pow_le A (r := t / 2) (by rw [hρ]; positivity) i j).mono
        fun k hk => by rwa [Real.norm_eq_abs]
    have hdiag := inv_le_res_diag hA (r := t / 2) (by positivity) (half_lt_self htpos) hbound
      ⟨0, NeZero.pos n⟩
    have h2 : 2 * (|M| + 1) ≤ t⁻¹ := by
      rw [le_inv_comm₀ (by positivity) htpos]
      simpa [one_div] using htM
    have hMabs : M ≤ |M| := le_abs_self M
    have habs0 : 0 ≤ |M| := abs_nonneg M
    linarith

omit [NeZero n] in
/-- The simplex `{y ≥ 0 : ∑ y = 1}` is compact. -/
theorem isCompact_simplex :
    IsCompact {y : Fin n → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} := by
  have hsub : {y : Fin n → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} ⊆ Set.Icc 0 1 := by
    rintro y ⟨hy0, hy1⟩
    refine ⟨fun i => hy0 i, fun i => ?_⟩
    calc y i ≤ ∑ j, y j := single_le_sum (fun j _ => hy0 j) (mem_univ i)
      _ = 1 := hy1
  have hclosed : IsClosed {y : Fin n → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} := by
    have h1 : IsClosed {y : Fin n → ℝ | ∀ i, 0 ≤ y i} := by
      have : {y : Fin n → ℝ | ∀ i, 0 ≤ y i} = ⋂ i, {y | 0 ≤ y i} := by ext; simp
      rw [this]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    have h2 : IsClosed {y : Fin n → ℝ | ∑ i, y i = 1} :=
      isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
    exact h1.inter h2
  exact isCompact_Icc.of_isClosed_subset hclosed hsub

/-- **Theorem 2.3.1 (Perron–Frobenius), nonnegative case** (p. 69): if `A ≥ 0` then `ρ(A)` is an
eigenvalue of `A` with a nonnegative, nonzero right eigenvector. -/
theorem perron_frobenius (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j) :
    ∃ e : Fin n → ℝ, (∀ i, 0 ≤ e i) ∧ e ≠ 0 ∧ A *ᵥ e = specRad A • e := by
  set ρ := specRad A with hρ
  -- a sequence `tₖ ↓ ρ` along which some entry of `R(tₖ)` exceeds `k`
  choose t ht using fun k : ℕ => exists_res_entry_gt A hA (k : ℝ) (δ := 1 / (k + 1))
    (by positivity)
  have htρ : ∀ k, ρ < t k := fun k => (ht k).1
  have htlim : Tendsto t atTop (𝓝 ρ) := by
    have h1 : ∀ k, t k ≤ ρ + 1 / ((k : ℝ) + 1) := fun k => (ht k).2.1.le
    have h2 : Tendsto (fun k : ℕ => ρ + 1 / ((k : ℝ) + 1)) atTop (𝓝 (ρ + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
      (fun k => (htρ k).le) h1
  -- the row-sum vectors `vₖ = R(tₖ)𝟙 ≥ 0` and their totals `Nₖ > k`
  set v : ℕ → Fin n → ℝ := fun k i => ∑ j, res A (t k) i j with hv
  have hv_eq : ∀ k, v k = res A (t k) *ᵥ fun _ => 1 := by
    intro k
    funext i
    simp [hv, mulVec, dotProduct]
  have hv0 : ∀ k i, 0 ≤ v k i := fun k i =>
    sum_nonneg fun j _ => res_nonneg hA ((specRad_nonneg A).trans_lt (htρ k)) i j
  set N : ℕ → ℝ := fun k => ∑ i, v k i with hN
  have hNgt : ∀ k : ℕ, (k : ℝ) < N k := by
    intro k
    obtain ⟨i, j, hij⟩ := (ht k).2.2
    calc (k : ℝ) < res A (t k) i j := hij
      _ ≤ v k i := single_le_sum
            (fun j _ => res_nonneg hA ((specRad_nonneg A).trans_lt (htρ k)) i j) (mem_univ j)
      _ ≤ N k := single_le_sum (fun i _ => hv0 k i) (mem_univ i)
  have hNpos : ∀ k, 0 < N k := fun k => (Nat.cast_nonneg k).trans_lt (hNgt k)
  -- `(tₖ I − A) vₖ = 𝟙`
  have hres : ∀ k, (t k • (1 : Matrix (Fin n) (Fin n) ℝ) - A) *ᵥ v k = fun _ => 1 := by
    intro k
    rw [hv_eq, mulVec_mulVec, (smul_one_sub_mul_res_real A (htρ k)).1, one_mulVec]
  -- the normalised vectors lie in the simplex
  set y : ℕ → Fin n → ℝ := fun k => (N k)⁻¹ • v k with hy
  have hyS : ∀ k, y k ∈ {y : Fin n → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} := by
    intro k
    refine ⟨fun i => mul_nonneg (inv_nonneg.2 (hNpos k).le) (hv0 k i), ?_⟩
    simp only [hy, Pi.smul_apply, smul_eq_mul, ← mul_sum]
    exact inv_mul_cancel₀ (hNpos k).ne'
  obtain ⟨e, heS, φ, hφ, hlim⟩ := isCompact_simplex.tendsto_subseq hyS
  refine ⟨e, heS.1, ?_, ?_⟩
  · intro he
    have := heS.2
    rw [he] at this
    simp at this
  · -- `(tₖ I − A) yₖ = Nₖ⁻¹ 𝟙 → 0`, and the left side tends to `(ρI − A) e`
    have hφlim : Tendsto (fun k => t (φ k)) atTop (𝓝 ρ) := htlim.comp hφ.tendsto_atTop
    have hNinv : Tendsto (fun k => (N (φ k))⁻¹) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k => N (φ k)) atTop atTop :=
        tendsto_atTop_mono (fun k => (hNgt (φ k)).le)
          (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
      exact tendsto_inv_atTop_zero.comp h1
    funext i
    -- the `i`-th coordinate of `(tₖI − A) yₖ`
    have hcoord : ∀ k, (t (φ k) • (1 : Matrix (Fin n) (Fin n) ℝ) - A) *ᵥ y (φ k) =
        (N (φ k))⁻¹ • fun _ => (1 : ℝ) := by
      intro k
      simp only [hy, mulVec_smul, hres]
    have h1 : Tendsto (fun k => ((t (φ k) • (1 : Matrix (Fin n) (Fin n) ℝ) - A) *ᵥ y (φ k)) i)
        atTop (𝓝 (((ρ • (1 : Matrix (Fin n) (Fin n) ℝ) - A) *ᵥ e) i)) := by
      simp only [mulVec, dotProduct, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      refine tendsto_finsetSum _ fun x _ => ?_
      exact ((hφlim.mul tendsto_const_nhds).sub tendsto_const_nhds).mul
        (tendsto_pi_nhds.1 hlim x)
    have h2 : Tendsto (fun k => ((t (φ k) • (1 : Matrix (Fin n) (Fin n) ℝ) - A) *ᵥ y (φ k)) i)
        atTop (𝓝 0) := by
      simp only [hcoord, Pi.smul_apply, smul_eq_mul, mul_one]
      exact hNinv
    have h3 := tendsto_nhds_unique h1 h2
    rw [sub_mulVec, smul_mulVec, one_mulVec] at h3
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h3
    simp only [Pi.smul_apply, smul_eq_mul]
    linarith

/-- Theorem 2.3.1 (p. 69), left eigenvector: `εA = ρ(A)ε` for some nonnegative, nonzero `ε`,
by applying the right-eigenvector statement to `Aᵀ`. -/
theorem perron_frobenius_left (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j) :
    ∃ ε : Fin n → ℝ, (∀ i, 0 ≤ ε i) ∧ ε ≠ 0 ∧ ε ᵥ* A = specRad A • ε := by
  obtain ⟨ε, hε0, hεne, hε⟩ := perron_frobenius Aᵀ fun i j => hA j i
  refine ⟨ε, hε0, hεne, ?_⟩
  rw [← mulVec_transpose, hε, specRad_transpose]

end SargentStachurski.OperatorsFixedPoints

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Consequences of Perron–Frobenius: spectral bounds, the local spectral radius, Markov matrices

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §2.3.1.1–§2.3.1.3
(pp. 69–71).

* Lemma 2.3.2 (Exercise 2.3.1): for `A ≥ 0`, `ρ(A)` lies between the smallest
  and largest row sums, and between the smallest and largest column sums, by
  summing the eigenvector equations.
* Lemma 2.3.3: for `A ≥ 0` and `h ≫ 0`, the local spectral radius
  `‖Aᵏh‖^{1/k}` converges to `ρ(A)`; the book cites Krasnosel'skii et al.
  (1972). The proof here squeezes between `‖Aᵏ‖^{1/k} (min h)^{1/k}` and
  `‖Aᵏ‖^{1/k} ‖h‖^{1/k}`, both of which converge to `ρ(A)` by Gelfand's formula.
  Norms are the supremum norm on vectors and the induced ℓ∞ operator norm.
* Markov matrices (Exercise 2.3.2 (i)–(iii), Exercise 2.3.3). The uniqueness
  and positivity of the stationary distribution for irreducible `P`
  (Exercise 2.3.2 (iv)) rest on the irreducible Perron–Frobenius theorem and
  are not claimed here.
-/

open Matrix Finset Filter Topology

namespace SargentStachurski.OperatorsFixedPoints

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} [NeZero n]

/-! ### Lemma 2.3.2 -/

/-- Lemma 2.3.2 (ii), p. 70, lower bound: if every column sum of `A ≥ 0` is at least `c`, then
`ρ(A) ≥ c`. Summing `Ae = ρe` over the coordinates of a nonnegative eigenvector `e` with `∑ e = S`
gives `ρS = ∑ⱼ colsumⱼ eⱼ ≥ cS`. -/
theorem le_specRad_of_colsum_ge (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j) {c : ℝ}
    (hc : ∀ j, c ≤ ∑ i, A i j) : c ≤ specRad A := by
  obtain ⟨e, he0, hene, he⟩ := perron_frobenius A hA
  have hS : 0 < ∑ j, e j := by
    rcases (sum_nonneg fun j _ => he0 j).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hene
      funext j
      exact (sum_eq_zero_iff_of_nonneg fun j _ => he0 j).1 h.symm j (mem_univ j)
  have hsum : specRad A * ∑ j, e j = ∑ j, (∑ i, A i j) * e j := by
    calc specRad A * ∑ j, e j = ∑ i, (A *ᵥ e) i := by
          rw [he]
          simp only [Pi.smul_apply, smul_eq_mul, ← mul_sum]
      _ = ∑ i, ∑ j, A i j * e j := rfl
      _ = ∑ j, ∑ i, A i j * e j := sum_comm
      _ = ∑ j, (∑ i, A i j) * e j := by simp only [sum_mul]
  have hge : c * ∑ j, e j ≤ ∑ j, (∑ i, A i j) * e j := by
    rw [mul_sum]
    exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hc j) (he0 j)
  rw [← hsum] at hge
  exact le_of_mul_le_mul_right hge hS

/-- Lemma 2.3.2 (ii), p. 70, upper bound: if every column sum of `A ≥ 0` is at most `C`, then
`ρ(A) ≤ C`. -/
theorem specRad_le_of_colsum_le (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j) {C : ℝ}
    (hC : ∀ j, ∑ i, A i j ≤ C) : specRad A ≤ C := by
  obtain ⟨e, he0, hene, he⟩ := perron_frobenius A hA
  have hS : 0 < ∑ j, e j := by
    rcases (sum_nonneg fun j _ => he0 j).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hene
      funext j
      exact (sum_eq_zero_iff_of_nonneg fun j _ => he0 j).1 h.symm j (mem_univ j)
  have hsum : specRad A * ∑ j, e j = ∑ j, (∑ i, A i j) * e j := by
    calc specRad A * ∑ j, e j = ∑ i, (A *ᵥ e) i := by
          rw [he]
          simp only [Pi.smul_apply, smul_eq_mul, ← mul_sum]
      _ = ∑ i, ∑ j, A i j * e j := rfl
      _ = ∑ j, ∑ i, A i j * e j := sum_comm
      _ = ∑ j, (∑ i, A i j) * e j := by simp only [sum_mul]
  have hle : ∑ j, (∑ i, A i j) * e j ≤ C * ∑ j, e j := by
    rw [mul_sum]
    exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hC j) (he0 j)
  rw [← hsum] at hle
  exact le_of_mul_le_mul_right hle hS

/-- Lemma 2.3.2 (i), p. 70: `ρ(A)` lies between the smallest and largest row sums of `A ≥ 0`, by
transposition. -/
theorem le_specRad_of_rowsum_ge (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j) {c : ℝ}
    (hc : ∀ i, c ≤ ∑ j, A i j) : c ≤ specRad A := by
  rw [← specRad_transpose]
  exact le_specRad_of_colsum_ge Aᵀ (fun i j => hA j i) hc

theorem specRad_le_of_rowsum_le (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j) {C : ℝ}
    (hC : ∀ i, ∑ j, A i j ≤ C) : specRad A ≤ C := by
  rw [← specRad_transpose]
  exact specRad_le_of_colsum_le Aᵀ (fun i j => hA j i) hC

/-! ### Lemma 2.3.3: the local spectral radius -/

/-- `c^{1/k} → 1` for `c > 0`. -/
theorem tendsto_rpow_one_div_natCast {c : ℝ} (hc : 0 < c) :
    Tendsto (fun k : ℕ => c ^ (1 / (k : ℝ))) atTop (𝓝 1) := by
  have h1 : Tendsto (fun k : ℕ => Real.log c * (1 / (k : ℝ))) atTop (𝓝 (Real.log c * 0)) :=
    tendsto_const_nhds.mul tendsto_one_div_atTop_nhds_zero_nat
  rw [mul_zero] at h1
  have h2 := (Real.continuous_exp.tendsto 0).comp h1
  rw [Real.exp_zero] at h2
  refine h2.congr fun k => ?_
  simp only [Function.comp]
  rw [Real.rpow_def_of_pos hc, mul_comm]

omit [NeZero n] in
/-- For `A ≥ 0` and `h ≥ m𝟙 > 0`, the row sums of `Aᵏ` are bounded by `(Aᵏh)ᵢ/m`, hence
`m‖Aᵏ‖ ≤ ‖Aᵏh‖`. -/
theorem norm_pow_mul_le_norm_mulVec (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    {h : Fin n → ℝ} {m : ℝ} (hm : 0 < m) (hmh : ∀ j, m ≤ h j) (k : ℕ) :
    m * ‖A ^ k‖ ≤ ‖A ^ k *ᵥ h‖ := by
  have hAk := pow_nonneg_entries hA k
  rw [← le_div_iff₀' hm]
  refine norm_le_of_rowsum_abs_le (A ^ k) (div_nonneg (norm_nonneg _) hm.le) fun i => ?_
  rw [le_div_iff₀ hm]
  calc (∑ j, |(A ^ k) i j|) * m = ∑ j, (A ^ k) i j * m := by
        rw [sum_mul]
        exact sum_congr rfl fun j _ => by rw [abs_of_nonneg (hAk i j)]
    _ ≤ ∑ j, (A ^ k) i j * h j := sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hmh j) (hAk i j)
    _ = (A ^ k *ᵥ h) i := rfl
    _ ≤ ‖A ^ k *ᵥ h‖ := by
        have := norm_le_pi_norm (A ^ k *ᵥ h) i
        rw [Real.norm_eq_abs] at this
        exact (le_abs_self _).trans this

/-- Lemma 2.3.3 (p. 70): for `A ≥ 0` and `h ≫ 0`, `‖Aᵏh‖^{1/k} → ρ(A)`, in the supremum norm. -/
theorem tendsto_norm_pow_mulVec_rpow (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    {h : Fin n → ℝ} (hh : ∀ j, 0 < h j) :
    Tendsto (fun k : ℕ => ‖A ^ k *ᵥ h‖ ^ (1 / (k : ℝ))) atTop (𝓝 (specRad A)) := by
  -- the minimum `m` of `h` and the norm `‖h‖`
  obtain ⟨j₀, -, hj₀⟩ := exists_min_image univ h univ_nonempty
  set m := h j₀ with hm
  have hmpos : 0 < m := hh j₀
  have hmh : ∀ j, m ≤ h j := fun j => hj₀ j (mem_univ j)
  have hhnorm : 0 < ‖h‖ := by
    have := norm_le_pi_norm h j₀
    rw [Real.norm_eq_abs, abs_of_pos (hh j₀)] at this
    exact hmpos.trans_le this
  have hG := tendsto_norm_pow_rpow A
  -- upper: `‖Aᵏh‖^{1/k} ≤ ‖Aᵏ‖^{1/k} ‖h‖^{1/k}`
  have hup : Tendsto (fun k : ℕ => ‖A ^ k‖ ^ (1 / (k : ℝ)) * ‖h‖ ^ (1 / (k : ℝ))) atTop
      (𝓝 (specRad A * 1)) := hG.mul (tendsto_rpow_one_div_natCast hhnorm)
  -- lower: `m^{1/k} ‖Aᵏ‖^{1/k} ≤ ‖Aᵏh‖^{1/k}`
  have hlo : Tendsto (fun k : ℕ => m ^ (1 / (k : ℝ)) * ‖A ^ k‖ ^ (1 / (k : ℝ))) atTop
      (𝓝 (1 * specRad A)) := (tendsto_rpow_one_div_natCast hmpos).mul hG
  rw [mul_one] at hup
  rw [one_mul] at hlo
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hup (fun k => ?_) (fun k => ?_)
  · rw [← Real.mul_rpow hmpos.le (norm_nonneg _)]
    exact Real.rpow_le_rpow (by positivity) (norm_pow_mul_le_norm_mulVec A hA hmpos hmh k)
      (by positivity)
  · rw [← Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    exact Real.rpow_le_rpow (norm_nonneg _) (Matrix.linfty_opNorm_mulVec _ _) (by positivity)

/-! ### Markov matrices (§2.3.1.3) -/

/-- A stochastic (Markov) matrix (p. 71): nonnegative with unit row sums. -/
structure IsMarkov (P : Matrix (Fin n) (Fin n) ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ P i j
  rowsum : ∀ i, ∑ j, P i j = 1

omit [NeZero n] in
/-- Exercise 2.3.2 (i), p. 71: the product of Markov matrices is Markov. -/
theorem IsMarkov.mul {P Q : Matrix (Fin n) (Fin n) ℝ} (hP : IsMarkov P) (hQ : IsMarkov Q) :
    IsMarkov (P * Q) where
  nonneg i j := by
    rw [Matrix.mul_apply]
    exact sum_nonneg fun l _ => mul_nonneg (hP.nonneg i l) (hQ.nonneg l j)
  rowsum i := by
    simp only [Matrix.mul_apply]
    rw [sum_comm]
    simp only [← mul_sum, hQ.rowsum, mul_one, hP.rowsum]

omit [NeZero n] in
/-- Powers of a Markov matrix are Markov. -/
theorem IsMarkov.pow {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsMarkov P) (k : ℕ) :
    IsMarkov (P ^ k) := by
  induction k with
  | zero =>
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
    · simp [pow_zero, Matrix.one_apply]
  | succ k ih => rw [pow_succ]; exact ih.mul hP

/-- Exercise 2.3.2 (ii), p. 71: `ρ(P) = 1` for a Markov matrix. -/
theorem IsMarkov.specRad_eq_one {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsMarkov P) : specRad P = 1 :=
  specRad_eq_of_rowsum_eq P hP.nonneg zero_le_one hP.rowsum

/-- Exercise 2.3.2 (iii), p. 71: a Markov matrix has a stationary distribution, a row vector
`ψ ≥ 0` with `ψ𝟙 = 1` and `ψP = ψ`, by the left Perron–Frobenius eigenvector for `ρ(P) = 1`. -/
theorem IsMarkov.exists_stationary {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsMarkov P) :
    ∃ ψ : Fin n → ℝ, (∀ i, 0 ≤ ψ i) ∧ ∑ i, ψ i = 1 ∧ ψ ᵥ* P = ψ := by
  obtain ⟨ε, hε0, hεne, hε⟩ := perron_frobenius_left P hP.nonneg
  rw [hP.specRad_eq_one, one_smul] at hε
  have hS : 0 < ∑ i, ε i := by
    rcases (sum_nonneg fun i _ => hε0 i).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hεne
      funext i
      exact (sum_eq_zero_iff_of_nonneg fun i _ => hε0 i).1 h.symm i (mem_univ i)
  refine ⟨(∑ i, ε i)⁻¹ • ε, fun i => mul_nonneg (inv_nonneg.2 hS.le) (hε0 i), ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, ← mul_sum]
    exact inv_mul_cancel₀ hS.ne'
  · rw [smul_vecMul, hε]

/-- Exercise 2.3.3 (p. 71): for a Markov matrix `P` and `ε > 0` there is no `h` with
`Ph ≥ h + ε`: at a maximiser `x̄` of `h`, `(Ph)(x̄) ≤ h(x̄)`. -/
theorem IsMarkov.not_mulVec_ge_add {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsMarkov P) {ε : ℝ}
    (hε : 0 < ε) : ¬ ∃ h : Fin n → ℝ, ∀ x, h x + ε ≤ (P *ᵥ h) x := by
  rintro ⟨h, hh⟩
  obtain ⟨x, -, hx⟩ := exists_max_image univ h univ_nonempty
  have : (P *ᵥ h) x ≤ h x := by
    calc (P *ᵥ h) x = ∑ y, P x y * h y := rfl
      _ ≤ ∑ y, P x y * h x :=
          sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hx y (mem_univ y)) (hP.nonneg x y)
      _ = h x := by rw [← sum_mul, hP.rowsum, one_mul]
  linarith [hh x]

end SargentStachurski.OperatorsFixedPoints

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The lake model

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §2.3.2 (pp. 71–75).

Workers exit the labour market at rate `d`, enter at rate `b` (initially
unemployed), separate at rate `α` and find jobs at rate `λ`, all in `(0, 1)`.
The unemployed and employed stocks `xₜ = (uₜ, eₜ)` follow `xₜ₊₁ = A xₜ` with the
matrix (2.13). Exercise 2.3.4: the workforce grows at `g = b − d`; Exercise
2.3.5: `ρ(A) = 1 + g`, because every column of `A ≥ 0` sums to `1 + g`;
Exercise 2.3.6: `1ᵀ` is a left eigenvector; Exercise 2.3.7: the right
eigenvector normalised by `1ᵀx̄ = 1` is (2.14). The long-run approximation
`Aᵗx₀ ≈ (1 + g)ᵗ n₀ x̄` rests on the convergence (2.11) of the
Perron–Frobenius theorem for positive matrices, which is not claimed here.
-/

open Matrix Finset

namespace SargentStachurski.OperatorsFixedPoints

/-- The lake model's rates, all in `(0, 1)` (p. 72). `lam` is the book's `λ`. -/
structure LakeModel where
  d : ℝ
  b : ℝ
  α : ℝ
  lam : ℝ
  d_pos : 0 < d
  d_lt_one : d < 1
  b_pos : 0 < b
  b_lt_one : b < 1
  α_pos : 0 < α
  α_lt_one : α < 1
  lam_pos : 0 < lam
  lam_lt_one : lam < 1

namespace LakeModel

variable (m : LakeModel)

/-- The transition matrix `A` of (2.13), acting on `x = (u, e)`. -/
noncomputable def A : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 - m.d) * (1 - m.lam) + m.b, (1 - m.d) * m.α + m.b;
     (1 - m.d) * m.lam, (1 - m.d) * (1 - m.α)]

/-- The growth rate of the workforce, `g = b − d` (p. 73). -/
def g : ℝ := m.b - m.d

theorem one_sub_d_pos : 0 < 1 - m.d := by linarith [m.d_lt_one]

theorem one_add_g_pos : 0 < 1 + m.g := by
  unfold g
  linarith [m.b_pos, m.d_lt_one]

/-- `A ≥ 0`. -/
theorem A_nonneg (i j : Fin 2) : 0 ≤ m.A i j := by
  have h1 := m.one_sub_d_pos
  have h2 := m.b_pos
  have h3 := m.α_pos
  have h4 := m.lam_pos
  have h5 := m.α_lt_one
  have h6 := m.lam_lt_one
  fin_cases i <;> fin_cases j <;> simp [A] <;> nlinarith

/-- Exercise 2.3.4 (p. 73): `nₜ₊₁ = (1 + g) nₜ`, since `uₜ₊₁ + eₜ₊₁ = (1 + g)(uₜ + eₜ)`. -/
theorem sum_mulVec (x : Fin 2 → ℝ) : (m.A *ᵥ x) 0 + (m.A *ᵥ x) 1 = (1 + m.g) * (x 0 + x 1) := by
  simp [A, mulVec, dotProduct, Fin.sum_univ_two, g]
  ring

/-- Every column of `A` sums to `1 + g`. -/
theorem colsum (j : Fin 2) : ∑ i, m.A i j = 1 + m.g := by
  fin_cases j <;> simp [A, Fin.sum_univ_two, g] <;> ring

/-- Exercise 2.3.5 (p. 73): `ρ(A) = 1 + g`. -/
theorem specRad_A : specRad m.A = 1 + m.g :=
  specRad_eq_of_colsum_eq m.A m.A_nonneg m.one_add_g_pos.le m.colsum

/-- Exercise 2.3.6 (p. 73): `1ᵀ = (1, 1)` is a left eigenvector of `A` for the eigenvalue
`1 + g`. -/
theorem one_vecMul : (fun _ => (1 : ℝ)) ᵥ* m.A = (1 + m.g) • fun _ => (1 : ℝ) := by
  funext j
  simp only [vecMul, dotProduct, one_mul, Pi.smul_apply, smul_eq_mul, mul_one]
  exact m.colsum j

/-- The long-run unemployment rate `ū` of (2.14), p. 74. -/
noncomputable def ubar : ℝ :=
  (1 + m.g - (1 - m.d) * (1 - m.α)) / (1 + m.g - (1 - m.d) * (1 - m.α) + (1 - m.d) * m.lam)

/-- The dominant right eigenvector `x̄ = (ū, ē)` with `ē = 1 − ū`, (2.14). -/
noncomputable def xbar : Fin 2 → ℝ := ![m.ubar, 1 - m.ubar]

theorem numer_eq : 1 + m.g - (1 - m.d) * (1 - m.α) = m.b + (1 - m.d) * m.α := by
  unfold g
  ring

theorem denom_pos : 0 < 1 + m.g - (1 - m.d) * (1 - m.α) + (1 - m.d) * m.lam := by
  rw [numer_eq]
  have := m.one_sub_d_pos
  have := m.b_pos
  have := m.α_pos
  have := m.lam_pos
  positivity

theorem xbar_sum : m.xbar 0 + m.xbar 1 = 1 := by
  simp [xbar]

/-- Exercise 2.3.7 (p. 73): `x̄` is a right eigenvector for `1 + g`. -/
theorem A_mulVec_xbar : m.A *ᵥ m.xbar = (1 + m.g) • m.xbar := by
  have hD := m.denom_pos
  have hub : m.ubar * (1 + m.g - (1 - m.d) * (1 - m.α) + (1 - m.d) * m.lam) =
      1 + m.g - (1 - m.d) * (1 - m.α) := by
    unfold ubar
    rw [div_mul_cancel₀ _ hD.ne']
  funext i
  fin_cases i <;> simp [A, xbar, mulVec, dotProduct, Fin.sum_univ_two, g] at hub ⊢ <;>
    nlinarith [hub]

/-- Exercise 2.3.7 (p. 73): `x̄` is the unique right eigenvector for `1 + g` with `1ᵀx = 1`. -/
theorem eq_xbar_of_eigen {x : Fin 2 → ℝ} (hx : m.A *ᵥ x = (1 + m.g) • x) (hsum : x 0 + x 1 = 1) :
    x = m.xbar := by
  have hD := m.denom_pos
  -- the first row gives `((1 − d)α + b) x₁ = (1 − d)λ x₀`; with `x₀ + x₁ = 1` this pins `x₀`
  have h0 : ((1 - m.d) * (1 - m.lam) + m.b) * x 0 + ((1 - m.d) * m.α + m.b) * x 1 =
      (1 + (m.b - m.d)) * x 0 := by
    have := congrFun hx 0
    simpa [A, mulVec, dotProduct, Fin.sum_univ_two, g] using this
  have hx0 : x 0 = m.ubar := by
    unfold ubar
    rw [eq_div_iff hD.ne', numer_eq]
    have hx1 : x 1 = 1 - x 0 := by linarith
    rw [hx1] at h0
    nlinarith [h0]
  funext i
  fin_cases i
  · simpa [xbar] using hx0
  · simp [xbar]
    linarith

end LakeModel

end SargentStachurski.OperatorsFixedPoints

set_option linter.style.longLine false
#print axioms SargentStachurski.OperatorsFixedPoints.GloballyStable
#print axioms SargentStachurski.OperatorsFixedPoints.globallyStable_of_tendsto
#print axioms SargentStachurski.OperatorsFixedPoints.GloballyStable.tendsto_iterate
#print axioms SargentStachurski.OperatorsFixedPoints.GloballyStable.exists_fixedPt
#print axioms SargentStachurski.OperatorsFixedPoints.GloballyStable.fixedPt_unique
#print axioms SargentStachurski.OperatorsFixedPoints.IsContractionOn
#print axioms SargentStachurski.OperatorsFixedPoints.IsContractionOn.mk
#print axioms SargentStachurski.OperatorsFixedPoints.IsContractionOn.mapsTo
#print axioms SargentStachurski.OperatorsFixedPoints.IsContractionOn.nonneg
#print axioms SargentStachurski.OperatorsFixedPoints.IsContractionOn.lt_one
#print axioms SargentStachurski.OperatorsFixedPoints.IsContractionOn.norm_sub_le
#print axioms SargentStachurski.OperatorsFixedPoints.IsContractionOn.fixedPt_unique
#print axioms SargentStachurski.OperatorsFixedPoints.IsContractionOn.iterate_mem
#print axioms SargentStachurski.OperatorsFixedPoints.IsContractionOn.norm_iterate_sub_fixedPt_le
#print axioms SargentStachurski.OperatorsFixedPoints.IsContractionOn.tendsto_iterate_fixedPt
#print axioms SargentStachurski.OperatorsFixedPoints.IsContractionOn.exists_fixedPt
#print axioms SargentStachurski.OperatorsFixedPoints.IsContractionOn.globallyStable
#print axioms SargentStachurski.OperatorsFixedPoints.IsContractionOn.globallyStable_univ
#print axioms SargentStachurski.OperatorsFixedPoints.LocallyStable
#print axioms SargentStachurski.OperatorsFixedPoints.GloballyStable.locallyStable
#print axioms SargentStachurski.OperatorsFixedPoints.IsConjugate
#print axioms SargentStachurski.OperatorsFixedPoints.IsConjugate.comm
#print axioms SargentStachurski.OperatorsFixedPoints.IsConjugate.of_comm
#print axioms SargentStachurski.OperatorsFixedPoints.IsConjugate.symm
#print axioms SargentStachurski.OperatorsFixedPoints.IsConjugate.trans
#print axioms SargentStachurski.OperatorsFixedPoints.IsConjugate.refl
#print axioms SargentStachurski.OperatorsFixedPoints.IsConjugate.iterate_comm
#print axioms SargentStachurski.OperatorsFixedPoints.IsConjugate.isFixedPt_iff
#print axioms SargentStachurski.OperatorsFixedPoints.IsConjugate.isFixedPt_symm_iff
#print axioms SargentStachurski.OperatorsFixedPoints.IsConjugate.fixedPointsEquiv
#print axioms SargentStachurski.OperatorsFixedPoints.IsConjugate.cardinal_fixedPoints_eq
#print axioms SargentStachurski.OperatorsFixedPoints.IsConjugate.existsUnique_fixedPt_iff
#print axioms SargentStachurski.OperatorsFixedPoints.isConjugate_similar
#print axioms SargentStachurski.OperatorsFixedPoints.IsTopConjugate
#print axioms SargentStachurski.OperatorsFixedPoints.IsTopConjugate.refl
#print axioms SargentStachurski.OperatorsFixedPoints.IsTopConjugate.symm
#print axioms SargentStachurski.OperatorsFixedPoints.IsTopConjugate.trans
#print axioms SargentStachurski.OperatorsFixedPoints.IsTopConjugate.tendsto_iterate_iff
#print axioms SargentStachurski.OperatorsFixedPoints.IsTopConjugate.globallyStable_iff
#print axioms SargentStachurski.OperatorsFixedPoints.IsTopConjugate.fixedPt_map
#print axioms SargentStachurski.OperatorsFixedPoints.IsTopConjugate.locallyStable_iff
#print axioms SargentStachurski.OperatorsFixedPoints.logHomeomorph
#print axioms SargentStachurski.OperatorsFixedPoints.logHomeomorph_apply
#print axioms SargentStachurski.OperatorsFixedPoints.logHomeomorph_symm_apply
#print axioms SargentStachurski.OperatorsFixedPoints.matrixHomeomorph
#print axioms SargentStachurski.OperatorsFixedPoints.det_ne_zero_of_mulVec_injective
#print axioms SargentStachurski.OperatorsFixedPoints.isTopConjugate_power
#print axioms SargentStachurski.OperatorsFixedPoints.iterate_sq
#print axioms SargentStachurski.OperatorsFixedPoints.locallyStable_sq_zero
#print axioms SargentStachurski.OperatorsFixedPoints.not_locallyStable_sq_one
#print axioms SargentStachurski.OperatorsFixedPoints.locallyStable_of_abs_deriv_lt_one
#print axioms SargentStachurski.OperatorsFixedPoints.ConvergesAtRateAtLeast
#print axioms SargentStachurski.OperatorsFixedPoints.ConvergesLinearly
#print axioms SargentStachurski.OperatorsFixedPoints.ConvergesQuadratically
#print axioms SargentStachurski.OperatorsFixedPoints.IsContractionOn.convergesAtRateAtLeast
#print axioms SargentStachurski.OperatorsFixedPoints.IsContractionOn.convergesLinearly
#print axioms SargentStachurski.OperatorsFixedPoints.error_ratio_near
#print axioms SargentStachurski.OperatorsFixedPoints.tendsto_error_ratio
#print axioms SargentStachurski.OperatorsFixedPoints.convergesLinearly_of_abs_deriv_lt_one
#print axioms SargentStachurski.OperatorsFixedPoints.newtonMap
#print axioms SargentStachurski.OperatorsFixedPoints.newtonMap_fixedPt_linearisation
#print axioms SargentStachurski.OperatorsFixedPoints.isFixedPt_newtonMap_iff
#print axioms SargentStachurski.OperatorsFixedPoints.real_le_isPartialOrder
#print axioms SargentStachurski.OperatorsFixedPoints.real_le_antisymm
#print axioms SargentStachurski.OperatorsFixedPoints.eq_isPartialOrder
#print axioms SargentStachurski.OperatorsFixedPoints.subset_isPartialOrder
#print axioms SargentStachurski.OperatorsFixedPoints.pointwise_isPartialOrder
#print axioms SargentStachurski.OperatorsFixedPoints.pointwise_le_def
#print axioms SargentStachurski.OperatorsFixedPoints.StrictLt
#print axioms SargentStachurski.OperatorsFixedPoints.not_strictLt_refl
#print axioms SargentStachurski.OperatorsFixedPoints.strictLt_not_isPartialOrder
#print axioms SargentStachurski.OperatorsFixedPoints.le_of_tendsto_pi
#print axioms SargentStachurski.OperatorsFixedPoints.matrix_le_iff_uncurry
#print axioms SargentStachurski.OperatorsFixedPoints.mulVec_le_mulVec
#print axioms SargentStachurski.OperatorsFixedPoints.abs_mulVec_le
#print axioms SargentStachurski.OperatorsFixedPoints.le_pow_mulVec_of_le
#print axioms SargentStachurski.OperatorsFixedPoints.strictLt_mulVec
#print axioms SargentStachurski.OperatorsFixedPoints.real_le_total
#print axioms SargentStachurski.OperatorsFixedPoints.nat_le_total
#print axioms SargentStachurski.OperatorsFixedPoints.pointwise_not_total
#print axioms SargentStachurski.OperatorsFixedPoints.subset_not_total
#print axioms SargentStachurski.OperatorsFixedPoints.isGreatest_unique
#print axioms SargentStachurski.OperatorsFixedPoints.isLeast_unique
#print axioms SargentStachurski.OperatorsFixedPoints.isGreatest_iUnion_iff
#print axioms SargentStachurski.OperatorsFixedPoints.not_exists_isGreatest_bounded
#print axioms SargentStachurski.OperatorsFixedPoints.isLUB_unique
#print axioms SargentStachurski.OperatorsFixedPoints.isGreatest_of_isLUB_mem
#print axioms SargentStachurski.OperatorsFixedPoints.IsGreatest.isLUB'
#print axioms SargentStachurski.OperatorsFixedPoints.IsLeast.isGLB'
#print axioms SargentStachurski.OperatorsFixedPoints.isLUB_iUnion
#print axioms SargentStachurski.OperatorsFixedPoints.isGLB_iInter
#print axioms SargentStachurski.OperatorsFixedPoints.not_exists_isLUB_Ioo
#print axioms SargentStachurski.OperatorsFixedPoints.isGLB_pair_pointwise
#print axioms SargentStachurski.OperatorsFixedPoints.isLUB_pair_pointwise
#print axioms SargentStachurski.OperatorsFixedPoints.IsSublattice
#print axioms SargentStachurski.OperatorsFixedPoints.isSublattice_nonneg
#print axioms SargentStachurski.OperatorsFixedPoints.isSublattice_pos
#print axioms SargentStachurski.OperatorsFixedPoints.isSublattice_abs_le_one
#print axioms SargentStachurski.OperatorsFixedPoints.sup'_apply_pointwise
#print axioms SargentStachurski.OperatorsFixedPoints.inf'_apply_pointwise
#print axioms SargentStachurski.OperatorsFixedPoints.isLUB_sup'_image
#print axioms SargentStachurski.OperatorsFixedPoints.isGLB_inf'_image
#print axioms SargentStachurski.OperatorsFixedPoints.IsSublattice.sup'_mem
#print axioms SargentStachurski.OperatorsFixedPoints.IsSublattice.inf'_mem
#print axioms SargentStachurski.OperatorsFixedPoints.isGreatest_of_sup'_mem
#print axioms SargentStachurski.OperatorsFixedPoints.not_exists_isGreatest_of_sup'_notMem
#print axioms SargentStachurski.OperatorsFixedPoints.Icc_inter_Icc_sublattice
#print axioms SargentStachurski.OperatorsFixedPoints.abs_add_le_pointwise
#print axioms SargentStachurski.OperatorsFixedPoints.inf_add_pointwise
#print axioms SargentStachurski.OperatorsFixedPoints.sup_add_pointwise
#print axioms SargentStachurski.OperatorsFixedPoints.sup_inf_pointwise
#print axioms SargentStachurski.OperatorsFixedPoints.inf_sup_pointwise
#print axioms SargentStachurski.OperatorsFixedPoints.abs_min_sub_min_le_abs'
#print axioms SargentStachurski.OperatorsFixedPoints.abs_inf_sub_inf_le_pointwise
#print axioms SargentStachurski.OperatorsFixedPoints.abs_sup_sub_sup_le_pointwise
#print axioms SargentStachurski.OperatorsFixedPoints.min_add_le_min_add_min
#print axioms SargentStachurski.OperatorsFixedPoints.inf_add_le_pointwise
#print axioms SargentStachurski.OperatorsFixedPoints.abs_min_sub_min_le_min
#print axioms SargentStachurski.OperatorsFixedPoints.abs_sup'_sub_sup'_le
#print axioms SargentStachurski.OperatorsFixedPoints.abs_inf'_sub_inf'_le
#print axioms SargentStachurski.OperatorsFixedPoints.upperEnvelope
#print axioms SargentStachurski.OperatorsFixedPoints.upperEnvelope_mapsTo
#print axioms SargentStachurski.OperatorsFixedPoints.isContractionOn_upperEnvelope
#print axioms SargentStachurski.OperatorsFixedPoints.monotone_affine_of_nonneg
#print axioms SargentStachurski.OperatorsFixedPoints.integral_mono_of_le
#print axioms SargentStachurski.OperatorsFixedPoints.isLUB_image_of_isGreatest
#print axioms SargentStachurski.OperatorsFixedPoints.isGLB_image_of_isLeast
#print axioms SargentStachurski.OperatorsFixedPoints.monotone_iterate
#print axioms SargentStachurski.OperatorsFixedPoints.monotone_mulVec_of_nonneg
#print axioms SargentStachurski.OperatorsFixedPoints.mul_le_mul_of_nonneg
#print axioms SargentStachurski.OperatorsFixedPoints.pow_nonneg_entries
#print axioms SargentStachurski.OperatorsFixedPoints.pow_le_pow_entries
#print axioms SargentStachurski.OperatorsFixedPoints.increasingFns
#print axioms SargentStachurski.OperatorsFixedPoints.monotone_two_mul
#print axioms SargentStachurski.OperatorsFixedPoints.monotone_indicator_ge
#print axioms SargentStachurski.OperatorsFixedPoints.not_monotone_neg
#print axioms SargentStachurski.OperatorsFixedPoints.not_monotone_indicator_le
#print axioms SargentStachurski.OperatorsFixedPoints.monotone_smul_add
#print axioms SargentStachurski.OperatorsFixedPoints.monotone_sup_inf
#print axioms SargentStachurski.OperatorsFixedPoints.isClosed_increasingFns
#print axioms SargentStachurski.OperatorsFixedPoints.monotone_expectation
#print axioms SargentStachurski.OperatorsFixedPoints.exists_indicator_decomposition
#print axioms SargentStachurski.OperatorsFixedPoints.isContractionOn_of_blackwell
#print axioms SargentStachurski.OperatorsFixedPoints.IsDistribution
#print axioms SargentStachurski.OperatorsFixedPoints.IsDistribution.mk
#print axioms SargentStachurski.OperatorsFixedPoints.IsDistribution.nonneg
#print axioms SargentStachurski.OperatorsFixedPoints.IsDistribution.sum_eq_one
#print axioms SargentStachurski.OperatorsFixedPoints.law
#print axioms SargentStachurski.OperatorsFixedPoints.law_isDistribution
#print axioms SargentStachurski.OperatorsFixedPoints.sum_mul_law
#print axioms SargentStachurski.OperatorsFixedPoints.FOSD
#print axioms SargentStachurski.OperatorsFixedPoints.fosd_law_of_le
#print axioms SargentStachurski.OperatorsFixedPoints.ccdf
#print axioms SargentStachurski.OperatorsFixedPoints.monotone_upper_indicator
#print axioms SargentStachurski.OperatorsFixedPoints.sum_upper_indicator_mul
#print axioms SargentStachurski.OperatorsFixedPoints.ccdf_le_of_fosd
#print axioms SargentStachurski.OperatorsFixedPoints.fosd_refl
#print axioms SargentStachurski.OperatorsFixedPoints.fosd_trans
#print axioms SargentStachurski.OperatorsFixedPoints.eq_of_ccdf_eq
#print axioms SargentStachurski.OperatorsFixedPoints.fosd_antisymm
#print axioms SargentStachurski.OperatorsFixedPoints.sum_mul_nonneg_of_tails_nonneg
#print axioms SargentStachurski.OperatorsFixedPoints.ccdf_sub
#print axioms SargentStachurski.OperatorsFixedPoints.ccdf_reindex
#print axioms SargentStachurski.OperatorsFixedPoints.fosd_of_ccdf_le
#print axioms SargentStachurski.OperatorsFixedPoints.cdf
#print axioms SargentStachurski.OperatorsFixedPoints.cdf_le_of_fosd
#print axioms SargentStachurski.OperatorsFixedPoints.quantileSet
#print axioms SargentStachurski.OperatorsFixedPoints.quantile
#print axioms SargentStachurski.OperatorsFixedPoints.quantile_le_of_fosd
#print axioms SargentStachurski.OperatorsFixedPoints.fosd_fin_two_iff
#print axioms SargentStachurski.OperatorsFixedPoints.affine_dominates
#print axioms SargentStachurski.OperatorsFixedPoints.iterate_le_iterate
#print axioms SargentStachurski.OperatorsFixedPoints.dominance_isPartialOrder
#print axioms SargentStachurski.OperatorsFixedPoints.fixedPt_le_of_dominates
#print axioms SargentStachurski.OperatorsFixedPoints.solowMap
#print axioms SargentStachurski.OperatorsFixedPoints.solowMap_monotone
#print axioms SargentStachurski.OperatorsFixedPoints.solowMap_le
#print axioms SargentStachurski.OperatorsFixedPoints.solow_fixedPt_le
#print axioms SargentStachurski.OperatorsFixedPoints.contMap
#print axioms SargentStachurski.OperatorsFixedPoints.contMap_monotone
#print axioms SargentStachurski.OperatorsFixedPoints.contMap_isContractionOn
#print axioms SargentStachurski.OperatorsFixedPoints.contMap_le
#print axioms SargentStachurski.OperatorsFixedPoints.contMap_fixedPt_le
#print axioms SargentStachurski.OperatorsFixedPoints.complexify
#print axioms SargentStachurski.OperatorsFixedPoints.complexify_apply
#print axioms SargentStachurski.OperatorsFixedPoints.complexify_pow
#print axioms SargentStachurski.OperatorsFixedPoints.complexify_transpose
#print axioms SargentStachurski.OperatorsFixedPoints.nnnorm_complexify
#print axioms SargentStachurski.OperatorsFixedPoints.norm_complexify
#print axioms SargentStachurski.OperatorsFixedPoints.specRad
#print axioms SargentStachurski.OperatorsFixedPoints.spectralRadius_complexify_ne_top
#print axioms SargentStachurski.OperatorsFixedPoints.specRad_nonneg
#print axioms SargentStachurski.OperatorsFixedPoints.mem_spectrum_iff_eigenpair
#print axioms SargentStachurski.OperatorsFixedPoints.tendsto_norm_pow_rpow
#print axioms SargentStachurski.OperatorsFixedPoints.eventually_norm_pow_le
#print axioms SargentStachurski.OperatorsFixedPoints.tendsto_norm_pow_zero
#print axioms SargentStachurski.OperatorsFixedPoints.summable_pow
#print axioms SargentStachurski.OperatorsFixedPoints.one_sub_mul_tsum
#print axioms SargentStachurski.OperatorsFixedPoints.tsum_mul_one_sub
#print axioms SargentStachurski.OperatorsFixedPoints.neumann_series
#print axioms SargentStachurski.OperatorsFixedPoints.specRad_transpose
#print axioms SargentStachurski.OperatorsFixedPoints.norm_le_norm_of_abs_le
#print axioms SargentStachurski.OperatorsFixedPoints.specRad_le_of_le
#print axioms SargentStachurski.OperatorsFixedPoints.rowsum_abs_le_norm
#print axioms SargentStachurski.OperatorsFixedPoints.norm_le_of_rowsum_abs_le
#print axioms SargentStachurski.OperatorsFixedPoints.abs_entry_le_norm
#print axioms SargentStachurski.OperatorsFixedPoints.norm_eq_of_rowsum_eq
#print axioms SargentStachurski.OperatorsFixedPoints.specRad_le_norm
#print axioms SargentStachurski.OperatorsFixedPoints.norm_le_specRad_of_mem_spectrum
#print axioms SargentStachurski.OperatorsFixedPoints.specRad_eq_of_rowsum_eq
#print axioms SargentStachurski.OperatorsFixedPoints.specRad_eq_of_colsum_eq
#print axioms SargentStachurski.OperatorsFixedPoints.eventually_abs_entry_pow_le
#print axioms SargentStachurski.OperatorsFixedPoints.mulVec_linear
#print axioms SargentStachurski.OperatorsFixedPoints.exists_matrix_of_linear
#print axioms SargentStachurski.OperatorsFixedPoints.matrixLinearEquiv
#print axioms SargentStachurski.OperatorsFixedPoints.matrixLinearEquiv_apply
#print axioms SargentStachurski.OperatorsFixedPoints.matrixFunEquiv
#print axioms SargentStachurski.OperatorsFixedPoints.kernelOp
#print axioms SargentStachurski.OperatorsFixedPoints.kernelOp_eq_mulVec
#print axioms SargentStachurski.OperatorsFixedPoints.kernelOp_linear
#print axioms SargentStachurski.OperatorsFixedPoints.productOp
#print axioms SargentStachurski.OperatorsFixedPoints.productOp_linear
#print axioms SargentStachurski.OperatorsFixedPoints.IsPositiveOp
#print axioms SargentStachurski.OperatorsFixedPoints.isPositiveOp_productOp
#print axioms SargentStachurski.OperatorsFixedPoints.isPositiveOp_mulVec_iff
#print axioms SargentStachurski.OperatorsFixedPoints.isPositiveOp_iff_monotone
#print axioms SargentStachurski.OperatorsFixedPoints.IsMarkovOp
#print axioms SargentStachurski.OperatorsFixedPoints.isMarkovOp_mulVec_iff
#print axioms SargentStachurski.OperatorsFixedPoints.mulVec_pos_of_markov
#print axioms SargentStachurski.OperatorsFixedPoints.vecMulOp
#print axioms SargentStachurski.OperatorsFixedPoints.vecMulOp_eq_vecMul
#print axioms SargentStachurski.OperatorsFixedPoints.isMarkovOp_iff_vecMulOp_distribution
#print axioms SargentStachurski.OperatorsFixedPoints.resPartial
#print axioms SargentStachurski.OperatorsFixedPoints.res
#print axioms SargentStachurski.OperatorsFixedPoints.res_apply
#print axioms SargentStachurski.OperatorsFixedPoints.smul_one_sub_mul_resPartial
#print axioms SargentStachurski.OperatorsFixedPoints.resPartial_mul_smul_one_sub
#print axioms SargentStachurski.OperatorsFixedPoints.resPartial_apply
#print axioms SargentStachurski.OperatorsFixedPoints.summable_res_entry
#print axioms SargentStachurski.OperatorsFixedPoints.tendsto_resPartial_apply
#print axioms SargentStachurski.OperatorsFixedPoints.tendsto_inv_pow_mul_apply
#print axioms SargentStachurski.OperatorsFixedPoints.smul_one_sub_mul_res
#print axioms SargentStachurski.OperatorsFixedPoints.res_mul_smul_one_sub
#print axioms SargentStachurski.OperatorsFixedPoints.res_nonneg
#print axioms SargentStachurski.OperatorsFixedPoints.inv_le_res_diag
#print axioms SargentStachurski.OperatorsFixedPoints.exists_mem_spectrum_norm_eq
#print axioms SargentStachurski.OperatorsFixedPoints.eventually_norm_entry_pow_complexify_le
#print axioms SargentStachurski.OperatorsFixedPoints.smul_one_sub_mul_res_real
#print axioms SargentStachurski.OperatorsFixedPoints.norm_res_complexify_le
#print axioms SargentStachurski.OperatorsFixedPoints.norm_le_card_mul_of_entry_norm_le
#print axioms SargentStachurski.OperatorsFixedPoints.notMem_spectrum_of_res_bounded
#print axioms SargentStachurski.OperatorsFixedPoints.exists_res_entry_gt
#print axioms SargentStachurski.OperatorsFixedPoints.isCompact_simplex
#print axioms SargentStachurski.OperatorsFixedPoints.perron_frobenius
#print axioms SargentStachurski.OperatorsFixedPoints.perron_frobenius_left
#print axioms SargentStachurski.OperatorsFixedPoints.le_specRad_of_colsum_ge
#print axioms SargentStachurski.OperatorsFixedPoints.specRad_le_of_colsum_le
#print axioms SargentStachurski.OperatorsFixedPoints.le_specRad_of_rowsum_ge
#print axioms SargentStachurski.OperatorsFixedPoints.specRad_le_of_rowsum_le
#print axioms SargentStachurski.OperatorsFixedPoints.tendsto_rpow_one_div_natCast
#print axioms SargentStachurski.OperatorsFixedPoints.norm_pow_mul_le_norm_mulVec
#print axioms SargentStachurski.OperatorsFixedPoints.tendsto_norm_pow_mulVec_rpow
#print axioms SargentStachurski.OperatorsFixedPoints.IsMarkov
#print axioms SargentStachurski.OperatorsFixedPoints.IsMarkov.mk
#print axioms SargentStachurski.OperatorsFixedPoints.IsMarkov.nonneg
#print axioms SargentStachurski.OperatorsFixedPoints.IsMarkov.rowsum
#print axioms SargentStachurski.OperatorsFixedPoints.IsMarkov.mul
#print axioms SargentStachurski.OperatorsFixedPoints.IsMarkov.pow
#print axioms SargentStachurski.OperatorsFixedPoints.IsMarkov.specRad_eq_one
#print axioms SargentStachurski.OperatorsFixedPoints.IsMarkov.exists_stationary
#print axioms SargentStachurski.OperatorsFixedPoints.IsMarkov.not_mulVec_ge_add
#print axioms SargentStachurski.OperatorsFixedPoints.LakeModel
#print axioms SargentStachurski.OperatorsFixedPoints.LakeModel.mk
#print axioms SargentStachurski.OperatorsFixedPoints.LakeModel.d
#print axioms SargentStachurski.OperatorsFixedPoints.LakeModel.b
#print axioms SargentStachurski.OperatorsFixedPoints.LakeModel.α
#print axioms SargentStachurski.OperatorsFixedPoints.LakeModel.lam
#print axioms SargentStachurski.OperatorsFixedPoints.LakeModel.d_pos
#print axioms SargentStachurski.OperatorsFixedPoints.LakeModel.d_lt_one
#print axioms SargentStachurski.OperatorsFixedPoints.LakeModel.b_pos
#print axioms SargentStachurski.OperatorsFixedPoints.LakeModel.b_lt_one
#print axioms SargentStachurski.OperatorsFixedPoints.LakeModel.α_pos
#print axioms SargentStachurski.OperatorsFixedPoints.LakeModel.α_lt_one
#print axioms SargentStachurski.OperatorsFixedPoints.LakeModel.lam_pos
#print axioms SargentStachurski.OperatorsFixedPoints.LakeModel.lam_lt_one
#print axioms SargentStachurski.OperatorsFixedPoints.LakeModel.A
#print axioms SargentStachurski.OperatorsFixedPoints.LakeModel.g
#print axioms SargentStachurski.OperatorsFixedPoints.LakeModel.one_sub_d_pos
#print axioms SargentStachurski.OperatorsFixedPoints.LakeModel.one_add_g_pos
#print axioms SargentStachurski.OperatorsFixedPoints.LakeModel.A_nonneg
#print axioms SargentStachurski.OperatorsFixedPoints.LakeModel.sum_mulVec
#print axioms SargentStachurski.OperatorsFixedPoints.LakeModel.colsum
#print axioms SargentStachurski.OperatorsFixedPoints.LakeModel.specRad_A
#print axioms SargentStachurski.OperatorsFixedPoints.LakeModel.one_vecMul
#print axioms SargentStachurski.OperatorsFixedPoints.LakeModel.ubar
#print axioms SargentStachurski.OperatorsFixedPoints.LakeModel.xbar
#print axioms SargentStachurski.OperatorsFixedPoints.LakeModel.numer_eq
#print axioms SargentStachurski.OperatorsFixedPoints.LakeModel.denom_pos
#print axioms SargentStachurski.OperatorsFixedPoints.LakeModel.xbar_sum
#print axioms SargentStachurski.OperatorsFixedPoints.LakeModel.A_mulVec_xbar
#print axioms SargentStachurski.OperatorsFixedPoints.LakeModel.eq_xbar_of_eigen
