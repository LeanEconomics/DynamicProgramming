/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ContinuousTime.OrderFixedPoints

/-!
# Order stability

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §9.1.1 (pp. 292–294).
Restated from the `FiniteStates/AbstractDynamicProgramming` project (Chapter 9), on which
the optimality theory of continuous-time MDPs in Chapter 10 rests.

A self-map `S` of a partially ordered set with exactly one fixed point `v̄` is upward stable if
`v ≼ Sv` implies `v ≼ v̄`, downward stable if `Sv ≼ v` implies `v̄ ≼ v`, and order stable if both
hold. No topology is involved.

* Exercise 9.1.1: `Tv = r + Av` with `A ≥ 0` and `ρ(A) < 1` is order stable on `ℝ^X`.
* Lemma 9.1.1: an order-preserving globally stable self-map of `V ⊆ ℝ^X` is order stable on `V`.
* Lemma 9.1.2: `S` is order stable on `V` iff it is order stable on the order dual `Vᵒᵈ`.
-/

open Finset Matrix Filter Topology Function Set

namespace SargentStachurski.ContinuousTime

/-- `S` is order stable (p. 293): it has exactly one fixed point `v̄`, and it is upward stable
(`v ≼ Sv ⇒ v ≼ v̄`) and downward stable (`Sv ≼ v ⇒ v̄ ≼ v`). -/
def OrderStable {V : Type*} [PartialOrder V] (S : V → V) : Prop :=
  ∃ u, IsFixedPt S u ∧ (∀ w, IsFixedPt S w → w = u) ∧ (∀ v, v ≤ S v → v ≤ u) ∧
    ∀ v, S v ≤ v → u ≤ v

/-- Upward and downward stability around some fixed point already force it to be the only one. -/
theorem orderStable_of_up_down {V : Type*} [PartialOrder V] {S : V → V} {u : V}
    (hu : IsFixedPt S u) (hup : ∀ v, v ≤ S v → v ≤ u) (hdown : ∀ v, S v ≤ v → u ≤ v) :
    OrderStable S :=
  ⟨u, hu, fun w hw => le_antisymm (hup w hw.eq.ge) (hdown w hw.eq.le), hup, hdown⟩

/-- Lemma 9.1.1 (p. 293), on a whole space: an order-preserving globally stable map on an
order-closed space (such as `ℝ^X` or `ℝ^{X × A}`) is order stable. -/
theorem orderStable_of_globallyStable {W : Type*} [TopologicalSpace W] [PartialOrder W]
    [OrderClosedTopology W] {S : W → W} (hm : Monotone S) (hs : GloballyStable S) :
    OrderStable S := by
  obtain ⟨u, hu, -, hlim⟩ := hs
  refine orderStable_of_up_down hu (fun v hv => ?_) fun v hv => ?_
  · have hk : ∀ k, v ≤ S^[k] v := by
      intro k
      induction k with
      | zero => exact le_rfl
      | succ k ih =>
        rw [iterate_succ_apply']
        exact hv.trans (hm ih)
    exact ge_of_tendsto' (hlim v) hk
  · have hk : ∀ k, S^[k] v ≤ v := by
      intro k
      induction k with
      | zero => exact le_rfl
      | succ k ih =>
        rw [iterate_succ_apply']
        exact (hm ih).trans hv
    exact le_of_tendsto' (hlim v) hk

/-- **Lemma 9.1.1** (p. 293): if `T` is an order-preserving self-map of `V ⊆ ℝ^X` that is globally
stable on `V`, then `T` (restricted to `V`) is order stable on `V`. -/
theorem orderStable_restrict {X : Type*} {U : Set (X → ℝ)} {S : (X → ℝ) → (X → ℝ)}
    (hmaps : MapsTo S U U) (hm : MonotoneOn S U) (hs : GloballyStableOn S U) :
    OrderStable (hmaps.restrict S U U) := by
  obtain ⟨u, huU, hu, -, hlim⟩ := hs
  have hfix : IsFixedPt (hmaps.restrict S U U) ⟨u, huU⟩ := Subtype.ext hu.eq
  have hiter : ∀ (v : U) k, (S^[k] v) ∈ U := fun v k => hmaps.iterate k v.2
  refine orderStable_of_up_down hfix (fun v hv => ?_) fun v hv => ?_
  · have hv' : (v : X → ℝ) ≤ S v := hv
    have hk : ∀ k, (v : X → ℝ) ≤ S^[k] v := by
      intro k
      induction k with
      | zero => exact le_rfl
      | succ k ih =>
        rw [iterate_succ_apply']
        exact hv'.trans (hm v.2 (hiter v k) ih)
    change (v : X → ℝ) ≤ u
    intro x
    exact ge_of_tendsto' (tendsto_pi_nhds.1 (hlim v v.2) x) fun k => hk k x
  · have hv' : S v ≤ (v : X → ℝ) := hv
    have hk : ∀ k, S^[k] v ≤ (v : X → ℝ) := by
      intro k
      induction k with
      | zero => exact le_rfl
      | succ k ih =>
        rw [iterate_succ_apply']
        exact (hm (hiter v k) v.2 ih).trans hv'
    change u ≤ (v : X → ℝ)
    intro x
    exact le_of_tendsto' (tendsto_pi_nhds.1 (hlim v v.2) x) fun k => hk k x

/-- **Exercise 9.1.1** (p. 293): for `A ≥ 0` with `ρ(A) < 1`, `Tv = r + Av` is order stable on
`ℝ^X`. -/
theorem orderStable_affineOp {X : Type*} [Fintype X] [Nonempty X]
    {A : Matrix X X ℝ} (hA : ∀ x x', 0 ≤ A x x') (hρ : specRad A < 1) (r : X → ℝ) :
    OrderStable (affineOp A r) := by
  classical
  exact orderStable_of_globallyStable (fun _ _ huv => add_le_add (mulVec_le_mulVec_of_nonneg hA huv)
    le_rfl) (globallyStable_affineOp hρ r)

/-- **Lemma 9.1.2** (p. 294): `S` is order stable on `V` iff it is order stable on the order dual
`Vᵒᵈ`. -/
theorem orderStable_dual_iff {V : Type*} [PartialOrder V] (S : V → V) :
    OrderStable (OrderDual.toDual ∘ S ∘ OrderDual.ofDual : Vᵒᵈ → Vᵒᵈ) ↔ OrderStable S := by
  constructor
  · rintro ⟨u, hu, -, hup, hdown⟩
    exact orderStable_of_up_down (u := OrderDual.ofDual u) (congrArg OrderDual.ofDual hu.eq)
      (fun v hv => hdown (OrderDual.toDual v) hv) fun v hv => hup (OrderDual.toDual v) hv
  · rintro ⟨u, hu, -, hup, hdown⟩
    exact orderStable_of_up_down (u := OrderDual.toDual u) (congrArg OrderDual.toDual hu.eq)
      (fun v hv => hdown (OrderDual.ofDual v) hv) fun v hv => hup (OrderDual.ofDual v) hv

end SargentStachurski.ContinuousTime
