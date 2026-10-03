/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Separation.Hausdorff

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
