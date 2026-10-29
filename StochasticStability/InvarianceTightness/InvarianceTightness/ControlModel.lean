/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InvarianceTightness.ModelRecursion
import Mathlib.Topology.Closure
import Mathlib.Topology.Constructions

/-!
# The deterministic control model CM(F) (MT §7.1.1, §7.2.1)

Meyn and Tweedie, §7.1.1, pp. 147–148, and §7.2.1, pp. 154–155.

The control model CM(F) associated with the recursion `Xₖ = F(Xₖ₋₁, Wₖ)` has trajectories
`xₖ = Fₖ(x₀, u₁, …, uₖ)` (`controlMap`, MT (2.5), (7.1), (7.9)), the controls ranging over a
control set `O ⊆ W`.

* `reachK F O k x = A₊ᵏ(x)` (MT (7.2), p. 147): the states reachable from `x` at time `k`;
  `reachK_zero` (`A₊⁰(x) = {x}`), `mem_reachK_succ` (one more step), `mem_reachK_succ'` (first
  step), `reachK_add` and `reachKSet_add` (the semigroup property
  `A₊^{k+j}(E) = A₊ᵏ(A₊ʲ(E))`, MT p. 154).
* `reach F O x = A₊(x)` (MT (7.3), (7.10)), `reachSet F O E = A₊(E)`, `noReach F O E = E⁰`
  (MT p. 154).
* `IsForwardAccessible F O` (MT p. 148, p. 152): `A₊(x)` has non-empty interior for every `x`.
* `IsCMInvariant F O E` (MT p. 154): `A₊(E) ⊆ E`; it is equivalent to one-step invariance
  (`isCMInvariant_iff_step`); unions, intersections and (for `F(·, u)` continuous) closures of
  invariant sets are invariant.
* `omegaSet F O C = Ω₊(C)` (MT (7.14)).
* **Proposition 7.2.1** (p. 155): `proposition_7_2_1_i` (`A₊(C)` and its closure are invariant),
  `proposition_7_2_1_ii` (`Ω₊(C)` is invariant), `proposition_7_2_1_iii` (`C⁰` is invariant, and
  closed when `C` is open).
* `IsKAccessible F O k B C`, `B →ᵏ C` (MT p. 157): `C ⊆ A₊ᵏ(y)` for every `y ∈ B`.
* `IsPeriodicOrbit F O G` (MT p. 158): disjoint closed sets `Gᵢ`, `i ∈ ZMod d`, with
  `A₊¹(Gᵢ) ⊆ Gᵢ₊₁`.

**Hypotheses.** The book takes `F` smooth; the topological statements here only use that each
`F(·, u)`, `u ∈ O`, is continuous (`controlMap_continuous`).
-/

namespace MeynTweedie.InvarianceTightness

open Set Topology

variable {X W : Type*}

/-! ### Reachable sets -/

/-- `A₊ᵏ(x)` (MT (7.2), p. 147): the states `Fₖ(x, u₁, …, uₖ)` with every control `uᵢ ∈ O`. -/
def reachK (F : X × W → X) (O : Set W) (k : ℕ) (x : X) : Set X :=
  {y | ∃ u : Fin k → W, (∀ i, u i ∈ O) ∧ controlMap F k x u = y}

/-- `A₊(x) = ⋃ₖ A₊ᵏ(x)` (MT (7.3), (7.10)): the states reachable from `x` at some time. -/
def reach (F : X × W → X) (O : Set W) (x : X) : Set X := ⋃ k, reachK F O k x

/-- `A₊ᵏ(E) = ⋃_{x ∈ E} A₊ᵏ(x)`. -/
def reachKSet (F : X × W → X) (O : Set W) (k : ℕ) (E : Set X) : Set X :=
  ⋃ x ∈ E, reachK F O k x

/-- `A₊(E) = ⋃_{x ∈ E} A₊(x)` (MT p. 154). -/
def reachSet (F : X × W → X) (O : Set W) (E : Set X) : Set X := ⋃ x ∈ E, reach F O x

/-- `E⁰ = {x : A₊(x) ∩ E = ∅}` (MT p. 154): the states that cannot reach `E`. -/
def noReach (F : X × W → X) (O : Set W) (E : Set X) : Set X := {x | Disjoint (reach F O x) E}

/-- `E` is **invariant** for CM(F) (MT p. 154): `A₊(E) ⊆ E`. -/
def IsCMInvariant (F : X × W → X) (O : Set W) (E : Set X) : Prop := reachSet F O E ⊆ E

/-- `A₊⁰(x) = {x}`. -/
@[simp] theorem reachK_zero (F : X × W → X) (O : Set W) (x : X) : reachK F O 0 x = {x} := by
  ext y
  simp only [reachK, controlMap_zero, mem_ofPred_eq, mem_singleton_iff]
  exact ⟨fun ⟨_, _, h⟩ => h.symm, fun h => ⟨Fin.elim0, fun i => i.elim0, h.symm⟩⟩

/-- One more step: `z ∈ A₊ᵏ⁺¹(x)` iff `z = F(y, w)` with `y ∈ A₊ᵏ(x)` and `w ∈ O`. -/
theorem mem_reachK_succ (F : X × W → X) (O : Set W) (k : ℕ) (x z : X) :
    z ∈ reachK F O (k + 1) x ↔ ∃ y ∈ reachK F O k x, ∃ w ∈ O, F (y, w) = z := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨_, ⟨Fin.init u, fun i => hu _, rfl⟩, u (Fin.last k), hu _, rfl⟩
  · rintro ⟨y, ⟨u, hu, rfl⟩, w, hw, rfl⟩
    refine ⟨Fin.snoc u w, fun i => ?_, ?_⟩
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hw
      · simpa using hu j
    · rw [controlMap_succ, Fin.init_snoc, Fin.snoc_last]

/-- The first step: `z ∈ A₊ᵏ⁺¹(x)` iff `z ∈ A₊ᵏ(F(x, w))` for some `w ∈ O`. -/
theorem mem_reachK_succ' (F : X × W → X) (O : Set W) (k : ℕ) (x z : X) :
    z ∈ reachK F O (k + 1) x ↔ ∃ w ∈ O, z ∈ reachK F O k (F (x, w)) := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u 0, hu 0, Fin.tail u, fun i => hu _, ?_⟩
    rw [← controlMap_succ_cons, Fin.cons_self_tail]
  · rintro ⟨w, hw, u, hu, rfl⟩
    refine ⟨Fin.cons w u, fun i => ?_, controlMap_succ_cons F k x w u⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hw
    · simpa using hu j

/-- `y ∈ A₊ᵏ(x)` and `w ∈ O` give `F(y, w) ∈ A₊ᵏ⁺¹(x)`. -/
theorem step_mem_reachK {F : X × W → X} {O : Set W} {k : ℕ} {x y : X} (hy : y ∈ reachK F O k x)
    {w : W} (hw : w ∈ O) : F (y, w) ∈ reachK F O (k + 1) x :=
  (mem_reachK_succ F O k x _).2 ⟨y, hy, w, hw, rfl⟩

/-- `x ∈ A₊⁰(x)`. -/
theorem self_mem_reachK_zero (F : X × W → X) (O : Set W) (x : X) : x ∈ reachK F O 0 x := by
  simp

/-- `x ∈ A₊(x)`. -/
theorem self_mem_reach (F : X × W → X) (O : Set W) (x : X) : x ∈ reach F O x :=
  mem_iUnion.2 ⟨0, self_mem_reachK_zero F O x⟩

/-- `y ∈ A₊(x)` iff `y ∈ A₊ᵏ(x)` for some `k`. -/
theorem mem_reach_iff {F : X × W → X} {O : Set W} {x y : X} :
    y ∈ reach F O x ↔ ∃ k, y ∈ reachK F O k x := mem_iUnion

/-- **The semigroup property** (MT p. 154): `A₊^{j+k}(x) = A₊ᵏ(A₊ʲ(x))`. -/
theorem reachK_add (F : X × W → X) (O : Set W) (j k : ℕ) (x : X) :
    reachK F O (j + k) x = reachKSet F O k (reachK F O j x) := by
  induction k with
  | zero =>
    ext y
    simp [reachKSet]
  | succ k ih =>
    ext z
    rw [← add_assoc, mem_reachK_succ, ih]
    simp only [reachKSet, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨y, ⟨x', hx', hy⟩, w, hw, rfl⟩
      exact ⟨x', hx', step_mem_reachK hy hw⟩
    · rintro ⟨x', hx', hz⟩
      obtain ⟨y, hy, w, hw, rfl⟩ := (mem_reachK_succ F O k x' z).1 hz
      exact ⟨y, ⟨x', hx', hy⟩, w, hw, rfl⟩

/-- **The semigroup property for sets** (MT p. 154): `A₊^{j+k}(E) = A₊ᵏ(A₊ʲ(E))`. -/
theorem reachKSet_add (F : X × W → X) (O : Set W) (j k : ℕ) (E : Set X) :
    reachKSet F O (j + k) E = reachKSet F O k (reachKSet F O j E) := by
  ext z
  simp only [reachKSet, mem_iUnion, exists_prop, reachK_add]
  constructor
  · rintro ⟨x, hx, y, hy, hz⟩
    exact ⟨y, ⟨x, hx, hy⟩, hz⟩
  · rintro ⟨y, ⟨x, hx, hy⟩, hz⟩
    exact ⟨x, hx, y, hy, hz⟩

/-- `y ∈ A₊ʲ(x)` and `z ∈ A₊ᵏ(y)` give `z ∈ A₊^{j+k}(x)`. -/
theorem reachK_trans {F : X × W → X} {O : Set W} {j k : ℕ} {x y z : X}
    (hy : y ∈ reachK F O j x) (hz : z ∈ reachK F O k y) : z ∈ reachK F O (j + k) x := by
  rw [reachK_add]
  exact mem_biUnion hy hz

/-- `y ∈ A₊(x)` and `z ∈ A₊(y)` give `z ∈ A₊(x)`. -/
theorem reach_trans {F : X × W → X} {O : Set W} {x y z : X} (hy : y ∈ reach F O x)
    (hz : z ∈ reach F O y) : z ∈ reach F O x := by
  obtain ⟨j, hj⟩ := mem_reach_iff.1 hy
  obtain ⟨k, hk⟩ := mem_reach_iff.1 hz
  exact mem_reach_iff.2 ⟨j + k, reachK_trans hj hk⟩

/-- If `O` is non-empty, `A₊ᵏ(x)` is non-empty. -/
theorem reachK_nonempty {F : X × W → X} {O : Set W} (hO : O.Nonempty) (k : ℕ) (x : X) :
    (reachK F O k x).Nonempty := by
  obtain ⟨w, hw⟩ := hO
  exact ⟨_, fun _ => w, fun _ => hw, rfl⟩

/-- `A₊ᵏ(x) ⊆ A₊(x)`. -/
theorem reachK_subset_reach (F : X × W → X) (O : Set W) (k : ℕ) (x : X) :
    reachK F O k x ⊆ reach F O x := subset_iUnion (fun k => reachK F O k x) k

/-! ### Invariant sets -/

/-- One-step invariance: `E` is invariant iff `F(x, w) ∈ E` for all `x ∈ E` and `w ∈ O`. -/
theorem isCMInvariant_iff_step {F : X × W → X} {O : Set W} {E : Set X} :
    IsCMInvariant F O E ↔ ∀ x ∈ E, ∀ w ∈ O, F (x, w) ∈ E := by
  constructor
  · intro h x hx w hw
    refine h (mem_biUnion hx (mem_reach_iff.2 ⟨1, ?_⟩))
    simpa using step_mem_reachK (self_mem_reachK_zero F O x) hw
  · intro h y hy
    obtain ⟨x, hx, hy⟩ := mem_iUnion₂.1 hy
    obtain ⟨k, hk⟩ := mem_reach_iff.1 hy
    have key : ∀ k, ∀ z ∈ reachK F O k x, z ∈ E := by
      intro k
      induction k with
      | zero =>
        intro z hz
        rw [reachK_zero, mem_singleton_iff] at hz
        exact hz ▸ hx
      | succ k ih =>
        intro z hz
        obtain ⟨y', hy', w, hw, rfl⟩ := (mem_reachK_succ F O k x z).1 hz
        exact h _ (ih y' hy') w hw
    exact key k y hk

/-- For an invariant `E`, `A₊ᵏ(x) ⊆ E` for every `x ∈ E`. -/
theorem IsCMInvariant.reachK_subset {F : X × W → X} {O : Set W} {E : Set X}
    (h : IsCMInvariant F O E) {x : X} (hx : x ∈ E) (k : ℕ) : reachK F O k x ⊆ E := fun _ hy =>
  h (mem_biUnion hx (reachK_subset_reach F O k x hy))

/-- For an invariant `E`, `A₊(x) ⊆ E` for every `x ∈ E`. -/
theorem IsCMInvariant.reach_subset {F : X × W → X} {O : Set W} {E : Set X}
    (h : IsCMInvariant F O E) {x : X} (hx : x ∈ E) : reach F O x ⊆ E := fun _ hy =>
  h (mem_biUnion hx hy)

/-- The empty set and the whole space are invariant. -/
theorem isCMInvariant_univ (F : X × W → X) (O : Set W) : IsCMInvariant F O univ :=
  subset_univ _

/-- Unions of invariant sets are invariant (MT p. 154). -/
theorem isCMInvariant_iUnion {ι : Sort*} {F : X × W → X} {O : Set W} {E : ι → Set X}
    (h : ∀ i, IsCMInvariant F O (E i)) : IsCMInvariant F O (⋃ i, E i) := by
  rw [isCMInvariant_iff_step]
  intro x hx w hw
  obtain ⟨i, hi⟩ := mem_iUnion.1 hx
  exact mem_iUnion.2 ⟨i, isCMInvariant_iff_step.1 (h i) x hi w hw⟩

/-- Intersections of invariant sets are invariant (MT p. 154). -/
theorem isCMInvariant_iInter {ι : Sort*} {F : X × W → X} {O : Set W} {E : ι → Set X}
    (h : ∀ i, IsCMInvariant F O (E i)) : IsCMInvariant F O (⋂ i, E i) := by
  rw [isCMInvariant_iff_step]
  intro x hx w hw
  exact mem_iInter.2 fun i => isCMInvariant_iff_step.1 (h i) x (mem_iInter.1 hx i) w hw

/-- `A₊(C)` is invariant. -/
theorem isCMInvariant_reachSet (F : X × W → X) (O : Set W) (C : Set X) :
    IsCMInvariant F O (reachSet F O C) := by
  intro z hz
  simp only [reachSet, mem_iUnion, exists_prop] at hz ⊢
  obtain ⟨y, ⟨x, hx, hy⟩, hz⟩ := hz
  exact ⟨x, hx, reach_trans hy hz⟩

/-- `A₊(x)` is invariant. -/
theorem isCMInvariant_reach (F : X × W → X) (O : Set W) (x : X) :
    IsCMInvariant F O (reach F O x) := by
  have := isCMInvariant_reachSet F O {x}
  simpa [reachSet] using this

/-- `C ⊆ A₊(C)`. -/
theorem subset_reachSet (F : X × W → X) (O : Set W) (C : Set X) : C ⊆ reachSet F O C :=
  fun x hx => mem_biUnion hx (self_mem_reach F O x)

/-- `A₊(C)` is the smallest invariant set containing `C`. -/
theorem reachSet_subset_of_isInvariant {F : X × W → X} {O : Set W} {C E : Set X}
    (hE : IsCMInvariant F O E) (hC : C ⊆ E) : reachSet F O C ⊆ E := fun _ hy => by
  obtain ⟨x, hx, hy⟩ := mem_iUnion₂.1 hy
  exact hE.reach_subset (hC hx) hy

/-- `A₊(A₊ᴺ(C)) = ⋃_{k ≥ N} A₊ᵏ(C)`. -/
theorem reachSet_reachKSet (F : X × W → X) (O : Set W) (N : ℕ) (C : Set X) :
    reachSet F O (reachKSet F O N C) = ⋃ k ≥ N, reachKSet F O k C := by
  ext z
  simp only [reachSet, reachKSet, reach, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨y, ⟨x, hx, hy⟩, k, hz⟩
    exact ⟨N + k, Nat.le_add_right N k, x, hx, reachK_trans hy hz⟩
  · rintro ⟨k, hk, x, hx, hz⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [reachK_add] at hz
    simp only [reachKSet, mem_iUnion, exists_prop] at hz
    obtain ⟨y, hy, hz⟩ := hz
    exact ⟨y, ⟨x, hx, hy⟩, j, hz⟩

variable [TopologicalSpace X]

/-- `Ω₊(C) = ⋂_{N ≥ 1} closure(⋃_{k ≥ N} A₊ᵏ(C))` (MT (7.14), p. 154). -/
def omegaSet (F : X × W → X) (O : Set W) (C : Set X) : Set X :=
  ⋂ N ≥ 1, closure (⋃ k ≥ N, reachKSet F O k C)

/-- CM(F) is **forward accessible** (MT p. 148 and p. 152): for every `x`, `A₊(x)` has non-empty
interior. -/
def IsForwardAccessible (F : X × W → X) (O : Set W) : Prop :=
  ∀ x, (interior (reach F O x)).Nonempty

/-- `Ω₊(C)` is closed. -/
theorem isClosed_omegaSet (F : X × W → X) (O : Set W) (C : Set X) :
    IsClosed (omegaSet F O C) :=
  isClosed_biInter fun _ _ => isClosed_closure

/-- If each `F(·, u)`, `u ∈ O`, is continuous, so is each `Fₖ(·, u)` with `u ∈ Oᵏ`. -/
theorem controlMap_continuous {F : X × W → X} {O : Set W}
    (hF : ∀ w ∈ O, Continuous fun x => F (x, w)) (k : ℕ) {u : Fin k → W} (hu : ∀ i, u i ∈ O) :
    Continuous fun x => controlMap F k x u := by
  induction k with
  | zero => exact continuous_id
  | succ k ih =>
    simp_rw [controlMap_succ]
    exact (hF _ (hu _)).comp (ih fun i => hu _)

/-- Closures of invariant sets are invariant when each `F(·, u)`, `u ∈ O`, is continuous
(MT p. 154). -/
theorem IsCMInvariant.closure {F : X × W → X} {O : Set W}
    (hF : ∀ w ∈ O, Continuous fun x => F (x, w)) {E : Set X} (hE : IsCMInvariant F O E) :
    IsCMInvariant F O (_root_.closure E) := by
  rw [isCMInvariant_iff_step] at hE ⊢
  intro x hx w hw
  exact map_mem_closure (f := fun x => F (x, w)) (hF w hw) hx fun y hy => hE y hy w hw

/-- **Proposition 7.2.1 (i)** (MT p. 155): `A₊(C)` and its closure are invariant. -/
theorem proposition_7_2_1_i {F : X × W → X} {O : Set W}
    (hF : ∀ w ∈ O, Continuous fun x => F (x, w)) (C : Set X) :
    IsCMInvariant F O (reachSet F O C) ∧ IsCMInvariant F O (_root_.closure (reachSet F O C)) :=
  ⟨isCMInvariant_reachSet F O C, (isCMInvariant_reachSet F O C).closure hF⟩

/-- **Proposition 7.2.1 (ii)** (MT p. 155): `Ω₊(C)` is invariant. -/
theorem proposition_7_2_1_ii {F : X × W → X} {O : Set W}
    (hF : ∀ w ∈ O, Continuous fun x => F (x, w)) (C : Set X) :
    IsCMInvariant F O (omegaSet F O C) := by
  refine isCMInvariant_iInter fun N => isCMInvariant_iInter fun _ => ?_
  rw [← reachSet_reachKSet]
  exact (isCMInvariant_reachSet F O _).closure hF

/-- The set of states from which `Fₖ(·, u) ∈ U` for some admissible `u` is open when `U` is. -/
theorem isOpen_setOf_reachK_inter {F : X × W → X} {O : Set W}
    (hF : ∀ w ∈ O, Continuous fun x => F (x, w)) (k : ℕ) {U : Set X} (hU : IsOpen U) :
    IsOpen {x | (reachK F O k x ∩ U).Nonempty} := by
  have : {x | (reachK F O k x ∩ U).Nonempty} =
      ⋃ u : {u : Fin k → W // ∀ i, u i ∈ O}, (fun x => controlMap F k x u.1) ⁻¹' U := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_preimage]
    constructor
    · rintro ⟨y, ⟨u, hu, rfl⟩, hy⟩
      exact ⟨⟨u, hu⟩, hy⟩
    · rintro ⟨⟨u, hu⟩, hy⟩
      exact ⟨_, ⟨u, hu, rfl⟩, hy⟩
  rw [this]
  exact isOpen_iUnion fun u => hU.preimage (controlMap_continuous hF k u.2)

/-- The set of states from which `A₊(x)` meets an open `U` is open. -/
theorem isOpen_setOf_reach_inter {F : X × W → X} {O : Set W}
    (hF : ∀ w ∈ O, Continuous fun x => F (x, w)) {U : Set X} (hU : IsOpen U) :
    IsOpen {x | (reach F O x ∩ U).Nonempty} := by
  have : {x | (reach F O x ∩ U).Nonempty} = ⋃ k, {x | (reachK F O k x ∩ U).Nonempty} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, reach, iUnion_inter, nonempty_iUnion]
  rw [this]
  exact isOpen_iUnion fun k => isOpen_setOf_reachK_inter hF k hU

/-- **Proposition 7.2.1 (iii)** (MT p. 155): `C⁰` is invariant, and closed if `C` is open. -/
theorem proposition_7_2_1_iii (F : X × W → X) (O : Set W) (C : Set X) :
    IsCMInvariant F O (noReach F O C) ∧
      ((∀ w ∈ O, Continuous fun x => F (x, w)) → IsOpen C → IsClosed (noReach F O C)) := by
  refine ⟨fun z hz => ?_, fun hF hC => ?_⟩
  · simp only [reachSet, mem_iUnion, exists_prop] at hz
    obtain ⟨x, hx, hz⟩ := hz
    exact Set.disjoint_left.2 fun y hy => Set.disjoint_left.1 hx (reach_trans hz hy)
  · have : noReach F O C = {x | (reach F O x ∩ C).Nonempty}ᶜ := by
      ext x
      simp [noReach, Set.not_nonempty_iff_eq_empty, Set.disjoint_iff_inter_eq_empty]
    rw [this]
    exact (isOpen_setOf_reach_inter hF hC).isClosed_compl

/-! ### `k`-accessibility and periodic orbits -/

omit [TopologicalSpace X] in
/-- `C` is **`k`-accessible** from `B`, `B →ᵏ C` (MT p. 157): `C ⊆ A₊ᵏ(y)` for every `y ∈ B`. -/
def IsKAccessible (F : X × W → X) (O : Set W) (k : ℕ) (B C : Set X) : Prop :=
  ∀ y ∈ B, C ⊆ reachK F O k y

variable (F : X × W → X) (O : Set W) (d : ℕ) in
/-- A **periodic orbit** of period `d` (MT p. 158): disjoint closed sets `G i`, `i ∈ ZMod d`, with
`A₊¹(Gᵢ) ⊆ Gᵢ₊₁`. -/
structure IsPeriodicOrbit (G : ZMod d → Set X) : Prop where
  /-- Each set of the orbit is closed. -/
  isClosed : ∀ i, IsClosed (G i)
  /-- The sets are disjoint. -/
  disjoint : ∀ i j, i ≠ j → Disjoint (G i) (G j)
  /-- One step moves `Gᵢ` into `Gᵢ₊₁`. -/
  step : ∀ i, ∀ x ∈ G i, ∀ w ∈ O, F (x, w) ∈ G (i + 1)

/-- On a periodic orbit, `A₊ⁿ(Gᵢ) ⊆ Gᵢ₊ₙ`. -/
theorem IsPeriodicOrbit.reachK_subset {F : X × W → X} {O : Set W} {d : ℕ} {G : ZMod d → Set X}
    (h : IsPeriodicOrbit F O d G) (n : ℕ) {i : ZMod d} {x : X} (hx : x ∈ G i) :
    reachK F O n x ⊆ G (i + n) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    intro z hz
    obtain ⟨y, hy, w, hw, rfl⟩ := (mem_reachK_succ F O n x z).1 hz
    have := h.step _ y (ih hy) w hw
    rwa [Nat.cast_succ, ← add_assoc]

end MeynTweedie.InvarianceTightness
