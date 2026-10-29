/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import VUniformErgodicity.HittingTimes
import VUniformErgodicity.CountableChains

/-!
# Communication, communicating classes and absorbing sets (MT §4.1.2)

Meyn and Tweedie, §4.1.2, pp. 77–80, together with the facts about reaching sets and about
absorbing sets that §4.2 uses on a general space.

**Reaching a set** (any measurable space).
* `hitProb_pos_iff`: `L(x, A) > 0` iff `Pⁿ(x, A) > 0` for some `n ≥ 1`; `pow_le_hitProb`:
  `Pⁿ(x, A) ≤ L(x, A)` for `n ≥ 1`; `potKernel_pos_iff`: the same for `U(x, A)`.
* `pow_add_pos_iff`: `P^{m+n}(x, A) > 0` iff `Pᵐ(x, {y : Pⁿ(y, A) > 0}) > 0`, the form of the
  Chapman–Kolmogorov equations used throughout the chapter.

**Absorbing sets** (MT p. 78 and p. 84): `IsAbsorbing P A` means `P(x, A) = 1` for `x ∈ A`.
`IsAbsorbing.pow_apply`: then `Pⁿ(x, A) = 1`, and `IsAbsorbing.hitProb_compl`: `L(x, Aᶜ) = 0`
for `x ∈ A`. `restrictKernel` is the kernel `P_A` restricted to the states of `A`, a Markov
kernel on `A` when `A` is absorbing (`isMarkovKernel_restrictKernel`), with
`P_Aⁿ(x, B) = Pⁿ(x, B)` (`restrictKernel_pow_apply`).

**Countable spaces** (measurable singletons).
* `Leads P x y` (`x → y`, p. 78): `x = y` or `L(x, {y}) > 0`; `leads_iff_exists_pow`: iff
  `Pⁿ(x, y) > 0` for some `n ≥ 0`; `pow_add_singleton_ge` (from (3.23)):
  `P^{n+m}(x, z) ≥ Pⁿ(x, y) Pᵐ(y, z)`.
* `Communicates P x y` (`x ↔ y`); **Proposition 4.1.1** (`proposition_4_1_1`, p. 78): `↔` is an
  equivalence relation, so the classes `commClass P x = C(x)` cover `X`, with `x ∈ C(x)`
  (`mem_commClass_self`, `iUnion_commClass`, `commClass_eq_or_disjoint`).
* `IsIrreducibleChain P` (p. 78): `C(x) = X` for some `x`; `isIrreducibleChain_iff`: all states
  communicate.
* `not_isAbsorbing_commClass_iff` (p. 78): `C(x)` is not absorbing iff `x → y` for some
  `y ∉ C(x)`.
* The decomposition (4.5), p. 78: `nonAbsorbingPart P = D` is the union of the classes that are
  not absorbing; `decomposition_4_5`: `X` is the union of the absorbing classes and `D`, and
  `decomposition_4_5_disjoint`: the pieces are disjoint.
* **Proposition 4.1.2** (`proposition_4_1_2`, p. 79): an absorbing communicating class `C`
  carries a transition kernel `P_C` with `P_C(x, y) = P(x, y)`, and the chain `Φ_C` with this
  kernel is irreducible.

**Corrections.** None. The heuristic of p. 79–80, that a chain started in `D` is either absorbed
or leaves every finite subset of `D`, is made rigorous only in Proposition 8.3.1 and is not
formalised here.
-/

namespace MeynTweedie.VUniformErgodicity

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Reaching a set -/

omit [MeasurableSpace X] in
/-- The event "the chain enters `A` at some time `n ≥ 1`" is the union of the events
`{Φₙ₊₁ ∈ A}`. -/
theorem firstReturn_ne_top_eq_iUnion (A : Set X) :
    {ω : ℕ → X | firstReturn A ω ≠ ⊤} = ⋃ n : ℕ, {ω | ω (n + 1) ∈ A} := by
  ext ω
  rw [mem_ofPred_eq, firstReturn_ne_top_iff, mem_iUnion]
  constructor
  · rintro ⟨n, hn, h⟩
    exact ⟨n - 1, by rwa [Nat.sub_add_cancel hn]⟩
  · rintro ⟨n, h⟩
    exact ⟨n + 1, by omega, h⟩

/-- `Pⁿ⁺¹(x, A) ≤ L(x, A)`: the chain is in `A` at time `n + 1` only if it enters `A`. -/
theorem pow_le_hitProb (P : Kernel X X) [IsMarkovKernel P] {A : Set X} (hA : MeasurableSet A)
    (n : ℕ) (x : X) : (P ^ (n + 1)) x A ≤ hitProb P A x := by
  rw [hitProb, firstReturn_ne_top_eq_iUnion, ← pathKernel_coord_mem P x _ hA]
  exact measure_mono (subset_iUnion (fun n => {ω : ℕ → X | ω (n + 1) ∈ A}) n)

/-- **`L(x, A) > 0` iff `Pⁿ(x, A) > 0` for some `n ≥ 1`** (MT p. 78 and p. 82). -/
theorem hitProb_pos_iff (P : Kernel X X) [IsMarkovKernel P] {A : Set X} (hA : MeasurableSet A)
    (x : X) : 0 < hitProb P A x ↔ ∃ n, 0 < (P ^ (n + 1)) x A := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have h0 : pathKernel P x (⋃ n : ℕ, {ω : ℕ → X | ω (n + 1) ∈ A}) = 0 :=
      measure_iUnion_null fun n => by
        rw [pathKernel_coord_mem P x _ hA]
        exact nonpos_iff_eq_zero.1 (hc n)
    rw [hitProb, firstReturn_ne_top_eq_iUnion, h0] at h
    exact lt_irrefl _ h
  · rintro ⟨n, hn⟩
    exact hn.trans_le (pow_le_hitProb P hA n x)

/-- `L(x, A) ≤ 1`. -/
theorem hitProb_le_one (P : Kernel X X) [IsMarkovKernel P] (A : Set X) (x : X) :
    hitProb P A x ≤ 1 := by
  have := isMarkovKernel_pathKernel P
  exact prob_le_one

/-- `U(x, A) > 0` iff `Pⁿ(x, A) > 0` for some `n ≥ 1`. -/
theorem potKernel_pos_iff (P : Kernel X X) {A : Set X} (hA : MeasurableSet A) (x : X) :
    0 < potKernel P x A ↔ ∃ n, 0 < (P ^ (n + 1)) x A := by
  rw [potKernel_apply P x hA, pos_iff_ne_zero, Ne, ENNReal.tsum_eq_zero]
  push Not
  simp_rw [pos_iff_ne_zero]

/-- **Chapman–Kolmogorov, positivity form**: `P^{m+n}(x, A) > 0` iff
`Pᵐ(x, {y : Pⁿ(y, A) > 0}) > 0`. -/
theorem pow_add_pos_iff (P : Kernel X X) (m n : ℕ) (x : X) {A : Set X} (hA : MeasurableSet A) :
    0 < (P ^ (m + n)) x A ↔ 0 < (P ^ m) x {y | 0 < (P ^ n) y A} := by
  rw [Kernel.pow_add_apply_eq_lintegral P m n x hA,
    lintegral_pos_iff_support (Kernel.measurable_coe _ hA)]
  have : Function.support (fun y => (P ^ n) y A) = {y | 0 < (P ^ n) y A} := by
    ext y
    simp [Function.mem_support, pos_iff_ne_zero]
  rw [this]

/-- The set `{y : Pⁿ(y, A) > 0}` is measurable. -/
theorem measurableSet_pow_pos (P : Kernel X X) (n : ℕ) {A : Set X} (hA : MeasurableSet A) :
    MeasurableSet {y | 0 < (P ^ n) y A} :=
  measurableSet_lt measurable_const (Kernel.measurable_coe _ hA)

/-! ### Absorbing sets -/

/-- A set `A` is *absorbing* if `P(x, A) = 1` for every `x ∈ A` (MT p. 78 and p. 84). -/
def IsAbsorbing (P : Kernel X X) (A : Set X) : Prop := ∀ x ∈ A, P x A = 1

/-- From a point of an absorbing set the chain stays in it: `Pⁿ(x, A) = 1` for `x ∈ A`. -/
theorem IsAbsorbing.pow_apply {P : Kernel X X} [IsMarkovKernel P] {A : Set X}
    (hAbs : IsAbsorbing P A) (hA : MeasurableSet A) (n : ℕ) {x : X} (hx : x ∈ A) :
    (P ^ n) x A = 1 := by
  induction n with
  | zero => rw [pow_zero_apply, Measure.dirac_apply' _ hA, indicator_of_mem hx, Pi.one_apply]
  | succ n ih =>
    have := isMarkovKernel_pow P (n + 1)
    refine le_antisymm prob_le_one ?_
    calc (1 : ℝ≥0∞) = ∫⁻ _ in A, 1 ∂(P ^ n) x := by rw [setLIntegral_const, one_mul, ih]
      _ = ∫⁻ y in A, P y A ∂(P ^ n) x :=
          setLIntegral_congr_fun hA fun y hy => (hAbs y hy).symm
      _ ≤ ∫⁻ y, P y A ∂(P ^ n) x := setLIntegral_le_lintegral _ _
      _ = (P ^ (n + 1)) x A := (pow_succ_apply' P n x hA).symm

/-- From a point of an absorbing set, `Pⁿ(x, Aᶜ) = 0`. -/
theorem IsAbsorbing.pow_compl {P : Kernel X X} [IsMarkovKernel P] {A : Set X}
    (hAbs : IsAbsorbing P A) (hA : MeasurableSet A) (n : ℕ) {x : X} (hx : x ∈ A) :
    (P ^ n) x Aᶜ = 0 := by
  have := isMarkovKernel_pow P n
  rw [prob_compl_eq_zero_iff hA]
  exact hAbs.pow_apply hA n hx

/-- From a point of an absorbing set, the chain never leaves it: `L(x, Aᶜ) = 0`. -/
theorem IsAbsorbing.hitProb_compl {P : Kernel X X} [IsMarkovKernel P] {A : Set X}
    (hAbs : IsAbsorbing P A) (hA : MeasurableSet A) {x : X} (hx : x ∈ A) :
    hitProb P Aᶜ x = 0 := by
  by_contra h
  obtain ⟨n, hn⟩ := (hitProb_pos_iff P hA.compl x).1 (pos_iff_ne_zero.2 h)
  rw [hAbs.pow_compl hA (n + 1) hx] at hn
  exact lt_irrefl _ hn

/-- From a point of an absorbing set `A`, no set disjoint from `A` is reached. -/
theorem IsAbsorbing.hitProb_eq_zero {P : Kernel X X} [IsMarkovKernel P] {A B : Set X}
    (hAbs : IsAbsorbing P A) (hA : MeasurableSet A) (hB : Disjoint A B) {x : X} (hx : x ∈ A) :
    hitProb P B x = 0 := by
  refine nonpos_iff_eq_zero.1 ?_
  rw [← hAbs.hitProb_compl hA hx]
  exact measure_mono fun ω hω => by
    obtain ⟨n, hn, h⟩ := (firstReturn_ne_top_iff B ω).1 hω
    exact (firstReturn_ne_top_iff Aᶜ ω).2 ⟨n, hn, fun h' => hB.ne_of_mem h' h rfl⟩

/-! ### The kernel restricted to an absorbing set -/

/-- The kernel `P_A` restricted to the states in `A` (MT p. 79 and p. 85):
`P_A(x, B) = P(x, B)` for `x ∈ A` and `B ⊆ A`. -/
noncomputable def restrictKernel (P : Kernel X X) {A : Set X} (hA : MeasurableSet A) :
    Kernel A A :=
  (P.comap Subtype.val measurable_subtype_coe).comapRight (MeasurableEmbedding.subtype_coe hA)

/-- `P_A(x, B) = P(x, B)`. -/
theorem restrictKernel_apply (P : Kernel X X) {A : Set X} (hA : MeasurableSet A) (x : A)
    {B : Set A} (hB : MeasurableSet B) : restrictKernel P hA x B = P x (Subtype.val '' B) := by
  rw [restrictKernel, Kernel.comapRight_apply' _ _ _ hB, Kernel.comap_apply]

/-- `P_A(x, ·)` is `P(x, ·)` pulled back to `A`. -/
theorem restrictKernel_apply_eq (P : Kernel X X) {A : Set X} (hA : MeasurableSet A) (x : A) :
    restrictKernel P hA x = (P x).comap Subtype.val := by
  rw [restrictKernel, Kernel.comapRight_apply, Kernel.comap_apply]

/-- `P_A` is a transition probability kernel on `A` when `A` is absorbing (MT p. 79, p. 85). -/
theorem isMarkovKernel_restrictKernel (P : Kernel X X) {A : Set X} (hA : MeasurableSet A)
    (hAbs : IsAbsorbing P A) : IsMarkovKernel (restrictKernel P hA) :=
  Kernel.IsMarkovKernel.comapRight _ _ fun x => by
    rw [Kernel.comap_apply, Subtype.range_coe]
    exact hAbs x x.2

/-- Integrals against `P_A(x, ·)` are integrals against `P(x, ·)` when `A` is absorbing. -/
theorem lintegral_restrictKernel (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (hAbs : IsAbsorbing P A) (x : A) {g : X → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y, g y ∂restrictKernel P hA x = ∫⁻ y, g y ∂P x := by
  rw [restrictKernel_apply_eq, ← lintegral_map hg measurable_subtype_coe,
    map_comap_subtype_coe hA, Measure.restrict_eq_self_of_ae_mem]
  rw [ae_iff]
  have : {a | ¬ a ∈ A} = Aᶜ := rfl
  rw [this, prob_compl_eq_zero_iff hA]
  exact hAbs x x.2

/-- The `n`-step kernel of `P_A` is `Pⁿ` restricted to `A`: `P_Aⁿ(x, B) = Pⁿ(x, B)`. -/
theorem restrictKernel_pow_apply (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (hAbs : IsAbsorbing P A) (n : ℕ) (x : A) {B : Set A}
    (hB : MeasurableSet B) : (restrictKernel P hA ^ n) x B = (P ^ n) x (Subtype.val '' B) := by
  have hB' : MeasurableSet (Subtype.val '' B) :=
    (MeasurableEmbedding.subtype_coe hA).measurableSet_image.2 hB
  induction n generalizing x with
  | zero =>
    rw [pow_zero_apply, pow_zero_apply, Measure.dirac_apply' _ hB, Measure.dirac_apply' _ hB']
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx, indicator_of_mem (mem_image_of_mem _ hx)]
      rfl
    · rw [indicator_of_notMem hx, indicator_of_notMem]
      rintro ⟨y, hy, hyx⟩
      exact hx (Subtype.ext hyx ▸ hy)
  | succ n ih =>
    rw [pow_succ_apply _ n x hB, pow_succ_apply _ n _ hB']
    simp_rw [ih]
    exact lintegral_restrictKernel P hA hAbs x (g := fun y => (P ^ n) y (Subtype.val '' B))
      (Kernel.measurable_coe _ hB')

/-! ### Communication on a countable space -/

variable [MeasurableSingletonClass X]

/-- `x` *leads to* `y`, `x → y` (MT p. 78): `L(x, y) > 0`, with the convention `x → x`. -/
def Leads (P : Kernel X X) [IsMarkovKernel P] (x y : X) : Prop :=
  x = y ∨ 0 < hitProb P {y} x

/-- `x → y` iff `Pⁿ(x, y) > 0` for some `n ≥ 0` (MT p. 78). -/
theorem leads_iff_exists_pow (P : Kernel X X) [IsMarkovKernel P] (x y : X) :
    Leads P x y ↔ ∃ n, 0 < (P ^ n) x {y} := by
  rw [Leads, hitProb_pos_iff P (measurableSet_singleton y)]
  constructor
  · rintro (rfl | ⟨n, hn⟩)
    · exact ⟨0, by rw [pow_zero_apply, Measure.dirac_apply_of_mem (mem_singleton x)]; exact one_pos⟩
    · exact ⟨n + 1, hn⟩
  · rintro ⟨n, hn⟩
    rcases n with _ | n
    · left
      rw [pow_zero_apply, Measure.dirac_apply' _ (measurableSet_singleton y)] at hn
      by_contra hxy
      rw [indicator_of_notMem (by simpa using hxy)] at hn
      exact lt_irrefl _ hn
    · exact Or.inr ⟨n, hn⟩

/-- (3.23), MT p. 78: `P^{n+m}(x, z) ≥ Pⁿ(x, y) Pᵐ(y, z)`. -/
theorem pow_add_singleton_ge (P : Kernel X X) (n m : ℕ) (x y z : X) :
    (P ^ n) x {y} * (P ^ m) y {z} ≤ (P ^ (n + m)) x {z} := by
  rw [Kernel.pow_add_apply_eq_lintegral P n m x (measurableSet_singleton z), mul_comm]
  calc (P ^ m) y {z} * (P ^ n) x {y} = ∫⁻ b in {y}, (P ^ m) b {z} ∂(P ^ n) x :=
        (lintegral_singleton (fun b => (P ^ m) b {z}) y).symm
    _ ≤ _ := setLIntegral_le_lintegral _ _

/-- `→` is transitive (MT p. 78). -/
theorem Leads.trans {P : Kernel X X} [IsMarkovKernel P] {x y z : X} (hxy : Leads P x y)
    (hyz : Leads P y z) : Leads P x z := by
  rw [leads_iff_exists_pow] at hxy hyz ⊢
  obtain ⟨n, hn⟩ := hxy
  obtain ⟨m, hm⟩ := hyz
  exact ⟨n + m, (ENNReal.mul_pos hn.ne' hm.ne').trans_le (pow_add_singleton_ge P n m x y z)⟩

omit [MeasurableSingletonClass X] in
/-- `x → x`. -/
theorem Leads.refl (P : Kernel X X) [IsMarkovKernel P] (x : X) : Leads P x x := Or.inl rfl

/-- `x` and `y` *communicate*, `x ↔ y` (MT p. 78): `x → y` and `y → x`. -/
def Communicates (P : Kernel X X) [IsMarkovKernel P] (x y : X) : Prop :=
  Leads P x y ∧ Leads P y x

/-- **Proposition 4.1.1** (MT p. 78): `↔` is an equivalence relation. -/
theorem proposition_4_1_1 (P : Kernel X X) [IsMarkovKernel P] : Equivalence (Communicates P) :=
  ⟨fun x => ⟨Leads.refl P x, Leads.refl P x⟩, fun h => ⟨h.2, h.1⟩,
    fun h1 h2 => ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩⟩

/-- The communicating class `C(x) = {y : x ↔ y}` (MT p. 78). -/
def commClass (P : Kernel X X) [IsMarkovKernel P] (x : X) : Set X := {y | Communicates P x y}

/-- `x ∈ C(x)`. -/
theorem mem_commClass_self (P : Kernel X X) [IsMarkovKernel P] (x : X) : x ∈ commClass P x :=
  (proposition_4_1_1 P).refl x

/-- The communicating classes cover `X` (Proposition 4.1.1). -/
theorem iUnion_commClass (P : Kernel X X) [IsMarkovKernel P] :
    ⋃ x, commClass P x = univ :=
  eq_univ_of_forall fun x => mem_iUnion.2 ⟨x, mem_commClass_self P x⟩

/-- Two communicating classes are equal or disjoint (Proposition 4.1.1). -/
theorem commClass_eq_or_disjoint (P : Kernel X X) [IsMarkovKernel P] (x y : X) :
    commClass P x = commClass P y ∨ Disjoint (commClass P x) (commClass P y) := by
  have he := proposition_4_1_1 P
  by_cases h : Communicates P x y
  · left
    ext z
    exact ⟨fun hz => he.trans (he.symm h) hz, fun hz => he.trans h hz⟩
  · right
    exact Set.disjoint_left.2 fun z hx hy => h (he.trans hx (he.symm hy))

/-- `y ∈ C(x)` iff `C(x) = C(y)`. -/
theorem commClass_eq_iff (P : Kernel X X) [IsMarkovKernel P] (x y : X) :
    commClass P x = commClass P y ↔ y ∈ commClass P x := by
  have he := proposition_4_1_1 P
  constructor
  · intro h
    rw [h]
    exact mem_commClass_self P y
  · intro h
    ext z
    exact ⟨fun hz => he.trans (he.symm h) hz, fun hz => he.trans h hz⟩

/-- An *irreducible* chain on a countable space (MT p. 78): `C(x) = X` for some `x`. -/
def IsIrreducibleChain (P : Kernel X X) [IsMarkovKernel P] : Prop := ∃ x, commClass P x = univ

/-- A chain is irreducible iff all states communicate. -/
theorem isIrreducibleChain_iff (P : Kernel X X) [IsMarkovKernel P] [Nonempty X] :
    IsIrreducibleChain P ↔ ∀ x y, Communicates P x y := by
  have he := proposition_4_1_1 P
  constructor
  · rintro ⟨x₀, hx₀⟩ x y
    have hx : x ∈ commClass P x₀ := hx₀ ▸ mem_univ x
    have hy : y ∈ commClass P x₀ := hx₀ ▸ mem_univ y
    exact he.trans (he.symm hx) hy
  · intro h
    obtain ⟨x₀⟩ := ‹Nonempty X›
    exact ⟨x₀, eq_univ_of_forall fun y => h x₀ y⟩

/-- The set `D` of states whose communicating class is not absorbing (MT (4.5), p. 78). -/
def nonAbsorbingPart (P : Kernel X X) [IsMarkovKernel P] : Set X :=
  {x | ¬ IsAbsorbing P (commClass P x)}

/-- `D` is a union of communicating classes: with `x`, it contains all of `C(x)`. -/
theorem commClass_subset_nonAbsorbingPart (P : Kernel X X) [IsMarkovKernel P] {x : X}
    (hx : x ∈ nonAbsorbingPart P) : commClass P x ⊆ nonAbsorbingPart P := fun y hy => by
  change ¬ IsAbsorbing P (commClass P y)
  rwa [← (commClass_eq_iff P x y).2 hy]

/-- **The decomposition (4.5)** (MT p. 78): `X = ⋃_{C(x) absorbing} C(x) ∪ D`. -/
theorem decomposition_4_5 (P : Kernel X X) [IsMarkovKernel P] :
    (⋃ x ∈ {x | IsAbsorbing P (commClass P x)}, commClass P x) ∪ nonAbsorbingPart P = univ := by
  refine eq_univ_of_forall fun y => ?_
  by_cases hy : IsAbsorbing P (commClass P y)
  · exact Or.inl (mem_biUnion hy (mem_commClass_self P y))
  · exact Or.inr hy

/-- The pieces of (4.5) are disjoint: distinct absorbing classes are disjoint, and every
absorbing class is disjoint from `D`. -/
theorem decomposition_4_5_disjoint (P : Kernel X X) [IsMarkovKernel P] :
    (∀ x y, commClass P x ≠ commClass P y → Disjoint (commClass P x) (commClass P y)) ∧
      Disjoint (⋃ x ∈ {x | IsAbsorbing P (commClass P x)}, commClass P x)
        (nonAbsorbingPart P) := by
  refine ⟨fun x y h => (commClass_eq_or_disjoint P x y).resolve_left h, ?_⟩
  refine Set.disjoint_left.2 fun z hz hD => ?_
  obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.1 hz
  exact hD (by rwa [← (commClass_eq_iff P x z).2 hzx])

variable [Countable X]

omit [MeasurableSpace X] [MeasurableSingletonClass X] in
/-- On a countable space with measurable singletons every set is measurable. -/
theorem measurableSet_of_countable [MeasurableSpace X] [MeasurableSingletonClass X]
    (A : Set X) : MeasurableSet A :=
  (Set.to_countable A).measurableSet

omit [MeasurableSingletonClass X] in
/-- A positive mass on a countable set sits on one of its points. -/
theorem exists_singleton_pos_of_pos (μ : Measure X) {A : Set X} (h : 0 < μ A) :
    ∃ y ∈ A, 0 < μ {y} := by
  by_contra hc
  push Not at hc
  have : μ (⋃ y ∈ A, {y}) = 0 :=
    (measure_biUnion_null_iff (Set.to_countable A)).2 fun y hy => nonpos_iff_eq_zero.1 (hc y hy)
  rw [biUnion_of_singleton] at this
  exact lt_irrefl _ (this ▸ h)

/-- MT p. 78: `C(x)` is not absorbing iff `x → y` for some state `y ∉ C(x)`. -/
theorem not_isAbsorbing_commClass_iff (P : Kernel X X) [IsMarkovKernel P] (x : X) :
    ¬ IsAbsorbing P (commClass P x) ↔ ∃ y ∉ commClass P x, Leads P x y := by
  have hC := measurableSet_of_countable (commClass P x)
  constructor
  · intro h
    simp only [IsAbsorbing, not_forall] at h
    obtain ⟨z, hz, hz1⟩ := h
    have hpos : 0 < P z (commClass P x)ᶜ := by
      rw [pos_iff_ne_zero, Ne, prob_compl_eq_zero_iff hC]
      exact hz1
    obtain ⟨y, hy, hzy⟩ := exists_singleton_pos_of_pos (P z) hpos
    refine ⟨y, hy, hz.1.trans ((leads_iff_exists_pow P z y).2 ⟨1, by rwa [pow_one]⟩)⟩
  · rintro ⟨y, hy, hxy⟩ hAbs
    obtain ⟨n, hn⟩ := (leads_iff_exists_pow P x y).1 hxy
    have h0 := hAbs.pow_compl hC n (mem_commClass_self P x)
    have : (P ^ n) x {y} ≤ (P ^ n) x (commClass P x)ᶜ :=
      measure_mono (singleton_subset_iff.2 hy)
    rw [h0] at this
    exact lt_irrefl _ (hn.trans_le this)

/-- **Proposition 4.1.2** (MT p. 79). If `C = C(x)` is an absorbing communicating class, the
matrix `P_C` (`P` restricted to the states of `C`) is a transition matrix, `P_C(y, z) = P(y, z)`,
and the chain `Φ_C` it defines on `C` is irreducible. -/
theorem proposition_4_1_2 (P : Kernel X X) [IsMarkovKernel P] (x : X)
    (hAbs : IsAbsorbing P (commClass P x)) :
    ∃ _ : IsMarkovKernel (restrictKernel P (measurableSet_of_countable (commClass P x))),
      (∀ y z : commClass P x,
        restrictKernel P (measurableSet_of_countable (commClass P x)) y {z} = P y {(z : X)}) ∧
      IsIrreducibleChain (restrictKernel P (measurableSet_of_countable (commClass P x))) := by
  set C := commClass P x with hCdef
  have hC := measurableSet_of_countable C
  have hM := isMarkovKernel_restrictKernel P hC hAbs
  refine ⟨hM, fun y z => ?_, ?_⟩
  · rw [restrictKernel_apply P hC y (measurableSet_singleton z), image_singleton]
  · have he := proposition_4_1_1 P
    have hlead : ∀ y z : C, Leads (restrictKernel P hC) y z := fun y z => by
      have hyz : Leads P y z := (he.trans (he.symm y.2) z.2).1
      obtain ⟨n, hn⟩ := (leads_iff_exists_pow P y z).1 hyz
      refine (leads_iff_exists_pow _ y z).2 ⟨n, ?_⟩
      rw [restrictKernel_pow_apply P hC hAbs n y (measurableSet_singleton z), image_singleton]
      exact hn
    exact ⟨⟨x, mem_commClass_self P x⟩, eq_univ_of_forall fun z =>
      ⟨hlead _ z, hlead z _⟩⟩

end MeynTweedie.VUniformErgodicity
