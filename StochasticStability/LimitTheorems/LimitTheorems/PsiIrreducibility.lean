/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.Communication

/-!
# φ-irreducibility (MT §4.2.1)

Meyn and Tweedie, §4.2.1, pp. 81–83. Throughout, `X` is an arbitrary measurable space: none of
the results needs a countably generated σ-algebra.

* `IsPhiIrreducible P φ` (p. 82): `φ(A) > 0` implies `L(x, A) > 0` for every `x`.
* `resolventHalf P = K_{a_{1/2}}` (4.9), with `resolventHalf_apply`:
  `K_{a_{1/2}}(x, A) = Σₙ Pⁿ(x, A) 2^{-(n+1)}`; `isMarkovKernel_resolventHalf`: it is a
  transition kernel; `resolventHalf_pos_iff`: `K_{a_{1/2}}(x, A) > 0` iff `Pⁿ(x, A) > 0` for
  some `n ≥ 0`; `resolventHalf_eq_zero_iff`, `resolventHalf_equiv` (p. 82): `K_{a_{1/2}}(x, ·)`
  is a probability measure equivalent to `I(x, ·) + U(x, ·)`.
* `hitProb_pos_of_compl` (the proof of Proposition 4.2.1): if `L(y, A) > 0` for every `y ∉ A`,
  then `L(x, A) > 0` for every `x`.
* **Proposition 4.2.1** (`proposition_4_2_1`, p. 82): φ-irreducibility is equivalent to each of
  (i) `U(x, A) > 0`, (ii) `Pⁿ(x, A) > 0` for some `n ≥ 1`, (iii) `K_{a_{1/2}}(x, A) > 0`,
  whenever `φ(A) > 0`.
* `IsPhiIrreducible.mono` (p. 82–83): a measure absolutely continuous with respect to an
  irreducibility measure (for instance a restriction, or an equivalent probability measure) is
  an irreducibility measure; `isPhiIrreducible_zero`: the zero measure is one for every chain.
* `isPhiIrreducible_dirac_of_leads` (p. 82): if every state leads to `x*`, the chain is
  `δ_{x*}`-irreducible; `isPhiIrreducible_dirac_iff`: this happens iff `L(x, {x*}) > 0` for all
  `x`.
* `isIrreducibleChain_iff_count` (p. 83): on a countable space, irreducibility in the sense of
  §4.1 is counting-measure irreducibility.

**Corrections.** None. The book's convention `x → x` (p. 78) does not give `L(x*, {x*}) > 0`
directly, but `isPhiIrreducible_dirac_of_leads` shows the claim of p. 82 holds as stated.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- **φ-irreducibility** (MT p. 82): whenever `φ(A) > 0`, `L(x, A) > 0` for every `x ∈ X`. -/
def IsPhiIrreducible (P : Kernel X X) [IsMarkovKernel P] (φ : Measure X) : Prop :=
  ∀ A, MeasurableSet A → 0 < φ A → ∀ x, 0 < hitProb P A x

/-! ### The resolvent `K_{a_{1/2}}` -/

/-- The kernel `K_{a_{1/2}} = Σₙ 2^{-(n+1)} Pⁿ` (4.9), MT p. 82: the resolvent `K_{a_ε}` of
(3.26) with `ε = 1/2`. -/
noncomputable abbrev resolventHalf (P : Kernel X X) : Kernel X X := resolvent P 2⁻¹

/-- (4.9): `K_{a_{1/2}}(x, A) = Σₙ Pⁿ(x, A) 2^{-(n+1)}`. -/
theorem resolventHalf_apply (P : Kernel X X) (x : X) {A : Set X} (hA : MeasurableSet A) :
    resolventHalf P x A = ∑' n, (P ^ n) x A * 2⁻¹ ^ (n + 1) := by
  rw [resolventHalf, resolvent, sampledKernel_apply P _ x hA]
  refine tsum_congr fun n => ?_
  rw [ENNReal.one_sub_inv_two, pow_succ, mul_comm, mul_comm (2⁻¹ ^ n)]

/-- `K_{a_{1/2}}` is a transition probability kernel. -/
theorem isMarkovKernel_resolventHalf (P : Kernel X X) [IsMarkovKernel P] :
    IsMarkovKernel (resolventHalf P) :=
  isMarkovKernel_resolvent P (ENNReal.inv_lt_one.2 ENNReal.one_lt_two)

/-- `K_{a_{1/2}}(x, A) > 0` iff `Pⁿ(x, A) > 0` for some `n ≥ 0`. -/
theorem resolventHalf_pos_iff (P : Kernel X X) (x : X) {A : Set X} (hA : MeasurableSet A) :
    0 < resolventHalf P x A ↔ ∃ n, 0 < (P ^ n) x A := by
  rw [resolventHalf_apply P x hA, pos_iff_ne_zero, Ne, ENNReal.tsum_eq_zero]
  push Not
  refine exists_congr fun n => ?_
  rw [mul_ne_zero_iff, pos_iff_ne_zero]
  exact and_iff_left (pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top))

/-- `K_{a_{1/2}}(x, A) = 0` iff `I(x, A) + U(x, A) = Σ_{n ≥ 0} Pⁿ(x, A) = 0` (MT p. 82). -/
theorem resolventHalf_eq_zero_iff (P : Kernel X X) (x : X) {A : Set X} (hA : MeasurableSet A) :
    resolventHalf P x A = 0 ↔ Measure.dirac x A + potKernel P x A = 0 := by
  have h1 := resolventHalf_pos_iff P x hA
  rw [← not_iff_not, ← ne_eq, ← ne_eq, ← pos_iff_ne_zero, ← pos_iff_ne_zero, h1,
    add_pos_iff, potKernel_pos_iff P hA x]
  constructor
  · rintro ⟨n, hn⟩
    rcases n with _ | n
    · left
      rwa [pow_zero_apply] at hn
    · exact Or.inr ⟨n, hn⟩
  · rintro (h | ⟨n, hn⟩)
    · exact ⟨0, by rwa [pow_zero_apply]⟩
    · exact ⟨n + 1, hn⟩

/-- MT p. 82: `K_{a_{1/2}}(x, ·)` is equivalent to `I(x, ·) + U(x, ·)`: they have the same null
sets. -/
theorem resolventHalf_equiv (P : Kernel X X) (x : X) :
    resolventHalf P x ≪ Measure.dirac x + potKernel P x ∧
      Measure.dirac x + potKernel P x ≪ resolventHalf P x := by
  constructor
  · refine Measure.AbsolutelyContinuous.mk fun A hA h => ?_
    rw [Measure.add_apply] at h
    exact (resolventHalf_eq_zero_iff P x hA).2 h
  · refine Measure.AbsolutelyContinuous.mk fun A hA h => ?_
    rw [Measure.add_apply]
    exact (resolventHalf_eq_zero_iff P x hA).1 h

/-! ### Proposition 4.2.1 -/

/-- The step in the proof of Proposition 4.2.1 (MT p. 82): if `L(y, A) > 0` for every `y ∉ A`,
then `L(x, A) > 0` for every `x`, by `L(x, A) = P(x, A) + ∫_{Aᶜ} P(x, dy) L(y, A)`. -/
theorem hitProb_pos_of_compl (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (h : ∀ y ∉ A, 0 < hitProb P A y) (x : X) : 0 < hitProb P A x := by
  rw [hitProb_first_step P hA x]
  by_cases hx : P x A = 0
  · have hc : P x Aᶜ = 1 := by rw [prob_compl_eq_one_sub hA, hx, tsub_zero]
    refine add_pos_iff.2 (Or.inr ?_)
    rw [setLIntegral_pos_iff (measurable_hitProb P hA)]
    have : Function.support (hitProb P A) ∩ Aᶜ = Aᶜ :=
      inter_eq_right.2 fun y hy => (h y hy).ne'
    rw [this, hc]
    exact one_pos
  · exact add_pos_iff.2 (Or.inl (pos_iff_ne_zero.2 hx))

/-- **Proposition 4.2.1** (MT p. 82). The chain is φ-irreducible iff, whenever `φ(A) > 0`,
for every `x`: (i) `U(x, A) > 0`; equivalently (ii) `Pⁿ(x, A) > 0` for some `n ≥ 1`;
equivalently (iii) `K_{a_{1/2}}(x, A) > 0`. -/
theorem proposition_4_2_1 (P : Kernel X X) [IsMarkovKernel P] (φ : Measure X) :
    (IsPhiIrreducible P φ ↔
      ∀ A, MeasurableSet A → 0 < φ A → ∀ x, 0 < potKernel P x A) ∧
    (IsPhiIrreducible P φ ↔
      ∀ A, MeasurableSet A → 0 < φ A → ∀ x, ∃ n, 0 < (P ^ (n + 1)) x A) ∧
    (IsPhiIrreducible P φ ↔
      ∀ A, MeasurableSet A → 0 < φ A → ∀ x, 0 < resolventHalf P x A) := by
  refine ⟨?_, ?_, ?_⟩
  · refine forall₄_congr fun A hA _ x => ?_
    rw [hitProb_pos_iff P hA, potKernel_pos_iff P hA]
  · exact forall₄_congr fun A hA _ x => hitProb_pos_iff P hA x
  · constructor
    · intro h A hA hφ x
      obtain ⟨n, hn⟩ := (hitProb_pos_iff P hA x).1 (h A hA hφ x)
      exact (resolventHalf_pos_iff P x hA).2 ⟨n + 1, hn⟩
    · intro h A hA hφ
      refine hitProb_pos_of_compl P hA fun y hy => ?_
      obtain ⟨n, hn⟩ := (resolventHalf_pos_iff P y hA).1 (h A hA hφ y)
      rcases n with _ | n
      · rw [pow_zero_apply, Measure.dirac_apply' _ hA, indicator_of_notMem hy] at hn
        exact absurd hn (lt_irrefl _)
      · exact (hitProb_pos_iff P hA y).2 ⟨n, hn⟩

/-! ### Elementary facts about irreducibility measures -/

/-- MT pp. 82–83: a measure absolutely continuous with respect to an irreducibility measure is an
irreducibility measure. In particular any restriction of an irreducibility measure, and any
measure equivalent to one, is an irreducibility measure. -/
theorem IsPhiIrreducible.mono {P : Kernel X X} [IsMarkovKernel P] {φ φ' : Measure X}
    (h : IsPhiIrreducible P φ) (hφ : φ' ≪ φ) : IsPhiIrreducible P φ' :=
  fun A hA hpos => h A hA (pos_iff_ne_zero.2 fun h0 => hpos.ne' (hφ h0))

/-- A restriction of an irreducibility measure is an irreducibility measure (MT p. 82). -/
theorem IsPhiIrreducible.restrict {P : Kernel X X} [IsMarkovKernel P] {φ : Measure X}
    (h : IsPhiIrreducible P φ) (B : Set X) : IsPhiIrreducible P (φ.restrict B) :=
  h.mono Measure.absolutelyContinuous_restrict

/-- Every chain is `0`-irreducible: the definition is vacuous for the zero measure. -/
theorem isPhiIrreducible_zero (P : Kernel X X) [IsMarkovKernel P] :
    IsPhiIrreducible P (0 : Measure X) :=
  fun A _ h => absurd h (by simp)

/-- `δ_{x*}`-irreducibility: the chain is `δ_{x*}`-irreducible iff `L(x, {x*}) > 0` for all
`x`. -/
theorem isPhiIrreducible_dirac_iff (P : Kernel X X) [IsMarkovKernel P] [MeasurableSingletonClass X]
    (xs : X) : IsPhiIrreducible P (Measure.dirac xs) ↔ ∀ x, 0 < hitProb P {xs} x := by
  constructor
  · intro h x
    exact h {xs} (measurableSet_singleton xs) (by simp) x
  · intro h A hA hpos x
    rw [Measure.dirac_apply' _ hA] at hpos
    have hxs : xs ∈ A := by
      by_contra hc
      rw [indicator_of_notMem hc] at hpos
      exact lt_irrefl _ hpos
    exact (h x).trans_le (measure_mono fun ω hω => by
      obtain ⟨n, hn, h'⟩ := (firstReturn_ne_top_iff {xs} ω).1 hω
      exact (firstReturn_ne_top_iff A ω).2 ⟨n, hn, (mem_singleton_iff.1 h') ▸ hxs⟩)

/-- MT p. 82: on a countable space, if `x → x*` for every state `x`, the chain is
`δ_{x*}`-irreducible. (For `x = x*` the convention `x* → x*` is not a return to `x*`; the
return follows from the other states, as in the proof of Proposition 4.2.1.) -/
theorem isPhiIrreducible_dirac_of_leads (P : Kernel X X) [IsMarkovKernel P]
    [MeasurableSingletonClass X] (xs : X) (h : ∀ x, Leads P x xs) :
    IsPhiIrreducible P (Measure.dirac xs) := by
  rw [isPhiIrreducible_dirac_iff]
  refine hitProb_pos_of_compl P (measurableSet_singleton xs) fun y hy => ?_
  exact (h y).resolve_left hy

/-- MT p. 83: on a countable space, irreducibility in the sense of §4.1 is
irreducibility with respect to counting measure. -/
theorem isIrreducibleChain_iff_count (P : Kernel X X) [IsMarkovKernel P]
    [MeasurableSingletonClass X] [Nonempty X] :
    IsIrreducibleChain P ↔ IsPhiIrreducible P Measure.count := by
  rw [isIrreducibleChain_iff]
  constructor
  · intro h A hA hpos x
    obtain ⟨y, hy⟩ : A.Nonempty := by
      by_contra hc
      rw [not_nonempty_iff_eq_empty.1 hc, measure_empty] at hpos
      exact lt_irrefl _ hpos
    have hy' : 0 < hitProb P {y} x := by
      have := isPhiIrreducible_dirac_of_leads P y fun z => (h z y).1
      exact this {y} (measurableSet_singleton y) (by simp) x
    exact hy'.trans_le (measure_mono fun ω hω => by
      obtain ⟨n, hn, h'⟩ := (firstReturn_ne_top_iff {y} ω).1 hω
      exact (firstReturn_ne_top_iff A ω).2 ⟨n, hn, (mem_singleton_iff.1 h') ▸ hy⟩)
  · intro h x y
    have hl : ∀ a b : X, Leads P a b := fun a b =>
      Or.inr (h {b} (measurableSet_singleton b) (by simp) a)
    exact ⟨hl x y, hl y x⟩

end MeynTweedie.LimitTheorems
