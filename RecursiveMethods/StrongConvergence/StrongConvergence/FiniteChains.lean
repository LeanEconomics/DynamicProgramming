/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib

/-!
# Finite Markov chains: ergodic sets

SLP §11.1, pp. 319–326. A Markov chain on a finite set `S` is a stochastic matrix `Π`
(`Matrix.rowStochastic ℝ S`). Its powers are stochastic, and the distribution `p ∈ Δ` of the
state moves to `pΠ`.

* `simplex`, `IsInvariantDist`: the unit simplex `Δ` and invariant distributions `pΠ = p`.
* `Cons`, `IsTransient`, `IsRecurrent` (p. 326): `j` is a consequent of `i` if `π⁽ⁿ⁾ᵢⱼ > 0` for
  some `n ≥ 1`; transient and recurrent states. A state is transient iff it is not recurrent
  (`isTransient_iff_not_isRecurrent`).
* `IsClosedSet`, `IsErgodic` (p. 321): `E` is closed if `P(s, E) = 1` for `s ∈ E`; ergodic if it
  is closed, nonempty, and no proper nonempty subset is closed. The book's definition omits
  nonemptiness, without which `∅` would be ergodic.
* **Theorem 11.1a** (`theorem_11_1a`): there is a recurrent state; the consequents of a
  recurrent state form an ergodic set, and every ergodic set arises this way; two ergodic sets
  are equal or disjoint; and a state is transient iff it lies in no ergodic set. So `S` is
  partitioned into `M ≥ 1` ergodic sets and the transient set.

The book's existence proof for a recurrent state is an induction along chains of transient
states; here a state whose set of consequents has the fewest elements is used instead.
-/

namespace StokeyLucasPrescott.StrongConvergence

open Matrix Finset

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The unit simplex `Δ` of probability vectors on `S`. -/
def simplex (S : Type*) [Fintype S] : Set (S → ℝ) := {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}

/-- An **invariant distribution** (p. 322): `p ∈ Δ` with `pΠ = p`. -/
def IsInvariantDist (P : Matrix S S ℝ) (p : S → ℝ) : Prop := p ∈ simplex S ∧ p ᵥ* P = p

/-- `j` is a **consequent** of `i` (p. 326): `π⁽ⁿ⁾ᵢⱼ > 0` for some `n ≥ 1`. -/
def Cons (P : Matrix S S ℝ) (i j : S) : Prop := ∃ n, 1 ≤ n ∧ 0 < (P ^ n) i j

/-- `i` is **transient** (p. 326): some consequent `j` of `i` has `π⁽ⁿ⁾ⱼᵢ = 0` for all `n ≥ 1`. -/
def IsTransient (P : Matrix S S ℝ) (i : S) : Prop :=
  ∃ j, Cons P i j ∧ ∀ n, 1 ≤ n → (P ^ n) j i = 0

/-- `i` is **recurrent** (p. 326): `i` is a consequent of each of its consequents. -/
def IsRecurrent (P : Matrix S S ℝ) (i : S) : Prop := ∀ j, Cons P i j → Cons P j i

/-- `E` is **closed**: `P(s, E) = 1` for every `s ∈ E`. -/
def IsClosedSet (P : Matrix S S ℝ) (E : Finset S) : Prop := ∀ i ∈ E, ∑ j ∈ E, P i j = 1

/-- An **ergodic set** (p. 321): nonempty, closed, and with no proper nonempty closed subset. -/
def IsErgodic (P : Matrix S S ℝ) (E : Finset S) : Prop :=
  E.Nonempty ∧ IsClosedSet P E ∧ ∀ F ⊆ E, F.Nonempty → IsClosedSet P F → F = E

/-- The consequents of `i`. -/
noncomputable def consSet (P : Matrix S S ℝ) (i : S) : Finset S := by
  classical exact univ.filter (Cons P i)

variable {P : Matrix S S ℝ}

theorem mem_consSet {i j : S} : j ∈ consSet P i ↔ Cons P i j := by simp [consSet]

theorem pow_mem_rowStochastic (hP : P ∈ rowStochastic ℝ S) (n : ℕ) :
    P ^ n ∈ rowStochastic ℝ S :=
  Submonoid.pow_mem _ hP n

theorem pow_nonneg' (hP : P ∈ rowStochastic ℝ S) (n : ℕ) (i j : S) : 0 ≤ (P ^ n) i j :=
  nonneg_of_mem_rowStochastic (pow_mem_rowStochastic hP n)

theorem pow_le_one' (hP : P ∈ rowStochastic ℝ S) (n : ℕ) (i j : S) : (P ^ n) i j ≤ 1 :=
  le_one_of_mem_rowStochastic (pow_mem_rowStochastic hP n)

theorem pow_row_sum (hP : P ∈ rowStochastic ℝ S) (n : ℕ) (i : S) : ∑ j, (P ^ n) i j = 1 :=
  sum_row_of_mem_rowStochastic (pow_mem_rowStochastic hP n) i

/-- Chapman–Kolmogorov: `π⁽ᵐ⁺ⁿ⁾ᵢₖ ≥ π⁽ᵐ⁾ᵢⱼ π⁽ⁿ⁾ⱼₖ`. -/
theorem pow_add_ge (hP : P ∈ rowStochastic ℝ S) (m n : ℕ) (i j k : S) :
    (P ^ m) i j * (P ^ n) j k ≤ (P ^ (m + n)) i k := by
  rw [pow_add, mul_apply]
  exact single_le_sum (f := fun l => (P ^ m) i l * (P ^ n) l k)
    (fun l _ => mul_nonneg (pow_nonneg' hP m i l) (pow_nonneg' hP n l k)) (mem_univ j)

theorem pow_add_pos (hP : P ∈ rowStochastic ℝ S) {m n : ℕ} {i j k : S} (h1 : 0 < (P ^ m) i j)
    (h2 : 0 < (P ^ n) j k) : 0 < (P ^ (m + n)) i k :=
  lt_of_lt_of_le (mul_pos h1 h2) (pow_add_ge hP m n i j k)

theorem Cons.trans (hP : P ∈ rowStochastic ℝ S) {i j k : S} (h1 : Cons P i j) (h2 : Cons P j k) :
    Cons P i k := by
  obtain ⟨m, hm, hm'⟩ := h1
  obtain ⟨n, -, hn'⟩ := h2
  exact ⟨m + n, by omega, pow_add_pos hP hm' hn'⟩

/-- Every state has a consequent. -/
theorem exists_cons (hP : P ∈ rowStochastic ℝ S) (i : S) : ∃ j, Cons P i j := by
  by_contra h
  push Not at h
  have : ∀ j, (P ^ 1) i j = 0 := fun j =>
    le_antisymm (not_lt.1 fun hp => h j ⟨1, le_rfl, hp⟩) (pow_nonneg' hP 1 i j)
  have hs := pow_row_sum hP 1 i
  simp [this] at hs

theorem isTransient_iff_not_isRecurrent (hP : P ∈ rowStochastic ℝ S) (i : S) :
    IsTransient P i ↔ ¬ IsRecurrent P i := by
  constructor
  · rintro ⟨j, hij, hj⟩ hrec
    obtain ⟨n, hn, hn'⟩ := hrec j hij
    exact (hj n hn ▸ hn').false
  · intro h
    simp only [IsRecurrent, not_forall] at h
    obtain ⟨j, hij, hji⟩ := h
    refine ⟨j, hij, fun n hn => le_antisymm (not_lt.1 fun hp => hji ⟨n, hn, hp⟩)
      (pow_nonneg' hP n j i)⟩

omit [DecidableEq S] in
/-- A positive sum has a positive term. -/
theorem exists_pos_of_sum_pos {f : S → ℝ} (h : 0 < ∑ k, f k) : ∃ k, 0 < f k := by
  by_contra hc
  push Not at hc
  exact (sum_nonpos fun k _ => hc k).not_gt h

/-- In a closed set, `P(i, j) = 0` for `i ∈ E`, `j ∉ E`. -/
theorem IsClosedSet.apply_eq_zero (hP : P ∈ rowStochastic ℝ S) {E : Finset S}
    (hE : IsClosedSet P E) {i j : S} (hi : i ∈ E) (hj : j ∉ E) : P i j = 0 := by
  have hsum := sum_row_of_mem_rowStochastic hP i
  rw [← sum_add_sum_compl E, hE i hi] at hsum
  have h0 : ∑ k ∈ Eᶜ, P i k = 0 := by linarith
  exact (sum_eq_zero_iff_of_nonneg fun k _ => nonneg_of_mem_rowStochastic hP).1 h0 j
    (mem_compl.2 hj)

/-- A closed set is never left: `π⁽ⁿ⁾ᵢⱼ > 0` and `i ∈ E` give `j ∈ E`. -/
theorem IsClosedSet.mem_of_pow_pos (hP : P ∈ rowStochastic ℝ S) {E : Finset S}
    (hE : IsClosedSet P E) {i : S} (hi : i ∈ E) :
    ∀ n {j : S}, 0 < (P ^ n) i j → j ∈ E := by
  intro n
  induction n with
  | zero =>
    intro j hj
    rw [pow_zero, one_apply] at hj
    split_ifs at hj with h
    · exact h ▸ hi
    · exact absurd hj (lt_irrefl 0)
  | succ n ih =>
    intro j hj
    rw [pow_succ, mul_apply] at hj
    obtain ⟨k, hk⟩ := exists_pos_of_sum_pos hj
    have hk1 : 0 < (P ^ n) i k := lt_of_le_of_ne (pow_nonneg' hP n i k) fun h => by
      rw [← h, zero_mul] at hk; exact lt_irrefl 0 hk
    have hk2 : 0 < P k j := lt_of_le_of_ne (nonneg_of_mem_rowStochastic hP) fun h => by
      rw [← h, mul_zero] at hk; exact lt_irrefl 0 hk
    by_contra hjE
    exact (hE.apply_eq_zero hP (ih hk1) hjE ▸ hk2).false

/-- A set from which no one-step transition leaves is closed. -/
theorem isClosedSet_of (hP : P ∈ rowStochastic ℝ S) {E : Finset S}
    (h : ∀ i ∈ E, ∀ j, 0 < P i j → j ∈ E) : IsClosedSet P E := by
  intro i hi
  have hsum := sum_row_of_mem_rowStochastic hP i
  rw [← sum_add_sum_compl E] at hsum
  have h0 : ∑ k ∈ Eᶜ, P i k = 0 := sum_eq_zero fun k hk =>
    le_antisymm (not_lt.1 fun hp => mem_compl.1 hk (h i hi k hp)) (nonneg_of_mem_rowStochastic hP)
  linarith

theorem isClosedSet_univ (hP : P ∈ rowStochastic ℝ S) : IsClosedSet P univ :=
  isClosedSet_of hP fun _ _ _ _ => mem_univ _

theorem consSet_closed (hP : P ∈ rowStochastic ℝ S) (i : S) : IsClosedSet P (consSet P i) :=
  isClosedSet_of hP fun k hk j hj => mem_consSet.2
    ((mem_consSet.1 hk).trans hP ⟨1, le_rfl, by rwa [pow_one]⟩)

theorem consSet_nonempty (hP : P ∈ rowStochastic ℝ S) (i : S) : (consSet P i).Nonempty :=
  let ⟨j, hj⟩ := exists_cons hP i; ⟨j, mem_consSet.2 hj⟩

/-- The consequents of a state of a closed set lie in it. -/
theorem IsClosedSet.consSet_subset (hP : P ∈ rowStochastic ℝ S) {E : Finset S}
    (hE : IsClosedSet P E) {i : S} (hi : i ∈ E) : consSet P i ⊆ E := fun _ hj =>
  let ⟨n, _, hn⟩ := mem_consSet.1 hj; hE.mem_of_pow_pos hP hi n hn

omit [Fintype S] [DecidableEq S] in
/-- Every nonempty closed set contains an ergodic set (one of least cardinality among its
nonempty closed subsets). -/
theorem exists_ergodic_subset {E : Finset S} (hne : E.Nonempty)
    (hE : IsClosedSet P E) : ∃ F ⊆ E, IsErgodic P F := by
  classical
  set C := E.powerset.filter fun F => F.Nonempty ∧ IsClosedSet P F
  have hC : C.Nonempty := ⟨E, mem_filter.2 ⟨mem_powerset_self E, hne, hE⟩⟩
  obtain ⟨F, hF, hmin⟩ := exists_min_image C card hC
  obtain ⟨hFE, hFne, hFc⟩ := by simpa [C] using hF
  refine ⟨F, hFE, hFne, hFc, fun G hGF hGne hGc => ?_⟩
  exact eq_of_subset_of_card_le hGF
    (hmin G (mem_filter.2 ⟨mem_powerset.2 (hGF.trans hFE), hGne, hGc⟩))

/-- An ergodic set is the set of consequents of each of its states. -/
theorem IsErgodic.eq_consSet (hP : P ∈ rowStochastic ℝ S) {E : Finset S} (hE : IsErgodic P E)
    {i : S} (hi : i ∈ E) : E = consSet P i :=
  (hE.2.2 _ (hE.2.1.consSet_subset hP hi) (consSet_nonempty hP i) (consSet_closed hP i)).symm

/-- The states of an ergodic set are recurrent. -/
theorem IsErgodic.isRecurrent (hP : P ∈ rowStochastic ℝ S) {E : Finset S} (hE : IsErgodic P E)
    {i : S} (hi : i ∈ E) : IsRecurrent P i := by
  intro j hij
  have hj : j ∈ E := hE.eq_consSet hP hi ▸ mem_consSet.2 hij
  exact mem_consSet.1 (hE.eq_consSet hP hj ▸ hi)

theorem IsRecurrent.self_mem_consSet (hP : P ∈ rowStochastic ℝ S) {i : S} (h : IsRecurrent P i) :
    i ∈ consSet P i := by
  obtain ⟨j, hj⟩ := exists_cons hP i
  exact mem_consSet.2 (hj.trans hP (h j hj))

/-- The consequents of a recurrent state form an ergodic set. -/
theorem IsRecurrent.isErgodic (hP : P ∈ rowStochastic ℝ S) {i : S} (h : IsRecurrent P i) :
    IsErgodic P (consSet P i) := by
  refine ⟨consSet_nonempty hP i, consSet_closed hP i, fun F hF hne hFc => ?_⟩
  obtain ⟨k, hk⟩ := hne
  refine subset_antisymm hF fun j hj => hFc.consSet_subset hP hk ?_
  exact mem_consSet.2 ((h k (mem_consSet.1 (hF hk))).trans hP (mem_consSet.1 hj))

/-- **Theorem 11.1a.** `S` is partitioned into `M ≥ 1` ergodic sets and the transient set: an
ergodic set exists; the consequents of a recurrent state form an ergodic set containing it, and
every ergodic set is the set of consequents of each of its (recurrent) states; distinct ergodic
sets are disjoint; and a state is transient iff it lies in no ergodic set. -/
theorem theorem_11_1a [Nonempty S] (hP : P ∈ rowStochastic ℝ S) :
    (∃ E, IsErgodic P E) ∧
      (∀ i, IsRecurrent P i → IsErgodic P (consSet P i) ∧ i ∈ consSet P i) ∧
      (∀ E, IsErgodic P E → ∀ i ∈ E, IsRecurrent P i ∧ E = consSet P i) ∧
      (∀ E E', IsErgodic P E → IsErgodic P E' → E = E' ∨ Disjoint E E') ∧
      ∀ i, IsTransient P i ↔ ∀ E, IsErgodic P E → i ∉ E := by
  refine ⟨?_, fun i h => ⟨h.isErgodic hP, h.self_mem_consSet hP⟩,
    fun E hE i hi => ⟨hE.isRecurrent hP hi, hE.eq_consSet hP hi⟩, fun E E' hE hE' => ?_,
    fun i => ?_⟩
  · obtain ⟨F, -, hF⟩ := exists_ergodic_subset univ_nonempty (isClosedSet_univ hP)
    exact ⟨F, hF⟩
  · by_cases h : Disjoint E E'
    · exact Or.inr h
    · obtain ⟨i, hi, hi'⟩ := not_disjoint_iff.1 h
      exact Or.inl ((hE.eq_consSet hP hi).trans (hE'.eq_consSet hP hi').symm)
  · rw [isTransient_iff_not_isRecurrent hP]
    constructor
    · intro h E hE hi
      exact h (hE.isRecurrent hP hi)
    · intro h hrec
      exact h _ (hrec.isErgodic hP) (hrec.self_mem_consSet hP)

end StokeyLucasPrescott.StrongConvergence
