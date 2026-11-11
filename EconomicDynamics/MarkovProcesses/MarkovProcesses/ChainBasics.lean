/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.LinearAlgebra.Matrix.Stochastic
import MarkovProcesses.ChainNumberTheory

/-!
# Finite Markov chains: transition matrices and the classification vocabulary

Miao, §3.1 opening and §3.1.1, pp. 86–93. A finite-state Markov chain is described by its
transition matrix `P`, a row-stochastic matrix (`P ∈ Matrix.rowStochastic ℝ S`, Mathlib) on a
finite state space `S`; the `m`-step transition probabilities are the entries of `P ^ m`. The
results of §3.1 for finite chains are statements about `P` and its powers and need no path
measure (the path-space description of Definition 3.0.1 is in `ChainProcess`).

* `mc_pow_mem`, `mc_pow_nonneg`, `mc_pow_le_one`, `mc_pow_row_sum`: `Pᵐ` is a transition matrix
  (p. 87).
* **(3.1)** (`eq_3_1`): the Chapman–Kolmogorov equation `p⁽ᵐ⁺ᵏ⁾ᵢⱼ = Σᵣ p⁽ᵏ⁾ᵢᵣ p⁽ᵐ⁾ᵣⱼ`, and
  its consequence `mc_pow_add_pos`.
* **Definition 3.1.1** (p. 90): `mc_Accessible P i j` (`i → j`: `p⁽ᵐ⁾ᵢⱼ > 0` for some `m ≥ 1`),
  `mc_Communicate P i j` (`i ↔ j`; `i ↔ i` by convention); `mc_communicate_equivalence`:
  communication is an equivalence relation.
* **Definition 3.1.2** (p. 90): `mc_IsIrreducible`, `mc_IsDecomposable`;
  `mc_isIrreducible_iff`: irreducibility is equivalent to `p⁽ᵏ⁾ᵢⱼ > 0` for some `k ≥ 1`, for
  every pair `i, j` including `i = j` (the alternative definition mentioned on p. 90).
* **Definition 3.1.3** (p. 91): `mc_IsRecurrent`, `mc_IsTransient` for finite chains.
* **Definition 3.1.4** (p. 93): `mc_returnSet`, `mc_period`, `mc_IsAperiodic`, `mc_IsPeriodic`;
  `mc_returnSet_isAddClosed`.
* `mc_IsClosed` and `mc_pow_eq_zero_of_closed`: if no arc leaves `E`, no path leaves `E`; this
  is the tool behind all the class computations of the examples.

**Departures.** For a state without returns the set of return times is empty and `mc_period`
is `0`; the book says the definition "applies to recurrent states only", but it applies to
every state with a return (state 1 of Example 3.1.3 is transient and aperiodic).
-/

namespace Miao.MarkovProcesses

open Matrix

variable {S : Type*} [Fintype S] [DecidableEq S] {P : Matrix S S ℝ}

/-! ### Transition matrices and their powers -/

/-- Miao, p. 87: if `P` is a transition matrix, so is `Pᵐ`. -/
theorem mc_pow_mem (hP : P ∈ rowStochastic ℝ S) (m : ℕ) : P ^ m ∈ rowStochastic ℝ S :=
  pow_mem hP m

/-- The entries of `Pᵐ` are nonnegative. -/
theorem mc_pow_nonneg (hP : P ∈ rowStochastic ℝ S) (m : ℕ) (i j : S) : 0 ≤ (P ^ m) i j :=
  nonneg_of_mem_rowStochastic (mc_pow_mem hP m)

/-- The entries of `Pᵐ` are at most one. -/
theorem mc_pow_le_one (hP : P ∈ rowStochastic ℝ S) (m : ℕ) (i j : S) : (P ^ m) i j ≤ 1 :=
  le_one_of_mem_rowStochastic (mc_pow_mem hP m)

/-- The rows of `Pᵐ` sum to one: the `i`-th row is the distribution `m` periods ahead from `i`
(Miao, p. 87). -/
theorem mc_pow_row_sum (hP : P ∈ rowStochastic ℝ S) (m : ℕ) (i : S) :
    ∑ j, (P ^ m) i j = 1 :=
  sum_row_of_mem_rowStochastic (mc_pow_mem hP m) i

/-- Entries of a stochastic matrix are nonnegative (restated for rewriting). -/
theorem mc_entry_nonneg (hP : P ∈ rowStochastic ℝ S) (i j : S) :
    0 ≤ P i j :=
  nonneg_of_mem_rowStochastic hP

/-- Miao, (3.1), p. 87: the **Chapman–Kolmogorov equation** `Pᵐ⁺ᵏ = PᵏPᵐ`, that is
`p⁽ᵐ⁺ᵏ⁾ᵢⱼ = Σᵣ p⁽ᵏ⁾ᵢᵣ p⁽ᵐ⁾ᵣⱼ`. -/
theorem eq_3_1 (P : Matrix S S ℝ) (m k : ℕ) (i j : S) :
    (P ^ (m + k)) i j = ∑ r, (P ^ k) i r * (P ^ m) r j := by
  rw [add_comm, pow_add, mul_apply]

/-- A consequence of (3.1): `p⁽ᵐ⁺ⁿ⁾ᵢₖ ≥ p⁽ᵐ⁾ᵢⱼ p⁽ⁿ⁾ⱼₖ`. -/
theorem mc_pow_add_ge (hP : P ∈ rowStochastic ℝ S) (m n : ℕ) (i j k : S) :
    (P ^ m) i j * (P ^ n) j k ≤ (P ^ (m + n)) i k := by
  rw [pow_add, mul_apply]
  exact Finset.single_le_sum (f := fun r => (P ^ m) i r * (P ^ n) r k)
    (fun r _ => mul_nonneg (mc_pow_nonneg hP m i r) (mc_pow_nonneg hP n r k))
    (Finset.mem_univ j)

/-- Positive `m`- and `n`-step transitions compose to a positive `(m + n)`-step transition. -/
theorem mc_pow_add_pos (hP : P ∈ rowStochastic ℝ S) {m n : ℕ} {i j k : S}
    (h1 : 0 < (P ^ m) i j) (h2 : 0 < (P ^ n) j k) : 0 < (P ^ (m + n)) i k :=
  lt_of_lt_of_le (mul_pos h1 h2) (mc_pow_add_ge hP m n i j k)

/-- Every row of a stochastic matrix has a positive entry. -/
theorem mc_exists_pos_entry [Nonempty S] (hP : P ∈ rowStochastic ℝ S) (i : S) :
    ∃ j, 0 < P i j := by
  by_contra h
  push Not at h
  have h0 : ∑ j, P i j = 0 :=
    Finset.sum_eq_zero fun j _ => le_antisymm (h j) (mc_entry_nonneg hP i j)
  rw [sum_row_of_mem_rowStochastic hP i] at h0
  exact one_ne_zero h0

/-! ### Closed sets -/

/-- A set `E` of states is **closed** if no arc leaves it: `pᵢⱼ = 0` for `i ∈ E`, `j ∉ E`. -/
def mc_IsClosed (P : Matrix S S ℝ) (E : Set S) : Prop := ∀ i ∈ E, ∀ j ∉ E, P i j = 0

/-- If no arc leaves `E`, then no path leaves `E`: `p⁽ⁿ⁾ᵢⱼ = 0` for `i ∈ E`, `j ∉ E`. -/
theorem mc_pow_eq_zero_of_closed {E : Set S} (hE : mc_IsClosed P E) (n : ℕ) {i j : S}
    (hi : i ∈ E) (hj : j ∉ E) : (P ^ n) i j = 0 := by
  induction n generalizing j with
  | zero =>
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    simp [hij]
  | succ n ih =>
    rw [pow_succ, mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k ∈ E
    · rw [hE k hk j hj, mul_zero]
    · rw [ih hk, zero_mul]

/-! ### Definition 3.1.1: accessibility and communication -/

/-- **Definition 3.1.1** (Miao, p. 90): `j` is **accessible** from `i` (`i → j`) if
`p⁽ᵐ⁾ᵢⱼ > 0` for some `m ≥ 1`. -/
def mc_Accessible (P : Matrix S S ℝ) (i j : S) : Prop := ∃ m, 1 ≤ m ∧ 0 < (P ^ m) i j

/-- **Definition 3.1.1** (Miao, p. 90): `i` and `j` **communicate** (`i ↔ j`) if each is
accessible from the other; by convention `i ↔ i`. -/
def mc_Communicate (P : Matrix S S ℝ) (i j : S) : Prop :=
  i = j ∨ (mc_Accessible P i j ∧ mc_Accessible P j i)

/-- Accessibility is transitive. -/
theorem mc_Accessible.trans (hP : P ∈ rowStochastic ℝ S) {i j k : S}
    (h1 : mc_Accessible P i j) (h2 : mc_Accessible P j k) : mc_Accessible P i k := by
  obtain ⟨m, hm, hm'⟩ := h1
  obtain ⟨n, hn, hn'⟩ := h2
  exact ⟨m + n, by omega, mc_pow_add_pos hP hm' hn'⟩

/-- A positive one-step transition gives accessibility. -/
theorem mc_accessible_of_pos {i j : S} (h : 0 < P i j) : mc_Accessible P i j :=
  ⟨1, le_rfl, by simpa using h⟩

/-- Miao, p. 90: communication is an **equivalence relation** (reflexive, symmetric,
transitive). -/
theorem mc_communicate_equivalence (hP : P ∈ rowStochastic ℝ S) :
    Equivalence (mc_Communicate P) where
  refl i := Or.inl rfl
  symm := by
    rintro i j (rfl | ⟨h1, h2⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨h2, h1⟩
  trans := by
    rintro i j k (rfl | ⟨h1, h2⟩) (rfl | ⟨h3, h4⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨h3, h4⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inr ⟨h1.trans hP h3, h4.trans hP h2⟩

/-- If `i ↔ j` and `j → k`, then `i → k`. -/
theorem mc_Communicate.accessible_trans (hP : P ∈ rowStochastic ℝ S) {i j k : S}
    (h1 : mc_Communicate P i j) (h2 : mc_Accessible P j k) : mc_Accessible P i k := by
  rcases h1 with rfl | ⟨h1, -⟩
  · exact h2
  · exact h1.trans hP h2

/-! ### Definition 3.1.2: irreducibility -/

/-- **Definition 3.1.2** (Miao, p. 90): the chain is **irreducible** if the state space is a
single communication class. -/
def mc_IsIrreducible (P : Matrix S S ℝ) : Prop := ∀ i j, mc_Communicate P i j

/-- **Definition 3.1.2** (Miao, p. 90): the chain is **decomposable** if there are at least two
communication classes. -/
def mc_IsDecomposable (P : Matrix S S ℝ) : Prop := ∃ i j, ¬ mc_Communicate P i j

/-- Miao, p. 90: decomposable is the negation of irreducible. -/
theorem mc_isDecomposable_iff : mc_IsDecomposable P ↔ ¬ mc_IsIrreducible P := by
  simp [mc_IsDecomposable, mc_IsIrreducible]

/-- Miao, p. 90: for an irreducible chain, for all states `i, j` (including `i = j`) there is
`k ≥ 1` with `p⁽ᵏ⁾ᵢⱼ > 0`, and conversely; "sometimes this property is used to define
irreducibility". -/
theorem mc_isIrreducible_iff (hP : P ∈ rowStochastic ℝ S) :
    mc_IsIrreducible P ↔ ∀ i j, mc_Accessible P i j := by
  constructor
  · intro h i j
    by_cases hij : i = j
    · subst hij
      have : Nonempty S := ⟨i⟩
      obtain ⟨k, hk⟩ := mc_exists_pos_entry hP i
      by_cases hki : k = i
      · subst hki; exact mc_accessible_of_pos hk
      · rcases h k i with h' | ⟨h', -⟩
        · exact absurd h' hki
        · exact (mc_accessible_of_pos hk).trans hP h'
    · rcases h i j with h' | ⟨h', -⟩
      · exact absurd h' hij
      · exact h'
  · intro h i j
    exact Or.inr ⟨h i j, h j i⟩

/-! ### Definition 3.1.3: recurrence and transience for finite chains -/

/-- **Definition 3.1.3** (Miao, p. 91): for finite chains, `i` is **recurrent** if whenever
`i → j`, also `j → i`. -/
def mc_IsRecurrent (P : Matrix S S ℝ) (i : S) : Prop :=
  ∀ j, mc_Accessible P i j → mc_Accessible P j i

/-- **Definition 3.1.3** (Miao, p. 91): a state is **transient** if it is not recurrent. -/
def mc_IsTransient (P : Matrix S S ℝ) (i : S) : Prop := ¬ mc_IsRecurrent P i

/-- Miao, p. 91: `i` is transient iff some state `j` is accessible from `i` but `i` is not
accessible from `j`. -/
theorem mc_isTransient_iff (i : S) :
    mc_IsTransient P i ↔ ∃ j, mc_Accessible P i j ∧ ¬ mc_Accessible P j i := by
  simp [mc_IsTransient, mc_IsRecurrent]

/-! ### Definition 3.1.4: periods -/

/-- The return times `{m ≥ 1 : p⁽ᵐ⁾ᵢᵢ > 0}` of the state `i`. -/
def mc_returnSet (P : Matrix S S ℝ) (i : S) : Set ℕ := {m | 1 ≤ m ∧ 0 < (P ^ m) i i}

/-- **Definition 3.1.4** (Miao, p. 93): the **period** `d(i)` of a state is the greatest common
divisor of the `m ≥ 1` with `p⁽ᵐ⁾ᵢᵢ > 0` (it is `0` if there is no such `m`). -/
noncomputable def mc_period (P : Matrix S S ℝ) (i : S) : ℕ := mc_setGcd (mc_returnSet P i)

/-- **Definition 3.1.4** (Miao, p. 93): a state is **aperiodic** if its period is `1`. -/
def mc_IsAperiodic (P : Matrix S S ℝ) (i : S) : Prop := mc_period P i = 1

/-- **Definition 3.1.4** (Miao, p. 93): a state is **periodic** if its period is at least `2`. -/
def mc_IsPeriodic (P : Matrix S S ℝ) (i : S) : Prop := 2 ≤ mc_period P i

/-- The return times of a state are closed under addition (by (3.1)). -/
theorem mc_returnSet_isAddClosed (hP : P ∈ rowStochastic ℝ S) (i : S) :
    mc_IsAddClosed (mc_returnSet P i) := by
  rintro a ⟨ha, ha'⟩ b ⟨-, hb'⟩
  exact ⟨by omega, mc_pow_add_pos hP ha' hb'⟩

/-- A state with `p⁽ⁿ⁾ᵢᵢ > 0` (`n ≥ 1`) has period dividing `n`. -/
theorem mc_period_dvd (hP : P ∈ rowStochastic ℝ S) {i : S} {n : ℕ} (hn : n ∈ mc_returnSet P i) :
    mc_period P i ∣ n :=
  mc_setGcd_dvd (mc_returnSet_isAddClosed hP i) hn hn.1 hn

/-- Miao, p. 93: the state `i` has period `d` iff a return to `i` is impossible except in
multiples of `d`, and `d` is the greatest integer with this property (for a state with a
return). -/
theorem mc_period_spec (hP : P ∈ rowStochastic ℝ S) {i : S} {n₀ : ℕ}
    (hn₀ : n₀ ∈ mc_returnSet P i) :
    0 < mc_period P i ∧ (∀ n, 1 ≤ n → 0 < (P ^ n) i i → mc_period P i ∣ n) ∧
      ∀ d, (∀ n, 1 ≤ n → 0 < (P ^ n) i i → d ∣ n) → d ≤ mc_period P i := by
  have hS := mc_returnSet_isAddClosed hP i
  have hpos := mc_setGcd_pos hS hn₀ hn₀.1
  refine ⟨hpos, fun n h1 h2 => mc_period_dvd hP ⟨h1, h2⟩, fun d hd => ?_⟩
  exact Nat.le_of_dvd hpos (dvd_mc_setGcd hS hn₀ hn₀.1 fun s hs => hd s hs.1 hs.2)

end Miao.MarkovProcesses
