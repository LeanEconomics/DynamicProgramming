import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Data.Matrix.Block
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Analysis.Convex.Extreme
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The g.c.d. of a set of return times

Copied from `StochasticStability/DriftRegularity` (module `Period`, the g.c.d. part of
Meyn–Tweedie §5.4 and Lemma D.7.4), with names prefixed `mc_`. Used for the period of a state
(Miao, Definition 3.1.4, p. 93), Theorem 3.1.2 (p. 93) and the number-theory lemma in the proof
of Theorem 3.1.4 (p. 96; Billingsley, Appendix A21).

* `mc_IsAddClosed S`: `S ⊆ ℕ` is closed under addition; `mc_setGcd S`: the largest common
  divisor of the elements of `S` (`0` when `S` has no positive element).
* `mc_setGcd_dvd`, `dvd_mc_setGcd`, `mc_setGcd_pos`: for additively closed `S` with a positive
  element, `mc_setGcd S` divides every element and every common divisor divides it.
* `mc_eventually_mul_setGcd_mem`: such an `S` contains every large multiple of its g.c.d.;
  `mc_eventually_mem_of_setGcd_eq_one`: if the g.c.d. is `1`, `S` contains all large integers.
-/

namespace Miao.MarkovProcesses

/-- `S ⊆ ℕ` is closed under addition. -/
def mc_IsAddClosed (S : Set ℕ) : Prop := ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S

/-- The **greatest common divisor** of `S ⊆ ℕ`: the largest common divisor of its elements
(the period of Miao, Definition 3.1.4, p. 93). -/
noncomputable def mc_setGcd (S : Set ℕ) : ℕ := sSup {d | ∀ s ∈ S, d ∣ s}

/-- Multiples `(q + 1) b` of an element of an additively closed set lie in it. -/
theorem mc_IsAddClosed.succ_mul_mem {S : Set ℕ} (hS : mc_IsAddClosed S) {b : ℕ} (hb : b ∈ S)
    (q : ℕ) :
    (q + 1) * b ∈ S := by
  induction q with
  | zero => simpa using hb
  | succ q ih => rw [add_mul, one_mul]; exact hS _ ih _ hb

/-- Multiples `q b` of an element of `S ∪ {0}` lie in `S ∪ {0}`. -/
theorem mc_IsAddClosed.mul_mem_zero {S : Set ℕ} (hS : mc_IsAddClosed S) {b : ℕ} (hb : b = 0 ∨ b ∈ S)
    (q : ℕ) : q * b = 0 ∨ q * b ∈ S := by
  rcases hb with rfl | hb
  · left; simp
  · rcases q with _ | q
    · left; simp
    · exact Or.inr (hS.succ_mul_mem hb q)

/-- The sum of an element of `S ∪ {0}` and an element of `S` lies in `S`. -/
theorem mc_IsAddClosed.add_mem_of_zero {S : Set ℕ} (hS : mc_IsAddClosed S) {a b : ℕ}
    (ha : a = 0 ∨ a ∈ S) (hb : b ∈ S) : a + b ∈ S := by
  rcases ha with rfl | ha
  · simpa using hb
  · exact hS _ ha _ hb

/-- **The g.c.d. as a least difference.** If `S` is additively closed and has a positive element,
the least positive difference `g = b − a` of elements of `S ∪ {0}` (with `b ∈ S`) divides every
element of `S`, and every common divisor of `S` divides it. -/
theorem mc_exists_gcd_witness {S : Set ℕ} (hS : mc_IsAddClosed S) {s₀ : ℕ} (hs₀ : s₀ ∈ S)
    (hpos : 0 < s₀) :
    ∃ g a, 0 < g ∧ (a = 0 ∨ a ∈ S) ∧ a + g ∈ S ∧ (∀ s ∈ S, g ∣ s) ∧
      ∀ d, (∀ s ∈ S, d ∣ s) → d ∣ g := by
  set T : Set ℕ := {g | 0 < g ∧ ∃ a, (a = 0 ∨ a ∈ S) ∧ a + g ∈ S} with hT
  have hTne : T.Nonempty := ⟨s₀, hpos, 0, Or.inl rfl, by simpa using hs₀⟩
  obtain ⟨hgpos, a, ha, hag⟩ := Nat.sInf_mem hTne
  set g := sInf T
  refine ⟨g, a, hgpos, ha, hag, fun s hs => ?_, fun d hd => ?_⟩
  · -- the remainder of `s` modulo `g` is a smaller positive difference unless it is `0`
    by_contra hdvd
    have hr : 0 < s % g := Nat.pos_of_ne_zero fun h => hdvd (Nat.dvd_of_mod_eq_zero h)
    have hrT : s % g ∈ T := by
      refine ⟨hr, s / g * (a + g), hS.mul_mem_zero (Or.inr hag) _, ?_⟩
      have hsplit : s / g * (a + g) + s % g = s / g * a + s := by
        have := Nat.div_add_mod s g
        nlinarith [this]
      rw [hsplit]
      exact hS.add_mem_of_zero (hS.mul_mem_zero ha _) hs
    exact absurd (Nat.sInf_le hrT) (not_le.2 (Nat.mod_lt s hgpos))
  · have h1 : d ∣ a := by
      rcases ha with rfl | ha
      · exact dvd_zero d
      · exact hd a ha
    exact (Nat.dvd_add_right h1).1 (hd _ hag)

/-- For an additively closed `S` with a positive element, `mc_setGcd S` is the least positive
difference of `mc_exists_gcd_witness`. -/
theorem mc_setGcd_spec {S : Set ℕ} (hS : mc_IsAddClosed S) {s₀ : ℕ} (hs₀ : s₀ ∈ S) (hpos : 0 < s₀) :
    ∃ a, 0 < mc_setGcd S ∧ (a = 0 ∨ a ∈ S) ∧ a + mc_setGcd S ∈ S ∧ (∀ s ∈ S, mc_setGcd S ∣ s) ∧
      ∀ d, (∀ s ∈ S, d ∣ s) → d ∣ mc_setGcd S := by
  obtain ⟨g, a, hg, ha, hag, hdvd, hmax⟩ := mc_exists_gcd_witness hS hs₀ hpos
  have heq : mc_setGcd S = g := by
    refine IsGreatest.csSup_eq ⟨hdvd, fun d hd => Nat.le_of_dvd hg (hmax d hd)⟩
  rw [heq]
  exact ⟨a, hg, ha, hag, hdvd, hmax⟩

/-- `mc_setGcd S` divides every element of `S`. -/
theorem mc_setGcd_dvd {S : Set ℕ} (hS : mc_IsAddClosed S) {s₀ : ℕ} (hs₀ : s₀ ∈ S) (hpos : 0 < s₀)
    {s : ℕ} (hs : s ∈ S) : mc_setGcd S ∣ s := by
  obtain ⟨a, -, -, -, h, -⟩ := mc_setGcd_spec hS hs₀ hpos
  exact h s hs

/-- Every common divisor of `S` divides `mc_setGcd S`. -/
theorem dvd_mc_setGcd {S : Set ℕ} (hS : mc_IsAddClosed S) {s₀ : ℕ} (hs₀ : s₀ ∈ S) (hpos : 0 < s₀)
    {d : ℕ} (hd : ∀ s ∈ S, d ∣ s) : d ∣ mc_setGcd S := by
  obtain ⟨a, -, -, -, -, h⟩ := mc_setGcd_spec hS hs₀ hpos
  exact h d hd

/-- `mc_setGcd S > 0`. -/
theorem mc_setGcd_pos {S : Set ℕ} (hS : mc_IsAddClosed S) {s₀ : ℕ} (hs₀ : s₀ ∈ S) (hpos : 0 < s₀) :
    0 < mc_setGcd S := by
  obtain ⟨a, h, -⟩ := mc_setGcd_spec hS hs₀ hpos
  exact h

/-- An additively closed set of naturals with a positive
element contains every large enough multiple of its g.c.d. -/
theorem mc_eventually_mul_setGcd_mem {S : Set ℕ} (hS : mc_IsAddClosed S) {s₀ : ℕ} (hs₀ : s₀ ∈ S)
    (hpos : 0 < s₀) :
    ∃ N, ∀ n ≥ N, n * mc_setGcd S ∈ S := by
  obtain ⟨a, hg, ha, hag, hdvd, -⟩ := mc_setGcd_spec hS hs₀ hpos
  set g := mc_setGcd S
  by_cases ha0 : a = 0
  · subst ha0
    refine ⟨1, fun n hn => ?_⟩
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact hS.succ_mul_mem (by simpa using hag) q
  · have haS : a ∈ S := ha.resolve_left ha0
    obtain ⟨k, hk⟩ := hdvd a haS
    have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => ha0 (by rw [hk, h, mul_zero])
    refine ⟨k * k, fun n hn => ?_⟩
    have hx : k ≤ n / k := (Nat.le_div_iff_mul_le hk0).2 hn
    have hr : n % k < k := Nat.mod_lt n hk0
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_lt (hr.trans_le hx)
    -- `n g = (t + 1) a + (n % k) (a + g)`
    have hsplit : n * g = (t + 1) * a + n % k * (a + g) := by
      have h1 := Nat.div_add_mod n k
      rw [ht] at h1
      rw [hk]
      nlinarith [h1]
    rw [hsplit]
    rcases Nat.eq_zero_or_pos (n % k) with h0 | h0
    · rw [h0, zero_mul, add_zero]; exact hS.succ_mul_mem haS t
    · obtain ⟨r, hr'⟩ := Nat.exists_eq_add_of_lt h0
      rw [hr', zero_add]
      exact hS _ (hS.succ_mul_mem haS t) _ (hS.succ_mul_mem hag r)

/-- An additively closed set of naturals with a positive element and g.c.d. `1` contains every
large enough natural number (the lemma of Billingsley, Appendix A21, quoted in Miao, p. 96). -/
theorem mc_eventually_mem_of_setGcd_eq_one {S : Set ℕ} (hS : mc_IsAddClosed S) {s₀ : ℕ}
    (hs₀ : s₀ ∈ S) (hpos : 0 < s₀) (h1 : mc_setGcd S = 1) : ∃ N, ∀ n ≥ N, n ∈ S := by
  obtain ⟨N, hN⟩ := mc_eventually_mul_setGcd_mem hS hs₀ hpos
  exact ⟨N, fun n hn => by simpa [h1] using hN n hn⟩

/-- The argument of Theorem 3.1.2 (Miao, p. 93) on sets of times: if `n > 0` lies in two
additively closed sets `R₁`, `R₂`, and adding `n` maps each into the other, then the two sets
have the same g.c.d. -/
theorem mc_setGcd_eq_of_shift {R₁ R₂ : Set ℕ} (h₁ : mc_IsAddClosed R₁) (h₂ : mc_IsAddClosed R₂)
    {n : ℕ} (hn : 0 < n) (hn₁ : n ∈ R₁) (hn₂ : n ∈ R₂) (h12 : ∀ t ∈ R₂, n + t ∈ R₁)
    (h21 : ∀ t ∈ R₁, n + t ∈ R₂) : mc_setGcd R₁ = mc_setGcd R₂ := by
  apply Nat.dvd_antisymm
  · refine dvd_mc_setGcd h₂ hn₂ hn fun t ht => ?_
    exact (Nat.dvd_add_right (mc_setGcd_dvd h₁ hn₁ hn hn₁)).1 (mc_setGcd_dvd h₁ hn₁ hn (h12 t ht))
  · refine dvd_mc_setGcd h₁ hn₁ hn fun t ht => ?_
    exact (Nat.dvd_add_right (mc_setGcd_dvd h₂ hn₂ hn hn₂)).1 (mc_setGcd_dvd h₂ hn₂ hn (h21 t ht))

end Miao.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Finite Markov chains: classes, Theorems 3.1.1–3.1.2 and Remark 3.1.1

Miao, §3.1.1, pp. 91–94, and Exercise 1, p. 113.

* **Theorem 3.1.1** (p. 91): (a) `theorem_3_1_1a`: recurrence is a class property;
  (b) `theorem_3_1_1b`: a nonempty finite chain has a recurrent state, and the class of a
  recurrent state consists of recurrent states, so the state space splits into at least one
  recurrent class and the transient states; (c) `theorem_3_1_1c`: every state of an
  irreducible finite chain is recurrent.
* **Theorem 3.1.2** (p. 93, finite chains; the countable case is `theorem_3_1_2_countable` in
  `ChainCountable`): communicating states have the same period (`theorem_3_1_2`).
* **Remark 3.1.1** and **Exercise 1** (pp. 92, 113): the ergodic sets of Stokey, Lucas and
  Prescott are the recurrent classes (`ex_3_1`), with `mc_classOf`, `mc_IsErgodicSet`.

**Corrections.**
* Remark 3.1.1 defines an ergodic set as a set `E` with `Σ_{j ∈ E} pᵢⱼ = 1` for `i ∈ E` such
  that no proper subset has this property. Taken literally the empty set is the only such set,
  because `∅` is a proper subset of every nonempty set and has the property vacuously
  (`remark_3_1_1_literal`). The corrected definition (`mc_IsErgodicSet`) asks `E` to be
  nonempty and no proper nonempty subset to have the property; with it Exercise 1 holds.
* The proof of Theorem 3.1.1(b) asserts that "all transient states form one class"; this is
  false (the theorem itself only claims a set of transient states):
  `theorem_3_1_1b_proof_counterexample` (the chain `0 → 1 → 2 → 2` has transient states `0`
  and `1` that do not communicate). The proof's claim that the last state `j` of a chain of
  transient states has `pⱼⱼ = 1` is also not needed: here a state whose set of accessible
  states is smallest is shown to be recurrent.
-/

namespace Miao.MarkovProcesses

open Matrix

variable {S : Type*} [Fintype S] [DecidableEq S] {P : Matrix S S ℝ}

/-! ### Theorem 3.1.1 -/

/-- If `i ↔ m` and `i` is recurrent, then `m` is recurrent. -/
theorem mc_IsRecurrent.of_communicate (hP : P ∈ rowStochastic ℝ S) {i m : S}
    (hi : mc_IsRecurrent P i) (him : mc_Communicate P i m) : mc_IsRecurrent P m := by
  rcases him with rfl | ⟨h1, h2⟩
  · exact hi
  · intro j hmj
    exact (hi j (h1.trans hP hmj)).trans hP h1

/-- **Theorem 3.1.1(a)** (Miao, p. 91): for finite chains, either all states of a class are
transient or all are recurrent. -/
theorem theorem_3_1_1a (hP : P ∈ rowStochastic ℝ S) {i m : S} (him : mc_Communicate P i m) :
    (mc_IsRecurrent P i ↔ mc_IsRecurrent P m) ∧ (mc_IsTransient P i ↔ mc_IsTransient P m) := by
  have h1 : mc_IsRecurrent P i ↔ mc_IsRecurrent P m :=
    ⟨fun h => h.of_communicate hP him,
      fun h => h.of_communicate hP ((mc_communicate_equivalence hP).symm him)⟩
  exact ⟨h1, not_congr h1⟩

/-- The set of states accessible from `i`. -/
noncomputable def mc_consSet (P : Matrix S S ℝ) (i : S) : Finset S := by
  classical exact Finset.univ.filter (mc_Accessible P i)

/-- Membership in `mc_consSet`. -/
theorem mc_mem_consSet {i j : S} : j ∈ mc_consSet P i ↔ mc_Accessible P i j := by
  classical simp [mc_consSet]

/-- **Theorem 3.1.1(b)** (Miao, p. 91): the finite state space contains at least one recurrent
state, and the class of a recurrent state consists of recurrent states; so the state space is
partitioned into at least one recurrent class and a set of transient states. -/
theorem theorem_3_1_1b [Nonempty S] (hP : P ∈ rowStochastic ℝ S) :
    (∃ i, mc_IsRecurrent P i) ∧
      ∀ i, mc_IsRecurrent P i → ∀ j, mc_Communicate P i j → mc_IsRecurrent P j := by
  refine ⟨?_, fun i hi j hij => hi.of_communicate hP hij⟩
  obtain ⟨i, -, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun i => (mc_consSet P i).card) Finset.univ_nonempty
  -- every state accessible from `i` has the same accessible set as `i`
  have hsub : ∀ j, mc_Accessible P i j → mc_consSet P j ⊆ mc_consSet P i := fun j hj k hk =>
    mc_mem_consSet.2 (hj.trans hP (mc_mem_consSet.1 hk))
  have heq : ∀ j, mc_Accessible P i j → mc_consSet P j = mc_consSet P i := fun j hj =>
    Finset.eq_of_subset_of_card_le (hsub j hj) (hmin j (Finset.mem_univ j))
  obtain ⟨k, hk⟩ := mc_exists_pos_entry hP i
  have hik : mc_Accessible P i k := mc_accessible_of_pos hk
  refine ⟨k, fun l hkl => ?_⟩
  have hil : mc_Accessible P i l := hik.trans hP hkl
  have hkk : k ∈ mc_consSet P l := by rw [heq l hil, mc_mem_consSet]; exact hik
  exact mc_mem_consSet.1 hkk

/-- **Theorem 3.1.1(c)** (Miao, p. 91): for an irreducible finite chain all states are
recurrent. -/
theorem theorem_3_1_1c (hP : P ∈ rowStochastic ℝ S) (hirr : mc_IsIrreducible P) (i : S) :
    mc_IsRecurrent P i := fun j _ => (mc_isIrreducible_iff hP).1 hirr j i

/-! ### A chain whose transient states do not form one class -/

/-- The chain `0 → 1 → 2 → 2` on three states. -/
def mc_chain012 : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 0; 0, 0, 1; 0, 0, 1]

/-- `mc_chain012` is a transition matrix. -/
theorem mc_chain012_mem : mc_chain012 ∈ rowStochastic ℝ (Fin 3) := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_⟩ <;> fin_cases i <;> try fin_cases j
  all_goals simp [mc_chain012, Fin.sum_univ_succ]

/-- Miao, proof of Theorem 3.1.1(b), p. 92, corrected: the transient states need not form one
class. In `0 → 1 → 2 → 2`, states `0` and `1` are transient but do not communicate. -/
theorem theorem_3_1_1b_proof_counterexample :
    mc_IsTransient mc_chain012 0 ∧ mc_IsTransient mc_chain012 1 ∧
      ¬ mc_Communicate mc_chain012 0 1 := by
  have hP := mc_chain012_mem
  have hc1 : mc_IsClosed mc_chain012 {j | j ≠ 0} := by
    intro i hi j hj
    simp only [Set.mem_ofPred_eq, not_not] at hi hj
    subst hj
    fin_cases i <;> simp_all [mc_chain012]
  have hc2 : mc_IsClosed mc_chain012 {2} := by
    intro i hi j hj
    simp only [Set.mem_singleton_iff] at hi hj
    subst hi
    fin_cases j <;> simp_all [mc_chain012]
  have h10 : ¬ mc_Accessible mc_chain012 1 0 := by
    rintro ⟨m, -, hm⟩
    rw [mc_pow_eq_zero_of_closed hc1 m (by decide) (by simp)] at hm
    exact lt_irrefl _ hm
  have h21 : ¬ mc_Accessible mc_chain012 2 1 := by
    rintro ⟨m, -, hm⟩
    rw [mc_pow_eq_zero_of_closed hc2 m (by simp) (by decide)] at hm
    exact lt_irrefl _ hm
  have h01 : mc_Accessible mc_chain012 0 1 := mc_accessible_of_pos (by simp [mc_chain012])
  have h12 : mc_Accessible mc_chain012 1 2 := mc_accessible_of_pos (by simp [mc_chain012])
  refine ⟨(mc_isTransient_iff 0).2 ⟨1, h01, h10⟩, (mc_isTransient_iff 1).2 ⟨2, h12, h21⟩, ?_⟩
  rintro (h | ⟨-, h⟩)
  · exact absurd h (by decide)
  · exact h10 h

/-! ### Theorem 3.1.2 -/

/-- **Theorem 3.1.2** (Miao, p. 93), finite chains: all states in the same class have the same
period. -/
theorem theorem_3_1_2 (hP : P ∈ rowStochastic ℝ S) {i j : S} (hij : mc_Communicate P i j) :
    mc_period P i = mc_period P j := by
  rcases hij with rfl | ⟨⟨r, hr, hr'⟩, ⟨s, hs, hs'⟩⟩
  · rfl
  refine mc_setGcd_eq_of_shift (mc_returnSet_isAddClosed hP i) (mc_returnSet_isAddClosed hP j)
    (n := r + s) (by omega) ⟨by omega, mc_pow_add_pos hP hr' hs'⟩ ?_ ?_ ?_
  · refine ⟨by omega, ?_⟩
    have := mc_pow_add_pos hP hs' hr'
    rwa [add_comm s r] at this
  · rintro t ⟨ht, ht'⟩
    refine ⟨by omega, ?_⟩
    have := mc_pow_add_pos hP (mc_pow_add_pos hP hr' ht') hs'
    rwa [show r + t + s = r + s + t by omega] at this
  · rintro t ⟨ht, ht'⟩
    refine ⟨by omega, ?_⟩
    have := mc_pow_add_pos hP (mc_pow_add_pos hP hs' ht') hr'
    rwa [show s + t + r = r + s + t by omega] at this

/-! ### Remark 3.1.1 and Exercise 1: ergodic sets -/

/-- The communication class of `i`, as a finite set. -/
noncomputable def mc_classOf (P : Matrix S S ℝ) (i : S) : Finset S := by
  classical exact Finset.univ.filter (mc_Communicate P i)

/-- Membership in `mc_classOf`. -/
theorem mc_mem_classOf {i j : S} : j ∈ mc_classOf P i ↔ mc_Communicate P i j := by
  classical simp [mc_classOf]

/-- The defining property of an ergodic set in Remark 3.1.1: `Σ_{j ∈ E} pᵢⱼ = 1` for `i ∈ E`. -/
def mc_SumsToOne (P : Matrix S S ℝ) (E : Finset S) : Prop := ∀ i ∈ E, ∑ j ∈ E, P i j = 1

/-- Remark 3.1.1 (Miao, p. 92) **as printed**: `E` has the property, and no proper subset of
`E` has it. -/
def mc_IsErgodicSetLiteral (P : Matrix S S ℝ) (E : Finset S) : Prop :=
  mc_SumsToOne P E ∧ ∀ F, F ⊂ E → ¬ mc_SumsToOne P F

/-- Remark 3.1.1 (Miao, p. 92), corrected: an **ergodic set** is a nonempty `E` with the property
of which no proper nonempty subset has the property. -/
def mc_IsErgodicSet (P : Matrix S S ℝ) (E : Finset S) : Prop :=
  E.Nonempty ∧ mc_SumsToOne P E ∧ ∀ F, F.Nonempty → F ⊂ E → ¬ mc_SumsToOne P F

omit [Fintype S] [DecidableEq S] in
/-- Remark 3.1.1 (Miao, p. 92) as printed is degenerate: the empty set is the only "ergodic set",
since `∅` is a proper subset of every nonempty set and has the property vacuously. -/
theorem remark_3_1_1_literal (E : Finset S) : mc_IsErgodicSetLiteral P E ↔ E = ∅ := by
  constructor
  · rintro ⟨-, h⟩
    by_contra hE
    exact h ∅ (Finset.nonempty_iff_ne_empty.2 hE).empty_ssubset (by simp [mc_SumsToOne])
  · rintro rfl
    exact ⟨by simp [mc_SumsToOne], fun F hF => absurd hF (Finset.not_ssubset_empty F)⟩

/-- For a transition matrix, `Σ_{j ∈ E} pᵢⱼ = 1` on `E` iff no arc leaves `E`. -/
theorem mc_sumsToOne_iff_closed (hP : P ∈ rowStochastic ℝ S) (E : Finset S) :
    mc_SumsToOne P E ↔ mc_IsClosed P (E : Set S) := by
  have hsplit : ∀ i, ∑ j ∈ E, P i j + ∑ j ∈ Eᶜ, P i j = 1 := fun i => by
    rw [Finset.sum_add_sum_compl, sum_row_of_mem_rowStochastic hP]
  constructor
  · intro h i hi j hj
    have h0 : ∑ j ∈ Eᶜ, P i j = 0 := by linarith [hsplit i, h i hi]
    exact (Finset.sum_eq_zero_iff_of_nonneg fun k _ => mc_entry_nonneg hP i k).1 h0 j
      (by simpa using hj)
  · intro h i hi
    have h0 : ∑ j ∈ Eᶜ, P i j = 0 :=
      Finset.sum_eq_zero fun j hj => h i hi j (by simpa using hj)
    linarith [hsplit i]

/-- The class of a recurrent state is closed. -/
theorem mc_classOf_closed (hP : P ∈ rowStochastic ℝ S) {i : S} (hi : mc_IsRecurrent P i) :
    mc_IsClosed P (mc_classOf P i : Set S) := by
  intro k hk j hj
  by_contra hne
  have hkj : mc_Accessible P k j :=
    mc_accessible_of_pos (lt_of_le_of_ne (mc_entry_nonneg hP k j) (Ne.symm hne))
  have hik : mc_Communicate P i k := mc_mem_classOf.1 hk
  have hij : mc_Accessible P i j := hik.accessible_trans hP hkj
  exact hj (mc_mem_classOf.2 (Or.inr ⟨hij, hi j hij⟩))

/-- **Exercise 1** (Miao, p. 113; Remark 3.1.1, p. 92): for finite chains, a set of states is an
ergodic set (in the corrected sense) iff it is a recurrent class. -/
theorem ex_3_1 (hP : P ∈ rowStochastic ℝ S) (E : Finset S) :
    mc_IsErgodicSet P E ↔ ∃ i, mc_IsRecurrent P i ∧ E = mc_classOf P i := by
  constructor
  · rintro ⟨⟨i, hi⟩, hsum, hmin⟩
    have hclosed := (mc_sumsToOne_iff_closed hP E).1 hsum
    -- for `k ∈ E`, the states reachable from `k` in `≥ 0` steps fill `E`
    have hfill : ∀ k ∈ E, ∀ j ∈ E, j = k ∨ mc_Accessible P k j := by
      intro k hk
      classical
      set R : Finset S := Finset.univ.filter (fun j => j = k ∨ mc_Accessible P k j) with hR
      have hRE : R ⊆ E := by
        intro j hj
        rw [hR, Finset.mem_filter] at hj
        rcases hj.2 with rfl | ⟨m, -, hm⟩
        · exact hk
        · by_contra hjE
          rw [mc_pow_eq_zero_of_closed hclosed m hk hjE] at hm
          exact lt_irrefl _ hm
      have hRc : mc_IsClosed P (R : Set S) := by
        intro l hl j hj
        by_contra hne
        have hlj : mc_Accessible P l j :=
          mc_accessible_of_pos (lt_of_le_of_ne (mc_entry_nonneg hP l j) (Ne.symm hne))
        apply hj
        rw [Finset.mem_coe, hR, Finset.mem_filter] at hl ⊢
        refine ⟨Finset.mem_univ j, Or.inr ?_⟩
        rcases hl.2 with rfl | hkl
        · exact hlj
        · exact hkl.trans hP hlj
      have hRne : R.Nonempty := ⟨k, by simp [hR]⟩
      have hReq : R = E := by
        by_contra hne
        exact hmin R hRne (Finset.ssubset_iff_subset_ne.2 ⟨hRE, hne⟩)
          ((mc_sumsToOne_iff_closed hP R).2 hRc)
      intro j hj
      rw [← hReq, hR, Finset.mem_filter] at hj
      exact hj.2
    have hrec : mc_IsRecurrent P i := by
      intro j hij
      have hjE : j ∈ E := by
        by_contra hjE
        obtain ⟨m, -, hm⟩ := hij
        rw [mc_pow_eq_zero_of_closed hclosed m hi hjE] at hm
        exact lt_irrefl _ hm
      rcases hfill j hjE i hi with rfl | h
      · exact hij
      · exact h
    refine ⟨i, hrec, Finset.ext fun j => ?_⟩
    rw [mc_mem_classOf]
    constructor
    · intro hj
      rcases hfill i hi j hj with rfl | h
      · exact Or.inl rfl
      · exact Or.inr ⟨h, hrec j h⟩
    · rintro (rfl | ⟨h, -⟩)
      · exact hi
      · by_contra hjE
        obtain ⟨m, -, hm⟩ := h
        rw [mc_pow_eq_zero_of_closed hclosed m hi hjE] at hm
        exact lt_irrefl _ hm
  · rintro ⟨i, hi, rfl⟩
    have hclosed := mc_classOf_closed hP hi
    refine ⟨⟨i, mc_mem_classOf.2 (Or.inl rfl)⟩, (mc_sumsToOne_iff_closed hP _).2 hclosed, ?_⟩
    rintro F ⟨k, hk⟩ hFE hF
    have hFc := (mc_sumsToOne_iff_closed hP F).1 hF
    apply (Finset.ssubset_iff_subset_ne.1 hFE).2
    refine Finset.Subset.antisymm hFE.1 fun j hj => ?_
    have hik : mc_Communicate P i k := mc_mem_classOf.1 (hFE.1 hk)
    have hij : mc_Communicate P i j := mc_mem_classOf.1 hj
    have hkj : mc_Communicate P k j :=
      (mc_communicate_equivalence hP).trans ((mc_communicate_equivalence hP).symm hik) hij
    rcases hkj with rfl | ⟨⟨m, -, hm⟩, -⟩
    · exact hk
    · by_contra hjF
      rw [mc_pow_eq_zero_of_closed hFc m hk hjF] at hm
      exact lt_irrefl _ hm

end Miao.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Finite Markov chains: stationary distributions, Theorems 3.1.3–3.1.4

Miao, §3.1.2, pp. 94–97.

* **Definition 3.1.5** (p. 94): `mc_IsStationary P μ`: `μ` is a distribution (row vector) with
  `μ = μP`; `mc_IsStationary.pow`: then `μ = μPᵗ`, and `μₜ = μ₀Pᵗ` is the distribution at `t`.
* **Theorem 3.1.3** (p. 94): if `p⁽ᵏ⁾ᵢⱼ > 0` for all `i, j` and one `k > 0`, there is a unique
  stationary distribution `μ`, `p⁽ᵗ⁾ᵢⱼ → μⱼ > 0` for all `i, j` (`theorem_3_1_3`). The steps of
  the proof are `theorem_3_1_3_mono` (`mₜ` increases), `theorem_3_1_3_anti` (`Mₜ` decreases),
  `theorem_3_1_3_min_step`, `theorem_3_1_3_max_step` (the two displayed inequalities, for the
  `k`-step matrix with `δ = minᵢⱼ p⁽ᵏ⁾ᵢⱼ`) and `theorem_3_1_3_gap_step`
  (`Δ_{t+k} ≤ (1 − 2δ)Δₜ`).
* **Theorem 3.1.4** (p. 96, `theorem_3_1_4`): a finite chain is irreducible and aperiodic iff
  there is `k₀ > 0` with `p⁽ᵏ⁾ᵢⱼ > 0` for all `i, j` and all `k ≥ k₀`.
* The general case (p. 97): `mc_exists_stationary` (every finite chain has a stationary
  distribution, from a limit point of the Cesàro averages of a row of `Pᵗ`);
  `mc_stationary_unique_of_irreducible`, `mc_stationary_pos_of_irreducible` (uniqueness and
  positivity under irreducibility); `stationary_p97_transient` (stationary distributions vanish
  on transient states); `stationary_p97_class` (each recurrent class carries a unique stationary
  distribution `mc_classDist`, supported by the class); `stationary_p97_decomposition` (every
  stationary distribution is a convex combination of these); `stationary_p97_infinite` (with two
  recurrent classes there are infinitely many stationary distributions).

**Corrections.**
* Theorem 3.1.3 needs one `k` for all pairs `i, j` (as its proof uses). If `k` may depend on
  `i, j` the conclusion fails: `theorem_3_1_3_counterexample` (the two-state swap, which is
  Example 3.1.2 with `1 × 1` blocks, has `p⁽ᵏ⁾ᵢⱼ > 0` for some `k` for every pair, but `p⁽ᵗ⁾₀₀`
  does not converge).
* After Theorems 3.1.3 and 3.1.4 the book says that Example 3.1.2 has no stationary distribution.
  This is false: every finite chain has one (`mc_exists_stationary`), and the swap has
  `(1/2, 1/2)` (`theorem_3_1_3_counterexample`); what fails for Example 3.1.2 is the convergence
  of `Pᵗ` (`example_3_1_2_stationary`, `example_3_1_2_not_tendsto` in `ChainExamples`).
* Theorem 3.1.3 is stated for a nonempty state space (otherwise no distribution exists).
* The proof's bound `Δₜ ≤ (1 − 2δ)ᵗ` is used here in the form `Δ_{nk} ≤ (1 − δ)ⁿ`, which follows
  from the displayed step and needs no case distinction on `δ ≤ 1/2`.
-/

namespace Miao.MarkovProcesses

open Matrix Filter Topology

variable {S : Type*} [Fintype S] [DecidableEq S] {P : Matrix S S ℝ}

/-! ### Definition 3.1.5 -/

/-- **Definition 3.1.5** (Miao, p. 94): `μ` is an **invariant** (**stationary**) distribution of
the chain with transition matrix `P`: a distribution (row vector) with `μ = μP`. -/
def mc_IsStationary (P : Matrix S S ℝ) (μ : S → ℝ) : Prop :=
  (∀ i, 0 ≤ μ i) ∧ ∑ i, μ i = 1 ∧ μ ᵥ* P = μ

omit [DecidableEq S] in
/-- The entries of `v ᵥ* M`. -/
theorem mc_vecMul_apply (v : S → ℝ) (M : Matrix S S ℝ) (j : S) :
    (v ᵥ* M) j = ∑ i, v i * M i j := rfl

/-- Miao, p. 94: the distribution in period `t` is `μₜ = μ₀Pᵗ`; it satisfies
`μₜ₊₁ = μₜP`. -/
theorem mc_dist_succ (μ₀ : S → ℝ) (t : ℕ) : μ₀ ᵥ* P ^ (t + 1) = (μ₀ ᵥ* P ^ t) ᵥ* P := by
  rw [vecMul_vecMul, pow_succ]

/-- A stationary distribution is invariant under every power: `μ = μPᵗ`. -/
theorem mc_IsStationary.pow {μ : S → ℝ} (hμ : mc_IsStationary P μ) (t : ℕ) :
    μ ᵥ* P ^ t = μ := by
  induction t with
  | zero => simp
  | succ t ih => rw [mc_dist_succ, ih, hμ.2.2]

/-- The entries of a stationary distribution: `μⱼ = Σᵢ μᵢ p⁽ᵗ⁾ᵢⱼ`. -/
theorem mc_IsStationary.apply_eq {μ : S → ℝ} (hμ : mc_IsStationary P μ) (t : ℕ) (j : S) :
    μ j = ∑ i, μ i * (P ^ t) i j := by
  rw [← mc_vecMul_apply, hμ.pow t]

/-- `μⱼ ≥ μᵢ p⁽ᵗ⁾ᵢⱼ` for a stationary distribution. -/
theorem mc_IsStationary.le_apply (hP : P ∈ rowStochastic ℝ S) {μ : S → ℝ}
    (hμ : mc_IsStationary P μ) (t : ℕ) (i j : S) : μ i * (P ^ t) i j ≤ μ j := by
  rw [hμ.apply_eq t j]
  exact Finset.single_le_sum (f := fun l => μ l * (P ^ t) l j)
    (fun l _ => mul_nonneg (hμ.1 l) (mc_pow_nonneg hP t l j)) (Finset.mem_univ i)

omit [DecidableEq S] in
/-- A convex combination of stationary distributions is stationary. -/
theorem mc_IsStationary.convex {μ ν : S → ℝ} (hμ : mc_IsStationary P μ)
    (hν : mc_IsStationary P ν) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    mc_IsStationary P (t • μ + (1 - t) • ν) := by
  refine ⟨fun i => ?_, ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ht0 (hμ.1 i)) (mul_nonneg (by linarith) (hν.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hμ.2.1, hν.2.1]
    ring
  · rw [add_vecMul, smul_vecMul, smul_vecMul, hμ.2.2, hν.2.2]

omit [DecidableEq S] in
/-- A distribution has a state of positive mass. -/
theorem mc_exists_pos_of_sum_eq_one {μ : S → ℝ} (h : ∑ i, μ i = 1) : ∃ i, 0 < μ i := by
  by_contra hne
  push Not at hne
  have : ∑ i, μ i ≤ 0 := Finset.sum_nonpos fun i _ => hne i
  linarith

/-! ### Theorem 3.1.3 -/

/-- `m_t = minᵢ p⁽ᵗ⁾ᵢⱼ`, the minimum of column `j` of `Pᵗ` (Miao, p. 94). -/
noncomputable def mc_colMin [Nonempty S] (P : Matrix S S ℝ) (j : S) (t : ℕ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun i => (P ^ t) i j

/-- `M_t = maxᵢ p⁽ᵗ⁾ᵢⱼ`, the maximum of column `j` of `Pᵗ` (Miao, p. 94). -/
noncomputable def mc_colMax [Nonempty S] (P : Matrix S S ℝ) (j : S) (t : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => (P ^ t) i j

omit [Fintype S] [DecidableEq S] in
/-- The minimum is attained. -/
theorem mc_colMin_le [Fintype S] [DecidableEq S] [Nonempty S] (j : S) (t : ℕ) (i : S) :
    mc_colMin P j t ≤ (P ^ t) i j :=
  Finset.inf'_le _ (Finset.mem_univ i)

/-- `p⁽ᵗ⁾ᵢⱼ ≤ M_t`. -/
theorem mc_le_colMax [Nonempty S] (j : S) (t : ℕ) (i : S) : (P ^ t) i j ≤ mc_colMax P j t :=
  Finset.le_sup' (fun i => (P ^ t) i j) (Finset.mem_univ i)

/-- `M_t ≤ 1`. -/
theorem mc_colMax_le_one [Nonempty S] (hP : P ∈ rowStochastic ℝ S) (j : S) (t : ℕ) :
    mc_colMax P j t ≤ 1 :=
  Finset.sup'_le _ _ fun i _ => mc_pow_le_one hP t i j

/-- `m_t ≥ 0`. -/
theorem mc_colMin_nonneg [Nonempty S] (hP : P ∈ rowStochastic ℝ S) (j : S) (t : ℕ) :
    0 ≤ mc_colMin P j t :=
  Finset.le_inf' _ _ fun i _ => mc_pow_nonneg hP t i j

/-- A weighted average with stochastic weights lies above a lower bound. -/
theorem mc_avg_ge {Q : Matrix S S ℝ} (hQ : Q ∈ rowStochastic ℝ S) (i : S) {x : S → ℝ} {a : ℝ}
    (h : ∀ v, a ≤ x v) : a ≤ ∑ v, Q i v * x v := by
  calc a = ∑ v, Q i v * a := by rw [← Finset.sum_mul, sum_row_of_mem_rowStochastic hQ, one_mul]
    _ ≤ ∑ v, Q i v * x v := Finset.sum_le_sum fun v _ =>
        mul_le_mul_of_nonneg_left (h v) (nonneg_of_mem_rowStochastic hQ)

/-- A weighted average with stochastic weights lies below an upper bound. -/
theorem mc_avg_le {Q : Matrix S S ℝ} (hQ : Q ∈ rowStochastic ℝ S) (i : S) {x : S → ℝ} {a : ℝ}
    (h : ∀ v, x v ≤ a) : ∑ v, Q i v * x v ≤ a := by
  calc ∑ v, Q i v * x v ≤ ∑ v, Q i v * a := Finset.sum_le_sum fun v _ =>
        mul_le_mul_of_nonneg_left (h v) (nonneg_of_mem_rowStochastic hQ)
    _ = a := by rw [← Finset.sum_mul, sum_row_of_mem_rowStochastic hQ, one_mul]

/-- Miao, proof of Theorem 3.1.3, step 1, p. 95: the column minima `mₜ` increase. -/
theorem theorem_3_1_3_mono [Nonempty S] (hP : P ∈ rowStochastic ℝ S) (j : S) (t : ℕ) :
    mc_colMin P j t ≤ mc_colMin P j (t + 1) := by
  refine Finset.le_inf' _ _ fun i _ => ?_
  rw [pow_succ', mul_apply]
  exact mc_avg_ge hP i fun v => mc_colMin_le j t v

/-- Miao, proof of Theorem 3.1.3, step 2, p. 95: the column maxima `Mₜ` decrease. -/
theorem theorem_3_1_3_anti [Nonempty S] (hP : P ∈ rowStochastic ℝ S) (j : S) (t : ℕ) :
    mc_colMax P j (t + 1) ≤ mc_colMax P j t := by
  refine Finset.sup'_le _ _ fun i _ => ?_
  rw [pow_succ', mul_apply]
  exact mc_avg_le hP i fun v => mc_le_colMax j t v

/-- Miao, proof of Theorem 3.1.3, p. 95, first display: if every entry of `Q = Pᵏ` is at least
`δ`, then `m_{t+k} ≥ δMₜ + (1 − δ)mₜ`. -/
theorem theorem_3_1_3_min_step [Nonempty S] (hP : P ∈ rowStochastic ℝ S) (j : S) {k : ℕ}
    {δ : ℝ} (hδ : ∀ i v, δ ≤ (P ^ k) i v) (t : ℕ) :
    δ * mc_colMax P j t + (1 - δ) * mc_colMin P j t ≤ mc_colMin P j (k + t) := by
  obtain ⟨l, -, hl⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty fun i => (P ^ t) i j
  refine Finset.le_inf' _ _ fun i _ => ?_
  have hQ := mc_pow_mem hP k
  set m := mc_colMin P j t
  set x : S → ℝ := fun v => (P ^ t) v j
  have hx : ∀ v, m ≤ x v := fun v => mc_colMin_le j t v
  have hsum : ∑ v, (P ^ k) i v * x v = m + ∑ v, (P ^ k) i v * (x v - m) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      sum_row_of_mem_rowStochastic hQ, one_mul]
    ring
  have hsingle : (P ^ k) i l * (x l - m) ≤ ∑ v, (P ^ k) i v * (x v - m) :=
    Finset.single_le_sum (f := fun v => (P ^ k) i v * (x v - m))
      (fun v _ => mul_nonneg (mc_pow_nonneg hP k i v) (sub_nonneg.2 (hx v)))
      (Finset.mem_univ l)
  have hxl : x l = mc_colMax P j t := hl.symm
  have hδl : δ * (x l - m) ≤ (P ^ k) i l * (x l - m) :=
    mul_le_mul_of_nonneg_right (hδ i l) (sub_nonneg.2 (hx l))
  rw [pow_add, mul_apply]
  change _ ≤ ∑ v, (P ^ k) i v * x v
  rw [hsum, ← hxl]
  nlinarith

/-- Miao, proof of Theorem 3.1.3, p. 95, second display: `M_{t+k} ≤ δmₜ + (1 − δ)Mₜ`. -/
theorem theorem_3_1_3_max_step [Nonempty S] (hP : P ∈ rowStochastic ℝ S) (j : S) {k : ℕ}
    {δ : ℝ} (hδ : ∀ i v, δ ≤ (P ^ k) i v) (t : ℕ) :
    mc_colMax P j (k + t) ≤ δ * mc_colMin P j t + (1 - δ) * mc_colMax P j t := by
  obtain ⟨l, -, hl⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty fun i => (P ^ t) i j
  refine Finset.sup'_le _ _ fun i _ => ?_
  have hQ := mc_pow_mem hP k
  set M := mc_colMax P j t
  set x : S → ℝ := fun v => (P ^ t) v j
  have hx : ∀ v, x v ≤ M := fun v => mc_le_colMax j t v
  have hsum : ∑ v, (P ^ k) i v * x v = M - ∑ v, (P ^ k) i v * (M - x v) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      sum_row_of_mem_rowStochastic hQ, one_mul]
    ring
  have hsingle : (P ^ k) i l * (M - x l) ≤ ∑ v, (P ^ k) i v * (M - x v) :=
    Finset.single_le_sum (f := fun v => (P ^ k) i v * (M - x v))
      (fun v _ => mul_nonneg (mc_pow_nonneg hP k i v) (sub_nonneg.2 (hx v)))
      (Finset.mem_univ l)
  have hxl : x l = mc_colMin P j t := hl.symm
  have hδl : δ * (M - x l) ≤ (P ^ k) i l * (M - x l) :=
    mul_le_mul_of_nonneg_right (hδ i l) (sub_nonneg.2 (hx l))
  rw [pow_add, mul_apply]
  change ∑ v, (P ^ k) i v * x v ≤ _
  rw [hsum, ← hxl]
  nlinarith

/-- Miao, proof of Theorem 3.1.3, p. 95: `Δ_{t+k} ≤ (1 − 2δ)Δₜ`, `Δₜ = Mₜ − mₜ`. -/
theorem theorem_3_1_3_gap_step [Nonempty S] (hP : P ∈ rowStochastic ℝ S) (j : S) {k : ℕ}
    {δ : ℝ} (hδ : ∀ i v, δ ≤ (P ^ k) i v) (t : ℕ) :
    mc_colMax P j (k + t) - mc_colMin P j (k + t) ≤
      (1 - 2 * δ) * (mc_colMax P j t - mc_colMin P j t) := by
  have h1 := theorem_3_1_3_min_step hP j hδ t
  have h2 := theorem_3_1_3_max_step hP j hδ t
  nlinarith

/-- **Theorem 3.1.3** (Miao, p. 94): if `p⁽ᵏ⁾ᵢⱼ > 0` for all `i, j` and some (one) `k > 0`, the
chain has a unique stationary distribution `μ`, and `p⁽ᵗ⁾ᵢⱼ → μⱼ > 0` for all `i, j`. -/
theorem theorem_3_1_3 [Nonempty S] (hP : P ∈ rowStochastic ℝ S)
    (hk : ∃ k, 0 < k ∧ ∀ i j, 0 < (P ^ k) i j) :
    ∃ μ, mc_IsStationary P μ ∧ (∀ j, 0 < μ j) ∧
      (∀ i j, Tendsto (fun t => (P ^ t) i j) atTop (𝓝 (μ j))) ∧
      ∀ ν, mc_IsStationary P ν → ν = μ := by
  obtain ⟨k, hk0, hkpos⟩ := hk
  set δ := (Finset.univ : Finset (S × S)).inf' Finset.univ_nonempty
    (fun p => (P ^ k) p.1 p.2) with hδdef
  have hδ : ∀ i v, δ ≤ (P ^ k) i v := fun i v =>
    Finset.inf'_le (fun p : S × S => (P ^ k) p.1 p.2) (Finset.mem_univ (i, v))
  have hδpos : 0 < δ := (Finset.lt_inf'_iff _).2 fun p _ => hkpos p.1 p.2
  have i₀ : S := Classical.arbitrary S
  have hδ1 : δ ≤ 1 := (hδ i₀ i₀).trans (mc_pow_le_one hP k i₀ i₀)
  -- the limit of each column
  have hlim : ∀ j, ∃ a, 0 < a ∧ ∀ i, Tendsto (fun t => (P ^ t) i j) atTop (𝓝 a) := by
    intro j
    have hmono : Monotone (mc_colMin P j) := monotone_nat_of_le_succ (theorem_3_1_3_mono hP j)
    have hanti : Antitone (mc_colMax P j) := antitone_nat_of_succ_le (theorem_3_1_3_anti hP j)
    have hbdd : BddAbove (Set.range (mc_colMin P j)) :=
      ⟨1, by rintro _ ⟨t, rfl⟩; exact (mc_colMin_le j t i₀).trans (mc_pow_le_one hP t i₀ j)⟩
    have hbdd' : BddBelow (Set.range (mc_colMax P j)) :=
      ⟨0, by rintro _ ⟨t, rfl⟩; exact (mc_pow_nonneg hP t i₀ j).trans (mc_le_colMax j t i₀)⟩
    set a := ⨆ t, mc_colMin P j t
    set b := ⨅ t, mc_colMax P j t
    have ha := tendsto_atTop_ciSup hmono hbdd
    have hb := tendsto_atTop_ciInf hanti hbdd'
    have hmM : ∀ t t', mc_colMin P j t ≤ mc_colMax P j t' := fun t t' =>
      (hmono (le_max_left t t')).trans (((mc_colMin_le j _ i₀).trans
        (mc_le_colMax j _ i₀)).trans (hanti (le_max_right t t')))
    have hab : a ≤ b := le_ciInf fun t' => ciSup_le fun t => hmM t t'
    have hgap : ∀ n, mc_colMax P j (n * k) - mc_colMin P j (n * k) ≤ (1 - δ) ^ n := by
      intro n
      induction n with
      | zero =>
        simp only [zero_mul, pow_zero]
        linarith [mc_colMax_le_one hP j 0, mc_colMin_nonneg hP j 0]
      | succ n ih =>
        have hstep := theorem_3_1_3_gap_step hP j hδ (n * k)
        have hΔ : 0 ≤ mc_colMax P j (n * k) - mc_colMin P j (n * k) :=
          sub_nonneg.2 (hmM _ _)
        rw [show (n + 1) * k = k + n * k by ring, pow_succ]
        calc _ ≤ (1 - 2 * δ) * (mc_colMax P j (n * k) - mc_colMin P j (n * k)) := hstep
          _ ≤ (1 - δ) * (mc_colMax P j (n * k) - mc_colMin P j (n * k)) := by nlinarith
          _ ≤ (1 - δ) * (1 - δ) ^ n := mul_le_mul_of_nonneg_left ih (by linarith)
          _ = (1 - δ) ^ n * (1 - δ) := mul_comm _ _
    have hba : b - a ≤ 0 := by
      refine le_of_tendsto_of_tendsto' tendsto_const_nhds
        (tendsto_pow_atTop_nhds_zero_of_lt_one (r := 1 - δ) (by linarith) (by linarith))
        fun n => ?_
      have h1 : b ≤ mc_colMax P j (n * k) := ciInf_le hbdd' (n * k)
      have h2 : mc_colMin P j (n * k) ≤ a := le_ciSup hbdd (n * k)
      linarith [hgap n]
    have hb' : Tendsto (mc_colMax P j) atTop (𝓝 a) := by
      rwa [show a = b by linarith]
    refine ⟨a, ?_, fun i => tendsto_of_tendsto_of_tendsto_of_le_of_le ha hb'
      (fun t => mc_colMin_le j t i) (fun t => mc_le_colMax j t i)⟩
    have : δ ≤ mc_colMin P j k := Finset.le_inf' _ _ fun i _ => hδ i j
    exact hδpos.trans_le (this.trans (le_ciSup hbdd k))
  choose μ hμpos hμlim using hlim
  have hsum : ∑ j, μ j = 1 := by
    have h := tendsto_finsetSum Finset.univ fun j _ => hμlim j i₀
    simp only [mc_pow_row_sum hP] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  have hstat : mc_IsStationary P μ := by
    refine ⟨fun j => (hμpos j).le, hsum, funext fun j => ?_⟩
    rw [mc_vecMul_apply]
    have h1 : Tendsto (fun t => ∑ v, (P ^ t) i₀ v * P v j) atTop (𝓝 (∑ v, μ v * P v j)) :=
      tendsto_finsetSum _ fun v _ => (hμlim v i₀).mul_const _
    have h2 : Tendsto (fun t => (P ^ (t + 1)) i₀ j) atTop (𝓝 (μ j)) :=
      (hμlim j i₀).comp (tendsto_add_atTop_nat 1)
    simp only [pow_succ, mul_apply] at h2
    exact tendsto_nhds_unique h1 h2
  refine ⟨μ, hstat, hμpos, fun i j => hμlim j i, fun ν hν => funext fun j => ?_⟩
  have h1 : Tendsto (fun t => ∑ i, ν i * (P ^ t) i j) atTop (𝓝 (∑ i, ν i * μ j)) :=
    tendsto_finsetSum _ fun i _ => (hμlim j i).const_mul _
  rw [← Finset.sum_mul, hν.2.1, one_mul] at h1
  have h2 : (fun t => ∑ i, ν i * (P ^ t) i j) = fun _ => ν j :=
    funext fun t => (hν.apply_eq t j).symm
  rw [h2] at h1
  exact tendsto_nhds_unique tendsto_const_nhds h1

/-! ### The two-state swap -/

/-- The two-state swap `[0 1; 1 0]` (Example 3.1.2 with `1 × 1` blocks). -/
def mc_swap : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- The swap is a transition matrix. -/
theorem mc_swap_mem : mc_swap ∈ rowStochastic ℝ (Fin 2) := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_⟩ <;> fin_cases i <;> try fin_cases j
  all_goals simp [mc_swap, Fin.sum_univ_succ]

/-- `swap² = 1`. -/
theorem mc_swap_sq : mc_swap ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mc_swap, sq, mul_apply, Fin.sum_univ_succ]

/-- Even powers of the swap are the identity. -/
theorem mc_swap_pow_even (n : ℕ) : mc_swap ^ (2 * n) = 1 := by
  rw [pow_mul, mc_swap_sq, one_pow]

/-- Odd powers of the swap are the swap. -/
theorem mc_swap_pow_odd (n : ℕ) : mc_swap ^ (2 * n + 1) = mc_swap := by
  rw [pow_succ, mc_swap_pow_even, one_mul]

/-- Miao, Theorem 3.1.3, p. 94, **counterexample** to the reading in which `k` may depend on
`i, j`: for the swap every pair has `p⁽ᵏ⁾ᵢⱼ > 0` for some `k > 0`, but `p⁽ᵗ⁾₀₀` alternates
`1, 0, 1, …` and does not converge. The swap still has the stationary distribution
`(1/2, 1/2)`, contradicting the remark after Theorem 3.1.3 that Example 3.1.2 has none. -/
theorem theorem_3_1_3_counterexample :
    (∀ i j, ∃ k, 0 < k ∧ 0 < (mc_swap ^ k) i j) ∧
      ¬ (∃ L, Tendsto (fun t => (mc_swap ^ t) 0 0) atTop (𝓝 L)) ∧
      mc_IsStationary mc_swap (fun _ => 1 / 2) := by
  refine ⟨fun i j => ?_, ?_, ?_⟩
  · by_cases hij : i = j
    · refine ⟨2, by norm_num, ?_⟩
      rw [mc_swap_sq, hij]; simp
    · refine ⟨1, by norm_num, ?_⟩
      fin_cases i <;> fin_cases j <;> simp_all [mc_swap]
  · rintro ⟨L, hL⟩
    have h2 : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
      tendsto_atTop_mono (fun n => by dsimp only [id]; omega) tendsto_id
    have h3 : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
      tendsto_atTop_mono (fun n => by dsimp only [id]; omega) tendsto_id
    have he := hL.comp h2
    have ho := hL.comp h3
    simp only [Function.comp_def, mc_swap_pow_even, mc_swap_pow_odd] at he ho
    have h1 : L = 1 := tendsto_nhds_unique he (by simp)
    have h0 : L = 0 := tendsto_nhds_unique ho (by simp [mc_swap])
    linarith
  · refine ⟨fun _ => by norm_num, by norm_num, funext fun j => ?_⟩
    fin_cases j <;> simp [mc_vecMul_apply, mc_swap, Fin.sum_univ_succ]

/-! ### Existence: every finite chain has a stationary distribution -/

/-- `(P⁰)ᵢⱼ = 0` and `(Pᵗ)ᵢⱼ = 0` for all `t ≥ 1` when `j ≠ i` is not accessible from `i`. -/
theorem mc_pow_eq_zero_of_not_accessible (hP : P ∈ rowStochastic ℝ S) {i j : S} (hij : j ≠ i)
    (hacc : ¬ mc_Accessible P i j) (t : ℕ) : (P ^ t) i j = 0 := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [Ne.symm hij]
  · exact le_antisymm (not_lt.1 fun h => hacc ⟨t, ht, h⟩) (mc_pow_nonneg hP t i j)

/-- Miao, p. 97 (existence, used for every recurrent class): every finite chain has a stationary
distribution. More precisely, for each state `i` there is one charging only `i` and the states
accessible from `i`: a limit point of the Cesàro averages `(1/(n+1)) Σ_{t ≤ n} p⁽ᵗ⁾ᵢ·`. -/
theorem mc_exists_stationary [Nonempty S] (hP : P ∈ rowStochastic ℝ S) (i : S) :
    ∃ μ, mc_IsStationary P μ ∧ ∀ j, j ≠ i → ¬ mc_Accessible P i j → μ j = 0 := by
  set c : ℕ → S → ℝ := fun n j => (1 / ((n : ℝ) + 1)) * ∑ t ∈ Finset.range (n + 1), (P ^ t) i j
    with hc
  have hn1 : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hcnn : ∀ n j, 0 ≤ c n j := fun n j => mul_nonneg (by have := hn1 n; positivity)
    (Finset.sum_nonneg fun t _ => mc_pow_nonneg hP t i j)
  have hsumc : ∀ n, ∑ j, c n j = 1 := by
    intro n
    simp only [hc, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mc_pow_row_sum hP, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    field_simp [(hn1 n).ne']
    push_cast; ring
  have hcle : ∀ n j, c n j ≤ 1 := fun n j => by
    rw [← hsumc n]
    exact Finset.single_le_sum (fun l _ => hcnn n l) (Finset.mem_univ j)
  -- `c_n P − c_n = (p⁽ⁿ⁺¹⁾ᵢⱼ − p⁽⁰⁾ᵢⱼ)/(n+1)`
  have hdiff : ∀ n j, (c n ᵥ* P) j - c n j =
      (1 / ((n : ℝ) + 1)) * ((P ^ (n + 1)) i j - (P ^ 0) i j) := by
    intro n j
    have hshift : ∀ t, ∑ v, (P ^ t) i v * P v j = (P ^ (t + 1)) i j := fun t => by
      rw [pow_succ, mul_apply]
    change ∑ v, c n v * P v j - c n j = _
    simp only [hc, mul_assoc, ← Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [hshift, ← mul_sub]
    rw [← Finset.sum_sub_distrib, Finset.sum_range_sub (fun t => (P ^ t) i j)]
  have hdiff_le : ∀ n j, |(c n ᵥ* P) j - c n j| ≤ 1 / ((n : ℝ) + 1) := by
    intro n j
    rw [hdiff, abs_mul, abs_of_pos (by have := hn1 n; positivity)]
    have h1 := mc_pow_nonneg hP (n + 1) i j
    have h2 := mc_pow_le_one hP (n + 1) i j
    have h3 := mc_pow_nonneg hP 0 i j
    have h4 := mc_pow_le_one hP 0 i j
    have : |(P ^ (n + 1)) i j - (P ^ 0) i j| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    calc 1 / ((n : ℝ) + 1) * |(P ^ (n + 1)) i j - (P ^ 0) i j| ≤ 1 / ((n : ℝ) + 1) * 1 :=
          mul_le_mul_of_nonneg_left this (by have := hn1 n; positivity)
      _ = 1 / ((n : ℝ) + 1) := mul_one _
  have hK : IsCompact (Set.univ.pi fun _ : S => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨μ, -, φ, hφ, hlim⟩ := hK.tendsto_subseq (x := c)
    fun n => Set.mem_univ_pi.2 fun j => ⟨hcnn n j, hcle n j⟩
  have hcoord : ∀ j, Tendsto (fun n => c (φ n) j) atTop (𝓝 (μ j)) := fun j =>
    (continuous_apply j).continuousAt.tendsto.comp hlim
  refine ⟨μ, ⟨fun j => ge_of_tendsto' (hcoord j) fun n => hcnn _ j, ?_, funext fun j => ?_⟩, ?_⟩
  · exact tendsto_nhds_unique (tendsto_finsetSum _ fun j _ => hcoord j)
      (by simp only [hsumc]; exact tendsto_const_nhds)
  · have h1 : Tendsto (fun n => (c (φ n) ᵥ* P) j) atTop (𝓝 ((μ ᵥ* P) j)) := by
      simp only [mc_vecMul_apply]
      exact tendsto_finsetSum _ fun v _ => (hcoord v).mul_const _
    have hinv : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
      simpa [Function.comp_def] using this
    have h2 : Tendsto (fun n => (c (φ n) ᵥ* P) j - c (φ n) j) atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact hdiff_le (φ n) j) hinv
    have h3 := h2.add (hcoord j)
    simp only [sub_add_cancel, zero_add] at h3
    exact tendsto_nhds_unique h1 h3
  · intro j hji hacc
    have h0 : ∀ n, c n j = 0 := fun n => by
      simp [hc, mc_pow_eq_zero_of_not_accessible hP hji hacc]
    exact tendsto_nhds_unique (hcoord j) (by simp only [h0]; exact tendsto_const_nhds)

/-! ### Positivity and uniqueness on a communicating class -/

/-- A stationary distribution carried by a set `C` of mutually communicating states charges
every state of `C`. -/
theorem mc_stationary_pos_of (hP : P ∈ rowStochastic ℝ S) {C : Finset S}
    (hC : ∀ i ∈ C, ∀ j ∈ C, mc_Communicate P i j) {μ : S → ℝ} (hμ : mc_IsStationary P μ)
    (hsupp : ∀ j ∉ C, μ j = 0) : ∀ j ∈ C, 0 < μ j := by
  obtain ⟨k, hk⟩ := mc_exists_pos_of_sum_eq_one hμ.2.1
  have hkC : k ∈ C := by
    by_contra h
    rw [hsupp k h] at hk
    exact lt_irrefl _ hk
  intro j hj
  rcases hC k hkC j hj with rfl | ⟨⟨m, -, hm⟩, -⟩
  · exact hk
  · exact (mul_pos hk hm).trans_le (hμ.le_apply hP m k j)

/-- Two stationary distributions carried by a set `C` of mutually communicating states are
equal (if `w = μ − cν ≥ 0` is invariant and vanishes somewhere in `C`, it vanishes on `C`). -/
theorem mc_stationary_unique_of (hP : P ∈ rowStochastic ℝ S) {C : Finset S}
    (hC : ∀ i ∈ C, ∀ j ∈ C, mc_Communicate P i j) {μ ν : S → ℝ} (hμ : mc_IsStationary P μ)
    (hν : mc_IsStationary P ν) (hμs : ∀ j ∉ C, μ j = 0) (hνs : ∀ j ∉ C, ν j = 0) : μ = ν := by
  have hνpos := mc_stationary_pos_of hP hC hν hνs
  have hμpos := mc_stationary_pos_of hP hC hμ hμs
  have hCne : C.Nonempty := by
    obtain ⟨k, hk⟩ := mc_exists_pos_of_sum_eq_one hμ.2.1
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [hμs k (by simp [h])] at hk
    exact lt_irrefl _ hk
  set c := C.inf' hCne fun j => μ j / ν j
  obtain ⟨j₀, hj₀, hc⟩ := Finset.exists_mem_eq_inf' hCne fun j => μ j / ν j
  set w := μ - c • ν
  have hw_nn : ∀ j, 0 ≤ w j := by
    intro j
    by_cases hj : j ∈ C
    · have h1 : c ≤ μ j / ν j := Finset.inf'_le _ hj
      rw [le_div_iff₀ (hνpos j hj)] at h1
      simp only [w, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    · simp [w, hμs j hj, hνs j hj]
  have hw_inv : ∀ t, w ᵥ* P ^ t = w := fun t => by
    rw [sub_vecMul, smul_vecMul, hμ.pow, hν.pow]
  have hc' : c = μ j₀ / ν j₀ := hc
  have hw0 : w j₀ = 0 := by
    simp only [w, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hc', div_mul_cancel₀ _ (hνpos j₀ hj₀).ne']
    ring
  have hwC : ∀ i, w i = 0 := by
    intro i
    by_cases hi : i ∈ C
    · rcases hC i hi j₀ hj₀ with rfl | ⟨⟨m, -, hm⟩, -⟩
      · exact hw0
      · have hle : w i * (P ^ m) i j₀ ≤ w j₀ := by
          calc w i * (P ^ m) i j₀ ≤ ∑ l, w l * (P ^ m) l j₀ :=
                Finset.single_le_sum (f := fun l => w l * (P ^ m) l j₀)
                  (fun l _ => mul_nonneg (hw_nn l) (mc_pow_nonneg hP m l j₀))
                  (Finset.mem_univ i)
            _ = w j₀ := by rw [← mc_vecMul_apply, hw_inv m]
        rw [hw0] at hle
        refine le_antisymm ?_ (hw_nn i)
        by_contra h
        push Not at h
        linarith [mul_pos h hm]
    · simp [w, hμs i hi, hνs i hi]
  have hμeq : ∀ j, μ j = c * ν j := fun j => by
    have := hwC j
    simp only [w, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith
  have hc1 : c = 1 := by
    have := hμ.2.1
    simp only [hμeq, ← Finset.mul_sum, hν.2.1, mul_one] at this
    exact this
  funext j
  rw [hμeq, hc1, one_mul]

/-- Miao, p. 97: an irreducible finite chain has at most one stationary distribution. -/
theorem mc_stationary_unique_of_irreducible (hP : P ∈ rowStochastic ℝ S)
    (hirr : mc_IsIrreducible P) {μ ν : S → ℝ} (hμ : mc_IsStationary P μ)
    (hν : mc_IsStationary P ν) : μ = ν :=
  mc_stationary_unique_of hP (C := Finset.univ) (fun i _ j _ => hirr i j) hμ hν
    (fun j hj => absurd (Finset.mem_univ j) hj) (fun j hj => absurd (Finset.mem_univ j) hj)

/-- The stationary distribution of an irreducible finite chain charges every state. -/
theorem mc_stationary_pos_of_irreducible (hP : P ∈ rowStochastic ℝ S)
    (hirr : mc_IsIrreducible P) {μ : S → ℝ} (hμ : mc_IsStationary P μ) (j : S) : 0 < μ j :=
  mc_stationary_pos_of hP (C := Finset.univ) (fun i _ j _ => hirr i j) hμ
    (fun j hj => absurd (Finset.mem_univ j) hj) j (Finset.mem_univ j)

/-- Miao, p. 97: an irreducible finite chain has a unique stationary distribution, and it is
positive. -/
theorem mc_irreducible_stationary [Nonempty S] (hP : P ∈ rowStochastic ℝ S)
    (hirr : mc_IsIrreducible P) :
    ∃ μ, mc_IsStationary P μ ∧ (∀ j, 0 < μ j) ∧ ∀ ν, mc_IsStationary P ν → ν = μ := by
  obtain ⟨μ, hμ, -⟩ := mc_exists_stationary hP (Classical.arbitrary S)
  exact ⟨μ, hμ, mc_stationary_pos_of_irreducible hP hirr hμ,
    fun ν hν => mc_stationary_unique_of_irreducible hP hirr hν hμ⟩

/-! ### Stationary distributions of a general finite chain (Miao, p. 97) -/

/-- Miao, p. 97: a stationary distribution vanishes on transient states. -/
theorem stationary_p97_transient (hP : P ∈ rowStochastic ℝ S) {μ : S → ℝ}
    (hμ : mc_IsStationary P μ) {i : S} (hi : mc_IsTransient P i) : μ i = 0 := by
  classical
  obtain ⟨j, hij, hji⟩ := (mc_isTransient_iff i).1 hi
  by_contra hne
  have hμi : 0 < μ i := lt_of_le_of_ne (hμ.1 i) (Ne.symm hne)
  -- `D`: the states from which `i` can be reached in `≥ 0` steps
  set D : Finset S := Finset.univ.filter fun k => k = i ∨ mc_Accessible P k i with hD
  have hmemD : ∀ k, k ∈ D ↔ k = i ∨ mc_Accessible P k i := fun k => by simp [hD]
  have hpos_acc : ∀ k l, P k l ≠ 0 → mc_Accessible P k l := fun k l h =>
    mc_accessible_of_pos (lt_of_le_of_ne (mc_entry_nonneg hP k l) (Ne.symm h))
  -- no arc enters `D` from outside
  have hout : ∀ v ∉ D, ∀ k ∈ D, P v k = 0 := by
    intro v hv k hk
    by_contra h
    apply hv
    rw [hmemD] at hk ⊢
    rcases hk with rfl | hk
    · exact Or.inr (hpos_acc v k h)
    · exact Or.inr ((hpos_acc v k h).trans hP hk)
  -- mass balance on `D`
  have hbal : ∑ v ∈ D, μ v * (1 - ∑ k ∈ D, P v k) = 0 := by
    have h1 : ∑ k ∈ D, μ k = ∑ v, μ v * ∑ k ∈ D, P v k := by
      calc ∑ k ∈ D, μ k = ∑ k ∈ D, ∑ v, μ v * P v k := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← mc_vecMul_apply, hμ.2.2]
        _ = ∑ v, μ v * ∑ k ∈ D, P v k := by
            rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    have h2 : ∑ v, μ v * ∑ k ∈ D, P v k = ∑ v ∈ D, μ v * ∑ k ∈ D, P v k := by
      rw [← Finset.sum_add_sum_compl D]
      have : ∑ v ∈ Dᶜ, μ v * ∑ k ∈ D, P v k = 0 := Finset.sum_eq_zero fun v hv => by
        rw [Finset.sum_eq_zero fun k hk => hout v (by simpa using hv) k hk, mul_zero]
      rw [this, add_zero]
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    linarith
  have hterm : ∀ v ∈ D, 0 < μ v → ∑ k ∈ D, P v k = 1 := by
    intro v hv hμv
    have hle : ∑ k ∈ D, P v k ≤ 1 := by
      rw [← sum_row_of_mem_rowStochastic hP v]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ D)
        fun k _ _ => mc_entry_nonneg hP v k
    have hnn : ∀ u ∈ D, 0 ≤ μ u * (1 - ∑ k ∈ D, P u k) := fun u _ => by
      refine mul_nonneg (hμ.1 u) (sub_nonneg.2 ?_)
      rw [← sum_row_of_mem_rowStochastic hP u]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ D)
        fun k _ _ => mc_entry_nonneg hP u k
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hbal v hv
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hμv.ne'
    · linarith
  -- `E = D ∩ {μ > 0}` is closed
  have hE : mc_IsClosed P {k | k ∈ D ∧ 0 < μ k} := by
    rintro k ⟨hkD, hμk⟩ l hl
    by_contra hkl
    have hμl : 0 < μ l := by
      have := hμ.le_apply hP 1 k l
      rw [pow_one] at this
      exact (mul_pos hμk (lt_of_le_of_ne (mc_entry_nonneg hP k l) (Ne.symm hkl))).trans_le this
    have hlD : l ∉ D := fun h => hl ⟨h, hμl⟩
    have hsplit : ∑ k' ∈ D, P k k' + ∑ k' ∈ Dᶜ, P k k' = 1 := by
      rw [Finset.sum_add_sum_compl, sum_row_of_mem_rowStochastic hP]
    have hc0 : ∑ k' ∈ Dᶜ, P k k' = 0 := by linarith [hterm k hkD hμk]
    exact hkl ((Finset.sum_eq_zero_iff_of_nonneg fun k' _ => mc_entry_nonneg hP k k').1 hc0 l
      (by simpa using hlD))
  have hjD : j ∉ D := by
    rw [hmemD]
    rintro (rfl | h)
    · exact hji hij
    · exact hji h
  obtain ⟨m, -, hm⟩ := hij
  rw [mc_pow_eq_zero_of_closed hE m ⟨(hmemD i).2 (Or.inl rfl), hμi⟩
    fun h => hjD h.1] at hm
  exact lt_irrefl _ hm

/-- Members of the class of a recurrent state communicate with each other. -/
theorem mc_classOf_communicate (hP : P ∈ rowStochastic ℝ S) (i : S) :
    ∀ k ∈ mc_classOf P i, ∀ l ∈ mc_classOf P i, mc_Communicate P k l := fun _ hk _ hl =>
  (mc_communicate_equivalence hP).trans
    ((mc_communicate_equivalence hP).symm (mc_mem_classOf.1 hk)) (mc_mem_classOf.1 hl)

/-- Communicating states have the same class. -/
theorem mc_classOf_eq (hP : P ∈ rowStochastic ℝ S) {i j : S} (hij : mc_Communicate P i j) :
    mc_classOf P i = mc_classOf P j := by
  ext k
  simp only [mc_mem_classOf]
  exact ⟨fun h => (mc_communicate_equivalence hP).trans
      ((mc_communicate_equivalence hP).symm hij) h,
    fun h => (mc_communicate_equivalence hP).trans hij h⟩

/-- The stationary distribution attached to a set of states `C`: some stationary distribution
carried by `C` (unique when `C` is a recurrent class, `stationary_p97_class`). -/
noncomputable def mc_classDist (P : Matrix S S ℝ) (C : Finset S) : S → ℝ :=
  Classical.epsilon fun ν => mc_IsStationary P ν ∧ ∀ j ∉ C, ν j = 0

/-- Miao, p. 97: each recurrent class `C` carries a unique stationary distribution
`mc_classDist P C`, and it charges every state of `C`. -/
theorem stationary_p97_class [Nonempty S] (hP : P ∈ rowStochastic ℝ S) {i : S}
    (hi : mc_IsRecurrent P i) :
    mc_IsStationary P (mc_classDist P (mc_classOf P i)) ∧
      (∀ j ∉ mc_classOf P i, mc_classDist P (mc_classOf P i) j = 0) ∧
      (∀ j ∈ mc_classOf P i, 0 < mc_classDist P (mc_classOf P i) j) ∧
      ∀ ν, mc_IsStationary P ν → (∀ j ∉ mc_classOf P i, ν j = 0) →
        ν = mc_classDist P (mc_classOf P i) := by
  have hex : ∃ ν, mc_IsStationary P ν ∧ ∀ j ∉ mc_classOf P i, ν j = 0 := by
    obtain ⟨μ, hμ, hsupp⟩ := mc_exists_stationary hP i
    refine ⟨μ, hμ, fun j hj => hsupp j ?_ ?_⟩
    · rintro rfl; exact hj (mc_mem_classOf.2 (Or.inl rfl))
    · exact fun h => hj (mc_mem_classOf.2 (Or.inr ⟨h, hi j h⟩))
  have hspec := Classical.epsilon_spec hex
  have hC := mc_classOf_communicate hP i
  exact ⟨hspec.1, hspec.2, mc_stationary_pos_of hP hC hspec.1 hspec.2,
    fun ν hν hνs => mc_stationary_unique_of hP hC hν hspec.1 hνs hspec.2⟩

/-- The recurrent classes of the chain. -/
noncomputable def mc_recClasses (P : Matrix S S ℝ) : Finset (Finset S) := by
  classical exact (Finset.univ.filter (mc_IsRecurrent P)).image (mc_classOf P)

/-- Membership in `mc_recClasses`. -/
theorem mc_mem_recClasses {C : Finset S} :
    C ∈ mc_recClasses P ↔ ∃ i, mc_IsRecurrent P i ∧ mc_classOf P i = C := by
  classical simp [mc_recClasses]

/-- Miao, p. 97: every stationary distribution is a convex combination of the stationary
distributions of the recurrent classes. -/
theorem stationary_p97_decomposition [Nonempty S] (hP : P ∈ rowStochastic ℝ S) {μ : S → ℝ}
    (hμ : mc_IsStationary P μ) :
    ∃ w : Finset S → ℝ, (∀ C ∈ mc_recClasses P, 0 ≤ w C) ∧ ∑ C ∈ mc_recClasses P, w C = 1 ∧
      μ = ∑ C ∈ mc_recClasses P, w C • mc_classDist P C := by
  classical
  set R : Finset S → S → ℝ := fun C j => if j ∈ C then μ j else 0 with hR
  -- the pieces of `μ` sum to `μ`
  have hpt : ∀ j, ∑ C ∈ mc_recClasses P, R C j = μ j := by
    intro j
    by_cases hj : mc_IsRecurrent P j
    · have hjC : mc_classOf P j ∈ mc_recClasses P := mc_mem_recClasses.2 ⟨j, hj, rfl⟩
      rw [Finset.sum_eq_single (mc_classOf P j)]
      · simp [hR, mc_mem_classOf.2 (Or.inl rfl)]
      · intro C hC hne
        obtain ⟨i, -, rfl⟩ := mc_mem_recClasses.1 hC
        have : j ∉ mc_classOf P i := fun h => hne (mc_classOf_eq hP (mc_mem_classOf.1 h))
        simp [hR, this]
      · exact fun h => absurd hjC h
    · rw [stationary_p97_transient hP hμ hj]
      refine Finset.sum_eq_zero fun C hC => ?_
      obtain ⟨i, hi, rfl⟩ := mc_mem_recClasses.1 hC
      by_cases h : j ∈ mc_classOf P i
      · exact absurd (hi.of_communicate hP (mc_mem_classOf.1 h)) hj
      · simp [hR, h]
  -- each piece is a multiple of the class distribution
  have hpiece : ∀ C ∈ mc_recClasses P, R C = (∑ j ∈ C, μ j) • mc_classDist P C := by
    intro C hC
    obtain ⟨i, hi, rfl⟩ := mc_mem_recClasses.1 hC
    obtain ⟨-, -, -, huniq⟩ := stationary_p97_class hP hi
    set C := mc_classOf P i
    have hclosed := mc_classOf_closed hP hi
    have hRinv : R C ᵥ* P = R C := by
      funext j
      rw [mc_vecMul_apply]
      by_cases hj : j ∈ C
      · simp only [hR, hj, ite_true]
        have hμj : μ j = ∑ k, μ k * P k j := by rw [← mc_vecMul_apply, hμ.2.2]
        rw [hμj]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : k ∈ C
        · simp [hk]
        · simp only [hk, ite_false, zero_mul]
          by_cases hμk : μ k = 0
          · rw [hμk, zero_mul]
          by_cases hkj : P k j = 0
          · rw [hkj, mul_zero]
          exfalso
          have hrec : mc_IsRecurrent P k := by
            by_contra h
            exact hμk (stationary_p97_transient hP hμ h)
          have hacc : mc_Accessible P k j :=
            mc_accessible_of_pos (lt_of_le_of_ne (mc_entry_nonneg hP k j) (Ne.symm hkj))
          have hjk : mc_Communicate P j k := Or.inr ⟨hrec j hacc, hacc⟩
          exact hk (mc_mem_classOf.2 ((mc_communicate_equivalence hP).trans
            (mc_mem_classOf.1 hj) hjk))
      · simp only [hR, hj, ite_false]
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hk : k ∈ C
        · simp [hk, hclosed k hk j hj]
        · simp [hk]
    by_cases hw : ∑ j ∈ C, μ j = 0
    · have h0 : ∀ j ∈ C, μ j = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hμ.1 j).1 hw
      rw [hw, zero_smul]
      funext j
      by_cases hj : j ∈ C <;> simp [hR, hj, h0]
    · have hwpos : 0 < ∑ j ∈ C, μ j :=
        lt_of_le_of_ne (Finset.sum_nonneg fun j _ => hμ.1 j) (Ne.symm hw)
      have hstat : mc_IsStationary P ((∑ j ∈ C, μ j)⁻¹ • R C) := by
        refine ⟨fun j => ?_, ?_, ?_⟩
        · simp only [Pi.smul_apply, smul_eq_mul, hR]
          split_ifs
          · exact mul_nonneg (inv_nonneg.2 hwpos.le) (hμ.1 j)
          · simp
        · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hR]
          rw [Finset.sum_ite_mem, Finset.univ_inter, inv_mul_cancel₀ hw]
        · rw [smul_vecMul, hRinv]
      have heq := huniq _ hstat fun j hj => by simp [hR, hj]
      rw [← heq, smul_smul, mul_inv_cancel₀ hw, one_smul]
  refine ⟨fun C => ∑ j ∈ C, μ j, fun C _ => Finset.sum_nonneg fun j _ => hμ.1 j, ?_, ?_⟩
  · have : ∀ C ∈ mc_recClasses P, ∑ j ∈ C, μ j = ∑ j, R C j := fun C _ => by
      simp only [hR]; rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    simp only [hpt, hμ.2.1]
  · funext j
    rw [← hpt j, Finset.sum_apply]
    exact Finset.sum_congr rfl fun C hC => by rw [hpiece C hC]

/-- Miao, p. 97: if there are at least two recurrent classes, there are infinitely many
stationary distributions. -/
theorem stationary_p97_infinite [Nonempty S] (hP : P ∈ rowStochastic ℝ S) {i j : S}
    (hi : mc_IsRecurrent P i) (hj : mc_IsRecurrent P j) (hij : ¬ mc_Communicate P i j) :
    {μ | mc_IsStationary P μ}.Infinite := by
  obtain ⟨h1, -, hpos1, -⟩ := stationary_p97_class hP hi
  obtain ⟨h2, hs2, -, -⟩ := stationary_p97_class hP hj
  set ρ₁ := mc_classDist P (mc_classOf P i)
  set ρ₂ := mc_classDist P (mc_classOf P j)
  have hiC : i ∉ mc_classOf P j := fun h =>
    hij ((mc_communicate_equivalence hP).symm (mc_mem_classOf.1 h))
  have hρ₂ : ρ₂ i = 0 := hs2 i hiC
  have hρ₁ : 0 < ρ₁ i := hpos1 i (mc_mem_classOf.2 (Or.inl rfl))
  have : Infinite (Set.Icc (0 : ℝ) 1) := Set.Icc.infinite zero_lt_one
  refine Set.infinite_of_injective_forall_mem
    (f := fun t : Set.Icc (0 : ℝ) 1 => (t : ℝ) • ρ₁ + (1 - (t : ℝ)) • ρ₂) ?_
    fun t => h1.convex h2 t.2.1 t.2.2
  intro s t hst
  have := congrFun hst i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hρ₂, mul_zero, add_zero] at this
  exact Subtype.ext (mul_right_cancel₀ hρ₁.ne' this)

/-! ### Theorem 3.1.4 -/

/-- The chain is aperiodic: every state has period `1`. -/
def mc_IsAperiodicChain (P : Matrix S S ℝ) : Prop := ∀ i, mc_IsAperiodic P i

/-- **Theorem 3.1.4** (Miao, p. 96): a finite chain is irreducible and aperiodic iff there is
`k₀ > 0` with `p⁽ᵏ⁾ᵢⱼ > 0` for all `i, j` and all `k ≥ k₀`. -/
theorem theorem_3_1_4 (hP : P ∈ rowStochastic ℝ S) :
    (mc_IsIrreducible P ∧ mc_IsAperiodicChain P) ↔
      ∃ k₀, 0 < k₀ ∧ ∀ k ≥ k₀, ∀ i j, 0 < (P ^ k) i j := by
  constructor
  · rintro ⟨hirr, hap⟩
    have hacc := (mc_isIrreducible_iff hP).1 hirr
    -- all large times are return times of `j`
    have hN : ∀ j, ∃ N, ∀ n ≥ N, 0 < (P ^ n) j j := by
      intro j
      obtain ⟨m, hm, hm'⟩ := hacc j j
      obtain ⟨N, hN⟩ := mc_eventually_mem_of_setGcd_eq_one (mc_returnSet_isAddClosed hP j)
        ⟨hm, hm'⟩ hm (hap j)
      exact ⟨N, fun n hn => (hN n hn).2⟩
    choose N hN using hN
    choose r hr hr' using hacc
    refine ⟨Finset.univ.sup (fun p : S × S => N p.2 + r p.1 p.2) + 1, by omega,
      fun k hk i j => ?_⟩
    have hle : N j + r i j ≤ Finset.univ.sup (fun p : S × S => N p.2 + r p.1 p.2) :=
      Finset.le_sup (f := fun p : S × S => N p.2 + r p.1 p.2) (Finset.mem_univ (i, j))
    have := mc_pow_add_pos hP (hr' i j) (hN j (k - r i j) (by omega))
    rwa [show r i j + (k - r i j) = k by omega] at this
  · rintro ⟨k₀, hk₀, h⟩
    refine ⟨(mc_isIrreducible_iff hP).2 fun i j => ⟨k₀, hk₀, h k₀ le_rfl i j⟩, fun i => ?_⟩
    have hS := mc_returnSet_isAddClosed hP i
    have h1 : k₀ ∈ mc_returnSet P i := ⟨hk₀, h k₀ le_rfl i i⟩
    have h2 : k₀ + 1 ∈ mc_returnSet P i := ⟨by omega, h (k₀ + 1) (by omega) i i⟩
    have hd1 := mc_setGcd_dvd hS h1 hk₀ h1
    have hd2 := mc_setGcd_dvd hS h1 hk₀ h2
    exact Nat.dvd_one.1 ((Nat.dvd_add_right hd1).1 hd2)

end Miao.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Finite Markov chains: Figure 3.1 and Examples 3.1.1–3.1.3, 3.1.6

Miao, §3.1, pp. 87–94, 96–97. States `1, 2, …` of the book are `0, 1, …` here.

* **Figure 3.1** (`fig31`, p. 87): the classes are `{1, 3}` and `{2, 4}` (`fig31_communicate`:
  `i ↔ j` iff `i ≡ j mod 2`), all states are recurrent and aperiodic (`fig31_recurrent`).
* **Example 3.1.1** (regime shifts, `ex311 p q`, p. 87): the formula for `Pᵐ`
  (`example_3_1_1_pow`), its limit (`example_3_1_1_tendsto`), irreducibility, recurrence and
  aperiodicity, and the unique stationary distribution `((1 − q), (1 − p))/(2 − p − q)`, the
  common row of the limit (`example_3_1_1_stationary`, pp. 91, 93, 96).
* **Example 3.1.2** (cyclical moving subsets, `ex312 P₁ P₂`, p. 88): the formulas for `P²ᵐ` and
  `P²ᵐ⁺¹` (`example_3_1_2_pow_even`, `example_3_1_2_pow_odd`); the chain is irreducible, all
  states are recurrent and have period `2` (`example_3_1_2_classes`, pp. 91–93); it has a
  stationary distribution (`example_3_1_2_stationary`), but `Pᵗ` does not converge
  (`example_3_1_2_not_tendsto`).
* **Example 3.1.3** (`ex313 α`, p. 88): `Pᵐ` for `m ≥ 1` (`example_3_1_3_pow`), its limit
  (`example_3_1_3_tendsto`), state 1 transient and states 2, 3 recurrent and aperiodic, with
  classes `{1}` and `{2, 3}` (`example_3_1_3_classes`, pp. 91–93).
* **Example 3.1.6** (random walk with two barriers, `ex316 p q`, p. 89): states 1 and 4 are
  absorbing, the classes are `{1}`, `{2, 3}`, `{4}`, the first and last recurrent, `{2, 3}`
  transient (`example_3_1_6_classes`, pp. 92, 94), and there are infinitely many stationary
  distributions (`example_3_1_6_infinite`, p. 97).

**Corrections.**
* Example 3.1.2: the book says (pp. 96–97) that there is no stationary distribution; there is
  one (`example_3_1_2_stationary`); what fails is the convergence of `Pᵗ`.
* Example 3.1.3: the displayed formula for `Pᵐ` holds for `m ≥ 1` only (`P⁰ = I`); it is stated
  for `m + 1`.
-/

namespace Miao.MarkovProcesses

open Matrix Filter Topology

variable {S : Type*} [Fintype S] [DecidableEq S] {P : Matrix S S ℝ}

/-! ### Tools for the examples -/

/-- A state cannot reach a state outside a closed set containing it. -/
theorem mc_not_accessible_of_closed {E : Set S} (hE : mc_IsClosed P E) {i j : S} (hi : i ∈ E)
    (hj : j ∉ E) : ¬ mc_Accessible P i j := by
  rintro ⟨m, -, hm⟩
  rw [mc_pow_eq_zero_of_closed hE m hi hj] at hm
  exact lt_irrefl _ hm

/-- A state of a closed set from which it is reachable from every state of the set is
recurrent. -/
theorem mc_isRecurrent_of_closed {E : Set S} (hE : mc_IsClosed P E) {i : S} (hi : i ∈ E)
    (h : ∀ j ∈ E, mc_Accessible P j i) : mc_IsRecurrent P i := by
  intro j hij
  by_contra hji
  have hjE : j ∈ E := by
    by_contra hjE
    exact mc_not_accessible_of_closed hE hi hjE hij
  exact hji (h j hjE)

/-- A state with `pᵢᵢ > 0` is aperiodic. -/
theorem mc_isAperiodic_of_pos (hP : P ∈ rowStochastic ℝ S) {i : S} (h : 0 < P i i) :
    mc_IsAperiodic P i := by
  have h1 : 1 ∈ mc_returnSet P i := ⟨le_rfl, by simpa using h⟩
  exact Nat.dvd_one.1 (mc_period_dvd hP h1)

/-- An absorbing state (`{i}` closed) stays put: `p⁽ⁿ⁾ᵢᵢ = 1` for all `n`. -/
theorem mc_pow_absorbing (hP : P ∈ rowStochastic ℝ S) {i : S} (hi : mc_IsClosed P {i})
    (n : ℕ) : (P ^ n) i i = 1 := by
  have h := mc_pow_row_sum hP n i
  rwa [Finset.sum_eq_single i (fun j _ hj => mc_pow_eq_zero_of_closed hi n rfl hj)
    (fun h => absurd (Finset.mem_univ i) h)] at h

/-! ### Figure 3.1 -/

/-- The transition matrix of Figure 3.1 (Miao, p. 87). -/
noncomputable def fig31 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1 / 3, 0, 2 / 3, 0; 0, 1 / 4, 0, 3 / 4; 1 / 2, 0, 1 / 2, 0; 0, 1 / 4, 0, 3 / 4]

/-- The matrix of Figure 3.1 is a transition matrix. -/
theorem fig31_mem : fig31 ∈ rowStochastic ℝ (Fin 4) := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_⟩ <;> fin_cases i <;> try fin_cases j
  all_goals norm_num [fig31, Fin.sum_univ_succ]

/-- The states of a given parity form a closed set for `fig31`. -/
theorem fig31_closed (r : ℕ) : mc_IsClosed fig31 {i | (i : ℕ) % 2 = r % 2} := by
  have h : ∀ i j : Fin 4, fig31 i j ≠ 0 → (i : ℕ) % 2 = (j : ℕ) % 2 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [fig31]
  intro i hi j hj
  simp only [Set.mem_ofPred_eq] at hi hj
  by_contra hne
  exact hj ((h i j hne).symm.trans hi)

/-- Miao, p. 90: the chain of Figure 3.1 has the two classes `{1, 3}` and `{2, 4}`: `i ↔ j` iff
`i` and `j` have the same parity (in the book's numbering as well). -/
theorem fig31_communicate (i j : Fin 4) :
    mc_Communicate fig31 i j ↔ (i : ℕ) % 2 = (j : ℕ) % 2 := by
  constructor
  · intro h
    by_contra hne
    rcases h with rfl | ⟨h, -⟩
    · exact hne rfl
    · exact mc_not_accessible_of_closed (fig31_closed i) (by simp) (by simpa using Ne.symm hne) h
  · intro h
    by_cases hij : i = j
    · exact Or.inl hij
    · refine Or.inr ⟨mc_accessible_of_pos ?_, mc_accessible_of_pos ?_⟩ <;>
        fin_cases i <;> fin_cases j <;> simp_all [fig31]

/-- Miao, pp. 91–93: all states of Figure 3.1 are recurrent and aperiodic, and `{1, 3}`, `{2, 4}`
are recurrent classes. -/
theorem fig31_recurrent (i : Fin 4) : mc_IsRecurrent fig31 i ∧ mc_IsAperiodic fig31 i := by
  refine ⟨mc_isRecurrent_of_closed (fig31_closed i) (by simp) fun j hj => ?_,
    mc_isAperiodic_of_pos fig31_mem ?_⟩
  · by_cases hji : j = i
    · subst hji; exact mc_accessible_of_pos (by fin_cases j <;> simp [fig31])
    · rcases (fig31_communicate j i).2 (by simpa using hj) with h | ⟨h, -⟩
      · exact absurd h hji
      · exact h
  · fin_cases i <;> simp [fig31]

/-! ### Example 3.1.1 -/

/-- **Example 3.1.1** (regime shifts, Miao, p. 87): `P = [p, 1 − p; 1 − q, q]`. -/
def ex311 (p q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![p, 1 - p; 1 - q, q]

/-- `ex311 p q` is a transition matrix for `p, q ∈ [0, 1]`. -/
theorem ex311_mem {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ex311 p q ∈ rowStochastic ℝ (Fin 2) := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_⟩ <;> fin_cases i <;> try fin_cases j
  all_goals simp [ex311, Fin.sum_univ_succ] <;> linarith

/-- **Example 3.1.1** (Miao, p. 88): the `m`-step transition matrix
`Pᵐ = (2 − p − q)⁻¹ [1 − q, 1 − p; 1 − q, 1 − p] + (p + q − 1)ᵐ (2 − p − q)⁻¹ [1 − p, p − 1;
q − 1, 1 − q]` (for `p + q ≠ 2`). -/
theorem example_3_1_1_pow {p q : ℝ} (hpq : p + q ≠ 2) (m : ℕ) :
    ex311 p q ^ m = (1 / (2 - p - q)) • !![1 - q, 1 - p; 1 - q, 1 - p] +
      ((p + q - 1) ^ m / (2 - p - q)) • !![1 - p, p - 1; q - 1, 1 - q] := by
  have h2 : (2 - p - q) ≠ 0 := fun h => hpq (by linarith)
  induction m with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring
  | succ m ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ex311, mul_apply, Fin.sum_univ_succ, pow_succ] <;> field_simp <;> ring

/-- The limit matrix of Example 3.1.1: both rows are `((1 − q), (1 − p))/(2 − p − q)`. -/
noncomputable def ex311Lim (p q : ℝ) : Fin 2 → ℝ := ![(1 - q) / (2 - p - q), (1 - p) / (2 - p - q)]

/-- **Example 3.1.1** (Miao, p. 88): `Pᵐ` converges, each row to
`((1 − q), (1 − p))/(2 − p − q)`, when `p, q ∈ (0, 1)`. -/
theorem example_3_1_1_tendsto {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1)
    (i j : Fin 2) : Tendsto (fun m => (ex311 p q ^ m) i j) atTop (𝓝 (ex311Lim p q j)) := by
  have hpq : p + q ≠ 2 := fun h => by linarith
  have hr : Tendsto (fun m => (p + q - 1) ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (abs_lt.2 ⟨by linarith, by linarith⟩)
  simp only [example_3_1_1_pow hpq]
  have key : ∀ c d : ℝ, Tendsto (fun m => 1 / (2 - p - q) * c + (p + q - 1) ^ m / (2 - p - q) * d)
      atTop (𝓝 (1 / (2 - p - q) * c)) := fun c d => by
    have := ((hr.div_const (2 - p - q)).mul_const d).const_add (1 / (2 - p - q) * c)
    simpa using this
  fin_cases i <;> fin_cases j <;> simp only [ex311Lim] <;>
    simpa [div_eq_inv_mul, mul_comm] using key _ _

/-- **Example 3.1.1** (Miao, pp. 91–93, 96): for `p, q ∈ (0, 1)` the chain is irreducible, all
states are recurrent and aperiodic, and the unique stationary distribution is the common row
`((1 − q), (1 − p))/(2 − p − q)` of the limit. -/
theorem example_3_1_1_stationary {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q)
    (hq1 : q < 1) :
    mc_IsIrreducible (ex311 p q) ∧ (∀ i, mc_IsRecurrent (ex311 p q) i) ∧
      mc_IsAperiodicChain (ex311 p q) ∧ mc_IsStationary (ex311 p q) (ex311Lim p q) ∧
      ∀ ν, mc_IsStationary (ex311 p q) ν → ν = ex311Lim p q := by
  have hP := ex311_mem hp0.le hp1.le hq0.le hq1.le
  have hpos : ∀ i j, 0 < (ex311 p q ^ 1) i j := fun i j => by
    fin_cases i <;> fin_cases j <;> simp [ex311] <;> linarith
  have hirr : mc_IsIrreducible (ex311 p q) :=
    (mc_isIrreducible_iff hP).2 fun i j => ⟨1, le_rfl, hpos i j⟩
  obtain ⟨μ, hμ, -, hlim, huniq⟩ := theorem_3_1_3 hP ⟨1, one_pos, hpos⟩
  have hμeq : μ = ex311Lim p q := funext fun j =>
    tendsto_nhds_unique (hlim 0 j) (example_3_1_1_tendsto hp0 hp1 hq0 hq1 0 j)
  subst hμeq
  refine ⟨hirr, theorem_3_1_1c hP hirr, fun i => mc_isAperiodic_of_pos hP ?_, hμ, huniq⟩
  simpa using hpos i i

/-! ### Example 3.1.2 -/

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- **Example 3.1.2** (cyclical moving subsets, Miao, p. 88): `P = [0, P₁; P₂, 0]` with `P₁`
a `k × (n − k)` and `P₂` an `(n − k) × k` transition matrix. -/
def ex312 (P₁ : Matrix α β ℝ) (P₂ : Matrix β α ℝ) : Matrix (α ⊕ β) (α ⊕ β) ℝ :=
  fromBlocks 0 P₁ P₂ 0

omit [DecidableEq α] [DecidableEq β] in
/-- The hypothesis of Example 3.1.2: a rectangular transition matrix with positive entries. -/
def mc_IsPosStochastic (A : Matrix α β ℝ) : Prop := (∀ a b, 0 < A a b) ∧ ∀ a, ∑ b, A a b = 1

/-- Powers of a block-diagonal matrix. -/
theorem mc_fromBlocks_diag_pow (A : Matrix α α ℝ) (D : Matrix β β ℝ) (m : ℕ) :
    fromBlocks A 0 0 D ^ m = fromBlocks (A ^ m) 0 0 (D ^ m) := by
  induction m with
  | zero => simp [fromBlocks_one]
  | succ m ih => rw [pow_succ, ih, fromBlocks_multiply]; simp [pow_succ]

/-- **Example 3.1.2** (Miao, p. 88): `P²ᵐ = [(P₁P₂)ᵐ, 0; 0, (P₂P₁)ᵐ]`. -/
theorem example_3_1_2_pow_even (P₁ : Matrix α β ℝ) (P₂ : Matrix β α ℝ) (m : ℕ) :
    ex312 P₁ P₂ ^ (2 * m) = fromBlocks ((P₁ * P₂) ^ m) 0 0 ((P₂ * P₁) ^ m) := by
  rw [pow_mul, sq, ex312, fromBlocks_multiply]
  simpa using mc_fromBlocks_diag_pow (P₁ * P₂) (P₂ * P₁) m

/-- **Example 3.1.2** (Miao, p. 88): `P²ᵐ⁺¹ = [0, (P₁P₂)ᵐP₁; (P₂P₁)ᵐP₂, 0]`. -/
theorem example_3_1_2_pow_odd (P₁ : Matrix α β ℝ) (P₂ : Matrix β α ℝ) (m : ℕ) :
    ex312 P₁ P₂ ^ (2 * m + 1) = fromBlocks 0 ((P₁ * P₂) ^ m * P₁) ((P₂ * P₁) ^ m * P₂) 0 := by
  rw [pow_succ, example_3_1_2_pow_even]
  rw [ex312, fromBlocks_multiply]
  simp

/-- Example 3.1.2 is a transition matrix. -/
theorem ex312_mem {P₁ : Matrix α β ℝ} {P₂ : Matrix β α ℝ} (h₁ : mc_IsPosStochastic P₁)
    (h₂ : mc_IsPosStochastic P₂) : ex312 P₁ P₂ ∈ rowStochastic ℝ (α ⊕ β) := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨?_, ?_⟩
  · rintro (a | b) (a' | b') <;> simp [ex312, (h₁.1 _ _).le, (h₂.1 _ _).le]
  · rintro (a | b) <;> simp [ex312, Fintype.sum_sum_type, h₁.2, h₂.2]

/-- **Example 3.1.2** (Miao, pp. 91–93): with nonempty blocks the chain is irreducible, every
state is recurrent, and every state has period `2`. -/
theorem example_3_1_2_classes [Nonempty α] [Nonempty β] {P₁ : Matrix α β ℝ}
    {P₂ : Matrix β α ℝ} (h₁ : mc_IsPosStochastic P₁) (h₂ : mc_IsPosStochastic P₂) :
    mc_IsIrreducible (ex312 P₁ P₂) ∧ (∀ x, mc_IsRecurrent (ex312 P₁ P₂) x) ∧
      ∀ x, mc_period (ex312 P₁ P₂) x = 2 := by
  have hP := ex312_mem h₁ h₂
  set Q := ex312 P₁ P₂
  have hab : ∀ a b, mc_Accessible Q (Sum.inl a) (Sum.inr b) := fun a b =>
    mc_accessible_of_pos (by simpa [Q, ex312] using h₁.1 a b)
  have hba : ∀ b a, mc_Accessible Q (Sum.inr b) (Sum.inl a) := fun b a =>
    mc_accessible_of_pos (by simpa [Q, ex312] using h₂.1 b a)
  have hacc : ∀ x y, mc_Accessible Q x y := by
    obtain ⟨a₀⟩ := ‹Nonempty α›
    obtain ⟨b₀⟩ := ‹Nonempty β›
    rintro (a | b) (a' | b')
    · exact (hab a b₀).trans hP (hba b₀ a')
    · exact hab a b'
    · exact hba b a'
    · exact (hba b a₀).trans hP (hab a₀ b')
  have hirr := (mc_isIrreducible_iff hP).2 hacc
  refine ⟨hirr, theorem_3_1_1c hP hirr, fun x => ?_⟩
  -- `2` is a return time
  have h2 : 2 ∈ mc_returnSet Q x := by
    obtain ⟨a₀⟩ := ‹Nonempty α›
    obtain ⟨b₀⟩ := ‹Nonempty β›
    refine ⟨by norm_num, ?_⟩
    rcases x with a | b
    · have h := mc_pow_add_pos hP (pow_one Q ▸ (by simpa [Q, ex312] using h₁.1 a b₀) :
        0 < (Q ^ 1) (Sum.inl a) (Sum.inr b₀))
        (pow_one Q ▸ (by simpa [Q, ex312] using h₂.1 b₀ a) :
        0 < (Q ^ 1) (Sum.inr b₀) (Sum.inl a))
      simpa using h
    · have h := mc_pow_add_pos hP (pow_one Q ▸ (by simpa [Q, ex312] using h₂.1 b a₀) :
        0 < (Q ^ 1) (Sum.inr b) (Sum.inl a₀))
        (pow_one Q ▸ (by simpa [Q, ex312] using h₁.1 a₀ b) :
        0 < (Q ^ 1) (Sum.inl a₀) (Sum.inr b))
      simpa using h
  -- every return time is even
  have heven : ∀ n ∈ mc_returnSet Q x, 2 ∣ n := by
    rintro n ⟨-, hn⟩
    by_contra hodd
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
    rw [example_3_1_2_pow_odd] at hn
    rcases x with a | b <;> simp at hn
  have hS := mc_returnSet_isAddClosed hP x
  exact Nat.dvd_antisymm (mc_setGcd_dvd hS h2 (by norm_num) h2)
    (dvd_mc_setGcd hS h2 (by norm_num) heven)

omit [DecidableEq α] [DecidableEq β] in
/-- Miao, pp. 96–97, corrected: Example 3.1.2 **has** a stationary distribution (contrary to the
text), as every finite chain does. -/
theorem example_3_1_2_stationary [Nonempty α] {P₁ : Matrix α β ℝ} {P₂ : Matrix β α ℝ}
    (h₁ : mc_IsPosStochastic P₁) (h₂ : mc_IsPosStochastic P₂) :
    ∃ μ, mc_IsStationary (ex312 P₁ P₂) μ := by
  classical
  obtain ⟨μ, hμ, -⟩ := mc_exists_stationary (ex312_mem h₁ h₂) (Sum.inl (Classical.arbitrary α))
  exact ⟨μ, hμ⟩

/-- Miao, pp. 96–97: Example 3.1.2 violates the hypothesis of Theorem 3.1.3: the powers `Pᵗ` do
not converge (entrywise). -/
theorem example_3_1_2_not_tendsto [Nonempty α] {P₁ : Matrix α β ℝ} {P₂ : Matrix β α ℝ}
    (h₁ : mc_IsPosStochastic P₁) (h₂ : mc_IsPosStochastic P₂) :
    ¬ ∃ L : Matrix (α ⊕ β) (α ⊕ β) ℝ,
      ∀ x y, Tendsto (fun t => (ex312 P₁ P₂ ^ t) x y) atTop (𝓝 (L x y)) := by
  rintro ⟨L, hL⟩
  have hev : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp only [id]; omega) tendsto_id
  have hodd : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp only [id]; omega) tendsto_id
  -- every entry of the limit vanishes
  have hL0 : ∀ x y, L x y = 0 := by
    intro x y
    rcases x with a | b <;> rcases y with a' | b'
    · refine tendsto_nhds_unique ((hL _ _).comp hodd) ?_
      simp [Function.comp_def, example_3_1_2_pow_odd]
    · refine tendsto_nhds_unique ((hL _ _).comp hev) ?_
      simp [Function.comp_def, example_3_1_2_pow_even]
    · refine tendsto_nhds_unique ((hL _ _).comp hev) ?_
      simp [Function.comp_def, example_3_1_2_pow_even]
    · refine tendsto_nhds_unique ((hL _ _).comp hodd) ?_
      simp [Function.comp_def, example_3_1_2_pow_odd]
  obtain ⟨μ, hμ⟩ := example_3_1_2_stationary h₁ h₂
  have hμ0 : ∀ y, μ y = 0 := fun y => by
    have h := tendsto_finsetSum Finset.univ fun x _ => (hL x y).const_mul (μ x)
    simp only [hL0, mul_zero, Finset.sum_const_zero] at h
    refine tendsto_nhds_unique ?_ h
    simp only [← hμ.apply_eq]
    exact tendsto_const_nhds
  have := hμ.2.1
  simp [hμ0] at this

/-! ### Example 3.1.3 -/

/-- **Example 3.1.3** (Miao, p. 88): `P = [1 − α, α/2, α/2; 0, 1/2, 1/2; 0, 1/2, 1/2]`. -/
noncomputable def ex313 (a : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 - a, a / 2, a / 2; 0, 1 / 2, 1 / 2; 0, 1 / 2, 1 / 2]

/-- `ex313 α` is a transition matrix for `α ∈ [0, 1]`. -/
theorem ex313_mem {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : ex313 a ∈ rowStochastic ℝ (Fin 3) := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_⟩ <;> fin_cases i <;> try fin_cases j
  all_goals norm_num [ex313, Fin.sum_univ_succ] <;> linarith

/-- **Example 3.1.3** (Miao, p. 88): `Pᵐ = [(1 − α)ᵐ, βₘ/2, βₘ/2; 0, 1/2, 1/2; 0, 1/2, 1/2]` with
`βₘ = 1 − (1 − α)ᵐ`, for `m ≥ 1` (stated for `m + 1`). -/
theorem example_3_1_3_pow (a : ℝ) (m : ℕ) :
    ex313 a ^ (m + 1) = !![(1 - a) ^ (m + 1), (1 - (1 - a) ^ (m + 1)) / 2,
      (1 - (1 - a) ^ (m + 1)) / 2; 0, 1 / 2, 1 / 2; 0, 1 / 2, 1 / 2] := by
  induction m with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ex313]
  | succ m ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ex313, mul_apply, Fin.sum_univ_succ] <;> ring

/-- **Example 3.1.3** (Miao, p. 88): for `α ∈ (0, 1)`, `Pᵐ` converges to the matrix with all rows
`(0, 1/2, 1/2)`. -/
theorem example_3_1_3_tendsto {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (i j : Fin 3) :
    Tendsto (fun m => (ex313 a ^ m) i j) atTop (𝓝 (![0, 1 / 2, 1 / 2] j)) := by
  have hr : Tendsto (fun m => (1 - a) ^ (m + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)).comp
      (tendsto_add_atTop_nat 1)
  rw [← tendsto_add_atTop_iff_nat 1]
  simp only [example_3_1_3_pow]
  have hb : Tendsto (fun m => (1 - (1 - a) ^ (m + 1)) / 2) atTop (𝓝 2⁻¹) := by
    simpa using (hr.const_sub 1).div_const 2
  fin_cases i <;> fin_cases j <;> simp [hr, hb]

/-- **Example 3.1.3** (Miao, pp. 91–93): for `α ∈ (0, 1)`, state 1 is transient, states 2 and 3
are recurrent and aperiodic, and the classes are `{1}` and `{2, 3}`. -/
theorem example_3_1_3_classes {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    mc_IsTransient (ex313 a) 0 ∧ mc_IsRecurrent (ex313 a) 1 ∧ mc_IsRecurrent (ex313 a) 2 ∧
      mc_IsAperiodic (ex313 a) 1 ∧ mc_IsAperiodic (ex313 a) 2 ∧
      ∀ i j, mc_Communicate (ex313 a) i j ↔ (i = j ∨ (i ≠ 0 ∧ j ≠ 0)) := by
  have hP := ex313_mem ha0.le ha1.le
  have hE : mc_IsClosed (ex313 a) {i | i ≠ 0} := by
    intro i hi j hj
    simp only [Set.mem_ofPred_eq, not_not] at hi hj
    subst hj
    fin_cases i <;> simp_all [ex313]
  have hpos : ∀ i j : Fin 3, i ≠ 0 → j ≠ 0 → 0 < ex313 a i j := fun i j hi hj => by
    fin_cases i <;> fin_cases j <;> simp_all [ex313]
  have hrec : ∀ i : Fin 3, i ≠ 0 → mc_IsRecurrent (ex313 a) i := fun i hi =>
    mc_isRecurrent_of_closed hE hi fun j hj => mc_accessible_of_pos (hpos j i hj hi)
  have h01 : mc_Accessible (ex313 a) 0 1 := mc_accessible_of_pos (by simp [ex313]; linarith)
  have h10 : ¬ mc_Accessible (ex313 a) 1 0 := mc_not_accessible_of_closed hE (by decide) (by simp)
  refine ⟨(mc_isTransient_iff 0).2 ⟨1, h01, h10⟩, hrec 1 (by decide), hrec 2 (by decide),
    mc_isAperiodic_of_pos hP (hpos 1 1 (by decide) (by decide)),
    mc_isAperiodic_of_pos hP (hpos 2 2 (by decide) (by decide)), fun i j => ?_⟩
  constructor
  · rintro (h | ⟨hij, hji⟩)
    · exact Or.inl h
    · by_cases hij' : i = j
      · exact Or.inl hij'
      refine Or.inr ⟨fun hi => ?_, fun hj => ?_⟩
      · subst hi
        exact mc_not_accessible_of_closed hE (by simpa using Ne.symm hij') (by simp) hji
      · subst hj
        exact mc_not_accessible_of_closed hE (by simpa using hij') (by simp) hij
  · rintro (h | ⟨hi, hj⟩)
    · exact Or.inl h
    · exact Or.inr ⟨mc_accessible_of_pos (hpos i j hi hj), mc_accessible_of_pos (hpos j i hj hi)⟩

/-! ### Example 3.1.6 -/

/-- **Example 3.1.6** (random walk with two barriers, Miao, p. 89). -/
def ex316 (p q : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; q, 0, p, 0; 0, q, 0, p; 0, 0, 0, 1]

/-- `ex316 p q` is a transition matrix when `p, q ≥ 0`, `p + q = 1`. -/
theorem ex316_mem {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) :
    ex316 p q ∈ rowStochastic ℝ (Fin 4) := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_⟩ <;> fin_cases i <;> try fin_cases j
  all_goals simp [ex316, Fin.sum_univ_succ] <;> linarith

/-- **Example 3.1.6** (Miao, pp. 89, 92, 94): for `p, q > 0`, `p + q = 1`, states 1 and 4 are
absorbing (`p⁽ⁿ⁾₁₁ = p⁽ⁿ⁾₄₄ = 1`), the classes are `{1}`, `{2, 3}` and `{4}`, states 1 and 4
are recurrent and states 2 and 3 are transient. -/
theorem example_3_1_6_classes {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : p + q = 1) :
    (∀ n, (ex316 p q ^ n) 0 0 = 1 ∧ (ex316 p q ^ n) 3 3 = 1) ∧
      mc_IsRecurrent (ex316 p q) 0 ∧ mc_IsRecurrent (ex316 p q) 3 ∧
      mc_IsTransient (ex316 p q) 1 ∧ mc_IsTransient (ex316 p q) 2 ∧
      ∀ i j, mc_Communicate (ex316 p q) i j ↔ (i = j ∨ ((i = 1 ∨ i = 2) ∧ (j = 1 ∨ j = 2))) := by
  have hP := ex316_mem hp.le hq.le hpq
  have h0 : mc_IsClosed (ex316 p q) {0} := by
    intro i hi j hj
    simp only [Set.mem_singleton_iff] at hi hj
    subst hi; fin_cases j <;> simp_all [ex316]
  have h3 : mc_IsClosed (ex316 p q) {3} := by
    intro i hi j hj
    simp only [Set.mem_singleton_iff] at hi hj
    subst hi; fin_cases j <;> simp_all [ex316]
  have hrec0 : mc_IsRecurrent (ex316 p q) 0 := mc_isRecurrent_of_closed h0 rfl fun j hj => by
    rw [Set.mem_singleton_iff] at hj; subst hj; exact mc_accessible_of_pos (by simp [ex316])
  have hrec3 : mc_IsRecurrent (ex316 p q) 3 := mc_isRecurrent_of_closed h3 rfl fun j hj => by
    rw [Set.mem_singleton_iff] at hj; subst hj; exact mc_accessible_of_pos (by simp [ex316])
  have h12 : mc_Accessible (ex316 p q) 1 2 := mc_accessible_of_pos (by simpa [ex316] using hp)
  have h21 : mc_Accessible (ex316 p q) 2 1 := mc_accessible_of_pos (by simpa [ex316] using hq)
  have h10 : mc_Accessible (ex316 p q) 1 0 := mc_accessible_of_pos (by simpa [ex316] using hq)
  have h23 : mc_Accessible (ex316 p q) 2 3 := mc_accessible_of_pos (by simpa [ex316] using hp)
  have hn0 : ∀ j, j ≠ 0 → ¬ mc_Accessible (ex316 p q) 0 j := fun j hj =>
    mc_not_accessible_of_closed h0 rfl hj
  have hn3 : ∀ j, j ≠ 3 → ¬ mc_Accessible (ex316 p q) 3 j := fun j hj =>
    mc_not_accessible_of_closed h3 rfl hj
  refine ⟨fun n => ⟨mc_pow_absorbing hP h0 n, mc_pow_absorbing hP h3 n⟩, hrec0, hrec3,
    (mc_isTransient_iff 1).2 ⟨0, h10, hn0 1 (by decide)⟩,
    (mc_isTransient_iff 2).2 ⟨3, h23, hn3 2 (by decide)⟩, fun i j => ?_⟩
  constructor
  · rintro (h | ⟨hij, hji⟩)
    · exact Or.inl h
    · by_cases hij' : i = j
      · exact Or.inl hij'
      right
      fin_cases i <;> fin_cases j <;> simp_all
  · rintro (h | ⟨hi, hj⟩)
    · exact Or.inl h
    · by_cases hij : i = j
      · exact Or.inl hij
      right
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exact absurd rfl hij
      · exact ⟨h12, h21⟩
      · exact ⟨h21, h12⟩
      · exact absurd rfl hij

/-- Miao, p. 97 applied to Example 3.1.6: with the two recurrent classes `{1}` and `{4}` there
are infinitely many stationary distributions. -/
theorem example_3_1_6_infinite {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : p + q = 1) :
    {μ | mc_IsStationary (ex316 p q) μ}.Infinite := by
  obtain ⟨-, h0, h3, -, -, hc⟩ := example_3_1_6_classes hp hq hpq
  exact stationary_p97_infinite (ex316_mem hp.le hq.le hpq) h0 h3
    fun h => by rcases (hc 0 3).1 h with h | ⟨h, -⟩ <;> simp_all

end Miao.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercises 3 and 6 of Chapter 3

Miao, §3.1.3, pp. 97–98, and §3.4, pp. 113–114 (Exercise 1 is `ex_3_1` in `ChainClasses`).

* **Exercise 3** (§3.1.3, pp. 97–98): the truncated birth–death chain `ex33 k p` on
  `{0, …, k − 1}` (up with probability `p`, down with probability `q = 1 − p`, `p₀₀ = q`,
  `p_{k−1,k−1} = p`) is irreducible for `0 < p < 1` and has the unique stationary distribution
  `πᵢ = (1 − ρ)ρⁱ/(1 − ρᵏ)`, `ρ = p/q ≠ 1` (`ex_3_3`), and `πᵢ = 1/k` when `ρ = 1`
  (`ex_3_3_half`). As `k → ∞`, `πᵢ → (1 − ρ)ρⁱ` when `ρ < 1` and `πᵢ → 0` when `ρ > 1`
  (`ex_3_3_limit_lt`, `ex_3_3_limit_gt`, p. 98).
* **Exercise 6** (p. 114): a doubly stochastic, irreducible and aperiodic chain on `N` states
  has the uniform stationary distribution `πᵢ = 1/N`, it is the unique one, and
  `p⁽ᵗ⁾ᵢⱼ → 1/N` (`ex_3_6`); aperiodicity is needed only for the convergence
  (`ex_3_6_irreducible`).

The stationarity proofs use detailed balance (`mc_isStationary_of_detailed_balance`).
-/

namespace Miao.MarkovProcesses

open Matrix Filter Topology

variable {S : Type*} [Fintype S] [DecidableEq S] {P : Matrix S S ℝ}

/-- Detailed balance implies stationarity: if `μᵢpᵢⱼ = μⱼpⱼᵢ` for all `i, j`, then `μ = μP`. -/
theorem mc_isStationary_of_detailed_balance (hP : P ∈ rowStochastic ℝ S) {μ : S → ℝ}
    (hμ0 : ∀ i, 0 ≤ μ i) (hμ1 : ∑ i, μ i = 1) (hdb : ∀ i j, μ i * P i j = μ j * P j i) :
    mc_IsStationary P μ := by
  refine ⟨hμ0, hμ1, funext fun j => ?_⟩
  rw [mc_vecMul_apply]
  simp only [hdb _ j, ← Finset.mul_sum, sum_row_of_mem_rowStochastic hP, mul_one]

/-! ### Exercise 3 -/

/-- The transition probabilities of the truncated birth–death chain on `{0, …, k − 1}`, as a
function of the values of the states. -/
def ex33Fn (k : ℕ) (p : ℝ) (a b : ℕ) : ℝ :=
  (if b = a + 1 then p else 0) + (if b + 1 = a then 1 - p else 0) +
    (if b = a then (if a = 0 then 1 - p else 0) + (if a + 1 = k then p else 0) else 0)

/-- **Exercise 3** (Miao, pp. 97–98): the truncated birth–death chain on `{0, …, k − 1}`. -/
def ex33 (k : ℕ) (p : ℝ) : Matrix (Fin k) (Fin k) ℝ := fun i j => ex33Fn k p i j

/-- The truncated birth–death chain is a transition matrix for `0 ≤ p ≤ 1`. -/
theorem ex33_mem {k : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ex33 k p ∈ rowStochastic ℝ (Fin k) := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · simp only [ex33, ex33Fn]
    have : 0 ≤ 1 - p := by linarith
    split_ifs <;> linarith
  · simp only [ex33]
    rw [Fin.sum_univ_eq_sum_range (fun b => ex33Fn k p i b) k]
    have hi := i.2
    set a := (i : ℕ)
    simp only [ex33Fn, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range]
    have h2 : ∑ x ∈ Finset.range k, (if x + 1 = a then 1 - p else 0) =
        if a = 0 then 0 else 1 - p := by
      rcases Nat.eq_zero_or_pos a with h | h
      · simp [h]
      · obtain ⟨m, hm⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
        rw [hm]
        simp only [Nat.add_right_cancel_iff, Finset.sum_ite_eq', Finset.mem_range]
        simp [show m < k by omega]
    rw [h2]
    split_ifs <;> first | (exfalso; omega) | ring

/-- The stationary distribution of Exercise 3 for `ρ ≠ 1`. -/
noncomputable def ex33Dist (k : ℕ) (ρ : ℝ) (i : Fin k) : ℝ := (1 - ρ) * ρ ^ (i : ℕ) / (1 - ρ ^ k)

/-- The truncated chain is irreducible for `0 < p < 1` (and `k ≥ 1`). -/
theorem ex33_irreducible {k : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    mc_IsIrreducible (ex33 k p) := by
  have hP := ex33_mem (k := k) hp0.le hp1.le
  have hq : 0 < 1 - p := by linarith
  have hup : ∀ i j : Fin k, (j : ℕ) = i + 1 → mc_Accessible (ex33 k p) i j := fun i j h =>
    mc_accessible_of_pos (by
      simp only [ex33, ex33Fn, h, ite_true, show (i : ℕ) + 1 + 1 ≠ i by omega,
        show (i : ℕ) + 1 ≠ i by omega, ite_false]; linarith)
  have hdown : ∀ i j : Fin k, (i : ℕ) = j + 1 → mc_Accessible (ex33 k p) i j := fun i j h =>
    mc_accessible_of_pos (by
      simp only [ex33, ex33Fn, h, ite_true, show (j : ℕ) ≠ j + 1 + 1 by omega,
        show (j : ℕ) ≠ j + 1 by omega, ite_false]; linarith)
  -- states with larger value are reached by steps up, smaller by steps down
  have hupk : ∀ d (i j : Fin k), (j : ℕ) = i + d + 1 → mc_Accessible (ex33 k p) i j := by
    intro d
    induction d with
    | zero => exact fun i j h => hup i j (by omega)
    | succ d ih =>
      intro i j h
      exact (ih i ⟨i + d + 1, by omega⟩ rfl).trans hP (hup _ j (by simp; omega))
  have hdownk : ∀ d (i j : Fin k), (i : ℕ) = j + d + 1 → mc_Accessible (ex33 k p) i j := by
    intro d
    induction d with
    | zero => exact fun i j h => hdown i j (by omega)
    | succ d ih =>
      intro i j h
      exact (hdown i ⟨j + d + 1, by omega⟩ (by simp; omega)).trans hP (ih _ j rfl)
  intro i j
  by_cases hij : i = j
  · exact Or.inl hij
  refine Or.inr ⟨?_, ?_⟩
  · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · exact hupk ((j : ℕ) - i - 1) i j (by omega)
    · exact hdownk ((i : ℕ) - j - 1) i j (by omega)
  · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · exact hdownk ((j : ℕ) - i - 1) j i (by omega)
    · exact hupk ((i : ℕ) - j - 1) j i (by omega)

/-- Detailed balance for the truncated chain, for any `μ` with `μ_{a+1} q = μ_a p`. -/
theorem ex33_detailed_balance {k : ℕ} {p : ℝ} {μ : Fin k → ℝ}
    (h : ∀ i j : Fin k, (j : ℕ) = i + 1 → μ i * p = μ j * (1 - p)) (i j : Fin k) :
    μ i * ex33 k p i j = μ j * ex33 k p j i := by
  by_cases hij : i = j
  · rw [hij]
  have hv : (i : ℕ) ≠ j := Fin.val_ne_of_ne hij
  simp only [ex33, ex33Fn, show (j : ℕ) ≠ i by omega, show (i : ℕ) ≠ j by omega, ite_false,
    add_zero]
  by_cases h1 : (j : ℕ) = i + 1
  · simp only [h1, ite_true, show (i : ℕ) + 1 + 1 ≠ i by omega, ite_false, add_zero,
      show (i : ℕ) ≠ i + 1 + 1 by omega, zero_add]
    exact h i j h1
  · by_cases h2 : (i : ℕ) = j + 1
    · simp only [h2, ite_true, show (j : ℕ) + 1 + 1 ≠ j by omega, ite_false, add_zero,
        show (j : ℕ) ≠ j + 1 + 1 by omega, zero_add]
      exact (h j i h2).symm
    · simp only [h1, h2, ite_false, add_zero, show ¬ ((j : ℕ) + 1 = i) by omega,
        show ¬ ((i : ℕ) + 1 = j) by omega, mul_zero]

/-- **Exercise 3** (Miao, pp. 97–98): for `0 < p < 1` with `ρ = p/q ≠ 1` and `k ≥ 1`, the
truncated birth–death chain has the unique stationary distribution
`πᵢ = (1 − ρ)ρⁱ/(1 − ρᵏ)`. -/
theorem ex_3_3 {k : ℕ} (hk : 0 < k) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hρ : p / (1 - p) ≠ 1) :
    mc_IsStationary (ex33 k p) (ex33Dist k (p / (1 - p))) ∧
      ∀ ν, mc_IsStationary (ex33 k p) ν → ν = ex33Dist k (p / (1 - p)) := by
  have hP := ex33_mem (k := k) hp0.le hp1.le
  have hq : 0 < 1 - p := by linarith
  set ρ := p / (1 - p) with hρdef
  have hρ0 : 0 < ρ := div_pos hp0 hq
  have hρq : ρ * (1 - p) = p := div_mul_cancel₀ p hq.ne'
  have hρk : 1 - ρ ^ k ≠ 0 := by
    intro h
    have : ρ ^ k = 1 := by linarith
    exact hρ ((pow_eq_one_iff_of_nonneg hρ0.le hk.ne').1 this)
  have hstat : mc_IsStationary (ex33 k p) (ex33Dist k ρ) := by
    refine mc_isStationary_of_detailed_balance hP (fun i => ?_) ?_ ?_
    · simp only [ex33Dist]
      rcases lt_or_gt_of_ne hρ with h | h
      · have h1 : 0 < 1 - ρ ^ k := by
          have := pow_lt_one₀ hρ0.le h hk.ne'
          linarith
        exact div_nonneg (mul_nonneg (by linarith) (pow_nonneg hρ0.le _)) h1.le
      · have h1 : 1 - ρ ^ k < 0 := by
          have := one_lt_pow₀ h hk.ne'
          linarith
        exact div_nonneg_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (by linarith)
          (pow_nonneg hρ0.le _)) h1.le
    · simp only [ex33Dist, ← Finset.sum_div, ← Finset.mul_sum]
      rw [Fin.sum_univ_eq_sum_range (fun i => ρ ^ i) k, geom_sum_eq hρ]
      have h1 : ρ - 1 ≠ 0 := sub_ne_zero.2 hρ
      field_simp
      ring
    · refine ex33_detailed_balance fun i j h => ?_
      simp only [ex33Dist, h, pow_succ]
      field_simp
      linarith [hρq]
  exact ⟨hstat, fun ν hν => mc_stationary_unique_of_irreducible hP (ex33_irreducible hp0 hp1)
    hν hstat⟩

/-- **Exercise 3** (Miao, p. 98), the case `ρ = 1` (`p = 1/2`): the stationary distribution is
`πᵢ = 1/k`. -/
theorem ex_3_3_half {k : ℕ} (hk : 0 < k) :
    mc_IsStationary (ex33 k (1 / 2)) (fun _ => (1 : ℝ) / k) ∧
      ∀ ν, mc_IsStationary (ex33 k (1 / 2)) ν → ν = fun _ => (1 : ℝ) / k := by
  have hP := ex33_mem (k := k) (p := 1 / 2) (by norm_num) (by norm_num)
  have hstat : mc_IsStationary (ex33 k (1 / 2)) (fun _ => (1 : ℝ) / k) := by
    refine mc_isStationary_of_detailed_balance hP (fun _ => by positivity) ?_
      (ex33_detailed_balance fun _ _ _ => by norm_num)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  exact ⟨hstat, fun ν hν => mc_stationary_unique_of_irreducible hP
    (ex33_irreducible (by norm_num) (by norm_num)) hν hstat⟩

/-- Miao, p. 98: for `ρ < 1`, `πᵢ → (1 − ρ)ρⁱ` as `k → ∞`. -/
theorem ex_3_3_limit_lt {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (i : ℕ) :
    Tendsto (fun k : ℕ => (1 - ρ) * ρ ^ i / (1 - ρ ^ k)) atTop (𝓝 ((1 - ρ) * ρ ^ i)) := by
  have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_sub 1)
  simp only [sub_zero] at h
  have h3 : Tendsto (fun k : ℕ => (1 - ρ) * ρ ^ i / (1 - ρ ^ k)) atTop
      (𝓝 ((1 - ρ) * ρ ^ i / 1)) := tendsto_const_nhds.div h one_ne_zero
  rwa [div_one] at h3

/-- Miao, p. 98: for `ρ > 1`, `πᵢ → 0` as `k → ∞`. -/
theorem ex_3_3_limit_gt {ρ : ℝ} (hρ1 : 1 < ρ) (i : ℕ) :
    Tendsto (fun k : ℕ => (1 - ρ) * ρ ^ i / (1 - ρ ^ k)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k : ℕ => 1 - ρ ^ k) atTop atBot :=
    tendsto_atBot_add_const_left _ 1 (tendsto_neg_atTop_atBot.comp
      (tendsto_pow_atTop_atTop_of_one_lt hρ1))
  have h2 := (tendsto_inv_atBot_zero.comp h1).const_mul ((1 - ρ) * ρ ^ i)
  simpa [div_eq_mul_inv] using h2

/-! ### Exercise 6 -/

/-- **Exercise 6** (Miao, p. 114), without aperiodicity: an irreducible doubly stochastic chain
on `N` states has the unique stationary distribution `πᵢ = 1/N`. -/
theorem ex_3_6_irreducible [Nonempty S] (hP : P ∈ rowStochastic ℝ S)
    (hcol : ∀ j, ∑ i, P i j = 1) (hirr : mc_IsIrreducible P) :
    mc_IsStationary P (fun _ => (1 : ℝ) / Fintype.card S) ∧
      ∀ ν, mc_IsStationary P ν → ν = fun _ => (1 : ℝ) / Fintype.card S := by
  have hN : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hstat : mc_IsStationary P (fun _ => (1 : ℝ) / Fintype.card S) := by
    refine ⟨fun _ => by positivity, ?_, funext fun j => ?_⟩
    · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    · rw [mc_vecMul_apply, ← Finset.mul_sum, hcol, mul_one]
  exact ⟨hstat, fun ν hν => mc_stationary_unique_of_irreducible hP hirr hν hstat⟩

/-- **Exercise 6** (Miao, p. 114): a doubly stochastic, irreducible and aperiodic chain on `N`
states has the stationary distribution `πᵢ = 1/N`; it is the unique one, and
`p⁽ᵗ⁾ᵢⱼ → 1/N` for all `i, j` (Theorems 3.1.3 and 3.1.4). -/
theorem ex_3_6 [Nonempty S] (hP : P ∈ rowStochastic ℝ S) (hcol : ∀ j, ∑ i, P i j = 1)
    (hirr : mc_IsIrreducible P) (hap : mc_IsAperiodicChain P) :
    mc_IsStationary P (fun _ => (1 : ℝ) / Fintype.card S) ∧
      (∀ ν, mc_IsStationary P ν → ν = fun _ => (1 : ℝ) / Fintype.card S) ∧
      ∀ i j, Tendsto (fun t => (P ^ t) i j) atTop (𝓝 ((1 : ℝ) / Fintype.card S)) := by
  obtain ⟨hstat, huniq⟩ := ex_3_6_irreducible hP hcol hirr
  obtain ⟨k₀, hk₀, hpos⟩ := (theorem_3_1_4 hP).1 ⟨hirr, hap⟩
  obtain ⟨μ, hμ, -, hlim, -⟩ := theorem_3_1_3 hP ⟨k₀, hk₀, hpos k₀ le_rfl⟩
  have hμeq := huniq μ hμ
  refine ⟨hstat, huniq, fun i j => ?_⟩
  have := hlim i j
  rwa [hμeq] at this

end Miao.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Countable-state Markov chains: transitions, periods, first passages, recurrence

Miao, §3.1 and §3.1.3, pp. 86–99. The state space `S` is arbitrary (countable in the book); a
transition matrix is `P : S → S → [0, ∞]` with rows summing to one (`mc_IsStochasticE`), and
matrices are multiplied with `[0, ∞]`-valued sums (`mc_mulE`), so that every rearrangement of
sums is free. The `n`-step transition probabilities are `mc_powE P n`.

**Path probabilities.** The probabilities of events about the path are computed by products
along paths (the cylinder probabilities of `ChainProcess`). The **first-passage probability**
`f⁽ⁿ⁺¹⁾ₐⱼ = Pr(X₁ ≠ j, …, Xₙ ≠ j, Xₙ₊₁ = j | X₀ = a)` is the sum of these products over paths
avoiding `j` before time `n + 1`: `mc_fpE P j n a = ((PDⱼ)ⁿP)ₐⱼ`, with `PDⱼ` the matrix `P`
with column `j` replaced by zeros (`mc_tabooE`). Hence, for the first return time
`τⱼ = min {k ≥ 1 : Xₖ = j}`,
`Pr(τⱼ < ∞ | X₀ = a) = Σₙ f⁽ⁿ⁺¹⁾ₐⱼ` (`mc_hitE`) and
`E[τⱼ | X₀ = j] = Σₙ (n + 1) f⁽ⁿ⁺¹⁾ⱼⱼ` (`mc_meanRetE`, the expectation when `τⱼ < ∞` almost
surely, which is the case in which Definition 3.1.6 uses it).

* (3.1) for countable chains (`eq_3_1_countable`) and `mc_powE_row_sum`.
* **Definition 3.1.1**, **Definition 3.1.2**, **Definition 3.1.4** for countable chains:
  `mc_AccessibleE`, `mc_CommunicateE`, `mc_IsIrreducibleE`, `mc_periodE`;
  `mc_isIrreducibleE_iff`.
* **Theorem 3.1.2** (p. 93) for countable chains (`theorem_3_1_2_countable`).
* **Theorem 3.1.4**, countable version (p. 99, `theorem_3_1_4_countable`): irreducible and
  aperiodic iff for all `i, j` there is `k₀` with `p⁽ᵏ⁾ᵢⱼ > 0` for `k ≥ k₀`; the uniform `k₀`
  of the finite case fails (`theorem_3_1_4_countable_counterexample` in `ChainCountableExamples`).
* **Definition 3.1.6** (p. 98): `mc_IsTransientE` (`Pr(τᵢ < ∞ | X₀ = i) < 1`),
  `mc_IsRecurrentE`, `mc_IsPositiveRecurrentE`, `mc_IsNullRecurrentE`.
* The first-step recursion `mc_fpE_succ`, `mc_hitE_le_one` (`Pr(τⱼ < ∞) ≤ 1`), the
  **first-entrance decomposition** `mc_first_entrance`
  (`p⁽ⁿ⁺¹⁾ₐⱼ = Σ_{m ≤ n} f⁽ᵐ⁺¹⁾ₐⱼ p⁽ⁿ⁻ᵐ⁾ⱼⱼ`), and the generating-function identity
  `mc_visits_eq` (`Σₙ p⁽ⁿ⁺¹⁾ₐⱼ = Pr(τⱼ < ∞ | X₀ = a)(1 + Σₙ p⁽ⁿ⁺¹⁾ⱼⱼ)`).
* `mc_isTransientE_iff`: `i` is transient iff `Σₙ p⁽ⁿ⁾ᵢᵢ < ∞`.
* **Theorem 3.1.1(a)** for countable chains with Definition 3.1.6 (p. 98,
  `theorem_3_1_1a_countable`): recurrence and transience are class properties.
-/

namespace Miao.MarkovProcesses

open Filter Topology
open scoped ENNReal

variable {S : Type*}

/-! ### Matrices with entries in `[0, ∞]` -/

/-- A transition matrix on a (countable) state space: the rows sum to one. -/
def mc_IsStochasticE (P : S → S → ℝ≥0∞) : Prop := ∀ i, ∑' j, P i j = 1

/-- The product of two `[0, ∞]`-valued matrices. -/
noncomputable def mc_mulE (A B : S → S → ℝ≥0∞) : S → S → ℝ≥0∞ := fun i k => ∑' j, A i j * B j k

/-- The identity matrix. -/
noncomputable def mc_idE [DecidableEq S] : S → S → ℝ≥0∞ := fun i j => if i = j then 1 else 0

/-- The `n`-step transition matrix `Pⁿ`, `Pⁿ⁺¹ = P Pⁿ`. -/
noncomputable def mc_powE [DecidableEq S] (P : S → S → ℝ≥0∞) : ℕ → S → S → ℝ≥0∞
  | 0 => mc_idE
  | n + 1 => mc_mulE P (mc_powE P n)

/-- Matrix multiplication is associative. -/
theorem mc_mulE_assoc (A B C : S → S → ℝ≥0∞) :
    mc_mulE (mc_mulE A B) C = mc_mulE A (mc_mulE B C) := by
  funext i l
  simp only [mc_mulE, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, mul_assoc]
  exact ENNReal.tsum_comm

/-- `1 · A = A`. -/
theorem mc_idE_mulE [DecidableEq S] (A : S → S → ℝ≥0∞) : mc_mulE mc_idE A = A := by
  funext i k
  simp only [mc_mulE, mc_idE, ite_mul, one_mul, zero_mul]
  rw [tsum_eq_single i fun j hj => by simp [Ne.symm hj]]
  simp

/-- `A · 1 = A`. -/
theorem mc_mulE_idE [DecidableEq S] (A : S → S → ℝ≥0∞) : mc_mulE A mc_idE = A := by
  funext i k
  simp only [mc_mulE, mc_idE, mul_ite, mul_one, mul_zero]
  rw [tsum_eq_single k fun j hj => by simp [hj]]
  simp

/-- `P¹ = P`. -/
theorem mc_powE_one [DecidableEq S] (P : S → S → ℝ≥0∞) : mc_powE P 1 = P := by
  simp [mc_powE, mc_mulE_idE]

/-- `Pᵐ⁺ⁿ = PᵐPⁿ`. -/
theorem mc_powE_add [DecidableEq S] (P : S → S → ℝ≥0∞) (m n : ℕ) :
    mc_powE P (m + n) = mc_mulE (mc_powE P m) (mc_powE P n) := by
  induction m with
  | zero => simp [mc_powE, mc_idE_mulE]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega]
    simp only [mc_powE, ih, mc_mulE_assoc]

/-- `Pⁿ⁺¹ = PⁿP`. -/
theorem mc_powE_succ' [DecidableEq S] (P : S → S → ℝ≥0∞) (n : ℕ) :
    mc_powE P (n + 1) = mc_mulE (mc_powE P n) P := by
  rw [mc_powE_add, mc_powE_one]

/-- Miao, (3.1), p. 87, for countable chains: `p⁽ᵐ⁺ᵏ⁾ᵢⱼ = Σᵣ p⁽ᵏ⁾ᵢᵣ p⁽ᵐ⁾ᵣⱼ`. -/
theorem eq_3_1_countable [DecidableEq S] (P : S → S → ℝ≥0∞) (m k : ℕ) (i j : S) :
    mc_powE P (m + k) i j = ∑' r, mc_powE P k i r * mc_powE P m r j := by
  rw [add_comm, mc_powE_add]; rfl

/-- A consequence of (3.1): `p⁽ᵐ⁺ⁿ⁾ᵢₖ ≥ p⁽ᵐ⁾ᵢⱼ p⁽ⁿ⁾ⱼₖ`. -/
theorem mc_powE_add_ge [DecidableEq S] (P : S → S → ℝ≥0∞) (m n : ℕ) (i j k : S) :
    mc_powE P m i j * mc_powE P n j k ≤ mc_powE P (m + n) i k := by
  rw [mc_powE_add]
  exact ENNReal.le_tsum (f := fun r => mc_powE P m i r * mc_powE P n r k) j

/-- Positive transitions compose. -/
theorem mc_powE_add_pos [DecidableEq S] (P : S → S → ℝ≥0∞) {m n : ℕ} {i j k : S}
    (h1 : 0 < mc_powE P m i j) (h2 : 0 < mc_powE P n j k) : 0 < mc_powE P (m + n) i k :=
  lt_of_lt_of_le (ENNReal.mul_pos h1.ne' h2.ne') (mc_powE_add_ge P m n i j k)

/-- The rows of `Pⁿ` sum to one. -/
theorem mc_powE_row_sum [DecidableEq S] {P : S → S → ℝ≥0∞} (hP : mc_IsStochasticE P) (n : ℕ)
    (i : S) : ∑' j, mc_powE P n i j = 1 := by
  induction n generalizing i with
  | zero =>
    simp only [mc_powE, mc_idE]
    rw [tsum_eq_single i fun j hj => by simp [Ne.symm hj]]
    simp
  | succ n ih =>
    simp only [mc_powE, mc_mulE]
    rw [ENNReal.tsum_comm]
    simp only [ENNReal.tsum_mul_left, ih, mul_one, hP i]

/-- Entries of `Pⁿ` are at most one. -/
theorem mc_powE_le_one [DecidableEq S] {P : S → S → ℝ≥0∞} (hP : mc_IsStochasticE P) (n : ℕ)
    (i j : S) : mc_powE P n i j ≤ 1 := by
  rw [← mc_powE_row_sum hP n i]
  exact ENNReal.le_tsum j

/-- Entries of a transition matrix are at most one. -/
theorem mc_le_one_of_stochasticE {P : S → S → ℝ≥0∞} (hP : mc_IsStochasticE P) (i j : S) :
    P i j ≤ 1 := by
  rw [← hP i]; exact ENNReal.le_tsum j

/-! ### Definitions 3.1.1, 3.1.2 and 3.1.4 for countable chains -/

/-- **Definition 3.1.1** (Miao, p. 90): `j` is accessible from `i` if `p⁽ᵐ⁾ᵢⱼ > 0`, `m ≥ 1`. -/
def mc_AccessibleE [DecidableEq S] (P : S → S → ℝ≥0∞) (i j : S) : Prop :=
  ∃ m, 1 ≤ m ∧ 0 < mc_powE P m i j

/-- **Definition 3.1.1** (Miao, p. 90): `i ↔ j`, with `i ↔ i` by convention. -/
def mc_CommunicateE [DecidableEq S] (P : S → S → ℝ≥0∞) (i j : S) : Prop :=
  i = j ∨ (mc_AccessibleE P i j ∧ mc_AccessibleE P j i)

/-- **Definition 3.1.2** (Miao, p. 90): irreducibility. -/
def mc_IsIrreducibleE [DecidableEq S] (P : S → S → ℝ≥0∞) : Prop := ∀ i j, mc_CommunicateE P i j

/-- Accessibility is transitive. -/
theorem mc_AccessibleE.trans [DecidableEq S] {P : S → S → ℝ≥0∞} {i j k : S}
    (h1 : mc_AccessibleE P i j) (h2 : mc_AccessibleE P j k) : mc_AccessibleE P i k := by
  obtain ⟨m, hm, hm'⟩ := h1
  obtain ⟨n, hn, hn'⟩ := h2
  exact ⟨m + n, by omega, mc_powE_add_pos P hm' hn'⟩

/-- A positive one-step transition gives accessibility. -/
theorem mc_accessibleE_of_pos [DecidableEq S] {P : S → S → ℝ≥0∞} {i j : S} (h : 0 < P i j) :
    mc_AccessibleE P i j :=
  ⟨1, le_rfl, by rwa [mc_powE_one]⟩

/-- Miao, p. 90, countable chains: irreducibility iff every state is accessible from every
state (including itself). -/
theorem mc_isIrreducibleE_iff [DecidableEq S] {P : S → S → ℝ≥0∞} (hP : mc_IsStochasticE P) :
    mc_IsIrreducibleE P ↔ ∀ i j, mc_AccessibleE P i j := by
  constructor
  · intro h i j
    by_cases hij : i = j
    · subst hij
      obtain ⟨k, hk⟩ : ∃ k, 0 < P i k := by
        by_contra hne
        push Not at hne
        have : ∑' k, P i k = 0 := ENNReal.tsum_eq_zero.2 fun k => nonpos_iff_eq_zero.1 (hne k)
        rw [hP i] at this
        exact one_ne_zero this
      by_cases hki : k = i
      · subst hki; exact mc_accessibleE_of_pos hk
      · rcases h k i with h' | ⟨h', -⟩
        · exact absurd h' hki
        · exact (mc_accessibleE_of_pos hk).trans h'
    · rcases h i j with h' | ⟨h', -⟩
      · exact absurd h' hij
      · exact h'
  · exact fun h i j => Or.inr ⟨h i j, h j i⟩

/-- The return times of `i`. -/
def mc_returnSetE [DecidableEq S] (P : S → S → ℝ≥0∞) (i : S) : Set ℕ :=
  {m | 1 ≤ m ∧ 0 < mc_powE P m i i}

/-- **Definition 3.1.4** (Miao, p. 93), countable chains: the period of `i`. -/
noncomputable def mc_periodE [DecidableEq S] (P : S → S → ℝ≥0∞) (i : S) : ℕ :=
  mc_setGcd (mc_returnSetE P i)

/-- Return times are closed under addition. -/
theorem mc_returnSetE_isAddClosed [DecidableEq S] (P : S → S → ℝ≥0∞) (i : S) :
    mc_IsAddClosed (mc_returnSetE P i) := by
  rintro a ⟨ha, ha'⟩ b ⟨-, hb'⟩
  exact ⟨by omega, mc_powE_add_pos P ha' hb'⟩

/-- **Theorem 3.1.2** (Miao, p. 93), countable chains: communicating states have the same
period. -/
theorem theorem_3_1_2_countable [DecidableEq S] (P : S → S → ℝ≥0∞) {i j : S}
    (hij : mc_CommunicateE P i j) : mc_periodE P i = mc_periodE P j := by
  rcases hij with rfl | ⟨⟨r, hr, hr'⟩, ⟨s, hs, hs'⟩⟩
  · rfl
  refine mc_setGcd_eq_of_shift (mc_returnSetE_isAddClosed P i) (mc_returnSetE_isAddClosed P j)
    (n := r + s) (by omega) ⟨by omega, mc_powE_add_pos P hr' hs'⟩ ?_ ?_ ?_
  · refine ⟨by omega, ?_⟩
    have := mc_powE_add_pos P hs' hr'
    rwa [add_comm s r] at this
  · rintro t ⟨ht, ht'⟩
    refine ⟨by omega, ?_⟩
    have := mc_powE_add_pos P (mc_powE_add_pos P hr' ht') hs'
    rwa [show r + t + s = r + s + t by omega] at this
  · rintro t ⟨ht, ht'⟩
    refine ⟨by omega, ?_⟩
    have := mc_powE_add_pos P (mc_powE_add_pos P hs' ht') hr'
    rwa [show s + t + r = r + s + t by omega] at this

/-- **Theorem 3.1.4** (Miao, p. 99: "Theorem 3.1.4 also applies"), countable chains, corrected:
a chain is irreducible and aperiodic iff for every pair `i, j` there is `k₀` with `p⁽ᵏ⁾ᵢⱼ > 0`
for all `k ≥ k₀`. The `k₀` cannot be chosen uniformly in `i, j`
(`theorem_3_1_4_countable_counterexample`). -/
theorem theorem_3_1_4_countable [DecidableEq S] {P : S → S → ℝ≥0∞} (hP : mc_IsStochasticE P) :
    (mc_IsIrreducibleE P ∧ ∀ i, mc_periodE P i = 1) ↔
      ∀ i j, ∃ k₀, 0 < k₀ ∧ ∀ k ≥ k₀, 0 < mc_powE P k i j := by
  constructor
  · rintro ⟨hirr, hap⟩ i j
    have hacc := (mc_isIrreducibleE_iff hP).1 hirr
    obtain ⟨m, hm, hm'⟩ := hacc j j
    obtain ⟨N, hN⟩ := mc_eventually_mem_of_setGcd_eq_one (mc_returnSetE_isAddClosed P j)
      ⟨hm, hm'⟩ hm (hap j)
    obtain ⟨r, hr, hr'⟩ := hacc i j
    refine ⟨N + r + 1, by omega, fun k hk => ?_⟩
    have := mc_powE_add_pos P hr' (hN (k - r) (by omega)).2
    rwa [show r + (k - r) = k by omega] at this
  · intro h
    refine ⟨(mc_isIrreducibleE_iff hP).2 fun i j => ?_, fun i => ?_⟩
    · obtain ⟨k₀, hk₀, hk⟩ := h i j
      exact ⟨k₀, hk₀, hk k₀ le_rfl⟩
    · obtain ⟨k₀, hk₀, hk⟩ := h i i
      have hS := mc_returnSetE_isAddClosed P i
      have h1 : k₀ ∈ mc_returnSetE P i := ⟨hk₀, hk k₀ le_rfl⟩
      have h2 : k₀ + 1 ∈ mc_returnSetE P i := ⟨by omega, hk (k₀ + 1) (by omega)⟩
      exact Nat.dvd_one.1 ((Nat.dvd_add_right (mc_setGcd_dvd hS h1 hk₀ h1)).1
        (mc_setGcd_dvd hS h1 hk₀ h2))

/-! ### First passages -/

/-- The taboo matrix `PDⱼ`: `P` with the column of `j` replaced by zeros (paths may not visit
`j`). -/
noncomputable def mc_tabooE [DecidableEq S] (P : S → S → ℝ≥0∞) (j : S) : S → S → ℝ≥0∞ :=
  fun a b => if b = j then 0 else P a b

/-- The **first-passage probability** `f⁽ⁿ⁺¹⁾ₐⱼ = Pr(X₁ ≠ j, …, Xₙ ≠ j, Xₙ₊₁ = j | X₀ = a)`,
the sum over paths avoiding `j` before time `n + 1` of the path products: `((PDⱼ)ⁿP)ₐⱼ`. -/
noncomputable def mc_fpE [DecidableEq S] (P : S → S → ℝ≥0∞) (j : S) (n : ℕ) (a : S) : ℝ≥0∞ :=
  mc_mulE (mc_powE (mc_tabooE P j) n) P a j

/-- `Pr(τⱼ < ∞ | X₀ = a) = Σₙ f⁽ⁿ⁺¹⁾ₐⱼ`, the probability of ever reaching `j` (at a time
`≥ 1`). -/
noncomputable def mc_hitE [DecidableEq S] (P : S → S → ℝ≥0∞) (a j : S) : ℝ≥0∞ :=
  ∑' n, mc_fpE P j n a

/-- The mean return time `E[τⱼ | X₀ = j] = Σₙ (n + 1) f⁽ⁿ⁺¹⁾ⱼⱼ` (when `τⱼ < ∞` a.s.). -/
noncomputable def mc_meanRetE [DecidableEq S] (P : S → S → ℝ≥0∞) (j : S) : ℝ≥0∞ :=
  ∑' n : ℕ, ((n : ℝ≥0∞) + 1) * mc_fpE P j n j

/-- The expected number of visits to `j` at times `≥ 1`, `Σₙ p⁽ⁿ⁺¹⁾ₐⱼ`. -/
noncomputable def mc_visitsE [DecidableEq S] (P : S → S → ℝ≥0∞) (a j : S) : ℝ≥0∞ :=
  ∑' n, mc_powE P (n + 1) a j

/-- **Definition 3.1.6** (Miao, p. 98): `i` is **transient** if `Pr(τᵢ < ∞ | X₀ = i) < 1`. -/
def mc_IsTransientE [DecidableEq S] (P : S → S → ℝ≥0∞) (i : S) : Prop := mc_hitE P i i < 1

/-- `i` is **recurrent** if `Pr(τᵢ < ∞ | X₀ = i) = 1`. -/
def mc_IsRecurrentE [DecidableEq S] (P : S → S → ℝ≥0∞) (i : S) : Prop := mc_hitE P i i = 1

/-- **Definition 3.1.6** (Miao, p. 98): `i` is **positive recurrent** if
`Pr(τᵢ < ∞ | X₀ = i) = 1` and `E[τᵢ | X₀ = i] < ∞`. -/
def mc_IsPositiveRecurrentE [DecidableEq S] (P : S → S → ℝ≥0∞) (i : S) : Prop :=
  mc_hitE P i i = 1 ∧ mc_meanRetE P i < ∞

/-- **Definition 3.1.6** (Miao, p. 98): `i` is **null recurrent** if `Pr(τᵢ < ∞ | X₀ = i) = 1`
and `E[τᵢ | X₀ = i] = ∞`. -/
def mc_IsNullRecurrentE [DecidableEq S] (P : S → S → ℝ≥0∞) (i : S) : Prop :=
  mc_hitE P i i = 1 ∧ mc_meanRetE P i = ∞

/-- Splitting a sum at `j`. -/
theorem mc_tsum_split [DecidableEq S] (f : S → ℝ≥0∞) (j : S) :
    ∑' x, f x = f j + ∑' x, if x = j then 0 else f x := by
  convert ENNReal.tsum_eq_add_tsum_ite (f := f) j

/-- The taboo sum: `Σ_b (PDⱼ)ₐ_b g_b = Σ_{b ≠ j} pₐ_b g_b`. -/
theorem mc_tsum_taboo [DecidableEq S] (P : S → S → ℝ≥0∞) (j a : S) (g : S → ℝ≥0∞) :
    ∑' b, mc_tabooE P j a b * g b = ∑' b, if b = j then 0 else P a b * g b := by
  refine tsum_congr fun b => ?_
  by_cases hb : b = j <;> simp [mc_tabooE, hb]

/-- The **first-step recursion**: `f⁽¹⁾ₐⱼ = pₐⱼ`. -/
theorem mc_fpE_zero [DecidableEq S] (P : S → S → ℝ≥0∞) (j a : S) : mc_fpE P j 0 a = P a j := by
  simp [mc_fpE, mc_powE, mc_idE_mulE]

/-- The **first-step recursion**: `f⁽ⁿ⁺²⁾ₐⱼ = Σ_{b ≠ j} pₐ_b f⁽ⁿ⁺¹⁾_bⱼ`. -/
theorem mc_fpE_succ [DecidableEq S] (P : S → S → ℝ≥0∞) (j : S) (n : ℕ) (a : S) :
    mc_fpE P j (n + 1) a = ∑' b, if b = j then 0 else P a b * mc_fpE P j n b := by
  rw [← mc_tsum_taboo]
  simp only [mc_fpE, mc_powE, mc_mulE_assoc]
  rfl

/-- Miao, p. 98: `Pr(τⱼ < ∞ | X₀ = a) ≤ 1`. -/
theorem mc_hitE_le_one [DecidableEq S] {P : S → S → ℝ≥0∞} (hP : mc_IsStochasticE P) (a j : S) :
    mc_hitE P a j ≤ 1 := by
  have key : ∀ N a, ∑ n ∈ Finset.range N, mc_fpE P j n a ≤ 1 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      intro a
      rw [Finset.sum_range_succ', mc_fpE_zero]
      simp only [mc_fpE_succ]
      rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
      calc ∑' b, ∑ n ∈ Finset.range N, (if b = j then 0 else P a b * mc_fpE P j n b) + P a j
          = ∑' b, (if b = j then 0 else P a b * ∑ n ∈ Finset.range N, mc_fpE P j n b) +
              P a j := by
            congr 1
            refine tsum_congr fun b => ?_
            by_cases hb : b = j <;> simp [hb, Finset.mul_sum]
        _ ≤ ∑' b, (if b = j then 0 else P a b) + P a j := by
            gcongr with b
            by_cases hb : b = j
            · simp [hb]
            · simp only [hb, ite_false]
              exact mul_le_of_le_one_right' (ih b)
        _ = 1 := by
            rw [add_comm, ← mc_tsum_split]
            exact hP a
  exact ENNReal.tsum_le_of_sum_range_le fun N => key N a

/-- The **first-entrance decomposition**: `p⁽ⁿ⁺¹⁾ₐⱼ = Σ_{m ≤ n} f⁽ᵐ⁺¹⁾ₐⱼ p⁽ⁿ⁻ᵐ⁾ⱼⱼ`. -/
theorem mc_first_entrance [DecidableEq S] (P : S → S → ℝ≥0∞) (j : S) (n : ℕ) (a : S) :
    mc_powE P (n + 1) a j =
      ∑ m ∈ Finset.range (n + 1), mc_fpE P j m a * mc_powE P (n - m) j j := by
  induction n generalizing a with
  | zero => simp [mc_fpE_zero, mc_powE, mc_idE, mc_mulE_idE]
  | succ n ih =>
    rw [Finset.sum_range_succ', mc_fpE_zero, Nat.sub_zero]
    simp only [mc_fpE_succ, Nat.add_sub_add_right]
    have h1 : mc_powE P (n + 1 + 1) a j =
        P a j * mc_powE P (n + 1) j j +
          ∑' b, if b = j then 0 else P a b * mc_powE P (n + 1) b j := by
      rw [mc_powE]
      exact mc_tsum_split (fun b => P a b * mc_powE P (n + 1) b j) j
    rw [h1, add_comm]
    congr 1
    simp only [ih, Finset.mul_sum, ← ENNReal.tsum_mul_right]
    rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
    refine tsum_congr fun b => ?_
    by_cases hb : b = j
    · simp [hb]
    · simp only [hb, ite_false, mul_assoc]

/-- `f⁽ⁿ⁺¹⁾ₐⱼ ≤ p⁽ⁿ⁺¹⁾ₐⱼ`. -/
theorem mc_fpE_le_powE [DecidableEq S] (P : S → S → ℝ≥0∞) (j : S) (n : ℕ) (a : S) :
    mc_fpE P j n a ≤ mc_powE P (n + 1) a j := by
  rw [mc_first_entrance]
  calc mc_fpE P j n a = mc_fpE P j n a * mc_powE P (n - n) j j := by
        simp [mc_powE, mc_idE]
    _ ≤ _ := Finset.single_le_sum (f := fun m => mc_fpE P j m a * mc_powE P (n - m) j j)
        (fun _ _ => bot_le) (Finset.self_mem_range_succ n)

/-- The Cauchy product of two `[0, ∞]`-valued series. -/
theorem mc_tsum_cauchy (a b : ℕ → ℝ≥0∞) :
    ∑' n, ∑ k ∈ Finset.range (n + 1), a k * b (n - k) = (∑' n, a n) * ∑' n, b n := by
  simp_rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun k l => a k * b l]
  rw [← ENNReal.tsum_mul_right]
  simp_rw [← ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_prod (f := fun k l => a k * b l),
    ← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun n => ?_
  rw [tsum_fintype]
  exact (Finset.sum_coe_sort (Finset.antidiagonal n) fun kl => a kl.1 * b kl.2).symm

/-- Miao, p. 98 (generating functions): `Σₙ p⁽ⁿ⁺¹⁾ₐⱼ = Pr(τⱼ < ∞ | X₀ = a)(1 + Σₙ p⁽ⁿ⁺¹⁾ⱼⱼ)`. -/
theorem mc_visits_eq [DecidableEq S] (P : S → S → ℝ≥0∞) (a j : S) :
    mc_visitsE P a j = mc_hitE P a j * (1 + mc_visitsE P j j) := by
  have h0 : ∑' n, mc_powE P n j j = 1 + mc_visitsE P j j := by
    rw [tsum_eq_zero_add' ENNReal.summable]
    simp [mc_powE, mc_idE, mc_visitsE]
  rw [← h0, mc_hitE, ← mc_tsum_cauchy, mc_visitsE]
  exact tsum_congr fun n => mc_first_entrance P j n a

/-- A partial-sum form of the Cauchy product inequality. -/
theorem mc_sum_cauchy_le (a b : ℕ → ℝ≥0∞) (N : ℕ) :
    ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range (n + 1), a k * b (n - k) ≤
      (∑ k ∈ Finset.range N, a k) * ∑ r ∈ Finset.range N, b r := by
  rw [Finset.sum_comm' (t' := Finset.range N) (s' := fun k => Finset.Ico k N)
    (h := fun n k => by simp only [Finset.mem_range, Finset.mem_Ico]; omega)]
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [← Finset.mul_sum]
  gcongr
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (Nat.sub_le N k))

/-- From `u ≤ f + f u` with `u < ∞` and `f < 1`: `u ≤ 1/(1 − f)`. -/
theorem mc_le_of_le_add_mul {u f : ℝ≥0∞} (hu : u ≠ ∞) (hf : f < 1) (h : u ≤ f + f * u) :
    u ≤ ENNReal.ofReal (1 / (1 - f.toReal)) := by
  have hf' : f ≠ ∞ := (hf.trans ENNReal.one_lt_top).ne
  have hfr : f.toReal < 1 := by
    have := ENNReal.toReal_strict_mono ENNReal.one_ne_top hf
    simpa using this
  have hfr0 : 0 ≤ f.toReal := ENNReal.toReal_nonneg
  have h' : u.toReal ≤ f.toReal + f.toReal * u.toReal := by
    have := ENNReal.toReal_mono (by finiteness) h
    rwa [ENNReal.toReal_add hf' (by finiteness), ENNReal.toReal_mul] at this
  rw [← ENNReal.ofReal_toReal hu]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- The finite partial sums of the visits are finite. -/
theorem mc_sum_powE_ne_top [DecidableEq S] {P : S → S → ℝ≥0∞} (hP : mc_IsStochasticE P)
    (N : ℕ) (a j : S) : ∑ n ∈ Finset.range N, mc_powE P (n + 1) a j ≠ ∞ :=
  ENNReal.sum_ne_top.2 fun n _ => ((mc_powE_le_one hP (n + 1) a j).trans_lt
    ENNReal.one_lt_top).ne

/-- Miao, p. 98: a state `i` is transient (`Pr(τᵢ < ∞ | X₀ = i) < 1`) iff the expected number of
returns `Σₙ p⁽ⁿ⁺¹⁾ᵢᵢ` is finite; it is recurrent iff this number is infinite. -/
theorem mc_isTransientE_iff [DecidableEq S] {P : S → S → ℝ≥0∞} (hP : mc_IsStochasticE P)
    (i : S) : mc_IsTransientE P i ↔ mc_visitsE P i i < ∞ := by
  constructor
  · intro hF
    set f := mc_hitE P i i
    have hpart : ∀ N, ∑ n ∈ Finset.range N, mc_powE P (n + 1) i i ≤
        ENNReal.ofReal (1 / (1 - f.toReal)) := by
      intro N
      refine mc_le_of_le_add_mul (mc_sum_powE_ne_top hP N i i) hF ?_
      set U := ∑ n ∈ Finset.range N, mc_powE P (n + 1) i i
      have h1 : U ≤ (∑ m ∈ Finset.range N, mc_fpE P i m i) *
          ∑ r ∈ Finset.range N, mc_powE P r i i := by
        refine le_of_eq_of_le (Finset.sum_congr rfl fun n _ => mc_first_entrance P i n i) ?_
        exact mc_sum_cauchy_le (fun m => mc_fpE P i m i) (fun r => mc_powE P r i i) N
      have h2 : ∑ m ∈ Finset.range N, mc_fpE P i m i ≤ f := ENNReal.sum_le_tsum _
      have h3 : ∑ r ∈ Finset.range N, mc_powE P r i i ≤ 1 + U := by
        calc ∑ r ∈ Finset.range N, mc_powE P r i i ≤ ∑ r ∈ Finset.range (N + 1), mc_powE P r i i :=
              Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (Nat.le_succ N))
          _ = 1 + U := by
              rw [Finset.sum_range_succ', add_comm]
              simp [mc_powE, mc_idE, U]
      calc U ≤ f * (1 + U) := h1.trans (mul_le_mul' h2 h3)
        _ = f + f * U := by rw [mul_add, mul_one]
    exact lt_of_le_of_lt (ENNReal.tsum_le_of_sum_range_le hpart) ENNReal.ofReal_lt_top
  · intro hU
    by_contra hF
    have hF1 : mc_hitE P i i = 1 := le_antisymm (mc_hitE_le_one hP i i) (not_lt.1 hF)
    have h := mc_visits_eq P i i
    rw [hF1, one_mul] at h
    have hne : mc_visitsE P i i ≠ ∞ := hU.ne
    have : (1 : ℝ≥0∞) + mc_visitsE P i i ≠ mc_visitsE P i i := by
      intro h'
      have := (ENNReal.add_left_inj hne).1 (h'.trans (zero_add _).symm)
      exact one_ne_zero this
    exact this h.symm

/-- Recurrence is equivalent to infinitely many expected returns. -/
theorem mc_isRecurrentE_iff [DecidableEq S] {P : S → S → ℝ≥0∞} (hP : mc_IsStochasticE P)
    (i : S) : mc_IsRecurrentE P i ↔ mc_visitsE P i i = ∞ := by
  have h1 : mc_IsRecurrentE P i ↔ ¬ mc_IsTransientE P i := by
    simp only [mc_IsRecurrentE, mc_IsTransientE, not_lt]
    exact ⟨fun h => h.ge, fun h => le_antisymm (mc_hitE_le_one hP i i) h⟩
  rw [h1, mc_isTransientE_iff hP, not_lt, top_le_iff]

/-- Shifted sums of a sequence are at most the full sum. -/
theorem mc_tsum_shift_le (g : ℕ → ℝ≥0∞) (c : ℕ) : ∑' n, g (n + c) ≤ ∑' n, g n :=
  ENNReal.tsum_comp_le_tsum_of_injective (fun _ _ h => by simpa using h) g

/-- **Theorem 3.1.1(a)** (Miao, p. 98), countable chains with Definition 3.1.6: if `i ↔ j` and
`i` is recurrent, so is `j`; hence all states of a class are recurrent or all are transient. -/
theorem theorem_3_1_1a_countable [DecidableEq S] {P : S → S → ℝ≥0∞} (hP : mc_IsStochasticE P)
    {i j : S} (hij : mc_CommunicateE P i j) (hi : mc_IsRecurrentE P i) : mc_IsRecurrentE P j := by
  rcases hij with rfl | ⟨⟨r, -, hr⟩, ⟨s, -, hs⟩⟩
  · exact hi
  rw [mc_isRecurrentE_iff hP] at hi ⊢
  have hc : mc_powE P s j i * mc_powE P r i j ≠ 0 := (ENNReal.mul_pos hs.ne' hr.ne').ne'
  have hle : ∀ n, mc_powE P s j i * mc_powE P r i j * mc_powE P (n + 1) i i ≤
      mc_powE P (n + (s + r) + 1) j j := by
    intro n
    have e : n + (s + r) + 1 = s + ((n + 1) + r) := by omega
    rw [e]
    calc mc_powE P s j i * mc_powE P r i j * mc_powE P (n + 1) i i
        = mc_powE P s j i * (mc_powE P (n + 1) i i * mc_powE P r i j) := by ring
      _ ≤ mc_powE P s j i * mc_powE P ((n + 1) + r) i j := by
          gcongr; exact mc_powE_add_ge P _ _ _ _ _
      _ ≤ _ := mc_powE_add_ge P _ _ _ _ _
  have h1 : mc_powE P s j i * mc_powE P r i j * mc_visitsE P i i = ∞ := by
    rw [hi, ENNReal.mul_top hc]
  refine top_le_iff.1 (h1 ▸ ?_)
  calc mc_powE P s j i * mc_powE P r i j * mc_visitsE P i i
      = ∑' n, mc_powE P s j i * mc_powE P r i j * mc_powE P (n + 1) i i := by
        rw [mc_visitsE, ENNReal.tsum_mul_left]
    _ ≤ ∑' n, mc_powE P (n + (s + r) + 1) j j := ENNReal.tsum_le_tsum hle
    _ ≤ mc_visitsE P j j := mc_tsum_shift_le (fun n => mc_powE P (n + 1) j j) (s + r)

end Miao.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Markov processes (Definition 3.0.1) and Markov chains on path space

Miao, Chapter 3 opening and §3.1, pp. 85–87 and 94.

* **Definition 3.0.1** (p. 85): `mc_IsMarkovProcess μ X` for a process `X : ℕ → Ω → S` on a
  probability space `(Ω, μ)` with countable state space: for all `t`, `k ≤ t`, histories
  `x₀, …, xₖ` and sets `A`,
  `Pr(Xₜ₊₁ ∈ A | Xₜ = x₀, …, Xₜ₋ₖ = xₖ) = Pr(Xₜ₊₁ ∈ A | Xₜ = x₀)`. Conditional probabilities are
  elementary ratios, and the definition is stated in cross-multiplied form
  `Pr(Xₜ₊₁ ∈ A, H) Pr(Xₜ = x₀) = Pr(Xₜ₊₁ ∈ A, Xₜ = x₀) Pr(H)`, which is the book's equation
  whenever the conditioning events have positive probability and imposes nothing otherwise.
  `mc_IsTimeHomogeneous μ X`: `Pr(Xₜ₊₁ ∈ A | Xₜ = x)` does not depend on `t`.
* **The chain with transition matrix `P` and initial distribution `π₀`** (p. 86): a process
  whose finite-dimensional distributions are the path products
  `Pr(X₀ = x₀, …, Xₙ = xₙ) = π₀(x₀) p_{x₀x₁} ⋯ p_{x_{n−1}xₙ}` (`mc_cylProb`, `mc_HasChainLaw`).
  `mc_markov_of_chainLaw`: such a process is a time-homogeneous Markov process with
  `Pr(X₀ = i) = π₀ᵢ` and `Pr(Xₜ₊₁ = j | Xₜ = i) = pᵢⱼ`; `mc_marginal_of_chainLaw`: its
  distribution at time `t` is `π₀Pᵗ` (p. 94), so the `i`-th row of `Pᵗ` is the distribution `t`
  periods ahead from `i` (p. 87).

**Scope.** The existence and uniqueness of the path measure (p. 86, "a general version of this
result is stated in Theorem 3.2.3") is Theorem 3.2.3 of §3.2 and is not proved here. All the
results of §3.1 are statements about `P`, its powers and the path products, which is why the
chapter's other modules work with `P` directly; the first-passage probabilities of
`ChainCountable` are sums of the path products of this module.
-/

namespace Miao.MarkovProcesses

open MeasureTheory
open scoped ENNReal

variable {Ω S : Type*} [MeasurableSpace Ω]

/-- The history event `{Xₜ = x₀, Xₜ₋₁ = x₁, …, Xₜ₋ₖ = xₖ}`. -/
def mc_histEvent (X : ℕ → Ω → S) (t k : ℕ) (x : Fin (k + 1) → S) : Set Ω :=
  {ω | ∀ i : Fin (k + 1), X (t - i) ω = x i}

/-- **Definition 3.0.1** (Miao, p. 85): `X` is a **Markov process** under `μ`: for all `t`,
`k ≤ t`, histories `x` and sets `A`,
`Pr(Xₜ₊₁ ∈ A | Xₜ = x₀, …, Xₜ₋ₖ = xₖ) = Pr(Xₜ₊₁ ∈ A | Xₜ = x₀)` (cross-multiplied). -/
def mc_IsMarkovProcess (μ : Measure Ω) (X : ℕ → Ω → S) : Prop :=
  ∀ t k, k ≤ t → ∀ (x : Fin (k + 1) → S) (A : Set S),
    μ ({ω | X (t + 1) ω ∈ A} ∩ mc_histEvent X t k x) * μ {ω | X t ω = x 0} =
      μ ({ω | X (t + 1) ω ∈ A} ∩ {ω | X t ω = x 0}) * μ (mc_histEvent X t k x)

/-- **Definition 3.0.1** (Miao, p. 86): the Markov process is **time-homogeneous** if
`Pr(Xₜ₊₁ ∈ A | Xₜ = x)` does not depend on `t`: it is `Q(x, A)` for one `Q`. -/
def mc_IsTimeHomogeneous (μ : Measure Ω) (X : ℕ → Ω → S) : Prop :=
  ∃ Q : S → Set S → ℝ≥0∞, ∀ t x A,
    μ ({ω | X (t + 1) ω ∈ A} ∩ {ω | X t ω = x}) = Q x A * μ {ω | X t ω = x}

/-- The path product `π₀(x₀) p_{x₀x₁} ⋯ p_{x_{n−1}xₙ}`: the probability of the cylinder event
`{X₀ = x₀, …, Xₙ = xₙ}` for the chain with transition matrix `P` and initial distribution `π₀`
(Miao, p. 86). -/
noncomputable def mc_cylProb (π₀ : S → ℝ≥0∞) (P : S → S → ℝ≥0∞) (n : ℕ) (x : Fin (n + 1) → S) :
    ℝ≥0∞ :=
  π₀ (x 0) * ∏ i : Fin n, P (x i.castSucc) (x i.succ)

/-- The process `X` has the finite-dimensional distributions of the chain `(π₀, P)`. -/
def mc_HasChainLaw (μ : Measure Ω) (X : ℕ → Ω → S) (π₀ : S → ℝ≥0∞) (P : S → S → ℝ≥0∞) :
    Prop :=
  ∀ n (x : Fin (n + 1) → S), μ {ω | ∀ i : Fin (n + 1), X i ω = x i} = mc_cylProb π₀ P n x

/-- The path `(X₀, …, Xₙ)` as a tuple. -/
def mc_pathVec (X : ℕ → Ω → S) (n : ℕ) (ω : Ω) : Fin (n + 1) → S := fun i => X i ω

/-- The probability of `{(X₀, …, Xₙ) ∈ C}` is the sum of the cylinder probabilities over `C`. -/
theorem mc_measure_path_mem [Countable S] {μ : Measure Ω} {X : ℕ → Ω → S}
    (hX : ∀ t s, MeasurableSet {ω | X t ω = s}) (n : ℕ) (C : Set (Fin (n + 1) → S)) :
    μ (mc_pathVec X n ⁻¹' C) =
      ∑' y, C.indicator (fun y => μ {ω | ∀ i : Fin (n + 1), X i ω = y i}) y := by
  have hpre : ∀ y : Fin (n + 1) → S,
      mc_pathVec X n ⁻¹' {y} = {ω | ∀ i : Fin (n + 1), X i ω = y i} := fun y => by
    ext ω; simp [mc_pathVec, funext_iff]
  have hmeas : ∀ y : Fin (n + 1) → S, MeasurableSet (mc_pathVec X n ⁻¹' {y}) := fun y => by
    rw [hpre, Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => hX i (y i)
  rw [← tsum_measure_preimage_singleton (Set.to_countable C) fun y _ => hmeas y,
    tsum_subtype C (fun y => μ (mc_pathVec X n ⁻¹' {y}))]
  simp only [hpre]

/-- The key step: `Pr(Xₜ₊₁ ∈ A, (X₀, …, Xₜ) ∈ C) = Σ_{y ∈ C} Pr((X₀, …, Xₜ) = y) P(yₜ, A)`. -/
theorem mc_measure_step [Countable S] {μ : Measure Ω} {X : ℕ → Ω → S} {π₀ : S → ℝ≥0∞}
    {P : S → S → ℝ≥0∞} (hX : ∀ t s, MeasurableSet {ω | X t ω = s})
    (hlaw : mc_HasChainLaw μ X π₀ P) (t : ℕ) (A : Set S) (C : Set (Fin (t + 1) → S)) :
    μ ({ω | X (t + 1) ω ∈ A} ∩ mc_pathVec X t ⁻¹' C) =
      ∑' y, C.indicator (fun y => mc_cylProb π₀ P t y *
        ∑' j, A.indicator (P (y (Fin.last t))) j) y := by
  set D : Set (Fin (t + 1 + 1) → S) := {z | z (Fin.last (t + 1)) ∈ A ∧ Fin.init z ∈ C}
  have hset : {ω | X (t + 1) ω ∈ A} ∩ mc_pathVec X t ⁻¹' C = mc_pathVec X (t + 1) ⁻¹' D := by
    ext ω
    have hinit : Fin.init (mc_pathVec X (t + 1) ω) = mc_pathVec X t ω := rfl
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, D, hinit]
    rfl
  rw [hset, mc_measure_path_mem hX, ← (Fin.snocEquiv fun _ => S).tsum_eq, ENNReal.tsum_prod',
    ENNReal.tsum_comm]
  have hsn : ∀ (j : S) (y : Fin (t + 1) → S),
      (Fin.snocEquiv fun _ => S) (j, y) = Fin.snoc y j := fun _ _ => rfl
  refine tsum_congr fun y => ?_
  simp only [hsn]
  by_cases hy : y ∈ C
  · simp only [Set.indicator_of_mem hy, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun j => ?_
    by_cases hj : j ∈ A
    · have hD : (Fin.snoc y j : Fin (t + 1 + 1) → S) ∈ D := by
        simp [D, hj, hy, Fin.init_snoc]
      rw [Set.indicator_of_mem hD, Set.indicator_of_mem hj, hlaw, mc_cylProb, mc_cylProb,
        Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, Fin.succ_castSucc]
      have h0 : (Fin.snoc y j : Fin (t + 1 + 1) → S) 0 = y 0 := by
        rw [show (0 : Fin (t + 1 + 1)) = Fin.castSucc 0 from rfl, Fin.snoc_castSucc]
      rw [h0, mul_assoc]
    · have hD : (Fin.snoc y j : Fin (t + 1 + 1) → S) ∉ D := by
        simp [D, hj]
      rw [Set.indicator_of_notMem hD, Set.indicator_of_notMem hj, mul_zero]
  · have hD : ∀ j, (Fin.snoc y j : Fin (t + 1 + 1) → S) ∉ D := fun j => by
      simp [D, hy, Fin.init_snoc]
    simp only [Set.indicator_of_notMem hy, Set.indicator_of_notMem (hD _), tsum_zero]

/-- If every `y ∈ C` ends at `s`, then
`Pr(Xₜ₊₁ ∈ A, (X₀, …, Xₜ) ∈ C) = P(s, A) Pr((X₀, …, Xₜ) ∈ C)`. -/
theorem mc_measure_step_const [Countable S] {μ : Measure Ω} {X : ℕ → Ω → S} {π₀ : S → ℝ≥0∞}
    {P : S → S → ℝ≥0∞} (hX : ∀ t s, MeasurableSet {ω | X t ω = s})
    (hlaw : mc_HasChainLaw μ X π₀ P) (t : ℕ) (A : Set S) {C : Set (Fin (t + 1) → S)} {s : S}
    (hC : ∀ y ∈ C, y (Fin.last t) = s) :
    μ ({ω | X (t + 1) ω ∈ A} ∩ mc_pathVec X t ⁻¹' C) =
      (∑' j, A.indicator (P s) j) * μ (mc_pathVec X t ⁻¹' C) := by
  rw [mc_measure_step hX hlaw, mc_measure_path_mem hX, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun y => ?_
  by_cases hy : y ∈ C
  · simp only [Set.indicator_of_mem hy, hC y hy]
    rw [hlaw t y, mul_comm]
  · simp [Set.indicator_of_notMem hy]

/-- Miao, p. 86: a process with the finite-dimensional distributions of the chain `(π₀, P)` is a
time-homogeneous Markov process (Definition 3.0.1) with `Pr(X₀ = i) = π₀ᵢ` and
`Pr(Xₜ₊₁ = j | Xₜ = i) = pᵢⱼ` (cross-multiplied). -/
theorem mc_markov_of_chainLaw [Countable S] {μ : Measure Ω} {X : ℕ → Ω → S} {π₀ : S → ℝ≥0∞}
    {P : S → S → ℝ≥0∞} (hX : ∀ t s, MeasurableSet {ω | X t ω = s})
    (hlaw : mc_HasChainLaw μ X π₀ P) :
    mc_IsMarkovProcess μ X ∧ mc_IsTimeHomogeneous μ X ∧ (∀ i, μ {ω | X 0 ω = i} = π₀ i) ∧
      ∀ t i j, μ ({ω | X (t + 1) ω = j} ∩ {ω | X t ω = i}) = P i j * μ {ω | X t ω = i} := by
  -- `{Xₜ = s}` as a path event
  have hlast : ∀ t (s : S), {ω | X t ω = s} =
      mc_pathVec X t ⁻¹' {y | y (Fin.last t) = s} := fun t s => by
    ext ω; simp [mc_pathVec]
  have hhom : ∀ t s (A : Set S), μ ({ω | X (t + 1) ω ∈ A} ∩ {ω | X t ω = s}) =
      (∑' j, A.indicator (P s) j) * μ {ω | X t ω = s} := fun t s A => by
    rw [hlast]
    exact mc_measure_step_const hX hlaw t A fun y hy => hy
  refine ⟨?_, ⟨fun s A => ∑' j, A.indicator (P s) j, hhom⟩, fun i => ?_, fun t i j => ?_⟩
  · intro t k _ x A
    have hH : mc_histEvent X t k x =
        mc_pathVec X t ⁻¹' {y | ∀ i : Fin (k + 1), y ⟨t - i, by omega⟩ = x i} := by
      ext ω; simp [mc_histEvent, mc_pathVec]
    have h1 : μ ({ω | X (t + 1) ω ∈ A} ∩ mc_histEvent X t k x) =
        (∑' j, A.indicator (P (x 0)) j) * μ (mc_histEvent X t k x) := by
      rw [hH]
      refine mc_measure_step_const hX hlaw t A fun y hy => ?_
      have := hy 0
      simpa [Fin.last] using this
    rw [h1, hhom]
    ring
  · have h := hlaw 0 (fun _ => i)
    simp only [mc_cylProb, Finset.univ_eq_empty, Finset.prod_empty, mul_one] at h
    rw [← h]
    congr 1
    ext ω
    simp
  · have h := hhom t i {j}
    simp only [Set.mem_singleton_iff] at h
    rw [h]
    congr 1
    rw [tsum_eq_single j fun k hk => by simp [hk]]
    simp

/-- Miao, pp. 87, 94: for the chain `(π₀, P)`, the distribution in period `t` is `π₀Pᵗ`:
`Pr(Xₜ = j) = Σᵢ π₀ᵢ p⁽ᵗ⁾ᵢⱼ`; in particular, starting from `i` (`π₀ = δᵢ`), it is the `i`-th
row of `Pᵗ`. -/
theorem mc_marginal_of_chainLaw [Countable S] [DecidableEq S] {μ : Measure Ω} {X : ℕ → Ω → S}
    {π₀ : S → ℝ≥0∞} {P : S → S → ℝ≥0∞} (hX : ∀ t s, MeasurableSet {ω | X t ω = s})
    (hlaw : mc_HasChainLaw μ X π₀ P) (t : ℕ) (j : S) :
    μ {ω | X t ω = j} = ∑' i, π₀ i * mc_powE P t i j := by
  obtain ⟨-, -, h0, hstep⟩ := mc_markov_of_chainLaw hX hlaw
  induction t generalizing j with
  | zero =>
    simp only [mc_powE, mc_idE, mul_ite, mul_one, mul_zero]
    rw [tsum_eq_single j fun i hi => by simp [hi], h0]
    simp
  | succ t ih =>
    -- partition `{Xₜ₊₁ = j}` according to `Xₜ`
    have hpart : μ {ω | X (t + 1) ω = j} =
        ∑' s, μ ({ω | X (t + 1) ω = j} ∩ {ω | X t ω = s}) := by
      have h := tsum_measure_preimage_singleton (μ := μ.restrict {ω | X (t + 1) ω = j})
        (Set.countable_univ (α := S)) (f := X t) fun s _ => hX t s
      rw [Set.preimage_univ, Measure.restrict_apply_univ] at h
      rw [← h, tsum_univ (f := fun s : S => (μ.restrict {ω | X (t + 1) ω = j}) (X t ⁻¹' {s}))]
      refine tsum_congr fun s => ?_
      rw [Measure.restrict_apply (show MeasurableSet (X t ⁻¹' {s}) from hX t s), Set.inter_comm]
      rfl
    rw [hpart]
    simp only [hstep, ih, mc_powE_succ', mc_mulE]
    simp only [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    exact tsum_congr fun s => tsum_congr fun i => by ring

end Miao.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Countable-state Markov chains: stationary distributions and Theorem 3.1.5

Miao, §3.1.3, pp. 97–99. Setting and notation as in `ChainCountable`.

* **Definition 3.1.5** for countable chains: `mc_IsInvariantE` (`μ = μP` for a
  `[0, ∞]`-valued row vector), `mc_IsStationaryE` (an invariant probability vector).
* The cycle measure of a state `i`, `mc_cycleE P i k = Σₙ Pr(Xₙ₊₁ = k, τᵢ ≥ n + 1 | X₀ = i)`,
  the expected number of visits to `k` during an excursion from `i`: it is invariant when `i` is
  recurrent (`mc_cycleE_invariant`), it is the smallest invariant measure with mass `1` at `i`
  (`mc_cycleE_le`), and its total mass is the mean return time `E[τᵢ | X₀ = i]`
  (`mc_cycleE_mass`).
* `mc_recurrent_of_stationary`: an irreducible chain with a stationary distribution is
  recurrent; `mc_stationary_eq_inv`: then every stationary distribution satisfies
  `μⱼ = 1/E[τⱼ | X₀ = j]` and every state is positive recurrent.
* **Theorem 3.1.5** (p. 99), for an irreducible chain:
  (a) `theorem_3_1_5a`: if the chain is transient, `Σₖ p⁽ᵏ⁾ᵢⱼ < ∞` and `p⁽ᵏ⁾ᵢⱼ → 0` for all
  `i, j`, and there is no stationary distribution;
  (b) `theorem_3_1_5b`: if it is null recurrent, there is no stationary distribution,
  `Σₖ p⁽ᵏ⁾ᵢⱼ = ∞` and `E[τⱼ | X₀ = j] = ∞` for all `i, j`;
  (c) `theorem_3_1_5c`: if it is positive recurrent, there is a unique stationary distribution
  and `μⱼ = 1/E[τⱼ | X₀ = j] > 0` for all `j`;
  `theorem_3_1_5_trichotomy`: exactly one of these holds, for all states at once.
* Finite chains (p. 99: "for a finite state space, cases (a)–(b) cannot happen"):
  `theorem_3_1_5_finite`: an irreducible finite chain (a real transition matrix) is positive
  recurrent and its stationary distribution is `μⱼ = 1/E[τⱼ | X₀ = j]`; the bridge is
  `mc_toE` with `mc_powE_toE` (`p⁽ⁿ⁾` computed in `[0, ∞]` and in `ℝ` agree).

**Not formalised.** The limits `p⁽ᵏ⁾ᵢⱼ → 0` in case (b) and `p⁽ᵏ⁾ᵢⱼ → 1/E[τⱼ | X₀ = j]` in case
(c) (Billingsley's Theorem 8.8; they need aperiodicity and the renewal theorem or a coupling
argument). Aperiodicity is not needed for anything proved here. For finite chains the limit in
(c) is Theorem 3.1.3 together with Theorem 3.1.4.
-/

namespace Miao.MarkovProcesses

open Filter Topology Matrix
open scoped ENNReal

variable {S : Type*} [DecidableEq S] {P : S → S → ℝ≥0∞}

/-! ### Invariant measures -/

/-- An **invariant measure** of `P`: a `[0, ∞]`-valued row vector with `μ = μP`. -/
def mc_IsInvariantE (P : S → S → ℝ≥0∞) (μ : S → ℝ≥0∞) : Prop := ∀ j, ∑' i, μ i * P i j = μ j

/-- **Definition 3.1.5** (Miao, p. 94) for countable chains: a **stationary distribution** is an
invariant probability vector. -/
def mc_IsStationaryE (P : S → S → ℝ≥0∞) (μ : S → ℝ≥0∞) : Prop :=
  mc_IsInvariantE P μ ∧ ∑' i, μ i = 1

/-- An invariant measure is invariant under every power: `μ = μPⁿ`. -/
theorem mc_IsInvariantE.pow {μ : S → ℝ≥0∞} (hμ : mc_IsInvariantE P μ) (n : ℕ) (j : S) :
    ∑' i, μ i * mc_powE P n i j = μ j := by
  induction n generalizing j with
  | zero =>
    simp only [mc_powE, mc_idE, mul_ite, mul_one, mul_zero]
    rw [tsum_eq_single j fun i hi => by simp [hi]]
    simp
  | succ n ih =>
    rw [← hμ j]
    simp only [mc_powE_succ', mc_mulE, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun l => ?_
    rw [← ih l, ← ENNReal.tsum_mul_right]
    exact tsum_congr fun i => by ring

/-- `μᵢ p⁽ⁿ⁾ᵢⱼ ≤ μⱼ`. -/
theorem mc_IsInvariantE.le {μ : S → ℝ≥0∞} (hμ : mc_IsInvariantE P μ) (n : ℕ) (i j : S) :
    μ i * mc_powE P n i j ≤ μ j := by
  rw [← hμ.pow n j]; exact ENNReal.le_tsum (f := fun i => μ i * mc_powE P n i j) i

/-- A stationary distribution of an irreducible chain charges every state. -/
theorem mc_stationaryE_pos {μ : S → ℝ≥0∞} (hirr : mc_IsIrreducibleE P)
    (hμ : mc_IsStationaryE P μ) (j : S) : 0 < μ j := by
  obtain ⟨i, hi⟩ : ∃ i, μ i ≠ 0 := by
    by_contra h
    push Not at h
    have := hμ.2
    simp [h] at this
  rcases hirr i j with rfl | ⟨⟨m, -, hm⟩, -⟩
  · exact pos_iff_ne_zero.2 hi
  · exact lt_of_lt_of_le (ENNReal.mul_pos hi hm.ne') (hμ.1.le m i j)

omit [DecidableEq S] in
/-- The entries of a stationary distribution are at most one. -/
theorem mc_stationaryE_le_one {μ : S → ℝ≥0∞} (hμ : mc_IsStationaryE P μ) (j : S) : μ j ≤ 1 := by
  rw [← hμ.2]; exact ENNReal.le_tsum j

/-- If `i → j` then `Pr(τⱼ < ∞ | X₀ = i) > 0`. -/
theorem mc_hitE_pos {i j : S} (h : mc_AccessibleE P i j) : 0 < mc_hitE P i j := by
  obtain ⟨m, hm, hm'⟩ := h
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [mc_first_entrance] at hm'
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm'.ne'
  have hk' : 0 < mc_fpE P j k i := pos_iff_ne_zero.2 (left_ne_zero_of_mul hk)
  exact hk'.trans_le (ENNReal.le_tsum (f := fun n => mc_fpE P j n i) k)

/-- `Σₙ p⁽ⁿ⁺¹⁾ₐⱼ ≤ 1 + Σₙ p⁽ⁿ⁺¹⁾ⱼⱼ`. -/
theorem mc_visitsE_le (hP : mc_IsStochasticE P) (a j : S) :
    mc_visitsE P a j ≤ 1 + mc_visitsE P j j := by
  rw [mc_visits_eq]
  calc mc_hitE P a j * (1 + mc_visitsE P j j) ≤ 1 * (1 + mc_visitsE P j j) := by
        gcongr; exact mc_hitE_le_one hP a j
    _ = _ := one_mul _

/-- Miao, p. 98: an irreducible chain with a stationary distribution is recurrent (if `j` were
transient, `Σₙ μⱼ = Σᵢ μᵢ Σₙ p⁽ⁿ⁺¹⁾ᵢⱼ ≤ 1 + Σₙ p⁽ⁿ⁺¹⁾ⱼⱼ < ∞`). -/
theorem mc_recurrent_of_stationary (hP : mc_IsStochasticE P) (hirr : mc_IsIrreducibleE P)
    {μ : S → ℝ≥0∞} (hμ : mc_IsStationaryE P μ) (j : S) : mc_IsRecurrentE P j := by
  by_contra hrec
  have htr : mc_IsTransientE P j := by
    simp only [mc_IsTransientE, mc_IsRecurrentE] at hrec ⊢
    exact lt_of_le_of_ne (mc_hitE_le_one hP j j) hrec
  have hU := (mc_isTransientE_iff hP j).1 htr
  have hsum : ∑' _ : ℕ, μ j = ∑' i, μ i * mc_visitsE P i j := by
    simp only [mc_visitsE, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    exact tsum_congr fun n => (hμ.1.pow (n + 1) j).symm
  have hle : ∑' i, μ i * mc_visitsE P i j ≤ 1 + mc_visitsE P j j := by
    calc ∑' i, μ i * mc_visitsE P i j ≤ ∑' i, μ i * (1 + mc_visitsE P j j) :=
          ENNReal.tsum_le_tsum fun i => by gcongr; exact mc_visitsE_le hP i j
      _ = 1 + mc_visitsE P j j := by rw [ENNReal.tsum_mul_right, hμ.2, one_mul]
  have htop : ∑' _ : ℕ, μ j = ∞ :=
    ENNReal.tsum_const_eq_top_of_ne_zero (mc_stationaryE_pos hirr hμ j).ne'
  rw [hsum, ← top_le_iff] at htop
  exact absurd (htop.trans hle) (not_le.2 (ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, hU⟩))

/-! ### The cycle measure -/

/-- `Pr(Xₙ₊₁ = k, X₁, …, Xₙ ≠ i | X₀ = i) = ((PDᵢ)ⁿP)ᵢₖ`. -/
noncomputable def mc_cycleStepE (P : S → S → ℝ≥0∞) (i : S) (n : ℕ) (k : S) : ℝ≥0∞ :=
  mc_mulE (mc_powE (mc_tabooE P i) n) P i k

/-- The **cycle measure** of `i`: the expected number of visits to `k` at times
`1, …, τᵢ`. -/
noncomputable def mc_cycleE (P : S → S → ℝ≥0∞) (i : S) (k : S) : ℝ≥0∞ :=
  ∑' n, mc_cycleStepE P i n k

/-- The forward recursion `Gₙ₊₁(k) = Σ_{l ≠ i} Gₙ(l) pₗₖ`. -/
theorem mc_cycleStepE_succ (P : S → S → ℝ≥0∞) (i : S) (n : ℕ) (k : S) :
    mc_cycleStepE P i (n + 1) k =
      ∑' l, if l = i then 0 else mc_cycleStepE P i n l * P l k := by
  simp only [mc_cycleStepE]
  rw [mc_powE_succ', mc_mulE_assoc]
  simp only [mc_mulE]
  have h1 : ∀ l, (if l = i then 0 else (∑' m, mc_powE (mc_tabooE P i) n i m * P m l) * P l k) =
      ∑' m, mc_powE (mc_tabooE P i) n i m * (mc_tabooE P i m l * P l k) := fun l => by
    by_cases hl : l = i
    · simp [hl, mc_tabooE]
    · simp only [hl, ite_false, mc_tabooE, ← ENNReal.tsum_mul_right, mul_assoc]
  simp only [h1]
  rw [ENNReal.tsum_comm]
  simp only [ENNReal.tsum_mul_left]

/-- `G₀(k) = pᵢₖ`. -/
theorem mc_cycleStepE_zero (P : S → S → ℝ≥0∞) (i k : S) : mc_cycleStepE P i 0 k = P i k := by
  simp [mc_cycleStepE, mc_powE, mc_idE_mulE]

/-- The cycle measure at `i` is the return probability. -/
theorem mc_cycleE_self (P : S → S → ℝ≥0∞) (i : S) : mc_cycleE P i i = mc_hitE P i i := rfl

/-- For a recurrent state `i`, the cycle measure is invariant. -/
theorem mc_cycleE_invariant {i : S} (hi : mc_IsRecurrentE P i) :
    mc_IsInvariantE P (mc_cycleE P i) := by
  intro k
  have h1 : mc_cycleE P i k = P i k + ∑' n, mc_cycleStepE P i (n + 1) k := by
    rw [mc_cycleE, tsum_eq_zero_add' ENNReal.summable, mc_cycleStepE_zero]
  rw [h1]
  simp only [mc_cycleE, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  simp only [mc_cycleStepE_succ]
  have h2 : ∀ n, ∑' l, mc_cycleStepE P i n l * P l k =
      mc_cycleStepE P i n i * P i k + ∑' l, if l = i then 0 else mc_cycleStepE P i n l * P l k :=
    fun n => mc_tsum_split (fun l => mc_cycleStepE P i n l * P l k) i
  simp only [h2]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
  congr 1
  rw [← mc_cycleE, mc_cycleE_self, hi, one_mul]

/-- The cycle measure is the smallest invariant measure with mass `1` at `i`. -/
theorem mc_cycleE_le {i : S} {μ : S → ℝ≥0∞} (hμ : mc_IsInvariantE P μ) (hμi : μ i = 1)
    (k : S) : mc_cycleE P i k ≤ μ k := by
  have key : ∀ N k, ∑ n ∈ Finset.range N, mc_cycleStepE P i n k ≤ μ k := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      intro k
      rw [Finset.sum_range_succ', mc_cycleStepE_zero]
      simp only [mc_cycleStepE_succ]
      rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable, ← hμ k,
        mc_tsum_split (fun l => μ l * P l k) i, hμi, one_mul, add_comm]
      gcongr with l
      by_cases hl : l = i
      · simp [hl]
      · simp only [hl, ite_false, ← Finset.sum_mul]
        exact mul_le_mul_left (ih l) _
  exact ENNReal.tsum_le_of_sum_range_le fun N => key N k

/-- `Σ'ₙ Σ'ₘ g(m + n) = Σ'ₖ (k + 1) g(k)`. -/
theorem mc_tsum_tsum_add (g : ℕ → ℝ≥0∞) :
    ∑' n, ∑' m, g (m + n) = ∑' k : ℕ, ((k : ℝ≥0∞) + 1) * g k := by
  rw [← ENNReal.tsum_prod (f := fun n m => g (m + n)),
    ← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun k => ?_
  rw [tsum_fintype]
  have : ∀ x : Finset.antidiagonal k, g ((x : ℕ × ℕ).2 + (x : ℕ × ℕ).1) = g k := fun x => by
    have := Finset.mem_antidiagonal.1 x.2
    rw [add_comm, this]
  simp only [Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply]
  rw [Finset.sum_congr rfl fun x _ => this x, Finset.sum_const, Finset.card_univ,
    Fintype.card_coe, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
  push_cast; ring

/-- The total mass of the cycle measure of a recurrent state is the mean return time:
`Σₖ νₖ = E[τᵢ | X₀ = i]` (Kac). -/
theorem mc_cycleE_mass (hP : mc_IsStochasticE P) {i : S} (hi : mc_IsRecurrentE P i) :
    ∑' k, mc_cycleE P i k = mc_meanRetE P i := by
  have hP' : ∀ b, ∑' k, P b k = 1 := hP
  set s : ℕ → ℝ≥0∞ := fun n => ∑' l, mc_powE (mc_tabooE P i) n i l
  have hrow : ∀ n, ∑' k, mc_cycleStepE P i n k = s n := fun n => by
    simp only [mc_cycleStepE, mc_mulE, s]
    rw [ENNReal.tsum_comm]
    simp only [ENNReal.tsum_mul_left, hP', mul_one]
  have hstep : ∀ n, s (n + 1) + mc_fpE P i n i = s n := fun n => by
    simp only [s, mc_powE_succ', mc_mulE, mc_fpE]
    rw [ENNReal.tsum_comm, ← ENNReal.tsum_add]
    simp only [ENNReal.tsum_mul_left]
    refine tsum_congr fun l => ?_
    have : ∑' k, mc_tabooE P i l k + P l i = 1 := by
      rw [add_comm, ← hP l, mc_tsum_split (P l) i]
      rfl
    rw [← mul_add, this, mul_one]
  have hs : ∀ n, s n + ∑ m ∈ Finset.range n, mc_fpE P i m i = 1 := by
    intro n
    induction n with
    | zero =>
      simp only [s, mc_powE, mc_idE, Finset.range_zero, Finset.sum_empty, add_zero]
      rw [tsum_eq_single i fun j hj => by simp [Ne.symm hj]]
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ, add_comm _ (mc_fpE P i n i), ← add_assoc, hstep, ih]
  have htail : ∀ n, s n = ∑' m, mc_fpE P i (m + n) i := by
    intro n
    have h1 := (ENNReal.summable (f := fun m => mc_fpE P i (m + n) i)).sum_add_tsum_nat_add'
      (f := fun m => mc_fpE P i m i)
    have hfin : ∑ m ∈ Finset.range n, mc_fpE P i m i ≠ ∞ := by
      refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
      rw [← hs n]; exact le_add_self
    have h2 : ∑ m ∈ Finset.range n, mc_fpE P i m i + s n =
        ∑ m ∈ Finset.range n, mc_fpE P i m i + ∑' m, mc_fpE P i (m + n) i := by
      rw [h1, add_comm, hs n]
      exact hi.symm
    exact (ENNReal.add_right_inj hfin).1 h2
  calc ∑' k, mc_cycleE P i k = ∑' n, s n := by
        simp only [mc_cycleE]
        rw [ENNReal.tsum_comm]
        exact tsum_congr hrow
    _ = ∑' n, ∑' m, mc_fpE P i (m + n) i := tsum_congr htail
    _ = mc_meanRetE P i := mc_tsum_tsum_add (fun m => mc_fpE P i m i)

/-- `E[τᵢ | X₀ = i] ≥ Pr(τᵢ < ∞ | X₀ = i)`. -/
theorem mc_hitE_le_meanRetE (i : S) : mc_hitE P i i ≤ mc_meanRetE P i :=
  ENNReal.tsum_le_tsum fun _ => le_mul_of_one_le_left bot_le le_add_self

/-! ### Stationary distributions and mean return times -/

/-- Miao, Theorem 3.1.5(c), existence: a positive recurrent state `i` gives the stationary
distribution `ν/E[τᵢ | X₀ = i]`, `ν` the cycle measure, with mass `1/E[τᵢ | X₀ = i]` at `i`. -/
theorem mc_stationary_of_posRec (hP : mc_IsStochasticE P) {i : S}
    (hi : mc_IsPositiveRecurrentE P i) :
    mc_IsStationaryE P (fun k => mc_cycleE P i k * (mc_meanRetE P i)⁻¹) := by
  have hm0 : mc_meanRetE P i ≠ 0 := by
    have := mc_hitE_le_meanRetE (P := P) i
    rw [hi.1] at this
    exact (lt_of_lt_of_le one_pos this).ne'
  refine ⟨fun k => ?_, ?_⟩
  · calc ∑' l, mc_cycleE P i l * (mc_meanRetE P i)⁻¹ * P l k
        = (∑' l, mc_cycleE P i l * P l k) * (mc_meanRetE P i)⁻¹ := by
          rw [← ENNReal.tsum_mul_right]; exact tsum_congr fun l => by ring
      _ = mc_cycleE P i k * (mc_meanRetE P i)⁻¹ := by rw [mc_cycleE_invariant hi.1 k]
  · rw [ENNReal.tsum_mul_right, mc_cycleE_mass hP hi.1]
    exact ENNReal.mul_inv_cancel hm0 hi.2.ne

/-- Miao, Theorem 3.1.5(c), the formula `μⱼ = 1/E[τⱼ | X₀ = j]`: for an irreducible chain, every
stationary distribution satisfies `μⱼ = 1/E[τⱼ | X₀ = j]` and every state is positive recurrent.
-/
theorem mc_stationary_eq_inv (hP : mc_IsStochasticE P) (hirr : mc_IsIrreducibleE P)
    {μ : S → ℝ≥0∞} (hμ : mc_IsStationaryE P μ) (j : S) :
    μ j = (mc_meanRetE P j)⁻¹ ∧ mc_IsPositiveRecurrentE P j := by
  have hrec := mc_recurrent_of_stationary hP hirr hμ j
  have hμj := mc_stationaryE_pos hirr hμ j
  have hμj' : μ j ≠ ∞ := ((mc_stationaryE_le_one hμ j).trans_lt ENNReal.one_lt_top).ne
  set c := (μ j)⁻¹
  have hc : c ≠ ∞ := ENNReal.inv_ne_top.2 hμj.ne'
  set μ' : S → ℝ≥0∞ := fun k => μ k * c
  have hμ'inv : mc_IsInvariantE P μ' := fun k => by
    simp only [μ', mul_comm (μ _) c, mul_assoc, ENNReal.tsum_mul_left, hμ.1 k]
  have hμ'j : μ' j = 1 := ENNReal.mul_inv_cancel hμj.ne' hμj'
  have hμ'fin : ∀ k, μ' k ≠ ∞ := fun k =>
    ENNReal.mul_ne_top ((mc_stationaryE_le_one hμ k).trans_lt ENNReal.one_lt_top).ne hc
  set ν := mc_cycleE P j
  have hνinv : ∀ k, ∑' l, ν l * P l k = ν k := mc_cycleE_invariant hrec
  have hνle : ∀ k, ν k ≤ μ' k := mc_cycleE_le hμ'inv hμ'j
  have hνfin : ∀ k, ν k ≠ ∞ := fun k => ne_top_of_le_ne_top (hμ'fin k) (hνle k)
  set w : S → ℝ≥0∞ := fun k => μ' k - ν k
  have hsplit : ∀ k, μ' k = ν k + w k := fun k => (add_tsub_cancel_of_le (hνle k)).symm
  have hwinv : mc_IsInvariantE P w := fun k => by
    have h1 : ν k + ∑' l, w l * P l k = ν k + w k := by
      rw [← hsplit, ← hμ'inv k, ← hνinv k, ← ENNReal.tsum_add]
      exact tsum_congr fun l => by rw [hsplit l, add_mul]
    exact (ENNReal.add_right_inj (hνfin k)).1 h1
  have hwj : w j = 0 := by
    simp only [w, hμ'j]
    rw [show ν j = 1 from hrec, tsub_self]
  have hw0 : ∀ l, w l = 0 := by
    intro l
    by_cases hl : l = j
    · rw [hl, hwj]
    · obtain ⟨m, -, hm⟩ := ((mc_isIrreducibleE_iff hP).1 hirr) l j
      have := hwinv.le m l j
      rw [hwj, nonpos_iff_eq_zero, mul_eq_zero] at this
      exact this.resolve_right hm.ne'
  have hμν : ∀ k, μ' k = ν k := fun k => by rw [hsplit k, hw0 k, add_zero]
  have hmass : mc_meanRetE P j = c := by
    rw [← mc_cycleE_mass hP hrec]
    calc ∑' k, ν k = ∑' k, μ' k := tsum_congr fun k => (hμν k).symm
      _ = c := by simp only [μ']; rw [ENNReal.tsum_mul_right, hμ.2, one_mul]
  refine ⟨by rw [hmass, inv_inv], hrec, ?_⟩
  rw [hmass]
  exact lt_top_iff_ne_top.2 hc

/-! ### Theorem 3.1.5 -/

/-- The chain is transient, null recurrent or positive recurrent (all states). -/
theorem mc_transient_or_recurrent (hP : mc_IsStochasticE P) (i : S) :
    mc_IsTransientE P i ∨ mc_IsRecurrentE P i := by
  rcases lt_or_eq_of_le (mc_hitE_le_one hP i i) with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- **Theorem 3.1.5(a)** (Miao, p. 99): for an irreducible chain with a transient state, every
state is transient, `Σₖ p⁽ᵏ⁾ᵢⱼ < ∞` and `p⁽ᵏ⁾ᵢⱼ → 0` for all `i, j`, and there is no stationary
distribution. -/
theorem theorem_3_1_5a (hP : mc_IsStochasticE P) (hirr : mc_IsIrreducibleE P) {i : S}
    (hi : mc_IsTransientE P i) :
    (∀ j, mc_IsTransientE P j) ∧ (∀ a j, ∑' k, mc_powE P k a j < ∞) ∧
      (∀ a j, Tendsto (fun k => mc_powE P k a j) atTop (𝓝 0)) ∧
      ¬ ∃ μ, mc_IsStationaryE P μ := by
  have htr : ∀ j, mc_IsTransientE P j := by
    intro j
    rcases mc_transient_or_recurrent hP j with h | h
    · exact h
    · have := theorem_3_1_1a_countable hP (hirr j i) h
      exact absurd this (ne_of_lt hi)
  have hsum : ∀ a j, ∑' k, mc_powE P k a j < ∞ := by
    intro a j
    rw [tsum_eq_zero_add' ENNReal.summable]
    refine ENNReal.add_lt_top.2 ⟨(mc_powE_le_one hP 0 a j).trans_lt ENNReal.one_lt_top, ?_⟩
    exact (mc_visitsE_le hP a j).trans_lt
      (ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, (mc_isTransientE_iff hP j).1 (htr j)⟩)
  refine ⟨htr, hsum, fun a j => ENNReal.tendsto_atTop_zero_of_tsum_ne_top (hsum a j).ne, ?_⟩
  rintro ⟨μ, hμ⟩
  exact absurd (mc_recurrent_of_stationary hP hirr hμ i) (ne_of_lt hi)

/-- **Theorem 3.1.5(b)** (Miao, p. 99): for an irreducible chain with a null recurrent state,
every state is null recurrent, there is no stationary distribution, and
`Σₖ p⁽ᵏ⁾ᵢⱼ = ∞`, `E[τⱼ | X₀ = j] = ∞` for all `i, j`. The limit `p⁽ᵏ⁾ᵢⱼ → 0` is not proved. -/
theorem theorem_3_1_5b (hP : mc_IsStochasticE P) (hirr : mc_IsIrreducibleE P) {i : S}
    (hi : mc_IsNullRecurrentE P i) :
    (∀ j, mc_IsNullRecurrentE P j) ∧ (¬ ∃ μ, mc_IsStationaryE P μ) ∧
      ∀ a j, ∑' k, mc_powE P k a j = ∞ := by
  have hnost : ¬ ∃ μ, mc_IsStationaryE P μ := by
    rintro ⟨μ, hμ⟩
    exact absurd hi.2 (mc_stationary_eq_inv hP hirr hμ i).2.2.ne
  have hrec : ∀ j, mc_IsRecurrentE P j := fun j =>
    theorem_3_1_1a_countable hP (hirr i j) hi.1
  refine ⟨fun j => ⟨hrec j, ?_⟩, hnost, fun a j => ?_⟩
  · by_contra h
    exact hnost ⟨_, mc_stationary_of_posRec hP ⟨hrec j, lt_top_iff_ne_top.2 h⟩⟩
  · have hF : mc_hitE P a j ≠ 0 :=
      (mc_hitE_pos (((mc_isIrreducibleE_iff hP).1 hirr) a j)).ne'
    have hU : mc_visitsE P a j = ∞ := by
      rw [mc_visits_eq, (mc_isRecurrentE_iff hP j).1 (hrec j), add_top, ENNReal.mul_top hF]
    rw [tsum_eq_zero_add' ENNReal.summable]
    change _ + mc_visitsE P a j = ∞
    rw [hU, add_top]

/-- **Theorem 3.1.5(c)** (Miao, p. 99): for an irreducible chain with a positive recurrent
state, every state is positive recurrent and there is a unique stationary distribution `μ`, with
`μⱼ = 1/E[τⱼ | X₀ = j] > 0` for all `j`. The limit `p⁽ᵏ⁾ᵢⱼ → μⱼ` is not proved. -/
theorem theorem_3_1_5c (hP : mc_IsStochasticE P) (hirr : mc_IsIrreducibleE P) {i : S}
    (hi : mc_IsPositiveRecurrentE P i) :
    ∃ μ, mc_IsStationaryE P μ ∧ (∀ j, μ j = (mc_meanRetE P j)⁻¹ ∧ 0 < μ j) ∧
      (∀ j, mc_IsPositiveRecurrentE P j) ∧ ∀ ν, mc_IsStationaryE P ν → ν = μ := by
  have hμ := mc_stationary_of_posRec hP hi
  refine ⟨_, hμ, fun j => ⟨(mc_stationary_eq_inv hP hirr hμ j).1, mc_stationaryE_pos hirr hμ j⟩,
    fun j => (mc_stationary_eq_inv hP hirr hμ j).2, fun ν hν => funext fun j => ?_⟩
  rw [(mc_stationary_eq_inv hP hirr hν j).1, (mc_stationary_eq_inv hP hirr hμ j).1]

/-- Miao, Theorem 3.1.5 (p. 99): an irreducible chain is transient, null recurrent or positive
recurrent, each property holding for all states at once. -/
theorem theorem_3_1_5_trichotomy (hP : mc_IsStochasticE P) (hirr : mc_IsIrreducibleE P)
    [Nonempty S] :
    (∀ j, mc_IsTransientE P j) ∨ (∀ j, mc_IsNullRecurrentE P j) ∨
      ∀ j, mc_IsPositiveRecurrentE P j := by
  obtain ⟨i⟩ := ‹Nonempty S›
  rcases mc_transient_or_recurrent hP i with h | h
  · exact Or.inl (theorem_3_1_5a hP hirr h).1
  · by_cases hm : mc_meanRetE P i = ∞
    · exact Or.inr (Or.inl (theorem_3_1_5b hP hirr ⟨h, hm⟩).1)
    · obtain ⟨-, -, -, hpos, -⟩ := theorem_3_1_5c hP hirr ⟨h, lt_top_iff_ne_top.2 hm⟩
      exact Or.inr (Or.inr hpos)

/-! ### Finite chains -/

/-- A real transition matrix seen as a `[0, ∞]`-valued one. -/
noncomputable def mc_toE {T : Type*} (P : Matrix T T ℝ) : T → T → ℝ≥0∞ :=
  fun i j => ENNReal.ofReal (P i j)

/-- The `n`-step transitions computed in `[0, ∞]` are those of the real matrix. -/
theorem mc_powE_toE {T : Type*} [Fintype T] [DecidableEq T] {P : Matrix T T ℝ}
    (hP : P ∈ rowStochastic ℝ T) (n : ℕ) (i j : T) :
    mc_powE (mc_toE P) n i j = ENNReal.ofReal ((P ^ n) i j) := by
  induction n generalizing i with
  | zero => by_cases h : i = j <;> simp [mc_powE, mc_idE, h]
  | succ n ih =>
    simp only [mc_powE, mc_mulE, ih, mc_toE, tsum_fintype]
    rw [pow_succ', mul_apply, ENNReal.ofReal_sum_of_nonneg fun l _ =>
      mul_nonneg (nonneg_of_mem_rowStochastic hP) (mc_pow_nonneg hP n l j)]
    exact Finset.sum_congr rfl fun l _ =>
      (ENNReal.ofReal_mul (nonneg_of_mem_rowStochastic hP)).symm

/-- A real transition matrix is a transition matrix in `[0, ∞]`. -/
theorem mc_toE_stochastic {T : Type*} [Fintype T] [DecidableEq T] {P : Matrix T T ℝ}
    (hP : P ∈ rowStochastic ℝ T) : mc_IsStochasticE (mc_toE P) := fun i => by
  simp only [mc_toE, tsum_fintype]
  rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => nonneg_of_mem_rowStochastic hP,
    sum_row_of_mem_rowStochastic hP, ENNReal.ofReal_one]

/-- **Theorem 3.1.5** for finite chains (Miao, p. 99: "for a finite state space, cases (a)–(b)
cannot happen"): an irreducible finite chain is positive recurrent, and its (unique) stationary
distribution is `μⱼ = 1/E[τⱼ | X₀ = j]`. -/
theorem theorem_3_1_5_finite {T : Type*} [Fintype T] [DecidableEq T] [Nonempty T]
    {P : Matrix T T ℝ} (hP : P ∈ rowStochastic ℝ T) (hirr : mc_IsIrreducible P) :
    (∀ j, mc_IsPositiveRecurrentE (mc_toE P) j) ∧
      ∃ μ, mc_IsStationary P μ ∧ ∀ j, ENNReal.ofReal (μ j) = (mc_meanRetE (mc_toE P) j)⁻¹ := by
  obtain ⟨μ, hμ, -, -⟩ := mc_irreducible_stationary hP hirr
  have hPE := mc_toE_stochastic hP
  have hirrE : mc_IsIrreducibleE (mc_toE P) := by
    refine (mc_isIrreducibleE_iff hPE).2 fun i j => ?_
    obtain ⟨m, hm, hm'⟩ := (mc_isIrreducible_iff hP).1 hirr i j
    exact ⟨m, hm, by rw [mc_powE_toE hP]; exact ENNReal.ofReal_pos.2 hm'⟩
  have hμE : mc_IsStationaryE (mc_toE P) (fun i => ENNReal.ofReal (μ i)) := by
    refine ⟨fun j => ?_, ?_⟩
    · simp only [mc_toE, tsum_fintype]
      conv_rhs => rw [hμ.apply_eq 1 j, pow_one]
      rw [ENNReal.ofReal_sum_of_nonneg fun i _ =>
        mul_nonneg (hμ.1 i) (nonneg_of_mem_rowStochastic hP)]
      exact Finset.sum_congr rfl fun i _ => (ENNReal.ofReal_mul (hμ.1 i)).symm
    · rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg fun i _ => hμ.1 i, hμ.2.1,
        ENNReal.ofReal_one]
  exact ⟨fun j => (mc_stationary_eq_inv hPE hirrE hμE j).2,
    μ, hμ, fun j => (mc_stationary_eq_inv hPE hirrE hμE j).1⟩

end Miao.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Countable-state Markov chains: Examples 3.1.4–3.1.5 and counterexamples

Miao, §3.1, pp. 88–89, and §3.1.3, pp. 97–99.

* **Example 3.1.4** (the birth–death chain `Xₜ = max {0, bₜ + Xₜ₋₁}`, `ex314 p`, p. 88, with
  `Pr(bₜ = 1) = p`): `example_3_1_4_irreducible` (irreducible and aperiodic, p. 97);
  `example_3_1_4_transient` (for `p > 1/2` every state is transient and `p⁽ˡ⁾₀ⱼ → 0`, p. 97–99);
  `example_3_1_4_stationary` (for `p < 1/2`, `πᵢ = (1 − ρ)ρⁱ`, `ρ = p/q`, is the stationary
  distribution of the untruncated chain, which is positive recurrent, p. 98);
  `example_3_1_4_half` (for `p = 1/2` there is no stationary distribution, so the chain is not
  positive recurrent).
* **Example 3.1.5** (the unrestricted random walk on `ℤ`, `ex315`, p. 89):
  `example_3_1_5` (irreducible, every state has period `2`, no stationary distribution, p. 97).
* `theorem_3_1_4_countable_counterexample`: the uniform `k₀` of Theorem 3.1.4 fails for
  countable chains (Example 3.1.4 moves at most one step per period).
* `theorem_3_1_1b_countable_counterexample`: Theorem 3.1.1(b) fails for countable chains: the
  shift `i ↦ i + 1` on `ℕ` has no recurrent state.

**Corrections.**
* p. 98 says that Parts (a)–(b) of Theorem 3.1.1 remain true for countable chains. Part (b)
  (there is at least one recurrent class) is false (`theorem_3_1_1b_countable_counterexample`).
* p. 99 says that Theorem 3.1.4 also applies to countable chains. As stated (one `k₀` for all
  `i, j`) it is false (`theorem_3_1_4_countable_counterexample`); the pairwise version is
  `theorem_3_1_4_countable`.

**Not formalised.** Null recurrence for `p = 1/2` in Example 3.1.4: only the absence of a
stationary distribution (hence of positive recurrence) is proved, not recurrence. For Example
3.1.5, `p⁽ⁿ⁾ᵢⱼ → 0` is not proved (the absence of a stationary distribution is).
-/

namespace Miao.MarkovProcesses

open Filter Topology
open scoped ENNReal

/-! ### Two-point sums -/

/-- A sum with two nonzero terms. -/
theorem mc_tsum_pair {T : Type*} (f : T → ℝ≥0∞) {a b : T} (hab : a ≠ b)
    (hf : ∀ x, x ≠ a → x ≠ b → f x = 0) : ∑' x, f x = f a + f b := by
  classical
  rw [tsum_eq_sum (s := {a, b}) fun x hx => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact hf x hx.1 hx.2]
  exact Finset.sum_pair hab

/-! ### Example 3.1.4: the birth–death chain -/

/-- **Example 3.1.4** (Miao, p. 88): `Xₜ = max {0, bₜ + Xₜ₋₁}` with `Pr(bₜ = 1) = p`,
`Pr(bₜ = −1) = q = 1 − p`; from `i` the chain moves to `i + 1` with probability `p` and to
`max {0, i − 1}` with probability `q`. -/
noncomputable def ex314 (p : ℝ) (i j : ℕ) : ℝ≥0∞ :=
  if j = i + 1 then ENNReal.ofReal p else if j = i - 1 then ENNReal.ofReal (1 - p) else 0

/-- The rows of `ex314 p` sum to one. -/
theorem ex314_stochastic {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : mc_IsStochasticE (ex314 p) := by
  intro i
  rw [mc_tsum_pair _ (show i + 1 ≠ i - 1 by omega) fun x h1 h2 => by simp [ex314, h1, h2]]
  simp only [ex314, ite_true, show i - 1 ≠ i + 1 by omega, ite_false]
  rw [← ENNReal.ofReal_add hp0 (by linarith)]
  simp

/-- Column `0` of `ex314 p`: `Σᵢ μᵢ pᵢ₀ = q(μ₀ + μ₁)`. -/
theorem ex314_col_zero (p : ℝ) (μ : ℕ → ℝ≥0∞) :
    ∑' i, μ i * ex314 p i 0 = μ 0 * ENNReal.ofReal (1 - p) + μ 1 * ENNReal.ofReal (1 - p) := by
  rw [mc_tsum_pair _ (show (0 : ℕ) ≠ 1 by omega) fun x h1 h2 => by
    simp only [ex314]
    split_ifs <;> first | (exfalso; omega) | simp]
  simp [ex314]

/-- Column `j + 1` of `ex314 p`: `Σᵢ μᵢ pᵢ,ⱼ₊₁ = pμⱼ + qμⱼ₊₂`. -/
theorem ex314_col_succ (p : ℝ) (μ : ℕ → ℝ≥0∞) (j : ℕ) :
    ∑' i, μ i * ex314 p i (j + 1) =
      μ j * ENNReal.ofReal p + μ (j + 2) * ENNReal.ofReal (1 - p) := by
  rw [mc_tsum_pair _ (show j ≠ j + 2 by omega) fun x h1 h2 => by
    simp only [ex314]
    split_ifs <;> first | (exfalso; omega) | simp]
  simp only [ex314, ite_true, show j + 1 = j + 2 - 1 by omega,
    show j + 2 - 1 ≠ j + 2 + 1 by omega, ite_false]

/-- The birth–death chain moves at most one step per period: `p⁽ⁿ⁾ᵢⱼ ≠ 0 ⇒ j ≤ i + n`. -/
theorem ex314_pow_ne_zero (p : ℝ) (n i j : ℕ) (h : mc_powE (ex314 p) n i j ≠ 0) : j ≤ i + n := by
  induction n generalizing i with
  | zero =>
    by_contra hne
    simp [mc_powE, mc_idE, show i ≠ j by omega] at h
  | succ n ih =>
    simp only [mc_powE, mc_mulE] at h
    obtain ⟨k, hk⟩ : ∃ k, ex314 p i k * mc_powE (ex314 p) n k j ≠ 0 := by
      by_contra hne
      push Not at hne
      exact h (ENNReal.tsum_eq_zero.2 hne)
    have h1 := left_ne_zero_of_mul hk
    have h2 := ih k (right_ne_zero_of_mul hk)
    have hk' : k ≤ i + 1 := by
      by_contra hki
      simp [ex314, show k ≠ i + 1 by omega, show k ≠ i - 1 by omega] at h1
    omega

/-- **Example 3.1.4** (Miao, p. 97): for `0 < p < 1` the birth–death chain is irreducible and
aperiodic. -/
theorem example_3_1_4_irreducible {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    mc_IsIrreducibleE (ex314 p) ∧ ∀ i, mc_periodE (ex314 p) i = 1 := by
  have hP := ex314_stochastic hp0.le hp1.le
  have hup : ∀ i, mc_AccessibleE (ex314 p) i (i + 1) := fun i =>
    mc_accessibleE_of_pos (by simp [ex314, hp0])
  have hdown : ∀ i, mc_AccessibleE (ex314 p) (i + 1) i := fun i =>
    mc_accessibleE_of_pos (by simp [ex314, show i ≠ i + 1 + 1 by omega]; linarith)
  have hupk : ∀ k i, mc_AccessibleE (ex314 p) i (i + k + 1) := by
    intro k
    induction k with
    | zero => exact hup
    | succ k ih => exact fun i => (ih i).trans (hup _)
  have hdownk : ∀ k i, mc_AccessibleE (ex314 p) (i + k + 1) i := by
    intro k
    induction k with
    | zero => exact hdown
    | succ k ih => exact fun i => (hdown _).trans (ih i)
  have hacc : ∀ i j, mc_AccessibleE (ex314 p) i j := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · obtain ⟨k, rfl⟩ : ∃ k, j = i + k + 1 := ⟨j - i - 1, by omega⟩
      exact hupk k i
    · exact (hup i).trans (hdown i)
    · obtain ⟨k, rfl⟩ : ∃ k, i = j + k + 1 := ⟨i - j - 1, by omega⟩
      exact hdownk k j
  have hirr := (mc_isIrreducibleE_iff hP).2 hacc
  refine ⟨hirr, fun i => ?_⟩
  have h0 : mc_periodE (ex314 p) 0 = 1 := by
    have h1 : 1 ∈ mc_returnSetE (ex314 p) 0 :=
      ⟨le_rfl, by rw [mc_powE_one]; simp [ex314]; linarith⟩
    exact Nat.dvd_one.1 (mc_setGcd_dvd (mc_returnSetE_isAddClosed _ 0) h1 one_pos h1)
  rw [← theorem_3_1_2_countable (ex314 p) (hirr 0 i), h0]

/-- **Theorem 3.1.4** (Miao, p. 99: "Theorem 3.1.4 also applies"), **counterexample**: the
birth–death chain is irreducible and aperiodic, but there is no `k₀` with `p⁽ᵏ⁾ᵢⱼ > 0` for all
`i, j` and all `k ≥ k₀`. -/
theorem theorem_3_1_4_countable_counterexample {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    mc_IsIrreducibleE (ex314 p) ∧ (∀ i, mc_periodE (ex314 p) i = 1) ∧
      ¬ ∃ k₀, 0 < k₀ ∧ ∀ k ≥ k₀, ∀ i j, 0 < mc_powE (ex314 p) k i j := by
  refine ⟨(example_3_1_4_irreducible hp0 hp1).1, (example_3_1_4_irreducible hp0 hp1).2, ?_⟩
  rintro ⟨k₀, -, h⟩
  have := ex314_pow_ne_zero p k₀ 0 (k₀ + 1) (h k₀ le_rfl 0 (k₀ + 1)).ne'
  omega

/-- The sum `Σ_{b ≠ 0} p_{kb} x_b` for the birth–death chain. -/
theorem ex314_taboo_sum (p : ℝ) (k : ℕ) (x : ℕ → ℝ≥0∞) :
    ∑' b, (if b = 0 then 0 else ex314 p k b * x b) =
      ENNReal.ofReal p * x (k + 1) +
        (if k - 1 = 0 then 0 else ENNReal.ofReal (1 - p) * x (k - 1)) := by
  rw [mc_tsum_pair _ (show k + 1 ≠ k - 1 by omega) fun b h1 h2 => by simp [ex314, h1, h2]]
  simp only [ex314, ite_true, show k - 1 ≠ k + 1 by omega, ite_false,
    show k + 1 ≠ 0 by omega]

/-- **Example 3.1.4** (Miao, pp. 97–99): for `1/2 < p < 1` the birth–death chain is transient:
`Pr(τ₀ < ∞ | X₀ = 0) ≤ 2q < 1`; hence every state is transient and `p⁽ˡ⁾₀ⱼ → 0` for every `j`.
-/
theorem example_3_1_4_transient {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) :
    mc_hitE (ex314 p) 0 0 ≤ ENNReal.ofReal (2 * (1 - p)) ∧ (∀ j, mc_IsTransientE (ex314 p) j) ∧
      ∀ j, Tendsto (fun l => mc_powE (ex314 p) l 0 j) atTop (𝓝 0) := by
  have hP := ex314_stochastic (by linarith) hp1.le
  set q := 1 - p
  set r := q / p with hr
  have hp : 0 < p := by linarith
  have hq : 0 < q := by simp only [q]; linarith
  have hr0 : 0 ≤ r := div_nonneg hq.le hp.le
  have hrp : r * p = q := div_mul_cancel₀ q hp.ne'
  -- the minimal-solution bound `Σ_{n<N} f⁽ⁿ⁺¹⁾ₖ₀ ≤ rᵏ` for `k ≥ 1`
  have key : ∀ N k, 1 ≤ k → ∑ n ∈ Finset.range N, mc_fpE (ex314 p) 0 n k ≤
      ENNReal.ofReal (r ^ k) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      intro k hk
      rw [Finset.sum_range_succ', mc_fpE_zero]
      simp only [mc_fpE_succ]
      rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
      have h1 : ∑' b, ∑ n ∈ Finset.range N,
          (if b = 0 then 0 else ex314 p k b * mc_fpE (ex314 p) 0 n b) =
          ∑' b, (if b = 0 then 0 else ex314 p k b *
            ∑ n ∈ Finset.range N, mc_fpE (ex314 p) 0 n b) := tsum_congr fun b => by
        by_cases hb : b = 0 <;> simp [hb, Finset.mul_sum]
      rw [h1, ex314_taboo_sum]
      by_cases hk1 : k = 1
      · subst hk1
        simp only [Nat.sub_self, ite_true, add_zero]
        have hval : ex314 p 1 0 = ENNReal.ofReal q := by simp [ex314, q]
        rw [hval]
        calc ENNReal.ofReal p * ∑ n ∈ Finset.range N, mc_fpE (ex314 p) 0 n (1 + 1) +
              ENNReal.ofReal q ≤ ENNReal.ofReal p * ENNReal.ofReal (r ^ 2) + ENNReal.ofReal q := by
              gcongr; exact ih 2 (by norm_num)
          _ = ENNReal.ofReal (r ^ 1) := by
              rw [← ENNReal.ofReal_mul hp.le, ← ENNReal.ofReal_add (by positivity) hq.le]
              congr 1
              have : r * (p * r) = r * q := by rw [mul_comm p r, hrp]
              nlinarith [this]
      · have hk2 : k - 1 ≠ 0 := by omega
        simp only [hk2, ite_false]
        have hval : ex314 p k 0 = 0 := by simp [ex314]; omega
        rw [hval, add_zero]
        calc ENNReal.ofReal p * ∑ n ∈ Finset.range N, mc_fpE (ex314 p) 0 n (k + 1) +
              ENNReal.ofReal q * ∑ n ∈ Finset.range N, mc_fpE (ex314 p) 0 n (k - 1)
            ≤ ENNReal.ofReal p * ENNReal.ofReal (r ^ (k + 1)) +
                ENNReal.ofReal q * ENNReal.ofReal (r ^ (k - 1)) := by
              gcongr
              · exact ih _ (by omega)
              · exact ih _ (by omega)
          _ = ENNReal.ofReal (r ^ k) := by
              rw [← ENNReal.ofReal_mul hp.le, ← ENNReal.ofReal_mul hq.le,
                ← ENNReal.ofReal_add (by positivity) (by positivity)]
              congr 1
              obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
              simp only [Nat.add_sub_cancel, pow_succ]
              have : r * (p * r) = r * q := by rw [mul_comm p r, hrp]
              nlinarith [this, pow_nonneg hr0 m]
  have hF1 : mc_hitE (ex314 p) 1 0 ≤ ENNReal.ofReal r := by
    have := ENNReal.tsum_le_of_sum_range_le fun N => key N 1 le_rfl
    rw [pow_one] at this
    exact this
  have hF0 : mc_hitE (ex314 p) 0 0 =
      ENNReal.ofReal q + ENNReal.ofReal p * mc_hitE (ex314 p) 1 0 := by
    rw [mc_hitE, tsum_eq_zero_add' ENNReal.summable, mc_fpE_zero]
    simp only [mc_fpE_succ]
    rw [ENNReal.tsum_comm]
    have h1 : ∀ b, ∑' n, (if b = 0 then 0 else ex314 p 0 b * mc_fpE (ex314 p) 0 n b) =
        if b = 0 then 0 else ex314 p 0 b * mc_hitE (ex314 p) b 0 := fun b => by
      by_cases hb : b = 0 <;> simp [hb, mc_hitE, ENNReal.tsum_mul_left]
    simp only [h1, ex314_taboo_sum, Nat.zero_sub, ite_true, add_zero]
    simp [ex314, q]
  have hbound : mc_hitE (ex314 p) 0 0 ≤ ENNReal.ofReal (2 * q) := by
    rw [hF0]
    calc ENNReal.ofReal q + ENNReal.ofReal p * mc_hitE (ex314 p) 1 0 ≤
          ENNReal.ofReal q + ENNReal.ofReal p * ENNReal.ofReal r := by gcongr
      _ = ENNReal.ofReal (2 * q) := by
          rw [← ENNReal.ofReal_mul hp.le, ← ENNReal.ofReal_add hq.le (by positivity)]
          congr 1
          rw [mul_comm p r, hrp]; ring
  have htr0 : mc_IsTransientE (ex314 p) 0 := by
    refine lt_of_le_of_lt hbound ?_
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by simp only [q]; linarith)
  obtain ⟨htr, -, hlim, -⟩ :=
    theorem_3_1_5a hP (example_3_1_4_irreducible hp (by linarith)).1 htr0
  exact ⟨hbound, htr, fun j => hlim 0 j⟩

/-- **Example 3.1.4** (Miao, p. 98): for `0 < p < 1/2`, `πᵢ = (1 − ρ)ρⁱ` with `ρ = p/q` is the
stationary distribution of the (untruncated) birth–death chain; hence the chain is positive
recurrent, `π` is its unique stationary distribution, and `πⱼ = 1/E[τⱼ | X₀ = j]`. -/
theorem example_3_1_4_stationary {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1 / 2) :
    mc_IsStationaryE (ex314 p) (fun i => ENNReal.ofReal ((1 - p / (1 - p)) * (p / (1 - p)) ^ i)) ∧
      (∀ j, mc_IsPositiveRecurrentE (ex314 p) j) ∧
      ∀ j, ENNReal.ofReal ((1 - p / (1 - p)) * (p / (1 - p)) ^ j) =
        (mc_meanRetE (ex314 p) j)⁻¹ := by
  have hP := ex314_stochastic hp0.le (by linarith)
  have hirr := (example_3_1_4_irreducible hp0 (by linarith)).1
  set q := 1 - p with hq
  set ρ := p / q with hρ
  have hq0 : 0 < q := by linarith
  have hρ0 : 0 ≤ ρ := div_nonneg hp0.le hq0.le
  have hρ1 : ρ < 1 := (div_lt_one hq0).2 (by linarith)
  have hρq : ρ * q = p := div_mul_cancel₀ p hq0.ne'
  set π : ℕ → ℝ := fun i => (1 - ρ) * ρ ^ i
  have hπ0 : ∀ i, 0 ≤ π i := fun i => mul_nonneg (by linarith) (pow_nonneg hρ0 i)
  have hstat : mc_IsStationaryE (ex314 p) (fun i => ENNReal.ofReal (π i)) := by
    refine ⟨fun j => ?_, ?_⟩
    · rcases j with _ | j
      · rw [ex314_col_zero, ← ENNReal.ofReal_mul (hπ0 0), ← ENNReal.ofReal_mul (hπ0 1),
          ← ENNReal.ofReal_add (mul_nonneg (hπ0 0) hq0.le) (mul_nonneg (hπ0 1) hq0.le)]
        congr 1
        simp only [π, pow_zero, pow_one]
        have : (1 - ρ) * ρ * q = (1 - ρ) * p := by rw [mul_assoc, hρq]
        nlinarith [this]
      · rw [ex314_col_succ, ← ENNReal.ofReal_mul (hπ0 j), ← ENNReal.ofReal_mul (hπ0 (j + 2)),
          ← ENNReal.ofReal_add (mul_nonneg (hπ0 j) hp0.le) (mul_nonneg (hπ0 (j + 2)) hq0.le)]
        congr 1
        simp only [π, pow_succ]
        have : ρ * ρ * q = ρ * p := by rw [mul_assoc, hρq]
        have h2 : (1 - ρ) * ρ ^ j * ρ * ρ * q = (1 - ρ) * ρ ^ j * ρ * p := by
          rw [mul_assoc ((1 - ρ) * ρ ^ j * ρ), hρq]
        nlinarith [h2, pow_nonneg hρ0 j]
    · rw [← ENNReal.ofReal_tsum_of_nonneg hπ0
        ((summable_geometric_of_lt_one hρ0 hρ1).mul_left (1 - ρ))]
      simp only [π]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1,
        mul_inv_cancel₀ (by linarith), ENNReal.ofReal_one]
  exact ⟨hstat, fun j => (mc_stationary_eq_inv hP hirr hstat j).2,
    fun j => (mc_stationary_eq_inv hP hirr hstat j).1⟩

/-- **Example 3.1.4** (Miao, p. 99), `p = 1/2`: the birth–death chain has no stationary
distribution, so it is not positive recurrent (Theorem 3.1.5(c)). -/
theorem example_3_1_4_half :
    (¬ ∃ μ, mc_IsStationaryE (ex314 (1 / 2)) μ) ∧
      ∀ j, ¬ mc_IsPositiveRecurrentE (ex314 (1 / 2)) j := by
  have hP := ex314_stochastic (p := 1 / 2) (by norm_num) (by norm_num)
  have hirr := (example_3_1_4_irreducible (p := 1 / 2) (by norm_num) (by norm_num)).1
  have hnost : ¬ ∃ μ, mc_IsStationaryE (ex314 (1 / 2)) μ := by
    rintro ⟨μ, hμ⟩
    have hfin : ∀ i, μ i ≠ ∞ := fun i =>
      ((mc_stationaryE_le_one hμ i).trans_lt ENNReal.one_lt_top).ne
    have hh' : ENNReal.ofReal (1 / 2) = 2⁻¹ := by
      rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
    have hh : ENNReal.ofReal (1 - 1 / 2) = 2⁻¹ := by
      rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, hh']
    -- invariance forces `μ` to be constant
    have hconst : ∀ i, μ (i + 1) = μ i := by
      intro i
      induction i with
      | zero =>
        have h := hμ.1 0
        rw [ex314_col_zero, hh, ← add_mul] at h
        have h2 : (μ 0 + μ 1) * 2⁻¹ * 2 = μ 0 * 2 := by rw [h]
        rw [mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one, mul_two] at h2
        exact ((ENNReal.add_right_inj (hfin 0)).1 h2)
      | succ i ih =>
        have h := hμ.1 (i + 1)
        rw [ex314_col_succ, hh, hh', ← add_mul, ih] at h
        have h2 : (μ i + μ (i + 1 + 1)) * 2⁻¹ * 2 = μ i * 2 := by rw [h]
        rw [mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one, mul_two] at h2
        rw [ih]
        exact (ENNReal.add_right_inj (hfin i)).1 h2
    have hall : ∀ i, μ i = μ 0 := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih => rw [hconst, ih]
    have hsum := hμ.2
    simp only [hall] at hsum
    by_cases h0 : μ 0 = 0
    · simp [h0] at hsum
    · rw [ENNReal.tsum_const_eq_top_of_ne_zero h0] at hsum
      exact ENNReal.top_ne_one hsum
  refine ⟨hnost, fun j hj => hnost ?_⟩
  obtain ⟨μ, hμ, -⟩ := theorem_3_1_5c hP hirr hj
  exact ⟨μ, hμ⟩

/-! ### Example 3.1.5: the unrestricted random walk -/

/-- **Example 3.1.5** (Miao, p. 89): the unrestricted random walk on `ℤ`, moving `±1` with
probability `1/2` each. -/
noncomputable def ex315 (i j : ℤ) : ℝ≥0∞ := if j = i + 1 ∨ j = i - 1 then 2⁻¹ else 0

/-- The rows of `ex315` sum to one. -/
theorem ex315_stochastic : mc_IsStochasticE ex315 := by
  intro i
  rw [mc_tsum_pair _ (show i + 1 ≠ i - 1 by omega) fun x h1 h2 => by simp [ex315, h1, h2]]
  simp only [ex315, true_or, or_true, ite_true]
  exact ENNReal.inv_two_add_inv_two

/-- Column sums of `ex315`: `Σᵢ μᵢ pᵢⱼ = (μⱼ₋₁ + μⱼ₊₁)/2`. -/
theorem ex315_col (μ : ℤ → ℝ≥0∞) (j : ℤ) :
    ∑' i, μ i * ex315 i j = μ (j - 1) * 2⁻¹ + μ (j + 1) * 2⁻¹ := by
  rw [mc_tsum_pair _ (show j - 1 ≠ j + 1 by omega) fun x h1 h2 => by
    simp only [ex315]
    split_ifs <;> first | (exfalso; omega) | simp]
  simp only [ex315, show j = j - 1 + 1 ∨ j = j - 1 - 1 from Or.inl (by ring),
    show j = j + 1 + 1 ∨ j = j + 1 - 1 from Or.inr (by ring), ite_true]

/-- Parity: `p⁽ⁿ⁾ᵢⱼ ≠ 0 ⇒ j − i + n` is even. -/
theorem ex315_pow_parity (n : ℕ) (i j : ℤ) (h : mc_powE ex315 n i j ≠ 0) :
    Even (j - i + n) := by
  induction n generalizing i with
  | zero =>
    by_contra hne
    have hij : i ≠ j := fun h' => hne (by subst h'; simp)
    simp [mc_powE, mc_idE, hij] at h
  | succ n ih =>
    simp only [mc_powE, mc_mulE] at h
    obtain ⟨k, hk⟩ : ∃ k, ex315 i k * mc_powE ex315 n k j ≠ 0 := by
      by_contra hne
      push Not at hne
      exact h (ENNReal.tsum_eq_zero.2 hne)
    have h1 := left_ne_zero_of_mul hk
    have h2 := ih k (right_ne_zero_of_mul hk)
    have hk' : k = i + 1 ∨ k = i - 1 := by
      by_contra hki
      simp [ex315, hki] at h1
    push_cast
    rcases hk' with rfl | rfl
    · have e : j - i + ((n : ℤ) + 1) = (j - (i + 1) + n) + 2 := by ring
      rw [e]
      exact h2.add even_two
    · convert h2 using 1
      ring

/-- **Example 3.1.5** (Miao, p. 97): the unrestricted random walk is irreducible, every state has
period `2`, and there is no stationary distribution. -/
theorem example_3_1_5 :
    mc_IsIrreducibleE ex315 ∧ (∀ i, mc_periodE ex315 i = 2) ∧
      ¬ ∃ μ, mc_IsStationaryE ex315 μ := by
  have hP := ex315_stochastic
  have hup : ∀ i, mc_AccessibleE ex315 i (i + 1) := fun i =>
    mc_accessibleE_of_pos (by simp [ex315])
  have hdown : ∀ i, mc_AccessibleE ex315 i (i - 1) := fun i =>
    mc_accessibleE_of_pos (by simp [ex315])
  have hupk : ∀ (k : ℕ) i, mc_AccessibleE ex315 i (i + k + 1) := by
    intro k
    induction k with
    | zero => simpa using hup
    | succ k ih => exact fun i => (ih i).trans (by simpa [add_assoc] using hup (i + k + 1))
  have hdownk : ∀ (k : ℕ) i, mc_AccessibleE ex315 i (i - k - 1) := by
    intro k
    induction k with
    | zero => simpa using hdown
    | succ k ih => exact fun i => (ih i).trans (by
        have := hdown (i - k - 1); push_cast; convert this using 1; ring)
  have hacc : ∀ i j, mc_AccessibleE ex315 i j := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, j = i + k + 1 := ⟨(j - i - 1).toNat, by omega⟩
      rw [hk]; exact hupk k i
    · exact (hup i).trans (by simpa using hdown (i + 1))
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, j = i - k - 1 := ⟨(i - j - 1).toNat, by omega⟩
      rw [hk]; exact hdownk k i
  have hirr := (mc_isIrreducibleE_iff hP).2 hacc
  refine ⟨hirr, fun i => ?_, ?_⟩
  · have hS := mc_returnSetE_isAddClosed ex315 i
    have h2 : 2 ∈ mc_returnSetE ex315 i := by
      refine ⟨by norm_num, ?_⟩
      have h := mc_powE_add_pos ex315 (m := 1) (n := 1) (i := i) (j := i + 1) (k := i)
        (by rw [mc_powE_one]; simp [ex315]) (by rw [mc_powE_one]; simp [ex315])
      simpa using h
    have heven : ∀ n ∈ mc_returnSetE ex315 i, 2 ∣ n := by
      rintro n ⟨-, hn⟩
      have := ex315_pow_parity n i i hn.ne'
      simp only [sub_self, zero_add] at this
      exact (Int.natCast_dvd_natCast.1 (even_iff_two_dvd.1 this))
    exact Nat.dvd_antisymm (mc_setGcd_dvd hS h2 (by norm_num) h2)
      (dvd_mc_setGcd hS h2 (by norm_num) heven)
  · rintro ⟨μ, hμ⟩
    have hfin : ∀ i, μ i ≠ ∞ := fun i =>
      ((mc_stationaryE_le_one hμ i).trans_lt ENNReal.one_lt_top).ne
    set a : ℤ → ℝ := fun i => (μ i).toReal
    have ha0 : ∀ i, 0 ≤ a i := fun i => ENNReal.toReal_nonneg
    -- `a` is affine: its increments are constant
    have hrec : ∀ j, a (j + 1) - a j = a j - a (j - 1) := by
      intro j
      have h := hμ.1 j
      rw [ex315_col] at h
      have h' := congrArg ENNReal.toReal h
      rw [ENNReal.toReal_add (ENNReal.mul_ne_top (hfin _) (by norm_num))
        (ENNReal.mul_ne_top (hfin _) (by norm_num)), ENNReal.toReal_mul, ENNReal.toReal_mul]
        at h'
      simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat] at h'
      simp only [a]
      linarith
    set d := a 1 - a 0
    have hd : ∀ j, a (j + 1) - a j = d := by
      intro j
      induction j using Int.induction_on with
      | zero => simp [d]
      | succ k ih => rw [hrec, show (k : ℤ) + 1 - 1 = k by ring, ih]
      | pred k ih =>
        have := hrec (-(k : ℤ))
        rw [show -(k : ℤ) - 1 + 1 = -(k : ℤ) by ring]
        linarith
    have hpos : ∀ n : ℕ, a n = a 0 + n * d := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => push_cast; linarith [hd n]
    have hneg : ∀ n : ℕ, a (-(n : ℤ)) = a 0 - n * d := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have := hd (-((n : ℤ) + 1))
        push_cast
        rw [show -((n : ℤ) + 1) + 1 = -(n : ℤ) by ring] at this
        linarith
    have hd0 : d = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · obtain ⟨n, hn⟩ := exists_nat_gt (a 0 / -d)
        have := ha0 n
        rw [hpos n] at this
        rw [div_lt_iff₀ (by linarith)] at hn
        nlinarith
      · obtain ⟨n, hn⟩ := exists_nat_gt (a 0 / d)
        have := ha0 (-(n : ℤ))
        rw [hneg n] at this
        rw [div_lt_iff₀ h] at hn
        nlinarith
    have hconst : ∀ i, μ i = μ 0 := by
      intro i
      have hi : a i = a 0 := by
        rcases Int.eq_nat_or_neg i with ⟨n, rfl | rfl⟩
        · rw [hpos, hd0]; ring
        · rw [hneg, hd0]; ring
      exact (ENNReal.toReal_eq_toReal_iff' (hfin i) (hfin 0)).1 hi
    have hsum := hμ.2
    simp only [hconst] at hsum
    by_cases h0 : μ 0 = 0
    · simp [h0] at hsum
    · rw [ENNReal.tsum_const_eq_top_of_ne_zero h0] at hsum
      exact ENNReal.top_ne_one hsum

/-! ### The shift: a countable chain without recurrent states -/

/-- The deterministic shift `i ↦ i + 1` on `ℕ`. -/
noncomputable def mc_shift (i j : ℕ) : ℝ≥0∞ := if j = i + 1 then 1 else 0

/-- Miao, p. 98, **counterexample** to "Parts (a)–(b) of Theorem 3.1.1 are still true" for
countable chains: the shift on `ℕ` is a transition matrix with no recurrent state (every state
is transient, `Pr(τᵢ < ∞ | X₀ = i) = 0`), so the state space contains no recurrent class. -/
theorem theorem_3_1_1b_countable_counterexample :
    mc_IsStochasticE mc_shift ∧ ∀ i, mc_hitE mc_shift i i = 0 ∧ mc_IsTransientE mc_shift i := by
  have hP : mc_IsStochasticE mc_shift := fun i => by
    simp only [mc_shift]
    exact tsum_ite_eq (i + 1) 1
  have hpow : ∀ n i j, mc_powE mc_shift n i j = if j = i + n then 1 else 0 := by
    intro n
    induction n with
    | zero => intro i j; simp [mc_powE, mc_idE, eq_comm]
    | succ n ih =>
      intro i j
      simp only [mc_powE, mc_mulE, mc_shift, ih, ite_mul, one_mul, zero_mul]
      rw [tsum_eq_single (i + 1) fun k hk => by simp [hk]]
      simp only [ite_true]
      congr 1
      simp only [eq_iff_iff]
      omega
  refine ⟨hP, fun i => ?_⟩
  have h0 : mc_hitE mc_shift i i = 0 := by
    refine ENNReal.tsum_eq_zero.2 fun n => le_antisymm ?_ bot_le
    calc mc_fpE mc_shift i n i ≤ mc_powE mc_shift (n + 1) i i := mc_fpE_le_powE _ _ _ _
      _ = 0 := by rw [hpow]; simp
  exact ⟨h0, by rw [mc_IsTransientE, h0]; exact one_pos⟩

end Miao.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Transition functions

Copied from `RecursiveMethods/MarkovProcesses` (SLP Chapter 8, module `TransitionFunctions.lean`),
with the
namespace renamed to `Miao.MarkovProcesses`, the results numbered in SLP prefixed
`slp_` and the helper lemmas and definitions prefixed `gp_`.

SLP §8.1, pp. 212–220. A transition function (`IsTransitionFunction`) is exactly a Markov kernel
(`gp_isTransitionFunction_iff`). The Markov operator `T` on nonnegative and on bounded measurable
functions (`markovOp`, `markovOpR`) and its adjoint `T*` on probability measures (`adjointOp`):
Theorem 8.1 and its corollary (`slp_theorem_8_1`, `slp_theorem_8_1_cor`), Exercise 8.1
(`slp_ex_8_1`),
Theorem 8.2 (`slp_theorem_8_2`), Exercise 8.2 (`slp_ex_8_2`), Theorem 8.3 and its corollary
(`slp_theorem_8_3`, `slp_theorem_8_3_cor`), the pairing `⟨f, λ⟩` and Exercise 8.3 (`slp_ex_8_3`),
the
`n`-step transition functions and Exercise 8.4 (`kpow`, `slp_ex_8_4a`, `slp_ex_8_4b`), the sequence
`λₙ = T*ⁿλ₀` (`gp_adjointOp_iterate`), and the Feller and monotonicity properties (`IsFeller`,
`IsMonotoneTF`). Theorems 8.1 and 8.3 follow the book's proofs: indicators, then simple
functions, then increasing limits.
-/

namespace Miao.MarkovProcesses

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {Z : Type*} [MeasurableSpace Z]

/-- A **transition function** (SLP p. 212): each `Q(z, ·)` is a probability measure and each
`Q(·, A)` is measurable. -/
def IsTransitionFunction (Q : Z → Set Z → ℝ≥0∞) : Prop :=
  (∀ z, ∃ μ : Measure Z, IsProbabilityMeasure μ ∧ ∀ A, MeasurableSet A → μ A = Q z A) ∧
    ∀ A, MeasurableSet A → Measurable fun z => Q z A

/-- Transition functions are Mathlib's Markov kernels. -/
theorem gp_isTransitionFunction_iff (Q : Z → Set Z → ℝ≥0∞) :
    IsTransitionFunction Q ↔
      ∃ κ : Kernel Z Z, IsMarkovKernel κ ∧ ∀ z A, MeasurableSet A → κ z A = Q z A := by
  constructor
  · rintro ⟨h1, h2⟩
    choose μ hμ hμQ using h1
    have hm : Measurable μ := Measure.measurable_of_measurable_coe _ fun A hA => by
      have : (fun z => μ z A) = fun z => Q z A := funext fun z => hμQ z A hA
      rw [this]
      exact h2 A hA
    exact ⟨⟨μ, hm⟩, ⟨fun z => hμ z⟩, fun z A hA => hμQ z A hA⟩
  · rintro ⟨κ, hκ, hQ⟩
    refine ⟨fun z => ⟨κ z, inferInstance, fun A hA => hQ z A hA⟩, fun A hA => ?_⟩
    have : (fun z => Q z A) = fun z => κ z A := funext fun z => (hQ z A hA).symm
    rw [this]
    exact κ.measurable_coe hA

variable (κ : Kernel Z Z)

/-- The **Markov operator** on nonnegative functions (SLP (1), p. 213):
`(Tf)(z) = ∫ f(z′) Q(z, dz′)`. -/
noncomputable def markovOp (f : Z → ℝ≥0∞) (z : Z) : ℝ≥0∞ := ∫⁻ z', f z' ∂κ z

/-- The Markov operator on real functions. -/
noncomputable def markovOpR (f : Z → ℝ) (z : Z) : ℝ := ∫ z', f z' ∂κ z

/-- The **adjoint** `T*` (SLP (2), p. 213): `(T*λ)(A) = ∫ Q(z, A) λ(dz)`. -/
noncomputable def adjointOp (lam : Measure Z) : Measure Z := lam.bind κ

theorem gp_markovOp_indicator {A : Set Z} (hA : MeasurableSet A) (c : ℝ≥0∞) (z : Z) :
    markovOp κ (A.indicator fun _ => c) z = c * κ z A := by
  rw [markovOp, lintegral_indicator_const hA]

/-- **Theorem 8.1.** `T` maps nonnegative measurable functions into nonnegative measurable
functions. The book's proof: `Tχ_A = Q(·, A)` is measurable; `T` is additive on simple
functions; and `T` commutes with increasing limits (Monotone Convergence Theorem). -/
theorem slp_theorem_8_1 {f : Z → ℝ≥0∞} (hf : Measurable f) : Measurable (markovOp κ f) := by
  refine Measurable.ennreal_induction (motive := fun f => Measurable (markovOp κ f))
    ?_ ?_ ?_ hf
  · intro c s hs
    have : markovOp κ (s.indicator fun _ => c) = fun z => c * κ z s :=
      funext (gp_markovOp_indicator κ hs c)
    rw [this]
    exact measurable_const.mul (κ.measurable_coe hs)
  · intro f g hfg hf hg ihf ihg
    have : markovOp κ (f + g) = fun z => markovOp κ f z + markovOp κ g z := funext fun z =>
      lintegral_add_left hf _
    rw [this]
    exact ihf.add ihg
  · intro f hf hmono ih
    have : markovOp κ (fun x => ⨆ n, f n x) = fun z => ⨆ n, markovOp κ (f n) z :=
      funext fun z => lintegral_iSup hf hmono
    rw [this]
    exact Measurable.iSup ih

variable [IsMarkovKernel κ]

theorem gp_integrable_of_bounded {μ : Measure Z} [IsFiniteMeasure μ] {f : Z → ℝ} (hf : Measurable f)
    {M : ℝ} (hM : ∀ z, |f z| ≤ M) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable M (Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs]; exact hM z)

/-- **Corollary to Theorem 8.1.** `T` maps bounded measurable functions into bounded measurable
functions: `Tf = Tf⁺ − Tf⁻`, and `|Tf| ≤ sup |f|`. -/
theorem slp_theorem_8_1_cor {f : Z → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ z, |f z| ≤ M) :
    Measurable (markovOpR κ f) ∧ ∀ z, |markovOpR κ f z| ≤ M := by
  constructor
  · have heq : markovOpR κ f = fun z =>
        (markovOp κ (fun z' => ENNReal.ofReal (f z')) z).toReal -
          (markovOp κ (fun z' => ENNReal.ofReal (-f z')) z).toReal := funext fun z =>
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part (gp_integrable_of_bounded hf hM)
    rw [heq]
    exact (slp_theorem_8_1 κ hf.ennreal_ofReal).ennreal_toReal.sub
      (slp_theorem_8_1 κ hf.neg.ennreal_ofReal).ennreal_toReal
  · intro z
    have := norm_integral_le_of_norm_le_const (μ := κ z) (C := M) (f := f)
      (Eventually.of_forall fun z' => by rw [Real.norm_eq_abs]; exact hM z')
    simpa [markovOpR, Real.norm_eq_abs, measureReal_def] using this

/-- **Exercise 8.1.** `T(αf + βg) = αTf + βTg` on bounded measurable functions. -/
theorem slp_ex_8_1 {f g : Z → ℝ} (hf : Measurable f) (hg : Measurable g) {M : ℝ}
    (hfM : ∀ z, |f z| ≤ M) (hgM : ∀ z, |g z| ≤ M) (α β : ℝ) :
    markovOpR κ (fun z => α * f z + β * g z) =
      fun z => α * markovOpR κ f z + β * markovOpR κ g z := by
  funext z
  simp only [markovOpR]
  rw [integral_add ((gp_integrable_of_bounded hf hfM).const_mul α)
    ((gp_integrable_of_bounded hg hgM).const_mul β), integral_const_mul, integral_const_mul]

omit [IsMarkovKernel κ] in
/-- `(T*λ)(A) = ∫ Q(z, A) λ(dz)` (SLP (2)). -/
theorem gp_adjointOp_apply (lam : Measure Z) {A : Set Z} (hA : MeasurableSet A) :
    adjointOp κ lam A = ∫⁻ z, κ z A ∂lam :=
  Measure.bind_apply hA κ.aemeasurable

/-- **Theorem 8.2.** `T*` maps probability measures to probability measures: `T*λ(∅) = 0`,
`T*λ(Z) = 1`, and countable additivity follows from that of each `Q(z, ·)` by the Monotone
Convergence Theorem. -/
theorem slp_theorem_8_2 (lam : Measure Z) [IsProbabilityMeasure lam] :
    IsProbabilityMeasure (adjointOp κ lam) ∧
      ∀ A : ℕ → Set Z, (∀ n, MeasurableSet (A n)) → Pairwise (Function.onFun Disjoint A) →
        ∫⁻ z, κ z (⋃ n, A n) ∂lam = ∑' n, ∫⁻ z, κ z (A n) ∂lam := by
  refine ⟨⟨?_⟩, fun A hA hd => ?_⟩
  · rw [gp_adjointOp_apply κ lam MeasurableSet.univ]
    simp
  · simp_rw [measure_iUnion hd hA]
    exact lintegral_tsum fun n => (κ.measurable_coe (hA n)).aemeasurable

omit [IsMarkovKernel κ] in
/-- **Exercise 8.2.** `T*` is affine: `T*[αλ + (1 − α)μ] = αT*λ + (1 − α)T*μ`. -/
theorem slp_ex_8_2 (lam μ : Measure Z) (α : ℝ≥0∞) :
    adjointOp κ (α • lam + (1 - α) • μ) = α • adjointOp κ lam + (1 - α) • adjointOp κ μ := by
  ext A hA
  simp only [gp_adjointOp_apply κ _ hA, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  rfl

omit [IsMarkovKernel κ] in
/-- **Theorem 8.3.** `∫ (Tf) dλ = ∫ f d(T*λ)` for nonnegative measurable `f`. The book's proof:
indicators, simple functions, then the Monotone Convergence Theorem on both sides. -/
theorem slp_theorem_8_3 (lam : Measure Z) {f : Z → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, markovOp κ f z ∂lam = ∫⁻ z', f z' ∂adjointOp κ lam := by
  refine Measurable.ennreal_induction (motive := fun f =>
    ∫⁻ z, markovOp κ f z ∂lam = ∫⁻ z', f z' ∂adjointOp κ lam) ?_ ?_ ?_ hf
  · intro c s hs
    simp_rw [gp_markovOp_indicator κ hs]
    rw [lintegral_indicator hs, setLIntegral_const, gp_adjointOp_apply κ lam hs,
      lintegral_const_mul _ (κ.measurable_coe hs), mul_comm]
  · intro f g hfg hf hg ihf ihg
    have : ∀ z, markovOp κ (f + g) z = markovOp κ f z + markovOp κ g z := fun z =>
      lintegral_add_left hf _
    simp_rw [this]
    rw [lintegral_add_left (slp_theorem_8_1 κ hf), ihf, ihg, Pi.add_def,
      lintegral_add_left hf]
  · intro f hf hmono ih
    have : ∀ z, markovOp κ (fun x => ⨆ n, f n x) z = ⨆ n, markovOp κ (f n) z := fun z =>
      lintegral_iSup hf hmono
    simp_rw [this]
    rw [lintegral_iSup (fun n => slp_theorem_8_1 κ (hf n))
      (fun m n hmn z => lintegral_mono (hmono hmn)), lintegral_iSup hf hmono]
    simp_rw [ih]

/-- **Corollary to Theorem 8.3.** `∫ (Tf) dλ = ∫ f d(T*λ)` for bounded measurable `f`. -/
theorem slp_theorem_8_3_cor (lam : Measure Z) [IsProbabilityMeasure lam] {f : Z → ℝ}
    (hf : Measurable f) {M : ℝ} (hM : ∀ z, |f z| ≤ M) :
    ∫ z, markovOpR κ f z ∂lam = ∫ z', f z' ∂adjointOp κ lam := by
  have : IsProbabilityMeasure (adjointOp κ lam) := (slp_theorem_8_2 κ lam).1
  have hTf := slp_theorem_8_1_cor κ hf hM
  have hpos : ∀ g : Z → ℝ, Measurable g → (∀ z, |g z| ≤ M) → ∀ z,
      markovOpR κ g z = (markovOp κ (fun z' => ENNReal.ofReal (g z')) z).toReal -
        (markovOp κ (fun z' => ENNReal.ofReal (-g z')) z).toReal := fun g hg hgM z =>
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part (gp_integrable_of_bounded hg hgM)
  have hfin : ∀ g : Z → ℝ, Measurable g → (∀ z, |g z| ≤ M) → ∀ z,
      markovOp κ (fun z' => ENNReal.ofReal (g z')) z ≠ ∞ := fun g hg hgM z =>
    ((gp_integrable_of_bounded hg hgM (μ := κ z)).lintegral_lt_top).ne
  have hbd : ∀ g : Z → ℝ, Measurable g → (∀ z, |g z| ≤ M) →
      Integrable (fun z => (markovOp κ (fun z' => ENNReal.ofReal (g z')) z).toReal) lam :=
    fun g hg hgM => gp_integrable_of_bounded (slp_theorem_8_1 κ hg.ennreal_ofReal).ennreal_toReal
      (M := |M|) fun z => by
        rw [abs_of_nonneg ENNReal.toReal_nonneg]
        refine ENNReal.toReal_le_of_le_ofReal (abs_nonneg M) ?_
        calc markovOp κ (fun z' => ENNReal.ofReal (g z')) z
            ≤ ∫⁻ _, ENNReal.ofReal |M| ∂κ z :=
              lintegral_mono fun z' => ENNReal.ofReal_le_ofReal
                ((le_abs_self _).trans ((hgM z').trans (le_abs_self M)))
          _ = ENNReal.ofReal |M| := by simp
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part (gp_integrable_of_bounded hf hM),
    integral_congr_ae (Eventually.of_forall (hpos f hf hM))]
  rw [integral_sub, integral_toReal (slp_theorem_8_1 κ hf.ennreal_ofReal).aemeasurable
    (Eventually.of_forall fun z => (hfin f hf hM z).lt_top),
    integral_toReal (f := fun z => markovOp κ (fun z' => ENNReal.ofReal (-f z')) z)
      (slp_theorem_8_1 κ hf.neg.ennreal_ofReal).aemeasurable
    (Eventually.of_forall fun z => (hfin (fun z => -f z) hf.neg (fun z => by
      rw [abs_neg]; exact hM z) z).lt_top),
    slp_theorem_8_3 κ lam hf.ennreal_ofReal,
    slp_theorem_8_3 κ lam (f := fun z => ENNReal.ofReal (-f z)) hf.neg.ennreal_ofReal]
  · exact hbd f hf hM
  · exact hbd (fun z => -f z) hf.neg fun z => by rw [abs_neg]; exact hM z

/-- The pairing `⟨f, λ⟩ = ∫ f dλ` (SLP p. 218). -/
noncomputable def gp_pairing (f : Z → ℝ) (lam : Measure Z) : ℝ := ∫ z, f z ∂lam

omit [IsMarkovKernel κ] in
/-- **Exercise 8.3.** The pairing is linear in `f` and affine in `λ`. -/
theorem slp_ex_8_3 {f g : Z → ℝ} (hf : Measurable f) (hg : Measurable g) {M : ℝ}
    (hfM : ∀ z, |f z| ≤ M) (hgM : ∀ z, |g z| ≤ M) (a b : ℝ) (lam μ : Measure Z)
    [IsProbabilityMeasure lam] [IsProbabilityMeasure μ] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    gp_pairing (fun z => a * f z + b * g z) lam = a * gp_pairing f lam + b * gp_pairing g lam ∧
      gp_pairing f (ENNReal.ofReal α • lam + ENNReal.ofReal (1 - α) • μ) =
        α * gp_pairing f lam + (1 - α) * gp_pairing f μ := by
  constructor
  · simp only [gp_pairing]
    rw [integral_add ((gp_integrable_of_bounded hf hfM).const_mul a)
      ((gp_integrable_of_bounded hg hgM).const_mul b), integral_const_mul, integral_const_mul]
  · simp only [gp_pairing]
    rw [integral_add_measure ((gp_integrable_of_bounded hf hfM).smul_measure ENNReal.ofReal_ne_top)
      ((gp_integrable_of_bounded hf hfM).smul_measure ENNReal.ofReal_ne_top),
      integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal hα0,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul, smul_eq_mul]

/-- The `n`-step transition function (SLP p. 219): `Q⁰ = id`,
`Qⁿ⁺¹(z, A) = ∫ Qⁿ(z′, A) Q(z, dz′)`. -/
noncomputable def kpow (κ : Kernel Z Z) : ℕ → Kernel Z Z
  | 0 => Kernel.id
  | n + 1 => kpow κ n ∘ₖ κ

omit [IsMarkovKernel κ] in
theorem gp_kpow_one : kpow κ 1 = κ := by simp [kpow]

/-- **Exercise 8.4a.** The functions `Qⁿ` are transition functions. -/
theorem slp_ex_8_4a (n : ℕ) : IsMarkovKernel (kpow κ n) := by
  induction n with
  | zero => exact inferInstanceAs (IsMarkovKernel Kernel.id)
  | succ n ih => exact inferInstanceAs (IsMarkovKernel (kpow κ n ∘ₖ κ))

omit [IsMarkovKernel κ] in
theorem gp_kpow_add (n m : ℕ) : kpow κ (n + m) = kpow κ m ∘ₖ kpow κ n := by
  induction n with
  | zero => simp [kpow]
  | succ n ih =>
    rw [show n + 1 + m = (n + m) + 1 by omega, kpow, ih, kpow, Kernel.comp_assoc]

omit [IsMarkovKernel κ] in
theorem gp_markovOp_comp (η : Kernel Z Z) {f : Z → ℝ≥0∞} (hf : Measurable f) :
    markovOp (η ∘ₖ κ) f = markovOp κ (markovOp η f) := by
  funext z
  exact Kernel.lintegral_comp η κ z hf

omit [IsMarkovKernel κ] in
theorem gp_adjointOp_comp (η : Kernel Z Z) (lam : Measure Z) :
    adjointOp (η ∘ₖ κ) lam = adjointOp η (adjointOp κ lam) := by
  simp only [adjointOp]
  rw [Measure.bind_bind κ.aemeasurable η.aemeasurable]
  rfl

omit [IsMarkovKernel κ] in
/-- **Exercise 8.4b.** `T⁽ⁿ⁺ᵐ⁾f = Tⁿ(Tᵐf)` and `T*⁽ⁿ⁺ᵐ⁾λ = T*ⁿ(T*ᵐλ)`. -/
theorem slp_ex_8_4b (n m : ℕ) {f : Z → ℝ≥0∞} (hf : Measurable f) (lam : Measure Z) :
    markovOp (kpow κ (n + m)) f = markovOp (kpow κ n) (markovOp (kpow κ m) f) ∧
      adjointOp (kpow κ (n + m)) lam = adjointOp (kpow κ n) (adjointOp (kpow κ m) lam) := by
  constructor
  · rw [gp_kpow_add, gp_markovOp_comp _ _ hf]
  · rw [add_comm, gp_kpow_add, gp_adjointOp_comp]

omit [IsMarkovKernel κ] in
/-- `λₙ = T*λₙ₋₁ = T*ⁿlam₀` (SLP p. 219). -/
theorem gp_adjointOp_iterate (n : ℕ) (lam₀ : Measure Z) :
    (adjointOp κ)^[n] lam₀ = adjointOp (kpow κ n) lam₀ := by
  induction n generalizing lam₀ with
  | zero =>
    change lam₀ = lam₀.bind Kernel.id
    have : (⇑(Kernel.id : Kernel Z Z)) = fun z => Measure.dirac z := funext Kernel.id_apply
    rw [this, Measure.bind_dirac]
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, kpow, gp_adjointOp_comp]

/-- `Q` has the **Feller property** (SLP p. 220): `T` maps bounded continuous functions to
continuous functions. -/
def IsFeller [TopologicalSpace Z] (κ : Kernel Z Z) : Prop :=
  ∀ f : Z → ℝ, Continuous f → (∃ M, ∀ z, |f z| ≤ M) → Continuous (markovOpR κ f)

/-- `Q` is **monotone** (SLP p. 220): `T` maps bounded nondecreasing measurable functions to
nondecreasing functions. -/
def IsMonotoneTF [Preorder Z] (κ : Kernel Z Z) : Prop :=
  ∀ f : Z → ℝ, Measurable f → (∃ M, ∀ z, |f z| ≤ M) → Monotone f → Monotone (markovOpR κ f)

end Miao.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Stochastic kernels, `n`-step transitions and the operators `T`, `T*`

Miao, §3.2, pp. 99–104. A stochastic kernel is a Markov kernel (`definition_3_2_1`); a transition
function is a stochastic kernel from a space to itself (`definition_3_2_1_transition`). Here a
kernel takes values in `[0, ∞]` rather than `[0, 1]`; a probability measure takes values in
`[0, 1]` anyway.

* **Theorem 3.2.1** (`theorem_3_2_1`): the direct product `P₁ ⊗ P₂`, the unique stochastic
  kernel `P₃` on `(W, 𝒳 × 𝒴)` with `P₃(w, A × B) = ∫_A P₂(x, B) P₁(w, dx)`. It is Mathlib's
  `P₁ ⊗ₖ P₂` (with `P₂` not depending on `w`); uniqueness holds because finite measures on a
  product agree once they agree on rectangles.
* **Theorem 3.2.5** and **(3.5)**, which **Exercise 3.2** asks for (`theorem_3_2_5`, `eq_3_4`,
  `eq_3_4_unique`, `eq_3_5`, `ex_3_2`): `Pⁿ = kpow P n` is a transition function, it satisfies
  the Chapman–Kolmogorov recursion (3.4), (3.4) determines it, and
  `Pᵐ⁺ⁿ(a, A) = ∫ Pᵐ(x, A) Pⁿ(a, dx)`.
* **Definition 3.2.2**: `T = markovOpR P` on bounded measurable functions and
  `T* = adjointOp P` on probability measures. **Exercise 3.4** (`ex_3_4`): `T` maps `B(X, 𝒳)`
  into itself, `T*` maps `P(X, 𝒳)` into itself, and
  `∫ Tf dλ = ∫ f d(T*λ) = ∫∫ f(y) P(x, dy) λ(dx)`.
* p. 103: `T⁽ⁿ⁺ᵐ⁾f = Tⁿ(Tᵐf)` and `T*⁽ⁿ⁺ᵐ⁾λ = T*ⁿ(T*ᵐλ)` (`eq_p103_T`, `eq_p103_Tstar`);
  p. 104: `λₙ = T*λₙ₋₁ = T*ⁿλ₀` (`eq_p104_iterate`); invariant distributions
  (`IsInvariantDist`, `isInvariantDist_iff`).

The book defines `Pⁿ` by (3.4), `Pⁿ(a, A) = ∫ P(x, A) Pⁿ⁻¹(a, dx)`; the Lean `kpow P n` (from SLP)
is defined by the other recursion `Pⁿ⁺¹(a, A) = ∫ Pⁿ(x, A) P(a, dx)`, and `eq_3_4_unique` shows
that the two agree.
-/

namespace Miao.MarkovProcesses

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {W X Y : Type*} [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y]

/-- A **stochastic kernel** (Miao, Definition 3.2.1, p. 99): each `P(x, ·)` is a probability
measure on `(Y, 𝒴)`, and each `P(·, A)` is `𝒳`-measurable. -/
def IsStochasticKernel (P : X → Set Y → ℝ≥0∞) : Prop :=
  (∀ x, ∃ μ : Measure Y, IsProbabilityMeasure μ ∧ ∀ A, MeasurableSet A → μ A = P x A) ∧
    ∀ A, MeasurableSet A → Measurable fun x => P x A

/-- **Definition 3.2.1** (Miao, p. 99). Stochastic kernels are exactly Mathlib's Markov kernels. -/
theorem definition_3_2_1 (P : X → Set Y → ℝ≥0∞) :
    IsStochasticKernel P ↔
      ∃ κ : Kernel X Y, IsMarkovKernel κ ∧ ∀ x A, MeasurableSet A → κ x A = P x A := by
  constructor
  · rintro ⟨h1, h2⟩
    choose μ hμ hμP using h1
    have hm : Measurable μ := Measure.measurable_of_measurable_coe _ fun A hA => by
      have : (fun x => μ x A) = fun x => P x A := funext fun x => hμP x A hA
      rw [this]
      exact h2 A hA
    exact ⟨⟨μ, hm⟩, ⟨fun x => hμ x⟩, fun x A hA => hμP x A hA⟩
  · rintro ⟨κ, hκ, hP⟩
    refine ⟨fun x => ⟨κ x, inferInstance, fun A hA => hP x A hA⟩, fun A hA => ?_⟩
    have : (fun x => P x A) = fun x => κ x A := funext fun x => (hP x A hA).symm
    rw [this]
    exact κ.measurable_coe hA

/-- **Definition 3.2.1** (Miao, p. 100): a **transition function** is a stochastic kernel from
`(X, 𝒳)` to itself; this is SLP's notion `IsTransitionFunction`. -/
theorem definition_3_2_1_transition (P : X → Set X → ℝ≥0∞) :
    IsStochasticKernel P ↔ IsTransitionFunction P := Iff.rfl

/-- **Theorem 3.2.1** (Miao, p. 100; SLP Theorem 8.5). For stochastic kernels `P₁` on `(W, 𝒳)`
and `P₂` on `(X, 𝒴)` there is a unique stochastic kernel `P₃` on `(W, 𝒳 × 𝒴)` with
`P₃(w, A × B) = ∫_A P₂(x, B) P₁(w, dx)`; it is the direct product `P₁ ⊗ₖ P₂`. -/
theorem theorem_3_2_1 (P₁ : Kernel W X) [IsMarkovKernel P₁] (P₂ : Kernel X Y)
    [IsMarkovKernel P₂] :
    ∃! P₃ : Kernel W (X × Y), IsMarkovKernel P₃ ∧ ∀ w A B, MeasurableSet A → MeasurableSet B →
      P₃ w (A ×ˢ B) = ∫⁻ x in A, P₂ x B ∂P₁ w := by
  refine ⟨P₁ ⊗ₖ P₂.prodMkLeft W, ⟨inferInstance, fun w A B hA hB => ?_⟩, ?_⟩
  · rw [Kernel.compProd_apply_prod hA hB]
    rfl
  · rintro P₃ ⟨hP₃, h⟩
    ext w : 1
    refine Measure.ext_prod fun {A} {B} hA hB => ?_
    rw [h w A B hA hB, Kernel.compProd_apply_prod hA hB]
    rfl

/-- **(3.4)** (Miao, p. 102), the Chapman–Kolmogorov recursion: `P¹ = P` and
`Pⁿ⁺¹(a, A) = ∫ P(x, A) Pⁿ(a, dx)`. -/
theorem eq_3_4 (P : Kernel X X) (n : ℕ) (a : X) {A : Set X} (hA : MeasurableSet A) :
    kpow P 1 = P ∧ kpow P (n + 1) a A = ∫⁻ x, P x A ∂kpow P n a := by
  refine ⟨gp_kpow_one P, ?_⟩
  rw [gp_kpow_add P n 1, gp_kpow_one, Kernel.comp_apply' _ _ _ hA]

/-- (3.4) determines `Pⁿ` (Miao, p. 102): any sequence of kernels with `Q₁ = P` and
`Qₙ₊₁(a, A) = ∫ P(x, A) Qₙ(a, dx)` is `Qₙ = kpow P n` for all `n ≥ 1`. -/
theorem eq_3_4_unique (P : Kernel X X) (Q : ℕ → Kernel X X) (h1 : Q 1 = P)
    (hs : ∀ n, 1 ≤ n → ∀ a A, MeasurableSet A → Q (n + 1) a A = ∫⁻ x, P x A ∂Q n a) :
    ∀ n, 1 ≤ n → Q n = kpow P n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rw [h1, gp_kpow_one]
  | succ n hn ih =>
    ext a A hA
    rw [hs n hn a A hA, (eq_3_4 P n a hA).2, ih]

/-- **Theorem 3.2.5** (Miao, p. 102). Each `Pⁿ` is a transition function. -/
theorem theorem_3_2_5 (P : Kernel X X) [IsMarkovKernel P] (n : ℕ) : IsMarkovKernel (kpow P n) :=
  slp_ex_8_4a P n

/-- **(3.5)** (Miao, p. 103): `Pᵐ⁺ⁿ(a, A) = ∫ Pᵐ(x, A) Pⁿ(a, dx)`. -/
theorem eq_3_5 (P : Kernel X X) (m n : ℕ) (a : X) {A : Set X} (hA : MeasurableSet A) :
    kpow P (m + n) a A = ∫⁻ x, kpow P m x A ∂kpow P n a := by
  rw [add_comm, gp_kpow_add, Kernel.comp_apply' _ _ _ hA]

/-- **Exercise 3.2** (Miao, p. 113): Theorem 3.2.5 and (3.5). -/
theorem ex_3_2 (P : Kernel X X) [IsMarkovKernel P] :
    (∀ n, IsMarkovKernel (kpow P n)) ∧
      ∀ m n a A, MeasurableSet A → kpow P (m + n) a A = ∫⁻ x, kpow P m x A ∂kpow P n a :=
  ⟨theorem_3_2_5 P, fun m n a _ hA => eq_3_5 P m n a hA⟩

/-- **Exercise 3.4** (Miao, p. 113; Definition 3.2.2, p. 103). `T` maps bounded measurable
functions to bounded measurable functions, `T*` maps probability measures to probability
measures, and `∫ Tf dλ = ∫ f d(T*λ) = ∫∫ f(y) P(x, dy) λ(dx)`. -/
theorem ex_3_4 (P : Kernel X X) [IsMarkovKernel P] {f : X → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) (lam : Measure X) [IsProbabilityMeasure lam] :
    (Measurable (markovOpR P f) ∧ ∀ x, |markovOpR P f x| ≤ M) ∧
      IsProbabilityMeasure (adjointOp P lam) ∧
      ∫ x, markovOpR P f x ∂lam = ∫ y, f y ∂adjointOp P lam ∧
      ∫ y, f y ∂adjointOp P lam = ∫ x, ∫ y, f y ∂P x ∂lam :=
  ⟨slp_theorem_8_1_cor P hf hM, (slp_theorem_8_2 P lam).1,
    slp_theorem_8_3_cor P lam hf hM, (slp_theorem_8_3_cor P lam hf hM).symm⟩

/-- Miao, p. 103: `T⁽ⁿ⁺ᵐ⁾f = Tⁿ(Tᵐf)` for bounded measurable `f`. -/
theorem eq_p103_T (P : Kernel X X) [IsMarkovKernel P] (n m : ℕ) {f : X → ℝ}
    (hf : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) :
    markovOpR (kpow P (n + m)) f = markovOpR (kpow P n) (markovOpR (kpow P m) f) := by
  have := slp_ex_8_4a P m
  have := slp_ex_8_4a P n
  funext x
  rw [gp_kpow_add]
  exact Kernel.integral_comp (gp_integrable_of_bounded hf hM)

/-- Miao, p. 103: `T*⁽ⁿ⁺ᵐ⁾λ = T*ⁿ(T*ᵐλ)`. -/
theorem eq_p103_Tstar (P : Kernel X X) (n m : ℕ) (lam : Measure X) :
    adjointOp (kpow P (n + m)) lam = adjointOp (kpow P n) (adjointOp (kpow P m) lam) :=
  (slp_ex_8_4b P n m measurable_const lam (f := fun _ => 0)).2

/-- Miao, p. 104: `λₙ = T*λₙ₋₁ = T*ⁿλ₀`, and each `λₙ` is a probability measure. -/
theorem eq_p104_iterate (P : Kernel X X) [IsMarkovKernel P] (lam₀ : Measure X)
    [IsProbabilityMeasure lam₀] (n : ℕ) :
    (adjointOp P)^[n + 1] lam₀ = adjointOp P ((adjointOp P)^[n] lam₀) ∧
      (adjointOp P)^[n] lam₀ = adjointOp (kpow P n) lam₀ ∧
      IsProbabilityMeasure (adjointOp (kpow P n) lam₀) := by
  have := slp_ex_8_4a P n
  exact ⟨Function.iterate_succ_apply' _ _ _, gp_adjointOp_iterate P n lam₀,
    (slp_theorem_8_2 (kpow P n) lam₀).1⟩

/-- An **invariant (stationary) distribution** (Miao, p. 104): a probability measure `π` with
`T*π = π`. -/
def IsInvariantDist (P : Kernel X X) (π : Measure X) : Prop :=
  IsProbabilityMeasure π ∧ adjointOp P π = π

/-- Miao, p. 104: `π` is invariant iff `π(A) = ∫ P(x, A) π(dx)` for all `A ∈ 𝒳`. -/
theorem isInvariantDist_iff (P : Kernel X X) (π : Measure X) [IsProbabilityMeasure π] :
    IsInvariantDist P π ↔ ∀ A, MeasurableSet A → π A = ∫⁻ x, P x A ∂π := by
  constructor
  · rintro ⟨-, h⟩ A hA
    rw [← gp_adjointOp_apply P π hA, h]
  · intro h
    refine ⟨inferInstance, Measure.ext fun A hA => ?_⟩
    rw [gp_adjointOp_apply P π hA, ← h A hA]

end Miao.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Measures on sequence spaces: Ionescu Tulcea, Kolmogorov and the Markov process of `(μ₀, P)`

Miao, §3.2, pp. 100–102.

* `gp_eq_of_map_frestrictLe`: a probability measure on `Π n, Xₙ` is determined by its
  finite-dimensional distributions (the uniqueness half of Theorems 3.2.2–3.2.4).
* **Theorem 3.2.4** (Ionescu Tulcea, `theorem_3_2_4`, `tulceaFD`, `tulceaFD_zero`,
  `tulceaFD_succ`): given `Q₀` on `Ω₀` and kernels `Qₙ₊₁(ω₀, …, ωₙ; dωₙ₊₁)`, the measures `Pₙ`
  on `Ω₀ × ⋯ × Ωₙ` defined by the iterated integrals, and a unique `Pr` on `Π Ωₙ` whose
  finite-dimensional distributions are the `Pₙ`; the coordinate process realises them. The
  construction is Mathlib's `Kernel.trajMeasure`.
* **Theorem 3.2.2** (Kolmogorov extension, `theorem_3_2_2`, `eq_3_2_iff`): a sequence of
  probability measures `μₜ` on `Xᵗ⁺¹` satisfying the consistency condition (3.2) extends uniquely
  to `X^∞`. Departure: `X` is assumed to be a standard Borel space. Mathlib has no general
  Kolmogorov extension theorem, and the theorem is false for arbitrary measurable spaces (the
  classical counterexamples of Andersen and Jessen; not formalised here). The proof derives
  Kolmogorov from Ionescu Tulcea: disintegrating `μₜ₊₁` over its first `t + 1` coordinates
  (`Measure.condKernel`, which needs a standard Borel `X`) gives kernels `κₜ` with
  `μₜ₊₁ = μₜ ⊗ κₜ`.
* **Theorem 3.2.3** (`theorem_3_2_3`, `markovPath`) and **Remark 3.2.1** (the coordinate
  process `Xₜ(ω) = ωₜ` on the canonical space): for `μ₀` and a transition function `P` the
  canonical process is Markov with transition function `P`, in the rigorous form that the joint
  law of `(X₀, …, Xₜ, Xₜ₊₁)` is the law of `(X₀, …, Xₜ)` composed with `P(Xₜ, ·)`; in particular
  `Pr(Xₜ ∈ A, Xₜ₊₁ ∈ B) = ∫_A P(x, B) Pr(Xₜ ∈ dx)`, which is the meaning of
  `Pr(Xₜ₊₁ ∈ B | Xₜ = x) = P(x, B)`. `X₀ ~ μ₀`, `Xₜ ~ T*ᵗμ₀`, and `Pr` is the unique measure with
  these properties.

Typo in Theorem 3.2.4: the kernels are stated as `Qₙ : (Ω₀ × ⋯ × Ωₙ) × 𝓕ₙ₊₁ → [0, 1]` for
`n ≥ 1`, but the formula for `Pₙ` uses `Q₁(ω₀; dω₁), …, Qₙ(ω₀, …, ωₙ₋₁; dωₙ)`; the Lean kernel
`κ n` is the book's `Qₙ₊₁(ω₀, …, ωₙ; dωₙ₊₁)`, `n ≥ 0`. The finite products are indexed by
`Finset.Iic n = {0, …, n}`, so the book's `Xᵗ` is `Π i : Iic (t - 1), X`.
-/

namespace Miao.MarkovProcesses

open MeasureTheory ProbabilityTheory Filter Topology Preorder
open scoped ENNReal

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]

/-- Probability measures on `Π n, Xₙ` with the same finite-dimensional distributions on the
initial segments `{0, …, n}` are equal. -/
theorem gp_eq_of_map_frestrictLe {ν ν' : Measure (Π n, X n)} [IsProbabilityMeasure ν]
    (h : ∀ n, ν'.map (frestrictLe n) = ν.map (frestrictLe n)) : ν' = ν := by
  have hproj : IsProjectiveMeasureFamily (fun I : Finset ℕ => ν.map I.restrict) :=
    isProjectiveMeasureFamily_map_restrict (X := fun n (ω : Π n, X n) => ω n) (P := ν)
      (fun t => (measurable_pi_apply t).aemeasurable)
  have h1 : IsProjectiveLimit ν (fun I : Finset ℕ => ν.map I.restrict) := fun _ => rfl
  have h2 : IsProjectiveLimit ν' (fun I : Finset ℕ => ν.map I.restrict) :=
    (isProjectiveLimit_nat_iff hproj ν').2 fun n => h n
  exact h2.unique h1

/-- The finite-dimensional distributions `Pₙ` on `Ω₀ × ⋯ × Ωₙ` of Theorem 3.2.4 (Miao, p. 102):
`P₀ = Q₀` and `Pₙ₊₁` is `Pₙ` followed by `Qₙ₊₁(ω₀, …, ωₙ; dωₙ₊₁)` (`tulceaFD_succ`). -/
noncomputable def tulceaFD (Q₀ : Measure (X 0))
    (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1))) (n : ℕ) :
    Measure (Π i : Finset.Iic n, X i) :=
  Kernel.partialTraj κ 0 n ∘ₘ Q₀.map (MeasurableEquiv.piUnique _).symm

variable (Q₀ : Measure (X 0)) [IsProbabilityMeasure Q₀]
  (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1))) [∀ n, IsMarkovKernel (κ n)]

omit [IsProbabilityMeasure Q₀] in
/-- The marginals of `trajMeasure` are the measures `Pₙ`. -/
theorem gp_trajMeasure_map_frestrictLe (n : ℕ) :
    (Kernel.trajMeasure Q₀ κ).map (frestrictLe n) = tulceaFD Q₀ κ n := by
  rw [Kernel.trajMeasure, Measure.map_comp _ _ (measurable_frestrictLe n),
    Kernel.traj_map_frestrictLe, tulceaFD]

omit [IsProbabilityMeasure Q₀] [∀ n, IsMarkovKernel (κ n)] in
/-- Theorem 3.2.4 (Miao, p. 102): `P₀ = Q₀` (on the one-point product `Ω₀`). -/
theorem tulceaFD_zero : tulceaFD Q₀ κ 0 = Q₀.map (MeasurableEquiv.piUnique _).symm := by
  rw [tulceaFD, Kernel.partialTraj_self, Measure.id_comp]

/-- Theorem 3.2.4 (Miao, p. 102), the iterated integrals:
`Pₙ₊₁(A × Aₙ₊₁) = ∫_A Qₙ₊₁(ω₀, …, ωₙ; Aₙ₊₁) Pₙ(dω₀ ⋯ dωₙ)` for measurable `A ⊆ Ω₀ × ⋯ × Ωₙ`;
for `A = A₀ × ⋯ × Aₙ` and iterated, this is the book's formula for `Pₙ₊₁(A₀ × ⋯ × Aₙ₊₁)`. -/
theorem tulceaFD_succ (n : ℕ) {A : Set (Π i : Finset.Iic n, X i)} (hA : MeasurableSet A)
    {B : Set (X (n + 1))} (hB : MeasurableSet B) :
    tulceaFD Q₀ κ (n + 1)
        {y | frestrictLe₂ (Nat.le_succ n) y ∈ A ∧ y ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ ∈ B} =
      ∫⁻ ω in A, κ n ω B ∂tulceaFD Q₀ κ n := by
  have hm : Measurable fun x : Π n, X n => (frestrictLe n x, x (n + 1)) :=
    (measurable_frestrictLe n).prodMk (measurable_pi_apply _)
  have hS : MeasurableSet
      {y : Π i : Finset.Iic (n + 1), X i |
        frestrictLe₂ (Nat.le_succ n) y ∈ A ∧ y ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ ∈ B} :=
    ((measurable_frestrictLe₂ _) hA).inter ((measurable_pi_apply _) hB)
  rw [← gp_trajMeasure_map_frestrictLe, Measure.map_apply (measurable_frestrictLe _) hS,
    ← gp_trajMeasure_map_frestrictLe, ← Measure.compProd_apply_prod hA hB,
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure,
    Measure.map_apply hm (hA.prod hB)]
  rfl

/-- **Theorem 3.2.4** (Ionescu Tulcea, Miao, p. 102). There is a unique probability measure `Pr`
on `(Π Ωₙ, ⊗ 𝓕ₙ)` whose finite-dimensional distributions are the `Pₙ`, and the coordinate
process `Xₙ(ω) = ωₙ` satisfies `Pr(X₀ ∈ A₀, …, Xₙ ∈ Aₙ) = Pₙ(A₀ × ⋯ × Aₙ)`. -/
theorem theorem_3_2_4 :
    ∃! Pr : Measure (Π n, X n), IsProbabilityMeasure Pr ∧
      (∀ n, Pr.map (frestrictLe n) = tulceaFD Q₀ κ n) ∧
      ∀ (n : ℕ) (A : (i : Finset.Iic n) → Set (X i)), (∀ i, MeasurableSet (A i)) →
        Pr {ω | ∀ i : Finset.Iic n, ω i ∈ A i} = tulceaFD Q₀ κ n (Set.univ.pi A) := by
  refine ⟨Kernel.trajMeasure Q₀ κ, ⟨inferInstance, gp_trajMeasure_map_frestrictLe Q₀ κ,
    fun n A hA => ?_⟩, ?_⟩
  · rw [← gp_trajMeasure_map_frestrictLe, Measure.map_apply (measurable_frestrictLe n)
      (MeasurableSet.univ_pi hA)]
    congr 1
    ext ω
    simp [frestrictLe_apply]
  · rintro Pr ⟨hPr, hmarg, -⟩
    refine gp_eq_of_map_frestrictLe fun n => ?_
    rw [hmarg, gp_trajMeasure_map_frestrictLe]

/-! ### One state space: the snoc map on initial segments -/

variable {Z : Type*} [MeasurableSpace Z]

/-- Append a last coordinate: `((x₀, …, xₜ), z) ↦ (x₀, …, xₜ, z)`. -/
def gp_snocIic (t : ℕ) (p : (Π _ : Finset.Iic t, Z) × Z) : Π _ : Finset.Iic (t + 1), Z :=
  fun i => if h : i.1 ≤ t then p.1 ⟨i.1, Finset.mem_Iic.2 h⟩ else p.2

theorem gp_measurable_snocIic (t : ℕ) : Measurable (gp_snocIic (Z := Z) t) := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases h : i.1 ≤ t
  · simp only [gp_snocIic, h, ↓reduceDIte]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [gp_snocIic, h, ↓reduceDIte]
    exact measurable_snd

omit [MeasurableSpace Z] in
theorem gp_snocIic_pair (t : ℕ) (ω : ℕ → Z) :
    gp_snocIic t (frestrictLe t ω, ω (t + 1)) = frestrictLe (t + 1) ω := by
  funext i
  by_cases h : i.1 ≤ t
  · simp [gp_snocIic, h, frestrictLe_apply]
  · have hi : i.1 = t + 1 := by have := Finset.mem_Iic.1 i.2; omega
    simp [gp_snocIic, frestrictLe_apply, hi]

omit [MeasurableSpace Z] in
theorem gp_snocIic_restrict (t : ℕ) (y : Π _ : Finset.Iic (t + 1), Z) :
    gp_snocIic t (frestrictLe₂ (π := fun _ => Z) (Nat.le_succ t) y,
      y ⟨t + 1, Finset.mem_Iic.2 le_rfl⟩) = y := by
  funext i
  by_cases h : i.1 ≤ t
  · simp [gp_snocIic, h, frestrictLe₂_apply]
  · have hi : i = ⟨t + 1, Finset.mem_Iic.2 le_rfl⟩ := by
      have := Finset.mem_Iic.1 i.2; ext; simp only; omega
    simp [gp_snocIic, hi]

theorem gp_frestrictLe_zero (ω : ℕ → Z) :
    frestrictLe 0 ω = (MeasurableEquiv.piUnique (fun _ : Finset.Iic (0 : ℕ) => Z)).symm (ω 0) := by
  funext i
  have hi : i.1 = 0 := Finset.mem_Iic.1 i.2 |>.antisymm (Nat.zero_le _)
  simp [frestrictLe_apply, hi]

/-! ### Theorem 3.2.3 -/

/-- The kernels `(x₀, …, xₙ) ↦ P(xₙ, ·)` that drive the Markov process. -/
noncomputable def gp_lastKernel (P : Kernel Z Z) (n : ℕ) : Kernel (Π _ : Finset.Iic n, Z) Z :=
  P.comap (fun x => x ⟨n, Finset.mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

theorem gp_isMarkovKernel_lastKernel (P : Kernel Z Z) [IsMarkovKernel P] (n : ℕ) :
    IsMarkovKernel (gp_lastKernel P n) := by
  unfold gp_lastKernel
  infer_instance

/-- The law `Pr` on `(X^∞, 𝒳^∞)` of the Markov process with initial distribution `μ₀` and
transition function `P` (Miao, Theorem 3.2.3, p. 101), built by Ionescu Tulcea. -/
noncomputable def markovPath (P : Kernel Z Z) [IsMarkovKernel P] (μ₀ : Measure Z) :
    Measure (ℕ → Z) :=
  have := gp_isMarkovKernel_lastKernel P
  Kernel.trajMeasure (X := fun _ => Z) μ₀ (gp_lastKernel P)

variable (P : Kernel Z Z) [IsMarkovKernel P] (μ₀ : Measure Z) [IsProbabilityMeasure μ₀]

theorem gp_isProbabilityMeasure_markovPath : IsProbabilityMeasure (markovPath P μ₀) := by
  have := gp_isMarkovKernel_lastKernel P
  unfold markovPath
  infer_instance

/-- The Markov property of `markovPath`: the law of `((X₀, …, Xₜ), Xₜ₊₁)` is the law of
`(X₀, …, Xₜ)` composed with `P(Xₜ, ·)`. -/
theorem gp_markovPath_markov (t : ℕ) :
    (markovPath P μ₀).map (fun ω => (frestrictLe t ω, ω (t + 1))) =
      (markovPath P μ₀).map (frestrictLe t) ⊗ₘ gp_lastKernel P t := by
  have := gp_isMarkovKernel_lastKernel P
  exact (Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ => Z) (μ₀ := μ₀) (κ := gp_lastKernel P) (a := t)).symm

omit [IsProbabilityMeasure μ₀] in
/-- The initial distribution of `markovPath` is `μ₀`. -/
theorem gp_markovPath_map_zero : (markovPath P μ₀).map (fun ω => ω 0) = μ₀ := by
  have := gp_isMarkovKernel_lastKernel P
  have h0 := gp_trajMeasure_map_frestrictLe (X := fun _ => Z) μ₀ (gp_lastKernel P) 0
  rw [tulceaFD_zero] at h0
  have he : (fun ω : ℕ → Z => ω 0) =
      (fun y : Π _ : Finset.Iic (0 : ℕ), Z => y ⟨0, Finset.mem_Iic.2 le_rfl⟩) ∘ frestrictLe 0 :=
    rfl
  have hev : Measurable fun y : Π _ : Finset.Iic (0 : ℕ), Z => y ⟨0, Finset.mem_Iic.2 le_rfl⟩ :=
    measurable_pi_apply _
  rw [he, ← Measure.map_map hev (measurable_frestrictLe 0)]
  change ((Kernel.trajMeasure (X := fun _ => Z) μ₀ (gp_lastKernel P)).map (frestrictLe 0)).map _
    = μ₀
  rw [h0, Measure.map_map hev (MeasurableEquiv.measurable _)]
  exact Measure.map_id

/-- Uniqueness for Theorem 3.2.3: a probability measure on paths with initial law `μ₀` and the
Markov property for `P` is `markovPath P μ₀`. -/
theorem gp_markovPath_unique {Pr : Measure (ℕ → Z)} [IsProbabilityMeasure Pr]
    (h0 : Pr.map (fun ω => ω 0) = μ₀)
    (hM : ∀ t, Pr.map (fun ω => (frestrictLe t ω, ω (t + 1))) =
      Pr.map (frestrictLe t) ⊗ₘ gp_lastKernel P t) : Pr = markovPath P μ₀ := by
  have := gp_isProbabilityMeasure_markovPath P μ₀
  have := gp_isMarkovKernel_lastKernel P
  refine gp_eq_of_map_frestrictLe fun t => ?_
  induction t with
  | zero =>
    have he : (frestrictLe 0 : (ℕ → Z) → _) =
        (MeasurableEquiv.piUnique (fun _ : Finset.Iic (0 : ℕ) => Z)).symm ∘ fun ω => ω 0 :=
      funext gp_frestrictLe_zero
    have hev0 : Measurable fun ω : ℕ → Z => ω 0 := measurable_pi_apply 0
    rw [he, ← Measure.map_map (MeasurableEquiv.measurable _) hev0,
      ← Measure.map_map (MeasurableEquiv.measurable _) hev0, h0,
      gp_markovPath_map_zero]
  | succ t ih =>
    have hp : Measurable fun ω : ℕ → Z => (frestrictLe t ω, ω (t + 1)) :=
      (measurable_frestrictLe t).prodMk (measurable_pi_apply _)
    have he : (frestrictLe (t + 1) : (ℕ → Z) → _) =
        gp_snocIic t ∘ fun ω => (frestrictLe t ω, ω (t + 1)) :=
      funext fun ω => (gp_snocIic_pair t ω).symm
    rw [he, ← Measure.map_map (gp_measurable_snocIic t) hp,
      ← Measure.map_map (gp_measurable_snocIic t) hp, hM, gp_markovPath_markov, ih]

/-- **Theorem 3.2.3** (Miao, p. 101). For a probability measure `μ₀` and a transition function
`P` there is a unique probability measure `Pr` on `(X^∞, 𝒳^∞)` under which the coordinate process
`Xₜ(ω) = ωₜ` (Remark 3.2.1) has `X₀ ~ μ₀` and is Markov with transition function `P`: the joint
law of `((X₀, …, Xₜ), Xₜ₊₁)` is the law of `(X₀, …, Xₜ)` composed with `P(Xₜ, ·)`. -/
theorem theorem_3_2_3 :
    ∃! Pr : Measure (ℕ → Z), IsProbabilityMeasure Pr ∧ Pr.map (fun ω => ω 0) = μ₀ ∧
      ∀ t, Pr.map (fun ω => (frestrictLe t ω, ω (t + 1))) =
        Pr.map (frestrictLe t) ⊗ₘ gp_lastKernel P t := by
  refine ⟨markovPath P μ₀, ⟨gp_isProbabilityMeasure_markovPath P μ₀,
    gp_markovPath_map_zero P μ₀, gp_markovPath_markov P μ₀⟩, ?_⟩
  rintro Pr ⟨hPr, h0, hM⟩
  exact gp_markovPath_unique P μ₀ h0 hM

/-- **Theorem 3.2.3 (a)** (Miao, p. 101): `Pr(Xₜ₊₁ ∈ B | Xₜ = x) = P(x, B)`, in the form
`law(Xₜ, Xₜ₊₁) = law(Xₜ) ⊗ P`, that is `Pr(Xₜ ∈ A, Xₜ₊₁ ∈ B) = ∫_A P(x, B) Pr(Xₜ ∈ dx)`. -/
theorem theorem_3_2_3_transition (t : ℕ) :
    (markovPath P μ₀).map (fun ω => (ω t, ω (t + 1))) =
        (markovPath P μ₀).map (fun ω => ω t) ⊗ₘ P ∧
      ∀ A B, MeasurableSet A → MeasurableSet B →
        markovPath P μ₀ {ω | ω t ∈ A ∧ ω (t + 1) ∈ B} =
          ∫⁻ x in A, P x B ∂(markovPath P μ₀).map (fun ω => ω t) := by
  have := gp_isProbabilityMeasure_markovPath P μ₀
  have := gp_isMarkovKernel_lastKernel P
  have hpair : Measurable fun ω : ℕ → Z => (ω t, ω (t + 1)) :=
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  have hlaw : (markovPath P μ₀).map (fun ω => (ω t, ω (t + 1))) =
      (markovPath P μ₀).map (fun ω => ω t) ⊗ₘ P := by
    refine Measure.ext_prod fun {A} {B} hA hB => ?_
    have hev : Measurable fun y : Π _ : Finset.Iic t, Z => y ⟨t, Finset.mem_Iic.2 le_rfl⟩ :=
      measurable_pi_apply _
    have hp : Measurable fun ω : ℕ → Z => (frestrictLe t ω, ω (t + 1)) :=
      (measurable_frestrictLe t).prodMk (measurable_pi_apply _)
    have hset : (fun ω : ℕ → Z => (ω t, ω (t + 1))) ⁻¹' A ×ˢ B =
        (fun ω : ℕ → Z => (frestrictLe t ω, ω (t + 1))) ⁻¹'
          (((fun y : Π _ : Finset.Iic t, Z => y ⟨t, Finset.mem_Iic.2 le_rfl⟩) ⁻¹' A) ×ˢ B) :=
      rfl
    have hlt : (fun ω : ℕ → Z => ω t) =
        (fun y : Π _ : Finset.Iic t, Z => y ⟨t, Finset.mem_Iic.2 le_rfl⟩) ∘ frestrictLe t := rfl
    rw [Measure.map_apply hpair (hA.prod hB), hset, ← Measure.map_apply hp ((hev hA).prod hB),
      gp_markovPath_markov, Measure.compProd_apply_prod (hev hA) hB,
      Measure.compProd_apply_prod hA hB, hlt, ← Measure.map_map hev (measurable_frestrictLe t),
      setLIntegral_map hA (P.measurable_coe hB) hev]
    rfl
  refine ⟨hlaw, fun A B hA hB => ?_⟩
  rw [← Measure.compProd_apply_prod hA hB, ← hlaw, Measure.map_apply hpair (hA.prod hB)]
  rfl

/-- Theorem 3.2.3 and p. 104: under `Pr`, `X₀ ~ μ₀` and `Xₜ ~ T*ᵗμ₀ = λₜ`. -/
theorem theorem_3_2_3_marginal (t : ℕ) :
    (markovPath P μ₀).map (fun ω => ω t) = adjointOp (kpow P t) μ₀ := by
  have := gp_isProbabilityMeasure_markovPath P μ₀
  induction t with
  | zero => rw [gp_markovPath_map_zero, ← gp_adjointOp_iterate P 0 μ₀]; rfl
  | succ t ih =>
    have hpair : Measurable fun ω : ℕ → Z => (ω t, ω (t + 1)) :=
      (measurable_pi_apply _).prodMk (measurable_pi_apply _)
    have hs : (markovPath P μ₀).map (fun ω => ω (t + 1)) =
        ((markovPath P μ₀).map (fun ω => (ω t, ω (t + 1)))).snd := by
      rw [Measure.snd, Measure.map_map measurable_snd hpair]
      rfl
    rw [hs, (theorem_3_2_3_transition P μ₀ t).1, Measure.snd_compProd, ih, add_comm,
      eq_p103_Tstar, gp_kpow_one]
    rfl

/-! ### Theorem 3.2.2 (Kolmogorov extension) -/

/-- Append `X` as the last factor of a rectangle: `A₀ × ⋯ × Aₜ ↦ A₀ × ⋯ × Aₜ × X`. -/
def gp_extendBox (t : ℕ) (A : Finset.Iic t → Set Z) : Finset.Iic (t + 1) → Set Z :=
  fun i => if h : i.1 ≤ t then A ⟨i.1, Finset.mem_Iic.2 h⟩ else Set.univ

omit [MeasurableSpace Z] in
theorem gp_preimage_extendBox (t : ℕ) (A : Finset.Iic t → Set Z) :
    frestrictLe₂ (π := fun _ => Z) (Nat.le_succ t) ⁻¹' Set.univ.pi A =
      Set.univ.pi (gp_extendBox t A) := by
  ext y
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, frestrictLe₂_apply]
  constructor
  · intro h i
    by_cases hi : i.1 ≤ t
    · simpa [gp_extendBox, hi] using h ⟨i.1, Finset.mem_Iic.2 hi⟩
    · simp [gp_extendBox, hi]
  · intro h i
    have := h ⟨i.1, Finset.mem_Iic.2 ((Finset.mem_Iic.1 i.2).trans (Nat.le_succ t))⟩
    simpa [gp_extendBox, Finset.mem_Iic.1 i.2] using this

/-- **(3.2)** (Miao, p. 100), the Kolmogorov consistency condition
`μₜ(A₀ × ⋯ × Aₜ) = μₜ₊₁(A₀ × ⋯ × Aₜ × X)`, is equivalent to `μₜ` being the image of `μₜ₊₁`
under the projection forgetting the last coordinate. -/
theorem eq_3_2_iff (μ : (n : ℕ) → Measure (Π _ : Finset.Iic n, Z))
    [∀ n, IsProbabilityMeasure (μ n)] (t : ℕ) :
    (∀ A : Finset.Iic t → Set Z, (∀ i, MeasurableSet (A i)) →
        μ t (Set.univ.pi A) = μ (t + 1) (Set.univ.pi (gp_extendBox t A))) ↔
      (μ (t + 1)).map (frestrictLe₂ (π := fun _ => Z) (Nat.le_succ t)) = μ t := by
  have hm : Measurable (frestrictLe₂ (π := fun _ => Z) (Nat.le_succ t)) :=
    measurable_frestrictLe₂ _
  constructor
  · intro h
    have : IsProbabilityMeasure
        ((μ (t + 1)).map (frestrictLe₂ (π := fun _ => Z) (Nat.le_succ t))) := inferInstance
    refine (ext_of_generate_finite _ generateFrom_pi.symm isPiSystem_pi ?_ (by simp)).symm
    rintro _ ⟨A, hA, rfl⟩
    rw [h A fun i => hA i (Set.mem_univ i), Measure.map_apply hm
      (MeasurableSet.univ_pi fun i => hA i (Set.mem_univ i)), gp_preimage_extendBox]
  · intro h A hA
    rw [← h, Measure.map_apply hm (MeasurableSet.univ_pi hA), gp_preimage_extendBox]

/-- **Theorem 3.2.2** (Kolmogorov extension, Miao, p. 100). Let `X` be a standard Borel space and
`μₜ` probability measures on `Xᵗ⁺¹ = Π i ∈ {0, …, t}, X` satisfying the consistency condition
(3.2). Then there is a unique probability measure `μ` on `X^∞` with `μ(A × X^∞) = μₜ(A)` for all
measurable `A ⊆ Xᵗ⁺¹`, i.e. `μₜ` is the image of `μ` under `ω ↦ (ω₀, …, ωₜ)`. The proof
disintegrates `μₜ₊₁ = μₜ ⊗ κₜ` and applies Ionescu Tulcea (Theorem 3.2.4). -/
theorem theorem_3_2_2 [StandardBorelSpace Z] (μ : (n : ℕ) → Measure (Π _ : Finset.Iic n, Z))
    [∀ n, IsProbabilityMeasure (μ n)]
    (h32 : ∀ t (A : Finset.Iic t → Set Z), (∀ i, MeasurableSet (A i)) →
      μ t (Set.univ.pi A) = μ (t + 1) (Set.univ.pi (gp_extendBox t A))) :
    ∃! ν : Measure (ℕ → Z), IsProbabilityMeasure ν ∧ ∀ n, ν.map (frestrictLe n) = μ n := by
  have hcons : ∀ t, (μ (t + 1)).map (frestrictLe₂ (π := fun _ => Z) (Nat.le_succ t)) = μ t :=
    fun t => (eq_3_2_iff μ t).1 (h32 t)
  obtain ⟨y₀⟩ := nonempty_of_isProbabilityMeasure (μ 0)
  have : Nonempty Z := ⟨y₀ ⟨0, Finset.mem_Iic.2 le_rfl⟩⟩
  -- the pair `((x₀, …, xₜ), xₜ₊₁)` of an element of `Xᵗ⁺²`
  let pr : (t : ℕ) → (Π _ : Finset.Iic (t + 1), Z) → (Π _ : Finset.Iic t, Z) × Z := fun t y =>
    (frestrictLe₂ (π := fun _ => Z) (Nat.le_succ t) y, y ⟨t + 1, Finset.mem_Iic.2 le_rfl⟩)
  have hpr : ∀ t, Measurable (pr t) := fun t =>
    (measurable_frestrictLe₂ (X := fun _ => Z) (Nat.le_succ t)).prodMk
      (measurable_pi_apply (⟨t + 1, Finset.mem_Iic.2 le_rfl⟩ : Finset.Iic (t + 1)))
  let ρ : (t : ℕ) → Measure ((Π _ : Finset.Iic t, Z) × Z) := fun t => (μ (t + 1)).map (pr t)
  have hρ : ∀ t, IsProbabilityMeasure (ρ t) := fun t =>
    inferInstance
  have hfst : ∀ t, (ρ t).fst = μ t := fun t => by
    rw [Measure.fst, Measure.map_map measurable_fst (hpr t)]
    exact hcons t
  let κ : (t : ℕ) → Kernel (Π _ : Finset.Iic t, Z) Z := fun t => (ρ t).condKernel
  have hdis : ∀ t, μ t ⊗ₘ κ t = ρ t := fun t => by
    rw [← hfst t]
    exact (ρ t).disintegrate (ρ t).condKernel
  let μ₀ : Measure Z := (μ 0).map fun y => y ⟨0, Finset.mem_Iic.2 le_rfl⟩
  have hμ₀ : IsProbabilityMeasure μ₀ :=
    inferInstance
  let ν : Measure (ℕ → Z) := Kernel.trajMeasure (X := fun _ => Z) μ₀ κ
  have hmarg : ∀ n, ν.map (frestrictLe n) = μ n := by
    intro n
    induction n with
    | zero =>
      have h0 := gp_trajMeasure_map_frestrictLe (X := fun _ => Z) μ₀ κ 0
      rw [tulceaFD_zero] at h0
      change (Kernel.trajMeasure (X := fun _ => Z) μ₀ κ).map (frestrictLe 0) = μ 0
      rw [h0]
      change Measure.map _ (Measure.map
        (fun y : Π _ : Finset.Iic (0 : ℕ), Z => y ⟨0, Finset.mem_Iic.2 le_rfl⟩) (μ 0)) = μ 0
      have hev : Measurable fun y : Π _ : Finset.Iic (0 : ℕ), Z => y ⟨0, Finset.mem_Iic.2 le_rfl⟩ :=
        measurable_pi_apply _
      rw [Measure.map_map (MeasurableEquiv.measurable _) hev]
      have hid : ((MeasurableEquiv.piUnique (fun _ : Finset.Iic (0 : ℕ) => Z)).symm ∘
          fun y : Π _ : Finset.Iic (0 : ℕ), Z => y ⟨0, Finset.mem_Iic.2 le_rfl⟩) = id := by
        funext y i
        have hi : i = ⟨0, Finset.mem_Iic.2 le_rfl⟩ := Subsingleton.elim _ _
        subst hi
        rfl
      rw [hid, Measure.map_id]
    | succ n ih =>
      have hp : Measurable fun ω : ℕ → Z => (frestrictLe n ω, ω (n + 1)) :=
        (measurable_frestrictLe n).prodMk (measurable_pi_apply _)
      have he : (frestrictLe (n + 1) : (ℕ → Z) → _) =
          gp_snocIic n ∘ fun ω => (frestrictLe n ω, ω (n + 1)) :=
        funext fun ω => (gp_snocIic_pair n ω).symm
      have hkey := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
        (X := fun _ => Z) (μ₀ := μ₀) (κ := κ) (a := n)
      have hid : gp_snocIic n ∘ pr n = id := funext fun y => gp_snocIic_restrict n y
      rw [he, ← Measure.map_map (gp_measurable_snocIic n) hp]
      change ((Kernel.trajMeasure (X := fun _ => Z) μ₀ κ).map _).map _ = _
      rw [← hkey]
      change (ν.map (frestrictLe n) ⊗ₘ κ n).map _ = _
      rw [ih, hdis, Measure.map_map (gp_measurable_snocIic n) (hpr n), hid, Measure.map_id]
  have hν : IsProbabilityMeasure ν := by
    change IsProbabilityMeasure (Kernel.trajMeasure (X := fun _ => Z) μ₀ κ)
    infer_instance
  refine ⟨ν, ⟨hν, hmarg⟩, ?_⟩
  rintro ν' ⟨hν', hmarg'⟩
  exact gp_eq_of_map_frestrictLe fun n => by rw [hmarg', hmarg]

end Miao.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The total variation norm

Copied from `RecursiveMethods/StrongConvergence` (SLP Chapter 11, module `TotalVariation.lean`),
with the
namespace renamed to `Miao.MarkovProcesses`, the results numbered in SLP prefixed
`slp_` and the helper lemmas and definitions prefixed `gp_`.

SLP §11.3, pp. 338–344. For a set function `D` (a signed measure, or `λ₁ − λ₂` for finite
measures) the total variation is `‖D‖ = sup Σᵢ |D(Aᵢ)|` over finite measurable partitions
`A₁, …, Aₖ` of `S` (`gp_tvOf`, (1) on p. 339). `tvNorm ν` is the norm of a signed measure (the
book's
`Φ(S, 𝒮)` is Mathlib's `SignedMeasure S`), and `tvDist λ₁ λ₂ = ‖λ₁ − λ₂‖`.

* **Exercise 11.3** (`slp_ex_11_3`): every signed measure is a difference of finite measures, and
  `‖·‖` is a norm on signed measures.
* **Lemma 11.5** (`slp_lemma_11_5`): for finite measures of equal mass,
  `‖λ₁ − λ₂‖ = 2 sup_A |λ₁(A) − λ₂(A)|`. The book proves it for probability measures, using
  Lemma 7.12, and applies it in Lemma 11.11 to measures of equal but smaller mass. Here it is
  proved for equal masses, using the Hahn decomposition.
-/

namespace Miao.MarkovProcesses

open MeasureTheory Set Finset
open scoped Pointwise

variable {S : Type*} [MeasurableSpace S]

/-- A finite measurable partition `A₁, …, Aₖ` of `S`. -/
def gp_IsPartition {k : ℕ} (A : Fin k → Set S) : Prop :=
  (∀ i, MeasurableSet (A i)) ∧ Pairwise (Function.onFun Disjoint A) ∧ ⋃ i, A i = Set.univ

/-- The sums `Σᵢ |D(Aᵢ)|` over finite measurable partitions. -/
def gp_partSums (D : Set S → ℝ) : Set ℝ :=
  {x | ∃ k, ∃ A : Fin k → Set S, gp_IsPartition A ∧ x = ∑ i, |D (A i)|}

/-- The total variation `sup Σᵢ |D(Aᵢ)|` over finite measurable partitions ((1), p. 339). -/
noncomputable def gp_tvOf (D : Set S → ℝ) : ℝ := sSup (gp_partSums D)

/-- The **total variation norm** of a signed measure. -/
noncomputable def tvNorm (ν : SignedMeasure S) : ℝ := gp_tvOf fun A => ν A

/-- `‖λ₁ − λ₂‖` for finite measures. -/
noncomputable def tvDist (μ₁ μ₂ : Measure S) : ℝ := gp_tvOf fun A => μ₁.real A - μ₂.real A

/-- `sup_A |λ₁(A) − λ₂(A)|` over measurable `A`. -/
noncomputable def gp_supDiff (μ₁ μ₂ : Measure S) : ℝ :=
  sSup ((fun A => |μ₁.real A - μ₂.real A|) '' {A | MeasurableSet A})

theorem gp_isPartition_univ : gp_IsPartition (fun _ : Fin 1 => (Set.univ : Set S)) :=
  ⟨fun _ => MeasurableSet.univ, fun i j hij => absurd (Subsingleton.elim i j) hij,
    iUnion_const _⟩

/-- The partition `{B, Bᶜ}`. -/
theorem gp_isPartition_pair {B : Set S} (hB : MeasurableSet B) :
    gp_IsPartition (fun i : Fin 2 => if i = 0 then B else Bᶜ) := by
  refine ⟨fun i => ?_, fun i j hij => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact hB
    · exact hB.compl
  · fin_cases i <;> fin_cases j <;> simp_all [Function.onFun, disjoint_compl_right,
      disjoint_compl_left]
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    by_cases hx : x ∈ B
    · exact ⟨0, by simpa using hx⟩
    · exact ⟨1, by simpa using hx⟩

theorem gp_partSums_nonempty (D : Set S → ℝ) : (gp_partSums D).Nonempty :=
  ⟨_, 1, _, gp_isPartition_univ, rfl⟩

/-- A finite measure of a partition adds up to the whole. -/
theorem gp_sum_partition_real (μ : Measure S) [IsFiniteMeasure μ] {k : ℕ} {A : Fin k → Set S}
    (hA : gp_IsPartition A) : ∑ i, μ.real (A i) = μ.real Set.univ := by
  rw [← measureReal_iUnion_fintype hA.2.1 hA.1, hA.2.2]

theorem gp_sum_partition_inter_real (μ : Measure S) [IsFiniteMeasure μ] {k : ℕ}
    {A : Fin k → Set S} (hA : gp_IsPartition A) {B : Set S} (hB : MeasurableSet B) :
    ∑ i, μ.real (A i ∩ B) = μ.real B := by
  rw [← measureReal_iUnion_fintype (fun i j hij => (hA.2.1 hij).mono inter_subset_left
    inter_subset_left) fun i => (hA.1 i).inter hB, ← iUnion_inter, hA.2.2, univ_inter]

theorem gp_partSums_bddAbove_of_le {D : Set S → ℝ} {C : ℝ}
    (h : ∀ k (A : Fin k → Set S), gp_IsPartition A → ∑ i, |D (A i)| ≤ C) :
    BddAbove (gp_partSums D) :=
  ⟨C, by rintro _ ⟨k, A, hA, rfl⟩; exact h k A hA⟩

/-- For finite measures the partition sums are bounded by `λ₁(S) + λ₂(S)`. -/
theorem gp_partSums_le_of_measures (μ₁ μ₂ : Measure S) [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂] {k : ℕ} {A : Fin k → Set S} (hA : gp_IsPartition A) :
    ∑ i, |μ₁.real (A i) - μ₂.real (A i)| ≤ μ₁.real Set.univ + μ₂.real Set.univ := by
  rw [← gp_sum_partition_real μ₁ hA, ← gp_sum_partition_real μ₂ hA, ← sum_add_distrib]
  exact sum_le_sum fun i _ => (abs_sub _ _).trans (by
    rw [abs_of_nonneg measureReal_nonneg, abs_of_nonneg measureReal_nonneg])

theorem gp_bddAbove_tvDist (μ₁ μ₂ : Measure S) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] :
    BddAbove (gp_partSums fun A => μ₁.real A - μ₂.real A) :=
  gp_partSums_bddAbove_of_le fun _ _ hA => gp_partSums_le_of_measures μ₁ μ₂ hA

/-- **Lemma 11.5**, for finite measures of equal mass: `‖λ₁ − λ₂‖ = 2 sup_A |λ₁(A) − λ₂(A)|`.
Let `B` be a Hahn set (`λ₁ ≥ λ₂` on subsets of `B`, `λ₁ ≤ λ₂` on subsets of `Bᶜ`) and
`D = λ₁ − λ₂`. Then `|D(A)| ≤ D(B)` for every `A`, each partition sum is at most
`D(B) − D(Bᶜ) = 2D(B)`, and `{B, Bᶜ}` attains it. -/
theorem slp_lemma_11_5 (μ₁ μ₂ : Measure S) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (h : μ₁ Set.univ = μ₂ Set.univ) :
    tvDist μ₁ μ₂ = 2 * gp_supDiff μ₁ μ₂ ∧ ∃ B, MeasurableSet B ∧
      gp_supDiff μ₁ μ₂ = μ₁.real B - μ₂.real B ∧ μ₂.real Bᶜ - μ₁.real Bᶜ = μ₁.real B - μ₂.real B :=
          by
  obtain ⟨B, hB, hpos, hneg⟩ := hahn_decomposition μ₁ μ₂
  set D : Set S → ℝ := fun A => μ₁.real A - μ₂.real A
  have hP : ∀ t, MeasurableSet t → t ⊆ B → 0 ≤ D t := fun t ht htB => by
    have := ENNReal.toReal_mono (measure_ne_top μ₁ t) (hpos t ht htB)
    simp only [D, measureReal_def]; linarith
  have hN : ∀ t, MeasurableSet t → t ⊆ Bᶜ → D t ≤ 0 := fun t ht htB => by
    have := ENNReal.toReal_mono (measure_ne_top μ₂ t) (hneg t ht htB)
    simp only [D, measureReal_def]; linarith
  have hsplit : ∀ A, MeasurableSet A → D A = D (A ∩ B) + D (A ∩ Bᶜ) := fun A hA => by
    have h1 := measureReal_inter_add_sdiff (μ := μ₁) (s := A) hB
    have h2 := measureReal_inter_add_sdiff (μ := μ₂) (s := A) hB
    rw [sdiff_eq] at h1 h2
    simp only [D]; linarith
  have hcompl : D Bᶜ = -D B := by
    have h1 := measureReal_add_measureReal_compl (μ := μ₁) hB
    have h2 := measureReal_add_measureReal_compl (μ := μ₂) hB
    have h3 : μ₁.real Set.univ = μ₂.real Set.univ := by simp only [measureReal_def, h]
    simp only [D]; linarith
  have hDB : 0 ≤ D B := hP B hB subset_rfl
  -- `|D(A)| ≤ D(B)`
  have habs : ∀ A, MeasurableSet A → |D A| ≤ D B := by
    intro A hA
    have e1 := hsplit A hA
    have e2 := hsplit B hB
    have e3 := hsplit Bᶜ hB.compl
    have a1 := hP (A ∩ B) (hA.inter hB) inter_subset_right
    have a2 := hN (A ∩ Bᶜ) (hA.inter hB.compl) inter_subset_right
    have a3 : D (B ∩ Bᶜ) = 0 := by simp [D]
    have hBA : D (A ∩ B) ≤ D B := by
      have := hsplit (B) hB
      have h4 := measureReal_inter_add_sdiff (μ := μ₁) (s := B) hA
      have h5 := measureReal_inter_add_sdiff (μ := μ₂) (s := B) hA
      have h6 := hP (B \ A) (hB.diff hA) sdiff_subset
      rw [inter_comm] at h4 h5
      simp only [D] at h6 ⊢; linarith
    have hBA' : D Bᶜ ≤ D (A ∩ Bᶜ) := by
      have h4 := measureReal_inter_add_sdiff (μ := μ₁) (s := Bᶜ) hA
      have h5 := measureReal_inter_add_sdiff (μ := μ₂) (s := Bᶜ) hA
      have h6 := hN (Bᶜ \ A) (hB.compl.diff hA) sdiff_subset
      rw [inter_comm] at h4 h5
      simp only [D] at h6 ⊢; linarith
    rw [abs_le]; constructor <;> linarith
  -- every partition sum is at most `2 D(B)`
  have hpart : ∀ k (A : Fin k → Set S), gp_IsPartition A → ∑ i, |D (A i)| ≤ 2 * D B := by
    intro k A hA
    calc ∑ i, |D (A i)| ≤ ∑ i, (D (A i ∩ B) - D (A i ∩ Bᶜ)) := sum_le_sum fun i _ => by
          rw [hsplit (A i) (hA.1 i)]
          have := hP (A i ∩ B) ((hA.1 i).inter hB) inter_subset_right
          have := hN (A i ∩ Bᶜ) ((hA.1 i).inter hB.compl) inter_subset_right
          rw [abs_le]; constructor <;> linarith
      _ = D B - D Bᶜ := by
          simp only [D, sum_sub_distrib, gp_sum_partition_inter_real μ₁ hA hB,
            gp_sum_partition_inter_real μ₂ hA hB, gp_sum_partition_inter_real μ₁ hA hB.compl,
            gp_sum_partition_inter_real μ₂ hA hB.compl]
      _ = 2 * D B := by rw [hcompl]; ring
  have htv : tvDist μ₁ μ₂ = 2 * D B := by
    refine le_antisymm (csSup_le (gp_partSums_nonempty _) ?_) ?_
    · rintro _ ⟨k, A, hA, rfl⟩; exact hpart k A hA
    · refine le_csSup (gp_bddAbove_tvDist μ₁ μ₂) ⟨2, _, gp_isPartition_pair hB, ?_⟩
      simp only [Fin.sum_univ_two, Fin.isValue, ↓reduceIte, one_ne_zero]
      change 2 * D B = |D B| + |D Bᶜ|
      rw [hcompl, abs_neg, abs_of_nonneg hDB]; ring
  have hsup : gp_supDiff μ₁ μ₂ = D B := by
    refine le_antisymm (csSup_le ⟨_, ∅, MeasurableSet.empty, rfl⟩ ?_) ?_
    · rintro _ ⟨A, hA, rfl⟩; exact habs A hA
    · refine le_csSup ⟨D B, ?_⟩ ⟨B, hB, abs_of_nonneg hDB⟩
      rintro _ ⟨A, hA, rfl⟩; exact habs A hA
  refine ⟨by rw [htv, hsup], B, hB, hsup, ?_⟩
  have := hcompl
  simp only [D] at this ⊢; linarith

/-- Every signed measure is a difference of finite measures (its Jordan decomposition). -/
theorem gp_exists_sub_measures (ν : SignedMeasure S) :
    ∃ (μ₁ μ₂ : Measure S) (_ : IsFiniteMeasure μ₁) (_ : IsFiniteMeasure μ₂),
      ν = μ₁.toSignedMeasure - μ₂.toSignedMeasure :=
  ⟨_, _, inferInstance, inferInstance, (SignedMeasure.toSignedMeasure_toJordanDecomposition ν).symm⟩

theorem gp_tvNorm_sub_eq (μ₁ μ₂ : Measure S) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] :
    tvNorm (μ₁.toSignedMeasure - μ₂.toSignedMeasure) = tvDist μ₁ μ₂ := by
  unfold tvNorm tvDist gp_tvOf gp_partSums
  congr 1
  ext x
  refine exists_congr fun k => exists_congr fun A => and_congr_right fun hA => ?_
  have e : ∑ i, |(μ₁.toSignedMeasure - μ₂.toSignedMeasure) (A i)| =
      ∑ i, |μ₁.real (A i) - μ₂.real (A i)| :=
    sum_congr rfl fun i _ => by rw [Measure.toSignedMeasure_sub_apply (hA.1 i)]
  exact Iff.of_eq (congrArg (x = ·) e)

theorem gp_bddAbove_tvNorm (ν : SignedMeasure S) : BddAbove (gp_partSums fun A => ν A) := by
  obtain ⟨μ₁, μ₂, _, _, rfl⟩ := gp_exists_sub_measures ν
  refine gp_partSums_bddAbove_of_le (C := μ₁.real Set.univ + μ₂.real Set.univ) fun k A hA => ?_
  have e : ∑ i, |(μ₁.toSignedMeasure - μ₂.toSignedMeasure) (A i)| =
      ∑ i, |μ₁.real (A i) - μ₂.real (A i)| :=
    sum_congr rfl fun i _ => by rw [Measure.toSignedMeasure_sub_apply (hA.1 i)]
  exact e ▸ gp_partSums_le_of_measures μ₁ μ₂ hA

theorem gp_tvOf_nonneg {D : Set S → ℝ} (hD : BddAbove (gp_partSums D)) : 0 ≤ gp_tvOf D :=
  le_trans (sum_nonneg fun _ _ => abs_nonneg _) (le_csSup hD ⟨1, _, gp_isPartition_univ, rfl⟩)

theorem gp_abs_le_tvOf {D : Set S → ℝ} (hD : BddAbove (gp_partSums D)) {A : Set S}
    (hA : MeasurableSet A) : |D A| ≤ gp_tvOf D := by
  refine le_trans ?_ (le_csSup hD ⟨2, _, gp_isPartition_pair hA, rfl⟩)
  simp only [Fin.sum_univ_two, Fin.isValue, ↓reduceIte, one_ne_zero]
  linarith [abs_nonneg (D Aᶜ)]

/-- **Exercise 11.3.** Signed measures (differences of finite measures) form a vector space,
and the total variation `‖ν‖ = sup Σᵢ |ν(Aᵢ)|` is a norm on it. -/
theorem slp_ex_11_3 :
    (∀ ν : SignedMeasure S, ∃ (μ₁ μ₂ : Measure S) (_ : IsFiniteMeasure μ₁)
      (_ : IsFiniteMeasure μ₂), ν = μ₁.toSignedMeasure - μ₂.toSignedMeasure) ∧
    tvNorm (0 : SignedMeasure S) = 0 ∧ (∀ ν : SignedMeasure S, 0 ≤ tvNorm ν) ∧
    (∀ ν : SignedMeasure S, tvNorm ν = 0 → ν = 0) ∧
    (∀ (c : ℝ) (ν : SignedMeasure S), tvNorm (c • ν) = |c| * tvNorm ν) ∧
    ∀ ν ν' : SignedMeasure S, tvNorm (ν + ν') ≤ tvNorm ν + tvNorm ν' := by
  refine ⟨gp_exists_sub_measures, ?_, fun ν => gp_tvOf_nonneg (gp_bddAbove_tvNorm ν), fun ν h => ?_,
    fun c ν => ?_, fun ν ν' => ?_⟩
  · refine le_antisymm (csSup_le (gp_partSums_nonempty _) ?_) (gp_tvOf_nonneg (gp_bddAbove_tvNorm
      0))
    rintro _ ⟨k, A, -, rfl⟩
    simp
  · ext A hA
    have := gp_abs_le_tvOf (gp_bddAbove_tvNorm ν) hA
    change |ν A| ≤ tvNorm ν at this
    rw [h] at this
    simpa using abs_nonpos_iff.1 this
  · have hset : gp_partSums (fun A => (c • ν) A) = |c| • gp_partSums fun A => ν A := by
      ext x
      rw [Set.mem_smul_set]
      constructor
      · rintro ⟨k, A, hA, rfl⟩
        refine ⟨_, ⟨k, A, hA, rfl⟩, ?_⟩
        simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, abs_mul, mul_sum]
      · rintro ⟨_, ⟨k, A, hA, rfl⟩, rfl⟩
        refine ⟨k, A, hA, ?_⟩
        simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, abs_mul, mul_sum]
    unfold tvNorm gp_tvOf
    rw [hset, Real.sSup_smul_of_nonneg (abs_nonneg c), smul_eq_mul]
  · refine csSup_le (gp_partSums_nonempty _) ?_
    rintro _ ⟨k, A, hA, rfl⟩
    calc ∑ i, |(ν + ν') (A i)| ≤ ∑ i, |ν (A i)| + ∑ i, |ν' (A i)| := by
          rw [← sum_add_distrib]
          exact sum_le_sum fun i _ => by
            simp only [FunLike.coe_add, Pi.add_apply]; exact abs_add_le _ _
      _ ≤ tvNorm ν + tvNorm ν' := add_le_add (le_csSup (gp_bddAbove_tvNorm ν) ⟨k, A, hA, rfl⟩)
          (le_csSup (gp_bddAbove_tvNorm ν') ⟨k, A, hA, rfl⟩)

end Miao.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Characterizations of strong convergence

Copied from `RecursiveMethods/StrongConvergence` (SLP Chapter 11, module `TVConvergence.lean`),
with the
namespace renamed to `Miao.MarkovProcesses`, the results numbered in SLP prefixed
`slp_` and the helper lemmas and definitions prefixed `gp_`.

SLP §11.3, Theorems 11.6–11.7 and Lemma 11.8, pp. 340–344. Throughout, `λₙ` and `λ` are
probability measures.

* `gp_abs_integral_sub_le_tvDist`: `|∫ f dλ₁ − ∫ f dλ₂| ≤ ‖λ₁ − λ₂‖` for measurable `|f| ≤ 1`. With
  a
  Hahn set `B`, `λ₁ = λ₂ + α₁` on `B` and `λ₂ = λ₁ + α₂` on `Bᶜ`, and the difference of the
  integrals is `∫ f dα₁ − ∫ f dα₂`.
* **Theorem 11.6** (`slp_theorem_11_6`): `‖λₙ − λ‖ → 0` iff `λₙ(A) → λ(A)` uniformly in `A`.
* SLP's Theorem 11.7 (which needs SLP's strong convergence) is not copied.
* **Lemma 11.8** (`slp_lemma_11_8`): the probability measures are complete in the total variation
  norm. The book's proof that the limit `λ(A) = lim λₙ(A)` is countably additive exchanges a
  limit and a sum without justification. The exchange holds because the convergence is uniform
  in `A`: the tails `λ(⋃_{i ≥ K} Aᵢ)` are within `ε` of `λₙ(⋃_{i ≥ K} Aᵢ)`, which tend to `0`.
-/

namespace Miao.MarkovProcesses

open MeasureTheory Filter Topology Set

variable {S : Type*} [MeasurableSpace S]

theorem gp_abs_sub_le_add (μ₁ μ₂ : Measure S) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (A : Set S) : |μ₁.real A - μ₂.real A| ≤ μ₁.real univ + μ₂.real univ :=
  (abs_sub _ _).trans (by
    rw [abs_of_nonneg measureReal_nonneg, abs_of_nonneg measureReal_nonneg]
    exact add_le_add (measureReal_mono (subset_univ A)) (measureReal_mono (subset_univ A)))

theorem gp_bddAbove_supDiff (μ₁ μ₂ : Measure S) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] :
    BddAbove ((fun A => |μ₁.real A - μ₂.real A|) '' {A | MeasurableSet A}) :=
  ⟨_, by rintro _ ⟨A, -, rfl⟩; exact gp_abs_sub_le_add μ₁ μ₂ A⟩

/-- `2|λ₁(A) − λ₂(A)| ≤ ‖λ₁ − λ₂‖` for probability measures. -/
theorem gp_two_abs_le_tvDist (μ₁ μ₂ : Measure S) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] {A : Set S} (hA : MeasurableSet A) :
    2 * |μ₁.real A - μ₂.real A| ≤ tvDist μ₁ μ₂ := by
  rw [(slp_lemma_11_5 μ₁ μ₂ (by simp)).1]
  exact mul_le_mul_of_nonneg_left (le_csSup (gp_bddAbove_supDiff μ₁ μ₂) ⟨A, hA, rfl⟩)
    zero_le_two

/-- If `|λ₁(A) − λ₂(A)| ≤ δ` for all `A`, then `‖λ₁ − λ₂‖ ≤ 2δ`. -/
theorem gp_tvDist_le_of_forall (μ₁ μ₂ : Measure S) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] {δ : ℝ} (h : ∀ A, MeasurableSet A → |μ₁.real A - μ₂.real A| ≤ δ) :
    tvDist μ₁ μ₂ ≤ 2 * δ := by
  rw [(slp_lemma_11_5 μ₁ μ₂ (by simp)).1]
  refine mul_le_mul_of_nonneg_left (csSup_le ⟨_, ∅, MeasurableSet.empty, rfl⟩ ?_) zero_le_two
  rintro _ ⟨A, hA, rfl⟩
  exact h A hA

theorem gp_tvDist_nonneg (μ₁ μ₂ : Measure S) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] :
    0 ≤ tvDist μ₁ μ₂ :=
  gp_tvOf_nonneg (gp_bddAbove_tvDist μ₁ μ₂)

/-- For a nonnegative sequence, `uₙ → 0` iff eventually `uₙ < ε` for every `ε > 0`. -/
theorem gp_tendsto_zero_iff_of_nonneg {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n) :
    Tendsto u atTop (𝓝 0) ↔ ∀ ε > 0, ∀ᶠ n in atTop, u n < ε := by
  rw [tendsto_order]
  exact ⟨fun h => h.2, fun h => ⟨fun a ha => Eventually.of_forall fun n => ha.trans_le (hu n), h⟩⟩

/-- **Theorem 11.6.** `‖λₙ − λ‖ → 0` iff `λₙ(A) → λ(A)` uniformly in `A`. -/
theorem slp_theorem_11_6 (ls : ℕ → Measure S) (l : Measure S) [∀ n, IsProbabilityMeasure (ls n)]
    [IsProbabilityMeasure l] :
    Tendsto (fun n => tvDist (ls n) l) atTop (𝓝 0) ↔
      ∀ ε > 0, ∀ᶠ n in atTop, ∀ A, MeasurableSet A → |(ls n).real A - l.real A| < ε := by
  rw [gp_tendsto_zero_iff_of_nonneg fun n => gp_tvDist_nonneg (ls n) l]
  constructor
  · intro h ε hε
    filter_upwards [h (2 * ε) (by positivity)] with n hn A hA
    have := gp_two_abs_le_tvDist (ls n) l hA
    linarith
  · intro h ε hε
    filter_upwards [h (ε / 4) (by positivity)] with n hn
    have := gp_tvDist_le_of_forall (ls n) l fun A hA => (hn A hA).le
    linarith

theorem gp_integrable_of_abs_le (μ : Measure S) [IsFiniteMeasure μ] {f : S → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ s, |f s| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall fun s => by
    rw [Real.norm_eq_abs]; exact hC s)

/-- The partition `{B, Bᶜ}` bounds `|D(B)| + |D(Bᶜ)|` by the total variation. -/
theorem gp_abs_add_abs_compl_le (μ₁ μ₂ : Measure S) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    {B : Set S} (hB : MeasurableSet B) :
    |μ₁.real B - μ₂.real B| + |μ₁.real Bᶜ - μ₂.real Bᶜ| ≤ tvDist μ₁ μ₂ := by
  refine le_trans (le_of_eq ?_) (le_csSup (gp_bddAbove_tvDist μ₁ μ₂) ⟨2, _, gp_isPartition_pair hB,
      rfl⟩)
  simp [Fin.sum_univ_two]

/-- `|∫ f dλ₁ − ∫ f dλ₂| ≤ ‖λ₁ − λ₂‖` for measurable `f` with `|f| ≤ 1`. -/
theorem gp_abs_integral_sub_le_tvDist (μ₁ μ₂ : Measure S) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    {f : S → ℝ} (hf : Measurable f) (h1 : ∀ s, |f s| ≤ 1) :
    |∫ s, f s ∂μ₁ - ∫ s, f s ∂μ₂| ≤ tvDist μ₁ μ₂ := by
  obtain ⟨B, hB, hpos, hneg⟩ := hahn_decomposition μ₁ μ₂
  have hle1 : μ₂.restrict B ≤ μ₁.restrict B := Measure.le_iff.2 fun t ht => by
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact hpos _ (ht.inter hB) inter_subset_right
  have hle2 : μ₁.restrict Bᶜ ≤ μ₂.restrict Bᶜ := Measure.le_iff.2 fun t ht => by
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact hneg _ (ht.inter hB.compl) inter_subset_right
  set α₁ := μ₁.restrict B - μ₂.restrict B
  set α₂ := μ₂.restrict Bᶜ - μ₁.restrict Bᶜ
  have e1 : α₁ + μ₂.restrict B = μ₁.restrict B := Measure.sub_add_cancel_of_le hle1
  have e2 : α₂ + μ₁.restrict Bᶜ = μ₂.restrict Bᶜ := Measure.sub_add_cancel_of_le hle2
  have : IsFiniteMeasure α₁ := isFiniteMeasure_of_le _ (Measure.sub_le (μ := μ₁.restrict B))
  have : IsFiniteMeasure α₂ := isFiniteMeasure_of_le _ (Measure.sub_le (μ := μ₂.restrict Bᶜ))
  have hi : ∀ (μ : Measure S) [IsFiniteMeasure μ], Integrable f μ := fun μ _ =>
    gp_integrable_of_abs_le μ hf h1
  have hsplit1 : ∫ s, f s ∂μ₁ = ∫ s, f s ∂α₁ + ∫ s in B, f s ∂μ₂ + ∫ s in Bᶜ, f s ∂μ₁ := by
    rw [← integral_add_compl hB (hi μ₁), ← e1, integral_add_measure (hi α₁) (hi _)]
  have hsplit2 : ∫ s, f s ∂μ₂ = ∫ s in B, f s ∂μ₂ + (∫ s, f s ∂α₂ + ∫ s in Bᶜ, f s ∂μ₁) := by
    rw [← integral_add_compl hB (hi μ₂), ← e2, integral_add_measure (hi α₂) (hi _)]
  have hb : ∀ (α : Measure S) [IsFiniteMeasure α], |∫ s, f s ∂α| ≤ α.real univ := fun α _ => by
    have := norm_integral_le_of_norm_le_const (μ := α) (C := 1)
      (Eventually.of_forall fun s => by rw [Real.norm_eq_abs]; exact h1 s)
    rwa [Real.norm_eq_abs, one_mul] at this
  have hm1 : α₁.real univ = μ₁.real B - μ₂.real B := by
    have := congrArg (fun μ : Measure S => (μ univ).toReal) e1
    simp only [Measure.coe_add, Pi.add_apply, Measure.restrict_apply_univ] at this
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at this
    simp only [Measure.real]; linarith
  have hm2 : α₂.real univ = μ₂.real Bᶜ - μ₁.real Bᶜ := by
    have := congrArg (fun μ : Measure S => (μ univ).toReal) e2
    simp only [Measure.coe_add, Pi.add_apply, Measure.restrict_apply_univ] at this
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at this
    simp only [Measure.real]; linarith
  have hD1 : 0 ≤ μ₁.real B - μ₂.real B := by
    have := ENNReal.toReal_mono (measure_ne_top μ₁ B) (hpos B hB subset_rfl)
    simp only [Measure.real]; linarith
  have hD2 : μ₁.real Bᶜ - μ₂.real Bᶜ ≤ 0 := by
    have := ENNReal.toReal_mono (measure_ne_top μ₂ Bᶜ) (hneg Bᶜ hB.compl subset_rfl)
    simp only [Measure.real]; linarith
  have htv := gp_abs_add_abs_compl_le μ₁ μ₂ hB
  rw [abs_of_nonneg hD1, abs_of_nonpos hD2] at htv
  have hb1 := hb α₁
  have hb2 := hb α₂
  rw [hsplit1, hsplit2]
  calc |∫ s, f s ∂α₁ + ∫ s in B, f s ∂μ₂ + ∫ s in Bᶜ, f s ∂μ₁ -
        (∫ s in B, f s ∂μ₂ + (∫ s, f s ∂α₂ + ∫ s in Bᶜ, f s ∂μ₁))|
      = |∫ s, f s ∂α₁ - ∫ s, f s ∂α₂| := by ring_nf
    _ ≤ |∫ s, f s ∂α₁| + |∫ s, f s ∂α₂| := abs_sub _ _
    _ ≤ tvDist μ₁ μ₂ := by linarith

omit [MeasurableSpace S] in
/-- The tails `⋃_{i ≥ K} Aᵢ` of a disjoint sequence decrease to `∅`. -/
theorem gp_iInter_tails_eq_empty {f : ℕ → Set S} (hd : Pairwise (Function.onFun Disjoint f)) :
    (⋂ K, ⋃ i, ⋃ (_ : K ≤ i), f i) = ∅ := by
  ext x
  simp only [mem_iInter, mem_iUnion, mem_empty_iff_false, iff_false, not_forall, not_exists]
  by_cases hx : ∃ i, x ∈ f i
  · obtain ⟨i, hi⟩ := hx
    refine ⟨i + 1, fun j hj hxj => ?_⟩
    exact Set.disjoint_left.1 (hd (show i ≠ j by omega)) hi hxj
  · push Not at hx
    exact ⟨0, fun j _ hj => hx j hj⟩

/-- **Lemma 11.8.** The probability measures are complete in the total variation norm: a Cauchy
sequence `λₙ` converges to the probability measure `λ(A) = lim λₙ(A)`. -/
theorem slp_lemma_11_8 (ls : ℕ → Measure S) [∀ n, IsProbabilityMeasure (ls n)]
    (hC : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, tvDist (ls n) (ls m) < ε) :
    ∃ l : Measure S, IsProbabilityMeasure l ∧ Tendsto (fun n => tvDist (ls n) l) atTop (𝓝 0) := by
  -- (7): the measures of sets are uniformly Cauchy
  have hunif : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, ∀ A, MeasurableSet A →
      |(ls n).real A - (ls m).real A| < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hC (2 * ε) (by positivity)
    exact ⟨N, fun n hn m hm A hA => by
      have := gp_two_abs_le_tvDist (ls n) (ls m) hA; have := hN n hn m hm; linarith⟩
  have hcauchy : ∀ A, MeasurableSet A → CauchySeq fun n => (ls n).real A := fun A hA =>
    Metric.cauchySeq_iff.2 fun ε hε =>
      let ⟨N, hN⟩ := hunif ε hε
      ⟨N, fun m hm n hn => by rw [Real.dist_eq]; exact hN m hm n hn A hA⟩
  set F : Set S → ℝ := fun A => limUnder atTop fun n => (ls n).real A
  have hF : ∀ A, MeasurableSet A → Tendsto (fun n => (ls n).real A) atTop (𝓝 (F A)) :=
    fun A hA => (hcauchy A hA).tendsto_limUnder
  have hFu : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ A, MeasurableSet A → |(ls n).real A - F A| ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hunif ε hε
    refine ⟨N, fun n hn A hA => ?_⟩
    have hlim : Tendsto (fun m => |(ls n).real A - (ls m).real A|) atTop
        (𝓝 |(ls n).real A - F A|) := ((hF A hA).const_sub _).abs
    exact le_of_tendsto hlim (eventually_atTop.2 ⟨N, fun m hm => (hN n hn m hm A hA).le⟩)
  have hF0 : ∀ A, MeasurableSet A → 0 ≤ F A := fun A hA =>
    ge_of_tendsto (hF A hA) (Eventually.of_forall fun n => measureReal_nonneg)
  have hFe : F ∅ = 0 := tendsto_nhds_unique (hF ∅ MeasurableSet.empty) (by simp)
  have hFuniv : F univ = 1 := tendsto_nhds_unique (hF univ MeasurableSet.univ) (by simp)
  -- countable additivity
  have hsum : ∀ (f : ℕ → Set S), (∀ i, MeasurableSet (f i)) →
      Pairwise (Function.onFun Disjoint f) → HasSum (fun i => F (f i)) (F (⋃ i, f i)) := by
    intro f hf hd
    set T : ℕ → Set S := fun K => ⋃ i, ⋃ (_ : K ≤ i), f i
    have hT : ∀ K, MeasurableSet (T K) := fun K =>
      MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hf i
    -- for each `λₙ`: `λₙ(⋃ Aᵢ) = Σ_{i<K} λₙ(Aᵢ) + λₙ(T_K)`
    have hsplit : ∀ n K, (ls n).real (⋃ i, f i) =
        ∑ i ∈ Finset.range K, (ls n).real (f i) + (ls n).real (T K) := by
      intro n K
      have hU : (⋃ i, f i) = (⋃ i ∈ Finset.range K, f i) ∪ T K := by
        ext x
        simp only [mem_iUnion, mem_union, Finset.mem_range, T]
        constructor
        · rintro ⟨i, hi⟩
          by_cases hiK : i < K
          · exact Or.inl ⟨i, hiK, hi⟩
          · exact Or.inr ⟨i, by omega, hi⟩
        · rintro (⟨i, -, hi⟩ | ⟨i, -, hi⟩) <;> exact ⟨i, hi⟩
      have hdisj : Disjoint (⋃ i ∈ Finset.range K, f i) (T K) := by
        refine Set.disjoint_left.2 fun x hx hx' => ?_
        simp only [mem_iUnion, Finset.mem_range, T] at hx hx'
        obtain ⟨i, hi, hxi⟩ := hx
        obtain ⟨j, hj, hxj⟩ := hx'
        exact Set.disjoint_left.1 (hd (show i ≠ j by omega)) hxi hxj
      rw [hU, measureReal_union hdisj (hT K) (measure_ne_top _ _) (measure_ne_top _ _),
        measureReal_biUnion_finset (fun i _ j _ hij => hd hij) (fun i _ => hf i)
          (fun i _ => measure_ne_top _ _)]
    have hlimsplit : ∀ K, F (⋃ i, f i) = ∑ i ∈ Finset.range K, F (f i) + F (T K) := by
      intro K
      have h1 := hF _ (MeasurableSet.iUnion hf)
      have h2 : Tendsto (fun n => ∑ i ∈ Finset.range K, (ls n).real (f i) + (ls n).real (T K))
          atTop (𝓝 (∑ i ∈ Finset.range K, F (f i) + F (T K))) :=
        (tendsto_finsetSum _ fun i _ => hF _ (hf i)).add (hF _ (hT K))
      exact tendsto_nhds_unique (h1.congr fun n => hsplit n K) h2
    -- the tails tend to zero, uniformly
    have htail : Tendsto (fun K => F (T K)) atTop (𝓝 0) := by
      rw [gp_tendsto_zero_iff_of_nonneg fun K => hF0 _ (hT K)]
      intro ε hε
      obtain ⟨N, hN⟩ := hFu (ε / 2) (by positivity)
      have hanti : Antitone T := fun K K' hKK' => iUnion_mono fun i =>
        iUnion_subset fun hi => subset_iUnion (fun _ : K ≤ i => f i) (hKK'.trans hi)
      have hlim := tendsto_measure_iInter_atTop (μ := ls N) (fun K => (hT K).nullMeasurableSet)
        hanti ⟨0, measure_ne_top _ _⟩
      rw [gp_iInter_tails_eq_empty hd, measure_empty] at hlim
      have hlim' : Tendsto (fun K => (ls N).real (T K)) atTop (𝓝 0) := by
        have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
        simpa [Function.comp_def, Measure.real] using this
      filter_upwards [hlim'.eventually (gt_mem_nhds (half_pos hε))] with K hK
      have := hN N le_rfl (T K) (hT K)
      rw [abs_le] at this
      linarith
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun i => hF0 _ (hf i))]
    have := htail.const_sub (F (⋃ i, f i))
    rw [sub_zero] at this
    exact this.congr fun K => by rw [hlimsplit K]; ring
  -- the limit measure
  set l : Measure S := Measure.ofMeasurable (fun A _ => ENNReal.ofReal (F A)) (by simp [hFe])
    (fun f hf hd => by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => hF0 _ (hf i)) (hsum f hf hd).summable,
        (hsum f hf hd).tsum_eq])
  have hl : ∀ A, MeasurableSet A → l.real A = F A := fun A hA => by
    rw [measureReal_def, Measure.ofMeasurable_apply A hA, ENNReal.toReal_ofReal (hF0 A hA)]
  have hlp : IsProbabilityMeasure l :=
    ⟨by rw [Measure.ofMeasurable_apply _ MeasurableSet.univ, hFuniv, ENNReal.ofReal_one]⟩
  refine ⟨l, hlp, (gp_tendsto_zero_iff_of_nonneg fun n => gp_tvDist_nonneg (ls n) l).2 fun ε hε =>
      ?_⟩
  obtain ⟨N, hN⟩ := hFu (ε / 4) (by positivity)
  refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
  have := gp_tvDist_le_of_forall (ls n) l fun A hA => by rw [hl A hA]; exact hN n hn A hA
  linarith

end Miao.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Condition M and geometric convergence

Copied from `RecursiveMethods/StrongConvergence` (SLP Chapter 11, module `ConditionM.lean`), with
the
namespace renamed to `Miao.MarkovProcesses`, the results numbered in SLP prefixed
`slp_` and the helper lemmas and definitions prefixed `gp_`.

SLP §11.4, Lemma 11.11 and Theorem 11.12, pp. 349–351. `T*ⁿλ = adjointOp (kpow κ n) λ`.

* `gp_tvDist_comm`, `gp_tvDist_triangle`, `gp_eq_of_tvDist_eq_zero`: the total variation distance
  is a
  metric on probability measures.
* **Lemma 11.11** (`slp_lemma_11_11`): under Condition M for `(N, ε)`, `T*ᴺ` is a contraction of
  modulus `1 − ε` in the total variation norm. With a Hahn set `B`, write `λᵢ = αᵢ + γ`, with
  `α₁ = λ₁|_B − λ₂|_B` and `α₂ = λ₂|_{Bᶜ} − λ₁|_{Bᶜ}` of equal mass `c`, so
  `‖λ₁ − λ₂‖ ≥ 2c`. Then `(T*ᴺλ₁)(A) − (T*ᴺλ₂)(A) = ∫ Pᴺ(·, A) dα₁ − ∫ Pᴺ(·, A) dα₂`. If
  `Pᴺ(·, A) ≥ ε`, both integrals lie in `[εc, c]`; otherwise the same holds for `Aᶜ`. The book
  applies Lemma 11.5 to `T*ᴺαᵢ`, which are not probability measures; this proof avoids that.
* **Theorem 11.12** (`slp_theorem_11_12`): under Condition M there is a unique `λ*` with
  `‖T*^{Nk}λ₀ − λ*‖ ≤ (1 − ε)ᵏ‖λ₀ − λ*‖` for all `λ₀`. It is the unique invariant probability
  measure, and `‖T*ⁿλ₀ − λ*‖ ≤ 2(1 − ε)^⌊n/N⌋`. These two facts the book leaves implicit.
  Conversely (`slp_theorem_11_12_converse`), this bound implies Condition M for `(NK, 1/4)`.
  The fixed point is found by the contraction argument, using Lemma 11.8 for completeness.
-/

namespace Miao.MarkovProcesses

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {S : Type*} [MeasurableSpace S]

/-- **Condition M** for `(N, ε)` (SLP p. 348; Miao, Condition M, p. 105): `N ≥ 1`, `ε > 0`, and
for each measurable `A`, either `Pᴺ(s, A) ≥ ε` for all `s`, or `Pᴺ(s, Aᶜ) ≥ ε` for all `s`.
Copied from `RecursiveMethods/StrongConvergence` (module `Doeblin.lean`). -/
def ConditionMFor (κ : Kernel S S) (N : ℕ) (ε : ℝ) : Prop :=
  1 ≤ N ∧ 0 < ε ∧ ∀ A, MeasurableSet A →
    (∀ s, ε ≤ (kpow κ N s).real A) ∨ ∀ s, ε ≤ (kpow κ N s).real Aᶜ

/-- `P` satisfies **Condition M** for some `(N, ε)`. -/
def ConditionM (κ : Kernel S S) : Prop := ∃ N ε, ConditionMFor κ N ε

theorem gp_isMarkov_kpow {κ : Kernel S S} [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (kpow κ n) := slp_ex_8_4a κ n

theorem gp_tvDist_comm (μ₁ μ₂ : Measure S) : tvDist μ₁ μ₂ = tvDist μ₂ μ₁ := by
  unfold tvDist gp_tvOf gp_partSums
  congr 1
  ext x
  refine exists_congr fun k => exists_congr fun A => and_congr_right fun _ => ?_
  simp only [abs_sub_comm]

theorem gp_tvDist_triangle (μ₁ μ₂ μ₃ : Measure S) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    [IsFiniteMeasure μ₃] : tvDist μ₁ μ₃ ≤ tvDist μ₁ μ₂ + tvDist μ₂ μ₃ := by
  refine csSup_le (gp_partSums_nonempty _) ?_
  rintro _ ⟨k, A, hA, rfl⟩
  calc ∑ i, |μ₁.real (A i) - μ₃.real (A i)|
      ≤ ∑ i, |μ₁.real (A i) - μ₂.real (A i)| + ∑ i, |μ₂.real (A i) - μ₃.real (A i)| := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun i _ => abs_sub_le _ _ _
    _ ≤ tvDist μ₁ μ₂ + tvDist μ₂ μ₃ :=
        add_le_add (le_csSup (gp_bddAbove_tvDist μ₁ μ₂) ⟨k, A, hA, rfl⟩)
          (le_csSup (gp_bddAbove_tvDist μ₂ μ₃) ⟨k, A, hA, rfl⟩)

theorem gp_tvDist_le_two (μ₁ μ₂ : Measure S) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] :
    tvDist μ₁ μ₂ ≤ 2 := by
  refine csSup_le (gp_partSums_nonempty _) ?_
  rintro _ ⟨k, A, hA, rfl⟩
  have := gp_partSums_le_of_measures μ₁ μ₂ hA
  simp only [probReal_univ] at this
  linarith

theorem gp_eq_of_tvDist_eq_zero {μ₁ μ₂ : Measure S} [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (h : tvDist μ₁ μ₂ ≤ 0) : μ₁ = μ₂ := by
  ext A hA
  have := gp_two_abs_le_tvDist μ₁ μ₂ hA
  have h0 : μ₁.real A = μ₂.real A := by
    have := abs_nonneg (μ₁.real A - μ₂.real A)
    have : |μ₁.real A - μ₂.real A| = 0 := by linarith
    linarith [abs_eq_zero.1 this]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h0

/-- `(λ ⊗ P)(A) = ∫ P(s, A) λ(ds)` in real terms, for finite `λ`. -/
theorem gp_bind_real_eq (κ : Kernel S S) [IsMarkovKernel κ] (μ : Measure S) [IsFiniteMeasure μ]
    {A : Set S} (hA : MeasurableSet A) :
    (adjointOp κ μ).real A = ∫ s, (κ s).real A ∂μ := by
  rw [measureReal_def, gp_adjointOp_apply κ μ hA]
  exact (integral_toReal (κ.measurable_coe hA).aemeasurable
    (Eventually.of_forall fun s => measure_lt_top _ _)).symm

/-- **Lemma 11.11.** Under Condition M for `(N, ε)`, `T*ᴺ` is a contraction of modulus `1 − ε`:
`‖T*ᴺλ₁ − T*ᴺλ₂‖ ≤ (1 − ε)‖λ₁ − λ₂‖`. -/
theorem slp_lemma_11_11 {κ : Kernel S S} [IsMarkovKernel κ] {N : ℕ} {ε : ℝ}
    (hM : ConditionMFor κ N ε) (μ₁ μ₂ : Measure S) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] :
    tvDist (adjointOp (kpow κ N) μ₁) (adjointOp (kpow κ N) μ₂) ≤ (1 - ε) * tvDist μ₁ μ₂ := by
  obtain ⟨-, hε, hMA⟩ := hM
  set P := kpow κ N
  have hP : IsMarkovKernel P := gp_isMarkov_kpow N
  have : IsProbabilityMeasure (adjointOp P μ₁) := (slp_theorem_8_2 P μ₁).1
  have : IsProbabilityMeasure (adjointOp P μ₂) := (slp_theorem_8_2 P μ₂).1
  have hε1 : ε ≤ 1 := by
    obtain ⟨s⟩ := nonempty_of_isProbabilityMeasure μ₁
    rcases hMA ∅ MeasurableSet.empty with h | h
    · have := h s; simp at this; linarith
    · have := h s; simp at this; linarith
  -- the Hahn decomposition: `λᵢ = αᵢ + γ`
  obtain ⟨B, hB, hpos, hneg⟩ := hahn_decomposition μ₁ μ₂
  have hle1 : μ₂.restrict B ≤ μ₁.restrict B := Measure.le_iff.2 fun t ht => by
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact hpos _ (ht.inter hB) inter_subset_right
  have hle2 : μ₁.restrict Bᶜ ≤ μ₂.restrict Bᶜ := Measure.le_iff.2 fun t ht => by
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact hneg _ (ht.inter hB.compl) inter_subset_right
  set α₁ := μ₁.restrict B - μ₂.restrict B
  set α₂ := μ₂.restrict Bᶜ - μ₁.restrict Bᶜ
  set γ := μ₂.restrict B + μ₁.restrict Bᶜ
  have e1 : α₁ + μ₂.restrict B = μ₁.restrict B := Measure.sub_add_cancel_of_le hle1
  have e2 : α₂ + μ₁.restrict Bᶜ = μ₂.restrict Bᶜ := Measure.sub_add_cancel_of_le hle2
  have : IsFiniteMeasure α₁ := isFiniteMeasure_of_le _ (Measure.sub_le (μ := μ₁.restrict B))
  have : IsFiniteMeasure α₂ := isFiniteMeasure_of_le _ (Measure.sub_le (μ := μ₂.restrict Bᶜ))
  have hl1 : μ₁ = α₁ + γ := by
    conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := μ₁) hB, ← e1]
    simp only [γ, add_assoc]
  have hl2 : μ₂ = α₂ + γ := by
    conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := μ₂) hB, ← e2]
    simp only [γ]; abel
  set c₁ := α₁.real univ
  set c₂ := α₂.real univ
  have hc : c₁ = c₂ := by
    have h1 : μ₁.real univ = c₁ + γ.real univ := by rw [hl1, measureReal_add_apply]
    have h2 : μ₂.real univ = c₂ + γ.real univ := by rw [hl2, measureReal_add_apply]
    simp only [probReal_univ] at h1 h2
    linarith
  have hm1 : c₁ = μ₁.real B - μ₂.real B := by
    have := congrArg (fun μ : Measure S => (μ univ).toReal) e1
    simp only [Measure.coe_add, Pi.add_apply, Measure.restrict_apply_univ] at this
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at this
    simp only [c₁, Measure.real]; linarith
  have hm2 : c₂ = μ₂.real Bᶜ - μ₁.real Bᶜ := by
    have := congrArg (fun μ : Measure S => (μ univ).toReal) e2
    simp only [Measure.coe_add, Pi.add_apply, Measure.restrict_apply_univ] at this
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at this
    simp only [c₂, Measure.real]; linarith
  have hc0 : 0 ≤ c₁ := measureReal_nonneg
  have htv : 2 * c₁ ≤ tvDist μ₁ μ₂ := by
    have := gp_abs_add_abs_compl_le μ₁ μ₂ hB
    rw [← hm1, show μ₁.real Bᶜ - μ₂.real Bᶜ = -c₂ by rw [hm2]; ring, abs_neg, ← hc,
      abs_of_nonneg hc0] at this
    linarith
  -- integrals of `Pᴺ(·, A)`
  have hint : ∀ (α : Measure S) [IsFiniteMeasure α] (A : Set S), MeasurableSet A →
      Integrable (fun s => (P s).real A) α := fun α _ A hA =>
    gp_integrable_of_abs_le α (P.measurable_coe hA).ennreal_toReal
      fun s => by rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one
  have hsplit : ∀ (μ α : Measure S) [IsFiniteMeasure μ] [IsFiniteMeasure α], μ = α + γ →
      ∀ A, MeasurableSet A → (adjointOp P μ).real A =
        ∫ s, (P s).real A ∂α + ∫ s, (P s).real A ∂γ := by
    intro μ α _ _ hμ A hA
    rw [gp_bind_real_eq P μ hA, hμ, integral_add_measure (hint α A hA) (hint γ A hA)]
  have hbound : ∀ (α : Measure S) [IsFiniteMeasure α] (A : Set S), MeasurableSet A →
      (∀ s, ε ≤ (P s).real A) →
        ε * α.real univ ≤ ∫ s, (P s).real A ∂α ∧ ∫ s, (P s).real A ∂α ≤ α.real univ := by
    intro α _ A hA hεA
    constructor
    · have := integral_mono (integrable_const ε) (hint α A hA) hεA
      rwa [integral_const, smul_eq_mul, mul_comm] at this
    · have := integral_mono (hint α A hA) (integrable_const 1) fun s => measureReal_le_one
      rwa [integral_const, smul_eq_mul, mul_one] at this
  have hcompl : ∀ (α : Measure S) [IsFiniteMeasure α] (A : Set S), MeasurableSet A →
      ∫ s, (P s).real A ∂α + ∫ s, (P s).real Aᶜ ∂α = α.real univ := by
    intro α _ A hA
    rw [← integral_add (hint α A hA) (hint α Aᶜ hA.compl)]
    simp_rw [measureReal_add_measureReal_compl hA, probReal_univ]
    rw [integral_const, smul_eq_mul, mul_one]
  have hA : ∀ A, MeasurableSet A →
      |(adjointOp P μ₁).real A - (adjointOp P μ₂).real A| ≤ (1 - ε) * c₁ := by
    intro A hA
    rw [hsplit μ₁ α₁ hl1 A hA, hsplit μ₂ α₂ hl2 A hA]
    rcases hMA A hA with h | h
    · obtain ⟨a1, a2⟩ := hbound α₁ A hA h
      obtain ⟨b1, b2⟩ := hbound α₂ A hA h
      have hc2 : α₂.real univ = c₁ := hc.symm
      have hc1 : α₁.real univ = c₁ := rfl
      rw [abs_le]; constructor <;> nlinarith
    · obtain ⟨a1, a2⟩ := hbound α₁ Aᶜ hA.compl h
      obtain ⟨b1, b2⟩ := hbound α₂ Aᶜ hA.compl h
      have f1 := hcompl α₁ A hA
      have f2 := hcompl α₂ A hA
      have hc2 : α₂.real univ = c₁ := hc.symm
      have hc1 : α₁.real univ = c₁ := rfl
      rw [abs_le]; constructor <;> nlinarith
  have := gp_tvDist_le_of_forall _ _ hA
  nlinarith

variable {κ : Kernel S S} [IsMarkovKernel κ]

theorem gp_isProb_adjoint (n : ℕ) (μ : Measure S) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (adjointOp (kpow κ n) μ) := by
  have := gp_isMarkov_kpow (κ := κ) n
  exact (slp_theorem_8_2 (kpow κ n) μ).1

omit [IsMarkovKernel κ] in
theorem gp_adjoint_add (n m : ℕ) (μ : Measure S) :
    adjointOp (kpow κ (n + m)) μ = adjointOp (kpow κ n) (adjointOp (kpow κ m) μ) :=
  (slp_ex_8_4b κ n m measurable_const μ (f := fun _ => 0)).2

/-- Iterating Lemma 11.11: `‖T*^{Nk}λ₁ − T*^{Nk}λ₂‖ ≤ (1 − ε)ᵏ‖λ₁ − λ₂‖`. -/
theorem gp_tvDist_iterate_le {N : ℕ} {ε : ℝ} (hM : ConditionMFor κ N ε) (μ₁ μ₂ : Measure S)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] (k : ℕ) :
    tvDist (adjointOp (kpow κ (N * k)) μ₁) (adjointOp (kpow κ (N * k)) μ₂) ≤
      (1 - ε) ^ k * tvDist μ₁ μ₂ := by
  have hε1 : ε ≤ 1 := by
    obtain ⟨s⟩ := nonempty_of_isProbabilityMeasure μ₁
    have := gp_isMarkov_kpow (κ := κ) N
    rcases hM.2.2 ∅ MeasurableSet.empty with h | h
    · have := h s; simp at this; linarith [hM.2.1]
    · have := h s; simp at this; linarith
  induction k with
  | zero => simp [kpow, adjointOp]
  | succ k ih =>
    have := gp_isProb_adjoint (κ := κ) (N * k) μ₁
    have := gp_isProb_adjoint (κ := κ) (N * k) μ₂
    rw [show N * (k + 1) = N + N * k by ring, gp_adjoint_add, gp_adjoint_add, pow_succ']
    calc _ ≤ (1 - ε) * tvDist (adjointOp (kpow κ (N * k)) μ₁) (adjointOp (kpow κ (N * k)) μ₂) :=
          slp_lemma_11_11 hM _ _
      _ ≤ (1 - ε) * ((1 - ε) ^ k * tvDist μ₁ μ₂) :=
          mul_le_mul_of_nonneg_left ih (by linarith)
      _ = _ := by ring

/-- **Theorem 11.12.** Under Condition M for `(N, ε)` there is a unique probability measure
`λ*` such that `‖T*^{Nk}λ₀ − λ*‖ ≤ (1 − ε)ᵏ‖λ₀ − λ*‖` for all `λ₀` and `k`; moreover `λ*` is
invariant, `T*λ* = λ*`, and `‖T*ⁿλ₀ − λ*‖ ≤ 2(1 − ε)^⌊n/N⌋` for all `n`. -/
theorem slp_theorem_11_12 [Nonempty S] {N : ℕ} {ε : ℝ} (hM : ConditionMFor κ N ε) :
    ∃ lstar : Measure S, IsProbabilityMeasure lstar ∧
      (∀ (l₀ : Measure S) [IsProbabilityMeasure l₀] (k : ℕ),
        tvDist (adjointOp (kpow κ (N * k)) l₀) lstar ≤ (1 - ε) ^ k * tvDist l₀ lstar) ∧
      (∀ l' : Measure S, IsProbabilityMeasure l' →
        (∀ (l₀ : Measure S) [IsProbabilityMeasure l₀] (k : ℕ),
          tvDist (adjointOp (kpow κ (N * k)) l₀) l' ≤ (1 - ε) ^ k * tvDist l₀ l') → l' = lstar) ∧
      adjointOp κ lstar = lstar ∧
      ∀ (l₀ : Measure S) [IsProbabilityMeasure l₀] (n : ℕ),
        tvDist (adjointOp (kpow κ n) l₀) lstar ≤ 2 * (1 - ε) ^ (n / N) := by
  obtain ⟨hN, hε, hMA⟩ := hM
  obtain ⟨s₀⟩ := ‹Nonempty S›
  have hε1 : ε ≤ 1 := by
    have := gp_isMarkov_kpow (κ := κ) N
    rcases hMA ∅ MeasurableSet.empty with h | h
    · have := h s₀; simp at this; linarith
    · have := h s₀; simp at this; linarith
  have hr0 : 0 ≤ 1 - ε := by linarith
  have hr1 : 1 - ε < 1 := by linarith
  set T : ℕ → Measure S → Measure S := fun n μ => adjointOp (kpow κ n) μ
  have hTp : ∀ n (μ : Measure S) [IsProbabilityMeasure μ], IsProbabilityMeasure (T n μ) :=
    fun n μ _ => gp_isProb_adjoint n μ
  -- the iterates from `δ_{s₀}`
  set seq : ℕ → Measure S := fun k => T (N * k) (Measure.dirac s₀)
  have hseqp : ∀ k, IsProbabilityMeasure (seq k) := fun k => hTp _ _
  have hstep : ∀ k, tvDist (seq (k + 1)) (seq k) ≤ 2 * (1 - ε) ^ k := by
    intro k
    have h1 : seq (k + 1) = T (N * k) (T N (Measure.dirac s₀)) := by
      simp only [seq, T]; rw [← gp_adjoint_add]; ring_nf
    have : IsProbabilityMeasure (T N (Measure.dirac s₀)) := hTp _ _
    rw [h1]
    calc _ ≤ (1 - ε) ^ k * tvDist (T N (Measure.dirac s₀)) (Measure.dirac s₀) :=
          gp_tvDist_iterate_le ⟨hN, hε, hMA⟩ _ _ k
      _ ≤ (1 - ε) ^ k * 2 := mul_le_mul_of_nonneg_left (gp_tvDist_le_two _ _) (pow_nonneg hr0 k)
      _ = _ := mul_comm _ _
  have hgeom : ∀ m d, tvDist (seq (m + d)) (seq m) ≤ 2 * (1 - ε) ^ m / ε := by
    intro m d
    have hsum : tvDist (seq (m + d)) (seq m) ≤
        2 * ∑ j ∈ Finset.range d, (1 - ε) ^ (m + j) := by
      induction d with
      | zero =>
        simp only [add_zero, Finset.range_zero, Finset.sum_empty, mul_zero]
        exact le_of_eq (by
          refine le_antisymm (csSup_le (gp_partSums_nonempty _) ?_) (gp_tvOf_nonneg
            (gp_bddAbove_tvDist _ _))
          rintro _ ⟨k, A, -, rfl⟩; simp)
      | succ d ih =>
        calc tvDist (seq (m + (d + 1))) (seq m)
            ≤ tvDist (seq (m + d + 1)) (seq (m + d)) + tvDist (seq (m + d)) (seq m) :=
              gp_tvDist_triangle _ _ _
          _ ≤ 2 * (1 - ε) ^ (m + d) + 2 * ∑ j ∈ Finset.range d, (1 - ε) ^ (m + j) :=
              add_le_add (hstep _) ih
          _ = 2 * ∑ j ∈ Finset.range (d + 1), (1 - ε) ^ (m + j) := by
              rw [Finset.sum_range_succ]; ring
    refine hsum.trans ?_
    have hgs : ∑ j ∈ Finset.range d, (1 - ε) ^ (m + j) =
        (1 - ε) ^ m * ((1 - (1 - ε) ^ d) / ε) := by
      have hε0 : ε ≠ 0 := hε.ne'
      rw [show (1 - (1 - ε) ^ d) / ε = ∑ j ∈ Finset.range d, (1 - ε) ^ j by
        rw [geom_sum_eq (by linarith), show 1 - ε - 1 = -ε by ring, div_neg, ← neg_div,
          neg_sub], Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [pow_add]
    rw [hgs]
    have : (1 - (1 - ε) ^ d) / ε ≤ 1 / ε :=
      div_le_div_of_nonneg_right (by linarith [pow_nonneg hr0 d]) hε.le
    calc 2 * ((1 - ε) ^ m * ((1 - (1 - ε) ^ d) / ε)) ≤ 2 * ((1 - ε) ^ m * (1 / ε)) := by
          gcongr
      _ = 2 * (1 - ε) ^ m / ε := by ring
  -- Cauchy, hence convergent (Lemma 11.8)
  have hcauchy : ∀ δ > 0, ∃ K, ∀ n ≥ K, ∀ m ≥ K, tvDist (seq n) (seq m) < δ := by
    intro δ hδ
    have hlim : Tendsto (fun K => 2 * (1 - ε) ^ K / ε) atTop (𝓝 (2 * 0 / ε)) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul 2).div_const ε
    rw [mul_zero, zero_div] at hlim
    obtain ⟨K, hK⟩ := (hlim.eventually (gt_mem_nhds hδ)).exists_forall_of_atTop
    refine ⟨K, fun n hn m hm => ?_⟩
    have hmono : ∀ j ≥ K, 2 * (1 - ε) ^ j / ε ≤ 2 * (1 - ε) ^ K / ε := fun j hj =>
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hr0 hr1.le hj) zero_le_two) hε.le
    rcases le_total m n with hmn | hnm
    · have := hgeom m (n - m)
      rw [Nat.add_sub_cancel' hmn] at this
      exact this.trans_lt ((hmono m hm).trans_lt (hK K le_rfl))
    · have := hgeom n (m - n)
      rw [Nat.add_sub_cancel' hnm, gp_tvDist_comm] at this
      exact this.trans_lt ((hmono n hn).trans_lt (hK K le_rfl))
  obtain ⟨lstar, hlp, hconv⟩ := slp_lemma_11_8 seq hcauchy
  -- `λ*` is a fixed point of `T*ᴺ`
  have hfix : T N lstar = lstar := by
    have : IsProbabilityMeasure (T N lstar) := hTp _ _
    have hlimf : Tendsto (fun k => (1 - ε) * tvDist (seq k) lstar + tvDist (seq (k + 1)) lstar)
        atTop (𝓝 0) := by
      have h1 := (hconv.const_mul (1 - ε)).add (hconv.comp (tendsto_add_atTop_nat 1))
      simpa using h1
    refine gp_eq_of_tvDist_eq_zero (ge_of_tendsto' hlimf fun k => ?_)
    · have e : seq (k + 1) = T N (seq k) := by
        simp only [seq, T]; rw [← gp_adjoint_add]; ring_nf
      calc tvDist (T N lstar) lstar
            ≤ tvDist (T N lstar) (seq (k + 1)) + tvDist (seq (k + 1)) lstar :=
            gp_tvDist_triangle _ _ _
        _ ≤ (1 - ε) * tvDist (seq k) lstar + tvDist (seq (k + 1)) lstar := by
            gcongr
            rw [e, gp_tvDist_comm]
            exact slp_lemma_11_11 ⟨hN, hε, hMA⟩ _ _
  have hfixk : ∀ k, T (N * k) lstar = lstar := by
    intro k
    induction k with
    | zero => simp [T, kpow, adjointOp]
    | succ k ih =>
      simp only [T] at ih ⊢
      rw [show N * (k + 1) = N * k + N by ring, gp_adjoint_add,
        show adjointOp (kpow κ N) lstar = lstar from hfix, ih]
  have h1 : ∀ (l₀ : Measure S) [IsProbabilityMeasure l₀] (k : ℕ),
      tvDist (T (N * k) l₀) lstar ≤ (1 - ε) ^ k * tvDist l₀ lstar := by
    intro l₀ _ k
    have := gp_tvDist_iterate_le ⟨hN, hε, hMA⟩ l₀ lstar k
    rwa [show adjointOp (kpow κ (N * k)) lstar = lstar from hfixk k] at this
  refine ⟨lstar, hlp, h1, fun l' hl' hl'1 => ?_, ?_, fun l₀ _ n => ?_⟩
  · -- uniqueness
    refine (gp_eq_of_tvDist_eq_zero ?_).symm
    have hlim : Tendsto (fun k => (1 - ε) ^ k * 2) atTop (𝓝 (0 * 2)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const 2
    rw [zero_mul] at hlim
    refine ge_of_tendsto' hlim fun k => ?_
    have := hl'1 lstar k
    rw [show adjointOp (kpow κ (N * k)) lstar = lstar from hfixk k] at this
    exact this.trans (mul_le_mul_of_nonneg_left (gp_tvDist_le_two _ _) (pow_nonneg hr0 k))
  · -- invariance: `T*λ*` is also a fixed point of the contraction `T*ᴺ`
    have : IsProbabilityMeasure (adjointOp κ lstar) := by
      have := hTp 1 lstar; simpa [T, gp_kpow_one] using this
    have hcomm : T N (adjointOp κ lstar) = adjointOp κ lstar := by
      have e1 : adjointOp κ lstar = T 1 lstar := by simp [T, gp_kpow_one]
      rw [e1]
      simp only [T]
      rw [← gp_adjoint_add, show N + 1 = 1 + N by ring, gp_adjoint_add]
      exact congrArg _ hfix
    have hc := slp_lemma_11_11 ⟨hN, hε, hMA⟩ (adjointOp κ lstar) lstar
    rw [show adjointOp (kpow κ N) (adjointOp κ lstar) = adjointOp κ lstar from hcomm,
      show adjointOp (kpow κ N) lstar = lstar from hfix] at hc
    refine gp_eq_of_tvDist_eq_zero ?_
    nlinarith [gp_tvDist_nonneg (adjointOp κ lstar) lstar]
  · -- the rate for every `n`
    have hsplit : T n l₀ = T (N * (n / N)) (T (n % N) l₀) := by
      simp only [T]; rw [← gp_adjoint_add, Nat.div_add_mod]
    have : IsProbabilityMeasure (T (n % N) l₀) := hTp _ _
    change tvDist (T n l₀) lstar ≤ _
    rw [hsplit]
    calc _ ≤ (1 - ε) ^ (n / N) * tvDist (T (n % N) l₀) lstar := h1 _ _
      _ ≤ (1 - ε) ^ (n / N) * 2 :=
          mul_le_mul_of_nonneg_left (gp_tvDist_le_two _ _) (pow_nonneg hr0 _)
      _ = _ := mul_comm _ _

/-- **Theorem 11.12** (converse). If `‖T*^{Nk}λ₀ − λ*‖ ≤ (1 − ε)ᵏ‖λ₀ − λ*‖` for all `λ₀` and `k`,
with `N ≥ 1` and `0 < ε ≤ 1`, then Condition M holds for `(NK, 1/4)`, where `(1 − ε)ᴷ ≤ 1/4`. -/
theorem slp_theorem_11_12_converse {N : ℕ} {ε : ℝ} (hN : 1 ≤ N)
    (hε : 0 < ε) (hε1 : ε ≤ 1) {lstar : Measure S} [IsProbabilityMeasure lstar]
    (h : ∀ (l₀ : Measure S) [IsProbabilityMeasure l₀] (k : ℕ),
      tvDist (adjointOp (kpow κ (N * k)) l₀) lstar ≤ (1 - ε) ^ k * tvDist l₀ lstar) :
    ConditionM κ := by
  have hlim : Tendsto (fun K => (1 - ε) ^ K) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  obtain ⟨K₀, hK₀⟩ := (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num)))
    |>.exists_forall_of_atTop
  set K := K₀ + 1
  have hK : (1 - ε) ^ K ≤ 1 / 4 := (hK₀ K (by omega)).le
  have hNK : 1 ≤ N * K := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have := gp_isMarkov_kpow (κ := κ) (N * K)
  -- `|Pᴺᴷ(s, A) − λ*(A)| ≤ 1/4`
  have hclose : ∀ s A, MeasurableSet A → |(kpow κ (N * K) s).real A - lstar.real A| ≤ 1 / 4 := by
    intro s A hA
    have e : adjointOp (kpow κ (N * K)) (Measure.dirac s) = kpow κ (N * K) s :=
      Measure.dirac_bind (Kernel.measurable _) s
    have h1 := h (Measure.dirac s) K
    rw [e] at h1
    have h2 := gp_two_abs_le_tvDist (kpow κ (N * K) s) lstar hA
    have h3 := gp_tvDist_le_two (Measure.dirac s) lstar
    have h4 : (1 - ε) ^ K * tvDist (Measure.dirac s) lstar ≤ 1 / 4 * 2 :=
      mul_le_mul hK h3 (gp_tvDist_nonneg _ _) (by norm_num)
    linarith
  refine ⟨N * K, 1 / 4, hNK, by norm_num, fun A hA => ?_⟩
  rcases le_total (1 / 2) (lstar.real A) with hA2 | hA2
  · exact Or.inl fun s => by have := abs_le.1 (hclose s A hA); linarith
  · refine Or.inr fun s => ?_
    have hc : lstar.real Aᶜ = 1 - lstar.real A := probReal_compl_eq_one_sub hA
    have := abs_le.1 (hclose s Aᶜ hA.compl)
    linarith

end Miao.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Strong convergence: total variation, Condition M and the Minorization Condition

Miao, §3.3.1, pp. 104–108.

* (3.6): `dTV λ₁ λ₂ = sup_A |λ₁(A) − λ₂(A)|` (`dTV`). SLP's total variation norm `tvDist` is
  twice it (`gp_tvDist_eq_two_mul_dTV`). p. 105: `dTV` is a metric on probability measures and
  the space is complete (`eq_p105_metric`, `eq_p105_complete`, from SLP Lemma 11.8).
* **Definition 3.3.1** (`ConvStrongly`).
* **Condition M** is SLP's `ConditionMFor κ N ε` (copied in `ConvergenceSLPConditionM`).
* **Theorem 3.3.1** (`theorem_3_3_1`, `theorem_3_3_1_contraction`, `theorem_3_3_1_invariant`,
  `theorem_3_3_1_converse`), from SLP Theorem 11.12. Departure: `X` is assumed nonempty (there
  is no probability measure on `∅`). The limit `π` is also invariant and
  `dTV(T*ⁿλ₀, π) ≤ (1 − ε)^⌊n/N⌋` for every `n`, which the book uses but does not state.
* The **Minorization Condition** (`MinorizationFor`, `Minorization`) and **Proposition 3.3.1**.
  The direction Minorization ⇒ Condition M is proved as in the book (`proposition_3_3_1`, first
  part). The book's proof of the converse ("define `μ = δ_A`") is meaningless, and the converse
  fails with the same `N`: on three states, `P(i, ·)` uniform on the two other states satisfies
  Condition M for `(N, ε) = (1, 1/2)` but no minorization with `N = 1`
  (`proposition_3_3_1_counterexample`). Proved instead: Condition M implies the Minorization
  Condition for some larger `N` whenever the invariant measure of Theorem 3.3.1 has an atom
  (`proposition_3_3_1_of_atom`), in particular on every countable state space
  (`proposition_3_3_1`, second part). The general case (true for countably generated
  σ-algebras by Meyn–Tweedie, Theorem 16.0.2) is not formalised.
* **Examples 3.3.1–3.3.3** (`example_3_3_1`, `example_3_3_2`, `example_3_3_3`,
  `example_3_3_3_finite`). In Example 3.3.3 the finite case is stated for a power `Pᴺ` with
  positive entries; that an irreducible aperiodic finite chain has one is Theorem 3.1.4 (the
  `Chain` modules).
-/

namespace Miao.MarkovProcesses

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- **(3.6)** (Miao, p. 104): the **total variation distance**
`dTV(λ₁, λ₂) = sup_{A ∈ 𝒳} |λ₁(A) − λ₂(A)|`. -/
noncomputable def dTV (lam₁ lam₂ : Measure X) : ℝ :=
  sSup ((fun A => |lam₁.real A - lam₂.real A|) '' {A | MeasurableSet A})

theorem gp_dTV_eq_supDiff (lam₁ lam₂ : Measure X) : dTV lam₁ lam₂ = gp_supDiff lam₁ lam₂ := rfl

/-- SLP's total variation norm `‖λ₁ − λ₂‖` is `2 dTV(λ₁, λ₂)` (SLP Lemma 11.5). -/
theorem gp_tvDist_eq_two_mul_dTV (lam₁ lam₂ : Measure X) [IsProbabilityMeasure lam₁]
    [IsProbabilityMeasure lam₂] : tvDist lam₁ lam₂ = 2 * dTV lam₁ lam₂ :=
  (slp_lemma_11_5 lam₁ lam₂ (by simp)).1

theorem gp_abs_le_dTV (lam₁ lam₂ : Measure X) [IsProbabilityMeasure lam₁]
    [IsProbabilityMeasure lam₂] {A : Set X} (hA : MeasurableSet A) :
    |lam₁.real A - lam₂.real A| ≤ dTV lam₁ lam₂ :=
  le_csSup (gp_bddAbove_supDiff lam₁ lam₂) ⟨A, hA, rfl⟩

theorem gp_dTV_le_of_forall (lam₁ lam₂ : Measure X) {δ : ℝ}
    (h : ∀ A, MeasurableSet A → |lam₁.real A - lam₂.real A| ≤ δ) : dTV lam₁ lam₂ ≤ δ := by
  refine csSup_le ⟨_, ∅, MeasurableSet.empty, rfl⟩ ?_
  rintro _ ⟨A, hA, rfl⟩
  exact h A hA

theorem gp_dTV_nonneg (lam₁ lam₂ : Measure X) [IsProbabilityMeasure lam₁]
    [IsProbabilityMeasure lam₂] : 0 ≤ dTV lam₁ lam₂ :=
  (abs_nonneg _).trans (gp_abs_le_dTV lam₁ lam₂ MeasurableSet.empty)

theorem gp_dTV_le_one (lam₁ lam₂ : Measure X) [IsProbabilityMeasure lam₁]
    [IsProbabilityMeasure lam₂] : dTV lam₁ lam₂ ≤ 1 := by
  have := gp_tvDist_le_two lam₁ lam₂
  rw [gp_tvDist_eq_two_mul_dTV] at this
  linarith

/-- Miao, p. 105: `dTV` is a metric on `P(X, 𝒳)`. -/
theorem eq_p105_metric (lam₁ lam₂ lam₃ : Measure X) [IsProbabilityMeasure lam₁]
    [IsProbabilityMeasure lam₂] [IsProbabilityMeasure lam₃] :
    0 ≤ dTV lam₁ lam₂ ∧ dTV lam₁ lam₂ = dTV lam₂ lam₁ ∧
      dTV lam₁ lam₃ ≤ dTV lam₁ lam₂ + dTV lam₂ lam₃ ∧ (dTV lam₁ lam₂ = 0 ↔ lam₁ = lam₂) := by
  have h12 := gp_tvDist_eq_two_mul_dTV lam₁ lam₂
  have h21 := gp_tvDist_eq_two_mul_dTV lam₂ lam₁
  have h13 := gp_tvDist_eq_two_mul_dTV lam₁ lam₃
  have h23 := gp_tvDist_eq_two_mul_dTV lam₂ lam₃
  have hc := gp_tvDist_comm lam₁ lam₂
  have ht := gp_tvDist_triangle lam₁ lam₂ lam₃
  refine ⟨gp_dTV_nonneg lam₁ lam₂, by linarith, by linarith, fun h => ?_, fun h => ?_⟩
  · exact gp_eq_of_tvDist_eq_zero (by linarith)
  · subst h
    refine le_antisymm (gp_dTV_le_of_forall _ _ fun A _ => by simp) (gp_dTV_nonneg _ _)

/-- Miao, p. 105 (SLP Lemma 11.8): `P(X, 𝒳)` with the total variation distance is complete. -/
theorem eq_p105_complete (ls : ℕ → Measure X) [∀ n, IsProbabilityMeasure (ls n)]
    (hC : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, dTV (ls n) (ls m) < ε) :
    ∃ l : Measure X, IsProbabilityMeasure l ∧ Tendsto (fun n => dTV (ls n) l) atTop (𝓝 0) := by
  obtain ⟨l, hl, hconv⟩ := slp_lemma_11_8 ls fun ε hε => by
    obtain ⟨N, hN⟩ := hC (ε / 2) (by positivity)
    refine ⟨N, fun n hn m hm => ?_⟩
    rw [gp_tvDist_eq_two_mul_dTV]
    linarith [hN n hn m hm]
  refine ⟨l, hl, ?_⟩
  have : (fun n => dTV (ls n) l) = fun n => tvDist (ls n) l / 2 := funext fun n => by
    rw [gp_tvDist_eq_two_mul_dTV]; ring
  rw [this]
  simpa using hconv.div_const 2

/-- **Definition 3.3.1** (Miao, p. 105): `λₙ` **converges strongly** to `λ` if
`dTV(λₙ, λ) → 0`. -/
def ConvStrongly (ls : ℕ → Measure X) (l : Measure X) : Prop :=
  Tendsto (fun n => dTV (ls n) l) atTop (𝓝 0)

variable {κ : Kernel X X} [IsMarkovKernel κ]

/-- Proof of **Theorem 3.3.1** (Miao, p. 106; SLP Lemma 11.11): under Condition M for `(N, ε)`,
`T*ᴺ` is a contraction of modulus `1 − ε` for the total variation distance. -/
theorem theorem_3_3_1_contraction {N : ℕ} {ε : ℝ} (hM : ConditionMFor κ N ε)
    (lam₁ lam₂ : Measure X) [IsProbabilityMeasure lam₁] [IsProbabilityMeasure lam₂] :
    dTV (adjointOp (kpow κ N) lam₁) (adjointOp (kpow κ N) lam₂) ≤ (1 - ε) * dTV lam₁ lam₂ := by
  have := gp_isProb_adjoint (κ := κ) N lam₁
  have := gp_isProb_adjoint (κ := κ) N lam₂
  have h := slp_lemma_11_11 hM lam₁ lam₂
  rw [gp_tvDist_eq_two_mul_dTV, gp_tvDist_eq_two_mul_dTV] at h
  linarith

/-- (3.8) in terms of `dTV` is (3.8) in terms of SLP's `tvDist`. -/
theorem gp_eq_3_8_iff {N : ℕ} {ε : ℝ} (π : Measure X) [IsProbabilityMeasure π] :
    (∀ (l₀ : Measure X) [IsProbabilityMeasure l₀] (k : ℕ),
        dTV (adjointOp (kpow κ (N * k)) l₀) π ≤ (1 - ε) ^ k * dTV l₀ π) ↔
      ∀ (l₀ : Measure X) [IsProbabilityMeasure l₀] (k : ℕ),
        tvDist (adjointOp (kpow κ (N * k)) l₀) π ≤ (1 - ε) ^ k * tvDist l₀ π := by
  constructor
  · intro h l₀ _ k
    have := gp_isProb_adjoint (κ := κ) (N * k) l₀
    rw [gp_tvDist_eq_two_mul_dTV, gp_tvDist_eq_two_mul_dTV]
    nlinarith [h l₀ k]
  · intro h l₀ _ k
    have := gp_isProb_adjoint (κ := κ) (N * k) l₀
    have := h l₀ k
    rw [gp_tvDist_eq_two_mul_dTV, gp_tvDist_eq_two_mul_dTV] at this
    nlinarith

/-- **Theorem 3.3.1** (Miao, p. 106; SLP Theorem 11.12). If `P` satisfies Condition M for
`N ≥ 1` and `ε > 0`, there is a unique probability measure `π` with
`dTV(T*ᴺᵏλ₀, π) ≤ (1 − ε)ᵏ dTV(λ₀, π)` (3.8) for all `λ₀ ∈ P(X, 𝒳)` and all `k`. -/
theorem theorem_3_3_1 [Nonempty X] {N : ℕ} {ε : ℝ} (hM : ConditionMFor κ N ε) :
    ∃! π : Measure X, IsProbabilityMeasure π ∧
      ∀ (l₀ : Measure X) [IsProbabilityMeasure l₀] (k : ℕ),
        dTV (adjointOp (kpow κ (N * k)) l₀) π ≤ (1 - ε) ^ k * dTV l₀ π := by
  obtain ⟨π, hπ, h1, huniq, -, -⟩ := slp_theorem_11_12 hM
  refine ⟨π, ⟨hπ, (gp_eq_3_8_iff π).2 h1⟩, ?_⟩
  rintro π' ⟨hπ', h'⟩
  exact huniq π' hπ' ((gp_eq_3_8_iff π').1 h')

/-- Theorem 3.3.1 (Miao, p. 106): the measure `π` is invariant, `T*π = π`, and
`dTV(T*ⁿλ₀, π) ≤ (1 − ε)^⌊n/N⌋` for every `n`. -/
theorem theorem_3_3_1_invariant [Nonempty X] {N : ℕ} {ε : ℝ} (hM : ConditionMFor κ N ε) :
    ∃ π : Measure X, IsProbabilityMeasure π ∧ adjointOp κ π = π ∧
      (∀ (l₀ : Measure X) [IsProbabilityMeasure l₀] (k : ℕ),
        dTV (adjointOp (kpow κ (N * k)) l₀) π ≤ (1 - ε) ^ k * dTV l₀ π) ∧
      ∀ (l₀ : Measure X) [IsProbabilityMeasure l₀] (n : ℕ),
        dTV (adjointOp (kpow κ n) l₀) π ≤ (1 - ε) ^ (n / N) := by
  obtain ⟨π, hπ, h1, -, hinv, hrate⟩ := slp_theorem_11_12 hM
  refine ⟨π, hπ, hinv, (gp_eq_3_8_iff π).2 h1, fun l₀ _ n => ?_⟩
  have := gp_isProb_adjoint (κ := κ) n l₀
  have := hrate l₀ n
  rw [gp_tvDist_eq_two_mul_dTV] at this
  linarith

/-- **Theorem 3.3.1**, converse (Miao, p. 107): if (3.8) holds for some `N ≥ 1`, `0 < ε ≤ 1` and
probability measure `π`, then Condition M holds (for `(NK, 1/4)` with `(1 − ε)ᴷ ≤ 1/4`). -/
theorem theorem_3_3_1_converse {N : ℕ} {ε : ℝ} (hN : 1 ≤ N) (hε : 0 < ε) (hε1 : ε ≤ 1)
    {π : Measure X} [IsProbabilityMeasure π]
    (h : ∀ (l₀ : Measure X) [IsProbabilityMeasure l₀] (k : ℕ),
      dTV (adjointOp (kpow κ (N * k)) l₀) π ≤ (1 - ε) ^ k * dTV l₀ π) :
    ConditionM κ :=
  slp_theorem_11_12_converse hN hε hε1 ((gp_eq_3_8_iff π).1 h)

omit [IsMarkovKernel κ] in
/-- The **Minorization Condition** for `(N, α, μ)` (Miao, p. 107): `N ≥ 1`, `α > 0`, `μ` is a
probability measure and `Pᴺ(x, ·) ≥ αμ(·)` for all `x`. -/
def MinorizationFor (κ : Kernel X X) (N : ℕ) (α : ℝ) (μ : Measure X) : Prop :=
  1 ≤ N ∧ 0 < α ∧ IsProbabilityMeasure μ ∧
    ∀ x A, MeasurableSet A → α * μ.real A ≤ (kpow κ N x).real A

/-- The **Minorization Condition** holds for some `(N, α, μ)`. -/
def Minorization (κ : Kernel X X) : Prop := ∃ N α μ, MinorizationFor κ N α μ

omit [IsMarkovKernel κ] in
/-- **Proposition 3.3.1**, first half (Miao, p. 107): the Minorization Condition for
`(N, α, μ)` implies Condition M for `(N, α/2)`. -/
theorem proposition_3_3_1_forward {N : ℕ} {α : ℝ} {μ : Measure X}
    (h : MinorizationFor κ N α μ) : ConditionMFor κ N (α / 2) := by
  obtain ⟨hN, hα, hμ, hmin⟩ := h
  refine ⟨hN, by positivity, fun A hA => ?_⟩
  rcases le_total (1 / 2) (μ.real A) with h2 | h2
  · exact Or.inl fun x => by nlinarith [hmin x A hA]
  · refine Or.inr fun x => ?_
    have hc : μ.real Aᶜ = 1 - μ.real A := probReal_compl_eq_one_sub hA
    nlinarith [hmin x Aᶜ hA.compl]

/-- The three-state kernel `P(i, ·) = ½(δ_{i+1} + δ_{i+2})` on `Fin 3`. -/
noncomputable def gp_threeKernel : Kernel (Fin 3) (Fin 3) :=
  Kernel.ofFunOfCountable fun i => (1 / 2 : ℝ≥0∞) • (Measure.dirac (i + 1) + Measure.dirac (i + 2))

theorem gp_threeKernel_real (i : Fin 3) (A : Set (Fin 3)) :
    (gp_threeKernel i).real A =
      (A.indicator (1 : Fin 3 → ℝ) (i + 1) + A.indicator (1 : Fin 3 → ℝ) (i + 2)) / 2 := by
  have h : gp_threeKernel i A =
      2⁻¹ * A.indicator 1 (i + 1) + 2⁻¹ * A.indicator 1 (i + 2) := by
    simp [gp_threeKernel, Kernel.ofFunOfCountable]
  rw [measureReal_def, h]
  by_cases h1 : i + 1 ∈ A <;> by_cases h2 : i + 2 ∈ A <;> simp [h1, h2, ENNReal.inv_two_add_inv_two]

/-- **Proposition 3.3.1**: the converse fails with the same `N`. On `Fin 3`, the kernel
`P(i, ·) = ½(δ_{i+1} + δ_{i+2})` satisfies Condition M for `(1, 1/2)` but the Minorization
Condition for `N = 1` fails for every `α` and `μ` (the book's proof claims `(N, ε)`). -/
theorem proposition_3_3_1_counterexample :
    ConditionMFor gp_threeKernel 1 (1 / 2) ∧ ∀ α μ, ¬ MinorizationFor gp_threeKernel 1 α μ := by
  refine ⟨⟨le_rfl, by norm_num, fun A _ => ?_⟩, fun α μ ⟨_, hα, hμ, hmin⟩ => ?_⟩
  · simp only [gp_kpow_one, gp_threeKernel_real]
    by_cases h0 : (0 : Fin 3) ∈ A <;> by_cases h1 : (1 : Fin 3) ∈ A <;>
      by_cases h2 : (2 : Fin 3) ∈ A
    all_goals try (left; intro i; fin_cases i <;> simp_all <;> norm_num; done)
    all_goals (right; intro i; fin_cases i <;> simp_all <;> norm_num)
  · have hz : ∀ i : Fin 3, μ {i} = 0 := fun i => by
      have := hmin i {i} (MeasurableSet.singleton i)
      rw [gp_kpow_one, gp_threeKernel_real] at this
      have hne1 : i + 1 ≠ i := by fin_cases i <;> decide
      have hne2 : i + 2 ≠ i := by fin_cases i <;> decide
      rw [Set.indicator_of_notMem (by simp [hne1]),
        Set.indicator_of_notMem (by simp [hne2]), add_zero, zero_div] at this
      have h0 : μ.real {i} = 0 :=
        le_antisymm (by nlinarith [measureReal_nonneg (μ := μ) (s := {i})]) measureReal_nonneg
      exact (measureReal_eq_zero_iff (measure_ne_top μ _)).1 h0
    have : μ Set.univ ≤ ∑' i : Fin 3, μ {i} := by
      rw [← Set.iUnion_of_singleton (α := Fin 3)]
      exact measure_iUnion_le _
    simp [hz] at this

/-- Corrected **Proposition 3.3.1**, converse: if Condition M holds and the invariant measure
`π` of Theorem 3.3.1 has an atom `x₀`, the Minorization Condition holds with `μ = δ_{x₀}`. -/
theorem proposition_3_3_1_of_atom [MeasurableSingletonClass X] {N : ℕ} {ε : ℝ}
    (hM : ConditionMFor κ N ε) {π : Measure X} [IsProbabilityMeasure π]
    (h38 : ∀ (l₀ : Measure X) [IsProbabilityMeasure l₀] (k : ℕ),
      dTV (adjointOp (kpow κ (N * k)) l₀) π ≤ (1 - ε) ^ k * dTV l₀ π)
    {x₀ : X} (hx₀ : 0 < π.real {x₀}) : Minorization κ := by
  obtain ⟨hN, hε, hMA⟩ := hM
  have hε1 : ε ≤ 1 := by
    have := gp_isMarkov_kpow (κ := κ) N
    rcases hMA ∅ MeasurableSet.empty with h | h
    · have := h x₀; simp at this; linarith
    · have := h x₀; simp at this; linarith
  have hlim : Tendsto (fun k => (1 - ε) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  obtain ⟨K₀, hK₀⟩ := (hlim.eventually (gt_mem_nhds (half_pos hx₀))).exists_forall_of_atTop
  set K := K₀ + 1
  have hK : (1 - ε) ^ K < π.real {x₀} / 2 := hK₀ K (by omega)
  have hNK : 1 ≤ N * K := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have := gp_isMarkov_kpow (κ := κ) (N * K)
  have hclose : ∀ x, π.real {x₀} / 2 ≤ (kpow κ (N * K) x).real {x₀} := fun x => by
    have e : adjointOp (kpow κ (N * K)) (Measure.dirac x) = kpow κ (N * K) x :=
      Measure.dirac_bind (Kernel.measurable _) x
    have h1 := h38 (Measure.dirac x) K
    rw [e] at h1
    have h2 := gp_abs_le_dTV (kpow κ (N * K) x) π (MeasurableSet.singleton x₀)
    have h3 := gp_dTV_le_one (Measure.dirac x) π
    have h4 : (1 - ε) ^ K * dTV (Measure.dirac x) π ≤ (1 - ε) ^ K :=
      mul_le_of_le_one_right (pow_nonneg (by linarith) _) h3
    have := (abs_le.1 (h2.trans (h1.trans h4))).1
    linarith
  refine ⟨N * K, π.real {x₀} / 2, Measure.dirac x₀, hNK, half_pos hx₀, inferInstance,
    fun x A hA => ?_⟩
  by_cases hA0 : x₀ ∈ A
  · have h1 : (Measure.dirac x₀).real A = 1 := by
      simp [measureReal_def, Measure.dirac_apply_of_mem hA0]
    rw [h1, mul_one]
    exact (hclose x).trans (measureReal_mono (Set.singleton_subset_iff.2 hA0))
  · have h0 : (Measure.dirac x₀).real A = 0 := by
      simp [measureReal_def, Measure.dirac_apply' _ hA, Set.indicator_of_notMem hA0]
    rw [h0, mul_zero]
    exact measureReal_nonneg

/-- **Proposition 3.3.1** (Miao, p. 107), corrected. The Minorization Condition implies
Condition M; on a nonempty countable state space (with measurable singletons) Condition M
implies the Minorization Condition. (On `X = ∅` Condition M holds vacuously and the
Minorization Condition fails, since there is no probability measure.) -/
theorem proposition_3_3_1 :
    (Minorization κ → ConditionM κ) ∧
      (∀ [Countable X] [MeasurableSingletonClass X] [Nonempty X],
        ConditionM κ → Minorization κ) := by
  refine ⟨fun ⟨N, α, μ, h⟩ => ⟨N, α / 2, proposition_3_3_1_forward h⟩, fun hM => ?_⟩
  obtain ⟨N, ε, hM⟩ := hM
  obtain ⟨π, ⟨hπ, h38⟩, -⟩ := theorem_3_3_1 hM
  have : ∃ x₀, 0 < π.real {x₀} := by
    by_contra hcon
    push Not at hcon
    have hz : ∀ x, π {x} = 0 := fun x =>
      (measureReal_eq_zero_iff (measure_ne_top π _)).1 (le_antisymm (hcon x) measureReal_nonneg)
    have := π.tsum_indicator_apply_singleton Set.univ MeasurableSet.univ
    simp [hz] at this
  obtain ⟨x₀, hx₀⟩ := this
  exact proposition_3_3_1_of_atom hM h38 hx₀

/-- **Example 3.3.1** (Miao, p. 108). If `Pᴺ(x, {x₀}) > ε` for all `x`, Condition M holds for
`(N, ε)`: a set containing `x₀`, or its complement, has `Pᴺ`-mass at least `ε` from every `x`. -/
theorem example_3_3_1 [MeasurableSingletonClass X] {x₀ : X} {N : ℕ} {ε : ℝ} (hN : 1 ≤ N)
    (hε : 0 < ε) (h : ∀ x, ε < (kpow κ N x).real {x₀}) : ConditionMFor κ N ε := by
  have := gp_isMarkov_kpow (κ := κ) N
  refine ⟨hN, hε, fun A _ => ?_⟩
  by_cases hA : x₀ ∈ A
  · exact Or.inl fun x => (h x).le.trans (measureReal_mono (Set.singleton_subset_iff.2 hA))
  · exact Or.inr fun x => (h x).le.trans (measureReal_mono (Set.singleton_subset_iff.2 hA))

/-- **Example 3.3.2** (Miao, p. 108). If `P(x, A) = ∫_A p(x, x′) μ(dx′)` with `p ≥ ε > 0` and `μ`
a probability measure, the Minorization Condition holds for `(1, ε, μ)`. -/
theorem example_3_3_2 {μ : Measure X} [IsProbabilityMeasure μ] {p : X → X → ℝ≥0∞} {ε : ℝ}
    (hε : 0 < ε) (hp : ∀ x y, ENNReal.ofReal ε ≤ p x y)
    (hP : ∀ x A, MeasurableSet A → κ x A = ∫⁻ y in A, p x y ∂μ) :
    MinorizationFor κ 1 ε μ := by
  refine ⟨le_rfl, hε, inferInstance, fun x A hA => ?_⟩
  rw [gp_kpow_one]
  have hle : ENNReal.ofReal ε * μ A ≤ κ x A := by
    rw [hP x A hA, ← setLIntegral_const]
    exact lintegral_mono fun y => hp x y
  have := ENNReal.toReal_mono (measure_ne_top (κ x) A) hle
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hε.le] at this

/-- **Example 3.3.3** (Miao, p. 108). On a countable `X`, if
`α = Σ_y inf_x Pᴺ(x, {y}) > 0` (3.9), the Minorization Condition holds for `(N, α, ν)` with
`ν{y} = α⁻¹ inf_x Pᴺ(x, {y})`. -/
theorem example_3_3_3 [Countable X] [MeasurableSingletonClass X] {N : ℕ} (hN : 1 ≤ N)
    (hα : 0 < ∑' y, ⨅ x, kpow κ N x {y}) :
    ∃ ν : Measure X, (∀ y, ν {y} = (∑' y, ⨅ x, kpow κ N x {y})⁻¹ * ⨅ x, kpow κ N x {y}) ∧
      MinorizationFor κ N (∑' y, ⨅ x, kpow κ N x {y}).toReal ν := by
  have := gp_isMarkov_kpow (κ := κ) N
  set m : X → ℝ≥0∞ := fun y => ⨅ x, kpow κ N x {y}
  set α := ∑' y, m y
  have hX : Nonempty X := by
    by_contra hX
    rw [not_nonempty_iff] at hX
    simp [α] at hα
  obtain ⟨x₀⟩ := hX
  have hα1 : α ≤ 1 := by
    calc α ≤ ∑' y, kpow κ N x₀ {y} := ENNReal.tsum_le_tsum fun y => iInf_le _ x₀
      _ = kpow κ N x₀ Set.univ := by
          simpa using (kpow κ N x₀).tsum_indicator_apply_singleton Set.univ MeasurableSet.univ
      _ = 1 := measure_univ
  have hαt : α ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hα1
  set ν : Measure X := Measure.sum fun y => (α⁻¹ * m y) • Measure.dirac y
  have hνA : ∀ A, MeasurableSet A → ν A = ∑' y, A.indicator (fun y => α⁻¹ * m y) y := by
    intro A hA
    simp only [ν, Measure.sum_apply _ hA, Measure.smul_apply, Measure.dirac_apply' _ hA,
      smul_eq_mul]
    congr 1
    funext y
    by_cases hy : y ∈ A <;> simp [hy]
  have hν1 : ν Set.univ = 1 := by
    rw [hνA _ MeasurableSet.univ]
    simp only [Set.indicator_univ]
    rw [ENNReal.tsum_mul_left, ENNReal.inv_mul_cancel hα.ne' hαt]
  have hνp : IsProbabilityMeasure ν := ⟨hν1⟩
  refine ⟨ν, fun y => ?_, hN, ENNReal.toReal_pos hα.ne' hαt, hνp, fun x A hA => ?_⟩
  · rw [hνA _ (MeasurableSet.singleton y), tsum_eq_single y fun z hz => by simp [hz]]
    simp [m]
  · have hle : α * ν A ≤ kpow κ N x A := by
      rw [hνA A hA, ← ENNReal.tsum_mul_left,
        ← (kpow κ N x).tsum_indicator_apply_singleton A hA]
      refine ENNReal.tsum_le_tsum fun y => ?_
      by_cases hy : y ∈ A
      · simp only [Set.indicator_of_mem hy]
        rw [← mul_assoc, ENNReal.mul_inv_cancel hα.ne' hαt, one_mul]
        exact iInf_le _ x
      · simp [hy]
    have := ENNReal.toReal_mono (measure_ne_top _ A) hle
    rwa [ENNReal.toReal_mul] at this

omit [IsMarkovKernel κ] in
/-- **Example 3.3.3**, finite case (Miao, p. 108): if `X` is finite and nonempty and some power
`Pᴺ` has all entries positive (by Theorem 3.1.4 this holds for an irreducible aperiodic chain),
then (3.9) holds. -/
theorem example_3_3_3_finite [Finite X] [Nonempty X] {N : ℕ}
    (hpos : ∀ x y, 0 < kpow κ N x {y}) : 0 < ∑' y, ⨅ x, kpow κ N x {y} := by
  obtain ⟨y₀⟩ := ‹Nonempty X›
  obtain ⟨x₁, hx₁⟩ := exists_eq_ciInf_of_finite (f := fun x => kpow κ N x {y₀})
  calc (0 : ℝ≥0∞) < ⨅ x, kpow κ N x {y₀} := by rw [← hx₁]; exact hpos x₁ y₀
    _ ≤ ∑' y, ⨅ x, kpow κ N x {y} := ENNReal.le_tsum (f := fun y => ⨅ x, kpow κ N x {y}) y₀

end Miao.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Formulas for the total variation distance (Exercise 3.5 and (3.7))

Miao, (3.7), p. 105, and Exercise 3.5, p. 114, with the book's normalisation
`dTV(λ₁, λ₂) = sup_A |λ₁(A) − λ₂(A)|` (3.6). With this normalisation all three formulas hold as
printed; SLP's norm `‖λ₁ − λ₂‖` is `2 dTV` (`gp_tvDist_eq_two_mul_dTV`), which is where a factor
of `2` would otherwise appear.

* **Exercise 3.5(b)** (`ex_3_5b`): if `λ₁, λ₂` have densities `g, h` with respect to `ρ`, then
  `dTV(λ₁, λ₂) = 1 − ∫ min(g, h) dρ = ½ ∫ |g − h| dρ = ∫ (g − h)⁺ dρ`, the supremum being
  attained at `A = {g > h}`.
* **(3.7)** (`eq_3_7`): the same with `ρ = ν = λ₁ + λ₂` and the Radon–Nikodym derivatives
  `dλᵢ/dν`.
* **Exercise 3.5(a)** (`ex_3_5a`): for `a < b`,
  `dTV(λ₁, λ₂) = (b − a)⁻¹ sup_{f : X → [a, b]} |∫ f dλ₁ − ∫ f dλ₂|`, the supremum over
  measurable `f`.
-/

namespace Miao.MarkovProcesses

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- A measure with a nonnegative integrable density: `λ(A) = ∫_A g dρ`. -/
theorem gp_withDensity_real {ρ : Measure X} {g : X → ℝ} (hg0 : 0 ≤ g) (hgi : Integrable g ρ)
    {A : Set X} (hA : MeasurableSet A) :
    (ρ.withDensity fun x => ENNReal.ofReal (g x)).real A = ∫ x in A, g x ∂ρ := by
  rw [measureReal_def, withDensity_apply _ hA,
    ← ofReal_integral_eq_lintegral_ofReal hgi.integrableOn (ae_of_all _ fun x => hg0 x),
    ENNReal.toReal_ofReal (setIntegral_nonneg hA fun x _ => hg0 x)]

/-- The density of a probability measure is integrable. -/
theorem gp_integrable_density {ρ : Measure X} {lam : Measure X} [IsProbabilityMeasure lam]
    {g : X → ℝ} (hgm : Measurable g) (hg0 : 0 ≤ g)
    (hl : lam = ρ.withDensity fun x => ENNReal.ofReal (g x)) : Integrable g ρ := by
  refine ⟨hgm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hg0)).2 ?_⟩
  have := measure_univ (μ := lam)
  rw [hl, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
  rw [this]
  exact ENNReal.one_lt_top

/-- **Exercise 3.5(b)** (Miao, p. 114). If `λ₁` and `λ₂` have densities `g` and `h` with respect
to `ρ`, then `dTV(λ₁, λ₂) = 1 − ∫ min(g, h) dρ`; moreover `dTV(λ₁, λ₂) = ½ ∫ |g − h| dρ` and
the supremum in (3.6) is attained at `A = {g > h}`. -/
theorem ex_3_5b {ρ : Measure X} (lam₁ lam₂ : Measure X) [IsProbabilityMeasure lam₁]
    [IsProbabilityMeasure lam₂] {g h : X → ℝ} (hgm : Measurable g) (hhm : Measurable h)
    (hg0 : 0 ≤ g) (hh0 : 0 ≤ h) (h1 : lam₁ = ρ.withDensity fun x => ENNReal.ofReal (g x))
    (h2 : lam₂ = ρ.withDensity fun x => ENNReal.ofReal (h x)) :
    dTV lam₁ lam₂ = 1 - ∫ x, min (g x) (h x) ∂ρ ∧
      dTV lam₁ lam₂ = 1 / 2 * ∫ x, |g x - h x| ∂ρ ∧
      dTV lam₁ lam₂ = lam₁.real {x | h x < g x} - lam₂.real {x | h x < g x} := by
  have hgi := gp_integrable_density hgm hg0 h1
  have hhi := gp_integrable_density hhm hh0 h2
  have hr1 : ∀ A, MeasurableSet A → lam₁.real A = ∫ x in A, g x ∂ρ := fun A hA => by
    rw [h1]; exact gp_withDensity_real hg0 hgi hA
  have hr2 : ∀ A, MeasurableSet A → lam₂.real A = ∫ x in A, h x ∂ρ := fun A hA => by
    rw [h2]; exact gp_withDensity_real hh0 hhi hA
  have hg1 : ∫ x, g x ∂ρ = 1 := by
    have := hr1 Set.univ MeasurableSet.univ
    rwa [probReal_univ, Measure.restrict_univ, eq_comm] at this
  have hh1 : ∫ x, h x ∂ρ = 1 := by
    have := hr2 Set.univ MeasurableSet.univ
    rwa [probReal_univ, Measure.restrict_univ, eq_comm] at this
  set D := ∫ x, max (g x - h x) 0 ∂ρ
  set D' := ∫ x, max (h x - g x) 0 ∂ρ
  have hgh : Integrable (fun x => g x - h x) ρ := hgi.sub hhi
  have hhg : Integrable (fun x => h x - g x) ρ := hhi.sub hgi
  have hpi : Integrable (fun x => max (g x - h x) 0) ρ := hgh.sup (integrable_zero _ _ _)
  have hpi' : Integrable (fun x => max (h x - g x) 0) ρ := hhg.sup (integrable_zero _ _ _)
  have hDD : D = D' := by
    have : ∫ x, (max (g x - h x) 0 - max (h x - g x) 0) ∂ρ = 0 := by
      have e : (fun x => max (g x - h x) 0 - max (h x - g x) 0) = fun x => g x - h x :=
        funext fun x => by
          rcases le_total (g x) (h x) with hx | hx
          · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
          · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
      rw [e, integral_sub hgi hhi, hg1, hh1, sub_self]
    rw [integral_sub hpi hpi'] at this
    linarith
  have hB : MeasurableSet {x | h x < g x} := measurableSet_lt hhm hgm
  have hDB : D = ∫ x in {x | h x < g x}, (g x - h x) ∂ρ := by
    rw [← integral_indicator hB]
    change ∫ x, max (g x - h x) 0 ∂ρ = _
    congr 1
    funext x
    by_cases hx : h x < g x
    · rw [Set.indicator_of_mem (show x ∈ {x | h x < g x} from hx), max_eq_left (by linarith)]
    · rw [Set.indicator_of_notMem (show x ∉ {x | h x < g x} from hx),
        max_eq_right (by push Not at hx; linarith)]
  have hdiff : ∀ A, MeasurableSet A →
      lam₁.real A - lam₂.real A = ∫ x in A, (g x - h x) ∂ρ := fun A hA => by
    rw [hr1 A hA, hr2 A hA, integral_sub hgi.integrableOn hhi.integrableOn]
  have hbound : ∀ A, MeasurableSet A → |lam₁.real A - lam₂.real A| ≤ D := by
    intro A hA
    rw [hdiff A hA, abs_le]
    constructor
    · have : ∫ x in A, (h x - g x) ∂ρ ≤ D' :=
        (setIntegral_mono hhg.integrableOn hpi'.integrableOn fun x => le_max_left _ _).trans
          (setIntegral_le_integral hpi' (ae_of_all _ fun x => le_max_right _ _))
      have e : ∫ x in A, (h x - g x) ∂ρ = -∫ x in A, (g x - h x) ∂ρ := by
        rw [← integral_neg]; congr 1; funext x; ring
      linarith
    · exact (setIntegral_mono hgh.integrableOn hpi.integrableOn fun x => le_max_left _ _).trans
        (setIntegral_le_integral hpi (ae_of_all _ fun x => le_max_right _ _))
  have hdTV : dTV lam₁ lam₂ = D := by
    refine le_antisymm (gp_dTV_le_of_forall _ _ hbound) ?_
    have := gp_abs_le_dTV lam₁ lam₂ hB
    rw [hdiff _ hB, ← hDB] at this
    exact (le_abs_self D).trans this
  refine ⟨?_, ?_, ?_⟩
  · rw [hdTV]
    have e : (fun x => max (g x - h x) 0) = fun x => g x - min (g x) (h x) := funext fun x => by
      rcases le_total (g x) (h x) with hx | hx
      · rw [max_eq_right (by linarith), min_eq_left hx]; ring
      · rw [max_eq_left (by linarith), min_eq_right hx]
    have hmi : Integrable (fun x => min (g x) (h x)) ρ := hgi.inf hhi
    change ∫ x, max (g x - h x) 0 ∂ρ = _
    rw [e, integral_sub hgi hmi, hg1]
  · rw [hdTV]
    have e : (fun x => |g x - h x|) = fun x => max (g x - h x) 0 + max (h x - g x) 0 :=
      funext fun x => by
        rcases le_total (g x) (h x) with hx | hx
        · rw [abs_of_nonpos (by linarith), max_eq_right (by linarith), max_eq_left (by linarith)]
          ring
        · rw [abs_of_nonneg (by linarith), max_eq_left (by linarith), max_eq_right (by linarith)]
          ring
    rw [e, integral_add hpi hpi']
    change D = 1 / 2 * (D + D')
    rw [← hDD]
    ring
  · rw [hdTV, hdiff _ hB, hDB]

/-- **(3.7)** (Miao, p. 105). With `ν = λ₁ + λ₂` and the Radon–Nikodym derivatives
`dλᵢ/dν`, `dTV(λ₁, λ₂) = ½ ∫ |dλ₁/dν − dλ₂/dν| dν = 1 − ∫ min(dλ₁/dν, dλ₂/dν) dν`. -/
theorem eq_3_7 (lam₁ lam₂ : Measure X) [IsProbabilityMeasure lam₁] [IsProbabilityMeasure lam₂] :
    dTV lam₁ lam₂ = 1 / 2 * ∫ x, |(lam₁.rnDeriv (lam₁ + lam₂) x).toReal -
        (lam₂.rnDeriv (lam₁ + lam₂) x).toReal| ∂(lam₁ + lam₂) ∧
      dTV lam₁ lam₂ = 1 - ∫ x, min (lam₁.rnDeriv (lam₁ + lam₂) x).toReal
        (lam₂.rnDeriv (lam₁ + lam₂) x).toReal ∂(lam₁ + lam₂) := by
  set ν := lam₁ + lam₂
  have hdens : ∀ (lam : Measure X) [IsProbabilityMeasure lam], lam ≤ ν →
      lam = ν.withDensity fun x => ENNReal.ofReal (lam.rnDeriv ν x).toReal := by
    intro lam _ hle
    have hac : lam ≪ ν := Measure.absolutelyContinuous_of_le hle
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq lam ν hac]
    refine withDensity_congr_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top lam ν] with x hx
    rw [ENNReal.ofReal_toReal hx.ne]
  have e1 := hdens lam₁ (Measure.le_add_right le_rfl)
  have e2 := hdens lam₂ (Measure.le_add_left le_rfl)
  obtain ⟨hmin, habs, -⟩ := ex_3_5b lam₁ lam₂ (Measure.measurable_rnDeriv _ _).ennreal_toReal
    (Measure.measurable_rnDeriv _ _).ennreal_toReal (fun x => ENNReal.toReal_nonneg)
    (fun x => ENNReal.toReal_nonneg) e1 e2
  exact ⟨habs, hmin⟩

/-- **Exercise 3.5(a)** (Miao, p. 114). For `a < b`,
`dTV(λ₁, λ₂) = (b − a)⁻¹ sup_{f : X → [a, b]} |∫ f dλ₁ − ∫ f dλ₂|`, the supremum taken over
measurable `f`. -/
theorem ex_3_5a (lam₁ lam₂ : Measure X) [IsProbabilityMeasure lam₁] [IsProbabilityMeasure lam₂]
    {a b : ℝ} (hab : a < b) :
    dTV lam₁ lam₂ = (b - a)⁻¹ * sSup {r | ∃ f : X → ℝ, Measurable f ∧
      (∀ x, f x ∈ Set.Icc a b) ∧ r = |∫ x, f x ∂lam₁ - ∫ x, f x ∂lam₂|} := by
  set S := {r | ∃ f : X → ℝ, Measurable f ∧
      (∀ x, f x ∈ Set.Icc a b) ∧ r = |∫ x, f x ∂lam₁ - ∫ x, f x ∂lam₂|}
  have hba : 0 < b - a := sub_pos.2 hab
  have hbound : ∀ r ∈ S, r ≤ (b - a) * dTV lam₁ lam₂ := by
    rintro _ ⟨f, hf, hfab, rfl⟩
    set φ : X → ℝ := fun x => (2 * f x - (a + b)) / (b - a)
    have hφ : Measurable φ := ((hf.const_mul 2).sub_const _).div_const _
    have hφ1 : ∀ x, |φ x| ≤ 1 := fun x => by
      obtain ⟨h1, h2⟩ := hfab x
      rw [abs_div, abs_of_pos hba, div_le_one hba, abs_le]
      constructor <;> linarith
    have hfi : ∀ (lam : Measure X) [IsProbabilityMeasure lam], Integrable f lam :=
      fun lam _ => gp_integrable_of_bounded hf (M := max |a| |b|) fun x => by
        obtain ⟨h1, h2⟩ := hfab x
        rw [abs_le]
        constructor
        · linarith [neg_abs_le a, le_max_left |a| |b|]
        · linarith [le_abs_self b, le_max_right |a| |b|]
    have hint : ∀ (lam : Measure X) [IsProbabilityMeasure lam],
        ∫ x, φ x ∂lam = (2 * ∫ x, f x ∂lam - (a + b)) / (b - a) := fun lam _ => by
      simp only [φ]
      rw [integral_div, integral_sub ((hfi lam).const_mul 2) (integrable_const _),
        integral_const_mul, integral_const, probReal_univ, one_smul]
    have h := gp_abs_integral_sub_le_tvDist lam₁ lam₂ hφ hφ1
    rw [hint lam₁, hint lam₂, gp_tvDist_eq_two_mul_dTV, ← sub_div, abs_div, abs_of_pos hba,
      div_le_iff₀ hba] at h
    have e : 2 * ∫ x, f x ∂lam₁ - (a + b) - (2 * ∫ x, f x ∂lam₂ - (a + b)) =
        2 * (∫ x, f x ∂lam₁ - ∫ x, f x ∂lam₂) := by ring
    rw [e, abs_mul, abs_two] at h
    nlinarith
  have hne : S.Nonempty := ⟨_, fun _ => a, measurable_const, fun _ => ⟨le_rfl, hab.le⟩, rfl⟩
  have hbdd : BddAbove S := ⟨_, hbound⟩
  have hattain : ∀ A, MeasurableSet A →
      (b - a) * |lam₁.real A - lam₂.real A| ∈ S := by
    intro A hA
    refine ⟨fun x => a + (b - a) * A.indicator 1 x,
      measurable_const.add ((measurable_one.indicator hA).const_mul _), fun x => ?_, ?_⟩
    · by_cases hx : x ∈ A
      · simp only [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
        exact ⟨by linarith, by linarith⟩
      · simp only [Set.indicator_of_notMem hx, mul_zero, add_zero]
        exact ⟨le_rfl, hab.le⟩
    · have hint : ∀ (lam : Measure X) [IsProbabilityMeasure lam],
          ∫ x, (a + (b - a) * A.indicator 1 x) ∂lam = a + (b - a) * lam.real A :=
        fun lam _ => by
          have hI : Integrable (fun x => (b - a) * A.indicator (1 : X → ℝ) x) lam :=
            ((integrable_const (1 : ℝ)).indicator hA).const_mul _
          rw [integral_add (integrable_const _) hI, integral_const,
            probReal_univ, one_smul, integral_const_mul, integral_indicator_one hA]
      rw [hint lam₁, hint lam₂]
      have e : a + (b - a) * lam₁.real A - (a + (b - a) * lam₂.real A) =
          (b - a) * (lam₁.real A - lam₂.real A) := by ring
      rw [e, abs_mul, abs_of_pos hba]
  have hS : sSup S = (b - a) * dTV lam₁ lam₂ := by
    refine le_antisymm (csSup_le hne hbound) ?_
    rw [← le_div_iff₀' hba]
    refine gp_dTV_le_of_forall _ _ fun A hA => ?_
    rw [le_div_iff₀' hba]
    exact le_csSup hbdd (hattain A hA)
  rw [hS, ← mul_assoc, inv_mul_cancel₀ hba.ne', one_mul]

end Miao.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Weak convergence: basic tools

Copied from `RecursiveMethods/WeakConvergence` (SLP Chapter 12, module `WeakBasics.lean`), with the
namespace renamed to `Miao.MarkovProcesses`, the results numbered in SLP prefixed
`slp_` and the helper lemmas and definitions prefixed `gp_`.

SLP §12.1, pp. 353–358. `(S, ρ)` is a metric space with its Borel sets.

* **Exercise 12.1** (`slp_ex_12_1`): for a Borel `S ⊆ ℝˡ`, the Borel sets of `S` are the Borel sets
  of
  `ℝˡ` contained in `S`; relatively open sets are traces of open sets; relative interiors are
  relatively open; and an open set is its own interior.
* **Exercise 12.2** (`slp_ex_12_2`): the distance `ρ(s, A)` is `1`-Lipschitz, hence uniformly
  continuous, and `Ā = {s : ρ(s, A) = 0}` for nonempty `A`.
* `ConvWeak` (p. 354): `λₙ ⇒ λ` if `∫ f dλₙ → ∫ f dλ` for every bounded continuous `f`.
* **Lemma 12.1** (`slp_lemma_12_1`): for a closed `F` the continuous functions
  `fₙ(s) = max(0, 1 − n ρ(s, F))` decrease, equal `1` on `F`, lie in `[0, 1]`, and
  `∫ fₙ dλ → λ(F)` for every probability measure `λ`. The book proves the limit with the sets
  `Fₙ = {ρ(·, F) ≤ 1/n}`; here dominated convergence is used.
* **Lemma 12.2** (`slp_lemma_12_2`): for measurable `a ≤ f < b`, the sets `Fᵢ = {f ≥ a + ic/k}` give
  `a + (c/k) Σ μ(Fᵢ) ≤ ∫ f dμ ≤ a + (c/k) Σ μ(Fᵢ) + ε` for every probability `μ`. The `Fᵢ` are
  closed if `f` is continuous. The book sums by parts; here the pointwise inequality
  `m/k ≤ g < (m + 1)/k`, with `m = #{i ≤ k : i/k ≤ g}`, is integrated.
-/

namespace Miao.MarkovProcesses

open MeasureTheory Filter Topology Set BoundedContinuousFunction

/-- **Exercise 12.1.** For a Borel set `S ⊆ ℝˡ`: (a) the Borel sets of `S` are the Borel subsets
of `ℝˡ` contained in `S`; (b) the relatively open sets are the traces `A′ ∩ S` of open sets;
(c) relative interiors are relatively open; (d) a relatively open set is its own interior. -/
theorem slp_ex_12_1 {l : ℕ} {S : Set (Fin l → ℝ)} (hS : MeasurableSet S) :
    (∀ A : Set S, MeasurableSet A ↔ MeasurableSet (Subtype.val '' A)) ∧
      (∀ A : Set S, IsOpen A ↔ ∃ A' : Set (Fin l → ℝ), IsOpen A' ∧ Subtype.val ⁻¹' A' = A) ∧
      (∀ A : Set S, IsOpen (interior A)) ∧ ∀ A : Set S, IsOpen A → interior A = A := by
  refine ⟨fun A => ⟨fun hA => hS.subtype_image hA, fun hA => ?_⟩, fun A => isOpen_induced_iff,
    fun A => isOpen_interior, fun A hA => hA.interior_eq⟩
  have := (measurable_subtype_coe (p := fun x => x ∈ S)) hA
  rwa [Subtype.val_injective.preimage_image] at this

variable {S : Type*} [MetricSpace S]

/-- **Exercise 12.2.** (a) `|ρ(x, A) − ρ(y, A)| ≤ ρ(x, y)`; (b) `ρ(·, A)` is uniformly
continuous; (c) for nonempty `A`, `Ā = {s : ρ(s, A) = 0}`. -/
theorem slp_ex_12_2 (A : Set S) :
    (∀ x y, |Metric.infDist x A - Metric.infDist y A| ≤ dist x y) ∧
      UniformContinuous (fun s => Metric.infDist s A) ∧
      (A.Nonempty → closure A = {s | Metric.infDist s A = 0}) := by
  refine ⟨fun x y => ?_, (Metric.lipschitz_infDist_pt A).uniformContinuous, fun hA => ?_⟩
  · have := (Metric.lipschitz_infDist_pt A).dist_le_mul x y
    rwa [NNReal.coe_one, one_mul, Real.dist_eq] at this
  · ext s; exact Metric.mem_closure_iff_infDist_zero hA

/-- The functions of Lemma 12.1: `fₙ(s) = max(0, 1 − (n + 1) ρ(s, F))`. -/
noncomputable def gp_bump (F : Set S) (n : ℕ) (s : S) : ℝ :=
  max 0 (1 - (n + 1) * Metric.infDist s F)

theorem gp_continuous_bump (F : Set S) (n : ℕ) : Continuous (gp_bump F n) :=
  continuous_const.max (continuous_const.sub (continuous_const.mul
    (Metric.continuous_infDist_pt F)))

theorem gp_bump_mem (F : Set S) (n : ℕ) (s : S) : 0 ≤ gp_bump F n s ∧ gp_bump F n s ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (by
    have := Metric.infDist_nonneg (x := s) (s := F)
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])⟩

theorem gp_bump_eq_one {F : Set S} {s : S} (hs : s ∈ F) (n : ℕ) : gp_bump F n s = 1 := by
  simp [gp_bump, Metric.infDist_zero_of_mem hs]

theorem gp_bump_antitone (F : Set S) (s : S) : Antitone fun n => gp_bump F n s := fun m n hmn => by
  refine max_le_max le_rfl (sub_le_sub_left (mul_le_mul_of_nonneg_right ?_
    Metric.infDist_nonneg) 1)
  exact_mod_cast Nat.succ_le_succ hmn

/-- `fₙ → 1_F` pointwise for closed nonempty `F`. -/
theorem gp_tendsto_bump {F : Set S} (hF : IsClosed F) (hne : F.Nonempty) (s : S) :
    Tendsto (fun n => gp_bump F n s) atTop (𝓝 (F.indicator 1 s)) := by
  by_cases hs : s ∈ F
  · simp [gp_bump_eq_one hs, indicator_of_mem hs]
  · rw [indicator_of_notMem hs]
    have hpos : 0 < Metric.infDist s F :=
      (hF.notMem_iff_infDist_pos hne).1 hs
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / Metric.infDist s F)
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
    have : 1 ≤ (n + 1) * Metric.infDist s F := by
      rw [div_lt_iff₀ hpos] at hN
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    simp only [gp_bump]
    exact (max_eq_left (by linarith)).symm

variable [MeasurableSpace S] [BorelSpace S]

/-- `λₙ` **converges weakly** to `λ` (p. 354): `∫ f dλₙ → ∫ f dλ` for every bounded continuous
`f`. -/
def ConvWeak (ls : ℕ → Measure S) (l : Measure S) : Prop :=
  ∀ f : S →ᵇ ℝ, Tendsto (fun n => ∫ s, f s ∂ls n) atTop (𝓝 (∫ s, f s ∂l))

/-- **Lemma 12.1.** For a closed set `F` there are continuous `fₙ`, decreasing in `n`, with
`fₙ = 1` on `F`, `0 ≤ fₙ ≤ 1`, and `∫ fₙ dλ → λ(F)` for every probability measure `λ`. -/
theorem slp_lemma_12_1 {F : Set S} (hF : IsClosed F) :
    ∃ f : ℕ → S → ℝ, (∀ n, Continuous (f n)) ∧ (∀ s, Antitone fun n => f n s) ∧
      (∀ n, ∀ s ∈ F, f n s = 1) ∧ (∀ n s, 0 ≤ f n s ∧ f n s ≤ 1) ∧
      ∀ (μ : Measure S) [IsProbabilityMeasure μ],
        Tendsto (fun n => ∫ s, f n s ∂μ) atTop (𝓝 (μ.real F)) := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ _ => 0, fun _ => continuous_const, fun _ _ _ _ => le_rfl, fun _ s hs => hs.elim,
      fun _ _ => ⟨le_rfl, zero_le_one⟩, fun μ _ => by simp⟩
  refine ⟨gp_bump F, gp_continuous_bump F, gp_bump_antitone F, fun n s hs => gp_bump_eq_one hs n,
    gp_bump_mem F, fun μ _ => ?_⟩
  have hlim := tendsto_integral_of_dominated_convergence (μ := μ) (F := gp_bump F)
    (f := F.indicator 1) (fun _ => 1)
    (fun n => (gp_continuous_bump F n).aestronglyMeasurable) (integrable_const 1)
    (fun n => Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (gp_bump_mem F n s).1]; exact (gp_bump_mem F n s).2)
    (Eventually.of_forall fun s => gp_tendsto_bump hF hne s)
  rwa [integral_indicator_one hF.measurableSet] at hlim

/-- For `0 ≤ g < 1` and `m = #{1 ≤ i ≤ k : i/k ≤ g}`: `m/k ≤ g < (m + 1)/k`. -/
theorem gp_count_bounds {k : ℕ} (hk : 1 ≤ k) {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g < 1) :
    (((Finset.Icc 1 k).filter fun i : ℕ => (i : ℝ) / k ≤ g).card : ℝ) / k ≤ g ∧
      g < (((Finset.Icc 1 k).filter fun i : ℕ => (i : ℝ) / k ≤ g).card + 1 : ℝ) / k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hkg : 0 ≤ k * g := mul_nonneg hk'.le hg0
  have hfloor : ⌊(k : ℝ) * g⌋₊ ≤ k := by
    have : (k : ℝ) * g < k := by nlinarith
    exact_mod_cast (Nat.floor_le hkg).trans this.le
  have hset : ((Finset.Icc 1 k).filter fun i : ℕ => (i : ℝ) / k ≤ g) =
      Finset.Icc 1 ⌊(k : ℝ) * g⌋₊ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc]
    rw [div_le_iff₀ hk', mul_comm g, ← Nat.le_floor_iff hkg]
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3.trans hfloor⟩, h3⟩
  rw [hset, Nat.card_Icc, Nat.add_sub_cancel]
  constructor
  · rw [div_le_iff₀ hk']; have := Nat.floor_le hkg; linarith [mul_comm (k : ℝ) g]
  · rw [lt_div_iff₀ hk', mul_comm]; exact Nat.lt_floor_add_one _

omit [BorelSpace S] in
/-- **Lemma 12.2.** For measurable `f` with `a ≤ f < b`, `c = b − a`, and `ε > 0`, there are `k ≥ 1`
and sets `Fᵢ = {f ≥ a + ic/k}`, `1 ≤ i ≤ k`, independent of `μ`, with
`a + (c/k) Σ μ(Fᵢ) ≤ ∫ f dμ ≤ a + (c/k) Σ μ(Fᵢ) + ε` for every probability `μ`. If `f` is
continuous the `Fᵢ` are closed. -/
theorem slp_lemma_12_2 {f : S → ℝ} (hf : Measurable f) {a b : ℝ} (hab : ∀ s, a ≤ f s ∧ f s < b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ F : ℕ → Set S, (∀ i, MeasurableSet (F i)) ∧
      (Continuous f → ∀ i, IsClosed (F i)) ∧
      ∀ (μ : Measure S) [IsProbabilityMeasure μ],
        a + (b - a) / k * ∑ i ∈ Finset.Icc 1 k, μ.real (F i) ≤ ∫ s, f s ∂μ ∧
          ∫ s, f s ∂μ ≤ a + (b - a) / k * ∑ i ∈ Finset.Icc 1 k, μ.real (F i) + ε := by
  set k := ⌈(b - a) / ε⌉₊ + 1
  have hk : 1 ≤ k := Nat.le_add_left 1 _
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set F : ℕ → Set S := fun i => {s | a + (b - a) * i / k ≤ f s}
  refine ⟨k, hk, F, fun i => measurableSet_le measurable_const hf,
    fun hc i => isClosed_le continuous_const hc, fun μ _ => ?_⟩
  obtain ⟨s₀⟩ := nonempty_of_isProbabilityMeasure μ
  have hba : 0 < b - a := by have := hab s₀; linarith
  have hck : (b - a) / k ≤ ε := by
    rw [div_le_iff₀ hk']
    have := Nat.le_ceil ((b - a) / ε)
    rw [div_le_iff₀ hε] at this
    have : (⌈(b - a) / ε⌉₊ : ℝ) ≤ k := by simp [k]
    nlinarith
  -- the pointwise inequality, with `g = (f − a)/(b − a)`
  set cnt : S → ℝ := fun s => ∑ i ∈ Finset.Icc 1 k, (F i).indicator 1 s
  have hcnt : ∀ s, cnt s = (((Finset.Icc 1 k).filter fun i : ℕ =>
      (i : ℝ) / k ≤ (f s - a) / (b - a)).card : ℝ) := fun s => by
    simp only [cnt, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : a + (b - a) * i / k ≤ f s ↔ (i : ℝ) / k ≤ (f s - a) / (b - a) := by
      have e : (b - a) * (i : ℝ) / k = (i : ℝ) / k * (b - a) := by ring
      rw [le_div_iff₀ hba, ← e]; constructor <;> intro h <;> linarith
    by_cases h : a + (b - a) * i / k ≤ f s
    · have hm : s ∈ F i := h
      simp [Set.indicator_of_mem hm, this.1 h]
    · have hm : s ∉ F i := h
      have h2 : ¬ ((i : ℝ) / k ≤ (f s - a) / (b - a)) := fun h' => h (this.2 h')
      simp [Set.indicator_of_notMem hm, h2]
  have hpt : ∀ s, (b - a) / k * cnt s ≤ f s - a ∧ f s - a ≤ (b - a) / k * cnt s + (b - a) / k := by
    intro s
    obtain ⟨h1, h2⟩ := hab s
    obtain ⟨c1, c2⟩ := gp_count_bounds hk (g := (f s - a) / (b - a)) (div_nonneg (by linarith)
        hba.le)
      ((div_lt_one hba).2 (by linarith))
    rw [hcnt]
    constructor
    · calc (b - a) / k * _ = (b - a) * (_ / k) := by ring
        _ ≤ (b - a) * ((f s - a) / (b - a)) := mul_le_mul_of_nonneg_left c1 hba.le
        _ = f s - a := by field_simp
    · calc f s - a = (b - a) * ((f s - a) / (b - a)) := by field_simp
        _ ≤ (b - a) * ((_ + 1) / k) := mul_le_mul_of_nonneg_left c2.le hba.le
        _ = _ := by ring
  have hfi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable (|a| + |b|)
    (Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_le]; obtain ⟨h1, h2⟩ := hab s
      constructor <;> linarith [abs_nonneg a, abs_nonneg b, neg_abs_le a, le_abs_self b])
  have hci : Integrable cnt μ := integrable_finsetSum _ fun i _ =>
    (integrable_const 1).indicator (measurableSet_le measurable_const hf)
  have hint_cnt : ∫ s, cnt s ∂μ = ∑ i ∈ Finset.Icc 1 k, μ.real (F i) := by
    rw [integral_finsetSum _ fun i _ => (integrable_const 1).indicator
      (measurableSet_le measurable_const hf)]
    exact Finset.sum_congr rfl fun i _ => integral_indicator_one
      (measurableSet_le measurable_const hf)
  have hfa : Integrable (fun s => f s - a) μ := hfi.sub (integrable_const a)
  have hca : Integrable (fun s => (b - a) / k * cnt s + (b - a) / k) μ :=
    (hci.const_mul _).add (integrable_const _)
  have hlo := integral_mono (hci.const_mul ((b - a) / k)) hfa fun s => (hpt s).1
  have hhi := integral_mono hfa hca fun s => (hpt s).2
  rw [integral_const_mul, hint_cnt, integral_sub hfi (integrable_const a)] at hlo
  rw [integral_add (hci.const_mul _) (integrable_const _), integral_const_mul, hint_cnt,
    integral_sub hfi (integrable_const a)] at hhi
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hlo hhi
  constructor <;> linarith

end Miao.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Characterizations of weak convergence

Copied from `RecursiveMethods/WeakConvergence` (SLP Chapter 12, module `Portmanteau.lean`), with the
namespace renamed to `Miao.MarkovProcesses`, the results numbered in SLP prefixed
`slp_` and the helper lemmas and definitions prefixed `gp_`.

SLP §12.1, Theorem 12.3, pp. 358–360. For probability measures `λₙ`, `λ` on a metric space the
following are equivalent (`slp_theorem_12_3`):

* (a) `λₙ ⇒ λ`;
* (b) `limsup λₙ(F) ≤ λ(F)` for closed `F`;
* (c) `liminf λₙ(G) ≥ λ(G)` for open `G`;
* (d) `λₙ(A) → λ(A)` whenever `λ(∂A) = 0`.

`limsup ≤` and `liminf ≥` are written as: for every `ε > 0`, eventually `λₙ(F) < λ(F) + ε`
(`gp_LimsupLe`), respectively `λₙ(G) > λ(G) − ε`. The proofs follow the book: (a) ⇒ (b) by
Lemma 12.1, (b) ⇒ (a) by Lemma 12.2, (b) ⇔ (c) by complements, (b) ⇒ (d) through the interior and
the closure, and (d) ⇒ (b) through thickenings with null boundaries.
-/

namespace Miao.MarkovProcesses

open MeasureTheory Filter Topology Set BoundedContinuousFunction

variable {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]

/-- `limsup uₙ ≤ c`, written without `limsup`. -/
def gp_LimsupLe (u : ℕ → ℝ) (c : ℝ) : Prop := ∀ ε > 0, ∀ᶠ n in atTop, u n < c + ε

/-- `liminf uₙ ≥ c`, written without `liminf`. -/
def gp_LiminfGe (u : ℕ → ℝ) (c : ℝ) : Prop := ∀ ε > 0, ∀ᶠ n in atTop, c - ε < u n

theorem gp_tendsto_of_limsup_liminf {u : ℕ → ℝ} {c : ℝ} (h1 : gp_LimsupLe u c) (h2 : gp_LiminfGe u
    c) :
    Tendsto u atTop (𝓝 c) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [h2 (c - a) (by linarith)] with n hn; linarith
  · filter_upwards [h1 (a - c) (by linarith)] with n hn; linarith

/-- A continuous function with values in `[0, 1]` as a bounded continuous function. -/
noncomputable def gp_toBCF {f : S → ℝ} (hc : Continuous f) (h : ∀ s, 0 ≤ f s ∧ f s ≤ 1) : S →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨f, hc⟩ 1 fun x y => by
    simp only [ContinuousMap.coe_mk, Real.dist_eq]
    rw [abs_le]; constructor <;> linarith [h x, h y]

/-- (a) ⇒ (b). -/
theorem gp_limsup_closed_of_weak {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l] (h : ConvWeak ls l) {F : Set S}
    (hF : IsClosed F) : gp_LimsupLe (fun n => (ls n).real F) (l.real F) := by
  intro ε hε
  obtain ⟨f, hc, -, h1, h01, hlim⟩ := slp_lemma_12_1 hF
  obtain ⟨m, hm⟩ := ((hlim l).eventually (gt_mem_nhds (show l.real F < l.real F + ε / 2 by
    linarith))).exists
  set g := gp_toBCF (hc m) (h01 m)
  have hint : ∀ (μ : Measure S) [IsProbabilityMeasure μ], μ.real F ≤ ∫ s, g s ∂μ := by
    intro μ _
    rw [← integral_indicator_one hF.measurableSet]
    refine integral_mono (integrable_const (1 : ℝ) |>.indicator hF.measurableSet)
      (g.integrable μ) fun s => ?_
    by_cases hs : s ∈ F
    · simp [indicator_of_mem hs, g, gp_toBCF, h1 m s hs]
    · simp [indicator_of_notMem hs, g, gp_toBCF, (h01 m s).1]
  filter_upwards [(h g).eventually (gt_mem_nhds (show ∫ s, g s ∂l < l.real F + ε by
    change ∫ s, f m s ∂l < _; linarith))] with n hn
  exact (hint (ls n)).trans_lt hn

/-- The upper half of (b) ⇒ (a), through Lemma 12.2. -/
theorem gp_limsup_integral_of_closed {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l]
    (hb : ∀ F, IsClosed F → gp_LimsupLe (fun n => (ls n).real F) (l.real F)) (g : S →ᵇ ℝ) :
    gp_LimsupLe (fun n => ∫ s, g s ∂ls n) (∫ s, g s ∂l) := by
  intro ε hε
  set a := -‖g‖ - 1
  set b := ‖g‖ + 1
  have hab : ∀ s, a ≤ g s ∧ g s < b := fun s => by
    have := abs_le.1 ((Real.norm_eq_abs _).symm ▸ g.norm_coe_le_norm s)
    constructor <;> linarith
  have hc : 0 < b - a := by simp only [a, b]; linarith [norm_nonneg g]
  obtain ⟨k, hk, F, -, hFc, hF⟩ :=
    slp_lemma_12_2 g.continuous.measurable hab (ε := ε / 3) (by positivity)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set δ := ε / (3 * (b - a))
  have hδ : 0 < δ := by positivity
  have hev : ∀ᶠ n in atTop, ∀ i ∈ Finset.Icc 1 k, (ls n).real (F i) < l.real (F i) + δ :=
    (Filter.eventually_all_finset _).2 fun i _ => hb (F i) (hFc g.continuous i) δ hδ
  filter_upwards [hev] with n hn
  obtain ⟨-, hup⟩ := hF (ls n)
  obtain ⟨hlo, -⟩ := hF l
  have hsum : ∑ i ∈ Finset.Icc 1 k, (ls n).real (F i) ≤
      ∑ i ∈ Finset.Icc 1 k, l.real (F i) + k * δ := by
    calc _ ≤ ∑ i ∈ Finset.Icc 1 k, (l.real (F i) + δ) :=
          Finset.sum_le_sum fun i hi => (hn i hi).le
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
  have hkδ : (b - a) / k * (k * δ) = ε / 3 := by
    simp only [δ]; field_simp
  have := mul_le_mul_of_nonneg_left hsum (div_nonneg hc.le hk'.le)
  rw [mul_add, hkδ] at this
  linarith

/-- (b) ⇒ (a). -/
theorem gp_weak_of_limsup_closed {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l]
    (hb : ∀ F, IsClosed F → gp_LimsupLe (fun n => (ls n).real F) (l.real F)) : ConvWeak ls l := by
  intro g
  refine gp_tendsto_of_limsup_liminf (gp_limsup_integral_of_closed hb g) fun ε hε => ?_
  filter_upwards [gp_limsup_integral_of_closed hb (-g) ε hε] with n hn
  simp only [BoundedContinuousFunction.coe_neg, Pi.neg_apply, integral_neg] at hn
  linarith

/-- (b) ⇒ (c), by complements. -/
theorem gp_liminf_open_of_limsup_closed {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l]
    (hb : ∀ F, IsClosed F → gp_LimsupLe (fun n => (ls n).real F) (l.real F)) {G : Set S}
    (hG : IsOpen G) : gp_LiminfGe (fun n => (ls n).real G) (l.real G) := by
  intro ε hε
  filter_upwards [hb Gᶜ hG.isClosed_compl ε hε] with n hn
  rw [probReal_compl_eq_one_sub hG.measurableSet,
    probReal_compl_eq_one_sub hG.measurableSet] at hn
  linarith

/-- (c) ⇒ (b), by complements. -/
theorem gp_limsup_closed_of_liminf_open {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l]
    (hc : ∀ G, IsOpen G → gp_LiminfGe (fun n => (ls n).real G) (l.real G)) {F : Set S}
    (hF : IsClosed F) : gp_LimsupLe (fun n => (ls n).real F) (l.real F) := by
  intro ε hε
  filter_upwards [hc Fᶜ hF.isOpen_compl ε hε] with n hn
  rw [probReal_compl_eq_one_sub hF.measurableSet,
    probReal_compl_eq_one_sub hF.measurableSet] at hn
  linarith

/-- (b) ⇒ (d): `λ(Å) = λ(A) = λ(Ā)` when `λ(∂A) = 0`. -/
theorem gp_tendsto_of_null_frontier {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l]
    (hb : ∀ F, IsClosed F → gp_LimsupLe (fun n => (ls n).real F) (l.real F)) {A : Set S}
    (h0 : l (frontier A) = 0) :
    Tendsto (fun n => (ls n).real A) atTop (𝓝 (l.real A)) := by
  have hcl : l.real (closure A) ≤ l.real (interior A) := by
    rw [closure_eq_interior_union_frontier]
    refine (measureReal_union_le _ _).trans ?_
    rw [measureReal_def (s := frontier A), h0, ENNReal.toReal_zero, add_zero]
  have h1 : l.real (interior A) ≤ l.real A := measureReal_mono interior_subset
  have h2 : l.real A ≤ l.real (closure A) := measureReal_mono subset_closure
  refine gp_tendsto_of_limsup_liminf (fun ε hε => ?_) (fun ε hε => ?_)
  · filter_upwards [hb _ isClosed_closure ε hε] with n hn
    have := measureReal_mono (μ := ls n) (subset_closure (s := A))
    linarith
  · filter_upwards [gp_liminf_open_of_limsup_closed hb isOpen_interior ε hε] with n hn
    have := measureReal_mono (μ := ls n) (interior_subset (s := A))
    linarith

/-- (d) ⇒ (b), through thickenings `{ρ(·, F) < r}` with null boundaries. -/
theorem gp_limsup_closed_of_null_frontier {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l]
    (hd : ∀ A, MeasurableSet A → l (frontier A) = 0 →
      Tendsto (fun n => (ls n).real A) atTop (𝓝 (l.real A))) {F : Set S} (hF : IsClosed F) :
    gp_LimsupLe (fun n => (ls n).real F) (l.real F) := by
  intro ε hε
  obtain ⟨rs, hrs, hpos⟩ := exists_null_frontiers_thickening l F
  have hlim :=
    tendsto_measure_thickening_of_isClosed (μ := l) ⟨1, one_pos, measure_ne_top _ _⟩ hF
  have hrs' : Tendsto rs atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hrs, Eventually.of_forall fun n => (hpos n).1⟩
  have hlim' : Tendsto (fun n => l.real (Metric.thickening (rs n) F)) atTop (𝓝 (l.real F)) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (hlim.comp hrs')
  obtain ⟨m, hm⟩ := (hlim'.eventually (gt_mem_nhds (show l.real F < l.real F + ε / 2 by
    linarith))).exists
  have hA := hd _ Metric.isOpen_thickening.measurableSet (hpos m).2
  filter_upwards [hA.eventually (gt_mem_nhds (show l.real (Metric.thickening (rs m) F) <
    l.real (Metric.thickening (rs m) F) + ε / 2 by linarith))] with n hn
  have := measureReal_mono (μ := ls n) (Metric.self_subset_thickening (hpos m).1 F)
  linarith

/-- **Theorem 12.3.** For probability measures on a metric space, the following are equivalent:
(a) `λₙ ⇒ λ`; (b) `limsup λₙ(F) ≤ λ(F)` for closed `F`; (c) `liminf λₙ(G) ≥ λ(G)` for open
`G`; (d) `λₙ(A) → λ(A)` whenever `λ(∂A) = 0`. -/
theorem slp_theorem_12_3 (ls : ℕ → Measure S) (l : Measure S) [∀ n, IsProbabilityMeasure (ls n)]
    [IsProbabilityMeasure l] :
    (ConvWeak ls l ↔ ∀ F, IsClosed F → gp_LimsupLe (fun n => (ls n).real F) (l.real F)) ∧
      (ConvWeak ls l ↔ ∀ G, IsOpen G → gp_LiminfGe (fun n => (ls n).real G) (l.real G)) ∧
      (ConvWeak ls l ↔ ∀ A, MeasurableSet A → l (frontier A) = 0 →
        Tendsto (fun n => (ls n).real A) atTop (𝓝 (l.real A))) := by
  refine ⟨⟨fun h F hF => gp_limsup_closed_of_weak h hF, gp_weak_of_limsup_closed⟩, ⟨fun h G hG =>
    gp_liminf_open_of_limsup_closed (fun F hF => gp_limsup_closed_of_weak h hF) hG,
    fun hc => gp_weak_of_limsup_closed fun F hF => gp_limsup_closed_of_liminf_open hc hF⟩,
    ⟨fun h A _ h0 => gp_tendsto_of_null_frontier (fun F hF => gp_limsup_closed_of_weak h hF) h0,
    fun hd => gp_weak_of_limsup_closed fun F hF => gp_limsup_closed_of_null_frontier hd hF⟩⟩

end Miao.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Convergence-determining families and uniqueness

Copied from `RecursiveMethods/WeakConvergence` (SLP Chapter 12, module `Determining.lean`), with the
namespace renamed to `Miao.MarkovProcesses`, the results numbered in SLP prefixed
`slp_` and the helper lemmas and definitions prefixed `gp_`.

SLP §12.1, Theorems 12.4–12.6 and their corollaries, pp. 360–364.

* **Theorem 12.4** (`slp_theorem_12_4`): if `𝒜` is closed under finite intersections and every open
  set is a countable union of members of `𝒜`, then `λₙ(A) → λ(A)` on `𝒜` gives `λₙ ⇒ λ`.
  Finite unions converge by inclusion–exclusion (`gp_tendsto_finite_union`), and then condition (c)
  of Theorem 12.3 holds.
* **Theorem 12.5** (`slp_theorem_12_5`): in a second countable metric space, it suffices that every
  ball `b(x, ε)` contain some `A ∈ 𝒜` with `x ∈ Å`. The book takes `S` a Borel subset of `ℝˡ`;
  every subset of `ℝˡ` is second countable, so the theorem applies to it.
* **Corollary** (`slp_theorem_12_5_cor`): finite intersections of open balls with `λ`-null
  boundaries form a convergence-determining class (`gp_IsConvDetermining`).
* **Theorem 12.6** (`slp_theorem_12_6`): every Borel set lies between a closed and an open set whose
  measures differ by less than `ε`. Proved from Mathlib's regularity of finite measures on
  metric spaces.
* **Corollaries 1–2** (`slp_theorem_12_6_cor1`, `slp_theorem_12_6_cor2`): two probability measures
  that
  agree on closed sets, or on integrals of bounded continuous functions, are equal; so weak
  limits are unique (`gp_convWeak_unique`), and a convergence-determining class determines measures
  (`gp_IsConvDetermining.eq`, the book's "(Why?)" on p. 362).
-/

namespace Miao.MarkovProcesses

open MeasureTheory Filter Topology Set BoundedContinuousFunction

variable {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]

omit [MetricSpace S] [BorelSpace S] in
/-- Finite unions `⋃_{j<m} Aⱼ` of members of `𝒜` converge, by inclusion–exclusion. -/
theorem gp_tendsto_finite_union {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l] {𝒜 : Set (Set S)}
    (hmeas : ∀ A ∈ 𝒜, MeasurableSet A) (hinter : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ∩ B ∈ 𝒜)
    (h : ∀ A ∈ 𝒜, Tendsto (fun n => (ls n).real A) atTop (𝓝 (l.real A))) :
    ∀ m (A : ℕ → Set S), (∀ i, A i ∈ 𝒜) →
      Tendsto (fun n => (ls n).real (⋃ j ∈ Finset.range m, A j)) atTop
        (𝓝 (l.real (⋃ j ∈ Finset.range m, A j))) := by
  intro m
  induction m with
  | zero => intro A _; simp
  | succ m ih =>
    intro A hA
    have hU : (⋃ j ∈ Finset.range (m + 1), A j) = (⋃ j ∈ Finset.range m, A j) ∪ A m := by
      rw [Finset.range_add_one, Finset.set_biUnion_insert, union_comm]
    have hI : (⋃ j ∈ Finset.range m, A j) ∩ A m = ⋃ j ∈ Finset.range m, (A j ∩ A m) := by
      rw [iUnion₂_inter]
    have hmU : MeasurableSet (⋃ j ∈ Finset.range m, A j) :=
      Finset.measurableSet_biUnion _ fun j _ => hmeas _ (hA j)
    have key : ∀ (μ : Measure S) [IsProbabilityMeasure μ],
        μ.real (⋃ j ∈ Finset.range (m + 1), A j) = μ.real (⋃ j ∈ Finset.range m, A j) +
          μ.real (A m) - μ.real (⋃ j ∈ Finset.range m, (A j ∩ A m)) := by
      intro μ _
      rw [hU, ← hI]
      have := measureReal_union_add_inter (μ := μ) (s := ⋃ j ∈ Finset.range m, A j)
        (hmeas _ (hA m)) (measure_ne_top μ _) (measure_ne_top μ _)
      linarith
    simp_rw [key]
    exact ((ih A hA).add (h _ (hA m))).sub
      (ih (fun j => A j ∩ A m) fun j => hinter _ (hA j) _ (hA m))

/-- **Theorem 12.4.** If `𝒜` is closed under finite intersections and every open set is a
countable union of members of `𝒜`, then `λₙ(A) → λ(A)` for all `A ∈ 𝒜` implies `λₙ ⇒ λ`. -/
theorem slp_theorem_12_4 {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l] {𝒜 : Set (Set S)}
    (hmeas : ∀ A ∈ 𝒜, MeasurableSet A) (hinter : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ∩ B ∈ 𝒜)
    (hopen : ∀ G, IsOpen G → ∃ T : Set (Set S), T.Countable ∧ T ⊆ 𝒜 ∧ ⋃₀ T = G)
    (h : ∀ A ∈ 𝒜, Tendsto (fun n => (ls n).real A) atTop (𝓝 (l.real A))) : ConvWeak ls l := by
  refine (slp_theorem_12_3 ls l).2.1.2 fun G hG ε hε => ?_
  obtain ⟨T, hTc, hT𝒜, hTG⟩ := hopen G hG
  rcases T.eq_empty_or_nonempty with rfl | hTne
  · rw [sUnion_empty] at hTG
    subst hTG
    exact Eventually.of_forall fun n => by simp; linarith
  obtain ⟨A, hAeq⟩ := hTc.exists_eq_range hTne
  have hA : ∀ i, A i ∈ 𝒜 := fun i => hT𝒜 (hAeq ▸ mem_range_self i)
  have hGA : G = ⋃ i, A i := by rw [← hTG, hAeq, sUnion_range]
  -- continuity from below
  set U : ℕ → Set S := fun m => ⋃ j ∈ Finset.range m, A j
  have hmono : Monotone U := fun m m' hmm' => biUnion_subset_biUnion_left
    (Finset.coe_subset.2 (Finset.range_subset_range.2 hmm'))
  have hUG : (⋃ m, U m) = G := by
    rw [hGA]
    ext x
    simp only [U, mem_iUnion, Finset.mem_range]
    exact ⟨fun ⟨_, j, _, hj⟩ => ⟨j, hj⟩, fun ⟨j, hj⟩ => ⟨j + 1, j, by omega, hj⟩⟩
  have hlim : Tendsto (fun m => l.real (U m)) atTop (𝓝 (l.real G)) := by
    have := tendsto_measure_iUnion_atTop (μ := l) hmono
    rw [hUG] at this
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp this
  obtain ⟨m, hm⟩ := (hlim.eventually (lt_mem_nhds (show l.real G - ε / 2 < l.real G by
    linarith))).exists
  filter_upwards [(gp_tendsto_finite_union hmeas hinter h m A hA).eventually
    (lt_mem_nhds (show l.real (U m) - ε / 2 < l.real (U m) by linarith))] with n hn
  have := measureReal_mono (μ := ls n) (show U m ⊆ G from hUG ▸ subset_iUnion U m)
  simp only [U] at hn hm this
  linarith

/-- **Theorem 12.5.** In a second countable metric space (for instance any Borel `S ⊆ ℝˡ`), if
`𝒜` is closed under finite intersections and every ball `b(x, ε)` contains some `A ∈ 𝒜` with
`x ∈ Å`, then `λₙ(A) → λ(A)` for all `A ∈ 𝒜` implies `λₙ ⇒ λ`. -/
theorem slp_theorem_12_5 [SecondCountableTopology S] {ls : ℕ → Measure S} {l : Measure S}
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l] {𝒜 : Set (Set S)}
    (hmeas : ∀ A ∈ 𝒜, MeasurableSet A) (hinter : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ∩ B ∈ 𝒜)
    (hball : ∀ x, ∀ ε > 0, ∃ A ∈ 𝒜, x ∈ interior A ∧ A ⊆ Metric.ball x ε)
    (h : ∀ A ∈ 𝒜, Tendsto (fun n => (ls n).real A) atTop (𝓝 (l.real A))) : ConvWeak ls l := by
  refine slp_theorem_12_4 hmeas hinter (fun G hG => ?_) h
  -- for `x ∈ G` choose `Aₓ ∈ 𝒜` with `x ∈ Åₓ ⊆ Aₓ ⊆ G`
  have hx : ∀ x : G, ∃ A ∈ 𝒜, (x : S) ∈ interior A ∧ A ⊆ G := fun x => by
    obtain ⟨ε, hε, hεG⟩ := Metric.isOpen_iff.1 hG x x.2
    obtain ⟨A, hA, hxA, hAb⟩ := hball x ε hε
    exact ⟨A, hA, hxA, hAb.trans hεG⟩
  choose A hA hxA hAG using hx
  obtain ⟨T, hTc, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable (fun x : G => interior (A x))
    fun _ => isOpen_interior
  have hcover : (⋃ x : G, interior (A x)) = G := by
    refine subset_antisymm (iUnion_subset fun x => interior_subset.trans (hAG x)) fun y hy => ?_
    exact mem_iUnion.2 ⟨⟨y, hy⟩, hxA ⟨y, hy⟩⟩
  refine ⟨A '' T, hTc.image A, image_subset_iff.2 fun x _ => hA x, subset_antisymm ?_ ?_⟩
  · exact sUnion_subset fun _ ⟨x, _, hx⟩ => hx ▸ hAG x
  · intro y hy
    rw [← hcover, ← hTeq] at hy
    obtain ⟨x, hxT, hyx⟩ := mem_iUnion₂.1 hy
    exact ⟨A x, ⟨x, hxT, rfl⟩, interior_subset hyx⟩

/-- `𝒜` is a **convergence-determining class** (p. 362): `λₙ(A) → λ(A)` for all `A ∈ 𝒜` with
`λ(∂A) = 0` implies `λₙ ⇒ λ`. -/
def gp_IsConvDetermining (𝒜 : Set (Set S)) : Prop :=
  ∀ (ls : ℕ → Measure S) (l : Measure S), (∀ n, IsProbabilityMeasure (ls n)) →
    IsProbabilityMeasure l →
      (∀ A ∈ 𝒜, l (frontier A) = 0 → Tendsto (fun n => (ls n).real A) atTop (𝓝 (l.real A))) →
        ConvWeak ls l

omit [MeasurableSpace S] [BorelSpace S] in
/-- The boundary of a finite intersection lies in the union of the boundaries. -/
theorem gp_frontier_iInter_fin_subset {m : ℕ} (s : Fin m → Set S) :
    frontier (⋂ i, s i) ⊆ ⋃ i, frontier (s i) := by
  intro x hx
  rw [frontier, interior_iInter_of_finite] at hx
  obtain ⟨hcl, hint⟩ := hx
  simp only [mem_iInter, not_forall] at hint
  obtain ⟨i, hi⟩ := hint
  exact mem_iUnion.2 ⟨i, closure_mono (iInter_subset s i) hcl, hi⟩

/-- Finite intersections of open balls. -/
def gp_ballInters (S : Type*) [MetricSpace S] : Set (Set S) :=
  {A | ∃ m, ∃ c : Fin m → S, ∃ r : Fin m → ℝ, A = ⋂ i, Metric.ball (c i) (r i)}

/-- **Corollary to Theorem 12.5.** In a second countable metric space, finite intersections of
open balls form a convergence-determining class. -/
theorem slp_theorem_12_5_cor [SecondCountableTopology S] : gp_IsConvDetermining (gp_ballInters S)
    := by
  intro ls l _ _ h
  -- the finite intersections of balls whose boundaries are `λ`-null
  set 𝒜 : Set (Set S) := {A | ∃ m, ∃ c : Fin m → S, ∃ r : Fin m → ℝ,
    (∀ i, l (frontier (Metric.ball (c i) (r i))) = 0) ∧ A = ⋂ i, Metric.ball (c i) (r i)}
  have hfr : ∀ A ∈ 𝒜, l (frontier A) = 0 := by
    rintro A ⟨m, c, r, hnull, rfl⟩
    refine measure_mono_null (gp_frontier_iInter_fin_subset _) ?_
    exact measure_iUnion_null hnull
  refine slp_theorem_12_5 (𝒜 := 𝒜) (fun A ⟨m, c, r, _, hA⟩ => hA ▸
    MeasurableSet.iInter fun i => Metric.isOpen_ball.measurableSet) ?_ ?_
    (fun A hA => h A (by obtain ⟨m, c, r, -, hA⟩ := hA; exact ⟨m, c, r, hA⟩) (hfr A hA))
  · rintro A ⟨m, c, r, hn, rfl⟩ B ⟨m', c', r', hn', rfl⟩
    refine ⟨m + m', Fin.append c c', Fin.append r r', fun i => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa using hn i
      · simpa using hn' i
    · ext x
      simp only [mem_inter_iff, mem_iInter]
      constructor
      · rintro ⟨h1, h2⟩ i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · simpa using h1 i
        · simpa using h2 i
      · intro h
        exact ⟨fun i => by simpa using h (Fin.castAdd m' i),
          fun i => by simpa using h (Fin.natAdd m i)⟩
  · intro x ε hε
    obtain ⟨rs, hrs, hpos⟩ := exists_null_frontiers_thickening l {x}
    obtain ⟨n, hn⟩ := (hrs.eventually (gt_mem_nhds hε)).exists
    refine ⟨Metric.ball x (rs n), ⟨1, fun _ => x, fun _ => rs n, fun _ => ?_, ?_⟩, ?_,
      Metric.ball_subset_ball hn.le⟩
    · simpa [Metric.thickening_singleton] using (hpos n).2
    · ext y; simp
    · rw [Metric.isOpen_ball.interior_eq]; exact Metric.mem_ball_self (hpos n).1

/-- **Theorem 12.6.** For a probability measure on a metric space, every Borel set `B` lies
between a closed `A` and an open `C` with `λ(C) − λ(A) < ε`. -/
theorem slp_theorem_12_6 (l : Measure S) [IsProbabilityMeasure l] {B : Set S} (hB : MeasurableSet B)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A C, IsClosed A ∧ IsOpen C ∧ A ⊆ B ∧ B ⊆ C ∧ l.real C - l.real A < ε := by
  have hε2 : (ENNReal.ofReal (ε / 2)) ≠ 0 := by simp [hε]
  obtain ⟨A, hAB, hA, hlt⟩ := hB.exists_isClosed_lt_add (measure_ne_top l B) hε2
  obtain ⟨C, hBC, hC, hCl⟩ := B.exists_isOpen_lt_of_lt (l B + ENNReal.ofReal (ε / 2))
    (ENNReal.lt_add_right (measure_ne_top l B) hε2)
  refine ⟨A, C, hA, hC, hAB, hBC, ?_⟩
  have h1 : l.real B < l.real A + ε / 2 := by
    have := ENNReal.toReal_strict_mono (by finiteness) hlt
    rwa [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity)] at this
  have h2 : l.real C < l.real B + ε / 2 := by
    have := ENNReal.toReal_strict_mono (by finiteness) hCl
    rwa [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity)] at this
  linarith

/-- **Corollary 1 to Theorem 12.6.** Probability measures that agree on closed sets are equal. -/
theorem slp_theorem_12_6_cor1 {l μ : Measure S} [IsProbabilityMeasure l] [IsProbabilityMeasure μ]
    (h : ∀ A, IsClosed A → l A = μ A) : l = μ := by
  have hr : ∀ A, IsClosed A → l.real A = μ.real A := fun A hA => by simp [Measure.real, h A hA]
  have hopen : ∀ C, IsOpen C → l.real C = μ.real C := fun C hC => by
    have := hr Cᶜ hC.isClosed_compl
    rwa [probReal_compl_eq_one_sub hC.measurableSet, probReal_compl_eq_one_sub hC.measurableSet,
      sub_right_inj] at this
  ext B hB
  have hle : ∀ (ν₁ ν₂ : Measure S) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂],
      (∀ A, IsClosed A → ν₁.real A = ν₂.real A) → (∀ C, IsOpen C → ν₁.real C = ν₂.real C) →
        ν₁.real B ≤ ν₂.real B := by
    intro ν₁ ν₂ _ _ hc ho
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨A, C, hA, hC, hAB, hBC, hlt⟩ := slp_theorem_12_6 ν₂ hB hε
    calc ν₁.real B ≤ ν₁.real C := measureReal_mono hBC
      _ = ν₂.real C := ho C hC
      _ < ν₂.real A + ε := by linarith
      _ ≤ ν₂.real B + ε := by linarith [measureReal_mono (μ := ν₂) hAB]
  have h1 := hle l μ hr hopen
  have h2 := hle μ l (fun A hA => (hr A hA).symm) (fun C hC => (hopen C hC).symm)
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1
    (le_antisymm h1 h2)

/-- **Corollary 2 to Theorem 12.6.** Probability measures with the same integrals of all
bounded continuous functions are equal (Lemma 12.1 and Corollary 1). -/
theorem slp_theorem_12_6_cor2 {l μ : Measure S} [IsProbabilityMeasure l] [IsProbabilityMeasure μ]
    (h : ∀ f : S →ᵇ ℝ, ∫ s, f s ∂l = ∫ s, f s ∂μ) : l = μ := by
  refine slp_theorem_12_6_cor1 fun A hA => ?_
  obtain ⟨f, hc, -, -, h01, hlim⟩ := slp_lemma_12_1 hA
  have heq : ∀ n, ∫ s, f n s ∂l = ∫ s, f n s ∂μ := fun n => h (gp_toBCF (hc n) (h01 n))
  have := tendsto_nhds_unique (hlim l) ((hlim μ).congr fun n => (heq n).symm)
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 this

/-- Weak limits are unique (p. 364). -/
theorem gp_convWeak_unique {ls : ℕ → Measure S} {l μ : Measure S} [IsProbabilityMeasure l]
    [IsProbabilityMeasure μ] (h1 : ConvWeak ls l) (h2 : ConvWeak ls μ) : l = μ :=
  slp_theorem_12_6_cor2 fun f => tendsto_nhds_unique (h1 f) (h2 f)

/-- A convergence-determining class determines probability measures (p. 362, "(Why?)"): apply
the definition to the constant sequence `μ`. -/
theorem gp_IsConvDetermining.eq {𝒜 : Set (Set S)} (h𝒜 : gp_IsConvDetermining 𝒜) {l μ : Measure S}
    [IsProbabilityMeasure l] [IsProbabilityMeasure μ] (h : ∀ A ∈ 𝒜, l A = μ A) : l = μ := by
  have hw : ConvWeak (fun _ => μ) l := h𝒜 (fun _ => μ) l (fun _ => inferInstance) inferInstance
    fun A hA _ => by simp [Measure.real, h A hA]
  exact gp_convWeak_unique hw (fun f => tendsto_const_nhds)

end Miao.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Distribution functions on `ℝˡ`

Copied from `RecursiveMethods/WeakConvergence` (SLP Chapter 12, module
`DistributionFunctions.lean`), with the
namespace renamed to `Miao.MarkovProcesses`, the results numbered in SLP prefixed
`slp_` and the helper lemmas and definitions prefixed `gp_`.

SLP §12.2, pp. 364–369. Points of `ℝˡ` are functions `Fin l → ℝ`, ordered coordinatewise. The
distribution function of `λ` is `F(x) = λ((−∞, x])` (`gp_distFun`). The half-open box `(a, b]` is
`∏ᵢ (aᵢ, bᵢ]` (`gp_box`), and for `t ⊆ {1, …, l}` its vertex `a + θₜd` takes `bᵢ` for `i ∈ t` and
`aᵢ` otherwise (`gp_vertex`).

* **Exercise 12.3** (`slp_ex_12_3`): a nondecreasing `F` continuous from above and from below at `x`
  is continuous at `x`.
* **Theorem 12.7a** (`slp_theorem_12_7a`): (D1) `F` is nondecreasing, tends to `0` as any coordinate
  tends to `−∞`, and to `1` as all coordinates tend to `+∞`; (D2) `F` is continuous from above;
  (D3) `Σₜ (−1)^{l − |t|} F(a + θₜd) = λ((a, b]) ≥ 0`. (D3) comes from the identity
  `1_{(a,b]} = ∏ᵢ (1[xᵢ ≤ bᵢ] − 1[xᵢ ≤ aᵢ])`, expanded as a sum over `t`.
* **Theorem 12.7b**, uniqueness (`gp_distFun_injective`): the sets `(−∞, x]` form a π-system
  generating the Borel sets of `ℝˡ`, so `F` determines `λ`. Existence is in
  `MultivariateStieltjes`.
* **Theorem 12.7c** (`slp_theorem_12_7c`): `F` is continuous from below at `x` iff `λ(∂(−∞, x]) =
  0`.
-/

namespace Miao.MarkovProcesses

open MeasureTheory Filter Topology Set

variable {l : ℕ}

/-- The distribution function `F(x) = λ((−∞, x])`. -/
noncomputable def gp_distFun (μ : Measure (Fin l → ℝ)) (x : Fin l → ℝ) : ℝ := μ.real (Iic x)

/-- The half-open box `(a, b] = ∏ᵢ (aᵢ, bᵢ]`. -/
def gp_box (a b : Fin l → ℝ) : Set (Fin l → ℝ) := Set.pi univ fun i => Ioc (a i) (b i)

/-- The vertex of `(a, b]` taking `bᵢ` for `i ∈ t` and `aᵢ` otherwise. -/
def gp_vertex (a b : Fin l → ℝ) (t : Finset (Fin l)) : Fin l → ℝ := fun i => if i ∈ t then b i else
    a i

/-- The alternating vertex sum `Σₜ (−1)^{l − |t|} F(a + θₜd)` of (D3). -/
def gp_vertexSum (F : (Fin l → ℝ) → ℝ) (a b : Fin l → ℝ) : ℝ :=
  ∑ t : Finset (Fin l), (-1 : ℝ) ^ (l - t.card) * F (gp_vertex a b t)

/-- The vector `ε1 = (ε, …, ε)`. -/
def gp_diag (ε : ℝ) : Fin l → ℝ := fun _ => ε

/-- `F` is **continuous from above** at `x`: `F(x + ε1) → F(x)` as `ε ↓ 0`. -/
def gp_ContFromAbove (F : (Fin l → ℝ) → ℝ) (x : Fin l → ℝ) : Prop :=
  Tendsto (fun ε => F (x + gp_diag ε)) (𝓝[>] 0) (𝓝 (F x))

/-- `F` is **continuous from below** at `x`: `F(x − ε1) → F(x)` as `ε ↓ 0`. -/
def gp_ContFromBelow (F : (Fin l → ℝ) → ℝ) (x : Fin l → ℝ) : Prop :=
  Tendsto (fun ε => F (x - gp_diag ε)) (𝓝[>] 0) (𝓝 (F x))

theorem gp_Iic_eq_pi (x : Fin l → ℝ) : Iic x = Set.pi univ fun i => Iic (x i) := by
  ext y; simp [Pi.le_def]

/-- The product expansion: `1_{(a,b]}(y) = Σₜ (−1)^{l − |t|} 1[y ≤ a + θₜd]` for `a ≤ b`. -/
theorem gp_box_indicator_eq {a b : Fin l → ℝ} (hab : a ≤ b) (y : Fin l → ℝ) :
    (gp_box a b).indicator (1 : (Fin l → ℝ) → ℝ) y =
      ∑ t : Finset (Fin l), (-1 : ℝ) ^ (l - t.card) * (Iic (gp_vertex a b t)).indicator 1 y := by
  classical
  -- `1_{(a,b]}(y) = ∏ᵢ (1[yᵢ ≤ bᵢ] − 1[yᵢ ≤ aᵢ])`
  have hprod : (gp_box a b).indicator (1 : (Fin l → ℝ) → ℝ) y =
      ∏ i, ((Iic (b i)).indicator (1 : ℝ → ℝ) (y i) + -(Iic (a i)).indicator 1 (y i)) := by
    by_cases hy : y ∈ gp_box a b
    · rw [indicator_of_mem hy, Pi.one_apply]
      symm
      refine Finset.prod_eq_one fun i _ => ?_
      have hi := hy i (mem_univ i)
      rw [indicator_of_mem (show y i ∈ Iic (b i) from hi.2),
        indicator_of_notMem (show y i ∉ Iic (a i) from fun h => (not_le.2 hi.1) h)]
      simp
    · rw [indicator_of_notMem hy]
      simp only [gp_box, Set.mem_pi, mem_univ, true_implies, not_forall] at hy
      obtain ⟨i, hi⟩ := hy
      symm
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      by_cases h1 : y i ≤ a i
      · rw [indicator_of_mem (show y i ∈ Iic (b i) from h1.trans (hab i)),
          indicator_of_mem (show y i ∈ Iic (a i) from h1)]; simp
      · have h2 : ¬ y i ≤ b i := fun h => hi ⟨not_le.1 h1, h⟩
        rw [indicator_of_notMem (show y i ∉ Iic (b i) from h2),
          indicator_of_notMem (show y i ∉ Iic (a i) from h1)]; simp
  rw [hprod, Finset.prod_add, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.prod_neg, Finset.card_univ_sdiff, Fintype.card_fin]
  -- the product of indicators is the indicator of `(−∞, gp_vertex]`
  have hv : (∏ i ∈ t, (Iic (b i)).indicator (1 : ℝ → ℝ) (y i)) *
      ∏ i ∈ Finset.univ \ t, (Iic (a i)).indicator (1 : ℝ → ℝ) (y i) =
        (Iic (gp_vertex a b t)).indicator 1 y := by
    by_cases hy : y ≤ gp_vertex a b t
    · rw [indicator_of_mem (show y ∈ Iic (gp_vertex a b t) from hy), Pi.one_apply]
      rw [Finset.prod_eq_one fun i hi => ?_, Finset.prod_eq_one fun i hi => ?_, one_mul]
      · have := hy i; simp only [gp_vertex, Finset.mem_sdiff] at this hi
        simp only [hi.2, ↓reduceIte] at this
        rw [indicator_of_mem (show y i ∈ Iic (a i) from this)]; rfl
      · have := hy i; simp only [gp_vertex] at this
        simp only [hi, ↓reduceIte] at this
        rw [indicator_of_mem (show y i ∈ Iic (b i) from this)]; rfl
    · rw [indicator_of_notMem (show y ∉ Iic (gp_vertex a b t) from hy)]
      rw [Pi.le_def] at hy
      push Not at hy
      obtain ⟨i, hi⟩ := hy
      by_cases hit : i ∈ t
      · simp only [gp_vertex, hit, ↓reduceIte] at hi
        rw [Finset.prod_eq_zero hit (indicator_of_notMem (show y i ∉ Iic (b i) from
          not_le.2 hi) _), zero_mul]
      · simp only [gp_vertex, hit, ↓reduceIte] at hi
        rw [Finset.prod_eq_zero (Finset.mem_sdiff.2 ⟨Finset.mem_univ i, hit⟩)
          (indicator_of_notMem (show y i ∉ Iic (a i) from not_le.2 hi) _), mul_zero]
  rw [← hv]
  ring

theorem gp_measurableSet_box (a b : Fin l → ℝ) : MeasurableSet (gp_box a b) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc

/-- (D3): `Σₜ (−1)^{l − |t|} F(a + θₜd) = λ((a, b])`. -/
theorem gp_vertexSum_eq (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ] {a b : Fin l → ℝ}
    (hab : a ≤ b) : gp_vertexSum (gp_distFun μ) a b = μ.real (gp_box a b) := by
  rw [← integral_indicator_one (gp_measurableSet_box a b)]
  simp_rw [gp_box_indicator_eq hab]
  rw [integral_finsetSum _ fun t _ =>
    ((integrable_const 1).indicator measurableSet_Iic).const_mul _]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [integral_const_mul, integral_indicator_one measurableSet_Iic]
  rfl

theorem gp_distFun_mono (μ : Measure (Fin l → ℝ)) [IsFiniteMeasure μ] : Monotone (gp_distFun μ) :=
  fun _ _ hxy => measureReal_mono (Iic_subset_Iic.2 hxy)

/-- Continuity from above of `F`, as a squeeze along `ε ↓ 0`, given decreasing sets whose
measures converge. -/
theorem gp_contFromAbove_distFun (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ]
    (x : Fin l → ℝ) : gp_ContFromAbove (gp_distFun μ) x := by
  set A : ℕ → Set (Fin l → ℝ) := fun n => Iic (x + gp_diag (1 / (n + 1)))
  have hanti : Antitone A := fun m n hmn => Iic_subset_Iic.2 fun i => by
    simp only [Pi.add_apply, gp_diag]
    gcongr
  have hinter : (⋂ n, A n) = Iic x := by
    ext y
    simp only [A, mem_iInter, mem_Iic, Pi.le_def, Pi.add_apply, gp_diag]
    constructor
    · intro h i
      refine le_of_forall_pos_lt_add fun δ hδ => ?_
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
      linarith [h n i]
    · intro h n i
      linarith [h i, show (0 : ℝ) < 1 / (n + 1) by positivity]
  have hlim : Tendsto (fun n => μ.real (A n)) atTop (𝓝 (μ.real (Iic x))) := by
    have := tendsto_measure_iInter_atTop (μ := μ) (fun n => measurableSet_Iic.nullMeasurableSet)
      hanti ⟨0, measure_ne_top _ _⟩
    rw [hinter] at this
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp this
  rw [gp_ContFromAbove, tendsto_order]
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact lt_of_lt_of_le hc (gp_distFun_mono μ fun i => by
      simp only [Pi.add_apply, gp_diag]; linarith [show (0 : ℝ) < ε from hε])
  · obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hc)).exists
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / (n + 1) by positivity)] with ε hε
    exact lt_of_le_of_lt (gp_distFun_mono μ fun i => by
      simp only [Pi.add_apply, gp_diag]; linarith [hε.2]) hn

/-- **Theorem 12.7a.** The distribution function of a probability measure on `ℝˡ` satisfies
(D1): it is nondecreasing, tends to `0` as any coordinate tends to `−∞` and to `1` as all
coordinates tend to `+∞`; (D2): it is continuous from above; and (D3): the alternating vertex
sum over any box is `λ((a, b]) ≥ 0`. -/
theorem slp_theorem_12_7a (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ] :
    (Monotone (gp_distFun μ) ∧
      (∀ i, ∀ ε > 0, ∃ M, ∀ x : Fin l → ℝ, x i ≤ M → gp_distFun μ x < ε) ∧
      (∀ ε > 0, ∃ M, ∀ x : Fin l → ℝ, (∀ i, M ≤ x i) → 1 - ε < gp_distFun μ x)) ∧
      (∀ x, gp_ContFromAbove (gp_distFun μ) x) ∧
      ∀ a b, a ≤ b → gp_vertexSum (gp_distFun μ) a b = μ.real (gp_box a b) ∧
        0 ≤ gp_vertexSum (gp_distFun μ) a b := by
  refine ⟨⟨gp_distFun_mono μ, fun i ε hε => ?_, fun ε hε => ?_⟩, gp_contFromAbove_distFun μ,
    fun a b hab => ⟨gp_vertexSum_eq μ hab, gp_vertexSum_eq μ hab ▸ measureReal_nonneg⟩⟩
  · -- the `i`-th marginal of `(−∞, −n]` tends to `0`
    set A : ℕ → Set (Fin l → ℝ) := fun n => {y | y i ≤ -n}
    have hanti : Antitone A := fun m n hmn y hy => by
      simp only [A, mem_ofPred_eq] at hy ⊢
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith
    have hempty : (⋂ n, A n) = ∅ := by
      ext y
      simp only [A, mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall,
        not_le]
      obtain ⟨n, hn⟩ := exists_nat_gt (-y i)
      exact ⟨n, by linarith⟩
    have hlim := tendsto_measure_iInter_atTop (μ := μ)
      (fun n => (measurableSet_le (measurable_pi_apply i) measurable_const).nullMeasurableSet)
      hanti ⟨0, measure_ne_top _ _⟩
    rw [hempty, measure_empty] at hlim
    have hlim' : Tendsto (fun n => μ.real (A n)) atTop (𝓝 0) := by
      simpa [Function.comp_def, Measure.real] using
        (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
    obtain ⟨n, hn⟩ := (hlim'.eventually (gt_mem_nhds hε)).exists
    refine ⟨-n, fun x hx => lt_of_le_of_lt (measureReal_mono fun y hy => ?_) hn⟩
    exact (hy i).trans hx
  · -- the sets `(−∞, n1]` increase to `ℝˡ`
    set A : ℕ → Set (Fin l → ℝ) := fun n => Iic (gp_diag n)
    have hmono : Monotone A := fun m n hmn => Iic_subset_Iic.2 fun i => by
      simp only [gp_diag]; exact_mod_cast hmn
    have hunion : (⋃ n, A n) = univ := by
      refine eq_univ_of_forall fun y => mem_iUnion.2 ⟨⌈∑ j, |y j|⌉₊, fun i => ?_⟩
      simp only [gp_diag]
      calc y i ≤ |y i| := le_abs_self _
        _ ≤ ∑ j, |y j| := Finset.single_le_sum (f := fun j => |y j|) (fun j _ => abs_nonneg _)
            (Finset.mem_univ i)
        _ ≤ ⌈∑ j, |y j|⌉₊ := Nat.le_ceil _
    have hlim := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hunion, measure_univ] at hlim
    have hlim' : Tendsto (fun n => μ.real (A n)) atTop (𝓝 1) := by
      simpa [Function.comp_def, Measure.real] using
        (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp hlim
    obtain ⟨n, hn⟩ := (hlim'.eventually (lt_mem_nhds (show 1 - ε < 1 by linarith))).exists
    exact ⟨n, fun x hx => lt_of_lt_of_le hn (gp_distFun_mono μ fun i => hx i)⟩

/-- The sets `(−∞, x]` generate the Borel sets of `ℝˡ`. -/
theorem gp_generateFrom_Iic_pi :
    MeasurableSpace.generateFrom (range fun x : Fin l → ℝ => Iic x) =
      (MeasurableSpace.pi : MeasurableSpace (Fin l → ℝ)) := by
  rw [← generateFrom_eq_pi (C := fun _ => range (Iic : ℝ → Set ℝ))
    (fun _ => (borel_eq_generateFrom_Iic ℝ).symm.trans BorelSpace.measurable_eq.symm)
    fun _ => ⟨fun n => Iic (n : ℝ), fun n => mem_range_self _,
      eq_univ_of_forall fun x => mem_iUnion.2 ⟨⌈x⌉₊, Nat.le_ceil x⟩⟩]
  congr 1
  ext A
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨fun i => Iic (x i), fun i _ => ⟨x i, rfl⟩, (gp_Iic_eq_pi x).symm⟩
  · rintro ⟨T, hT, rfl⟩
    choose x hx using fun i => hT i (mem_univ i)
    exact ⟨x, by change Iic x = _; rw [gp_Iic_eq_pi]; congr 1; funext i; exact hx i⟩

/-- **Theorem 12.7b** (uniqueness). A probability measure on `ℝˡ` is determined by its
distribution function. -/
theorem gp_distFun_injective {μ ν : Measure (Fin l → ℝ)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : gp_distFun μ = gp_distFun ν) : μ = ν := by
  refine ext_of_generate_finite _ gp_generateFrom_Iic_pi.symm ?_ ?_ (by simp)
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _
    exact ⟨x ⊓ y, Iic_inter_Iic.symm⟩
  · rintro _ ⟨x, rfl⟩
    have := congrFun h x
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 this

/-- The open lower orthant `{y : y < x}` (all coordinates strictly smaller). -/
def gp_lowerOpen (x : Fin l → ℝ) : Set (Fin l → ℝ) := Set.pi univ fun i => Iio (x i)

theorem gp_frontier_Iic_eq (x : Fin l → ℝ) : frontier (Iic x) = Iic x \ gp_lowerOpen x := by
  rw [frontier, isClosed_Iic.closure_eq, gp_Iic_eq_pi, interior_pi_set finite_univ]
  simp_rw [interior_Iic]
  rfl

theorem gp_lowerOpen_subset (x : Fin l → ℝ) : gp_lowerOpen x ⊆ Iic x := fun _ hy i => (hy i
    trivial).le

/-- `F(x − ε1) → λ({y < x})` as `ε ↓ 0`. -/
theorem gp_tendsto_distFun_below (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ]
    (x : Fin l → ℝ) :
    Tendsto (fun ε => gp_distFun μ (x - gp_diag ε)) (𝓝[>] 0) (𝓝 (μ.real (gp_lowerOpen x))) := by
  set A : ℕ → Set (Fin l → ℝ) := fun n => Iic (x - gp_diag (1 / (n + 1)))
  have hmono : Monotone A := fun m n hmn => Iic_subset_Iic.2 fun i => by
    simp only [Pi.sub_apply, gp_diag]
    gcongr
  have hunion : (⋃ n, A n) = gp_lowerOpen x := by
    ext y
    simp only [A, mem_iUnion, mem_Iic, Pi.le_def, Pi.sub_apply, gp_diag, gp_lowerOpen, Set.mem_pi,
      mem_univ, true_implies, mem_Iio]
    constructor
    · rintro ⟨n, hn⟩ i; linarith [hn i, show (0 : ℝ) < 1 / (n + 1) by positivity]
    · intro h
      choose N hN using fun i => exists_nat_one_div_lt (sub_pos.2 (h i))
      refine ⟨Finset.univ.sup N, fun i => ?_⟩
      have hle : (N i : ℝ) ≤ Finset.univ.sup N := by
        exact_mod_cast Finset.le_sup (f := N) (Finset.mem_univ i)
      have : 1 / ((Finset.univ.sup N : ℕ) + 1 : ℝ) ≤ 1 / (N i + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith [hN i]
  have hlim : Tendsto (fun n => μ.real (A n)) atTop (𝓝 (μ.real (gp_lowerOpen x))) := by
    have := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hunion] at this
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp this
  rw [tendsto_order]
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds hc)).exists
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / (n + 1) by positivity)] with ε hε
    exact lt_of_lt_of_le hn (gp_distFun_mono μ fun i => by
      simp only [Pi.sub_apply, gp_diag]; linarith [hε.2])
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    refine lt_of_le_of_lt (measureReal_mono (s₂ := gp_lowerOpen x) fun y hy i _ => ?_) hc
    have := hy i
    simp only [Pi.sub_apply, gp_diag] at this
    exact lt_of_le_of_lt this (by linarith [show (0 : ℝ) < ε from hε])

/-- **Theorem 12.7c.** `F` is continuous from below at `x` iff the boundary of `(−∞, x]` is
`λ`-null. -/
theorem slp_theorem_12_7c (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ] (x : Fin l → ℝ) :
    gp_ContFromBelow (gp_distFun μ) x ↔ μ (frontier (Iic x)) = 0 := by
  have hdiff : μ.real (frontier (Iic x)) = gp_distFun μ x - μ.real (gp_lowerOpen x) := by
    rw [gp_frontier_Iic_eq, measureReal_sdiff (gp_lowerOpen_subset x)
      (MeasurableSet.univ_pi fun _ => measurableSet_Iio)]
    rfl
  have h0 : μ (frontier (Iic x)) = 0 ↔ μ.real (frontier (Iic x)) = 0 := by
    rw [measureReal_def, ENNReal.toReal_eq_zero_iff]; simp [measure_ne_top]
  rw [h0, hdiff, sub_eq_zero]
  constructor
  · intro h
    exact tendsto_nhds_unique h (gp_tendsto_distFun_below μ x)
  · intro h
    rw [gp_ContFromBelow, h]
    exact gp_tendsto_distFun_below μ x

/-- **Exercise 12.3.** A nondecreasing `F` that is continuous from above and from below at `x` is
continuous at `x`. -/
theorem slp_ex_12_3 {F : (Fin l → ℝ) → ℝ} (hF : Monotone F) {x : Fin l → ℝ}
    (ha : gp_ContFromAbove F x) (hb : gp_ContFromBelow F x) : ContinuousAt F x := by
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨ε₁, hε₁, h1⟩ := (Metric.tendsto_nhdsWithin_nhds.1 ha) δ hδ
  obtain ⟨ε₂, hε₂, h2⟩ := (Metric.tendsto_nhdsWithin_nhds.1 hb) δ hδ
  set ε := min ε₁ ε₂ / 2
  have hε : 0 < ε := by positivity
  have hu := h1 (x := ε) (show ε ∈ Ioi 0 from hε) (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε]; simp only [ε]
    linarith [min_le_left ε₁ ε₂, half_lt_self (lt_min hε₁ hε₂)])
  have hl := h2 (x := ε) (show ε ∈ Ioi 0 from hε) (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε]; simp only [ε]
    linarith [min_le_right ε₁ ε₂, half_lt_self (lt_min hε₁ hε₂)])
  rw [Real.dist_eq] at hu hl
  filter_upwards [Metric.ball_mem_nhds x hε] with y hy
  rw [Metric.mem_ball, dist_pi_lt_iff hε] at hy
  have hlo : x - gp_diag ε ≤ y := fun i => by
    have := hy i; rw [Real.dist_eq, abs_lt] at this; simp only [Pi.sub_apply, gp_diag]; linarith
  have hhi : y ≤ x + gp_diag ε := fun i => by
    have := hy i; rw [Real.dist_eq, abs_lt] at this; simp only [Pi.add_apply, gp_diag]; linarith
  have := hF hlo
  have := hF hhi
  rw [Real.dist_eq, abs_lt]
  rw [abs_lt] at hu hl
  constructor <;> linarith

end Miao.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Weak convergence of distribution functions

Copied from `RecursiveMethods/WeakConvergence` (SLP Chapter 12, module
`DistributionConvergence.lean`), with the
namespace renamed to `Miao.MarkovProcesses`, the results numbered in SLP prefixed
`slp_` and the helper lemmas and definitions prefixed `gp_`.

SLP §12.3, Theorem 12.8 and Exercises 12.4–12.5, pp. 369–372.

* `gp_nullCoord μ i`: the levels `c` with `λ{y : yᵢ = c} = 0`. Its complement is countable
  (`gp_countable_nullCoord_compl`), so it is dense.
* `gp_continuousAt_distFun`: a point whose coordinates are all null levels is a continuity point
  of `F`.
* **Theorem 12.8** (`slp_theorem_12_8`): `λₙ ⇒ λ` iff `Fₙ(x) → F(x)` at every continuity point `x`
  of
  `F`. For (⇐), boxes with null-level coordinates satisfy the hypotheses of Theorem 12.5, and
  their measures are alternating sums of `F` at continuity points.
* **Exercise 12.4** (`slp_ex_12_4`): for `S ⊆ ℝˡ` Borel, `λₙ ⇒ λ` on `S` iff the extensions
  `λ̂(A) = λ(A ∩ S)` converge weakly on `ℝˡ`.
-/

namespace Miao.MarkovProcesses

open MeasureTheory Filter Topology Set BoundedContinuousFunction

variable {l : ℕ}

/-- The levels `c` with `λ{y : yᵢ = c} = 0`. -/
def gp_nullCoord (μ : Measure (Fin l → ℝ)) (i : Fin l) : Set ℝ := {c | μ {y | y i = c} = 0}

theorem gp_countable_nullCoord_compl (μ : Measure (Fin l → ℝ)) [IsFiniteMeasure μ] (i : Fin l) :
    (gp_nullCoord μ i)ᶜ.Countable := by
  refine (Measure.countable_meas_level_set_pos (μ := μ) (measurable_pi_apply i)).mono ?_
  intro c hc
  exact pos_iff_ne_zero.2 hc

theorem gp_dense_nullCoord (μ : Measure (Fin l → ℝ)) [IsFiniteMeasure μ] (i : Fin l) :
    Dense (gp_nullCoord μ i) := by
  simpa using (gp_countable_nullCoord_compl μ i).dense_compl ℝ

/-- A point whose coordinates are null levels is a continuity point of `F`. -/
theorem gp_continuousAt_distFun (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ]
    {v : Fin l → ℝ} (hv : ∀ i, v i ∈ gp_nullCoord μ i) : ContinuousAt (gp_distFun μ) v := by
  refine slp_ex_12_3 (gp_distFun_mono μ) (gp_contFromAbove_distFun μ v) ((slp_theorem_12_7c μ v).2
      ?_)
  refine measure_mono_null (t := ⋃ i, {y : Fin l → ℝ | y i = v i}) (fun y hy => ?_)
    (measure_iUnion_null fun i => hv i)
  rw [gp_frontier_Iic_eq] at hy
  obtain ⟨hle, hlt⟩ := hy
  simp only [gp_lowerOpen, Set.mem_pi, mem_univ, true_implies, mem_Iio, not_forall, not_lt] at hlt
  obtain ⟨i, hi⟩ := hlt
  exact mem_iUnion.2 ⟨i, le_antisymm (hle i) hi⟩

/-- A continuity point of `F` has a `λ`-null boundary of `(−∞, x]`. -/
theorem gp_frontier_null_of_continuousAt (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ]
    {x : Fin l → ℝ} (h : ContinuousAt (gp_distFun μ) x) : μ (frontier (Iic x)) = 0 := by
  refine (slp_theorem_12_7c μ x).1 ?_
  have hc : Tendsto (fun ε : ℝ => x - gp_diag ε) (𝓝[>] 0) (𝓝 x) := by
    have : Tendsto (fun ε : ℝ => x - gp_diag ε) (𝓝 0) (𝓝 (x - gp_diag 0)) :=
      (continuous_const.sub (continuous_pi fun _ => continuous_id)).tendsto 0
    have h0 : x - gp_diag 0 = x := by ext; simp [gp_diag]
    rw [h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact h.tendsto.comp hc

theorem gp_box_inter (a b a' b' : Fin l → ℝ) : gp_box a b ∩ gp_box a' b' = gp_box (a ⊔ a') (b ⊓ b')
    := by
  ext y
  simp only [gp_box, mem_inter_iff, Set.mem_pi, mem_univ, true_implies, mem_Ioc, Pi.sup_apply,
    Pi.inf_apply, max_lt_iff, le_min_iff]
  constructor
  · rintro ⟨h1, h2⟩ i; exact ⟨⟨(h1 i).1, (h2 i).1⟩, (h1 i).2, (h2 i).2⟩
  · intro h; exact ⟨fun i => ⟨(h i).1.1, (h i).2.1⟩, fun i => ⟨(h i).1.2, (h i).2.2⟩⟩

theorem gp_box_eq_empty {a b : Fin l → ℝ} (h : ¬ a ≤ b) : gp_box a b = ∅ := by
  rw [Pi.le_def] at h
  push Not at h
  obtain ⟨i, hi⟩ := h
  ext y
  simp only [gp_box, Set.mem_pi, mem_univ, true_implies, mem_Ioc, mem_empty_iff_false, iff_false,
    not_forall]
  exact ⟨i, fun h => by linarith [h.1, h.2]⟩

/-- **Theorem 12.8.** For probability measures on `ℝˡ`, `λₙ ⇒ λ` iff `Fₙ(x) → F(x)` at every
continuity point `x` of `F`. -/
theorem slp_theorem_12_8 (ls : ℕ → Measure (Fin l → ℝ)) (μ : Measure (Fin l → ℝ))
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure μ] :
    ConvWeak ls μ ↔ ∀ x, ContinuousAt (gp_distFun μ) x →
      Tendsto (fun n => gp_distFun (ls n) x) atTop (𝓝 (gp_distFun μ x)) := by
  constructor
  · intro h x hx
    exact (slp_theorem_12_3 ls μ).2.2.1 h (Iic x) measurableSet_Iic
      (gp_frontier_null_of_continuousAt μ hx)
  · intro h
    set 𝒜 : Set (Set (Fin l → ℝ)) := {A | ∃ a b, (∀ i, a i ∈ gp_nullCoord μ i ∧
      b i ∈ gp_nullCoord μ i) ∧ A = gp_box a b}
    refine slp_theorem_12_5 (𝒜 := 𝒜) (fun A ⟨a, b, _, hA⟩ => hA ▸ gp_measurableSet_box a b) ?_ ?_ ?_
    · rintro _ ⟨a, b, hab, rfl⟩ _ ⟨a', b', hab', rfl⟩
      refine ⟨a ⊔ a', b ⊓ b', fun i => ⟨?_, ?_⟩, gp_box_inter a b a' b'⟩
      · simp only [Pi.sup_apply]; rcases le_total (a i) (a' i) with h1 | h1
        · rw [max_eq_right h1]; exact (hab' i).1
        · rw [max_eq_left h1]; exact (hab i).1
      · simp only [Pi.inf_apply]; rcases le_total (b i) (b' i) with h1 | h1
        · rw [min_eq_left h1]; exact (hab i).2
        · rw [min_eq_right h1]; exact (hab' i).2
    · intro x ε hε
      have hε2 : 0 < ε / 2 := by positivity
      choose a ha hai using fun i => (gp_dense_nullCoord μ i).exists_between
        (show x i - ε / 2 < x i by linarith)
      choose b hb hbi using fun i => (gp_dense_nullCoord μ i).exists_between
        (show x i < x i + ε / 2 by linarith)
      refine ⟨gp_box a b, ⟨a, b, fun i => ⟨ha i, hb i⟩, rfl⟩, ?_, fun y hy => ?_⟩
      · refine mem_interior.2 ⟨Set.pi univ fun i => Ioo (a i) (b i), fun y hy i _ =>
          ⟨(hy i trivial).1, (hy i trivial).2.le⟩,
          isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo, fun i _ => ⟨(hai i).2, (hbi i).1⟩⟩
      · rw [Metric.mem_ball, dist_pi_lt_iff hε]
        intro i
        have := hy i trivial
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [(hai i).1, (hbi i).2, this.1, this.2]
    · rintro _ ⟨a, b, hab, rfl⟩
      by_cases hle : a ≤ b
      · simp_rw [← gp_vertexSum_eq _ hle]
        refine tendsto_finsetSum _ fun t _ => (h _ ?_).const_mul _
        refine gp_continuousAt_distFun μ fun i => ?_
        simp only [gp_vertex]
        split_ifs
        · exact (hab i).2
        · exact (hab i).1
      · simp [gp_box_eq_empty hle]

/-- **Exercise 12.4.** For `S ⊆ ℝˡ`, `λₙ ⇒ λ` on `S` iff the extensions `λ̂(A) = λ(A ∩ S)` converge
weakly on `ℝˡ`. (Measurability of `S` is not needed.) -/
theorem slp_ex_12_4 {S : Set (Fin l → ℝ)} (ls : ℕ → Measure S) (μ : Measure S)
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure μ] :
    ConvWeak ls μ ↔ ConvWeak (fun n => (ls n).map Subtype.val) (μ.map Subtype.val) := by
  have hmap : ∀ (ν : Measure S) {F : Set (Fin l → ℝ)}, MeasurableSet F →
      (ν.map Subtype.val).real F = ν.real (Subtype.val ⁻¹' F) := fun ν F hF => by
    rw [measureReal_def, Measure.map_apply measurable_subtype_coe hF]; rfl
  rw [(slp_theorem_12_3 ls μ).1, (slp_theorem_12_3 _ _).1]
  constructor
  · intro h F hF
    simp_rw [hmap _ hF.measurableSet]
    exact h _ (hF.preimage continuous_subtype_val)
  · intro h A hA
    obtain ⟨F, hF, rfl⟩ := isClosed_induced_iff.1 hA
    have := h F hF
    simp_rw [hmap _ hF.measurableSet] at this
    exact this

/-- **Exercise 12.5a.** On `S = [a, b] ⊆ ℝˡ`, if `λₙ([a, x]) → λ([a, x])` for every `x ∈ S`, then
`λₙ ⇒ λ` (through Exercise 12.4 and Theorem 12.8). -/
theorem slp_ex_12_5a {a b : Fin l → ℝ} (ls : ℕ → Measure (Icc a b)) (μ : Measure (Icc a b))
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure μ]
    (h : ∀ x ∈ Icc a b, Tendsto (fun n => (ls n).real (Subtype.val ⁻¹' Icc a x)) atTop
      (𝓝 (μ.real (Subtype.val ⁻¹' Icc a x)))) : ConvWeak ls μ := by
  obtain ⟨s₀⟩ := nonempty_of_isProbabilityMeasure μ
  have hab : a ≤ b := s₀.2.1.trans s₀.2.2
  refine (slp_ex_12_4 ls μ).2 ((slp_theorem_12_8 _ _).2 fun y _ => ?_)
  have hmap : ∀ (ν : Measure (Icc a b)), gp_distFun (ν.map Subtype.val) y =
      ν.real (Subtype.val ⁻¹' Iic y) := fun ν => by
    rw [gp_distFun, measureReal_def, Measure.map_apply measurable_subtype_coe measurableSet_Iic];
        rfl
  simp_rw [hmap]
  by_cases hay : a ≤ y
  · have hpre : (Subtype.val ⁻¹' Iic y : Set (Icc a b)) = Subtype.val ⁻¹' Icc a (y ⊓ b) := by
      ext s
      simp only [mem_preimage, mem_Iic, mem_Icc, le_inf_iff]
      exact ⟨fun hs => ⟨s.2.1, hs, s.2.2⟩, fun hs => hs.2.1⟩
    rw [hpre]
    exact h _ ⟨le_inf hay hab, inf_le_right⟩
  · have hpre : (Subtype.val ⁻¹' Iic y : Set (Icc a b)) = ∅ := by
      ext s
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact fun hs => hay (s.2.1.trans hs)
    simp [hpre]

/-- The continuous nondecreasing ramp `gₙ(s) = min 1 (n Σᵢ max 0 (sᵢ - xᵢ))`, which increases to the
indicator of `{s : ¬ s ≤ x}` (used for Exercise 12.5b in place of the book's Lemma 12.1
functions). -/
noncomputable def gp_ramp (x : Fin l → ℝ) (n : ℕ) (s : Fin l → ℝ) : ℝ :=
  min 1 ((n : ℝ) * ∑ i, max 0 (s i - x i))

theorem gp_continuous_ramp (x : Fin l → ℝ) (n : ℕ) : Continuous (gp_ramp x n) := by
  unfold gp_ramp; fun_prop

theorem gp_ramp_mem (x : Fin l → ℝ) (n : ℕ) (s : Fin l → ℝ) : 0 ≤ gp_ramp x n s ∧ gp_ramp x n s ≤ 1
    :=
  ⟨le_min zero_le_one (mul_nonneg n.cast_nonneg
    (Finset.sum_nonneg fun _ _ => le_max_left _ _)), min_le_left _ _⟩

theorem gp_monotone_ramp (x : Fin l → ℝ) (n : ℕ) : Monotone (gp_ramp x n) := fun s t hst =>
  min_le_min_left _ (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
    max_le_max le_rfl (by linarith [hst i])) n.cast_nonneg)

theorem gp_tendsto_ramp (x s : Fin l → ℝ) :
    Tendsto (fun n => gp_ramp x n s) atTop (𝓝 ((Iic x)ᶜ.indicator 1 s)) := by
  by_cases hs : s ≤ x
  · have : ∀ n, gp_ramp x n s = 0 := fun n => by
      have : ∀ i, max 0 (s i - x i) = 0 := fun i => max_eq_left (by linarith [hs i])
      simp [gp_ramp, this]
    simp only [this, indicator_of_notMem (show s ∉ (Iic x)ᶜ by simpa using hs)]
    exact tendsto_const_nhds
  · obtain ⟨i, hi⟩ : ∃ i, x i < s i := by
      by_contra h; push Not at h; exact hs h
    have hc : s i - x i ≤ ∑ j, max 0 (s j - x j) :=
      (le_max_right _ _).trans (Finset.single_le_sum (f := fun j => max 0 (s j - x j))
        (fun j _ => le_max_left _ _) (Finset.mem_univ i))
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / (s i - x i))
    rw [indicator_of_mem (show s ∈ (Iic x)ᶜ by simpa using hs)]
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
    have hpos : 0 < s i - x i := by linarith
    have : 1 ≤ (n : ℝ) * ∑ j, max 0 (s j - x j) := by
      have h1 : 1 < N * (s i - x i) := by rwa [div_lt_iff₀ hpos] at hN
      have h2 : (N : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    simp [gp_ramp, min_eq_left this]

/-- **Exercise 12.5b** (corrected). On `S = [a, b]`, probability measures agreeing on the integrals
of all continuous nondecreasing functions are equal. (The book's hint cites "Theorem 12.1", i.e.
Lemma 12.1, whose functions are nonincreasing; nondecreasing functions suffice, which is what
Theorem 12.12 needs.) -/
theorem slp_ex_12_5b {a b : Fin l → ℝ} (lam μ : Measure (Icc a b)) [IsProbabilityMeasure lam]
    [IsProbabilityMeasure μ] (h : ∀ f : Icc a b →ᵇ ℝ, Monotone f → ∫ s, f s ∂lam = ∫ s, f s ∂μ) :
    lam = μ := by
  have hE : ∀ x : Fin l → ℝ, MeasurableSet (Subtype.val ⁻¹' (Iic x)ᶜ : Set (Icc a b)) :=
    fun x => measurableSet_Iic.compl.preimage measurable_subtype_coe
  have hlim : ∀ (ν : Measure (Icc a b)) [IsProbabilityMeasure ν] (x : Fin l → ℝ),
      Tendsto (fun n => ∫ s, gp_ramp x n (s : Fin l → ℝ) ∂ν) atTop
        (𝓝 (ν.real (Subtype.val ⁻¹' (Iic x)ᶜ))) := fun ν _ x => by
    rw [← integral_indicator_one (hE x)]
    refine tendsto_integral_of_dominated_convergence (fun _ => 1)
      (fun n => ((gp_continuous_ramp x n).comp continuous_subtype_val).aestronglyMeasurable)
      (integrable_const 1) (fun n => Eventually.of_forall fun s => ?_)
      (Eventually.of_forall fun s => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (gp_ramp_mem x n s).1]; exact (gp_ramp_mem x n s).2
    · exact gp_tendsto_ramp x s
  have heq : ∀ x : Fin l → ℝ, lam.real (Subtype.val ⁻¹' (Iic x)ᶜ) =
      μ.real (Subtype.val ⁻¹' (Iic x)ᶜ) := fun x => by
    refine tendsto_nhds_unique (hlim lam x) ?_
    have := hlim μ x
    refine this.congr fun n => (h ⟨⟨fun s => gp_ramp x n s,
      (gp_continuous_ramp x n).comp continuous_subtype_val⟩, ⟨1, fun s t => ?_⟩⟩
      (fun s t hst => gp_monotone_ramp x n hst)).symm
    have := gp_ramp_mem x n s; have := gp_ramp_mem x n t
    simp only [Real.dist_eq, abs_le]; constructor <;> linarith
  have hconv : ConvWeak (fun _ => μ) lam := by
    refine slp_ex_12_5a _ _ fun x _ => ?_
    have hpre : (Subtype.val ⁻¹' Icc a x : Set (Icc a b)) = (Subtype.val ⁻¹' (Iic x)ᶜ)ᶜ := by
      ext s
      simp only [mem_preimage, mem_Icc, mem_compl_iff, mem_Iic, not_not]
      exact ⟨fun hs => hs.2, fun hs => ⟨s.2.1, hs⟩⟩
    rw [hpre, probReal_compl_eq_one_sub (hE x), probReal_compl_eq_one_sub (hE x), heq]
    exact tendsto_const_nhds
  exact gp_convWeak_unique hconv fun _ => tendsto_const_nhds

end Miao.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Support, Helly's theorem and tightness (SLP §12.3, pp. 371–375)

Copied from `RecursiveMethods/WeakConvergence` (SLP Chapter 12, module `Helly.lean`), with the
namespace renamed to `Miao.MarkovProcesses`, the results numbered in SLP prefixed
`slp_` and the helper lemmas and definitions prefixed `gp_`.

* the **support** of a probability measure (p. 371): the intersection of two closed sets of measure
  one is closed of measure one ("(Why?)"), and on a second-countable space the smallest closed set
  of measure one exists (`gp_exists_support`, by Lindelöf — the book's "extends to any family" needs
  separability);
* the general lemma behind every compactness argument of the chapter: a **tight** sequence of
  probability measures on a separable metric space has a weakly convergent subsequence
  (`gp_exists_convWeak_subseq_of_tight`, through Prokhorov's theorem);
* **Theorem 12.9 (Helly)** and its **Corollary 1**, corrected: hypothesis (3), `Fₙ(a̲) = 0` and
  `Fₙ(b̄) = 1`, does not confine the measures to `[a̲, b̄]` when `l ≥ 2`
  (`slp_theorem_12_9_false_hyp`: `δ_{(-n, 0)}` has no weakly convergent subsequence), and the
  conclusion `F(a̲) = 0` fails even for `l = 1` (`slp_theorem_12_9_false_concl`: `δ_{1/(n+1)}`). The
  true statement takes the measures concentrated on `[a̲, b̄]` and concludes the same of the limit
  (`slp_theorem_12_9_cor1`, `slp_theorem_12_9`);
* **Exercise 12.6**: (a) holds for `l = 1` (`slp_ex_12_6a`) and fails for `l = 2`
  (`slp_ex_12_6a_false`); (b), (c) are tightness (`slp_ex_12_6b`, `slp_ex_12_6c`; closedness is not
  needed);
* **Corollary 2** (corrected): a monotone sequence of distribution functions of measures
  concentrated on `[a̲, b̄]` converges weakly (`slp_theorem_12_9_cor2`).
-/

namespace Miao.MarkovProcesses

open MeasureTheory Filter Topology Set BoundedContinuousFunction

/-! ### The support of a measure -/

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- `A` is the **support** of `μ` (SLP p. 371): the smallest closed set of measure one. -/
def gp_IsSupport (μ : Measure X) (A : Set X) : Prop :=
  IsClosed A ∧ μ A = 1 ∧ ∀ B, IsClosed B → μ B = 1 → A ⊆ B

variable [OpensMeasurableSpace X]

/-- The "(Why?)" of p. 371: two closed sets of measure one meet in a closed set of measure one. -/
theorem gp_support_inter (μ : Measure X) [IsProbabilityMeasure μ] {A B : Set X} (hA : IsClosed A)
    (hB : IsClosed B) (hμA : μ A = 1) (hμB : μ B = 1) : IsClosed (A ∩ B) ∧ μ (A ∩ B) = 1 := by
  refine ⟨hA.inter hB, (prob_compl_eq_zero_iff (hA.inter hB).measurableSet).1 ?_⟩
  rw [compl_inter]
  exact measure_union_null ((prob_compl_eq_zero_iff hA.measurableSet).2 hμA)
    ((prob_compl_eq_zero_iff hB.measurableSet).2 hμB)

/-- The support exists and is unique on a second-countable space (SLP p. 371–372; the extension
from two sets to an arbitrary family needs Lindelöf). -/
theorem gp_exists_support [SecondCountableTopology X] (μ : Measure X) [IsProbabilityMeasure μ] :
    ∃! A, gp_IsSupport μ A := by
  set C := {B : Set X | IsClosed B ∧ μ B = 1}
  have hcl : IsClosed (⋂₀ C) := isClosed_sInter fun B hB => hB.1
  have hnull : μ (⋂₀ C)ᶜ = 0 := by
    rw [compl_sInter]
    obtain ⟨T, hTc, hTsub, hTeq⟩ := TopologicalSpace.isOpen_sUnion_countable (compl '' C)
      (by rintro _ ⟨B, hB, rfl⟩; exact hB.1.isOpen_compl)
    rw [← hTeq]
    refine (measure_sUnion_null_iff hTc).2 fun U hU => ?_
    obtain ⟨B, hB, rfl⟩ := hTsub hU
    exact (prob_compl_eq_zero_iff hB.1.measurableSet).2 hB.2
  refine ⟨⋂₀ C, ⟨hcl, (prob_compl_eq_zero_iff hcl.measurableSet).1 hnull,
    fun B hB hμB => sInter_subset_of_mem ⟨hB, hμB⟩⟩, fun A hA => ?_⟩
  exact (hA.2.2 _ hcl ((prob_compl_eq_zero_iff hcl.measurableSet).1 hnull)).antisymm
    (sInter_subset_of_mem ⟨hA.1, hA.2.1⟩)

/-! ### Tightness and weakly convergent subsequences -/

/-- A **tight** sequence of probability measures on a separable metric space (for every `ε > 0` a
compact `K` with `λₙ(K) > 1 - ε` for all `n`) has a weakly convergent subsequence. This is the
form in which Helly's theorem is used throughout the chapter (Prokhorov's theorem). -/
theorem gp_exists_convWeak_subseq_of_tight {S : Type*} [MetricSpace S]
    [TopologicalSpace.SeparableSpace S] [MeasurableSpace S] [BorelSpace S] (ls : ℕ → Measure S)
    [∀ n, IsProbabilityMeasure (ls n)]
    (htight : ∀ ε > 0, ∃ K, IsCompact K ∧ ∀ n, 1 - ε < (ls n).real K) :
    ∃ μ : Measure S, IsProbabilityMeasure μ ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvWeak (ls ∘ φ) μ := by
  let P : ℕ → ProbabilityMeasure S := fun n => ⟨ls n, inferInstance⟩
  have hT : IsTightMeasureSet {((μ : ProbabilityMeasure S) : Measure S) | μ ∈ range P} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    by_cases hεtop : ε = ⊤
    · exact ⟨∅, isCompact_empty, fun μ _ => hεtop ▸ le_top⟩
    obtain ⟨K, hK, hKn⟩ := htight ε.toReal (ENNReal.toReal_pos hε.ne' hεtop)
    refine ⟨K, hK, ?_⟩
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    have h1 : (ls n).real Kᶜ ≤ ε.toReal := by
      rw [probReal_compl_eq_one_sub hK.measurableSet]; linarith [hKn n]
    change (ls n) Kᶜ ≤ ε
    rw [← ofReal_measureReal (μ := ls n) (s := Kᶜ), ← ENNReal.ofReal_toReal hεtop]
    exact ENNReal.ofReal_le_ofReal h1
  obtain ⟨ν, -, φ, hφ, hlim⟩ := (isCompact_closure_of_isTightMeasureSet hT).tendsto_subseq
    (fun n => subset_closure ⟨n, rfl⟩)
  exact ⟨ν, inferInstance, φ, hφ, fun f =>
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim f⟩

/-! ### Helly's theorem -/

variable {l : ℕ}

/-- A weak limit of measures concentrated on a closed set is concentrated on it (Theorem 12.3b). -/
theorem gp_measure_eq_one_of_convWeak {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    {ls : ℕ → Measure S} {μ : Measure S} [∀ n, IsProbabilityMeasure (ls n)]
    [IsProbabilityMeasure μ] (h : ConvWeak ls μ) {F : Set S} (hF : IsClosed F)
    (hls : ∀ n, ls n F = 1) : μ F = 1 := by
  have hlim := (slp_theorem_12_3 ls μ).1.1 h F hF
  have h1 : 1 ≤ μ.real F := le_of_forall_pos_lt_add fun ε hε => by
    obtain ⟨n, hn⟩ := (hlim ε hε).exists
    have h1n : (ls n).real F = 1 := by rw [measureReal_def, hls n, ENNReal.toReal_one]
    change (ls n).real F < _ at hn
    linarith
  have : μ.real F = 1 := le_antisymm measureReal_le_one h1
  rw [← ofReal_measureReal, this, ENNReal.ofReal_one]

/-- **Corollary 1 to Theorem 12.9** (Helly, measure form), corrected: probability measures on
`ℝˡ` concentrated on `[a̲, b̄]` have a subsequence converging weakly to a probability measure
concentrated on `[a̲, b̄]`. -/
theorem slp_theorem_12_9_cor1 {a b : Fin l → ℝ} (ls : ℕ → Measure (Fin l → ℝ))
    [∀ n, IsProbabilityMeasure (ls n)] (h : ∀ n, ls n (Icc a b) = 1) :
    ∃ μ : Measure (Fin l → ℝ), IsProbabilityMeasure μ ∧ μ (Icc a b) = 1 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvWeak (ls ∘ φ) μ := by
  obtain ⟨μ, hμ, φ, hφ, hconv⟩ := gp_exists_convWeak_subseq_of_tight ls fun ε hε =>
    ⟨Icc a b, isCompact_Icc, fun n => by
      rw [measureReal_def, h n, ENNReal.toReal_one]; linarith⟩
  have : ∀ n, IsProbabilityMeasure ((ls ∘ φ) n) := fun n =>
    inferInstanceAs (IsProbabilityMeasure (ls (φ n)))
  exact ⟨μ, hμ, gp_measure_eq_one_of_convWeak hconv isClosed_Icc fun n => h (φ n), φ, hφ, hconv⟩

/-- Concentration on `[a̲, b̄]` in terms of the distribution function: `F(x) = 0` whenever some
`xᵢ < a̲ᵢ`, and `F(b̄) = 1`. -/
theorem gp_concentrated_iff {a b : Fin l → ℝ} (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ] :
    μ (Icc a b) = 1 ↔ (∀ x, (∃ i, x i < a i) → gp_distFun μ x = 0) ∧ gp_distFun μ b = 1 := by
  constructor
  · intro h
    have hc : μ (Icc a b)ᶜ = 0 := (prob_compl_eq_zero_iff measurableSet_Icc).2 h
    refine ⟨fun x ⟨i, hi⟩ => ?_, ?_⟩
    · have : μ (Iic x) = 0 := measure_mono_null (t := (Icc a b)ᶜ) (fun y hy hyab => by
        exact absurd ((hyab.1 i).trans (hy i)) (not_le.2 hi)) hc
      rw [gp_distFun, measureReal_def, this, ENNReal.toReal_zero]
    · have : μ (Iic b) = 1 :=
        le_antisymm prob_le_one (h ▸ measure_mono fun y hy => hy.2)
      rw [gp_distFun, measureReal_def, this, ENNReal.toReal_one]
  · rintro ⟨h0, h1⟩
    have hb : μ (Iic b)ᶜ = 0 := by
      have : μ.real (Iic b)ᶜ = 0 := by
        rw [probReal_compl_eq_one_sub measurableSet_Iic]; rw [gp_distFun] at h1; linarith
      exact (measureReal_eq_zero_iff).1 this
    have hk : ∀ i (k : ℕ), μ (Iic (Function.update b i (a i - 1 / (k + 1)))) = 0 := fun i k => by
      have := h0 (Function.update b i (a i - 1 / (k + 1))) ⟨i, by
        simp only [Function.update_self]; linarith [Nat.one_div_pos_of_nat (α := ℝ) (n := k)]⟩
      exact (measureReal_eq_zero_iff).1 this
    refine (prob_compl_eq_zero_iff measurableSet_Icc).1 (measure_mono_null (t := (Iic b)ᶜ ∪
      ⋃ i, ⋃ k : ℕ, Iic (Function.update b i (a i - 1 / (k + 1)))) ?_
      (measure_union_null hb (measure_iUnion_null fun i => measure_iUnion_null (hk i))))
    intro y hy
    by_cases hyb : y ≤ b
    · right
      obtain ⟨i, hi⟩ : ∃ i, y i < a i := by
        by_contra hne; push Not at hne; exact hy ⟨hne, hyb⟩
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hi)
      simp only [mem_iUnion]
      refine ⟨i, k, fun j => ?_⟩
      rcases eq_or_ne j i with rfl | hji
      · simp only [Function.update_self]; linarith
      · rw [Function.update_of_ne hji]; exact hyb j
    · exact Or.inl hyb

/-- **Theorem 12.9 (Helly)**, corrected: distribution functions vanishing whenever some
`xᵢ < a̲ᵢ` and equal to one at `b̄` have a subsequence converging weakly to a distribution
function with the same properties. -/
theorem slp_theorem_12_9 {a b : Fin l → ℝ} (ls : ℕ → Measure (Fin l → ℝ))
    [∀ n, IsProbabilityMeasure (ls n)]
    (h0 : ∀ n x, (∃ i, x i < a i) → gp_distFun (ls n) x = 0) (h1 : ∀ n, gp_distFun (ls n) b = 1) :
    ∃ μ : Measure (Fin l → ℝ), IsProbabilityMeasure μ ∧
      (∀ x, (∃ i, x i < a i) → gp_distFun μ x = 0) ∧ gp_distFun μ b = 1 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvWeak (ls ∘ φ) μ := by
  obtain ⟨μ, hμ, hab, φ, hφ, hconv⟩ :=
    slp_theorem_12_9_cor1 ls fun n => (gp_concentrated_iff (ls n)).2 ⟨h0 n, h1 n⟩
  exact ⟨μ, hμ, ((gp_concentrated_iff μ).1 hab).1, ((gp_concentrated_iff μ).1 hab).2, φ, hφ, hconv⟩

/-- The distribution function of a unit mass. -/
theorem gp_distFun_dirac (p x : Fin l → ℝ) :
    gp_distFun (Measure.dirac p) x = if p ≤ x then 1 else 0 := by
  rw [gp_distFun, measureReal_def, Measure.dirac_apply' p measurableSet_Iic]
  split_ifs with h
  · rw [indicator_of_mem (show p ∈ Iic x from h)]; simp
  · rw [indicator_of_notMem (show p ∉ Iic x from h)]; simp

/-- The sequence `δ_{(-n, 0)}` on `ℝ²` has no weakly convergent subsequence: its mass escapes
to `-∞` in the first coordinate. -/
theorem gp_not_convWeak_escape (φ : ℕ → ℕ) (hφ : StrictMono φ) (μ : Measure (Fin 2 → ℝ))
    [IsProbabilityMeasure μ] :
    ¬ ConvWeak ((fun n : ℕ => Measure.dirac (![-(n : ℝ), 0] : Fin 2 → ℝ)) ∘ φ) μ := by
  intro hconv
  have : ∀ n, IsProbabilityMeasure
      (((fun n : ℕ => Measure.dirac (![-(n : ℝ), 0] : Fin 2 → ℝ)) ∘ φ) n) := fun n =>
    inferInstanceAs (IsProbabilityMeasure (Measure.dirac _))
  set G : ℕ → Set (Fin 2 → ℝ) := fun M => {y | -(M : ℝ) < y 0}
  have hG : ∀ M, IsOpen (G M) := fun M => isOpen_lt continuous_const (continuous_apply 0)
  have hnull : ∀ M, μ (G M) = 0 := fun M => by
    have hlim := (slp_theorem_12_3 _ μ).2.1.1 hconv (G M) (hG M)
    have : μ.real (G M) ≤ 0 := le_of_forall_pos_lt_add fun ε hε => by
      obtain ⟨n, hn, hnM⟩ := ((hlim ε hε).and (eventually_ge_atTop M)).exists
      have hφn : M ≤ φ n := hnM.trans (hφ.id_le n)
      have : ((Measure.dirac (![-(φ n : ℝ), 0] : Fin 2 → ℝ))).real (G M) = 0 := by
        rw [measureReal_def, Measure.dirac_apply' _ (hG M).measurableSet,
          indicator_of_notMem (by simpa [G] using hφn)]; simp
      simp only [Function.comp_apply] at hn
      linarith
    exact (measureReal_eq_zero_iff).1 (le_antisymm this measureReal_nonneg)
  have hU : (⋃ M, G M) = univ := eq_univ_of_forall fun y => by
    obtain ⟨M, hM⟩ := exists_nat_gt (-(y 0))
    exact mem_iUnion.2 ⟨M, by simp only [G, mem_ofPred]; linarith⟩
  have := measure_iUnion_null hnull
  rw [hU, measure_univ] at this
  exact one_ne_zero this

/-- **Theorem 12.9 / Corollary 1 are false as printed (hypothesis).** On `ℝ²`, `δ_{(-n, 0)}`
satisfies (3) with `a̲ = (0, -1)`, `b̄ = (1, 1)` (`Fₙ(a̲) = 0`, `Fₙ(b̄) = 1`), but no
subsequence converges weakly. -/
theorem slp_theorem_12_9_false_hyp :
    let ls := fun n : ℕ => Measure.dirac (![-(n : ℝ), 0] : Fin 2 → ℝ)
    (∀ n, gp_distFun (ls n) ![0, -1] = 0 ∧ gp_distFun (ls n) ![1, 1] = 1) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ μ : Measure (Fin 2 → ℝ), IsProbabilityMeasure μ →
        ¬ ConvWeak (ls ∘ φ) μ := by
  intro ls
  refine ⟨fun n => ⟨?_, ?_⟩, fun φ hφ μ _ => gp_not_convWeak_escape φ hφ μ⟩
  · rw [gp_distFun_dirac, ite_eq_right_iff]
    intro h; have := h 1; norm_num at this
  · rw [gp_distFun_dirac, ite_eq_left_iff]
    intro h; exfalso; apply h
    intro i; fin_cases i <;> simp; linarith [n.cast_nonneg (α := ℝ)]

/-- **Theorem 12.9 / Corollary 1 are false as printed (conclusion).** On `ℝ`, `δ_{1/(n+1)}`
satisfies (3) with `a̲ = 0`, `b̄ = 1`, and does converge weakly, but every weak limit of every
subsequence has `F(a̲) = 1`, not `0`. -/
theorem slp_theorem_12_9_false_concl :
    let ls := fun n : ℕ => Measure.dirac (fun _ => 1 / ((n : ℝ) + 1) : Fin 1 → ℝ)
    (∀ n, gp_distFun (ls n) 0 = 0 ∧ gp_distFun (ls n) 1 = 1) ∧ ConvWeak ls (Measure.dirac 0) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ μ : Measure (Fin 1 → ℝ), IsProbabilityMeasure μ →
        ConvWeak (ls ∘ φ) μ → gp_distFun μ 0 = 1 := by
  intro ls
  have hconv : ConvWeak ls (Measure.dirac 0) := fun f => by
    simp only [ls, integral_dirac]
    exact (f.continuous.tendsto 0).comp (tendsto_pi_nhds.2 fun _ =>
      tendsto_one_div_add_atTop_nhds_zero_nat)
  refine ⟨fun n => ⟨?_, ?_⟩, hconv, fun φ hφ μ _ h => ?_⟩
  · rw [gp_distFun_dirac, ite_eq_right_iff]
    intro h; have := h 0; simp only [Pi.zero_apply] at this
    linarith [Nat.one_div_pos_of_nat (α := ℝ) (n := n)]
  · rw [gp_distFun_dirac, ite_eq_left_iff]
    intro h; exfalso; apply h
    intro i; simp only [Pi.one_apply]
    exact (div_le_one (by positivity)).2 (by linarith [n.cast_nonneg (α := ℝ)])
  · have : ∀ n, IsProbabilityMeasure ((ls ∘ φ) n) := fun n =>
      inferInstanceAs (IsProbabilityMeasure (Measure.dirac _))
    have : μ = Measure.dirac 0 :=
      gp_convWeak_unique h fun f => (hconv f).comp hφ.tendsto_atTop
    rw [this, gp_distFun_dirac, ite_eq_left_iff]
    exact fun h => absurd le_rfl h

/-! ### Exercise 12.6 -/

/-- **Exercise 12.6a** (`l = 1`). If for every `ε > 0` there are `a̲, b̄` with
`Fₙ(b̄) - Fₙ(a̲) > 1 - ε` for all `n`, some subsequence converges weakly. -/
theorem slp_ex_12_6a (ls : ℕ → Measure (Fin 1 → ℝ)) [∀ n, IsProbabilityMeasure (ls n)]
    (h : ∀ ε > 0, ∃ a b : Fin 1 → ℝ, ∀ n, 1 - ε < gp_distFun (ls n) b - gp_distFun (ls n) a) :
    ∃ μ : Measure (Fin 1 → ℝ), IsProbabilityMeasure μ ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvWeak (ls ∘ φ) μ := by
  refine gp_exists_convWeak_subseq_of_tight ls fun ε hε => ?_
  obtain ⟨a, b, hab⟩ := h ε hε
  refine ⟨Icc a b, isCompact_Icc, fun n => (hab n).trans_le ?_⟩
  have hsub : Iic b \ Iic a ⊆ Icc a b := fun y ⟨hyb, hya⟩ => by
    refine ⟨fun i => ?_, hyb⟩
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    by_contra hlt
    exact hya fun j => (Subsingleton.elim j 0 ▸ (not_le.1 hlt).le)
  exact (le_measureReal_sdiff).trans (measureReal_mono hsub)

/-- **Exercise 12.6a is false for `l ≥ 2`**: `δ_{(-n, 0)}` on `ℝ²` has `Fₙ(b̄) - Fₙ(a̲) = 1` for
`a̲ = (0, -1)`, `b̄ = (1, 1)`, yet no subsequence converges weakly. -/
theorem slp_ex_12_6a_false :
    let ls := fun n : ℕ => Measure.dirac (![-(n : ℝ), 0] : Fin 2 → ℝ)
    (∀ ε > 0, ∃ a b : Fin 2 → ℝ, ∀ n, 1 - ε < gp_distFun (ls n) b - gp_distFun (ls n) a) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ μ : Measure (Fin 2 → ℝ), IsProbabilityMeasure μ →
        ¬ ConvWeak (ls ∘ φ) μ := by
  intro ls
  refine ⟨fun ε hε => ⟨![0, -1], ![1, 1], fun n => ?_⟩, slp_theorem_12_9_false_hyp.2⟩
  rw [(slp_theorem_12_9_false_hyp.1 n).1, (slp_theorem_12_9_false_hyp.1 n).2]
  linarith

/-- **Exercise 12.6b.** A tight sequence of probability measures on `ℝˡ` has a weakly convergent
subsequence. -/
theorem slp_ex_12_6b (ls : ℕ → Measure (Fin l → ℝ)) [∀ n, IsProbabilityMeasure (ls n)]
    (htight : ∀ ε > 0, ∃ K, IsCompact K ∧ ∀ n, 1 - ε < (ls n).real K) :
    ∃ μ : Measure (Fin l → ℝ), IsProbabilityMeasure μ ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvWeak (ls ∘ φ) μ :=
  gp_exists_convWeak_subseq_of_tight ls htight

/-- **Exercise 12.6c.** The same on `S ⊆ ℝˡ` (the book assumes `S` closed; this is not needed). -/
theorem slp_ex_12_6c {S : Set (Fin l → ℝ)} (ls : ℕ → Measure S) [∀ n, IsProbabilityMeasure (ls n)]
    (htight : ∀ ε > 0, ∃ K, IsCompact K ∧ ∀ n, 1 - ε < (ls n).real K) :
    ∃ μ : Measure S, IsProbabilityMeasure μ ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvWeak (ls ∘ φ) μ :=
  gp_exists_convWeak_subseq_of_tight ls htight

/-! ### Corollary 2: monotone sequences -/

/-- **Corollary 2 to Theorem 12.9**, corrected: a monotone sequence of distribution functions
(`Fₙ₊₁ ≤ Fₙ` for all `n`, or `Fₙ₊₁ ≥ Fₙ` for all `n`) of measures concentrated on `[a̲, b̄]`
converges weakly to a probability measure concentrated on `[a̲, b̄]`. Proof: Helly gives a
subsequential limit `μ`; the whole sequence `Fₙ(x)` converges (bounded and monotone), so at
continuity points of `F_μ` its limit is `F_μ(x)`, and Theorem 12.8 applies. -/
theorem slp_theorem_12_9_cor2 {a b : Fin l → ℝ} (ls : ℕ → Measure (Fin l → ℝ))
    [∀ n, IsProbabilityMeasure (ls n)] (h : ∀ n, ls n (Icc a b) = 1)
    (hmono : (∀ n, gp_distFun (ls (n + 1)) ≤ gp_distFun (ls n)) ∨
      (∀ n, gp_distFun (ls n) ≤ gp_distFun (ls (n + 1)))) :
    ∃ μ : Measure (Fin l → ℝ), IsProbabilityMeasure μ ∧ μ (Icc a b) = 1 ∧ ConvWeak ls μ := by
  obtain ⟨μ, hμ, hab, φ, hφ, hconv⟩ := slp_theorem_12_9_cor1 ls h
  have : ∀ n, IsProbabilityMeasure ((ls ∘ φ) n) := fun n =>
    inferInstanceAs (IsProbabilityMeasure (ls (φ n)))
  have hconvx : ∀ x, ∃ c, Tendsto (fun n => gp_distFun (ls n) x) atTop (𝓝 c) := fun x => by
    have hbdd : ∀ n, 0 ≤ gp_distFun (ls n) x ∧ gp_distFun (ls n) x ≤ 1 := fun n =>
      ⟨measureReal_nonneg, measureReal_le_one⟩
    rcases hmono with hm | hm
    · exact ⟨_, tendsto_atTop_ciInf (antitone_nat_of_succ_le fun n => hm n x)
        ⟨0, by rintro _ ⟨n, rfl⟩; exact (hbdd n).1⟩⟩
    · exact ⟨_, tendsto_atTop_ciSup (monotone_nat_of_le_succ fun n => hm n x)
        ⟨1, by rintro _ ⟨n, rfl⟩; exact (hbdd n).2⟩⟩
  refine ⟨μ, hμ, hab, (slp_theorem_12_8 ls μ).2 fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := hconvx x
  have hsub := (slp_theorem_12_8 (ls ∘ φ) μ).1 hconv x hx
  rwa [tendsto_nhds_unique (hc.comp hφ.tendsto_atTop) hsub] at hc

end Miao.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Feller property and existence of invariant measures (SLP §12.4, pp. 375–378)

Copied from `RecursiveMethods/WeakConvergence` (SLP Chapter 12, module `FellerInvariant.lean`),
with the
namespace renamed to `Miao.MarkovProcesses`, the results numbered in SLP prefixed
`slp_` and the helper lemmas and definitions prefixed `gp_`.

* **Exercise 12.7**: on any metric space, the Feller property `T[C(S)] ⊆ C(S)` is equivalent to
  `sₙ → s ⇒ P(sₙ, ·) ⇒ P(s, ·)` and to `λₙ ⇒ λ ⇒ T*λₙ ⇒ T*λ` (`slp_ex_12_7`);
* **Exercise 12.8**: the cycle `s ↦ 1 - s` on `[0, 1]` is Feller; from `δ_s`, `s ≠ 1/2`, the even
  and odd iterates converge to the distinct non-invariant `δ_s`, `δ_{1-s}`; the invariant
  measures are exactly the measures symmetric about `1/2` (`slp_ex_12_8a`–`slp_ex_12_8c`);
* the limit step shared by Theorems 12.10 and 12.12 and Exercise 12.12 (`gp_invariant_of_convWeak`):
  if `νₙ ⇒ μ` and `⟨f, νₙ⟩ - ⟨f, T*νₙ⟩ → 0` for every bounded continuous `f`, then `μ` is
  invariant;
* **Theorem 12.10**: on a compact metric space a Feller transition function has an invariant
  probability measure, through the Cesàro averages of `T*ⁿδ_s` and Prokhorov's theorem. (The book
  works on compact `S ⊆ ℝˡ` and invokes Helly on `ℝˡ`; any compact metric space works. `S` must be
  nonempty.)
-/

namespace Miao.MarkovProcesses

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal

variable {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]

omit [MeasurableSpace S] [BorelSpace S] in
/-- Bounded continuous functions are bounded by their sup norm. -/
theorem gp_bcf_abs_le_norm (f : S →ᵇ ℝ) (s : S) : |f s| ≤ ‖f‖ := by
  rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm s

/-- Point masses at a convergent sequence converge weakly. -/
theorem gp_convWeak_dirac {s : ℕ → S} {s₀ : S} (hs : Tendsto s atTop (𝓝 s₀)) :
    ConvWeak (fun n => Measure.dirac (s n)) (Measure.dirac s₀) := fun f => by
  simp only [integral_dirac]
  exact (f.continuous.tendsto s₀).comp hs

variable (κ : Kernel S S) [IsMarkovKernel κ]

omit [MetricSpace S] [BorelSpace S] [IsMarkovKernel κ] in
theorem gp_adjointOp_dirac (s : S) : adjointOp κ (Measure.dirac s) = κ s :=
  Measure.dirac_bind κ.measurable s

/-- `∫ Tf dλ = ∫ f d(T*λ)` for bounded continuous `f` (Theorem 8.3). -/
theorem gp_integral_markovOpR (lam : Measure S) [IsProbabilityMeasure lam] (f : S →ᵇ ℝ) :
    ∫ s, markovOpR κ f s ∂lam = ∫ s, f s ∂adjointOp κ lam :=
  slp_theorem_8_3_cor κ lam f.continuous.measurable (gp_bcf_abs_le_norm f)

/-- Under the Feller property, `Tf` as a bounded continuous function. -/
noncomputable def gp_fellerBCF {κ : Kernel S S} [IsMarkovKernel κ] (hF : IsFeller κ) (f : S →ᵇ ℝ) :
    S →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨markovOpR κ f, hF f f.continuous ⟨‖f‖, gp_bcf_abs_le_norm f⟩⟩ (2 * ‖f‖) fun x y => by
      have hx := (slp_theorem_8_1_cor κ f.continuous.measurable (gp_bcf_abs_le_norm f)).2 x
      have hy := (slp_theorem_8_1_cor κ f.continuous.measurable (gp_bcf_abs_le_norm f)).2 y
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      linarith [abs_sub (markovOpR κ f x) (markovOpR κ f y)]

theorem gp_fellerBCF_apply {κ : Kernel S S} [IsMarkovKernel κ] (hF : IsFeller κ) (f : S →ᵇ ℝ)
    (s : S) : gp_fellerBCF hF f s = markovOpR κ f s := rfl

/-- **Exercise 12.7.** On a metric space the following are equivalent: (a) the Feller property;
(b) `sₙ → s` implies `P(sₙ, ·) ⇒ P(s, ·)`; (c) `λₙ ⇒ λ` implies `T*λₙ ⇒ T*λ`. -/
theorem slp_ex_12_7 :
    (IsFeller κ ↔ ∀ (s : ℕ → S) (s₀ : S), Tendsto s atTop (𝓝 s₀) →
      ConvWeak (fun n => κ (s n)) (κ s₀)) ∧
    (IsFeller κ ↔ ∀ (ls : ℕ → Measure S) (lam : Measure S), (∀ n, IsProbabilityMeasure (ls n)) →
      IsProbabilityMeasure lam → ConvWeak ls lam →
        ConvWeak (fun n => adjointOp κ (ls n)) (adjointOp κ lam)) := by
  have hab : IsFeller κ ↔ ∀ (s : ℕ → S) (s₀ : S), Tendsto s atTop (𝓝 s₀) →
      ConvWeak (fun n => κ (s n)) (κ s₀) := by
    constructor
    · intro hF s s₀ hs f
      exact ((hF f f.continuous ⟨‖f‖, gp_bcf_abs_le_norm f⟩).tendsto s₀).comp hs
    · intro h f hf ⟨M, hM⟩
      rw [continuous_iff_seqContinuous]
      intro s s₀ hs
      exact h s s₀ hs (BoundedContinuousFunction.mkOfBound ⟨f, hf⟩ (2 * M) fun x y => by
        simp only [ContinuousMap.coe_mk, Real.dist_eq]
        linarith [abs_sub (f x) (f y), hM x, hM y])
  refine ⟨hab, ⟨fun hF ls lam hls hlam h f => ?_, fun h => hab.2 fun s s₀ hs => ?_⟩⟩
  · rw [← gp_integral_markovOpR κ lam f]
    exact (h (gp_fellerBCF hF f)).congr fun n => gp_integral_markovOpR κ (ls n) f
  · have := h _ _ (fun n => inferInstance) inferInstance (gp_convWeak_dirac hs)
    simpa only [gp_adjointOp_dirac] using this

/-! ### Exercise 12.8: the cycle `s ↦ 1 - s` -/

/-- The transition function of `sₜ₊₁ = 1 - sₜ` on `[0, 1]`: `P(s, ·) = δ_{1-s}`. -/
noncomputable def gp_flipKernel : Kernel unitInterval unitInterval :=
  Kernel.deterministic unitInterval.symm unitInterval.continuous_symm.measurable

theorem gp_isMarkovKernel_flipKernel : IsMarkovKernel gp_flipKernel := by
  unfold gp_flipKernel; infer_instance

theorem gp_adjointOp_flip (μ : Measure unitInterval) :
    adjointOp gp_flipKernel μ = μ.map unitInterval.symm :=
  Measure.deterministic_comp_eq_map _

theorem gp_adjointOp_flip_dirac (s : unitInterval) :
    adjointOp gp_flipKernel (Measure.dirac s) = Measure.dirac (unitInterval.symm s) := by
  rw [gp_adjointOp_flip, Measure.map_dirac' unitInterval.continuous_symm.measurable]

/-- **Exercise 12.8a.** `P(s, ·) = δ_{1-s}`, and `P` has the Feller property. -/
theorem slp_ex_12_8a : (∀ s, gp_flipKernel s = Measure.dirac (unitInterval.symm s)) ∧
    IsFeller gp_flipKernel := by
  have hP : ∀ s, gp_flipKernel s = Measure.dirac (unitInterval.symm s) := fun s =>
    Kernel.deterministic_apply _ s
  refine ⟨hP, fun f hf _ => ?_⟩
  have : markovOpR gp_flipKernel f = f ∘ unitInterval.symm := funext fun s => by
    simp only [markovOpR, hP, integral_dirac, Function.comp_apply]
  rw [this]
  exact hf.comp unitInterval.continuous_symm

theorem gp_iterate_flip_dirac (s : unitInterval) (n : ℕ) :
    (adjointOp gp_flipKernel)^[2 * n] (Measure.dirac s) = Measure.dirac s ∧
      (adjointOp gp_flipKernel)^[2 * n + 1] (Measure.dirac s) =
        Measure.dirac (unitInterval.symm s) := by
  induction n with
  | zero => exact ⟨rfl, gp_adjointOp_flip_dirac s⟩
  | succ n ih =>
    have h2 : 2 * (n + 1) = (2 * n + 1) + 1 := by ring
    rw [h2, Function.iterate_succ_apply', ih.2, gp_adjointOp_flip_dirac, unitInterval.symm_symm,
      Function.iterate_succ_apply', Function.iterate_succ_apply', ih.2, gp_adjointOp_flip_dirac,
      unitInterval.symm_symm, gp_adjointOp_flip_dirac]
    exact ⟨rfl, rfl⟩

theorem gp_symm_ne_self {s : unitInterval} (hs : (s : ℝ) ≠ 1 / 2) : unitInterval.symm s ≠ s := by
  intro h
  have := congrArg Subtype.val h
  rw [unitInterval.coe_symm_eq] at this
  exact hs (by linarith)

/-- **Exercise 12.8b.** From `δ_s` with `s ≠ 1/2`, the even iterates converge to `δ_s` and the odd
ones to `δ_{1-s}`; the two limits differ and neither is invariant. -/
theorem slp_ex_12_8b (s : unitInterval) (hs : (s : ℝ) ≠ 1 / 2) :
    ConvWeak (fun n => (adjointOp gp_flipKernel)^[2 * n] (Measure.dirac s)) (Measure.dirac s) ∧
      ConvWeak (fun n => (adjointOp gp_flipKernel)^[2 * n + 1] (Measure.dirac s))
        (Measure.dirac (unitInterval.symm s)) ∧
      Measure.dirac s ≠ Measure.dirac (unitInterval.symm s) ∧
      adjointOp gp_flipKernel (Measure.dirac s) ≠ Measure.dirac s ∧
      adjointOp gp_flipKernel (Measure.dirac (unitInterval.symm s)) ≠
        Measure.dirac (unitInterval.symm s) := by
  have hne : Measure.dirac s ≠ Measure.dirac (unitInterval.symm s) := fun h =>
    gp_symm_ne_self hs (dirac_eq_dirac_iff.1 h).symm
  refine ⟨fun f => ?_, fun f => ?_, hne, ?_, ?_⟩
  · simp only [fun n => (gp_iterate_flip_dirac s n).1]; exact tendsto_const_nhds
  · simp only [fun n => (gp_iterate_flip_dirac s n).2]; exact tendsto_const_nhds
  · rw [gp_adjointOp_flip_dirac]; exact hne.symm
  · rw [gp_adjointOp_flip_dirac, unitInterval.symm_symm]; exact hne

/-- **Exercise 12.8c.** The invariant measures are exactly the measures symmetric about `1/2`;
among them are `δ_{1/2}` and `½(δ_s + δ_{1-s})` for every `s`, so there are infinitely many. -/
theorem slp_ex_12_8c :
    (∀ μ : Measure unitInterval, adjointOp gp_flipKernel μ = μ ↔ μ.map unitInterval.symm = μ) ∧
      ∀ s : unitInterval, adjointOp gp_flipKernel
        ((2 : ℝ≥0∞)⁻¹ • (Measure.dirac s + Measure.dirac (unitInterval.symm s))) =
          (2 : ℝ≥0∞)⁻¹ • (Measure.dirac s + Measure.dirac (unitInterval.symm s)) := by
  refine ⟨fun μ => by rw [gp_adjointOp_flip], fun s => ?_⟩
  have hm := unitInterval.continuous_symm.measurable
  rw [gp_adjointOp_flip, Measure.map_smul, Measure.map_add _ _ hm, Measure.map_dirac' hm,
    Measure.map_dirac' hm, unitInterval.symm_symm, add_comm]
  exact hm.aemeasurable

/-! ### Invariant limits and Theorem 12.10 -/

variable {κ}

omit [MetricSpace S] [BorelSpace S] in
theorem gp_isProbabilityMeasure_iterate (lam : Measure S) [IsProbabilityMeasure lam] (n : ℕ) :
    IsProbabilityMeasure ((adjointOp κ)^[n] lam) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure lam)
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (slp_theorem_8_2 κ _).1

/-- If `νₙ ⇒ μ` and `⟨f, νₙ⟩ - ⟨f, T*νₙ⟩ → 0` for every bounded continuous `f`, then `μ` is
invariant under a Feller `P` (the limit step of Theorem 12.10). -/
theorem gp_invariant_of_convWeak (hF : IsFeller κ) {ν : ℕ → Measure S}
    [∀ n, IsProbabilityMeasure (ν n)] {μ : Measure S} [IsProbabilityMeasure μ]
    (hconv : ConvWeak ν μ)
    (hdiff : ∀ f : S →ᵇ ℝ, Tendsto (fun n => ∫ s, f s ∂ν n - ∫ s, f s ∂adjointOp κ (ν n))
      atTop (𝓝 0)) : adjointOp κ μ = μ := by
  have : IsProbabilityMeasure (adjointOp κ μ) := (slp_theorem_8_2 κ μ).1
  refine slp_theorem_12_6_cor2 fun f => ?_
  rw [← gp_integral_markovOpR κ μ f]
  have h1 : Tendsto (fun n => ∫ s, f s ∂adjointOp κ (ν n)) atTop (𝓝 (∫ s, f s ∂μ)) := by
    have := (hconv f).sub (hdiff f)
    simp only [sub_sub_cancel, sub_zero] at this
    exact this
  exact tendsto_nhds_unique ((hconv (gp_fellerBCF hF f)).congr fun n =>
    gp_integral_markovOpR κ (ν n) f) h1

/-- **Theorem 12.10.** On a nonempty compact metric space, a transition function with the Feller
property has an invariant probability measure. -/
theorem slp_theorem_12_10 [CompactSpace S] [Nonempty S] (hF : IsFeller κ) :
    ∃ μ : Measure S, IsProbabilityMeasure μ ∧ adjointOp κ μ = μ := by
  have : TopologicalSpace.SeparableSpace S := inferInstance
  set lam₀ := Measure.dirac (Classical.arbitrary S)
  set L : ℕ → Measure S := fun n => (adjointOp κ)^[n] lam₀
  have hL : ∀ n, IsProbabilityMeasure (L n) := fun n => gp_isProbabilityMeasure_iterate lam₀ n
  have hLs : ∀ n, L (n + 1) = adjointOp κ (L n) := fun n => Function.iterate_succ_apply' _ _ _
  set c : ℕ → ℝ≥0∞ := fun N => ((N : ℝ≥0∞) + 1)⁻¹
  have hc : ∀ N, (c N).toReal = ((N : ℝ) + 1)⁻¹ := fun N => by
    simp only [c, ENNReal.toReal_inv]
    rw [ENNReal.toReal_add (ENNReal.natCast_ne_top N) ENNReal.one_ne_top]
    simp
  set avg : ℕ → Measure S := fun N => c N • ∑ n ∈ Finset.range (N + 1), L n
  have havg : ∀ N, IsProbabilityMeasure (avg N) := fun N => ⟨by
    simp only [avg, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, measure_univ,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, smul_eq_mul, c]
    push_cast
    exact ENNReal.inv_mul_cancel (by positivity)
      (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top N, ENNReal.one_ne_top⟩)⟩
  have hint : ∀ N (g : S →ᵇ ℝ), ∫ s, g s ∂avg N =
      ((N : ℝ) + 1)⁻¹ * ∑ n ∈ Finset.range (N + 1), ∫ s, g s ∂L n := fun N g => by
    simp only [avg]
    rw [integral_smul_measure, integral_finsetSum_measure fun n _ => g.integrable _, hc,
      smul_eq_mul]
  have hintT : ∀ N (g : S →ᵇ ℝ), ∫ s, g s ∂adjointOp κ (avg N) =
      ((N : ℝ) + 1)⁻¹ * ∑ n ∈ Finset.range (N + 1), ∫ s, g s ∂L (n + 1) := fun N g => by
    rw [← gp_integral_markovOpR κ (avg N) g]
    change ∫ s, gp_fellerBCF hF g s ∂avg N = _
    rw [hint]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hLs, ← gp_integral_markovOpR κ (L n) g]
    rfl
  obtain ⟨μ, hμ, φ, hφ, hconv⟩ := gp_exists_convWeak_subseq_of_tight avg fun ε hε =>
    ⟨univ, isCompact_univ, fun n => by rw [probReal_univ]; linarith⟩
  have : ∀ n, IsProbabilityMeasure ((avg ∘ φ) n) := fun n => havg (φ n)
  refine ⟨μ, hμ, gp_invariant_of_convWeak hF hconv fun f => ?_⟩
  have hdiff : ∀ N, ∫ s, f s ∂avg N - ∫ s, f s ∂adjointOp κ (avg N) =
      ((N : ℝ) + 1)⁻¹ * (∫ s, f s ∂L 0 - ∫ s, f s ∂L (N + 1)) := fun N => by
    rw [hint, hintT, ← mul_sub, ← Finset.sum_sub_distrib, Finset.sum_range_sub']
  have hbd : ∀ n, |∫ s, f s ∂L n| ≤ ‖f‖ := fun n => by
    rw [← Real.norm_eq_abs]
    exact f.norm_integral_le_norm (L n)
  have hlim : Tendsto (fun N : ℕ => ∫ s, f s ∂avg N - ∫ s, f s ∂adjointOp κ (avg N)) atTop
      (𝓝 0) := by
    simp_rw [hdiff]
    refine squeeze_zero_norm (a := fun N : ℕ => ((N : ℝ) + 1)⁻¹ * (2 * ‖f‖)) (fun N => ?_) ?_
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity)]
      gcongr
      linarith [abs_sub (∫ s, f s ∂L 0) (∫ s, f s ∂L (N + 1)), hbd 0, hbd (N + 1)]
    · simpa using (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add
        (tendsto_const_nhds (x := (1 : ℝ))))).mul_const (2 * ‖f‖)
  exact hlim.comp hφ.tendsto_atTop

end Miao.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Weak convergence: tightness, Prohorov, the Feller property and Krylov–Bogolubov

Miao, §3.3.2, pp. 108–111. `X` is a metric space with its Borel σ-algebra.

* **Definition 3.3.2**: `λₙ ⇒ λ` is SLP's `ConvWeak` (`definition_3_3_2`). Strong convergence
  implies weak convergence (p. 104, `eq_p104_strong_imp_weak`), and `δ_{1/(n+1)} ⇒ δ₀` weakly but
  not strongly (p. 108, `eq_p108_dirac`).
* **Definition 3.3.3**: tight families (`IsTightFamily`).
* **Theorem 3.3.2** (Prohorov). As printed ("there exist `μ` and a subsequence `μₙₖ ⇒ μ` iff
  `{μₙ}` is tight") the "only if" is false: on `ℝ`, `μₙ = δ₀` for even `n` and `μₙ = δₙ` for odd
  `n` has the convergent subsequence `(δ₀)` but is not tight (`theorem_3_3_2_counterexample`).
  Proved: on a complete separable metric space `{μₙ}` is tight iff every subsequence has a
  weakly convergent further subsequence (`theorem_3_3_2`). Tight ⇒ convergent subsequence is
  Mathlib's Prokhorov theorem (via SLP's `gp_exists_convWeak_subseq_of_tight`), and it needs no
  completeness. The converse follows Mathlib's `isTightMeasureSet_of_isCompact_closure`, with
  its compactness hypothesis replaced by the sequential one and the portmanteau theorem
  (SLP Theorem 12.3).
* **Definition 3.3.4**: the Feller property is SLP's `IsFeller` (`definition_3_3_4`).
* **Theorem 3.3.3** (Krylov–Bogolubov, `theorem_3_3_3`): the book's proof with the Cesàro
  averages `(1/n) Σ_{k ≤ n} Pᵏ(x, ·)`. Completeness of `X` is not needed.
* **Corollary 3.3.1** (`corollary_3_3_1`), SLP Theorem 12.10. Departure: `X` must be nonempty.
-/

namespace Miao.MarkovProcesses

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- **Definition 3.3.3** (Miao, p. 109): a family `M` of probability measures is **tight** if for
every `ε > 0` there is a compact `K` with `λ(K) ≥ 1 − ε` for all `λ ∈ M`. -/
def IsTightFamily [TopologicalSpace X] (M : Set (Measure X)) : Prop :=
  ∀ ε > 0, ∃ K, IsCompact K ∧ ∀ lam ∈ M, 1 - ε ≤ lam.real K

/-- **Definition 3.3.2** (Miao, p. 109): `λₙ ⇒ λ` iff `∫ f dλₙ → ∫ f dλ` for every bounded
continuous `f`. -/
theorem definition_3_3_2 [MetricSpace X] (ls : ℕ → Measure X) (l : Measure X) :
    ConvWeak ls l ↔ ∀ f : X →ᵇ ℝ, Tendsto (fun n => ∫ x, f x ∂ls n) atTop (𝓝 (∫ x, f x ∂l)) :=
  Iff.rfl

/-- **Definition 3.3.4** (Miao, p. 110): `P` has the **Feller property** iff `T` maps the bounded
continuous functions into themselves. -/
theorem definition_3_3_4 [MetricSpace X] [BorelSpace X] (κ : Kernel X X) [IsMarkovKernel κ] :
    IsFeller κ ↔ ∀ f : X →ᵇ ℝ, ∃ g : X →ᵇ ℝ, ⇑g = markovOpR κ f := by
  constructor
  · intro hF f
    exact ⟨gp_fellerBCF hF f, rfl⟩
  · rintro h f hf ⟨M, hM⟩
    have hb : ∀ x y, dist (f x) (f y) ≤ 2 * M := fun x y => by
      rw [Real.dist_eq]; linarith [abs_sub (f x) (f y), hM x, hM y]
    obtain ⟨g, hg⟩ := h (BoundedContinuousFunction.mkOfBound ⟨f, hf⟩ (2 * M) hb)
    have : markovOpR κ f = g := hg.symm
    rw [this]
    exact g.continuous

/-- Tight sequences have weakly convergent subsequences (Prokhorov). -/
theorem gp_exists_convWeak_subseq [MetricSpace X] [TopologicalSpace.SeparableSpace X]
    [BorelSpace X] (μ : ℕ → Measure X) [∀ n, IsProbabilityMeasure (μ n)]
    (h : IsTightFamily (Set.range μ)) :
    ∃ ν : Measure X, IsProbabilityMeasure ν ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvWeak (μ ∘ φ) ν :=
  gp_exists_convWeak_subseq_of_tight μ fun ε hε => by
    obtain ⟨K, hK, hKμ⟩ := h (ε / 2) (by positivity)
    exact ⟨K, hK, fun n => by linarith [hKμ (μ n) ⟨n, rfl⟩]⟩

/-- **Theorem 3.3.2** (Prohorov, Miao, p. 109), corrected. On a complete separable metric space
a sequence of probability measures is tight iff every subsequence (indeed every sequence
`μ ∘ ψ`) has a weakly convergent subsequence. -/
theorem theorem_3_3_2 [MetricSpace X] [TopologicalSpace.SeparableSpace X] [CompleteSpace X]
    [BorelSpace X] (μ : ℕ → Measure X) [∀ n, IsProbabilityMeasure (μ n)] :
    IsTightFamily (Set.range μ) ↔ ∀ ψ : ℕ → ℕ, ∃ ν : Measure X, IsProbabilityMeasure ν ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvWeak (fun k => μ (ψ (φ k))) ν := by
  constructor
  · intro h ψ
    have : ∀ n, IsProbabilityMeasure ((μ ∘ ψ) n) := fun n => inferInstanceAs
      (IsProbabilityMeasure (μ (ψ n)))
    obtain ⟨ν, hν, φ, hφ, hc⟩ := gp_exists_convWeak_subseq (μ ∘ ψ) fun ε hε => by
      obtain ⟨K, hK, hKμ⟩ := h ε hε
      exact ⟨K, hK, fun lam ⟨n, hn⟩ => hKμ lam ⟨ψ n, hn⟩⟩
    exact ⟨ν, hν, φ, hφ, hc⟩
  · intro H ε hε
    have : Nonempty X := nonempty_of_isProbabilityMeasure (μ 0)
    obtain ⟨D, hD⟩ := TopologicalSpace.exists_dense_seq X
    set u : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
    have hu : ∀ m, 0 < u m := fun m => by positivity
    set G : ℕ → ℕ → Set X := fun m k => ⋃ i ∈ Finset.range (k + 1), Metric.ball (D i) (u m)
    have hGo : ∀ m k, IsOpen (G m k) := fun m k => isOpen_biUnion fun i _ => Metric.isOpen_ball
    have hGmono : ∀ m, Monotone (G m) := fun m k k' hkk' =>
      Set.biUnion_subset_biUnion_left fun i hi => by
        simp only [Finset.coe_range, Set.mem_Iio] at hi ⊢; omega
    have hGU : ∀ m, ⋃ k, G m k = Set.univ := fun m => by
      refine Set.eq_univ_of_forall fun x => ?_
      obtain ⟨i, hi⟩ := hD.exists_dist_lt x (hu m)
      exact Set.mem_iUnion.2 ⟨i, Set.mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_self i))
        (by rw [Metric.mem_ball]; exact hi)⟩
    have claim : ∀ m (δ : ℝ), 0 < δ → ∃ k, ∀ n, 1 - δ < (μ n).real (G m k) := by
      intro m δ hδ
      by_contra hcon
      push Not at hcon
      choose ψ hψ using hcon
      obtain ⟨ν, hν, φ, hφ, hconv⟩ := H ψ
      have hlim := (slp_theorem_12_3 _ ν).2.1.1 hconv
      have hbound : ∀ j, ν.real (G m j) ≤ 1 - δ / 2 := by
        intro j
        have ev := hlim (G m j) (hGo m j) (δ / 2) (half_pos hδ)
        obtain ⟨k, hk1, hk2⟩ := (ev.and (eventually_ge_atTop j)).exists
        have : (μ (ψ (φ k))).real (G m j) ≤ (μ (ψ (φ k))).real (G m (φ k)) :=
          measureReal_mono (hGmono m (hk2.trans (hφ.id_le k))) (measure_ne_top _ _)
        linarith [hψ (φ k)]
      have htend : Tendsto (fun j => ν.real (G m j)) atTop (𝓝 (ν.real Set.univ)) := by
        have := tendsto_measure_iUnion_atTop (μ := ν) (hGmono m)
        rw [hGU m] at this
        exact (ENNReal.tendsto_toReal (measure_ne_top ν _)).comp this
      rw [probReal_univ] at htend
      have := le_of_tendsto' htend hbound
      linarith
    set δ : ℕ → ℝ := fun m => ε / 2 / 2 ^ m
    have hδ : ∀ m, 0 < δ m := fun m => by positivity
    choose k hk using fun m => claim m (δ m) (hδ m)
    set C : ℕ → Set X := fun m => ⋃ i ∈ Finset.range (k m + 1), Metric.closedBall (D i) (u m)
    have hGC : ∀ m, G m (k m) ⊆ C m := fun m =>
      Set.biUnion_mono subset_rfl fun i _ => Metric.ball_subset_closedBall
    have hCc : ∀ m, IsClosed (C m) := fun m =>
      isClosed_biUnion_finset fun i _ => Metric.isClosed_closedBall
    set K := ⋂ m, C m
    have hKc : IsClosed K := isClosed_iInter hCc
    have hKt : TotallyBounded K := by
      refine Metric.totallyBounded_iff.2 fun r hr => ?_
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hr
      refine ⟨D '' (Finset.range (k m + 1) : Set ℕ), (Finset.finite_toSet _).image _, ?_⟩
      intro x hx
      have hxC := Set.mem_iInter.1 hx m
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hxC
      refine Set.mem_iUnion₂.2 ⟨D i, ⟨i, hi, rfl⟩, ?_⟩
      exact Metric.closedBall_subset_ball hm hxi
    refine ⟨K, hKt.isCompact_of_isClosed hKc, ?_⟩
    rintro _ ⟨n, rfl⟩
    have hCn : ∀ m, μ n (C m)ᶜ ≤ ENNReal.ofReal (δ m) := fun m => by
      rw [← ofReal_measureReal]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [probReal_compl_eq_one_sub (hCc m).measurableSet]
      linarith [hk m n, measureReal_mono (μ := μ n) (hGC m) (measure_ne_top _ _)]
    have hKn : μ n Kᶜ ≤ ENNReal.ofReal ε := by
      calc μ n Kᶜ = μ n (⋃ m, (C m)ᶜ) := by rw [Set.compl_iInter]
        _ ≤ ∑' m, μ n (C m)ᶜ := measure_iUnion_le _
        _ ≤ ∑' m, ENNReal.ofReal (δ m) := ENNReal.tsum_le_tsum hCn
        _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => (hδ m).le) (summable_geometric_two' ε),
            tsum_geometric_two']
    have hKr : (μ n).real Kᶜ ≤ ε := by
      rw [measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal hε.le hKn
    rw [probReal_compl_eq_one_sub hKc.measurableSet] at hKr
    linarith

/-- **Theorem 3.3.2** as printed is false (Miao, p. 109): on `ℝ` the sequence `δ₀, δ₁, δ₀, δ₃, …`
(`μₙ = δ₀` for even `n`, `δₙ` for odd `n`) has a weakly convergent subsequence but is not
tight. -/
theorem theorem_3_3_2_counterexample :
    let μ : ℕ → Measure ℝ := fun n => if Even n then Measure.dirac 0 else Measure.dirac (n : ℝ)
    (∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvWeak (μ ∘ φ) ν) ∧
      ¬ IsTightFamily (Set.range μ) := by
  intro μ
  refine ⟨⟨Measure.dirac 0, inferInstance, fun k => 2 * k, fun a b hab => by
    change 2 * a < 2 * b; omega,
    fun f => ?_⟩, fun h => ?_⟩
  · have : (fun n => ∫ x, f x ∂(μ ∘ fun k => 2 * k) n) = fun _ => ∫ x, f x ∂Measure.dirac 0 :=
      funext fun n => by simp [μ]
    rw [this]
    exact tendsto_const_nhds
  · obtain ⟨K, hK, hKμ⟩ := h (1 / 2) (by norm_num)
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hK.isBounded
    set n := 2 * ⌈R⌉₊ + 1
    have hodd : ¬ Even n := by simp [n]
    have hnR : R < (n : ℝ) := by
      have := Nat.le_ceil R
      simp only [n]
      push_cast
      linarith [show (0 : ℝ) ≤ ⌈R⌉₊ from Nat.cast_nonneg _]
    have hnK : (n : ℝ) ∉ K := fun hn => by
      have := hR hn
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg (Nat.cast_nonneg _)] at this
      linarith
    have := hKμ (μ n) ⟨n, rfl⟩
    simp only [μ, hodd, ↓reduceIte] at this
    rw [measureReal_def, Measure.dirac_apply' _ hK.measurableSet,
      Set.indicator_of_notMem hnK] at this
    norm_num at this

/-- Miao, p. 104: strong convergence implies weak convergence. -/
theorem eq_p104_strong_imp_weak [MetricSpace X] [BorelSpace X] (ls : ℕ → Measure X)
    (l : Measure X) [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure l]
    (h : ConvStrongly ls l) : ConvWeak ls l := by
  intro f
  set C := ‖f‖ + 1
  have hC : 0 < C := by positivity
  have hg : ∀ x, |f x / C| ≤ 1 := fun x => by
    rw [abs_div, abs_of_pos hC, div_le_one hC]
    exact (gp_bcf_abs_le_norm f x).trans (by linarith)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    ((h.const_mul (2 * C)).trans_eq (by rw [mul_zero]) :
      Tendsto (fun n => 2 * C * dTV (ls n) l) atTop (𝓝 0))
  have := gp_abs_integral_sub_le_tvDist (ls n) l (f.continuous.measurable.div_const C) hg
  rw [integral_div, integral_div, ← sub_div, abs_div, abs_of_pos hC, div_le_iff₀ hC,
    gp_tvDist_eq_two_mul_dTV] at this
  rw [Real.norm_eq_abs]
  linarith

/-- Miao, p. 108: `δ_{1/(n+1)} ⇒ δ₀` weakly, but `dTV(δ_{1/(n+1)}, δ₀) = 1` for all `n`, so the
convergence is not strong. -/
theorem eq_p108_dirac :
    ConvWeak (fun n : ℕ => Measure.dirac (1 / ((n : ℝ) + 1))) (Measure.dirac 0) ∧
      ∀ n : ℕ, dTV (Measure.dirac (1 / ((n : ℝ) + 1))) (Measure.dirac (0 : ℝ)) = 1 := by
  refine ⟨gp_convWeak_dirac tendsto_one_div_add_atTop_nhds_zero_nat, fun n => ?_⟩
  refine le_antisymm (gp_dTV_le_one _ _) ?_
  have h := gp_abs_le_dTV (Measure.dirac (1 / ((n : ℝ) + 1))) (Measure.dirac (0 : ℝ))
    (MeasurableSet.singleton 0)
  have hne : (1 / ((n : ℝ) + 1)) ∉ ({0} : Set ℝ) := by
    rw [Set.mem_singleton_iff]; positivity
  have e1 : (Measure.dirac (1 / ((n : ℝ) + 1))).real {0} = 0 := by
    rw [measureReal_def, Measure.dirac_apply' _ (MeasurableSet.singleton 0),
      Set.indicator_of_notMem hne, ENNReal.toReal_zero]
  have e2 : (Measure.dirac (0 : ℝ)).real {0} = 1 := by simp
  rw [e1, e2, zero_sub, abs_neg, abs_one] at h
  exact h

/-- **Theorem 3.3.3** (Krylov–Bogolubov, Miao, p. 110). If `P` is Feller on a separable metric
space and `{Pⁿ(x, ·)}_{n ≥ 1}` is tight for some `x`, then `P` has an invariant probability
measure. The proof is the book's: a weak limit of the Cesàro averages of `Pⁿ(x, ·)`. -/
theorem theorem_3_3_3 [MetricSpace X] [TopologicalSpace.SeparableSpace X] [BorelSpace X]
    {κ : Kernel X X} [IsMarkovKernel κ] (hF : IsFeller κ) {x : X}
    (htight : IsTightFamily {lam | ∃ n, 1 ≤ n ∧ lam = kpow κ n x}) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧ adjointOp κ μ = μ := by
  set lam₀ := κ x
  set L : ℕ → Measure X := fun n => (adjointOp κ)^[n] lam₀
  have hL : ∀ n, IsProbabilityMeasure (L n) := fun n => gp_isProbabilityMeasure_iterate lam₀ n
  have hLs : ∀ n, L (n + 1) = adjointOp κ (L n) := fun n => Function.iterate_succ_apply' _ _ _
  have hLk : ∀ n, L n = kpow κ (n + 1) x := fun n => by
    simp only [L, lam₀]
    rw [← gp_adjointOp_dirac κ x, ← Function.iterate_succ_apply, gp_adjointOp_iterate,
      gp_adjointOp_dirac]
  set c : ℕ → ℝ≥0∞ := fun N => ((N : ℝ≥0∞) + 1)⁻¹
  have hc : ∀ N, (c N).toReal = ((N : ℝ) + 1)⁻¹ := fun N => by
    simp only [c, ENNReal.toReal_inv]
    rw [ENNReal.toReal_add (ENNReal.natCast_ne_top N) ENNReal.one_ne_top]
    simp
  have hc1 : ∀ N, c N * ((N : ℝ≥0∞) + 1) = 1 := fun N =>
    ENNReal.inv_mul_cancel (by positivity)
      (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top N, ENNReal.one_ne_top⟩)
  set avg : ℕ → Measure X := fun N => c N • ∑ n ∈ Finset.range (N + 1), L n
  have havg : ∀ N, IsProbabilityMeasure (avg N) := fun N => ⟨by
    simp only [avg, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, measure_univ,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, smul_eq_mul]
    push_cast
    exact hc1 N⟩
  have hint : ∀ N (g : X →ᵇ ℝ), ∫ s, g s ∂avg N =
      ((N : ℝ) + 1)⁻¹ * ∑ n ∈ Finset.range (N + 1), ∫ s, g s ∂L n := fun N g => by
    simp only [avg]
    rw [integral_smul_measure, integral_finsetSum_measure fun n _ => g.integrable _, hc,
      smul_eq_mul]
  have hintT : ∀ N (g : X →ᵇ ℝ), ∫ s, g s ∂adjointOp κ (avg N) =
      ((N : ℝ) + 1)⁻¹ * ∑ n ∈ Finset.range (N + 1), ∫ s, g s ∂L (n + 1) := fun N g => by
    rw [← gp_integral_markovOpR κ (avg N) g]
    change ∫ s, gp_fellerBCF hF g s ∂avg N = _
    rw [hint]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hLs, ← gp_integral_markovOpR κ (L n) g]
    rfl
  -- the Cesàro averages are tight
  have htavg : ∀ ε > 0, ∃ K, IsCompact K ∧ ∀ N, 1 - ε < (avg N).real K := by
    intro ε hε
    obtain ⟨K, hK, hKL⟩ := htight (ε / 2) (by positivity)
    refine ⟨K, hK, fun N => ?_⟩
    have hLK : ∀ n, ENNReal.ofReal (1 - ε / 2) ≤ L n K := fun n => by
      rw [← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal (hKL _ ⟨n + 1, by omega, hLk n⟩)
    have hle : ENNReal.ofReal (1 - ε / 2) ≤ avg N K := by
      calc ENNReal.ofReal (1 - ε / 2)
          = c N * (((N : ℝ≥0∞) + 1) * ENNReal.ofReal (1 - ε / 2)) := by
            rw [← mul_assoc, hc1, one_mul]
        _ ≤ c N * ∑ n ∈ Finset.range (N + 1), L n K := by
            gcongr
            calc ((N : ℝ≥0∞) + 1) * ENNReal.ofReal (1 - ε / 2)
                = ∑ n ∈ Finset.range (N + 1), ENNReal.ofReal (1 - ε / 2) := by
                  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; rfl
              _ ≤ ∑ n ∈ Finset.range (N + 1), L n K := Finset.sum_le_sum fun n _ => hLK n
        _ = avg N K := by
            simp only [avg, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
              smul_eq_mul]
    have := ENNReal.toReal_mono (measure_ne_top _ K) hle
    rw [ENNReal.toReal_ofReal'] at this
    rw [measureReal_def]
    linarith [le_max_left (1 - ε / 2) 0]
  obtain ⟨μ, hμ, φ, hφ, hconv⟩ := gp_exists_convWeak_subseq_of_tight avg htavg
  have : ∀ n, IsProbabilityMeasure ((avg ∘ φ) n) := fun n => havg (φ n)
  refine ⟨μ, hμ, gp_invariant_of_convWeak hF hconv fun f => ?_⟩
  have hdiff : ∀ N, ∫ s, f s ∂avg N - ∫ s, f s ∂adjointOp κ (avg N) =
      ((N : ℝ) + 1)⁻¹ * (∫ s, f s ∂L 0 - ∫ s, f s ∂L (N + 1)) := fun N => by
    rw [hint, hintT, ← mul_sub, ← Finset.sum_sub_distrib, Finset.sum_range_sub']
  have hbd : ∀ n, |∫ s, f s ∂L n| ≤ ‖f‖ := fun n => by
    rw [← Real.norm_eq_abs]
    exact f.norm_integral_le_norm (L n)
  have hlim : Tendsto (fun N : ℕ => ∫ s, f s ∂avg N - ∫ s, f s ∂adjointOp κ (avg N)) atTop
      (𝓝 0) := by
    simp_rw [hdiff]
    refine squeeze_zero_norm (a := fun N : ℕ => ((N : ℝ) + 1)⁻¹ * (2 * ‖f‖)) (fun N => ?_) ?_
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity)]
      gcongr
      linarith [abs_sub (∫ s, f s ∂L 0) (∫ s, f s ∂L (N + 1)), hbd 0, hbd (N + 1)]
    · simpa using (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add
        (tendsto_const_nhds (x := (1 : ℝ))))).mul_const (2 * ‖f‖)
  exact hlim.comp hφ.tendsto_atTop

/-- **Corollary 3.3.1** (Miao, p. 111; SLP Theorem 12.10). On a nonempty compact metric space
every Feller transition function has an invariant distribution. -/
theorem corollary_3_3_1 [MetricSpace X] [CompactSpace X] [Nonempty X] [BorelSpace X]
    {κ : Kernel X X} [IsMarkovKernel κ] (hF : IsFeller κ) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧ adjointOp κ μ = μ :=
  slp_theorem_12_10 hF

end Miao.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Invariant sets, ergodic measures and Theorem 3.3.4

Miao, §3.3.2, pp. 111–112.

* **Definition 3.3.5**: `P`-invariant sets (`IsPInvariantSet`) and ergodic measures
  (`IsErgodicMeasure`). The book's definition of an *ergodic set* (`IsErgodicSetBook`: `E` with
  `P(x, E) = 1` for `π`-a.e. `x ∈ E` and no proper subset with this property) is defective: `∅`
  has the property vacuously and is a proper subset of every nonempty set, so the only ergodic
  set is `∅` (`definition_3_3_5_ergodicSet_eq_empty`).
* The example on p. 111: for `P(0, ·) = δ₀`, `P(1, ·) = δ₁` every probability measure is invariant
  (`example_p111_invariant`), and `π` is ergodic iff `π{0} ∈ {0, 1}`, so `δ₀` and `δ₁` are the
  ergodic measures (`example_p111_ergodic`). (The book calls `{0}` "a `δ{0}`-invariant set";
  invariance of a set refers to `P`, and `{0}`, `{1}` are `P`-invariant.)
* **Theorem 3.3.4** (the book refers to the Birkhoff theorem of Chapter 4). Proved here directly:
  - `I` is convex (`theorem_3_3_4_convex`);
  - `E` is the set of extreme points of `I` (`theorem_3_3_4_extreme`). If `A` is invariant with
    `0 < π(A) < 1`, `π` is the average of its normalised restrictions to `A` and `Aᶜ`, both
    invariant. Conversely, if `π` is ergodic and `π = aπ₁ + bπ₂`, the density `h = dπ₁/dπ` has
    `{h > 1}` invariant up to a `π`-null set (`gp_ae_invariant_of_density`, comparing `π₁` with the
    invariant measure with density `min(h, 1)`), hence it contains an invariant set of the same
    measure (`gp_exists_invariantSet`); ergodicity forces `h = 1`;
  - distinct ergodic measures are mutually singular (`theorem_3_3_4_singular`), by the same
    argument applied to `π₁` and `(π₁ + π₂)/2`.
  - "Every invariant measure is a convex combination of ergodic measures" is false for finite
    convex combinations: for `P(x, ·) = δₓ` on `ℝ` the uniform distribution on `[0, 1]` is
    invariant but is no finite combination of ergodic measures
    (`theorem_3_3_4_combination_counterexample`). The correct statement is the ergodic
    decomposition (an integral over ergodic measures, for standard Borel spaces), which is not
    formalised here.
-/

namespace Miao.MarkovProcesses

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- A **`P`-invariant set** (Miao, Definition 3.3.5, p. 111): `P(x, A) = 1` for every `x ∈ A`. -/
def IsPInvariantSet (κ : Kernel X X) (A : Set X) : Prop :=
  MeasurableSet A ∧ ∀ x ∈ A, κ x A = 1

/-- An **ergodic** invariant measure (Miao, Definition 3.3.5, p. 111): `π(A) ∈ {0, 1}` for every
`P`-invariant set `A`. -/
def IsErgodicMeasure (κ : Kernel X X) (π : Measure X) : Prop :=
  IsInvariantDist κ π ∧ ∀ A, IsPInvariantSet κ A → π A = 0 ∨ π A = 1

/-- The book's **ergodic set** (Miao, Definition 3.3.5, p. 111), literally: `P(x, E) = 1` for
`π`-a.e. `x ∈ E`, and no proper subset of `E` has this property. -/
def IsErgodicSetBook (κ : Kernel X X) (π : Measure X) (E : Set X) : Prop :=
  MeasurableSet E ∧ (∀ᵐ x ∂π, x ∈ E → κ x E = 1) ∧
    ∀ F, F ⊂ E → MeasurableSet F → ¬ ∀ᵐ x ∂π, x ∈ F → κ x F = 1

/-- **Definition 3.3.5** (Miao, p. 111) is defective: the empty set has the defining property
and is a proper subset of every nonempty set, so the only "ergodic set" is `∅`. -/
theorem definition_3_3_5_ergodicSet_eq_empty {κ : Kernel X X} {π : Measure X} {E : Set X}
    (h : IsErgodicSetBook κ π E) : E = ∅ := by
  by_contra hE
  exact h.2.2 ∅ (Set.empty_ssubset.2 (Set.nonempty_iff_ne_empty.2 hE)) MeasurableSet.empty
    (ae_of_all _ fun x hx => absurd hx (Set.notMem_empty x))

/-- Miao, p. 111: for `P(0, ·) = δ₀`, `P(1, ·) = δ₁` (the identity kernel on `{0, 1}`) every
probability measure is invariant. -/
theorem example_p111_invariant (π : Measure (Fin 2)) [IsProbabilityMeasure π] :
    IsInvariantDist Kernel.id π :=
  ⟨inferInstance, (gp_adjointOp_iterate (Kernel.id : Kernel (Fin 2) (Fin 2)) 0 π).symm⟩

/-- Miao, pp. 111–112: for the identity kernel on `{0, 1}`, `π` is ergodic iff `π{0} = 0` or
`π{0} = 1`; so `δ₀` and `δ₁` are the ergodic measures, and `π = pδ₀ + (1 − p)δ₁` is ergodic only
for `p ∈ {0, 1}`. -/
theorem example_p111_ergodic (π : Measure (Fin 2)) [IsProbabilityMeasure π] :
    IsErgodicMeasure Kernel.id π ↔ π {0} = 0 ∨ π {0} = 1 := by
  constructor
  · rintro ⟨-, h⟩
    exact h {0} ⟨MeasurableSet.singleton 0, fun x hx => by
      rw [Set.mem_singleton_iff] at hx; subst hx; simp [Kernel.id_apply]⟩
  · intro h0
    refine ⟨example_p111_invariant π, fun A _ => ?_⟩
    have h1 : π {1} = 1 - π {0} := by
      rw [← prob_compl_eq_one_sub (MeasurableSet.singleton 0)]
      congr 1
      ext x; fin_cases x <;> simp
    have hd : ∀ y : Fin 2, π {y} = 1 → π = Measure.dirac y := fun y hy => by
      rw [Measure.ext_iff_singleton]
      intro a
      by_cases ha : a = y
      · subst ha; simp [hy]
      · have : π {a} = 0 := by
          refine le_antisymm ?_ zero_le
          have := prob_add_prob_compl (μ := π) (MeasurableSet.singleton y)
          rw [hy] at this
          calc π {a} ≤ π {y}ᶜ :=
              measure_mono (Set.singleton_subset_iff.2 (Set.mem_compl_singleton_iff.2 ha))
            _ = 0 := by
              have h2 : (1 : ℝ≥0∞) + π {y}ᶜ = 1 + 0 := by rw [this, add_zero]
              exact (ENNReal.add_right_inj ENNReal.one_ne_top).1 h2
        rw [this, Measure.dirac_apply' _ (MeasurableSet.singleton a),
          Set.indicator_of_notMem (Set.notMem_singleton_iff.2 (Ne.symm ha))]
    have hA : ∀ y : Fin 2, (Measure.dirac y) A = 0 ∨ (Measure.dirac y) A = 1 := fun y => by
      by_cases hy : y ∈ A
      · exact Or.inr (Measure.dirac_apply_of_mem hy)
      · left; simp [Measure.dirac_apply' _ (MeasurableSet.of_discrete), hy]
    rcases h0 with h0 | h0
    · rw [hd 1 (by rw [h1, h0, tsub_zero])]; exact hA 1
    · rw [hd 0 h0]; exact hA 0

/-- `T*` is affine: `T*(aμ + bν) = aT*μ + bT*ν`. -/
theorem gp_adjointOp_add_smul (κ : Kernel X X) (μ ν : Measure X) (a b : ℝ≥0∞) :
    adjointOp κ (a • μ + b • ν) = a • adjointOp κ μ + b • adjointOp κ ν := by
  ext A hA
  simp only [gp_adjointOp_apply κ _ hA, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  rfl

/-- `T*(cμ) = cT*μ`. -/
theorem gp_adjointOp_smul (κ : Kernel X X) (μ : Measure X) (c : ℝ≥0∞) :
    adjointOp κ (c • μ) = c • adjointOp κ μ := by
  ext A hA
  simp only [gp_adjointOp_apply κ _ hA, Measure.smul_apply, smul_eq_mul]
  rw [lintegral_smul_measure]
  rfl

/-- **Theorem 3.3.4** (Miao, p. 112): the set `I` of invariant probability measures is convex. -/
theorem theorem_3_3_4_convex (κ : Kernel X X) :
    Convex ℝ≥0∞ {π : Measure X | IsInvariantDist κ π} := by
  rintro π₁ ⟨h₁, e₁⟩ π₂ ⟨h₂, e₂⟩ a b - - hab
  refine ⟨⟨?_⟩, ?_⟩
  · simp [hab]
  · rw [gp_adjointOp_add_smul, e₁, e₂]

/-- `T*(μ.withDensity f)(A) = ∫ f(x) P(x, A) μ(dx)`. -/
theorem gp_adjointOp_withDensity (κ : Kernel X X) (μ : Measure X) {f : X → ℝ≥0∞}
    (hf : Measurable f) {A : Set X} (hA : MeasurableSet A) :
    adjointOp κ (μ.withDensity f) A = ∫⁻ x, f x * κ x A ∂μ := by
  rw [gp_adjointOp_apply κ _ hA, lintegral_withDensity_eq_lintegral_mul _ hf (κ.measurable_coe hA)]
  rfl

/-- If a measurable `f ≤ 1` has `∫ f dμ = 1` for a probability measure `μ`, then `f = 1`
`μ`-a.e. -/
theorem gp_ae_eq_one_of_lintegral {μ : Measure X} [IsProbabilityMeasure μ] {f : X → ℝ≥0∞}
    (hf : Measurable f) (h1 : ∀ x, f x ≤ 1) (hint : ∫⁻ x, f x ∂μ = 1) : ∀ᵐ x ∂μ, f x = 1 := by
  have h0 : ∫⁻ x, (1 - f x) ∂μ = 0 := by
    rw [lintegral_sub hf (by rw [hint]; exact ENNReal.one_ne_top) (ae_of_all _ h1), hint]
    simp
  replace h0 := (lintegral_eq_zero_iff (f := fun x => 1 - f x) (measurable_const.sub hf)).1 h0
  filter_upwards [h0] with x hx
  exact le_antisymm (h1 x) (tsub_eq_zero_iff_le.1 hx)

/-- A set that is invariant up to a null set of an invariant `π` contains an invariant set of the
same `π`-measure: if `P(x, B) = 1` for `π`-a.e. `x ∈ B`, then
`B' = {x : Pⁿ(x, B) = 1 for all n}` is `P`-invariant, `B' ⊆ B` and `π(B \ B') = 0`. -/
theorem gp_exists_invariantSet (κ : Kernel X X) [IsMarkovKernel κ] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : adjointOp κ π = π) {B : Set X} (hB : MeasurableSet B)
    (hae : ∀ᵐ x ∂π, x ∈ B → κ x B = 1) :
    ∃ B', B' ⊆ B ∧ IsPInvariantSet κ B' ∧ π (B \ B') = 0 := by
  set Bn : ℕ → Set X := fun n => {x | kpow κ n x B = 1}
  have hBn : ∀ n, MeasurableSet (Bn n) := fun n =>
    (Kernel.measurable_coe (kpow κ n) hB) (measurableSet_singleton 1)
  have hB0 : Bn 0 = B := by
    ext x
    by_cases hx : x ∈ B <;> simp [Bn, kpow, Kernel.id_apply, Measure.dirac_apply' _ hB, hx]
  have hstep : ∀ n x, kpow κ (n + 1) x B = ∫⁻ y, kpow κ n y B ∂κ x := fun n x => by
    rw [eq_3_5 κ n 1 x hB, gp_kpow_one]
  have hmk : ∀ n, IsMarkovKernel (kpow κ n) := theorem_3_2_5 κ
  refine ⟨⋂ n, Bn n, fun x hx => hB0 ▸ Set.mem_iInter.1 hx 0, ⟨MeasurableSet.iInter hBn,
    fun x hx => ?_⟩, ?_⟩
  · -- invariance
    have hc : ∀ n, κ x (Bn n)ᶜ = 0 := fun n => by
      have h1 : ∫⁻ y, kpow κ n y B ∂κ x = 1 := by
        rw [← hstep]; exact Set.mem_iInter.1 hx (n + 1)
      have := gp_ae_eq_one_of_lintegral (μ := κ x) (Kernel.measurable_coe _ hB)
        (fun y => prob_le_one) h1
      rw [ae_iff] at this
      exact this
    rw [← prob_compl_eq_zero_iff (MeasurableSet.iInter hBn), Set.compl_iInter]
    exact measure_iUnion_null hc
  · -- `π(B \ B') = 0`
    have hnull : ∀ n, π (B \ Bn n) = 0 := by
      intro n
      induction n with
      | zero => rw [hB0, Set.sdiff_self, measure_empty]
      | succ n ih =>
        set N := B \ Bn n
        have hN : MeasurableSet N := hB.diff (hBn n)
        have hκN : ∀ᵐ x ∂π, κ x N = 0 := by
          have : ∫⁻ x, κ x N ∂π = 0 := by rw [← gp_adjointOp_apply κ π hN, hπ, ih]
          exact (lintegral_eq_zero_iff (κ.measurable_coe hN)).1 this
        have hgood : ∀ᵐ x ∂π, x ∈ B → x ∈ Bn (n + 1) := by
          filter_upwards [hae, hκN] with x hx1 hx2 hxB
          have hBN : κ x (B \ N) = 1 := by rw [measure_sdiff_null hx2, hx1 hxB]
          refine le_antisymm prob_le_one ?_
          rw [hstep, ← hBN, ← lintegral_indicator_one (hB.diff hN)]
          refine lintegral_mono fun y => ?_
          by_cases hy : y ∈ B \ N
          · rw [Set.indicator_of_mem hy, Pi.one_apply]
            have : y ∈ Bn n := by
              by_contra hyn
              exact hy.2 ⟨hy.1, hyn⟩
            exact le_of_eq this.symm
          · rw [Set.indicator_of_notMem hy]; exact zero_le
        rw [ae_iff] at hgood
        refine le_antisymm (le_of_eq_of_le ?_ hgood.le) zero_le
        congr 1
        ext x
        simp
    rw [Set.sdiff_iInter]
    exact measure_iUnion_null hnull

/-- If `π` and `π.withDensity h` are invariant (the latter finite), the set `{h > 1}` is
invariant up to a `π`-null set. The invariant measure with density `min(h, 1)` is subinvariant,
hence invariant, so the measure with density `h − min(h, 1)`, which lives on `{h > 1}`, is
invariant too. -/
theorem gp_ae_invariant_of_density (κ : Kernel X X) [IsMarkovKernel κ] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : adjointOp κ π = π) {h : X → ℝ≥0∞} (hh : Measurable h)
    (hπ₁ : adjointOp κ (π.withDensity h) = π.withDensity h) :
    ∀ᵐ x ∂π, x ∈ {x | 1 < h x} → κ x {x | 1 < h x} = 1 := by
  set B := {x | 1 < h x}
  have hB : MeasurableSet B := measurableSet_lt measurable_const hh
  set g : X → ℝ≥0∞ := fun x => min (h x) 1
  have hg : Measurable g := hh.min measurable_const
  set ρ := π.withDensity g
  set D := {x | h x ≤ 1}
  have hD : MeasurableSet D := measurableSet_le hh measurable_const
  have hgh : ∀ x, g x ≤ h x := fun x => min_le_left _ _
  have hhg : Measurable fun x => h x - g x := hh.sub hg
  have hg1 : ∀ x, g x ≤ 1 := fun x => min_le_right _ _
  have hρfin : ∀ A, ρ A ≠ ∞ := fun A => by
    refine ne_top_of_le_ne_top (measure_ne_top π Set.univ) ?_
    calc ρ A ≤ ρ Set.univ := measure_mono (Set.subset_univ A)
      _ = ∫⁻ x, g x ∂π := by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      _ ≤ ∫⁻ _, 1 ∂π := lintegral_mono hg1
      _ = π Set.univ := by simp
  -- Step 1: `T*ρ ≤ ρ`
  have hsub : ∀ A, MeasurableSet A → adjointOp κ ρ A ≤ ρ A := by
    intro A hA
    have h1 : adjointOp κ ρ (A ∩ D) ≤ ρ (A ∩ D) := by
      calc adjointOp κ ρ (A ∩ D) = ∫⁻ x, g x * κ x (A ∩ D) ∂π :=
            gp_adjointOp_withDensity κ π hg (hA.inter hD)
        _ ≤ ∫⁻ x, h x * κ x (A ∩ D) ∂π := lintegral_mono fun x => mul_le_mul_left (hgh x) _
        _ = π.withDensity h (A ∩ D) := by
            rw [← gp_adjointOp_withDensity κ π hh (hA.inter hD), hπ₁]
        _ = ρ (A ∩ D) := by
            rw [withDensity_apply _ (hA.inter hD), withDensity_apply _ (hA.inter hD)]
            refine setLIntegral_congr_fun (hA.inter hD) fun x hx => ?_
            exact (min_eq_left hx.2).symm
    have h2 : adjointOp κ ρ (A \ D) ≤ ρ (A \ D) := by
      calc adjointOp κ ρ (A \ D) = ∫⁻ x, g x * κ x (A \ D) ∂π :=
            gp_adjointOp_withDensity κ π hg (hA.diff hD)
        _ ≤ ∫⁻ x, κ x (A \ D) ∂π := lintegral_mono fun x => by
            calc g x * κ x (A \ D) ≤ 1 * κ x (A \ D) := mul_le_mul_left (hg1 x) _
              _ = κ x (A \ D) := one_mul _
        _ = π (A \ D) := by rw [← gp_adjointOp_apply κ π (hA.diff hD), hπ]
        _ = ρ (A \ D) := by
            rw [withDensity_apply _ (hA.diff hD), ← setLIntegral_one]
            refine setLIntegral_congr_fun (hA.diff hD) fun x hx => ?_
            have : 1 < h x := lt_of_not_ge hx.2
            exact (min_eq_right this.le).symm
    calc adjointOp κ ρ A = adjointOp κ ρ (A ∩ D) + adjointOp κ ρ (A \ D) :=
          (measure_inter_add_sdiff A hD).symm
      _ ≤ ρ (A ∩ D) + ρ (A \ D) := add_le_add h1 h2
      _ = ρ A := measure_inter_add_sdiff A hD
  -- Step 2: `T*ρ = ρ`
  have hρuniv : adjointOp κ ρ Set.univ = ρ Set.univ := by
    rw [gp_adjointOp_withDensity κ π hg MeasurableSet.univ, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
    simp
  have hinv : ∀ A, MeasurableSet A → adjointOp κ ρ A = ρ A := by
    intro A hA
    refine le_antisymm (hsub A hA) ?_
    have e1 := measure_add_measure_compl (μ := ρ) hA
    have e2 := measure_add_measure_compl (μ := adjointOp κ ρ) hA
    rw [hρuniv, ← e1] at e2
    refine ENNReal.le_of_add_le_add_right (hρfin Aᶜ) ?_
    calc ρ A + ρ Aᶜ = adjointOp κ ρ A + adjointOp κ ρ Aᶜ := e2.symm
      _ ≤ adjointOp κ ρ A + ρ Aᶜ := add_le_add le_rfl (hsub Aᶜ hA.compl)
  -- Step 3: the measure `σ` with density `h - g` is invariant on `Bᶜ`
  have hsplit : ∀ A, MeasurableSet A →
      π.withDensity h A = π.withDensity (fun x => h x - g x) A + ρ A := fun A hA => by
    rw [withDensity_apply _ hA, withDensity_apply _ hA, withDensity_apply _ hA,
      ← lintegral_add_right _ hg]
    exact lintegral_congr fun x => (tsub_add_cancel_of_le (hgh x)).symm
  have hσ : adjointOp κ (π.withDensity fun x => h x - g x) Bᶜ =
      π.withDensity (fun x => h x - g x) Bᶜ := by
    have hm2 : Measurable fun x => g x * κ x Bᶜ := hg.mul (κ.measurable_coe hB.compl)
    have e : adjointOp κ (π.withDensity h) Bᶜ =
        adjointOp κ (π.withDensity fun x => h x - g x) Bᶜ + adjointOp κ ρ Bᶜ := by
      rw [gp_adjointOp_withDensity κ π hh hB.compl,
        gp_adjointOp_withDensity κ π hhg hB.compl,
        gp_adjointOp_withDensity κ π hg hB.compl, ← lintegral_add_right _ hm2]
      refine lintegral_congr fun x => ?_
      rw [← add_mul, tsub_add_cancel_of_le (hgh x)]
    rw [hπ₁, hsplit _ hB.compl, hinv _ hB.compl] at e
    exact ((ENNReal.add_left_inj (hρfin _)).1 e).symm
  -- Step 4: `σ(Bᶜ) = 0`, so `P(x, Bᶜ) = 0` for `π`-a.e. `x ∈ B`
  have hσ0 : π.withDensity (fun x => h x - g x) Bᶜ = 0 := by
    rw [withDensity_apply _ hB.compl]
    refine (setLIntegral_congr_fun hB.compl fun x hx => ?_).trans (lintegral_zero)
    have hx' : h x ≤ 1 := not_lt.1 hx
    simp [g, min_eq_left hx']
  rw [← hσ, gp_adjointOp_withDensity κ π hhg hB.compl,
    lintegral_eq_zero_iff (f := fun x => (h x - g x) * κ x Bᶜ)
      (hhg.mul (κ.measurable_coe hB.compl))] at hσ0
  filter_upwards [hσ0] with x hx hxB
  have hpos : h x - g x ≠ 0 := by
    have : 1 < h x := hxB
    simp only [g, min_eq_right this.le]
    exact (tsub_pos_of_lt this).ne'
  have : κ x Bᶜ = 0 := (mul_eq_zero.1 hx).resolve_left hpos
  exact (prob_compl_eq_zero_iff hB).1 this

/-- The key lemma for Theorem 3.3.4. If `π` and `π₁ ≪ π` are invariant probability measures,
there is a `P`-invariant set `B'` (built from `{dπ₁/dπ > 1}`) with `π(B') ≠ 1` and such that
`π₁(B') = 0` forces `π₁ = π`. -/
theorem gp_density_invariantSet (κ : Kernel X X) [IsMarkovKernel κ] {π π₁ : Measure X}
    [IsProbabilityMeasure π] [IsProbabilityMeasure π₁] (hπ : adjointOp κ π = π)
    (hπ₁ : adjointOp κ π₁ = π₁) (hac : π₁ ≪ π) :
    ∃ B', IsPInvariantSet κ B' ∧ (π₁ B' = 0 → π₁ = π) ∧ π B' ≠ 1 := by
  set h := π₁.rnDeriv π
  have hh : Measurable h := Measure.measurable_rnDeriv _ _
  have hπ1eq : π.withDensity h = π₁ := Measure.withDensity_rnDeriv_eq _ _ hac
  have hint : ∫⁻ x, h x ∂π = 1 := by
    rw [← Measure.restrict_univ (μ := π), ← withDensity_apply _ MeasurableSet.univ, hπ1eq,
      measure_univ]
  set B := {x | 1 < h x}
  have hB : MeasurableSet B := measurableSet_lt measurable_const hh
  have hae := gp_ae_invariant_of_density κ hπ hh (by rw [hπ1eq]; exact hπ₁)
  obtain ⟨B', hB'B, hB'inv, hnull⟩ := gp_exists_invariantSet κ hπ hB hae
  refine ⟨B', hB'inv, fun h0 => ?_, fun h1 => ?_⟩
  · -- `π₁(B') = 0` gives `π(B) = 0`, so `h ≤ 1`, so `h = 1`
    have hπ₁B : π₁ B = 0 := by
      refine le_antisymm ?_ zero_le
      calc π₁ B ≤ π₁ (B \ B') + π₁ B' := by
            rw [← measure_union Set.disjoint_sdiff_left hB'inv.1, Set.sdiff_union_self]
            exact measure_mono Set.subset_union_left
        _ = 0 := by rw [hac hnull, h0, add_zero]
    have hπB : π B = 0 := by
      refine le_antisymm ?_ zero_le
      calc π B = ∫⁻ _ in B, 1 ∂π := by rw [setLIntegral_one]
        _ ≤ ∫⁻ x in B, h x ∂π := setLIntegral_mono hh fun x hx => le_of_lt hx
        _ = π₁ B := by rw [← withDensity_apply _ hB, hπ1eq]
        _ = 0 := hπ₁B
    have hle : ∀ᵐ x ∂π, h x ≤ 1 := by
      rw [ae_iff]
      simpa [B, not_le] using hπB
    have h0' : ∫⁻ x, (1 - h x) ∂π = 0 := by
      rw [lintegral_sub hh (by rw [hint]; exact ENNReal.one_ne_top) hle, hint]
      simp
    have hge := (lintegral_eq_zero_iff (f := fun x => 1 - h x) (measurable_const.sub hh)).1 h0'
    have heq : h =ᵐ[π] 1 := by
      filter_upwards [hle, hge] with x hx1 hx2
      exact le_antisymm hx1 (tsub_eq_zero_iff_le.1 hx2)
    rw [← hπ1eq, withDensity_congr_ae heq, withDensity_one]
  · -- `π(B') = 1` is impossible: `h > 1` a.e. contradicts `∫ h dπ = 1`
    have hπB : π Bᶜ = 0 := by
      have : π B = 1 := le_antisymm prob_le_one (h1 ▸ measure_mono hB'B)
      exact (prob_compl_eq_zero_iff hB).2 this
    have hgt : ∀ᵐ x ∂π, 1 < h x := by
      have e : {x | ¬ 1 < h x} = Bᶜ := by ext x; simp [B]
      rw [ae_iff, e]
      exact hπB
    have h0' : ∫⁻ x, (h x - 1) ∂π = 0 := by
      rw [lintegral_sub measurable_const (by simp) (hgt.mono fun x hx => hx.le), hint]
      simp
    have hle := (lintegral_eq_zero_iff (f := fun x => h x - 1) (hh.sub measurable_const)).1 h0'
    have hfalse : ∀ᵐ x ∂π, False := by
      filter_upwards [hgt, hle] with x hx1 hx2
      exact absurd (tsub_eq_zero_iff_le.1 hx2) (not_le.2 hx1)
    rw [ae_iff] at hfalse
    simp at hfalse

/-- **Theorem 3.3.4** (Miao, p. 112): the ergodic measures are exactly the extreme points of the
convex set `I` of invariant probability measures. -/
theorem theorem_3_3_4_extreme (κ : Kernel X X) [IsMarkovKernel κ] (π : Measure X) :
    IsErgodicMeasure κ π ↔ π ∈ Set.extremePoints ℝ≥0∞ {π : Measure X | IsInvariantDist κ π} := by
  constructor
  · rintro ⟨⟨hπp, hπ⟩, herg⟩
    refine mem_extremePoints.2 ⟨⟨hπp, hπ⟩, ?_⟩
    have key : ∀ π₁ : Measure X, IsInvariantDist κ π₁ → ∀ a b : ℝ≥0∞, 0 < a →
        ∀ π₂ : Measure X, a • π₁ + b • π₂ = π → π₁ = π := by
      rintro π₁ ⟨hp₁, hi₁⟩ a b ha π₂ hsum
      have hac : π₁ ≪ π := fun A hA => by
        have : a * π₁ A ≤ π A := by
          rw [← hsum, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
          exact le_self_add
        rw [hA, nonpos_iff_eq_zero, mul_eq_zero] at this
        exact this.resolve_left ha.ne'
      obtain ⟨B', hB', himp, hne⟩ := gp_density_invariantSet κ hπ hi₁ hac
      rcases herg B' hB' with h0 | h1
      · exact himp (hac h0)
      · exact absurd h1 hne
    intro π₁ h₁ π₂ h₂ ⟨a, b, ha, hb, hab, hsum⟩
    refine ⟨key π₁ h₁ a b ha π₂ hsum, key π₂ h₂ b a hb π₁ ?_⟩
    rw [add_comm]; exact hsum
  · intro hext
    obtain ⟨⟨hπp, hπ⟩, hext'⟩ := mem_extremePoints.1 hext
    refine ⟨⟨hπp, hπ⟩, fun A hA => ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hA0, hA1⟩ := hcon
    have hAc0 : π Aᶜ ≠ 0 := fun h => hA1 ((prob_compl_eq_zero_iff hA.1).1 h)
    have hAc1 : π Aᶜ ≠ ∞ := measure_ne_top _ _
    have hAt : π A ≠ ∞ := measure_ne_top _ _
    -- the restrictions to `A` and `Aᶜ` are invariant
    have hzero : ∫⁻ x in Aᶜ, κ x A ∂π = 0 := by
      have e := lintegral_add_compl (fun x => κ x A) (μ := π) hA.1
      rw [← gp_adjointOp_apply κ π hA.1, hπ, setLIntegral_congr_fun hA.1 hA.2,
        setLIntegral_const, one_mul] at e
      have : π A + ∫⁻ x in Aᶜ, κ x A ∂π = π A + 0 := by rw [e, add_zero]
      exact (ENNReal.add_right_inj hAt).1 this
    have hresA : adjointOp κ (π.restrict A) = π.restrict A := by
      ext B hB
      rw [gp_adjointOp_apply κ _ hB, Measure.restrict_apply hB]
      have e1 : ∀ x ∈ A, κ x B = κ x (B ∩ A) := fun x hx => by
        have : κ x Aᶜ = 0 := (prob_compl_eq_zero_iff hA.1).2 (hA.2 x hx)
        rw [← measure_inter_add_sdiff B hA.1, Set.sdiff_eq,
          measure_mono_null Set.inter_subset_right this, add_zero]
      have e2 : ∫⁻ x in Aᶜ, κ x (B ∩ A) ∂π = 0 :=
        le_antisymm ((setLIntegral_mono (κ.measurable_coe hA.1) fun x _ =>
          measure_mono Set.inter_subset_right).trans hzero.le) zero_le
      have e3 := lintegral_add_compl (fun x => κ x (B ∩ A)) (μ := π) hA.1
      rw [e2, add_zero, ← gp_adjointOp_apply κ π (hB.inter hA.1), hπ] at e3
      rw [setLIntegral_congr_fun hA.1 e1, e3]
    have hresAc : adjointOp κ (π.restrict Aᶜ) = π.restrict Aᶜ := by
      have hadd : adjointOp κ π = adjointOp κ (π.restrict A) + adjointOp κ (π.restrict Aᶜ) := by
        have := gp_adjointOp_add_smul κ (π.restrict A) (π.restrict Aᶜ) 1 1
        rw [one_smul, one_smul, one_smul, one_smul, Measure.restrict_add_restrict_compl hA.1]
          at this
        exact this
      ext B hB
      have e := congrArg (fun μ : Measure X => μ B) hadd
      simp only [Measure.add_apply] at e
      rw [hπ, hresA] at e
      have e2 : π B = π.restrict A B + π.restrict Aᶜ B := by
        rw [← Measure.add_apply, Measure.restrict_add_restrict_compl hA.1]
      rw [e2] at e
      exact ((ENNReal.add_right_inj (measure_ne_top (π.restrict A) B)).1 e).symm
    set π₁ := (π A)⁻¹ • π.restrict A
    set π₂ := (π Aᶜ)⁻¹ • π.restrict Aᶜ
    have hp : ∀ (C : Set X), MeasurableSet C → π C ≠ 0 → π C ≠ ∞ →
        IsProbabilityMeasure ((π C)⁻¹ • π.restrict C) := fun C hC h0 ht => ⟨by
      rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        smul_eq_mul, ENNReal.inv_mul_cancel h0 ht]⟩
    have h₁ : IsInvariantDist κ π₁ :=
      ⟨hp A hA.1 hA0 hAt, by rw [gp_adjointOp_smul, hresA]⟩
    have h₂ : IsInvariantDist κ π₂ :=
      ⟨hp Aᶜ hA.1.compl hAc0 hAc1, by rw [gp_adjointOp_smul, hresAc]⟩
    have hseg : π ∈ openSegment ℝ≥0∞ π₁ π₂ := by
      refine ⟨π A, π Aᶜ, pos_iff_ne_zero.2 hA0, pos_iff_ne_zero.2 hAc0,
        by rw [measure_add_measure_compl hA.1, measure_univ], ?_⟩
      simp only [π₁, π₂, smul_smul, ENNReal.mul_inv_cancel hA0 hAt,
        ENNReal.mul_inv_cancel hAc0 hAc1, one_smul]
      exact Measure.restrict_add_restrict_compl hA.1
    have h1 := (hext' π₁ h₁ π₂ h₂ hseg).1
    have : π₁ A = 1 := by
      simp only [π₁, Measure.smul_apply, Measure.restrict_apply hA.1, Set.inter_self, smul_eq_mul]
      exact ENNReal.inv_mul_cancel hA0 hAt
    exact hA1 (h1 ▸ this)

/-- **Theorem 3.3.4** (Miao, p. 112): two distinct ergodic measures are mutually singular. -/
theorem theorem_3_3_4_singular (κ : Kernel X X) [IsMarkovKernel κ] {π₁ π₂ : Measure X}
    (h₁ : IsErgodicMeasure κ π₁) (h₂ : IsErgodicMeasure κ π₂) (hne : π₁ ≠ π₂) :
    π₁ ⟂ₘ π₂ := by
  obtain ⟨⟨hp₁, hi₁⟩, he₁⟩ := h₁
  obtain ⟨⟨hp₂, hi₂⟩, he₂⟩ := h₂
  set π := (2⁻¹ : ℝ≥0∞) • π₁ + (2⁻¹ : ℝ≥0∞) • π₂
  have hhalf : (2⁻¹ : ℝ≥0∞) + 2⁻¹ = 1 := ENNReal.inv_two_add_inv_two
  have hπ : IsInvariantDist κ π :=
    theorem_3_3_4_convex κ ⟨hp₁, hi₁⟩ ⟨hp₂, hi₂⟩ (zero_le) (zero_le) hhalf
  obtain ⟨hπp, hπi⟩ := hπ
  have hac : π₁ ≪ π := fun A hA => by
    have : 2⁻¹ * π₁ A ≤ π A := by
      simp only [π, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      exact le_self_add
    rw [hA, nonpos_iff_eq_zero, mul_eq_zero] at this
    exact this.resolve_left (by simp)
  obtain ⟨B', hB', himp, hne1⟩ := gp_density_invariantSet κ hπi hi₁ hac
  have hB'm := hB'.1
  rcases he₁ B' hB' with h0 | h1
  · exfalso
    have heq := himp h0
    refine hne ?_
    rw [heq]
    ext A hA
    have e : π A = 2⁻¹ * π A + 2⁻¹ * π₂ A := by
      conv_lhs => rw [show π = (2⁻¹ : ℝ≥0∞) • π₁ + (2⁻¹ : ℝ≥0∞) • π₂ from rfl]
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      rw [heq]
    have hfin : 2⁻¹ * π A ≠ ∞ := ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
    have e2 : 2⁻¹ * π A + 2⁻¹ * π A = 2⁻¹ * π A + 2⁻¹ * π₂ A := by
      rw [← add_mul, hhalf, one_mul]; exact e
    have e3 := (ENNReal.add_right_inj hfin).1 e2
    exact (ENNReal.mul_right_inj (by simp) (by simp)).1 e3
  · rcases he₂ B' hB' with h0' | h1'
    · exact ⟨B'ᶜ, hB'm.compl, (prob_compl_eq_zero_iff hB'm).2 h1, by rw [compl_compl]; exact h0'⟩
    · exfalso
      refine hne1 ?_
      simp only [π, Measure.add_apply, Measure.smul_apply, smul_eq_mul, h1, h1', mul_one, hhalf]

/-- **Theorem 3.3.4** (Miao, p. 112): "every invariant measure is a convex combination of
ergodic measures" is false for finite convex combinations. For `P(x, ·) = δₓ` on `ℝ` the uniform
distribution on `[0, 1]` is invariant, but it is not `Σᵢ tᵢπᵢ` for any finitely many ergodic
`πᵢ`: every ergodic `πᵢ` gives mass `0` or `1` to every Borel set, so some interval
`[j/(n+1), (j+1)/(n+1))` is null for all of them. -/
theorem theorem_3_3_4_combination_counterexample :
    IsInvariantDist (Kernel.id : Kernel ℝ ℝ) (volume.restrict (Set.Icc (0 : ℝ) 1)) ∧
      ¬ ∃ (n : ℕ) (t : Fin n → ℝ≥0∞) (πs : Fin n → Measure ℝ),
        (∀ i, IsErgodicMeasure Kernel.id (πs i)) ∧
          volume.restrict (Set.Icc (0 : ℝ) 1) = ∑ i, t i • πs i := by
  have hprob : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  refine ⟨⟨hprob, (gp_adjointOp_iterate (Kernel.id : Kernel ℝ ℝ) 0 _).symm⟩, ?_⟩
  rintro ⟨n, t, πs, herg, hsum⟩
  -- every Borel set is invariant, so ergodic measures are `0`–`1` valued
  have h01 : ∀ i A, MeasurableSet A → πs i A = 0 ∨ πs i A = 1 := fun i A hA =>
    (herg i).2 A ⟨hA, fun x hx => by simp [Kernel.id_apply, Measure.dirac_apply_of_mem hx]⟩
  have hprobi : ∀ i, IsProbabilityMeasure (πs i) := fun i => (herg i).1.1
  set I : Fin (n + 1) → Set ℝ := fun j =>
    Set.Ico ((j : ℝ) / (n + 1)) (((j : ℝ) + 1) / (n + 1))
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hIsub : ∀ j, I j ⊆ Set.Icc 0 1 := fun j x hx => by
    obtain ⟨h1, h2⟩ := hx
    have hj : ((j : ℕ) : ℝ) + 1 ≤ n + 1 := by
      have := j.2; exact_mod_cast Nat.succ_le_of_lt this
    refine ⟨le_trans (by positivity) h1, h2.le.trans ?_⟩
    rw [div_le_one hn]; exact hj
  have hIpos : ∀ j, volume.restrict (Set.Icc (0 : ℝ) 1) (I j) ≠ 0 := fun j => by
    rw [Measure.restrict_apply measurableSet_Ico, Set.inter_eq_left.2 (hIsub j), Real.volume_Ico]
    refine (ENNReal.ofReal_pos.2 ?_).ne'
    rw [← sub_div, add_sub_cancel_left]
    positivity
  have hdisj : ∀ j j', j ≠ j' → Disjoint (I j) (I j') := fun j j' hjj' => by
    rw [Set.disjoint_left]
    rintro x ⟨a1, a2⟩ ⟨b1, b2⟩
    have c1 : ((j : ℕ) : ℝ) < (j' : ℕ) + 1 := by
      have := a1.trans_lt b2; rwa [div_lt_div_iff_of_pos_right hn] at this
    have c2 : ((j' : ℕ) : ℝ) < (j : ℕ) + 1 := by
      have := b1.trans_lt a2; rwa [div_lt_div_iff_of_pos_right hn] at this
    have d1 : (j : ℕ) < j' + 1 := by exact_mod_cast c1
    have d2 : (j' : ℕ) < j + 1 := by exact_mod_cast c2
    exact hjj' (Fin.ext (by omega))
  -- each interval gets mass `1` from some `πᵢ`
  have hpick : ∀ j, ∃ i, πs i (I j) = 1 := fun j => by
    by_contra hcon
    push Not at hcon
    have hz : ∀ i, πs i (I j) = 0 := fun i =>
      (h01 i (I j) measurableSet_Ico).resolve_right (hcon i)
    refine hIpos j ?_
    rw [hsum, Measure.coe_finsetSum, Finset.sum_apply]
    exact Finset.sum_eq_zero fun i _ => by simp [hz i]
  choose f hf using hpick
  have hinj : Function.Injective f := fun j j' hjj' => by
    by_contra hne
    have hu := measure_union (μ := πs (f j)) (hdisj j j' hne) measurableSet_Ico
    rw [hf j, hjj', hf j'] at hu
    have : πs (f j') (I j ∪ I j') ≤ 1 := prob_le_one
    rw [hu] at this
    norm_num at this
  have := Fintype.card_le_of_injective f hinj
  simp at this

end Miao.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Monotone Markov processes (SLP §12.4, pp. 378–383)

Copied from `RecursiveMethods/WeakConvergence` (SLP Chapter 12, module `MonotoneProcesses.lean`),
with the
namespace renamed to `Miao.MarkovProcesses`, the results numbered in SLP prefixed
`slp_` and the helper lemmas and definitions prefixed `gp_`.

* **dominance** `μ ≥ λ` (p. 378): `⟨f, μ⟩ ≥ ⟨f, λ⟩` for all bounded measurable nondecreasing `f`;
* **Exercise 12.9**: dominance orders distribution functions the other way (`slp_ex_12_9a`); on `ℝ`
  the converse holds (`slp_ex_12_9b`, via the layer-cake formula and the classification of lower
  sets of `ℝ`); on `ℝ²` it fails (`slp_ex_12_9c`, `μ = ½(δ_{(1,0)} + δ_{(0,1)})`,
  `λ = ½(δ_{(0,0)} + δ_{(1,1)})`);
* **Exercise 12.10**: squeezing between dominance-ordered weakly convergent sequences (for any
  `S ⊆ ℝˡ`, not only rectangles);
* **Exercise 12.11**: `P` monotone ⇔ `T*` preserves dominance ⇔ `s ≥ s′ ⇒ P(s, ·) ≥ P(s′, ·)`;
* monotone sequences of measures on `[a, b]` converge weakly (`gp_convWeak_of_dominance_mono`, from
  Corollary 2 to Helly);
* **Exercise 12.12**: `T*ⁿδ_a` increases and `T*ⁿδ_b` decreases, and both converge to invariant
  measures;
* **Assumption 12.1**, **Exercise 12.14**, **Lemma 12.11** and **Theorem 12.12** (a monotone Feller
  process satisfying the mixing condition has a unique invariant measure, which is globally
  stable). The proof of Theorem 12.12 supplies the two steps the book leaves implicit: the lower
  bound `(Tⁿf)(b) - (Tⁿf)(a) ≥ 0`, and uniqueness from global convergence.
-/

namespace Miao.MarkovProcesses

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal

/-! ### Dominance -/

variable {S : Type*} [MeasurableSpace S] [Preorder S]

/-- `μ` **dominates** `λ` (SLP p. 378): `⟨f, μ⟩ ≥ ⟨f, λ⟩` for every bounded measurable
nondecreasing `f`. -/
def Dominates (μ lam : Measure S) : Prop :=
  ∀ f : S → ℝ, Measurable f → (∃ M, ∀ s, |f s| ≤ M) → Monotone f → ∫ s, f s ∂lam ≤ ∫ s, f s ∂μ

theorem Dominates.trans {μ ν lam : Measure S} (h1 : Dominates μ ν) (h2 : Dominates ν lam) :
    Dominates μ lam := fun f hf hb hm => (h2 f hf hb hm).trans (h1 f hf hb hm)

/-- Dominance compares the masses of measurable upper sets. -/
theorem Dominates.real_le {μ lam : Measure S} (h : Dominates μ lam) {U : Set S}
    (hU : MeasurableSet U) (hup : IsUpperSet U) : lam.real U ≤ μ.real U := by
  have hm : Monotone (U.indicator (1 : S → ℝ)) := fun s t hst => by
    by_cases hs : s ∈ U
    · simp [hs, hup hst hs]
    · rw [indicator_of_notMem hs]; exact indicator_nonneg (fun _ _ => zero_le_one) t
  have := h (U.indicator 1) (measurable_const.indicator hU) ⟨1, fun s => by
    by_cases hs : s ∈ U
    · rw [indicator_of_mem hs, Pi.one_apply, abs_one]
    · rw [indicator_of_notMem hs, abs_zero]; exact zero_le_one⟩ hm
  rwa [integral_indicator_one hU, integral_indicator_one hU] at this

variable {l : ℕ}

/-- **Exercise 12.9a.** If `μ ≥ λ` on `ℝˡ` then `F_μ ≤ F_λ`. -/
theorem slp_ex_12_9a {μ lam : Measure (Fin l → ℝ)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure lam] (h : Dominates μ lam) (x : Fin l → ℝ) :
    gp_distFun μ x ≤ gp_distFun lam x := by
  have := h.real_le measurableSet_Iic.compl (isLowerSet_Iic x).compl
  rw [probReal_compl_eq_one_sub measurableSet_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
    at this
  simp only [gp_distFun]; linarith

/-- **Exercise 12.9a** on `S ⊆ ℝˡ`: if `μ ≥ λ` then `μ(S ∩ (-∞, x]) ≤ λ(S ∩ (-∞, x])` for every
`x ∈ ℝˡ`. -/
theorem slp_ex_12_9a_subtype {S : Set (Fin l → ℝ)} {μ lam : Measure S} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure lam] (h : Dominates μ lam) (x : Fin l → ℝ) :
    μ.real (Subtype.val ⁻¹' Iic x) ≤ lam.real (Subtype.val ⁻¹' Iic x) := by
  have hm : MeasurableSet (Subtype.val ⁻¹' Iic x : Set S) :=
    measurableSet_Iic.preimage measurable_subtype_coe
  have := h.real_le hm.compl (fun s t (hst : (s : Fin l → ℝ) ≤ t) hs ht => hs (hst.trans ht))
  rw [probReal_compl_eq_one_sub hm, probReal_compl_eq_one_sub hm] at this
  linarith

/-- On `ℝ`, `F_μ ≤ F_λ` gives `μ(L) ≤ λ(L)` for every lower set `L`: `L` is `∅`, `ℝ`,
`(-∞, c]` or `(-∞, c)`. -/
theorem gp_measure_lower_le {μ lam : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure lam]
    (h : ∀ x, μ.real (Iic x) ≤ lam.real (Iic x)) {L : Set ℝ} (hL : IsLowerSet L) :
    μ L ≤ lam L := by
  have hE : ∀ x, μ (Iic x) ≤ lam (Iic x) := fun x =>
    (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).1 (h x)
  rcases L.eq_empty_or_nonempty with rfl | hne
  · simp
  by_cases hbdd : BddAbove L
  · by_cases hc : sSup L ∈ L
    · have : L = Iic (sSup L) :=
        Subset.antisymm (fun y hy => le_csSup hbdd hy) (fun y hy => hL hy hc)
      rw [this]; exact hE _
    · have hLc : L = ⋃ n : ℕ, Iic (sSup L - 1 / ((n : ℝ) + 1)) := by
        ext y
        simp only [mem_iUnion, mem_Iic]
        constructor
        · intro hy
          have hlt : y < sSup L := lt_of_le_of_ne (le_csSup hbdd hy) fun h => hc (h ▸ hy)
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
          exact ⟨n, by linarith⟩
        · rintro ⟨n, hn⟩
          have := Nat.one_div_pos_of_nat (α := ℝ) (n := n)
          obtain ⟨z, hz, hyz⟩ := exists_lt_of_lt_csSup hne (show y < sSup L by linarith)
          exact hL hyz.le hz
      have hmono : Monotone fun n : ℕ => Iic (sSup L - 1 / ((n : ℝ) + 1)) := fun m n hmn =>
        Iic_subset_Iic.2 (sub_le_sub_left (one_div_le_one_div_of_le (by positivity)
          (by have : (m : ℝ) ≤ n := by exact_mod_cast hmn
              linarith)) _)
      rw [hLc]
      exact le_of_tendsto_of_tendsto' (tendsto_measure_iUnion_atTop hmono)
        (tendsto_measure_iUnion_atTop hmono) fun n => hE _
  · have : L = univ := eq_univ_of_forall fun y => by
      obtain ⟨z, hz, hyz⟩ := not_bddAbove_iff.1 hbdd y
      exact hL hyz.le hz
    rw [this, measure_univ, measure_univ]

/-- **Exercise 12.9b.** On `ℝ`, `F_μ ≤ F_λ` implies `μ ≥ λ`. -/
theorem slp_ex_12_9b (μ lam : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure lam]
    (h : ∀ x, μ.real (Iic x) ≤ lam.real (Iic x)) : Dominates μ lam := by
  intro f hf ⟨M, hM⟩ hmono
  set g := fun s => f s + M
  have hg0 : ∀ s, 0 ≤ g s := fun s => by
    have := hM s; rw [abs_le] at this; simp only [g]; linarith
  have hgM : ∀ s, |g s| ≤ 2 * M := fun s => by
    have := hM s; rw [abs_le] at this
    rw [abs_of_nonneg (hg0 s)]; simp only [g]; linarith
  have hgm : Measurable g := hf.add_const M
  have hshift : ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν], ∫ s, f s ∂ν = ∫ s, g s ∂ν - M :=
    fun ν _ => by
      simp only [g]
      rw [integral_add (gp_integrable_of_bounded hf hM) (integrable_const M), integral_const,
        probReal_univ, one_smul]
      ring
  have hlc : ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν],
      ∫ s, g s ∂ν = (∫⁻ t in Ioi 0, ν {s | t < g s}).toReal := fun ν _ => by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hg0) hgm.aestronglyMeasurable,
      lintegral_eq_lintegral_meas_lt ν (Eventually.of_forall hg0) hgm.aemeasurable]
  have hup : ∀ t, IsUpperSet {s | t < g s} := fun t s s' hss' (hs : t < g s) =>
    show t < g s' from lt_of_lt_of_le hs (add_le_add_left (hmono hss') M)
  have hle : ∀ t, lam {s | t < g s} ≤ μ {s | t < g s} := fun t => by
    have hmeas : MeasurableSet {s | t < g s} := measurableSet_lt measurable_const hgm
    have := gp_measure_lower_le h (hup t).compl
    have h1 := (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).2 this
    rw [← measureReal_def, ← measureReal_def, probReal_compl_eq_one_sub hmeas,
      probReal_compl_eq_one_sub hmeas] at h1
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).1 (by
      rw [← measureReal_def, ← measureReal_def]; linarith)
  have hfin : ∫⁻ t in Ioi 0, μ {s | t < g s} ≠ ⊤ := by
    rw [← lintegral_eq_lintegral_meas_lt μ (Eventually.of_forall hg0) hgm.aemeasurable]
    exact (gp_integrable_of_bounded hgm hgM (μ := μ)).lintegral_lt_top.ne
  rw [hshift lam, hshift μ, hlc lam, hlc μ]
  linarith [ENNReal.toReal_mono hfin (lintegral_mono hle)]

/-- The mass of a measurable set under `½(δ_p + δ_q)`. -/
theorem gp_real_half_dirac {α : Type*} [MeasurableSpace α] (p q : α) {A : Set α}
    (hA : MeasurableSet A) :
    ((2 : ℝ≥0∞)⁻¹ • (Measure.dirac p + Measure.dirac q)).real A =
      (A.indicator (1 : α → ℝ) p + A.indicator (1 : α → ℝ) q) / 2 := by
  rw [measureReal_def, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' p hA,
    Measure.dirac_apply' q hA, smul_eq_mul]
  by_cases hp : p ∈ A <;> by_cases hq : q ∈ A <;>
    simp [hp, hq, ENNReal.toReal_inv, ENNReal.toReal_add]
  all_goals norm_num

/-- **Exercise 12.9c.** On `ℝ²` the converse of Exercise 12.9a fails:
`μ = ½(δ_{(1,0)} + δ_{(0,1)})` and `λ = ½(δ_{(0,0)} + δ_{(1,1)})` have `F_μ ≤ F_λ`, but the
nondecreasing indicator of `{x ≥ (1, 1)}` integrates to `0` under `μ` and to `½` under `λ`. -/
theorem slp_ex_12_9c :
    let μ := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (![1, 0] : Fin 2 → ℝ) + Measure.dirac ![0, 1])
    let lam := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (![0, 0] : Fin 2 → ℝ) + Measure.dirac ![1, 1])
    (∀ x, gp_distFun μ x ≤ gp_distFun lam x) ∧ ¬ Dominates μ lam := by
  intro μ lam
  have hle : ∀ (a b : ℝ) (x : Fin 2 → ℝ), (![a, b] : Fin 2 → ℝ) ≤ x ↔ a ≤ x 0 ∧ b ≤ x 1 :=
    fun a b x => by simp [Pi.le_def, Fin.forall_fin_two]
  have hle2 : ∀ a b c d : ℝ, (![a, b] : Fin 2 → ℝ) ≤ ![c, d] ↔ a ≤ c ∧ b ≤ d :=
    fun a b c d => by simp [Pi.le_def, Fin.forall_fin_two]
  refine ⟨fun x => ?_, fun h => ?_⟩
  · have i1 : ∀ p : Fin 2 → ℝ, 0 ≤ (Iic x).indicator (1 : (Fin 2 → ℝ) → ℝ) p := fun p =>
      indicator_nonneg (fun _ _ => zero_le_one) p
    have hA : (![1, 0] : Fin 2 → ℝ) ∈ Iic x → (![0, 0] : Fin 2 → ℝ) ∈ Iic x := fun h => by
      rw [mem_Iic, hle] at h ⊢; exact ⟨by linarith [h.1], h.2⟩
    have hB : (![0, 1] : Fin 2 → ℝ) ∈ Iic x → (![0, 0] : Fin 2 → ℝ) ∈ Iic x := fun h => by
      rw [mem_Iic, hle] at h ⊢; exact ⟨h.1, by linarith [h.2]⟩
    have hC : (![1, 0] : Fin 2 → ℝ) ∈ Iic x → (![0, 1] : Fin 2 → ℝ) ∈ Iic x →
        (![1, 1] : Fin 2 → ℝ) ∈ Iic x := fun h h' => by
      rw [mem_Iic, hle] at h h' ⊢; exact ⟨h.1, h'.2⟩
    simp only [gp_distFun, μ, lam, gp_real_half_dirac _ _ measurableSet_Iic]
    by_cases h1 : (![1, 0] : Fin 2 → ℝ) ∈ Iic x <;> by_cases h2 : (![0, 1] : Fin 2 → ℝ) ∈ Iic x
    · simp only [indicator_of_mem h1, indicator_of_mem h2, indicator_of_mem (hA h1),
        indicator_of_mem (hC h1 h2), Pi.one_apply, le_refl]
    · simp only [indicator_of_mem h1, indicator_of_notMem h2, indicator_of_mem (hA h1),
        Pi.one_apply]
      linarith [i1 ![1, 1]]
    · simp only [indicator_of_notMem h1, indicator_of_mem h2, indicator_of_mem (hB h2),
        Pi.one_apply]
      linarith [i1 ![1, 1]]
    · simp only [indicator_of_notMem h1, indicator_of_notMem h2]
      linarith [i1 ![0, 0], i1 ![1, 1]]
  · have hU : MeasurableSet (Ici (![1, 1] : Fin 2 → ℝ)) := measurableSet_Ici
    have := h.real_le hU (isUpperSet_Ici _)
    have n00 : (![0, 0] : Fin 2 → ℝ) ∉ Ici ![1, 1] := fun h => by
      rw [mem_Ici, hle2] at h; linarith [h.1]
    have n10 : (![1, 0] : Fin 2 → ℝ) ∉ Ici ![1, 1] := fun h => by
      rw [mem_Ici, hle2] at h; linarith [h.2]
    have n01 : (![0, 1] : Fin 2 → ℝ) ∉ Ici ![1, 1] := fun h => by
      rw [mem_Ici, hle2] at h; linarith [h.1]
    have m11 : (![1, 1] : Fin 2 → ℝ) ∈ Ici ![1, 1] := mem_Ici.2 le_rfl
    simp only [μ, lam, gp_real_half_dirac _ _ hU, indicator_of_notMem n00, indicator_of_notMem n10,
      indicator_of_notMem n01, indicator_of_mem m11, Pi.one_apply] at this
    linarith

/-! ### Exercise 12.10 -/

theorem gp_distFun_map_val {S : Set (Fin l → ℝ)} (ν : Measure S) (x : Fin l → ℝ) :
    gp_distFun (ν.map Subtype.val) x = ν.real (Subtype.val ⁻¹' Iic x) := by
  rw [gp_distFun, measureReal_def, Measure.map_apply measurable_subtype_coe measurableSet_Iic]; rfl

/-- **Exercise 12.10.** If `μ₁ₙ ≤ λₙ ≤ μ₂ₙ` and `μ₁ₙ ⇒ μ`, `μ₂ₙ ⇒ μ`, then `λₙ ⇒ μ`. (The book
states it for `S = [a, b]`; the argument through Exercise 12.4 and Theorem 12.8 works for any
`S ⊆ ℝˡ`.) -/
theorem slp_ex_12_10 {S : Set (Fin l → ℝ)} (μ₁ μ₂ ls : ℕ → Measure S) (μ : Measure S)
    [∀ n, IsProbabilityMeasure (μ₁ n)] [∀ n, IsProbabilityMeasure (μ₂ n)]
    [∀ n, IsProbabilityMeasure (ls n)] [IsProbabilityMeasure μ]
    (h₁ : ∀ n, Dominates (ls n) (μ₁ n)) (h₂ : ∀ n, Dominates (μ₂ n) (ls n))
    (hc₁ : ConvWeak μ₁ μ) (hc₂ : ConvWeak μ₂ μ) : ConvWeak ls μ := by
  rw [slp_ex_12_4, slp_theorem_12_8] at hc₁ hc₂ ⊢
  intro x hx
  have e1 := hc₁ x hx
  have e2 := hc₂ x hx
  simp only [gp_distFun_map_val] at e1 e2 ⊢
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le e2 e1
    (fun n => slp_ex_12_9a_subtype (h₂ n) x) (fun n => slp_ex_12_9a_subtype (h₁ n) x)

/-! ### Exercise 12.11 and iterates -/

variable (κ : Kernel S S) [IsMarkovKernel κ]

/-- **Exercise 12.11.** The following are equivalent: (a) `P` is monotone; (b) `μ ≥ λ` implies
`T*μ ≥ T*λ`; (c) `s ≥ s′` implies `P(s, ·) ≥ P(s′, ·)`. -/
theorem slp_ex_12_11 :
    (IsMonotoneTF κ ↔ ∀ (μ lam : Measure S), IsProbabilityMeasure μ → IsProbabilityMeasure lam →
      Dominates μ lam → Dominates (adjointOp κ μ) (adjointOp κ lam)) ∧
    (IsMonotoneTF κ ↔ ∀ s s' : S, s' ≤ s → Dominates (κ s) (κ s')) := by
  have hab : IsMonotoneTF κ → ∀ (μ lam : Measure S), IsProbabilityMeasure μ →
      IsProbabilityMeasure lam → Dominates μ lam →
        Dominates (adjointOp κ μ) (adjointOp κ lam) := fun hM μ lam _ _ h f hf hb hm => by
    obtain ⟨M, hMb⟩ := hb
    rw [← slp_theorem_8_3_cor κ lam hf hMb, ← slp_theorem_8_3_cor κ μ hf hMb]
    have := slp_theorem_8_1_cor κ hf hMb
    exact h _ this.1 ⟨M, this.2⟩ (hM f hf ⟨M, hMb⟩ hm)
  have hbc : (∀ (μ lam : Measure S), IsProbabilityMeasure μ → IsProbabilityMeasure lam →
      Dominates μ lam → Dominates (adjointOp κ μ) (adjointOp κ lam)) →
        ∀ s s' : S, s' ≤ s → Dominates (κ s) (κ s') := fun h s s' hss' => by
    have := h (Measure.dirac s) (Measure.dirac s') inferInstance inferInstance
      (fun f hf _ hm => by
        rw [integral_dirac' f s' hf.stronglyMeasurable, integral_dirac' f s hf.stronglyMeasurable]
        exact hm hss')
    rwa [gp_adjointOp_dirac, gp_adjointOp_dirac] at this
  have hca : (∀ s s' : S, s' ≤ s → Dominates (κ s) (κ s')) → IsMonotoneTF κ :=
    fun h f hf hb hm s' s hss' => h s s' hss' f hf hb hm
  exact ⟨⟨hab, fun h => hca (hbc h)⟩, ⟨fun h => hbc (hab h), hca⟩⟩

omit [Preorder S] [IsMarkovKernel κ] in
theorem gp_markovOpR_kpow_zero {f : S → ℝ} (hf : Measurable f) : markovOpR (kpow κ 0) f = f := by
  funext s
  simp only [markovOpR, kpow, Kernel.id_apply]
  exact integral_dirac' f s hf.stronglyMeasurable

omit [Preorder S] in
/-- `T⁽ⁿ⁺ᵐ⁾f = Tⁿ(Tᵐf)` for bounded measurable `f`. -/
theorem gp_markovOpR_kpow_add (n m : ℕ) {f : S → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ s, |f s| ≤ M) :
    markovOpR (kpow κ (n + m)) f = markovOpR (kpow κ n) (markovOpR (kpow κ m) f) := by
  have := slp_ex_8_4a κ m
  have := slp_ex_8_4a κ n
  funext s
  rw [gp_kpow_add]
  exact Kernel.integral_comp (gp_integrable_of_bounded hf hM)

/-- The iterates of a monotone transition function are monotone. -/
theorem gp_isMonotoneTF_kpow {κ : Kernel S S} [IsMarkovKernel κ] (hM : IsMonotoneTF κ) (n : ℕ) :
    IsMonotoneTF (kpow κ n) := by
  induction n with
  | zero => intro f hf _ hm; rw [gp_markovOpR_kpow_zero κ hf]; exact hm
  | succ n ih =>
    intro f hf ⟨M, hb⟩ hm
    have := slp_ex_8_4a κ n
    rw [add_comm, gp_markovOpR_kpow_add κ 1 n hf hb, gp_kpow_one]
    have := slp_theorem_8_1_cor (kpow κ n) hf hb
    exact hM _ this.1 ⟨M, this.2⟩ (ih f hf ⟨M, hb⟩ hm)

omit [Preorder S] [IsMarkovKernel κ] in
theorem gp_iterate_dirac (n : ℕ) (s : S) :
    (adjointOp κ)^[n] (Measure.dirac s) = kpow κ n s := by
  rw [gp_adjointOp_iterate, gp_adjointOp_dirac]

/-- `T*ⁿ` preserves dominance for monotone `P`. -/
theorem gp_dominates_iterate {κ : Kernel S S} [IsMarkovKernel κ] (hM : IsMonotoneTF κ)
    {μ lam : Measure S} [IsProbabilityMeasure μ] [IsProbabilityMeasure lam]
    (h : Dominates μ lam) (n : ℕ) :
    Dominates ((adjointOp κ)^[n] μ) ((adjointOp κ)^[n] lam) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact (slp_ex_12_11 κ).1.1 hM _ _ (gp_isProbabilityMeasure_iterate μ n)
      (gp_isProbabilityMeasure_iterate lam n) ih

/-! ### Monotone processes on `[a, b]` -/

variable {a b : Fin l → ℝ}

/-- The bottom `a` of `[a, b]`. -/
def gp_IccBot (hab : a ≤ b) : Icc a b := ⟨a, left_mem_Icc.2 hab⟩

/-- The top `b` of `[a, b]`. -/
def gp_IccTop (hab : a ≤ b) : Icc a b := ⟨b, right_mem_Icc.2 hab⟩

theorem gp_IccBot_le (hab : a ≤ b) (s : Icc a b) : gp_IccBot hab ≤ s := s.2.1

theorem gp_le_IccTop (hab : a ≤ b) (s : Icc a b) : s ≤ gp_IccTop hab := s.2.2

/-- Every probability measure dominates `δ_a` and is dominated by `δ_b`. -/
theorem gp_dominates_dirac_bot_top (hab : a ≤ b) (ν : Measure (Icc a b)) [IsProbabilityMeasure ν] :
    Dominates ν (Measure.dirac (gp_IccBot hab)) ∧ Dominates (Measure.dirac (gp_IccTop hab)) ν := by
  refine ⟨fun f hf ⟨M, hM⟩ hm => ?_, fun f hf ⟨M, hM⟩ hm => ?_⟩
  · rw [integral_dirac]
    have := integral_mono (integrable_const (f (gp_IccBot hab))) (gp_integrable_of_bounded hf hM (μ
        := ν))
      fun s => hm (gp_IccBot_le hab s)
    rwa [integral_const, probReal_univ, one_smul] at this
  · rw [integral_dirac]
    have := integral_mono (gp_integrable_of_bounded hf hM (μ := ν))
      (integrable_const (f (gp_IccTop hab))) fun s => hm (gp_le_IccTop hab s)
    rwa [integral_const, probReal_univ, one_smul] at this

/-- A probability measure on `ℝˡ` concentrated on `[a, b]` is the extension of a probability
measure on `[a, b]`. -/
theorem gp_exists_subtype_measure (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ]
    (h : μ (Icc a b) = 1) :
    ∃ ν : Measure (Icc a b), IsProbabilityMeasure ν ∧ ν.map Subtype.val = μ := by
  have hmap : (μ.comap Subtype.val).map (Subtype.val : Icc a b → Fin l → ℝ) = μ := by
    rw [map_comap_subtype_coe measurableSet_Icc]
    exact Measure.restrict_eq_self_of_ae_mem
      (mem_ae_iff.2 ((prob_compl_eq_zero_iff measurableSet_Icc).2 h))
  refine ⟨μ.comap Subtype.val, ?_, hmap⟩
  have : IsProbabilityMeasure ((μ.comap Subtype.val).map (Subtype.val : Icc a b → Fin l → ℝ)) := by
    rw [hmap]; infer_instance
  exact (Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.aemeasurable).1 this

theorem gp_map_val_Icc (ν : Measure (Icc a b)) [IsProbabilityMeasure ν] :
    ν.map Subtype.val (Icc a b) = 1 := by
  rw [Measure.map_apply measurable_subtype_coe measurableSet_Icc]
  have : (Subtype.val ⁻¹' Icc a b : Set (Icc a b)) = univ := eq_univ_of_forall fun s => s.2
  rw [this, measure_univ]

/-- A **monotone sequence of measures** on `[a, b]` (SLP p. 379) converges weakly (Corollary 2 to
Helly, through Exercise 12.9a and Exercise 12.4). -/
theorem gp_convWeak_of_dominance_mono (ν : ℕ → Measure (Icc a b)) [∀ n, IsProbabilityMeasure (ν n)]
    (hmono : (∀ n, Dominates (ν (n + 1)) (ν n)) ∨ (∀ n, Dominates (ν n) (ν (n + 1)))) :
    ∃ μ : Measure (Icc a b), IsProbabilityMeasure μ ∧ ConvWeak ν μ := by
  obtain ⟨μ', hμ', hab', hconv⟩ := slp_theorem_12_9_cor2 (a := a) (b := b)
    (fun n => (ν n).map Subtype.val) (fun n => gp_map_val_Icc (ν n)) (by
      rcases hmono with h | h
      · exact Or.inl fun n => Pi.le_def.2 fun x => by
          rw [gp_distFun_map_val, gp_distFun_map_val]; exact slp_ex_12_9a_subtype (h n) x
      · exact Or.inr fun n => Pi.le_def.2 fun x => by
          rw [gp_distFun_map_val, gp_distFun_map_val]; exact slp_ex_12_9a_subtype (h n) x)
  obtain ⟨μ, hμ, hmap⟩ := gp_exists_subtype_measure μ' hab'
  refine ⟨μ, hμ, (slp_ex_12_4 ν μ).2 ?_⟩
  rw [hmap]; exact hconv

/-- **Exercise 12.12.** For monotone Feller `P` on `[a, b]`, `T*ⁿδ_a` is increasing and `T*ⁿδ_b`
decreasing, and each converges weakly to an invariant measure. -/
theorem slp_ex_12_12 (hab : a ≤ b) (κ : Kernel (Icc a b) (Icc a b)) [IsMarkovKernel κ]
    (hM : IsMonotoneTF κ) (hF : IsFeller κ) :
    (∀ n, Dominates ((adjointOp κ)^[n + 1] (Measure.dirac (gp_IccBot hab)))
      ((adjointOp κ)^[n] (Measure.dirac (gp_IccBot hab)))) ∧
    (∀ n, Dominates ((adjointOp κ)^[n] (Measure.dirac (gp_IccTop hab)))
      ((adjointOp κ)^[n + 1] (Measure.dirac (gp_IccTop hab)))) ∧
    (∃ μ, IsProbabilityMeasure μ ∧
      ConvWeak (fun n => (adjointOp κ)^[n] (Measure.dirac (gp_IccBot hab))) μ ∧
      adjointOp κ μ = μ) ∧
    (∃ μ, IsProbabilityMeasure μ ∧
      ConvWeak (fun n => (adjointOp κ)^[n] (Measure.dirac (gp_IccTop hab))) μ ∧
      adjointOp κ μ = μ) := by
  have hP : ∀ (lam : Measure (Icc a b)) [IsProbabilityMeasure lam],
      IsProbabilityMeasure (adjointOp κ lam) := fun lam _ => (slp_theorem_8_2 κ lam).1
  have hbot : ∀ n, Dominates ((adjointOp κ)^[n + 1] (Measure.dirac (gp_IccBot hab)))
      ((adjointOp κ)^[n] (Measure.dirac (gp_IccBot hab))) := fun n => by
    rw [Function.iterate_succ_apply]
    exact gp_dominates_iterate hM (gp_dominates_dirac_bot_top hab _).1 n
  have htop : ∀ n, Dominates ((adjointOp κ)^[n] (Measure.dirac (gp_IccTop hab)))
      ((adjointOp κ)^[n + 1] (Measure.dirac (gp_IccTop hab))) := fun n => by
    rw [Function.iterate_succ_apply]
    exact gp_dominates_iterate hM (gp_dominates_dirac_bot_top hab _).2 n
  have hlim : ∀ s : Icc a b, ((∀ n, Dominates ((adjointOp κ)^[n + 1] (Measure.dirac s))
      ((adjointOp κ)^[n] (Measure.dirac s))) ∨ (∀ n, Dominates ((adjointOp κ)^[n]
        (Measure.dirac s)) ((adjointOp κ)^[n + 1] (Measure.dirac s)))) →
      ∃ μ, IsProbabilityMeasure μ ∧
        ConvWeak (fun n => (adjointOp κ)^[n] (Measure.dirac s)) μ ∧ adjointOp κ μ = μ :=
    fun s hs => by
      have : ∀ n, IsProbabilityMeasure ((adjointOp κ)^[n] (Measure.dirac s)) := fun n =>
        gp_isProbabilityMeasure_iterate _ n
      obtain ⟨μ, hμ, hconv⟩ := gp_convWeak_of_dominance_mono _ hs
      refine ⟨μ, hμ, hconv, gp_invariant_of_convWeak hF hconv fun f => ?_⟩
      have := (hconv f).sub ((hconv f).comp (tendsto_add_atTop_nat 1))
      rw [sub_self] at this
      refine this.congr fun n => ?_
      simp only [Function.comp_apply, Function.iterate_succ_apply']
  exact ⟨hbot, htop, hlim _ (Or.inl hbot), hlim _ (Or.inr htop)⟩

/-! ### Assumption 12.1, Exercise 12.14, Lemma 12.11 and Theorem 12.12 -/

/-- **Assumption 12.1.** There are `c ∈ [a, b]`, `ε > 0` and `N ≥ 1` with `Pᴺ(a, [c, b]) ≥ ε`
and `Pᴺ(b, [a, c]) ≥ ε`. -/
def gp_Assumption12_1 (hab : a ≤ b) (κ : Kernel (Icc a b) (Icc a b)) (c : Icc a b) (ε : ℝ)
    (N : ℕ) : Prop :=
  0 < ε ∧ 1 ≤ N ∧ ε ≤ (kpow κ N (gp_IccBot hab)).real (Ici c) ∧
    ε ≤ (kpow κ N (gp_IccTop hab)).real (Iic c)

/-- **Exercise 12.14.** Under monotonicity, Assumption 12.1 holds from every starting point:
`Pᴺ(s, [a, c]) ≥ ε` and `Pᴺ(s, [c, b]) ≥ ε`. -/
theorem slp_ex_12_14 {hab : a ≤ b} {κ : Kernel (Icc a b) (Icc a b)} [IsMarkovKernel κ]
    (hM : IsMonotoneTF κ) {c : Icc a b} {ε : ℝ} {N : ℕ} (hA : gp_Assumption12_1 hab κ c ε N)
    (s : Icc a b) : ε ≤ (kpow κ N s).real (Iic c) ∧ ε ≤ (kpow κ N s).real (Ici c) := by
  have := slp_ex_8_4a κ N
  have hdom := (slp_ex_12_11 (kpow κ N)).2.1 (gp_isMonotoneTF_kpow hM N)
  refine ⟨?_, hA.2.2.1.trans ((hdom s _ (gp_IccBot_le hab s)).real_le measurableSet_Ici
    (isUpperSet_Ici c))⟩
  have := (hdom _ s (gp_le_IccTop hab s)).real_le measurableSet_Iic.compl (isLowerSet_Iic c).compl
  rw [probReal_compl_eq_one_sub measurableSet_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
    at this
  linarith [hA.2.2.2]

/-- **Lemma 12.11.** Under monotonicity and Assumption 12.1, for bounded measurable
nondecreasing `f`: `εf(c) + (1 - ε)f(a) ≤ (Tᴺf)(s) ≤ εf(c) + (1 - ε)f(b)`. -/
theorem slp_lemma_12_11 {hab : a ≤ b} {κ : Kernel (Icc a b) (Icc a b)} [IsMarkovKernel κ]
    (hM : IsMonotoneTF κ) {c : Icc a b} {ε : ℝ} {N : ℕ} (hA : gp_Assumption12_1 hab κ c ε N)
    {f : Icc a b → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ s, |f s| ≤ M) (hm : Monotone f)
    (s : Icc a b) :
    ε * f c + (1 - ε) * f (gp_IccBot hab) ≤ markovOpR (kpow κ N) f s ∧
      markovOpR (kpow κ N) f s ≤ ε * f c + (1 - ε) * f (gp_IccTop hab) := by
  have := slp_ex_8_4a κ N
  obtain ⟨hp, hq⟩ := slp_ex_12_14 hM hA s
  set ν := kpow κ N s
  have hfi : Integrable f ν := gp_integrable_of_bounded hf hb
  have hI : ∀ (A : Set (Icc a b)), MeasurableSet A → Integrable (A.indicator (1 : Icc a b → ℝ)) ν :=
    fun A hA => by exact (integrable_const (1 : ℝ)).indicator hA
  constructor
  · have hle : ∀ t, f (gp_IccBot hab) + (f c - f (gp_IccBot hab)) * (Ici c).indicator 1 t ≤ f t :=
      fun t => by
        by_cases ht : t ∈ Ici c
        · simp only [indicator_of_mem ht, Pi.one_apply, mul_one]; linarith [hm ht]
        · simp only [indicator_of_notMem ht, mul_zero, add_zero]; exact hm (gp_IccBot_le hab t)
    have := integral_mono ((integrable_const _).add ((hI _ measurableSet_Ici).const_mul _)) hfi hle
    simp only [Pi.add_apply] at this
    rw [integral_add (integrable_const _) ((hI _ measurableSet_Ici).const_mul _),
      integral_const, probReal_univ, one_smul, integral_const_mul,
      integral_indicator_one measurableSet_Ici] at this
    have hca : f (gp_IccBot hab) ≤ f c := hm (gp_IccBot_le hab c)
    change _ ≤ ∫ t, f t ∂ν
    nlinarith
  · have hle : ∀ t, f t ≤ f (gp_IccTop hab) - (f (gp_IccTop hab) - f c) * (Iic c).indicator 1 t :=
      fun t => by
        by_cases ht : t ∈ Iic c
        · simp only [indicator_of_mem ht, Pi.one_apply, mul_one]; linarith [hm ht]
        · simp only [indicator_of_notMem ht, mul_zero, sub_zero]; exact hm (gp_le_IccTop hab t)
    have := integral_mono hfi ((integrable_const _).sub ((hI _ measurableSet_Iic).const_mul _)) hle
    simp only [Pi.sub_apply] at this
    rw [integral_sub (integrable_const _) ((hI _ measurableSet_Iic).const_mul _),
      integral_const, probReal_univ, one_smul, integral_const_mul,
      integral_indicator_one measurableSet_Iic] at this
    have hcb : f c ≤ f (gp_IccTop hab) := hm (gp_le_IccTop hab c)
    change ∫ t, f t ∂ν ≤ _
    nlinarith

/-- **Theorem 12.12.** On `[a, b]`, a monotone Feller transition function satisfying Assumption
12.1 has a unique invariant probability measure `λ*`, and `T*ⁿλ₀ ⇒ λ*` for every `λ₀`. -/
theorem slp_theorem_12_12 (hab : a ≤ b) (κ : Kernel (Icc a b) (Icc a b)) [IsMarkovKernel κ]
    (hM : IsMonotoneTF κ) (hF : IsFeller κ) {c : Icc a b} {ε : ℝ} {N : ℕ}
    (hA : gp_Assumption12_1 hab κ c ε N) :
    ∃ μ : Measure (Icc a b), IsProbabilityMeasure μ ∧ adjointOp κ μ = μ ∧
      (∀ ν : Measure (Icc a b), IsProbabilityMeasure ν → adjointOp κ ν = ν → ν = μ) ∧
      ∀ lam₀ : Measure (Icc a b), IsProbabilityMeasure lam₀ →
        ConvWeak (fun n => (adjointOp κ)^[n] lam₀) μ := by
  obtain ⟨-, -, ⟨μa, hμa, hca, hia⟩, ⟨μb, hμb, hcb, hib⟩⟩ := slp_ex_12_12 hab κ hM hF
  set lo := gp_IccBot hab
  set hi := gp_IccTop hab
  have hε1 : ε ≤ 1 := by
    have := slp_ex_8_4a κ N
    exact hA.2.2.1.trans measureReal_le_one
  -- the limits along `Tⁿf` at the two ends
  have hT : ∀ (s : Icc a b) (f : Icc a b →ᵇ ℝ) (n : ℕ),
      ∫ t, f t ∂(adjointOp κ)^[n] (Measure.dirac s) = markovOpR (kpow κ n) f s :=
    fun s f n => by rw [gp_iterate_dirac]; rfl
  have heq : μa = μb := by
    refine slp_ex_12_5b μa μb fun f hfm => ?_
    have hfb := gp_bcf_abs_le_norm f
    have hfmeas := f.continuous.measurable
    set d : ℕ → ℝ := fun n => markovOpR (kpow κ n) f hi - markovOpR (kpow κ n) f lo
    have hdlim : Tendsto d atTop (𝓝 (∫ t, f t ∂μb - ∫ t, f t ∂μa)) := by
      have h1 := hcb f; have h2 := hca f
      simp only [hT] at h1 h2
      exact h1.sub h2
    have hd0 : ∀ n, 0 ≤ d n := fun n => sub_nonneg.2
      (gp_isMonotoneTF_kpow hM n f hfmeas ⟨_, hfb⟩ hfm (gp_IccBot_le hab hi))
    have hdN : ∀ m, d (N * m) ≤ (1 - ε) ^ m * (f hi - f lo) := fun m => by
      induction m with
      | zero =>
        simp only [d, mul_zero, pow_zero, one_mul, gp_markovOpR_kpow_zero κ hfmeas]; rfl
      | succ m ih =>
        have := slp_ex_8_4a κ (N * m)
        have hg := slp_theorem_8_1_cor (kpow κ (N * m)) hfmeas hfb
        have hgm := gp_isMonotoneTF_kpow hM (N * m) f hfmeas ⟨_, hfb⟩ hfm
        have hsplit : markovOpR (kpow κ (N * (m + 1))) f =
            markovOpR (kpow κ N) (markovOpR (kpow κ (N * m)) f) := by
          rw [show N * (m + 1) = N + N * m by ring, gp_markovOpR_kpow_add κ N (N * m) hfmeas hfb]
        have hup := (slp_lemma_12_11 hM hA hg.1 hg.2 hgm hi).2
        have hlo := (slp_lemma_12_11 hM hA hg.1 hg.2 hgm lo).1
        simp only [d, hsplit]
        have h1ε : 0 ≤ 1 - ε := by linarith
        calc _ ≤ (1 - ε) * d (N * m) := by simp only [d]; linarith
          _ ≤ (1 - ε) * ((1 - ε) ^ m * (f hi - f lo)) := mul_le_mul_of_nonneg_left ih h1ε
          _ = _ := by ring
    have hNm : Tendsto (fun m => N * m) atTop atTop :=
      tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m hA.2.1) tendsto_id
    have hup : ∫ t, f t ∂μb - ∫ t, f t ∂μa ≤ 0 := by
      have hbound : Tendsto (fun m : ℕ => (1 - ε) ^ m * (f hi - f lo)) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith [hA.1])
          ).mul_const (f hi - f lo)
      exact le_of_tendsto_of_tendsto' (hdlim.comp hNm) hbound hdN
    have hlow : 0 ≤ ∫ t, f t ∂μb - ∫ t, f t ∂μa := ge_of_tendsto' hdlim hd0
    linarith
  subst heq
  have hglob : ∀ lam₀ : Measure (Icc a b), IsProbabilityMeasure lam₀ →
      ConvWeak (fun n => (adjointOp κ)^[n] lam₀) μa := fun lam₀ _ => by
    have : ∀ (ν : Measure (Icc a b)) [IsProbabilityMeasure ν] n,
        IsProbabilityMeasure ((adjointOp κ)^[n] ν) := fun ν _ n => gp_isProbabilityMeasure_iterate
            ν n
    exact slp_ex_12_10 (fun n => (adjointOp κ)^[n] (Measure.dirac lo))
      (fun n => (adjointOp κ)^[n] (Measure.dirac hi)) (fun n => (adjointOp κ)^[n] lam₀) μa
      (fun n => gp_dominates_iterate hM (gp_dominates_dirac_bot_top hab lam₀).1 n)
      (fun n => gp_dominates_iterate hM (gp_dominates_dirac_bot_top hab lam₀).2 n) hca hcb
  refine ⟨μa, hμa, hia, fun ν _ hν => ?_, hglob⟩
  have hconst : ConvWeak (fun n => (adjointOp κ)^[n] ν) ν := fun f => by
    simp only [Function.iterate_fixed hν]; exact tendsto_const_nhds
  have : ∀ n, IsProbabilityMeasure ((adjointOp κ)^[n] ν) := fun n =>
    gp_isProbabilityMeasure_iterate ν n
  exact gp_convWeak_unique hconst (hglob ν inferInstance)

end Miao.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Dependence on a parameter, and a loose end (SLP §§12.5–12.6, pp. 383–388)

Copied from `RecursiveMethods/WeakConvergence` (SLP Chapter 12, module `Parameters.lean`), with the
namespace renamed to `Miao.MarkovProcesses`, the results numbered in SLP prefixed
`slp_` and the helper lemmas and definitions prefixed `gp_`.

* **Theorem 12.13**: on a compact metric state space, if `(s, θ) ↦ P_θ(s, ·)` is weakly continuous
  and each `T_θ*` has a unique fixed point `μ_θ`, then `θ ↦ μ_θ` is weakly continuous. The book's
  "uniformly continuous on `S × Θ̂`" step becomes the sequential lemma `gp_tendsto_uniform_markovOp`
  (`T_{θₙ}f → T_{θ₀}f` uniformly), proved by compactness of `S`; `Θ` may be any metric space;
* **Lemma 12.14**: for Feller `Q` and bounded continuous `f` on `X × Z`,
  `(Tf)(y, z) = ∫ f(y, z′) Q(z, dz′)` is bounded and continuous (`slp_lemma_12_14_cont`), for any
  metric spaces `X`, `Z`; and `T` preserves monotonicity, strict monotonicity, concavity and strict
  concavity in `y` (`slp_lemma_12_14_mono`, `_strictMono`, `_concave`, `_strictConcave`). The key
  limit
  (1) is proved with the continuous majorants `gₖ(z′) = sup_{n ≥ k} |f(yₙ, z′) - f(y, z′)|`
  (maxima of a jointly continuous function over the compact sets `{y} ∪ {yₙ : n ≥ k}`) in place of
  the book's boundary-counting argument; this avoids the book's inexact description of
  `∂E_k(ε)`.
-/

namespace Miao.MarkovProcesses

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction

/-! ### Theorem 12.13 -/

variable {S Θ : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S] [MetricSpace Θ]

omit [BorelSpace S] in
/-- Under the joint weak continuity of Theorem 12.13(b) on compact `S`, `T_{θₙ}f → T_{θ₀}f`
uniformly whenever `θₙ → θ₀`. -/
theorem gp_tendsto_uniform_markovOp [CompactSpace S] (P : Θ → Kernel S S)
    (hcont : ∀ (s : ℕ → S) (θ : ℕ → Θ) (s₀ : S) (θ₀ : Θ), Tendsto s atTop (𝓝 s₀) →
      Tendsto θ atTop (𝓝 θ₀) → ConvWeak (fun n => P (θ n) (s n)) (P θ₀ s₀))
    {θ : ℕ → Θ} {θ₀ : Θ} (hθ : Tendsto θ atTop (𝓝 θ₀)) (f : S →ᵇ ℝ) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ s, |markovOpR (P (θ n)) f s - markovOpR (P θ₀) f s| < ε := by
  intro ε hε
  by_contra hne
  rw [not_eventually, frequently_atTop] at hne
  choose nk hnk hbad using hne
  have hbad' : ∀ k, ∃ s, ε ≤ |markovOpR (P (θ (nk k))) f s - markovOpR (P θ₀) f s| := fun k => by
    have := hbad k; push Not at this; exact this
  choose sk hsk using hbad'
  obtain ⟨s₀, -, ψ, hψ, hsψ⟩ := isCompact_univ.tendsto_subseq (fun k => mem_univ (sk k))
  have hn : Tendsto (fun j => nk (ψ j)) atTop atTop :=
    tendsto_atTop_mono (fun j => (hψ.id_le j).trans (hnk (ψ j))) tendsto_id
  have hA := hcont (sk ∘ ψ) (fun j => θ (nk (ψ j))) s₀ θ₀ hsψ (hθ.comp hn) f
  have hB := hcont (sk ∘ ψ) (fun _ => θ₀) s₀ θ₀ hsψ tendsto_const_nhds f
  have hdiff := (hA.sub hB).abs
  rw [sub_self, abs_zero] at hdiff
  obtain ⟨j, hj⟩ := (hdiff.eventually (gt_mem_nhds hε)).exists
  exact absurd (hsk (ψ j)) (not_le.2 hj)

/-- **Theorem 12.13.** Let `S` be a compact metric space and `Θ` a metric space. If
(b) `(sₙ, θₙ) → (s₀, θ₀)` implies `P_{θₙ}(sₙ, ·) ⇒ P_{θ₀}(s₀, ·)`, and (c) each `T_θ*` has a
unique fixed point `μ_θ`, then `θₙ → θ₀` implies `μ_{θₙ} ⇒ μ_{θ₀}`. -/
theorem slp_theorem_12_13 [CompactSpace S] (P : Θ → Kernel S S) [∀ θ, IsMarkovKernel (P θ)]
    (hcont : ∀ (s : ℕ → S) (θ : ℕ → Θ) (s₀ : S) (θ₀ : Θ), Tendsto s atTop (𝓝 s₀) →
      Tendsto θ atTop (𝓝 θ₀) → ConvWeak (fun n => P (θ n) (s n)) (P θ₀ s₀))
    (μ : Θ → Measure S) [∀ θ, IsProbabilityMeasure (μ θ)]
    (hfix : ∀ θ, adjointOp (P θ) (μ θ) = μ θ)
    (huniq : ∀ θ (ν : Measure S), IsProbabilityMeasure ν → adjointOp (P θ) ν = ν → ν = μ θ)
    {θ : ℕ → Θ} {θ₀ : Θ} (hθ : Tendsto θ atTop (𝓝 θ₀)) :
    ConvWeak (fun n => μ (θ n)) (μ θ₀) := by
  have hF0 : IsFeller (P θ₀) :=
    (slp_ex_12_7 (P θ₀)).1.2 fun s s₀ hs => hcont s (fun _ => θ₀) s₀ θ₀ hs tendsto_const_nhds
  have hT : ∀ (κ : Kernel S S) [IsMarkovKernel κ] (g : S →ᵇ ℝ),
      Measurable (markovOpR κ g) ∧ ∀ s, |markovOpR κ g s| ≤ ‖g‖ := fun κ _ g =>
    slp_theorem_8_1_cor κ g.continuous.measurable (gp_bcf_abs_le_norm g)
  intro f
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨μh, hμh, φ, hφ, hconv⟩ := gp_exists_convWeak_subseq_of_tight (fun k => μ (θ (ns k)))
    fun ε hε => ⟨univ, isCompact_univ, fun n => by rw [probReal_univ]; linarith⟩
  set m : ℕ → ℕ := fun j => ns (φ j)
  have hm : Tendsto m atTop atTop := hns.comp hφ.tendsto_atTop
  have : ∀ j, IsProbabilityMeasure (((fun k => μ (θ (ns k))) ∘ φ) j) := fun j =>
    inferInstanceAs (IsProbabilityMeasure (μ (θ (ns (φ j)))))
  -- the subsequential limit is a fixed point of `T₀*`
  have hinv : adjointOp (P θ₀) μh = μh := by
    have : IsProbabilityMeasure (adjointOp (P θ₀) μh) := (slp_theorem_8_2 (P θ₀) μh).1
    refine slp_theorem_12_6_cor2 fun g => ?_
    rw [← gp_integral_markovOpR (P θ₀) μh g]
    have h1 : Tendsto (fun j => ∫ s, markovOpR (P θ₀) g s ∂μ (θ (m j))) atTop
        (𝓝 (∫ s, markovOpR (P θ₀) g s ∂μh)) := hconv (gp_fellerBCF hF0 g)
    have h2 : Tendsto (fun j => ∫ s, g s ∂μ (θ (m j))) atTop (𝓝 (∫ s, g s ∂μh)) := hconv g
    have h3 : Tendsto (fun j => ∫ s, markovOpR (P θ₀) g s ∂μ (θ (m j)) -
        ∫ s, g s ∂μ (θ (m j))) atTop (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      filter_upwards [hm.eventually (gp_tendsto_uniform_markovOp P hcont hθ g (ε / 2)
        (half_pos hε))] with j hj
      have hgj : ∫ s, g s ∂μ (θ (m j)) = ∫ s, markovOpR (P (θ (m j))) g s ∂μ (θ (m j)) := by
        rw [gp_integral_markovOpR, hfix]
      rw [hgj, Real.dist_eq, sub_zero, ← integral_sub
        (gp_integrable_of_bounded (hT _ g).1 (hT _ g).2)
        (gp_integrable_of_bounded (hT _ g).1 (hT _ g).2)]
      have := norm_integral_le_of_norm_le_const (μ := μ (θ (m j))) (C := ε / 2)
        (f := fun s => markovOpR (P θ₀) g s - markovOpR (P (θ (m j))) g s)
        (Eventually.of_forall fun s => by
          rw [Real.norm_eq_abs, abs_sub_comm]; exact (hj s).le)
      rw [probReal_univ, mul_one, Real.norm_eq_abs] at this
      linarith
    have h4 := h3.add h2
    simp only [sub_add_cancel, zero_add] at h4
    exact (tendsto_nhds_unique h4 h1).symm
  have := huniq θ₀ μh hμh hinv
  subst this
  exact ⟨φ, hconv f⟩

/-! ### Lemma 12.14 -/

variable {X Z : Type*} [MetricSpace X] [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]

/-- The key limit (1) in the proof of Lemma 12.14: if `yₙ → y` and `Q(zₙ, ·) ⇒ Q(z, ·)`, then
`∫ |f(yₙ, z′) - f(y, z′)| Q(zₙ, dz′) → 0`. -/
theorem gp_tendsto_integral_abs_sub (f : X × Z →ᵇ ℝ) {y : ℕ → X} {y₀ : X}
    (hy : Tendsto y atTop (𝓝 y₀)) {ν : ℕ → Measure Z} {ν₀ : Measure Z}
    [∀ n, IsProbabilityMeasure (ν n)] [IsProbabilityMeasure ν₀] (hν : ConvWeak ν ν₀) :
    Tendsto (fun n => ∫ z', |f (y n, z') - f (y₀, z')| ∂ν n) atTop (𝓝 0) := by
  set h : Z → X → ℝ := fun z' w => |f (w, z') - f (y₀, z')|
  have hh : Continuous (Function.uncurry h) := by
    have : Function.uncurry h = fun p : Z × X => |f (p.2, p.1) - f (y₀, p.1)| := rfl
    rw [this]
    exact ((f.continuous.comp (continuous_snd.prodMk continuous_fst)).sub
      (f.continuous.comp (continuous_const.prodMk continuous_fst))).abs
  have hbd : ∀ z' w, h z' w ≤ 2 * ‖f‖ := fun z' w => by
    have h1 := gp_bcf_abs_le_norm f (w, z'); have h2 := gp_bcf_abs_le_norm f (y₀, z')
    linarith [abs_sub (f (w, z')) (f (y₀, z'))]
  set W : ℕ → Set X := fun k => insert y₀ (range fun n => y (n + k))
  have hW : ∀ k, IsCompact (W k) := fun k =>
    (hy.comp (tendsto_add_atTop_nat k)).isCompact_insert_range
  set g : ℕ → Z → ℝ := fun k z' => sSup (h z' '' W k)
  have hne : ∀ k z', (h z' '' W k).Nonempty := fun k z' => (insert_nonempty _ _).image _
  have hbdd : ∀ k z', BddAbove (h z' '' W k) := fun k z' =>
    ⟨2 * ‖f‖, by rintro _ ⟨w, -, rfl⟩; exact hbd z' w⟩
  have hg0 : ∀ k z', 0 ≤ g k z' := fun k z' =>
    (abs_nonneg _).trans (le_csSup (hbdd k z') ⟨y₀, mem_insert _ _, rfl⟩)
  have hg2 : ∀ k z', g k z' ≤ 2 * ‖f‖ := fun k z' =>
    csSup_le (hne k z') (by rintro _ ⟨w, -, rfl⟩; exact hbd z' w)
  have hgle : ∀ k n z', k ≤ n → |f (y n, z') - f (y₀, z')| ≤ g k z' := fun k n z' hkn =>
    le_csSup (hbdd k z') ⟨y n, mem_insert_of_mem _ ⟨n - k, by
      simp only; rw [Nat.sub_add_cancel hkn]⟩, rfl⟩
  have hgc : ∀ k, Continuous (g k) := fun k => (hW k).continuous_sSup hh
  set G : ℕ → Z →ᵇ ℝ := fun k => BoundedContinuousFunction.mkOfBound ⟨g k, hgc k⟩ (2 * ‖f‖)
    fun a b => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq, abs_le]
      constructor <;> linarith [hg0 k a, hg0 k b, hg2 k a, hg2 k b]
  -- `gₖ ↓ 0` pointwise
  have hgk : ∀ z', Tendsto (fun k => g k z') atTop (𝓝 0) := fun z' => by
    have hc : Tendsto (fun n => f (y n, z')) atTop (𝓝 (f (y₀, z'))) :=
      (f.continuous.tendsto _).comp (hy.prodMk_nhds tendsto_const_nhds)
    rw [Metric.tendsto_nhds] at hc ⊢
    intro ε hε
    obtain ⟨K, hK⟩ := eventually_atTop.1 (hc (ε / 2) (half_pos hε))
    refine eventually_atTop.2 ⟨K, fun k hk => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hg0 k z')]
    refine lt_of_le_of_lt (csSup_le (hne k z') ?_) (half_lt_self hε)
    rintro _ ⟨w, hw, rfl⟩
    rcases hw with rfl | ⟨n, rfl⟩
    · simp only [h, sub_self, abs_zero]; positivity
    · have := hK (n + k) (by omega)
      rw [Real.dist_eq] at this; exact this.le
  -- `∫ gₖ dν₀ → 0` by dominated convergence
  have hGk : Tendsto (fun k => ∫ z', g k z' ∂ν₀) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := ν₀) (fun _ => 2 * ‖f‖)
      (fun k => (hgc k).aestronglyMeasurable) (integrable_const _)
      (fun k => Eventually.of_forall fun z' => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg0 k z')]; exact hg2 k z')
      (Eventually.of_forall hgk)
    simpa using this
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨k, hk⟩ := (hGk.eventually (gt_mem_nhds (half_pos hε))).exists
  have hconvk : Tendsto (fun n => ∫ z', g k z' ∂ν n) atTop (𝓝 (∫ z', g k z' ∂ν₀)) := hν (G k)
  filter_upwards [hconvk.eventually (gt_mem_nhds (show ∫ z', g k z' ∂ν₀ < ε by linarith)),
    eventually_ge_atTop k] with n hn hkn
  have hint : Integrable (fun z' => |f (y n, z') - f (y₀, z')|) (ν n) :=
    gp_integrable_of_bounded ((hh.comp (continuous_id.prodMk continuous_const)).measurable)
      (M := 2 * ‖f‖) fun z' => by
        rw [abs_abs]; exact hbd z' (y n)
  have h1 : ∫ z', |f (y n, z') - f (y₀, z')| ∂ν n ≤ ∫ z', g k z' ∂ν n :=
    integral_mono hint ((G k).integrable _) fun z' => hgle k n z' hkn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
  linarith

/-- **Lemma 12.14** (continuity). For a Feller transition function `Q` on `Z` and bounded continuous
`f` on `X × Z`, `(Tf)(y, z) = ∫ f(y, z′) Q(z, dz′)` is bounded and continuous. (The book takes
`X ⊆ ℝˡ`, `Z ⊆ ℝᵏ` convex; continuity holds for any metric spaces.) -/
theorem slp_lemma_12_14_cont (Q : Kernel Z Z) [IsMarkovKernel Q] (hQ : IsFeller Q)
    (f : X × Z →ᵇ ℝ) :
    Continuous (fun p : X × Z => ∫ z', f (p.1, z') ∂Q p.2) ∧
      ∀ p : X × Z, |∫ z', f (p.1, z') ∂Q p.2| ≤ ‖f‖ := by
  refine ⟨?_, fun p => ?_⟩
  · rw [continuous_iff_seqContinuous]
    intro p p₀ hp
    have hy : Tendsto (fun n => (p n).1) atTop (𝓝 p₀.1) := (continuous_fst.tendsto _).comp hp
    have hz : Tendsto (fun n => (p n).2) atTop (𝓝 p₀.2) := (continuous_snd.tendsto _).comp hp
    have hQz := (slp_ex_12_7 Q).1.1 hQ _ _ hz
    set F₀ : Z →ᵇ ℝ := f.compContinuous ⟨fun z' => (p₀.1, z'), by fun_prop⟩
    have hv : Tendsto (fun n => ∫ z', f (p₀.1, z') ∂Q (p n).2) atTop
        (𝓝 (∫ z', f (p₀.1, z') ∂Q p₀.2)) := hQz F₀
    have hd := gp_tendsto_integral_abs_sub f hy hQz
    have hu : Tendsto (fun n => ∫ z', f ((p n).1, z') ∂Q (p n).2 -
        ∫ z', f (p₀.1, z') ∂Q (p n).2) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => ?_) hd
      set Fn : Z →ᵇ ℝ := f.compContinuous ⟨fun z' => ((p n).1, z'), by fun_prop⟩
      rw [← integral_sub (f := fun z' => f ((p n).1, z')) (g := fun z' => f (p₀.1, z'))
        (Fn.integrable _) (F₀.integrable _)]
      exact norm_integral_le_integral_norm _
    have := hu.add hv
    simp only [sub_add_cancel, zero_add] at this
    exact this
  · have := norm_integral_le_of_norm_le_const (μ := Q p.2) (C := ‖f‖)
      (f := fun z' => f (p.1, z')) (Eventually.of_forall fun z' => f.norm_coe_le_norm _)
    rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this

variable {l : ℕ} {E : Set (Fin l → ℝ)}

omit [MetricSpace Z] [BorelSpace Z] in
/-- **Lemma 12.14** (monotonicity). If `f(·, z′)` is nondecreasing on `X` for every `z′`, so is
`Tf(·, z)`. -/
theorem slp_lemma_12_14_mono (Q : Kernel Z Z) [IsMarkovKernel Q] {f : (Fin l → ℝ) → Z → ℝ}
    (hint : ∀ y ∈ E, ∀ z, Integrable (f y) (Q z)) (hf : ∀ z', MonotoneOn (fun y => f y z') E)
    (z : Z) : MonotoneOn (fun y => ∫ z', f y z' ∂Q z) E := fun y hy y' hy' hyy' =>
  integral_mono (hint y hy z) (hint y' hy' z) fun z' => hf z' hy hy' hyy'

omit [MetricSpace Z] [BorelSpace Z] in
/-- A strict pointwise inequality between integrable functions integrates to a strict inequality
under a probability measure. -/
theorem gp_integral_lt_integral_of_lt {μ : Measure Z} [IsProbabilityMeasure μ] {u v : Z → ℝ}
    (hu : Integrable u μ) (hv : Integrable v μ) (h : ∀ z, u z < v z) :
    ∫ z, u z ∂μ < ∫ z, v z ∂μ := by
  have hpos : 0 < ∫ z, (v z - u z) ∂μ := by
    rw [integral_pos_iff_support_of_nonneg (fun z => (sub_pos.2 (h z)).le) (hv.sub hu)]
    have : Function.support (fun z => v z - u z) = univ :=
      eq_univ_of_forall fun z => (sub_pos.2 (h z)).ne'
    rw [this, measure_univ]; exact zero_lt_one
  rw [integral_sub hv hu] at hpos
  linarith

omit [MetricSpace Z] [BorelSpace Z] in
/-- **Lemma 12.14** (strict monotonicity). -/
theorem slp_lemma_12_14_strictMono (Q : Kernel Z Z) [IsMarkovKernel Q] {f : (Fin l → ℝ) → Z → ℝ}
    (hint : ∀ y ∈ E, ∀ z, Integrable (f y) (Q z)) (hf : ∀ z', StrictMonoOn (fun y => f y z') E)
    (z : Z) : StrictMonoOn (fun y => ∫ z', f y z' ∂Q z) E := fun y hy y' hy' hyy' =>
  gp_integral_lt_integral_of_lt (hint y hy z) (hint y' hy' z) fun z' => hf z' hy hy' hyy'

omit [MetricSpace Z] [BorelSpace Z] in
/-- **Lemma 12.14** (concavity). If `f(·, z′)` is concave on the convex set `X` for every `z′`,
so is `Tf(·, z)`. -/
theorem slp_lemma_12_14_concave (Q : Kernel Z Z) [IsMarkovKernel Q] {f : (Fin l → ℝ) → Z → ℝ}
    (hint : ∀ y ∈ E, ∀ z, Integrable (f y) (Q z)) (hE : Convex ℝ E)
    (hf : ∀ z', ConcaveOn ℝ E (fun y => f y z')) (z : Z) :
    ConcaveOn ℝ E (fun y => ∫ z', f y z' ∂Q z) := by
  refine ⟨hE, fun y hy y' hy' α β hα hβ hαβ => ?_⟩
  simp only [smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((hint y hy z).const_mul α) ((hint y' hy' z).const_mul β)]
  refine integral_mono (((hint y hy z).const_mul α).add ((hint y' hy' z).const_mul β))
    (hint _ (hE hy hy' hα hβ hαβ) z) fun z' => ?_
  have := (hf z').2 hy hy' hα hβ hαβ
  simpa only [smul_eq_mul] using this

omit [MetricSpace Z] [BorelSpace Z] in
/-- **Lemma 12.14** (strict concavity). -/
theorem slp_lemma_12_14_strictConcave (Q : Kernel Z Z) [IsMarkovKernel Q]
    {f : (Fin l → ℝ) → Z → ℝ} (hint : ∀ y ∈ E, ∀ z, Integrable (f y) (Q z)) (hE : Convex ℝ E)
    (hf : ∀ z', StrictConcaveOn ℝ E (fun y => f y z')) (z : Z) :
    StrictConcaveOn ℝ E (fun y => ∫ z', f y z' ∂Q z) := by
  refine ⟨hE, fun y hy y' hy' hne α β hα hβ hαβ => ?_⟩
  simp only [smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((hint y hy z).const_mul α) ((hint y' hy' z).const_mul β)]
  refine gp_integral_lt_integral_of_lt (((hint y hy z).const_mul α).add
    ((hint y' hy' z).const_mul β)) (hint _ (hE hy hy' hα.le hβ.le hαβ) z) fun z' => ?_
  have := (hf z').2 hy hy' hne hα hβ hαβ
  simpa only [smul_eq_mul] using this

end Miao.MarkovProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Monotone processes and continuous dependence on parameters

Miao, §3.3.2, pp. 112–113. The book cites SLP for both theorems; the proofs are SLP's
Theorems 12.12 and 12.13, copied in `ConvergenceSLPMonotoneProcesses` and
`ConvergenceSLPParameters`.

* **Definition 3.3.6**: `P` is increasing if `T` maps bounded increasing (measurable) functions to
  increasing functions: SLP's `IsMonotoneTF` (`definition_3_3_6`). "Increasing" is read as
  nondecreasing for the componentwise order, and `f` must be measurable for `Tf` to be defined.
* The **Mixing Condition** (`MixingCondition`), SLP's Assumption 12.1. `X = [a, b] ⊂ ℝˡ` is the
  subtype `Set.Icc a b` of `Fin l → ℝ`, and `[c, b]`, `[a, c]` are `Set.Ici c`, `Set.Iic c` in it.
* **Theorem 3.3.5** (`theorem_3_3_5`): a unique invariant `λ*` and `T*ⁿλ₀ ⇒ λ*` for all `λ₀`.
* **Theorem 3.3.6** (`theorem_3_3_6`, and `theorem_3_3_6_euclidean` in the book's setting
  `X ⊆ ℝˡ` compact, `Θ ⊆ ℝᵐ`): `θₙ → θ₀` implies `μ_{θₙ} ⇒ μ_{θ₀}`. The general version holds for
  any compact metric `X` and metric `Θ`.
-/

namespace Miao.MarkovProcesses

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- **Definition 3.3.6** (Miao, p. 112): `P` is **increasing** if `Tf` is increasing for every
bounded increasing (measurable) `f`. -/
theorem definition_3_3_6 {X : Type*} [MeasurableSpace X] [Preorder X] (κ : Kernel X X) :
    IsMonotoneTF κ ↔ ∀ f : X → ℝ, Measurable f → (∃ M, ∀ x, |f x| ≤ M) → Monotone f →
      Monotone (markovOpR κ f) := Iff.rfl

variable {l : ℕ} {a b : Fin l → ℝ}

/-- The **Mixing Condition** (Miao, p. 112): `X = [a, b] ⊂ ℝˡ`, and for some `c ∈ X`, `ε > 0`,
`N ≥ 1`: `Pᴺ(a, [c, b]) ≥ ε` and `Pᴺ(b, [a, c]) ≥ ε`. -/
def MixingCondition (hab : a ≤ b) (κ : Kernel (Set.Icc a b) (Set.Icc a b)) (c : Set.Icc a b)
    (ε : ℝ) (N : ℕ) : Prop :=
  0 < ε ∧ 1 ≤ N ∧ ε ≤ (kpow κ N (gp_IccBot hab)).real (Set.Ici c) ∧
    ε ≤ (kpow κ N (gp_IccTop hab)).real (Set.Iic c)

theorem gp_mixingCondition_iff (hab : a ≤ b) (κ : Kernel (Set.Icc a b) (Set.Icc a b))
    (c : Set.Icc a b) (ε : ℝ) (N : ℕ) :
    MixingCondition hab κ c ε N ↔ gp_Assumption12_1 hab κ c ε N := Iff.rfl

/-- **Theorem 3.3.5** (Miao, p. 112; SLP Theorem 12.12). On `X = [a, b] ⊂ ℝˡ`, if `P` is
increasing, has the Feller property and satisfies the Mixing Condition, then `P` has a unique
invariant probability measure `λ*`, and `T*ⁿλ₀ ⇒ λ*` for every `λ₀ ∈ P(X, 𝒳)`. -/
theorem theorem_3_3_5 (hab : a ≤ b) (κ : Kernel (Set.Icc a b) (Set.Icc a b)) [IsMarkovKernel κ]
    (hM : IsMonotoneTF κ) (hF : IsFeller κ) {c : Set.Icc a b} {ε : ℝ} {N : ℕ}
    (hmix : MixingCondition hab κ c ε N) :
    ∃ lstar : Measure (Set.Icc a b), IsProbabilityMeasure lstar ∧ adjointOp κ lstar = lstar ∧
      (∀ ν : Measure (Set.Icc a b), IsProbabilityMeasure ν → adjointOp κ ν = ν → ν = lstar) ∧
      ∀ lam₀ : Measure (Set.Icc a b), IsProbabilityMeasure lam₀ →
        ConvWeak (fun n => adjointOp (kpow κ n) lam₀) lstar := by
  obtain ⟨μ, hμ, hinv, huniq, hconv⟩ := slp_theorem_12_12 hab κ hM hF hmix
  refine ⟨μ, hμ, hinv, huniq, fun lam₀ h₀ => ?_⟩
  have := hconv lam₀ h₀
  simpa only [gp_adjointOp_iterate] using this

/-- **Theorem 3.3.6** (Miao, p. 113; SLP Theorem 12.13), for a compact metric state space `X` and
a metric parameter space `Θ`. If (b) `(xₙ, θₙ) → (x₀, θ₀)` implies `P_{θₙ}(xₙ, ·) ⇒ P_{θ₀}(x₀, ·)`
and (c) each `T*_θ` has a unique fixed point `μ_θ`, then `θₙ → θ₀` implies `μ_{θₙ} ⇒ μ_{θ₀}`. -/
theorem theorem_3_3_6 {X Θ : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Θ] [CompactSpace X] (P : Θ → Kernel X X) [∀ θ, IsMarkovKernel (P θ)]
    (hcont : ∀ (x : ℕ → X) (θ : ℕ → Θ) (x₀ : X) (θ₀ : Θ), Tendsto x atTop (𝓝 x₀) →
      Tendsto θ atTop (𝓝 θ₀) → ConvWeak (fun n => P (θ n) (x n)) (P θ₀ x₀))
    (μ : Θ → Measure X) [∀ θ, IsProbabilityMeasure (μ θ)]
    (hfix : ∀ θ, adjointOp (P θ) (μ θ) = μ θ)
    (huniq : ∀ θ (ν : Measure X), IsProbabilityMeasure ν → adjointOp (P θ) ν = ν → ν = μ θ)
    {θ : ℕ → Θ} {θ₀ : Θ} (hθ : Tendsto θ atTop (𝓝 θ₀)) :
    ConvWeak (fun n => μ (θ n)) (μ θ₀) :=
  slp_theorem_12_13 P hcont μ hfix huniq hθ

/-- **Theorem 3.3.6** (Miao, p. 113) in the book's setting: `X ⊆ ℝˡ` compact, `Θ ⊆ ℝᵐ`. -/
theorem theorem_3_3_6_euclidean {m : ℕ} {K : Set (Fin l → ℝ)} (hK : IsCompact K)
    {Θ : Set (Fin m → ℝ)} (P : Θ → Kernel K K) [∀ θ, IsMarkovKernel (P θ)]
    (hcont : ∀ (x : ℕ → K) (θ : ℕ → Θ) (x₀ : K) (θ₀ : Θ), Tendsto x atTop (𝓝 x₀) →
      Tendsto θ atTop (𝓝 θ₀) → ConvWeak (fun n => P (θ n) (x n)) (P θ₀ x₀))
    (μ : Θ → Measure K) [∀ θ, IsProbabilityMeasure (μ θ)]
    (hfix : ∀ θ, adjointOp (P θ) (μ θ) = μ θ)
    (huniq : ∀ θ (ν : Measure K), IsProbabilityMeasure ν → adjointOp (P θ) ν = ν → ν = μ θ)
    {θ : ℕ → Θ} {θ₀ : Θ} (hθ : Tendsto θ atTop (𝓝 θ₀)) :
    ConvWeak (fun n => μ (θ n)) (μ θ₀) := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  exact theorem_3_3_6 P hcont μ hfix huniq hθ

end Miao.MarkovProcesses

set_option linter.style.longLine false
#print axioms Miao.MarkovProcesses.mc_IsAddClosed
#print axioms Miao.MarkovProcesses.mc_setGcd
#print axioms Miao.MarkovProcesses.mc_IsAddClosed.succ_mul_mem
#print axioms Miao.MarkovProcesses.mc_IsAddClosed.mul_mem_zero
#print axioms Miao.MarkovProcesses.mc_IsAddClosed.add_mem_of_zero
#print axioms Miao.MarkovProcesses.mc_exists_gcd_witness
#print axioms Miao.MarkovProcesses.mc_setGcd_spec
#print axioms Miao.MarkovProcesses.mc_setGcd_dvd
#print axioms Miao.MarkovProcesses.dvd_mc_setGcd
#print axioms Miao.MarkovProcesses.mc_setGcd_pos
#print axioms Miao.MarkovProcesses.mc_eventually_mul_setGcd_mem
#print axioms Miao.MarkovProcesses.mc_eventually_mem_of_setGcd_eq_one
#print axioms Miao.MarkovProcesses.mc_setGcd_eq_of_shift
#print axioms Miao.MarkovProcesses.mc_pow_mem
#print axioms Miao.MarkovProcesses.mc_pow_nonneg
#print axioms Miao.MarkovProcesses.mc_pow_le_one
#print axioms Miao.MarkovProcesses.mc_pow_row_sum
#print axioms Miao.MarkovProcesses.mc_entry_nonneg
#print axioms Miao.MarkovProcesses.eq_3_1
#print axioms Miao.MarkovProcesses.mc_pow_add_ge
#print axioms Miao.MarkovProcesses.mc_pow_add_pos
#print axioms Miao.MarkovProcesses.mc_exists_pos_entry
#print axioms Miao.MarkovProcesses.mc_IsClosed
#print axioms Miao.MarkovProcesses.mc_pow_eq_zero_of_closed
#print axioms Miao.MarkovProcesses.mc_Accessible
#print axioms Miao.MarkovProcesses.mc_Communicate
#print axioms Miao.MarkovProcesses.mc_Accessible.trans
#print axioms Miao.MarkovProcesses.mc_accessible_of_pos
#print axioms Miao.MarkovProcesses.mc_communicate_equivalence
#print axioms Miao.MarkovProcesses.mc_Communicate.accessible_trans
#print axioms Miao.MarkovProcesses.mc_IsIrreducible
#print axioms Miao.MarkovProcesses.mc_IsDecomposable
#print axioms Miao.MarkovProcesses.mc_isDecomposable_iff
#print axioms Miao.MarkovProcesses.mc_isIrreducible_iff
#print axioms Miao.MarkovProcesses.mc_IsRecurrent
#print axioms Miao.MarkovProcesses.mc_IsTransient
#print axioms Miao.MarkovProcesses.mc_isTransient_iff
#print axioms Miao.MarkovProcesses.mc_returnSet
#print axioms Miao.MarkovProcesses.mc_period
#print axioms Miao.MarkovProcesses.mc_IsAperiodic
#print axioms Miao.MarkovProcesses.mc_IsPeriodic
#print axioms Miao.MarkovProcesses.mc_returnSet_isAddClosed
#print axioms Miao.MarkovProcesses.mc_period_dvd
#print axioms Miao.MarkovProcesses.mc_period_spec
#print axioms Miao.MarkovProcesses.mc_IsRecurrent.of_communicate
#print axioms Miao.MarkovProcesses.theorem_3_1_1a
#print axioms Miao.MarkovProcesses.mc_consSet
#print axioms Miao.MarkovProcesses.mc_mem_consSet
#print axioms Miao.MarkovProcesses.theorem_3_1_1b
#print axioms Miao.MarkovProcesses.theorem_3_1_1c
#print axioms Miao.MarkovProcesses.mc_chain012
#print axioms Miao.MarkovProcesses.mc_chain012_mem
#print axioms Miao.MarkovProcesses.theorem_3_1_1b_proof_counterexample
#print axioms Miao.MarkovProcesses.theorem_3_1_2
#print axioms Miao.MarkovProcesses.mc_classOf
#print axioms Miao.MarkovProcesses.mc_mem_classOf
#print axioms Miao.MarkovProcesses.mc_SumsToOne
#print axioms Miao.MarkovProcesses.mc_IsErgodicSetLiteral
#print axioms Miao.MarkovProcesses.mc_IsErgodicSet
#print axioms Miao.MarkovProcesses.remark_3_1_1_literal
#print axioms Miao.MarkovProcesses.mc_sumsToOne_iff_closed
#print axioms Miao.MarkovProcesses.mc_classOf_closed
#print axioms Miao.MarkovProcesses.ex_3_1
#print axioms Miao.MarkovProcesses.mc_IsStationary
#print axioms Miao.MarkovProcesses.mc_vecMul_apply
#print axioms Miao.MarkovProcesses.mc_dist_succ
#print axioms Miao.MarkovProcesses.mc_IsStationary.pow
#print axioms Miao.MarkovProcesses.mc_IsStationary.apply_eq
#print axioms Miao.MarkovProcesses.mc_IsStationary.le_apply
#print axioms Miao.MarkovProcesses.mc_IsStationary.convex
#print axioms Miao.MarkovProcesses.mc_exists_pos_of_sum_eq_one
#print axioms Miao.MarkovProcesses.mc_colMin
#print axioms Miao.MarkovProcesses.mc_colMax
#print axioms Miao.MarkovProcesses.mc_colMin_le
#print axioms Miao.MarkovProcesses.mc_le_colMax
#print axioms Miao.MarkovProcesses.mc_colMax_le_one
#print axioms Miao.MarkovProcesses.mc_colMin_nonneg
#print axioms Miao.MarkovProcesses.mc_avg_ge
#print axioms Miao.MarkovProcesses.mc_avg_le
#print axioms Miao.MarkovProcesses.theorem_3_1_3_mono
#print axioms Miao.MarkovProcesses.theorem_3_1_3_anti
#print axioms Miao.MarkovProcesses.theorem_3_1_3_min_step
#print axioms Miao.MarkovProcesses.theorem_3_1_3_max_step
#print axioms Miao.MarkovProcesses.theorem_3_1_3_gap_step
#print axioms Miao.MarkovProcesses.theorem_3_1_3
#print axioms Miao.MarkovProcesses.mc_swap
#print axioms Miao.MarkovProcesses.mc_swap_mem
#print axioms Miao.MarkovProcesses.mc_swap_sq
#print axioms Miao.MarkovProcesses.mc_swap_pow_even
#print axioms Miao.MarkovProcesses.mc_swap_pow_odd
#print axioms Miao.MarkovProcesses.theorem_3_1_3_counterexample
#print axioms Miao.MarkovProcesses.mc_pow_eq_zero_of_not_accessible
#print axioms Miao.MarkovProcesses.mc_exists_stationary
#print axioms Miao.MarkovProcesses.mc_stationary_pos_of
#print axioms Miao.MarkovProcesses.mc_stationary_unique_of
#print axioms Miao.MarkovProcesses.mc_stationary_unique_of_irreducible
#print axioms Miao.MarkovProcesses.mc_stationary_pos_of_irreducible
#print axioms Miao.MarkovProcesses.mc_irreducible_stationary
#print axioms Miao.MarkovProcesses.stationary_p97_transient
#print axioms Miao.MarkovProcesses.mc_classOf_communicate
#print axioms Miao.MarkovProcesses.mc_classOf_eq
#print axioms Miao.MarkovProcesses.mc_classDist
#print axioms Miao.MarkovProcesses.stationary_p97_class
#print axioms Miao.MarkovProcesses.mc_recClasses
#print axioms Miao.MarkovProcesses.mc_mem_recClasses
#print axioms Miao.MarkovProcesses.stationary_p97_decomposition
#print axioms Miao.MarkovProcesses.stationary_p97_infinite
#print axioms Miao.MarkovProcesses.mc_IsAperiodicChain
#print axioms Miao.MarkovProcesses.theorem_3_1_4
#print axioms Miao.MarkovProcesses.mc_not_accessible_of_closed
#print axioms Miao.MarkovProcesses.mc_isRecurrent_of_closed
#print axioms Miao.MarkovProcesses.mc_isAperiodic_of_pos
#print axioms Miao.MarkovProcesses.mc_pow_absorbing
#print axioms Miao.MarkovProcesses.fig31
#print axioms Miao.MarkovProcesses.fig31_mem
#print axioms Miao.MarkovProcesses.fig31_closed
#print axioms Miao.MarkovProcesses.fig31_communicate
#print axioms Miao.MarkovProcesses.fig31_recurrent
#print axioms Miao.MarkovProcesses.ex311
#print axioms Miao.MarkovProcesses.ex311_mem
#print axioms Miao.MarkovProcesses.example_3_1_1_pow
#print axioms Miao.MarkovProcesses.ex311Lim
#print axioms Miao.MarkovProcesses.example_3_1_1_tendsto
#print axioms Miao.MarkovProcesses.example_3_1_1_stationary
#print axioms Miao.MarkovProcesses.ex312
#print axioms Miao.MarkovProcesses.mc_IsPosStochastic
#print axioms Miao.MarkovProcesses.mc_fromBlocks_diag_pow
#print axioms Miao.MarkovProcesses.example_3_1_2_pow_even
#print axioms Miao.MarkovProcesses.example_3_1_2_pow_odd
#print axioms Miao.MarkovProcesses.ex312_mem
#print axioms Miao.MarkovProcesses.example_3_1_2_classes
#print axioms Miao.MarkovProcesses.example_3_1_2_stationary
#print axioms Miao.MarkovProcesses.example_3_1_2_not_tendsto
#print axioms Miao.MarkovProcesses.ex313
#print axioms Miao.MarkovProcesses.ex313_mem
#print axioms Miao.MarkovProcesses.example_3_1_3_pow
#print axioms Miao.MarkovProcesses.example_3_1_3_tendsto
#print axioms Miao.MarkovProcesses.example_3_1_3_classes
#print axioms Miao.MarkovProcesses.ex316
#print axioms Miao.MarkovProcesses.ex316_mem
#print axioms Miao.MarkovProcesses.example_3_1_6_classes
#print axioms Miao.MarkovProcesses.example_3_1_6_infinite
#print axioms Miao.MarkovProcesses.mc_isStationary_of_detailed_balance
#print axioms Miao.MarkovProcesses.ex33Fn
#print axioms Miao.MarkovProcesses.ex33
#print axioms Miao.MarkovProcesses.ex33_mem
#print axioms Miao.MarkovProcesses.ex33Dist
#print axioms Miao.MarkovProcesses.ex33_irreducible
#print axioms Miao.MarkovProcesses.ex33_detailed_balance
#print axioms Miao.MarkovProcesses.ex_3_3
#print axioms Miao.MarkovProcesses.ex_3_3_half
#print axioms Miao.MarkovProcesses.ex_3_3_limit_lt
#print axioms Miao.MarkovProcesses.ex_3_3_limit_gt
#print axioms Miao.MarkovProcesses.ex_3_6_irreducible
#print axioms Miao.MarkovProcesses.ex_3_6
#print axioms Miao.MarkovProcesses.mc_IsStochasticE
#print axioms Miao.MarkovProcesses.mc_mulE
#print axioms Miao.MarkovProcesses.mc_idE
#print axioms Miao.MarkovProcesses.mc_powE
#print axioms Miao.MarkovProcesses.mc_mulE_assoc
#print axioms Miao.MarkovProcesses.mc_idE_mulE
#print axioms Miao.MarkovProcesses.mc_mulE_idE
#print axioms Miao.MarkovProcesses.mc_powE_one
#print axioms Miao.MarkovProcesses.mc_powE_add
#print axioms Miao.MarkovProcesses.mc_powE_succ'
#print axioms Miao.MarkovProcesses.eq_3_1_countable
#print axioms Miao.MarkovProcesses.mc_powE_add_ge
#print axioms Miao.MarkovProcesses.mc_powE_add_pos
#print axioms Miao.MarkovProcesses.mc_powE_row_sum
#print axioms Miao.MarkovProcesses.mc_powE_le_one
#print axioms Miao.MarkovProcesses.mc_le_one_of_stochasticE
#print axioms Miao.MarkovProcesses.mc_AccessibleE
#print axioms Miao.MarkovProcesses.mc_CommunicateE
#print axioms Miao.MarkovProcesses.mc_IsIrreducibleE
#print axioms Miao.MarkovProcesses.mc_AccessibleE.trans
#print axioms Miao.MarkovProcesses.mc_accessibleE_of_pos
#print axioms Miao.MarkovProcesses.mc_isIrreducibleE_iff
#print axioms Miao.MarkovProcesses.mc_returnSetE
#print axioms Miao.MarkovProcesses.mc_periodE
#print axioms Miao.MarkovProcesses.mc_returnSetE_isAddClosed
#print axioms Miao.MarkovProcesses.theorem_3_1_2_countable
#print axioms Miao.MarkovProcesses.theorem_3_1_4_countable
#print axioms Miao.MarkovProcesses.mc_tabooE
#print axioms Miao.MarkovProcesses.mc_fpE
#print axioms Miao.MarkovProcesses.mc_hitE
#print axioms Miao.MarkovProcesses.mc_meanRetE
#print axioms Miao.MarkovProcesses.mc_visitsE
#print axioms Miao.MarkovProcesses.mc_IsTransientE
#print axioms Miao.MarkovProcesses.mc_IsRecurrentE
#print axioms Miao.MarkovProcesses.mc_IsPositiveRecurrentE
#print axioms Miao.MarkovProcesses.mc_IsNullRecurrentE
#print axioms Miao.MarkovProcesses.mc_tsum_split
#print axioms Miao.MarkovProcesses.mc_tsum_taboo
#print axioms Miao.MarkovProcesses.mc_fpE_zero
#print axioms Miao.MarkovProcesses.mc_fpE_succ
#print axioms Miao.MarkovProcesses.mc_hitE_le_one
#print axioms Miao.MarkovProcesses.mc_first_entrance
#print axioms Miao.MarkovProcesses.mc_fpE_le_powE
#print axioms Miao.MarkovProcesses.mc_tsum_cauchy
#print axioms Miao.MarkovProcesses.mc_visits_eq
#print axioms Miao.MarkovProcesses.mc_sum_cauchy_le
#print axioms Miao.MarkovProcesses.mc_le_of_le_add_mul
#print axioms Miao.MarkovProcesses.mc_sum_powE_ne_top
#print axioms Miao.MarkovProcesses.mc_isTransientE_iff
#print axioms Miao.MarkovProcesses.mc_isRecurrentE_iff
#print axioms Miao.MarkovProcesses.mc_tsum_shift_le
#print axioms Miao.MarkovProcesses.theorem_3_1_1a_countable
#print axioms Miao.MarkovProcesses.mc_histEvent
#print axioms Miao.MarkovProcesses.mc_IsMarkovProcess
#print axioms Miao.MarkovProcesses.mc_IsTimeHomogeneous
#print axioms Miao.MarkovProcesses.mc_cylProb
#print axioms Miao.MarkovProcesses.mc_HasChainLaw
#print axioms Miao.MarkovProcesses.mc_pathVec
#print axioms Miao.MarkovProcesses.mc_measure_path_mem
#print axioms Miao.MarkovProcesses.mc_measure_step
#print axioms Miao.MarkovProcesses.mc_measure_step_const
#print axioms Miao.MarkovProcesses.mc_markov_of_chainLaw
#print axioms Miao.MarkovProcesses.mc_marginal_of_chainLaw
#print axioms Miao.MarkovProcesses.mc_IsInvariantE
#print axioms Miao.MarkovProcesses.mc_IsStationaryE
#print axioms Miao.MarkovProcesses.mc_IsInvariantE.pow
#print axioms Miao.MarkovProcesses.mc_IsInvariantE.le
#print axioms Miao.MarkovProcesses.mc_stationaryE_pos
#print axioms Miao.MarkovProcesses.mc_stationaryE_le_one
#print axioms Miao.MarkovProcesses.mc_hitE_pos
#print axioms Miao.MarkovProcesses.mc_visitsE_le
#print axioms Miao.MarkovProcesses.mc_recurrent_of_stationary
#print axioms Miao.MarkovProcesses.mc_cycleStepE
#print axioms Miao.MarkovProcesses.mc_cycleE
#print axioms Miao.MarkovProcesses.mc_cycleStepE_succ
#print axioms Miao.MarkovProcesses.mc_cycleStepE_zero
#print axioms Miao.MarkovProcesses.mc_cycleE_self
#print axioms Miao.MarkovProcesses.mc_cycleE_invariant
#print axioms Miao.MarkovProcesses.mc_cycleE_le
#print axioms Miao.MarkovProcesses.mc_tsum_tsum_add
#print axioms Miao.MarkovProcesses.mc_cycleE_mass
#print axioms Miao.MarkovProcesses.mc_hitE_le_meanRetE
#print axioms Miao.MarkovProcesses.mc_stationary_of_posRec
#print axioms Miao.MarkovProcesses.mc_stationary_eq_inv
#print axioms Miao.MarkovProcesses.mc_transient_or_recurrent
#print axioms Miao.MarkovProcesses.theorem_3_1_5a
#print axioms Miao.MarkovProcesses.theorem_3_1_5b
#print axioms Miao.MarkovProcesses.theorem_3_1_5c
#print axioms Miao.MarkovProcesses.theorem_3_1_5_trichotomy
#print axioms Miao.MarkovProcesses.mc_toE
#print axioms Miao.MarkovProcesses.mc_powE_toE
#print axioms Miao.MarkovProcesses.mc_toE_stochastic
#print axioms Miao.MarkovProcesses.theorem_3_1_5_finite
#print axioms Miao.MarkovProcesses.mc_tsum_pair
#print axioms Miao.MarkovProcesses.ex314
#print axioms Miao.MarkovProcesses.ex314_stochastic
#print axioms Miao.MarkovProcesses.ex314_col_zero
#print axioms Miao.MarkovProcesses.ex314_col_succ
#print axioms Miao.MarkovProcesses.ex314_pow_ne_zero
#print axioms Miao.MarkovProcesses.example_3_1_4_irreducible
#print axioms Miao.MarkovProcesses.theorem_3_1_4_countable_counterexample
#print axioms Miao.MarkovProcesses.ex314_taboo_sum
#print axioms Miao.MarkovProcesses.example_3_1_4_transient
#print axioms Miao.MarkovProcesses.example_3_1_4_stationary
#print axioms Miao.MarkovProcesses.example_3_1_4_half
#print axioms Miao.MarkovProcesses.ex315
#print axioms Miao.MarkovProcesses.ex315_stochastic
#print axioms Miao.MarkovProcesses.ex315_col
#print axioms Miao.MarkovProcesses.ex315_pow_parity
#print axioms Miao.MarkovProcesses.example_3_1_5
#print axioms Miao.MarkovProcesses.mc_shift
#print axioms Miao.MarkovProcesses.theorem_3_1_1b_countable_counterexample
#print axioms Miao.MarkovProcesses.IsTransitionFunction
#print axioms Miao.MarkovProcesses.gp_isTransitionFunction_iff
#print axioms Miao.MarkovProcesses.markovOp
#print axioms Miao.MarkovProcesses.markovOpR
#print axioms Miao.MarkovProcesses.adjointOp
#print axioms Miao.MarkovProcesses.gp_markovOp_indicator
#print axioms Miao.MarkovProcesses.slp_theorem_8_1
#print axioms Miao.MarkovProcesses.gp_integrable_of_bounded
#print axioms Miao.MarkovProcesses.slp_theorem_8_1_cor
#print axioms Miao.MarkovProcesses.slp_ex_8_1
#print axioms Miao.MarkovProcesses.gp_adjointOp_apply
#print axioms Miao.MarkovProcesses.slp_theorem_8_2
#print axioms Miao.MarkovProcesses.slp_ex_8_2
#print axioms Miao.MarkovProcesses.slp_theorem_8_3
#print axioms Miao.MarkovProcesses.slp_theorem_8_3_cor
#print axioms Miao.MarkovProcesses.gp_pairing
#print axioms Miao.MarkovProcesses.slp_ex_8_3
#print axioms Miao.MarkovProcesses.kpow
#print axioms Miao.MarkovProcesses.gp_kpow_one
#print axioms Miao.MarkovProcesses.slp_ex_8_4a
#print axioms Miao.MarkovProcesses.gp_kpow_add
#print axioms Miao.MarkovProcesses.gp_markovOp_comp
#print axioms Miao.MarkovProcesses.gp_adjointOp_comp
#print axioms Miao.MarkovProcesses.slp_ex_8_4b
#print axioms Miao.MarkovProcesses.gp_adjointOp_iterate
#print axioms Miao.MarkovProcesses.IsFeller
#print axioms Miao.MarkovProcesses.IsMonotoneTF
#print axioms Miao.MarkovProcesses.IsStochasticKernel
#print axioms Miao.MarkovProcesses.definition_3_2_1
#print axioms Miao.MarkovProcesses.definition_3_2_1_transition
#print axioms Miao.MarkovProcesses.theorem_3_2_1
#print axioms Miao.MarkovProcesses.eq_3_4
#print axioms Miao.MarkovProcesses.eq_3_4_unique
#print axioms Miao.MarkovProcesses.theorem_3_2_5
#print axioms Miao.MarkovProcesses.eq_3_5
#print axioms Miao.MarkovProcesses.ex_3_2
#print axioms Miao.MarkovProcesses.ex_3_4
#print axioms Miao.MarkovProcesses.eq_p103_T
#print axioms Miao.MarkovProcesses.eq_p103_Tstar
#print axioms Miao.MarkovProcesses.eq_p104_iterate
#print axioms Miao.MarkovProcesses.IsInvariantDist
#print axioms Miao.MarkovProcesses.isInvariantDist_iff
#print axioms Miao.MarkovProcesses.gp_eq_of_map_frestrictLe
#print axioms Miao.MarkovProcesses.tulceaFD
#print axioms Miao.MarkovProcesses.gp_trajMeasure_map_frestrictLe
#print axioms Miao.MarkovProcesses.tulceaFD_zero
#print axioms Miao.MarkovProcesses.tulceaFD_succ
#print axioms Miao.MarkovProcesses.theorem_3_2_4
#print axioms Miao.MarkovProcesses.gp_snocIic
#print axioms Miao.MarkovProcesses.gp_measurable_snocIic
#print axioms Miao.MarkovProcesses.gp_snocIic_pair
#print axioms Miao.MarkovProcesses.gp_snocIic_restrict
#print axioms Miao.MarkovProcesses.gp_frestrictLe_zero
#print axioms Miao.MarkovProcesses.gp_lastKernel
#print axioms Miao.MarkovProcesses.gp_isMarkovKernel_lastKernel
#print axioms Miao.MarkovProcesses.markovPath
#print axioms Miao.MarkovProcesses.gp_isProbabilityMeasure_markovPath
#print axioms Miao.MarkovProcesses.gp_markovPath_markov
#print axioms Miao.MarkovProcesses.gp_markovPath_map_zero
#print axioms Miao.MarkovProcesses.gp_markovPath_unique
#print axioms Miao.MarkovProcesses.theorem_3_2_3
#print axioms Miao.MarkovProcesses.theorem_3_2_3_transition
#print axioms Miao.MarkovProcesses.theorem_3_2_3_marginal
#print axioms Miao.MarkovProcesses.gp_extendBox
#print axioms Miao.MarkovProcesses.gp_preimage_extendBox
#print axioms Miao.MarkovProcesses.eq_3_2_iff
#print axioms Miao.MarkovProcesses.theorem_3_2_2
#print axioms Miao.MarkovProcesses.gp_IsPartition
#print axioms Miao.MarkovProcesses.gp_partSums
#print axioms Miao.MarkovProcesses.gp_tvOf
#print axioms Miao.MarkovProcesses.tvNorm
#print axioms Miao.MarkovProcesses.tvDist
#print axioms Miao.MarkovProcesses.gp_supDiff
#print axioms Miao.MarkovProcesses.gp_isPartition_univ
#print axioms Miao.MarkovProcesses.gp_isPartition_pair
#print axioms Miao.MarkovProcesses.gp_partSums_nonempty
#print axioms Miao.MarkovProcesses.gp_sum_partition_real
#print axioms Miao.MarkovProcesses.gp_sum_partition_inter_real
#print axioms Miao.MarkovProcesses.gp_partSums_bddAbove_of_le
#print axioms Miao.MarkovProcesses.gp_partSums_le_of_measures
#print axioms Miao.MarkovProcesses.gp_bddAbove_tvDist
#print axioms Miao.MarkovProcesses.slp_lemma_11_5
#print axioms Miao.MarkovProcesses.gp_exists_sub_measures
#print axioms Miao.MarkovProcesses.gp_tvNorm_sub_eq
#print axioms Miao.MarkovProcesses.gp_bddAbove_tvNorm
#print axioms Miao.MarkovProcesses.gp_tvOf_nonneg
#print axioms Miao.MarkovProcesses.gp_abs_le_tvOf
#print axioms Miao.MarkovProcesses.slp_ex_11_3
#print axioms Miao.MarkovProcesses.gp_abs_sub_le_add
#print axioms Miao.MarkovProcesses.gp_bddAbove_supDiff
#print axioms Miao.MarkovProcesses.gp_two_abs_le_tvDist
#print axioms Miao.MarkovProcesses.gp_tvDist_le_of_forall
#print axioms Miao.MarkovProcesses.gp_tvDist_nonneg
#print axioms Miao.MarkovProcesses.gp_tendsto_zero_iff_of_nonneg
#print axioms Miao.MarkovProcesses.slp_theorem_11_6
#print axioms Miao.MarkovProcesses.gp_integrable_of_abs_le
#print axioms Miao.MarkovProcesses.gp_abs_add_abs_compl_le
#print axioms Miao.MarkovProcesses.gp_abs_integral_sub_le_tvDist
#print axioms Miao.MarkovProcesses.gp_iInter_tails_eq_empty
#print axioms Miao.MarkovProcesses.slp_lemma_11_8
#print axioms Miao.MarkovProcesses.ConditionMFor
#print axioms Miao.MarkovProcesses.ConditionM
#print axioms Miao.MarkovProcesses.gp_isMarkov_kpow
#print axioms Miao.MarkovProcesses.gp_tvDist_comm
#print axioms Miao.MarkovProcesses.gp_tvDist_triangle
#print axioms Miao.MarkovProcesses.gp_tvDist_le_two
#print axioms Miao.MarkovProcesses.gp_eq_of_tvDist_eq_zero
#print axioms Miao.MarkovProcesses.gp_bind_real_eq
#print axioms Miao.MarkovProcesses.slp_lemma_11_11
#print axioms Miao.MarkovProcesses.gp_isProb_adjoint
#print axioms Miao.MarkovProcesses.gp_adjoint_add
#print axioms Miao.MarkovProcesses.gp_tvDist_iterate_le
#print axioms Miao.MarkovProcesses.slp_theorem_11_12
#print axioms Miao.MarkovProcesses.slp_theorem_11_12_converse
#print axioms Miao.MarkovProcesses.dTV
#print axioms Miao.MarkovProcesses.gp_dTV_eq_supDiff
#print axioms Miao.MarkovProcesses.gp_tvDist_eq_two_mul_dTV
#print axioms Miao.MarkovProcesses.gp_abs_le_dTV
#print axioms Miao.MarkovProcesses.gp_dTV_le_of_forall
#print axioms Miao.MarkovProcesses.gp_dTV_nonneg
#print axioms Miao.MarkovProcesses.gp_dTV_le_one
#print axioms Miao.MarkovProcesses.eq_p105_metric
#print axioms Miao.MarkovProcesses.eq_p105_complete
#print axioms Miao.MarkovProcesses.ConvStrongly
#print axioms Miao.MarkovProcesses.theorem_3_3_1_contraction
#print axioms Miao.MarkovProcesses.gp_eq_3_8_iff
#print axioms Miao.MarkovProcesses.theorem_3_3_1
#print axioms Miao.MarkovProcesses.theorem_3_3_1_invariant
#print axioms Miao.MarkovProcesses.theorem_3_3_1_converse
#print axioms Miao.MarkovProcesses.MinorizationFor
#print axioms Miao.MarkovProcesses.Minorization
#print axioms Miao.MarkovProcesses.proposition_3_3_1_forward
#print axioms Miao.MarkovProcesses.gp_threeKernel
#print axioms Miao.MarkovProcesses.gp_threeKernel_real
#print axioms Miao.MarkovProcesses.proposition_3_3_1_counterexample
#print axioms Miao.MarkovProcesses.proposition_3_3_1_of_atom
#print axioms Miao.MarkovProcesses.proposition_3_3_1
#print axioms Miao.MarkovProcesses.example_3_3_1
#print axioms Miao.MarkovProcesses.example_3_3_2
#print axioms Miao.MarkovProcesses.example_3_3_3
#print axioms Miao.MarkovProcesses.example_3_3_3_finite
#print axioms Miao.MarkovProcesses.gp_withDensity_real
#print axioms Miao.MarkovProcesses.gp_integrable_density
#print axioms Miao.MarkovProcesses.ex_3_5b
#print axioms Miao.MarkovProcesses.eq_3_7
#print axioms Miao.MarkovProcesses.ex_3_5a
#print axioms Miao.MarkovProcesses.slp_ex_12_1
#print axioms Miao.MarkovProcesses.slp_ex_12_2
#print axioms Miao.MarkovProcesses.gp_bump
#print axioms Miao.MarkovProcesses.gp_continuous_bump
#print axioms Miao.MarkovProcesses.gp_bump_mem
#print axioms Miao.MarkovProcesses.gp_bump_eq_one
#print axioms Miao.MarkovProcesses.gp_bump_antitone
#print axioms Miao.MarkovProcesses.gp_tendsto_bump
#print axioms Miao.MarkovProcesses.ConvWeak
#print axioms Miao.MarkovProcesses.slp_lemma_12_1
#print axioms Miao.MarkovProcesses.gp_count_bounds
#print axioms Miao.MarkovProcesses.slp_lemma_12_2
#print axioms Miao.MarkovProcesses.gp_LimsupLe
#print axioms Miao.MarkovProcesses.gp_LiminfGe
#print axioms Miao.MarkovProcesses.gp_tendsto_of_limsup_liminf
#print axioms Miao.MarkovProcesses.gp_toBCF
#print axioms Miao.MarkovProcesses.gp_limsup_closed_of_weak
#print axioms Miao.MarkovProcesses.gp_limsup_integral_of_closed
#print axioms Miao.MarkovProcesses.gp_weak_of_limsup_closed
#print axioms Miao.MarkovProcesses.gp_liminf_open_of_limsup_closed
#print axioms Miao.MarkovProcesses.gp_limsup_closed_of_liminf_open
#print axioms Miao.MarkovProcesses.gp_tendsto_of_null_frontier
#print axioms Miao.MarkovProcesses.gp_limsup_closed_of_null_frontier
#print axioms Miao.MarkovProcesses.slp_theorem_12_3
#print axioms Miao.MarkovProcesses.gp_tendsto_finite_union
#print axioms Miao.MarkovProcesses.slp_theorem_12_4
#print axioms Miao.MarkovProcesses.slp_theorem_12_5
#print axioms Miao.MarkovProcesses.gp_IsConvDetermining
#print axioms Miao.MarkovProcesses.gp_frontier_iInter_fin_subset
#print axioms Miao.MarkovProcesses.gp_ballInters
#print axioms Miao.MarkovProcesses.slp_theorem_12_5_cor
#print axioms Miao.MarkovProcesses.slp_theorem_12_6
#print axioms Miao.MarkovProcesses.slp_theorem_12_6_cor1
#print axioms Miao.MarkovProcesses.slp_theorem_12_6_cor2
#print axioms Miao.MarkovProcesses.gp_convWeak_unique
#print axioms Miao.MarkovProcesses.gp_IsConvDetermining.eq
#print axioms Miao.MarkovProcesses.gp_distFun
#print axioms Miao.MarkovProcesses.gp_box
#print axioms Miao.MarkovProcesses.gp_vertex
#print axioms Miao.MarkovProcesses.gp_vertexSum
#print axioms Miao.MarkovProcesses.gp_diag
#print axioms Miao.MarkovProcesses.gp_ContFromAbove
#print axioms Miao.MarkovProcesses.gp_ContFromBelow
#print axioms Miao.MarkovProcesses.gp_Iic_eq_pi
#print axioms Miao.MarkovProcesses.gp_box_indicator_eq
#print axioms Miao.MarkovProcesses.gp_measurableSet_box
#print axioms Miao.MarkovProcesses.gp_vertexSum_eq
#print axioms Miao.MarkovProcesses.gp_distFun_mono
#print axioms Miao.MarkovProcesses.gp_contFromAbove_distFun
#print axioms Miao.MarkovProcesses.slp_theorem_12_7a
#print axioms Miao.MarkovProcesses.gp_generateFrom_Iic_pi
#print axioms Miao.MarkovProcesses.gp_distFun_injective
#print axioms Miao.MarkovProcesses.gp_lowerOpen
#print axioms Miao.MarkovProcesses.gp_frontier_Iic_eq
#print axioms Miao.MarkovProcesses.gp_lowerOpen_subset
#print axioms Miao.MarkovProcesses.gp_tendsto_distFun_below
#print axioms Miao.MarkovProcesses.slp_theorem_12_7c
#print axioms Miao.MarkovProcesses.slp_ex_12_3
#print axioms Miao.MarkovProcesses.gp_nullCoord
#print axioms Miao.MarkovProcesses.gp_countable_nullCoord_compl
#print axioms Miao.MarkovProcesses.gp_dense_nullCoord
#print axioms Miao.MarkovProcesses.gp_continuousAt_distFun
#print axioms Miao.MarkovProcesses.gp_frontier_null_of_continuousAt
#print axioms Miao.MarkovProcesses.gp_box_inter
#print axioms Miao.MarkovProcesses.gp_box_eq_empty
#print axioms Miao.MarkovProcesses.slp_theorem_12_8
#print axioms Miao.MarkovProcesses.slp_ex_12_4
#print axioms Miao.MarkovProcesses.slp_ex_12_5a
#print axioms Miao.MarkovProcesses.gp_ramp
#print axioms Miao.MarkovProcesses.gp_continuous_ramp
#print axioms Miao.MarkovProcesses.gp_ramp_mem
#print axioms Miao.MarkovProcesses.gp_monotone_ramp
#print axioms Miao.MarkovProcesses.gp_tendsto_ramp
#print axioms Miao.MarkovProcesses.slp_ex_12_5b
#print axioms Miao.MarkovProcesses.gp_IsSupport
#print axioms Miao.MarkovProcesses.gp_support_inter
#print axioms Miao.MarkovProcesses.gp_exists_support
#print axioms Miao.MarkovProcesses.gp_exists_convWeak_subseq_of_tight
#print axioms Miao.MarkovProcesses.gp_measure_eq_one_of_convWeak
#print axioms Miao.MarkovProcesses.slp_theorem_12_9_cor1
#print axioms Miao.MarkovProcesses.gp_concentrated_iff
#print axioms Miao.MarkovProcesses.slp_theorem_12_9
#print axioms Miao.MarkovProcesses.gp_distFun_dirac
#print axioms Miao.MarkovProcesses.gp_not_convWeak_escape
#print axioms Miao.MarkovProcesses.slp_theorem_12_9_false_hyp
#print axioms Miao.MarkovProcesses.slp_theorem_12_9_false_concl
#print axioms Miao.MarkovProcesses.slp_ex_12_6a
#print axioms Miao.MarkovProcesses.slp_ex_12_6a_false
#print axioms Miao.MarkovProcesses.slp_ex_12_6b
#print axioms Miao.MarkovProcesses.slp_ex_12_6c
#print axioms Miao.MarkovProcesses.slp_theorem_12_9_cor2
#print axioms Miao.MarkovProcesses.gp_bcf_abs_le_norm
#print axioms Miao.MarkovProcesses.gp_convWeak_dirac
#print axioms Miao.MarkovProcesses.gp_adjointOp_dirac
#print axioms Miao.MarkovProcesses.gp_integral_markovOpR
#print axioms Miao.MarkovProcesses.gp_fellerBCF
#print axioms Miao.MarkovProcesses.gp_fellerBCF_apply
#print axioms Miao.MarkovProcesses.slp_ex_12_7
#print axioms Miao.MarkovProcesses.gp_flipKernel
#print axioms Miao.MarkovProcesses.gp_isMarkovKernel_flipKernel
#print axioms Miao.MarkovProcesses.gp_adjointOp_flip
#print axioms Miao.MarkovProcesses.gp_adjointOp_flip_dirac
#print axioms Miao.MarkovProcesses.slp_ex_12_8a
#print axioms Miao.MarkovProcesses.gp_iterate_flip_dirac
#print axioms Miao.MarkovProcesses.gp_symm_ne_self
#print axioms Miao.MarkovProcesses.slp_ex_12_8b
#print axioms Miao.MarkovProcesses.slp_ex_12_8c
#print axioms Miao.MarkovProcesses.gp_isProbabilityMeasure_iterate
#print axioms Miao.MarkovProcesses.gp_invariant_of_convWeak
#print axioms Miao.MarkovProcesses.slp_theorem_12_10
#print axioms Miao.MarkovProcesses.IsTightFamily
#print axioms Miao.MarkovProcesses.definition_3_3_2
#print axioms Miao.MarkovProcesses.definition_3_3_4
#print axioms Miao.MarkovProcesses.gp_exists_convWeak_subseq
#print axioms Miao.MarkovProcesses.theorem_3_3_2
#print axioms Miao.MarkovProcesses.theorem_3_3_2_counterexample
#print axioms Miao.MarkovProcesses.eq_p104_strong_imp_weak
#print axioms Miao.MarkovProcesses.eq_p108_dirac
#print axioms Miao.MarkovProcesses.theorem_3_3_3
#print axioms Miao.MarkovProcesses.corollary_3_3_1
#print axioms Miao.MarkovProcesses.IsPInvariantSet
#print axioms Miao.MarkovProcesses.IsErgodicMeasure
#print axioms Miao.MarkovProcesses.IsErgodicSetBook
#print axioms Miao.MarkovProcesses.definition_3_3_5_ergodicSet_eq_empty
#print axioms Miao.MarkovProcesses.example_p111_invariant
#print axioms Miao.MarkovProcesses.example_p111_ergodic
#print axioms Miao.MarkovProcesses.gp_adjointOp_add_smul
#print axioms Miao.MarkovProcesses.gp_adjointOp_smul
#print axioms Miao.MarkovProcesses.theorem_3_3_4_convex
#print axioms Miao.MarkovProcesses.gp_adjointOp_withDensity
#print axioms Miao.MarkovProcesses.gp_ae_eq_one_of_lintegral
#print axioms Miao.MarkovProcesses.gp_exists_invariantSet
#print axioms Miao.MarkovProcesses.gp_ae_invariant_of_density
#print axioms Miao.MarkovProcesses.gp_density_invariantSet
#print axioms Miao.MarkovProcesses.theorem_3_3_4_extreme
#print axioms Miao.MarkovProcesses.theorem_3_3_4_singular
#print axioms Miao.MarkovProcesses.theorem_3_3_4_combination_counterexample
#print axioms Miao.MarkovProcesses.Dominates
#print axioms Miao.MarkovProcesses.Dominates.trans
#print axioms Miao.MarkovProcesses.Dominates.real_le
#print axioms Miao.MarkovProcesses.slp_ex_12_9a
#print axioms Miao.MarkovProcesses.slp_ex_12_9a_subtype
#print axioms Miao.MarkovProcesses.gp_measure_lower_le
#print axioms Miao.MarkovProcesses.slp_ex_12_9b
#print axioms Miao.MarkovProcesses.gp_real_half_dirac
#print axioms Miao.MarkovProcesses.slp_ex_12_9c
#print axioms Miao.MarkovProcesses.gp_distFun_map_val
#print axioms Miao.MarkovProcesses.slp_ex_12_10
#print axioms Miao.MarkovProcesses.slp_ex_12_11
#print axioms Miao.MarkovProcesses.gp_markovOpR_kpow_zero
#print axioms Miao.MarkovProcesses.gp_markovOpR_kpow_add
#print axioms Miao.MarkovProcesses.gp_isMonotoneTF_kpow
#print axioms Miao.MarkovProcesses.gp_iterate_dirac
#print axioms Miao.MarkovProcesses.gp_dominates_iterate
#print axioms Miao.MarkovProcesses.gp_IccBot
#print axioms Miao.MarkovProcesses.gp_IccTop
#print axioms Miao.MarkovProcesses.gp_IccBot_le
#print axioms Miao.MarkovProcesses.gp_le_IccTop
#print axioms Miao.MarkovProcesses.gp_dominates_dirac_bot_top
#print axioms Miao.MarkovProcesses.gp_exists_subtype_measure
#print axioms Miao.MarkovProcesses.gp_map_val_Icc
#print axioms Miao.MarkovProcesses.gp_convWeak_of_dominance_mono
#print axioms Miao.MarkovProcesses.slp_ex_12_12
#print axioms Miao.MarkovProcesses.gp_Assumption12_1
#print axioms Miao.MarkovProcesses.slp_ex_12_14
#print axioms Miao.MarkovProcesses.slp_lemma_12_11
#print axioms Miao.MarkovProcesses.slp_theorem_12_12
#print axioms Miao.MarkovProcesses.gp_tendsto_uniform_markovOp
#print axioms Miao.MarkovProcesses.slp_theorem_12_13
#print axioms Miao.MarkovProcesses.gp_tendsto_integral_abs_sub
#print axioms Miao.MarkovProcesses.slp_lemma_12_14_cont
#print axioms Miao.MarkovProcesses.slp_lemma_12_14_mono
#print axioms Miao.MarkovProcesses.gp_integral_lt_integral_of_lt
#print axioms Miao.MarkovProcesses.slp_lemma_12_14_strictMono
#print axioms Miao.MarkovProcesses.slp_lemma_12_14_concave
#print axioms Miao.MarkovProcesses.slp_lemma_12_14_strictConcave
#print axioms Miao.MarkovProcesses.definition_3_3_6
#print axioms Miao.MarkovProcesses.MixingCondition
#print axioms Miao.MarkovProcesses.gp_mixingCondition_iff
#print axioms Miao.MarkovProcesses.theorem_3_3_5
#print axioms Miao.MarkovProcesses.theorem_3_3_6
#print axioms Miao.MarkovProcesses.theorem_3_3_6_euclidean
