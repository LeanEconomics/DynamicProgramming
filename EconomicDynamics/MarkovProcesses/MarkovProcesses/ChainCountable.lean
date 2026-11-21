/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovProcesses.ChainNumberTheory
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.BigOperators.Intervals

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
