/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovProcesses.ChainStationary
import Mathlib.Data.Matrix.Block

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
