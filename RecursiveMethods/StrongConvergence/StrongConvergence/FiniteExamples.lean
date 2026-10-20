/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StrongConvergence.FiniteConvergence

/-!
# Finite Markov chains: Examples 1–5

SLP §11.1, pp. 321–325.

* **Example 1** (`ex1`): `Π = [3/4 1/4; 1/4 3/4]`. `Πⁿ` has diagonal `1/2 + 2⁻⁽ⁿ⁺¹⁾` and
  off-diagonal `1/2 − 2⁻⁽ⁿ⁺¹⁾` (`ex1_pow`), with the book's `Π²`, `Π³`, `Π⁴`; it converges to the
  matrix with all entries `1/2`. `S` is the only ergodic set, and `(1/2, 1/2)` is invariant.
* **Example 2** (`ex2`): one transient state; `Πⁿ` has first row `((1−γ)ⁿ, δₙ/2, δₙ/2)` with
  `δₙ = 1 − (1 − γ)ⁿ`, and converges.
* **Example 3** (`ex3`): `Π = [0 Π₁; Π₂ 0]` with `Π₁ = Π₂` the matrix of Example 1, on
  `S = {1, 2} ⊔ {3, 4}`. `Π²ⁿ` and `Π²ⁿ⁺¹` converge to the book's limits, `Πⁿ` does not, and the
  averages converge to the matrix with all entries `1/4`. `S` is the only ergodic set, and it
  has cyclically moving subsets.
* **Example 4** (`ex4`): `Π = [Π₁ 0; 0 Π₂]`: two ergodic sets, `Πⁿ` converges, and every convex
  combination of the two invariant distributions is invariant.
* **Example 5** (`ex5`): one transient state and two absorbing states; `Πⁿ` converges, and the
  limit's first row is `(0, α, β)`.
-/

namespace StokeyLucasPrescott.StrongConvergence

open Matrix Finset Filter Topology

/-! ### Example 1 -/

/-- The matrix of Example 1. -/
noncomputable def ex1 : Matrix (Fin 2) (Fin 2) ℝ := !![3 / 4, 1 / 4; 1 / 4, 3 / 4]

theorem ex1_mem : ex1 ∈ rowStochastic ℝ (Fin 2) := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_⟩ <;> fin_cases i <;> (try fin_cases j) <;>
    simp [ex1, Fin.sum_univ_two] <;> norm_num

/-- `Πⁿ` in Example 1. -/
theorem ex1_pow (n : ℕ) :
    ex1 ^ n = !![1 / 2 + (1 / 2) ^ (n + 1), 1 / 2 - (1 / 2) ^ (n + 1);
      1 / 2 - (1 / 2) ^ (n + 1), 1 / 2 + (1 / 2) ^ (n + 1)] := by
  induction n with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp <;> norm_num
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ex1, mul_apply, Fin.sum_univ_two] <;> ring

/-- The book's `Π²`, `Π³`, `Π⁴` (p. 321). -/
theorem ex1_pow_234 :
    ex1 ^ 2 = !![5 / 8, 3 / 8; 3 / 8, 5 / 8] ∧ ex1 ^ 3 = !![9 / 16, 7 / 16; 7 / 16, 9 / 16] ∧
      ex1 ^ 4 = !![17 / 32, 15 / 32; 15 / 32, 17 / 32] := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [ex1_pow] <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp <;> norm_num

/-- `Πⁿ → [1/2 1/2; 1/2 1/2]`. -/
theorem ex1_tendsto :
    Tendsto (fun n => ex1 ^ n) atTop (𝓝 !![1 / 2, 1 / 2; 1 / 2, 1 / 2]) := by
  have h : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (tendsto_add_atTop_nat 1)
  rw [tendsto_matrix_iff]
  intro i j
  simp only [ex1_pow]
  fin_cases i <;> fin_cases j <;> simp
  · simpa using h.const_add (1 / 2 : ℝ)
  · simpa using h.const_sub (1 / 2 : ℝ)
  · simpa using h.const_sub (1 / 2 : ℝ)
  · simpa using h.const_add (1 / 2 : ℝ)

/-- In Example 1, `S` is the only ergodic set, and `p* = (1/2, 1/2)` is invariant. -/
theorem ex1_ergodic :
    (∀ E, IsErgodic ex1 E ↔ E = univ) ∧ IsInvariantDist ex1 ![1 / 2, 1 / 2] := by
  have hpos : ∀ i j, 0 < ex1 i j := fun i j => by
    fin_cases i <;> fin_cases j <;> simp [ex1]
  have hcons : ∀ i j, Cons ex1 i j := fun i j => ⟨1, le_rfl, by rw [pow_one]; exact hpos i j⟩
  obtain ⟨E₀, hE₀, huniq⟩ := (theorem_11_2 ex1_mem).1.2 ⟨0, fun i => hcons i 0⟩
  refine ⟨fun E => ⟨fun hE => ?_, fun hE => ?_⟩, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hE.1
    rw [hE.eq_consSet ex1_mem hi]
    ext j; simp [mem_consSet, hcons]
  · subst hE
    have : E₀ = univ := by
      obtain ⟨i, hi⟩ := hE₀.1
      rw [hE₀.eq_consSet ex1_mem hi]
      ext j; simp [mem_consSet, hcons]
    rw [← this]; exact hE₀
  · refine ⟨fun i => by fin_cases i <;> simp, by simp [Fin.sum_univ_two]; norm_num⟩
  · ext j; fin_cases j <;> simp [ex1, vecMul, dotProduct, Fin.sum_univ_two] <;> norm_num

/-! ### Example 2 -/

/-- The matrix of Example 2. -/
noncomputable def ex2 (γ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 - γ, γ / 2, γ / 2; 0, 1 / 2, 1 / 2; 0, 1 / 2, 1 / 2]

/-- `Πⁿ` in Example 2, for `n ≥ 1`, with `δₙ = 1 − (1 − γ)ⁿ`. -/
theorem ex2_pow (γ : ℝ) (n : ℕ) :
    ex2 γ ^ (n + 1) = !![(1 - γ) ^ (n + 1), (1 - (1 - γ) ^ (n + 1)) / 2,
      (1 - (1 - γ) ^ (n + 1)) / 2; 0, 1 / 2, 1 / 2; 0, 1 / 2, 1 / 2] := by
  induction n with
  | zero => rw [zero_add, pow_one]; ext i j; fin_cases i <;> fin_cases j <;> simp [ex2]
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ex2, mul_apply, Fin.sum_univ_three] <;> ring

/-- In Example 2, `Πⁿ` converges to the matrix with rows `(0, 1/2, 1/2)`. -/
theorem ex2_tendsto {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    Tendsto (fun n => ex2 γ ^ n) atTop
      (𝓝 !![0, 1 / 2, 1 / 2; 0, 1 / 2, 1 / 2; 0, 1 / 2, 1 / 2]) := by
  have h : Tendsto (fun n : ℕ => (1 - γ) ^ (n + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)).comp
      (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n : ℕ => (1 - (1 - γ) ^ (n + 1)) / 2) atTop (𝓝 2⁻¹) := by
    simpa using (h.const_sub 1).div_const 2
  rw [← tendsto_add_atTop_iff_nat 1, tendsto_matrix_iff]
  intro i j
  simp only [ex2_pow]
  fin_cases i <;> fin_cases j <;> simp [h, h2]

/-- In Example 2, `s₁` is transient and `{s₂, s₃}` is the only ergodic set. -/
theorem ex2_ergodic {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    IsTransient (ex2 γ) 0 ∧ ∀ E, IsErgodic (ex2 γ) E ↔ E = {1, 2} := by
  have hP : ex2 γ ∈ rowStochastic ℝ (Fin 3) := by
    rw [mem_rowStochastic_iff_sum]
    refine ⟨fun i j => ?_, fun i => ?_⟩ <;> fin_cases i <;> (try fin_cases j) <;>
      simp [ex2, Fin.sum_univ_three] <;> linarith
  have hclosed : IsClosedSet (ex2 γ) {1, 2} := isClosedSet_of hP fun i hi j hj => by
    fin_cases i <;> fin_cases j <;> simp_all [ex2]
  have hcons1 : ∀ i, Cons (ex2 γ) i 1 := fun i => ⟨1, le_rfl, by
    rw [pow_one]; fin_cases i <;> norm_num [ex2, hγ0]⟩
  have hcons : ∀ j, Cons (ex2 γ) 1 j ↔ j ∈ ({1, 2} : Finset (Fin 3)) := fun j => by
    constructor
    · rintro ⟨n, -, hn⟩; exact hclosed.mem_of_pow_pos hP (by simp) n hn
    · intro hj
      refine ⟨1, le_rfl, ?_⟩
      rw [pow_one]
      fin_cases j <;> simp_all [ex2]
  have hE12 : consSet (ex2 γ) 1 = {1, 2} := by ext j; rw [mem_consSet, hcons]
  obtain ⟨E₀, hE₀, huniq⟩ := (theorem_11_2 hP).1.2 ⟨1, hcons1⟩
  have hE₀eq : E₀ = {1, 2} := by
    obtain ⟨i, hi⟩ := hE₀.1
    have h1 : (1 : Fin 3) ∈ E₀ := hE₀.eq_consSet hP hi ▸ mem_consSet.2 (hcons1 i)
    rw [hE₀.eq_consSet hP h1, hE12]
  refine ⟨⟨1, hcons1 0, fun n hn => ?_⟩, fun E => ⟨fun hE => (huniq E hE).trans hE₀eq,
    fun hE => hE ▸ hE₀eq ▸ hE₀⟩⟩
  exact le_antisymm (not_lt.1 fun hp => by
    have := hclosed.mem_of_pow_pos hP (by simp) n hp; simp at this) (pow_nonneg' hP n 1 0)

/-! ### Example 5 -/

/-- The matrix of Example 5. -/
noncomputable def ex5 (α β γ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 - γ, α * γ, β * γ; 0, 1, 0; 0, 0, 1]

/-- `Πⁿ` in Example 5, with `δₙ = 1 − (1 − γ)ⁿ`. -/
theorem ex5_pow (α β γ : ℝ) (n : ℕ) :
    ex5 α β γ ^ n = !![(1 - γ) ^ n, α * (1 - (1 - γ) ^ n), β * (1 - (1 - γ) ^ n); 0, 1, 0;
      0, 0, 1] := by
  induction n with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ex5, mul_apply, Fin.sum_univ_three] <;> ring

/-- In Example 5, `Πⁿ` converges; its limit's first row is `(0, α, β)`, a convex combination of
the rows for the two absorbing states. -/
theorem ex5_tendsto {α β γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    Tendsto (fun n => ex5 α β γ ^ n) atTop (𝓝 !![0, α, β; 0, 1, 0; 0, 0, 1]) := by
  have h : Tendsto (fun n : ℕ => (1 - γ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  rw [tendsto_matrix_iff]
  intro i j
  simp only [ex5_pow]
  fin_cases i <;> fin_cases j <;> simp [h]
  · simpa using (h.const_sub 1).const_mul α
  · simpa using (h.const_sub 1).const_mul β

/-- In Example 5, `{s₂}` and `{s₃}` are ergodic sets and `s₁` is transient. -/
theorem ex5_ergodic {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hαβ : α + β = 1) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) :
    IsErgodic (ex5 α β γ) {1} ∧ IsErgodic (ex5 α β γ) {2} ∧ IsTransient (ex5 α β γ) 0 := by
  have hP : ex5 α β γ ∈ rowStochastic ℝ (Fin 3) := by
    rw [mem_rowStochastic_iff_sum]
    refine ⟨fun i j => ?_, fun i => ?_⟩ <;> fin_cases i <;> (try fin_cases j) <;>
      simp [ex5, Fin.sum_univ_three] <;> nlinarith
  have hsingle : ∀ k : Fin 3, k ≠ 0 → IsErgodic (ex5 α β γ) {k} := fun k hk => by
    refine ⟨by simp, fun i hi => ?_, fun F hF hne _ => ?_⟩
    · rw [Finset.mem_singleton] at hi; subst hi
      fin_cases i <;> simp_all [ex5]
    · exact (Finset.Nonempty.subset_singleton_iff hne).1 hF
  refine ⟨hsingle 1 (by decide), hsingle 2 (by decide), 1, ⟨1, le_rfl, by
    rw [pow_one]; exact mul_pos hα hγ0⟩, fun n hn => ?_⟩
  rw [ex5_pow]
  simp

/-! ### Examples 3 and 4 -/

/-- The matrix of Example 3, with `k = l − k = 2` and `Π₁ = Π₂` from Example 1. -/
noncomputable def ex3 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ := fromBlocks 0 ex1 ex1 0

/-- The matrix of Example 4, with `Π₁ = Π₂` from Example 1. -/
noncomputable def ex4 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ := fromBlocks ex1 0 0 ex1

/-- The limit of `Πⁿ` in Example 1. -/
noncomputable def halfMat : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 2, 1 / 2; 1 / 2, 1 / 2]

theorem fromBlocks_diag_pow (A D : Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ) :
    fromBlocks A 0 0 D ^ n = fromBlocks (A ^ n) 0 0 (D ^ n) := by
  induction n with
  | zero => simp [fromBlocks_one]
  | succ n ih => rw [pow_succ, ih, fromBlocks_multiply]; simp [pow_succ]

theorem ex3_pow_even (n : ℕ) : ex3 ^ (2 * n) = fromBlocks (ex1 ^ (2 * n)) 0 0 (ex1 ^ (2 * n)) := by
  have hsq : ex3 ^ 2 = fromBlocks (ex1 ^ 2) 0 0 (ex1 ^ 2) := by
    rw [sq, ex3, fromBlocks_multiply]; simp [sq]
  rw [pow_mul, hsq, fromBlocks_diag_pow, ← pow_mul]

theorem ex3_pow_odd (n : ℕ) :
    ex3 ^ (2 * n + 1) = fromBlocks 0 (ex1 ^ (2 * n + 1)) (ex1 ^ (2 * n + 1)) 0 := by
  rw [pow_succ, ex3_pow_even, ex3, fromBlocks_multiply]; simp [pow_succ]

theorem continuous_diagBlocks :
    Continuous fun M : Matrix (Fin 2) (Fin 2) ℝ => fromBlocks M 0 0 M :=
  Continuous.matrix_fromBlocks continuous_id continuous_const continuous_const continuous_id

theorem continuous_offBlocks :
    Continuous fun M : Matrix (Fin 2) (Fin 2) ℝ => fromBlocks 0 M M 0 :=
  Continuous.matrix_fromBlocks continuous_const continuous_id continuous_id continuous_const

/-- Example 3: `Π²ⁿ` and `Π²ⁿ⁺¹` converge to the book's limits (p. 323). -/
theorem ex3_even_odd :
    Tendsto (fun n => ex3 ^ (2 * n)) atTop (𝓝 (fromBlocks halfMat 0 0 halfMat)) ∧
      Tendsto (fun n => ex3 ^ (2 * n + 1)) atTop (𝓝 (fromBlocks 0 halfMat halfMat 0)) := by
  have h2 : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_id.const_mul_atTop' (by norm_num)
  constructor
  · simp_rw [ex3_pow_even]
    exact (continuous_diagBlocks.tendsto halfMat).comp (ex1_tendsto.comp h2)
  · simp_rw [ex3_pow_odd]
    exact (continuous_offBlocks.tendsto halfMat).comp
      (ex1_tendsto.comp ((tendsto_add_atTop_nat 1).comp h2))

/-- Example 3: `Πⁿ` does not converge. -/
theorem ex3_not_tendsto : ¬ ∃ Q, Tendsto (fun n => ex3 ^ n) atTop (𝓝 Q) := by
  rintro ⟨Q, hQ⟩
  have h2 : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_id.const_mul_atTop' (by norm_num)
  have he := tendsto_nhds_unique (hQ.comp h2) ex3_even_odd.1
  have ho := tendsto_nhds_unique (hQ.comp ((tendsto_add_atTop_nat 1).comp h2)) ex3_even_odd.2
  have := congrFun (congrFun (he.symm.trans ho) (Sum.inl 0)) (Sum.inl 0)
  simp [halfMat] at this

theorem ex1_pos (i j : Fin 2) : 0 < ex1 i j := by
  fin_cases i <;> fin_cases j <;> simp [ex1]

theorem ex1_sq_pos (i j : Fin 2) : 0 < (ex1 ^ 2) i j := by
  rw [ex1_pow]; fin_cases i <;> fin_cases j <;> simp <;> norm_num

theorem ex3_mem : ex3 ∈ rowStochastic ℝ (Fin 2 ⊕ Fin 2) := by
  rw [mem_rowStochastic_iff_sum]
  have h1 := ex1_mem
  rw [mem_rowStochastic_iff_sum] at h1
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · rcases i with i | i <;> rcases j with j | j <;> simp [ex3, h1.1]
  · rcases i with i | i <;> simp [ex3, Fintype.sum_sum_type, h1.2]

/-- In Example 3 every state is a consequent of every state (in one or two steps). -/
theorem ex3_cons (i j : Fin 2 ⊕ Fin 2) : Cons ex3 i j := by
  rcases i with a | a <;> rcases j with b | b
  · exact ⟨2, by norm_num, by
      have := ex3_pow_even 1; simp only [mul_one] at this; rw [this]; simpa using ex1_sq_pos a b⟩
  · exact ⟨1, le_rfl, by rw [pow_one]; simpa [ex3] using ex1_pos a b⟩
  · exact ⟨1, le_rfl, by rw [pow_one]; simpa [ex3] using ex1_pos a b⟩
  · exact ⟨2, by norm_num, by
      have := ex3_pow_even 1; simp only [mul_one] at this; rw [this]; simpa using ex1_sq_pos a b⟩

/-- Example 3: the averages converge to the matrix with all entries `1/4` (p. 324), whose rows
are the unique invariant distribution. -/
theorem ex3_cesaro : Tendsto (cesaro ex3) atTop (𝓝 (Matrix.of fun _ _ => (1 / 4 : ℝ))) := by
  obtain ⟨Q, -, hQ, -⟩ := theorem_11_1b ex3_mem
  obtain ⟨hrows, hinv, -⟩ := (theorem_11_2 ex3_mem).2 hQ (Sum.inl 0) fun i => ex3_cons i _
  have hu : IsInvariantDist ex3 fun _ => 1 / 4 := by
    refine ⟨⟨fun _ => by norm_num, by simp⟩, ?_⟩
    ext j
    have h1 := ex1_mem
    rcases j with j | j <;> fin_cases j <;>
      simp [ex3, vecMul, dotProduct, Fintype.sum_sum_type, ex1, Fin.sum_univ_two] <;> norm_num
  have hQj := (hinv _).1 hu
  have : Q = Matrix.of fun _ _ => (1 / 4 : ℝ) := by
    ext i j; rw [hrows i, ← hQj]; rfl
  rwa [this] at hQ

/-- Example 3: `S` is the only ergodic set, and it has cyclically moving subsets
`C₁ = {s₁, s₂}`, `C₂ = {s₃, s₄}`. -/
theorem ex3_ergodic : (∀ E, IsErgodic ex3 E ↔ E = univ) ∧ HasCyclicSubsets ex3 univ := by
  have hcons : ∀ i, consSet ex3 i = univ := fun i => by ext j; simp [mem_consSet, ex3_cons]
  obtain ⟨E₀, hE₀, huniq⟩ := (theorem_11_2 ex3_mem).1.2 ⟨Sum.inl 0, fun i => ex3_cons i _⟩
  have hE₀u : E₀ = univ := by
    obtain ⟨i, hi⟩ := hE₀.1; rw [hE₀.eq_consSet ex3_mem hi, hcons]
  refine ⟨fun E => ⟨fun hE => (huniq E hE).trans hE₀u, fun hE => hE ▸ hE₀u ▸ hE₀⟩, ?_⟩
  have h1 := ex1_mem
  rw [mem_rowStochastic_iff_sum] at h1
  set C : ℕ → Finset (Fin 2 ⊕ Fin 2) := fun k =>
    if k % 2 = 0 then univ.filter (fun i => i.isLeft) else univ.filter (fun i => i.isRight)
  refine ⟨2, le_rfl, C, fun k => ?_, fun k => ?_, fun k k' hk hk' hne => ?_, fun _ => subset_univ _,
    fun i _ => ?_, fun k i hi => ?_⟩
  · simp only [C, Nat.add_mod_right]
  · simp only [C]; split_ifs
    · exact ⟨Sum.inl 0, by simp⟩
    · exact ⟨Sum.inr 0, by simp⟩
  · interval_cases k <;> interval_cases k' <;> simp_all [C, Finset.disjoint_left]
  · rcases i with a | a
    · exact ⟨0, by simp [C]⟩
    · exact ⟨1, by simp [C]⟩
  · rcases Nat.mod_two_eq_zero_or_one k with hk | hk
    · have hk1 : (k + 1) % 2 = 1 := by omega
      simp only [C, hk, hk1, ↓reduceIte, one_ne_zero, mem_filter, mem_univ, true_and] at hi ⊢
      rcases i with a | a
      · rw [sum_filter, Fintype.sum_sum_type]; simp [ex3, h1.2]
      · simp at hi
    · have hk1 : (k + 1) % 2 = 0 := by omega
      simp only [C, hk, hk1, ↓reduceIte, one_ne_zero, mem_filter, mem_univ, true_and] at hi ⊢
      rcases i with a | a
      · simp at hi
      · rw [sum_filter, Fintype.sum_sum_type]; simp [ex3, h1.2]

/-- Example 4: `Πⁿ` converges to `[Q₁ 0; 0 Q₂]` with `Q₁ = Q₂` the limit of Example 1. -/
theorem ex4_tendsto : Tendsto (fun n => ex4 ^ n) atTop (𝓝 (fromBlocks halfMat 0 0 halfMat)) := by
  simp_rw [ex4, fromBlocks_diag_pow]
  exact (continuous_diagBlocks.tendsto halfMat).comp ex1_tendsto

/-- The invariant distributions form a convex set. -/
theorem IsInvariantDist.convex {S : Type*} [Fintype S] {P : Matrix S S ℝ} {p q : S → ℝ}
    (hp : IsInvariantDist P p) (hq : IsInvariantDist P q) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsInvariantDist P (t • p + (1 - t) • q) := by
  refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hp.1.1 i, hq.1.1 i]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum, hp.1.2,
      hq.1.2]; ring
  · rw [add_vecMul, smul_vecMul, smul_vecMul, hp.2, hq.2]

/-- Example 4: two ergodic sets `E₁ = {s₁, s₂}`, `E₂ = {s₃, s₄}`, with invariant distributions
`p₁* = (1/2, 1/2, 0, 0)` and `p₂* = (0, 0, 1/2, 1/2)`; every convex combination of these is
invariant. -/
theorem ex4_ergodic :
    IsErgodic ex4 (univ.filter fun i => i.isLeft) ∧ IsErgodic ex4 (univ.filter fun i => i.isRight) ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 → IsInvariantDist ex4
        (t • (Sum.elim (fun _ => 1 / 2) 0 : Fin 2 ⊕ Fin 2 → ℝ) +
          (1 - t) • (Sum.elim 0 (fun _ => 1 / 2) : Fin 2 ⊕ Fin 2 → ℝ)) := by
  have h1 := ex1_mem
  rw [mem_rowStochastic_iff_sum] at h1
  have hP : ex4 ∈ rowStochastic ℝ (Fin 2 ⊕ Fin 2) := by
    rw [mem_rowStochastic_iff_sum]
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · rcases i with i | i <;> rcases j with j | j <;> simp [ex4, h1.1]
    · rcases i with i | i <;> simp [ex4, Fintype.sum_sum_type, h1.2]
  have hblock : ∀ (b : Bool) (E : Finset (Fin 2 ⊕ Fin 2)),
      E = univ.filter (fun i => i.isLeft = b) → IsErgodic ex4 E := by
    intro b E hE
    have hclosed : IsClosedSet ex4 E := isClosedSet_of hP fun i hi j hj => by
      subst hE
      rcases i with a | a <;> rcases j with c | c <;> simp_all [ex4]
    have hreach : ∀ i ∈ E, ∀ j ∈ E, Cons ex4 i j := fun i hi j hj => by
      subst hE
      refine ⟨1, le_rfl, ?_⟩
      rw [pow_one]
      rcases i with a | a <;> rcases j with c | c <;> simp_all [ex4, ex1_pos]
    have hne : E.Nonempty := by
      subst hE; cases b
      · exact ⟨Sum.inr 0, by simp⟩
      · exact ⟨Sum.inl 0, by simp⟩
    refine ⟨hne, hclosed, fun F hF hFne hFc => subset_antisymm hF fun j hj => ?_⟩
    obtain ⟨k, hk⟩ := hFne
    exact hFc.consSet_subset hP hk (mem_consSet.2 (hreach k (hF hk) j hj))
  refine ⟨hblock true _ (by ext i; simp), hblock false _ (by ext i; simp), fun t ht0 ht1 => ?_⟩
  refine IsInvariantDist.convex ?_ ?_ ht0 ht1
  · refine ⟨⟨fun i => by rcases i with i | i <;> simp, by simp [Fintype.sum_sum_type]⟩, ?_⟩
    ext j
    rcases j with j | j <;> fin_cases j <;>
      simp [ex4, vecMul, dotProduct, Fintype.sum_sum_type, ex1, Fin.sum_univ_two] <;> norm_num
  · refine ⟨⟨fun i => by rcases i with i | i <;> simp, by simp [Fintype.sum_sum_type]⟩, ?_⟩
    ext j
    rcases j with j | j <;> fin_cases j <;>
      simp [ex4, vecMul, dotProduct, Fintype.sum_sum_type, ex1, Fin.sum_univ_two] <;> norm_num

end StokeyLucasPrescott.StrongConvergence
