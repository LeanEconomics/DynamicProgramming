import Mathlib
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Finite Markov chains: long-run averages

SLP §11.1, Theorem 11.1b–c, pp. 326–328. The averages `A⁽ⁿ⁾ = (1/n) Σ_{k<n} Πᵏ` (`cesaro`) are
stochastic matrices. They lie in the compact set of matrices with entries in `[0, 1]`, so every
subsequence has a convergent subsequence. Each limit `Q` of a subsequence satisfies
`Q = QΠ = ΠQ` (`limit_mul`), since `A⁽ⁿ⁾Π − A⁽ⁿ⁾ = (Πⁿ − I)/n → 0`. Two such limits `Q`, `B`
satisfy `Q = QB = BQ = B`, so the whole sequence converges.

* **Theorem 11.1b** (`theorem_11_1b`): `A⁽ⁿ⁾ → Q`, a stochastic matrix with `Q = QΠ = ΠQ`; and
  `(1/n) Σ_{k<n} p₀Πᵏ → p₀Q` for every `p₀`.
* **Theorem 11.1c** (`theorem_11_1c`): each row of `Q` is an invariant distribution, so `p₀Q` is
  one for every `p₀ ∈ Δ`; and every invariant distribution `r` satisfies `r = rQ`, a convex
  combination of the rows of `Q`.
-/

namespace StokeyLucasPrescott.StrongConvergence

open Matrix Finset Filter Topology

variable {S : Type*} [Fintype S] [DecidableEq S] {P : Matrix S S ℝ}

/-- The average `A⁽ⁿ⁾ = (1/n) Σ_{k<n} Πᵏ`. -/
noncomputable def cesaro (P : Matrix S S ℝ) (n : ℕ) : Matrix S S ℝ :=
  (n : ℝ)⁻¹ • ∑ k ∈ range n, P ^ k

omit [Fintype S] [DecidableEq S] in
theorem tendsto_matrix_iff {ι : Type*} {l : Filter ι} {f : ι → Matrix S S ℝ}
    {M : Matrix S S ℝ} :
    Tendsto f l (𝓝 M) ↔ ∀ i j, Tendsto (fun x => f x i j) l (𝓝 (M i j)) := by
  constructor
  · intro h i j
    exact (((continuous_apply j).comp (continuous_apply i)).tendsto M).comp h
  · intro h
    exact tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => h i j

theorem simplex_vecMul (hP : P ∈ rowStochastic ℝ S) {p : S → ℝ} (hp : p ∈ simplex S) :
    p ᵥ* P ∈ simplex S := by
  refine ⟨fun j => sum_nonneg fun i _ => mul_nonneg (hp.1 i) (nonneg_of_mem_rowStochastic hP),
    ?_⟩
  simp only [vecMul, dotProduct]
  rw [sum_comm]
  simp [← mul_sum, sum_row_of_mem_rowStochastic hP, hp.2]

theorem cesaro_mem (hP : P ∈ rowStochastic ℝ S) {n : ℕ} (hn : 1 ≤ n) :
    cesaro P n ∈ rowStochastic ℝ S := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · simp only [cesaro, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
    exact mul_nonneg (inv_nonneg.2 hn'.le) (sum_nonneg fun k _ => pow_nonneg' hP k i j)
  · simp only [cesaro, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
    rw [← mul_sum, sum_comm]
    simp [pow_row_sum hP, hn'.ne']

theorem isClosed_rowStochastic : IsClosed (rowStochastic ℝ S : Set (Matrix S S ℝ)) := by
  have : (rowStochastic ℝ S : Set (Matrix S S ℝ)) =
      (⋂ i, ⋂ j, {M : Matrix S S ℝ | 0 ≤ M i j}) ∩ ⋂ i, {M | ∑ j, M i j = 1} := by
    ext M
    simp [mem_rowStochastic_iff_sum]
  rw [this]
  refine (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_le continuous_const ?_).inter
    (isClosed_iInter fun i => isClosed_eq (continuous_finsetSum _ fun j _ => ?_) continuous_const)
  · exact (continuous_apply j).comp (continuous_apply i)
  · exact (continuous_apply j).comp (continuous_apply i)

/-- The matrices with entries in `[0, 1]`. -/
def unitBox (S : Type*) : Set (Matrix S S ℝ) :=
  Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

omit [Fintype S] [DecidableEq S] in
theorem mem_unitBox {M : Matrix S S ℝ} : M ∈ unitBox S ↔ ∀ i j, M i j ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨fun h i j => h i trivial j trivial, fun h i _ j _ => h i j⟩

omit [Fintype S] [DecidableEq S] in
theorem isCompact_unitBox : IsCompact (unitBox S) :=
  isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc

theorem rowStochastic_subset_unitBox : (rowStochastic ℝ S : Set (Matrix S S ℝ)) ⊆ unitBox S :=
  fun _ hM => mem_unitBox.2 fun _ _ =>
    ⟨nonneg_of_mem_rowStochastic hM, le_one_of_mem_rowStochastic hM⟩

/-- Telescoping: `Σ_{k<n} Πᵏ⁺¹ − Σ_{k<n} Πᵏ = Πⁿ − I`. -/
theorem sum_pow_succ_sub (n : ℕ) :
    ∑ k ∈ range n, P ^ (k + 1) - ∑ k ∈ range n, P ^ k = P ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sub_eq_iff_eq_add] at ih
    rw [sum_range_succ, sum_range_succ, ih]
    abel

theorem cesaro_mul_sub (n : ℕ) : cesaro P n * P - cesaro P n = (n : ℝ)⁻¹ • (P ^ n - 1) := by
  rw [cesaro, smul_mul_assoc, sum_mul, ← smul_sub]
  simp_rw [← pow_succ]
  rw [sum_pow_succ_sub]

theorem mul_cesaro_sub (n : ℕ) : P * cesaro P n - cesaro P n = (n : ℝ)⁻¹ • (P ^ n - 1) := by
  rw [cesaro, mul_smul_comm, mul_sum, ← smul_sub]
  simp_rw [← pow_succ']
  rw [sum_pow_succ_sub]

/-- `(Πⁿ − I)/n → 0`. -/
theorem tendsto_pow_sub_div (hP : P ∈ rowStochastic ℝ S) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • (P ^ n - 1)) atTop (𝓝 0) := by
  rw [tendsto_matrix_iff]
  intro i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Matrix.zero_apply]
  have hb : ∀ n : ℕ, |(P ^ n) i j - (1 : Matrix S S ℝ) i j| ≤ 1 := fun n => by
    have h0 := pow_nonneg' hP n i j
    have h1 := pow_le_one' hP n i j
    rw [one_apply]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  refine squeeze_zero_norm (a := fun n : ℕ => (n : ℝ)⁻¹) (fun n => ?_)
    tendsto_inv_atTop_nhds_zero_nat
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg n))]
  exact mul_le_of_le_one_right (inv_nonneg.2 (Nat.cast_nonneg n)) (hb n)

/-- A limit `B` of `A⁽ᵐᵏ⁾` along indices `mₖ → ∞` satisfies `BΠ = B = ΠB`. -/
theorem limit_mul (hP : P ∈ rowStochastic ℝ S) {m : ℕ → ℕ} (hm : Tendsto m atTop atTop)
    {B : Matrix S S ℝ} (hB : Tendsto (fun k => cesaro P (m k)) atTop (𝓝 B)) :
    B * P = B ∧ P * B = B := by
  have h0 := (tendsto_pow_sub_div hP).comp hm
  constructor
  · have h1 : Tendsto (fun k => cesaro P (m k) * P - cesaro P (m k)) atTop (𝓝 (B * P - B)) :=
      ((hB.comp tendsto_id).mul_const P).sub hB
    simp_rw [cesaro_mul_sub] at h1
    exact sub_eq_zero.1 (tendsto_nhds_unique h1 h0)
  · have h1 : Tendsto (fun k => P * cesaro P (m k) - cesaro P (m k)) atTop (𝓝 (P * B - B)) :=
      (hB.const_mul P).sub hB
    simp_rw [mul_cesaro_sub] at h1
    exact sub_eq_zero.1 (tendsto_nhds_unique h1 h0)

theorem mul_pow_eq {B : Matrix S S ℝ} (h : B * P = B) (n : ℕ) : B * P ^ n = B := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← mul_assoc, ih, h]

theorem pow_mul_eq {B : Matrix S S ℝ} (h : P * B = B) (n : ℕ) : P ^ n * B = B := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_assoc, ih, h]

theorem mul_cesaro_eq {B : Matrix S S ℝ} (h : B * P = B) {n : ℕ} (hn : 1 ≤ n) :
    B * cesaro P n = B := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [cesaro, mul_smul_comm, mul_sum]
  simp_rw [mul_pow_eq h]
  rw [sum_const, card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hn', one_smul]

theorem cesaro_mul_eq {B : Matrix S S ℝ} (h : P * B = B) {n : ℕ} (hn : 1 ≤ n) :
    cesaro P n * B = B := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [cesaro, smul_mul_assoc, sum_mul]
  simp_rw [pow_mul_eq h]
  rw [sum_const, card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hn', one_smul]

/-- **Theorem 11.1b.** The averages `A⁽ⁿ⁾ = (1/n) Σ_{k<n} Πᵏ` converge to a stochastic matrix
`Q` with `Q = QΠ = ΠQ`; hence `(1/n) Σ_{k<n} p₀Πᵏ = p₀A⁽ⁿ⁾ → p₀Q` for every `p₀`. -/
theorem theorem_11_1b (hP : P ∈ rowStochastic ℝ S) :
    ∃ Q ∈ rowStochastic ℝ S, Tendsto (cesaro P) atTop (𝓝 Q) ∧ Q * P = Q ∧ P * Q = Q ∧
      ∀ p₀ : S → ℝ, Tendsto (fun n => p₀ ᵥ* cesaro P n) atTop (𝓝 (p₀ ᵥ* Q)) := by
  have : FirstCountableTopology (Matrix S S ℝ) :=
    inferInstanceAs (FirstCountableTopology (S → S → ℝ))
  have hK := isCompact_unitBox (S := S)
  have hmem : ∀ n, cesaro P n ∈ unitBox S := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact mem_unitBox.2 fun i j => by simp [cesaro]
    · exact rowStochastic_subset_unitBox (cesaro_mem hP hn)
  obtain ⟨Q, -, φ, hφ, hQ⟩ := hK.tendsto_subseq hmem
  have hQm : Tendsto φ atTop atTop := hφ.tendsto_atTop
  obtain ⟨hQP, hPQ⟩ := limit_mul hP hQm hQ
  -- every limit point equals `Q`
  have huniq : ∀ {m : ℕ → ℕ}, Tendsto m atTop atTop → ∀ {B : Matrix S S ℝ},
      Tendsto (fun k => cesaro P (m k)) atTop (𝓝 B) → B = Q := by
    intro m hm B hB
    obtain ⟨hBP, hPB⟩ := limit_mul hP hm hB
    have e2 : B * Q = B := by
      have := hQ.const_mul B
      refine tendsto_nhds_unique this (tendsto_const_nhds.congr' ?_)
      filter_upwards [hQm.eventually_ge_atTop 1] with k hk
      exact (mul_cesaro_eq hBP hk).symm
    have e3 : B * Q = Q := by
      have := hB.mul_const Q
      refine tendsto_nhds_unique this (tendsto_const_nhds.congr' ?_)
      filter_upwards [hm.eventually_ge_atTop 1] with k hk
      exact (cesaro_mul_eq hPQ hk).symm
    rw [← e2, e3]
  have hconv : Tendsto (cesaro P) atTop (𝓝 Q) := by
    refine tendsto_of_subseq_tendsto fun ns hns => ?_
    obtain ⟨B, -, ψ, hψ, hB⟩ := hK.tendsto_subseq fun k => hmem (ns k)
    have hBQ := huniq (hns.comp hψ.tendsto_atTop) hB
    exact ⟨ψ, hBQ ▸ hB⟩
  have hQs : Q ∈ rowStochastic ℝ S :=
    isClosed_rowStochastic.mem_of_tendsto hconv
      (eventually_atTop.2 ⟨1, fun n hn => cesaro_mem hP hn⟩)
  refine ⟨Q, hQs, hconv, hQP, hPQ, fun p₀ => ?_⟩
  have hc : Continuous fun M : Matrix S S ℝ => p₀ ᵥ* M :=
    continuous_const.matrix_vecMul continuous_id
  exact (hc.tendsto Q).comp hconv

/-- **Theorem 11.1c.** Each row of `Q` is an invariant distribution, hence so is `p₀Q` for every
`p₀ ∈ Δ`; and every invariant distribution `r` satisfies `rQ = r`: it is the convex combination
`Σᵢ rᵢ Qᵢ` of the rows of `Q`. -/
theorem theorem_11_1c (hP : P ∈ rowStochastic ℝ S) {Q : Matrix S S ℝ}
    (hQ : Tendsto (cesaro P) atTop (𝓝 Q)) :
    (∀ i, IsInvariantDist P (Q i)) ∧ (∀ p₀ ∈ simplex S, IsInvariantDist P (p₀ ᵥ* Q)) ∧
      ∀ r, IsInvariantDist P r → r ᵥ* Q = r := by
  have hm : Tendsto (fun n : ℕ => n) atTop atTop := tendsto_id
  obtain ⟨hQP, -⟩ := limit_mul hP hm hQ
  have hQs : Q ∈ rowStochastic ℝ S :=
    isClosed_rowStochastic.mem_of_tendsto hQ
      (eventually_atTop.2 ⟨1, fun n hn => cesaro_mem hP hn⟩)
  have hrow : ∀ i, IsInvariantDist P (Q i) := fun i => by
    refine ⟨⟨fun j => nonneg_of_mem_rowStochastic hQs, sum_row_of_mem_rowStochastic hQs i⟩, ?_⟩
    funext j
    have := congrFun (congrFun hQP i) j
    simpa [mul_apply, vecMul, dotProduct] using this
  refine ⟨hrow, fun p₀ hp₀ => ⟨simplex_vecMul hQs hp₀, ?_⟩, fun r hr => ?_⟩
  · rw [vecMul_vecMul, hQP]
  · have hpow : ∀ k, r ᵥ* P ^ k = r := fun k => by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ← vecMul_vecMul, ih, hr.2]
    have hc : ∀ n, 1 ≤ n → r ᵥ* cesaro P n = r := fun n hn => by
      have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      rw [cesaro, vecMul_smul, vecMul_sum]
      simp_rw [hpow]
      rw [sum_const, card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hn',
        one_smul]
    have hcont : Continuous fun M : Matrix S S ℝ => r ᵥ* M :=
      continuous_const.matrix_vecMul continuous_id
    have := (hcont.tendsto Q).comp hQ
    refine tendsto_nhds_unique this (tendsto_const_nhds.congr' ?_)
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (hc n hn).symm

end StokeyLucasPrescott.StrongConvergence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Finite Markov chains: ergodic sets and the limit `Q`

SLP §11.1, Exercise 11.1 and Theorem 11.2, pp. 329–331.

* `harmonic_const` (a maximum principle): a function `h` with `h = Πh` on a closed set `E`, in
  which some state `j` is reachable from every state, is constant on `E`. The columns of `Q`
  satisfy `h = Πh` because `Q = ΠQ`.
* `exists_ergodic_reach`: from every state some ergodic set is reached.
* **Theorem 11.2** (`theorem_11_2`): `Π` has a unique ergodic set iff some state `sⱼ` is a
  consequent of every state. Then all rows of `Q` equal `Qⱼ = p*`, the unique invariant
  distribution, and `p₀Q = p*` for every `p₀ ∈ Δ`. The book derives the second half from
  Theorem 11.1; here it comes from the maximum principle.
-/

namespace StokeyLucasPrescott.StrongConvergence

open Matrix Finset Filter Topology

variable {S : Type*} [Fintype S] [DecidableEq S] {P : Matrix S S ℝ}

/-- On a closed set, `h = Πh` gives `h = Πⁿh`. -/
theorem harmonic_pow (hP : P ∈ rowStochastic ℝ S) {E : Finset S} (hE : IsClosedSet P E)
    {h : S → ℝ} (hh : ∀ i ∈ E, h i = ∑ k, P i k * h k) :
    ∀ n, ∀ i ∈ E, h i = ∑ k, (P ^ n) i k * h k := by
  intro n
  induction n with
  | zero => intro i _; simp [one_apply]
  | succ n ih =>
    intro i hi
    have e : ∀ k, (P ^ (n + 1)) i k * h k = ∑ l, P i l * ((P ^ n) l k * h k) := fun k => by
      rw [pow_succ', mul_apply, sum_mul]
      exact sum_congr rfl fun l _ => by ring
    simp_rw [e]
    rw [sum_comm, hh i hi]
    refine sum_congr rfl fun l _ => ?_
    rw [← mul_sum]
    by_cases hl : l ∈ E
    · rw [← ih l hl]
    · rw [hE.apply_eq_zero hP hi hl, zero_mul, zero_mul]

/-- If `h = Πh` on a closed set `E`, `i ∈ E` maximizes `h` over `E`, and `π⁽ⁿ⁾ᵢⱼ > 0`, then `j`
also maximizes `h`. -/
theorem harmonic_max_spread (hP : P ∈ rowStochastic ℝ S) {E : Finset S} (hE : IsClosedSet P E)
    {h : S → ℝ} (hh : ∀ i ∈ E, h i = ∑ k, P i k * h k) {i : S} (hi : i ∈ E)
    (hmax : ∀ k ∈ E, h k ≤ h i) {n : ℕ} {j : S} (hj : 0 < (P ^ n) i j) : h j = h i := by
  have hjE : j ∈ E := hE.mem_of_pow_pos hP hi n hj
  have hsum : ∑ k, (P ^ n) i k * (h i - h k) = 0 := by
    simp_rw [mul_sub, sum_sub_distrib, ← sum_mul, pow_row_sum hP, one_mul]
    rw [← harmonic_pow hP hE hh n i hi, sub_self]
  have hnn : ∀ k ∈ univ, 0 ≤ (P ^ n) i k * (h i - h k) := fun k _ => by
    by_cases hk : k ∈ E
    · exact mul_nonneg (pow_nonneg' hP n i k) (sub_nonneg.2 (hmax k hk))
    · have : (P ^ n) i k = 0 := le_antisymm
        (not_lt.1 fun hp => hk (hE.mem_of_pow_pos hP hi n hp)) (pow_nonneg' hP n i k)
      rw [this, zero_mul]
  have := (sum_eq_zero_iff_of_nonneg hnn).1 hsum j (mem_univ j)
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 hj.ne'
  · linarith

/-- **Maximum principle.** If `h = Πh` on a closed set `E` and `j ∈ E` is a consequent of every
other state of `E`, then `h` is constant on `E`. -/
theorem harmonic_const (hP : P ∈ rowStochastic ℝ S) {E : Finset S} (hE : IsClosedSet P E)
    {h : S → ℝ} (hh : ∀ i ∈ E, h i = ∑ k, P i k * h k) {j : S}
    (hj : ∀ i ∈ E, i ≠ j → Cons P i j) : ∀ i ∈ E, h i = h j := by
  intro i₀ hi₀
  have hne : E.Nonempty := ⟨i₀, hi₀⟩
  obtain ⟨a, ha, hamax⟩ := exists_max_image E h hne
  obtain ⟨b, hb, hbmin⟩ := exists_min_image E h hne
  have hreach : ∀ i ∈ E, ∃ n, 0 < (P ^ n) i j := fun i hi => by
    by_cases hij : i = j
    · exact ⟨0, by rw [hij, pow_zero, one_apply_eq]; exact one_pos⟩
    · obtain ⟨n, -, hn⟩ := hj i hi hij; exact ⟨n, hn⟩
  obtain ⟨n, hn⟩ := hreach a ha
  obtain ⟨m, hm⟩ := hreach b hb
  have hja : h j = h a := harmonic_max_spread hP hE hh ha hamax hn
  have hneg : ∀ i ∈ E, -h i = ∑ k, P i k * -h k := fun i hi => by
    rw [hh i hi, ← sum_neg_distrib]
    simp
  have hjb : -h j = -h b := harmonic_max_spread hP hE hneg hb
    (fun k hk => neg_le_neg (hbmin k hk)) hm
  have h1 := hamax i₀ hi₀
  have h2 := hbmin i₀ hi₀
  linarith

/-- From every state some ergodic set is reached. -/
theorem exists_ergodic_reach (hP : P ∈ rowStochastic ℝ S) (i : S) :
    ∃ E, IsErgodic P E ∧ ∃ k ∈ E, Cons P i k := by
  obtain ⟨F, hF, hFe⟩ := exists_ergodic_subset (consSet_nonempty hP i) (consSet_closed hP i)
  obtain ⟨k, hk⟩ := hFe.1
  exact ⟨F, hFe, k, hk, mem_consSet.1 (hF hk)⟩

omit [DecidableEq S] in
/-- The columns of a matrix `B` with `ΠB = B` satisfy `h = Πh`. -/
theorem column_harmonic {B : Matrix S S ℝ} (hB : P * B = B) (c : S) :
    ∀ i, B i c = ∑ k, P i k * B k c := fun i => by
  conv_lhs => rw [← hB]
  rfl

/-- **Theorem 11.2.** `Π` has a unique ergodic set iff some state `sⱼ` is a consequent of every
state. In that case every row of `Q` is `Qⱼ`, the unique invariant distribution `p*`, and
`p₀Q = p*` for every `p₀ ∈ Δ`. -/
theorem theorem_11_2 [Nonempty S] (hP : P ∈ rowStochastic ℝ S) :
    ((∃! E, IsErgodic P E) ↔ ∃ j, ∀ i, Cons P i j) ∧
      ∀ {Q : Matrix S S ℝ}, Tendsto (cesaro P) atTop (𝓝 Q) → ∀ j, (∀ i, Cons P i j) →
        (∀ i, Q i = Q j) ∧ (∀ r, IsInvariantDist P r ↔ r = Q j) ∧
          ∀ p₀ ∈ simplex S, p₀ ᵥ* Q = Q j := by
  obtain ⟨⟨E₀, hE₀⟩, -, -, -, -⟩ := theorem_11_1a hP
  refine ⟨⟨fun ⟨E, hE, huniq⟩ => ?_, fun ⟨j, hj⟩ => ?_⟩, fun {Q} hQ j hj => ?_⟩
  · obtain ⟨j, hjE⟩ := hE.1
    refine ⟨j, fun i => ?_⟩
    obtain ⟨F, hF, k, hkF, hik⟩ := exists_ergodic_reach hP i
    have hFE := huniq F hF
    subst hFE
    exact hik.trans hP (mem_consSet.1 (hF.eq_consSet hP hkF ▸ hjE))
  · have hall : ∀ E, IsErgodic P E → E = consSet P j := fun E hE => by
      obtain ⟨i, hi⟩ := hE.1
      have hjE : j ∈ E := hE.eq_consSet hP hi ▸ mem_consSet.2 (hj i)
      exact hE.eq_consSet hP hjE
    exact ⟨E₀, hE₀, fun E hE => (hall E hE).trans (hall E₀ hE₀).symm⟩
  · obtain ⟨-, hPQ⟩ := limit_mul hP tendsto_id hQ
    have hrows : ∀ i, Q i = Q j := fun i => funext fun c =>
      harmonic_const hP (isClosedSet_univ hP) (fun i _ => column_harmonic hPQ c i)
        (fun i _ _ => hj i) i (mem_univ i)
    have hrQ : ∀ r : S → ℝ, r ∈ simplex S → r ᵥ* Q = Q j := fun r hr => by
      funext c
      simp only [vecMul, dotProduct]
      simp_rw [hrows]
      rw [← sum_mul, hr.2, one_mul]
    have hc := (theorem_11_1c hP hQ)
    refine ⟨hrows, fun r => ⟨fun hr => ?_, fun hr => ?_⟩, hrQ⟩
    · rw [← hc.2.2 r hr, hrQ r hr.1]
    · rw [hr]; exact hc.1 j

end StokeyLucasPrescott.StrongConvergence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Finite Markov chains: the block form of `Q`

SLP §11.1, Exercise 11.1, pp. 329–330. Let `G` (`recSet`) be the union of the ergodic sets; by
Theorem 11.1a its complement is the transient set `F`.

* `tendsto_tail`: the probability `Πⁿ(i, F)` of still being in `F` after `n` steps tends to `0`.
  Every state reaches `G` with positive probability within `n₀` steps, so `Πⁿ⁰(i, F) ≤ 1 − δ`
  for all `i`, and `G` is closed, so `Π^{kn₀}(i, F) ≤ (1 − δ)ᵏ`.
* **Exercise 11.1** (`ex_11_1`):
  * the columns of `Q` for transient states are zero;
  * the rows of `Q` for an ergodic set `E` vanish outside `E`, and are all equal;
  * the absorption probabilities `w_E(i) = lim Πⁿ(i, E)` exist and sum to one over the ergodic
    sets, and `Qᵢⱼ = Σ_E w_E(i) q_E(j)`, with `q_E` the common row of `Q` on `E`.

  The book writes the transient block as `w_j Q_j`, an outer product of the column `w_j` and the
  common row of `Q_j`.
-/

namespace StokeyLucasPrescott.StrongConvergence

open Matrix Finset Filter Topology

variable {S : Type*} [Fintype S] [DecidableEq S] {P : Matrix S S ℝ}

/-- The ergodic sets. -/
noncomputable def ergSets (P : Matrix S S ℝ) : Finset (Finset S) := by
  classical exact univ.filter (IsErgodic P)

/-- The recurrent states: the union `G` of the ergodic sets. -/
noncomputable def recSet (P : Matrix S S ℝ) : Finset S := (ergSets P).biUnion id

omit [DecidableEq S] in
theorem mem_ergSets {E : Finset S} : E ∈ ergSets P ↔ IsErgodic P E := by
  classical simp [ergSets]

theorem mem_recSet {i : S} : i ∈ recSet P ↔ ∃ E, IsErgodic P E ∧ i ∈ E := by
  simp [recSet, mem_ergSets]

theorem recSet_closed (hP : P ∈ rowStochastic ℝ S) : IsClosedSet P (recSet P) :=
  isClosedSet_of hP fun i hi j hj => by
    obtain ⟨E, hE, hiE⟩ := mem_recSet.1 hi
    exact mem_recSet.2 ⟨E, hE, hE.2.1.mem_of_pow_pos hP hiE 1 (by rwa [pow_one])⟩

theorem ergSets_pairwiseDisjoint (hP : P ∈ rowStochastic ℝ S) :
    (ergSets P : Set (Finset S)).PairwiseDisjoint id := by
  intro E hE E' hE' hne
  refine disjoint_left.2 fun i hi hi' => hne ?_
  exact ((mem_ergSets.1 hE).eq_consSet hP hi).trans ((mem_ergSets.1 hE').eq_consSet hP hi').symm

/-- The probability `Πⁿ(i, E)` of being in `E` after `n` steps. -/
def mass (P : Matrix S S ℝ) (n : ℕ) (i : S) (E : Finset S) : ℝ := ∑ k ∈ E, (P ^ n) i k

theorem mass_nonneg (hP : P ∈ rowStochastic ℝ S) (n : ℕ) (i : S) (E : Finset S) :
    0 ≤ mass P n i E :=
  sum_nonneg fun k _ => pow_nonneg' hP n i k

theorem mass_le_one (hP : P ∈ rowStochastic ℝ S) (n : ℕ) (i : S) (E : Finset S) :
    mass P n i E ≤ 1 := by
  rw [← pow_row_sum hP n i, mass]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ E) fun k _ _ => pow_nonneg' hP n i k

theorem mass_add_compl (hP : P ∈ rowStochastic ℝ S) (n : ℕ) (i : S) (E : Finset S) :
    mass P n i E + mass P n i Eᶜ = 1 := by
  rw [mass, mass, sum_add_sum_compl, pow_row_sum hP]

/-- `Πⁿ⁺ᵐ(i, A) = Σₗ Πⁿ(i, l) Πᵐ(l, A)`. -/
theorem mass_add (n m : ℕ) (i : S) (A : Finset S) :
    mass P (n + m) i A = ∑ l, (P ^ n) i l * mass P m l A := by
  simp only [mass, pow_add, mul_apply]
  rw [sum_comm]
  exact sum_congr rfl fun l _ => by rw [mul_sum]

/-- From a closed set, the mass outside it stays zero. -/
theorem mass_compl_eq_zero (hP : P ∈ rowStochastic ℝ S) {E : Finset S} (hE : IsClosedSet P E)
    {l : S} (hl : l ∈ E) (m : ℕ) : mass P m l Eᶜ = 0 :=
  sum_eq_zero fun k hk => le_antisymm (not_lt.1 fun hp => mem_compl.1 hk
    (hE.mem_of_pow_pos hP hl m hp)) (pow_nonneg' hP m l k)

/-- The mass in a closed set is nondecreasing in time. -/
theorem mass_mono (hP : P ∈ rowStochastic ℝ S) {E : Finset S} (hE : IsClosedSet P E) (i : S) :
    Monotone fun n => mass P n i E := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [mass_add]
  calc mass P n i E = ∑ l ∈ E, (P ^ n) i l * mass P 1 l E := by
        refine sum_congr rfl fun l hl => ?_
        have h0 := mass_compl_eq_zero hP hE hl 1
        have h1 := mass_add_compl hP 1 l E
        rw [show mass P 1 l E = 1 by linarith, mul_one]
    _ ≤ ∑ l, (P ^ n) i l * mass P 1 l E :=
        sum_le_sum_of_subset_of_nonneg (subset_univ E) fun l _ _ =>
          mul_nonneg (pow_nonneg' hP n i l) (mass_nonneg hP 1 l E)

/-- Every state reaches the recurrent states with positive probability. -/
theorem exists_mass_recSet_pos (hP : P ∈ rowStochastic ℝ S) (i : S) :
    ∃ n, 0 < mass P n i (recSet P) := by
  obtain ⟨E, hE, k, hk, n, -, hn⟩ := exists_ergodic_reach hP i
  refine ⟨n, lt_of_lt_of_le hn ?_⟩
  exact single_le_sum (f := fun k => (P ^ n) i k) (fun k _ => pow_nonneg' hP n i k)
    (mem_recSet.2 ⟨E, hE, hk⟩)

/-- The probability of still being transient after `n` steps tends to zero. -/
theorem tendsto_tail [Nonempty S] (hP : P ∈ rowStochastic ℝ S) (i : S) :
    Tendsto (fun n => mass P n i (recSet P)ᶜ) atTop (𝓝 0) := by
  set G := recSet P
  have hG := recSet_closed (P := P) hP
  choose nn hnn using exists_mass_recSet_pos hP
  set n₀ := univ.sup nn + 1
  have hmono : ∀ l, mass P (nn l) l G ≤ mass P n₀ l G := fun l =>
    mass_mono hP hG l ((le_sup (f := nn) (mem_univ l)).trans (Nat.le_succ _))
  obtain ⟨l₀, -, hl₀⟩ := exists_min_image univ (fun l => mass P n₀ l G) univ_nonempty
  set δ := mass P n₀ l₀ G
  have hδ : 0 < δ := lt_of_lt_of_le (hnn l₀) (hmono l₀)
  have hδ1 : δ ≤ 1 := mass_le_one hP n₀ l₀ G
  -- one block of `n₀` steps multiplies the transient mass by at most `1 − δ`
  have hstep : ∀ m l, mass P (m * n₀ + n₀) l Gᶜ ≤ (1 - δ) * mass P (m * n₀) l Gᶜ := by
    intro m l
    rw [mass_add, mass, mul_sum]
    rw [← sum_add_sum_compl G]
    have h1 : ∑ k ∈ G, (P ^ (m * n₀)) l k * mass P n₀ k Gᶜ = 0 :=
      sum_eq_zero fun k hk => by rw [mass_compl_eq_zero hP hG hk, mul_zero]
    rw [h1, zero_add]
    refine sum_le_sum fun k _ => ?_
    have h2 := mass_add_compl hP n₀ k G
    have h3 := hl₀ k (mem_univ k)
    have h4 := pow_nonneg' hP (m * n₀) l k
    nlinarith
  have hgeo : ∀ m l, mass P (m * n₀) l Gᶜ ≤ (1 - δ) ^ m := by
    intro m
    induction m with
    | zero => intro l; simpa using mass_le_one hP 0 l Gᶜ
    | succ m ih =>
      intro l
      rw [Nat.succ_mul, pow_succ]
      calc mass P (m * n₀ + n₀) l Gᶜ ≤ (1 - δ) * mass P (m * n₀) l Gᶜ := hstep m l
        _ ≤ (1 - δ) * (1 - δ) ^ m := mul_le_mul_of_nonneg_left (ih l) (by linarith)
        _ = (1 - δ) ^ m * (1 - δ) := mul_comm _ _
  have hanti : Antitone fun n => mass P n i Gᶜ := fun a b hab => by
    have := mass_mono hP hG i hab
    have h1 := mass_add_compl hP a i G
    have h2 := mass_add_compl hP b i G
    dsimp only; linarith
  have hn₀ : 0 < n₀ := Nat.succ_pos _
  refine squeeze_zero (fun n => mass_nonneg hP n i Gᶜ) (fun n => ?_)
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (r := 1 - δ) (by linarith) (by linarith)).comp
      (Nat.tendsto_div_const_atTop hn₀.ne'))
  dsimp only [Function.comp_apply]
  exact (hanti (Nat.div_mul_le_self n n₀)).trans (hgeo (n / n₀) i)

theorem cesaro_apply (n : ℕ) (i j : S) :
    cesaro P n i j = (n : ℝ)⁻¹ * ∑ k ∈ range n, (P ^ k) i j := by
  simp [cesaro, Matrix.smul_apply, Matrix.sum_apply]

/-- If `Πᵏᵢⱼ → a` then `Qᵢⱼ = a`. -/
theorem Q_apply_of_tendsto {Q : Matrix S S ℝ} (hQ : Tendsto (cesaro P) atTop (𝓝 Q)) {i j : S}
    {a : ℝ} (h : Tendsto (fun k => (P ^ k) i j) atTop (𝓝 a)) : Q i j = a := by
  have h1 := tendsto_matrix_iff.1 hQ i j
  simp_rw [cesaro_apply] at h1
  exact tendsto_nhds_unique h1 h.cesaro

theorem not_mem_recSet_iff [Nonempty S] (hP : P ∈ rowStochastic ℝ S) {j : S} :
    j ∉ recSet P ↔ IsTransient P j := by
  rw [(theorem_11_1a hP).2.2.2.2 j, mem_recSet]
  simp only [not_exists, not_and]

/-- **Exercise 11.1.** The limit `Q` of the averages has the block form of p. 330: the columns
for transient states vanish; the rows for an ergodic set `E` vanish outside `E` and are all
equal; and with the absorption probabilities `w_E(i) = lim Πⁿ(i, E)`, which sum to one over the
ergodic sets, `Qᵢⱼ = Σ_E w_E(i) q_E(j)`, where `q_E = Q_{σ(E)}` is the common row on `E`. -/
theorem ex_11_1 [Nonempty S] (hP : P ∈ rowStochastic ℝ S) {Q : Matrix S S ℝ}
    (hQ : Tendsto (cesaro P) atTop (𝓝 Q)) :
    (∀ i j, IsTransient P j → Q i j = 0) ∧
      (∀ E, IsErgodic P E → ∀ i ∈ E, ∀ j ∉ E, Q i j = 0) ∧
      (∀ E, IsErgodic P E → ∀ i ∈ E, ∀ i' ∈ E, Q i = Q i') ∧
      ∀ i, ∃ w : Finset S → ℝ,
        (∀ E, IsErgodic P E → Tendsto (fun n => mass P n i E) atTop (𝓝 (w E))) ∧
          ∑ E ∈ ergSets P, w E = 1 ∧
          ∀ σ : Finset S → S, (∀ E, IsErgodic P E → σ E ∈ E) →
            ∀ j, Q i j = ∑ E ∈ ergSets P, w E * Q (σ E) j := by
  obtain ⟨-, hPQ⟩ := limit_mul hP tendsto_id hQ
  have hQs : Q ∈ rowStochastic ℝ S :=
    isClosed_rowStochastic.mem_of_tendsto hQ
      (eventually_atTop.2 ⟨1, fun n hn => cesaro_mem hP hn⟩)
  -- rows within an ergodic set
  have hrows : ∀ E, IsErgodic P E → ∀ i ∈ E, ∀ i' ∈ E, Q i = Q i' := by
    intro E hE i hi i' hi'
    funext c
    exact harmonic_const hP hE.2.1 (fun k _ => column_harmonic hPQ c k)
      (fun k hk _ => mem_consSet.1 (hE.eq_consSet hP hk ▸ hi')) i hi
  refine ⟨fun i j hj => ?_, fun E hE i hi j hj => ?_, hrows, fun i => ?_⟩
  · -- transient columns
    apply Q_apply_of_tendsto hQ
    have hj' := (not_mem_recSet_iff hP).2 hj
    refine squeeze_zero (fun k => pow_nonneg' hP k i j) (fun k => ?_) (tendsto_tail hP i)
    exact single_le_sum (f := fun l => (P ^ k) i l) (fun l _ => pow_nonneg' hP k i l)
      (mem_compl.2 hj')
  · -- rows of an ergodic set vanish outside it
    apply Q_apply_of_tendsto hQ
    refine tendsto_const_nhds.congr fun k => ?_
    exact (le_antisymm (not_lt.1 fun hp => hj (hE.2.1.mem_of_pow_pos hP hi k hp))
      (pow_nonneg' hP k i j)).symm
  · -- absorption probabilities
    have hconv : ∀ E, IsErgodic P E →
        Tendsto (fun n => mass P n i E) atTop (𝓝 (⨆ n, mass P n i E)) := fun E hE =>
      tendsto_atTop_ciSup (mass_mono hP hE.2.1 i) ⟨1, by
        rintro _ ⟨n, rfl⟩; exact mass_le_one hP n i E⟩
    set w : Finset S → ℝ := fun E => ⨆ n, mass P n i E
    have hsumE : ∀ n, ∑ E ∈ ergSets P, mass P n i E = mass P n i (recSet P) := fun n => by
      rw [recSet, mass, sum_biUnion (ergSets_pairwiseDisjoint hP)]
      rfl
    have hwlim : Tendsto (fun n => ∑ E ∈ ergSets P, mass P n i E) atTop
        (𝓝 (∑ E ∈ ergSets P, w E)) :=
      tendsto_finsetSum _ fun E hE => hconv E (mem_ergSets.1 hE)
    have hone : Tendsto (fun n => mass P n i (recSet P)) atTop (𝓝 1) := by
      have := (tendsto_tail hP i).const_sub 1
      rw [sub_zero] at this
      refine this.congr fun n => ?_
      have := mass_add_compl hP n i (recSet P)
      linarith
    simp_rw [hsumE] at hwlim
    refine ⟨w, hconv, tendsto_nhds_unique hwlim hone, fun σ hσ j => ?_⟩
    -- `Qᵢⱼ = Σₖ Πⁿᵢₖ Qₖⱼ`, split into the ergodic sets and the transient set
    have hsplit : ∀ n, Q i j = ∑ E ∈ ergSets P, mass P n i E * Q (σ E) j +
        ∑ k ∈ (recSet P)ᶜ, (P ^ n) i k * Q k j := fun n => by
      have e := congrFun (congrFun (pow_mul_eq hPQ n) i) j
      rw [mul_apply] at e
      rw [← e, ← sum_add_sum_compl (recSet P), recSet, sum_biUnion (ergSets_pairwiseDisjoint hP)]
      congr 1
      refine sum_congr rfl fun E hE => ?_
      rw [mass, sum_mul]
      refine sum_congr rfl fun k hk => ?_
      rw [hrows E (mem_ergSets.1 hE) k hk (σ E) (hσ E (mem_ergSets.1 hE))]
    have hrest : Tendsto (fun n => ∑ k ∈ (recSet P)ᶜ, (P ^ n) i k * Q k j) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => ?_) (tendsto_tail hP i)
      rw [Real.norm_eq_abs, mass]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
      rw [abs_mul, abs_of_nonneg (pow_nonneg' hP n i k),
        abs_of_nonneg (nonneg_of_mem_rowStochastic hQs)]
      exact mul_le_of_le_one_right (pow_nonneg' hP n i k) (le_one_of_mem_rowStochastic hQs)
    have hlim : Tendsto (fun n => ∑ E ∈ ergSets P, mass P n i E * Q (σ E) j +
        ∑ k ∈ (recSet P)ᶜ, (P ^ n) i k * Q k j) atTop
        (𝓝 (∑ E ∈ ergSets P, w E * Q (σ E) j + 0)) :=
      (tendsto_finsetSum _ fun E hE => (hconv E (mem_ergSets.1 hE)).mul_const _).add hrest
    rw [add_zero] at hlim
    exact tendsto_nhds_unique (tendsto_const_nhds.congr hsplit) hlim

end StokeyLucasPrescott.StrongConvergence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Sets of natural numbers closed under addition

A set `R ⊆ ℕ` closed under addition, containing a positive element, whose elements have no
common divisor other than `1`, contains every sufficiently large integer
(`eventually_mem_of_add_closed`). This is the number theory behind aperiodicity in Theorem
11.4: the return times of a state form such a set.

The proof: call `d > 0` *big* if `R` contains all large multiples of `d`. Each positive `r ∈ R`
is big. If `d` is big and `r ∈ R`, then `gcd(d, r)` is big, by the Chicken McNugget theorem
(`frobeniusNumber_pair`) applied to `d/g` and `r/g`. So the least big `d` divides every element
of `R`, and is `1`.
-/

namespace StokeyLucasPrescott.StrongConvergence

/-- Coprime `a, b ≥ 1`: every `s ≥ ab` is `xa + yb` with `x, y ∈ ℕ`. -/
theorem exists_nonneg_comb {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b) {s : ℕ}
    (hs : a * b ≤ s) : ∃ x y : ℕ, x * a + y * b = s := by
  rcases Nat.lt_or_ge 1 a with ha1 | ha1
  · rcases Nat.lt_or_ge 1 b with hb1 | hb1
    · have hab1 : 1 ≤ a * b := Nat.mul_pos ha hb
      have hF := (frobeniusNumber_iff.1 (frobeniusNumber_pair hab ha1 hb1)).2 s (by omega)
      obtain ⟨x, y, h⟩ := (AddSubmonoid.mem_closure_pair a b s).1 hF
      exact ⟨x, y, by simpa [smul_eq_mul] using h⟩
    · exact ⟨0, s, by rw [show b = 1 by omega]; ring⟩
  · exact ⟨s, 0, by rw [show a = 1 by omega]; ring⟩

/-- `d > 0` is **big** for `R` if `R` contains all large multiples of `d`. -/
def BigFor (R : Set ℕ) (d : ℕ) : Prop := 0 < d ∧ ∃ n₀, ∀ n ≥ n₀, n * d ∈ R

theorem nsmul_mem {R : Set ℕ} (hadd : ∀ a ∈ R, ∀ b ∈ R, a + b ∈ R) {r : ℕ} (hr : r ∈ R) :
    ∀ n, 1 ≤ n → n * r ∈ R := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simpa using hr
    · rw [Nat.succ_mul]; exact hadd _ (ih hpos) _ hr

theorem bigFor_gcd {R : Set ℕ} (hadd : ∀ a ∈ R, ∀ b ∈ R, a + b ∈ R) {d r : ℕ}
    (hd : BigFor R d) (hr : r ∈ R) (hr0 : 0 < r) : BigFor R (Nat.gcd d r) := by
  obtain ⟨hd0, n₀, hn₀⟩ := hd
  set g := Nat.gcd d r
  have hg : 0 < g := Nat.gcd_pos_of_pos_left r hd0
  set d' := d / g
  set r' := r / g
  have hd' : d = d' * g := (Nat.div_mul_cancel (Nat.gcd_dvd_left d r)).symm
  have hr' : r = r' * g := (Nat.div_mul_cancel (Nat.gcd_dvd_right d r)).symm
  have hd'0 : 0 < d' := Nat.div_pos (Nat.gcd_le_left r hd0) hg
  have hr'0 : 0 < r' := Nat.div_pos (Nat.gcd_le_right (m := d) hr0) hg
  have hcop : Nat.Coprime d' r' := Nat.coprime_div_gcd_div_gcd hg
  refine ⟨hg, (n₀ + 1) * d' + d' * r', fun t ht => ?_⟩
  obtain ⟨x, y, hxy⟩ := exists_nonneg_comb hcop hd'0 hr'0
    (s := t - (n₀ + 1) * d') (by omega)
  have ht' : t * g = (n₀ + 1 + x) * d + y * r := by
    have : t = (n₀ + 1 + x) * d' + y * r' := by
      have := Nat.sub_add_cancel (show (n₀ + 1) * d' ≤ t by omega)
      rw [← this, ← hxy]; ring
    rw [this, hd', hr']; ring
  rw [ht']
  have h1 : (n₀ + 1 + x) * d ∈ R := hn₀ _ (by omega)
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simpa using h1
  · exact hadd _ h1 _ (nsmul_mem hadd hr y hy)

/-- A set of naturals closed under addition, with a positive element and no common divisor
other than `1`, contains all sufficiently large naturals. -/
theorem eventually_mem_of_add_closed {R : Set ℕ} (hadd : ∀ a ∈ R, ∀ b ∈ R, a + b ∈ R)
    (hne : ∃ a ∈ R, 0 < a) (hgcd : ∀ d, (∀ n ∈ R, d ∣ n) → d = 1) :
    ∃ n₀, ∀ n ≥ n₀, n ∈ R := by
  classical
  obtain ⟨a, ha, ha0⟩ := hne
  have hex : ∃ d, BigFor R d := ⟨a, ha0, 1, fun n hn => nsmul_mem hadd ha n hn⟩
  set d₀ := Nat.find hex
  have hd₀ : BigFor R d₀ := Nat.find_spec hex
  have hdvd : ∀ n ∈ R, d₀ ∣ n := by
    intro r hr
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · exact dvd_zero _
    · have hb := bigFor_gcd hadd hd₀ hr hr0
      have hle : d₀ ≤ Nat.gcd d₀ r := Nat.find_min' hex hb
      have hge : Nat.gcd d₀ r ≤ d₀ := Nat.gcd_le_left r hd₀.1
      have : Nat.gcd d₀ r = d₀ := le_antisymm hge hle
      rw [← this]; exact Nat.gcd_dvd_right d₀ r
  have h1 := hgcd d₀ hdvd
  obtain ⟨-, n₀, hn₀⟩ := hd₀
  refine ⟨n₀, fun n hn => ?_⟩
  have := hn₀ n hn
  rwa [h1, mul_one] at this

end StokeyLucasPrescott.StrongConvergence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Finite Markov chains: convergence of `p₀Πⁿ`

SLP §11.1, Lemma 11.3 and Theorem 11.4, pp. 331–333. With `‖x‖_Δ = Σⱼ |xⱼ|` (`l1`), let
`εⱼ = minᵢ πᵢⱼ` and `ε = Σⱼ εⱼ` (`epsSum`).

* **Lemma 11.3** (`lemma_11_3`): `‖pΠ − qΠ‖_Δ ≤ (1 − ε)‖p − q‖_Δ` whenever `Σ p = Σ q`; in
  particular `p ↦ pΠ` is a contraction of modulus `1 − ε` on `Δ`.
* **Theorem 11.4** (`theorem_11_4`). The book states: `S` has a unique ergodic set with no
  cyclically moving subsets iff `ε⁽ᴺ⁾ > 0` for some `N ≥ 1`; then `p₀Πⁿ → p*` geometrically,
  uniformly in `p₀`. The book never defines cyclically moving subsets, and its proof of the
  converse assumes convergence rather than the stated hypothesis. Here `HasCyclicSubsets`
  defines them (a split of an ergodic set into `d ≥ 2` nonempty sets visited in turn, as in
  Example 3), and three conditions are proved equivalent:
  1. `ε⁽ᴺ⁾ > 0` for some `N ≥ 1`;
  2. there is a unique ergodic set, and it has no cyclically moving subsets;
  3. `p₀Πⁿ` converges, to the same limit for every `p₀ ∈ Δ`.

  Under them the invariant distribution `p*` is unique and
  `‖p₀Πⁿ − p*‖_Δ ≤ 2(1 − ε⁽ᴺ⁾)^⌊n/N⌋` (`theorem_11_4_rate`). That (2) implies (1) uses
  aperiodicity: the return times of a state of the ergodic set have greatest common divisor
  `d`. If `d ≥ 2`, the residues mod `d` of the times at which states are reached split the set
  into cyclically moving subsets. If `d = 1`, the return times include all large integers
  (`eventually_mem_of_add_closed`).
-/

namespace StokeyLucasPrescott.StrongConvergence

open Matrix Finset Filter Topology

variable {S : Type*} [Fintype S] [DecidableEq S] {P : Matrix S S ℝ}

/-- The norm `‖x‖_Δ = Σⱼ |xⱼ|`. -/
def l1 (x : S → ℝ) : ℝ := ∑ j, |x j|

/-- `εⱼ = minᵢ πᵢⱼ`. -/
noncomputable def epsMin [Nonempty S] (P : Matrix S S ℝ) (j : S) : ℝ :=
  univ.inf' univ_nonempty fun i => P i j

/-- `ε = Σⱼ minᵢ πᵢⱼ`. -/
noncomputable def epsSum [Nonempty S] (P : Matrix S S ℝ) : ℝ := ∑ j, epsMin P j

omit [DecidableEq S] in
theorem epsMin_le [Nonempty S] (i j : S) : epsMin P j ≤ P i j :=
  inf'_le _ (mem_univ i)

theorem epsSum_nonneg [Nonempty S] (hP : P ∈ rowStochastic ℝ S) : 0 ≤ epsSum P :=
  sum_nonneg fun _ _ => (le_inf'_iff _ _).2 fun _ _ => nonneg_of_mem_rowStochastic hP

theorem epsSum_le_one [Nonempty S] (hP : P ∈ rowStochastic ℝ S) : epsSum P ≤ 1 := by
  obtain ⟨i⟩ := ‹Nonempty S›
  rw [← sum_row_of_mem_rowStochastic hP i]
  exact sum_le_sum fun j _ => epsMin_le i j

/-- **Lemma 11.3.** If `Σ p = Σ q`, then `‖pΠ − qΠ‖_Δ ≤ (1 − ε)‖p − q‖_Δ`. -/
theorem lemma_11_3 [Nonempty S] (hP : P ∈ rowStochastic ℝ S) {p q : S → ℝ}
    (hpq : ∑ i, p i = ∑ i, q i) : l1 (p ᵥ* P - q ᵥ* P) ≤ (1 - epsSum P) * l1 (p - q) := by
  set d := p - q
  have hd : ∑ i, d i = 0 := by simp [d, sum_sub_distrib, hpq]
  have hcol : ∀ j, (p ᵥ* P - q ᵥ* P) j = ∑ i, d i * (P i j - epsMin P j) := fun j => by
    have e1 : ∑ i, d i * (P i j - epsMin P j) = ∑ i, d i * P i j - (∑ i, d i) * epsMin P j := by
      rw [sum_mul, ← sum_sub_distrib]; exact sum_congr rfl fun i _ => by ring
    rw [e1, hd, zero_mul, sub_zero]
    simp only [Pi.sub_apply, vecMul, dotProduct, d, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  calc l1 (p ᵥ* P - q ᵥ* P) = ∑ j, |∑ i, d i * (P i j - epsMin P j)| := by
        simp only [l1, hcol]
    _ ≤ ∑ j, ∑ i, |d i| * (P i j - epsMin P j) := sum_le_sum fun j _ =>
        (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun i _ => by
          rw [abs_mul, abs_of_nonneg (sub_nonneg.2 (epsMin_le i j))]))
    _ = ∑ i, |d i| * (1 - epsSum P) := by
        rw [sum_comm]
        refine sum_congr rfl fun i _ => ?_
        rw [← mul_sum, sum_sub_distrib, sum_row_of_mem_rowStochastic hP]
        rfl
    _ = (1 - epsSum P) * l1 (p - q) := by rw [l1, ← sum_mul, mul_comm]

omit [DecidableEq S] in
theorem l1_sub_le_two {p q : S → ℝ} (hp : p ∈ simplex S) (hq : q ∈ simplex S) :
    l1 (p - q) ≤ 2 := by
  calc l1 (p - q) ≤ ∑ j, (p j + q j) := sum_le_sum fun j _ => by
        rw [Pi.sub_apply, abs_le]; constructor <;> linarith [hp.1 j, hq.1 j]
    _ = 2 := by rw [sum_add_distrib, hp.2, hq.2]; norm_num

/-- Iterating Lemma 11.3. -/
theorem l1_pow_le [Nonempty S] (hP : P ∈ rowStochastic ℝ S) {p q : S → ℝ} (hp : p ∈ simplex S)
    (hq : q ∈ simplex S) (k : ℕ) :
    l1 (p ᵥ* P ^ k - q ᵥ* P ^ k) ≤ (1 - epsSum P) ^ k * l1 (p - q) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpk := simplex_vecMul (pow_mem_rowStochastic hP k) hp
    have hqk := simplex_vecMul (pow_mem_rowStochastic hP k) hq
    rw [pow_succ, ← vecMul_vecMul, ← vecMul_vecMul, pow_succ, mul_comm _ (1 - epsSum P),
      mul_assoc]
    exact (lemma_11_3 hP (hpk.2.trans hqk.2.symm)).trans
      (mul_le_mul_of_nonneg_left ih (sub_nonneg.2 (epsSum_le_one hP)))

omit [DecidableEq S] in
theorem isClosed_simplex : IsClosed (simplex S) := by
  have : simplex S = (⋂ i, {p : S → ℝ | 0 ≤ p i}) ∩ {p | ∑ i, p i = 1} := by
    ext p; simp [simplex]
  rw [this]
  exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)

omit [DecidableEq S] in
theorem abs_le_l1 (x : S → ℝ) (j : S) : |x j| ≤ l1 x :=
  single_le_sum (f := fun j => |x j|) (fun _ _ => abs_nonneg _) (mem_univ j)

omit [DecidableEq S] in
theorem eq_of_l1_le {x y : S → ℝ} (h : l1 (x - y) ≤ 0) : x = y := by
  funext j
  have := (abs_le_l1 (x - y) j).trans h
  rw [Pi.sub_apply] at this
  linarith [abs_nonneg (x j - y j), abs_sub_lt_iff.1 (lt_of_le_of_lt this zero_lt_one),
    abs_nonpos_iff.1 this]

/-- Positive transitions from `i` into `A` exhaust row `i` when `A` captures all of them. -/
theorem sum_eq_one_of_pos_mem (hP : P ∈ rowStochastic ℝ S) {i : S} {A : Finset S}
    (h : ∀ l, 0 < P i l → l ∈ A) : ∑ l ∈ A, P i l = 1 := by
  have hsum := sum_row_of_mem_rowStochastic hP i
  rw [← sum_add_sum_compl A] at hsum
  have h0 : ∑ k ∈ Aᶜ, P i k = 0 := sum_eq_zero fun k hk =>
    le_antisymm (not_lt.1 fun hp => mem_compl.1 hk (h k hp)) (nonneg_of_mem_rowStochastic hP)
  linarith

theorem apply_eq_zero_of_sum_eq_one (hP : P ∈ rowStochastic ℝ S) {i l : S} {A : Finset S}
    (h : ∑ k ∈ A, P i k = 1) (hl : l ∉ A) : P i l = 0 := by
  have hsum := sum_row_of_mem_rowStochastic hP i
  rw [← sum_add_sum_compl A, h] at hsum
  have h0 : ∑ k ∈ Aᶜ, P i k = 0 := by linarith
  exact (sum_eq_zero_iff_of_nonneg fun k _ => nonneg_of_mem_rowStochastic hP).1 h0 l
    (mem_compl.2 hl)

/-- An ergodic set `E` has **cyclically moving subsets** (p. 323) if it splits into `d ≥ 2`
nonempty disjoint sets `C₀, …, C_{d−1}` (indexed periodically, `C_{k+d} = C_k`) such that from
`C_k` the chain moves to `C_{k+1}` with probability one. -/
def HasCyclicSubsets (P : Matrix S S ℝ) (E : Finset S) : Prop :=
  ∃ d, 2 ≤ d ∧ ∃ C : ℕ → Finset S, (∀ k, C (k + d) = C k) ∧ (∀ k, (C k).Nonempty) ∧
    (∀ k k', k < d → k' < d → k ≠ k' → Disjoint (C k) (C k')) ∧ (∀ k, C k ⊆ E) ∧
    (∀ i ∈ E, ∃ k, i ∈ C k) ∧ ∀ k, ∀ i ∈ C k, ∑ l ∈ C (k + 1), P i l = 1

omit [Fintype S] [DecidableEq S] in
theorem periodic_mod {d : ℕ} {C : ℕ → Finset S} (hC : ∀ k, C (k + d) = C k) (k : ℕ) :
    C k = C (k % d) := by
  conv_lhs => rw [← Nat.mod_add_div k d]
  induction k / d with
  | zero => simp
  | succ m ih => rw [Nat.mul_succ, ← add_assoc, hC, ih]

/-- Along cyclically moving subsets, `n` steps from `C_k` land in `C_{k+n}`. -/
theorem cyclic_pow (hP : P ∈ rowStochastic ℝ S) {C : ℕ → Finset S}
    (hstep : ∀ k, ∀ i ∈ C k, ∑ l ∈ C (k + 1), P i l = 1) :
    ∀ n k, ∀ i ∈ C k, ∀ l, 0 < (P ^ n) i l → l ∈ C (k + n) := by
  intro n
  induction n with
  | zero =>
    intro k i hi l hl
    rw [pow_zero, one_apply] at hl
    split_ifs at hl with h
    · exact h ▸ hi
    · exact absurd hl (lt_irrefl 0)
  | succ n ih =>
    intro k i hi l hl
    rw [pow_succ, mul_apply] at hl
    obtain ⟨m, hm⟩ := exists_pos_of_sum_pos hl
    have hm1 : 0 < (P ^ n) i m := lt_of_le_of_ne (pow_nonneg' hP n i m) fun h => by
      rw [← h, zero_mul] at hm; exact lt_irrefl 0 hm
    have hm2 : 0 < P m l := lt_of_le_of_ne (nonneg_of_mem_rowStochastic hP) fun h => by
      rw [← h, mul_zero] at hm; exact lt_irrefl 0 hm
    have hmC := ih k i hi m hm1
    by_contra hlC
    rw [← add_assoc] at hlC
    exact (apply_eq_zero_of_sum_eq_one hP (hstep _ m hmC) hlC ▸ hm2).false

/-- If `ε⁽ᴺ⁾ > 0`, some column of `Πᴺ` is positive. -/
theorem exists_pos_column [Nonempty S] {N : ℕ} (h : 0 < epsSum (P ^ N)) :
    ∃ j, ∀ i, 0 < (P ^ N) i j := by
  obtain ⟨j, hj⟩ := exists_pos_of_sum_pos h
  exact ⟨j, fun i => lt_of_lt_of_le hj (epsMin_le i j)⟩

/-- A positive column of `Πᴺ` gives `ε⁽ᴺ⁾ > 0`. -/
theorem epsSum_pos_of_column [Nonempty S] (hP : P ∈ rowStochastic ℝ S) {N : ℕ} {j : S}
    (h : ∀ i, 0 < (P ^ N) i j) : 0 < epsSum (P ^ N) := by
  have hj : 0 < epsMin (P ^ N) j := (lt_inf'_iff _).2 fun i _ => h i
  have hnn : ∀ k ∈ univ, 0 ≤ epsMin (P ^ N) k := fun k _ =>
    (le_inf'_iff _ _).2 fun i _ => pow_nonneg' hP N i k
  exact lt_of_lt_of_le hj (single_le_sum hnn (mem_univ j))

/-- **Theorem 11.4** (the rate). If `ε⁽ᴺ⁾ > 0`, there is a unique invariant distribution `p*`
and `‖p₀Πⁿ − p*‖_Δ ≤ 2(1 − ε⁽ᴺ⁾)^⌊n/N⌋` for every `p₀ ∈ Δ`. -/
theorem theorem_11_4_rate [Nonempty S] (hP : P ∈ rowStochastic ℝ S) {N : ℕ} (hN : 1 ≤ N)
    (hε : 0 < epsSum (P ^ N)) :
    ∃ p, IsInvariantDist P p ∧ (∀ r, IsInvariantDist P r → r = p) ∧
      ∀ p₀ ∈ simplex S, ∀ n, l1 (p₀ ᵥ* P ^ n - p) ≤ 2 * (1 - epsSum (P ^ N)) ^ (n / N) := by
  obtain ⟨Q, -, hQ, -⟩ := theorem_11_1b hP
  obtain ⟨i₀⟩ := ‹Nonempty S›
  set p := Q i₀
  have hp : IsInvariantDist P p := (theorem_11_1c hP hQ).1 i₀
  have hPN := pow_mem_rowStochastic hP N
  have hfix : ∀ {r}, IsInvariantDist P r → ∀ m, r ᵥ* P ^ m = r := fun {r} hr m => by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, ← vecMul_vecMul, ih, hr.2]
  have hrate : ∀ p₀ ∈ simplex S, ∀ n,
      l1 (p₀ ᵥ* P ^ n - p) ≤ 2 * (1 - epsSum (P ^ N)) ^ (n / N) := by
    intro p₀ hp₀ n
    have hsplit : P ^ n = P ^ (n % N) * (P ^ N) ^ (n / N) := by
      rw [← pow_mul, ← pow_add, Nat.mod_add_div]
    have hq := simplex_vecMul (pow_mem_rowStochastic hP (n % N)) hp₀
    have hpk : p = p ᵥ* (P ^ N) ^ (n / N) := by rw [← pow_mul, hfix hp]
    rw [hsplit, ← vecMul_vecMul]
    conv_lhs => rw [hpk]
    calc _ ≤ (1 - epsSum (P ^ N)) ^ (n / N) * l1 (p₀ ᵥ* P ^ (n % N) - p) :=
          l1_pow_le hPN hq hp.1 _
      _ ≤ (1 - epsSum (P ^ N)) ^ (n / N) * 2 :=
          mul_le_mul_of_nonneg_left (l1_sub_le_two hq hp.1)
            (pow_nonneg (sub_nonneg.2 (epsSum_le_one hPN)) _)
      _ = _ := mul_comm _ _
  refine ⟨p, hp, fun r hr => eq_of_l1_le ?_, hrate⟩
  have hlim : Tendsto (fun n => 2 * (1 - epsSum (P ^ N)) ^ (n / N)) atTop (𝓝 (2 * 0)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.2 (epsSum_le_one hPN))
      (by linarith)).comp (Nat.tendsto_div_const_atTop (by omega))).const_mul 2
  rw [mul_zero] at hlim
  refine ge_of_tendsto hlim (Eventually.of_forall fun n => ?_)
  have := hrate r hr.1 n
  rwa [hfix hr] at this

omit [DecidableEq S] in
theorem tendsto_of_l1 {u : ℕ → S → ℝ} {p : S → ℝ}
    (h : Tendsto (fun n => l1 (u n - p)) atTop (𝓝 0)) : Tendsto u atTop (𝓝 p) := by
  refine tendsto_pi_nhds.2 fun j => ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm (fun n => ?_) h
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
  exact abs_le_l1 (u n - p) j

/-- (1) ⇒ (3): `ε⁽ᴺ⁾ > 0` gives convergence of `p₀Πⁿ` to the same limit for all `p₀ ∈ Δ`. -/
theorem conv_of_eps [Nonempty S] (hP : P ∈ rowStochastic ℝ S) {N : ℕ} (hN : 1 ≤ N)
    (hε : 0 < epsSum (P ^ N)) :
    ∃ p, ∀ p₀ ∈ simplex S, Tendsto (fun n => p₀ ᵥ* P ^ n) atTop (𝓝 p) := by
  obtain ⟨p, -, -, hrate⟩ := theorem_11_4_rate hP hN hε
  have hPN := pow_mem_rowStochastic hP N
  refine ⟨p, fun p₀ hp₀ => tendsto_of_l1 ?_⟩
  have hlim : Tendsto (fun n => 2 * (1 - epsSum (P ^ N)) ^ (n / N)) atTop (𝓝 (2 * 0)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.2 (epsSum_le_one hPN))
      (by linarith)).comp (Nat.tendsto_div_const_atTop (by omega))).const_mul 2
  rw [mul_zero] at hlim
  refine squeeze_zero (fun n => sum_nonneg fun j _ => abs_nonneg _) (fun n => ?_) hlim
  exact hrate p₀ hp₀ n

/-- (3) ⇒ (1): the book's converse. -/
theorem eps_of_conv [Nonempty S] (hP : P ∈ rowStochastic ℝ S) {p : S → ℝ}
    (h : ∀ p₀ ∈ simplex S, Tendsto (fun n => p₀ ᵥ* P ^ n) atTop (𝓝 p)) :
    ∃ N, 1 ≤ N ∧ 0 < epsSum (P ^ N) := by
  obtain ⟨i₀⟩ := ‹Nonempty S›
  have he : ∀ i, (Pi.single i 1 : S → ℝ) ∈ simplex S := fun i =>
    ⟨fun k => by by_cases h : k = i <;> simp [h], by simp⟩
  have hps : p ∈ simplex S := isClosed_simplex.mem_of_tendsto (h _ (he i₀))
    (Eventually.of_forall fun n => simplex_vecMul (pow_mem_rowStochastic hP n) (he i₀))
  obtain ⟨j, hj⟩ := exists_pos_of_sum_pos (hps.2 ▸ one_pos : 0 < ∑ i, p i)
  have hev : ∀ᶠ n in atTop, ∀ i, 0 < (P ^ n) i j := by
    rw [eventually_all]
    intro i
    have := (tendsto_pi_nhds.1 (h _ (he i))) j
    simp only [single_one_vecMul] at this
    exact this.eventually (lt_mem_nhds hj)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  exact ⟨N + 1, by omega, epsSum_pos_of_column hP (hN (N + 1) (by omega))⟩

/-- (1) ⇒ (2): a positive column of `Πᴺ` gives a unique ergodic set, without cyclically moving
subsets. -/
theorem uniqueErgodic_of_eps [Nonempty S] (hP : P ∈ rowStochastic ℝ S) {N : ℕ} (hN : 1 ≤ N)
    (hε : 0 < epsSum (P ^ N)) :
    ∃ E, (IsErgodic P E ∧ ∀ E', IsErgodic P E' → E' = E) ∧ ¬ HasCyclicSubsets P E := by
  obtain ⟨j, hj⟩ := exists_pos_column hε
  have hcons : ∀ i, Cons P i j := fun i => ⟨N, hN, hj i⟩
  obtain ⟨E, hE, huniq⟩ := (theorem_11_2 hP).1.2 ⟨j, hcons⟩
  refine ⟨E, ⟨hE, huniq⟩, ?_⟩
  rintro ⟨d, hd, C, hper, hne, hdisj, -, -, hstep⟩
  obtain ⟨i₀, hi₀⟩ := hne 0
  obtain ⟨i₁, hi₁⟩ := hne 1
  have h0 : j ∈ C (0 + N) := cyclic_pow hP hstep N 0 i₀ hi₀ j (hj i₀)
  have h1 : j ∈ C (1 + N) := cyclic_pow hP hstep N 1 i₁ hi₁ j (hj i₁)
  rw [periodic_mod hper] at h0 h1
  have hne' : (0 + N) % d ≠ (1 + N) % d := by
    intro heq
    have h' : 0 + N ≡ 1 + N [MOD d] := heq
    have := Nat.ModEq.add_right_cancel' N h'
    have hd1 := (Nat.modEq_iff_dvd' (Nat.zero_le 1)).1 this
    have := Nat.le_of_dvd one_pos hd1
    omega
  exact disjoint_left.1 (hdisj _ _ (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) hne') h0 h1

/-- Splitting a positive `(m+n)`-step transition: some intermediate state `l` has
`π⁽ᵐ⁾ᵢₗ > 0` and `π⁽ⁿ⁾ₗₖ > 0`. -/
theorem exists_mid (hP : P ∈ rowStochastic ℝ S) {m n : ℕ} {i k : S}
    (h : 0 < (P ^ (m + n)) i k) : ∃ l, 0 < (P ^ m) i l ∧ 0 < (P ^ n) l k := by
  rw [pow_add, mul_apply] at h
  obtain ⟨l, hl⟩ := exists_pos_of_sum_pos h
  refine ⟨l, lt_of_le_of_ne (pow_nonneg' hP m i l) fun h0 => ?_,
    lt_of_le_of_ne (pow_nonneg' hP n l k) fun h0 => ?_⟩
  · rw [← h0, zero_mul] at hl; exact lt_irrefl 0 hl
  · rw [← h0, mul_zero] at hl; exact lt_irrefl 0 hl

/-- If all return times of `j` to itself are multiples of `d ≥ 2`, the ergodic set containing
`j` has cyclically moving subsets: `C_k` is the set of states reached from `j` at times
`≡ k (mod d)`. -/
theorem hasCyclicSubsets_of_period (hP : P ∈ rowStochastic ℝ S) {E : Finset S}
    (hE : IsErgodic P E) {j : S} (hj : j ∈ E) {d : ℕ} (hd : 2 ≤ d)
    (hdvd : ∀ n, 1 ≤ n → 0 < (P ^ n) j j → d ∣ n) : HasCyclicSubsets P E := by
  classical
  have hEj : E = consSet P j := hE.eq_consSet hP hj
  have hrec : ∀ i ∈ E, Cons P i j := fun i hi =>
    mem_consSet.1 (hE.eq_consSet hP hi ▸ hj)
  -- times of reaching a state are well defined mod `d`
  have hcong : ∀ i ∈ E, ∀ a b, 0 < (P ^ a) j i → 0 < (P ^ b) j i → a % d = b % d := by
    intro i hi a b ha hb
    obtain ⟨c, hc, hc'⟩ := hrec i hi
    have h1 := hdvd (a + c) (by omega) (pow_add_pos hP ha hc')
    have h2 := hdvd (b + c) (by omega) (pow_add_pos hP hb hc')
    have : a + c ≡ b + c [MOD d] :=
      ((Nat.modEq_zero_iff_dvd.2 h1).trans (Nat.modEq_zero_iff_dvd.2 h2).symm)
    exact Nat.ModEq.add_right_cancel' c this
  set C : ℕ → Finset S := fun k => E.filter fun i => ∃ n, 0 < (P ^ n) j i ∧ n % d = k % d
  have hmemC : ∀ {k i}, i ∈ C k ↔ i ∈ E ∧ ∃ n, 0 < (P ^ n) j i ∧ n % d = k % d := by
    intro k i; simp [C]
  obtain ⟨n₁, hn₁, hn₁'⟩ := hrec j hj
  have hdn₁ := hdvd n₁ hn₁ hn₁'
  have hn₁d : d ≤ n₁ := Nat.le_of_dvd (by omega) hdn₁
  refine ⟨d, hd, C, fun k => ?_, fun k => ?_, fun k k' hk hk' hne => ?_, fun k => filter_subset _ _,
    fun i hi => ?_, fun k i hi => ?_⟩
  · ext i; simp only [hmemC, Nat.add_mod_right]
  · -- a state reached at time `k % d`, on the way back to `j`
    have hlt : k % d < d := Nat.mod_lt _ (by omega)
    have hsplit : 0 < (P ^ (k % d + (n₁ - k % d))) j j := by
      rwa [Nat.add_sub_cancel' (by omega)]
    obtain ⟨l, hl, -⟩ := exists_mid hP hsplit
    exact ⟨l, hmemC.2 ⟨hE.2.1.mem_of_pow_pos hP hj _ hl, k % d, hl, Nat.mod_mod _ _⟩⟩
  · refine disjoint_left.2 fun i hi hi' => hne ?_
    obtain ⟨hiE, n, hn, hnk⟩ := hmemC.1 hi
    obtain ⟨-, n', hn', hnk'⟩ := hmemC.1 hi'
    have := hcong i hiE n n' hn hn'
    rw [hnk, hnk', Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hk'] at this
    exact this
  · obtain ⟨n, -, hn⟩ := mem_consSet.1 (hEj ▸ hi)
    exact ⟨n, hmemC.2 ⟨hi, n, hn, rfl⟩⟩
  · obtain ⟨hiE, n, hn, hnk⟩ := hmemC.1 hi
    refine sum_eq_one_of_pos_mem hP fun l hl => hmemC.2 ⟨?_, n + 1, ?_, ?_⟩
    · exact hE.2.1.mem_of_pow_pos hP hiE 1 (by rwa [pow_one])
    · exact pow_add_pos hP hn (by rwa [pow_one])
    · exact Nat.ModEq.add_right 1 hnk

/-- (2) ⇒ (1): a unique ergodic set without cyclically moving subsets gives `ε⁽ᴺ⁾ > 0`. The
return times of a state `j` of the ergodic set are closed under addition; by
`hasCyclicSubsets_of_period` they have no common divisor `d ≥ 2`, so they contain all large
integers, and `Πᴺ` has a positive `j`-th column for large `N`. -/
theorem eps_of_uniqueErgodic [Nonempty S] (hP : P ∈ rowStochastic ℝ S) {E : Finset S}
    (hE : IsErgodic P E) (huniq : ∀ E', IsErgodic P E' → E' = E)
    (hcyc : ¬ HasCyclicSubsets P E) : ∃ N, 1 ≤ N ∧ 0 < epsSum (P ^ N) := by
  obtain ⟨j, hj⟩ := (theorem_11_2 hP).1.1 ⟨E, hE, huniq⟩
  have hjE : j ∈ E := by
    obtain ⟨i, hi⟩ := hE.1
    exact hE.eq_consSet hP hi ▸ mem_consSet.2 (hj i)
  set R : Set ℕ := {n | 1 ≤ n ∧ 0 < (P ^ n) j j}
  have hadd : ∀ a ∈ R, ∀ b ∈ R, a + b ∈ R := fun a ha b hb =>
    ⟨by have := ha.1; omega, pow_add_pos hP ha.2 hb.2⟩
  obtain ⟨n₁, hn₁, hn₁'⟩ := hj j
  have hgcd : ∀ d, (∀ n ∈ R, d ∣ n) → d = 1 := by
    intro d hd
    rcases Nat.lt_or_ge d 2 with hd2 | hd2
    · rcases Nat.lt_or_ge d 1 with hd1 | hd1
      · have := hd n₁ ⟨hn₁, hn₁'⟩
        rw [show d = 0 by omega, zero_dvd_iff] at this
        omega
      · omega
    · exact absurd (hasCyclicSubsets_of_period hP hE hjE hd2 fun n hn hpos => hd n ⟨hn, hpos⟩)
        hcyc
  obtain ⟨n₀, hn₀⟩ := eventually_mem_of_add_closed hadd ⟨n₁, ⟨hn₁, hn₁'⟩, by omega⟩ hgcd
  choose m hm1 hm using hj
  set N := univ.sup m + n₀ + 1
  refine ⟨N, by omega, epsSum_pos_of_column (j := j) hP fun i => ?_⟩
  have hmi : m i ≤ univ.sup m := le_sup (f := m) (mem_univ i)
  have hrest : N - m i ∈ R := hn₀ _ (by omega)
  have := pow_add_pos hP (hm i) hrest.2
  rwa [Nat.add_sub_cancel' (by omega)] at this

/-- **Theorem 11.4.** For a finite chain the following are equivalent: (1) `ε⁽ᴺ⁾ > 0` for some
`N ≥ 1`; (2) there is a unique ergodic set and it has no cyclically moving subsets; (3) `p₀Πⁿ`
converges, to the same limit for every `p₀ ∈ Δ`. The rate of convergence is in
`theorem_11_4_rate`. -/
theorem theorem_11_4 [Nonempty S] (hP : P ∈ rowStochastic ℝ S) :
    ((∃ N, 1 ≤ N ∧ 0 < epsSum (P ^ N)) ↔
      ∃ E, (IsErgodic P E ∧ ∀ E', IsErgodic P E' → E' = E) ∧ ¬ HasCyclicSubsets P E) ∧
    ((∃ N, 1 ≤ N ∧ 0 < epsSum (P ^ N)) ↔
      ∃ p, ∀ p₀ ∈ simplex S, Tendsto (fun n => p₀ ᵥ* P ^ n) atTop (𝓝 p)) :=
  ⟨⟨fun ⟨_, hN, hε⟩ => uniqueErgodic_of_eps hP hN hε,
      fun ⟨_, ⟨hE, huniq⟩, hcyc⟩ => eps_of_uniqueErgodic hP hE huniq hcyc⟩,
    ⟨fun ⟨_, hN, hε⟩ => conv_of_eps hP hN hε, fun ⟨_, h⟩ => eps_of_conv hP h⟩⟩

end StokeyLucasPrescott.StrongConvergence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Transition functions

SLP §8.1, pp. 212–220. A transition function (`IsTransitionFunction`) is exactly a Markov kernel
(`isTransitionFunction_iff`). The Markov operator `T` on nonnegative and on bounded measurable
functions (`markovOp`, `markovOpR`) and its adjoint `T*` on probability measures (`adjointOp`):
Theorem 8.1 and its corollary (`theorem_8_1`, `theorem_8_1_cor`), Exercise 8.1 (`ex_8_1`),
Theorem 8.2 (`theorem_8_2`), Exercise 8.2 (`ex_8_2`), Theorem 8.3 and its corollary
(`theorem_8_3`, `theorem_8_3_cor`), the pairing `⟨f, λ⟩` and Exercise 8.3 (`ex_8_3`), the
`n`-step transition functions and Exercise 8.4 (`kpow`, `ex_8_4a`, `ex_8_4b`), the sequence
`λₙ = T*ⁿλ₀` (`adjointOp_iterate`), and the Feller and monotonicity properties (`IsFeller`,
`IsMonotoneTF`). Theorems 8.1 and 8.3 follow the book's proofs: indicators, then simple
functions, then increasing limits.
-/

namespace StokeyLucasPrescott.StrongConvergence

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {Z : Type*} [MeasurableSpace Z]

/-- A **transition function** (SLP p. 212): each `Q(z, ·)` is a probability measure and each
`Q(·, A)` is measurable. -/
def IsTransitionFunction (Q : Z → Set Z → ℝ≥0∞) : Prop :=
  (∀ z, ∃ μ : Measure Z, IsProbabilityMeasure μ ∧ ∀ A, MeasurableSet A → μ A = Q z A) ∧
    ∀ A, MeasurableSet A → Measurable fun z => Q z A

/-- Transition functions are Mathlib's Markov kernels. -/
theorem isTransitionFunction_iff (Q : Z → Set Z → ℝ≥0∞) :
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

theorem markovOp_indicator {A : Set Z} (hA : MeasurableSet A) (c : ℝ≥0∞) (z : Z) :
    markovOp κ (A.indicator fun _ => c) z = c * κ z A := by
  rw [markovOp, lintegral_indicator_const hA]

/-- **Theorem 8.1.** `T` maps nonnegative measurable functions into nonnegative measurable
functions. The book's proof: `Tχ_A = Q(·, A)` is measurable; `T` is additive on simple
functions; and `T` commutes with increasing limits (Monotone Convergence Theorem). -/
theorem theorem_8_1 {f : Z → ℝ≥0∞} (hf : Measurable f) : Measurable (markovOp κ f) := by
  refine Measurable.ennreal_induction (motive := fun f => Measurable (markovOp κ f))
    ?_ ?_ ?_ hf
  · intro c s hs
    have : markovOp κ (s.indicator fun _ => c) = fun z => c * κ z s :=
      funext (markovOp_indicator κ hs c)
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

theorem integrable_of_bounded {μ : Measure Z} [IsFiniteMeasure μ] {f : Z → ℝ} (hf : Measurable f)
    {M : ℝ} (hM : ∀ z, |f z| ≤ M) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable M (Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs]; exact hM z)

/-- **Corollary to Theorem 8.1.** `T` maps bounded measurable functions into bounded measurable
functions: `Tf = Tf⁺ − Tf⁻`, and `|Tf| ≤ sup |f|`. -/
theorem theorem_8_1_cor {f : Z → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ z, |f z| ≤ M) :
    Measurable (markovOpR κ f) ∧ ∀ z, |markovOpR κ f z| ≤ M := by
  constructor
  · have heq : markovOpR κ f = fun z =>
        (markovOp κ (fun z' => ENNReal.ofReal (f z')) z).toReal -
          (markovOp κ (fun z' => ENNReal.ofReal (-f z')) z).toReal := funext fun z =>
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part (integrable_of_bounded hf hM)
    rw [heq]
    exact (theorem_8_1 κ hf.ennreal_ofReal).ennreal_toReal.sub
      (theorem_8_1 κ hf.neg.ennreal_ofReal).ennreal_toReal
  · intro z
    have := norm_integral_le_of_norm_le_const (μ := κ z) (C := M) (f := f)
      (Eventually.of_forall fun z' => by rw [Real.norm_eq_abs]; exact hM z')
    simpa [markovOpR, Real.norm_eq_abs, measureReal_def] using this

/-- **Exercise 8.1.** `T(αf + βg) = αTf + βTg` on bounded measurable functions. -/
theorem ex_8_1 {f g : Z → ℝ} (hf : Measurable f) (hg : Measurable g) {M : ℝ}
    (hfM : ∀ z, |f z| ≤ M) (hgM : ∀ z, |g z| ≤ M) (α β : ℝ) :
    markovOpR κ (fun z => α * f z + β * g z) =
      fun z => α * markovOpR κ f z + β * markovOpR κ g z := by
  funext z
  simp only [markovOpR]
  rw [integral_add ((integrable_of_bounded hf hfM).const_mul α)
    ((integrable_of_bounded hg hgM).const_mul β), integral_const_mul, integral_const_mul]

omit [IsMarkovKernel κ] in
/-- `(T*λ)(A) = ∫ Q(z, A) λ(dz)` (SLP (2)). -/
theorem adjointOp_apply (lam : Measure Z) {A : Set Z} (hA : MeasurableSet A) :
    adjointOp κ lam A = ∫⁻ z, κ z A ∂lam :=
  Measure.bind_apply hA κ.aemeasurable

/-- **Theorem 8.2.** `T*` maps probability measures to probability measures: `T*λ(∅) = 0`,
`T*λ(Z) = 1`, and countable additivity follows from that of each `Q(z, ·)` by the Monotone
Convergence Theorem. -/
theorem theorem_8_2 (lam : Measure Z) [IsProbabilityMeasure lam] :
    IsProbabilityMeasure (adjointOp κ lam) ∧
      ∀ A : ℕ → Set Z, (∀ n, MeasurableSet (A n)) → Pairwise (Function.onFun Disjoint A) →
        ∫⁻ z, κ z (⋃ n, A n) ∂lam = ∑' n, ∫⁻ z, κ z (A n) ∂lam := by
  refine ⟨⟨?_⟩, fun A hA hd => ?_⟩
  · rw [adjointOp_apply κ lam MeasurableSet.univ]
    simp
  · simp_rw [measure_iUnion hd hA]
    exact lintegral_tsum fun n => (κ.measurable_coe (hA n)).aemeasurable

omit [IsMarkovKernel κ] in
/-- **Exercise 8.2.** `T*` is affine: `T*[αλ + (1 − α)μ] = αT*λ + (1 − α)T*μ`. -/
theorem ex_8_2 (lam μ : Measure Z) (α : ℝ≥0∞) :
    adjointOp κ (α • lam + (1 - α) • μ) = α • adjointOp κ lam + (1 - α) • adjointOp κ μ := by
  ext A hA
  simp only [adjointOp_apply κ _ hA, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  rfl

omit [IsMarkovKernel κ] in
/-- **Theorem 8.3.** `∫ (Tf) dλ = ∫ f d(T*λ)` for nonnegative measurable `f`. The book's proof:
indicators, simple functions, then the Monotone Convergence Theorem on both sides. -/
theorem theorem_8_3 (lam : Measure Z) {f : Z → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, markovOp κ f z ∂lam = ∫⁻ z', f z' ∂adjointOp κ lam := by
  refine Measurable.ennreal_induction (motive := fun f =>
    ∫⁻ z, markovOp κ f z ∂lam = ∫⁻ z', f z' ∂adjointOp κ lam) ?_ ?_ ?_ hf
  · intro c s hs
    simp_rw [markovOp_indicator κ hs]
    rw [lintegral_indicator hs, setLIntegral_const, adjointOp_apply κ lam hs,
      lintegral_const_mul _ (κ.measurable_coe hs), mul_comm]
  · intro f g hfg hf hg ihf ihg
    have : ∀ z, markovOp κ (f + g) z = markovOp κ f z + markovOp κ g z := fun z =>
      lintegral_add_left hf _
    simp_rw [this]
    rw [lintegral_add_left (theorem_8_1 κ hf), ihf, ihg, Pi.add_def,
      lintegral_add_left hf]
  · intro f hf hmono ih
    have : ∀ z, markovOp κ (fun x => ⨆ n, f n x) z = ⨆ n, markovOp κ (f n) z := fun z =>
      lintegral_iSup hf hmono
    simp_rw [this]
    rw [lintegral_iSup (fun n => theorem_8_1 κ (hf n))
      (fun m n hmn z => lintegral_mono (hmono hmn)), lintegral_iSup hf hmono]
    simp_rw [ih]

/-- **Corollary to Theorem 8.3.** `∫ (Tf) dλ = ∫ f d(T*λ)` for bounded measurable `f`. -/
theorem theorem_8_3_cor (lam : Measure Z) [IsProbabilityMeasure lam] {f : Z → ℝ}
    (hf : Measurable f) {M : ℝ} (hM : ∀ z, |f z| ≤ M) :
    ∫ z, markovOpR κ f z ∂lam = ∫ z', f z' ∂adjointOp κ lam := by
  have : IsProbabilityMeasure (adjointOp κ lam) := (theorem_8_2 κ lam).1
  have hTf := theorem_8_1_cor κ hf hM
  have hpos : ∀ g : Z → ℝ, Measurable g → (∀ z, |g z| ≤ M) → ∀ z,
      markovOpR κ g z = (markovOp κ (fun z' => ENNReal.ofReal (g z')) z).toReal -
        (markovOp κ (fun z' => ENNReal.ofReal (-g z')) z).toReal := fun g hg hgM z =>
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part (integrable_of_bounded hg hgM)
  have hfin : ∀ g : Z → ℝ, Measurable g → (∀ z, |g z| ≤ M) → ∀ z,
      markovOp κ (fun z' => ENNReal.ofReal (g z')) z ≠ ∞ := fun g hg hgM z =>
    ((integrable_of_bounded hg hgM (μ := κ z)).lintegral_lt_top).ne
  have hbd : ∀ g : Z → ℝ, Measurable g → (∀ z, |g z| ≤ M) →
      Integrable (fun z => (markovOp κ (fun z' => ENNReal.ofReal (g z')) z).toReal) lam :=
    fun g hg hgM => integrable_of_bounded (theorem_8_1 κ hg.ennreal_ofReal).ennreal_toReal
      (M := |M|) fun z => by
        rw [abs_of_nonneg ENNReal.toReal_nonneg]
        refine ENNReal.toReal_le_of_le_ofReal (abs_nonneg M) ?_
        calc markovOp κ (fun z' => ENNReal.ofReal (g z')) z
            ≤ ∫⁻ _, ENNReal.ofReal |M| ∂κ z :=
              lintegral_mono fun z' => ENNReal.ofReal_le_ofReal
                ((le_abs_self _).trans ((hgM z').trans (le_abs_self M)))
          _ = ENNReal.ofReal |M| := by simp
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part (integrable_of_bounded hf hM),
    integral_congr_ae (Eventually.of_forall (hpos f hf hM))]
  rw [integral_sub, integral_toReal (theorem_8_1 κ hf.ennreal_ofReal).aemeasurable
    (Eventually.of_forall fun z => (hfin f hf hM z).lt_top),
    integral_toReal (f := fun z => markovOp κ (fun z' => ENNReal.ofReal (-f z')) z)
      (theorem_8_1 κ hf.neg.ennreal_ofReal).aemeasurable
    (Eventually.of_forall fun z => (hfin (fun z => -f z) hf.neg (fun z => by
      rw [abs_neg]; exact hM z) z).lt_top),
    theorem_8_3 κ lam hf.ennreal_ofReal,
    theorem_8_3 κ lam (f := fun z => ENNReal.ofReal (-f z)) hf.neg.ennreal_ofReal]
  · exact hbd f hf hM
  · exact hbd (fun z => -f z) hf.neg fun z => by rw [abs_neg]; exact hM z

/-- The pairing `⟨f, λ⟩ = ∫ f dλ` (SLP p. 218). -/
noncomputable def pairing (f : Z → ℝ) (lam : Measure Z) : ℝ := ∫ z, f z ∂lam

omit [IsMarkovKernel κ] in
/-- **Exercise 8.3.** The pairing is linear in `f` and affine in `λ`. -/
theorem ex_8_3 {f g : Z → ℝ} (hf : Measurable f) (hg : Measurable g) {M : ℝ}
    (hfM : ∀ z, |f z| ≤ M) (hgM : ∀ z, |g z| ≤ M) (a b : ℝ) (lam μ : Measure Z)
    [IsProbabilityMeasure lam] [IsProbabilityMeasure μ] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    pairing (fun z => a * f z + b * g z) lam = a * pairing f lam + b * pairing g lam ∧
      pairing f (ENNReal.ofReal α • lam + ENNReal.ofReal (1 - α) • μ) =
        α * pairing f lam + (1 - α) * pairing f μ := by
  constructor
  · simp only [pairing]
    rw [integral_add ((integrable_of_bounded hf hfM).const_mul a)
      ((integrable_of_bounded hg hgM).const_mul b), integral_const_mul, integral_const_mul]
  · simp only [pairing]
    rw [integral_add_measure ((integrable_of_bounded hf hfM).smul_measure ENNReal.ofReal_ne_top)
      ((integrable_of_bounded hf hfM).smul_measure ENNReal.ofReal_ne_top),
      integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal hα0,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul, smul_eq_mul]

/-- The `n`-step transition function (SLP p. 219): `Q⁰ = id`,
`Qⁿ⁺¹(z, A) = ∫ Qⁿ(z′, A) Q(z, dz′)`. -/
noncomputable def kpow (κ : Kernel Z Z) : ℕ → Kernel Z Z
  | 0 => Kernel.id
  | n + 1 => kpow κ n ∘ₖ κ

omit [IsMarkovKernel κ] in
theorem kpow_one : kpow κ 1 = κ := by simp [kpow]

/-- **Exercise 8.4a.** The functions `Qⁿ` are transition functions. -/
theorem ex_8_4a (n : ℕ) : IsMarkovKernel (kpow κ n) := by
  induction n with
  | zero => exact inferInstanceAs (IsMarkovKernel Kernel.id)
  | succ n ih => exact inferInstanceAs (IsMarkovKernel (kpow κ n ∘ₖ κ))

omit [IsMarkovKernel κ] in
theorem kpow_add (n m : ℕ) : kpow κ (n + m) = kpow κ m ∘ₖ kpow κ n := by
  induction n with
  | zero => simp [kpow]
  | succ n ih =>
    rw [show n + 1 + m = (n + m) + 1 by omega, kpow, ih, kpow, Kernel.comp_assoc]

omit [IsMarkovKernel κ] in
theorem markovOp_comp (η : Kernel Z Z) {f : Z → ℝ≥0∞} (hf : Measurable f) :
    markovOp (η ∘ₖ κ) f = markovOp κ (markovOp η f) := by
  funext z
  exact Kernel.lintegral_comp η κ z hf

omit [IsMarkovKernel κ] in
theorem adjointOp_comp (η : Kernel Z Z) (lam : Measure Z) :
    adjointOp (η ∘ₖ κ) lam = adjointOp η (adjointOp κ lam) := by
  simp only [adjointOp]
  rw [Measure.bind_bind κ.aemeasurable η.aemeasurable]
  rfl

omit [IsMarkovKernel κ] in
/-- **Exercise 8.4b.** `T⁽ⁿ⁺ᵐ⁾f = Tⁿ(Tᵐf)` and `T*⁽ⁿ⁺ᵐ⁾λ = T*ⁿ(T*ᵐλ)`. -/
theorem ex_8_4b (n m : ℕ) {f : Z → ℝ≥0∞} (hf : Measurable f) (lam : Measure Z) :
    markovOp (kpow κ (n + m)) f = markovOp (kpow κ n) (markovOp (kpow κ m) f) ∧
      adjointOp (kpow κ (n + m)) lam = adjointOp (kpow κ n) (adjointOp (kpow κ m) lam) := by
  constructor
  · rw [kpow_add, markovOp_comp _ _ hf]
  · rw [add_comm, kpow_add, adjointOp_comp]

omit [IsMarkovKernel κ] in
/-- `λₙ = T*λₙ₋₁ = T*ⁿlam₀` (SLP p. 219). -/
theorem adjointOp_iterate (n : ℕ) (lam₀ : Measure Z) :
    (adjointOp κ)^[n] lam₀ = adjointOp (kpow κ n) lam₀ := by
  induction n generalizing lam₀ with
  | zero =>
    change lam₀ = lam₀.bind Kernel.id
    have : (⇑(Kernel.id : Kernel Z Z)) = fun z => Measure.dirac z := funext Kernel.id_apply
    rw [this, Measure.bind_dirac]
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, kpow, adjointOp_comp]

/-- `Q` has the **Feller property** (SLP p. 220): `T` maps bounded continuous functions to
continuous functions. -/
def IsFeller [TopologicalSpace Z] (κ : Kernel Z Z) : Prop :=
  ∀ f : Z → ℝ, Continuous f → (∃ M, ∀ z, |f z| ≤ M) → Continuous (markovOpR κ f)

/-- `Q` is **monotone** (SLP p. 220): `T` maps bounded nondecreasing measurable functions to
nondecreasing functions. -/
def IsMonotoneTF [Preorder Z] (κ : Kernel Z Z) : Prop :=
  ∀ f : Z → ℝ, Measurable f → (∃ M, ∀ z, |f z| ≤ M) → Monotone f → Monotone (markovOpR κ f)

end StokeyLucasPrescott.StrongConvergence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Convergence concepts for measures

SLP §11.2, pp. 334–338. For probability measures `λₙ`, `λ`:

* `ConvSetwise`: `λₙ(A) → λ(A)` for every measurable `A` ((1), p. 335).
* `ConvIntegrals`: `∫ f dλₙ → ∫ f dλ` for every bounded measurable `f` ((2), p. 335).
* `ConvWeak`: `∫ f dλₙ → ∫ f dλ` for every bounded continuous `f` ((3), p. 337).
* `ConvStrong`: (2), uniformly over measurable `f` with `‖f‖ ≤ 1` (p. 337).

Results:

* **Exercise 11.2** (`ex_11_2`): (1) implies (2); so the two are equivalent (`convSetwise_iff`).
  The book's route is uniform approximation by simple functions. Here, for `0 ≤ f ≤ C`, the
  layer-cake formula `∫ f dλ = ∫₀^C λ{f > t} dt` and dominated convergence in `t` are used.
* The halving example (p. 336, `halving_not_setwise`, `halving_weak`): unit masses at `2⁻ⁿ`
  converge weakly to the unit mass at `0`, but converge setwise to no probability measure at all.
  The book takes `S = [0, 1]`; here `S = ℝ`, and the masses all lie in `[0, 1]`.
-/

namespace StokeyLucasPrescott.StrongConvergence

open MeasureTheory Filter Topology Set BoundedContinuousFunction

variable {S : Type*} [MeasurableSpace S]

/-- `λₙ` converges **setwise** to `λ` ((1), p. 335). -/
def ConvSetwise (ls : ℕ → Measure S) (l : Measure S) : Prop :=
  ∀ A, MeasurableSet A → Tendsto (fun n => (ls n).real A) atTop (𝓝 (l.real A))

/-- `∫ f dλₙ → ∫ f dλ` for every bounded measurable `f` ((2), p. 335). -/
def ConvIntegrals (ls : ℕ → Measure S) (l : Measure S) : Prop :=
  ∀ f : S → ℝ, Measurable f → (∃ C, ∀ s, |f s| ≤ C) →
    Tendsto (fun n => ∫ s, f s ∂ls n) atTop (𝓝 (∫ s, f s ∂l))

/-- `λₙ` converges **weakly** to `λ` ((3), p. 337). -/
def ConvWeak [TopologicalSpace S] (ls : ℕ → Measure S) (l : Measure S) : Prop :=
  ∀ f : S →ᵇ ℝ, Tendsto (fun n => ∫ s, f s ∂ls n) atTop (𝓝 (∫ s, f s ∂l))

/-- `λₙ` converges **strongly** to `λ` (p. 337): (2) holds, uniformly over `‖f‖ ≤ 1`. -/
def ConvStrong (ls : ℕ → Measure S) (l : Measure S) : Prop :=
  ConvIntegrals ls l ∧ ∀ ε > 0, ∀ᶠ n in atTop, ∀ f : S → ℝ, Measurable f →
    (∀ s, |f s| ≤ 1) → |∫ s, f s ∂ls n - ∫ s, f s ∂l| < ε

/-- (2) implies (1): integrate indicator functions. -/
theorem convSetwise_of_convIntegrals {ls : ℕ → Measure S} {l : Measure S}
    (h : ConvIntegrals ls l) : ConvSetwise ls l := by
  intro A hA
  have := h (A.indicator 1) (measurable_one.indicator hA) ⟨1, fun s => by
    by_cases hs : s ∈ A <;> simp [hs]⟩
  simpa [integral_indicator_one hA] using this

/-- The layer-cake integrand `t ↦ λ{f > t}` is antitone, hence measurable. -/
theorem measurable_meas_lt (μ : Measure S) [IsFiniteMeasure μ] (f : S → ℝ) :
    Measurable fun t : ℝ => μ.real {a | t < f a} := by
  refine Antitone.measurable fun t t' htt' => ?_
  exact measureReal_mono fun a (ha : t' < f a) => lt_of_le_of_lt htt' ha

/-- **Exercise 11.2.** Setwise convergence of probability measures implies convergence of the
integrals of all bounded measurable functions. -/
theorem ex_11_2 {ls : ℕ → Measure S} {l : Measure S} [∀ n, IsProbabilityMeasure (ls n)]
    [IsProbabilityMeasure l] (h : ConvSetwise ls l) : ConvIntegrals ls l := by
  intro f hf ⟨C, hC⟩
  -- reduce to `g = f + C`, with `0 ≤ g ≤ 2C`
  set g := fun s => f s + C
  have hg0 : ∀ s, 0 ≤ g s := fun s => by have := (abs_le.1 (hC s)).1; simp only [g]; linarith
  have hg1 : ∀ s, g s ≤ 2 * C := fun s => by
    have := (abs_le.1 (hC s)).2; simp only [g]; linarith
  have hgm : Measurable g := hf.add_const C
  have hint : ∀ (μ : Measure S) [IsProbabilityMeasure μ], Integrable g μ := fun μ _ =>
    Integrable.of_bound hgm.aestronglyMeasurable (2 * C) (Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 s)]; exact hg1 s)
  have hfint : ∀ (μ : Measure S) [IsProbabilityMeasure μ], Integrable f μ := fun μ _ =>
    Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs]; exact hC s)
  have hcake : ∀ (μ : Measure S) [IsProbabilityMeasure μ],
      ∫ s, f s ∂μ = (∫ t in Ioi 0, μ.real {a | t < g a}) - C := fun μ _ => by
    rw [← (hint μ).integral_eq_integral_meas_lt (Eventually.of_forall hg0), integral_add (hfint μ)
      (integrable_const C)]
    simp
  simp_rw [hcake]
  refine Tendsto.sub_const ?_ C
  -- dominated convergence in `t`
  refine tendsto_integral_of_dominated_convergence ((Ioc (0 : ℝ) (2 * C)).indicator 1)
    (fun n => (measurable_meas_lt (ls n) g).aestronglyMeasurable) ?_ (fun n => ?_) ?_
  · exact ((integrable_indicator_iff measurableSet_Ioc).2
      (integrableOn_const measure_Ioc_lt_top.ne)).restrict
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun t (ht : 0 < t) => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    by_cases htC : t ≤ 2 * C
    · rw [indicator_of_mem (show t ∈ Ioc 0 (2 * C) from ⟨ht, htC⟩), Pi.one_apply]
      exact measureReal_le_one
    · have : {a | t < g a} = ∅ := by
        ext a; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
        exact (hg1 a).trans (le_of_lt (not_le.1 htC))
      rw [this, measureReal_empty]
      exact indicator_nonneg (fun _ _ => zero_le_one) t
  · exact Eventually.of_forall fun t => h _ (measurableSet_lt measurable_const hgm)

/-- (1) and (2) are equivalent for probability measures. -/
theorem convSetwise_iff {ls : ℕ → Measure S} {l : Measure S} [∀ n, IsProbabilityMeasure (ls n)]
    [IsProbabilityMeasure l] : ConvSetwise ls l ↔ ConvIntegrals ls l :=
  ⟨ex_11_2, convSetwise_of_convIntegrals⟩

/-- The deterministic system `s_{t+1} = s_t/2` started at `1`: unit masses at `2⁻ⁿ`. -/
noncomputable def halving (n : ℕ) : Measure ℝ := Measure.dirac ((1 / 2 : ℝ) ^ n)

/-- The halving example (p. 336): the unit masses at `2⁻ⁿ` converge setwise to no finite
measure. Each interval `(0, 2⁻ᵏ)` has `λₙ`-measure `1` for `n > k`, so a setwise limit would give
it measure `1`; but the intervals decrease to `∅`. -/
theorem halving_not_setwise (l : Measure ℝ) [IsFiniteMeasure l] : ¬ ConvSetwise halving l := by
  intro h
  set U : ℕ → Set ℝ := fun k => Ioo 0 ((1 / 2 : ℝ) ^ k)
  have hU1 : ∀ k, l (U k) = 1 := by
    intro k
    have hlim := h (U k) measurableSet_Ioo
    have hev : ∀ᶠ n in atTop, (halving n).real (U k) = 1 := by
      filter_upwards [eventually_gt_atTop k] with n hn
      have hmem : (1 / 2 : ℝ) ^ n ∈ U k :=
        ⟨by positivity, pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) hn⟩
      rw [halving, measureReal_def, Measure.dirac_apply_of_mem hmem]
      rfl
    have := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm))
    rw [measureReal_def, ENNReal.toReal_eq_one_iff] at this
    exact this
  have hanti : Antitone U := fun k k' hkk' => Ioo_subset_Ioo_right
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) hkk')
  have hempty : (⋂ k, U k) = ∅ := by
    ext t
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall, U, mem_Ioo, not_and,
      not_lt]
    by_cases ht : 0 < t
    · obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one ht (by norm_num : (1 / 2 : ℝ) < 1)
      exact ⟨k, fun _ => hk.le⟩
    · exact ⟨0, fun h0 => absurd h0 ht⟩
  have hlim := tendsto_measure_iInter_atTop (μ := l) (fun k => measurableSet_Ioo.nullMeasurableSet)
    hanti ⟨0, measure_ne_top l _⟩
  rw [hempty, measure_empty] at hlim
  have : (fun k => l (U k)) = fun _ => 1 := funext hU1
  rw [Function.comp_def, this] at hlim
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hlim)

/-- The halving example (p. 337): the unit masses at `2⁻ⁿ` converge weakly to the unit mass at
`0`. -/
theorem halving_weak : ConvWeak halving (Measure.dirac 0) := by
  intro f
  simp only [halving, integral_dirac]
  exact (f.continuous.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
    (by norm_num))

end StokeyLucasPrescott.StrongConvergence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The total variation norm

SLP §11.3, pp. 338–344. For a set function `D` (a signed measure, or `λ₁ − λ₂` for finite
measures) the total variation is `‖D‖ = sup Σᵢ |D(Aᵢ)|` over finite measurable partitions
`A₁, …, Aₖ` of `S` (`tvOf`, (1) on p. 339). `tvNorm ν` is the norm of a signed measure (the book's
`Φ(S, 𝒮)` is Mathlib's `SignedMeasure S`), and `tvDist λ₁ λ₂ = ‖λ₁ − λ₂‖`.

* **Exercise 11.3** (`ex_11_3`): every signed measure is a difference of finite measures, and
  `‖·‖` is a norm on signed measures.
* **Lemma 11.5** (`lemma_11_5`): for finite measures of equal mass,
  `‖λ₁ − λ₂‖ = 2 sup_A |λ₁(A) − λ₂(A)|`. The book proves it for probability measures, using
  Lemma 7.12, and applies it in Lemma 11.11 to measures of equal but smaller mass. Here it is
  proved for equal masses, using the Hahn decomposition.
-/

namespace StokeyLucasPrescott.StrongConvergence

open MeasureTheory Set Finset
open scoped Pointwise

variable {S : Type*} [MeasurableSpace S]

/-- A finite measurable partition `A₁, …, Aₖ` of `S`. -/
def IsPartition {k : ℕ} (A : Fin k → Set S) : Prop :=
  (∀ i, MeasurableSet (A i)) ∧ Pairwise (Function.onFun Disjoint A) ∧ ⋃ i, A i = Set.univ

/-- The sums `Σᵢ |D(Aᵢ)|` over finite measurable partitions. -/
def partSums (D : Set S → ℝ) : Set ℝ :=
  {x | ∃ k, ∃ A : Fin k → Set S, IsPartition A ∧ x = ∑ i, |D (A i)|}

/-- The total variation `sup Σᵢ |D(Aᵢ)|` over finite measurable partitions ((1), p. 339). -/
noncomputable def tvOf (D : Set S → ℝ) : ℝ := sSup (partSums D)

/-- The **total variation norm** of a signed measure. -/
noncomputable def tvNorm (ν : SignedMeasure S) : ℝ := tvOf fun A => ν A

/-- `‖λ₁ − λ₂‖` for finite measures. -/
noncomputable def tvDist (μ₁ μ₂ : Measure S) : ℝ := tvOf fun A => μ₁.real A - μ₂.real A

/-- `sup_A |λ₁(A) − λ₂(A)|` over measurable `A`. -/
noncomputable def supDiff (μ₁ μ₂ : Measure S) : ℝ :=
  sSup ((fun A => |μ₁.real A - μ₂.real A|) '' {A | MeasurableSet A})

theorem isPartition_univ : IsPartition (fun _ : Fin 1 => (Set.univ : Set S)) :=
  ⟨fun _ => MeasurableSet.univ, fun i j hij => absurd (Subsingleton.elim i j) hij,
    iUnion_const _⟩

/-- The partition `{B, Bᶜ}`. -/
theorem isPartition_pair {B : Set S} (hB : MeasurableSet B) :
    IsPartition (fun i : Fin 2 => if i = 0 then B else Bᶜ) := by
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

theorem partSums_nonempty (D : Set S → ℝ) : (partSums D).Nonempty :=
  ⟨_, 1, _, isPartition_univ, rfl⟩

/-- A finite measure of a partition adds up to the whole. -/
theorem sum_partition_real (μ : Measure S) [IsFiniteMeasure μ] {k : ℕ} {A : Fin k → Set S}
    (hA : IsPartition A) : ∑ i, μ.real (A i) = μ.real Set.univ := by
  rw [← measureReal_iUnion_fintype hA.2.1 hA.1, hA.2.2]

theorem sum_partition_inter_real (μ : Measure S) [IsFiniteMeasure μ] {k : ℕ}
    {A : Fin k → Set S} (hA : IsPartition A) {B : Set S} (hB : MeasurableSet B) :
    ∑ i, μ.real (A i ∩ B) = μ.real B := by
  rw [← measureReal_iUnion_fintype (fun i j hij => (hA.2.1 hij).mono inter_subset_left
    inter_subset_left) fun i => (hA.1 i).inter hB, ← iUnion_inter, hA.2.2, univ_inter]

theorem partSums_bddAbove_of_le {D : Set S → ℝ} {C : ℝ}
    (h : ∀ k (A : Fin k → Set S), IsPartition A → ∑ i, |D (A i)| ≤ C) :
    BddAbove (partSums D) :=
  ⟨C, by rintro _ ⟨k, A, hA, rfl⟩; exact h k A hA⟩

/-- For finite measures the partition sums are bounded by `λ₁(S) + λ₂(S)`. -/
theorem partSums_le_of_measures (μ₁ μ₂ : Measure S) [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂] {k : ℕ} {A : Fin k → Set S} (hA : IsPartition A) :
    ∑ i, |μ₁.real (A i) - μ₂.real (A i)| ≤ μ₁.real Set.univ + μ₂.real Set.univ := by
  rw [← sum_partition_real μ₁ hA, ← sum_partition_real μ₂ hA, ← sum_add_distrib]
  exact sum_le_sum fun i _ => (abs_sub _ _).trans (by
    rw [abs_of_nonneg measureReal_nonneg, abs_of_nonneg measureReal_nonneg])

theorem bddAbove_tvDist (μ₁ μ₂ : Measure S) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] :
    BddAbove (partSums fun A => μ₁.real A - μ₂.real A) :=
  partSums_bddAbove_of_le fun _ _ hA => partSums_le_of_measures μ₁ μ₂ hA

/-- **Lemma 11.5**, for finite measures of equal mass: `‖λ₁ − λ₂‖ = 2 sup_A |λ₁(A) − λ₂(A)|`.
Let `B` be a Hahn set (`λ₁ ≥ λ₂` on subsets of `B`, `λ₁ ≤ λ₂` on subsets of `Bᶜ`) and
`D = λ₁ − λ₂`. Then `|D(A)| ≤ D(B)` for every `A`, each partition sum is at most
`D(B) − D(Bᶜ) = 2D(B)`, and `{B, Bᶜ}` attains it. -/
theorem lemma_11_5 (μ₁ μ₂ : Measure S) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (h : μ₁ Set.univ = μ₂ Set.univ) :
    tvDist μ₁ μ₂ = 2 * supDiff μ₁ μ₂ ∧ ∃ B, MeasurableSet B ∧
      supDiff μ₁ μ₂ = μ₁.real B - μ₂.real B ∧ μ₂.real Bᶜ - μ₁.real Bᶜ = μ₁.real B - μ₂.real B := by
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
  have hpart : ∀ k (A : Fin k → Set S), IsPartition A → ∑ i, |D (A i)| ≤ 2 * D B := by
    intro k A hA
    calc ∑ i, |D (A i)| ≤ ∑ i, (D (A i ∩ B) - D (A i ∩ Bᶜ)) := sum_le_sum fun i _ => by
          rw [hsplit (A i) (hA.1 i)]
          have := hP (A i ∩ B) ((hA.1 i).inter hB) inter_subset_right
          have := hN (A i ∩ Bᶜ) ((hA.1 i).inter hB.compl) inter_subset_right
          rw [abs_le]; constructor <;> linarith
      _ = D B - D Bᶜ := by
          simp only [D, sum_sub_distrib, sum_partition_inter_real μ₁ hA hB,
            sum_partition_inter_real μ₂ hA hB, sum_partition_inter_real μ₁ hA hB.compl,
            sum_partition_inter_real μ₂ hA hB.compl]
      _ = 2 * D B := by rw [hcompl]; ring
  have htv : tvDist μ₁ μ₂ = 2 * D B := by
    refine le_antisymm (csSup_le (partSums_nonempty _) ?_) ?_
    · rintro _ ⟨k, A, hA, rfl⟩; exact hpart k A hA
    · refine le_csSup (bddAbove_tvDist μ₁ μ₂) ⟨2, _, isPartition_pair hB, ?_⟩
      simp only [Fin.sum_univ_two, Fin.isValue, ↓reduceIte, one_ne_zero]
      change 2 * D B = |D B| + |D Bᶜ|
      rw [hcompl, abs_neg, abs_of_nonneg hDB]; ring
  have hsup : supDiff μ₁ μ₂ = D B := by
    refine le_antisymm (csSup_le ⟨_, ∅, MeasurableSet.empty, rfl⟩ ?_) ?_
    · rintro _ ⟨A, hA, rfl⟩; exact habs A hA
    · refine le_csSup ⟨D B, ?_⟩ ⟨B, hB, abs_of_nonneg hDB⟩
      rintro _ ⟨A, hA, rfl⟩; exact habs A hA
  refine ⟨by rw [htv, hsup], B, hB, hsup, ?_⟩
  have := hcompl
  simp only [D] at this ⊢; linarith

/-- Every signed measure is a difference of finite measures (its Jordan decomposition). -/
theorem exists_sub_measures (ν : SignedMeasure S) :
    ∃ (μ₁ μ₂ : Measure S) (_ : IsFiniteMeasure μ₁) (_ : IsFiniteMeasure μ₂),
      ν = μ₁.toSignedMeasure - μ₂.toSignedMeasure :=
  ⟨_, _, inferInstance, inferInstance, (SignedMeasure.toSignedMeasure_toJordanDecomposition ν).symm⟩

theorem tvNorm_sub_eq (μ₁ μ₂ : Measure S) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] :
    tvNorm (μ₁.toSignedMeasure - μ₂.toSignedMeasure) = tvDist μ₁ μ₂ := by
  unfold tvNorm tvDist tvOf partSums
  congr 1
  ext x
  refine exists_congr fun k => exists_congr fun A => and_congr_right fun hA => ?_
  have e : ∑ i, |(μ₁.toSignedMeasure - μ₂.toSignedMeasure) (A i)| =
      ∑ i, |μ₁.real (A i) - μ₂.real (A i)| :=
    sum_congr rfl fun i _ => by rw [Measure.toSignedMeasure_sub_apply (hA.1 i)]
  exact Iff.of_eq (congrArg (x = ·) e)

theorem bddAbove_tvNorm (ν : SignedMeasure S) : BddAbove (partSums fun A => ν A) := by
  obtain ⟨μ₁, μ₂, _, _, rfl⟩ := exists_sub_measures ν
  refine partSums_bddAbove_of_le (C := μ₁.real Set.univ + μ₂.real Set.univ) fun k A hA => ?_
  have e : ∑ i, |(μ₁.toSignedMeasure - μ₂.toSignedMeasure) (A i)| =
      ∑ i, |μ₁.real (A i) - μ₂.real (A i)| :=
    sum_congr rfl fun i _ => by rw [Measure.toSignedMeasure_sub_apply (hA.1 i)]
  exact e ▸ partSums_le_of_measures μ₁ μ₂ hA

theorem tvOf_nonneg {D : Set S → ℝ} (hD : BddAbove (partSums D)) : 0 ≤ tvOf D :=
  le_trans (sum_nonneg fun _ _ => abs_nonneg _) (le_csSup hD ⟨1, _, isPartition_univ, rfl⟩)

theorem abs_le_tvOf {D : Set S → ℝ} (hD : BddAbove (partSums D)) {A : Set S}
    (hA : MeasurableSet A) : |D A| ≤ tvOf D := by
  refine le_trans ?_ (le_csSup hD ⟨2, _, isPartition_pair hA, rfl⟩)
  simp only [Fin.sum_univ_two, Fin.isValue, ↓reduceIte, one_ne_zero]
  linarith [abs_nonneg (D Aᶜ)]

/-- **Exercise 11.3.** Signed measures (differences of finite measures) form a vector space,
and the total variation `‖ν‖ = sup Σᵢ |ν(Aᵢ)|` is a norm on it. -/
theorem ex_11_3 :
    (∀ ν : SignedMeasure S, ∃ (μ₁ μ₂ : Measure S) (_ : IsFiniteMeasure μ₁)
      (_ : IsFiniteMeasure μ₂), ν = μ₁.toSignedMeasure - μ₂.toSignedMeasure) ∧
    tvNorm (0 : SignedMeasure S) = 0 ∧ (∀ ν : SignedMeasure S, 0 ≤ tvNorm ν) ∧
    (∀ ν : SignedMeasure S, tvNorm ν = 0 → ν = 0) ∧
    (∀ (c : ℝ) (ν : SignedMeasure S), tvNorm (c • ν) = |c| * tvNorm ν) ∧
    ∀ ν ν' : SignedMeasure S, tvNorm (ν + ν') ≤ tvNorm ν + tvNorm ν' := by
  refine ⟨exists_sub_measures, ?_, fun ν => tvOf_nonneg (bddAbove_tvNorm ν), fun ν h => ?_,
    fun c ν => ?_, fun ν ν' => ?_⟩
  · refine le_antisymm (csSup_le (partSums_nonempty _) ?_) (tvOf_nonneg (bddAbove_tvNorm 0))
    rintro _ ⟨k, A, -, rfl⟩
    simp
  · ext A hA
    have := abs_le_tvOf (bddAbove_tvNorm ν) hA
    change |ν A| ≤ tvNorm ν at this
    rw [h] at this
    simpa using abs_nonpos_iff.1 this
  · have hset : partSums (fun A => (c • ν) A) = |c| • partSums fun A => ν A := by
      ext x
      rw [Set.mem_smul_set]
      constructor
      · rintro ⟨k, A, hA, rfl⟩
        refine ⟨_, ⟨k, A, hA, rfl⟩, ?_⟩
        simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, abs_mul, mul_sum]
      · rintro ⟨_, ⟨k, A, hA, rfl⟩, rfl⟩
        refine ⟨k, A, hA, ?_⟩
        simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, abs_mul, mul_sum]
    unfold tvNorm tvOf
    rw [hset, Real.sSup_smul_of_nonneg (abs_nonneg c), smul_eq_mul]
  · refine csSup_le (partSums_nonempty _) ?_
    rintro _ ⟨k, A, hA, rfl⟩
    calc ∑ i, |(ν + ν') (A i)| ≤ ∑ i, |ν (A i)| + ∑ i, |ν' (A i)| := by
          rw [← sum_add_distrib]
          exact sum_le_sum fun i _ => by
            simp only [FunLike.coe_add, Pi.add_apply]; exact abs_add_le _ _
      _ ≤ tvNorm ν + tvNorm ν' := add_le_add (le_csSup (bddAbove_tvNorm ν) ⟨k, A, hA, rfl⟩)
          (le_csSup (bddAbove_tvNorm ν') ⟨k, A, hA, rfl⟩)

end StokeyLucasPrescott.StrongConvergence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Characterizations of strong convergence

SLP §11.3, Theorems 11.6–11.7 and Lemma 11.8, pp. 340–344. Throughout, `λₙ` and `λ` are
probability measures.

* `abs_integral_sub_le_tvDist`: `|∫ f dλ₁ − ∫ f dλ₂| ≤ ‖λ₁ − λ₂‖` for measurable `|f| ≤ 1`. With a
  Hahn set `B`, `λ₁ = λ₂ + α₁` on `B` and `λ₂ = λ₁ + α₂` on `Bᶜ`, and the difference of the
  integrals is `∫ f dα₁ − ∫ f dα₂`.
* **Theorem 11.6** (`theorem_11_6`): `‖λₙ − λ‖ → 0` iff `λₙ(A) → λ(A)` uniformly in `A`.
* **Theorem 11.7** (`theorem_11_7`): `‖λₙ − λ‖ → 0` iff `λₙ → λ` strongly. The book
  approximates by simple functions; here the bound above is used directly.
* **Lemma 11.8** (`lemma_11_8`): the probability measures are complete in the total variation
  norm. The book's proof that the limit `λ(A) = lim λₙ(A)` is countably additive exchanges a
  limit and a sum without justification. The exchange holds because the convergence is uniform
  in `A`: the tails `λ(⋃_{i ≥ K} Aᵢ)` are within `ε` of `λₙ(⋃_{i ≥ K} Aᵢ)`, which tend to `0`.
-/

namespace StokeyLucasPrescott.StrongConvergence

open MeasureTheory Filter Topology Set

variable {S : Type*} [MeasurableSpace S]

theorem abs_sub_le_add (μ₁ μ₂ : Measure S) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (A : Set S) : |μ₁.real A - μ₂.real A| ≤ μ₁.real univ + μ₂.real univ :=
  (abs_sub _ _).trans (by
    rw [abs_of_nonneg measureReal_nonneg, abs_of_nonneg measureReal_nonneg]
    exact add_le_add (measureReal_mono (subset_univ A)) (measureReal_mono (subset_univ A)))

theorem bddAbove_supDiff (μ₁ μ₂ : Measure S) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] :
    BddAbove ((fun A => |μ₁.real A - μ₂.real A|) '' {A | MeasurableSet A}) :=
  ⟨_, by rintro _ ⟨A, -, rfl⟩; exact abs_sub_le_add μ₁ μ₂ A⟩

/-- `2|λ₁(A) − λ₂(A)| ≤ ‖λ₁ − λ₂‖` for probability measures. -/
theorem two_abs_le_tvDist (μ₁ μ₂ : Measure S) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] {A : Set S} (hA : MeasurableSet A) :
    2 * |μ₁.real A - μ₂.real A| ≤ tvDist μ₁ μ₂ := by
  rw [(lemma_11_5 μ₁ μ₂ (by simp)).1]
  exact mul_le_mul_of_nonneg_left (le_csSup (bddAbove_supDiff μ₁ μ₂) ⟨A, hA, rfl⟩)
    zero_le_two

/-- If `|λ₁(A) − λ₂(A)| ≤ δ` for all `A`, then `‖λ₁ − λ₂‖ ≤ 2δ`. -/
theorem tvDist_le_of_forall (μ₁ μ₂ : Measure S) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] {δ : ℝ} (h : ∀ A, MeasurableSet A → |μ₁.real A - μ₂.real A| ≤ δ) :
    tvDist μ₁ μ₂ ≤ 2 * δ := by
  rw [(lemma_11_5 μ₁ μ₂ (by simp)).1]
  refine mul_le_mul_of_nonneg_left (csSup_le ⟨_, ∅, MeasurableSet.empty, rfl⟩ ?_) zero_le_two
  rintro _ ⟨A, hA, rfl⟩
  exact h A hA

theorem tvDist_nonneg (μ₁ μ₂ : Measure S) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] :
    0 ≤ tvDist μ₁ μ₂ :=
  tvOf_nonneg (bddAbove_tvDist μ₁ μ₂)

/-- For a nonnegative sequence, `uₙ → 0` iff eventually `uₙ < ε` for every `ε > 0`. -/
theorem tendsto_zero_iff_of_nonneg {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n) :
    Tendsto u atTop (𝓝 0) ↔ ∀ ε > 0, ∀ᶠ n in atTop, u n < ε := by
  rw [tendsto_order]
  exact ⟨fun h => h.2, fun h => ⟨fun a ha => Eventually.of_forall fun n => ha.trans_le (hu n), h⟩⟩

/-- **Theorem 11.6.** `‖λₙ − λ‖ → 0` iff `λₙ(A) → λ(A)` uniformly in `A`. -/
theorem theorem_11_6 (ls : ℕ → Measure S) (l : Measure S) [∀ n, IsProbabilityMeasure (ls n)]
    [IsProbabilityMeasure l] :
    Tendsto (fun n => tvDist (ls n) l) atTop (𝓝 0) ↔
      ∀ ε > 0, ∀ᶠ n in atTop, ∀ A, MeasurableSet A → |(ls n).real A - l.real A| < ε := by
  rw [tendsto_zero_iff_of_nonneg fun n => tvDist_nonneg (ls n) l]
  constructor
  · intro h ε hε
    filter_upwards [h (2 * ε) (by positivity)] with n hn A hA
    have := two_abs_le_tvDist (ls n) l hA
    linarith
  · intro h ε hε
    filter_upwards [h (ε / 4) (by positivity)] with n hn
    have := tvDist_le_of_forall (ls n) l fun A hA => (hn A hA).le
    linarith

theorem integrable_of_abs_le (μ : Measure S) [IsFiniteMeasure μ] {f : S → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ s, |f s| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall fun s => by
    rw [Real.norm_eq_abs]; exact hC s)

/-- The partition `{B, Bᶜ}` bounds `|D(B)| + |D(Bᶜ)|` by the total variation. -/
theorem abs_add_abs_compl_le (μ₁ μ₂ : Measure S) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    {B : Set S} (hB : MeasurableSet B) :
    |μ₁.real B - μ₂.real B| + |μ₁.real Bᶜ - μ₂.real Bᶜ| ≤ tvDist μ₁ μ₂ := by
  refine le_trans (le_of_eq ?_) (le_csSup (bddAbove_tvDist μ₁ μ₂) ⟨2, _, isPartition_pair hB, rfl⟩)
  simp [Fin.sum_univ_two]

/-- `|∫ f dλ₁ − ∫ f dλ₂| ≤ ‖λ₁ − λ₂‖` for measurable `f` with `|f| ≤ 1`. -/
theorem abs_integral_sub_le_tvDist (μ₁ μ₂ : Measure S) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
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
    integrable_of_abs_le μ hf h1
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
  have htv := abs_add_abs_compl_le μ₁ μ₂ hB
  rw [abs_of_nonneg hD1, abs_of_nonpos hD2] at htv
  have hb1 := hb α₁
  have hb2 := hb α₂
  rw [hsplit1, hsplit2]
  calc |∫ s, f s ∂α₁ + ∫ s in B, f s ∂μ₂ + ∫ s in Bᶜ, f s ∂μ₁ -
        (∫ s in B, f s ∂μ₂ + (∫ s, f s ∂α₂ + ∫ s in Bᶜ, f s ∂μ₁))|
      = |∫ s, f s ∂α₁ - ∫ s, f s ∂α₂| := by ring_nf
    _ ≤ |∫ s, f s ∂α₁| + |∫ s, f s ∂α₂| := abs_sub _ _
    _ ≤ tvDist μ₁ μ₂ := by linarith

/-- **Theorem 11.7.** `‖λₙ − λ‖ → 0` iff `λₙ → λ` strongly: `∫ f dλₙ → ∫ f dλ` for every bounded
measurable `f`, uniformly over `‖f‖ ≤ 1`. -/
theorem theorem_11_7 (ls : ℕ → Measure S) (l : Measure S) [∀ n, IsProbabilityMeasure (ls n)]
    [IsProbabilityMeasure l] :
    Tendsto (fun n => tvDist (ls n) l) atTop (𝓝 0) ↔ ConvStrong ls l := by
  have hnn := fun n => tvDist_nonneg (ls n) l
  constructor
  · intro h
    refine ⟨fun f hf ⟨C, hC⟩ => ?_, fun ε hε => ?_⟩
    · -- scale `f` into the unit ball
      set K := |C| + 1
      have hK : 0 < K := by positivity
      have hg : ∀ s, |f s / K| ≤ 1 := fun s => by
        rw [abs_div, abs_of_pos hK, div_le_one hK]
        exact (hC s).trans ((le_abs_self C).trans (by linarith))
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
        ((h.const_mul K).trans_eq (by rw [mul_zero]) : Tendsto (fun n => K * tvDist (ls n) l)
          atTop (𝓝 0))
      have := abs_integral_sub_le_tvDist (ls n) l (hf.div_const K) hg
      rw [integral_div, integral_div, ← sub_div, abs_div, abs_of_pos hK, div_le_iff₀ hK] at this
      rw [Real.norm_eq_abs]; linarith
    · filter_upwards [(tendsto_zero_iff_of_nonneg hnn).1 h ε hε] with n hn f hf h1
      exact (abs_integral_sub_le_tvDist (ls n) l hf h1).trans_lt hn
  · rintro ⟨-, h⟩
    refine (theorem_11_6 ls l).2 fun ε hε => ?_
    filter_upwards [h ε hε] with n hn A hA
    have := hn (A.indicator 1) (measurable_one.indicator hA) fun s => by
      by_cases hs : s ∈ A <;> simp [hs]
    simpa [integral_indicator_one hA] using this

omit [MeasurableSpace S] in
/-- The tails `⋃_{i ≥ K} Aᵢ` of a disjoint sequence decrease to `∅`. -/
theorem iInter_tails_eq_empty {f : ℕ → Set S} (hd : Pairwise (Function.onFun Disjoint f)) :
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
theorem lemma_11_8 (ls : ℕ → Measure S) [∀ n, IsProbabilityMeasure (ls n)]
    (hC : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, tvDist (ls n) (ls m) < ε) :
    ∃ l : Measure S, IsProbabilityMeasure l ∧ Tendsto (fun n => tvDist (ls n) l) atTop (𝓝 0) := by
  -- (7): the measures of sets are uniformly Cauchy
  have hunif : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, ∀ A, MeasurableSet A →
      |(ls n).real A - (ls m).real A| < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hC (2 * ε) (by positivity)
    exact ⟨N, fun n hn m hm A hA => by
      have := two_abs_le_tvDist (ls n) (ls m) hA; have := hN n hn m hm; linarith⟩
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
      rw [tendsto_zero_iff_of_nonneg fun K => hF0 _ (hT K)]
      intro ε hε
      obtain ⟨N, hN⟩ := hFu (ε / 2) (by positivity)
      have hanti : Antitone T := fun K K' hKK' => iUnion_mono fun i =>
        iUnion_subset fun hi => subset_iUnion (fun _ : K ≤ i => f i) (hKK'.trans hi)
      have hlim := tendsto_measure_iInter_atTop (μ := ls N) (fun K => (hT K).nullMeasurableSet)
        hanti ⟨0, measure_ne_top _ _⟩
      rw [iInter_tails_eq_empty hd, measure_empty] at hlim
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
  refine ⟨l, hlp, (tendsto_zero_iff_of_nonneg fun n => tvDist_nonneg (ls n) l).2 fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hFu (ε / 4) (by positivity)
  refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
  have := tvDist_le_of_forall (ls n) l fun A hA => by rw [hl A hA]; exact hN n hn A hA
  linarith

end StokeyLucasPrescott.StrongConvergence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Doeblin's condition and Condition M

SLP §11.4, pp. 344–349. `P` is a transition function, a Markov kernel `κ`, with `n`-step
transitions `Pⁿ = kpow κ n`.

* `DoeblinFor κ φ N ε` (**Condition D**, p. 345): `φ` is a finite measure, and `φ(A) ≤ ε` implies
  `Pᴺ(s, A) ≤ 1 − ε` for all `s`. `doeblinFor_mono` shows it persists for `N′ ≥ N` (the book's
  "Why?").
* `ConditionMFor κ N ε` (**Condition M**, p. 348): for each `A`, either `Pᴺ(s, A) ≥ ε` for all
  `s`, or `Pᴺ(s, Aᶜ) ≥ ε` for all `s`.
* **Exercise 11.4** (`ex_11_4a`–`ex_11_4j`): sufficient conditions for Condition D, and three
  kernels violating it.
* **Exercise 11.5** (`ex_11_5a`, `ex_11_5b`, `ex_11_5c`): Condition M holds in Exercise 11.4c and
  11.4e, and implies Condition D. The identity on two points satisfies D but not M.
-/

namespace StokeyLucasPrescott.StrongConvergence

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {S : Type*} [MeasurableSpace S]

/-- **Condition D** (Doeblin, p. 345) for `(φ, N, ε)`. -/
def DoeblinFor (κ : Kernel S S) (φ : Measure S) (N : ℕ) (ε : ℝ) : Prop :=
  IsFiniteMeasure φ ∧ 1 ≤ N ∧ 0 < ε ∧
    ∀ A, MeasurableSet A → φ.real A ≤ ε → ∀ s, (kpow κ N s).real A ≤ 1 - ε

/-- `P` satisfies **Condition D** for some `(φ, N, ε)`. -/
def ConditionD (κ : Kernel S S) : Prop := ∃ φ N ε, DoeblinFor κ φ N ε

/-- **Condition M** (p. 348) for `(N, ε)`. -/
def ConditionMFor (κ : Kernel S S) (N : ℕ) (ε : ℝ) : Prop :=
  1 ≤ N ∧ 0 < ε ∧ ∀ A, MeasurableSet A →
    (∀ s, ε ≤ (kpow κ N s).real A) ∨ ∀ s, ε ≤ (kpow κ N s).real Aᶜ

/-- `P` satisfies **Condition M** for some `(N, ε)`. -/
def ConditionM (κ : Kernel S S) : Prop := ∃ N ε, ConditionMFor κ N ε

variable {κ : Kernel S S} [IsMarkovKernel κ]

omit [IsMarkovKernel κ] in
/-- Chapman–Kolmogorov: `Pⁿ⁺ᵐ(s, A) = ∫ Pᵐ(s′, A) Pⁿ(s, ds′)`. -/
theorem kpow_add_apply (n m : ℕ) (s : S) {A : Set S} (hA : MeasurableSet A) :
    kpow κ (n + m) s A = ∫⁻ s', kpow κ m s' A ∂kpow κ n s := by
  rw [kpow_add, Kernel.comp_apply' _ _ _ hA]

theorem isMarkov_kpow (n : ℕ) : IsMarkovKernel (kpow κ n) := ex_8_4a κ n

/-- An average of numbers at most `c ≤ 1` is at most `c`. -/
theorem kpow_real_le_of_forall {n m : ℕ} {A : Set S} (hA : MeasurableSet A) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ s', (kpow κ m s').real A ≤ c) (s : S) : (kpow κ (n + m) s).real A ≤ c := by
  have := isMarkov_kpow (κ := κ) n
  have := isMarkov_kpow (κ := κ) m
  have hle : kpow κ (n + m) s A ≤ ENNReal.ofReal c := by
    rw [kpow_add_apply n m s hA]
    calc ∫⁻ s', kpow κ m s' A ∂kpow κ n s ≤ ∫⁻ _, ENNReal.ofReal c ∂kpow κ n s :=
          lintegral_mono fun s' => by
            rw [← ENNReal.ofReal_toReal (measure_ne_top _ A)]
            exact ENNReal.ofReal_le_ofReal (h s')
      _ = ENNReal.ofReal c := by simp
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal hc hle

/-- Condition D for `(φ, N, ε)` holds for `(φ, N′, ε)`, `N′ ≥ N` (p. 345, "Why?"). -/
theorem doeblinFor_mono [Nonempty S] {φ : Measure S} {N N' : ℕ} {ε : ℝ}
    (h : DoeblinFor κ φ N ε) (hNN' : N ≤ N') : DoeblinFor κ φ N' ε := by
  obtain ⟨hφ, hN, hε, hD⟩ := h
  have hε1 : ε ≤ 1 := by
    obtain ⟨s⟩ := ‹Nonempty S›
    have := hD ∅ MeasurableSet.empty (by simp [hε.le]) s
    simp at this; linarith
  refine ⟨hφ, hN.trans hNN', hε, fun A hA hφA s => ?_⟩
  have := kpow_real_le_of_forall (n := N' - N) (m := N) hA (by linarith)
    (fun s' => hD A hA hφA s') s
  rwa [Nat.sub_add_cancel hNN'] at this

theorem real_le_one_sub_of_compl {μ : Measure S} [IsProbabilityMeasure μ] {A : Set S}
    (hA : MeasurableSet A) {c : ℝ} (h : c ≤ μ.real Aᶜ) : μ.real A ≤ 1 - c := by
  have := probReal_compl_eq_one_sub (μ := μ) hA
  linarith

/-- A finite measure gives mass at most `ε` to some point of any injective sequence. -/
theorem exists_small_atom [MeasurableSingletonClass S] (φ : Measure S) [IsFiniteMeasure φ]
    {x : ℕ → S} (hx : Function.Injective x) {ε : ℝ} (hε : 0 < ε) :
    ∃ k, φ.real {x k} ≤ ε := by
  by_contra hc
  push Not at hc
  obtain ⟨K, hK⟩ := exists_nat_gt (φ.real univ / ε)
  have hsum : φ.real (⋃ k ∈ Finset.range K, {x k}) = ∑ k ∈ Finset.range K, φ.real {x k} :=
    measureReal_biUnion_finset (fun i _ j _ hij => Set.disjoint_singleton.2 (hx.ne hij))
      (fun k _ => measurableSet_singleton _) (fun k _ => measure_ne_top _ _)
  have hlt : (K : ℝ) * ε < ∑ k ∈ Finset.range K, φ.real {x k} := by
    rcases Nat.eq_zero_or_pos K with rfl | hK0
    · rw [Nat.cast_zero] at hK
      exact absurd hK (not_lt.2 (div_nonneg measureReal_nonneg hε.le))
    · calc (K : ℝ) * ε = ∑ _k ∈ Finset.range K, ε := by simp
        _ < _ := Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.2 (by omega))
          fun k _ => hc k
  have hle := measureReal_mono (μ := φ) (subset_univ (⋃ k ∈ Finset.range K, {x k}))
  rw [div_lt_iff₀ hε] at hK
  linarith

omit [IsMarkovKernel κ] in
/-- **Exercise 11.4a.** On a finite set with all subsets measurable, every `P` satisfies
Condition D (with `φ` the counting measure). -/
theorem ex_11_4a [Finite S] [MeasurableSingletonClass S] : ConditionD κ := by
  have : IsFiniteMeasure (Measure.count : Measure S) := ⟨by
    rw [Measure.count_apply_finite _ Set.finite_univ]; exact ENNReal.natCast_lt_top _⟩
  refine ⟨Measure.count, 1, 1 / 2, this, le_rfl, by norm_num, fun A hA hφA s => ?_⟩
  have hA0 : A = ∅ := by
    by_contra hne
    obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.2 hne
    have h1 : (1 : ℝ) ≤ (Measure.count : Measure S).real A := by
      have := measureReal_mono (μ := (Measure.count : Measure S)) (Set.singleton_subset_iff.2 ha)
      rw [measureReal_def, Measure.count_singleton] at this
      simpa using this
    linarith
  subst hA0
  simp only [measureReal_empty]
  norm_num

/-- **Exercise 11.4b.** On `ℕ`, if the tails `Σ_{j ≥ J} pᵢⱼ` tend to zero uniformly in `i`,
Condition D holds (with `φ` the counting measure on `{0, …, J − 1}`). -/
theorem ex_11_4b {κ : Kernel ℕ ℕ} [IsMarkovKernel κ]
    (htail : ∀ δ > 0, ∃ J, ∀ i, (κ i).real (Ici J) ≤ δ) : ConditionD κ := by
  obtain ⟨J, hJ⟩ := htail (1 / 2) (by norm_num)
  set φ : Measure ℕ := Measure.count.restrict (Iio J)
  have hφ : IsFiniteMeasure φ := ⟨by
    rw [Measure.restrict_apply_univ, Measure.count_apply_finite _ (Set.finite_Iio J)]
    exact ENNReal.natCast_lt_top _⟩
  refine ⟨φ, 1, 1 / 2, hφ, le_rfl, by norm_num, fun A hA hφA i => ?_⟩
  have hsub : A ⊆ Ici J := by
    intro a ha
    by_contra hlt
    have hmem : a ∈ A ∩ Iio J := ⟨ha, Set.mem_Iio.2 (not_le.1 fun h => hlt h)⟩
    have h1 : (1 : ℝ≥0∞) ≤ φ A := by
      rw [Measure.restrict_apply hA, ← Measure.count_singleton a]
      exact measure_mono (Set.singleton_subset_iff.2 hmem)
    have h1 : (1 : ℝ) ≤ φ.real A :=
      ENNReal.toReal_one ▸ ENNReal.toReal_mono (measure_ne_top φ A) h1
    linarith
  rw [kpow_one]
  calc (κ i).real A ≤ (κ i).real (Ici J) := measureReal_mono hsub
    _ ≤ 1 / 2 := hJ i
    _ = 1 - 1 / 2 := by norm_num

/-- **Exercise 11.4c.** If `Pᴺ(s, {s₀}) > ε` for all `s`, Condition D holds (with `φ = δ_{s₀}`). -/
theorem ex_11_4c [MeasurableSingletonClass S] {s₀ : S} {N : ℕ} {ε : ℝ} (hN : 1 ≤ N)
    (hε : 0 < ε) (h : ∀ s, ε < (kpow κ N s).real {s₀}) : ConditionD κ := by
  have := isMarkov_kpow (κ := κ) N
  refine ⟨Measure.dirac s₀, N, min ε (1 / 2), inferInstance, hN, lt_min hε (by norm_num),
    fun A hA hφA s => ?_⟩
  have hs₀ : s₀ ∉ A := fun hmem => by
    rw [measureReal_def, Measure.dirac_apply_of_mem hmem, ENNReal.toReal_one] at hφA
    have := min_le_right ε (1 / 2 : ℝ)
    linarith
  refine real_le_one_sub_of_compl hA ?_
  calc min ε (1 / 2) ≤ ε := min_le_left _ _
    _ ≤ (kpow κ N s).real {s₀} := (h s).le
    _ ≤ (kpow κ N s).real Aᶜ := measureReal_mono (Set.singleton_subset_iff.2 hs₀)

/-- **Exercise 11.4d.** If `Pᴺ(s, A) ≤ φ(A)` for a finite measure `φ`, Condition D holds. -/
theorem ex_11_4d {φ : Measure S} [IsFiniteMeasure φ] {N : ℕ} (hN : 1 ≤ N)
    (h : ∀ s A, MeasurableSet A → kpow κ N s A ≤ φ A) : ConditionD κ := by
  have := isMarkov_kpow (κ := κ) N
  refine ⟨φ, N, 1 / 2, inferInstance, hN, by norm_num, fun A hA hφA s => ?_⟩
  have : (kpow κ N s).real A ≤ φ.real A :=
    ENNReal.toReal_mono (measure_ne_top φ A) (h s A hA)
  linarith

omit [IsMarkovKernel κ] in
/-- The lower bound `P(s, A) ≥ δ μ(A)` from a density bounded below by `δ`. -/
theorem density_lower {μ : Measure S} {p : S → S → ℝ} {δ : ℝ} (hp : ∀ s x, δ ≤ p s x)
    (hκ : ∀ s A, MeasurableSet A → κ s A = ∫⁻ x in A, ENNReal.ofReal (p s x) ∂μ) (s : S)
    {A : Set S} (hA : MeasurableSet A) : ENNReal.ofReal δ * μ A ≤ κ s A := by
  rw [hκ s A hA, ← setLIntegral_const]
  exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hp s x)

/-- **Exercise 11.4e.** If `P(s, A) = ∫_A p(s, s′) μ(ds′)` for a finite measure `μ` and a density
bounded below by `δ > 0`, Condition D holds. -/
theorem ex_11_4e {μ : Measure S} [IsFiniteMeasure μ] {p : S → S → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hp : ∀ s x, δ ≤ p s x)
    (hκ : ∀ s A, MeasurableSet A → κ s A = ∫⁻ x in A, ENNReal.ofReal (p s x) ∂μ) :
    ConditionD κ := by
  rcases isEmpty_or_nonempty S with hS | ⟨⟨s₀⟩⟩
  · exact ⟨μ, 1, 1 / 2, inferInstance, le_rfl, by norm_num, fun A _ _ s => isEmptyElim s⟩
  set m := μ.real univ
  have hm : 0 < m := by
    refine lt_of_le_of_ne measureReal_nonneg fun h0 => ?_
    have hμ0 : μ = 0 := Measure.measure_univ_eq_zero.1
      ((ENNReal.toReal_eq_zero_iff _).1 h0.symm |>.resolve_right (measure_ne_top μ univ))
    have := hκ s₀ univ MeasurableSet.univ
    rw [measure_univ, hμ0, Measure.restrict_zero, lintegral_zero_measure] at this
    exact one_ne_zero this
  set ε := δ * m / (1 + δ)
  have hε : 0 < ε := by positivity
  refine ⟨μ, 1, ε, inferInstance, le_rfl, hε, fun A hA hμA s => ?_⟩
  rw [kpow_one]
  refine real_le_one_sub_of_compl hA ?_
  have hlow := density_lower hp hκ s hA.compl
  have hreal : δ * μ.real Aᶜ ≤ (κ s).real Aᶜ := by
    have := ENNReal.toReal_mono (measure_ne_top _ _) hlow
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ.le] at this
  have hcompl : μ.real Aᶜ = m - μ.real A := measureReal_compl hA
  have hεeq : δ * (m - ε) = ε := by simp only [ε]; field_simp; ring
  calc ε = δ * (m - ε) := hεeq.symm
    _ ≤ δ * μ.real Aᶜ := mul_le_mul_of_nonneg_left (by linarith) hδ.le
    _ ≤ (κ s).real Aᶜ := hreal

/-- **Exercise 11.4f.** If `P(s, A) = ∫_A p(s, s′) μ(ds′)` with `p ≤ K`, Condition D holds (by
Exercise 11.4d with `φ = Kμ`). -/
theorem ex_11_4f {μ : Measure S} [IsFiniteMeasure μ] {p : S → S → ℝ} {K : ℝ}
    (hp : ∀ s x, p s x ≤ K)
    (hκ : ∀ s A, MeasurableSet A → κ s A = ∫⁻ x in A, ENNReal.ofReal (p s x) ∂μ) :
    ConditionD κ := by
  refine ex_11_4d (φ := K.toNNReal • μ) le_rfl fun s A hA => ?_
  rw [kpow_one, hκ s A hA, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
    ← setLIntegral_const]
  exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hp s x)

omit [IsMarkovKernel κ] in
/-- For the mixture `P = αP₁ + (1 − α)P₂`, `Pⁿ ≥ αⁿP₁ⁿ`. -/
theorem kpow_mixture_ge {κ₁ κ₂ : Kernel S S} [IsMarkovKernel κ₁] {α : ℝ}
    (hκ : ∀ s, κ s = ENNReal.ofReal α • κ₁ s + ENNReal.ofReal (1 - α) • κ₂ s) (hα : 0 ≤ α) :
    ∀ n s {A : Set S}, MeasurableSet A →
      ENNReal.ofReal (α ^ n) * kpow κ₁ n s A ≤ kpow κ n s A := by
  intro n
  induction n with
  | zero => intro s A hA; simp [kpow]
  | succ n ih =>
    intro s A hA
    rw [show n + 1 = 1 + n by ring, kpow_add_apply 1 n s hA, kpow_add_apply 1 n s hA, kpow_one,
      kpow_one]
    calc ENNReal.ofReal (α ^ (1 + n)) * ∫⁻ s', kpow κ₁ n s' A ∂κ₁ s
        = ∫⁻ s', ENNReal.ofReal (α ^ n) * kpow κ₁ n s' A ∂(ENNReal.ofReal α • κ₁ s) := by
          rw [lintegral_smul_measure, lintegral_const_mul _ (Kernel.measurable_coe _ hA),
            pow_add, pow_one, ENNReal.ofReal_mul hα, smul_eq_mul, mul_assoc]
      _ ≤ ∫⁻ s', ENNReal.ofReal (α ^ n) * kpow κ₁ n s' A ∂κ s :=
          lintegral_mono' (by rw [hκ s]; exact Measure.le_add_right le_rfl) le_rfl
      _ ≤ ∫⁻ s', kpow κ n s' A ∂κ s := lintegral_mono fun s' => ih s' hA

/-- **Exercise 11.4g.** If `P = αP₁ + (1 − α)P₂` with `α ∈ (0, 1)` and `P₁` satisfies Condition D
for `(φ, N, ε)`, then `P` satisfies it for `(φ, N, αᴺε)`. -/
theorem ex_11_4g {κ₁ κ₂ : Kernel S S} [IsMarkovKernel κ₁] {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hκ : ∀ s, κ s = ENNReal.ofReal α • κ₁ s + ENNReal.ofReal (1 - α) • κ₂ s)
    {φ : Measure S} {N : ℕ} {ε : ℝ} (h₁ : DoeblinFor κ₁ φ N ε) :
    DoeblinFor κ φ N (α ^ N * ε) := by
  obtain ⟨hφ, hN, hε, hD⟩ := h₁
  have := isMarkov_kpow (κ := κ) N
  have := isMarkov_kpow (κ := κ₁) N
  have hαN : α ^ N ≤ 1 := pow_le_one₀ hα0.le hα1.le
  refine ⟨hφ, hN, by positivity, fun A hA hφA s => real_le_one_sub_of_compl hA ?_⟩
  have h1 : ε ≤ (kpow κ₁ N s).real Aᶜ := by
    have := hD A hA (hφA.trans (by nlinarith)) s
    have := probReal_compl_eq_one_sub (μ := kpow κ₁ N s) hA
    linarith
  have h2 := kpow_mixture_ge hκ hα0.le N s hA.compl
  have h3 := ENNReal.toReal_mono (measure_ne_top _ _) h2
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h3
  change α ^ N * (kpow κ₁ N s).real Aᶜ ≤ (kpow κ N s).real Aᶜ at h3
  nlinarith [pow_pos hα0 N]

/-- The `n`-step transitions of a deterministic kernel: `Pⁿ(s, ·) = δ_{fⁿ(s)}`. -/
theorem kpow_deterministic {f : S → S} (hf : Measurable f) (n : ℕ) (s : S) :
    kpow (Kernel.deterministic f hf) n s = Measure.dirac (f^[n] s) := by
  induction n generalizing s with
  | zero => simp [kpow, Kernel.id_apply]
  | succ n ih =>
    rw [kpow, Kernel.comp_deterministic_eq_comap, Kernel.comap_apply, ih,
      Function.iterate_succ_apply]

/-- A deterministic injective map on a space with infinitely many points violates Condition D:
a finite `φ` gives small mass to some point `fᴺ(yₖ)`, which `Pᴺ` reaches with probability one
from `yₖ`. -/
theorem not_conditionD_deterministic [MeasurableSingletonClass S] {f : S → S}
    (hf : Measurable f) (hinj : Function.Injective f) {y : ℕ → S}
    (hy : Function.Injective y) : ¬ ConditionD (Kernel.deterministic f hf) := by
  rintro ⟨φ, N, ε, hφ, -, hε, hD⟩
  obtain ⟨k, hk⟩ := exists_small_atom φ ((hinj.iterate N).comp hy) hε
  have := hD _ (measurableSet_singleton _) hk (y k)
  simp only [Function.comp_apply] at this
  rw [kpow_deterministic, measureReal_def, Measure.dirac_apply_of_mem (mem_singleton _),
    ENNReal.toReal_one] at this
  linarith

/-- **Exercise 11.4h.** The identity on a countably infinite set violates Condition D. -/
theorem ex_11_4h : ¬ ConditionD (Kernel.deterministic (id : ℕ → ℕ) measurable_id) :=
  not_conditionD_deterministic measurable_id Function.injective_id Function.injective_id

/-- **Exercise 11.4i.** The shift `sᵢ ↦ sᵢ₊₁` violates Condition D. -/
theorem ex_11_4i : ¬ ConditionD (Kernel.deterministic Nat.succ measurable_from_top) :=
  not_conditionD_deterministic measurable_from_top Nat.succ_injective Function.injective_id

/-- The halving map `s ↦ s/2` on `[0, 1]`. -/
noncomputable def halve (s : Icc (0 : ℝ) 1) : Icc (0 : ℝ) 1 :=
  ⟨s.1 / 2, by have := s.2; constructor <;> linarith [this.1, this.2]⟩

theorem measurable_halve : Measurable halve :=
  (Continuous.subtype_mk (continuous_subtype_val.div_const 2) _).measurable

/-- **Exercise 11.4j.** The deterministic halving `P(s, A) = 1` iff `s/2 ∈ A` on `[0, 1]`
violates Condition D. -/
theorem ex_11_4j : ¬ ConditionD (Kernel.deterministic halve measurable_halve) := by
  refine not_conditionD_deterministic measurable_halve (fun a b h => ?_)
    (y := fun k => ⟨1 / (k + 1 : ℝ), by positivity, by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]⟩) ?_
  · have := congrArg Subtype.val h
    simp only [halve] at this
    exact Subtype.ext (by linarith)
  · intro j k h
    have := congrArg Subtype.val h
    simp only at this
    have : (j : ℝ) + 1 = k + 1 := by
      rwa [one_div, one_div, inv_inj] at this
    exact_mod_cast (by linarith : (j : ℝ) = k)

/-- **Exercise 11.5a** (for Exercise 11.4c). If `Pᴺ(s, {s₀}) > ε` for all `s`, Condition M
holds: `s₀` lies in `A` or in `Aᶜ`. -/
theorem ex_11_5a_c [MeasurableSingletonClass S] {s₀ : S} {N : ℕ} {ε : ℝ} (hN : 1 ≤ N)
    (hε : 0 < ε) (h : ∀ s, ε < (kpow κ N s).real {s₀}) : ConditionM κ := by
  have := isMarkov_kpow (κ := κ) N
  refine ⟨N, ε, hN, hε, fun A hA => ?_⟩
  by_cases hs₀ : s₀ ∈ A
  · exact Or.inl fun s => (h s).le.trans (measureReal_mono (Set.singleton_subset_iff.2 hs₀))
  · exact Or.inr fun s => (h s).le.trans (measureReal_mono (Set.singleton_subset_iff.2 hs₀))

/-- **Exercise 11.5a** (for Exercise 11.4e). A density bounded below by `δ > 0` gives Condition M
with `ε = δμ(S)/2`: one of `A`, `Aᶜ` has `μ`-measure at least `μ(S)/2`. -/
theorem ex_11_5a_e {μ : Measure S} [IsFiniteMeasure μ] {p : S → S → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hp : ∀ s x, δ ≤ p s x)
    (hκ : ∀ s A, MeasurableSet A → κ s A = ∫⁻ x in A, ENNReal.ofReal (p s x) ∂μ) :
    ConditionM κ := by
  rcases isEmpty_or_nonempty S with hS | ⟨⟨s₀⟩⟩
  · exact ⟨1, 1, le_rfl, one_pos, fun A _ => Or.inl fun s => isEmptyElim s⟩
  set m := μ.real univ
  have hm : 0 < m := by
    refine lt_of_le_of_ne measureReal_nonneg fun h0 => ?_
    have hμ0 : μ = 0 := Measure.measure_univ_eq_zero.1
      ((ENNReal.toReal_eq_zero_iff _).1 h0.symm |>.resolve_right (measure_ne_top μ univ))
    have := hκ s₀ univ MeasurableSet.univ
    rw [measure_univ, hμ0, Measure.restrict_zero, lintegral_zero_measure] at this
    exact one_ne_zero this
  have hlow : ∀ s {A : Set S}, MeasurableSet A → δ * μ.real A ≤ (κ s).real A := fun s A hA => by
    have := ENNReal.toReal_mono (measure_ne_top _ _) (density_lower hp hκ s hA)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ.le] at this
  refine ⟨1, δ * m / 2, le_rfl, by positivity, fun A hA => ?_⟩
  simp only [kpow_one]
  have hsum : μ.real A + μ.real Aᶜ = m := measureReal_add_measureReal_compl hA
  rcases le_total (m / 2) (μ.real A) with hA2 | hA2
  · exact Or.inl fun s => le_trans (by nlinarith) (hlow s hA)
  · exact Or.inr fun s => le_trans (by nlinarith) (hlow s hA.compl)

/-- **Exercise 11.5b.** Condition M implies Condition D (with `φ = Pᴺ(s₀, ·)` and `ε/2`). -/
theorem ex_11_5b (h : ConditionM κ) : ConditionD κ := by
  obtain ⟨N, ε, hN, hε, hM⟩ := h
  have := isMarkov_kpow (κ := κ) N
  rcases isEmpty_or_nonempty S with hS | ⟨⟨s₀⟩⟩
  · exact ⟨0, 1, 1, inferInstance, le_rfl, one_pos, fun A _ _ s => isEmptyElim s⟩
  refine ⟨kpow κ N s₀, N, ε / 2, inferInstance, hN, by positivity, fun A hA hφA s => ?_⟩
  rcases hM A hA with h1 | h2
  · have := h1 s₀; linarith
  · have := real_le_one_sub_of_compl hA (h2 s); linarith

/-- **Exercise 11.5c.** The identity on two points satisfies Condition D (Exercise 11.4a) but not
Condition M: from `true` the set `{false}` is never reached, and from `false` its complement
`{true}` is never reached. -/
theorem ex_11_5c :
    ConditionD (Kernel.deterministic (id : Bool → Bool) measurable_id) ∧
      ¬ ConditionM (Kernel.deterministic (id : Bool → Bool) measurable_id) := by
  refine ⟨ex_11_4a, ?_⟩
  rintro ⟨N, ε, -, hε, hM⟩
  rcases hM {false} (measurableSet_singleton _) with h | h
  · have := h true
    rw [kpow_deterministic, measureReal_def, Measure.dirac_apply' _ (measurableSet_singleton _)]
      at this
    simp at this; linarith
  · have := h false
    rw [kpow_deterministic, measureReal_def,
      Measure.dirac_apply' _ (measurableSet_singleton _).compl] at this
    simp at this; linarith

end StokeyLucasPrescott.StrongConvergence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Ergodic sets under Doeblin's condition

SLP §11.4, pp. 346–348: Theorem 11.9a and Theorem 11.10a.

* `IsConsequentSet κ s E`: `Pⁿ(s, E) = 1` for all `n ≥ 1`.
* `IsInvariantSet κ E`: `E` is a consequent set of each of its points. The book's definition
  allows `E = ∅`, which would make every nonempty set fail to be ergodic (`∅` is an invariant
  subset of smaller measure); invariant sets are required to be nonempty here.
* `IsErgodicSetD κ φ E`: an invariant set with no invariant subset of smaller `φ`-measure.

Results:

* `invariant_real_gt`: under Condition D for `(φ, N, ε)`, every invariant set has `φ(E) > ε`.
* `invariant_of_consequent` (the book's `E′ = ∩ₙ (E − Fₙ)`): a consequent set of `s₀` contains a
  consequent set of `s₀` that is invariant.
* `exists_ergodic_subset_of_invariant`: every invariant set contains an ergodic set. **The book's
  argument has a gap**: the intersection of a strictly decreasing sequence of invariant sets is
  invariant but need not be ergodic. Here, take an invariant `G₁` with `φ(G₁)` within `ε/2` of
  the infimum `m` of `φ` over invariant subsets; two invariant subsets of `G₁` with measure
  below `m + ε/2` must meet, since otherwise `2m < m + ε/2`. So the intersections of a
  minimizing sequence remain invariant, and their intersection attains `m`.
* **Theorem 11.9a** (`theorem_11_9a`): every consequent set contains an ergodic set; two ergodic
  sets are disjoint or agree up to `φ`-null sets; there are `M` pairwise disjoint ergodic sets
  with `1 ≤ M` and `Mε < φ(S)`, and every ergodic set agrees with one of them up to a `φ`-null
  set. The transient set is the complement of their union.
* **Theorem 11.10a** (`theorem_11_10a`): if moreover every set of positive `φ`-measure is
  reached from every state, any two ergodic sets agree up to `φ`-null sets.
-/

namespace StokeyLucasPrescott.StrongConvergence

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {S : Type*} [MeasurableSpace S] {κ : Kernel S S} [IsMarkovKernel κ]

/-- `E` is a **consequent set** of `s` (p. 346). -/
def IsConsequentSet (κ : Kernel S S) (s : S) (E : Set S) : Prop :=
  MeasurableSet E ∧ ∀ n, 1 ≤ n → kpow κ n s E = 1

/-- `E` is **invariant** (p. 346): nonempty, and a consequent set of each of its points. -/
def IsInvariantSet (κ : Kernel S S) (E : Set S) : Prop :=
  MeasurableSet E ∧ E.Nonempty ∧ ∀ s ∈ E, ∀ n, 1 ≤ n → kpow κ n s E = 1

/-- `E` is **ergodic** (p. 346): invariant, with no invariant subset of smaller `φ`-measure. -/
def IsErgodicSetD (κ : Kernel S S) (φ : Measure S) (E : Set S) : Prop :=
  IsInvariantSet κ E ∧ ∀ F ⊆ E, IsInvariantSet κ F → φ E ≤ φ F

/-- Two sets of full measure meet in a set of full measure. -/
theorem measure_inter_eq_one {μ : Measure S} [IsProbabilityMeasure μ] {E F : Set S}
    (hE : MeasurableSet E) (hF : MeasurableSet F) (h1 : μ E = 1) (h2 : μ F = 1) :
    μ (E ∩ F) = 1 := by
  rw [← prob_compl_eq_zero_iff (hE.inter hF), compl_inter]
  rw [← prob_compl_eq_zero_iff hE] at h1
  rw [← prob_compl_eq_zero_iff hF] at h2
  exact measure_union_null h1 h2

/-- Countably many sets of full measure meet in a set of full measure. -/
theorem measure_iInter_eq_one {μ : Measure S} [IsProbabilityMeasure μ] {K : ℕ → Set S}
    (hK : ∀ k, MeasurableSet (K k)) (h1 : ∀ k, μ (K k) = 1) : μ (⋂ k, K k) = 1 := by
  rw [← prob_compl_eq_zero_iff (MeasurableSet.iInter hK), compl_iInter]
  exact measure_iUnion_null fun k => (prob_compl_eq_zero_iff (hK k)).2 (h1 k)

theorem IsInvariantSet.inter {E F : Set S} (hE : IsInvariantSet κ E) (hF : IsInvariantSet κ F)
    (hne : (E ∩ F).Nonempty) : IsInvariantSet κ (E ∩ F) := by
  refine ⟨hE.1.inter hF.1, hne, fun s hs n hn => ?_⟩
  have := isMarkov_kpow (κ := κ) n
  exact measure_inter_eq_one hE.1 hF.1 (hE.2.2 s hs.1 n hn) (hF.2.2 s hs.2 n hn)

theorem isInvariantSet_iInter {K : ℕ → Set S} (hK : ∀ k, IsInvariantSet κ (K k))
    (hne : (⋂ k, K k).Nonempty) : IsInvariantSet κ (⋂ k, K k) := by
  refine ⟨MeasurableSet.iInter fun k => (hK k).1, hne, fun s hs n hn => ?_⟩
  have := isMarkov_kpow (κ := κ) n
  exact measure_iInter_eq_one (fun k => (hK k).1)
    fun k => (hK k).2.2 s (mem_iInter.1 hs k) n hn

omit [IsMarkovKernel κ] in
/-- Under Condition D a consequent set has `φ`-measure greater than `ε` (p. 346, "Why?"). -/
theorem consequent_real_gt {φ : Measure S} {N : ℕ} {ε : ℝ} (hD : DoeblinFor κ φ N ε) {s : S}
    {E : Set S} (hE : IsConsequentSet κ s E) : ε < φ.real E := by
  by_contra hle
  have := hD.2.2.2 E hE.1 (not_lt.1 hle) s
  rw [measureReal_def, hE.2 N hD.2.1, ENNReal.toReal_one] at this
  linarith [hD.2.2.1]

omit [IsMarkovKernel κ] in
theorem invariant_real_gt {φ : Measure S} {N : ℕ} {ε : ℝ} (hD : DoeblinFor κ φ N ε)
    {E : Set S} (hE : IsInvariantSet κ E) : ε < φ.real E := by
  obtain ⟨s, hs⟩ := hE.2.1
  exact consequent_real_gt hD ⟨hE.1, hE.2.2 s hs⟩

/-- If `f ≤ 1` and `∫ f dμ = 1` for a probability measure `μ`, then `f = 1` `μ`-a.e. -/
theorem measure_eq_one_of_lintegral {μ : Measure S} [IsProbabilityMeasure μ] {f : S → ℝ≥0∞}
    (hf : Measurable f) (h1 : ∀ x, f x ≤ 1) (hint : ∫⁻ x, f x ∂μ = 1) :
    μ {x | f x = 1} = 1 := by
  have hsub : ∫⁻ x, (1 - f x) ∂μ = 0 := by
    rw [lintegral_sub hf (by rw [hint]; exact ENNReal.one_ne_top)
      (Eventually.of_forall h1), lintegral_const, measure_univ, mul_one, hint, tsub_self]
  have hsub' := (lintegral_eq_zero_iff (f := fun x => 1 - f x) (measurable_const.sub hf)).1 hsub
  have hae : ∀ᵐ x ∂μ, f x = 1 := hsub'.mono fun x hx => by
    simp only [Pi.zero_apply] at hx
    exact le_antisymm (h1 x) (tsub_eq_zero_iff_le.1 hx)
  rw [← prob_compl_eq_zero_iff (measurableSet_eq_fun hf measurable_const)]
  exact ae_iff.1 hae

/-- The book's `E′ = E ∩ ⋂ₙ {s : Pⁿ(s, E) = 1}`. -/
def consCore (κ : Kernel S S) (E : Set S) : Set S :=
  E ∩ ⋂ n : ℕ, {s | kpow κ (n + 1) s E = 1}

omit [IsMarkovKernel κ] in
theorem measurableSet_consCore {E : Set S} (hE : MeasurableSet E) :
    MeasurableSet (consCore κ E) :=
  hE.inter (MeasurableSet.iInter fun n =>
    Kernel.measurable_coe (kpow κ (n + 1)) hE (measurableSet_singleton 1))

/-- If `E` is a consequent set of `s`, so is `E′`. -/
theorem IsConsequentSet.consCore {s : S} {E : Set S} (hE : IsConsequentSet κ s E) :
    IsConsequentSet κ s (consCore κ E) := by
  refine ⟨measurableSet_consCore hE.1, fun m hm => ?_⟩
  have := isMarkov_kpow (κ := κ) m
  refine measure_inter_eq_one hE.1 (MeasurableSet.iInter fun n =>
    Kernel.measurable_coe (kpow κ (n + 1)) hE.1 (measurableSet_singleton 1)) (hE.2 m hm)
    (measure_iInter_eq_one (fun n => Kernel.measurable_coe (kpow κ (n + 1)) hE.1
      (measurableSet_singleton 1)) fun n => ?_)
  have := isMarkov_kpow (κ := κ) (n + 1)
  refine measure_eq_one_of_lintegral (Kernel.measurable_coe _ hE.1) (fun x => prob_le_one) ?_
  rw [← kpow_add_apply m (n + 1) s hE.1]
  exact hE.2 _ (by omega)

/-- A consequent set `E` of `s₀` contains the invariant consequent set `E′` (p. 347). -/
theorem invariant_of_consequent {s₀ : S} {E : Set S} (hE : IsConsequentSet κ s₀ E) :
    IsInvariantSet κ (consCore κ E) ∧ IsConsequentSet κ s₀ (consCore κ E) ∧
      consCore κ E ⊆ E := by
  have hc := hE.consCore
  refine ⟨⟨hc.1, ?_, fun s hs n hn => ?_⟩, hc, inter_subset_left⟩
  · by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have := hc.2 1 le_rfl
    rw [hne, measure_empty] at this
    exact zero_ne_one this
  · have hsE : IsConsequentSet κ s E := ⟨hE.1, fun m hm => by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact mem_iInter.1 hs.2 k⟩
    exact hsE.consCore.2 n hn

omit [MeasurableSpace S] [IsMarkovKernel κ] in
theorem iInter_le_succ (H : ℕ → Set S) (k : ℕ) :
    (⋂ j, ⋂ (_ : j ≤ k + 1), H j) = (⋂ j, ⋂ (_ : j ≤ k), H j) ∩ H (k + 1) := by
  ext x
  simp only [mem_iInter, mem_inter_iff]
  constructor
  · intro h; exact ⟨fun j hj => h j (by omega), h (k + 1) le_rfl⟩
  · rintro ⟨h, h'⟩ j hj
    rcases Nat.lt_or_ge j (k + 1) with hlt | hge
    · exact h j (by omega)
    · rwa [show j = k + 1 by omega]

/-- Every invariant set contains an ergodic set. (Corrected argument; see the module
docstring.) -/
theorem exists_ergodic_subset_of_invariant {φ : Measure S} {N : ℕ} {ε : ℝ}
    (hD : DoeblinFor κ φ N ε) {G : Set S} (hG : IsInvariantSet κ G) :
    ∃ E ⊆ G, IsErgodicSetD κ φ E := by
  have hφ := hD.1
  have hε := hD.2.2.1
  set Inv : Set S → Set (Set S) := fun G => {F | F ⊆ G ∧ IsInvariantSet κ F}
  set val : Set S → Set ℝ := fun G => (fun F => φ.real F) '' Inv G
  have hbdd : ∀ G, BddBelow (val G) := fun G =>
    ⟨ε, by rintro _ ⟨F, hF, rfl⟩; exact (invariant_real_gt hD hF.2).le⟩
  have hval_ge : ∀ G, (val G).Nonempty → ε ≤ sInf (val G) := fun G hne =>
    le_csInf hne (by rintro _ ⟨F, hF, rfl⟩; exact (invariant_real_gt hD hF.2).le)
  -- `G₁`: an invariant subset of `G` within `ε/2` of the infimum `m`
  set m := sInf (val G)
  have hne : (val G).Nonempty := ⟨_, G, ⟨subset_rfl, hG⟩, rfl⟩
  obtain ⟨_, ⟨G₁, hG₁, rfl⟩, hG₁lt⟩ :=
    exists_lt_of_csInf_lt hne (show m < m + ε / 2 by linarith)
  have hmle : ∀ F ∈ Inv G, m ≤ φ.real F := fun F hF => csInf_le (hbdd G) ⟨F, hF, rfl⟩
  have hεm := hval_ge G hne
  -- any two invariant subsets of `G₁` meet
  have hInvInter : ∀ F ∈ Inv G₁, ∀ F' ∈ Inv G₁, F ∩ F' ∈ Inv G₁ := by
    intro F hF F' hF'
    have hmeet : (F ∩ F').Nonempty := by
      by_contra hdis
      rw [not_nonempty_iff_eq_empty] at hdis
      have hd : Disjoint F F' := Set.disjoint_iff_inter_eq_empty.2 hdis
      have h1 := measureReal_union hd hF'.2.1 (measure_ne_top φ F) (measure_ne_top φ F')
      have h2 : φ.real (F ∪ F') ≤ φ.real G₁ := measureReal_mono (union_subset hF.1 hF'.1)
      have h3 := hmle F ⟨hF.1.trans hG₁.1, hF.2⟩
      have h4 := hmle F' ⟨hF'.1.trans hG₁.1, hF'.2⟩
      linarith
    exact ⟨inter_subset_left.trans hF.1, hF.2.inter hF'.2 hmeet⟩
  -- a minimizing sequence of invariant subsets of `G₁`
  set m' := sInf (val G₁)
  have hne₁ : (val G₁).Nonempty := ⟨_, G₁, ⟨subset_rfl, hG₁.2⟩, rfl⟩
  have hm'le : ∀ F ∈ Inv G₁, m' ≤ φ.real F := fun F hF => csInf_le (hbdd G₁) ⟨F, hF, rfl⟩
  have hεm' := hval_ge G₁ hne₁
  have hseq : ∀ k : ℕ, ∃ F ∈ Inv G₁, φ.real F < m' + 1 / (k + 1) := fun k => by
    obtain ⟨_, ⟨F, hF, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne₁
      (show m' < m' + 1 / (k + 1) by have : (0 : ℝ) < 1 / (k + 1) := by positivity
                                     linarith)
    exact ⟨F, hF, hlt⟩
  choose H hH hHlt using hseq
  set Kseq : ℕ → Set S := fun k => ⋂ j, ⋂ (_ : j ≤ k), H j
  have hK : ∀ k, Kseq k ∈ Inv G₁ := by
    intro k
    induction k with
    | zero =>
      have : Kseq 0 = H 0 := by
        ext x; simp only [Kseq, mem_iInter, Nat.le_zero]
        exact ⟨fun h => h 0 rfl, fun h j hj => hj ▸ h⟩
      rw [this]; exact hH 0
    | succ k ih =>
      have : Kseq (k + 1) = Kseq k ∩ H (k + 1) := iInter_le_succ H k
      rw [this]; exact hInvInter _ ih _ (hH (k + 1))
  set K := ⋂ k, Kseq k
  have hanti : Antitone Kseq := fun a b hab => by
    intro x hx
    simp only [Kseq, mem_iInter] at hx ⊢
    exact fun j hj => hx j (hj.trans hab)
  have hlim : Tendsto (fun k => φ.real (Kseq k)) atTop (𝓝 (φ.real K)) := by
    have := tendsto_measure_iInter_atTop (μ := φ) (fun k => (hK k).2.1.nullMeasurableSet)
      hanti ⟨0, measure_ne_top _ _⟩
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp this
  have hKge : m' ≤ φ.real K := ge_of_tendsto hlim (Eventually.of_forall fun k => hm'le _ (hK k))
  have hKne : K.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, measureReal_empty] at hKge
    linarith
  have hKinv : K ∈ Inv G₁ :=
    ⟨(iInter_subset Kseq 0).trans (hK 0).1, isInvariantSet_iInter (fun k => (hK k).2) hKne⟩
  have hKH : ∀ k, K ⊆ H k := fun k =>
    (iInter_subset Kseq k).trans (biInter_subset_of_mem (show k ≤ k from le_rfl))
  have hKle : φ.real K ≤ m' := by
    by_contra hgt
    push Not at hgt
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hgt)
    have := (measureReal_mono (μ := φ) (hKH k)).trans_lt (hHlt k)
    linarith
  refine ⟨K, hKinv.1.trans hG₁.1, hKinv.2, fun F hFK hF => ?_⟩
  have := hm'le F ⟨hFK.trans hKinv.1, hF⟩
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).1
    (hKle.trans this)

/-- Two ergodic sets are disjoint or agree up to `φ`-null sets (p. 347). -/
theorem ergodic_disjoint_or_eq {φ : Measure S} {E E' : Set S} (hE : IsErgodicSetD κ φ E)
    (hE' : IsErgodicSetD κ φ E') :
    Disjoint E E' ∨ (φ (E ∩ E') = φ E ∧ φ (E ∩ E') = φ E') := by
  by_cases hd : Disjoint E E'
  · exact Or.inl hd
  · have hne : (E ∩ E').Nonempty := Set.not_disjoint_iff_nonempty_inter.1 hd
    have hinv := hE.1.inter hE'.1 hne
    exact Or.inr ⟨le_antisymm (measure_mono inter_subset_left) (hE.2 _ inter_subset_left hinv),
      le_antisymm (measure_mono inter_subset_right) (hE'.2 _ inter_subset_right hinv)⟩

omit [IsMarkovKernel κ] in
/-- `M` pairwise disjoint ergodic sets have `Mε < φ(S)`. -/
theorem card_mul_lt {φ : Measure S} {N : ℕ} {ε : ℝ} (hD : DoeblinFor κ φ N ε) {M : ℕ}
    {E : Fin M → Set S} (hE : ∀ m, IsErgodicSetD κ φ (E m))
    (hd : Pairwise (Function.onFun Disjoint E)) (hM : 1 ≤ M) : M * ε < φ.real univ := by
  have hφ := hD.1
  have hsum : φ.real (⋃ m, E m) = ∑ m, φ.real (E m) :=
    measureReal_iUnion_fintype hd (fun m => (hE m).1.1) (fun m => measure_ne_top _ _)
  have hlt : (M : ℝ) * ε < ∑ m, φ.real (E m) := by
    calc (M : ℝ) * ε = ∑ _m : Fin M, ε := by simp
      _ < _ := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.2 ⟨⟨0, hM⟩⟩)
          fun m _ => invariant_real_gt hD (hE m).1
  have := measureReal_mono (μ := φ) (subset_univ (⋃ m, E m))
  linarith

/-- **Theorem 11.9a.** Under Condition D for `(φ, N, ε)`: (i) every consequent set contains an
ergodic set; (ii) two ergodic sets are disjoint or agree up to `φ`-null sets; (iii) `M`
pairwise disjoint ergodic sets have `Mε < φ(S)`; and (iv) there are `M ≥ 1` pairwise disjoint
ergodic sets such that every ergodic set agrees with one of them up to a `φ`-null set. Their
union's complement is the transient set. -/
theorem theorem_11_9a [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ} (hD : DoeblinFor κ φ N ε) :
    (∀ s E, IsConsequentSet κ s E → ∃ F ⊆ E, IsErgodicSetD κ φ F) ∧
      (∀ E E', IsErgodicSetD κ φ E → IsErgodicSetD κ φ E' →
        Disjoint E E' ∨ (φ (E ∩ E') = φ E ∧ φ (E ∩ E') = φ E')) ∧
      (∀ (M : ℕ) (E : Fin M → Set S), (∀ m, IsErgodicSetD κ φ (E m)) →
        Pairwise (Function.onFun Disjoint E) → 1 ≤ M → M * ε < φ.real univ) ∧
      ∃ M : ℕ, 1 ≤ M ∧ M * ε < φ.real univ ∧ ∃ E : Fin M → Set S, (∀ m, IsErgodicSetD κ φ (E m)) ∧
        Pairwise (Function.onFun Disjoint E) ∧
        ∀ F, IsErgodicSetD κ φ F → ∃ m, φ (F ∩ E m) = φ F ∧ φ (F ∩ E m) = φ (E m) := by
  classical
  have hφ := hD.1
  have hε := hD.2.2.1
  have hcontains : ∀ s E, IsConsequentSet κ s E → ∃ F ⊆ E, IsErgodicSetD κ φ F := by
    intro s E hE
    obtain ⟨hinv, -, hsub⟩ := invariant_of_consequent hE
    obtain ⟨F, hF, hFe⟩ := exists_ergodic_subset_of_invariant hD hinv
    exact ⟨F, hF.trans hsub, hFe⟩
  refine ⟨hcontains, fun E E' => ergodic_disjoint_or_eq,
    fun M E hE hd hM => card_mul_lt hD hE hd hM, ?_⟩
  -- a maximal family of disjoint ergodic sets
  set P : ℕ → Prop := fun M => ∃ E : Fin M → Set S, (∀ m, IsErgodicSetD κ φ (E m)) ∧
    Pairwise (Function.onFun Disjoint E)
  obtain ⟨s₀⟩ := ‹Nonempty S›
  have huniv : IsInvariantSet κ univ := ⟨MeasurableSet.univ, univ_nonempty, fun s _ n _ => by
    have := isMarkov_kpow (κ := κ) n; exact measure_univ⟩
  obtain ⟨E₀, -, hE₀⟩ := exists_ergodic_subset_of_invariant hD huniv
  have hP1 : P 1 := ⟨fun _ => E₀, fun _ => hE₀, fun i j hij => absurd (Subsingleton.elim i j) hij⟩
  obtain ⟨B, hB⟩ := exists_nat_gt (φ.real univ / ε)
  have hPle : ∀ M, P M → M ≤ B := by
    intro M ⟨E, hE, hd⟩
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · exact Nat.zero_le _
    · have := card_mul_lt hD hE hd hM
      rw [div_lt_iff₀ hε] at hB
      exact_mod_cast (show (M : ℝ) ≤ B by nlinarith)
  set M₀ := Nat.findGreatest P B
  have hPM₀ : P M₀ := Nat.findGreatest_spec (hPle 1 hP1) hP1
  have hM₀ : 1 ≤ M₀ := Nat.le_findGreatest (hPle 1 hP1) hP1
  obtain ⟨E, hE, hd⟩ := hPM₀
  refine ⟨M₀, hM₀, card_mul_lt hD hE hd hM₀, E, hE, hd, fun F hF => ?_⟩
  by_contra hno
  push Not at hno
  -- `F` is disjoint from every `E m`, so the family extends
  have hdisj : ∀ m, Disjoint F (E m) := fun m =>
    ((ergodic_disjoint_or_eq hF (hE m)).resolve_right fun ⟨h1, h2⟩ => hno m h1 h2)
  have hP' : P (M₀ + 1) := by
    refine ⟨Fin.snoc E F, fun m => ?_, fun i j hij => ?_⟩
    · refine Fin.lastCases ?_ (fun i => ?_) m
      · simpa using hF
      · simpa using hE i
    · induction i using Fin.lastCases with
      | last => induction j using Fin.lastCases with
        | last => exact absurd rfl hij
        | cast j => simpa [Function.onFun] using hdisj j
      | cast i => induction j using Fin.lastCases with
        | last => simpa [Function.onFun] using (hdisj i).symm
        | cast j =>
          simpa [Function.onFun] using hd (fun h => hij (by rw [h]))
  have := Nat.le_findGreatest (hPle _ hP') hP'
  omega

/-- **Theorem 11.10a.** If in addition every set of positive `φ`-measure is reached from every
state, any two ergodic sets agree up to `φ`-null sets: there is only one ergodic set. -/
theorem theorem_11_10a {φ : Measure S} {N : ℕ} {ε : ℝ} (hD : DoeblinFor κ φ N ε)
    (hirr : ∀ A, MeasurableSet A → 0 < φ A → ∀ s, ∃ n, 1 ≤ n ∧ 0 < kpow κ n s A)
    {E E' : Set S} (hE : IsErgodicSetD κ φ E) (hE' : IsErgodicSetD κ φ E') :
    φ (E ∩ E') = φ E ∧ φ (E ∩ E') = φ E' := by
  refine (ergodic_disjoint_or_eq hE hE').resolve_left fun hd => ?_
  have hpos : 0 < φ E' := by
    have := invariant_real_gt hD hE'.1
    exact ENNReal.toReal_pos_iff.1 (lt_trans hD.2.2.1 this) |>.1
  obtain ⟨s, hs⟩ := hE.1.2.1
  obtain ⟨n, hn, hpos'⟩ := hirr E' hE'.1.1 hpos s
  have := isMarkov_kpow (κ := κ) n
  have h1 : kpow κ n s E = 1 := hE.1.2.2 s hs n hn
  have hle : kpow κ n s E' ≤ kpow κ n s Eᶜ := measure_mono hd.subset_compl_left
  rw [prob_compl_eq_one_sub hE.1.1, h1, tsub_self] at hle
  exact (lt_of_lt_of_le hpos' hle).false

end StokeyLucasPrescott.StrongConvergence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Markov chains on a countable set: Examples 6 and 7

SLP §11.1, pp. 333–334. On `S = ℕ`:

* **Example 6** (`ex6`): the identity. Every `{sᵢ}` is an invariant set and every `δᵢ` an
  invariant distribution, so there are infinitely many of each.
* **Example 7** (`ex7`): the shift `sᵢ ↦ sᵢ₊₁`. Every state is transient (it is never revisited),
  `Πᵏ → 0` entrywise, and there is no invariant probability measure: "all of the probability
  wanders off to infinity".
-/

namespace StokeyLucasPrescott.StrongConvergence

open MeasureTheory ProbabilityTheory Set Filter Topology

/-- **Example 6.** For the identity on `ℕ`, each `{i}` is an invariant set and each `δᵢ` an
invariant distribution; these are pairwise distinct. -/
theorem ex6 :
    (∀ i, IsInvariantSet (Kernel.deterministic (id : ℕ → ℕ) measurable_id) {i}) ∧
      (∀ i, adjointOp (Kernel.deterministic (id : ℕ → ℕ) measurable_id) (Measure.dirac i) =
        Measure.dirac i) ∧
      Function.Injective fun i : ℕ => Measure.dirac i := by
  refine ⟨fun i => ⟨measurableSet_singleton i, singleton_nonempty i, fun s hs n _ => ?_⟩,
    fun i => ?_, fun i j h => ?_⟩
  · rw [mem_singleton_iff] at hs
    subst hs
    rw [kpow_deterministic, Function.iterate_id, id, Measure.dirac_apply_of_mem (mem_singleton s)]
  · rw [adjointOp, Measure.dirac_bind (Kernel.measurable _), Kernel.deterministic_apply, id]
  · have := congrArg (fun μ : Measure ℕ => μ {i}) h
    simp only [Measure.dirac_apply_of_mem (mem_singleton i)] at this
    by_contra hij
    rw [Measure.dirac_apply' _ (measurableSet_singleton i), indicator_of_notMem
      (show j ∉ ({i} : Set ℕ) from fun h' => hij (mem_singleton_iff.1 h').symm)] at this
    exact one_ne_zero this

/-- **Example 7.** For the shift on `ℕ`: no state is ever revisited, so every state is transient;
`Πᵏ → 0` entrywise; and there is no invariant probability measure. -/
theorem ex7 :
    (∀ i n, 1 ≤ n → kpow (Kernel.deterministic Nat.succ measurable_from_top) n i {i} = 0) ∧
      (∀ i j, Tendsto (fun k =>
        (kpow (Kernel.deterministic Nat.succ measurable_from_top) k i).real {j}) atTop (𝓝 0)) ∧
      ∀ μ : Measure ℕ, IsProbabilityMeasure μ →
        adjointOp (Kernel.deterministic Nat.succ measurable_from_top) μ ≠ μ := by
  have hk : ∀ k i, kpow (Kernel.deterministic Nat.succ measurable_from_top) k i =
      Measure.dirac (i + k) := fun k i => by
    rw [kpow_deterministic, Nat.succ_iterate]
  refine ⟨fun i n hn => ?_, fun i j => ?_, fun μ hμ h => ?_⟩
  · rw [hk, Measure.dirac_apply' _ (measurableSet_singleton i), indicator_of_notMem]
    simp; omega
  · refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨j + 1, fun k hk' => ?_⟩)
    dsimp only
    rw [hk, measureReal_def, Measure.dirac_apply' _ (measurableSet_singleton j),
      indicator_of_notMem (by simp; omega)]
    rfl
  · -- `μ = μ ∘ succ⁻¹` forces `μ{n} = 0` for all `n`
    have hmap : ∀ A, MeasurableSet A → μ (Nat.succ ⁻¹' A) = μ A := fun A hA => by
      have := congrArg (fun ν : Measure ℕ => ν A) h
      simp only [adjointOp] at this
      rw [Measure.bind_apply hA (Kernel.aemeasurable _)] at this
      rw [← this]
      simp only [Kernel.deterministic_apply]
      rw [← lintegral_indicator_one (measurable_from_top (f := Nat.succ) hA)]
      refine lintegral_congr fun n => ?_
      rw [Measure.dirac_apply' _ hA]
      by_cases hn : n + 1 ∈ A
      · rw [indicator_of_mem (show n ∈ Nat.succ ⁻¹' A from hn), indicator_of_mem hn]; rfl
      · rw [indicator_of_notMem (show n ∉ Nat.succ ⁻¹' A from hn), indicator_of_notMem hn]
    have h0 : ∀ n, μ {n} = 0 := by
      intro n
      induction n with
      | zero =>
        rw [← hmap _ (measurableSet_singleton 0)]
        have : Nat.succ ⁻¹' ({0} : Set ℕ) = ∅ := by ext m; simp
        rw [this, measure_empty]
      | succ n ih =>
        rw [← hmap _ (measurableSet_singleton _)]
        have : Nat.succ ⁻¹' ({n + 1} : Set ℕ) = {n} := by ext m; simp
        rw [this, ih]
    have : μ univ = 0 := by
      rw [← iUnion_of_singleton (α := ℕ)]
      exact measure_iUnion_null h0
    rw [measure_univ] at this
    exact one_ne_zero this

end StokeyLucasPrescott.StrongConvergence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Condition M and geometric convergence

SLP §11.4, Lemma 11.11 and Theorem 11.12, pp. 349–351. `T*ⁿλ = adjointOp (kpow κ n) λ`.

* `tvDist_comm`, `tvDist_triangle`, `eq_of_tvDist_eq_zero`: the total variation distance is a
  metric on probability measures.
* **Lemma 11.11** (`lemma_11_11`): under Condition M for `(N, ε)`, `T*ᴺ` is a contraction of
  modulus `1 − ε` in the total variation norm. With a Hahn set `B`, write `λᵢ = αᵢ + γ`, with
  `α₁ = λ₁|_B − λ₂|_B` and `α₂ = λ₂|_{Bᶜ} − λ₁|_{Bᶜ}` of equal mass `c`, so
  `‖λ₁ − λ₂‖ ≥ 2c`. Then `(T*ᴺλ₁)(A) − (T*ᴺλ₂)(A) = ∫ Pᴺ(·, A) dα₁ − ∫ Pᴺ(·, A) dα₂`. If
  `Pᴺ(·, A) ≥ ε`, both integrals lie in `[εc, c]`; otherwise the same holds for `Aᶜ`. The book
  applies Lemma 11.5 to `T*ᴺαᵢ`, which are not probability measures; this proof avoids that.
* **Theorem 11.12** (`theorem_11_12`): under Condition M there is a unique `λ*` with
  `‖T*^{Nk}λ₀ − λ*‖ ≤ (1 − ε)ᵏ‖λ₀ − λ*‖` for all `λ₀`. It is the unique invariant probability
  measure, and `‖T*ⁿλ₀ − λ*‖ ≤ 2(1 − ε)^⌊n/N⌋`. These two facts the book leaves implicit.
  Conversely (`theorem_11_12_converse`), this bound implies Condition M for `(NK, 1/4)`.
  The fixed point is found by the contraction argument, using Lemma 11.8 for completeness.
-/

namespace StokeyLucasPrescott.StrongConvergence

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {S : Type*} [MeasurableSpace S]

theorem tvDist_comm (μ₁ μ₂ : Measure S) : tvDist μ₁ μ₂ = tvDist μ₂ μ₁ := by
  unfold tvDist tvOf partSums
  congr 1
  ext x
  refine exists_congr fun k => exists_congr fun A => and_congr_right fun _ => ?_
  simp only [abs_sub_comm]

theorem tvDist_triangle (μ₁ μ₂ μ₃ : Measure S) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    [IsFiniteMeasure μ₃] : tvDist μ₁ μ₃ ≤ tvDist μ₁ μ₂ + tvDist μ₂ μ₃ := by
  refine csSup_le (partSums_nonempty _) ?_
  rintro _ ⟨k, A, hA, rfl⟩
  calc ∑ i, |μ₁.real (A i) - μ₃.real (A i)|
      ≤ ∑ i, |μ₁.real (A i) - μ₂.real (A i)| + ∑ i, |μ₂.real (A i) - μ₃.real (A i)| := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun i _ => abs_sub_le _ _ _
    _ ≤ tvDist μ₁ μ₂ + tvDist μ₂ μ₃ :=
        add_le_add (le_csSup (bddAbove_tvDist μ₁ μ₂) ⟨k, A, hA, rfl⟩)
          (le_csSup (bddAbove_tvDist μ₂ μ₃) ⟨k, A, hA, rfl⟩)

theorem tvDist_le_two (μ₁ μ₂ : Measure S) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] :
    tvDist μ₁ μ₂ ≤ 2 := by
  refine csSup_le (partSums_nonempty _) ?_
  rintro _ ⟨k, A, hA, rfl⟩
  have := partSums_le_of_measures μ₁ μ₂ hA
  simp only [probReal_univ] at this
  linarith

theorem eq_of_tvDist_eq_zero {μ₁ μ₂ : Measure S} [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (h : tvDist μ₁ μ₂ ≤ 0) : μ₁ = μ₂ := by
  ext A hA
  have := two_abs_le_tvDist μ₁ μ₂ hA
  have h0 : μ₁.real A = μ₂.real A := by
    have := abs_nonneg (μ₁.real A - μ₂.real A)
    have : |μ₁.real A - μ₂.real A| = 0 := by linarith
    linarith [abs_eq_zero.1 this]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h0

/-- `(λ ⊗ P)(A) = ∫ P(s, A) λ(ds)` in real terms, for finite `λ`. -/
theorem bind_real_eq (κ : Kernel S S) [IsMarkovKernel κ] (μ : Measure S) [IsFiniteMeasure μ]
    {A : Set S} (hA : MeasurableSet A) :
    (adjointOp κ μ).real A = ∫ s, (κ s).real A ∂μ := by
  rw [measureReal_def, adjointOp_apply κ μ hA]
  exact (integral_toReal (κ.measurable_coe hA).aemeasurable
    (Eventually.of_forall fun s => measure_lt_top _ _)).symm

/-- **Lemma 11.11.** Under Condition M for `(N, ε)`, `T*ᴺ` is a contraction of modulus `1 − ε`:
`‖T*ᴺλ₁ − T*ᴺλ₂‖ ≤ (1 − ε)‖λ₁ − λ₂‖`. -/
theorem lemma_11_11 {κ : Kernel S S} [IsMarkovKernel κ] {N : ℕ} {ε : ℝ}
    (hM : ConditionMFor κ N ε) (μ₁ μ₂ : Measure S) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] :
    tvDist (adjointOp (kpow κ N) μ₁) (adjointOp (kpow κ N) μ₂) ≤ (1 - ε) * tvDist μ₁ μ₂ := by
  obtain ⟨-, hε, hMA⟩ := hM
  set P := kpow κ N
  have hP : IsMarkovKernel P := isMarkov_kpow N
  have : IsProbabilityMeasure (adjointOp P μ₁) := (theorem_8_2 P μ₁).1
  have : IsProbabilityMeasure (adjointOp P μ₂) := (theorem_8_2 P μ₂).1
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
    have := abs_add_abs_compl_le μ₁ μ₂ hB
    rw [← hm1, show μ₁.real Bᶜ - μ₂.real Bᶜ = -c₂ by rw [hm2]; ring, abs_neg, ← hc,
      abs_of_nonneg hc0] at this
    linarith
  -- integrals of `Pᴺ(·, A)`
  have hint : ∀ (α : Measure S) [IsFiniteMeasure α] (A : Set S), MeasurableSet A →
      Integrable (fun s => (P s).real A) α := fun α _ A hA =>
    integrable_of_abs_le α (P.measurable_coe hA).ennreal_toReal
      fun s => by rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one
  have hsplit : ∀ (μ α : Measure S) [IsFiniteMeasure μ] [IsFiniteMeasure α], μ = α + γ →
      ∀ A, MeasurableSet A → (adjointOp P μ).real A =
        ∫ s, (P s).real A ∂α + ∫ s, (P s).real A ∂γ := by
    intro μ α _ _ hμ A hA
    rw [bind_real_eq P μ hA, hμ, integral_add_measure (hint α A hA) (hint γ A hA)]
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
  have := tvDist_le_of_forall _ _ hA
  nlinarith

variable {κ : Kernel S S} [IsMarkovKernel κ]

theorem isProb_adjoint (n : ℕ) (μ : Measure S) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (adjointOp (kpow κ n) μ) := by
  have := isMarkov_kpow (κ := κ) n
  exact (theorem_8_2 (kpow κ n) μ).1

omit [IsMarkovKernel κ] in
theorem adjoint_add (n m : ℕ) (μ : Measure S) :
    adjointOp (kpow κ (n + m)) μ = adjointOp (kpow κ n) (adjointOp (kpow κ m) μ) :=
  (ex_8_4b κ n m measurable_const μ (f := fun _ => 0)).2

/-- Iterating Lemma 11.11: `‖T*^{Nk}λ₁ − T*^{Nk}λ₂‖ ≤ (1 − ε)ᵏ‖λ₁ − λ₂‖`. -/
theorem tvDist_iterate_le {N : ℕ} {ε : ℝ} (hM : ConditionMFor κ N ε) (μ₁ μ₂ : Measure S)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] (k : ℕ) :
    tvDist (adjointOp (kpow κ (N * k)) μ₁) (adjointOp (kpow κ (N * k)) μ₂) ≤
      (1 - ε) ^ k * tvDist μ₁ μ₂ := by
  have hε1 : ε ≤ 1 := by
    obtain ⟨s⟩ := nonempty_of_isProbabilityMeasure μ₁
    have := isMarkov_kpow (κ := κ) N
    rcases hM.2.2 ∅ MeasurableSet.empty with h | h
    · have := h s; simp at this; linarith [hM.2.1]
    · have := h s; simp at this; linarith
  induction k with
  | zero => simp [kpow, adjointOp]
  | succ k ih =>
    have := isProb_adjoint (κ := κ) (N * k) μ₁
    have := isProb_adjoint (κ := κ) (N * k) μ₂
    rw [show N * (k + 1) = N + N * k by ring, adjoint_add, adjoint_add, pow_succ']
    calc _ ≤ (1 - ε) * tvDist (adjointOp (kpow κ (N * k)) μ₁) (adjointOp (kpow κ (N * k)) μ₂) :=
          lemma_11_11 hM _ _
      _ ≤ (1 - ε) * ((1 - ε) ^ k * tvDist μ₁ μ₂) :=
          mul_le_mul_of_nonneg_left ih (by linarith)
      _ = _ := by ring

/-- **Theorem 11.12.** Under Condition M for `(N, ε)` there is a unique probability measure
`λ*` such that `‖T*^{Nk}λ₀ − λ*‖ ≤ (1 − ε)ᵏ‖λ₀ − λ*‖` for all `λ₀` and `k`; moreover `λ*` is
invariant, `T*λ* = λ*`, and `‖T*ⁿλ₀ − λ*‖ ≤ 2(1 − ε)^⌊n/N⌋` for all `n`. -/
theorem theorem_11_12 [Nonempty S] {N : ℕ} {ε : ℝ} (hM : ConditionMFor κ N ε) :
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
    have := isMarkov_kpow (κ := κ) N
    rcases hMA ∅ MeasurableSet.empty with h | h
    · have := h s₀; simp at this; linarith
    · have := h s₀; simp at this; linarith
  have hr0 : 0 ≤ 1 - ε := by linarith
  have hr1 : 1 - ε < 1 := by linarith
  set T : ℕ → Measure S → Measure S := fun n μ => adjointOp (kpow κ n) μ
  have hTp : ∀ n (μ : Measure S) [IsProbabilityMeasure μ], IsProbabilityMeasure (T n μ) :=
    fun n μ _ => isProb_adjoint n μ
  -- the iterates from `δ_{s₀}`
  set seq : ℕ → Measure S := fun k => T (N * k) (Measure.dirac s₀)
  have hseqp : ∀ k, IsProbabilityMeasure (seq k) := fun k => hTp _ _
  have hstep : ∀ k, tvDist (seq (k + 1)) (seq k) ≤ 2 * (1 - ε) ^ k := by
    intro k
    have h1 : seq (k + 1) = T (N * k) (T N (Measure.dirac s₀)) := by
      simp only [seq, T]; rw [← adjoint_add]; ring_nf
    have : IsProbabilityMeasure (T N (Measure.dirac s₀)) := hTp _ _
    rw [h1]
    calc _ ≤ (1 - ε) ^ k * tvDist (T N (Measure.dirac s₀)) (Measure.dirac s₀) :=
          tvDist_iterate_le ⟨hN, hε, hMA⟩ _ _ k
      _ ≤ (1 - ε) ^ k * 2 := mul_le_mul_of_nonneg_left (tvDist_le_two _ _) (pow_nonneg hr0 k)
      _ = _ := mul_comm _ _
  have hgeom : ∀ m d, tvDist (seq (m + d)) (seq m) ≤ 2 * (1 - ε) ^ m / ε := by
    intro m d
    have hsum : tvDist (seq (m + d)) (seq m) ≤
        2 * ∑ j ∈ Finset.range d, (1 - ε) ^ (m + j) := by
      induction d with
      | zero =>
        simp only [add_zero, Finset.range_zero, Finset.sum_empty, mul_zero]
        exact le_of_eq (by
          refine le_antisymm (csSup_le (partSums_nonempty _) ?_) (tvOf_nonneg
            (bddAbove_tvDist _ _))
          rintro _ ⟨k, A, -, rfl⟩; simp)
      | succ d ih =>
        calc tvDist (seq (m + (d + 1))) (seq m)
            ≤ tvDist (seq (m + d + 1)) (seq (m + d)) + tvDist (seq (m + d)) (seq m) :=
              tvDist_triangle _ _ _
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
      rw [Nat.add_sub_cancel' hnm, tvDist_comm] at this
      exact this.trans_lt ((hmono n hn).trans_lt (hK K le_rfl))
  obtain ⟨lstar, hlp, hconv⟩ := lemma_11_8 seq hcauchy
  -- `λ*` is a fixed point of `T*ᴺ`
  have hfix : T N lstar = lstar := by
    have : IsProbabilityMeasure (T N lstar) := hTp _ _
    have hlimf : Tendsto (fun k => (1 - ε) * tvDist (seq k) lstar + tvDist (seq (k + 1)) lstar)
        atTop (𝓝 0) := by
      have h1 := (hconv.const_mul (1 - ε)).add (hconv.comp (tendsto_add_atTop_nat 1))
      simpa using h1
    refine eq_of_tvDist_eq_zero (ge_of_tendsto' hlimf fun k => ?_)
    · have e : seq (k + 1) = T N (seq k) := by
        simp only [seq, T]; rw [← adjoint_add]; ring_nf
      calc tvDist (T N lstar) lstar
            ≤ tvDist (T N lstar) (seq (k + 1)) + tvDist (seq (k + 1)) lstar :=
            tvDist_triangle _ _ _
        _ ≤ (1 - ε) * tvDist (seq k) lstar + tvDist (seq (k + 1)) lstar := by
            gcongr
            rw [e, tvDist_comm]
            exact lemma_11_11 ⟨hN, hε, hMA⟩ _ _
  have hfixk : ∀ k, T (N * k) lstar = lstar := by
    intro k
    induction k with
    | zero => simp [T, kpow, adjointOp]
    | succ k ih =>
      simp only [T] at ih ⊢
      rw [show N * (k + 1) = N * k + N by ring, adjoint_add,
        show adjointOp (kpow κ N) lstar = lstar from hfix, ih]
  have h1 : ∀ (l₀ : Measure S) [IsProbabilityMeasure l₀] (k : ℕ),
      tvDist (T (N * k) l₀) lstar ≤ (1 - ε) ^ k * tvDist l₀ lstar := by
    intro l₀ _ k
    have := tvDist_iterate_le ⟨hN, hε, hMA⟩ l₀ lstar k
    rwa [show adjointOp (kpow κ (N * k)) lstar = lstar from hfixk k] at this
  refine ⟨lstar, hlp, h1, fun l' hl' hl'1 => ?_, ?_, fun l₀ _ n => ?_⟩
  · -- uniqueness
    refine (eq_of_tvDist_eq_zero ?_).symm
    have hlim : Tendsto (fun k => (1 - ε) ^ k * 2) atTop (𝓝 (0 * 2)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const 2
    rw [zero_mul] at hlim
    refine ge_of_tendsto' hlim fun k => ?_
    have := hl'1 lstar k
    rw [show adjointOp (kpow κ (N * k)) lstar = lstar from hfixk k] at this
    exact this.trans (mul_le_mul_of_nonneg_left (tvDist_le_two _ _) (pow_nonneg hr0 k))
  · -- invariance: `T*λ*` is also a fixed point of the contraction `T*ᴺ`
    have : IsProbabilityMeasure (adjointOp κ lstar) := by
      have := hTp 1 lstar; simpa [T, kpow_one] using this
    have hcomm : T N (adjointOp κ lstar) = adjointOp κ lstar := by
      have e1 : adjointOp κ lstar = T 1 lstar := by simp [T, kpow_one]
      rw [e1]
      simp only [T]
      rw [← adjoint_add, show N + 1 = 1 + N by ring, adjoint_add]
      exact congrArg _ hfix
    have hc := lemma_11_11 ⟨hN, hε, hMA⟩ (adjointOp κ lstar) lstar
    rw [show adjointOp (kpow κ N) (adjointOp κ lstar) = adjointOp κ lstar from hcomm,
      show adjointOp (kpow κ N) lstar = lstar from hfix] at hc
    refine eq_of_tvDist_eq_zero ?_
    nlinarith [tvDist_nonneg (adjointOp κ lstar) lstar]
  · -- the rate for every `n`
    have hsplit : T n l₀ = T (N * (n / N)) (T (n % N) l₀) := by
      simp only [T]; rw [← adjoint_add, Nat.div_add_mod]
    have : IsProbabilityMeasure (T (n % N) l₀) := hTp _ _
    change tvDist (T n l₀) lstar ≤ _
    rw [hsplit]
    calc _ ≤ (1 - ε) ^ (n / N) * tvDist (T (n % N) l₀) lstar := h1 _ _
      _ ≤ (1 - ε) ^ (n / N) * 2 :=
          mul_le_mul_of_nonneg_left (tvDist_le_two _ _) (pow_nonneg hr0 _)
      _ = _ := mul_comm _ _

/-- **Theorem 11.12** (converse). If `‖T*^{Nk}λ₀ − λ*‖ ≤ (1 − ε)ᵏ‖λ₀ − λ*‖` for all `λ₀` and `k`,
with `N ≥ 1` and `0 < ε ≤ 1`, then Condition M holds for `(NK, 1/4)`, where `(1 − ε)ᴷ ≤ 1/4`. -/
theorem theorem_11_12_converse {N : ℕ} {ε : ℝ} (hN : 1 ≤ N)
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
  have := isMarkov_kpow (κ := κ) (N * K)
  -- `|Pᴺᴷ(s, A) − λ*(A)| ≤ 1/4`
  have hclose : ∀ s A, MeasurableSet A → |(kpow κ (N * K) s).real A - lstar.real A| ≤ 1 / 4 := by
    intro s A hA
    have e : adjointOp (kpow κ (N * K)) (Measure.dirac s) = kpow κ (N * K) s :=
      Measure.dirac_bind (Kernel.measurable _) s
    have h1 := h (Measure.dirac s) K
    rw [e] at h1
    have h2 := two_abs_le_tvDist (kpow κ (N * K) s) lstar hA
    have h3 := tvDist_le_two (Measure.dirac s) lstar
    have h4 : (1 - ε) ^ K * tvDist (Measure.dirac s) lstar ≤ 1 / 4 * 2 :=
      mul_le_mul hK h3 (tvDist_nonneg _ _) (by norm_num)
    linarith
  refine ⟨N * K, 1 / 4, hNK, by norm_num, fun A hA => ?_⟩
  rcases le_total (1 / 2) (lstar.real A) with hA2 | hA2
  · exact Or.inl fun s => by have := abs_le.1 (hclose s A hA); linarith
  · refine Or.inr fun s => ?_
    have hc : lstar.real Aᶜ = 1 - lstar.real A := probReal_compl_eq_one_sub hA
    have := abs_le.1 (hclose s Aᶜ hA.compl)
    linarith

end StokeyLucasPrescott.StrongConvergence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Cesàro averages of `T*ⁿλ`

The averages `(1/N) Σ_{n=1}^{N} T*ⁿλ` of Theorem 11.9b (`cesaroM κ n μ`, with `N = n + 1`), and the
property that they are uniformly Cauchy on sets (`CesaroCauchy`), which for probability measures
is Cauchy-ness in the total variation norm (`tvDist_cesaro_le`). The class of measures with this
property is closed under sums and scalar multiples, invariant under `T*` (`cesaroCauchy_adjoint`),
and closed under perturbations of small mass after any number of steps (`cesaroCauchy_of_approx`).
-/

namespace StokeyLucasPrescott.StrongConvergence

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {S : Type*} [MeasurableSpace S]

/-! ### Linearity of `T*` -/

theorem adjointOp_add (η : Kernel S S) (μ ν : Measure S) :
    adjointOp η (μ + ν) = adjointOp η μ + adjointOp η ν := by
  ext A hA
  simp [adjointOp_apply η _ hA, lintegral_add_measure]

theorem adjointOp_smul (η : Kernel S S) (c : ℝ≥0∞) (μ : Measure S) :
    adjointOp η (c • μ) = c • adjointOp η μ := by
  ext A hA
  simp [adjointOp_apply η _ hA, lintegral_smul_measure]

theorem adjointOp_zero (η : Kernel S S) : adjointOp η (0 : Measure S) = 0 := by
  ext A hA; simp [adjointOp_apply η _ hA]

theorem adjointOp_finsetSum (η : Kernel S S) {ι : Type*} (s : Finset ι) (μ : ι → Measure S) :
    adjointOp η (∑ i ∈ s, μ i) = ∑ i ∈ s, adjointOp η (μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [adjointOp_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, adjointOp_add, ih]

theorem adjointOp_mono (η : Kernel S S) {μ ν : Measure S} (h : μ ≤ ν) :
    adjointOp η μ ≤ adjointOp η ν := by
  refine Measure.le_iff.2 fun A hA => ?_
  rw [adjointOp_apply η _ hA, adjointOp_apply η _ hA]
  exact lintegral_mono' h le_rfl

variable {κ : Kernel S S} [IsMarkovKernel κ]

theorem adjointOp_kpow_univ (k : ℕ) (μ : Measure S) :
    adjointOp (kpow κ k) μ univ = μ univ := by
  have := isMarkov_kpow (κ := κ) k
  rw [adjointOp_apply _ _ MeasurableSet.univ]; simp

theorem isFinite_adjoint (k : ℕ) (μ : Measure S) [IsFiniteMeasure μ] :
    IsFiniteMeasure (adjointOp (kpow κ k) μ) :=
  ⟨by rw [adjointOp_kpow_univ]; exact measure_lt_top μ univ⟩

theorem adjoint_real_le (k : ℕ) (μ : Measure S) [IsFiniteMeasure μ] (A : Set S) :
    (adjointOp (kpow κ k) μ).real A ≤ μ.real univ := by
  have := isFinite_adjoint (κ := κ) k μ
  calc (adjointOp (kpow κ k) μ).real A ≤ (adjointOp (kpow κ k) μ).real univ :=
        measureReal_mono (subset_univ A)
    _ = μ.real univ := by rw [measureReal_def, adjointOp_kpow_univ]; rfl

/-! ### Cesàro averages -/

variable (κ) in
/-- The Cesàro average `(1/(n+1)) Σ_{k=1}^{n+1} T*ᵏλ` (Theorem 11.9b, with `N = n + 1`). -/
noncomputable def cesaroM (n : ℕ) (μ : Measure S) : Measure S :=
  ((n : ℝ≥0∞) + 1)⁻¹ • ∑ k ∈ Finset.range (n + 1), adjointOp (kpow κ (k + 1)) μ

omit [IsMarkovKernel κ] in
theorem cesaroM_apply (n : ℕ) (μ : Measure S) (A : Set S) :
    cesaroM κ n μ A =
      ((n : ℝ≥0∞) + 1)⁻¹ * ∑ k ∈ Finset.range (n + 1), adjointOp (kpow κ (k + 1)) μ A := by
  simp [cesaroM, Measure.coe_finsetSum, Finset.sum_apply]

theorem cesaroM_real (n : ℕ) (μ : Measure S) [IsFiniteMeasure μ] (A : Set S) :
    (cesaroM κ n μ).real A =
      ((n : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (n + 1), (adjointOp (kpow κ (k + 1)) μ).real A := by
  rw [measureReal_def, cesaroM_apply, ENNReal.toReal_mul, ENNReal.toReal_sum fun k _ => by
    have := isFinite_adjoint (κ := κ) (k + 1) μ; exact measure_ne_top _ _]
  congr 1
  rw [ENNReal.toReal_inv, ENNReal.toReal_add (ENNReal.natCast_ne_top n) ENNReal.one_ne_top]
  simp

theorem cesaroM_univ (n : ℕ) (μ : Measure S) : cesaroM κ n μ univ = μ univ := by
  rw [cesaroM_apply]
  simp only [adjointOp_kpow_univ, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← mul_assoc, Nat.cast_add, Nat.cast_one,
    ENNReal.inv_mul_cancel (by positivity) (by simp), one_mul]

theorem isFinite_cesaroM (n : ℕ) (μ : Measure S) [IsFiniteMeasure μ] :
    IsFiniteMeasure (cesaroM κ n μ) := ⟨by rw [cesaroM_univ]; exact measure_lt_top μ univ⟩

theorem isProb_cesaroM (n : ℕ) (μ : Measure S) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (cesaroM κ n μ) := ⟨by rw [cesaroM_univ]; exact measure_univ⟩

theorem cesaroM_real_nonneg_le (n : ℕ) (μ : Measure S) [IsFiniteMeasure μ] (A : Set S) :
    0 ≤ (cesaroM κ n μ).real A ∧ (cesaroM κ n μ).real A ≤ μ.real univ := by
  have := isFinite_cesaroM (κ := κ) n μ
  refine ⟨measureReal_nonneg, (measureReal_mono (subset_univ A)).trans ?_⟩
  rw [measureReal_def, cesaroM_univ]; rfl

omit [IsMarkovKernel κ] in
theorem cesaroM_add (n : ℕ) (μ ν : Measure S) :
    cesaroM κ n (μ + ν) = cesaroM κ n μ + cesaroM κ n ν := by
  simp only [cesaroM, adjointOp_add, Finset.sum_add_distrib, smul_add]

omit [IsMarkovKernel κ] in
theorem cesaroM_smul (n : ℕ) (c : ℝ≥0∞) (μ : Measure S) :
    cesaroM κ n (c • μ) = c • cesaroM κ n μ := by
  simp only [cesaroM, adjointOp_smul, ← Finset.smul_sum, smul_comm c]

/-- Shifting the starting measure by `r` steps moves the averages by at most `r λ(S)/(n+1)`. -/
theorem abs_cesaro_shift_le (n r : ℕ) (μ : Measure S) [IsFiniteMeasure μ] (A : Set S) :
    |(cesaroM κ n (adjointOp (kpow κ r) μ)).real A - (cesaroM κ n μ).real A| ≤
      r * μ.real univ / ((n : ℝ) + 1) := by
  have := isFinite_adjoint (κ := κ) r μ
  set a : ℕ → ℝ := fun k => (adjointOp (kpow κ k) μ).real A
  have ha : ∀ k, 0 ≤ a k ∧ a k ≤ μ.real univ := fun k => ⟨measureReal_nonneg,
    adjoint_real_le k μ A⟩
  have hshift : ∀ k, (adjointOp (kpow κ (k + 1)) (adjointOp (kpow κ r) μ)).real A =
      a (k + 1 + r) := fun k => by rw [← adjoint_add]
  rw [cesaroM_real, cesaroM_real, Finset.sum_congr rfl (fun k _ => hshift k)]
  rw [← mul_sub, abs_mul, abs_of_pos (by positivity), ← Finset.sum_sub_distrib]
  -- `Σ_{k≤n} (a(k+1+r) − a(k+1)) = Σ_{k<r} (a(n+2+k) − a(k+1))`
  have hsum : ∑ k ∈ Finset.range (n + 1), (a (k + 1 + r) - a (k + 1)) =
      ∑ k ∈ Finset.range r, (a (n + 1 + k + 1) - a (k + 1)) := by
    have h1 := Finset.sum_range_add (fun k => a (k + 1)) (n + 1) r
    have h2 := Finset.sum_range_add (fun k => a (k + 1)) r (n + 1)
    have h3 : ∑ k ∈ Finset.range (n + 1), a (k + 1 + r) =
        ∑ k ∈ Finset.range (n + 1), a (r + k + 1) :=
      Finset.sum_congr rfl fun k _ => by rw [show k + 1 + r = r + k + 1 by ring]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, h3]
    rw [show r + (n + 1) = n + 1 + r by ring] at h2
    linarith
  rw [hsum]
  have hb : |∑ k ∈ Finset.range r, (a (n + 1 + k + 1) - a (k + 1))| ≤ r * μ.real univ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ Finset.range r, |a (n + 1 + k + 1) - a (k + 1)| ≤
          ∑ _k ∈ Finset.range r, μ.real univ := Finset.sum_le_sum fun k _ => by
            rw [abs_le]; constructor <;> linarith [ha (n + 1 + k + 1), ha (k + 1)]
      _ = r * μ.real univ := by simp
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

/-! ### Uniformly Cauchy averages -/

variable (κ) in
/-- The Cesàro averages of `μ` are uniformly Cauchy on sets. -/
def CesaroCauchy (μ : Measure S) : Prop :=
  ∀ η > 0, ∃ n₀, ∀ n ≥ n₀, ∀ m ≥ n₀, ∀ A, MeasurableSet A →
    |(cesaroM κ n μ).real A - (cesaroM κ m μ).real A| ≤ η

omit [IsMarkovKernel κ] in
theorem cesaroCauchy_zero : CesaroCauchy κ 0 := fun η hη => ⟨0, fun n _ m _ A _ => by
  simp [cesaroM, adjointOp_zero, hη.le]⟩

theorem CesaroCauchy.add {μ ν : Measure S} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : CesaroCauchy κ μ) (hν : CesaroCauchy κ ν) : CesaroCauchy κ (μ + ν) := by
  intro η hη
  obtain ⟨n₁, h₁⟩ := hμ (η / 2) (half_pos hη)
  obtain ⟨n₂, h₂⟩ := hν (η / 2) (half_pos hη)
  refine ⟨max n₁ n₂, fun n hn m hm A hA => ?_⟩
  have := isFinite_cesaroM (κ := κ) n μ; have := isFinite_cesaroM (κ := κ) n ν
  have := isFinite_cesaroM (κ := κ) m μ; have := isFinite_cesaroM (κ := κ) m ν
  rw [cesaroM_add, cesaroM_add, measureReal_add_apply, measureReal_add_apply]
  have := h₁ n (le_of_max_le_left hn) m (le_of_max_le_left hm) A hA
  have := h₂ n (le_of_max_le_right hn) m (le_of_max_le_right hm) A hA
  calc _ = |((cesaroM κ n μ).real A - (cesaroM κ m μ).real A) +
        ((cesaroM κ n ν).real A - (cesaroM κ m ν).real A)| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (by linarith)

omit [IsMarkovKernel κ] in
theorem CesaroCauchy.smul {μ : Measure S} [IsFiniteMeasure μ] (hμ : CesaroCauchy κ μ)
    (c : ℝ≥0∞) : CesaroCauchy κ (c • μ) := by
  intro η hη
  obtain ⟨n₀, h⟩ := hμ (η / (c.toReal + 1)) (by positivity)
  refine ⟨n₀, fun n hn m hm A hA => ?_⟩
  rw [cesaroM_smul, cesaroM_smul, measureReal_ennreal_smul_apply,
    measureReal_ennreal_smul_apply, ← mul_sub,
    abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  have h' := h n hn m hm A hA
  calc c.toReal * |(cesaroM κ n μ).real A - (cesaroM κ m μ).real A| ≤
        (c.toReal + 1) * (η / (c.toReal + 1)) :=
        mul_le_mul (by linarith) h' (abs_nonneg _) (by positivity)
    _ = η := by field_simp

theorem cesaroCauchy_finsetSum {ι : Type*} (s : Finset ι) (μ : ι → Measure S)
    [∀ i, IsFiniteMeasure (μ i)] (h : ∀ i ∈ s, CesaroCauchy κ (μ i)) :
    CesaroCauchy κ (∑ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cesaroCauchy_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **Closure under small perturbations.** If for every `η > 0` some `T*ʳμ` is a measure with
uniformly Cauchy averages plus a measure of mass at most `η`, the averages of `μ` are uniformly
Cauchy. -/
theorem cesaroCauchy_of_approx {μ : Measure S} [IsFiniteMeasure μ]
    (h : ∀ η > 0, ∃ (r : ℕ) (μ' ρ : Measure S) (_ : IsFiniteMeasure μ') (_ : IsFiniteMeasure ρ),
      adjointOp (kpow κ r) μ = μ' + ρ ∧ CesaroCauchy κ μ' ∧ ρ.real univ ≤ η) :
    CesaroCauchy κ μ := by
  intro η hη
  obtain ⟨r, μ', ρ, _, _, hdec, hc, hρ⟩ := h (η / 4) (by positivity)
  obtain ⟨n₁, h₁⟩ := hc (η / 4) (by positivity)
  obtain ⟨n₂, hn₂⟩ := exists_nat_gt (4 * r * μ.real univ / η)
  refine ⟨max n₁ n₂, fun n hn m hm A hA => ?_⟩
  have hsh : ∀ k ≥ n₂, |(cesaroM κ k (adjointOp (kpow κ r) μ)).real A - (cesaroM κ k μ).real A| ≤
      η / 4 := fun k hk => by
    refine (abs_cesaro_shift_le k r μ A).trans ?_
    have hk' : (n₂ : ℝ) ≤ k := by exact_mod_cast hk
    rw [div_le_iff₀ (by positivity)]
    have := (div_lt_iff₀ hη).1 hn₂
    nlinarith [measureReal_nonneg (μ := μ) (s := univ)]
  have hmid : |(cesaroM κ n (adjointOp (kpow κ r) μ)).real A -
      (cesaroM κ m (adjointOp (kpow κ r) μ)).real A| ≤ η / 4 + η / 4 := by
    have := isFinite_cesaroM (κ := κ) n μ'; have := isFinite_cesaroM (κ := κ) n ρ
    have := isFinite_cesaroM (κ := κ) m μ'; have := isFinite_cesaroM (κ := κ) m ρ
    rw [hdec, cesaroM_add, cesaroM_add, measureReal_add_apply, measureReal_add_apply]
    have h1 := h₁ n (le_of_max_le_left hn) m (le_of_max_le_left hm) A hA
    have h2 := cesaroM_real_nonneg_le (κ := κ) n ρ A
    have h3 := cesaroM_real_nonneg_le (κ := κ) m ρ A
    calc _ = |((cesaroM κ n μ').real A - (cesaroM κ m μ').real A) +
          ((cesaroM κ n ρ).real A - (cesaroM κ m ρ).real A)| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add h1 (by rw [abs_le]; constructor <;> linarith))
  have e1 := hsh n (le_of_max_le_right hn)
  have e2 := hsh m (le_of_max_le_right hm)
  calc _ = |((cesaroM κ n μ).real A - (cesaroM κ n (adjointOp (kpow κ r) μ)).real A) +
        ((cesaroM κ n (adjointOp (kpow κ r) μ)).real A -
          (cesaroM κ m (adjointOp (kpow κ r) μ)).real A) +
        ((cesaroM κ m (adjointOp (kpow κ r) μ)).real A - (cesaroM κ m μ).real A)| := by ring_nf
    _ ≤ _ := by
      refine (abs_add_le _ _).trans ?_
      refine (add_le_add (abs_add_le _ _) le_rfl).trans ?_
      rw [abs_sub_comm] at e1
      linarith

/-- `T*` preserves uniformly Cauchy averages. -/
theorem cesaroCauchy_adjoint {μ : Measure S} [IsFiniteMeasure μ] (hμ : CesaroCauchy κ μ)
    (r : ℕ) : CesaroCauchy κ (adjointOp (kpow κ r) μ) := by
  have := isFinite_adjoint (κ := κ) r μ
  refine cesaroCauchy_of_approx fun η hη => ⟨0, adjointOp (kpow κ r) μ, 0, inferInstance,
    inferInstance, by rw [add_zero, ← adjoint_add, zero_add], ?_, by simp [hη.le]⟩
  -- `T*ʳμ` differs from `μ` by a shift
  intro η hη
  obtain ⟨n₁, h₁⟩ := hμ (η / 3) (by positivity)
  obtain ⟨n₂, hn₂⟩ := exists_nat_gt (3 * r * μ.real univ / η)
  refine ⟨max n₁ n₂, fun n hn m hm A hA => ?_⟩
  have hsh : ∀ k ≥ n₂, |(cesaroM κ k (adjointOp (kpow κ r) μ)).real A - (cesaroM κ k μ).real A| ≤
      η / 3 := fun k hk => by
    refine (abs_cesaro_shift_le k r μ A).trans ?_
    have hk' : (n₂ : ℝ) ≤ k := by exact_mod_cast hk
    rw [div_le_iff₀ (by positivity)]
    have := (div_lt_iff₀ hη).1 hn₂
    nlinarith [measureReal_nonneg (μ := μ) (s := univ)]
  have e1 := hsh n (le_of_max_le_right hn)
  have e2 := hsh m (le_of_max_le_right hm)
  have e3 := h₁ n (le_of_max_le_left hn) m (le_of_max_le_left hm) A hA
  rw [abs_le] at e1 e2 e3 ⊢
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2]

/-- For probability measures, uniformly Cauchy averages are Cauchy in total variation. -/
theorem tvDist_cesaro_le {μ : Measure S} [IsProbabilityMeasure μ] (hμ : CesaroCauchy κ μ) :
    ∀ η > 0, ∃ n₀, ∀ n ≥ n₀, ∀ m ≥ n₀, tvDist (cesaroM κ n μ) (cesaroM κ m μ) < η := by
  intro η hη
  obtain ⟨n₀, h⟩ := hμ (η / 4) (by positivity)
  refine ⟨n₀, fun n hn m hm => ?_⟩
  have := isProb_cesaroM (κ := κ) n μ
  have := isProb_cesaroM (κ := κ) m μ
  have := tvDist_le_of_forall (cesaroM κ n μ) (cesaroM κ m μ) (h n hn m hm)
  linarith

end StokeyLucasPrescott.StrongConvergence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Invariant measures on an ergodic set

Three facts about an ergodic set `E` (in the sense of p. 346), used for Theorem 11.9b–c.

* `exists_reach`: every subset `A ⊆ E` of positive `φ`-measure is reached from every point of
  `E`. (Otherwise the points of `E \ A` that never reach `A` form an invariant set of smaller
  `φ`-measure.)
* `pos_of_invariant`: an invariant probability measure concentrated on `E` charges every set
  that meets `E` in positive `φ`-measure; so `φ` restricted to `E` is absolutely continuous with
  respect to it (`absCont_of_concentrated`).
* `invariant_unique`: under Condition D there is at most one invariant probability measure
  concentrated on `E`. For two of them, `π₁`, `π₂`, with Hahn set `H`, the measures
  `(π₁ − π₂)` restricted to `H` and `(π₂ − π₁)` restricted to `Hᶜ` are invariant
  (`posPart_invariant`), mutually singular, and both charge every `φ`-positive part of `E`.
-/

namespace StokeyLucasPrescott.StrongConvergence

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {S : Type*} [MeasurableSpace S] {κ : Kernel S S} [IsMarkovKernel κ]

omit [IsMarkovKernel κ] in
/-- An invariant measure is invariant under every `T*ⁿ`. -/
theorem invariant_iterate {π : Measure S} (hπ : adjointOp κ π = π) (n : ℕ) :
    adjointOp (kpow κ n) π = π := by
  induction n with
  | zero =>
    change π.bind (kpow κ 0) = π
    have : (⇑(kpow κ 0)) = fun z => Measure.dirac z := funext fun z => by
      simp [kpow, Kernel.id_apply]
    rw [this, Measure.bind_dirac]
  | succ n ih => rw [adjoint_add, kpow_one, hπ, ih]

/-- From a point that never reaches `A` (after time `0`), the chain stays where `A` is never
reached. -/
theorem kpow_noReach_eq_one {E A : Set S} (hE : IsInvariantSet κ E) (hA : MeasurableSet A)
    {t : S} (htE : t ∈ E) (ht : ∀ n, 1 ≤ n → kpow κ n t A = 0) (m : ℕ) (hm : 1 ≤ m) :
    kpow κ m t ((E \ A) ∩ ⋂ n : ℕ, {u | kpow κ (n + 1) u A = 0}) = 1 := by
  have := isMarkov_kpow (κ := κ) m
  have hmeasI : ∀ n : ℕ, MeasurableSet {u | kpow κ (n + 1) u A = 0} := fun n =>
    Kernel.measurable_coe (kpow κ (n + 1)) hA (measurableSet_singleton 0)
  refine measure_inter_eq_one (hE.1.diff hA) (MeasurableSet.iInter hmeasI) ?_
    (measure_iInter_eq_one hmeasI fun n => ?_)
  · rw [sdiff_eq_compl_inter, inter_comm]
    exact measure_inter_eq_one hE.1 hA.compl (hE.2.2 t htE m hm)
      (by rw [prob_compl_eq_one_sub hA, ht m hm, tsub_zero])
  · have h0 : ∫⁻ u, kpow κ (n + 1) u A ∂kpow κ m t = 0 := by
      rw [← kpow_add_apply m (n + 1) t hA]; exact ht _ (by omega)
    rw [lintegral_eq_zero_iff (Kernel.measurable_coe _ hA)] at h0
    rw [← prob_compl_eq_zero_iff (hmeasI n)]
    exact ae_iff.1 h0

/-- **Reachability.** In an ergodic set every subset of positive `φ`-measure is reached from
every point. -/
theorem exists_reach {φ : Measure S} [IsFiniteMeasure φ] {E : Set S} (hE : IsErgodicSetD κ φ E)
    {A : Set S} (hA : MeasurableSet A) (hAE : A ⊆ E) (hpos : 0 < φ A) {s : S} (hs : s ∈ E) :
    ∃ n, 1 ≤ n ∧ 0 < kpow κ n s A := by
  by_contra hne
  push Not at hne
  have hzero : ∀ n, 1 ≤ n → kpow κ n s A = 0 := fun n hn => le_antisymm (hne n hn) zero_le
  set G := (E \ A) ∩ ⋂ n : ℕ, {u | kpow κ (n + 1) u A = 0}
  have hGmem : ∀ u ∈ G, u ∈ E ∧ ∀ n, 1 ≤ n → kpow κ n u A = 0 := fun u hu => by
    refine ⟨hu.1.1, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact mem_iInter.1 hu.2 k
  have hGinv : IsInvariantSet κ G := by
    refine ⟨(hE.1.1.diff hA).inter (MeasurableSet.iInter fun n =>
      Kernel.measurable_coe (kpow κ (n + 1)) hA (measurableSet_singleton 0)), ?_, fun u hu m hm =>
        kpow_noReach_eq_one hE.1 hA (hGmem u hu).1 (hGmem u hu).2 m hm⟩
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    have : kpow κ 1 s G = 1 := kpow_noReach_eq_one hE.1 hA hs hzero 1 le_rfl
    rw [hemp, measure_empty] at this
    exact zero_ne_one this
  have hle := hE.2 G (fun u hu => (hGmem u hu).1) hGinv
  have hGsub : G ⊆ E \ A := inter_subset_left
  have h1 : φ G ≤ φ E - φ A := by
    rw [← measure_sdiff hAE hA.nullMeasurableSet (measure_ne_top φ A)]
    exact measure_mono hGsub
  have h2 : φ E - φ A < φ E := ENNReal.sub_lt_self (measure_ne_top φ E)
    (ne_of_gt (lt_of_lt_of_le hpos (measure_mono hAE))) hpos.ne'
  exact absurd (hle.trans h1) (not_le.2 h2)

/-- An invariant probability measure concentrated on an ergodic set `E` charges every set that
meets `E` in positive `φ`-measure. -/
theorem pos_of_invariant {φ : Measure S} [IsFiniteMeasure φ] {E : Set S}
    (hE : IsErgodicSetD κ φ E) {π : Measure S} [IsProbabilityMeasure π] (hπ : adjointOp κ π = π)
    (hπE : π E = 1) {A : Set S} (hA : MeasurableSet A) (hpos : 0 < φ (A ∩ E)) : 0 < π A := by
  by_contra h0
  have h0 : π (A ∩ E) = 0 := measure_mono_null inter_subset_left (le_antisymm (not_lt.1 h0)
    zero_le)
  have hAE : MeasurableSet (A ∩ E) := hA.inter hE.1.1
  have hae : ∀ n : ℕ, ∀ᵐ s ∂π, kpow κ (n + 1) s (A ∩ E) = 0 := fun n => by
    have : ∫⁻ s, kpow κ (n + 1) s (A ∩ E) ∂π = 0 := by
      rw [← adjointOp_apply _ _ hAE, invariant_iterate hπ]; exact h0
    exact (lintegral_eq_zero_iff (Kernel.measurable_coe _ hAE)).1 this
  have hE' : ∀ᵐ s ∂π, s ∈ E := by
    rw [ae_iff, ← compl_def, prob_compl_eq_zero_iff hE.1.1]; exact hπE
  obtain ⟨s, hsE, hs⟩ := (hE'.and (ae_all_iff.2 hae)).exists
  obtain ⟨n, hn, hpos'⟩ := exists_reach hE hAE inter_subset_right hpos hsE
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [hs k] at hpos'
  exact lt_irrefl _ hpos'

/-- A measure absolutely continuous with respect to `φ` and concentrated on the ergodic set `E`
is absolutely continuous with respect to every invariant probability measure on `E`. -/
theorem absCont_of_concentrated {φ : Measure S} [IsFiniteMeasure φ] {E : Set S}
    (hE : IsErgodicSetD κ φ E) {π : Measure S} [IsProbabilityMeasure π] (hπ : adjointOp κ π = π)
    (hπE : π E = 1) {K : Measure S} (hK : K ≪ φ) (hKE : K Eᶜ = 0) : K ≪ π := by
  refine Measure.AbsolutelyContinuous.mk fun A hA hπA => ?_
  have hφ : φ (A ∩ E) = 0 := by
    by_contra hne
    exact absurd hπA (pos_of_invariant hE hπ hπE hA (pos_iff_ne_zero.2 hne)).ne'
  have h1 : K (A ∩ E) = 0 := hK hφ
  have h2 : K (A ∩ Eᶜ) = 0 := measure_mono_null inter_subset_right hKE
  calc K A = K (A ∩ E) + K (A \ E) := (measure_inter_add_sdiff A hE.1.1).symm
    _ = 0 := by rw [Set.sdiff_eq, h1, h2, add_zero]

/-- For invariant probability measures `π₁, π₂` and a Hahn set `H` (`π₂ ≤ π₁` on `H`,
`π₁ ≤ π₂` off `H`), the positive part `(π₁ − π₂)|_H` is invariant. -/
theorem posPart_invariant {π₁ π₂ : Measure S} [IsProbabilityMeasure π₁] [IsProbabilityMeasure π₂]
    (h₁ : adjointOp κ π₁ = π₁) (h₂ : adjointOp κ π₂ = π₂) {H : Set S} (hH : MeasurableSet H)
    (hle : π₂.restrict H ≤ π₁.restrict H) (hle' : π₁.restrict Hᶜ ≤ π₂.restrict Hᶜ) :
    adjointOp κ (π₁.restrict H - π₂.restrict H) = π₁.restrict H - π₂.restrict H := by
  set α := π₁.restrict H - π₂.restrict H
  have hα : α + π₂.restrict H = π₁.restrict H := Measure.sub_add_cancel_of_le hle
  have hαfin : IsFiniteMeasure α := by
    refine ⟨lt_of_le_of_lt ?_ (measure_lt_top (π₁.restrict H) univ)⟩
    rw [← hα]; exact le_add_right le_rfl
  have hPfin : IsFiniteMeasure (adjointOp κ α) := by
    have := isFinite_adjoint (κ := κ) 1 α; rwa [kpow_one] at this
  have hαreal : ∀ A, MeasurableSet A →
      α.real A = π₁.real (A ∩ H) - π₂.real (A ∩ H) := fun A hA => by
    have := congrArg (fun μ : Measure S => μ.real A) hα
    rw [measureReal_add_apply, measureReal_restrict_apply hA,
      measureReal_restrict_apply hA] at this
    linarith
  -- `(αP)(A) ≥ π₁(A) − π₂(A)`
  have hint : ∀ A, MeasurableSet A → π₁.real A - π₂.real A ≤ (adjointOp κ α).real A := by
    intro A hA
    set f : S → ℝ := fun s => (κ s).real A
    have hfm : Measurable f := (κ.measurable_coe hA).ennreal_toReal
    have hf01 : ∀ s, 0 ≤ f s ∧ f s ≤ 1 := fun s => ⟨measureReal_nonneg, measureReal_le_one⟩
    have hfi : ∀ (μ : Measure S) [IsFiniteMeasure μ], Integrable f μ := fun μ _ =>
      integrable_of_abs_le μ hfm (C := 1) fun s => by
        rw [abs_of_nonneg (hf01 s).1]; exact (hf01 s).2
    have e1 : π₁.real A = ∫ s in H, f s ∂π₁ + ∫ s in Hᶜ, f s ∂π₁ := by
      rw [integral_add_compl hH (hfi π₁), ← bind_real_eq κ π₁ hA]
      rw [h₁]
    have e2 : π₂.real A = ∫ s in H, f s ∂π₂ + ∫ s in Hᶜ, f s ∂π₂ := by
      rw [integral_add_compl hH (hfi π₂), ← bind_real_eq κ π₂ hA]
      rw [h₂]
    have e3 : (adjointOp κ α).real A = ∫ s in H, f s ∂π₁ - ∫ s in H, f s ∂π₂ := by
      rw [bind_real_eq κ α hA]
      have := integral_add_measure (hfi α) (hfi (π₂.restrict H)) (f := f)
      rw [hα] at this
      linarith
    have e4 : ∫ s in Hᶜ, f s ∂π₁ ≤ ∫ s in Hᶜ, f s ∂π₂ :=
      integral_mono_measure hle' (Eventually.of_forall fun s => (hf01 s).1) (hfi _)
    linarith
  have hge : ∀ A, MeasurableSet A → α.real A ≤ (adjointOp κ α).real A := by
    intro A hA
    calc α.real A = π₁.real (A ∩ H) - π₂.real (A ∩ H) := hαreal A hA
      _ ≤ (adjointOp κ α).real (A ∩ H) := hint _ (hA.inter hH)
      _ ≤ (adjointOp κ α).real A := measureReal_mono inter_subset_left
  have hmass : (adjointOp κ α).real univ = α.real univ := by
    have := adjointOp_kpow_univ (κ := κ) 1 α; rw [kpow_one] at this
    rw [measureReal_def, this]; rfl
  refine Measure.ext fun A hA => ?_
  have h1 := hge A hA
  have h2 := hge Aᶜ hA.compl
  rw [measureReal_compl hA, measureReal_compl hA, hmass] at h2
  have h3 : (adjointOp κ α).real A = α.real A := le_antisymm (by linarith) h1
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h3

/-- **Uniqueness.** Under Condition D, an ergodic set carries at most one invariant probability
measure. -/
theorem invariant_unique {φ : Measure S} {N : ℕ} {ε : ℝ} (hD : DoeblinFor κ φ N ε) {E : Set S}
    (hE : IsErgodicSetD κ φ E) {π₁ π₂ : Measure S} [IsProbabilityMeasure π₁]
    [IsProbabilityMeasure π₂] (h₁ : adjointOp κ π₁ = π₁) (h₂ : adjointOp κ π₂ = π₂)
    (h₁E : π₁ E = 1) (h₂E : π₂ E = 1) : π₁ = π₂ := by
  have hφ := hD.1
  obtain ⟨H, hH, hHle, hHle'⟩ := hahn_decomposition π₁ π₂
  have hle : π₂.restrict H ≤ π₁.restrict H := Measure.le_iff.2 fun t ht => by
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact hHle _ (ht.inter hH) inter_subset_right
  have hle' : π₁.restrict Hᶜ ≤ π₂.restrict Hᶜ := Measure.le_iff.2 fun t ht => by
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact hHle' _ (ht.inter hH.compl) inter_subset_right
  have hP := posPart_invariant h₁ h₂ hH hle hle'
  have hN := posPart_invariant h₂ h₁ hH.compl hle' (by rw [compl_compl]; exact hle)
  -- the two parts and their masses
  set α := π₁.restrict H - π₂.restrict H
  set β := π₂.restrict Hᶜ - π₁.restrict Hᶜ
  have hα : α + π₂.restrict H = π₁.restrict H := Measure.sub_add_cancel_of_le hle
  have hβ : β + π₁.restrict Hᶜ = π₂.restrict Hᶜ := Measure.sub_add_cancel_of_le hle'
  have hαfin : IsFiniteMeasure α :=
    ⟨lt_of_le_of_lt (by rw [← hα]; exact le_add_right le_rfl) (measure_lt_top (π₁.restrict H) univ)⟩
  have hβfin : IsFiniteMeasure β :=
    ⟨lt_of_le_of_lt (by rw [← hβ]; exact le_add_right le_rfl)
      (measure_lt_top (π₂.restrict Hᶜ) univ)⟩
  have hαH : α Hᶜ = 0 := by
    have := congrArg (fun μ : Measure S => μ Hᶜ) hα
    simp only [Measure.add_apply, Measure.restrict_apply hH.compl, compl_inter_self,
      measure_empty, add_zero] at this
    exact this
  have hβH : β H = 0 := by
    have := congrArg (fun μ : Measure S => μ H) hβ
    simp only [Measure.add_apply, Measure.restrict_apply hH, inter_compl_self,
      measure_empty, add_zero] at this
    exact this
  have hαE : α Eᶜ = 0 := by
    have := congrArg (fun μ : Measure S => μ Eᶜ) hα
    simp only [Measure.add_apply, Measure.restrict_apply hE.1.1.compl] at this
    have h0 : π₁ (Eᶜ ∩ H) = 0 := measure_mono_null inter_subset_left
      ((prob_compl_eq_zero_iff hE.1.1).2 h₁E)
    rw [h0] at this
    exact (add_eq_zero.1 this).1
  have hβE : β Eᶜ = 0 := by
    have := congrArg (fun μ : Measure S => μ Eᶜ) hβ
    simp only [Measure.add_apply, Measure.restrict_apply hE.1.1.compl] at this
    have h0 : π₂ (Eᶜ ∩ Hᶜ) = 0 := measure_mono_null inter_subset_left
      ((prob_compl_eq_zero_iff hE.1.1).2 h₂E)
    rw [h0] at this
    exact (add_eq_zero.1 this).1
  have hmass : α univ = β univ := by
    have ha := congrArg (fun μ : Measure S => μ.real univ) hα
    have hb := congrArg (fun μ : Measure S => μ.real univ) hβ
    rw [measureReal_add_apply, measureReal_restrict_apply MeasurableSet.univ, univ_inter,
      measureReal_restrict_apply MeasurableSet.univ, univ_inter] at ha hb
    have h1 := measureReal_add_measureReal_compl (μ := π₁) hH
    have h2 := measureReal_add_measureReal_compl (μ := π₂) hH
    simp only [probReal_univ] at h1 h2
    have : α.real univ = β.real univ := by linarith
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 this
  -- a nonzero part, normalised, would charge both `H` and `Hᶜ`
  by_cases ha0 : α univ = 0
  · have hα0 : α = 0 := Measure.measure_univ_eq_zero.1 ha0
    have hβ0 : β = 0 := Measure.measure_univ_eq_zero.1 (hmass ▸ ha0)
    rw [hα0, zero_add] at hα
    rw [hβ0, zero_add] at hβ
    ext A hA
    rw [← measure_inter_add_sdiff A hH, ← measure_inter_add_sdiff (μ := π₂) A hH,
      ← Measure.restrict_apply hA, ← Measure.restrict_apply hA, ← hα, Set.sdiff_eq,
      ← Measure.restrict_apply hA, ← Measure.restrict_apply hA, hβ]
  · exfalso
    have hφE : 0 < φ E := by
      have := invariant_real_gt hD hE.1
      exact ENNReal.toReal_pos_iff.1 (lt_trans hD.2.2.1 this) |>.1
    set c := (α univ)⁻¹
    have hc : c ≠ ⊤ := ENNReal.inv_ne_top.2 ha0
    have hαp : IsProbabilityMeasure (c • α) :=
      ⟨by rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel ha0 (measure_ne_top _ _)]⟩
    have hβp : IsProbabilityMeasure (c • β) :=
      ⟨by rw [Measure.smul_apply, smul_eq_mul, ← hmass,
        ENNReal.inv_mul_cancel ha0 (measure_ne_top _ _)]⟩
    have hαinv : adjointOp κ (c • α) = c • α := by rw [adjointOp_smul, hP]
    have hβinv : adjointOp κ (c • β) = c • β := by rw [adjointOp_smul, hN]
    have hαE1 : (c • α) E = 1 := by
      rw [← prob_compl_eq_zero_iff hE.1.1, Measure.smul_apply, hαE, smul_zero]
    have hβE1 : (c • β) E = 1 := by
      rw [← prob_compl_eq_zero_iff hE.1.1, Measure.smul_apply, hβE, smul_zero]
    have hsplit : φ E = φ (H ∩ E) + φ (Hᶜ ∩ E) := by
      rw [inter_comm H, inter_comm Hᶜ, ← Set.sdiff_eq, measure_inter_add_sdiff E hH]
    rcases eq_zero_or_pos (φ (H ∩ E)) with h0 | hpos
    · have hpos' : 0 < φ (Hᶜ ∩ E) := by
        rw [hsplit, h0, zero_add] at hφE; exact hφE
      have := pos_of_invariant hE hαinv hαE1 hH.compl hpos'
      rw [Measure.smul_apply, hαH, smul_zero] at this
      exact lt_irrefl _ this
    · have := pos_of_invariant hE hβinv hβE1 hH hpos
      rw [Measure.smul_apply, hβH, smul_zero] at this
      exact lt_irrefl _ this

end StokeyLucasPrescott.StrongConvergence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Cesàro convergence for measures with bounded density

Let `π` be an invariant probability measure. For a measure `λ = hπ` with bounded density, the
Cesàro averages of `T*ⁿλ` are uniformly Cauchy on sets (`cesaroCauchy_withDensity`). This is von
Neumann's mean ergodic theorem in `L²(π)` (Mathlib's
`ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`), applied to the adjoint of
the Markov operator `T`.

`T` is built without choosing representatives: with `ρ = π ⊗ P` the joint law of two successive
states, the maps `J₁ f = f ∘ fst` and `J₂ f = f ∘ snd` are isometries `L²(π) → L²(ρ)` (both
marginals of `ρ` are `π`, by invariance), and `T = J₁† J₂`. Thus `‖T‖ ≤ 1`, and
`⟪T f, g⟫ = ∫ g(x) ∫ f(y) P(x, dy) π(dx)`, so `T` acts on bounded functions as
`f ↦ ∫ f(y) P(·, dy)` (`markovL2_toLp`). Since
`(T*ᵏλ)(A) = ⟪Tᵏ 1_A, h⟫ = ⟪1_A, (T†)ᵏ h⟫`, the averages of `λ` are inner products of `1_A`
with the Birkhoff averages of `T†` at `h`, which converge in `L²(π)`.
-/

namespace StokeyLucasPrescott.StrongConvergence

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

variable {S : Type*} [MeasurableSpace S] {κ : Kernel S S} [IsMarkovKernel κ] {π : Measure S}
  [IsProbabilityMeasure π]

theorem measurePreserving_fst_compProd :
    MeasurePreserving Prod.fst (π ⊗ₘ κ) π :=
  ⟨measurable_fst, Measure.fst_compProd π κ⟩

theorem measurePreserving_snd_compProd (hπ : adjointOp κ π = π) :
    MeasurePreserving Prod.snd (π ⊗ₘ κ) π :=
  ⟨measurable_snd, by rw [← Measure.snd, Measure.snd_compProd]; exact hπ⟩

variable (κ π) in
/-- `J₁ f = f ∘ fst`, an isometry `L²(π) → L²(π ⊗ P)`. -/
noncomputable def jFst : Lp ℝ 2 π →L[ℝ] Lp ℝ 2 (π ⊗ₘ κ) :=
  (Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst_compProd).toContinuousLinearMap

/-- `J₂ f = f ∘ snd`, an isometry `L²(π) → L²(π ⊗ P)` when `π` is invariant. -/
noncomputable def jSnd (hπ : adjointOp κ π = π) : Lp ℝ 2 π →L[ℝ] Lp ℝ 2 (π ⊗ₘ κ) :=
  (Lp.compMeasurePreservingₗᵢ ℝ Prod.snd (measurePreserving_snd_compProd hπ)).toContinuousLinearMap

/-- The Markov operator on `L²(π)`, `T = J₁† J₂`. -/
noncomputable def markovL2 (hπ : adjointOp κ π = π) : Lp ℝ 2 π →L[ℝ] Lp ℝ 2 π :=
  (jFst κ π).adjoint.comp (jSnd hπ)

theorem norm_markovL2_le (hπ : adjointOp κ π = π) : ‖markovL2 hπ‖ ≤ 1 := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  rw [ContinuousLinearMap.adjoint.norm_map]
  calc ‖jFst κ π‖ * ‖jSnd hπ‖ ≤ 1 * 1 := mul_le_mul
        (LinearIsometry.norm_toContinuousLinearMap_le _)
        (LinearIsometry.norm_toContinuousLinearMap_le _)
        (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem inner_real_apply (a b : ℝ) : inner ℝ a b = a * b := by
  simp [RCLike.inner_apply, mul_comm]

omit [IsProbabilityMeasure π] in
/-- A bounded measurable function is in `L²` of a finite measure. -/
theorem memLp_two_of_bound {μ : Measure S} [IsFiniteMeasure μ] {f : S → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ s, |f s| ≤ C) : MemLp f 2 μ :=
  MemLp.of_bound hf.aestronglyMeasurable C (Eventually.of_forall fun s => by
    rw [Real.norm_eq_abs]; exact hC s)

/-- `⟪T f, g⟫ = ∫ f(y) g(x) d(π ⊗ P)`. -/
theorem inner_markovL2 (hπ : adjointOp κ π = π) (f g : Lp ℝ 2 π) :
    inner ℝ (markovL2 hπ f) g = ∫ p, f p.2 * g p.1 ∂(π ⊗ₘ κ) := by
  rw [markovL2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  have h1 := Lp.coeFn_compMeasurePreserving f (measurePreserving_snd_compProd hπ)
  have h2 := Lp.coeFn_compMeasurePreserving g (measurePreserving_fst_compProd (κ := κ))
  filter_upwards [h1, h2] with p hp1 hp2
  rw [inner_real_apply]
  exact congrArg₂ (· * ·) hp1 hp2

/-- On bounded measurable functions `T f = ∫ f(y) P(·, dy)`. -/
theorem markovL2_toLp (hπ : adjointOp κ π = π) {F : S → ℝ} (hF : Measurable F) {C : ℝ}
    (hC : ∀ s, |F s| ≤ C) :
    markovL2 hπ ((memLp_two_of_bound hF hC).toLp F) =
      (memLp_two_of_bound (theorem_8_1_cor κ hF hC).1 (theorem_8_1_cor κ hF hC).2).toLp
        (markovOpR κ F) := by
  refine ext_inner_right ℝ fun g => ?_
  rw [inner_markovL2, MeasureTheory.L2.inner_def]
  have hFa := MemLp.coeFn_toLp (memLp_two_of_bound (μ := π) hF hC)
  have hKa := MemLp.coeFn_toLp (memLp_two_of_bound (μ := π) (theorem_8_1_cor κ hF hC).1
    (theorem_8_1_cor κ hF hC).2)
  -- the left side, by Fubini
  have hFsnd : (fun p : S × S => (memLp_two_of_bound (μ := π) hF hC).toLp F p.2) =ᵐ[π ⊗ₘ κ]
      fun p => F p.2 :=
    (measurePreserving_snd_compProd hπ).quasiMeasurePreserving.ae_eq_comp hFa
  have hgint : Integrable (fun p : S × S => g p.1) (π ⊗ₘ κ) := by
    have := (Lp.memLp g).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    exact (measurePreserving_fst_compProd (κ := κ)).integrable_comp_of_integrable this
  have hint : Integrable (fun p : S × S => F p.2 * g p.1) (π ⊗ₘ κ) :=
    hgint.bdd_mul (hF.comp measurable_snd).aestronglyMeasurable
      (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hC p.2)
  have hL : ∫ p, (memLp_two_of_bound (μ := π) hF hC).toLp F p.2 * g p.1 ∂(π ⊗ₘ κ) =
      ∫ p, F p.2 * g p.1 ∂(π ⊗ₘ κ) :=
    integral_congr_ae (by filter_upwards [hFsnd] with p hp; rw [hp])
  rw [hL, Measure.integral_compProd hint]
  refine integral_congr_ae ?_
  filter_upwards [hKa] with x hx
  rw [inner_real_apply, hx, markovOpR, ← integral_mul_const]

/-- The `n`-step probabilities `x ↦ Pⁿ(x, A)`. -/
noncomputable def stepFn (κ : Kernel S S) (k : ℕ) (A : Set S) (x : S) : ℝ := (kpow κ k x).real A

omit [IsMarkovKernel κ] in
theorem measurable_stepFn (k : ℕ) {A : Set S} (hA : MeasurableSet A) :
    Measurable (stepFn κ k A) :=
  (Kernel.measurable_coe (kpow κ k) hA).ennreal_toReal

theorem abs_stepFn_le (k : ℕ) (A : Set S) (x : S) : |stepFn κ k A x| ≤ 1 := by
  have := isMarkov_kpow (κ := κ) k
  rw [stepFn, abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one

theorem markovOpR_stepFn (k : ℕ) {A : Set S} (hA : MeasurableSet A) :
    markovOpR κ (stepFn κ k A) = stepFn κ (k + 1) A := by
  funext x
  have := isMarkov_kpow (κ := κ) k
  simp only [markovOpR, stepFn]
  change _ = ((kpow κ k ∘ₖ κ) x).real A
  rw [measureReal_def, Kernel.comp_apply' _ _ _ hA,
    ← integral_toReal (Kernel.measurable_coe _ hA).aemeasurable
      (Eventually.of_forall fun y => measure_lt_top (kpow κ k y) A)]
  rfl

theorem markovL2_iterate (hπ : adjointOp κ π = π) {A : Set S} (hA : MeasurableSet A) (k : ℕ) :
    (markovL2 hπ)^[k] ((memLp_two_of_bound (μ := π) (measurable_stepFn (κ := κ) 0 hA)
      (abs_stepFn_le 0 A)).toLp _) =
      (memLp_two_of_bound (μ := π) (measurable_stepFn (κ := κ) k hA)
        (abs_stepFn_le k A)).toLp _ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, markovL2_toLp hπ (measurable_stepFn k hA)
      (abs_stepFn_le k A)]
    congr 1
    exact markovOpR_stepFn k hA

omit [IsProbabilityMeasure π] in
/-- `⟪Tᵏ x, y⟫ = ⟪x, (T†)ᵏ y⟫`. -/
theorem inner_iterate_adjoint (T : Lp ℝ 2 π →L[ℝ] Lp ℝ 2 π) (k : ℕ) (x y : Lp ℝ 2 π) :
    inner ℝ (T^[k] x) y = inner ℝ x (T.adjoint^[k] y) := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← ContinuousLinearMap.adjoint_inner_right, ih,
      Function.iterate_succ_apply]

/-- A bounded density gives a finite measure. -/
theorem isFiniteMeasure_withDensity_of_bound {H : S → ℝ≥0} {C : ℝ≥0} (hC : ∀ s, H s ≤ C) :
    IsFiniteMeasure (π.withDensity fun s => (H s : ℝ≥0∞)) := by
  refine isFiniteMeasure_withDensity (ne_of_lt (lt_of_le_of_lt (lintegral_mono fun s =>
    (ENNReal.coe_le_coe.2 (hC s))) ?_))
  simp

/-- `(T*ᵏ(hπ))(A) = ∫ Pᵏ(x, A) h(x) π(dx)`. -/
theorem adjoint_withDensity_real {H : S → ℝ≥0} (hH : Measurable H) {C : ℝ≥0}
    (hC : ∀ s, H s ≤ C) (k : ℕ) {A : Set S} (hA : MeasurableSet A) :
    have : IsFiniteMeasure (π.withDensity fun s => (H s : ℝ≥0∞)) :=
      isFiniteMeasure_withDensity_of_bound hC
    (adjointOp (kpow κ k) (π.withDensity fun s => (H s : ℝ≥0∞))).real A =
      ∫ x, stepFn κ k A x * (H x : ℝ) ∂π := by
  intro _
  have := isMarkov_kpow (κ := κ) k
  rw [bind_real_eq _ _ hA, integral_withDensity_eq_integral_smul hH]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, stepFn]
  ring

/-- `⟪f, h⟫ = ∫ f h dπ` for bounded measurable functions. -/
theorem inner_toLp_toLp {F G : S → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ s, |F s| ≤ C)
    (hG : Measurable G) {D : ℝ} (hD : ∀ s, |G s| ≤ D) :
    inner ℝ ((memLp_two_of_bound (μ := π) hF hC).toLp F)
      ((memLp_two_of_bound (μ := π) hG hD).toLp G) = ∫ x, F x * G x ∂π := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_two_of_bound (μ := π) hF hC),
    MemLp.coeFn_toLp (memLp_two_of_bound (μ := π) hG hD)] with x h1 h2
  rw [inner_real_apply, h1, h2]

/-- **Cesàro convergence for bounded densities.** If `π` is invariant and `λ = hπ` with `h`
bounded, the Cesàro averages of `T*ⁿλ` are uniformly Cauchy on sets. -/
theorem cesaroCauchy_withDensity (hπ : adjointOp κ π = π) {H : S → ℝ≥0} (hH : Measurable H)
    {C : ℝ≥0} (hC : ∀ s, H s ≤ C) :
    CesaroCauchy κ (π.withDensity fun s => (H s : ℝ≥0∞)) := by
  have hfin := isFiniteMeasure_withDensity_of_bound (π := π) hC
  set V := (markovL2 hπ).adjoint
  have hV : ‖V‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]; exact norm_markovL2_le hπ
  have hHm : Measurable fun s => (H s : ℝ) := hH.coe_nnreal_real
  have hHb : ∀ s, |(H s : ℝ)| ≤ C := fun s => by
    rw [abs_of_nonneg (NNReal.coe_nonneg _)]; exact_mod_cast hC s
  set h := (memLp_two_of_bound (μ := π) hHm hHb).toLp _
  set B : ℕ → Lp ℝ 2 π := fun n => birkhoffAverage ℝ V _root_.id n h
  have hcauchy : CauchySeq B := (V.tendsto_birkhoffAverage_orthogonalProjection hV h).cauchySeq
  -- the averages as inner products
  have hkey : ∀ n A, (hA : MeasurableSet A) →
      (cesaroM κ n (π.withDensity fun s => (H s : ℝ≥0∞))).real A =
        inner ℝ ((memLp_two_of_bound (μ := π) (measurable_stepFn (κ := κ) 0 hA)
          (abs_stepFn_le 0 A)).toLp _) (V (B (n + 1))) := by
    intro n A hA
    set u := (memLp_two_of_bound (μ := π) (measurable_stepFn (κ := κ) 0 hA)
      (abs_stepFn_le 0 A)).toLp _
    have hterm : ∀ k, (adjointOp (kpow κ (k + 1)) (π.withDensity fun s => (H s : ℝ≥0∞))).real A =
        inner ℝ u (V^[k + 1] h) := fun k => by
      rw [adjoint_withDensity_real hH hC (k + 1) hA, ← inner_iterate_adjoint,
        markovL2_iterate hπ hA, inner_toLp_toLp (measurable_stepFn (k + 1) hA)
          (abs_stepFn_le (k + 1) A) hHm hHb]
    rw [cesaroM_real, Finset.sum_congr rfl fun k _ => hterm k, ← inner_sum, ← real_inner_smul_right]
    congr 1
    simp only [B, birkhoffAverage, birkhoffSum, id, map_smul, map_sum]
    congr 1
    · push_cast; ring
    · exact Finset.sum_congr rfl fun k _ => Function.iterate_succ_apply' V k h
  intro η hη
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hcauchy η hη
  refine ⟨N, fun n hn m hm A hA => ?_⟩
  rw [hkey n A hA, hkey m A hA, ← inner_sub_right, ← map_sub]
  set u := (memLp_two_of_bound (μ := π) (measurable_stepFn (κ := κ) 0 hA)
    (abs_stepFn_le 0 A)).toLp _
  have hu : ‖u‖ ≤ 1 := by
    have := Lp.norm_le_of_ae_bound (f := u) zero_le_one (by
      filter_upwards [MemLp.coeFn_toLp (memLp_two_of_bound (μ := π)
        (measurable_stepFn (κ := κ) 0 hA) (abs_stepFn_le 0 A))] with x hx
      rw [hx, Real.norm_eq_abs]; exact abs_stepFn_le 0 A x)
    rw [show measureUnivNNReal π = 1 by simp [measureUnivNNReal]] at this
    simpa using this
  have hd : ‖B (n + 1) - B (m + 1)‖ < η := by
    rw [← dist_eq_norm]; exact hN _ (by omega) _ (by omega)
  calc |inner ℝ u (V (B (n + 1) - B (m + 1)))| ≤ ‖u‖ * ‖V (B (n + 1) - B (m + 1))‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ 1 * (1 * ‖B (n + 1) - B (m + 1)‖) := by
        gcongr
        exact (V.le_opNorm _).trans (mul_le_mul_of_nonneg_right hV (norm_nonneg _))
    _ ≤ η := by linarith

end StokeyLucasPrescott.StrongConvergence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Existence of invariant measures under Doeblin's condition

Under Condition D for `(φ, N, ε)`, every probability measure `λ` yields an invariant probability
measure `π` with `π(A) = 1` whenever all the Cesàro averages of `λ` give `A` mass one
(`exists_invariant`). The construction is elementary.

* **A reference measure.** `ψ = Σⱼ 2^{-(j+1)} φPʲ` (`doeblinRef`) is finite, with `φ ≤ 2ψ` and
  `ψP ≤ 2ψ`, so `ψPᵐ ≤ 2ᵐψ`.
* **Uniform integrability** (`adjoint_real_le_ref`). For `μ` of mass at most one,
  `μP^{Nj}(A) ≤ b_j ψ(A) + (1 − ε)ʲ μ(S)`. Split `μPᴺ` by a Hahn set `H` for `μPᴺ − (2/ε)ψ`:
  off `H` it is below `(2/ε)ψ`, and `ψ(H) ≤ ε/2`, so Doeblin gives `μPᴺ(H) ≤ (1 − ε)μ(S)`.
  Hence the Cesàro averages are uniformly absolutely continuous with respect to `ψ`
  (`cesaro_small`).
* **The limit.** Along a non-principal ultrafilter on `ℕ`, the averages converge on every set
  (they lie in `[0, 1]`). The limit is finitely additive, and by uniform absolute continuity
  countably additive. Integrals of `[0, 1]`-valued functions converge too, by a uniform
  discretisation (`abs_integral_sub_levels_le`). The averages are nearly invariant, so the
  limit is invariant.
-/

namespace StokeyLucasPrescott.StrongConvergence

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {S : Type*} [MeasurableSpace S] {κ : Kernel S S} [IsMarkovKernel κ]

omit [IsMarkovKernel κ] in
theorem adjointOp_kpow_zero (μ : Measure S) : adjointOp (kpow κ 0) μ = μ := by
  change μ.bind (kpow κ 0) = μ
  have : (⇑(kpow κ 0)) = fun z => Measure.dirac z := funext fun z => by
    simp [kpow, Kernel.id_apply]
  rw [this, Measure.bind_dirac]

/-! ### The reference measure -/

variable (κ) in
/-- `ψ = Σⱼ 2^{-(j+1)} φPʲ`. -/
noncomputable def doeblinRef (φ : Measure S) : Measure S :=
  Measure.sum fun j : ℕ => ((2 : ℝ≥0∞) ^ (j + 1))⁻¹ • adjointOp (kpow κ j) φ

omit [IsMarkovKernel κ] in
theorem doeblinRef_apply (φ : Measure S) {A : Set S} (hA : MeasurableSet A) :
    doeblinRef κ φ A = ∑' j : ℕ, ((2 : ℝ≥0∞) ^ (j + 1))⁻¹ * adjointOp (kpow κ j) φ A := by
  simp [doeblinRef, Measure.sum_apply _ hA]

theorem tsum_inv_two_pow_succ : ∑' j : ℕ, ((2 : ℝ≥0∞) ^ (j + 1))⁻¹ = 1 := by
  have : ∀ j : ℕ, ((2 : ℝ≥0∞) ^ (j + 1))⁻¹ = 2⁻¹ * 2⁻¹ ^ j := fun j => by
    rw [← ENNReal.inv_pow, pow_succ, ENNReal.mul_inv (by simp) (by simp), mul_comm]
  simp_rw [this]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
    ENNReal.inv_mul_cancel (by simp) (by simp)]

theorem isFinite_doeblinRef (φ : Measure S) [IsFiniteMeasure φ] :
    IsFiniteMeasure (doeblinRef κ φ) := ⟨by
  rw [doeblinRef_apply φ MeasurableSet.univ]
  simp only [adjointOp_kpow_univ]
  rw [ENNReal.tsum_mul_right, tsum_inv_two_pow_succ, one_mul]
  exact measure_lt_top φ univ⟩

omit [IsMarkovKernel κ] in
theorem le_two_doeblinRef (φ : Measure S) : φ ≤ (2 : ℝ≥0∞) • doeblinRef κ φ := by
  refine Measure.le_iff.2 fun A hA => ?_
  rw [Measure.smul_apply, doeblinRef_apply φ hA, smul_eq_mul]
  calc φ A = 2 * (((2 : ℝ≥0∞) ^ (0 + 1))⁻¹ * adjointOp (kpow κ 0) φ A) := by
        rw [adjointOp_kpow_zero, zero_add, pow_one, ← mul_assoc,
          ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]
    _ ≤ _ := by gcongr; exact ENNReal.le_tsum (f := fun j : ℕ =>
        ((2 : ℝ≥0∞) ^ (j + 1))⁻¹ * adjointOp (kpow κ j) φ A) 0

omit [IsMarkovKernel κ] in
theorem adjoint_doeblinRef_le (φ : Measure S) :
    adjointOp κ (doeblinRef κ φ) ≤ (2 : ℝ≥0∞) • doeblinRef κ φ := by
  refine Measure.le_iff.2 fun A hA => ?_
  rw [adjointOp_apply κ _ hA, Measure.smul_apply, smul_eq_mul, doeblinRef_apply φ hA,
    doeblinRef, lintegral_sum_measure]
  simp only [lintegral_smul_measure]
  have hstep : ∀ j : ℕ, ∫⁻ s, κ s A ∂adjointOp (kpow κ j) φ = adjointOp (kpow κ (j + 1)) φ A :=
    fun j => by
      rw [← adjointOp_apply κ _ hA]
      have := adjoint_add (κ := κ) 1 j φ
      rw [kpow_one, add_comm] at this
      rw [this]
  simp_rw [hstep]
  rw [← ENNReal.tsum_mul_left]
  calc ∑' j : ℕ, ((2 : ℝ≥0∞) ^ (j + 1))⁻¹ * adjointOp (kpow κ (j + 1)) φ A
      = ∑' j : ℕ, 2 * (((2 : ℝ≥0∞) ^ (j + 1 + 1))⁻¹ * adjointOp (kpow κ (j + 1)) φ A) := by
        congr 1; funext j
        rw [← mul_assoc, pow_succ _ (j + 1), ENNReal.mul_inv (by simp) (by simp), mul_comm 2,
          mul_assoc _ 2⁻¹, ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]
    _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective (f := Nat.succ) Nat.succ_injective
        (fun j => 2 * (((2 : ℝ≥0∞) ^ (j + 1))⁻¹ * adjointOp (kpow κ j) φ A))

omit [IsMarkovKernel κ] in
theorem adjoint_kpow_doeblinRef_le (φ : Measure S) (m : ℕ) :
    adjointOp (kpow κ m) (doeblinRef κ φ) ≤ ((2 : ℝ≥0∞) ^ m) • doeblinRef κ φ := by
  induction m with
  | zero => rw [adjointOp_kpow_zero, pow_zero, one_smul]
  | succ m ih =>
    rw [adjoint_add, kpow_one]
    calc adjointOp (kpow κ m) (adjointOp κ (doeblinRef κ φ)) ≤
          adjointOp (kpow κ m) ((2 : ℝ≥0∞) • doeblinRef κ φ) :=
          adjointOp_mono _ (adjoint_doeblinRef_le φ)
      _ = (2 : ℝ≥0∞) • adjointOp (kpow κ m) (doeblinRef κ φ) := adjointOp_smul _ _ _
      _ ≤ (2 : ℝ≥0∞) • ((2 : ℝ≥0∞) ^ m • doeblinRef κ φ) := Measure.le_iff'.2 fun A => by
          simp only [Measure.smul_apply, smul_eq_mul]
          gcongr; exact Measure.le_iff'.1 ih A
      _ = ((2 : ℝ≥0∞) ^ (m + 1)) • doeblinRef κ φ := by rw [smul_smul, pow_succ, mul_comm]

/-! ### Uniform integrability -/

omit [IsMarkovKernel κ] in
/-- Condition D forces `ε ≤ 1`. -/
theorem doeblin_eps_le_one [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ}
    (hD : DoeblinFor κ φ N ε) : ε ≤ 1 := by
  obtain ⟨s⟩ := ‹Nonempty S›
  have := hD.2.2.2 ∅ MeasurableSet.empty (by simp only [measureReal_empty]; exact hD.2.2.1.le) s
  simp only [measureReal_empty] at this
  linarith

/-- The constants `b_j = Σ_{i<j} (2/ε) 2^{Ni}`. -/
noncomputable def refBound (N : ℕ) (ε : ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, 2 / ε * 2 ^ (N * i)

theorem refBound_nonneg {N : ℕ} {ε : ℝ} (hε : 0 < ε) (j : ℕ) : 0 ≤ refBound N ε j :=
  Finset.sum_nonneg fun i _ => by positivity

/-- **Uniform integrability.** Under Condition D, for `μ` of mass at most one,
`μP^{Nj}(A) ≤ b_j ψ(A) + (1 − ε)ʲ μ(S)`. -/
theorem adjoint_real_le_ref [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ}
    (hD : DoeblinFor κ φ N ε) (j : ℕ) :
    ∀ (μ : Measure S) [IsFiniteMeasure μ], μ.real univ ≤ 1 → ∀ A, MeasurableSet A →
      (adjointOp (kpow κ (N * j)) μ).real A ≤
        refBound N ε j * (doeblinRef κ φ).real A + (1 - ε) ^ j * μ.real univ := by
  have hφ := hD.1
  have hε := hD.2.2.1
  have hε1 := doeblin_eps_le_one hD
  have hψ := isFinite_doeblinRef (κ := κ) φ
  induction j with
  | zero =>
    intro μ _ _ A _
    simp only [mul_zero, adjointOp_kpow_zero, refBound, Finset.range_zero, Finset.sum_empty,
      zero_mul, pow_zero, one_mul, zero_add]
    exact measureReal_mono (subset_univ A)
  | succ j ih =>
    intro μ _ hμ A hA
    set ψ := doeblinRef κ φ
    set c : ℝ≥0∞ := ENNReal.ofReal (2 / ε)
    set ν := adjointOp (kpow κ N) μ
    have hν : IsFiniteMeasure ν := isFinite_adjoint N μ
    have hνu : ν.real univ = μ.real univ := by
      rw [measureReal_def, adjointOp_kpow_univ]; rfl
    have hcψfin : IsFiniteMeasure (c • ψ) := ⟨by
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top ψ univ)⟩
    obtain ⟨H, hH, hH1, hH2⟩ := hahn_decomposition ν (c • ψ)
    -- `ψ(H) ≤ ε/2`, hence `φ(H) ≤ ε` and `ν(H) ≤ (1 − ε) μ(S)`
    have hcψ : (2 / ε) * ψ.real H ≤ 1 := by
      have h1 := hH1 H hH subset_rfl
      have h2 : (c • ψ).real H ≤ ν.real H := ENNReal.toReal_mono (measure_ne_top _ _) h1
      rw [measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal (by positivity)] at h2
      linarith [measureReal_mono (μ := ν) (subset_univ H)]
    have hφH : φ.real H ≤ ε := by
      have h1 : φ.real H ≤ ((2 : ℝ≥0∞) • ψ).real H :=
        ENNReal.toReal_mono (by
          rw [Measure.smul_apply, smul_eq_mul]
          exact ENNReal.mul_ne_top (by simp) (measure_ne_top ψ H)) (le_two_doeblinRef φ H)
      rw [measureReal_ennreal_smul_apply] at h1
      have : (2 : ℝ≥0∞).toReal = 2 := by simp
      rw [this] at h1
      have h2 : ψ.real H ≤ ε / 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hε] at hcψ; linarith
      linarith
    have hνH : ν.real H ≤ (1 - ε) * μ.real univ := by
      have := isMarkov_kpow (κ := κ) N
      rw [bind_real_eq _ _ hH]
      calc ∫ s, (kpow κ N s).real H ∂μ ≤ ∫ _s, (1 - ε) ∂μ :=
            integral_mono (integrable_of_abs_le μ (Kernel.measurable_coe _ hH).ennreal_toReal
              (C := 1) fun s => by
                rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
              (integrable_const _) fun s => hD.2.2.2 H hH hφH s
        _ = (1 - ε) * μ.real univ := by rw [integral_const, smul_eq_mul, mul_comm]
    -- the two pieces
    set R := ν.restrict H
    set K := ν.restrict Hᶜ
    have hsplit : ν = R + K := (Measure.restrict_add_restrict_compl hH).symm
    have hK : K ≤ c • ψ := Measure.le_iff.2 fun t ht => by
      rw [Measure.restrict_apply ht]
      exact (hH2 _ (ht.inter hH.compl) inter_subset_right).trans
        (measure_mono inter_subset_left)
    have hRu : R.real univ = ν.real H := by
      rw [measureReal_restrict_apply MeasurableSet.univ, univ_inter]
    have hKbound : (adjointOp (kpow κ (N * j)) K).real A ≤
        2 / ε * 2 ^ (N * j) * ψ.real A := by
      have h1 : adjointOp (kpow κ (N * j)) K ≤ (c * 2 ^ (N * j)) • ψ := by
        calc adjointOp (kpow κ (N * j)) K ≤ adjointOp (kpow κ (N * j)) (c • ψ) :=
              adjointOp_mono _ hK
          _ = c • adjointOp (kpow κ (N * j)) ψ := adjointOp_smul _ _ _
          _ ≤ c • ((2 : ℝ≥0∞) ^ (N * j) • ψ) := Measure.le_iff'.2 fun B => by
              simp only [Measure.smul_apply, smul_eq_mul]
              gcongr; exact Measure.le_iff'.1 (adjoint_kpow_doeblinRef_le φ (N * j)) B
          _ = (c * 2 ^ (N * j)) • ψ := smul_smul _ _ _
      have h2 := ENNReal.toReal_mono (by
          rw [Measure.smul_apply, smul_eq_mul]
          exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp))
            (measure_ne_top ψ A))
        (Measure.le_iff'.1 h1 A)
      have hfin : IsFiniteMeasure (adjointOp (kpow κ (N * j)) K) := isFinite_adjoint _ K
      rw [← measureReal_def, ← measureReal_def, measureReal_ennreal_smul_apply,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h2
      simpa using h2
    have hRbound := ih R (by rw [hRu]; linarith [measureReal_mono (μ := ν) (subset_univ H)]) A hA
    rw [show N * (j + 1) = N * j + N by ring, adjoint_add]
    change (adjointOp (kpow κ (N * j)) ν).real A ≤ _
    have : IsFiniteMeasure (adjointOp (kpow κ (N * j)) R) := isFinite_adjoint _ R
    have : IsFiniteMeasure (adjointOp (kpow κ (N * j)) K) := isFinite_adjoint _ K
    rw [hsplit, adjointOp_add, measureReal_add_apply (h₁ := measure_ne_top _ _)
      (h₂ := measure_ne_top _ _)]
    have hpow : 0 ≤ (1 - ε) ^ j := pow_nonneg (by linarith) j
    have : (1 - ε) ^ j * R.real univ ≤ (1 - ε) ^ (j + 1) * μ.real univ := by
      rw [hRu, pow_succ, mul_assoc]; exact mul_le_mul_of_nonneg_left hνH hpow
    simp only [refBound, Finset.sum_range_succ] at hRbound ⊢
    nlinarith [measureReal_nonneg (μ := ψ) (s := A)]

/-- The Cesàro averages are uniformly absolutely continuous with respect to `ψ`. -/
theorem cesaro_small [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ} (hD : DoeblinFor κ φ N ε)
    (μ : Measure S) [IsProbabilityMeasure μ] {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ n₀, ∀ n ≥ n₀, ∀ A, MeasurableSet A → (doeblinRef κ φ).real A ≤ δ →
      (cesaroM κ n μ).real A ≤ η := by
  have hε := hD.2.2.1
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < η / 3)
    (by linarith : 1 - ε < 1)
  set b := refBound N ε j
  have hb := refBound_nonneg (N := N) hε j
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (3 * (N * j) / η)
  refine ⟨η / 3 / (b + 1), by positivity, n₀, fun n hn A hA hψA => ?_⟩
  have hterm : ∀ k, (adjointOp (kpow κ (k + 1)) μ).real A ≤
      2 * η / 3 + if k + 1 < N * j then 1 else 0 := fun k => by
    split_ifs with hk
    · have := isProb_adjoint (κ := κ) (k + 1) μ
      have : (adjointOp (kpow κ (k + 1)) μ).real A ≤ 1 := measureReal_le_one
      linarith
    · obtain ⟨m, hm⟩ : ∃ m, k + 1 = N * j + m := ⟨k + 1 - N * j, by omega⟩
      have := isProb_adjoint (κ := κ) m μ
      rw [hm, adjoint_add]
      have h1 := adjoint_real_le_ref hD j (adjointOp (kpow κ m) μ) (by simp) A hA
      simp only [probReal_univ, mul_one] at h1
      have h2 : b * (doeblinRef κ φ).real A ≤ η / 3 := by
        calc b * (doeblinRef κ φ).real A ≤ (b + 1) * (η / 3 / (b + 1)) :=
              mul_le_mul (by linarith) hψA measureReal_nonneg (by positivity)
          _ = η / 3 := by
              have hb1 : b + 1 ≠ 0 := by positivity
              field_simp
      linarith
  rw [cesaroM_real]
  have hsum : ∑ k ∈ Finset.range (n + 1), (adjointOp (kpow κ (k + 1)) μ).real A ≤
      (n + 1) * (2 * η / 3) + N * j := by
    calc ∑ k ∈ Finset.range (n + 1), (adjointOp (kpow κ (k + 1)) μ).real A ≤
          ∑ k ∈ Finset.range (n + 1), (2 * η / 3 + if k + 1 < N * j then (1 : ℝ) else 0) :=
          Finset.sum_le_sum fun k _ => hterm k
      _ = (n + 1) * (2 * η / 3) + ∑ k ∈ Finset.range (n + 1),
            (if k + 1 < N * j then (1 : ℝ) else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast; ring
      _ ≤ (n + 1) * (2 * η / 3) + N * j := by
          gcongr
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
            mul_one]
          have : ((Finset.range (n + 1)).filter fun k => k + 1 < N * j) ⊆
              Finset.range (N * j) := fun k hk => by
            simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢; omega
          have := Finset.card_le_card this
          rw [Finset.card_range] at this
          exact_mod_cast this
  have hn' : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hNj : (N : ℝ) * j ≤ η / 3 * (n + 1) := by
    have := (div_lt_iff₀ hη).1 hn₀
    nlinarith
  calc ((n : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (n + 1), (adjointOp (kpow κ (k + 1)) μ).real A ≤
        ((n : ℝ) + 1)⁻¹ * ((n + 1) * (2 * η / 3) + N * j) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ ((n : ℝ) + 1)⁻¹ * ((n + 1) * (2 * η / 3) + η / 3 * (n + 1)) := by gcongr
    _ = η := by field_simp; ring

/-! ### Discretising integrals -/

omit [MeasurableSpace S] in
/-- `|g(s) − (1/k) #{i < k : (i+1)/k < g(s)}| ≤ 1/k` for `0 ≤ g(s) ≤ 1`. -/
theorem abs_sub_levels_le {g : S → ℝ} {k : ℕ} (hk : 0 < k) (s : S) (h0 : 0 ≤ g s)
    (h1 : g s ≤ 1) :
    |g s - (k : ℝ)⁻¹ * ∑ i ∈ Finset.range k,
      {x | ((i : ℝ) + 1) / k < g x}.indicator (1 : S → ℝ) s| ≤ (k : ℝ)⁻¹ := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set x := (k : ℝ) * g s
  have hx0 : 0 ≤ x := by positivity
  have hxk : x ≤ k := by
    calc x ≤ (k : ℝ) * 1 := mul_le_mul_of_nonneg_left h1 hk'.le
      _ = k := mul_one _
  set m := ⌈x⌉₊
  have hmk : m ≤ k := Nat.ceil_le.2 hxk
  have hcount : ∑ i ∈ Finset.range k, {x | ((i : ℝ) + 1) / k < g x}.indicator (1 : S → ℝ) s =
      ((m - 1 : ℕ) : ℝ) := by
    have hfilt : (Finset.range k).filter (fun i : ℕ => ((i : ℝ) + 1) / k < g s) =
        Finset.range (m - 1) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      rw [div_lt_iff₀ hk', mul_comm]
      have : ((i : ℝ) + 1 < x) ↔ i + 1 < m := by
        rw [Nat.lt_ceil]; push_cast; rfl
      rw [this]
      omega
    rw [← Finset.card_range (m - 1), ← hfilt, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : ((i : ℝ) + 1) / k < g s
    · simp only [indicator_of_mem (show s ∈ {x | ((i : ℝ) + 1) / k < g x} from hi), hi,
        ↓reduceIte, Pi.one_apply]
    · simp only [indicator_of_notMem (show s ∉ {x | ((i : ℝ) + 1) / k < g x} from hi), hi,
        ↓reduceIte]
  rw [hcount]
  have hxm : x ≤ m := Nat.le_ceil x
  have hmx : (m : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  have key : |x - ((m - 1 : ℕ) : ℝ)| ≤ 1 := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · rw [hm] at hxm ⊢
      simp only [Nat.zero_sub, sub_zero, CharP.cast_eq_zero] at hxm ⊢
      rw [abs_of_nonneg hx0]; linarith
    · rw [Nat.cast_sub hm, Nat.cast_one, abs_le]
      constructor <;> linarith
  have : g s - (k : ℝ)⁻¹ * ((m - 1 : ℕ) : ℝ) = (k : ℝ)⁻¹ * (x - ((m - 1 : ℕ) : ℝ)) := by
    simp only [x]; field_simp
  rw [this, abs_mul, abs_of_pos (inv_pos.2 hk')]
  exact (mul_le_mul_of_nonneg_left key (inv_pos.2 hk').le).trans (le_of_eq (mul_one _))

/-- `|∫ g dμ − (1/k) Σ_{i<k} μ{(i+1)/k < g}| ≤ 1/k` for `0 ≤ g ≤ 1` and a probability `μ`. -/
theorem abs_integral_sub_levels_le (μ : Measure S) [IsProbabilityMeasure μ] {g : S → ℝ}
    (hg : Measurable g) (h01 : ∀ s, 0 ≤ g s ∧ g s ≤ 1) {k : ℕ} (hk : 0 < k) :
    |∫ s, g s ∂μ - (k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, μ.real {x | ((i : ℝ) + 1) / k < g x}| ≤
      (k : ℝ)⁻¹ := by
  have hmeas : ∀ i : ℕ, MeasurableSet {x | ((i : ℝ) + 1) / k < g x} := fun i =>
    measurableSet_lt measurable_const hg
  have hint : ∀ i : ℕ, Integrable ({x | ((i : ℝ) + 1) / k < g x}.indicator (1 : S → ℝ)) μ :=
    fun i => (integrable_const 1).indicator (hmeas i)
  have hD : ∫ s, (k : ℝ)⁻¹ * ∑ i ∈ Finset.range k,
      {x | ((i : ℝ) + 1) / k < g x}.indicator (1 : S → ℝ) s ∂μ =
        (k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, μ.real {x | ((i : ℝ) + 1) / k < g x} := by
    rw [integral_const_mul, integral_finsetSum _ fun i _ => hint i]
    simp only [integral_indicator_one (hmeas _)]
  have hgi : Integrable g μ := integrable_of_abs_le μ hg (C := 1) fun s => by
    rw [abs_of_nonneg (h01 s).1]; exact (h01 s).2
  have hDi : Integrable (fun s => (k : ℝ)⁻¹ * ∑ i ∈ Finset.range k,
      {x | ((i : ℝ) + 1) / k < g x}.indicator (1 : S → ℝ) s) μ :=
    (integrable_finsetSum _ fun i _ => hint i).const_mul _
  rw [← hD, ← integral_sub hgi hDi]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ s, |g s - (k : ℝ)⁻¹ * ∑ i ∈ Finset.range k,
        {x | ((i : ℝ) + 1) / k < g x}.indicator (1 : S → ℝ) s| ∂μ ≤ ∫ _s, (k : ℝ)⁻¹ ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun s => abs_nonneg _)
          (integrable_const _) (Eventually.of_forall fun s =>
            abs_sub_levels_le hk s (h01 s).1 (h01 s).2)
    _ = (k : ℝ)⁻¹ := by simp

/-! ### The ultrafilter limit -/

theorem hyperfilter_le_atTop : (hyperfilter ℕ : Filter ℕ) ≤ atTop :=
  hyperfilter_le_cofinite.trans Nat.cofinite_eq_atTop.le

variable (κ) in
/-- The limit of the Cesàro averages on `A` along a non-principal ultrafilter. -/
noncomputable def cesaroLim (μ : Measure S) (A : Set S) : ℝ :=
  limUnder (hyperfilter ℕ : Filter ℕ) fun n => (cesaroM κ n μ).real A

/-- Bounded sequences converge along an ultrafilter. -/
theorem tendsto_ultra_of_mem {u : ℕ → ℝ} (hu : ∀ n, u n ∈ Icc (0 : ℝ) 1) :
    Tendsto u (hyperfilter ℕ) (𝓝 (limUnder (hyperfilter ℕ : Filter ℕ) u)) := by
  refine tendsto_nhds_limUnder ?_
  obtain ⟨x, -, hx⟩ := isCompact_iff_ultrafilter_le_nhds.1 isCompact_Icc
    ((hyperfilter ℕ).map u) (by
      rw [Ultrafilter.coe_map, le_principal_iff, mem_map]
      exact Filter.univ_mem' fun n => hu n)
  exact ⟨x, by rwa [Ultrafilter.coe_map] at hx⟩

theorem tendsto_cesaroLim (μ : Measure S) [IsProbabilityMeasure μ] (A : Set S) :
    Tendsto (fun n => (cesaroM κ n μ).real A) (hyperfilter ℕ) (𝓝 (cesaroLim κ μ A)) :=
  tendsto_ultra_of_mem fun n => by
    have := isProb_cesaroM (κ := κ) n μ
    exact ⟨measureReal_nonneg, measureReal_le_one⟩

/-- Sequences tending to a limit at infinity tend to it along the ultrafilter. -/
theorem tendsto_ultra {u : ℕ → ℝ} {a : ℝ} (h : Tendsto u atTop (𝓝 a)) :
    Tendsto u (hyperfilter ℕ) (𝓝 a) := h.mono_left hyperfilter_le_atTop

theorem cesaroLim_union (μ : Measure S) [IsProbabilityMeasure μ] {A B : Set S}
    (hd : Disjoint A B) (hB : MeasurableSet B) :
    cesaroLim κ μ (A ∪ B) = cesaroLim κ μ A + cesaroLim κ μ B := by
  refine tendsto_nhds_unique (tendsto_cesaroLim μ (A ∪ B)) ?_
  have := (tendsto_cesaroLim (κ := κ) μ A).add (tendsto_cesaroLim (κ := κ) μ B)
  refine this.congr fun n => ?_
  have := isProb_cesaroM (κ := κ) n μ
  exact (measureReal_union hd hB).symm

theorem cesaroLim_nonneg (μ : Measure S) [IsProbabilityMeasure μ] (A : Set S) :
    0 ≤ cesaroLim κ μ A :=
  ge_of_tendsto (tendsto_cesaroLim μ A) (Eventually.of_forall fun _ => measureReal_nonneg)

theorem cesaroLim_univ (μ : Measure S) [IsProbabilityMeasure μ] : cesaroLim κ μ univ = 1 := by
  refine tendsto_nhds_unique (tendsto_cesaroLim μ univ) ?_
  refine tendsto_const_nhds.congr fun n => ?_
  have := isProb_cesaroM (κ := κ) n μ
  exact probReal_univ.symm

theorem cesaroLim_empty (μ : Measure S) [IsProbabilityMeasure μ] : cesaroLim κ μ ∅ = 0 := by
  refine tendsto_nhds_unique (tendsto_cesaroLim μ ∅) ?_
  exact tendsto_const_nhds.congr fun _ => by simp

/-- The limit is countably additive, by uniform absolute continuity. -/
theorem hasSum_cesaroLim [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ} (hD : DoeblinFor κ φ N ε)
    (μ : Measure S) [IsProbabilityMeasure μ] {f : ℕ → Set S} (hf : ∀ i, MeasurableSet (f i))
    (hd : Pairwise (Function.onFun Disjoint f)) :
    HasSum (fun i => cesaroLim κ μ (f i)) (cesaroLim κ μ (⋃ i, f i)) := by
  have hφ := hD.1
  have hψ := isFinite_doeblinRef (κ := κ) φ
  set P : ℕ → Set S := fun n => ⋃ i ∈ Finset.range n, f i
  have hPm : ∀ n, MeasurableSet (P n) := fun n =>
    Finset.measurableSet_biUnion _ fun i _ => hf i
  have hPsum : ∀ n, cesaroLim κ μ (P n) = ∑ i ∈ Finset.range n, cesaroLim κ μ (f i) := by
    intro n
    refine tendsto_nhds_unique (tendsto_cesaroLim μ (P n)) ?_
    refine (tendsto_finsetSum _ fun i _ => tendsto_cesaroLim (κ := κ) μ (f i)).congr fun m => ?_
    have := isProb_cesaroM (κ := κ) m μ
    exact (measureReal_biUnion_finset (fun i _ j _ hij => hd hij) fun i _ => hf i).symm
  set T : ℕ → Set S := fun n => (⋃ i, f i) \ P n
  have hTsplit : ∀ n, cesaroLim κ μ (⋃ i, f i) = cesaroLim κ μ (P n) + cesaroLim κ μ (T n) := by
    intro n
    rw [← cesaroLim_union μ disjoint_sdiff_right ((MeasurableSet.iUnion hf).diff (hPm n))]
    congr 1
    exact (union_sdiff_cancel (iUnion₂_subset fun i _ => subset_iUnion f i)).symm
  -- `ψ(Tₙ) → 0`
  have hPmono : Monotone P := fun m n hmn => biUnion_subset_biUnion_left fun i hi => by
    simp only [Finset.coe_range, mem_Iio] at hi ⊢; omega
  have hPU : (⋃ n, P n) = ⋃ i, f i := by
    ext x; simp only [P, mem_iUnion, Finset.mem_range]
    exact ⟨fun ⟨n, i, _, hx⟩ => ⟨i, hx⟩, fun ⟨i, hx⟩ => ⟨i + 1, i, by omega, hx⟩⟩
  have hψT : Tendsto (fun n => (doeblinRef κ φ).real (T n)) atTop (𝓝 0) := by
    have h1 := tendsto_measure_iUnion_atTop (μ := doeblinRef κ φ) hPmono
    rw [hPU] at h1
    have h2 := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h1
    have h3 := h2.const_sub ((doeblinRef κ φ).real (⋃ i, f i))
    rw [show ((doeblinRef κ φ) (⋃ i, f i)).toReal = (doeblinRef κ φ).real (⋃ i, f i) from rfl,
      sub_self] at h3
    refine h3.congr fun n => ?_
    simp only [Function.comp_apply, T]
    rw [measureReal_sdiff (iUnion₂_subset fun i _ => subset_iUnion f i) (hPm n)]
    rfl
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun i => cesaroLim_nonneg μ _)]
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨δ, hδ, n₀, hsmall⟩ := cesaro_small hD μ (half_pos hη)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 ((hψT.eventually (gt_mem_nhds hδ)))
  refine ⟨N₁, fun n hn => ?_⟩
  have hTle : cesaroLim κ μ (T n) ≤ η / 2 := by
    refine le_of_tendsto (tendsto_cesaroLim μ (T n)) ?_
    refine (Filter.eventually_ge_atTop n₀).filter_mono hyperfilter_le_atTop |>.mono fun m hm => ?_
    exact hsmall m hm (T n) ((MeasurableSet.iUnion hf).diff (hPm n)) (hN₁ n hn).le
  rw [Real.dist_eq, ← hPsum, hTsplit n]
  rw [abs_sub_comm, add_sub_cancel_left, abs_of_nonneg (cesaroLim_nonneg μ _)]
  linarith

omit [IsMarkovKernel κ] in
/-- `T*` commutes with the Cesàro averages. -/
theorem adjoint_cesaroM (n : ℕ) (μ : Measure S) :
    adjointOp κ (cesaroM κ n μ) = cesaroM κ n (adjointOp (kpow κ 1) μ) := by
  simp only [cesaroM, adjointOp_smul, adjointOp_finsetSum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 := adjoint_add (κ := κ) 1 (k + 1) μ
  have h2 := adjoint_add (κ := κ) (k + 1) 1 μ
  rw [kpow_one] at h1
  rw [← h1, ← h2, add_comm]

/-- Integrals of `[0, 1]`-valued functions converge along the ultrafilter. -/
theorem tendsto_integral_ultra (μ : Measure S) [IsProbabilityMeasure μ] {π : Measure S}
    [IsProbabilityMeasure π] (hπ : ∀ A, MeasurableSet A → π.real A = cesaroLim κ μ A)
    {g : S → ℝ} (hg : Measurable g) (h01 : ∀ s, 0 ≤ g s ∧ g s ≤ 1) :
    Tendsto (fun n => ∫ s, g s ∂cesaroM κ n μ) (hyperfilter ℕ) (𝓝 (∫ s, g s ∂π)) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨k, hk⟩ := exists_nat_gt (3 / η)
  have hk0 : 0 < k := by
    have : (0 : ℝ) < k := lt_trans (by positivity) hk
    exact_mod_cast this
  have hkη : 3 * (k : ℝ)⁻¹ < η := by
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
    rw [div_lt_iff₀ hη] at hk
    rw [← div_eq_mul_inv, div_lt_iff₀ hk']; linarith
  set G : ℕ → Set S := fun i => {x | ((i : ℝ) + 1) / k < g x}
  have hG : ∀ i, MeasurableSet (G i) := fun i => measurableSet_lt measurable_const hg
  have happrox : Tendsto (fun n => (k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, (cesaroM κ n μ).real (G i))
      (hyperfilter ℕ) (𝓝 ((k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, π.real (G i))) := by
    simp only [fun i => hπ (G i) (hG i)]
    exact (tendsto_finsetSum _ fun i _ => tendsto_cesaroLim μ (G i)).const_mul _
  filter_upwards [happrox.eventually (Metric.ball_mem_nhds _ (inv_pos.2
    (show (0 : ℝ) < k by exact_mod_cast hk0)))] with n hn
  have := isProb_cesaroM (κ := κ) n μ
  have e1 := abs_integral_sub_levels_le (cesaroM κ n μ) hg h01 hk0
  have e2 := abs_integral_sub_levels_le π hg h01 hk0
  rw [Real.dist_eq] at hn
  rw [Real.dist_eq]
  calc |∫ s, g s ∂cesaroM κ n μ - ∫ s, g s ∂π| ≤ (k : ℝ)⁻¹ + (k : ℝ)⁻¹ + (k : ℝ)⁻¹ := by
        rw [abs_le] at e1 e2 ⊢
        rw [abs_lt] at hn
        constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, hn.1, hn.2]
    _ < η := by linarith

/-- **Existence of invariant measures under Condition D.** Every probability measure `λ` yields
an invariant probability measure `π`, the limit of its Cesàro averages along a non-principal
ultrafilter on each measurable set. -/
theorem exists_invariant [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ} (hD : DoeblinFor κ φ N ε)
    (μ : Measure S) [IsProbabilityMeasure μ] :
    ∃ π : Measure S, IsProbabilityMeasure π ∧ adjointOp κ π = π ∧
      ∀ A, MeasurableSet A → π.real A = cesaroLim κ μ A := by
  set π : Measure S := Measure.ofMeasurable (fun A _ => ENNReal.ofReal (cesaroLim κ μ A))
    (by simp [cesaroLim_empty]) fun f hf hd => by
      have h := hasSum_cesaroLim hD μ hf hd
      rw [← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun i => cesaroLim_nonneg μ _) h.summable]
  have hπA : ∀ A, MeasurableSet A → π A = ENNReal.ofReal (cesaroLim κ μ A) := fun A hA =>
    Measure.ofMeasurable_apply A hA
  have hprob : IsProbabilityMeasure π :=
    ⟨by rw [hπA univ MeasurableSet.univ, cesaroLim_univ, ENNReal.ofReal_one]⟩
  have hπr : ∀ A, MeasurableSet A → π.real A = cesaroLim κ μ A := fun A hA => by
    rw [measureReal_def, hπA A hA, ENNReal.toReal_ofReal (cesaroLim_nonneg μ A)]
  refine ⟨π, hprob, ?_, hπr⟩
  have hPfin : IsFiniteMeasure (adjointOp κ π) := by
    have := isFinite_adjoint (κ := κ) 1 π; rwa [kpow_one] at this
  refine Measure.ext fun A hA => ?_
  have hreal : (adjointOp κ π).real A = π.real A := by
    set g : S → ℝ := fun s => (κ s).real A
    have hg : Measurable g := (κ.measurable_coe hA).ennreal_toReal
    have h01 : ∀ s, 0 ≤ g s ∧ g s ≤ 1 := fun s => ⟨measureReal_nonneg, measureReal_le_one⟩
    rw [bind_real_eq κ π hA, hπr A hA]
    refine tendsto_nhds_unique (tendsto_integral_ultra μ hπr hg h01) ?_
    -- `∫ g dλₙ = (T*λₙ)(A)`, within `1/(n+1)` of `λₙ(A)`
    have hsh : Tendsto (fun n => (cesaroM κ n (adjointOp (kpow κ 1) μ)).real A -
        (cesaroM κ n μ).real A) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => ?_) (tendsto_one_div_add_atTop_nhds_zero_nat)
      rw [Real.norm_eq_abs]
      refine (abs_cesaro_shift_le n 1 μ A).trans (le_of_eq ?_)
      simp [div_eq_mul_inv]
    have := (tendsto_ultra hsh).add (tendsto_cesaroLim (κ := κ) μ A)
    rw [zero_add] at this
    refine this.congr fun n => ?_
    have := isFinite_cesaroM (κ := κ) n μ
    rw [sub_add_cancel, ← adjoint_cesaroM, bind_real_eq κ _ hA]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 hreal

end StokeyLucasPrescott.StrongConvergence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Theorems 11.9b–c and 11.10b–c

The book states these and refers to Doob (1953, §V.5) and Neveu (1965, §V.3) for proofs. The
proof here combines the preceding modules.

1. Measures absolutely continuous with respect to an invariant probability measure `π` have
   uniformly Cauchy Cesàro averages (`cesaroCauchy_of_absCont`): truncate the density and use
   the mean ergodic theorem for bounded densities.
2. Every finite measure concentrated on an ergodic set `E` does
   (`cesaroCauchy_of_concentrated`). By the Lebesgue decomposition with respect to `φ`,
   `μPᴺ = K + R` with `K ≪ φ` (hence `K ≪ π_E`) and `R` singular. Doeblin's condition applied
   to a `φ`-null set carrying `R` gives `R(S) ≤ (1 − ε)μ(S)`. Iterating, `μP^{Nj}` is a good
   measure plus one of mass at most `(1 − ε)ʲμ(S)`.
3. **Absorption** (`tendsto_kpow_transient`): from every state the probability of being in the
   transient set `F = (⋃ₘ Eₘ)ᶜ` tends to `0`. The limit `g = lim Pⁿ(·, F)` is harmonic; if
   `γ = sup g > 0`, the set `{g = γ}` is invariant with `φ`-measure at least `ε`. So it contains
   an ergodic set, which must agree with some `Eₘ`, where `g = 0`.
4. Hence every finite measure has uniformly Cauchy averages, which gives Theorem 11.9b; part (c)
   and Theorem 11.10b–c follow from uniqueness on each ergodic set (`invariant_unique`).
-/

namespace StokeyLucasPrescott.StrongConvergence

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

variable {S : Type*} [MeasurableSpace S] {κ : Kernel S S} [IsMarkovKernel κ]

/-! ### Absolutely continuous measures -/

/-- Truncations `min f n` of a function increase to it. -/
theorem iSup_min_natCast (x : ℝ≥0∞) : ⨆ n : ℕ, min x (n : ℝ≥0∞) = x := by
  refine le_antisymm (iSup_le fun n => min_le_left _ _) ?_
  rcases eq_or_ne x ⊤ with rfl | hx
  · simp only [min_eq_right le_top]
    exact le_of_eq ENNReal.iSup_natCast.symm
  · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hx
    exact le_iSup_of_le n (le_of_eq (min_eq_left hn.le).symm)

/-- **Step 1.** A finite measure absolutely continuous with respect to an invariant probability
measure has uniformly Cauchy Cesàro averages. -/
theorem cesaroCauchy_of_absCont {π : Measure S} [IsProbabilityMeasure π]
    (hπ : adjointOp κ π = π) {ν : Measure S} [IsFiniteMeasure ν] (hν : ν ≪ π) :
    CesaroCauchy κ ν := by
  set f := ν.rnDeriv π
  have hfm : Measurable f := Measure.measurable_rnDeriv ν π
  have hνf : π.withDensity f = ν := Measure.withDensity_rnDeriv_eq ν π hν
  have hint : ∫⁻ s, f s ∂π ≠ ⊤ := by
    have : (π.withDensity f) univ = ∫⁻ s, f s ∂π := by
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← this, hνf]
    exact measure_ne_top ν univ
  -- the truncations converge in mass
  have htend : Tendsto (fun n : ℕ => ∫⁻ s, min (f s) n ∂π) atTop (𝓝 (∫⁻ s, f s ∂π)) := by
    have hmono : Monotone fun (n : ℕ) (s : S) => min (f s) (n : ℝ≥0∞) := fun m n hmn s =>
      min_le_min_left _ (by exact_mod_cast hmn)
    have := lintegral_iSup (μ := π) (fun n => hfm.min measurable_const) hmono
    simp only [iSup_min_natCast] at this
    rw [this]
    exact tendsto_atTop_iSup fun m n hmn => lintegral_mono fun s =>
      min_le_min_left _ (by exact_mod_cast hmn)
  refine cesaroCauchy_of_approx fun η hη => ?_
  have hev := (ENNReal.tendsto_toReal hint).comp htend
  obtain ⟨n, hn⟩ := ((hev.const_sub (∫⁻ s, f s ∂π).toReal).eventually
    (gt_mem_nhds (show (∫⁻ s, f s ∂π).toReal - (∫⁻ s, f s ∂π).toReal < η by
      rw [sub_self]; exact hη))).exists
  simp only [Function.comp_apply] at hn
  -- the bounded part and the remainder
  set H : S → ℝ≥0 := fun s => (min (f s) n).toNNReal
  have hH : Measurable H := (hfm.min measurable_const).ennreal_toNNReal
  have hHb : ∀ s, H s ≤ n := fun s => by
    simp only [H]
    rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (ne_top_of_le_ne_top
      (ENNReal.natCast_ne_top n) (min_le_right _ _))]
    exact_mod_cast min_le_right _ _
  have hHf : ∀ s, (H s : ℝ≥0∞) = min (f s) n := fun s =>
    ENNReal.coe_toNNReal (ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (min_le_right _ _))
  set ν' := π.withDensity fun s => (H s : ℝ≥0∞)
  set ρ := π.withDensity fun s => f s - min (f s) n
  have hν'fin : IsFiniteMeasure ν' := isFiniteMeasure_withDensity_of_bound hHb
  have hsplit : ν = ν' + ρ := by
    rw [← hνf]
    simp only [ν', ρ, hHf]
    rw [← withDensity_add_left (hfm.min measurable_const)]
    congr 1
    funext s
    exact (add_tsub_cancel_of_le (min_le_left _ _)).symm
  have hρu : ρ univ = ∫⁻ s, f s ∂π - ∫⁻ s, min (f s) n ∂π := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      lintegral_sub (hfm.min measurable_const)
        (ne_top_of_le_ne_top hint (lintegral_mono fun s => min_le_left _ _))
        (Eventually.of_forall fun s => min_le_left _ _)]
  have hρfin : IsFiniteMeasure ρ := ⟨by
    rw [hρu]; exact lt_of_le_of_lt tsub_le_self (lt_top_iff_ne_top.2 hint)⟩
  refine ⟨0, ν', ρ, hν'fin, hρfin, by rw [adjointOp_kpow_zero, hsplit],
    cesaroCauchy_withDensity hπ hH hHb, ?_⟩
  rw [measureReal_def, hρu, ENNReal.toReal_sub_of_le
    (lintegral_mono fun s => min_le_left _ _) hint]
  linarith

/-! ### Measures concentrated on an ergodic set -/

/-- The step-`N` decomposition: `μPᴺ` is a measure absolutely continuous with respect to `φ`,
plus a measure of mass at most `(1 − ε) μ(S)`, both concentrated on `E` if `μ` is. -/
theorem doeblin_decomp {φ : Measure S} {N : ℕ} {ε : ℝ} (hD : DoeblinFor κ φ N ε) {E : Set S}
    (hE : IsInvariantSet κ E) (μ : Measure S) [IsFiniteMeasure μ] (hμE : μ Eᶜ = 0) :
    ∃ (K R : Measure S) (_ : IsFiniteMeasure K) (_ : IsFiniteMeasure R),
      adjointOp (kpow κ N) μ = K + R ∧ K ≪ φ ∧ K Eᶜ = 0 ∧ R Eᶜ = 0 ∧
        R.real univ ≤ (1 - ε) * μ.real univ := by
  have hφ := hD.1
  set ν := adjointOp (kpow κ N) μ
  have hν : IsFiniteMeasure ν := isFinite_adjoint N μ
  have := isMarkov_kpow (κ := κ) N
  have hνE : ν Eᶜ = 0 := by
    rw [adjointOp_apply _ _ hE.1.compl]
    have hae : ∀ᵐ s ∂μ, s ∈ E := by
      rw [ae_iff]; simpa [compl_def] using hμE
    rw [lintegral_congr_ae (g := fun _ => 0) (hae.mono fun s hs => by
      rw [prob_compl_eq_zero_iff hE.1]; exact hE.2.2 s hs N hD.2.1)]
    simp
  set K := φ.withDensity (ν.rnDeriv φ)
  set R := ν.singularPart φ
  have hKle : K ≤ ν := Measure.withDensity_rnDeriv_le ν φ
  have hRle : R ≤ ν := Measure.singularPart_le ν φ
  have hKfin : IsFiniteMeasure K :=
    ⟨lt_of_le_of_lt (Measure.le_iff'.1 hKle univ) (measure_lt_top ν univ)⟩
  have hRfin : IsFiniteMeasure R :=
    ⟨lt_of_le_of_lt (Measure.le_iff'.1 hRle univ) (measure_lt_top ν univ)⟩
  refine ⟨K, R, hKfin, hRfin, ?_, withDensity_absolutelyContinuous _ _,
    nonpos_iff_eq_zero.1 ((Measure.le_iff'.1 hKle _).trans hνE.le),
    nonpos_iff_eq_zero.1 ((Measure.le_iff'.1 hRle _).trans hνE.le), ?_⟩
  · rw [add_comm]; exact Measure.haveLebesgueDecomposition_add ν φ
  · -- `R` lives on a `φ`-null set `Z`
    have hsing := Measure.mutuallySingular_singularPart ν φ
    set Z := hsing.nullSetᶜ
    have hZ : MeasurableSet Z := hsing.measurableSet_nullSet.compl
    have hφZ : φ.real Z = 0 := by rw [measureReal_def, hsing.measure_compl_nullSet]; rfl
    have hRZ : R.real univ = R.real Z := by
      rw [← measureReal_add_measureReal_compl (μ := R) hZ, compl_compl,
        measureReal_def R hsing.nullSet, hsing.measure_nullSet]; simp
    have hνZ : ν.real Z ≤ (1 - ε) * μ.real univ := by
      rw [bind_real_eq _ _ hZ]
      calc ∫ s, (kpow κ N s).real Z ∂μ ≤ ∫ _s, (1 - ε) ∂μ :=
            integral_mono (integrable_of_abs_le μ (Kernel.measurable_coe _ hZ).ennreal_toReal
              (C := 1) fun s => by
                rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
              (integrable_const _) fun s => hD.2.2.2 Z hZ (by rw [hφZ]; exact hD.2.2.1.le) s
        _ = (1 - ε) * μ.real univ := by rw [integral_const, smul_eq_mul, mul_comm]
    rw [hRZ]
    exact (ENNReal.toReal_mono (measure_ne_top _ _) (Measure.le_iff'.1 hRle Z)).trans hνZ

/-- **Step 2.** Every finite measure concentrated on an ergodic set carrying an invariant
probability measure has uniformly Cauchy Cesàro averages. -/
theorem cesaroCauchy_of_concentrated {φ : Measure S} {N : ℕ} {ε : ℝ} (hD : DoeblinFor κ φ N ε)
    {E : Set S} (hE : IsErgodicSetD κ φ E) {π : Measure S} [IsProbabilityMeasure π]
    (hπ : adjointOp κ π = π) (hπE : π E = 1) (μ : Measure S) [IsFiniteMeasure μ]
    (hμE : μ Eᶜ = 0) : CesaroCauchy κ μ := by
  have hφ := hD.1
  have hε := hD.2.2.1
  have : Nonempty S := ⟨hE.1.2.1.some⟩
  have h1 : 0 ≤ 1 - ε := by linarith [doeblin_eps_le_one hD]
  -- the iterated decomposition
  have hiter : ∀ (j : ℕ) (μ : Measure S) [IsFiniteMeasure μ], μ Eᶜ = 0 →
      ∃ (G R : Measure S) (_ : IsFiniteMeasure G) (_ : IsFiniteMeasure R),
        adjointOp (kpow κ (N * j)) μ = G + R ∧ CesaroCauchy κ G ∧ R Eᶜ = 0 ∧
          R.real univ ≤ (1 - ε) ^ j * μ.real univ := by
    intro j
    induction j with
    | zero =>
      intro μ _ hμE
      exact ⟨0, μ, inferInstance, inferInstance, by rw [mul_zero, adjointOp_kpow_zero, zero_add],
        cesaroCauchy_zero, hμE, by simp⟩
    | succ j ih =>
      intro μ _ hμE
      obtain ⟨G, R, hG, hR, hdec, hGc, hRE, hRu⟩ := ih μ hμE
      obtain ⟨K, R', hK, hR', hdec', hKφ, hKE, hR'E, hR'u⟩ := doeblin_decomp hD hE.1 R hRE
      have := isFinite_adjoint (κ := κ) N G
      refine ⟨adjointOp (kpow κ N) G + K, R', inferInstance, hR', ?_,
        (cesaroCauchy_adjoint hGc N).add
          (cesaroCauchy_of_absCont hπ (absCont_of_concentrated hE hπ hπE hKφ hKE)), hR'E, ?_⟩
      · rw [show N * (j + 1) = N + N * j by ring, adjoint_add, hdec, adjointOp_add, hdec',
          add_assoc]
      · calc R'.real univ ≤ (1 - ε) * R.real univ := hR'u
          _ ≤ (1 - ε) * ((1 - ε) ^ j * μ.real univ) := mul_le_mul_of_nonneg_left hRu h1
          _ = (1 - ε) ^ (j + 1) * μ.real univ := by ring
  refine cesaroCauchy_of_approx fun η hη => ?_
  have hε1 : 1 - ε < 1 := by linarith
  · obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (show 0 < η / (μ.real univ + 1) by positivity) hε1
    obtain ⟨G, R, hG, hR, hdec, hGc, -, hRu⟩ := hiter j μ hμE
    refine ⟨N * j, G, R, hG, hR, hdec, hGc, hRu.trans ?_⟩
    have hμ0 := measureReal_nonneg (μ := μ) (s := univ)
    calc (1 - ε) ^ j * μ.real univ ≤ η / (μ.real univ + 1) * (μ.real univ + 1) :=
          mul_le_mul hj.le (by linarith) hμ0 (by positivity)
      _ = η := by field_simp

/-! ### Absorption into the ergodic sets -/

omit [IsMarkovKernel κ] in
theorem iInf_shift_antitone {a : ℕ → ℝ≥0∞} (ha : Antitone a) (m : ℕ) :
    ⨅ n, a (m + n) = ⨅ n, a n :=
  le_antisymm (le_iInf fun n => (iInf_le _ n).trans (ha (Nat.le_add_left n m)))
    (le_iInf fun n => iInf_le _ (m + n))

/-- **Absorption.** From every state, the probability of being in the transient set
`F = (⋃ₘ Eₘ)ᶜ` tends to `0`. -/
theorem tendsto_kpow_transient [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ}
    (hD : DoeblinFor κ φ N ε) {M : ℕ} {E : Fin M → Set S} (hE : ∀ m, IsErgodicSetD κ φ (E m))
    (hall : ∀ F, IsErgodicSetD κ φ F → ∃ m, φ (F ∩ E m) = φ F ∧ φ (F ∩ E m) = φ (E m))
    (s : S) : Tendsto (fun n => kpow κ n s (⋃ m, E m)ᶜ) atTop (𝓝 0) := by
  have hφ := hD.1
  have hε := hD.2.2.1
  set F := (⋃ m, E m)ᶜ
  have hF : MeasurableSet F := (MeasurableSet.iUnion fun m => (hE m).1.1).compl
  have hzero : ∀ m, ∀ t ∈ E m, ∀ n, kpow κ n t F = 0 := by
    intro m t ht n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [kpow, Kernel.id_apply]
      rw [Measure.dirac_apply' t hF, indicator_of_notMem
        (show t ∉ F from fun h => h (mem_iUnion.2 ⟨m, ht⟩))]
    · have := isMarkov_kpow (κ := κ) n
      have h1 := (hE m).1.2.2 t ht n hn
      have hsub : F ⊆ (E m)ᶜ := fun x hx hxm => hx (mem_iUnion.2 ⟨m, hxm⟩)
      refine measure_mono_null hsub ?_
      rw [prob_compl_eq_zero_iff (hE m).1.1]; exact h1
  have hstep : ∀ t, kpow κ 1 t F ≤ F.indicator 1 t := fun t => by
    have := isMarkov_kpow (κ := κ) 1
    by_cases ht : t ∈ F
    · rw [indicator_of_mem ht]; exact prob_le_one
    · obtain ⟨m, hm⟩ := mem_iUnion.1 (not_not.1 ht)
      rw [hzero m t hm 1]; exact zero_le
  have hanti : ∀ t, Antitone fun n => kpow κ n t F := fun t =>
    antitone_nat_of_succ_le fun n => by
      have := isMarkov_kpow (κ := κ) n
      rw [kpow_add_apply n 1 t hF]
      calc ∫⁻ s', kpow κ 1 s' F ∂kpow κ n t ≤ ∫⁻ s', F.indicator 1 s' ∂kpow κ n t :=
            lintegral_mono hstep
        _ = kpow κ n t F := lintegral_indicator_one hF
  set g : S → ℝ≥0∞ := fun t => ⨅ n, kpow κ n t F
  have hgm : Measurable g := Measurable.iInf fun n => Kernel.measurable_coe _ hF
  have hg1 : ∀ t, g t ≤ 1 := fun t => by
    have := isMarkov_kpow (κ := κ) 0
    exact (iInf_le _ 0).trans prob_le_one
  have hgE : ∀ m, ∀ t ∈ E m, g t = 0 := fun m t ht =>
    le_antisymm ((iInf_le _ 0).trans (le_of_eq (hzero m t ht 0))) zero_le
  -- `g` is harmonic
  have hharm : ∀ t m, g t = ∫⁻ t', g t' ∂kpow κ m t := by
    intro t m
    have := isMarkov_kpow (κ := κ) m
    rw [lintegral_iInf (fun n => Kernel.measurable_coe _ hF)
      (fun a b hab t' => hanti t' hab) (by
        have := isMarkov_kpow (κ := κ) 0
        exact ne_top_of_le_ne_top (ENNReal.one_ne_top) (by
          calc ∫⁻ t', kpow κ 0 t' F ∂kpow κ m t ≤ ∫⁻ _t', 1 ∂kpow κ m t :=
                lintegral_mono fun t' => prob_le_one
            _ = 1 := by simp))]
    simp_rw [← kpow_add_apply m _ t hF]
    exact (iInf_shift_antitone (hanti t) m).symm
  set gr : S → ℝ := fun t => (g t).toReal
  have hgrm : Measurable gr := hgm.ennreal_toReal
  have hgr01 : ∀ t, 0 ≤ gr t ∧ gr t ≤ 1 := fun t =>
    ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal zero_le_one (by
      rw [ENNReal.ofReal_one]; exact hg1 t)⟩
  have hgri : ∀ (μ : Measure S) [IsFiniteMeasure μ], Integrable gr μ := fun μ _ =>
    integrable_of_abs_le μ hgrm (C := 1) fun t => by
      rw [abs_of_nonneg (hgr01 t).1]; exact (hgr01 t).2
  have hharmr : ∀ t m, gr t = ∫ t', gr t' ∂kpow κ m t := fun t m => by
    have := isMarkov_kpow (κ := κ) m
    simp only [gr]
    rw [integral_toReal hgm.aemeasurable (Eventually.of_forall fun t' =>
      lt_of_le_of_lt (hg1 t') ENNReal.one_lt_top), ← hharm]
  set γ := ⨆ t, gr t
  have hbdd : BddAbove (range gr) := ⟨1, by rintro _ ⟨t, rfl⟩; exact (hgr01 t).2⟩
  have hgrγ : ∀ t, gr t ≤ γ := fun t => le_ciSup hbdd t
  -- `γ ≤ 0`
  have hγ : γ ≤ 0 := by
    by_contra hγpos
    push Not at hγpos
    set B : ℝ → Set S := fun η' => {t | γ - η' < gr t}
    have hBm : ∀ η', MeasurableSet (B η') := fun η' => measurableSet_lt measurable_const hgrm
    -- from a nearly maximal point the chain stays nearly maximal
    have hkey : ∀ t η η', 0 < η' → γ - η < gr t → 1 - η / η' < (kpow κ N t).real (B η') := by
      intro t η η' hη' ht
      have := isMarkov_kpow (κ := κ) N
      have hle : ∀ t', gr t' ≤ γ - η' + η' * (B η').indicator (fun _ => (1 : ℝ)) t' :=
        fun t' => by
          by_cases h : t' ∈ B η'
          · rw [indicator_of_mem h, mul_one]; linarith [hgrγ t']
          · rw [indicator_of_notMem h, mul_zero, add_zero]
            simp only [B, mem_ofPred_eq, not_lt] at h; exact h
      have hI : Integrable (fun t' => η' * (B η').indicator (fun _ => (1 : ℝ)) t')
          (kpow κ N t) := ((integrable_const (1 : ℝ)).indicator (hBm η')).const_mul η'
      have hint : ∫ t', gr t' ∂kpow κ N t ≤
          ∫ t', (γ - η' + η' * (B η').indicator (fun _ => (1 : ℝ)) t') ∂kpow κ N t :=
        integral_mono (hgri (kpow κ N t)) ((integrable_const (γ - η')).add hI) hle
      have hrhs : ∫ t', (γ - η' + η' * (B η').indicator (fun _ => (1 : ℝ)) t') ∂kpow κ N t =
          γ - η' + η' * (kpow κ N t).real (B η') := by
        rw [integral_add (integrable_const _) hI, integral_const, probReal_univ, one_smul,
          integral_const_mul, integral_indicator_const _ (hBm η'), smul_eq_mul, mul_one]
      rw [hrhs, ← hharmr t N] at hint
      have h3 : γ - η < γ - η' + η' * (kpow κ N t).real (B η') := lt_of_lt_of_le ht hint
      have h4 : 1 - η / η' = (η' - η) / η' := by field_simp
      rw [h4, div_lt_iff₀ hη']
      linarith
    have hBlarge : ∀ η', 0 < η' → ε < φ.real (B η') := by
      intro η' hη'
      obtain ⟨t, ht⟩ := exists_lt_of_lt_ciSup (show γ - ε * η' / 2 < γ by
        have : 0 < ε * η' / 2 := by positivity
        linarith)
      have h1 := hkey t (ε * η' / 2) η' hη' ht
      have h2 : ε * η' / 2 / η' = ε / 2 := by field_simp
      rw [h2] at h1
      by_contra hle
      have := hD.2.2.2 (B η') (hBm η') (not_lt.1 hle) t
      linarith
    -- the set where `g` is maximal
    set Binf := {t | γ ≤ gr t}
    have hBinfm : MeasurableSet Binf := measurableSet_le measurable_const hgrm
    have hBinf_eq : Binf = ⋂ k : ℕ, B (1 / ((k : ℝ) + 1)) := by
      ext t
      simp only [Binf, B, mem_ofPred_eq, mem_iInter]
      constructor
      · intro h k; have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
      · intro h
        refine le_of_forall_pos_lt_add fun δ hδ => ?_
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
        linarith [h k]
    have hBinfφ : ε ≤ φ.real Binf := by
      have hanti' : Antitone fun k : ℕ => B (1 / ((k : ℝ) + 1)) := fun a b hab t ht => by
        simp only [B, mem_ofPred_eq] at ht ⊢
        have : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by
            have : (a : ℝ) ≤ b := by exact_mod_cast hab
            linarith)
        linarith
      have h1 := tendsto_measure_iInter_atTop (μ := φ)
        (fun k : ℕ => (hBm (1 / ((k : ℝ) + 1))).nullMeasurableSet) hanti' ⟨0, measure_ne_top _ _⟩
      rw [← hBinf_eq] at h1
      have h2 := (ENNReal.tendsto_toReal (measure_ne_top φ Binf)).comp h1
      exact ge_of_tendsto h2 (Eventually.of_forall fun k =>
        (hBlarge (1 / ((k : ℝ) + 1)) (by positivity)).le)
    have hBinf_ne : Binf.Nonempty := by
      by_contra hemp
      rw [not_nonempty_iff_eq_empty] at hemp
      rw [hemp, measureReal_empty] at hBinfφ
      linarith
    -- `Binf` is invariant
    have hBinv : IsInvariantSet κ Binf := by
      refine ⟨hBinfm, hBinf_ne, fun t ht n hn => ?_⟩
      have := isMarkov_kpow (κ := κ) n
      have hγt : gr t = γ := le_antisymm (hgrγ t) ht
      have h0 : ∫ t', (γ - gr t') ∂kpow κ n t = 0 := by
        rw [integral_sub (integrable_const _) (hgri _), integral_const, probReal_univ, one_smul,
          ← hharmr t n, hγt, sub_self]
      have hae := (integral_eq_zero_iff_of_nonneg (fun t' => sub_nonneg.2 (hgrγ t'))
        ((integrable_const _).sub (hgri _))).1 h0
      rw [← prob_compl_eq_zero_iff hBinfm]
      refine measure_mono_null (fun t' ht' => ?_) (ae_iff.1 hae)
      simp only [Binf, mem_compl_iff, mem_ofPred_eq, not_le] at ht'
      simp only [mem_ofPred_eq, Pi.zero_apply]
      linarith
    obtain ⟨E', hE'sub, hE'erg⟩ := exists_ergodic_subset_of_invariant hD hBinv
    obtain ⟨m, hm, -⟩ := hall E' hE'erg
    have hdisj : E' ∩ E m = ∅ := eq_empty_of_forall_notMem fun t ⟨h1, h2⟩ => by
      have := hE'sub h1
      simp only [Binf, mem_ofPred_eq, gr, hgE m t h2, ENNReal.toReal_zero] at this
      linarith
    rw [hdisj, measure_empty] at hm
    have := invariant_real_gt hD hE'erg.1
    rw [measureReal_def, ← hm, ENNReal.toReal_zero] at this
    linarith
  have hg0 : g s = 0 := by
    have h1 : gr s = 0 := le_antisymm ((hgrγ s).trans hγ) (hgr01 s).1
    rcases (ENNReal.toReal_eq_zero_iff _).1 h1 with h | h
    · exact h
    · exact absurd h (ne_top_of_le_ne_top ENNReal.one_ne_top (hg1 s))
  rw [← hg0]
  exact tendsto_atTop_iInf (hanti s)

/-- Integrated absorption: the mass of `T*ⁿμ` in the transient set tends to `0`. -/
theorem tendsto_adjoint_transient [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ}
    (hD : DoeblinFor κ φ N ε) {M : ℕ} {E : Fin M → Set S} (hE : ∀ m, IsErgodicSetD κ φ (E m))
    (hall : ∀ F, IsErgodicSetD κ φ F → ∃ m, φ (F ∩ E m) = φ F ∧ φ (F ∩ E m) = φ (E m))
    (μ : Measure S) [IsFiniteMeasure μ] :
    Tendsto (fun n => adjointOp (kpow κ n) μ (⋃ m, E m)ᶜ) atTop (𝓝 0) := by
  have hF : MeasurableSet (⋃ m, E m)ᶜ := (MeasurableSet.iUnion fun m => (hE m).1.1).compl
  simp_rw [adjointOp_apply _ _ hF]
  have := tendsto_lintegral_of_dominated_convergence (μ := μ) (fun _ => 1)
    (fun n => Kernel.measurable_coe (kpow κ n) hF)
    (fun n => Eventually.of_forall fun s => by
      have := isMarkov_kpow (κ := κ) n; exact prob_le_one)
    (by simp) (Eventually.of_forall fun s => tendsto_kpow_transient hD hE hall s)
  simpa using this

/-- Each ergodic set carries an invariant probability measure. -/
theorem exists_invariant_on [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ}
    (hD : DoeblinFor κ φ N ε) {E : Set S} (hE : IsErgodicSetD κ φ E) :
    ∃ π : Measure S, IsProbabilityMeasure π ∧ adjointOp κ π = π ∧ π E = 1 := by
  obtain ⟨s, hs⟩ := hE.1.2.1
  obtain ⟨π, hπp, hπinv, hπr⟩ := exists_invariant hD (Measure.dirac s)
  refine ⟨π, hπp, hπinv, ?_⟩
  have hone : ∀ n, (cesaroM κ n (Measure.dirac s)).real E = 1 := fun n => by
    rw [cesaroM_real]
    have : ∀ k, (adjointOp (kpow κ (k + 1)) (Measure.dirac s)).real E = 1 := fun k => by
      rw [adjointOp, Measure.dirac_bind (kpow κ (k + 1)).measurable, measureReal_def,
        hE.1.2.2 s hs (k + 1) (by omega), ENNReal.toReal_one]
    simp only [this, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast
    exact inv_mul_cancel₀ (by positivity)
  have hlim : cesaroLim κ (Measure.dirac s) E = 1 :=
    tendsto_nhds_unique (tendsto_cesaroLim _ E) (tendsto_const_nhds.congr fun n => (hone n).symm)
  rw [← ofReal_measureReal (μ := π) (s := E), hπr E hE.1.1, hlim, ENNReal.ofReal_one]

/-- Every finite measure has uniformly Cauchy Cesàro averages under Condition D. -/
theorem cesaroCauchy_all [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ} (hD : DoeblinFor κ φ N ε)
    (μ : Measure S) [IsFiniteMeasure μ] : CesaroCauchy κ μ := by
  obtain ⟨-, -, -, M, -, -, E, hE, hdisj, hall⟩ := theorem_11_9a hD
  choose π hπp hπinv hπE using fun m => exists_invariant_on hD (hE m)
  refine cesaroCauchy_of_approx fun η hη => ?_
  set F := (⋃ m, E m)ᶜ
  have hEm : ∀ m, MeasurableSet (E m) := fun m => (hE m).1.1
  have hFm : MeasurableSet F := (MeasurableSet.iUnion hEm).compl
  have hlim := (ENNReal.tendsto_toReal (ENNReal.zero_ne_top)).comp
    (tendsto_adjoint_transient hD hE hall μ)
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (show (0 : ℝ≥0∞).toReal < η by simpa))).exists
  set ν := adjointOp (kpow κ n) μ
  have hν : IsFiniteMeasure ν := isFinite_adjoint n μ
  have hsplit : ν = ∑ m, ν.restrict (E m) + ν.restrict F := by
    rw [← Measure.sum_fintype, ← Measure.restrict_iUnion hdisj hEm,
      Measure.restrict_add_restrict_compl (MeasurableSet.iUnion hEm)]
  have hGfin : IsFiniteMeasure (∑ m, ν.restrict (E m)) := by
    refine ⟨?_⟩
    rw [Measure.coe_finsetSum, Finset.sum_apply]
    exact ENNReal.sum_lt_top.2 fun m _ => measure_lt_top _ _
  refine ⟨n, ∑ m, ν.restrict (E m), ν.restrict F, hGfin, inferInstance, hsplit,
    cesaroCauchy_finsetSum _ _ fun m _ => cesaroCauchy_of_concentrated hD (hE m) (hπinv m)
      (hπE m) _ (by rw [Measure.restrict_apply (hEm m).compl, compl_inter_self, measure_empty]),
    ?_⟩
  rw [measureReal_restrict_apply MeasurableSet.univ, univ_inter]
  exact hn.le

/-- **Theorem 11.9b.** Under Condition D, for every `λ₀` the Cesàro averages
`(1/N) Σ_{n=1}^{N} T*ⁿλ₀` converge in total variation, and the limit is invariant. -/
theorem theorem_11_9b [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ} (hD : DoeblinFor κ φ N ε)
    (l₀ : Measure S) [IsProbabilityMeasure l₀] :
    ∃ μ : Measure S, IsProbabilityMeasure μ ∧ adjointOp κ μ = μ ∧
      Tendsto (fun n => tvDist (cesaroM κ n l₀) μ) atTop (𝓝 0) := by
  have : ∀ n, IsProbabilityMeasure (cesaroM κ n l₀) := fun n => isProb_cesaroM n l₀
  obtain ⟨μ, hμ, hlim⟩ := lemma_11_8 (fun n => cesaroM κ n l₀)
    (tvDist_cesaro_le (cesaroCauchy_all hD l₀))
  refine ⟨μ, hμ, ?_, hlim⟩
  have hPfin : IsFiniteMeasure (adjointOp κ μ) := by
    have := isFinite_adjoint (κ := κ) 1 μ; rwa [kpow_one] at this
  refine Measure.ext fun A hA => ?_
  have hset : Tendsto (fun n => (cesaroM κ n l₀).real A) atTop (𝓝 (μ.real A)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero_norm (fun n => ?_) (by simpa using hlim.div_const 2)
    rw [norm_norm, Real.norm_eq_abs]
    have := two_abs_le_tvDist (cesaroM κ n l₀) μ hA
    linarith
  set f : S → ℝ := fun s => (κ s).real A
  have hf : Measurable f := (κ.measurable_coe hA).ennreal_toReal
  have hf1 : ∀ s, |f s| ≤ 1 := fun s => by
    rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one
  have hint : Tendsto (fun n => ∫ s, f s ∂cesaroM κ n l₀) atTop (𝓝 (∫ s, f s ∂μ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero_norm (fun n => ?_) hlim
    rw [norm_norm, Real.norm_eq_abs]
    exact abs_integral_sub_le_tvDist _ _ hf hf1
  have hsh : Tendsto (fun n => ∫ s, f s ∂cesaroM κ n l₀) atTop (𝓝 (μ.real A)) := by
    have hd : Tendsto (fun n => (cesaroM κ n (adjointOp (kpow κ 1) l₀)).real A -
        (cesaroM κ n l₀).real A) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
      rw [Real.norm_eq_abs]
      refine (abs_cesaro_shift_le n 1 l₀ A).trans (le_of_eq ?_)
      simp [div_eq_mul_inv]
    have := hd.add hset
    rw [zero_add] at this
    refine this.congr fun n => ?_
    have := isFinite_cesaroM (κ := κ) n l₀
    rw [sub_add_cancel, ← adjoint_cesaroM, bind_real_eq κ _ hA]
  have heq : (adjointOp κ μ).real A = μ.real A := by
    rw [bind_real_eq κ μ hA]; exact tendsto_nhds_unique hint hsh
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 heq

/-- An invariant measure gives the transient set measure zero. -/
theorem invariant_transient_null [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ}
    (hD : DoeblinFor κ φ N ε) {M : ℕ} {E : Fin M → Set S} (hE : ∀ m, IsErgodicSetD κ φ (E m))
    (hall : ∀ F, IsErgodicSetD κ φ F → ∃ m, φ (F ∩ E m) = φ F ∧ φ (F ∩ E m) = φ (E m))
    {μ : Measure S} [IsProbabilityMeasure μ] (hμ : adjointOp κ μ = μ) :
    μ (⋃ m, E m)ᶜ = 0 := by
  have h := tendsto_adjoint_transient hD hE hall μ
  simp only [invariant_iterate hμ] at h
  exact tendsto_nhds_unique tendsto_const_nhds h

/-- The restriction of an invariant measure to an ergodic set is invariant. -/
theorem restrict_invariant [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ}
    (hD : DoeblinFor κ φ N ε) {M : ℕ} {E : Fin M → Set S} (hE : ∀ m, IsErgodicSetD κ φ (E m))
    (hdisj : Pairwise (Function.onFun Disjoint E))
    (hall : ∀ F, IsErgodicSetD κ φ F → ∃ m, φ (F ∩ E m) = φ F ∧ φ (F ∩ E m) = φ (E m))
    {μ : Measure S} [IsProbabilityMeasure μ] (hμ : adjointOp κ μ = μ) (m : Fin M) :
    adjointOp κ (μ.restrict (E m)) = μ.restrict (E m) := by
  have hEm : ∀ m, MeasurableSet (E m) := fun m => (hE m).1.1
  have hκE : ∀ m', ∀ s ∈ E m', κ s (E m') = 1 := fun m' s hs => by
    have := (hE m').1.2.2 s hs 1 le_rfl; rwa [kpow_one] at this
  have hF := invariant_transient_null hD hE hall hμ
  ext A hA
  rw [adjointOp_apply κ _ hA, Measure.restrict_apply hA]
  have h1 : μ (A ∩ E m) = ∫⁻ s, κ s (A ∩ E m) ∂μ := by
    rw [← adjointOp_apply κ _ (hA.inter (hEm m)), hμ]
  rw [h1, ← lintegral_add_compl (fun s => κ s (A ∩ E m)) (hEm m)]
  have hoff : ∫⁻ s in (E m)ᶜ, κ s (A ∩ E m) ∂μ = 0 := by
    rw [lintegral_eq_zero_iff (κ.measurable_coe (hA.inter (hEm m)))]
    have hae : ∀ᵐ s ∂μ, s ∈ ⋃ m, E m := by
      rw [ae_iff]; simpa [compl_def] using hF
    rw [EventuallyEq, ae_restrict_iff' (hEm m).compl]
    filter_upwards [hae] with s hs hsm
    obtain ⟨m', hm'⟩ := mem_iUnion.1 hs
    have hne : m' ≠ m := fun h => hsm (h ▸ hm')
    have h0 : κ s (E m) = 0 := by
      refine measure_mono_null (hdisj hne).subset_compl_left ?_
      rw [prob_compl_eq_zero_iff (hEm m')]; exact hκE m' s hm'
    exact measure_mono_null inter_subset_right h0
  rw [hoff, add_zero]
  refine setLIntegral_congr_fun (hEm m) fun s hs => ?_
  symm
  have h0 : κ s (A \ E m) = 0 := measure_mono_null (show A \ E m ⊆ (E m)ᶜ from
    fun x hx => hx.2) (by
    rw [prob_compl_eq_zero_iff (hEm m)]; exact hκE m s hs)
  rw [← measure_inter_add_sdiff A (hEm m), h0, add_zero]

/-- **Theorem 11.9c.** Under Condition D there are `M ≥ 1` ergodic sets `E₁, …, E_M`, each
carrying an invariant probability measure `πₘ`, and every invariant probability measure is the
convex combination `Σₘ μ(Eₘ) πₘ`. -/
theorem theorem_11_9c [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ} (hD : DoeblinFor κ φ N ε) :
    ∃ (M : ℕ) (E : Fin M → Set S) (π : Fin M → Measure S), 1 ≤ M ∧
      (∀ m, IsErgodicSetD κ φ (E m)) ∧ Pairwise (Function.onFun Disjoint E) ∧
      (∀ m, IsProbabilityMeasure (π m) ∧ adjointOp κ (π m) = π m ∧ π m (E m) = 1) ∧
      ∀ μ : Measure S, IsProbabilityMeasure μ → adjointOp κ μ = μ →
        ∑ m, μ (E m) = 1 ∧ μ = ∑ m, μ (E m) • π m := by
  obtain ⟨-, -, -, M, hM1, -, E, hE, hdisj, hall⟩ := theorem_11_9a hD
  choose π hπp hπinv hπE using fun m => exists_invariant_on hD (hE m)
  refine ⟨M, E, π, hM1, hE, hdisj, fun m => ⟨hπp m, hπinv m, hπE m⟩, fun μ hμp hμ => ?_⟩
  have hEm : ∀ m, MeasurableSet (E m) := fun m => (hE m).1.1
  have hF := invariant_transient_null hD hE hall hμ
  have hrestr : ∀ m, μ.restrict (E m) = μ (E m) • π m := by
    intro m
    have hinv := restrict_invariant hD hE hdisj hall hμ m
    by_cases h0 : μ (E m) = 0
    · rw [h0, zero_smul, Measure.restrict_eq_zero.2 h0]
    · set c := (μ (E m))⁻¹
      have hρp : IsProbabilityMeasure (c • μ.restrict (E m)) := ⟨by
        rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
          smul_eq_mul, ENNReal.inv_mul_cancel h0 (measure_ne_top _ _)]⟩
      have hρinv : adjointOp κ (c • μ.restrict (E m)) = c • μ.restrict (E m) := by
        rw [adjointOp_smul, hinv]
      have hρE : (c • μ.restrict (E m)) (E m) = 1 := by
        rw [Measure.smul_apply, Measure.restrict_apply (hEm m), inter_self, smul_eq_mul,
          ENNReal.inv_mul_cancel h0 (measure_ne_top _ _)]
      have := invariant_unique hD (hE m) hρinv (hπinv m) hρE (hπE m)
      rw [← this, smul_smul, ENNReal.mul_inv_cancel h0 (measure_ne_top _ _), one_smul]
  have hsplit : μ = ∑ m, μ.restrict (E m) := by
    rw [← Measure.sum_fintype, ← Measure.restrict_iUnion hdisj hEm]
    conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := μ) (MeasurableSet.iUnion hEm)]
    rw [Measure.restrict_eq_zero.2 hF, add_zero]
  refine ⟨?_, by rw [← Finset.sum_congr rfl fun m _ => hrestr m]; exact hsplit⟩
  calc ∑ m, μ (E m) = μ (⋃ m, E m) := by
        rw [measure_iUnion hdisj hEm, tsum_fintype]
    _ = 1 := by
        rw [← prob_compl_eq_zero_iff (MeasurableSet.iUnion hEm)]; exact hF

/-- Under the reachability condition of Theorem 11.10 there is exactly one ergodic set in the
decomposition of Theorem 11.9. -/
theorem ergodic_count_eq_one [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ}
    (hD : DoeblinFor κ φ N ε)
    (hirr : ∀ A, MeasurableSet A → 0 < φ A → ∀ s, ∃ n, 1 ≤ n ∧ 0 < kpow κ n s A)
    {M : ℕ} {E : Fin M → Set S} (hM : 1 ≤ M) (hE : ∀ m, IsErgodicSetD κ φ (E m))
    (hdisj : Pairwise (Function.onFun Disjoint E)) : M = 1 := by
  by_contra hne
  have h2 : 2 ≤ M := by omega
  set m₀ : Fin M := ⟨0, by omega⟩
  set m₁ : Fin M := ⟨1, by omega⟩
  have hne' : m₀ ≠ m₁ := fun h => by simpa [m₀, m₁] using congrArg Fin.val h
  have h := (theorem_11_10a hD hirr (hE m₀) (hE m₁)).1
  rw [(hdisj hne').inter_eq, measure_empty] at h
  have := invariant_real_gt hD (hE m₀).1
  rw [measureReal_def, ← h, ENNReal.toReal_zero] at this
  linarith [hD.2.2.1]

/-- **Theorem 11.10b.** Under the reachability condition, `T*` has exactly one invariant
probability measure. -/
theorem theorem_11_10b [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ} (hD : DoeblinFor κ φ N ε)
    (hirr : ∀ A, MeasurableSet A → 0 < φ A → ∀ s, ∃ n, 1 ≤ n ∧ 0 < kpow κ n s A) :
    ∃! μ : Measure S, IsProbabilityMeasure μ ∧ adjointOp κ μ = μ := by
  obtain ⟨M, E, π, hM, hE, hdisj, hπ, hall⟩ := theorem_11_9c hD
  have hM1 := ergodic_count_eq_one hD hirr hM hE hdisj
  subst hM1
  obtain ⟨hπp, hπinv, -⟩ := hπ 0
  refine ⟨π 0, ⟨hπp, hπinv⟩, fun μ ⟨hμp, hμ⟩ => ?_⟩
  obtain ⟨hsum, hdec⟩ := hall μ hμp hμ
  simp only [Fin.sum_univ_one] at hsum hdec
  rw [hdec, hsum, one_smul]

/-- **Theorem 11.10c.** Under the reachability condition, the Cesàro averages of `T*ⁿλ₀`
converge in total variation to the unique invariant measure, for every `λ₀`. -/
theorem theorem_11_10c [Nonempty S] {φ : Measure S} {N : ℕ} {ε : ℝ} (hD : DoeblinFor κ φ N ε)
    (hirr : ∀ A, MeasurableSet A → 0 < φ A → ∀ s, ∃ n, 1 ≤ n ∧ 0 < kpow κ n s A) :
    ∃ lstar : Measure S, IsProbabilityMeasure lstar ∧ adjointOp κ lstar = lstar ∧
      ∀ (l₀ : Measure S) [IsProbabilityMeasure l₀],
        Tendsto (fun n => tvDist (cesaroM κ n l₀) lstar) atTop (𝓝 0) := by
  obtain ⟨lstar, ⟨hp, hinv⟩, huniq⟩ := theorem_11_10b hD hirr
  refine ⟨lstar, hp, hinv, fun l₀ _ => ?_⟩
  obtain ⟨μ, hμp, hμinv, hlim⟩ := theorem_11_9b hD l₀
  rwa [huniq μ ⟨hμp, hμinv⟩] at hlim

end StokeyLucasPrescott.StrongConvergence

set_option linter.style.longLine false
#print axioms StokeyLucasPrescott.StrongConvergence.simplex
#print axioms StokeyLucasPrescott.StrongConvergence.IsInvariantDist
#print axioms StokeyLucasPrescott.StrongConvergence.Cons
#print axioms StokeyLucasPrescott.StrongConvergence.IsTransient
#print axioms StokeyLucasPrescott.StrongConvergence.IsRecurrent
#print axioms StokeyLucasPrescott.StrongConvergence.IsClosedSet
#print axioms StokeyLucasPrescott.StrongConvergence.IsErgodic
#print axioms StokeyLucasPrescott.StrongConvergence.consSet
#print axioms StokeyLucasPrescott.StrongConvergence.mem_consSet
#print axioms StokeyLucasPrescott.StrongConvergence.pow_mem_rowStochastic
#print axioms StokeyLucasPrescott.StrongConvergence.pow_nonneg'
#print axioms StokeyLucasPrescott.StrongConvergence.pow_le_one'
#print axioms StokeyLucasPrescott.StrongConvergence.pow_row_sum
#print axioms StokeyLucasPrescott.StrongConvergence.pow_add_ge
#print axioms StokeyLucasPrescott.StrongConvergence.pow_add_pos
#print axioms StokeyLucasPrescott.StrongConvergence.Cons.trans
#print axioms StokeyLucasPrescott.StrongConvergence.exists_cons
#print axioms StokeyLucasPrescott.StrongConvergence.isTransient_iff_not_isRecurrent
#print axioms StokeyLucasPrescott.StrongConvergence.exists_pos_of_sum_pos
#print axioms StokeyLucasPrescott.StrongConvergence.IsClosedSet.apply_eq_zero
#print axioms StokeyLucasPrescott.StrongConvergence.IsClosedSet.mem_of_pow_pos
#print axioms StokeyLucasPrescott.StrongConvergence.isClosedSet_of
#print axioms StokeyLucasPrescott.StrongConvergence.isClosedSet_univ
#print axioms StokeyLucasPrescott.StrongConvergence.consSet_closed
#print axioms StokeyLucasPrescott.StrongConvergence.consSet_nonempty
#print axioms StokeyLucasPrescott.StrongConvergence.IsClosedSet.consSet_subset
#print axioms StokeyLucasPrescott.StrongConvergence.exists_ergodic_subset
#print axioms StokeyLucasPrescott.StrongConvergence.IsErgodic.eq_consSet
#print axioms StokeyLucasPrescott.StrongConvergence.IsErgodic.isRecurrent
#print axioms StokeyLucasPrescott.StrongConvergence.IsRecurrent.self_mem_consSet
#print axioms StokeyLucasPrescott.StrongConvergence.IsRecurrent.isErgodic
#print axioms StokeyLucasPrescott.StrongConvergence.theorem_11_1a
#print axioms StokeyLucasPrescott.StrongConvergence.cesaro
#print axioms StokeyLucasPrescott.StrongConvergence.tendsto_matrix_iff
#print axioms StokeyLucasPrescott.StrongConvergence.simplex_vecMul
#print axioms StokeyLucasPrescott.StrongConvergence.cesaro_mem
#print axioms StokeyLucasPrescott.StrongConvergence.isClosed_rowStochastic
#print axioms StokeyLucasPrescott.StrongConvergence.unitBox
#print axioms StokeyLucasPrescott.StrongConvergence.mem_unitBox
#print axioms StokeyLucasPrescott.StrongConvergence.isCompact_unitBox
#print axioms StokeyLucasPrescott.StrongConvergence.rowStochastic_subset_unitBox
#print axioms StokeyLucasPrescott.StrongConvergence.sum_pow_succ_sub
#print axioms StokeyLucasPrescott.StrongConvergence.cesaro_mul_sub
#print axioms StokeyLucasPrescott.StrongConvergence.mul_cesaro_sub
#print axioms StokeyLucasPrescott.StrongConvergence.tendsto_pow_sub_div
#print axioms StokeyLucasPrescott.StrongConvergence.limit_mul
#print axioms StokeyLucasPrescott.StrongConvergence.mul_pow_eq
#print axioms StokeyLucasPrescott.StrongConvergence.pow_mul_eq
#print axioms StokeyLucasPrescott.StrongConvergence.mul_cesaro_eq
#print axioms StokeyLucasPrescott.StrongConvergence.cesaro_mul_eq
#print axioms StokeyLucasPrescott.StrongConvergence.theorem_11_1b
#print axioms StokeyLucasPrescott.StrongConvergence.theorem_11_1c
#print axioms StokeyLucasPrescott.StrongConvergence.harmonic_pow
#print axioms StokeyLucasPrescott.StrongConvergence.harmonic_max_spread
#print axioms StokeyLucasPrescott.StrongConvergence.harmonic_const
#print axioms StokeyLucasPrescott.StrongConvergence.exists_ergodic_reach
#print axioms StokeyLucasPrescott.StrongConvergence.column_harmonic
#print axioms StokeyLucasPrescott.StrongConvergence.theorem_11_2
#print axioms StokeyLucasPrescott.StrongConvergence.ergSets
#print axioms StokeyLucasPrescott.StrongConvergence.recSet
#print axioms StokeyLucasPrescott.StrongConvergence.mem_ergSets
#print axioms StokeyLucasPrescott.StrongConvergence.mem_recSet
#print axioms StokeyLucasPrescott.StrongConvergence.recSet_closed
#print axioms StokeyLucasPrescott.StrongConvergence.ergSets_pairwiseDisjoint
#print axioms StokeyLucasPrescott.StrongConvergence.mass
#print axioms StokeyLucasPrescott.StrongConvergence.mass_nonneg
#print axioms StokeyLucasPrescott.StrongConvergence.mass_le_one
#print axioms StokeyLucasPrescott.StrongConvergence.mass_add_compl
#print axioms StokeyLucasPrescott.StrongConvergence.mass_add
#print axioms StokeyLucasPrescott.StrongConvergence.mass_compl_eq_zero
#print axioms StokeyLucasPrescott.StrongConvergence.mass_mono
#print axioms StokeyLucasPrescott.StrongConvergence.exists_mass_recSet_pos
#print axioms StokeyLucasPrescott.StrongConvergence.tendsto_tail
#print axioms StokeyLucasPrescott.StrongConvergence.cesaro_apply
#print axioms StokeyLucasPrescott.StrongConvergence.Q_apply_of_tendsto
#print axioms StokeyLucasPrescott.StrongConvergence.not_mem_recSet_iff
#print axioms StokeyLucasPrescott.StrongConvergence.ex_11_1
#print axioms StokeyLucasPrescott.StrongConvergence.exists_nonneg_comb
#print axioms StokeyLucasPrescott.StrongConvergence.BigFor
#print axioms StokeyLucasPrescott.StrongConvergence.nsmul_mem
#print axioms StokeyLucasPrescott.StrongConvergence.bigFor_gcd
#print axioms StokeyLucasPrescott.StrongConvergence.eventually_mem_of_add_closed
#print axioms StokeyLucasPrescott.StrongConvergence.l1
#print axioms StokeyLucasPrescott.StrongConvergence.epsMin
#print axioms StokeyLucasPrescott.StrongConvergence.epsSum
#print axioms StokeyLucasPrescott.StrongConvergence.epsMin_le
#print axioms StokeyLucasPrescott.StrongConvergence.epsSum_nonneg
#print axioms StokeyLucasPrescott.StrongConvergence.epsSum_le_one
#print axioms StokeyLucasPrescott.StrongConvergence.lemma_11_3
#print axioms StokeyLucasPrescott.StrongConvergence.l1_sub_le_two
#print axioms StokeyLucasPrescott.StrongConvergence.l1_pow_le
#print axioms StokeyLucasPrescott.StrongConvergence.isClosed_simplex
#print axioms StokeyLucasPrescott.StrongConvergence.abs_le_l1
#print axioms StokeyLucasPrescott.StrongConvergence.eq_of_l1_le
#print axioms StokeyLucasPrescott.StrongConvergence.sum_eq_one_of_pos_mem
#print axioms StokeyLucasPrescott.StrongConvergence.apply_eq_zero_of_sum_eq_one
#print axioms StokeyLucasPrescott.StrongConvergence.HasCyclicSubsets
#print axioms StokeyLucasPrescott.StrongConvergence.periodic_mod
#print axioms StokeyLucasPrescott.StrongConvergence.cyclic_pow
#print axioms StokeyLucasPrescott.StrongConvergence.exists_pos_column
#print axioms StokeyLucasPrescott.StrongConvergence.epsSum_pos_of_column
#print axioms StokeyLucasPrescott.StrongConvergence.theorem_11_4_rate
#print axioms StokeyLucasPrescott.StrongConvergence.tendsto_of_l1
#print axioms StokeyLucasPrescott.StrongConvergence.conv_of_eps
#print axioms StokeyLucasPrescott.StrongConvergence.eps_of_conv
#print axioms StokeyLucasPrescott.StrongConvergence.uniqueErgodic_of_eps
#print axioms StokeyLucasPrescott.StrongConvergence.exists_mid
#print axioms StokeyLucasPrescott.StrongConvergence.hasCyclicSubsets_of_period
#print axioms StokeyLucasPrescott.StrongConvergence.eps_of_uniqueErgodic
#print axioms StokeyLucasPrescott.StrongConvergence.theorem_11_4
#print axioms StokeyLucasPrescott.StrongConvergence.ex1
#print axioms StokeyLucasPrescott.StrongConvergence.ex1_mem
#print axioms StokeyLucasPrescott.StrongConvergence.ex1_pow
#print axioms StokeyLucasPrescott.StrongConvergence.ex1_pow_234
#print axioms StokeyLucasPrescott.StrongConvergence.ex1_tendsto
#print axioms StokeyLucasPrescott.StrongConvergence.ex1_ergodic
#print axioms StokeyLucasPrescott.StrongConvergence.ex2
#print axioms StokeyLucasPrescott.StrongConvergence.ex2_pow
#print axioms StokeyLucasPrescott.StrongConvergence.ex2_tendsto
#print axioms StokeyLucasPrescott.StrongConvergence.ex2_ergodic
#print axioms StokeyLucasPrescott.StrongConvergence.ex5
#print axioms StokeyLucasPrescott.StrongConvergence.ex5_pow
#print axioms StokeyLucasPrescott.StrongConvergence.ex5_tendsto
#print axioms StokeyLucasPrescott.StrongConvergence.ex5_ergodic
#print axioms StokeyLucasPrescott.StrongConvergence.ex3
#print axioms StokeyLucasPrescott.StrongConvergence.ex4
#print axioms StokeyLucasPrescott.StrongConvergence.halfMat
#print axioms StokeyLucasPrescott.StrongConvergence.fromBlocks_diag_pow
#print axioms StokeyLucasPrescott.StrongConvergence.ex3_pow_even
#print axioms StokeyLucasPrescott.StrongConvergence.ex3_pow_odd
#print axioms StokeyLucasPrescott.StrongConvergence.continuous_diagBlocks
#print axioms StokeyLucasPrescott.StrongConvergence.continuous_offBlocks
#print axioms StokeyLucasPrescott.StrongConvergence.ex3_even_odd
#print axioms StokeyLucasPrescott.StrongConvergence.ex3_not_tendsto
#print axioms StokeyLucasPrescott.StrongConvergence.ex1_pos
#print axioms StokeyLucasPrescott.StrongConvergence.ex1_sq_pos
#print axioms StokeyLucasPrescott.StrongConvergence.ex3_mem
#print axioms StokeyLucasPrescott.StrongConvergence.ex3_cons
#print axioms StokeyLucasPrescott.StrongConvergence.ex3_cesaro
#print axioms StokeyLucasPrescott.StrongConvergence.ex3_ergodic
#print axioms StokeyLucasPrescott.StrongConvergence.ex4_tendsto
#print axioms StokeyLucasPrescott.StrongConvergence.IsInvariantDist.convex
#print axioms StokeyLucasPrescott.StrongConvergence.ex4_ergodic
#print axioms StokeyLucasPrescott.StrongConvergence.IsTransitionFunction
#print axioms StokeyLucasPrescott.StrongConvergence.isTransitionFunction_iff
#print axioms StokeyLucasPrescott.StrongConvergence.markovOp
#print axioms StokeyLucasPrescott.StrongConvergence.markovOpR
#print axioms StokeyLucasPrescott.StrongConvergence.adjointOp
#print axioms StokeyLucasPrescott.StrongConvergence.markovOp_indicator
#print axioms StokeyLucasPrescott.StrongConvergence.theorem_8_1
#print axioms StokeyLucasPrescott.StrongConvergence.integrable_of_bounded
#print axioms StokeyLucasPrescott.StrongConvergence.theorem_8_1_cor
#print axioms StokeyLucasPrescott.StrongConvergence.ex_8_1
#print axioms StokeyLucasPrescott.StrongConvergence.adjointOp_apply
#print axioms StokeyLucasPrescott.StrongConvergence.theorem_8_2
#print axioms StokeyLucasPrescott.StrongConvergence.ex_8_2
#print axioms StokeyLucasPrescott.StrongConvergence.theorem_8_3
#print axioms StokeyLucasPrescott.StrongConvergence.theorem_8_3_cor
#print axioms StokeyLucasPrescott.StrongConvergence.pairing
#print axioms StokeyLucasPrescott.StrongConvergence.ex_8_3
#print axioms StokeyLucasPrescott.StrongConvergence.kpow
#print axioms StokeyLucasPrescott.StrongConvergence.kpow_one
#print axioms StokeyLucasPrescott.StrongConvergence.ex_8_4a
#print axioms StokeyLucasPrescott.StrongConvergence.kpow_add
#print axioms StokeyLucasPrescott.StrongConvergence.markovOp_comp
#print axioms StokeyLucasPrescott.StrongConvergence.adjointOp_comp
#print axioms StokeyLucasPrescott.StrongConvergence.ex_8_4b
#print axioms StokeyLucasPrescott.StrongConvergence.adjointOp_iterate
#print axioms StokeyLucasPrescott.StrongConvergence.IsFeller
#print axioms StokeyLucasPrescott.StrongConvergence.IsMonotoneTF
#print axioms StokeyLucasPrescott.StrongConvergence.ConvSetwise
#print axioms StokeyLucasPrescott.StrongConvergence.ConvIntegrals
#print axioms StokeyLucasPrescott.StrongConvergence.ConvWeak
#print axioms StokeyLucasPrescott.StrongConvergence.ConvStrong
#print axioms StokeyLucasPrescott.StrongConvergence.convSetwise_of_convIntegrals
#print axioms StokeyLucasPrescott.StrongConvergence.measurable_meas_lt
#print axioms StokeyLucasPrescott.StrongConvergence.ex_11_2
#print axioms StokeyLucasPrescott.StrongConvergence.convSetwise_iff
#print axioms StokeyLucasPrescott.StrongConvergence.halving
#print axioms StokeyLucasPrescott.StrongConvergence.halving_not_setwise
#print axioms StokeyLucasPrescott.StrongConvergence.halving_weak
#print axioms StokeyLucasPrescott.StrongConvergence.IsPartition
#print axioms StokeyLucasPrescott.StrongConvergence.partSums
#print axioms StokeyLucasPrescott.StrongConvergence.tvOf
#print axioms StokeyLucasPrescott.StrongConvergence.tvNorm
#print axioms StokeyLucasPrescott.StrongConvergence.tvDist
#print axioms StokeyLucasPrescott.StrongConvergence.supDiff
#print axioms StokeyLucasPrescott.StrongConvergence.isPartition_univ
#print axioms StokeyLucasPrescott.StrongConvergence.isPartition_pair
#print axioms StokeyLucasPrescott.StrongConvergence.partSums_nonempty
#print axioms StokeyLucasPrescott.StrongConvergence.sum_partition_real
#print axioms StokeyLucasPrescott.StrongConvergence.sum_partition_inter_real
#print axioms StokeyLucasPrescott.StrongConvergence.partSums_bddAbove_of_le
#print axioms StokeyLucasPrescott.StrongConvergence.partSums_le_of_measures
#print axioms StokeyLucasPrescott.StrongConvergence.bddAbove_tvDist
#print axioms StokeyLucasPrescott.StrongConvergence.lemma_11_5
#print axioms StokeyLucasPrescott.StrongConvergence.exists_sub_measures
#print axioms StokeyLucasPrescott.StrongConvergence.tvNorm_sub_eq
#print axioms StokeyLucasPrescott.StrongConvergence.bddAbove_tvNorm
#print axioms StokeyLucasPrescott.StrongConvergence.tvOf_nonneg
#print axioms StokeyLucasPrescott.StrongConvergence.abs_le_tvOf
#print axioms StokeyLucasPrescott.StrongConvergence.ex_11_3
#print axioms StokeyLucasPrescott.StrongConvergence.abs_sub_le_add
#print axioms StokeyLucasPrescott.StrongConvergence.bddAbove_supDiff
#print axioms StokeyLucasPrescott.StrongConvergence.two_abs_le_tvDist
#print axioms StokeyLucasPrescott.StrongConvergence.tvDist_le_of_forall
#print axioms StokeyLucasPrescott.StrongConvergence.tvDist_nonneg
#print axioms StokeyLucasPrescott.StrongConvergence.tendsto_zero_iff_of_nonneg
#print axioms StokeyLucasPrescott.StrongConvergence.theorem_11_6
#print axioms StokeyLucasPrescott.StrongConvergence.integrable_of_abs_le
#print axioms StokeyLucasPrescott.StrongConvergence.abs_add_abs_compl_le
#print axioms StokeyLucasPrescott.StrongConvergence.abs_integral_sub_le_tvDist
#print axioms StokeyLucasPrescott.StrongConvergence.theorem_11_7
#print axioms StokeyLucasPrescott.StrongConvergence.iInter_tails_eq_empty
#print axioms StokeyLucasPrescott.StrongConvergence.lemma_11_8
#print axioms StokeyLucasPrescott.StrongConvergence.DoeblinFor
#print axioms StokeyLucasPrescott.StrongConvergence.ConditionD
#print axioms StokeyLucasPrescott.StrongConvergence.ConditionMFor
#print axioms StokeyLucasPrescott.StrongConvergence.ConditionM
#print axioms StokeyLucasPrescott.StrongConvergence.kpow_add_apply
#print axioms StokeyLucasPrescott.StrongConvergence.isMarkov_kpow
#print axioms StokeyLucasPrescott.StrongConvergence.kpow_real_le_of_forall
#print axioms StokeyLucasPrescott.StrongConvergence.doeblinFor_mono
#print axioms StokeyLucasPrescott.StrongConvergence.real_le_one_sub_of_compl
#print axioms StokeyLucasPrescott.StrongConvergence.exists_small_atom
#print axioms StokeyLucasPrescott.StrongConvergence.ex_11_4a
#print axioms StokeyLucasPrescott.StrongConvergence.ex_11_4b
#print axioms StokeyLucasPrescott.StrongConvergence.ex_11_4c
#print axioms StokeyLucasPrescott.StrongConvergence.ex_11_4d
#print axioms StokeyLucasPrescott.StrongConvergence.density_lower
#print axioms StokeyLucasPrescott.StrongConvergence.ex_11_4e
#print axioms StokeyLucasPrescott.StrongConvergence.ex_11_4f
#print axioms StokeyLucasPrescott.StrongConvergence.kpow_mixture_ge
#print axioms StokeyLucasPrescott.StrongConvergence.ex_11_4g
#print axioms StokeyLucasPrescott.StrongConvergence.kpow_deterministic
#print axioms StokeyLucasPrescott.StrongConvergence.not_conditionD_deterministic
#print axioms StokeyLucasPrescott.StrongConvergence.ex_11_4h
#print axioms StokeyLucasPrescott.StrongConvergence.ex_11_4i
#print axioms StokeyLucasPrescott.StrongConvergence.halve
#print axioms StokeyLucasPrescott.StrongConvergence.measurable_halve
#print axioms StokeyLucasPrescott.StrongConvergence.ex_11_4j
#print axioms StokeyLucasPrescott.StrongConvergence.ex_11_5a_c
#print axioms StokeyLucasPrescott.StrongConvergence.ex_11_5a_e
#print axioms StokeyLucasPrescott.StrongConvergence.ex_11_5b
#print axioms StokeyLucasPrescott.StrongConvergence.ex_11_5c
#print axioms StokeyLucasPrescott.StrongConvergence.IsConsequentSet
#print axioms StokeyLucasPrescott.StrongConvergence.IsInvariantSet
#print axioms StokeyLucasPrescott.StrongConvergence.IsErgodicSetD
#print axioms StokeyLucasPrescott.StrongConvergence.measure_inter_eq_one
#print axioms StokeyLucasPrescott.StrongConvergence.measure_iInter_eq_one
#print axioms StokeyLucasPrescott.StrongConvergence.IsInvariantSet.inter
#print axioms StokeyLucasPrescott.StrongConvergence.isInvariantSet_iInter
#print axioms StokeyLucasPrescott.StrongConvergence.consequent_real_gt
#print axioms StokeyLucasPrescott.StrongConvergence.invariant_real_gt
#print axioms StokeyLucasPrescott.StrongConvergence.measure_eq_one_of_lintegral
#print axioms StokeyLucasPrescott.StrongConvergence.consCore
#print axioms StokeyLucasPrescott.StrongConvergence.measurableSet_consCore
#print axioms StokeyLucasPrescott.StrongConvergence.IsConsequentSet.consCore
#print axioms StokeyLucasPrescott.StrongConvergence.invariant_of_consequent
#print axioms StokeyLucasPrescott.StrongConvergence.iInter_le_succ
#print axioms StokeyLucasPrescott.StrongConvergence.exists_ergodic_subset_of_invariant
#print axioms StokeyLucasPrescott.StrongConvergence.ergodic_disjoint_or_eq
#print axioms StokeyLucasPrescott.StrongConvergence.card_mul_lt
#print axioms StokeyLucasPrescott.StrongConvergence.theorem_11_9a
#print axioms StokeyLucasPrescott.StrongConvergence.theorem_11_10a
#print axioms StokeyLucasPrescott.StrongConvergence.ex6
#print axioms StokeyLucasPrescott.StrongConvergence.ex7
#print axioms StokeyLucasPrescott.StrongConvergence.tvDist_comm
#print axioms StokeyLucasPrescott.StrongConvergence.tvDist_triangle
#print axioms StokeyLucasPrescott.StrongConvergence.tvDist_le_two
#print axioms StokeyLucasPrescott.StrongConvergence.eq_of_tvDist_eq_zero
#print axioms StokeyLucasPrescott.StrongConvergence.bind_real_eq
#print axioms StokeyLucasPrescott.StrongConvergence.lemma_11_11
#print axioms StokeyLucasPrescott.StrongConvergence.isProb_adjoint
#print axioms StokeyLucasPrescott.StrongConvergence.adjoint_add
#print axioms StokeyLucasPrescott.StrongConvergence.tvDist_iterate_le
#print axioms StokeyLucasPrescott.StrongConvergence.theorem_11_12
#print axioms StokeyLucasPrescott.StrongConvergence.theorem_11_12_converse
#print axioms StokeyLucasPrescott.StrongConvergence.adjointOp_add
#print axioms StokeyLucasPrescott.StrongConvergence.adjointOp_smul
#print axioms StokeyLucasPrescott.StrongConvergence.adjointOp_zero
#print axioms StokeyLucasPrescott.StrongConvergence.adjointOp_finsetSum
#print axioms StokeyLucasPrescott.StrongConvergence.adjointOp_mono
#print axioms StokeyLucasPrescott.StrongConvergence.adjointOp_kpow_univ
#print axioms StokeyLucasPrescott.StrongConvergence.isFinite_adjoint
#print axioms StokeyLucasPrescott.StrongConvergence.adjoint_real_le
#print axioms StokeyLucasPrescott.StrongConvergence.cesaroM
#print axioms StokeyLucasPrescott.StrongConvergence.cesaroM_apply
#print axioms StokeyLucasPrescott.StrongConvergence.cesaroM_real
#print axioms StokeyLucasPrescott.StrongConvergence.cesaroM_univ
#print axioms StokeyLucasPrescott.StrongConvergence.isFinite_cesaroM
#print axioms StokeyLucasPrescott.StrongConvergence.isProb_cesaroM
#print axioms StokeyLucasPrescott.StrongConvergence.cesaroM_real_nonneg_le
#print axioms StokeyLucasPrescott.StrongConvergence.cesaroM_add
#print axioms StokeyLucasPrescott.StrongConvergence.cesaroM_smul
#print axioms StokeyLucasPrescott.StrongConvergence.abs_cesaro_shift_le
#print axioms StokeyLucasPrescott.StrongConvergence.CesaroCauchy
#print axioms StokeyLucasPrescott.StrongConvergence.cesaroCauchy_zero
#print axioms StokeyLucasPrescott.StrongConvergence.CesaroCauchy.add
#print axioms StokeyLucasPrescott.StrongConvergence.CesaroCauchy.smul
#print axioms StokeyLucasPrescott.StrongConvergence.cesaroCauchy_finsetSum
#print axioms StokeyLucasPrescott.StrongConvergence.cesaroCauchy_of_approx
#print axioms StokeyLucasPrescott.StrongConvergence.cesaroCauchy_adjoint
#print axioms StokeyLucasPrescott.StrongConvergence.tvDist_cesaro_le
#print axioms StokeyLucasPrescott.StrongConvergence.invariant_iterate
#print axioms StokeyLucasPrescott.StrongConvergence.kpow_noReach_eq_one
#print axioms StokeyLucasPrescott.StrongConvergence.exists_reach
#print axioms StokeyLucasPrescott.StrongConvergence.pos_of_invariant
#print axioms StokeyLucasPrescott.StrongConvergence.absCont_of_concentrated
#print axioms StokeyLucasPrescott.StrongConvergence.posPart_invariant
#print axioms StokeyLucasPrescott.StrongConvergence.invariant_unique
#print axioms StokeyLucasPrescott.StrongConvergence.measurePreserving_fst_compProd
#print axioms StokeyLucasPrescott.StrongConvergence.measurePreserving_snd_compProd
#print axioms StokeyLucasPrescott.StrongConvergence.jFst
#print axioms StokeyLucasPrescott.StrongConvergence.jSnd
#print axioms StokeyLucasPrescott.StrongConvergence.markovL2
#print axioms StokeyLucasPrescott.StrongConvergence.norm_markovL2_le
#print axioms StokeyLucasPrescott.StrongConvergence.inner_real_apply
#print axioms StokeyLucasPrescott.StrongConvergence.memLp_two_of_bound
#print axioms StokeyLucasPrescott.StrongConvergence.inner_markovL2
#print axioms StokeyLucasPrescott.StrongConvergence.markovL2_toLp
#print axioms StokeyLucasPrescott.StrongConvergence.stepFn
#print axioms StokeyLucasPrescott.StrongConvergence.measurable_stepFn
#print axioms StokeyLucasPrescott.StrongConvergence.abs_stepFn_le
#print axioms StokeyLucasPrescott.StrongConvergence.markovOpR_stepFn
#print axioms StokeyLucasPrescott.StrongConvergence.markovL2_iterate
#print axioms StokeyLucasPrescott.StrongConvergence.inner_iterate_adjoint
#print axioms StokeyLucasPrescott.StrongConvergence.isFiniteMeasure_withDensity_of_bound
#print axioms StokeyLucasPrescott.StrongConvergence.adjoint_withDensity_real
#print axioms StokeyLucasPrescott.StrongConvergence.inner_toLp_toLp
#print axioms StokeyLucasPrescott.StrongConvergence.cesaroCauchy_withDensity
#print axioms StokeyLucasPrescott.StrongConvergence.adjointOp_kpow_zero
#print axioms StokeyLucasPrescott.StrongConvergence.doeblinRef
#print axioms StokeyLucasPrescott.StrongConvergence.doeblinRef_apply
#print axioms StokeyLucasPrescott.StrongConvergence.tsum_inv_two_pow_succ
#print axioms StokeyLucasPrescott.StrongConvergence.isFinite_doeblinRef
#print axioms StokeyLucasPrescott.StrongConvergence.le_two_doeblinRef
#print axioms StokeyLucasPrescott.StrongConvergence.adjoint_doeblinRef_le
#print axioms StokeyLucasPrescott.StrongConvergence.adjoint_kpow_doeblinRef_le
#print axioms StokeyLucasPrescott.StrongConvergence.doeblin_eps_le_one
#print axioms StokeyLucasPrescott.StrongConvergence.refBound
#print axioms StokeyLucasPrescott.StrongConvergence.refBound_nonneg
#print axioms StokeyLucasPrescott.StrongConvergence.adjoint_real_le_ref
#print axioms StokeyLucasPrescott.StrongConvergence.cesaro_small
#print axioms StokeyLucasPrescott.StrongConvergence.abs_sub_levels_le
#print axioms StokeyLucasPrescott.StrongConvergence.abs_integral_sub_levels_le
#print axioms StokeyLucasPrescott.StrongConvergence.hyperfilter_le_atTop
#print axioms StokeyLucasPrescott.StrongConvergence.cesaroLim
#print axioms StokeyLucasPrescott.StrongConvergence.tendsto_ultra_of_mem
#print axioms StokeyLucasPrescott.StrongConvergence.tendsto_cesaroLim
#print axioms StokeyLucasPrescott.StrongConvergence.tendsto_ultra
#print axioms StokeyLucasPrescott.StrongConvergence.cesaroLim_union
#print axioms StokeyLucasPrescott.StrongConvergence.cesaroLim_nonneg
#print axioms StokeyLucasPrescott.StrongConvergence.cesaroLim_univ
#print axioms StokeyLucasPrescott.StrongConvergence.cesaroLim_empty
#print axioms StokeyLucasPrescott.StrongConvergence.hasSum_cesaroLim
#print axioms StokeyLucasPrescott.StrongConvergence.adjoint_cesaroM
#print axioms StokeyLucasPrescott.StrongConvergence.tendsto_integral_ultra
#print axioms StokeyLucasPrescott.StrongConvergence.exists_invariant
#print axioms StokeyLucasPrescott.StrongConvergence.iSup_min_natCast
#print axioms StokeyLucasPrescott.StrongConvergence.cesaroCauchy_of_absCont
#print axioms StokeyLucasPrescott.StrongConvergence.doeblin_decomp
#print axioms StokeyLucasPrescott.StrongConvergence.cesaroCauchy_of_concentrated
#print axioms StokeyLucasPrescott.StrongConvergence.iInf_shift_antitone
#print axioms StokeyLucasPrescott.StrongConvergence.tendsto_kpow_transient
#print axioms StokeyLucasPrescott.StrongConvergence.tendsto_adjoint_transient
#print axioms StokeyLucasPrescott.StrongConvergence.exists_invariant_on
#print axioms StokeyLucasPrescott.StrongConvergence.cesaroCauchy_all
#print axioms StokeyLucasPrescott.StrongConvergence.theorem_11_9b
#print axioms StokeyLucasPrescott.StrongConvergence.invariant_transient_null
#print axioms StokeyLucasPrescott.StrongConvergence.restrict_invariant
#print axioms StokeyLucasPrescott.StrongConvergence.theorem_11_9c
#print axioms StokeyLucasPrescott.StrongConvergence.ergodic_count_eq_one
#print axioms StokeyLucasPrescott.StrongConvergence.theorem_11_10b
#print axioms StokeyLucasPrescott.StrongConvergence.theorem_11_10c
