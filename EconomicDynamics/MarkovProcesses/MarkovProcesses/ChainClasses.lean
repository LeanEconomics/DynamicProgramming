/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovProcesses.ChainBasics
import Mathlib.Data.Fintype.Card

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
