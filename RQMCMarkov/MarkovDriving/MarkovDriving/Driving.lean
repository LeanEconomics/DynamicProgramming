/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDriving.Unbiased
import Mathlib.Data.Int.Star

/-!
# Driving a finite Markov chain by uniforms: inverse CDF, paths, stacks, counts (post #3)

Post #3 simulates a chain with `n` states and transition matrix `P` by the inverse-CDF rule: from
state `i` with a uniform `u`, go to the smallest `j` with `u ≤ cs_{ij} = Σ_{k ≤ j} p_{ik}`. A
uniform sequence `u¹, u², …` then "drives" the chain; in the stack representation each state has
its own sequence, and the `k`-th departure from `i` uses point `k` of stack `i`.

**Conventions.** States are `Fin n`, `0`-indexed (post #3's `x_j` is `j - 1 : Fin n`); a
stochastic matrix is `P : Fin n → Fin n → ℝ` with `IsStochastic P` (nonnegative rows summing to
one). Time starts at `0`: a path is `x : ℕ → S` with `x 0 = x₀`, and `u t` drives the
transition `t → t + 1` (post #3's `u^t` and `x^{t+1}`). Counts over the horizon `T` use the
times `t < T` (occupation) and the transitions `t → t + 1`, `t < T`.

## Main definitions

* `IsStochastic P`; `cumProb P i m = Σ_{k < m} P i k` (post #3's `cs_{ij}` is `cumProb P i j`);
  `step P i u`, the inverse-CDF update, total (the last state when no `j` qualifies, `u > 1`).
* `drive G x₀ u` (any update rule `G : S → α → S`) and `drivenPath P x₀ u = drive (step P) x₀ u`.
* `stackDrive G x₀ v` (per-state stacks `v : S → ℕ → α`), `stackPath P x₀ v`, and the
  `departureIndex path t = #{t' < t : path t' = path t}`.
* `occCount path i T` (the visit counter) and `transCount path i j T`.
* `IsSpellStart`, `runLength path t T` (censored at `T`), `spellCount path i T`.

## Main results

* `step_eq_iff`: for `u ∈ (0, 1]`, `step P i u = j ↔ cs_{i,j-1} < u ≤ cs_{ij}`;
  `step_preimage_inter_Ioc`, `step_mono`, `measurable_step`; `step_zero` (precision: at `u = 0`
  the rule picks the first state even if `p_{i1} = 0`, a null event).
* `uniformIco_step_eq`, `volume_step_eq`: `volume {u ∈ [0,1) : step P i u = j} = P i j`
  (post #3, "the probability that it falls in the interval … is exactly … `p_{2j}`").
* `step_post3_example`: post #3's `n = 3` example (`u = 0.79` goes to the second state).
* `drive_eq_iff`, `stackDrive_eq_iff`: pathwise descriptions (the path equals `s` up to `T` iff
  `s` starts at `x₀` and each transition of `s` is produced by the corresponding uniform);
  `stackDrive_succ` ("the `k`-th visit to state `i` uses point `k` of stack `i`");
  `departureIndex_injective`: the stack entries used at different times are different.
* Counts: `occCount_succ`, `transCount_succ`, `occCount_add`, `transCount_add`,
  `sum_occCount` (`Σ_i N_i(T) = T`), `sum_transCount_right` (`Σ_j N_ij(T) = N_i(T)`),
  `sum_transCount_left`, `flowBalance`, `abs_flowBalance_le` (post #3, "every state is entered as
  often as it is left (allowing for the first and last states)").
* Spells: `runLength_eq_iff`, `spellCount_succ_eq` (spells of `i` = start + entries into `i`).
-/

namespace RQMCMarkov.MarkovDriving

open MeasureTheory Finset

/-- A **stochastic matrix** on a finite state space: nonnegative rows summing to one. -/
structure IsStochastic {S : Type*} [Fintype S] (P : S → S → ℝ) : Prop where
  /-- Every transition probability is nonnegative. -/
  nonneg : ∀ i j, 0 ≤ P i j
  /-- Every row sums to one. -/
  sum_eq_one : ∀ i, ∑ j, P i j = 1

variable {n : ℕ}

/-- The cumulative row sum `cumProb P i m = Σ_{k < m} P i k` (states `Fin n`, `0`-indexed).
Post #3's `cs_{ij} = Σ_{k=1}^{j} p_{ik}` (`1`-indexed) is `cumProb P i j`; for a state
`j : Fin n` the post's interval `(cs_{i,j-1}, cs_{ij}]` is `(cumProb P i j, cumProb P i (j+1)]`. -/
noncomputable def cumProb (P : Fin n → Fin n → ℝ) (i : Fin n) (m : ℕ) : ℝ :=
  ∑ k ∈ univ.filter (fun k : Fin n ↦ (k : ℕ) < m), P i k

/-- The last state `n - 1` of `Fin n` (`Fin n` is nonempty since it contains `i`). -/
def lastState (i : Fin n) : Fin n := ⟨n - 1, by have := i.isLt; omega⟩

/-- **The inverse-CDF update** (post #3): from state `i` with uniform `u`, go to the smallest
`j` with `u ≤ cs_{ij}`, i.e. `u ≤ cumProb P i (j + 1)`. Total: if no such `j` exists (only when
`u > 1`), go to the last state. -/
noncomputable def step (P : Fin n → Fin n → ℝ) (i : Fin n) (u : ℝ) : Fin n :=
  (insert (lastState i) (univ.filter fun j : Fin n ↦ u ≤ cumProb P i (j + 1))).min'
    (insert_nonempty _ _)

/-- `cumProb P i 0 = 0`. -/
theorem cumProb_zero (P : Fin n → Fin n → ℝ) (i : Fin n) : cumProb P i 0 = 0 := by
  unfold cumProb
  rw [Finset.sum_eq_zero]
  intro k hk
  exact absurd (Finset.mem_filter.1 hk).2 (Nat.not_lt_zero _)

/-- `cumProb P i (j + 1) = cumProb P i j + P i j`. -/
theorem cumProb_succ (P : Fin n → Fin n → ℝ) (i j : Fin n) :
    cumProb P i (j + 1) = cumProb P i j + P i j := by
  unfold cumProb
  have h : univ.filter (fun k : Fin n ↦ (k : ℕ) < j + 1) =
      insert j (univ.filter (fun k : Fin n ↦ (k : ℕ) < j)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    rw [Nat.lt_succ_iff, Nat.le_iff_lt_or_eq, Fin.ext_iff]
    tauto
  rw [h, Finset.sum_insert, add_comm]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, lt_irrefl, not_false_eq_true]

/-- For `m ≥ n`, `cumProb P i m` is the whole row sum. -/
theorem cumProb_of_le (P : Fin n → Fin n → ℝ) (i : Fin n) {m : ℕ} (hm : n ≤ m) :
    cumProb P i m = ∑ k, P i k := by
  unfold cumProb
  rw [Finset.filter_true_of_mem]
  intro k _
  exact lt_of_lt_of_le k.isLt hm

/-- The cumulative sums of a nonnegative row are monotone. -/
theorem cumProb_mono {P : Fin n → Fin n → ℝ} (hP : ∀ i j, 0 ≤ P i j) (i : Fin n) :
    Monotone (cumProb P i) := by
  intro a b hab
  unfold cumProb
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ ↦ hP i k)
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  omega

/-- The cumulative sums of a stochastic row lie in `[0, 1]`. -/
theorem cumProb_mem_Icc {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n) (m : ℕ) :
    cumProb P i m ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · rw [← cumProb_zero P i]
    exact cumProb_mono hP.nonneg i (Nat.zero_le m)
  · rw [← hP.sum_eq_one i, ← cumProb_of_le P i (le_max_left n m)]
    exact cumProb_mono hP.nonneg i (le_max_right n m)

/-- **The inverse-CDF rule** (post #3): for `u ∈ (0, 1]`, `step P i u = j` iff
`cs_{i,j-1} < u ≤ cs_{ij}`, i.e. `cumProb P i j < u ≤ cumProb P i (j + 1)`. -/
theorem step_eq_iff {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i j : Fin n) {u : ℝ}
    (hu : u ∈ Set.Ioc (0 : ℝ) 1) :
    step P i u = j ↔ cumProb P i j < u ∧ u ≤ cumProb P i (j + 1) := by
  have hlast : cumProb P i ((lastState i : ℕ) + 1) = 1 := by
    rw [cumProb_of_le P i (by simp only [lastState]; omega), hP.sum_eq_one i]
  constructor
  · intro h
    have hj : j ∈ insert (lastState i) (univ.filter fun j : Fin n ↦ u ≤ cumProb P i (j + 1)) :=
      h ▸ Finset.min'_mem _ _
    refine ⟨?_, ?_⟩
    · by_cases hj0 : (j : ℕ) = 0
      · rw [hj0, cumProb_zero]
        exact hu.1
      · by_contra hcon
        have hk : (⟨j - 1, by omega⟩ : Fin n) ∈
            insert (lastState i) (univ.filter fun j : Fin n ↦ u ≤ cumProb P i (j + 1)) := by
          refine Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩)
          have : (j : ℕ) - 1 + 1 = j := by omega
          change u ≤ cumProb P i ((j : ℕ) - 1 + 1)
          rw [this]
          exact le_of_not_gt hcon
        have hle : step P i u ≤ ⟨j - 1, by omega⟩ := Finset.min'_le _ _ hk
        rw [h, Fin.le_def] at hle
        change (j : ℕ) ≤ j - 1 at hle
        omega
    · rcases Finset.mem_insert.1 hj with hj | hj
      · rw [hj, hlast]
        exact hu.2
      · exact (Finset.mem_filter.1 hj).2
  · rintro ⟨h1, h2⟩
    have hj : j ∈ insert (lastState i) (univ.filter fun j : Fin n ↦ u ≤ cumProb P i (j + 1)) :=
      Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩)
    refine le_antisymm (Finset.min'_le _ _ hj) (Finset.le_min' _ _ _ ?_)
    intro y hy
    rcases Finset.mem_insert.1 hy with hy | hy
    · rw [hy, Fin.le_def]
      simp only [lastState]
      omega
    · have hy' := (Finset.mem_filter.1 hy).2
      by_contra hlt
      rw [not_le, Fin.lt_def] at hlt
      have := cumProb_mono hP.nonneg i (show (y : ℕ) + 1 ≤ j by omega)
      linarith

/-- The inverse-CDF update is monotone in the uniform. -/
theorem step_mono (P : Fin n → Fin n → ℝ) (i : Fin n) : Monotone (step P i) := by
  intro u u' huu'
  refine Finset.min'_subset _ ?_
  intro j hj
  rcases Finset.mem_insert.1 hj with hj | hj
  · exact hj ▸ Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_filter.2
      ⟨Finset.mem_univ _, le_trans huu' (Finset.mem_filter.1 hj).2⟩)

/-- **Precision on post #3's rule at `u = 0`**: "the smallest index such that `u ≤ cs`" sends
`u = 0` to the first state even when `p_{i1} = 0`; this is why `step_eq_iff` takes
`u ∈ (0, 1]`. The event `u = 0` has probability zero, so the law is unaffected. -/
theorem step_zero {P : Fin n → Fin n → ℝ} (hP : ∀ i j, 0 ≤ P i j) (i : Fin n) :
    (step P i 0 : ℕ) = 0 := by
  have h0 : (⟨0, by have := i.isLt; omega⟩ : Fin n) ∈
      insert (lastState i) (univ.filter fun j : Fin n ↦ (0 : ℝ) ≤ cumProb P i (j + 1)) := by
    refine Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩)
    rw [← cumProb_zero P i]
    exact cumProb_mono hP i (Nat.zero_le _)
  have hle : step P i 0 ≤ ⟨0, by have := i.isLt; omega⟩ := Finset.min'_le _ _ h0
  rw [Fin.le_def] at hle
  exact Nat.le_zero.1 hle

/-- The inverse-CDF update is measurable in the uniform. -/
theorem measurable_step (P : Fin n → Fin n → ℝ) (i : Fin n) : Measurable (step P i) := by
  refine measurable_to_countable' fun j ↦ ?_
  refine Set.OrdConnected.measurableSet ⟨fun a ha b hb x hx ↦ ?_⟩
  have ha' : step P i a = j := ha
  have hb' : step P i b = j := hb
  change step P i x = j
  exact le_antisymm (hb' ▸ step_mono P i hx.2) (ha' ▸ step_mono P i hx.1)

/-- The preimage of `j` within `(0, 1]` is post #3's interval `(cs_{i,j-1}, cs_{ij}]`. -/
theorem step_preimage_inter_Ioc {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i j : Fin n) :
    {u | step P i u = j} ∩ Set.Ioc 0 1 = Set.Ioc (cumProb P i j) (cumProb P i (j + 1)) := by
  ext u
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioc]
  constructor
  · rintro ⟨h, hu⟩
    exact (step_eq_iff hP i j hu).1 h
  · rintro ⟨h1, h2⟩
    have hu : u ∈ Set.Ioc (0 : ℝ) 1 :=
      ⟨lt_of_le_of_lt (cumProb_mem_Icc hP i j).1 h1, h2.trans (cumProb_mem_Icc hP i _).2⟩
    exact ⟨(step_eq_iff hP i j hu).2 ⟨h1, h2⟩, hu⟩

/-- **Key fact** (post #3): "the probability that [the uniform] falls in the interval
`(cs_{2,j-1}, cs_{2j}]` is exactly `p_{2j}`": `U[0,1){u : step P i u = j} = P i j`. -/
theorem uniformIco_step_eq {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i j : Fin n) :
    uniformIco {u | step P i u = j} = ENNReal.ofReal (P i j) := by
  rw [uniformIco_eq_restrict_Ioc, Measure.restrict_apply' measurableSet_Ioc,
    step_preimage_inter_Ioc hP, Real.volume_Ioc, cumProb_succ, add_sub_cancel_left]

/-- **Key fact**, Lebesgue form: `volume {u ∈ [0,1) : step P i u = j} = P i j`. -/
theorem volume_step_eq {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i j : Fin n) :
    volume ({u | step P i u = j} ∩ Set.Ico 0 1) = ENNReal.ofReal (P i j) := by
  rw [← uniformIco_step_eq hP i j, Measure.restrict_apply' measurableSet_Ico]

/-- **Post #3's worked example**: with `n = 3` and row `[0.2, 0.6, 0.2]` from the second state
(`1 : Fin 3`), the draw `u = 0.79` sends the chain to the second state, "because this is above
0.2 and below 0.8"; draws in `(0, 0.2]` go to the first state and draws in `(0.8, 1]` to the
third. -/
theorem step_post3_example {P : Fin 3 → Fin 3 → ℝ} (hP : IsStochastic P) (h0 : P 1 0 = 0.2)
    (h1 : P 1 1 = 0.6) (h2 : P 1 2 = 0.2) :
    step P 1 0.79 = 1 ∧ (∀ u ∈ Set.Ioc (0 : ℝ) 0.2, step P 1 u = 0) ∧
      (∀ u ∈ Set.Ioc (0.8 : ℝ) 1, step P 1 u = 2) := by
  have c0 : cumProb P 1 0 = 0 := cumProb_zero P 1
  have c1 : cumProb P 1 1 = 0.2 := by
    have : cumProb P 1 1 = cumProb P 1 0 + P 1 0 := cumProb_succ P 1 0
    change cumProb P 1 1 = 0.2
    rw [this, c0, h0, zero_add]
  have c2 : cumProb P 1 2 = 0.8 := by
    have : cumProb P 1 2 = cumProb P 1 1 + P 1 1 := cumProb_succ P 1 1
    change cumProb P 1 2 = 0.8
    rw [this, c1, h1]
    norm_num
  have c3 : cumProb P 1 3 = 1 := by
    have : cumProb P 1 3 = cumProb P 1 2 + P 1 2 := cumProb_succ P 1 2
    change cumProb P 1 3 = 1
    rw [this, c2, h2]
    norm_num
  refine ⟨?_, fun u hu ↦ ?_, fun u hu ↦ ?_⟩
  · rw [step_eq_iff hP 1 1 ⟨by norm_num, by norm_num⟩]
    change cumProb P 1 1 < 0.79 ∧ 0.79 ≤ cumProb P 1 (1 + 1)
    rw [c1, c2]
    norm_num
  · rw [step_eq_iff hP 1 0 ⟨hu.1, hu.2.trans (by norm_num)⟩]
    change cumProb P 1 0 < u ∧ u ≤ cumProb P 1 (0 + 1)
    rw [c0, c1]
    exact hu
  · rw [step_eq_iff hP 1 2 ⟨lt_trans (by norm_num) hu.1, hu.2⟩]
    change cumProb P 1 2 < u ∧ u ≤ cumProb P 1 (2 + 1)
    rw [c2, c3]
    exact hu

/-! ### Paths driven by a sequence -/

variable {S : Type*}

/-- The path driven by a sequence `u` through an update rule `G` (post #3, "this sequence of
uniform random numbers 'driving' the Markov chain"): `x 0 = x₀`, `x (t+1) = G (x t) (u t)`. So
`u t` drives the transition from time `t` to `t + 1` (post #3's `u^t`, `x^{t+1}`, shifted to
start at `0`). -/
def drive {α : Type*} (G : S → α → S) (x₀ : S) (u : ℕ → α) : ℕ → S
  | 0 => x₀
  | t + 1 => G (drive G x₀ u t) (u t)

/-- The path driven by `u` from `x₀` with the inverse-CDF update `step P` (post #3's MC/QMC
simulation of the chain, depending on what `u` is). -/
noncomputable abbrev drivenPath (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (u : ℕ → ℝ) : ℕ → Fin n :=
  drive (step P) x₀ u

/-- `drive` starts at `x₀`. -/
theorem drive_zero {α : Type*} (G : S → α → S) (x₀ : S) (u : ℕ → α) : drive G x₀ u 0 = x₀ :=
  rfl

/-- The recursion of `drive`. -/
theorem drive_succ {α : Type*} (G : S → α → S) (x₀ : S) (u : ℕ → α) (t : ℕ) :
    drive G x₀ u (t + 1) = G (drive G x₀ u t) (u t) :=
  rfl

/-- **Pathwise description of `drive`**: the driven path equals `s` at times `0, …, T` iff
`s 0 = x₀` and every transition `s t → s (t+1)`, `t < T`, is the update of `s t` by `u t`. -/
theorem drive_eq_iff {α : Type*} (G : S → α → S) (x₀ : S) (u : ℕ → α) (s : ℕ → S) (T : ℕ) :
    (∀ t ≤ T, drive G x₀ u t = s t) ↔ s 0 = x₀ ∧ ∀ t < T, G (s t) (u t) = s (t + 1) := by
  induction T with
  | zero =>
    constructor
    · intro h
      exact ⟨(h 0 le_rfl).symm, fun t ht ↦ absurd ht (Nat.not_lt_zero t)⟩
    · rintro ⟨h0, -⟩ t ht
      rw [Nat.le_zero.1 ht]
      exact h0.symm
  | succ T ih =>
    constructor
    · intro h
      have hT := ih.1 fun t ht ↦ h t (ht.trans (Nat.le_succ T))
      refine ⟨hT.1, fun t ht ↦ ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | ht
      · exact hT.2 t ht
      · rw [ht, ← h T (Nat.le_succ T), ← h (T + 1) le_rfl, drive_succ]
    · rintro ⟨h0, hs⟩ t ht
      have hT := ih.2 ⟨h0, fun t ht ↦ hs t (ht.trans (Nat.lt_succ_self T))⟩
      rcases Nat.le_succ_iff.1 ht with ht | ht
      · exact hT t ht
      · rw [ht, drive_succ, hT T le_rfl, hs T (Nat.lt_succ_self T)]

/-! ### Counts -/

variable [DecidableEq S]

/-- **Occupation count** (the visit counter): `occCount path i T = #{t < T : path t = i}`, the
number of visits to `i` strictly before time `T` (times `0, …, T - 1`). -/
def occCount (path : ℕ → S) (i : S) (T : ℕ) : ℕ :=
  ((range T).filter fun t ↦ path t = i).card

/-- **Transition count** `transCount path i j T = #{t < T : path t = i ∧ path (t+1) = j}`, the
number of transitions `i → j` among the first `T` transitions (times `0 → 1, …, T-1 → T`). -/
def transCount (path : ℕ → S) (i j : S) (T : ℕ) : ℕ :=
  ((range T).filter fun t ↦ path t = i ∧ path (t + 1) = j).card

/-- No visits before time `0`. -/
theorem occCount_zero (path : ℕ → S) (i : S) : occCount path i 0 = 0 := rfl

/-- No transitions before time `0`. -/
theorem transCount_zero (path : ℕ → S) (i j : S) : transCount path i j 0 = 0 := rfl

/-- One more period adds one visit iff the path is in `i` at time `T`. -/
theorem occCount_succ (path : ℕ → S) (i : S) (T : ℕ) :
    occCount path i (T + 1) = occCount path i T + if path T = i then 1 else 0 := by
  unfold occCount
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : path T = i
  · simp only [h, ↓reduceIte]
    rw [Finset.card_insert_of_notMem]
    intro hT
    exact lt_irrefl T (Finset.mem_range.1 (Finset.mem_filter.1 hT).1)
  · simp only [h, ↓reduceIte, add_zero]

/-- One more transition adds one to `transCount i j` iff it is `i → j`. -/
theorem transCount_succ (path : ℕ → S) (i j : S) (T : ℕ) :
    transCount path i j (T + 1) =
      transCount path i j T + if path T = i ∧ path (T + 1) = j then 1 else 0 := by
  unfold transCount
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : path T = i ∧ path (T + 1) = j
  · simp only [h, and_self, ↓reduceIte]
    rw [Finset.card_insert_of_notMem]
    intro hT
    exact lt_irrefl T (Finset.mem_range.1 (Finset.mem_filter.1 hT).1)
  · simp only [h, ↓reduceIte, add_zero]

/-- At most `T` visits before time `T`. -/
theorem occCount_le (path : ℕ → S) (i : S) (T : ℕ) : occCount path i T ≤ T :=
  (Finset.card_filter_le _ _).trans (Finset.card_range T).le

/-- The occupation count is monotone in the horizon. -/
theorem occCount_mono (path : ℕ → S) (i : S) {T T' : ℕ} (h : T ≤ T') :
    occCount path i T ≤ occCount path i T' :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.2 h))

/-- `transCount i j ≤ occCount i`. -/
theorem transCount_le_occCount (path : ℕ → S) (i j : S) (T : ℕ) :
    transCount path i j T ≤ occCount path i T :=
  Finset.card_le_card fun t ht ↦ by
    rw [Finset.mem_filter] at ht ⊢
    exact ⟨ht.1, ht.2.1⟩

/-- The occupation count before `T` depends only on the path before `T`. -/
theorem occCount_congr {p q : ℕ → S} {T : ℕ} (h : ∀ t < T, p t = q t) (i : S) :
    occCount p i T = occCount q i T := by
  unfold occCount
  rw [Finset.filter_congr fun t ht ↦ by rw [h t (Finset.mem_range.1 ht)]]

/-- The first `T` transition counts depend only on the path up to time `T`. -/
theorem transCount_congr {p q : ℕ → S} {T : ℕ} (h : ∀ t ≤ T, p t = q t) (i j : S) :
    transCount p i j T = transCount q i j T := by
  unfold transCount
  refine congrArg _ (Finset.filter_congr fun t ht ↦ ?_)
  have ht' := Finset.mem_range.1 ht
  rw [h t ht'.le, h (t + 1) ht']

/-- Splitting the horizon: visits before `a + b` are those before `a` plus those of the shifted
path `t ↦ path (a + t)` before `b`. -/
theorem occCount_add (path : ℕ → S) (i : S) (a b : ℕ) :
    occCount path i (a + b) = occCount path i a + occCount (fun t ↦ path (a + t)) i b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [← add_assoc, occCount_succ, ih, occCount_succ, add_assoc]

/-- Splitting the horizon for transition counts. -/
theorem transCount_add (path : ℕ → S) (i j : S) (a b : ℕ) :
    transCount path i j (a + b) =
      transCount path i j a + transCount (fun t ↦ path (a + t)) i j b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [← add_assoc, transCount_succ, ih, transCount_succ, add_assoc]
    rfl

/-! ### Per-state stacks -/

/-- The **departure index** at time `t`: the number of earlier visits to the current state,
`#{t' < t : path t' = path t}`. The departure from `path t` at time `t` is the
`departureIndex`-th departure (counting from `0`) from that state. -/
def departureIndex (path : ℕ → S) (t : ℕ) : ℕ := occCount path (path t) t

/-- The departure index at time `t` depends only on the path up to time `t`. -/
theorem departureIndex_congr {p q : ℕ → S} {t : ℕ} (h : ∀ t' ≤ t, p t' = q t') :
    departureIndex p t = departureIndex q t := by
  unfold departureIndex
  rw [h t le_rfl]
  exact occCount_congr (fun t' ht' ↦ h t' ht'.le) _

/-- Later visits to the same state have larger departure indices; so the pairs
`(path t, departureIndex path t)` are distinct for distinct `t`. -/
theorem departureIndex_lt {path : ℕ → S} {t t' : ℕ} (htt' : t < t') (h : path t = path t') :
    departureIndex path t < departureIndex path t' := by
  unfold departureIndex
  rw [← h]
  have h1 := occCount_succ path (path t) t
  simp only [eq_self, ↓reduceIte] at h1
  have h2 := occCount_mono path (path t) (show t + 1 ≤ t' from htt')
  omega

/-- Injectivity of `t ↦ (path t, departureIndex path t)`. -/
theorem departureIndex_injective (path : ℕ → S) :
    Function.Injective fun t ↦ (path t, departureIndex path t) := by
  intro t t' h
  simp only [Prod.mk.injEq] at h
  rcases lt_trichotomy t t' with htt' | htt' | htt'
  · exact absurd h.2 (departureIndex_lt htt' h.1).ne
  · exact htt'
  · exact absurd h.2 (departureIndex_lt htt' h.1.symm).ne'

/-- The state and the per-state departure counters of the stack representation. -/
def stackState {α : Type*} (G : S → α → S) (x₀ : S) (v : S → ℕ → α) : ℕ → S × (S → ℕ)
  | 0 => (x₀, fun _ ↦ 0)
  | t + 1 =>
    let p := stackState G x₀ v t
    (G p.1 (v p.1 (p.2 p.1)), Function.update p.2 p.1 (p.2 p.1 + 1))

/-- **The stack representation** (post #3, "each state has its own stack … the `k`-th visit to
state `i` uses point `k` of stack `i`"): each state `i` has its own sequence `v i`, and the
`k`-th departure from `i` (`k = 0, 1, …`) is driven by `v i k` through the update `G`. -/
def stackDrive {α : Type*} (G : S → α → S) (x₀ : S) (v : S → ℕ → α) (t : ℕ) : S :=
  (stackState G x₀ v t).1

/-- The stack-driven chain with the inverse-CDF update. -/
noncomputable abbrev stackPath (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (v : Fin n → ℕ → ℝ) :
    ℕ → Fin n :=
  stackDrive (step P) x₀ v

/-- The counters of `stackState` are the visit counts of the stack path. -/
theorem stackState_snd {α : Type*} (G : S → α → S) (x₀ : S) (v : S → ℕ → α) (t : ℕ) (i : S) :
    (stackState G x₀ v t).2 i = occCount (stackDrive G x₀ v) i t := by
  induction t generalizing i with
  | zero => rfl
  | succ t ih =>
    rw [occCount_succ, ← ih]
    change Function.update (stackState G x₀ v t).2 (stackState G x₀ v t).1
      ((stackState G x₀ v t).2 (stackState G x₀ v t).1 + 1) i = _
    unfold stackDrive
    by_cases h : (stackState G x₀ v t).1 = i
    · subst h
      rw [Function.update_self]
      simp only [eq_self, ↓reduceIte]
    · rw [Function.update_of_ne (Ne.symm h)]
      simp only [h, ↓reduceIte, add_zero]

/-- `stackDrive` starts at `x₀`. -/
theorem stackDrive_zero {α : Type*} (G : S → α → S) (x₀ : S) (v : S → ℕ → α) :
    stackDrive G x₀ v 0 = x₀ :=
  rfl

/-- **The stack recursion**: the transition at time `t` uses entry `departureIndex t` of the
stack of the current state. -/
theorem stackDrive_succ {α : Type*} (G : S → α → S) (x₀ : S) (v : S → ℕ → α) (t : ℕ) :
    stackDrive G x₀ v (t + 1) = G (stackDrive G x₀ v t)
      (v (stackDrive G x₀ v t) (departureIndex (stackDrive G x₀ v) t)) := by
  unfold departureIndex
  rw [← stackState_snd]
  rfl

/-- **Pathwise description of the stack representation**: the stack path equals `s` at times
`0, …, T` iff `s 0 = x₀` and each transition `s t → s (t+1)`, `t < T`, is the update of `s t`
by entry `departureIndex s t` of stack `s t`. -/
theorem stackDrive_eq_iff {α : Type*} (G : S → α → S) (x₀ : S) (v : S → ℕ → α) (s : ℕ → S)
    (T : ℕ) : (∀ t ≤ T, stackDrive G x₀ v t = s t) ↔
      s 0 = x₀ ∧ ∀ t < T, G (s t) (v (s t) (departureIndex s t)) = s (t + 1) := by
  induction T with
  | zero =>
    constructor
    · intro h
      exact ⟨(h 0 le_rfl).symm, fun t ht ↦ absurd ht (Nat.not_lt_zero t)⟩
    · rintro ⟨h0, -⟩ t ht
      rw [Nat.le_zero.1 ht]
      exact h0.symm
  | succ T ih =>
    constructor
    · intro h
      have hT := ih.1 fun t ht ↦ h t (ht.trans (Nat.le_succ T))
      refine ⟨hT.1, fun t ht ↦ ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | ht
      · exact hT.2 t ht
      · rw [ht, ← h T (Nat.le_succ T), ← h (T + 1) le_rfl, stackDrive_succ,
          departureIndex_congr fun t' ht' ↦ h t' (ht'.trans (Nat.le_succ T))]
    · rintro ⟨h0, hs⟩ t ht
      have hT := ih.2 ⟨h0, fun t ht ↦ hs t (ht.trans (Nat.lt_succ_self T))⟩
      rcases Nat.le_succ_iff.1 ht with ht | ht
      · exact hT t ht
      · rw [ht, stackDrive_succ, hT T le_rfl, departureIndex_congr hT,
          hs T (Nat.lt_succ_self T)]

/-! ### Spells -/

/-- A **spell** (maximal run of equal states) starts at time `t` iff `t = 0` or the state
changes at `t`. -/
abbrev IsSpellStart (path : ℕ → S) (t : ℕ) : Prop := t = 0 ∨ path (t - 1) ≠ path t

/-- The **length of the run starting at `t`**, censored at the horizon `T`: the number of
`k < T - t` such that the path stays in `path t` throughout times `t, …, t + k`. For a spell
start `t`, this is the length of that spell (or of its part before `T`). -/
def runLength (path : ℕ → S) (t T : ℕ) : ℕ :=
  ((range (T - t)).filter fun k ↦ ∀ m ≤ k, path (t + m) = path t).card

/-- The number of spells in state `i` that start before `T`. -/
def spellCount (path : ℕ → S) (i : S) (T : ℕ) : ℕ :=
  ((range T).filter fun t ↦ IsSpellStart path t ∧ path t = i).card

/-- A run that stays exactly `k` periods and then leaves, before the horizon, has length `k`. -/
theorem runLength_eq_of_exit {path : ℕ → S} {t T k : ℕ} (hk : t + k < T)
    (hstay : ∀ m < k, path (t + m) = path t) (hexit : path (t + k) ≠ path t) :
    runLength path t T = k := by
  unfold runLength
  have : (range (T - t)).filter (fun k ↦ ∀ m ≤ k, path (t + m) = path t) = range k := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨-, hm⟩
      by_contra hmk
      exact hexit (hm k (not_lt.1 hmk))
    · intro hmk
      exact ⟨by omega, fun m' hm' ↦ hstay m' (lt_of_le_of_lt hm' hmk)⟩
  rw [this, Finset.card_range]

/-- **Run lengths**: for `t + k < T`, the run starting at `t` has length `k` iff the path stays
in `path t` for times `t, …, t + k - 1` and leaves at `t + k`. -/
theorem runLength_eq_iff {path : ℕ → S} {t T k : ℕ} (hk : t + k < T) :
    runLength path t T = k ↔
      (∀ m < k, path (t + m) = path t) ∧ path (t + k) ≠ path t := by
  constructor
  · intro h
    by_cases hall : ∀ m ≤ k, path (t + m) = path t
    · exfalso
      have hsub : range (k + 1) ⊆
          (range (T - t)).filter (fun k ↦ ∀ m ≤ k, path (t + m) = path t) := by
        intro m hm
        rw [Finset.mem_range] at hm
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, fun m' hm' ↦ hall m' (by omega)⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_range] at this
      unfold runLength at h
      omega
    · have hex : ∃ m, m ≤ k ∧ path (t + m) ≠ path t := by
        by_contra hne
        exact hall fun m hm ↦ by
          by_contra hm'
          exact hne ⟨m, hm, hm'⟩
      classical
      let m0 := Nat.find hex
      have hm0 : m0 ≤ k ∧ path (t + m0) ≠ path t := Nat.find_spec hex
      have hstay : ∀ m < m0, path (t + m) = path t := fun m hm ↦ by
        by_contra hne
        exact Nat.find_min hex hm ⟨by omega, hne⟩
      have := runLength_eq_of_exit (show t + m0 < T by omega) hstay hm0.2
      rw [h] at this
      rw [this]
      exact ⟨hstay, hm0.2⟩
  · rintro ⟨hstay, hexit⟩
    exact runLength_eq_of_exit hk hstay hexit

/-- One more period adds one spell of `i` iff a spell of `i` starts at time `T`. -/
theorem spellCount_succ (path : ℕ → S) (i : S) (T : ℕ) :
    spellCount path i (T + 1) =
      spellCount path i T + if IsSpellStart path T ∧ path T = i then 1 else 0 := by
  unfold spellCount
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : IsSpellStart path T ∧ path T = i
  · simp only [h, and_self, ↓reduceIte]
    rw [Finset.card_insert_of_notMem]
    intro hT
    exact lt_irrefl T (Finset.mem_range.1 (Finset.mem_filter.1 hT).1)
  · simp only [h, ↓reduceIte, add_zero]

variable [Fintype S]

/-- The occupation counts before `T` add up to `T`. -/
theorem sum_occCount (path : ℕ → S) (T : ℕ) : ∑ i, occCount path i T = T := by
  induction T with
  | zero => exact Finset.sum_const_zero
  | succ T ih =>
    simp only [occCount_succ]
    rw [Finset.sum_add_distrib, ih, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ↓reduceIte]

/-- **Departures**: `Σ_j transCount i j T = occCount i T` (each visit before `T` is followed by
exactly one transition among the first `T`). -/
theorem sum_transCount_right (path : ℕ → S) (i : S) (T : ℕ) :
    ∑ j, transCount path i j T = occCount path i T := by
  unfold transCount occCount
  rw [Finset.card_eq_sum_card_fiberwise (f := fun t ↦ path (t + 1)) (t := univ)
    (fun _ _ ↦ Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.filter_filter]

/-- **Arrivals**: `Σ_j transCount j i T + 1{path 0 = i} = occCount i T + 1{path T = i}`. -/
theorem sum_transCount_left (path : ℕ → S) (i : S) (T : ℕ) :
    ∑ j, transCount path j i T + (if path 0 = i then 1 else 0) =
      occCount path i T + if path T = i then 1 else 0 := by
  induction T with
  | zero => rw [Finset.sum_eq_zero fun j _ ↦ transCount_zero path j i, occCount_zero]
  | succ T ih =>
    simp only [transCount_succ]
    rw [Finset.sum_add_distrib, occCount_succ]
    have h1 : ∑ j, (if path T = j ∧ path (T + 1) = i then 1 else 0) =
        if path (T + 1) = i then 1 else 0 := by
      simp only [ite_and]
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_univ, ↓reduceIte]
    rw [h1]
    omega

/-- **Flow balance** (post #3, "every state is entered as often as it is left (allowing for
the first and last states)"): out-count minus in-count is `1{path 0 = i} − 1{path T = i}`. -/
theorem flowBalance (path : ℕ → S) (i : S) (T : ℕ) :
    (∑ j, transCount path i j T : ℤ) - ∑ j, transCount path j i T =
      (if path 0 = i then 1 else 0) - if path T = i then 1 else 0 := by
  have h1 := sum_transCount_right path i T
  have h2 := sum_transCount_left path i T
  have h1' : (∑ j, transCount path i j T : ℤ) = occCount path i T := by exact_mod_cast h1
  have h2' : (∑ j, transCount path j i T : ℤ) + (if path 0 = i then 1 else 0) =
      occCount path i T + if path T = i then 1 else 0 := by
    have := congrArg (fun m : ℕ ↦ (m : ℤ)) h2
    push_cast [apply_ite (fun m : ℕ ↦ (m : ℤ))] at this
    exact this
  push_cast
  linarith

/-- **Flow balance**, bound form: `|Σ_j transCount i j − Σ_j transCount j i| ≤ 1`. -/
theorem abs_flowBalance_le (path : ℕ → S) (i : S) (T : ℕ) :
    |(∑ j, transCount path i j T : ℤ) - ∑ j, transCount path j i T| ≤ 1 := by
  rw [flowBalance]
  split_ifs <;> norm_num

/-- All transition counts add up to the number of transitions `T`. -/
theorem sum_sum_transCount (path : ℕ → S) (T : ℕ) : ∑ i, ∑ j, transCount path i j T = T := by
  simp only [sum_transCount_right]
  exact sum_occCount path T

/-- **Spells are entries**: the spells of `i` starting at times `0, …, T` are the start (if
`path 0 = i`) plus the entries `j → i`, `j ≠ i`, among the first `T` transitions. -/
theorem spellCount_succ_eq (path : ℕ → S) (i : S) (T : ℕ) :
    spellCount path i (T + 1) =
      (if path 0 = i then 1 else 0) + ∑ j ∈ univ.erase i, transCount path j i T := by
  induction T with
  | zero =>
    rw [spellCount_succ, Finset.sum_eq_zero fun j _ ↦ transCount_zero path j i]
    have h0 : IsSpellStart path 0 := Or.inl rfl
    simp only [h0, true_and]
    change 0 + _ = _ + 0
    rw [zero_add, add_zero]
  | succ T ih =>
    rw [spellCount_succ, ih]
    simp only [transCount_succ]
    rw [Finset.sum_add_distrib]
    have h1 : ∑ j ∈ univ.erase i, (if path T = j ∧ path (T + 1) = i then 1 else 0) =
        if path T ≠ i ∧ path (T + 1) = i then 1 else 0 := by
      simp only [ite_and]
      rw [Finset.sum_ite_eq]
      by_cases h : path T = i
      · simp only [h, Finset.mem_erase, ne_eq, not_true_eq_false, false_and, ↓reduceIte]
      · simp only [h, Finset.mem_erase, ne_eq, not_false_eq_true, Finset.mem_univ, and_self,
          ↓reduceIte]
    rw [h1]
    have h2 : (IsSpellStart path (T + 1) ∧ path (T + 1) = i) ↔
        (path T ≠ i ∧ path (T + 1) = i) := by
      unfold IsSpellStart
      rw [Nat.add_sub_cancel]
      constructor
      · rintro ⟨h | h, hi⟩
        · exact absurd h (Nat.succ_ne_zero T)
        · exact ⟨hi ▸ h, hi⟩
      · rintro ⟨h, hi⟩
        exact ⟨Or.inr (hi ▸ h), hi⟩
    rw [if_congr h2 rfl rfl]
    omega

end RQMCMarkov.MarkovDriving
