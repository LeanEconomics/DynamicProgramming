/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NonlinearStateSpace.StrongMarkov
import Mathlib.Probability.Process.HittingTime

/-!
# Occupation, hitting and return times (MT §3.4.3)

Meyn and Tweedie, §3.4.3, pp. 64–67. For a measurable `A ⊆ X`:

* `occTime A = η_A = Σ_{n ≥ 1} 1_A(Φₙ)`, the occupation time (p. 64);
* `firstReturn A = τ_A = min{n ≥ 1 : Φₙ ∈ A}` and `firstHit A = σ_A = min{n ≥ 0 : Φₙ ∈ A}`
  (p. 64), both Mathlib's `hittingAfter`, valued in `ℕ ∪ {∞}`;
* `returnTimeK A k = τ_A(k)`, the time of the `k`-th visit to `A` after time `0` (3.29);
* `potKernel_eq_lintegral_occTime` (3.30): `U(x, A) = Σ_{n ≥ 1} Pⁿ(x, A) = E_x[η_A]`;
* `hitProb P A x = L(x, A) = P_x(τ_A < ∞)` (3.31), with `firstReturn_ne_top_iff`
  (`= P_x(Φ ever enters A)`) and `measurable_hitProb`;
* **Proposition 3.4.4** (`proposition_3_4_4`, p. 65): `τ_A` and `σ_A` are stopping times;
  `isStoppingTime_returnTimeK`: so are all the `τ_A(k)`;
* `pathKernel_first_step`: first-step analysis, `P_x(Φ₁ ∈ C, θΦ ∈ B) = ∫_C P(x, dy) P_y(B)`;
* `tabooKernel` (`(P I_{Aᶜ})ⁿ P`, p. 66) and the taboo probabilities `tabooProb`
  (`_AP^n(x, B) = P_x(Φₙ ∈ B, τ_A ≥ n)`, p. 67), with `tabooProb_one`, `tabooProb_succ` (3.33)
  and `tabooProb_eq_tabooKernel` (the operator form `_AP^n = (P I_{Aᶜ})^{n−1} P`);
* **Proposition 3.4.5** (`proposition_3_4_5_i`, `proposition_3_4_5_i_succ`,
  `proposition_3_4_5_ii`, p. 65) and its operator form `firstReturn_eq_tabooKernel`
  (`P_x(τ_A = k) = [(P I_{Aᶜ})^{k−1} P](x, A)`, p. 66);
* `hitProb_eq_tsum` (p. 66): `L(x, A) = Σ_k [(P I_{Aᶜ})^{k−1} P](x, A)`, and `hitProb_first_step`:
  `L(x, A) = P(x, A) + ∫_{Aᶜ} P(x, dy) L(y, A)`;
* `tabooPotKernel` (3.34): `U_A = Σ_{n ≥ 1} _APⁿ`, and `tabooPotKernel_self` (p. 67):
  `U_A(x, A) = L(x, A)`.

**Corrections.** None.
-/

namespace MeynTweedie.NonlinearStateSpace

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Definitions -/

/-- The occupation time `η_A = Σ_{n ≥ 1} 1_A(Φₙ)`, the number of visits to `A` after time `0`
(MT p. 64). -/
noncomputable def occTime (A : Set X) (ω : ℕ → X) : ℝ≥0∞ := ∑' n, A.indicator 1 (ω (n + 1))

/-- The first return time `τ_A = min{n ≥ 1 : Φₙ ∈ A}` (`∞` if there is none), MT p. 64. -/
noncomputable def firstReturn (A : Set X) : (ℕ → X) → WithTop ℕ :=
  hittingAfter (fun n ω => ω n) A 1

/-- The first hitting time `σ_A = min{n ≥ 0 : Φₙ ∈ A}` (`∞` if there is none), MT p. 64. -/
noncomputable def firstHit (A : Set X) : (ℕ → X) → WithTop ℕ :=
  hittingAfter (fun n ω => ω n) A 0

/-- The `k`-th return time `τ_A(k)` (3.29), MT p. 64: `τ_A(0) = 0` and
`τ_A(k + 1) = min{n > τ_A(k) : Φₙ ∈ A}` (`∞` once a return fails). -/
noncomputable def returnTimeK (A : Set X) : ℕ → (ℕ → X) → WithTop ℕ
  | 0 => fun _ => 0
  | k + 1 => fun ω => WithTop.recTopCoe (C := fun _ => WithTop ℕ) ⊤
      (fun m => hittingAfter (fun n ω => ω n) A (m + 1) ω) (returnTimeK A k ω)

/-- The return probability `L(x, A) = P_x(τ_A < ∞)` (3.31), MT p. 64. -/
noncomputable def hitProb (P : Kernel X X) [IsMarkovKernel P] (A : Set X) (x : X) : ℝ≥0∞ :=
  pathKernel P x {ω | firstReturn A ω ≠ ⊤}

/-! ### Pathwise facts -/

omit [MeasurableSpace X] in
/-- `τ_A(1) = τ_A`. -/
theorem returnTimeK_one (A : Set X) : returnTimeK A 1 = firstReturn A := rfl

omit [MeasurableSpace X] in
/-- On `{τ_A(k) = m}`, `τ_A(k + 1) = min{n ≥ m + 1 : Φₙ ∈ A}`. -/
theorem returnTimeK_succ_of_eq (A : Set X) {k m : ℕ} {ω : ℕ → X}
    (h : returnTimeK A k ω = WithTop.some m) :
    returnTimeK A (k + 1) ω = hittingAfter (fun n ω => ω n) A (m + 1) ω := by
  simp only [returnTimeK, h]
  rfl

omit [MeasurableSpace X] in
/-- On `{τ_A(k) = ∞}`, `τ_A(k + 1) = ∞`. -/
theorem returnTimeK_succ_of_top (A : Set X) {k : ℕ} {ω : ℕ → X}
    (h : returnTimeK A k ω = ⊤) : returnTimeK A (k + 1) ω = ⊤ := by
  simp only [returnTimeK, h]
  rfl

omit [MeasurableSpace X] in
/-- `τ_A < ∞` iff the chain enters `A` at some time `n ≥ 1` (MT (3.31)). -/
theorem firstReturn_ne_top_iff (A : Set X) (ω : ℕ → X) :
    firstReturn A ω ≠ ⊤ ↔ ∃ n, 1 ≤ n ∧ ω n ∈ A := by
  rw [firstReturn, ne_eq, hittingAfter_eq_top_iff]
  push Not
  rfl

omit [MeasurableSpace X] in
/-- `n ≤ τ_A` iff the chain avoids `A` at times `1, …, n − 1`. -/
theorem le_firstReturn_iff (A : Set X) (ω : ℕ → X) (n : ℕ) :
    WithTop.some n ≤ firstReturn A ω ↔ ∀ j, 1 ≤ j → j < n → ω j ∉ A := by
  rw [firstReturn, ← not_lt, hittingAfter_lt_iff]
  simp only [mem_Ico, not_exists, not_and]
  exact ⟨fun h j h1 h2 hj => h j ⟨h1, h2⟩ hj, fun h j hj => h j hj.1 hj.2⟩

omit [MeasurableSpace X] in
/-- `τ_A ≥ 1`. -/
theorem one_le_firstReturn (A : Set X) (ω : ℕ → X) : WithTop.some 1 ≤ firstReturn A ω :=
  le_hittingAfter ω

omit [MeasurableSpace X] in
/-- `τ_A = n + 1` iff `τ_A ≥ n + 1` and `Φₙ₊₁ ∈ A`. -/
theorem firstReturn_eq_iff (A : Set X) (ω : ℕ → X) (n : ℕ) :
    firstReturn A ω = WithTop.some (n + 1) ↔
      WithTop.some (n + 1) ≤ firstReturn A ω ∧ ω (n + 1) ∈ A := by
  constructor
  · intro h
    refine ⟨h.ge, ?_⟩
    have := hittingAfter_mem_set_of_ne_top (u := fun n (ω : ℕ → X) => ω n) (s := A) (n := 1)
      (ω := ω) (by rw [← firstReturn, h]; exact WithTop.coe_ne_top)
    rw [← firstReturn, h] at this
    exact this
  · rintro ⟨hle, hA⟩
    exact le_antisymm (hittingAfter_le_of_mem (by omega) hA) hle

omit [MeasurableSpace X] in
/-- `τ_A ≥ n + 2` iff `Φ₁ ∉ A` and `τ_A ∘ θ ≥ n + 1`. -/
theorem le_firstReturn_succ_iff (A : Set X) (ω : ℕ → X) (n : ℕ) :
    WithTop.some (n + 2) ≤ firstReturn A ω ↔
      ω 1 ∈ Aᶜ ∧ WithTop.some (n + 1) ≤ firstReturn A (shift 1 ω) := by
  rw [le_firstReturn_iff, le_firstReturn_iff]
  simp only [shift_apply, mem_compl_iff]
  constructor
  · intro h
    exact ⟨h 1 le_rfl (by omega), fun j hj1 hj2 => h (1 + j) (by omega) (by omega)⟩
  · rintro ⟨h1, h⟩ j hj1 hj2
    rcases Nat.lt_or_ge j 2 with hj | hj
    · rwa [show j = 1 by omega]
    · have := h (j - 1) (by omega) (by omega)
      rwa [show 1 + (j - 1) = j by omega] at this

omit [MeasurableSpace X] in
/-- `σ_A = 0` iff `Φ₀ ∈ A`. -/
theorem firstHit_eq_zero_iff (A : Set X) (ω : ℕ → X) :
    firstHit A ω = WithTop.some 0 ↔ ω 0 ∈ A := by
  constructor
  · intro h
    have := hittingAfter_mem_set_of_ne_top (u := fun n (ω : ℕ → X) => ω n) (s := A) (n := 0)
      (ω := ω) (by rw [← firstHit, h]; exact WithTop.coe_ne_top)
    rw [← firstHit, h] at this
    exact this
  · intro h
    exact le_antisymm (hittingAfter_le_of_mem le_rfl h) (le_hittingAfter ω)

omit [MeasurableSpace X] in
/-- If `Φ₀ ∉ A` then `σ_A = τ_A`. -/
theorem firstHit_eq_firstReturn (A : Set X) {ω : ℕ → X} (h : ω 0 ∉ A) :
    firstHit A ω = firstReturn A ω := by
  refine le_antisymm ?_ ?_
  · rcases eq_or_ne (firstReturn A ω) ⊤ with ht | ht
    · rw [ht]; exact le_top
    · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 ht
      have h1 := (firstReturn_eq_iff A ω (m - 1)).1
      have hm1 : 1 ≤ m := by
        have := one_le_firstReturn A ω
        rw [← hm] at this
        exact WithTop.coe_le_coe.1 this
      rw [show m = m - 1 + 1 by omega] at hm
      rw [← hm]
      exact hittingAfter_le_of_mem (Nat.zero_le _) (h1 hm.symm).2
  · rcases eq_or_ne (firstHit A ω) ⊤ with ht | ht
    · rw [ht]; exact le_top
    · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 ht
      have hmem := hittingAfter_mem_set_of_ne_top (u := fun n (ω : ℕ → X) => ω n) (s := A)
        (n := 0) (ω := ω) ht
      rw [← firstHit, ← hm] at hmem
      have hm0 : m ≠ 0 := by rintro rfl; exact h hmem
      rw [← hm]
      exact hittingAfter_le_of_mem (by omega) hmem

/-! ### Measurability and Proposition 3.4.4 -/

/-- The coordinate process is adapted to its natural filtration. -/
theorem adapted_coord : Adapted (natFilt (X := X)) fun n (ω : ℕ → X) => ω n :=
  fun n => measurable_coord_natFilt n

/-- **Proposition 3.4.4** (MT p. 65): `τ_A` and `σ_A` are stopping times. -/
theorem proposition_3_4_4 {A : Set X} (hA : MeasurableSet A) :
    IsStoppingTime (natFilt (X := X)) (firstReturn A) ∧
      IsStoppingTime (natFilt (X := X)) (firstHit A) :=
  ⟨adapted_coord.isStoppingTime_hittingAfter hA, adapted_coord.isStoppingTime_hittingAfter hA⟩

/-- Every `τ_A(k)` is a stopping time. -/
theorem isStoppingTime_returnTimeK {A : Set X} (hA : MeasurableSet A) (k : ℕ) :
    IsStoppingTime (natFilt (X := X)) (returnTimeK A k) := by
  induction k with
  | zero => exact isStoppingTime_const _ 0
  | succ k ih =>
    intro i
    have hset : {ω | returnTimeK A (k + 1) ω ≤ WithTop.some i} =
        ⋃ m ∈ Finset.range (i + 1), {ω | returnTimeK A k ω = WithTop.some m} ∩
          {ω | hittingAfter (fun n (ω : ℕ → X) => ω n) A (m + 1) ω ≤ WithTop.some i} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, Finset.mem_range, exists_prop]
      constructor
      · intro h
        cases hk : returnTimeK A k ω with
        | top => rw [returnTimeK_succ_of_top A hk] at h; simp at h
        | coe m =>
          rw [returnTimeK_succ_of_eq A hk] at h
          have hle := (le_hittingAfter (u := fun n (ω : ℕ → X) => ω n) (s := A)
            (n := m + 1) ω).trans h
          exact ⟨m, by have := WithTop.coe_le_coe.1 hle; omega, rfl, h⟩
      · rintro ⟨m, _, hm, h⟩
        rwa [returnTimeK_succ_of_eq A hm]
    rw [hset]
    refine Finset.measurableSet_biUnion _ fun m hm => ?_
    have hmi : m ≤ i := Nat.le_of_lt_succ (Finset.mem_range.1 hm)
    exact ((natFilt (X := X)).mono hmi _ (ih.measurableSet_eq_of_countable m)).inter
      (adapted_coord.isStoppingTime_hittingAfter hA i)

/-- `{τ_A < ∞}` is an event. -/
theorem measurableSet_firstReturn_ne_top {A : Set X} (hA : MeasurableSet A) :
    MeasurableSet {ω : ℕ → X | firstReturn A ω ≠ ⊤} :=
  measurableSet_ne_top (proposition_3_4_4 hA).1

/-- `{τ_A = n}` is an event. -/
theorem measurableSet_firstReturn_eq {A : Set X} (hA : MeasurableSet A) (n : ℕ) :
    MeasurableSet {ω : ℕ → X | firstReturn A ω = WithTop.some n} :=
  (natFilt (X := X)).le n _ ((proposition_3_4_4 hA).1.measurableSet_eq_of_countable n)

/-- `{τ_A ≥ n}` is an event. -/
theorem measurableSet_le_firstReturn {A : Set X} (hA : MeasurableSet A) (n : ℕ) :
    MeasurableSet {ω : ℕ → X | WithTop.some n ≤ firstReturn A ω} := by
  have : {ω : ℕ → X | WithTop.some n ≤ firstReturn A ω} =
      ⋂ j ∈ Finset.range n, {ω | 1 ≤ j → ω j ∈ Aᶜ} := by
    ext ω
    simp only [mem_ofPred_eq, le_firstReturn_iff, mem_iInter, Finset.mem_range, mem_compl_iff]
    exact ⟨fun h j hj h1 => h j h1 hj, fun h j h1 hj => h j hj h1⟩
  rw [this]
  refine Finset.measurableSet_biInter _ fun j _ => ?_
  by_cases hj : 1 ≤ j
  · have : {ω : ℕ → X | 1 ≤ j → ω j ∈ Aᶜ} = {ω | ω j ∈ Aᶜ} := by ext; simp [hj]
    rw [this]
    exact (measurable_pi_apply j : Measurable fun ω : ℕ → X => ω j) hA.compl
  · simp [hj]

/-- `η_A` is measurable. -/
theorem measurable_occTime {A : Set X} (hA : MeasurableSet A) :
    Measurable (occTime (X := X) A) :=
  Measurable.tsum fun _ => (measurable_one.indicator hA).comp (measurable_pi_apply _)

/-- `x ↦ L(x, A)` is measurable. -/
theorem measurable_hitProb (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) : Measurable (hitProb P A) :=
  Kernel.measurable_coe _ (measurableSet_firstReturn_ne_top hA)

/-! ### The potential kernel and occupation times -/

/-- (3.30), MT p. 64: `U(x, A) = Σ_{n ≥ 1} Pⁿ(x, A) = E_x[η_A]`. -/
theorem potKernel_eq_lintegral_occTime (P : Kernel X X) [IsMarkovKernel P] (x : X)
    {A : Set X} (hA : MeasurableSet A) :
    potKernel P x A = ∫⁻ ω, occTime A ω ∂pathKernel P x := by
  unfold occTime
  rw [potKernel_apply P x hA,
    lintegral_tsum (f := fun n (ω : ℕ → X) => A.indicator 1 (ω (n + 1))) fun n =>
      ((measurable_one.indicator hA).comp (measurable_pi_apply (n + 1))).aemeasurable]
  refine tsum_congr fun n => ?_
  have hm : MeasurableSet {ω : ℕ → X | ω (n + 1) ∈ A} := measurable_pi_apply (n + 1) hA
  rw [← pathKernel_coord_mem P x (n + 1) hA, ← lintegral_indicator_one hm]
  rfl

/-! ### First-step analysis and taboo probabilities -/

/-- **First-step analysis.** `P_x(Φ₁ ∈ C, θΦ ∈ B) = ∫_C P(x, dy) P_y(B)`. -/
theorem pathKernel_first_step (P : Kernel X X) [IsMarkovKernel P] (x : X) {C : Set X}
    (hC : MeasurableSet C) {B : Set (ℕ → X)} (hB : MeasurableSet B) :
    pathKernel P x ({ω | ω 1 ∈ C} ∩ shift 1 ⁻¹' B) = ∫⁻ y in C, pathKernel P y B ∂P x := by
  have := isMarkovKernel_pathKernel P
  have hG : MeasurableSet[natFilt 1] {ω : ℕ → X | ω 1 ∈ C} :=
    measurableSet_coord_natFilt le_rfl hC
  have hGm : MeasurableSet {ω : ℕ → X | ω 1 ∈ C} := measurable_pi_apply 1 hC
  have hi : Measurable (B.indicator (1 : (ℕ → X) → ℝ≥0∞)) := measurable_one.indicator hB
  have h := markov_lintegral P (Measure.dirac x) hG hi
  rw [pathMeasure_dirac] at h
  have hsh : MeasurableSet (shift 1 ⁻¹' B) := measurable_shift 1 hB
  have e1 : ∫⁻ ω in {ω : ℕ → X | ω 1 ∈ C}, B.indicator 1 (shift 1 ω) ∂pathKernel P x =
      pathKernel P x ({ω | ω 1 ∈ C} ∩ shift 1 ⁻¹' B) := by
    calc ∫⁻ ω in {ω : ℕ → X | ω 1 ∈ C}, B.indicator 1 (shift 1 ω) ∂pathKernel P x
        = ∫⁻ ω in {ω : ℕ → X | ω 1 ∈ C}, (shift 1 ⁻¹' B).indicator 1 ω ∂pathKernel P x := rfl
      _ = _ := by rw [lintegral_indicator_one hsh, Measure.restrict_apply hsh, inter_comm]
  simp_rw [lintegral_indicator_one hB] at h
  have hk : Measurable fun y => pathKernel P y B := Kernel.measurable_coe _ hB
  rw [← e1, h, ← lintegral_indicator hGm]
  have e2 : ({ω : ℕ → X | ω 1 ∈ C}.indicator fun ω => pathKernel P (ω 1) B) =
      fun ω => C.indicator (fun y => pathKernel P y B) (ω 1) := by
    ext ω; by_cases h : ω 1 ∈ C <;> simp [h]
  rw [e2, ← lintegral_map (hk.indicator hC) (measurable_pi_apply 1), pathKernel_map_coord,
    pow_one, lintegral_indicator hC]

/-- The taboo kernel `(P I_{Aᶜ})ⁿ P` (MT p. 66): move by `P`, killing the path whenever it is in
`A`, `n` times, then move once more by `P`. -/
noncomputable def tabooKernel (P : Kernel X X) {A : Set X} (hA : MeasurableSet A) (n : ℕ) :
    Kernel X X :=
  P ∘ₖ ((indKernel hA.compl ∘ₖ P) ^ n)

/-- `(P I_B)(x, ·) = P(x, ·)` restricted to `B`. -/
theorem comp_indKernel_eq_restrict (P : Kernel X X) {B : Set X} (hB : MeasurableSet B)
    (x : X) : (indKernel hB ∘ₖ P) x = (P x).restrict B := by
  ext C hC
  rw [comp_indKernel_apply P hB x hC, Measure.restrict_apply hC]

/-- `(P I_{Aᶜ})⁰ P = P`. -/
theorem tabooKernel_zero (P : Kernel X X) {A : Set X} (hA : MeasurableSet A) :
    tabooKernel P hA 0 = P := by
  rw [tabooKernel, pow_zero]
  exact Kernel.comp_id P

/-- (3.33), operator form: `[(P I_{Aᶜ})ⁿ⁺¹ P](x, B) = ∫_{Aᶜ} P(x, dy) [(P I_{Aᶜ})ⁿ P](y, B)`. -/
theorem tabooKernel_succ_apply (P : Kernel X X) {A : Set X} (hA : MeasurableSet A) (n : ℕ)
    (x : X) {B : Set X} (hB : MeasurableSet B) :
    tabooKernel P hA (n + 1) x B = ∫⁻ y in Aᶜ, tabooKernel P hA n y B ∂P x := by
  rw [tabooKernel, pow_succ]
  change (P ∘ₖ (((indKernel hA.compl ∘ₖ P) ^ n) ∘ₖ (indKernel hA.compl ∘ₖ P))) x B = _
  rw [← Kernel.comp_assoc, Kernel.comp_apply' _ _ _ hB, comp_indKernel_eq_restrict]
  rfl

/-- The taboo probabilities `_APⁿ(x, B) = P_x(Φₙ ∈ B, τ_A ≥ n)` (MT p. 67). -/
noncomputable def tabooProb (P : Kernel X X) [IsMarkovKernel P] (A : Set X) (n : ℕ) (x : X)
    (B : Set X) : ℝ≥0∞ :=
  pathKernel P x ({ω | ω n ∈ B} ∩ {ω | WithTop.some n ≤ firstReturn A ω})

/-- `_AP¹(x, B) = P(x, B)` (MT p. 67). -/
theorem tabooProb_one (P : Kernel X X) [IsMarkovKernel P] (A : Set X) (x : X) {B : Set X}
    (hB : MeasurableSet B) : tabooProb P A 1 x B = P x B := by
  have : {ω : ℕ → X | WithTop.some 1 ≤ firstReturn A ω} = univ :=
    eq_univ_of_forall fun ω => one_le_firstReturn A ω
  rw [tabooProb, this, inter_univ, pathKernel_coord_mem P x 1 hB, pow_one]

/-- (3.33), MT p. 67: `_APⁿ⁺¹(x, B) = ∫_{Aᶜ} P(x, dy) _APⁿ(y, B)` for `n ≥ 1`. -/
theorem tabooProb_succ (P : Kernel X X) [IsMarkovKernel P] {A : Set X} (hA : MeasurableSet A)
    (n : ℕ) (x : X) {B : Set X} (hB : MeasurableSet B) :
    tabooProb P A (n + 2) x B = ∫⁻ y in Aᶜ, tabooProb P A (n + 1) y B ∂P x := by
  have hset : {ω : ℕ → X | ω (n + 2) ∈ B} ∩ {ω | WithTop.some (n + 2) ≤ firstReturn A ω} =
      {ω | ω 1 ∈ Aᶜ} ∩ shift 1 ⁻¹' ({ω | ω (n + 1) ∈ B} ∩
        {ω | WithTop.some (n + 1) ≤ firstReturn A ω}) := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, shift_apply,
      le_firstReturn_succ_iff A ω n]
    rw [show 1 + (n + 1) = n + 2 by omega]
    tauto
  rw [tabooProb, hset, pathKernel_first_step P x hA.compl
    (B := {ω | ω (n + 1) ∈ B} ∩ {ω | WithTop.some (n + 1) ≤ firstReturn A ω})
    ((measurable_pi_apply (n + 1) hB).inter (measurableSet_le_firstReturn hA (n + 1)))]
  rfl

/-- The operator form of the taboo probabilities (MT p. 67):
`_APⁿ⁺¹(x, B) = [(P I_{Aᶜ})ⁿ P](x, B)`. -/
theorem tabooProb_eq_tabooKernel (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (n : ℕ) (x : X) {B : Set X} (hB : MeasurableSet B) :
    tabooProb P A (n + 1) x B = tabooKernel P hA n x B := by
  induction n generalizing x with
  | zero => rw [tabooProb_one P A x hB, tabooKernel_zero]
  | succ n ih =>
    rw [tabooProb_succ P hA n x hB, tabooKernel_succ_apply P hA n x hB]
    exact setLIntegral_congr_fun hA.compl fun y _ => ih y

/-! ### Proposition 3.4.5 -/

/-- `{τ_A = n + 1} = {Φₙ₊₁ ∈ A, τ_A ≥ n + 1}`, so `P_x(τ_A = n + 1) = _APⁿ⁺¹(x, A)`. -/
theorem firstReturn_eq_tabooProb (P : Kernel X X) [IsMarkovKernel P] (A : Set X) (n : ℕ)
    (x : X) : pathKernel P x {ω | firstReturn A ω = WithTop.some (n + 1)} =
      tabooProb P A (n + 1) x A := by
  rw [tabooProb]
  congr 1
  ext ω
  simp only [mem_ofPred_eq, mem_inter_iff, firstReturn_eq_iff A ω n]
  tauto

/-- **Proposition 3.4.5 (i)**, first part (MT p. 65): `P_x(τ_A = 1) = P(x, A)`. -/
theorem proposition_3_4_5_i (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (x : X) :
    pathKernel P x {ω | firstReturn A ω = WithTop.some 1} = P x A := by
  rw [firstReturn_eq_tabooProb P A 0 x, tabooProb_one P A x hA]

/-- **Proposition 3.4.5 (i)**, recursion (MT p. 65):
`P_x(τ_A = n + 1) = ∫_{Aᶜ} P(x, dy) P_y(τ_A = n)` for `n ≥ 1`. -/
theorem proposition_3_4_5_i_succ (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (n : ℕ) (x : X) :
    pathKernel P x {ω | firstReturn A ω = WithTop.some (n + 2)} =
      ∫⁻ y in Aᶜ, pathKernel P y {ω | firstReturn A ω = WithTop.some (n + 1)} ∂P x := by
  rw [firstReturn_eq_tabooProb P A (n + 1) x, tabooProb_succ P hA n x hA]
  exact setLIntegral_congr_fun hA.compl fun y _ => (firstReturn_eq_tabooProb P A n y).symm

/-- The operator form of Proposition 3.4.5 (MT p. 66):
`P_x(τ_A = n + 1) = [(P I_{Aᶜ})ⁿ P](x, A)`. -/
theorem firstReturn_eq_tabooKernel (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (n : ℕ) (x : X) :
    pathKernel P x {ω | firstReturn A ω = WithTop.some (n + 1)} = tabooKernel P hA n x A := by
  rw [firstReturn_eq_tabooProb, tabooProb_eq_tabooKernel P hA n x hA]

/-- The iterated-integral form of Proposition 3.4.5 (i): `P_x(τ_A = n + 1)` is
`∫_{Aᶜ} P(x, dy₁) ∫_{Aᶜ} P(y₁, dy₂) ⋯ P(yₙ, A)`, the `n`-fold nested integral `nestedTaboo`. -/
noncomputable def nestedTaboo (P : Kernel X X) (A : Set X) : ℕ → X → ℝ≥0∞
  | 0 => fun x => P x A
  | n + 1 => fun x => ∫⁻ y in Aᶜ, nestedTaboo P A n y ∂P x

/-- `P_x(τ_A = n + 1)` equals the nested integral of Proposition 3.4.5 (i). -/
theorem firstReturn_eq_nestedTaboo (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (n : ℕ) (x : X) :
    pathKernel P x {ω | firstReturn A ω = WithTop.some (n + 1)} = nestedTaboo P A n x := by
  induction n generalizing x with
  | zero => exact proposition_3_4_5_i P hA x
  | succ n ih =>
    rw [proposition_3_4_5_i_succ P hA n x]
    exact setLIntegral_congr_fun hA.compl fun y _ => ih y

/-- **Proposition 3.4.5 (ii)** (MT p. 65): `P_x(σ_A = 0) = 1_A(x)`, and for `x ∉ A`, `n ≥ 1`,
`P_x(σ_A = n) = P_x(τ_A = n)`. -/
theorem proposition_3_4_5_ii (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (x : X) :
    pathKernel P x {ω | firstHit A ω = WithTop.some 0} = A.indicator 1 x ∧
      (x ∉ A → ∀ n, 1 ≤ n → pathKernel P x {ω | firstHit A ω = WithTop.some n} =
        pathKernel P x {ω | firstReturn A ω = WithTop.some n}) := by
  refine ⟨?_, fun hx n _ => ?_⟩
  · have : {ω : ℕ → X | firstHit A ω = WithTop.some 0} = {ω | ω 0 ∈ A} := by
      ext ω; exact firstHit_eq_zero_iff A ω
    rw [this, pathKernel_zero_mem P x hA]
  · have hnull : pathKernel P x {ω : ℕ → X | ω 0 ∈ Aᶜ}ᶜ = 0 := by
      have : {ω : ℕ → X | ω 0 ∈ Aᶜ}ᶜ = {ω | ω 0 ∈ A} := by ext ω; simp
      rw [this, pathKernel_zero_mem P x hA, indicator_of_notMem hx]
    rw [← measure_inter_conull (s := {ω | firstHit A ω = WithTop.some n}) hnull,
      ← measure_inter_conull (s := {ω | firstReturn A ω = WithTop.some n}) hnull]
    congr 1
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_compl_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by rwa [← firstHit_eq_firstReturn A h2], h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by rwa [firstHit_eq_firstReturn A h2], h2⟩

/-! ### The return probability `L` -/

/-- (MT p. 66): `L(x, A) = Σ_{k ≥ 1} P_x(τ_A = k) = Σ_{k ≥ 1} [(P I_{Aᶜ})^{k−1} P](x, A)`. -/
theorem hitProb_eq_tsum (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (x : X) :
    hitProb P A x = ∑' n, tabooKernel P hA n x A := by
  have hset : {ω : ℕ → X | firstReturn A ω ≠ ⊤} =
      ⋃ n : ℕ, {ω | firstReturn A ω = WithTop.some (n + 1)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h
      obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 h
      have h1 := one_le_firstReturn A ω
      rw [← hm] at h1
      have h1' := WithTop.coe_le_coe.1 h1
      exact ⟨m - 1, by rw [← hm, show m - 1 + 1 = m by omega]⟩
    · rintro ⟨n, h⟩; rw [h]; exact WithTop.coe_ne_top
  rw [hitProb, hset, measure_iUnion (fun i j hij => Set.disjoint_left.2 fun ω hi hj => hij
    (by have := hi.symm.trans hj; simpa using this))
    (fun n => measurableSet_firstReturn_eq hA (n + 1))]
  exact tsum_congr fun n => firstReturn_eq_tabooKernel P hA n x

/-- **First-step equation for `L`**: `L(x, A) = P(x, A) + ∫_{Aᶜ} P(x, dy) L(y, A)`. -/
theorem hitProb_first_step (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (x : X) :
    hitProb P A x = P x A + ∫⁻ y in Aᶜ, hitProb P A y ∂P x := by
  have hset : {ω : ℕ → X | firstReturn A ω ≠ ⊤} =
      {ω | ω 1 ∈ A} ∪ ({ω | ω 1 ∈ Aᶜ} ∩ shift 1 ⁻¹' {ω | firstReturn A ω ≠ ⊤}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_preimage, mem_compl_iff,
      firstReturn_ne_top_iff, shift_apply]
    constructor
    · rintro ⟨n, hn, h⟩
      by_cases h1 : ω 1 ∈ A
      · exact Or.inl h1
      · refine Or.inr ⟨h1, n - 1, ?_, ?_⟩
        · by_contra h0
          exact h1 (by rwa [show n = 1 by omega] at h)
        · rwa [show 1 + (n - 1) = n by omega]
    · rintro (h | ⟨_, n, hn, h⟩)
      · exact ⟨1, le_rfl, h⟩
      · exact ⟨1 + n, by omega, h⟩
  have hdisj : Disjoint {ω : ℕ → X | ω 1 ∈ A}
      ({ω | ω 1 ∈ Aᶜ} ∩ shift 1 ⁻¹' {ω | firstReturn A ω ≠ ⊤}) :=
    Set.disjoint_left.2 fun ω h1 h2 => h2.1 h1
  rw [hitProb, hset, measure_union hdisj ((measurable_pi_apply 1 hA.compl).inter
      (measurable_shift 1 (measurableSet_firstReturn_ne_top hA))),
    pathKernel_first_step P x hA.compl (measurableSet_firstReturn_ne_top hA),
    pathKernel_coord_mem P x 1 hA, pow_one]
  rfl

/-- The taboo potential kernel `U_A = Σ_{n ≥ 1} _APⁿ` (3.34), MT p. 67. -/
noncomputable def tabooPotKernel (P : Kernel X X) {A : Set X} (hA : MeasurableSet A) :
    Kernel X X :=
  Kernel.sum fun n => tabooKernel P hA n

/-- (3.34): `U_A(x, B) = Σ_{n ≥ 1} _APⁿ(x, B)`. -/
theorem tabooPotKernel_apply (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (x : X) {B : Set X} (hB : MeasurableSet B) :
    tabooPotKernel P hA x B = ∑' n, tabooProb P A (n + 1) x B := by
  rw [tabooPotKernel, Kernel.sum_apply' _ _ hB]
  exact tsum_congr fun n => (tabooProb_eq_tabooKernel P hA n x hB).symm

/-- MT p. 67: `U_A(x, A) = L(x, A)`. -/
theorem tabooPotKernel_self (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (x : X) : tabooPotKernel P hA x A = hitProb P A x := by
  rw [tabooPotKernel, Kernel.sum_apply' _ _ hA, hitProb_eq_tsum P hA x]

end MeynTweedie.NonlinearStateSpace
