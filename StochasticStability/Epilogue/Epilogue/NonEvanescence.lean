/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.HarrisDecomposition
import Epilogue.TChains

/-!
# Non-evanescent and recurrent chains (MT §9.0, §9.2)

Meyn and Tweedie, Theorem 9.0.2 (p. 200) and §9.2, pp. 206–208. `X` is a locally compact,
second-countable Hausdorff space with its Borel σ-algebra.

**Definitions** (pp. 200, 206).
* `tendsToInfty`: the event `{Φ → ∞}` that the path visits every compact set only finitely
  often. `tendsToInfty_eq_iInter`: for a compact exhaustion `Kₙ`,
  `{Φ → ∞} = ⋂ₙ {Φ ∈ Kₙ i.o.}ᶜ`, so it is an event (`measurableSet_tendsToInfty`, p. 206); it is
  shift invariant (`isShiftInvariant_tendsToInfty`).
* `IsNonEvanescent P`: `P_x{Φ → ∞} = 0` for every `x` (p. 206).

**Tools.**
* `ioSet_union`, `ioSet_biUnion_range`: a path in a finite union infinitely often is in one of
  the sets infinitely often.
* `hitProb_le_tsum`, `hitSet_subset_iUnion`; `IsTransientSet.exists_cover_hitSet`: for a
  transient `A`, the set `Ā = {L(·, A) > 0}` is covered by countably many uniformly transient sets
  (Proposition 8.3.2).
* `sampledKernel_le_hitProbZero`: `K_a(x, B) ≤ P_x(σ_B < ∞)` (the corrected (5.45)).
* `pathKernel_tendsToInfty_eq_zero`: if `Q(y, K) = 1` for a compact `K`, then `P_y{Φ → ∞} = 0`.

**Results.**
* **Theorem 9.2.1** (`theorem_9_2_1`, p. 207): for a T-chain and a transient `A`,
  `P_x({Φ → ∞} ∪ {Φ ∈ A⁰ i.o.}) = 1`, where `A⁰ = {y : L(y, A) = 0}`; `theorem_9_2_1_enters` is
  the book's form with `{Φ enters A⁰}`, and `theorem_9_2_1_not_transient`: a non-evanescent
  T-chain does not have `X` transient.
* **Theorem 9.2.2** (`theorem_9_2_2`, p. 207): for a `ψ`-irreducible T-chain, `X = H ∪ N` with
  `H` empty or a maximal Harris set, `N` transient, and `L(x, H) = 1 − P_x{Φ → ∞}` (9.14);
  (i) `theorem_9_2_2_i`: the chain is recurrent iff `P_x{Φ → ∞} < 1` for some `x`;
  (ii) `theorem_9_2_2_ii`: it is Harris iff it is non-evanescent.
* **Theorem 9.0.2** (`theorem_9_0_2`, p. 200): the same as Theorem 9.2.2 (ii).

**Corrections.** The book's Theorem 9.2.1 uses `L(x, A⁰) ≥ K_a(x, A⁰)`, which needs `a(0) = 0`
(see `lemma_5_5_1_counterexample`); the proof here uses `P_x(σ_{A⁰} < ∞) ≥ K_a(x, A⁰)` and the
first-hitting form of Theorem 9.1.3 (`theorem_9_1_3_ae`).
-/

namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Infinitely many visits to finite unions -/

omit [MeasurableSpace X] in
/-- `{Φ ∈ A ∪ B i.o.} = {Φ ∈ A i.o.} ∪ {Φ ∈ B i.o.}`. -/
theorem ioSet_union (A B : Set X) : ioSet (A ∪ B) = ioSet A ∪ ioSet B := by
  refine Subset.antisymm (fun ω hω => ?_)
    (union_subset (ioSet_mono subset_union_left) (ioSet_mono subset_union_right))
  by_contra h
  simp only [mem_union, not_or, ioSet, mem_ofPred_eq, not_forall, not_exists, not_and] at h
  obtain ⟨⟨N₁, h₁⟩, ⟨N₂, h₂⟩⟩ := h
  obtain ⟨k, hk, hkAB⟩ := hω (max N₁ N₂)
  rcases hkAB with hA | hB
  · exact h₁ k (le_of_max_le_left hk) hA
  · exact h₂ k (le_of_max_le_right hk) hB

omit [MeasurableSpace X] in
/-- A path in `⋃_{i < n} Aᵢ` infinitely often is in some `Aᵢ` infinitely often. -/
theorem ioSet_biUnion_range (A : ℕ → Set X) (n : ℕ) :
    ioSet (⋃ i ∈ Finset.range n, A i) ⊆ ⋃ i ∈ Finset.range n, ioSet (A i) := by
  induction n with
  | zero =>
    intro ω hω
    obtain ⟨k, -, hk⟩ := hω 0
    simp at hk
  | succ n ih =>
    rw [Finset.range_add_one, Finset.set_biUnion_insert, Finset.set_biUnion_insert, ioSet_union]
    exact union_subset_union le_rfl ih

/-! ### Transient sets and their accessible sets -/

/-- `L(x, A) ≤ Σⱼ L(x, Bⱼ)` when `A ⊆ ⋃ⱼ Bⱼ`. -/
theorem hitProb_le_tsum (P : Kernel X X) [IsMarkovKernel P] {A : Set X} {B : ℕ → Set X}
    (hAB : A ⊆ ⋃ j, B j) (x : X) : hitProb P A x ≤ ∑' j, hitProb P (B j) x := by
  refine (measure_mono fun ω hω => ?_).trans (measure_iUnion_le _)
  simp only [mem_ofPred_eq, firstReturn_ne_top_iff, mem_iUnion] at hω ⊢
  obtain ⟨n, hn, hnA⟩ := hω
  obtain ⟨j, hj⟩ := mem_iUnion.1 (hAB hnA)
  exact ⟨j, n, hn, hj⟩

/-- `{L(·, A) > 0} ⊆ ⋃ⱼ {L(·, Bⱼ) > 0}` when `A ⊆ ⋃ⱼ Bⱼ`. -/
theorem hitSet_subset_iUnion (P : Kernel X X) [IsMarkovKernel P] {A : Set X} {B : ℕ → Set X}
    (hAB : A ⊆ ⋃ j, B j) : hitSet P A ⊆ ⋃ j, hitSet P (B j) := by
  intro x hx
  by_contra h
  simp only [mem_iUnion, not_exists, hitSet, mem_ofPred_eq, not_lt, nonpos_iff_eq_zero] at h
  have hle := hitProb_le_tsum P hAB x
  simp only [h, tsum_zero] at hle
  exact (lt_irrefl 0) (hx.trans_le hle)

/-- For a transient set `A`, the set `Ā = {L(·, A) > 0}` is covered by countably many uniformly
transient sets (Proposition 8.3.2, MT p. 207). -/
theorem IsTransientSet.exists_cover_hitSet {P : Kernel X X} [IsMarkovKernel P] {A : Set X}
    (hA : IsTransientSet P A) :
    ∃ D : ℕ → Set X, (∀ i, IsUniformlyTransient P (D i)) ∧ hitSet P A ⊆ ⋃ i, D i := by
  obtain ⟨B, hB, hAB⟩ := hA
  have hcov : ∀ j, IsTransientSet P (hitSet P (B j)) := fun j => proposition_8_3_2_cover P (hB j)
  choose E hE hEcov using hcov
  refine ⟨fun n => E (Nat.unpair n).1 (Nat.unpair n).2, fun n => hE _ _, fun x hx => ?_⟩
  obtain ⟨j, hj⟩ := mem_iUnion.1 (hitSet_subset_iUnion P hAB hx)
  obtain ⟨i, hi⟩ := mem_iUnion.1 (hEcov j hj)
  refine mem_iUnion.2 ⟨Nat.pair j i, ?_⟩
  simp only [Nat.unpair_pair]
  exact hi

/-- `P_x(σ_B < ∞) = P_x(Φₙ ∈ B for some n ≥ 0)`. -/
theorem hitProbZero_eq_exists (P : Kernel X X) [IsMarkovKernel P] (B : Set X) (x : X) :
    hitProbZero P B x = pathKernel P x {ω | ∃ n, ω n ∈ B} := by
  rw [hitProbZero]
  congr 1
  ext ω
  simp only [mem_ofPred_eq, firstHit, ne_eq, hittingAfter_eq_top_iff, not_forall, not_not,
    exists_prop, zero_le, true_and]

/-- The corrected (5.45): `K_a(x, B) ≤ P_x(σ_B < ∞)`. -/
theorem sampledKernel_le_hitProbZero (P : Kernel X X) [IsMarkovKernel P] {a : ℕ → ℝ≥0∞}
    (ha : IsSamplingDist a) {B : Set X} (hB : MeasurableSet B) (x : X) :
    sampledKernel P a x B ≤ hitProbZero P B x := by
  rw [hitProbZero_eq_exists]; exact lemma_5_5_1_firstHit P ha hB x

/-! ### The event `{Φ → ∞}` -/

variable [TopologicalSpace X] in
/-- The event `{Φ → ∞}` (MT p. 200): the path visits each compact set only finitely often. -/
def tendsToInfty : Set (ℕ → X) := {ω | ∀ K : Set X, IsCompact K → ω ∉ ioSet K}

omit [MeasurableSpace X] in
variable [TopologicalSpace X] in
/-- `{Φ → ∞}` is shift invariant. -/
theorem isShiftInvariant_tendsToInfty : IsShiftInvariant (tendsToInfty (X := X)) := by
  intro m ω
  simp only [tendsToInfty, mem_ofPred_eq, shift_mem_ioSet_iff]

omit [MeasurableSpace X] in
variable [TopologicalSpace X] in
/-- For a compact exhaustion `Kₙ`, `{Φ → ∞} = ⋂ₙ {Φ ∈ Kₙ i.o.}ᶜ` (MT p. 206). -/
theorem tendsToInfty_eq_iInter (K : CompactExhaustion X) :
    tendsToInfty (X := X) = ⋂ n, (ioSet (K n))ᶜ := by
  ext ω
  simp only [tendsToInfty, mem_ofPred_eq, mem_iInter, mem_compl_iff]
  constructor
  · exact fun h n => h (K n) (K.isCompact n)
  · intro h L hL hω
    obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hL
    exact h n (ioSet_mono hn hω)

variable [TopologicalSpace X] [T2Space X] [OpensMeasurableSpace X] [WeaklyLocallyCompactSpace X]
  [SigmaCompactSpace X] in
/-- `{Φ → ∞}` is an event (MT p. 206). -/
theorem measurableSet_tendsToInfty : MeasurableSet (tendsToInfty (X := X)) := by
  rw [tendsToInfty_eq_iInter (CompactExhaustion.choice X)]
  exact MeasurableSet.iInter fun n =>
    (measurableSet_ioSet ((CompactExhaustion.choice X).isCompact n).measurableSet).compl

variable [TopologicalSpace X] in
/-- The chain is **non-evanescent** (MT p. 206) if `P_x{Φ → ∞} = 0` for every `x`. -/
def IsNonEvanescent (P : Kernel X X) [IsMarkovKernel P] : Prop :=
  ∀ x, pathKernel P x tendsToInfty = 0

variable [TopologicalSpace X] in
/-- If `Q(y, K) = 1` for a compact `K`, then `P_y{Φ → ∞} = 0`. -/
theorem pathKernel_tendsToInfty_eq_zero (P : Kernel X X) [IsMarkovKernel P] {K : Set X}
    (hK : IsCompact K) (hKm : MeasurableSet K) {y : X} (hQ : harrisQ P K y = 1) :
    pathKernel P y tendsToInfty = 0 := by
  have := isMarkovKernel_pathKernel P
  have h0 : pathKernel P y (ioSet K)ᶜ = 0 := by
    rw [prob_compl_eq_zero_iff (measurableSet_ioSet hKm)]; exact hQ
  exact measure_mono_null (fun ω hω => hω K hK) h0

/-! ### Theorem 9.2.1 -/

variable [TopologicalSpace X] [T2Space X] [OpensMeasurableSpace X] [WeaklyLocallyCompactSpace X]
  [SigmaCompactSpace X] in
/-- **Theorem 9.2.1** (MT p. 207): for a T-chain and a transient set `A`, almost surely either
`Φ → ∞` or `Φ` is in `A⁰ = {y : L(y, A) = 0}` infinitely often:
`P_x({Φ → ∞} ∪ {Φ ∈ A⁰ i.o.}) = 1` for every `x`. -/
theorem theorem_9_2_1 {P : Kernel X X} [IsMarkovKernel P] (hT : IsTChain P) {A : Set X}
    (hAm : MeasurableSet A) (hA : IsTransientSet P A) (x : X) :
    pathKernel P x (tendsToInfty ∪ ioSet (noHitSet P A)) = 1 := by
  have := isMarkovKernel_pathKernel P
  obtain ⟨a, T, ha, ⟨-, hTle, hTlsc⟩, hTpos⟩ := hT
  obtain ⟨Ai, hAi, hcov⟩ := hA.exists_cover_hitSet
  set A0 := noHitSet P A
  have hA0 : MeasurableSet A0 := measurable_hitProb P hAm (measurableSet_singleton 0)
  -- the open sets `O i j = {T(·, Aᵢ) > (j+1)⁻¹}` and `O' j = {T(·, A⁰) > (j+1)⁻¹}`
  set O : ℕ → ℕ → Set X := fun i j => {y | ((j : ℝ≥0∞) + 1)⁻¹ < T y (Ai i)}
  set O' : ℕ → Set X := fun j => {y | ((j : ℝ≥0∞) + 1)⁻¹ < T y A0}
  have hOopen : ∀ i j, IsOpen (O i j) := fun i j =>
    (hTlsc _ (hAi i).1).isOpen_preimage _
  have hO'open : ∀ j, IsOpen (O' j) := fun j => (hTlsc _ hA0).isOpen_preimage _
  -- each `O i j` is uniformly transient
  have hOut : ∀ i j, IsUniformlyTransient P (O i j) := fun i j =>
    proposition_8_3_2 P (hAi i) (hOopen i j).measurableSet ha
      ⟨((j : ℝ≥0∞) + 1)⁻¹, by simp, fun y hy => hy.le.trans ((hTle y) _)⟩
  -- on `O' j`, `P_y(σ_{A⁰} < ∞) ≥ (j+1)⁻¹`
  have hO'hit : ∀ j, ∀ y ∈ O' j, ((j : ℝ≥0∞) + 1)⁻¹ ≤ hitProbZero P A0 y := fun j y hy =>
    hy.le.trans (((hTle y) A0).trans (sampledKernel_le_hitProbZero P ha hA0 y))
  -- the open sets `W M = O' M ∪ ⋃_{i ≤ M} O i M` increase to `X`
  set W : ℕ → Set X := fun M => O' M ∪ ⋃ i ∈ Finset.range (M + 1), O i M
  have hWopen : ∀ M, IsOpen (W M) := fun M =>
    (hO'open M).union (isOpen_biUnion fun i _ => hOopen i M)
  have hinv_anti : ∀ {j k : ℕ}, j ≤ k → ((k : ℝ≥0∞) + 1)⁻¹ ≤ ((j : ℝ≥0∞) + 1)⁻¹ :=
    fun hjk => ENNReal.inv_le_inv.2 (by gcongr)
  have hWmono : Monotone W := by
    intro M M' hMM' y hy
    rcases hy with hy | hy
    · exact Or.inl ((hinv_anti hMM').trans_lt hy)
    · simp only [mem_iUnion, Finset.mem_range] at hy
      obtain ⟨i, hi, hyi⟩ := hy
      refine Or.inr (mem_iUnion₂.2 ⟨i, Finset.mem_range.2 (by omega), ?_⟩)
      exact (hinv_anti hMM').trans_lt hyi
  have hWcov : ∀ y, ∃ M, y ∈ W M := by
    intro y
    have hpos := hTpos y
    have hsub : (univ : Set X) ⊆ A0 ∪ ⋃ i, Ai i := by
      intro z _
      by_cases hz : z ∈ A0
      · exact Or.inl hz
      · refine Or.inr (hcov ?_)
        exact pos_iff_ne_zero.2 hz
    have hle : T y univ ≤ T y A0 + ∑' i, T y (Ai i) := by
      calc T y univ ≤ T y (A0 ∪ ⋃ i, Ai i) := measure_mono hsub
        _ ≤ T y A0 + T y (⋃ i, Ai i) := measure_union_le _ _
        _ ≤ T y A0 + ∑' i, T y (Ai i) := by gcongr; exact measure_iUnion_le Ai
    by_cases h0 : T y A0 = 0
    · rw [h0, zero_add] at hle
      have : ∃ i, 0 < T y (Ai i) := by
        by_contra hc
        push Not at hc
        have : ∑' i, T y (Ai i) = 0 := by simp [fun i => le_antisymm (hc i) zero_le]
        exact (lt_irrefl 0) (hpos.trans_le (hle.trans_eq this))
      obtain ⟨i, hi⟩ := this
      obtain ⟨j, hj⟩ := ENNReal.exists_inv_nat_lt hi.ne'
      refine ⟨max i j, Or.inr (mem_iUnion₂.2 ⟨i, Finset.mem_range.2 (by omega), ?_⟩)⟩
      refine lt_of_le_of_lt ?_ hj
      exact ENNReal.inv_le_inv.2 (by norm_cast; omega)
    · obtain ⟨j, hj⟩ := ENNReal.exists_inv_nat_lt h0
      refine ⟨j, Or.inl (lt_of_le_of_lt ?_ hj)⟩
      exact ENNReal.inv_le_inv.2 (by simp)
  -- every compact set lies in some `W M`
  have hcompact : ∀ K : Set X, IsCompact K → ∃ M, K ⊆ W M := fun K hK =>
    hK.elim_directed_cover W hWopen (fun y _ => mem_iUnion.2 (hWcov y)) hWmono.directed_le
  -- for each compact `K`, `{Φ ∈ K i.o.} ⊆ {Φ ∈ A⁰ i.o.}` a.s.
  have hK : ∀ K : Set X, IsCompact K →
      ∀ᵐ ω ∂pathKernel P x, ω ∈ ioSet K → ω ∈ ioSet A0 := by
    intro K hKc
    obtain ⟨M, hKM⟩ := hcompact K hKc
    have h1 := theorem_9_1_3_ae P (Measure.dirac x) hA0 (by simp) (hO'hit M)
    rw [pathMeasure_dirac] at h1
    have h2 : ∀ i, ∀ᵐ ω ∂pathKernel P x, ω ∉ ioSet (O i M) := fun i => by
      obtain ⟨B, hB, hbd⟩ := (hOut i M).exists_bound
      have hQ0 := harrisQ_eq_zero_of_potKernel_ne_top P (hOopen i M).measurableSet
        (ne_top_of_le_ne_top hB (hbd x))
      exact measure_eq_zero_iff_ae_notMem.1 hQ0
    filter_upwards [h1, ae_all_iff.2 h2] with ω hω1 hω2 hωK
    have hW := ioSet_mono hKM hωK
    rw [ioSet_union] at hW
    rcases hW with hW | hW
    · exact hω1 hW
    · obtain ⟨i, -, hi⟩ := mem_iUnion₂.1 (ioSet_biUnion_range (fun i => O i M) (M + 1) hW)
      exact absurd hi (hω2 i)
  -- combine along a compact exhaustion
  set Kx := CompactExhaustion.choice X
  have hall : ∀ᵐ ω ∂pathKernel P x, ∀ n, ω ∈ ioSet (Kx n) → ω ∈ ioSet A0 :=
    ae_all_iff.2 fun n => hK (Kx n) (Kx.isCompact n)
  have hm : MeasurableSet (tendsToInfty ∪ ioSet A0) :=
    measurableSet_tendsToInfty.union (measurableSet_ioSet hA0)
  refine (prob_compl_eq_zero_iff hm).1 (measure_mono_null (fun ω hω => ?_) (ae_iff.1 hall))
  simp only [mem_compl_iff, mem_union, not_or] at hω
  obtain ⟨h1, h2⟩ := hω
  rw [tendsToInfty_eq_iInter Kx] at h1
  simp only [mem_iInter, mem_compl_iff, not_forall, not_not] at h1
  obtain ⟨n, hn⟩ := h1
  exact fun h => h2 (h n hn)

variable [TopologicalSpace X] [T2Space X] [OpensMeasurableSpace X] [WeaklyLocallyCompactSpace X]
  [SigmaCompactSpace X] in
/-- **Theorem 9.2.1**, the book's form (9.12): `P_x({Φ → ∞} ∪ {Φ enters A⁰}) = 1`. -/
theorem theorem_9_2_1_enters {P : Kernel X X} [IsMarkovKernel P] (hT : IsTChain P) {A : Set X}
    (hAm : MeasurableSet A) (hA : IsTransientSet P A) (x : X) :
    pathKernel P x (tendsToInfty ∪ {ω | ∃ n, ω n ∈ noHitSet P A}) = 1 := by
  have := isMarkovKernel_pathKernel P
  have hA0 : MeasurableSet (noHitSet P A) := measurable_hitProb P hAm (measurableSet_singleton 0)
  refine le_antisymm prob_le_one ((theorem_9_2_1 hT hAm hA x).symm.le.trans
    (measure_mono (union_subset_union le_rfl fun ω hω => ?_)))
  obtain ⟨k, -, hk⟩ := hω 0
  exact ⟨k, hk⟩

variable [TopologicalSpace X] [T2Space X] [OpensMeasurableSpace X] [WeaklyLocallyCompactSpace X]
  [SigmaCompactSpace X] in
/-- **Theorem 9.2.1**, last claim (MT p. 207): for a non-evanescent T-chain, `X` is not
transient. -/
theorem theorem_9_2_1_not_transient [Nonempty X] {P : Kernel X X} [IsMarkovKernel P]
    (hT : IsTChain P) (hne : IsNonEvanescent P) : ¬ IsTransientSet P univ := by
  intro htr
  have := isMarkovKernel_pathKernel P
  obtain ⟨x⟩ := ‹Nonempty X›
  have h := theorem_9_2_1 hT MeasurableSet.univ htr x
  have hempty : noHitSet P (univ : Set X) = ∅ := by
    ext y
    simp only [noHitSet, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    have : hitProb P univ y = 1 := by
      have h1 := le_hitProb_of_kernel P MeasurableSet.univ y
      rw [measure_univ] at h1
      exact le_antisymm (hitProb_le_one P univ y) h1
    rw [this]; exact one_ne_zero
  have hio : ioSet (∅ : Set X) = ∅ := by ext ω; simp [ioSet]
  rw [hempty, hio, union_empty, hne x] at h
  exact zero_ne_one h

/-! ### Theorem 9.2.2 -/

variable [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- A maximal irreducibility measure charges some compact set. -/
theorem exists_compact_pos {ψ : Measure X} (hψ : ψ ≠ 0) : ∃ K, IsCompact K ∧ 0 < ψ K := by
  set Kx := CompactExhaustion.choice X
  have : 0 < ψ (⋃ n, Kx n) := by
    rw [Kx.iUnion_eq]; exact pos_iff_ne_zero.2 fun h => hψ (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨n, hn⟩ := exists_measure_pos_of_iUnion this
  exact ⟨Kx n, Kx.isCompact n, hn⟩

variable [TopologicalSpace X] [T2Space X] [BorelSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] in
/-- (9.14) for a maximal Harris set `H` of a T-chain: `L(x, H) = 1 − P_x{Φ → ∞}`. -/
theorem hitProb_maximalHarris_eq {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : ψ ≠ 0) (hT : IsTChain P) {H : Set X} (hH : IsMaximalHarrisSet P ψ H)
    (hN : IsTransientSet P Hᶜ) (x : X) : hitProb P H x = 1 - pathKernel P x tendsToInfty := by
  have := isMarkovKernel_pathKernel P
  obtain ⟨hHm, -, habs, hmax, hQ⟩ := hH
  -- `Hᶜ⁰ = H`
  have hN0 : noHitSet P Hᶜ = H := by
    ext y
    constructor
    · intro hy
      by_contra hyH
      have h1 : P y Hᶜ = 0 := le_antisymm
        ((le_hitProb_of_kernel P hHm.compl y).trans_eq hy) zero_le
      have h2 : P y H = 1 := by
        rw [← prob_compl_eq_zero_iff hHm]; exact h1
      have : y ∈ harrisInfty P H := le_antisymm (hitProb_le_one P H y)
        (h2.symm.le.trans (le_hitProb_of_kernel P hHm y))
      rw [hmax] at this
      exact hyH this
    · intro hy
      exact habs.hitProb_compl hHm hy
  have h921 := theorem_9_2_1 hT hHm.compl hN x
  rw [hN0] at h921
  -- from `H`, `Φ → ∞` has probability zero
  obtain ⟨K, hK, hψK⟩ := exists_compact_pos hψ
  have hy0 : ∀ y ∈ H, pathKernel P y tendsToInfty = 0 := fun y hy =>
    pathKernel_tendsToInfty_eq_zero P hK hK.measurableSet (hQ K hK.measurableSet hψK y hy)
  have hTm : MeasurableSet (tendsToInfty (X := X)) := measurableSet_tendsToInfty
  have hτ := (proposition_3_4_4 (X := X) hHm).1
  have hFm := measurableSet_firstReturn_ne_top (X := X) hHm
  have hinter : pathKernel P x (tendsToInfty ∩ {ω | firstReturn H ω ≠ ⊤}) = 0 := by
    rw [pathKernel_inter_ne_top_of_shiftInvariant P x hτ hTm isShiftInvariant_tendsToInfty]
    exact (setLIntegral_congr_fun hFm fun ω hω => hy0 _
      (stoppedState_firstReturn_mem H hω)).trans (by simp)
  have hunion : pathKernel P x (tendsToInfty ∪ {ω | firstReturn H ω ≠ ⊤}) = 1 :=
    le_antisymm prob_le_one (h921.symm.le.trans (measure_mono
      (union_subset_union le_rfl (ioSet_subset_firstReturn H))))
  have hsum := measure_union_add_inter (μ := pathKernel P x) (tendsToInfty (X := X)) hFm
  rw [hunion, hinter, add_zero] at hsum
  have hfin : pathKernel P x tendsToInfty ≠ ∞ := measure_ne_top _ _
  rw [hitProb]
  exact ENNReal.eq_sub_of_add_eq hfin (by rw [add_comm]; exact hsum.symm)

variable [TopologicalSpace X] [T2Space X] [BorelSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] in
/-- In the transient case `P_x{Φ → ∞} = 1` for every `x`. -/
theorem pathKernel_tendsToInfty_of_transient {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hT : IsTChain P) (htr : IsTransientChain P ψ) (x : X) :
    pathKernel P x tendsToInfty = 1 := by
  have := isMarkovKernel_pathKernel P
  have h := theorem_9_2_1 hT MeasurableSet.univ htr.2 x
  have hempty : noHitSet P (univ : Set X) = ∅ := by
    ext y
    simp only [noHitSet, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    have : hitProb P univ y = 1 := by
      have h1 := le_hitProb_of_kernel P MeasurableSet.univ y
      rw [measure_univ] at h1
      exact le_antisymm (hitProb_le_one P univ y) h1
    rw [this]; exact one_ne_zero
  have hio : ioSet (∅ : Set X) = ∅ := by ext ω; simp [ioSet]
  rwa [hempty, hio, union_empty] at h

variable [TopologicalSpace X] [T2Space X] [BorelSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] in
/-- **Theorem 9.2.2**, decomposition (MT p. 207): for a `ψ`-irreducible T-chain, `X = H ∪ N` where
`H` is empty or a maximal Harris set, `N = Hᶜ` is transient, and
`L(x, H) = 1 − P_x{Φ → ∞}` for every `x` (9.14). -/
theorem theorem_9_2_2 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hT : IsTChain P) :
    ∃ H : Set X, (H = ∅ ∨ IsMaximalHarrisSet P ψ H) ∧ IsTransientSet P Hᶜ ∧
      ∀ x, hitProb P H x = 1 - pathKernel P x tendsToInfty := by
  rcases theorem_8_3_4 P hψ with hrec | htr
  · obtain ⟨H, hH, hN, -⟩ := theorem_9_1_5 hrec
    exact ⟨H, Or.inr hH, hN, hitProb_maximalHarris_eq hψ.1 hT hH hN⟩
  · refine ⟨∅, Or.inl rfl, by rw [compl_empty]; exact htr.2, fun x => ?_⟩
    rw [pathKernel_tendsToInfty_of_transient hT htr x, tsub_self]
    have := isMarkovKernel_pathKernel P
    have : hitProb P (∅ : Set X) x = 0 := by
      rw [hitProb]
      refine measure_mono_null (fun ω hω => ?_) measure_empty
      obtain ⟨n, -, hn⟩ := (firstReturn_ne_top_iff ∅ ω).1 hω
      exact hn
    exact this

variable [TopologicalSpace X] [T2Space X] [BorelSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] in
/-- **Theorem 9.2.2 (i)** (MT p. 207): a `ψ`-irreducible T-chain is recurrent iff
`P_x{Φ → ∞} < 1` for some `x`. -/
theorem theorem_9_2_2_i {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hT : IsTChain P) :
    IsRecurrentChain P ψ ↔ ∃ x, pathKernel P x tendsToInfty < 1 := by
  constructor
  · intro hrec
    obtain ⟨H, hH, hN, -⟩ := theorem_9_1_5 hrec
    obtain ⟨x, hx⟩ := hH.2.1
    have h := hitProb_maximalHarris_eq hψ.1 hT hH hN x
    have h1 : hitProb P H x = 1 := by
      have := hH.2.2.2.1
      rw [← this] at hx
      exact hx
    refine ⟨x, ?_⟩
    rw [h1] at h
    have hfin : pathKernel P x tendsToInfty ≤ 1 := by
      have := isMarkovKernel_pathKernel P; exact prob_le_one
    have : pathKernel P x tendsToInfty = 0 := by
      by_contra hne
      have : 1 - pathKernel P x tendsToInfty < 1 :=
        ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hne
      rw [← h] at this
      exact lt_irrefl _ this
    rw [this]; exact one_pos
  · rintro ⟨x, hx⟩
    rcases theorem_8_3_4 P hψ with hrec | htr
    · exact hrec
    · exact absurd (pathKernel_tendsToInfty_of_transient hT htr x) hx.ne

variable [TopologicalSpace X] [T2Space X] [BorelSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] in
/-- **Theorem 9.2.2 (ii)** (MT p. 207): a `ψ`-irreducible T-chain is Harris recurrent iff it is
non-evanescent. -/
theorem theorem_9_2_2_ii {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hT : IsTChain P) :
    IsHarris P ψ ↔ IsNonEvanescent P := by
  constructor
  · intro hH x
    obtain ⟨K, hK, hψK⟩ := exists_compact_pos hψ.1
    exact pathKernel_tendsToInfty_eq_zero P hK hK.measurableSet
      (theorem_9_1_4 hH hK.measurableSet hψK x)
  · intro hne
    have hX : Nonempty X := by
      by_contra h
      rw [not_nonempty_iff] at h
      exact hψ.1 (Measure.eq_zero_of_isEmpty ψ)
    obtain ⟨x₀⟩ := hX
    have hrec : IsRecurrentChain P ψ :=
      (theorem_9_2_2_i hψ hT).2 ⟨x₀, by rw [hne x₀]; exact one_pos⟩
    obtain ⟨H, hH, hN, -⟩ := theorem_9_1_5 hrec
    have hL : ∀ x, hitProb P H x = 1 := fun x => by
      rw [hitProb_maximalHarris_eq hψ.1 hT hH hN x, hne x, tsub_zero]
    obtain ⟨hHm, -, -, -, hQ⟩ := hH
    refine ⟨hψ, fun A hA hψA x _ => le_antisymm (harrisQ_le_one P A x) ?_⟩
    have hge := harrisQ_ge_stopping P hA x (proposition_3_4_4 hHm).1
    have hT' := measurableSet_firstReturn_ne_top (X := X) hHm
    calc (1 : ℝ≥0∞) = hitProb P H x := (hL x).symm
      _ = ∫⁻ _ in {ω | firstReturn H ω ≠ ⊤}, 1 ∂pathKernel P x := by
          rw [setLIntegral_const, one_mul]; rfl
      _ = ∫⁻ ω in {ω | firstReturn H ω ≠ ⊤}, harrisQ P A (stoppedState (firstReturn H) ω)
            ∂pathKernel P x :=
          setLIntegral_congr_fun hT' fun ω hω =>
            (hQ A hA hψA _ (stoppedState_firstReturn_mem H hω)).symm
      _ ≤ harrisQ P A x := hge

variable [TopologicalSpace X] [T2Space X] [BorelSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] in
/-- **Theorem 9.0.2** (MT p. 200): a `ψ`-irreducible T-chain is Harris recurrent iff
`P_x{Φ → ∞} = 0` for every `x`. -/
theorem theorem_9_0_2 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hT : IsTChain P) :
    IsHarris P ψ ↔ ∀ x, pathKernel P x tendsToInfty = 0 :=
  theorem_9_2_2_ii hψ hT

end MeynTweedie.Epilogue
