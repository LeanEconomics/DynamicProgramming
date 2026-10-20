/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MeasureIntegration.SigmaAlgebras

/-!
# Measures

SLP §7.2, pp. 170–173. The book's measure (`IsMeasure`) is a countably additive set function on
a σ-algebra with values in `[0, +∞]`; on the measurable sets of a `MeasurableSpace` these are
exactly Mathlib's `Measure`s (`isMeasure_iff`). Finite additivity (`IsMeasure.union`), Exercise
7.4 (`ex_7_4a`, `ex_7_4b`), Exercise 7.5 (`ex_7_5`), Theorem 7.1 with the book's proofs
(`theorem_7_1a`, `theorem_7_1b`), almost everywhere (`ae_iff_book`), and the discrete
probability measures of the introduction (`discrete_isMeasure`).
-/

namespace StokeyLucasPrescott.MeasureIntegration

open Set MeasureTheory Filter Topology Function
open scoped ENNReal

variable {S : Type*}

theorem IsSigmaAlgebra.union_mem {𝒮 : Set (Set S)} (h : IsSigmaAlgebra 𝒮) {A B : Set S}
    (hA : A ∈ 𝒮) (hB : B ∈ 𝒮) : A ∪ B ∈ 𝒮 := by
  have := h.iUnion_mem (fun n => if n = 0 then A else B) fun n => by split_ifs <;> assumption
  convert this using 1
  ext x
  simp only [mem_union, mem_iUnion]
  constructor
  · rintro (hx | hx)
    · exact ⟨0, by simpa using hx⟩
    · exact ⟨1, by simpa using hx⟩
  · rintro ⟨n, hn⟩
    split_ifs at hn
    · exact Or.inl hn
    · exact Or.inr hn

theorem IsSigmaAlgebra.inter_mem {𝒮 : Set (Set S)} (h : IsSigmaAlgebra 𝒮) {A B : Set S}
    (hA : A ∈ 𝒮) (hB : B ∈ 𝒮) : A ∩ B ∈ 𝒮 := by
  have := h.compl_mem _ (h.union_mem (h.compl_mem _ hA) (h.compl_mem _ hB))
  rwa [compl_union, compl_compl, compl_compl] at this

theorem IsSigmaAlgebra.diff_mem {𝒮 : Set (Set S)} (h : IsSigmaAlgebra 𝒮) {A B : Set S}
    (hA : A ∈ 𝒮) (hB : B ∈ 𝒮) : A \ B ∈ 𝒮 :=
  h.inter_mem hA (h.compl_mem _ hB)

/-- A **measure** on `(S, 𝒮)` (SLP p. 170): `μ(∅) = 0`, `μ ≥ 0` (built into the values
`[0, +∞]`), and countable additivity over disjoint sequences in `𝒮`. -/
structure IsMeasure (𝒮 : Set (Set S)) (μ : Set S → ℝ≥0∞) : Prop where
  empty : μ ∅ = 0
  iUnion : ∀ A : ℕ → Set S, (∀ n, A n ∈ 𝒮) → Pairwise (Disjoint on A) →
    μ (⋃ n, A n) = ∑' n, μ (A n)

/-- Mathlib's measures are measures in the book's sense. -/
theorem isMeasure_coe [MeasurableSpace S] (ν : Measure S) :
    IsMeasure {A | MeasurableSet A} ν :=
  ⟨measure_empty, fun _ hA hd => measure_iUnion hd hA⟩

/-- On the measurable sets of a `MeasurableSpace`, the book's measures are exactly Mathlib's
`Measure`s. -/
theorem isMeasure_iff [MeasurableSpace S] (μ : Set S → ℝ≥0∞) :
    IsMeasure {A | MeasurableSet A} μ ↔ ∃ ν : Measure S, ∀ A, MeasurableSet A → ν A = μ A := by
  constructor
  · intro h
    refine ⟨Measure.ofMeasurable (fun A _ => μ A) h.empty fun A hA hd => h.iUnion A hA hd,
      fun A hA => Measure.ofMeasurable_apply A hA⟩
  · rintro ⟨ν, hν⟩
    refine ⟨by rw [← hν _ MeasurableSet.empty, measure_empty], fun A hA hd => ?_⟩
    rw [← hν _ (MeasurableSet.iUnion hA), measure_iUnion hd hA]
    exact tsum_congr fun n => hν _ (hA n)

/-- A measure is finitely additive. -/
theorem IsMeasure.union {𝒮 : Set (Set S)} {μ : Set S → ℝ≥0∞} (h : IsMeasure 𝒮 μ)
    (h𝒮 : IsSigmaAlgebra 𝒮) {A B : Set S} (hA : A ∈ 𝒮) (hB : B ∈ 𝒮) (hAB : Disjoint A B) :
    μ (A ∪ B) = μ A + μ B := by
  let f : ℕ → Set S := fun n => if n = 0 then A else if n = 1 then B else ∅
  have hf : ∀ n, f n ∈ 𝒮 := fun n => by
    simp only [f]
    split_ifs
    exacts [hA, hB, h𝒮.empty_mem]
  have hd : Pairwise (Disjoint on f) := by
    intro m n hmn
    simp only [Function.onFun, f]
    split_ifs <;> first | omega | exact hAB | exact hAB.symm | simp
  have hU : (⋃ n, f n) = A ∪ B := by
    ext x
    simp only [mem_iUnion, mem_union, f]
    constructor
    · rintro ⟨n, hn⟩
      split_ifs at hn
      · exact Or.inl hn
      · exact Or.inr hn
      · exact hn.elim
    · rintro (hx | hx)
      · exact ⟨0, by simpa using hx⟩
      · exact ⟨1, by simpa using hx⟩
  rw [← hU, h.iUnion f hf hd, tsum_eq_sum (s := Finset.range 2)]
  · simp [f, Finset.sum_range_succ]
  · intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    simp [f, show n ≠ 0 by omega, show n ≠ 1 by omega, h.empty]

/-- **Exercise 7.4a.** The sum of two measures is a measure. -/
theorem ex_7_4a {𝒮 : Set (Set S)} {μ₁ μ₂ : Set S → ℝ≥0∞} (h₁ : IsMeasure 𝒮 μ₁)
    (h₂ : IsMeasure 𝒮 μ₂) : IsMeasure 𝒮 (fun A => μ₁ A + μ₂ A) :=
  ⟨by simp [h₁.empty, h₂.empty], fun A hA hd => by
    rw [h₁.iUnion A hA hd, h₂.iUnion A hA hd, ENNReal.tsum_add]⟩

/-- **Exercise 7.4b.** For `B ∈ 𝒮`, `A ↦ μ(A ∩ B)` is a measure. -/
theorem ex_7_4b {𝒮 : Set (Set S)} {μ : Set S → ℝ≥0∞} (h : IsMeasure 𝒮 μ)
    (h𝒮 : IsSigmaAlgebra 𝒮) {B : Set S} (hB : B ∈ 𝒮) : IsMeasure 𝒮 (fun A => μ (A ∩ B)) :=
  ⟨by simp [h.empty], fun A hA hd => by
    rw [iUnion_inter]
    exact h.iUnion _ (fun n => h𝒮.inter_mem (hA n) hB)
      fun m n hmn => (hd hmn).mono inter_subset_left inter_subset_left⟩

/-- **Exercise 7.5.** If `A ⊆ B` then `μ(A) ≤ μ(B)`, and if also `μ(A) < ∞` then
`μ(B \ A) = μ(B) − μ(A)`. -/
theorem ex_7_5 {𝒮 : Set (Set S)} {μ : Set S → ℝ≥0∞} (h : IsMeasure 𝒮 μ)
    (h𝒮 : IsSigmaAlgebra 𝒮) {A B : Set S} (hA : A ∈ 𝒮) (hB : B ∈ 𝒮) (hAB : A ⊆ B) :
    μ A ≤ μ B ∧ (μ A < ∞ → μ (B \ A) = μ B - μ A) := by
  have hsplit : μ B = μ A + μ (B \ A) := by
    rw [← h.union h𝒮 hA (h𝒮.diff_mem hB hA) disjoint_sdiff_right, union_sdiff_cancel hAB]
  refine ⟨hsplit ▸ le_self_add, fun hfin => ?_⟩
  rw [hsplit, ENNReal.add_sub_cancel_left hfin.ne]

/-- **Theorem 7.1a.** For an increasing sequence in `𝒮`, `μ(⋃ Aₙ) = limₙ μ(Aₙ)`. The book's
proof: `μ(⋃ Aₙ) = Σ μ(Aₙ \ Aₙ₋₁)`, whose partial sums are `μ(A_N)` by finite additivity (so no
case split on `μ(Aₙ) = ∞` is needed). -/
theorem theorem_7_1a {𝒮 : Set (Set S)} {μ : Set S → ℝ≥0∞} (h : IsMeasure 𝒮 μ)
    (h𝒮 : IsSigmaAlgebra 𝒮) {A : ℕ → Set S} (hA : ∀ n, A n ∈ 𝒮) (hmono : Monotone A) :
    Tendsto (fun n => μ (A n)) atTop (𝓝 (μ (⋃ n, A n))) := by
  have hD : ∀ n, disjointed A n ∈ 𝒮 := by
    intro n
    cases n with
    | zero => rw [disjointed_zero]; exact hA 0
    | succ n => rw [hmono.disjointed_add_one]; exact h𝒮.diff_mem (hA _) (hA _)
  have hsum : ∀ N, ∑ n ∈ Finset.range (N + 1), μ (disjointed A n) = μ (A N) := by
    intro N
    induction N with
    | zero => simp [disjointed_zero]
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, hmono.disjointed_add_one,
        ← h.union h𝒮 (hA N) (h𝒮.diff_mem (hA _) (hA _)) disjoint_sdiff_right,
        union_sdiff_cancel (hmono (Nat.le_succ N) : A N ⊆ A (N + 1))]
  rw [← iUnion_disjointed, h.iUnion _ hD (disjoint_disjointed A)]
  have := (ENNReal.tendsto_nat_tsum fun n => μ (disjointed A n)).comp
    (tendsto_add_atTop_nat 1)
  refine this.congr fun N => ?_
  simp only [Function.comp_apply]
  exact hsum N

/-- **Theorem 7.1b.** For a decreasing sequence in `𝒮` with `μ(B_m) < ∞` for some `m`,
`μ(⋂ Bₙ) = limₙ μ(Bₙ)`. The book's proof: apply (a) to `B_m \ B_{m+n}`. -/
theorem theorem_7_1b {𝒮 : Set (Set S)} {μ : Set S → ℝ≥0∞} (h : IsMeasure 𝒮 μ)
    (h𝒮 : IsSigmaAlgebra 𝒮) {B : ℕ → Set S} (hB : ∀ n, B n ∈ 𝒮) (hanti : Antitone B) {m : ℕ}
    (hm : μ (B m) < ∞) : Tendsto (fun n => μ (B n)) atTop (𝓝 (μ (⋂ n, B n))) := by
  set C : ℕ → Set S := fun n => B m \ B (m + n)
  have hC : ∀ n, C n ∈ 𝒮 := fun n => h𝒮.diff_mem (hB m) (hB _)
  have hCmono : Monotone C := fun i j hij => sdiff_subset_sdiff_right (hanti (by omega))
  have hCU : (⋃ n, C n) = B m \ ⋂ n, B n := by
    ext x
    simp only [C, mem_iUnion, Set.mem_sdiff, mem_iInter, not_forall]
    constructor
    · rintro ⟨n, hx, hn⟩
      exact ⟨hx, m + n, hn⟩
    · rintro ⟨hx, k, hk⟩
      exact ⟨k, hx, fun h' => hk (hanti (by omega) h')⟩
  have hI : (⋂ n, B n) ∈ 𝒮 := h𝒮.iInter_mem B hB
  have hIm : (⋂ n, B n) ⊆ B m := iInter_subset B m
  have h1 := theorem_7_1a h h𝒮 hC hCmono
  rw [hCU, (ex_7_5 h h𝒮 hI (hB m) hIm).2 (((ex_7_5 h h𝒮 hI (hB m) hIm).1).trans_lt hm)] at h1
  have hle : ∀ n, μ (B (m + n)) ≤ μ (B m) := fun n => (ex_7_5 h h𝒮 (hB _) (hB m)
    (hanti (by omega))).1
  have h2 : Tendsto (fun n => μ (B m) - μ (C n)) atTop
      (𝓝 (μ (B m) - (μ (B m) - μ (⋂ n, B n)))) :=
    ENNReal.Tendsto.sub tendsto_const_nhds h1 (Or.inl hm.ne)
  rw [ENNReal.sub_sub_cancel hm.ne (ex_7_5 h h𝒮 hI (hB m) hIm).1] at h2
  have h3 : ∀ n, μ (B m) - μ (C n) = μ (B (m + n)) := fun n => by
    rw [(ex_7_5 h h𝒮 (hB _) (hB m) (hanti (by omega))).2 ((hle n).trans_lt hm),
      ENNReal.sub_sub_cancel hm.ne (hle n)]
  simp only [h3] at h2
  exact (tendsto_add_atTop_iff_nat m).1 (by simpa only [add_comm] using h2)

/-- **Almost everywhere** (SLP p. 171): a proposition holds `μ`-a.e. iff it holds off a
measurable set of measure zero. -/
theorem ae_iff_book [MeasurableSpace S] (μ : Measure S) (P : S → Prop) :
    (∀ᵐ s ∂μ, P s) ↔ ∃ A, MeasurableSet A ∧ μ A = 0 ∧ ∀ s ∈ Aᶜ, P s := by
  constructor
  · intro h
    obtain ⟨A, hsub, hA, hA0⟩ := exists_measurable_superset_of_null (ae_iff.1 h)
    exact ⟨A, hA, hA0, fun s hs => by_contra fun hP => hs (hsub hP)⟩
  · rintro ⟨A, -, hA0, hP⟩
    exact measure_mono_null (fun s hs => by_contra fun hsA => hs (hP s hsA)) hA0

/-- The discrete measure `μ(A) = Σ_{s ∈ A} πₛ`. -/
noncomputable def discreteMeasure (π : S → ℝ≥0∞) (A : Set S) : ℝ≥0∞ := ∑' s, A.indicator π s

/-- **The discrete probability space** (SLP pp. 167 and 171): for weights `πₛ ≥ 0` with
`Σ πₛ = 1`, `μ(A) = Σ_{s ∈ A} πₛ` is a probability measure on the σ-algebra of all subsets. -/
theorem discrete_isMeasure (π : S → ℝ≥0∞) (hπ : ∑' s, π s = 1) :
    IsMeasure univ (discreteMeasure π) ∧ discreteMeasure π univ = 1 := by
  refine ⟨⟨by simp [discreteMeasure], fun A _ hd => ?_⟩, by simpa [discreteMeasure] using hπ⟩
  simp only [discreteMeasure]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun s => ?_
  by_cases hs : ∃ k, s ∈ A k
  · obtain ⟨k, hk⟩ := hs
    rw [indicator_of_mem (mem_iUnion.2 ⟨k, hk⟩), tsum_eq_single k, indicator_of_mem hk]
    intro n hn
    exact indicator_of_notMem (fun h' => (hd hn).ne_of_mem h' hk rfl) _
  · push Not at hs
    rw [indicator_of_notMem (by simpa using hs)]
    simp [indicator_of_notMem (hs _)]

end StokeyLucasPrescott.MeasureIntegration
