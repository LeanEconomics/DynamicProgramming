/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.UniformTransience

/-!
# First-entrance and last-exit decompositions (MT §8.2.1)

Meyn and Tweedie, §8.2.1, pp. 177–179. `_APⁿ(x, B) = P_x(Φₙ ∈ B, τ_A ≥ n)` is `tabooProb`, and
as a measure in `B` it is `tabooKernel P hA (n − 1) x` (`HittingTimes`).

* `pathKernel_inter_shift`: the Markov property at a fixed time `n` under `P_x`, for an event
  `G ∈ 𝓕ₙ^Φ`: `P_x(G ∩ θ⁻ⁿS) = ∫_G P_{Φₙ}(S) dP_x`.
* `map_restrict_le_firstReturn`: the law of `Φₙ₊₁` on `{τ_A ≥ n + 1}` is `_APⁿ⁺¹(x, ·)`.
* **(8.18)**, the first-entrance decomposition (`firstEntrance_decomposition`, p. 178):
  `Pⁿ(x, B) = _APⁿ(x, B) + Σ_{j=1}^{n−1} ∫_A _APʲ(x, dw) Pⁿ⁻ʲ(w, B)`.
* **(8.19)**, the last-exit decomposition (`lastExit_decomposition`, p. 178):
  `Pⁿ(x, B) = _APⁿ(x, B) + Σ_{j=1}^{n−1} ∫_A Pʲ(x, dw) _APⁿ⁻ʲ(w, B)`.
* (8.25) and (8.26) at `z = 1` (`potKernel_firstEntrance`, `potKernel_lastExit`, p. 179):
  `U(x, B) = U_A(x, B) + ∫_A U_A(x, dw) U(w, B)` and `U(x, B) = U_A(x, B) + ∫_A U(x, dw) U_A(w, B)`.
* `potKernel_eq_zero_of_lastExit`: the form of (8.26) used for Proposition 8.1.4 and
  Theorem 8.3.6: if `U_A(x, B) = 0` and `∫_A U(x, dw) U_A(w, B) = 0`, then `U(x, B) = 0`.

**Corrections.** None. The generating functions `U^{(z)}`, `U_A^{(z)}` of (8.20)–(8.21) are a
device for summing (8.18)–(8.19); the identities are proved here directly at `z = 1`, where all
terms are nonnegative.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- **The Markov property at a fixed time** under `P_x`: for `G ∈ 𝓕ₙ^Φ` and an event `S`,
`P_x(G ∩ θ⁻ⁿS) = ∫_G P_{Φₙ}(S) dP_x`. -/
theorem pathKernel_inter_shift (P : Kernel X X) [IsMarkovKernel P] (x : X) {n : ℕ}
    {G : Set (ℕ → X)} (hG : MeasurableSet[natFilt n] G) {S : Set (ℕ → X)}
    (hS : MeasurableSet S) :
    pathKernel P x (G ∩ shift n ⁻¹' S) = ∫⁻ ω in G, pathKernel P (ω n) S ∂pathKernel P x := by
  have := isMarkovKernel_pathKernel P
  have hGm : MeasurableSet G := (natFilt (X := X)).le n _ hG
  have hi : Measurable (S.indicator (1 : (ℕ → X) → ℝ≥0∞)) := measurable_one.indicator hS
  have h := markov_lintegral P (Measure.dirac x) hG hi
  rw [pathMeasure_dirac] at h
  have hsh : MeasurableSet (shift n ⁻¹' S) := measurable_shift n hS
  simp_rw [lintegral_indicator_one hS] at h
  rw [← h]
  calc pathKernel P x (G ∩ shift n ⁻¹' S)
      = ∫⁻ ω in G, (shift n ⁻¹' S).indicator 1 ω ∂pathKernel P x := by
        rw [lintegral_indicator_one hsh, Measure.restrict_apply hsh, inter_comm]
    _ = _ := rfl

/-- The law of `Φₙ₊₁` on `{τ_A ≥ n + 1}` is `_APⁿ⁺¹(x, ·) = [(P I_{Aᶜ})ⁿ P](x, ·)`. -/
theorem map_restrict_le_firstReturn (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (n : ℕ) (x : X) :
    ((pathKernel P x).restrict {ω | WithTop.some (n + 1) ≤ firstReturn A ω}).map
      (fun ω => ω (n + 1)) = tabooKernel P hA n x := by
  ext B hB
  rw [Measure.map_apply (measurable_pi_apply (n + 1)) hB,
    Measure.restrict_apply (measurable_pi_apply (n + 1) hB),
    ← tabooProb_eq_tabooKernel P hA n x hB]
  rfl

/-- `∫_{τ_A ≥ n+1} f(Φₙ₊₁) dP_x = ∫ f d(_APⁿ⁺¹(x, ·))`. -/
theorem setLIntegral_le_firstReturn (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (n : ℕ) (x : X) {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω in {ω | WithTop.some (n + 1) ≤ firstReturn A ω}, f (ω (n + 1)) ∂pathKernel P x =
      ∫⁻ w, f w ∂tabooKernel P hA n x := by
  rw [← map_restrict_le_firstReturn P hA n x, lintegral_map hf (measurable_pi_apply (n + 1))]

/-- **(8.18), the first-entrance decomposition** (MT p. 178):
`Pⁿ⁺¹(x, B) = _APⁿ⁺¹(x, B) + Σ_{j=0}^{n−1} ∫_A _APʲ⁺¹(x, dw) Pⁿ⁻ʲ(w, B)`. -/
theorem firstEntrance_decomposition (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (n : ℕ) (x : X) {B : Set X} (hB : MeasurableSet B) :
    (P ^ (n + 1)) x B = tabooProb P A (n + 1) x B +
      ∑ j ∈ Finset.range n, ∫⁻ w in A, (P ^ (n - j)) w B ∂tabooKernel P hA j x := by
  have := isMarkovKernel_pathKernel P
  have hτ := (proposition_3_4_4 hA).1
  set E : ℕ → Set (ℕ → X) := fun j =>
    {ω | firstReturn A ω = WithTop.some (j + 1)} ∩ {ω | ω (n + 1) ∈ B} with hE
  have hEm : ∀ j, MeasurableSet (E j) := fun j =>
    (measurableSet_firstReturn_eq hA (j + 1)).inter (measurable_pi_apply (n + 1) hB)
  have hTm : MeasurableSet ({ω : ℕ → X | ω (n + 1) ∈ B} ∩
      {ω | WithTop.some (n + 1) ≤ firstReturn A ω}) :=
    (measurable_pi_apply (n + 1) hB).inter (measurableSet_le_firstReturn hA (n + 1))
  have hcover : {ω : ℕ → X | ω (n + 1) ∈ B} =
      ({ω | ω (n + 1) ∈ B} ∩ {ω | WithTop.some (n + 1) ≤ firstReturn A ω}) ∪
        ⋃ j ∈ Finset.range n, E j := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_iUnion, Finset.mem_range, hE,
      exists_prop]
    constructor
    · intro h
      by_cases hle : WithTop.some (n + 1) ≤ firstReturn A ω
      · exact Or.inl ⟨h, hle⟩
      · push Not at hle
        obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hle)
        rw [← hm] at hle
        have hm' := WithTop.coe_lt_coe.1 hle
        have h1 : 1 ≤ m := by
          have := one_le_firstReturn A ω
          rw [← hm] at this
          exact WithTop.coe_le_coe.1 this
        exact Or.inr ⟨m - 1, by omega, by rw [← hm, show m - 1 + 1 = m by omega], h⟩
    · rintro (⟨h, -⟩ | ⟨j, -, -, h⟩) <;> exact h
  have hdisj : Disjoint ({ω : ℕ → X | ω (n + 1) ∈ B} ∩
      {ω | WithTop.some (n + 1) ≤ firstReturn A ω}) (⋃ j ∈ Finset.range n, E j) := by
    rw [Set.disjoint_left]
    rintro ω ⟨-, hle⟩ hω
    simp only [mem_iUnion, Finset.mem_range, hE, mem_inter_iff, mem_ofPred_eq] at hω
    obtain ⟨j, hj, hτj, -⟩ := hω
    change WithTop.some (n + 1) ≤ firstReturn A ω at hle
    rw [hτj] at hle
    have := WithTop.coe_le_coe.1 hle
    omega
  have hpd : PairwiseDisjoint (↑(Finset.range n)) E := fun i _ j _ hij =>
    Set.disjoint_left.2 fun ω hi hj => hij (by
      have := hi.1.symm.trans hj.1
      exact Nat.succ_injective (WithTop.coe_inj.1 this))
  rw [← pathKernel_coord_mem P x (n + 1) hB, hcover, measure_union hdisj
    (Finset.measurableSet_biUnion _ fun j _ => hEm j), measure_biUnion_finset hpd
    fun j _ => hEm j]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j < n := Finset.mem_range.1 hj
  have hG : MeasurableSet[natFilt (j + 1)] {ω : ℕ → X | firstReturn A ω = WithTop.some (j + 1)} :=
    hτ.measurableSet_eq_of_countable (j + 1)
  have hS : MeasurableSet {ω : ℕ → X | ω (n - j) ∈ B} := measurable_pi_apply (n - j) hB
  have hEeq : E j = {ω | firstReturn A ω = WithTop.some (j + 1)} ∩
      shift (j + 1) ⁻¹' {ω | ω (n - j) ∈ B} := by
    ext ω
    simp only [hE, mem_inter_iff, mem_ofPred_eq, mem_preimage, shift_apply]
    rw [show j + 1 + (n - j) = n + 1 by omega]
  have hf : Measurable fun w => (P ^ (n - j)) w B := Kernel.measurable_coe _ hB
  rw [hEeq, pathKernel_inter_shift P x hG hS]
  simp_rw [pathKernel_coord_mem P _ (n - j) hB]
  have hset : {ω : ℕ → X | firstReturn A ω = WithTop.some (j + 1)} =
      {ω | WithTop.some (j + 1) ≤ firstReturn A ω} ∩ {ω | ω (j + 1) ∈ A} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, firstReturn_eq_iff A ω j]
  rw [hset, inter_comm, ← Measure.restrict_restrict (s := {ω : ℕ → X | ω (j + 1) ∈ A})
      (measurable_pi_apply (j + 1) hA),
    ← lintegral_indicator (s := {ω : ℕ → X | ω (j + 1) ∈ A}) (measurable_pi_apply (j + 1) hA)]
  have e : ({ω : ℕ → X | ω (j + 1) ∈ A}.indicator fun ω => (P ^ (n - j)) (ω (j + 1)) B) =
      fun ω => A.indicator (fun w => (P ^ (n - j)) w B) (ω (j + 1)) := by
    ext ω; by_cases h : ω (j + 1) ∈ A <;> simp [h]
  rw [e, setLIntegral_le_firstReturn P hA j x (hf.indicator hA), lintegral_indicator hA]

/-- **(8.19), the last-exit decomposition** (MT p. 178):
`Pⁿ⁺¹(x, B) = _APⁿ⁺¹(x, B) + Σ_{j=0}^{n−1} ∫_A Pʲ⁺¹(x, dw) _APⁿ⁻ʲ(w, B)`. -/
theorem lastExit_decomposition (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (n : ℕ) (x : X) {B : Set X} (hB : MeasurableSet B) :
    (P ^ (n + 1)) x B = tabooProb P A (n + 1) x B +
      ∑ j ∈ Finset.range n, ∫⁻ w in A, tabooProb P A (n - j) w B ∂(P ^ (j + 1)) x := by
  classical
  have := isMarkovKernel_pathKernel P
  set T : ℕ → Set (ℕ → X) := fun k => {ω | ω k ∈ B} ∩ {ω | WithTop.some k ≤ firstReturn A ω}
    with hT
  have hTm : ∀ k, MeasurableSet (T k) := fun k =>
    (measurable_pi_apply k hB).inter (measurableSet_le_firstReturn hA k)
  set E : ℕ → Set (ℕ → X) := fun j => {ω | ω (j + 1) ∈ A} ∩ shift (j + 1) ⁻¹' T (n - j)
    with hE
  have hEm : ∀ j, MeasurableSet (E j) := fun j =>
    (measurable_pi_apply (j + 1) hA).inter (measurable_shift (j + 1) (hTm (n - j)))
  -- pathwise description of the pieces
  have hTchar : ∀ ω : ℕ → X, ω ∈ T (n + 1) ↔ ω (n + 1) ∈ B ∧ ∀ t, 1 ≤ t → t ≤ n → ω t ∉ A :=
    fun ω => by
      simp only [hT, mem_inter_iff, mem_ofPred_eq, le_firstReturn_iff]
      exact and_congr_right fun _ => ⟨fun h t h1 h2 => h t h1 (by omega),
        fun h t h1 h2 => h t h1 (by omega)⟩
  have hEchar : ∀ j < n, ∀ ω : ℕ → X, ω ∈ E j ↔ ω (j + 1) ∈ A ∧ ω (n + 1) ∈ B ∧
      ∀ t, j + 2 ≤ t → t ≤ n → ω t ∉ A := fun j hj ω => by
    simp only [hE, hT, mem_inter_iff, mem_ofPred_eq, mem_preimage, shift_apply,
      le_firstReturn_iff]
    rw [show j + 1 + (n - j) = n + 1 by omega]
    refine and_congr_right fun _ => and_congr_right fun _ => ⟨fun h t h1 h2 => ?_,
      fun h i h1 h2 => h (j + 1 + i) (by omega) (by omega)⟩
    have := h (t - (j + 1)) (by omega) (by omega)
    rwa [show j + 1 + (t - (j + 1)) = t by omega] at this
  have hcover : {ω : ℕ → X | ω (n + 1) ∈ B} = T (n + 1) ∪ ⋃ j ∈ Finset.range n, E j := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_iUnion, Finset.mem_range, exists_prop]
    constructor
    · intro h
      by_cases hall : ∀ t, 1 ≤ t → t ≤ n → ω t ∉ A
      · exact Or.inl ((hTchar ω).2 ⟨h, hall⟩)
      · push Not at hall
        set F := (Finset.Icc 1 n).filter fun t => ω t ∈ A
        have hFne : F.Nonempty := by
          obtain ⟨t, h1, h2, h3⟩ := hall
          exact ⟨t, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨h1, h2⟩, h3⟩⟩
        set t₀ := F.max' hFne
        have ht₀ := Finset.mem_filter.1 (F.max'_mem hFne)
        have ht₀I := Finset.mem_Icc.1 ht₀.1
        refine Or.inr ⟨t₀ - 1, by omega, (hEchar (t₀ - 1) (by omega) ω).2 ⟨?_, h, ?_⟩⟩
        · rw [show t₀ - 1 + 1 = t₀ by omega]; exact ht₀.2
        · intro t h1 h2 htA
          have : t ≤ t₀ := F.le_max' t (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, h2⟩,
            htA⟩)
          omega
    · rintro (h | ⟨j, hj, h⟩)
      · exact ((hTchar ω).1 h).1
      · exact ((hEchar j hj ω).1 h).2.1
  have hdisj : Disjoint (T (n + 1)) (⋃ j ∈ Finset.range n, E j) := by
    rw [Set.disjoint_left]
    intro ω h1 h2
    simp only [mem_iUnion, Finset.mem_range, exists_prop] at h2
    obtain ⟨j, hj, h⟩ := h2
    exact ((hTchar ω).1 h1).2 (j + 1) (by omega) (by omega) ((hEchar j hj ω).1 h).1
  have hpd : PairwiseDisjoint (↑(Finset.range n)) E := by
    intro i hi j hj hij
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2
    have hi' := Finset.mem_range.1 hi
    have hj' := Finset.mem_range.1 hj
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact ((hEchar i hi' ω).1 h1).2.2 (j + 1) (by omega) (by omega) ((hEchar j hj' ω).1 h2).1
    · exact ((hEchar j hj' ω).1 h2).2.2 (i + 1) (by omega) (by omega) ((hEchar i hi' ω).1 h1).1
  rw [← pathKernel_coord_mem P x (n + 1) hB, hcover, measure_union hdisj
    (Finset.measurableSet_biUnion _ fun j _ => hEm j), measure_biUnion_finset hpd
    fun j _ => hEm j]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hE, pathKernel_coord_inter_shift P x (j + 1) hA (hTm (n - j))]
  rfl

/-- **(8.25) at `z = 1`**, the first-entrance decomposition of `U` (MT p. 179):
`U(x, B) = U_A(x, B) + ∫_A U_A(x, dw) U(w, B)`. -/
theorem potKernel_firstEntrance (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (x : X) {B : Set X} (hB : MeasurableSet B) :
    potKernel P x B = tabooPotKernel P hA x B +
      ∫⁻ w in A, potKernel P w B ∂tabooPotKernel P hA x := by
  have hU : ∀ w, potKernel P w B = ∑' m, (P ^ (m + 1)) w B := fun w => potKernel_apply P w hB
  rw [potKernel_apply P x hB, tabooPotKernel_apply P hA x hB]
  simp_rw [firstEntrance_decomposition P hA _ x hB]
  rw [ENNReal.tsum_add]
  congr 1
  have hint : ∫⁻ w in A, potKernel P w B ∂tabooPotKernel P hA x =
      ∑' j, ∑' m, ∫⁻ w in A, (P ^ (m + 1)) w B ∂tabooKernel P hA j x := by
    rw [tabooPotKernel, Kernel.sum_apply, Measure.restrict_sum _ hA, lintegral_sum_measure]
    refine tsum_congr fun j => ?_
    simp_rw [hU]
    exact lintegral_tsum fun m => (Kernel.measurable_coe _ hB).aemeasurable
  rw [hint, ← tsum_sum_antidiagonal (fun p => ∫⁻ w in A, (P ^ (p.2 + 1)) w B ∂tabooKernel P hA
    p.1 x), tsum_eq_zero_add' ENNReal.summable]
  simp only [Finset.range_zero, Finset.sum_empty, zero_add]
  refine tsum_congr fun n => ?_
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun j m => ∫⁻ w in A,
    (P ^ (m + 1)) w B ∂tabooKernel P hA j x)]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [show n + 1 - j = n - j + 1 by have := Finset.mem_range.1 hj; omega]

/-- **(8.26) at `z = 1`**, the last-exit decomposition of `U` (MT p. 179):
`U(x, B) = U_A(x, B) + ∫_A U(x, dw) U_A(w, B)`. -/
theorem potKernel_lastExit (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (x : X) {B : Set X} (hB : MeasurableSet B) :
    potKernel P x B = tabooPotKernel P hA x B +
      ∫⁻ w in A, tabooPotKernel P hA w B ∂potKernel P x := by
  have hUA : ∀ w, tabooPotKernel P hA w B = ∑' m, tabooProb P A (m + 1) w B := fun w =>
    tabooPotKernel_apply P hA w hB
  have hmeas : ∀ m, Measurable fun w => tabooProb P A (m + 1) w B := fun m => by
    simp_rw [tabooProb_eq_tabooKernel P hA m _ hB]
    exact Kernel.measurable_coe _ hB
  rw [potKernel_apply P x hB, tabooPotKernel_apply P hA x hB]
  simp_rw [lastExit_decomposition P hA _ x hB]
  rw [ENNReal.tsum_add]
  congr 1
  have hint : ∫⁻ w in A, tabooPotKernel P hA w B ∂potKernel P x =
      ∑' j, ∑' m, ∫⁻ w in A, tabooProb P A (m + 1) w B ∂(P ^ (j + 1)) x := by
    rw [potKernel, Kernel.sum_apply, Measure.restrict_sum _ hA, lintegral_sum_measure]
    refine tsum_congr fun j => ?_
    simp_rw [hUA]
    exact lintegral_tsum fun m => (hmeas m).aemeasurable
  rw [hint, ← tsum_sum_antidiagonal (fun p => ∫⁻ w in A, tabooProb P A (p.2 + 1) w B
    ∂(P ^ (p.1 + 1)) x), tsum_eq_zero_add' ENNReal.summable]
  simp only [Finset.range_zero, Finset.sum_empty, zero_add]
  refine tsum_congr fun n => ?_
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun j m => ∫⁻ w in A,
    tabooProb P A (m + 1) w B ∂(P ^ (j + 1)) x)]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [show n + 1 - j = n - j + 1 by have := Finset.mem_range.1 hj; omega]

/-- **The last-exit inequality in use** (Proposition 8.1.4, Theorem 8.3.6): if `U_A(x, B) = 0`
and `∫_A Pʲ(x, dw) U_A(w, B) = 0` for every `j ≥ 1` (for instance, when `U_A(w, B) = 0` for all
`w ∈ A` outside a set `N` with `Pʲ(x, N) = 0`), then `U(x, B) = 0`. -/
theorem potKernel_eq_zero_of_lastExit (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (x : X) {B : Set X} (hB : MeasurableSet B)
    (h0 : tabooPotKernel P hA x B = 0)
    (h1 : ∫⁻ w in A, tabooPotKernel P hA w B ∂potKernel P x = 0) : potKernel P x B = 0 := by
  rw [potKernel_lastExit P hA x hB, h0, h1, add_zero]

end MeynTweedie.LimitTheorems
