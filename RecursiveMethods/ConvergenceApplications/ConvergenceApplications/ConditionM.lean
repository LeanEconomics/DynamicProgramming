/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ConvergenceApplications.Doeblin
import ConvergenceApplications.TVConvergence

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

namespace StokeyLucasPrescott.ConvergenceApplications

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

end StokeyLucasPrescott.ConvergenceApplications
