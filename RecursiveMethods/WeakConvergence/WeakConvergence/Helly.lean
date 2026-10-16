/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import WeakConvergence.DistributionConvergence

/-!
# Support, Helly's theorem and tightness (SLP §12.3, pp. 371–375)

* the **support** of a probability measure (p. 371): the intersection of two closed sets of measure
  one is closed of measure one ("(Why?)"), and on a second-countable space the smallest closed set
  of measure one exists (`exists_support`, by Lindelöf — the book's "extends to any family" needs
  separability);
* the general lemma behind every compactness argument of the chapter: a **tight** sequence of
  probability measures on a separable metric space has a weakly convergent subsequence
  (`exists_convWeak_subseq_of_tight`, through Prokhorov's theorem);
* **Theorem 12.9 (Helly)** and its **Corollary 1**, corrected: hypothesis (3), `Fₙ(a̲) = 0` and
  `Fₙ(b̄) = 1`, does not confine the measures to `[a̲, b̄]` when `l ≥ 2`
  (`theorem_12_9_false_hyp`: `δ_{(-n, 0)}` has no weakly convergent subsequence), and the
  conclusion `F(a̲) = 0` fails even for `l = 1` (`theorem_12_9_false_concl`: `δ_{1/(n+1)}`). The
  true statement takes the measures concentrated on `[a̲, b̄]` and concludes the same of the limit
  (`theorem_12_9_cor1`, `theorem_12_9`);
* **Exercise 12.6**: (a) holds for `l = 1` (`ex_12_6a`) and fails for `l = 2`
  (`ex_12_6a_false`); (b), (c) are tightness (`ex_12_6b`, `ex_12_6c`; closedness is not needed);
* **Corollary 2** (corrected): a monotone sequence of distribution functions of measures
  concentrated on `[a̲, b̄]` converges weakly (`theorem_12_9_cor2`).
-/

namespace StokeyLucasPrescott.WeakConvergence

open MeasureTheory Filter Topology Set BoundedContinuousFunction

/-! ### The support of a measure -/

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- `A` is the **support** of `μ` (SLP p. 371): the smallest closed set of measure one. -/
def IsSupport (μ : Measure X) (A : Set X) : Prop :=
  IsClosed A ∧ μ A = 1 ∧ ∀ B, IsClosed B → μ B = 1 → A ⊆ B

variable [OpensMeasurableSpace X]

/-- The "(Why?)" of p. 371: two closed sets of measure one meet in a closed set of measure one. -/
theorem support_inter (μ : Measure X) [IsProbabilityMeasure μ] {A B : Set X} (hA : IsClosed A)
    (hB : IsClosed B) (hμA : μ A = 1) (hμB : μ B = 1) : IsClosed (A ∩ B) ∧ μ (A ∩ B) = 1 := by
  refine ⟨hA.inter hB, (prob_compl_eq_zero_iff (hA.inter hB).measurableSet).1 ?_⟩
  rw [compl_inter]
  exact measure_union_null ((prob_compl_eq_zero_iff hA.measurableSet).2 hμA)
    ((prob_compl_eq_zero_iff hB.measurableSet).2 hμB)

/-- The support exists and is unique on a second-countable space (SLP p. 371–372; the extension
from two sets to an arbitrary family needs Lindelöf). -/
theorem exists_support [SecondCountableTopology X] (μ : Measure X) [IsProbabilityMeasure μ] :
    ∃! A, IsSupport μ A := by
  set C := {B : Set X | IsClosed B ∧ μ B = 1}
  have hcl : IsClosed (⋂₀ C) := isClosed_sInter fun B hB => hB.1
  have hnull : μ (⋂₀ C)ᶜ = 0 := by
    rw [compl_sInter]
    obtain ⟨T, hTc, hTsub, hTeq⟩ := TopologicalSpace.isOpen_sUnion_countable (compl '' C)
      (by rintro _ ⟨B, hB, rfl⟩; exact hB.1.isOpen_compl)
    rw [← hTeq]
    refine (measure_sUnion_null_iff hTc).2 fun U hU => ?_
    obtain ⟨B, hB, rfl⟩ := hTsub hU
    exact (prob_compl_eq_zero_iff hB.1.measurableSet).2 hB.2
  refine ⟨⋂₀ C, ⟨hcl, (prob_compl_eq_zero_iff hcl.measurableSet).1 hnull,
    fun B hB hμB => sInter_subset_of_mem ⟨hB, hμB⟩⟩, fun A hA => ?_⟩
  exact (hA.2.2 _ hcl ((prob_compl_eq_zero_iff hcl.measurableSet).1 hnull)).antisymm
    (sInter_subset_of_mem ⟨hA.1, hA.2.1⟩)

/-! ### Tightness and weakly convergent subsequences -/

/-- A **tight** sequence of probability measures on a separable metric space (for every `ε > 0` a
compact `K` with `λₙ(K) > 1 - ε` for all `n`) has a weakly convergent subsequence. This is the
form in which Helly's theorem is used throughout the chapter (Prokhorov's theorem). -/
theorem exists_convWeak_subseq_of_tight {S : Type*} [MetricSpace S]
    [TopologicalSpace.SeparableSpace S] [MeasurableSpace S] [BorelSpace S] (ls : ℕ → Measure S)
    [∀ n, IsProbabilityMeasure (ls n)]
    (htight : ∀ ε > 0, ∃ K, IsCompact K ∧ ∀ n, 1 - ε < (ls n).real K) :
    ∃ μ : Measure S, IsProbabilityMeasure μ ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvWeak (ls ∘ φ) μ := by
  let P : ℕ → ProbabilityMeasure S := fun n => ⟨ls n, inferInstance⟩
  have hT : IsTightMeasureSet {((μ : ProbabilityMeasure S) : Measure S) | μ ∈ range P} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    by_cases hεtop : ε = ⊤
    · exact ⟨∅, isCompact_empty, fun μ _ => hεtop ▸ le_top⟩
    obtain ⟨K, hK, hKn⟩ := htight ε.toReal (ENNReal.toReal_pos hε.ne' hεtop)
    refine ⟨K, hK, ?_⟩
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    have h1 : (ls n).real Kᶜ ≤ ε.toReal := by
      rw [probReal_compl_eq_one_sub hK.measurableSet]; linarith [hKn n]
    change (ls n) Kᶜ ≤ ε
    rw [← ofReal_measureReal (μ := ls n) (s := Kᶜ), ← ENNReal.ofReal_toReal hεtop]
    exact ENNReal.ofReal_le_ofReal h1
  obtain ⟨ν, -, φ, hφ, hlim⟩ := (isCompact_closure_of_isTightMeasureSet hT).tendsto_subseq
    (fun n => subset_closure ⟨n, rfl⟩)
  exact ⟨ν, inferInstance, φ, hφ, fun f =>
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim f⟩

/-! ### Helly's theorem -/

variable {l : ℕ}

/-- A weak limit of measures concentrated on a closed set is concentrated on it (Theorem 12.3b). -/
theorem measure_eq_one_of_convWeak {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    {ls : ℕ → Measure S} {μ : Measure S} [∀ n, IsProbabilityMeasure (ls n)]
    [IsProbabilityMeasure μ] (h : ConvWeak ls μ) {F : Set S} (hF : IsClosed F)
    (hls : ∀ n, ls n F = 1) : μ F = 1 := by
  have hlim := (theorem_12_3 ls μ).1.1 h F hF
  have h1 : 1 ≤ μ.real F := le_of_forall_pos_lt_add fun ε hε => by
    obtain ⟨n, hn⟩ := (hlim ε hε).exists
    have h1n : (ls n).real F = 1 := by rw [measureReal_def, hls n, ENNReal.toReal_one]
    change (ls n).real F < _ at hn
    linarith
  have : μ.real F = 1 := le_antisymm measureReal_le_one h1
  rw [← ofReal_measureReal, this, ENNReal.ofReal_one]

/-- **Corollary 1 to Theorem 12.9** (Helly, measure form), corrected: probability measures on
`ℝˡ` concentrated on `[a̲, b̄]` have a subsequence converging weakly to a probability measure
concentrated on `[a̲, b̄]`. -/
theorem theorem_12_9_cor1 {a b : Fin l → ℝ} (ls : ℕ → Measure (Fin l → ℝ))
    [∀ n, IsProbabilityMeasure (ls n)] (h : ∀ n, ls n (Icc a b) = 1) :
    ∃ μ : Measure (Fin l → ℝ), IsProbabilityMeasure μ ∧ μ (Icc a b) = 1 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvWeak (ls ∘ φ) μ := by
  obtain ⟨μ, hμ, φ, hφ, hconv⟩ := exists_convWeak_subseq_of_tight ls fun ε hε =>
    ⟨Icc a b, isCompact_Icc, fun n => by
      rw [measureReal_def, h n, ENNReal.toReal_one]; linarith⟩
  have : ∀ n, IsProbabilityMeasure ((ls ∘ φ) n) := fun n =>
    inferInstanceAs (IsProbabilityMeasure (ls (φ n)))
  exact ⟨μ, hμ, measure_eq_one_of_convWeak hconv isClosed_Icc fun n => h (φ n), φ, hφ, hconv⟩

/-- Concentration on `[a̲, b̄]` in terms of the distribution function: `F(x) = 0` whenever some
`xᵢ < a̲ᵢ`, and `F(b̄) = 1`. -/
theorem concentrated_iff {a b : Fin l → ℝ} (μ : Measure (Fin l → ℝ)) [IsProbabilityMeasure μ] :
    μ (Icc a b) = 1 ↔ (∀ x, (∃ i, x i < a i) → distFun μ x = 0) ∧ distFun μ b = 1 := by
  constructor
  · intro h
    have hc : μ (Icc a b)ᶜ = 0 := (prob_compl_eq_zero_iff measurableSet_Icc).2 h
    refine ⟨fun x ⟨i, hi⟩ => ?_, ?_⟩
    · have : μ (Iic x) = 0 := measure_mono_null (t := (Icc a b)ᶜ) (fun y hy hyab => by
        exact absurd ((hyab.1 i).trans (hy i)) (not_le.2 hi)) hc
      rw [distFun, measureReal_def, this, ENNReal.toReal_zero]
    · have : μ (Iic b) = 1 :=
        le_antisymm prob_le_one (h ▸ measure_mono fun y hy => hy.2)
      rw [distFun, measureReal_def, this, ENNReal.toReal_one]
  · rintro ⟨h0, h1⟩
    have hb : μ (Iic b)ᶜ = 0 := by
      have : μ.real (Iic b)ᶜ = 0 := by
        rw [probReal_compl_eq_one_sub measurableSet_Iic]; rw [distFun] at h1; linarith
      exact (measureReal_eq_zero_iff).1 this
    have hk : ∀ i (k : ℕ), μ (Iic (Function.update b i (a i - 1 / (k + 1)))) = 0 := fun i k => by
      have := h0 (Function.update b i (a i - 1 / (k + 1))) ⟨i, by
        simp only [Function.update_self]; linarith [Nat.one_div_pos_of_nat (α := ℝ) (n := k)]⟩
      exact (measureReal_eq_zero_iff).1 this
    refine (prob_compl_eq_zero_iff measurableSet_Icc).1 (measure_mono_null (t := (Iic b)ᶜ ∪
      ⋃ i, ⋃ k : ℕ, Iic (Function.update b i (a i - 1 / (k + 1)))) ?_
      (measure_union_null hb (measure_iUnion_null fun i => measure_iUnion_null (hk i))))
    intro y hy
    by_cases hyb : y ≤ b
    · right
      obtain ⟨i, hi⟩ : ∃ i, y i < a i := by
        by_contra hne; push Not at hne; exact hy ⟨hne, hyb⟩
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hi)
      simp only [mem_iUnion]
      refine ⟨i, k, fun j => ?_⟩
      rcases eq_or_ne j i with rfl | hji
      · simp only [Function.update_self]; linarith
      · rw [Function.update_of_ne hji]; exact hyb j
    · exact Or.inl hyb

/-- **Theorem 12.9 (Helly)**, corrected: distribution functions vanishing whenever some
`xᵢ < a̲ᵢ` and equal to one at `b̄` have a subsequence converging weakly to a distribution
function with the same properties. -/
theorem theorem_12_9 {a b : Fin l → ℝ} (ls : ℕ → Measure (Fin l → ℝ))
    [∀ n, IsProbabilityMeasure (ls n)]
    (h0 : ∀ n x, (∃ i, x i < a i) → distFun (ls n) x = 0) (h1 : ∀ n, distFun (ls n) b = 1) :
    ∃ μ : Measure (Fin l → ℝ), IsProbabilityMeasure μ ∧
      (∀ x, (∃ i, x i < a i) → distFun μ x = 0) ∧ distFun μ b = 1 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvWeak (ls ∘ φ) μ := by
  obtain ⟨μ, hμ, hab, φ, hφ, hconv⟩ :=
    theorem_12_9_cor1 ls fun n => (concentrated_iff (ls n)).2 ⟨h0 n, h1 n⟩
  exact ⟨μ, hμ, ((concentrated_iff μ).1 hab).1, ((concentrated_iff μ).1 hab).2, φ, hφ, hconv⟩

/-- The distribution function of a unit mass. -/
theorem distFun_dirac (p x : Fin l → ℝ) :
    distFun (Measure.dirac p) x = if p ≤ x then 1 else 0 := by
  rw [distFun, measureReal_def, Measure.dirac_apply' p measurableSet_Iic]
  split_ifs with h
  · rw [indicator_of_mem (show p ∈ Iic x from h)]; simp
  · rw [indicator_of_notMem (show p ∉ Iic x from h)]; simp

/-- The sequence `δ_{(-n, 0)}` on `ℝ²` has no weakly convergent subsequence: its mass escapes
to `-∞` in the first coordinate. -/
theorem not_convWeak_escape (φ : ℕ → ℕ) (hφ : StrictMono φ) (μ : Measure (Fin 2 → ℝ))
    [IsProbabilityMeasure μ] :
    ¬ ConvWeak ((fun n : ℕ => Measure.dirac (![-(n : ℝ), 0] : Fin 2 → ℝ)) ∘ φ) μ := by
  intro hconv
  have : ∀ n, IsProbabilityMeasure
      (((fun n : ℕ => Measure.dirac (![-(n : ℝ), 0] : Fin 2 → ℝ)) ∘ φ) n) := fun n =>
    inferInstanceAs (IsProbabilityMeasure (Measure.dirac _))
  set G : ℕ → Set (Fin 2 → ℝ) := fun M => {y | -(M : ℝ) < y 0}
  have hG : ∀ M, IsOpen (G M) := fun M => isOpen_lt continuous_const (continuous_apply 0)
  have hnull : ∀ M, μ (G M) = 0 := fun M => by
    have hlim := (theorem_12_3 _ μ).2.1.1 hconv (G M) (hG M)
    have : μ.real (G M) ≤ 0 := le_of_forall_pos_lt_add fun ε hε => by
      obtain ⟨n, hn, hnM⟩ := ((hlim ε hε).and (eventually_ge_atTop M)).exists
      have hφn : M ≤ φ n := hnM.trans (hφ.id_le n)
      have : ((Measure.dirac (![-(φ n : ℝ), 0] : Fin 2 → ℝ))).real (G M) = 0 := by
        rw [measureReal_def, Measure.dirac_apply' _ (hG M).measurableSet,
          indicator_of_notMem (by simpa [G] using hφn)]; simp
      simp only [Function.comp_apply] at hn
      linarith
    exact (measureReal_eq_zero_iff).1 (le_antisymm this measureReal_nonneg)
  have hU : (⋃ M, G M) = univ := eq_univ_of_forall fun y => by
    obtain ⟨M, hM⟩ := exists_nat_gt (-(y 0))
    exact mem_iUnion.2 ⟨M, by simp only [G, mem_ofPred]; linarith⟩
  have := measure_iUnion_null hnull
  rw [hU, measure_univ] at this
  exact one_ne_zero this

/-- **Theorem 12.9 / Corollary 1 are false as printed (hypothesis).** On `ℝ²`, `δ_{(-n, 0)}`
satisfies (3) with `a̲ = (0, -1)`, `b̄ = (1, 1)` (`Fₙ(a̲) = 0`, `Fₙ(b̄) = 1`), but no
subsequence converges weakly. -/
theorem theorem_12_9_false_hyp :
    let ls := fun n : ℕ => Measure.dirac (![-(n : ℝ), 0] : Fin 2 → ℝ)
    (∀ n, distFun (ls n) ![0, -1] = 0 ∧ distFun (ls n) ![1, 1] = 1) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ μ : Measure (Fin 2 → ℝ), IsProbabilityMeasure μ →
        ¬ ConvWeak (ls ∘ φ) μ := by
  intro ls
  refine ⟨fun n => ⟨?_, ?_⟩, fun φ hφ μ _ => not_convWeak_escape φ hφ μ⟩
  · rw [distFun_dirac, ite_eq_right_iff]
    intro h; have := h 1; norm_num at this
  · rw [distFun_dirac, ite_eq_left_iff]
    intro h; exfalso; apply h
    intro i; fin_cases i <;> simp; linarith [n.cast_nonneg (α := ℝ)]

/-- **Theorem 12.9 / Corollary 1 are false as printed (conclusion).** On `ℝ`, `δ_{1/(n+1)}`
satisfies (3) with `a̲ = 0`, `b̄ = 1`, and does converge weakly, but every weak limit of every
subsequence has `F(a̲) = 1`, not `0`. -/
theorem theorem_12_9_false_concl :
    let ls := fun n : ℕ => Measure.dirac (fun _ => 1 / ((n : ℝ) + 1) : Fin 1 → ℝ)
    (∀ n, distFun (ls n) 0 = 0 ∧ distFun (ls n) 1 = 1) ∧ ConvWeak ls (Measure.dirac 0) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ μ : Measure (Fin 1 → ℝ), IsProbabilityMeasure μ →
        ConvWeak (ls ∘ φ) μ → distFun μ 0 = 1 := by
  intro ls
  have hconv : ConvWeak ls (Measure.dirac 0) := fun f => by
    simp only [ls, integral_dirac]
    exact (f.continuous.tendsto 0).comp (tendsto_pi_nhds.2 fun _ =>
      tendsto_one_div_add_atTop_nhds_zero_nat)
  refine ⟨fun n => ⟨?_, ?_⟩, hconv, fun φ hφ μ _ h => ?_⟩
  · rw [distFun_dirac, ite_eq_right_iff]
    intro h; have := h 0; simp only [Pi.zero_apply] at this
    linarith [Nat.one_div_pos_of_nat (α := ℝ) (n := n)]
  · rw [distFun_dirac, ite_eq_left_iff]
    intro h; exfalso; apply h
    intro i; simp only [Pi.one_apply]
    exact (div_le_one (by positivity)).2 (by linarith [n.cast_nonneg (α := ℝ)])
  · have : ∀ n, IsProbabilityMeasure ((ls ∘ φ) n) := fun n =>
      inferInstanceAs (IsProbabilityMeasure (Measure.dirac _))
    have : μ = Measure.dirac 0 :=
      convWeak_unique h fun f => (hconv f).comp hφ.tendsto_atTop
    rw [this, distFun_dirac, ite_eq_left_iff]
    exact fun h => absurd le_rfl h

/-! ### Exercise 12.6 -/

/-- **Exercise 12.6a** (`l = 1`). If for every `ε > 0` there are `a̲, b̄` with
`Fₙ(b̄) - Fₙ(a̲) > 1 - ε` for all `n`, some subsequence converges weakly. -/
theorem ex_12_6a (ls : ℕ → Measure (Fin 1 → ℝ)) [∀ n, IsProbabilityMeasure (ls n)]
    (h : ∀ ε > 0, ∃ a b : Fin 1 → ℝ, ∀ n, 1 - ε < distFun (ls n) b - distFun (ls n) a) :
    ∃ μ : Measure (Fin 1 → ℝ), IsProbabilityMeasure μ ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvWeak (ls ∘ φ) μ := by
  refine exists_convWeak_subseq_of_tight ls fun ε hε => ?_
  obtain ⟨a, b, hab⟩ := h ε hε
  refine ⟨Icc a b, isCompact_Icc, fun n => (hab n).trans_le ?_⟩
  have hsub : Iic b \ Iic a ⊆ Icc a b := fun y ⟨hyb, hya⟩ => by
    refine ⟨fun i => ?_, hyb⟩
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    by_contra hlt
    exact hya fun j => (Subsingleton.elim j 0 ▸ (not_le.1 hlt).le)
  exact (le_measureReal_sdiff).trans (measureReal_mono hsub)

/-- **Exercise 12.6a is false for `l ≥ 2`**: `δ_{(-n, 0)}` on `ℝ²` has `Fₙ(b̄) - Fₙ(a̲) = 1` for
`a̲ = (0, -1)`, `b̄ = (1, 1)`, yet no subsequence converges weakly. -/
theorem ex_12_6a_false :
    let ls := fun n : ℕ => Measure.dirac (![-(n : ℝ), 0] : Fin 2 → ℝ)
    (∀ ε > 0, ∃ a b : Fin 2 → ℝ, ∀ n, 1 - ε < distFun (ls n) b - distFun (ls n) a) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ μ : Measure (Fin 2 → ℝ), IsProbabilityMeasure μ →
        ¬ ConvWeak (ls ∘ φ) μ := by
  intro ls
  refine ⟨fun ε hε => ⟨![0, -1], ![1, 1], fun n => ?_⟩, theorem_12_9_false_hyp.2⟩
  rw [(theorem_12_9_false_hyp.1 n).1, (theorem_12_9_false_hyp.1 n).2]
  linarith

/-- **Exercise 12.6b.** A tight sequence of probability measures on `ℝˡ` has a weakly convergent
subsequence. -/
theorem ex_12_6b (ls : ℕ → Measure (Fin l → ℝ)) [∀ n, IsProbabilityMeasure (ls n)]
    (htight : ∀ ε > 0, ∃ K, IsCompact K ∧ ∀ n, 1 - ε < (ls n).real K) :
    ∃ μ : Measure (Fin l → ℝ), IsProbabilityMeasure μ ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvWeak (ls ∘ φ) μ :=
  exists_convWeak_subseq_of_tight ls htight

/-- **Exercise 12.6c.** The same on `S ⊆ ℝˡ` (the book assumes `S` closed; this is not needed). -/
theorem ex_12_6c {S : Set (Fin l → ℝ)} (ls : ℕ → Measure S) [∀ n, IsProbabilityMeasure (ls n)]
    (htight : ∀ ε > 0, ∃ K, IsCompact K ∧ ∀ n, 1 - ε < (ls n).real K) :
    ∃ μ : Measure S, IsProbabilityMeasure μ ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvWeak (ls ∘ φ) μ :=
  exists_convWeak_subseq_of_tight ls htight

/-! ### Corollary 2: monotone sequences -/

/-- **Corollary 2 to Theorem 12.9**, corrected: a monotone sequence of distribution functions
(`Fₙ₊₁ ≤ Fₙ` for all `n`, or `Fₙ₊₁ ≥ Fₙ` for all `n`) of measures concentrated on `[a̲, b̄]`
converges weakly to a probability measure concentrated on `[a̲, b̄]`. Proof: Helly gives a
subsequential limit `μ`; the whole sequence `Fₙ(x)` converges (bounded and monotone), so at
continuity points of `F_μ` its limit is `F_μ(x)`, and Theorem 12.8 applies. -/
theorem theorem_12_9_cor2 {a b : Fin l → ℝ} (ls : ℕ → Measure (Fin l → ℝ))
    [∀ n, IsProbabilityMeasure (ls n)] (h : ∀ n, ls n (Icc a b) = 1)
    (hmono : (∀ n, distFun (ls (n + 1)) ≤ distFun (ls n)) ∨
      (∀ n, distFun (ls n) ≤ distFun (ls (n + 1)))) :
    ∃ μ : Measure (Fin l → ℝ), IsProbabilityMeasure μ ∧ μ (Icc a b) = 1 ∧ ConvWeak ls μ := by
  obtain ⟨μ, hμ, hab, φ, hφ, hconv⟩ := theorem_12_9_cor1 ls h
  have : ∀ n, IsProbabilityMeasure ((ls ∘ φ) n) := fun n =>
    inferInstanceAs (IsProbabilityMeasure (ls (φ n)))
  have hconvx : ∀ x, ∃ c, Tendsto (fun n => distFun (ls n) x) atTop (𝓝 c) := fun x => by
    have hbdd : ∀ n, 0 ≤ distFun (ls n) x ∧ distFun (ls n) x ≤ 1 := fun n =>
      ⟨measureReal_nonneg, measureReal_le_one⟩
    rcases hmono with hm | hm
    · exact ⟨_, tendsto_atTop_ciInf (antitone_nat_of_succ_le fun n => hm n x)
        ⟨0, by rintro _ ⟨n, rfl⟩; exact (hbdd n).1⟩⟩
    · exact ⟨_, tendsto_atTop_ciSup (monotone_nat_of_le_succ fun n => hm n x)
        ⟨1, by rintro _ ⟨n, rfl⟩; exact (hbdd n).2⟩⟩
  refine ⟨μ, hμ, hab, (theorem_12_8 ls μ).2 fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := hconvx x
  have hsub := (theorem_12_8 (ls ∘ φ) μ).1 hconv x hx
  rwa [tendsto_nhds_unique (hc.comp hφ.tendsto_atTop) hsub] at hc

end StokeyLucasPrescott.WeakConvergence
