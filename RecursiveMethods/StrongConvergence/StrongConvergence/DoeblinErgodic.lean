/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StrongConvergence.Doeblin

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
