/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InvarianceTightness.Decompositions
import InvarianceTightness.PetiteSets

/-!
# The recurrence/transience dichotomy without splitting (MT §8.0, §8.3)

Meyn and Tweedie, Theorem 8.0.1 (p. 172) and §8.3, pp. 182–187. `ψ` is a maximal irreducibility
measure throughout.

* `lintegral_pow_potKernel_le`: `∫ Pᵐ(x, dw) U(w, A) ≤ U(x, A)`, the inequality (8.36).
* `IsTransientChain.not_isRecurrentChain`: a chain is not both recurrent and transient.
* **Theorem 8.3.4** (`theorem_8_3_4`, p. 185): a `ψ`-irreducible chain is recurrent or transient;
  the proof finds `A_r = {y ∈ A : U(y, A) ≤ r}` in `B⁺(X)` and covers `X` by the uniformly
  transient sets `A_r(M)`. `isRecurrentChain_or_isTransientChain`: exactly one of the two holds.
* **Theorem 8.3.5** (`theorem_8_3_5`, p. 186): if `X` is transient, every petite set is uniformly
  transient.
* **Theorem 8.0.1** (`theorem_8_0_1`, p. 172): a `ψ`-irreducible chain is recurrent (every set in
  `B⁺(X)` is recurrent), or transient with every petite set uniformly transient.
* `hitProb_mono`: `L(x, A) ≤ L(x, B)` for `A ⊆ B`.
* **Theorem 8.3.6** (p. 186): (i) `theorem_8_3_6_i`, a non-empty petite `C` with `L(x, C) ≡ 1` on
  `C` makes the chain recurrent, and `C ∈ B⁺(X)`; (ii) `theorem_8_3_6_ii`, the chain is transient
  iff there are `C, D ∈ B⁺(X)` with `L(x, C) < 1` for every `x ∈ D`.
* **Proposition 8.3.7** (`proposition_8_3_7`, p. 186): every `ψ`-null set is transient.
* **Proposition 8.3.8** (`proposition_8_3_8`, p. 187): on a countably generated space there is a
  `d`-cycle `D₀, …, D_{d−1}` whose exceptional set `N = (⋃ Dᵢ)ᶜ` is `ψ`-null and transient.

**Corrections.**
* Theorem 8.3.6 (i) needs `C ≠ ∅`: the empty set is petite and satisfies `L ≡ 1` on `C`
  vacuously, so as stated the theorem would make every `ψ`-irreducible chain recurrent. The
  counterexample, a transient chain, is `theorem_8_3_6_i_counterexample` in `RandomWalkIntegers`.
  The book's remark "we do not assume `C ∈ B⁺(X)`, but this follows" holds for non-empty `C`.
* Theorem 8.3.5 needs no irreducibility: if `X` is covered by uniformly transient sets, every
  petite set is uniformly transient, since its petite measure charges one of the covering sets.
* In the converse of Theorem 8.3.6 (ii) the book takes a petite `C ∈ B⁺(X)` (which needs the
  existence of small sets, Theorem 5.2.2); the proof here takes for `C` a uniformly transient set
  in `B⁺(X)`, which every transient chain has, and needs no countable generation.
-/

namespace MeynTweedie.InvarianceTightness

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- (8.36): `∫ Pᵐ(x, dw) U(w, A) = Σ_{n ≥ m+1} Pⁿ(x, A) ≤ U(x, A)`. -/
theorem lintegral_pow_potKernel_le (P : Kernel X X) (m : ℕ) (x : X) {A : Set X}
    (hA : MeasurableSet A) : ∫⁻ w, potKernel P w A ∂(P ^ m) x ≤ potKernel P x A := by
  simp_rw [potKernel_apply P _ hA]
  rw [lintegral_tsum fun n => (Kernel.measurable_coe _ hA).aemeasurable]
  calc ∑' n, ∫⁻ w, (P ^ (n + 1)) w A ∂(P ^ m) x = ∑' n, (P ^ ((n + m) + 1)) x A := by
        refine tsum_congr fun n => ?_
        rw [show n + m + 1 = m + (n + 1) by omega,
          Kernel.pow_add_apply_eq_lintegral P m (n + 1) x hA]
    _ ≤ ∑' n, (P ^ (n + 1)) x A :=
        ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective m) fun n => (P ^ (n + 1)) x A

/-- If `Pᵐ(x, A*) > 0` where `U(·, A) = ∞` on `A*`, then `U(x, A) = ∞` (8.36). -/
theorem potKernel_eq_top_of_pow_pos (P : Kernel X X) {m : ℕ} {x : X} {A S : Set X}
    (hA : MeasurableSet A) (hS : MeasurableSet S) (hSA : ∀ y ∈ S, potKernel P y A = ∞)
    (hpos : 0 < (P ^ m) x S) : potKernel P x A = ∞ := by
  refine top_le_iff.1 ((?_ : ∞ ≤ ∫⁻ w, potKernel P w A ∂(P ^ m) x).trans
    (lintegral_pow_potKernel_le P m x hA))
  calc ∞ = ∫⁻ _ in S, ∞ ∂(P ^ m) x := by rw [setLIntegral_const, ENNReal.top_mul hpos.ne']
    _ = ∫⁻ w in S, potKernel P w A ∂(P ^ m) x :=
        setLIntegral_congr_fun hS fun y hy => (hSA y hy).symm
    _ ≤ _ := setLIntegral_le_lintegral _ _

/-- A chain is not both recurrent and transient. -/
theorem IsTransientChain.not_isRecurrentChain {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} (h : IsTransientChain P ψ) : ¬ IsRecurrentChain P ψ := by
  rintro ⟨hψ, hrec⟩
  obtain ⟨B, hB, hcov⟩ := h.2
  have : ∃ n, 0 < ψ (B n) := by
    by_contra hc
    push Not at hc
    have h0 : ψ (⋃ n, B n) = 0 := measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (hc n)
    exact hψ.1 (Measure.measure_univ_eq_zero.1 (measure_mono_null hcov h0))
  obtain ⟨n, hn⟩ := this
  obtain ⟨y, hy⟩ := nonempty_of_measure_ne_zero hn.ne'
  obtain ⟨hBm, M, hM, hb⟩ := hB n
  exact hM (top_le_iff.1 (hrec (B n) hBm hn y ▸ hb y hy))

/-- **Theorem 8.3.4** (MT p. 185): a `ψ`-irreducible chain is either recurrent or transient. -/
theorem theorem_8_3_4 (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) : IsRecurrentChain P ψ ∨ IsTransientChain P ψ := by
  by_cases hrec : IsRecurrentChain P ψ
  · exact Or.inl hrec
  right
  refine ⟨hψ, ?_⟩
  have : ∃ A, MeasurableSet A ∧ 0 < ψ A ∧ ∃ x, potKernel P x A ≠ ∞ := by
    by_contra hc
    push Not at hc
    exact hrec ⟨hψ, fun A hA hpos x => hc A hA hpos x⟩
  obtain ⟨A, hA, hψA, xs, hxs⟩ := this
  set Astar := {y | potKernel P y A = ∞} with hAstar
  have hAsm : MeasurableSet Astar :=
    (Kernel.measurable_coe _ hA) (measurableSet_singleton ∞)
  -- `ψ(A*) = 0`
  have hAs0 : ψ Astar = 0 := by
    by_contra h0
    obtain ⟨n, hn⟩ := (hitProb_pos_iff P hAsm xs).1 (hψ.2.1 Astar hAsm (pos_iff_ne_zero.2 h0) xs)
    exact hxs (potKernel_eq_top_of_pow_pos P hA hAsm (fun y hy => hy) hn)
  -- some `A_r = {y ∈ A : U(y, A) ≤ r}` lies in `B⁺(X)`
  set Ar : ℕ → Set X := fun r => {y ∈ A | potKernel P y A ≤ r} with hAr
  have hArm : ∀ r, MeasurableSet (Ar r) := fun r =>
    hA.inter (measurableSet_le (Kernel.measurable_coe _ hA) measurable_const)
  have hcov : A \ Astar ⊆ ⋃ r, Ar r := fun y hy => by
    obtain ⟨r, hr⟩ := ENNReal.exists_nat_gt (show potKernel P y A ≠ ∞ from hy.2)
    exact mem_iUnion.2 ⟨r, hy.1, hr.le⟩
  have : ∃ r, 0 < ψ (Ar r) := by
    by_contra hc
    push Not at hc
    have h0 : ψ (⋃ r, Ar r) = 0 := measure_iUnion_null fun r => nonpos_iff_eq_zero.1 (hc r)
    have h1 : ψ (A \ Astar) = 0 := measure_mono_null hcov h0
    rw [measure_sdiff_null hAs0] at h1
    exact hψA.ne' h1
  obtain ⟨r, hr⟩ := this
  have hut : IsUniformlyTransient P (Ar r) :=
    ⟨hArm r, r, ENNReal.natCast_ne_top r, fun y hy =>
      (measure_mono (fun z hz => hz.1)).trans hy.2⟩
  exact isTransientSet_univ_of_uniformlyTransient P hψ.2.1 hut hr

/-- **The dichotomy, exclusive form**: a `ψ`-irreducible chain is recurrent or transient, and not
both. -/
theorem isRecurrentChain_or_isTransientChain (P : Kernel X X) [IsMarkovKernel P]
    {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) :
    (IsRecurrentChain P ψ ∨ IsTransientChain P ψ) ∧
      ¬ (IsRecurrentChain P ψ ∧ IsTransientChain P ψ) :=
  ⟨theorem_8_3_4 P hψ, fun h => h.2.not_isRecurrentChain h.1⟩

/-- **Theorem 8.3.5** (MT p. 186): if `X` is transient, every petite set is uniformly transient.
No irreducibility is needed. -/
theorem theorem_8_3_5 (P : Kernel X X) [IsMarkovKernel P] (hT : IsTransientSet P univ)
    {C : Set X} (hC : IsPetite P C) : IsUniformlyTransient P C := by
  obtain ⟨a, ν, hCm, ha, hν, hle⟩ := hC
  obtain ⟨B, hB, hcov⟩ := hT
  have : ∃ n, 0 < ν (B n) := by
    by_contra hc
    push Not at hc
    have h0 : ν (⋃ n, B n) = 0 := measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (hc n)
    exact hν (Measure.measure_univ_eq_zero.1 (measure_mono_null hcov h0))
  obtain ⟨n, hn⟩ := this
  exact proposition_8_3_2 P (hB n) hCm ha ⟨ν (B n), hn, fun x hx => hle x hx (B n)⟩

/-- **Theorem 8.0.1** (MT p. 172): a `ψ`-irreducible chain is either (i) recurrent: every set in
`B⁺(X)` is recurrent, indeed `U(x, A) = ∞` for every `x`; or (ii) transient: `X` has a countable
cover by uniformly transient sets, and every petite set is uniformly transient. -/
theorem theorem_8_0_1 (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) :
    (IsRecurrentChain P ψ ∧ ∀ A, MeasurableSet A → 0 < ψ A → IsRecurrentSet P A) ∨
      (IsTransientChain P ψ ∧ ∀ C, IsPetite P C → IsUniformlyTransient P C) := by
  rcases theorem_8_3_4 P hψ with h | h
  · exact Or.inl ⟨h, fun A hA hpos x _ => h.2 A hA hpos x⟩
  · exact Or.inr ⟨h, fun C hC => theorem_8_3_5 P h.2 hC⟩

/-- `L(x, A) ≤ L(x, B)` for `A ⊆ B`. -/
theorem hitProb_mono (P : Kernel X X) [IsMarkovKernel P] {A B : Set X} (hAB : A ⊆ B) (x : X) :
    hitProb P A x ≤ hitProb P B x := by
  refine measure_mono fun ω hω => ?_
  obtain ⟨n, hn, h⟩ := (firstReturn_ne_top_iff A ω).1 hω
  exact (firstReturn_ne_top_iff B ω).2 ⟨n, hn, hAB h⟩

/-- **Theorem 8.3.6 (i)** (MT p. 186): if a **non-empty** petite set `C` has `L(x, C) = 1` for
every `x ∈ C`, the chain is recurrent, and `C ∈ B⁺(X)`. -/
theorem theorem_8_3_6_i (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {C : Set X} (hC : IsPetite P C) (hne : C.Nonempty)
    (hL : ∀ x ∈ C, hitProb P C x = 1) : IsRecurrentChain P ψ ∧ 0 < ψ C := by
  have hCm : MeasurableSet C := by obtain ⟨a, ν, h, -⟩ := hC; exact h
  obtain ⟨hpos, hU⟩ := proposition_8_3_1_ii_irreducible P hψ hCm hne hL
  refine ⟨?_, hpos⟩
  rcases theorem_8_3_4 P hψ with h | h
  · exact h
  · obtain ⟨-, M, hM, hb⟩ := theorem_8_3_5 P h.2 hC
    obtain ⟨y, hy⟩ := hne
    exact absurd (top_le_iff.1 (hU y ▸ hb y hy)) hM

/-- A `ψ`-irreducible chain with a uniformly transient set in `B⁺(X)` is transient. -/
theorem isTransientChain_of_uniformlyTransient (P : Kernel X X) [IsMarkovKernel P]
    {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) {A : Set X}
    (hA : IsUniformlyTransient P A) (hpos : 0 < ψ A) : IsTransientChain P ψ :=
  ⟨hψ, isTransientSet_univ_of_uniformlyTransient P hψ.2.1 hA hpos⟩

/-- A transient chain has a uniformly transient set in `B⁺(X)`. -/
theorem IsTransientChain.exists_uniformlyTransient {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} (h : IsTransientChain P ψ) :
    ∃ B, IsUniformlyTransient P B ∧ 0 < ψ B := by
  obtain ⟨B, hB, hcov⟩ := h.2
  by_contra hc
  push Not at hc
  have h0 : ψ (⋃ n, B n) = 0 := measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (hc _ (hB n))
  exact h.1.1 (Measure.measure_univ_eq_zero.1 (measure_mono_null hcov h0))

/-- `L(x, B) ≤ L(x, B ∩ F)` when `F` is absorbing and `x ∈ F`: the chain never leaves `F`. -/
theorem hitProb_inter_absorbing (P : Kernel X X) [IsMarkovKernel P] {B F : Set X}
    (hF : MeasurableSet F) (habs : IsAbsorbing P F) {x : X} (hx : x ∈ F) :
    hitProb P B x ≤ hitProb P (B ∩ F) x := by
  have h0 := habs.hitProb_compl hF hx
  calc hitProb P B x ≤ hitProb P (B ∩ F) x + hitProb P Fᶜ x := by
        refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
        obtain ⟨n, hn, h⟩ := (firstReturn_ne_top_iff B ω).1 hω
        by_cases hnF : ω n ∈ F
        · exact Or.inl ((firstReturn_ne_top_iff _ ω).2 ⟨n, hn, h, hnF⟩)
        · exact Or.inr ((firstReturn_ne_top_iff _ ω).2 ⟨n, hn, hnF⟩)
    _ = hitProb P (B ∩ F) x := by rw [h0, add_zero]

omit [MeasurableSpace X] in
/-- `τ_A = ∞` iff the chain never visits `A` at a time `n ≥ 1`. -/
theorem firstReturn_eq_top_iff (A : Set X) (ω : ℕ → X) :
    firstReturn A ω = ⊤ ↔ ∀ n, 1 ≤ n → ω n ∉ A :=
  hittingAfter_eq_top_iff

/-- `{τ_A ≥ n} ∈ 𝓕ₙ^Φ` (it depends on `Φ₁, …, Φₙ₋₁` only). -/
theorem measurableSet_natFilt_le_firstReturn {A : Set X} (hA : MeasurableSet A) (n : ℕ) :
    MeasurableSet[natFilt n] {ω : ℕ → X | WithTop.some n ≤ firstReturn A ω} := by
  have : {ω : ℕ → X | WithTop.some n ≤ firstReturn A ω} =
      ⋂ j ∈ Finset.range n, {ω | 1 ≤ j → ω j ∈ Aᶜ} := by
    ext ω
    simp only [mem_ofPred_eq, le_firstReturn_iff, mem_iInter, Finset.mem_range, mem_compl_iff]
    exact ⟨fun h j hj h1 => h j h1 hj, fun h j h1 hj => h j hj h1⟩
  rw [this]
  refine Finset.measurableSet_biInter _ fun j hj => ?_
  by_cases h1 : 1 ≤ j
  · have : {ω : ℕ → X | 1 ≤ j → ω j ∈ Aᶜ} = {ω | ω j ∈ Aᶜ} := by ext; simp [h1]
    rw [this]
    exact measurableSet_coord_natFilt (Finset.mem_range.1 hj).le hA.compl
  · simp [h1]

/-- **Theorem 8.3.6 (ii)** (MT p. 186): a `ψ`-irreducible chain is transient iff there are sets
`C, D ∈ B⁺(X)` with `L(x, C) < 1` for every `x ∈ D`. -/
theorem theorem_8_3_6_ii (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) :
    IsTransientChain P ψ ↔ ∃ C D : Set X, MeasurableSet C ∧ MeasurableSet D ∧ 0 < ψ C ∧
      0 < ψ D ∧ ∀ x ∈ D, hitProb P C x < 1 := by
  have := isMarkovKernel_pathKernel P
  constructor
  · intro h
    obtain ⟨B, hB, hψB⟩ := h.exists_uniformlyTransient
    refine ⟨B, {y | hitProb P B y < 1}, hB.1,
      measurableSet_lt (measurable_hitProb P hB.1) measurable_const, hψB, ?_, fun x hx => hx⟩
    rw [pos_iff_ne_zero]
    intro h0
    have hfull : IsFull ψ {y | hitProb P B y < 1}ᶜ := by rw [IsFull, compl_compl]; exact h0
    obtain ⟨F, hFsub, hFne, hFm, habs, hFfull⟩ := proposition_4_2_3_ii hψ
      (measurableSet_lt (measurable_hitProb P hB.1) measurable_const).compl hfull
    have hL1 : ∀ x ∈ F, hitProb P (B ∩ F) x = 1 := fun x hx => by
      have : hitProb P B x = 1 := by
        have := hFsub hx
        simp only [mem_compl_iff, mem_ofPred_eq, not_lt] at this
        exact le_antisymm (hitProb_le_one P B x) this
      exact le_antisymm (hitProb_le_one P _ x) (this ▸ hitProb_inter_absorbing P hFm habs hx)
    have hpos : 0 < ψ (B ∩ F) := by
      rw [pos_iff_ne_zero]
      intro h0
      have : ψ B ≤ ψ (B ∩ F) + ψ Fᶜ := by
        calc ψ B ≤ ψ ((B ∩ F) ∪ Fᶜ) := measure_mono fun y hy => by
              by_cases hyF : y ∈ F
              · exact Or.inl ⟨hy, hyF⟩
              · exact Or.inr hyF
          _ ≤ _ := measure_union_le _ _
      rw [h0, hFfull, add_zero] at this
      exact hψB.ne' (nonpos_iff_eq_zero.1 this)
    obtain ⟨y, hy⟩ := nonempty_of_measure_ne_zero hpos.ne'
    have hrec := proposition_8_3_1_ii P (hB.1.inter hFm) fun x hx => hL1 x hx.2
    obtain ⟨M, hM, hb⟩ := hB.exists_bound
    exact hM (top_le_iff.1 (hrec y hy ▸ (measure_mono inter_subset_left).trans (hb y)))
  · rintro ⟨C, D, hC, hD, hψC, hψD, hL⟩
    -- `D_k = {x ∈ D : L(x, C) ≤ 1 − (k + 1)⁻¹}` cover `D`
    set Dk : ℕ → Set X := fun k => {x ∈ D | hitProb P C x ≤ 1 - ((k + 1 : ℕ) : ℝ≥0∞)⁻¹}
      with hDk
    have hDkm : ∀ k, MeasurableSet (Dk k) := fun k =>
      hD.inter (measurableSet_le (measurable_hitProb P hC) measurable_const)
    have hcov : D ⊆ ⋃ k, Dk k := fun x hx => by
      obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt (tsub_pos_of_lt (hL x hx)).ne'
      refine mem_iUnion.2 ⟨k, hx, ?_⟩
      have h1 : ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ 1 - hitProb P C x :=
        (ENNReal.inv_le_inv.2 (by exact_mod_cast Nat.le_succ k)).trans hk.le
      calc hitProb P C x = 1 - (1 - hitProb P C x) :=
            (ENNReal.sub_sub_cancel ENNReal.one_ne_top (hitProb_le_one P C x)).symm
        _ ≤ _ := tsub_le_tsub_left h1 1
    have : ∃ k, 0 < ψ (Dk k) := by
      by_contra hc
      push Not at hc
      exact hψD.ne' (measure_mono_null hcov (measure_iUnion_null fun k =>
        nonpos_iff_eq_zero.1 (hc k)))
    obtain ⟨k, hk⟩ := this
    set ε : ℝ≥0∞ := ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ with hε
    have hε0 : 0 < ε := by simp [hε]
    have hε1 : ε ≤ 1 := by
      rw [hε]; exact ENNReal.inv_le_one.2 (by exact_mod_cast Nat.succ_pos k)
    have hεL : ∀ y ∈ Dk k, ε ≤ 1 - hitProb P C y := fun y hy =>
      ENNReal.le_sub_of_add_le_left (ne_top_of_le_ne_top ENNReal.one_ne_top
        (hitProb_le_one P C y)) ((add_le_add hy.2 le_rfl).trans
        (le_of_eq (tsub_add_cancel_of_le hε1)))
    by_cases hDC : 0 < ψ (Dk k ∩ C)
    · -- `D_ε ∩ C` is uniformly transient
      refine isTransientChain_of_uniformlyTransient P hψ ⟨(hDkm k).inter hC, (1 - (1 - ε))⁻¹,
        ?_, fun x _ => proposition_8_3_1_iii P ((hDkm k).inter hC)
          (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hε0.ne') (fun y hy =>
            (hitProb_mono P inter_subset_right y).trans hy.1.2) x⟩ hDC
      rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top hε1]
      exact ENNReal.inv_ne_top.2 hε0.ne'
    · -- `E = D_ε \ C` is in `B⁺(X)`
      push Not at hDC
      set E := Dk k ∩ Cᶜ with hE
      have hEm : MeasurableSet E := (hDkm k).inter hC.compl
      have hψE : 0 < ψ E := by
        rw [pos_iff_ne_zero]
        intro h0
        have : ψ (Dk k) ≤ ψ (Dk k ∩ C) + ψ E := by
          calc ψ (Dk k) ≤ ψ ((Dk k ∩ C) ∪ E) := measure_mono fun y hy => by
                by_cases hyC : y ∈ C
                · exact Or.inl ⟨hy, hyC⟩
                · exact Or.inr ⟨hy, hyC⟩
            _ ≤ _ := measure_union_le _ _
        rw [nonpos_iff_eq_zero.1 hDC, h0, add_zero] at this
        exact hk.ne' (nonpos_iff_eq_zero.1 this)
      -- some `C_δ = {y ∈ C : _CPⁿ⁺¹(y, E) ≥ δ}` is in `B⁺(X)`
      set Cnj : ℕ → ℕ → Set X := fun n j =>
        {y ∈ C | ((j + 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ tabooKernel P hC n y E} with hCnj
      have hCnjm : ∀ n j, MeasurableSet (Cnj n j) := fun n j =>
        hC.inter (measurableSet_le measurable_const (Kernel.measurable_coe _ hEm))
      have hex : ∃ n j, 0 < ψ (Cnj n j) := by
        by_contra hc
        push Not at hc
        set N := ⋃ n, ⋃ j, Cnj n j with hN
        have hNm : MeasurableSet N := MeasurableSet.iUnion fun n => MeasurableSet.iUnion
          fun j => hCnjm n j
        have hψN : ψ N = 0 := measure_iUnion_null fun n => measure_iUnion_null fun j =>
          nonpos_iff_eq_zero.1 (hc n j)
        have hψH := hψ.hitSet_null hNm hψN
        have hgood : 0 < ψ (C \ (N ∪ {y | 0 < hitProb P N y})) := by
          rw [measure_sdiff_null (measure_union_null hψN hψH)]; exact hψC
        obtain ⟨y₀, hy₀C, hy₀⟩ := nonempty_of_measure_ne_zero hgood.ne'
        simp only [mem_union, mem_ofPred_eq, not_or, not_lt, nonpos_iff_eq_zero] at hy₀
        -- `U_C(w, E) = 0` for `w ∈ C \ N`
        have hUC : ∀ w ∈ C, w ∉ N → tabooPotKernel P hC w E = 0 := fun w hwC hwN => by
          rw [tabooPotKernel, Kernel.sum_apply' _ _ hEm, ENNReal.tsum_eq_zero]
          intro n
          by_contra h0
          obtain ⟨j, hj⟩ := ENNReal.exists_inv_nat_lt h0
          exact hwN (mem_iUnion.2 ⟨n, mem_iUnion.2 ⟨j, hwC,
            (ENNReal.inv_le_inv.2 (by exact_mod_cast Nat.le_succ j)).trans hj.le⟩⟩)
        have hUN : potKernel P y₀ N = 0 := by
          rw [potKernel_apply P y₀ hNm, ENNReal.tsum_eq_zero]
          intro n
          exact nonpos_iff_eq_zero.1 (hy₀.2 ▸ pow_le_hitProb P hNm n y₀)
        have hUE : potKernel P y₀ E = 0 := by
          refine potKernel_eq_zero_of_lastExit P hC y₀ hEm (hUC y₀ hy₀C hy₀.1) ?_
          refine nonpos_iff_eq_zero.1 ?_
          calc ∫⁻ w in C, tabooPotKernel P hC w E ∂potKernel P y₀
              ≤ ∫⁻ w, N.indicator (fun _ => ∞) w ∂potKernel P y₀ := by
                rw [← lintegral_indicator hC]
                refine lintegral_mono fun w => ?_
                by_cases hwC : w ∈ C
                · by_cases hwN : w ∈ N
                  · rw [indicator_of_mem hwN]; exact le_top
                  · rw [indicator_of_mem hwC, hUC w hwC hwN]; exact zero_le
                · rw [indicator_of_notMem hwC]; exact zero_le
            _ = 0 := by rw [lintegral_indicator_const hNm, hUN, mul_zero]
        have hpos := (potKernel_pos_iff P hEm y₀).2
          ((hitProb_pos_iff P hEm y₀).1 (hψ.2.1 E hEm hψE y₀))
        rw [hUE] at hpos
        exact lt_irrefl _ hpos
      obtain ⟨n, j, hnj⟩ := hex
      set δ : ℝ≥0∞ := ((j + 1 : ℕ) : ℝ≥0∞)⁻¹ with hδ
      have hδ0 : 0 < δ := by simp [hδ]
      -- for `x ∈ C_δ`, `1 − L(x, C_δ) ≥ ε δ`
      have hCδm := hCnjm n j
      have hbound : ∀ x ∈ Cnj n j, hitProb P (Cnj n j) x ≤ 1 - ε * δ := by
        intro x hx
        set G : Set (ℕ → X) := {ω | WithTop.some (n + 1) ≤ firstReturn C ω} ∩
          {ω | ω (n + 1) ∈ E} with hGdef
        have hG : MeasurableSet[natFilt (n + 1)] G :=
          (measurableSet_natFilt_le_firstReturn hC (n + 1)).inter
            (measurableSet_coord_natFilt le_rfl hEm)
        have hTop : MeasurableSet {ω : ℕ → X | firstReturn C ω = ⊤} := by
          convert (measurableSet_firstReturn_ne_top hC).compl using 1
          ext ω; simp
        have hsub : G ∩ shift (n + 1) ⁻¹' {ω | firstReturn C ω = ⊤} ⊆
            {ω | firstReturn (Cnj n j) ω = ⊤} := by
          rintro ω ⟨⟨h1, h2⟩, h3⟩
          simp only [mem_ofPred_eq, mem_preimage] at h1 h2 h3
          rw [mem_ofPred_eq, firstReturn_eq_top_iff]
          intro t ht htC
          have htC' : ω t ∈ C := htC.1
          rcases lt_trichotomy t (n + 1) with htn | htn | htn
          · exact (le_firstReturn_iff C ω (n + 1)).1 h1 t ht htn htC'
          · rw [htn] at htC'; exact h2.2 htC'
          · have := (firstReturn_eq_top_iff C _).1 h3 (t - (n + 1)) (by omega)
            rw [shift_apply, show n + 1 + (t - (n + 1)) = t by omega] at this
            exact this htC'
        have hlow : ε * δ ≤ pathKernel P x {ω | firstReturn (Cnj n j) ω = ⊤} := by
          refine le_trans ?_ (measure_mono hsub)
          rw [pathKernel_inter_shift P x hG hTop, hGdef, inter_comm,
            ← Measure.restrict_restrict (s := {ω : ℕ → X | ω (n + 1) ∈ E})
              (measurable_pi_apply (n + 1) hEm),
            ← lintegral_indicator (s := {ω : ℕ → X | ω (n + 1) ∈ E})
              (measurable_pi_apply (n + 1) hEm)]
          have e : ({ω : ℕ → X | ω (n + 1) ∈ E}.indicator fun ω =>
              pathKernel P (ω (n + 1)) {ω | firstReturn C ω = ⊤}) =
              fun ω => E.indicator (fun y => pathKernel P y {ω | firstReturn C ω = ⊤})
                (ω (n + 1)) := by
            ext ω; by_cases h : ω (n + 1) ∈ E <;> simp [h]
          rw [e, setLIntegral_le_firstReturn P hC n x
            ((Kernel.measurable_coe _ hTop).indicator hEm), lintegral_indicator hEm]
          calc ε * δ ≤ ε * tabooKernel P hC n x E := mul_le_mul' le_rfl hx.2
            _ = ∫⁻ _ in E, ε ∂tabooKernel P hC n x := by rw [setLIntegral_const, mul_comm]
            _ ≤ _ := setLIntegral_mono (Kernel.measurable_coe _ hTop) fun y hy => by
                have hc := prob_compl_eq_one_sub (μ := pathKernel P y)
                  (measurableSet_firstReturn_ne_top hC)
                have hset : {ω : ℕ → X | firstReturn C ω ≠ ⊤}ᶜ =
                    {ω | firstReturn C ω = ⊤} := by ext ω; simp
                rw [hset] at hc
                rw [hc]
                exact hεL y hy.1
        have hc := prob_compl_eq_one_sub (μ := pathKernel P x)
          (measurableSet_firstReturn_ne_top hCδm)
        have hset : {ω : ℕ → X | firstReturn (Cnj n j) ω ≠ ⊤}ᶜ =
            {ω | firstReturn (Cnj n j) ω = ⊤} := by ext ω; simp
        rw [hset] at hc
        rw [hc] at hlow
        have hle := tsub_le_tsub_left hlow 1
        rwa [ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one] at hle
      have hεδ : 0 < ε * δ := ENNReal.mul_pos hε0.ne' hδ0.ne'
      have hεδ1 : ε * δ ≤ 1 := (mul_le_mul' hε1 (by
        rw [hδ]; exact ENNReal.inv_le_one.2 (by exact_mod_cast Nat.succ_pos j))).trans
        (le_of_eq (one_mul 1))
      refine isTransientChain_of_uniformlyTransient P hψ ⟨hCδm, (1 - (1 - ε * δ))⁻¹, ?_,
        fun x _ => proposition_8_3_1_iii P hCδm
          (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hεδ.ne') hbound x⟩ hnj
      rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top hεδ1]
      exact ENNReal.inv_ne_top.2 hεδ.ne'

/-- **Proposition 8.3.7** (MT p. 186): for a `ψ`-irreducible chain every `ψ`-null set is
transient. -/
theorem proposition_8_3_7 (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {D : Set X} (hD : MeasurableSet D) (h0 : ψ D = 0) :
    IsTransientSet P D := by
  have hfull : IsFull ψ Dᶜ := by rw [IsFull, compl_compl]; exact h0
  obtain ⟨F, hFsub, -, hFm, habs, hFfull⟩ := proposition_4_2_3_ii hψ hD.compl hfull
  have hψF : 0 < ψ F := by
    rw [pos_iff_ne_zero]
    intro h
    exact hψ.1 (Measure.measure_univ_eq_zero.1 (by
      rw [← union_compl_self F]; exact measure_union_null h hFfull))
  have habs' : IsAbsorbing P Fᶜᶜ := by rw [compl_compl]; exact habs
  refine (proposition_8_3_3 P hFm.compl habs' fun x _ => ?_).mono
    fun x hx hxF => hFsub hxF hx
  rw [compl_compl]
  exact hψ.2.1 F hFm hψF x

/-- **Proposition 8.3.8** (MT p. 187): on a countably generated space, a `ψ`-irreducible chain has
a `d`-cycle `D₀, …, D_{d−1}` (`P(x, D_{i+1}) = 1` on `Dᵢ`), and the exceptional set
`N = (⋃ Dᵢ)ᶜ` is `ψ`-null and transient. -/
theorem proposition_8_3_8 [MeasurableSpace.CountablyGenerated X] (P : Kernel X X)
    [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) :
    ∃ (d : ℕ) (D : ZMod d → Set X), 0 < d ∧ IsCycle P ψ d D ∧
      ψ (⋃ i, D i)ᶜ = 0 ∧ IsTransientSet P (⋃ i, D i)ᶜ := by
  obtain ⟨d, hd⟩ := exists_isPeriod P hψ
  obtain ⟨D, hD⟩ := hd.2.1
  have hm : MeasurableSet (⋃ i, D i)ᶜ := by
    have : NeZero d := ⟨hd.1.ne'⟩
    exact (MeasurableSet.iUnion fun i => hD.measurableSet i).compl
  exact ⟨d, D, hd.1, hD, hD.null_compl, proposition_8_3_7 P hψ hm hD.null_compl⟩

end MeynTweedie.InvarianceTightness
