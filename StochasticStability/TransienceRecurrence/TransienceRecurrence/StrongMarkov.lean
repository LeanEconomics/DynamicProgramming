/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import TransienceRecurrence.MarkovProperty

/-!
# Stopping times and the strong Markov property (MT §3.4.3)

Meyn and Tweedie, §3.4.3, pp. 64–66. A stopping time for the chain is a stopping time
`ζ : (ℕ → X) → ℕ ∪ {∞}` (Mathlib's `WithTop ℕ`) for the natural filtration `𝓕ₙ^Φ` of the
coordinate process (p. 65). `𝓕_ζ^Φ` is Mathlib's `hζ.measurableSpace`.

* `iSup_natFilt`: `⋁ₙ 𝓕ₙ^Φ` is the product σ-algebra.
* `measurableSet_stoppedField_iff` (p. 66): `A ∈ 𝓕_ζ^Φ` iff `A` is an event and
  `A ∩ {ζ = n} ∈ 𝓕ₙ^Φ` for every `n`; this is the book's definition of `𝓕_ζ^Φ`.
* `stoppedState ζ = Φ_ζ` and `shiftAt ζ = θ^ζ` (p. 66), meaningful on `{ζ < ∞}`;
  `measurable_stoppedState`, `measurable_shiftAt`.
* `measurable_stoppedField_indicator`: `1_{ζ<∞} k(Φ_ζ)` is `𝓕_ζ^Φ`-measurable.
* `strong_markov_lintegral_mul`: the same with an `𝓕_ζ^Φ`-measurable weight `F ≥ 0`.
* `strong_markov_lintegral`, `strong_markov_measure`, `strong_markov_setIntegral`: for
  `A ∈ 𝓕_ζ^Φ`, `∫_{A ∩ {ζ<∞}} H ∘ θ^ζ dP_μ = ∫_{A ∩ {ζ<∞}} E_{Φ_ζ}[H] dP_μ`, for nonnegative and
  for integrable `H`, and as an identity of measures on path space.
* `strong_markov_property` (3.32): `E_μ[1_{ζ<∞} θ^ζH | 𝓕_ζ^Φ] = 1_{ζ<∞} E_{Φ_ζ}[H]`, `P_μ`-a.s.,
  for measurable `H` with `1_{ζ<∞} θ^ζH` integrable.
* `StrongMarkovProperty` (p. 66): the property (3.32) for every initial law, bounded measurable
  `H` and stopping time; **Proposition 3.4.6** (`proposition_3_4_6`, p. 66): every chain has it.

The proof is the book's: decompose over `{ζ = n}` and use the Markov property at each fixed
`n` (`markov_lintegral`, `markov_setIntegral`).

**Corrections.** The book writes (3.32) as an identity "on the set `{ζ < ∞}`" between
conditional expectations of `θ^ζH`, which is only defined on `{ζ < ∞}`. The precise statement
proved here multiplies both sides by `1_{ζ<∞}`, an `𝓕_ζ^Φ`-measurable factor.
-/

namespace MeynTweedie.TransienceRecurrence

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### The σ-algebra `𝓕_ζ^Φ` -/

/-- The natural filtration generates the product σ-algebra: `⋁ₙ 𝓕ₙ^Φ = B(X)^ℕ`. -/
theorem iSup_natFilt :
    ⨆ n, natFilt (X := X) n = (MeasurableSpace.pi : MeasurableSpace (ℕ → X)) := by
  refine le_antisymm (iSup_le (natFilt (X := X)).le) ?_
  refine iSup_le fun i => ?_
  exact ((measurable_coord_natFilt i).comap_le).trans (le_iSup (fun n => natFilt (X := X) n) i)

omit [MeasurableSpace X] in
/-- On `{ζ ≤ i}`, `ζ` takes one of the values `0, …, i`. -/
theorem setOf_le_eq_biUnion (τ : (ℕ → X) → WithTop ℕ) (i : ℕ) :
    {ω | τ ω ≤ WithTop.some i} = ⋃ n ∈ Finset.range (i + 1), {ω | τ ω = n} := by
  ext ω
  simp only [mem_ofPred_eq, mem_iUnion, Finset.mem_range, exists_prop]
  constructor
  · intro h
    cases ht : τ ω with
    | top => rw [ht] at h; simp at h
    | coe t => rw [ht] at h; exact ⟨t, Nat.lt_succ_of_le (WithTop.coe_le_coe.1 h), rfl⟩
  · rintro ⟨n, hn, h⟩
    rw [h]; exact WithTop.coe_le_coe.2 (Nat.le_of_lt_succ hn)

omit [MeasurableSpace X] in
/-- `{ζ = ∞}` is the complement of `⋃ₙ {ζ = n}`. -/
theorem setOf_ne_top_eq_iUnion (τ : (ℕ → X) → WithTop ℕ) :
    {ω | τ ω ≠ ⊤} = ⋃ n : ℕ, {ω | τ ω = n} := by
  ext ω
  simp only [mem_ofPred_eq, mem_iUnion]
  constructor
  · intro h
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 h
    exact ⟨t, ht.symm⟩
  · rintro ⟨n, h⟩; rw [h]; exact WithTop.coe_ne_top

/-- `{ζ < ∞}` is an event. -/
theorem measurableSet_ne_top {τ : (ℕ → X) → WithTop ℕ}
    (hτ : IsStoppingTime (natFilt (X := X)) τ) : MeasurableSet {ω | τ ω ≠ ⊤} := by
  rw [setOf_ne_top_eq_iUnion]
  exact MeasurableSet.iUnion fun n =>
    (natFilt (X := X)).le n _ (hτ.measurableSet_eq_of_countable n)

/-- (MT p. 66) `A ∈ 𝓕_ζ^Φ` iff `A` is an event with `A ∩ {ζ = n} ∈ 𝓕ₙ^Φ` for all `n`: Mathlib's
`𝓕_ζ` is the book's. -/
theorem measurableSet_stoppedField_iff {τ : (ℕ → X) → WithTop ℕ}
    (hτ : IsStoppingTime (natFilt (X := X)) τ) (A : Set (ℕ → X)) :
    MeasurableSet[hτ.measurableSpace] A ↔
      MeasurableSet A ∧ ∀ n : ℕ, MeasurableSet[natFilt n] (A ∩ {ω | τ ω = n}) := by
  rw [hτ.measurableSet, iSup_natFilt]
  refine and_congr Iff.rfl ⟨fun h n => ?_, fun h i => ?_⟩
  · have : A ∩ {ω | τ ω = n} = (A ∩ {ω | τ ω ≤ n}) ∩ {ω | τ ω = n} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨ha, he⟩; exact ⟨⟨ha, he.le⟩, he⟩
      · rintro ⟨⟨ha, _⟩, he⟩; exact ⟨ha, he⟩
    rw [this]
    exact (h n).inter (hτ.measurableSet_eq_of_countable n)
  · rw [setOf_le_eq_biUnion, inter_iUnion₂]
    refine Finset.measurableSet_biUnion _ fun n hn => ?_
    exact (natFilt (X := X)).mono (Nat.le_of_lt_succ (Finset.mem_range.1 hn)) _ (h n)

/-- `{ζ < ∞} ∈ 𝓕_ζ^Φ`. -/
theorem measurableSet_stoppedField_ne_top {τ : (ℕ → X) → WithTop ℕ}
    (hτ : IsStoppingTime (natFilt (X := X)) τ) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω ≠ ⊤} := by
  rw [measurableSet_stoppedField_iff]
  refine ⟨measurableSet_ne_top hτ, fun n => ?_⟩
  have : {ω : ℕ → X | τ ω ≠ ⊤} ∩ {ω | τ ω = n} = {ω | τ ω = n} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, and_iff_right_iff_imp]
    intro h; rw [h]; exact WithTop.coe_ne_top
  rw [this]
  exact hτ.measurableSet_eq_of_countable n

/-! ### `Φ_ζ` and `θ^ζ` -/

/-- `Φ_ζ = Φₙ` on `{ζ = n}` (MT p. 66); its value on `{ζ = ∞}` is irrelevant. -/
noncomputable def stoppedState (τ : (ℕ → X) → WithTop ℕ) (ω : ℕ → X) : X := ω (τ ω).untopA

/-- The shift `θ^ζ = θⁿ` on `{ζ = n}` (MT p. 66). -/
noncomputable def shiftAt (τ : (ℕ → X) → WithTop ℕ) (ω : ℕ → X) : ℕ → X := shift (τ ω).untopA ω

omit [MeasurableSpace X] in
/-- On `{ζ = n}`, `Φ_ζ = Φₙ`. -/
theorem stoppedState_of_eq {τ : (ℕ → X) → WithTop ℕ} {ω : ℕ → X} {n : ℕ} (h : τ ω = n) :
    stoppedState τ ω = ω n := by
  simp only [stoppedState, h]; rfl

omit [MeasurableSpace X] in
/-- On `{ζ = n}`, `θ^ζ = θⁿ`. -/
theorem shiftAt_of_eq {τ : (ℕ → X) → WithTop ℕ} {ω : ℕ → X} {n : ℕ} (h : τ ω = n) :
    shiftAt τ ω = shift n ω := by
  simp only [shiftAt, h]; rfl

/-- A function on path space that agrees with a measurable `Fₙ` on each `{ζ = n}` and with a
measurable `F_∞` on `{ζ = ∞}` is measurable. -/
theorem measurable_of_stopping_pieces {β : Type*} [MeasurableSpace β]
    {τ : (ℕ → X) → WithTop ℕ} (hτ : IsStoppingTime (natFilt (X := X)) τ) {F : (ℕ → X) → β}
    (Fn : ℕ → (ℕ → X) → β) (Ftop : (ℕ → X) → β) (hFn : ∀ n, Measurable (Fn n))
    (hFtop : Measurable Ftop) (hn : ∀ (n : ℕ) ω, τ ω = n → F ω = Fn n ω)
    (htop : ∀ ω, τ ω = ⊤ → F ω = Ftop ω) : Measurable F := by
  intro S hS
  have hset : F ⁻¹' S = (⋃ n : ℕ, {ω | τ ω = n} ∩ Fn n ⁻¹' S) ∪
      ({ω | τ ω ≠ ⊤}ᶜ ∩ Ftop ⁻¹' S) := by
    ext ω
    simp only [mem_preimage, mem_union, mem_iUnion, mem_inter_iff, mem_ofPred_eq,
      mem_compl_iff, not_not]
    cases ht : τ ω with
    | top => simp [htop ω ht]
    | coe t =>
      simp only [WithTop.coe_ne_top, false_and, or_false]
      constructor
      · intro h; exact ⟨t, rfl, by rwa [← hn t ω ht]⟩
      · rintro ⟨k, hk, h⟩
        rw [WithTop.coe_inj.1 hk] at ht
        rwa [hn k ω ht]
  rw [hset]
  refine MeasurableSet.union (MeasurableSet.iUnion fun n => ?_)
    ((measurableSet_ne_top hτ).compl.inter (hFtop hS))
  exact ((natFilt (X := X)).le n _ (hτ.measurableSet_eq_of_countable n)).inter (hFn n hS)

/-- `Φ_ζ` is measurable. -/
theorem measurable_stoppedState {τ : (ℕ → X) → WithTop ℕ}
    (hτ : IsStoppingTime (natFilt (X := X)) τ) : Measurable (stoppedState τ) :=
  measurable_of_stopping_pieces hτ (fun n ω => ω n) (fun ω => ω (⊤ : WithTop ℕ).untopA)
    (fun n => measurable_pi_apply n) (measurable_pi_apply _)
    (fun _ _ h => stoppedState_of_eq h) (fun ω h => by simp [stoppedState, h])

/-- `θ^ζ` is measurable. -/
theorem measurable_shiftAt {τ : (ℕ → X) → WithTop ℕ}
    (hτ : IsStoppingTime (natFilt (X := X)) τ) : Measurable (shiftAt τ) :=
  measurable_of_stopping_pieces hτ (fun n ω => shift n ω) (fun ω => shift (⊤ : WithTop ℕ).untopA ω)
    (fun n => measurable_shift n) (measurable_shift _)
    (fun _ _ h => shiftAt_of_eq h) (fun ω h => by simp [shiftAt, h])

/-- `1_{ζ<∞} k(Φ_ζ)` is `𝓕_ζ^Φ`-measurable for measurable `k`. -/
theorem measurable_stoppedField_indicator {τ : (ℕ → X) → WithTop ℕ}
    (hτ : IsStoppingTime (natFilt (X := X)) τ) {k : X → ℝ} (hk : Measurable k) :
    Measurable[hτ.measurableSpace]
      ({ω | τ ω ≠ ⊤}.indicator fun ω => k (stoppedState τ ω)) := by
  intro S hS
  rw [measurableSet_stoppedField_iff]
  refine ⟨((hk.comp (measurable_stoppedState hτ)).indicator (measurableSet_ne_top hτ)) hS,
    fun n => ?_⟩
  have : ({ω | τ ω ≠ ⊤}.indicator fun ω => k (stoppedState τ ω)) ⁻¹' S ∩ {ω | τ ω = n} =
      {ω | ω n ∈ k ⁻¹' S} ∩ {ω | τ ω = n} := by
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      have hne : τ ω ≠ ⊤ := by rw [h2]; exact WithTop.coe_ne_top
      rw [indicator_of_mem (show ω ∈ {ω | τ ω ≠ ⊤} from hne), stoppedState_of_eq h2] at h1
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      have hne : τ ω ≠ ⊤ := by rw [h2]; exact WithTop.coe_ne_top
      rw [indicator_of_mem (show ω ∈ {ω | τ ω ≠ ⊤} from hne), stoppedState_of_eq h2]
      exact ⟨h1, h2⟩
  rw [this]
  exact (measurableSet_coord_natFilt le_rfl (hk hS)).inter (hτ.measurableSet_eq_of_countable n)

/-! ### The strong Markov property -/

omit [MeasurableSpace X] in
/-- `A ∩ {ζ < ∞}` is the disjoint union of the `A ∩ {ζ = n}`. -/
theorem inter_ne_top_eq_iUnion (τ : (ℕ → X) → WithTop ℕ) (A : Set (ℕ → X)) :
    A ∩ {ω | τ ω ≠ ⊤} = ⋃ n : ℕ, A ∩ {ω | τ ω = n} := by
  rw [setOf_ne_top_eq_iUnion, inter_iUnion]

omit [MeasurableSpace X] in
/-- The pieces `A ∩ {ζ = n}` are pairwise disjoint. -/
theorem pairwise_disjoint_inter_eq (τ : (ℕ → X) → WithTop ℕ) (A : Set (ℕ → X)) :
    Pairwise (Function.onFun Disjoint fun n : ℕ => A ∩ {ω | τ ω = n}) := by
  intro i j hij
  refine Set.disjoint_left.2 fun ω hi hj => hij ?_
  exact WithTop.coe_inj.1 (hi.2.symm.trans hj.2)

/-- **The strong Markov property** for nonnegative functionals: for a stopping time `ζ`,
`A ∈ 𝓕_ζ^Φ` and measurable `H ≥ 0`,
`∫_{A ∩ {ζ<∞}} H ∘ θ^ζ dP_μ = ∫_{A ∩ {ζ<∞}} E_{Φ_ζ}[H] dP_μ`. -/
theorem strong_markov_lintegral (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {τ : (ℕ → X) → WithTop ℕ}
    (hτ : IsStoppingTime (natFilt (X := X)) τ) {A : Set (ℕ → X)}
    (hA : MeasurableSet[hτ.measurableSpace] A) {H : (ℕ → X) → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ ω in A ∩ {ω | τ ω ≠ ⊤}, H (shiftAt τ ω) ∂pathMeasure P μ =
      ∫⁻ ω in A ∩ {ω | τ ω ≠ ⊤}, ∫⁻ ω', H ω' ∂pathKernel P (stoppedState τ ω)
        ∂pathMeasure P μ := by
  rw [measurableSet_stoppedField_iff] at hA
  have hm : ∀ n : ℕ, MeasurableSet (A ∩ {ω | τ ω = n}) := fun n =>
    (natFilt (X := X)).le n _ (hA.2 n)
  rw [inter_ne_top_eq_iUnion, lintegral_iUnion hm (pairwise_disjoint_inter_eq τ A),
    lintegral_iUnion hm (pairwise_disjoint_inter_eq τ A)]
  refine tsum_congr fun n => ?_
  calc ∫⁻ ω in A ∩ {ω | τ ω = n}, H (shiftAt τ ω) ∂pathMeasure P μ
      = ∫⁻ ω in A ∩ {ω | τ ω = n}, H (shift n ω) ∂pathMeasure P μ :=
        setLIntegral_congr_fun (hm n) fun ω hω => by rw [shiftAt_of_eq hω.2]
    _ = ∫⁻ ω in A ∩ {ω | τ ω = n}, ∫⁻ ω', H ω' ∂pathKernel P (ω n) ∂pathMeasure P μ :=
        markov_lintegral P μ (hA.2 n) hH
    _ = _ := setLIntegral_congr_fun (hm n) fun ω hω => by rw [stoppedState_of_eq hω.2]

/-- **The strong Markov property** with an `𝓕_ζ^Φ`-measurable weight: for `F ≥ 0` measurable
for `𝓕_ζ^Φ` and measurable `H ≥ 0`,
`E_μ[F · H ∘ θ^ζ; ζ < ∞] = E_μ[F · E_{Φ_ζ}[H]; ζ < ∞]`. -/
theorem strong_markov_lintegral_mul (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {τ : (ℕ → X) → WithTop ℕ}
    (hτ : IsStoppingTime (natFilt (X := X)) τ) {F : (ℕ → X) → ℝ≥0∞}
    (hF : Measurable[hτ.measurableSpace] F) {H : (ℕ → X) → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ ω in {ω | τ ω ≠ ⊤}, F ω * H (shiftAt τ ω) ∂pathMeasure P μ =
      ∫⁻ ω in {ω | τ ω ≠ ⊤}, F ω * ∫⁻ ω', H ω' ∂pathKernel P (stoppedState τ ω)
        ∂pathMeasure P μ := by
  have := isMarkovKernel_pathKernel P
  have hle := hτ.measurableSpace_le
  have hG : Measurable fun ω => H (shiftAt τ ω) := hH.comp (measurable_shiftAt hτ)
  have hK : Measurable fun ω : ℕ → X => ∫⁻ ω', H ω' ∂pathKernel P (stoppedState τ ω) :=
    hH.lintegral_kernel.comp (measurable_stoppedState hτ)
  refine Measurable.ennreal_induction (motive := fun F => ∫⁻ ω in {ω | τ ω ≠ ⊤},
      F ω * H (shiftAt τ ω) ∂pathMeasure P μ = ∫⁻ ω in {ω | τ ω ≠ ⊤},
        F ω * ∫⁻ ω', H ω' ∂pathKernel P (stoppedState τ ω) ∂pathMeasure P μ) ?_ ?_ ?_ hF
  · intro c s hs
    have hs' : MeasurableSet s := hle _ hs
    have e1 : ∀ ω, s.indicator (fun _ => c) ω * H (shiftAt τ ω) =
        s.indicator (fun ω => c * H (shiftAt τ ω)) ω := fun ω => by
      by_cases h : ω ∈ s <;> simp [h]
    have e2 : ∀ ω, s.indicator (fun _ => c) ω * ∫⁻ ω', H ω' ∂pathKernel P (stoppedState τ ω) =
        s.indicator (fun ω => c * ∫⁻ ω', H ω' ∂pathKernel P (stoppedState τ ω)) ω := fun ω => by
      by_cases h : ω ∈ s <;> simp [h]
    simp_rw [e1, e2, setLIntegral_indicator hs', lintegral_const_mul _ hG,
      lintegral_const_mul _ hK]
    rw [strong_markov_lintegral P μ hτ hs hH]
  · intro f g _ hf hg ihf ihg
    simp_rw [Pi.add_apply, add_mul]
    rw [lintegral_add_left (f := fun ω => f ω * H (shiftAt τ ω)) ((hf.mono hle le_rfl).mul hG),
      lintegral_add_left (f := fun ω => f ω * ∫⁻ ω', H ω' ∂pathKernel P (stoppedState τ ω))
        ((hf.mono hle le_rfl).mul hK), ihf, ihg]
  · intro f hf hmono ih
    simp_rw [ENNReal.iSup_mul]
    rw [lintegral_iSup (f := fun k ω => f k ω * H (shiftAt τ ω))
        (fun k => ((hf k).mono hle le_rfl).mul hG)
        (fun i j hij ω => mul_le_mul_left (hmono hij ω) _),
      lintegral_iSup (f := fun k ω => f k ω * ∫⁻ ω', H ω' ∂pathKernel P (stoppedState τ ω))
        (fun k => ((hf k).mono hle le_rfl).mul hK)
        (fun i j hij ω => mul_le_mul_left (hmono hij ω) _)]
    simp_rw [ih]

/-- **The strong Markov property as an identity of measures.** For `A ∈ 𝓕_ζ^Φ`, the law of the
post-`ζ` path `θ^ζΦ` on `A ∩ {ζ < ∞}` is the mixture of the `P_y` over the law of `Φ_ζ` on
`A ∩ {ζ < ∞}`. -/
theorem strong_markov_measure (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {τ : (ℕ → X) → WithTop ℕ}
    (hτ : IsStoppingTime (natFilt (X := X)) τ) {A : Set (ℕ → X)}
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    ((pathMeasure P μ).restrict (A ∩ {ω | τ ω ≠ ⊤})).map (shiftAt τ) =
      pathKernel P ∘ₘ (((pathMeasure P μ).restrict (A ∩ {ω | τ ω ≠ ⊤})).map
        (stoppedState τ)) := by
  have := isMarkovKernel_pathKernel P
  ext B hB
  have hi : Measurable (B.indicator (1 : (ℕ → X) → ℝ≥0∞)) := measurable_one.indicator hB
  have h := strong_markov_lintegral P μ hτ hA hi
  rw [Measure.map_apply (measurable_shiftAt hτ) hB, Measure.bind_apply hB (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe _ hB) (measurable_stoppedState hτ),
    ← lintegral_indicator_one (measurable_shiftAt hτ hB)]
  simp_rw [lintegral_indicator_one hB] at h
  exact h

/-- **The strong Markov property** for integrable functionals: for `A ∈ 𝓕_ζ^Φ` and measurable
`H` with `1_{ζ<∞} θ^ζH` integrable, `∫_{A ∩ {ζ<∞}} θ^ζH dP_μ = ∫_{A ∩ {ζ<∞}} E_{Φ_ζ}[H] dP_μ`. -/
theorem strong_markov_setIntegral (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {τ : (ℕ → X) → WithTop ℕ}
    (hτ : IsStoppingTime (natFilt (X := X)) τ) {A : Set (ℕ → X)}
    (hA : MeasurableSet[hτ.measurableSpace] A) {H : (ℕ → X) → ℝ} (hH : Measurable H)
    (hint : IntegrableOn (fun ω => H (shiftAt τ ω)) (A ∩ {ω | τ ω ≠ ⊤}) (pathMeasure P μ)) :
    ∫ ω in A ∩ {ω | τ ω ≠ ⊤}, H (shiftAt τ ω) ∂pathMeasure P μ =
      ∫ ω in A ∩ {ω | τ ω ≠ ⊤}, ∫ ω', H ω' ∂pathKernel P (stoppedState τ ω)
        ∂pathMeasure P μ := by
  have := isMarkovKernel_pathKernel P
  have := isProbabilityMeasure_pathMeasure P μ
  have hA' := (measurableSet_stoppedField_iff hτ A).1 hA
  have hAm : MeasurableSet (A ∩ {ω | τ ω ≠ ⊤}) := hA'.1.inter (measurableSet_ne_top hτ)
  have hmeas := strong_markov_measure P μ hτ hA
  have hi : Integrable H (((pathMeasure P μ).restrict (A ∩ {ω | τ ω ≠ ⊤})).map (shiftAt τ)) :=
    (integrable_map_measure hH.aestronglyMeasurable (measurable_shiftAt hτ).aemeasurable).2 hint
  rw [hmeas] at hi
  have hk : StronglyMeasurable fun y => ∫ ω', H ω' ∂pathKernel P y :=
    StronglyMeasurable.integral_kernel hH.stronglyMeasurable
  calc ∫ ω in A ∩ {ω | τ ω ≠ ⊤}, H (shiftAt τ ω) ∂pathMeasure P μ
      = ∫ ω', H ω' ∂(((pathMeasure P μ).restrict (A ∩ {ω | τ ω ≠ ⊤})).map (shiftAt τ)) :=
        (integral_map (measurable_shiftAt hτ).aemeasurable hH.aestronglyMeasurable).symm
    _ = ∫ ω', H ω' ∂(pathKernel P ∘ₘ (((pathMeasure P μ).restrict
          (A ∩ {ω | τ ω ≠ ⊤})).map (stoppedState τ))) := by rw [hmeas]
    _ = ∫ y, ∫ ω', H ω' ∂pathKernel P y ∂(((pathMeasure P μ).restrict
          (A ∩ {ω | τ ω ≠ ⊤})).map (stoppedState τ)) := integral_measure_comp _ _ hi
    _ = _ := integral_map (measurable_stoppedState hτ).aemeasurable hk.aestronglyMeasurable

/-- **The strong Markov property** (3.32), MT p. 66: for a stopping time `ζ` and measurable `H`
with `1_{ζ<∞} θ^ζH` integrable, `E_μ[1_{ζ<∞} θ^ζH | 𝓕_ζ^Φ] = 1_{ζ<∞} E_{Φ_ζ}[H]`, `P_μ`-a.s. -/
theorem strong_markov_property (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {τ : (ℕ → X) → WithTop ℕ}
    (hτ : IsStoppingTime (natFilt (X := X)) τ) {H : (ℕ → X) → ℝ} (hH : Measurable H)
    (hint : Integrable ({ω | τ ω ≠ ⊤}.indicator fun ω => H (shiftAt τ ω)) (pathMeasure P μ)) :
    (pathMeasure P μ)[{ω | τ ω ≠ ⊤}.indicator (fun ω => H (shiftAt τ ω)) | hτ.measurableSpace]
      =ᵐ[pathMeasure P μ]
        {ω | τ ω ≠ ⊤}.indicator fun ω => ∫ ω', H ω' ∂pathKernel P (stoppedState τ ω) := by
  have := isMarkovKernel_pathKernel P
  have := isProbabilityMeasure_pathMeasure P μ
  have hT := measurableSet_ne_top hτ
  have hk : Measurable fun y => ∫ ω', H ω' ∂pathKernel P y :=
    (StronglyMeasurable.integral_kernel hH.stronglyMeasurable).measurable
  have hgm := measurable_stoppedField_indicator hτ hk
  have hint' : IntegrableOn (fun ω => H (shiftAt τ ω)) {ω | τ ω ≠ ⊤} (pathMeasure P μ) :=
    (integrable_indicator_iff hT).1 hint
  -- integrability of the right-hand side
  have hg : Integrable ({ω | τ ω ≠ ⊤}.indicator fun ω => ∫ ω', H ω' ∂pathKernel P
      (stoppedState τ ω)) (pathMeasure P μ) := by
    refine ⟨(hgm.mono hτ.measurableSpace_le le_rfl).aestronglyMeasurable, ?_⟩
    have hlin := strong_markov_lintegral P μ hτ (A := univ) MeasurableSet.univ
      (H := fun ω => ‖H ω‖ₑ) hH.enorm
    simp only [univ_inter] at hlin
    rw [HasFiniteIntegral, lintegral_congr fun ω => enorm_indicator_eq_indicator_enorm _ ω,
      lintegral_indicator hT]
    calc ∫⁻ ω in {ω | τ ω ≠ ⊤}, ‖∫ ω', H ω' ∂pathKernel P (stoppedState τ ω)‖ₑ
          ∂pathMeasure P μ
        ≤ ∫⁻ ω in {ω | τ ω ≠ ⊤}, ∫⁻ ω', ‖H ω'‖ₑ ∂pathKernel P (stoppedState τ ω)
            ∂pathMeasure P μ := lintegral_mono fun ω => enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ ω in {ω | τ ω ≠ ⊤}, ‖H (shiftAt τ ω)‖ₑ ∂pathMeasure P μ := hlin.symm
      _ < ∞ := hint'.2
  refine (ae_eq_condExp_of_forall_setIntegral_eq hτ.measurableSpace_le hint
    (fun s _ _ => hg.integrableOn) (fun s hs _ => ?_)
    (hgm.stronglyMeasurable).aestronglyMeasurable).symm
  have hsm : MeasurableSet s := hτ.measurableSpace_le _ hs
  rw [setIntegral_indicator hT, setIntegral_indicator hT]
  exact (strong_markov_setIntegral P μ hτ hs hH (hint'.mono_set inter_subset_right)).symm

variable (X) in
/-- The strong Markov property of a chain with transition kernel `P` (MT p. 66): (3.32) holds
for every initial distribution `μ`, every bounded measurable `H` on path space and every stopping
time `ζ` of the natural filtration. -/
def StrongMarkovProperty (P : Kernel X X) [IsMarkovKernel P] : Prop :=
  ∀ (μ : Measure X) [IsProbabilityMeasure μ] (H : (ℕ → X) → ℝ), Measurable H →
    (∃ B, ∀ ω, |H ω| ≤ B) → ∀ (τ : (ℕ → X) → WithTop ℕ)
    (hτ : IsStoppingTime (natFilt (X := X)) τ),
    (pathMeasure P μ)[{ω | τ ω ≠ ⊤}.indicator (fun ω => H (shiftAt τ ω)) | hτ.measurableSpace]
      =ᵐ[pathMeasure P μ]
        {ω | τ ω ≠ ⊤}.indicator fun ω => ∫ ω', H ω' ∂pathKernel P (stoppedState τ ω)

/-- **Proposition 3.4.6** (MT p. 66): a Markov chain with discrete time parameter always has the
strong Markov property. -/
theorem proposition_3_4_6 (P : Kernel X X) [IsMarkovKernel P] : StrongMarkovProperty X P := by
  intro μ _ H hH hB τ hτ
  obtain ⟨B, hB⟩ := hB
  have := isProbabilityMeasure_pathMeasure P μ
  refine strong_markov_property P μ hτ hH ?_
  refine (Integrable.of_bound (hH.comp (measurable_shiftAt hτ)).aestronglyMeasurable B
    (Eventually.of_forall fun ω => ?_)).indicator (measurableSet_ne_top hτ)
  rw [Real.norm_eq_abs]; exact hB _

end MeynTweedie.TransienceRecurrence
