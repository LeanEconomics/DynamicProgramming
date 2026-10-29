/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DriftRegularity.RegularityConverse

/-!
# Evaluating non-positivity (MT §11.5.1)

Meyn and Tweedie, §11.5.1, pp. 278–279. The test function `V ≥ 0` is real valued; (11.43),
`sup_x ∫ P(x, dy) |V(y) − V(x)| < ∞`, is written with the extended norm,
`∫⁻ P(x, dy) ‖V(y) − V(x)‖ₑ ≤ B` for a finite `B`.

**One-transition Markov property.** `pathKernel_map_pair`: under `P_x` the law of `(Φ₀, Φ₁)` is
`δₓ ⊗ P(x, ·)`; `lintegral_pair`, `integral_pair`, and at a general time `setLIntegral_pair`,
`setIntegral_pair`: `E[h(Φₙ, Φₙ₊₁); G] = E[∫ P(Φₙ, dz) h(Φₙ, z); G]` for `G ∈ 𝓕ₙ^Φ`.

**Results.**
* **Theorem 11.5.1** (`theorem_11_5_1`, p. 278): if `ΔV ≥ 0` off `C` (11.42), the increments are
  bounded in mean (11.43), and `V(x₀) > V(x)` on `C` (11.44), then `E_{x₀}[τ_C] = ∞`. The proof is
  the book's: if `E_{x₀}[τ_C] < ∞`, (11.43) makes `Σ_{k<σ_C} (V(Φ_{k+1}) − V(Φ_k))` integrable
  (`integral_tsum`), each term has nonnegative mean by (11.42), so `E[V(Φ_{σ_C})] ≥ V(x₀)`, while
  `V(Φ_{σ_C}) < V(x₀)` almost surely.
* **Theorem 11.5.2** (`theorem_11_5_2`, p. 279): with `C ∈ B⁺(X)` and
  `C⁺ = {x : V(x) > V(y) for all y ∈ C} ∈ B⁺(X)`, the chain is null; the proof combines
  Theorem 11.5.1 with Theorem 11.1.4.
* The example after Theorem 11.5.2 (`theorem_11_5_2_counterexample`, p. 279): without (11.43)
  the conclusion fails. The chain `escKernel` on `ℤ₊` (`k(i) = 2i + 1`) with `V(i) = i` has
  `ΔV(i) = ½ > 0` for `i ≥ 1` and `C = {0}`, `C⁺ = {i ≥ 1}` in `B⁺`, but `E_0[τ_0] ≤ 3`, so it
  is positive.

**Hypotheses.** In Theorem 11.5.2 the book's `C⁺ = {V > sup_C V}` is replaced by the (larger)
set `{x : V(x) > V(y) for all y ∈ C}`; asking it to be in `B⁺(X)` is weaker.

**Corrections.** None.
-/

namespace MeynTweedie.DriftRegularity

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {P : Kernel X X}

/-! ### The law of a transition -/

/-- The law of `(Φ₀, Φ₁)` under `P_x` is `δₓ ⊗ P(x, ·)`. -/
theorem pathKernel_map_pair (P : Kernel X X) [IsMarkovKernel P] (x : X) :
    (pathKernel P x).map (fun ω => (ω 0, ω 1)) = (P x).map (fun z => (x, z)) := by
  have := isMarkovKernel_pathKernel P
  have hm : Measurable fun ω : ℕ → X => (ω 0, ω 1) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
  have hm2 : Measurable fun z : X => (x, z) := measurable_const.prodMk measurable_id
  have : IsProbabilityMeasure ((pathKernel P x).map fun ω => (ω 0, ω 1)) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod (fun s hs => ?_)
    (by rw [Measure.map_apply hm MeasurableSet.univ, Measure.map_apply hm2 MeasurableSet.univ]
        simp)
  obtain ⟨A, hA, B, hB, rfl⟩ := hs
  rw [Measure.map_apply hm (hA.prod hB), Measure.map_apply hm2 (hA.prod hB)]
  set A' : ℕ → Set X := fun i => if i = 0 then A else B with hA'
  have hA'm : ∀ i, MeasurableSet (A' i) := fun i => by
    simp only [hA']; split_ifs; exacts [hA, hB]
  have hbox : (fun ω : ℕ → X => (ω 0, ω 1)) ⁻¹' (A ×ˢ B) = boxSet 1 A' := by
    ext ω
    simp only [mem_preimage, mem_prod, boxSet, mem_ofPred_eq, hA']
    constructor
    · rintro ⟨h0, h1⟩ i hi
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hi with rfl | rfl
      · simpa using h0
      · simpa using h1
    · intro h
      exact ⟨by simpa using h 0 (by norm_num), by simpa using h 1 le_rfl⟩
  rw [hbox, pathKernel_boxSet P x 1 hA'm]
  simp only [cylFn, hA']
  by_cases hx : x ∈ A
  · have : (fun z : X => (x, z)) ⁻¹' (A ×ˢ B) = B := by ext z; simp [hx]
    rw [this, indicator_of_mem (by simpa using hx)]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    exact lintegral_indicator_one hB
  · have : (fun z : X => (x, z)) ⁻¹' (A ×ˢ B) = ∅ := by ext z; simp [hx]
    rw [this, indicator_of_notMem (by simpa using hx), measure_empty]

/-- `E_x[h(Φ₀, Φ₁)] = ∫ P(x, dz) h(x, z)`. -/
theorem lintegral_pair (P : Kernel X X) [IsMarkovKernel P] (x : X) {h : X × X → ℝ≥0∞}
    (hh : Measurable h) : ∫⁻ ω, h (ω 0, ω 1) ∂pathKernel P x = ∫⁻ z, h (x, z) ∂P x := by
  have hm : Measurable fun ω : ℕ → X => (ω 0, ω 1) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
  have hm2 : Measurable fun z : X => (x, z) := measurable_const.prodMk measurable_id
  rw [← lintegral_map hh hm, pathKernel_map_pair, lintegral_map hh hm2]

/-- `E_x[h(Φ₀, Φ₁)] = ∫ P(x, dz) h(x, z)` for real `h`. -/
theorem integral_pair (P : Kernel X X) [IsMarkovKernel P] (x : X) {h : X × X → ℝ}
    (hh : Measurable h) : ∫ ω, h (ω 0, ω 1) ∂pathKernel P x = ∫ z, h (x, z) ∂P x := by
  have hm : Measurable fun ω : ℕ → X => (ω 0, ω 1) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
  have hm2 : Measurable fun z : X => (x, z) := measurable_const.prodMk measurable_id
  rw [← integral_map hm.aemeasurable hh.aestronglyMeasurable, pathKernel_map_pair,
    integral_map hm2.aemeasurable hh.aestronglyMeasurable]

/-- **The Markov property for one transition**: for `G ∈ 𝓕ₙ^Φ`,
`E_μ[h(Φₙ, Φₙ₊₁); G] = E_μ[∫ P(Φₙ, dz) h(Φₙ, z); G]`. -/
theorem setLIntegral_pair (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {n : ℕ} {G : Set (ℕ → X)} (hG : MeasurableSet[natFilt n] G)
    {h : X × X → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ ω in G, h (ω n, ω (n + 1)) ∂pathMeasure P μ =
      ∫⁻ ω in G, ∫⁻ z, h (ω n, z) ∂P (ω n) ∂pathMeasure P μ := by
  have hH : Measurable fun ω' : ℕ → X => h (ω' 0, ω' 1) :=
    hh.comp ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1))
  have h1 := markov_lintegral P μ hG hH
  simp only [shift, add_zero] at h1
  rw [h1]
  refine setLIntegral_congr_fun ((natFilt (X := X)).le n _ hG) fun ω _ => ?_
  exact lintegral_pair P (ω n) hh

/-- **The Markov property for one transition**, real form. -/
theorem setIntegral_pair (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {n : ℕ} {G : Set (ℕ → X)} (hG : MeasurableSet[natFilt n] G)
    {h : X × X → ℝ} (hh : Measurable h)
    (hint : IntegrableOn (fun ω => h (ω n, ω (n + 1))) G (pathMeasure P μ)) :
    ∫ ω in G, h (ω n, ω (n + 1)) ∂pathMeasure P μ =
      ∫ ω in G, ∫ z, h (ω n, z) ∂P (ω n) ∂pathMeasure P μ := by
  have hH : Measurable fun ω' : ℕ → X => h (ω' 0, ω' 1) :=
    hh.comp ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1))
  have h1 := markov_setIntegral P μ hG hH (by simpa [shift] using hint)
  simp only [shift, add_zero] at h1
  rw [h1]
  refine setIntegral_congr_fun ((natFilt (X := X)).le n _ hG) fun ω _ => ?_
  exact integral_pair P (ω n) hh

/-! ### Theorem 11.5.1 -/

omit [MeasurableSpace X] in
/-- `Φ_{σ_A} ∈ A` when `σ_A < ∞`. -/
theorem mem_of_firstHit_eq {A : Set X} {ω : ℕ → X} {t : ℕ}
    (h : firstHit A ω = WithTop.some t) : ω t ∈ A := by
  by_contra hc
  have h1 := (le_firstHit_iff A ω t).1 (le_of_eq h.symm)
  have h2 : WithTop.some (t + 1) ≤ firstHit A ω := (le_firstHit_iff A ω (t + 1)).2 fun j hj => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · exact h1 j hj
    · rw [hj]; exact hc
  rw [h] at h2
  exact absurd (WithTop.coe_le_coe.1 h2) (by omega)

/-- Increments bounded in mean (11.43) make `V` integrable for every `P(x, ·)`. -/
theorem integrable_of_increments {V : X → ℝ} (hV : Measurable V) {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hinc : ∀ x, ∫⁻ y, ‖V y - V x‖ₑ ∂P x ≤ B) [IsMarkovKernel P] (x : X) :
    Integrable V (P x) := by
  refine ⟨hV.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  calc ∫⁻ y, ‖V y‖ₑ ∂P x ≤ ∫⁻ y, (‖V y - V x‖ₑ + ‖V x‖ₑ) ∂P x := lintegral_mono fun y => by
        calc ‖V y‖ₑ = ‖(V y - V x) + V x‖ₑ := by rw [sub_add_cancel]
          _ ≤ _ := enorm_add_le _ _
    _ = ∫⁻ y, ‖V y - V x‖ₑ ∂P x + ‖V x‖ₑ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    _ < ∞ := ENNReal.add_lt_top.2 ⟨(hinc x).trans_lt hB.lt_top, enorm_lt_top⟩

/-- **Theorem 11.5.1** (MT p. 278). Let `V ≥ 0` satisfy `ΔV ≥ 0` off `C` (11.42), with increments
bounded in mean, `sup_x ∫ P(x, dy) |V(y) − V(x)| < ∞` (11.43). If `V(x₀) > V(x)` for every
`x ∈ C` (11.44), then `E_{x₀}[τ_C] = ∞`. -/
theorem theorem_11_5_1 [IsMarkovKernel P] {V : X → ℝ} (hV : Measurable V)
    {C : Set X} (hC : MeasurableSet C) (hdrift : ∀ x ∉ C, V x ≤ ∫ y, V y ∂P x)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hinc : ∀ x, ∫⁻ y, ‖V y - V x‖ₑ ∂P x ≤ B)
    {x₀ : X} (hx₀ : ∀ x ∈ C, V x < V x₀) : meanReturnTime P C x₀ = ∞ := by
  have hx₀C : x₀ ∉ C := fun h => lt_irrefl _ (hx₀ x₀ h)
  have := isMarkovKernel_pathKernel P
  by_contra hfin
  set μ := pathKernel P x₀ with hμ
  have hσ := (proposition_3_4_4 hC).2
  have hGk := measurableSet_lt_of_isStoppingTime hσ
  have hG : ∀ k : ℕ, MeasurableSet {ω : ℕ → X | (k : WithTop ℕ) < firstHit C ω} :=
    fun k => (natFilt (X := X)).le k _ (hGk k)
  have hEσ : ∫⁻ ω, ENat.toENNReal (firstHit C ω) ∂μ ≠ ∞ := by
    change meanHitTime P C x₀ ≠ ∞; rwa [meanHitTime_of_notMem P hC hx₀C]
  -- the increments before `σ_C`
  set F : ℕ → (ℕ → X) → ℝ := fun k => {ω | (k : WithTop ℕ) < firstHit C ω}.indicator
    fun ω => V (ω (k + 1)) - V (ω k) with hFdef
  have hDm : ∀ k, Measurable fun ω : ℕ → X => V (ω (k + 1)) - V (ω k) := fun k =>
    (hV.comp (measurable_pi_apply (k + 1))).sub (hV.comp (measurable_pi_apply k))
  have hFm : ∀ k, Measurable (F k) := fun k => (hDm k).indicator (hG k)
  have hpairm : Measurable fun p : X × X => ‖V p.2 - V p.1‖ₑ :=
    ((hV.comp measurable_snd).sub (hV.comp measurable_fst)).enorm
  have hDnorm : ∀ k : ℕ, ∫⁻ ω in {ω | (k : WithTop ℕ) < firstHit C ω},
      ‖V (ω (k + 1)) - V (ω k)‖ₑ ∂μ ≤ B * μ {ω | (k : WithTop ℕ) < firstHit C ω} := fun k => by
    have hpair := setLIntegral_pair P (Measure.dirac x₀) (hGk k) hpairm
    rw [pathMeasure_dirac] at hpair
    rw [hpair, ← setLIntegral_const]
    exact setLIntegral_mono measurable_const fun ω _ => hinc (ω k)
  have hFnorm : ∀ k, ∫⁻ ω, ‖F k ω‖ₑ ∂μ ≤ B * μ {ω | (k : WithTop ℕ) < firstHit C ω} :=
    fun k => by
      simp_rw [hFdef, enorm_indicator_eq_indicator_enorm]
      rw [lintegral_indicator (hG k)]
      exact hDnorm k
  have hsum : ∑' k, ∫⁻ ω, ‖F k ω‖ₑ ∂μ ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hB hEσ) ?_
    calc ∑' k, ∫⁻ ω, ‖F k ω‖ₑ ∂μ ≤ ∑' k : ℕ, B * μ {ω | (k : WithTop ℕ) < firstHit C ω} :=
          ENNReal.tsum_le_tsum hFnorm
      _ = B * ∑' k : ℕ, ∫⁻ ω in {ω | (k : WithTop ℕ) < firstHit C ω}, 1 ∂μ := by
          rw [ENNReal.tsum_mul_left]; simp
      _ = B * ∫⁻ ω, ENat.toENNReal (firstHit C ω) ∂μ := by
          simp_rw [toENNReal_eq_sumBefore_one (firstHit C)]
          rw [lintegral_sumBefore μ hG fun _ => measurable_const]
  -- each increment has nonnegative mean, by (11.42)
  have hFpos : ∀ k, 0 ≤ ∫ ω, F k ω ∂μ := fun k => by
    have hint : IntegrableOn (fun ω : ℕ → X => V (ω (k + 1)) - V (ω k))
        {ω | (k : WithTop ℕ) < firstHit C ω} (pathMeasure P (Measure.dirac x₀)) := by
      rw [pathMeasure_dirac]
      exact ⟨(hDm k).aestronglyMeasurable, (hDnorm k).trans_lt
        (ENNReal.mul_lt_top hB.lt_top (measure_lt_top _ _))⟩
    rw [hFdef, integral_indicator (hG k), hμ, ← pathMeasure_dirac,
      setIntegral_pair P (Measure.dirac x₀) (hGk k)
        (h := fun p : X × X => V p.2 - V p.1)
        ((hV.comp measurable_snd).sub (hV.comp measurable_fst)) hint]
    refine setIntegral_nonneg (hG k) fun ω hω => ?_
    have hωk : ω k ∉ C := notMem_of_lt_firstHit hω
    have hVi := integrable_of_increments hV hB hinc (ω k)
    change 0 ≤ ∫ z, (V z - V (ω k)) ∂P (ω k)
    rw [integral_sub hVi (integrable_const _), integral_const, smul_eq_mul, probReal_univ,
      one_mul]
    linarith [hdrift (ω k) hωk]
  -- `σ_C < ∞` and `Φ₀ = x₀`, almost surely
  have hae_fin : ∀ᵐ ω ∂μ, firstHit C ω ≠ ⊤ := by
    filter_upwards [ae_lt_top (measurable_toENNReal_firstHit hC) hEσ] with ω hω
    intro h
    rw [h, show ENat.toENNReal (⊤ : WithTop ℕ) = ⊤ from ENat.toENNReal_top] at hω
    exact lt_irrefl _ hω
  have hae0 : ∀ᵐ ω ∂μ, V (ω 0) = V x₀ := by
    have hm : MeasurableSet {y | V y ≠ V x₀} := (measurableSet_singleton _).compl.preimage hV
    have h0 : μ {ω | ω 0 ∈ {y | V y ≠ V x₀}} = 0 := by
      rw [hμ, pathKernel_zero_mem P x₀ hm, indicator_of_notMem (by simp)]
    exact measure_mono_null (fun ω hω => hω) h0
  set Vs : (ℕ → X) → ℝ := fun ω => V (stoppedState (firstHit C) ω) with hVsdef
  have hVs : Measurable Vs := hV.comp (measurable_stoppedState hσ)
  -- pathwise, the increments telescope
  have hsupp : ∀ ω (t : ℕ), firstHit C ω = WithTop.some t → ∀ k ∉ Finset.range t, F k ω = 0 :=
    fun ω t ht k hk => by
      refine indicator_of_notMem (fun h => hk (Finset.mem_range.2 ?_)) _
      have h' : (k : WithTop ℕ) < WithTop.some t := ht ▸ h
      rw [Nat.cast_withTop] at h'
      exact WithTop.coe_lt_coe.1 h'
  have htel : ∀ᵐ ω ∂μ, ∑' k, F k ω = Vs ω - V x₀ := by
    filter_upwards [hae_fin, hae0] with ω hω h0
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hω
    rw [tsum_eq_sum (s := Finset.range t) (hsupp ω t ht.symm)]
    have hF : ∀ k ∈ Finset.range t, F k ω = V (ω (k + 1)) - V (ω k) := fun k hk => by
      refine indicator_of_mem (s := {ω | (k : WithTop ℕ) < firstHit C ω})
        (show (k : WithTop ℕ) < firstHit C ω by
        rw [← ht, Nat.cast_withTop]; exact WithTop.coe_lt_coe.2 (Finset.mem_range.1 hk)) _
    rw [Finset.sum_congr rfl hF, Finset.sum_range_sub (fun k => V (ω k)), ← h0, hVsdef]
    simp only [stoppedState_of_eq ht.symm]
  have hnorm : ∀ᵐ ω ∂μ, ‖∑' k, F k ω‖ₑ ≤ ∑' k, ‖F k ω‖ₑ := by
    filter_upwards [hae_fin] with ω hω
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hω
    rw [tsum_eq_sum (s := Finset.range t) (hsupp ω t ht.symm)]
    exact (enorm_sum_le _ _).trans (ENNReal.sum_le_tsum _)
  -- `V(x₀) − V(Φ_σ)` is integrable, has integral `−Σ E[F_k] ≤ 0`, and is positive a.s.
  have hDint : Integrable (fun ω => V x₀ - Vs ω) μ := by
    refine ⟨(measurable_const.sub hVs).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    calc ∫⁻ ω, ‖V x₀ - Vs ω‖ₑ ∂μ = ∫⁻ ω, ‖∑' k, F k ω‖ₑ ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [htel] with ω hω
          rw [hω, ← enorm_neg, neg_sub]
      _ ≤ ∫⁻ ω, ∑' k, ‖F k ω‖ₑ ∂μ := lintegral_mono_ae hnorm
      _ = ∑' k, ∫⁻ ω, ‖F k ω‖ₑ ∂μ := lintegral_tsum fun k => (hFm k).enorm.aemeasurable
      _ < ∞ := hsum.lt_top
  have hle : ∫ ω, (V x₀ - Vs ω) ∂μ ≤ 0 := by
    calc ∫ ω, (V x₀ - Vs ω) ∂μ = ∫ ω, -∑' k, F k ω ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [htel] with ω hω
          rw [hω, neg_sub]
      _ = -∑' k, ∫ ω, F k ω ∂μ := by
          rw [integral_neg, integral_tsum (fun k => (hFm k).aestronglyMeasurable) hsum]
      _ ≤ 0 := neg_nonpos.2 (tsum_nonneg hFpos)
  have hpos_ae : ∀ᵐ ω ∂μ, 0 < V x₀ - Vs ω := by
    filter_upwards [hae_fin] with ω hω
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hω
    have hmem : ω t ∈ C := mem_of_firstHit_eq ht.symm
    simp only [hVsdef, stoppedState_of_eq ht.symm, sub_pos]
    exact hx₀ _ hmem
  have hgt : 0 < ∫ ω, (V x₀ - Vs ω) ∂μ := by
    refine (integral_pos_iff_support_of_nonneg_ae (hpos_ae.mono fun ω h => h.le) hDint).2 ?_
    have hc : μ (Function.support fun ω => V x₀ - Vs ω)ᶜ = 0 :=
      ae_iff.1 (hpos_ae.mono fun ω h => h.ne')
    by_contra h0
    have h0' : μ (Function.support fun ω => V x₀ - Vs ω) = 0 := nonpos_iff_eq_zero.1 (not_lt.1 h0)
    have := measure_union_le (μ := μ) (Function.support fun ω => V x₀ - Vs ω)
      (Function.support fun ω => V x₀ - Vs ω)ᶜ
    rw [union_compl_self, measure_univ, h0', hc, add_zero] at this
    exact absurd this (by simp)
  linarith

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 11.5.2** (MT p. 279): for a `ψ`-irreducible chain, if `V ≥ 0` satisfies (11.42) off
a set `C ∈ B⁺(X)` and (11.43), and the set `C⁺` of states where `V` exceeds every value on `C` is
in `B⁺(X)`, then the chain is non-positive (null). -/
theorem theorem_11_5_2 [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ)
    {V : X → ℝ} (hV : Measurable V) {C : Set X} (hC : MeasurableSet C) (hψC : 0 < ψ C)
    (hdrift : ∀ x ∉ C, V x ≤ ∫ y, V y ∂P x) {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hinc : ∀ x, ∫⁻ y, ‖V y - V x‖ₑ ∂P x ≤ B) (hψCp : 0 < ψ {x | ∀ y ∈ C, V y < V x}) :
    IsNull P ψ := by
  refine ⟨hψ, fun hex => ?_⟩
  obtain ⟨S, -, hfull, -, Cs, hCs, hcov⟩ := (theorem_11_1_4 hψ).1 ⟨hψ, hex⟩
  set Cp := {x | ∀ y ∈ C, V y < V x}
  obtain ⟨n, hn⟩ : ∃ n, 0 < ψ (Cp ∩ Cs n) := by
    by_contra hc
    push Not at hc
    have h1 : Cp ⊆ (⋃ n, Cp ∩ Cs n) ∪ Sᶜ := fun x hx => by
      by_cases hS : x ∈ S
      · rw [← hcov] at hS
        obtain ⟨n, hn⟩ := mem_iUnion.1 hS
        exact Or.inl (mem_iUnion.2 ⟨n, hx, hn⟩)
      · exact Or.inr hS
    have h2 : ψ Cp = 0 := measure_mono_null h1 (measure_union_null
      (measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (hc n)) hfull)
    exact hψCp.ne' h2
  obtain ⟨x, hxp, hxn⟩ := nonempty_of_measure_ne_zero hn.ne'
  obtain ⟨M, hM, hbound⟩ := (hCs n).2 C hC hψC
  have hinf := theorem_11_5_1 hV hC hdrift hB hinc hxp
  exact hM (top_le_iff.1 (hinf ▸ hbound x hxn))

/-! ### Bounded mean increments cannot be dropped -/

/-- The transition law of the example on p. 279 (with `k(i) = 2i + 1 > 2i`): from `0` jump to
`j ≥ 1` with probability `2^{-j}`; from `i ≥ 1` jump to `0` or to `2i + 1` with probability
`½` each. -/
noncomputable def escMeas (n : ℕ) : Measure ℕ :=
  if n = 0 then Measure.sum fun j => (2⁻¹ : ℝ≥0∞) ^ (j + 1) • Measure.dirac (j + 1)
  else (2⁻¹ : ℝ≥0∞) • Measure.dirac 0 + (2⁻¹ : ℝ≥0∞) • Measure.dirac (2 * n + 1)

/-- The chain of the example on p. 279. -/
noncomputable def escKernel : Kernel ℕ ℕ := ⟨escMeas, measurable_of_countable _⟩

/-- `Σ_j 2^{-(j+1)} = 1`. -/
theorem tsum_inv_two_pow_succ_eq_one : ∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ (j + 1) = 1 := by
  simp_rw [pow_succ, ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two,
    inv_inv]
  exact ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top

/-- `∫ f dP(0, ·) = Σ_j 2^{-(j+1)} f(j + 1)`. -/
theorem lintegral_escKernel_zero (f : ℕ → ℝ≥0∞) :
    ∫⁻ i, f i ∂escKernel 0 = ∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ (j + 1) * f (j + 1) := by
  change ∫⁻ i, f i ∂escMeas 0 = _
  simp [escMeas, lintegral_sum_measure, lintegral_smul_measure]

/-- `∫ f dP(i, ·) = ½ f(0) + ½ f(2i + 1)` for `i ≥ 1`. -/
theorem lintegral_escKernel_pos {i : ℕ} (hi : i ≠ 0) (f : ℕ → ℝ≥0∞) :
    ∫⁻ j, f j ∂escKernel i = 2⁻¹ * f 0 + 2⁻¹ * f (2 * i + 1) := by
  change ∫⁻ j, f j ∂escMeas i = _
  simp [escMeas, hi, lintegral_add_measure, lintegral_smul_measure]

/-- The example on p. 279 is a transition kernel. -/
theorem isMarkovKernel_escKernel : IsMarkovKernel escKernel := by
  refine ⟨fun i => ⟨?_⟩⟩
  rw [← setLIntegral_one, Measure.restrict_univ]
  by_cases hi : i = 0
  · subst hi
    rw [lintegral_escKernel_zero]
    simpa using tsum_inv_two_pow_succ_eq_one
  · rw [lintegral_escKernel_pos hi]
    simp [ENNReal.inv_two_add_inv_two]

/-- **The bounded-increment condition (11.43) cannot be dropped in Theorem 11.5.2** (MT p. 279).
For the chain `escKernel` and `V(i) = i`: `ΔV(i) = ½ > 0` for every `i ≥ 1`, the sets `C = {0}`
and `C⁺ = {i ≥ 1}` are in `B⁺`, yet the chain is positive (`E_0[τ_0] ≤ 3`); (11.43) fails. -/
theorem theorem_11_5_2_counterexample :
    haveI := isMarkovKernel_escKernel
    ∃ ψ : Measure ℕ, IsMaximalIrreducibility escKernel ψ ∧ 0 < ψ {0} ∧
      (∀ i ∉ ({0} : Set ℕ), (i : ℝ) ≤ ∫ j, (j : ℝ) ∂escKernel i) ∧
      0 < ψ {i | ∀ j ∈ ({0} : Set ℕ), (j : ℝ) < i} ∧ IsPositive escKernel ψ ∧
      ¬ ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ i, ∫⁻ j, ‖(j : ℝ) - i‖ₑ ∂escKernel i ≤ B := by
  have := isMarkovKernel_escKernel
  have hm : ∀ A : Set ℕ, MeasurableSet A := fun A => measurableSet_of_countable A
  -- `δ₀` is an irreducibility measure
  have hirr : IsPhiIrreducible escKernel (Measure.dirac 0) := by
    refine isPhiIrreducible_of_pow_pos fun A hA hA0 x => ?_
    have h0A : (0 : ℕ) ∈ A := by
      by_contra h; rw [Measure.dirac_apply' _ hA, indicator_of_notMem h] at hA0
      exact lt_irrefl 0 hA0
    by_cases hx : x = 0
    · refine ⟨0, ?_⟩
      rw [pow_zero_apply, Measure.dirac_apply' _ hA, hx, indicator_of_mem h0A]
      exact one_pos
    · refine ⟨1, ?_⟩
      rw [pow_one, ← lintegral_indicator_one hA, lintegral_escKernel_pos hx,
        indicator_of_mem h0A]
      exact lt_of_lt_of_le (by simp) le_self_add
  set ψ := maxIrrMeasure escKernel (Measure.dirac 0)
  have hψ : IsMaximalIrreducibility escKernel ψ :=
    isMaximalIrreducibility_maxIrrMeasure _ hirr (by simp)
  have hψ0 : 0 < ψ {0} := (hψ.pos_iff_hitProb_pos (hm _)).2 fun x => hirr _ (hm _) (by simp) x
  -- `E_j[σ_0] ≤ 2`, so `E_0[τ_0] ≤ 3`
  set W : ℕ → ℝ≥0∞ := fun i => if i = 0 then 0 else 2 with hWdef
  have hW : ∀ x ∉ ({0} : Set ℕ), ∫⁻ y, W y ∂escKernel x + 1 ≤ W x := fun x hx => by
    have hx' : x ≠ 0 := by simpa using hx
    rw [lintegral_escKernel_pos hx']
    simp [hWdef, hx', ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_add_one_eq_two]
  have hmin := (theorem_11_3_5_iii escKernel (hm {0})).2 W (measurable_of_countable _) hW
  have hE0 : meanReturnTime escKernel {0} 0 ≠ ∞ := by
    rw [meanReturnTime_eq_one_add _ (hm _)]
    refine ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ne_top_of_le_ne_top
      (b := ∫⁻ y, W y ∂escKernel 0) ?_ (lintegral_mono hmin)⟩
    rw [lintegral_escKernel_zero]
    simp only [hWdef, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    rw [ENNReal.tsum_mul_right, tsum_inv_two_pow_succ_eq_one, one_mul]
    exact ENNReal.ofNat_ne_top
  have hatom : IsAccessibleAtom escKernel ψ {0} := ⟨isAtom_singleton _ 0, hψ, hψ0⟩
  have hpos := (theorem_10_2_2 hatom (mem_singleton 0)).1.2 hE0
  refine ⟨ψ, hψ, hψ0, fun i hi => ?_, ?_, hpos, ?_⟩
  · have hi' : i ≠ 0 := by simpa using hi
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun j => Nat.cast_nonneg j)
      (measurable_of_countable _).aestronglyMeasurable, lintegral_escKernel_pos hi']
    simp only [CharP.cast_eq_zero, ENNReal.ofReal_zero, mul_zero, zero_add]
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity)]
    push_cast
    norm_num
    linarith
  · have hset : {i : ℕ | ∀ j ∈ ({0} : Set ℕ), (j : ℝ) < i} = {0}ᶜ := by
      ext i; simp [Nat.pos_iff_ne_zero]
    rw [hset]
    refine (hψ.pos_iff_hitProb_pos (hm _)).2 fun x => (hitProb_pos_iff _ (hm _) x).2 ⟨0, ?_⟩
    rw [zero_add, pow_one, ← lintegral_indicator_one (hm _)]
    by_cases hx : x = 0
    · subst hx
      rw [lintegral_escKernel_zero]
      simp only [mem_compl_iff, mem_singleton_iff, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        not_false_eq_true, indicator_of_mem, Pi.one_apply, mul_one]
      rw [tsum_inv_two_pow_succ_eq_one]; exact one_pos
    · rw [lintegral_escKernel_pos hx]
      simp only [mem_compl_iff, mem_singleton_iff, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        not_false_eq_true, indicator_of_mem, Pi.one_apply, mul_one]
      exact lt_of_lt_of_le (by simp) le_add_self
  · rintro ⟨B, hB, hbound⟩
    obtain ⟨i, hi⟩ := ENNReal.exists_nat_gt (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hB :
      (2 : ℝ≥0∞) * B ≠ ∞)
    have hi0 : i ≠ 0 := by rintro rfl; simp at hi
    have h1 := hbound i
    rw [lintegral_escKernel_pos hi0] at h1
    have h2 : (2⁻¹ : ℝ≥0∞) * i ≤ B := by
      refine le_trans ?_ (le_self_add.trans h1)
      simp [enorm_neg]
    have h3 : (i : ℝ≥0∞) ≤ 2 * B := by
      calc (i : ℝ≥0∞) = 2 * (2⁻¹ * i) := by
            rw [← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
        _ ≤ 2 * B := mul_le_mul' le_rfl h2
    exact absurd hi (not_lt.2 h3)

end MeynTweedie.DriftRegularity
