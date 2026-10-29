/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.TChains
import Epilogue.FellerModels
import Epilogue.SpreadOut
import Epilogue.LinearIrreducibility

/-!
# Continuous components for specific models (MT §6.3)

Meyn and Tweedie, §6.3, pp. 134–139. Lemma 6.3.4 and Proposition 6.3.5 are in
`LinearTChains`.

* `IsSmall.isPetite`: a small set is petite (Proposition 5.5.3).
* **Proposition 6.3.1** (`proposition_6_3_1`, p. 134): random walk on a half line with
  `Γ(−∞, 0) > 0` is a `δ₀`-irreducible T-chain (all compact sets are small, Theorem 6.2.5 (i)).
* `isProbabilityMeasure_convPow`, `randomWalkKernel_pow_apply'`: `Pⁿ(y, A) = Γ^{n∗}(A − y)`.
* **Proposition 6.3.2** (`proposition_6_3_2`, p. 134): the unrestricted random walk is a T-chain
  iff it is spread out. For "spread out ⇒ T-chain" the component is `η μ_Leb|_E(A − x)`, from
  the Lebesgue minorant of `Γ^{n∗}` (`exists_lebesgue_minorant`); for the converse the book's
  argument (6.9)–(6.10) is formalised with `lintegral_translate_volume`.
* `pi_mono_fin`: `μ ≤ ν` implies `μ^{⊗k} ≤ ν^{⊗k}`.
* **Proposition 6.3.3** (`proposition_6_3_3`, p. 136): a controllable LSS(F, G) model whose noise
  is not singular with respect to Lebesgue measure (LSS4) has an everywhere non-trivial
  continuous component for its `n`-skeleton, so it is a T-chain. The book proves the case of
  scalar noise and says the general case needs much more notation; the proof here covers every
  noise dimension `p`: the component is the translate by `Fⁿx` of the law of `Cₙ(W₁, …, Wₙ)` for
  the absolutely continuous part of `Γ`, which is absolutely continuous because `Cₙ` is onto.
* `arKernel_isTChain` (p. 137): the AR(k) model with noise not singular with respect to Lebesgue
  measure is a T-chain (its state space realization is controllable, Proposition 4.4.2).
* `randomWalk_rational_weakFeller_not_irreducible` (p. 130): a random walk with increments on
  the rationals is weak Feller but irreducible for no nonzero measure.
* **Proposition 6.3.6** (`proposition_6_3_6`, p. 139): under (SETAR2) the SETAR model is a
  `μ_Leb`-irreducible T-chain, Lebesgue measure is maximal, and every compact set is small.

**Hypotheses.** (SETAR2) is stated as `Γ_j ≪ μ_Leb` and `μ_Leb ≪ Γ_j` (a density positive almost
everywhere); the thresholds need not be ordered for the result.

**Not formalised.** The storage-model remark after Proposition 6.3.1 (the model is not
constructed here), the remark after Proposition 6.3.3 on ARMA models (only the AR(k) case is
formalised) and on controllable subspaces, the Gaussian strong Feller remark of §6.3.3, and the
weakened support conditions after Proposition 6.3.6 (informal).

**Corrections.** None. The proof of Proposition 6.3.6 differs from the book's (see its
docstring).
-/

namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal Matrix

/-- A small set is petite. -/
theorem IsSmall.isPetite {X : Type*} [MeasurableSpace X] {P : Kernel X X} {C : Set X}
    (h : IsSmall P C) : IsPetite P C := by
  obtain ⟨m, ν, h⟩ := h
  exact ⟨_, _, proposition_5_5_3 h⟩

/-! ### Random walks (§6.3.1) -/

/-- **Proposition 6.3.1** (MT p. 134): random walk on a half line with `Γ(−∞, 0) > 0` is a
`δ₀`-irreducible T-chain. -/
theorem proposition_6_3_1 (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (h : 0 < Γ (Iio 0)) :
    ∃ _ : IsMarkovKernel (halfLineWalkKernel Γ),
      IsPhiIrreducible (halfLineWalkKernel Γ) (Measure.dirac 0) ∧
        IsTChain (halfLineWalkKernel Γ) := by
  obtain ⟨hM, hirr⟩ := proposition_4_3_1 Γ
  exact ⟨hM, hirr.2 h, theorem_6_2_5_i fun K hK =>
    (halfLine_isSmall_of_isCompact Γ h hK).isPetite⟩

/-- The convolution power `Γ^{n∗}` of a probability measure is a probability measure. -/
theorem isProbabilityMeasure_convPow (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (n : ℕ) :
    IsProbabilityMeasure (convPow Γ n) := by
  unfold convPow; infer_instance

/-- `Pⁿ(y, A) = Γ^{n∗}{w : y + w ∈ A}` for random walk. -/
theorem randomWalkKernel_pow_apply' (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (n : ℕ) (y : ℝ)
    {A : Set ℝ} (hA : MeasurableSet A) :
    (randomWalkKernel Γ ^ n) y A = convPow Γ n {w | y + w ∈ A} := by
  rw [randomWalkKernel_pow_apply, Measure.map_apply (measurable_const_add y) hA]
  rfl

/-- **Proposition 6.3.2** (MT p. 134): the unrestricted random walk on `ℝ` is a T-chain iff it
is spread out. -/
theorem proposition_6_3_2 (Γ : Measure ℝ) [IsProbabilityMeasure Γ] :
    IsTChain (randomWalkKernel Γ) ↔ IsSpreadOut Γ := by
  have hM := isMarkovKernel_randomWalkKernel Γ
  constructor
  · rintro ⟨a, T, ha, hT, hpos⟩
    by_contra hns
    have hsing : ∀ n, convPow Γ n ⟂ₘ (volume : Measure ℝ) := by
      intro n
      by_cases hn : 1 ≤ n
      · by_contra h
        exact hns ⟨n, hn, h⟩
      · have hn0 : n = 0 := by omega
        subst hn0
        refine ⟨{0}ᶜ, (measurableSet_singleton 0).compl, ?_, by simp⟩
        rw [convPow, Measure.map_apply (measurable_sum_fin 0) (measurableSet_singleton 0).compl]
        have : (fun u : Fin 0 → ℝ => ∑ i, u i) ⁻¹' {0}ᶜ = ∅ := by ext u; simp
        rw [this, measure_empty]
    choose s hs hΓs hvs using fun n => hsing n
    set A : Set ℝ := ⋃ n, (s n)ᶜ
    have hAm : MeasurableSet A := MeasurableSet.iUnion fun n => (hs n).compl
    have hvA : volume A = 0 := measure_iUnion_null hvs
    have hΓA : ∀ n, convPow Γ n Aᶜ = 0 := fun n =>
      measure_mono_null (fun w hw => by
        simp only [A, compl_iUnion, mem_iInter, compl_compl] at hw; exact hw n) (hΓs n)
    have hK0 : sampledKernel (randomWalkKernel Γ) a 0 Aᶜ = 0 := by
      rw [sampledKernel_apply _ a 0 hAm.compl]
      refine ENNReal.tsum_eq_zero.2 fun n => ?_
      rw [randomWalkKernel_pow_apply' Γ n 0 hAm.compl]
      simp only [zero_add, ofPred_mem_eq, hΓA n, mul_zero]
    have hT0 : T 0 A = T 0 univ := by
      have h1 := measure_add_measure_compl (μ := T 0) hAm
      have h2 : T 0 Aᶜ = 0 := nonpos_iff_eq_zero.1 ((hT.2.1 0 _).trans hK0.le)
      rw [h2, add_zero] at h1
      exact h1
    have hδ : 0 < T 0 A := hT0 ▸ hpos 0
    have hδfin : T 0 A ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top
      ((measure_mono (subset_univ _)).trans (hT.1 0))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
      (hT.2.2 A hAm 0 (T 0 A / 2) (ENNReal.half_lt_self hδ.ne' hδfin))
    -- integrate `K_a(·, A)` against Lebesgue measure
    have hint : ∫⁻ y, sampledKernel (randomWalkKernel Γ) a y A ∂volume = 0 := by
      simp_rw [sampledKernel_apply _ a _ hAm]
      rw [lintegral_tsum fun n => ((Kernel.measurable_coe _ hAm).const_mul _).aemeasurable]
      refine ENNReal.tsum_eq_zero.2 fun n => ?_
      have := isProbabilityMeasure_convPow Γ n
      rw [lintegral_const_mul _ (Kernel.measurable_coe _ hAm)]
      simp_rw [randomWalkKernel_pow_apply' Γ n _ hAm]
      rw [lintegral_translate_volume (convPow Γ n) hAm, hvA, mul_zero]
    have hpos' : 0 < ∫⁻ y, sampledKernel (randomWalkKernel Γ) a y A ∂volume := by
      calc (0 : ℝ≥0∞) < T 0 A / 2 * volume (Metric.ball (0 : ℝ) ε) :=
            ENNReal.mul_pos (ENNReal.half_pos hδ.ne').ne' (Metric.measure_ball_pos _ _ hε).ne'
        _ = ∫⁻ _ in Metric.ball (0 : ℝ) ε, T 0 A / 2 ∂volume := by rw [setLIntegral_const]
        _ ≤ ∫⁻ y in Metric.ball (0 : ℝ) ε, sampledKernel (randomWalkKernel Γ) a y A ∂volume :=
            setLIntegral_mono (Kernel.measurable_coe _ hAm) fun y hy =>
              (hball hy).le.trans (hT.2.1 y A)
        _ ≤ _ := setLIntegral_le_lintegral _ _
    exact absurd hint hpos'.ne'
  · rintro ⟨n, hn, hns⟩
    have := isProbabilityMeasure_convPow Γ n
    obtain ⟨E, hEm, hE0, hEfin, η, hη, hle⟩ := exists_lebesgue_minorant hns
    set ν : Measure ℝ := η • volume.restrict E
    have hνfin : ν univ ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top (convPow Γ n) univ) (hle univ)
    have hνf : IsFiniteMeasure ν := ⟨hνfin.lt_top⟩
    have hνac : ν ≪ volume := (Measure.smul_absolutelyContinuous).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
    have hTle : ∀ x, randomWalkKernel ν x ≤ sampledKernel (randomWalkKernel Γ) (diracDist n) x :=
      fun x => by
        rw [sampledKernel_diracDist, randomWalkKernel_pow_apply, randomWalkKernel_apply]
        exact Measure.map_mono hle (measurable_const_add x)
    refine ⟨diracDist n, randomWalkKernel ν, isSamplingDist_diracDist n,
      ⟨fun x => ?_, hTle, fun A hA => ?_⟩, fun x => ?_⟩
    · have := isMarkovKernel_sampledKernel (randomWalkKernel Γ) (isSamplingDist_diracDist n)
      exact (hTle x univ).trans prob_le_one
    · have : (fun x => randomWalkKernel ν x A) = fun x => ν {w | x + w ∈ A} := by
        ext x; exact randomWalkKernel_apply' ν x hA
      rw [this]
      exact lsc_translate volume hνac hA
    · rw [randomWalkKernel_apply' ν x MeasurableSet.univ]
      simp only [mem_univ, ofPred_true, ν, Measure.smul_apply, Measure.restrict_apply_univ,
        smul_eq_mul]
      exact ENNReal.mul_pos hη.ne' hE0.ne'

/-! ### Linear models (§6.3.2) -/

/-- `μ ≤ ν` implies `μ^{⊗k} ≤ ν^{⊗k}` on `Fin k → α`. -/
theorem pi_mono_fin {α : Type*} [MeasurableSpace α] {μ ν : Measure α} [SigmaFinite μ]
    [SigmaFinite ν] (h : μ ≤ ν) (k : ℕ) :
    Measure.pi (fun _ : Fin k => μ) ≤ Measure.pi (fun _ : Fin k => ν) := by
  induction k with
  | zero => rw [Measure.pi_of_empty, Measure.pi_of_empty]
  | succ k ih =>
    have e1 := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => μ) 0
    have e2 := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => ν) 0
    rw [← (e1.symm _).map_eq, ← (e2.symm _).map_eq]
    exact Measure.map_mono (Measure.prod_mono h ih) (MeasurableEquiv.measurable _)

variable {n p : ℕ}

/-- **Proposition 6.3.3** (MT p. 136): if the linear control model LCM(F, G) on `ℝⁿ` is
controllable (LCM3) and the disturbance law is not singular with respect to Lebesgue measure
(LSS4), then the `n`-skeleton of LSS(F, G) has an everywhere non-trivial continuous component, so
LSS(F, G) is a T-chain. The book proves the scalar-noise case; this is the general case `W ∈ ℝᵖ`.
The component is `T(x, A) = ν{v : Fⁿx + v ∈ A}`, where `ν` is the law of `Cₙ(W₁, …, Wₙ)` with the
`Wᵢ` drawn from the absolutely continuous part of `Γ`. -/
theorem proposition_6_3_3 (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    {F : Matrix (Fin n) (Fin n) ℝ} {G : Matrix (Fin n) (Fin p) ℝ} (hc : IsControllable F G)
    (hns : ¬ Γ ⟂ₘ volume) :
    (∃ T : Kernel (Fin n → ℝ) (Fin n → ℝ),
      IsContinuousComponent (lssMatrixKernel Γ F G) (diracDist n) T ∧ ∀ x, 0 < T x univ) ∧
      IsTChain (lssMatrixKernel Γ F G) := by
  have hM := isMarkovKernel_lssMatrixKernel Γ F G
  set Γac : Measure (Fin p → ℝ) := volume.withDensity (Γ.rnDeriv volume)
  have hle : Γac ≤ Γ := Measure.withDensity_rnDeriv_le Γ volume
  have hΓac0 : Γac ≠ 0 := fun h0 => hns ((Measure.withDensity_rnDeriv_eq_zero Γ volume).1 h0)
  have hfin : IsFiniteMeasure Γac := isFiniteMeasure_of_le Γ hle
  have hac : Γac ≪ volume := withDensity_absolutelyContinuous _ _
  set ν := ctrbLaw Γac F G n
  have hνle : ν ≤ ctrbLaw Γ F G n :=
    Measure.map_mono (pi_mono_fin hle n) (measurable_ctrbMap F G n)
  have hνfin : IsFiniteMeasure ν := by unfold ν ctrbLaw; infer_instance
  have hνac : ν ≪ volume := by
    have hL : Function.Surjective (ctrbMap F G n) :=
      LinearMap.range_eq_top.1 (range_ctrbMap_eq_top hc le_rfl)
    refine Measure.AbsolutelyContinuous.mk fun S hS h0 => ?_
    have key := ae_comp_linearMap_mem_iff (ctrbMap F G n)
      (volume : Measure (Fin n → Fin p → ℝ)) (volume : Measure (Fin n → ℝ)) hL hS.compl
    have hpre : volume (ctrbMap F G n ⁻¹' S) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem] at h0 ⊢
      simpa using key.2 (by simpa using h0)
    have hpi : Measure.pi (fun _ : Fin n => Γac) ≪ volume := by
      rw [volume_pi]; exact pi_absolutelyContinuous hac n
    rw [show ν = (Measure.pi fun _ : Fin n => Γac).map (ctrbMap F G n) from rfl,
      Measure.map_apply (measurable_ctrbMap F G n) hS]
    exact hpi hpre
  have hνpos : 0 < ν univ := by
    rw [show ν = (Measure.pi fun _ : Fin n => Γac).map (ctrbMap F G n) from rfl,
      Measure.map_apply (measurable_ctrbMap F G n) MeasurableSet.univ,
      preimage_univ, Measure.pi_univ]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact ENNReal.pow_pos (pos_iff_ne_zero.2 fun h => hΓac0 (Measure.measure_univ_eq_zero.1 h)) n
  have hstep : Measurable fun q : (Fin n → ℝ) × (Fin n → ℝ) => (F ^ n) *ᵥ q.1 + q.2 :=
    ((Continuous.matrix_mulVec continuous_const continuous_fst).add continuous_snd).measurable
  set T := recursionKernel ν fun q : (Fin n → ℝ) × (Fin n → ℝ) => (F ^ n) *ᵥ q.1 + q.2
  have hTle : ∀ x, T x ≤ sampledKernel (lssMatrixKernel Γ F G) (diracDist n) x := fun x => by
    rw [sampledKernel_diracDist, lss_pow_eq, recursionKernel_apply ν hstep x]
    exact Measure.map_mono hνle (hstep.comp measurable_prodMk_left)
  have hT : IsContinuousComponent (lssMatrixKernel Γ F G) (diracDist n) T := by
    refine ⟨fun x => ?_, hTle, fun A hA => ?_⟩
    · have := isMarkovKernel_sampledKernel (lssMatrixKernel Γ F G) (isSamplingDist_diracDist n)
      exact (hTle x univ).trans prob_le_one
    · have : (fun x => T x A) = (fun t => ν {w | t + w ∈ A}) ∘ fun x => (F ^ n) *ᵥ x := by
        ext x; exact recursionKernel_apply' ν hstep x hA
      rw [this]
      exact (lsc_translate volume hνac hA).comp
        (Continuous.matrix_mulVec continuous_const continuous_id)
  have hTpos : ∀ x, 0 < T x univ := fun x => by
    rw [recursionKernel_apply' ν hstep x MeasurableSet.univ]
    simpa using hνpos
  exact ⟨⟨T, hT, hTpos⟩, diracDist n, T, isSamplingDist_diracDist n, hT, hTpos⟩

/-! ### The SETAR model (§6.3.4) -/

/-- **Proposition 6.3.6** (MT p. 139): under (SETAR2), every regime noise `Γ_j` equivalent to
Lebesgue measure (a density positive on the whole line), the SETAR model is a
`μ_Leb`-irreducible T-chain; Lebesgue measure is a maximal irreducibility measure, and every
compact set is small. The proof here does not glue local components with the book's minimum of
measures: since `x ↦ Γ_j{w : φ(j) + θ(j)x + w ∈ C}` is lower semicontinuous and positive in every
regime, a compact set reaches a small set `C ∈ B⁺(X)` uniformly in one step, so it is small, and
Theorem 6.2.5 (i) applies. -/
theorem proposition_6_3_6 {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ)
    [∀ j, IsProbabilityMeasure (Γ j)] (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ)
    (h1 : ∀ j, Γ j ≪ volume) (h2 : ∀ j, volume ≪ Γ j) :
    ∃ _ : IsMarkovKernel (setarKernel Γ φ θ r),
      IsMaximalIrreducibility (setarKernel Γ φ θ r) volume ∧
      (∀ K : Set ℝ, IsCompact K → IsSmall (setarKernel Γ φ θ r) K) ∧
      IsTChain (setarKernel Γ φ θ r) := by
  have hM := isMarkovKernel_setarKernel Γ φ θ r
  set P := setarKernel Γ φ θ r
  have hstep : ∀ x {A : Set ℝ}, MeasurableSet A → 0 < volume A → 0 < P x A :=
    fun x A hA hpos => by
    rw [setarKernel_apply' Γ φ θ r x hA]
    refine pos_iff_ne_zero.2 fun h0 => hpos.ne' ?_
    have := h2 (setarRegime r x) h0
    rwa [show {w : ℝ | φ (setarRegime r x) + θ (setarRegime r x) * x + w ∈ A} =
      (fun w => (φ (setarRegime r x) + θ (setarRegime r x) * x) + w) ⁻¹' A from rfl,
      measure_preimage_add] at this
  have hnull : ∀ x {A : Set ℝ}, MeasurableSet A → volume A = 0 → P x A = 0 :=
    fun x A hA h0 => by
    rw [setarKernel_apply' Γ φ θ r x hA]
    refine h1 _ ?_
    rw [show {w : ℝ | φ (setarRegime r x) + θ (setarRegime r x) * x + w ∈ A} =
      (fun w => (φ (setarRegime r x) + θ (setarRegime r x) * x) + w) ⁻¹' A from rfl,
      measure_preimage_add]
    exact h0
  have hirr : IsPhiIrreducible P volume := fun A hA hpos x =>
    (hitProb_pos_iff P hA x).2 ⟨0, by rw [zero_add, pow_one]; exact hstep x hA hpos⟩
  have hmax : IsMaximalIrreducibility P volume := by
    refine ⟨NeZero.ne _, hirr, fun ψ hψ => Measure.AbsolutelyContinuous.mk fun A hA h0 => ?_⟩
    by_contra hpos
    have hpow : ∀ k x, (P ^ (k + 1)) x A = 0 := fun k x => by
      rw [pow_succ_apply' P k x hA]
      simp_rw [hnull _ hA h0]
      exact lintegral_zero
    obtain ⟨k, hk⟩ := (hitProb_pos_iff P hA 0).1 (hψ A hA (pos_iff_ne_zero.2 hpos) 0)
    exact hk.ne' (hpow k 0)
  obtain ⟨C, -, mC, νC, hC, hvC, -⟩ := theorem_5_2_2 P hmax MeasurableSet.univ (by simp)
  have hsmall : ∀ K : Set ℝ, IsCompact K → IsSmall P K := by
    intro K hK
    set g : Fin (m + 1) → ℝ → ℝ≥0∞ := fun j x => Γ j {w | (φ j + θ j * x) + w ∈ C}
    have hg : ∀ j, LowerSemicontinuous (g j) := fun j =>
      (lsc_translate volume (h1 j) hC.1).comp (continuous_const.add (continuous_const.mul
        continuous_id))
    have hgpos : ∀ j x, 0 < g j x := fun j x => by
      refine pos_iff_ne_zero.2 fun h0 => hvC.ne' ?_
      have := h2 j h0
      rwa [show {w : ℝ | (φ j + θ j * x) + w ∈ C} = (fun w => (φ j + θ j * x) + w) ⁻¹' C
        from rfl, measure_preimage_add] at this
    have hPg : ∀ x, P x C = g (setarRegime r x) x := fun x => by
      rw [setarKernel_apply' Γ φ θ r x hC.1]
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · rw [hKe]
      exact ⟨mC, νC, hC.mono MeasurableSet.empty (empty_subset _)⟩
    choose xm _ hxm using fun j => LowerSemicontinuousOn.exists_isMinOn hKne hK
      ((hg j).lowerSemicontinuousOn K)
    set δ := Finset.univ.inf fun j => g j (xm j)
    have hδ : 0 < δ := (Finset.lt_inf_iff ENNReal.zero_lt_top).2 fun j _ => hgpos j (xm j)
    have hδle : ∀ x ∈ K, δ ≤ (P ^ 1) x C := fun x hx => by
      rw [pow_one, hPg]
      exact (Finset.inf_le (Finset.mem_univ _)).trans
        (isMinOn_iff.1 (hxm (setarRegime r x)) x hx)
    exact ⟨1 + mC, _, proposition_5_2_4_i P hC hK.measurableSet hδ hδle⟩
  exact ⟨hM, hmax, hsmall, theorem_6_2_5_i fun K hK => (hsmall K hK).isPetite⟩

/-! ### Remarks: AR(k) models and rational random walks -/

/-- MT p. 137: the AR(k) model in its state space form is a T-chain whenever the noise law is
not singular with respect to Lebesgue measure, since its realization is controllable
(Proposition 4.4.2) and Proposition 6.3.3 applies. -/
theorem arKernel_isTChain (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {k : ℕ} (α : Fin k → ℝ)
    (hns : ¬ Γ ⟂ₘ volume) : IsTChain (arKernel Γ α) := by
  rw [arKernel_eq_lssMatrixKernel]
  have hg : Measurable fun w : ℝ => (fun _ : Fin 1 => w) :=
    measurable_pi_iff.mpr fun _ => measurable_id
  refine (proposition_6_3_3 _ (proposition_4_4_2 α).2 fun h => hns ?_).2
  obtain ⟨s, hs, hΓs, hvs⟩ := h
  refine ⟨(fun w : ℝ => (fun _ : Fin 1 => w)) ⁻¹' s, hg hs, ?_, ?_⟩
  · rwa [Measure.map_apply hg hs] at hΓs
  · have hmp := (volume_preserving_funUnique (Fin 1) ℝ).symm
    have : (fun w : ℝ => (fun _ : Fin 1 => w)) = (MeasurableEquiv.funUnique (Fin 1) ℝ).symm := by
      ext w i; simp [MeasurableEquiv.funUnique]
    rw [← preimage_compl, this, hmp.measure_preimage hs.compl.nullMeasurableSet]
    exact hvs

/-- MT p. 130: the weak Feller property does not connect open sets with irreducibility. A
random walk whose increments are concentrated on the rationals is weak Feller but is
`φ`-irreducible for no nonzero `φ`. -/
theorem randomWalk_rational_weakFeller_not_irreducible (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hΓ : Γ (range (Rat.cast : ℚ → ℝ))ᶜ = 0) :
    IsWeakFeller (randomWalkKernel Γ) ∧
      (haveI := isMarkovKernel_randomWalkKernel Γ
        ∀ φ : Measure ℝ, IsPhiIrreducible (randomWalkKernel Γ) φ → φ = 0) := by
  obtain ⟨_, -, -, h, -⟩ := randomWalk_rational Γ hΓ
  exact ⟨(proposition_6_1_3 Γ).1, h⟩

end MeynTweedie.Epilogue
