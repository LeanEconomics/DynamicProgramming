/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import VUniformErgodicity.Accessibility
import VUniformErgodicity.LinearControllability
import Mathlib.MeasureTheory.Measure.Haar.Disintegration
import Mathlib.MeasureTheory.Measure.ContinuousPreimage
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# ψ-irreducible linear state space models (MT §4.4.3)

Meyn and Tweedie, §4.4.3, pp. 92–93: the linear state space model LSS(F, G),
`Xₖ₊₁ = F Xₖ + G Wₖ₊₁` on `ℝⁿ` (`lssMatrixKernel Γ F G`), with a disturbance law `Γ` on `ℝᵖ`.

The book assumes Gaussian noise (LSS3) and argues through the Gaussian density (4.18) of
`Pᵏ(x, ·)`. The proof here needs only that `Γ` is *equivalent* to Lebesgue measure (it has an
everywhere positive density): `Pᵏ(x, ·)` is the image of `Γ^{⊗k}` under the affine map
`u ↦ Fᵏx + C_k u`, and for `k ≥ n` the linear part is onto by controllability, so
`Pᵏ(x, ·)` is equivalent to Lebesgue measure (Mathlib's disintegration of Haar measure along
a surjective linear map).

* `pi_absolutelyContinuous`: `μ ≪ ν` implies `μ^{⊗k} ≪ ν^{⊗k}`.
* `ctrbLaw Γ F G k`: the law of `C_k (W₁, …, W_k)`; `lss_pow_eq`: `Pᵏ(x, ·)` is its translate
  by `Fᵏ x`; `ctrbLaw_equiv`, `lss_pow_equiv`: if `C_k` is onto, these laws are equivalent to
  Lebesgue measure.
* **Proposition 4.4.3** (`proposition_4_4_3`, p. 92), for a controllable pair and noise
  equivalent to Lebesgue measure: (i) the chain is `φ`-irreducible for every `φ ≪ μ_Leb`
  (`lss_isPhiIrreducible`); (ii) Lebesgue measure is a maximal irreducibility measure
  (`lss_isMaximalIrreducibility`); (iii) `A ⇝ B` for every compact `A` and every `B` with
  `μ_Leb(B) > 0` (`lss_unifAccessible`, via the lower semicontinuity `lss_lowerSemicontinuous`
  of `t ↦ ν(B − t)`).
* `proposition_4_4_3_gaussian`: the Gaussian case (LSS3), `W ∼ N(0, I)`.
* `ctrbSubspace_isAbsorbing` (p. 93): for any disturbance law, the range `X₀` of `C_n` is
  absorbing.

**Corrections.**
* The density (4.18) has the wrong normalising constant: it should be
  `(2π)^{−n/2} |Σ_k|^{−1/2}`, not `(2π|Σ_k|)^{−k/2}`. For `n = 1`, `k = 2`, `F = 0`, `G = 1`
  (so `Σ₂ = 1`) the book's function integrates to `(2π)^{−1/2} ≠ 1`, while the corrected one
  integrates to `1` (`density_4_18_counterexample`).

The moment formulas (4.15)–(4.16) and the Gaussian form of `Pᵏ(x, ·)` are not formalised: the
proof above does not use them. Their linear-algebra content, `Σ_k = C_k C_kᵀ` and
`rank Σ_k = rank C_k`, is in `LinearControllability`. The claim that the chain restricted to
`X₀` is again a controllable LSS model, and hence `μ_Leb`-irreducible on `X₀`, is not
formalised (it needs coordinates on the subspace).
-/

namespace MeynTweedie.VUniformErgodicity

open MeasureTheory ProbabilityTheory Set Filter Topology Matrix
open scoped ENNReal Matrix symmDiff

/-- `μ ≪ ν` implies `μ^{⊗k} ≪ ν^{⊗k}` on `Fin k → α`. -/
theorem pi_absolutelyContinuous {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
    [SigmaFinite μ] [SigmaFinite ν] (h : μ ≪ ν) (k : ℕ) :
    Measure.pi (fun _ : Fin k => μ) ≪ Measure.pi (fun _ : Fin k => ν) := by
  induction k with
  | zero => rw [Measure.pi_of_empty, Measure.pi_of_empty]
  | succ k ih =>
    have e1 := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => μ) 0
    have e2 := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => ν) 0
    rw [← (e1.symm _).map_eq, ← (e2.symm _).map_eq]
    exact (h.prod ih).map (MeasurableEquiv.measurable _)

variable {n p : ℕ}

/-- `C_k` is measurable. -/
theorem measurable_ctrbMap (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (k : ℕ) : Measurable (ctrbMap F G k) :=
  (ctrbMap F G k).continuous_of_finiteDimensional.measurable

/-- The law of `C_k (W₁, …, W_k)` for i.i.d. `Wᵢ ∼ Γ`. -/
noncomputable def ctrbLaw (Γ : Measure (Fin p → ℝ)) (F : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) : Measure (Fin n → ℝ) :=
  (Measure.pi fun _ : Fin k => Γ).map (ctrbMap F G k)

/-- `Pᵏ(x, ·)` is the law of `C_k (W₁, …, W_k)` translated by `Fᵏ x` ((4.14)). -/
theorem lss_pow_eq (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) (x : Fin n → ℝ) :
    (lssMatrixKernel Γ F G ^ k) x = (ctrbLaw Γ F G k).map fun y => (F ^ k) *ᵥ x + y := by
  rw [lssMatrixKernel_pow_apply, ctrbLaw,
    Measure.map_map (measurable_const_add _) (measurable_ctrbMap F G k)]
  congr 1
  funext u
  simp [ctrbMap_apply]

/-- If `C_k` is onto and `Γ` is equivalent to Lebesgue measure, the law of
`C_k (W₁, …, W_k)` is equivalent to Lebesgue measure. -/
theorem ctrbLaw_equiv (Γ : Measure (Fin p → ℝ)) [SigmaFinite Γ] (F : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin n) (Fin p) ℝ) {k : ℕ} (hsurj : LinearMap.range (ctrbMap F G k) = ⊤)
    (h1 : Γ ≪ volume) (h2 : volume ≪ Γ) :
    ctrbLaw Γ F G k ≪ volume ∧ volume ≪ ctrbLaw Γ F G k := by
  have hL : Function.Surjective (ctrbMap F G k) := LinearMap.range_eq_top.1 hsurj
  have hmL := measurable_ctrbMap F G k
  have key : ∀ S : Set (Fin n → ℝ), MeasurableSet S →
      (volume (ctrbMap F G k ⁻¹' S) = 0 ↔ volume S = 0) := fun S hS => by
    have := ae_comp_linearMap_mem_iff (ctrbMap F G k) (volume : Measure (Fin k → Fin p → ℝ))
      (volume : Measure (Fin n → ℝ)) hL hS.compl
    rw [measure_eq_zero_iff_ae_notMem, measure_eq_zero_iff_ae_notMem]
    simpa using this
  have hpi1 : Measure.pi (fun _ : Fin k => Γ) ≪ volume := by
    rw [volume_pi]
    exact pi_absolutelyContinuous h1 k
  have hpi2 : volume ≪ Measure.pi (fun _ : Fin k => Γ) := by
    rw [volume_pi]
    exact pi_absolutelyContinuous h2 k
  constructor
  · refine Measure.AbsolutelyContinuous.mk fun S hS h0 => ?_
    rw [ctrbLaw, Measure.map_apply hmL hS]
    exact hpi1 ((key S hS).2 h0)
  · refine Measure.AbsolutelyContinuous.mk fun S hS h0 => ?_
    rw [ctrbLaw, Measure.map_apply hmL hS] at h0
    exact (key S hS).1 (hpi2 h0)

/-- If `C_k` is onto and `Γ` is equivalent to Lebesgue measure, `Pᵏ(x, ·)` is equivalent to
Lebesgue measure for every `x`. -/
theorem lss_pow_equiv (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) {k : ℕ}
    (hsurj : LinearMap.range (ctrbMap F G k) = ⊤) (h1 : Γ ≪ volume) (h2 : volume ≪ Γ)
    (x : Fin n → ℝ) : (lssMatrixKernel Γ F G ^ k) x ≪ volume ∧
      volume ≪ (lssMatrixKernel Γ F G ^ k) x := by
  obtain ⟨hν1, hν2⟩ := ctrbLaw_equiv Γ F G hsurj h1 h2
  rw [lss_pow_eq]
  have hm := measurable_const_add ((F ^ k) *ᵥ x)
  constructor
  · refine Measure.AbsolutelyContinuous.mk fun S hS h0 => ?_
    rw [Measure.map_apply hm hS]
    exact hν1 (by rw [measure_preimage_add]; exact h0)
  · refine Measure.AbsolutelyContinuous.mk fun S hS h0 => ?_
    rw [Measure.map_apply hm hS] at h0
    have := hν2 h0
    rwa [measure_preimage_add] at this

/-- **Proposition 4.4.3 (i)** (MT p. 92): for a controllable pair and a disturbance law
equivalent to Lebesgue measure, LSS(F, G) is `φ`-irreducible for every `φ ≪ μ_Leb`. -/
theorem lss_isPhiIrreducible (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    {F : Matrix (Fin n) (Fin n) ℝ} {G : Matrix (Fin n) (Fin p) ℝ}
    [IsMarkovKernel (lssMatrixKernel Γ F G)] (hc : IsControllable F G) (h1 : Γ ≪ volume)
    (h2 : volume ≪ Γ) {φ : Measure (Fin n → ℝ)} (hφ : φ ≪ volume) :
    IsPhiIrreducible (lssMatrixKernel Γ F G) φ := by
  intro A hA hpos x
  have hA0 : volume A ≠ 0 := fun h => hpos.ne' (hφ h)
  obtain ⟨-, hvol⟩ := lss_pow_equiv Γ F G (k := n + 1) (range_ctrbMap_eq_top hc (by omega))
    h1 h2 x
  exact (hitProb_pos_iff _ hA x).2 ⟨n, pos_iff_ne_zero.2 fun h => hA0 (hvol h)⟩

/-- **Proposition 4.4.3 (ii)** (MT p. 92): Lebesgue measure is a maximal irreducibility measure
for LSS(F, G). -/
theorem lss_isMaximalIrreducibility (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    {F : Matrix (Fin n) (Fin n) ℝ} {G : Matrix (Fin n) (Fin p) ℝ}
    [IsMarkovKernel (lssMatrixKernel Γ F G)] (hc : IsControllable F G) (h1 : Γ ≪ volume)
    (h2 : volume ≪ Γ) :
    IsMaximalIrreducibility (lssMatrixKernel Γ F G) volume := by
  refine ⟨NeZero.ne _, lss_isPhiIrreducible Γ hc h1 h2 Measure.AbsolutelyContinuous.rfl,
    fun φ' hφ' => Measure.AbsolutelyContinuous.mk fun A hA h0 => ?_⟩
  by_contra hcon
  set P := lssMatrixKernel Γ F G
  have hreach : ∀ y, ∃ m, 0 < (P ^ (m + 1)) y A := fun y =>
    (hitProb_pos_iff P hA y).1 (hφ' A hA (pos_iff_ne_zero.2 hcon) y)
  have hcover : (⋃ m, {y | 0 < (P ^ (m + 1)) y A}) = univ :=
    eq_univ_of_forall fun y => mem_iUnion.2 (hreach y)
  have := isMarkovKernel_pow P (n + 1)
  have hpos : 0 < (P ^ (n + 1)) 0 (⋃ m, {y | 0 < (P ^ (m + 1)) y A}) := by
    rw [hcover, measure_univ]
    exact one_pos
  obtain ⟨m, hm⟩ := exists_measure_pos_of_iUnion hpos
  have h3 := (pow_add_pos_iff P (n + 1) (m + 1) 0 hA).2 hm
  obtain ⟨hac, -⟩ := lss_pow_equiv Γ F G (k := n + 1 + (m + 1))
    (range_ctrbMap_eq_top hc (by omega)) h1 h2 0
  exact h3.ne' (hac h0)

/-- The translations `y ↦ t + y` as a continuous family of continuous maps. -/
noncomputable def translateCM (n : ℕ) : (Fin n → ℝ) → C(Fin n → ℝ, Fin n → ℝ) :=
  ContinuousMap.curry ⟨fun q : (Fin n → ℝ) × (Fin n → ℝ) => q.1 + q.2, continuous_add⟩

/-- For a finite measure `ν ≪ μ_Leb` and a set `B'` of finite Lebesgue measure,
`t ↦ ν(B' − t)` is lower semicontinuous. -/
theorem lss_lowerSemicontinuous {ν : Measure (Fin n → ℝ)} [IsFiniteMeasure ν]
    (hν : ν ≪ volume) {B' : Set (Fin n → ℝ)} (hB'm : MeasurableSet B')
    (hB'fin : volume B' ≠ ⊤) :
    LowerSemicontinuous fun t => ν (translateCM n t ⁻¹' B') := by
  intro t₀ y hy
  have hfg : Tendsto (translateCM n) (𝓝 t₀) (𝓝 (translateCM n t₀)) :=
    (ContinuousMap.curry _).continuous.tendsto t₀
  have hvol := tendsto_measure_symmDiff_preimage_nhds_zero (μ := volume) (ν := volume) hfg
    (Eventually.of_forall fun t => measurePreserving_add_left volume t)
    (measurePreserving_add_left volume t₀) hB'm.nullMeasurableSet hB'fin
  have hνeq : volume.withDensity (ν.rnDeriv volume) = ν :=
    Measure.withDensity_rnDeriv_eq ν volume hν
  have hint : ∫⁻ x, ν.rnDeriv volume x ∂volume ≠ ⊤ := by
    rw [Measure.lintegral_rnDeriv hν]
    exact measure_ne_top ν univ
  have hνt : Tendsto (fun t => ν ((translateCM n t ⁻¹' B') ∆ (translateCM n t₀ ⁻¹' B')))
      (𝓝 t₀) (𝓝 0) := by
    refine (tendsto_setLIntegral_zero hint hvol).congr fun t => ?_
    rw [← withDensity_apply', hνeq]
  have hε : 0 < ν (translateCM n t₀ ⁻¹' B') - y := tsub_pos_of_lt hy
  filter_upwards [hνt.eventually (gt_mem_nhds hε)] with t ht
  have hle : ν (translateCM n t₀ ⁻¹' B') ≤
      ν (translateCM n t ⁻¹' B') + ν ((translateCM n t ⁻¹' B') ∆ (translateCM n t₀ ⁻¹' B')) := by
    have := le_measure_symmDiff (μ := ν) (s₁ := translateCM n t₀ ⁻¹' B')
      (s₂ := translateCM n t ⁻¹' B')
    rw [symmDiff_comm] at this
    rw [add_comm]
    exact tsub_le_iff_right.1 this
  by_contra hcon
  push Not at hcon
  have : ν (translateCM n t₀ ⁻¹' B') < ν (translateCM n t₀ ⁻¹' B') :=
    calc ν (translateCM n t₀ ⁻¹' B') ≤
          y + ν ((translateCM n t ⁻¹' B') ∆ (translateCM n t₀ ⁻¹' B')) :=
          hle.trans (add_le_add_left hcon _)
      _ < y + (ν (translateCM n t₀ ⁻¹' B') - y) := ENNReal.add_lt_add_left hy.ne_top ht
      _ = ν (translateCM n t₀ ⁻¹' B') := add_tsub_cancel_of_le hy.le
  exact lt_irrefl _ this

/-- **Proposition 4.4.3 (iii)** (MT p. 92): for every compact `A` and every `B` with
`μ_Leb(B) > 0`, `A ⇝ B`. -/
theorem lss_unifAccessible (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    {F : Matrix (Fin n) (Fin n) ℝ} {G : Matrix (Fin n) (Fin p) ℝ}
    [IsMarkovKernel (lssMatrixKernel Γ F G)] (hc : IsControllable F G) (h1 : Γ ≪ volume)
    (h2 : volume ≪ Γ) {A B : Set (Fin n → ℝ)} (hA : IsCompact A) (hB : MeasurableSet B)
    (hBpos : 0 < volume B) : UnifAccessible (lssMatrixKernel Γ F G) A B := by
  have hsurj := range_ctrbMap_eq_top hc (k := n + 1) (by omega)
  obtain ⟨hν1, hν2⟩ := ctrbLaw_equiv Γ F G hsurj h1 h2
  have hνfin : IsFiniteMeasure (ctrbLaw Γ F G (n + 1)) := by
    rw [ctrbLaw]
    infer_instance
  obtain ⟨R, hR⟩ : ∃ R : ℕ, 0 < volume (B ∩ Metric.ball (0 : Fin n → ℝ) R) := by
    have hU : B = ⋃ R : ℕ, B ∩ Metric.ball (0 : Fin n → ℝ) R := by
      ext y
      simp only [mem_iUnion, mem_inter_iff, Metric.mem_ball, dist_zero_right]
      refine ⟨fun hy => ?_, fun ⟨_, hy, _⟩ => hy⟩
      obtain ⟨R, hR⟩ := exists_nat_gt ‖y‖
      exact ⟨R, hy, hR⟩
    rw [hU] at hBpos
    exact exists_measure_pos_of_iUnion hBpos
  set B' := B ∩ Metric.ball (0 : Fin n → ℝ) R
  have hB'm : MeasurableSet B' := hB.inter measurableSet_ball
  have hB'fin : volume B' ≠ ⊤ :=
    ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
  set g : (Fin n → ℝ) → ℝ≥0∞ := fun t => ctrbLaw Γ F G (n + 1) (translateCM n t ⁻¹' B')
  have hgpos : ∀ t, 0 < g t := fun t => pos_iff_ne_zero.2 fun h0 => by
    have := hν2 h0
    change volume ((fun y => t + y) ⁻¹' B') = 0 at this
    rw [measure_preimage_add] at this
    exact hR.ne' this
  have hlsc := lss_lowerSemicontinuous hν1 hB'm hB'fin
  rcases A.eq_empty_or_nonempty with hAe | hAne
  · exact ⟨1, one_pos, fun x hx => by rw [hAe] at hx; exact absurd hx (notMem_empty x)⟩
  have hT : IsCompact ((fun x => (F ^ (n + 1)) *ᵥ x) '' A) :=
    hA.image (Continuous.matrix_mulVec continuous_const continuous_id)
  obtain ⟨t₀, -, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn (hAne.image _) hT
    (hlsc.lowerSemicontinuousOn _)
  refine ⟨g t₀, hgpos t₀, fun x hx => ?_⟩
  calc g t₀ ≤ g ((F ^ (n + 1)) *ᵥ x) := isMinOn_iff.1 hmin _ (mem_image_of_mem _ hx)
    _ = (lssMatrixKernel Γ F G ^ (n + 1)) x B' := by
        rw [lss_pow_eq, Measure.map_apply (measurable_const_add _) hB'm]
        rfl
    _ ≤ (lssMatrixKernel Γ F G ^ (n + 1)) x B := measure_mono inter_subset_left
    _ ≤ hitProb (lssMatrixKernel Γ F G) B x := pow_le_hitProb _ hB n x

/-- **Proposition 4.4.3** (MT p. 92). If `(F, G)` is controllable and the disturbance law is
equivalent to Lebesgue measure (for instance Gaussian, `proposition_4_4_3_gaussian`), then
LSS(F, G) is `φ`-irreducible for every `φ` with a density, Lebesgue measure is a maximal
irreducibility measure, and `A ⇝ B` for every compact `A` and every `B` of positive Lebesgue
measure. -/
theorem proposition_4_4_3 (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    {F : Matrix (Fin n) (Fin n) ℝ} {G : Matrix (Fin n) (Fin p) ℝ} (hc : IsControllable F G)
    (h1 : Γ ≪ volume) (h2 : volume ≪ Γ) :
    ∃ _ : IsMarkovKernel (lssMatrixKernel Γ F G),
      (∀ φ : Measure (Fin n → ℝ), φ ≪ volume → IsPhiIrreducible (lssMatrixKernel Γ F G) φ) ∧
      IsMaximalIrreducibility (lssMatrixKernel Γ F G) volume ∧
      ∀ A B : Set (Fin n → ℝ), IsCompact A → MeasurableSet B → 0 < volume B →
        UnifAccessible (lssMatrixKernel Γ F G) A B := by
  have hM := isMarkovKernel_lssMatrixKernel Γ F G
  exact ⟨hM, fun φ hφ => lss_isPhiIrreducible Γ hc h1 h2 hφ,
    lss_isMaximalIrreducibility Γ hc h1 h2,
    fun A B hA hB hBpos => lss_unifAccessible Γ hc h1 h2 hA hB hBpos⟩

/-- The standard Gaussian law `N(0, I)` on `ℝᵖ` (LSS3) is equivalent to Lebesgue measure. -/
theorem stdGaussian_equiv_volume (p : ℕ) :
    Measure.pi (fun _ : Fin p => gaussianReal 0 1) ≪ volume ∧
      volume ≪ Measure.pi (fun _ : Fin p => gaussianReal 0 1) := by
  rw [volume_pi]
  exact ⟨pi_absolutelyContinuous (gaussianReal_absolutelyContinuous 0 one_ne_zero) p,
    pi_absolutelyContinuous (gaussianReal_absolutelyContinuous' 0 one_ne_zero) p⟩

/-- **Proposition 4.4.3**, Gaussian case (MT p. 92): under (LSS1)–(LSS3), `W ∼ N(0, I)`, with
`(F, G)` controllable, the conclusions of Proposition 4.4.3 hold. -/
theorem proposition_4_4_3_gaussian {F : Matrix (Fin n) (Fin n) ℝ}
    {G : Matrix (Fin n) (Fin p) ℝ} (hc : IsControllable F G) :
    ∃ _ : IsMarkovKernel (lssMatrixKernel (Measure.pi fun _ : Fin p => gaussianReal 0 1) F G),
      (∀ φ : Measure (Fin n → ℝ), φ ≪ volume →
        IsPhiIrreducible (lssMatrixKernel (Measure.pi fun _ : Fin p => gaussianReal 0 1) F G) φ) ∧
      IsMaximalIrreducibility (lssMatrixKernel (Measure.pi fun _ : Fin p => gaussianReal 0 1) F G)
        volume ∧
      ∀ A B : Set (Fin n → ℝ), IsCompact A → MeasurableSet B → 0 < volume B →
        UnifAccessible (lssMatrixKernel (Measure.pi fun _ : Fin p => gaussianReal 0 1) F G) A B :=
  proposition_4_4_3 _ hc (stdGaussian_equiv_volume p).1 (stdGaussian_equiv_volume p).2

/-- MT p. 93: for any disturbance law, the range `X₀` of the controllability matrix is an
absorbing set of LSS(F, G). -/
theorem ctrbSubspace_isAbsorbing (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) :
    MeasurableSet (↑(LinearMap.range (ctrbMap F G n)) : Set (Fin n → ℝ)) ∧
      IsAbsorbing (lssMatrixKernel Γ F G)
        (↑(LinearMap.range (ctrbMap F G n)) : Set (Fin n → ℝ)) := by
  have hm : MeasurableSet (↑(LinearMap.range (ctrbMap F G n)) : Set (Fin n → ℝ)) :=
    (Submodule.closed_of_finiteDimensional _).measurableSet
  refine ⟨hm, fun x hx => ?_⟩
  rw [lssMatrixKernel, recursionKernel_apply' Γ (measurable_lssMatrixStep F G) x hm]
  have : {w | F *ᵥ (x, w).1 + G *ᵥ (x, w).2 ∈
      (↑(LinearMap.range (ctrbMap F G n)) : Set (Fin n → ℝ))} = univ :=
    eq_univ_of_forall fun w => ctrbSubspace_absorbing_step F G hx w
  rw [this, measure_univ]

/-- **Correction to (4.18)** (MT p. 93). For `n = 1`, `k = 2`, `F = 0`, `G = 1` the variance is
`Σ₂ = 1`, and the book's density `(2π|Σ_k|)^{−k/2} exp(−y²/2)` integrates to `(2π)^{−1/2} ≠ 1`;
with the correct constant `(2π)^{−n/2} |Σ_k|^{−1/2}` it integrates to `1`. -/
theorem density_4_18_counterexample :
    ∫ y : ℝ, (2 * Real.pi * 1)⁻¹ ^ ((2 : ℝ) / 2) * Real.exp (-(1 / 2) * y ^ 2) ≠ 1 ∧
      ∫ y : ℝ, (Real.sqrt (2 * Real.pi))⁻¹ * (1 : ℝ)⁻¹ * Real.exp (-(1 / 2) * y ^ 2) = 1 := by
  have hg : ∫ y : ℝ, Real.exp (-(1 / 2) * y ^ 2) = Real.sqrt (2 * Real.pi) := by
    rw [integral_gaussian]
    congr 1
    field_simp
  have hpi : 0 < 2 * Real.pi := by positivity
  constructor
  · rw [integral_const_mul, hg, mul_one, div_self two_ne_zero, Real.rpow_one]
    intro h
    have hs : Real.sqrt (2 * Real.pi) = 2 * Real.pi := by
      field_simp at h
      linarith
    have h2 := Real.sq_sqrt hpi.le
    rw [hs] at h2
    nlinarith [Real.two_le_pi]
  · rw [integral_const_mul, hg, inv_one, mul_one]
    exact inv_mul_cancel₀ (Real.sqrt_pos.2 hpi).ne'

end MeynTweedie.VUniformErgodicity
