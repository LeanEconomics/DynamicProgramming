/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Irreducibility.LinearIrreducibility

/-!
# The linear state space model restricted to its controllable subspace (MT §4.4.3)

Meyn and Tweedie, §4.4.3, p. 93. When `(F, G)` is not controllable, the range
`X₀ = R[F^{n−1}G | ⋯ | FG | G] = {Σ_{i<n} Fⁱ G wᵢ}` of the controllability matrix
(`ctrbSubspace F G`) is absorbing for LSS(F, G) (`ctrbSubspace_isAbsorbing`), so the chain can be
restricted to `X₀` (Proposition 4.2.4). The book states that the restricted process is again a
linear state space model with a controllable pair `(F₀, G₀)`, and hence, by Proposition 4.4.3, is
`μ_Leb`-irreducible on `X₀`.

Lebesgue measure on `X₀` is taken to be any additive Haar measure `μ₀` on the subspace `X₀`
(any two are proportional; the image of Lebesgue measure under a linear isometry
`EuclideanSpace ℝ (Fin r) ≃ X₀` is one of them).

* `pow_mulVec_mem_ctrbSubspace`: `X₀` is invariant under `F`; `ctrbMap_mem_ctrbSubspace`:
  `C_k u ∈ X₀` for every `k`.
* `ctrbF₀`, `ctrbG₀`: the restricted pair `F₀ = F|_{X₀}`, `G₀ : ℝᵖ → X₀`;
  `restrictKernel_eq_lssKernel`: the restricted chain is the linear state space model
  LSS(F₀, G₀) on `X₀`; `restricted_controllable`: `(F₀, G₀)` is controllable, every state of `X₀`
  being reached from every other in `n` steps.
* `restricted_pow_eq_zero_iff`: for `k ≥ n` and a disturbance law equivalent to Lebesgue measure,
  `P_{X₀}ᵏ(x, B) = 0` iff `μ₀(B) = 0`.
* `restricted_isPhiIrreducible`, `restricted_isMaximalIrreducibility` and the summary
  `restricted_irreducible` (p. 93): the restricted chain is `φ`-irreducible for every `φ ≪ μ₀`,
  and `μ₀` is a maximal irreducibility measure. The Gaussian case (LSS3) is
  `restricted_irreducible_gaussian`.

No controllability hypothesis is needed: when `(F, G)` is controllable, `X₀ = ℝⁿ`.

**Corrections.** None.
-/

namespace MeynTweedie.Irreducibility

open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped ENNReal Matrix

variable {n p : ℕ}

/-- The controllable subspace `X₀`, the range of the controllability matrix `C_n` (MT p. 93). -/
noncomputable abbrev ctrbSubspace (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) :
    Submodule ℝ (Fin n → ℝ) :=
  LinearMap.range (ctrbMap F G n)

/-- `X₀` is a measurable set. -/
theorem measurableSet_ctrbSubspace (F : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin n) (Fin p) ℝ) : MeasurableSet (ctrbSubspace F G : Set (Fin n → ℝ)) :=
  (Submodule.closed_of_finiteDimensional _).measurableSet

/-- `X₀` is invariant under `F`, hence under every power `Fᵏ`. -/
theorem pow_mulVec_mem_ctrbSubspace (F : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin n) (Fin p) ℝ) {x : Fin n → ℝ} (hx : x ∈ ctrbSubspace F G) (k : ℕ) :
    (F ^ k) *ᵥ x ∈ ctrbSubspace F G := by
  induction k with
  | zero => rwa [pow_zero, one_mulVec]
  | succ k ih =>
    have := ctrbSubspace_absorbing_step F G ih 0
    rwa [mulVec_zero, add_zero, mulVec_mulVec, ← pow_succ'] at this

/-- `C_k u ∈ X₀` for every `k` (Cayley–Hamilton). -/
theorem ctrbMap_mem_ctrbSubspace (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (k : ℕ) (u : Fin k → Fin p → ℝ) : ctrbMap F G k u ∈ ctrbSubspace F G :=
  range_ctrbMap_le_n F G k ⟨u, rfl⟩

/-- `C_k` as a linear map onto `X₀`. -/
noncomputable def ctrbMap₀ (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (k : ℕ) : (Fin k → Fin p → ℝ) →ₗ[ℝ] ctrbSubspace F G :=
  (ctrbMap F G k).codRestrict _ (ctrbMap_mem_ctrbSubspace F G k)

/-- For `k ≥ n`, `C_k` maps onto `X₀`. -/
theorem ctrbMap₀_surjective (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    {k : ℕ} (hk : n ≤ k) : Function.Surjective (ctrbMap₀ F G k) := by
  rintro ⟨y, hy⟩
  obtain ⟨u, hu⟩ := range_ctrbMap_mono F G hk hy
  exact ⟨u, Subtype.ext hu⟩

/-! ### The restricted pair `(F₀, G₀)` -/

/-- `F₀ = F` restricted to `X₀`. -/
noncomputable def ctrbF₀ (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) :
    ctrbSubspace F G →L[ℝ] ctrbSubspace F G :=
  LinearMap.toContinuousLinearMap ((Matrix.mulVecLin F).restrict fun x hx => by
    simpa using pow_mulVec_mem_ctrbSubspace F G hx 1)

/-- `G₀ = G` viewed as a map into `X₀`. -/
noncomputable def ctrbG₀ (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) :
    (Fin p → ℝ) →L[ℝ] ctrbSubspace F G :=
  LinearMap.toContinuousLinearMap ((Matrix.mulVecLin G).codRestrict _ fun w => by
    have := ctrbSubspace_absorbing_step F G (zero_mem (ctrbSubspace F G)) w
    simpa using this)

/-- `↑(F₀ x + G₀ w) = F x + G w`. -/
theorem coe_ctrbStep (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (x : ctrbSubspace F G) (w : Fin p → ℝ) :
    ((ctrbF₀ F G x + ctrbG₀ F G w : ctrbSubspace F G) : Fin n → ℝ) = F *ᵥ x + G *ᵥ w := rfl

/-- MT p. 93: the chain restricted to the absorbing set `X₀` is the linear state space model
LSS(F₀, G₀) on `X₀`. -/
theorem restrictKernel_eq_lssKernel (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) :
    (restrictKernel (lssMatrixKernel Γ F G) (measurableSet_ctrbSubspace F G) :
        Kernel (ctrbSubspace F G) (ctrbSubspace F G)) =
      lssKernel Γ (ctrbF₀ F G) (ctrbG₀ F G) := by
  ext x B hB
  have hB' : MeasurableSet (Subtype.val '' B : Set (Fin n → ℝ)) :=
    (MeasurableEmbedding.subtype_coe (measurableSet_ctrbSubspace F G)).measurableSet_image.2 hB
  rw [restrictKernel_apply _ _ x hB, lssMatrixKernel,
    recursionKernel_apply' Γ (measurable_lssMatrixStep F G) _ hB']
  erw [lssKernel_apply' Γ (ctrbF₀ F G) (ctrbG₀ F G) x hB]
  congr 1
  ext w
  simp only [mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨b, hb, hbw⟩
    have : b = ctrbF₀ F G x + ctrbG₀ F G w := Subtype.ext (by rw [coe_ctrbStep]; exact hbw)
    exact this ▸ hb
  · intro h
    exact ⟨_, h, coe_ctrbStep F G x w⟩

/-- The control trajectories of `(F₀, G₀)` are those of `(F, G)` started in `X₀`. -/
theorem coe_controlMap_ctrb (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (k : ℕ) (x₀ : ctrbSubspace F G) (u : Fin k → Fin p → ℝ) :
    ((controlMap (fun q : ctrbSubspace F G × (Fin p → ℝ) => ctrbF₀ F G q.1 + ctrbG₀ F G q.2)
        k x₀ u : ctrbSubspace F G) : Fin n → ℝ) = lcmTrajectory F G k x₀ u := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [controlMap_succ, coe_ctrbStep, ih]
    rfl

/-- MT p. 93: the pair `(F₀, G₀)` is controllable: every state of `X₀` is reached from every
initial state in `X₀`, in `n` steps. -/
theorem restricted_controllable (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (x₀ x : ctrbSubspace F G) :
    ∃ u : Fin n → Fin p → ℝ,
      controlMap (fun q : ctrbSubspace F G × (Fin p → ℝ) => ctrbF₀ F G q.1 + ctrbG₀ F G q.2)
        n x₀ u = x := by
  have hmem : (x : Fin n → ℝ) - (F ^ n) *ᵥ x₀ ∈ ctrbSubspace F G :=
    sub_mem x.2 (pow_mulVec_mem_ctrbSubspace F G x₀.2 n)
  obtain ⟨u, hu⟩ := hmem
  refine ⟨u, Subtype.ext ?_⟩
  rw [coe_controlMap_ctrb, lcmTrajectory_eq_ctrbMap, hu, add_sub_cancel]

/-! ### Irreducibility of the restricted chain -/

/-- For `k ≥ n` and a disturbance law equivalent to Lebesgue measure, the `k`-step law of the
restricted chain has the same null sets as any Haar measure `μ₀` on `X₀`. -/
theorem restricted_pow_eq_zero_iff (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (h1 : Γ ≪ volume)
    (h2 : volume ≪ Γ) (μ₀ : Measure (ctrbSubspace F G)) [μ₀.IsAddHaarMeasure] {k : ℕ}
    (hk : n ≤ k) (x : ctrbSubspace F G) {B : Set (ctrbSubspace F G)} (hB : MeasurableSet B) :
    ((restrictKernel (lssMatrixKernel Γ F G) (measurableSet_ctrbSubspace F G) :
        Kernel (ctrbSubspace F G) (ctrbSubspace F G)) ^ k) x B = 0 ↔ μ₀ B = 0 := by
  have hX := measurableSet_ctrbSubspace F G
  have := isMarkovKernel_lssMatrixKernel Γ F G
  have hAbs := (ctrbSubspace_isAbsorbing Γ F G).2
  have hB' : MeasurableSet (Subtype.val '' B : Set (Fin n → ℝ)) :=
    (MeasurableEmbedding.subtype_coe hX).measurableSet_image.2 hB
  set c₀ : ctrbSubspace F G := ⟨(F ^ k) *ᵥ x, pow_mulVec_mem_ctrbSubspace F G x.2 k⟩
  set L₀ := ctrbMap₀ F G k
  have hL₀ : Measurable L₀ := L₀.continuous_of_finiteDimensional.measurable
  have hT : MeasurableSet (L₀ ⁻¹' ((fun y => c₀ + y) ⁻¹' B)) :=
    hL₀ ((measurable_const_add c₀) hB)
  have hset : ctrbMap F G k ⁻¹' ((fun y => (F ^ k) *ᵥ (x : Fin n → ℝ) + y) ⁻¹' (Subtype.val '' B)) =
      L₀ ⁻¹' ((fun y => c₀ + y) ⁻¹' B) := by
    ext u
    simp only [mem_preimage, mem_image]
    constructor
    · rintro ⟨b, hb, hbu⟩
      have : b = c₀ + L₀ u := Subtype.ext hbu
      exact this ▸ hb
    · intro h
      exact ⟨_, h, rfl⟩
  rw [restrictKernel_pow_apply _ hX hAbs k x hB, lss_pow_eq]
  erw [Measure.map_apply (measurable_const_add ((F ^ k) *ᵥ (x : Fin n → ℝ))) hB', ctrbLaw,
    Measure.map_apply (measurable_ctrbMap F G k)
      (measurable_const_add ((F ^ k) *ᵥ (x : Fin n → ℝ)) hB'), hset]
  have hpi1 : Measure.pi (fun _ : Fin k => Γ) ≪ volume := by
    rw [volume_pi]
    exact pi_absolutelyContinuous h1 k
  have hpi2 : volume ≪ Measure.pi (fun _ : Fin k => Γ) := by
    rw [volume_pi]
    exact pi_absolutelyContinuous h2 k
  have key := ae_comp_linearMap_mem_iff L₀ (volume : Measure (Fin k → Fin p → ℝ)) μ₀
    (ctrbMap₀_surjective F G hk) ((measurable_const_add c₀) hB).compl
  have key' : volume (L₀ ⁻¹' ((fun y => c₀ + y) ⁻¹' B)) = 0 ↔
      μ₀ ((fun y => c₀ + y) ⁻¹' B) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem, measure_eq_zero_iff_ae_notMem]
    simpa using key
  rw [measure_preimage_add] at key'
  exact ⟨fun h => key'.1 (hpi2 h), fun h => hpi1 (key'.2 h)⟩

/-- MT p. 93: the restricted chain is `φ`-irreducible for every `φ ≪ μ₀`. -/
theorem restricted_isPhiIrreducible (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (h1 : Γ ≪ volume)
    (h2 : volume ≪ Γ) (μ₀ : Measure (ctrbSubspace F G)) [μ₀.IsAddHaarMeasure]
    [IsMarkovKernel (restrictKernel (lssMatrixKernel Γ F G) (measurableSet_ctrbSubspace F G) :
        Kernel (ctrbSubspace F G) (ctrbSubspace F G))]
    {φ : Measure (ctrbSubspace F G)} (hφ : φ ≪ μ₀) :
    IsPhiIrreducible (restrictKernel (lssMatrixKernel Γ F G) (measurableSet_ctrbSubspace F G) :
        Kernel (ctrbSubspace F G) (ctrbSubspace F G)) φ := by
  intro A hA hpos x
  have hA0 : μ₀ A ≠ 0 := fun h => hpos.ne' (hφ h)
  refine (hitProb_pos_iff _ hA x).2 ⟨n, pos_iff_ne_zero.2 fun h => hA0 ?_⟩
  exact (restricted_pow_eq_zero_iff Γ F G h1 h2 μ₀ (by omega) x hA).1 h

/-- MT p. 93: any Haar measure `μ₀` on `X₀` is a maximal irreducibility measure for the
restricted chain. -/
theorem restricted_isMaximalIrreducibility (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (h1 : Γ ≪ volume)
    (h2 : volume ≪ Γ) (μ₀ : Measure (ctrbSubspace F G)) [μ₀.IsAddHaarMeasure]
    [IsMarkovKernel (restrictKernel (lssMatrixKernel Γ F G) (measurableSet_ctrbSubspace F G) :
        Kernel (ctrbSubspace F G) (ctrbSubspace F G))] :
    IsMaximalIrreducibility (restrictKernel (lssMatrixKernel Γ F G)
        (measurableSet_ctrbSubspace F G) : Kernel (ctrbSubspace F G) (ctrbSubspace F G)) μ₀ := by
  set P : Kernel (ctrbSubspace F G) (ctrbSubspace F G) :=
    restrictKernel (lssMatrixKernel Γ F G) (measurableSet_ctrbSubspace F G)
  refine ⟨NeZero.ne _, restricted_isPhiIrreducible Γ F G h1 h2 μ₀
    Measure.AbsolutelyContinuous.rfl, fun φ' hφ' => Measure.AbsolutelyContinuous.mk
      fun A hA h0 => ?_⟩
  by_contra hcon
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
  exact h3.ne' ((restricted_pow_eq_zero_iff Γ F G h1 h2 μ₀ (k := n + 1 + (m + 1)) (by omega)
    0 hA).2 h0)

/-- **The restricted model** (MT p. 93). For any `(F, G)` and a disturbance law equivalent to
Lebesgue measure, the chain restricted to the absorbing controllable subspace `X₀` is a
transition kernel on `X₀`, equal to LSS(F₀, G₀) with `(F₀, G₀)` controllable; it is
`φ`-irreducible for every `φ ≪ μ₀`, and `μ₀` (Lebesgue measure on `X₀`) is a maximal
irreducibility measure. -/
theorem restricted_irreducible (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (h1 : Γ ≪ volume)
    (h2 : volume ≪ Γ) (μ₀ : Measure (ctrbSubspace F G)) [μ₀.IsAddHaarMeasure] :
    ∃ _ : IsMarkovKernel (restrictKernel (lssMatrixKernel Γ F G)
        (measurableSet_ctrbSubspace F G) : Kernel (ctrbSubspace F G) (ctrbSubspace F G)),
      (restrictKernel (lssMatrixKernel Γ F G) (measurableSet_ctrbSubspace F G) :
          Kernel (ctrbSubspace F G) (ctrbSubspace F G)) =
        lssKernel Γ (ctrbF₀ F G) (ctrbG₀ F G) ∧
      (∀ φ : Measure (ctrbSubspace F G), φ ≪ μ₀ →
        IsPhiIrreducible (restrictKernel (lssMatrixKernel Γ F G)
          (measurableSet_ctrbSubspace F G) : Kernel (ctrbSubspace F G) (ctrbSubspace F G)) φ) ∧
      IsMaximalIrreducibility (restrictKernel (lssMatrixKernel Γ F G)
        (measurableSet_ctrbSubspace F G) : Kernel (ctrbSubspace F G) (ctrbSubspace F G)) μ₀ := by
  have hM := isMarkovKernel_restrictKernel (lssMatrixKernel Γ F G)
    (measurableSet_ctrbSubspace F G) (ctrbSubspace_isAbsorbing Γ F G).2
  exact ⟨hM, restrictKernel_eq_lssKernel Γ F G,
    fun φ hφ => restricted_isPhiIrreducible Γ F G h1 h2 μ₀ hφ,
    restricted_isMaximalIrreducibility Γ F G h1 h2 μ₀⟩

/-- The restricted model with Gaussian noise (LSS3), MT p. 93. -/
theorem restricted_irreducible_gaussian (F : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin n) (Fin p) ℝ) (μ₀ : Measure (ctrbSubspace F G)) [μ₀.IsAddHaarMeasure] :
    ∃ _ : IsMarkovKernel (restrictKernel (lssMatrixKernel (Measure.pi fun _ : Fin p =>
        gaussianReal 0 1) F G) (measurableSet_ctrbSubspace F G) :
          Kernel (ctrbSubspace F G) (ctrbSubspace F G)),
      (∀ φ : Measure (ctrbSubspace F G), φ ≪ μ₀ →
        IsPhiIrreducible (restrictKernel (lssMatrixKernel (Measure.pi fun _ : Fin p =>
          gaussianReal 0 1) F G) (measurableSet_ctrbSubspace F G) :
            Kernel (ctrbSubspace F G) (ctrbSubspace F G)) φ) ∧
      IsMaximalIrreducibility (restrictKernel (lssMatrixKernel (Measure.pi fun _ : Fin p =>
        gaussianReal 0 1) F G) (measurableSet_ctrbSubspace F G) :
          Kernel (ctrbSubspace F G) (ctrbSubspace F G)) μ₀ := by
  obtain ⟨hM, -, h1, h2⟩ := restricted_irreducible _ F G (stdGaussian_equiv_volume p).1
    (stdGaussian_equiv_volume p).2 μ₀
  exact ⟨hM, h1, h2⟩

end MeynTweedie.Irreducibility
