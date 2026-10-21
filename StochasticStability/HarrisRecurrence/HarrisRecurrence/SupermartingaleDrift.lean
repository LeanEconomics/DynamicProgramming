/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import HarrisRecurrence.DriftCriteria
import Mathlib.Probability.Martingale.Convergence

/-!
# The drift supermartingale on path space (MT §9.4.1)

Meyn and Tweedie, proof of Theorem 9.4.1, p. 214. For a measurable `V : X → ℝ₊` and a measurable
`C ⊆ X` with the drift condition (V1) off `C`, `∫ P(x, dy) V(y) ≤ V(x)` for `x ∉ C`, the process
`V(Φₖ)` killed on entering `C`,

  `Mₖ = V(Φₖ) 1{Φ₀, …, Φₖ₋₁ ∉ C} = V(Φₖ) 1{σ_C ≥ k}`,

is a nonnegative supermartingale for the natural filtration `𝓕ₖ^Φ`, under `P_μ` for every initial
law `μ` with `∫ V dμ < ∞` (in particular under every `P_x`). Mathlib's martingale convergence
theorem (`MeasureTheory.Submartingale.exists_ae_tendsto_of_bdd`) then gives an almost surely
finite limit.

* `avoidSet C k = {Φ₀, …, Φₖ₋₁ ∉ C} = {σ_C ≥ k}` and `measurableSet_natFilt_avoidSet`: it lies in
  `𝓕ₖ₋₁^Φ ⊆ 𝓕ₖ^Φ`.
* `killedV V C k = Mₖ` (real valued) and `killedVE V C k` (the same, `[0, ∞]`-valued).
* `setLIntegral_killedVE_succ_le`: `∫_G M_{k+1} dP_μ ≤ ∫_G M_k dP_μ` for `G ∈ 𝓕ₖ^Φ`, the
  computation on p. 214.
* `lintegral_killedVE_le`: `E_μ[Mₖ] ≤ ∫ V dμ`.
* `supermartingale_killedV`: `(Mₖ, 𝓕ₖ^Φ)` is a supermartingale under `P_μ`.
* `ae_tendsto_killedV`: `Mₖ → M_∞ < ∞`, `P_μ`-a.s.
* `ae_bddAbove_of_avoid`: on `{σ_C = ∞}` the values `V(Φₖ)` are bounded, `P_μ`-a.s.;
  with `C = ∅` this is the convergence of a nonnegative superharmonic function along the path.

**Corrections.** None.
-/

namespace MeynTweedie.HarrisRecurrence

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X]

/-- `{σ_C ≥ k} = {Φ₀, …, Φₖ₋₁ ∉ C}`: the path has avoided `C` before time `k`. -/
def avoidSet (C : Set X) (k : ℕ) : Set (ℕ → X) := {ω | ∀ i < k, ω i ∉ C}

/-- `{σ_C ≥ k} ∈ 𝓕ₙ^Φ` for `k ≤ n + 1`. -/
theorem measurableSet_natFilt_avoidSet {C : Set X} (hC : MeasurableSet C) {k n : ℕ}
    (hkn : k ≤ n + 1) : MeasurableSet[natFilt n] (avoidSet C k) := by
  have : avoidSet C k = ⋂ i ∈ Finset.range k, {ω : ℕ → X | ω i ∈ Cᶜ} := by
    ext ω; simp [avoidSet]
  rw [this]
  exact Finset.measurableSet_biInter _ fun i hi =>
    measurableSet_coord_natFilt (by rw [Finset.mem_range] at hi; omega) hC.compl

/-- `{σ_C ≥ k}` is an event. -/
theorem measurableSet_avoidSet {C : Set X} (hC : MeasurableSet C) (k : ℕ) :
    MeasurableSet (avoidSet C k) :=
  (natFilt (X := X)).le k _ (measurableSet_natFilt_avoidSet hC (Nat.le_succ k))

omit [MeasurableSpace X] in
/-- `{σ_C ≥ k + 1} ⊆ {σ_C ≥ k}`. -/
theorem avoidSet_succ_subset (C : Set X) (k : ℕ) : avoidSet C (k + 1) ⊆ avoidSet C k :=
  fun _ h i hi => h i (by omega)

/-- The killed process `Mₖ = V(Φₖ) 1{σ_C ≥ k}`, `[0, ∞]`-valued. -/
noncomputable def killedVE (V : X → ℝ≥0) (C : Set X) (k : ℕ) (ω : ℕ → X) : ℝ≥0∞ :=
  (avoidSet C k).indicator (fun ω => (V (ω k) : ℝ≥0∞)) ω

/-- The killed process `Mₖ = V(Φₖ) 1{σ_C ≥ k}` (MT p. 214). -/
noncomputable def killedV (V : X → ℝ≥0) (C : Set X) (k : ℕ) (ω : ℕ → X) : ℝ :=
  (avoidSet C k).indicator (fun ω => (V (ω k) : ℝ)) ω

omit [MeasurableSpace X] in
/-- `Mₖ ≥ 0`. -/
theorem killedV_nonneg (V : X → ℝ≥0) (C : Set X) (k : ℕ) (ω : ℕ → X) : 0 ≤ killedV V C k ω :=
  indicator_nonneg (fun _ _ => NNReal.coe_nonneg _) ω

omit [MeasurableSpace X] in
/-- The two versions of `Mₖ` agree. -/
theorem ofReal_killedV (V : X → ℝ≥0) (C : Set X) (k : ℕ) (ω : ℕ → X) :
    ENNReal.ofReal (killedV V C k ω) = killedVE V C k ω := by
  unfold killedV killedVE
  by_cases h : ω ∈ avoidSet C k <;> simp [h]

/-- `Mₖ` is `𝓕ₖ^Φ`-measurable. -/
theorem measurable_natFilt_killedV {V : X → ℝ≥0} (hV : Measurable V) {C : Set X}
    (hC : MeasurableSet C) (k : ℕ) : Measurable[natFilt k] (killedV V C k) := by
  refine Measurable.indicator ?_ (measurableSet_natFilt_avoidSet hC (Nat.le_succ k))
  exact (measurable_coe_nnreal_real.comp hV).comp (measurable_coord_natFilt k)

/-- `Mₖ` is measurable (`[0, ∞]`-valued version). -/
theorem measurable_killedVE {V : X → ℝ≥0} (hV : Measurable V) {C : Set X}
    (hC : MeasurableSet C) (k : ℕ) : Measurable (killedVE V C k) :=
  ((measurable_coe_nnreal_ennreal.comp hV).comp (measurable_pi_apply k)).indicator
    (measurableSet_avoidSet hC k)

/-- **The supermartingale inequality** (MT p. 214): under (V1) off `C`, for `G ∈ 𝓕ₖ^Φ`,
`∫_G M_{k+1} dP_μ ≤ ∫_G M_k dP_μ`. -/
theorem setLIntegral_killedVE_succ_le (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {V : X → ℝ≥0} (hV : Measurable V) {C : Set X}
    (hC : MeasurableSet C) (hdrift : ∀ x ∉ C, ∫⁻ y, (V y : ℝ≥0∞) ∂P x ≤ V x) {k : ℕ}
    {G : Set (ℕ → X)} (hG : MeasurableSet[natFilt k] G) :
    ∫⁻ ω in G, killedVE V C (k + 1) ω ∂pathMeasure P μ ≤
      ∫⁻ ω in G, killedVE V C k ω ∂pathMeasure P μ := by
  have hVe : Measurable fun y => (V y : ℝ≥0∞) := measurable_coe_nnreal_ennreal.comp hV
  have hA1 : MeasurableSet[natFilt k] (avoidSet C (k + 1)) :=
    measurableSet_natFilt_avoidSet hC le_rfl
  have hGm : MeasurableSet G := (natFilt (X := X)).le k _ hG
  have hA1m := measurableSet_avoidSet (X := X) hC (k + 1)
  have hA0m := measurableSet_avoidSet (X := X) hC k
  unfold killedVE
  rw [setLIntegral_indicator hA1m, setLIntegral_indicator hA0m,
    setLIntegral_succ P μ (hA1.inter hG) hVe]
  calc ∫⁻ ω in avoidSet C (k + 1) ∩ G, ∫⁻ y, (V y : ℝ≥0∞) ∂P (ω k) ∂pathMeasure P μ
      ≤ ∫⁻ ω in avoidSet C (k + 1) ∩ G, (V (ω k) : ℝ≥0∞) ∂pathMeasure P μ :=
        setLIntegral_mono ((hVe.comp (measurable_pi_apply k))) fun ω hω =>
          hdrift (ω k) (hω.1 k (Nat.lt_succ_self k))
    _ ≤ ∫⁻ ω in avoidSet C k ∩ G, (V (ω k) : ℝ≥0∞) ∂pathMeasure P μ :=
        lintegral_mono_set (inter_subset_inter_left G (avoidSet_succ_subset C k))

/-- `E_μ[Mₖ] ≤ ∫ V dμ`. -/
theorem lintegral_killedVE_le (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {V : X → ℝ≥0} (hV : Measurable V) {C : Set X}
    (hC : MeasurableSet C) (hdrift : ∀ x ∉ C, ∫⁻ y, (V y : ℝ≥0∞) ∂P x ≤ V x) (k : ℕ) :
    ∫⁻ ω, killedVE V C k ω ∂pathMeasure P μ ≤ ∫⁻ x, (V x : ℝ≥0∞) ∂μ := by
  induction k with
  | zero =>
    have h0 : ∀ ω : ℕ → X, killedVE V C 0 ω = (V (ω 0) : ℝ≥0∞) := fun ω => by
      simp [killedVE, avoidSet]
    simp_rw [h0]
    have hVe : Measurable fun y => (V y : ℝ≥0∞) := measurable_coe_nnreal_ennreal.comp hV
    conv_rhs => rw [← pathMeasure_map_zero P μ]
    rw [lintegral_map hVe (measurable_pi_apply 0)]
  | succ k ih =>
    have h := setLIntegral_killedVE_succ_le P μ hV hC hdrift (k := k) MeasurableSet.univ
    simp only [Measure.restrict_univ] at h
    exact h.trans ih

/-- `Mₖ` is integrable when `∫ V dμ < ∞`. -/
theorem integrable_killedV (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {V : X → ℝ≥0} (hV : Measurable V) {C : Set X}
    (hC : MeasurableSet C) (hdrift : ∀ x ∉ C, ∫⁻ y, (V y : ℝ≥0∞) ∂P x ≤ V x)
    (hfin : ∫⁻ x, (V x : ℝ≥0∞) ∂μ ≠ ∞) (k : ℕ) : Integrable (killedV V C k) (pathMeasure P μ) := by
  refine ⟨((measurable_natFilt_killedV hV hC k).mono ((natFilt (X := X)).le k)
    le_rfl).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have : ∀ ω, ‖killedV V C k ω‖ₑ = killedVE V C k ω := fun ω => by
    rw [← ofReal_killedV, Real.enorm_eq_ofReal (killedV_nonneg V C k ω)]
  simp_rw [this]
  exact (lintegral_killedVE_le P μ hV hC hdrift k).trans_lt hfin.lt_top

/-- `∫_G Mₖ = (∫_G Mₖ)` in `[0, ∞]`, converted to reals. -/
theorem setIntegral_killedV_eq (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {V : X → ℝ≥0} (hV : Measurable V) {C : Set X}
    (hC : MeasurableSet C) (k : ℕ) (G : Set (ℕ → X)) :
    ∫ ω in G, killedV V C k ω ∂pathMeasure P μ =
      (∫⁻ ω in G, killedVE V C k ω ∂pathMeasure P μ).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (killedV_nonneg V C k))
    (((measurable_natFilt_killedV hV hC k).mono ((natFilt (X := X)).le k)
      le_rfl).aestronglyMeasurable)]
  simp_rw [ofReal_killedV]

/-- **The killed drift process is a supermartingale** (MT p. 214): under (V1) off `C` and
`∫ V dμ < ∞`, `(Mₖ, 𝓕ₖ^Φ)` is a nonnegative supermartingale under `P_μ`. -/
theorem supermartingale_killedV (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {V : X → ℝ≥0} (hV : Measurable V) {C : Set X}
    (hC : MeasurableSet C) (hdrift : ∀ x ∉ C, ∫⁻ y, (V y : ℝ≥0∞) ∂P x ≤ V x)
    (hfin : ∫⁻ x, (V x : ℝ≥0∞) ∂μ ≠ ∞) :
    Supermartingale (killedV V C) natFilt (pathMeasure P μ) := by
  have := isProbabilityMeasure_pathMeasure P μ
  refine supermartingale_of_setIntegral_succ_le
    (fun k => (measurable_natFilt_killedV hV hC k).stronglyMeasurable)
    (integrable_killedV P μ hV hC hdrift hfin) fun k G hG => ?_
  rw [setIntegral_killedV_eq P μ hV hC, setIntegral_killedV_eq P μ hV hC]
  have hfin' : ∫⁻ ω in G, killedVE V C k ω ∂pathMeasure P μ ≠ ∞ :=
    ne_top_of_le_ne_top hfin ((setLIntegral_le_lintegral _ _).trans
      (lintegral_killedVE_le P μ hV hC hdrift k))
  exact ENNReal.toReal_mono hfin' (setLIntegral_killedVE_succ_le P μ hV hC hdrift hG)

/-- **Supermartingale convergence for the drift process**: `Mₖ` converges `P_μ`-a.s. to a finite
limit. -/
theorem ae_tendsto_killedV (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {V : X → ℝ≥0} (hV : Measurable V) {C : Set X}
    (hC : MeasurableSet C) (hdrift : ∀ x ∉ C, ∫⁻ y, (V y : ℝ≥0∞) ∂P x ≤ V x)
    (hfin : ∫⁻ x, (V x : ℝ≥0∞) ∂μ ≠ ∞) :
    ∀ᵐ ω ∂pathMeasure P μ, ∃ c, Tendsto (fun k => killedV V C k ω) atTop (𝓝 c) := by
  have := isProbabilityMeasure_pathMeasure P μ
  have hsub := (supermartingale_killedV P μ hV hC hdrift hfin).neg
  have hbdd : ∀ k, eLpNorm ((-killedV V C) k) 1 (pathMeasure P μ) ≤
      (∫⁻ x, (V x : ℝ≥0∞) ∂μ).toNNReal := by
    intro k
    rw [ENNReal.coe_toNNReal hfin,
      eLpNorm_one_eq_lintegral_enorm ((hsub.integrable k).aestronglyMeasurable)]
    have : ∀ ω, ‖(-killedV V C) k ω‖ₑ = killedVE V C k ω := fun ω => by
      rw [Pi.neg_apply, Pi.neg_apply, enorm_neg, ← ofReal_killedV,
        Real.enorm_eq_ofReal (killedV_nonneg V C k ω)]
    simp_rw [this]
    exact lintegral_killedVE_le P μ hV hC hdrift k
  filter_upwards [hsub.exists_ae_tendsto_of_bdd hbdd] with ω ⟨c, hc⟩
  refine ⟨-c, ?_⟩
  have := hc.neg
  simp only [Pi.neg_apply, neg_neg] at this
  exact this

/-- **On `{σ_C = ∞}`, `V(Φₖ)` stays bounded**, `P_μ`-a.s. (MT p. 214): there `Mₖ = V(Φₖ)`, which
converges. -/
theorem ae_bddAbove_of_avoid (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {V : X → ℝ≥0} (hV : Measurable V) {C : Set X}
    (hC : MeasurableSet C) (hdrift : ∀ x ∉ C, ∫⁻ y, (V y : ℝ≥0∞) ∂P x ≤ V x)
    (hfin : ∫⁻ x, (V x : ℝ≥0∞) ∂μ ≠ ∞) :
    ∀ᵐ ω ∂pathMeasure P μ, (∀ i, ω i ∉ C) → ∃ r : ℝ, ∀ k, (V (ω k) : ℝ) ≤ r := by
  filter_upwards [ae_tendsto_killedV P μ hV hC hdrift hfin] with ω ⟨c, hc⟩ hav
  have heq : (fun k => killedV V C k ω) = fun k => (V (ω k) : ℝ) := by
    funext k
    simp only [killedV]
    rw [indicator_of_mem (show ω ∈ avoidSet C k from fun i _ => hav i)]
  rw [heq] at hc
  obtain ⟨r, hr⟩ := hc.bddAbove_range
  exact ⟨r, fun k => hr (mem_range_self k)⟩

end MeynTweedie.HarrisRecurrence
