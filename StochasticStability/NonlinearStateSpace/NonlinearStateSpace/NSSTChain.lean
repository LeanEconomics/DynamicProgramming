/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NonlinearStateSpace.ForwardAccessibility
import NonlinearStateSpace.LocalInverse
import NonlinearStateSpace.TChains
import NonlinearStateSpace.ModelNonlinearModels

/-!
# Forward accessible NSS(F) models are T-chains (MT §7.1.2, §7.1.4)

Meyn and Tweedie, §7.1.2, pp. 149–151, and §7.1.4, pp. 153–154. The state space `X` and the noise
space `W` are finite-dimensional real normed spaces, `W` with a Haar measure `volume`.

* `IsLSCDensity Γ γ` (MT (SNSS3), p. 149; (NSS3), p. 153): `Γ = γ · Leb` with `γ` lower
  semicontinuous; `controlSet γ = O_w = {γ > 0}`, an open set (`isOpen_controlSet`) carrying
  all of `Γ` (`measure_compl_controlSet`).
* `nssKernel_pow_apply_density`: `Pᵏ(x, A) = ∫ 1_A(Fₖ(x, u)) γ(u₁) ⋯ γ(uₖ) du` ((7.6)).
* `exists_continuousComponent` (the core of the proof of Proposition 7.1.2, (7.6)–(7.8)): if
  the joint control map is `C¹` at `(x₀, u⁰)` with `u⁰ ∈ O_wᵏ` and `∂Fₖ/∂u (x₀, u⁰)` is onto,
  then `Pᵏ` has a continuous component `T` with `T(x₀, X) > 0`, and (`k ≥ 1`) `x₀` has an open
  small neighbourhood.
* **Proposition 7.1.5** (p. 154): `proposition_7_1_5`, under (NSS3) and the rank condition (CM3)
  for a `C¹` map `F`, every point has an open small neighbourhood and NSS(F) is a T-chain;
  `proposition_7_1_5_of_forwardAccessible`, the same from forward accessibility when the
  critical values of the control maps are null (the Sard hypothesis of Proposition 7.1.4).
* **Proposition 7.1.2** (p. 149): `proposition_7_1_2`, under (SNSS3) a forward accessible scalar
  model `X = ℝ` is a T-chain (no Sard hypothesis, by Theorem 7.1.1).

**Hypotheses.** `C¹` replaces the book's `C^∞`. The control set is `{γ > 0}` as in (NSS3); the
book's Proposition 7.1.5 assumes forward accessibility, which is used through Proposition 7.1.4
in the form (CM3).
-/

namespace MeynTweedie.NonlinearStateSpace

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasureSpace W]
  [BorelSpace W] [(volume : Measure W).IsAddHaarMeasure]

/-! ### The density condition (NSS3) -/

omit [NormedSpace ℝ W] [FiniteDimensional ℝ W] [BorelSpace W]
  [(volume : Measure W).IsAddHaarMeasure] in
/-- The density condition (SNSS3)/(NSS3) (MT pp. 149, 153): the disturbance law is `Γ = γ · Leb`
with a lower semicontinuous density `γ`. -/
def IsLSCDensity (Γ : Measure W) (γ : W → ℝ≥0∞) : Prop :=
  LowerSemicontinuous γ ∧ Γ = volume.withDensity γ

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasureSpace W]
  [BorelSpace W] [(volume : Measure W).IsAddHaarMeasure] in
/-- The control set `O_w = {w : γ(w) > 0}` of (NSS3). -/
def controlSet {W : Type*} (γ : W → ℝ≥0∞) : Set W := {w | 0 < γ w}

omit [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasureSpace W] [BorelSpace W]
  [(volume : Measure W).IsAddHaarMeasure] in
/-- `O_w` is open (MT p. 149). -/
theorem isOpen_controlSet {γ : W → ℝ≥0∞} (hγ : LowerSemicontinuous γ) :
    IsOpen (controlSet γ) :=
  hγ.isOpen_preimage 0

omit [NormedSpace ℝ W] [FiniteDimensional ℝ W] [BorelSpace W]
  [(volume : Measure W).IsAddHaarMeasure] in
/-- The disturbances lie in `O_w` with probability one (MT p. 149): `Γ(O_wᶜ) = 0`. -/
theorem measure_compl_controlSet {Γ : Measure W} {γ : W → ℝ≥0∞} (hΓ : IsLSCDensity Γ γ)
    [OpensMeasurableSpace W] : Γ (controlSet γ)ᶜ = 0 := by
  have hm := (isOpen_controlSet hΓ.1).measurableSet.compl
  rw [hΓ.2, withDensity_apply _ hm, setLIntegral_congr_fun hm (g := fun _ => 0)
    fun w hw => by simpa [controlSet] using hw]
  simp

/-- The density `γ(u₁) ⋯ γ(uₖ)` of `Γ^{⊗k}`. -/
noncomputable def prodDensity (γ : W → ℝ≥0∞) (k : ℕ) (u : Fin k → W) : ℝ≥0∞ := ∏ i, γ (u i)

omit [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasureSpace W] [BorelSpace W]
  [(volume : Measure W).IsAddHaarMeasure] in
/-- The product density is lower semicontinuous. -/
theorem lowerSemicontinuous_prodDensity {γ : W → ℝ≥0∞} (hγ : LowerSemicontinuous γ) (k : ℕ) :
    LowerSemicontinuous (prodDensity γ k) :=
  lowerSemicontinuous_finset_prod _ fun i _ => hγ.comp (continuous_apply i)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasureSpace W]
  [BorelSpace W] [(volume : Measure W).IsAddHaarMeasure] in
/-- The product density is positive on `O_wᵏ`. -/
theorem prodDensity_pos {γ : W → ℝ≥0∞} {k : ℕ} {u : Fin k → W} (hu : ∀ i, u i ∈ controlSet γ) :
    0 < prodDensity γ k u := by
  rw [prodDensity, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
  exact fun i _ => (hu i).ne'

/-- `Γ^{⊗k} = (γ(u₁) ⋯ γ(uₖ)) · Leb` under (NSS3). -/
theorem pi_eq_withDensity_prodDensity {Γ : Measure W} [IsProbabilityMeasure Γ] {γ : W → ℝ≥0∞}
    (hΓ : IsLSCDensity Γ γ) (k : ℕ) :
    Measure.pi (fun _ : Fin k => Γ) = (volume : Measure (Fin k → W)).withDensity
      (prodDensity γ k) := by
  have hSF : SigmaFinite ((volume : Measure W).withDensity γ) := by
    rw [← hΓ.2]; infer_instance
  have := pi_withDensity_eq (volume : Measure W) hΓ.1.measurable k
  rw [hΓ.2]
  exact this

/-- `(L⁻¹A).indicator f = 1_A(L ·) f`. -/
theorem indicator_preimage_eq_mul {α β : Type*} (L : α → β) (A : Set β) (f : α → ℝ≥0∞) (y : α) :
    (L ⁻¹' A).indicator f y = A.indicator 1 (L y) * f y := by
  by_cases h : L y ∈ A
  · rw [indicator_of_mem (show y ∈ L ⁻¹' A from h), indicator_of_mem h]; simp
  · rw [indicator_of_notMem (show y ∉ L ⁻¹' A from h), indicator_of_notMem h]; simp

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [BorelSpace X] in
/-- **The `k`-step kernel of NSS(F) under (NSS3)** ((7.6), MT p. 150):
`Pᵏ(x, A) = ∫ 1_A(Fₖ(x, u)) γ(u₁) ⋯ γ(uₖ) du`. -/
theorem nssKernel_pow_apply_density {Γ : Measure W} [IsProbabilityMeasure Γ] {γ : W → ℝ≥0∞}
    (hΓ : IsLSCDensity Γ γ) {F : X × W → X} (hF : Measurable F) (k : ℕ) (x : X) {A : Set X}
    (hA : MeasurableSet A) :
    (nssKernel Γ F ^ k) x A =
      ∫⁻ u, A.indicator 1 (controlMap F k x u) * prodDensity γ k u ∂volume := by
  rw [nssKernel, recursionKernel_pow_apply' Γ hF k x hA, pi_eq_withDensity_prodDensity hΓ k,
    show {u | controlMap F k x u ∈ A} = controlMap F k x ⁻¹' A from rfl,
    withDensity_apply _ (measurable_controlMap_right hF k x hA),
    ← lintegral_indicator (measurable_controlMap_right hF k x hA)]
  exact lintegral_congr fun u => indicator_preimage_eq_mul _ A _ u

/-! ### Continuous components from the rank condition -/

/-- **The continuous component of Proposition 7.1.2** ((7.6)–(7.8), MT pp. 149–151, and its
multidimensional form for Proposition 7.1.5): if the joint control map
`(x, u) ↦ Fₖ(x, u)` is `C¹` at `(x₀, u⁰)`, `u⁰ ∈ O_wᵏ`, and `∂Fₖ/∂u (x₀, u⁰)` is onto, then
`Pᵏ` has a continuous component `T` with `T(x₀, X) > 0`; if moreover `k ≥ 1`, some open
neighbourhood of `x₀` is small. -/
theorem exists_continuousComponent {Γ : Measure W} [IsProbabilityMeasure Γ] {γ : W → ℝ≥0∞}
    (hΓ : IsLSCDensity Γ γ) {F : X × W → X} (hF : Measurable F) {k : ℕ} {x₀ : X}
    {u₀ : Fin k → W} (hu₀ : ∀ i, u₀ i ∈ controlSet γ)
    (hG : ContDiffAt ℝ 1 (fun p : X × (Fin k → W) => controlMap F k p.1 p.2) (x₀, u₀))
    (hsurj : Function.Surjective
      ((fderiv ℝ (fun p : X × (Fin k → W) => controlMap F k p.1 p.2) (x₀, u₀)).comp
        (ContinuousLinearMap.inr ℝ X (Fin k → W)))) :
    (∃ T : Kernel X X, IsContinuousComponent (nssKernel Γ F) (diracDist k) T ∧ 0 < T x₀ univ) ∧
      (0 < k → ∃ N : Set X, IsOpen N ∧ x₀ ∈ N ∧ IsSmall (nssKernel Γ F) N) := by
  have hM := isMarkovKernel_recursionKernel Γ hF
  set μ : Measure (Fin k → W) := volume
  obtain ⟨L, K, -, hKl, ⟨y₀, hy₀⟩, hle⟩ := exists_lsc_minorant μ hG hsurj univ_mem
    (lowerSemicontinuous_prodDensity hΓ.1 k) (prodDensity_pos hu₀)
  have hKx : ∀ x, LowerSemicontinuous fun y => K (x, y) := fun x =>
    hKl.comp (continuous_const.prodMk continuous_id)
  have hKy : ∀ y, LowerSemicontinuous fun x => K (x, y) := fun y =>
    hKl.comp (continuous_id.prodMk continuous_const)
  have hKm : ∀ x, Measurable fun y => K (x, y) := fun x => (hKx x).measurable
  -- `T(x, A) = ∫ 1_A(L y) K(x, y) dy`
  set Tf : X → Measure X := fun x => (μ.withDensity fun y => K (x, y)).map L with hTf
  have hTapp : ∀ x A, MeasurableSet A → Tf x A = ∫⁻ y, A.indicator 1 (L y) * K (x, y) ∂μ := by
    intro x A hA
    rw [hTf, Measure.map_apply L.continuous.measurable hA,
      withDensity_apply _ (L.continuous.measurable hA), ← lintegral_indicator
        (L.continuous.measurable hA)]
    exact lintegral_congr fun y => indicator_preimage_eq_mul _ A _ y
  have hTlsc : ∀ A, MeasurableSet A → LowerSemicontinuous fun x => Tf x A := by
    intro A hA
    have : (fun x => Tf x A) = fun x => ∫⁻ y, A.indicator 1 (L y) * K (x, y) ∂μ := by
      ext x; exact hTapp x A hA
    rw [this]
    refine lowerSemicontinuous_lintegral_of_lsc μ (fun x => ?_) fun y => ?_
    · exact (((measurable_const.indicator (L.continuous.measurable hA)).comp
        measurable_id).mul (hKm x))
    · exact lowerSemicontinuous_const_mul (hKy y) _
  set T : Kernel X X := ⟨Tf, Measure.measurable_of_measurable_coe _ fun A hA =>
    (hTlsc A hA).measurable⟩ with hT
  have hTle : ∀ x, T x ≤ (nssKernel Γ F ^ k) x := fun x => by
    refine Measure.le_intro fun A hA _ => ?_
    change Tf x A ≤ _
    rw [hTapp x A hA, nssKernel_pow_apply_density hΓ hF k x hA]
    refine (hle x A hA).trans (le_of_eq ?_)
    simp [μ]
  have hkM := isMarkovKernel_pow (nssKernel Γ F) k
  refine ⟨⟨T, ⟨fun x => (hTle x univ).trans prob_le_one, fun x => ?_, hTlsc⟩, ?_⟩, fun hk => ?_⟩
  · rw [sampledKernel_diracDist]; exact hTle x
  · change 0 < Tf x₀ univ
    rw [hTapp x₀ univ MeasurableSet.univ]
    simp only [indicator_univ, Pi.one_apply, one_mul]
    rw [pos_iff_ne_zero]
    intro h0
    rw [lintegral_eq_zero_iff (hKm x₀)] at h0
    have hopen : IsOpen {y | 0 < K (x₀, y)} := (hKx x₀).isOpen_preimage 0
    have hpos := hopen.measure_pos μ ⟨y₀, hy₀⟩
    have hnull : μ {y | 0 < K (x₀, y)} = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [h0] with y hy
      simp only [Pi.zero_apply] at hy ⊢
      rw [hy]
      exact lt_irrefl 0
    exact hpos.ne' hnull
  · -- an open small neighbourhood
    obtain ⟨c, hc0, hc⟩ := exists_between hy₀
    obtain ⟨N, N', hN, hN', hxN, hyN', hNN⟩ :=
      isOpen_prod_iff.1 (hKl.isOpen_preimage c) x₀ y₀ hc
    refine ⟨N, hN, hxN, k, c • (μ.restrict N').map L, hN.measurableSet, hk, ?_, fun x hx => ?_⟩
    · intro h0
      have := congrArg (fun ν : Measure X => ν univ) h0
      simp only [Measure.smul_apply, Measure.map_apply L.continuous.measurable
        MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ, smul_eq_mul,
        Measure.coe_zero, Pi.zero_apply, mul_eq_zero] at this
      rcases this with h | h
      · exact hc0.ne' h
      · exact (hN'.measure_pos μ ⟨y₀, hyN'⟩).ne' h
    · refine Measure.le_intro fun A hA _ => ?_
      refine le_trans ?_ (hTle x A)
      change _ ≤ Tf x A
      rw [hTapp x A hA, Measure.smul_apply, Measure.map_apply L.continuous.measurable hA,
        smul_eq_mul, ← lintegral_indicator_one (L.continuous.measurable hA),
        ← lintegral_const_mul _ (measurable_one.indicator (L.continuous.measurable hA))]
      calc ∫⁻ y, c * (L ⁻¹' A).indicator 1 y ∂μ.restrict N'
          ≤ ∫⁻ y in N', A.indicator 1 (L y) * K (x, y) ∂μ := by
            refine setLIntegral_mono' hN'.measurableSet fun y hy => ?_
            rw [indicator_preimage_eq_mul, Pi.one_apply, mul_one, mul_comm]
            exact mul_le_mul_right (le_of_lt (hNN (mk_mem_prod hx hy))) _
        _ ≤ ∫⁻ y, A.indicator 1 (L y) * K (x, y) ∂μ := setLIntegral_le_lintegral _ _

/-! ### Propositions 7.1.5 and 7.1.2 -/

/-- Under the rank condition at `x` (for a `C¹` map `F`), `Pᵏ` has a continuous component
non-trivial at `x`, and `x` has an open small neighbourhood. -/
theorem exists_continuousComponent_of_hasFullRankAt {Γ : Measure W} [IsProbabilityMeasure Γ]
    {γ : W → ℝ≥0∞} (hΓ : IsLSCDensity Γ γ) {F : X × W → X} (hF : ContDiff ℝ 1 F) {x : X}
    {k : ℕ} {u : Fin k → W} (h : HasFullRankAt F (controlSet γ) x k u) :
    (∃ T : Kernel X X, IsContinuousComponent (nssKernel Γ F) (diracDist k) T ∧ 0 < T x univ) ∧
      ∃ N : Set X, IsOpen N ∧ x ∈ N ∧ IsSmall (nssKernel Γ F) N := by
  have hG := (contDiff_controlMap hF k).contDiffAt (x := (x, u))
  have hsurj := h.2.2
  rw [← fderiv_controlMap_comp_inr hF k x u] at hsurj
  have := exists_continuousComponent hΓ hF.continuous.measurable h.2.1 hG hsurj
  exact ⟨this.1, this.2 h.1⟩

/-- **Proposition 7.1.5** (MT p. 154): if NSS(F) satisfies the density condition (NSS3) and its
control model satisfies the rank condition (CM3) (by Proposition 7.1.4, forward accessibility),
for a `C¹` map `F`, then the state space is a union of open small sets, and NSS(F) is a
T-chain. -/
theorem proposition_7_1_5 {Γ : Measure W} [IsProbabilityMeasure Γ] {γ : W → ℝ≥0∞}
    (hΓ : IsLSCDensity Γ γ) {F : X × W → X} (hF : ContDiff ℝ 1 F)
    (h : RankCondition F (controlSet γ)) :
    (∀ x, ∃ N : Set X, IsOpen N ∧ x ∈ N ∧ IsSmall (nssKernel Γ F) N) ∧
      IsTChain (nssKernel Γ F) := by
  refine ⟨fun x => ?_, proposition_6_2_4 fun x => ?_⟩
  · obtain ⟨k, u, hk⟩ := h x
    exact (exists_continuousComponent_of_hasFullRankAt hΓ hF hk).2
  · obtain ⟨k, u, hk⟩ := h x
    obtain ⟨T, hT, hpos⟩ := (exists_continuousComponent_of_hasFullRankAt hΓ hF hk).1
    exact ⟨diracDist k, T, isSamplingDist_diracDist k, hT, hpos⟩

/-- **Proposition 7.1.5** from forward accessibility (MT p. 154), through the "only if" half of
Proposition 7.1.4: the Sard hypothesis `CriticalValuesNull` (null critical values of the control
maps) is assumed explicitly. -/
theorem proposition_7_1_5_of_forwardAccessible (μ : Measure X) [μ.IsAddHaarMeasure]
    [Nontrivial X] {Γ : Measure W} [IsProbabilityMeasure Γ] {γ : W → ℝ≥0∞}
    (hΓ : IsLSCDensity Γ γ) {F : X × W → X}
    (hF : ContDiff ℝ 1 F) (hS : CriticalValuesNull μ F (controlSet γ))
    (hfa : IsForwardAccessible F (controlSet γ)) :
    (∀ x, ∃ N : Set X, IsOpen N ∧ x ∈ N ∧ IsSmall (nssKernel Γ F) N) ∧
      IsTChain (nssKernel Γ F) :=
  proposition_7_1_5 hΓ hF (proposition_7_1_4_of_forwardAccessible μ hS hfa)

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] in
/-- **Proposition 7.1.2** (MT p. 149): a scalar nonlinear state space model SNSS(F) (`X = ℝ`) with
a `C¹` map `F`, satisfying the density condition (SNSS3), whose control model is forward
accessible, is a T-chain. (The book takes `W = ℝ`; any finite-dimensional `W` works.) -/
theorem proposition_7_1_2 {Γ : Measure W} [IsProbabilityMeasure Γ] {γ : W → ℝ≥0∞}
    (hΓ : IsLSCDensity Γ γ) {F : ℝ × W → ℝ} (hF : ContDiff ℝ 1 F)
    (hfa : IsForwardAccessible F (controlSet γ)) : IsTChain (nssKernel Γ F) :=
  (proposition_7_1_5 hΓ hF ((theorem_7_1_1 hF (isOpen_controlSet hΓ.1)).1 hfa)).2

end MeynTweedie.NonlinearStateSpace
