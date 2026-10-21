/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PseudoAtoms.SmallSetsModels
import PseudoAtoms.LinearIrreducibility
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Small sets for the linear state space model (MT §5.3.5)

Meyn and Tweedie, §5.3.5, p. 110: for the controllable Gaussian LSS(F, G) model every compact set
is small.

The book argues from the continuity and positivity of the Gaussian density of `Pⁿ(x, ·)`, whose
covariance `Σ_n = C_n C_nᵀ` is positive definite under controllability. Mathlib has no
multivariate Gaussian density, so the proof here is coordinate-free: `Pᵐ(x, ·)` is the image of
`Γ^{⊗m}` under `u ↦ Fᵐx + C_m u`, and

* `exists_preimage_ge_of_surjective`: a surjective linear map `L : E → ℝⁿ` pulls Lebesgue
  measure on a ball back to at least a multiple of it under any Haar measure on `E`, restricted
  to a larger ball (uniqueness of Haar measure on `ℝⁿ × ker L ≃ E`);
* `pi_fin_mono`, `pi_smul_restrict`, `pi_ge_restrict`: lower bounds pass to products;
* `gaussianReal_ge_restrict`, `gaussianPi_ge_restrict`: `N(0, I)` dominates a multiple of
  Lebesgue measure on every closed ball, since its density is bounded below there;
* `lss_isSmallSet_of_isCompact`: for any disturbance law with that property and a controllable
  pair `(F, G)`, every compact `K` is `max n 1`-small, with minorising measure a multiple of
  Lebesgue measure on any ball `B̄(0, r)`, `r > 0`; the compactness of `K` enters only through
  the boundedness of `Fᵐ K`;
* `lss_gaussian_isSmallSet_of_isCompact`, `lss_gaussian_isSmall_of_isCompact`: the Gaussian
  case (LSS3).

The book takes `m = n`; here `m = max n 1`, since `IsSmallSet` requires `m ≥ 1` and `n = 0` is
allowed.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal Matrix

variable {n p : ℕ}

/-- **A surjective linear map pushes a Haar measure above a multiple of Lebesgue measure on a
ball.** For a surjective linear `L : E → ℝⁿ` and `R ≥ 0` there are `R'` and `c > 0` with
`μ(L⁻¹(S) ∩ B̄(0, R')) ≥ c μ_Leb(S ∩ B̄(0, R))` for every measurable `S`. -/
theorem exists_preimage_ge_of_surjective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {n : ℕ} (L : E →ₗ[ℝ] (Fin n → ℝ)) (hL : Function.Surjective L)
    (R : ℝ) : ∃ R' : ℝ, ∃ c : ℝ≥0∞, 0 < c ∧ ∀ S, MeasurableSet S →
      c * volume (S ∩ closedBall 0 R) ≤ μ (L ⁻¹' S ∩ closedBall 0 R') := by
  obtain ⟨T, hT⟩ := LinearMap.exists_rightInverse_of_surjective L (LinearMap.range_eq_top.2 hL)
  set K := LinearMap.ker L
  let f : (Fin n → ℝ) × K →ₗ[ℝ] E := T ∘ₗ LinearMap.fst ℝ _ _ + K.subtype ∘ₗ LinearMap.snd ℝ _ _
  have hLT : ∀ y, L (T y) = y := fun y => LinearMap.congr_fun hT y
  have hf : ∀ q, f q = T q.1 + q.2 := fun q => rfl
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨y, k⟩ h
    rw [hf] at h
    have h1 : y = 0 := by
      have := congrArg L h
      rwa [map_add, hLT, show L (k : E) = 0 from k.2, add_zero, map_zero] at this
    subst h1
    simp only [map_zero, zero_add] at h
    exact Prod.ext rfl (Subtype.ext h)
  have hsurj : Function.Surjective f := fun e => by
    refine ⟨(L e, ⟨e - T (L e), ?_⟩), ?_⟩
    · rw [LinearMap.mem_ker, map_sub, hLT, sub_self]
    · rw [hf]; simp
  let Φ := (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  have hΦ : ∀ q, Φ q = T q.1 + q.2 := fun q => rfl
  set lam := μ.map Φ.symm with hlam
  have : lam.IsAddHaarMeasure := Φ.symm.isAddHaarMeasure_map μ
  set ρ := (volume : Measure (Fin n → ℝ)).prod (Measure.addHaar : Measure K) with hρ
  have hlamρ : lam = Measure.addHaarScalarFactor lam ρ • ρ :=
    Measure.isAddLeftInvariant_eq_smul lam ρ
  set c₀ := Measure.addHaarScalarFactor lam ρ
  have hc₀ : (c₀ : ℝ≥0∞) ≠ 0 := by
    intro h0
    have hz : lam = 0 := by rw [hlamρ, ENNReal.coe_eq_zero.1 h0, zero_smul]
    have := measure_ball_pos lam (0 : (Fin n → ℝ) × K) one_pos
    rw [hz] at this
    exact lt_irrefl _ this
  set Tc := LinearMap.toContinuousLinearMap T
  refine ⟨‖Tc‖ * R + 1, c₀ * Measure.addHaar (ball (0 : K) 1),
    ENNReal.mul_pos hc₀ (measure_ball_pos _ _ one_pos).ne', fun S hS => ?_⟩
  set A := (S ∩ closedBall 0 R) ×ˢ ball (0 : K) 1 with hA
  have hAm : MeasurableSet A := (hS.inter measurableSet_closedBall).prod measurableSet_ball
  have hsub : Φ '' A ⊆ L ⁻¹' S ∩ closedBall 0 (‖Tc‖ * R + 1) := by
    rintro _ ⟨⟨y, k⟩, ⟨⟨hyS, hyR⟩, hk⟩, rfl⟩
    rw [hΦ]
    refine ⟨?_, ?_⟩
    · change L (T y + (k : E)) ∈ S
      rwa [map_add, hLT, show L (k : E) = 0 from k.2, add_zero]
    · rw [mem_closedBall_zero_iff] at hyR ⊢
      rw [mem_ball_zero_iff] at hk
      calc ‖T y + (k : E)‖ ≤ ‖T y‖ + ‖(k : E)‖ := norm_add_le _ _
        _ ≤ ‖Tc‖ * R + 1 := by
          gcongr
          · calc ‖T y‖ = ‖Tc y‖ := rfl
              _ ≤ ‖Tc‖ * ‖y‖ := Tc.le_opNorm y
              _ ≤ ‖Tc‖ * R := by gcongr
          · exact hk.le
  have hmeasA : μ (Φ '' A) = lam A := by
    rw [hlam, Measure.map_apply Φ.symm.continuous.measurable hAm,
      ContinuousLinearEquiv.image_eq_preimage_symm]
  calc c₀ * Measure.addHaar (ball (0 : K) 1) * volume (S ∩ closedBall 0 R)
      = lam A := by
        rw [hlamρ, Measure.smul_apply, hA, hρ, Measure.prod_prod, ENNReal.smul_def, smul_eq_mul]
        ring
    _ = μ (Φ '' A) := hmeasA.symm
    _ ≤ _ := measure_mono hsub


/-! ### Lower bounds for product measures -/

/-- Products of measures are monotone: `μ ≤ ν` implies `μ^{⊗k} ≤ ν^{⊗k}`. -/
theorem pi_fin_mono {α : Type*} [MeasurableSpace α] {μ ν : Measure α} [SigmaFinite μ]
    [SigmaFinite ν] (h : μ ≤ ν) (k : ℕ) :
    Measure.pi (fun _ : Fin k => μ) ≤ Measure.pi (fun _ : Fin k => ν) := by
  induction k with
  | zero => rw [Measure.pi_of_empty, Measure.pi_of_empty]
  | succ k ih =>
    have e1 := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => μ) 0
    have e2 := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => ν) 0
    rw [← (e1.symm _).map_eq, ← (e2.symm _).map_eq]
    exact Measure.map_mono (Measure.prod_mono h ih) (MeasurableEquiv.measurable _)

/-- `(c μ|_s)^{⊗ι} = c^{|ι|} μ^{⊗ι}|_{sⁱ}`. -/
theorem pi_smul_restrict {ι : Type*} [Fintype ι] {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] (c : NNReal) (s : Set α) :
    Measure.pi (fun _ : ι => c • μ.restrict s) =
      c ^ Fintype.card ι • (Measure.pi fun _ : ι => μ).restrict (Set.univ.pi fun _ => s) := by
  rw [Measure.restrict_pi_pi]
  refine Measure.pi_eq fun t _ => ?_
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]

/-- The standard Gaussian law on `ℝ` dominates a multiple of Lebesgue measure on every closed
ball. -/
theorem gaussianReal_ge_restrict (R : ℝ) :
    ∃ c : NNReal, 0 < c ∧ c • volume.restrict (closedBall (0 : ℝ) R) ≤ gaussianReal 0 1 := by
  set c := Real.toNNReal ((√(2 * Real.pi))⁻¹ * Real.exp (-R ^ 2 / 2))
  refine ⟨c, Real.toNNReal_pos.2 (by positivity), Measure.le_intro fun B hB _ => ?_⟩
  rw [Measure.smul_apply, Measure.restrict_apply hB, gaussianReal_of_var_ne_zero 0 one_ne_zero,
    withDensity_apply _ hB, ENNReal.smul_def, smul_eq_mul]
  calc (c : ℝ≥0∞) * volume (B ∩ closedBall 0 R) = ∫⁻ _ in B ∩ closedBall 0 R, (c : ℝ≥0∞) := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ w in B ∩ closedBall 0 R, gaussianPDF 0 1 w :=
        setLIntegral_mono' (hB.inter measurableSet_closedBall) fun w hw => by
          change ENNReal.ofReal _ ≤ ENNReal.ofReal _
          refine ENNReal.ofReal_le_ofReal ?_
          rw [gaussianPDFReal]
          simp only [NNReal.coe_one, mul_one, sub_zero]
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
          have h2 := hw.2
          rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at h2
          have : w ^ 2 ≤ R ^ 2 := sq_le_sq' h2.1 h2.2
          linarith
    _ ≤ ∫⁻ w in B, gaussianPDF 0 1 w := lintegral_mono_set inter_subset_left

/-- The standard Gaussian law on `ℝᵖ` dominates a multiple of Lebesgue measure on every closed
ball. -/
theorem gaussianPi_ge_restrict (p : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ c : NNReal, 0 < c ∧ c • volume.restrict (closedBall (0 : Fin p → ℝ) R) ≤
      Measure.pi (fun _ : Fin p => gaussianReal 0 1) := by
  obtain ⟨c, hc, hle⟩ := gaussianReal_ge_restrict R
  refine ⟨c ^ p, pow_pos hc p, ?_⟩
  have h := pi_fin_mono hle p
  rw [pi_smul_restrict, Fintype.card_fin] at h
  rwa [closedBall_pi _ hR, volume_pi]

/-- A law on `ℝᵖ` dominating multiples of Lebesgue measure on balls has products with the same
property. -/
theorem pi_ge_restrict {p : ℕ} {Γ : Measure (Fin p → ℝ)} [SigmaFinite Γ] (k : ℕ) {R : ℝ}
    (hR : 0 ≤ R) {c : NNReal} (hle : c • volume.restrict (closedBall (0 : Fin p → ℝ) R) ≤ Γ) :
    c ^ k • volume.restrict (closedBall (0 : Fin k → Fin p → ℝ) R) ≤
      Measure.pi (fun _ : Fin k => Γ) := by
  have h := pi_fin_mono hle k
  rw [pi_smul_restrict, Fintype.card_fin] at h
  rwa [closedBall_pi _ hR, volume_pi]


/-! ### Compact sets are small -/

/-- **Compact sets are small for LSS(F, G)** (MT §5.3.5, p. 110), for any disturbance law `Γ`
dominating a multiple of Lebesgue measure on each closed ball about `0`: if `(F, G)` is
controllable, every compact `K` is small, with `m = max n 1` and a minorising measure a multiple
of Lebesgue measure on any closed ball `B̄(0, r)`, `r > 0`. -/
theorem lss_isSmallSet_of_isCompact (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (hΓ : ∀ R : ℝ, 0 ≤ R → ∃ c : NNReal, 0 < c ∧
      c • volume.restrict (closedBall (0 : Fin p → ℝ) R) ≤ Γ)
    {F : Matrix (Fin n) (Fin n) ℝ} {G : Matrix (Fin n) (Fin p) ℝ} (hc : IsControllable F G)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) {r : ℝ} (hr : 0 < r) :
    ∃ a : ℝ≥0∞, 0 < a ∧
      IsSmallSet (lssMatrixKernel Γ F G) (max n 1) (a • volume.restrict (closedBall 0 r)) K := by
  set m := max n 1 with hm
  set L := ctrbMap F G m
  have hL : Function.Surjective L :=
    LinearMap.range_eq_top.1 (range_ctrbMap_eq_top hc (le_max_left n 1))
  obtain ⟨R₀, hR₀⟩ := (hK.image (Matrix.mulVecLin (F ^ m)).continuous_of_finiteDimensional
    ).isBounded.subset_closedBall (0 : Fin n → ℝ)
  obtain ⟨R', c₁, hc₁, hA⟩ := exists_preimage_ge_of_surjective
    (volume : Measure (Fin m → Fin p → ℝ)) L hL (R₀ + r)
  obtain ⟨c₂, hc₂, hle⟩ := hΓ (max R' 0) (le_max_right _ _)
  have hpi := pi_ge_restrict m (le_max_right R' 0) hle
  refine ⟨(c₂ : ℝ≥0∞) ^ m * c₁, ENNReal.mul_pos (pow_ne_zero _ (by exact_mod_cast hc₂.ne'))
    hc₁.ne', hK.isClosed.measurableSet, lt_max_of_lt_right one_pos, ?_, fun x hx => ?_⟩
  · intro h0
    have h1 := congrArg (fun μ : Measure (Fin n → ℝ) => μ univ) h0
    simp only [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      smul_eq_mul, Measure.coe_zero, Pi.zero_apply, mul_eq_zero] at h1
    rcases h1 with (h1 | h1) | h1
    · exact pow_ne_zero m (ENNReal.coe_ne_zero.2 hc₂.ne') h1
    · exact hc₁.ne' h1
    · exact (measure_closedBall_pos volume 0 hr).ne' h1
  refine Measure.le_intro fun B hB _ => ?_
  set v := (F ^ m) *ᵥ x
  have hv : ‖v‖ ≤ R₀ := mem_closedBall_zero_iff.1 (hR₀ ⟨x, hx, rfl⟩)
  set S := (fun y => v + y) ⁻¹' B with hS
  have hSm : MeasurableSet S := measurable_const_add v hB
  rw [lss_pow_eq, Measure.map_apply (measurable_const_add v) hB, ctrbLaw,
    Measure.map_apply (measurable_ctrbMap F G m) hSm, Measure.smul_apply,
    Measure.restrict_apply hB, smul_eq_mul]
  have hshift : (fun y => v + y) ⁻¹' (B ∩ closedBall 0 r) ⊆ S ∩ closedBall 0 (R₀ + r) := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    have h2 := mem_closedBall_zero_iff.1 hy.2
    rw [mem_closedBall_zero_iff]
    calc ‖y‖ = ‖(v + y) - v‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖v + y‖ + ‖v‖ := norm_sub_le _ _
      _ ≤ R₀ + r := by linarith
  calc (c₂ : ℝ≥0∞) ^ m * c₁ * volume (B ∩ closedBall 0 r)
      = (c₂ : ℝ≥0∞) ^ m * (c₁ * volume ((fun y => v + y) ⁻¹' (B ∩ closedBall 0 r))) := by
        rw [measure_preimage_add, mul_assoc]
    _ ≤ (c₂ : ℝ≥0∞) ^ m * (c₁ * volume (S ∩ closedBall 0 (R₀ + r))) := by
        gcongr
    _ ≤ (c₂ : ℝ≥0∞) ^ m * volume (L ⁻¹' S ∩ closedBall 0 (max R' 0)) := by
        gcongr
        exact (hA S hSm).trans (measure_mono (inter_subset_inter_right _
          (closedBall_subset_closedBall (le_max_left R' 0))))
    _ = (c₂ ^ m • volume.restrict (closedBall (0 : Fin m → Fin p → ℝ) (max R' 0)))
          (L ⁻¹' S) := by
        rw [Measure.smul_apply, Measure.restrict_apply ((measurable_ctrbMap F G m) hSm),
          ENNReal.smul_def, smul_eq_mul, ENNReal.coe_pow]
    _ ≤ (Measure.pi fun _ : Fin m => Γ) (L ⁻¹' S) := hpi _

/-- **§5.3.5, Gaussian case** (MT p. 110): for the controllable LSS(F, G) model with
`W ∼ N(0, I)` (LSS3), every compact set is small. -/
theorem lss_gaussian_isSmallSet_of_isCompact {F : Matrix (Fin n) (Fin n) ℝ}
    {G : Matrix (Fin n) (Fin p) ℝ} (hc : IsControllable F G) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) {r : ℝ} (hr : 0 < r) :
    ∃ a : ℝ≥0∞, 0 < a ∧
      IsSmallSet (lssMatrixKernel (Measure.pi fun _ : Fin p => gaussianReal 0 1) F G) (max n 1)
        (a • volume.restrict (closedBall 0 r)) K :=
  lss_isSmallSet_of_isCompact _ (fun R hR => gaussianPi_ge_restrict p R hR) hc hK hr

/-- **§5.3.5** (MT p. 110): for the controllable Gaussian LSS(F, G) model every compact set is
small. -/
theorem lss_gaussian_isSmall_of_isCompact {F : Matrix (Fin n) (Fin n) ℝ}
    {G : Matrix (Fin n) (Fin p) ℝ} (hc : IsControllable F G) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) :
    IsSmall (lssMatrixKernel (Measure.pi fun _ : Fin p => gaussianReal 0 1) F G) K := by
  obtain ⟨a, -, h⟩ := lss_gaussian_isSmallSet_of_isCompact hc hK one_pos
  exact ⟨_, _, h⟩

end MeynTweedie.PseudoAtoms
