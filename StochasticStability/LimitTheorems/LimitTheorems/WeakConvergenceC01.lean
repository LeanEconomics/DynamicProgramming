/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.TightnessC01
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Weak convergence in `C([0,1], ℝ)`: tightness plus fidis, continuous mapping, converging together

Generic weak-convergence machinery on the path space, used for the functional CLT (MT,
Theorem 17.4.4, p. 446, the FCLT part of Theorem 17.4.5, and Theorem D.6.4). References are to
Billingsley, *Convergence of Probability Measures* (2nd ed., 1999). Convergence in distribution
is Mathlib's `TendstoInDistribution`.

## Main results

* `tendstoInDistribution_of_tight_of_fidiLin` (Billingsley Thms 5.1 and 7.1, Prokhorov): random
  paths `Xₙ : Ωₙ → C([0,1], ℝ)` with tight laws whose linear fidis `fidiLin t c ∘ Xₙ` converge in
  distribution to `fidiLin t c` under a probability measure `W` converge in distribution to `W`.
  Variants: `tendstoInDistribution_of_tight_of_fidiLin'` (any limit path of law `W`),
  `tendstoInDistribution_of_tight_of_fidiLin_single` (one probability space).
* `tendstoInDistribution_polygonal_of_blocks`: the assembled statement for
  `Xₙ = polygonal n (n^{-1/2} S)` under the block condition of `TightnessC01`.
* `tendstoInDistribution_fidiLin_polygonal_of_steps`: the linear fidis of
  `polygonal n (n^{-1/2} S)` converge as soon as the step values `Σ c i n^{-1/2} S ⌊n t i⌋` do and
  single normalised increments are negligible in probability.
* `tendstoInDistribution_congr_limit_law`: the limit only matters through its law (used to pass
  from a Gaussian limit variable to `fidiLin t c` under a Wiener measure).
* Continuous mapping (Mathlib's `TendstoInDistribution.continuous_comp`) for the two functionals
  of MT §17.4: `continuous_eval_one_C01` with `tendstoInDistribution_eval_one` (`u(1)`), and
  `supPath f = ⨆ t, f t` with `le_supPath`, `supPath_le_iff`, `exists_supPath_eq`,
  `abs_supPath_sub_le`, `continuous_supPath`, `tendstoInDistribution_supPath` (`max u`).
* Converging together (Billingsley Thm 3.1): `tendstoInDistribution_of_norm_sub_tendsto` (in
  probability) and `tendstoInDistribution_of_ae_norm_sub_tendsto` (almost surely), wrappers of
  Mathlib's `tendstoInDistribution_of_tendstoInMeasure_sub`.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal

/-- Changing the limit random variable to another one with the same law preserves convergence
in distribution. -/
theorem tendstoInDistribution_congr_limit_law {E : Type*} [TopologicalSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E] {Ω : ℕ → Type*}
    {mΩ : ∀ n, MeasurableSpace (Ω n)} {Q : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (Q n)]
    {X : ∀ n, Ω n → E} {Ω' Ω'' : Type*} [MeasurableSpace Ω'] [MeasurableSpace Ω'']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {P'' : Measure Ω''} [IsProbabilityMeasure P'']
    {Z : Ω' → E} {Z' : Ω'' → E} (h : TendstoInDistribution X atTop Z Q P')
    (hZ' : AEMeasurable Z' P'') (hlaw : P'.map Z = P''.map Z') :
    TendstoInDistribution X atTop Z' Q P'' where
  forall_aemeasurable := h.forall_aemeasurable
  aemeasurable_limit := hZ'
  tendsto := by
    have e : (⟨P''.map Z', inferInstance⟩ : ProbabilityMeasure E) =
        ⟨P'.map Z, inferInstance⟩ := Subtype.ext hlaw.symm
    rw [e]
    exact h.tendsto

/-- **Convergence of random paths from tightness and the linear fidis** (Billingsley, Thm 7.1
with Thm 7.5 / Prokhorov). Let `Xₙ : Ωₙ → C([0,1], ℝ)` be random paths under probability
measures `Qₙ` whose laws are tight. If for every `k`, `t`, `c` the linear fidi `fidiLin t c ∘ Xₙ`
converges in distribution to `fidiLin t c` under a probability measure `W` on the path space,
then `Xₙ ⇒ W` (convergence in distribution to the identity on `(C([0,1], ℝ), W)`).

Proof: by Prokhorov the laws lie in a compact set; every cluster point has the linear fidis of
`W` (continuous mapping), hence equals `W` (`ext_of_fidiLin`). -/
theorem tendstoInDistribution_of_tight_of_fidiLin [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {Ω : ℕ → Type*} {mΩ : ∀ n, MeasurableSpace (Ω n)}
    {Q : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (Q n)]
    {X : ∀ n, Ω n → C(unitInterval, ℝ)} (hX : ∀ n, AEMeasurable (X n) (Q n))
    (htight : IsTightMeasureSet (Set.range fun n => (Q n).map (X n)))
    (W : Measure C(unitInterval, ℝ)) [IsProbabilityMeasure W]
    (hfidi : ∀ (k : ℕ) (t : Fin k → unitInterval) (c : Fin k → ℝ),
      TendstoInDistribution (fun n => fidiLin t c ∘ X n) atTop (fidiLin t c) Q W) :
    TendstoInDistribution X atTop id Q W where
  forall_aemeasurable := hX
  aemeasurable_limit := aemeasurable_id
  tendsto := by
    set ρ : ℕ → ProbabilityMeasure C(unitInterval, ℝ) :=
      fun n => ⟨(Q n).map (X n), inferInstance⟩ with hρ
    set w : ProbabilityMeasure C(unitInterval, ℝ) := ⟨W.map id, inferInstance⟩ with hw
    change Tendsto ρ atTop (𝓝 w)
    have hS : IsTightMeasureSet
        {((μ : ProbabilityMeasure C(unitInterval, ℝ)) : Measure C(unitInterval, ℝ)) |
          μ ∈ Set.range ρ} := by
      refine htight.subset ?_
      rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    have hK := isCompact_closure_of_isTightMeasureSet hS
    refine hK.tendsto_nhds_of_unique_mapClusterPt
      (Eventually.of_forall fun n => subset_closure ⟨n, rfl⟩) fun ν _ hν => ?_
    have hfd : ∀ (k : ℕ) (t : Fin k → unitInterval) (c : Fin k → ℝ),
        (ν : Measure C(unitInterval, ℝ)).map (fidiLin t c) = W.map (fidiLin t c) := by
      intro k t c
      have hg := ProbabilityMeasure.continuous_map (Ω := C(unitInterval, ℝ)) (Ω' := ℝ)
        (continuous_fidiLin t c)
      have hcl := hν.tendsto_comp (hg.tendsto ν)
      have hlim := (hfidi k t c).tendsto
      have e : ((fun μ : ProbabilityMeasure C(unitInterval, ℝ) => μ.map (fidiLin t c)) ∘ ρ) =
          fun n => (⟨(Q n).map (fidiLin t c ∘ X n), inferInstance⟩ : ProbabilityMeasure ℝ) := by
        funext n
        apply Subtype.ext
        change ((Q n).map (X n)).map (fidiLin t c) = (Q n).map (fidiLin t c ∘ X n)
        exact AEMeasurable.map_map_of_aemeasurable
          (continuous_fidiLin t c).measurable.aemeasurable (hX n)
      rw [e] at hcl
      have heq := eq_of_nhds_neBot (hcl.clusterPt.mono hlim)
      have := congrArg (fun μ : ProbabilityMeasure ℝ => (μ : Measure ℝ)) heq
      exact this
    have hνW : (ν : Measure C(unitInterval, ℝ)) = W := ext_of_fidiLin hfd
    apply Subtype.ext
    change (ν : Measure C(unitInterval, ℝ)) = W.map id
    rw [Measure.map_id, hνW]

/-- `tendstoInDistribution_of_tight_of_fidiLin` with any limit random path `Z` of law `W`. -/
theorem tendstoInDistribution_of_tight_of_fidiLin' [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {Ω : ℕ → Type*} {mΩ : ∀ n, MeasurableSpace (Ω n)}
    {Q : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (Q n)]
    {X : ∀ n, Ω n → C(unitInterval, ℝ)} (hX : ∀ n, AEMeasurable (X n) (Q n))
    (htight : IsTightMeasureSet (Set.range fun n => (Q n).map (X n)))
    (W : Measure C(unitInterval, ℝ)) [IsProbabilityMeasure W]
    (hfidi : ∀ (k : ℕ) (t : Fin k → unitInterval) (c : Fin k → ℝ),
      TendstoInDistribution (fun n => fidiLin t c ∘ X n) atTop (fidiLin t c) Q W)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → C(unitInterval, ℝ)} (hZ : AEMeasurable Z P') (hZW : P'.map Z = W) :
    TendstoInDistribution X atTop Z Q P' :=
  tendstoInDistribution_congr_limit_law
    (tendstoInDistribution_of_tight_of_fidiLin hX htight W hfidi) hZ
    (by rw [Measure.map_id, hZW])

/-- Single-probability-space form of `tendstoInDistribution_of_tight_of_fidiLin`:
`Xₙ : Ω → C([0,1], ℝ)` under one probability measure `Q`. -/
theorem tendstoInDistribution_of_tight_of_fidiLin_single [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {X : ℕ → Ω → C(unitInterval, ℝ)} (hX : ∀ n, AEMeasurable (X n) Q)
    (htight : IsTightMeasureSet (Set.range fun n => Q.map (X n)))
    (W : Measure C(unitInterval, ℝ)) [IsProbabilityMeasure W]
    (hfidi : ∀ (k : ℕ) (t : Fin k → unitInterval) (c : Fin k → ℝ),
      TendstoInDistribution (fun n => fidiLin t c ∘ X n) atTop (fidiLin t c) (fun _ => Q) W) :
    TendstoInDistribution X atTop id (fun _ => Q) W :=
  tendstoInDistribution_of_tight_of_fidiLin (Q := fun _ => Q) hX htight W hfidi

/-- **Assembly for normalised polygonal partial-sum processes.** Let `S : ℕ → Ω → ℝ` be measurable
with `S 0 = 0`, satisfying the block condition of `modulus_condition_polygonal_of_blocks`, and let
`W` be a probability measure on the path space such that every linear fidi of
`Xₙ = polygonal n (n^{-1/2} S)` converges in distribution to the same fidi under `W`. Then
`Xₙ ⇒ W`. -/
theorem tendstoInDistribution_polygonal_of_blocks [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {S : ℕ → Ω → ℝ} (hSm : ∀ k, Measurable (S k))
    (hS0 : ∀ ω, S 0 ω = 0)
    (hS : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ≥0∞, 0 < η → ∃ m : ℕ, 0 < m ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ j : ℕ,
      (m : ℝ≥0∞) * Q {ω | ∃ i ≤ n / m + 1, ε * √(n : ℝ) ≤ |S (j + i) ω - S j ω|} ≤ η)
    (W : Measure C(unitInterval, ℝ)) [IsProbabilityMeasure W]
    (hfidi : ∀ (k : ℕ) (t : Fin k → unitInterval) (c : Fin k → ℝ),
      TendstoInDistribution
        (fun (n : ℕ) ω => fidiLin t c (polygonal n (fun j => (√(n : ℝ))⁻¹ * S j ω))) atTop
        (fidiLin t c) (fun _ => Q) W) :
    TendstoInDistribution (fun (n : ℕ) ω => polygonal n (fun j => (√(n : ℝ))⁻¹ * S j ω))
      atTop id (fun _ => Q) W :=
  tendstoInDistribution_of_tight_of_fidiLin_single
    (fun n => (measurable_polygonal_comp (fun k => (hSm k).const_mul _) n).aemeasurable)
    (isTightMeasureSet_polygonal_of_blocks Q hSm hS0 hS) W hfidi

/-- The functional `f ↦ f 1` (the endpoint `u(1)` of MT §17.4) is continuous. -/
theorem continuous_eval_one_C01 : Continuous fun f : C(unitInterval, ℝ) => f 1 :=
  continuous_eval_const 1

/-- The supremum functional `supPath f = sup_t f t` (the functional `max u` of MT §17.4). -/
noncomputable def supPath (f : C(unitInterval, ℝ)) : ℝ := ⨆ t, f t

/-- `f t ≤ supPath f`. -/
theorem le_supPath (f : C(unitInterval, ℝ)) (t : unitInterval) : f t ≤ supPath f :=
  le_ciSup (isCompact_range f.continuous).bddAbove t

/-- `supPath f ≤ C` iff `f t ≤ C` for all `t`. -/
theorem supPath_le_iff (f : C(unitInterval, ℝ)) {C : ℝ} : supPath f ≤ C ↔ ∀ t, f t ≤ C :=
  ⟨fun h t => (le_supPath f t).trans h, fun h => ciSup_le h⟩

/-- The supremum is attained: `supPath f = f t₀` for some `t₀`. -/
theorem exists_supPath_eq (f : C(unitInterval, ℝ)) : ∃ t₀, supPath f = f t₀ := by
  obtain ⟨t₀, -, ht₀⟩ := isCompact_univ.exists_isMaxOn univ_nonempty f.continuous.continuousOn
  exact ⟨t₀, le_antisymm ((supPath_le_iff f).mpr fun t => ht₀ (mem_univ t)) (le_supPath f t₀)⟩

/-- `|supPath f − supPath g| ≤ ‖f − g‖`. -/
theorem abs_supPath_sub_le (f g : C(unitInterval, ℝ)) : |supPath f - supPath g| ≤ ‖f - g‖ := by
  have hb : ∀ (f g : C(unitInterval, ℝ)), supPath f ≤ supPath g + ‖f - g‖ := by
    intro f g
    refine (supPath_le_iff f).mpr fun t => ?_
    have h1 := (f - g).norm_coe_le_norm t
    rw [ContinuousMap.sub_apply, Real.norm_eq_abs] at h1
    have h2 := le_supPath g t
    linarith [le_abs_self (f t - g t)]
  rw [abs_sub_le_iff]
  constructor
  · linarith [hb f g]
  · have := hb g f
    rw [← norm_neg (g - f), neg_sub] at this
    linarith

/-- The supremum functional is continuous on `C([0,1], ℝ)`. -/
theorem continuous_supPath : Continuous supPath := by
  refine Metric.continuous_iff.mpr fun f ε hε => ⟨ε, hε, fun g hg => ?_⟩
  rw [Real.dist_eq]
  rw [dist_eq_norm] at hg
  exact (abs_supPath_sub_le g f).trans_lt hg

/-- **Continuous mapping, endpoint**: if `Xₙ ⇒ Z` in `C([0,1], ℝ)` then `Xₙ(1) ⇒ Z(1)`. -/
theorem tendstoInDistribution_eval_one [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {Ω : ℕ → Type*} {mΩ : ∀ n, MeasurableSpace (Ω n)}
    {Q : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (Q n)]
    {X : ∀ n, Ω n → C(unitInterval, ℝ)} {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Z : Ω' → C(unitInterval, ℝ)}
    (h : TendstoInDistribution X atTop Z Q P') :
    TendstoInDistribution (fun n ω => X n ω 1) atTop (fun ω => Z ω 1) Q P' :=
  h.continuous_comp (g := fun f : C(unitInterval, ℝ) => f 1) continuous_eval_one_C01

/-- **Continuous mapping, supremum**: if `Xₙ ⇒ Z` in `C([0,1], ℝ)` then
`sup_t Xₙ(t) ⇒ sup_t Z(t)`. -/
theorem tendstoInDistribution_supPath [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {Ω : ℕ → Type*} {mΩ : ∀ n, MeasurableSpace (Ω n)}
    {Q : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (Q n)]
    {X : ∀ n, Ω n → C(unitInterval, ℝ)} {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Z : Ω' → C(unitInterval, ℝ)}
    (h : TendstoInDistribution X atTop Z Q P') :
    TendstoInDistribution (fun n ω => supPath (X n ω)) atTop (fun ω => supPath (Z ω)) Q P' :=
  h.continuous_comp (g := supPath) continuous_supPath

/-- **Converging together** (Billingsley, Thm 3.1) in `C([0,1], ℝ)`: if `Xₙ ⇒ Z` and
`‖Yₙ − Xₙ‖ → 0` in probability (all on one probability space), then `Yₙ ⇒ Z`. A thin wrapper of
Mathlib's `tendstoInDistribution_of_tendstoInMeasure_sub`. -/
theorem tendstoInDistribution_of_norm_sub_tendsto [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {X Y : ℕ → Ω → C(unitInterval, ℝ)} {Z : Ω' → C(unitInterval, ℝ)}
    (hXZ : TendstoInDistribution X atTop Z (fun _ => Q) P')
    (hXY : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => Q {ω | ε ≤ ‖Y n ω - X n ω‖}) atTop (𝓝 0))
    (hY : ∀ n, AEMeasurable (Y n) Q) :
    TendstoInDistribution Y atTop Z (fun _ => Q) P' := by
  refine tendstoInDistribution_of_tendstoInMeasure_sub Y Z hXZ ?_ hY
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  simp only [Pi.sub_apply, Pi.zero_apply, sub_zero]
  exact hXY ε hε

/-- Converging together, almost-sure form: if `Xₙ ⇒ Z` and `‖Yₙ − Xₙ‖ → 0` almost surely, then
`Yₙ ⇒ Z`. -/
theorem tendstoInDistribution_of_ae_norm_sub_tendsto [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {X Y : ℕ → Ω → C(unitInterval, ℝ)} {Z : Ω' → C(unitInterval, ℝ)}
    (hXZ : TendstoInDistribution X atTop Z (fun _ => Q) P')
    (hXY : ∀ᵐ ω ∂Q, Tendsto (fun n => ‖Y n ω - X n ω‖) atTop (𝓝 0))
    (hY : ∀ n, AEMeasurable (Y n) Q) :
    TendstoInDistribution Y atTop Z (fun _ => Q) P' := by
  have hX := hXZ.forall_aemeasurable
  refine tendstoInDistribution_of_tendstoInMeasure_sub Y Z hXZ ?_ hY
  refine tendstoInMeasure_of_tendsto_ae (fun n => ((hY n).sub (hX n)).aestronglyMeasurable) ?_
  filter_upwards [hXY] with ω hω
  rw [Pi.zero_apply]
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Pi.sub_apply] using hω)

/-- **Fidis of polygonal processes from step values.** Let `S : ℕ → Ω → ℝ` be measurable, and
suppose the linear combinations `Σ c i · n^{-1/2} S ⌊n t i⌋` of step values converge in
distribution to `Z`, and that single normalised increments are negligible:
`n^{-1/2} (S (⌊nτ⌋+1) − S ⌊nτ⌋) → 0` in probability for each `τ ∈ [0,1]`. Then the linear fidi
`fidiLin t c` of `polygonal n (n^{-1/2} S)` converges in distribution to `Z` (converging together
with `abs_fidiLin_polygonal_sub_le`). -/
theorem tendstoInDistribution_fidiLin_polygonal_of_steps [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {S : ℕ → Ω → ℝ} (hSm : ∀ k, Measurable (S k)) {k : ℕ}
    (t : Fin k → unitInterval) (c : Fin k → ℝ) {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → ℝ}
    (hstep : TendstoInDistribution
      (fun (n : ℕ) ω => ∑ i, c i * ((√(n : ℝ))⁻¹ * S ⌊(n : ℝ) * t i⌋₊ ω)) atTop Z
      (fun _ => Q) P')
    (hinc : ∀ τ : unitInterval, ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => Q {ω | ε ≤
      |(√(n : ℝ))⁻¹ * (S (⌊(n : ℝ) * τ⌋₊ + 1) ω - S ⌊(n : ℝ) * τ⌋₊ ω)|}) atTop (𝓝 0)) :
    TendstoInDistribution
      (fun (n : ℕ) ω => fidiLin t c (polygonal n (fun j => (√(n : ℝ))⁻¹ * S j ω))) atTop Z
      (fun _ => Q) P' := by
  set Y : ℕ → Ω → ℝ := fun n ω => fidiLin t c (polygonal n (fun j => (√(n : ℝ))⁻¹ * S j ω))
  set X : ℕ → Ω → ℝ := fun n ω => ∑ i, c i * ((√(n : ℝ))⁻¹ * S ⌊(n : ℝ) * t i⌋₊ ω)
  have hY : ∀ n, AEMeasurable (Y n) Q := fun n =>
    ((measurable_fidiLin t c).comp
      (measurable_polygonal_comp (fun j => (hSm j).const_mul _) n)).aemeasurable
  refine tendstoInDistribution_of_tendstoInMeasure_sub Y Z hstep ?_ hY
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  set inc : Fin k → ℕ → Ω → ℝ := fun i n ω =>
    (√(n : ℝ))⁻¹ * (S (⌊(n : ℝ) * t i⌋₊ + 1) ω - S ⌊(n : ℝ) * t i⌋₊ ω)
  set ε' : Fin k → ℝ := fun i => ε / (k * (|c i| + 1))
  have hk : ∀ i : Fin k, (0 : ℝ) < k := fun i => by exact_mod_cast Fin.pos i
  have hε' : ∀ i, 0 < ε' i := fun i => by
    have := hk i
    positivity
  have hsub : ∀ n, {ω | ε ≤ ‖(Y - X) n ω - (0 : ℕ → Ω → ℝ) n ω‖} ⊆
      ⋃ i ∈ (Finset.univ : Finset (Fin k)), {ω | ε' i ≤ |inc i n ω|} := by
    intro n ω hω
    rw [mem_ofPred_eq, Pi.sub_apply, Pi.sub_apply, Pi.zero_apply, Pi.zero_apply, sub_zero,
      Real.norm_eq_abs] at hω
    have hb := abs_fidiLin_polygonal_sub_le t c n (fun j => (√(n : ℝ))⁻¹ * S j ω)
    have hb' : ε ≤ ∑ i, |c i| * |inc i n ω| := by
      refine hω.trans (le_of_eq_of_le ?_ (hb.trans (le_of_eq ?_)))
      · rfl
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp only [inc, mul_sub]
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      rw [Finset.univ_eq_empty, Finset.sum_empty] at hb'
      exact absurd hb' (not_le.mpr hε)
    · have hne : (Finset.univ : Finset (Fin k)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hk0⟩⟩
      have hsum : ∑ _i : Fin k, ε / k ≤ ∑ i, |c i| * |inc i n ω| := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have : (k : ℝ) * (ε / k) = ε := mul_div_cancel₀ ε (by exact_mod_cast hk0.ne')
        rw [this]
        exact hb'
      obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le hne hsum
      refine mem_biUnion (Finset.mem_univ i) ?_
      rw [mem_ofPred_eq]
      have hci : |c i| * |inc i n ω| ≤ (|c i| + 1) * |inc i n ω| :=
        mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      have hpos : (0 : ℝ) < |c i| + 1 := by positivity
      change ε / (k * (|c i| + 1)) ≤ |inc i n ω|
      rw [div_le_iff₀ (mul_pos (hk i) hpos)]
      have h1 : ε / k ≤ (|c i| + 1) * |inc i n ω| := hi.trans hci
      rw [div_le_iff₀ (hk i)] at h1
      nlinarith
  have hlim : Tendsto (fun n => ∑ i ∈ (Finset.univ : Finset (Fin k)),
      Q {ω | ε' i ≤ |inc i n ω|}) atTop (𝓝 0) := by
    rw [← Finset.sum_const_zero (s := (Finset.univ : Finset (Fin k)))]
    exact tendsto_finsetSum _ fun i _ => hinc (t i) (ε' i) (hε' i)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => zero_le) fun n => ?_
  exact (measure_mono (hsub n)).trans (measure_biUnion_finset_le _ _)

end MeynTweedie.LimitTheorems
