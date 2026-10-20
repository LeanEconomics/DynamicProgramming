/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StrongConvergence.CesaroAverages
import StrongConvergence.DoeblinErgodic

/-!
# Invariant measures on an ergodic set

Three facts about an ergodic set `E` (in the sense of p. 346), used for Theorem 11.9b–c.

* `exists_reach`: every subset `A ⊆ E` of positive `φ`-measure is reached from every point of
  `E`. (Otherwise the points of `E \ A` that never reach `A` form an invariant set of smaller
  `φ`-measure.)
* `pos_of_invariant`: an invariant probability measure concentrated on `E` charges every set
  that meets `E` in positive `φ`-measure; so `φ` restricted to `E` is absolutely continuous with
  respect to it (`absCont_of_concentrated`).
* `invariant_unique`: under Condition D there is at most one invariant probability measure
  concentrated on `E`. For two of them, `π₁`, `π₂`, with Hahn set `H`, the measures
  `(π₁ − π₂)` restricted to `H` and `(π₂ − π₁)` restricted to `Hᶜ` are invariant
  (`posPart_invariant`), mutually singular, and both charge every `φ`-positive part of `E`.
-/

namespace StokeyLucasPrescott.StrongConvergence

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {S : Type*} [MeasurableSpace S] {κ : Kernel S S} [IsMarkovKernel κ]

omit [IsMarkovKernel κ] in
/-- An invariant measure is invariant under every `T*ⁿ`. -/
theorem invariant_iterate {π : Measure S} (hπ : adjointOp κ π = π) (n : ℕ) :
    adjointOp (kpow κ n) π = π := by
  induction n with
  | zero =>
    change π.bind (kpow κ 0) = π
    have : (⇑(kpow κ 0)) = fun z => Measure.dirac z := funext fun z => by
      simp [kpow, Kernel.id_apply]
    rw [this, Measure.bind_dirac]
  | succ n ih => rw [adjoint_add, kpow_one, hπ, ih]

/-- From a point that never reaches `A` (after time `0`), the chain stays where `A` is never
reached. -/
theorem kpow_noReach_eq_one {E A : Set S} (hE : IsInvariantSet κ E) (hA : MeasurableSet A)
    {t : S} (htE : t ∈ E) (ht : ∀ n, 1 ≤ n → kpow κ n t A = 0) (m : ℕ) (hm : 1 ≤ m) :
    kpow κ m t ((E \ A) ∩ ⋂ n : ℕ, {u | kpow κ (n + 1) u A = 0}) = 1 := by
  have := isMarkov_kpow (κ := κ) m
  have hmeasI : ∀ n : ℕ, MeasurableSet {u | kpow κ (n + 1) u A = 0} := fun n =>
    Kernel.measurable_coe (kpow κ (n + 1)) hA (measurableSet_singleton 0)
  refine measure_inter_eq_one (hE.1.diff hA) (MeasurableSet.iInter hmeasI) ?_
    (measure_iInter_eq_one hmeasI fun n => ?_)
  · rw [sdiff_eq_compl_inter, inter_comm]
    exact measure_inter_eq_one hE.1 hA.compl (hE.2.2 t htE m hm)
      (by rw [prob_compl_eq_one_sub hA, ht m hm, tsub_zero])
  · have h0 : ∫⁻ u, kpow κ (n + 1) u A ∂kpow κ m t = 0 := by
      rw [← kpow_add_apply m (n + 1) t hA]; exact ht _ (by omega)
    rw [lintegral_eq_zero_iff (Kernel.measurable_coe _ hA)] at h0
    rw [← prob_compl_eq_zero_iff (hmeasI n)]
    exact ae_iff.1 h0

/-- **Reachability.** In an ergodic set every subset of positive `φ`-measure is reached from
every point. -/
theorem exists_reach {φ : Measure S} [IsFiniteMeasure φ] {E : Set S} (hE : IsErgodicSetD κ φ E)
    {A : Set S} (hA : MeasurableSet A) (hAE : A ⊆ E) (hpos : 0 < φ A) {s : S} (hs : s ∈ E) :
    ∃ n, 1 ≤ n ∧ 0 < kpow κ n s A := by
  by_contra hne
  push Not at hne
  have hzero : ∀ n, 1 ≤ n → kpow κ n s A = 0 := fun n hn => le_antisymm (hne n hn) zero_le
  set G := (E \ A) ∩ ⋂ n : ℕ, {u | kpow κ (n + 1) u A = 0}
  have hGmem : ∀ u ∈ G, u ∈ E ∧ ∀ n, 1 ≤ n → kpow κ n u A = 0 := fun u hu => by
    refine ⟨hu.1.1, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact mem_iInter.1 hu.2 k
  have hGinv : IsInvariantSet κ G := by
    refine ⟨(hE.1.1.diff hA).inter (MeasurableSet.iInter fun n =>
      Kernel.measurable_coe (kpow κ (n + 1)) hA (measurableSet_singleton 0)), ?_, fun u hu m hm =>
        kpow_noReach_eq_one hE.1 hA (hGmem u hu).1 (hGmem u hu).2 m hm⟩
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    have : kpow κ 1 s G = 1 := kpow_noReach_eq_one hE.1 hA hs hzero 1 le_rfl
    rw [hemp, measure_empty] at this
    exact zero_ne_one this
  have hle := hE.2 G (fun u hu => (hGmem u hu).1) hGinv
  have hGsub : G ⊆ E \ A := inter_subset_left
  have h1 : φ G ≤ φ E - φ A := by
    rw [← measure_sdiff hAE hA.nullMeasurableSet (measure_ne_top φ A)]
    exact measure_mono hGsub
  have h2 : φ E - φ A < φ E := ENNReal.sub_lt_self (measure_ne_top φ E)
    (ne_of_gt (lt_of_lt_of_le hpos (measure_mono hAE))) hpos.ne'
  exact absurd (hle.trans h1) (not_le.2 h2)

/-- An invariant probability measure concentrated on an ergodic set `E` charges every set that
meets `E` in positive `φ`-measure. -/
theorem pos_of_invariant {φ : Measure S} [IsFiniteMeasure φ] {E : Set S}
    (hE : IsErgodicSetD κ φ E) {π : Measure S} [IsProbabilityMeasure π] (hπ : adjointOp κ π = π)
    (hπE : π E = 1) {A : Set S} (hA : MeasurableSet A) (hpos : 0 < φ (A ∩ E)) : 0 < π A := by
  by_contra h0
  have h0 : π (A ∩ E) = 0 := measure_mono_null inter_subset_left (le_antisymm (not_lt.1 h0)
    zero_le)
  have hAE : MeasurableSet (A ∩ E) := hA.inter hE.1.1
  have hae : ∀ n : ℕ, ∀ᵐ s ∂π, kpow κ (n + 1) s (A ∩ E) = 0 := fun n => by
    have : ∫⁻ s, kpow κ (n + 1) s (A ∩ E) ∂π = 0 := by
      rw [← adjointOp_apply _ _ hAE, invariant_iterate hπ]; exact h0
    exact (lintegral_eq_zero_iff (Kernel.measurable_coe _ hAE)).1 this
  have hE' : ∀ᵐ s ∂π, s ∈ E := by
    rw [ae_iff, ← compl_def, prob_compl_eq_zero_iff hE.1.1]; exact hπE
  obtain ⟨s, hsE, hs⟩ := (hE'.and (ae_all_iff.2 hae)).exists
  obtain ⟨n, hn, hpos'⟩ := exists_reach hE hAE inter_subset_right hpos hsE
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [hs k] at hpos'
  exact lt_irrefl _ hpos'

/-- A measure absolutely continuous with respect to `φ` and concentrated on the ergodic set `E`
is absolutely continuous with respect to every invariant probability measure on `E`. -/
theorem absCont_of_concentrated {φ : Measure S} [IsFiniteMeasure φ] {E : Set S}
    (hE : IsErgodicSetD κ φ E) {π : Measure S} [IsProbabilityMeasure π] (hπ : adjointOp κ π = π)
    (hπE : π E = 1) {K : Measure S} (hK : K ≪ φ) (hKE : K Eᶜ = 0) : K ≪ π := by
  refine Measure.AbsolutelyContinuous.mk fun A hA hπA => ?_
  have hφ : φ (A ∩ E) = 0 := by
    by_contra hne
    exact absurd hπA (pos_of_invariant hE hπ hπE hA (pos_iff_ne_zero.2 hne)).ne'
  have h1 : K (A ∩ E) = 0 := hK hφ
  have h2 : K (A ∩ Eᶜ) = 0 := measure_mono_null inter_subset_right hKE
  calc K A = K (A ∩ E) + K (A \ E) := (measure_inter_add_sdiff A hE.1.1).symm
    _ = 0 := by rw [Set.sdiff_eq, h1, h2, add_zero]

/-- For invariant probability measures `π₁, π₂` and a Hahn set `H` (`π₂ ≤ π₁` on `H`,
`π₁ ≤ π₂` off `H`), the positive part `(π₁ − π₂)|_H` is invariant. -/
theorem posPart_invariant {π₁ π₂ : Measure S} [IsProbabilityMeasure π₁] [IsProbabilityMeasure π₂]
    (h₁ : adjointOp κ π₁ = π₁) (h₂ : adjointOp κ π₂ = π₂) {H : Set S} (hH : MeasurableSet H)
    (hle : π₂.restrict H ≤ π₁.restrict H) (hle' : π₁.restrict Hᶜ ≤ π₂.restrict Hᶜ) :
    adjointOp κ (π₁.restrict H - π₂.restrict H) = π₁.restrict H - π₂.restrict H := by
  set α := π₁.restrict H - π₂.restrict H
  have hα : α + π₂.restrict H = π₁.restrict H := Measure.sub_add_cancel_of_le hle
  have hαfin : IsFiniteMeasure α := by
    refine ⟨lt_of_le_of_lt ?_ (measure_lt_top (π₁.restrict H) univ)⟩
    rw [← hα]; exact le_add_right le_rfl
  have hPfin : IsFiniteMeasure (adjointOp κ α) := by
    have := isFinite_adjoint (κ := κ) 1 α; rwa [kpow_one] at this
  have hαreal : ∀ A, MeasurableSet A →
      α.real A = π₁.real (A ∩ H) - π₂.real (A ∩ H) := fun A hA => by
    have := congrArg (fun μ : Measure S => μ.real A) hα
    rw [measureReal_add_apply, measureReal_restrict_apply hA,
      measureReal_restrict_apply hA] at this
    linarith
  -- `(αP)(A) ≥ π₁(A) − π₂(A)`
  have hint : ∀ A, MeasurableSet A → π₁.real A - π₂.real A ≤ (adjointOp κ α).real A := by
    intro A hA
    set f : S → ℝ := fun s => (κ s).real A
    have hfm : Measurable f := (κ.measurable_coe hA).ennreal_toReal
    have hf01 : ∀ s, 0 ≤ f s ∧ f s ≤ 1 := fun s => ⟨measureReal_nonneg, measureReal_le_one⟩
    have hfi : ∀ (μ : Measure S) [IsFiniteMeasure μ], Integrable f μ := fun μ _ =>
      integrable_of_abs_le μ hfm (C := 1) fun s => by
        rw [abs_of_nonneg (hf01 s).1]; exact (hf01 s).2
    have e1 : π₁.real A = ∫ s in H, f s ∂π₁ + ∫ s in Hᶜ, f s ∂π₁ := by
      rw [integral_add_compl hH (hfi π₁), ← bind_real_eq κ π₁ hA]
      rw [h₁]
    have e2 : π₂.real A = ∫ s in H, f s ∂π₂ + ∫ s in Hᶜ, f s ∂π₂ := by
      rw [integral_add_compl hH (hfi π₂), ← bind_real_eq κ π₂ hA]
      rw [h₂]
    have e3 : (adjointOp κ α).real A = ∫ s in H, f s ∂π₁ - ∫ s in H, f s ∂π₂ := by
      rw [bind_real_eq κ α hA]
      have := integral_add_measure (hfi α) (hfi (π₂.restrict H)) (f := f)
      rw [hα] at this
      linarith
    have e4 : ∫ s in Hᶜ, f s ∂π₁ ≤ ∫ s in Hᶜ, f s ∂π₂ :=
      integral_mono_measure hle' (Eventually.of_forall fun s => (hf01 s).1) (hfi _)
    linarith
  have hge : ∀ A, MeasurableSet A → α.real A ≤ (adjointOp κ α).real A := by
    intro A hA
    calc α.real A = π₁.real (A ∩ H) - π₂.real (A ∩ H) := hαreal A hA
      _ ≤ (adjointOp κ α).real (A ∩ H) := hint _ (hA.inter hH)
      _ ≤ (adjointOp κ α).real A := measureReal_mono inter_subset_left
  have hmass : (adjointOp κ α).real univ = α.real univ := by
    have := adjointOp_kpow_univ (κ := κ) 1 α; rw [kpow_one] at this
    rw [measureReal_def, this]; rfl
  refine Measure.ext fun A hA => ?_
  have h1 := hge A hA
  have h2 := hge Aᶜ hA.compl
  rw [measureReal_compl hA, measureReal_compl hA, hmass] at h2
  have h3 : (adjointOp κ α).real A = α.real A := le_antisymm (by linarith) h1
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h3

/-- **Uniqueness.** Under Condition D, an ergodic set carries at most one invariant probability
measure. -/
theorem invariant_unique {φ : Measure S} {N : ℕ} {ε : ℝ} (hD : DoeblinFor κ φ N ε) {E : Set S}
    (hE : IsErgodicSetD κ φ E) {π₁ π₂ : Measure S} [IsProbabilityMeasure π₁]
    [IsProbabilityMeasure π₂] (h₁ : adjointOp κ π₁ = π₁) (h₂ : adjointOp κ π₂ = π₂)
    (h₁E : π₁ E = 1) (h₂E : π₂ E = 1) : π₁ = π₂ := by
  have hφ := hD.1
  obtain ⟨H, hH, hHle, hHle'⟩ := hahn_decomposition π₁ π₂
  have hle : π₂.restrict H ≤ π₁.restrict H := Measure.le_iff.2 fun t ht => by
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact hHle _ (ht.inter hH) inter_subset_right
  have hle' : π₁.restrict Hᶜ ≤ π₂.restrict Hᶜ := Measure.le_iff.2 fun t ht => by
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact hHle' _ (ht.inter hH.compl) inter_subset_right
  have hP := posPart_invariant h₁ h₂ hH hle hle'
  have hN := posPart_invariant h₂ h₁ hH.compl hle' (by rw [compl_compl]; exact hle)
  -- the two parts and their masses
  set α := π₁.restrict H - π₂.restrict H
  set β := π₂.restrict Hᶜ - π₁.restrict Hᶜ
  have hα : α + π₂.restrict H = π₁.restrict H := Measure.sub_add_cancel_of_le hle
  have hβ : β + π₁.restrict Hᶜ = π₂.restrict Hᶜ := Measure.sub_add_cancel_of_le hle'
  have hαfin : IsFiniteMeasure α :=
    ⟨lt_of_le_of_lt (by rw [← hα]; exact le_add_right le_rfl) (measure_lt_top (π₁.restrict H) univ)⟩
  have hβfin : IsFiniteMeasure β :=
    ⟨lt_of_le_of_lt (by rw [← hβ]; exact le_add_right le_rfl)
      (measure_lt_top (π₂.restrict Hᶜ) univ)⟩
  have hαH : α Hᶜ = 0 := by
    have := congrArg (fun μ : Measure S => μ Hᶜ) hα
    simp only [Measure.add_apply, Measure.restrict_apply hH.compl, compl_inter_self,
      measure_empty, add_zero] at this
    exact this
  have hβH : β H = 0 := by
    have := congrArg (fun μ : Measure S => μ H) hβ
    simp only [Measure.add_apply, Measure.restrict_apply hH, inter_compl_self,
      measure_empty, add_zero] at this
    exact this
  have hαE : α Eᶜ = 0 := by
    have := congrArg (fun μ : Measure S => μ Eᶜ) hα
    simp only [Measure.add_apply, Measure.restrict_apply hE.1.1.compl] at this
    have h0 : π₁ (Eᶜ ∩ H) = 0 := measure_mono_null inter_subset_left
      ((prob_compl_eq_zero_iff hE.1.1).2 h₁E)
    rw [h0] at this
    exact (add_eq_zero.1 this).1
  have hβE : β Eᶜ = 0 := by
    have := congrArg (fun μ : Measure S => μ Eᶜ) hβ
    simp only [Measure.add_apply, Measure.restrict_apply hE.1.1.compl] at this
    have h0 : π₂ (Eᶜ ∩ Hᶜ) = 0 := measure_mono_null inter_subset_left
      ((prob_compl_eq_zero_iff hE.1.1).2 h₂E)
    rw [h0] at this
    exact (add_eq_zero.1 this).1
  have hmass : α univ = β univ := by
    have ha := congrArg (fun μ : Measure S => μ.real univ) hα
    have hb := congrArg (fun μ : Measure S => μ.real univ) hβ
    rw [measureReal_add_apply, measureReal_restrict_apply MeasurableSet.univ, univ_inter,
      measureReal_restrict_apply MeasurableSet.univ, univ_inter] at ha hb
    have h1 := measureReal_add_measureReal_compl (μ := π₁) hH
    have h2 := measureReal_add_measureReal_compl (μ := π₂) hH
    simp only [probReal_univ] at h1 h2
    have : α.real univ = β.real univ := by linarith
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 this
  -- a nonzero part, normalised, would charge both `H` and `Hᶜ`
  by_cases ha0 : α univ = 0
  · have hα0 : α = 0 := Measure.measure_univ_eq_zero.1 ha0
    have hβ0 : β = 0 := Measure.measure_univ_eq_zero.1 (hmass ▸ ha0)
    rw [hα0, zero_add] at hα
    rw [hβ0, zero_add] at hβ
    ext A hA
    rw [← measure_inter_add_sdiff A hH, ← measure_inter_add_sdiff (μ := π₂) A hH,
      ← Measure.restrict_apply hA, ← Measure.restrict_apply hA, ← hα, Set.sdiff_eq,
      ← Measure.restrict_apply hA, ← Measure.restrict_apply hA, hβ]
  · exfalso
    have hφE : 0 < φ E := by
      have := invariant_real_gt hD hE.1
      exact ENNReal.toReal_pos_iff.1 (lt_trans hD.2.2.1 this) |>.1
    set c := (α univ)⁻¹
    have hc : c ≠ ⊤ := ENNReal.inv_ne_top.2 ha0
    have hαp : IsProbabilityMeasure (c • α) :=
      ⟨by rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel ha0 (measure_ne_top _ _)]⟩
    have hβp : IsProbabilityMeasure (c • β) :=
      ⟨by rw [Measure.smul_apply, smul_eq_mul, ← hmass,
        ENNReal.inv_mul_cancel ha0 (measure_ne_top _ _)]⟩
    have hαinv : adjointOp κ (c • α) = c • α := by rw [adjointOp_smul, hP]
    have hβinv : adjointOp κ (c • β) = c • β := by rw [adjointOp_smul, hN]
    have hαE1 : (c • α) E = 1 := by
      rw [← prob_compl_eq_zero_iff hE.1.1, Measure.smul_apply, hαE, smul_zero]
    have hβE1 : (c • β) E = 1 := by
      rw [← prob_compl_eq_zero_iff hE.1.1, Measure.smul_apply, hβE, smul_zero]
    have hsplit : φ E = φ (H ∩ E) + φ (Hᶜ ∩ E) := by
      rw [inter_comm H, inter_comm Hᶜ, ← Set.sdiff_eq, measure_inter_add_sdiff E hH]
    rcases eq_zero_or_pos (φ (H ∩ E)) with h0 | hpos
    · have hpos' : 0 < φ (Hᶜ ∩ E) := by
        rw [hsplit, h0, zero_add] at hφE; exact hφE
      have := pos_of_invariant hE hαinv hαE1 hH.compl hpos'
      rw [Measure.smul_apply, hαH, smul_zero] at this
      exact lt_irrefl _ this
    · have := pos_of_invariant hE hβinv hβE1 hH hpos
      rw [Measure.smul_apply, hβH, smul_zero] at this
      exact lt_irrefl _ this

end StokeyLucasPrescott.StrongConvergence
