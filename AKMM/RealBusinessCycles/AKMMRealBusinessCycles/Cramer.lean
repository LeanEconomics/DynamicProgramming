/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMRealBusinessCycles.SpectralDensity
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# The spectral representation

AKMM, §14.3.1, pp. 412–413 (a result beyond the text): the spectral representation theorem
(Cramér) in its Hilbert-space form.

Let `X : ℤ → H` (a complex Hilbert space) satisfy `⟪Xₛ, Xₜ⟫ = ∫ e_{t−s} dF` for a finite measure
`F` on the circle, as every weakly stationary process does (`sden_spectral`).

* The exponentials `eₜ ∈ L²(F)` (`cramExp`) have the same Gram matrix (`cram_inner_exp`) and span a
  dense subspace (`cram_dense`), so `eₜ ↦ Xₜ` extends to a linear isometry
  `V : L²(F) → H` (**the Kolmogorov isometry**, `cramIso`, `cram_iso_exp`, `cram_iso_inner`),
  unique (`cram_iso_unique`), whose range is the closed linear span `H_X` of the process
  (`cram_iso_range`).
* The random measure `Z(A) = V(1_A)` (`cramZ`) has orthogonal increments:
  `⟪Z(A), Z(B)⟫ = F(A ∩ B)` (`cram_Z_inner`), `‖Z(A)‖² = F(A)` (`cram_Z_norm_sq`), `Z(A) ⊥ Z(B)`
  for disjoint `A`, `B` (`cram_Z_orth`), `Z(A ∪ B) = Z(A) + Z(B)` (`cram_Z_union`),
  `Z(𝕋) = X₀` (`cram_Z_univ`).
* `cram_spectral_representation` packages the theorem for weakly stationary processes.

In stochastic-integral notation `Xₜ = ∫ e^{itω} dZ(ω)`: the integral of a step function
`Σ aₖ1_{Aₖ}` against `Z` is `Σ aₖZ(Aₖ) = V(Σ aₖ1_{Aₖ})`, and `V` is its isometric extension to
`L²(F)`, so `∫ e^{itω} dZ(ω) = V(eₜ) = Xₜ`. The notation itself is not formalised. For a real
process `F` is symmetric (`herg_symm_of_real`), and pairing `ω` with `−ω` gives the book's real
form `Yₜ = ∫_{[0,π]} cos(ωt) dU(ω) + ∫_{(0,π]} sin(ωt) dW(ω)` with orthogonal real random
measures `U`, `W`; the book's `A(ω)dω`, `B(ω)dω` stand for `dU`, `dW` (which are given by
densities only in special cases).
-/

namespace AKMM.RealBusinessCycles

open Complex MeasureTheory AddCircle Filter Topology
open scoped ComplexConjugate InnerProductSpace

variable {T : ℝ} [Fact (0 < T)] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The exponential `eₜ(x) = e^{2πitx/T}` as an element of `L²(F)`. -/
noncomputable def cramExp (F : Measure (AddCircle T)) [IsFiniteMeasure F] (t : ℤ) :
    Lp ℂ 2 F :=
  ContinuousMap.toLp 2 F ℂ (fourier t)

/-- `⟪eₛ, eₜ⟫_{L²(F)} = ∫ e_{t−s} dF`. -/
theorem cram_inner_exp (F : Measure (AddCircle T)) [IsFiniteMeasure F] (s t : ℤ) :
    ⟪cramExp F s, cramExp F t⟫_ℂ = ∫ x, fourier (t - s) x ∂F := by
  unfold cramExp
  rw [ContinuousMap.inner_toLp]
  congr 1
  funext x
  rw [← fourier_neg, sub_eq_add_neg, fourier_add]

/-- The exponentials span a dense subspace of `L²(F)` for every finite measure `F` on the
circle. -/
theorem cram_dense (F : Measure (AddCircle T)) [IsFiniteMeasure F] :
    (Submodule.span ℂ (Set.range (cramExp F))).topologicalClosure = ⊤ := by
  convert!
    (ContinuousMap.toLp_denseRange ℂ F ℂ (p := 2) (by simp)).topologicalClosure_map_submodule
      span_fourier_closure_eq_top
  rw [Submodule.map_span]
  unfold cramExp
  rw [Set.range_comp']
  simp only [ContinuousLinearMap.coe_coe]

theorem cram_denseRange (F : Measure (AddCircle T)) [IsFiniteMeasure F] :
    DenseRange (Finsupp.linearCombination ℂ (cramExp F)) := by
  have : Set.range ⇑(Finsupp.linearCombination ℂ (cramExp F)) =
      (Submodule.span ℂ (Set.range (cramExp F)) : Set (Lp ℂ 2 F)) := by
    rw [← LinearMap.coe_range, Finsupp.range_linearCombination]
  rw [DenseRange, this, Submodule.dense_iff_topologicalClosure_eq_top]
  exact cram_dense F

/-- If `⟪Xₛ, Xₜ⟫ = ∫ e_{t−s} dF`, then `‖Σ cₜXₜ‖ = ‖Σ cₜeₜ‖_{L²(F)}`. -/
theorem cram_norm_eq (F : Measure (AddCircle T)) [IsFiniteMeasure F] (X : ℤ → H)
    (hX : ∀ s t, ⟪X s, X t⟫_ℂ = ∫ x, fourier (t - s) x ∂F) (c : ℤ →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ X c‖ = ‖Finsupp.linearCombination ℂ (cramExp F) c‖ := by
  have key : ⟪Finsupp.linearCombination ℂ X c, Finsupp.linearCombination ℂ X c⟫_ℂ =
      ⟪Finsupp.linearCombination ℂ (cramExp F) c,
        Finsupp.linearCombination ℂ (cramExp F) c⟫_ℂ := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right, hX, cram_inner_exp]
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), key]

variable [CompleteSpace H]

/-- AKMM, pp. 412–413 (beyond the text). **The Kolmogorov isometry.** If `⟪Xₛ, Xₜ⟫ = ∫ e_{t−s} dF`,
the map `eₜ ↦ Xₜ` extends to a linear isometry `V : L²(F) → H`. -/
noncomputable def cramIso (F : Measure (AddCircle T)) [IsFiniteMeasure F] (X : ℤ → H)
    (hX : ∀ s t, ⟪X s, X t⟫_ℂ = ∫ x, fourier (t - s) x ∂F) : Lp ℂ 2 F →ₗᵢ[ℂ] H :=
  (Finsupp.linearCombination ℂ X).extendOfIsometry (cram_denseRange F) (cram_norm_eq F X hX)

/-- `V(eₜ) = Xₜ` for every `t`. -/
theorem cram_iso_exp (F : Measure (AddCircle T)) [IsFiniteMeasure F] (X : ℤ → H)
    (hX : ∀ s t, ⟪X s, X t⟫_ℂ = ∫ x, fourier (t - s) x ∂F) (t : ℤ) :
    cramIso F X hX (cramExp F t) = X t := by
  have := LinearMap.extendOfIsometry_eq (f := Finsupp.linearCombination ℂ X)
    (cram_denseRange F) (cram_norm_eq F X hX) (Finsupp.single t 1)
  simp only [Finsupp.linearCombination_single, one_smul] at this
  exact this

/-- `V` preserves inner products: `⟪Vf, Vg⟫_H = ∫ ḡ… = ⟪f, g⟫_{L²(F)}`. -/
theorem cram_iso_inner (F : Measure (AddCircle T)) [IsFiniteMeasure F] (X : ℤ → H)
    (hX : ∀ s t, ⟪X s, X t⟫_ℂ = ∫ x, fourier (t - s) x ∂F) (f g : Lp ℂ 2 F) :
    ⟪cramIso F X hX f, cramIso F X hX g⟫_ℂ = ⟪f, g⟫_ℂ :=
  LinearIsometry.inner_map_map _ _ _

/-- **Uniqueness of the Kolmogorov isometry**: it is the only linear isometry with
`V(eₜ) = Xₜ` for all `t`. -/
theorem cram_iso_unique (F : Measure (AddCircle T)) [IsFiniteMeasure F] (X : ℤ → H)
    (hX : ∀ s t, ⟪X s, X t⟫_ℂ = ∫ x, fourier (t - s) x ∂F) (V : Lp ℂ 2 F →ₗᵢ[ℂ] H)
    (hV : ∀ t, V (cramExp F t) = X t) : V = cramIso F X hX := by
  refine (LinearMap.extendOfIsometry_unique _ (cram_denseRange F) (cram_norm_eq F X hX) V
    (Finsupp.lhom_ext fun t a => ?_)).symm
  simp [Finsupp.linearCombination_single, hV]

/-- **The range of the Kolmogorov isometry** is the closed linear span `H_X` of the process:
`V` maps `L²(F)` onto `H_X`. -/
theorem cram_iso_range (F : Measure (AddCircle T)) [IsFiniteMeasure F] (X : ℤ → H)
    (hX : ∀ s t, ⟪X s, X t⟫_ℂ = ∫ x, fourier (t - s) x ∂F) :
    LinearMap.range (cramIso F X hX).toLinearMap =
      (Submodule.span ℂ (Set.range X)).topologicalClosure := by
  set V := cramIso F X hX
  have hmap : (Submodule.span ℂ (Set.range (cramExp F))).map V.toLinearMap =
      Submodule.span ℂ (Set.range X) := by
    have e : (V.toLinearMap ∘ cramExp F) = X := funext fun t => cram_iso_exp F X hX t
    rw [Submodule.map_span, ← Set.range_comp, e]
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    have hf : f ∈ closure (Submodule.span ℂ (Set.range (cramExp F)) : Set (Lp ℂ 2 F)) := by
      rw [← Submodule.topologicalClosure_coe, cram_dense]
      trivial
    have h1 := image_closure_subset_closure_image V.continuous ⟨f, hf, rfl⟩
    change V f ∈ ((Submodule.span ℂ (Set.range X)).topologicalClosure : Set H)
    rw [Submodule.topologicalClosure_coe]
    refine closure_mono ?_ h1
    rintro _ ⟨g, hg, rfl⟩
    rw [← hmap]
    exact ⟨g, hg, rfl⟩
  · refine Submodule.topologicalClosure_minimal _ ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨t, rfl⟩
      exact ⟨cramExp F t, cram_iso_exp F X hX t⟩
    · rw [LinearMap.coe_range]
      exact V.isometry.isClosedEmbedding.isClosed_range

/-- The orthogonal-increment random measure `Z(A) = V(1_A) ∈ H` (so that, formally,
`Xₜ = ∫ e^{itω} dZ(ω)`). -/
noncomputable def cramZ (F : Measure (AddCircle T)) [IsFiniteMeasure F] (X : ℤ → H)
    (hX : ∀ s t, ⟪X s, X t⟫_ℂ = ∫ x, fourier (t - s) x ∂F) (A : Set (AddCircle T))
    (hA : MeasurableSet A) : H :=
  cramIso F X hX (indicatorConstLp 2 hA (measure_ne_top F A) (1 : ℂ))

/-- **Orthogonal increments**: `⟪Z(A), Z(B)⟫ = F(A ∩ B)`. -/
theorem cram_Z_inner (F : Measure (AddCircle T)) [IsFiniteMeasure F] (X : ℤ → H)
    (hX : ∀ s t, ⟪X s, X t⟫_ℂ = ∫ x, fourier (t - s) x ∂F) {A B : Set (AddCircle T)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ⟪cramZ F X hX A hA, cramZ F X hX B hB⟫_ℂ = (F.real (A ∩ B) : ℂ) := by
  unfold cramZ
  rw [cram_iso_inner, L2.inner_indicatorConstLp_one_indicatorConstLp_one]
  rfl

/-- `E|Z(A)|² = ‖Z(A)‖² = F(A)`. -/
theorem cram_Z_norm_sq (F : Measure (AddCircle T)) [IsFiniteMeasure F] (X : ℤ → H)
    (hX : ∀ s t, ⟪X s, X t⟫_ℂ = ∫ x, fourier (t - s) x ∂F) {A : Set (AddCircle T)}
    (hA : MeasurableSet A) : ‖cramZ F X hX A hA‖ ^ 2 = F.real A := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), cram_Z_inner, Set.inter_self]
  simp

/-- Increments over disjoint sets are orthogonal. -/
theorem cram_Z_orth (F : Measure (AddCircle T)) [IsFiniteMeasure F] (X : ℤ → H)
    (hX : ∀ s t, ⟪X s, X t⟫_ℂ = ∫ x, fourier (t - s) x ∂F) {A B : Set (AddCircle T)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Disjoint A B) :
    ⟪cramZ F X hX A hA, cramZ F X hX B hB⟫_ℂ = 0 := by
  rw [cram_Z_inner, Set.disjoint_iff_inter_eq_empty.1 hAB]
  simp

/-- `Z` is additive: `Z(A ∪ B) = Z(A) + Z(B)` for disjoint `A`, `B`. -/
theorem cram_Z_union (F : Measure (AddCircle T)) [IsFiniteMeasure F] (X : ℤ → H)
    (hX : ∀ s t, ⟪X s, X t⟫_ℂ = ∫ x, fourier (t - s) x ∂F) {A B : Set (AddCircle T)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Disjoint A B) :
    cramZ F X hX (A ∪ B) (hA.union hB) = cramZ F X hX A hA + cramZ F X hX B hB := by
  unfold cramZ
  rw [indicatorConstLp_disjoint_union hA hB (measure_ne_top F A) (measure_ne_top F B) hAB,
    map_add]

/-- `Z(𝕋) = X₀`: the total increment is the value at time `0`. -/
theorem cram_Z_univ (F : Measure (AddCircle T)) [IsFiniteMeasure F] (X : ℤ → H)
    (hX : ∀ s t, ⟪X s, X t⟫_ℂ = ∫ x, fourier (t - s) x ∂F) :
    cramZ F X hX Set.univ MeasurableSet.univ = X 0 := by
  rw [← cram_iso_exp F X hX 0]
  unfold cramZ
  congr 1
  refine Lp.ext ?_
  filter_upwards [indicatorConstLp_coeFn (p := 2) (μ := F) (s := Set.univ)
    (hs := MeasurableSet.univ) (hμs := measure_ne_top F _) (c := (1 : ℂ)),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ := F) (fourier (T := T) 0)] with x h1 h2
  rw [cramExp, h1, h2, fourier_zero]
  simp

/-- AKMM, pp. 412–413 (beyond the text). **The spectral representation theorem (Cramér),
Hilbert-space form.** A weakly stationary
process `X : ℤ → H` with autocovariance `γ` has a finite spectral measure `F` on the circle, and
there is a linear isometry `V` of `L²(F)` onto the closed linear span `H_X` of the process with
`V(eₜ) = Xₜ` for all `t`; it is unique (`cram_iso_unique`) and `Z(A) = V(1_A)` has orthogonal
increments with `‖Z(A)‖² = F(A)` (`cram_Z_inner`, `cram_Z_norm_sq`). -/
theorem cram_spectral_representation {X : ℤ → H} {γ : ℤ → ℂ} (hX : sdenStationary X γ) :
    ∃ F : Measure (AddCircle T), ∃ _ : IsFiniteMeasure F, (∀ h, γ h = ∫ x, fourier h x ∂F) ∧
      ∃ V : Lp ℂ 2 F →ₗᵢ[ℂ] H, (∀ t, V (cramExp F t) = X t) ∧
        LinearMap.range V.toLinearMap = (Submodule.span ℂ (Set.range X)).topologicalClosure := by
  obtain ⟨F, hF, hγ, hXF⟩ := sden_spectral (T := T) hX
  exact ⟨F, hF, hγ, cramIso F X hXF, cram_iso_exp F X hXF, cram_iso_range F X hXF⟩

end AKMM.RealBusinessCycles
