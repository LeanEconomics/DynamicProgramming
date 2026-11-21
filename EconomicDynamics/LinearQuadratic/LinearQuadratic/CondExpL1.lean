/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LinearQuadratic.Basics
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Process.Filtration

/-!
# The conditional expectations of `L¹(Ω, F, Pr)` given a filtration

Copied from `EconomicDynamics/RationalExpectations` (module `CondExpL1`), namespace renamed.

Miao, Chapter 2, p. 45 (the probability space `(Ω, F, Pr)`, the filtration `{F_t}` and `E_t`)
and Definition 2.3.1, p. 52. For a finite measure `μ` on `(Ω, m0)` and a filtration
`ℱ : Filtration ℕ m0`, Mathlib's `L¹` conditional expectation `condExpL1CLM` given `ℱ t` is a
`CondExpSystem` on `Ω →₁[μ] 𝕜`, for any `RCLike` scalar field `𝕜`:

* `condExpSystemL1 𝕜 ℱ μ : CondExpSystem 𝕜 (Ω →₁[μ] 𝕜)`, in particular for `𝕜 = ℝ`
  (`condExpSystemL1_real`) and for `𝕜 = ℂ` (`condExpSystemL1_complex`, the field used in the
  Klein and Sims theorems). `E_t` is `𝕜`-linear (`condExpL1CLM_smul`), `‖E_t‖ ≤ 1`
  (`condExpL1_norm_apply_le`, from `integral_norm_condExp_le`) and the tower property holds
  both ways (`condExpL1_tower_le`, `condExpL1_tower_ge`).
* Interpretation: `E_t X` agrees a.e. with `μ[X | ℱ t]` (`condExpL1_ae_eq_condExp`);
  `E_t X = X` iff `X` is a.e. equal to an `ℱ t`-strongly measurable function
  (`condExpL1_eq_self_iff`, `condExpL1_eq_self_iff_exists`), so `IsAdaptedV` is adaptedness;
  `‖X‖ = ∫|X|` (`l1_norm_eq_integral_abs`), so `IsStableProc` on `L¹` is exactly
  Definition 2.3.1's `max_j E|X_j| < M` (`l1_isStableProc_iff`).

Departure: the book's processes are measurable functions; here (as for any `L¹` theory) they
are classes of functions up to `Pr`-null sets.
-/

open MeasureTheory

namespace Miao.LinearQuadratic

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- `‖E X‖ ≤ ‖X‖` for Mathlib's `L¹` conditional expectation (Miao, p. 45). -/
theorem condExpL1_norm_apply_le {𝕜 : Type*} [RCLike 𝕜] (μ : Measure Ω)
    {m : MeasurableSpace Ω} (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (X : Ω →₁[μ] 𝕜) :
    ‖condExpL1CLM 𝕜 hm μ X‖ ≤ ‖X‖ := by
  have hX : Integrable (⇑X) μ := L1.integrable_coeFn X
  have hae := condExp_ae_eq_condExpL1CLM hm hX
  rw [Integrable.toL1_coeFn X hX] at hae
  rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm]
  calc ∫ ω, ‖condExpL1CLM 𝕜 hm μ X ω‖ ∂μ = ∫ ω, ‖(μ[⇑X | m]) ω‖ ∂μ :=
        integral_congr_ae (hae.mono fun ω h => by simp only [h])
    _ ≤ ∫ ω, ‖X ω‖ ∂μ := integral_norm_condExp_le _

/-- `E_t X` agrees a.e. with `μ[X | m]` (Miao, p. 45). -/
theorem condExpL1_ae_eq_condExp {𝕜 : Type*} [RCLike 𝕜] (μ : Measure Ω)
    {m : MeasurableSpace Ω} (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (X : Ω →₁[μ] 𝕜) :
    condExpL1CLM 𝕜 hm μ X =ᵐ[μ] μ[⇑X | m] := by
  have hX : Integrable (⇑X) μ := L1.integrable_coeFn X
  have hae := condExp_ae_eq_condExpL1CLM hm hX
  rw [Integrable.toL1_coeFn X hX] at hae
  exact hae.symm

/-- `E_s E_t = E_s` for `m₁ ≤ m₂` (law of iterated expectations, Miao, p. 45). -/
theorem condExpL1_tower_le {𝕜 : Type*} [RCLike 𝕜] (μ : Measure Ω)
    {m₁ m₂ : MeasurableSpace Ω} (h12 : m₁ ≤ m₂) (hm₂ : m₂ ≤ m0) [SigmaFinite (μ.trim hm₂)]
    [SigmaFinite (μ.trim (h12.trans hm₂))] (X : Ω →₁[μ] 𝕜) :
    condExpL1CLM 𝕜 (h12.trans hm₂) μ (condExpL1CLM 𝕜 hm₂ μ X) =
      condExpL1CLM 𝕜 (h12.trans hm₂) μ X := by
  apply Lp.ext_iff.mpr
  have h1 := condExpL1_ae_eq_condExp μ (h12.trans hm₂) (condExpL1CLM 𝕜 hm₂ μ X)
  have h2 : μ[⇑(condExpL1CLM 𝕜 hm₂ μ X) | m₁] =ᵐ[μ] μ[μ[⇑X | m₂] | m₁] :=
    condExp_congr_ae (condExpL1_ae_eq_condExp μ hm₂ X)
  have h3 : μ[μ[⇑X | m₂] | m₁] =ᵐ[μ] μ[⇑X | m₁] := condExp_condExp_of_le h12 hm₂
  have h4 := condExpL1_ae_eq_condExp μ (h12.trans hm₂) X
  exact h1.trans (h2.trans (h3.trans h4.symm))

/-- `E_t E_s = E_s` for `m₁ ≤ m₂`: `E_s X` is already `m₂`-measurable (Miao, p. 45). -/
theorem condExpL1_tower_ge {𝕜 : Type*} [RCLike 𝕜] (μ : Measure Ω)
    {m₁ m₂ : MeasurableSpace Ω} (h12 : m₁ ≤ m₂) (hm₂ : m₂ ≤ m0) [SigmaFinite (μ.trim hm₂)]
    [SigmaFinite (μ.trim (h12.trans hm₂))] (X : Ω →₁[μ] 𝕜) :
    condExpL1CLM 𝕜 hm₂ μ (condExpL1CLM 𝕜 (h12.trans hm₂) μ X) =
      condExpL1CLM 𝕜 (h12.trans hm₂) μ X :=
  condExpL1CLM_of_aestronglyMeasurable' _
    ((aestronglyMeasurable_condExpL1CLM (hm := h12.trans hm₂) X).mono h12)

/-- `E_t` as a `𝕜`-linear map (`condExpL1CLM` is `𝕜`-homogeneous, `condExpL1CLM_smul`). -/
noncomputable def condExpL1CLMK (𝕜 : Type*) [RCLike 𝕜] (μ : Measure Ω)
    {m : MeasurableSpace Ω} (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] :
    (Ω →₁[μ] 𝕜) →L[𝕜] Ω →₁[μ] 𝕜 where
  toFun := condExpL1CLM 𝕜 hm μ
  map_add' := (condExpL1CLM 𝕜 hm μ).map_add
  map_smul' c X := condExpL1CLM_smul c X
  cont := (condExpL1CLM 𝕜 hm μ).continuous

theorem condExpL1CLMK_apply (𝕜 : Type*) [RCLike 𝕜] (μ : Measure Ω)
    {m : MeasurableSpace Ω} (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (X : Ω →₁[μ] 𝕜) :
    condExpL1CLMK 𝕜 μ hm X = condExpL1CLM 𝕜 hm μ X := rfl

/-- **The concrete instance** (Miao, p. 45): for a finite measure `μ` and a filtration
`ℱ`, `E_t = ` Mathlib's `L¹` conditional expectation given `ℱ t` is a `CondExpSystem` on
`L¹(Ω, F, μ; 𝕜)`. -/
noncomputable def condExpSystemL1 (𝕜 : Type*) [RCLike 𝕜] (ℱ : Filtration ℕ m0)
    (μ : Measure Ω) [IsFiniteMeasure μ] : CondExpSystem 𝕜 (Ω →₁[μ] 𝕜) where
  E t := condExpL1CLMK 𝕜 μ (ℱ.le t)
  norm_le t := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun X => by
    rw [one_mul]
    exact condExpL1_norm_apply_le μ (ℱ.le t) X
  tower_le s t hst := by
    ext1 X
    exact condExpL1_tower_le μ (ℱ.mono hst) (ℱ.le t) X
  tower_ge s t hst := by
    ext1 X
    exact condExpL1_tower_ge μ (ℱ.mono hst) (ℱ.le t) X

theorem condExpSystemL1_E_apply (𝕜 : Type*) [RCLike 𝕜] (ℱ : Filtration ℕ m0)
    (μ : Measure Ω) [IsFiniteMeasure μ] (t : ℕ) (X : Ω →₁[μ] 𝕜) :
    (condExpSystemL1 𝕜 ℱ μ).E t X = condExpL1CLM 𝕜 (ℱ.le t) μ X := rfl

/-- The real instance `CondExpSystem ℝ (Ω →₁[μ] ℝ)` (Miao, p. 45). -/
noncomputable def condExpSystemL1_real (ℱ : Filtration ℕ m0) (μ : Measure Ω)
    [IsFiniteMeasure μ] : CondExpSystem ℝ (Ω →₁[μ] ℝ) :=
  condExpSystemL1 ℝ ℱ μ

/-- The complex instance `CondExpSystem ℂ (Ω →₁[μ] ℂ)`, the setting of the Klein and Sims
theorems (Miao, pp. 55–64). -/
noncomputable def condExpSystemL1_complex (ℱ : Filtration ℕ m0) (μ : Measure Ω)
    [IsFiniteMeasure μ] : CondExpSystem ℂ (Ω →₁[μ] ℂ) :=
  condExpSystemL1 ℂ ℱ μ

/-- Miao, p. 45: `E_t X` agrees a.e. with the conditional expectation `μ[X | ℱ t]`. -/
theorem condExpSystemL1_ae_eq (𝕜 : Type*) [RCLike 𝕜] (ℱ : Filtration ℕ m0)
    (μ : Measure Ω) [IsFiniteMeasure μ] (t : ℕ) (X : Ω →₁[μ] 𝕜) :
    (condExpSystemL1 𝕜 ℱ μ).E t X =ᵐ[μ] μ[⇑X | ℱ t] :=
  condExpL1_ae_eq_condExp μ (ℱ.le t) X

/-- Miao, p. 45 (adaptedness): `E_t X = X` iff `X` is a.e. strongly `ℱ t`-measurable. -/
theorem condExpL1_eq_self_iff (𝕜 : Type*) [RCLike 𝕜] (ℱ : Filtration ℕ m0)
    (μ : Measure Ω) [IsFiniteMeasure μ] (t : ℕ) (X : Ω →₁[μ] 𝕜) :
    (condExpSystemL1 𝕜 ℱ μ).E t X = X ↔ AEStronglyMeasurable[ℱ t] (⇑X) μ := by
  constructor
  · intro h
    have hm := aestronglyMeasurable_condExpL1CLM (hm := ℱ.le t) X
    rw [← condExpSystemL1_E_apply, h] at hm
    exact hm
  · intro h
    exact condExpL1CLM_of_aestronglyMeasurable' X h

/-- Miao, p. 45: `E_t X = X` iff `X` has an `ℱ t`-strongly measurable representative. -/
theorem condExpL1_eq_self_iff_exists (𝕜 : Type*) [RCLike 𝕜] (ℱ : Filtration ℕ m0)
    (μ : Measure Ω) [IsFiniteMeasure μ] (t : ℕ) (X : Ω →₁[μ] 𝕜) :
    (condExpSystemL1 𝕜 ℱ μ).E t X = X ↔
      ∃ g : Ω → 𝕜, StronglyMeasurable[ℱ t] g ∧ ⇑X =ᵐ[μ] g := by
  rw [condExpL1_eq_self_iff]
  exact ⟨fun h => ⟨h.mk _, h.stronglyMeasurable_mk, h.ae_eq_mk⟩,
    fun ⟨g, hg, hXg⟩ => ⟨g, hg, hXg⟩⟩

/-- Miao, p. 45: a process of `L¹` vectors is adapted (`IsAdaptedV`) iff every component has an
`ℱ t`-strongly measurable representative. -/
theorem condExpL1_isAdaptedV_iff (𝕜 : Type*) [RCLike 𝕜] (ℱ : Filtration ℕ m0)
    (μ : Measure Ω) [IsFiniteMeasure μ] {ι : Type*} (x : ℕ → ι → Ω →₁[μ] 𝕜) :
    IsAdaptedV (condExpSystemL1 𝕜 ℱ μ) x ↔
      ∀ t i, ∃ g : Ω → 𝕜, StronglyMeasurable[ℱ t] g ∧ ⇑(x t i) =ᵐ[μ] g := by
  simp only [IsAdaptedV, condExpL1_eq_self_iff_exists]

/-- Definition 2.3.1 (Miao, p. 52): the `L¹` norm is `E|X|`. -/
theorem l1_norm_eq_integral_abs {μ : Measure Ω} (X : Ω →₁[μ] ℝ) :
    ‖X‖ = ∫ ω, |X ω| ∂μ := by
  rw [L1.norm_eq_integral_norm]
  rfl

/-- **Definition 2.3.1** (Miao, p. 52) on `L¹`: `IsStableProc x` is exactly
`max_j E|x_{t,j}| < M` for all `t`, some `M > 0`. -/
theorem l1_isStableProc_iff {μ : Measure Ω} {ι : Type*} (x : ℕ → ι → Ω →₁[μ] ℝ) :
    IsStableProc x ↔ ∃ M, 0 < M ∧ ∀ t i, ∫ ω, |x t i ω| ∂μ < M := by
  simp only [IsStableProc, l1_norm_eq_integral_abs]

/-- The complex form of Definition 2.3.1 (Miao, p. 52): `‖X‖ = E|X|` on `L¹(Ω; ℂ)`. -/
theorem l1_norm_eq_integral_norm_complex {μ : Measure Ω} (X : Ω →₁[μ] ℂ) :
    ‖X‖ = ∫ ω, ‖X ω‖ ∂μ :=
  L1.norm_eq_integral_norm X

end Miao.LinearQuadratic
