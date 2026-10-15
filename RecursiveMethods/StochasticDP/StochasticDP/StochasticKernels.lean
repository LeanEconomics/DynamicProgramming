/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticDP.TransitionFunctions

/-!
# Stochastic kernels and iterated integrals

SLP §8.3, pp. 225–234. A stochastic kernel on `{X, 𝒴}` (`IsStochasticKernel`) is a Markov
kernel from `X` to `Y` (`isStochasticKernel_iff`). Theorem 8.4 and its corollary
(`theorem_8_4`, `theorem_8_4_cor`); the direct product `P₁ × P₂` of Theorem 8.5 (`directProd`,
`theorem_8_5`, `theorem_8_5_unique`); the iterated integral formula (4) of Theorem 8.6 and its
corollary (`theorem_8_6`, `theorem_8_6_cor`) and Theorem 8.7 for integrable functions
(`theorem_8_7`); and Exercise 8.9 (`ex_8_9a`, `ex_8_9b`).

The book proves Theorems 8.4–8.6 with the Monotone Class Lemma, starting from measurable
rectangles; the same argument, in π-λ form, is Mathlib's for its kernel composition.
-/

namespace StokeyLucasPrescott.StochasticDP

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {W X Y : Type*} [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y]

/-- A **stochastic kernel** on `{X, 𝒴}` (SLP p. 226): each `P(x, ·)` is a probability measure on
`Y` and each `P(·, B)` is measurable. -/
def IsStochasticKernel (P : X → Set Y → ℝ≥0∞) : Prop :=
  (∀ x, ∃ μ : Measure Y, IsProbabilityMeasure μ ∧ ∀ B, MeasurableSet B → μ B = P x B) ∧
    ∀ B, MeasurableSet B → Measurable fun x => P x B

/-- Stochastic kernels are Mathlib's Markov kernels. -/
theorem isStochasticKernel_iff (P : X → Set Y → ℝ≥0∞) :
    IsStochasticKernel P ↔
      ∃ κ : Kernel X Y, IsMarkovKernel κ ∧ ∀ x B, MeasurableSet B → κ x B = P x B := by
  constructor
  · rintro ⟨h1, h2⟩
    choose μ hμ hμP using h1
    have hm : Measurable μ := Measure.measurable_of_measurable_coe _ fun B hB => by
      have : (fun x => μ x B) = fun x => P x B := funext fun x => hμP x B hB
      rw [this]
      exact h2 B hB
    exact ⟨⟨μ, hm⟩, ⟨fun x => hμ x⟩, fun x B hB => hμP x B hB⟩
  · rintro ⟨κ, hκ, hP⟩
    refine ⟨fun x => ⟨κ x, inferInstance, fun B hB => hP x B hB⟩, fun B hB => ?_⟩
    have : (fun x => P x B) = fun x => κ x B := funext fun x => (hP x B hB).symm
    rw [this]
    exact κ.measurable_coe hB

/-- **Theorem 8.4.** For `F ≥ 0` measurable on `X × Y`, `(TF)(x) = ∫ F(x, y) P(x, dy)` is
measurable. -/
theorem theorem_8_4 (P : Kernel X Y) [IsSFiniteKernel P] {F : X × Y → ℝ≥0∞}
    (hF : Measurable F) : Measurable fun x => ∫⁻ y, F (x, y) ∂P x :=
  hF.lintegral_kernel_prod_right'

/-- **Corollary to Theorem 8.4.** For bounded measurable `F`, `TF` is bounded and measurable. -/
theorem theorem_8_4_cor (P : Kernel X Y) [IsMarkovKernel P] {F : X × Y → ℝ}
    (hF : Measurable F) {M : ℝ} (hM : ∀ p, |F p| ≤ M) :
    Measurable (fun x => ∫ y, F (x, y) ∂P x) ∧ ∀ x, |∫ y, F (x, y) ∂P x| ≤ M := by
  refine ⟨(hF.stronglyMeasurable.integral_kernel_prod_right' (κ := P)).measurable, fun x => ?_⟩
  have := norm_integral_le_of_norm_le_const (μ := P x) (C := M) (f := fun y => F (x, y))
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hM (x, y))
  simpa [Real.norm_eq_abs, measureReal_def] using this

/-- The **direct product** `P₃ = P₁ × P₂` (SLP p. 229): `P₃(w, ·)` is the law of `(x, y)` when
`x ~ P₁(w, ·)` and then `y ~ P₂(x, ·)`. -/
noncomputable def directProd (P₁ : Kernel W X) (P₂ : Kernel X Y) : Kernel W (X × Y) :=
  P₁ ⊗ₖ Kernel.prodMkLeft W P₂

theorem isMarkovKernel_directProd (P₁ : Kernel W X) (P₂ : Kernel X Y) [IsMarkovKernel P₁]
    [IsMarkovKernel P₂] : IsMarkovKernel (directProd P₁ P₂) := by
  unfold directProd
  infer_instance

/-- **Theorem 8.5.** `P₃(w, A × B) = ∫_A P₂(x, B) P₁(w, dx)`, and `P₃` is a stochastic kernel on
`{W, 𝒳 × 𝒴}`. -/
theorem theorem_8_5 (P₁ : Kernel W X) (P₂ : Kernel X Y) [IsMarkovKernel P₁] [IsMarkovKernel P₂]
    (w : W) {A : Set X} {B : Set Y} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    directProd P₁ P₂ w (A ×ˢ B) = ∫⁻ x in A, P₂ x B ∂P₁ w ∧
      IsMarkovKernel (directProd P₁ P₂) := by
  refine ⟨?_, isMarkovKernel_directProd P₁ P₂⟩
  rw [directProd, Kernel.compProd_apply_prod hA hB]
  rfl

/-- **Theorem 8.5, uniqueness.** A probability measure on `X × Y` with the values (3) on
measurable rectangles is `P₃(w, ·)`. -/
theorem theorem_8_5_unique (P₁ : Kernel W X) (P₂ : Kernel X Y) [IsMarkovKernel P₁]
    [IsMarkovKernel P₂] (w : W) {ν : Measure (X × Y)} [IsProbabilityMeasure ν]
    (hν : ∀ A B, MeasurableSet A → MeasurableSet B → ν (A ×ˢ B) = ∫⁻ x in A, P₂ x B ∂P₁ w) :
    ν = directProd P₁ P₂ w := by
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro _ ⟨A, hA, B, hB, rfl⟩
    rw [hν A B hA hB, (theorem_8_5 P₁ P₂ w hA hB).1]
  · have := isMarkovKernel_directProd P₁ P₂
    simp

/-- **Theorem 8.6.** For `F ≥ 0` measurable on `X × Y`,
`∫ F dP₃(w, ·) = ∫_X [∫_Y F(x, y) P₂(x, dy)] P₁(w, dx)`. -/
theorem theorem_8_6 (P₁ : Kernel W X) (P₂ : Kernel X Y) [IsMarkovKernel P₁] [IsMarkovKernel P₂]
    (w : W) {F : X × Y → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F p ∂directProd P₁ P₂ w = ∫⁻ x, ∫⁻ y, F (x, y) ∂P₂ x ∂P₁ w :=
  Kernel.lintegral_compProd _ _ w hF

/-- **Theorem 8.7.** (4) holds for every `F` integrable for `P₃(ŵ, ·)`. -/
theorem theorem_8_7 (P₁ : Kernel W X) (P₂ : Kernel X Y) [IsMarkovKernel P₁] [IsMarkovKernel P₂]
    (w : W) {F : X × Y → ℝ} (hF : Integrable F (directProd P₁ P₂ w)) :
    ∫ p, F p ∂directProd P₁ P₂ w = ∫ x, ∫ y, F (x, y) ∂P₂ x ∂P₁ w :=
  integral_compProd hF

/-- **Corollary to Theorem 8.6.** (4) holds for bounded measurable `F`. -/
theorem theorem_8_6_cor (P₁ : Kernel W X) (P₂ : Kernel X Y) [IsMarkovKernel P₁]
    [IsMarkovKernel P₂] (w : W) {F : X × Y → ℝ} (hF : Measurable F) {M : ℝ}
    (hM : ∀ p, |F p| ≤ M) :
    ∫ p, F p ∂directProd P₁ P₂ w = ∫ x, ∫ y, F (x, y) ∂P₂ x ∂P₁ w := by
  have := isMarkovKernel_directProd P₁ P₂
  exact theorem_8_7 P₁ P₂ w (integrable_of_bounded hF hM)

/-- **Exercise 8.9a (Product Measure Theorem).** For probability spaces `(X, μ)` and `(Y, ν)`
there is a unique probability measure `λ` on `X × Y` with `λ(A × B) = μ(A)ν(B)`. -/
theorem ex_8_9a (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    (IsProbabilityMeasure (μ.prod ν) ∧
      ∀ A B, MeasurableSet A → MeasurableSet B → μ.prod ν (A ×ˢ B) = μ A * ν B) ∧
      ∀ lam : Measure (X × Y), (∀ A B, MeasurableSet A → MeasurableSet B →
        lam (A ×ˢ B) = μ A * ν B) → lam = μ.prod ν :=
  ⟨⟨inferInstance, fun A B _ _ => Measure.prod_prod A B⟩,
    fun _ h => (Measure.prod_eq h).symm⟩

/-- **Exercise 8.9b (Tonelli and Fubini).** The two iterated integrals of a nonnegative
measurable, or a `λ`-integrable, function equal its integral. -/
theorem ex_8_9b (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    (∀ F : X × Y → ℝ≥0∞, Measurable F →
      ∫⁻ p, F p ∂μ.prod ν = ∫⁻ x, ∫⁻ y, F (x, y) ∂ν ∂μ ∧
        ∫⁻ p, F p ∂μ.prod ν = ∫⁻ y, ∫⁻ x, F (x, y) ∂μ ∂ν) ∧
      ∀ F : X × Y → ℝ, Integrable F (μ.prod ν) →
        ∫ p, F p ∂μ.prod ν = ∫ x, ∫ y, F (x, y) ∂ν ∂μ ∧
          ∫ p, F p ∂μ.prod ν = ∫ y, ∫ x, F (x, y) ∂μ ∂ν :=
  ⟨fun F hF => ⟨lintegral_prod F hF.aemeasurable, lintegral_prod_symm F hF.aemeasurable⟩,
    fun F hF => ⟨integral_prod F hF, integral_prod_symm F hF⟩⟩

end StokeyLucasPrescott.StochasticDP
