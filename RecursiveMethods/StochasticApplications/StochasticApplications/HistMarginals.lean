/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticApplications.Theorem94

/-!
# Marginals of the history measures

Two facts used to evaluate expectations along plans in §9.4: dropping the last date maps `μᵗ⁺¹`
to `μᵗ` (`map_init_hist`), so a function of the history up to `t` has the same integral under
both; and with i.i.d. shocks, `Q(z, ·) = μ`, the last shock is distributed as `μ`
(`map_last_hist_const`).
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {Z : Type*} [MeasurableSpace Z] (Q : Kernel Z Z) [IsMarkovKernel Q]

/-- Dropping the last date: `μᵗ⁺¹(z₀, ·)` maps to `μᵗ(z₀, ·)`. -/
theorem map_init_hist (t : ℕ) (z₀ : Z) :
    (hist Q (t + 1) z₀).map Fin.init = hist Q t z₀ := by
  have := ex_8_8a Q t
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf (measurable_init t),
    hist_succ_lintegral_last Q t z₀ (f := fun h => f (Fin.init h)) (hf.comp (measurable_init t))]
  simp only [Fin.init_snoc, lintegral_const, measure_univ, mul_one]

theorem lintegral_init (t : ℕ) (z₀ : Z) {f : (Fin t → Z) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ h, f (Fin.init h) ∂hist Q (t + 1) z₀ = ∫⁻ h, f h ∂hist Q t z₀ := by
  rw [← lintegral_map hf (measurable_init t), map_init_hist]

theorem integral_init (t : ℕ) (z₀ : Z) {F : (Fin t → Z) → ℝ}
    (hF : AEStronglyMeasurable F (hist Q t z₀)) :
    ∫ h, F (Fin.init h) ∂hist Q (t + 1) z₀ = ∫ h, F h ∂hist Q t z₀ := by
  rw [← map_init_hist Q t z₀] at hF ⊢
  rw [integral_map (measurable_init t).aemeasurable hF]

theorem integrable_init (t : ℕ) (z₀ : Z) {F : (Fin t → Z) → ℝ}
    (hF : Integrable F (hist Q t z₀)) :
    Integrable (fun h => F (Fin.init h)) (hist Q (t + 1) z₀) := by
  rw [← map_init_hist Q t z₀] at hF
  exact hF.comp_measurable (measurable_init t)

/-- With i.i.d. shocks the last shock is distributed as `μ`. -/
theorem map_last_hist_const (μ : Measure Z) [IsProbabilityMeasure μ] (t : ℕ) (z₀ : Z) :
    (hist (Kernel.const Z μ) (t + 1) z₀).map (lastState z₀) = μ := by
  have := ex_8_8a (Kernel.const Z μ) t
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf (measurable_lastState z₀ (t + 1)),
    hist_succ_lintegral_last _ t z₀ (f := fun h => f (lastState z₀ h))
      (hf.comp (measurable_lastState z₀ (t + 1)))]
  simp only [lastState_snoc, Kernel.const_apply, lintegral_const, measure_univ, mul_one]

end StokeyLucasPrescott.StochasticApplications
