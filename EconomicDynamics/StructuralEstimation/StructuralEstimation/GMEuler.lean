/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Example 12.1.1: Euler-equation moment conditions (Miao, §12.1, pp. 388–389)

Miao, Example 12.1.1, pp. 388–389. For the consumption/portfolio model of Chapter 8.3 the Euler
equation is `u'(C_t) = β E_t[R_{j,t+1} u'(C_{t+1})]`. With `h = βR_{j,t+1}u'(C_{t+1})/u'(C_t) − 1`
and CRRA utility `u(c) = c^{1−γ}/(1 − γ)` (`gm_crra_hasDerivAt`: `u'(c) = c^{−γ}`), the Euler
equation implies the orthogonality conditions `E[z_t h] = 0` for every `z_t` in the date-`t`
information set (`example_12_1_1`), and in particular the moment condition (12.1) `E h = 0`
(`example_12_1_1_mean`). The date-`t` information is a sub-σ-algebra `F`, `E_t = E[· | F]`,
`C_t` and `z_t` are `F`-measurable, and integrability of the products involved is assumed.
The Euler equation itself is quoted from Chapter 8 (it is not re-derived here).
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Topology

/-- CRRA marginal utility `u'(c) = c^{−γ}`. -/
noncomputable def gm_crraMU (γ c : ℝ) : ℝ := c ^ (-γ)

/-- Miao, Example 12.1.1: for `u(c) = c^{1−γ}/(1 − γ)` (`γ ≠ 1`), `u'(c) = c^{−γ}`. -/
theorem gm_crra_hasDerivAt {γ c : ℝ} (hγ : γ ≠ 1) (hc : 0 < c) :
    HasDerivAt (fun c : ℝ => c ^ (1 - γ) / (1 - γ)) (gm_crraMU γ c) c := by
  have h1 : (1 - γ) ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have := (Real.hasDerivAt_rpow_const (p := 1 - γ) (Or.inl hc.ne')).div_const (1 - γ)
  convert this using 1
  rw [gm_crraMU, mul_div_cancel_left₀ _ h1]
  congr 1
  ring

/-- Miao, Example 12.1.1: the Euler moment function
`h(C_t, C_{t+1}, R_{j,t+1}, θ) = βR_{j,t+1}u'(C_{t+1})/u'(C_t) − 1`, `θ = (β, γ)`. -/
noncomputable def gm_eulerMoment (β γ C C' R : ℝ) : ℝ :=
  β * R * gm_crraMU γ C' / gm_crraMU γ C - 1

/-- With CRRA utility `h = βR(C_{t+1}/C_t)^{−γ} − 1`. -/
theorem gm_eulerMoment_eq {β γ C C' R : ℝ} (hC : 0 < C) (hC' : 0 < C') :
    gm_eulerMoment β γ C C' R = β * R * (C' / C) ^ (-γ) - 1 := by
  rw [gm_eulerMoment, gm_crraMU, gm_crraMU, Real.div_rpow hC'.le hC.le, mul_div_assoc]

/-- **Example 12.1.1** (Miao, p. 389). If the Euler equation
`u'(C_t) = β E_t[R_{j,t+1} u'(C_{t+1})]` holds, with `C_t > 0` and `z_t` measurable with respect to
the date-`t` information `F`, then `E[z_t h(C_t, C_{t+1}, R_{j,t+1}, θ)] = 0`. -/
theorem example_12_1_1 {Ω : Type*} {F : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
    (hF : F ≤ mΩ) {P : Measure Ω} [IsProbabilityMeasure P] {β γ : ℝ} {C C' R z : Ω → ℝ}
    (hC : Measurable[F] C) (hCpos : ∀ ω, 0 < C ω) (hz : Measurable[F] z)
    (hY : Integrable (fun ω => β * R ω * gm_crraMU γ (C' ω)) P)
    (hzY : Integrable (fun ω => z ω / gm_crraMU γ (C ω) * (β * R ω * gm_crraMU γ (C' ω))) P)
    (hzint : Integrable z P)
    (heuler : P[fun ω => β * R ω * gm_crraMU γ (C' ω) | F] =ᵐ[P]
      fun ω => gm_crraMU γ (C ω)) :
    ∫ ω, z ω * gm_eulerMoment β γ (C ω) (C' ω) (R ω) ∂P = 0 := by
  have hu : ∀ ω, gm_crraMU γ (C ω) ≠ 0 := fun ω => (Real.rpow_pos_of_pos (hCpos ω) _).ne'
  set Y : Ω → ℝ := fun ω => β * R ω * gm_crraMU γ (C' ω) with hYdef
  set w : Ω → ℝ := fun ω => z ω / gm_crraMU γ (C ω) with hwdef
  have hwm : StronglyMeasurable[F] w :=
    (hz.div (hC.pow_const (-γ))).stronglyMeasurable
  have : IsFiniteMeasure (P.trim hF) := isFiniteMeasure_trim hF
  have key : ∫ ω, w ω * Y ω ∂P = ∫ ω, z ω ∂P := by
    rw [← integral_condExp hF]
    refine integral_congr_ae ?_
    filter_upwards [condExp_mul_of_stronglyMeasurable_left (μ := P) (m := F) (g := Y) hwm hzY hY,
      heuler] with ω h1 h2
    change P[w * Y | F] ω = z ω
    rw [h1, Pi.mul_apply, h2]
    simp only [hwdef]
    field_simp [hu ω]
  have hpt : (fun ω => z ω * gm_eulerMoment β γ (C ω) (C' ω) (R ω)) =
      fun ω => w ω * Y ω - z ω := by
    funext ω
    simp only [gm_eulerMoment, hwdef, hYdef]
    field_simp [hu ω]
  rw [hpt, integral_sub hzY hzint, key, sub_self]

/-- Miao, (12.1) for Example 12.1.1 (`z_t = 1`): the Euler equation implies `E h = 0`. -/
theorem example_12_1_1_mean {Ω : Type*} {F : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
    (hF : F ≤ mΩ) {P : Measure Ω} [IsProbabilityMeasure P] {β γ : ℝ} {C C' R : Ω → ℝ}
    (hC : Measurable[F] C) (hCpos : ∀ ω, 0 < C ω)
    (hY : Integrable (fun ω => β * R ω * gm_crraMU γ (C' ω)) P)
    (hzY : Integrable (fun ω => 1 / gm_crraMU γ (C ω) * (β * R ω * gm_crraMU γ (C' ω))) P)
    (heuler : P[fun ω => β * R ω * gm_crraMU γ (C' ω) | F] =ᵐ[P]
      fun ω => gm_crraMU γ (C ω)) :
    ∫ ω, gm_eulerMoment β γ (C ω) (C' ω) (R ω) ∂P = 0 := by
  have := example_12_1_1 hF hC hCpos (z := fun _ => 1) measurable_const hY hzY
    (integrable_const 1) heuler
  simpa using this

end Miao.StructuralEstimation
