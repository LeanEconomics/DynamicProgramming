/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PartialInformation.HMFilter
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Hidden Markov-switching model (the Hamilton filter)

Miao, §10.1.3, pp. 339–340. The hidden chain is as in §10.1.2 and the measurement equation is
`y_t = h(x_t, ε_t)` with `ε_t` IID; `f(x, y) = Pr(h(x, ε) = y)` is read as the density of
`h(x, ε)` (for continuous signals `Pr(h(x, ε) = y)` is zero; the filter uses the density). The
filter recursion is that of `HMFilter` with emission weight `f`:

* prediction `π_t(eᵢ | yᵗ⁻¹) = Σⱼ pⱼᵢ π_{t−1}(eⱼ | yᵗ⁻¹)` (`hm_hamilton_predict`),
* updating `π_t(eᵢ | yᵗ) = f(eᵢ, y_t) π_t(eᵢ | yᵗ⁻¹) / Σⱼ f(eⱼ, y_t) π_t(eⱼ | yᵗ⁻¹)`
  (`hm_hamilton_update`; the book prints `f(x, y_t)` in the numerator for `f(eᵢ, y_t)`).

For the consumption example `Δ ln C_t = κ(x_t) + ε_t`, `ε_t ~ N(0, σ²)`: the law of
`κ(x) + ε` is `N(κ(x), σ²)` with density `f(x, ·)` (`hm_switch_law`, `hm_switch_density`), the
predictive density `Σⱼ f(eⱼ, y) π_t(eⱼ | yᵗ⁻¹)` integrates to one (`hm_switch_predictive`), and
in the two-regime case the update is the log-odds rule
`log(π₁/π₂ | yᵗ) = log(π₁/π₂ | yᵗ⁻¹) + ((y − κ₂)² − (y − κ₁)²)/(2σ²)` (`hm_switch_logodds`).
The stationary prior of a two-state chain is `(p₂₁, p₁₂)/(p₁₂ + p₂₁)` (`hm_two_state_stationary`).
-/

namespace Miao.PartialInformation

open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {X Y : Type*} [Fintype X] [DecidableEq X]

/-- Miao, p. 339 (Hamilton filter, prediction):
`π_t(eᵢ | yᵗ⁻¹) = Σⱼ pⱼᵢ π_{t−1}(eⱼ | yᵗ⁻¹)`; date `t − 1` is `t` here. -/
theorem hm_hamilton_predict (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ)
    (hP : ∀ i, ∑ j, P i j = 1) (t : ℕ) (ys : Fin (t + 1) → Y) (i : X) :
    hm_pred μ0 P f t ys i = ∑ j, P j i * hm_post μ0 P f t ys j :=
  hm_pred_eq μ0 P f hP t ys i

/-- Miao, p. 340 (Hamilton filter, updating):
`π_t(eᵢ | yᵗ) = f(eᵢ, y_t) π_t(eᵢ | yᵗ⁻¹) / Σⱼ f(eⱼ, y_t) π_t(eⱼ | yᵗ⁻¹)`. -/
theorem hm_hamilton_update (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ)
    (hP : ∀ i, ∑ j, P i j = 1) (t : ℕ) (ys : Fin (t + 1) → Y) (y : Y)
    (hl : hm_lik μ0 P f t ys ≠ 0) (i : X) :
    hm_post μ0 P f (t + 1) (Fin.snoc ys y) i =
      f i y * hm_pred μ0 P f t ys i / ∑ j, f j y * hm_pred μ0 P f t ys j :=
  hm_post_update μ0 P f hP t ys y hl i

omit [Fintype X] [DecidableEq X] in
/-- Miao, p. 339: in `Δ ln C_t = κ(x_t) + ε_t` with `ε_t ~ N(0, σ²)`, the law of `κ(x) + ε` is
`N(κ(x), σ²)`. -/
theorem hm_switch_law (κ : X → ℝ) (σ2 : ℝ≥0) (x : X) :
    (gaussianReal 0 σ2).map (fun e => κ x + e) = gaussianReal (κ x) σ2 := by
  rw [gaussianReal_map_const_add, zero_add]

/-- The emission density of the consumption-growth example, `f(x, y) = φ(y; κ(x), σ²)`. -/
noncomputable def hm_switchDensity (κ : X → ℝ) (σ2 : ℝ≥0) (x : X) (y : ℝ) : ℝ :=
  gaussianPDFReal (κ x) σ2 y

omit [Fintype X] [DecidableEq X] in
/-- Miao, p. 339: `f(x, ·)` is the density of `h(x, ε) = κ(x) + ε`: for `σ² ≠ 0` the law of
`κ(x) + ε` has density `f(x, ·)` with respect to Lebesgue measure, `f > 0`, `∫ f(x, y) dy = 1`. -/
theorem hm_switch_density (κ : X → ℝ) {σ2 : ℝ≥0} (hσ : σ2 ≠ 0) (x : X) :
    (gaussianReal 0 σ2).map (fun e => κ x + e) =
        volume.withDensity (fun y => ENNReal.ofReal (hm_switchDensity κ σ2 x y)) ∧
      (∀ y, 0 < hm_switchDensity κ σ2 x y) ∧ ∫ y, hm_switchDensity κ σ2 x y = 1 := by
  refine ⟨?_, fun y => gaussianPDFReal_pos _ _ _ hσ, integral_gaussianPDFReal_eq_one _ hσ⟩
  rw [hm_switch_law, gaussianReal_of_var_ne_zero _ hσ]
  rfl

/-- Miao, p. 340: the one-step predictive density `Σⱼ f(eⱼ, y) π_t(eⱼ | yᵗ⁻¹)` of the
consumption-growth example integrates to one. -/
theorem hm_switch_predictive (μ0 : X → ℝ) (P : Matrix X X ℝ) (κ : X → ℝ) {σ2 : ℝ≥0}
    (hσ : σ2 ≠ 0) (hP : ∀ i, ∑ j, P i j = 1) (t : ℕ) (ys : Fin (t + 1) → ℝ)
    (hl : hm_lik μ0 P (hm_switchDensity κ σ2) t ys ≠ 0) :
    ∫ y, ∑ j, hm_switchDensity κ σ2 j y * hm_pred μ0 P (hm_switchDensity κ σ2) t ys j = 1 := by
  rw [integral_finsetSum _ (fun j _ => by
    unfold hm_switchDensity
    exact (integrable_gaussianPDFReal _ _).mul_const _)]
  simp only [integral_mul_const, (hm_switch_density κ hσ _).2.2, one_mul]
  unfold hm_pred
  rw [← Finset.sum_div, div_self]
  rw [hm_predJoint_sum μ0 P _ hP]
  exact hl

/-- Miao, p. 340, two-regime case: the Hamilton update in log-odds form,
`log(π₁/π₂ | yᵗ) = log(π₁/π₂ | yᵗ⁻¹) + ((y − κ₂)² − (y − κ₁)²)/(2σ²)`, for positive predicted
probabilities. -/
theorem hm_switch_logodds (κ : Fin 2 → ℝ) {σ2 : ℝ≥0} (hσ : σ2 ≠ 0) (p : Fin 2 → ℝ)
    (hp : ∀ i, 0 < p i) (y : ℝ) :
    Real.log ((hm_switchDensity κ σ2 0 y * p 0 / ∑ j, hm_switchDensity κ σ2 j y * p j) /
        (hm_switchDensity κ σ2 1 y * p 1 / ∑ j, hm_switchDensity κ σ2 j y * p j)) =
      Real.log (p 0 / p 1) + ((y - κ 1) ^ 2 - (y - κ 0) ^ 2) / (2 * σ2) := by
  have h0 := gaussianPDFReal_pos (κ 0) σ2 y hσ
  have h1 := gaussianPDFReal_pos (κ 1) σ2 y hσ
  have hS : 0 < ∑ j, hm_switchDensity κ σ2 j y * p j :=
    Finset.sum_pos (fun j _ => mul_pos (gaussianPDFReal_pos _ _ _ hσ) (hp j)) Finset.univ_nonempty
  rw [div_div_div_cancel_right₀ hS.ne']
  unfold hm_switchDensity at h0 h1 ⊢
  rw [show gaussianPDFReal (κ 0) σ2 y * p 0 / (gaussianPDFReal (κ 1) σ2 y * p 1) =
      (gaussianPDFReal (κ 0) σ2 y / gaussianPDFReal (κ 1) σ2 y) * (p 0 / p 1) by
    field_simp]
  rw [Real.log_mul (div_pos h0 h1).ne' (div_pos (hp 0) (hp 1)).ne', Real.log_div h0.ne' h1.ne']
  simp only [gaussianPDFReal]
  have hc : 0 < (√(2 * Real.pi * (σ2 : ℝ)))⁻¹ := by
    have : (0 : ℝ) < σ2 := lt_of_le_of_ne σ2.2 (fun h => hσ (by exact_mod_cast h.symm))
    positivity
  rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_mul hc.ne' (Real.exp_pos _).ne',
    Real.log_exp, Real.log_exp]
  ring

/-- Miao, p. 340: the stationary distribution of a two-state chain with switching
probabilities `p₁₂, p₂₁` (not both zero) is `(p₂₁, p₁₂)/(p₁₂ + p₂₁)`; it may serve as the
initial prior `π₀(· | y⁻¹)`. -/
theorem hm_two_state_stationary (a b : ℝ) (hab : a + b ≠ 0) :
    let P : Matrix (Fin 2) (Fin 2) ℝ := !![1 - a, a; b, 1 - b]
    let pss : Fin 2 → ℝ := ![b / (a + b), a / (a + b)]
    (∀ j, ∑ i, pss i * P i j = pss j) ∧ ∑ i, pss i = 1 := by
  intro P pss
  refine ⟨fun j => ?_, ?_⟩
  · fin_cases j <;> simp [P, pss, Fin.sum_univ_two] <;> field_simp <;> ring
  · simp only [pss, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← add_div, add_comm b a, div_self hab]

end Miao.PartialInformation
