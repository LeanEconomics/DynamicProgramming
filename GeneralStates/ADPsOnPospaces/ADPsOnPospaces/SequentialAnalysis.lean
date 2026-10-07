/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Sequential analysis

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §1.4 (pp. 49–54).

Draws `Z₁, Z₂, …` are iid with density `f₀` or `f₁`; the state is the posterior probability
`π` that `f = f₁`.

* Bayes' rule (1.56): `κ(π, z) = πf₁(z)/((1 − π)f₀(z) + πf₁(z))` stays in `[0, 1]`, and the
  predictive density `ψ(π, z) = (1 − π)f₀(z) + πf₁(z)` (1.57) integrates to one.
* Beliefs are a martingale: `∫ κ(π, z)ψ(π, z) dz = π`.
* The Bellman operator of (1.58), `(Tg)(π) = min{πL₀, (1 − π)L₁, c + ∫ g(κ(π, z))ψ(π, z) dz}`,
  is order preserving and maps nonnegative functions to functions between `0` and
  `min{πL₀, (1 − π)L₁}`.

Theorem 1.4.1 (the optimal loss function uniquely solves (1.58), with optimal policies the
minimizers of `Q(π, a)`) has no discounting; the book proves it as Theorem 3.2.9, in Chapter 3.
-/

open MeasureTheory

namespace SargentStachurski.ADPsOnPospaces

variable {f₀ f₁ : ℝ → ℝ}

/-- The predictive density (1.57): `ψ(π, z) = (1 − π)f₀(z) + πf₁(z)`. -/
def predDensity (f₀ f₁ : ℝ → ℝ) (π z : ℝ) : ℝ := (1 - π) * f₀ z + π * f₁ z

/-- Bayes' rule (1.56): `κ(π, z) = πf₁(z)/((1 − π)f₀(z) + πf₁(z))`. -/
noncomputable def bayesUpdate (f₀ f₁ : ℝ → ℝ) (π z : ℝ) : ℝ := π * f₁ z / predDensity f₀ f₁ π z

/-- (1.56): the posterior is a probability. -/
theorem bayesUpdate_mem_Icc (hf₀ : ∀ z, 0 ≤ f₀ z) (hf₁ : ∀ z, 0 ≤ f₁ z) {π : ℝ}
    (hπ : π ∈ Set.Icc (0 : ℝ) 1) (z : ℝ) : bayesUpdate f₀ f₁ π z ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hπ
  have ha : 0 ≤ (1 - π) * f₀ z := mul_nonneg (by linarith) (hf₀ z)
  have hb : 0 ≤ π * f₁ z := mul_nonneg h0 (hf₁ z)
  refine ⟨div_nonneg hb (add_nonneg ha hb), ?_⟩
  rcases (add_nonneg ha hb).eq_or_lt with h | h
  · simp [bayesUpdate, predDensity, ← h]
  · exact (div_le_one h).2 (by linarith)

/-- `κ(π, z)ψ(π, z) = πf₁(z)`, also where `ψ(π, z) = 0`. -/
theorem bayesUpdate_mul_predDensity (hf₀ : ∀ z, 0 ≤ f₀ z) (hf₁ : ∀ z, 0 ≤ f₁ z) {π : ℝ}
    (hπ : π ∈ Set.Icc (0 : ℝ) 1) (z : ℝ) :
    bayesUpdate f₀ f₁ π z * predDensity f₀ f₁ π z = π * f₁ z := by
  obtain ⟨h0, h1⟩ := hπ
  have ha : 0 ≤ (1 - π) * f₀ z := mul_nonneg (by linarith) (hf₀ z)
  have hb : 0 ≤ π * f₁ z := mul_nonneg h0 (hf₁ z)
  rcases eq_or_ne (predDensity f₀ f₁ π z) 0 with h | h
  · have : π * f₁ z = 0 := by simp only [predDensity] at h; linarith
    rw [h, this, mul_zero]
  · exact div_mul_cancel₀ _ h

/-- (1.57): the predictive density integrates to one. -/
theorem integral_predDensity (hi₀ : Integrable f₀) (hi₁ : Integrable f₁)
    (h₀ : ∫ z, f₀ z = 1) (h₁ : ∫ z, f₁ z = 1) (π : ℝ) : ∫ z, predDensity f₀ f₁ π z = 1 := by
  simp only [predDensity]
  rw [integral_add (hi₀.const_mul _) (hi₁.const_mul _), integral_const_mul, integral_const_mul,
    h₀, h₁]
  ring

/-- §1.4.1: beliefs are a martingale, `∫ κ(π, z)ψ(π, z) dz = π`. -/
theorem integral_bayesUpdate_mul_predDensity (hf₀ : ∀ z, 0 ≤ f₀ z) (hf₁ : ∀ z, 0 ≤ f₁ z)
    (h₁ : ∫ z, f₁ z = 1) {π : ℝ} (hπ : π ∈ Set.Icc (0 : ℝ) 1) :
    ∫ z, bayesUpdate f₀ f₁ π z * predDensity f₀ f₁ π z = π := by
  simp only [bayesUpdate_mul_predDensity hf₀ hf₁ hπ, integral_const_mul, h₁, mul_one]

/-- The Bellman operator of (1.58):
`(Tg)(π) = min{πL₀, (1 − π)L₁, c + ∫ g(κ(π, z))ψ(π, z) dz}`. -/
noncomputable def seqBellman (f₀ f₁ : ℝ → ℝ) (L₀ L₁ c : ℝ) (g : ℝ → ℝ) (π : ℝ) : ℝ :=
  min (π * L₀) (min ((1 - π) * L₁)
    (c + ∫ z, g (bayesUpdate f₀ f₁ π z) * predDensity f₀ f₁ π z))

/-- The Bellman operator (1.58) is order preserving on bounded measurable functions. -/
theorem seqBellman_mono (hf₀ : ∀ z, 0 ≤ f₀ z) (hf₁ : ∀ z, 0 ≤ f₁ z) (hm₀ : Measurable f₀)
    (hm₁ : Measurable f₁) (hi₀ : Integrable f₀) (hi₁ : Integrable f₁) {L₀ L₁ c : ℝ}
    {g g' : ℝ → ℝ} (hg : Measurable g) (hg' : Measurable g') {M : ℝ} (hgM : ∀ x, |g x| ≤ M)
    (hgM' : ∀ x, |g' x| ≤ M) (hle : g ≤ g') {π : ℝ} (hπ : π ∈ Set.Icc (0 : ℝ) 1) :
    seqBellman f₀ f₁ L₀ L₁ c g π ≤ seqBellman f₀ f₁ L₀ L₁ c g' π := by
  have hψ : Integrable (predDensity f₀ f₁ π) := (hi₀.const_mul _).add (hi₁.const_mul _)
  have hψ0 : ∀ z, 0 ≤ predDensity f₀ f₁ π z := fun z =>
    add_nonneg (mul_nonneg (by linarith [hπ.2]) (hf₀ z)) (mul_nonneg hπ.1 (hf₁ z))
  have hκm : Measurable (bayesUpdate f₀ f₁ π) :=
    (measurable_const.mul hm₁).div ((measurable_const.mul hm₀).add (measurable_const.mul hm₁))
  have hint : ∀ {h : ℝ → ℝ}, Measurable h → (∀ x, |h x| ≤ M) →
      Integrable fun z => h (bayesUpdate f₀ f₁ π z) * predDensity f₀ f₁ π z := by
    intro h hh hhM
    refine hψ.bdd_mul (hh.comp hκm).aestronglyMeasurable (c := M) ?_
    exact Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hhM _
  refine min_le_min le_rfl (min_le_min le_rfl (add_le_add le_rfl ?_))
  exact integral_mono (hint hg hgM) (hint hg' hgM') fun z =>
    mul_le_mul_of_nonneg_right (hle _) (hψ0 z)

/-- The Bellman operator (1.58) maps nonnegative functions into `[0, min{πL₀, (1 − π)L₁}]`. -/
theorem seqBellman_mem (hf₀ : ∀ z, 0 ≤ f₀ z) (hf₁ : ∀ z, 0 ≤ f₁ z) {L₀ L₁ c : ℝ}
    (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁) (hc : 0 ≤ c) {g : ℝ → ℝ} (hg : ∀ x, 0 ≤ g x) {π : ℝ}
    (hπ : π ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ seqBellman f₀ f₁ L₀ L₁ c g π ∧
      seqBellman f₀ f₁ L₀ L₁ c g π ≤ min (π * L₀) ((1 - π) * L₁) := by
  obtain ⟨h0, h1⟩ := hπ
  have hψ0 : ∀ z, 0 ≤ predDensity f₀ f₁ π z := fun z =>
    add_nonneg (mul_nonneg (by linarith) (hf₀ z)) (mul_nonneg h0 (hf₁ z))
  have hI : 0 ≤ ∫ z, g (bayesUpdate f₀ f₁ π z) * predDensity f₀ f₁ π z :=
    integral_nonneg fun z => mul_nonneg (hg _) (hψ0 z)
  refine ⟨le_min (mul_nonneg h0 hL₀) (le_min (mul_nonneg (by linarith) hL₁) (by linarith)),
    le_min (min_le_left _ _) ((min_le_right _ _).trans (min_le_left _ _))⟩

end SargentStachurski.ADPsOnPospaces
