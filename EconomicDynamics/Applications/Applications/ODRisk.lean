/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.ODOption

/-!
# Option exercise: an increase in risk delays investment

Miao, §8.1, pp. 233–234. `F₁` is riskier than `F₂` in the sense of second-order stochastic
dominance (`od_Riskier`) if both have the same mean and `∫ u dF₁ ≤ ∫ u dF₂` for every concave
increasing `u`.

* `od_option_riskier`: if `F₁` is riskier than `F₂` (both on `[0, B]`), then the option value is
  higher under the riskier distribution — the continuation value `β∫V₁ dF₁ ≥ β∫V₂ dF₂` and
  `V₁ ≥ V₂` on `[0, B]`, so the decision maker prefers the riskier project — and the investment
  threshold is higher, `z₁* ≥ z₂*`: "an increase in risk … induces the decision maker to delay
  investment" (p. 234).

The book argues "by the convexity of the value function"; the proof applies the definition of
second-order dominance to the concave increasing function `z ↦ min(z − q, I) = z − max(q, z − I)`
(`od_min_concave`), which with the equal means gives `∫ max(q, z − I) dF₁ ≥ ∫ max(q, z − I) dF₂`
for every `q`, and then compares the fixed points of the two scalar Bellman maps
(`od_fixed_le_of_le`).
-/

namespace Miao.Applications

open MeasureTheory

/-- `F₁` is riskier than `F₂` (second-order stochastic dominance with equal means; Miao,
p. 233). -/
def od_Riskier (F₁ F₂ : Measure ℝ) : Prop :=
  ∫ x, x ∂F₁ = ∫ x, x ∂F₂ ∧
    ∀ u : ℝ → ℝ, ConcaveOn ℝ Set.univ u → Monotone u → ∫ x, u x ∂F₁ ≤ ∫ x, u x ∂F₂

/-- `z ↦ min(z − q, I)` is concave and increasing. -/
theorem od_min_concave (q I : ℝ) :
    ConcaveOn ℝ Set.univ (fun z : ℝ => min (z - q) I) ∧ Monotone (fun z : ℝ => min (z - q) I) :=
  ⟨((concaveOn_id convex_univ).sub (convexOn_const q convex_univ)).inf
      (concaveOn_const I convex_univ),
    fun x y hxy => min_le_min (by linarith) le_rfl⟩

/-- Under a riskier distribution the integral of `max(q, z − I)` is larger. -/
theorem od_integral_max_riskier {F₁ F₂ : Measure ℝ} [IsProbabilityMeasure F₁]
    [IsProbabilityMeasure F₂] {B : ℝ} (hF₁ : ∀ᵐ z ∂F₁, z ∈ Set.Icc 0 B)
    (hF₂ : ∀ᵐ z ∂F₂, z ∈ Set.Icc 0 B) (hR : od_Riskier F₁ F₂) (q I : ℝ) :
    ∫ z, max q (z - I) ∂F₂ ≤ ∫ z, max q (z - I) ∂F₁ := by
  obtain ⟨hc, hm⟩ := od_min_concave q I
  have h := hR.2 _ hc hm
  have hfun : (fun z : ℝ => min (z - q) I) = fun z => z - max q (z - I) := by
    funext z
    rcases le_total q (z - I) with h' | h'
    · rw [max_eq_right h', min_eq_right (by linarith)]; ring
    · rw [max_eq_left h', min_eq_left (by linarith)]
  have hint : ∀ {F : Measure ℝ} [IsProbabilityMeasure F], (∀ᵐ z ∂F, z ∈ Set.Icc 0 B) →
      ∫ z, (z - max q (z - I)) ∂F = ∫ z, z ∂F - ∫ z, max q (z - I) ∂F := fun hF =>
    integral_sub (od_integrable_of_continuous hF continuous_id)
      ((integrable_const q).sup (od_integrable_sub hF I))
  rw [hfun, hint hF₁, hint hF₂, hR.1] at h
  linarith

/-- Miao, pp. 233–234: if project 1 is riskier than project 2 (second-order stochastic dominance,
same mean), the decision maker prefers the riskier project — its option value is higher, both
before the draw (`β∫V₂ dF₂ ≤ β∫V₁ dF₁`) and at every payoff (`V₂ ≤ V₁` on `[0, B]`) — and the
riskier project has the higher investment threshold, so an increase in risk delays investment. -/
theorem od_option_riskier {F₁ F₂ : Measure ℝ} [IsProbabilityMeasure F₁]
    [IsProbabilityMeasure F₂] {B I β : ℝ} (hF₁ : ∀ᵐ z ∂F₁, z ∈ Set.Icc 0 B)
    (hF₂ : ∀ᵐ z ∂F₂, z ∈ Set.Icc 0 B) (hβ0 : 0 < β) (hβ1 : β < 1) (hR : od_Riskier F₁ F₂)
    {V₁ V₂ : ℝ → ℝ} (hV₁ : od_OptionBellman F₁ B I β V₁) (hV₂ : od_OptionBellman F₂ B I β V₂) :
    β * ∫ z, V₂ z ∂F₂ ≤ β * ∫ z, V₁ z ∂F₁ ∧ (∀ z ∈ Set.Icc 0 B, V₂ z ≤ V₁ z) ∧
      β * ∫ z, V₂ z ∂F₂ + I ≤ β * ∫ z, V₁ z ∂F₁ + I := by
  have hle : β * ∫ z, V₂ z ∂F₂ ≤ β * ∫ z, V₁ z ∂F₁ :=
    od_fixed_le_of_le hβ1 (od_optΦ_lipschitz hF₂ hβ0.le)
      (fun x => mul_le_mul_of_nonneg_left (od_integral_max_riskier hF₁ hF₂ hR x I) hβ0.le)
      (od_option_cont_fixed hF₁ hV₁) (od_option_cont_fixed hF₂ hV₂)
  refine ⟨hle, fun z hz => ?_, by linarith⟩
  rw [hV₁ z hz, hV₂ z hz]
  exact max_le_max hle le_rfl

end Miao.Applications
