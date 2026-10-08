/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveDecisionProcesses.GeneralMDP
import RecursiveDecisionProcesses.Feller
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Optimal savings as a linear decision process

Sargent and Stachurski, *Dynamic Programming*, Volume 2, Example 6.1.5 (p. 191) and Example 6.1.8
(p. 198).

Wealth `x`, consumption `a ∈ Γ(x) = [0, x]`, utility `u` bounded and continuous, gross return `R`,
and iid income `y ∼ φ`:
`∫ v(x')K(x, a, dx') = β ∫ v(R(x − a) + y)φ(dy)`. Wealth is a real state with
`Γ(x) = [0, max(x, 0)]`.

* **Example 6.1.5**: the savings model is an LDP (an MDP with `P(x, a) = law of R(x − a) + y`).
* **Example 6.1.8**: if `φ` has a continuous density, `P` is strong Feller (Example 6.1.2), so by
  Proposition 6.1.7 the fundamental optimality properties hold, `v* ∈ bcX`, VFI converges
  geometrically on `bcX`, and OPI and HPI converge.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.RecursiveDecisionProcesses

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

namespace Savings

theorem measurable_next (R : ℝ) :
    Measurable (uncurry fun (p : ℝ × ℝ) (y : ℝ) => R * (p.1 - p.2) + y) :=
  (measurable_const.mul ((measurable_fst.comp measurable_fst).sub
    (measurable_snd.comp measurable_fst))).add measurable_snd

/-- The kernel `P(x, a) = law of R(x − a) + y`, `y ∼ φ`. -/
noncomputable abbrev P (R : ℝ) (φ : Measure ℝ) [IsProbabilityMeasure φ] : Kernel (ℝ × ℝ) ℝ :=
  shockKernel (fun (p : ℝ × ℝ) (y : ℝ) => R * (p.1 - p.2) + y) (measurable_next R) φ

/-- The reward `u(a)`. -/
noncomputable def reward (u : ℝ → ℝ) (hu : Continuous u) (hub : ∃ C, ∀ c, |u c| ≤ C) :
    BM (ℝ × ℝ) :=
  ⟨fun p => u p.2, hu.measurable.comp measurable_snd, ⟨hub.choose, fun _ => hub.choose_spec _⟩⟩

/-- The savings model as an LDP (an MDP with `K = βP`). -/
noncomputable def ldp (u : ℝ → ℝ) (hu : Continuous u) (hub : ∃ C, ∀ c, |u c| ≤ C) {β : ℝ}
    (hβ0 : 0 ≤ β) (R : ℝ) (φ : Measure ℝ) [IsProbabilityMeasure φ] : LDP ℝ ℝ :=
  have := shockKernel_isMarkov (fun (p : ℝ × ℝ) (y : ℝ) => R * (p.1 - p.2) + y)
    (measurable_next R) φ
  ofMDP (fun x => Icc 0 (max x 0)) (reward u hu hub) hβ0 (P R φ)
    ⟨fun _ => 0, measurable_const, fun _ => ⟨le_rfl, le_max_right _ _⟩⟩

/-- **Example 6.1.5** (p. 191): the savings model is an LDP with
`(T_σ v)(x) = u(σ(x)) + β ∫ v(R(x − σ(x)) + y)φ(dy)`. -/
theorem example_6_1_5 (u : ℝ → ℝ) (hu : Continuous u) (hub : ∃ C, ∀ c, |u c| ≤ C) {β : ℝ}
    (hβ0 : 0 ≤ β) (R : ℝ) (φ : Measure ℝ) [IsProbabilityMeasure φ]
    (σ : (ldp u hu hub hβ0 R φ).Policy) (v : BM ℝ) (x : ℝ) :
    ((ldp u hu hub hβ0 R φ).adp.T σ v).toFun x =
      u (σ.1 x) + β * ∫ y, v.toFun (R * (x - σ.1 x) + y) ∂φ := by
  rw [show ((ldp u hu hub hβ0 R φ).adp.T σ v).toFun x =
      u (σ.1 x) + β * ∫ x', v.toFun x' ∂(P R φ (x, σ.1 x)) from rfl, P,
    integral_shockKernel _ _ _ v.measurable']

/-- The income distribution with continuous density `φ`. -/
noncomputable def densityMeasure (φ : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity fun y => ((φ y).toNNReal : ENNReal)

theorem densityMeasure_isProbability {φ : ℝ → ℝ} (hφ0 : ∀ y, 0 ≤ φ y)
    (hφ1 : ∫ y, φ y = 1) : IsProbabilityMeasure (densityMeasure φ) := by
  have hint : Integrable φ := Integrable.of_integral_ne_zero (by rw [hφ1]; exact one_ne_zero)
  refine ⟨?_⟩
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have := ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hφ0)
  rw [hφ1, ENNReal.ofReal_one] at this
  rw [this]
  rfl

/-- **Example 6.1.8** (p. 198): if income has a continuous density `φ`, the savings model is a
strong Feller MDP, so by Proposition 6.1.7 the fundamental optimality properties hold, `v* ∈ bcX`,
VFI converges geometrically on `bcX`, and OPI and HPI converge. -/
theorem example_6_1_8 (u : ℝ → ℝ) (hu : Continuous u) (hub : ∃ C, ∀ c, |u c| ≤ C) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (R : ℝ) {φ : ℝ → ℝ} (hφc : Continuous φ) (hφ0 : ∀ y, 0 ≤ φ y)
    (hφ1 : ∫ y, φ y = 1) :
    have := densityMeasure_isProbability hφ0 hφ1
    (∀ h : BM ℝ, ContinuousOn (fun p => ∫ x', h.toFun x' ∂(P R (densityMeasure φ) p))
      {p | p.2 ∈ Icc 0 (max p.1 0)}) ∧
    ∃ hw : (ldp u hu hub hβ0 R (densityMeasure φ)).adp.WellPosed,
      (ldp u hu hub hβ0 R (densityMeasure φ)).adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ LDP.bc ℝ,
        (ldp u hu hub hβ0 R (densityMeasure φ)).adp.VFIGeometric (LDP.bc ℝ) vstar ∧
        ∀ g, (ldp u hu hub hβ0 R (densityMeasure φ)).adp.IsSelector g →
          (ldp u hu hub hβ0 R (densityMeasure φ)).adp.OPIConverges g vstar ∧
            (ldp u hu hub hβ0 R (densityMeasure φ)).adp.HPIConverges hw g vstar := by
  intro hprob
  have hmark := shockKernel_isMarkov (fun (p : ℝ × ℝ) (y : ℝ) => R * (p.1 - p.2) + y)
    (measurable_next R) (densityMeasure φ)
  -- strong Feller, by a change of variable (Example 6.1.2)
  have hS : ∀ h : BM ℝ, ContinuousOn (fun p => ∫ x', h.toFun x' ∂(P R (densityMeasure φ) p))
      {p | p.2 ∈ Icc 0 (max p.1 0)} := fun h => by
    have heq : ∀ p : ℝ × ℝ, ∫ x', h.toFun x' ∂(P R (densityMeasure φ) p) =
        1 * ∫ y, h.toFun (R * (p.1 - p.2) + y) * φ y := fun p => by
      rw [P, integral_shockKernel _ _ _ h.measurable', densityMeasure,
        integral_withDensity_eq_integral_smul (f := fun y => (φ y).toNNReal)
          hφc.measurable.real_toNNReal, one_mul]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [NNReal.smul_def, Real.coe_toNNReal _ (hφ0 y), smul_eq_mul]
      ring
    simp_rw [heq]
    exact example_6_1_2 (β := fun _ => 1) continuousOn_const
      (g := fun p : ℝ × ℝ => R * (p.1 - p.2))
      (continuous_const.mul (continuous_fst.sub continuous_snd)).continuousOn hφc hφ0 hφ1
      h.measurable' (fun x => BM.abs_le_norm h x)
  have hB : HasMaxSelections fun x : ℝ => Icc (0 : ℝ) (max x 0) :=
    hasMaxSelections_Icc (g := fun _ => 0) (h := fun x => max x 0) continuous_const
      (continuous_id.max continuous_const) fun x => le_max_right _ _
  obtain ⟨hw, hFO, vstar, hv, hgeo, hconv⟩ := proposition_6_1_7 (fun x : ℝ => Icc 0 (max x 0))
    (reward u hu hub) hβ0 hβ1 (P R (densityMeasure φ))
    ⟨fun _ => 0, measurable_const, fun _ => ⟨le_rfl, le_max_right _ _⟩⟩ hB
    (hu.comp continuous_snd).continuousOn fun h _ => hS h
  exact ⟨hS, hw, hFO, vstar, hv, hgeo, hconv hS⟩

end Savings

end SargentStachurski.RecursiveDecisionProcesses
