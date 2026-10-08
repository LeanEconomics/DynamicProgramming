/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveDecisionProcesses.CEMDP

/-!
# Kreps–Porteus versus risk sensitivity

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §7.3.4 (pp. 241–244).

In the setting of §7.2.5 (`ξ ∼ φ`, transition `f(x, a, ξ)`):

* the risk-sensitive MDP (7.28), `B_RS(x, a, v) = r(x, a) + (β/θ) ln 𝔼 exp(θ v(f(x, a, ξ)))`, is
  the case `ℰ = ℰ^θ` of (7.24); Proposition 7.2.10 applies (`section_7_3_4`);
* the multiplicative Kreps–Porteus aggregator
  `B_MKP(x, a, v) = r(x, a) {𝔼 v(f(x, a, ξ))^ν}^{β/ν}`, `ν ≠ 0`, with `r = exp r̂` positive, gives
  an RDP (`mkpRDP`) on the measurable `v` with `e^{−K} ≤ v ≤ e^K` for some `K`;
* **Exercise 7.3.4**: `v ↦ ln v` is an isomorphism of the generated ADPs, with
  `B_MKP(x, a, v) = exp[B_RS(x, a, ln v)]` (with `r̂ = ln r`, `θ = ν`; Exercise 7.1.5).

The book's solution takes the bounded measurable `v > 0`, whose logarithms need not be bounded
below; `ln v ∈ bX` exactly when `v` is bounded above and away from zero, which is the value space
used here. The reward `r̂ = ln r` is bounded on `G`, as `(Γ, bX, B_RS)` requires.
-/

open Set Function Filter Topology MeasureTheory

namespace SargentStachurski.RecursiveDecisionProcesses

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

variable {X A Ξ : Type*} [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace Ξ]

/-- The risk-sensitive MDP (7.28): `B_RS(x, a, v) = r(x, a) + (β/θ) ln 𝔼 exp(θ v(f(x, a, ξ)))`. -/
noncomputable def rsRDP (Γ : X → Set A) (r : X × A → ℝ) (hr : Measurable r)
    (hrb : ∃ C, ∀ x, ∀ a ∈ Γ x, |r (x, a)| ≤ C) {β : ℝ} (hβ : 0 ≤ β) (φ : Measure Ξ)
    [IsProbabilityMeasure φ] {f : X × A → Ξ → X} (hf : Measurable (uncurry f)) {θ : ℝ}
    (hθ : θ ≠ 0) (hΓ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x) : BRDP X A :=
  ceBRDP Γ r hr hrb hβ φ hf (entropicCE_isCertEquiv hθ) (measurable_entropicCE_comp hf θ) hΓ

theorem rsRDP_B (Γ : X → Set A) (r : X × A → ℝ) (hr : Measurable r)
    (hrb : ∃ C, ∀ x, ∀ a ∈ Γ x, |r (x, a)| ≤ C) {β : ℝ} (hβ : 0 ≤ β) (φ : Measure Ξ)
    [IsProbabilityMeasure φ] {f : X × A → Ξ → X} (hf : Measurable (uncurry f)) {θ : ℝ}
    (hθ : θ ≠ 0) (hΓ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x) (x : X) (a : A)
    (v : X → ℝ) :
    (rsRDP Γ r hr hrb hβ φ hf hθ hΓ).B x a v =
      r (x, a) + β / θ * Real.log (∫ ξ, Real.exp (θ * v (f (x, a) ξ)) ∂φ) := by
  change r (x, a) + β * (θ⁻¹ * Real.log (∫ ξ, Real.exp (θ * v (f (x, a) ξ)) ∂φ)) = _
  ring

/-- §7.3.4 (p. 243): the risk-sensitive MDP satisfies the conclusions of Proposition 7.2.10 under
Assumption 7.2.11: the fundamental optimality properties hold, `v* ∈ bcX` and VFI converges
geometrically on `bcX`. -/
theorem section_7_3_4 [Nonempty X] [TopologicalSpace X] [TopologicalSpace A]
    [FirstCountableTopology X] [FirstCountableTopology A] (Γ : X → Set A) (r : X × A → ℝ)
    (hr : Measurable r) (hrb : ∃ C, ∀ x, ∀ a ∈ Γ x, |r (x, a)| ≤ C) {β : ℝ} (hβ : 0 ≤ β)
    (hβ1 : β < 1) (φ : Measure Ξ) [IsProbabilityMeasure φ] {f : X × A → Ξ → X}
    (hf : Measurable (uncurry f)) {θ : ℝ} (hθ : θ ≠ 0)
    (hΓ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x) (hΓmax : HasMaxSelections Γ)
    (hrc : ContinuousOn r {p | p.2 ∈ Γ p.1})
    (hfc : ∀ z, ContinuousOn (fun p => f p z) {p | p.2 ∈ Γ p.1}) :
    ∃ hw : (rsRDP Γ r hr hrb hβ φ hf hθ hΓ).toRDP.adp.WellPosed,
      (rsRDP Γ r hr hrb hβ φ hf hθ hΓ).toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ LDP.bc X,
        (rsRDP Γ r hr hrb hβ φ hf hθ hΓ).toRDP.adp.VFIGeometric (LDP.bc X) vstar :=
  proposition_7_2_10 Γ r hr hrb hβ hβ1 φ hf _ _ hΓ hΓmax hrc hfc (exercise_7_2_6 θ)

/-- Measurable `v : X → ℝ` with `e^{−K} ≤ v ≤ e^K` for some `K`: the positive functions with
`ln v ∈ bX`. -/
abbrev PosValues (X : Type*) [MeasurableSpace X] : Type _ :=
  {v : X → ℝ // Measurable v ∧ ∃ K, ∀ x, Real.exp (-K) ≤ v x ∧ v x ≤ Real.exp K}

theorem PosValues.pos (v : PosValues X) (x : X) : 0 < v.1 x := by
  obtain ⟨K, hK⟩ := v.2.2
  exact (Real.exp_pos _).trans_le (hK x).1

theorem PosValues.abs_log_le (v : PosValues X) : ∃ K, ∀ x, |Real.log (v.1 x)| ≤ K := by
  obtain ⟨K, hK⟩ := v.2.2
  refine ⟨K, fun x => abs_le.2 ⟨?_, ?_⟩⟩
  · have := Real.log_le_log (Real.exp_pos _) (hK x).1
    rwa [Real.log_exp] at this
  · have := Real.log_le_log (v.pos x) (hK x).2
    rwa [Real.log_exp] at this

/-- `ln v ∈ bX`. -/
noncomputable def PosValues.log (v : PosValues X) : BM X :=
  ⟨fun x => Real.log (v.1 x), Real.measurable_log.comp v.2.1, v.abs_log_le⟩

/-- `exp h` for `h ∈ bX`. -/
noncomputable def PosValues.exp (h : BM X) : PosValues X :=
  ⟨fun x => Real.exp (h.toFun x), Real.measurable_exp.comp h.measurable', ‖h‖, fun x =>
    ⟨Real.exp_le_exp.2 (neg_le_of_abs_le (BM.abs_le_norm h x)),
      Real.exp_le_exp.2 (le_of_abs_le (BM.abs_le_norm h x))⟩⟩

/-- The multiplicative Kreps–Porteus aggregator
`B_MKP(x, a, v) = r(x, a) {𝔼 v(f(x, a, ξ))^ν}^{β/ν}` with `r = exp r̂`. -/
noncomputable def mkpAgg (rhat : X × A → ℝ) (β ν : ℝ) (φ : Measure Ξ) (f : X × A → Ξ → X) :
    X → A → (X → ℝ) → ℝ :=
  fun x a v => Real.exp (rhat (x, a)) * (∫ ξ, v (f (x, a) ξ) ^ ν ∂φ) ^ (β / ν)

/-- Taking logs (p. 243): `B_MKP(x, a, v) = exp[B_RS(x, a, ln v)]` with `r̂ = ln r` and `θ = ν`. -/
theorem mkpAgg_eq_exp (rhat : X × A → ℝ) (β ν : ℝ) (φ : Measure Ξ) [IsProbabilityMeasure φ]
    {f : X × A → Ξ → X} (hf : Measurable (uncurry f)) (v : PosValues X) (x : X) (a : A) :
    mkpAgg rhat β ν φ f x a v.1 =
      Real.exp (ceAgg rhat β f (entropicCE φ ν) x a (Real.log ∘ v.1)) := by
  have hL : IsLInf φ fun ξ => Real.log (v.1 (f (x, a) ξ)) := by
    obtain ⟨K, hK⟩ := v.abs_log_le
    exact ⟨(Real.measurable_log.comp
      (v.2.1.comp (measurable_section hf (x, a)))).aestronglyMeasurable,
      K, Eventually.of_forall fun ξ => hK _⟩
  have hI : ∫ ξ, v.1 (f (x, a) ξ) ^ ν ∂φ = ∫ ξ, Real.exp (ν * Real.log (v.1 (f (x, a) ξ))) ∂φ :=
    integral_congr_ae (Eventually.of_forall fun ξ => by
      change v.1 (f (x, a) ξ) ^ ν = Real.exp (ν * Real.log (v.1 (f (x, a) ξ)))
      rw [Real.rpow_def_of_pos (v.pos _), mul_comm])
  change Real.exp (rhat (x, a)) * (∫ ξ, v.1 (f (x, a) ξ) ^ ν ∂φ) ^ (β / ν) =
    Real.exp (rhat (x, a) +
      β * (ν⁻¹ * Real.log (∫ ξ, Real.exp (ν * Real.log (v.1 (f (x, a) ξ))) ∂φ)))
  rw [hI, Real.rpow_def_of_pos (integral_exp_pos' hL ν), ← Real.exp_add]
  congr 1
  ring

/-- The multiplicative Kreps–Porteus RDP `(Γ, V, B_MKP)` (§7.3.4), with `V` the measurable `v`
satisfying `e^{−K} ≤ v ≤ e^K` for some `K`. -/
noncomputable def mkpRDP (Γ : X → Set A) (rhat : X × A → ℝ) (hr : Measurable rhat)
    (hrb : ∃ C, ∀ x, ∀ a ∈ Γ x, |rhat (x, a)| ≤ C) {β : ℝ} (hβ : 0 ≤ β) (φ : Measure Ξ)
    [IsProbabilityMeasure φ] {f : X × A → Ξ → X} (hf : Measurable (uncurry f)) {ν : ℝ}
    (hν : ν ≠ 0) (hΓ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x) :
    RDP X A (PosValues X) where
  ev v := v.1
  ev_le_iff _ _ := Iff.rfl
  Γ := Γ
  B := mkpAgg rhat β ν φ f
  mono x a ha v w h := by
    rw [mkpAgg_eq_exp rhat β ν φ hf v, mkpAgg_eq_exp rhat β ν φ hf w]
    exact Real.exp_le_exp.2 ((rsRDP Γ rhat hr hrb hβ φ hf hν hΓ).mono x a ha v.log w.log
      (BM.le_def.2 fun y => Real.log_le_log (v.pos y) (h y)))
  consistent σ hσ hσΓ v := by
    let R := rsRDP Γ rhat hr hrb hβ φ hf hν hΓ
    refine ⟨PosValues.exp (R.toRDP.adp.T ⟨σ, hσ, hσΓ⟩ v.log), funext fun x => ?_⟩
    change Real.exp ((R.toRDP.adp.T ⟨σ, hσ, hσΓ⟩ v.log).toFun x) = _
    rw [R.toRDP_T_apply, mkpAgg_eq_exp rhat β ν φ hf v]
    rfl
  exists_policy := hΓ

/-- **Exercise 7.3.4** (p. 244): the multiplicative Kreps–Porteus RDP and the risk-sensitive RDP
(with `r̂ = ln r` and `θ = ν`) generate isomorphic ADPs: `v ↦ ln v` is an order isomorphism
conjugating their policy operators (Exercise 7.1.5 with `φ = ln`). -/
theorem exercise_7_3_4 (Γ : X → Set A) (rhat : X × A → ℝ) (hr : Measurable rhat)
    (hrb : ∃ C, ∀ x, ∀ a ∈ Γ x, |rhat (x, a)| ≤ C) {β : ℝ} (hβ : 0 ≤ β) (φ : Measure Ξ)
    [IsProbabilityMeasure φ] {f : X × A → Ξ → X} (hf : Measurable (uncurry f)) {ν : ℝ}
    (hν : ν ≠ 0) (hΓ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x) :
    ∃ F : PosValues X ≃o BM X, (∀ v, (F v).toFun = Real.log ∘ v.1) ∧
      ∀ (σ : (mkpRDP Γ rhat hr hrb hβ φ hf hν hΓ).Policy)
        (σ' : (rsRDP Γ rhat hr hrb hβ φ hf hν hΓ).toRDP.Policy), σ.1 = σ'.1 → ∀ v,
        F ((mkpRDP Γ rhat hr hrb hβ φ hf hν hΓ).adp.T σ v) =
          (rsRDP Γ rhat hr hrb hβ φ hf hν hΓ).toRDP.adp.T σ' (F v) :=
  (mkpRDP Γ rhat hr hrb hβ φ hf hν hΓ).exercise_7_1_5 (rsRDP Γ rhat hr hrb hβ φ hf hν hΓ).toRDP
    Real.log Real.exp Real.strictMonoOn_log (fun _ ht => Real.exp_log ht)
    (fun v x => v.pos x) (fun v => ⟨v.log, rfl⟩)
    (fun h => ⟨PosValues.exp h, funext fun _ => (Real.log_exp _).symm⟩)
    (fun x a _ v => mkpAgg_eq_exp rhat β ν φ hf v x a)

end SargentStachurski.RecursiveDecisionProcesses
