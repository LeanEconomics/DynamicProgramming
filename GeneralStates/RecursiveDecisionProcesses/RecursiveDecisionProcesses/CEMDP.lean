/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveDecisionProcesses.CertaintyEquivalents
import RecursiveDecisionProcesses.BoundedRDP
import Mathlib.MeasureTheory.Integral.Prod

/-!
# MDPs with certainty equivalents

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §7.2.5 (pp. 230–231).

* The aggregator (7.24), `B_ℰ(x, a, v) = r(x, a) + β ℰ[v(f(x, a, ξ))]` with `ξ ∼ φ` on `Z`, as an
  RDP on `bX` (`ceBRDP`). With `ℰ = 𝔼` this is (7.23). `r` need only be bounded on `G`, and the
  measurability of `(x, a) ↦ ℰ[v(f(x, a, ξ))]` is the book's standing assumption.
* Cash invariance of `ℰ` gives Blackwell's condition with `λ = β`.
* **Proposition 7.2.10**: under Assumption 7.2.11, with `ℰ` continuous, the fundamental optimality
  properties hold, `v* ∈ bcX` and VFI converges geometrically on `bcX` (Proposition 7.2.2).
  Assumption 7.2.11 (i) is stated as the maximum theorem for `Γ` (`HasMaxSelections`); the state
  and action spaces are first countable, as the book's metric spaces are.
-/

open Set Function Filter Topology MeasureTheory

namespace SargentStachurski.RecursiveDecisionProcesses

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

variable {X A Z : Type*} [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace Z]

/-- The aggregator (7.24): `B_ℰ(x, a, v) = r(x, a) + β ℰ[v(f(x, a, ξ))]`. -/
def ceAgg (r : X × A → ℝ) (β : ℝ) (f : X × A → Z → X) (E : (Z → ℝ) → ℝ) :
    X → A → (X → ℝ) → ℝ :=
  fun x a v => r (x, a) + β * E fun z => v (f (x, a) z)

theorem isLInf_comp (φ : Measure Z) {f : X × A → Z → X} (hf : Measurable (uncurry f))
    (v : BM X) (p : X × A) : IsLInf φ fun z => v.toFun (f p z) :=
  ⟨(v.measurable'.comp (measurable_section hf p)).aestronglyMeasurable, ‖v‖,
    Eventually.of_forall fun _ => BM.abs_le_norm v _⟩

omit [MeasurableSpace X] [MeasurableSpace A] in
/-- A certainty equivalent maps `|W| ≤ N` into `[ℰ(0) − N, ℰ(0) + N]`. -/
theorem IsCertEquiv.abs_sub_le {φ : Measure Z} {E : (Z → ℝ) → ℝ} (hE : IsCertEquiv φ E)
    {W : Z → ℝ} (hW : IsLInf φ W) {N : ℝ} (hN : ∀ᵐ z ∂φ, |W z| ≤ N) :
    |E W - E fun _ => 0| ≤ N := by
  have h1 := hE.cash (fun _ => 0) (isLInf_const 0) N
  have h2 := hE.cash (fun _ => 0) (isLInf_const 0) (-N)
  have hup := hE.mono W _ hW ((isLInf_const 0).add_const N)
    (hN.mono fun z hz => by simpa using le_of_abs_le hz)
  have hlo := hE.mono _ W ((isLInf_const 0).add_const (-N)) hW
    (hN.mono fun z hz => by simpa using neg_le_of_abs_le hz)
  rw [h1] at hup
  rw [h2] at hlo
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-- The RDP `(Γ, bX, B_ℰ)` of §7.2.5.2: `r` measurable and bounded on `G`, `0 ≤ β`, `ξ ∼ φ`,
`f` measurable, `ℰ` a certainty equivalent on `L∞(Z, φ)` with `(x, a) ↦ ℰ[v(f(x, a, ξ))]`
measurable. -/
noncomputable def ceBRDP (Γ : X → Set A) (r : X × A → ℝ) (hr : Measurable r)
    (hrb : ∃ C, ∀ x, ∀ a ∈ Γ x, |r (x, a)| ≤ C) {β : ℝ} (hβ : 0 ≤ β) (φ : Measure Z)
    {f : X × A → Z → X} (hf : Measurable (uncurry f)) {E : (Z → ℝ) → ℝ} (hE : IsCertEquiv φ E)
    (hEm : ∀ v : BM X, Measurable fun p : X × A => E fun z => v.toFun (f p z))
    (hΓ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x) : BRDP X A where
  Γ := Γ
  B := ceAgg r β f E
  measurable v := hr.add ((hEm v).const_mul β)
  mono x a _ v w hvw := add_le_add le_rfl (mul_le_mul_of_nonneg_left (hE.mono _ _
    (isLInf_comp φ hf v (x, a)) (isLInf_comp φ hf w (x, a))
    (Eventually.of_forall fun _ => BM.le_def.1 hvw _)) hβ)
  bdd v := by
    obtain ⟨C, hC⟩ := hrb
    refine ⟨C + β * (|E fun _ => 0| + ‖v‖), fun x a ha => ?_⟩
    have hW := hE.abs_sub_le (isLInf_comp φ hf v (x, a))
      (Eventually.of_forall fun z => BM.abs_le_norm v (f (x, a) z))
    have hEW : |E fun z => v.toFun (f (x, a) z)| ≤ |E fun _ => 0| + ‖v‖ := by
      have := abs_sub_abs_le_abs_sub (E fun z => v.toFun (f (x, a) z)) (E fun _ => 0)
      linarith
    change |r (x, a) + β * E (fun z => v.toFun (f (x, a) z))| ≤ _
    refine (abs_add_le _ _).trans (add_le_add (hC x a ha) ?_)
    rw [abs_mul, abs_of_nonneg hβ]
    exact mul_le_mul_of_nonneg_left hEW hβ
  exists_policy := hΓ

/-- Cash invariance gives Blackwell's condition with `λ = β`:
`B_ℰ(x, a, v + κ) = B_ℰ(x, a, v) + βκ` (proof of Proposition 7.2.10). -/
theorem ceBRDP_isBlackwell (Γ : X → Set A) (r : X × A → ℝ) (hr : Measurable r)
    (hrb : ∃ C, ∀ x, ∀ a ∈ Γ x, |r (x, a)| ≤ C) {β : ℝ} (hβ : 0 ≤ β) (φ : Measure Z)
    {f : X × A → Z → X} (hf : Measurable (uncurry f)) {E : (Z → ℝ) → ℝ} (hE : IsCertEquiv φ E)
    (hEm : ∀ v : BM X, Measurable fun p : X × A => E fun z => v.toFun (f p z))
    (hΓ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x) :
    (ceBRDP Γ r hr hrb hβ φ hf hE hEm hΓ).IsBlackwell β := by
  intro x a _ v κ _
  have h := hE.cash _ (isLInf_comp φ hf v (x, a)) κ
  change r (x, a) + β * (E fun z => v.toFun (f (x, a) z) + κ) ≤
    r (x, a) + β * (E fun z => v.toFun (f (x, a) z)) + β * κ
  rw [h]
  linarith

/-- If `ℰ` is continuous, `f(·, z)` is continuous on `G` and `v` is continuous, then
`(x, a) ↦ ℰ[v(f(x, a, ξ))]` is continuous on `G` (proof of Proposition 7.2.10). -/
theorem continuousOn_ce [TopologicalSpace X] [TopologicalSpace A] [FirstCountableTopology X]
    [FirstCountableTopology A] {φ : Measure Z} {f : X × A → Z → X} (hf : Measurable (uncurry f))
    {E : (Z → ℝ) → ℝ} (hEc : IsContinuousCE φ E) {G : Set (X × A)}
    (hfc : ∀ z, ContinuousOn (fun p => f p z) G) {v : BM X} (hv : Continuous v.toFun) :
    ContinuousOn (fun p => E fun z => v.toFun (f p z)) G := by
  intro p hp
  refine tendsto_iff_seq_tendsto.2 fun ps hps => ?_
  exact hEc (fun n z => v.toFun (f (ps n) z)) (fun z => v.toFun (f p z)) ‖v‖
    (fun n => (isLInf_comp φ hf v (ps n)).1)
    (fun _ => Eventually.of_forall fun _ => BM.abs_le_norm v _) (isLInf_comp φ hf v p)
    (Eventually.of_forall fun z => (hv.tendsto _).comp ((hfc z p hp).tendsto.comp hps))

/-- **Proposition 7.2.10** (p. 231): under Assumption 7.2.11 (the maximum theorem for `Γ`, `r`
bounded and continuous on `G`, `f(·, z)` continuous on `G`), if `ℰ` is a continuous certainty
equivalent and `0 ≤ β < 1`, then for `(Γ, bX, B_ℰ)` (i) the fundamental optimality properties hold,
(ii) `v* ∈ bcX` and (iii) VFI converges geometrically on `bcX`. -/
theorem proposition_7_2_10 [Nonempty X] [TopologicalSpace X] [TopologicalSpace A]
    [FirstCountableTopology X] [FirstCountableTopology A] (Γ : X → Set A) (r : X × A → ℝ)
    (hr : Measurable r) (hrb : ∃ C, ∀ x, ∀ a ∈ Γ x, |r (x, a)| ≤ C) {β : ℝ} (hβ : 0 ≤ β)
    (hβ1 : β < 1) (φ : Measure Z) {f : X × A → Z → X} (hf : Measurable (uncurry f))
    {E : (Z → ℝ) → ℝ} (hE : IsCertEquiv φ E)
    (hEm : ∀ v : BM X, Measurable fun p : X × A => E fun z => v.toFun (f p z))
    (hΓ : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x) (hΓmax : HasMaxSelections Γ)
    (hrc : ContinuousOn r {p | p.2 ∈ Γ p.1})
    (hfc : ∀ z, ContinuousOn (fun p => f p z) {p | p.2 ∈ Γ p.1}) (hEc : IsContinuousCE φ E) :
    ∃ hw : (ceBRDP Γ r hr hrb hβ φ hf hE hEm hΓ).toRDP.adp.WellPosed,
      (ceBRDP Γ r hr hrb hβ φ hf hE hEm hΓ).toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ LDP.bc X,
        (ceBRDP Γ r hr hrb hβ φ hf hE hEm hΓ).toRDP.adp.VFIGeometric (LDP.bc X) vstar := by
  have hΓ' : HasMaxSelections (ceBRDP Γ r hr hrb hβ φ hf hE hEm hΓ).Γ := hΓmax
  obtain ⟨hw, hFO, vstar, hv, hgeo, -⟩ := (ceBRDP Γ r hr hrb hβ φ hf hE hEm hΓ).proposition_7_2_2
    hΓ' hβ hβ1 (ceBRDP_isBlackwell Γ r hr hrb hβ φ hf hE hEm hΓ) fun v hv =>
      hrc.add (continuousOn_const.mul (continuousOn_ce hf hEc hfc hv))
  exact ⟨hw, hFO, vstar, hv, hgeo⟩

/-- `p ↦ ∫ h(f(p, ξ))φ(dξ)` is measurable. -/
theorem measurable_integral_comp {Y : Type*} [MeasurableSpace Y] {φ : Measure Z} [SFinite φ]
    {f : Y → Z → X} (hf : Measurable (uncurry f)) {h : X → ℝ} (hh : Measurable h) :
    Measurable fun p => ∫ z, h (f p z) ∂φ :=
  ((hh.comp hf).stronglyMeasurable.integral_prod_right' (ν := φ)).measurable

/-- The measurability assumption of §7.2.5.2 holds for `ℰ = 𝔼`. -/
theorem measurable_meanCE_comp {φ : Measure Z} [SFinite φ] {f : X × A → Z → X}
    (hf : Measurable (uncurry f)) (v : BM X) :
    Measurable fun p : X × A => meanCE φ fun z => v.toFun (f p z) :=
  measurable_integral_comp hf v.measurable'

/-- The measurability assumption of §7.2.5.2 holds for the entropic certainty equivalent. -/
theorem measurable_entropicCE_comp {φ : Measure Z} [SFinite φ] {f : X × A → Z → X}
    (hf : Measurable (uncurry f)) (θ : ℝ) (v : BM X) :
    Measurable fun p : X × A => entropicCE φ θ fun z => v.toFun (f p z) :=
  (Real.measurable_log.comp (measurable_integral_comp hf
    (Real.measurable_exp.comp (measurable_const.mul v.measurable')))).const_mul _

end SargentStachurski.RecursiveDecisionProcesses
