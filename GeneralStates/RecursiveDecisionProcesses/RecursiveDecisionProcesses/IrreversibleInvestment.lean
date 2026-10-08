/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveDecisionProcesses.CEMDP

/-!
# Irreversible investment

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §7.3.2–§7.3.3 (pp. 233–241).

Capital `k ∈ ℝ`, an exogenous state `z ∈ E` with `Z' = g(Z, ξ)`, `ξ ∼ φ`, investment
`i ∈ Γ(k, z) = [0, θf(k, z)]`, and the aggregator
`B(k, z, i, v) = f(k, z) − i + β ℰ[v(i + (1 − δ)k, g(z, ξ))]`.

* Assumption 7.3.1: `f` bounded and continuous; `g` measurable with `g(·, ξ)` continuous for each
  `ξ` (implied by joint continuity). Nonemptiness of `Γ` needs `θf ≥ 0`; `f ≥ 0` and `θ ≥ 0` are
  assumed. The exogenous state lies in any first countable Borel space (`ℝᵐ` in the book).
* **Proposition 7.3.1** and **Exercise 7.3.3**: with `ℰ = 𝔼`, the conclusions of
  Proposition 7.2.10.
* **Proposition 7.3.2**: the same for any continuous certainty equivalent `ℰ` (§7.3.2.2).
* **Example 7.3.1**: Proposition 7.3.2 applies to the entropic certainty equivalent (the CVaR case
  rests on Example 7.2.2, not formalised).
* §7.3.3.2: the risk-sensitive form of the robust firm problem,
  `B = f − i − (β/γ) ln ∫ exp[−γ v(k', g(z, ξ))]φ(dξ)`, `γ > 0`, satisfies the conclusions of
  Proposition 7.3.2. The passage from the robust (7.3.3.1) to the risk-sensitive form is the
  duality (7.22), which is not formalised.
-/

open Set Function Filter Topology MeasureTheory

namespace SargentStachurski.RecursiveDecisionProcesses

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

variable (E Ξ : Type*) [TopologicalSpace E] [MeasurableSpace E] [MeasurableSpace Ξ] in
/-- The irreversible investment model of §7.3.2.1 under Assumption 7.3.1. -/
structure Investment where
  /-- production (revenue) -/
  F : ℝ × E → ℝ
  continuous_F : Continuous F
  F_nonneg : ∀ x, 0 ≤ F x
  F_bdd : ∃ C, ∀ x, F x ≤ C
  /-- the exogenous law of motion -/
  g : E → Ξ → E
  measurable_g : Measurable (uncurry g)
  continuous_g : ∀ ξ, Continuous fun z => g z ξ
  /-- the borrowing constraint parameter -/
  θ : ℝ
  θ_nonneg : 0 ≤ θ
  /-- the depreciation rate -/
  δ : ℝ
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- the shock distribution -/
  φ : Measure Ξ
  [isProb : IsProbabilityMeasure φ]

namespace Investment

attribute [local instance] Investment.isProb

variable {E Ξ : Type*} [TopologicalSpace E] [FirstCountableTopology E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [MeasurableSpace Ξ] (M : Investment E Ξ)

/-- `Γ(k, z) = [0, θf(k, z)]`. -/
def Γ (x : ℝ × E) : Set ℝ := Icc 0 (M.θ * M.F x)

/-- The reward `r(k, z, i) = f(k, z) − i`. -/
def r (p : (ℝ × E) × ℝ) : ℝ := M.F p.1 - p.2

/-- The transition `(k, z, i, ξ) ↦ (i + (1 − δ)k, g(z, ξ))`. -/
def next (p : (ℝ × E) × ℝ) (ξ : Ξ) : ℝ × E := (p.2 + (1 - M.δ) * p.1.1, M.g p.1.2 ξ)

omit [FirstCountableTopology E] in
theorem measurable_r : Measurable M.r :=
  (M.continuous_F.measurable.comp measurable_fst).sub measurable_snd

omit [FirstCountableTopology E] [OpensMeasurableSpace E] in
theorem r_bdd : ∃ C, ∀ x, ∀ a ∈ M.Γ x, |M.r (x, a)| ≤ C := by
  obtain ⟨C, hC⟩ := M.F_bdd
  refine ⟨C + M.θ * C, fun x a ha => ?_⟩
  have h1 := hC x
  have h2 := M.F_nonneg x
  have h3 := mul_le_mul_of_nonneg_left h1 M.θ_nonneg
  change |M.F x - a| ≤ _
  rw [abs_le]
  constructor <;> linarith [ha.1, ha.2]

omit [FirstCountableTopology E] [OpensMeasurableSpace E] in
theorem measurable_next : Measurable (uncurry M.next) :=
  ((measurable_snd.comp measurable_fst).add (measurable_const.mul
    (measurable_fst.comp (measurable_fst.comp measurable_fst)))).prodMk
    (M.measurable_g.comp ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
      measurable_snd))

omit [FirstCountableTopology E] [OpensMeasurableSpace E] in
theorem exists_policy : ∃ σ : ℝ × E → ℝ, Measurable σ ∧ ∀ x, σ x ∈ M.Γ x :=
  ⟨fun _ => 0, measurable_const, fun x => ⟨le_rfl, mul_nonneg M.θ_nonneg (M.F_nonneg x)⟩⟩

theorem hasMaxSelections : HasMaxSelections M.Γ :=
  hasMaxSelections_Icc continuous_const (continuous_const.mul M.continuous_F)
    fun x => mul_nonneg M.θ_nonneg (M.F_nonneg x)

/-- The measurability assumption of §7.3.2.2: `(k, z, i) ↦ ℰ[v(i + (1 − δ)k, g(z, ξ))]` is
measurable for every `v ∈ bX`. -/
def IsMeasurableCE (E' : (Ξ → ℝ) → ℝ) : Prop :=
  ∀ v : BM (ℝ × E), Measurable fun p : (ℝ × E) × ℝ => E' fun ξ => v.toFun (M.next p ξ)

/-- The firm problem with certainty equivalent `ℰ` as an RDP on `bX` (§7.3.2.2). -/
noncomputable def rdp {E' : (Ξ → ℝ) → ℝ} (hE : IsCertEquiv M.φ E') (hEm : M.IsMeasurableCE E') :
    BRDP (ℝ × E) ℝ :=
  ceBRDP M.Γ M.r M.measurable_r M.r_bdd M.β_nonneg M.φ M.measurable_next hE hEm M.exists_policy

omit [FirstCountableTopology E] in
/-- The aggregator (7.26): `B(k, z, i, v) = f(k, z) − i + β ℰ[v(i + (1 − δ)k, g(z, ξ))]`. -/
theorem rdp_B {E' : (Ξ → ℝ) → ℝ} (hE : IsCertEquiv M.φ E') (hEm : M.IsMeasurableCE E')
    (k : ℝ) (z : E) (i : ℝ) (v : ℝ × E → ℝ) :
    (M.rdp hE hEm).B (k, z) i v =
      M.F (k, z) - i + M.β * E' fun ξ => v (i + (1 - M.δ) * k, M.g z ξ) :=
  rfl

/-- **Proposition 7.3.2** (p. 237): if Assumption 7.3.1 holds and `ℰ` is a continuous certainty
equivalent, then (i) the fundamental optimality properties hold, (ii) `v* ∈ bcX` and (iii) VFI
converges geometrically on `bcX`. -/
theorem proposition_7_3_2 [Nonempty E] {E' : (Ξ → ℝ) → ℝ} (hE : IsCertEquiv M.φ E')
    (hEm : M.IsMeasurableCE E') (hEc : IsContinuousCE M.φ E') :
    ∃ hw : (M.rdp hE hEm).toRDP.adp.WellPosed, (M.rdp hE hEm).toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ LDP.bc (ℝ × E), (M.rdp hE hEm).toRDP.adp.VFIGeometric (LDP.bc (ℝ × E)) vstar :=
  proposition_7_2_10 M.Γ M.r M.measurable_r M.r_bdd M.β_nonneg M.β_lt_one M.φ M.measurable_next
    hE hEm M.exists_policy M.hasMaxSelections
    ((M.continuous_F.comp continuous_fst).sub continuous_snd).continuousOn
    (fun ξ => ((continuous_snd.add (continuous_const.mul
      (continuous_fst.comp continuous_fst))).prodMk
      ((M.continuous_g ξ).comp (continuous_snd.comp continuous_fst))).continuousOn) hEc

/-- The risk-neutral firm problem (§7.3.2.1): `ℰ = 𝔼`. -/
noncomputable def meanRDP : BRDP (ℝ × E) ℝ :=
  M.rdp meanCE_isCoherent.1 (measurable_meanCE_comp M.measurable_next)

/-- The firm problem with the entropic certainty equivalent `ℰ^θ`. -/
noncomputable def entropicRDP {θ : ℝ} (hθ : θ ≠ 0) : BRDP (ℝ × E) ℝ :=
  M.rdp (entropicCE_isCertEquiv hθ) (measurable_entropicCE_comp M.measurable_next θ)

/-- **Proposition 7.3.1** (p. 234) and **Exercise 7.3.3** (p. 234): under Assumption 7.3.1, the
risk-neutral firm problem `B(k, z, i, v) = f(k, z) − i + β ∫ v(i + (1 − δ)k, g(z, ξ))φ(dξ)` is an
RDP, the fundamental optimality properties hold, `v* ∈ bcX` and VFI converges geometrically on
`bcX` (Proposition 7.2.10 with `ℰ = 𝔼`). -/
theorem proposition_7_3_1 [Nonempty E] :
    ∃ hw : M.meanRDP.toRDP.adp.WellPosed, M.meanRDP.toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ LDP.bc (ℝ × E), M.meanRDP.toRDP.adp.VFIGeometric (LDP.bc (ℝ × E)) vstar :=
  M.proposition_7_3_2 _ _ example_7_2_1

/-- **Example 7.3.1** (p. 237): Proposition 7.3.2 applies with the entropic certainty equivalent
(Exercise 7.2.6), for every `θ ≠ 0`. -/
theorem example_7_3_1 [Nonempty E] {θ : ℝ} (hθ : θ ≠ 0) :
    ∃ hw : (M.entropicRDP hθ).toRDP.adp.WellPosed,
      (M.entropicRDP hθ).toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ LDP.bc (ℝ × E), (M.entropicRDP hθ).toRDP.adp.VFIGeometric (LDP.bc (ℝ × E)) vstar :=
  M.proposition_7_3_2 _ _ (exercise_7_2_6 θ)

/-- §7.3.3.2 (p. 240): the risk-sensitive form of the robust firm problem has aggregator
`f(k, z) − i − (β/γ) ln ∫ exp[−γ v(k', g(z, ξ))]φ(dξ)`, the case `ℰ = ℰ_γ` (`θ = −γ`) of (7.26);
for `γ > 0` the fundamental optimality properties hold, `v* ∈ bcX` and VFI converges
geometrically on `bcX`. -/
theorem section_7_3_3 [Nonempty E] {γ : ℝ} (hγ : 0 < γ) :
    (∀ k z i (v : ℝ × E → ℝ), (M.entropicRDP (neg_ne_zero.2 hγ.ne')).B (k, z) i v =
        M.F (k, z) - i - M.β / γ *
          Real.log (∫ ξ, Real.exp (-γ * v (i + (1 - M.δ) * k, M.g z ξ)) ∂M.φ)) ∧
    ∃ hw : (M.entropicRDP (neg_ne_zero.2 hγ.ne')).toRDP.adp.WellPosed,
      (M.entropicRDP (neg_ne_zero.2 hγ.ne')).toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ LDP.bc (ℝ × E),
        (M.entropicRDP (neg_ne_zero.2 hγ.ne')).toRDP.adp.VFIGeometric (LDP.bc (ℝ × E)) vstar := by
  refine ⟨fun k z i v => ?_, M.example_7_3_1 (neg_ne_zero.2 hγ.ne')⟩
  change M.F (k, z) - i + M.β * ((-γ)⁻¹ * Real.log
    (∫ ξ, Real.exp (-γ * v (i + (1 - M.δ) * k, M.g z ξ)) ∂M.φ)) = _
  field_simp
  ring

end Investment

end SargentStachurski.RecursiveDecisionProcesses
