/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AdditionalApplications.RDP
import AdditionalApplications.LDPOptimality

/-!
# Bounded contracting RDPs

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §7.2.1 (pp. 218–220).

* §7.2.1.1: value space `V = bX`, an aggregator `B` with `(x, a) ↦ B(x, a, v)` measurable (on
  `X × A`; values off `G` are irrelevant) and monotone in `v`. With `B` bounded in `(x, a) ∈ G` for
  each `v`, `(Γ, bX, B)` is an RDP (`BRDP.toRDP`). The book's "the function `B` is bounded" must be
  read for each fixed `v`: with Blackwell's condition, `v ↦ B(x, a, v)` is unbounded on `bX`.
* Assumption 7.2.1: Blackwell's condition `B(x, a, v + κ) ≤ B(x, a, v) + λκ`, `λ ∈ [0, 1)`.
* **Proposition 7.2.1** (finite actions): the fundamental optimality properties hold, VFI
  converges geometrically on `V` and OPI and HPI converge; if `X` is also finite, HPI reaches `v*`
  in finitely many steps.
* **Proposition 7.2.2** (continuous case): under Assumption 7.2.2 (the maximum theorem for `Γ` and
  `B` continuous on `G` for `v ∈ bcX`), the fundamental optimality properties hold, `v* ∈ bcX` and
  VFI converges geometrically on `bcX`; under Assumption 7.2.3 OPI and HPI converge.
-/

open Set Function Filter Topology MeasureTheory

namespace SargentStachurski.AdditionalApplications

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

/-- The framework of §7.2.1.1, with `B` bounded on `G` for each `v` (Assumption 7.2.1, first
part): value space `bX`, `B` measurable and monotone in `v`. -/
structure BRDP (X A : Type*) [MeasurableSpace X] [MeasurableSpace A] where
  /-- the feasible correspondence -/
  Γ : X → Set A
  /-- the aggregator -/
  B : X → A → (X → ℝ) → ℝ
  /-- `(x, a) ↦ B(x, a, v)` is measurable -/
  measurable : ∀ v : BM X, Measurable fun p : X × A => B p.1 p.2 v.toFun
  /-- `B` is monotone in `v` on `G` -/
  mono : ∀ x, ∀ a ∈ Γ x, ∀ v w : BM X, v ≤ w → B x a v.toFun ≤ B x a w.toFun
  /-- `B` is bounded on `G` for each `v` -/
  bdd : ∀ v : BM X, ∃ C, ∀ x, ∀ a ∈ Γ x, |B x a v.toFun| ≤ C
  /-- a feasible policy exists -/
  exists_policy : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x

namespace BRDP

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A] (M : BRDP X A)

/-- §7.2.1.1 (p. 218): `(Γ, bX, B)` is an RDP. -/
noncomputable def toRDP : RDP X A (BM X) where
  ev := BM.toFun
  ev_le_iff _ _ := Iff.rfl
  Γ := M.Γ
  B := M.B
  mono := M.mono
  consistent σ hσ hσΓ v := by
    obtain ⟨C, hC⟩ := M.bdd v
    exact ⟨⟨fun x => M.B x (σ x) v.toFun, (M.measurable v).comp (measurable_id.prodMk hσ),
      ⟨C, fun x => hC x _ (hσΓ x)⟩⟩, rfl⟩
  exists_policy := M.exists_policy

theorem toRDP_T_apply (σ : M.toRDP.Policy) (v : BM X) (x : X) :
    (M.toRDP.adp.T σ v).toFun x = M.B x (σ.1 x) v.toFun :=
  M.toRDP.ev_adp_T σ v x

/-- Blackwell's condition (Assumption 7.2.1): `B(x, a, v + κ) ≤ B(x, a, v) + λκ` on `G`. -/
def IsBlackwell (lam : ℝ) : Prop :=
  ∀ x, ∀ a ∈ M.Γ x, ∀ v : BM X, ∀ κ : ℝ, 0 ≤ κ →
    M.B x a (fun y => v.toFun y + κ) ≤ M.B x a v.toFun + lam * κ

/-- Blackwell's condition for the policy operators, with `e = 𝟙`. -/
theorem T_blackwell {lam : ℝ} (hB : M.IsBlackwell lam) (σ : M.toRDP.Policy) (v : BM X)
    (κ : ℝ) (hκ : 0 ≤ κ) :
    M.toRDP.adp.T σ (v + κ • BM.const 1) ≤ M.toRDP.adp.T σ v + (lam * κ) • BM.const 1 := by
  refine BM.le_def.2 fun x => ?_
  have h1 : (v + κ • BM.const 1).toFun = fun y => v.toFun y + κ := funext fun y => by
    simp [BM.const_apply]
  change (M.toRDP.adp.T σ (v + κ • BM.const 1)).toFun x ≤
    (M.toRDP.adp.T σ v).toFun x + lam * κ * 1
  rw [M.toRDP_T_apply, M.toRDP_T_apply, h1, mul_one]
  exact hB x _ (σ.2.2 x) v κ hκ

/-- With finitely many actions and measurable sections `{x | a ∈ Γ(x)}`, the RDP is regular
(Lemma 7.1.1). -/
theorem regular_of_finite [Finite A] (hΓ : ∀ a, MeasurableSet {x | a ∈ M.Γ x}) :
    M.toRDP.adp.Regular := fun v =>
  (M.toRDP.lemma_7_1_1 hΓ v fun _ =>
    (M.measurable v).comp (measurable_id.prodMk measurable_const)).2.1

/-- **Proposition 7.2.1** (p. 219): under Assumption 7.2.1, with `A` finite (and measurable
sections `{x | a ∈ Γ(x)}`), (i) the fundamental optimality properties hold, (ii) VFI converges
geometrically on `V = bX`, and (iii) OPI and HPI converge. -/
theorem proposition_7_2_1 [Nonempty X] [Finite A] (hΓ : ∀ a, MeasurableSet {x | a ∈ M.Γ x})
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hB : M.IsBlackwell lam) :
    ∃ hw : M.toRDP.adp.WellPosed, M.toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar, M.toRDP.adp.VFIGeometric univ vstar ∧
        ∀ g, M.toRDP.adp.IsSelector g →
          M.toRDP.adp.OPIConverges g vstar ∧ M.toRDP.adp.HPIConverges hw g vstar := by
  have hr := M.regular_of_finite hΓ
  obtain ⟨hw, hFO, vstar, -, hgeo, hconv⟩ := BanachLattice.theorem_4_1_3_univ
    BM.isNormalizedOrderUnit_one M.toRDP.adp hlam0 hlam1 (M.T_blackwell hB)
    ⟨isClosed_univ, fun v _ => hr v, mapsTo_univ _ _⟩ univ_nonempty
  exact ⟨hw, hFO, vstar, hgeo, hconv hr⟩

/-- **Proposition 7.2.1**, last claim (p. 219): if `X` is also finite, the fundamental optimality
properties hold and HPI reaches `v*` in finitely many steps from every `v ∈ V_U`
(Lemma 3.1.1 and Theorem 2.2.6). -/
theorem proposition_7_2_1_finite [Nonempty X] [Finite X] [Finite A]
    (hΓ : ∀ a, MeasurableSet {x | a ∈ M.Γ x}) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hB : M.IsBlackwell lam) :
    ∃ hw : M.toRDP.adp.WellPosed, M.toRDP.adp.FundamentalOptimality hw ∧
      ∀ g, M.toRDP.adp.IsSelector g → ∀ v ∈ M.toRDP.adp.VU,
        ∃ n, M.toRDP.adp.IsValueFunction ((M.toRDP.adp.howard hw g)^[n] v) := by
  have hT : ∀ σ v w, dist (M.toRDP.adp.T σ v) (M.toRDP.adp.T σ w) ≤ lam * dist v w := by
    intro σ v w
    rw [dist_eq_norm, dist_eq_norm]
    exact BanachLattice.lemma_4_1_2 BM.isNormalizedOrderUnit_one (M.toRDP.adp.mono σ) hlam0
      (M.T_blackwell hB σ) v w
  have hgs := ADP.isGloballyStable_of_contraction ⟨0⟩ hlam0 hlam1 hT
  have hfin : M.toRDP.adp.IsFinite := Set.finite_range _
  exact ⟨_, ADP.fundamentalOptimality_of_finite hgs.isOrderStable (M.regular_of_finite hΓ) hfin⟩

/-- Under Assumption 7.2.2, a greedy policy exists at every `v ∈ bcX` and `Tv ∈ bcX`
(Lemma 7.1.2). -/
theorem greedy_of_continuous [TopologicalSpace X] [TopologicalSpace A]
    (hΓ : HasMaxSelections M.Γ) {v : BM X}
    (hc : ContinuousOn (fun p : X × A => M.B p.1 p.2 v.toFun) {p | p.2 ∈ M.Γ p.1}) :
    v ∈ M.toRDP.adp.VG ∧ Continuous (M.toRDP.adp.bellman v).toFun := by
  obtain ⟨-, -, hv, hTc, -⟩ := M.toRDP.lemma_7_1_2 hΓ v hc
  exact ⟨hv, hTc⟩

/-- **Proposition 7.2.2** (p. 220): under Assumptions 7.2.1 and 7.2.2 (the maximum theorem for `Γ`,
Theorem A.3.3, and `B` continuous on `G` for `v ∈ bcX`), (i) the fundamental optimality properties
hold, (ii) `v* ∈ bcX` and (iii) VFI converges geometrically on `bcX`. Under Assumption 7.2.3
(`B` continuous on `G` for every `v ∈ bX`), OPI and HPI also converge. -/
theorem proposition_7_2_2 [Nonempty X] [TopologicalSpace X] [TopologicalSpace A]
    (hΓ : HasMaxSelections M.Γ) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hB : M.IsBlackwell lam)
    (hc : ∀ v : BM X, Continuous v.toFun →
      ContinuousOn (fun p : X × A => M.B p.1 p.2 v.toFun) {p | p.2 ∈ M.Γ p.1}) :
    ∃ hw : M.toRDP.adp.WellPosed, M.toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ LDP.bc X, M.toRDP.adp.VFIGeometric (LDP.bc X) vstar ∧
        ((∀ v : BM X, ContinuousOn (fun p : X × A => M.B p.1 p.2 v.toFun) {p | p.2 ∈ M.Γ p.1}) →
          ∀ g, M.toRDP.adp.IsSelector g →
            M.toRDP.adp.OPIConverges g vstar ∧ M.toRDP.adp.HPIConverges hw g vstar) := by
  have hsr : M.toRDP.adp.IsSemiRegular (LDP.bc X) :=
    ⟨LDP.isClosed_bc, fun v hv => (M.greedy_of_continuous hΓ (hc v hv)).1,
      fun v hv => (M.greedy_of_continuous hΓ (hc v hv)).2⟩
  obtain ⟨hw, hFO, vstar, hv, hgeo, hconv⟩ := BanachLattice.theorem_4_1_3_univ
    BM.isNormalizedOrderUnit_one M.toRDP.adp hlam0 hlam1 (M.T_blackwell hB) hsr
    ⟨0, LDP.zero_mem_bc⟩
  exact ⟨hw, hFO, vstar, hv, hgeo, fun hall =>
    hconv fun v => (M.greedy_of_continuous hΓ (hall v)).1⟩

end BRDP

end SargentStachurski.AdditionalApplications
