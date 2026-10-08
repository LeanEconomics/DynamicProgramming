/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ADPsOnBanachSpace.BMOperators
import ADPsOnBanachSpace.FirmProblem

/-!
# Firm valuation on `bX`

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §4.2.1.1 and §4.2.1.3 (pp. 133–136).

* §4.2.1.1: the firm ADP `(bX, 𝕋_FV)` with policy operators (4.10), the greedy policy (4.11),
  the Bellman equation (4.13), and **Proposition 4.2.1** by Theorem 4.1.3 with `e = 𝟙`, `λ = β`.
* §4.2.1.3: state-dependent discounting, `T_σ v = σs + (1 − σ)(π + Kv)` (4.14) with
  `(Kv)(x) = β(x) ∫ v(x')P(x, dx')`; the Bellman equation (4.15), and **Proposition 4.2.2**
  (**Exercise 4.2.1**) under Assumption 4.2.1 `ρ(K) < 1`, by Theorem 4.1.8.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.ADPsOnBanachSpace

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

variable {X : Type*} [MeasurableSpace X]

/-- `id` is an isometric order embedding of `bX` into itself. -/
theorem isIsoOrderEmbedding_id : BanachLattice.IsIsoOrderEmbedding (id : BM X → BM X) :=
  ⟨fun v w => dist_eq_norm v w, fun _ _ => Iff.rfl⟩

namespace FirmProblem

variable (F : FirmProblem X)

/-- The policy operator (4.10) on `bX`. -/
noncomputable def TBM (σ : FirmPolicy X) (v : BM X) : BM X :=
  ⟨F.Tσ σ.1 v.toFun, (F.Tσ_mapsTo σ.2 (BM.mem_bX v)).1, (F.Tσ_mapsTo σ.2 (BM.mem_bX v)).2⟩

/-- The firm valuation ADP `(bX, 𝕋_FV)` (§4.2.1.1). -/
noncomputable def adpBM : ADP (BM X) (FirmPolicy X) where
  T := F.TBM
  mono σ _ _ h := F.Tσ_mono σ.1 (BM.mem_bX _) (BM.mem_bX _) h
  nonempty := ⟨⟨fun _ => true, measurable_const⟩⟩

/-- The `v`-greedy policy (4.11): sell when `s ≥ π + βPv`. -/
noncomputable def sellBM (v : BM X) : FirmPolicy X :=
  ⟨fun x => decide (F.profit x + F.β * markovOp F.P v.toFun x ≤ F.s),
    F.measurable_sellPolicy (BM.mem_bX v)⟩

theorem sellBM_isGreedy (v : BM X) : F.adpBM.IsGreedy v (F.sellBM v) := fun τ x =>
  (F.Tσ_le_max τ.1 v.toFun x).trans_eq (F.Tσ_sellPolicy v.toFun x).symm

theorem adpBM_regular : F.adpBM.Regular := fun v => ⟨_, F.sellBM_isGreedy v⟩

/-- (4.13): the Bellman operator is `Tv = s ∨ (π + βPv)`. -/
theorem adpBM_bellman_apply (v : BM X) (x : X) :
    (F.adpBM.bellman v).toFun x = max F.s (F.profit x + F.β * markovOp F.P v.toFun x) := by
  have h := F.adpBM.isGreedy_greedy (F.adpBM_regular v)
  rw [← F.Tσ_sellPolicy v.toFun x]
  exact le_antisymm (F.sellBM_isGreedy v _ x) (h (F.sellBM v) x)

/-- Blackwell's condition (4.4) with `e = 𝟙` and `λ = β`. -/
theorem blackwell (σ : FirmPolicy X) (v : BM X) (κ : ℝ) (hκ : 0 ≤ κ) :
    F.adpBM.T σ (v + κ • BM.const 1) ≤ F.adpBM.T σ v + (F.β * κ) • BM.const 1 := fun x => by
  have := F.isMarkov
  change F.Tσ σ.1 (v + κ • BM.const 1).toFun x ≤ F.Tσ σ.1 v.toFun x + F.β * κ * 1
  have hP : markovOp F.P (v + κ • BM.const 1).toFun x = markovOp F.P v.toFun x + κ := by
    have h1 := markovOp_add F.P (BM.mem_bX v) (const_mem_bX κ)
    have h2 : (v + κ • BM.const 1).toFun = v.toFun + fun _ => κ := by
      funext y
      simp only [BM.add_apply, BM.smul_apply, BM.const_apply, Pi.add_apply, mul_one]
    rw [h2, h1, markovOp_const]
    rfl
  simp only [Tσ, hP]
  split_ifs
  · nlinarith [F.β_nonneg]
  · nlinarith [F.β_nonneg]

/-- **Proposition 4.2.1** (p. 133): for the firm valuation ADP `(bX, 𝕋_FV)` the fundamental
optimality properties hold, VFI converges (geometrically), and OPI and HPI converge. -/
theorem proposition_4_2_1 [Nonempty X] :
    ∃ hw : F.adpBM.WellPosed, F.adpBM.FundamentalOptimality hw ∧ ∃ vstar,
      F.adpBM.VFIGeometric univ vstar ∧ F.adpBM.VFIConverges vstar ∧
        ∀ g, F.adpBM.IsSelector g → F.adpBM.OPIConverges g vstar ∧
          F.adpBM.HPIConverges hw g vstar := by
  have hsr : F.adpBM.IsSemiRegular univ :=
    ⟨isClosed_univ, fun v _ => F.adpBM_regular v, mapsTo_univ _ _⟩
  obtain ⟨hw, hFO, vstar, -, hgeo, hconv⟩ := BanachLattice.theorem_4_1_3_univ
    BM.isNormalizedOrderUnit_one F.adpBM F.β_nonneg F.β_lt_one F.blackwell hsr univ_nonempty
  have hT : ∀ σ v w, dist (F.adpBM.T σ v) (F.adpBM.T σ w) ≤ F.β * dist v w := fun σ v w => by
    rw [dist_eq_norm, dist_eq_norm]
    exact BanachLattice.lemma_4_1_2 BM.isNormalizedOrderUnit_one (F.adpBM.mono σ) F.β_nonneg
      (F.blackwell σ) v w
  have hgs := ADP.isGloballyStable_of_contraction ⟨0⟩ F.β_nonneg F.β_lt_one hT
  obtain ⟨w, -, -, -, hwG, hwb⟩ := hFO.exists_vstar
  obtain ⟨-, w', hw', hvfi, -⟩ := ADP.theorem_3_1_2 F.adpBM_regular hgs
    ((F.adpBM.solvesBellman_iff hwG).1 hwb)
  obtain rfl : vstar = w' := hgeo.1.unique hw'
  exact ⟨hw, hFO, vstar, hgeo, hvfi, hconv F.adpBM_regular⟩

end FirmProblem

/-! ### State-dependent discounting -/

/-- The firm problem with state-dependent discounting (§4.2.1.3): a bounded nonnegative discount
function `β(x) = 1/(1 + r(x))`. -/
structure FirmSD (X : Type*) [MeasurableSpace X] where
  /-- the stochastic kernel of the state -/
  P : Kernel X X
  isMarkov : IsMarkovKernel P
  /-- the profit function -/
  profit : BM X
  /-- the state-dependent discount factor -/
  βf : BM X
  βf_nonneg : 0 ≤ βf
  /-- the sale price -/
  s : ℝ

namespace FirmSD

variable (F : FirmSD X)

/-- The discount operator `(Kv)(x) = β(x) ∫ v(x')P(x, dx')`. -/
noncomputable def K : BM X →L[ℝ] BM X :=
  have := F.isMarkov
  BM.mulCLM F.βf ∘L BM.markovCLM F.P

theorem K_apply (v : BM X) (x : X) :
    (F.K v).toFun x = F.βf.toFun x * markovOp F.P v.toFun x := rfl

theorem K_isPositive : BanachLattice.IsPositiveOp F.K := by
  have := F.isMarkov
  exact fun v hv => BM.mulCLM_isPositive F.βf_nonneg _ (BM.markovCLM_isPositive F.P v hv)

/-- The indicator of continuing, `1 − σ`. -/
def cont (σ : FirmPolicy X) : BM X :=
  ⟨fun x => if σ.1 x then 0 else 1, Measurable.ite (σ.2 (measurableSet_singleton true))
    measurable_const measurable_const, ⟨1, fun x => by split_ifs <;> simp⟩⟩

/-- `r_σ = σs + (1 − σ)π`. -/
def rσ (σ : FirmPolicy X) : BM X :=
  ⟨fun x => if σ.1 x then F.s else F.profit.toFun x, Measurable.ite
    (σ.2 (measurableSet_singleton true)) measurable_const F.profit.measurable', by
      obtain ⟨C, hC⟩ := F.profit.bdd'
      exact ⟨max |F.s| C, fun x => by
        split_ifs
        · exact le_max_left _ _
        · exact (hC x).trans (le_max_right _ _)⟩⟩

/-- `K_σ = (1 − σ)K`. -/
noncomputable def Kσ (σ : FirmPolicy X) : BM X →L[ℝ] BM X := BM.mulCLM (cont σ) ∘L F.K

/-- The policy operator (4.14): `T_σ v = σs + (1 − σ)(π + Kv)`. -/
noncomputable def T (σ : FirmPolicy X) (v : BM X) : BM X := F.rσ σ + F.Kσ σ v

theorem T_apply (σ : FirmPolicy X) (v : BM X) (x : X) :
    (F.T σ v).toFun x = if σ.1 x then F.s else F.profit.toFun x + (F.K v).toFun x := by
  simp only [T, Kσ, BM.add_apply, ContinuousLinearMap.comp_apply, BM.mulCLM_apply, rσ, cont]
  split_ifs <;> simp

/-- The firm ADP with state-dependent discounting, `(bX, 𝕋_FV)`. -/
noncomputable def adp : ADP (BM X) (FirmPolicy X) where
  T := F.T
  mono σ v w h x := by
    rw [F.T_apply, F.T_apply]
    split_ifs
    · exact le_rfl
    · exact add_le_add le_rfl (F.K_isPositive.mono h x)
  nonempty := ⟨⟨fun _ => true, measurable_const⟩⟩

/-- The `v`-greedy policy: sell when `s ≥ π + Kv`. -/
noncomputable def sell (v : BM X) : FirmPolicy X :=
  ⟨fun x => decide (F.profit.toFun x + (F.K v).toFun x ≤ F.s), measurable_to_bool (by
    have : (fun x => decide (F.profit.toFun x + (F.K v).toFun x ≤ F.s)) ⁻¹' {true} =
        {x | F.profit.toFun x + (F.K v).toFun x ≤ F.s} := by
      ext x
      simp
    rw [this]
    exact measurableSet_le (F.profit + F.K v).measurable' measurable_const)⟩

theorem T_sell_apply (v : BM X) (x : X) :
    (F.T (F.sell v) v).toFun x = max F.s (F.profit.toFun x + (F.K v).toFun x) := by
  rw [F.T_apply]
  by_cases h : F.profit.toFun x + (F.K v).toFun x ≤ F.s
  · simp [sell, h]
  · simp only [sell, h, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact (max_eq_right (le_of_not_ge h)).symm

theorem sell_isGreedy (v : BM X) : F.adp.IsGreedy v (F.sell v) := fun τ x => by
  change (F.T τ v).toFun x ≤ (F.T (F.sell v) v).toFun x
  rw [F.T_sell_apply, F.T_apply]
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem adp_regular : F.adp.Regular := fun v => ⟨_, F.sell_isGreedy v⟩

/-- (4.15): the Bellman operator is `Tv = s ∨ (π + Kv)`. -/
theorem adp_bellman_apply (v : BM X) (x : X) :
    (F.adp.bellman v).toFun x = max F.s (F.profit.toFun x + (F.K v).toFun x) := by
  have h := F.adp.isGreedy_greedy (F.adp_regular v)
  rw [← F.T_sell_apply v x]
  exact le_antisymm (F.sell_isGreedy v _ x) (h (F.sell v) x)

/-- The ADP is additive: `T_σ v = r_σ + K_σ v` with `K_σ = (1 − σ)K` positive. -/
theorem isAdditive : BanachLattice.IsAdditive id F.adp F.rσ F.Kσ :=
  ⟨fun σ v hv => BM.mulCLM_isPositive (fun x => by simp only [cont]; split_ifs <;> norm_num) _
    (F.K_isPositive v hv), fun _ _ => rfl⟩

/-- `K_σ ≤ K` on the positive cone. -/
theorem Kσ_le_K (σ : FirmPolicy X) (h : BM X) (hh : 0 ≤ h) : F.Kσ σ h ≤ F.K h := fun x => by
  change (cont σ).toFun x * (F.K h).toFun x ≤ (F.K h).toFun x
  have := F.K_isPositive h hh x
  simp only [cont]
  split_ifs
  · simpa using this
  · simp

/-- **Proposition 4.2.2** (p. 136), **Exercise 4.2.1**: under Assumption 4.2.1, `ρ(K) < 1`, the
fundamental optimality properties hold for the firm ADP with state-dependent discounting, VFI
converges (geometrically), and OPI and HPI converge. -/
theorem proposition_4_2_2 (hρ : BanachLattice.specRad F.K < 1) :
    ∃ hw : F.adp.WellPosed, F.adp.FundamentalOptimality hw ∧ ∃ vstar,
      F.adp.VFIGeometric univ vstar ∧ F.adp.VFIConverges vstar ∧
        ∀ g, F.adp.IsSelector g → F.adp.OPIConverges g vstar ∧ F.adp.HPIConverges hw g vstar := by
  have hD := BanachLattice.example_4_1_1 F.K_isPositive hρ
  have hsr : F.adp.IsSemiRegular univ :=
    ⟨isClosed_univ, fun v _ => F.adp_regular v, mapsTo_univ _ _⟩
  obtain ⟨hw, hFO, vstar, -, hgeo, hconv⟩ := BanachLattice.theorem_4_1_8 isIsoOrderEmbedding_id
    F.adp F.isAdditive hD F.Kσ_le_K hsr univ_nonempty
  have hgs : F.adp.IsGloballyStable := fun σ =>
    (BanachLattice.theorem_4_1_4 isIsoOrderEmbedding_id ⟨hD, fun v w =>
      (F.isAdditive.abs_sub σ v w).trans (F.Kσ_le_K σ _ (abs_nonneg _))⟩).1
  obtain ⟨w, -, -, -, hwG, hwb⟩ := hFO.exists_vstar
  obtain ⟨-, w', hw', hvfi, -⟩ := ADP.theorem_3_1_2 F.adp_regular hgs
    ((F.adp.solvesBellman_iff hwG).1 hwb)
  obtain rfl : vstar = w' := hgeo.1.unique hw'
  exact ⟨hw, hFO, vstar, hgeo, hvfi, hconv F.adp_regular⟩

end FirmSD

end SargentStachurski.ADPsOnBanachSpace
