/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AbstractDecisionProcesses.Algorithms
import AbstractDecisionProcesses.FirmProblem
import AbstractDecisionProcesses.BXOrder

/-!
# Firm valuation as an ADP

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §2.3.1 (pp. 79–80).

The firm problem of §1.1 is the ADP `(bX, 𝕋_FV)` with the policy operators (2.12) and the
pointwise order.

* **Exercise 2.3.1**: each `T_σ` is an order preserving self-map of `(bX, ≤)`; the ADP is
  well-posed and order stable.
* The ADP's greedy policies are those of (2.13), a greedy policy always exists (regularity), and
  the ADP Bellman operator is `Tv = s ∨ (π + βPv)` (1.9).
* **Exercise 2.3.2** (order continuity) and **Exercise 2.3.3** (order boundedness).
* As the book remarks (p. 80), Theorem 2.2.8 now gives the fundamental optimality properties
  and the convergence of VFI, OPI and HPI for the firm problem.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.AbstractDecisionProcesses

variable {X : Type*} [MeasurableSpace X]

namespace FirmProblem

variable (F : FirmProblem X)

/-- The firm ADP `(bX, 𝕋_FV)` (§2.3.1), with policy operators (2.12). -/
noncomputable def adp : ADP ↥(bX X) (FirmPolicy X) where
  T σ v := ⟨F.Tσ σ.1 v.1, F.Tσ_mapsTo σ.2 v.2⟩
  mono σ v w h := F.Tσ_mono σ.1 v.2 w.2 h
  nonempty := ⟨⟨fun _ => true, measurable_const⟩⟩

/-- **Exercise 2.3.1** (p. 79): each `T_σ` is an order preserving self-map of `(bX, ≤)`. -/
theorem exercise_2_3_1 (σ : FirmPolicy X) : Monotone (F.adp.T σ) := F.adp.mono σ

/-- The firm ADP is well-posed (§1.1.1.2). -/
theorem adp_wellPosed : F.adp.WellPosed := fun σ => by
  obtain ⟨u, huV, hu, huniq, -⟩ := F.toDP.globallyStable σ
  exact ⟨⟨u, huV⟩, Subtype.ext hu, fun w hw =>
    Subtype.ext (huniq w.1 w.2 (congrArg Subtype.val hw))⟩

/-- The firm ADP is order stable (Lemma A.5.19). -/
theorem adp_isOrderStable : F.adp.IsOrderStable := fun σ =>
  orderStable_of_up_down (u := ⟨F.toDP.vσ σ, F.toDP.vσ_mem σ⟩) (Subtype.ext (F.toDP.T_vσ σ))
    (fun v hv => F.toDP.le_vσ v.2 hv) fun v hv => F.toDP.vσ_le v.2 hv

/-- §2.3.1 (p. 80): the ADP's `v`-greedy policies are exactly those of (2.13). -/
theorem adp_isGreedy_iff (v : ↥(bX X)) (σ : FirmPolicy X) :
    F.adp.IsGreedy v σ ↔ F.IsGreedy v.1 σ.1 :=
  (F.isGreedy_iff v.1 σ).symm

/-- §2.3.1 (p. 80): the firm ADP is regular. -/
theorem adp_regular : F.adp.Regular := fun v => by
  obtain ⟨σ, hσ⟩ := F.toDP.exists_greedy v.1 v.2
  exact ⟨σ, hσ⟩

/-- §2.3.1 (p. 80): the ADP Bellman operator is `Tv = s ∨ (π + βPv)`, as in (1.9). -/
theorem adp_bellman_apply (v : ↥(bX X)) (x : X) :
    (F.adp.bellman v : X → ℝ) x = max F.s (F.profit x + F.β * markovOp F.P v x) := by
  refine le_antisymm (F.Tσ_le_max _ _ x) ?_
  rw [← F.Tσ_sellPolicy]
  exact F.adp.T_le_bellman ⟨_, F.measurable_sellPolicy v.2⟩ (F.adp_regular v) x

/-- **Exercise 2.3.2** (p. 80): the firm ADP is order continuous. -/
theorem adp_isOrderContinuous : F.adp.IsOrderContinuous := by
  have := F.isMarkov
  intro σ g w hg hw
  have hlim := tendsto_of_isLUB_bX hg hw
  refine isLUB_of_tendsto_bX (fun a b h => F.adp.mono σ (hg h)) fun x => ?_
  change Tendsto (fun n => F.Tσ σ.1 (g n) x) atTop (𝓝 (F.Tσ σ.1 w x))
  simp only [Tσ]
  split_ifs
  · exact tendsto_const_nhds
  · exact tendsto_const_nhds.add ((tendsto_markovOp F.P (fun n => (g n).2) w.2
      (fun y a b h => hg h y) hlim x).const_mul F.β)

/-- **Exercise 2.3.3** (p. 80): the firm ADP is order bounded: with `|π| ≤ M`, the constant
`(|s| + M)/(1 − β)` is mapped down by every `T_σ`. -/
theorem adp_orderBounded : F.adp.OrderBounded := by
  have := F.isMarkov
  obtain ⟨M, hM0, hM⟩ := F.profit_mem.2.nonneg_bound
  have h1β : 0 < 1 - F.β := sub_pos.2 F.β_lt_one
  set K := (|F.s| + M) / (1 - F.β)
  have hK : (1 - F.β) * K = |F.s| + M := mul_div_cancel₀ _ h1β.ne'
  have hsK : F.s ≤ K :=
    (le_abs_self _).trans ((le_add_of_nonneg_right hM0).trans
      (le_div_self (add_nonneg (abs_nonneg _) hM0) h1β (by linarith [F.β_nonneg])))
  refine ⟨⟨fun _ => K, const_mem_bX K⟩, fun σ x => ?_⟩
  change F.Tσ σ.1 (fun _ => K) x ≤ K
  simp only [Tσ, markovOp_const]
  split_ifs
  · exact hsK
  · nlinarith [(abs_le.1 (hM x)).2, abs_nonneg F.s]

/-- §2.3.1 (p. 80), via **Theorem 2.2.8**: the firm ADP satisfies the fundamental optimality
properties, and VFI, OPI and HPI all converge, for every greedy selector. -/
theorem adp_optimality :
    F.adp.FundamentalOptimality F.adp_isOrderStable.wellPosed ∧
      ∃ vstar, F.adp.IsValueFunction vstar ∧ F.adp.VFIConverges vstar ∧
        ∀ g, F.adp.IsSelector g → F.adp.OPIConverges g vstar ∧
          F.adp.HPIConverges F.adp_isOrderStable.wellPosed g vstar :=
  ADP.convergence_of_dedekind F.adp_isOrderStable F.adp_regular countablyDedekindComplete_bX
    F.adp_orderBounded F.adp_isOrderContinuous

end FirmProblem

end SargentStachurski.AbstractDecisionProcesses
