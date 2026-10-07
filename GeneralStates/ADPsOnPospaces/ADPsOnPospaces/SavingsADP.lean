/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ADPsOnPospaces.Algorithms
import ADPsOnPospaces.OptimalSavings
import ADPsOnPospaces.BXOrder

/-!
# Optimal savings as an ADP

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §2.3.2 (pp. 80–82).

The optimal savings problem of §1.3 is the ADP `(bℝ₊, 𝕋_OS)` with the policy operators (1.42)
and the pointwise order.

* The policy operators are order preserving self-maps of `bℝ₊` (Exercise 1.3.1); the ADP is
  well-posed and order stable (Lemma 1.3.1, Lemma A.5.19).
* The ADP's greedy policies are those of (1.49) ((2.14)–(2.15)); the ADP is regular exactly when
  greedy policies exist (Lemma 1.3.2 (i)), and then its Bellman operator is (1.51).
* **Exercise 2.3.4** (`u ≥ 0` gives `u ∈ V_U`) and **Exercise 2.3.5** (order boundedness and
  order continuity).
* Given Lemma 1.3.2 (i), Theorem 2.2.8 gives the fundamental optimality properties and the
  convergence of VFI, OPI and HPI.
-/

open Set Function Filter Topology MeasureTheory

open scoped NNReal

namespace SargentStachurski.ADPsOnPospaces

/-- The policy that consumes all wealth, `σ(w) = w`. -/
def consumeAll : SavingsPolicy := ⟨id, measurable_id, fun _ => le_rfl⟩

namespace OptimalSavings

variable (S : OptimalSavings)

/-- The optimal savings ADP `(bℝ₊, 𝕋_OS)` (§2.3.2). -/
noncomputable def adp : ADP ↥(bX ℝ≥0) SavingsPolicy where
  T σ v := ⟨S.Tσ σ.1 v.1, S.Tσ_mapsTo σ.2.1 v.2⟩
  mono σ v w h := affineOp_mono (S.isMarkovLike_Pσ σ.2.1) S.β_nonneg v.2 w.2 h
  nonempty := ⟨consumeAll⟩

/-- §2.3.2 (p. 81): the optimal savings ADP is well-posed (Lemma 1.3.1). -/
theorem adp_wellPosed : S.adp.WellPosed := fun σ => by
  obtain ⟨u, huV, hu, huniq, -⟩ := S.Tσ_globallyStable σ.2.1
  exact ⟨⟨u, huV⟩, Subtype.ext hu, fun w hw =>
    Subtype.ext (huniq w.1 w.2 (congrArg Subtype.val hw))⟩

/-- §2.3.2 (p. 81): the optimal savings ADP is order stable (Lemma A.5.19). -/
theorem adp_isOrderStable : S.adp.IsOrderStable := fun σ => by
  obtain ⟨u, huV, hu, -, hlim⟩ := S.Tσ_globallyStable σ.2.1
  have hmono : ∀ v ∈ bX ℝ≥0, ∀ w ∈ bX ℝ≥0, v ≤ w → S.Tσ σ.1 v ≤ S.Tσ σ.1 w :=
    fun _ hv _ hw h => affineOp_mono (S.isMarkovLike_Pσ σ.2.1) S.β_nonneg hv hw h
  exact orderStable_of_up_down (u := ⟨u, huV⟩) (Subtype.ext hu)
    (fun v hv => le_of_le_map_of_tendsto (S.Tσ_mapsTo σ.2.1) hmono v.2 (hlim v v.2) hv)
    fun v hv => le_of_map_le_of_tendsto (S.Tσ_mapsTo σ.2.1) hmono v.2 (hlim v v.2) hv

/-- (2.14)–(2.15) (p. 81): `σ` is greedy for the ADP iff it is `v`-greedy in the sense of (1.49).
(A policy can be changed at a single wealth level, so no appeal to Lemma 1.3.2 is needed.) -/
theorem adp_isGreedy_iff (v : ↥(bX ℝ≥0)) (σ : SavingsPolicy) :
    S.adp.IsGreedy v σ ↔ S.IsGreedy v.1 σ := by
  constructor
  · intro h w c hc
    classical
    let τ : SavingsPolicy := ⟨fun x => if x = w then c else σ.1 x,
      Measurable.ite (measurableSet_singleton w) measurable_const σ.2.1, fun x => by
        by_cases hx : x = w
        · simp only [hx, ↓reduceIte]; exact hc
        · simp only [hx, ↓reduceIte]; exact σ.2.2 x⟩
    have := h τ w
    change S.Tσ (fun x => if x = w then c else σ.1 x) v w ≤ S.Tσ σ.1 v w at this
    simpa [Tσ, affineOp, rσ, Pσ, objective] using this
  · exact fun h τ w => h w _ (τ.2.2 w)

/-- §2.3.2 (p. 81): the ADP is regular iff `v`-greedy policies exist for every `v ∈ bℝ₊`, which
is Lemma 1.3.2 (i). -/
theorem adp_regular_iff : S.adp.Regular ↔ ∀ v ∈ bX ℝ≥0, ∃ σ, S.IsGreedy v σ := by
  constructor
  · intro h v hv
    obtain ⟨σ, hσ⟩ := h ⟨v, hv⟩
    exact ⟨σ, (S.adp_isGreedy_iff ⟨v, hv⟩ σ).1 hσ⟩
  · intro h v
    obtain ⟨σ, hσ⟩ := h v.1 v.2
    exact ⟨σ, (S.adp_isGreedy_iff v σ).2 hσ⟩

/-- §2.3.2 (p. 81): for a regular ADP, the Bellman operator is (1.51). -/
theorem adp_bellman_apply (hr : S.adp.Regular) (v : ↥(bX ℝ≥0)) (w : ℝ≥0) :
    (S.adp.bellman v : ℝ≥0 → ℝ) w = S.bellmanOp v w := by
  have hg := (S.adp_isGreedy_iff v _).1 (S.adp.isGreedy_greedy (hr v))
  have : Nonempty {c : ℝ≥0 // c ≤ w} := ⟨⟨0, bot_le⟩⟩
  refine le_antisymm ?_ (ciSup_le fun c => hg w c c.2)
  exact le_ciSup (S.bddAbove_objective v.2.2 w) ⟨(S.adp.greedy v).1 w, (S.adp.greedy v).2.2 w⟩

/-- **Exercise 2.3.4** (p. 82): if `u ≥ 0` then `u ≤ Tu`, i.e. `u ∈ V_U` (the ADP being regular). -/
theorem exercise_2_3_4 (hr : S.adp.Regular) (hu : ∀ c, 0 ≤ S.u c) :
    (⟨S.u, S.u_cont.measurable, S.u_bdd⟩ : ↥(bX ℝ≥0)) ∈ S.adp.VU := by
  have := S.φ_prob
  refine ⟨hr _, ?_⟩
  refine le_trans (fun w => ?_) (S.adp.T_le_bellman consumeAll (hr _))
  change S.u w ≤ S.Tσ id S.u w
  simp only [Tσ, affineOp, rσ, id]
  exact le_add_of_nonneg_right (mul_nonneg S.β_nonneg (integral_nonneg fun y => hu _))

/-- **Exercise 2.3.5** (p. 82), order boundedness: with `|u| ≤ M`, the constant `M/(1 − β)` is
mapped down by every `T_σ`. -/
theorem adp_orderBounded : S.adp.OrderBounded := by
  have := S.φ_prob
  obtain ⟨M, hM0, hM⟩ := S.u_bdd.nonneg_bound
  have h1β : 0 < 1 - S.β := sub_pos.2 S.β_lt_one
  set K := M / (1 - S.β)
  have hK : M + S.β * K = K := by
    have : K * (1 - S.β) = M := div_mul_cancel₀ M h1β.ne'
    linarith
  refine ⟨⟨fun _ => K, const_mem_bX K⟩, fun σ w => ?_⟩
  change S.Tσ σ.1 (fun _ => K) w ≤ K
  simp only [Tσ, affineOp, rσ, Pσ, cont, integral_const, probReal_univ, one_smul]
  linarith [(abs_le.1 (hM (σ.1 w))).2]

/-- **Exercise 2.3.5** (p. 82), order continuity, by the monotone convergence theorem. -/
theorem adp_isOrderContinuous : S.adp.IsOrderContinuous := by
  have := S.φ_prob
  intro σ g v hg hv
  have hlim := tendsto_of_isLUB_bX hg hv
  refine isLUB_of_tendsto_bX (fun a b h => S.adp.mono σ (hg h)) fun w => ?_
  change Tendsto (fun n => S.Tσ σ.1 (g n) w) atTop (𝓝 (S.Tσ σ.1 v w))
  simp only [Tσ, affineOp]
  refine tendsto_const_nhds.add (Tendsto.const_mul S.β ?_)
  exact integral_tendsto_of_tendsto_of_monotone (fun n => S.integrable_comp (g n).2 _)
    (S.integrable_comp v.2 _) (Filter.Eventually.of_forall fun y a b h => hg h _)
    (Filter.Eventually.of_forall fun y => hlim _)

/-- §2.3.2 with **Theorem 2.2.8**: given Lemma 1.3.2 (i), the optimal savings ADP satisfies the
fundamental optimality properties, and VFI, OPI and HPI all converge. -/
theorem adp_optimality (hgreedy : ∀ v ∈ bX ℝ≥0, ∃ σ, S.IsGreedy v σ) :
    S.adp.FundamentalOptimality S.adp_isOrderStable.wellPosed ∧
      ∃ vstar, S.adp.IsValueFunction vstar ∧ S.adp.VFIConverges vstar ∧
        ∀ g, S.adp.IsSelector g → S.adp.OPIConverges g vstar ∧
          S.adp.HPIConverges S.adp_isOrderStable.wellPosed g vstar :=
  ADP.convergence_of_dedekind S.adp_isOrderStable ((S.adp_regular_iff).2 hgreedy)
    countablyDedekindComplete_bX S.adp_orderBounded S.adp_isOrderContinuous

end OptimalSavings

end SargentStachurski.ADPsOnPospaces
