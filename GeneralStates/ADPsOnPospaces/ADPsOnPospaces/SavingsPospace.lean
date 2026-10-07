/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ADPsOnPospaces.SavingsADP
import ADPsOnPospaces.BoundedMeasurable
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Optimal savings on the Banach lattice `bℝ₊`

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §3.2.2 (pp. 108–109).

The optimal savings ADP `(bℝ₊, 𝕋_OS)` with policy operators (3.8), now on the Banach lattice
`bℝ₊` with the supremum norm.

* Each `T_σ` is globally stable (Lemma 1.3.1), and greedy policies are those of (3.10).
* **Proposition 3.2.1** (the strongly continuous case): given Lemma 1.3.2 (i) (greedy policies
  exist, which needs the continuous density of Assumption 1.3.1 and is proved in Chapter 6),
  Theorem 3.1.4 gives the fundamental optimality properties and convergence of VFI, OPI and HPI.
  **Remark 3.2.1**: Theorem 3.1.5 gives the same.
* **Exercise 3.2.7** (the weakly continuous case, `φ` any probability measure): for `v ∈ bcℝ₊` a
  `v`-greedy policy exists (the largest maximizer, shown measurable by a sequential compactness
  argument) and the Bellman operator maps `bcℝ₊` into itself.
* **Proposition 3.2.2**: by Theorem 3.1.5 with `V₀ = bcℝ₊`, the fundamental optimality properties
  hold, the value function is continuous, and VFI converges geometrically on `bcℝ₊`.
-/

open Set Function Filter Topology MeasureTheory

open scoped NNReal

namespace SargentStachurski.ADPsOnPospaces

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace

namespace OptimalSavings

variable (S : OptimalSavings)

/-- The policy operator (3.8) on `bℝ₊`. -/
noncomputable def TBM (σ : SavingsPolicy) (v : BM ℝ≥0) : BM ℝ≥0 :=
  ⟨S.Tσ σ.1 v.toFun, (S.Tσ_mapsTo σ.2.1 (BM.mem_bX v)).1, (S.Tσ_mapsTo σ.2.1 (BM.mem_bX v)).2⟩

/-- The optimal savings ADP `(bℝ₊, 𝕋_OS)` on the Banach lattice `bℝ₊`. -/
noncomputable def adpBM : ADP (BM ℝ≥0) SavingsPolicy where
  T := S.TBM
  mono σ v w h := affineOp_mono (S.isMarkovLike_Pσ σ.2.1) S.β_nonneg (BM.mem_bX v)
    (BM.mem_bX w) h
  nonempty := ⟨consumeAll⟩

/-- Lemma 1.3.1: the ADP is globally stable on `bℝ₊`. -/
theorem adpBM_isGloballyStable : S.adpBM.IsGloballyStable := fun σ =>
  BM.globallyStable_of_bX (fun _ => rfl) (S.Tσ_globallyStable σ.2.1)

/-- (3.10): `σ` is greedy for the ADP iff `σ(w)` maximizes (3.10) at every `w`. -/
theorem adpBM_isGreedy_iff (v : BM ℝ≥0) (σ : SavingsPolicy) :
    S.adpBM.IsGreedy v σ ↔ S.IsGreedy v.toFun σ := by
  constructor
  · intro h w c hc
    classical
    let τ : SavingsPolicy := ⟨fun x => if x = w then c else σ.1 x,
      Measurable.ite (measurableSet_singleton w) measurable_const σ.2.1, fun x => by
        by_cases hx : x = w
        · simp only [hx, ↓reduceIte]
          exact hc
        · simp only [hx, ↓reduceIte]
          exact σ.2.2 x⟩
    have := h τ w
    change S.Tσ (fun x => if x = w then c else σ.1 x) v.toFun w ≤ S.Tσ σ.1 v.toFun w at this
    simpa [Tσ, affineOp, rσ, Pσ, objective] using this
  · exact fun h τ w => h w _ (τ.2.2 w)

/-- On `V_G`, the ADP Bellman operator is (1.51). -/
theorem adpBM_bellman_apply {v : BM ℝ≥0} (hv : v ∈ S.adpBM.VG) (w : ℝ≥0) :
    (S.adpBM.bellman v).toFun w = S.bellmanOp v.toFun w := by
  have hg := (S.adpBM_isGreedy_iff v _).1 (S.adpBM.isGreedy_greedy hv)
  have : Nonempty {c : ℝ≥0 // c ≤ w} := ⟨⟨0, bot_le⟩⟩
  refine le_antisymm ?_ (ciSup_le fun c => hg w c c.2)
  exact le_ciSup (S.bddAbove_objective v.bdd' w) ⟨(S.adpBM.greedy v).1 w, (S.adpBM.greedy v).2.2 w⟩

/-- The ADP is order bounded: with `|u| ≤ M`, the constant `M/(1 − β)` is mapped down by every
`T_σ`. -/
theorem adpBM_orderBounded : S.adpBM.OrderBounded := by
  have := S.φ_prob
  obtain ⟨M, hM0, hM⟩ := S.u_bdd.nonneg_bound
  have h1β : 0 < 1 - S.β := sub_pos.2 S.β_lt_one
  set K := M / (1 - S.β)
  have hK : M + S.β * K = K := by
    have : K * (1 - S.β) = M := div_mul_cancel₀ M h1β.ne'
    linarith
  refine ⟨BM.const K, fun σ w => ?_⟩
  change S.Tσ σ.1 (fun _ => K) w ≤ K
  simp only [Tσ, affineOp, rσ, Pσ, cont, integral_const, probReal_univ, one_smul]
  linarith [(abs_le.1 (hM (σ.1 w))).2]

/-- Each `T_σ` is a contraction of modulus `β` for the supremum norm. -/
theorem adpBM_contraction (σ : SavingsPolicy) (v w : BM ℝ≥0) :
    dist (S.adpBM.T σ v) (S.adpBM.T σ w) ≤ S.β * dist v w := by
  have := S.φ_prob
  refine BM.dist_le (mul_nonneg S.β_nonneg dist_nonneg) fun x => ?_
  change |S.u (σ.1 x) + S.β * S.cont v.toFun x (σ.1 x) -
    (S.u (σ.1 x) + S.β * S.cont w.toFun x (σ.1 x))| ≤ _
  have hsub : S.cont v.toFun x (σ.1 x) - S.cont w.toFun x (σ.1 x) =
      S.cont (v - w).toFun x (σ.1 x) := by
    simp only [cont, BM.sub_apply]
    exact (integral_sub (S.integrable_comp (BM.mem_bX v) _)
      (S.integrable_comp (BM.mem_bX w) _)).symm
  rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg S.β_nonneg, hsub]
  refine mul_le_mul_of_nonneg_left (S.abs_cont_le (fun y => ?_) _ _) S.β_nonneg
  rw [BM.sub_apply]
  exact BM.abs_sub_le_dist v w y

/-- **Proposition 3.2.1** (p. 108): given Lemma 1.3.2 (i) (greedy policies exist), the optimal
savings ADP obeys the fundamental optimality properties and VFI, OPI and HPI converge, by
Theorem 3.1.4 (`bℝ₊` is countably Dedekind complete, Corollary A.5.17). -/
theorem proposition_3_2_1 (hgreedy : ∀ v ∈ bX ℝ≥0, ∃ σ, S.IsGreedy v σ) :
    S.adpBM.FundamentalOptimality S.adpBM_isGloballyStable.wellPosed ∧
      ∃ vstar, S.adpBM.IsValueFunction vstar ∧ S.adpBM.VFIConverges vstar ∧
        ∀ g, S.adpBM.IsSelector g → S.adpBM.OPIConverges g vstar ∧
          S.adpBM.HPIConverges S.adpBM_isGloballyStable.wellPosed g vstar :=
  ADP.theorem_3_1_4 (fun v => (hgreedy v.toFun (BM.mem_bX v)).imp fun σ hσ =>
    (S.adpBM_isGreedy_iff v σ).2 hσ) S.adpBM_isGloballyStable S.adpBM_orderBounded
    BM.countablyDedekindComplete

/-- **Remark 3.2.1** (p. 108): Proposition 3.2.1 also follows from Theorem 3.1.5, which adds
geometric convergence of VFI. -/
theorem remark_3_2_1 (hgreedy : ∀ v ∈ bX ℝ≥0, ∃ σ, S.IsGreedy v σ) :
    S.adpBM.FundamentalOptimality (ADP.isGloballyStable_of_contraction ⟨0⟩ S.β_nonneg
        S.β_lt_one S.adpBM_contraction).wellPosed ∧
      ∃ vstar, S.adpBM.VFIGeometric univ vstar := by
  obtain ⟨hFO, vstar, -, hgeo, -⟩ := ADP.theorem_3_1_5 BM.isSupNonexpansive S.β_nonneg
    S.β_lt_one S.adpBM_contraction ⟨isClosed_univ, fun v _ =>
      (hgreedy v.toFun (BM.mem_bX v)).imp fun σ hσ => (S.adpBM_isGreedy_iff v σ).2 hσ,
      mapsTo_univ _ _⟩ univ_nonempty
  exact ⟨hFO, vstar, hgeo⟩

/-! ### The weakly continuous case -/

/-- For continuous bounded `v`, `(w, c) ↦ ∫ v(R(w − c) + y) φ(dy)` is continuous. -/
theorem continuous_cont {v : BM ℝ≥0} (hv : Continuous v.toFun) :
    Continuous fun p : ℝ≥0 × ℝ≥0 => S.cont v.toFun p.1 p.2 := by
  have := S.φ_prob
  refine continuous_of_dominated (bound := fun _ => ‖v‖) (fun p => ?_) (fun p => ?_)
    (integrable_const _) (Eventually.of_forall fun y => ?_)
  · exact (v.measurable'.comp (measurable_const.add measurable_id)).aestronglyMeasurable
  · exact Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm v _
  · exact hv.comp ((continuous_const.mul (continuous_fst.sub continuous_snd)).add
      continuous_const)

/-- For continuous bounded `v`, the objective `(w, c) ↦ u(c) + β ∫ v(R(w − c) + y) φ(dy)` is
continuous. -/
theorem continuous_objective {v : BM ℝ≥0} (hv : Continuous v.toFun) :
    Continuous fun p : ℝ≥0 × ℝ≥0 => S.objective v.toFun p.1 p.2 :=
  (S.u_cont.comp continuous_snd).add (continuous_const.mul (S.continuous_cont hv))

/-- The maximizers of (3.10) at wealth `w`. -/
def argmaxSet (v : BM ℝ≥0) (w : ℝ≥0) : Set ℝ≥0 :=
  {c | c ≤ w ∧ ∀ d ≤ w, S.objective v.toFun w d ≤ S.objective v.toFun w c}

theorem argmaxSet_nonempty {v : BM ℝ≥0} (hv : Continuous v.toFun) (w : ℝ≥0) :
    (S.argmaxSet v w).Nonempty := by
  have hcpt : IsCompact (Icc (0 : ℝ≥0) w) := isCompact_Icc
  obtain ⟨c, hc, hmax⟩ := hcpt.exists_isMaxOn ⟨0, le_rfl, bot_le⟩
    ((S.continuous_objective hv).comp (continuous_const.prodMk continuous_id)).continuousOn
  exact ⟨c, hc.2, fun d hd => hmax ⟨bot_le, hd⟩⟩

theorem isClosed_argmaxSet {v : BM ℝ≥0} (hv : Continuous v.toFun) (w : ℝ≥0) :
    IsClosed (S.argmaxSet v w) := by
  have hO : Continuous fun c => S.objective v.toFun w c :=
    (S.continuous_objective hv).comp (continuous_const.prodMk continuous_id)
  have heq : {c | ∀ d ≤ w, S.objective v.toFun w d ≤ S.objective v.toFun w c} =
      ⋂ d, ⋂ (_ : d ≤ w), {c | S.objective v.toFun w d ≤ S.objective v.toFun w c} := by
    ext c
    simp
  have h2 : IsClosed {c | ∀ d ≤ w, S.objective v.toFun w d ≤ S.objective v.toFun w c} :=
    heq ▸ isClosed_iInter fun d => isClosed_iInter fun _ => isClosed_le continuous_const hO
  exact (isClosed_le continuous_id continuous_const).inter h2

/-- The largest maximizer of (3.10). -/
noncomputable def greedyBM (v : BM ℝ≥0) (w : ℝ≥0) : ℝ≥0 := sSup (S.argmaxSet v w)

theorem greedyBM_mem {v : BM ℝ≥0} (hv : Continuous v.toFun) (w : ℝ≥0) :
    S.greedyBM v w ∈ S.argmaxSet v w :=
  (S.isClosed_argmaxSet hv w).csSup_mem (S.argmaxSet_nonempty hv w) ⟨w, fun _ hc => hc.1⟩

/-- The largest maximizer is upper semicontinuous: `{w | a ≤ σ(w)}` is closed. -/
theorem isClosed_le_greedyBM {v : BM ℝ≥0} (hv : Continuous v.toFun) (a : ℝ≥0) :
    IsClosed {w | a ≤ S.greedyBM v w} := by
  refine isSeqClosed_iff_isClosed.1 fun ws w hws hlim => ?_
  have hO := S.continuous_objective hv
  obtain ⟨B, hB⟩ := hlim.bddAbove_range
  have hc : ∀ n, S.greedyBM v (ws n) ∈ Icc (0 : ℝ≥0) B := fun n =>
    ⟨bot_le, ((S.greedyBM_mem hv (ws n)).1).trans (hB ⟨n, rfl⟩)⟩
  obtain ⟨c, -, φ, hφ, hcφ⟩ := isCompact_Icc.tendsto_subseq hc
  have hwφ : Tendsto (ws ∘ φ) atTop (𝓝 w) := hlim.comp hφ.tendsto_atTop
  have hcw : c ≤ w := le_of_tendsto_of_tendsto' hcφ hwφ fun k =>
    (S.greedyBM_mem hv (ws (φ k))).1
  have hac : a ≤ c := ge_of_tendsto' hcφ fun k => hws (φ k)
  have hmem : c ∈ S.argmaxSet v w := by
    refine ⟨hcw, fun d hd => ?_⟩
    have hdk : Tendsto (fun k => min d (ws (φ k))) atTop (𝓝 d) := by
      have := (tendsto_const_nhds (x := d)).min hwφ
      rwa [min_eq_left hd] at this
    refine le_of_tendsto_of_tendsto' ((hO.tendsto (w, d)).comp (hwφ.prodMk_nhds hdk))
      ((hO.tendsto (w, c)).comp (hwφ.prodMk_nhds hcφ)) fun k => ?_
    exact (S.greedyBM_mem hv (ws (φ k))).2 _ (min_le_right _ _)
  exact hac.trans (le_csSup ⟨w, fun _ hc => hc.1⟩ hmem)

/-- The largest maximizer is a feasible (Borel) policy. -/
noncomputable def greedyPolicy {v : BM ℝ≥0} (hv : Continuous v.toFun) : SavingsPolicy :=
  ⟨S.greedyBM v, measurable_of_Ici fun a => (S.isClosed_le_greedyBM hv a).measurableSet,
    fun w => (S.greedyBM_mem hv w).1⟩

/-- For continuous `v`, the Bellman operator (1.51) is continuous in wealth. -/
theorem continuous_bellmanOp {v : BM ℝ≥0} (hv : Continuous v.toFun) :
    Continuous (S.bellmanOp v.toFun) := by
  have hO := S.continuous_objective hv
  have heq : S.bellmanOp v.toFun = fun w =>
      sSup ((fun t => S.objective v.toFun w (t * w)) '' Icc (0 : ℝ≥0) 1) := by
    funext w
    simp only [bellmanOp, iSup]
    congr 1
    ext z
    constructor
    · rintro ⟨⟨c, hc⟩, rfl⟩
      rcases eq_or_ne w 0 with rfl | hw
      · obtain rfl : c = 0 := le_antisymm hc bot_le
        exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩
      · refine ⟨c / w, ⟨bot_le, div_le_one_of_le₀ hc (bot_le)⟩, ?_⟩
        simp only [div_mul_cancel₀ c hw]
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t * w, mul_le_of_le_one_left (bot_le) ht.2⟩, rfl⟩
  rw [heq]
  exact isCompact_Icc.continuous_sSup (hO.comp (continuous_fst.prodMk
    (continuous_snd.mul continuous_fst)))

/-- **Exercise 3.2.7** (p. 109): if `v ∈ bcℝ₊`, then a `v`-greedy policy exists, and the Bellman
operator maps `bcℝ₊` into itself. -/
theorem exercise_3_2_7 {v : BM ℝ≥0} (hv : Continuous v.toFun) :
    S.IsGreedy v.toFun (S.greedyPolicy hv) ∧ Continuous (S.adpBM.bellman v).toFun := by
  have hg : S.IsGreedy v.toFun (S.greedyPolicy hv) := fun w c hc =>
    (S.greedyBM_mem hv w).2 c hc
  refine ⟨hg, ?_⟩
  have hvG : v ∈ S.adpBM.VG := ⟨_, (S.adpBM_isGreedy_iff v _).2 hg⟩
  rw [funext (S.adpBM_bellman_apply hvG)]
  exact S.continuous_bellmanOp hv

/-- `bcℝ₊` is closed in `bℝ₊`: uniform limits of continuous functions are continuous. -/
theorem isClosed_bc : IsClosed {v : BM ℝ≥0 | Continuous v.toFun} := by
  refine isSeqClosed_iff_isClosed.1 fun vs v hvs hlim => ?_
  exact (BM.tendstoUniformly_of_tendsto hlim).continuous (Frequently.of_forall hvs)

/-- **Proposition 3.2.2** (p. 109): with `φ` an arbitrary probability measure, the optimal savings
ADP obeys the fundamental optimality properties, the value function is continuous, and VFI
converges geometrically on `bcℝ₊`, by Theorem 3.1.5 with `V₀ = bcℝ₊`. -/
theorem proposition_3_2_2 :
    S.adpBM.FundamentalOptimality (ADP.isGloballyStable_of_contraction ⟨0⟩ S.β_nonneg
        S.β_lt_one S.adpBM_contraction).wellPosed ∧
      ∃ vstar, Continuous vstar.toFun ∧
        S.adpBM.VFIGeometric {v : BM ℝ≥0 | Continuous v.toFun} vstar := by
  obtain ⟨hFO, vstar, hv, hgeo, -⟩ := ADP.theorem_3_1_5 BM.isSupNonexpansive S.β_nonneg
    S.β_lt_one S.adpBM_contraction ⟨isClosed_bc, fun v hv =>
      ⟨_, (S.adpBM_isGreedy_iff v _).2 (S.exercise_3_2_7 hv).1⟩,
      fun v hv => (S.exercise_3_2_7 hv).2⟩ ⟨BM.const 0, continuous_const⟩
  exact ⟨hFO, vstar, hv, hgeo⟩

end OptimalSavings

end SargentStachurski.ADPsOnPospaces
