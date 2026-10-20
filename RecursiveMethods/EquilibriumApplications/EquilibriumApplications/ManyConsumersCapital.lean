/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.ManyConsumersOperator
import EquilibriumApplications.ManyConsumersClosed
import EquilibriumApplications.ManyConsumersExample

/-!
# A capital bound: `U(κ)` is closed, and `v` solves (4)

SLP §16.7, pp. 497–499.

* `MCCapitalBound Φ` is (T8): `(γ, y) ∈ Φ(κ)` implies `‖y‖ ≤ max(‖κ‖, R)` (fix (ii) of the NOTE
  to Exercise 16.7a). The example technology violates it (`mcExPhi_not_capitalBound`).
* `mc_path_bound`, `mcProdSetUnb_eq` (`Y′(κ) = Y(κ)` under (T8)), `ex_16_7a_closed_of_bound`
  (the book's `Y(κ)` is closed under (T8)).
* `mc_seqTrunc_tendsto`, `mc_utility_tendsto_coord`: `uᵢ` is continuous for coordinatewise
  convergence on `C` (the tail bound of Exercise 5.11d plus sup-norm continuity on truncations).
* `mcUtilSet_isClosed`: under (T8), `U(κ)` is closed (paths stay in a compact ball; Tychonoff and
  the closed graph of `Φ` give a feasible limit allocation).
* `ex_16_7c_of_bound`, `mc_eq4_of_bound`, `mc_support_unique_fixed_of_bound`: Exercise 16.7c,
  equation (4), and "the unique admissible solution of (4) is the support function (2)", with the
  closedness hypothesis discharged.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open Filter Topology Set

variable {l p : ℕ} {Φ : (Fin p → ℝ) → Set ((Fin l → ℝ) × (Fin p → ℝ))} {ι : Type*} [Fintype ι]

/-- **(T8), a capital bound** (fix (ii) of the NOTE to Exercise 16.7a): for some `R ≥ 0`,
`(γ, y) ∈ Φ(κ)` implies `‖y‖ ≤ max(‖κ‖, R)`. -/
def MCCapitalBound (Φ : (Fin p → ℝ) → Set ((Fin l → ℝ) × (Fin p → ℝ))) : Prop :=
  ∃ R, 0 ≤ R ∧ ∀ κ, 0 ≤ κ → ∀ q ∈ Φ κ, ‖q.2‖ ≤ max ‖κ‖ R

/-- The example technology `y ≤ 2κ` violates (T8). -/
theorem mcExPhi_not_capitalBound : ¬ MCCapitalBound mcExPhi := by
  rintro ⟨R, hR, h⟩
  have hκ : (0 : Fin 1 → ℝ) ≤ fun _ => R + 1 := fun _ => by
    change (0 : ℝ) ≤ R + 1
    linarith
  have hq : ((0 : Fin 1 → ℝ), (fun _ => 2 * (R + 1) : Fin 1 → ℝ)) ∈ mcExPhi (fun _ => R + 1) :=
    ⟨le_rfl, fun _ => sub_nonneg.2 (Real.exp_le_one_iff.2 (by
      change -(R + 1) ≤ 0
      linarith)), fun _ => by
        change (0 : ℝ) ≤ 2 * (R + 1)
        linarith, fun _ => le_rfl⟩
  have := h _ hκ _ hq
  have e1 : ‖(fun _ => 2 * (R + 1) : Fin 1 → ℝ)‖ = 2 * (R + 1) := by
    rw [pi_norm_const, Real.norm_of_nonneg (by linarith)]
  have e2 : ‖(fun _ => R + 1 : Fin 1 → ℝ)‖ = R + 1 := by
    rw [pi_norm_const, Real.norm_of_nonneg (by linarith)]
  rw [e1, e2, max_eq_left (by linarith)] at this
  linarith

omit [Fintype ι] in
/-- Under (T8) every feasible capital path satisfies `‖k_t‖ ≤ max(‖k₀‖, R)`. -/
theorem mc_path_bound {R : ℝ} (hR : ∀ κ, 0 ≤ κ → ∀ q ∈ Φ κ, ‖q.2‖ ≤ max ‖κ‖ R)
    {k : ℕ → Fin p → ℝ} {γ : ℕ → Fin l → ℝ} (hk0 : ∀ t, 0 ≤ k t)
    (hk : ∀ t, (γ t, k (t + 1)) ∈ Φ (k t)) : ∀ t, ‖k t‖ ≤ max ‖k 0‖ R := by
  intro t
  induction t with
  | zero => exact le_max_left _ _
  | succ t ih => exact (hR _ (hk0 t) _ (hk t)).trans (max_le ih (le_max_right _ _))

omit [Fintype ι] in
/-- Under (T8), `Y′(κ) = Y(κ)`: feasible capital paths are automatically bounded. -/
theorem mcProdSetUnb_eq (hb : MCCapitalBound Φ) (κ : Fin p → ℝ) :
    mcProdSetUnb Φ κ = mcProdSet Φ κ := by
  obtain ⟨R, -, hR⟩ := hb
  refine Subset.antisymm ?_ (mcProdSet_subset_unb κ)
  rintro c ⟨hc0, k, hk0, hkk, hk⟩
  have hbd := mc_path_bound hR hk0 hk
  exact ⟨hc0, BddSeq.mk k (max ‖k 0‖ R) hbd, hk0, hkk, hk⟩

omit [Fintype ι] in
/-- **Exercise 16.7a under (T8)**: the book's `Y(κ)` is closed. -/
theorem ex_16_7a_closed_of_bound (hΦ : ManyConsumersTech Φ) (hb : MCCapitalBound Φ)
    {κ : Fin p → ℝ} (hκ : 0 ≤ κ) : IsClosed (mcProdSet Φ κ) := by
  rw [← mcProdSetUnb_eq hb]
  exact ex_16_7a_closed hΦ hκ

omit [Fintype ι] in
/-- Coordinatewise convergence makes truncations converge in the sup norm. -/
theorem mc_seqTrunc_tendsto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {xs : ℕ → BddSeq E} {x : BddSeq E} (hlim : ∀ t, Tendsto (fun n => xs n t) atTop (𝓝 (x t)))
    (T : ℕ) : Tendsto (fun n => seqTrunc T (xs n)) atTop (𝓝 (seqTrunc T x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsum : Tendsto (fun n => ∑ t ∈ Finset.range (T + 1), ‖xs n t - x t‖) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.range (T + 1)) fun t _ =>
      tendsto_iff_norm_sub_tendsto_zero.1 (hlim t)
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hsum
  rw [← map_sub]
  refine lp.norm_le_of_forall_le (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun t => ?_
  rw [seqTrunc_apply, mc_sub_apply]
  split_ifs with h
  · exact Finset.single_le_sum (f := fun t => ‖xs n t - x t‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_range.2 (by omega))
  · rw [norm_zero]
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _

omit [Fintype ι] in
/-- **Utility is continuous for coordinatewise convergence** (the product topology): if
`x_n → x` coordinate by coordinate in `C`, then `u(x_n) → u(x)`. The tail bound
`|u(x) − u(xᵀ)| ≤ 2Bβᵀ` of Exercise 5.11d reduces this to sup-norm continuity on truncations. -/
theorem mc_utility_tendsto_coord {W : (Fin l → ℝ) → ℝ → ℝ} {β : ℝ}
    (hW : IsAggregator (Ici (0 : Fin l → ℝ)) W β) {v : BddSeq (Fin l → ℝ) → ℝ}
    (hv : IsAggregatorFixedPoint (Ici 0) W v) {xs : ℕ → BddSeq (Fin l → ℝ)}
    {x : BddSeq (Fin l → ℝ)} (hxs : ∀ n, xs n ∈ mcCons l) (hx : x ∈ mcCons l)
    (hlim : ∀ t, Tendsto (fun n => xs n t) atTop (𝓝 (x t))) :
    Tendsto (fun n => v (xs n)) atTop (𝓝 (v x)) := by
  obtain ⟨B, hB⟩ := hv.bounded
  have hbd := aggregator_seqTrunc_bound self_mem_Ici hW hv hB
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hpow : Tendsto (fun T : ℕ => 2 * B * β ^ T) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hW.beta_pos.le
      hW.beta_lt_one).const_mul (2 * B)
  obtain ⟨T, hT⟩ := (hpow.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 3))).exists
  have hcont : Tendsto (fun n => v (seqTrunc T (xs n))) atTop (𝓝 (v (seqTrunc T x))) :=
    ((hv.continuousOn _ (seqTrunc_mem_seqSet self_mem_Ici hx T)).tendsto).comp
      (tendsto_nhdsWithin_iff.2 ⟨mc_seqTrunc_tendsto hlim T,
        Eventually.of_forall fun n => seqTrunc_mem_seqSet self_mem_Ici (hxs n) T⟩)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hcont (ε / 3) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hbd T _ (hxs n)
  have h2 := hbd T _ hx
  have h3 := hN n hn
  rw [Real.dist_eq] at h3 ⊢
  have e1 := abs_sub_le (v (xs n)) (v (seqTrunc T (xs n))) (v x)
  have e2 := abs_sub_le (v (seqTrunc T (xs n))) (v (seqTrunc T x)) (v x)
  rw [abs_sub_comm (v (seqTrunc T x))] at e2
  linarith

/-- **`U(κ)` is closed under (T8).** Feasible capital paths stay in a compact ball, so the
allocations stay in a compact set of the product topology; a coordinatewise convergent
subsequence has a feasible limit (closed graph of `Φ`), and utilities converge
(`mc_utility_tendsto_coord`). -/
theorem mcUtilSet_isClosed {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, IsAggregator (Ici (0 : Fin l → ℝ)) (W i) (β i))
    {u : ι → BddSeq (Fin l → ℝ) → ℝ} (hu : ∀ i, IsAggregatorFixedPoint (Ici 0) (W i) (u i))
    (hΦ : ManyConsumersTech Φ) (hb : MCCapitalBound Φ) (κ : Fin p → ℝ) :
    IsClosed (mcUtilSet Φ u κ) := by
  obtain ⟨R, -, hR⟩ := hb
  set R' := max ‖κ‖ R with hR'
  set K : Set (Fin p → ℝ) := Metric.closedBall 0 R' ∩ Ici 0 with hKdef
  have hKc : IsCompact K := (isCompact_closedBall 0 R').inter_right isClosed_Ici
  have hQ := hΦ.isCompact_image hKc inter_subset_right
  have hbdd : ∀ m : Fin l, BddAbove ((fun q : (Fin l → ℝ) × (Fin p → ℝ) => q.1 m) ''
      {q | ∃ κ' ∈ K, q ∈ Φ κ'}) := fun m =>
    (hQ.image ((continuous_apply m).comp continuous_fst)).bddAbove
  choose g hg using hbdd
  refine isClosed_of_closure_subset fun z hz => ?_
  obtain ⟨zs, hzs, hlim⟩ := mem_closure_iff_seq_limit.1 hz
  choose c hc hzc using hzs
  choose hc0 k hk0 hkk hk using fun n => (hc n).2
  have hkK : ∀ n t, k n t ∈ K := fun n t => by
    refine ⟨mem_closedBall_zero_iff.2 ?_, hk0 n t⟩
    have := mc_path_bound (k := fun t => k n t) hR (fun t => hk0 n t) (hk n) t
    rwa [hkk n] at this
  have hcle : ∀ n i t, c n i t ≤ g := fun n i t m => by
    have h1 : (∑ j, c n j) t m ≤ g m := hg m ⟨_, ⟨k n t, hkK n t, hk n t⟩, rfl⟩
    rw [mc_sum_apply] at h1
    simp only [Finset.sum_apply] at h1
    exact (Finset.single_le_sum (f := fun j => c n j t m)
      (fun j _ => ((hc n).1 j t) m) (Finset.mem_univ i)).trans h1
  set X : ℕ → ℕ → (ι → Fin l → ℝ) × (Fin p → ℝ) := fun n t => (fun i => c n i t, k n t)
  have hXP : ∀ n, X n ∈ Set.pi univ fun _ => Icc (0 : ι → Fin l → ℝ) (fun _ => g) ×ˢ K :=
    fun n t _ => ⟨⟨fun i => (hc n).1 i t, fun i => hcle n i t⟩, hkK n t⟩
  obtain ⟨X0, hX0, φ, hφ, hXlim⟩ :=
    (isCompact_univ_pi fun _ => isCompact_Icc.prod hKc).tendsto_subseq hXP
  have hev : ∀ t, Continuous fun x : ℕ → (ι → Fin l → ℝ) × (Fin p → ℝ) => x t := fun t =>
    continuous_apply t
  have hct : ∀ i t, Tendsto (fun n => c (φ n) i t) atTop (𝓝 ((X0 t).1 i)) := fun i t =>
    (((continuous_apply i).comp (continuous_fst.comp (hev t))).tendsto _).comp hXlim
  have hkt : ∀ t, Tendsto (fun n => k (φ n) t) atTop (𝓝 (X0 t).2) := fun t =>
    ((continuous_snd.comp (hev t)).tendsto _).comp hXlim
  have hgn : ∀ t i, ‖(X0 t).1 i‖ ≤ ‖g‖ := fun t i => by
    have hm := (hX0 t (mem_univ t)).1
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg g)).2 fun m => ?_
    rw [Real.norm_of_nonneg (hm.1 i m)]
    exact (hm.2 i m).trans ((Real.le_norm_self _).trans (norm_le_pi_norm g m))
  set c0 : ι → BddSeq (Fin l → ℝ) := fun i =>
    BddSeq.mk (fun t => (X0 t).1 i) ‖g‖ fun t => hgn t i with hc0def
  set k0 : BddSeq (Fin p → ℝ) := BddSeq.mk (fun t => (X0 t).2) R' fun t => by
    have := (hX0 t (mem_univ t)).2.1
    rwa [mem_closedBall_zero_iff] at this with hk0def
  have hcC : ∀ i, c0 i ∈ mcCons l := fun i t => (hX0 t (mem_univ t)).1.1 i
  have hsum : ∀ t, Tendsto (fun n => (∑ i, c (φ n) i) t) atTop (𝓝 ((∑ i, c0 i) t)) :=
    fun t => by
      simp only [mc_sum_apply]
      exact tendsto_finsetSum _ fun i _ => hct i t
  have hfeas : mcFeasible Φ κ c0 := by
    refine ⟨hcC, fun t => ?_, k0, fun t => (hX0 t (mem_univ t)).2.2, ?_, fun t => ?_⟩
    · rw [mc_sum_apply]
      exact Finset.sum_nonneg fun i _ => hcC i t
    · change (X0 0).2 = κ
      exact tendsto_nhds_unique (hkt 0) (by simp [hkk])
    · have hG := hΦ.isClosed_graph.mem_of_tendsto
        ((hkt t).prodMk_nhds ((hsum t).prodMk_nhds (hkt (t + 1))))
        (Eventually.of_forall fun n => ⟨hk0 (φ n) t, hk (φ n) t⟩)
      exact hG.2
  refine ⟨c0, hfeas, funext fun i => tendsto_nhds_unique
    (((continuous_apply i).tendsto z).comp (hlim.comp hφ.tendsto_atTop)) ?_⟩
  have h := mc_utility_tendsto_coord (hW i) (hu i) (fun n => (hc (φ n)).1 i) (hcC i)
    fun t => hct i t
  refine h.congr fun n => ?_
  simp only [Function.comp_apply, hzc]

/-- **Exercise 16.7c under (T8)**, with no closedness hypothesis. -/
theorem ex_16_7c_of_bound {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, ManyConsumersAggregator (W i) (β i)) {u : ι → BddSeq (Fin l → ℝ) → ℝ}
    (hu : ∀ i, IsAggregatorFixedPoint (Ici 0) (W i) (u i)) (hΦ : ManyConsumersTech Φ)
    (hb : MCCapitalBound Φ) {κ : Fin p → ℝ} (hκ : 0 ≤ κ) (z : ι → ℝ) :
    z ∈ mcUtilSet Φ u κ ↔ 0 ≤ z ∧ ∀ θ ∈ mcSimplex ι, ∑ i, θ i * z i ≤ mcSupport Φ u κ θ :=
  ex_16_7c hW hu hΦ hκ (mcUtilSet_isClosed (fun i => (hW i).agg) hu hΦ hb κ) z

/-- **Equation (4) under (T8)**: `v = Tv` with no closedness hypothesis. -/
theorem mc_eq4_of_bound {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, ManyConsumersAggregator (W i) (β i)) {u : ι → BddSeq (Fin l → ℝ) → ℝ}
    (hu : ∀ i, IsAggregatorFixedPoint (Ici 0) (W i) (u i)) (hΦ : ManyConsumersTech Φ)
    (hb : MCCapitalBound Φ) {κ : Fin p → ℝ} (hκ : 0 ≤ κ) (θ : ι → ℝ) :
    mcSupport Φ u κ θ = mcOperator W Φ (mcSupport Φ u) κ θ :=
  mc_eq4 hW hu hΦ (fun κ' _ => mcUtilSet_isClosed (fun i => (hW i).agg) hu hΦ hb κ') hκ θ

/-- **The Principle of Optimality under (T8)**: the support function `v` of (2) is the unique
admissible solution of (4). -/
theorem mc_support_unique_fixed_of_bound {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, ManyConsumersAggregator (W i) (β i)) {u : ι → BddSeq (Fin l → ℝ) → ℝ}
    (hu : ∀ i, IsAggregatorFixedPoint (Ici 0) (W i) (u i)) (hΦ : ManyConsumersTech Φ)
    (hb : MCCapitalBound Φ) {β0 : ℝ} (hβ0 : ∀ i, β i ≤ β0) (hβ00 : 0 ≤ β0) (hβ1 : β0 < 1) :
    (∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι,
      mcOperator W Φ (mcSupport Φ u) κ θ = mcSupport Φ u κ θ) ∧
    ∀ w, MCAdmissible w → (∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, mcOperator W Φ w κ θ = w κ θ) →
      ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, w κ θ = mcSupport Φ u κ θ :=
  mc_support_unique_fixed hW hu hΦ hβ0 hβ00 hβ1
    fun κ' _ => mcUtilSet_isClosed (fun i => (hW i).agg) hu hΦ hb κ'

end StokeyLucasPrescott.EquilibriumApplications
