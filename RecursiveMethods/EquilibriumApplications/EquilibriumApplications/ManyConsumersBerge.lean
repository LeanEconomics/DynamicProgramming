/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.ManyConsumersCapital

/-!
# Continuity of `Tf`, of `v`, and the policy correspondence

SLP §16.7, pp. 498–499. `F_s` is the set of `f ∈ F` (`MCInF`) of support-function type
(`mcSupportType`).

* Preliminaries: `mcSimplex_isCompact`, `mc_sum_posPart_le`, `mc_uniform_of_tendsto`
  (`f(κₙ, ·) → f(κ, ·)` uniformly on `Δᴵ`), `mcObjective_tendsto` (joint continuity of the
  objective).
* `mcConstraint_uhc`: the constraint correspondence of (4) is upper hemicontinuous for `f ∈ F`.
* `mcConstraint_lhc`: it is lower hemicontinuous for `f ∈ F_s` (consumption shaved by
  `(γᵢ − δₙ)⁺` and free disposal; utilities by the corrected hint `𝒰ᵃ = B`). This is the step
  that fails for general `f ∈ F` (`ex_16_7e_counterexample`).
* **Exercise 16.7e, corrected**: `mcOperator_tendsto`, `mcOperator_continuousOn` (Berge's maximum
  theorem, proved directly with sequences) and `ex_16_7e` (`T` maps `F_s` into `F_s`).
* **Exercise 16.7g**: `mcPolicy` (the policy correspondence), `mcPolicy_value`,
  `mcPolicy_nonempty`, `ex_16_7g_uhc` (upper hemicontinuity for `f ∈ F_s`).
* **The solution of (4) is continuous**: `mc_exists_beta`, `ex_16_7e_fixed` (the admissible fixed
  point lies in `F`), `mcSupport_inF` (under (T8) the support function `v` of (2) is in `F_s`), and
  `ex_16_7g_support` (under (T8) the policy correspondence for `f = v` is nonempty,
  convex-valued and upper hemicontinuous).
* **Pareto optima as equilibria**: `mc_supporting_nonneg` (supporting prices are nonnegative on
  `C`), `mc_competitiveEq_of_pos` (with the cheaper point `0`, a Pareto optimum is a competitive
  equilibrium when every consumer's bundle has positive value).

**Not proved.** The cheaper-point condition itself (`φ(cᵢ) > 0` for every consumer) is assumed in
`mc_competitiveEq_of_pos`; it can fail for a consumer whose bundle has zero value. Existence of the
utility functions `u_W` (Exercise 5.11d) is a hypothesis throughout.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open Filter Topology Set

variable {l p : ℕ} {Φ : (Fin p → ℝ) → Set ((Fin l → ℝ) × (Fin p → ℝ))} {ι : Type*} [Fintype ι]

/-! ### Preliminaries -/

/-- `Δᴵ` is compact. -/
theorem mcSimplex_isCompact : IsCompact (mcSimplex ι) := by
  refine (isCompact_Icc (a := (0 : ι → ℝ)) (b := 1)).of_isClosed_subset ?_
    fun θ hθ => ⟨hθ.1, fun i => mcSimplex_le_one hθ i⟩
  have e : mcSimplex ι = (⋂ i, {θ : ι → ℝ | 0 ≤ θ i}) ∩ {θ | ∑ i, θ i = 1} := by
    ext θ
    exact ⟨fun h => ⟨mem_iInter.2 h.1, h.2⟩, fun h => ⟨mem_iInter.1 h.1, h.2⟩⟩
  rw [e]
  exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)

omit [Fintype ι] in
/-- `Σᵢ (aᵢ − δ)⁺ ≤ (Σᵢ aᵢ − δ)⁺` for `aᵢ ≥ 0`, `δ ≥ 0`. -/
theorem mc_sum_posPart_le (s : Finset ι) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∑ i ∈ s, max (a i - δ) 0 ≤ max (∑ i ∈ s, a i - δ) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    have hA : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg fun i _ => ha i
    rcases le_total δ (a j) with h | h
    · rw [max_eq_left (by linarith : 0 ≤ a j - δ)]
      have h1 : max (∑ i ∈ s, a i - δ) 0 ≤ ∑ i ∈ s, a i := max_le (by linarith) hA
      exact le_max_of_le_left (by linarith)
    · rw [max_eq_right (by linarith : a j - δ ≤ 0), zero_add]
      exact ih.trans (max_le_max (by linarith [ha j]) le_rfl)

/-- Uniform convergence of `f(κₙ, ·) → f(κ, ·)` on `Δᴵ` for `f ∈ F` (uniform continuity on the
compact set `{κₙ} ∪ {κ}` × `Δᴵ`). -/
theorem mc_uniform_of_tendsto {f : (Fin p → ℝ) → (ι → ℝ) → ℝ} (hf : MCInF f)
    {κs : ℕ → Fin p → ℝ} {κ : Fin p → ℝ} (hκs : ∀ᶠ n in atTop, 0 ≤ κs n) (hκ : 0 ≤ κ)
    (hlim : Tendsto κs atTop (𝓝 κ)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ θ ∈ mcSimplex ι, |f (κs n) θ - f κ θ| < ε := by
  intro ε hε
  set K := insert κ (range κs) ∩ Ici 0 with hK
  have hKc : IsCompact K := hlim.isCompact_insert_range.inter_right isClosed_Ici
  have huc := (hKc.prod mcSimplex_isCompact).uniformContinuousOn_of_continuous
    (hf.cont.mono (prod_mono inter_subset_right le_rfl))
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuousOn_iff.1 huc ε hε
  filter_upwards [hκs, Metric.tendsto_nhds.1 hlim δ hδ] with n hn hd θ hθ
  have h := hδε ((κs n), θ) ⟨⟨mem_insert_of_mem _ ⟨n, rfl⟩, hn⟩, hθ⟩ (κ, θ)
    ⟨⟨mem_insert _ _, hκ⟩, hθ⟩ (by rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]; exact hd)
  rwa [Real.dist_eq] at h

/-- Joint continuity of the objective of (4) in `(θ, q)`. -/
theorem mcObjective_tendsto {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, IsAggregator (Ici (0 : Fin l → ℝ)) (W i) (β i)) {θs : ℕ → ι → ℝ} {θ : ι → ℝ}
    (hθ : Tendsto θs atTop (𝓝 θ)) {qs : ℕ → (ι → Fin l → ℝ) × (ι → ℝ) × (Fin p → ℝ)}
    {q : (ι → Fin l → ℝ) × (ι → ℝ) × (Fin p → ℝ)} (hq : Tendsto qs atTop (𝓝 q))
    (hqs : ∀ᶠ n in atTop, (∀ i, 0 ≤ (qs n).1 i) ∧ 0 ≤ (qs n).2.1)
    (hq0 : (∀ i, 0 ≤ q.1 i) ∧ 0 ≤ q.2.1) :
    Tendsto (fun n => mcObjective W (θs n) (qs n)) atTop (𝓝 (mcObjective W θ q)) := by
  unfold mcObjective
  refine tendsto_finsetSum _ fun i _ => ?_
  refine (((continuous_apply i).tendsto _).comp hθ).mul ?_
  have hin : Tendsto (fun n => ((qs n).1 i, (qs n).2.1 i)) atTop
      (𝓝[Ici 0 ×ˢ Ici 0] (q.1 i, q.2.1 i)) :=
    tendsto_nhdsWithin_iff.2 ⟨((((continuous_apply i).comp continuous_fst).tendsto _).comp
      hq).prodMk_nhds ((((continuous_apply i).comp (continuous_fst.comp continuous_snd)).tendsto
        _).comp hq), hqs.mono fun n hn =>
          (show ((qs n).1 i, (qs n).2.1 i) ∈ Ici 0 ×ˢ Ici 0 from ⟨hn.1 i, hn.2 i⟩)⟩
  exact ((hW i).continuousOn _ (show (q.1 i, q.2.1 i) ∈ Ici 0 ×ˢ Ici 0 from
    ⟨hq0.1 i, hq0.2 i⟩)).tendsto.comp hin

/-! ### Upper and lower hemicontinuity of the constraint correspondence -/

/-- **Upper hemicontinuity of the constraint correspondence** of (4) for `f ∈ F`: constraint
points along `κₙ → κ` have a subsequence converging to a constraint point at `κ`. -/
theorem mcConstraint_uhc (hΦ : ManyConsumersTech Φ) {f : (Fin p → ℝ) → (ι → ℝ) → ℝ}
    (hf : MCInF f) {κs : ℕ → Fin p → ℝ} {κ : Fin p → ℝ} (hκs : ∀ n, 0 ≤ κs n)
    (hlim : Tendsto κs atTop (𝓝 κ)) {qs : ℕ → (ι → Fin l → ℝ) × (ι → ℝ) × (Fin p → ℝ)}
    (hqs : ∀ n, qs n ∈ mcConstraint Φ f (κs n)) :
    ∃ q ∈ mcConstraint Φ f κ, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (qs ∘ φ) atTop (𝓝 q) := by
  classical
  obtain ⟨M, hM⟩ := hf.bdd
  have hκ : 0 ≤ κ := ge_of_tendsto' hlim hκs
  set K := insert κ (range κs) with hKdef
  have hKc : IsCompact K := hlim.isCompact_insert_range
  have hK0 : K ⊆ Ici 0 := by
    rintro x (rfl | ⟨n, rfl⟩)
    exacts [hκ, hκs n]
  have hQ := hΦ.isCompact_image hKc hK0
  have hbdd : ∀ m : Fin l, BddAbove ((fun q : (Fin l → ℝ) × (Fin p → ℝ) => q.1 m) ''
      {q | ∃ κ' ∈ K, q ∈ Φ κ'}) := fun m =>
    (hQ.image ((continuous_apply m).comp continuous_fst)).bddAbove
  choose g hg using hbdd
  have hmem : ∀ n, qs n ∈ Icc (0 : ι → Fin l → ℝ) (fun _ => g) ×ˢ
      (Icc (0 : ι → ℝ) (fun _ => M) ×ˢ (Prod.snd '' {q | ∃ κ' ∈ K, q ∈ Φ κ'})) := by
    intro n
    have hq := hqs n
    have hκ' := mcConstraint_kappa_nonneg hΦ (hκs n) hq
    have hin : (∑ j, (qs n).1 j, (qs n).2.2) ∈ {q | ∃ κ' ∈ K, q ∈ Φ κ'} :=
      ⟨κs n, mem_insert_of_mem _ ⟨n, rfl⟩, hq.2.1⟩
    refine ⟨⟨hq.1, fun i m => ?_⟩, ⟨hq.2.2.1, fun i => (mcUpper_le hq.2.2 i).trans
      (hM _ hκ' _ (mc_single_mem_simplex i))⟩, ⟨_, hin, rfl⟩⟩
    have h1 : (∑ j, (qs n).1 j) m ≤ g m := hg m ⟨_, hin, rfl⟩
    simp only [Finset.sum_apply] at h1
    exact (Finset.single_le_sum (f := fun j => (qs n).1 j m) (fun j _ => hq.1 j m)
      (Finset.mem_univ i)).trans h1
  obtain ⟨q, -, φ, hφ, hq⟩ :=
    (isCompact_Icc.prod (isCompact_Icc.prod (hQ.image continuous_snd))).tendsto_subseq hmem
  refine ⟨q, ?_, φ, hφ, hq⟩
  have h1 : Tendsto (fun n => (qs (φ n)).1) atTop (𝓝 q.1) := (continuous_fst.tendsto _).comp hq
  have h2 : Tendsto (fun n => (qs (φ n)).2.1) atTop (𝓝 q.2.1) :=
    ((continuous_fst.comp continuous_snd).tendsto _).comp hq
  have h3 : Tendsto (fun n => (qs (φ n)).2.2) atTop (𝓝 q.2.2) :=
    ((continuous_snd.comp continuous_snd).tendsto _).comp hq
  have hκφ : Tendsto (fun n => κs (φ n)) atTop (𝓝 κ) := hlim.comp hφ.tendsto_atTop
  have hγ : ∀ i, 0 ≤ q.1 i := fun i =>
    ge_of_tendsto' (((continuous_apply i).tendsto _).comp h1) fun n => (hqs (φ n)).1 i
  have hsum : Tendsto (fun n => ∑ i, (qs (φ n)).1 i) atTop (𝓝 (∑ i, q.1 i)) :=
    ((continuous_finsetSum _ fun i _ => continuous_apply i).tendsto _).comp h1
  have hG := hΦ.isClosed_graph.mem_of_tendsto (hκφ.prodMk_nhds (hsum.prodMk_nhds h3))
    (Eventually.of_forall fun n => ⟨hκs (φ n), (hqs (φ n)).2.1⟩)
  have hκ' : 0 ≤ q.2.2 := (hΦ.nonneg κ hκ _ hG.2).2
  refine ⟨hγ, hG.2, ge_of_tendsto' h2 fun n => (hqs (φ n)).2.2.1, fun θ hθ => ?_⟩
  have hfθ : Tendsto (fun n => f (qs (φ n)).2.2 θ) atTop (𝓝 (f q.2.2 θ)) := by
    have hin : Tendsto (fun n => ((qs (φ n)).2.2, θ)) atTop
        (𝓝[Ici 0 ×ˢ mcSimplex ι] (q.2.2, θ)) :=
      tendsto_nhdsWithin_iff.2 ⟨h3.prodMk_nhds tendsto_const_nhds, Eventually.of_forall
        fun n => ⟨mcConstraint_kappa_nonneg hΦ (hκs (φ n)) (hqs (φ n)), hθ⟩⟩
    exact (hf.cont (q.2.2, θ) ⟨hκ', hθ⟩).tendsto.comp hin
  exact le_of_tendsto_of_tendsto' (((continuous_finsetSum _ fun i _ =>
    continuous_const.mul (continuous_apply i)).tendsto _).comp h2) hfθ
    fun n => (hqs (φ n)).2.2.2 θ hθ

/-- **Lower hemicontinuity of the constraint correspondence** of (4) for `f ∈ F` of
support-function type (the missing step of Exercise 16.7e). Consumption: shave `δₙ` off each
consumer (`(γᵢ − δₙ)⁺`) and use free disposal under the lower-hemicontinuous `Φ`; utilities: by the
corrected hint, `z′ ≤ z″ₙ + ηₙ𝟙` with `z″ₙ ∈ 𝒰_f(κ′ₙ)` and `ηₙ = sup_θ |f(κ′ₙ, θ) − f(κ′, θ)| → 0`,
and `min(z′, z″ₙ) ∈ 𝒰_f(κ′ₙ)` is within `ηₙ` of `z′`. -/
theorem mcConstraint_lhc (hΦ : ManyConsumersTech Φ) {f : (Fin p → ℝ) → (ι → ℝ) → ℝ}
    (hf : MCInF f) (hfs : mcSupportType f) {κs : ℕ → Fin p → ℝ} {κ : Fin p → ℝ}
    (hκs : ∀ n, 0 ≤ κs n) (hlim : Tendsto κs atTop (𝓝 κ))
    {q : (ι → Fin l → ℝ) × (ι → ℝ) × (Fin p → ℝ)} (hq : q ∈ mcConstraint Φ f κ) :
    ∃ qs : ℕ → (ι → Fin l → ℝ) × (ι → ℝ) × (Fin p → ℝ),
      (∀ᶠ n in atTop, qs n ∈ mcConstraint Φ f (κs n)) ∧ Tendsto qs atTop (𝓝 q) := by
  obtain ⟨hγ, hΦq, hz⟩ := hq
  have hκ : 0 ≤ κ := ge_of_tendsto' hlim hκs
  obtain ⟨ps, hps, hpslim⟩ := hΦ.lhc κs κ hκs hlim _ hΦq
  set δ : ℕ → ℝ := fun n => ‖(ps n).1 - ∑ i, q.1 i‖ with hδdef
  have hδ0 : ∀ n, 0 ≤ δ n := fun n => norm_nonneg _
  have hδlim : Tendsto δ atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 ((continuous_fst.tendsto _).comp hpslim)
  set γs : ℕ → ι → Fin l → ℝ := fun n i m => max (q.1 i m - δ n) 0 with hγsdef
  have hγs : Tendsto γs atTop (𝓝 q.1) := tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun m => by
    have h := (tendsto_const_nhds (x := q.1 i m)).sub hδlim |>.max
      (tendsto_const_nhds (x := (0 : ℝ)))
    have hγim : (0 : ℝ) ≤ q.1 i m := hγ i m
    rwa [sub_zero, max_eq_left hγim] at h
  set κ's : ℕ → Fin p → ℝ := fun n => (ps n).2 with hκ'sdef
  have hκ'lim : Tendsto κ's atTop (𝓝 q.2.2) := (continuous_snd.tendsto _).comp hpslim
  have hκ' : 0 ≤ q.2.2 := (hΦ.nonneg κ hκ _ hΦq).2
  have hκ's0 : ∀ᶠ n in atTop, 0 ≤ κ's n := hps.mono fun n hn => (hΦ.nonneg _ (hκs n) _ hn).2
  obtain ⟨M, hM⟩ := hf.bdd
  set η : ℕ → ℝ := fun n =>
    sSup (insert 0 ((fun θ => |f (κ's n) θ - f q.2.2 θ|) '' mcSimplex ι)) with hηdef
  have hbddη : ∀ n, 0 ≤ κ's n →
      BddAbove (insert 0 ((fun θ => |f (κ's n) θ - f q.2.2 θ|) '' mcSimplex ι)) := by
    intro n hn
    refine ⟨max M 0, ?_⟩
    rintro _ (rfl | ⟨θ, hθ, rfl⟩)
    · exact le_max_right _ _
    · have h1 := hf.nonneg _ hn θ hθ
      have h2 := hf.nonneg _ hκ' θ hθ
      have h3 := hM _ hn θ hθ
      have h4 := hM _ hκ' θ hθ
      rw [abs_le]
      constructor <;> linarith [le_max_left M 0]
  have hη0 : ∀ n, 0 ≤ η n := fun n => Real.sSup_nonneg fun x hx => by
    rcases hx with rfl | ⟨θ, -, rfl⟩
    exacts [le_rfl, abs_nonneg _]
  have hηbd : ∀ n, 0 ≤ κ's n → ∀ θ ∈ mcSimplex ι, |f (κ's n) θ - f q.2.2 θ| ≤ η n :=
    fun n hn θ hθ => le_csSup (hbddη n hn) (mem_insert_of_mem _ ⟨θ, hθ, rfl⟩)
  have hunif := mc_uniform_of_tendsto hf hκ's0 hκ' hκ'lim
  have hηlim : Tendsto η atTop (𝓝 0) := by
    rw [tendsto_order]
    refine ⟨fun a ha => Eventually.of_forall fun n => ha.trans_le (hη0 n), fun a ha => ?_⟩
    filter_upwards [hunif (a / 2) (half_pos ha)] with n hn
    refine (csSup_le (insert_nonempty _ _) ?_).trans_lt (half_lt_self ha)
    rintro _ (rfl | ⟨θ, hθ, rfl⟩)
    · exact (half_pos ha).le
    · exact (hn θ hθ).le
  have hzex : ∀ n, ∃ zn : ι → ℝ,
      0 ≤ κ's n → zn ∈ mcUpper f (κ's n) ∧ ∀ i, |zn i - q.2.1 i| ≤ η n := by
    intro n
    by_cases hn : 0 ≤ κ's n
    · have hmem : q.2.1 ∈ mcUpper (fun κ θ => f κ θ + η n) (κ's n) :=
        ⟨hz.1, fun θ hθ => (hz.2 θ hθ).trans (by
          have := (abs_le.1 (hηbd n hn θ hθ)).1
          linarith)⟩
      rw [ex_16_7f_hint (hf.nonneg _ hn) (hfs _ hn) (hη0 n)] at hmem
      obtain ⟨-, z'', hz'', hle⟩ := hmem
      refine ⟨fun i => min (q.2.1 i) (z'' i), fun _ => ⟨⟨fun i => le_min (hz.1 i) (hz''.1 i),
        fun θ hθ => ?_⟩, fun i => ?_⟩⟩
      · exact (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (min_le_right _ _)
          (hθ.1 i)).trans (hz''.2 θ hθ)
      · have h1 : q.2.1 i ≤ z'' i + η n := hle i
        have h2 : q.2.1 i - η n ≤ min (q.2.1 i) (z'' i) :=
          le_min (by linarith [hη0 n]) (by linarith)
        have h3 := min_le_left (q.2.1 i) (z'' i)
        rw [abs_le]
        constructor <;> linarith [hη0 n]
    · exact ⟨q.2.1, fun h => absurd h hn⟩
  choose zs hzs using hzex
  refine ⟨fun n => (γs n, zs n, κ's n), ?_, ?_⟩
  · filter_upwards [hps, hκ's0] with n hn hn0
    refine ⟨fun i m => le_max_right _ _, ?_, (hzs n hn0).1⟩
    refine hΦ.disposal (κs n) (hκs n) (ps n).1 (ps n).2 hn _ _
      (fun m => ?_) (fun m => ?_) hn0 le_rfl
    · simp only [Finset.sum_apply, Pi.zero_apply, hγsdef]
      exact Finset.sum_nonneg fun i _ => le_max_right _ _
    have hpos := (hΦ.nonneg _ (hκs n) _ hn).1 m
    have hclose : |(ps n).1 m - (∑ i, q.1 i) m| ≤ δ n := by
      have := norm_le_pi_norm ((ps n).1 - ∑ i, q.1 i) m
      rwa [Pi.sub_apply, Real.norm_eq_abs] at this
    simp only [Finset.sum_apply, hγsdef] at hclose ⊢
    have h1 := mc_sum_posPart_le Finset.univ (a := fun i => q.1 i m) (fun i => hγ i m) (hδ0 n)
    have h2 := (abs_le.1 hclose).1
    exact h1.trans (max_le (by linarith) hpos)
  · refine hγs.prodMk_nhds (Tendsto.prodMk_nhds ?_ hκ'lim)
    refine tendsto_pi_nhds.2 fun i => ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (hκ's0.mono fun n hn => ?_) hηlim
    rw [Real.norm_eq_abs]
    exact (hzs n hn).2 i

/-! ### Exercise 16.7e, corrected: `T` maps `F_s` into `F_s` (Berge's maximum theorem) -/

/-- The **policy correspondence** of (4): the maximisers of the objective on the constraint
set. -/
def mcPolicy (W : ι → (Fin l → ℝ) → ℝ → ℝ)
    (Φ : (Fin p → ℝ) → Set ((Fin l → ℝ) × (Fin p → ℝ))) (f : (Fin p → ℝ) → (ι → ℝ) → ℝ)
    (κ : Fin p → ℝ) (θ : ι → ℝ) : Set ((ι → Fin l → ℝ) × (ι → ℝ) × (Fin p → ℝ)) :=
  {q ∈ mcConstraint Φ f κ | ∀ q' ∈ mcConstraint Φ f κ, mcObjective W θ q' ≤ mcObjective W θ q}

/-- A maximiser attains `Tf`. -/
theorem mcPolicy_value {W : ι → (Fin l → ℝ) → ℝ → ℝ} {f : (Fin p → ℝ) → (ι → ℝ) → ℝ}
    {κ : Fin p → ℝ} {θ : ι → ℝ} {q : (ι → Fin l → ℝ) × (ι → ℝ) × (Fin p → ℝ)}
    (hq : q ∈ mcPolicy W Φ f κ θ) : mcOperator W Φ f κ θ = mcObjective W θ q :=
  IsGreatest.csSup_eq ⟨⟨q, hq.1, rfl⟩, by rintro _ ⟨q', hq', rfl⟩; exact hq.2 q' hq'⟩

/-- The policy correspondence is nonempty for `f ∈ F` (Exercise 16.7d). -/
theorem mcPolicy_nonempty {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, IsAggregator (Ici (0 : Fin l → ℝ)) (W i) (β i)) (hΦ : ManyConsumersTech Φ)
    {f : (Fin p → ℝ) → (ι → ℝ) → ℝ} (hf : MCInF f) {κ : Fin p → ℝ} (hκ : 0 ≤ κ)
    (θ : ι → ℝ) : (mcPolicy W Φ f κ θ).Nonempty := by
  obtain ⟨q, hq, hmax, -⟩ := ex_16_7d_exists_max hW hΦ hf hκ θ
  exact ⟨q, hq, hmax⟩

/-- **Sequential continuity of `Tf`** for `f ∈ F` of support-function type: along
`(κₙ, θₙ) → (κ, θ)` in `ℝᵖ₊ × Δᴵ`, `Tf(κₙ, θₙ) → Tf(κ, θ)`. Lower bound from lower
hemicontinuity (`mcConstraint_lhc`), upper bound from upper hemicontinuity
(`mcConstraint_uhc`) along every subsequence. -/
theorem mcOperator_tendsto {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, IsAggregator (Ici (0 : Fin l → ℝ)) (W i) (β i)) (hΦ : ManyConsumersTech Φ)
    {f : (Fin p → ℝ) → (ι → ℝ) → ℝ} (hf : MCInF f) (hfs : mcSupportType f)
    {κs : ℕ → Fin p → ℝ} {θs : ℕ → ι → ℝ} {κ : Fin p → ℝ} {θ : ι → ℝ} (hκs : ∀ n, 0 ≤ κs n)
    (hκl : Tendsto κs atTop (𝓝 κ)) (hθl : Tendsto θs atTop (𝓝 θ)) :
    Tendsto (fun n => mcOperator W Φ f (κs n) (θs n)) atTop (𝓝 (mcOperator W Φ f κ θ)) := by
  have hκ : 0 ≤ κ := ge_of_tendsto' hκl hκs
  choose qm hqm using fun n => mcPolicy_nonempty hW hΦ hf (hκs n) (θs n)
  obtain ⟨q0, hq0⟩ := mcPolicy_nonempty hW hΦ hf hκ θ
  obtain ⟨qs, hqs, hqsl⟩ := mcConstraint_lhc hΦ hf hfs hκs hκl hq0.1
  have hlow : Tendsto (fun n => mcObjective W (θs n) (qs n)) atTop
      (𝓝 (mcOperator W Φ f κ θ)) := by
    rw [mcPolicy_value hq0]
    exact mcObjective_tendsto hW hθl hqsl (hqs.mono fun n hn => ⟨hn.1, hn.2.2.1⟩)
      ⟨hq0.1.1, hq0.1.2.2.1⟩
  have hle : ∀ᶠ n in atTop, mcObjective W (θs n) (qs n) ≤ mcOperator W Φ f (κs n) (θs n) :=
    hqs.mono fun n hn => by
      rw [mcPolicy_value (hqm n)]
      exact (hqm n).2 _ hn
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨q1, hq1, ms, hms, hq1l⟩ := mcConstraint_uhc hΦ hf (fun n => hκs (ns n))
    (hκl.comp hns) (qs := fun n => qm (ns n)) fun n => (hqm (ns n)).1
  refine ⟨ms, ?_⟩
  have hnm : Tendsto (fun n => ns (ms n)) atTop atTop := hns.comp hms.tendsto_atTop
  have hval : Tendsto (fun n => mcOperator W Φ f (κs (ns (ms n))) (θs (ns (ms n)))) atTop
      (𝓝 (mcObjective W θ q1)) := by
    have := mcObjective_tendsto hW (hθl.comp hnm) hq1l (Eventually.of_forall fun n =>
      ⟨(hqm (ns (ms n))).1.1, (hqm (ns (ms n))).1.2.2.1⟩) ⟨hq1.1, hq1.2.2.1⟩
    refine this.congr fun n => ?_
    exact (mcPolicy_value (hqm (ns (ms n)))).symm
  have hup : mcObjective W θ q1 ≤ mcOperator W Φ f κ θ := by
    rw [mcPolicy_value hq0]
    exact hq0.2 _ hq1
  have hdown : mcOperator W Φ f κ θ ≤ mcObjective W θ q1 :=
    le_of_tendsto_of_tendsto (hlow.comp hnm) hval (hnm.eventually hle)
  rwa [le_antisymm hup hdown] at hval

/-- **`Tf` is continuous on `ℝᵖ₊ × Δᴵ`** for `f ∈ F` of support-function type. -/
theorem mcOperator_continuousOn {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, IsAggregator (Ici (0 : Fin l → ℝ)) (W i) (β i)) (hΦ : ManyConsumersTech Φ)
    {f : (Fin p → ℝ) → (ι → ℝ) → ℝ} (hf : MCInF f) (hfs : mcSupportType f) :
    ContinuousOn (fun x : (Fin p → ℝ) × (ι → ℝ) => mcOperator W Φ f x.1 x.2)
      (Ici 0 ×ˢ mcSimplex ι) := by
  rw [continuousOn_iff_continuous_domRestrict, continuous_iff_seqContinuous]
  intro xs x hxs
  have hv : Tendsto (fun n => (xs n : (Fin p → ℝ) × (ι → ℝ))) atTop
      (𝓝 (x : (Fin p → ℝ) × (ι → ℝ))) := (continuous_subtype_val.tendsto x).comp hxs
  exact mcOperator_tendsto hW hΦ hf hfs (fun n => (xs n).2.1)
    ((continuous_fst.tendsto _).comp hv) ((continuous_snd.tendsto _).comp hv)

/-- **Exercise 16.7e, corrected**: `T` maps the closed subset `F_s` of `F` (functions of
support-function type) into itself. -/
theorem ex_16_7e {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, IsAggregator (Ici (0 : Fin l → ℝ)) (W i) (β i)) (hΦ : ManyConsumersTech Φ)
    {f : (Fin p → ℝ) → (ι → ℝ) → ℝ} (hf : MCInF f) (hfs : mcSupportType f) :
    MCInF (mcOperator W Φ f) ∧ mcSupportType (mcOperator W Φ f) := by
  obtain ⟨M, hM⟩ := hf.bdd
  exact ⟨⟨mcOperator_continuousOn hW hΦ hf hfs, mcOperator_bdd hW hΦ hM hf.nonneg,
    fun κ hκ θ hθ => mcOperator_nonneg hW hΦ hM hf.nonneg hκ hθ⟩,
    mcOperator_supportType hW hΦ hM hf.nonneg⟩

/-! ### Exercise 16.7g, corrected: upper hemicontinuity of the policy correspondence -/

/-- **Exercise 16.7g, upper hemicontinuity**: for `f ∈ F` of support-function type, maximisers
along `(κₙ, θₙ) → (κ, θ)` have a subsequence converging to a maximiser at `(κ, θ)`. -/
theorem ex_16_7g_uhc {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, IsAggregator (Ici (0 : Fin l → ℝ)) (W i) (β i)) (hΦ : ManyConsumersTech Φ)
    {f : (Fin p → ℝ) → (ι → ℝ) → ℝ} (hf : MCInF f) (hfs : mcSupportType f)
    {κs : ℕ → Fin p → ℝ} {θs : ℕ → ι → ℝ} {κ : Fin p → ℝ} {θ : ι → ℝ} (hκs : ∀ n, 0 ≤ κs n)
    (hκl : Tendsto κs atTop (𝓝 κ)) (hθl : Tendsto θs atTop (𝓝 θ))
    {qs : ℕ → (ι → Fin l → ℝ) × (ι → ℝ) × (Fin p → ℝ)}
    (hqs : ∀ n, qs n ∈ mcPolicy W Φ f (κs n) (θs n)) :
    ∃ q ∈ mcPolicy W Φ f κ θ, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (qs ∘ φ) atTop (𝓝 q) := by
  obtain ⟨M, hM⟩ := hf.bdd
  have hκ : 0 ≤ κ := ge_of_tendsto' hκl hκs
  obtain ⟨q, hq, φ, hφ, hql⟩ := mcConstraint_uhc hΦ hf hκs hκl fun n => (hqs n).1
  have hT := (mcOperator_tendsto hW hΦ hf hfs hκs hκl hθl).comp hφ.tendsto_atTop
  have hO := mcObjective_tendsto hW (hθl.comp hφ.tendsto_atTop) hql
    (Eventually.of_forall fun n => ⟨(hqs (φ n)).1.1, (hqs (φ n)).1.2.2.1⟩) ⟨hq.1, hq.2.2.1⟩
  have heq : mcOperator W Φ f κ θ = mcObjective W θ q :=
    tendsto_nhds_unique hT (hO.congr fun n => (mcPolicy_value (hqs (φ n))).symm)
  obtain ⟨q0, hq0⟩ := mcPolicy_nonempty hW hΦ hf hκ θ
  refine ⟨q, ⟨hq, fun q' hq' => ?_⟩, φ, hφ, hql⟩
  rw [← heq, mcPolicy_value hq0]
  exact hq0.2 q' hq'

/-! ### The continuous fixed point and the continuity of `v` -/

omit [Fintype ι] in
/-- With `βᵢ < 1` and finitely many consumers there is a common modulus `β ∈ [0, 1)`. -/
theorem mc_exists_beta [Finite ι] {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, IsAggregator (Ici (0 : Fin l → ℝ)) (W i) (β i)) :
    ∃ β0, (∀ i, β i ≤ β0) ∧ 0 ≤ β0 ∧ β0 < 1 := by
  have := Fintype.ofFinite ι
  by_cases hne : Nonempty ι
  · obtain ⟨i0⟩ := hne
    exact ⟨Finset.univ.sup' ⟨i0, Finset.mem_univ _⟩ β,
      fun i => Finset.le_sup' β (Finset.mem_univ i),
      (hW i0).beta_pos.le.trans (Finset.le_sup' β (Finset.mem_univ i0)),
      (Finset.sup'_lt_iff _).2 fun i _ => (hW i).beta_lt_one⟩
  · exact ⟨0, fun i => absurd ⟨i⟩ hne, le_rfl, zero_lt_one⟩

/-- **The solution of (4) is continuous** (Exercise 16.7f with 16.7e): the admissible fixed point
of `T` lies in `F`. The iterates `Tⁿ0` lie in `F_s` (`ex_16_7e`) and converge to it uniformly on
`ℝᵖ₊ × Δᴵ` (`|Tⁿ0 − v| ≤ βⁿ‖v‖`). -/
theorem ex_16_7e_fixed {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, ManyConsumersAggregator (W i) (β i)) (hΦ : ManyConsumersTech Φ) :
    ∃ v, MCInF v ∧ MCAdmissible v ∧
      ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, mcOperator W Φ v κ θ = v κ θ := by
  obtain ⟨β0, hβ0, hβ00, hβ1⟩ := mc_exists_beta fun i => (hW i).agg
  obtain ⟨v, hv, hTv⟩ := ex_16_7f_exists_fixed hW hΦ hβ0 hβ00 hβ1
  set F : ℕ → (Fin p → ℝ) → (ι → ℝ) → ℝ := fun n => (mcOperator W Φ)^[n] fun _ _ => 0 with hFdef
  have hFs : ∀ n, F (n + 1) = mcOperator W Φ (F n) := fun n =>
    Function.iterate_succ_apply' _ _ _
  have hF : ∀ n, MCInF (F n) ∧ MCAdmissible (F n) := by
    intro n
    induction n with
    | zero =>
      exact ⟨⟨continuousOn_const, ⟨0, fun _ _ _ _ => le_rfl⟩, fun _ _ _ _ => le_rfl⟩,
        ⟨⟨0, fun _ _ _ _ => le_rfl⟩, fun _ _ _ _ => le_rfl, fun _ _ _ _ ε hε =>
          ⟨0, zero_mem_mcUpper fun _ _ => le_rfl, by
            simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
            change (0 : ℝ) - ε < 0
            linarith⟩⟩⟩
    | succ n ih =>
      rw [hFs]
      exact ⟨(ex_16_7e (fun i => (hW i).agg) hΦ ih.1 ih.2.support).1,
        mcOperator_admissible (fun i => (hW i).agg) hΦ ih.2⟩
  obtain ⟨Mv, hMv⟩ := hv.bdd
  set a := max Mv 0 with ha
  have ha0 : 0 ≤ a := le_max_right _ _
  have hbound : ∀ n, ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, |F n κ θ - v κ θ| ≤ β0 ^ n * a := by
    intro n
    induction n with
    | zero =>
      intro κ hκ θ hθ
      rw [pow_zero, one_mul]
      change |0 - v κ θ| ≤ a
      rw [zero_sub, abs_neg, abs_of_nonneg (hv.nonneg κ hκ θ hθ)]
      exact (hMv κ hκ θ hθ).trans (le_max_left _ _)
    | succ n ih =>
      intro κ hκ θ hθ
      rw [hFs, ← hTv κ hκ θ hθ]
      have := ex_16_7f hW hΦ (hF n).2 hv (mul_nonneg (pow_nonneg hβ00 n) ha0) ih hβ0 κ hκ θ hθ
      calc _ ≤ β0 * (β0 ^ n * a) := this
        _ = β0 ^ (n + 1) * a := by ring
  have hunif : TendstoUniformlyOn (fun n (x : (Fin p → ℝ) × (ι → ℝ)) => F n x.1 x.2)
      (fun x => v x.1 x.2) atTop (Ici 0 ×ˢ mcSimplex ι) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hlim : Tendsto (fun n => β0 ^ n * a) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ00 hβ1).mul_const a
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn x hx
    rw [Real.dist_eq, abs_sub_comm]
    exact (hbound n x.1 hx.1 x.2 hx.2).trans_lt hn
  exact ⟨v, ⟨hunif.continuousOn (Frequently.of_forall fun n => (hF n).1.cont), hv.bdd,
    hv.nonneg⟩, hv, hTv⟩

/-- **The support function `v` of (2) is continuous** under (T8): it is the unique admissible
solution of (4) (`mc_support_unique_fixed_of_bound`), which is continuous (`ex_16_7e_fixed`).
So `v ∈ F_s`. -/
theorem mcSupport_inF {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, ManyConsumersAggregator (W i) (β i)) {u : ι → BddSeq (Fin l → ℝ) → ℝ}
    (hu : ∀ i, IsAggregatorFixedPoint (Ici 0) (W i) (u i)) (hΦ : ManyConsumersTech Φ)
    (hb : MCCapitalBound Φ) : MCInF (mcSupport Φ u) ∧ mcSupportType (mcSupport Φ u) := by
  obtain ⟨β0, hβ0, hβ00, hβ1⟩ := mc_exists_beta fun i => (hW i).agg
  obtain ⟨v, hvF, hvA, hTv⟩ := ex_16_7e_fixed (W := W) hW hΦ
  have heq := (mc_support_unique_fixed_of_bound hW hu hΦ hb hβ0 hβ00 hβ1).2 v hvA hTv
  have hS := mcSupport_admissible hu hΦ
  exact ⟨⟨hvF.cont.congr fun x hx => (heq x.1 hx.1 x.2 hx.2).symm, hS.bdd, hS.nonneg⟩,
    hS.support⟩

/-- **Exercise 16.7g for `v`** under (T8): the policy correspondence of (4) with `f = v` is
nonempty, convex-valued and upper hemicontinuous on `ℝᵖ₊ × Δᴵ`. -/
theorem ex_16_7g_support {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, ManyConsumersAggregator (W i) (β i)) {u : ι → BddSeq (Fin l → ℝ) → ℝ}
    (hu : ∀ i, IsAggregatorFixedPoint (Ici 0) (W i) (u i)) (hΦ : ManyConsumersTech Φ)
    (hb : MCCapitalBound Φ) :
    (∀ κ, 0 ≤ κ → ∀ θ, (mcPolicy W Φ (mcSupport Φ u) κ θ).Nonempty) ∧
    (∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, Convex ℝ (mcPolicy W Φ (mcSupport Φ u) κ θ)) ∧
    ∀ κs : ℕ → Fin p → ℝ, ∀ θs : ℕ → ι → ℝ, ∀ κ θ, (∀ n, 0 ≤ κs n) →
      Tendsto κs atTop (𝓝 κ) → Tendsto θs atTop (𝓝 θ) →
      ∀ qs : ℕ → (ι → Fin l → ℝ) × (ι → ℝ) × (Fin p → ℝ),
        (∀ n, qs n ∈ mcPolicy W Φ (mcSupport Φ u) (κs n) (θs n)) →
        ∃ q ∈ mcPolicy W Φ (mcSupport Φ u) κ θ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
          Tendsto (qs ∘ φ) atTop (𝓝 q) := by
  obtain ⟨hF, hFs⟩ := mcSupport_inF hW hu hΦ hb
  exact ⟨fun κ hκ θ => mcPolicy_nonempty (fun i => (hW i).agg) hΦ hF hκ θ,
    fun κ hκ θ hθ => ex_16_7g hW hu hΦ hκ hθ,
    fun κs θs κ θ hκs hκl hθl qs hqs => ex_16_7g_uhc (fun i => (hW i).agg) hΦ hF hFs hκs hκl hθl
      hqs⟩

/-! ### Pareto optima as competitive equilibria -/

omit [Fintype ι] in
/-- A supporting price `φ` of a Pareto optimum (from `mc_welfare`) is nonnegative on `C`: by
(W4), `uᵢ(cᵢ + x) ≥ uᵢ(cᵢ)`, so `φ(cᵢ + x) ≥ φ(cᵢ)`. -/
theorem mc_supporting_nonneg [Nonempty ι] {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, ManyConsumersAggregator (W i) (β i)) {u : ι → BddSeq (Fin l → ℝ) → ℝ}
    (hu : ∀ i, IsAggregatorFixedPoint (Ici 0) (W i) (u i)) {kh : Fin p → ℝ}
    {c : ι → BddSeq (Fin l → ℝ)} {y : Unit → BddSeq (Fin l → ℝ)}
    (hc : ∀ i, c i ∈ mcCons l) {φ : StrongDual ℝ (BddSeq (Fin l → ℝ))}
    (hφ : SupportsAllocation (fun _ : ι => mcCons l) u (fun _ : Unit => mcProdSet Φ kh) c y φ)
    {x : BddSeq (Fin l → ℝ)} (hx : x ∈ mcCons l) : 0 ≤ φ x := by
  obtain ⟨i0⟩ := ‹Nonempty ι›
  have hcx : c i0 + x ∈ mcCons l := fun t => by
    change (0 : Fin l → ℝ) ≤ (c i0 + x) t
    rw [mc_add_apply]
    exact add_nonneg (hc i0 t) (hx t)
  have hle := hφ.1 i0 _ hcx (mc_utility_mono (hW i0) (hu i0) (hc i0) hcx fun t => by
    rw [mc_add_apply]
    exact le_add_of_nonneg_right (hx t))
  rw [map_add] at hle
  linarith

/-- **Pareto optima are competitive equilibria when every consumer's bundle has positive
value** (the Remark after Theorem 15.4 with the cheaper point `0 ∈ C`). Under the hypotheses of
`mc_welfare`, a Pareto optimum supported by `φ` with `φ(cᵢ) > 0` for all `i` is a competitive
equilibrium. -/
theorem mc_competitiveEq_of_pos {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, ManyConsumersAggregator (W i) (β i)) {u : ι → BddSeq (Fin l → ℝ) → ℝ}
    (hu : ∀ i, IsAggregatorFixedPoint (Ici 0) (W i) (u i)) (hΦ : ManyConsumersTech Φ)
    {kh : Fin p → ℝ} (hk : kh ∈ interior (mcM Φ)) {c : ι → BddSeq (Fin l → ℝ)}
    {y : Unit → BddSeq (Fin l → ℝ)}
    (hPO : ParetoOptimal (fun _ : ι => mcCons l) u (fun _ : Unit => mcProdSet Φ kh) c y)
    {φ : StrongDual ℝ (BddSeq (Fin l → ℝ))}
    (hφ : SupportsAllocation (fun _ : ι => mcCons l) u (fun _ : Unit => mcProdSet Φ kh) c y φ)
    (hpos : ∀ i, 0 < φ (c i)) :
    CompetitiveEq (fun _ : ι => mcCons l) u (fun _ : Unit => mcProdSet Φ kh) c y φ := by
  obtain ⟨h1, -, h3, -⟩ := mc_assumptions hW hu hΦ hk
  have h0 : (0 : BddSeq (Fin l → ℝ)) ∈ mcCons l := fun t => by
    change (0 : Fin l → ℝ) ≤ (0 : BddSeq (Fin l → ℝ)) t
    rw [lp.coeFn_zero]
    rfl
  exact remark_cheaper_point h1 h3 hPO.1 hφ fun i => ⟨0, h0, by rw [map_zero]; exact hpos i⟩

end StokeyLucasPrescott.EquilibriumApplications
