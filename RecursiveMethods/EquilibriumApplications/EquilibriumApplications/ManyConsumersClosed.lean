/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.ManyConsumers

/-!
# Exercise 16.7a, corrected: the production set with unbounded capital paths is closed

SLP §16.7, p. 497.

* `ManyConsumersTech.isCompact_image`, `ManyConsumersTech.isClosed_graph`: by (T1)–(T2), `Φ` maps
  compact sets of `ℝᵖ₊` to compact sets and has a closed graph.
* `mcReach`, `mcReach_spec`: the capital stocks reachable from `k̂` at date `t` form a compact
  subset of `ℝᵖ₊`.
* `ex_16_7a_closed`: `Y′(k̂)` (capital paths in `(ℝᵖ₊)^∞`, not required to be bounded) is closed in
  the sup norm.
* `ex_16_7a_unb`: `Y′(k̂)` is convex, satisfies Assumption 15.6, and has an interior point when
  `k̂ ∈ int M`.

**Correction.** Exercise 16.7a's "`Y(k̂)` is closed" is false for the book's `Y(k̂)`
(`ex_16_7a_counterexample`); it holds for `Y′(k̂)`, fix (i) of the NOTE. Fix (ii), a bound on
capital (T8), is `MCCapitalBound` in `ManyConsumersCapital`; under it `Y′(k̂) = Y(k̂)`.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open Filter Topology Set

variable {l p : ℕ} {Φ : (Fin p → ℝ) → Set ((Fin l → ℝ) × (Fin p → ℝ))}

/-- The image `⋃_{κ ∈ K} Φ(κ)` of a compact `K ⊆ ℝᵖ₊` is compact ((T1) upper hemicontinuity and
(T2) compact values). -/
theorem ManyConsumersTech.isCompact_image (hΦ : ManyConsumersTech Φ) {K : Set (Fin p → ℝ)}
    (hK : IsCompact K) (hK0 : K ⊆ Ici 0) : IsCompact {q | ∃ κ ∈ K, q ∈ Φ κ} := by
  refine IsSeqCompact.isCompact fun qs hqs => ?_
  choose κs hκs hqκ using hqs
  obtain ⟨κ, hκ, φ, hφ, hlim⟩ := hK.tendsto_subseq hκs
  obtain ⟨q, hq, ψ, hψ, hlim'⟩ := hΦ.uhc (κs ∘ φ) κ (fun n => hK0 (hκs (φ n))) hlim
    (qs ∘ φ) fun n => hqκ (φ n)
  exact ⟨q, ⟨κ, hκ, hq⟩, φ ∘ ψ, hφ.comp hψ, hlim'⟩

/-- The graph `{(κ, q) : κ ≥ 0, q ∈ Φ(κ)}` is closed (from (T1) upper hemicontinuity). -/
theorem ManyConsumersTech.isClosed_graph (hΦ : ManyConsumersTech Φ) :
    IsClosed {x : (Fin p → ℝ) × ((Fin l → ℝ) × (Fin p → ℝ)) | 0 ≤ x.1 ∧ x.2 ∈ Φ x.1} := by
  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨xs, hxs, hlim⟩ := mem_closure_iff_seq_limit.1 hx
  have h1 : Tendsto (fun n => (xs n).1) atTop (𝓝 x.1) := (continuous_fst.tendsto _).comp hlim
  have h2 : Tendsto (fun n => (xs n).2) atTop (𝓝 x.2) := (continuous_snd.tendsto _).comp hlim
  have hx0 : 0 ≤ x.1 := ge_of_tendsto' h1 fun n => (hxs n).1
  obtain ⟨q, hq, φ, hφ, hlimq⟩ := hΦ.uhc (fun n => (xs n).1) x.1 (fun n => (hxs n).1) h1
    (fun n => (xs n).2) fun n => (hxs n).2
  have e : q = x.2 := tendsto_nhds_unique hlimq (h2.comp hφ.tendsto_atTop)
  exact ⟨hx0, e ▸ hq⟩

/-- The capital stocks reachable from `k̂` at date `t`. -/
def mcReach (Φ : (Fin p → ℝ) → Set ((Fin l → ℝ) × (Fin p → ℝ))) (kh : Fin p → ℝ) :
    ℕ → Set (Fin p → ℝ)
  | 0 => {kh}
  | t + 1 => {y | ∃ κ ∈ mcReach Φ kh t, ∃ γ, (γ, y) ∈ Φ κ}

/-- Each reachable set is compact and nonnegative (induction on `t`, using
`ManyConsumersTech.isCompact_image`). -/
theorem mcReach_spec (hΦ : ManyConsumersTech Φ) {kh : Fin p → ℝ} (hkh : 0 ≤ kh) (t : ℕ) :
    IsCompact (mcReach Φ kh t) ∧ mcReach Φ kh t ⊆ Ici 0 := by
  induction t with
  | zero =>
    refine ⟨isCompact_singleton, fun κ hκ => ?_⟩
    rw [mem_singleton_iff.1 hκ]
    exact hkh
  | succ t ih =>
    have e : mcReach Φ kh (t + 1) = Prod.snd '' {q | ∃ κ ∈ mcReach Φ kh t, q ∈ Φ κ} := by
      ext y
      constructor
      · rintro ⟨κ, hκ, γ, hq⟩
        exact ⟨(γ, y), ⟨κ, hκ, hq⟩, rfl⟩
      · rintro ⟨q, ⟨κ, hκ, hq⟩, rfl⟩
        exact ⟨κ, hκ, q.1, hq⟩
    refine ⟨?_, ?_⟩
    · rw [e]
      exact (hΦ.isCompact_image ih.1 ih.2).image continuous_snd
    · rintro y ⟨κ, hκ, γ, hq⟩
      exact (hΦ.nonneg κ (ih.2 hκ) _ hq).2

/-- **Exercise 16.7a, closedness, corrected** (fix (i) of the NOTE): with unbounded capital paths
allowed, `Y′(k̂)` is closed in the sup norm. Feasible paths stay in the compact reachable sets, so a
subsequence of the paths converges coordinatewise (Tychonoff), and the closed graph of `Φ` passes
the constraints to the limit. -/
theorem ex_16_7a_closed (hΦ : ManyConsumersTech Φ) {kh : Fin p → ℝ} (hkh : 0 ≤ kh) :
    IsClosed (mcProdSetUnb Φ kh) := by
  have hspec := mcReach_spec hΦ hkh
  have hpath : ∀ k : ℕ → Fin p → ℝ, k 0 = kh → (∀ t, ∃ γ, (γ, k (t + 1)) ∈ Φ (k t)) →
      ∀ t, k t ∈ mcReach Φ kh t := by
    intro k hk0 hk t
    induction t with
    | zero => rw [hk0]; exact mem_singleton _
    | succ t ih =>
      obtain ⟨γ, hγ⟩ := hk t
      exact ⟨k t, ih, γ, hγ⟩
  refine isClosed_of_closure_subset fun c hc => ?_
  obtain ⟨cs, hcs, hlim⟩ := mem_closure_iff_seq_limit.1 hc
  choose hcs0 ks hks0 hksk hks using hcs
  have hmem : ∀ n, ks n ∈ Set.pi univ (mcReach Φ kh) := fun n t _ =>
    hpath (ks n) (hksk n) (fun t => ⟨_, hks n t⟩) t
  obtain ⟨k, hk, φ, hφ, hlimk⟩ :=
    (isCompact_univ_pi fun t => (hspec t).1).tendsto_subseq hmem
  have hkt : ∀ t, Tendsto (fun n => ks (φ n) t) atTop (𝓝 (k t)) := fun t =>
    ((continuous_apply t).tendsto _).comp hlimk
  have hct : ∀ t, Tendsto (fun n => cs (φ n) t) atTop (𝓝 (c t)) := fun t =>
    ((continuous_seq_coord t).tendsto _).comp (hlim.comp hφ.tendsto_atTop)
  refine ⟨fun t => ge_of_tendsto' (hct t) fun n => hcs0 (φ n) t, k,
    fun t => (hspec t).2 (hk t (mem_univ t)), mem_singleton_iff.1 (hk 0 (mem_univ 0)),
    fun t => ?_⟩
  have hG := hΦ.isClosed_graph.mem_of_tendsto
    ((hkt t).prodMk_nhds ((hct t).prodMk_nhds (hkt (t + 1))))
    (Eventually.of_forall fun n => ⟨hks0 (φ n) t, hks (φ n) t⟩)
  exact hG.2

/-- **Exercise 16.7a, corrected, the other properties**: `Y′(k̂)` is convex (T5), satisfies
Assumption 15.6 (T3), contains `Y(k̂)`, and so has an interior point when `k̂ ∈ int M`. -/
theorem ex_16_7a_unb (hΦ : ManyConsumersTech Φ) (kh : Fin p → ℝ) :
    Convex ℝ (mcProdSetUnb Φ kh) ∧ SeqTruncClosed (mcProdSetUnb Φ kh) ∧
      (kh ∈ interior (mcM Φ) → (interior (mcProdSetUnb Φ kh)).Nonempty) := by
  refine ⟨?_, ?_, fun hk => (ex_16_7a_interior hΦ hk).mono
    (interior_mono (mcProdSet_subset_unb kh))⟩
  · rintro c ⟨hc0, k, hk0, hkk, hk⟩ c' ⟨hc0', k', hk0', hkk', hk'⟩ a b ha hb hab
    obtain rfl : b = 1 - a := by linarith
    refine ⟨fun t => ?_, a • k + (1 - a) • k', fun t => ?_, ?_, fun t => ?_⟩
    · rw [seq_coord_combo]
      exact add_nonneg (smul_nonneg ha (hc0 t)) (smul_nonneg hb (hc0' t))
    · exact add_nonneg (smul_nonneg ha (hk0 t)) (smul_nonneg hb (hk0' t))
    · simp only [Pi.add_apply, Pi.smul_apply, hkk, hkk']
      exact Convex.combo_self hab kh
    · rw [seq_coord_combo]
      have := hΦ.graph_convex (k t) (k' t) (hk0 t) (hk0' t) _ (hk t) _ (hk' t) a ha
        (by linarith)
      simpa only [Prod.smul_mk, Prod.mk_add_mk, Pi.add_apply, Pi.smul_apply] using this
  · rintro c ⟨hc0, k, hk0, hkk, hk⟩
    refine Eventually.of_forall fun T => ⟨fun t => ?_, k, hk0, hkk, fun t => ?_⟩
    · rw [seqTrunc_apply]
      split_ifs
      exacts [hc0 t, le_rfl]
    · rw [seqTrunc_apply]
      split_ifs
      · exact hk t
      · exact hΦ.disposal _ (hk0 t) _ _ (hk t) 0 _ le_rfl (hc0 t)
          (hΦ.nonneg _ (hk0 t) _ (hk t)).2 le_rfl

end StokeyLucasPrescott.EquilibriumApplications
