/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveDecisionProcesses.Correspondences
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# Maximizers over finite action sets and unique maximizers

Sargent and Stachurski, *Dynamic Programming*, Volume 2, the proof of Lemma 7.1.1 (p. 216) and
the last claim of Theorem A.3.3 (p. 351), as used in Lemma 7.1.2.

* `exists_measurable_argmax`: with finitely many actions, measurable sections `{x | a ∈ Γ(x)}` and
  measurable `x ↦ q(x, a)`, the first maximizer in an enumeration `a₁, …, aₙ` of `A` is a
  measurable selection attaining `max_{a ∈ Γ(x)} q(x, a)`. This is the construction in the proof
  of Lemma 7.1.1.
* `HasContinuousUniqueMax Γ`: the last claim of Theorem A.3.3 (Berge): a selection that is the
  unique maximizer of a function continuous on `G = graph Γ` is continuous. It is proved for the
  interval correspondences `[g(x), h(x)]` of Exercise A.3.1 on any sequential state space
  (`hasContinuousUniqueMax_Icc`): along `xₙ → x`, every subsequence of the maximizers has a further
  subsequence converging to a maximizer at `x`, which must be the unique one.
-/

open Set Function Filter Topology

namespace SargentStachurski.RecursiveDecisionProcesses

variable {X A : Type*}

/-- The construction in the proof of **Lemma 7.1.1** (p. 216): with `A` finite, `{x | a ∈ Γ(x)}`
and `x ↦ q(x, a)` measurable for each `a`, and `Γ` nonempty, the first maximizer in an
enumeration of `A` is a measurable selection attaining `max_{a ∈ Γ(x)} q(x, a)`. -/
theorem exists_measurable_argmax [MeasurableSpace X] [MeasurableSpace A] [Finite A]
    {Γ : X → Set A} (hΓ : ∀ a, MeasurableSet {x | a ∈ Γ x}) (hne : ∀ x, (Γ x).Nonempty)
    {q : X → A → ℝ} (hq : ∀ a, Measurable fun x => q x a) :
    ∃ σ : X → A, Measurable σ ∧ (∀ x, σ x ∈ Γ x) ∧ ∀ x, ∀ a ∈ Γ x, q x a ≤ q x (σ x) := by
  classical
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin A
  -- the indices of the maximizers
  let M : X → Finset (Fin n) := fun x => Finset.univ.filter fun i =>
    e.symm i ∈ Γ x ∧ ∀ j, e.symm j ∈ Γ x → q x (e.symm j) ≤ q x (e.symm i)
  have hM : ∀ x, (M x).Nonempty := fun x => by
    obtain ⟨a, ha⟩ := hne x
    have hF : (Finset.univ.filter fun i : Fin n => e.symm i ∈ Γ x).Nonempty :=
      ⟨e a, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simpa using ha⟩⟩
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image _ (fun i => q x (e.symm i)) hF
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hi).2,
      fun j hj => hmax j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)⟩⟩
  let idx : X → Fin n := fun x => (M x).min' (hM x)
  have hidx : ∀ x, idx x ∈ M x := fun x => Finset.min'_mem _ _
  have hmemM : ∀ i, MeasurableSet {x | i ∈ M x} := fun i => by
    have heq : {x | i ∈ M x} = {x | e.symm i ∈ Γ x} ∩
        ⋂ j, ({x | e.symm j ∈ Γ x}ᶜ ∪ {x | q x (e.symm j) ≤ q x (e.symm i)}) := by
      ext x
      simp only [M, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
        Set.mem_inter_iff, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun j => ?_⟩
        by_cases hj : e.symm j ∈ Γ x
        · exact Or.inr (h2 j hj)
        · exact Or.inl hj
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun j hj => (h2 j).resolve_left (not_not.2 hj)⟩
    rw [heq]
    exact (hΓ _).inter (MeasurableSet.iInter fun j =>
      (hΓ _).compl.union (measurableSet_le (hq _) (hq _)))
  have hidxm : Measurable idx := by
    refine measurable_to_countable' fun i => ?_
    have heq : idx ⁻¹' {i} = {x | i ∈ M x} ∩ ⋂ j, ({x | j ∈ M x}ᶜ ∪ {_x | i ≤ j}) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq]
      constructor
      · rintro rfl
        refine ⟨hidx x, fun j => ?_⟩
        by_cases hj : j ∈ M x
        · exact Or.inr (Finset.min'_le _ j hj)
        · exact Or.inl hj
      · rintro ⟨hi, hmin⟩
        refine le_antisymm (Finset.min'_le _ i hi) (Finset.le_min' _ (hM x) i fun j hj => ?_)
        exact (hmin j).resolve_left (not_not.2 hj)
    rw [heq]
    refine (hmemM i).inter (MeasurableSet.iInter fun j => (hmemM j).compl.union ?_)
    by_cases h' : i ≤ j
    · simp [h']
    · simp [h']
  refine ⟨fun x => e.symm (idx x), (measurable_of_countable _).comp hidxm,
    fun x => (Finset.mem_filter.1 (hidx x)).2.1, fun x a ha => ?_⟩
  have := (Finset.mem_filter.1 (hidx x)).2.2 (e a) (by simpa using ha)
  simpa using this

/-- The last claim of **Theorem A.3.3** (p. 351) for `Γ`: a feasible selection `σ` that is the
unique maximizer of `q(x, ·)` over `Γ(x)`, for `q` continuous on `G = graph Γ`, is continuous. -/
def HasContinuousUniqueMax [TopologicalSpace X] [TopologicalSpace A] (Γ : X → Set A) : Prop :=
  ∀ q : X × A → ℝ, ContinuousOn q {p | p.2 ∈ Γ p.1} → ∀ σ : X → A, (∀ x, σ x ∈ Γ x) →
    (∀ x, ∀ a ∈ Γ x, q (x, a) ≤ q (x, σ x)) →
    (∀ x, ∀ a ∈ Γ x, q (x, σ x) ≤ q (x, a) → a = σ x) → Continuous σ

/-- The last claim of **Theorem A.3.3** for the interval correspondences of Exercise A.3.1: if
`g ≤ h` are continuous, a unique maximizer over `[g(x), h(x)]` of a function continuous on the
graph is continuous in `x`. -/
theorem hasContinuousUniqueMax_Icc [TopologicalSpace X] [SequentialSpace X] {g h : X → ℝ}
    (hg : Continuous g) (hh : Continuous h) (hgh : ∀ x, g x ≤ h x) :
    HasContinuousUniqueMax fun x => Icc (g x) (h x) := by
  intro q hq σ hσ hmax huniq
  refine continuous_iff_seqContinuous.2 fun xs x hx => ?_
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  have hx' : Tendsto (xs ∘ ns) atTop (𝓝 x) := hx.comp hns
  obtain ⟨φ, hφ, c, hc, hcφ⟩ := exists_subseq_Icc hg hh hx' (ys := fun n => σ (xs (ns n)))
    fun n => hσ (xs (ns n))
  refine ⟨φ, ?_⟩
  have hxφ : Tendsto (xs ∘ ns ∘ φ) atTop (𝓝 x) := hx'.comp hφ.tendsto_atTop
  -- the limit `c` maximizes `q(x, ·)` over `[g(x), h(x)]`
  have hcmax : ∀ b ∈ Icc (g x) (h x), q (x, b) ≤ q (x, c) := by
    intro b hb
    let bs : ℕ → ℝ := fun k => max (g (xs (ns (φ k)))) (min b (h (xs (ns (φ k)))))
    have hbs : Tendsto bs atTop (𝓝 b) := by
      have := ((hg.tendsto x).comp hxφ).max
        ((tendsto_const_nhds (x := b)).min ((hh.tendsto x).comp hxφ))
      rwa [clamp_eq hb] at this
    have hG1 : Tendsto (fun k => ((xs ∘ ns ∘ φ) k, bs k)) atTop
        (𝓝[{p : X × ℝ | p.2 ∈ Icc (g p.1) (h p.1)}] (x, b)) :=
      tendsto_nhdsWithin_iff.2 ⟨hxφ.prodMk_nhds hbs, Eventually.of_forall fun k =>
        clamp_mem (hgh _) b⟩
    have hG2 : Tendsto (fun k => ((xs ∘ ns ∘ φ) k, σ (xs (ns (φ k))))) atTop
        (𝓝[{p : X × ℝ | p.2 ∈ Icc (g p.1) (h p.1)}] (x, c)) :=
      tendsto_nhdsWithin_iff.2 ⟨hxφ.prodMk_nhds hcφ, Eventually.of_forall fun k => hσ _⟩
    exact le_of_tendsto_of_tendsto' ((hq (x, b) hb).tendsto.comp hG1)
      ((hq (x, c) hc).tendsto.comp hG2) fun k => hmax _ _ (clamp_mem (hgh _) b)
  have hcx : c = σ x := huniq x c hc (hcmax _ (hσ x))
  rw [← hcx]
  exact hcφ

end SargentStachurski.RecursiveDecisionProcesses
