/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DynamicGames.RGMaximal
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Compactness: Proposition 21.1.2, Lemma 21.1.4, Exercises 21.1–21.2

Miao, Proposition 21.1.2 (p. 745), Lemma 21.1.4 (p. 746) and Exercises 21.1–21.2 (p. 771).

* `rg_mem_B_iff_punish`: when every coordinate `xᵢ` attains its minimum `pᵢ` on `W`, the
  continuation values off the equilibrium action can be taken to be the worst punishments:
  `v ∈ B(W)` iff `v = (1 − δ) u(a) + δ w₀` with `w₀ ∈ W` and
  `(1 − δ) uᵢ(a'ᵢ, a₋ᵢ) + δ min_W xᵢ ≤ vᵢ` for all `i, a'ᵢ`. This is the Cronshaw–Luenberger form
  of `B` (p. 747) and the key to compactness for infinite action sets.
* `ex_21_2`: with compact action sets and continuous payoffs, `B(W)` is compact for compact `W`;
  `lemma_21_1_4` is the finite case.
* `ex_21_1`: with compact action sets and continuous payoffs, `V` is compact;
  `proposition_21_1_2` is the finite case. The proof is the book's second proof
  (`cl V ⊆ B(cl V)`, then Lemma 21.1.2), with the compactness of `B(cl V)` replacing the
  extraction of a convergent subsequence of admissible pairs.
-/

namespace Miao.DynamicGames

variable {ι : Type*} {A : ι → Type*}

/-- Admissibility with the worst punishments (Miao, p. 747, the operator of Cronshaw and
Luenberger): if `pᵢ ∈ W` minimises the `i`-th coordinate on `W`, then `v ∈ B(W)` iff
`v = (1 − δ) u(a) + δ w₀` for some `a` and `w₀ ∈ W` with
`(1 − δ) uᵢ(a'ᵢ, a₋ᵢ) + δ (pᵢ)ᵢ ≤ (1 − δ) uᵢ(a) + δ (w₀)ᵢ` for all `i, a'ᵢ`. -/
theorem rg_mem_B_iff_punish {δ : ℝ} {u : rg_Prof A → ι → ℝ} (hδ0 : 0 ≤ δ) {W : Set (ι → ℝ)}
    {p : ι → ι → ℝ} (hp : ∀ i, p i ∈ W ∧ ∀ x ∈ W, p i i ≤ x i) {v : ι → ℝ} :
    v ∈ rg_B δ u W ↔ ∃ a, ∃ w0 ∈ W, (v = fun j => (1 - δ) * u a j + δ * w0 j) ∧
      ∀ (i : ι) (x : A i),
        (1 - δ) * u (rg_upd a i x) i + δ * p i i ≤ (1 - δ) * u a i + δ * w0 i := by
  constructor
  · rintro ⟨a, w, ⟨hw, hic⟩, rfl⟩
    refine ⟨a, w a, hw a, rfl, fun i x => le_trans ?_ (hic i x)⟩
    have := mul_le_mul_of_nonneg_left ((hp i).2 _ (hw (rg_upd a i x))) hδ0
    linarith
  · rintro ⟨a, w0, hw0, rfl, hic⟩
    classical
    let w : rg_Prof A → ι → ℝ := fun a' =>
      if a' = a then w0 else if h : ∃ k, ∃ y : A k, a' = rg_upd a k y then p h.choose else w0
    have hwa : w a = w0 := by simp [w]
    refine ⟨a, w, ⟨fun a' => ?_, fun i x => ?_⟩, by rw [hwa]⟩
    · simp only [w]
      split_ifs
      · exact hw0
      · exact (hp _).1
      · exact hw0
    · rw [hwa]
      by_cases hx : rg_upd a i x = a
      · rw [hx, hwa]
      · have hex : ∃ k, ∃ y : A k, rg_upd a i x = rg_upd a k y := ⟨i, x, rfl⟩
        have hwv : w (rg_upd a i x) = p hex.choose := by
          simp only [w]
          split_ifs
          rfl
        obtain ⟨y, hy⟩ := hex.choose_spec
        have hji : hex.choose = i := rg_upd_player_eq a x y hy hx
        rw [hwv, hji]
        exact hic i x

/-- **Exercise 21.2** (Miao, p. 771; Lemma 21.1.4 for compact action sets). With compact action
sets, continuous payoffs and `δ ≥ 0`, `B(W)` is compact whenever `W` is compact. -/
theorem ex_21_2 [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)] {δ : ℝ}
    {u : rg_Prof A → ι → ℝ} (hu : ∀ j, Continuous fun a => u a j) (hδ0 : 0 ≤ δ)
    {W : Set (ι → ℝ)} (hW : IsCompact W) : IsCompact (rg_B δ u W) := by
  rcases W.eq_empty_or_nonempty with rfl | hne
  · convert isCompact_empty
    ext v
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨a, w, ⟨hw, -⟩, -⟩
    exact hw a
  have hmin : ∀ i, ∃ x ∈ W, IsMinOn (fun y : ι → ℝ => y i) W x := fun i =>
    hW.exists_isMinOn hne (continuous_apply i).continuousOn
  choose p hpW hpmin using hmin
  have hp : ∀ i, p i ∈ W ∧ ∀ x ∈ W, p i i ≤ x i := fun i => ⟨hpW i, fun x hx => hpmin i hx⟩
  classical
  set S : Set (rg_Prof A × (ι → ℝ)) := {q | q.2 ∈ W} ∩ ⋂ (i : ι), ⋂ (x : A i),
    {q | (1 - δ) * u (rg_upd q.1 i x) i + δ * p i i ≤ (1 - δ) * u q.1 i + δ * q.2 i} with hS
  have hupd : ∀ (i : ι) (x : A i),
      Continuous fun q : rg_Prof A × (ι → ℝ) => u (rg_upd q.1 i x) i := by
    intro i x
    have : (fun q : rg_Prof A × (ι → ℝ) => rg_upd q.1 i x) =
        fun q => Function.update q.1 i x := by
      funext q
      rw [rg_upd_eq]
    exact (hu i).comp (this ▸ continuous_fst.update i continuous_const)
  have hSc : IsClosed S := by
    refine (hW.isClosed.preimage continuous_snd).inter
      (isClosed_iInter fun i => isClosed_iInter fun x => isClosed_le ?_ ?_)
    · exact (continuous_const.mul (hupd i x)).add continuous_const
    · exact (continuous_const.mul ((hu i).comp continuous_fst)).add
        (continuous_const.mul ((continuous_apply i).comp continuous_snd))
  have hSk : IsCompact S :=
    (isCompact_univ.prod hW).of_isClosed_subset hSc fun q hq => ⟨trivial, hq.1⟩
  have himg : rg_B δ u W = (fun q : rg_Prof A × (ι → ℝ) =>
      fun j => (1 - δ) * u q.1 j + δ * q.2 j) '' S := by
    ext v
    rw [rg_mem_B_iff_punish hδ0 hp]
    constructor
    · rintro ⟨a, w0, hw0, rfl, hic⟩
      refine ⟨(a, w0), ⟨hw0, ?_⟩, rfl⟩
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      exact hic
    · rintro ⟨⟨a, w0⟩, ⟨hw0, hic⟩, rfl⟩
      simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hic
      exact ⟨a, w0, hw0, rfl, hic⟩
  rw [himg]
  refine hSk.image (continuous_pi fun j => ?_)
  exact (continuous_const.mul ((hu j).comp continuous_fst)).add
    (continuous_const.mul ((continuous_apply j).comp continuous_snd))

/-- **Lemma 21.1.4** (Compactness, Miao, p. 746): with finitely many players and finite action
sets, `B(W)` is compact if `W` is compact. -/
theorem lemma_21_1_4 [Finite ι] [∀ i, Finite (A i)] {δ : ℝ} {u : rg_Prof A → ι → ℝ}
    (hδ0 : 0 ≤ δ) {W : Set (ι → ℝ)} (hW : IsCompact W) : IsCompact (rg_B δ u W) := by
  let _ : ∀ i, TopologicalSpace (A i) := fun _ => ⊥
  have : ∀ i, DiscreteTopology (A i) := fun _ => ⟨rfl⟩
  exact ex_21_2 (fun _ => continuous_of_discreteTopology) hδ0 hW

/-- `[−M, M]ⁿ` is compact. -/
theorem rg_box_isCompact (M : ℝ) : IsCompact (rg_box ι M) :=
  isCompact_univ_pi fun _ => isCompact_Icc

/-- **Exercise 21.1** (Miao, p. 771; Proposition 21.1.2 for compact action sets). With compact
action sets, continuous bounded payoffs and `0 ≤ δ < 1`, the SPE payoff set `V` is compact. -/
theorem ex_21_1 [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)] {δ M : ℝ}
    {u : rg_Prof A → ι → ℝ} (hu : ∀ j, Continuous fun a => u a j) (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) : IsCompact (rg_V δ u) := by
  have hVbox : rg_V δ u ⊆ rg_box ι M := fun v hv => rg_mem_box.2 (rg_V_bdd hM hδ0 hδ1 v hv)
  have hcl : closure (rg_V δ u) ⊆ rg_box ι M := closure_minimal hVbox (rg_box_isClosed M)
  have hclc : IsCompact (closure (rg_V δ u)) :=
    (rg_box_isCompact M).of_isClosed_subset isClosed_closure hcl
  have hB := ex_21_2 hu hδ0 hclc
  have h1 : rg_V δ u ⊆ rg_B δ u (closure (rg_V δ u)) :=
    (theorem_21_1_1 hM hδ0 hδ1).subset.trans (lemma_21_1_3 δ u subset_closure)
  have h2 : closure (rg_V δ u) ⊆ rg_B δ u (closure (rg_V δ u)) := closure_minimal h1 hB.isClosed
  have h3 : rg_B δ u (closure (rg_V δ u)) ⊆ rg_V δ u :=
    lemma_21_1_2 hM hδ0 hδ1 ⟨M, fun x hx => rg_mem_box.1 (hcl hx)⟩ h2
  have hclosed : IsClosed (rg_V δ u) := closure_subset_iff_isClosed.1 (h2.trans h3)
  exact (rg_box_isCompact M).of_isClosed_subset hclosed hVbox

/-- **Proposition 21.1.2** (Miao, p. 745): with finitely many players and finite action sets,
the SPE payoff set `V` is compact. -/
theorem proposition_21_1_2 [Finite ι] [∀ i, Finite (A i)] {δ M : ℝ} {u : rg_Prof A → ι → ℝ}
    (hM : ∀ a j, |u a j| ≤ M) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) : IsCompact (rg_V δ u) := by
  let _ : ∀ i, TopologicalSpace (A i) := fun _ => ⊥
  have : ∀ i, DiscreteTopology (A i) := fun _ => ⟨rfl⟩
  exact ex_21_1 (fun _ => continuous_of_discreteTopology) hM hδ0 hδ1

end Miao.DynamicGames
