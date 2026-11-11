/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DynamicGames.RGCompact
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Computing `V` by iterating `B`

Miao, §21.1.3, pp. 746–747: Theorem 21.1.3 and the operators of Cronshaw–Luenberger and of
Judd–Yeltekin–Conklin. Finitely many players and finite action sets, as in the book.

* `theorem_21_1_3`: if `W₀ ⊇ V` is compact and `B(W₀) ⊆ W₀`, then `Wₜ = Bᵗ(W₀)` are compact,
  decreasing, contain `V`, and `V = ⋂ₜ Wₜ`. `theorem_21_1_3_hausdorff`: `Wₜ → V` in the
  Hausdorff distance (the book's `V = lim Bᵗ(W₀)`).
* `rg_maxBox u = ×ᵢ [uᵢ min, uᵢ max]`, the maximal payoff set: compact, contains `V`, and
  `B(maxBox) ⊆ maxBox`, so it is a valid `W₀` (`rg_theorem_21_1_3_maxBox`).
* `rg_BCL`: the operator `B` of Cronshaw–Luenberger with the worst punishment
  `w̲ᵢ = inf_{w ∈ W} wᵢ`; it equals `B` on compact sets (`rg_BCL_eq`), and `V` is its largest
  compact fixed point (`rg_cronshaw_luenberger`).
* `rg_Bstar W = co B(co W)` (Judd–Yeltekin–Conklin) is monotone (`rg_Bstar_mono`). Its
  compactness-preservation is not formalised: Mathlib v4.34.0 lacks compactness of the convex
  hull of a compact set (Carathéodory).
-/

namespace Miao.DynamicGames

open Filter Topology

variable {ι : Type*} {A : ι → Type*}

/-- A compact subset of `ℝⁿ` is bounded (`n` finite). -/
theorem rg_bdd_of_isCompact [Finite ι] {W : Set (ι → ℝ)} (hW : IsCompact W) : rg_Bdd W := by
  have := Fintype.ofFinite ι
  have hb : ∀ j, BddAbove ((fun x : ι → ℝ => |x j|) '' W) := fun j =>
    hW.bddAbove_image (continuous_abs.comp (continuous_apply j)).continuousOn
  choose C hC using hb
  refine ⟨∑ j, |C j|, fun x hx j => ?_⟩
  have h1 : |x j| ≤ C j := hC j ⟨x, hx, rfl⟩
  have h2 : |C j| ≤ ∑ k, |C k| :=
    Finset.single_le_sum (f := fun k => |C k|) (fun k _ => abs_nonneg _) (Finset.mem_univ j)
  linarith [le_abs_self (C j)]

/-- **Theorem 21.1.3** (Miao, p. 746). With finitely many players and finite action sets, let
`W₀ ⊇ V` be compact with `B(W₀) ⊆ W₀`. Then every `Wₜ = Bᵗ(W₀)` is compact,
`V ⊆ ⋯ ⊆ W₂ ⊆ W₁ ⊆ W₀`, and `V = ⋂ₜ Wₜ`. -/
theorem theorem_21_1_3 [Finite ι] [∀ i, Finite (A i)] {δ M : ℝ} {u : rg_Prof A → ι → ℝ}
    (hM : ∀ a j, |u a j| ≤ M) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {W0 : Set (ι → ℝ)}
    (hW0 : IsCompact W0) (hVW : rg_V δ u ⊆ W0) (hBW : rg_B δ u W0 ⊆ W0) :
    (∀ t, IsCompact ((rg_B δ u)^[t] W0)) ∧
      (∀ t, (rg_B δ u)^[t + 1] W0 ⊆ (rg_B δ u)^[t] W0) ∧
      (∀ t, rg_V δ u ⊆ (rg_B δ u)^[t] W0) ∧ rg_V δ u = ⋂ t, (rg_B δ u)^[t] W0 := by
  set Wt : ℕ → Set (ι → ℝ) := fun t => (rg_B δ u)^[t] W0 with hWt
  have hsucc : ∀ t, Wt (t + 1) = rg_B δ u (Wt t) := fun t =>
    Function.iterate_succ_apply' _ _ _
  have hc : ∀ t, IsCompact (Wt t) := by
    intro t
    induction t with
    | zero => exact hW0
    | succ t ih => rw [hsucc]; exact lemma_21_1_4 hδ0 ih
  have hstep : ∀ t, Wt (t + 1) ⊆ Wt t := by
    intro t
    induction t with
    | zero => exact hBW
    | succ t ih =>
      rw [hsucc, hsucc]
      rw [hsucc] at ih
      exact lemma_21_1_3 δ u ih
  have hV : ∀ t, rg_V δ u ⊆ Wt t := by
    intro t
    induction t with
    | zero => exact hVW
    | succ t ih =>
      rw [hsucc, theorem_21_1_1 hM hδ0 hδ1]
      exact lemma_21_1_3 δ u ih
  have hanti : Antitone Wt := antitone_nat_of_succ_le hstep
  refine ⟨hc, hstep, hV, Set.Subset.antisymm (Set.subset_iInter hV) ?_⟩
  set K := ⋂ t, Wt t with hK
  have hKW0 : K ⊆ W0 := Set.iInter_subset Wt 0
  have hKB : K ⊆ rg_B δ u K := by
    intro v hv
    have hvt : ∀ t, v ∈ rg_B δ u (Wt t) := fun t => hsucc t ▸ Set.mem_iInter.1 hv (t + 1)
    choose a w hadm hveq using hvt
    obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber a
    have hinf : (a ⁻¹' {y}).Infinite := Set.infinite_coe_iff.1 hy
    classical
    let S : ℕ → Set (rg_Prof A → ι → ℝ) := fun t =>
      (⋂ a', {w' | w' a' ∈ Wt t}) ∩ ((⋂ (i : ι), ⋂ (x : A i), {w' | (1 - δ) * u (rg_upd y i x) i +
        δ * w' (rg_upd y i x) i ≤ (1 - δ) * u y i + δ * w' y i}) ∩
        {w' | v = fun j => (1 - δ) * u y j + δ * w' y j})
    have hSmem : ∀ t w', w' ∈ S t ↔ rg_Admissible δ u (Wt t) y w' ∧
        v = fun j => (1 - δ) * u y j + δ * w' y j := by
      intro t w'
      simp only [S, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, rg_Admissible,
        and_assoc]
    have hSne : ∀ t, (S t).Nonempty := by
      intro t
      obtain ⟨s, hs, hts⟩ := hinf.exists_gt t
      have hys : a s = y := hs
      refine ⟨w s, (hSmem t (w s)).2 ⟨⟨fun a' => hanti hts.le ((hadm s).1 a'), ?_⟩, ?_⟩⟩
      · rw [← hys]
        exact (hadm s).2
      · rw [← hys]
        exact hveq s
    have hScl : ∀ t, IsClosed (S t) := by
      intro t
      refine (isClosed_iInter fun a' => (hc t).isClosed.preimage (continuous_apply a')).inter
        ((isClosed_iInter fun i => isClosed_iInter fun x => isClosed_le ?_ ?_).inter ?_)
      · exact continuous_const.add
          (continuous_const.mul ((continuous_apply i).comp (continuous_apply _)))
      · exact continuous_const.add
          (continuous_const.mul ((continuous_apply i).comp (continuous_apply _)))
      · exact isClosed_eq continuous_const (continuous_pi fun j => continuous_const.add
          (continuous_const.mul ((continuous_apply j).comp (continuous_apply y))))
    have hSstep : ∀ t, S (t + 1) ⊆ S t := by
      intro t w' hw'
      rw [hSmem] at hw' ⊢
      exact ⟨⟨fun a' => hstep t (hw'.1.1 a'), hw'.1.2⟩, hw'.2⟩
    have hS0 : IsCompact (S 0) :=
      (isCompact_univ_pi fun _ => hW0).of_isClosed_subset (hScl 0)
        fun w' hw' a' _ => ((hSmem 0 w').1 hw').1.1 a'
    obtain ⟨w', hw'⟩ :=
      IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hSstep hSne hS0 hScl
    have hw't : ∀ t, w' ∈ S t := Set.mem_iInter.1 hw'
    refine ⟨y, w', ⟨fun a' => Set.mem_iInter.2 fun t => ((hSmem t w').1 (hw't t)).1.1 a',
      ((hSmem 0 w').1 (hw't 0)).1.2⟩, ((hSmem 0 w').1 (hw't 0)).2⟩
  have hKb : rg_Bdd K := by
    obtain ⟨C, hC⟩ := rg_bdd_of_isCompact hW0
    exact ⟨C, fun x hx => hC x (hKW0 hx)⟩
  exact hKB.trans (lemma_21_1_2 hM hδ0 hδ1 hKb hKB)

/-- **Theorem 21.1.3** (Miao, p. 746), `V = lim_{t→∞} Bᵗ(W₀)`: the decreasing compact sets
`Bᵗ(W₀)` converge to `V` in the Hausdorff distance. -/
theorem theorem_21_1_3_hausdorff [Fintype ι] [∀ i, Finite (A i)] {δ M : ℝ}
    {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    {W0 : Set (ι → ℝ)} (hW0 : IsCompact W0) (hVW : rg_V δ u ⊆ W0) (hBW : rg_B δ u W0 ⊆ W0) :
    Tendsto (fun t => Metric.hausdorffDist ((rg_B δ u)^[t] W0) (rg_V δ u)) atTop (𝓝 0) := by
  obtain ⟨hc, hstep, hV, heq⟩ := theorem_21_1_3 hM hδ0 hδ1 hW0 hVW hBW
  set Wt : ℕ → Set (ι → ℝ) := fun t => (rg_B δ u)^[t] W0 with hWt
  have hanti : Antitone Wt := antitone_nat_of_succ_le hstep
  rcases (rg_V δ u).eq_empty_or_nonempty with hVe | _
  · simp only [hVe, Metric.hausdorffDist_empty]
    exact tendsto_const_nhds
  rw [Metric.tendsto_atTop]
  intro ε hε
  set C : ℕ → Set (ι → ℝ) := fun t => Wt t ∩ {x | ε / 2 ≤ Metric.infDist x (rg_V δ u)}
  have hCcl : ∀ t, IsClosed (C t) := fun t =>
    (hc t).isClosed.inter (isClosed_le continuous_const (Metric.continuous_infDist_pt _))
  have hCstep : ∀ t, C (t + 1) ⊆ C t := fun t =>
    Set.inter_subset_inter_left _ (hstep t)
  obtain ⟨T, hT⟩ : ∃ T, C T = ∅ := by
    by_contra hne
    push Not at hne
    have hne' : ∀ t, (C t).Nonempty := hne
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hCstep
      hne' ((hc 0).of_isClosed_subset (hCcl 0) Set.inter_subset_left) hCcl
    have hxt : ∀ t, x ∈ C t := Set.mem_iInter.1 hx
    have hxV : x ∈ rg_V δ u := by
      rw [heq]
      exact Set.mem_iInter.2 fun t => (hxt t).1
    have := (hxt 0).2
    simp only [Set.mem_ofPred_eq, Metric.infDist_zero_of_mem hxV] at this
    linarith
  refine ⟨T, fun n hn => ?_⟩
  have hlt : ∀ x ∈ Wt n, Metric.infDist x (rg_V δ u) < ε / 2 := by
    intro x hx
    by_contra hge
    have : x ∈ C T := ⟨hanti hn hx, not_lt.1 hge⟩
    rw [hT] at this
    exact this
  have hle : Metric.hausdorffDist (Wt n) (rg_V δ u) ≤ ε / 2 :=
    Metric.hausdorffDist_le_of_infDist (by linarith) (fun x hx => (hlt x hx).le)
      (fun x hx => by rw [Metric.infDist_zero_of_mem (hV n hx)]; linarith)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.hausdorffDist_nonneg]
  linarith

/-- `uᵢ min = min_{a ∈ A} uᵢ(a)` (Miao, p. 747). -/
noncomputable def rg_umin (u : rg_Prof A → ι → ℝ) (i : ι) : ℝ := ⨅ a, u a i

/-- `uᵢ max = max_{a ∈ A} uᵢ(a)` (Miao, p. 747). -/
noncomputable def rg_umax (u : rg_Prof A → ι → ℝ) (i : ι) : ℝ := ⨆ a, u a i

/-- The maximal payoff set `W = ×ᵢ [uᵢ min, uᵢ max]` (Miao, p. 747). -/
def rg_maxBox (u : rg_Prof A → ι → ℝ) : Set (ι → ℝ) :=
  Set.univ.pi fun i => Set.Icc (rg_umin u i) (rg_umax u i)

/-- Every stage payoff lies in the maximal payoff set (finite `A`). -/
theorem rg_u_mem_maxBox [Finite (rg_Prof A)] (u : rg_Prof A → ι → ℝ) (a : rg_Prof A) :
    u a ∈ rg_maxBox u := by
  refine Set.mem_univ_pi.2 fun i => ⟨?_, ?_⟩
  · exact ciInf_le (Set.finite_range fun a => u a i).bddBelow a
  · exact le_ciSup (Set.finite_range fun a => u a i).bddAbove a

/-- The maximal payoff set is compact. -/
theorem rg_maxBox_isCompact (u : rg_Prof A → ι → ℝ) : IsCompact (rg_maxBox u) :=
  isCompact_univ_pi fun _ => isCompact_Icc

/-- `V` lies in the maximal payoff set (finite `A`). -/
theorem rg_V_subset_maxBox [Finite (rg_Prof A)] {δ M : ℝ} {u : rg_Prof A → ι → ℝ}
    (hM : ∀ a j, |u a j| ≤ M) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) : rg_V δ u ⊆ rg_maxBox u := by
  rintro v ⟨σ, -, rfl⟩
  refine Set.mem_univ_pi.2 fun i => ?_
  have h := fun t => Set.mem_univ_pi.1 (rg_u_mem_maxBox u (rg_path σ t)) i
  exact rg_pathPay_mem hM hδ0 hδ1 _ i (fun t => (h t).1) (fun t => (h t).2)

/-- `B` maps the maximal payoff set into itself (finite `A`). -/
theorem rg_B_maxBox_subset [Finite (rg_Prof A)] {δ : ℝ} {u : rg_Prof A → ι → ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) : rg_B δ u (rg_maxBox u) ⊆ rg_maxBox u :=
  rg_B_subset_of_convex hδ0 hδ1 (convex_pi fun _ _ => convex_Icc _ _) (rg_u_mem_maxBox u)
    le_rfl

/-- Miao, p. 747: the maximal payoff set is a valid starting point for Theorem 21.1.3, so
`V = ⋂ₜ Bᵗ(×ᵢ [uᵢ min, uᵢ max])`. -/
theorem rg_theorem_21_1_3_maxBox [Finite ι] [∀ i, Finite (A i)] {δ M : ℝ}
    {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    rg_V δ u = ⋂ t, (rg_B δ u)^[t] (rg_maxBox u) :=
  (theorem_21_1_3 hM hδ0 hδ1 (rg_maxBox_isCompact u) (rg_V_subset_maxBox hM hδ0 hδ1)
    (rg_B_maxBox_subset hδ0 hδ1)).2.2.2

/-- The operator of Cronshaw and Luenberger (Miao, p. 747): `B(W)` is the set of
`(1 − δ) u(a) + δ w` with `w ∈ W` satisfying `ICᵢ` for all `i`:
`(1 − δ) uᵢ(a) + δ wᵢ ≥ (1 − δ) uᵢ(a'ᵢ, a₋ᵢ) + δ w̲ᵢ` for all `a'ᵢ`, `w̲ᵢ = inf_{w ∈ W} wᵢ`. -/
noncomputable def rg_BCL (δ : ℝ) (u : rg_Prof A → ι → ℝ) (W : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {v | ∃ a, ∃ w ∈ W, (v = fun j => (1 - δ) * u a j + δ * w j) ∧ ∀ (i : ι) (x : A i),
    (1 - δ) * u (rg_upd a i x) i + δ * sInf ((fun y : ι → ℝ => y i) '' W) ≤
      (1 - δ) * u a i + δ * w i}

/-- On compact sets the Cronshaw–Luenberger operator is the APS operator `B`. -/
theorem rg_BCL_eq {δ : ℝ} {u : rg_Prof A → ι → ℝ} (hδ0 : 0 ≤ δ) {W : Set (ι → ℝ)}
    (hW : IsCompact W) : rg_BCL δ u W = rg_B δ u W := by
  rcases W.eq_empty_or_nonempty with rfl | hne
  · ext v
    simp only [rg_BCL, Set.mem_empty_iff_false, false_and, exists_false, Set.mem_ofPred_eq,
      false_iff]
    rintro ⟨a, w, ⟨hw, -⟩, -⟩
    exact hw a
  have hmin : ∀ i, ∃ x ∈ W, IsMinOn (fun y : ι → ℝ => y i) W x := fun i =>
    hW.exists_isMinOn hne (continuous_apply i).continuousOn
  choose p hpW hpmin using hmin
  have hp : ∀ i, p i ∈ W ∧ ∀ x ∈ W, p i i ≤ x i := fun i => ⟨hpW i, fun x hx => hpmin i hx⟩
  have hinf : ∀ i, sInf ((fun y : ι → ℝ => y i) '' W) = p i i := fun i =>
    IsLeast.csInf_eq ⟨⟨p i, hpW i, rfl⟩, by rintro _ ⟨x, hx, rfl⟩; exact (hp i).2 x hx⟩
  ext v
  rw [rg_mem_B_iff_punish hδ0 hp]
  simp only [rg_BCL, Set.mem_ofPred_eq, hinf]

/-- Cronshaw and Luenberger (Miao, p. 747): with finitely many players and finite action sets,
`V` lies in the maximal payoff set, is a fixed point of their operator, and contains every
compact `W` with `W ⊆ B(W)`; so `V` is its largest compact fixed point. -/
theorem rg_cronshaw_luenberger [Finite ι] [∀ i, Finite (A i)] {δ M : ℝ}
    {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    rg_V δ u ⊆ rg_maxBox u ∧ rg_V δ u = rg_BCL δ u (rg_V δ u) ∧
      ∀ W, IsCompact W → W ⊆ rg_BCL δ u W → W ⊆ rg_V δ u := by
  refine ⟨rg_V_subset_maxBox hM hδ0 hδ1, ?_, fun W hW hWB => ?_⟩
  · rw [rg_BCL_eq hδ0 (proposition_21_1_2 hM hδ0 hδ1)]
    exact theorem_21_1_1 hM hδ0 hδ1
  · rw [rg_BCL_eq hδ0 hW] at hWB
    exact hWB.trans (lemma_21_1_2 hM hδ0 hδ1 (rg_bdd_of_isCompact hW) hWB)

/-- The operator `B*(co W) = co B(co W)` of Judd, Yeltekin and Conklin (Miao, p. 747). -/
noncomputable def rg_Bstar (δ : ℝ) (u : rg_Prof A → ι → ℝ) (W : Set (ι → ℝ)) :
    Set (ι → ℝ) :=
  convexHull ℝ (rg_B δ u (convexHull ℝ W))

/-- Miao, p. 747: `B*` is monotone. -/
theorem rg_Bstar_mono (δ : ℝ) (u : rg_Prof A → ι → ℝ) {W W' : Set (ι → ℝ)} (h : W ⊆ W') :
    rg_Bstar δ u W ⊆ rg_Bstar δ u W' :=
  convexHull_mono (lemma_21_1_3 δ u (convexHull_mono h))

end Miao.DynamicGames
