/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DynamicGames.CGRecursive
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Real

/-!
# The equilibrium value set

Miao, §21.4.3, pp. 764–766: the APS method for the credible-policy economy.

* `cg_Admissible`, `cg_B`, `cg_SelfGenerating`: Definitions 21.4.2–21.4.4.
* `lemma_21_4_2`: `B` is monotone and (for compact `X`, `Y`, closed `C` and continuous `r`)
  preserves compactness. The proof writes `B(W)` as the continuous image of the compact set
  `cg_K W` of tuples `((x, y), w₁, w₂)` with a single punishment value `w₂ ∈ W`
  (`cg_B_eq_image`, which needs only `W` compact).
* `lemma_21_4_3`: a bounded self-generating `W` has `B(W) ⊆ V`. The proof builds the recursive
  strategy of §21.4.5 whose states are the values in `W` (as in the book's proof).
* `theorem_21_4_1`: `V = B(V)`, `V` is bounded, and it contains every bounded fixed point.
  "Largest fixed point" needs the qualifier *bounded*: `B(ℝ) = ℝ` in Example 21.4.2
  (`cg_theorem_21_4_1_unbounded` in `CGExamples`).
* The algorithm on pp. 765–766: step 1 (`cg_aps_step1`), the characterisation of
  `B([w_min⁰, w_max⁰])` in step 2 (`cg_aps_step2`, `cg_aps_step2_max`), and step 3: the iterates
  `W_{j+1} = B(W_j)` decrease, are compact, contain `V`, and their intersection is `V`
  (`cg_aps_step3`). In the book's formula for `w¹_max` the bounds of the constraint must be the
  bounds `w⁰_max`, `w⁰_min` of `W₀`, not the unknowns `w¹_max`, `w¹_min`.
-/

open Filter Topology

namespace Miao.DynamicGames

variable {X Y : Type*}

/-- **Definition 21.4.2** (Miao, p. 764): `(x, y, w)` is admissible with respect to `W`. -/
def cg_Admissible (δ : ℝ) (r : X → Y → ℝ) (C : Set (X × Y)) (W : Set ℝ) (x : X) (y : Y)
    (w : X × Y → ℝ) : Prop :=
  (x, y) ∈ C ∧ (∀ q, w q ∈ W) ∧
    ∀ y', (1 - δ) * r x y' + δ * w (x, y') ≤ (1 - δ) * r x y + δ * w (x, y)

/-- **Definition 21.4.3** (Miao, p. 764): `B(W)`, the values of admissible tuples. -/
def cg_B (δ : ℝ) (r : X → Y → ℝ) (C : Set (X × Y)) (W : Set ℝ) : Set ℝ :=
  {v | ∃ x y w, cg_Admissible δ r C W x y w ∧ v = (1 - δ) * r x y + δ * w (x, y)}

/-- **Definition 21.4.4** (Miao, p. 764): `W` is self-generating if `W ⊆ B(W)`. -/
def cg_SelfGenerating (δ : ℝ) (r : X → Y → ℝ) (C : Set (X × Y)) (W : Set ℝ) : Prop :=
  W ⊆ cg_B δ r C W

/-- **Definition 21.4.2** (Miao, p. 764), unfolded. -/
theorem definition_21_4_2 (δ : ℝ) (r : X → Y → ℝ) (C : Set (X × Y)) (W : Set ℝ) (x : X) (y : Y)
    (w : X × Y → ℝ) : cg_Admissible δ r C W x y w ↔ (x, y) ∈ C ∧ (∀ q, w q ∈ W) ∧
      ∀ y', (1 - δ) * r x y' + δ * w (x, y') ≤ (1 - δ) * r x y + δ * w (x, y) := Iff.rfl

/-- **Definition 21.4.3** (Miao, p. 764), unfolded. -/
theorem definition_21_4_3 (δ : ℝ) (r : X → Y → ℝ) (C : Set (X × Y)) (W : Set ℝ) (v : ℝ) :
    v ∈ cg_B δ r C W ↔
      ∃ x y w, cg_Admissible δ r C W x y w ∧ v = (1 - δ) * r x y + δ * w (x, y) := Iff.rfl

/-- **Definition 21.4.4** (Miao, p. 764), unfolded. -/
theorem definition_21_4_4 (δ : ℝ) (r : X → Y → ℝ) (C : Set (X × Y)) (W : Set ℝ) :
    cg_SelfGenerating δ r C W ↔ W ⊆ cg_B δ r C W := Iff.rfl

theorem cg_B_mono (δ : ℝ) (r : X → Y → ℝ) (C : Set (X × Y)) : Monotone (cg_B δ r C) := by
  intro W W' hWW' v ⟨x, y, w, ⟨hC, hw, hIC⟩, hv⟩
  exact ⟨x, y, w, ⟨hC, fun q => hWW' (hw q), hIC⟩, hv⟩

/-- Tuples `((x, y), w₁, w₂)` with `(x, y) ∈ C`, `w₁, w₂ ∈ W` and
`(1 − δ) r(x, y') + δ w₂ ≤ (1 − δ) r(x, y) + δ w₁` for all `y'`. -/
def cg_K (δ : ℝ) (r : X → Y → ℝ) (C : Set (X × Y)) (W : Set ℝ) : Set ((X × Y) × ℝ × ℝ) :=
  {q | q.1 ∈ C ∧ q.2.1 ∈ W ∧ q.2.2 ∈ W ∧
    ∀ y', (1 - δ) * r q.1.1 y' + δ * q.2.2 ≤ (1 - δ) * r q.1.1 q.1.2 + δ * q.2.1}

theorem cg_K_mono (δ : ℝ) (r : X → Y → ℝ) (C : Set (X × Y)) : Monotone (cg_K δ r C) := by
  intro W W' h q ⟨h1, h2, h3, h4⟩
  exact ⟨h1, h h2, h h3, h4⟩

/-- For compact `W`, `B(W)` is the image of `cg_K W` under `((x, y), w₁, w₂) ↦ (1 − δ) r + δ w₁`:
a single punishment value (the minimum of `W`) suffices. -/
theorem cg_B_eq_image {δ : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ) {W : Set ℝ}
    (hW : IsCompact W) :
    cg_B δ r C W = (fun q : (X × Y) × ℝ × ℝ => (1 - δ) * r q.1.1 q.1.2 + δ * q.2.1) ''
      cg_K δ r C W := by
  classical
  ext v
  constructor
  · rintro ⟨x, y, w, ⟨hC, hw, hIC⟩, rfl⟩
    have hne : W.Nonempty := ⟨_, hw (x, y)⟩
    refine ⟨((x, y), w (x, y), sInf W), ⟨hC, hw _, hW.sInf_mem hne, fun y' => ?_⟩, rfl⟩
    have h1 : sInf W ≤ w (x, y') := csInf_le hW.bddBelow (hw _)
    have h2 := hIC y'
    have h3 : δ * sInf W ≤ δ * w (x, y') := mul_le_mul_of_nonneg_left h1 hδ0
    dsimp only
    linarith
  · rintro ⟨⟨⟨x, y⟩, w₁, w₂⟩, ⟨hC, h1, h2, hIC⟩, rfl⟩
    refine ⟨x, y, fun q => if q = (x, y) then w₁ else w₂, ⟨hC, fun q => ?_, fun y' => ?_⟩, ?_⟩
    · dsimp only
      split_ifs
      · exact h1
      · exact h2
    · by_cases hy : y' = y
      · subst hy; exact le_rfl
      · have : ((x, y') : X × Y) ≠ (x, y) := by simp [hy]
        simp only [this, ↓reduceIte]
        exact hIC y'
    · simp

/-- `cg_K W` is compact for compact `W`, compact `X`, `Y`, closed `C` and continuous `r`. -/
theorem cg_K_isCompact [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X]
    [CompactSpace Y] {δ : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hC : IsClosed C)
    (hr : Continuous (fun q : X × Y => r q.1 q.2)) {W : Set ℝ} (hW : IsCompact W) :
    IsCompact (cg_K δ r C W) := by
  have hrc : ∀ y', Continuous (fun q : (X × Y) × ℝ × ℝ => r q.1.1 y') := fun y' =>
    hr.comp (continuous_fst.fst.prodMk continuous_const)
  have hr2 : Continuous (fun q : (X × Y) × ℝ × ℝ => r q.1.1 q.1.2) :=
    hr.comp continuous_fst
  have hD : IsClosed {q : (X × Y) × ℝ × ℝ |
      ∀ y', (1 - δ) * r q.1.1 y' + δ * q.2.2 ≤ (1 - δ) * r q.1.1 q.1.2 + δ * q.2.1} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun y' => isClosed_le
      ((continuous_const.mul (hrc y')).add (continuous_const.mul continuous_snd.snd))
      ((continuous_const.mul hr2).add (continuous_const.mul continuous_snd.fst))
  have hP : IsCompact (C ×ˢ (W ×ˢ W)) := hC.isCompact.prod (hW.prod hW)
  have : cg_K δ r C W = (C ×ˢ (W ×ˢ W)) ∩ {q : (X × Y) × ℝ × ℝ |
      ∀ y', (1 - δ) * r q.1.1 y' + δ * q.2.2 ≤ (1 - δ) * r q.1.1 q.1.2 + δ * q.2.1} := by
    ext q
    simp only [cg_K, Set.mem_inter_iff, Set.mem_prod, Set.mem_ofPred_eq]
    tauto
  rw [this]
  exact hP.inter_right hD

/-- **Lemma 21.4.2** (Miao, p. 764). The operator `B` is monotone and preserves compactness
(for compact `X`, `Y`, closed `C`, continuous `r` and `0 ≤ δ`). -/
theorem lemma_21_4_2 [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X]
    [CompactSpace Y] {δ : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ) (hC : IsClosed C)
    (hr : Continuous (fun q : X × Y => r q.1 q.2)) :
    Monotone (cg_B δ r C) ∧ ∀ W, IsCompact W → IsCompact (cg_B δ r C W) := by
  refine ⟨cg_B_mono δ r C, fun W hW => ?_⟩
  rw [cg_B_eq_image hδ0 hW]
  exact (cg_K_isCompact hC hr hW).image
    ((continuous_const.mul (hr.comp continuous_fst)).add (continuous_const.mul continuous_snd.fst))

/-- `V ⊆ B(V)` (Miao, p. 765, "by Lemma 21.4.1"): an SPE value is generated by the first-period
outcome and the continuation values `w(ξ, η) = Uᵍ(σ|_(ξ, η))`. -/
theorem cg_V_subset_B {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) : cg_V δ r C ⊆ cg_B δ r C (cg_V δ r C) := by
  rintro _ ⟨σ, hσ, rfl⟩
  obtain ⟨hcont, hC, hdev⟩ := (lemma_21_4_1 hδ0 hδ1 hM σ).1 hσ
  refine ⟨(σ []).1, (σ []).2, fun q => cg_U δ r (cg_cont σ [q]),
    ⟨hC, fun q => ⟨_, hcont q.1 q.2, rfl⟩, hdev⟩, ?_⟩
  exact cg_U_rec hδ0 hδ1 hM σ

/-- Pasting: play `q` first, then `τ (ξ, η)` after the first-period outcome `(ξ, η)`. -/
def cg_paste (q : X × Y) (τ : X × Y → CGProfile X Y) : CGProfile X Y
  | [] => q
  | p :: h => τ p h

/-- If `W ⊆ V` then `B(W) ⊆ V` (Lemma 21.4.1, "if" half). -/
theorem cg_B_subset_V {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) {W : Set ℝ} (hW : W ⊆ cg_V δ r C) : cg_B δ r C W ⊆ cg_V δ r C := by
  rintro _ ⟨x, y, w, ⟨hC, hw, hIC⟩, rfl⟩
  choose τ hτ hτv using fun q => hW (hw q)
  have hc : ∀ q, cg_cont (cg_paste (x, y) τ) [q] = τ q := fun q => rfl
  refine ⟨cg_paste (x, y) τ, ?_, ?_⟩
  · rw [lemma_21_4_1 hδ0 hδ1 hM]
    refine ⟨fun ξ η => by rw [hc]; exact hτ _, hC, fun η => ?_⟩
    have e : cg_paste (x, y) τ [] = (x, y) := rfl
    rw [e, hc, hc, hτv, hτv]
    exact hIC η
  · rw [cg_U_rec hδ0 hδ1 hM]
    have e : cg_paste (x, y) τ [] = (x, y) := rfl
    rw [e, hc, hτv]

/-- A bounded self-generating set is contained in `V` (the first half of Lemma 21.4.3's proof:
the recursive strategy whose states are the values in `W`). -/
theorem cg_selfGenerating_subset_V {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) {W : Set ℝ} (hWb : Bornology.IsBounded W)
    (hSG : cg_SelfGenerating δ r C W) : W ⊆ cg_V δ r C := by
  classical
  intro v0 hv0
  obtain ⟨K, hK⟩ := isBounded_iff_forall_norm_le.1 hWb
  have hc : ∀ s, s ∈ W → ∃ x y w, cg_Admissible δ r C W x y w ∧
      s = (1 - δ) * r x y + δ * w (x, y) := fun s hs => hSG hs
  choose zx zy zw hadm hval using hc
  let zh : ℝ → X := fun s => if hs : s ∈ W then zx s hs else zx v0 hv0
  let zg : ℝ → Y := fun s => if hs : s ∈ W then zy s hs else zy v0 hv0
  let Vf : ℝ → X → Y → ℝ := fun s ξ η => if hs : s ∈ W then zw s hs (ξ, η) else zw v0 hv0 (ξ, η)
  have hzh : ∀ s (hs : s ∈ W), zh s = zx s hs := fun s hs => by simp [zh, hs]
  have hzg : ∀ s (hs : s ∈ W), zg s = zy s hs := fun s hs => by simp [zg, hs]
  have hVf : ∀ s (hs : s ∈ W) ξ η, Vf s ξ η = zw s hs (ξ, η) := fun s hs ξ η => by simp [Vf, hs]
  have hspe := cg_recursive_spe (C := C) (K := K) (S := W) (zh := zh) (zg := zg) (Vf := Vf)
    hδ0 hδ1 hM (fun s hs => by have := hK s hs; rwa [Real.norm_eq_abs] at this)
    (fun s hs ξ η => by rw [hVf s hs]; exact (hadm s hs).2.1 _)
    (fun s hs => by rw [hzh s hs, hzg s hs, hVf s hs]; exact (hval s hs).symm)
    (fun s hs => by rw [hzh s hs, hzg s hs]; exact (hadm s hs).1)
    (fun s hs y' => by
      rw [hzh s hs, hVf s hs]
      have := (hadm s hs).2.2 y'
      rw [← hval s hs] at this
      exact this) v0 hv0
  exact ⟨_, hspe.1, hspe.2⟩

/-- **Lemma 21.4.3** (self-generation, Miao, p. 764). If `W ⊆ ℝ` is bounded and self-generating,
then `B(W) ⊆ V`. -/
theorem lemma_21_4_3 {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) {W : Set ℝ} (hWb : Bornology.IsBounded W)
    (hSG : cg_SelfGenerating δ r C W) : cg_B δ r C W ⊆ cg_V δ r C :=
  cg_B_subset_V hδ0 hδ1 hM (cg_selfGenerating_subset_V hδ0 hδ1 hM hWb hSG)

/-- **Theorem 21.4.1** (Miao, p. 765), corrected. `V = B(V)`, `V` is bounded, and `V` contains
every bounded fixed point of `B`: it is the largest *bounded* fixed point. (Without
boundedness the claim fails: `cg_theorem_21_4_1_unbounded`.) -/
theorem theorem_21_4_1 {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) :
    cg_V δ r C = cg_B δ r C (cg_V δ r C) ∧ Bornology.IsBounded (cg_V δ r C) ∧
      ∀ W, Bornology.IsBounded W → cg_B δ r C W = W → W ⊆ cg_V δ r C := by
  refine ⟨Set.Subset.antisymm (cg_V_subset_B hδ0 hδ1 hM) (cg_B_subset_V hδ0 hδ1 hM le_rfl),
    cg_V_isBounded hδ0 hδ1 hM, fun W hWb hfix => ?_⟩
  have hSG : cg_SelfGenerating δ r C W := hfix.symm.subset
  exact hfix.symm.subset.trans (lemma_21_4_3 hδ0 hδ1 hM hWb hSG)

/-- A value generated by `V ∪ {v}` is an SPE value. -/
theorem cg_mem_V_of_mem_B_insert {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) {v : ℝ}
    (hv : v ∈ cg_B δ r C (insert v (cg_V δ r C))) : v ∈ cg_V δ r C := by
  have hb : Bornology.IsBounded (insert v (cg_V δ r C)) :=
    (cg_V_isBounded hδ0 hδ1 hM).insert v
  have hSG : cg_SelfGenerating δ r C (insert v (cg_V δ r C)) := by
    intro w hw
    rcases hw with rfl | hw
    · exact hv
    · exact cg_B_mono δ r C (Set.subset_insert _ _) (cg_V_subset_B hδ0 hδ1 hM hw)
  exact lemma_21_4_3 hδ0 hδ1 hM hb hSG hv

/-- Miao, p. 765, step 1 of the algorithm: if `a ≤ r ≤ b` on `C` (e.g. `a = min_C r`,
`b = max_C r`), then `V ⊆ W₀ = [a, b]` and `B(W₀) ⊆ W₀`. -/
theorem cg_aps_step1 {δ M a b : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) (hab : ∀ q ∈ C, a ≤ r q.1 q.2 ∧ r q.1 q.2 ≤ b) :
    cg_V δ r C ⊆ Set.Icc a b ∧ cg_B δ r C (Set.Icc a b) ⊆ Set.Icc a b := by
  refine ⟨cg_V_subset_Icc hδ0 hδ1 hM hab, ?_⟩
  rintro _ ⟨x, y, w, ⟨hC, hw, -⟩, rfl⟩
  obtain ⟨h1, h2⟩ := hab _ hC
  obtain ⟨h3, h4⟩ := hw (x, y)
  have h5 : 0 ≤ 1 - δ := by linarith
  constructor <;> nlinarith

/-- Miao, p. 765, step 2 of the algorithm: for `a ≤ b`, `B([a, b])` is the set of
`(1 − δ) r(x, y) + δ w₁` over `(x, y) ∈ C`, `w₁, w₂ ∈ [a, b]` with
`(1 − δ) r(x, y) + δ w₁ ≥ (1 − δ) r(x, y') + δ w₂` for all `y'` (the problem defining `w¹_min`). -/
theorem cg_aps_step2 {δ a b : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ) (v : ℝ) :
    v ∈ cg_B δ r C (Set.Icc a b) ↔ ∃ x y w₁ w₂, (x, y) ∈ C ∧ w₁ ∈ Set.Icc a b ∧
      w₂ ∈ Set.Icc a b ∧ (∀ y', (1 - δ) * r x y' + δ * w₂ ≤ (1 - δ) * r x y + δ * w₁) ∧
      v = (1 - δ) * r x y + δ * w₁ := by
  rw [cg_B_eq_image hδ0 isCompact_Icc]
  constructor
  · rintro ⟨⟨⟨x, y⟩, w₁, w₂⟩, ⟨hC, h1, h2, hIC⟩, rfl⟩
    exact ⟨x, y, w₁, w₂, hC, h1, h2, hIC, rfl⟩
  · rintro ⟨x, y, w₁, w₂, hC, h1, h2, hIC, rfl⟩
    exact ⟨⟨⟨x, y⟩, w₁, w₂⟩, ⟨hC, h1, h2, hIC⟩, rfl⟩

/-- Miao, p. 765, step 2 of the algorithm: `w¹_max = max B([a, b])` solves
`max_{(x, y) ∈ C} (1 − δ) r(x, y) + δ b` subject to
`(1 − δ) r(x, y) + δ b ≥ (1 − δ) r(x, y') + δ a` for all `y'` (with the bounds `b = w⁰_max`,
`a = w⁰_min` of `W₀` in the constraint). -/
theorem cg_aps_step2_max {δ a b : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hab : a ≤ b) (m : ℝ) :
    IsGreatest (cg_B δ r C (Set.Icc a b)) m ↔
      IsGreatest {v | ∃ x y, (x, y) ∈ C ∧
        (∀ y', (1 - δ) * r x y' + δ * a ≤ (1 - δ) * r x y + δ * b) ∧
        v = (1 - δ) * r x y + δ * b} m := by
  set S := {v | ∃ x y, (x, y) ∈ C ∧
    (∀ y', (1 - δ) * r x y' + δ * a ≤ (1 - δ) * r x y + δ * b) ∧ v = (1 - δ) * r x y + δ * b}
  have hST : S ⊆ cg_B δ r C (Set.Icc a b) := by
    rintro _ ⟨x, y, hC, hIC, rfl⟩
    exact (cg_aps_step2 hδ0 _).2 ⟨x, y, b, a, hC, ⟨hab, le_rfl⟩, ⟨le_rfl, hab⟩, hIC, rfl⟩
  have hTS : ∀ t ∈ cg_B δ r C (Set.Icc a b), ∃ s ∈ S, t ≤ s := by
    intro t ht
    obtain ⟨x, y, w₁, w₂, hC, h1, h2, hIC, rfl⟩ := (cg_aps_step2 hδ0 _).1 ht
    refine ⟨_, ⟨x, y, hC, fun y' => ?_, rfl⟩, ?_⟩
    · have := hIC y'
      have : δ * a ≤ δ * w₂ := mul_le_mul_of_nonneg_left h2.1 hδ0
      have : δ * w₁ ≤ δ * b := mul_le_mul_of_nonneg_left h1.2 hδ0
      linarith
    · have : δ * w₁ ≤ δ * b := mul_le_mul_of_nonneg_left h1.2 hδ0
      linarith
  constructor
  · rintro ⟨hm, hub⟩
    obtain ⟨s, hs, hms⟩ := hTS m hm
    have : s = m := le_antisymm (hub (hST hs)) hms
    exact ⟨this ▸ hs, fun s hs => hub (hST hs)⟩
  · rintro ⟨hm, hub⟩
    refine ⟨hST hm, fun t ht => ?_⟩
    obtain ⟨s, hs, hts⟩ := hTS t ht
    exact hts.trans (hub hs)

/-- Miao, pp. 765–766, step 3 of the algorithm. Starting from `W₀ = [a, b]` with `a ≤ r ≤ b` on
`C`, the iterates `W_j = B^j(W₀)` decrease, contain `V`, are compact, and converge to `V`:
`⋂_j W_j = V` (for compact Hausdorff `X`, `Y`, closed `C`, continuous `r`). -/
theorem cg_aps_step3 [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X]
    [CompactSpace Y] [T2Space X] [T2Space Y] {δ M a b : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) (hC : IsClosed C)
    (hr : Continuous (fun q : X × Y => r q.1 q.2))
    (hab : ∀ q ∈ C, a ≤ r q.1 q.2 ∧ r q.1 q.2 ≤ b) :
    (∀ j, (cg_B δ r C)^[j + 1] (Set.Icc a b) ⊆ (cg_B δ r C)^[j] (Set.Icc a b)) ∧
      (∀ j, cg_V δ r C ⊆ (cg_B δ r C)^[j] (Set.Icc a b)) ∧
      (∀ j, IsCompact ((cg_B δ r C)^[j] (Set.Icc a b))) ∧
      ⋂ j, (cg_B δ r C)^[j] (Set.Icc a b) = cg_V δ r C := by
  set W : ℕ → Set ℝ := fun j => (cg_B δ r C)^[j] (Set.Icc a b) with hWdef
  have hWs : ∀ j, W (j + 1) = cg_B δ r C (W j) := fun j => by
    simp only [hWdef, Function.iterate_succ_apply']
  obtain ⟨hV0, hB0⟩ := cg_aps_step1 hδ0 hδ1 hM hab
  have hdec : ∀ j, W (j + 1) ⊆ W j := by
    intro j
    induction j with
    | zero => rw [hWs]; exact hB0
    | succ j ih =>
      calc W (j + 1 + 1) = cg_B δ r C (W (j + 1)) := hWs _
        _ ⊆ cg_B δ r C (W j) := cg_B_mono δ r C ih
        _ = W (j + 1) := (hWs j).symm
  have hVW : ∀ j, cg_V δ r C ⊆ W j := by
    intro j
    induction j with
    | zero => exact hV0
    | succ j ih =>
      rw [hWs, (theorem_21_4_1 hδ0 hδ1 hM).1]
      exact cg_B_mono δ r C ih
  have hcpt : ∀ j, IsCompact (W j) := by
    intro j
    induction j with
    | zero => exact isCompact_Icc
    | succ j ih => rw [hWs]; exact (lemma_21_4_2 hδ0 hC hr).2 _ ih
  refine ⟨hdec, hVW, hcpt, ?_⟩
  set Winf := ⋂ j, W j
  have hWinf_cpt : IsCompact Winf :=
    (hcpt 0).of_isClosed_subset (isClosed_iInter fun j => (hcpt j).isClosed)
      (Set.iInter_subset _ 0)
  have hf : Continuous (fun q : (X × Y) × ℝ × ℝ => (1 - δ) * r q.1.1 q.1.2 + δ * q.2.1) :=
    (continuous_const.mul (hr.comp continuous_fst)).add (continuous_const.mul continuous_snd.fst)
  have h1 : cg_B δ r C Winf ⊆ Winf := by
    intro v hv
    refine Set.mem_iInter.2 fun j => hdec j ?_
    rw [hWs]
    exact cg_B_mono δ r C (Set.iInter_subset _ j) hv
  have h2 : Winf ⊆ cg_B δ r C Winf := by
    intro v hv
    have hvj : ∀ j, v ∈ W (j + 1) := fun j => Set.mem_iInter.1 hv (j + 1)
    set L : ℕ → Set ((X × Y) × ℝ × ℝ) := fun j =>
      cg_K δ r C (W j) ∩ (fun q : (X × Y) × ℝ × ℝ => (1 - δ) * r q.1.1 q.1.2 + δ * q.2.1) ⁻¹'
        {v}
    have hLc : ∀ j, IsCompact (L j) := fun j =>
      (cg_K_isCompact hC hr (hcpt j)).inter_right (isClosed_singleton.preimage hf)
    have hne : (⋂ j, L j).Nonempty := by
      refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed L
        (fun j => Set.inter_subset_inter_left _ (cg_K_mono δ r C (hdec j)))
        (fun j => ?_) (hLc 0) (fun j => (hLc j).isClosed)
      have := hvj j
      rw [hWs, cg_B_eq_image hδ0 (hcpt j)] at this
      obtain ⟨q, hq, hqv⟩ := this
      exact ⟨q, hq, hqv⟩
    obtain ⟨q, hq⟩ := hne
    have hqj : ∀ j, q ∈ L j := Set.mem_iInter.1 hq
    rw [cg_B_eq_image hδ0 hWinf_cpt]
    refine ⟨q, ⟨(hqj 0).1.1, Set.mem_iInter.2 fun j => (hqj j).1.2.1,
      Set.mem_iInter.2 fun j => (hqj j).1.2.2.1, (hqj 0).1.2.2.2⟩, (hqj 0).2⟩
  have hfix : cg_B δ r C Winf = Winf := Set.Subset.antisymm h1 h2
  have hbdd : Bornology.IsBounded Winf := hWinf_cpt.isBounded
  exact Set.Subset.antisymm ((theorem_21_4_1 hδ0 hδ1 hM).2.2 _ hbdd hfix)
    (Set.subset_iInter hVW)

end Miao.DynamicGames
