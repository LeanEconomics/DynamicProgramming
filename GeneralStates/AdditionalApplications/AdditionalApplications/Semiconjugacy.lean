/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AdditionalApplications.Conjugacy

/-!
# Strong semiconjugacy

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §5.2.1.1–5.2.1.2 (pp. 160–163).

`(V, S)` and `(V̂, Ŝ)` are strongly semiconjugate under `F, G` when `S = G ∘ F` and `Ŝ = F ∘ G`
(5.14).

* **Exercise 5.2.1**: (5.14) implies (5.15).
* **Lemma 5.2.1**: fixed points, and uniqueness of fixed points, transfer.
* **Lemma 5.2.2 (i)**: order stability transfers when `F, G` are both order preserving or both
  order reversing.
* **Lemma 5.2.2 (ii)**, **Theorem 5.2.3** and **Theorem 5.2.4**: strong order stability transfers
  when the maps also carry decreasing limits. The book's order continuity (§A.5.1.3) only covers
  increasing sequences, and with it alone all three statements fail
  (`SemiconjCounterexample`); the proofs here use limits in both directions.
-/

open Set Function Filter Topology

namespace SargentStachurski.AdditionalApplications

/-- `(V, S)` and `(V̂, Ŝ)` are strongly semiconjugate under `F, G` (5.14): `S = G ∘ F` on `V` and
`Ŝ = F ∘ G` on `V̂`. -/
def IsStronglySemiconj {V W : Type*} (S : V → V) (Sh : W → W) (F : V → W) (G : W → V) : Prop :=
  (∀ v, S v = G (F v)) ∧ ∀ w, Sh w = F (G w)

/-- `S` preserves decreasing limits: `vₙ ↓ v` implies that `Svₙ` has infimum `Sv`. -/
def OrderContinuousDown {V W : Type*} [PartialOrder V] [PartialOrder W] (S : V → W) : Prop :=
  ∀ (f : ℕ → V) (v : V), Antitone f → IsGLB (range f) v → IsGLB (range (S ∘ f)) (S v)

/-- An order-reversing `S` turns increasing limits into decreasing ones: `vₙ ↑ v` implies that
`Svₙ` has infimum `Sv`. -/
def AntiContinuousUp {V W : Type*} [PartialOrder V] [PartialOrder W] (S : V → W) : Prop :=
  ∀ (f : ℕ → V) (v : V), Monotone f → IsLUB (range f) v → IsGLB (range (S ∘ f)) (S v)

/-- An order-reversing `S` turns decreasing limits into increasing ones: `vₙ ↓ v` implies that
`Svₙ` has supremum `Sv` (the hypothesis of Theorem 5.2.4). -/
def AntiContinuousDown {V W : Type*} [PartialOrder V] [PartialOrder W] (S : V → W) : Prop :=
  ∀ (f : ℕ → V) (v : V), Antitone f → IsGLB (range f) v → IsLUB (range (S ∘ f)) (S v)

namespace IsStronglySemiconj

variable {V W : Type*} {S : V → V} {Sh : W → W} {F : V → W} {G : W → V}

/-- The roles of the two systems can be swapped. -/
theorem swap (h : IsStronglySemiconj S Sh F G) : IsStronglySemiconj Sh S G F := ⟨h.2, h.1⟩

/-- **Exercise 5.2.1** (p. 161): (5.14) implies (5.15), `F ∘ S = Ŝ ∘ F` and `G ∘ Ŝ = S ∘ G`. -/
theorem exercise_5_2_1 (h : IsStronglySemiconj S Sh F G) : Semiconj F S Sh ∧ Semiconj G Sh S :=
  ⟨fun v => by rw [h.1, h.2], fun w => by rw [h.1, h.2]⟩

/-- `Ŝⁿ⁺¹ = F ∘ Sⁿ ∘ G`. -/
theorem iterate_succ (h : IsStronglySemiconj S Sh F G) (n : ℕ) (w : W) :
    Sh^[n + 1] w = F (S^[n] (G w)) := by
  rw [iterate_succ_apply, h.2, ← (Semiconj.iterate_right h.exercise_5_2_1.1 n) (G w)]

/-- **Lemma 5.2.1 (i)** (p. 161): `F` maps fixed points of `S` to fixed points of `Ŝ`. -/
theorem fixed_F (h : IsStronglySemiconj S Sh F G) {v : V} (hv : S v = v) : Sh (F v) = F v := by
  rw [← h.exercise_5_2_1.1 v, hv]

/-- **Lemma 5.2.1 (ii)**: `G` maps fixed points of `Ŝ` to fixed points of `S`. -/
theorem fixed_G (h : IsStronglySemiconj S Sh F G) {w : W} (hw : Sh w = w) : S (G w) = G w :=
  h.swap.fixed_F hw

/-- Unique fixed points transfer under `F`. -/
theorem isUniqueFixed (h : IsStronglySemiconj S Sh F G) {v : V} (hv : IsUniqueFixed S v) :
    IsUniqueFixed Sh (F v) := by
  refine ⟨h.fixed_F hv.1, fun w hw => ?_⟩
  have hGw : G w = v := hv.2 _ (h.fixed_G hw)
  rw [← hw, h.2, hGw]

/-- **Lemma 5.2.1 (iii)**: `S` has a unique fixed point iff `Ŝ` does. -/
theorem existsUnique_iff (h : IsStronglySemiconj S Sh F G) :
    (∃! v, S v = v) ↔ ∃! w, Sh w = w :=
  ⟨fun ⟨v, hv, hu⟩ => ⟨F v, (h.isUniqueFixed ⟨hv, hu⟩).1, (h.isUniqueFixed ⟨hv, hu⟩).2⟩,
    fun ⟨w, hw, hu⟩ => ⟨G w, (h.swap.isUniqueFixed ⟨hw, hu⟩).1, (h.swap.isUniqueFixed ⟨hw, hu⟩).2⟩⟩

variable [PartialOrder V] [PartialOrder W]

/-- One direction of Lemma 5.2.2 (i), with `F` and `G` order preserving. -/
theorem orderStable_mono (h : IsStronglySemiconj S Sh F G) (hF : Monotone F) (hG : Monotone G)
    (hS : OrderStable S) : OrderStable Sh := by
  obtain ⟨u, hu, -, hup, hdown⟩ := hS
  refine orderStable_of_up_down (h.fixed_F hu) (fun w hw => ?_) fun w hw => ?_
  · have h1 : G w ≤ S (G w) := by rw [← h.exercise_5_2_1.2 w]; exact hG hw
    have h2 : Sh w ≤ F u := by rw [h.2]; exact hF (hup _ h1)
    exact hw.trans h2
  · have h1 : S (G w) ≤ G w := by rw [← h.exercise_5_2_1.2 w]; exact hG hw
    have h2 : F u ≤ Sh w := by rw [h.2]; exact hF (hdown _ h1)
    exact h2.trans hw

/-- One direction of Lemma 5.2.2 (i), with `F` and `G` order reversing. -/
theorem orderStable_anti (h : IsStronglySemiconj S Sh F G) (hF : Antitone F) (hG : Antitone G)
    (hS : OrderStable S) : OrderStable Sh := by
  obtain ⟨u, hu, -, hup, hdown⟩ := hS
  refine orderStable_of_up_down (h.fixed_F hu) (fun w hw => ?_) fun w hw => ?_
  · have h1 : S (G w) ≤ G w := by rw [← h.exercise_5_2_1.2 w]; exact hG hw
    have h2 : Sh w ≤ F u := by rw [h.2]; exact hF (hdown _ h1)
    exact hw.trans h2
  · have h1 : G w ≤ S (G w) := by rw [← h.exercise_5_2_1.2 w]; exact hG hw
    have h2 : F u ≤ Sh w := by rw [h.2]; exact hF (hup _ h1)
    exact h2.trans hw

/-- **Lemma 5.2.2 (i)** (p. 162): if `F, G` are both order preserving or both order reversing,
`S` is order stable on `V` iff `Ŝ` is order stable on `V̂`. -/
theorem lemma_5_2_2_i (h : IsStronglySemiconj S Sh F G)
    (hFG : (Monotone F ∧ Monotone G) ∨ (Antitone F ∧ Antitone G)) :
    OrderStable S ↔ OrderStable Sh := by
  rcases hFG with ⟨hF, hG⟩ | ⟨hF, hG⟩
  · exact ⟨h.orderStable_mono hF hG, h.swap.orderStable_mono hG hF⟩
  · exact ⟨h.orderStable_anti hF hG, h.swap.orderStable_anti hG hF⟩

/-- Increasing limits of an orbit can be read off the shifted orbit. -/
theorem increasesTo_of_succ {f : ℕ → V} (hf : Monotone f) {v : V}
    (h : IsLUB (range fun n => f (n + 1)) v) : IncreasesTo f v :=
  ⟨hf, (isLUB_range_succ_iff hf v).1 h⟩

/-- Decreasing limits of an orbit can be read off the shifted orbit. -/
theorem decreasesTo_of_succ {f : ℕ → V} (hf : Antitone f) {v : V}
    (h : IsGLB (range fun n => f (n + 1)) v) : DecreasesTo f v := by
  refine ⟨hf, ?_⟩
  have key : lowerBounds (range fun n => f (n + 1)) = lowerBounds (range f) := by
    ext w
    simp only [mem_lowerBounds, Set.forall_mem_range]
    exact ⟨fun h n => (h n).trans (hf (Nat.le_succ n)), fun h n => h (n + 1)⟩
  rw [IsGLB, ← key]
  exact h

/-- Strong order stability passes from `Ŝ` to `S` when `F, G` are order preserving and `G`
carries increasing and decreasing limits. -/
theorem stronglyOrderStable_mono (h : IsStronglySemiconj S Sh F G) (hF : Monotone F)
    (hG : Monotone G) (hGu : OrderContinuous G) (hGd : OrderContinuousDown G)
    (hSh : StronglyOrderStable Sh) : StronglyOrderStable S := by
  obtain ⟨w₀, hw₀, huniq, hup, hdown⟩ := hSh
  have hfix := h.swap.isUniqueFixed ⟨hw₀, huniq⟩
  refine ⟨G w₀, hfix.1, hfix.2, fun v hv => ?_, fun v hv => ?_⟩
  · have hFv : F v ≤ Sh (F v) := by rw [← h.exercise_5_2_1.1 v]; exact hF hv
    obtain ⟨hm, hl⟩ := hup _ hFv
    have hmono : Monotone fun n => S^[n] v := monotone_nat_of_le_succ fun n => by
      have := (show Monotone S from fun a b hab => by rw [h.1, h.1]; exact hG (hF hab)).iterate n hv
      rwa [← iterate_succ_apply] at this
    refine increasesTo_of_succ hmono ?_
    have heq : (fun n => S^[n + 1] v) = G ∘ fun n => Sh^[n] (F v) :=
      funext fun n => h.swap.iterate_succ n v
    rw [heq]
    exact hGu _ _ hm hl
  · have hFv : Sh (F v) ≤ F v := by rw [← h.exercise_5_2_1.1 v]; exact hF hv
    obtain ⟨hm, hl⟩ := hdown _ hFv
    have hanti : Antitone fun n => S^[n] v := antitone_nat_of_succ_le fun n => by
      have := (show Monotone S from fun a b hab => by rw [h.1, h.1]; exact hG (hF hab)).iterate n hv
      rwa [← iterate_succ_apply] at this
    refine decreasesTo_of_succ hanti ?_
    have heq : (fun n => S^[n + 1] v) = G ∘ fun n => Sh^[n] (F v) :=
      funext fun n => h.swap.iterate_succ n v
    rw [heq]
    exact hGd _ _ hm hl

/-- Strong order stability passes from `Ŝ` to `S` when `F, G` are order reversing and `G` turns
decreasing limits into increasing ones and vice versa. -/
theorem stronglyOrderStable_anti (h : IsStronglySemiconj S Sh F G) (hF : Antitone F)
    (hG : Antitone G) (hGu : AntiContinuousUp G) (hGd : AntiContinuousDown G)
    (hSh : StronglyOrderStable Sh) : StronglyOrderStable S := by
  obtain ⟨w₀, hw₀, huniq, hup, hdown⟩ := hSh
  have hfix := h.swap.isUniqueFixed ⟨hw₀, huniq⟩
  have hSm : Monotone S := fun a b hab => by rw [h.1, h.1]; exact hG (hF hab)
  refine ⟨G w₀, hfix.1, hfix.2, fun v hv => ?_, fun v hv => ?_⟩
  · have hFv : Sh (F v) ≤ F v := by rw [← h.exercise_5_2_1.1 v]; exact hF hv
    obtain ⟨hm, hl⟩ := hdown _ hFv
    have hmono : Monotone fun n => S^[n] v := monotone_nat_of_le_succ fun n => by
      have := hSm.iterate n hv
      rwa [← iterate_succ_apply] at this
    refine increasesTo_of_succ hmono ?_
    have heq : (fun n => S^[n + 1] v) = G ∘ fun n => Sh^[n] (F v) :=
      funext fun n => h.swap.iterate_succ n v
    rw [heq]
    exact hGd _ _ hm hl
  · have hFv : F v ≤ Sh (F v) := by rw [← h.exercise_5_2_1.1 v]; exact hF hv
    obtain ⟨hm, hl⟩ := hup _ hFv
    have hanti : Antitone fun n => S^[n] v := antitone_nat_of_succ_le fun n => by
      have := hSm.iterate n hv
      rwa [← iterate_succ_apply] at this
    refine decreasesTo_of_succ hanti ?_
    have heq : (fun n => S^[n + 1] v) = G ∘ fun n => Sh^[n] (F v) :=
      funext fun n => h.swap.iterate_succ n v
    rw [heq]
    exact hGu _ _ hm hl

/-- **Lemma 5.2.2 (ii)** (p. 162), with order continuity read in both directions: if `F, G` are
order preserving and carry increasing and decreasing limits, or are order reversing and swap
them, then `S` is strongly order stable iff `Ŝ` is. -/
theorem lemma_5_2_2_ii (h : IsStronglySemiconj S Sh F G)
    (hFG : (Monotone F ∧ Monotone G ∧ OrderContinuous F ∧ OrderContinuousDown F ∧
        OrderContinuous G ∧ OrderContinuousDown G) ∨
      (Antitone F ∧ Antitone G ∧ AntiContinuousUp F ∧ AntiContinuousDown F ∧
        AntiContinuousUp G ∧ AntiContinuousDown G)) :
    StronglyOrderStable S ↔ StronglyOrderStable Sh := by
  rcases hFG with ⟨hF, hG, hFu, hFd, hGu, hGd⟩ | ⟨hF, hG, hFu, hFd, hGu, hGd⟩
  · exact ⟨h.swap.stronglyOrderStable_mono hG hF hFu hFd,
      h.stronglyOrderStable_mono hF hG hGu hGd⟩
  · exact ⟨h.swap.stronglyOrderStable_anti hG hF hFu hFd,
      h.stronglyOrderStable_anti hF hG hGu hGd⟩

/-- **Theorem 5.2.3** (p. 163), with `G` carrying increasing and decreasing limits: if `F, G`
are order preserving and `Ŝ` is strongly order stable with fixed point `w̄`, then `S` is strongly
order stable with fixed point `v̄ = Gw̄`, and `w ≼ Ŝw ⟹ GŜⁿw ↑ v̄` (5.16). -/
theorem theorem_5_2_3 (h : IsStronglySemiconj S Sh F G) (hF : Monotone F) (hG : Monotone G)
    (hGu : OrderContinuous G) (hGd : OrderContinuousDown G) {wbar : W}
    (hSh : StronglyOrderStable Sh) (hw : Sh wbar = wbar) :
    StronglyOrderStable S ∧ S (G wbar) = G wbar ∧
      ∀ w, w ≤ Sh w → IncreasesTo (fun n => G (Sh^[n] w)) (G wbar) := by
  refine ⟨h.stronglyOrderStable_mono hF hG hGu hGd hSh, h.fixed_G hw, fun w hle => ?_⟩
  obtain ⟨u, -, huniq, hup, -⟩ := hSh
  obtain ⟨hm, hl⟩ := hup w hle
  rw [huniq wbar hw]
  exact ⟨hG.comp hm, hGu _ _ hm hl⟩

/-- **Theorem 5.2.4** (p. 163), with `G` also turning increasing limits into decreasing ones: if
`F, G` are order reversing and `Ŝ` is strongly order stable with fixed point `w̄`, then `S` is
strongly order stable with fixed point `v̄ = Gw̄`, and `Ŝw ≼ w ⟹ GŜⁿw ↑ v̄` (5.17). -/
theorem theorem_5_2_4 (h : IsStronglySemiconj S Sh F G) (hF : Antitone F) (hG : Antitone G)
    (hGu : AntiContinuousUp G) (hGd : AntiContinuousDown G) {wbar : W}
    (hSh : StronglyOrderStable Sh) (hw : Sh wbar = wbar) :
    StronglyOrderStable S ∧ S (G wbar) = G wbar ∧
      ∀ w, Sh w ≤ w → IncreasesTo (fun n => G (Sh^[n] w)) (G wbar) := by
  refine ⟨h.stronglyOrderStable_anti hF hG hGu hGd hSh, h.fixed_G hw, fun w hle => ?_⟩
  obtain ⟨u, -, huniq, -, hdown⟩ := hSh
  obtain ⟨hm, hl⟩ := hdown w hle
  rw [huniq wbar hw]
  exact ⟨hG.comp hm, hGd _ _ hm hl⟩

end IsStronglySemiconj

end SargentStachurski.AdditionalApplications
