/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Fintype.Lattice

/-!
# The probabilities of the secretary problem

Copied from `EconomicDynamics/MarkovDecisionProcesses` (module `Secretary`),
with the namespace renamed.

Miao, pp. 148–149. `N` objects of distinct quality are observed in a uniformly random order: a
permutation `σ` of `Fin N`, `σ i` being the quality rank (`0` = best) of the object observed at
position `i` (the `(i + 1)`-th object). For the `k`-th object (`1 ≤ k ≤ N`, position `k − 1`):

* `bestOfFirst N k`: it is the best of the first `k` objects; `card_bestOfFirst`: this has
  probability `1/k` (so `Q_{t+1}(z, 1) = 1/(t + 1)`, p. 148, as a marginal probability);
* `bestOfAll N k`: it is the best of all; `card_bestOfAll`: probability `1/N`;
* `secretary_prob`: **Miao, p. 149**, `Pr(best of N | best of first k) = Pr(best of N) /
  Pr(best of first k) = (1/N)/(1/k) = k/N`.

Not formalised: that the indicators of "best so far" are independent (the Markov property of the
book's state process, with a transition function that does not depend on the current state); only
the marginal probabilities are proved.
-/

namespace Miao.FiniteHorizonDP

open Equiv

/-- An equal-size partition: if the `m` pieces of a partition of a finite type have the same
cardinality, each has `1/m` of the elements. -/
theorem card_mul_of_equal_partition {α : Type*} [Fintype α] {m : ℕ}
    (E : Fin m → Finset α) (hdisj : ∀ i j, i ≠ j → Disjoint (E i) (E j))
    (hcov : ∀ x, ∃ i, x ∈ E i) (heq : ∀ i j, (E i).card = (E j).card) (i₀ : Fin m) :
    (E i₀).card * m = Fintype.card α := by
  classical
  have hu : (Finset.univ : Finset α) = Finset.univ.biUnion E := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_biUnion, true_and, true_iff]
    exact hcov x
  rw [← Finset.card_univ, hu, Finset.card_biUnion fun i _ j _ hij => hdisj i j hij]
  rw [Finset.sum_congr rfl fun i _ => heq i i₀, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_comm]

/-- The `k`-th object is the best of the first `k` (position `p = k − 1`). -/
def bestOfFirst (N : ℕ) (p : Fin N) : Finset (Perm (Fin N)) :=
  Finset.univ.filter fun σ => ∀ j : Fin N, j.val ≤ p.val → σ p ≤ σ j

/-- The object at position `p` is the best of all `N`. -/
def bestOfAll (N : ℕ) (p : Fin N) : Finset (Perm (Fin N)) :=
  Finset.univ.filter fun σ => σ p = ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) p.2⟩

/-- Miao, p. 149: the object at position `p` is the best of all with probability `1/N`:
`#{σ : σ(p) = 0} · N = N!`. -/
theorem card_bestOfAll (N : ℕ) (p : Fin N) :
    (bestOfAll N p).card * N = Fintype.card (Perm (Fin N)) := by
  let E : Fin N → Finset (Perm (Fin N)) := fun v => Finset.univ.filter fun σ => σ p = v
  have h0 : bestOfAll N p = E ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) p.2⟩ := rfl
  rw [h0]
  refine card_mul_of_equal_partition E (fun v w hvw => ?_) (fun σ => ⟨σ p, by simp [E]⟩)
    (fun v w => ?_) _
  · refine Finset.disjoint_left.2 fun σ h1 h2 => hvw ?_
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    rw [← h1, ← h2]
  · refine Finset.card_nbij' (fun σ => swap v w * σ) (fun σ => swap v w * σ) ?_ ?_ ?_ ?_
    · intro σ hσ
      have hσ' : σ p = v := by simpa [E] using hσ
      simp [E, Perm.mul_apply, hσ']
    · intro σ hσ
      have hσ' : σ p = w := by simpa [E] using hσ
      simp [E, Perm.mul_apply, hσ']
    · intro σ _
      simp [← mul_assoc]
    · intro σ _
      simp [← mul_assoc]

theorem swap_val_le {N : ℕ} {a b j : Fin N} {p : ℕ} (ha : a.val ≤ p) (hb : b.val ≤ p)
    (hj : j.val ≤ p) : (swap a b j).val ≤ p := by
  rw [swap_apply_def]
  split_ifs <;> assumption

/-- Miao, p. 148: the object at position `p` (the `(p + 1)`-th) is the best of the first `p + 1`
with probability `1/(p + 1)`: `#{σ : σ(p) ≤ σ(j) for j ≤ p} · (p + 1) = N!`. -/
theorem card_bestOfFirst (N : ℕ) (p : Fin N) :
    (bestOfFirst N p).card * (p.val + 1) = Fintype.card (Perm (Fin N)) := by
  let ι : Fin (p.val + 1) → Fin N := fun i => ⟨i.val, by omega⟩
  have hι : ∀ i, (ι i).val ≤ p.val := fun i => Nat.lt_succ_iff.1 i.2
  let E : Fin (p.val + 1) → Finset (Perm (Fin N)) := fun i =>
    Finset.univ.filter fun σ => ∀ j : Fin N, j.val ≤ p.val → σ (ι i) ≤ σ j
  have h0 : bestOfFirst N p = E (Fin.last p.val) := by
    have : ι (Fin.last p.val) = p := Fin.ext rfl
    simp only [bestOfFirst, E, this]
  rw [h0]
  refine card_mul_of_equal_partition E (fun i i' hii' => ?_) (fun σ => ?_) (fun i i' => ?_) _
  · refine Finset.disjoint_left.2 fun σ h1 h2 => hii' ?_
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    have := le_antisymm (h1 _ (hι i')) (h2 _ (hι i))
    have h' := congrArg Fin.val (σ.injective this)
    exact Fin.ext h'
  · obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun j : Fin N =>
      j.val ≤ p.val) σ ⟨p, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm hmin
    refine ⟨⟨m.val, Nat.lt_succ_iff.2 hm⟩, ?_⟩
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun j hj => hmin j hj
  · refine Finset.card_nbij' (fun σ => σ * swap (ι i) (ι i')) (fun σ => σ * swap (ι i) (ι i'))
      ?_ ?_ ?_ ?_
    · intro σ hσ
      simp only [E, Finset.coe_filter, Finset.mem_univ, true_and] at hσ ⊢
      intro j hj
      simp only [Perm.mul_apply, swap_apply_right]
      exact hσ _ (swap_val_le (hι i) (hι i') hj)
    · intro σ hσ
      simp only [E, Finset.coe_filter, Finset.mem_univ, true_and] at hσ ⊢
      intro j hj
      simp only [Perm.mul_apply, swap_apply_left]
      exact hσ _ (swap_val_le (hι i) (hι i') hj)
    · intro σ _
      simp [mul_assoc]
    · intro σ _
      simp [mul_assoc]

/-- The best of all is the best of the first `k`. -/
theorem bestOfAll_subset (N : ℕ) (p : Fin N) : bestOfAll N p ⊆ bestOfFirst N p := by
  intro σ hσ
  simp only [bestOfAll, bestOfFirst, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
  intro j _
  rw [hσ, Fin.le_iff_val_le_val]
  exact Nat.zero_le _

/-- **Miao, p. 149.** For the `k`-th object (`k = p + 1`): `Pr(best of first k) = 1/k`,
`Pr(best of N) = 1/N`, and `Pr(best of N | best of first k) = Pr(best of N)/Pr(best of first k)
= k/N` (uniform probability on the `N!` orders). -/
theorem secretary_prob (N : ℕ) (p : Fin N) :
    ((bestOfFirst N p).card : ℝ) / Fintype.card (Perm (Fin N)) = 1 / (p.val + 1) ∧
      ((bestOfAll N p).card : ℝ) / Fintype.card (Perm (Fin N)) = 1 / N ∧
      ((bestOfAll N p ∩ bestOfFirst N p).card : ℝ) / (bestOfFirst N p).card =
        (p.val + 1) / N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_le_of_lt (Nat.zero_le _) p.2
  have hF : (0 : ℝ) < Fintype.card (Perm (Fin N)) := by exact_mod_cast Fintype.card_pos
  have hB := card_bestOfFirst N p
  have hA := card_bestOfAll N p
  have hB' : ((bestOfFirst N p).card : ℝ) * (p.val + 1) = Fintype.card (Perm (Fin N)) := by
    exact_mod_cast hB
  have hA' : ((bestOfAll N p).card : ℝ) * N = Fintype.card (Perm (Fin N)) := by
    exact_mod_cast hA
  have hBpos : (0 : ℝ) < (bestOfFirst N p).card := by
    have : 0 < (bestOfFirst N p).card := Nat.pos_of_ne_zero fun h => by
      rw [h, zero_mul] at hB
      exact (Fintype.card_pos (α := Perm (Fin N))).ne hB
    exact_mod_cast this
  have hApos : (0 : ℝ) < (bestOfAll N p).card := by
    have : 0 < (bestOfAll N p).card := Nat.pos_of_ne_zero fun h => by
      rw [h, zero_mul] at hA
      exact (Fintype.card_pos (α := Perm (Fin N))).ne hA
    exact_mod_cast this
  rw [Finset.inter_eq_left.2 (bestOfAll_subset N p)]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hB']
    field_simp
  · rw [← hA']
    field_simp
  · rw [div_eq_div_iff hBpos.ne' hN.ne', hA', ← hB', mul_comm]

end Miao.FiniteHorizonDP
