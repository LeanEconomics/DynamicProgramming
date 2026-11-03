/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OwenScrambling.ScrambleGain

/-!
# The two-dimensional Hammersley net is a `(0,m,2)`-net in every base

To show the hypotheses of the scrambled-net theorems can be met in more than one dimension: the
Hammersley point set `{(i/b^m, φ_b(i)) : i < b^m}`, with `φ_b` the radical inverse (digits
reversed), is a `(0,m,2)`-net in base `b` for every `b ≥ 2` and `m` (Niederreiter 1992).

## Main results

* `revDigits`, `cellEnum`, `hammersleyDigits`: the net as digit points.
* `eq_of_agree_of_agree_rev`: `r₀` leading digits of `w` and `r₁` leading digits of its reversal,
  `r₀ + r₁ = m`, determine `w`.
* `isNet_hammersley`: the Hammersley net is a `(0,m,2)`-net in base `b`.
-/

namespace RQMCMarkov.OwenScrambling

open Finset

variable {b : ℕ}

/-- The digit string read backwards. -/
def revDigits {m : ℕ} (w : Fin m → Fin b) : Fin m → Fin b := fun k ↦ w (Fin.rev k)

/-- The enumeration of the `m`-digit strings by their cell index `0, …, b^m - 1`. -/
noncomputable def cellEnum (hb : 0 < b) (m : ℕ) : Fin (b ^ m) ≃ (Fin m → Fin b) :=
  (Equiv.ofBijective (cellFin (D := m) hb) (cellFin_bijective hb)).symm

/-- The **Hammersley net** in base `b` with `b^m` points: point `i` has the digits of `i/b^m` in
coordinate `0` and the same digits reversed in coordinate `1` (the radical inverse). -/
noncomputable def hammersleyDigits (hb : 0 < b) (m : ℕ) : Fin (b ^ m) → Fin 2 → Fin m → Fin b :=
  fun i ↦ ![cellEnum hb m i, revDigits (cellEnum hb m i)]

/-- A string is determined by its first `r₀` digits and the first `r₁` digits of its reversal
when `r₀ + r₁ = m`. -/
theorem eq_of_agree_of_agree_rev {m r₀ r₁ : ℕ} (hr : r₀ + r₁ = m) {w w' : Fin m → Fin b}
    (h₀ : Agree r₀ w w') (h₁ : Agree r₁ (revDigits w) (revDigits w')) : w = w' := by
  funext k
  by_cases hk : (k : ℕ) < r₀
  · exact h₀ k hk
  · have hrev : ((Fin.rev k : Fin m) : ℕ) < r₁ := by
      rw [Fin.val_rev]
      omega
    have := h₁ (Fin.rev k) hrev
    simp only [revDigits, Fin.rev_rev] at this
    exact this

/-- **The Hammersley net is a `(0,m,2)`-net in base `b`** (every `b ≥ 2`): each elementary box
of volume `b^{-m}` contains exactly one point. -/
theorem isNet_hammersley (hb : 1 < b) (m : ℕ) :
    IsNet b 0 m fun i j ↦ digitPoint (hammersleyDigits (lt_trans Nat.zero_lt_one hb) m i j) 0 := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  refine ⟨Nat.zero_le m, rfl, fun i j ↦ digitPoint_mem_Ico hb0 _ ⟨le_rfl, one_pos⟩, ?_⟩
  intro r a hr ha
  rw [Nat.sub_zero, Fin.sum_univ_two] at hr
  have hrD : ∀ j, r j ≤ m := by
    intro j
    fin_cases j
    · exact le_trans (Nat.le_add_right _ _) hr.le
    · exact le_trans (Nat.le_add_left _ _) hr.le
  rw [pow_zero]
  set Φ : (Fin m → Fin b) → Fin (b ^ r 0) × Fin (b ^ r 1) := fun w ↦
    (⟨prefixVal w (r 0), prefixVal_lt hb0 _ _⟩,
      ⟨prefixVal (revDigits w) (r 1), prefixVal_lt hb0 _ _⟩) with hΦ
  have hinj : Function.Injective Φ := by
    intro w w' h
    simp only [hΦ, Prod.mk.injEq, Fin.mk.injEq] at h
    exact eq_of_agree_of_agree_rev hr ((prefixVal_eq_iff_agree hb0 (hrD 0) _ _).1 h.1)
      ((prefixVal_eq_iff_agree hb0 (hrD 1) _ _).1 h.2)
  have hbij : Function.Bijective Φ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod]
    rw [← pow_add, hr]
  obtain ⟨w₀, hw₀⟩ := hbij.2 (⟨a 0, ha 0⟩, ⟨a 1, ha 1⟩)
  have hiff : ∀ i, boxIndex b r (fun j ↦ digitPoint (hammersleyDigits hb0 m i j) 0) = a ↔
      cellEnum hb0 m i = w₀ := by
    intro i
    rw [boxIndex_digitPoint hb0 hrD, funext_iff, Fin.forall_fin_two]
    simp only [hammersleyDigits, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    constructor
    · rintro ⟨h0, h1⟩
      refine hinj (hw₀.symm ▸ ?_)
      simp only [hΦ, Prod.mk.injEq, Fin.mk.injEq]
      exact ⟨h0, h1⟩
    · rintro rfl
      have := congrArg (fun p ↦ ((p.1 : ℕ), (p.2 : ℕ))) hw₀
      simp only [hΦ, Prod.mk.injEq] at this
      exact this
  rw [Finset.filter_congr fun i _ ↦ hiff i, Finset.card_eq_one]
  refine ⟨(cellEnum hb0 m).symm w₀, ?_⟩
  ext i
  rw [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨-, h⟩
    rw [← h, Equiv.symm_apply_apply]
  · rintro rfl
    exact ⟨Finset.mem_univ _, Equiv.apply_symm_apply _ _⟩

end RQMCMarkov.OwenScrambling
