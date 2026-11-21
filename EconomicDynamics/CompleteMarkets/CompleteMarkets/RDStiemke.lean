/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.Order.Compact

/-!
# Stiemke's lemma

Miao, proof of Theorem 13.4.2, p. 429, cites Stiemke's Lemma: a subspace `L ⊆ ℝᴷ` contains no
nonzero nonnegative vector iff there is a strictly positive `q ∈ ℝᴷ` orthogonal to `L`. It is
proved here from the compact–closed Hahn–Banach separation theorem, separating the simplex from
`L`.
-/

namespace Miao.CompleteMarkets

/-- The standard simplex `{v ≥ 0 : ∑ₖ vₖ = 1}` in `ℝᴷ`. -/
def rd_simplex (K : Type*) [Fintype K] : Set (K → ℝ) := {v | (∀ k, 0 ≤ v k) ∧ ∑ k, v k = 1}

variable {K : Type*} [Fintype K]

/-- The simplex is convex. -/
theorem rd_simplex_convex : Convex ℝ (rd_simplex K) := by
  refine fun f hf g hg a b ha hb hab => ⟨fun x => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hf.1 x)) (mul_nonneg hb (hg.1 x))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hf.2, hg.2, mul_one,
      mul_one, hab]

/-- The simplex is compact. -/
theorem rd_simplex_compact : IsCompact (rd_simplex K) := by
  refine IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : K → ℝ)) (b := 1)) ?_ ?_
  · have : rd_simplex K = (⋂ k, {v : K → ℝ | 0 ≤ v k}) ∩ {v | ∑ k, v k = 1} := by
      ext v
      simp [rd_simplex]
    rw [this]
    exact (isClosed_iInter fun k => isClosed_le continuous_const (continuous_apply k)).inter
      (isClosed_eq (by fun_prop) continuous_const)
  · intro v hv
    refine ⟨fun k => hv.1 k, fun k => ?_⟩
    have := Finset.single_le_sum (f := v) (fun k _ => hv.1 k) (Finset.mem_univ k)
    rw [hv.2] at this
    exact this

/-- **Stiemke's Lemma** (Miao, p. 429). A subspace `L` of `ℝᴷ` contains no nonzero nonnegative
vector iff some strictly positive `q` is orthogonal to `L`. -/
theorem rd_stiemke (L : Submodule ℝ (K → ℝ)) :
    (∀ v ∈ L, (∀ k, 0 ≤ v k) → v = 0) ↔
      ∃ q : K → ℝ, (∀ k, 0 < q k) ∧ ∀ v ∈ L, ∑ k, q k * v k = 0 := by
  classical
  constructor
  · intro hL
    have hdisj : Disjoint (rd_simplex K) (L : Set (K → ℝ)) := by
      rw [Set.disjoint_left]
      intro v hv hvL
      have h0 := hL v hvL hv.1
      have := hv.2
      rw [h0] at this
      simp at this
    obtain ⟨φ, u, w, hu, huw, hw⟩ := geometric_hahn_banach_compact_closed rd_simplex_convex
      rd_simplex_compact L.convex (Submodule.closed_of_finiteDimensional L) hdisj
    have hw0 : w < 0 := by simpa using hw 0 L.zero_mem
    have hφL : ∀ b ∈ L, φ b = 0 := by
      intro b hb
      by_contra hne
      have := hw (((w - 1) / φ b) • b) (L.smul_mem _ hb)
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at this
      linarith
    refine ⟨fun k => -φ (fun j => if k = j then 1 else 0), fun k => ?_, fun v hv => ?_⟩
    · have hmem : (fun j => if k = j then (1 : ℝ) else 0) ∈ rd_simplex K := by
        refine ⟨fun j => by dsimp only; split_ifs <;> norm_num, ?_⟩
        simp
      have := hu _ hmem
      linarith
    · have hv' := hφL v hv
      rw [pi_eq_sum_univ v, map_sum] at hv'
      simp only [map_smul, smul_eq_mul] at hv'
      have : ∑ k, -φ (fun j => if k = j then (1 : ℝ) else 0) * v k =
          -∑ k, v k * φ (fun j => if k = j then 1 else 0) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [this, hv', neg_zero]
  · rintro ⟨q, hq, hqL⟩ v hv hnn
    by_contra hne
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
    have hpos : 0 < v k := lt_of_le_of_ne (hnn k) (Ne.symm hk)
    have : 0 < ∑ k, q k * v k :=
      Finset.sum_pos' (fun j _ => mul_nonneg (hq j).le (hnn j))
        ⟨k, Finset.mem_univ k, mul_pos (hq k) hpos⟩
    rw [hqL v hv] at this
    exact lt_irrefl 0 this

end Miao.CompleteMarkets
