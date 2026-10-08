/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ContinuousTime.MarkovSemigroups
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Jump chains

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §10.1.4.2–§10.1.4.4 (pp. 323–329).

A jump chain is built from a rate function `λ : X → (0, ∞)` and a jump matrix `Π ∈ M(ℝ^X)`; its
intensity matrix is `Q(x, x') = λ(x)(Π(x, x') − I(x, x'))` (10.31).

* (10.31) is an intensity matrix; conversely (§10.1.4.4), an intensity matrix with nonzero rows is
  `λ(Π − I)` for `λ(x) = −Q(x, x)` and the stochastic `Π = I + Q/λ`.
* The integrated Kolmogorov backward equation: (10.32) and (10.36) are the same equation, by the
  change of variables `s = t − τ`.
* **Lemma 10.1.11**: a continuous solution of (10.32) has `P₀ = I` and `Ṗ_t = QP_t`; with
  Proposition 10.1.8 it is `e^{tQ}` (the analytic part of the proof of Proposition 10.1.9).
* Exercise 10.1.20: the inventory jump matrix (10.37) is stochastic.

Lemma 10.1.10, that the transition probabilities of the process built by Algorithm 10.1 satisfy
(10.32), is a statement about the law of a stochastic process and is not formalised (see
`docs/corrections.md`).
-/

open Finset Matrix Filter Topology Function Set

namespace SargentStachurski.ContinuousTime

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The intensity matrix (10.31) of a jump chain: `Q(x, x') = λ(x)(Π(x, x') − I(x, x'))`. -/
def jumpIntensity (lam : X → ℝ) (J : Matrix X X ℝ) : Matrix X X ℝ :=
  Matrix.of fun x x' => lam x * (J x x' - (1 : Matrix X X ℝ) x x')

/-- (10.31) is an intensity matrix when `λ ≥ 0` and `Π` is stochastic (p. 324). -/
theorem isIntensity_jumpIntensity {lam : X → ℝ} (hlam : ∀ x, 0 ≤ lam x) {J : Matrix X X ℝ}
    (hJ : IsMarkov J) : IsIntensity (jumpIntensity lam J) := by
  refine ⟨fun x x' hxx' => ?_, fun x => ?_⟩
  · simp only [jumpIntensity, Matrix.of_apply, Matrix.one_apply_ne hxx', sub_zero]
    exact mul_nonneg (hlam x) (hJ.nonneg x x')
  · simp only [jumpIntensity, Matrix.of_apply, ← Finset.mul_sum, Finset.sum_sub_distrib,
      hJ.rowsum x]
    simp [Matrix.one_apply]

/-- The jump matrix of an intensity matrix with nonzero rows (§10.1.4.4): `Π = I + Q/λ`,
`λ(x) = −Q(x, x)`. -/
noncomputable def intensityJumpChain (Q : Matrix X X ℝ) : Matrix X X ℝ :=
  Matrix.of fun x x' => (1 : Matrix X X ℝ) x x' + Q x x' / (-Q x x)

/-- §10.1.4.4 (p. 327): if `Q` is an intensity matrix with `Q(x, x) < 0` for all `x`, then
`Π = I + Q/λ` is stochastic and `Q = λ(Π − I)` with `λ(x) = −Q(x, x) > 0`. -/
theorem intensityJumpChain_spec {Q : Matrix X X ℝ} (hQ : IsIntensity Q) (hdiag : ∀ x, Q x x < 0) :
    IsMarkov (intensityJumpChain Q) ∧
      Q = jumpIntensity (fun x => -Q x x) (intensityJumpChain Q) := by
  have hlam : ∀ x, 0 < -Q x x := fun x => neg_pos.2 (hdiag x)
  refine ⟨⟨fun x x' => ?_, fun x => ?_⟩, ?_⟩
  · simp only [intensityJumpChain, Matrix.of_apply, Matrix.one_apply]
    by_cases hx : x = x'
    · subst hx
      simp only [↓reduceIte]
      rw [div_neg, div_self (hdiag x).ne]
      norm_num
    · simp only [hx, ↓reduceIte, zero_add]
      exact div_nonneg (hQ.1 x x' hx) (hlam x).le
  · simp only [intensityJumpChain, Matrix.of_apply, Finset.sum_add_distrib, ← Finset.sum_div,
      hQ.2 x, zero_div, add_zero]
    simp [Matrix.one_apply]
  · ext x x'
    simp only [jumpIntensity, intensityJumpChain, Matrix.of_apply, add_sub_cancel_left]
    field_simp [(hlam x).ne']
    rw [mul_div_assoc, div_self (hdiag x).ne, mul_one]

/-- The integrated backward equations (10.32) and (10.36) agree, by `s = t − τ`. -/
theorem integral_backward_eq (f : ℝ → ℝ) (c t : ℝ) :
    Real.exp (-t * c) * (∫ s in (0 : ℝ)..t, f s * Real.exp (s * c)) =
      ∫ τ in (0 : ℝ)..t, f (t - τ) * Real.exp (-τ * c) := by
  have h := intervalIntegral.integral_comp_sub_left (fun s => f s * Real.exp (s * c)) (a := 0)
    (b := t) t
  simp only [sub_self, sub_zero] at h
  rw [← h, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun τ _ => ?_
  rw [mul_left_comm, ← Real.exp_add]
  ring_nf

omit [DecidableEq X] in
/-- The fundamental theorem of calculus on `[0, ∞)`: for `f` continuous on `[0, ∞)`,
`u ↦ ∫₀^u f` has derivative `f(t)` within `[0, ∞)` at every `t ≥ 0`. -/
theorem hasDerivWithinAt_integral_Ici {f : ℝ → ℝ} (hf : ContinuousOn f (Ici 0)) {t : ℝ}
    (ht : 0 ≤ t) : HasDerivWithinAt (fun u => ∫ s in (0 : ℝ)..u, f s) (f t) (Ici 0) t := by
  have hint : IntervalIntegrable f MeasureTheory.volume 0 t :=
    (hf.mono fun s hs => le_trans (le_min le_rfl ht) hs.1).intervalIntegrable
  rcases ht.lt_or_eq with htpos | rfl
  · exact (intervalIntegral.integral_hasDerivAt_right hint
      ((hf.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi t htpos)
      (hf.continuousAt (Ici_mem_nhds htpos))).hasDerivWithinAt
  · exact intervalIntegral.integral_hasDerivWithinAt_right hint
      ((hf.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter_nhdsWithin measurableSet_Ioi 0)
      ((hf 0 (Set.mem_Ici.2 le_rfl)).mono Ioi_subset_Ici_self)

/-- **Lemma 10.1.11** (p. 325): if the entries of `t ↦ P_t` are continuous on `[0, ∞)` and satisfy
the integrated Kolmogorov backward equation (10.32), then `P₀ = I` and `Ṗ_t = QP_t` on `[0, ∞)`,
for `Q = λ(Π − I)`. -/
theorem backward_of_integrated {lam : X → ℝ} {J : Matrix X X ℝ} {P : ℝ → Matrix X X ℝ}
    (hcont : ∀ x x', ContinuousOn (fun t => P t x x') (Ici 0))
    (hint : ∀ t, 0 ≤ t → ∀ x x', P t x x' = Real.exp (-t * lam x) * (1 : Matrix X X ℝ) x x' +
      lam x * ∫ τ in (0 : ℝ)..t, (J * P (t - τ)) x x' * Real.exp (-τ * lam x)) :
    P 0 = 1 ∧ ∀ t, 0 ≤ t → ∀ x x', HasDerivWithinAt (fun s => P s x x')
      ((jumpIntensity lam J * P t) x x') (Ici 0) t := by
  refine ⟨?_, fun t ht x x' => ?_⟩
  · ext x x'
    rw [hint 0 le_rfl]
    simp
  -- rewrite (10.32) as (10.36)
  set h : ℝ → ℝ := fun s => (J * P s) x x' * Real.exp (s * lam x)
  have h36 : ∀ s, 0 ≤ s → P s x x' = Real.exp (-s * lam x) *
      ((1 : Matrix X X ℝ) x x' + lam x * ∫ σ in (0 : ℝ)..s, h σ) := fun s hs => by
    rw [hint s hs x x', mul_add, mul_left_comm (Real.exp _), integral_backward_eq]
  have hhcont : ContinuousOn h (Ici 0) := by
    refine ContinuousOn.mul ?_
      (Real.continuous_exp.comp (continuous_id.mul continuous_const)).continuousOn
    simp only [Matrix.mul_apply]
    exact continuousOn_finsetSum _ fun z _ => continuousOn_const.mul (hcont z x')
  have hG := hasDerivWithinAt_integral_Ici hhcont ht
  have hE : HasDerivWithinAt (fun s => Real.exp (-s * lam x)) (-lam x * Real.exp (-t * lam x))
      (Ici 0) t := by
    have h1 : HasDerivAt (fun s : ℝ => -s * lam x) (-lam x) t := by
      simpa using (hasDerivAt_id t).neg.mul_const (lam x)
    exact (h1.exp.congr_deriv (by ring)).hasDerivWithinAt
  have hF := hE.mul ((hG.const_mul (lam x)).const_add ((1 : Matrix X X ℝ) x x'))
  refine (hF.congr (fun s hs => h36 s hs) (h36 t ht)).congr_deriv ?_
  -- `−λP_t + λ(ΠP_t) = (λ(Π − I)P_t)(x, x')`
  have hexp : Real.exp (-t * lam x) * Real.exp (t * lam x) = 1 := by
    rw [← Real.exp_add]
    simp
  have hR : ∑ j, lam x * (J x j - (1 : Matrix X X ℝ) x j) * P t j x' =
      lam x * ∑ j, J x j * P t j x' - lam x * P t x x' := by
    have e1 : ∑ j, lam x * (J x j - (1 : Matrix X X ℝ) x j) * P t j x' =
        ∑ j, lam x * (J x j * P t j x') - ∑ j, lam x * ((1 : Matrix X X ℝ) x j * P t j x') := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_eq_single (f := fun j => (1 : Matrix X X ℝ) x j * P t j x') x
      (fun j _ hj => by rw [Matrix.one_apply_ne' hj, zero_mul]) (by simp), Matrix.one_apply_eq,
      one_mul]
  have h36t := h36 t ht
  simp only [h, Matrix.mul_apply] at h36t
  simp only [h, jumpIntensity, Matrix.mul_apply, Matrix.of_apply]
  rw [hR]
  linear_combination (lam x * ∑ j, J x j * P t j x') * hexp + lam x * h36t

/-- **Proposition 10.1.9**, analytic part (p. 324): a continuous solution of the integrated backward
equation (10.32) is the Markov semigroup `P_t = e^{tQ}` with `Q = λ(Π − I)`. -/
theorem eq_exp_of_integrated {lam : X → ℝ} {J : Matrix X X ℝ} {P : ℝ → Matrix X X ℝ}
    (hcont : ∀ x x', ContinuousOn (fun t => P t x x') (Ici 0))
    (hint : ∀ t, 0 ≤ t → ∀ x x', P t x x' = Real.exp (-t * lam x) * (1 : Matrix X X ℝ) x x' +
      lam x * ∫ τ in (0 : ℝ)..t, (J * P (t - τ)) x x' * Real.exp (-τ * lam x))
    {t : ℝ} (ht : 0 ≤ t) : P t = NormedSpace.exp (t • jumpIntensity lam J) := by
  obtain ⟨h0, hd⟩ := backward_of_integrated hcont hint
  exact eq_exp_of_backward h0 hd ht

/-! ### Inventory dynamics (§10.1.4.3) -/

/-- The inventory jump matrix (10.37) on `X = {0, …, b}`: from `0` the firm restocks to `b`;
from `0 < x ≤ b` inventory falls to `x − U ∧ x`, where `P{U = k} = φ(k)`, `k ≥ 1`. -/
noncomputable def inventoryJump (b : ℕ) (φ : ℕ → ℝ) (x y : Fin (b + 1)) : ℝ :=
  if (x : ℕ) = 0 then (if (y : ℕ) = b then 1 else 0)
  else if (x : ℕ) ≤ y then 0
  else if 0 < (y : ℕ) then φ (x - y)
  else 1 - ∑ k ∈ range x, φ k

/-- **Exercise 10.1.20** (p. 326): for a distribution `φ` of `U` on `{1, 2, …}`, the inventory jump
matrix `Π` is stochastic. -/
theorem isMarkov_inventoryJump (b : ℕ) {φ : ℕ → ℝ} (hφ0 : φ 0 = 0) (hφ : ∀ k, 0 ≤ φ k)
    (hsum : HasSum φ 1) : IsMarkov (Matrix.of (inventoryJump b φ)) := by
  have hS : ∀ n, ∑ k ∈ range n, φ k ≤ 1 := fun n =>
    sum_le_hasSum (range n) (fun k _ => hφ k) hsum
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · simp only [Matrix.of_apply, inventoryJump]
    split_ifs <;> first | exact hφ _ | linarith [hS x]
  · simp only [Matrix.of_apply, inventoryJump]
    rw [Fin.sum_univ_eq_sum_range (fun y => if (x : ℕ) = 0 then (if y = b then 1 else 0)
      else if (x : ℕ) ≤ y then 0 else if 0 < y then φ (x - y) else 1 - ∑ k ∈ range x, φ k) (b + 1)]
    by_cases hx : (x : ℕ) = 0
    · simp [hx]
    · have hxb : (x : ℕ) ≤ b := Nat.lt_succ_iff.1 x.2
      have hsplit : ∀ y, (if (x : ℕ) = 0 then (if y = b then (1 : ℝ) else 0)
          else if (x : ℕ) ≤ y then 0 else if 0 < y then φ (x - y)
          else 1 - ∑ k ∈ range x, φ k) =
          (if y = 0 then 1 - ∑ k ∈ range x, φ k else 0) +
            (if y ∈ Finset.Ico 1 (x : ℕ) then φ (x - y) else 0) := fun y => by
        simp only [hx, ↓reduceIte, Finset.mem_Ico]
        by_cases hy0 : y = 0
        · subst hy0
          have : ¬ (x : ℕ) ≤ 0 := by omega
          simp [this]
        · by_cases hxy : (x : ℕ) ≤ y
          · simp [hxy, hy0]
          · simp [hxy, hy0, show y < (x : ℕ) by omega, Nat.pos_of_ne_zero hy0]
      simp only [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range,
        show 0 < b + 1 by omega, ↓reduceIte]
      rw [← Finset.sum_filter, show (Finset.range (b + 1)).filter (· ∈ Finset.Ico 1 (x : ℕ)) =
          Finset.Ico 1 (x : ℕ) by
        ext y
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        omega]
      rw [Finset.sum_Ico_reflect φ 1 (show (x : ℕ) ≤ x + 1 by omega)]
      rw [show (x : ℕ) + 1 - x = 1 by omega, show (x : ℕ) + 1 - 1 = x by omega,
        Finset.sum_range_eq_add_Ico φ (Nat.pos_of_ne_zero hx), hφ0, zero_add]
      ring

end SargentStachurski.ContinuousTime
