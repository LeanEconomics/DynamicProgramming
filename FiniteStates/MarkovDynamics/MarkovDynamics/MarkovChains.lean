/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDynamics.Basics
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Markov chains on a finite state space

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §3.1.1 and §3.1.2
(pp. 81–88).

A `P`-Markov chain is a process whose next-state distribution given the
history is `P(Xₜ, ·)`, (3.1). What the chapter proves about such chains is
expressed through `P` alone: the `k`-step transition probabilities are the
entries of `Pᵏ`, (3.2), written here as a sum of path probabilities, with the
law of total probability `Pᵏ⁺¹(x, x') = ∑_z Pᵏ(x, z)P(z, x')` of Exercise
3.1.2; the marginal distributions evolve by `ψₜ₊₁ = ψₜP`, (3.3)–(3.5);
expectations are `E h(Xₜ) = ⟨ψ₀Pᵗ, h⟩`, (3.6), Exercise 3.1.4; stationary
distributions are fixed points of `ψ ↦ ψP`. Lemma 3.1.1 characterises
irreducibility. The ergodic theorem (Theorem 3.1.2) is cited by the book from
Brémaud (2020) and is not claimed here: it is a statement about almost every
sample path, which the finite-dimensional description does not reach.
-/

open Finset Matrix

namespace SargentStachurski.MarkovDynamics

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The probability of a path `z₀, z₁, …, zₖ` under `P`: `∏ P(zᵢ, zᵢ₊₁)` (Algorithm 3.1). -/
def pathProb (P : Matrix X X ℝ) {k : ℕ} (z : Fin (k + 1) → X) : ℝ :=
  ∏ i : Fin k, P (z i.castSucc) (z i.succ)

/-- Paths of length `k` from `x` to `x'`. -/
def paths (k : ℕ) (x x' : X) : Finset (Fin (k + 1) → X) :=
  univ.filter fun z => z 0 = x ∧ z (Fin.last k) = x'

omit [Fintype X] [DecidableEq X] in
/-- Appending a step to a path multiplies its probability by the transition probability. -/
theorem pathProb_snoc (P : Matrix X X ℝ) {k : ℕ} (w : Fin (k + 1) → X) (x' : X) :
    pathProb P (Fin.snoc w x' : Fin (k + 2) → X) = pathProb P w * P (w (Fin.last k)) x' := by
  unfold pathProb
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine prod_congr rfl fun i _ => ?_
    rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc]

/-- (3.2), p. 85: `Pᵏ(x, x')` is the probability that a `P`-Markov chain started at `x` is at
`x'` after `k` steps, the total probability of all paths from `x` to `x'` of length `k`. -/
theorem pow_apply_eq_sum_paths (P : Matrix X X ℝ) (k : ℕ) (x x' : X) :
    (P ^ k) x x' = ∑ z ∈ paths k x x', pathProb P z := by
  induction k generalizing x' with
  | zero =>
    -- the only path of length `0` is the constant path, present iff `x = x'`
    simp only [pow_zero, Matrix.one_apply, paths, pathProb, Fin.last_zero]
    by_cases hxx : x = x'
    · subst hxx
      have h1 : (if x = x then (1 : ℝ) else 0) = 1 := by simp
      rw [h1]
      have : (univ.filter fun z : Fin 1 → X => z 0 = x ∧ z 0 = x) = {fun _ => x} := by
        ext z
        simp only [mem_filter, mem_univ, true_and, mem_singleton, and_self]
        constructor
        · intro h; funext i; rw [Subsingleton.elim i 0]; exact h
        · rintro rfl; rfl
      rw [this, sum_singleton]
      simp
    · have h1 : (if x = x' then (1 : ℝ) else 0) = 0 := by simp [hxx]
      rw [h1]
      refine (sum_eq_zero fun z hz => ?_).symm
      exfalso
      simp only [mem_filter, mem_univ, true_and] at hz
      exact hxx (hz.1.symm.trans hz.2)
  | succ k ih =>
    -- `Pᵏ⁺¹(x, x') = ∑_z Pᵏ(x, z) P(z, x')`; a path of length `k + 1` from `x` to `x'` is a path of
    -- length `k` from `x` to some `z`, followed by the step `z → x'`
    rw [pow_succ, Matrix.mul_apply]
    have hsplit : ∀ z, (P ^ k) x z * P z x' = ∑ w ∈ paths k x z, pathProb P w * P z x' := by
      intro z
      rw [ih z, sum_mul]
    simp only [hsplit]
    have hfib : ∀ z, paths k x z =
        (univ.filter fun w : Fin (k + 1) → X => w 0 = x).filter (fun w => w (Fin.last k) = z) := by
      intro z
      ext w
      simp [paths]
    have hz : ∀ z, ∑ w ∈ paths k x z, pathProb P w * P z x' =
        ∑ w ∈ (univ.filter fun w : Fin (k + 1) → X => w 0 = x).filter
          (fun w => w (Fin.last k) = z), pathProb P w * P (w (Fin.last k)) x' := by
      intro z
      rw [hfib]
      exact sum_congr rfl fun w hw => by rw [(mem_filter.1 hw).2]
    simp only [hz]
    rw [Finset.sum_fiberwise (univ.filter fun w : Fin (k + 1) → X => w 0 = x)
      (fun w => w (Fin.last k)) (fun w => pathProb P w * P (w (Fin.last k)) x')]
    -- the paths of length `k + 1` from `x` to `x'` are the images of the paths from `x` under
    -- `w ↦ snoc w x'`
    have himage : paths (k + 1) x x' =
        (univ.filter fun w : Fin (k + 1) → X => w 0 = x).image
          (fun w => (Fin.snoc w x' : Fin (k + 2) → X)) := by
      ext v
      simp only [paths, mem_filter, mem_univ, true_and, mem_image]
      constructor
      · rintro ⟨h0, hl⟩
        refine ⟨Fin.init v, ?_, ?_⟩
        · simpa [Fin.init] using h0
        · rw [← hl]
          exact Fin.snoc_init_self v
      · rintro ⟨w, hw, rfl⟩
        refine ⟨?_, Fin.snoc_last _ _⟩
        change (Fin.snoc w x' : Fin (k + 2) → X) 0 = x
        rw [← Fin.castSucc_zero, Fin.snoc_castSucc]
        exact hw
    rw [himage, sum_image]
    · exact sum_congr rfl fun w _ => (pathProb_snoc P w x').symm
    · intro w _ v _ h
      have := congrArg Fin.init h
      rwa [Fin.init_snoc, Fin.init_snoc] at this

/-- Exercise 3.1.2 (p. 85), the inductive step: `Pᵏ⁺¹(x, x') = ∑_z Pᵏ(x, z) P(z, x')` is the law
of total probability for the `(k + 1)`-step transition. -/
theorem pow_succ_apply (P : Matrix X X ℝ) (k : ℕ) (x x' : X) :
    (P ^ (k + 1)) x x' = ∑ z, (P ^ k) x z * P z x' := by
  rw [pow_succ, Matrix.mul_apply]

/-! ### Marginal distributions (§3.1.2) -/

omit [DecidableEq X] in
/-- (3.3)–(3.4), p. 86: the next marginal distribution is `ψP`, `ψ'(x') = ∑ₓ P(x, x')ψ(x)`. -/
theorem vecMul_apply (P : Matrix X X ℝ) (ψ : X → ℝ) (x' : X) :
    (ψ ᵥ* P) x' = ∑ x, P x x' * ψ x := by
  simp only [vecMul, dotProduct, mul_comm]

omit [DecidableEq X] in
/-- `ψ ↦ ψP` maps distributions to distributions (Vol. 1, Ex 2.3.14). -/
theorem IsMarkov.isDistribution_vecMul {P : Matrix X X ℝ} (hP : IsMarkov P) {ψ : X → ℝ}
    (hψ : IsDistribution ψ) : IsDistribution (ψ ᵥ* P) where
  nonneg x' := by
    rw [vecMul_apply]
    exact sum_nonneg fun x _ => mul_nonneg (hP.nonneg x x') (hψ.nonneg x)
  sum_eq_one := by
    simp only [vecMul_apply]
    rw [sum_comm]
    simp only [← sum_mul, hP.rowsum, one_mul, hψ.sum_eq_one]

/-- `ψPᵗ` is a distribution whenever `ψ` is. -/
theorem IsMarkov.isDistribution_vecMul_pow {P : Matrix X X ℝ} (hP : IsMarkov P) {ψ : X → ℝ}
    (hψ : IsDistribution ψ) (t : ℕ) : IsDistribution (ψ ᵥ* P ^ t) := by
  induction t with
  | zero => simpa using hψ
  | succ t ih => rw [pow_succ, ← vecMul_vecMul]; exact hP.isDistribution_vecMul ih

/-- (3.5), p. 86: iterating `ψₜ₊₁ = ψₜP` gives `ψₜ = ψ₀Pᵗ`. -/
theorem iterate_vecMul (P : Matrix X X ℝ) (ψ : X → ℝ) (t : ℕ) :
    (fun φ => φ ᵥ* P)^[t] ψ = ψ ᵥ* P ^ t := by
  induction t with
  | zero => simp
  | succ t ih => rw [Function.iterate_succ_apply', ih, vecMul_vecMul, pow_succ]

/-- Exercise 3.1.4 (p. 87), (3.6): `E h(Xₜ) = ∑ h(x)(ψ₀Pᵗ)(x) = ⟨ψ₀Pᵗ, h⟩`, which also equals
`ψ₀(Pᵗh)`. -/
theorem expectation_eq_dotProduct (P : Matrix X X ℝ) (ψ₀ h : X → ℝ) (t : ℕ) :
    ∑ x, h x * (ψ₀ ᵥ* P ^ t) x = (ψ₀ ᵥ* P ^ t) ⬝ᵥ h ∧
      (ψ₀ ᵥ* P ^ t) ⬝ᵥ h = ψ₀ ⬝ᵥ (P ^ t *ᵥ h) := by
  constructor
  · simp only [dotProduct, mul_comm]
  · rw [dotProduct_mulVec]

/-- A stationary distribution (p. 87): `ψ*P = ψ*`. -/
def IsStationary (P : Matrix X X ℝ) (ψ : X → ℝ) : Prop := ψ ᵥ* P = ψ

/-- If `ψ*` is stationary and `Xₜ ∼ ψ*`, then `Xₜ₊ₖ ∼ ψ*` for all `k` (p. 87). -/
theorem IsStationary.vecMul_pow {P : Matrix X X ℝ} {ψ : X → ℝ} (h : IsStationary P ψ) (k : ℕ) :
    ψ ᵥ* P ^ k = ψ := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← vecMul_vecMul, ih, h]

/-! ### Irreducibility (Lemma 3.1.1) -/

/-- Irreducibility (Vol. 1, p. 69): `P ≥ 0` and every state leads to every other in some positive
number of steps, `∑_{k≥1} Pᵏ ≫ 0`. -/
def Irreducible (P : Matrix X X ℝ) : Prop :=
  (∀ x x', 0 ≤ P x x') ∧ ∀ x x', ∃ k ≥ 1, 0 < (P ^ k) x x'

/-- Entries of products of nonnegative matrices dominate single terms:
`Pᵃ⁺ᵇ(x, x') ≥ Pᵃ(x, z) Pᵇ(z, x')`. -/
theorem IsMarkov.pow_add_apply_ge {P : Matrix X X ℝ} (hP : IsMarkov P) (a b : ℕ) (x z x' : X) :
    (P ^ a) x z * (P ^ b) z x' ≤ (P ^ (a + b)) x x' := by
  rw [pow_add, Matrix.mul_apply]
  exact single_le_sum (fun y _ => mul_nonneg ((hP.pow a).nonneg x y) ((hP.pow b).nonneg y x'))
    (mem_univ z)

/-- Lemma 3.1.1 (p. 85): a Markov matrix is irreducible iff for all `x, x'` some `k ≥ 0` has
`Pᵏ(x, x') > 0`, i.e. the chain eventually visits every state from every state with positive
probability. The `k = 0` case only arises for `x = x'`, and then a positive-step return exists
through any other state, or by `P(x, x) = 1` when `X = {x}`. -/
theorem IsMarkov.irreducible_iff {P : Matrix X X ℝ} (hP : IsMarkov P) :
    Irreducible P ↔ ∀ x x', ∃ k, 0 < (P ^ k) x x' := by
  constructor
  · rintro ⟨-, h⟩ x x'
    obtain ⟨k, -, hk⟩ := h x x'
    exact ⟨k, hk⟩
  · intro h
    refine ⟨hP.nonneg, fun x x' => ?_⟩
    by_cases hxx : x = x'
    · subst hxx
      -- a return to `x` in a positive number of steps
      by_cases hX : ∃ y, y ≠ x
      · obtain ⟨y, hy⟩ := hX
        obtain ⟨k₁, hk₁⟩ := h x y
        obtain ⟨k₂, hk₂⟩ := h y x
        have hk₁' : 1 ≤ k₁ := by
          rcases Nat.eq_zero_or_pos k₁ with rfl | hpos
          · simp [Ne.symm hy] at hk₁
          · exact hpos
        refine ⟨k₁ + k₂, by omega, ?_⟩
        exact lt_of_lt_of_le (mul_pos hk₁ hk₂) (hP.pow_add_apply_ge k₁ k₂ x y x)
      · -- `X = {x}`: the row sum forces `P(x, x) = 1`
        have hX' : ∀ y, y = x := fun y => by
          by_contra hy
          exact hX ⟨y, hy⟩
        refine ⟨1, le_rfl, ?_⟩
        rw [pow_one]
        have := hP.rowsum x
        rw [Fintype.sum_eq_single x (fun y hy => absurd (hX' y) hy)] at this
        rw [this]
        exact one_pos
    · obtain ⟨k, hk⟩ := h x x'
      refine ⟨k, ?_, hk⟩
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · simp [hxx] at hk
      · exact hpos

end SargentStachurski.MarkovDynamics
