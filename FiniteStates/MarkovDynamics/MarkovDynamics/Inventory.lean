/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDynamics.MarkovChains
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# S–s inventory dynamics

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §3.1.1.2 (pp. 82–84)
and Exercises 3.1.1, 3.1.3.

A firm reorders `S` units whenever its inventory `Xₜ` is at or below `s`;
demand `Dₜ₊₁` is IID geometric with parameter `p`:
`Xₜ₊₁ = max{Xₜ − Dₜ₊₁, 0} + S·1{Xₜ ≤ s}`. Exercise 3.1.1: the state space
`{0, …, S + s}` is invariant. The transition matrix is
`P(x, x') = ∑_d 1{h(x, d) = x'} φ(d)`, and Exercise 3.1.3 shows it is
irreducible: from any state the chain reaches `s`, then `S + s`, then any
state, each step with positive probability. The book proves this for `x > s`
and leaves `x ≤ s` to the reader; here the case `x ≤ s` is handled by a
first step to `S` (demand at least `x`), which needs `s < S` as in the
book's calibration (`S = 100`, `s = 10`). Without `s < S` the chain is still
irreducible but reaches `s` only after several reorders; that case is not
formalised.
-/

open Finset Matrix

namespace SargentStachurski.MarkovDynamics

/-- The S–s inventory model: order size `S`, threshold `s`, geometric demand parameter `p`. -/
structure Inventory where
  S : ℕ
  s : ℕ
  p : ℝ
  s_lt_S : s < S
  p_pos : 0 < p
  p_lt_one : p < 1

namespace Inventory

variable (m : Inventory)

/-- The state space `X = {0, …, S + s}`, as `Fin (S + s + 1)`. -/
abbrev State := Fin (m.S + m.s + 1)

/-- The update rule `h(x, d) = max{x − d, 0} + S·1{x ≤ s}` (p. 83); `ℕ` subtraction is the
truncation `max{x − d, 0}`. -/
def h (x d : ℕ) : ℕ := (x - d) + if x ≤ m.s then m.S else 0

/-- Exercise 3.1.1 (p. 83): `X = {0, …, S + s}` is invariant: `x ≤ S + s` implies
`h(x, d) ≤ S + s`. -/
theorem h_le (x d : ℕ) (hx : x ≤ m.S + m.s) : m.h x d ≤ m.S + m.s := by
  unfold h
  split_ifs with hxs <;> omega

/-- The next state, as an element of the state space. -/
def next (x : m.State) (d : ℕ) : m.State :=
  ⟨m.h x d, Nat.lt_succ_of_le (m.h_le x d (Nat.le_of_lt_succ x.2))⟩

/-- The geometric demand distribution `φ(d) = p(1 − p)^d` on `ℤ₊` (p. 83). -/
noncomputable def φ (d : ℕ) : ℝ := m.p * (1 - m.p) ^ d

theorem φ_pos (d : ℕ) : 0 < m.φ d :=
  mul_pos m.p_pos (pow_pos (by linarith [m.p_lt_one]) d)

theorem one_sub_p_nonneg : 0 ≤ 1 - m.p := by linarith [m.p_lt_one]

theorem one_sub_p_lt_one : 1 - m.p < 1 := by linarith [m.p_pos]

theorem summable_φ : Summable m.φ :=
  (summable_geometric_of_lt_one m.one_sub_p_nonneg m.one_sub_p_lt_one).mul_left m.p

/-- The demand distribution sums to one. -/
theorem tsum_φ : ∑' d, m.φ d = 1 := by
  unfold φ
  rw [tsum_mul_left, tsum_geometric_of_lt_one m.one_sub_p_nonneg m.one_sub_p_lt_one]
  have h1 : (1 : ℝ) - (1 - m.p) = m.p := by ring
  rw [h1, inv_eq_one_div, mul_one_div, div_self m.p_pos.ne']

/-- The transition matrix `P(x, x') = ∑_d 1{h(x, d) = x'} φ(d)` (p. 83). -/
noncomputable def P : Matrix m.State m.State ℝ :=
  Matrix.of fun x x' => ∑' d : ℕ, if m.next x d = x' then m.φ d else 0

theorem P_apply (x x' : m.State) : m.P x x' = ∑' d : ℕ, if m.next x d = x' then m.φ d else 0 := rfl

theorem summable_term (x x' : m.State) :
    Summable fun d : ℕ => if m.next x d = x' then m.φ d else 0 :=
  m.summable_φ.of_nonneg_of_le (fun d => by split_ifs <;> [exact (m.φ_pos d).le; exact le_rfl])
    (fun d => by split_ifs <;> [exact le_rfl; exact (m.φ_pos d).le])

/-- `P` is a Markov matrix: nonnegative, and each row sums to `∑_d φ(d) = 1` because every demand
leads to exactly one next state. -/
theorem isMarkov_P : IsMarkov m.P where
  nonneg x x' := tsum_nonneg fun d => by split_ifs <;> [exact (m.φ_pos d).le; exact le_rfl]
  rowsum x := by
    simp only [P_apply]
    rw [← Summable.tsum_finsetSum fun x' _ => m.summable_term x x', ← m.tsum_φ]
    refine tsum_congr fun d => ?_
    rw [sum_ite_eq univ (m.next x d) (fun _ => m.φ d)]
    simp

/-- A single demand realisation gives a lower bound on a transition probability. -/
theorem φ_le_P (x : m.State) (d : ℕ) : m.φ d ≤ m.P x (m.next x d) := by
  rw [P_apply]
  have := (m.summable_term x (m.next x d)).le_tsum d fun d' _ => by
    split_ifs <;> [exact (m.φ_pos d').le; exact le_rfl]
  simpa using this

/-- Transitions realised by some demand have positive probability. -/
theorem P_pos (x : m.State) (d : ℕ) : 0 < m.P x (m.next x d) := (m.φ_pos d).trans_le (m.φ_le_P x d)

theorem next_val (x : m.State) (d : ℕ) : (m.next x d : ℕ) = m.h x d := rfl

/-- The threshold state `s`. -/
def sState : m.State := ⟨m.s, by omega⟩

theorem sState_val : (m.sState : ℕ) = m.s := rfl

/-- The full state `S + s`. -/
def fullState : m.State := ⟨m.S + m.s, by omega⟩

theorem fullState_val : (m.fullState : ℕ) = m.S + m.s := rfl

/-- The state `S`. -/
def SState : m.State := ⟨m.S, by omega⟩

theorem SState_val : (m.SState : ℕ) = m.S := rfl

/-- From `x > s`, demand `x − s` leads to `s`. -/
theorem next_eq_sState {x : m.State} (hx : m.s < x) : m.next x ((x : ℕ) - m.s) = m.sState := by
  rw [Fin.ext_iff, next_val, sState_val]
  unfold h
  split_ifs <;> omega

/-- From `s`, zero demand leads to `S + s`. -/
theorem next_sState_zero : m.next m.sState 0 = m.fullState := by
  rw [Fin.ext_iff, next_val, sState_val, fullState_val]
  unfold h
  split_ifs <;> omega

/-- From `S + s`, demand `S + s − y` leads to any `y`. -/
theorem next_fullState (y : m.State) : m.next m.fullState (m.S + m.s - y) = y := by
  rw [Fin.ext_iff, next_val, fullState_val]
  unfold h
  have hy : (y : ℕ) ≤ m.S + m.s := Nat.le_of_lt_succ y.2
  have hs := m.s_lt_S
  split_ifs <;> omega

/-- From `x ≤ s`, demand `x` leads to `S`. -/
theorem next_eq_SState {x : m.State} (hx : (x : ℕ) ≤ m.s) : m.next x x = m.SState := by
  rw [Fin.ext_iff, next_val, SState_val]
  unfold h
  split_ifs
  omega

/-- Exercise 3.1.3 (p. 85): the inventory chain is irreducible. From `x > s`: `x → s → S + s → y`
in three steps; from `x ≤ s`: `x → S → s → S + s → y` in four, using `s < S`. -/
theorem irreducible_P : Irreducible m.P := by
  have hM := m.isMarkov_P
  refine ⟨hM.nonneg, fun x y => ?_⟩
  -- the three-step path from `s`'s predecessor: `s → S + s → y`
  have h2 : 0 < (m.P ^ 2) m.sState y := by
    have := hM.pow_add_apply_ge 1 1 m.sState m.fullState y
    rw [pow_one] at this
    refine lt_of_lt_of_le (mul_pos ?_ ?_) this
    · have := m.P_pos m.sState 0
      rwa [m.next_sState_zero] at this
    · have := m.P_pos m.fullState (m.S + m.s - y)
      rwa [m.next_fullState y] at this
  by_cases hx : m.s < x
  · refine ⟨3, by norm_num, ?_⟩
    have := hM.pow_add_apply_ge 1 2 x m.sState y
    rw [pow_one] at this
    refine lt_of_lt_of_le (mul_pos ?_ h2) this
    have := m.P_pos x ((x : ℕ) - m.s)
    rwa [m.next_eq_sState hx] at this
  · refine ⟨4, by norm_num, ?_⟩
    have hxs : (x : ℕ) ≤ m.s := not_lt.1 hx
    have hS : m.s < m.SState := m.s_lt_S
    have h3 : 0 < (m.P ^ 3) m.SState y := by
      have := hM.pow_add_apply_ge 1 2 m.SState m.sState y
      rw [pow_one] at this
      refine lt_of_lt_of_le (mul_pos ?_ h2) this
      have := m.P_pos m.SState ((m.SState : ℕ) - m.s)
      rwa [m.next_eq_sState hS] at this
    have := hM.pow_add_apply_ge 1 3 x m.SState y
    rw [pow_one] at this
    refine lt_of_lt_of_le (mul_pos ?_ h3) this
    have := m.P_pos x x
    rwa [m.next_eq_SState hxs] at this

end Inventory

end SargentStachurski.MarkovDynamics
