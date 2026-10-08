/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDynamics.ConditionalExpectations
import MarkovDynamics.PositiveChains
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination

/-!
# The day labourer

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §3.1.2.1 (pp. 88–89).

A worker is unemployed (`1`) or employed (`2`); he is hired with probability
`α` and fired with probability `β`, (3.8). Exercise 3.1.6: the unique
stationary distribution is `ψ* = (β, α)/(α + β)`, (3.9). The book then
asserts `ψPᵗ → ψ*` for every distribution `ψ`; here this is proved in closed
form, `(ψPᵗ)(1) − ψ*(1) = (1 − α − β)ᵗ (ψ(1) − ψ*(1))`, with `|1 − α − β| < 1`.
Exercise 3.1.7's general statement for everywhere-positive `P` is proved in
`PositiveChains` and applied here. Exercise 3.2.3: the two-state matrix is
monotone increasing iff `α + β ≤ 1`. Exercises 3.1.5, 3.1.8 and 3.1.9 are
computational.
-/

open Finset Matrix Filter Topology

namespace SargentStachurski.MarkovDynamics

/-- The day labourer's hiring rate `α` and firing rate `β`, both in `(0, 1)`. -/
structure DayLaborer where
  α : ℝ
  β : ℝ
  α_pos : 0 < α
  α_lt_one : α < 1
  β_pos : 0 < β
  β_lt_one : β < 1

namespace DayLaborer

variable (m : DayLaborer)

/-- The transition matrix (3.8), with state `0` unemployed and `1` employed. -/
noncomputable def P : Matrix (Fin 2) (Fin 2) ℝ := !![1 - m.α, m.α; m.β, 1 - m.β]

theorem isMarkov_P : IsMarkov m.P where
  nonneg i j := by
    have := m.α_pos; have := m.α_lt_one; have := m.β_pos; have := m.β_lt_one
    fin_cases i <;> fin_cases j <;> simp [P] <;> linarith
  rowsum i := by fin_cases i <;> simp [P, Fin.sum_univ_two]

theorem α_add_β_pos : 0 < m.α + m.β := by linarith [m.α_pos, m.β_pos]

/-- The stationary distribution (3.9): `ψ* = (β, α)/(α + β)`. -/
noncomputable def ψstar : Fin 2 → ℝ := ![m.β / (m.α + m.β), m.α / (m.α + m.β)]

theorem isDistribution_ψstar : IsDistribution m.ψstar where
  nonneg i := by
    fin_cases i
    · exact div_nonneg m.β_pos.le m.α_add_β_pos.le
    · exact div_nonneg m.α_pos.le m.α_add_β_pos.le
  sum_eq_one := by
    have := m.α_add_β_pos.ne'
    simp [ψstar, Fin.sum_univ_two]
    field_simp
    ring

/-- Exercise 3.1.6 (p. 88): `ψ*` is stationary. -/
theorem isStationary_ψstar : IsStationary m.P m.ψstar := by
  have hne := m.α_add_β_pos.ne'
  funext j
  fin_cases j <;> simp [P, ψstar, vecMul, dotProduct, Fin.sum_univ_two] <;> field_simp <;> ring

/-- Exercise 3.1.6 (p. 88): `ψ*` is the only stationary distribution. -/
theorem eq_ψstar_of_isStationary {ψ : Fin 2 → ℝ} (hψ : IsDistribution ψ) (hs : IsStationary m.P ψ) :
    ψ = m.ψstar := by
  have hne := m.α_add_β_pos.ne'
  have hsum : ψ 0 + ψ 1 = 1 := by simpa [Fin.sum_univ_two] using hψ.sum_eq_one
  -- `(1 − α)ψ₀ + βψ₁ = ψ₀`, i.e. `αψ₀ = βψ₁`
  have h0 : ψ 0 * (1 - m.α) + ψ 1 * m.β = ψ 0 := by
    have := congrFun hs 0
    simpa [P, vecMul, dotProduct, Fin.sum_univ_two] using this
  have h1 : ψ 1 = 1 - ψ 0 := by linarith
  rw [h1] at h0
  have hψ0' : ψ 0 * (m.α + m.β) = m.β := by linear_combination -h0
  funext j
  fin_cases j
  · change ψ 0 = m.β / (m.α + m.β)
    rw [eq_div_iff hne]
    exact hψ0'
  · change ψ 1 = m.α / (m.α + m.β)
    rw [eq_div_iff hne, h1]
    linear_combination -hψ0'

/-- The one-step recursion for the unemployment probability:
`(ψP)(1) − β/(α + β) = (1 − α − β)(ψ(1) − β/(α + β))` for a distribution `ψ`. -/
theorem vecMul_zero_sub (ψ : Fin 2 → ℝ) (hsum : ψ 0 + ψ 1 = 1) :
    (ψ ᵥ* m.P) 0 - m.β / (m.α + m.β) = (1 - m.α - m.β) * (ψ 0 - m.β / (m.α + m.β)) := by
  have hne := m.α_add_β_pos.ne'
  have h1 : ψ 1 = 1 - ψ 0 := by linarith
  simp only [P, vecMul, dotProduct, Fin.sum_univ_two, h1]
  simp
  field_simp
  ring

/-- The `t`-step recursion: `(ψPᵗ)(1) − ψ*(1) = (1 − α − β)ᵗ (ψ(1) − ψ*(1))`. -/
theorem vecMul_pow_zero_sub {ψ : Fin 2 → ℝ} (hψ : IsDistribution ψ) (t : ℕ) :
    (ψ ᵥ* m.P ^ t) 0 - m.β / (m.α + m.β) = (1 - m.α - m.β) ^ t * (ψ 0 - m.β / (m.α + m.β)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hsum : (ψ ᵥ* m.P ^ t) 0 + (ψ ᵥ* m.P ^ t) 1 = 1 := by
      simpa [Fin.sum_univ_two] using (m.isMarkov_P.isDistribution_vecMul_pow hψ t).sum_eq_one
    rw [pow_succ, ← vecMul_vecMul, m.vecMul_zero_sub _ hsum, ih]
    ring

/-- `|1 − α − β| < 1`. -/
theorem abs_one_sub_lt_one : |1 - m.α - m.β| < 1 := by
  rw [abs_lt]
  constructor <;> linarith [m.α_pos, m.α_lt_one, m.β_pos, m.β_lt_one]

/-- The claim of p. 88: `ψPᵗ → ψ*` for every distribution `ψ`, so `ψ ↦ ψP` is globally stable
on `D(X)`. -/
theorem tendsto_vecMul_pow {ψ : Fin 2 → ℝ} (hψ : IsDistribution ψ) :
    Tendsto (fun t : ℕ => ψ ᵥ* m.P ^ t) atTop (𝓝 m.ψstar) := by
  have hne := m.α_add_β_pos.ne'
  have hgeom : Tendsto (fun t : ℕ => (1 - m.α - m.β) ^ t * (ψ 0 - m.β / (m.α + m.β))) atTop
      (𝓝 0) := by
    have habs := tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg (1 - m.α - m.β))
      m.abs_one_sub_lt_one
    simp only [← abs_pow] at habs
    have hpow : Tendsto (fun t : ℕ => (1 - m.α - m.β) ^ t) atTop (𝓝 0) :=
      tendsto_zero_iff_abs_tendsto_zero _ |>.2 habs
    simpa using hpow.mul_const (ψ 0 - m.β / (m.α + m.β))
  have h0 : Tendsto (fun t : ℕ => (ψ ᵥ* m.P ^ t) 0) atTop (𝓝 (m.β / (m.α + m.β))) := by
    have := hgeom
    simp_rw [← m.vecMul_pow_zero_sub hψ] at this
    have h := this.add_const (m.β / (m.α + m.β))
    simpa using h
  have hdist : ∀ t, (ψ ᵥ* m.P ^ t) 0 + (ψ ᵥ* m.P ^ t) 1 = 1 := fun t => by
    simpa [Fin.sum_univ_two] using (m.isMarkov_P.isDistribution_vecMul_pow hψ t).sum_eq_one
  have h1 : Tendsto (fun t : ℕ => (ψ ᵥ* m.P ^ t) 1) atTop (𝓝 (m.α / (m.α + m.β))) := by
    have : (fun t : ℕ => (ψ ᵥ* m.P ^ t) 1) = fun t => 1 - (ψ ᵥ* m.P ^ t) 0 := by
      funext t
      linarith [hdist t]
    rw [this]
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub h0
    have heq : 1 - m.β / (m.α + m.β) = m.α / (m.α + m.β) := by
      field_simp
      ring
    rwa [heq] at h
  rw [tendsto_pi_nhds]
  intro j
  fin_cases j
  · simpa [ψstar] using h0
  · simpa [ψstar] using h1

/-- Every entry of `P` is positive. -/
theorem P_pos (i j : Fin 2) : 0 < m.P i j := by
  have := m.α_pos; have := m.α_lt_one; have := m.β_pos; have := m.β_lt_one
  fin_cases i <;> fin_cases j <;> simp [P] <;> linarith

/-- Exercise 3.1.7 (p. 89), first part: the day labourer's `ψ ↦ ψP` is globally stable on `D(X)`,
by the general result for `P ≫ 0`. -/
theorem globallyStable_distMap : GloballyStable (distMap m.isMarkov_P) :=
  MarkovDynamics.globallyStable_distMap m.isMarkov_P m.P_pos

end DayLaborer

/-- Exercise 3.2.3 (p. 93): the two-state matrix `P_w = [[1 − α, α], [β, 1 − β]]` is monotone
increasing iff `α + β ≤ 1`; the bounds `α, β ∈ [0, 1]` are not needed for this equivalence. -/
theorem monotoneIncreasing_two_state_iff (α β : ℝ) :
    MonotoneIncreasing !![1 - α, α; β, 1 - β] ↔ α + β ≤ 1 := by
  constructor
  · intro h
    have hu : Monotone fun i : Fin 2 => ((i : ℕ) : ℝ) := fun a b hab => Nat.cast_le.2 hab
    have := h 0 1 (by decide) _ hu
    simp [Fin.sum_univ_two] at this
    linarith
  · intro h x y hxy u hu
    have h01 : u 0 ≤ u 1 := hu (by decide)
    fin_cases x <;> fin_cases y
    · exact le_rfl
    · simp [Fin.sum_univ_two]
      nlinarith
    · exact absurd hxy (by decide)
    · exact le_rfl

end SargentStachurski.MarkovDynamics
