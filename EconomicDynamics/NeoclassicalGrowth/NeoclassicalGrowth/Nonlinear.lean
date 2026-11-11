/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoclassicalGrowth.PhaseDiagram
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Nonlinear systems

Copied from `EconomicDynamics/DifferenceEquations` (module `Nonlinear`), namespace renamed.

Miao, §1.6, pp. 28–32.

* **Example 1.6.1** (optimal growth). The steady-state equations `C̄ = f(K̄) − δK̄`,
  `1 = β(f'(K̄) + 1 − δ)` (`example_1_6_1_steady`); the first-order Taylor coefficients of the
  Euler equation and the resource constraint (`example_1_6_1_linearization`); the linearised
  equations are equivalent to the printed matrix system (`example_1_6_1_matrix`) and to the
  reduced system with matrix `[[1/β, −1], [f''/A, 1 − βf''/A]]`, `A = −u''/u'`
  (`example_1_6_1_reduced`; the printed entries are correct); trace
  `T = 1 + 1/β − βf''/A > 1 + 1/β > 2` and determinant `1/β > 1` (`example_1_6_1_trace_det`);
  the roots satisfy `0 < λ₁ < 1 < λ₂` (`example_1_6_1_roots`), so the steady state is a saddle:
  for every `dK₀` there is exactly one bounded linearised path, and it converges
  (`example_1_6_1_saddle`).
* **Definition 1.6.1** (periodic points): `Function.minimalPeriod f x = p` iff `fᵖ(x) = x` and
  `p` is the least such positive integer (`definition_1_6_1`); the `p`-cycle has `p` distinct
  points (`definition_1_6_1_cycle`).
* The logistic map `f(x) = 4x − 4x²` (definition copied from
  `RecursiveMethods/DeterministicDynamics/LogisticMap.lean`): the second iterate
  `16x − 80x² + 128x³ − 64x⁴` (`logistic_two`), the fixed points of `f` are exactly `0, 3/4`
  (`logistic_fixed_iff`), those of `f²` exactly `0, 3/4, (5 ± √5)/8` (`logistic_two_fixed_iff`),
  `(5 ± √5)/8` form a two-cycle of minimal period 2 (`logistic_two_cycle`), and the printed
  decimals `0.3455`, `0.9045` are correct to four places (`logistic_two_cycle_decimals`).
-/

open Filter Topology

namespace Miao.NeoclassicalGrowth

open scoped Matrix

/-! ### Example 1.6.1: optimal growth -/

/-- **Example 1.6.1** (Miao, p. 31): a constant path `(K̄, C̄)` satisfies the resource constraint
(1.43) and the Euler equation `u'(C) = βu'(C)(f'(K) + 1 − δ)` iff `C̄ = f(K̄) − δK̄` and
`1 = β(f'(K̄) + 1 − δ)` (given `u'(C̄) ≠ 0`). -/
theorem example_1_6_1_steady {f fp up : ℝ → ℝ} {β δ K C : ℝ} (hu : up C ≠ 0) :
    (C + K - (1 - δ) * K = f K ∧ up C = β * up C * (fp K + 1 - δ)) ↔
      (C = f K - δ * K ∧ 1 = β * (fp K + 1 - δ)) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by linarith, ?_⟩
    have : up C * 1 = up C * (β * (fp K + 1 - δ)) := by linarith
    exact mul_left_cancel₀ hu this
  · rintro ⟨h1, h2⟩
    refine ⟨by linarith, ?_⟩
    linear_combination (up C) * h2

/-- **Example 1.6.1** (Miao, p. 31): the first-order Taylor coefficients at the steady state.
For the Euler residual `u'(C_t) − βu'(C_{t+1})(f'(K_{t+1}) + 1 − δ)` the partial derivatives in
`C_t`, `C_{t+1}`, `K_{t+1}` are `u''`, `−βu''(f' + 1 − δ)`, `−βu'f''`; for the resource residual
`C_t + K_{t+1} − (1 − δ)K_t − f(K_t)` they are `1`, `1`, `−(1 − δ) − f'` in `C_t`, `K_{t+1}`,
`K_t`. Setting the linear terms to zero gives the two linearised equations of the book. -/
theorem example_1_6_1_linearization {f fp up : ℝ → ℝ} {β δ Kb Cb upp fpp : ℝ}
    (hf : HasDerivAt f (fp Kb) Kb) (hfp : HasDerivAt fp fpp Kb) (hup : HasDerivAt up upp Cb) :
    HasDerivAt (fun C => up C - β * up Cb * (fp Kb + 1 - δ)) upp Cb ∧
      HasDerivAt (fun C' => up Cb - β * up C' * (fp Kb + 1 - δ))
        (-(β * upp * (fp Kb + 1 - δ))) Cb ∧
      HasDerivAt (fun K' => up Cb - β * up Cb * (fp K' + 1 - δ)) (-(β * up Cb * fpp)) Kb ∧
      HasDerivAt (fun C => C + Kb - (1 - δ) * Kb - f Kb) 1 Cb ∧
      HasDerivAt (fun K' => Cb + K' - (1 - δ) * Kb - f Kb) 1 Kb ∧
      HasDerivAt (fun K => Cb + Kb - (1 - δ) * K - f K) (-(1 - δ) - fp Kb) Kb := by
  refine ⟨HasDerivAt.sub_const _ hup, ?_, ?_, ?_, ?_, ?_⟩
  · have := HasDerivAt.const_sub (up Cb)
      (HasDerivAt.mul_const (HasDerivAt.const_mul β hup) (fp Kb + 1 - δ))
    convert this using 1
  · have := HasDerivAt.const_sub (up Cb)
      (HasDerivAt.const_mul (β * up Cb) (HasDerivAt.add_const (1 - δ) hfp))
    convert this using 1
    ext K; ring
  · have := HasDerivAt.sub_const (f Kb) (HasDerivAt.sub_const ((1 - δ) * Kb)
      (HasDerivAt.add_const Kb (hasDerivAt_id Cb)))
    simpa using this
  · have := HasDerivAt.sub_const (f Kb) (HasDerivAt.sub_const ((1 - δ) * Kb)
      (HasDerivAt.const_add Cb (hasDerivAt_id Kb)))
    simpa using this
  · have := HasDerivAt.sub (HasDerivAt.const_sub (Cb + Kb)
      (HasDerivAt.const_mul (1 - δ) (hasDerivAt_id Kb))) hf
    convert this using 1
    · ext K; simp only [Pi.sub_apply, id]
    · ring

theorem vec2_eq_iff (a b c d : ℝ) : (![a, b] : Fin 2 → ℝ) = ![c, d] ↔ a = c ∧ b = d := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem mulVec22 (a b c d x y : ℝ) :
    !![a, b; c, d] *ᵥ ![x, y] = ![a * x + b * y, c * x + d * y] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **Example 1.6.1** (Miao, p. 31): at the steady state (`β(f' + 1 − δ) = 1`, `u'' ≠ 0`) the
two linearised equations
`u''dC_t = βu''(f' + 1 − δ)dC_{t+1} + βu'f''dK_{t+1}` and
`dC_t + dK_{t+1} − (1 − δ)dK_t = f'dK_t` are equivalent to the printed system
`[[βu'f''/u'', 1], [1, 0]] (dK_{t+1}, dC_{t+1}) = [[0, 1], [f' + 1 − δ, −1]] (dK_t, dC_t)`. -/
theorem example_1_6_1_matrix {β δ up upp fp fpp : ℝ} (hupp : upp ≠ 0)
    (hss : β * (fp + 1 - δ) = 1) (dK dC : ℕ → ℝ) (t : ℕ) :
    (upp * dC t = β * upp * (fp + 1 - δ) * dC (t + 1) + β * up * fpp * dK (t + 1) ∧
        dC t + dK (t + 1) - (1 - δ) * dK t = fp * dK t) ↔
      !![β * up * fpp / upp, 1; 1, 0] *ᵥ ![dK (t + 1), dC (t + 1)] =
        !![0, 1; fp + 1 - δ, -1] *ᵥ ![dK t, dC t] := by
  rw [mulVec22, mulVec22, vec2_eq_iff]
  have h1 : β * upp * (fp + 1 - δ) = upp := by rw [mul_comm β, mul_assoc, hss, mul_one]
  rw [h1]
  constructor
  · rintro ⟨e1, e2⟩
    refine ⟨?_, by linarith⟩
    field_simp
    linarith
  · rintro ⟨e1, e2⟩
    refine ⟨?_, by linarith⟩
    field_simp at e1
    linarith

/-- **Example 1.6.1** (Miao, p. 31): with `A = −u''/u'` (`u' > 0`, `u'' ≠ 0`) and
`β(f' + 1 − δ) = 1`, the linearised equations are equivalent to
`(dK_{t+1}, dC_{t+1}) = [[1/β, −1], [f''/A, 1 − βf''/A]] (dK_t, dC_t)`, as printed. -/
theorem example_1_6_1_reduced {β δ up upp fp fpp : ℝ} (hβ : β ≠ 0) (hup : 0 < up)
    (hupp : upp ≠ 0) (hss : β * (fp + 1 - δ) = 1) (dK dC : ℕ → ℝ) (t : ℕ) :
    (upp * dC t = β * upp * (fp + 1 - δ) * dC (t + 1) + β * up * fpp * dK (t + 1) ∧
        dC t + dK (t + 1) - (1 - δ) * dK t = fp * dK t) ↔
      ![dK (t + 1), dC (t + 1)] =
        !![1 / β, -1; fpp / (-upp / up), 1 - β * fpp / (-upp / up)] *ᵥ ![dK t, dC t] := by
  rw [mulVec22, vec2_eq_iff]
  have hfp : fp + 1 - δ = 1 / β := by field_simp; linarith
  have h1 : β * upp * (fp + 1 - δ) = upp := by rw [mul_comm β, mul_assoc, hss, mul_one]
  rw [h1]
  have hup' : up ≠ 0 := hup.ne'
  constructor
  · rintro ⟨e1, e2⟩
    have eK : dK (t + 1) = 1 / β * dK t + -1 * dC t := by rw [← hfp]; linarith
    refine ⟨eK, ?_⟩
    rw [eK] at e1
    field_simp
    field_simp at e1
    linarith
  · rintro ⟨e1, e2⟩
    refine ⟨?_, ?_⟩
    · rw [e2, e1]
      field_simp
      ring
    · rw [e1, ← hfp]; ring

/-- **Example 1.6.1** (Miao, p. 31): for `0 < β < 1`, `f'' < 0`, `A > 0`, the coefficient matrix
has trace `T = 1 + 1/β − βf''/A > 1 + 1/β > 2` and determinant `D = 1/β > 1`. -/
theorem example_1_6_1_trace_det {β fpp A : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hf : fpp < 0)
    (hA : 0 < A) :
    1 / β + (1 - β * fpp / A) = 1 + 1 / β - β * fpp / A ∧
      1 / β * (1 - β * fpp / A) - (-1) * (fpp / A) = 1 / β ∧
      1 + 1 / β < 1 + 1 / β - β * fpp / A ∧ 2 < 1 + 1 / β ∧ 1 < 1 / β := by
  have h1 : 1 < 1 / β := by rw [lt_div_iff₀ hβ0]; linarith
  have h2 : β * fpp / A < 0 := div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hβ0 hf) hA
  refine ⟨by ring, by field_simp; ring, by linarith, by linarith, h1⟩

/-- **Example 1.6.1** (Miao, p. 31): the characteristic roots satisfy `0 < λ₁ < 1 < λ₂`, so
the steady state is a saddle point. -/
theorem example_1_6_1_roots {β fpp A : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hf : fpp < 0)
    (hA : 0 < A) :
    cp22 (1 / β) (-1) (fpp / A) (1 - β * fpp / A) 1 < 0 ∧
      0 < lamLo (1 / β) (-1) (fpp / A) (1 - β * fpp / A) ∧
      lamLo (1 / β) (-1) (fpp / A) (1 - β * fpp / A) < 1 ∧
      1 < lamHi (1 / β) (-1) (fpp / A) (1 - β * fpp / A) := by
  have h2 : β * fpp / A < 0 := div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hβ0 hf) hA
  have hcp : ∀ μ, cp22 (1 / β) (-1) (fpp / A) (1 - β * fpp / A) μ =
      μ ^ 2 - (1 + 1 / β - β * fpp / A) * μ + 1 / β := fun μ => by
    simp only [cp22]; field_simp; ring
  have h1 : cp22 (1 / β) (-1) (fpp / A) (1 - β * fpp / A) 1 < 0 := by
    rw [hcp]; linarith
  obtain ⟨hlo, hhi⟩ := roots22_lt h1
  refine ⟨h1, ?_, hlo, hhi⟩
  have h0 := cp22_factor h1 0
  rw [hcp] at h0
  have hb : 0 < 1 / β := by positivity
  nlinarith

/-- **Example 1.6.1** (Miao, p. 31): the saddle property of the linearised system. For every
`dK₀` (capital is predetermined) there is exactly one bounded solution, it starts at
`dC₀ = k dK₀` on the saddle line, and it converges to the steady state. -/
theorem example_1_6_1_saddle {β fpp A : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hf : fpp < 0)
    (hA : 0 < A) (dK0 : ℝ) :
    (∃ dK dC : ℕ → ℝ, IsSol22 (1 / β) (-1) (fpp / A) (1 - β * fpp / A) dK dC ∧ dK 0 = dK0 ∧
      Tendsto dK atTop (𝓝 0) ∧ Tendsto dC atTop (𝓝 0)) ∧
    ∀ dK dC : ℕ → ℝ, IsSol22 (1 / β) (-1) (fpp / A) (1 - β * fpp / A) dK dC → BddSeq dK →
      BddSeq dC → dC 0 = kSaddle (1 / β) (-1) (fpp / A) (1 - β * fpp / A) * dK 0 := by
  obtain ⟨h1, hlo0, -, -⟩ := example_1_6_1_roots hβ0 hβ1 hf hA
  have hm : 0 < -1 * (fpp / A) := by
    have := div_neg_of_neg_of_pos hf hA; linarith
  have hc : 0 < cp22 (1 / β) (-1) (fpp / A) (1 - β * fpp / A) (-1) := by
    rw [cp22_factor h1 (-1)]
    have := (roots22_lt h1).2
    nlinarith
  refine ⟨(saddle22_iff h1 hm).2 hc dK0, fun dK dC h hK hC => ?_⟩
  exact (sHi_zero_iff h1 hm dK dC 0).1 (sHi_zero_of_bdd h1 h hK hC)

/-! ### Definition 1.6.1: periodic points -/

/-- **Definition 1.6.1** (Miao, pp. 31–32): `x*` is a periodic point of period `p > 0` (`p` is
the smallest positive integer with `fᵖ(x*) = x*`) iff `Function.minimalPeriod f x* = p`. -/
theorem definition_1_6_1 {α : Type*} (f : α → α) (x : α) {p : ℕ} (hp : 0 < p) :
    Function.minimalPeriod f x = p ↔ f^[p] x = x ∧ ∀ q, 0 < q → q < p → f^[q] x ≠ x := by
  constructor
  · rintro rfl
    exact ⟨Function.iterate_minimalPeriod, fun q hq hlt =>
      Function.not_isPeriodicPt_of_pos_of_lt_minimalPeriod hq.ne' hlt⟩
  · rintro ⟨h, hmin⟩
    have hle := Function.IsPeriodicPt.minimalPeriod_le hp h
    have hpos := Function.IsPeriodicPt.minimalPeriod_pos hp h
    by_contra hne
    exact hmin _ hpos (lt_of_le_of_ne hle hne) Function.iterate_minimalPeriod

/-- **Definition 1.6.1** (Miao, p. 32): the `p`-cycle `{x*, f(x*), …, f^{p−1}(x*)}` of a point of
minimal period `p` has exactly `p` distinct points. -/
theorem definition_1_6_1_cycle {α : Type*} [DecidableEq α] (f : α → α) (x : α) :
    ((Finset.range (Function.minimalPeriod f x)).image (fun k => f^[k] x)).card =
      Function.minimalPeriod f x := by
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro m hm n hn hmn
  exact Function.iterate_injOn_Iio_minimalPeriod (by simpa using hm) (by simpa using hn) hmn

/-! ### The logistic map -/

/-- The logistic map `f(x) = 4x − 4x²` (Miao, p. 32). Copied from
`RecursiveMethods/DeterministicDynamics/LogisticMap.lean` (`logistic`). -/
def logistic (x : ℝ) : ℝ := 4 * x - 4 * x ^ 2

/-- Miao, p. 32: `f²(x) = 16x − 80x² + 128x³ − 64x⁴`. -/
theorem logistic_two (x : ℝ) :
    logistic^[2] x = 16 * x - 80 * x ^ 2 + 128 * x ^ 3 - 64 * x ^ 4 := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id, logistic]
  ring

/-- Miao, p. 32: the fixed points of `f` are exactly `0` and `0.75`. Copied (restated) from
`RecursiveMethods/DeterministicDynamics/LogisticMap.lean` (`ex_6_3a`). -/
theorem logistic_fixed_iff (x : ℝ) : logistic x = x ↔ x = 0 ∨ x = 3 / 4 := by
  simp only [logistic]
  constructor
  · intro h
    have : x * (3 - 4 * x) = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> norm_num

/-- Miao, p. 32: the fixed points of `f²` are exactly `0`, `3/4` and `(5 ± √5)/8`. -/
theorem logistic_two_fixed_iff (x : ℝ) :
    logistic^[2] x = x ↔
      x = 0 ∨ x = 3 / 4 ∨ x = (5 - Real.sqrt 5) / 8 ∨ x = (5 + Real.sqrt 5) / 8 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have key : logistic^[2] x - x =
      -(x * (4 * x - 3) * (16 * ((x - (5 - Real.sqrt 5) / 8) * (x - (5 + Real.sqrt 5) / 8)))) := by
    rw [logistic_two]
    linear_combination (-(x * (4 * x - 3)) / 4) * h5
  constructor
  · intro h
    have : x * (4 * x - 3) * (16 * ((x - (5 - Real.sqrt 5) / 8) *
        (x - (5 + Real.sqrt 5) / 8))) = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (Or.inl (by linarith))
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · norm_num at h2
      · rcases mul_eq_zero.1 h2 with h3 | h3
        · exact Or.inr (Or.inr (Or.inl (by linarith)))
        · exact Or.inr (Or.inr (Or.inr (by linarith)))
  · intro h
    have : logistic^[2] x - x = 0 := by
      rw [key]
      rcases h with rfl | rfl | rfl | rfl <;> ring
    linarith

/-- Miao, p. 32: `(5 − √5)/8` and `(5 + √5)/8` form a two-cycle: `f` swaps them, and each has
minimal period `2` (Definition 1.6.1). -/
theorem logistic_two_cycle :
    logistic ((5 - Real.sqrt 5) / 8) = (5 + Real.sqrt 5) / 8 ∧
      logistic ((5 + Real.sqrt 5) / 8) = (5 - Real.sqrt 5) / 8 ∧
      Function.minimalPeriod logistic ((5 - Real.sqrt 5) / 8) = 2 ∧
      Function.minimalPeriod logistic ((5 + Real.sqrt 5) / 8) = 2 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have e1 : logistic ((5 - Real.sqrt 5) / 8) = (5 + Real.sqrt 5) / 8 := by
    simp only [logistic]; linear_combination (-1 / 16 : ℝ) * h5
  have e2 : logistic ((5 + Real.sqrt 5) / 8) = (5 - Real.sqrt 5) / 8 := by
    simp only [logistic]; linear_combination (-1 / 16 : ℝ) * h5
  have hper : ∀ y, logistic^[2] y = y → logistic y ≠ y →
      Function.minimalPeriod logistic y = 2 := fun y h2 h1 => by
    refine (definition_1_6_1 logistic y (by norm_num)).2 ⟨h2, fun q hq hlt => ?_⟩
    obtain rfl : q = 1 := by omega
    simpa using h1
  refine ⟨e1, e2, hper _ ?_ ?_, hper _ ?_ ?_⟩
  · simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id]
    rw [e1, e2]
  · rw [e1]; intro h; linarith
  · simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id]
    rw [e2, e1]
  · rw [e2]; intro h; linarith

/-- Miao, p. 32: the printed decimals are correct to four places:
`|(5 − √5)/8 − 0.3455| < 0.00005` and `|(5 + √5)/8 − 0.9045| < 0.00005`. -/
theorem logistic_two_cycle_decimals :
    |(5 - Real.sqrt 5) / 8 - 0.3455| < 0.00005 ∧ |(5 + Real.sqrt 5) / 8 - 0.9045| < 0.00005 := by
  have hlo : (2.236 : ℝ) < Real.sqrt 5 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hhi : Real.sqrt 5 < 2.2361 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  constructor <;> rw [abs_lt] <;> constructor <;> linarith

end Miao.NeoclassicalGrowth
