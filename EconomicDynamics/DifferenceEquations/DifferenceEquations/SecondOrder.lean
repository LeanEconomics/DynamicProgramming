/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DifferenceEquations.Scalar
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Scalar second-order linear equations

Miao, §1.3, pp. 12–15, and (1.19), p. 15: `x_{t+2} = a x_{t+1} + b x_t + c z_t` (1.13).

* Characteristic roots: `λ₁ + λ₂ = a`, `λ₁λ₂ = −b` iff `μ² − aμ − b = (μ − λ₁)(μ − λ₂)`
  (`char_roots_iff`); complex roots always exist (`char_roots_exist`); the factorisation (1.15)
  (`eq_1_15`); superposition (`superposition`, `sub_isHomSol`).
* Case 1 (distinct real roots): `c₁λ₁ᵗ + c₂λ₂ᵗ` solves (1.16) (`eq_1_17`) and every solution has
  this form (`eq_1_17_general`); sink (`case1_sink`, also with bounded forcing,
  `case1_sink_bdd`) and indeterminacy (`case1_sink_indeterminate`); source
  (`case1_source`). **Correction:** "explodes" means unbounded, not `|x_t| → ∞`: for roots `±2`
  the solution `2ᵗ + (−2)ᵗ` vanishes at every odd `t` (`case1_source_not_tendsto`). The
  saddle-path solution `x_{t+1} = λ₁x_t − (c/λ₂) Σ λ₂^{−j} z_{t+j}` (`saddlePath`,
  `case1_saddle_eq`) solves (1.13) (`case1_saddle_isSol`), is bounded (`case1_saddle_bdd`), and
  is the unique bounded solution with the given `x₀` (`case1_saddle_unique`, `case1_saddle`).
* Case 2 (repeated root `λ`): `(c₁ + tc₂)λᵗ` solves (1.16) (`case2_solution`), with the book's
  verification (`case2_verification`). **Correction:** it is the general solution only for
  `λ ≠ 0` (`case2_general`); for `λ = 0` the solution `0, 1, 0, 0, …` is not of this form
  (`case2_general_counterexample`). Stability: all solutions converge to 0 iff `|λ| < 1`
  (`case2_stable_iff`).
* Case 3 (complex roots `re^{±iθ}`): the roots (`case3_roots`), the book's complex computation
  (`case3_complex_form`, `case3_conj_real`), real solutions `rᵗ(A cos θt + B sin θt)`
  (`case3_solution`), which are all real solutions when `sin θ ≠ 0` (`case3_general`); damped
  for `r < 1` (`case3_damped`) and explosive (unbounded) for `r > 1` (`case3_explosive`).
* (1.19): `x` solves (1.13) iff `(x_t, x_{t+1})` solves the first-order system (`eq_1_19`,
  `eq_1_19_of_system`).
-/

open Filter Topology

namespace Miao.DifferenceEquations

/-- `x` solves `x_{t+2} = a x_{t+1} + b x_t + c z_t` (Miao, (1.13), p. 12). -/
def IsSecondOrderSol (a b c : ℝ) (z x : ℕ → ℝ) : Prop :=
  ∀ t, x (t + 2) = a * x (t + 1) + b * x t + c * z t

/-- `x` solves the homogeneous equation `x_{t+2} = a x_{t+1} + b x_t` (Miao, (1.16), p. 12). -/
def IsHomSol (a b : ℝ) (x : ℕ → ℝ) : Prop :=
  ∀ t, x (t + 2) = a * x (t + 1) + b * x t

/-- Miao, p. 12: `λ₁ + λ₂ = a` and `λ₁λ₂ = −b` iff `μ² − aμ − b = (μ − λ₁)(μ − λ₂)` for all
`μ`; in particular `λ₁`, `λ₂` are the characteristic roots. -/
theorem char_roots_iff {K : Type*} [Field K] [CharZero K] (a b l1 l2 : K) :
    (l1 + l2 = a ∧ l1 * l2 = -b) ↔ ∀ μ : K, μ ^ 2 - a * μ - b = (μ - l1) * (μ - l2) := by
  constructor
  · rintro ⟨h1, h2⟩ μ
    rw [← h1, show b = -(l1 * l2) by rw [h2, neg_neg]]
    ring
  · intro h
    have h0 := h 0
    have h1 := h 1
    exact ⟨by linear_combination h1 - h0, by linear_combination -h0⟩

/-- Miao, p. 12: the two (possibly complex) characteristic roots exist for all real `a`, `b`. -/
theorem char_roots_exist (a b : ℝ) : ∃ l1 l2 : ℂ, l1 + l2 = a ∧ l1 * l2 = -b := by
  set s : ℂ := ((a : ℂ) ^ 2 + 4 * b) ^ ((2 : ℂ)⁻¹)
  have hs : s ^ 2 = (a : ℂ) ^ 2 + 4 * b := by
    have := Complex.cpow_nat_inv_pow ((a : ℂ) ^ 2 + 4 * b) (n := 2) (by norm_num)
    simp only [Nat.cast_ofNat] at this
    exact this
  refine ⟨(a + s) / 2, (a - s) / 2, by ring, ?_⟩
  linear_combination (-1 / 4 : ℂ) * hs

/-- Miao, (1.15), p. 12: with `λ₁ + λ₂ = a`, `λ₁λ₂ = −b`,
`(L⁻¹ − λ₁)(L⁻¹ − λ₂)x_t = x_{t+2} − a x_{t+1} − b x_t`. -/
theorem eq_1_15 {a b l1 l2 : ℝ} (h1 : l1 + l2 = a) (h2 : l1 * l2 = -b) (x : ℕ → ℝ) (t : ℕ) :
    (x (t + 2) - l2 * x (t + 1)) - l1 * (x (t + 1) - l2 * x t) =
      x (t + 2) - a * x (t + 1) - b * x t := by
  rw [← h1, show b = -(l1 * l2) by rw [h2, neg_neg]]
  ring

/-- Miao, p. 13 (superposition): a homogeneous solution plus a particular solution solves
(1.13). -/
theorem superposition {a b c : ℝ} {z xh xp : ℕ → ℝ} (hh : IsHomSol a b xh)
    (hp : IsSecondOrderSol a b c z xp) : IsSecondOrderSol a b c z (fun t => xh t + xp t) := by
  intro t
  simp only
  rw [hh t, hp t]
  ring

/-- Miao, p. 13: the difference of two solutions of (1.13) solves (1.16), so every solution is
`xᵖ + xʰ`. -/
theorem sub_isHomSol {a b c : ℝ} {z x xp : ℕ → ℝ} (hx : IsSecondOrderSol a b c z x)
    (hp : IsSecondOrderSol a b c z xp) : IsHomSol a b (fun t => x t - xp t) := by
  intro t
  simp only
  rw [hx t, hp t]
  ring

/-- Solutions of (1.16) agreeing at `t = 0, 1` agree everywhere. -/
theorem IsHomSol.ext {a b : ℝ} {x y : ℕ → ℝ} (hx : IsHomSol a b x) (hy : IsHomSol a b y)
    (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  have key : ∀ t, x t = y t ∧ x (t + 1) = y (t + 1) := by
    intro t
    induction t with
    | zero => exact ⟨h0, h1⟩
    | succ n ih => exact ⟨ih.2, by rw [hx n, hy n, ih.1, ih.2]⟩
  exact funext fun t => (key t).1

/-- For a solution of (1.16), `u_t = x_{t+1} − λ₂x_t` satisfies `u_{t+1} = λ₁u_t`. -/
theorem hom_factor {a b l1 l2 : ℝ} (h1 : l1 + l2 = a) (h2 : l1 * l2 = -b) {x : ℕ → ℝ}
    (hx : IsHomSol a b x) (t : ℕ) :
    x (t + 1 + 1) - l2 * x (t + 1) = l1 * (x (t + 1) - l2 * x t) := by
  rw [show t + 1 + 1 = t + 2 from rfl, hx t]
  linear_combination (-x (t + 1)) * h1 + x t * h2

/-- For a solution of (1.13), `u_t = x_{t+1} − λ₂x_t` satisfies `u_{t+1} = λ₁u_t + c z_t`. -/
theorem sol_factor {a b c l1 l2 : ℝ} (h1 : l1 + l2 = a) (h2 : l1 * l2 = -b)
    {z x : ℕ → ℝ} (hx : IsSecondOrderSol a b c z x) (t : ℕ) :
    x (t + 1 + 1) - l2 * x (t + 1) = l1 * (x (t + 1) - l2 * x t) + c * z t := by
  rw [show t + 1 + 1 = t + 2 from rfl, hx t]
  linear_combination (-x (t + 1)) * h1 + x t * h2

/-! ### Case 1: distinct real roots -/

/-- **Case 1** (Miao, (1.17), p. 13): `c₁λ₁ᵗ + c₂λ₂ᵗ` solves (1.16). -/
theorem eq_1_17 {a b l1 l2 : ℝ} (h1 : l1 + l2 = a) (h2 : l1 * l2 = -b) (c1 c2 : ℝ) :
    IsHomSol a b (fun t => c1 * l1 ^ t + c2 * l2 ^ t) := by
  intro t
  have hr1 : l1 ^ 2 = a * l1 + b := by rw [← h1, show b = -(l1 * l2) by rw [h2, neg_neg]]; ring
  have hr2 : l2 ^ 2 = a * l2 + b := by rw [← h1, show b = -(l1 * l2) by rw [h2, neg_neg]]; ring
  simp only [pow_add, pow_one]
  linear_combination c1 * l1 ^ t * hr1 + c2 * l2 ^ t * hr2

/-- **Case 1** (Miao, (1.17), p. 13): for distinct roots every solution of (1.16) is
`c₁λ₁ᵗ + c₂λ₂ᵗ`, with `c₁ = (x₁ − λ₂x₀)/(λ₁ − λ₂)`, `c₂ = (λ₁x₀ − x₁)/(λ₁ − λ₂)`. -/
theorem eq_1_17_general {a b l1 l2 : ℝ} (h1 : l1 + l2 = a) (h2 : l1 * l2 = -b) (hne : l1 ≠ l2)
    {x : ℕ → ℝ} (hx : IsHomSol a b x) :
    x = fun t => (x 1 - l2 * x 0) / (l1 - l2) * l1 ^ t + (l1 * x 0 - x 1) / (l1 - l2) * l2 ^ t := by
  have hd : l1 - l2 ≠ 0 := sub_ne_zero.2 hne
  refine hx.ext (eq_1_17 h1 h2 _ _) ?_ ?_
  · simp only [pow_zero, mul_one]; field_simp; ring
  · simp only [pow_one]; field_simp; ring

/-- **Case 1, sink** (Miao, p. 13): if `|λ₁| < 1` and `|λ₂| < 1`, every solution of (1.16)
converges to the steady state `0`. -/
theorem case1_sink {a b l1 l2 : ℝ} (h1 : l1 + l2 = a) (h2 : l1 * l2 = -b) (hl1 : |l1| < 1)
    (hl2 : |l2| < 1) {x : ℕ → ℝ} (hx : IsHomSol a b x) : Tendsto x atTop (𝓝 0) := by
  have hu : ∀ t, x (t + 1 + 1) - l2 * x (t + 1) = l1 * (x (t + 1) - l2 * x t) :=
    hom_factor h1 h2 hx
  have hu0 : Tendsto (fun t => x (t + 1) - l2 * x t) atTop (𝓝 0) := by
    have := (pow_mul_tendsto_zero_iff (b := l1) (k := 1) one_ne_zero).2 hl1
    have h := this.mul_const (x 1 - l2 * x 0)
    simp only [mul_one, zero_mul] at h
    exact h.congr (fun t => (geom_eq (x := fun t => x (t + 1) - l2 * x t) hu t).symm)
  exact tendsto_zero_of_forced hl2 (fun t => by ring) hu0

/-- **Case 1, sink** (Miao, p. 13): with bounded forcing and `|λ₁|, |λ₂| < 1`, every solution
of (1.13) is bounded, whatever `x₀` and `x₁`. -/
theorem case1_sink_bdd {a b c l1 l2 : ℝ} (h1 : l1 + l2 = a) (h2 : l1 * l2 = -b)
    (hl1 : |l1| < 1) (hl2 : |l2| < 1) {z x : ℕ → ℝ} (hz : BddSeq z)
    (hx : IsSecondOrderSol a b c z x) : BddSeq x := by
  have hu : BddSeq (fun t => x (t + 1) - l2 * x t) := by
    refine bddSeq_of_forced hl1 (w := fun t => c * z t) (fun t => sol_factor h1 h2 hx t) ?_
    obtain ⟨M, hM⟩ := hz
    exact ⟨|c| * M, fun t => by
      change |c * z t| ≤ _
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM t) (abs_nonneg c)⟩
  exact bddSeq_of_forced hl2 (fun t => by ring) hu

/-- **Case 1, sink: indeterminacy** (Miao, p. 13): the initial value `x₀` does not pin down the
solution: `λ₁ᵗ` and `λ₂ᵗ` are distinct convergent solutions with `x₀ = 1`. -/
theorem case1_sink_indeterminate {a b l1 l2 : ℝ} (h1 : l1 + l2 = a) (h2 : l1 * l2 = -b)
    (hne : l1 ≠ l2) (hl1 : |l1| < 1) (hl2 : |l2| < 1) :
    ∃ x y : ℕ → ℝ, IsHomSol a b x ∧ IsHomSol a b y ∧ x 0 = y 0 ∧ x ≠ y ∧
      Tendsto x atTop (𝓝 0) ∧ Tendsto y atTop (𝓝 0) := by
  have hx := eq_1_17 h1 h2 1 0
  have hy := eq_1_17 h1 h2 0 1
  refine ⟨_, _, hx, hy, by simp, fun h => hne ?_, case1_sink h1 h2 hl1 hl2 hx,
    case1_sink h1 h2 hl1 hl2 hy⟩
  simpa using congrFun h 1

/-- **Case 1, source** (Miao, p. 13): if `|λ₁| > 1` and `|λ₂| > 1` (distinct), every solution
of (1.16) other than `0` explodes (is unbounded). -/
theorem case1_source {a b l1 l2 : ℝ} (h1 : l1 + l2 = a) (h2 : l1 * l2 = -b) (hne : l1 ≠ l2)
    (hl1 : 1 < |l1|) (hl2 : 1 < |l2|) {x : ℕ → ℝ} (hx : IsHomSol a b x)
    (h0 : x 0 ≠ 0 ∨ x 1 ≠ 0) : ¬ BddSeq x := by
  rintro ⟨M, hM⟩
  have hbu : ∀ l : ℝ, BddSeq (fun t => x (t + 1) - l * x t) := fun l =>
    ⟨M + |l| * M, fun t => (abs_sub _ _).trans (add_le_add (hM _)
      (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)))⟩
  have hu := (geom_bdd_iff hl1 (x := fun t => x (t + 1) - l2 * x t)
    (hom_factor h1 h2 hx)).1 (hbu l2)
  have hv := (geom_bdd_iff hl2 (x := fun t => x (t + 1) - l1 * x t)
    (hom_factor (by linarith) (by linarith) hx)).1 (hbu l1)
  simp only [zero_add] at hu hv
  have hd : (l1 - l2) * x 0 = 0 := by linarith
  have hx0 : x 0 = 0 := (mul_eq_zero.1 hd).resolve_left (sub_ne_zero.2 hne)
  rw [hx0, mul_zero, sub_zero] at hu
  rcases h0 with h | h
  · exact h hx0
  · exact h hu

/-- **Correction** (Miao, p. 13, "this solution explodes"): in a source the solution need not
satisfy `|x_t| → ∞`. For `x_{t+2} = 4x_t` (roots `±2`), `x_t = 2ᵗ + (−2)ᵗ` is a solution that
vanishes at every odd `t`. -/
theorem case1_source_not_tendsto :
    IsHomSol 0 4 (fun t => 2 ^ t + (-2) ^ t) ∧ (∀ k, (2 : ℝ) ^ (2 * k + 1) + (-2) ^ (2 * k + 1) = 0)
      ∧ ¬ Tendsto (fun t => |(2 : ℝ) ^ t + (-2) ^ t|) atTop atTop := by
  have hodd : ∀ k, (2 : ℝ) ^ (2 * k + 1) + (-2) ^ (2 * k + 1) = 0 := fun k => by
    rw [pow_succ, pow_succ, pow_mul, pow_mul]; norm_num
  refine ⟨fun t => by simp only [pow_add]; ring, hodd, fun h => ?_⟩
  obtain ⟨N, hN⟩ := (tendsto_atTop.1 h 1).exists_forall_of_atTop
  have := hN (2 * N + 1) (by omega)
  rw [hodd N, abs_zero] at this
  norm_num at this

/-- The saddle path of Case 1 (Miao, p. 13): `x₀` given and
`x_{t+1} = λ₁x_t + w_t`, `w_t = −(c/λ₂) Σ_j (1/λ₂)ʲ z_{t+j}` (the forward solution (1.8)). -/
noncomputable def saddlePath (l1 l2 c : ℝ) (z : ℕ → ℝ) (x0 : ℝ) : ℕ → ℝ
  | 0 => x0
  | t + 1 => l1 * saddlePath l1 l2 c z x0 t + fwdSol l2 c z t

/-- **Case 1, saddle path** (Miao, p. 13): the saddle path satisfies the displayed equation
`x_{t+1} = λ₁x_t − (c/λ₂) Σ_{j≥0} λ₂^{−j} z_{t+j}`. -/
theorem case1_saddle_eq (l1 l2 c : ℝ) (z : ℕ → ℝ) (x0 : ℝ) (t : ℕ) :
    saddlePath l1 l2 c z x0 (t + 1) = l1 * saddlePath l1 l2 c z x0 t -
      c / l2 * ∑' j : ℕ, l2 ^ (-(j : ℤ)) * z (t + j) := by
  simp only [saddlePath, fwdSol, zpow_neg, zpow_natCast, inv_pow, one_div]
  ring

/-- **Case 1, saddle path** (Miao, pp. 13–14): for `|λ₂| > 1` and bounded `z` the saddle path
solves (1.13). -/
theorem case1_saddle_isSol {a b c l1 l2 : ℝ} (h1 : l1 + l2 = a) (h2 : l1 * l2 = -b)
    (hl2 : 1 < |l2|) {z : ℕ → ℝ} (hz : BddSeq z) (x0 : ℝ) :
    IsSecondOrderSol a b c z (saddlePath l1 l2 c z x0) := by
  intro t
  have hw := eq_1_8_isScalarSol (c := c) hl2 hz t
  have e1 : saddlePath l1 l2 c z x0 (t + 2) =
      l1 * saddlePath l1 l2 c z x0 (t + 1) + fwdSol l2 c z (t + 1) := rfl
  have e2 : saddlePath l1 l2 c z x0 (t + 1) =
      l1 * saddlePath l1 l2 c z x0 t + fwdSol l2 c z t := rfl
  rw [e1, hw, ← h1, show b = -(l1 * l2) by rw [h2, neg_neg]]
  linear_combination (-l2) * e2

/-- **Case 1, saddle path** (Miao, p. 14): for `|λ₁| < 1 < |λ₂|` and bounded `z` the saddle path
is bounded. -/
theorem case1_saddle_bdd {l1 l2 c : ℝ} (hl1 : |l1| < 1) (hl2 : 1 < |l2|) {z : ℕ → ℝ}
    (hz : BddSeq z) (x0 : ℝ) : BddSeq (saddlePath l1 l2 c z x0) :=
  bddSeq_of_forced hl1 (fun _ => rfl) (eq_1_8_bdd hl2 hz)

/-- **Case 1, saddle path** (Miao, p. 14): for `|λ₁| < 1 < |λ₂|` and bounded `z`, any bounded
solution of (1.13) with initial value `x₀` is the saddle path. -/
theorem case1_saddle_unique {a b c l1 l2 : ℝ} (h1 : l1 + l2 = a) (h2 : l1 * l2 = -b)
    (hl1 : |l1| < 1) (hl2 : 1 < |l2|) {z x : ℕ → ℝ} (hz : BddSeq z)
    (hx : IsSecondOrderSol a b c z x) (hB : BddSeq x) : x = saddlePath l1 l2 c z (x 0) := by
  set y := saddlePath l1 l2 c z (x 0)
  have hD := sub_isHomSol hx (case1_saddle_isSol h1 h2 hl2 hz (x 0))
  have hDB : BddSeq (fun t => x t - y t) := by
    obtain ⟨M, hM⟩ := hB
    obtain ⟨M', hM'⟩ := case1_saddle_bdd (c := c) hl1 hl2 hz (x 0)
    exact ⟨M + M', fun t => (abs_sub _ _).trans (add_le_add (hM t) (hM' t))⟩
  set v : ℕ → ℝ := fun t => (x (t + 1) - y (t + 1)) - l1 * (x t - y t) with hvdef
  have hv : ∀ t, v (t + 1) = l2 * v t := fun t => by
    have := hom_factor (l1 := l2) (l2 := l1) (by linarith) (by linarith) hD t
    simp only [hvdef]
    linarith
  have hvB : BddSeq v := by
    obtain ⟨M, hM⟩ := hDB
    exact ⟨M + |l1| * M, fun t => (abs_sub _ _).trans (add_le_add (hM _)
      (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)))⟩
  have hv0 := (geom_bdd_iff hl2 hv).1 hvB
  have hvall : ∀ t, v t = 0 := fun t => by
    rw [geom_eq hv t, hv0, mul_zero]
  have hD0 : x 0 - y 0 = 0 := by simp [y, saddlePath]
  have hg : ∀ t, x (t + 1) - y (t + 1) = l1 * (x t - y t) := fun t => by
    have := hvall t
    simp only [hvdef] at this
    linarith
  ext t
  have := geom_eq (x := fun t => x t - y t) hg t
  simp only [hD0, mul_zero] at this
  linarith

/-- **Case 1, saddle path** (Miao, pp. 13–14): for `|λ₁| < 1 < |λ₂|` and bounded `z`, for each
`x₀` there is exactly one bounded solution of (1.13) starting at `x₀`: the saddle path. -/
theorem case1_saddle {a b c l1 l2 : ℝ} (h1 : l1 + l2 = a) (h2 : l1 * l2 = -b)
    (hl1 : |l1| < 1) (hl2 : 1 < |l2|) {z : ℕ → ℝ} (hz : BddSeq z) (x0 : ℝ) :
    ∃! x : ℕ → ℝ, x 0 = x0 ∧ IsSecondOrderSol a b c z x ∧ BddSeq x := by
  refine ⟨saddlePath l1 l2 c z x0, ⟨rfl, case1_saddle_isSol h1 h2 hl2 hz x0,
    case1_saddle_bdd hl1 hl2 hz x0⟩, fun x ⟨hx0, hx, hB⟩ => ?_⟩
  rw [case1_saddle_unique h1 h2 hl1 hl2 hz hx hB, hx0]

/-! ### Case 2: a repeated root -/

/-- **Case 2** (Miao, p. 14): with the repeated root `λ` (`a = 2λ`, `b = −λ²`), `(c₁ + tc₂)λᵗ`
solves (1.16). -/
theorem case2_solution (l c1 c2 : ℝ) :
    IsHomSol (2 * l) (-l ^ 2) (fun t => (c1 + t * c2) * l ^ t) := by
  intro t
  push_cast
  simp only [pow_add]
  ring

/-- **Case 2** (Miao, p. 14): the book's verification. With `(L⁻¹ − λ)y_t = y_{t+1} − λy_t`,
`(L⁻¹ − λ)²x_t = x_{t+2} − 2λx_{t+1} + λ²x_t`, `(L⁻¹ − λ)[(c₁ + tc₂)λᵗ] = c₂λ^{t+1}` and
`(L⁻¹ − λ)[c₂λ^{t+1}] = 0`. -/
theorem case2_verification (l c1 c2 : ℝ) (x : ℕ → ℝ) (t : ℕ) :
    ((x (t + 2) - l * x (t + 1)) - l * (x (t + 1) - l * x t) =
        x (t + 2) - 2 * l * x (t + 1) - (-l ^ 2) * x t) ∧
      ((c1 + ((t + 1 : ℕ) : ℝ) * c2) * l ^ (t + 1) - l * ((c1 + t * c2) * l ^ t) =
        c2 * l ^ (t + 1)) ∧
      c2 * l ^ (t + 1 + 1) - l * (c2 * l ^ (t + 1)) = 0 := by
  refine ⟨by ring, ?_, by rw [pow_succ _ (t + 1)]; ring⟩
  push_cast
  rw [pow_succ]
  ring

/-- **Case 2, corrected** (Miao, p. 14): for `λ ≠ 0` every solution of (1.16) is
`(c₁ + tc₂)λᵗ` with `c₁ = x₀`, `c₂ = (x₁ − λx₀)/λ`. -/
theorem case2_general {l : ℝ} (hl : l ≠ 0) {x : ℕ → ℝ} (hx : IsHomSol (2 * l) (-l ^ 2) x) :
    x = fun t : ℕ => (x 0 + (t : ℝ) * ((x 1 - l * x 0) / l)) * l ^ t := by
  refine hx.ext (case2_solution _ _ _) ?_ ?_
  · simp
  · simp only [Nat.cast_one, one_mul, pow_one]; field_simp; ring

/-- **Counterexample to Case 2 as printed** (Miao, p. 14): for the repeated root `λ = 0`
(`a = b = 0`), `x = (0, 1, 0, 0, …)` solves (1.16) but is not `(c₁ + tc₂)0ᵗ` for any
`c₁, c₂`. -/
theorem case2_general_counterexample :
    IsHomSol (2 * 0) (-0 ^ 2) (fun t => if t = 1 then 1 else 0) ∧
      ¬ ∃ c1 c2 : ℝ, ∀ t : ℕ, (if t = 1 then (1 : ℝ) else 0) = (c1 + t * c2) * 0 ^ t := by
  refine ⟨fun t => by simp, ?_⟩
  rintro ⟨c1, c2, h⟩
  have := h 1
  simp at this

/-- **Case 2, stability** (Miao, p. 14): with a repeated root `λ`, every solution of (1.16)
converges to `0` iff `|λ| < 1`. -/
theorem case2_stable_iff (l : ℝ) :
    (∀ x, IsHomSol (2 * l) (-l ^ 2) x → Tendsto x atTop (𝓝 0)) ↔ |l| < 1 := by
  constructor
  · intro h
    have := h _ (case2_solution l 1 0)
    simp only [mul_zero, add_zero, one_mul] at this
    exact (pow_mul_tendsto_zero_iff (b := l) one_ne_zero).1 (by simpa using this)
  · intro hl x hx
    exact case1_sink (l1 := l) (l2 := l) (by ring) (by ring) hl hl hx

/-! ### Case 3: complex roots -/

/-- **Case 3** (Miao, p. 14): `λ₁ = re^{iθ}`, `λ₂ = re^{−iθ}` are the characteristic roots of
`μ² − aμ − b` for `a = 2r cos θ`, `b = −r²`. -/
theorem case3_roots (r θ : ℝ) :
    (r * Complex.exp (θ * Complex.I)) + (r * Complex.exp (-θ * Complex.I)) =
        ((2 * r * Real.cos θ : ℝ) : ℂ) ∧
      (r * Complex.exp (θ * Complex.I)) * (r * Complex.exp (-θ * Complex.I)) =
        -((-r ^ 2 : ℝ) : ℂ) := by
  constructor
  · rw [Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    push_cast
    ring
  · rw [mul_mul_mul_comm, ← Complex.exp_add]
    push_cast
    ring_nf
    simp

/-- **Case 3** (Miao, p. 14): the book's computation
`c₁λ₁ᵗ + c₂λ₂ᵗ = rᵗ[(c₁ + c₂) cos θt + (c₁ − c₂) i sin θt]` for `λ₁,₂ = re^{±iθ}`. -/
theorem case3_complex_form (r θ : ℝ) (c1 c2 : ℂ) (t : ℕ) :
    c1 * (r * Complex.exp (θ * Complex.I)) ^ t + c2 * (r * Complex.exp (-θ * Complex.I)) ^ t =
      (r : ℂ) ^ t * ((c1 + c2) * (Real.cos (θ * t) : ℂ) +
        (c1 - c2) * (Real.sin (θ * t) : ℂ) * Complex.I) := by
  rw [mul_pow, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    show (t : ℂ) * (θ * Complex.I) = ((θ * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
    show (t : ℂ) * (-θ * Complex.I) = ((-(θ * t) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-- **Case 3** (Miao, p. 15): if `c₂ = c̄₁` then `c₁ + c₂` and `(c₁ − c₂)i` are real. -/
theorem case3_conj_real (c : ℂ) :
    (c + (starRingEnd ℂ) c).im = 0 ∧ ((c - (starRingEnd ℂ) c) * Complex.I).im = 0 := by
  simp

/-- **Case 3** (Miao, p. 15): with conjugate constants `c₂ = c̄₁` the complex solution is the
real `rᵗ[A cos θt + B sin θt]`, `A = 2 Re c₁`, `B = −2 Im c₁`. -/
theorem case3_real_form (r θ : ℝ) (c : ℂ) (t : ℕ) :
    c * (r * Complex.exp (θ * Complex.I)) ^ t +
        (starRingEnd ℂ) c * (r * Complex.exp (-θ * Complex.I)) ^ t =
      ((r ^ t * (2 * c.re * Real.cos (θ * t) + (-2 * c.im) * Real.sin (θ * t)) : ℝ) : ℂ) := by
  rw [case3_complex_form]
  apply Complex.ext <;> simp <;> ring

/-- **Case 3** (Miao, p. 15): `rᵗ[A cos θt + B sin θt]` solves (1.16) for the complex roots
`re^{±iθ}`, i.e. `a = 2r cos θ`, `b = −r²`. -/
theorem case3_solution (r θ A B : ℝ) :
    IsHomSol (2 * r * Real.cos θ) (-r ^ 2)
      (fun t : ℕ => r ^ t * (A * Real.cos (θ * t) + B * Real.sin (θ * t))) := by
  intro t
  have hc : Real.cos (θ * ((t + 2 : ℕ) : ℝ)) =
      2 * Real.cos θ * Real.cos (θ * ((t + 1 : ℕ) : ℝ)) - Real.cos (θ * t) := by
    push_cast
    rw [show θ * ((t : ℝ) + 2) = θ * (t + 1) + θ by ring,
      show θ * (t : ℝ) = θ * (t + 1) - θ by ring, Real.cos_add, Real.cos_sub]
    ring
  have hs : Real.sin (θ * ((t + 2 : ℕ) : ℝ)) =
      2 * Real.cos θ * Real.sin (θ * ((t + 1 : ℕ) : ℝ)) - Real.sin (θ * t) := by
    push_cast
    rw [show θ * ((t : ℝ) + 2) = θ * (t + 1) + θ by ring,
      show θ * (t : ℝ) = θ * (t + 1) - θ by ring, Real.sin_add, Real.sin_sub]
    ring
  simp only
  rw [hc, hs, pow_add, pow_add]
  ring

/-- **Case 3** (Miao, p. 15): for genuinely complex roots (`r ≠ 0`, `sin θ ≠ 0`) every real
solution of (1.16) is `rᵗ[A cos θt + B sin θt]`, with `A = x₀`,
`B = (x₁ − r cos θ x₀)/(r sin θ)`. -/
theorem case3_general {r θ : ℝ} (hr : r ≠ 0) (hs : Real.sin θ ≠ 0) {x : ℕ → ℝ}
    (hx : IsHomSol (2 * r * Real.cos θ) (-r ^ 2) x) :
    x = fun t : ℕ => r ^ t * (x 0 * Real.cos (θ * t) +
      (x 1 - r * Real.cos θ * x 0) / (r * Real.sin θ) * Real.sin (θ * t)) := by
  refine hx.ext (case3_solution _ _ _ _) ?_ ?_
  · simp
  · simp only [pow_one, Nat.cast_one, mul_one]
    field_simp
    ring

/-- **Case 3** (Miao, p. 15): for `0 ≤ r < 1` the oscillations are damped:
`rᵗ[A cos θt + B sin θt] → 0`. -/
theorem case3_damped_form {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (θ A B : ℝ) :
    Tendsto (fun t : ℕ => r ^ t * (A * Real.cos (θ * t) + B * Real.sin (θ * t))) atTop
      (𝓝 0) := by
  refine squeeze_zero_norm (a := fun t => r ^ t * (|A| + |B|)) (fun t => ?_) ?_
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hr0 t)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hr0 t)
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    · rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr).mul_const (|A| + |B|)

/-- **Case 3** (Miao, p. 15): for `0 < r < 1` and `sin θ ≠ 0` every solution of (1.16)
converges to `0`. -/
theorem case3_damped {r θ : ℝ} (hr0 : 0 < r) (hr : r < 1) (hs : Real.sin θ ≠ 0) {x : ℕ → ℝ}
    (hx : IsHomSol (2 * r * Real.cos θ) (-r ^ 2) x) : Tendsto x atTop (𝓝 0) := by
  rw [case3_general hr0.ne' hs hx]
  exact case3_damped_form hr0.le hr θ _ _

/-- **Case 3** (Miao, p. 15): for `r > 1` and `sin θ ≠ 0` the oscillations are explosive: every
nonzero solution of (1.16) is unbounded. The proof uses the invariant
`Q_t = x_{t+1}² − a x_t x_{t+1} + r² x_t² = |x_{t+1} − λ₂x_t|²`, which grows like `r^{2t}`. -/
theorem case3_explosive {r θ : ℝ} (hr : 1 < r) (hs : Real.sin θ ≠ 0) {x : ℕ → ℝ}
    (hx : IsHomSol (2 * r * Real.cos θ) (-r ^ 2) x) (h0 : x 0 ≠ 0 ∨ x 1 ≠ 0) : ¬ BddSeq x := by
  set a := 2 * r * Real.cos θ
  set Q : ℕ → ℝ := fun t => x (t + 1) ^ 2 - a * x t * x (t + 1) + r ^ 2 * x t ^ 2 with hQdef
  have hQ : ∀ t, Q (t + 1) = r ^ 2 * Q t := fun t => by
    simp only [hQdef]
    rw [show t + 1 + 1 = t + 2 from rfl, hx t]
    ring
  have hQ0 : 0 < Q 0 := by
    have hcs := Real.sin_sq_add_cos_sq θ
    have heq : Q 0 = (x 1 - r * Real.cos θ * x 0) ^ 2 + r ^ 2 * Real.sin θ ^ 2 * x 0 ^ 2 := by
      simp only [hQdef, a]
      linear_combination (-(r ^ 2 * x 0 ^ 2)) * hcs
    rw [heq]
    rcases h0 with h | h
    · have : 0 < r ^ 2 * Real.sin θ ^ 2 * x 0 ^ 2 := by positivity
      nlinarith [sq_nonneg (x 1 - r * Real.cos θ * x 0)]
    · by_cases hx0 : x 0 = 0
      · rw [hx0]; simp only [mul_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow, add_zero]; positivity
      · have : 0 < r ^ 2 * Real.sin θ ^ 2 * x 0 ^ 2 := by positivity
        nlinarith [sq_nonneg (x 1 - r * Real.cos θ * x 0)]
  rintro ⟨M, hM⟩
  have hsq : ∀ t, x t ^ 2 ≤ M ^ 2 := fun t => by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hM t) 2
  have hxy : ∀ t, |a * x t * x (t + 1)| ≤ |a| * (M * M) := fun t => by
    rw [abs_mul, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hM t) (hM _) (abs_nonneg _)
      ((abs_nonneg _).trans (hM t))) (abs_nonneg _)
  have hbound : ∀ t, Q t ≤ M ^ 2 + |a| * (M * M) + r ^ 2 * M ^ 2 := fun t => by
    simp only [hQdef]
    have := neg_abs_le (a * x t * x (t + 1))
    nlinarith [hsq t, hsq (t + 1), hxy t, sq_nonneg r]
  have hr2 : 1 < |r ^ 2| := by rw [abs_of_pos (by positivity)]; nlinarith
  obtain ⟨t, ht⟩ := ((abs_pow_mul_tendsto_atTop hr2 hQ0.ne').eventually_gt_atTop
    (M ^ 2 + |a| * (M * M) + r ^ 2 * M ^ 2)).exists
  have hQt : Q t = (r ^ 2) ^ t * Q 0 := geom_eq hQ t
  have hpos : 0 < Q t := by rw [hQt]; positivity
  rw [← hQt, abs_of_pos hpos] at ht
  linarith [hbound t]

/-! ### The first-order form (1.19) -/

/-- Miao, (1.19), p. 15: `x` solves (1.13) iff `X_t = (x_t, x_{t+1})` solves the first-order
system `X_{t+1} = [[0, 1], [b, a]] X_t + [0; c] z_t`, written as (1.20) with `A = I`. -/
theorem eq_1_19 (a b c : ℝ) (z x : ℕ → ℝ) :
    IsSecondOrderSol a b c z x ↔
      IsSolution (1 : Matrix (Fin 2) (Fin 2) ℝ) !![0, 1; b, a] !![0; c] (fun t => ![z t])
        (fun t => ![x t, x (t + 1)]) := by
  simp only [IsSolution, Matrix.one_mulVec]
  constructor
  · intro h t
    ext i
    fin_cases i
    · simp
    · simp [h t]
      ring
  · intro h t
    have := congrFun (h t) 1
    simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.mulVec_cons, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.mulVec_empty, add_zero,
      Pi.add_apply, Pi.smul_apply, Function.comp_apply, Matrix.head_cons, smul_eq_mul,
      Matrix.tail_cons] at this
    rw [show t + 2 = t + 1 + 1 from rfl, this]
    ring

/-- Miao, (1.19), p. 15: conversely, a solution `X` of the first-order system has
`X_t = (x_t, x_{t+1})` with `x_t = X_t(0)` a solution of (1.13). -/
theorem eq_1_19_of_system {a b c : ℝ} {z : ℕ → ℝ} {X : ℕ → Fin 2 → ℝ}
    (h : IsSolution (1 : Matrix (Fin 2) (Fin 2) ℝ) !![0, 1; b, a] !![0; c] (fun t => ![z t]) X) :
    IsSecondOrderSol a b c z (fun t => X t 0) ∧ ∀ t, X t = ![X t 0, X (t + 1) 0] := by
  simp only [IsSolution, Matrix.one_mulVec] at h
  have h0 : ∀ t, X (t + 1) 0 = X t 1 := fun t => by
    have := congrFun (h t) 0
    rw [show X t = ![X t 0, X t 1] by ext i; fin_cases i <;> rfl] at this
    simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.mulVec_cons,
      Matrix.mulVec_empty, add_zero, Pi.add_apply, Pi.smul_apply, Function.comp_apply,
      Matrix.cons_val_zero, Matrix.head_cons, smul_eq_mul, mul_zero, Matrix.tail_cons, mul_one,
      zero_add] at this
    linarith
  have h1 : ∀ t, X (t + 1) 1 = b * X t 0 + a * X t 1 + c * z t := fun t => by
    have := congrFun (h t) 1
    rw [show X t = ![X t 0, X t 1] by ext i; fin_cases i <;> rfl] at this
    simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.mulVec_cons,
      Matrix.mulVec_empty, add_zero, Pi.add_apply, Pi.smul_apply, Function.comp_apply,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, smul_eq_mul,
      Matrix.tail_cons] at this
    linarith
  refine ⟨fun t => ?_, fun t => ?_⟩
  · simp only
    rw [show t + 2 = t + 1 + 1 from rfl, h0, h1, h0]
    ring
  · ext i
    fin_cases i
    · simp
    · simp [h0]

end Miao.DifferenceEquations
