/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DifferenceEquations.Scalar
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Phase diagrams

Miao, §1.5, pp. 27–28: the linear system
`x_{t+1} = ã x_t + b y_t − e`, `y_{t+1} = c x_t − d̃ y_t + f` with `a = ã − 1`, `d = d̃ + 1`
and `a, b, c, d, e, f > 0`; `x₀` is given.

**A 2×2 saddle toolkit** (used again in `Exercises.lean`). For the homogeneous system
`X_{t+1} = m₁₁X_t + m₁₂Y_t`, `Y_{t+1} = m₂₁X_t + m₂₂Y_t` (`IsSol22`) with characteristic
polynomial `p(μ) = μ² − (m₁₁ + m₂₂)μ + (m₁₁m₂₂ − m₁₂m₂₁)` (`cp22`) and `p(1) < 0`: the roots
`λ_lo < 1 < λ_hi` are real (`roots22_lt`); `λ_lo > −1 ⟺ p(−1) > 0` (`lamLo_gt_neg_one_iff`);
`s_t = m₂₁X_t + (λ − m₁₁)Y_t` is geometric at rate `λ` for each root (`sVar_succ`); a bounded
solution has `s^hi = 0` (`sHi_zero_of_bdd`); and, when `m₁₂m₂₁ > 0`, for `X₀` predetermined the
saddle path `Y₀ = kX₀`, `k = (λ_lo − m₁₁)/m₁₂` (`saddle22`) is the unique bounded solution and
converges iff `p(−1) > 0` (`saddle22_unique`, `saddle22_tendsto`, `saddle22_unbounded`,
`saddle22_iff`, `saddle22_only_zero`).

**The book's system.** The Δ-form (`phase_delta`), the isocline equivalences
(`phase_isocline_x`, `phase_isocline_y`), the unique steady state (`phase_steady_state`), and
the roots of `[[1 + a, b], [c, 1 − d]]`: real, one below and one above `1` (`phase_roots`).

**Correction.** The book says the phase diagram shows a convergent saddle path with all other
paths diverging. The second root lies in `(−1, 1)` only when `(2 + a)(2 − d) > bc`
(`phase_lamLo_iff`). Under that condition each `x₀` has exactly one convergent path, on the
downward-sloping saddle line, and every other path is unbounded (`phase_saddle`,
`phase_saddle_slope`); and "every `x₀` has a convergent path" is equivalent to the condition
(`phase_saddle_iff`). For `a = b = c = e = f = 1`, `d = 3` both roots are unstable and the
steady state is the only bounded path (`phase_counterexample`).
-/

open Filter Topology

namespace Miao.DifferenceEquations

/-! ### A 2×2 saddle toolkit -/

/-- `(X, Y)` solves `X_{t+1} = m₁₁X_t + m₁₂Y_t`, `Y_{t+1} = m₂₁X_t + m₂₂Y_t`. -/
def IsSol22 (m11 m12 m21 m22 : ℝ) (X Y : ℕ → ℝ) : Prop :=
  ∀ t, X (t + 1) = m11 * X t + m12 * Y t ∧ Y (t + 1) = m21 * X t + m22 * Y t

/-- The characteristic polynomial `p(μ) = μ² − tr μ + det` of `[[m₁₁, m₁₂], [m₂₁, m₂₂]]`. -/
def cp22 (m11 m12 m21 m22 μ : ℝ) : ℝ :=
  μ ^ 2 - (m11 + m22) * μ + (m11 * m22 - m12 * m21)

/-- The discriminant `tr² − 4 det`. -/
def disc22 (m11 m12 m21 m22 : ℝ) : ℝ :=
  (m11 + m22) ^ 2 - 4 * (m11 * m22 - m12 * m21)

/-- The smaller root `(tr − √disc)/2`. -/
noncomputable def lamLo (m11 m12 m21 m22 : ℝ) : ℝ :=
  ((m11 + m22) - Real.sqrt (disc22 m11 m12 m21 m22)) / 2

/-- The larger root `(tr + √disc)/2`. -/
noncomputable def lamHi (m11 m12 m21 m22 : ℝ) : ℝ :=
  ((m11 + m22) + Real.sqrt (disc22 m11 m12 m21 m22)) / 2

/-- The variable `s_t = m₂₁X_t + (λ − m₁₁)Y_t` attached to the root `λ` (a left eigenvector). -/
def sVar (m11 m21 l : ℝ) (X Y : ℕ → ℝ) (t : ℕ) : ℝ :=
  m21 * X t + (l - m11) * Y t

variable {m11 m12 m21 m22 : ℝ}

theorem disc22_pos (h1 : cp22 m11 m12 m21 m22 1 < 0) : 0 < disc22 m11 m12 m21 m22 := by
  simp only [cp22, disc22] at *
  nlinarith [sq_nonneg (m11 + m22 - 2)]

theorem cp22_factor (h1 : cp22 m11 m12 m21 m22 1 < 0) (μ : ℝ) :
    cp22 m11 m12 m21 m22 μ = (μ - lamLo m11 m12 m21 m22) * (μ - lamHi m11 m12 m21 m22) := by
  have hs := Real.sq_sqrt (disc22_pos h1).le
  simp only [cp22, lamLo, lamHi, disc22] at *
  linear_combination (1 / 4) * hs

theorem cp22_lamLo (h1 : cp22 m11 m12 m21 m22 1 < 0) :
    cp22 m11 m12 m21 m22 (lamLo m11 m12 m21 m22) = 0 := by
  rw [cp22_factor h1]; ring

theorem cp22_lamHi (h1 : cp22 m11 m12 m21 m22 1 < 0) :
    cp22 m11 m12 m21 m22 (lamHi m11 m12 m21 m22) = 0 := by
  rw [cp22_factor h1]; ring

theorem lamLo_lt_lamHi (h1 : cp22 m11 m12 m21 m22 1 < 0) :
    lamLo m11 m12 m21 m22 < lamHi m11 m12 m21 m22 := by
  have := Real.sqrt_pos.2 (disc22_pos h1)
  simp only [lamLo, lamHi]
  linarith

/-- With `p(1) < 0` the two roots are real with `λ_lo < 1 < λ_hi`. -/
theorem roots22_lt (h1 : cp22 m11 m12 m21 m22 1 < 0) :
    lamLo m11 m12 m21 m22 < 1 ∧ 1 < lamHi m11 m12 m21 m22 := by
  have hf := cp22_factor h1 1
  have hlt := lamLo_lt_lamHi h1
  rw [hf] at h1
  constructor <;> nlinarith

/-- With `p(1) < 0`: `λ_lo > −1 ⟺ p(−1) > 0`. -/
theorem lamLo_gt_neg_one_iff (h1 : cp22 m11 m12 m21 m22 1 < 0) :
    -1 < lamLo m11 m12 m21 m22 ↔ 0 < cp22 m11 m12 m21 m22 (-1) := by
  have hf := cp22_factor h1 (-1)
  have hhi := (roots22_lt h1).2
  rw [hf]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- With `p(1) < 0`: `|λ_lo| < 1 ⟺ p(−1) > 0`. -/
theorem abs_lamLo_lt_one_iff (h1 : cp22 m11 m12 m21 m22 1 < 0) :
    |lamLo m11 m12 m21 m22| < 1 ↔ 0 < cp22 m11 m12 m21 m22 (-1) := by
  rw [abs_lt, ← lamLo_gt_neg_one_iff h1]
  exact ⟨fun h => h.1, fun h => ⟨h, (roots22_lt h1).1⟩⟩

/-- `p(m₁₁) = −m₁₂m₂₁`, so `m₁₂m₂₁ > 0` puts `m₁₁` strictly between the roots. -/
theorem lamLo_lt_m11 (h1 : cp22 m11 m12 m21 m22 1 < 0) (hm : 0 < m12 * m21) :
    lamLo m11 m12 m21 m22 < m11 ∧ m11 < lamHi m11 m12 m21 m22 := by
  have hf := cp22_factor h1 m11
  have hlt := lamLo_lt_lamHi h1
  have : cp22 m11 m12 m21 m22 m11 = -(m12 * m21) := by simp only [cp22]; ring
  rw [this] at hf
  constructor <;> nlinarith

/-- For a root `λ` of `p`, one step of the system multiplies `s` by `λ`. -/
theorem sVar_step {l : ℝ} (hl : cp22 m11 m12 m21 m22 l = 0) {X Y : ℕ → ℝ} {t : ℕ}
    (hX : X (t + 1) = m11 * X t + m12 * Y t) (hY : Y (t + 1) = m21 * X t + m22 * Y t) :
    sVar m11 m21 l X Y (t + 1) = l * sVar m11 m21 l X Y t := by
  simp only [sVar, cp22] at *
  rw [hX, hY]
  linear_combination (-Y t) * hl

/-- For a root `λ` and a solution, `s_t = λᵗ s₀`. -/
theorem sVar_succ {l : ℝ} (hl : cp22 m11 m12 m21 m22 l = 0) {X Y : ℕ → ℝ}
    (h : IsSol22 m11 m12 m21 m22 X Y) (t : ℕ) :
    sVar m11 m21 l X Y t = l ^ t * sVar m11 m21 l X Y 0 :=
  geom_eq (fun t => sVar_step hl (h t).1 (h t).2) t

/-- Recovering `(X, Y)` from the two `s` variables. -/
theorem recover22 {l1 l2 : ℝ} (hne : l1 ≠ l2) (hm21 : m21 ≠ 0) (X Y : ℕ → ℝ) (t : ℕ) :
    X t = ((l2 - m11) * sVar m11 m21 l1 X Y t - (l1 - m11) * sVar m11 m21 l2 X Y t) /
        (m21 * (l2 - l1)) ∧
      Y t = (sVar m11 m21 l2 X Y t - sVar m11 m21 l1 X Y t) / (l2 - l1) := by
  have hd : l2 - l1 ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  simp only [sVar]
  constructor <;> field_simp <;> ring

/-- Solutions with the same initial values coincide. -/
theorem IsSol22.ext {X Y X' Y' : ℕ → ℝ} (h : IsSol22 m11 m12 m21 m22 X Y)
    (h' : IsSol22 m11 m12 m21 m22 X' Y') (hX : X 0 = X' 0) (hY : Y 0 = Y' 0) :
    X = X' ∧ Y = Y' := by
  have key : ∀ t, X t = X' t ∧ Y t = Y' t := by
    intro t
    induction t with
    | zero => exact ⟨hX, hY⟩
    | succ n ih => exact ⟨by rw [(h n).1, (h' n).1, ih.1, ih.2],
        by rw [(h n).2, (h' n).2, ih.1, ih.2]⟩
  exact ⟨funext fun t => (key t).1, funext fun t => (key t).2⟩

theorem bddSeq_lin {X Y : ℕ → ℝ} (hX : BddSeq X) (hY : BddSeq Y) (p q : ℝ) :
    BddSeq (fun t => p * X t + q * Y t) := by
  obtain ⟨M, hM⟩ := hX
  obtain ⟨M', hM'⟩ := hY
  refine ⟨|p| * M + |q| * M', fun t => (abs_add_le _ _).trans (add_le_add ?_ ?_)⟩
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM t) (abs_nonneg _)
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM' t) (abs_nonneg _)

/-- A bounded solution has `s^hi₀ = 0` (the unstable component vanishes). -/
theorem sHi_zero_of_bdd (h1 : cp22 m11 m12 m21 m22 1 < 0) {X Y : ℕ → ℝ}
    (h : IsSol22 m11 m12 m21 m22 X Y) (hX : BddSeq X) (hY : BddSeq Y) :
    sVar m11 m21 (lamHi m11 m12 m21 m22) X Y 0 = 0 := by
  have hhi := (roots22_lt h1).2
  exact (geom_bdd_iff (by rw [abs_of_pos (by linarith)]; exact hhi)
    (fun t => sVar_step (cp22_lamHi h1) (h t).1 (h t).2)).1
    (bddSeq_lin hX hY m21 (lamHi m11 m12 m21 m22 - m11))

/-- The slope of the saddle path, `k = (λ_lo − m₁₁)/m₁₂`. -/
noncomputable def kSaddle (m11 m12 m21 m22 : ℝ) : ℝ :=
  (lamLo m11 m12 m21 m22 - m11) / m12

/-- `s^hi₀ = 0 ⟺ Y₀ = kX₀`: the saddle line. -/
theorem sHi_zero_iff (h1 : cp22 m11 m12 m21 m22 1 < 0) (hm : 0 < m12 * m21) (X Y : ℕ → ℝ)
    (t : ℕ) : sVar m11 m21 (lamHi m11 m12 m21 m22) X Y t = 0 ↔
      Y t = kSaddle m11 m12 m21 m22 * X t := by
  have hm12 : m12 ≠ 0 := by rintro h; simp [h] at hm
  have hb := lamLo_lt_m11 h1 hm
  have hhi : lamHi m11 m12 m21 m22 - m11 ≠ 0 := by linarith
  have hprod : (lamLo m11 m12 m21 m22 - m11) * (lamHi m11 m12 m21 m22 - m11) = -(m12 * m21) := by
    have := cp22_factor h1 m11
    simp only [cp22] at this
    linarith
  simp only [sVar, kSaddle]
  constructor
  · intro h
    rw [div_mul_eq_mul_div, eq_div_iff hm12]
    have : (lamHi m11 m12 m21 m22 - m11) * (Y t * m12) =
        (lamHi m11 m12 m21 m22 - m11) * ((lamLo m11 m12 m21 m22 - m11) * X t) := by
      linear_combination m12 * h - X t * hprod
    exact mul_left_cancel₀ hhi this
  · intro h
    rw [h]
    field_simp
    linear_combination X t * hprod

/-- The saddle path `X_t = λ_loᵗX₀`, `Y_t = λ_loᵗ k X₀` solves the system. -/
theorem saddle22 (h1 : cp22 m11 m12 m21 m22 1 < 0) (hm12 : m12 ≠ 0) (X0 : ℝ) :
    IsSol22 m11 m12 m21 m22 (fun t => lamLo m11 m12 m21 m22 ^ t * X0)
      (fun t => lamLo m11 m12 m21 m22 ^ t * (kSaddle m11 m12 m21 m22 * X0)) := by
  have hc := cp22_lamLo h1
  intro t
  simp only [kSaddle, cp22, pow_succ] at *
  constructor
  · field_simp; ring
  · field_simp
    linear_combination (lamLo m11 m12 m21 m22 ^ t * X0) * hc

/-- With `|λ_lo| < 1` the saddle path converges to `0`. -/
theorem saddle22_tendsto (h1 : cp22 m11 m12 m21 m22 1 < 0) (hc : 0 < cp22 m11 m12 m21 m22 (-1))
    (X0 : ℝ) : Tendsto (fun t => lamLo m11 m12 m21 m22 ^ t * X0) atTop (𝓝 0) ∧
      Tendsto (fun t => lamLo m11 m12 m21 m22 ^ t * (kSaddle m11 m12 m21 m22 * X0)) atTop
        (𝓝 0) := by
  have hl := (abs_lamLo_lt_one_iff h1).2 hc
  have h := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hl
  exact ⟨by simpa using h.mul_const X0, by simpa using h.mul_const _⟩

/-- A bounded solution lies on the saddle line, so it is the saddle path through its `X₀`. -/
theorem saddle22_unique (h1 : cp22 m11 m12 m21 m22 1 < 0) (hm : 0 < m12 * m21)
    {X Y : ℕ → ℝ} (h : IsSol22 m11 m12 m21 m22 X Y) (hX : BddSeq X) (hY : BddSeq Y) :
    X = (fun t => lamLo m11 m12 m21 m22 ^ t * X 0) ∧
      Y = (fun t => lamLo m11 m12 m21 m22 ^ t * (kSaddle m11 m12 m21 m22 * X 0)) := by
  have hm12 : m12 ≠ 0 := by rintro h; simp [h] at hm
  have hY0 := (sHi_zero_iff h1 hm X Y 0).1 (sHi_zero_of_bdd h1 h hX hY)
  exact h.ext (saddle22 h1 hm12 (X 0)) (by simp) (by simp [hY0])

/-- Off the saddle line every solution is unbounded. -/
theorem saddle22_unbounded (h1 : cp22 m11 m12 m21 m22 1 < 0) (hm : 0 < m12 * m21)
    {X Y : ℕ → ℝ} (h : IsSol22 m11 m12 m21 m22 X Y) (hoff : Y 0 ≠ kSaddle m11 m12 m21 m22 * X 0) :
    ¬ (BddSeq X ∧ BddSeq Y) := fun ⟨hX, hY⟩ =>
  hoff ((sHi_zero_iff h1 hm X Y 0).1 (sHi_zero_of_bdd h1 h hX hY))

/-- `s` of a solution converging to `0` converges to `0`. -/
theorem sVar_tendsto {X Y : ℕ → ℝ} (l : ℝ) (hX : Tendsto X atTop (𝓝 0))
    (hY : Tendsto Y atTop (𝓝 0)) : Tendsto (sVar m11 m21 l X Y) atTop (𝓝 0) := by
  have := (hX.const_mul m21).add (hY.const_mul (l - m11))
  simp only [mul_zero, add_zero] at this
  exact this

/-- Every `X₀` has a solution converging to the steady state iff `p(−1) > 0` (given `p(1) < 0`
and `m₁₂m₂₁ > 0`). -/
theorem saddle22_iff (h1 : cp22 m11 m12 m21 m22 1 < 0) (hm : 0 < m12 * m21) :
    (∀ X0, ∃ X Y : ℕ → ℝ, IsSol22 m11 m12 m21 m22 X Y ∧ X 0 = X0 ∧
      Tendsto X atTop (𝓝 0) ∧ Tendsto Y atTop (𝓝 0)) ↔ 0 < cp22 m11 m12 m21 m22 (-1) := by
  have hm12 : m12 ≠ 0 := by rintro h; simp [h] at hm
  have hm21 : m21 ≠ 0 := by rintro h; simp [h] at hm
  constructor
  · intro H
    obtain ⟨X, Y, h, hX0, hX, hY⟩ := H 1
    have hhi0 := sHi_zero_of_bdd h1 h (bddSeq_of_tendsto hX) (bddSeq_of_tendsto hY)
    have hlo0 : sVar m11 m21 (lamLo m11 m12 m21 m22) X Y 0 ≠ 0 := by
      intro h0
      have hlt := lamLo_lt_lamHi h1
      simp only [sVar] at h0 hhi0
      have hY0 : Y 0 = 0 := by
        have : (lamHi m11 m12 m21 m22 - lamLo m11 m12 m21 m22) * Y 0 = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left (by linarith)
      rw [hY0, hX0] at h0
      simp only [mul_one, mul_zero, add_zero] at h0
      exact hm21 h0
    have hs := sVar_tendsto (m11 := m11) (m21 := m21) (lamLo m11 m12 m21 m22) hX hY
    have : Tendsto (fun t => lamLo m11 m12 m21 m22 ^ t *
        sVar m11 m21 (lamLo m11 m12 m21 m22) X Y 0) atTop (𝓝 0) :=
      hs.congr (fun t => sVar_succ (cp22_lamLo h1) h t)
    exact (abs_lamLo_lt_one_iff h1).1 ((pow_mul_tendsto_zero_iff hlo0).1 this)
  · intro hc X0
    exact ⟨_, _, saddle22 h1 hm12 X0, by simp, saddle22_tendsto h1 hc X0⟩

/-- If `p(−1) < 0` both roots are unstable and the only bounded solution is `0`. -/
theorem saddle22_only_zero (h1 : cp22 m11 m12 m21 m22 1 < 0) (hm : 0 < m12 * m21)
    (hc : cp22 m11 m12 m21 m22 (-1) < 0) {X Y : ℕ → ℝ} (h : IsSol22 m11 m12 m21 m22 X Y)
    (hX : BddSeq X) (hY : BddSeq Y) : X = 0 ∧ Y = 0 := by
  have hm21 : m21 ≠ 0 := by rintro h; simp [h] at hm
  have hlo : lamLo m11 m12 m21 m22 < -1 := by
    rcases lt_trichotomy (lamLo m11 m12 m21 m22) (-1) with h' | h' | h'
    · exact h'
    · have := cp22_factor h1 (-1)
      rw [h'] at this
      simp at this
      linarith
    · linarith [(lamLo_gt_neg_one_iff h1).1 h']
  have hlo0 : sVar m11 m21 (lamLo m11 m12 m21 m22) X Y 0 = 0 :=
    (geom_bdd_iff (by rw [abs_of_neg (by linarith)]; linarith)
      (fun t => sVar_step (cp22_lamLo h1) (h t).1 (h t).2)).1
      (bddSeq_lin hX hY m21 (lamLo m11 m12 m21 m22 - m11))
  have hhi0 := sHi_zero_of_bdd h1 h hX hY
  have hne := (lamLo_lt_lamHi h1).ne
  have hr := recover22 (m11 := m11) hne hm21 X Y 0
  rw [hlo0, hhi0] at hr
  simp only [mul_zero, zero_div, sub_self] at hr
  exact (h.ext (X' := fun _ => 0) (Y' := fun _ => 0) (fun t => by simp) hr.1 hr.2)

/-! ### The book's phase diagram -/

/-- The system of Miao, p. 27, in terms of `a = ã − 1` and `d = d̃ + 1`:
`x_{t+1} = (1 + a)x_t + b y_t − e`, `y_{t+1} = c x_t + (1 − d)y_t + f`. -/
def IsPhaseSol (a b c d e f : ℝ) (x y : ℕ → ℝ) : Prop :=
  ∀ t, x (t + 1) = (1 + a) * x t + b * y t - e ∧ y (t + 1) = c * x t + (1 - d) * y t + f

/-- Forward iteration of the system from `(x₀, y₀)`. -/
def phaseIter (a b c d e f x0 y0 : ℝ) : ℕ → ℝ × ℝ
  | 0 => (x0, y0)
  | t + 1 => ((1 + a) * (phaseIter a b c d e f x0 y0 t).1 + b * (phaseIter a b c d e f x0 y0 t).2
      - e, c * (phaseIter a b c d e f x0 y0 t).1 + (1 - d) * (phaseIter a b c d e f x0 y0 t).2 + f)

theorem phaseIter_sol {a b c d e f x0 y0 : ℝ} :
    IsPhaseSol a b c d e f (fun t => (phaseIter a b c d e f x0 y0 t).1)
      (fun t => (phaseIter a b c d e f x0 y0 t).2) := fun _ => ⟨rfl, rfl⟩

/-- Miao, p. 27: the system `x_{t+1} = ãx_t + by_t − e`, `y_{t+1} = cx_t − d̃y_t + f` is
`IsPhaseSol` with `a = ã − 1`, `d = d̃ + 1`. -/
theorem phase_tilde (at' b c dt e f : ℝ) (x y : ℕ → ℝ) :
    (∀ t, x (t + 1) = at' * x t + b * y t - e ∧ y (t + 1) = c * x t - dt * y t + f) ↔
      IsPhaseSol (at' - 1) b c (dt + 1) e f x y := by
  simp only [IsPhaseSol]
  constructor <;> intro h t <;> constructor <;> linarith [(h t).1, (h t).2]

/-- Miao, p. 27: `Δx_t = ax_t + by_t − e` and `Δy_t = cx_t − dy_t + f`. -/
theorem phase_delta {a b c d e f : ℝ} {x y : ℕ → ℝ} (h : IsPhaseSol a b c d e f x y) (t : ℕ) :
    x (t + 1) - x t = a * x t + b * y t - e ∧ y (t + 1) - y t = c * x t - d * y t + f := by
  rw [(h t).1, (h t).2]
  constructor <;> ring

/-- Miao, p. 28: for `b > 0`, `Δx ≥ 0 ⟺ y ≥ −(a/b)x + e/b` (and strictly). -/
theorem phase_isocline_x {a b e : ℝ} (hb : 0 < b) (x y : ℝ) :
    (0 ≤ a * x + b * y - e ↔ -(a / b) * x + e / b ≤ y) ∧
      (0 < a * x + b * y - e ↔ -(a / b) * x + e / b < y) := by
  have : -(a / b) * x + e / b = (e - a * x) / b := by field_simp; ring
  rw [this, div_le_iff₀ hb, div_lt_iff₀ hb]
  constructor <;> constructor <;> intro h <;> linarith

/-- Miao, p. 28: for `d > 0`, `Δy ≥ 0 ⟺ y ≤ (c/d)x + f/d` (and strictly). -/
theorem phase_isocline_y {c d f : ℝ} (hd : 0 < d) (x y : ℝ) :
    (0 ≤ c * x - d * y + f ↔ y ≤ c / d * x + f / d) ∧
      (0 < c * x - d * y + f ↔ y < c / d * x + f / d) := by
  have : c / d * x + f / d = (c * x + f) / d := by field_simp
  rw [this, le_div_iff₀ hd, lt_div_iff₀ hd]
  constructor <;> constructor <;> intro h <;> linarith

/-- Miao, p. 28: for `a, b, c, d > 0` the steady state is unique:
`x̄ = (ed − bf)/(ad + bc)`, `ȳ = (af + ce)/(ad + bc)`. -/
theorem phase_steady_state {a b c d e f : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (xb yb : ℝ) :
    IsPhaseSol a b c d e f (fun _ => xb) (fun _ => yb) ↔
      xb = (e * d - b * f) / (a * d + b * c) ∧ yb = (a * f + c * e) / (a * d + b * c) := by
  have hD : 0 < a * d + b * c := by positivity
  simp only [IsPhaseSol]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h 0
    constructor <;> rw [eq_div_iff hD.ne'] <;> nlinarith
  · rintro ⟨rfl, rfl⟩ _
    constructor <;> field_simp <;> ring

theorem bddSeq_sub_const {x : ℕ → ℝ} (hx : BddSeq x) (k : ℝ) : BddSeq (fun t => x t - k) := by
  obtain ⟨M, hM⟩ := hx
  exact ⟨M + |k|, fun t => (abs_sub _ _).trans (add_le_add (hM t) le_rfl)⟩

/-- Deviations from a steady state `(x̄, ȳ)` solve the homogeneous system with matrix
`[[1 + a, b], [c, 1 − d]]`. -/
theorem phase_dev {a b c d e f xb yb : ℝ} {x y : ℕ → ℝ}
    (hss : IsPhaseSol a b c d e f (fun _ => xb) (fun _ => yb)) (h : IsPhaseSol a b c d e f x y) :
    IsSol22 (1 + a) b c (1 - d) (fun t => x t - xb) (fun t => y t - yb) := by
  intro t
  obtain ⟨h1, h2⟩ := h t
  obtain ⟨s1, s2⟩ := hss 0
  constructor
  · simp only; rw [h1]; linear_combination (-1 : ℝ) * s1
  · simp only; rw [h2]; linear_combination (-1 : ℝ) * s2

theorem phase_cp_one {a b c d : ℝ} : cp22 (1 + a) b c (1 - d) 1 = -(a * d) - b * c := by
  simp only [cp22]; ring

theorem phase_cp_neg_one {a b c d : ℝ} :
    cp22 (1 + a) b c (1 - d) (-1) = (2 + a) * (2 - d) - b * c := by
  simp only [cp22]; ring

/-- Miao, p. 28: the coefficient matrix `[[1 + a, b], [c, 1 − d]]` has two real roots, one
below and one above `1`. -/
theorem phase_roots {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    cp22 (1 + a) b c (1 - d) 1 < 0 ∧ lamLo (1 + a) b c (1 - d) < 1 ∧
      1 < lamHi (1 + a) b c (1 - d) := by
  have h1 : cp22 (1 + a) b c (1 - d) 1 < 0 := by rw [phase_cp_one]; nlinarith [mul_pos ha hd]
  exact ⟨h1, roots22_lt h1⟩

/-- **Correction** (Miao, p. 28): the smaller root lies in `(−1, 1)` iff
`(2 + a)(2 − d) > bc`. -/
theorem phase_lamLo_iff {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    |lamLo (1 + a) b c (1 - d)| < 1 ↔ b * c < (2 + a) * (2 - d) := by
  rw [abs_lamLo_lt_one_iff (phase_roots ha hb hc hd).1, phase_cp_neg_one, sub_pos]

/-- **Saddle path** (Miao, p. 28, corrected): if `(2 + a)(2 − d) > bc`, for every `x₀` the path
starting at `y₀ = ȳ + k(x₀ − x̄)`, `k = (λ_lo − 1 − a)/b`, converges to the steady state; every
bounded path is of this form; every other path is unbounded. -/
theorem phase_saddle {a b c d e f : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hcond : b * c < (2 + a) * (2 - d)) (x0 : ℝ) :
    (∃ x y : ℕ → ℝ, IsPhaseSol a b c d e f x y ∧ x 0 = x0 ∧
      Tendsto x atTop (𝓝 ((e * d - b * f) / (a * d + b * c))) ∧
      Tendsto y atTop (𝓝 ((a * f + c * e) / (a * d + b * c)))) ∧
    ∀ x y : ℕ → ℝ, IsPhaseSol a b c d e f x y →
      ((BddSeq x ∧ BddSeq y) ↔ y 0 - (a * f + c * e) / (a * d + b * c) =
        kSaddle (1 + a) b c (1 - d) * (x 0 - (e * d - b * f) / (a * d + b * c))) := by
  set xb := (e * d - b * f) / (a * d + b * c)
  set yb := (a * f + c * e) / (a * d + b * c)
  have h1 := (phase_roots ha hb hc hd).1
  have hm : 0 < b * c := mul_pos hb hc
  have hc1 : 0 < cp22 (1 + a) b c (1 - d) (-1) := by rw [phase_cp_neg_one]; linarith
  have hss : IsPhaseSol a b c d e f (fun _ => xb) (fun _ => yb) :=
    (phase_steady_state ha hb hc hd _ _).2 ⟨rfl, rfl⟩
  have hdevB : ∀ x y : ℕ → ℝ, IsPhaseSol a b c d e f x y →
      y 0 - yb = kSaddle (1 + a) b c (1 - d) * (x 0 - xb) →
      Tendsto x atTop (𝓝 xb) ∧ Tendsto y atTop (𝓝 yb) := by
    intro x y h hk
    have hdev := phase_dev hss h
    obtain ⟨hX, hY⟩ := hdev.ext (saddle22 h1 hb.ne' (x 0 - xb)) (by simp) (by simpa using hk)
    obtain ⟨t1, t2⟩ := saddle22_tendsto h1 hc1 (x 0 - xb)
    rw [← hX] at t1
    rw [← hY] at t2
    exact ⟨by simpa using t1.add_const xb, by simpa using t2.add_const yb⟩
  refine ⟨?_, fun x y h => ⟨fun ⟨hx, hy⟩ => ?_, fun hk => ?_⟩⟩
  · obtain ⟨x, y, hxy⟩ : ∃ x y : ℕ → ℝ, IsPhaseSol a b c d e f x y ∧ x 0 = x0 ∧
        y 0 = yb + kSaddle (1 + a) b c (1 - d) * (x0 - xb) :=
      ⟨fun t => (phaseIter a b c d e f x0 (yb + kSaddle (1 + a) b c (1 - d) * (x0 - xb)) t).1,
        fun t => (phaseIter a b c d e f x0 (yb + kSaddle (1 + a) b c (1 - d) * (x0 - xb)) t).2,
        phaseIter_sol, rfl, rfl⟩
    obtain ⟨h, hx0, hy0⟩ := hxy
    refine ⟨x, y, h, hx0, hdevB x y h (by rw [hy0, hx0]; ring)⟩
  · have h0 := sHi_zero_of_bdd h1 (phase_dev hss h) (bddSeq_sub_const hx xb)
      (bddSeq_sub_const hy yb)
    exact (sHi_zero_iff h1 hm _ _ 0).1 h0
  · obtain ⟨t1, t2⟩ := hdevB x y h hk
    exact ⟨bddSeq_of_tendsto t1, bddSeq_of_tendsto t2⟩

/-- Miao, p. 28 (Figure 1.4): the saddle path `y − ȳ = k(x − x̄)` slopes down, more steeply
than the isocline `Δx = 0` (slope `−a/b`): `k < −a/b < 0`. -/
theorem phase_saddle_slope {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    kSaddle (1 + a) b c (1 - d) < -(a / b) ∧ -(a / b) < 0 := by
  have hlo := (phase_roots ha hb hc hd).2.1
  simp only [kSaddle]
  refine ⟨?_, by have := div_pos ha hb; linarith⟩
  rw [div_lt_iff₀ hb]
  have : -(a / b) * b = -a := by field_simp
  linarith

/-- **Correction** (Miao, p. 28): every `x₀` has a path converging to the steady state iff
`(2 + a)(2 − d) > bc`. -/
theorem phase_saddle_iff {a b c d e f : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) :
    (∀ x0, ∃ x y : ℕ → ℝ, IsPhaseSol a b c d e f x y ∧ x 0 = x0 ∧
      Tendsto x atTop (𝓝 ((e * d - b * f) / (a * d + b * c))) ∧
      Tendsto y atTop (𝓝 ((a * f + c * e) / (a * d + b * c)))) ↔
      b * c < (2 + a) * (2 - d) := by
  constructor
  · intro H
    have h1 := (phase_roots ha hb hc hd).1
    have hss : IsPhaseSol a b c d e f (fun _ => (e * d - b * f) / (a * d + b * c))
        (fun _ => (a * f + c * e) / (a * d + b * c)) :=
      (phase_steady_state ha hb hc hd _ _).2 ⟨rfl, rfl⟩
    have := (saddle22_iff h1 (mul_pos hb hc)).1 (fun X0 => by
      obtain ⟨x, y, h, hx0, hx, hy⟩ := H (X0 + (e * d - b * f) / (a * d + b * c))
      exact ⟨_, _, phase_dev hss h, by simp [hx0],
        by simpa using hx.sub_const ((e * d - b * f) / (a * d + b * c)),
        by simpa using hy.sub_const ((a * f + c * e) / (a * d + b * c))⟩)
    rwa [phase_cp_neg_one, sub_pos] at this
  · intro hcond x0
    exact (phase_saddle (e := e) (f := f) ha hb hc hd hcond x0).1

/-- **Counterexample** (Miao, p. 28): for `a = b = c = e = f = 1`, `d = 3` one has
`(2 + a)(2 − d) = −3 < 1 = bc`; both roots are unstable (`λ_lo < −1`, `λ_hi > 1`), and the
steady state `(1/2, 1/2)` is the only bounded path: no convergent saddle path exists. -/
theorem phase_counterexample :
    lamLo (1 + 1) 1 1 (1 - 3) < -1 ∧ 1 < lamHi (1 + 1) 1 1 (1 - 3) ∧
      ∀ x y : ℕ → ℝ, IsPhaseSol 1 1 1 3 1 1 x y → BddSeq x → BddSeq y →
        x = (fun _ => 1 / 2) ∧ y = (fun _ => 1 / 2) := by
  have h1 : cp22 (1 + 1) 1 1 (1 - 3) 1 < 0 := by rw [phase_cp_one]; norm_num
  have hc : cp22 (1 + 1) 1 1 (1 - 3) (-1) < 0 := by rw [phase_cp_neg_one]; norm_num
  refine ⟨?_, (roots22_lt h1).2, fun x y h hx hy => ?_⟩
  · by_contra hlo
    push Not at hlo
    rcases hlo.lt_or_eq with hlt | heq
    · linarith [(lamLo_gt_neg_one_iff h1).1 hlt]
    · have := cp22_factor h1 (-1)
      rw [← heq] at this
      simp at this
      linarith
  · have hss : IsPhaseSol 1 1 1 3 1 1 (fun _ => 1 / 2) (fun _ => 1 / 2) := by
      intro t; constructor <;> norm_num
    obtain ⟨hX, hY⟩ := saddle22_only_zero h1 (by norm_num) hc (phase_dev hss h)
      (bddSeq_sub_const hx _) (bddSeq_sub_const hy _)
    constructor
    · ext t; have := congrFun hX t; simp only [Pi.zero_apply] at this; linarith
    · ext t; have := congrFun hY t; simp only [Pi.zero_apply] at this; linarith

end Miao.DifferenceEquations
