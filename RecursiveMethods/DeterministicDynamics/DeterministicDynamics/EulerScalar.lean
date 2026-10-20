/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib

/-!
# One state variable: the roots of the linearized Euler equation

SLP §6.4, pp. 154–156. With one state variable the stacked matrix is
`A = [[J, K], [1, 0]]` with `J = −(F_yy + βF_xx)/(βF_xy)` and `K = −1/β`. Its characteristic
polynomial is `λ² − Jλ + 1/β`.

* **The growth example** (pp. 154–155, `growth_roots`). For `U[f(k) − y]`,
  `J = 1 + β⁻¹ + c` with `c = βf''U'/U'' > 0`. The polynomial `λ² − (1 + β⁻¹ + c)λ + β⁻¹` has one
  root in `(0, 1)` and one above `1/β` (Figure 6.3).
* **Exercise 6.6** (`ex_6_6`). With the second-order conditions of a concave `F` at the steady
  state (`F_xx ≤ 0`, `F_yy ≤ 0`, `F_xxF_yy ≥ F_xy²`, `F_xy ≠ 0`):
  (a) both roots of `A` are real;
  (b) both are positive if `F_xy > 0`;
  (c) both are negative if `F_xy < 0`.
  The product of the roots is `1/β > 0`, and their sum `J` has the sign of `F_xy`.

Roots are stated as the complex roots of the polynomial (`quadRoot`), so "real" is a conclusion.
-/

namespace StokeyLucasPrescott.DeterministicDynamics

open Complex

/-- `μ` is a root of `λ² − sλ + p`. -/
def quadRoot (s p : ℝ) (μ : ℂ) : Prop := μ ^ 2 - (s : ℂ) * μ + (p : ℂ) = 0

/-- If `s² ≥ 4p`, the roots of `λ² − sλ + p` are `(s ± √(s² − 4p))/2`, and they are real. -/
theorem quadRoot_real {s p : ℝ} (hd : 4 * p ≤ s ^ 2) {μ : ℂ} (hμ : quadRoot s p μ) :
    ∃ r : ℝ, μ = r ∧ (r = (s + Real.sqrt (s ^ 2 - 4 * p)) / 2 ∨
      r = (s - Real.sqrt (s ^ 2 - 4 * p)) / 2) := by
  set q := Real.sqrt (s ^ 2 - 4 * p)
  have hq : q ^ 2 = s ^ 2 - 4 * p := Real.sq_sqrt (by linarith)
  have hfac : (μ - ((s + q) / 2 : ℝ)) * (μ - ((s - q) / 2 : ℝ)) = 0 := by
    have e : (μ - ((s + q) / 2 : ℝ)) * (μ - ((s - q) / 2 : ℝ)) =
        μ ^ 2 - (s : ℂ) * μ + ((s ^ 2 - q ^ 2) / 4 : ℝ) := by push_cast; ring
    have e2 : ((s ^ 2 - q ^ 2) / 4 : ℝ) = p := by rw [hq]; ring
    rw [e, e2]
    exact hμ
  rcases mul_eq_zero.1 hfac with h | h
  · exact ⟨_, sub_eq_zero.1 h, Or.inl rfl⟩
  · exact ⟨_, sub_eq_zero.1 h, Or.inr rfl⟩

/-- **The growth example** (pp. 154–155). For `c > 0` and `0 < β < 1`, the roots of
`λ² − (1 + β⁻¹ + c)λ + β⁻¹` are real, one in `(0, 1)` and one greater than `1/β`. -/
theorem growth_roots {β c : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hc : 0 < c) :
    ∃ l₁ l₂ : ℝ, 0 < l₁ ∧ l₁ < 1 ∧ 1 / β < l₂ ∧ quadRoot (1 + β⁻¹ + c) β⁻¹ l₁ ∧
      quadRoot (1 + β⁻¹ + c) β⁻¹ l₂ ∧ ∀ μ, quadRoot (1 + β⁻¹ + c) β⁻¹ μ → μ = l₁ ∨ μ = l₂ := by
  set s := 1 + β⁻¹ + c
  have hbi : 1 < β⁻¹ := (one_lt_inv₀ hβ0).2 hβ1
  -- `p(1) = −c < 0` and `p(1/β) = −c/β < 0` while `p(0) = 1/β > 0`
  have hd : 4 * β⁻¹ ≤ s ^ 2 := by
    simp only [s]; nlinarith [sq_nonneg (1 - β⁻¹)]
  set q := Real.sqrt (s ^ 2 - 4 * β⁻¹)
  have hq : q ^ 2 = s ^ 2 - 4 * β⁻¹ := Real.sq_sqrt (by linarith)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqc : (q : ℂ) ^ 2 = (s : ℂ) ^ 2 - 4 * (β : ℂ)⁻¹ := by
    have := congrArg (fun x : ℝ => (x : ℂ)) hq
    push_cast at this
    exact this
  have hroot : ∀ r : ℝ, r = (s + q) / 2 ∨ r = (s - q) / 2 → quadRoot s β⁻¹ r := by
    rintro r (rfl | rfl) <;> simp only [quadRoot] <;> push_cast <;>
      linear_combination (1 / 4 : ℂ) * hqc
  -- locate the roots through the sign of `p`
  have hp1 : (1 : ℝ) ^ 2 - s * 1 + β⁻¹ < 0 := by simp only [s]; linarith
  have hpβ : β⁻¹ ^ 2 - s * β⁻¹ + β⁻¹ < 0 := by simp only [s]; nlinarith
  -- `p(r) = (r − r₁)(r − r₂)` with `r₁ ≤ r₂`
  have hfact : ∀ r : ℝ, r ^ 2 - s * r + β⁻¹ = (r - (s - q) / 2) * (r - (s + q) / 2) := fun r => by
    have : s ^ 2 - q ^ 2 = 4 * β⁻¹ := by linarith
    nlinarith
  have h1 := hfact 1
  have h2 := hfact β⁻¹
  have hlt1 : (s - q) / 2 < 1 ∧ 1 < (s + q) / 2 := by
    rw [h1] at hp1
    constructor <;> nlinarith
  have hlt2 : β⁻¹ < (s + q) / 2 := by
    rw [h2] at hpβ
    nlinarith
  have hpos : 0 < (s - q) / 2 := by
    have : q < s := by
      have hs : 0 < s := by simp only [s]; linarith
      nlinarith
    linarith
  refine ⟨(s - q) / 2, (s + q) / 2, hpos, hlt1.1, by rw [one_div]; exact hlt2,
    hroot _ (Or.inr rfl), hroot _ (Or.inl rfl), fun μ hμ => ?_⟩
  obtain ⟨r, rfl, hr⟩ := quadRoot_real hd hμ
  rcases hr with rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- **Exercise 6.6.** With `F_xx ≤ 0`, `F_yy ≤ 0`, `F_xxF_yy ≥ F_xy²`, `F_xy ≠ 0` and `β > 0`, the
roots of `λ² − Jλ + 1/β`, `J = −(F_yy + βF_xx)/(βF_xy)`, are real, with product `1/β`, and both
have the sign of `F_xy`. -/
theorem ex_6_6 {Fxx Fxy Fyy β : ℝ} (hβ : 0 < β) (hxx : Fxx ≤ 0) (hyy : Fyy ≤ 0)
    (hdet : Fxy ^ 2 ≤ Fxx * Fyy) (hxy : Fxy ≠ 0) :
    ∃ l₁ l₂ : ℝ, l₁ * l₂ = 1 / β ∧
      quadRoot (-(Fyy + β * Fxx) / (β * Fxy)) (1 / β) l₁ ∧
      quadRoot (-(Fyy + β * Fxx) / (β * Fxy)) (1 / β) l₂ ∧
      (∀ μ, quadRoot (-(Fyy + β * Fxx) / (β * Fxy)) (1 / β) μ → μ = l₁ ∨ μ = l₂) ∧
      (0 < Fxy → 0 < l₁ ∧ 0 < l₂) ∧ (Fxy < 0 → l₁ < 0 ∧ l₂ < 0) := by
  set s := -(Fyy + β * Fxx) / (β * Fxy)
  have hsq : 0 < Fxy ^ 2 := by positivity
  have hxx' : Fxx < 0 := lt_of_le_of_ne hxx fun h => by rw [h, zero_mul] at hdet; linarith
  have hyy' : Fyy < 0 := lt_of_le_of_ne hyy fun h => by rw [h, mul_zero] at hdet; linarith
  have hS : Fyy + β * Fxx < 0 := by nlinarith
  -- the discriminant: `(F_yy + βF_xx)² ≥ 4βF_xxF_yy ≥ 4βF_xy²`
  have hd : 4 * (1 / β) ≤ s ^ 2 := by
    have h1 : 4 * β * Fxy ^ 2 ≤ (Fyy + β * Fxx) ^ 2 := by
      nlinarith [sq_nonneg (Fyy - β * Fxx)]
    have hb : 0 < (β * Fxy) ^ 2 := by positivity
    simp only [s, div_pow, neg_sq]
    rw [le_div_iff₀ hb]
    field_simp
    nlinarith
  set q := Real.sqrt (s ^ 2 - 4 * (1 / β))
  have hq : q ^ 2 = s ^ 2 - 4 * (1 / β) := Real.sq_sqrt (by linarith)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqc : (q : ℂ) ^ 2 = (s : ℂ) ^ 2 - 4 * (1 / (β : ℂ)) := by
    have := congrArg (fun x : ℝ => (x : ℂ)) hq
    push_cast at this
    exact this
  have hroot : ∀ r : ℝ, r = (s + q) / 2 ∨ r = (s - q) / 2 → quadRoot s (1 / β) r := by
    rintro r (rfl | rfl) <;> simp only [quadRoot] <;> push_cast <;>
      linear_combination (1 / 4 : ℂ) * hqc
  have hprod : (s + q) / 2 * ((s - q) / 2) = 1 / β := by nlinarith
  have hqs : q < |s| := by
    have h1 : 0 < 1 / β := by positivity
    have h2 : q ^ 2 < |s| ^ 2 := by rw [sq_abs, hq]; linarith
    exact lt_of_pow_lt_pow_left₀ 2 (abs_nonneg s) h2
  refine ⟨(s + q) / 2, (s - q) / 2, hprod, hroot _ (Or.inl rfl), hroot _ (Or.inr rfl),
    fun μ hμ => ?_, fun hpos => ?_, fun hneg => ?_⟩
  · obtain ⟨r, rfl, hr⟩ := quadRoot_real hd hμ
    rcases hr with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · have hs : 0 < s := by
      simp only [s]; exact div_pos (by linarith) (by positivity)
    rw [abs_of_pos hs] at hqs
    constructor <;> linarith
  · have hs : s < 0 := by
      simp only [s]; exact div_neg_of_pos_of_neg (by linarith) (by nlinarith)
    rw [abs_of_neg hs] at hqs
    constructor <;> linarith

end StokeyLucasPrescott.DeterministicDynamics
