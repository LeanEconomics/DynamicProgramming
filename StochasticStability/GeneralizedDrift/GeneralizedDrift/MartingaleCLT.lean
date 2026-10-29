/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.AtomCLT
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# A central limit theorem for martingale differences (used in MT §17.4–17.5)

Copied for Chapter 19 from the Chapter 17 project
(`LimitTheorems/MartingaleCLT.lean`), with the namespace changed to
`MeynTweedie.GeneralizedDrift` and the imports to `GeneralizedDrift.*`.

Mathlib has the CLT for i.i.d. sequences only. The CLT criteria of §17.5 (Theorem 17.5.3) rest
on a CLT for the martingale `Mₙ(g)` of (17.43). This module proves a martingale-difference CLT by
McLeish's method (*Ann. Probab.* 2 (1974)), in a form without complex logarithms.

**Setting.** `Dₖ` is `𝓕ₖ₊₁`-measurable, square integrable, with `E[Dₖ | 𝓕ₖ] = 0`; the normalised
squares satisfy `(1/n) Σ_{k<n} Dₖ² → σ²` almost surely and `Σ_{k<n} E[Dₖ²] ≤ C n`.

**Tools.**
* `norm_prod_sub_prod_le_sum`: `‖Π aₖ − Π bₖ‖ ≤ Σ ‖aₖ − bₖ‖` for `‖aₖ‖, ‖bₖ‖ ≤ 1`.
* `norm_cexp_div_sub_le`: `‖e^{iy}/(1 + iy) − e^{−y²/2}‖ ≤ 2|y|³` for every real `y`.
* `prod_one_add_le`: `Π (1 + yₖ) ≤ e^{C} (1 + Σ yₖ)` when each `yₖ > 0` has `Σ_{j<k} yⱼ ≤ C`.
* `integral_mul_eq_zero_of_condExp`: `E[F G] = 0` for `𝓕`-measurable `F` and `E[G | 𝓕] = 0`.

**Result.** `martingale_clt`: `n^{−1/2} Σ_{k<n} Dₖ ⇒ N(0, σ²)`.

The proof truncates `Dₖ/√n` once `Σ_{j<k} Dⱼ²/n` exceeds `σ² + 1`, writes `e^{itS'ₙ} = Tₙ Uₙ` with
`Tₙ = Π (1 + itX'ₖ)` and `Uₙ = Π e^{itX'ₖ}/(1 + itX'ₖ)`, and uses `E[Tₙ] = 1` (the martingale
property), `sup_n E|Tₙ|² < ∞` (the truncation), `|Uₙ| ≤ 1` and `Uₙ → e^{−t²σ²/2}` a.s.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {Ω₀ : Type*} [mΩ₀ : MeasurableSpace Ω₀]

/-! ### Elementary inequalities -/

/-- `‖Π_{k<n} aₖ − Π_{k<n} bₖ‖ ≤ Σ_{k<n} ‖aₖ − bₖ‖` when all `‖aₖ‖, ‖bₖ‖ ≤ 1`. -/
theorem norm_prod_sub_prod_le_sum (a b : ℕ → ℂ) (ha : ∀ k, ‖a k‖ ≤ 1) (hb : ∀ k, ‖b k‖ ≤ 1)
    (n : ℕ) :
    ‖∏ k ∈ Finset.range n, a k - ∏ k ∈ Finset.range n, b k‖ ≤
      ∑ k ∈ Finset.range n, ‖a k - b k‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.sum_range_succ]
    have hA : ‖∏ k ∈ Finset.range n, a k‖ ≤ 1 := by
      rw [norm_prod]; exact Finset.prod_le_one₀ (fun k _ => norm_nonneg _) fun k _ => ha k
    have e : (∏ k ∈ Finset.range n, a k) * a n - (∏ k ∈ Finset.range n, b k) * b n =
        (∏ k ∈ Finset.range n, a k) * (a n - b n) +
          (∏ k ∈ Finset.range n, a k - ∏ k ∈ Finset.range n, b k) * b n := by ring
    rw [e]
    calc ‖(∏ k ∈ Finset.range n, a k) * (a n - b n) +
          (∏ k ∈ Finset.range n, a k - ∏ k ∈ Finset.range n, b k) * b n‖
        ≤ ‖(∏ k ∈ Finset.range n, a k) * (a n - b n)‖ +
          ‖(∏ k ∈ Finset.range n, a k - ∏ k ∈ Finset.range n, b k) * b n‖ := norm_add_le _ _
      _ ≤ 1 * ‖a n - b n‖ + (∑ k ∈ Finset.range n, ‖a k - b k‖) * 1 := by
          rw [norm_mul, norm_mul]
          gcongr
          · exact hb n
      _ = _ := by ring

/-- `‖1 + y i‖² = 1 + y²`. -/
theorem norm_one_add_mul_I_sq (y : ℝ) : ‖(1 : ℂ) + y * Complex.I‖ ^ 2 = 1 + y ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp; ring

/-- `‖1 + y i‖ ≥ 1`. -/
theorem one_le_norm_one_add_mul_I (y : ℝ) : 1 ≤ ‖(1 : ℂ) + y * Complex.I‖ := by
  have h := norm_one_add_mul_I_sq y
  have h0 : 0 ≤ ‖(1 : ℂ) + y * Complex.I‖ := norm_nonneg _
  nlinarith [sq_nonneg y]

/-- `‖e^{iy}‖ = 1`. -/
theorem norm_cexp_mul_I (y : ℝ) : ‖Complex.exp (y * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I y

/-- `‖e^{iy}/(1 + iy)‖ ≤ 1`. -/
theorem norm_cexp_div_le_one (y : ℝ) :
    ‖Complex.exp (y * Complex.I) / (1 + y * Complex.I)‖ ≤ 1 := by
  rw [norm_div, norm_cexp_mul_I]
  exact div_le_one_of_le₀ (one_le_norm_one_add_mul_I y) (norm_nonneg _)

/-- `‖e^{−u}‖ ≤ 1` for `u ≥ 0`, as a complex number. -/
theorem norm_cexp_neg_le_one {u : ℝ} (hu : 0 ≤ u) : ‖(Real.exp (-u) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.2 (by linarith)

/-- **The key estimate**: `‖e^{iy}/(1 + iy) − e^{−y²/2}‖ ≤ 2|y|³` for every real `y`. -/
theorem norm_cexp_div_sub_le (y : ℝ) :
    ‖Complex.exp (y * Complex.I) / (1 + y * Complex.I) - (Real.exp (-(y ^ 2 / 2)) : ℂ)‖ ≤
      2 * |y| ^ 3 := by
  by_cases hy : 1 ≤ |y|
  · calc ‖Complex.exp (y * Complex.I) / (1 + y * Complex.I) - (Real.exp (-(y ^ 2 / 2)) : ℂ)‖
        ≤ ‖Complex.exp (y * Complex.I) / (1 + y * Complex.I)‖ +
          ‖(Real.exp (-(y ^ 2 / 2)) : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (norm_cexp_div_le_one y) (norm_cexp_neg_le_one (by positivity))
      _ ≤ 2 * |y| ^ 3 := by nlinarith [one_le_pow₀ (n := 3) hy]
  · push Not at hy
    have hy1 : |y| ≤ 1 := hy.le
    have hne : (1 : ℂ) + y * Complex.I ≠ 0 := by
      intro h
      have := one_le_norm_one_add_mul_I y
      rw [h, norm_zero] at this
      linarith
    -- Taylor for `e^{iy}`
    have hx : ‖(y : ℂ) * Complex.I‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]; exact hy1
    have hR1 := Complex.exp_bound hx (n := 3) (by norm_num)
    have hsum : ∑ m ∈ Finset.range 3, ((y : ℂ) * Complex.I) ^ m / (m.factorial : ℂ) =
        1 + y * Complex.I - (y ^ 2 / 2 : ℝ) := by
      simp [Finset.sum_range_succ, Nat.factorial]
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [hsum] at hR1
    have hnx : ‖(y : ℂ) * Complex.I‖ = |y| := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [hnx] at hR1
    -- Taylor for `e^{−y²/2}`
    have hu : |-(y ^ 2 / 2)| ≤ 1 := by
      rw [abs_neg, abs_of_nonneg (by positivity)]
      nlinarith [abs_nonneg y, sq_abs y]
    have hR2 := Real.abs_exp_sub_one_sub_id_le hu
    set R2 := Real.exp (-(y ^ 2 / 2)) - 1 - -(y ^ 2 / 2) with hR2def
    have hR2' : |R2| ≤ |y| ^ 3 / 4 := by
      calc |R2| ≤ (-(y ^ 2 / 2)) ^ 2 := hR2
        _ = |y| ^ 4 / 4 := by rw [← sq_abs y]; ring
        _ ≤ |y| ^ 3 / 4 := by
            have : |y| ^ 4 ≤ |y| ^ 3 := by
              rw [pow_succ]; exact mul_le_of_le_one_right (by positivity) hy1
            linarith
    set R1 := Complex.exp (y * Complex.I) - (1 + y * Complex.I - (y ^ 2 / 2 : ℝ)) with hR1def
    have hdiff : Complex.exp (y * Complex.I) - (1 + y * Complex.I) * (Real.exp (-(y ^ 2 / 2)) : ℂ)
        = R1 + (y ^ 3 / 2 : ℝ) * Complex.I - (1 + y * Complex.I) * (R2 : ℂ) := by
      rw [hR1def, hR2def]
      push_cast
      ring_nf
    have hnorm1 : ‖(1 : ℂ) + y * Complex.I‖ ≤ 2 := by
      calc ‖(1 : ℂ) + y * Complex.I‖ ≤ ‖(1 : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ := norm_add_le _ _
        _ ≤ 2 := by rw [norm_one, hnx]; linarith
    have hbound : ‖Complex.exp (y * Complex.I) - (1 + y * Complex.I) *
        (Real.exp (-(y ^ 2 / 2)) : ℂ)‖ ≤ 2 * |y| ^ 3 := by
      rw [hdiff]
      have h1 : ‖R1‖ ≤ |y| ^ 3 * (4 * (6 * 3 : ℝ)⁻¹) := by
        have := hR1; norm_num [Nat.factorial] at this ⊢; linarith
      have h2 : ‖((y ^ 3 / 2 : ℝ) : ℂ) * Complex.I‖ = |y| ^ 3 / 2 := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_div,
          abs_pow]; norm_num
      have h3 : ‖(1 + y * Complex.I) * (R2 : ℂ)‖ ≤ 2 * (|y| ^ 3 / 4) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul hnorm1 hR2' (abs_nonneg _) (by norm_num)
      calc ‖R1 + ((y ^ 3 / 2 : ℝ) : ℂ) * Complex.I - (1 + y * Complex.I) * (R2 : ℂ)‖
          ≤ ‖R1‖ + ‖((y ^ 3 / 2 : ℝ) : ℂ) * Complex.I‖ + ‖(1 + y * Complex.I) * (R2 : ℂ)‖ :=
            norm_sub_le_of_le (norm_add_le _ _) le_rfl
        _ ≤ |y| ^ 3 * (4 * (6 * 3 : ℝ)⁻¹) + |y| ^ 3 / 2 + 2 * (|y| ^ 3 / 4) := by
            rw [h2]; linarith
        _ ≤ 2 * |y| ^ 3 := by
            have : 0 ≤ |y| ^ 3 := by positivity
            nlinarith
    have hsplit : Complex.exp (y * Complex.I) / (1 + y * Complex.I) -
        (Real.exp (-(y ^ 2 / 2)) : ℂ) = (Complex.exp (y * Complex.I) - (1 + y * Complex.I) *
          (Real.exp (-(y ^ 2 / 2)) : ℂ)) / (1 + y * Complex.I) := by
      field_simp
    rw [hsplit, norm_div]
    exact (div_le_of_le_mul₀ (norm_nonneg _) (by positivity)
      (hbound.trans (le_mul_of_one_le_right (by positivity) (one_le_norm_one_add_mul_I y))))

/-- `Π_{k<n} (1 + yₖ) ≤ e^{C} (1 + Σ_{k<n} yₖ)` for `yₖ ≥ 0` such that `Σ_{j<k} yⱼ ≤ C` whenever
`yₖ ≠ 0`. -/
theorem prod_one_add_le (y : ℕ → ℝ) (hy0 : ∀ k, 0 ≤ y k) {C : ℝ} (hC : 0 ≤ C)
    (hy : ∀ k, y k ≠ 0 → ∑ j ∈ Finset.range k, y j ≤ C) (n : ℕ) :
    ∏ k ∈ Finset.range n, (1 + y k) ≤ Real.exp C * (1 + ∑ k ∈ Finset.range n, y k) := by
  have hexp : ∀ m, ∏ k ∈ Finset.range m, (1 + y k) ≤ Real.exp (∑ k ∈ Finset.range m, y k) := by
    intro m
    rw [Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun k _ => by linarith [hy0 k]) fun k _ => by
      have := Real.add_one_le_exp (y k); linarith
  induction n with
  | zero =>
    rw [Finset.prod_range_zero, Finset.sum_range_zero, add_zero, mul_one]
    exact Real.one_le_exp hC
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    have hsum0 : 0 ≤ ∑ k ∈ Finset.range n, y k := Finset.sum_nonneg fun k _ => hy0 k
    by_cases hyn : y n = 0
    · rw [hyn, add_zero, mul_one, add_zero]; exact ih
    · have hle := hy n hyn
      have hP0 : 0 ≤ ∏ k ∈ Finset.range n, (1 + y k) :=
        Finset.prod_nonneg fun k _ => by linarith [hy0 k]
      calc (∏ k ∈ Finset.range n, (1 + y k)) * (1 + y n)
          ≤ Real.exp (∑ k ∈ Finset.range n, y k) * (1 + y n) :=
            mul_le_mul_of_nonneg_right (hexp n) (by linarith [hy0 n])
        _ ≤ Real.exp C * (1 + y n) :=
            mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hle) (by linarith [hy0 n])
        _ ≤ Real.exp C * (1 + (∑ k ∈ Finset.range n, y k + y n)) := by
            gcongr; linarith

/-- If `F` is `𝓕`-measurable and `E[G | 𝓕] = 0`, then `E[F G] = 0`. -/
theorem integral_mul_eq_zero_of_condExp {Ω : Type*} {m0 : MeasurableSpace Ω} {Q : Measure Ω}
    [IsFiniteMeasure Q] {m : MeasurableSpace Ω} (hm : m ≤ m0) {F G : Ω → ℝ}
    (hF : StronglyMeasurable[m] F) (hFG : Integrable (fun ω => F ω * G ω) Q)
    (hG : Integrable G Q) (hG0 : Q[G | m] =ᵐ[Q] 0) : ∫ ω, F ω * G ω ∂Q = 0 := by
  have h1 : Q[fun ω => F ω * G ω | m] =ᵐ[Q] fun ω => F ω * Q[G | m] ω :=
    condExp_mul_of_stronglyMeasurable_left hF hFG hG
  have h2 : Q[fun ω => F ω * G ω | m] =ᵐ[Q] fun _ => (0 : ℝ) :=
    h1.trans (hG0.mono fun ω h => by simp only [h, Pi.zero_apply, mul_zero])
  rw [← integral_condExp hm, integral_congr_ae h2, integral_zero]

/-! ### Products of characteristic factors -/

/-- `e^{i Σ xₖ} = Π (1 + i xₖ) · Π e^{i xₖ}/(1 + i xₖ)`. -/
theorem cexp_sum_eq_prod_mul (x : ℕ → ℝ) (n : ℕ) :
    Complex.exp (((∑ k ∈ Finset.range n, x k : ℝ) : ℂ) * Complex.I) =
      (∏ k ∈ Finset.range n, (1 + (x k : ℂ) * Complex.I)) *
        ∏ k ∈ Finset.range n,
          Complex.exp ((x k : ℂ) * Complex.I) / (1 + (x k : ℂ) * Complex.I) := by
  rw [← Finset.prod_mul_distrib]
  push_cast
  rw [Finset.sum_mul, Complex.exp_sum]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hne : (1 : ℂ) + (x k : ℂ) * Complex.I ≠ 0 := by
    intro h
    have := one_le_norm_one_add_mul_I (x k)
    rw [h, norm_zero] at this
    linarith
  rw [mul_div_cancel₀ _ hne]

/-- `‖Π (1 + i xₖ)‖² = Π (1 + xₖ²)`. -/
theorem norm_prod_one_add_sq (x : ℕ → ℝ) (n : ℕ) :
    ‖∏ k ∈ Finset.range n, (1 + (x k : ℂ) * Complex.I)‖ ^ 2 =
      ∏ k ∈ Finset.range n, (1 + x k ^ 2) := by
  rw [norm_prod, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun k _ => norm_one_add_mul_I_sq (x k)

/-- `‖Π e^{i xₖ}/(1 + i xₖ) − e^{−Σ xₖ²/2}‖ ≤ 2 Σ |xₖ|³`. -/
theorem norm_prod_cexp_div_sub_le (x : ℕ → ℝ) (n : ℕ) :
    ‖∏ k ∈ Finset.range n, Complex.exp ((x k : ℂ) * Complex.I) / (1 + (x k : ℂ) * Complex.I) -
      (Real.exp (-((∑ k ∈ Finset.range n, x k ^ 2) / 2)) : ℂ)‖ ≤
      2 * ∑ k ∈ Finset.range n, |x k| ^ 3 := by
  have hprod : (Real.exp (-((∑ k ∈ Finset.range n, x k ^ 2) / 2)) : ℂ) =
      ∏ k ∈ Finset.range n, (Real.exp (-(x k ^ 2 / 2)) : ℂ) := by
    rw [← Complex.ofReal_prod, ← Real.exp_sum]
    congr 2
    rw [Finset.sum_div, ← Finset.sum_neg_distrib]
  rw [hprod, Finset.mul_sum]
  refine (norm_prod_sub_prod_le_sum _ _ (fun k => norm_cexp_div_le_one (x k))
    (fun k => norm_cexp_neg_le_one (by positivity)) n).trans ?_
  exact Finset.sum_le_sum fun k _ => norm_cexp_div_sub_le (x k)

/-! ### The truncated product `Tₙ` -/

/-- The truncation weights `1{Σ_{j<k} Yⱼ² ≤ c}`. -/
noncomputable def truncWeight (Y : ℕ → Ω₀ → ℝ) (c : ℝ) (k : ℕ) (ω : Ω₀) : ℝ :=
  if ∑ j ∈ Finset.range k, Y j ω ^ 2 ≤ c then 1 else 0

/-- The product `T_m = Π_{k<m} (1 + i t Y'ₖ)` of the truncated variables `Y'ₖ = Yₖ 1{…}`. -/
noncomputable def truncProd (Y : ℕ → Ω₀ → ℝ) (c t : ℝ) (m : ℕ) (ω : Ω₀) : ℂ :=
  ∏ k ∈ Finset.range m, (1 + ((t * (Y k ω * truncWeight Y c k ω) : ℝ) : ℂ) * Complex.I)

omit [MeasurableSpace Ω₀] in
/-- The weights are `0` or `1`. -/
theorem truncWeight_eq_zero_or_one (Y : ℕ → Ω₀ → ℝ) (c : ℝ) (k : ℕ) (ω : Ω₀) :
    truncWeight Y c k ω = 0 ∨ truncWeight Y c k ω = 1 := by
  unfold truncWeight; split_ifs <;> simp

omit [MeasurableSpace Ω₀] in
/-- **The truncation bound**: `‖T_m‖² ≤ e^{t² c} (1 + t² Σ_{k<m} Yₖ²)`. -/
theorem norm_truncProd_sq_le (Y : ℕ → Ω₀ → ℝ) {c : ℝ} (hc : 0 ≤ c) (t : ℝ) (m : ℕ) (ω : Ω₀) :
    ‖truncProd Y c t m ω‖ ^ 2 ≤
      Real.exp (t ^ 2 * c) * (1 + t ^ 2 * ∑ k ∈ Finset.range m, Y k ω ^ 2) := by
  set y : ℕ → ℝ := fun k => (t * (Y k ω * truncWeight Y c k ω)) ^ 2 with hy
  have hsq : ∀ k, (Y k ω * truncWeight Y c k ω) ^ 2 ≤ Y k ω ^ 2 := fun k => by
    rcases truncWeight_eq_zero_or_one Y c k ω with h | h <;> rw [h] <;>
      nlinarith [sq_nonneg (Y k ω)]
  have hprop : ∀ k, y k ≠ 0 → ∑ j ∈ Finset.range k, y j ≤ t ^ 2 * c := by
    intro k hk
    have hw : truncWeight Y c k ω = 1 := by
      rcases truncWeight_eq_zero_or_one Y c k ω with h | h
      · exfalso; apply hk; simp [hy, h]
      · exact h
    have hq : ∑ j ∈ Finset.range k, Y j ω ^ 2 ≤ c := by
      unfold truncWeight at hw
      split_ifs at hw with h
      · exact h
      · simp at hw
    calc ∑ j ∈ Finset.range k, y j = t ^ 2 * ∑ j ∈ Finset.range k,
          (Y j ω * truncWeight Y c j ω) ^ 2 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; simp only [hy]; ring
      _ ≤ t ^ 2 * ∑ j ∈ Finset.range k, Y j ω ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hsq j) (sq_nonneg t)
      _ ≤ t ^ 2 * c := mul_le_mul_of_nonneg_left hq (sq_nonneg t)
  have h1 := prod_one_add_le y (fun k => sq_nonneg _) (mul_nonneg (sq_nonneg t) hc) hprop m
  rw [truncProd, norm_prod_one_add_sq (fun k => t * (Y k ω * truncWeight Y c k ω))]
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  refine add_le_add le_rfl ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  simp only [hy]
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left (hsq k) (sq_nonneg t)

/-- **`E[T_m] = 1`**: for martingale differences `Yₖ` (`𝓕ₖ₊₁`-measurable, square integrable,
`E[Yₖ | 𝓕ₖ] = 0`), the truncated product has mean `1`. -/
theorem integral_truncProd_eq_one {Q : Measure Ω₀} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ₀} {Y : ℕ → Ω₀ → ℝ} (hY : ∀ k, StronglyMeasurable[ℱ (k + 1)] (Y k))
    (hL2 : ∀ k, MemLp (Y k) 2 Q) (h0 : ∀ k, Q[Y k | ℱ k] =ᵐ[Q] 0) {c : ℝ} (hc : 0 ≤ c)
    (t : ℝ) (m : ℕ) : ∫ ω, truncProd Y c t m ω ∂Q = 1 := by
  -- measurability with respect to the filtration
  have hYm : ∀ j k, j < k → Measurable[ℱ k] (Y j) := fun j k hjk =>
    (hY j).measurable.mono (ℱ.mono (by omega)) le_rfl
  have hqm : ∀ k, Measurable[ℱ k] fun ω => ∑ j ∈ Finset.range k, Y j ω ^ 2 := fun k =>
    Finset.measurable_sum _ fun j hj => (hYm j k (Finset.mem_range.1 hj)).pow_const 2
  have hwm : ∀ k, Measurable[ℱ k] (truncWeight Y c k) := fun k =>
    Measurable.ite (measurableSet_le (hqm k) measurable_const) measurable_const measurable_const
  have hfac : ∀ k m, k < m → Measurable[ℱ m] fun ω =>
      (1 : ℂ) + ((t * (Y k ω * truncWeight Y c k ω) : ℝ) : ℂ) * Complex.I := by
    intro k m hkm
    have h1 : Measurable[ℱ m] fun ω => t * (Y k ω * truncWeight Y c k ω) :=
      measurable_const.mul ((hYm k m hkm).mul ((hwm k).mono (ℱ.mono hkm.le) le_rfl))
    exact measurable_const.add ((Complex.measurable_ofReal.comp h1).mul measurable_const)
  have hTm : ∀ m, Measurable[ℱ m] (truncProd Y c t m) := fun m =>
    Finset.measurable_prod _ fun k hk => hfac k m (Finset.mem_range.1 hk)
  have hTm0 : ∀ m, Measurable (truncProd Y c t m) := fun m => (hTm m).mono (ℱ.le m) le_rfl
  have hYm0 : ∀ k, Measurable (Y k) := fun k => (hY k).measurable.mono (ℱ.le (k + 1)) le_rfl
  -- integrability of `‖T_m‖²`
  have hTsq : ∀ m, Integrable (fun ω => ‖truncProd Y c t m ω‖ ^ 2) Q := by
    intro m
    have hbd : Integrable (fun ω => Real.exp (t ^ 2 * c) *
        (1 + t ^ 2 * ∑ k ∈ Finset.range m, Y k ω ^ 2)) Q :=
      ((integrable_const 1).add ((integrable_finsetSum _ fun k _ =>
        (hL2 k).integrable_sq).const_mul _)).const_mul _
    refine hbd.mono' ((hTm0 m).norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact norm_truncProd_sq_le Y hc t m ω
  have hTint : ∀ m, Integrable (truncProd Y c t m) Q := fun m =>
    ((integrable_const (1 : ℝ)).add (hTsq m)).mono' (hTm0 m).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        have h := sq_nonneg (‖truncProd Y c t m ω‖ - 1)
        simp only [Pi.add_apply]
        nlinarith [norm_nonneg (truncProd Y c t m ω)])
  induction m with
  | zero => simp [truncProd]
  | succ m ih =>
    -- `∫ T_m Y'_m = 0`
    set w := truncWeight Y c m with hw
    have hprodint : Integrable (fun ω => truncProd Y c t m ω * ((Y m ω * w ω : ℝ) : ℂ)) Q := by
      refine (((hTsq m).add (hL2 m).integrable_sq).const_mul (1 / 2)).mono'
        ((hTm0 m).mul (Complex.measurable_ofReal.comp ((hYm0 m).mul
          ((hwm m).mono (ℱ.le m) le_rfl)))).aestronglyMeasurable
        (Eventually.of_forall fun ω => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      have hw01 : |w ω| ≤ 1 := by
        rcases truncWeight_eq_zero_or_one Y c m ω with h | h <;> simp [hw, h]
      have h1 : ‖truncProd Y c t m ω‖ * (|Y m ω| * |w ω|) ≤ ‖truncProd Y c t m ω‖ * |Y m ω| :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (abs_nonneg _) hw01) (norm_nonneg _)
      have h2 : ‖truncProd Y c t m ω‖ * |Y m ω| ≤
          (‖truncProd Y c t m ω‖ ^ 2 + Y m ω ^ 2) / 2 := by
        nlinarith [sq_nonneg (‖truncProd Y c t m ω‖ - |Y m ω|), sq_abs (Y m ω)]
      simp only [Pi.add_apply]
      linarith
    have hzero : ∫ ω, truncProd Y c t m ω * ((Y m ω * w ω : ℝ) : ℂ) ∂Q = 0 := by
      have hre : ∫ ω, (truncProd Y c t m ω).re * w ω * Y m ω ∂Q = 0 := by
        refine integral_mul_eq_zero_of_condExp (ℱ.le m)
          ((Complex.measurable_re.comp (hTm m)).mul (hwm m)).stronglyMeasurable ?_
          ((hL2 m).integrable one_le_two) (h0 m)
        refine (Complex.reCLM.integrable_comp hprodint).congr (Eventually.of_forall fun ω => ?_)
        simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero]
        ring
      have him : ∫ ω, (truncProd Y c t m ω).im * w ω * Y m ω ∂Q = 0 := by
        refine integral_mul_eq_zero_of_condExp (ℱ.le m)
          ((Complex.measurable_im.comp (hTm m)).mul (hwm m)).stronglyMeasurable ?_
          ((hL2 m).integrable one_le_two) (h0 m)
        refine (Complex.imCLM.integrable_comp hprodint).congr (Eventually.of_forall fun ω => ?_)
        simp only [Complex.imCLM_apply, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, zero_add]
        ring
      apply Complex.ext
      · have hc := Complex.reCLM.integral_comp_comm hprodint
        simp only [Complex.reCLM_apply] at hc
        rw [← hc]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
          Complex.zero_re]
        rw [← hre]
        congr 1; ext ω; ring
      · have hc := Complex.imCLM.integral_comp_comm hprodint
        simp only [Complex.imCLM_apply] at hc
        rw [← hc]
        simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
          Complex.zero_im]
        rw [← him]
        congr 1; ext ω; ring
    have hsplit : truncProd Y c t (m + 1) = fun ω => truncProd Y c t m ω +
        ((t : ℂ) * Complex.I) * (truncProd Y c t m ω * ((Y m ω * w ω : ℝ) : ℂ)) := by
      ext ω
      rw [truncProd, Finset.prod_range_succ, ← truncProd]
      push_cast
      ring
    rw [hsplit, integral_add (hTint m) (hprodint.const_mul _), integral_const_mul, hzero,
      mul_zero, add_zero, ih]

/-! ### The limit `E[Tₙ Uₙ] → L` -/

/-- If `E[Tₙ] = 1`, `E‖Tₙ‖² ≤ K`, `‖Uₙ‖ ≤ 1` and `Uₙ → L` almost surely, then `E[Tₙ Uₙ] → L`. -/
theorem tendsto_integral_mul_of_bdd {Q : Measure Ω₀} [IsProbabilityMeasure Q]
    {T U : ℕ → Ω₀ → ℂ} {L : ℂ} {K : ℝ} (hTm : ∀ n, Measurable (T n))
    (hUm : ∀ n, Measurable (U n)) (hT1 : ∀ n, ∫ ω, T n ω ∂Q = 1)
    (hT2 : ∀ n, Integrable (fun ω => ‖T n ω‖ ^ 2) Q) (hK : ∀ n, ∫ ω, ‖T n ω‖ ^ 2 ∂Q ≤ K)
    (hU : ∀ n ω, ‖U n ω‖ ≤ 1) (hL : ‖L‖ ≤ 1)
    (hUL : ∀ᵐ ω ∂Q, Tendsto (fun n => U n ω) atTop (𝓝 L)) :
    Tendsto (fun n => ∫ ω, T n ω * U n ω ∂Q) atTop (𝓝 L) := by
  have hTint : ∀ n, Integrable (T n) Q := fun n =>
    ((integrable_const (1 : ℝ)).add (hT2 n)).mono' (hTm n).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        simp only [Pi.add_apply]
        nlinarith [norm_nonneg (T n ω), sq_nonneg (‖T n ω‖ - 1)])
  have hULb : ∀ n ω, ‖U n ω - L‖ ≤ 2 := fun n ω =>
    (norm_sub_le _ _).trans (by linarith [hU n ω])
  -- `E‖Uₙ − L‖² → 0`
  have he : Tendsto (fun n => ∫ ω, ‖U n ω - L‖ ^ 2 ∂Q) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := Q) (F := fun n ω => ‖U n ω - L‖ ^ 2)
      (f := fun _ => (0 : ℝ)) (fun _ => (4 : ℝ))
      (fun n => (((hUm n).sub measurable_const).norm.pow_const 2).aestronglyMeasurable)
      (integrable_const 4) (fun n => Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [hULb n ω, norm_nonneg (U n ω - L)])
      (hUL.mono fun ω hω => by
        have h1 := ((hω.sub (tendsto_const_nhds (x := L))).norm.pow 2)
        simpa using h1)
    simpa using h
  have hK0 : 0 ≤ K := (integral_nonneg fun ω => sq_nonneg _).trans (hK 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ := ε / (K + 1) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 he (δ * ε) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hen := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun ω => sq_nonneg _)] at hen
  -- `E[TₙUₙ] − L = E[Tₙ(Uₙ − L)]`
  have hprod : Integrable (fun ω => T n ω * (U n ω - L)) Q :=
    ((hTint n).norm.const_mul 2).mono'
      ((hTm n).mul ((hUm n).sub measurable_const)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [norm_mul]; nlinarith [hULb n ω, norm_nonneg (T n ω)])
  have heq : ∫ ω, T n ω * U n ω ∂Q - L = ∫ ω, T n ω * (U n ω - L) ∂Q := by
    have : (fun ω => T n ω * (U n ω - L)) = fun ω => T n ω * U n ω - T n ω * L := by
      ext ω; ring
    rw [this, integral_sub (hprod.add ((hTint n).mul_const L) |>.congr
      (Eventually.of_forall fun ω => by simp only [Pi.add_apply]; ring))
      ((hTint n).mul_const L), integral_mul_const, hT1, one_mul]
  rw [dist_eq_norm, heq]
  -- the Cauchy–Schwarz type bound
  have hbound : ∀ ω, ‖T n ω * (U n ω - L)‖ ≤
      (δ * ‖T n ω‖ ^ 2 + δ⁻¹ * ‖U n ω - L‖ ^ 2) / 2 := by
    intro ω
    rw [norm_mul]
    have h1 : 0 ≤ (δ * ‖T n ω‖ - ‖U n ω - L‖) ^ 2 := sq_nonneg _
    have h2 : δ * ‖T n ω‖ * ‖U n ω - L‖ ≤ (δ ^ 2 * ‖T n ω‖ ^ 2 + ‖U n ω - L‖ ^ 2) / 2 := by
      nlinarith
    rw [show (δ * ‖T n ω‖ ^ 2 + δ⁻¹ * ‖U n ω - L‖ ^ 2) / 2 =
        δ⁻¹ * ((δ ^ 2 * ‖T n ω‖ ^ 2 + ‖U n ω - L‖ ^ 2) / 2) by field_simp]
    rw [le_inv_mul_iff₀ hδpos]
    linarith
  have hbint : Integrable (fun ω => (δ * ‖T n ω‖ ^ 2 + δ⁻¹ * ‖U n ω - L‖ ^ 2) / 2) Q := by
    refine (((hT2 n).const_mul δ).add (Integrable.const_mul ?_ δ⁻¹)).div_const 2
    exact (integrable_const (4 : ℝ)).mono'
      (((hUm n).sub measurable_const).norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [hULb n ω, norm_nonneg (U n ω - L)])
  calc ‖∫ ω, T n ω * (U n ω - L) ∂Q‖ ≤ ∫ ω, ‖T n ω * (U n ω - L)‖ ∂Q :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ ω, (δ * ‖T n ω‖ ^ 2 + δ⁻¹ * ‖U n ω - L‖ ^ 2) / 2 ∂Q :=
        integral_mono hprod.norm hbint hbound
    _ = (δ * ∫ ω, ‖T n ω‖ ^ 2 ∂Q + δ⁻¹ * ∫ ω, ‖U n ω - L‖ ^ 2 ∂Q) / 2 := by
        rw [integral_div, integral_add ((hT2 n).const_mul δ), integral_const_mul,
          integral_const_mul]
        refine Integrable.const_mul ?_ δ⁻¹
        exact (integrable_const (4 : ℝ)).mono'
          (((hUm n).sub measurable_const).norm.pow_const 2).aestronglyMeasurable
          (Eventually.of_forall fun ω => by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
            nlinarith [hULb n ω, norm_nonneg (U n ω - L)])
    _ ≤ (δ * K + δ⁻¹ * (δ * ε)) / 2 := by
        gcongr
        · exact hK n
    _ < ε := by
        rw [inv_mul_cancel_left₀ hδpos.ne']
        have : δ * K < ε := by
          rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith
        linarith

/-! ### The martingale CLT -/

/-- **A martingale CLT** (McLeish's method): let `Dₖ` be `𝓕ₖ₊₁`-measurable square-integrable
martingale differences, `E[Dₖ | 𝓕ₖ] = 0`, with `(1/n) Σ_{k<n} Dₖ² → σ²` almost surely and
`Σ_{k<n} E[Dₖ²] ≤ C n`. Then `n^{−1/2} Σ_{k<n} Dₖ` converges in distribution to `N(0, σ²)`. -/
theorem martingale_clt {Q : Measure Ω₀} [IsProbabilityMeasure Q] {ℱ : Filtration ℕ mΩ₀}
    {D : ℕ → Ω₀ → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0) {σ2 : ℝ} (hσ : 0 ≤ σ2)
    (hvar : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, D k ω ^ 2) / n) atTop
      (𝓝 σ2))
    {C : ℝ} (hbdd : ∀ n : ℕ, ∑ k ∈ Finset.range n, ∫ ω, D k ω ^ 2 ∂Q ≤ C * n)
    {Ω' : Type*} [MeasurableSpace Ω'] {Q' : Measure Ω'} [IsProbabilityMeasure Q'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 σ2.toNNReal) Q') :
    TendstoInDistribution (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, D k ω) atTop
      Z (fun _ => Q) Q' := by
  have hDm : ∀ k, Measurable (D k) := fun k => (hD k).measurable.mono (ℱ.le (k + 1)) le_rfl
  have hC0 : 0 ≤ C := by
    have := hbdd 1
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_one, mul_one] at this
    exact (integral_nonneg fun ω => sq_nonneg _).trans this
  refine TendstoInDistribution.of_tendsto_charFun (fun n =>
    (measurable_const.mul (Finset.measurable_sum _ fun k _ => hDm k)).aemeasurable)
    hZ.aemeasurable fun t => ?_
  set L : ℂ := ((Real.exp (-(t ^ 2 * σ2 / 2)) : ℝ) : ℂ) with hLdef
  have htarget : charFun (Q'.map Z) t = L := by
    rw [hZ.map_eq, charFun_gaussianReal, hLdef, Real.coe_toNNReal _ hσ]
    push_cast
    congr 1
    ring
  rw [htarget]
  have hcf : ∀ n : ℕ, charFun (Q.map fun ω => (√(n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, D k ω) t =
      ∫ ω, Complex.exp (((t * ((√(n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, D k ω) : ℝ) : ℂ) *
        Complex.I) ∂Q := by
    intro n
    have hSm : Measurable fun ω => (√(n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, D k ω :=
      measurable_const.mul (Finset.measurable_sum _ fun k _ => hDm k)
    have hcont : Continuous fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) := by
      fun_prop
    rw [charFun_apply_real, integral_map hSm.aemeasurable hcont.aestronglyMeasurable]
    congr 1
    ext ω
    push_cast
    ring_nf
  simp_rw [hcf]
  -- the normalised and truncated variables
  set c := σ2 + 1 with hc
  have hc0 : 0 ≤ c := by linarith
  set X : ℕ → ℕ → Ω₀ → ℝ := fun n k ω => (√(n : ℝ))⁻¹ * D k ω with hXdef
  have hXsq_pt : ∀ n k ω, X n k ω ^ 2 = D k ω ^ 2 / n := fun n k ω => by
    simp only [hXdef]
    rw [mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n), inv_mul_eq_div]
  have hXm : ∀ n k, StronglyMeasurable[ℱ (k + 1)] (X n k) := fun n k =>
    (hD k).const_mul _
  have hXL2 : ∀ n k, MemLp (X n k) 2 Q := fun n k => (hL2 k).const_mul _
  have hX0 : ∀ n k, Q[X n k | ℱ k] =ᵐ[Q] 0 := fun n k => by
    have := condExp_smul (μ := Q) ((√(n : ℝ))⁻¹) (D k) (ℱ k)
    refine this.trans ((h0 k).mono fun ω h => ?_)
    simp [h]
  set w : ℕ → ℕ → Ω₀ → ℝ := fun n k ω => truncWeight (X n) c k ω with hw
  set T : ℕ → Ω₀ → ℂ := fun n ω => truncProd (X n) c t n ω with hTdef
  set U : ℕ → Ω₀ → ℂ := fun n ω => ∏ k ∈ Finset.range n,
    Complex.exp (((t * (X n k ω * w n k ω)) : ℝ) * Complex.I) /
      (1 + ((t * (X n k ω * w n k ω)) : ℝ) * Complex.I) with hUdef
  -- measurability
  have hXm0 : ∀ n k, Measurable (X n k) := fun n k => measurable_const.mul (hDm k)
  have hwm : ∀ n k, Measurable (w n k) := fun n k =>
    Measurable.ite (measurableSet_le (Finset.measurable_sum _ fun j _ => (hXm0 n j).pow_const 2)
      measurable_const) measurable_const measurable_const
  have hxpm : ∀ n k, Measurable fun ω => ((t * (X n k ω * w n k ω) : ℝ) : ℂ) := fun n k =>
    Complex.measurable_ofReal.comp (measurable_const.mul ((hXm0 n k).mul (hwm n k)))
  have hTm : ∀ n, Measurable (T n) := fun n =>
    Finset.measurable_prod _ fun k _ => measurable_const.add ((hxpm n k).mul measurable_const)
  have hUm : ∀ n, Measurable (U n) := fun n =>
    Finset.measurable_prod _ fun k _ => (Complex.measurable_exp.comp
      ((hxpm n k).mul measurable_const)).div (measurable_const.add
        ((hxpm n k).mul measurable_const))
  -- `e^{itS'ₙ} = TₙUₙ`
  have hTU : ∀ n ω, Complex.exp (((t * ∑ k ∈ Finset.range n, X n k ω * w n k ω : ℝ) : ℂ) *
      Complex.I) = T n ω * U n ω := by
    intro n ω
    rw [Finset.mul_sum]
    exact cexp_sum_eq_prod_mul (fun k => t * (X n k ω * w n k ω)) n
  -- `E[Tₙ] = 1` and `E‖Tₙ‖² ≤ K`
  have hT1 : ∀ n, ∫ ω, T n ω ∂Q = 1 := fun n =>
    integral_truncProd_eq_one (hXm n) (hXL2 n) (hX0 n) hc0 t n
  have hXsq : ∀ n, ∫ ω, ∑ k ∈ Finset.range n, X n k ω ^ 2 ∂Q ≤ C := by
    intro n
    rw [integral_finsetSum _ fun k _ => (hXL2 n k).integrable_sq]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hC0]
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have : ∀ k, ∫ ω, X n k ω ^ 2 ∂Q = (∫ ω, D k ω ^ 2 ∂Q) / n := fun k => by
      simp only [hXdef, mul_pow, inv_pow, Real.sq_sqrt hn'.le]
      rw [integral_const_mul, inv_mul_eq_div]
    simp_rw [this]
    rw [← Finset.sum_div, div_le_iff₀ hn']
    exact hbdd n
  have hT2 : ∀ n, Integrable (fun ω => ‖T n ω‖ ^ 2) Q := by
    intro n
    have hbd : Integrable (fun ω => Real.exp (t ^ 2 * c) *
        (1 + t ^ 2 * ∑ k ∈ Finset.range n, X n k ω ^ 2)) Q :=
      ((integrable_const 1).add ((integrable_finsetSum _ fun k _ =>
        (hXL2 n k).integrable_sq).const_mul _)).const_mul _
    refine hbd.mono' ((hTm n).norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact norm_truncProd_sq_le (X n) hc0 t n ω
  have hK : ∀ n, ∫ ω, ‖T n ω‖ ^ 2 ∂Q ≤ Real.exp (t ^ 2 * c) * (1 + t ^ 2 * C) := by
    intro n
    calc ∫ ω, ‖T n ω‖ ^ 2 ∂Q ≤ ∫ ω, Real.exp (t ^ 2 * c) *
          (1 + t ^ 2 * ∑ k ∈ Finset.range n, X n k ω ^ 2) ∂Q :=
          integral_mono (hT2 n) (((integrable_const 1).add ((integrable_finsetSum _ fun k _ =>
            (hXL2 n k).integrable_sq).const_mul _)).const_mul _)
            fun ω => norm_truncProd_sq_le (X n) hc0 t n ω
      _ = Real.exp (t ^ 2 * c) * (1 + t ^ 2 * ∫ ω, ∑ k ∈ Finset.range n, X n k ω ^ 2 ∂Q) := by
          rw [integral_const_mul, integral_add (integrable_const 1)
            ((integrable_finsetSum _ fun k _ => (hXL2 n k).integrable_sq).const_mul _),
            integral_const_mul, integral_const, probReal_univ, one_smul]
      _ ≤ Real.exp (t ^ 2 * c) * (1 + t ^ 2 * C) := by
          gcongr
          exact hXsq n
  have hU1 : ∀ n ω, ‖U n ω‖ ≤ 1 := fun n ω => by
    rw [hUdef, norm_prod]
    exact Finset.prod_le_one₀ (fun k _ => norm_nonneg _) fun k _ => norm_cexp_div_le_one _
  have hL1 : ‖L‖ ≤ 1 := norm_cexp_neg_le_one (by positivity)
  -- the almost sure behaviour
  have hae : ∀ᵐ ω ∂Q, (∀ᶠ n in atTop, ∀ k < n, w n k ω = 1) ∧
      Tendsto (fun n => U n ω) atTop (𝓝 L) := by
    filter_upwards [hvar] with ω hω
    set q : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, X n k ω ^ 2 with hq
    have hqeq : ∀ n, 1 ≤ n → q n = (∑ k ∈ Finset.range n, D k ω ^ 2) / n := by
      intro n _
      simp only [hq, hXsq_pt, Finset.sum_div]
    have hqt : Tendsto q atTop (𝓝 σ2) := hω.congr' (eventually_atTop.2 ⟨1, fun n hn =>
      (hqeq n hn).symm⟩)
    have hev : ∀ᶠ n in atTop, q n < c := hqt.eventually (eventually_lt_nhds (by linarith))
    have hw1 : ∀ᶠ n in atTop, ∀ k < n, w n k ω = 1 := by
      filter_upwards [hev] with n hn k hk
      have hle : ∑ j ∈ Finset.range k, X n j ω ^ 2 ≤ c :=
        calc ∑ j ∈ Finset.range k, X n j ω ^ 2 ≤ q n :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hk.le)
                fun j _ _ => sq_nonneg _
          _ ≤ c := hn.le
      simp [hw, truncWeight, hle]
    refine ⟨hw1, ?_⟩
    -- the largest square among the first `n + 1`
    set u : ℕ → ℝ := fun j => D j ω ^ 2 with hu
    have hu1 : Tendsto (fun j : ℕ => u j / ((j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_term_div_of_tendsto_average hω
    have hkmax : ∀ n, ∃ k ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (n + 1), u j ≤ u k :=
      fun n => Finset.exists_max_image _ u Finset.nonempty_range_add_one
    choose kmax hkmax1 hkmax2 using hkmax
    have hu2 := tendsto_index_div_of_le (fun j => sq_nonneg _) hu1 (k := kmax)
      (fun n => Nat.lt_succ_iff.1 (Finset.mem_range.1 (hkmax1 n)))
    set B : ℕ → ℝ := fun n => √(u (kmax n) / n) with hB
    have hBt : Tendsto B atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
        have : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
          tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
        rw [add_zero] at this
        refine this.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
        have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
        field_simp
      have h2 := hu2.mul h1
      rw [zero_mul] at h2
      have h3 := (Real.continuous_sqrt.tendsto _).comp h2
      rw [Real.sqrt_zero] at h3
      refine h3.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
      have hn0 : (n : ℝ) + 1 ≠ 0 := by positivity
      have hn1 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have : u (kmax n) / ((n : ℝ) + 1) * (((n : ℝ) + 1) / n) = u (kmax n) / n := by
        field_simp
      simp only [Function.comp_apply, hB]
      rw [this]
    have hXB : ∀ n, 1 ≤ n → ∀ k < n, |X n k ω| ≤ B n := by
      intro n hn k hk
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [hB, ← Real.sqrt_sq_eq_abs]
      refine Real.sqrt_le_sqrt ?_
      rw [hXsq_pt]
      exact div_le_div_of_nonneg_right (hkmax2 n k (Finset.mem_range.2 (by omega))) hn'.le
    -- `Uₙ − e^{−t² qₙ/2} → 0` and `e^{−t² qₙ/2} → L`
    have hexp : Tendsto (fun n => ((Real.exp (-(t ^ 2 * q n / 2)) : ℝ) : ℂ)) atTop (𝓝 L) := by
      have := (Complex.continuous_ofReal.comp Real.continuous_exp).tendsto _ |>.comp
        (((hqt.const_mul (t ^ 2)).div_const 2).neg)
      exact this
    have hdiff : Tendsto (fun n => U n ω - ((Real.exp (-(t ^ 2 * q n / 2)) : ℝ) : ℂ)) atTop
        (𝓝 0) := by
      have hbound := ((hBt.mul hqt).const_mul (2 * |t| ^ 3))
      rw [zero_mul, mul_zero] at hbound
      refine squeeze_zero_norm' ?_ hbound
      filter_upwards [hw1, eventually_ge_atTop 1] with n hn hn1
      have hU' : U n ω = ∏ k ∈ Finset.range n, Complex.exp (((t * X n k ω) : ℝ) * Complex.I) /
          (1 + ((t * X n k ω) : ℝ) * Complex.I) := by
        refine Finset.prod_congr rfl fun k hk => ?_
        rw [hn k (Finset.mem_range.1 hk), mul_one]
      have hq' : -(t ^ 2 * q n / 2) = -((∑ k ∈ Finset.range n, (t * X n k ω) ^ 2) / 2) := by
        simp only [hq, mul_pow, Finset.mul_sum]
      rw [hU', hq']
      refine (norm_prod_cexp_div_sub_le (fun k => t * X n k ω) n).trans ?_
      have hsum : ∑ k ∈ Finset.range n, |t * X n k ω| ^ 3 ≤ |t| ^ 3 * (B n * q n) := by
        have h3 : 0 ≤ |t| ^ 3 := by positivity
        calc ∑ k ∈ Finset.range n, |t * X n k ω| ^ 3
            ≤ ∑ k ∈ Finset.range n, |t| ^ 3 * (B n * X n k ω ^ 2) := by
              refine Finset.sum_le_sum fun k hk => ?_
              have h1 := hXB n hn1 k (Finset.mem_range.1 hk)
              rw [abs_mul, mul_pow]
              have : |X n k ω| ^ 3 ≤ B n * X n k ω ^ 2 := by
                have e : |X n k ω| ^ 3 = |X n k ω| * X n k ω ^ 2 := by
                  rw [← sq_abs (X n k ω)]; ring
                rw [e]
                exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
              exact mul_le_mul_of_nonneg_left this h3
          _ = |t| ^ 3 * (B n * q n) := by
              rw [← Finset.mul_sum, ← Finset.mul_sum]
      calc 2 * ∑ k ∈ Finset.range n, |t * X n k ω| ^ 3 ≤ 2 * (|t| ^ 3 * (B n * q n)) := by
            linarith
        _ = 2 * |t| ^ 3 * (B n * q n) := by ring
    have := hdiff.add hexp
    rw [zero_add] at this
    exact this.congr fun n => by ring
  -- `E[e^{itS'ₙ}] → L`
  have hmain := tendsto_integral_mul_of_bdd hTm hUm hT1 hT2 hK hU1 hL1
    (hae.mono fun ω h => h.2)
  -- `E[e^{itSₙ}] − E[e^{itS'ₙ}] → 0`
  have hS : ∀ (n : ℕ) ω, (t * ((√(n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, D k ω) : ℝ) =
      t * ∑ k ∈ Finset.range n, X n k ω := fun n ω => by
    simp only [hXdef, Finset.mul_sum]
  have hmeasS : ∀ n, Measurable fun ω => Complex.exp
      (((t * ∑ k ∈ Finset.range n, X n k ω : ℝ) : ℂ) * Complex.I) := fun n =>
    Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp (measurable_const.mul
      (Finset.measurable_sum _ fun k _ => hXm0 n k))).mul measurable_const)
  have hmeasS' : ∀ n, Measurable fun ω => Complex.exp
      (((t * ∑ k ∈ Finset.range n, X n k ω * w n k ω : ℝ) : ℂ) * Complex.I) := fun n =>
    Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp (measurable_const.mul
      (Finset.measurable_sum _ fun k _ => (hXm0 n k).mul (hwm n k)))).mul measurable_const)
  have hgap : Tendsto (fun n => ∫ ω, (Complex.exp
      (((t * ∑ k ∈ Finset.range n, X n k ω : ℝ) : ℂ) * Complex.I) - Complex.exp
      (((t * ∑ k ∈ Finset.range n, X n k ω * w n k ω : ℝ) : ℂ) * Complex.I)) ∂Q) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := Q) (f := fun _ => (0 : ℂ))
      (fun _ => (2 : ℝ)) (fun n => ((hmeasS n).sub (hmeasS' n)).aestronglyMeasurable)
      (integrable_const 2) (fun n => Eventually.of_forall fun ω => by
        refine (norm_sub_le _ _).trans ?_
        rw [Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I]; norm_num)
      (hae.mono fun ω h => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [h.1] with n hn
        have : ∑ k ∈ Finset.range n, X n k ω * w n k ω = ∑ k ∈ Finset.range n, X n k ω :=
          Finset.sum_congr rfl fun k hk => by rw [hn k (Finset.mem_range.1 hk), mul_one]
        simp only [Pi.sub_apply]
        rw [this, sub_self])
    simpa using h
  have hintS : ∀ n, Integrable (fun ω => Complex.exp
      (((t * ∑ k ∈ Finset.range n, X n k ω : ℝ) : ℂ) * Complex.I)) Q := fun n =>
    Integrable.of_bound (hmeasS n).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by rw [Complex.norm_exp_ofReal_mul_I])
  have hintS' : ∀ n, Integrable (fun ω => Complex.exp
      (((t * ∑ k ∈ Finset.range n, X n k ω * w n k ω : ℝ) : ℂ) * Complex.I)) Q := fun n =>
    Integrable.of_bound (hmeasS' n).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by rw [Complex.norm_exp_ofReal_mul_I])
  have hfinal := hgap.add hmain
  rw [zero_add] at hfinal
  refine hfinal.congr fun n => ?_
  have e1 : ∫ ω, T n ω * U n ω ∂Q = ∫ ω, Complex.exp
      (((t * ∑ k ∈ Finset.range n, X n k ω * w n k ω : ℝ) : ℂ) * Complex.I) ∂Q :=
    integral_congr_ae (Eventually.of_forall fun ω => (hTU n ω).symm)
  have hsubint : Integrable (fun ω => Complex.exp
      (((t * ∑ k ∈ Finset.range n, X n k ω : ℝ) : ℂ) * Complex.I) - Complex.exp
      (((t * ∑ k ∈ Finset.range n, X n k ω * w n k ω : ℝ) : ℂ) * Complex.I)) Q :=
    (hintS n).sub (hintS' n)
  rw [e1, ← integral_add hsubint (hintS' n)]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [sub_add_cancel]
  rw [hS n ω]

end MeynTweedie.GeneralizedDrift
