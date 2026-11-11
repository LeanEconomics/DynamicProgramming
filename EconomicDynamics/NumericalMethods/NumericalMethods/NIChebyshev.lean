/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ChebyshevGauss
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import NumericalMethods.NIWeighted

/-!
# Chebyshev polynomials (Miao, §11.3.1, pp. 357–358)

The Chebyshev polynomials are Mathlib's `Polynomial.Chebyshev.T ℝ n`. This module proves the
book's claims about them.

* `ni_cheb_recursion`: `T₀ = 1`, `T₁ = x`, `T₂ = 2x² − 1`, `Tₙ = 2x Tₙ₋₁ − Tₙ₋₂`.
* `ni_cheb_cos`, `ni_cheb_arccos`: `Tₙ(cos θ) = cos nθ` and `Tₙ(x) = cos(n arccos x)` on
  `[−1, 1]`.
* `ni_chebWeight_isWeighting`: `(1 − x²)^{−1/2}` is a weighting function on `(−1, 1)`
  (Definition 11.3.1); `ni_cheb_orthogonal`: the `Tₙ` are mutually orthogonal for it, with
  `⟨T₀, T₀⟩ = π` and `⟨Tₙ, Tₙ⟩ = π/2` for `n ≥ 1`.
* `ni_cheb_roots`: the roots of `Tₙ` are exactly `xₖ = cos(π(2k − 1)/(2n))`, `k = 1, …, n`, and
  these are distinct (`ni_chebNode_injOn`).
* `ni_cheb_extrema_value`, `ni_cheb_isLocalExtrOn_iff`, `ni_cheb_localMax_eq_one`,
  `ni_cheb_localMin_eq_neg_one`: on `[−1, 1]`, `Tₙ` has its `n + 1` extrema exactly at
  `cos(πk/n)`, `k = 0, …, n` (distinct, `ni_cheb_extrema_injOn`); `Tₙ = 1` at every maximum and
  `Tₙ = −1` at every minimum.
* `ni_cheb_discrete_orthogonality`: for the `m` roots `xₖ` of `Tₘ` and `i, j < m`,
  `∑ₖ Tᵢ(xₖ)Tⱼ(xₖ)` is `0` (`i ≠ j`), `m/2` (`i = j ≠ 0`), `m` (`i = j = 0`).
-/

open Polynomial Polynomial.Chebyshev Real MeasureTheory

namespace Miao.NumericalMethods

/-- Miao, p. 357: the Chebyshev recursion `T₀ = 1`, `T₁ = x`, `T₂ = 2x² − 1`,
`Tₙ = 2x Tₙ₋₁ − Tₙ₋₂`. -/
theorem ni_cheb_recursion :
    T ℝ 0 = 1 ∧ T ℝ 1 = X ∧ T ℝ 2 = 2 * X ^ 2 - 1 ∧
      ∀ n : ℕ, T ℝ ((n + 2 : ℕ) : ℤ) = 2 * X * T ℝ ((n + 1 : ℕ) : ℤ) - T ℝ (n : ℤ) := by
  refine ⟨T_zero ℝ, T_one ℝ, T_two ℝ, fun n => ?_⟩
  push_cast
  exact T_add_two ℝ n

/-- Miao, p. 357: `Tₙ(cos θ) = cos(nθ)`. -/
theorem ni_cheb_cos (n : ℕ) (θ : ℝ) : (T ℝ n).eval (cos θ) = cos (n * θ) := by
  have := T_real_cos θ (n : ℤ)
  simp only [Int.cast_natCast] at this
  exact this

/-- Miao, p. 357: equivalently `Tₙ(x) = cos(n arccos x)` for `x ∈ [−1, 1]`. -/
theorem ni_cheb_arccos (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (T ℝ n).eval x = cos (n * arccos x) := by
  rw [← ni_cheb_cos, cos_arccos hx.1 hx.2]

/-- The Chebyshev weighting function `w(x) = (1 − x²)^{−1/2}` (Miao, p. 357). -/
noncomputable def ni_chebWeight (x : ℝ) : ℝ := (1 - x ^ 2) ^ (-(1 / 2 : ℝ))

theorem ni_chebWeight_eq {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ni_chebWeight x = √(1 - x ^ 2)⁻¹ := by
  have h : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  rw [ni_chebWeight, Real.rpow_neg h, Real.sqrt_inv, Real.sqrt_eq_rpow]

/-- **Definition 11.3.1** for the Chebyshev weight (Miao, p. 357): `(1 − x²)^{−1/2}` is positive
on `(−1, 1)` with finite integral. -/
theorem ni_chebWeight_isWeighting : ni_IsWeightingFunction ni_chebWeight (Set.Ioo (-1) 1) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [ni_chebWeight_eq hx]
    have : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    positivity
  · have h := intervalIntegrable_sqrt_one_sub_sq_inv
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at h
    refine (h.mono_set Set.Ioo_subset_Ioc_self).congr_fun (fun x hx => ?_) measurableSet_Ioo
    rw [ni_chebWeight_eq hx]

/-- The weighted inner product with the Chebyshev weight is integration against Mathlib's
`measureT`. -/
theorem ni_inner_cheb_eq (f g : ℝ → ℝ) :
    ni_inner ni_chebWeight (Set.Ioo (-1) 1) f g = ∫ x, f x * g x ∂measureT := by
  rw [integral_measureT, intervalIntegral.integral_of_le (by norm_num),
    integral_Ioc_eq_integral_Ioo]
  unfold ni_inner
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  rw [ni_chebWeight_eq hx]

/-- **Definition 11.3.1** applied to the Chebyshev polynomials (Miao, p. 357): the `Tₙ` are
mutually orthogonal with respect to `(1 − x²)^{−1/2}` on `[−1, 1]`. -/
theorem ni_cheb_orthogonal :
    ni_Orthogonal ni_chebWeight (Set.Ioo (-1) 1) (fun n : ℕ => fun x => (T ℝ n).eval x) := by
  intro i j hij
  rw [ni_inner_cheb_eq]
  exact integral_eval_T_real_mul_eval_T_real_measureT_of_ne hij

/-- Miao, p. 357: `⟨T₀, T₀⟩_w = π` and `⟨Tₙ, Tₙ⟩_w = π/2` for `n ≥ 1`. -/
theorem ni_cheb_norms (n : ℕ) :
    ni_inner ni_chebWeight (Set.Ioo (-1) 1) (fun x => (T ℝ n).eval x) (fun x => (T ℝ n).eval x)
      = if n = 0 then π else π / 2 := by
  rw [ni_inner_cheb_eq]
  split_ifs with h
  · subst h
    exact integral_eval_T_real_mul_self_measureT_zero
  · exact integral_T_real_mul_self_measureT_of_ne_zero h

/-- The Chebyshev nodes `xₖ = cos(π(2k − 1)/(2n))` (Miao, p. 357). -/
noncomputable def ni_chebNode (n k : ℕ) : ℝ := cos (π * (2 * k - 1) / (2 * n))

theorem ni_chebNode_succ (n l : ℕ) :
    ni_chebNode n (l + 1) = cos ((2 * l + 1) * π / (2 * n)) := by
  unfold ni_chebNode
  congr 1
  push_cast
  ring

/-- Miao, p. 357: the roots of `Tₙ` are exactly `xₖ = cos(π(2k − 1)/(2n))`, `k = 1, …, n`. -/
theorem ni_cheb_roots (n : ℕ) (x : ℝ) :
    (T ℝ n).eval x = 0 ↔ ∃ k ∈ Finset.Icc 1 n, x = ni_chebNode n k := by
  have hne : T ℝ n ≠ 0 := T_ne_zero (R := ℝ) n
  rw [← IsRoot.def, ← mem_roots hne, roots_T_real, Finset.mem_val, Finset.mem_image]
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨l + 1, Finset.mem_Icc.mpr ⟨by omega, by simp at hl; omega⟩, ?_⟩
    rw [ni_chebNode_succ]
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    refine ⟨k - 1, Finset.mem_range.mpr (by omega), ?_⟩
    have : k = (k - 1) + 1 := by omega
    rw [this, ni_chebNode_succ, Nat.add_sub_cancel]

/-- Miao, p. 357: the `n` Chebyshev nodes are distinct. -/
theorem ni_chebNode_injOn (n : ℕ) : Set.InjOn (ni_chebNode n) (Finset.Icc 1 n : Set ℕ) := by
  intro k hk l hl hkl
  have hk' := Finset.mem_Icc.mp (Finset.mem_coe.mp hk)
  have hl' := Finset.mem_Icc.mp (Finset.mem_coe.mp hl)
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have mem : ∀ j : ℕ, 1 ≤ j → j ≤ n → π * (2 * j - 1) / (2 * n) ∈ Set.Icc 0 π := by
    intro j hj1 hj2
    have hj1' : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    have hj2' : (j : ℝ) ≤ n := by exact_mod_cast hj2
    constructor
    · apply div_nonneg _ (by positivity)
      exact mul_nonneg pi_pos.le (by linarith)
    · rw [div_le_iff₀ (by positivity)]
      nlinarith [pi_pos]
  have h := injOn_cos (mem k hk'.1 hk'.2) (mem l hl'.1 hl'.2) hkl
  field_simp at h
  have : (k : ℝ) = l := by nlinarith [pi_pos]
  exact_mod_cast this

/-- Miao, p. 358: at the `n + 1` points `cos(πk/n)`, `k = 0, …, n`, `Tₙ = (−1)ᵏ`; in particular
`Tₙ = ±1` there. -/
theorem ni_cheb_extrema_value {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    (T ℝ n).eval (cos (π * k / n)) = (-1) ^ k := by
  rw [show π * k / n = k * π / n by ring, eval_T_real_cos_int_mul_pi_div hn,
    Int.cast_negOnePow_natCast]

/-- Miao, p. 358: the `n + 1` extremal points `cos(πk/n)`, `k = 0, …, n`, are distinct. -/
theorem ni_cheb_extrema_injOn {n : ℕ} (hn : n ≠ 0) :
    Set.InjOn (fun k : ℕ => cos (π * k / n)) (Finset.range (n + 1) : Set ℕ) := by
  intro k hk l hl hkl
  have hk' := Finset.mem_range.mp (Finset.mem_coe.mp hk)
  have hl' := Finset.mem_range.mp (Finset.mem_coe.mp hl)
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have mem : ∀ j : ℕ, j < n + 1 → π * j / n ∈ Set.Icc 0 π := by
    intro j hj
    have hj' : (j : ℝ) ≤ n := by exact_mod_cast (show j ≤ n by omega)
    constructor
    · positivity
    · rw [div_le_iff₀ hn']
      nlinarith [pi_pos]
  have h := injOn_cos (mem k hk') (mem l hl') hkl
  field_simp at h
  have : (k : ℝ) = l := by nlinarith [pi_pos]
  exact_mod_cast this

/-- Miao, p. 358: `|Tₙ(x)| ≤ 1` on `[−1, 1]`. -/
theorem ni_cheb_abs_le_one (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(T ℝ n).eval x| ≤ 1 :=
  abs_eval_T_real_le_one n (abs_le.mpr hx)

/-- A Chebyshev polynomial of positive degree is not locally constant at any point of
`[−1, 1]` relative to `[−1, 1]`. -/
theorem ni_cheb_not_locally_const {n : ℕ} (hn : n ≠ 0) {x c : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1)
    (h : ∀ᶠ y in nhdsWithin x (Set.Icc (-1) 1), (T ℝ n).eval y = c) : False := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp h
  have hsub : ∃ a b : ℝ, a < b ∧ Set.Ioo a b ⊆ {y | IsRoot (T ℝ n - Polynomial.C c) y} := by
    rcases lt_or_eq_of_le hx.2 with hlt | heq
    · refine ⟨x, min (x + ε) 1, lt_min (by linarith) hlt, fun y hy => ?_⟩
      have hy1 : y < x + ε := lt_of_lt_of_le hy.2 (min_le_left _ _)
      have hy2 : y < 1 := lt_of_lt_of_le hy.2 (min_le_right _ _)
      have hb : y ∈ Metric.ball x ε := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [hy.1]
      have : (T ℝ n).eval y = c := hball ⟨hb, ⟨by linarith [hx.1, hy.1], hy2.le⟩⟩
      simp [IsRoot, this]
    · refine ⟨max (x - ε) (-1), x, max_lt (by linarith) (by linarith), fun y hy => ?_⟩
      have hy1 : x - ε < y := lt_of_le_of_lt (le_max_left _ _) hy.1
      have hy2 : -1 < y := lt_of_le_of_lt (le_max_right _ _) hy.1
      have hb : y ∈ Metric.ball x ε := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [hy.2]
      have : (T ℝ n).eval y = c := hball ⟨hb, ⟨hy2.le, by linarith [hy.2]⟩⟩
      simp [IsRoot, this]
  obtain ⟨a, b, hab, hsub⟩ := hsub
  have hzero := Polynomial.eq_zero_of_infinite_isRoot _ ((Set.Ioo_infinite hab).mono hsub)
  have hT : T ℝ n = Polynomial.C c := sub_eq_zero.mp hzero
  have h1 : (T ℝ n).eval (cos (π / (2 * n))) = 0 := by
    rw [ni_cheb_cos]
    have : (n : ℝ) * (π / (2 * n)) = π / 2 := by
      field_simp
    rw [this, cos_pi_div_two]
  have h2 : (T ℝ n).eval 1 = 1 := by exact_mod_cast T_eval_one ℝ (n : ℤ)
  rw [hT, eval_C] at h1 h2
  linarith

/-- On `[−1, 1]`, `Tₙ` takes only the values `±1` at local extrema (relative to `[−1, 1]`). -/
theorem ni_cheb_localExtr_value {n : ℕ} (hn : n ≠ 0) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1)
    (h : IsLocalExtrOn (T ℝ n).eval (Set.Icc (-1) 1) x) :
    (T ℝ n).eval x = 1 ∨ (T ℝ n).eval x = -1 := by
  rcases eq_or_ne x 1 with rfl | h1
  · left; exact_mod_cast T_eval_one ℝ (n : ℤ)
  rcases eq_or_ne x (-1) with rfl | h2
  · have := T_eval_neg_one ℝ (n : ℤ)
    rw [Int.cast_negOnePow_natCast] at this
    rw [this]
    exact neg_one_pow_eq_or ℝ n
  have hint : x ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hx.1 (Ne.symm h2), lt_of_le_of_ne hx.2 h1⟩
  have hnhds : Set.Icc (-1 : ℝ) 1 ∈ nhds x := Icc_mem_nhds hint.1 hint.2
  have hext : IsLocalExtr (T ℝ n).eval x := by
    rcases h with (h : IsLocalMinOn _ _ _) | (h : IsLocalMaxOn _ _ _)
    · exact Or.inl (h.isLocalMin hnhds)
    · exact Or.inr (h.isLocalMax hnhds)
  rcases eq_or_ne n 1 with rfl | hn1
  · exfalso
    have hd := hext.deriv_eq_zero
    rw [Polynomial.deriv] at hd
    simp at hd
  obtain ⟨k, -, rfl⟩ := (isLocalExtr_T_real_iff (by omega) x).mp hext
  rw [eval_T_real_cos_int_mul_pi_div hn, Int.cast_negOnePow_natCast]
  exact neg_one_pow_eq_or ℝ k

/-- Miao, p. 358: at every maximum of `Tₙ` on `[−1, 1]` (local, relative to `[−1, 1]`),
`Tₙ(x) = 1`. -/
theorem ni_cheb_localMax_eq_one {n : ℕ} (hn : n ≠ 0) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1)
    (h : IsLocalMaxOn (T ℝ n).eval (Set.Icc (-1) 1) x) : (T ℝ n).eval x = 1 := by
  rcases ni_cheb_localExtr_value hn hx (Or.inr h) with h1 | h1
  · exact h1
  · exfalso
    refine ni_cheb_not_locally_const hn hx (c := -1) ?_
    filter_upwards [h, self_mem_nhdsWithin] with y hy hyI
    have := (abs_le.mp (ni_cheb_abs_le_one n hyI)).1
    linarith

/-- Miao, p. 358: at every minimum of `Tₙ` on `[−1, 1]` (local, relative to `[−1, 1]`),
`Tₙ(x) = −1`. -/
theorem ni_cheb_localMin_eq_neg_one {n : ℕ} (hn : n ≠ 0) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) (h : IsLocalMinOn (T ℝ n).eval (Set.Icc (-1) 1) x) :
    (T ℝ n).eval x = -1 := by
  rcases ni_cheb_localExtr_value hn hx (Or.inl h) with h1 | h1
  · exfalso
    refine ni_cheb_not_locally_const hn hx (c := 1) ?_
    filter_upwards [h, self_mem_nhdsWithin] with y hy hyI
    have := (abs_le.mp (ni_cheb_abs_le_one n hyI)).2
    linarith
  · exact h1

/-- Miao, p. 358: `Tₙ` (`n ≥ 1`) has its extrema on `[−1, 1]` exactly at the `n + 1` points
`x = cos(πk/n)`, `k = 0, 1, …, n`. -/
theorem ni_cheb_isLocalExtrOn_iff {n : ℕ} (hn : n ≠ 0) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    IsLocalExtrOn (T ℝ n).eval (Set.Icc (-1) 1) x ↔ ∃ k ≤ n, x = cos (π * k / n) := by
  constructor
  · intro h
    rcases h with (h : IsLocalMinOn _ _ _) | (h : IsLocalMaxOn _ _ _)
    · obtain ⟨k, hk, -, rfl⟩ :=
        (eval_T_real_eq_neg_one_iff hn x).mp (ni_cheb_localMin_eq_neg_one hn hx h)
      exact ⟨k, hk, by ring_nf⟩
    · obtain ⟨k, hk, -, rfl⟩ :=
        (eval_T_real_eq_one_iff hn x).mp (ni_cheb_localMax_eq_one hn hx h)
      exact ⟨k, hk, by ring_nf⟩
  · rintro ⟨k, hk, rfl⟩
    rw [show π * k / n = k * π / n by ring]
    exact (isExtrOn_T_real hn hk).isLocalExtrOn

/-- **Discrete orthogonality** (Miao, p. 358): if `xₖ`, `k = 1, …, m`, are the `m` roots of `Tₘ`
and `i, j < m`, then `∑ₖ Tᵢ(xₖ)Tⱼ(xₖ)` is `0` if `i ≠ j`, `m/2` if `i = j ≠ 0` and `m` if
`i = j = 0`. -/
theorem ni_cheb_discrete_orthogonality {m i j : ℕ} (hi : i < m) (hj : j < m) :
    ∑ k ∈ Finset.Icc 1 m, (T ℝ i).eval (ni_chebNode m k) * (T ℝ j).eval (ni_chebNode m k) =
      if i ≠ j then 0 else if i = 0 then (m : ℝ) else m / 2 := by
  have hm : m ≠ 0 := by omega
  have hdeg : (T ℝ i * T ℝ j).degree < 2 * m := by
    rw [degree_mul, degree_T, degree_T]
    simp only [Int.natAbs_natCast]
    norm_cast
    omega
  have hq := integral_eq_sumZeroes hm hdeg
  simp only [eval_mul] at hq
  have hsum : ∑ k ∈ Finset.Icc 1 m,
      (T ℝ i).eval (ni_chebNode m k) * (T ℝ j).eval (ni_chebNode m k) =
      ∑ l ∈ Finset.range m, (T ℝ i).eval (cos ((2 * l + 1) / (2 * m) * π)) *
        (T ℝ j).eval (cos ((2 * l + 1) / (2 * m) * π)) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [add_comm 1 l, ni_chebNode_succ, show (2 * (l : ℝ) + 1) * π / (2 * m) =
      (2 * l + 1) / (2 * m) * π by ring]
  rw [hsum]
  have hm' : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have key : ∑ l ∈ Finset.range m, (T ℝ i).eval (cos ((2 * l + 1) / (2 * m) * π)) *
        (T ℝ j).eval (cos ((2 * l + 1) / (2 * m) * π)) =
      m / π * ∫ x, (T ℝ i).eval x * (T ℝ j).eval x ∂measureT := by
    rw [hq, sumZeroes, ← mul_assoc, div_mul_div_comm, mul_comm (m : ℝ) π,
      div_self (by positivity), one_mul]
    simp only [eval_mul]
  rw [key]
  split_ifs with h1 h2
  · rw [integral_eval_T_real_mul_eval_T_real_measureT_of_ne h1, mul_zero]
  · push Not at h1
    subst h1 h2
    simp only [Nat.cast_zero]
    rw [integral_eval_T_real_mul_self_measureT_zero]
    field_simp
  · push Not at h1
    subst h1
    rw [integral_T_real_mul_self_measureT_of_ne_zero h2]
    field_simp

end Miao.NumericalMethods
