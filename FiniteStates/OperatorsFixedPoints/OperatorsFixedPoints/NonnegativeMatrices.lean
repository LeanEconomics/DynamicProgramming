/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OperatorsFixedPoints.PerronFrobenius
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Consequences of Perron–Frobenius: spectral bounds, the local spectral radius, Markov matrices

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §2.3.1.1–§2.3.1.3
(pp. 69–71).

* Lemma 2.3.2 (Exercise 2.3.1): for `A ≥ 0`, `ρ(A)` lies between the smallest
  and largest row sums, and between the smallest and largest column sums, by
  summing the eigenvector equations.
* Lemma 2.3.3: for `A ≥ 0` and `h ≫ 0`, the local spectral radius
  `‖Aᵏh‖^{1/k}` converges to `ρ(A)`; the book cites Krasnosel'skii et al.
  (1972). The proof here squeezes between `‖Aᵏ‖^{1/k} (min h)^{1/k}` and
  `‖Aᵏ‖^{1/k} ‖h‖^{1/k}`, both of which converge to `ρ(A)` by Gelfand's formula.
  Norms are the supremum norm on vectors and the induced ℓ∞ operator norm.
* Markov matrices (Exercise 2.3.2 (i)–(iii), Exercise 2.3.3). The uniqueness
  and positivity of the stationary distribution for irreducible `P`
  (Exercise 2.3.2 (iv)) rest on the irreducible Perron–Frobenius theorem and
  are not claimed here.
-/

open Matrix Finset Filter Topology

namespace SargentStachurski.OperatorsFixedPoints

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} [NeZero n]

/-! ### Lemma 2.3.2 -/

/-- Lemma 2.3.2 (ii), p. 70, lower bound: if every column sum of `A ≥ 0` is at least `c`, then
`ρ(A) ≥ c`. Summing `Ae = ρe` over the coordinates of a nonnegative eigenvector `e` with `∑ e = S`
gives `ρS = ∑ⱼ colsumⱼ eⱼ ≥ cS`. -/
theorem le_specRad_of_colsum_ge (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j) {c : ℝ}
    (hc : ∀ j, c ≤ ∑ i, A i j) : c ≤ specRad A := by
  obtain ⟨e, he0, hene, he⟩ := perron_frobenius A hA
  have hS : 0 < ∑ j, e j := by
    rcases (sum_nonneg fun j _ => he0 j).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hene
      funext j
      exact (sum_eq_zero_iff_of_nonneg fun j _ => he0 j).1 h.symm j (mem_univ j)
  have hsum : specRad A * ∑ j, e j = ∑ j, (∑ i, A i j) * e j := by
    calc specRad A * ∑ j, e j = ∑ i, (A *ᵥ e) i := by
          rw [he]
          simp only [Pi.smul_apply, smul_eq_mul, ← mul_sum]
      _ = ∑ i, ∑ j, A i j * e j := rfl
      _ = ∑ j, ∑ i, A i j * e j := sum_comm
      _ = ∑ j, (∑ i, A i j) * e j := by simp only [sum_mul]
  have hge : c * ∑ j, e j ≤ ∑ j, (∑ i, A i j) * e j := by
    rw [mul_sum]
    exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hc j) (he0 j)
  rw [← hsum] at hge
  exact le_of_mul_le_mul_right hge hS

/-- Lemma 2.3.2 (ii), p. 70, upper bound: if every column sum of `A ≥ 0` is at most `C`, then
`ρ(A) ≤ C`. -/
theorem specRad_le_of_colsum_le (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j) {C : ℝ}
    (hC : ∀ j, ∑ i, A i j ≤ C) : specRad A ≤ C := by
  obtain ⟨e, he0, hene, he⟩ := perron_frobenius A hA
  have hS : 0 < ∑ j, e j := by
    rcases (sum_nonneg fun j _ => he0 j).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hene
      funext j
      exact (sum_eq_zero_iff_of_nonneg fun j _ => he0 j).1 h.symm j (mem_univ j)
  have hsum : specRad A * ∑ j, e j = ∑ j, (∑ i, A i j) * e j := by
    calc specRad A * ∑ j, e j = ∑ i, (A *ᵥ e) i := by
          rw [he]
          simp only [Pi.smul_apply, smul_eq_mul, ← mul_sum]
      _ = ∑ i, ∑ j, A i j * e j := rfl
      _ = ∑ j, ∑ i, A i j * e j := sum_comm
      _ = ∑ j, (∑ i, A i j) * e j := by simp only [sum_mul]
  have hle : ∑ j, (∑ i, A i j) * e j ≤ C * ∑ j, e j := by
    rw [mul_sum]
    exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hC j) (he0 j)
  rw [← hsum] at hle
  exact le_of_mul_le_mul_right hle hS

/-- Lemma 2.3.2 (i), p. 70: `ρ(A)` lies between the smallest and largest row sums of `A ≥ 0`, by
transposition. -/
theorem le_specRad_of_rowsum_ge (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j) {c : ℝ}
    (hc : ∀ i, c ≤ ∑ j, A i j) : c ≤ specRad A := by
  rw [← specRad_transpose]
  exact le_specRad_of_colsum_ge Aᵀ (fun i j => hA j i) hc

theorem specRad_le_of_rowsum_le (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j) {C : ℝ}
    (hC : ∀ i, ∑ j, A i j ≤ C) : specRad A ≤ C := by
  rw [← specRad_transpose]
  exact specRad_le_of_colsum_le Aᵀ (fun i j => hA j i) hC

/-! ### Lemma 2.3.3: the local spectral radius -/

/-- `c^{1/k} → 1` for `c > 0`. -/
theorem tendsto_rpow_one_div_natCast {c : ℝ} (hc : 0 < c) :
    Tendsto (fun k : ℕ => c ^ (1 / (k : ℝ))) atTop (𝓝 1) := by
  have h1 : Tendsto (fun k : ℕ => Real.log c * (1 / (k : ℝ))) atTop (𝓝 (Real.log c * 0)) :=
    tendsto_const_nhds.mul tendsto_one_div_atTop_nhds_zero_nat
  rw [mul_zero] at h1
  have h2 := (Real.continuous_exp.tendsto 0).comp h1
  rw [Real.exp_zero] at h2
  refine h2.congr fun k => ?_
  simp only [Function.comp]
  rw [Real.rpow_def_of_pos hc, mul_comm]

omit [NeZero n] in
/-- For `A ≥ 0` and `h ≥ m𝟙 > 0`, the row sums of `Aᵏ` are bounded by `(Aᵏh)ᵢ/m`, hence
`m‖Aᵏ‖ ≤ ‖Aᵏh‖`. -/
theorem norm_pow_mul_le_norm_mulVec (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    {h : Fin n → ℝ} {m : ℝ} (hm : 0 < m) (hmh : ∀ j, m ≤ h j) (k : ℕ) :
    m * ‖A ^ k‖ ≤ ‖A ^ k *ᵥ h‖ := by
  have hAk := pow_nonneg_entries hA k
  rw [← le_div_iff₀' hm]
  refine norm_le_of_rowsum_abs_le (A ^ k) (div_nonneg (norm_nonneg _) hm.le) fun i => ?_
  rw [le_div_iff₀ hm]
  calc (∑ j, |(A ^ k) i j|) * m = ∑ j, (A ^ k) i j * m := by
        rw [sum_mul]
        exact sum_congr rfl fun j _ => by rw [abs_of_nonneg (hAk i j)]
    _ ≤ ∑ j, (A ^ k) i j * h j := sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hmh j) (hAk i j)
    _ = (A ^ k *ᵥ h) i := rfl
    _ ≤ ‖A ^ k *ᵥ h‖ := by
        have := norm_le_pi_norm (A ^ k *ᵥ h) i
        rw [Real.norm_eq_abs] at this
        exact (le_abs_self _).trans this

/-- Lemma 2.3.3 (p. 70): for `A ≥ 0` and `h ≫ 0`, `‖Aᵏh‖^{1/k} → ρ(A)`, in the supremum norm. -/
theorem tendsto_norm_pow_mulVec_rpow (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    {h : Fin n → ℝ} (hh : ∀ j, 0 < h j) :
    Tendsto (fun k : ℕ => ‖A ^ k *ᵥ h‖ ^ (1 / (k : ℝ))) atTop (𝓝 (specRad A)) := by
  -- the minimum `m` of `h` and the norm `‖h‖`
  obtain ⟨j₀, -, hj₀⟩ := exists_min_image univ h univ_nonempty
  set m := h j₀ with hm
  have hmpos : 0 < m := hh j₀
  have hmh : ∀ j, m ≤ h j := fun j => hj₀ j (mem_univ j)
  have hhnorm : 0 < ‖h‖ := by
    have := norm_le_pi_norm h j₀
    rw [Real.norm_eq_abs, abs_of_pos (hh j₀)] at this
    exact hmpos.trans_le this
  have hG := tendsto_norm_pow_rpow A
  -- upper: `‖Aᵏh‖^{1/k} ≤ ‖Aᵏ‖^{1/k} ‖h‖^{1/k}`
  have hup : Tendsto (fun k : ℕ => ‖A ^ k‖ ^ (1 / (k : ℝ)) * ‖h‖ ^ (1 / (k : ℝ))) atTop
      (𝓝 (specRad A * 1)) := hG.mul (tendsto_rpow_one_div_natCast hhnorm)
  -- lower: `m^{1/k} ‖Aᵏ‖^{1/k} ≤ ‖Aᵏh‖^{1/k}`
  have hlo : Tendsto (fun k : ℕ => m ^ (1 / (k : ℝ)) * ‖A ^ k‖ ^ (1 / (k : ℝ))) atTop
      (𝓝 (1 * specRad A)) := (tendsto_rpow_one_div_natCast hmpos).mul hG
  rw [mul_one] at hup
  rw [one_mul] at hlo
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hup (fun k => ?_) (fun k => ?_)
  · rw [← Real.mul_rpow hmpos.le (norm_nonneg _)]
    exact Real.rpow_le_rpow (by positivity) (norm_pow_mul_le_norm_mulVec A hA hmpos hmh k)
      (by positivity)
  · rw [← Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    exact Real.rpow_le_rpow (norm_nonneg _) (Matrix.linfty_opNorm_mulVec _ _) (by positivity)

/-! ### Markov matrices (§2.3.1.3) -/

/-- A stochastic (Markov) matrix (p. 71): nonnegative with unit row sums. -/
structure IsMarkov (P : Matrix (Fin n) (Fin n) ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ P i j
  rowsum : ∀ i, ∑ j, P i j = 1

omit [NeZero n] in
/-- Exercise 2.3.2 (i), p. 71: the product of Markov matrices is Markov. -/
theorem IsMarkov.mul {P Q : Matrix (Fin n) (Fin n) ℝ} (hP : IsMarkov P) (hQ : IsMarkov Q) :
    IsMarkov (P * Q) where
  nonneg i j := by
    rw [Matrix.mul_apply]
    exact sum_nonneg fun l _ => mul_nonneg (hP.nonneg i l) (hQ.nonneg l j)
  rowsum i := by
    simp only [Matrix.mul_apply]
    rw [sum_comm]
    simp only [← mul_sum, hQ.rowsum, mul_one, hP.rowsum]

omit [NeZero n] in
/-- Powers of a Markov matrix are Markov. -/
theorem IsMarkov.pow {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsMarkov P) (k : ℕ) :
    IsMarkov (P ^ k) := by
  induction k with
  | zero =>
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
    · simp [pow_zero, Matrix.one_apply]
  | succ k ih => rw [pow_succ]; exact ih.mul hP

/-- Exercise 2.3.2 (ii), p. 71: `ρ(P) = 1` for a Markov matrix. -/
theorem IsMarkov.specRad_eq_one {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsMarkov P) : specRad P = 1 :=
  specRad_eq_of_rowsum_eq P hP.nonneg zero_le_one hP.rowsum

/-- Exercise 2.3.2 (iii), p. 71: a Markov matrix has a stationary distribution, a row vector
`ψ ≥ 0` with `ψ𝟙 = 1` and `ψP = ψ`, by the left Perron–Frobenius eigenvector for `ρ(P) = 1`. -/
theorem IsMarkov.exists_stationary {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsMarkov P) :
    ∃ ψ : Fin n → ℝ, (∀ i, 0 ≤ ψ i) ∧ ∑ i, ψ i = 1 ∧ ψ ᵥ* P = ψ := by
  obtain ⟨ε, hε0, hεne, hε⟩ := perron_frobenius_left P hP.nonneg
  rw [hP.specRad_eq_one, one_smul] at hε
  have hS : 0 < ∑ i, ε i := by
    rcases (sum_nonneg fun i _ => hε0 i).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hεne
      funext i
      exact (sum_eq_zero_iff_of_nonneg fun i _ => hε0 i).1 h.symm i (mem_univ i)
  refine ⟨(∑ i, ε i)⁻¹ • ε, fun i => mul_nonneg (inv_nonneg.2 hS.le) (hε0 i), ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, ← mul_sum]
    exact inv_mul_cancel₀ hS.ne'
  · rw [smul_vecMul, hε]

/-- Exercise 2.3.3 (p. 71): for a Markov matrix `P` and `ε > 0` there is no `h` with
`Ph ≥ h + ε`: at a maximiser `x̄` of `h`, `(Ph)(x̄) ≤ h(x̄)`. -/
theorem IsMarkov.not_mulVec_ge_add {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsMarkov P) {ε : ℝ}
    (hε : 0 < ε) : ¬ ∃ h : Fin n → ℝ, ∀ x, h x + ε ≤ (P *ᵥ h) x := by
  rintro ⟨h, hh⟩
  obtain ⟨x, -, hx⟩ := exists_max_image univ h univ_nonempty
  have : (P *ᵥ h) x ≤ h x := by
    calc (P *ᵥ h) x = ∑ y, P x y * h y := rfl
      _ ≤ ∑ y, P x y * h x :=
          sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hx y (mem_univ y)) (hP.nonneg x y)
      _ = h x := by rw [← sum_mul, hP.rowsum, one_mul]
  linarith [hh x]

end SargentStachurski.OperatorsFixedPoints
