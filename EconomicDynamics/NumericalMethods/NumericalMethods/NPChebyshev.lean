/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NumericalMethods.NPProjection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ChebyshevGauss
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Orthogonal collocation with Chebyshev polynomials

Miao, *Economic Dynamics in Discrete Time*, §11.5 (pp. 371–372 and footnote 7;
p. 375 for the tensor-product basis).

Orthogonal collocation takes as collocation points the `n` roots of the
`(n+1)`-th basis function; with the Chebyshev basis `φⱼ = T_{j−1}` these are the
Chebyshev nodes `x_k = cos((2k + 1)π/(2n))`, `k = 0, …, n − 1`.

* Footnote 7: the `(n+1)`-th Chebyshev basis function `T_n` has degree `n` and
  exactly `n` distinct real roots, the Chebyshev nodes (`np_footnote7_chebyshev`).
  As a statement about arbitrary basis functions it is false: a degree-`n`
  polynomial need not have `n` real roots (`np_footnote7_counterexample`).
* Discrete orthogonality of `T₀, …, T_{n−1}` at the Chebyshev nodes
  (`np_cheb_discrete_orth`) makes the basis matrix `(T_j(x_k))` nonsingular
  (`np_cheb_basis_det_ne_zero`). Hence, with `n` coefficients and the `n`
  Chebyshev nodes: Chebyshev regression (least squares at the nodes) coincides
  with collocation/interpolation (`np_cheb_regression_iff_collocation`), and the
  Galerkin method with the Gauss–Chebyshev quadrature inner product coincides
  with orthogonal collocation (`np_cheb_galerkin_iff_collocation`).
* The tensor-product basis `φ_ij = T_{i−1} ⊗ T_{j−1}` of p. 375 is orthogonal
  for the product Chebyshev weight `w(k, z)`; we prove this on the normalised
  square `[−1, 1]²` (`np_cheb_tensor_orthogonal`). The affine change of
  variables to `[k_m, k_M] × [z_m, z_M]` only rescales the inner product.

The Chebyshev interpolation theorem invoked on p. 372 ("these zero conditions
force `R(x; c)` to be close to zero") belongs to §11.3 and is not repeated here.
-/

namespace Miao.NumericalMethods.NP

open Finset Polynomial Polynomial.Chebyshev Real Matrix MeasureTheory

/-- The `n` Chebyshev nodes `x_k = cos((2k + 1)π/(2n))`, `k = 0, …, n − 1` (Miao, p. 372). -/
noncomputable def np_chebNode (n k : ℕ) : ℝ := cos ((2 * k + 1) / (2 * n) * π)

/-- Footnote 7 (Miao, p. 372) for the Chebyshev basis: the `(n+1)`-th basis function `T_n` has
degree `n` and exactly `n` roots, which are distinct and are the Chebyshev nodes. -/
theorem np_footnote7_chebyshev (n : ℕ) :
    (T ℝ n).natDegree = n ∧ Multiset.card (T ℝ n).roots = n ∧ (T ℝ n).roots.Nodup ∧
      ∀ k < n, (T ℝ n).IsRoot (np_chebNode n k) := by
  refine ⟨(natDegree_T ℝ (n : ℤ)).trans (Int.natAbs_natCast n), ?_, ?_, fun k hk => ?_⟩
  · rw [roots_T_real, Finset.card_val, Finset.card_image_of_injOn, Finset.card_range]
    exact (Finset.range n).nodup_map_iff_injOn.mp (roots_T_real_nodup n)
  · rw [roots_T_real]
    exact (Finset.image _ _).nodup
  · have hn : (n : ℝ) ≠ 0 := by
      have : 0 < n := by omega
      positivity
    rw [IsRoot.def, np_chebNode]
    have h := T_real_cos ((2 * k + 1) / (2 * n) * π) (n : ℤ)
    simp only [Int.cast_natCast] at h
    rw [h, cos_eq_zero_iff]
    exact ⟨k, by push_cast; field_simp⟩

/-- Correction to footnote 7 (Miao, p. 372): a polynomial with degree-`n` leading term need not
have `n` real roots; `X² + 1` has degree `2` and none. -/
theorem np_footnote7_counterexample :
    ∃ p : ℝ[X], p.natDegree = 2 ∧ p.roots = 0 := by
  refine ⟨X ^ 2 + C 1, natDegree_X_pow_add_C, ?_⟩
  refine Multiset.eq_zero_of_forall_notMem fun x hx => ?_
  rw [mem_roots (X_pow_add_C_ne_zero (by norm_num) _), IsRoot.def] at hx
  simp only [eval_add, eval_pow, eval_X, eval_C] at hx
  nlinarith [sq_nonneg x]

/-- The sum of `T_m` over the Chebyshev nodes vanishes unless `2n ∣ m`. -/
theorem np_cheb_sum_T {n : ℕ} (hn : n ≠ 0) {m : ℤ} (hm : ¬ (2 * n : ℤ) ∣ m) :
    ∑ k ∈ range n, (T ℝ m).eval (np_chebNode n k) = 0 := by
  have h := sumZeroes_T_of_not_dvd (n := n) hm
  rw [sumZeroes] at h
  have hpi : π / n ≠ 0 := div_ne_zero pi_ne_zero (Nat.cast_ne_zero.2 hn)
  exact (mul_eq_zero.1 h).resolve_left hpi

theorem np_cheb_not_dvd {n : ℕ} {m : ℤ} (h0 : m ≠ 0) (h1 : |m| < 2 * n) :
    ¬ (2 * n : ℤ) ∣ m := fun h => h0 (Int.eq_zero_of_abs_lt_dvd h h1)

/-- Discrete orthogonality of the Chebyshev polynomials at the Chebyshev nodes: for `i, j < n`,
`∑_k T_i(x_k) T_j(x_k)` is `0` if `i ≠ j`, `n` if `i = j = 0`, and `n/2` if `i = j ≠ 0`. -/
theorem np_cheb_discrete_orth {n i j : ℕ} (hi : i < n) (hj : j < n) :
    ∑ k ∈ range n, (T ℝ i).eval (np_chebNode n k) * (T ℝ j).eval (np_chebNode n k) =
      if i = j then (if i = 0 then (n : ℝ) else n / 2) else 0 := by
  have hn : n ≠ 0 := by omega
  have hprod : ∀ x : ℝ, (T ℝ i).eval x * (T ℝ j).eval x =
      ((T ℝ ((i : ℤ) + j)).eval x + (T ℝ ((i : ℤ) - j)).eval x) / 2 := by
    intro x
    have h := congrArg (Polynomial.eval x) (T_mul_T ℝ (i : ℤ) (j : ℤ))
    simp only [eval_mul, eval_add, eval_ofNat] at h
    linarith
  simp only [hprod]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  have h0 : ∑ k ∈ range n, (T ℝ 0).eval (np_chebNode n k) = n := by simp
  by_cases hij : i = j
  · subst hij
    simp only [sub_self, ↓reduceIte, h0]
    by_cases hi0 : i = 0
    · subst hi0
      simp only [Nat.cast_zero, add_zero, ↓reduceIte, h0]
      ring
    · simp only [hi0, ↓reduceIte]
      rw [np_cheb_sum_T hn (np_cheb_not_dvd (by omega) (by rw [abs_lt]; constructor <;> omega))]
      ring
  · simp only [hij, ↓reduceIte]
    rw [np_cheb_sum_T hn (np_cheb_not_dvd (by omega) (by rw [abs_lt]; constructor <;> omega)),
      np_cheb_sum_T hn (np_cheb_not_dvd (by omega) (by rw [abs_lt]; constructor <;> omega))]
    ring

/-- The Chebyshev basis matrix `(T_j(x_k))` at the `n` Chebyshev nodes is nonsingular. -/
theorem np_cheb_basis_det_ne_zero (n : ℕ) :
    (Matrix.of fun (k j : Fin n) => (T ℝ (j : ℕ)).eval (np_chebNode n k)).det ≠ 0 := by
  set M : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun k j => (T ℝ (j : ℕ)).eval (np_chebNode n k)
  have hG : Mᵀ * M = Matrix.diagonal fun j : Fin n => if (j : ℕ) = 0 then (n : ℝ) else n / 2 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.diagonal_apply]
    simp only [M, Matrix.transpose_apply, Matrix.of_apply]
    rw [Fin.sum_univ_eq_sum_range (fun k => (T ℝ (i : ℕ)).eval (np_chebNode n k) *
      (T ℝ (j : ℕ)).eval (np_chebNode n k)) n, np_cheb_discrete_orth i.2 j.2]
    by_cases h : i = j
    · subst h
      simp
    · have h' : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
      simp [h, h']
  have hdiag :
      (Matrix.diagonal fun j : Fin n => if (j : ℕ) = 0 then (n : ℝ) else n / 2).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun j _ => ?_
    have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by have := j.2; omega)
    split_ifs
    · exact this
    · exact div_ne_zero this two_ne_zero
  intro hM
  apply hdiag
  rw [← hG, Matrix.det_mul, Matrix.det_transpose, hM, mul_zero]

/-- Chebyshev regression and collocation coincide when the number of nodes equals the number of
coefficients (Miao, pp. 371–373): with the basis `T₀, …, T_{n−1}` and the `n` Chebyshev nodes,
`c` minimises `∑_k (f̂(x_k; c) − h(x_k))²` iff `f̂(x_k; c) = h(x_k)` at every node. -/
theorem np_cheb_regression_iff_collocation (n : ℕ) (h : ℝ → ℝ) (c : Fin n → ℝ) :
    (∀ c', ∑ k : Fin n, (1 : ℝ) *
        (np_approx (fun j : Fin n => fun x => (T ℝ (j : ℕ)).eval x) c (np_chebNode n k) -
          h (np_chebNode n k)) ^ 2 ≤
      ∑ k : Fin n, (1 : ℝ) *
        (np_approx (fun j : Fin n => fun x => (T ℝ (j : ℕ)).eval x) c' (np_chebNode n k) -
          h (np_chebNode n k)) ^ 2) ↔
      ∀ k : Fin n, np_approx (fun j : Fin n => fun x => (T ℝ (j : ℕ)).eval x) c
        (np_chebNode n k) = h (np_chebNode n k) :=
  np_regression_iff_interpolation (fun k : Fin n => np_chebNode n k) (fun _ => one_pos)
    (fun j : Fin n => fun x => (T ℝ (j : ℕ)).eval x) h (np_cheb_basis_det_ne_zero n) c

/-- Orthogonal collocation and Galerkin coincide (Miao, pp. 372–373): with the Chebyshev basis,
the Gauss–Chebyshev quadrature inner product at the `n` Chebyshev nodes (weights `π/n`), the
Galerkin conditions `⟨R, T_i⟩ = 0`, `i < n`, hold iff `R` vanishes at the Chebyshev nodes. -/
theorem np_cheb_galerkin_iff_collocation {n : ℕ} (hn : n ≠ 0) (R : ℝ → ℝ) :
    (∀ i, np_proj (np_quadIP (fun k : Fin n => np_chebNode n k) fun _ => π / n) R
        (fun i : Fin n => fun x => (T ℝ (i : ℕ)).eval x) i = 0) ↔
      ∀ k : Fin n, R (np_chebNode n k) = 0 := by
  refine np_galerkin_quadrature_iff_collocation _
    (fun _ => div_ne_zero pi_ne_zero (Nat.cast_ne_zero.2 hn)) R _ ?_
  have h := np_cheb_basis_det_ne_zero n
  rwa [← Matrix.det_transpose] at h

/-- The tensor-product Chebyshev basis is orthogonal for the product Chebyshev weight (Miao,
p. 375), on the normalised square `[−1, 1]²` with weight `(1 − x²)^{−1/2}(1 − y²)^{−1/2}`:
`⟨φ_ij, φ_i'j'⟩_w = ⟨T_i, T_i'⟩⟨T_j, T_j'⟩`, which vanishes unless `(i, j) = (i', j')`. -/
theorem np_cheb_tensor_orthogonal (i j i' j' : ℕ) (h : (i, j) ≠ (i', j')) :
    ∫ p : ℝ × ℝ, ((T ℝ i).eval p.1 * (T ℝ j).eval p.2) * ((T ℝ i').eval p.1 * (T ℝ j').eval p.2)
      ∂(measureT.prod measureT) = 0 := by
  have hsplit : (fun p : ℝ × ℝ => ((T ℝ i).eval p.1 * (T ℝ j).eval p.2) *
      ((T ℝ i').eval p.1 * (T ℝ j').eval p.2)) =
      fun p => ((T ℝ i).eval p.1 * (T ℝ i').eval p.1) * ((T ℝ j).eval p.2 * (T ℝ j').eval p.2) := by
    funext p
    ring
  have : SFinite (measureT : Measure ℝ) := by
    unfold measureT
    infer_instance
  rw [hsplit, integral_prod_mul (fun x => (T ℝ i).eval x * (T ℝ i').eval x)
    (fun y => (T ℝ j).eval y * (T ℝ j').eval y)]
  by_cases hi : i = i'
  · subst hi
    have hj : j ≠ j' := fun e => h (by rw [e])
    rw [integral_eval_T_real_mul_eval_T_real_measureT_of_ne hj, mul_zero]
  · rw [integral_eval_T_real_mul_eval_T_real_measureT_of_ne hi, zero_mul]

end Miao.NumericalMethods.NP
