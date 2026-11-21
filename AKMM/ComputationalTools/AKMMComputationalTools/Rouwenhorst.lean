/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Rouwenhorst method

AKMM, §10.4.2, p. 271. The Rouwenhorst matrix `Π_N` is defined by the recursion of p. 271,
indexed here by `n = N − 1`: `Π_1 = [1]` (which gives the book's `Π_2`, `rouwenhorst_two`), and
`Π_{n+1}` is `p[Π 0; 0′ 0] + (1 − p)[0 Π; 0 0′] + (1 − p)[0′ 0; Π 0] + p[0 0′; 0 Π]` with all but
the top and bottom rows divided by two (`rouwenhorst`).

The book prints the weights of the last two matrices as `p` and `1 − p`; with those weights the
method does not work (`rouwenhorst_printed_counterexample`: for `N = 3`, `p = 3/4` the binomial
law is not invariant and the conditional mean at the top state is `0`, not `ρz`). With the
weights `1 − p`, `p` (Rouwenhorst 1995; Kopecky–Suen 2010) everything holds:

* row `i` of `Π_{n+1}` has generating polynomial `(p + (1 − p)X)^{n−i}((1 − p) + pX)^i`
  (`rouwenhorst_eq_coeff`), so `Π_N` is a Markov matrix (`rouwenhorst_nonneg`,
  `rouwenhorst_row_sum`);
* the conditional mean of the index is `(n − i)(1 − p) + ip` (`rouwenhorst_cond_mean_index`),
  hence on the grid `z̄_j = ψ(j − n/2)`, `E[z′ | z̄ᵢ] = (2p − 1)z̄ᵢ = ρz̄ᵢ` for `p = (1 + ρ)/2`
  (`rouwenhorst_cond_mean`);
* the invariant distribution is binomial, `λ_j = C(n, j)/2ⁿ` (`rouwenhorst_invariant`), with mean
  `0` and variance `ψ²n/4 = m²σ_z²/(N − 1)` on the grid from `−mσ_z` to `mσ_z`
  (`rouwenhorst_stationary_mean`, `rouwenhorst_stationary_var`);
* so `p = (1 + ρ)/2` and `m = √(N − 1)` match the AR(1) mean `0`, variance `σ_z²` and first-order
  autocorrelation `ρ` (`rouwenhorst_matches_ar1`).

The convergence of the invariant law to a normal distribution as `N → ∞` (de Moivre–Laplace) is
cited by the book and not formalised.
-/

namespace AKMM.ComputationalTools

open Polynomial Finset

/-- AKMM, p. 271: the Rouwenhorst matrix `Π_{n+1}` (`N = n + 1` states), as a function of the
row `i` and column `j` (zero outside `0 ≤ i, j ≤ n`), by the recursion with the weights
`p, 1 − p, 1 − p, p` on the four padded copies of `Π_n`, and the rows `0 < i < n` halved. -/
noncomputable def rouwenhorst (p : ℝ) : ℕ → ℕ → ℕ → ℝ
  | 0 => fun i j => if i = 0 ∧ j = 0 then 1 else 0
  | n + 1 => fun i j =>
      if n + 1 < i then 0 else
      (p * rouwenhorst p n i j
        + (1 - p) * (if j = 0 then 0 else rouwenhorst p n i (j - 1))
        + (1 - p) * (if i = 0 then 0 else rouwenhorst p n (i - 1) j)
        + p * (if i = 0 ∨ j = 0 then 0 else rouwenhorst p n (i - 1) (j - 1)))
      / (if i = 0 ∨ i = n + 1 then 1 else 2)

/-- AKMM, p. 271, step 1: the recursion starts from `Π_2 = [p, 1 − p; 1 − p, p]`. -/
theorem rouwenhorst_two (p : ℝ) :
    rouwenhorst p 1 0 0 = p ∧ rouwenhorst p 1 0 1 = 1 - p ∧ rouwenhorst p 1 1 0 = 1 - p ∧
      rouwenhorst p 1 1 1 = p := by
  simp [rouwenhorst]

/-- Rows below the last are zero. -/
theorem rouwenhorst_row_zero (p : ℝ) {n i : ℕ} (hi : n < i) (j : ℕ) :
    rouwenhorst p n i j = 0 := by
  cases n with
  | zero =>
    have : i ≠ 0 := by omega
    simp [rouwenhorst, this]
  | succ n =>
    simp only [rouwenhorst, hi, ↓reduceIte]

/-- AKMM, p. 271: the entries of `Π_N` are nonnegative for `p ∈ [0, 1]`. -/
theorem rouwenhorst_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (n i j : ℕ) :
    0 ≤ rouwenhorst p n i j := by
  induction n generalizing i j with
  | zero =>
    simp only [rouwenhorst]
    split_ifs <;> norm_num
  | succ n ih =>
    simp only [rouwenhorst]
    have hq : 0 ≤ 1 - p := by linarith
    split_ifs <;> first
      | exact le_rfl
      | positivity
      | (apply div_nonneg _ (by norm_num)
         have := ih i j; have := ih i (j - 1); have := ih (i - 1) j; have := ih (i - 1) (j - 1)
         positivity)

/-- The generating polynomial `p + (1 − p)X` of a state that stays low. -/
noncomputable def rwLow (p : ℝ) : ℝ[X] := C (1 - p) * X + C p

/-- The generating polynomial `(1 − p) + pX` of a state that stays high. -/
noncomputable def rwHigh (p : ℝ) : ℝ[X] := C p * X + C (1 - p)

/-- The generating polynomial of row `i` of `Π_{n+1}`: `(p + (1 − p)X)^{n−i}((1 − p) + pX)^i`. -/
noncomputable def rwRow (p : ℝ) (n i : ℕ) : ℝ[X] := rwLow p ^ (n - i) * rwHigh p ^ i

/-- Multiplying by `C v * X + C u` mixes neighbouring coefficients. -/
theorem rw_coeff_linear_mul (u v : ℝ) (Q : ℝ[X]) (j : ℕ) :
    ((C v * X + C u) * Q).coeff j = u * Q.coeff j + v * (if j = 0 then 0 else Q.coeff (j - 1)) := by
  rw [add_mul, coeff_add, mul_assoc, coeff_C_mul, coeff_C_mul]
  cases j with
  | zero => simp
  | succ j => simp [coeff_X_mul]; ring

/-- AKMM, p. 271 (Kopecky–Suen): the entries of `Π_{n+1}` are the coefficients of the row
polynomials, `π_{ij} = [Xʲ](p + (1 − p)X)^{n−i}((1 − p) + pX)^i`. -/
theorem rouwenhorst_eq_coeff (p : ℝ) (n : ℕ) {i : ℕ} (hi : i ≤ n) (j : ℕ) :
    rouwenhorst p n i j = (rwRow p n i).coeff j := by
  induction n generalizing i j with
  | zero =>
    obtain rfl : i = 0 := by omega
    simp only [rouwenhorst, rwRow, Nat.sub_self, pow_zero, mul_one, true_and, coeff_one]
  | succ n ih =>
    simp only [rouwenhorst, show ¬ n + 1 < i by omega, ↓reduceIte]
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · -- the top row
      have hrow : rwRow p (n + 1) 0 = rwLow p * rwRow p n 0 := by
        simp only [rwRow, Nat.sub_zero, pow_zero, mul_one, pow_succ]; ring
      rw [hrow, rwLow, rw_coeff_linear_mul]
      simp only [true_or, ↓reduceIte, mul_zero, add_zero, div_one]
      rw [ih (by omega) j]
      split_ifs
      · ring
      · rw [ih (by omega) (j - 1)]
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      simp only [Nat.add_sub_cancel, Nat.add_eq_zero_iff, one_ne_zero, and_false, false_or,
        ↓reduceIte]
      have hhigh : rwRow p (n + 1) (k + 1) = rwHigh p * rwRow p n k := by
        simp only [rwRow, pow_succ, show n + 1 - (k + 1) = n - k by omega]; ring
      rcases Nat.lt_or_ge k n with hk | hk
      · -- an interior row: both copies contribute, and the row is halved
        have hlow : rwRow p (n + 1) (k + 1) = rwLow p * rwRow p n (k + 1) := by
          simp only [rwRow, show n + 1 - (k + 1) = n - (k + 1) + 1 by omega, pow_succ]; ring
        have hne : k + 1 ≠ n + 1 := by omega
        simp only [hne, ↓reduceIte]
        have e1 := congrArg (fun Q => Q.coeff j) hlow
        have e2 := congrArg (fun Q => Q.coeff j) hhigh
        simp only [rwLow, rwHigh, rw_coeff_linear_mul] at e1 e2
        rw [ih (by omega) j, ih (by omega) j]
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · simp only [↓reduceIte, mul_zero, add_zero] at e1 e2 ⊢
          rw [div_eq_iff (by norm_num)]
          linarith
        · have hj0 : j ≠ 0 := by omega
          simp only [hj0, ↓reduceIte] at e1 e2 ⊢
          rw [ih (by omega) (j - 1), ih (by omega) (j - 1), div_eq_iff (by norm_num)]
          linarith
      · -- the bottom row: only the shifted copy contributes
        obtain rfl : k = n := by omega
        simp only [↓reduceIte, div_one]
        rw [rouwenhorst_row_zero p (by omega : k < k + 1),
          rouwenhorst_row_zero p (by omega : k < k + 1), hhigh, rwHigh, rw_coeff_linear_mul,
          ih le_rfl j]
        split_ifs
        · ring
        · rw [ih le_rfl (j - 1)]; ring

/-- The row polynomials have degree at most `n`. -/
theorem rwRow_natDegree_le (p : ℝ) {n i : ℕ} (hi : i ≤ n) : (rwRow p n i).natDegree ≤ n := by
  have hl : (rwLow p).natDegree ≤ 1 := by unfold rwLow; exact natDegree_linear_le
  have hh : (rwHigh p).natDegree ≤ 1 := by unfold rwHigh; exact natDegree_linear_le
  unfold rwRow
  calc (rwLow p ^ (n - i) * rwHigh p ^ i).natDegree
      ≤ (rwLow p ^ (n - i)).natDegree + (rwHigh p ^ i).natDegree := natDegree_mul_le
    _ ≤ (n - i) * 1 + i * 1 := by
        gcongr
        · exact natDegree_pow_le.trans (Nat.mul_le_mul_left _ hl)
        · exact natDegree_pow_le.trans (Nat.mul_le_mul_left _ hh)
    _ = n := by omega

/-- A sum of coefficients times powers is an evaluation. -/
theorem rw_sum_coeff_pow {Q : ℝ[X]} {n : ℕ} (hQ : Q.natDegree ≤ n) (x : ℝ) :
    ∑ j ∈ range (n + 1), Q.coeff j * x ^ j = Q.eval x :=
  (eval_eq_sum_range' (by omega) x).symm

/-- A sum of coefficients times indices is the derivative at `1`. -/
theorem rw_sum_coeff_mul_index {Q : ℝ[X]} {n : ℕ} (hQ : Q.natDegree ≤ n) :
    ∑ j ∈ range (n + 1), Q.coeff j * j = (derivative Q).eval 1 := by
  rw [derivative_eval, sum_over_range' Q (fun k => by simp) (n + 1) (by omega)]
  simp

/-- AKMM, p. 271: "divide all but the top and the bottom rows by two so that the elements in each
row are equal to one": every row of `Π_{n+1}` sums to one. -/
theorem rouwenhorst_row_sum (p : ℝ) {n i : ℕ} (hi : i ≤ n) :
    ∑ j ∈ range (n + 1), rouwenhorst p n i j = 1 := by
  have h := rw_sum_coeff_pow (rwRow_natDegree_le p hi) 1
  simp only [one_pow, mul_one] at h
  rw [sum_congr rfl fun j _ => rouwenhorst_eq_coeff p n hi j, h]
  simp [rwRow, rwLow, rwHigh]

/-- AKMM, p. 271: the conditional mean of the next index from row `i` is
`(n − i)(1 − p) + ip` (each of the `n − i` low coins turns high with probability `1 − p`, each of
the `i` high coins stays high with probability `p`). -/
theorem rouwenhorst_cond_mean_index (p : ℝ) {n i : ℕ} (hi : i ≤ n) :
    ∑ j ∈ range (n + 1), rouwenhorst p n i j * j = ((n - i : ℕ) : ℝ) * (1 - p) + i * p := by
  rw [sum_congr rfl fun j _ => by rw [rouwenhorst_eq_coeff p n hi j],
    rw_sum_coeff_mul_index (rwRow_natDegree_le p hi)]
  simp [rwRow, rwLow, rwHigh, derivative_mul, derivative_pow]

/-- The polynomial `(X + 1)ⁿ` is the binomial combination of the row polynomials. -/
theorem rw_binomial_rows (p : ℝ) (n : ℕ) :
    (X + 1 : ℝ[X]) ^ n = ∑ i ∈ range (n + 1), ((n.choose i : ℕ) : ℝ[X]) * rwRow p n i := by
  have hsum : rwHigh p + rwLow p = X + 1 := by
    simp only [rwHigh, rwLow]
    rw [show C p * X + C (1 - p) + (C (1 - p) * X + C p) =
        C (p + (1 - p)) * X + C ((1 - p) + p) by simp only [C_add]; ring]
    simp
  rw [← hsum, add_pow]
  refine sum_congr rfl fun i _ => ?_
  unfold rwRow
  ring

/-- AKMM, p. 271: the invariant distribution of `Π_{n+1}` is the binomial law
`λ_j = C(n, j)/2ⁿ`, for every `p`. -/
theorem rouwenhorst_invariant (p : ℝ) (n j : ℕ) :
    ∑ i ∈ range (n + 1), (n.choose i : ℝ) / 2 ^ n * rouwenhorst p n i j =
      (n.choose j : ℝ) / 2 ^ n := by
  have h := congrArg (fun Q => Q.coeff j) (rw_binomial_rows p n)
  simp only [coeff_X_add_one_pow, finsetSum_coeff, coeff_natCast_mul] at h
  rw [h, div_eq_mul_inv, sum_mul]
  refine sum_congr rfl fun i hi => ?_
  rw [rouwenhorst_eq_coeff p n (by simpa [Nat.lt_succ_iff] using hi) j]
  ring

/-- The binomial weights sum to `2ⁿ`, with first moment `n2ⁿ/2` and second moment
`n(n + 1)2ⁿ/4`. -/
theorem rw_binomial_moments (n : ℕ) :
    ∑ j ∈ range (n + 1), (n.choose j : ℝ) = 2 ^ n ∧
      ∑ j ∈ range (n + 1), (j : ℝ) * n.choose j = n * 2 ^ n / 2 ∧
      ∑ j ∈ range (n + 1), (j : ℝ) ^ 2 * n.choose j = n * (n + 1) * 2 ^ n / 4 := by
  have h0 : ∑ j ∈ range (n + 1), (n.choose j : ℝ) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  have h1 : ∀ m : ℕ, ∑ j ∈ range (m + 1), (j : ℝ) * m.choose j = m * 2 ^ m / 2 := by
    intro m
    have := Nat.sum_range_mul_choose m
    have hc : ∑ j ∈ range (m + 1), (j : ℝ) * m.choose j = ((m * 2 ^ (m - 1) : ℕ) : ℝ) := by
      rw [← this]; push_cast; rfl
    rw [hc]
    cases m with
    | zero => simp
    | succ m => push_cast; rw [pow_succ]; ring
  refine ⟨h0, h1 n, ?_⟩
  cases n with
  | zero => simp
  | succ m =>
    rw [sum_range_succ']
    have hterm : ∀ k ∈ range (m + 1), ((k + 1 : ℕ) : ℝ) ^ 2 * ((m + 1).choose (k + 1) : ℝ) =
        (m + 1) * ((k : ℝ) * m.choose k + m.choose k) := by
      intro k _
      have := Nat.add_one_mul_choose_eq m k
      have hc : ((m + 1 : ℕ) : ℝ) * (m.choose k : ℝ) =
          ((m + 1).choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at hc ⊢
      nlinarith [hc]
    rw [sum_congr rfl hterm, ← mul_sum, sum_add_distrib, h1 m,
      (by exact_mod_cast Nat.sum_range_choose m : ∑ j ∈ range (m + 1), (m.choose j : ℝ) = 2 ^ m)]
    push_cast
    rw [pow_succ]
    ring

/-- AKMM, p. 271: the equally spaced grid `z̄_j = ψ(j − n/2)`, `j = 0, …, n`; with
`ψ = 2mσ_z/n` it runs from `−mσ_z` to `mσ_z`. -/
noncomputable def rwGrid (ψ : ℝ) (n j : ℕ) : ℝ := ψ * (j - n / 2)

/-- The grid runs from `−mσ_z` to `mσ_z` when `ψ = 2mσ_z/n`. -/
theorem rwGrid_ends {n : ℕ} (hn : 0 < n) (m σz : ℝ) :
    rwGrid (2 * m * σz / n) n 0 = -(m * σz) ∧ rwGrid (2 * m * σz / n) n n = m * σz := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  unfold rwGrid
  constructor <;> field_simp <;> ring

/-- AKMM, p. 271: on the grid, the conditional mean is `E[z′ | z̄ᵢ] = (2p − 1)z̄ᵢ`. -/
theorem rouwenhorst_cond_mean (p ψ : ℝ) {n i : ℕ} (hi : i ≤ n) :
    ∑ j ∈ range (n + 1), rouwenhorst p n i j * rwGrid ψ n j = (2 * p - 1) * rwGrid ψ n i := by
  have h1 := rouwenhorst_row_sum p hi
  have h2 := rouwenhorst_cond_mean_index p hi
  have hsub : ((n - i : ℕ) : ℝ) = n - i := by push_cast [hi]; ring
  unfold rwGrid
  have : ∀ j ∈ range (n + 1), rouwenhorst p n i j * (ψ * (j - n / 2)) =
      ψ * (rouwenhorst p n i j * j) - ψ * n / 2 * rouwenhorst p n i j := fun j _ => by ring
  rw [sum_congr rfl this, sum_sub_distrib, ← mul_sum, ← mul_sum, h1, h2, hsub]
  ring

/-- AKMM, p. 271: the stationary mean of the grid under the binomial law is `0`. -/
theorem rouwenhorst_stationary_mean (ψ : ℝ) (n : ℕ) :
    ∑ j ∈ range (n + 1), (n.choose j : ℝ) / 2 ^ n * rwGrid ψ n j = 0 := by
  obtain ⟨h0, h1, -⟩ := rw_binomial_moments n
  unfold rwGrid
  have : ∀ j ∈ range (n + 1), (n.choose j : ℝ) / 2 ^ n * (ψ * (j - n / 2)) =
      ψ / 2 ^ n * ((j : ℝ) * n.choose j) - ψ * n / 2 / 2 ^ n * (n.choose j : ℝ) :=
    fun j _ => by ring
  rw [sum_congr rfl this, sum_sub_distrib, ← mul_sum, ← mul_sum, h0, h1]
  field_simp
  ring

/-- AKMM, p. 271: the stationary variance of the grid under the binomial law is `ψ²n/4`. -/
theorem rouwenhorst_stationary_var (ψ : ℝ) (n : ℕ) :
    ∑ j ∈ range (n + 1), (n.choose j : ℝ) / 2 ^ n * rwGrid ψ n j ^ 2 = ψ ^ 2 * n / 4 := by
  obtain ⟨h0, h1, h2⟩ := rw_binomial_moments n
  unfold rwGrid
  have : ∀ j ∈ range (n + 1), (n.choose j : ℝ) / 2 ^ n * (ψ * (j - n / 2)) ^ 2 =
      ψ ^ 2 / 2 ^ n * ((j : ℝ) ^ 2 * n.choose j) - ψ ^ 2 * n / 2 ^ n * ((j : ℝ) * n.choose j) +
        ψ ^ 2 * n ^ 2 / 4 / 2 ^ n * (n.choose j : ℝ) := fun j _ => by ring
  rw [sum_congr rfl this, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← mul_sum,
    h0, h1, h2]
  field_simp
  ring

/-- AKMM, p. 271: the stationary first-order autocovariance is `(2p − 1)` times the variance. -/
theorem rouwenhorst_stationary_autocov (p ψ : ℝ) (n : ℕ) :
    ∑ i ∈ range (n + 1), (n.choose i : ℝ) / 2 ^ n * rwGrid ψ n i *
        ∑ j ∈ range (n + 1), rouwenhorst p n i j * rwGrid ψ n j =
      (2 * p - 1) * (ψ ^ 2 * n / 4) := by
  rw [← rouwenhorst_stationary_var ψ n, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [rouwenhorst_cond_mean p ψ (by simpa [Nat.lt_succ_iff] using hi)]
  ring

/-- AKMM, p. 271: "We can set `p` and `m` by `p = (1 + ρ)/2` and `m = √(N − 1)`. Then … the
unconditional mean and unconditional variance of the Markov chain are the same as those of the
original AR(1) process": with `N = n + 1 ≥ 2` states on the grid from `−mσ_z` to `mσ_z`, the
chain is stochastic, its invariant law is binomial with mean `0` and variance `σ_z²`, the
conditional mean is `ρz̄ᵢ`, and the first-order autocovariance is `ρσ_z²`. -/
theorem rouwenhorst_matches_ar1 {ρ σz : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {n : ℕ} (hn : 0 < n) :
    let p := (1 + ρ) / 2
    let ψ := 2 * √n * σz / n
    (∀ i j, 0 ≤ rouwenhorst p n i j) ∧
    (∀ i ≤ n, ∑ j ∈ range (n + 1), rouwenhorst p n i j = 1) ∧
    rwGrid ψ n 0 = -(√n * σz) ∧ rwGrid ψ n n = √n * σz ∧
    (∀ j, ∑ i ∈ range (n + 1), (n.choose i : ℝ) / 2 ^ n * rouwenhorst p n i j =
      (n.choose j : ℝ) / 2 ^ n) ∧
    ∑ j ∈ range (n + 1), (n.choose j : ℝ) / 2 ^ n * rwGrid ψ n j = 0 ∧
    ∑ j ∈ range (n + 1), (n.choose j : ℝ) / 2 ^ n * rwGrid ψ n j ^ 2 = σz ^ 2 ∧
    (∀ i ≤ n, ∑ j ∈ range (n + 1), rouwenhorst p n i j * rwGrid ψ n j = ρ * rwGrid ψ n i) ∧
    ∑ i ∈ range (n + 1), (n.choose i : ℝ) / 2 ^ n * rwGrid ψ n i *
        ∑ j ∈ range (n + 1), rouwenhorst p n i j * rwGrid ψ n j = ρ * σz ^ 2 := by
  intro p ψ
  have hp0 : 0 ≤ p := by simp only [p]; linarith
  have hp1 : p ≤ 1 := by simp only [p]; linarith
  have hρ : 2 * p - 1 = ρ := by simp only [p]; ring
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hvar : ψ ^ 2 * n / 4 = σz ^ 2 := by
    simp only [ψ]
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hn'.le]
    field_simp
    ring
  obtain ⟨he0, he1⟩ := rwGrid_ends hn (√n) σz
  refine ⟨rouwenhorst_nonneg hp0 hp1 n, fun i hi => rouwenhorst_row_sum p hi, he0, he1,
    rouwenhorst_invariant p n, rouwenhorst_stationary_mean ψ n, ?_, fun i hi => ?_, ?_⟩
  · rw [rouwenhorst_stationary_var, hvar]
  · rw [rouwenhorst_cond_mean p ψ hi, hρ]
  · rw [rouwenhorst_stationary_autocov, hvar, hρ]

/-- AKMM, p. 271, the recursion as printed: from the book's `Π_2` (`n = 1`), the weights of
`[0′ 0; Π 0]` and `[0 0′; 0 Π]` are `p` and `1 − p` (instead of `1 − p` and `p`). -/
noncomputable def rouwenhorstPrinted (p : ℝ) : ℕ → ℕ → ℕ → ℝ
  | 0 => fun i j => if i = 0 ∧ j = 0 then 1 else 0
  | 1 => fun i j => if 1 < i ∨ 1 < j then 0 else if i = j then p else 1 - p
  | n + 2 => fun i j =>
      if n + 2 < i then 0 else
      (p * rouwenhorstPrinted p (n + 1) i j
        + (1 - p) * (if j = 0 then 0 else rouwenhorstPrinted p (n + 1) i (j - 1))
        + p * (if i = 0 then 0 else rouwenhorstPrinted p (n + 1) (i - 1) j)
        + (1 - p) * (if i = 0 ∨ j = 0 then 0 else rouwenhorstPrinted p (n + 1) (i - 1) (j - 1)))
      / (if i = 0 ∨ i = n + 2 then 1 else 2)

/-- AKMM, p. 271: the printed recursion fails. For `N = 3` and `p = 3/4` (`ρ = 1/2`) its matrix
has rows `(9/16, 6/16, 1/16)`, `(3/8, 1/2, 1/8)`, `(3/16, 10/16, 3/16)`: the binomial law
`(1/4, 1/2, 1/4)` is not invariant (column `0` gives `3/8`), and from the top state `z̄ = 1` of
the grid `z̄_j = j − 1` the conditional mean is `0`, not `ρz̄ = 1/2`. The corrected recursion
has `(1/4, 1/2, 1/4)` invariant and conditional mean `ρz̄` (`rouwenhorst_invariant`,
`rouwenhorst_cond_mean`). -/
theorem rouwenhorst_printed_counterexample :
    ∑ i ∈ range 3, ((2 : ℕ).choose i : ℝ) / 2 ^ 2 * rouwenhorstPrinted (3 / 4) 2 i 0 = 3 / 8 ∧
      ((2 : ℕ).choose 0 : ℝ) / 2 ^ 2 = 1 / 4 ∧
      ∑ j ∈ range 3, rouwenhorstPrinted (3 / 4) 2 2 j * rwGrid 1 2 j = 0 ∧
      (2 * (3 / 4 : ℝ) - 1) * rwGrid 1 2 2 = 1 / 2 := by
  refine ⟨?_, by norm_num, ?_, ?_⟩
  · simp [sum_range_succ, rouwenhorstPrinted, Nat.choose]
    norm_num
  · simp [sum_range_succ, rouwenhorstPrinted, rwGrid]
    norm_num
  · simp [rwGrid]
    norm_num

end AKMM.ComputationalTools
