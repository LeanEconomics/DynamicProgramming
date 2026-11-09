/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Order.Field.Basic
import NumericalMethods.NISplines

/-!
# pp-form and B-splines (Miao, §11.3.2, pp. 361–362)

* `ni_ppForm_exists`: every polynomial piece of degree `< k` has a pp-form
  `pⱼ(x) = ∑ᵢ (x − xⱼ₋₁)^{k−i} cⱼᵢ` (Taylor expansion at the left break).
* `ni_bspline ξ j k`: de Boor's B-spline of order `k` for the knots `ξ` (the Cox–de Boor
  recursion; `ni_bspline_recursion` is the book's formula), with a monotone knot sequence:
  `ni_bspline_nonneg` (nonnegative), `ni_bspline_support` (zero outside `[ξⱼ, ξⱼ₊ₖ)`),
  `ni_bspline_piecewise_poly` (a polynomial of degree `≤ k − 1` on each knot interval).
* `ni_bookKnots_monotone`: the book's knot sequence `ξ₁ = ⋯ = ξₖ = x₀ < ⋯ < ξₖ₊ₙ = ⋯ = xₙ`
  (`ξₖ₊ᵢ = xᵢ`) is monotone, so the above apply to it.
* `ni_bspline_two`: the order-2 B-splines are the tent functions
  `(x − ξⱼ)/(ξⱼ₊₁ − ξⱼ)` on `[ξⱼ, ξⱼ₊₁)` and `(ξⱼ₊₂ − x)/(ξⱼ₊₂ − ξⱼ₊₁)` on `[ξⱼ₊₁, ξⱼ₊₂)`;
  `ni_bspline_two_book_formula_false`: the formula printed in the book has the two numerators
  swapped.
* `ni_bform_piecewise_poly`: a B-form `∑ⱼ Bⱼₖ aⱼ` is a polynomial of degree `≤ k − 1` on each
  knot interval.

de Boor's theorem that every spline has a unique B-form (Curry–Schoenberg) is cited, not proved
in the book, and is not formalised.
-/

open Polynomial

namespace Miao.NumericalMethods

/-- Miao, p. 361 (pp-form): a polynomial piece `p` of degree `< k` can be written as
`p(x) = ∑_{i=1}^{k} (x − a)^{k−i} cᵢ` (here with `cᵢ` indexed by `i = 0, …, k − 1`). -/
theorem ni_ppForm_exists (k : ℕ) (p : ℝ[X]) (hp : p.natDegree < k) (a : ℝ) :
    ∃ c : Fin k → ℝ, ∀ x, p.eval x = ∑ i : Fin k, (x - a) ^ (k - 1 - (i : ℕ)) * c i := by
  refine ⟨fun i => (taylor a p).coeff (k - 1 - i), fun x => ?_⟩
  have hdeg : (taylor a p).natDegree < k := by rwa [natDegree_taylor]
  have h1 : p.eval x = (taylor a p).eval (x - a) := by
    rw [taylor_eval]
    ring_nf
  rw [h1, eval_eq_sum_range' hdeg, ← Finset.sum_range_reflect (fun m => (taylor a p).coeff m *
    (x - a) ^ m) k, ← Fin.sum_univ_eq_sum_range (fun i => (taylor a p).coeff (k - 1 - i) *
    (x - a) ^ (k - 1 - i)) k]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- De Boor's B-splines, indexed by the degree `d = k − 1`: `ni_Bdeg ξ j 0 = 1_{[ξⱼ, ξⱼ₊₁)}` and
the Cox–de Boor recursion. -/
noncomputable def ni_Bdeg (ξ : ℕ → ℝ) : ℕ → ℕ → ℝ → ℝ
  | j, 0, x => if ξ j ≤ x ∧ x < ξ (j + 1) then 1 else 0
  | j, d + 1, x => (x - ξ j) / (ξ (j + d + 1) - ξ j) * ni_Bdeg ξ j d x +
      (ξ (j + d + 2) - x) / (ξ (j + d + 2) - ξ (j + 1)) * ni_Bdeg ξ (j + 1) d x

/-- The `j`th B-spline of order `k` for the knots `ξ` (Miao, p. 362). -/
noncomputable def ni_bspline (ξ : ℕ → ℝ) (j k : ℕ) (x : ℝ) : ℝ := ni_Bdeg ξ j (k - 1) x

/-- Miao, p. 362: `Bⱼ₁(x) = 1` if `x ∈ [ξⱼ, ξⱼ₊₁)` and `0` otherwise. -/
theorem ni_bspline_one (ξ : ℕ → ℝ) (j : ℕ) (x : ℝ) :
    ni_bspline ξ j 1 x = if ξ j ≤ x ∧ x < ξ (j + 1) then 1 else 0 := by
  simp [ni_bspline, ni_Bdeg]

/-- Miao, p. 362 (Cox–de Boor recursion): for `k ≥ 2`,
`Bⱼₖ(x) = (x − ξⱼ)/(ξⱼ₊ₖ₋₁ − ξⱼ) Bⱼ,ₖ₋₁(x) + (ξⱼ₊ₖ − x)/(ξⱼ₊ₖ − ξⱼ₊₁) Bⱼ₊₁,ₖ₋₁(x)`. -/
theorem ni_bspline_recursion (ξ : ℕ → ℝ) (j k : ℕ) (hk : 2 ≤ k) (x : ℝ) :
    ni_bspline ξ j k x = (x - ξ j) / (ξ (j + k - 1) - ξ j) * ni_bspline ξ j (k - 1) x +
      (ξ (j + k) - x) / (ξ (j + k) - ξ (j + 1)) * ni_bspline ξ (j + 1) (k - 1) x := by
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 2 := ⟨k - 2, by omega⟩
  simp only [ni_bspline, show d + 2 - 1 = d + 1 by omega, ni_Bdeg,
    show j + (d + 2) = j + d + 2 by omega, show j + d + 2 - 1 = j + d + 1 by omega,
    Nat.add_sub_cancel]

/-- Miao, p. 362: `Bⱼₖ` is zero outside `[ξⱼ, ξⱼ₊ₖ)` (monotone knots). -/
theorem ni_Bdeg_support {ξ : ℕ → ℝ} (hξ : Monotone ξ) :
    ∀ d j x, ¬ (ξ j ≤ x ∧ x < ξ (j + d + 1)) → ni_Bdeg ξ j d x = 0 := by
  intro d
  induction d with
  | zero =>
    intro j x hx
    simp only [ni_Bdeg]
    simp only [add_zero] at hx
    simp [hx]
  | succ d ih =>
    intro j x hx
    simp only [ni_Bdeg]
    have h1 : ni_Bdeg ξ j d x = 0 := by
      refine ih j x fun h => hx ⟨h.1, lt_of_lt_of_le h.2 (hξ (by omega))⟩
    have h2 : ni_Bdeg ξ (j + 1) d x = 0 := by
      refine ih (j + 1) x fun h => hx ⟨(hξ (by omega)).trans h.1, ?_⟩
      have : j + 1 + d + 1 = j + (d + 1) + 1 := by omega
      rw [← this]
      exact h.2
    rw [h1, h2]
    ring

/-- Miao, p. 362: `Bⱼₖ(x) = 0` outside the interval `[ξⱼ, ξⱼ₊ₖ)` (`k ≥ 1`, monotone knots). -/
theorem ni_bspline_support {ξ : ℕ → ℝ} (hξ : Monotone ξ) (j k : ℕ) (hk : 1 ≤ k) (x : ℝ)
    (hx : ¬ (ξ j ≤ x ∧ x < ξ (j + k))) : ni_bspline ξ j k x = 0 := by
  unfold ni_bspline
  refine ni_Bdeg_support hξ (k - 1) j x ?_
  rwa [show j + (k - 1) + 1 = j + k by omega]

/-- Miao, p. 362: `Bⱼₖ ≥ 0` (monotone knots). -/
theorem ni_Bdeg_nonneg {ξ : ℕ → ℝ} (hξ : Monotone ξ) : ∀ d j x, 0 ≤ ni_Bdeg ξ j d x := by
  intro d
  induction d with
  | zero =>
    intro j x
    simp only [ni_Bdeg]
    split_ifs <;> norm_num
  | succ d ih =>
    intro j x
    simp only [ni_Bdeg]
    refine add_nonneg ?_ ?_
    · by_cases h : ξ j ≤ x ∧ x < ξ (j + d + 1)
      · refine mul_nonneg (div_nonneg (by linarith [h.1]) ?_) (ih j x)
        linarith [hξ (show j ≤ j + d + 1 by omega)]
      · rw [ni_Bdeg_support hξ d j x h, mul_zero]
    · by_cases h : ξ (j + 1) ≤ x ∧ x < ξ (j + 1 + d + 1)
      · have e : j + 1 + d + 1 = j + d + 2 := by omega
        rw [e] at h
        refine mul_nonneg (div_nonneg (by linarith [h.2]) ?_) (ih (j + 1) x)
        linarith [hξ (show j + 1 ≤ j + d + 2 by omega)]
      · rw [ni_Bdeg_support hξ d (j + 1) x h, mul_zero]

/-- Miao, p. 362: `Bⱼₖ(x) ≥ 0` (monotone knots). -/
theorem ni_bspline_nonneg {ξ : ℕ → ℝ} (hξ : Monotone ξ) (j k : ℕ) (x : ℝ) :
    0 ≤ ni_bspline ξ j k x :=
  ni_Bdeg_nonneg hξ (k - 1) j x

/-- On a knot interval `[ξᵢ, ξᵢ₊₁)` the order-1 B-spline `Bⱼ₁` is the constant `δᵢⱼ`. -/
theorem ni_Bdeg_zero_on {ξ : ℕ → ℝ} (hξ : Monotone ξ) (i j : ℕ) {x : ℝ}
    (hx : ξ i ≤ x ∧ x < ξ (i + 1)) : ni_Bdeg ξ j 0 x = if i = j then 1 else 0 := by
  simp only [ni_Bdeg]
  split_ifs with h1 h2 h2
  · rfl
  · exfalso
    rcases lt_or_gt_of_ne h2 with h | h
    · have := hξ (show i + 1 ≤ j by omega)
      linarith [h1.1, hx.2]
    · have := hξ (show j + 1 ≤ i by omega)
      linarith [h1.2, hx.1]
  · subst h2
    exact absurd hx h1
  · rfl

/-- Miao, p. 362: `Bⱼₖ` is a piecewise polynomial of degree `k − 1`: on each knot interval
`[ξᵢ, ξᵢ₊₁)` it agrees with a polynomial of degree at most `k − 1` (monotone knots). -/
theorem ni_Bdeg_piecewise_poly {ξ : ℕ → ℝ} (hξ : Monotone ξ) (i : ℕ) :
    ∀ d j, ∃ p : ℝ[X], p.natDegree ≤ d ∧
      ∀ x, ξ i ≤ x ∧ x < ξ (i + 1) → ni_Bdeg ξ j d x = p.eval x := by
  intro d
  induction d with
  | zero =>
    intro j
    refine ⟨C (if i = j then 1 else 0), (natDegree_C _).le, fun x hx => ?_⟩
    rw [ni_Bdeg_zero_on hξ i j hx, eval_C]
  | succ d ih =>
    intro j
    obtain ⟨p₁, hp₁, hx₁⟩ := ih j
    obtain ⟨p₂, hp₂, hx₂⟩ := ih (j + 1)
    refine ⟨C (1 / (ξ (j + d + 1) - ξ j)) * (X - C (ξ j)) * p₁ +
      C (1 / (ξ (j + d + 2) - ξ (j + 1))) * (C (ξ (j + d + 2)) - X) * p₂, ?_, fun x hx => ?_⟩
    · have hlin1 : (C (1 / (ξ (j + d + 1) - ξ j)) * (X - C (ξ j))).natDegree ≤ 1 := by
        refine (natDegree_C_mul_le _ _).trans ?_
        exact (natDegree_sub_le _ _).trans (by simp)
      have hlin2 : (C (1 / (ξ (j + d + 2) - ξ (j + 1))) * (C (ξ (j + d + 2)) - X)).natDegree
          ≤ 1 := by
        refine (natDegree_C_mul_le _ _).trans ?_
        exact (natDegree_sub_le _ _).trans (by simp)
      refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine (natDegree_mul_le).trans ?_
        omega
      · refine (natDegree_mul_le).trans ?_
        omega
    · simp only [ni_Bdeg, hx₁ x hx, hx₂ x hx, eval_add, eval_mul, eval_C, eval_sub, eval_X]
      ring

/-- Miao, p. 362: `Bⱼₖ` is a piecewise polynomial of degree `≤ k − 1`. -/
theorem ni_bspline_piecewise_poly {ξ : ℕ → ℝ} (hξ : Monotone ξ) (i j k : ℕ) :
    ∃ p : ℝ[X], p.natDegree ≤ k - 1 ∧
      ∀ x, ξ i ≤ x ∧ x < ξ (i + 1) → ni_bspline ξ j k x = p.eval x :=
  ni_Bdeg_piecewise_poly hξ i (k - 1) j

/-- Miao, p. 362: the B-form `φ(x) = ∑ⱼ Bⱼₖ(x) aⱼ` is a polynomial of degree `≤ k − 1` on each
knot interval. -/
theorem ni_bform_piecewise_poly {ξ : ℕ → ℝ} (hξ : Monotone ξ) (k N i : ℕ) (a : ℕ → ℝ) :
    ∃ p : ℝ[X], p.natDegree ≤ k - 1 ∧ ∀ x, ξ i ≤ x ∧ x < ξ (i + 1) →
      ∑ j ∈ Finset.Icc 1 N, ni_bspline ξ j k x * a j = p.eval x := by
  choose p hp hx using fun j => ni_bspline_piecewise_poly hξ i j k
  refine ⟨∑ j ∈ Finset.Icc 1 N, p j * C (a j), ?_, fun x hxi => ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
    exact (natDegree_mul_le).trans (by simp [hp j])
  · rw [eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hx j x hxi, eval_mul, eval_C]

/-- The book's knot sequence (Miao, p. 362): `ξₘ = x_{min(m − k, n)}` (natural subtraction), i.e.
`ξ₁ = ⋯ = ξₖ = x₀`, `ξₖ₊ᵢ = xᵢ`, `ξₖ₊ₙ = ⋯ = ξₖ₊ₙ₊ₖ₋₁ = xₙ`. -/
def ni_bookKnots (k n : ℕ) (x : ℕ → ℝ) (m : ℕ) : ℝ := x (min (m - k) n)

/-- The book's knot sequence is monotone when the breaks are, so the B-spline properties
apply. -/
theorem ni_bookKnots_monotone {k n : ℕ} {x : ℕ → ℝ} (hx : Monotone x) :
    Monotone (ni_bookKnots k n x) := by
  intro a b hab
  exact hx (min_le_min_right n (Nat.sub_le_sub_right hab k))

/-- The book's knots satisfy `ξₖ₊ᵢ = xᵢ` for `i = 0, …, n`. -/
theorem ni_bookKnots_breaks (k n : ℕ) (x : ℕ → ℝ) (i : ℕ) (hi : i ≤ n) :
    ni_bookKnots k n x (k + i) = x i := by
  simp [ni_bookKnots, hi]

/-- Miao, p. 362 (tent functions): the order-2 B-spline is `(x − ξⱼ)/(ξⱼ₊₁ − ξⱼ)` on
`[ξⱼ, ξⱼ₊₁)`, `(ξⱼ₊₂ − x)/(ξⱼ₊₂ − ξⱼ₊₁)` on `[ξⱼ₊₁, ξⱼ₊₂)` and `0` otherwise. -/
theorem ni_bspline_two (ξ : ℕ → ℝ) (j : ℕ) (x : ℝ) :
    ni_bspline ξ j 2 x =
      if ξ j ≤ x ∧ x < ξ (j + 1) then (x - ξ j) / (ξ (j + 1) - ξ j)
      else if ξ (j + 1) ≤ x ∧ x < ξ (j + 2) then (ξ (j + 2) - x) / (ξ (j + 2) - ξ (j + 1))
      else 0 := by
  simp only [ni_bspline, Nat.reduceSub, ni_Bdeg, add_zero, show j + 1 + 1 = j + 2 by omega]
  by_cases hA : ξ j ≤ x ∧ x < ξ (j + 1)
  · have hB : ¬ (ξ (j + 1) ≤ x ∧ x < ξ (j + 2)) := fun h => by linarith [hA.2, h.1]
    simp [hA, hB]
  · by_cases hB : ξ (j + 1) ≤ x ∧ x < ξ (j + 2)
    · simp [hA, hB]
    · simp [hA, hB]

/-- Miao, p. 362 (correction): the order-2 formula printed in the book,
`(ξⱼ₊₁ − x)/(ξⱼ₊₁ − ξⱼ)` on `[ξⱼ, ξⱼ₊₁]`, is wrong: for the knots `ξₘ = m`, `j = 0`, `x = 1/4`
it gives `3/4`, while `B₀₂(1/4) = 1/4`. -/
theorem ni_bspline_two_book_formula_false :
    ni_bspline (fun m => (m : ℝ)) 0 2 (1 / 4) = 1 / 4 ∧
      ((((0 + 1 : ℕ) : ℝ) - 1 / 4) / (((0 + 1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ)) : ℝ) = 3 / 4 := by
  refine ⟨?_, by norm_num⟩
  rw [ni_bspline_two]
  norm_num

end Miao.NumericalMethods
