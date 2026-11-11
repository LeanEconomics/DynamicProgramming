/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Topology.Algebra.Polynomial
import NumericalMethods.NIWeighted

/-!
# Legendre polynomials (Miao, §11.3.1, p. 357)

The `n`th Legendre polynomial is given by Rodrigues' formula
`Pₙ(x) = ((−1)ⁿ / (2ⁿ n!)) dⁿ/dxⁿ (1 − x²)ⁿ`, `P₀ = 1`, on `[−1, 1]`, with weighting function
`w = 1`.

* `ni_legendre n`: the polynomial `((−1)ⁿ / (2ⁿ n!)) Dⁿ (1 − X²)ⁿ`;
  `ni_legendre_eval_eq_iteratedDeriv` shows it evaluates to the book's function.
* `ni_legendre_zero`: `P₀ = 1`; `ni_legendre_natDegree_le`: `deg Pₙ ≤ n`.
* `ni_legendre_orthogonal_low`: `∫_{−1}^{1} q Pₙ = 0` for every polynomial `q` of degree `< n`
  (Rodrigues' formula and `n` integrations by parts).
* `ni_legendre_orthogonal`: the Legendre polynomials are mutually orthogonal with respect to the
  weighting function `w = 1` on `(−1, 1)` (Definition 11.3.1).
* `ni_affine_maps_Icc`, `ni_legendre_shifted_orthogonal`: the transformation
  `z = 2(x − a)/(b − a) − 1` maps `[a, b]` onto `[−1, 1]`, and the transformed Legendre
  polynomials are orthogonal on `(a, b)`.
-/

open Polynomial MeasureTheory

namespace Miao.NumericalMethods

/-- Polynomial derivatives agree with derivatives of the polynomial function. -/
theorem ni_iteratedDeriv_eval (p : ℝ[X]) (k : ℕ) :
    iteratedDeriv k (fun x => p.eval x) = fun x => (derivative^[k] p).eval x := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ']
    have : deriv (fun x => p.eval x) = fun x => (derivative p).eval x := by
      funext x
      exact Polynomial.deriv p
    rw [this, ih, Function.iterate_succ_apply]

/-- Integration by parts for polynomials on `[a, b]`. -/
theorem ni_poly_parts (p t : ℝ[X]) (a b : ℝ) :
    ∫ x in a..b, p.eval x * (derivative t).eval x =
      p.eval b * t.eval b - p.eval a * t.eval a - ∫ x in a..b, (derivative p).eval x * t.eval x :=
  intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun x _ => Polynomial.hasDerivAt p x)
    (fun x _ => Polynomial.hasDerivAt t x)
    ((Polynomial.continuous _).intervalIntegrable _ _)
    ((Polynomial.continuous _).intervalIntegrable _ _)

/-- The Rodrigues generator `(1 − X²)ⁿ`. -/
noncomputable def ni_legendreGen (n : ℕ) : ℝ[X] := (1 - X ^ 2) ^ n

/-- The `n`th Legendre polynomial `Pₙ = ((−1)ⁿ/(2ⁿ n!)) Dⁿ (1 − X²)ⁿ` (Miao, p. 357). -/
noncomputable def ni_legendre (n : ℕ) : ℝ[X] :=
  C ((-1 : ℝ) ^ n / (2 ^ n * n.factorial)) * derivative^[n] (ni_legendreGen n)

/-- Miao, p. 357 (Rodrigues' formula): `Pₙ(x) = ((−1)ⁿ/(2ⁿ n!)) dⁿ/dxⁿ (1 − x²)ⁿ`. -/
theorem ni_legendre_eval_eq_iteratedDeriv (n : ℕ) (x : ℝ) :
    (ni_legendre n).eval x =
      (-1) ^ n / (2 ^ n * n.factorial) * iteratedDeriv n (fun y => (1 - y ^ 2) ^ n) x := by
  have : (fun y : ℝ => (1 - y ^ 2) ^ n) = fun y => (ni_legendreGen n).eval y := by
    funext y
    simp [ni_legendreGen]
  rw [this, ni_iteratedDeriv_eval]
  simp [ni_legendre]

/-- Miao, p. 357: `P₀(x) = 1`. -/
theorem ni_legendre_zero : ni_legendre 0 = 1 := by
  simp [ni_legendre, ni_legendreGen]

/-- The Legendre polynomial `Pₙ` has degree at most `n`. -/
theorem ni_legendre_natDegree_le (n : ℕ) : (ni_legendre n).natDegree ≤ n := by
  unfold ni_legendre
  refine (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_iterate_derivative _ _).trans ?_
  have h1 : (1 - X ^ 2 : ℝ[X]).natDegree ≤ 2 :=
    (natDegree_sub_le (1 : ℝ[X]) (X ^ 2)).trans (by simp)
  have h : (ni_legendreGen n).natDegree ≤ n * 2 :=
    natDegree_pow_le.trans (Nat.mul_le_mul_left _ h1)
  omega

/-- `±1` are roots of multiplicity `≥ n` of `(1 − X²)ⁿ`: the derivatives of order `< n` vanish
there. -/
theorem ni_legendreGen_iterate_root (n l : ℕ) (hl : l < n) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    (derivative^[l] (ni_legendreGen n)).eval s = 0 := by
  have hne : ni_legendreGen n ≠ 0 := by
    unfold ni_legendreGen
    refine pow_ne_zero _ fun h => ?_
    have := congrArg (Polynomial.eval 0) h
    simp at this
  have hdvd : (X - C s) ^ n ∣ ni_legendreGen n := by
    unfold ni_legendreGen
    refine pow_dvd_pow_of_dvd ?_ n
    rcases hs with rfl | rfl
    · exact ⟨-(X + 1 : ℝ[X]), by simp only [map_one]; ring⟩
    · exact ⟨(1 - X : ℝ[X]), by simp only [map_neg, map_one]; ring⟩
  have hmult : n ≤ (ni_legendreGen n).rootMultiplicity s :=
    (le_rootMultiplicity_iff hne).mpr hdvd
  exact isRoot_iterate_derivative_of_lt_rootMultiplicity (by omega)

/-- Repeated integration by parts: `∫_{−1}^{1} q · Dᵐ(1 − X²)ⁿ = (−1)ᵐ ∫_{−1}^{1} Dᵐq · (1 − X²)ⁿ`
for `m ≤ n`. -/
theorem ni_legendre_parts (n : ℕ) : ∀ m ≤ n, ∀ q : ℝ[X],
    ∫ x in (-1 : ℝ)..1, q.eval x * (derivative^[m] (ni_legendreGen n)).eval x =
      (-1) ^ m * ∫ x in (-1 : ℝ)..1, (derivative^[m] q).eval x * (ni_legendreGen n).eval x := by
  intro m
  induction m with
  | zero => intro _ q; simp
  | succ m ih =>
    intro hm q
    rw [Function.iterate_succ_apply', ni_poly_parts,
      ni_legendreGen_iterate_root n m (by omega) 1 (Or.inl rfl),
      ni_legendreGen_iterate_root n m (by omega) (-1) (Or.inr rfl), ih (by omega),
      Function.iterate_succ_apply]
    ring

/-- Miao, p. 357: `∫_{−1}^{1} q(x) Pₙ(x) dx = 0` for every polynomial `q` of degree `< n`. -/
theorem ni_legendre_orthogonal_low (n : ℕ) (q : ℝ[X]) (hq : q.natDegree < n) :
    ∫ x in (-1 : ℝ)..1, q.eval x * (ni_legendre n).eval x = 0 := by
  have e : ∀ x, q.eval x * (ni_legendre n).eval x =
      (-1) ^ n / (2 ^ n * n.factorial) *
        (q.eval x * (derivative^[n] (ni_legendreGen n)).eval x) := by
    intro x
    simp only [ni_legendre, eval_mul, eval_C]
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, ni_legendre_parts n n le_rfl,
    iterate_derivative_eq_zero hq]
  simp

/-- **Definition 11.3.1** applied to the Legendre polynomials (Miao, p. 357): `Pᵢ` and `Pⱼ` are
orthogonal with respect to the weighting function `w = 1` on `[−1, 1]` for `i ≠ j`. -/
theorem ni_legendre_orthogonal :
    ni_Orthogonal (fun _ => 1) (Set.Ioo (-1) 1) (fun n x => (ni_legendre n).eval x) := by
  have key : ∀ i j : ℕ, i < j →
      ∫ x in (-1 : ℝ)..1, (ni_legendre i).eval x * (ni_legendre j).eval x = 0 :=
    fun i j hij => ni_legendre_orthogonal_low j _ ((ni_legendre_natDegree_le i).trans_lt hij)
  intro i j hij
  unfold ni_inner
  simp only [mul_one]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num)]
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · rw [← key j i h]
    congr 1
    funext x
    ring

/-- Miao, p. 357: the transformation `z = 2(x − a)/(b − a) − 1` maps `[a, b]` onto `[−1, 1]`
(bijectively, with inverse `x = a + (z + 1)(b − a)/2`). -/
theorem ni_affine_maps_Icc {a b : ℝ} (hab : a < b) :
    Set.BijOn (fun x => 2 * (x - a) / (b - a) - 1) (Set.Icc a b) (Set.Icc (-1) 1) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  refine ⟨fun x hx => ?_, fun x _ y _ hxy => ?_, fun z hz => ?_⟩
  · obtain ⟨h1, h2⟩ := hx
    constructor
    · have : 0 ≤ 2 * (x - a) / (b - a) := div_nonneg (by linarith) hba.le
      linarith
    · have : 2 * (x - a) / (b - a) ≤ 2 := by
        rw [div_le_iff₀ hba]; linarith
      linarith
  · have : 2 * (x - a) / (b - a) = 2 * (y - a) / (b - a) := by linarith [hxy]
    field_simp at this
    linarith
  · obtain ⟨h1, h2⟩ := hz
    refine ⟨a + (z + 1) * (b - a) / 2, ⟨?_, ?_⟩, ?_⟩
    · nlinarith
    · nlinarith
    · simp only
      field_simp
      ring

/-- Miao, p. 357: the transformed Legendre polynomials `Pₙ(2(x − a)/(b − a) − 1)` are mutually
orthogonal on `(a, b)` with weight `1`. -/
theorem ni_legendre_shifted_orthogonal {a b : ℝ} (hab : a < b) :
    ni_Orthogonal (fun _ => 1) (Set.Ioo a b)
      (fun n x => (ni_legendre n).eval (2 * (x - a) / (b - a) - 1)) := by
  intro i j hij
  have h := ni_legendre_orthogonal i j hij
  unfold ni_inner at h ⊢
  simp only [mul_one] at h ⊢
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num)] at h
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab.le]
  have hba : b - a ≠ 0 := (sub_pos.mpr hab).ne'
  have e : ∀ x, 2 * (x - a) / (b - a) - 1 = 2 / (b - a) * x + (-(2 * a) / (b - a) - 1) := by
    intro x; field_simp; ring
  simp_rw [e]
  rw [intervalIntegral.integral_comp_mul_add
    (fun z => (ni_legendre i).eval z * (ni_legendre j).eval z) (by positivity)]
  have e1 : 2 / (b - a) * a + (-(2 * a) / (b - a) - 1) = -1 := by field_simp; ring
  have e2 : 2 / (b - a) * b + (-(2 * a) / (b - a) - 1) = 1 := by field_simp; ring
  rw [e1, e2, h, smul_zero]

end Miao.NumericalMethods
