import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ChebyshevGauss
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Order.Monotone.Basic
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Gaussian quadrature (Miao, §11.1, pp. 347–350)

Miao, *Economic Dynamics in Discrete Time*, §11.1 "Numerical Integration". A quadrature rule
with nodes `xᵢ` and weights `wᵢ` approximates `∫ f(x) w(x) dx` by `∑ wᵢ f(xᵢ)` (`nqQuad`).
An `n`-point Gaussian rule for the weight `ω` (and a measure `μ`, Lebesgue measure on the domain
in the book) satisfies the `2n` moment conditions of p. 348 (`nqIsGaussRule`).

* `nq_quad_exact_of_moments`, `nq_gauss_exact`: a rule matching the moments of order `< m`
  integrates every polynomial of degree `< m` exactly; a Gaussian rule is exact for polynomials
  of degree `≤ 2n − 1` (p. 348: "if `f` can be approximated by polynomials accurately ...").
* `nq_gauss_not_exact_two_mul`: no `n`-point rule is exact for all polynomials of degree `2n`
  (Gauss–Legendre weight), so `2n` is the largest number of moment conditions `n` nodes can meet.
* `nq_gauss_weights_nonneg`, `nq_gauss_probability`: the weights of a Gaussian rule with distinct
  nodes and nonnegative weight function are nonnegative; when `ω` is a density they sum to one,
  which is the book's interpretation "mass points `xᵢ` and probabilities `wᵢ`" (p. 348).
* Gauss–Legendre (p. 349): `nq_legendre_change_of_variables` (the change of variables to
  `[a, b]`, an exact identity), `nq_legendre_interval_exact` (the transformed rule is exact on
  `[a, b]` for degree `≤ 2n − 1`), and the concrete rules `nq_legendre_one_point`,
  `nq_legendre_two_point` (nodes `±1/√3`).
* Gauss–Laguerre (p. 349): `nq_laguerre_present_value`, the change of variables for present
  values, an exact identity.
* Product rules (§11.1.2, p. 350): `nq_prodQuad_prod`, `nq_prod_gauss_exact` (the product of
  one-dimensional Gaussian rules integrates `∏ⱼ pⱼ(xⱼ)` exactly against `W(x) = ∏ⱼ wⱼ(xⱼ)`),
  `nq_prodQuad_card` (the number of nodes is `∏ⱼ nⱼ`: the curse of dimensionality).

**Departures.** The book writes "≃" for the quadrature approximation; we prove exactness on the
polynomial classes where the rules are exact and exact change-of-variables identities.
Integrals are Bochner integrals with respect to a measure `μ` (for the interval rules
`volume.restrict (Set.Ioc (-1) 1)` or `volume.restrict (Set.Icc a b)`). Computing nodes and
weights (the CompEcon toolbox) and Newton–Cotes rules (only named) are not formalised.
-/

namespace Miao.NumericalMethods

open MeasureTheory Polynomial

/-- Miao, p. 348: the quadrature sum `∑ᵢ wᵢ f(xᵢ)` with nodes `x` and weights `w`. -/
noncomputable def nqQuad {n : ℕ} (w x : Fin n → ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ i, w i * f (x i)

/-- Miao, p. 348: the `2n` conditions `∫ xᵏ ω(x) dx = ∑ᵢ wᵢ xᵢᵏ`, `k = 0, …, 2n − 1`, defining
an `n`-point Gaussian rule for the weight function `ω` (integrals with respect to `μ`); each
moment is required to exist. -/
def nqIsGaussRule (μ : Measure ℝ) (ω : ℝ → ℝ) {n : ℕ} (w x : Fin n → ℝ) : Prop :=
  ∀ k < 2 * n, Integrable (fun y => y ^ k * ω y) μ ∧
    ∫ y, y ^ k * ω y ∂μ = nqQuad w x (fun y => y ^ k)

/-- Miao, p. 348: a rule matching the moments `∫ yᵏ ω(y) dμ` of order `k < m` integrates every
polynomial of degree `< m` exactly against `ω`. -/
theorem nq_quad_exact_of_moments {μ : Measure ℝ} {ω : ℝ → ℝ} {n m : ℕ} {w x : Fin n → ℝ}
    (hI : ∀ k < m, Integrable (fun y => y ^ k * ω y) μ)
    (hM : ∀ k < m, ∫ y, y ^ k * ω y ∂μ = nqQuad w x (fun y => y ^ k))
    {p : ℝ[X]} (hp : p.natDegree < m) :
    ∫ y, p.eval y * ω y ∂μ = nqQuad w x p.eval := by
  have hsum : ∀ y, p.eval y * ω y =
      ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * (y ^ k * ω y) := by
    intro y
    rw [eval_eq_sum_range, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp_rw [hsum]
  rw [integral_finsetSum _ (fun k hk => ((hI k (by
      have := Finset.mem_range.mp hk; omega)).const_mul _))]
  simp_rw [integral_const_mul]
  have h2 : ∀ k ∈ Finset.range (p.natDegree + 1),
      p.coeff k * ∫ y, y ^ k * ω y ∂μ = p.coeff k * nqQuad w x (fun y => y ^ k) := by
    intro k hk
    rw [hM k (by have := Finset.mem_range.mp hk; omega)]
  rw [Finset.sum_congr rfl h2]
  unfold nqQuad
  simp_rw [eval_eq_sum_range (p := p), Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

/-- Miao, p. 348: an `n`-point Gaussian rule integrates every polynomial of degree `≤ 2n − 1`
exactly: `∫ p(x) ω(x) dx = ∑ᵢ wᵢ p(xᵢ)`. -/
theorem nq_gauss_exact {μ : Measure ℝ} {ω : ℝ → ℝ} {n : ℕ} {w x : Fin n → ℝ}
    (hG : nqIsGaussRule μ ω w x) {p : ℝ[X]} (hp : p.natDegree < 2 * n) :
    ∫ y, p.eval y * ω y ∂μ = nqQuad w x p.eval :=
  nq_quad_exact_of_moments (fun k hk => (hG k hk).1) (fun k hk => (hG k hk).2) hp

/-- Miao, p. 348 (optimality of the `2n` conditions): for the Gauss–Legendre weight on
`[a, b]`, no `n`-point rule is exact for all polynomials of degree `2n`; the witness is
`∏ᵢ (X − xᵢ)²`, whose integral is positive while the quadrature sum vanishes. -/
theorem nq_gauss_not_exact_two_mul {a b : ℝ} (hab : a < b) {n : ℕ} (w x : Fin n → ℝ) :
    ∃ p : ℝ[X], p.natDegree = 2 * n ∧
      ∫ y in Set.Icc a b, p.eval y ≠ nqQuad w x p.eval := by
  classical
  refine ⟨∏ i, (X - C (x i)) ^ 2, ?_, ?_⟩
  · rw [natDegree_prod_of_monic _ _ (fun i _ => (monic_X_sub_C (x i)).pow 2)]
    simp [natDegree_pow, mul_comm]
  · have hq : nqQuad w x (∏ i, (X - C (x i)) ^ 2).eval = 0 := by
      unfold nqQuad
      refine Finset.sum_eq_zero fun j _ => ?_
      change w j * (∏ i, (X - C (x i)) ^ 2).eval (x j) = 0
      rw [eval_prod, Finset.prod_eq_zero (Finset.mem_univ j) (by simp), mul_zero]
    rw [hq]
    refine ne_of_gt ?_
    set q : ℝ[X] := ∏ i, (X - C (x i)) ^ 2
    have hev : ∀ y, q.eval y = ∏ i, (y - x i) ^ 2 := fun y => by simp [q, eval_prod]
    have hnn : 0 ≤ fun y => q.eval y := fun y => by
      change 0 ≤ q.eval y
      rw [hev]; exact Finset.prod_nonneg fun i _ => sq_nonneg _
    have hint : Integrable (fun y => q.eval y) (volume.restrict (Set.Icc a b)) :=
      (q.continuous.integrableOn_Icc)
    rw [integral_pos_iff_support_of_nonneg hnn hint]
    have hsupp : Set.Icc a b \ Set.range x ⊆ Function.support (fun y => q.eval y) := by
      intro y hy
      rw [Function.mem_support, hev]
      refine Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero 2 (sub_ne_zero.mpr ?_)
      intro h
      exact hy.2 ⟨i, h.symm⟩
    have hmeas : MeasurableSet (Function.support (fun y => q.eval y)) :=
      q.continuous.isOpen_support.measurableSet
    rw [Measure.restrict_apply hmeas]
    have h0 : volume (Set.range x) = 0 := (Set.finite_range x).measure_zero _
    calc (0 : ENNReal) < volume (Set.Icc a b) := by
            rw [Real.volume_Icc]; exact ENNReal.ofReal_pos.mpr (by linarith)
      _ = volume (Set.Icc a b \ Set.range x) := (measure_sdiff_null h0).symm
      _ ≤ volume (Function.support (fun y => q.eval y) ∩ Set.Icc a b) :=
          measure_mono fun y hy => ⟨hsupp hy, hy.1⟩

/-- Miao, p. 348: the weights of a Gaussian rule with distinct nodes and a nonnegative weight
function are nonnegative: `wᵢ = ∫ ℓᵢ(x)² ω(x) dx ≥ 0`, with `ℓᵢ` the Lagrange basis polynomial
of degree `n − 1 ≤ 2n − 1`. -/
theorem nq_gauss_weights_nonneg {μ : Measure ℝ} {ω : ℝ → ℝ} {n : ℕ} {w x : Fin n → ℝ}
    (hG : nqIsGaussRule μ ω w x) (hx : Function.Injective x) (hω : ∀ y, 0 ≤ ω y)
    (i : Fin n) : 0 ≤ w i := by
  classical
  set L := Lagrange.basis Finset.univ x i
  have hinj : Set.InjOn x (Finset.univ : Finset (Fin n)) := hx.injOn
  have hdeg : (L ^ 2).natDegree < 2 * n := by
    have h1 := Lagrange.natDegree_basis hinj (Finset.mem_univ i)
    rw [Finset.card_univ, Fintype.card_fin] at h1
    calc (L ^ 2).natDegree ≤ 2 * L.natDegree := natDegree_pow_le
      _ < 2 * n := by
          change 2 * (Lagrange.basis Finset.univ x i).natDegree < 2 * n
          rw [h1]; have := i.2; omega
  have hex := nq_gauss_exact hG hdeg
  have hsum : nqQuad w x (L ^ 2).eval = w i := by
    unfold nqQuad
    rw [Finset.sum_eq_single i]
    · simp [L, Lagrange.eval_basis_self hinj (Finset.mem_univ i)]
    · intro j _ hji
      simp [L, Lagrange.eval_basis_of_ne hji.symm (Finset.mem_univ j)]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [← hsum, ← hex]
  exact integral_nonneg fun y => mul_nonneg (by rw [eval_pow]; positivity) (hω y)

/-- Miao, p. 348: when the weight function is a density (`∫ ω dμ = 1`, `ω ≥ 0`), a Gaussian
rule with distinct nodes is a discrete distribution: the weights are probabilities (nonnegative,
summing to one) and the discrete distribution matches the moments of order `≤ 2n − 1`. -/
theorem nq_gauss_probability {μ : Measure ℝ} {ω : ℝ → ℝ} {n : ℕ} {w x : Fin n → ℝ}
    (hG : nqIsGaussRule μ ω w x) (hx : Function.Injective x) (hω : ∀ y, 0 ≤ ω y)
    (hω1 : ∫ y, ω y ∂μ = 1) (hn : 0 < n) :
    (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      ∀ k < 2 * n, ∑ i, w i * x i ^ k = ∫ y, y ^ k * ω y ∂μ := by
  refine ⟨nq_gauss_weights_nonneg hG hx hω, ?_, fun k hk => ((hG k hk).2).symm⟩
  have h0 := (hG 0 (by omega)).2
  simp only [pow_zero, one_mul] at h0
  rw [hω1] at h0
  rw [h0]
  simp [nqQuad]

/-- Miao, p. 349 (Gauss–Legendre, change of variables): for `a ≠ b`,
`∫ₐᵇ f(x) dx = (b − a)/2 · ∫₋₁¹ f((t + 1)(b − a)/2 + a) dt`. -/
theorem nq_legendre_change_of_variables {a b : ℝ} (hab : a ≠ b) (f : ℝ → ℝ) :
    ∫ y in a..b, f y = (b - a) / 2 * ∫ t in (-1 : ℝ)..1, f ((t + 1) * (b - a) / 2 + a) := by
  have hc : (b - a) / 2 ≠ 0 := by
    intro h; apply hab; linarith
  have hfun : (fun t => f ((t + 1) * (b - a) / 2 + a)) =
      fun t => f ((b - a) / 2 * t + (a + b) / 2) := by
    funext t; congr 1; ring
  rw [hfun, intervalIntegral.integral_comp_mul_add (fun y => f y) hc]
  have h1 : (b - a) / 2 * -1 + (a + b) / 2 = a := by ring
  have h2 : (b - a) / 2 * 1 + (a + b) / 2 = b := by ring
  rw [h1, h2, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

/-- Miao, p. 349 (Gauss–Legendre on `[a, b]`): an `n`-point Gauss–Legendre rule on `[−1, 1]`,
transformed by the change of variables, integrates every polynomial of degree `≤ 2n − 1` exactly
on `[a, b]`: `∫ₐᵇ p = (b − a)/2 · ∑ᵢ wᵢ p((xᵢ + 1)(b − a)/2 + a)`. -/
theorem nq_legendre_interval_exact {n : ℕ} {w x : Fin n → ℝ}
    (hG : nqIsGaussRule (volume.restrict (Set.Ioc (-1) 1)) (fun _ => 1) w x) {a b : ℝ}
    (hab : a ≠ b) {p : ℝ[X]} (hp : p.natDegree < 2 * n) :
    ∫ y in a..b, p.eval y = (b - a) / 2 * ∑ i, w i * p.eval ((x i + 1) * (b - a) / 2 + a) := by
  set q : ℝ[X] := p.comp (C ((b - a) / 2) * X + C ((a + b) / 2))
  have hq : ∀ t, q.eval t = p.eval ((t + 1) * (b - a) / 2 + a) := by
    intro t
    simp only [q, eval_comp, eval_add, eval_mul, eval_C, eval_X]
    congr 1; ring
  have hqd : q.natDegree < 2 * n :=
    lt_of_le_of_lt (natDegree_comp_le.trans (by
      calc p.natDegree * (C ((b - a) / 2) * X + C ((a + b) / 2)).natDegree
          ≤ p.natDegree * 1 := Nat.mul_le_mul_left _ natDegree_linear_le
        _ = p.natDegree := mul_one _)) hp
  have hex := nq_gauss_exact hG hqd
  rw [nq_legendre_change_of_variables hab]
  congr 1
  rw [intervalIntegral.integral_of_le (by norm_num)]
  simp_rw [← hq]
  simpa [nqQuad, hq] using hex

/-- Miao, p. 349 (Gauss–Legendre, `n = 1`): the node `0` with weight `2` is the one-point
Gauss–Legendre rule on `[−1, 1]`. -/
theorem nq_legendre_one_point :
    nqIsGaussRule (volume.restrict (Set.Ioc (-1) 1)) (fun _ => 1)
      (fun _ : Fin 1 => (2 : ℝ)) (fun _ => 0) := by
  intro k hk
  refine ⟨((continuous_pow k).mul continuous_const).integrableOn_Ioc, ?_⟩
  rw [← intervalIntegral.integral_of_le (by norm_num)]
  simp only [mul_one, integral_pow]
  interval_cases k <;> norm_num [nqQuad]

/-- Miao, p. 349 (Gauss–Legendre, `n = 2`): the nodes `∓1/√3` with weights `1, 1` form the
two-point Gauss–Legendre rule on `[−1, 1]`. -/
theorem nq_legendre_two_point :
    nqIsGaussRule (volume.restrict (Set.Ioc (-1) 1)) (fun _ => 1)
      (fun _ : Fin 2 => (1 : ℝ)) ![-(1 / Real.sqrt 3), 1 / Real.sqrt 3] := by
  intro k hk
  refine ⟨((continuous_pow k).mul continuous_const).integrableOn_Ioc, ?_⟩
  rw [← intervalIntegral.integral_of_le (by norm_num)]
  simp only [mul_one, integral_pow]
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : Real.sqrt 3 ≠ 0 := by positivity
  interval_cases k
  · norm_num [nqQuad]
  · norm_num [nqQuad]
  · simp only [nqQuad, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    field_simp
    rw [h3]; norm_num
  · simp only [nqQuad, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    ring_nf

/-- Translation of an integral over a half-line: `∫_{(0,∞)} F(u + a) du = ∫_{(a,∞)} F(y) dy`. -/
theorem nq_integral_Ioi_shift (F : ℝ → ℝ) (a : ℝ) :
    ∫ u in Set.Ioi 0, F (u + a) = ∫ y in Set.Ioi a, F y := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_add_right_eq_self (fun y => (Set.Ioi a).indicator F y) a]
  congr 1
  funext u
  simp only [Set.indicator, Set.mem_Ioi]
  by_cases h : 0 < u
  · have h' : a < u + a := by linarith
    simp only [h, h', ↓reduceIte]
  · have h' : ¬ a < u + a := by linarith
    simp only [h, h', ↓reduceIte]

/-- Miao, p. 349 (Gauss–Laguerre, present values): for `r > 0`,
`∫ₐ^∞ e^{−ry} f(y) dy = e^{−ra}/r · ∫₀^∞ e^{−x} f(x/r + a) dx`, the change of variables that
turns a present value into a Gauss–Laguerre integral. -/
theorem nq_laguerre_present_value {r : ℝ} (hr : 0 < r) (a : ℝ) (f : ℝ → ℝ) :
    ∫ y in Set.Ioi a, Real.exp (-r * y) * f y =
      Real.exp (-r * a) / r * ∫ x in Set.Ioi 0, Real.exp (-x) * f (x / r + a) := by
  have h1 := integral_comp_mul_left_Ioi (fun x => Real.exp (-x) * f (x / r + a)) 0 hr
  rw [mul_zero] at h1
  have h2 : ∫ x in Set.Ioi 0, Real.exp (-x) * f (x / r + a) =
      r * ∫ u in Set.Ioi 0, Real.exp (-r * (u + a - a)) * f (u + a) := by
    have h1' : ∫ x in Set.Ioi 0, Real.exp (-x) * f (x / r + a) =
        r * ∫ x in Set.Ioi 0, Real.exp (-(r * x)) * f (r * x / r + a) := by
      rw [h1, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
    rw [h1']
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    congr 2
    · ring
    · field_simp
  rw [h2, nq_integral_Ioi_shift (fun y => Real.exp (-r * (y - a)) * f y) a,
    ← mul_assoc, div_mul_cancel₀ _ hr.ne', ← integral_const_mul]
  congr 1
  funext y
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Miao, p. 350: the product rule
`∑_{i₁} ⋯ ∑_{i_d} w¹_{i₁} ⋯ w^d_{i_d} F(x¹_{i₁}, …, x^d_{i_d})` built from one-dimensional rules
`(xʲ, wʲ)` with `nⱼ` points in dimension `j`. -/
noncomputable def nqProdQuad {d : ℕ} {n : Fin d → ℕ} (w x : (j : Fin d) → Fin (n j) → ℝ)
    (F : (Fin d → ℝ) → ℝ) : ℝ :=
  ∑ i : (j : Fin d) → Fin (n j), (∏ j, w j (i j)) * F (fun j => x j (i j))

/-- Miao, p. 350: on a product `F(x) = ∏ⱼ fⱼ(xⱼ)` the product rule is the product of the
one-dimensional quadrature sums. -/
theorem nq_prodQuad_prod {d : ℕ} {n : Fin d → ℕ} (w x : (j : Fin d) → Fin (n j) → ℝ)
    (f : Fin d → ℝ → ℝ) :
    nqProdQuad w x (fun y => ∏ j, f j (y j)) = ∏ j, nqQuad (w j) (x j) (f j) := by
  unfold nqProdQuad nqQuad
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun i _ => (Finset.prod_mul_distrib).symm

/-- Miao, p. 350 (multidimensional Gaussian quadrature): if `(xʲ, wʲ)` is an `nⱼ`-point Gaussian
rule for the weight `ωⱼ` in dimension `j`, the product rule integrates `∏ⱼ pⱼ(xⱼ)`
(`deg pⱼ ≤ 2nⱼ − 1`) exactly against `W(x) = ∏ⱼ ωⱼ(xⱼ)` with respect to the product measure. -/
theorem nq_prod_gauss_exact {d : ℕ} {n : Fin d → ℕ} {μ : Fin d → Measure ℝ}
    [∀ j, SigmaFinite (μ j)] {ω : Fin d → ℝ → ℝ} {w x : (j : Fin d) → Fin (n j) → ℝ}
    (hG : ∀ j, nqIsGaussRule (μ j) (ω j) (w j) (x j)) (p : Fin d → ℝ[X])
    (hp : ∀ j, (p j).natDegree < 2 * n j) :
    ∫ y, (∏ j, (p j).eval (y j)) * (∏ j, ω j (y j)) ∂(Measure.pi μ) =
      nqProdQuad w x (fun y => ∏ j, (p j).eval (y j)) := by
  simp_rw [← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod (fun j t => (p j).eval t * ω j t)]
  refine Eq.trans ?_ (nq_prodQuad_prod w x (fun j t => (p j).eval t)).symm
  exact Finset.prod_congr rfl fun j _ => nq_gauss_exact (hG j) (hp j)

/-- Miao, p. 350 (curse of dimensionality): the product rule uses `∏ⱼ nⱼ` nodes. -/
theorem nq_prodQuad_card {d : ℕ} (n : Fin d → ℕ) :
    Fintype.card ((j : Fin d) → Fin (n j)) = ∏ j, n j := by
  simp

end Miao.NumericalMethods

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Gauss–Chebyshev quadrature (Miao, §11.1.1, p. 349)

Miao, p. 349: Gauss–Chebyshev quadrature computes
`∫₋₁¹ f(x)(1 − x²)^{−1/2} dx ≃ (π/n) ∑ᵢ f(xᵢ)`, `xᵢ = cos((2i − 1)π/(2n))`, `i = 1, …, n`.
We prove that this rule is exact for every polynomial of degree `≤ 2n − 1`, i.e. that it is the
`n`-point Gaussian rule for the Chebyshev weight.

* `nq_chebyshev_substitution`: `∫₋₁¹ g(y)(1 − y²)^{−1/2} dy = ∫₀^π g(cos θ) dθ` for every `g`
  (the substitution `y = cos θ`), and `nq_chebyshev_integrableOn` (integrability of `g` against
  the weight follows from integrability of `g ∘ cos` on `[0, π]`).
* `nq_integral_cos_nat_mul`, `nq_cheb_sum_cos`: `∫₀^π cos(kθ) dθ = 0` and
  `∑ᵢ cos(kθᵢ) = 0` for `1 ≤ k ≤ 2n − 1` (`θᵢ = (2i + 1)π/(2n)`, 0-based).
* `nq_chebyshev_T_exact`: exactness on the Chebyshev polynomials `T₀, …, T_{2n−1}`
  (`Tₖ(cos θ) = cos(kθ)`), and `nq_chebyshev_exact` on all polynomials of degree `≤ 2n − 1`
  (the `Tₖ` span them: `deg Tₖ = k`, leading coefficient `2^{k−1}`).
* `nq_chebyshev_isGaussRule`: the Gauss–Chebyshev nodes and weights `π/n` satisfy the `2n`
  moment conditions of p. 348 (`nqIsGaussRule`).

**Departures.** Nodes are indexed `i = 0, …, n − 1` (`nqChebNode n i = cos((2i + 1)π/(2n))`),
the book's `i = 1, …, n` shifted by one. The improper integral over `(−1, 1)` is the Bochner
integral over `[−1, 1]` (the endpoints are null); `(1 − x²)^{−1/2}` is written
`(√(1 − x²))⁻¹`. The book writes "≃"; on polynomials of degree `≤ 2n − 1` it is an equality.
-/

namespace Miao.NumericalMethods

open MeasureTheory Polynomial Real

/-- Miao, p. 349: the Gauss–Chebyshev nodes `cos((2i + 1)π/(2n))`, `i = 0, …, n − 1` (the book's
`cos((2i − 1)π/(2n))`, `i = 1, …, n`). -/
noncomputable def nqChebNode (n : ℕ) (i : Fin n) : ℝ :=
  Real.cos ((2 * (i : ℝ) + 1) * π / (2 * n))

/-- Miao, p. 349 (substitution `y = cos θ`): for every `g`,
`∫₋₁¹ g(y)(1 − y²)^{−1/2} dy = ∫₀^π g(cos θ) dθ`. -/
theorem nq_chebyshev_substitution (g : ℝ → ℝ) :
    ∫ y in Set.Icc (-1) 1, g y * (√(1 - y ^ 2))⁻¹ = ∫ θ in (0 : ℝ)..π, g (Real.cos θ) := by
  have himg : Real.cos '' Set.Icc 0 π = Set.Icc (-1) 1 := Real.bijOn_cos.image_eq
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Icc
      (fun θ _ => (Real.hasDerivAt_cos θ).hasDerivWithinAt) Real.injOn_cos,
    intervalIntegral.integral_of_le pi_pos.le, integral_Icc_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hsq : √(1 - Real.cos θ ^ 2) = Real.sin θ := by
    rw [← Real.sin_sq, Real.sqrt_sq hs.le]
  simp only [hsq, abs_neg, abs_of_pos hs, smul_eq_mul]
  field_simp

/-- Miao, p. 349: `g` is integrable on `[−1, 1]` against the Chebyshev weight as soon as
`g ∘ cos` is integrable on `[0, π]`. -/
theorem nq_chebyshev_integrableOn {g : ℝ → ℝ}
    (hg : IntegrableOn (fun θ => g (Real.cos θ)) (Set.Icc 0 π)) :
    IntegrableOn (fun y => g y * (√(1 - y ^ 2))⁻¹) (Set.Icc (-1) 1) := by
  have himg : Real.cos '' Set.Icc 0 π = Set.Icc (-1) 1 := Real.bijOn_cos.image_eq
  rw [← himg, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Icc
      (fun θ _ => (Real.hasDerivAt_cos θ).hasDerivWithinAt) Real.injOn_cos,
    integrableOn_Icc_iff_integrableOn_Ioo]
  rw [integrableOn_Icc_iff_integrableOn_Ioo] at hg
  refine hg.congr_fun (fun θ hθ => ?_) measurableSet_Ioo
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hsq : √(1 - Real.cos θ ^ 2) = Real.sin θ := by
    rw [← Real.sin_sq, Real.sqrt_sq hs.le]
  simp only [hsq, abs_neg, abs_of_pos hs, smul_eq_mul]
  field_simp

/-- Miao, p. 349 (continuous part): `∫₀^π cos(kθ) dθ = π` if `k = 0` and `0` otherwise. -/
theorem nq_integral_cos_nat_mul (k : ℕ) :
    ∫ θ in (0 : ℝ)..π, Real.cos (k * θ) = if k = 0 then π else 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hk' : (k : ℝ) ≠ 0 := by positivity
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hk', integral_cos]
    simp [hk.ne', Real.sin_nat_mul_pi]

/-- Miao, p. 349 (discrete part): for `1 ≤ k ≤ 2n − 1`, `∑ᵢ cos(k(2i + 1)π/(2n)) = 0`
(telescoping `2 sin α cos((2i + 1)α) = sin((2i + 2)α) − sin(2iα)`, `α = kπ/(2n)`). -/
theorem nq_cheb_sum_cos (n k : ℕ) (hk1 : 0 < k) (hk2 : k < 2 * n) :
    ∑ i : Fin n, Real.cos (k * ((2 * (i : ℝ) + 1) * π / (2 * n))) = 0 := by
  set α : ℝ := k * π / (2 * n) with hα
  have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hαpos : 0 < α := by positivity
  have hαlt : α < π := by
    rw [hα, div_lt_iff₀ (by positivity)]
    have : (k : ℝ) < 2 * n := by exact_mod_cast hk2
    nlinarith [pi_pos]
  have hsin : Real.sin α ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hαpos hαlt).ne'
  have hterm : ∀ i : ℕ, 2 * Real.sin α * Real.cos (k * ((2 * (i : ℝ) + 1) * π / (2 * n))) =
      Real.sin (2 * ((i + 1 : ℕ) : ℝ) * α) - Real.sin (2 * (i : ℝ) * α) := by
    intro i
    have e0 : (k : ℝ) * ((2 * (i : ℝ) + 1) * π / (2 * n)) = (2 * i + 1) * α := by
      rw [hα]; ring
    have e1 : 2 * ((i + 1 : ℕ) : ℝ) * α = (2 * i + 1) * α + α := by push_cast; ring
    have e2 : 2 * (i : ℝ) * α = (2 * i + 1) * α - α := by ring
    rw [e0, e1, e2, Real.sin_add, Real.sin_sub]
    ring
  have hsum : 2 * Real.sin α *
      ∑ i : Fin n, Real.cos (k * ((2 * (i : ℝ) + 1) * π / (2 * n))) = 0 := by
    rw [Finset.mul_sum, Fin.sum_univ_eq_sum_range
      (fun i => 2 * Real.sin α * Real.cos (k * ((2 * (i : ℝ) + 1) * π / (2 * n)))),
      Finset.sum_congr rfl (fun i _ => hterm i),
      Finset.sum_range_sub (fun i => Real.sin (2 * (i : ℝ) * α))]
    have h2 : 2 * (n : ℝ) * α = k * π := by rw [hα]; field_simp
    simp [h2, Real.sin_nat_mul_pi]
  exact (mul_eq_zero.mp hsum).resolve_left (mul_ne_zero two_ne_zero hsin)

/-- Miao, p. 349: the Gauss–Chebyshev rule is exact for the Chebyshev polynomial `Tₖ`,
`k ≤ 2n − 1`: `∫₀^π Tₖ(cos θ) dθ = (π/n) ∑ᵢ Tₖ(xᵢ)`. -/
theorem nq_chebyshev_T_exact {n : ℕ} (hn : 0 < n) {k : ℕ} (hk : k < 2 * n) :
    ∫ θ in (0 : ℝ)..π, (Chebyshev.T ℝ (k : ℤ)).eval (Real.cos θ) =
      π / n * ∑ i, (Chebyshev.T ℝ (k : ℤ)).eval (nqChebNode n i) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  simp only [nqChebNode, Chebyshev.T_real_cos, Int.cast_natCast]
  rw [nq_integral_cos_nat_mul]
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · simp
    field_simp
  · rw [nq_cheb_sum_cos n k hk1 hk]
    simp [hk1.ne']

/-- Miao, p. 349 (exactness in `θ`-form): for `n ≥ 1` and `deg p ≤ 2n − 1`,
`∫₀^π p(cos θ) dθ = (π/n) ∑ᵢ p(xᵢ)`. -/
theorem nq_chebyshev_exact_theta {n : ℕ} (hn : 0 < n) :
    ∀ d, ∀ p : ℝ[X], p.natDegree = d → d < 2 * n →
      ∫ θ in (0 : ℝ)..π, p.eval (Real.cos θ) = π / n * ∑ i, p.eval (nqChebNode n i) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro p hpd hd
  rcases Nat.eq_zero_or_pos d with rfl | hd1
  · rw [eq_C_of_natDegree_eq_zero hpd]
    simp
    field_simp
  · have hp0 : p ≠ 0 := by
      rintro rfl; simp at hpd; omega
    set T' : ℝ[X] := Chebyshev.T ℝ (d : ℤ)
    have hTd : T'.natDegree = d := by simp [T']
    have hTl : T'.leadingCoeff = 2 ^ (d - 1) := by simp [T']
    have hT0 : T' ≠ 0 := by
      intro h; rw [h] at hTd; simp at hTd; omega
    set a : ℝ := p.leadingCoeff / 2 ^ (d - 1)
    have ha : a ≠ 0 := div_ne_zero (leadingCoeff_ne_zero.mpr hp0) (by positivity)
    set q : ℝ[X] := p - C a * T'
    have hdegCT : (C a * T').degree = p.degree := by
      rw [degree_C_mul ha, degree_eq_natDegree hT0, degree_eq_natDegree hp0, hTd, hpd]
    have hlcCT : p.leadingCoeff = (C a * T').leadingCoeff := by
      rw [leadingCoeff_mul, leadingCoeff_C, hTl]
      simp only [a]
      field_simp
    have hqlt : q.degree < p.degree := degree_sub_lt_left hdegCT.symm hp0 hlcCT
    have hqd : q.natDegree < d := by
      by_cases hq0 : q = 0
      · rw [hq0, natDegree_zero]; exact hd1
      · rw [← hpd]; exact natDegree_lt_natDegree hq0 hqlt
    have hIq := ih q.natDegree hqd q rfl (by omega)
    have hIT := nq_chebyshev_T_exact hn hd
    have hpq : p = q + C a * T' := by simp [q]
    rw [hpq]
    simp only [eval_add, eval_mul, eval_C]
    have i1 : IntervalIntegrable (fun θ => q.eval (Real.cos θ)) volume 0 π :=
      (q.continuous.comp Real.continuous_cos).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun θ => a * T'.eval (Real.cos θ)) volume 0 π :=
      (continuous_const.mul (T'.continuous.comp Real.continuous_cos)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul, hIq, hIT,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    ring

/-- Miao, p. 349 (Gauss–Chebyshev quadrature): for `n ≥ 1` and every polynomial `p` of degree
`≤ 2n − 1`, `∫₋₁¹ p(x)(1 − x²)^{−1/2} dx = (π/n) ∑ᵢ p(xᵢ)`, `xᵢ = cos((2i − 1)π/(2n))`. -/
theorem nq_chebyshev_exact {n : ℕ} (hn : 0 < n) {p : ℝ[X]} (hp : p.natDegree < 2 * n) :
    ∫ y in Set.Icc (-1) 1, p.eval y * (√(1 - y ^ 2))⁻¹ =
      nqQuad (fun _ => π / n) (nqChebNode n) p.eval := by
  rw [nq_chebyshev_substitution, nq_chebyshev_exact_theta hn _ p rfl hp, nqQuad,
    Finset.mul_sum]

/-- Miao, pp. 348–349: the Gauss–Chebyshev nodes and the weights `π/n` satisfy the `2n` moment
conditions of an `n`-point Gaussian rule for the weight `(1 − x²)^{−1/2}` on `[−1, 1]`. -/
theorem nq_chebyshev_isGaussRule {n : ℕ} (hn : 0 < n) :
    nqIsGaussRule (volume.restrict (Set.Icc (-1) 1)) (fun y => (√(1 - y ^ 2))⁻¹)
      (fun _ => π / n) (nqChebNode n) := by
  intro k hk
  refine ⟨nq_chebyshev_integrableOn
    ((continuous_pow k).comp Real.continuous_cos).integrableOn_Icc, ?_⟩
  have h := nq_chebyshev_exact hn (p := X ^ k) (by simpa using hk)
  simpa using h

end Miao.NumericalMethods

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Gauss–Hermite quadrature and normal expectations (Miao, §11.1.1, p. 349)

Miao, p. 349: Gauss–Hermite quadrature computes `∫ f(x) e^{−x²} dx ≃ ∑ᵢ wᵢ f(xᵢ)`, and is
"very useful to compute integrals with respect to normal distributions":
`E f(Y) = π^{−1/2} ∑ᵢ wᵢ f(√2 σ xᵢ + μ)` for `Y ~ N(μ, σ²)`.

* `nq_normal_expectation_hermite`: the change of variables behind the formula, an exact identity
  `E f(Y) = π^{−1/2} ∫ f(√2 σ x + μ) e^{−x²} dx` for every `f` (Bochner integrals).
* `nq_normal_expectation_gauss_hermite`: with an `n`-point Gauss–Hermite rule, the book's formula
  is exact for every polynomial `f` of degree `≤ 2n − 1`.
* `nq_hermite_one_point` (node `0`, weight `√π`) and `nq_hermite_two_point` (nodes `∓1/√2`,
  weights `√π/2`) are Gauss–Hermite rules; `nq_integral_odd_eq_zero`,
  `nq_integral_sq_mul_exp_neg_sq` (`∫ x² e^{−x²} dx = √π/2`) are the moments used.

**Departures.** The normal law is Mathlib's `gaussianReal μ v` with `v = σ²` (as `ℝ≥0`), `σ > 0`.
The book's "≃" is an equality on polynomials of degree `≤ 2n − 1`; the book's `Ef(Y) = …` is
the quadrature approximation, exact on that class.
-/

namespace Miao.NumericalMethods

open MeasureTheory Polynomial Real ProbabilityTheory

/-- Miao, p. 349 (normal expectations by Gauss–Hermite, exact change of variables): for
`Y ~ N(μ, σ²)` with `σ > 0` and every `f`, `E f(Y) = π^{−1/2} ∫ f(√2 σ x + μ) e^{−x²} dx`. -/
theorem nq_normal_expectation_hermite (m : ℝ) {σ : ℝ} (hσ : 0 < σ) (f : ℝ → ℝ) :
    ∫ y, f y ∂(gaussianReal m (Real.toNNReal (σ ^ 2))) =
      (√π)⁻¹ * ∫ x, f (√2 * σ * x + m) * Real.exp (-x ^ 2) := by
  set v : NNReal := Real.toNNReal (σ ^ 2)
  have hv : v ≠ 0 := by rw [ne_eq, Real.toNNReal_eq_zero, not_le]; positivity
  have hvr : (v : ℝ) = σ ^ 2 := Real.coe_toNNReal _ (sq_nonneg σ)
  rw [integral_gaussianReal_eq_integral_smul hv]
  set c : ℝ := √2 * σ with hcdef
  have hc : 0 < c := by positivity
  have key : ∫ y, gaussianPDFReal m v y • f y =
      c * ∫ x, gaussianPDFReal m v (c * x + m) • f (c * x + m) := by
    have h1 := Measure.integral_comp_mul_left
      (fun z => gaussianPDFReal m v (z + m) • f (z + m)) c
    have h2 := integral_add_right_eq_self (μ := volume) (fun z => gaussianPDFReal m v z • f z) m
    rw [h1, h2, abs_inv, abs_of_pos hc, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc.ne',
      one_mul]
  rw [key, ← integral_const_mul, ← integral_const_mul]
  congr 1
  funext x
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : √(2 * π * (v : ℝ)) = √2 * √π * σ := by
    rw [hvr, Real.sqrt_mul' _ (sq_nonneg σ), Real.sqrt_sq hσ.le,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have harg : -(c * x + m - m) ^ 2 / (2 * (v : ℝ)) = -x ^ 2 := by
    rw [hvr, hcdef]
    field_simp
    ring_nf
    rw [h2]
    ring
  rw [gaussianPDFReal_def]
  simp only [smul_eq_mul]
  rw [harg, hs, hcdef]
  have hpi : 0 < √π := Real.sqrt_pos.mpr pi_pos
  field_simp

/-- Miao, p. 349: with an `n`-point Gauss–Hermite rule `(xᵢ, wᵢ)` for the weight `e^{−x²}`, the
formula `E p(Y) = π^{−1/2} ∑ᵢ wᵢ p(√2 σ xᵢ + μ)`, `Y ~ N(μ, σ²)`, is exact for every polynomial
`p` of degree `≤ 2n − 1`. -/
theorem nq_normal_expectation_gauss_hermite {n : ℕ} {w x : Fin n → ℝ}
    (hG : nqIsGaussRule volume (fun y => Real.exp (-y ^ 2)) w x) (m : ℝ) {σ : ℝ} (hσ : 0 < σ)
    {p : ℝ[X]} (hp : p.natDegree < 2 * n) :
    ∫ y, p.eval y ∂(gaussianReal m (Real.toNNReal (σ ^ 2))) =
      (√π)⁻¹ * ∑ i, w i * p.eval (√2 * σ * x i + m) := by
  rw [nq_normal_expectation_hermite m hσ]
  set q : ℝ[X] := p.comp (C (√2 * σ) * X + C m)
  have hq : ∀ t, q.eval t = p.eval (√2 * σ * t + m) := by
    intro t; simp [q]
  have hqd : q.natDegree < 2 * n :=
    lt_of_le_of_lt (natDegree_comp_le.trans (by
      calc p.natDegree * (C (√2 * σ) * X + C m).natDegree ≤ p.natDegree * 1 :=
            Nat.mul_le_mul_left _ natDegree_linear_le
        _ = p.natDegree := mul_one _)) hp
  have hex := nq_gauss_exact hG hqd
  simp only [hq] at hex
  rw [hex]
  rfl

/-- The integral over `ℝ` of an odd function vanishes. -/
theorem nq_integral_odd_eq_zero {g : ℝ → ℝ} (hg : ∀ x, g (-x) = -g x) : ∫ x, g x = 0 := by
  have h := integral_neg_eq_self g (volume : Measure ℝ)
  simp only [hg, integral_neg] at h
  linarith

/-- `x ↦ xᵏ e^{−x²}` is integrable on `ℝ`. -/
theorem nq_integrable_pow_mul_exp_neg_sq (k : ℕ) :
    Integrable (fun y : ℝ => y ^ k * Real.exp (-y ^ 2)) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1) one_pos
    (s := (k : ℝ)) (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  simpa [Real.rpow_natCast] using h

/-- Miao, p. 349: `∫ e^{−x²} dx = √π`. -/
theorem nq_integral_exp_neg_sq : ∫ x : ℝ, Real.exp (-x ^ 2) = √π := by
  have h := integral_gaussian 1
  simpa using h

/-- Miao, p. 349: `∫ x² e^{−x²} dx = √π / 2` (via the variance of `N(0, 1/2)`). -/
theorem nq_integral_sq_mul_exp_neg_sq : ∫ x : ℝ, x ^ 2 * Real.exp (-x ^ 2) = √π / 2 := by
  have hσ : (0 : ℝ) < (√2)⁻¹ := by positivity
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h := nq_normal_expectation_hermite 0 hσ (fun y => y ^ 2)
  have hc : √2 * (√2)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  simp only [hc, one_mul, add_zero] at h
  set v : NNReal := Real.toNNReal ((√2)⁻¹ ^ 2)
  have hvr : (v : ℝ) = 1 / 2 := by
    rw [Real.coe_toNNReal _ (sq_nonneg _), inv_pow, h2]; norm_num
  have hvar := variance_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_sub (memLp_id_gaussianReal 2)] at hvar
  simp only [Pi.pow_apply, id] at hvar
  rw [integral_id_gaussianReal, hvr] at hvar
  have hE : ∫ y, y ^ 2 ∂(gaussianReal 0 v) = 1 / 2 := by linarith
  rw [hE] at h
  have hpi : 0 < √π := Real.sqrt_pos.mpr pi_pos
  field_simp at h ⊢
  linarith

/-- Miao, p. 349 (Gauss–Hermite, `n = 1`): the node `0` with weight `√π` is the one-point
Gauss–Hermite rule. -/
theorem nq_hermite_one_point :
    nqIsGaussRule volume (fun y => Real.exp (-y ^ 2)) (fun _ : Fin 1 => √π) (fun _ => 0) := by
  intro k hk
  refine ⟨nq_integrable_pow_mul_exp_neg_sq k, ?_⟩
  interval_cases k
  · simpa [nqQuad] using nq_integral_exp_neg_sq
  · simp only [nqQuad, pow_one, Finset.univ_unique, Finset.sum_singleton, mul_zero]
    exact nq_integral_odd_eq_zero fun x => by ring_nf

/-- Miao, p. 349 (Gauss–Hermite, `n = 2`): the nodes `∓1/√2` with weights `√π/2` form the
two-point Gauss–Hermite rule. -/
theorem nq_hermite_two_point :
    nqIsGaussRule volume (fun y => Real.exp (-y ^ 2)) (fun _ : Fin 2 => √π / 2)
      ![-(1 / √2), 1 / √2] := by
  intro k hk
  refine ⟨nq_integrable_pow_mul_exp_neg_sq k, ?_⟩
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2' : Real.sqrt 2 ≠ 0 := by positivity
  simp only [nqQuad, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  interval_cases k
  · simp only [pow_zero, one_mul, mul_one]
    rw [nq_integral_exp_neg_sq]; ring
  · rw [nq_integral_odd_eq_zero fun x => by ring_nf]
    ring
  · rw [nq_integral_sq_mul_exp_neg_sq]
    field_simp
    rw [h2]; ring
  · rw [nq_integral_odd_eq_zero fun x => by ring_nf]
    ring

end Miao.NumericalMethods

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Discretizing AR(1) processes (Miao, §11.2, pp. 350–354)

Miao, §11.2: the AR(1) process (11.1) `z_{t+1} = μ(1 − ρ) + ρ z_t + σ ε_{t+1}`, `ε` IID
`N(0, 1)`, is approximated by a finite Markov chain on `{z¹, …, z^N}` with transition matrix
`(π_{ij})`, by the methods of Tauchen (1986) and Tauchen and Hussey (1991); a Markov chain is
simulated by inverting its cumulative transition probabilities.

* The AR(1) (p. 351): `nq_ar1_mean_fixed` (`μ` is the only stationary mean),
  `nq_ar1_variance_fixed` (`σ_z² = σ²/(1 − ρ²)` is the only stationary variance), and
  `nq_ar1_stationary_law` (`N(μ, σ²/(1 − ρ²))` is a stationary law of (11.1)).
* Tauchen (pp. 351): the grid `nqTauchenGrid` (`nq_tauchen_grid_first`, `nq_tauchen_grid_last`,
  `nq_tauchen_grid_step`: `N` equally spaced points from `z_min = −mσ_z` to `z_max = mσ_z`), the
  cut points `nqTauchenCut` (midpoints of consecutive grid points, `nq_tauchen_cut_midpoint`,
  `nq_tauchen_cut_monotone`), the intervals `nqCell` (`nq_cell_eq`), the transition
  probabilities `nqTauchenProb` with `nq_tauchen_law` and `nq_tauchen_prob_eq` (Step 3:
  `π_{ij} = Pr(z_{t+1} ∈ I_j | z_t = zⁱ)` computed from (11.1)) and
  `nq_tauchen_stochastic` (the Tauchen matrix is stochastic, for any nondecreasing cut points).
  `nq_tauchen_printed_I2_upper`, `nq_tauchen_printed_IN_lower`: the printed interval endpoints
  are not the midpoints (correction).
* Tauchen–Hussey (pp. 352–353): `nq_th_ratio`, `nq_th_change_of_measure` (the transformation
  `∫ v f(·|z) = ∫ v (f(·|z)/f(·|0)) f(·|0)`), `nq_th_conditional_expectation` (the Gauss–Hermite
  form of `E[v(z')|z]`), `nq_th_exact` (with a Gauss–Hermite rule exact for the integrand,
  `E[v(z')|zⁱ] = ∑ⱼ π̃_{ij} v(zʲ)`), `nq_th_rowsum_integral` (the row sums `∑ⱼ π̃_{ij}` are the
  Gauss–Hermite approximation of `1`), `nq_th_rowsum_lt_one` ("we may have `∑ⱼ π̃_{ij} ≠ 1`": the
  two-point rule gives `e^{−ρ²/2} cosh ρ < 1` for every `ρ ≠ 0`), `nq_normalize_stochastic`
  and `nq_th_normalized_stochastic` (the normalised matrix `π_{ij}` is stochastic).
* Simulation (p. 353): `nq_sim_interval_volume` (`Pr(Π^c_{i,j−1} < p ≤ Π^c_{ij}) = π_{ij}` for
  `p` uniform on `[0, 1]`) and `nq_sim_unique` (every `p ∈ (0, 1]` selects exactly one state).

**Departures.** States and intervals are indexed `0, …, N − 1`; `nqCell c N j` is
`(−∞, c₁)` for `j = 0`, `[c_j, c_{j+1})` in between and `[c_{N−1}, ∞)` for `j = N − 1`. The
convergence `∑ⱼ π̃_{ij} → 1` as `N → ∞` (p. 353) needs the convergence theory of Gaussian
quadrature, which the book does not develop: not formalised. The steps of the algorithms
("in practice `m = 3` or `4`", the Matlab codes) are not formalised. The text of this draft has
no Rouwenhorst method.
-/

namespace Miao.NumericalMethods

open MeasureTheory Polynomial Real ProbabilityTheory

/-! ### The AR(1) process (11.1) -/

/-- Miao, (11.1), p. 351: `μ` is the unconditional mean of (11.1): for `ρ ≠ 1` it is the only
`m` with `m = μ(1 − ρ) + ρ m`. -/
theorem nq_ar1_mean_fixed {μ ρ m : ℝ} (hρ : ρ ≠ 1) : m = μ * (1 - ρ) + ρ * m ↔ m = μ := by
  constructor
  · intro h
    have h1 : (1 - ρ) * (m - μ) = 0 := by linarith
    have h2 : (1 - ρ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
    linarith [(mul_eq_zero.mp h1).resolve_left h2]
  · rintro rfl; ring

/-- Miao, p. 351: for `|ρ| < 1` the unconditional variance `σ_z² = σ²/(1 − ρ²)` of (11.1) is the
only `s` with `s = ρ² s + σ²` (variance of `ρ z_t + σ ε_{t+1}` with `ε` independent of `z_t`). -/
theorem nq_ar1_variance_fixed {ρ σ s : ℝ} (hρ : |ρ| < 1) :
    s = ρ ^ 2 * s + σ ^ 2 ↔ s = σ ^ 2 / (1 - ρ ^ 2) := by
  have h1 : 0 < 1 - ρ ^ 2 := by
    have := sq_lt_one_iff_abs_lt_one ρ |>.mpr hρ; linarith
  rw [eq_div_iff h1.ne']
  constructor <;> intro h <;> linarith

/-- Miao, (11.1), p. 351: `N(μ, σ_z²)`, `σ_z² = σ²/(1 − ρ²)`, is a stationary law of (11.1): if
`z_t ~ N(μ, σ_z²)` and `ε_{t+1} ~ N(0, 1)` is independent of `z_t`, then
`z_{t+1} = μ(1 − ρ) + ρ z_t + σ ε_{t+1} ~ N(μ, σ_z²)`. -/
theorem nq_ar1_stationary_law {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z ε : Ω → ℝ} {μ ρ σ : ℝ} (hρ : |ρ| < 1)
    (hZ : HasLaw Z (gaussianReal μ (Real.toNNReal (σ ^ 2 / (1 - ρ ^ 2)))) P)
    (hε : HasLaw ε (gaussianReal 0 1) P) (hind : IndepFun Z ε P) :
    HasLaw (fun ω => μ * (1 - ρ) + ρ * Z ω + σ * ε ω)
      (gaussianReal μ (Real.toNNReal (σ ^ 2 / (1 - ρ ^ 2)))) P := by
  have h1 : 0 < 1 - ρ ^ 2 := by
    have := sq_lt_one_iff_abs_lt_one ρ |>.mpr hρ; linarith
  set s : ℝ := σ ^ 2 / (1 - ρ ^ 2)
  have hs : 0 ≤ s := div_nonneg (sq_nonneg σ) h1.le
  have hX := gaussianReal_const_add (gaussianReal_const_mul hZ ρ) (μ * (1 - ρ))
  have hY := gaussianReal_const_mul hε σ
  have hind' : IndepFun (fun ω => μ * (1 - ρ) + ρ * Z ω) (fun ω => σ * ε ω) P :=
    hind.comp (φ := fun x => μ * (1 - ρ) + ρ * x) (ψ := fun x => σ * x)
      (by fun_prop) (by fun_prop)
  have hmap := gaussianReal_add_gaussianReal_of_indepFun hind' hX hY
  refine ⟨(hX.aemeasurable.add hY.aemeasurable), ?_⟩
  have hfun : (fun ω => μ * (1 - ρ) + ρ * Z ω + σ * ε ω) =
      (fun ω => μ * (1 - ρ) + ρ * Z ω) + (fun ω => σ * ε ω) := rfl
  rw [hfun, hmap]
  congr 1
  · ring
  · apply NNReal.eq
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk,
      Real.coe_toNNReal _ hs, mul_one]
    have := (nq_ar1_variance_fixed (σ := σ) (s := s) hρ).mpr rfl
    linarith

/-! ### Tauchen's method -/

/-- Miao, p. 351 (Tauchen, Step 1): the `N` equally spaced grid points
`zⁱ = z_min + i (z_max − z_min)/(N − 1)`, `i = 0, …, N − 1`. -/
noncomputable def nqTauchenGrid (N : ℕ) (zmin zmax : ℝ) (i : ℕ) : ℝ :=
  zmin + i * (zmax - zmin) / (N - 1)

/-- Miao, p. 351: the first grid point is `z_min`. -/
theorem nq_tauchen_grid_first (N : ℕ) (zmin zmax : ℝ) : nqTauchenGrid N zmin zmax 0 = zmin := by
  simp [nqTauchenGrid]

/-- Miao, p. 351: the last grid point is `z_max` (`N ≥ 2`). -/
theorem nq_tauchen_grid_last {N : ℕ} (hN : 2 ≤ N) (zmin zmax : ℝ) :
    nqTauchenGrid N zmin zmax (N - 1) = zmax := by
  have h : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have h1 : (N : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  simp only [nqTauchenGrid, h]
  field_simp
  ring

/-- Miao, p. 351: consecutive grid points are `(z_max − z_min)/(N − 1)` apart. -/
theorem nq_tauchen_grid_step (N : ℕ) (zmin zmax : ℝ) (i : ℕ) :
    nqTauchenGrid N zmin zmax (i + 1) - nqTauchenGrid N zmin zmax i = (zmax - zmin) / (N - 1) := by
  simp only [nqTauchenGrid]
  push_cast
  ring

/-- Miao, p. 351: the grid is symmetric for `z_max = mσ_z = −z_min`: `z^{N−1−i} = −zⁱ`. -/
theorem nq_tauchen_grid_symm {N : ℕ} (hN : 2 ≤ N) (m σz : ℝ) {i : ℕ} (hi : i ≤ N - 1) :
    nqTauchenGrid N (-(m * σz)) (m * σz) (N - 1 - i) = -nqTauchenGrid N (-(m * σz)) (m * σz) i := by
  have h : ((N - 1 - i : ℕ) : ℝ) = (N : ℝ) - 1 - i := by
    rw [Nat.cast_sub hi, Nat.cast_sub (by omega)]; simp
  have h1 : (N : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  simp only [nqTauchenGrid, h]
  field_simp
  ring

/-- Miao, p. 351 (Tauchen, Step 2): the cut points `c_j = z_min + (2j − 1)(z_max − z_min)/(2(N−1))`,
`j = 1, …, N − 1`, separating the intervals `I_j`. -/
noncomputable def nqTauchenCut (N : ℕ) (zmin zmax : ℝ) (j : ℕ) : ℝ :=
  zmin + (2 * j - 1) * (zmax - zmin) / (2 * (N - 1))

/-- Miao, p. 351: each cut point is the midpoint of two consecutive grid points. -/
theorem nq_tauchen_cut_midpoint (N : ℕ) (zmin zmax : ℝ) (j : ℕ) :
    nqTauchenCut N zmin zmax (j + 1) =
      (nqTauchenGrid N zmin zmax j + nqTauchenGrid N zmin zmax (j + 1)) / 2 := by
  simp only [nqTauchenCut, nqTauchenGrid]
  push_cast
  by_cases h : (N : ℝ) - 1 = 0
  · simp [h]
  · field_simp
    ring

/-- Miao, p. 351: the cut points are nondecreasing when `z_min ≤ z_max` and `N ≥ 2`. -/
theorem nq_tauchen_cut_monotone {N : ℕ} (hN : 2 ≤ N) {zmin zmax : ℝ} (h : zmin ≤ zmax) :
    Monotone (nqTauchenCut N zmin zmax) := by
  intro i j hij
  have hN' : (0 : ℝ) < 2 * ((N : ℝ) - 1) := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
  simp only [nqTauchenCut]
  have : (2 * (i : ℝ) - 1) * (zmax - zmin) ≤ (2 * (j : ℝ) - 1) * (zmax - zmin) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have := div_le_div_of_nonneg_right this hN'.le
  linarith

/-- Miao, p. 351 (correction): the printed upper endpoint `z_min + (z_max − z_min)/(N − 1)` of
`I₂` is not the cut point between `z²` and `z³` (book's numbering), which is
`z_min + 3(z_max − z_min)/(2(N − 1))` (here `nqTauchenCut N z_min z_max 2`). -/
theorem nq_tauchen_printed_I2_upper {N : ℕ} (hN : 2 ≤ N) {zmin zmax : ℝ} (h : zmin < zmax) :
    zmin + (zmax - zmin) / (N - 1) ≠ nqTauchenCut N zmin zmax 2 := by
  have hN' : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  simp only [nqTauchenCut]
  intro heq
  have : (zmax - zmin) / (N - 1) = 3 * (zmax - zmin) / (2 * (N - 1)) := by
    push_cast at heq ⊢; linarith
  field_simp at this
  linarith

/-- Miao, p. 351 (correction): the printed lower endpoint `z_min + N(z_max − z_min)/(2(N − 1))` of
`I_N` is not the last cut point `z_min + (2N − 3)(z_max − z_min)/(2(N − 1))` (the midpoint of
the two largest grid points) when `N ≥ 4`. -/
theorem nq_tauchen_printed_IN_lower {N : ℕ} (hN : 4 ≤ N) {zmin zmax : ℝ} (h : zmin < zmax) :
    zmin + N * (zmax - zmin) / (2 * (N - 1)) ≠ nqTauchenCut N zmin zmax (N - 1) := by
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hN' : (0 : ℝ) < 2 * ((N : ℝ) - 1) := by linarith
  have hc : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  simp only [nqTauchenCut, hc]
  intro heq
  have h2 : (N : ℝ) * (zmax - zmin) / (2 * ((N : ℝ) - 1)) =
      (2 * ((N : ℝ) - 1) - 1) * (zmax - zmin) / (2 * ((N : ℝ) - 1)) := by linarith
  rw [div_left_inj' hN'.ne'] at h2
  have h3 : (N : ℝ) = 2 * ((N : ℝ) - 1) - 1 :=
    mul_right_cancel₀ (sub_ne_zero.mpr h.ne') h2
  linarith

/-- Miao, p. 351 (Tauchen, Step 2): the intervals `I_j` determined by cut points `c`:
`(−∞, c₁)` for `j = 0`, `[c_j, c_{j+1})` for `0 < j < N − 1`, `[c_{N−1}, ∞)` for `j = N − 1`. -/
def nqCell (c : ℕ → ℝ) (N j : ℕ) : Set ℝ :=
  {z | (j = 0 ∨ c j ≤ z) ∧ (j + 1 = N ∨ z < c (j + 1))}

/-- The four shapes of the intervals `I_j`. -/
theorem nq_cell_eq (c : ℕ → ℝ) (N j : ℕ) :
    nqCell c N j =
      if j = 0 then (if j + 1 = N then Set.univ else Set.Iio (c (j + 1)))
      else (if j + 1 = N then Set.Ici (c j) else Set.Ico (c j) (c (j + 1))) := by
  ext z
  by_cases h0 : j = 0 <;> by_cases h1 : j + 1 = N <;>
    simp [nqCell, h0, h1, Set.mem_Ico] <;> tauto

/-- The intervals `I_j` are Borel sets. -/
theorem nq_cell_measurable (c : ℕ → ℝ) (N j : ℕ) : MeasurableSet (nqCell c N j) := by
  rw [nq_cell_eq]
  split_ifs
  · exact MeasurableSet.univ
  · exact measurableSet_Iio
  · exact measurableSet_Ici
  · exact measurableSet_Ico

/-- Miao, p. 351: for any probability measure and nondecreasing cut points, the probabilities of
the `N` intervals `I_j` sum to one (they telescope through the distribution function). -/
theorem nq_cells_sum_one (P : Measure ℝ) [IsProbabilityMeasure P] {c : ℕ → ℝ} (hc : Monotone c)
    {N : ℕ} (hN : 0 < N) : ∑ j ∈ Finset.range N, P.real (nqCell c N j) = 1 := by
  set G : ℕ → ℝ := fun k => if k = 0 then 0 else if k = N then 1 else P.real (Set.Iio (c k))
  have hG : ∀ j ∈ Finset.range N, P.real (nqCell c N j) = G (j + 1) - G j := by
    intro j hj
    have hjN := Finset.mem_range.mp hj
    have hN0 : N ≠ 0 := by omega
    rw [nq_cell_eq]
    by_cases h0 : j = 0 <;> by_cases h1 : j + 1 = N
    · subst h0
      simp [G, ← h1]
    · subst h0
      have h1' : (1 : ℕ) ≠ N := by simpa using h1
      simp [G, h1']
    · have hjN' : j ≠ N := by omega
      simp only [G, h0, h1, hjN', hN0, ↓reduceIte]
      rw [← Set.compl_Iio, measureReal_compl measurableSet_Iio, probReal_univ]
    · have hjN' : j ≠ N := by omega
      simp only [G, h0, h1, hjN', ↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false]
      have hdisj : Disjoint (Set.Iio (c j)) (Set.Ico (c j) (c (j + 1))) :=
        Set.disjoint_left.mpr fun z hz hz' => absurd hz'.1 (not_le.mpr hz)
      rw [← Set.Iio_union_Ico_eq_Iio (hc (Nat.le_add_right j 1)),
        measureReal_union (μ := P) hdisj measurableSet_Ico]
      ring
  rw [Finset.sum_congr rfl hG, Finset.sum_range_sub (f := G)]
  simp [G, hN.ne']

/-- Miao, p. 351 (Tauchen, Step 3): the transition probability
`π_{ij} = Pr(z_{t+1} ∈ I_j | z_t = zⁱ)`, the `N(ρ zⁱ, σ²)` probability of `I_j` (`μ = 0`). -/
noncomputable def nqTauchenProb (ρ σ : ℝ) (c : ℕ → ℝ) (N : ℕ) (zi : ℝ) (j : ℕ) : ℝ :=
  (gaussianReal (ρ * zi) (Real.toNNReal (σ ^ 2))).real (nqCell c N j)

/-- Miao, (11.1), p. 351: given `z_t = z`, `z_{t+1} = ρ z + σ ε_{t+1}` (`μ = 0`) has law
`N(ρ z, σ²)`: the image of `N(0, 1)` under `e ↦ ρ z + σ e`. -/
theorem nq_tauchen_law (ρ σ z : ℝ) :
    (gaussianReal 0 1).map (fun e => ρ * z + σ * e) =
      gaussianReal (ρ * z) (Real.toNNReal (σ ^ 2)) := by
  have hcomp : (fun e => ρ * z + σ * e) = (fun y => ρ * z + y) ∘ (fun e => σ * e) := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_const_add]
  congr 1
  · ring
  · apply NNReal.eq
    simp [Real.coe_toNNReal _ (sq_nonneg σ)]

/-- Miao, p. 351 (Step 3, "by (11.1), these transition probabilities can be easily computed"):
`π_{ij} = Pr(ρ zⁱ + σ ε ∈ I_j)` with `ε ~ N(0, 1)`. -/
theorem nq_tauchen_prob_eq (ρ σ : ℝ) (c : ℕ → ℝ) (N : ℕ) (zi : ℝ) (j : ℕ) :
    nqTauchenProb ρ σ c N zi j =
      (gaussianReal 0 1).real ((fun e => ρ * zi + σ * e) ⁻¹' nqCell c N j) := by
  rw [nqTauchenProb, ← nq_tauchen_law, measureReal_def, measureReal_def,
    Measure.map_apply (by fun_prop) (nq_cell_measurable c N j)]

/-- Miao, p. 351: the Tauchen matrix is stochastic: `π_{ij} ≥ 0` and `∑ⱼ π_{ij} = 1` for every
state `zⁱ`, for any nondecreasing cut points (in particular `nqTauchenCut`). -/
theorem nq_tauchen_stochastic (ρ σ : ℝ) {c : ℕ → ℝ} (hc : Monotone c) {N : ℕ} (hN : 0 < N)
    (zi : ℝ) :
    (∀ j, 0 ≤ nqTauchenProb ρ σ c N zi j) ∧
      ∑ j ∈ Finset.range N, nqTauchenProb ρ σ c N zi j = 1 :=
  ⟨fun _ => measureReal_nonneg, nq_cells_sum_one _ hc hN⟩

/-! ### The Tauchen–Hussey method -/

/-- Miao, p. 352: the conditional density `f(z'|z)` of `z_{t+1}` given `z_t = z` (`μ = 0`), the
`N(ρ z, σ²)` density. -/
noncomputable def nqCondDens (ρ σ z' z : ℝ) : ℝ :=
  gaussianPDFReal (ρ * z) (Real.toNNReal (σ ^ 2)) z'

/-- Miao, p. 352: `f(z'|z)/f(z'|0) = exp((z'² − (z' − ρz)²)/(2σ²))`. -/
theorem nq_th_ratio (ρ : ℝ) {σ : ℝ} (hσ : 0 < σ) (z' z : ℝ) :
    nqCondDens ρ σ z' z / nqCondDens ρ σ z' 0 =
      Real.exp ((z' ^ 2 - (z' - ρ * z) ^ 2) / (2 * σ ^ 2)) := by
  simp only [nqCondDens, gaussianPDFReal_def, Real.coe_toNNReal _ (sq_nonneg σ), mul_zero,
    sub_zero]
  have hA : (√(2 * π * σ ^ 2))⁻¹ ≠ 0 := by
    have : 0 < 2 * π * σ ^ 2 := by positivity
    positivity
  rw [mul_div_mul_left _ _ hA, ← Real.exp_sub]
  congr 1
  ring

/-- Miao, p. 352 (the Tauchen–Hussey transformation):
`∫ v(z') f(z'|z) dz' = ∫ v(z') (f(z'|z)/f(z'|0)) f(z'|0) dz'`. -/
theorem nq_th_change_of_measure (ρ : ℝ) {σ : ℝ} (hσ : 0 < σ) (v : ℝ → ℝ) (z : ℝ) :
    ∫ z', v z' * nqCondDens ρ σ z' z =
      ∫ z', v z' * (nqCondDens ρ σ z' z / nqCondDens ρ σ z' 0) * nqCondDens ρ σ z' 0 := by
  congr 1
  funext z'
  have hpos : 0 < nqCondDens ρ σ z' 0 :=
    gaussianPDFReal_pos _ _ _ (by rw [ne_eq, Real.toNNReal_eq_zero, not_le]; positivity)
  field_simp

/-- Miao, p. 352: `E[v(z')|z] = π^{−1/2} ∫ v(√2σx) f(√2σx|z)/f(√2σx|0) e^{−x²} dx`, the
Gauss–Hermite form of the conditional expectation after the transformation. -/
theorem nq_th_conditional_expectation (ρ : ℝ) {σ : ℝ} (hσ : 0 < σ) (v : ℝ → ℝ) (z : ℝ) :
    ∫ z', v z' ∂(gaussianReal (ρ * z) (Real.toNNReal (σ ^ 2))) =
      (√π)⁻¹ * ∫ x, v (√2 * σ * x) *
        (nqCondDens ρ σ (√2 * σ * x) z / nqCondDens ρ σ (√2 * σ * x) 0) *
          Real.exp (-x ^ 2) := by
  have hv : Real.toNNReal (σ ^ 2) ≠ 0 := by
    rw [ne_eq, Real.toNNReal_eq_zero, not_le]; positivity
  have h0 := nq_normal_expectation_hermite 0 hσ
    (fun z' => v z' * (nqCondDens ρ σ z' z / nqCondDens ρ σ z' 0))
  simp only [add_zero] at h0
  rw [← h0, integral_gaussianReal_eq_integral_smul hv, integral_gaussianReal_eq_integral_smul hv]
  have h1 := nq_th_change_of_measure ρ hσ v z
  simp only [nqCondDens, mul_zero] at h1
  simp only [smul_eq_mul]
  rw [show (fun x => gaussianPDFReal (ρ * z) (Real.toNNReal (σ ^ 2)) x * v x) =
    fun x => v x * gaussianPDFReal (ρ * z) (Real.toNNReal (σ ^ 2)) x from
      funext fun x => mul_comm _ _, h1]
  congr 1
  funext x
  simp only [nqCondDens, mul_zero]
  ring

/-- Miao, p. 352: the Tauchen–Hussey weights
`π̃_{ij} = π^{−1/2} wⱼ f(zʲ|zⁱ)/f(zʲ|0)`, `zʲ = √2 σ xⱼ` (Gauss–Hermite nodes `xⱼ`, weights
`wⱼ`); the book prints a spurious `∑ⱼ` in front (correction). -/
noncomputable def nqTHTilde {N : ℕ} (w x : Fin N → ℝ) (ρ σ zi : ℝ) (j : Fin N) : ℝ :=
  (√π)⁻¹ * w j * (nqCondDens ρ σ (√2 * σ * x j) zi / nqCondDens ρ σ (√2 * σ * x j) 0)

/-- Miao, p. 352: if the Gauss–Hermite rule `(x, w)` is exact for the transformed integrand
`g(x) = v(√2σx) f(√2σx|zⁱ)/f(√2σx|0)`, then `E[v(z')|zⁱ] = ∑ⱼ π̃_{ij} v(zʲ)`. -/
theorem nq_th_exact (ρ : ℝ) {σ : ℝ} (hσ : 0 < σ) (v : ℝ → ℝ) (zi : ℝ) {N : ℕ}
    {w x : Fin N → ℝ}
    (hex : ∫ y, (fun t => v (√2 * σ * t) *
        (nqCondDens ρ σ (√2 * σ * t) zi / nqCondDens ρ σ (√2 * σ * t) 0)) y *
          Real.exp (-y ^ 2) =
      nqQuad w x (fun t => v (√2 * σ * t) *
        (nqCondDens ρ σ (√2 * σ * t) zi / nqCondDens ρ σ (√2 * σ * t) 0))) :
    ∫ z', v z' ∂(gaussianReal (ρ * zi) (Real.toNNReal (σ ^ 2))) =
      ∑ j, nqTHTilde w x ρ σ zi j * v (√2 * σ * x j) := by
  rw [nq_th_conditional_expectation ρ hσ v zi, hex, nqQuad, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [nqTHTilde]
  ring

/-- Miao, p. 353: the row sums `∑ⱼ π̃_{ij}` are the Gauss–Hermite approximation of
`π^{−1/2} ∫ f(√2σx|zⁱ)/f(√2σx|0) e^{−x²} dx`, which equals `1` exactly. -/
theorem nq_th_rowsum_integral (ρ : ℝ) {σ : ℝ} (hσ : 0 < σ) (zi : ℝ) :
    (√π)⁻¹ * ∫ x, (nqCondDens ρ σ (√2 * σ * x) zi / nqCondDens ρ σ (√2 * σ * x) 0) *
      Real.exp (-x ^ 2) = 1 := by
  have h := nq_th_conditional_expectation ρ hσ (fun _ => 1) zi
  simp only [integral_const, probReal_univ, one_smul, one_mul] at h
  exact h.symm

/-- Miao, p. 352 ("we may have `∑ⱼ π̃_{ij} ≠ 1`"): with the two-point Gauss–Hermite rule
(`nq_hermite_two_point`), the state `z = σ` and any `ρ ≠ 0`, the row sum is
`e^{−ρ²/2} cosh ρ < 1`. -/
theorem nq_th_rowsum_lt_one {ρ σ : ℝ} (hσ : 0 < σ) (hρ : ρ ≠ 0) :
    ∑ j, nqTHTilde (fun _ : Fin 2 => √π / 2) ![-(1 / √2), 1 / √2] ρ σ σ j < 1 := by
  have h2 : √2 * σ * (1 / √2) = σ := by field_simp
  have h2' : √2 * σ * -(1 / √2) = -σ := by field_simp
  have hpi : 0 < √π := Real.sqrt_pos.mpr pi_pos
  simp only [nqTHTilde, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, h2, h2', nq_th_ratio ρ hσ]
  have e1 : ((-σ) ^ 2 - (-σ - ρ * σ) ^ 2) / (2 * σ ^ 2) = -ρ - ρ ^ 2 / 2 := by
    field_simp; ring
  have e2 : (σ ^ 2 - (σ - ρ * σ) ^ 2) / (2 * σ ^ 2) = ρ - ρ ^ 2 / 2 := by
    field_simp; ring
  rw [e1, e2]
  have hsum : (√π)⁻¹ * (√π / 2) * Real.exp (-ρ - ρ ^ 2 / 2) +
      (√π)⁻¹ * (√π / 2) * Real.exp (ρ - ρ ^ 2 / 2) =
      Real.exp (-(ρ ^ 2 / 2)) * Real.cosh ρ := by
    rw [Real.cosh_eq]
    have ea : Real.exp (-ρ - ρ ^ 2 / 2) = Real.exp (-ρ) * Real.exp (-(ρ ^ 2 / 2)) := by
      rw [← Real.exp_add]; ring_nf
    have eb : Real.exp (ρ - ρ ^ 2 / 2) = Real.exp ρ * Real.exp (-(ρ ^ 2 / 2)) := by
      rw [← Real.exp_add]; ring_nf
    rw [ea, eb]
    field_simp
    ring
  rw [hsum]
  -- `cosh ρ = 2 cosh²(ρ/2) − 1 ≤ 2 exp(ρ²/4) − 1 < exp(ρ²/2)`
  have hc2 : Real.cosh ρ = 2 * Real.cosh (ρ / 2) ^ 2 - 1 := by
    have := Real.cosh_two_mul (ρ / 2)
    rw [show 2 * (ρ / 2) = ρ by ring, Real.cosh_sq] at this
    rw [this, Real.cosh_sq]; ring
  have hle : Real.cosh (ρ / 2) ≤ Real.exp ((ρ / 2) ^ 2 / 2) := Real.cosh_le_exp_half_sq _
  have hpos : 0 ≤ Real.cosh (ρ / 2) := (Real.cosh_pos _).le
  set t : ℝ := Real.exp (ρ ^ 2 / 4)
  have ht : Real.exp ((ρ / 2) ^ 2 / 2) ^ 2 = t := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hsq : Real.cosh (ρ / 2) ^ 2 ≤ t := by
    rw [← ht]; exact pow_le_pow_left₀ hpos hle 2
  have ht1 : t ≠ 1 := by
    intro h
    have : ρ ^ 2 / 4 = 0 := by
      have := congrArg Real.log h
      rwa [Real.log_exp, Real.log_one] at this
    exact hρ (by nlinarith [sq_nonneg ρ])
  have hlt : 2 * t - 1 < t ^ 2 := by
    have : 0 < (t - 1) ^ 2 := by positivity
    nlinarith
  have hexp : Real.exp (ρ ^ 2 / 2) = t ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hcosh : Real.cosh ρ < Real.exp (ρ ^ 2 / 2) := by
    rw [hc2, hexp]; linarith
  have hE : Real.exp (-(ρ ^ 2 / 2)) * Real.exp (ρ ^ 2 / 2) = 1 := by
    rw [← Real.exp_add]; simp
  have hEpos : 0 < Real.exp (-(ρ ^ 2 / 2)) := Real.exp_pos _
  nlinarith

/-- Miao, p. 352: normalising nonnegative weights with positive sum, `q_j / ∑ₖ q_k`, gives a
probability vector. -/
theorem nq_normalize_stochastic {N : ℕ} (q : Fin N → ℝ) (hq : ∀ j, 0 ≤ q j)
    (hpos : 0 < ∑ j, q j) :
    (∀ j, 0 ≤ q j / ∑ k, q k) ∧ ∑ j, q j / ∑ k, q k = 1 := by
  refine ⟨fun j => div_nonneg (hq j) hpos.le, ?_⟩
  rw [← Finset.sum_div, div_self hpos.ne']

/-- Miao, p. 352: with positive Gauss–Hermite weights and `N ≥ 1`, the normalised Tauchen–Hussey
matrix `π_{ij} = π̃_{ij} / ∑ⱼ π̃_{ij}` is stochastic. -/
theorem nq_th_normalized_stochastic {N : ℕ} (hN : 0 < N) {w : Fin N → ℝ} (hw : ∀ j, 0 < w j)
    (x : Fin N → ℝ) (ρ : ℝ) {σ : ℝ} (hσ : 0 < σ) (zi : ℝ) :
    (∀ j, 0 ≤ nqTHTilde w x ρ σ zi j / ∑ k, nqTHTilde w x ρ σ zi k) ∧
      ∑ j, nqTHTilde w x ρ σ zi j / ∑ k, nqTHTilde w x ρ σ zi k = 1 := by
  have hpos : ∀ j, 0 < nqTHTilde w x ρ σ zi j := by
    intro j
    have hv : Real.toNNReal (σ ^ 2) ≠ 0 := by
      rw [ne_eq, Real.toNNReal_eq_zero, not_le]; positivity
    have h1 := gaussianPDFReal_pos (ρ * zi) _ (√2 * σ * x j) hv
    have h2 := gaussianPDFReal_pos (ρ * 0) _ (√2 * σ * x j) hv
    have hpi : 0 < √π := Real.sqrt_pos.mpr pi_pos
    simp only [nqTHTilde, nqCondDens]
    have := hw j
    positivity
  refine nq_normalize_stochastic _ (fun j => (hpos j).le) ?_
  exact Finset.sum_pos (fun j _ => hpos j) ⟨⟨0, hN⟩, Finset.mem_univ _⟩

/-! ### Simulating a Markov chain -/

/-- Miao, p. 353 (simulation, Step 3): for a uniform draw `p` on `[0, 1]`, the probability of
`Π^c_{i,j−1} < p ≤ Π^c_{ij}` (cumulative sums `Π^c_{ij} = ∑_{k ≤ j} π_{ik}`, `Π^c_{i,−1} = 0`)
is `π_{ij}`: the algorithm draws state `j` with the correct probability. -/
theorem nq_sim_interval_volume {N : ℕ} {p : ℕ → ℝ} (hp : ∀ k, 0 ≤ p k)
    (hsum : ∑ k ∈ Finset.range N, p k = 1) {j : ℕ} (hj : j < N) :
    (volume.restrict (Set.Icc (0 : ℝ) 1))
        (Set.Ioc (∑ k ∈ Finset.range j, p k) (∑ k ∈ Finset.range (j + 1), p k)) =
      ENNReal.ofReal (p j) := by
  have h0 : 0 ≤ ∑ k ∈ Finset.range j, p k := Finset.sum_nonneg fun k _ => hp k
  have h1 : ∑ k ∈ Finset.range (j + 1), p k ≤ 1 := by
    rw [← hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hj)
      (fun k _ _ => hp k)
  rw [Measure.restrict_apply measurableSet_Ioc]
  have hsub : Set.Ioc (∑ k ∈ Finset.range j, p k) (∑ k ∈ Finset.range (j + 1), p k) ∩
      Set.Icc 0 1 = Set.Ioc (∑ k ∈ Finset.range j, p k) (∑ k ∈ Finset.range (j + 1), p k) :=
    Set.inter_eq_left.mpr fun u hu => ⟨by linarith [hu.1], hu.2.trans h1⟩
  rw [hsub, Real.volume_Ioc, Finset.sum_range_succ]
  congr 1
  ring

/-- Miao, p. 353 (simulation, Step 3): every `p ∈ (0, 1]` selects exactly one state `j < N` with
`Π^c_{i,j−1} < p ≤ Π^c_{ij}` (the case `j = 0` is the book's "if `p_t ≤ π_{i1}`"). -/
theorem nq_sim_unique {N : ℕ} {p : ℕ → ℝ} (hp : ∀ k, 0 ≤ p k)
    (hsum : ∑ k ∈ Finset.range N, p k = 1) {u : ℝ} (hu : u ∈ Set.Ioc (0 : ℝ) 1) :
    ∃! j, j < N ∧ ∑ k ∈ Finset.range j, p k < u ∧ u ≤ ∑ k ∈ Finset.range (j + 1), p k := by
  classical
  have hmono : Monotone (fun m => ∑ k ∈ Finset.range m, p k) := fun a b hab =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hab)
      (fun k _ _ => hp k)
  have hex : ∃ m, u ≤ ∑ k ∈ Finset.range m, p k := ⟨N, hsum ▸ hu.2⟩
  set m := Nat.find hex
  have hm : u ≤ ∑ k ∈ Finset.range m, p k := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h
    rw [h] at hm
    simp at hm
    linarith [hu.1]
  have hmN : m ≤ N := Nat.find_min' hex (hsum ▸ hu.2)
  refine ⟨m - 1, ⟨by omega, ?_, ?_⟩, ?_⟩
  · have := Nat.find_min hex (show m - 1 < m by omega)
    exact lt_of_not_ge this
  · rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)]; exact hm
  · rintro j ⟨_, hj1, hj2⟩
    have hjm : j + 1 ≥ m := Nat.find_min' hex hj2
    by_contra hne
    have hjm' : m ≤ j := by omega
    have := hmono hjm'
    simp only at this
    linarith

end Miao.NumericalMethods

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Perturbation methods: recursive utility with unit EIS (Miao, §11.4, pp. 366–369)

Miao, §11.4 (the example of Hansen, Heaton and Li (2008)): recursive utility (11.3)
`V_t = [(1 − β) C_t^{1−ρ} + β R_t(V_{t+1})^{1−ρ}]^{1/(1−ρ)}`,
`R_t(V_{t+1}) = (E_t V_{t+1}^{1−γ})^{1/(1−γ)}`, is solved by perturbing the EIS parameter `ρ`
around the special case `ρ = 1`.

* `eq_11_4`: in logs, `v_t = ln(V_t/C_t)` satisfies (11.4)
  `v_t = (1 − ρ)^{−1} ln((1 − β) + β exp[(1 − ρ) Q_t(v_{t+1} + c_{t+1} − c_t)])`,
  `Q_t(y) = (1 − γ)^{−1} ln E_t exp[(1 − γ) y]` (`nqQ`; `nqCertEquiv` is `R_t`).
* `eq_11_5`: as `ρ → 1` the right side of (11.4) tends to `β Q_t(·)`: the unit-EIS equation
  (11.5) `v_t = β Q_t(v_{t+1} + c_{t+1} − c_t)`.
* `eq_11_7_s` (the perturbation step, in `s = 1 − ρ`): if `s v(s) = ln((1 − β) + β e^{s q(s)})`
  near `s = 0` (this is (11.4) multiplied by `1 − ρ`, i.e. `F(v_t(ρ), v_{t+1}(ρ), ρ) = 0`, with
  `q(s) = Q_t(v_{t+1}(ρ) + c_{t+1} − c_t)`) and `v`, `q` are twice differentiable, then
  differentiating twice at `s = 0` gives `v(0) = β q(0)` ((11.5)) and
  `v'(0) = β q'(0) + β(1 − β) q(0)²/2`. `eq_11_7` restates this in `ρ` as the book's (11.7)
  `v_t'(1) = −β(1 − β)/2 · Q_t(·)² + β Ẽ_t v_{t+1}'(1)`, given `q'(0) = −Ẽ_t v_{t+1}'(1)`.
* `nq_pert_taylor_first_order`: the first-order approximation `v_t(ρ) ≃ v_t(1) + (ρ − 1)v_t'(1)`
  has error `o(ρ − 1)`.
* `nq_Q_hasDerivAt`: the derivative of `Q_t` along `Y₀ + s Y₁` at `s = 0` is the expectation
  of `Y₁` under the tilted density `e^{(1−γ)Y₀}/E e^{(1−γ)Y₀}` (differentiation under the
  integral sign, with an integrable dominating function): this is the book's `Ẽ_t`, whose
  density `V_{t+1}(1)^{1−γ}/E_t V_{t+1}(1)^{1−γ}` equals `e^{(1−γ)Y₀}/E_t e^{(1−γ)Y₀}` for
  `Y₀ = v_{t+1}(1) + c_{t+1} − c_t = ln(V_{t+1}(1)/C_t)`.

**Departures.** Expectations `E_t` are integrals over a probability space `(Ω, P)` (next-period
shocks). The book's `F₁, F₂, F₃` chain rule is replaced by differentiating the identity
`s v(s) = h(s q(s))`, `h(u) = ln((1 − β) + β eᵘ)`; the smoothness of `ρ ↦ v_t(ρ)` is assumed as
in the book. `nq_Q_hasDerivAt` treats families affine in `s`, which is what the first
derivative sees. The closed form for the example is in `NQPerturbationExercise`.
-/

namespace Miao.NumericalMethods

open MeasureTheory Filter Topology Asymptotics

/-- Miao, p. 367: the certainty equivalent `R_t(V_{t+1}) = (E_t V_{t+1}^{1−γ})^{1/(1−γ)}`. -/
noncomputable def nqCertEquiv {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (V : Ω → ℝ) : ℝ :=
  (∫ ω, V ω ^ (1 - γ) ∂P) ^ (1 / (1 - γ))

/-- Miao, p. 368: `Q_t(y) = (1 − γ)^{−1} ln E_t exp[(1 − γ) y]`. -/
noncomputable def nqQ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (y : Ω → ℝ) : ℝ :=
  1 / (1 - γ) * Real.log (∫ ω, Real.exp ((1 - γ) * y ω) ∂P)

/-- Miao, (11.4), p. 368: with `V_t` given by (11.3) from `C_t > 0` and a positive next-period
utility `V_{t+1}`, `v_t = ln(V_t/C_t)` satisfies
`v_t = (1 − ρ)^{−1} ln((1 − β) + β exp[(1 − ρ) Q_t(v_{t+1} + c_{t+1} − c_t)])`,
where `v_{t+1} = ln(V_{t+1}/C_{t+1})`, `c = ln C`. -/
theorem eq_11_4 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {β γ ρ C : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : γ ≠ 1) (hρ : ρ ≠ 1) (hC : 0 < C)
    {V' C' : Ω → ℝ} (hV' : ∀ ω, 0 < V' ω) (hC' : ∀ ω, 0 < C' ω)
    (hint : Integrable (fun ω => V' ω ^ (1 - γ)) P) :
    Real.log (((1 - β) * C ^ (1 - ρ) + β * nqCertEquiv P γ V' ^ (1 - ρ)) ^ (1 / (1 - ρ)) / C) =
      1 / (1 - ρ) * Real.log ((1 - β) + β * Real.exp ((1 - ρ) *
        nqQ P γ (fun ω => Real.log (V' ω / C' ω) + Real.log (C' ω) - Real.log C))) := by
  have hγ' : (1 - γ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  have hρ' : (1 - ρ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  set I : ℝ := ∫ ω, V' ω ^ (1 - γ) ∂P
  have hVexp : ∀ ω, V' ω ^ (1 - γ) = Real.exp ((1 - γ) * Real.log (V' ω)) := fun ω => by
    rw [Real.rpow_def_of_pos (hV' ω), mul_comm]
  have hI : 0 < I := by
    have hint' : Integrable (fun ω => Real.exp ((1 - γ) * Real.log (V' ω))) P := by
      simpa only [hVexp] using hint
    simpa only [I, hVexp] using integral_exp_pos hint'
  -- the integral defining `Q_t`
  have hy : ∀ ω, Real.exp ((1 - γ) * (Real.log (V' ω / C' ω) + Real.log (C' ω) - Real.log C)) =
      V' ω ^ (1 - γ) * Real.exp (-(1 - γ) * Real.log C) := by
    intro ω
    rw [hVexp, ← Real.exp_add, Real.log_div (hV' ω).ne' (hC' ω).ne']
    congr 1; ring
  have hM : ∫ ω, Real.exp ((1 - γ) *
      (Real.log (V' ω / C' ω) + Real.log (C' ω) - Real.log C)) ∂P =
      I * Real.exp (-(1 - γ) * Real.log C) := by
    simp only [hy]
    rw [integral_mul_const]
  have hQ : nqQ P γ (fun ω => Real.log (V' ω / C' ω) + Real.log (C' ω) - Real.log C) =
      1 / (1 - γ) * Real.log I - Real.log C := by
    rw [nqQ, hM, Real.log_mul hI.ne' (Real.exp_pos _).ne', Real.log_exp]
    field_simp
    ring
  -- `log R = log I / (1 − γ)`
  set R : ℝ := nqCertEquiv P γ V'
  have hR : 0 < R := Real.rpow_pos_of_pos hI _
  have hlogR : Real.log R = 1 / (1 - γ) * Real.log I := by
    simp only [R, nqCertEquiv]
    rw [Real.log_rpow hI]
  set S : ℝ := (1 - β) * C ^ (1 - ρ) + β * R ^ (1 - ρ)
  have hS : 0 < S := by
    have := Real.rpow_pos_of_pos hC (1 - ρ)
    have := Real.rpow_pos_of_pos hR (1 - ρ)
    have : 0 < 1 - β := by linarith
    positivity
  have hinside : (1 - β) + β * Real.exp ((1 - ρ) *
      nqQ P γ (fun ω => Real.log (V' ω / C' ω) + Real.log (C' ω) - Real.log C)) =
      S / Real.exp ((1 - ρ) * Real.log C) := by
    rw [hQ, ← hlogR]
    simp only [S]
    rw [Real.rpow_def_of_pos hC, Real.rpow_def_of_pos hR]
    have he : Real.exp ((1 - ρ) * (Real.log R - Real.log C)) =
        Real.exp (Real.log R * (1 - ρ)) / Real.exp ((1 - ρ) * Real.log C) := by
      rw [← Real.exp_sub]; congr 1; ring
    rw [he, mul_comm (Real.log C) (1 - ρ)]
    field_simp
  rw [hinside, Real.log_div hS.ne' (Real.exp_pos _).ne', Real.log_exp,
    Real.log_div (Real.rpow_pos_of_pos hS _).ne' hC.ne', Real.log_rpow hS]
  field_simp

/-- Miao, (11.5), p. 368: as `ρ → 1` the right side of (11.4) tends to `β Q`: for every value
`q` of `Q_t(v_{t+1} + c_{t+1} − c_t)`,
`(1 − ρ)^{−1} ln((1 − β) + β e^{(1−ρ)q}) → β q` (the unit-EIS equation (11.5)); no restriction
on `β` is needed. -/
theorem eq_11_5 (β q : ℝ) :
    Tendsto (fun ρ => 1 / (1 - ρ) * Real.log ((1 - β) + β * Real.exp ((1 - ρ) * q)))
      (𝓝[≠] 1) (𝓝 (β * q)) := by
  have hk : HasDerivAt (fun s => (1 - β) + β * Real.exp (s * q)) (β * (Real.exp (0 * q) * q)) 0 :=
    (((hasDerivAt_id (0 : ℝ)).mul_const q).exp.const_mul β).const_add (1 - β) |>.congr_deriv
      (by simp)
  have hk0 : (1 - β) + β * Real.exp (0 * q) = 1 := by simp
  have hg : HasDerivAt (fun s => Real.log ((1 - β) + β * Real.exp (s * q))) (β * q) 0 := by
    have := hk.log (by rw [hk0]; exact one_ne_zero)
    rw [hk0] at this
    simpa using this
  have hslope := hg.tendsto_slope_zero
  have hsub : Tendsto (fun ρ : ℝ => 1 - ρ) (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact ((continuous_const.sub continuous_id).tendsto' 1 0 (by simp)).mono_left
        nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall fun ρ hρ => sub_ne_zero.mpr (Ne.symm hρ)
  refine (hslope.comp hsub).congr fun ρ => ?_
  simp only [Function.comp_apply, zero_add, smul_eq_mul, zero_mul, Real.exp_zero, mul_one,
    sub_add_cancel, Real.log_one, sub_zero, one_div]

/-- Miao, p. 369 ("by Taylor expansion, the approximate solution is given by
`v_t(ρ) ≃ v_t(1) + (ρ − 1) v_t'(1)`"): if `v_t` is differentiable at `ρ = 1` the error of the
first-order approximation is `o(ρ − 1)`. -/
theorem nq_pert_taylor_first_order {v : ℝ → ℝ} {v1 : ℝ} (hv : HasDerivAt v v1 1) :
    (fun ρ => v ρ - (v 1 + (ρ - 1) * v1)) =o[𝓝 1] fun ρ => ρ - 1 := by
  have h := hasDerivAt_iff_isLittleO.mp hv
  refine h.congr_left fun ρ => ?_
  simp only [smul_eq_mul]
  ring

/-- `h(u) = ln((1 − β) + β eᵘ)` has derivative `β eᵘ/((1 − β) + β eᵘ)`. -/
theorem nq_h_hasDerivAt {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (u : ℝ) :
    HasDerivAt (fun u => Real.log ((1 - β) + β * Real.exp u))
      (β * Real.exp u / ((1 - β) + β * Real.exp u)) u := by
  have hpos : 0 < (1 - β) + β * Real.exp u := by
    have := Real.exp_pos u; nlinarith
  exact ((Real.hasDerivAt_exp u).const_mul β).const_add (1 - β) |>.log hpos.ne'

/-- `h'(u) = β eᵘ/((1 − β) + β eᵘ)` has derivative `β(1 − β)` at `u = 0`. -/
theorem nq_h'_hasDerivAt_zero {β : ℝ} :
    HasDerivAt (fun u => β * Real.exp u / ((1 - β) + β * Real.exp u)) (β * (1 - β)) 0 := by
  have h1 := (Real.hasDerivAt_exp 0).const_mul β
  have h2 := ((Real.hasDerivAt_exp 0).const_mul β).const_add (1 - β)
  have hd := h1.div h2 (by simp)
  simp only [Real.exp_zero, mul_one, sub_add_cancel, one_pow, div_one] at hd
  convert hd using 1
  ring

/-- Miao, (11.7), p. 369 (the perturbation step, in `s = 1 − ρ`): if
`s v(s) = ln((1 − β) + β e^{s q(s)})` for `s` near `0` — equation (11.4) multiplied by `1 − ρ`,
i.e. `F(v_t(ρ), v_{t+1}(ρ), ρ) = 0`, with `v(s) = v_t(1 − s)` and
`q(s) = Q_t(v_{t+1}(1 − s) + c_{t+1} − c_t)` — and `v`, `q` are twice differentiable at `0`,
then differentiating once and twice at `s = 0` gives `v(0) = β q(0)` (equation (11.5)) and
`v'(0) = β q'(0) + β(1 − β) q(0)²/2`. -/
theorem eq_11_7_s {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {v q v1 q1 : ℝ → ℝ} {v2 q2 : ℝ}
    (hv : ∀ᶠ s in 𝓝 0, HasDerivAt v (v1 s) s) (hq : ∀ᶠ s in 𝓝 0, HasDerivAt q (q1 s) s)
    (hv1 : HasDerivAt v1 v2 0) (hq1 : HasDerivAt q1 q2 0)
    (hid : ∀ᶠ s in 𝓝 0, s * v s = Real.log ((1 - β) + β * Real.exp (s * q s))) :
    v 0 = β * q 0 ∧ v1 0 = β * q1 0 + β * (1 - β) / 2 * q 0 ^ 2 := by
  set hp : ℝ → ℝ := fun u => β * Real.exp u / ((1 - β) + β * Real.exp u)
  -- first derivatives of both sides agree near `0`
  have hD : ∀ᶠ s in 𝓝 0, v s + s * v1 s = hp (s * q s) * (q s + s * q1 s) := by
    filter_upwards [hv, hq, eventually_eventually_nhds.mpr hid] with s hvs hqs hids
    have hL : HasDerivAt (fun t => t * v t) (v s + s * v1 s) s :=
      ((hasDerivAt_id s).mul hvs).congr_deriv (by simp)
    have hm : HasDerivAt (fun t => t * q t) (q s + s * q1 s) s :=
      ((hasDerivAt_id s).mul hqs).congr_deriv (by simp)
    have hR : HasDerivAt (fun t => Real.log ((1 - β) + β * Real.exp (t * q t)))
        (hp (s * q s) * (q s + s * q1 s)) s :=
      by have h3 := (nq_h_hasDerivAt hβ0 hβ1 (s * q s)).comp s hm; exact h3
    exact hL.unique (hR.congr_of_eventuallyEq hids)
  have hp0 : hp 0 = β := by simp [hp]
  refine ⟨?_, ?_⟩
  · have := hD.self_of_nhds
    simp only [zero_mul, add_zero, hp0] at this
    exact this
  · -- second derivatives at `0`
    have hv0 : HasDerivAt v (v1 0) 0 := hv.self_of_nhds
    have hq0 : HasDerivAt q (q1 0) 0 := hq.self_of_nhds
    have hDL : HasDerivAt (fun s => v s + s * v1 s) (2 * v1 0) 0 :=
      (hv0.add ((hasDerivAt_id 0).mul hv1)).congr_deriv (by simp; ring)
    have hm0 : HasDerivAt (fun t => t * q t) (q 0) 0 :=
      ((hasDerivAt_id 0).mul hq0).congr_deriv (by simp)
    have hhp : HasDerivAt (fun s => hp (s * q s)) (β * (1 - β) * q 0) 0 := by
      have := (nq_h'_hasDerivAt_zero (β := β)).comp_of_eq 0 hm0 (by simp)
      exact this
    have hlin : HasDerivAt (fun s => q s + s * q1 s) (2 * q1 0) 0 :=
      (hq0.add ((hasDerivAt_id 0).mul hq1)).congr_deriv (by simp; ring)
    have hDR : HasDerivAt (fun s => hp (s * q s) * (q s + s * q1 s))
        (β * (1 - β) * q 0 * q 0 + β * (2 * q1 0)) 0 := by
      have := hhp.mul hlin
      simp only [zero_mul, hp0, add_zero] at this
      exact this
    have := hDL.unique (hDR.congr_of_eventuallyEq hD)
    linarith

/-- Miao, (11.7), p. 369: in terms of `ρ` (`v_t(ρ) = v(1 − ρ)`, so `v_t'(1) = −v'(0)`), and with
`q'(0) = −Ẽ_t v_{t+1}'(1)` (`nq_Q_hasDerivAt`),
`v_t'(1) = −β(1 − β)/2 · [Q_t(v_{t+1}(1) + c_{t+1} − c_t)]² + β Ẽ_t v_{t+1}'(1)`. -/
theorem eq_11_7 {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {v q v1 q1 : ℝ → ℝ} {v2 q2 Et : ℝ}
    (hv : ∀ᶠ s in 𝓝 0, HasDerivAt v (v1 s) s) (hq : ∀ᶠ s in 𝓝 0, HasDerivAt q (q1 s) s)
    (hv1 : HasDerivAt v1 v2 0) (hq1 : HasDerivAt q1 q2 0)
    (hid : ∀ᶠ s in 𝓝 0, s * v s = Real.log ((1 - β) + β * Real.exp (s * q s)))
    (hE : q1 0 = -Et) :
    -v1 0 = -(β * (1 - β)) / 2 * q 0 ^ 2 + β * Et := by
  have h := (eq_11_7_s hβ0 hβ1 hv hq hv1 hq1 hid).2
  rw [h, hE]
  ring

/-- Miao, p. 369 (the tilted expectation `Ẽ_t`): along `Y₀ + s Y₁`,
`d/ds Q_t(Y₀ + s Y₁)|_{s=0} = E[Y₁ e^{(1−γ)Y₀}]/E[e^{(1−γ)Y₀}]`, the expectation of `Y₁` under the
density `e^{(1−γ)Y₀}/E e^{(1−γ)Y₀}` (given an integrable dominating function). -/
theorem nq_Q_hasDerivAt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ : ℝ} (hγ : γ ≠ 1) {Y0 Y1 : Ω → ℝ} (hY0 : AEStronglyMeasurable Y0 P)
    (hY1 : AEStronglyMeasurable Y1 P)
    (hB : Integrable (fun ω => Real.exp ((1 - γ) * Y0 ω + |1 - γ| * |Y1 ω|)) P)
    (hB' : Integrable (fun ω => |Y1 ω| * Real.exp ((1 - γ) * Y0 ω + |1 - γ| * |Y1 ω|)) P) :
    HasDerivAt (fun s => nqQ P γ (fun ω => Y0 ω + s * Y1 ω))
      ((∫ ω, Y1 ω * Real.exp ((1 - γ) * Y0 ω) ∂P) / ∫ ω, Real.exp ((1 - γ) * Y0 ω) ∂P) 0 := by
  set c : ℝ := 1 - γ with hc
  have hc0 : c ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  set F : ℝ → Ω → ℝ := fun s ω => Real.exp (c * (Y0 ω + s * Y1 ω))
  set F' : ℝ → Ω → ℝ := fun s ω => c * Y1 ω * Real.exp (c * (Y0 ω + s * Y1 ω))
  have hmeasF : ∀ s, AEStronglyMeasurable (F s) P := fun s =>
    Real.continuous_exp.comp_aestronglyMeasurable ((hY0.add (hY1.const_mul s)).const_mul c)
  have hle : ∀ s ∈ Metric.ball (0 : ℝ) 1, ∀ ω,
      Real.exp (c * (Y0 ω + s * Y1 ω)) ≤ Real.exp (c * Y0 ω + |c| * |Y1 ω|) := by
    intro s hs ω
    apply Real.exp_le_exp.mpr
    have hs' : |s| ≤ 1 := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hs; exact hs.le
    have : c * (s * Y1 ω) ≤ |c| * |Y1 ω| := by
      calc c * (s * Y1 ω) ≤ |c * (s * Y1 ω)| := le_abs_self _
        _ = |c| * (|s| * |Y1 ω|) := by rw [abs_mul, abs_mul]
        _ ≤ |c| * (1 * |Y1 ω|) := by gcongr
        _ = |c| * |Y1 ω| := by ring
    linarith [mul_add c (Y0 ω) (s * Y1 ω)]
  have hint0 : Integrable (F 0) P := by
    refine hB.mono' (hmeasF 0) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hle 0 (Metric.mem_ball_self one_pos) ω
  have hmeasF' : AEStronglyMeasurable (F' 0) P :=
    ((hY1.const_mul c).mul (hmeasF 0))
  have hbound : ∀ᵐ ω ∂P, ∀ s ∈ Metric.ball (0 : ℝ) 1,
      ‖F' s ω‖ ≤ |c| * (|Y1 ω| * Real.exp (c * Y0 ω + |c| * |Y1 ω|)) := by
    refine ae_of_all _ fun ω s hs => ?_
    simp only [F', Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have := hle s hs ω
    have h1 : 0 ≤ |c| * |Y1 ω| := by positivity
    calc |c| * |Y1 ω| * Real.exp (c * (Y0 ω + s * Y1 ω))
        ≤ |c| * |Y1 ω| * Real.exp (c * Y0 ω + |c| * |Y1 ω|) :=
          mul_le_mul_of_nonneg_left this h1
      _ = |c| * (|Y1 ω| * Real.exp (c * Y0 ω + |c| * |Y1 ω|)) := by ring
  have hdiff : ∀ᵐ ω ∂P, ∀ s ∈ Metric.ball (0 : ℝ) 1, HasDerivAt (F · ω) (F' s ω) s := by
    refine ae_of_all _ fun ω s _ => ?_
    have := ((((hasDerivAt_id s).mul_const (Y1 ω)).const_add (Y0 ω)).const_mul c).exp
    exact this.congr_deriv (by simp [F']; ring)
  have hmain := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds (0 : ℝ) one_pos) (Eventually.of_forall hmeasF) hint0 hmeasF'
    hbound (hB'.const_mul |c|) hdiff).2
  have hF0 : ∫ ω, F 0 ω ∂P = ∫ ω, Real.exp (c * Y0 ω) ∂P := by simp [F]
  have hpos : 0 < ∫ ω, F 0 ω ∂P := integral_exp_pos hint0
  have hF'0 : ∫ ω, F' 0 ω ∂P = c * ∫ ω, Y1 ω * Real.exp (c * Y0 ω) ∂P := by
    rw [← integral_const_mul]
    congr 1; funext ω; simp [F']; ring
  have hlog := (hmain.log hpos.ne').const_mul (1 / c)
  refine hlog.congr_deriv ?_
  rw [hF'0, hF0]
  rw [hF0] at hpos
  field_simp

end Miao.NumericalMethods

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Hansen–Heaton–Li example in closed form (Miao, §11.4, pp. 367–369; Exercise 11.2)

Miao, §11.4: aggregate consumption `ln(C_{t+1}/C_t) = μ_c + x_t + σ_c ε_{c,t+1}`,
`x_{t+1} = φ x_t + σ_x ε_{x,t+1}` with independent standard normal shocks (`nqShock`, the law
of `(ε_c, ε_x)`). We compute the unit-EIS solution (11.6) and complete the first-order
perturbation (Exercise 11.2).

* `nq_gauss_exp_integral`, `nq_shock_exp`: the normal moment generating function.
* `eq_11_6_mgf`: `ln E_t exp[(1 − γ)(v_{t+1} + c_{t+1} − c_t)]` for the guess `v = A x + μ_v`
  (the displayed computation on p. 368).
* `eq_11_6`: the guess (11.6) solves (11.5) for all `x` iff `A = β/(1 − βφ)` and
  `μ_v = β/(1 − β) [μ_c + (1 − γ)/2 ((βσ_x/(1 − βφ))² + σ_c²)]`.
* `nq_gauss_tilt`, `nq_gauss_quad`, `nq_ex_11_2_tilt`: under the tilted measure `Ẽ_t` (density
  `e^{(1−γ)(v_{t+1}(1) + Δc)}/E_t[·]`, `nqTilt`), `ε_x` has mean `(1 − γ) A σ_x`, and the tilted
  expectation of a quadratic `−A_d x'²/2 + B_d x' + μ_d` in `x' = φx + σ_x ε_x` is
  `−A_d((φx + κ)² + σ_x²)/2 + B_d(φx + κ) + μ_d`, `κ = (1 − γ) A σ_x²`.
* `nq_ex_11_2_Q`, `nq_ex_11_2_a`, `nq_ex_11_2_b`: `Q_t(v_{t+1}(1) + Δc) = a x + b`,
  `a = Aφ + 1 = 1/(1 − βφ)`, `b = μ_v/β`.
* `nq_ex_11_2_match` and **`ex_11_2`** (Exercise 11.2): the conjecture
  `v_t'(1) = −A_d x_t²/2 + B_d x_t + μ_d` solves (11.7) for all `x_t` iff
  `A_d = β(1 − β)/((1 − βφ)²(1 − βφ²))`,
  `B_d = −β[(1 − β)μ_v/(β(1 − βφ)) + A_d φ κ]/(1 − βφ)`,
  `μ_d = [−β(1 − β)(μ_v/β)²/2 − βA_d(κ² + σ_x²)/2 + βB_d κ]/(1 − β)`,
  `κ = (1 − γ)βσ_x²/(1 − βφ)`.

**Departures and corrections.** The book uses `ρ` both for the EIS parameter of (11.3) and for
the autocorrelation of `x_t`; we write `φ` for the latter (so the book's `A = β/(1 − βρ)` is
`β/(1 − βφ)`). The book's "`A` and `μ_c` are constants to be determined" should read `μ_v`.
-/

namespace Miao.NumericalMethods

open MeasureTheory Real ProbabilityTheory

/-- Miao, p. 367: the law of the next-period shocks `(ε_c, ε_x)`, independent standard
normals. -/
noncomputable abbrev nqShock : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)

/-- The standard normal moment generating function: `E e^{bε} = e^{b²/2}`. -/
theorem nq_gauss_exp_integral (b : ℝ) :
    ∫ e, Real.exp (b * e) ∂(gaussianReal 0 1) = Real.exp (b ^ 2 / 2) := by
  have h := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) b
  simp only [mgf, id] at h
  rw [h]
  congr 1
  simp

/-- `E exp(a + b ε_c + c ε_x) = exp(a + (b² + c²)/2)`. -/
theorem nq_shock_exp (a b c : ℝ) :
    ∫ e, Real.exp (a + b * e.1 + c * e.2) ∂nqShock = Real.exp (a + (b ^ 2 + c ^ 2) / 2) := by
  have hfun : (fun e : ℝ × ℝ => Real.exp (a + b * e.1 + c * e.2)) =
      fun e => Real.exp a * (Real.exp (b * e.1) * Real.exp (c * e.2)) := by
    funext e; rw [Real.exp_add, Real.exp_add]; ring
  rw [hfun, integral_const_mul,
    integral_prod_mul (fun x => Real.exp (b * x)) (fun y => Real.exp (c * y)),
    nq_gauss_exp_integral, nq_gauss_exp_integral, ← Real.exp_add, ← Real.exp_add]
  congr 1; ring

/-- Miao, p. 368 (the displayed computation): for the guess `v = A x + μ_v`,
`ln E_t exp[(1 − γ)(v_{t+1} + c_{t+1} − c_t)]
  = (1 − γ)[(Aφ + 1)x_t + μ_v + μ_c] + (1 − γ)²/2 [(Aσ_x)² + σ_c²]`,
with `x_{t+1} = φ x_t + σ_x ε_x` and `c_{t+1} − c_t = μ_c + x_t + σ_c ε_c`. -/
theorem eq_11_6_mgf (γ A μv μc σc σx φ x : ℝ) :
    Real.log (∫ e, Real.exp ((1 - γ) * (A * (φ * x + σx * e.2) + μv + μc + x + σc * e.1))
      ∂nqShock) =
      (1 - γ) * ((A * φ + 1) * x + μv + μc) + (1 - γ) ^ 2 / 2 * ((A * σx) ^ 2 + σc ^ 2) := by
  have hfun : (fun e : ℝ × ℝ =>
      Real.exp ((1 - γ) * (A * (φ * x + σx * e.2) + μv + μc + x + σc * e.1))) =
      fun e => Real.exp ((1 - γ) * ((A * φ + 1) * x + μv + μc) + ((1 - γ) * σc) * e.1 +
        ((1 - γ) * A * σx) * e.2) := by
    funext e; congr 1; ring
  rw [hfun, nq_shock_exp, Real.log_exp]
  ring

/-- Miao, (11.6), p. 368: the guess `v_t = A x_t + μ_v` solves the unit-EIS equation (11.5)
`v_t = β/(1 − γ) ln E_t exp[(1 − γ)(v_{t+1} + c_{t+1} − c_t)]` for every `x_t` iff
`A = β/(1 − βφ)` and `μ_v = β/(1 − β) [μ_c + (1 − γ)/2 ((βσ_x/(1 − βφ))² + σ_c²)]`. -/
theorem eq_11_6 {β γ φ : ℝ} (hβ : β ≠ 1) (hγ : γ ≠ 1) (hβφ : β * φ ≠ 1) (μc σc σx A μv : ℝ) :
    (∀ x, A * x + μv = β / (1 - γ) * Real.log (∫ e, Real.exp ((1 - γ) *
      (A * (φ * x + σx * e.2) + μv + μc + x + σc * e.1)) ∂nqShock)) ↔
    A = β / (1 - β * φ) ∧
      μv = β / (1 - β) * (μc + (1 - γ) / 2 * ((β * σx / (1 - β * φ)) ^ 2 + σc ^ 2)) := by
  have hγ' : 1 - γ ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  have hβ' : 1 - β ≠ 0 := sub_ne_zero.mpr (Ne.symm hβ)
  have hβφ' : 1 - β * φ ≠ 0 := sub_ne_zero.mpr (Ne.symm hβφ)
  have hR : ∀ x, β / (1 - γ) * Real.log (∫ e, Real.exp ((1 - γ) *
      (A * (φ * x + σx * e.2) + μv + μc + x + σc * e.1)) ∂nqShock) =
      β * ((A * φ + 1) * x + μv + μc) + β * (1 - γ) / 2 * ((A * σx) ^ 2 + σc ^ 2) := by
    intro x
    rw [eq_11_6_mgf]
    field_simp
  simp_rw [hR]
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    have hA : A * (1 - β * φ) = β := by linarith
    have hA' : A = β / (1 - β * φ) := by rw [eq_div_iff hβφ']; exact hA
    refine ⟨hA', ?_⟩
    have hm : μv * (1 - β) = β * (μc + (1 - γ) / 2 * ((A * σx) ^ 2 + σc ^ 2)) := by linarith
    rw [← eq_div_iff hβ'] at hm
    rw [hm, hA']
    field_simp
  · rintro ⟨hA, hμ⟩ x
    have hA1 : A * (1 - β * φ) = β := by rw [hA]; field_simp
    have hσ : (β * σx / (1 - β * φ)) = A * σx := by rw [hA]; ring
    rw [hσ] at hμ
    have hμ1 : μv * (1 - β) = β * (μc + (1 - γ) / 2 * ((A * σx) ^ 2 + σc ^ 2)) := by
      rw [hμ]; field_simp
    linear_combination x * hA1 + hμ1

/-- Exponential tilting of the standard normal:
`E[f(ε) e^{kε}] = e^{k²/2} E_{N(k,1)}[f]`. -/
theorem nq_gauss_tilt (k : ℝ) (f : ℝ → ℝ) :
    ∫ e, f e * Real.exp (k * e) ∂(gaussianReal 0 1) =
      Real.exp (k ^ 2 / 2) * ∫ e, f e ∂(gaussianReal k 1) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero, ← integral_const_mul]
  congr 1
  funext e
  simp only [gaussianPDFReal_def, smul_eq_mul, NNReal.coe_one, mul_one, sub_zero]
  have : Real.exp (-e ^ 2 / 2) * Real.exp (k * e) =
      Real.exp (k ^ 2 / 2) * Real.exp (-(e - k) ^ 2 / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  linear_combination ((√(2 * π))⁻¹ * f e) * this

/-- Quadratic moments of `N(m, 1)`: `E[a y² + b y + c] = a(1 + m²) + b m + c`. -/
theorem nq_gauss_quad (m a b c : ℝ) :
    ∫ y, (a * y ^ 2 + b * y + c) ∂(gaussianReal m 1) = a * (1 + m ^ 2) + b * m + c := by
  have hI2 : Integrable (fun y : ℝ => y ^ 2) (gaussianReal m 1) := by
    simpa using (memLp_id_gaussianReal (μ := m) (v := 1) 2).integrable_sq
  have hI1 : Integrable (fun y : ℝ => y) (gaussianReal m 1) := by
    have := MemLp.integrable (by norm_num) (memLp_id_gaussianReal (μ := m) (v := 1) 1)
    exact this
  have hvar := variance_id_gaussianReal (μ := m) (v := 1)
  rw [variance_eq_sub (memLp_id_gaussianReal 2)] at hvar
  simp only [Pi.pow_apply, id] at hvar
  rw [integral_id_gaussianReal] at hvar
  have h2 : ∫ y, y ^ 2 ∂(gaussianReal m 1) = 1 + m ^ 2 := by
    simp only [NNReal.coe_one] at hvar; linarith
  have e1 : ∫ y, (a * y ^ 2 + b * y + c) ∂(gaussianReal m 1) =
      ∫ y, (a * y ^ 2 + b * y) ∂(gaussianReal m 1) + ∫ _, c ∂(gaussianReal m 1) :=
    integral_add ((hI2.const_mul a).add (hI1.const_mul b)) (integrable_const c)
  have e2 : ∫ y, (a * y ^ 2 + b * y) ∂(gaussianReal m 1) =
      ∫ y, a * y ^ 2 ∂(gaussianReal m 1) + ∫ y, b * y ∂(gaussianReal m 1) :=
    integral_add (hI2.const_mul a) (hI1.const_mul b)
  rw [e1, e2, integral_const_mul, integral_const_mul, h2, integral_id_gaussianReal,
    integral_const]
  simp

/-- Miao, p. 369: the tilted expectation `Ẽ_t[G] = E_t[G e^{c Y}]/E_t[e^{c Y}]`, `c = 1 − γ`,
`Y = v_{t+1}(1) + c_{t+1} − c_t` (the density `V_{t+1}(1)^{1−γ}/E_t V_{t+1}(1)^{1−γ}`). -/
noncomputable def nqTilt (c : ℝ) (Y G : ℝ × ℝ → ℝ) : ℝ :=
  (∫ e, G e * Real.exp (c * Y e) ∂nqShock) / ∫ e, Real.exp (c * Y e) ∂nqShock

/-- Miao, p. 369 (Exercise 11.2, the tilted expectation): with `Y = v_{t+1}(1) + Δc`
for `v(1) = A x + μ_v`, the tilted expectation of `−A_d x'²/2 + B_d x' + μ_d`,
`x' = φx + σ_x ε_x`, is `−A_d((φx + κ)² + σ_x²)/2 + B_d(φx + κ) + μ_d`,
`κ = (1 − γ) A σ_x²` (under `Ẽ_t`, `ε_x ~ N((1 − γ)Aσ_x, 1)`). -/
theorem nq_ex_11_2_tilt (γ A μv μc σc σx φ x Ad Bd μd : ℝ) :
    nqTilt (1 - γ) (fun e => A * (φ * x + σx * e.2) + μv + μc + x + σc * e.1)
      (fun e => -Ad / 2 * (φ * x + σx * e.2) ^ 2 + Bd * (φ * x + σx * e.2) + μd) =
      -Ad / 2 * ((φ * x + (1 - γ) * A * σx ^ 2) ^ 2 + σx ^ 2) +
        Bd * (φ * x + (1 - γ) * A * σx ^ 2) + μd := by
  set a0 : ℝ := (1 - γ) * ((A * φ + 1) * x + μv + μc)
  set b : ℝ := (1 - γ) * σc
  set k : ℝ := (1 - γ) * A * σx
  have hY : ∀ e : ℝ × ℝ, (1 - γ) * (A * (φ * x + σx * e.2) + μv + μc + x + σc * e.1) =
      a0 + b * e.1 + k * e.2 := fun e => by simp only [a0, b, k]; ring
  set G' : ℝ → ℝ := fun t => -Ad / 2 * (φ * x + σx * t) ^ 2 + Bd * (φ * x + σx * t) + μd
  have hnum : (fun e : ℝ × ℝ => (-Ad / 2 * (φ * x + σx * e.2) ^ 2 + Bd * (φ * x + σx * e.2) + μd)
      * Real.exp ((1 - γ) * (A * (φ * x + σx * e.2) + μv + μc + x + σc * e.1))) =
      fun e => (Real.exp a0 * Real.exp (b * e.1)) * (G' e.2 * Real.exp (k * e.2)) := by
    funext e; rw [hY, Real.exp_add, Real.exp_add]; simp only [G']; ring
  have hden : (fun e : ℝ × ℝ =>
      Real.exp ((1 - γ) * (A * (φ * x + σx * e.2) + μv + μc + x + σc * e.1))) =
      fun e => (Real.exp a0 * Real.exp (b * e.1)) * Real.exp (k * e.2) := by
    funext e; rw [hY, Real.exp_add, Real.exp_add]
  unfold nqTilt
  rw [hnum, hden,
    integral_prod_mul (fun s => Real.exp a0 * Real.exp (b * s)) (fun t => G' t * Real.exp (k * t)),
    integral_prod_mul (fun s => Real.exp a0 * Real.exp (b * s)) (fun t => Real.exp (k * t)),
    nq_gauss_tilt k G', nq_gauss_exp_integral k]
  have hG' : ∀ t, G' t = (-Ad / 2 * σx ^ 2) * t ^ 2 + (-Ad * φ * x * σx + Bd * σx) * t +
      (-Ad / 2 * (φ * x) ^ 2 + Bd * φ * x + μd) := fun t => by simp only [G']; ring
  have hM : ∫ t, G' t ∂(gaussianReal k 1) = (-Ad / 2 * σx ^ 2) * (1 + k ^ 2) +
      (-Ad * φ * x * σx + Bd * σx) * k + (-Ad / 2 * (φ * x) ^ 2 + Bd * φ * x + μd) := by
    simp_rw [hG']
    exact nq_gauss_quad k _ _ _
  rw [hM]
  have hE1 : 0 < ∫ s, Real.exp a0 * Real.exp (b * s) ∂(gaussianReal 0 1) := by
    rw [integral_const_mul, nq_gauss_exp_integral]; positivity
  have hE2 : 0 < Real.exp (k ^ 2 / 2) := Real.exp_pos _
  rw [mul_div_mul_left _ _ hE1.ne', mul_div_cancel_left₀ _ hE2.ne']
  simp only [k]
  ring

/-- Miao, p. 369 (Exercise 11.2): at `ρ = 1`, `Q_t(v_{t+1}(1) + c_{t+1} − c_t) = a x_t + b` with
`a = Aφ + 1`, `b = μ_v + μ_c + (1 − γ)/2((Aσ_x)² + σ_c²)`. -/
theorem nq_ex_11_2_Q {γ : ℝ} (hγ : γ ≠ 1) (A μv μc σc σx φ x : ℝ) :
    nqQ nqShock γ (fun e => A * (φ * x + σx * e.2) + μv + μc + x + σc * e.1) =
      (A * φ + 1) * x + (μv + μc + (1 - γ) / 2 * ((A * σx) ^ 2 + σc ^ 2)) := by
  have hγ' : 1 - γ ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  rw [nqQ, eq_11_6_mgf]
  field_simp
  ring

/-- Miao, p. 368: with `A = β/(1 − βφ)`, `a = Aφ + 1 = 1/(1 − βφ)` (so `A = β a`). -/
theorem nq_ex_11_2_a {β φ A : ℝ} (hβφ : β * φ ≠ 1) (hA : A = β / (1 - β * φ)) :
    A * φ + 1 = 1 / (1 - β * φ) := by
  have hβφ' : 1 - β * φ ≠ 0 := sub_ne_zero.mpr (Ne.symm hβφ)
  rw [hA]; field_simp; ring

/-- Miao, p. 368: with `μ_v` from (11.6), `b = μ_v + μ_c + (1 − γ)/2((Aσ_x)² + σ_c²) = μ_v/β`. -/
theorem nq_ex_11_2_b {β γ φ A μv μc σc σx : ℝ} (hβ0 : β ≠ 0) (hβ : β ≠ 1)
    (hA : A = β / (1 - β * φ))
    (hμv : μv = β / (1 - β) * (μc + (1 - γ) / 2 * ((β * σx / (1 - β * φ)) ^ 2 + σc ^ 2))) :
    μv + μc + (1 - γ) / 2 * ((A * σx) ^ 2 + σc ^ 2) = μv / β := by
  have hβ' : 1 - β ≠ 0 := sub_ne_zero.mpr (Ne.symm hβ)
  have hσ : A * σx = β * σx / (1 - β * φ) := by rw [hA]; ring
  rw [hσ]
  set K : ℝ := μc + (1 - γ) / 2 * ((β * σx / (1 - β * φ)) ^ 2 + σc ^ 2)
  have hK : μv + μc + (1 - γ) / 2 * ((β * σx / (1 - β * φ)) ^ 2 + σc ^ 2) = μv + K := by
    simp only [K]; ring
  rw [hK, hμv]
  field_simp
  ring

/-- Miao, (11.7), p. 369 (Exercise 11.2, matching coefficients): for constants `a, b, κ`, the
quadratic `−A_d x²/2 + B_d x + μ_d` satisfies
`−A_d x²/2 + B_d x + μ_d = −β(1 − β)/2 (a x + b)² + β[−A_d((φx + κ)² + σ_x²)/2 + B_d(φx + κ) + μ_d]`
for every `x` iff `A_d = β(1 − β)a²/(1 − βφ²)`, `B_d = −β((1 − β)ab + A_d φ κ)/(1 − βφ)` and
`μ_d = (−β(1 − β)b²/2 − βA_d(κ² + σ_x²)/2 + βB_d κ)/(1 − β)`. -/
theorem nq_ex_11_2_match {β φ a b κ σx Ad Bd μd : ℝ} (hβ : β ≠ 1) (hβφ : β * φ ≠ 1)
    (hβφ2 : β * φ ^ 2 ≠ 1) :
    (∀ x, -Ad / 2 * x ^ 2 + Bd * x + μd = -(β * (1 - β)) / 2 * (a * x + b) ^ 2 +
      β * (-Ad / 2 * ((φ * x + κ) ^ 2 + σx ^ 2) + Bd * (φ * x + κ) + μd)) ↔
    Ad = β * (1 - β) * a ^ 2 / (1 - β * φ ^ 2) ∧
      Bd = -β * ((1 - β) * a * b + Ad * φ * κ) / (1 - β * φ) ∧
      μd = (-β * (1 - β) * b ^ 2 / 2 - β * Ad * (κ ^ 2 + σx ^ 2) / 2 + β * Bd * κ) / (1 - β) := by
  have hβ' : 1 - β ≠ 0 := sub_ne_zero.mpr (Ne.symm hβ)
  have hβφ' : 1 - β * φ ≠ 0 := sub_ne_zero.mpr (Ne.symm hβφ)
  have hβφ2' : 1 - β * φ ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hβφ2)
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    have hm := h (-1)
    have eA : Ad * (1 - β * φ ^ 2) = β * (1 - β) * a ^ 2 := by
      linear_combination (-1 : ℝ) * h1 + (-1 : ℝ) * hm + 2 * h0
    have eB : Bd * (1 - β * φ) = -β * ((1 - β) * a * b + Ad * φ * κ) := by
      linear_combination (1 / 2 : ℝ) * h1 - (1 / 2 : ℝ) * hm
    have eM : μd * (1 - β) =
        -β * (1 - β) * b ^ 2 / 2 - β * Ad * (κ ^ 2 + σx ^ 2) / 2 + β * Bd * κ := by
      linear_combination h0
    refine ⟨?_, ?_, ?_⟩
    · rw [eq_div_iff hβφ2']; exact eA
    · rw [eq_div_iff hβφ']; exact eB
    · rw [eq_div_iff hβ']; exact eM
  · rintro ⟨hA, hB, hM⟩ x
    have eA : Ad * (1 - β * φ ^ 2) = β * (1 - β) * a ^ 2 := by
      rw [hA]; field_simp
    have eB : Bd * (1 - β * φ) = -β * ((1 - β) * a * b + Ad * φ * κ) := by
      rw [hB]; field_simp
    have eM : μd * (1 - β) =
        -β * (1 - β) * b ^ 2 / 2 - β * Ad * (κ ^ 2 + σx ^ 2) / 2 + β * Bd * κ := by
      rw [hM]; field_simp
    linear_combination (-(x ^ 2) / 2) * eA + x * eB + eM

/-- **Exercise 11.2** (Miao, p. 383): completing the solution of §11.4. With the unit-EIS
solution (11.6) (`A = β/(1 − βφ)`, `μ_v` as in `eq_11_6`), the conjecture
`v_t'(1) = −A_d x_t²/2 + B_d x_t + μ_d` solves (11.7),
`v_t'(1) = −β(1 − β)/2 [Q_t(v_{t+1}(1) + Δc)]² + β Ẽ_t v_{t+1}'(1)`, for every `x_t` iff
`A_d = β(1 − β)/((1 − βφ)²(1 − βφ²))`,
`B_d = −β[(1 − β)(1/(1 − βφ))(μ_v/β) + A_d φ κ]/(1 − βφ)`,
`μ_d = [−β(1 − β)(μ_v/β)²/2 − βA_d(κ² + σ_x²)/2 + βB_d κ]/(1 − β)`, with
`κ = (1 − γ)βσ_x²/(1 − βφ)`. The first-order approximation is then
`v_t(ρ) ≃ A x_t + μ_v + (ρ − 1)(−A_d x_t²/2 + B_d x_t + μ_d)`. -/
theorem ex_11_2 {β γ φ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : γ ≠ 1) (hβφ : β * φ ≠ 1)
    (hβφ2 : β * φ ^ 2 ≠ 1) {A μv : ℝ} (μc σc σx Ad Bd μd : ℝ) (hA : A = β / (1 - β * φ))
    (hμv : μv = β / (1 - β) * (μc + (1 - γ) / 2 * ((β * σx / (1 - β * φ)) ^ 2 + σc ^ 2))) :
    (∀ x, -Ad / 2 * x ^ 2 + Bd * x + μd =
      -(β * (1 - β)) / 2 *
          (nqQ nqShock γ (fun e => A * (φ * x + σx * e.2) + μv + μc + x + σc * e.1)) ^ 2 +
        β * nqTilt (1 - γ) (fun e => A * (φ * x + σx * e.2) + μv + μc + x + σc * e.1)
          (fun e => -Ad / 2 * (φ * x + σx * e.2) ^ 2 + Bd * (φ * x + σx * e.2) + μd)) ↔
    Ad = β * (1 - β) / ((1 - β * φ) ^ 2 * (1 - β * φ ^ 2)) ∧
      Bd = -β * ((1 - β) * (1 / (1 - β * φ)) * (μv / β) +
        Ad * φ * ((1 - γ) * β * σx ^ 2 / (1 - β * φ))) / (1 - β * φ) ∧
      μd = (-β * (1 - β) * (μv / β) ^ 2 / 2 -
        β * Ad * (((1 - γ) * β * σx ^ 2 / (1 - β * φ)) ^ 2 + σx ^ 2) / 2 +
          β * Bd * ((1 - γ) * β * σx ^ 2 / (1 - β * φ))) / (1 - β) := by
  have hβφ' : 1 - β * φ ≠ 0 := sub_ne_zero.mpr (Ne.symm hβφ)
  have ha := nq_ex_11_2_a hβφ hA
  have hb := nq_ex_11_2_b hβ0.ne' hβ1.ne hA hμv
  have hκ : (1 - γ) * A * σx ^ 2 = (1 - γ) * β * σx ^ 2 / (1 - β * φ) := by
    rw [hA]; ring
  simp_rw [nq_ex_11_2_Q hγ, nq_ex_11_2_tilt, ha, hb, hκ]
  rw [nq_ex_11_2_match hβ1.ne hβφ hβφ2]
  have hAd : β * (1 - β) * (1 / (1 - β * φ)) ^ 2 / (1 - β * φ ^ 2) =
      β * (1 - β) / ((1 - β * φ) ^ 2 * (1 - β * φ ^ 2)) := by
    field_simp
  rw [hAd]

end Miao.NumericalMethods

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Weighting functions and weighted inner products (Definition 11.3.1)

Miao, §11.3.1, pp. 356–357. A weighting function `w` on a set `s` of reals is positive on `s`
and integrable over `s`; it defines the inner product `⟨f, g⟩_w = ∫_s f g w` and orthogonality.

* `ni_IsWeightingFunction w s`, `ni_inner w s f g`, `ni_Orthogonal w s φ` (Definition 11.3.1).
* `definition_11_3_1`: the constant weight `1` on `(a, b)` is a weighting function.
* bilinearity, symmetry and positivity of `⟨·,·⟩_w`; Cauchy–Schwarz (`ni_inner_sq_le`).
* The induced norm is `‖f‖_w = √⟨f, f⟩_w` (`ni_wnorm`): it is absolutely homogeneous and
  satisfies the triangle inequality, so `‖f − g‖_w` is a (pseudo)metric.

Departures from the book.
* The book's definition is for a bounded interval `[a, b]`; positivity is required on the set
  `s` itself, which is taken to be the open interval `(a, b)` for the Chebyshev weight
  `(1 − x²)^{−1/2}` (undefined at `±1`) and `[0, ∞)`, `ℝ` for Laguerre and Hermite, which the
  book also uses with this definition.
* The book writes the induced norm as `‖f‖_w = ⟨f, f⟩_w`; this is not a norm
  (`ni_inner_self_not_homogeneous`): the norm is its square root.
-/

open MeasureTheory

namespace Miao.NumericalMethods

/-- **Definition 11.3.1** (weighting function, Miao, p. 356). `w` is positive on `s` and has a
finite integral over `s`. -/
def ni_IsWeightingFunction (w : ℝ → ℝ) (s : Set ℝ) : Prop :=
  (∀ x ∈ s, 0 < w x) ∧ IntegrableOn w s

/-- **Definition 11.3.1** (weighted inner product, Miao, p. 356): `⟨f, g⟩_w = ∫_s f g w`. -/
noncomputable def ni_inner (w : ℝ → ℝ) (s : Set ℝ) (f g : ℝ → ℝ) : ℝ :=
  ∫ x in s, f x * g x * w x

/-- **Definition 11.3.1** (mutual orthogonality, Miao, p. 356): `⟨φᵢ, φⱼ⟩_w = 0` for `i ≠ j`. -/
def ni_Orthogonal {ι : Type*} (w : ℝ → ℝ) (s : Set ℝ) (φ : ι → ℝ → ℝ) : Prop :=
  ∀ i j, i ≠ j → ni_inner w s (φ i) (φ j) = 0

/-- The norm induced by the weighted inner product, `‖f‖_w = √⟨f, f⟩_w` (Miao, p. 356, with the
square root restored). -/
noncomputable def ni_wnorm (w : ℝ → ℝ) (s : Set ℝ) (f : ℝ → ℝ) : ℝ :=
  Real.sqrt (ni_inner w s f f)

/-- **Definition 11.3.1** (Miao, p. 356): the weight `w = 1` on a bounded interval `(a, b)` is a
weighting function (the Legendre weight). -/
theorem definition_11_3_1 (a b : ℝ) :
    ni_IsWeightingFunction (fun _ => 1) (Set.Ioo a b) :=
  ⟨fun _ _ => one_pos, integrableOn_const (by simp) (by simp)⟩

/-- Miao, p. 356: the inner product is symmetric. -/
theorem ni_inner_comm (w : ℝ → ℝ) (s : Set ℝ) (f g : ℝ → ℝ) :
    ni_inner w s f g = ni_inner w s g f := by
  unfold ni_inner
  congr 1
  funext x
  ring

/-- Miao, p. 356: the inner product is additive in its first argument. -/
theorem ni_inner_add_left (w : ℝ → ℝ) (s : Set ℝ) (f₁ f₂ g : ℝ → ℝ)
    (h₁ : IntegrableOn (fun x => f₁ x * g x * w x) s)
    (h₂ : IntegrableOn (fun x => f₂ x * g x * w x) s) :
    ni_inner w s (fun x => f₁ x + f₂ x) g = ni_inner w s f₁ g + ni_inner w s f₂ g := by
  unfold ni_inner
  rw [← integral_add h₁ h₂]
  congr 1
  funext x
  ring

/-- Miao, p. 356: the inner product is homogeneous in its first argument. -/
theorem ni_inner_smul_left (w : ℝ → ℝ) (s : Set ℝ) (c : ℝ) (f g : ℝ → ℝ) :
    ni_inner w s (fun x => c * f x) g = c * ni_inner w s f g := by
  unfold ni_inner
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

/-- Miao, p. 356: `⟨f, f⟩_w ≥ 0` for a weighting function. -/
theorem ni_inner_self_nonneg {w : ℝ → ℝ} {s : Set ℝ} (hw : ni_IsWeightingFunction w s)
    (hs : MeasurableSet s) (f : ℝ → ℝ) : 0 ≤ ni_inner w s f f := by
  unfold ni_inner
  refine setIntegral_nonneg hs fun x hx => ?_
  exact mul_nonneg (mul_self_nonneg _) (hw.1 x hx).le

/-- Cauchy–Schwarz for the weighted inner product (Miao, p. 356, needed for the norm):
`⟨f, g⟩_w² ≤ ⟨f, f⟩_w ⟨g, g⟩_w`. -/
theorem ni_inner_sq_le {w : ℝ → ℝ} {s : Set ℝ} (hw : ni_IsWeightingFunction w s)
    (hs : MeasurableSet s) (f g : ℝ → ℝ)
    (hff : IntegrableOn (fun x => f x * f x * w x) s)
    (hfg : IntegrableOn (fun x => f x * g x * w x) s)
    (hgg : IntegrableOn (fun x => g x * g x * w x) s) :
    ni_inner w s f g ^ 2 ≤ ni_inner w s f f * ni_inner w s g g := by
  have key : ∀ t : ℝ, 0 ≤ ni_inner w s g g * (t * t) + 2 * ni_inner w s f g * t
      + ni_inner w s f f := by
    intro t
    have h0 := ni_inner_self_nonneg hw hs (fun x => f x + t * g x)
    have heq : ni_inner w s (fun x => f x + t * g x) (fun x => f x + t * g x)
        = ni_inner w s g g * (t * t) + 2 * ni_inner w s f g * t + ni_inner w s f f := by
      unfold ni_inner
      have e : (fun x => (f x + t * g x) * (f x + t * g x) * w x) = fun x =>
          (t * t) * (g x * g x * w x) + (2 * t) * (f x * g x * w x) + f x * f x * w x := by
        funext x; ring
      rw [e, integral_add (f := fun x => t * t * (g x * g x * w x) + 2 * t * (f x * g x * w x))
        ((hgg.const_mul _).add (hfg.const_mul _)) hff,
        integral_add (f := fun x => t * t * (g x * g x * w x))
          (hgg.const_mul _) (hfg.const_mul _), integral_const_mul, integral_const_mul]
      ring
    rw [heq] at h0
    exact h0
  have hd := discrim_le_zero key
  unfold discrim at hd
  nlinarith

/-- Miao, p. 356 (correction): `⟨f, f⟩_w` itself is not a norm, since it is not absolutely
homogeneous: for `w = 1` on `(0, 1)`, `⟨2, 2⟩_w = 4 ≠ 2 = 2 ⟨1, 1⟩_w`. -/
theorem ni_inner_self_not_homogeneous :
    ni_inner (fun _ => 1) (Set.Ioo 0 1) (fun _ => 2 * 1) (fun _ => 2 * 1) ≠
      2 * ni_inner (fun _ => 1) (Set.Ioo 0 1) (fun _ => 1) (fun _ => 1) := by
  unfold ni_inner
  simp only [mul_one, integral_const, smul_eq_mul]
  rw [measureReal_restrict_apply_univ, Real.volume_real_Ioo_of_le zero_le_one]
  norm_num

/-- Miao, p. 356: the induced norm `‖f‖_w = √⟨f, f⟩_w` is absolutely homogeneous. -/
theorem ni_wnorm_smul (w : ℝ → ℝ) (s : Set ℝ) (c : ℝ) (f : ℝ → ℝ) :
    ni_wnorm w s (fun x => c * f x) = |c| * ni_wnorm w s f := by
  unfold ni_wnorm
  have e : ni_inner w s (fun x => c * f x) (fun x => c * f x)
      = c ^ 2 * ni_inner w s f f := by
    rw [ni_inner_smul_left, ni_inner_comm, ni_inner_smul_left, ni_inner_comm]
    ring
  rw [e, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- Miao, p. 356: the induced norm satisfies the triangle inequality, so it induces "a natural
metric" `‖f − g‖_w`. -/
theorem ni_wnorm_add_le {w : ℝ → ℝ} {s : Set ℝ} (hw : ni_IsWeightingFunction w s)
    (hs : MeasurableSet s) (f g : ℝ → ℝ)
    (hff : IntegrableOn (fun x => f x * f x * w x) s)
    (hfg : IntegrableOn (fun x => f x * g x * w x) s)
    (hgg : IntegrableOn (fun x => g x * g x * w x) s) :
    ni_wnorm w s (fun x => f x + g x) ≤ ni_wnorm w s f + ni_wnorm w s g := by
  unfold ni_wnorm
  have e : ni_inner w s (fun x => f x + g x) (fun x => f x + g x)
      = ni_inner w s f f + 2 * ni_inner w s f g + ni_inner w s g g := by
    unfold ni_inner
    have e' : (fun x => (f x + g x) * (f x + g x) * w x) = fun x =>
        f x * f x * w x + 2 * (f x * g x * w x) + g x * g x * w x := by
      funext x; ring
    rw [e', integral_add (f := fun x => f x * f x * w x + 2 * (f x * g x * w x))
      (hff.add (hfg.const_mul _)) hgg,
      integral_add (f := fun x => f x * f x * w x) hff (hfg.const_mul _), integral_const_mul]
  have hA := ni_inner_self_nonneg hw hs f
  have hC := ni_inner_self_nonneg hw hs g
  have hCS := ni_inner_sq_le hw hs f g hff hfg hgg
  rw [e]
  rw [Real.sqrt_le_left]
  · have hsA := Real.sq_sqrt hA
    have hsC := Real.sq_sqrt hC
    have hB : ni_inner w s f g ≤ Real.sqrt (ni_inner w s f f) * Real.sqrt (ni_inner w s g g) := by
      rw [← Real.sqrt_mul hA]
      exact Real.le_sqrt_of_sq_le hCS
    nlinarith [Real.sqrt_nonneg (ni_inner w s f f), Real.sqrt_nonneg (ni_inner w s g g)]
  · positivity

end Miao.NumericalMethods

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The interpolation problem (Miao, §11.3, pp. 354–356)

The interpolant `f̂(x) = ∑ⱼ cⱼ φⱼ(x)` with basis functions `φⱼ`, the interpolation equation
`Φ c = y` with `Φᵢⱼ = φⱼ(xᵢ)`, the least-squares (regression) coefficients
`c = (Φ'Φ)⁻¹ Φ'y` when there are more nodes than coefficients, and the monomial basis of
§11.3.1.

* `ni_interp_eq_iff`: `f̂(xᵢ) = yᵢ` for all `i` iff `Φ c = y`.
* `ni_leastSquares_optimal`: `c = (Φ'Φ)⁻¹Φ'y` minimises `∑ᵢ (yᵢ − ∑ⱼ cⱼ φⱼ(xᵢ))²`.
* `ni_leastSquares_eq_interp`: when `m = n` and `Φ` is invertible, the least-squares
  coefficients solve the interpolation equation exactly.
* `ni_monomial_interp_unique`: for the monomial basis the interpolation matrix is the
  Vandermonde matrix; it is invertible iff the nodes are distinct, and then the interpolating
  coefficients exist and are unique; `ni_poly_interp_unique` is the polynomial (Lagrange) form.
* `ni_monomials_not_orthogonal`: the monomial basis is not mutually orthogonal with respect to
  any weighting function on a nondegenerate bounded interval (Miao, p. 356).

The claim that the Vandermonde matrix is "ill-conditioned" is qualitative and is not formalised.
-/

open Matrix MeasureTheory

namespace Miao.NumericalMethods

/-- The interpolant `f̂(x) = ∑ⱼ cⱼ φⱼ(x)` (Miao, p. 354). -/
def ni_fhat {n : ℕ} (φ : Fin n → ℝ → ℝ) (c : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ j, c j * φ j x

/-- The interpolation matrix `Φᵢⱼ = φⱼ(xᵢ)` (Miao, p. 355). -/
def ni_interpMatrix {m n : ℕ} (φ : Fin n → ℝ → ℝ) (x : Fin m → ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun i j => φ j (x i)

/-- Miao, p. 355 (the interpolation equation): `∑ⱼ cⱼ φⱼ(xᵢ) = yᵢ` for all `i` iff `Φ c = y`. -/
theorem ni_interp_eq_iff {m n : ℕ} (φ : Fin n → ℝ → ℝ) (x : Fin m → ℝ) (c : Fin n → ℝ)
    (y : Fin m → ℝ) : (∀ i, ni_fhat φ c (x i) = y i) ↔ ni_interpMatrix φ x *ᵥ c = y := by
  constructor
  · intro h
    funext i
    rw [← h i]
    simp [ni_fhat, ni_interpMatrix, mulVec, dotProduct, mul_comm]
  · intro h i
    rw [← h]
    simp [ni_fhat, ni_interpMatrix, mulVec, dotProduct, mul_comm]

/-- The sum of squared residuals `∑ᵢ (yᵢ − (Φc)ᵢ)²` of the regression method (Miao, p. 355). -/
def ni_ssr {m n : ℕ} (Φ : Matrix (Fin m) (Fin n) ℝ) (y : Fin m → ℝ) (c : Fin n → ℝ) : ℝ :=
  ∑ i, (y i - (Φ *ᵥ c) i) ^ 2

/-- The normal equations: `Φ'(y − Φc) = 0` for `c = (Φ'Φ)⁻¹Φ'y` (Miao, p. 355). -/
theorem ni_normal_equations {m n : ℕ} (Φ : Matrix (Fin m) (Fin n) ℝ) (y : Fin m → ℝ)
    (h : IsUnit (Φᵀ * Φ).det) : Φᵀ *ᵥ (y - Φ *ᵥ ((Φᵀ * Φ)⁻¹ *ᵥ (Φᵀ *ᵥ y))) = 0 := by
  rw [mulVec_sub, mulVec_mulVec, mulVec_mulVec, Matrix.mul_nonsing_inv _ h, one_mulVec,
    sub_self]

/-- Miao, p. 355 (least squares): when `Φ'Φ` is invertible, `c = (Φ'Φ)⁻¹Φ'y` minimises
`∑ᵢ (f(xᵢ) − ∑ⱼ cⱼ φⱼ(xᵢ))²`. -/
theorem ni_leastSquares_optimal {m n : ℕ} (Φ : Matrix (Fin m) (Fin n) ℝ) (y : Fin m → ℝ)
    (h : IsUnit (Φᵀ * Φ).det) (c : Fin n → ℝ) :
    ni_ssr Φ y ((Φᵀ * Φ)⁻¹ *ᵥ (Φᵀ *ᵥ y)) ≤ ni_ssr Φ y c := by
  set cs := (Φᵀ * Φ)⁻¹ *ᵥ (Φᵀ *ᵥ y)
  set r := y - Φ *ᵥ cs
  set d := Φ *ᵥ (cs - c)
  have hnorm := ni_normal_equations Φ y h
  have hrd : r ⬝ᵥ d = 0 := by
    simp only [d, dotProduct_mulVec, ← mulVec_transpose]
    rw [hnorm, zero_dotProduct]
  have hsplit : ∀ i, y i - (Φ *ᵥ c) i = r i + d i := by
    intro i
    simp only [r, d, mulVec_sub, Pi.sub_apply]
    ring
  have h1 : ni_ssr Φ y c = ni_ssr Φ y cs + 2 * (r ⬝ᵥ d) + ∑ i, d i ^ 2 := by
    unfold ni_ssr
    simp only [hsplit, dotProduct]
    have : ∀ i, y i - (Φ *ᵥ cs) i = r i := fun i => rfl
    simp only [this, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h1, hrd]
  have : 0 ≤ ∑ i, d i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

/-- Miao, p. 356: when `m = n` and `Φ` is invertible, the least-squares coefficients
`(Φ'Φ)⁻¹Φ'y` solve the interpolation equation `Φc = y`, i.e. regression is equivalent to the
interpolation equation. -/
theorem ni_leastSquares_eq_interp {n : ℕ} (Φ : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ)
    (h : IsUnit Φ.det) :
    (Φᵀ * Φ)⁻¹ *ᵥ (Φᵀ *ᵥ y) = Φ⁻¹ *ᵥ y ∧ Φ *ᵥ ((Φᵀ * Φ)⁻¹ *ᵥ (Φᵀ *ᵥ y)) = y := by
  have ht : IsUnit Φᵀ.det := by rwa [det_transpose]
  have e : (Φᵀ * Φ)⁻¹ * Φᵀ = Φ⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ht, Matrix.mul_one]
  refine ⟨?_, ?_⟩
  · rw [mulVec_mulVec, e]
  · rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc, e, Matrix.mul_nonsing_inv _ h,
      one_mulVec]

/-- The monomial basis `φⱼ(x) = x^(j−1)` (Miao, p. 356; indices from `0` here). -/
def ni_monomial {n : ℕ} (j : Fin n) (x : ℝ) : ℝ := x ^ (j : ℕ)

/-- Miao, p. 356: with the monomial basis the interpolation matrix is the Vandermonde matrix
`Φ = [1 xᵢ ⋯ xᵢⁿ⁻¹]`. -/
theorem ni_monomial_interpMatrix {n : ℕ} (x : Fin n → ℝ) :
    ni_interpMatrix ni_monomial x = Matrix.vandermonde x := by
  ext i j
  simp [ni_interpMatrix, ni_monomial, Matrix.vandermonde_apply]

/-- Miao, pp. 355–356 (monomial interpolation): the Vandermonde interpolation matrix is invertible
iff the nodes are distinct, and then for all data `y` there is exactly one coefficient vector
with `f̂(xᵢ) = yᵢ`. -/
theorem ni_monomial_interp_unique {n : ℕ} (x : Fin n → ℝ) :
    (ni_interpMatrix ni_monomial x).det ≠ 0 ↔ Function.Injective x := by
  rw [ni_monomial_interpMatrix]
  exact det_vandermonde_ne_zero_iff

/-- Miao, pp. 355–356: at distinct nodes the monomial interpolation equation has exactly one
solution. -/
theorem ni_monomial_interp_existsUnique {n : ℕ} (x : Fin n → ℝ) (hx : Function.Injective x)
    (y : Fin n → ℝ) : ∃! c : Fin n → ℝ, ∀ i, ni_fhat ni_monomial c (x i) = y i := by
  set Φ := ni_interpMatrix ni_monomial x
  have hdet : IsUnit Φ.det := isUnit_iff_ne_zero.mpr ((ni_monomial_interp_unique x).mpr hx)
  refine ⟨Φ⁻¹ *ᵥ y, ?_, ?_⟩
  · change ∀ i, ni_fhat ni_monomial (Φ⁻¹ *ᵥ y) (x i) = y i
    rw [ni_interp_eq_iff, mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, one_mulVec]
  · intro c hc
    rw [ni_interp_eq_iff] at hc
    rw [← hc, mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, one_mulVec]

/-- Miao, pp. 355–356 (polynomial interpolation, Lagrange form): at `n` distinct nodes there is
exactly one polynomial of degree `< n` taking prescribed values, namely the Lagrange
interpolant. -/
theorem ni_poly_interp_unique {n : ℕ} (x : Fin n → ℝ) (hx : Function.Injective x)
    (y : Fin n → ℝ) :
    ∃! p : Polynomial ℝ, p.degree < n ∧ ∀ i, p.eval (x i) = y i := by
  classical
  have hinj : Set.InjOn x (Finset.univ : Finset (Fin n)) := fun a _ b _ h => hx h
  refine ⟨Lagrange.interpolate Finset.univ x y, ⟨?_, fun i => ?_⟩, ?_⟩
  · simpa using Lagrange.degree_interpolate_lt (r := y) hinj
  · exact Lagrange.eval_interpolate_at_node y hinj (Finset.mem_univ i)
  · rintro q ⟨hq, hqy⟩
    refine Polynomial.eq_of_degrees_lt_of_eval_finset_eq (s := Finset.univ.image x) ?_ ?_ ?_
    · rwa [Finset.card_image_of_injective _ hx, Finset.card_univ, Fintype.card_fin]
    · rw [Finset.card_image_of_injective _ hx, Finset.card_univ, Fintype.card_fin]
      simpa using Lagrange.degree_interpolate_lt (r := y) hinj
    · intro z hz
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
      rw [hqy i, Lagrange.eval_interpolate_at_node y hinj (Finset.mem_univ i)]

/-- Miao, p. 356: the monomial basis functions are not mutually orthogonal for any weighting
function on a nondegenerate bounded interval: `⟨x⁰, x²⟩_w = ∫ x² w > 0`. -/
theorem ni_monomials_not_orthogonal {w : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hw : ni_IsWeightingFunction w (Set.Ioo a b)) :
    0 < ni_inner w (Set.Ioo a b) (fun x => x ^ 0) (fun x => x ^ 2) := by
  unfold ni_inner
  have hint : IntegrableOn (fun x : ℝ => x ^ 0 * x ^ 2 * w x) (Set.Ioo a b) := by
    have hc : ContinuousOn (fun x : ℝ => x ^ 0 * x ^ 2) (Set.Icc a b) := by fun_prop
    exact hw.2.continuousOn_mul_of_subset hc isCompact_Icc measurableSet_Ioo
      Set.Ioo_subset_Icc_self
  rw [setIntegral_pos_iff_support_of_nonneg_ae _ hint]
  · have hsub : Set.Ioo a b \ {0} ⊆ Function.support (fun x : ℝ => x ^ 0 * x ^ 2 * w x)
        ∩ Set.Ioo a b := by
      intro x ⟨hx, hx0⟩
      refine ⟨?_, hx⟩
      have : x ≠ 0 := hx0
      simp only [Function.mem_support, pow_zero, one_mul]
      exact (mul_pos (by positivity) (hw.1 x hx)).ne'
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [measure_sdiff_null (by simp)]
    simp [hab]
  · refine (ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ fun x hx => ?_)
    exact mul_nonneg (by positivity) (hw.1 x hx).le

end Miao.NumericalMethods

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Laguerre polynomials (Miao, §11.3.1, p. 357)

The `n`th Laguerre polynomial is `Lₙ(x) = (eˣ/n!) dⁿ/dxⁿ (xⁿ e^{−x})`, `L₀ = 1`, on `[0, ∞)`,
with weighting function `w(x) = e^{−x}`.

* `ni_lagOp p = p' − p`: `d/dx (p(x) e^{−x}) = (p' − p)(x) e^{−x}`
  (`ni_hasDerivAt_poly_mul_exp_neg`), so `dᵏ/dxᵏ (p e^{−x}) = (lagOpᵏ p) e^{−x}`
  (`ni_iteratedDeriv_poly_mul_exp_neg`).
* `ni_laguerre n = (1/n!) lagOpⁿ Xⁿ`, with `ni_laguerre_eval_eq_rodrigues` (the book's formula),
  `ni_laguerre_zero` (`L₀ = 1`) and `ni_laguerre_natDegree_le` (`deg Lₙ ≤ n`).
* `ni_laguerre_weight`: `e^{−x}` is a weighting function on `(0, ∞)` (Definition 11.3.1).
* `ni_laguerre_orthogonal_low`, `ni_laguerre_orthogonal`: `Lₙ` is orthogonal to every
  polynomial of lower degree, hence the `Lₙ` are mutually orthogonal for the weight `e^{−x}`.
-/

open Polynomial MeasureTheory Filter Topology Real

namespace Miao.NumericalMethods

/-- `x ↦ xⁱ e^{−x}` is integrable on `(0, ∞)` (the Gamma integral). -/
theorem ni_integrableOn_pow_mul_exp_neg (i : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ i * exp (-x)) (Set.Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := (i : ℝ) + 1) (by positivity)
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [add_sub_cancel_right, Real.rpow_natCast]
  ring

/-- `x ↦ p(x) e^{−x}` is integrable on `(0, ∞)` for every polynomial `p`. -/
theorem ni_integrableOn_poly_mul_exp_neg (p : ℝ[X]) :
    IntegrableOn (fun x : ℝ => p.eval x * exp (-x)) (Set.Ioi 0) := by
  have e : (fun x : ℝ => p.eval x * exp (-x)) = fun x =>
      ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (x ^ i * exp (-x)) := by
    funext x
    rw [eval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e]
  exact integrable_finsetSum _ fun i _ => (ni_integrableOn_pow_mul_exp_neg i).const_mul _

/-- `p(x) e^{−x} → 0` as `x → ∞`. -/
theorem ni_tendsto_poly_mul_exp_neg (p : ℝ[X]) :
    Tendsto (fun x : ℝ => p.eval x * exp (-x)) atTop (𝓝 0) := by
  have e : (fun x : ℝ => p.eval x * exp (-x)) = fun x =>
      ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (x ^ i * exp (-x)) := by
    funext x
    rw [eval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e]
  have h := tendsto_finsetSum (Finset.range (p.natDegree + 1)) fun i _ =>
    (tendsto_pow_mul_exp_neg_atTop_nhds_zero i).const_mul (p.coeff i)
  simpa using h

/-- The operator `p ↦ p' − p`. -/
noncomputable def ni_lagOp (p : ℝ[X]) : ℝ[X] := derivative p - p

/-- `d/dx (p(x) e^{−x}) = (p' − p)(x) e^{−x}`. -/
theorem ni_hasDerivAt_poly_mul_exp_neg (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun y => p.eval y * exp (-y)) ((ni_lagOp p).eval x * exp (-x)) x := by
  have h := (Polynomial.hasDerivAt p x).mul (hasDerivAt_neg x).exp
  convert h using 1
  simp only [ni_lagOp, eval_sub]
  ring

/-- `dᵏ/dxᵏ (p(x) e^{−x}) = (lagOpᵏ p)(x) e^{−x}`. -/
theorem ni_iteratedDeriv_poly_mul_exp_neg (p : ℝ[X]) (k : ℕ) :
    iteratedDeriv k (fun x => p.eval x * exp (-x)) =
      fun x => (ni_lagOp^[k] p).eval x * exp (-x) := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ']
    have : deriv (fun x => p.eval x * exp (-x)) = fun x => (ni_lagOp p).eval x * exp (-x) := by
      funext x
      exact (ni_hasDerivAt_poly_mul_exp_neg p x).deriv
    rw [this, ih, Function.iterate_succ_apply]

/-- The `n`th Laguerre polynomial `Lₙ = (1/n!) lagOpⁿ Xⁿ` (Miao, p. 357). -/
noncomputable def ni_laguerre (n : ℕ) : ℝ[X] :=
  C (1 / (n.factorial : ℝ)) * ni_lagOp^[n] (X ^ n)

/-- Miao, p. 357 (Rodrigues' formula): `Lₙ(x) = (eˣ/n!) dⁿ/dxⁿ (xⁿ e^{−x})`. -/
theorem ni_laguerre_eval_eq_rodrigues (n : ℕ) (x : ℝ) :
    (ni_laguerre n).eval x =
      exp x / n.factorial * iteratedDeriv n (fun y => y ^ n * exp (-y)) x := by
  have : (fun y : ℝ => y ^ n * exp (-y)) = fun y => (X ^ n : ℝ[X]).eval y * exp (-y) := by
    funext y
    simp
  rw [this, ni_iteratedDeriv_poly_mul_exp_neg]
  simp only [ni_laguerre, eval_mul, eval_C]
  have hx : exp x * exp (-x) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
  calc 1 / (n.factorial : ℝ) * (ni_lagOp^[n] (X ^ n)).eval x
      = 1 / n.factorial * (ni_lagOp^[n] (X ^ n)).eval x * (exp x * exp (-x)) := by
        rw [hx, mul_one]
    _ = _ := by ring

/-- Miao, p. 357: `L₀(x) = 1`. -/
theorem ni_laguerre_zero : ni_laguerre 0 = 1 := by
  simp [ni_laguerre]

/-- `deg (p' − p) ≤ deg p`. -/
theorem ni_lagOp_natDegree_le (p : ℝ[X]) : (ni_lagOp p).natDegree ≤ p.natDegree :=
  (natDegree_sub_le _ _).trans (max_le (natDegree_derivative_le p |>.trans (Nat.sub_le _ _))
    le_rfl)

/-- The Laguerre polynomial `Lₙ` has degree at most `n`. -/
theorem ni_laguerre_natDegree_le (n : ℕ) : (ni_laguerre n).natDegree ≤ n := by
  unfold ni_laguerre
  refine (natDegree_C_mul_le _ _).trans ?_
  have : ∀ k (p : ℝ[X]), (ni_lagOp^[k] p).natDegree ≤ p.natDegree := by
    intro k
    induction k with
    | zero => intro p; simp
    | succ k ih =>
      intro p
      rw [Function.iterate_succ_apply']
      exact (ni_lagOp_natDegree_le _).trans (ih p)
  exact (this n _).trans (natDegree_X_pow_le n)

/-- **Definition 11.3.1** for the Laguerre weight (Miao, p. 357): `e^{−x}` is a weighting
function on `(0, ∞)`. -/
theorem ni_laguerre_weight : ni_IsWeightingFunction (fun x => exp (-x)) (Set.Ioi 0) :=
  ⟨fun x _ => exp_pos _, by simpa using ni_integrableOn_pow_mul_exp_neg 0⟩

/-- `∫_0^∞ (p' − p)(x) e^{−x} dx = −p(0)`. -/
theorem ni_integral_lagOp (p : ℝ[X]) :
    ∫ x in Set.Ioi (0 : ℝ), (ni_lagOp p).eval x * exp (-x) = -p.eval 0 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun y => p.eval y * exp (-y)) (m := 0)
    ((ni_hasDerivAt_poly_mul_exp_neg p 0).continuousAt.continuousWithinAt)
    (fun x _ => ni_hasDerivAt_poly_mul_exp_neg p x)
    (ni_integrableOn_poly_mul_exp_neg _) (ni_tendsto_poly_mul_exp_neg p)
  rw [h]
  simp

/-- `X^{j−l}` divides `lagOpˡ Xʲ`, so `(lagOpˡ Xʲ)(0) = 0` for `l < j`. -/
theorem ni_lagOp_iterate_eval_zero (j : ℕ) : ∀ l < j, (ni_lagOp^[l] (X ^ j)).eval 0 = 0 := by
  have hdvd : ∀ l ≤ j, (X : ℝ[X]) ^ (j - l) ∣ ni_lagOp^[l] (X ^ j) := by
    intro l
    induction l with
    | zero => intro _; simp
    | succ l ih =>
      intro hl
      obtain ⟨r, hr⟩ := ih (by omega)
      rw [Function.iterate_succ_apply', hr]
      have hk : j - l = (j - (l + 1)) + 1 := by omega
      rw [hk]
      refine ⟨((j - (l + 1) + 1 : ℕ) : ℝ[X]) * r + X * derivative r - X * r, ?_⟩
      simp only [ni_lagOp, derivative_mul, derivative_X_pow, Nat.add_sub_cancel, C_eq_natCast]
      push_cast
      ring
  intro l hl
  obtain ⟨r, hr⟩ := hdvd l hl.le
  rw [hr, eval_mul, eval_pow, eval_X, zero_pow (by omega), zero_mul]

/-- Repeated integration by parts on `(0, ∞)` with weight `e^{−x}`. -/
theorem ni_laguerre_parts (j : ℕ) : ∀ m ≤ j, ∀ q : ℝ[X],
    ∫ x in Set.Ioi (0 : ℝ), q.eval x * (ni_lagOp^[m] (X ^ j)).eval x * exp (-x) =
      (-1) ^ m * ∫ x in Set.Ioi (0 : ℝ), (derivative^[m] q).eval x * x ^ j * exp (-x) := by
  intro m
  induction m with
  | zero => intro _ q; simp
  | succ m ih =>
    intro hm q
    rw [Function.iterate_succ_apply']
    set t := ni_lagOp^[m] (X ^ j)
    have ht0 : t.eval 0 = 0 := ni_lagOp_iterate_eval_zero j m (by omega)
    have split : ∀ x, q.eval x * (ni_lagOp t).eval x * exp (-x) =
        (ni_lagOp (q * t)).eval x * exp (-x) - (derivative q).eval x * t.eval x * exp (-x) := by
      intro x
      simp only [ni_lagOp, eval_sub, eval_mul, derivative_mul, eval_add]
      ring
    simp_rw [split]
    rw [integral_sub (ni_integrableOn_poly_mul_exp_neg _), ni_integral_lagOp, eval_mul, ht0,
      mul_zero, neg_zero, zero_sub, ih (by omega), Function.iterate_succ_apply]
    · ring
    · have := ni_integrableOn_poly_mul_exp_neg (derivative q * t)
      simp only [eval_mul] at this
      exact this

/-- Miao, p. 357: `∫_0^∞ q(x) Lₙ(x) e^{−x} dx = 0` for every polynomial `q` of degree `< n`. -/
theorem ni_laguerre_orthogonal_low (n : ℕ) (q : ℝ[X]) (hq : q.natDegree < n) :
    ∫ x in Set.Ioi (0 : ℝ), q.eval x * (ni_laguerre n).eval x * exp (-x) = 0 := by
  have e : ∀ x, q.eval x * (ni_laguerre n).eval x * exp (-x) =
      1 / (n.factorial : ℝ) * (q.eval x * (ni_lagOp^[n] (X ^ n)).eval x * exp (-x)) := by
    intro x
    simp only [ni_laguerre, eval_mul, eval_C]
    ring
  simp_rw [e]
  rw [integral_const_mul, ni_laguerre_parts n n le_rfl, iterate_derivative_eq_zero hq]
  simp

/-- **Definition 11.3.1** applied to the Laguerre polynomials (Miao, p. 357): `Lᵢ` and `Lⱼ` are
orthogonal with respect to the weighting function `e^{−x}` on `[0, ∞)` for `i ≠ j`. -/
theorem ni_laguerre_orthogonal :
    ni_Orthogonal (fun x => exp (-x)) (Set.Ioi 0) (fun n x => (ni_laguerre n).eval x) := by
  intro i j hij
  unfold ni_inner
  rcases lt_or_gt_of_ne hij with h | h
  · exact ni_laguerre_orthogonal_low j _ ((ni_laguerre_natDegree_le i).trans_lt h)
  · refine Eq.trans ?_ (ni_laguerre_orthogonal_low i _ ((ni_laguerre_natDegree_le j).trans_lt h))
    congr 1
    funext x
    ring

end Miao.NumericalMethods

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Hermite polynomials (Miao, §11.3.1, p. 357)

The `n`th Hermite polynomial is `Hₙ(x) = (−1)ⁿ e^{x²} dⁿ/dxⁿ e^{−x²}`, `H₀ = 1`, on `ℝ`, with
weighting function `w(x) = e^{−x²}` (the physicists' Hermite polynomials; Mathlib's `hermite`
are the probabilists' ones).

* `ni_hermOp p = p' − 2Xp`: `d/dx (p(x) e^{−x²}) = (p' − 2xp)(x) e^{−x²}`, and
  `ni_iteratedDeriv_poly_mul_exp_neg_sq`.
* `ni_hermite n = (−1)ⁿ hermOpⁿ 1`, with `ni_hermite_eval_eq_rodrigues` (the book's formula),
  `ni_hermite_zero` (`H₀ = 1`) and `ni_hermite_natDegree_le` (`deg Hₙ ≤ n`).
* `ni_hermite_weight`: `e^{−x²}` is a weighting function on `ℝ` (Definition 11.3.1).
* `ni_hermite_orthogonal_low`, `ni_hermite_orthogonal`: `Hₙ` is orthogonal to every polynomial
  of lower degree, hence the `Hₙ` are mutually orthogonal for the weight `e^{−x²}`.
-/

open Polynomial MeasureTheory Filter Topology Real

namespace Miao.NumericalMethods

/-- `x ↦ xⁱ e^{−x²}` is integrable on `ℝ`. -/
theorem ni_integrable_pow_mul_exp_neg_sq (i : ℕ) :
    Integrable (fun x : ℝ => x ^ i * exp (-x ^ 2)) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1) one_pos (s := (i : ℝ))
    (by have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith)
  refine h.congr (ae_of_all _ fun x => ?_)
  simp [Real.rpow_natCast]

/-- `x ↦ p(x) e^{−x²}` is integrable on `ℝ` for every polynomial `p`. -/
theorem ni_integrable_poly_mul_exp_neg_sq (p : ℝ[X]) :
    Integrable (fun x : ℝ => p.eval x * exp (-x ^ 2)) := by
  have e : (fun x : ℝ => p.eval x * exp (-x ^ 2)) = fun x =>
      ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (x ^ i * exp (-x ^ 2)) := by
    funext x
    rw [eval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e]
  exact integrable_finsetSum _ fun i _ => (ni_integrable_pow_mul_exp_neg_sq i).const_mul _

/-- `xⁱ e^{−x²} → 0` as `|x| → ∞`. -/
theorem ni_tendsto_pow_mul_exp_neg_sq (i : ℕ) :
    Tendsto (fun x : ℝ => x ^ i * exp (-x ^ 2)) (cocompact ℝ) (𝓝 0) := by
  have h := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (a := 1) one_pos (i : ℝ)
  refine squeeze_zero_norm (fun x => ?_) h
  rw [Real.norm_eq_abs, abs_mul, abs_pow, Real.rpow_natCast, abs_of_pos (exp_pos _)]
  simp

/-- `p(x) e^{−x²} → 0` as `|x| → ∞`. -/
theorem ni_tendsto_poly_mul_exp_neg_sq (p : ℝ[X]) :
    Tendsto (fun x : ℝ => p.eval x * exp (-x ^ 2)) (cocompact ℝ) (𝓝 0) := by
  have e : (fun x : ℝ => p.eval x * exp (-x ^ 2)) = fun x =>
      ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (x ^ i * exp (-x ^ 2)) := by
    funext x
    rw [eval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e]
  have h := tendsto_finsetSum (Finset.range (p.natDegree + 1)) fun i _ =>
    (ni_tendsto_pow_mul_exp_neg_sq i).const_mul (p.coeff i)
  simpa using h

/-- The operator `p ↦ p' − 2Xp`. -/
noncomputable def ni_hermOp (p : ℝ[X]) : ℝ[X] := derivative p - 2 * X * p

/-- `d/dx (p(x) e^{−x²}) = (p' − 2xp)(x) e^{−x²}`. -/
theorem ni_hasDerivAt_poly_mul_exp_neg_sq (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun y => p.eval y * exp (-y ^ 2)) ((ni_hermOp p).eval x * exp (-x ^ 2)) x := by
  have h := (Polynomial.hasDerivAt p x).mul ((hasDerivAt_pow 2 x).neg).exp
  convert h using 1
  simp only [ni_hermOp, eval_sub, eval_mul, eval_X, eval_ofNat, Pi.neg_apply]
  push_cast
  ring

/-- `dᵏ/dxᵏ (p(x) e^{−x²}) = (hermOpᵏ p)(x) e^{−x²}`. -/
theorem ni_iteratedDeriv_poly_mul_exp_neg_sq (p : ℝ[X]) (k : ℕ) :
    iteratedDeriv k (fun x => p.eval x * exp (-x ^ 2)) =
      fun x => (ni_hermOp^[k] p).eval x * exp (-x ^ 2) := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ']
    have : deriv (fun x => p.eval x * exp (-x ^ 2)) =
        fun x => (ni_hermOp p).eval x * exp (-x ^ 2) := by
      funext x
      exact (ni_hasDerivAt_poly_mul_exp_neg_sq p x).deriv
    rw [this, ih, Function.iterate_succ_apply]

/-- The `n`th Hermite polynomial `Hₙ = (−1)ⁿ hermOpⁿ 1` (Miao, p. 357). -/
noncomputable def ni_hermite (n : ℕ) : ℝ[X] :=
  C ((-1 : ℝ) ^ n) * ni_hermOp^[n] 1

/-- Miao, p. 357 (Rodrigues' formula): `Hₙ(x) = (−1)ⁿ e^{x²} dⁿ/dxⁿ e^{−x²}`. -/
theorem ni_hermite_eval_eq_rodrigues (n : ℕ) (x : ℝ) :
    (ni_hermite n).eval x = (-1) ^ n * exp (x ^ 2) * iteratedDeriv n (fun y => exp (-y ^ 2)) x := by
  have : (fun y : ℝ => exp (-y ^ 2)) = fun y => (1 : ℝ[X]).eval y * exp (-y ^ 2) := by
    funext y
    simp
  rw [this, ni_iteratedDeriv_poly_mul_exp_neg_sq]
  simp only [ni_hermite, eval_mul, eval_C]
  have hx : exp (x ^ 2) * exp (-x ^ 2) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
  calc (-1 : ℝ) ^ n * (ni_hermOp^[n] 1).eval x
      = (-1) ^ n * (ni_hermOp^[n] 1).eval x * (exp (x ^ 2) * exp (-x ^ 2)) := by
        rw [hx, mul_one]
    _ = _ := by ring

/-- Miao, p. 357: `H₀(x) = 1`. -/
theorem ni_hermite_zero : ni_hermite 0 = 1 := by
  simp [ni_hermite]

/-- `deg (p' − 2Xp) ≤ deg p + 1`. -/
theorem ni_hermOp_natDegree_le (p : ℝ[X]) : (ni_hermOp p).natDegree ≤ p.natDegree + 1 := by
  unfold ni_hermOp
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · exact (natDegree_derivative_le p).trans (by omega)
  · refine (natDegree_mul_le).trans ?_
    have : (2 * X : ℝ[X]).natDegree ≤ 1 := by
      refine (natDegree_mul_le).trans ?_
      simp
    omega

/-- The Hermite polynomial `Hₙ` has degree at most `n`. -/
theorem ni_hermite_natDegree_le (n : ℕ) : (ni_hermite n).natDegree ≤ n := by
  unfold ni_hermite
  refine (natDegree_C_mul_le _ _).trans ?_
  have : ∀ k, (ni_hermOp^[k] (1 : ℝ[X])).natDegree ≤ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact (ni_hermOp_natDegree_le _).trans (by omega)
  exact this n

/-- **Definition 11.3.1** for the Hermite weight (Miao, p. 357): `e^{−x²}` is a weighting
function on `ℝ`. -/
theorem ni_hermite_weight : ni_IsWeightingFunction (fun x => exp (-x ^ 2)) Set.univ :=
  ⟨fun x _ => exp_pos _, by simpa using ni_integrable_pow_mul_exp_neg_sq 0⟩

/-- `∫_ℝ (p' − 2xp)(x) e^{−x²} dx = 0`. -/
theorem ni_integral_hermOp (p : ℝ[X]) :
    ∫ x, (ni_hermOp p).eval x * exp (-x ^ 2) = 0 := by
  have h := integral_of_hasDerivAt_of_tendsto
    (f := fun y => p.eval y * exp (-y ^ 2)) (m := 0) (n := 0)
    (fun x => ni_hasDerivAt_poly_mul_exp_neg_sq p x)
    (ni_integrable_poly_mul_exp_neg_sq _)
    ((ni_tendsto_poly_mul_exp_neg_sq p).mono_left atBot_le_cocompact)
    ((ni_tendsto_poly_mul_exp_neg_sq p).mono_left atTop_le_cocompact)
  rw [h, sub_self]

/-- Repeated integration by parts on `ℝ` with weight `e^{−x²}`. -/
theorem ni_hermite_parts : ∀ m : ℕ, ∀ q : ℝ[X],
    ∫ x, q.eval x * (ni_hermOp^[m] 1).eval x * exp (-x ^ 2) =
      (-1) ^ m * ∫ x, (derivative^[m] q).eval x * exp (-x ^ 2) := by
  intro m
  induction m with
  | zero => intro q; simp
  | succ m ih =>
    intro q
    rw [Function.iterate_succ_apply']
    set t := ni_hermOp^[m] (1 : ℝ[X])
    have split : ∀ x, q.eval x * (ni_hermOp t).eval x * exp (-x ^ 2) =
        (ni_hermOp (q * t)).eval x * exp (-x ^ 2) -
          (derivative q).eval x * t.eval x * exp (-x ^ 2) := by
      intro x
      simp only [ni_hermOp, eval_sub, eval_mul, derivative_mul, eval_add]
      ring
    simp_rw [split]
    rw [integral_sub (ni_integrable_poly_mul_exp_neg_sq _), ni_integral_hermOp, zero_sub, ih,
      Function.iterate_succ_apply]
    · ring
    · have := ni_integrable_poly_mul_exp_neg_sq (derivative q * t)
      simp only [eval_mul] at this
      exact this

/-- Miao, p. 357: `∫_ℝ q(x) Hₙ(x) e^{−x²} dx = 0` for every polynomial `q` of degree `< n`. -/
theorem ni_hermite_orthogonal_low (n : ℕ) (q : ℝ[X]) (hq : q.natDegree < n) :
    ∫ x, q.eval x * (ni_hermite n).eval x * exp (-x ^ 2) = 0 := by
  have e : ∀ x, q.eval x * (ni_hermite n).eval x * exp (-x ^ 2) =
      (-1 : ℝ) ^ n * (q.eval x * (ni_hermOp^[n] 1).eval x * exp (-x ^ 2)) := by
    intro x
    simp only [ni_hermite, eval_mul, eval_C]
    ring
  simp_rw [e]
  rw [integral_const_mul, ni_hermite_parts n, iterate_derivative_eq_zero hq]
  simp

/-- **Definition 11.3.1** applied to the Hermite polynomials (Miao, p. 357): `Hᵢ` and `Hⱼ` are
orthogonal with respect to the weighting function `e^{−x²}` on `ℝ` for `i ≠ j`. -/
theorem ni_hermite_orthogonal :
    ni_Orthogonal (fun x => exp (-x ^ 2)) Set.univ (fun n x => (ni_hermite n).eval x) := by
  intro i j hij
  unfold ni_inner
  rw [setIntegral_univ]
  rcases lt_or_gt_of_ne hij with h | h
  · exact ni_hermite_orthogonal_low j _ ((ni_hermite_natDegree_le i).trans_lt h)
  · refine Eq.trans ?_ (ni_hermite_orthogonal_low i _ ((ni_hermite_natDegree_le j).trans_lt h))
    congr 1
    funext x
    ring

end Miao.NumericalMethods

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Chebyshev interpolation (Miao, §11.3.1, pp. 359–360)

With basis `φⱼ = Tⱼ₋₁`, `j = 1, …, n`, and the `n` roots `xₖ` of `Tₙ` as nodes:

* `ni_chebPhi_gram`: `Φ'Φ = diag(n, n/2, …, n/2)` (from the discrete orthogonality).
* `ni_chebCoeff_eq`: the least-squares coefficients `c = (Φ'Φ)⁻¹Φ'y` are
  `c₁ = (1/n) ∑ₖ f(xₖ)T₀(xₖ)` and `cⱼ = (2/n) ∑ₖ f(xₖ)Tⱼ₋₁(xₖ)` for `j ≥ 2`, and
  `ni_chebCoeff_eq_ratio`: `cⱼ = ∑ₖ f(xₖ)Tⱼ₋₁(xₖ) / ∑ₖ Tⱼ₋₁(xₖ)²`.
* `ni_chebInterpolant_nodes`: the Chebyshev interpolant `I_{n−1}^f = ∑ᵢ cᵢ Tᵢ₋₁` matches `f`
  exactly at the `n` roots of `Tₙ`.
* `ni_chebTruncation_bound` (11.2): on `[−1, 1]` the truncation error of dropping the terms
  `m + 1, …, n` is at most `∑ |cₖ|` over the dropped terms.
* `ni_chebInterp n f`: the degree-`n` Chebyshev interpolant of Theorem 11.3.1 (Lagrange form at
  the `n + 1` roots of `Tₙ₊₁`), equal to the coefficient form (`ni_chebInterp_eq_coeff_form`).
* `ni_lebesgue_inequality`: the first step of the proof of Theorem 11.3.1, the Lebesgue
  inequality `|f(x) − Iₙf(x)| ≤ |f(x) − p(x)| + Λₙ(x) maxₖ |f(xₖ) − p(xₖ)|` for every polynomial
  `p` of degree `≤ n`, with `Λₙ(x) = ∑ₖ |ℓₖ(x)|` the Lebesgue function.
* `theorem_11_3_1_counterexample`: Theorem 11.3.1 is false as printed ("for all `n`"): for
  `f(x) = x²`, `k = 3`, `n = 1` the right side is `0` and the left side is `1/2`.

The bound of Theorem 11.3.1 itself (for `n ≥ k`; Rivlin 1990) rests on Jackson's theorem and the
logarithmic growth of the Chebyshev Lebesgue constant, neither of which is in Mathlib; it is not
formalised here beyond the two items above. The remarks that the truncated series is "almost the
same as the minimax polynomial" are heuristic and not formalised.
-/

open Polynomial Polynomial.Chebyshev Real Matrix

namespace Miao.NumericalMethods

/-- Reindexing `∑_{k : Fin n} g(k + 1) = ∑_{k = 1}^{n} g(k)`. -/
theorem ni_sum_fin_succ (n : ℕ) (g : ℕ → ℝ) :
    ∑ k : Fin n, g ((k : ℕ) + 1) = ∑ k ∈ Finset.Icc 1 n, g k := by
  rw [Fin.sum_univ_eq_sum_range (fun k => g (k + 1)), ← Finset.Ico_add_one_right_eq_Icc,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  exact Finset.sum_congr rfl fun k _ => by rw [add_comm]

/-- The Chebyshev interpolation matrix `Φₖⱼ = Tⱼ₋₁(xₖ)` (Miao, p. 359; indices from `0`). -/
noncomputable def ni_chebPhi (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun k j => (T ℝ (j : ℕ)).eval (ni_chebNode n (k + 1))

/-- The diagonal of `Φ'Φ`: `n` for the first basis function and `n/2` for the others. -/
noncomputable def ni_chebGramDiag (n : ℕ) (j : Fin n) : ℝ :=
  if (j : ℕ) = 0 then n else n / 2

/-- Miao, p. 359: `Φ'Φ = diag(n, n/2, …, n/2)`. -/
theorem ni_chebPhi_gram (n : ℕ) :
    (ni_chebPhi n)ᵀ * ni_chebPhi n = Matrix.diagonal (ni_chebGramDiag n) := by
  ext i j
  rw [Matrix.mul_apply, Matrix.diagonal_apply]
  simp only [Matrix.transpose_apply, ni_chebPhi, Matrix.of_apply]
  rw [ni_sum_fin_succ n (fun k => (T ℝ (i : ℕ)).eval (ni_chebNode n k) *
    (T ℝ (j : ℕ)).eval (ni_chebNode n k)), ni_cheb_discrete_orthogonality i.2 j.2]
  by_cases h : i = j
  · subst h
    simp [ni_chebGramDiag]
  · have h' : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
    simp [h, h']

theorem ni_chebGramDiag_ne_zero {n : ℕ} (j : Fin n) : ni_chebGramDiag n j ≠ 0 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero (by rintro rfl; exact j.elim0))
  unfold ni_chebGramDiag
  split_ifs <;> positivity

theorem ni_chebGram_isUnit (n : ℕ) : IsUnit ((ni_chebPhi n)ᵀ * ni_chebPhi n).det := by
  rw [ni_chebPhi_gram, det_diagonal]
  exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun j _ => ni_chebGramDiag_ne_zero j)

/-- The data vector `yₖ = f(xₖ)` at the Chebyshev nodes. -/
noncomputable def ni_chebData (n : ℕ) (f : ℝ → ℝ) (k : Fin n) : ℝ := f (ni_chebNode n (k + 1))

/-- The least-squares coefficients `c = (Φ'Φ)⁻¹Φ'y` (Miao, p. 359). -/
noncomputable def ni_chebCoeff (n : ℕ) (f : ℝ → ℝ) : Fin n → ℝ :=
  ((ni_chebPhi n)ᵀ * ni_chebPhi n)⁻¹ *ᵥ ((ni_chebPhi n)ᵀ *ᵥ ni_chebData n f)

/-- Miao, p. 359: `c₁ = (1/n) ∑ₖ f(xₖ)T₀(xₖ)` and `cⱼ = (2/n) ∑ₖ f(xₖ)Tⱼ₋₁(xₖ)` for `j ≥ 2`. -/
theorem ni_chebCoeff_eq (n : ℕ) (f : ℝ → ℝ) (j : Fin n) :
    ni_chebCoeff n f j = (if (j : ℕ) = 0 then 1 / (n : ℝ) else 2 / n) *
      ∑ k ∈ Finset.Icc 1 n, f (ni_chebNode n k) * (T ℝ (j : ℕ)).eval (ni_chebNode n k) := by
  unfold ni_chebCoeff
  have hinv : (Matrix.diagonal (ni_chebGramDiag n))⁻¹ =
      Matrix.diagonal (fun j => (ni_chebGramDiag n j)⁻¹) := by
    refine Matrix.inv_eq_left_inv ?_
    rw [diagonal_mul_diagonal]
    convert diagonal_one with i
    exact inv_mul_cancel₀ (ni_chebGramDiag_ne_zero i)
  rw [ni_chebPhi_gram, hinv, mulVec_diagonal]
  have hs : ((ni_chebPhi n)ᵀ *ᵥ ni_chebData n f) j =
      ∑ k ∈ Finset.Icc 1 n, f (ni_chebNode n k) * (T ℝ (j : ℕ)).eval (ni_chebNode n k) := by
    rw [← ni_sum_fin_succ n (fun k => f (ni_chebNode n k) * (T ℝ (j : ℕ)).eval (ni_chebNode n k))]
    simp only [mulVec, dotProduct, transpose_apply, ni_chebPhi, of_apply, ni_chebData]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [hs]
  unfold ni_chebGramDiag
  split_ifs <;> simp [div_eq_mul_inv]

/-- Miao, p. 359: `cⱼ = ∑ₖ f(xₖ)Tⱼ₋₁(xₖ) / ∑ₖ Tⱼ₋₁(xₖ)²`. -/
theorem ni_chebCoeff_eq_ratio (n : ℕ) (f : ℝ → ℝ) (j : Fin n) :
    ni_chebCoeff n f j =
      (∑ k ∈ Finset.Icc 1 n, f (ni_chebNode n k) * (T ℝ (j : ℕ)).eval (ni_chebNode n k)) /
        ∑ k ∈ Finset.Icc 1 n, (T ℝ (j : ℕ)).eval (ni_chebNode n k) ^ 2 := by
  have hsq : ∑ k ∈ Finset.Icc 1 n, (T ℝ (j : ℕ)).eval (ni_chebNode n k) ^ 2 =
      ni_chebGramDiag n j := by
    simp_rw [sq]
    rw [ni_cheb_discrete_orthogonality j.2 j.2]
    simp [ni_chebGramDiag]
  rw [hsq, ni_chebCoeff_eq]
  unfold ni_chebGramDiag
  split_ifs <;> field_simp

/-- The Chebyshev interpolant `I_{n−1}^f(x) = ∑ᵢ cᵢ Tᵢ₋₁(x)` (Miao, p. 359). -/
noncomputable def ni_chebInterpolant (n : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ j : Fin n, ni_chebCoeff n f j * (T ℝ (j : ℕ)).eval x

/-- Miao, p. 359: `I_{n−1}^f` and `f` are exactly matched at the `n` roots of `Tₙ`. -/
theorem ni_chebInterpolant_nodes (n : ℕ) (f : ℝ → ℝ) (k : ℕ) (hk : k ∈ Finset.Icc 1 n) :
    ni_chebInterpolant n f (ni_chebNode n k) = f (ni_chebNode n k) := by
  have hdet : IsUnit (ni_chebPhi n).det := by
    have h := ni_chebGram_isUnit n
    rw [det_mul, det_transpose] at h
    exact isUnit_of_mul_isUnit_left h
  have h := (ni_leastSquares_eq_interp (ni_chebPhi n) (ni_chebData n f) hdet).2
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
  have hk' := congrFun h ⟨k - 1, by omega⟩
  have e : k - 1 + 1 = k := by omega
  simp only [mulVec, dotProduct, ni_chebPhi, of_apply, ni_chebData, e] at hk'
  rw [← hk']
  unfold ni_chebInterpolant ni_chebCoeff
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- Miao, (11.2), p. 360: since `|Tₖ| ≤ 1` on `[−1, 1]`, the difference between the full and the
truncated Chebyshev series is bounded by the sum of the absolute values of the dropped
coefficients. -/
theorem ni_chebTruncation_bound (c : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |∑ i ∈ Finset.range n, c i * (T ℝ i).eval x - ∑ i ∈ Finset.range m, c i * (T ℝ i).eval x|
      ≤ ∑ i ∈ Finset.Ico m n, |c i| := by
  rw [← Finset.sum_range_add_sum_Ico _ hmn, add_sub_cancel_left]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (ni_cheb_abs_le_one i hx)

/-- The degree-`n` Chebyshev interpolant `Iₙf` of Theorem 11.3.1: the polynomial interpolating
`f` at the `n + 1` roots of `Tₙ₊₁` (Lagrange form). -/
noncomputable def ni_chebInterp (n : ℕ) (f : ℝ → ℝ) : ℝ[X] :=
  Lagrange.interpolate (Finset.Icc 1 (n + 1)) (ni_chebNode (n + 1))
    (fun k => f (ni_chebNode (n + 1) k))

/-- `Iₙf` has degree at most `n` and interpolates `f` at the `n + 1` roots of `Tₙ₊₁`. -/
theorem ni_chebInterp_spec (n : ℕ) (f : ℝ → ℝ) :
    (ni_chebInterp n f).degree < (n + 1 : ℕ) ∧
      ∀ k ∈ Finset.Icc 1 (n + 1), (ni_chebInterp n f).eval (ni_chebNode (n + 1) k) =
        f (ni_chebNode (n + 1) k) := by
  have hinj := ni_chebNode_injOn (n + 1)
  refine ⟨?_, fun k hk => Lagrange.eval_interpolate_at_node _ hinj hk⟩
  have := Lagrange.degree_interpolate_lt (r := fun k => f (ni_chebNode (n + 1) k)) hinj
  rwa [Nat.card_Icc, Nat.add_sub_cancel] at this

/-- Miao, p. 359: the Lagrange-form interpolant `Iₙf` coincides with the coefficient form
`∑ⱼ cⱼ Tⱼ₋₁` computed from `n + 1` nodes. -/
theorem ni_chebInterp_eq_coeff_form (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    (ni_chebInterp n f).eval x = ni_chebInterpolant (n + 1) f x := by
  set P : ℝ[X] := ∑ j : Fin (n + 1), ni_chebCoeff (n + 1) f j • T ℝ (j : ℕ)
  have hP : ∀ y, P.eval y = ni_chebInterpolant (n + 1) f y := by
    intro y
    simp [P, eval_finsetSum, ni_chebInterpolant]
  have hdeg : P.degree < (Finset.Icc 1 (n + 1)).card := by
    simp only [Nat.card_Icc, Nat.add_sub_cancel]
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr fun j _ => ?_
    refine lt_of_le_of_lt (degree_smul_le _ _) ?_
    rw [degree_T, Int.natAbs_natCast]
    exact_mod_cast j.2
  have heq : P = ni_chebInterp n f := by
    refine Lagrange.eq_interpolate_of_eval_eq _ (ni_chebNode_injOn (n + 1)) hdeg fun k hk => ?_
    rw [hP]
    exact ni_chebInterpolant_nodes (n + 1) f k hk
  rw [← heq, hP]

/-- The Lebesgue function `Λₙ(x) = ∑ₖ |ℓₖ(x)|` of the Chebyshev nodes (`ℓₖ` the Lagrange
basis). -/
noncomputable def ni_lebesgueFn (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (n + 1),
    |(Lagrange.basis (Finset.Icc 1 (n + 1)) (ni_chebNode (n + 1)) k).eval x|

/-- Theorem 11.3.1 (Miao, p. 359), first step of the proof (the Lebesgue inequality): for every
polynomial `p` of degree `≤ n`, `|f(x) − Iₙf(x)| ≤ |f(x) − p(x)| + Λₙ(x) maxₖ |f(xₖ) − p(xₖ)|`;
in particular `‖f − Iₙf‖∞ ≤ (1 + Λₙ) ‖f − p‖∞`. -/
theorem ni_lebesgue_inequality (n : ℕ) (f : ℝ → ℝ) (p : ℝ[X]) (hp : p.degree < (n + 1 : ℕ))
    (E : ℝ) (hE : ∀ k ∈ Finset.Icc 1 (n + 1),
      |f (ni_chebNode (n + 1) k) - p.eval (ni_chebNode (n + 1) k)| ≤ E) (x : ℝ) :
    |f x - (ni_chebInterp n f).eval x| ≤ |f x - p.eval x| + ni_lebesgueFn n x * E := by
  set s := Finset.Icc 1 (n + 1)
  set v := ni_chebNode (n + 1)
  have hinj : Set.InjOn v s := ni_chebNode_injOn (n + 1)
  have hcard : p.degree < s.card := by simpa [s] using hp
  have hpI : p = Lagrange.interpolate s v (fun k => p.eval (v k)) :=
    Lagrange.eq_interpolate hinj hcard
  have hdiff : (ni_chebInterp n f).eval x - p.eval x =
      ∑ k ∈ s, (f (v k) - p.eval (v k)) * (Lagrange.basis s v k).eval x := by
    have h1 : ni_chebInterp n f - p =
        Lagrange.interpolate s v (fun k => f (v k) - p.eval (v k)) := by
      conv_lhs => rw [hpI]
      unfold ni_chebInterp
      rw [← map_sub]
      rfl
    rw [← eval_sub, h1, Lagrange.interpolate_apply, eval_finsetSum]
    simp
  have hbound : |(ni_chebInterp n f).eval x - p.eval x| ≤ ni_lebesgueFn n x * E := by
    rw [hdiff, ni_lebesgueFn, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (hE k hk) (abs_nonneg _)
  calc |f x - (ni_chebInterp n f).eval x|
      = |(f x - p.eval x) - ((ni_chebInterp n f).eval x - p.eval x)| := by ring_nf
    _ ≤ |f x - p.eval x| + |(ni_chebInterp n f).eval x - p.eval x| := abs_sub _ _
    _ ≤ _ := by linarith

/-- The uniform norm on `[−1, 1]`, `‖g‖∞ = sup_{x ∈ [−1,1]} |g(x)|`. -/
noncomputable def ni_supNorm (g : ℝ → ℝ) : ℝ := sSup ((fun x => |g x|) '' Set.Icc (-1) 1)

/-- The bound of **Theorem 11.3.1** (Chebyshev Interpolation Theorem, Miao, p. 359) as printed:
there is `dₖ` such that for all `n`,
`‖f − Iₙf‖∞ ≤ ((2/π) ln(n + 1) + 2) (dₖ/nᵏ) ‖f⁽ᵏ⁾‖∞`. -/
def ni_Theorem_11_3_1_bound (k : ℕ) (f : ℝ → ℝ) : Prop :=
  ∃ d : ℝ, ∀ n : ℕ, ni_supNorm (fun x => f x - (ni_chebInterp n f).eval x) ≤
    (2 / π * Real.log (n + 1) + 2) * (d / (n : ℝ) ^ k) * ni_supNorm (iteratedDeriv k f)

/-- **Theorem 11.3.1** (Miao, p. 359) is false as printed ("for all `n`"): `f(x) = x²` is `C^∞`,
take `k = 3`; then `f⁽³⁾ = 0`, so the right side vanishes for every `n`, while for `n = 1` the
interpolant at the roots `±1/√2` of `T₂` is the constant `1/2`, so `‖f − I₁f‖∞ ≥ 1/2`. The
bound (Rivlin) holds only for `n ≥ k`. -/
theorem theorem_11_3_1_counterexample : ¬ ni_Theorem_11_3_1_bound 3 (fun x => x ^ 2) := by
  rintro ⟨d, hd⟩
  have h1 := hd 1
  -- the third derivative vanishes
  have hder : iteratedDeriv 3 (fun x : ℝ => x ^ 2) = fun _ => 0 := by
    have e : (fun x : ℝ => x ^ 2) = fun x => (X ^ 2 : ℝ[X]).eval x := by funext x; simp
    rw [e, ni_iteratedDeriv_eval, iterate_derivative_eq_zero (by simp)]
    simp
  have hzero : ni_supNorm (iteratedDeriv 3 (fun x : ℝ => x ^ 2)) = 0 := by
    rw [hder, ni_supNorm]
    simp only [abs_zero]
    have hne : (Set.Icc (-1 : ℝ) 1).Nonempty := ⟨0, by norm_num, by norm_num⟩
    rw [hne.image_const, csSup_singleton]
  -- the interpolant is the constant `1/2`
  have hI : ni_chebInterp 1 (fun x => x ^ 2) = C (1 / 2) := by
    symm
    refine Lagrange.eq_interpolate_of_eval_eq _ (ni_chebNode_injOn 2) ?_ fun k hk => ?_
    · simp only [Nat.reduceAdd, Nat.card_Icc]
      exact lt_of_le_of_lt degree_C_le (by norm_num)
    · simp only [eval_C]
      have hk' : k = 1 ∨ k = 2 := by
        have := Finset.mem_Icc.mp hk
        omega
      rw [ni_chebNode, cos_sq]
      rcases hk' with rfl | rfl
      · have : 2 * (π * (2 * ((1 : ℕ) : ℝ) - 1) / (2 * ((1 + 1 : ℕ) : ℝ))) = π / 2 := by
          push_cast; ring
        rw [this, cos_pi_div_two]
        norm_num
      · have : 2 * (π * (2 * ((2 : ℕ) : ℝ) - 1) / (2 * ((1 + 1 : ℕ) : ℝ))) = π / 2 + π := by
          push_cast; ring
        rw [this, cos_add_pi, cos_pi_div_two]
        norm_num
  have hlow : (1 : ℝ) / 2 ≤
      ni_supNorm (fun x => x ^ 2 - (ni_chebInterp 1 (fun x => x ^ 2)).eval x) := by
    rw [hI, ni_supNorm]
    have hb : BddAbove ((fun x => |x ^ 2 - (C (1 / 2 : ℝ)).eval x|) '' Set.Icc (-1) 1) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      simp only [eval_C]
      rw [abs_le]
      constructor <;> nlinarith [hx.1, hx.2]
    have hmem : |(0 : ℝ) ^ 2 - (C (1 / 2 : ℝ)).eval 0| ∈
        (fun x => |x ^ 2 - (C (1 / 2 : ℝ)).eval x|) '' Set.Icc (-1) 1 :=
      ⟨0, ⟨by norm_num, by norm_num⟩, rfl⟩
    refine le_trans (le_of_eq ?_) (le_csSup hb hmem)
    simp only [eval_C]
    norm_num
  rw [hzero, mul_zero] at h1
  linarith

end Miao.NumericalMethods

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Lebesgue constant of the Chebyshev nodes (for Theorem 11.3.1)

Ingredient of the proof of Theorem 11.3.1 (Miao, p. 359, citing Rivlin 1990): the Lebesgue
function `Λₙ(x) = ∑ₖ |ℓₖ(x)|` of the `N = n + 1` roots of `T_N` grows only logarithmically,
`Λₙ(x) ≤ 4π (1 + ln(n + 1))` on `[−1, 1]` (`ni_lebesgueFn_le`). (Rivlin's sharp constant is
`(2/π) ln(n + 1) + 1`; any logarithmic bound suffices for Theorem 11.3.1, whose constant `dₖ` is
free.)

* `ni_cheb_deriv_node`: `T_N'(cos θ) sin θ = N sin(Nθ)`; at a node `|T_N'(xₖ)| sin θₖ = N`.
* `ni_basis_mul_eq`: `ℓₖ(x) (x − xₖ) T_N'(xₖ) = T_N(x)`.
* `ni_basis_abs_le`: `|ℓₖ(cos θ)| ≤ 2π / (1 + N|θ − θₖ|)` for `θ ∈ [0, π]`.
* `ni_harmonic_sum_le`: `∑_{k=1}^{N} 1/(1 + |a − k|) ≤ 2(1 + ln N)` for `a ≥ 0`.
-/

open Polynomial Polynomial.Chebyshev Real

namespace Miao.NumericalMethods

/-- The angle `θₖ = π(2k − 1)/(2N)` of the `k`th Chebyshev node. -/
noncomputable def ni_chebAngle (N k : ℕ) : ℝ := π * (2 * k - 1) / (2 * N)

theorem ni_chebAngle_mem {N k : ℕ} (hk : k ∈ Finset.Icc 1 N) :
    0 < ni_chebAngle N k ∧ ni_chebAngle N k < π := by
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hk2' : (k : ℝ) ≤ N := by exact_mod_cast hk2
  have hN : (0 : ℝ) < N := by linarith
  unfold ni_chebAngle
  constructor
  · apply div_pos _ (by positivity)
    exact mul_pos pi_pos (by linarith)
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith [pi_pos]

/-- `T_N'(cos θ) sin θ = N sin(Nθ)`. -/
theorem ni_cheb_deriv_cos (N : ℕ) (θ : ℝ) :
    (derivative (T ℝ N)).eval (cos θ) * sin θ = N * sin (N * θ) := by
  rw [T_derivative_eq_U, eval_mul, mul_assoc]
  have h := U_real_cos θ ((N : ℤ) - 1)
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one, sub_add_cancel] at h
  rw [h]
  simp

/-- At a Chebyshev node, `|T_N'(xₖ)| sin θₖ = N`. -/
theorem ni_cheb_deriv_node {N k : ℕ} (hk : k ∈ Finset.Icc 1 N) :
    |(derivative (T ℝ N)).eval (ni_chebNode N k)| * sin (ni_chebAngle N k) = N := by
  have hsin : 0 < sin (ni_chebAngle N k) :=
    sin_pos_of_pos_of_lt_pi (ni_chebAngle_mem hk).1 (ni_chebAngle_mem hk).2
  have hN : (N : ℝ) ≠ 0 := by
    have := (Finset.mem_Icc.mp hk); exact_mod_cast (show N ≠ 0 by omega)
  have h := ni_cheb_deriv_cos N (ni_chebAngle N k)
  have hnode : ni_chebNode N k = cos (ni_chebAngle N k) := rfl
  have hs : |sin (N * ni_chebAngle N k)| = 1 := by
    have e : (N : ℝ) * ni_chebAngle N k = k * π - π / 2 := by
      unfold ni_chebAngle; field_simp
    rw [e, sin_sub_pi_div_two, cos_nat_mul_pi, abs_neg, abs_pow, abs_neg, abs_one, one_pow]
  rw [hnode, ← abs_of_pos hsin, ← abs_mul, h, abs_mul, hs, mul_one, Nat.abs_cast]

/-- `ℓₖ(x) (x − xₖ) T_N'(xₖ) = T_N(x)` for the Lagrange basis at the roots of `T_N`. -/
theorem ni_basis_mul_eq {N k : ℕ} (hk : k ∈ Finset.Icc 1 N) (x : ℝ) :
    (Lagrange.basis (Finset.Icc 1 N) (ni_chebNode N) k).eval x * (x - ni_chebNode N k) *
      (derivative (T ℝ N)).eval (ni_chebNode N k) = (T ℝ N).eval x := by
  set s := Finset.Icc 1 N
  set v := ni_chebNode N
  have hinj : Set.InjOn v s := ni_chebNode_injOn N
  have hroot : (T ℝ N).IsRoot (v k) := (ni_cheb_roots N (v k)).mpr ⟨k, hk, rfl⟩
  set P := T ℝ N /ₘ (X - C (v k))
  have hP : (X - C (v k)) * P = T ℝ N := mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hder : (derivative (T ℝ N)).eval (v k) = P.eval (v k) := by
    rw [← hP, derivative_mul]
    simp
  have hPk : P.eval (v k) ≠ 0 := by
    rw [← hder]
    intro h0
    have := ni_cheb_deriv_node hk
    rw [h0, abs_zero, zero_mul] at this
    have hN : N ≠ 0 := by have := Finset.mem_Icc.mp hk; omega
    exact hN (by exact_mod_cast this.symm)
  have hcard : s.card = N := by simp [s]
  have hN : 1 ≤ N := (Finset.mem_Icc.mp hk).1.trans (Finset.mem_Icc.mp hk).2
  have hPdeg : P.degree < s.card := by
    rw [hcard]
    have hnat : P.natDegree = N - 1 := by
      rw [natDegree_divByMonic _ (monic_X_sub_C _), natDegree_T, natDegree_X_sub_C]
      simp
    refine (degree_le_natDegree).trans_lt ?_
    rw [hnat]
    exact_mod_cast (show N - 1 < N by omega)
  have hbasis : Lagrange.basis s v k = C (P.eval (v k))⁻¹ * P := by
    refine Polynomial.eq_of_degrees_lt_of_eval_index_eq s hinj ?_ ?_ fun j hj => ?_
    · rw [Lagrange.degree_basis hinj hk]
      exact_mod_cast (show s.card - 1 < s.card by omega)
    · rw [degree_C_mul (inv_ne_zero hPk)]
      exact hPdeg
    · rw [eval_mul, eval_C]
      by_cases hjk : j = k
      · subst hjk
        rw [Lagrange.eval_basis_self hinj hj, inv_mul_cancel₀ hPk]
      · rw [Lagrange.eval_basis_of_ne (Ne.symm hjk) hj]
        have hTj : (T ℝ N).eval (v j) = 0 := (ni_cheb_roots N (v j)).mpr ⟨j, hj, rfl⟩
        rw [← hP, eval_mul] at hTj
        have hne : v j - v k ≠ 0 := sub_ne_zero.mpr fun h => hjk (hinj hj hk h)
        simp only [eval_sub, eval_X, eval_C] at hTj
        rcases mul_eq_zero.mp hTj with h | h
        · exact absurd h hne
        · rw [h, mul_zero]
  rw [hbasis, hder, ← hP]
  simp only [eval_mul, eval_C, eval_sub, eval_X]
  field_simp

/-- `sin θₖ ≤ 2 sin((θ + θₖ)/2)` for `θ, θₖ ∈ [0, π]`. -/
theorem ni_sin_le_two_sin_half {θ φ : ℝ} (hθ : θ ∈ Set.Icc 0 π) (hφ : φ ∈ Set.Icc 0 π) :
    sin φ ≤ 2 * sin ((θ + φ) / 2) := by
  have ha0 : 0 ≤ φ / 2 := by linarith [hφ.1]
  have ha1 : φ / 2 ≤ π / 2 := by linarith [hφ.2]
  have hs : 0 ≤ sin (φ / 2) := sin_nonneg_of_nonneg_of_le_pi ha0 (by linarith)
  have hc : cos (φ / 2) ≤ 1 := cos_le_one _
  have hc0 : 0 ≤ cos (φ / 2) := cos_nonneg_of_mem_Icc ⟨by linarith, ha1⟩
  have hsc : sin (φ / 2) * cos (φ / 2) ≤ sin ((θ + φ) / 2) := by
    by_cases h : (θ + φ) / 2 ≤ π / 2
    · have : sin (φ / 2) ≤ sin ((θ + φ) / 2) :=
        sin_le_sin_of_le_of_le_pi_div_two (by linarith) h (by linarith [hθ.1])
      nlinarith
    · push Not at h
      have e : sin ((θ + φ) / 2) = sin (π - (θ + φ) / 2) := (sin_pi_sub _).symm
      have : cos (φ / 2) ≤ sin (π - (θ + φ) / 2) := by
        rw [← sin_pi_div_two_sub]
        exact sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith)
          (by linarith [hθ.2])
      rw [e]
      nlinarith [sin_le_one (φ / 2)]
  have e2 : sin φ = 2 * sin (φ / 2) * cos (φ / 2) := by
    rw [← sin_two_mul]; ring_nf
  rw [e2]
  linarith

/-- `|ℓₖ(cos θ)| ≤ 2π / (1 + N|θ − θₖ|)` for `θ ∈ [0, π]`. -/
theorem ni_basis_abs_le {N k : ℕ} (hk : k ∈ Finset.Icc 1 N) {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 π) :
    |(Lagrange.basis (Finset.Icc 1 N) (ni_chebNode N) k).eval (cos θ)| ≤
      2 * π / (1 + N * |θ - ni_chebAngle N k|) := by
  set ℓ := |(Lagrange.basis (Finset.Icc 1 N) (ni_chebNode N) k).eval (cos θ)|
  set u := θ - ni_chebAngle N k
  have hφ := ni_chebAngle_mem hk
  have hφI : ni_chebAngle N k ∈ Set.Icc 0 π := ⟨hφ.1.le, hφ.2.le⟩
  have hN : (0 : ℝ) < N := by
    have := Finset.mem_Icc.mp hk; exact_mod_cast (show 0 < N by omega)
  have hden : 0 < 1 + N * |u| := by positivity
  rw [le_div_iff₀ hden]
  by_cases hu : u = 0
  · have : θ = ni_chebAngle N k := by linarith
    have hval : ℓ = 1 := by
      simp only [ℓ, this]
      rw [show cos (ni_chebAngle N k) = ni_chebNode N k from rfl,
        Lagrange.eval_basis_self (ni_chebNode_injOn N) hk, abs_one]
    rw [hval, hu, abs_zero, mul_zero, add_zero, one_mul]
    linarith [pi_gt_three]
  -- the identity `ℓ |cos θ − cos θₖ| |T'(xₖ)| = |cos Nθ|`
  have hid := congrArg abs (ni_basis_mul_eq hk (cos θ))
  rw [abs_mul, abs_mul, ni_cheb_cos] at hid
  have hder := ni_cheb_deriv_node hk
  set D := |(derivative (T ℝ N)).eval (ni_chebNode N k)|
  have hsinφ : 0 < sin (ni_chebAngle N k) := sin_pos_of_pos_of_lt_pi hφ.1 hφ.2
  -- `|cos θ − cos θₖ| = 2 A B`
  set A := sin ((θ + ni_chebAngle N k) / 2)
  set B := |sin (u / 2)|
  have hA : 0 < A := by
    apply sin_pos_of_pos_of_lt_pi
    · linarith [hθ.1, hφ.1]
    · linarith [hθ.2, hφ.2]
  have hcs : |cos θ - ni_chebNode N k| = 2 * A * B := by
    rw [show ni_chebNode N k = cos (ni_chebAngle N k) from rfl, cos_sub_cos, abs_mul, abs_mul]
    simp only [abs_neg, abs_two]
    change 2 * |A| * |sin (u / 2)| = 2 * A * B
    rw [abs_of_pos hA]
  have hsA := ni_sin_le_two_sin_half hθ hφI
  -- `ℓ N B ≤ |cos Nθ|`
  have h1 : ℓ * N * B ≤ |cos (N * θ)| := by
    have e : ℓ * (2 * A * B) * D = |cos (N * θ)| := by rw [← hcs]; exact hid
    have e2 : D * sin (ni_chebAngle N k) = N := hder
    have hD : 0 ≤ D := abs_nonneg _
    have hℓ : 0 ≤ ℓ := abs_nonneg _
    have hB : 0 ≤ B := abs_nonneg _
    -- `ℓ N B * 2A = ℓ D sin θₖ B * 2A / sin θₖ ≤ …`
    have : ℓ * N * B * sin (ni_chebAngle N k) ≤ |cos (N * θ)| * sin (ni_chebAngle N k) := by
      calc ℓ * N * B * sin (ni_chebAngle N k)
          = ℓ * B * D * sin (ni_chebAngle N k) * sin (ni_chebAngle N k) := by
            rw [← e2]; ring
        _ ≤ ℓ * B * D * sin (ni_chebAngle N k) * (2 * A) := by
            gcongr
        _ = |cos (N * θ)| * sin (ni_chebAngle N k) := by rw [← e]; ring
    exact le_of_mul_le_mul_right this hsinφ
  -- `B ≥ |u|/π`
  have hu_le : |u| ≤ π := by
    rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2, hφ.1, hφ.2]
  have hu2 := abs_le.mp hu_le
  have hB : |u| / π ≤ B := by
    have habs : B = sin (|u| / 2) := by
      rcases le_total 0 u with h | h
      · rw [abs_of_nonneg h]
        exact abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))
      · rw [abs_of_nonpos h, show -u / 2 = -(u / 2) by ring, sin_neg]
        refine abs_of_nonpos ?_
        have : 0 ≤ sin (-(u / 2)) :=
          sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [abs_of_nonpos h])
        rw [sin_neg] at this
        linarith
    rw [habs]
    have := mul_le_sin (x := |u| / 2) (by positivity) (by linarith)
    calc |u| / π = 2 / π * (|u| / 2) := by ring
      _ ≤ _ := this
  -- `|cos Nθ| ≤ 1` and `≤ N|u|`
  have hc1 : |cos (N * θ)| ≤ 1 := abs_cos_le_one _
  have hc2 : |cos (N * θ)| ≤ N * |u| := by
    have h0 : cos (N * ni_chebAngle N k) = 0 := by
      have e : (N : ℝ) * ni_chebAngle N k = (2 * k - 1) * (π / 2) := by
        unfold ni_chebAngle; field_simp
      rw [e, cos_eq_zero_iff]
      refine ⟨k - 1, ?_⟩
      push_cast
      ring
    have := abs_cos_sub_cos_le (N * θ) (N * ni_chebAngle N k)
    rw [h0, sub_zero, ← mul_sub, abs_mul, Nat.abs_cast] at this
    exact this
  have hpi := pi_pos
  have hℓ0 : 0 ≤ ℓ := abs_nonneg _
  have key : ℓ * (N * |u|) ≤ π * |cos (N * θ)| := by
    have : ℓ * N * (|u| / π) ≤ |cos (N * θ)| :=
      le_trans (mul_le_mul_of_nonneg_left hB (by positivity)) h1
    rw [mul_div_assoc'] at this
    rw [div_le_iff₀ hpi] at this
    linarith
  have hupos : 0 < N * |u| := mul_pos hN (abs_pos.mpr hu)
  rcases le_total (N * |u|) 1 with hsmall | hbig
  · have hℓπ : ℓ ≤ π := by
      have : ℓ * (N * |u|) ≤ π * (N * |u|) := by nlinarith
      exact le_of_mul_le_mul_right this hupos
    nlinarith
  · have h2 : ℓ * (N * |u|) ≤ π := by nlinarith
    have hℓπ : ℓ ≤ π := by nlinarith
    nlinarith

/-- `∑_{j < r} 1/(1 + j) ≤ 1 + ln N` for `r ≤ N`. -/
theorem ni_harmonic_le {r N : ℕ} (hr : r ≤ N) :
    ∑ j ∈ Finset.range r, (1 : ℝ) / (1 + j) ≤ 1 + Real.log N := by
  have h1 : ∑ j ∈ Finset.range r, (1 : ℝ) / (1 + j) ≤ ∑ j ∈ Finset.range N, (1 : ℝ) / (1 + j) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hr)
      (fun j _ _ => by positivity)
  have h2 : ∑ j ∈ Finset.range N, (1 : ℝ) / (1 + j) = (harmonic N : ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  linarith [harmonic_le_one_add_log N]

/-- `∑_{k=1}^{N} 1/(1 + |a − k|) ≤ 2(1 + ln N)` for `a ≥ 0`. -/
theorem ni_harmonic_sum_le (N : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / (1 + |a - k|) ≤ 2 * (1 + Real.log N) := by
  set m := min ⌊a⌋₊ N
  have hmN : m ≤ N := min_le_right _ _
  have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext k; simp [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hIcc, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le m) hmN]
  have hA : ∑ k ∈ Finset.Ioc 0 m, (1 : ℝ) / (1 + |a - k|) ≤ 1 + Real.log N := by
    have hle : ∀ k ∈ Finset.Ioc 0 m, (1 : ℝ) / (1 + |a - k|) ≤ 1 / (1 + ((m - k : ℕ) : ℝ)) := by
      intro k hk
      have hkm : k ≤ m := (Finset.mem_Ioc.mp hk).2
      have hka : (k : ℝ) ≤ a := by
        have : (m : ℝ) ≤ a := by
          calc (m : ℝ) ≤ (⌊a⌋₊ : ℝ) := by exact_mod_cast min_le_left _ _
            _ ≤ a := Nat.floor_le ha
        exact le_trans (by exact_mod_cast hkm) this
      have hma : (m : ℝ) ≤ a := by
        calc (m : ℝ) ≤ (⌊a⌋₊ : ℝ) := by exact_mod_cast min_le_left _ _
          _ ≤ a := Nat.floor_le ha
      rw [abs_of_nonneg (by linarith), Nat.cast_sub hkm]
      apply one_div_le_one_div_of_le (by
        have : (k : ℝ) ≤ m := by exact_mod_cast hkm
        linarith)
      linarith
    refine (Finset.sum_le_sum hle).trans (le_of_eq_of_le ?_ (ni_harmonic_le hmN))
    refine Finset.sum_nbij' (fun k => m - k) (fun j => m - j) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      have := Finset.mem_Ioc.mp hk
      exact Finset.mem_range.mpr (by omega)
    · intro j hj
      have := Finset.mem_range.mp hj
      exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
    · intro k hk
      have := Finset.mem_Ioc.mp hk
      omega
    · intro j hj
      have := Finset.mem_range.mp hj
      omega
    · intro k _
      rfl
  have hB : ∑ k ∈ Finset.Ioc m N, (1 : ℝ) / (1 + |a - k|) ≤ 1 + Real.log N := by
    have hle : ∀ k ∈ Finset.Ioc m N, (1 : ℝ) / (1 + |a - k|) ≤
        1 / (1 + ((k - m - 1 : ℕ) : ℝ)) := by
      intro k hk
      have hk' := Finset.mem_Ioc.mp hk
      have hmlt : m < N := lt_of_lt_of_le hk'.1 hk'.2
      have hm : m = ⌊a⌋₊ := by
        rcases min_cases ⌊a⌋₊ N with h | h
        · exact h.1
        · omega
      have hak : a < k := by
        have h1 : a < ⌊a⌋₊ + 1 := Nat.lt_floor_add_one a
        have h2 : ((⌊a⌋₊ : ℕ) : ℝ) + 1 ≤ k := by
          rw [← hm]; exact_mod_cast hk'.1
        linarith
      have hcast : ((k - m - 1 : ℕ) : ℝ) = k - m - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        simp
      rw [abs_of_neg (by linarith), hcast]
      have hfa : (m : ℝ) ≤ a := by rw [hm]; exact Nat.floor_le ha
      have hfa2 : a < m + 1 := by rw [hm]; exact Nat.lt_floor_add_one a
      have hpos : (0 : ℝ) < 1 + (k - m - 1) := by
        have : (m : ℝ) + 1 ≤ k := by exact_mod_cast hk'.1
        linarith
      apply one_div_le_one_div_of_le hpos
      linarith
    refine (Finset.sum_le_sum hle).trans (le_of_eq_of_le ?_ (ni_harmonic_le (r := N - m)
      (by omega)))
    refine Finset.sum_nbij' (fun k => k - m - 1) (fun j => j + m + 1) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      have := Finset.mem_Ioc.mp hk
      exact Finset.mem_range.mpr (by omega)
    · intro j hj
      have := Finset.mem_range.mp hj
      exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
    · intro k hk
      have := Finset.mem_Ioc.mp hk
      omega
    · intro j _
      omega
    · intro k _
      rfl
  linarith

/-- The Lebesgue function of the Chebyshev nodes is at most `4π(1 + ln(n + 1))` on `[−1, 1]`. -/
theorem ni_lebesgueFn_le (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ni_lebesgueFn n x ≤ 4 * π * (1 + Real.log (n + 1)) := by
  set N := n + 1
  set θ := arccos x
  have hθ : θ ∈ Set.Icc 0 π := ⟨arccos_nonneg x, arccos_le_pi x⟩
  have hxθ : x = cos θ := (cos_arccos hx.1 hx.2).symm
  set a := N * θ / π + 1 / 2
  have ha : 0 ≤ a := by
    have : 0 ≤ (N : ℝ) * θ / π := div_nonneg (mul_nonneg (by positivity) hθ.1) pi_pos.le
    simp only [a]
    linarith
  have hterm : ∀ k ∈ Finset.Icc 1 N,
      |(Lagrange.basis (Finset.Icc 1 N) (ni_chebNode N) k).eval x| ≤
        2 * π * (1 / (1 + |a - k|)) := by
    intro k hk
    rw [hxθ]
    refine (ni_basis_abs_le hk hθ).trans ?_
    rw [mul_one_div]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    -- `|a − k| ≤ N|θ − θₖ|`
    have e : (N : ℝ) * (θ - ni_chebAngle N k) = π * (a - k) := by
      have hN : (N : ℝ) ≠ 0 := by positivity
      simp only [a, ni_chebAngle]
      field_simp
      ring
    have : |a - k| ≤ N * |θ - ni_chebAngle N k| := by
      have h1 : (N : ℝ) * |θ - ni_chebAngle N k| = π * |a - k| := by
        rw [← abs_of_nonneg (show (0 : ℝ) ≤ N by positivity), ← abs_mul, e, abs_mul,
          abs_of_pos pi_pos]
      rw [h1]
      have : 1 ≤ π := by linarith [pi_gt_three]
      nlinarith [abs_nonneg (a - k)]
    linarith
  unfold ni_lebesgueFn
  calc ∑ k ∈ Finset.Icc 1 (n + 1),
        |(Lagrange.basis (Finset.Icc 1 (n + 1)) (ni_chebNode (n + 1)) k).eval x|
      ≤ ∑ k ∈ Finset.Icc 1 N, 2 * π * (1 / (1 + |a - k|)) := Finset.sum_le_sum hterm
    _ = 2 * π * ∑ k ∈ Finset.Icc 1 N, 1 / (1 + |a - k|) := by rw [Finset.mul_sum]
    _ ≤ 2 * π * (2 * (1 + Real.log N)) := by
        gcongr
        exact ni_harmonic_sum_le N ha
    _ = 4 * π * (1 + Real.log (n + 1)) := by
        simp only [N]; push_cast; ring

end Miao.NumericalMethods

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Jackson's theorem for Lipschitz functions (for Theorem 11.3.1)

Ingredient of the proof of Theorem 11.3.1 (Miao, p. 359, citing Rivlin 1990): a function that is
`M`-Lipschitz on `[−1, 1]` can be approximated by a polynomial of degree `≤ n` to within
`C M / n` uniformly on `[−1, 1]`, with the absolute constant `C = 12(1 + π⁴)/π`
(`ni_jackson_lipschitz`).

The proof is Jackson's: put `g(θ) = f(cos θ)` (even, `2π`-periodic, `M`-Lipschitz) and convolve
it with the Jackson kernel `K(t) = F_m(t)²`, where `F_m(t) = ∑_{i<m} (1 + 2∑_{j=1}^{i} cos jt)` is
the Fejér kernel, `(1 − cos t) F_m(t) = 1 − cos mt` (`ni_fej_identity`). Since `K` is a cosine
polynomial of degree `2m − 2` and `g` is even, the convolution is a polynomial in `cos θ`
(`ni_conv_poly`); the error is at most `M ∫|t|K / ∫K ≤ 6(1 + π⁴) M / (π m)` (`ni_jackK_mass_ge`,
`ni_jackK_moment_le`).
-/

open Polynomial Polynomial.Chebyshev Real

namespace Miao.NumericalMethods

/-- Every polynomial of degree `< D` is a combination of `T₀, …, T_{D−1}`. -/
theorem ni_cheb_expand (R : ℝ[X]) (D : ℕ) (hR : R.degree < D) :
    ∃ c : ℕ → ℝ, ∀ y, R.eval y = ∑ i ∈ Finset.range D, c i * (T ℝ (i : ℤ)).eval y := by
  have hmem : R ∈ degreeLT ℝ D := by rwa [mem_degreeLT]
  rw [← Sequence.span_degreeLT (chebyshevTsequence ℝ) (by simp),
    show Set.Iio D = Finset.range D by simp,
    Submodule.mem_span_image_finset_iff_exists_fun'] at hmem
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c, fun y => ?_⟩
  rw [← hc, eval_finsetSum]
  simp [chebyshevTsequence]

/-- The Dirichlet polynomial `1 + 2∑_{j=1}^{i} T_j`. -/
noncomputable def ni_dirPoly (i : ℕ) : ℝ[X] := 1 + 2 * ∑ j ∈ Finset.Icc 1 i, T ℝ (j : ℤ)

/-- The Fejér polynomial `∑_{i<m} (1 + 2∑_{j=1}^{i} T_j)`. -/
noncomputable def ni_fejPoly (m : ℕ) : ℝ[X] := ∑ i ∈ Finset.range m, ni_dirPoly i

/-- The (unnormalised) Jackson polynomial `F_m²`. -/
noncomputable def ni_jackPoly (m : ℕ) : ℝ[X] := ni_fejPoly m ^ 2

/-- The Jackson kernel `K(t) = F_m(cos t)²`. -/
noncomputable def ni_jackK (m : ℕ) (t : ℝ) : ℝ := (ni_jackPoly m).eval (cos t)

/-- The Dirichlet sum `1 + 2∑_{j=1}^{i} cos jt`. -/
noncomputable def ni_dir (i : ℕ) (t : ℝ) : ℝ := 1 + 2 * ∑ j ∈ Finset.Icc 1 i, cos (j * t)

/-- The Fejér sum `∑_{i<m} (1 + 2∑_{j=1}^{i} cos jt)`. -/
noncomputable def ni_fej (m : ℕ) (t : ℝ) : ℝ := ∑ i ∈ Finset.range m, ni_dir i t

theorem ni_dirPoly_eval (i : ℕ) (t : ℝ) : (ni_dirPoly i).eval (cos t) = ni_dir i t := by
  simp [ni_dirPoly, ni_dir, eval_finsetSum]

theorem ni_fejPoly_eval (m : ℕ) (t : ℝ) : (ni_fejPoly m).eval (cos t) = ni_fej m t := by
  simp [ni_fejPoly, ni_fej, eval_finsetSum, ni_dirPoly_eval]

theorem ni_jackK_eq (m : ℕ) (t : ℝ) : ni_jackK m t = ni_fej m t ^ 2 := by
  simp [ni_jackK, ni_jackPoly, ni_fejPoly_eval]

theorem ni_jackK_nonneg (m : ℕ) (t : ℝ) : 0 ≤ ni_jackK m t := by
  rw [ni_jackK_eq]; positivity

theorem ni_jackK_continuous (m : ℕ) : Continuous (ni_jackK m) :=
  (Polynomial.continuous _).comp continuous_cos

theorem ni_jackK_even (m : ℕ) (t : ℝ) : ni_jackK m (-t) = ni_jackK m t := by
  simp [ni_jackK, cos_neg]

theorem ni_jackK_periodic (m : ℕ) (t : ℝ) : ni_jackK m (t + 2 * π) = ni_jackK m t := by
  simp [ni_jackK, cos_add_two_pi]

theorem ni_jackPoly_natDegree (m : ℕ) : (ni_jackPoly m).natDegree ≤ 2 * (m - 1) := by
  have hd : ∀ i, (ni_dirPoly i).natDegree ≤ i := by
    intro i
    unfold ni_dirPoly
    refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
    refine (natDegree_mul_le).trans ?_
    have : (∑ j ∈ Finset.Icc 1 i, T ℝ (j : ℤ)).natDegree ≤ i := by
      refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
      rw [natDegree_T, Int.natAbs_natCast]
      exact (Finset.mem_Icc.mp hj).2
    have h2 : (2 : ℝ[X]).natDegree = 0 := natDegree_ofNat 2
    omega
  have hf : (ni_fejPoly m).natDegree ≤ m - 1 := by
    unfold ni_fejPoly
    refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    exact (hd i).trans (by have := Finset.mem_range.mp hi; omega)
  unfold ni_jackPoly
  exact natDegree_pow_le.trans (Nat.mul_le_mul_left 2 hf)

/-- `(1 − cos t)(1 + 2∑_{j=1}^{i} cos jt) = cos it − cos (i + 1)t`. -/
theorem ni_dir_identity (i : ℕ) (t : ℝ) :
    (1 - cos t) * ni_dir i t = cos (i * t) - cos ((i + 1) * t) := by
  induction i with
  | zero => simp [ni_dir]
  | succ i ih =>
    unfold ni_dir at ih ⊢
    rw [Finset.sum_Icc_succ_top (by omega)]
    have htrig : cos ((i + 1 + 1) * t) + cos (i * t) = 2 * cos ((i + 1) * t) * cos t := by
      have e1 : (i + 1 + 1) * t = (i + 1) * t + t := by ring
      have e2 : (i : ℝ) * t = (i + 1) * t - t := by ring
      rw [e1, e2, cos_add, cos_sub]
      ring
    push_cast
    linear_combination ih + htrig

/-- `(1 − cos t) F_m(t) = 1 − cos mt` (Fejér). -/
theorem ni_fej_identity (m : ℕ) (t : ℝ) : (1 - cos t) * ni_fej m t = 1 - cos (m * t) := by
  unfold ni_fej
  rw [Finset.mul_sum]
  simp_rw [ni_dir_identity]
  have h := Finset.sum_range_sub' (fun i : ℕ => cos ((i : ℝ) * t)) m
  push_cast at h
  rw [h]
  simp

/-- `|F_m(t)| ≤ m²`. -/
theorem ni_fej_abs_le (m : ℕ) (t : ℝ) : |ni_fej m t| ≤ m ^ 2 := by
  have hd : ∀ i, |ni_dir i t| ≤ 1 + 2 * i := by
    intro i
    unfold ni_dir
    refine (abs_add_le _ _).trans ?_
    rw [abs_one, abs_mul, abs_two]
    have : |∑ j ∈ Finset.Icc 1 i, cos (j * t)| ≤ i := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun j _ => abs_cos_le_one _).trans ?_
      simp
    linarith
  have hsum : ∀ m : ℕ, ∑ i ∈ Finset.range m, (1 + 2 * (i : ℝ)) = m ^ 2 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  unfold ni_fej
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [← hsum m]
  exact Finset.sum_le_sum fun i _ => hd i

/-- Near `0`: `F_m(t) ≥ m²/2` for `|t| ≤ π/(3m)`. -/
theorem ni_fej_ge {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : |t| ≤ π / (3 * m)) :
    (m : ℝ) ^ 2 / 2 ≤ ni_fej m t := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hcos : ∀ j : ℕ, j < m → 1 / 2 ≤ cos (j * t) := by
    intro j hj
    have hj' : (j : ℝ) ≤ m := by exact_mod_cast hj.le
    have h1 : |(j : ℝ) * t| ≤ π / 3 := by
      rw [abs_mul, Nat.abs_cast]
      calc (j : ℝ) * |t| ≤ m * (π / (3 * m)) := by gcongr
        _ = π / 3 := by field_simp
    rw [← cos_abs, ← cos_pi_div_three]
    exact cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [pi_pos]) h1
  have hd : ∀ i ∈ Finset.range m, 1 + (i : ℝ) ≤ ni_dir i t := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    unfold ni_dir
    have : (i : ℝ) / 2 ≤ ∑ j ∈ Finset.Icc 1 i, cos (j * t) := by
      have h : ∑ j ∈ Finset.Icc 1 i, (1 : ℝ) / 2 ≤ ∑ j ∈ Finset.Icc 1 i, cos (j * t) :=
        Finset.sum_le_sum fun j hj => hcos j (by have := (Finset.mem_Icc.mp hj).2; omega)
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at h
      simp only [Nat.add_sub_cancel] at h
      linarith
    linarith
  have hsum : ∀ m : ℕ, ∑ i ∈ Finset.range m, (1 + (i : ℝ)) = m * (m + 1) / 2 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  unfold ni_fej
  have := Finset.sum_le_sum hd
  rw [hsum m] at this
  nlinarith

/-- `1 − cos t ≥ 2t²/π²` for `|t| ≤ π`. -/
theorem ni_one_sub_cos_ge {t : ℝ} (ht : |t| ≤ π) : 2 * t ^ 2 / π ^ 2 ≤ 1 - cos t := by
  have hs : |t| / π ≤ sin (|t| / 2) := by
    have := mul_le_sin (x := |t| / 2) (by positivity) (by linarith)
    calc |t| / π = 2 / π * (|t| / 2) := by ring
      _ ≤ _ := this
  have hcos : cos t = 1 - 2 * sin (|t| / 2) ^ 2 := by
    rw [← cos_abs, show |t| = 2 * (|t| / 2) by ring, cos_two_mul, ← sin_sq_add_cos_sq (|t| / 2)]
    ring_nf
  have h0 : 0 ≤ |t| / π := div_nonneg (abs_nonneg _) pi_pos.le
  have hsq : (|t| / π) ^ 2 ≤ sin (|t| / 2) ^ 2 := pow_le_pow_left₀ h0 hs 2
  rw [div_pow, sq_abs] at hsq
  rw [hcos]
  have : 2 * t ^ 2 / π ^ 2 = 2 * (t ^ 2 / π ^ 2) := by ring
  linarith

/-- Away from `0`: `0 ≤ F_m(t) ≤ π²/t²` for `0 < |t| ≤ π`. -/
theorem ni_fej_le {m : ℕ} {t : ℝ} (ht0 : t ≠ 0) (ht : |t| ≤ π) :
    0 ≤ ni_fej m t ∧ ni_fej m t ≤ π ^ 2 / t ^ 2 := by
  have hc := ni_one_sub_cos_ge ht
  have hpos : 0 < 2 * t ^ 2 / π ^ 2 := by positivity
  have hden : 0 < 1 - cos t := lt_of_lt_of_le hpos hc
  have hid := ni_fej_identity m t
  have hF : ni_fej m t = (1 - cos (m * t)) / (1 - cos t) := by
    field_simp; linarith
  have hnum0 : 0 ≤ 1 - cos (m * t) := by linarith [cos_le_one (m * t)]
  have hnum2 : 1 - cos (m * t) ≤ 2 := by linarith [neg_one_le_cos (m * t)]
  refine ⟨by rw [hF]; positivity, ?_⟩
  rw [hF, div_le_div_iff₀ hden (by positivity)]
  have : 2 * t ^ 2 ≤ π ^ 2 * (1 - cos t) := by
    have := mul_le_mul_of_nonneg_left hc (sq_nonneg π)
    rwa [mul_div_cancel₀ _ (by positivity)] at this
  nlinarith

/-- The mass of the Jackson kernel: `∫_{−π}^{π} K ≥ π m³/6`. -/
theorem ni_jackK_mass_ge {m : ℕ} (hm : 1 ≤ m) :
    π * (m : ℝ) ^ 3 / 6 ≤ ∫ t in -π..π, ni_jackK m t := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set δ := π / (3 * m)
  have hδ : 0 < δ := by positivity
  have hδπ : δ ≤ π := by
    rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith [pi_pos]
  have hint := (ni_jackK_continuous m).intervalIntegrable (μ := MeasureTheory.volume) (-π) π
  have h1 : ∫ t in -δ..δ, ni_jackK m t ≤ ∫ t in -π..π, ni_jackK m t :=
    intervalIntegral.integral_mono_interval (by linarith) (by linarith) hδπ
      (Filter.Eventually.of_forall fun t => ni_jackK_nonneg m t) hint
  have h2 : ∫ t in -δ..δ, ((m : ℝ) ^ 2 / 2) ^ 2 ≤ ∫ t in -δ..δ, ni_jackK m t := by
    refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      ((ni_jackK_continuous m).intervalIntegrable _ _) fun t ht => ?_
    rw [ni_jackK_eq]
    have hab : |t| ≤ δ := abs_le.mpr ⟨ht.1, ht.2⟩
    have := ni_fej_ge hm hab
    have h0 : 0 ≤ (m : ℝ) ^ 2 / 2 := by positivity
    exact pow_le_pow_left₀ h0 this 2
  rw [intervalIntegral.integral_const, smul_eq_mul] at h2
  have e : (δ - -δ) * ((m : ℝ) ^ 2 / 2) ^ 2 = π * (m : ℝ) ^ 3 / 6 := by
    simp only [δ]; field_simp; ring
  linarith

/-- The first moment of the Jackson kernel: `∫_{−π}^{π} |t| K(t) dt ≤ (1 + π⁴) m²`. -/
theorem ni_jackK_moment_le {m : ℕ} (hm : 1 ≤ m) :
    ∫ t in -π..π, |t| * ni_jackK m t ≤ (1 + π ^ 4) * (m : ℝ) ^ 2 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hcont : Continuous fun t => |t| * ni_jackK m t :=
    continuous_abs.mul (ni_jackK_continuous m)
  have hii : ∀ a b : ℝ, IntervalIntegrable (fun t => |t| * ni_jackK m t)
      MeasureTheory.volume a b := fun a b => hcont.intervalIntegrable a b
  -- evenness
  have heven : ∫ t in -π..0, |t| * ni_jackK m t = ∫ t in (0 : ℝ)..π, |t| * ni_jackK m t := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := π)
      (fun t => |t| * ni_jackK m t)
    simp only [abs_neg, ni_jackK_even, neg_zero] at this
    exact this.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals (hii (-π) 0) (hii 0 π), heven]
  -- split `[0, π]` at `1/m`
  set a := 1 / (m : ℝ)
  have ha : 0 < a := by positivity
  have haπ : a ≤ π := by
    have : a ≤ 1 := by rw [div_le_one hm']; exact hm1
    linarith [pi_gt_three]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hii 0 a) (hii a π)]
  have hA : ∫ t in (0 : ℝ)..a, |t| * ni_jackK m t ≤ (m : ℝ) ^ 2 / 2 := by
    have h := intervalIntegral.integral_mono_on ha.le (hii 0 a)
      ((continuous_id.mul continuous_const).intervalIntegrable (μ := MeasureTheory.volume) 0 a)
      (g := fun t => t * (m : ℝ) ^ 4) fun t ht => by
        rw [abs_of_nonneg ht.1, ni_jackK_eq]
        have hF := ni_fej_abs_le m t
        have : ni_fej m t ^ 2 ≤ (m : ℝ) ^ 4 := by
          have := pow_le_pow_left₀ (abs_nonneg _) hF 2
          rw [sq_abs] at this
          linarith [show ((m : ℝ) ^ 2) ^ 2 = (m : ℝ) ^ 4 by ring]
        exact mul_le_mul_of_nonneg_left this ht.1
    refine h.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_mul_const, integral_id]
    simp only [a]
    field_simp
    ring
  have hB : ∫ t in a..π, |t| * ni_jackK m t ≤ π ^ 4 * ((m : ℝ) ^ 2 / 2) := by
    have hcube : ContinuousOn (fun t : ℝ => π ^ 4 * (1 / t ^ 3)) (Set.uIcc a π) := by
      refine continuousOn_const.mul (continuousOn_const.div (continuousOn_pow 3) fun t ht => ?_)
      rw [Set.uIcc_of_le haπ] at ht
      have : 0 < t := lt_of_lt_of_le ha ht.1
      positivity
    have h := intervalIntegral.integral_mono_on haπ (hii a π) (hcube.intervalIntegrable)
      fun t ht => by
        have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
        have htπ : |t| ≤ π := by rw [abs_of_pos ht0]; exact ht.2
        rw [abs_of_pos ht0, ni_jackK_eq]
        obtain ⟨hF0, hF1⟩ := ni_fej_le (m := m) ht0.ne' htπ
        have hsq : ni_fej m t ^ 2 ≤ (π ^ 2 / t ^ 2) ^ 2 := pow_le_pow_left₀ hF0 hF1 2
        calc t * ni_fej m t ^ 2 ≤ t * (π ^ 2 / t ^ 2) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq ht0.le
          _ = π ^ 4 * (1 / t ^ 3) := by field_simp
    refine h.trans ?_
    rw [intervalIntegral.integral_const_mul]
    have hderiv : ∀ t ∈ Set.uIcc a π, HasDerivAt (fun t : ℝ => -1 / (2 * t ^ 2)) (1 / t ^ 3) t := by
      intro t ht
      rw [Set.uIcc_of_le haπ] at ht
      have ht0 : t ≠ 0 := (lt_of_lt_of_le ha ht.1).ne'
      have := ((hasDerivAt_pow 2 t).const_mul 2).inv (by positivity)
      convert this.const_mul (-1) using 1
      · funext s; simp [div_eq_mul_inv]
      · field_simp; ring
    have hint : IntervalIntegrable (fun t : ℝ => 1 / t ^ 3) MeasureTheory.volume a π := by
      refine ContinuousOn.intervalIntegrable ?_
      refine continuousOn_const.div (continuousOn_pow 3) fun t ht => ?_
      rw [Set.uIcc_of_le haπ] at ht
      have : 0 < t := lt_of_lt_of_le ha ht.1
      positivity
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    have hval : -1 / (2 * π ^ 2) - -1 / (2 * a ^ 2) ≤ (m : ℝ) ^ 2 / 2 := by
      have : -1 / (2 * a ^ 2) = -((m : ℝ) ^ 2 / 2) := by simp only [a]; field_simp
      rw [this]
      have : 0 < 1 / (2 * π ^ 2) := by positivity
      have e : -1 / (2 * π ^ 2) = -(1 / (2 * π ^ 2)) := by ring
      linarith
    exact mul_le_mul_of_nonneg_left hval (by positivity)
  linarith

end Miao.NumericalMethods

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Jackson's theorem (for Theorem 11.3.1)

Ingredient of the proof of Theorem 11.3.1 (Miao, p. 359, citing Rivlin 1990).

* `ni_conv_poly`: convolving an even `2π`-periodic continuous `g` with the Jackson kernel gives a
  polynomial of degree `≤ 2(m − 1)` in `cos θ`.
* `ni_jackson_lipschitz` (Jackson): an `M`-Lipschitz function on `[−1, 1]` is within
  `12(1 + π⁴)/π · M/n` of a polynomial of degree `≤ n` (`n ≥ 1`), uniformly on `[−1, 1]`.
-/

open Polynomial Polynomial.Chebyshev Real

namespace Miao.NumericalMethods

/-- The convolution of an even, `2π`-periodic, continuous `g` with the Jackson kernel is a
polynomial of degree `≤ 2(m − 1)` in `cos θ`. -/
theorem ni_conv_poly (m : ℕ) (g : ℝ → ℝ) (hg : Continuous g) (hgeven : ∀ s, g (-s) = g s)
    (hgper : ∀ s, g (s + 2 * π) = g s) :
    ∃ p : ℝ[X], p.natDegree ≤ 2 * (m - 1) ∧
      ∀ θ, ∫ t in -π..π, ni_jackK m t * g (θ - t) = p.eval (cos θ) := by
  set D := 2 * (m - 1) + 1
  have hdegR : (ni_jackPoly m).degree < D := by
    refine (degree_le_natDegree).trans_lt ?_
    exact_mod_cast Nat.lt_succ_of_le (ni_jackPoly_natDegree m)
  obtain ⟨c, hc⟩ := ni_cheb_expand (ni_jackPoly m) D hdegR
  set α : ℕ → ℝ := fun i => ∫ s in -π..π, cos (i * s) * g s
  refine ⟨∑ i ∈ Finset.range D, C (c i * α i) * T ℝ (i : ℤ), ?_, fun θ => ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_T, Int.natAbs_natCast]
    have := Finset.mem_range.mp hi
    omega
  -- shift to `∫ K(θ − s) g(s) ds`
  have hshift : ∫ t in -π..π, ni_jackK m t * g (θ - t) =
      ∫ s in -π..π, ni_jackK m (θ - s) * g s := by
    have h1 := intervalIntegral.integral_comp_sub_left
      (fun s => ni_jackK m (θ - s) * g s) θ (a := -π) (b := π)
    simp only [sub_sub_cancel] at h1
    rw [h1]
    have hper : Function.Periodic (fun s => ni_jackK m (θ - s) * g s) (2 * π) := by
      intro s
      simp only
      rw [hgper, show θ - (s + 2 * π) = θ - s - 2 * π by ring]
      have := ni_jackK_periodic m (θ - s - 2 * π)
      rw [sub_add_cancel] at this
      rw [this]
    have h2 := hper.intervalIntegral_add_eq (θ - π) (-π)
    rw [show θ - π + 2 * π = θ - -π by ring, show -π + 2 * π = π by ring,
      show θ - π = θ - π by rfl] at h2
    rw [h2]
  rw [hshift]
  -- expand the kernel
  have hK : ∀ s, ni_jackK m (θ - s) * g s = ∑ i ∈ Finset.range D,
      ((c i * cos (i * θ)) * (cos (i * s) * g s) + (c i * sin (i * θ)) * (sin (i * s) * g s)) := by
    intro s
    rw [ni_jackK, hc, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := ni_cheb_cos i (θ - s)
    rw [this, mul_sub, cos_sub]
    ring
  simp_rw [hK]
  have hcont1 : ∀ i : ℕ, Continuous fun s => cos (i * s) * g s := fun i =>
    (continuous_cos.comp (continuous_const.mul continuous_id)).mul hg
  have hcont2 : ∀ i : ℕ, Continuous fun s => sin (i * s) * g s := fun i =>
    (continuous_sin.comp (continuous_const.mul continuous_id)).mul hg
  rw [intervalIntegral.integral_finsetSum (f := fun i s =>
    (c i * cos (i * θ)) * (cos (i * s) * g s) + (c i * sin (i * θ)) * (sin (i * s) * g s))
    fun i _ => by apply Continuous.intervalIntegrable; fun_prop]
  -- the sine moments vanish by evenness of `g`
  have hβ : ∀ i : ℕ, ∫ s in -π..π, sin (i * s) * g s = 0 := by
    intro i
    have h := intervalIntegral.integral_comp_neg (a := -π) (b := π)
      (fun s => sin (i * s) * g s)
    simp only [neg_neg, mul_neg, sin_neg, hgeven, neg_mul] at h
    rw [intervalIntegral.integral_neg] at h
    linarith
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_add ((hcont1 i).const_mul _ |>.intervalIntegrable _ _)
    ((hcont2 i).const_mul _ |>.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hβ, eval_mul, eval_C, ni_cheb_cos]
  simp only [α]
  ring

/-- The constant of Jackson's theorem, `12(1 + π⁴)/π`. -/
noncomputable def ni_jacksonC : ℝ := 12 * (1 + π ^ 4) / π

theorem ni_jacksonC_pos : 0 < ni_jacksonC := by
  unfold ni_jacksonC; positivity

/-- **Jackson's theorem** for Lipschitz functions (used in the proof of Theorem 11.3.1, Miao,
p. 359): if `|f(x) − f(y)| ≤ M|x − y|` on `[−1, 1]` then for every `n ≥ 1` there is a polynomial
`p` of degree `≤ n` with `|f(x) − p(x)| ≤ 12(1 + π⁴)/π · M/n` on `[−1, 1]`. -/
theorem ni_jackson_lipschitz (f : ℝ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1, |f x - f y| ≤ M * |x - y|)
    {n : ℕ} (hn : 1 ≤ n) :
    ∃ p : ℝ[X], p.natDegree ≤ n ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1, |f x - p.eval x| ≤ ni_jacksonC * M / n := by
  set g : ℝ → ℝ := fun θ => f (cos θ)
  have hcosI : ∀ θ, cos θ ∈ Set.Icc (-1 : ℝ) 1 := fun θ => ⟨neg_one_le_cos θ, cos_le_one θ⟩
  have hglip : ∀ a b, |g a - g b| ≤ M * |a - b| := fun a b =>
    (hf _ (hcosI a) _ (hcosI b)).trans (mul_le_mul_of_nonneg_left (abs_cos_sub_cos_le a b) hM)
  have hgc : Continuous g := by
    have : LipschitzWith (Real.toNNReal M) g := by
      refine LipschitzWith.of_dist_le_mul fun a b => ?_
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hM]
      exact hglip a b
    exact this.continuous
  have hgeven : ∀ s, g (-s) = g s := fun s => by simp [g, cos_neg]
  have hgper : ∀ s, g (s + 2 * π) = g s := fun s => by simp [g, cos_add_two_pi]
  set m := n / 2 + 1
  have hm : 1 ≤ m := by omega
  have hdeg : 2 * (m - 1) ≤ n := by
    have : m - 1 = n / 2 := by omega
    rw [this]; exact Nat.mul_div_le n 2
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnm : (n : ℝ) < 2 * m := by
    have : n < 2 * m := by omega
    exact_mod_cast this
  set Z := ∫ t in -π..π, ni_jackK m t
  have hZ : π * (m : ℝ) ^ 3 / 6 ≤ Z := ni_jackK_mass_ge hm
  have hZpos : 0 < Z := lt_of_lt_of_le (by positivity) hZ
  have hJ := ni_jackK_moment_le hm
  obtain ⟨p₀, hp₀, hconv⟩ := ni_conv_poly m g hgc hgeven hgper
  refine ⟨C (1 / Z) * p₀, (natDegree_C_mul_le _ _).trans (hp₀.trans hdeg), fun x hx => ?_⟩
  set θ := arccos x
  have hxθ : cos θ = x := cos_arccos hx.1 hx.2
  have hfx : f x = g θ := by simp only [g, hxθ]
  rw [eval_mul, eval_C, hfx, ← hxθ, ← hconv θ]
  have hKc := ni_jackK_continuous m
  have hint1 : IntervalIntegrable (fun t => ni_jackK m t * g (θ - t)) MeasureTheory.volume
      (-π) π := (hKc.mul (hgc.comp (continuous_const.sub continuous_id))).intervalIntegrable _ _
  have hint0 : IntervalIntegrable (fun t => ni_jackK m t * g θ) MeasureTheory.volume (-π) π :=
    (hKc.mul continuous_const).intervalIntegrable _ _
  have hdiff : g θ - 1 / Z * ∫ t in -π..π, ni_jackK m t * g (θ - t) =
      1 / Z * ∫ t in -π..π, ni_jackK m t * (g θ - g (θ - t)) := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub hint0 hint1, intervalIntegral.integral_mul_const]
    field_simp
    rfl
  rw [hdiff, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Z)]
  have hpi : -π ≤ π := by linarith [pi_pos]
  have habs : |∫ t in -π..π, ni_jackK m t * (g θ - g (θ - t))| ≤
      M * ∫ t in -π..π, |t| * ni_jackK m t := by
    refine (intervalIntegral.abs_integral_le_integral_abs hpi).trans ?_
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hpi ?_ ?_ fun t _ => ?_
    · exact ((hKc.mul (continuous_const.sub (hgc.comp (continuous_const.sub
        continuous_id)))).abs).intervalIntegrable _ _
    · exact (continuous_const.mul (continuous_abs.mul hKc)).intervalIntegrable _ _
    · rw [abs_mul, abs_of_nonneg (ni_jackK_nonneg m t)]
      have := hglip θ (θ - t)
      rw [sub_sub_cancel] at this
      nlinarith [ni_jackK_nonneg m t]
  have hstep : 1 / Z * |∫ t in -π..π, ni_jackK m t * (g θ - g (θ - t))| ≤
      1 / Z * (M * ((1 + π ^ 4) * (m : ℝ) ^ 2)) :=
    mul_le_mul_of_nonneg_left (habs.trans (mul_le_mul_of_nonneg_left hJ hM)) (by positivity)
  refine hstep.trans ?_
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hZpos hn']
  unfold ni_jacksonC
  have hpi0 := pi_pos
  have key : M * ((1 + π ^ 4) * (m : ℝ) ^ 2) * n * π ≤ 12 * (1 + π ^ 4) * M * Z := by
    have h1 : M * ((1 + π ^ 4) * (m : ℝ) ^ 2) * n * π ≤
        M * ((1 + π ^ 4) * (m : ℝ) ^ 2) * (2 * m) * π := by
      have : 0 ≤ M * ((1 + π ^ 4) * (m : ℝ) ^ 2) := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnm.le this) hpi0.le
    have h2 : M * ((1 + π ^ 4) * (m : ℝ) ^ 2) * (2 * m) * π =
        12 * (1 + π ^ 4) * M * (π * (m : ℝ) ^ 3 / 6) := by ring
    have h3 : 12 * (1 + π ^ 4) * M * (π * (m : ℝ) ^ 3 / 6) ≤ 12 * (1 + π ^ 4) * M * Z :=
      mul_le_mul_of_nonneg_left hZ (by positivity)
    linarith
  calc M * ((1 + π ^ 4) * (m : ℝ) ^ 2) * n = M * ((1 + π ^ 4) * (m : ℝ) ^ 2) * n * π / π := by
        field_simp
    _ ≤ 12 * (1 + π ^ 4) * M * Z / π := by gcongr
    _ = 12 * (1 + π ^ 4) / π * M * Z := by ring

end Miao.NumericalMethods

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Theorem 11.3.1, the Chebyshev Interpolation Theorem (Miao, p. 359)

* `ni_jackson_Ck` (Jackson's theorem for `C^k` functions): there is `Cₖ` such that every `C^k`
  function `f` has, for every `n ≥ k`, a polynomial `p` of degree `≤ n` with
  `‖f − p‖∞ ≤ Cₖ ‖f⁽ᵏ⁾‖∞ / nᵏ` on `[−1, 1]` (by induction on `k` from the Lipschitz case,
  integrating the approximant of `f'`).
* `theorem_11_3_1`: for every `k ≥ 1` there is `dₖ` such that for every `C^k` function `f` and
  every `n ≥ k`,
  `‖f − Iₙf‖∞ ≤ ((2/π) ln(n + 1) + 2) (dₖ/nᵏ) ‖f⁽ᵏ⁾‖∞`, where `Iₙf` is the degree-`n` Chebyshev
  interpolant. Proof: Lebesgue inequality (`ni_lebesgue_inequality`), the logarithmic Lebesgue
  constant (`ni_lebesgueFn_le`) and Jackson's theorem.

Departures from the book (see `theorem_11_3_1_counterexample` for the first):
* the bound holds for `n ≥ k` only, not for all `n`;
* `f` is taken `C^k` on `ℝ` (every `C^k` function on `[−1, 1]` has such an extension; the
  extension theorem is not formalised), and `‖·‖∞` is the sup over `[−1, 1]`;
* `dₖ` depends on `k` only, not on `f` (stronger than printed).
-/

open Polynomial Polynomial.Chebyshev Real

namespace Miao.NumericalMethods

theorem ni_le_supNorm {h : ℝ → ℝ} (hc : Continuous h) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) : |h x| ≤ ni_supNorm h := by
  have hb : BddAbove ((fun x => |h x|) '' Set.Icc (-1) 1) :=
    isCompact_Icc.bddAbove_image (hc.abs.continuousOn)
  exact le_csSup hb ⟨x, hx, rfl⟩

theorem ni_supNorm_nonneg (h : ℝ → ℝ) : 0 ≤ ni_supNorm h := by
  unfold ni_supNorm
  refine Real.sSup_nonneg fun y hy => ?_
  obtain ⟨x, -, rfl⟩ := hy
  exact abs_nonneg _

theorem ni_supNorm_le {h : ℝ → ℝ} {B : ℝ} (hB : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |h x| ≤ B) :
    ni_supNorm h ≤ B := by
  unfold ni_supNorm
  refine csSup_le ⟨|h 0|, 0, ⟨by norm_num, by norm_num⟩, rfl⟩ ?_
  rintro _ ⟨x, hx, rfl⟩
  exact hB x hx

/-- An antiderivative `∑ᵢ qᵢ Xⁱ⁺¹/(i + 1)` of a polynomial `q`. -/
noncomputable def ni_antideriv (q : ℝ[X]) : ℝ[X] :=
  ∑ i ∈ Finset.range (q.natDegree + 1), C (q.coeff i / (i + 1)) * X ^ (i + 1)

theorem ni_antideriv_derivative (q : ℝ[X]) : derivative (ni_antideriv q) = q := by
  unfold ni_antideriv
  rw [derivative_sum]
  conv_rhs => rw [q.as_sum_range_C_mul_X_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [derivative_C_mul_X_pow, Nat.add_sub_cancel]
  congr 1
  push_cast
  field_simp

theorem ni_antideriv_natDegree (q : ℝ[X]) : (ni_antideriv q).natDegree ≤ q.natDegree + 1 := by
  unfold ni_antideriv
  refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_X_pow]
  have := Finset.mem_range.mp hi
  omega

/-- **Jackson's theorem** for `C^k` functions (used in the proof of Theorem 11.3.1, Miao,
p. 359): for `k ≥ 1` there is `Cₖ ≥ 0` such that every `C^k` function `f` has, for each
`n ≥ k`, a polynomial `p` of degree `≤ n` with `|f(x) − p(x)| ≤ Cₖ ‖f⁽ᵏ⁾‖∞ / nᵏ` on
`[−1, 1]`. -/
theorem ni_jackson_Ck (k : ℕ) (hk : 1 ≤ k) :
    ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ f : ℝ → ℝ, ContDiff ℝ k f → ∀ n : ℕ, k ≤ n →
      ∃ p : ℝ[X], p.natDegree ≤ n ∧ ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        |f x - p.eval x| ≤ Ck * ni_supNorm (iteratedDeriv k f) / (n : ℝ) ^ k := by
  induction k, hk using Nat.le_induction with
  | base =>
    refine ⟨ni_jacksonC, ni_jacksonC_pos.le, fun f hf n hn => ?_⟩
    have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
    have hdc : Continuous (deriv f) := by
      have := hf.continuous_iteratedDeriv 1 (by norm_num)
      rwa [iteratedDeriv_one] at this
    have hM : 0 ≤ ni_supNorm (deriv f) := ni_supNorm_nonneg _
    have hlip : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
        |f x - f y| ≤ ni_supNorm (deriv f) * |x - y| := by
      intro x hx y hy
      have := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
        (fun z _ => hd z) (fun z hz => by
          rw [Real.norm_eq_abs]
          exact ni_le_supNorm hdc hz) hy hx
      simpa [Real.norm_eq_abs] using this
    obtain ⟨p, hp, hpx⟩ := ni_jackson_lipschitz f hM hlip hn
    refine ⟨p, hp, fun x hx => ?_⟩
    rw [iteratedDeriv_one, pow_one]
    exact hpx x hx
  | succ k hk ih =>
    obtain ⟨Ck, hCk, hJ⟩ := ih
    refine ⟨ni_jacksonC * Ck * 2 ^ k, by have := ni_jacksonC_pos; positivity,
      fun f hf n hn => ?_⟩
    have hf' : ContDiff ℝ (k + 1 : ℕ) f := hf
    push_cast at hf'
    obtain ⟨hd, -, hg⟩ := contDiff_succ_iff_deriv.mp hf'
    obtain ⟨q, hq, hqx⟩ := hJ (deriv f) hg (n - 1) (by omega)
    have hit : iteratedDeriv k (deriv f) = iteratedDeriv (k + 1) f :=
      (iteratedDeriv_succ' (n := k) (f := f)).symm
    rw [hit] at hqx
    set M := Ck * ni_supNorm (iteratedDeriv (k + 1) f) / ((n - 1 : ℕ) : ℝ) ^ k
    have hn1 : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
      have : 0 < n - 1 := by omega
      exact_mod_cast this
    have hM : 0 ≤ M := by
      have := ni_supNorm_nonneg (iteratedDeriv (k + 1) f)
      positivity
    set Q := ni_antideriv q
    set h : ℝ → ℝ := fun x => f x - Q.eval x
    have hhd : ∀ x, HasDerivAt h (deriv f x - q.eval x) x := by
      intro x
      have := (hd x).hasDerivAt.sub (Polynomial.hasDerivAt Q x)
      rwa [ni_antideriv_derivative] at this
    have hlip : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
        |h x - h y| ≤ M * |x - y| := by
      intro x hx y hy
      have := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
        (fun z _ => (hhd z).differentiableAt) (fun z hz => by
          rw [(hhd z).deriv, Real.norm_eq_abs]
          exact hqx z hz) hy hx
      simpa [Real.norm_eq_abs] using this
    obtain ⟨p₀, hp₀, hp₀x⟩ := ni_jackson_lipschitz h hM hlip (show 1 ≤ n by omega)
    refine ⟨Q + p₀, ?_, fun x hx => ?_⟩
    · refine (natDegree_add_le _ _).trans (max_le ?_ hp₀)
      exact (ni_antideriv_natDegree q).trans (by omega)
    · have e : f x - (Q + p₀).eval x = h x - p₀.eval x := by
        simp only [h, eval_add]; ring
      rw [e]
      refine (hp₀x x hx).trans ?_
      -- `C M / n ≤ C Ck 2ᵏ ‖f⁽ᵏ⁺¹⁾‖ / n^{k+1}`
      have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hhalf : (n : ℝ) / 2 ≤ ((n - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega)]
        have : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
        push_cast
        linarith
      have hpow : ((n : ℝ) / 2) ^ k ≤ ((n - 1 : ℕ) : ℝ) ^ k :=
        pow_le_pow_left₀ (by positivity) hhalf k
      set S := ni_supNorm (iteratedDeriv (k + 1) f)
      have hS : 0 ≤ S := ni_supNorm_nonneg _
      have hC := ni_jacksonC_pos
      simp only [M]
      rw [div_pow] at hpow
      have hA : Ck * S / ((n - 1 : ℕ) : ℝ) ^ k ≤ Ck * S * 2 ^ k / (n : ℝ) ^ k := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h2 : (n : ℝ) ^ k ≤ 2 ^ k * ((n - 1 : ℕ) : ℝ) ^ k := by
          rw [div_le_iff₀ (by positivity)] at hpow
          linarith
        have : 0 ≤ Ck * S := by positivity
        nlinarith
      calc ni_jacksonC * (Ck * S / ((n - 1 : ℕ) : ℝ) ^ k) / n
          ≤ ni_jacksonC * (Ck * S * 2 ^ k / (n : ℝ) ^ k) / n := by gcongr
        _ = ni_jacksonC * Ck * 2 ^ k * S / (n : ℝ) ^ (k + 1) := by
          rw [pow_succ]; field_simp

/-- **Theorem 11.3.1** (Chebyshev Interpolation Theorem, Miao, p. 359; corrected): for every
`k ≥ 1` there is `dₖ` such that for every `C^k` function `f` and every `n ≥ k`,
`‖f − Iₙf‖∞ ≤ ((2/π) ln(n + 1) + 2) (dₖ/nᵏ) ‖f⁽ᵏ⁾‖∞`, where `Iₙf` is the degree-`n` Chebyshev
interpolant and `‖·‖∞` is the uniform norm on `[−1, 1]`. -/
theorem theorem_11_3_1 (k : ℕ) (hk : 1 ≤ k) :
    ∃ d : ℝ, ∀ f : ℝ → ℝ, ContDiff ℝ k f → ∀ n : ℕ, k ≤ n →
      ni_supNorm (fun x => f x - (ni_chebInterp n f).eval x) ≤
        (2 / π * Real.log (n + 1) + 2) * (d / (n : ℝ) ^ k) *
          ni_supNorm (iteratedDeriv k f) := by
  obtain ⟨Ck, hCk, hJ⟩ := ni_jackson_Ck k hk
  refine ⟨2 * π ^ 2 * Ck, fun f hf n hn => ?_⟩
  obtain ⟨p, hp, hpx⟩ := hJ f hf n hn
  set E := Ck * ni_supNorm (iteratedDeriv k f) / (n : ℝ) ^ k
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hE : 0 ≤ E := by
    have := ni_supNorm_nonneg (iteratedDeriv k f)
    positivity
  have hpdeg : p.degree < (n + 1 : ℕ) :=
    (degree_le_natDegree).trans_lt (by exact_mod_cast Nat.lt_succ_of_le hp)
  have hlog : 0 ≤ Real.log (n + 1) := Real.log_nonneg (by linarith)
  refine ni_supNorm_le fun x hx => ?_
  have hnodes : ∀ k' ∈ Finset.Icc 1 (n + 1),
      |f (ni_chebNode (n + 1) k') - p.eval (ni_chebNode (n + 1) k')| ≤ E :=
    fun k' _ => hpx _ ⟨neg_one_le_cos _, cos_le_one _⟩
  have h1 := ni_lebesgue_inequality n f p hpdeg E hnodes x
  have h2 := ni_lebesgueFn_le n hx
  have h3 : |f x - (ni_chebInterp n f).eval x| ≤ (1 + 4 * π * (1 + Real.log (n + 1))) * E := by
    have := hpx x hx
    have hΛ : ni_lebesgueFn n x * E ≤ 4 * π * (1 + Real.log (n + 1)) * E :=
      mul_le_mul_of_nonneg_right h2 hE
    linarith
  have hpi := pi_gt_three
  have hpi0 := pi_pos
  have : 1 + 4 * π * (1 + Real.log (n + 1)) ≤ 2 * π ^ 2 * (2 / π * Real.log (n + 1) + 2) := by
    have e : 2 * π ^ 2 * (2 / π * Real.log (n + 1) + 2) = 4 * π * Real.log (n + 1) + 4 * π ^ 2 := by
      field_simp
      norm_num
    rw [e]
    nlinarith
  calc |f x - (ni_chebInterp n f).eval x| ≤ (1 + 4 * π * (1 + Real.log (n + 1))) * E := h3
    _ ≤ 2 * π ^ 2 * (2 / π * Real.log (n + 1) + 2) * E := mul_le_mul_of_nonneg_right this hE
    _ = (2 / π * Real.log (n + 1) + 2) * (2 * π ^ 2 * Ck / (n : ℝ) ^ k) *
          ni_supNorm (iteratedDeriv k f) := by
        simp only [E]; ring

end Miao.NumericalMethods

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Splines and linear splines (Miao, §11.3.2, pp. 360–361)

A function `φ` on `[a, b]` is a spline of order `k` if it is `C^{k−2}` on `[a, b]` and there are
nodes `a = x₀ < x₁ < ⋯ < xₙ = b` such that `φ` is a polynomial of degree at most `k − 1` on each
`[xᵢ, xᵢ₊₁]`.

* `ni_IsSpline k n x φ` (the definition, Miao, p. 361).
* `ni_spline_two_piecewise_linear`: a spline of order 2 is a continuous piecewise linear
  function.
* `ni_node_interval`: every point of `[x₀, xₙ]` lies in some `[xᵢ, xᵢ₊₁]`.
* `ni_linear_spline_exists`, `ni_linear_spline_unique`: for every data `y₀, …, yₙ` there is a
  linear spline (order 2) interpolating them, and any two agree on `[x₀, xₙ]`.

The book says "a polynomial of order at most `k − 1`"; the intended meaning (as the examples of
order 2 = linear and order 4 = cubic show) is degree at most `k − 1`, which is what is used.
-/

open Polynomial

namespace Miao.NumericalMethods

/-- **Spline of order `k`** (Miao, p. 361): nodes `x₀ < ⋯ < xₙ`, `φ` is `C^{k−2}` on `[x₀, xₙ]`
and a polynomial of degree at most `k − 1` on each `[xᵢ, xᵢ₊₁]`. -/
def ni_IsSpline (k n : ℕ) (x : ℕ → ℝ) (φ : ℝ → ℝ) : Prop :=
  StrictMono x ∧ ContDiffOn ℝ ((k - 2 : ℕ) : WithTop ℕ∞) φ (Set.Icc (x 0) (x n)) ∧
    ∀ i < n, ∃ p : ℝ[X], p.natDegree ≤ k - 1 ∧ ∀ t ∈ Set.Icc (x i) (x (i + 1)), φ t = p.eval t

/-- Miao, p. 361: a spline of order 2 (a linear spline) is a continuous piecewise linear
function. -/
theorem ni_spline_two_piecewise_linear {n : ℕ} {x : ℕ → ℝ} {φ : ℝ → ℝ}
    (h : ni_IsSpline 2 n x φ) :
    ContinuousOn φ (Set.Icc (x 0) (x n)) ∧
      ∀ i < n, ∃ a b : ℝ, ∀ t ∈ Set.Icc (x i) (x (i + 1)), φ t = a + b * t := by
  refine ⟨?_, fun i hi => ?_⟩
  · have := h.2.1
    simpa using this.continuousOn
  · obtain ⟨p, hp, hφ⟩ := h.2.2 i hi
    refine ⟨p.coeff 0, p.coeff 1, fun t ht => ?_⟩
    rw [hφ t ht, eval_eq_sum_range' (n := 2) (by omega)]
    simp [Finset.sum_range_succ]

/-- Every point of `[x₀, xₙ]` (`n ≥ 1`) lies in some subinterval `[xᵢ, xᵢ₊₁]`, `i < n`. -/
theorem ni_node_interval {x : ℕ → ℝ} :
    ∀ n, 0 < n → ∀ t ∈ Set.Icc (x 0) (x n), ∃ i < n, t ∈ Set.Icc (x i) (x (i + 1)) := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro _ t ht
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, by omega, ht⟩
    · by_cases htn : t ≤ x n
      · obtain ⟨i, hi, hti⟩ := ih hn t ⟨ht.1, htn⟩
        exact ⟨i, by omega, hti⟩
      · exact ⟨n, by omega, ⟨(not_le.mp htn).le, ht.2⟩⟩

/-- Two affine functions agreeing at two distinct points agree everywhere. -/
theorem ni_affine_eq {a₁ b₁ a₂ b₂ u v : ℝ} (huv : u ≠ v) (hu : a₁ + b₁ * u = a₂ + b₂ * u)
    (hv : a₁ + b₁ * v = a₂ + b₂ * v) (t : ℝ) : a₁ + b₁ * t = a₂ + b₂ * t := by
  have hb : b₁ = b₂ := by
    have : (b₁ - b₂) * (u - v) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd (sub_eq_zero.mp h) huv
  subst hb
  linarith

/-- Miao, p. 361 (linear spline, uniqueness): two linear splines with the same nodes
interpolating the same data agree on `[x₀, xₙ]`. -/
theorem ni_linear_spline_unique {n : ℕ} (hn : 0 < n) {x : ℕ → ℝ} {φ ψ : ℝ → ℝ}
    (hφ : ni_IsSpline 2 n x φ) (hψ : ni_IsSpline 2 n x ψ) (heq : ∀ i ≤ n, φ (x i) = ψ (x i))
    (t : ℝ) (ht : t ∈ Set.Icc (x 0) (x n)) : φ t = ψ t := by
  obtain ⟨i, hi, hti⟩ := ni_node_interval n hn t ht
  obtain ⟨a₁, b₁, h₁⟩ := (ni_spline_two_piecewise_linear hφ).2 i hi
  obtain ⟨a₂, b₂, h₂⟩ := (ni_spline_two_piecewise_linear hψ).2 i hi
  have hlt : x i < x (i + 1) := hφ.1 (Nat.lt_succ_self i)
  have hu := heq i hi.le
  have hv := heq (i + 1) hi
  rw [h₁ _ ⟨le_rfl, hlt.le⟩, h₂ _ ⟨le_rfl, hlt.le⟩] at hu
  rw [h₁ _ ⟨hlt.le, le_rfl⟩, h₂ _ ⟨hlt.le, le_rfl⟩] at hv
  rw [h₁ t hti, h₂ t hti]
  exact ni_affine_eq hlt.ne hu hv t

/-- The slopes `sᵢ = (yᵢ₊₁ − yᵢ)/(xᵢ₊₁ − xᵢ)`. -/
noncomputable def ni_slope (x y : ℕ → ℝ) (i : ℕ) : ℝ := (y (i + 1) - y i) / (x (i + 1) - x i)

/-- The interpolating linear spline in closed form,
`φ(t) = y₀ + ∑ᵢ sᵢ (max(xᵢ, min(t, xᵢ₊₁)) − xᵢ)`. -/
noncomputable def ni_linSpline (n : ℕ) (x y : ℕ → ℝ) (t : ℝ) : ℝ :=
  y 0 + ∑ i ∈ Finset.range n, ni_slope x y i * (max (x i) (min t (x (i + 1))) - x i)

/-- On `[xⱼ, xⱼ₊₁]` the closed form is `yⱼ + sⱼ (t − xⱼ)`. -/
theorem ni_linSpline_piece {n : ℕ} {x : ℕ → ℝ} (hx : StrictMono x) (y : ℕ → ℝ) {j : ℕ}
    (hj : j < n) {t : ℝ} (ht : t ∈ Set.Icc (x j) (x (j + 1))) :
    ni_linSpline n x y t = y j + ni_slope x y j * (t - x j) := by
  unfold ni_linSpline
  rw [← Finset.sum_range_add_sum_Ico _ hj.le, Finset.sum_eq_sum_Ico_succ_bot hj]
  have hlow : ∀ i ∈ Finset.range j,
      ni_slope x y i * (max (x i) (min t (x (i + 1))) - x i) = y (i + 1) - y i := by
    intro i hi
    have hi' : i + 1 ≤ j := Finset.mem_range.mp hi
    have h1 : x (i + 1) ≤ t := (hx.monotone hi').trans ht.1
    have h2 : x i < x (i + 1) := hx (Nat.lt_succ_self i)
    rw [min_eq_right h1, max_eq_right h2.le, ni_slope]
    field_simp [(sub_pos.mpr h2).ne']
  have hhigh : ∀ i ∈ Finset.Ico (j + 1) n,
      ni_slope x y i * (max (x i) (min t (x (i + 1))) - x i) = 0 := by
    intro i hi
    have hi' : j + 1 ≤ i := (Finset.mem_Ico.mp hi).1
    have h1 : t ≤ x i := ht.2.trans (hx.monotone hi')
    have h2 : min t (x (i + 1)) ≤ x i := (min_le_left _ _).trans h1
    rw [max_eq_left h2, sub_self, mul_zero]
  rw [Finset.sum_congr rfl hlow, Finset.sum_congr rfl hhigh, Finset.sum_const_zero,
    Finset.sum_range_sub (fun i => y i), min_eq_left ht.2, max_eq_right ht.1]
  ring

/-- Miao, p. 361 (linear spline, existence): for strictly increasing nodes and any data there is
a linear spline (order 2) interpolating the data. -/
theorem ni_linear_spline_exists {n : ℕ} (hn : 0 < n) {x : ℕ → ℝ} (hx : StrictMono x)
    (y : ℕ → ℝ) : ni_IsSpline 2 n x (ni_linSpline n x y) ∧
      ∀ i ≤ n, ni_linSpline n x y (x i) = y i := by
  refine ⟨⟨hx, ?_, fun j hj => ?_⟩, fun i hi => ?_⟩
  · have hc : Continuous (ni_linSpline n x y) := by
      unfold ni_linSpline
      fun_prop
    simpa using hc.continuousOn
  · refine ⟨C (ni_slope x y j) * X + C (y j - ni_slope x y j * x j), natDegree_linear_le,
      fun t ht => ?_⟩
    · rw [ni_linSpline_piece hx y hj ht]
      simp
      ring
  · rcases lt_or_eq_of_le hi with hi | rfl
    · rw [ni_linSpline_piece hx y hi ⟨le_rfl, (hx (Nat.lt_succ_self i)).le⟩]
      ring
    · obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
      rw [ni_linSpline_piece hx y (Nat.lt_succ_self m) ⟨(hx (Nat.lt_succ_self m)).le, le_rfl⟩,
        ni_slope]
      field_simp [(sub_pos.mpr (hx (Nat.lt_succ_self m))).ne']
      ring

end Miao.NumericalMethods

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Cubic splines (Miao, §11.3.2, p. 361)

A cubic spline with nodes `x₀ < ⋯ < xₙ` is given by cubic pieces
`φ(x) = aᵢ + bᵢx + cᵢx² + dᵢx³` on `[xᵢ, xᵢ₊₁]` (`q : Fin n → Fin 4 → ℝ` holds the coefficients),
with (i) interpolation `φ(xᵢ) = yᵢ` and continuity, and (iii) continuity of `φ'` and `φ''` at the
interior nodes. These are `4n − 2` conditions for `4n` coefficients (`ni_cubic_condition_count`);
two end conditions are added:

* natural: `φ''(x₀) = φ''(xₙ) = 0`;
* Hermite (clamped): `φ'(x₀) = f'(x₀)`, `φ'(xₙ) = f'(xₙ)`;
* not-a-knot: `φ'''` continuous at `x₁` and at `xₙ₋₁`.

Main results (existence and uniqueness of the cubic spline for every data set):
`ni_natural_spline_existsUnique` (`n ≥ 1`), `ni_clamped_spline_existsUnique` (`n ≥ 1`),
`ni_notAKnot_spline_existsUnique` (`n ≥ 3`), and `ni_notAKnot_not_unique_two` (for `n = 2`
the not-a-knot conditions do not determine the spline). The proofs reduce, by the linear-algebra
lemma `ni_spline_existsUnique_of_homogeneous`, to the homogeneous problem, which is settled by the
second-derivative ("moment") equations `hᵢ₋₁Mᵢ₋₁ + 2(hᵢ₋₁ + hᵢ)Mᵢ + hᵢMᵢ₊₁ = 0` and a maximum
principle (diagonal dominance).

The pieces are recorded by their coefficients, as in the book's (ii); the one-sided limits of (iii)
are the values of the two adjacent pieces at the node.
-/

namespace Miao.NumericalMethods

/-- The cubic piece `q₀ + q₁t + q₂t² + q₃t³`. -/
def ni_cub (q : Fin 4 → ℝ) (t : ℝ) : ℝ := q 0 + q 1 * t + q 2 * t ^ 2 + q 3 * t ^ 3

/-- Its first derivative. -/
def ni_cub1 (q : Fin 4 → ℝ) (t : ℝ) : ℝ := q 1 + 2 * q 2 * t + 3 * q 3 * t ^ 2

/-- Its second derivative. -/
def ni_cub2 (q : Fin 4 → ℝ) (t : ℝ) : ℝ := 2 * q 2 + 6 * q 3 * t

/-- Its third derivative. -/
def ni_cub3 (q : Fin 4 → ℝ) : ℝ := 6 * q 3

theorem ni_hasDerivAt_cub (q : Fin 4 → ℝ) (t : ℝ) :
    HasDerivAt (ni_cub q) (ni_cub1 q t) t := by
  unfold ni_cub ni_cub1
  have h := ((((hasDerivAt_const t (q 0)).add ((hasDerivAt_id t).const_mul (q 1))).add
    ((hasDerivAt_pow 2 t).const_mul (q 2))).add ((hasDerivAt_pow 3 t).const_mul (q 3)))
  convert h using 1
  · funext y
    simp only [Pi.add_apply, id]
  · norm_num
    ring

theorem ni_hasDerivAt_cub1 (q : Fin 4 → ℝ) (t : ℝ) :
    HasDerivAt (ni_cub1 q) (ni_cub2 q t) t := by
  unfold ni_cub1 ni_cub2
  have h := (((hasDerivAt_const t (q 1)).add ((hasDerivAt_id t).const_mul (2 * q 2))).add
    ((hasDerivAt_pow 2 t).const_mul (3 * q 3)))
  convert h using 1
  · funext y
    simp only [Pi.add_apply, id]
  · norm_num
    ring

theorem ni_hasDerivAt_cub2 (q : Fin 4 → ℝ) (t : ℝ) :
    HasDerivAt (ni_cub2 q) (ni_cub3 q) t := by
  unfold ni_cub2 ni_cub3
  have h := (hasDerivAt_const t (2 * q 2)).add ((hasDerivAt_id t).const_mul (6 * q 3))
  convert h using 1
  · funext y
    simp only [Pi.add_apply, id]
  · ring

/-- Miao, p. 361: (i) and (iii) impose `(n + 1) + 3(n − 1) = 4n − 2` conditions on the `4n`
coefficients of (ii). -/
theorem ni_cubic_condition_count (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card (Fin (n + 1) ⊕ Fin (n - 1) × Fin 3) = 4 * n - 2 ∧
      Fintype.card (Fin n × Fin 4) = 4 * n := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  omega

/-- The `i`th piece (zero for `i ≥ n`). -/
def ni_piece {n : ℕ} (q : Fin n → Fin 4 → ℝ) (i : ℕ) : Fin 4 → ℝ :=
  if h : i < n then q ⟨i, h⟩ else 0

/-- (i): interpolation, `φ(xᵢ) = yᵢ` and `φ(xᵢ₊₁) = yᵢ₊₁` on every piece (this includes the
continuity of `φ`). -/
def ni_CubicInterp {n : ℕ} (x y : ℕ → ℝ) (q : Fin n → Fin 4 → ℝ) : Prop :=
  ∀ i < n, ni_cub (ni_piece q i) (x i) = y i ∧ ni_cub (ni_piece q i) (x (i + 1)) = y (i + 1)

/-- (iii): continuity of `φ'` and `φ''` at the interior nodes. -/
def ni_CubicSmooth {n : ℕ} (x : ℕ → ℝ) (q : Fin n → Fin 4 → ℝ) : Prop :=
  ∀ j, 1 ≤ j → j < n →
    ni_cub1 (ni_piece q (j - 1)) (x j) = ni_cub1 (ni_piece q j) (x j) ∧
      ni_cub2 (ni_piece q (j - 1)) (x j) = ni_cub2 (ni_piece q j) (x j)

/-- The left side of the interpolation and smoothness conditions as a linear map. -/
def ni_splineL (n : ℕ) (x : ℕ → ℝ) :
    (Fin n → Fin 4 → ℝ) →ₗ[ℝ] (Fin n → Fin 2 → ℝ) × (Fin (n - 1) → Fin 2 → ℝ) where
  toFun q := (fun i r => ni_cub (q i) (x (i + r)), fun j r =>
    if r = 0 then ni_cub1 (ni_piece q j) (x (j + 1)) - ni_cub1 (ni_piece q (j + 1)) (x (j + 1))
    else ni_cub2 (ni_piece q j) (x (j + 1)) - ni_cub2 (ni_piece q (j + 1)) (x (j + 1)))
  map_add' q q' := by
    ext i r
    · simp only [Pi.add_apply, ni_cub, Prod.fst_add]
      ring
    · simp only [ni_piece, ni_cub1, ni_cub2, Prod.snd_add, Pi.add_apply]
      split_ifs <;> simp <;> ring
  map_smul' c q := by
    ext i r
    · simp only [Pi.smul_apply, ni_cub, smul_eq_mul, Prod.smul_fst, RingHom.id_apply]
      ring
    · simp only [ni_piece, ni_cub1, ni_cub2, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply]
      split_ifs <;> simp <;> ring

/-- The right side for data `y`. -/
def ni_splineTarget (n : ℕ) (y : ℕ → ℝ) :
    (Fin n → Fin 2 → ℝ) × (Fin (n - 1) → Fin 2 → ℝ) :=
  (fun i r => y (i + r), fun _ _ => 0)

theorem ni_splineL_eq_iff {n : ℕ} (x y : ℕ → ℝ) (q : Fin n → Fin 4 → ℝ) :
    ni_splineL n x q = ni_splineTarget n y ↔ ni_CubicInterp x y q ∧ ni_CubicSmooth x q := by
  have hp : ∀ i (h : i < n), ni_piece q i = q ⟨i, h⟩ := fun i h => by simp [ni_piece, h]
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    refine ⟨fun i hi => ?_, fun j hj1 hj2 => ?_⟩
    · have a := congrFun (congrFun h1 ⟨i, hi⟩) 0
      have b := congrFun (congrFun h1 ⟨i, hi⟩) 1
      simp only [ni_splineL, ni_splineTarget, LinearMap.coe_mk, AddHom.coe_mk] at a b
      simp only [Fin.val_zero, add_zero, Fin.val_one] at a b
      rw [hp i hi]
      exact ⟨a, b⟩
    · have a := congrFun (congrFun h2 ⟨j - 1, by omega⟩) 0
      have b := congrFun (congrFun h2 ⟨j - 1, by omega⟩) 1
      simp only [ni_splineL, ni_splineTarget, LinearMap.coe_mk, AddHom.coe_mk] at a b
      have e : j - 1 + 1 = j := by omega
      simp only [ite_true, e, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false] at a b
      exact ⟨sub_eq_zero.mp a, sub_eq_zero.mp b⟩
  · rintro ⟨h1, h2⟩
    refine Prod.ext (funext fun i => funext fun r => ?_) (funext fun j => funext fun r => ?_)
    · simp only [ni_splineL, ni_splineTarget, LinearMap.coe_mk, AddHom.coe_mk]
      have := h1 i i.2
      rw [hp i i.2] at this
      fin_cases r
      · simpa using this.1
      · simpa using this.2
    · simp only [ni_splineL, ni_splineTarget, LinearMap.coe_mk, AddHom.coe_mk]
      have := h2 (j + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at this
      fin_cases r
      · simp [this.1]
      · simp [this.2]

/-- Linear algebra: if the homogeneous problem (zero data, zero end data) has only the zero
solution, then for all data and end data the spline exists and is unique. -/
theorem ni_spline_existsUnique_of_homogeneous {n : ℕ} (hn : 1 ≤ n) (x : ℕ → ℝ)
    (E : (Fin n → Fin 4 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))
    (hhom : ∀ q, ni_CubicInterp x (fun _ => 0) q → ni_CubicSmooth x q → E q = 0 → q = 0)
    (y : ℕ → ℝ) (e : Fin 2 → ℝ) :
    ∃! q : Fin n → Fin 4 → ℝ, ni_CubicInterp x y q ∧ ni_CubicSmooth x q ∧ E q = e := by
  set F := (ni_splineL n x).prod E
  have hF : ∀ q y e, F q = (ni_splineTarget n y, e) ↔
      ni_CubicInterp x y q ∧ ni_CubicSmooth x q ∧ E q = e := by
    intro q y e
    change (ni_splineL n x q, E q) = (ni_splineTarget n y, e) ↔ _
    rw [Prod.mk.injEq, ni_splineL_eq_iff, and_assoc]
  have hzero : ni_splineTarget n (fun _ => 0) = 0 := by
    simp only [ni_splineTarget]
    rfl
  have hinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    have : F q = (ni_splineTarget n (fun _ => 0), 0) := by
      rw [hq, hzero]
      rfl
    obtain ⟨h1, h2, h3⟩ := (hF q _ _).mp this
    exact hhom q h1 h2 h3
  have hdim : Module.finrank ℝ (Fin n → Fin 4 → ℝ) =
      Module.finrank ℝ (((Fin n → Fin 2 → ℝ) × (Fin (n - 1) → Fin 2 → ℝ)) × (Fin 2 → ℝ)) := by
    simp only [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_self,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  have hsurj : Function.Surjective F :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  obtain ⟨q, hq⟩ := hsurj (ni_splineTarget n y, e)
  refine ⟨q, (hF q y e).mp hq, fun q' hq' => hinj ?_⟩
  rw [hq, (hF q' y e).mpr hq']

/-- Two cubic identities (Taylor expansion of a cubic): with `h = v − u`,
`φ(v) − φ(u) = h φ'(u) + h²(2φ''(u) + φ''(v))/6 = h φ'(v) − h²(φ''(u) + 2φ''(v))/6`. -/
theorem ni_cub_taylor (q : Fin 4 → ℝ) (u v : ℝ) :
    ni_cub q v - ni_cub q u =
        (v - u) * ni_cub1 q u + (v - u) ^ 2 * (2 * ni_cub2 q u + ni_cub2 q v) / 6 ∧
      ni_cub q v - ni_cub q u =
        (v - u) * ni_cub1 q v - (v - u) ^ 2 * (ni_cub2 q u + 2 * ni_cub2 q v) / 6 ∧
      ni_cub3 q * (v - u) = ni_cub2 q v - ni_cub2 q u := by
  unfold ni_cub ni_cub1 ni_cub2 ni_cub3
  refine ⟨by ring, by ring, by ring⟩

/-- The moments `Mᵢ = φ''(xᵢ)`, `i = 0, …, n`. -/
def ni_moment {n : ℕ} (x : ℕ → ℝ) (q : Fin n → Fin 4 → ℝ) (i : ℕ) : ℝ :=
  if i < n then ni_cub2 (ni_piece q i) (x i) else ni_cub2 (ni_piece q (n - 1)) (x n)

/-- The moment equations of the homogeneous problem. -/
theorem ni_moment_facts {n : ℕ} {x : ℕ → ℝ} (hx : StrictMono x) {q : Fin n → Fin 4 → ℝ}
    (hI : ni_CubicInterp x (fun _ => 0) q) (hS : ni_CubicSmooth x q) :
    (∀ i < n, ni_cub2 (ni_piece q i) (x (i + 1)) = ni_moment x q (i + 1)) ∧
    (∀ i < n, ni_cub2 (ni_piece q i) (x i) = ni_moment x q i) ∧
    (∀ i < n, 6 * ni_cub1 (ni_piece q i) (x i) =
      -(x (i + 1) - x i) * (2 * ni_moment x q i + ni_moment x q (i + 1))) ∧
    (∀ i < n, 6 * ni_cub1 (ni_piece q i) (x (i + 1)) =
      (x (i + 1) - x i) * (ni_moment x q i + 2 * ni_moment x q (i + 1))) ∧
    (∀ i < n, ni_cub3 (ni_piece q i) * (x (i + 1) - x i) =
      ni_moment x q (i + 1) - ni_moment x q i) ∧
    (∀ j, 1 ≤ j → j < n →
      (x j - x (j - 1)) * ni_moment x q (j - 1) +
        2 * ((x j - x (j - 1)) + (x (j + 1) - x j)) * ni_moment x q j +
          (x (j + 1) - x j) * ni_moment x q (j + 1) = 0) := by
  have hR : ∀ i < n, ni_cub2 (ni_piece q i) (x (i + 1)) = ni_moment x q (i + 1) := by
    intro i hi
    unfold ni_moment
    split_ifs with h
    · have := (hS (i + 1) (by omega) h).2
      simpa using this
    · have : i = n - 1 := by omega
      subst this
      rw [show n - 1 + 1 = n by omega]
  have hL : ∀ i < n, ni_cub2 (ni_piece q i) (x i) = ni_moment x q i := by
    intro i hi
    simp [ni_moment, hi]
  have hD0 : ∀ i < n, 6 * ni_cub1 (ni_piece q i) (x i) =
      -(x (i + 1) - x i) * (2 * ni_moment x q i + ni_moment x q (i + 1)) := by
    intro i hi
    have hh : x (i + 1) - x i ≠ 0 := (sub_pos.mpr (hx (Nat.lt_succ_self i))).ne'
    have t := (ni_cub_taylor (ni_piece q i) (x i) (x (i + 1))).1
    rw [(hI i hi).1, (hI i hi).2, hR i hi, hL i hi, sub_self] at t
    have : (x (i + 1) - x i) * (6 * ni_cub1 (ni_piece q i) (x i) +
        (x (i + 1) - x i) * (2 * ni_moment x q i + ni_moment x q (i + 1))) = 0 := by
      linear_combination (-6) * t
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hh
    · linarith
  have hD1 : ∀ i < n, 6 * ni_cub1 (ni_piece q i) (x (i + 1)) =
      (x (i + 1) - x i) * (ni_moment x q i + 2 * ni_moment x q (i + 1)) := by
    intro i hi
    have hh : x (i + 1) - x i ≠ 0 := (sub_pos.mpr (hx (Nat.lt_succ_self i))).ne'
    have t := (ni_cub_taylor (ni_piece q i) (x i) (x (i + 1))).2.1
    rw [(hI i hi).1, (hI i hi).2, hR i hi, hL i hi, sub_self] at t
    have : (x (i + 1) - x i) * (6 * ni_cub1 (ni_piece q i) (x (i + 1)) -
        (x (i + 1) - x i) * (ni_moment x q i + 2 * ni_moment x q (i + 1))) = 0 := by
      linear_combination (-6) * t
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hh
    · linarith
  refine ⟨hR, hL, hD0, hD1, fun i hi => ?_, fun j hj1 hj2 => ?_⟩
  · rw [(ni_cub_taylor (ni_piece q i) (x i) (x (i + 1))).2.2, hR i hi, hL i hi]
  · have e1 := (hS j hj1 hj2).1
    have a := hD1 (j - 1) (by omega)
    have b := hD0 j hj2
    have e : j - 1 + 1 = j := by omega
    rw [e] at a
    rw [e1] at a
    linear_combination b - a

/-- If all moments vanish (and the data are zero), all pieces vanish. -/
theorem ni_moments_zero {n : ℕ} {x : ℕ → ℝ} (hx : StrictMono x) {q : Fin n → Fin 4 → ℝ}
    (hI : ni_CubicInterp x (fun _ => 0) q) (hS : ni_CubicSmooth x q)
    (hM : ∀ i ≤ n, ni_moment x q i = 0) : q = 0 := by
  obtain ⟨hR, hL, -, -, -, -⟩ := ni_moment_facts hx hI hS
  funext i r
  have hi := i.2
  have hp : ni_piece q i = q i := by simp [ni_piece, hi]
  have h2u := hL i hi
  have h2v := hR i hi
  have h0u := (hI i hi).1
  have h0v := (hI i hi).2
  rw [hp, hM i hi.le] at h2u
  rw [hp, hM (i + 1) hi] at h2v
  rw [hp] at h0u h0v
  have hlt : x i < x (i + 1) := hx (Nat.lt_succ_self _)
  have hne : x (i + 1) - x i ≠ 0 := (sub_pos.mpr hlt).ne'
  unfold ni_cub2 at h2u h2v
  unfold ni_cub at h0u h0v
  have q3 : q i 3 = 0 := by
    have : (x (i + 1) - x i) * (6 * q i 3) = 0 := by linear_combination h2v - h2u
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hne
    · linarith
  have q2 : q i 2 = 0 := by rw [q3] at h2u; linarith
  have q1 : q i 1 = 0 := by
    have : (x (i + 1) - x i) * q i 1 = 0 := by
      rw [q3, q2] at h0u h0v
      linear_combination h0v - h0u
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hne
    · exact h
  have q0 : q i 0 = 0 := by rw [q3, q2, q1] at h0u; linarith
  fin_cases r <;> simp [q0, q1, q2, q3]

/-- Interior maximum principle for the moment equations. -/
theorem ni_moment_interior {M h₁ h₂ m : ℝ} (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) {a b : ℝ}
    (hrow : h₁ * a + 2 * (h₁ + h₂) * m + h₂ * b = 0) (ha : |a| ≤ |m|) (hb : |b| ≤ |m|)
    (hmax : |m| = M) : M = 0 := by
  have h1 : 2 * (h₁ + h₂) * |m| ≤ h₁ * |a| + h₂ * |b| := by
    have e : 2 * (h₁ + h₂) * m = -(h₁ * a + h₂ * b) := by linarith
    calc 2 * (h₁ + h₂) * |m| = |2 * (h₁ + h₂) * m| := by
          rw [abs_mul, abs_of_pos (show (0 : ℝ) < 2 * (h₁ + h₂) by positivity)]
      _ = |h₁ * a + h₂ * b| := by rw [e, abs_neg]
      _ ≤ |h₁ * a| + |h₂ * b| := abs_add_le _ _
      _ = h₁ * |a| + h₂ * |b| := by rw [abs_mul, abs_mul, abs_of_pos hh₁, abs_of_pos hh₂]
  have : (h₁ + h₂) * |m| ≤ 0 := by nlinarith
  have hm : |m| ≤ 0 := by
    by_contra hc
    push Not at hc
    have : 0 < (h₁ + h₂) * |m| := mul_pos (by positivity) hc
    linarith
  rw [← hmax]
  exact le_antisymm hm (abs_nonneg _)

/-- The natural end conditions `φ''(x₀) = φ''(xₙ) = 0` as a linear map. -/
def ni_naturalE (n : ℕ) (x : ℕ → ℝ) : (Fin n → Fin 4 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun q := ![ni_cub2 (ni_piece q 0) (x 0), ni_cub2 (ni_piece q (n - 1)) (x n)]
  map_add' q q' := by
    ext r
    fin_cases r <;> simp [ni_piece, ni_cub2] <;> split_ifs <;> simp <;> ring
  map_smul' c q := by
    ext r
    fin_cases r <;> simp [ni_piece, ni_cub2] <;> split_ifs <;> simp <;> ring

/-- Uniqueness for the homogeneous natural spline. -/
theorem ni_natural_homogeneous {n : ℕ} (hn : 1 ≤ n) {x : ℕ → ℝ} (hx : StrictMono x)
    (q : Fin n → Fin 4 → ℝ) (hI : ni_CubicInterp x (fun _ => 0) q) (hS : ni_CubicSmooth x q)
    (hE : ni_naturalE n x q = 0) : q = 0 := by
  obtain ⟨hR, hL, -, -, -, hrow⟩ := ni_moment_facts hx hI hS
  have hE0 := congrFun hE 0
  have hE1 := congrFun hE 1
  simp only [ni_naturalE, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Pi.zero_apply] at hE0 hE1
  have hM0 : ni_moment x q 0 = 0 := by rw [← hL 0 hn]; exact hE0
  have hMn : ni_moment x q n = 0 := by simp [ni_moment, hE1]
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.range (n + 1))
    (fun i => |ni_moment x q i|) ⟨0, by simp⟩
  have hj' : j ≤ n := by simpa [Nat.lt_succ_iff] using hj
  have hzero : |ni_moment x q j| = 0 := by
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · rw [hM0, abs_zero]
    rcases lt_or_eq_of_le hj' with hjn | rfl
    · exact ni_moment_interior (sub_pos.mpr (hx (by omega)))
        (sub_pos.mpr (hx (Nat.lt_succ_self j))) (hrow j hjpos hjn)
        (hmax (j - 1) (Finset.mem_range.mpr (by omega)))
        (hmax (j + 1) (Finset.mem_range.mpr (by omega))) rfl
    · rw [hMn, abs_zero]
  apply ni_moments_zero hx hI hS
  intro i hi
  have := hmax i (Finset.mem_range.mpr (by omega))
  rw [hzero] at this
  exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))

/-- Miao, p. 361 (natural cubic spline): for strictly increasing nodes `x₀ < ⋯ < xₙ`, `n ≥ 1`, and
any data `y`, there is exactly one cubic spline with `φ(xᵢ) = yᵢ` and `φ''(x₀) = φ''(xₙ) = 0`. -/
theorem ni_natural_spline_existsUnique {n : ℕ} (hn : 1 ≤ n) {x : ℕ → ℝ} (hx : StrictMono x)
    (y : ℕ → ℝ) :
    ∃! q : Fin n → Fin 4 → ℝ, ni_CubicInterp x y q ∧ ni_CubicSmooth x q ∧
      ni_cub2 (ni_piece q 0) (x 0) = 0 ∧ ni_cub2 (ni_piece q (n - 1)) (x n) = 0 := by
  have h := ni_spline_existsUnique_of_homogeneous hn x (ni_naturalE n x)
    (ni_natural_homogeneous hn hx) y 0
  have hiff : ∀ q, ni_naturalE n x q = 0 ↔
      ni_cub2 (ni_piece q 0) (x 0) = 0 ∧ ni_cub2 (ni_piece q (n - 1)) (x n) = 0 := by
    intro q
    constructor
    · intro hq
      have a := congrFun hq 0
      have b := congrFun hq 1
      simp only [ni_naturalE, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Pi.zero_apply] at a b
      exact ⟨a, b⟩
    · rintro ⟨a, b⟩
      ext r
      fin_cases r <;> simp [ni_naturalE, a, b]
  simpa only [hiff] using h

/-- The clamped (Hermite) end conditions `φ'(x₀)`, `φ'(xₙ)` as a linear map. -/
def ni_clampedE (n : ℕ) (x : ℕ → ℝ) : (Fin n → Fin 4 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun q := ![ni_cub1 (ni_piece q 0) (x 0), ni_cub1 (ni_piece q (n - 1)) (x n)]
  map_add' q q' := by
    ext r
    fin_cases r <;> simp [ni_piece, ni_cub1] <;> split_ifs <;> simp <;> ring
  map_smul' c q := by
    ext r
    fin_cases r <;> simp [ni_piece, ni_cub1] <;> split_ifs <;> simp <;> ring

/-- Uniqueness for the homogeneous clamped spline. -/
theorem ni_clamped_homogeneous {n : ℕ} (hn : 1 ≤ n) {x : ℕ → ℝ} (hx : StrictMono x)
    (q : Fin n → Fin 4 → ℝ) (hI : ni_CubicInterp x (fun _ => 0) q) (hS : ni_CubicSmooth x q)
    (hE : ni_clampedE n x q = 0) : q = 0 := by
  obtain ⟨-, -, hD0, hD1, -, hrow⟩ := ni_moment_facts hx hI hS
  have hE0 := congrFun hE 0
  have hE1 := congrFun hE 1
  simp only [ni_clampedE, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Pi.zero_apply] at hE0 hE1
  have h0 : 2 * ni_moment x q 0 + ni_moment x q 1 = 0 := by
    have a := hD0 0 hn
    rw [hE0, mul_zero] at a
    have hh : 0 < x (0 + 1) - x 0 := sub_pos.mpr (hx (Nat.lt_succ_self 0))
    nlinarith
  have hnn : ni_moment x q (n - 1) + 2 * ni_moment x q n = 0 := by
    have a := hD1 (n - 1) (by omega)
    have e : n - 1 + 1 = n := by omega
    rw [e, hE1, mul_zero] at a
    have hh : 0 < x n - x (n - 1) := by
      have := hx (show n - 1 < n by omega)
      linarith
    nlinarith
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.range (n + 1))
    (fun i => |ni_moment x q i|) ⟨0, by simp⟩
  have hj' : j ≤ n := by simpa [Nat.lt_succ_iff] using hj
  have hzero : |ni_moment x q j| = 0 := by
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · have hb := hmax 1 (Finset.mem_range.mpr (by omega))
      have e : |ni_moment x q 1| = 2 * |ni_moment x q 0| := by
        rw [show ni_moment x q 1 = -(2 * ni_moment x q 0) by linarith, abs_neg, abs_mul,
          abs_two]
      linarith [abs_nonneg (ni_moment x q 0)]
    rcases lt_or_eq_of_le hj' with hjn | rfl
    · exact ni_moment_interior (sub_pos.mpr (hx (by omega)))
        (sub_pos.mpr (hx (Nat.lt_succ_self j))) (hrow j hjpos hjn)
        (hmax (j - 1) (Finset.mem_range.mpr (by omega)))
        (hmax (j + 1) (Finset.mem_range.mpr (by omega))) rfl
    · have hb := hmax (j - 1) (Finset.mem_range.mpr (by omega))
      have e : |ni_moment x q (j - 1)| = 2 * |ni_moment x q j| := by
        rw [show ni_moment x q (j - 1) = -(2 * ni_moment x q j) by linarith, abs_neg, abs_mul,
          abs_two]
      linarith [abs_nonneg (ni_moment x q j)]
  apply ni_moments_zero hx hI hS
  intro i hi
  have := hmax i (Finset.mem_range.mpr (by omega))
  rw [hzero] at this
  exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))

/-- Miao, p. 361 (Hermite or clamped cubic spline): for strictly increasing nodes, `n ≥ 1`, any
data `y` and any end slopes `s₀ = f'(x₀)`, `sₙ = f'(xₙ)`, there is exactly one cubic spline with
`φ(xᵢ) = yᵢ`, `φ'(x₀) = s₀` and `φ'(xₙ) = sₙ`. -/
theorem ni_clamped_spline_existsUnique {n : ℕ} (hn : 1 ≤ n) {x : ℕ → ℝ} (hx : StrictMono x)
    (y : ℕ → ℝ) (s₀ sₙ : ℝ) :
    ∃! q : Fin n → Fin 4 → ℝ, ni_CubicInterp x y q ∧ ni_CubicSmooth x q ∧
      ni_cub1 (ni_piece q 0) (x 0) = s₀ ∧ ni_cub1 (ni_piece q (n - 1)) (x n) = sₙ := by
  have h := ni_spline_existsUnique_of_homogeneous hn x (ni_clampedE n x)
    (ni_clamped_homogeneous hn hx) y ![s₀, sₙ]
  have hiff : ∀ q, ni_clampedE n x q = ![s₀, sₙ] ↔
      ni_cub1 (ni_piece q 0) (x 0) = s₀ ∧ ni_cub1 (ni_piece q (n - 1)) (x n) = sₙ := by
    intro q
    constructor
    · intro hq
      have a := congrFun hq 0
      have b := congrFun hq 1
      simp only [ni_clampedE, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
        Matrix.cons_val_one] at a b
      exact ⟨a, b⟩
    · rintro ⟨a, b⟩
      ext r
      fin_cases r <;> simp [ni_clampedE, a, b]
  simpa only [hiff] using h

/-- The not-a-knot end conditions (`φ'''` continuous at `x₁` and `xₙ₋₁`) as a linear map. -/
def ni_notAKnotE (n : ℕ) : (Fin n → Fin 4 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun q := ![ni_cub3 (ni_piece q 0) - ni_cub3 (ni_piece q 1),
    ni_cub3 (ni_piece q (n - 2)) - ni_cub3 (ni_piece q (n - 1))]
  map_add' q q' := by
    ext r
    fin_cases r <;> simp [ni_piece, ni_cub3] <;> split_ifs <;> simp <;> ring
  map_smul' c q := by
    ext r
    fin_cases r <;> simp [ni_piece, ni_cub3] <;> split_ifs <;> simp <;> ring

/-- The first not-a-knot row after eliminating `M₀`:
`(h₀ + 2h₁)M₁ + (h₁ − h₀)M₂ = 0`. -/
theorem ni_notAKnot_row {h₀ h₁ M₀ M₁ M₂ : ℝ} (hh₀ : 0 < h₀) (hh₁ : 0 < h₁)
    (hrow : h₀ * M₀ + 2 * (h₀ + h₁) * M₁ + h₁ * M₂ = 0)
    (hknot : h₁ * (M₁ - M₀) = h₀ * (M₂ - M₁)) :
    (h₀ + 2 * h₁) * M₁ + (h₁ - h₀) * M₂ = 0 := by
  have : (h₀ + h₁) * ((h₀ + 2 * h₁) * M₁ + (h₁ - h₀) * M₂) = 0 := by
    linear_combination h₁ * hrow + h₀ * hknot
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · exact h

/-- Maximum principle at a not-a-knot end row. -/
theorem ni_notAKnot_end {h₀ h₁ M₁ M₂ : ℝ} (hh₀ : 0 < h₀) (hh₁ : 0 < h₁)
    (hrow : (h₀ + 2 * h₁) * M₁ + (h₁ - h₀) * M₂ = 0) (hb : |M₂| ≤ |M₁|) : |M₁| = 0 := by
  have e : (h₀ + 2 * h₁) * |M₁| = |h₁ - h₀| * |M₂| := by
    rw [← abs_of_pos (show 0 < h₀ + 2 * h₁ by linarith), ← abs_mul, ← abs_mul,
      show (h₀ + 2 * h₁) * M₁ = -((h₁ - h₀) * M₂) by linarith, abs_neg]
  have hlt : |h₁ - h₀| < h₀ + 2 * h₁ := by
    rw [abs_lt]; constructor <;> linarith
  have : (h₀ + 2 * h₁ - |h₁ - h₀|) * |M₁| ≤ 0 := by
    nlinarith [abs_nonneg (h₁ - h₀), abs_nonneg M₁]
  have hm : |M₁| ≤ 0 := by
    by_contra hc
    push Not at hc
    have : 0 < (h₀ + 2 * h₁ - |h₁ - h₀|) * |M₁| := mul_pos (by linarith) hc
    linarith
  exact le_antisymm hm (abs_nonneg _)

/-- Uniqueness for the homogeneous not-a-knot spline (`n ≥ 3`). -/
theorem ni_notAKnot_homogeneous {n : ℕ} (hn : 3 ≤ n) {x : ℕ → ℝ} (hx : StrictMono x)
    (q : Fin n → Fin 4 → ℝ) (hI : ni_CubicInterp x (fun _ => 0) q) (hS : ni_CubicSmooth x q)
    (hE : ni_notAKnotE n q = 0) : q = 0 := by
  obtain ⟨-, -, -, -, hT, hrow⟩ := ni_moment_facts hx hI hS
  have hE0 := congrFun hE 0
  have hE1 := congrFun hE 1
  simp only [ni_notAKnotE, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Pi.zero_apply] at hE0 hE1
  set M := ni_moment x q
  have hpos : ∀ i, 0 < x (i + 1) - x i := fun i => sub_pos.mpr (hx (Nat.lt_succ_self i))
  -- the knot relations
  have hk0 : (x 2 - x 1) * (M 1 - M 0) = (x 1 - x 0) * (M 2 - M 1) := by
    have a := hT 0 (by omega)
    have b := hT 1 (by omega)
    have e : ni_cub3 (ni_piece q 0) = ni_cub3 (ni_piece q 1) := by linarith
    rw [e] at a
    linear_combination (x 1 - x 0) * b - (x 2 - x 1) * a
  have hkn : (x n - x (n - 1)) * (M (n - 1) - M (n - 2)) =
      (x (n - 1) - x (n - 2)) * (M n - M (n - 1)) := by
    have a := hT (n - 2) (by omega)
    have b := hT (n - 1) (by omega)
    have e1 : n - 2 + 1 = n - 1 := by omega
    have e2 : n - 1 + 1 = n := by omega
    rw [e1] at a
    rw [e2] at b
    have e : ni_cub3 (ni_piece q (n - 2)) = ni_cub3 (ni_piece q (n - 1)) := by linarith
    rw [e] at a
    linear_combination (x (n - 1) - x (n - 2)) * b - (x n - x (n - 1)) * a
  -- the two end rows
  have hr1 : ((x 1 - x 0) + 2 * (x 2 - x 1)) * M 1 + ((x 2 - x 1) - (x 1 - x 0)) * M 2 = 0 := by
    have r := hrow 1 le_rfl (by omega)
    simp only [Nat.sub_self] at r
    exact ni_notAKnot_row (hpos 0) (hpos 1) r hk0
  have hrn : ((x n - x (n - 1)) + 2 * (x (n - 1) - x (n - 2))) * M (n - 1) +
      ((x (n - 1) - x (n - 2)) - (x n - x (n - 1))) * M (n - 2) = 0 := by
    have r := hrow (n - 1) (by omega) (by omega)
    have e1 : n - 1 - 1 = n - 2 := by omega
    have e2 : n - 1 + 1 = n := by omega
    rw [e1, e2] at r
    have hp1 : 0 < x n - x (n - 1) := by have := hpos (n - 1); rwa [e2] at this
    have hp2 : 0 < x (n - 1) - x (n - 2) := by
      have := hpos (n - 2); rwa [show n - 2 + 1 = n - 1 by omega] at this
    exact ni_notAKnot_row (M₀ := M n) (M₁ := M (n - 1)) (M₂ := M (n - 2)) hp1 hp2
      (by linear_combination r) (by linear_combination hkn)
  -- maximum principle on `1, …, n − 1`
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.Icc 1 (n - 1))
    (fun i => |M i|) ⟨1, by simp; omega⟩
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
  have hzero : |M j| = 0 := by
    rcases eq_or_ne j 1 with rfl | hne1
    · exact ni_notAKnot_end (hpos 0) (hpos 1) hr1 (hmax 2 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
    rcases eq_or_ne j (n - 1) with rfl | hne2
    · have hp1 : 0 < x n - x (n - 1) := by
        have := hpos (n - 1); rwa [show n - 1 + 1 = n by omega] at this
      have hp2 : 0 < x (n - 1) - x (n - 2) := by
        have := hpos (n - 2); rwa [show n - 2 + 1 = n - 1 by omega] at this
      exact ni_notAKnot_end hp1 hp2 hrn (hmax (n - 2) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
    · exact ni_moment_interior (sub_pos.mpr (hx (by omega)))
        (sub_pos.mpr (hx (Nat.lt_succ_self j))) (hrow j hj1 (by omega))
        (hmax (j - 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
        (hmax (j + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)) rfl
  have hin : ∀ i, 1 ≤ i → i ≤ n - 1 → M i = 0 := by
    intro i hi1 hi2
    have := hmax i (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    rw [hzero] at this
    exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
  apply ni_moments_zero hx hI hS
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · rw [hin 1 le_rfl (by omega), hin 2 (by omega) (by omega)] at hk0
    have := hpos 1
    nlinarith
  rcases lt_or_eq_of_le hi with hin' | rfl
  · exact hin i hipos (by omega)
  · rw [hin (i - 1) (by omega) le_rfl, hin (i - 2) (by omega) (by omega)] at hkn
    have := hpos (i - 2)
    rw [show i - 2 + 1 = i - 1 by omega] at this
    nlinarith

/-- Miao, p. 361 (not-a-knot cubic spline): for strictly increasing nodes, `n ≥ 3`, and any data
`y`, there is exactly one cubic spline with `φ(xᵢ) = yᵢ` and `φ'''` continuous at `x₁` and
`xₙ₋₁`. -/
theorem ni_notAKnot_spline_existsUnique {n : ℕ} (hn : 3 ≤ n) {x : ℕ → ℝ} (hx : StrictMono x)
    (y : ℕ → ℝ) :
    ∃! q : Fin n → Fin 4 → ℝ, ni_CubicInterp x y q ∧ ni_CubicSmooth x q ∧
      ni_cub3 (ni_piece q 0) = ni_cub3 (ni_piece q 1) ∧
        ni_cub3 (ni_piece q (n - 2)) = ni_cub3 (ni_piece q (n - 1)) := by
  have h := ni_spline_existsUnique_of_homogeneous (by omega) x (ni_notAKnotE n)
    (ni_notAKnot_homogeneous hn hx) y 0
  have hiff : ∀ q, ni_notAKnotE n q = 0 ↔
      ni_cub3 (ni_piece q 0) = ni_cub3 (ni_piece q 1) ∧
        ni_cub3 (ni_piece q (n - 2)) = ni_cub3 (ni_piece q (n - 1)) := by
    intro q
    constructor
    · intro hq
      have a := congrFun hq 0
      have b := congrFun hq 1
      simp only [ni_notAKnotE, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Pi.zero_apply] at a b
      exact ⟨sub_eq_zero.mp a, sub_eq_zero.mp b⟩
    · rintro ⟨a, b⟩
      ext r
      fin_cases r <;> simp [ni_notAKnotE, a, b]
  simpa only [hiff] using h

/-- Miao, p. 361 (correction): with only two pieces (`n = 2`, nodes `0, 1, 2`) the not-a-knot
conditions do not determine the cubic spline: both pieces equal to `t(t − 1)(t − 2)` and both
equal to `0` interpolate the zero data. -/
theorem ni_notAKnot_not_unique_two :
    ¬ ∃! q : Fin 2 → Fin 4 → ℝ, ni_CubicInterp (fun i => (i : ℝ)) (fun _ => 0) q ∧
      ni_CubicSmooth (fun i => (i : ℝ)) q ∧
      ni_cub3 (ni_piece q 0) = ni_cub3 (ni_piece q 1) ∧
        ni_cub3 (ni_piece q (2 - 2)) = ni_cub3 (ni_piece q (2 - 1)) := by
  rintro ⟨q₀, -, huniq⟩
  set c : Fin 4 → ℝ := ![0, 2, -3, 1]
  set q : Fin 2 → Fin 4 → ℝ := fun _ => c
  have hpq : ∀ i < 2, ni_piece q i = c := fun i hi => by simp [ni_piece, hi, q]
  have h0 : ∀ i, ni_piece (0 : Fin 2 → Fin 4 → ℝ) i = 0 := fun i => by
    simp only [ni_piece]
    split_ifs <;> rfl
  have goodq : ni_CubicInterp (fun i => (i : ℝ)) (fun _ => 0) q ∧
      ni_CubicSmooth (fun i => (i : ℝ)) q ∧
      ni_cub3 (ni_piece q 0) = ni_cub3 (ni_piece q 1) ∧
        ni_cub3 (ni_piece q (2 - 2)) = ni_cub3 (ni_piece q (2 - 1)) := by
    refine ⟨fun i hi => ?_, fun j hj1 hj2 => ?_, ?_, ?_⟩
    · rw [hpq i hi]
      interval_cases i <;> simp [ni_cub, c] <;> norm_num
    · rw [hpq j hj2, hpq (j - 1) (by omega)]
      exact ⟨rfl, rfl⟩
    · rw [hpq 0 (by norm_num), hpq 1 (by norm_num)]
    · rw [hpq 0 (by norm_num), hpq 1 (by norm_num)]
  have good0 : ni_CubicInterp (fun i => (i : ℝ)) (fun _ => 0) (0 : Fin 2 → Fin 4 → ℝ) ∧
      ni_CubicSmooth (fun i => (i : ℝ)) (0 : Fin 2 → Fin 4 → ℝ) ∧
      ni_cub3 (ni_piece (0 : Fin 2 → Fin 4 → ℝ) 0) =
        ni_cub3 (ni_piece (0 : Fin 2 → Fin 4 → ℝ) 1) ∧
        ni_cub3 (ni_piece (0 : Fin 2 → Fin 4 → ℝ) (2 - 2)) =
          ni_cub3 (ni_piece (0 : Fin 2 → Fin 4 → ℝ) (2 - 1)) := by
    refine ⟨fun i _ => ?_, fun j _ _ => ?_, ?_, ?_⟩ <;>
      simp [h0, ni_cub, ni_cub1, ni_cub2, ni_cub3]
  have h1 := huniq q goodq
  have h2 := huniq 0 good0
  have : q = 0 := h1.trans h2.symm
  have := congrFun (congrFun this 0) 3
  simp [q, c] at this

end Miao.NumericalMethods

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Multidimensional approximation: tensor products (Miao, §11.3.3, pp. 364–366)

On `I = ∏ᵢ [aᵢ, bᵢ]` with univariate bases `φᵢⱼ` and nodes `xᵢⱼ` (`j = 1, …, nᵢ`), the tensor basis
is `φ_{j₁⋯j_d}(x) = ∏ᵢ φᵢⱼᵢ(xᵢ)`; evaluated on the tensor grid of nodes its interpolation matrix is
the tensor (Kronecker) product `Φ = Φ_d ⊗ ⋯ ⊗ Φ₁` of the univariate matrices.

* `ni_tensorMatrix Φ`: the `d`-fold tensor product, indexed by multi-indices;
  `ni_tensor_interpMatrix`: it is the interpolation matrix of the tensor basis on the tensor grid.
* `ni_tensorMatrix_mul`, `ni_tensorMatrix_one`: `(⊗Aᵢ)(⊗Bᵢ) = ⊗(AᵢBᵢ)`, `⊗1 = 1`.
* `ni_tensor_inverse`, `ni_tensor_coeff`: if every `Φᵢ` is invertible then
  `Φ⁻¹ = ⊗Φᵢ⁻¹` and `c = (Φ_d⁻¹ ⊗ ⋯ ⊗ Φ₁⁻¹) y` is the unique solution of `Φc = y`.
* `ni_tensor_card`: the tensor grid has `n = ∏ᵢ nᵢ` points, so `mᵈ` when every `nᵢ = m` (the
  curse of dimensionality).
* `ni_tensor_example_*`: the Miranda–Fackler example (`n₁ = 3`, `n₂ = 2`, monomial bases,
  nodes `{0, 1, 2}` and `{0, 1}`): the basis vector, the stacked nodes `X` and the `6 × 6`
  matrix `Φ = Φ₂ ⊗ Φ₁`.

Complete polynomial bases are only recommended by reference to Judd (1998) and are not
formalised; Smolyak grids are not discussed in the book.
-/

open Matrix

namespace Miao.NumericalMethods

/-- The tensor product `⊗ᵢ Φᵢ` of square matrices, indexed by multi-indices:
`(⊗Φᵢ)_{r c} = ∏ᵢ (Φᵢ)_{rᵢ cᵢ}`. -/
def ni_tensorMatrix {d : ℕ} {m : Fin d → ℕ} (Φ : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℝ) :
    Matrix (∀ i, Fin (m i)) (∀ i, Fin (m i)) ℝ :=
  Matrix.of fun r c => ∏ i, Φ i (r i) (c i)

/-- The tensor basis `φ_{j₁⋯j_d}(x₁, …, x_d) = ∏ᵢ φᵢⱼᵢ(xᵢ)` (Miao, p. 364). -/
def ni_tensorBasis {d : ℕ} {m : Fin d → ℕ} (φ : ∀ i, Fin (m i) → ℝ → ℝ) (j : ∀ i, Fin (m i))
    (x : Fin d → ℝ) : ℝ :=
  ∏ i, φ i (j i) (x i)

/-- Miao, p. 365: evaluated on the tensor grid of nodes `(x₁ᵣ₁, …, x_dᵣ_d)`, the interpolation
matrix of the tensor basis is the tensor product of the univariate interpolation matrices
`Φᵢ = [φᵢⱼ(xᵢₖ)]`. -/
theorem ni_tensor_interpMatrix {d : ℕ} {m : Fin d → ℕ} (φ : ∀ i, Fin (m i) → ℝ → ℝ)
    (x : ∀ i, Fin (m i) → ℝ) (r c : ∀ i, Fin (m i)) :
    ni_tensorBasis φ c (fun i => x i (r i)) =
      ni_tensorMatrix (fun i => ni_interpMatrix (φ i) (x i)) r c := by
  simp [ni_tensorBasis, ni_tensorMatrix, ni_interpMatrix]

/-- `(⊗Aᵢ)(⊗Bᵢ) = ⊗(AᵢBᵢ)` (mixed-product property). -/
theorem ni_tensorMatrix_mul {d : ℕ} {m : Fin d → ℕ}
    (A B : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℝ) :
    ni_tensorMatrix A * ni_tensorMatrix B = ni_tensorMatrix (fun i => A i * B i) := by
  ext r c
  simp only [ni_tensorMatrix, mul_apply, of_apply]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ, Finset.prod_mul_distrib]

/-- `⊗1 = 1`. -/
theorem ni_tensorMatrix_one {d : ℕ} {m : Fin d → ℕ} :
    ni_tensorMatrix (fun i => (1 : Matrix (Fin (m i)) (Fin (m i)) ℝ)) = 1 := by
  ext r c
  simp only [ni_tensorMatrix, of_apply, one_apply]
  by_cases h : r = c
  · subst h
    simp
  · simp only [h, ↓reduceIte]
    obtain ⟨i, hi⟩ : ∃ i, r i ≠ c i := by
      by_contra hc
      push Not at hc
      exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- Miao, p. 365: if every `Φᵢ` is invertible then `Φ = ⊗Φᵢ` is invertible with
`Φ⁻¹ = Φ_d⁻¹ ⊗ ⋯ ⊗ Φ₁⁻¹`. -/
theorem ni_tensor_inverse {d : ℕ} {m : Fin d → ℕ} (Φ : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℝ)
    (h : ∀ i, IsUnit (Φ i).det) :
    (ni_tensorMatrix Φ)⁻¹ = ni_tensorMatrix (fun i => (Φ i)⁻¹) ∧
      ni_tensorMatrix Φ * ni_tensorMatrix (fun i => (Φ i)⁻¹) = 1 := by
  have h1 : ni_tensorMatrix (fun i => (Φ i)⁻¹) * ni_tensorMatrix Φ = 1 := by
    rw [ni_tensorMatrix_mul]
    simp_rw [Matrix.nonsing_inv_mul _ (h _)]
    exact ni_tensorMatrix_one
  have h2 : ni_tensorMatrix Φ * ni_tensorMatrix (fun i => (Φ i)⁻¹) = 1 := by
    rw [ni_tensorMatrix_mul]
    simp_rw [Matrix.mul_nonsing_inv _ (h _)]
    exact ni_tensorMatrix_one
  exact ⟨Matrix.inv_eq_left_inv h1, h2⟩

/-- Miao, p. 365: if every `Φᵢ` is invertible, `c = (Φ_d⁻¹ ⊗ ⋯ ⊗ Φ₁⁻¹) y` is the unique solution
of the interpolation equation `Φc = y`. -/
theorem ni_tensor_coeff {d : ℕ} {m : Fin d → ℕ} (Φ : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℝ)
    (h : ∀ i, IsUnit (Φ i).det) (y : (∀ i, Fin (m i)) → ℝ) :
    ∃! c, ni_tensorMatrix Φ *ᵥ c = y ∧ c = ni_tensorMatrix (fun i => (Φ i)⁻¹) *ᵥ y := by
  obtain ⟨-, hmul⟩ := ni_tensor_inverse Φ h
  refine ⟨ni_tensorMatrix (fun i => (Φ i)⁻¹) *ᵥ y, ⟨?_, rfl⟩, fun c hc => hc.2⟩
  rw [mulVec_mulVec, hmul, one_mulVec]

/-- Miao, p. 364: the tensor grid has `n = ∏ᵢ nᵢ` points; with `nᵢ = m` for all `i` this is
`mᵈ`, which grows exponentially in the dimension (the curse of dimensionality, p. 366). -/
theorem ni_tensor_card {d : ℕ} (m : Fin d → ℕ) :
    Fintype.card (∀ i, Fin (m i)) = ∏ i, m i ∧
      ∀ M : ℕ, (∀ i, m i = M) → Fintype.card (∀ i, Fin (m i)) = M ^ d := by
  refine ⟨by simp, fun M hM => ?_⟩
  simp [hM]

/-- Miao, p. 365: the univariate monomial basis matrix on the nodes `{0, 1, 2}`. -/
theorem ni_tensor_example_Φ₁ :
    ni_interpMatrix (ni_monomial (n := 3)) ![0, 1, 2] = !![1, 0, 0; 1, 1, 1; 1, 2, 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [ni_interpMatrix, ni_monomial]

/-- Miao, p. 366: the univariate monomial basis matrix on the nodes `{0, 1}`. -/
theorem ni_tensor_example_Φ₂ :
    ni_interpMatrix (ni_monomial (n := 2)) ![0, 1] = !![1, 0; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ni_interpMatrix, ni_monomial]

/-- Miao, p. 365: the full basis `[1 x₂] ⊗ [1 x₁ x₁²] = [1 x₁ x₁² x₂ x₁x₂ x₁²x₂]`. -/
theorem ni_tensor_example_basis (x₁ x₂ : ℝ) :
    (fun r : Fin 6 => (fun ab : Fin 2 × Fin 3 => ![1, x₂] ab.1 * ![1, x₁, x₁ ^ 2] ab.2)
      (finProdFinEquiv.symm r)) = ![1, x₁, x₁ ^ 2, x₂, x₁ * x₂, x₁ ^ 2 * x₂] := by
  funext r
  fin_cases r <;> simp [finProdFinEquiv, Fin.divNat, Fin.modNat] <;> ring

/-- Miao, p. 366: the stacked nodes `X` (row `r` is the grid point `zᵣ = (x₁, x₂)`). -/
theorem ni_tensor_example_X :
    (Matrix.of fun (r : Fin 6) (c : Fin 2) =>
      ![![(0 : ℝ), 1, 2] ((finProdFinEquiv (m := 2) (n := 3)).symm r).2,
        ![(0 : ℝ), 1] ((finProdFinEquiv (m := 2) (n := 3)).symm r).1] c)
      = !![0, 0; 1, 0; 2, 0; 0, 1; 1, 1; 2, 1] := by
  ext r c
  fin_cases r <;> fin_cases c <;> simp [finProdFinEquiv, Fin.divNat, Fin.modNat]

/-- Miao, p. 366: `Φ = Φ₂ ⊗ Φ₁` is the displayed `6 × 6` matrix. -/
theorem ni_tensor_example_Φ :
    (kroneckerMap (· * ·) (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)
        (!![1, 0, 0; 1, 1, 1; 1, 2, 4] : Matrix (Fin 3) (Fin 3) ℝ)).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm =
      !![1, 0, 0, 0, 0, 0;
         1, 1, 1, 0, 0, 0;
         1, 2, 4, 0, 0, 0;
         1, 0, 0, 1, 0, 0;
         1, 1, 1, 1, 1, 1;
         1, 2, 4, 1, 2, 4] := by
  ext r c
  fin_cases r <;> fin_cases c <;> simp [finProdFinEquiv, kroneckerMap, Fin.divNat, Fin.modNat]

/-- Miao, p. 366: the example's interpolation matrix is invertible, so the coefficients are
`c = (Φ₂⁻¹ ⊗ Φ₁⁻¹) y`. -/
theorem ni_tensor_example_invertible :
    IsUnit (!![1, 0, 0; 1, 1, 1; 1, 2, 4] : Matrix (Fin 3) (Fin 3) ℝ).det ∧
      IsUnit (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ).det := by
  refine ⟨?_, ?_⟩ <;> rw [isUnit_iff_ne_zero] <;> norm_num [det_fin_three, det_fin_two]

end Miao.NumericalMethods

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 11.1 (Miao, p. 383)

The exercise asks for the CompEcon toolbox to construct the 5- and 20-degree approximants of
`f(x) = |x|^{0.6}` and `f(x) = (1 + 2x²)^{−1}` on `[−1, 1]` by (a) monomial interpolation on a
uniform grid, (b) Chebyshev interpolation at the Chebyshev nodes, (c) linear splines and (d) cubic
splines on uniform nodes, and to plot the approximation errors. The computation and the plots are
not formalised. The mathematical facts behind the exercise are:

* `ex_11_1_f1_not_differentiable`, `ex_11_1_f1_continuous`: `|x|^{0.6}` is continuous but not
  differentiable at `0`, so Theorem 11.3.1 (which needs `k ≥ 1` derivatives) does not apply to it;
* `ex_11_1_f2_smooth`: `(1 + 2x²)^{−1}` is `C^∞`;
* `ex_11_1`: for every `N ≥ 3` (in particular the degrees `5` and `20` of the exercise) and every
  `f`, the four approximants are well defined: (a) the monomial interpolant on the uniform grid
  `xᵢ = −1 + 2i/N` exists and is unique; (b) the Chebyshev interpolant interpolates `f` at the
  Chebyshev nodes; (c) the linear spline on the uniform nodes exists and is unique on `[−1, 1]`;
  (d) the cubic spline with the not-a-knot end condition (CompEcon's default) exists and is unique.
-/

open Polynomial Real

namespace Miao.NumericalMethods

/-- **Exercise 11.1** (Miao, p. 383): `|x|^{0.6}` is not differentiable at `0`. -/
theorem ex_11_1_f1_not_differentiable :
    ¬ DifferentiableAt ℝ (fun x : ℝ => |x| ^ (0.6 : ℝ)) 0 := by
  intro h
  set y := deriv (fun x : ℝ => |x| ^ (0.6 : ℝ)) 0
  have ht : Filter.Tendsto (fun t : ℝ => t ^ ((0.6 : ℝ) - 1)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds y) := by
    apply tendsto_nhdsWithin_congr _ h.hasDerivAt.tendsto_slope_zero_right
    intro x (hx : 0 < x)
    simp only [zero_add, abs_zero, smul_eq_mul, abs_of_pos hx]
    rw [Real.zero_rpow (by norm_num), sub_zero]
    field_simp
    nth_rw 1 [← add_sub_cancel 1 (0.6 : ℝ), Real.rpow_add hx]
    simp
  exact not_tendsto_nhds_of_tendsto_atTop (tendsto_rpow_neg_nhdsGT_zero (by norm_num)) y ht

/-- **Exercise 11.1** (Miao, p. 383): `|x|^{0.6}` is continuous. -/
theorem ex_11_1_f1_continuous : Continuous (fun x : ℝ => |x| ^ (0.6 : ℝ)) :=
  continuous_abs.rpow_const fun _ => Or.inr (by norm_num)

/-- **Exercise 11.1** (Miao, p. 383): `(1 + 2x²)^{−1}` is `C^∞`. -/
theorem ex_11_1_f2_smooth : ContDiff ℝ ⊤ (fun x : ℝ => (1 + 2 * x ^ 2)⁻¹) :=
  ContDiff.inv (by fun_prop) fun x => by positivity

/-- The uniform grid `xᵢ = −1 + 2i/N` on `[−1, 1]`. -/
noncomputable def ni_uniformGrid (N : ℕ) (i : ℕ) : ℝ := -1 + 2 * i / N

theorem ni_uniformGrid_strictMono {N : ℕ} (hN : 0 < N) : StrictMono (ni_uniformGrid N) := by
  intro a b hab
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have : (a : ℝ) < b := by exact_mod_cast hab
  unfold ni_uniformGrid
  have : 2 * (a : ℝ) / N < 2 * b / N := by
    apply div_lt_div_of_pos_right _ hN'
    linarith
  linarith

theorem ni_uniformGrid_ends {N : ℕ} (hN : 0 < N) :
    ni_uniformGrid N 0 = -1 ∧ ni_uniformGrid N N = 1 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨by simp [ni_uniformGrid], ?_⟩
  unfold ni_uniformGrid
  field_simp
  ring

/-- **Exercise 11.1** (Miao, p. 383): for `N ≥ 3` (the exercise uses `N = 5` and `N = 20`) and any
`f`, (a) the monomial interpolant on the uniform grid exists uniquely, (b) the Chebyshev
interpolant matches `f` at the Chebyshev nodes, (c) the linear spline on the uniform nodes exists
and is unique on `[−1, 1]`, and (d) the not-a-knot cubic spline on the uniform nodes exists
uniquely. -/
theorem ex_11_1 (N : ℕ) (hN : 3 ≤ N) (f : ℝ → ℝ) :
    (∃! c : Fin (N + 1) → ℝ, ∀ i : Fin (N + 1),
        ni_fhat ni_monomial c (ni_uniformGrid N i) = f (ni_uniformGrid N i)) ∧
    (∀ k ∈ Finset.Icc 1 (N + 1),
        (ni_chebInterp N f).eval (ni_chebNode (N + 1) k) = f (ni_chebNode (N + 1) k)) ∧
    (ni_IsSpline 2 N (ni_uniformGrid N) (ni_linSpline N (ni_uniformGrid N)
        (fun i => f (ni_uniformGrid N i))) ∧
      (∀ i ≤ N, ni_linSpline N (ni_uniformGrid N) (fun i => f (ni_uniformGrid N i))
        (ni_uniformGrid N i) = f (ni_uniformGrid N i)) ∧
      ∀ φ, ni_IsSpline 2 N (ni_uniformGrid N) φ →
        (∀ i ≤ N, φ (ni_uniformGrid N i) = f (ni_uniformGrid N i)) →
        ∀ t ∈ Set.Icc (-1 : ℝ) 1,
          φ t = ni_linSpline N (ni_uniformGrid N) (fun i => f (ni_uniformGrid N i)) t) ∧
    (∃! q : Fin N → Fin 4 → ℝ,
        ni_CubicInterp (ni_uniformGrid N) (fun i => f (ni_uniformGrid N i)) q ∧
        ni_CubicSmooth (ni_uniformGrid N) q ∧
        ni_cub3 (ni_piece q 0) = ni_cub3 (ni_piece q 1) ∧
          ni_cub3 (ni_piece q (N - 2)) = ni_cub3 (ni_piece q (N - 1))) := by
  have hN0 : 0 < N := by omega
  have hmono := ni_uniformGrid_strictMono hN0
  obtain ⟨hlo, hhi⟩ := ni_uniformGrid_ends hN0
  have hlin := ni_linear_spline_exists hN0 hmono (fun i => f (ni_uniformGrid N i))
  refine ⟨?_, (ni_chebInterp_spec N f).2, ⟨hlin.1, hlin.2, fun φ hφ hφi t ht => ?_⟩,
    ni_notAKnot_spline_existsUnique hN hmono _⟩
  · refine ni_monomial_interp_existsUnique _ ?_ _
    intro a b hab
    exact Fin.ext (by exact_mod_cast hmono.injective hab)
  · refine ni_linear_spline_unique hN0 hφ hlin.1 (fun i hi => ?_) t ?_
    · rw [hφi i hi, hlin.2 i hi]
    · rwa [hlo, hhi]

end Miao.NumericalMethods

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Interpolation at uniformly spaced nodes need not converge (Miao, p. 360)

Miao, p. 360: "interpolation at uniformly spaced nodes does not necessarily converge as we use
more points". We prove it (`ni_uniform_interp_not_convergent`): there is a continuous `f` on
`[−1, 1]` whose polynomial interpolants at the uniform nodes `xₖ = −1 + 2k/N`, `k = 0, …, N`, do
not converge to `f` uniformly.

* `ni_uniform_basis_lower`: at `x* = −1 + 1/N`, `|ℓₖ(x*)| ≥ C(N, k)/(4N²)`, so the Lebesgue
  function satisfies `∑ₖ |ℓₖ(x*)| ≥ 2^N/(4N²)` (`ni_uniform_lebesgue_lower`).
* `ni_uniformInterp N`: the interpolation operator on `C([−1, 1])` as a continuous linear map,
  with `‖ni_uniformInterp N‖ ≥ 2^N/(4N²)` (`ni_uniformInterp_norm_ge`), using a piecewise
  linear test function.
* The uniform boundedness principle (`banach_steinhaus`) then gives the divergent `f`.
-/

open Polynomial Filter Topology

namespace Miao.NumericalMethods

/-- `∏_{j=0}^{N} |2j − 1| ≥ 2^N N!/(2N)` for `N ≥ 1`. -/
theorem ni_prod_odd_ge (N : ℕ) (hN : 1 ≤ N) :
    (2 : ℝ) ^ N * N.factorial / (2 * N) ≤ ∏ j ∈ Finset.range (N + 1), |2 * (j : ℝ) - 1| := by
  rw [Finset.prod_range_succ']
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_zero, zero_sub, abs_neg, abs_one,
    mul_one]
  have hpos : ∀ j : ℕ, |2 * ((j : ℝ) + 1) - 1| = 2 * j + 1 := fun j => by
    rw [abs_of_pos (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])]; ring
  simp_rw [hpos]
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    rw [Finset.prod_range_succ, Nat.factorial_succ]
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hfac : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
    have e : (2 : ℝ) ^ (N + 1) * ((N + 1 : ℕ) * N.factorial : ℕ) / (2 * (N + 1 : ℕ)) =
        2 ^ N * N.factorial := by
      push_cast; field_simp; ring
    rw [e]
    have h2 : (2 : ℝ) ^ N * N.factorial ≤ 2 ^ N * N.factorial / (2 * N) * (2 * N + 1) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) N]
    exact h2.trans (mul_le_mul_of_nonneg_right ih (by positivity))

/-- `∏_{j ≠ k, j ≤ N} |k − j| = k!(N − k)!`. -/
theorem ni_prod_dist_eq (N k : ℕ) (hk : k ≤ N) :
    ∏ j ∈ (Finset.range (N + 1)).erase k, |(k : ℝ) - j| =
      (k.factorial : ℝ) * (N - k).factorial := by
  set g : ℕ → ℝ := fun j => if j = k then 1 else |(k : ℝ) - j|
  have h1 : ∏ j ∈ (Finset.range (N + 1)).erase k, |(k : ℝ) - j| =
      ∏ j ∈ (Finset.range (N + 1)).erase k, g j :=
    Finset.prod_congr rfl fun j hj => by simp [g, Finset.ne_of_mem_erase hj]
  rw [h1, Finset.prod_erase _ (by simp [g]), ← Finset.prod_range_mul_prod_Ico g
    (show k ≤ N + 1 by omega), Finset.prod_eq_prod_Ico_succ_bot (show k < N + 1 by omega)]
  have hlow : ∏ j ∈ Finset.range k, g j = k.factorial := by
    rw [← Finset.prod_range_reflect, ← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    simp only [g, show k - 1 - j ≠ k by omega, ↓reduceIte]
    rw [abs_of_nonneg (by
      have : ((k - 1 - j : ℕ) : ℝ) ≤ k := by exact_mod_cast (show k - 1 - j ≤ k by omega)
      linarith)]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  have hhigh : ∏ j ∈ Finset.Ico (k + 1) (N + 1), g j = (N - k).factorial := by
    rw [Finset.prod_Ico_eq_prod_range, show N + 1 - (k + 1) = N - k by omega,
      ← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [g, show k + 1 + j ≠ k by omega, ↓reduceIte]
    rw [abs_sub_comm, abs_of_nonneg (by push_cast; linarith)]
    push_cast
    ring
  rw [hlow, hhigh]
  simp [g]

/-- At `x* = −1 + 1/N`, the Lagrange basis for the uniform nodes satisfies
`|ℓₖ(x*)| ≥ C(N, k)/(4N²)`. -/
theorem ni_uniform_basis_lower (N : ℕ) (hN : 1 ≤ N) (k : ℕ) (hk : k ≤ N) :
    (N.choose k : ℝ) / (4 * N ^ 2) ≤
      |(Lagrange.basis (Finset.range (N + 1)) (ni_uniformGrid N) k).eval ((-1 : ℝ) + 1 / N)| := by
  set s := Finset.range (N + 1)
  set v := ni_uniformGrid N
  set xs : ℝ := -1 + 1 / N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hdiff : ∀ j : ℕ, xs - v j = -(2 * (j : ℝ) - 1) / N := by
    intro j; simp only [xs, v, ni_uniformGrid]; field_simp; ring
  have hne : ∀ j : ℕ, xs ≠ v j := by
    intro j h
    have := hdiff j
    rw [h, sub_self] at this
    have h2 : 2 * (j : ℝ) - 1 = 0 := by
      have := this.symm
      rw [neg_div, neg_eq_zero, div_eq_zero_iff] at this
      exact this.resolve_right hN'.ne'
    have : (2 * j : ℤ) = 1 := by exact_mod_cast (by linarith : (2 * (j : ℝ)) = 1)
    omega
  have hks : k ∈ s := Finset.mem_range.mpr (by omega)
  rw [Lagrange.eval_basis_not_at_node hks (hne k), Lagrange.eval_nodal, Lagrange.nodalWeight,
    abs_mul, abs_mul, abs_inv, Finset.abs_prod, Finset.abs_prod]
  simp only [abs_inv, Finset.prod_inv_distrib]
  -- the three factors
  have hnum : ∏ j ∈ s, |xs - v j| = (∏ j ∈ s, |2 * (j : ℝ) - 1|) / (N : ℝ) ^ (N + 1) := by
    simp_rw [hdiff, abs_div, abs_neg, Nat.abs_cast]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  have hden : ∏ j ∈ s.erase k, |v k - v j| =
      (2 / N) ^ N * ((k.factorial : ℝ) * (N - k).factorial) := by
    have : ∀ j, |v k - v j| = 2 / N * |(k : ℝ) - j| := by
      intro j
      simp only [v, ni_uniformGrid]
      rw [show -1 + 2 * (k : ℝ) / N - (-1 + 2 * j / N) = 2 / N * (k - j) by ring, abs_mul,
        abs_of_pos (by positivity)]
    simp_rw [this]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_erase_of_mem hks,
      Finset.card_range, Nat.add_sub_cancel, ni_prod_dist_eq N k hk]
  have hxk : |xs - v k| = |2 * (k : ℝ) - 1| / N := by
    rw [hdiff, abs_div, abs_neg, Nat.abs_cast]
  rw [hnum, hden, hxk]
  have hodd := ni_prod_odd_ge N hN
  have hk1 : |2 * (k : ℝ) - 1| ≤ 2 * N := by
    have : (k : ℝ) ≤ N := by exact_mod_cast hk
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    rw [abs_le]; constructor <;> linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hk0 : 0 < |2 * (k : ℝ) - 1| := by
    rw [abs_pos]
    intro h
    have : (2 * k : ℤ) = 1 := by exact_mod_cast (by linarith : (2 * (k : ℝ)) = 1)
    omega
  have hchoose : (N.choose k : ℝ) * (k.factorial * (N - k).factorial) = N.factorial := by
    rw [← mul_assoc]
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have hfk : (0 : ℝ) < k.factorial * (N - k).factorial := by
    have := k.factorial_pos; have := (N - k).factorial_pos; positivity
  set A := ∏ j ∈ s, |2 * (j : ℝ) - 1|
  set F : ℝ := k.factorial * (N - k).factorial
  -- the value equals `A / (|2k − 1| 2^N F)`
  have hval : A / (N : ℝ) ^ (N + 1) * (((2 / N) ^ N * F)⁻¹ * (|2 * (k : ℝ) - 1| / N)⁻¹) =
      A / (|2 * (k : ℝ) - 1| * 2 ^ N * F) := by
    rw [div_pow, pow_succ]
    field_simp
  rw [hval, div_le_div_iff₀ (by positivity) (by positivity)]
  have hA : (2 : ℝ) ^ N * N.factorial / (2 * N) ≤ A := hodd
  rw [div_le_iff₀ (by positivity)] at hA
  have hNf : (N.choose k : ℝ) * F = N.factorial := hchoose
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  have hC : (0 : ℝ) ≤ N.choose k := Nat.cast_nonneg _
  have s1 : (N.choose k : ℝ) * (|2 * (k : ℝ) - 1| * 2 ^ N * F) ≤
      (N.choose k : ℝ) * (2 * N * 2 ^ N * F) := by
    apply mul_le_mul_of_nonneg_left _ hC
    have := mul_le_mul_of_nonneg_right hk1 (le_of_lt (mul_pos h2N hfk))
    linarith [this]
  have s2 : (N.choose k : ℝ) * (2 * N * 2 ^ N * F) = 2 * N * (2 ^ N * N.factorial) := by
    rw [← hNf]; ring
  nlinarith [s1, s2, hA]

/-- The Lebesgue function of the uniform nodes at `x* = −1 + 1/N` is at least `2^N/(4N²)`. -/
theorem ni_uniform_lebesgue_lower (N : ℕ) (hN : 1 ≤ N) :
    (2 : ℝ) ^ N / (4 * N ^ 2) ≤ ∑ k ∈ Finset.range (N + 1),
      |(Lagrange.basis (Finset.range (N + 1)) (ni_uniformGrid N) k).eval ((-1 : ℝ) + 1 / N)| := by
  have h : ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) / (4 * N ^ 2) ≤
      ∑ k ∈ Finset.range (N + 1),
        |(Lagrange.basis (Finset.range (N + 1)) (ni_uniformGrid N) k).eval ((-1 : ℝ) + 1 / N)| :=
    Finset.sum_le_sum fun k hk =>
      ni_uniform_basis_lower N hN k (by have := Finset.mem_range.mp hk; omega)
  refine le_trans (le_of_eq ?_) h
  rw [← Finset.sum_div, ← Nat.cast_sum, Nat.sum_range_choose]
  push_cast
  ring

theorem ni_uniformGrid_mem {N : ℕ} (hN : 1 ≤ N) {k : ℕ} (hk : k ≤ N) :
    ni_uniformGrid N k ∈ Set.Icc (-1 : ℝ) 1 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
  unfold ni_uniformGrid
  constructor
  · have : 0 ≤ 2 * (k : ℝ) / N := by positivity
    linarith
  · have : 2 * (k : ℝ) / N ≤ 2 := by rw [div_le_iff₀ hN']; linarith
    linarith

/-- The polynomial interpolation operator at the uniform nodes `xₖ = −1 + 2k/N` on
`C([−1, 1])`, `f ↦ ∑ₖ f(xₖ) ℓₖ`, as a continuous linear map. -/
noncomputable def ni_uniformInterp (N : ℕ) :
    C(Set.Icc (-1 : ℝ) 1, ℝ) →L[ℝ] C(Set.Icc (-1 : ℝ) 1, ℝ) :=
  ∑ k ∈ Finset.range (N + 1),
    (ContinuousMap.evalCLM ℝ (Set.projIcc (-1 : ℝ) 1 (by norm_num) (ni_uniformGrid N k))).smulRight
      ((Lagrange.basis (Finset.range (N + 1)) (ni_uniformGrid N) k).toContinuousMapOn
        (Set.Icc (-1 : ℝ) 1))

theorem ni_uniformInterp_apply (N : ℕ) (f : C(Set.Icc (-1 : ℝ) 1, ℝ)) (x : Set.Icc (-1 : ℝ) 1) :
    ni_uniformInterp N f x = ∑ k ∈ Finset.range (N + 1),
      f (Set.projIcc (-1 : ℝ) 1 (by norm_num) (ni_uniformGrid N k)) *
        (Lagrange.basis (Finset.range (N + 1)) (ni_uniformGrid N) k).eval (x : ℝ) := by
  simp [ni_uniformInterp, ContinuousMap.sum_apply]

/-- `ni_uniformInterp N f` is the polynomial interpolating `f` at the uniform nodes. -/
theorem ni_uniformInterp_eq_interpolate (N : ℕ) (f : C(Set.Icc (-1 : ℝ) 1, ℝ))
    (x : Set.Icc (-1 : ℝ) 1) :
    ni_uniformInterp N f x = (Lagrange.interpolate (Finset.range (N + 1)) (ni_uniformGrid N)
      (fun k => f (Set.projIcc (-1 : ℝ) 1 (by norm_num) (ni_uniformGrid N k)))).eval (x : ℝ) := by
  rw [ni_uniformInterp_apply, Lagrange.interpolate_apply, eval_finsetSum]
  simp

/-- On `[x₀, x_N]` the linear spline through values in `[−1, 1]` stays in `[−1, 1]`. -/
theorem ni_linSpline_abs_le {N : ℕ} (hN : 1 ≤ N) {x : ℕ → ℝ} (hx : StrictMono x) {y : ℕ → ℝ}
    (hy : ∀ k, |y k| ≤ 1) {t : ℝ} (ht : t ∈ Set.Icc (x 0) (x N)) :
    |ni_linSpline N x y t| ≤ 1 := by
  obtain ⟨j, hj, htj⟩ := ni_node_interval N hN t ht
  rw [ni_linSpline_piece hx y hj htj, ni_slope]
  have hlt : x j < x (j + 1) := hx (Nat.lt_succ_self j)
  set lam := (t - x j) / (x (j + 1) - x j)
  have hl0 : 0 ≤ lam := div_nonneg (by linarith [htj.1]) (by linarith)
  have hl1 : lam ≤ 1 := by rw [div_le_one (by linarith)]; linarith [htj.2]
  have e : y j + (y (j + 1) - y j) / (x (j + 1) - x j) * (t - x j) =
      (1 - lam) * y j + lam * y (j + 1) := by
    simp only [lam]; field_simp; ring
  rw [e]
  have h1 := abs_le.mp (hy j)
  have h2 := abs_le.mp (hy (j + 1))
  rw [abs_le]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- `‖ni_uniformInterp N‖ ≥ 2^N/(4N²)` for `N ≥ 1`. -/
theorem ni_uniformInterp_norm_ge (N : ℕ) (hN : 1 ≤ N) :
    (2 : ℝ) ^ N / (4 * N ^ 2) ≤ ‖ni_uniformInterp N‖ := by
  set xs : ℝ := -1 + 1 / N
  set ℓ := fun k => (Lagrange.basis (Finset.range (N + 1)) (ni_uniformGrid N) k).eval xs
  set σ : ℕ → ℝ := fun k => if 0 ≤ ℓ k then 1 else -1
  have hmono := ni_uniformGrid_strictMono (show 0 < N by omega)
  obtain ⟨hlo, hhi⟩ := ni_uniformGrid_ends (show 0 < N by omega)
  have hspl := ni_linear_spline_exists (show 0 < N by omega) hmono σ
  have hcont : Continuous (ni_linSpline N (ni_uniformGrid N) σ) := by
    unfold ni_linSpline; fun_prop
  set φ : C(Set.Icc (-1 : ℝ) 1, ℝ) :=
    ⟨fun t => ni_linSpline N (ni_uniformGrid N) σ t, hcont.comp continuous_subtype_val⟩
  have hφ : ‖φ‖ ≤ 1 := by
    refine (ContinuousMap.norm_le _ zero_le_one).mpr fun t => ?_
    rw [Real.norm_eq_abs]
    refine ni_linSpline_abs_le hN hmono (fun k => ?_) ?_
    · simp only [σ]; split_ifs <;> simp
    · rw [hlo, hhi]; exact t.2
  have hxs : xs ∈ Set.Icc (-1 : ℝ) 1 := by
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    constructor
    · have : 0 ≤ 1 / (N : ℝ) := by positivity
      simp only [xs]; linarith
    · have : 1 / (N : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hN'
      simp only [xs]; linarith
  have hval : ni_uniformInterp N φ ⟨xs, hxs⟩ = ∑ k ∈ Finset.range (N + 1), |ℓ k| := by
    rw [ni_uniformInterp_apply]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkN : k ≤ N := by have := Finset.mem_range.mp hk; omega
    have hproj : (Set.projIcc (-1 : ℝ) 1 (by norm_num) (ni_uniformGrid N k) : ℝ) =
        ni_uniformGrid N k := by
      rw [Set.projIcc_of_mem _ (ni_uniformGrid_mem hN hkN)]
    have hφk : φ (Set.projIcc (-1 : ℝ) 1 (by norm_num) (ni_uniformGrid N k)) = σ k := by
      change ni_linSpline N (ni_uniformGrid N) σ
        (Set.projIcc (-1 : ℝ) 1 (by norm_num) (ni_uniformGrid N k) : ℝ) = σ k
      rw [hproj, hspl.2 k hkN]
    rw [hφk]
    change σ k * ℓ k = |ℓ k|
    simp only [σ]
    split_ifs with h
    · rw [one_mul, abs_of_nonneg h]
    · rw [abs_of_neg (not_le.mp h)]; ring
  have h1 : |ni_uniformInterp N φ ⟨xs, hxs⟩| ≤ ‖ni_uniformInterp N‖ := by
    calc |ni_uniformInterp N φ ⟨xs, hxs⟩| ≤ ‖ni_uniformInterp N φ‖ := by
          rw [← Real.norm_eq_abs]; exact ContinuousMap.norm_coe_le_norm _ _
      _ ≤ ‖ni_uniformInterp N‖ * ‖φ‖ := (ni_uniformInterp N).le_opNorm φ
      _ ≤ ‖ni_uniformInterp N‖ * 1 :=
        mul_le_mul_of_nonneg_left hφ (ni_uniformInterp N).opNorm_nonneg
      _ = ‖ni_uniformInterp N‖ := mul_one _
  rw [hval, abs_of_nonneg (Finset.sum_nonneg fun k _ => abs_nonneg _)] at h1
  exact (ni_uniform_lebesgue_lower N hN).trans h1

/-- Miao, p. 360: interpolation at uniformly spaced nodes does not necessarily converge: there is
a continuous `f` on `[−1, 1]` such that its interpolating polynomials at the uniform nodes
`xₖ = −1 + 2k/N`, `k = 0, …, N`, do not converge to `f` uniformly as `N → ∞`. -/
theorem ni_uniform_interp_not_convergent :
    ∃ f : C(Set.Icc (-1 : ℝ) 1, ℝ),
      ¬ Tendsto (fun n : ℕ => ni_uniformInterp (n + 1) f) atTop (𝓝 f) := by
  by_contra hcon
  push Not at hcon
  have hbdd : ∀ f : C(Set.Icc (-1 : ℝ) 1, ℝ), ∃ C, ∀ n : ℕ, ‖ni_uniformInterp (n + 1) f‖ ≤ C := by
    intro f
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
      (Metric.isBounded_range_of_tendsto _ (hcon f))
    exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩
  obtain ⟨C', hC'⟩ := banach_steinhaus hbdd
  have ht := tendsto_pow_const_div_const_pow_of_one_lt 2 (one_lt_two : (1 : ℝ) < 2)
  have hε : (0 : ℝ) < 1 / (4 * (|C'| + 1)) := by positivity
  obtain ⟨N, hN2, hN1⟩ := ((ht.eventually (gt_mem_nhds hε)).and
    (eventually_ge_atTop 1)).exists
  have hlow := ni_uniformInterp_norm_ge N hN1
  have hup := hC' (N - 1)
  rw [Nat.sub_add_cancel hN1] at hup
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN1
  have h2 : (0 : ℝ) < 2 ^ N := by positivity
  rw [div_lt_div_iff₀ h2 (by positivity)] at hN2
  rw [div_le_iff₀ (by positivity)] at hlow
  have : (2 : ℝ) ^ N ≤ C' * (4 * N ^ 2) := by
    calc (2 : ℝ) ^ N ≤ ‖ni_uniformInterp N‖ * (4 * N ^ 2) := hlow
      _ ≤ C' * (4 * N ^ 2) := mul_le_mul_of_nonneg_right hup (by positivity)
  have hC'abs : C' ≤ |C'| := le_abs_self C'
  nlinarith [abs_nonneg C', sq_nonneg (N : ℝ)]

end Miao.NumericalMethods

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Markov matrices, contractions and Blackwell's condition: the shared vocabulary

Copied from `FiniteStates/MarkovDecisionProcesses` (module `Basics`), namespace renamed to
`Miao.NumericalMethods.NP`.

Sargent and Stachurski, *Dynamic Programming*, Volume 1, Chapter 5 builds on
Markov matrices (§2.3.1.3), the contraction machinery of §1.2.2, Blackwell's
condition (Lemma 2.2.4), the comparison of fixed points of ordered operators
(Proposition 2.2.7) and the estimate `|max f − max g| ≤ max |f − g|`
(Lemma 2.2.2). Each chapter project is self-contained, so these are restated
here with short Mathlib proofs.
-/

namespace Miao.NumericalMethods.NP

open Finset Matrix Filter Topology Function

variable {X : Type*} [Fintype X]

/-- A stochastic (Markov) matrix on the finite state space `X` (Vol. 1, p. 71): nonnegative with
unit row sums. -/
structure IsMarkov (P : Matrix X X ℝ) : Prop where
  nonneg : ∀ x x', 0 ≤ P x x'
  rowsum : ∀ x, ∑ x', P x x' = 1

/-- A distribution on `X` (Vol. 1, p. 31): nonnegative and summing to one. -/
structure IsDistribution (ψ : X → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ ψ x
  sum_eq_one : ∑ x, ψ x = 1

/-- `(Ph)(x) = ∑ h(x')P(x, x')`, Vol. 1 (3.12). -/
theorem mulVec_apply_eq (P : Matrix X X ℝ) (h : X → ℝ) (x : X) :
    (P *ᵥ h) x = ∑ x', h x' * P x x' := by
  simp only [mulVec, dotProduct, mul_comm]

theorem IsMarkov.mul {P Q : Matrix X X ℝ} (hP : IsMarkov P) (hQ : IsMarkov Q) :
    IsMarkov (P * Q) where
  nonneg x x' := by
    rw [Matrix.mul_apply]
    exact sum_nonneg fun z _ => mul_nonneg (hP.nonneg x z) (hQ.nonneg z x')
  rowsum x := by
    simp only [Matrix.mul_apply]
    rw [sum_comm]
    simp only [← mul_sum, hQ.rowsum, mul_one, hP.rowsum]

/-- `Pᵏ` is Markov. -/
theorem IsMarkov.pow [DecidableEq X] {P : Matrix X X ℝ} (hP : IsMarkov P) (k : ℕ) :
    IsMarkov (P ^ k) := by
  induction k with
  | zero =>
    refine ⟨fun x x' => ?_, fun x => ?_⟩
    · simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
    · simp [pow_zero, Matrix.one_apply]
  | succ k ih => rw [pow_succ]; exact ih.mul hP

/-- A Markov matrix preserves `≤` on functions. -/
theorem IsMarkov.mulVec_le_mulVec {P : Matrix X X ℝ} (hP : IsMarkov P) {f g : X → ℝ} (hfg : f ≤ g) :
    P *ᵥ f ≤ P *ᵥ g := fun x =>
  sum_le_sum fun x' _ => mul_le_mul_of_nonneg_left (hfg x') (hP.nonneg x x')

/-- `P𝟙 = 𝟙`: constants are fixed by a Markov matrix. -/
theorem IsMarkov.mulVec_const {P : Matrix X X ℝ} (hP : IsMarkov P) (c : ℝ) :
    P *ᵥ (fun _ => c) = fun _ => c := by
  funext x
  simp only [mulVec, dotProduct, ← sum_mul, hP.rowsum, one_mul]

/-- `|Ph(x)| ≤ ‖h‖_∞` (Vol. 1, Ex 3.2.1). -/
theorem IsMarkov.abs_mulVec_le {P : Matrix X X ℝ} (hP : IsMarkov P) (h : X → ℝ) (x : X) :
    |(P *ᵥ h) x| ≤ ‖h‖ := by
  have hb : ∀ x', |h x'| ≤ ‖h‖ := fun x' => by
    have := norm_le_pi_norm h x'
    rwa [Real.norm_eq_abs] at this
  calc |(P *ᵥ h) x| = |∑ x', P x x' * h x'| := rfl
    _ ≤ ∑ x', |P x x' * h x'| := abs_sum_le_sum_abs _ _
    _ = ∑ x', P x x' * |h x'| := sum_congr rfl fun x' _ => by
        rw [abs_mul, abs_of_nonneg (hP.nonneg x x')]
    _ ≤ ∑ x', P x x' * ‖h‖ :=
        sum_le_sum fun x' _ => mul_le_mul_of_nonneg_left (hb x') (hP.nonneg x x')
    _ = ‖h‖ := by rw [← sum_mul, hP.rowsum, one_mul]

/-- `‖Ph‖_∞ ≤ ‖h‖_∞`. -/
theorem IsMarkov.norm_mulVec_le {P : Matrix X X ℝ} (hP : IsMarkov P) (h : X → ℝ) :
    ‖P *ᵥ h‖ ≤ ‖h‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro x
  rw [Real.norm_eq_abs]
  exact hP.abs_mulVec_le h x

/-- `|(Pf)(x) − (Pg)(x)| ≤ ‖f − g‖_∞`. -/
theorem IsMarkov.abs_mulVec_sub_le {P : Matrix X X ℝ} (hP : IsMarkov P) (f g : X → ℝ) (x : X) :
    |(P *ᵥ f) x - (P *ᵥ g) x| ≤ ‖f - g‖ := by
  have := hP.abs_mulVec_le (f - g) x
  rwa [mulVec_sub, Pi.sub_apply] at this

/-- Global stability (Vol. 1, p. 22). -/
def GloballyStable {U : Type*} [TopologicalSpace U] (T : U → U) : Prop :=
  ∃ u' : U, IsFixedPt T u' ∧ (∀ v, IsFixedPt T v → v = u') ∧
    ∀ u, Tendsto (fun k : ℕ => T^[k] u) atTop (𝓝 u')

variable {E : Type*} [NormedAddCommGroup E]

/-- A contraction of modulus `L` on `U` (Vol. 1, (1.17)). -/
structure IsContractionOn (T : E → E) (U : Set E) (L : ℝ) : Prop where
  mapsTo : Set.MapsTo T U U
  nonneg : 0 ≤ L
  lt_one : L < 1
  norm_sub_le : ∀ u ∈ U, ∀ v ∈ U, ‖T u - T v‖ ≤ L * ‖u - v‖

namespace IsContractionOn

variable {T : E → E} {U : Set E} {L : ℝ}

theorem fixedPt_unique (h : IsContractionOn T U L) {u v : E} (hu : u ∈ U) (hv : v ∈ U)
    (hfu : IsFixedPt T u) (hfv : IsFixedPt T v) : u = v := by
  have hb := h.norm_sub_le u hu v hv
  rw [hfu.eq, hfv.eq] at hb
  have hnn : 0 ≤ ‖u - v‖ := norm_nonneg _
  have hpos : 0 < 1 - L := by linarith [h.lt_one]
  have : ‖u - v‖ ≤ 0 := by nlinarith
  exact sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm this hnn))

theorem iterate_mem (h : IsContractionOn T U L) {u : E} (hu : u ∈ U) (k : ℕ) : T^[k] u ∈ U := by
  induction k with
  | zero => simpa using hu
  | succ k ih => rw [iterate_succ_apply']; exact h.mapsTo ih

theorem norm_iterate_sub_fixedPt_le (h : IsContractionOn T U L) {u u' : E} (hu : u ∈ U)
    (hu' : u' ∈ U) (hfix : IsFixedPt T u') (k : ℕ) :
    ‖T^[k] u - u'‖ ≤ L ^ k * ‖u - u'‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply']
    calc ‖T (T^[k] u) - u'‖ = ‖T (T^[k] u) - T u'‖ := by rw [hfix.eq]
      _ ≤ L * ‖T^[k] u - u'‖ := h.norm_sub_le _ (h.iterate_mem hu k) _ hu'
      _ ≤ L * (L ^ k * ‖u - u'‖) := mul_le_mul_of_nonneg_left ih h.nonneg
      _ = L ^ (k + 1) * ‖u - u'‖ := by ring

theorem tendsto_iterate_fixedPt (h : IsContractionOn T U L) {u u' : E} (hu : u ∈ U) (hu' : u' ∈ U)
    (hfix : IsFixedPt T u') : Tendsto (fun k : ℕ => T^[k] u) atTop (𝓝 u') := by
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [dist_eq_norm]
  refine squeeze_zero (fun _ => norm_nonneg _) (h.norm_iterate_sub_fixedPt_le hu hu' hfix) ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h.nonneg h.lt_one).mul_const ‖u - u'‖

/-- Banach's theorem (Vol. 1, Theorem 1.2.3), existence, from Mathlib's `ContractingWith`. -/
theorem exists_fixedPt [CompleteSpace E] (h : IsContractionOn T U L) (hU : IsClosed U)
    (hne : U.Nonempty) : ∃ u' ∈ U, IsFixedPt T u' := by
  have : CompleteSpace U := hU.completeSpace_coe
  have : Nonempty U := hne.to_subtype
  let T' : U → U := h.mapsTo.restrict T U U
  have hT' : ContractingWith ⟨L, h.nonneg⟩ T' := by
    refine ⟨by exact_mod_cast h.lt_one, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [T', Set.MapsTo.val_restrict_apply, Subtype.dist_eq, dist_eq_norm]
    exact h.norm_sub_le x x.2 y y.2
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : U, IsFixedPt T' u₀ := ⟨_, hT'.fixedPoint_isFixedPt⟩
  exact ⟨u₀.1, u₀.2, congrArg Subtype.val hu₀⟩

/-- A contraction on the whole of a complete space is globally stable (Vol. 1, Theorem 1.2.3). -/
theorem globallyStable_univ [CompleteSpace E] (h : IsContractionOn T Set.univ L) :
    GloballyStable T := by
  obtain ⟨u', -, hu'⟩ := h.exists_fixedPt isClosed_univ ⟨0, Set.mem_univ 0⟩
  exact ⟨u', hu', fun v hv => h.fixedPt_unique (Set.mem_univ v) (Set.mem_univ u') hv hu',
    fun u => h.tendsto_iterate_fixedPt (Set.mem_univ u) (Set.mem_univ u') hu'⟩

end IsContractionOn

omit [Fintype X] in
/-- Vol. 1, Proposition 2.2.7, in the form used here: if `S ≤ T` pointwise, `T` is order
preserving and its iterates from any point converge to `u_T`, then every fixed point of `S` lies
below `u_T`. The ambient space is `ℝ^X` with the pointwise order. -/
theorem fixedPt_le_of_le {S T : (X → ℝ) → (X → ℝ)} (hST : ∀ v, S v ≤ T v) (hT : Monotone T)
    {uS uT : X → ℝ} (huS : IsFixedPt S uS) (hlim : Tendsto (fun k : ℕ => T^[k] uS) atTop (𝓝 uT)) :
    uS ≤ uT := by
  have hle : ∀ k : ℕ, uS ≤ T^[k] uS := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [iterate_succ_apply']
      calc uS = S uS := huS.eq.symm
        _ ≤ T uS := hST uS
        _ ≤ T (T^[k] uS) := hT ih
  intro x
  exact ge_of_tendsto' (tendsto_pi_nhds.1 hlim x) fun k => hle k x

omit [Fintype X] in
/-- If `u ≤ Tu`, `T` is order preserving and `Tᵏu → u*`, then `u ≤ u*`: the monotone-improvement
step behind Howard policy iteration. -/
theorem le_fixedPt_of_le_apply {T : (X → ℝ) → (X → ℝ)} (hT : Monotone T) {u u' : X → ℝ}
    (hu : u ≤ T u) (hlim : Tendsto (fun k : ℕ => T^[k] u) atTop (𝓝 u')) : u ≤ u' := by
  have hle : ∀ k : ℕ, u ≤ T^[k] u := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [iterate_succ_apply']
      exact hu.trans (hT ih)
  intro x
  exact ge_of_tendsto' (tendsto_pi_nhds.1 hlim x) fun k => hle k x

/-- Blackwell's condition (Vol. 1, Lemma 2.2.4) on all of `ℝ^X`: an order-preserving `T` with
`T(u + c) ≤ Tu + βc` for `c ≥ 0` is a contraction of modulus `β` in the supremum norm. -/
theorem isContractionOn_of_blackwell {T : (X → ℝ) → (X → ℝ)} {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hmono : Monotone T)
    (hdisc : ∀ u : X → ℝ, ∀ c : ℝ, 0 ≤ c → T (u + fun _ : X => c) ≤ T u + fun _ : X => β * c) :
    IsContractionOn T Set.univ β := by
  refine ⟨Set.mapsTo_univ _ _, hβ0, hβ1, fun u _ v _ => ?_⟩
  have key : ∀ u v : X → ℝ, ∀ x : X, T u x - T v x ≤ β * ‖u - v‖ := by
    intro u v x
    have hle : u ≤ v + fun _ : X => ‖u - v‖ := fun y => by
      have := norm_le_pi_norm (u - v) y
      rw [Pi.sub_apply, Real.norm_eq_abs] at this
      simp only [Pi.add_apply]
      linarith [le_abs_self (u y - v y)]
    have h1 := hmono hle x
    have h2 := hdisc v ‖u - v‖ (norm_nonneg _) x
    simp only [Pi.add_apply] at h1 h2
    linarith
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg hβ0 (norm_nonneg _))]
  intro x
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_sub_le_iff]
  refine ⟨key u v x, ?_⟩
  have := key v u x
  rwa [norm_sub_rev] at this

omit [Fintype X] in
/-- Vol. 1, Lemma 2.2.2: for a nonempty finite `D`, `|max f − max g| ≤ max |f − g|`. -/
theorem abs_sup'_sub_sup'_le {D : Type*} {s : Finset D} (hs : s.Nonempty) (f g : D → ℝ) :
    |s.sup' hs f - s.sup' hs g| ≤ s.sup' hs fun z => |f z - g z| := by
  have key : ∀ f g : D → ℝ, s.sup' hs f - s.sup' hs g ≤ s.sup' hs fun z => |f z - g z| := by
    intro f g
    rw [sub_le_iff_le_add]
    refine Finset.sup'_le hs f fun z hz => ?_
    calc f z = (f z - g z) + g z := by ring
      _ ≤ |f z - g z| + g z := add_le_add (le_abs_self _) le_rfl
      _ ≤ (s.sup' hs fun z => |f z - g z|) + s.sup' hs g :=
          add_le_add (Finset.le_sup' (fun z => |f z - g z|) hz) (Finset.le_sup' g hz)
  rw [abs_sub_le_iff]
  refine ⟨key f g, ?_⟩
  have := key g f
  simpa [abs_sub_comm] using this

end Miao.NumericalMethods.NP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Markov decision processes, policies and lifetime values

Copied from `FiniteStates/MarkovDecisionProcesses` (module `MDP`), namespace renamed to
`Miao.NumericalMethods.NP`.

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §5.1.1 and §5.1.3.1
(pp. 128–136).

An MDP is `M = (Γ, β, r, P)`: a nonempty feasible correspondence `Γ`, a
discount factor `β ∈ (0, 1)`, a reward `r` and a stochastic kernel `P` from the
feasible state–action pairs `G` to `X`. Here `r` and `P` are given on all of
`X × A`, with `P(x, a, ·)` a distribution for every `a`; off `G` their values
never enter, since maximisation is over `Γ(x)` and policies are feasible.

A feasible policy `σ` induces the Markov matrix `P_σ(x, x') = P(x, σ(x), x')`
and reward `r_σ(x) = r(x, σ(x))`; its lifetime value is
`v_σ = ∑ βᵗP_σᵗ r_σ = (I − βP_σ)⁻¹ r_σ`, (5.18), the unique fixed point of the
policy operator `T_σ v = r_σ + βP_σ v`, (5.19)–(5.20), which is an
order-preserving contraction of modulus `β` (Exercise 5.1.7). Exercise 5.1.6
bounds `v_σ`, Exercises 5.1.8–5.1.9 identify the iterates `T_σᵏ v` with
truncated discounted sums.
-/

namespace Miao.NumericalMethods.NP

open Finset Matrix Filter Topology Function

/-- A Markov decision process `M = (Γ, β, r, P)` on the finite state space `X` and action space
`A` (p. 129). -/
structure MDP (X A : Type*) [Fintype X] [Fintype A] where
  Γ : X → Finset A
  Γ_nonempty : ∀ x, (Γ x).Nonempty
  β : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1
  r : X → A → ℝ
  P : X → A → X → ℝ
  P_nonneg : ∀ x a x', 0 ≤ P x a x'
  P_rowsum : ∀ x a, ∑ x', P x a x' = 1

namespace MDP

variable {X A : Type*} [Fintype X] [Fintype A] (M : MDP X A)

/-- The feasible state–action pairs `G = {(x, a) : a ∈ Γ(x)}` (p. 129). -/
def Feasible (x : X) (a : A) : Prop := a ∈ M.Γ x

/-- A feasible policy (5.16): `σ(x) ∈ Γ(x)` for all `x`. -/
abbrev IsFeasible (σ : X → A) : Prop := ∀ x, σ x ∈ M.Γ x

/-- The set `Σ` of feasible policies (5.16), as a subtype. -/
abbrev Policy := {σ : X → A // M.IsFeasible σ}

/-- A feasible policy exists: choose any feasible action in each state. -/
noncomputable def defaultPolicy : M.Policy :=
  ⟨fun x => (M.Γ_nonempty x).choose, fun x => (M.Γ_nonempty x).choose_spec⟩

theorem policy_nonempty : Nonempty M.Policy := ⟨M.defaultPolicy⟩

/-- The row `P(x, a, ·)` is a distribution. -/
theorem isDistribution_P (x : X) (a : A) : IsDistribution (M.P x a) :=
  ⟨M.P_nonneg x a, M.P_rowsum x a⟩

/-- The closed-loop transition matrix `P_σ(x, x') = P(x, σ(x), x')` (p. 134). -/
def Pσ (σ : X → A) : Matrix X X ℝ := Matrix.of fun x x' => M.P x (σ x) x'

theorem Pσ_apply (σ : X → A) (x x' : X) : M.Pσ σ x x' = M.P x (σ x) x' := rfl

/-- `P_σ ∈ M(ℝ^X)` (p. 134). -/
theorem isMarkov_Pσ (σ : X → A) : IsMarkov (M.Pσ σ) :=
  ⟨fun x x' => M.P_nonneg x (σ x) x', fun x => M.P_rowsum x (σ x)⟩

/-- The reward under `σ`: `r_σ(x) = r(x, σ(x))` (p. 134). -/
def rσ (σ : X → A) : X → ℝ := fun x => M.r x (σ x)

/-- The action value `B(x, a, v) = r(x, a) + β ∑ v(x')P(x, a, x')`, the expression maximised in
the Bellman equation (5.2). -/
def B (v : X → ℝ) (x : X) (a : A) : ℝ := M.r x a + M.β * ∑ x', v x' * M.P x a x'

/-- The policy operator (5.19): `(T_σ v)(x) = r(x, σ(x)) + β ∑ v(x')P(x, σ(x), x')`. -/
def Tσ (σ : X → A) (v : X → ℝ) : X → ℝ := fun x => M.B v x (σ x)

theorem Tσ_apply (σ : X → A) (v : X → ℝ) (x : X) :
    M.Tσ σ v x = M.r x (σ x) + M.β * ∑ x', v x' * M.P x (σ x) x' := rfl

/-- (5.20): `T_σ v = r_σ + βP_σ v`. -/
theorem Tσ_eq (σ : X → A) (v : X → ℝ) : M.Tσ σ v = M.rσ σ + M.β • (M.Pσ σ *ᵥ v) := by
  funext x
  simp only [Tσ, B, rσ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mulVec_apply_eq, Pσ_apply]

/-- Exercise 5.1.7 (i), p. 135: `T_σ` is an order-preserving self-map on `ℝ^X`. -/
theorem Tσ_monotone (σ : X → A) : Monotone (M.Tσ σ) := by
  intro v v' hvv' x
  simp only [Tσ_apply]
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (sum_le_sum fun x' _ => ?_) M.β_pos.le)
  exact mul_le_mul_of_nonneg_right (hvv' x') (M.P_nonneg x (σ x) x')

/-- `|(T_σ v)(x) − (T_σ v')(x)| ≤ β‖v − v'‖`. -/
theorem abs_Tσ_sub_le (σ : X → A) (v v' : X → ℝ) (x : X) :
    |M.Tσ σ v x - M.Tσ σ v' x| ≤ M.β * ‖v - v'‖ := by
  simp only [Tσ_apply]
  rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg M.β_pos.le]
  refine mul_le_mul_of_nonneg_left ?_ M.β_pos.le
  have := (M.isMarkov_Pσ σ).abs_mulVec_sub_le v v' x
  simp only [mulVec_apply_eq, Pσ_apply] at this
  exact this

/-- Exercise 5.1.7 (ii), p. 135: `T_σ` is a contraction of modulus `β` on `ℝ^X` under the supremum
norm. -/
theorem isContractionOn_Tσ (σ : X → A) : IsContractionOn (M.Tσ σ) Set.univ M.β where
  mapsTo := Set.mapsTo_univ _ _
  nonneg := M.β_pos.le
  lt_one := M.β_lt_one
  norm_sub_le v _ v' _ := by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg M.β_pos.le (norm_nonneg _))]
    intro x
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact M.abs_Tσ_sub_le σ v v' x

/-- The `σ`-value function `v_σ` (5.17)–(5.18), p. 134: the unique fixed point of `T_σ`. -/
noncomputable def vσ (σ : X → A) : X → ℝ :=
  Classical.choose ((M.isContractionOn_Tσ σ).exists_fixedPt isClosed_univ ⟨0, Set.mem_univ 0⟩)

/-- Exercise 5.1.7 (iii), p. 135: `v_σ` is a fixed point of `T_σ`. -/
theorem isFixedPt_vσ (σ : X → A) : IsFixedPt (M.Tσ σ) (M.vσ σ) :=
  (Classical.choose_spec
    ((M.isContractionOn_Tσ σ).exists_fixedPt isClosed_univ ⟨0, Set.mem_univ 0⟩)).2

/-- Exercise 5.1.7 (iii), p. 135: `v_σ` is the only fixed point of `T_σ` in `ℝ^X`. -/
theorem eq_vσ_of_isFixedPt (σ : X → A) {v : X → ℝ} (hv : IsFixedPt (M.Tσ σ) v) : v = M.vσ σ :=
  (M.isContractionOn_Tσ σ).fixedPt_unique (Set.mem_univ v) (Set.mem_univ _) hv (M.isFixedPt_vσ σ)

/-- Exercise 5.1.7 (iv), p. 135: `T_σᵏ v → v_σ` for every `v ∈ ℝ^X`. -/
theorem tendsto_iterate_Tσ (σ : X → A) (v : X → ℝ) :
    Tendsto (fun k : ℕ => (M.Tσ σ)^[k] v) atTop (𝓝 (M.vσ σ)) :=
  (M.isContractionOn_Tσ σ).tendsto_iterate_fixedPt (Set.mem_univ v) (Set.mem_univ _)
    (M.isFixedPt_vσ σ)

/-- `v_σ = r_σ + βP_σ v_σ`. -/
theorem vσ_eq (σ : X → A) : M.vσ σ = M.rσ σ + M.β • (M.Pσ σ *ᵥ M.vσ σ) := by
  rw [← Tσ_eq]
  exact (M.isFixedPt_vσ σ).eq.symm

/-- `‖βP_σ u‖ ≤ β‖u‖`. -/
theorem norm_smul_Pσ_mulVec_le (σ : X → A) (u : X → ℝ) :
    ‖M.β • (M.Pσ σ *ᵥ u)‖ ≤ M.β * ‖u‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg M.β_pos.le]
  exact mul_le_mul_of_nonneg_left ((M.isMarkov_Pσ σ).norm_mulVec_le u) M.β_pos.le

/-- `I − βP_σ` is invertible: `u = βP_σ u` forces `‖u‖ ≤ β‖u‖`. -/
theorem isUnit_one_sub_smul_Pσ [DecidableEq X] (σ : X → A) : IsUnit (1 - M.β • M.Pσ σ) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro u v huv
  have hd : (1 - M.β • M.Pσ σ) *ᵥ (u - v) = 0 := by
    rw [mulVec_sub]
    exact sub_eq_zero.2 huv
  rw [sub_mulVec, one_mulVec, sub_eq_zero, smul_mulVec] at hd
  have hnorm : ‖u - v‖ ≤ M.β * ‖u - v‖ := by
    calc ‖u - v‖ = ‖M.β • (M.Pσ σ *ᵥ (u - v))‖ := by rw [← hd]
      _ ≤ M.β * ‖u - v‖ := M.norm_smul_Pσ_mulVec_le σ _
  have : ‖u - v‖ ≤ 0 := by nlinarith [norm_nonneg (u - v), M.β_lt_one]
  exact sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm this (norm_nonneg _)))

/-- (5.18), p. 135: `v_σ = (I − βP_σ)⁻¹ r_σ`, by Lemma 3.2.1. -/
theorem vσ_eq_inv [DecidableEq X] (σ : X → A) : M.vσ σ = (1 - M.β • M.Pσ σ)⁻¹ *ᵥ M.rσ σ := by
  have hunit := M.isUnit_one_sub_smul_Pσ σ
  have h1 : (1 - M.β • M.Pσ σ) *ᵥ M.vσ σ = M.rσ σ := by
    rw [sub_mulVec, one_mulVec, smul_mulVec, sub_eq_iff_eq_add]
    exact M.vσ_eq σ
  calc M.vσ σ = (1 - M.β • M.Pσ σ)⁻¹ *ᵥ ((1 - M.β • M.Pσ σ) *ᵥ M.vσ σ) := by
        rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hunit),
          one_mulVec]
    _ = (1 - M.β • M.Pσ σ)⁻¹ *ᵥ M.rσ σ := by rw [h1]

/-- `‖βᵗP_σᵗ u‖ ≤ βᵗ‖u‖`. -/
theorem norm_pow_smul_mulVec_le [DecidableEq X] (σ : X → A) (u : X → ℝ) (t : ℕ) :
    ‖M.β ^ t • (M.Pσ σ ^ t *ᵥ u)‖ ≤ M.β ^ t * ‖u‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg M.β_pos.le t)]
  exact mul_le_mul_of_nonneg_left (((M.isMarkov_Pσ σ).pow t).norm_mulVec_le u)
    (pow_nonneg M.β_pos.le t)

/-- (5.18): the series `∑ₜ βᵗP_σᵗ r_σ` converges. -/
theorem summable_pow_smul_mulVec [DecidableEq X] (σ : X → A) :
    Summable fun t : ℕ => M.β ^ t • (M.Pσ σ ^ t *ᵥ M.rσ σ) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one M.β_pos.le M.β_lt_one).mul_right
    ‖M.rσ σ‖) (M.norm_pow_smul_mulVec_le σ _)

/-- Exercise 5.1.9 (p. 136) in matrix form: `T_σᵏ v = ∑_{t<k} βᵗP_σᵗ r_σ + βᵏP_σᵏ v`, the payoff
from following `σ` for `k` periods with terminal payoff `v`, the expectations being the entries
of `P_σᵗ`. -/
theorem iterate_Tσ_eq [DecidableEq X] (σ : X → A) (v : X → ℝ) (k : ℕ) :
    (M.Tσ σ)^[k] v =
      (∑ t ∈ range k, M.β ^ t • (M.Pσ σ ^ t *ᵥ M.rσ σ)) +
        M.β ^ k • (M.Pσ σ ^ k *ᵥ v) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply', ih, Tσ_eq, sum_range_succ', pow_zero, one_smul, pow_zero, one_mulVec]
    have h1 : ∀ (w : X → ℝ) (t : ℕ),
        M.β • (M.Pσ σ *ᵥ (M.β ^ t • (M.Pσ σ ^ t *ᵥ w))) =
          M.β ^ (t + 1) • (M.Pσ σ ^ (t + 1) *ᵥ w) := by
      intro w t
      rw [mulVec_smul, mulVec_mulVec, smul_smul, ← pow_succ', ← pow_succ']
    rw [mulVec_add, smul_add, mulVec_sum, smul_sum]
    simp only [h1]
    abel

/-- Exercise 5.1.8 (p. 135): starting from `v ≡ 0`, `T_σᵏ 0 = ∑_{t<k} βᵗP_σᵗ r_σ`. -/
theorem iterate_Tσ_zero [DecidableEq X] (σ : X → A) (k : ℕ) :
    (M.Tσ σ)^[k] 0 = ∑ t ∈ range k, M.β ^ t • (M.Pσ σ ^ t *ᵥ M.rσ σ) := by
  rw [iterate_Tσ_eq]
  simp

/-- (5.18) as a series: `v_σ = ∑ₜ βᵗP_σᵗ r_σ`. -/
theorem vσ_eq_tsum [DecidableEq X] (σ : X → A) :
    M.vσ σ = ∑' t : ℕ, M.β ^ t • (M.Pσ σ ^ t *ᵥ M.rσ σ) := by
  have hs := M.summable_pow_smul_mulVec σ
  have hlim := hs.hasSum.tendsto_sum_nat
  have hiter : (fun k : ℕ => ∑ t ∈ range k, M.β ^ t • (M.Pσ σ ^ t *ᵥ M.rσ σ)) =
      fun k => (M.Tσ σ)^[k] 0 := funext fun k => (M.iterate_Tσ_zero σ k).symm
  rw [hiter] at hlim
  exact tendsto_nhds_unique (M.tendsto_iterate_Tσ σ 0) hlim

/-- Exercise 5.1.6 (p. 135): if `|r| ≤ R` on the feasible pairs used by `σ`, then
`−R/(1 − β) ≤ v_σ ≤ R/(1 − β)`. -/
theorem abs_vσ_le (σ : X → A) {R : ℝ} (hR : ∀ x, |M.r x (σ x)| ≤ R) (x : X) :
    |M.vσ σ x| ≤ R / (1 - M.β) := by
  have hβ : 0 < 1 - M.β := by linarith [M.β_lt_one]
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (hR x)
  set C : ℝ := R / (1 - M.β) with hC
  have hCeq : R + M.β * C = C := by
    rw [hC]
    field_simp
    ring
  set S : Set (X → ℝ) := {v | ∀ y, |v y| ≤ C} with hS
  have hclosed : IsClosed S := by
    have : S = ⋂ y, {v : X → ℝ | |v y| ≤ C} := by ext; simp [hS]
    rw [this]
    exact isClosed_iInter fun y => isClosed_le (continuous_abs.comp (continuous_apply y))
      continuous_const
  have hmaps : ∀ v ∈ S, M.Tσ σ v ∈ S := by
    intro v hv y
    rw [Tσ_apply]
    calc |M.r y (σ y) + M.β * ∑ x', v x' * M.P y (σ y) x'|
        ≤ |M.r y (σ y)| + M.β * |∑ x', v x' * M.P y (σ y) x'| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_of_nonneg M.β_pos.le]
      _ ≤ R + M.β * C := by
          refine add_le_add (hR y) (mul_le_mul_of_nonneg_left ?_ M.β_pos.le)
          calc |∑ x', v x' * M.P y (σ y) x'| ≤ ∑ x', |v x'| * M.P y (σ y) x' := by
                refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x' _ => ?_)
                rw [abs_mul, abs_of_nonneg (M.P_nonneg y (σ y) x')]
            _ ≤ ∑ x', C * M.P y (σ y) x' := sum_le_sum fun x' _ =>
                mul_le_mul_of_nonneg_right (hv x') (M.P_nonneg y (σ y) x')
            _ = C := by rw [← mul_sum, M.P_rowsum, mul_one]
      _ = C := hCeq
  have hiter : ∀ k : ℕ, (M.Tσ σ)^[k] 0 ∈ S := by
    intro k
    induction k with
    | zero => intro y; simp only [iterate_zero, id, Pi.zero_apply, abs_zero]; positivity
    | succ k ih => rw [iterate_succ_apply']; exact hmaps _ ih
  exact hclosed.mem_of_tendsto (M.tendsto_iterate_Tσ σ 0) (Eventually.of_forall hiter) x

end MDP

end Miao.NumericalMethods.NP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimality: the Bellman operator, greedy policies and the algorithms

Copied from `FiniteStates/MarkovDecisionProcesses` (module `Bellman`), namespace renamed to
`Miao.NumericalMethods.NP`.

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §5.1.3.2–§5.1.4
(pp. 136–145).

The value function is `v* = ⋁_σ v_σ` over the finitely many feasible policies,
(5.21); `σ` is optimal if `v_σ = v*`. The Bellman operator (5.24) maximises the
action value over `Γ(x)`; a `v`-greedy policy attains that maximum, (5.22).
Exercises 5.1.10–5.1.12: the family `{T_σ v}` has least and greatest elements,
greedy policies exist and are exactly those with `T_σ v = Tv`, `T = ⋁_σ T_σ`,
and `T` is a contraction of modulus `β`. Proposition 5.1.1: `v*` is the unique
solution of the Bellman equation, `Tᵏv → v*`, Bellman's principle of
optimality holds, and an optimal policy exists (Exercise 5.1.13).

For the algorithms: Lemma 5.1.2 (`βP_σ` is a subgradient of `T` at `v` for a
`v`-greedy `σ`), the identity that makes Howard policy iteration a Newton step,
the monotone improvement step of HPI with its termination criterion, and the
observations that optimistic policy iteration with `m = 1` is VFI and that its
inner iterates converge to `v_σ` as `m → ∞`.
-/

namespace Miao.NumericalMethods.NP

open Finset Matrix Filter Topology Function

namespace MDP

variable {X A : Type*} [Fintype X] [Fintype A] (M : MDP X A)

/-- The Bellman operator (5.24): `(Tv)(x) = max_{a ∈ Γ(x)} {r(x, a) + β ∑ v(x')P(x, a, x')}`. -/
noncomputable def T (v : X → ℝ) : X → ℝ := fun x => (M.Γ x).sup' (M.Γ_nonempty x) (M.B v x)

theorem T_apply (v : X → ℝ) (x : X) :
    M.T v x = (M.Γ x).sup' (M.Γ_nonempty x) fun a => M.r x a + M.β * ∑ x', v x' * M.P x a x' := rfl

/-- `B(x, a, v) ≤ (Tv)(x)` for every feasible `a`. -/
theorem B_le_T (v : X → ℝ) {x : X} {a : A} (ha : a ∈ M.Γ x) : M.B v x a ≤ M.T v x :=
  Finset.le_sup' (M.B v x) ha

/-- `T_σ v ≤ Tv` for every feasible policy. -/
theorem Tσ_le_T (σ : M.Policy) (v : X → ℝ) : M.Tσ σ.1 v ≤ M.T v := fun x =>
  M.B_le_T v (σ.2 x)

/-- The action value is order preserving in `v`. -/
theorem B_mono {v v' : X → ℝ} (hvv' : v ≤ v') (x : X) (a : A) : M.B v x a ≤ M.B v' x a := by
  unfold B
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (sum_le_sum fun x' _ => ?_) M.β_pos.le)
  exact mul_le_mul_of_nonneg_right (hvv' x') (M.P_nonneg x a x')

/-- `T` is an order-preserving self-map on `ℝ^X`. -/
theorem T_monotone : Monotone M.T := by
  intro v v' hvv' x
  exact Finset.sup'_mono_fun fun a _ => M.B_mono hvv' x a

/-- `|B(x, a, v) − B(x, a, v')| ≤ β‖v − v'‖`. -/
theorem abs_B_sub_le (v v' : X → ℝ) (x : X) (a : A) : |M.B v x a - M.B v' x a| ≤ M.β * ‖v - v'‖ :=
  M.abs_Tσ_sub_le (fun _ => a) v v' x

/-- Exercise 5.1.12 (p. 137): `T` is a contraction of modulus `β` on `ℝ^X` under the supremum
norm. -/
theorem isContractionOn_T : IsContractionOn M.T Set.univ M.β where
  mapsTo := Set.mapsTo_univ _ _
  nonneg := M.β_pos.le
  lt_one := M.β_lt_one
  norm_sub_le v _ v' _ := by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg M.β_pos.le (norm_nonneg _))]
    intro x
    rw [Pi.sub_apply, Real.norm_eq_abs, T_apply, T_apply]
    refine (abs_sup'_sub_sup'_le _ _ _).trans (Finset.sup'_le _ _ fun a _ => ?_)
    exact M.abs_B_sub_le v v' x a

/-! ### Greedy policies (5.22) -/

/-- A `v`-greedy policy (5.22), p. 136: feasible, and `σ(x)` maximises the action value over
`Γ(x)`. -/
def IsGreedy (v : X → ℝ) (σ : X → A) : Prop :=
  M.IsFeasible σ ∧ ∀ x, ∀ a ∈ M.Γ x, M.B v x a ≤ M.B v x (σ x)

/-- A `v`-greedy policy, chosen by maximising the action value in each state. -/
noncomputable def greedy (v : X → ℝ) : X → A := fun x =>
  ((M.Γ x).exists_max_image (M.B v x) (M.Γ_nonempty x)).choose

theorem greedy_mem (v : X → ℝ) (x : X) : M.greedy v x ∈ M.Γ x :=
  ((M.Γ x).exists_max_image (M.B v x) (M.Γ_nonempty x)).choose_spec.1

/-- Exercise 5.1.11 (i), p. 137: a `v`-greedy policy exists. -/
theorem isGreedy_greedy (v : X → ℝ) : M.IsGreedy v (M.greedy v) :=
  ⟨M.greedy_mem v, fun x a ha =>
    ((M.Γ x).exists_max_image (M.B v x) (M.Γ_nonempty x)).choose_spec.2 a ha⟩

/-- The greedy policy as an element of `Σ`. -/
noncomputable def greedyPolicy (v : X → ℝ) : M.Policy := ⟨M.greedy v, M.greedy_mem v⟩

/-- Exercise 5.1.11 (ii), p. 137: a feasible `σ` is `v`-greedy iff `T_σ v = Tv`. -/
theorem isGreedy_iff_Tσ_eq_T (v : X → ℝ) (σ : M.Policy) :
    M.IsGreedy v σ.1 ↔ M.Tσ σ.1 v = M.T v := by
  constructor
  · rintro ⟨-, h⟩
    funext x
    exact le_antisymm (M.B_le_T v (σ.2 x)) (Finset.sup'_le _ _ fun a ha => h x a ha)
  · intro h
    refine ⟨σ.2, fun x a ha => ?_⟩
    have := congrFun h x
    rw [Tσ] at this
    rw [this]
    exact M.B_le_T v ha

/-- For a `v`-greedy `σ`, `T_σ v = Tv`. -/
theorem Tσ_eq_T_of_isGreedy {v : X → ℝ} {σ : X → A} (hσ : M.IsGreedy v σ) : M.Tσ σ v = M.T v :=
  (M.isGreedy_iff_Tσ_eq_T v ⟨σ, hσ.1⟩).1 hσ

/-- Exercise 5.1.11 (iii), p. 137: `(Tv)(x) = max_σ (T_σ v)(x)`, i.e. `T = ⋁_σ T_σ`. -/
theorem T_apply_eq_sup' [DecidableEq X] [DecidableEq A] (v : X → ℝ) (x : X) :
    M.T v x =
      univ.sup' (univ_nonempty_iff.2 M.policy_nonempty) fun σ : M.Policy => M.Tσ σ.1 v x := by
  apply le_antisymm
  · have h := congrFun (M.Tσ_eq_T_of_isGreedy (M.isGreedy_greedy v)) x
    rw [← h]
    exact Finset.le_sup' (fun σ : M.Policy => M.Tσ σ.1 v x) (mem_univ (M.greedyPolicy v))
  · exact Finset.sup'_le _ _ fun σ _ => M.Tσ_le_T σ v x

/-- Exercise 5.1.10 (p. 136), greatest element: `Tv` is the greatest element of `{T_σ v}_σ`. -/
theorem isGreatest_T (v : X → ℝ) : IsGreatest (Set.range fun σ : M.Policy => M.Tσ σ.1 v) (M.T v) :=
  ⟨⟨M.greedyPolicy v, M.Tσ_eq_T_of_isGreedy (M.isGreedy_greedy v)⟩, by
    rintro _ ⟨σ, rfl⟩
    exact M.Tσ_le_T σ v⟩

/-- The policy that minimises the action value in each state. -/
noncomputable def antiGreedy (v : X → ℝ) : X → A := fun x =>
  ((M.Γ x).exists_min_image (M.B v x) (M.Γ_nonempty x)).choose

theorem antiGreedy_mem (v : X → ℝ) (x : X) : M.antiGreedy v x ∈ M.Γ x :=
  ((M.Γ x).exists_min_image (M.B v x) (M.Γ_nonempty x)).choose_spec.1

/-- Exercise 5.1.10 (p. 136), least element: `{T_σ v}_σ` has a least element, the value of the
policy that minimises the action value in each state. -/
theorem isLeast_Tσ_antiGreedy (v : X → ℝ) :
    IsLeast (Set.range fun σ : M.Policy => M.Tσ σ.1 v) (M.Tσ (M.antiGreedy v) v) :=
  ⟨⟨⟨M.antiGreedy v, M.antiGreedy_mem v⟩, rfl⟩, by
    rintro _ ⟨σ, rfl⟩ x
    exact ((M.Γ x).exists_min_image (M.B v x) (M.Γ_nonempty x)).choose_spec.2 _ (σ.2 x)⟩

/-! ### The value function and Proposition 5.1.1 -/

variable [DecidableEq X] [DecidableEq A]

/-- The value function (5.21), p. 136: `v*(x) = max_{σ ∈ Σ} v_σ(x)`. -/
noncomputable def vstar : X → ℝ := fun x =>
  univ.sup' (univ_nonempty_iff.2 M.policy_nonempty) fun σ : M.Policy => M.vσ σ.1 x

/-- `v_σ ≤ v*` for every feasible policy. -/
theorem vσ_le_vstar (σ : M.Policy) : M.vσ σ.1 ≤ M.vstar := fun x =>
  Finset.le_sup' (fun σ : M.Policy => M.vσ σ.1 x) (mem_univ σ)

/-- An optimal policy (p. 136): a feasible `σ` with `v_σ = v*`. -/
def IsOptimal (σ : X → A) : Prop := M.IsFeasible σ ∧ M.vσ σ = M.vstar

/-- **Proposition 5.1.1 (i)**, existence half (pp. 137–138): `v*` is a fixed point of `T`. -/
theorem isFixedPt_T_vstar : IsFixedPt M.T M.vstar := by
  obtain ⟨vbar, -, hvbar⟩ := M.isContractionOn_T.exists_fixedPt isClosed_univ ⟨0, Set.mem_univ 0⟩
  -- `v̄ ≤ v*`: `v̄` is the value of its own greedy policy
  have h1 : vbar ≤ M.vstar := by
    have hfix : IsFixedPt (M.Tσ (M.greedy vbar)) vbar := by
      rw [IsFixedPt, M.Tσ_eq_T_of_isGreedy (M.isGreedy_greedy vbar)]
      exact hvbar
    rw [M.eq_vσ_of_isFixedPt _ hfix]
    exact M.vσ_le_vstar (M.greedyPolicy vbar)
  -- `v* ≤ v̄`: each `v_σ ≤ v̄` by Proposition 2.2.7, since `T_σ ≤ T`
  have h2 : M.vstar ≤ vbar := by
    intro x
    refine Finset.sup'_le _ _ fun σ _ => ?_
    exact fixedPt_le_of_le (M.Tσ_le_T σ) M.T_monotone (M.isFixedPt_vσ σ.1)
      (M.isContractionOn_T.tendsto_iterate_fixedPt (Set.mem_univ _) (Set.mem_univ _) hvbar) x
  have : M.vstar = vbar := le_antisymm h2 h1
  rw [this]
  exact hvbar

/-- Proposition 5.1.1 (i), uniqueness half: `v*` is the only fixed point of `T` in `ℝ^X`. -/
theorem eq_vstar_of_isFixedPt {v : X → ℝ} (hv : IsFixedPt M.T v) : v = M.vstar :=
  M.isContractionOn_T.fixedPt_unique (Set.mem_univ v) (Set.mem_univ _) hv M.isFixedPt_T_vstar

/-- The Bellman equation (5.2): `v*(x) = max_{a ∈ Γ(x)} {r(x, a) + β ∑ v*(x')P(x, a, x')}`,
with `v*` its unique solution (Proposition 5.1.1 (i)). -/
theorem bellman_equation (x : X) :
    M.vstar x = (M.Γ x).sup' (M.Γ_nonempty x) fun a =>
      M.r x a + M.β * ∑ x', M.vstar x' * M.P x a x' :=
  (congrFun M.isFixedPt_T_vstar.eq x).symm

/-- Proposition 5.1.1 (ii): `Tᵏv → v*` for all `v ∈ ℝ^X` (value function iteration, §5.1.4.1). -/
theorem tendsto_iterate_T (v : X → ℝ) : Tendsto (fun k : ℕ => M.T^[k] v) atTop (𝓝 M.vstar) :=
  M.isContractionOn_T.tendsto_iterate_fixedPt (Set.mem_univ v) (Set.mem_univ _) M.isFixedPt_T_vstar

theorem norm_iterate_T_sub_vstar_le (v : X → ℝ) (k : ℕ) :
    ‖M.T^[k] v - M.vstar‖ ≤ M.β ^ k * ‖v - M.vstar‖ :=
  M.isContractionOn_T.norm_iterate_sub_fixedPt_le (Set.mem_univ v) (Set.mem_univ _)
    M.isFixedPt_T_vstar k

omit [DecidableEq X] [DecidableEq A] in
/-- `T` is globally stable on `ℝ^X` (p. 137). -/
theorem globallyStable_T : GloballyStable M.T := M.isContractionOn_T.globallyStable_univ

/-- Optimality is `v_σ = v*` pointwise: `σ` is optimal iff it is feasible and `v_σ'(x) ≤ v_σ(x)` for
all feasible `σ'` and all `x`. -/
theorem isOptimal_iff (σ : X → A) :
    M.IsOptimal σ ↔
      M.IsFeasible σ ∧ ∀ (σ' : M.Policy) (x : X), M.vσ σ'.1 x ≤ M.vσ σ x := by
  constructor
  · rintro ⟨hσ, h⟩
    refine ⟨hσ, fun σ' x => ?_⟩
    rw [h]
    exact M.vσ_le_vstar σ' x
  · rintro ⟨hσ, h⟩
    refine ⟨hσ, funext fun x => le_antisymm (M.vσ_le_vstar ⟨σ, hσ⟩ x) ?_⟩
    exact Finset.sup'_le _ _ fun σ' _ => h σ' x

/-- **Proposition 5.1.1 (iii)**, Bellman's principle of optimality (p. 137), via (5.25):
`σ` is optimal iff it is `v*`-greedy. -/
theorem isOptimal_iff_isGreedy (σ : X → A) : M.IsOptimal σ ↔ M.IsGreedy M.vstar σ := by
  constructor
  · rintro ⟨hσ, h⟩
    rw [M.isGreedy_iff_Tσ_eq_T M.vstar ⟨σ, hσ⟩]
    -- `T_σ v* = T_σ v_σ = v_σ = v* = Tv*`
    rw [← h, (M.isFixedPt_vσ σ).eq, h, M.isFixedPt_T_vstar.eq]
  · intro h
    refine ⟨h.1, ?_⟩
    have hfix : IsFixedPt (M.Tσ σ) M.vstar := by
      rw [IsFixedPt, M.Tσ_eq_T_of_isGreedy h]
      exact M.isFixedPt_T_vstar
    exact (M.eq_vσ_of_isFixedPt σ hfix).symm

/-- Proposition 5.1.1 (iv), Exercise 5.1.13 (p. 139): an optimal policy exists, namely any
`v*`-greedy policy. -/
theorem isOptimal_greedy_vstar : M.IsOptimal (M.greedy M.vstar) :=
  (M.isOptimal_iff_isGreedy _).2 (M.isGreedy_greedy _)

theorem exists_isOptimal : ∃ σ : X → A, M.IsOptimal σ := ⟨_, M.isOptimal_greedy_vstar⟩

/-! ### Algorithms (§5.1.4) -/

omit [DecidableEq X] [DecidableEq A] in
/-- **Lemma 5.1.2** (p. 144): if `σ` is `v`-greedy then `βP_σ` is a subgradient of `T` at `v`:
`Tu ≥ Tv + βP_σ(u − v)` for all `u`. -/
theorem subgradient_of_isGreedy {v : X → ℝ} {σ : X → A} (hσ : M.IsGreedy v σ) (u : X → ℝ) :
    M.T v + M.β • (M.Pσ σ *ᵥ (u - v)) ≤ M.T u := by
  have h1 := M.Tσ_le_T ⟨σ, hσ.1⟩ u
  have h2 := M.Tσ_eq_T_of_isGreedy hσ
  rw [Tσ_eq] at h1 h2
  rw [← h2, mulVec_sub, smul_sub]
  intro x
  have := h1 x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
  linarith

omit [DecidableEq A] in
/-- HPI as Newton's method (p. 144): for a `v`-greedy `σ`, the Newton step
`Qv = (I − βP_σ)⁻¹(Tv − βP_σ v)` equals `(I − βP_σ)⁻¹ r_σ = v_σ`, the next value in HPI. -/
theorem newton_step_eq_vσ {v : X → ℝ} {σ : X → A} (hσ : M.IsGreedy v σ) :
    (1 - M.β • M.Pσ σ)⁻¹ *ᵥ (M.T v - M.β • (M.Pσ σ *ᵥ v)) = M.vσ σ := by
  rw [← M.Tσ_eq_T_of_isGreedy hσ, Tσ_eq, add_sub_cancel_right, M.vσ_eq_inv]

omit [DecidableEq X] [DecidableEq A] in
/-- Howard policy iteration (Algorithm 5.3), the improvement step: if `σ'` is `v_σ`-greedy then
`v_σ ≤ v_σ'`, since `v_σ = T_σ v_σ ≤ Tv_σ = T_σ' v_σ` and `T_σ'ᵏ v_σ → v_σ'`. -/
theorem vσ_le_vσ_of_isGreedy {σ : X → A} (hσ : M.IsFeasible σ) {σ' : X → A}
    (hσ' : M.IsGreedy (M.vσ σ) σ') : M.vσ σ ≤ M.vσ σ' := by
  have h : M.vσ σ ≤ M.Tσ σ' (M.vσ σ) := by
    rw [M.Tσ_eq_T_of_isGreedy hσ']
    calc M.vσ σ = M.Tσ σ (M.vσ σ) := (M.isFixedPt_vσ σ).eq.symm
      _ ≤ M.T (M.vσ σ) := M.Tσ_le_T ⟨σ, hσ⟩ _
  exact le_fixedPt_of_le_apply (M.Tσ_monotone σ') h (M.tendsto_iterate_Tσ σ' _)

/-- HPI, the termination criterion (Algorithm 5.3, line 6): if `σ'` is `v_σ`-greedy and
`v_σ' = v_σ`, then `σ'` is optimal. -/
theorem isOptimal_of_hpi_fixed {σ σ' : X → A} (hσ' : M.IsGreedy (M.vσ σ) σ')
    (heq : M.vσ σ' = M.vσ σ) : M.IsOptimal σ' := by
  have hfix : IsFixedPt M.T (M.vσ σ) := by
    rw [IsFixedPt, ← M.Tσ_eq_T_of_isGreedy hσ', ← heq]
    exact (M.isFixedPt_vσ σ').eq
  refine ⟨hσ'.1, ?_⟩
  rw [heq]
  exact M.eq_vstar_of_isFixedPt hfix

omit [DecidableEq X] [DecidableEq A] in
/-- Optimistic policy iteration (Algorithm 5.4) with `m = 1` is value function iteration: for a
`v`-greedy `σ`, `T_σ v = Tv` (p. 145). -/
theorem opi_one_step_eq_vfi {v : X → ℝ} {σ : X → A} (hσ : M.IsGreedy v σ) :
    (M.Tσ σ)^[1] v = M.T v := by
  rw [iterate_one]
  exact M.Tσ_eq_T_of_isGreedy hσ

omit [DecidableEq X] [DecidableEq A] in
/-- OPI approximates HPI as `m → ∞`: `T_σᵐ v → v_σ` (p. 145). -/
theorem tendsto_opi_inner (σ : X → A) (v : X → ℝ) :
    Tendsto (fun m : ℕ => (M.Tσ σ)^[m] v) atTop (𝓝 (M.vσ σ)) :=
  M.tendsto_iterate_Tσ σ v

end MDP

end Miao.NumericalMethods.NP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Discrete approximation methods for dynamic programming

Miao, *Economic Dynamics in Discrete Time*, §11.6.1 (pp. 377–380).

The stochastic growth model (11.9) is discretised on a capital grid
`K = {k₁, …, k_{n_k}}` and a Markov chain `(s_i, π_ij)` for `s = ln z`; the
discretised problem (11.10) is a finite Markov decision process with state
`(k_m, s_i)`, action `k' ∈ K`, reward `u(f(k_m, exp s_i) − k')` and transition
`(k', s_j)` with probability `π_ij`. We build this MDP (`GrowthGrid.toMDP`) and
prove, using the Sargent–Stachurski finite-MDP theory copied into `NPBasics`,
`NPMDP`, `NPBellman`:

* (11.11): the Bellman operator `B` of the MDP is the book's operator; it is a
  contraction of modulus `β`, so (11.10) has a unique solution `V = BV`
  (`eq_11_10`, `eq_11_10_unique`);
* value function iteration: `Bⁿ V₀ → V` with `‖V − Vₙ‖ ≤ βⁿ‖V − V₀‖`, and with
  `V₀ = 0` the iterate `Bⁿ 0` is the value of the `n`-period problem solved by
  backward induction (`np_vfi_backward_induction`);
* policy iteration: the policy evaluation system (11.12) has the unique
  solution `V_g = (I − βP_g)⁻¹ r_g`; the improvement step is monotone; both
  stopping rules (`gₙ = gₙ₋₁` or `Vₙ = Vₙ₋₁`) certify optimality; the
  algorithm stops after finitely many steps; and each step is the
  Newton–Kantorovich step for `F(V) = (I − B)V` (Puterman–Brumelle);
* modified policy iteration: `B̂ = T_{g₀}` is a `β`-contraction whose iterates
  converge to the solution of (11.12).

Abstract bounds used for the "truncation" and "projection" remarks:
`np_residual_bound` (`‖v − V‖ ≤ ‖v − Bv‖/(1 − β)`), `np_vfi_aposteriori` and
`np_fixedPt_perturbation`.

Departures: the book maximises over `k' ∈ K` without restricting consumption to
be positive; we follow (11.10) literally, the utility `u` being any real
function (feasibility restrictions can be built into `u`, e.g. a large penalty).
-/

namespace Miao.NumericalMethods.NP

open Finset Matrix Filter Topology Function

/-! ### Abstract contraction bounds -/

/-- Projection residual bound (Miao, p. 381, residual `R = V̂ − BV̂`): if `B` is a contraction of
modulus `β` with fixed point `V`, then `‖v − V‖ ≤ ‖v − Bv‖/(1 − β)` for every `v`. In particular a
zero residual identifies the true value function. -/
theorem np_residual_bound {E : Type*} [NormedAddCommGroup E] {B : E → E} {β : ℝ}
    (hB : IsContractionOn B Set.univ β) {V : E} (hV : IsFixedPt B V) (v : E) :
    ‖v - V‖ ≤ ‖v - B v‖ / (1 - β) := by
  have h1 : 0 < 1 - β := by linarith [hB.lt_one]
  have h2 : ‖B v - V‖ ≤ β * ‖v - V‖ := by
    have := hB.norm_sub_le v (Set.mem_univ _) V (Set.mem_univ _)
    rwa [hV.eq] at this
  have h3 : ‖v - V‖ ≤ ‖v - B v‖ + ‖B v - V‖ := by
    have := norm_add_le (v - B v) (B v - V)
    rwa [sub_add_sub_cancel] at this
  rw [le_div_iff₀ h1]
  nlinarith

/-- Miao, p. 381: the residual `R = v − Bv` vanishes iff `v` is the fixed point `V`. -/
theorem np_residual_zero_iff {E : Type*} [NormedAddCommGroup E] {B : E → E} {β : ℝ}
    (hB : IsContractionOn B Set.univ β) {V : E} (hV : IsFixedPt B V) (v : E) :
    v - B v = 0 ↔ v = V := by
  constructor
  · intro h
    exact hB.fixedPt_unique (Set.mem_univ v) (Set.mem_univ V) (sub_eq_zero.1 h).symm hV
  · rintro rfl
    rw [hV.eq, sub_self]

/-- A posteriori bound for value function iteration: `‖Bv − V‖ ≤ β/(1 − β) ‖Bv − v‖`, which
justifies stopping when successive iterates are close. -/
theorem np_vfi_aposteriori {E : Type*} [NormedAddCommGroup E] {B : E → E} {β : ℝ}
    (hB : IsContractionOn B Set.univ β) {V : E} (hV : IsFixedPt B V) (v : E) :
    ‖B v - V‖ ≤ β / (1 - β) * ‖B v - v‖ := by
  have h := np_residual_bound hB hV (B v)
  have h2 : ‖B v - B (B v)‖ ≤ β * ‖v - B v‖ :=
    hB.norm_sub_le v (Set.mem_univ _) (B v) (Set.mem_univ _)
  have h1 : 0 < 1 - β := by linarith [hB.lt_one]
  rw [norm_sub_rev v] at h2
  calc ‖B v - V‖ ≤ ‖B v - B (B v)‖ / (1 - β) := h
    _ ≤ β * ‖B v - v‖ / (1 - β) := div_le_div_of_nonneg_right h2 h1.le
    _ = β / (1 - β) * ‖B v - v‖ := by ring

/-- Approximation of the Bellman operator (Miao, p. 377: "as long as the truncated state space is
sufficiently large, the truncated problem can approximate the original problem arbitrarily
closely"): if two `β`-contractions are uniformly within `ε`, their fixed points are within
`ε/(1 − β)`. -/
theorem np_fixedPt_perturbation {E : Type*} [NormedAddCommGroup E] {B B' : E → E} {β ε : ℝ}
    (hB : IsContractionOn B Set.univ β) (hB' : IsContractionOn B' Set.univ β)
    {V V' : E} (hV : IsFixedPt B V) (hV' : IsFixedPt B' V') (hε : ∀ v, ‖B v - B' v‖ ≤ ε) :
    ‖V - V'‖ ≤ ε / (1 - β) := by
  have h1 : 0 < 1 - β := by linarith [hB.lt_one]
  have h2 : ‖B' V - B' V'‖ ≤ β * ‖V - V'‖ :=
    hB'.norm_sub_le V (Set.mem_univ _) V' (Set.mem_univ _)
  have h3 : ‖B V - B' V'‖ ≤ ‖B V - B' V‖ + ‖B' V - B' V'‖ := by
    have := norm_add_le (B V - B' V) (B' V - B' V')
    rwa [sub_add_sub_cancel] at this
  have h4 : ‖V - V'‖ = ‖B V - B' V'‖ := by rw [hV.eq, hV'.eq]
  rw [le_div_iff₀ h1]
  nlinarith [hε V]

/-! ### Extra facts on finite MDPs: backward induction and termination of policy iteration -/

namespace MDP

variable {X A : Type*} [Fintype X] [Fintype A] (M : MDP X A)

/-- The `k`-period payoff of the (possibly time-varying) plan `σ₀, σ₁, …` with zero terminal value,
computed by backward induction: `J₀ = 0`, `J_{k+1}(σ) = T_{σ₀} J_k(σ₁, σ₂, …)`. -/
noncomputable def np_horizonValue : ℕ → (ℕ → X → A) → X → ℝ
  | 0, _ => 0
  | k + 1, σ => M.Tσ (σ 0) (np_horizonValue k fun t => σ (t + 1))

/-- A stationary plan's `k`-period payoff is `T_σᵏ 0`. -/
theorem np_horizonValue_const (σ : X → A) (k : ℕ) :
    M.np_horizonValue k (fun _ => σ) = (M.Tσ σ)^[k] 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', ← ih]
    rfl

/-- Backward induction: `Tᵏ 0` is the value of the `k`-period problem, i.e. it bounds the payoff of
every feasible plan and is attained by a feasible plan. -/
theorem np_iterate_T_zero_eq_max (k : ℕ) :
    (∀ σ : ℕ → X → A, (∀ t, M.IsFeasible (σ t)) → M.np_horizonValue k σ ≤ M.T^[k] 0) ∧
      ∃ σ : ℕ → X → A, (∀ t, M.IsFeasible (σ t)) ∧ M.np_horizonValue k σ = M.T^[k] 0 := by
  induction k with
  | zero =>
    refine ⟨fun σ _ => le_rfl, fun _ => M.defaultPolicy.1, fun _ => M.defaultPolicy.2, rfl⟩
  | succ k ih =>
    obtain ⟨hle, σ', hσ', heq⟩ := ih
    refine ⟨fun σ hσ => ?_, ?_⟩
    · rw [iterate_succ_apply']
      calc M.np_horizonValue (k + 1) σ
          = M.Tσ (σ 0) (M.np_horizonValue k fun t => σ (t + 1)) := rfl
        _ ≤ M.Tσ (σ 0) (M.T^[k] 0) := M.Tσ_monotone _ (hle _ fun t => hσ (t + 1))
        _ ≤ M.T (M.T^[k] 0) := M.Tσ_le_T ⟨σ 0, hσ 0⟩ _
    · let g := M.greedy (M.T^[k] 0)
      refine ⟨fun t => if t = 0 then g else σ' (t - 1), fun t => ?_, ?_⟩
      · by_cases ht : t = 0
        · simp only [ht, ↓reduceIte]
          exact M.greedy_mem _
        · simp only [ht, ↓reduceIte]
          exact hσ' _
      · have hshift : (fun t => (fun t => if t = 0 then g else σ' (t - 1)) (t + 1)) = σ' := by
          funext t
          simp
        rw [iterate_succ_apply', ← M.Tσ_eq_T_of_isGreedy (M.isGreedy_greedy (M.T^[k] 0))]
        change M.Tσ (if (0 : ℕ) = 0 then g else σ' (0 - 1)) (M.np_horizonValue k _) = _
        rw [hshift, heq]
        rfl

/-- Howard policy iteration started at `σ₀`: `σ_{n+1}` is `v_{σₙ}`-greedy. -/
noncomputable def np_hpi (σ0 : X → A) : ℕ → X → A
  | 0 => σ0
  | n + 1 => M.greedy (M.vσ (np_hpi σ0 n))

theorem np_hpi_feasible {σ0 : X → A} (h0 : M.IsFeasible σ0) (n : ℕ) :
    M.IsFeasible (M.np_hpi σ0 n) := by
  cases n with
  | zero => exact h0
  | succ n => exact M.greedy_mem _

/-- Policy iteration is monotone: `v_{σₙ} ≤ v_{σₙ₊₁}`. -/
theorem np_hpi_mono {σ0 : X → A} (h0 : M.IsFeasible σ0) (n : ℕ) :
    M.vσ (M.np_hpi σ0 n) ≤ M.vσ (M.np_hpi σ0 (n + 1)) :=
  M.vσ_le_vσ_of_isGreedy (M.np_hpi_feasible h0 n) (M.isGreedy_greedy _)

/-- Policy iteration stops after finitely many steps: some `n` has `v_{σₙ₊₁} = v_{σₙ}` (the
values increase and there are finitely many policies). -/
theorem np_hpi_terminates {σ0 : X → A} (h0 : M.IsFeasible σ0) :
    ∃ n, M.vσ (M.np_hpi σ0 (n + 1)) = M.vσ (M.np_hpi σ0 n) := by
  by_contra hcon
  simp only [not_exists] at hcon
  have hsm : StrictMono fun n => M.vσ (M.np_hpi σ0 n) :=
    strictMono_nat_of_lt_succ fun n => lt_of_le_of_ne (M.np_hpi_mono h0 n) (Ne.symm (hcon n))
  have hfin : (Set.range fun n => M.vσ (M.np_hpi σ0 n)).Finite :=
    (Set.finite_range fun p : M.Policy => M.vσ p.1).subset (by
      rintro _ ⟨n, rfl⟩
      exact ⟨⟨_, M.np_hpi_feasible h0 n⟩, rfl⟩)
  exact Set.infinite_range_of_injective hsm.injective hfin

end MDP

/-! ### The discretised stochastic growth model (11.10) -/

/-- The data of the discretised growth model (11.10), Miao p. 378: a capital grid `k_m`, a
Markov chain `(s_i, π_ij)` for `s = ln z`, utility `u`, technology `f(k, z)` and `β ∈ (0, 1)`. -/
structure GrowthGrid (nk nz : ℕ) where
  kgrid : Fin nk → ℝ
  sgrid : Fin nz → ℝ
  pz : Matrix (Fin nz) (Fin nz) ℝ
  pz_markov : IsMarkov pz
  u : ℝ → ℝ
  f : ℝ → ℝ → ℝ
  β : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1

namespace GrowthGrid

variable {nk nz : ℕ} [NeZero nk] (G : GrowthGrid nk nz)

/-- The reward `u(f(k_m, exp s_i) − k')` of choosing grid point `k'` in state `(k_m, s_i)`. -/
noncomputable def reward (x : Fin nk × Fin nz) (a : Fin nk) : ℝ :=
  G.u (G.f (G.kgrid x.1) (Real.exp (G.sgrid x.2)) - G.kgrid a)

/-- The transition: next state `(k', s_j)` with probability `π_ij`. -/
def trans (x : Fin nk × Fin nz) (a : Fin nk) (y : Fin nk × Fin nz) : ℝ :=
  if y.1 = a then G.pz x.2 y.2 else 0

omit [NeZero nk] in
theorem trans_rowsum (x : Fin nk × Fin nz) (a : Fin nk) : ∑ y, G.trans x a y = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [trans]
  rw [Finset.sum_comm]
  simp [G.pz_markov.rowsum]

omit [NeZero nk] in
theorem trans_nonneg (x : Fin nk × Fin nz) (a : Fin nk) (y : Fin nk × Fin nz) :
    0 ≤ G.trans x a y := by
  unfold trans
  split_ifs
  · exact G.pz_markov.nonneg _ _
  · exact le_rfl

/-- The discretised dynamic programming problem (11.10) as a finite MDP on `K × S`. -/
noncomputable def toMDP : MDP (Fin nk × Fin nz) (Fin nk) where
  Γ := fun _ => Finset.univ
  Γ_nonempty := fun _ => Finset.univ_nonempty
  β := G.β
  β_pos := G.β_pos
  β_lt_one := G.β_lt_one
  r := G.reward
  P := G.trans
  P_nonneg := G.trans_nonneg
  P_rowsum := G.trans_rowsum

theorem toMDP_β : G.toMDP.β = G.β := rfl

/-- Every policy `g : K × S → K` is feasible. -/
theorem isFeasible (g : Fin nk × Fin nz → Fin nk) : G.toMDP.IsFeasible g :=
  fun _ => Finset.mem_univ _

/-- The action value of (11.10)–(11.11): the continuation is `∑_j π_ij v(k', s_j)`. -/
theorem B_apply (v : Fin nk × Fin nz → ℝ) (m : Fin nk) (i : Fin nz) (a : Fin nk) :
    G.toMDP.B v (m, i) a =
      G.u (G.f (G.kgrid m) (Real.exp (G.sgrid i)) - G.kgrid a) +
        G.β * ∑ j, G.pz i j * v (a, j) := by
  have h : ∑ y, v y * G.trans (m, i) a y = ∑ j, G.pz i j * v (a, j) := by
    rw [Fintype.sum_prod_type]
    simp only [trans]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [mul_comm]
  change G.reward (m, i) a + G.β * ∑ y, v y * G.trans (m, i) a y = _
  rw [h]
  rfl

/-- **(11.11)** (Miao, p. 378): the Bellman operator of the discretised problem is
`Bv(k_m, s_i) = max_{k' ∈ K} {u(f(k_m, exp s_i) − k') + β ∑_j π_ij v(k', s_j)}`. -/
theorem eq_11_11 (v : Fin nk × Fin nz → ℝ) (m : Fin nk) (i : Fin nz) :
    G.toMDP.T v (m, i) =
      Finset.univ.sup' Finset.univ_nonempty fun a : Fin nk =>
        G.u (G.f (G.kgrid m) (Real.exp (G.sgrid i)) - G.kgrid a) +
          G.β * ∑ j, G.pz i j * v (a, j) := by
  change Finset.univ.sup' _ (G.toMDP.B v (m, i)) = _
  congr 1
  funext a
  exact G.B_apply v m i a

/-- Miao, p. 378: the Bellman operator (11.11) is a contraction of modulus `β` in the supremum
norm ("the contraction mapping theorem ensures that there is a unique fixed point"). -/
theorem np_bellman_contraction : IsContractionOn G.toMDP.T Set.univ G.β :=
  G.toMDP.isContractionOn_T

variable [DecidableEq (Fin nk × Fin nz)]

/-- **(11.10)** (Miao, p. 378): the value function `V = v*` of the discretised problem satisfies
`V(k_m, s_i) = max_{k' ∈ K} {u(f(k_m, exp s_i) − k') + β ∑_j π_ij V(k', s_j)}`. -/
theorem eq_11_10 (m : Fin nk) (i : Fin nz) :
    G.toMDP.vstar (m, i) =
      Finset.univ.sup' Finset.univ_nonempty fun a : Fin nk =>
        G.u (G.f (G.kgrid m) (Real.exp (G.sgrid i)) - G.kgrid a) +
          G.β * ∑ j, G.pz i j * G.toMDP.vstar (a, j) := by
  rw [← eq_11_11]
  exact (congrFun G.toMDP.isFixedPt_T_vstar.eq (m, i)).symm

/-- (11.10), uniqueness (Miao, p. 378): any solution of (11.10) is `v*`. -/
theorem eq_11_10_unique {V : Fin nk × Fin nz → ℝ}
    (hV : ∀ m i, V (m, i) =
      Finset.univ.sup' Finset.univ_nonempty fun a : Fin nk =>
        G.u (G.f (G.kgrid m) (Real.exp (G.sgrid i)) - G.kgrid a) +
          G.β * ∑ j, G.pz i j * V (a, j)) :
    V = G.toMDP.vstar := by
  refine G.toMDP.eq_vstar_of_isFixedPt ?_
  funext x
  rw [eq_11_11, hV x.1 x.2]

/-- Value function iteration (Miao, p. 378): `Vₙ = Bⁿ V₀ → V` for any initial guess. -/
theorem np_vfi_tendsto (V0 : Fin nk × Fin nz → ℝ) :
    Tendsto (fun n : ℕ => G.toMDP.T^[n] V0) atTop (𝓝 G.toMDP.vstar) :=
  G.toMDP.tendsto_iterate_T V0

/-- Value function iteration converges at a geometric rate (Miao, p. 378):
`‖Vₙ − V‖ ≤ βⁿ ‖V₀ − V‖`. -/
theorem np_vfi_geometric (V0 : Fin nk × Fin nz → ℝ) (n : ℕ) :
    ‖G.toMDP.T^[n] V0 - G.toMDP.vstar‖ ≤ G.β ^ n * ‖V0 - G.toMDP.vstar‖ :=
  G.toMDP.norm_iterate_T_sub_vstar_le V0 n

omit [DecidableEq (Fin nk × Fin nz)] in
/-- Miao, p. 378: with `V₀ = 0`, value function iteration is backward induction on the
approximate finite-horizon problem: `Bⁿ 0` bounds the `n`-period payoff of every plan and is
attained by a plan. -/
theorem np_vfi_backward_induction (n : ℕ) :
    (∀ σ : ℕ → Fin nk × Fin nz → Fin nk, G.toMDP.np_horizonValue n σ ≤ G.toMDP.T^[n] 0) ∧
      ∃ σ : ℕ → Fin nk × Fin nz → Fin nk, G.toMDP.np_horizonValue n σ = G.toMDP.T^[n] 0 := by
  obtain ⟨h1, σ, -, h2⟩ := G.toMDP.np_iterate_T_zero_eq_max n
  exact ⟨fun σ => h1 σ fun t => G.isFeasible (σ t), σ, h2⟩

omit [DecidableEq (Fin nk × Fin nz)] in
/-- **(11.12)** (Miao, p. 379), policy evaluation: the value `V_g` of a stationary rule `g`
solves `V(k_m, s_i) = u(f(k_m, exp s_i) − g(k_m, s_i)) + β ∑_j π_ij V(g(k_m, s_i), s_j)`. -/
theorem eq_11_12 (g : Fin nk × Fin nz → Fin nk) (m : Fin nk) (i : Fin nz) :
    G.toMDP.vσ g (m, i) =
      G.u (G.f (G.kgrid m) (Real.exp (G.sgrid i)) - G.kgrid (g (m, i))) +
        G.β * ∑ j, G.pz i j * G.toMDP.vσ g (g (m, i), j) := by
  rw [← G.B_apply]
  exact (congrFun (G.toMDP.isFixedPt_vσ g).eq (m, i)).symm

omit [DecidableEq (Fin nk × Fin nz)] in
/-- (11.12), uniqueness: the linear system (11.12) has exactly one solution, `V_g`. -/
theorem eq_11_12_unique (g : Fin nk × Fin nz → Fin nk) {V : Fin nk × Fin nz → ℝ}
    (hV : ∀ m i, V (m, i) =
      G.u (G.f (G.kgrid m) (Real.exp (G.sgrid i)) - G.kgrid (g (m, i))) +
        G.β * ∑ j, G.pz i j * V (g (m, i), j)) :
    V = G.toMDP.vσ g := by
  refine G.toMDP.eq_vσ_of_isFixedPt g ?_
  funext x
  change G.toMDP.B V x (g x) = V x
  rw [G.B_apply, hV x.1 x.2]

/-- (11.12) solved as a linear system: `V_g = (I − βP_g)⁻¹ r_g`. -/
theorem eq_11_12_inv (g : Fin nk × Fin nz → Fin nk) :
    G.toMDP.vσ g = (1 - G.β • G.toMDP.Pσ g)⁻¹ *ᵥ G.toMDP.rσ g :=
  G.toMDP.vσ_eq_inv g

omit [DecidableEq (Fin nk × Fin nz)] in
/-- Policy improvement (Miao, p. 379): if `g₁` is greedy with respect to `V_{g₀}` (the arg max
step), then `V_{g₀} ≤ V_{g₁}`. -/
theorem np_pfi_improvement (g0 : Fin nk × Fin nz → Fin nk) :
    G.toMDP.vσ g0 ≤ G.toMDP.vσ (G.toMDP.greedy (G.toMDP.vσ g0)) :=
  G.toMDP.vσ_le_vσ_of_isGreedy (G.isFeasible g0) (G.toMDP.isGreedy_greedy _)

/-- Miao, p. 379, the stopping rule `gₙ = gₙ₋₁`: if `g` is greedy with respect to its own value
`V_g`, then `V_g` satisfies the Bellman equation (11.10), so `V_g = v*` and `g` is optimal. -/
theorem np_pfi_stop_policy {g : Fin nk × Fin nz → Fin nk}
    (hg : G.toMDP.IsGreedy (G.toMDP.vσ g) g) :
    G.toMDP.vσ g = G.toMDP.vstar ∧ G.toMDP.IsOptimal g :=
  ⟨(G.toMDP.isOptimal_of_hpi_fixed hg rfl).2, G.toMDP.isOptimal_of_hpi_fixed hg rfl⟩

/-- Miao, p. 379, the alternative stopping rule `Vₙ = Vₙ₋₁`: if `g'` is greedy with respect to
`V_g` and `V_{g'} = V_g`, then `g'` is optimal. -/
theorem np_pfi_stop_value {g g' : Fin nk × Fin nz → Fin nk}
    (hg' : G.toMDP.IsGreedy (G.toMDP.vσ g) g') (heq : G.toMDP.vσ g' = G.toMDP.vσ g) :
    G.toMDP.IsOptimal g' :=
  G.toMDP.isOptimal_of_hpi_fixed hg' heq

/-- Optimality (Miao, p. 379, "it is optimal"): the value `v*` dominates the value of every
stationary rule. -/
theorem np_vstar_ge (g : Fin nk × Fin nz → Fin nk) : G.toMDP.vσ g ≤ G.toMDP.vstar :=
  G.toMDP.vσ_le_vstar ⟨g, G.isFeasible g⟩

/-- Policy iteration terminates (Miao, p. 379, "until the first iteration `n` such that
`gₙ = gₙ₋₁` (or alternatively `Vₙ = Vₙ₋₁`)"): from any initial rule there is an `n` at which the
value stops changing, and the rule reached is optimal. -/
theorem np_pfi_terminates (g0 : Fin nk × Fin nz → Fin nk) :
    ∃ n, G.toMDP.vσ (G.toMDP.np_hpi g0 (n + 1)) = G.toMDP.vσ (G.toMDP.np_hpi g0 n) ∧
      G.toMDP.IsOptimal (G.toMDP.np_hpi g0 (n + 1)) := by
  obtain ⟨n, hn⟩ := G.toMDP.np_hpi_terminates (G.isFeasible g0)
  exact ⟨n, hn, G.toMDP.isOptimal_of_hpi_fixed (G.toMDP.isGreedy_greedy _) hn⟩

/-- Puterman–Brumelle (Miao, p. 379): policy iteration is the Newton–Kantorovich method for
`F(V) = (I − B)V`. If `g` is `V`-greedy, the next policy value is the Newton step with the
Jacobian `I − βP_g` of `F` along `g`: `V_g = V − (I − βP_g)⁻¹ (V − BV)`. -/
theorem np_pfi_newton {V : Fin nk × Fin nz → ℝ} {g : Fin nk × Fin nz → Fin nk}
    (hg : G.toMDP.IsGreedy V g) :
    G.toMDP.vσ g = V - (1 - G.β • G.toMDP.Pσ g)⁻¹ *ᵥ (V - G.toMDP.T V) := by
  rw [← toMDP_β]
  have hunit := G.toMDP.isUnit_one_sub_smul_Pσ g
  have hdet : IsUnit (1 - G.toMDP.β • G.toMDP.Pσ g).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 hunit
  have hV : V = (1 - G.toMDP.β • G.toMDP.Pσ g)⁻¹ *ᵥ ((1 - G.toMDP.β • G.toMDP.Pσ g) *ᵥ V) := by
    rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, one_mulVec]
  have key : (1 - G.toMDP.β • G.toMDP.Pσ g) *ᵥ V - (V - G.toMDP.T V) =
      G.toMDP.T V - G.toMDP.β • (G.toMDP.Pσ g *ᵥ V) := by
    rw [sub_mulVec, one_mulVec, smul_mulVec]
    abel
  rw [← G.toMDP.newton_step_eq_vσ hg, ← key, mulVec_sub, ← hV]

/-- Projection on the value function (Miao, p. 381): for any approximation `V̂` of the solution of
(11.10), `‖V̂ − V‖ ≤ ‖R‖/(1 − β)` with the residual `R = V̂ − BV̂`; a zero residual gives
`V̂ = V`. -/
theorem np_value_projection (Vh : Fin nk × Fin nz → ℝ) :
    ‖Vh - G.toMDP.vstar‖ ≤ ‖Vh - G.toMDP.T Vh‖ / (1 - G.β) ∧
      (Vh - G.toMDP.T Vh = 0 ↔ Vh = G.toMDP.vstar) :=
  ⟨np_residual_bound G.np_bellman_contraction G.toMDP.isFixedPt_T_vstar Vh,
    np_residual_zero_iff G.np_bellman_contraction G.toMDP.isFixedPt_T_vstar Vh⟩

omit [DecidableEq (Fin nk × Fin nz)] in
/-- Modified policy iteration (Miao, p. 379): the operator `B̂ V = r_{g₀} + βP_{g₀} V` is a
contraction of modulus `β` whose unique fixed point is the solution `V_{g₀}` of (11.12), and its
iterates converge to it. -/
theorem np_mpi (g0 : Fin nk × Fin nz → Fin nk) :
    IsContractionOn (G.toMDP.Tσ g0) Set.univ G.β ∧ IsFixedPt (G.toMDP.Tσ g0) (G.toMDP.vσ g0) ∧
      ∀ V0, Tendsto (fun n : ℕ => (G.toMDP.Tσ g0)^[n] V0) atTop (𝓝 (G.toMDP.vσ g0)) :=
  ⟨G.toMDP.isContractionOn_Tσ g0, G.toMDP.isFixedPt_vσ g0, G.toMDP.tendsto_iterate_Tσ g0⟩

end GrowthGrid

/-- A concrete discretised growth model (one grid point, one shock state, `β = 1/2`), showing the
data of `GrowthGrid` can be met. -/
noncomputable def np_growthGridExample : GrowthGrid 1 1 where
  kgrid := fun _ => 1
  sgrid := fun _ => 0
  pz := fun _ _ => 1
  pz_markov := ⟨fun _ _ => zero_le_one, fun _ => by simp⟩
  u := id
  f := fun k z => z * k
  β := 1 / 2
  β_pos := by norm_num
  β_lt_one := by norm_num

/-- The example's value function solves (11.10): `V = 0 + (1/2)V`, so `V = 0`. -/
theorem np_growthGridExample_vstar :
    np_growthGridExample.toMDP.vstar (0, 0) = 0 := by
  have h := GrowthGrid.eq_11_10 np_growthGridExample 0 0
  simp only [Finset.univ_unique, Finset.sup'_singleton, Fin.default_eq_zero,
    Finset.sum_singleton] at h
  generalize np_growthGridExample.toMDP.vstar (0, 0) = V at h ⊢
  simp [np_growthGridExample] at h
  linarith

end Miao.NumericalMethods.NP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Smooth approximation: value function interpolation

Miao, *Economic Dynamics in Discrete Time*, §11.6.2 (pp. 380–381).

Value function interpolation (Steps 1–4, p. 380): values `V(k_m, s_i)` on a
capital grid are interpolated to `V̂(k', s_j)` on `[k_min, k_max]`, and Step 3
computes `V₁(k_m, s_i) = sup_{k' ∈ [k_min, k_max]} {u(f(k_m, exp s_i) − k')
+ β ∑_j π_ij V̂₀(k', s_j)}`. We write the interpolant in the form
`V̂(k', s_j) = ∑_m w_m(k') V(k_m, s_j)` with weights `w_m(k') ≥ 0` summing to one
on `[k_min, k_max]` (an "averager", e.g. piecewise linear interpolation; we prove
that the two-node linear interpolation weights qualify). Under this
shape-preserving interpolation the fitted Bellman operator is a contraction of
modulus `β` (Blackwell), so the iteration of Step 4 converges to a unique fixed
point from any initial guess (`np_fitted_contraction`, `np_fitted_converges`).

The book does not state a convergence result for this method ("keep iterating
until convergence"); the theorem above is the one that makes the step sound.
Interpolation schemes that are not averagers (cubic splines, Chebyshev
interpolation) need not give a contraction; that remark is not formalised.
The projection variant (p. 381, residual `R = V̂ − BV̂`) is covered by the
abstract `np_residual_bound` and `np_residual_zero_iff` in `NPDiscreteDP`.
-/

namespace Miao.NumericalMethods.NP

open Finset Filter Topology Function

/-- The data of value function interpolation (Miao, p. 380): capital interval `[k_min, k_max]`,
capital grid, Markov chain for `s = ln z`, utility, technology, discount factor, and interpolation
weights `w_m(k')` that are nonnegative and sum to one on `[k_min, k_max]`; the period utility is
bounded above on the choice interval. -/
structure FittedGrid (nk nz : ℕ) where
  kmin : ℝ
  kmax : ℝ
  kmin_le : kmin ≤ kmax
  kgrid : Fin nk → ℝ
  sgrid : Fin nz → ℝ
  pz : Matrix (Fin nz) (Fin nz) ℝ
  pz_markov : IsMarkov pz
  u : ℝ → ℝ
  f : ℝ → ℝ → ℝ
  β : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1
  wt : ℝ → Fin nk → ℝ
  wt_nonneg : ∀ k ∈ Set.Icc kmin kmax, ∀ m, 0 ≤ wt k m
  wt_sum : ∀ k ∈ Set.Icc kmin kmax, ∑ m, wt k m = 1
  u_bdd : ∀ x : Fin nk × Fin nz,
    BddAbove (Set.range fun k : Set.Icc kmin kmax => u (f (kgrid x.1) (Real.exp (sgrid x.2)) - k))

namespace FittedGrid

variable {nk nz : ℕ} (G : FittedGrid nk nz)

/-- The interpolated continuation `∑_j π_ij V̂(k', s_j)` with
`V̂(k', s_j) = ∑_m w_m(k') V(k_m, s_j)`
(Steps 2–3, p. 380). -/
noncomputable def cont (V : Fin nk × Fin nz → ℝ) (i : Fin nz) (k : ℝ) : ℝ :=
  ∑ j, G.pz i j * ∑ m, G.wt k m * V (m, j)

/-- The objective of Step 3 at choice `k'`. -/
noncomputable def obj (V : Fin nk × Fin nz → ℝ) (x : Fin nk × Fin nz) (k : Set.Icc G.kmin G.kmax) :
    ℝ :=
  G.u (G.f (G.kgrid x.1) (Real.exp (G.sgrid x.2)) - k) + G.β * G.cont V x.2 k

/-- Step 3 (Miao, p. 380): `V₁(k_m, s_i) = sup_{k' ∈ [k_min, k_max]} {u(f(k_m, exp s_i) − k') +
β ∑_j π_ij V̂₀(k', s_j)}`. -/
noncomputable def fittedBellman (V : Fin nk × Fin nz → ℝ) : Fin nk × Fin nz → ℝ :=
  fun x => ⨆ k : Set.Icc G.kmin G.kmax, G.obj V x k

theorem cont_mono {V W : Fin nk × Fin nz → ℝ} (h : V ≤ W) (i : Fin nz) (k : Set.Icc G.kmin G.kmax) :
    G.cont V i k ≤ G.cont W i k := by
  unfold cont
  refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (G.pz_markov.nonneg i j)
  exact Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (h (m, j)) (G.wt_nonneg k k.2 m)

theorem cont_add_const (V : Fin nk × Fin nz → ℝ) (c : ℝ) (i : Fin nz)
    (k : Set.Icc G.kmin G.kmax) : G.cont (V + fun _ => c) i k = G.cont V i k + c := by
  unfold cont
  have h1 : ∀ j, ∑ m, G.wt k m * (V + fun _ : Fin nk × Fin nz => c) (m, j) =
      ∑ m, G.wt k m * V (m, j) + c := by
    intro j
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, G.wt_sum k k.2,
      one_mul]
  simp only [h1, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, G.pz_markov.rowsum, one_mul]

theorem cont_le_norm (V : Fin nk × Fin nz → ℝ) (i : Fin nz) (k : Set.Icc G.kmin G.kmax) :
    G.cont V i k ≤ ‖V‖ := by
  have hV : V ≤ fun _ => ‖V‖ := fun y => by
    have := norm_le_pi_norm V y
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  have h := G.cont_mono hV i k
  have h0 := G.cont_add_const 0 ‖V‖ i k
  have hz : G.cont 0 i k = 0 := by simp [cont]
  rw [zero_add, hz, zero_add] at h0
  exact h.trans h0.le

theorem bddAbove_obj (V : Fin nk × Fin nz → ℝ) (x : Fin nk × Fin nz) :
    BddAbove (Set.range (G.obj V x)) := by
  obtain ⟨Mu, hMu⟩ := G.u_bdd x
  refine ⟨Mu + G.β * ‖V‖, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact add_le_add (hMu ⟨k, rfl⟩)
    (mul_le_mul_of_nonneg_left (G.cont_le_norm V x.2 k) G.β_pos.le)

/-- Value function interpolation with an averaging (shape-preserving) interpolant: the fitted
Bellman operator of Steps 2–3 (Miao, p. 380) is a contraction of modulus `β` in the supremum
norm. -/
theorem np_fitted_contraction : IsContractionOn G.fittedBellman Set.univ G.β := by
  have hne : Nonempty (Set.Icc G.kmin G.kmax) := ⟨⟨G.kmin, Set.left_mem_Icc.2 G.kmin_le⟩⟩
  refine isContractionOn_of_blackwell G.β_pos.le G.β_lt_one ?_ ?_
  · intro V W h x
    exact ciSup_mono (G.bddAbove_obj W x) fun k =>
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (G.cont_mono h x.2 k) G.β_pos.le)
  · intro V c _ x
    refine ciSup_le fun k => ?_
    have h1 : G.obj (V + fun _ => c) x k = G.obj V x k + G.β * c := by
      simp only [obj, G.cont_add_const]
      ring
    rw [h1, Pi.add_apply]
    exact add_le_add (le_ciSup (G.bddAbove_obj V x) k) le_rfl

/-- Step 4 (Miao, p. 380), "keep iterating until convergence": the fitted Bellman operator has a
unique fixed point and its iterates converge to it from every initial guess `V₀`. -/
theorem np_fitted_converges :
    ∃ V : Fin nk × Fin nz → ℝ, IsFixedPt G.fittedBellman V ∧
      (∀ W, IsFixedPt G.fittedBellman W → W = V) ∧
        ∀ V0, Tendsto (fun n : ℕ => G.fittedBellman^[n] V0) atTop (𝓝 V) :=
  G.np_fitted_contraction.globallyStable_univ

end FittedGrid

/-- Piecewise linear interpolation between two nodes `k₁ < k₂`: the weights `(k₂ − k)/(k₂ − k₁)`
and `(k − k₁)/(k₂ − k₁)`. -/
noncomputable def np_linWeights (k1 k2 : ℝ) (k : ℝ) : Fin 2 → ℝ :=
  ![(k2 - k) / (k2 - k1), (k - k1) / (k2 - k1)]

/-- Linear interpolation is an averager on `[k₁, k₂]`: its weights are nonnegative and sum to one,
and it reproduces the data at the nodes. -/
theorem np_linWeights_averager {k1 k2 : ℝ} (h : k1 < k2) :
    (∀ k ∈ Set.Icc k1 k2, ∀ m, 0 ≤ np_linWeights k1 k2 k m) ∧
      (∀ k ∈ Set.Icc k1 k2, ∑ m, np_linWeights k1 k2 k m = 1) ∧
        np_linWeights k1 k2 k1 = ![1, 0] ∧ np_linWeights k1 k2 k2 = ![0, 1] := by
  have hd : 0 < k2 - k1 := sub_pos.2 h
  refine ⟨fun k hk m => ?_, fun k _ => ?_, ?_, ?_⟩
  · fin_cases m
    · exact div_nonneg (by linarith [hk.2]) hd.le
    · exact div_nonneg (by linarith [hk.1]) hd.le
  · simp only [np_linWeights, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring
  · funext m
    fin_cases m <;> simp [np_linWeights, hd.ne']
  · funext m
    fin_cases m <;> simp [np_linWeights, hd.ne']

/-- A concrete instance of value function interpolation: two capital nodes `0 < 1` with linear
interpolation, one shock state, zero utility and `β = 1/2`. -/
noncomputable def np_fittedGridExample : FittedGrid 2 1 where
  kmin := 0
  kmax := 1
  kmin_le := zero_le_one
  kgrid := ![0, 1]
  sgrid := fun _ => 0
  pz := fun _ _ => 1
  pz_markov := ⟨fun _ _ => zero_le_one, fun _ => by simp⟩
  u := fun _ => 0
  f := fun k _ => k
  β := 1 / 2
  β_pos := by norm_num
  β_lt_one := by norm_num
  wt := np_linWeights 0 1
  wt_nonneg := (np_linWeights_averager zero_lt_one).1
  wt_sum := (np_linWeights_averager zero_lt_one).2.1
  u_bdd := fun _ => ⟨0, by rintro _ ⟨k, rfl⟩; exact le_rfl⟩

/-- The example's fitted iteration converges (its operator is a `1/2`-contraction). -/
theorem np_fittedGridExample_contraction :
    IsContractionOn np_fittedGridExample.fittedBellman Set.univ (1 / 2) :=
  np_fittedGridExample.np_fitted_contraction

end Miao.NumericalMethods.NP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Projection methods: residuals and weighted-residual conditions

Miao, *Economic Dynamics in Discrete Time*, §11.5 (pp. 370–373).

A functional equation `F(f) = 0` is approximated by `f̂(x; c) = ∑ⱼ cⱼ φⱼ(x)`;
the residual is `R(x; c) = F̂(f̂(·; c))(x)` and the projections are
`Pᵢ(c) = ⟨R(·; c), pᵢ⟩`. We formalise the four choices of projection
directions `pᵢ` and the relations the text asserts between them.

* Collocation (p. 371): with the point-evaluation (quadrature) inner product,
  the projection conditions are exactly `R(xᵢ; c) = 0` (`np_collocation_iff`).
  As printed, the directions are indicator functions of points; under an
  integral inner product these give `Pᵢ ≡ 0` for every `c`
  (`np_collocation_integral_degenerate`), so the book's derivation needs the
  discrete inner product.
* Least squares (p. 372): `pᵢ = ∂R/∂cᵢ` (the book prints `∂cⱼ`). The
  projection conditions are the first-order conditions of `min_c ⟨R, R⟩`
  (`np_ls_hasFDerivAt`, `np_ls_foc`); they are equivalent to minimisation when
  `R` is affine in `c` (`np_ls_affine_iff`), but not in general
  (`np_ls_not_sufficient`).
* Galerkin (p. 372): `pᵢ = φᵢ`; the conditions say `R ⊥ span{φᵢ}`
  (`np_galerkin_iff_orthogonal`), and for `F(f) = f − h` Galerkin and least
  squares coincide: both characterise the best approximation of `h`
  (`np_galerkin_iff_ls`).
* Method of moments (p. 373): `pᵢ = x^{i−1}`.
* Quadrature-based projections are "weighted collocation methods" (p. 373):
  with a quadrature inner product the projections depend on `R` only through
  its values at the nodes (`np_quadrature_proj_eq`), and when there are as many
  nodes as coefficients and the direction matrix `(pᵢ(y_k))` is nonsingular the
  projection conditions are equivalent to collocation at the nodes
  (`np_quadrature_iff_collocation`); this applies to the method of moments at
  distinct nodes (`np_moments_iff_collocation`, Vandermonde). Discrete least
  squares fitting ("regression") with as many nodes as coefficients and a
  nonsingular basis matrix is interpolation (`np_regression_iff_interpolation`).
-/

namespace Miao.NumericalMethods.NP

open Finset Filter Topology Matrix
open scoped InnerProductSpace

/-! ### The projection framework -/

/-- Miao, p. 370: the approximation `f̂(x; c) = ∑ⱼ cⱼ φⱼ(x)`. -/
def np_approx {D : Type*} {n : ℕ} (φ : Fin n → D → ℝ) (c : Fin n → ℝ) : D → ℝ :=
  fun x => ∑ j, c j * φ j x

/-- Miao, p. 371, Step 3: the residual `R(x; c) = F̂(f̂(·; c))(x)`. -/
def np_residual {D : Type*} {n : ℕ} (Fh : (D → ℝ) → D → ℝ) (φ : Fin n → D → ℝ)
    (c : Fin n → ℝ) : D → ℝ :=
  Fh (np_approx φ c)

/-- Miao, p. 371, Step 4: the projections `Pᵢ(c) = ⟨R(·; c), pᵢ⟩` for an inner product `ip`. -/
def np_proj {D : Type*} {n : ℕ} (ip : (D → ℝ) → (D → ℝ) → ℝ) (R : D → ℝ) (p : Fin n → D → ℝ)
    (i : Fin n) : ℝ :=
  ip R (p i)

/-- A quadrature (discrete) inner product `⟨f, g⟩ = ∑_k w_k f(y_k) g(y_k)` with nodes `y_k` and
weights `w_k` (Miao, p. 373). -/
def np_quadIP {D : Type*} {m : ℕ} (y : Fin m → D) (w : Fin m → ℝ) (f g : D → ℝ) : ℝ :=
  ∑ k, w k * f (y k) * g (y k)

/-- Miao, p. 371: the collocation directions `pᵢ(x) = 1` if `x = xᵢ`, `0` otherwise. -/
noncomputable def np_collocDir {D : Type*} {n : ℕ} (x : Fin n → D) (i : Fin n) : D → ℝ := by
  classical
  exact fun z => if z = x i then 1 else 0

/-- Miao, p. 373: the method-of-moments directions `pᵢ(x) = x^{i−1}` (indexed from `0`). -/
def np_momentDir {n : ℕ} (i : Fin n) : ℝ → ℝ := fun x => x ^ (i : ℕ)

/-! ### Collocation -/

/-- **Collocation** (Miao, p. 371): with a quadrature inner product whose (distinct) nodes `y`
include the collocation points `xᵢ = y(ιᵢ)`, the projection on the `i`-th collocation direction
is `w_{ιᵢ} R(xᵢ; c)`. -/
theorem np_collocation_proj {D : Type*} {m n : ℕ} {y : Fin m → D} (hy : Function.Injective y)
    (w : Fin m → ℝ) (ι : Fin n → Fin m) (R : D → ℝ) (i : Fin n) :
    np_proj (np_quadIP y w) R (np_collocDir (y ∘ ι)) i = w (ι i) * R (y (ι i)) := by
  classical
  simp only [np_proj, np_quadIP, np_collocDir, Function.comp_apply, hy.eq_iff, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (ι i)]
  simp

/-- **Collocation** (Miao, p. 371): the projection conditions `Pᵢ(c) = 0` are exactly
`R(xᵢ; c) = 0`, `i = 1, …, n` (nonzero weights at the collocation nodes). -/
theorem np_collocation_iff {D : Type*} {m n : ℕ} {y : Fin m → D} (hy : Function.Injective y)
    {w : Fin m → ℝ} (hw : ∀ k, w k ≠ 0) (ι : Fin n → Fin m) (R : D → ℝ) :
    (∀ i, np_proj (np_quadIP y w) R (np_collocDir (y ∘ ι)) i = 0) ↔ ∀ i, R (y (ι i)) = 0 := by
  simp only [np_collocation_proj hy, mul_eq_zero, hw, false_or]

/-- Correction to Miao, p. 371: under the integral inner product `⟨f, g⟩ = ∫ f g dx` on `ℝ` the
book's collocation directions (indicators of points) give `Pᵢ(c) = 0` for every residual, so the
projection conditions carry no information; collocation needs point evaluation. -/
theorem np_collocation_integral_degenerate {n : ℕ} (x : Fin n → ℝ) (R : ℝ → ℝ) (i : Fin n) :
    ∫ z, R z * np_collocDir x i z = 0 := by
  classical
  refine MeasureTheory.integral_eq_zero_of_ae ?_
  have h : ∀ᵐ z ∂MeasureTheory.volume, z ≠ x i := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [h] with z hz
  simp [np_collocDir, hz]

/-! ### Least squares -/

/-- Miao, p. 372, the least squares method: the gradient of `c ↦ ⟨R(·; c), R(·; c)⟩ = ‖R(c)‖²` is
`2⟨R(c), DR(c) ·⟩`; its `i`-th component is `2⟨R, ∂R/∂cᵢ⟩`. -/
theorem np_ls_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    {R : (Fin n → ℝ) → E} {DR : (Fin n → ℝ) →L[ℝ] E} {c : Fin n → ℝ} (hR : HasFDerivAt R DR c) :
    HasFDerivAt (fun c => ⟪R c, R c⟫_ℝ) ((2 : ℕ) • (innerSL ℝ (R c)).comp DR) c ∧
      ∀ i, ((2 : ℕ) • (innerSL ℝ (R c)).comp DR) (Pi.single i 1) =
        2 * ⟪R c, DR (Pi.single i 1)⟫_ℝ := by
  refine ⟨?_, fun i => ?_⟩
  · have h := hR.norm_sq
    have he : (fun c => ⟪R c, R c⟫_ℝ) = fun c => ‖R c‖ ^ 2 := by
      funext c
      exact real_inner_self_eq_norm_sq (R c)
    rw [he]
    exact h
  · simp [two_smul, two_mul]

/-- Miao, p. 372: at a (local) minimiser of `⟨R(·; c), R(·; c)⟩` the least squares projection
conditions `⟨R(·; c), ∂R(·; c)/∂cᵢ⟩ = 0` hold. -/
theorem np_ls_foc {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    {R : (Fin n → ℝ) → E} {DR : (Fin n → ℝ) →L[ℝ] E} {c : Fin n → ℝ} (hR : HasFDerivAt R DR c)
    (hmin : IsLocalMin (fun c => ⟪R c, R c⟫_ℝ) c) (i : Fin n) :
    ⟪R c, DR (Pi.single i 1)⟫_ℝ = 0 := by
  obtain ⟨hd, hcomp⟩ := np_ls_hasFDerivAt hR
  have h0 := hmin.hasFDerivAt_eq_zero hd
  have h2 : (2 : ℝ) * ⟪R c, DR (Pi.single i 1)⟫_ℝ = 0 := by
    rw [← hcomp i, h0]
    simp
  linarith

/-- Miao, p. 372 ("it is equivalent to solving `min_c ⟨R, R⟩`"), the case where the equivalence
holds: if the residual is affine in the coefficients, `R(c) = r₀ + Lc`, then the least squares
projection conditions `⟨R(c), ∂R/∂cᵢ⟩ = ⟨R(c), L eᵢ⟩ = 0` hold iff `c` minimises `‖R‖`. -/
theorem np_ls_affine_iff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    (r0 : E) (L : (Fin n → ℝ) →ₗ[ℝ] E) (c : Fin n → ℝ) :
    (∀ i, ⟪r0 + L c, L (Pi.single i 1)⟫_ℝ = 0) ↔ ∀ c', ‖r0 + L c‖ ≤ ‖r0 + L c'‖ := by
  constructor
  · intro h c'
    have horth : ∀ d, ⟪r0 + L c, L d⟫_ℝ = 0 := by
      intro d
      rw [LinearMap.pi_apply_eq_sum_univ L d, inner_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hs : (fun j => if i = j then (1 : ℝ) else 0) = Pi.single i 1 := by
        funext j
        simp [Pi.single_apply, eq_comm]
      rw [inner_smul_right, hs, h i, mul_zero]
    have hdecomp : r0 + L c' = (r0 + L c) + L (c' - c) := by
      rw [map_sub]
      abel
    have hsq : ‖r0 + L c‖ ^ 2 ≤ ‖r0 + L c'‖ ^ 2 := by
      rw [hdecomp, norm_add_sq_real (r0 + L c) (L (c' - c)), horth]
      nlinarith [sq_nonneg ‖L (c' - c)‖]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq
  · intro h i
    let L' : (Fin n → ℝ) →L[ℝ] E := LinearMap.toContinuousLinearMap L
    have hR : HasFDerivAt (fun c => r0 + L c) L' c := by
      have : HasFDerivAt (fun c => r0 + L' c) L' c := L'.hasFDerivAt.const_add r0
      exact this
    have hmin : IsLocalMin (fun c => ⟪r0 + L c, r0 + L c⟫_ℝ) c := by
      refine Filter.Eventually.of_forall fun c' => ?_
      simp only [real_inner_self_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) (h c') 2
    exact np_ls_foc hR hmin i

/-- Correction to Miao, p. 372: for a residual that is not affine in `c`, the least squares
projection conditions do not imply minimisation. With `R(c) = c² − 1` (one coefficient), at
`c = 0` the derivative is `0`, so `⟨R, ∂R/∂c⟩ = 0`, yet `‖R(0)‖ = 1 > 0 = ‖R(1)‖`. -/
theorem np_ls_not_sufficient :
    ∃ (R : (Fin 1 → ℝ) → ℝ) (DR : (Fin 1 → ℝ) →L[ℝ] ℝ) (c : Fin 1 → ℝ),
      HasFDerivAt R DR c ∧ (∀ i, ⟪R c, DR (Pi.single i 1)⟫_ℝ = 0) ∧
        ¬ ∀ c', ‖R c‖ ≤ ‖R c'‖ := by
  refine ⟨fun c => c 0 ^ 2 - 1, 0, 0, ?_, fun i => by simp, ?_⟩
  · have h0 : HasFDerivAt (fun c : Fin 1 → ℝ => c 0) (ContinuousLinearMap.proj 0) 0 :=
      hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 1) (0 : Fin 1 → ℝ)
    have h1 := (h0.pow 2).sub_const 1
    convert h1 using 1
    simp
  · intro h
    have := h fun _ => 1
    norm_num at this

/-! ### Galerkin -/

/-- **Galerkin** (Miao, p. 372): the conditions `⟨R, φᵢ⟩ = 0`, `i = 1, …, n`, say that the
residual is orthogonal to the span of the basis functions. -/
theorem np_galerkin_iff_orthogonal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (φ : Fin n → E) (R : E) :
    (∀ i, ⟪R, φ i⟫_ℝ = 0) ↔ R ∈ (Submodule.span ℝ (Set.range φ))ᗮ := by
  rw [Submodule.mem_orthogonal]
  constructor
  · intro h u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [real_inner_comm]
      exact h i
    | zero => exact inner_zero_left _
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]
  · intro h i
    rw [real_inner_comm]
    exact h _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Galerkin and least squares coincide for `F(f) = f − h` (Miao, p. 372): the residual is
`R(c) = ∑ⱼ cⱼ φⱼ − h`, so `∂R/∂cᵢ = φᵢ`; the Galerkin conditions hold iff `c` minimises
`‖R(c)‖`, i.e. `∑ⱼ cⱼ φⱼ` is the best approximation of `h` in `span{φⱼ}`. -/
theorem np_galerkin_iff_ls {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    (φ : Fin n → E) (h : E) (c : Fin n → ℝ) :
    (∀ i, ⟪∑ j, c j • φ j - h, φ i⟫_ℝ = 0) ↔
      ∀ c' : Fin n → ℝ, ‖∑ j, c j • φ j - h‖ ≤ ‖∑ j, c' j • φ j - h‖ := by
  classical
  have hL : ∀ d : Fin n → ℝ, Fintype.linearCombination ℝ φ d = ∑ j, d j • φ j :=
    fun d => Fintype.linearCombination_apply ℝ φ d
  have hR : ∀ d : Fin n → ℝ, ∑ j, d j • φ j - h = -h + Fintype.linearCombination ℝ φ d := by
    intro d
    rw [hL]
    abel
  have hsingle : ∀ i, Fintype.linearCombination ℝ φ (Pi.single i 1) = φ i := by
    intro i
    rw [Fintype.linearCombination_apply_single, one_smul]
  have := np_ls_affine_iff (-h) (Fintype.linearCombination ℝ φ) c
  simp only [hsingle] at this
  simp only [hR]
  exact this

/-! ### Quadrature-based projections are weighted collocation -/

/-- Miao, p. 373: with a quadrature inner product, `Pᵢ(c) = ∑_k pᵢ(y_k) (w_k R(y_k; c))`; the
projections use the residual only at the quadrature nodes ("weighted collocation"). -/
theorem np_quadrature_proj_eq {D : Type*} {m n : ℕ} (y : Fin m → D) (w : Fin m → ℝ)
    (R : D → ℝ) (p : Fin n → D → ℝ) (i : Fin n) :
    np_proj (np_quadIP y w) R p i =
      ((Matrix.of fun i k => p i (y k)) *ᵥ fun k => w k * R (y k)) i := by
  simp only [np_proj, np_quadIP, Matrix.mulVec, dotProduct, Matrix.of_apply]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Miao, p. 373: quadrature-based projection conditions depend on `R` only through its values at
the nodes. -/
theorem np_quadrature_proj_congr {D : Type*} {m n : ℕ} (y : Fin m → D) (w : Fin m → ℝ)
    {R R' : D → ℝ} (h : ∀ k, R (y k) = R' (y k)) (p : Fin n → D → ℝ) (i : Fin n) :
    np_proj (np_quadIP y w) R p i = np_proj (np_quadIP y w) R' p i := by
  simp only [np_proj, np_quadIP, h]

/-- Miao, p. 373, "quadrature-based projection techniques are essentially weighted collocation
methods": with `n` nodes, nonzero weights and a nonsingular direction matrix `(pᵢ(y_k))`, the
projection conditions `Pᵢ(c) = 0` hold iff `R(y_k; c) = 0` at every node. -/
theorem np_quadrature_iff_collocation {D : Type*} {n : ℕ} (y : Fin n → D) {w : Fin n → ℝ}
    (hw : ∀ k, w k ≠ 0) (R : D → ℝ) (p : Fin n → D → ℝ)
    (hdet : (Matrix.of fun i k => p i (y k)).det ≠ 0) :
    (∀ i, np_proj (np_quadIP y w) R p i = 0) ↔ ∀ k, R (y k) = 0 := by
  simp only [np_quadrature_proj_eq]
  constructor
  · intro h k
    have hv := Matrix.eq_zero_of_mulVec_eq_zero hdet (funext h)
    have := congrFun hv k
    simp only [Pi.zero_apply, mul_eq_zero, hw k, false_or] at this
    exact this
  · intro h i
    have : (fun k => w k * R (y k)) = 0 := funext fun k => by simp [h k]
    rw [this, Matrix.mulVec_zero, Pi.zero_apply]

/-- **Method of moments** (Miao, p. 373) with a quadrature at `n` distinct nodes and nonzero
weights: the moment conditions `⟨R, x^{i−1}⟩ = 0` hold iff `R` vanishes at the nodes (the
direction matrix is a Vandermonde matrix). -/
theorem np_moments_iff_collocation {n : ℕ} {y : Fin n → ℝ} (hy : Function.Injective y)
    {w : Fin n → ℝ} (hw : ∀ k, w k ≠ 0) (R : ℝ → ℝ) :
    (∀ i, np_proj (np_quadIP y w) R (np_momentDir (n := n)) i = 0) ↔ ∀ k, R (y k) = 0 := by
  refine np_quadrature_iff_collocation y hw R np_momentDir ?_
  have h : (Matrix.of fun i k => np_momentDir (n := n) i (y k)) = (Matrix.vandermonde y).transpose
    := by
    ext i k
    simp [np_momentDir, Matrix.vandermonde_apply]
  rw [h, Matrix.det_transpose]
  exact Matrix.det_vandermonde_ne_zero_iff.2 hy

/-- **Galerkin with quadrature** (Miao, pp. 372–373): with `n` nodes, nonzero weights and a
nonsingular basis matrix `(φᵢ(y_k))`, the Galerkin conditions `⟨R, φᵢ⟩ = 0` are equivalent to
collocation at the nodes. -/
theorem np_galerkin_quadrature_iff_collocation {D : Type*} {n : ℕ} (y : Fin n → D)
    {w : Fin n → ℝ} (hw : ∀ k, w k ≠ 0) (R : D → ℝ) (φ : Fin n → D → ℝ)
    (hdet : (Matrix.of fun i k => φ i (y k)).det ≠ 0) :
    (∀ i, np_proj (np_quadIP y w) R φ i = 0) ↔ ∀ k, R (y k) = 0 :=
  np_quadrature_iff_collocation y hw R φ hdet

/-- Discrete least squares ("regression") with as many nodes as coefficients is interpolation
(Miao, pp. 372–373): if the basis matrix `(φⱼ(y_k))` is nonsingular and the weights are positive,
`c` minimises `∑_k w_k (f̂(y_k; c) − h(y_k))²` iff `f̂(y_k; c) = h(y_k)` at every node. -/
theorem np_regression_iff_interpolation {D : Type*} {n : ℕ} (y : Fin n → D) {w : Fin n → ℝ}
    (hw : ∀ k, 0 < w k) (φ : Fin n → D → ℝ) (h : D → ℝ)
    (hdet : (Matrix.of fun k j => φ j (y k)).det ≠ 0) (c : Fin n → ℝ) :
    (∀ c', ∑ k, w k * (np_approx φ c (y k) - h (y k)) ^ 2 ≤
        ∑ k, w k * (np_approx φ c' (y k) - h (y k)) ^ 2) ↔
      ∀ k, np_approx φ c (y k) = h (y k) := by
  set M : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun k j => φ j (y k) with hM
  have happrox : ∀ d k, np_approx φ d (y k) = (M *ᵥ d) k := by
    intro d k
    simp only [np_approx, hM, Matrix.mulVec, dotProduct, Matrix.of_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  constructor
  · intro hmin
    -- the interpolating coefficients `c* = M⁻¹ h` give objective `0`
    have hunit : IsUnit M.det := isUnit_iff_ne_zero.2 hdet
    set cs := M⁻¹ *ᵥ (fun k => h (y k)) with hcs
    have hcs' : ∀ k, np_approx φ cs (y k) = h (y k) := by
      intro k
      rw [happrox, hcs, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
    have h0 := hmin cs
    simp only [hcs', sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      Finset.sum_const_zero] at h0
    have hterm : ∀ k ∈ Finset.univ, 0 ≤ w k * (np_approx φ c (y k) - h (y k)) ^ 2 :=
      fun k _ => mul_nonneg (hw k).le (sq_nonneg _)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 (le_antisymm h0
      (Finset.sum_nonneg hterm))
    intro k
    have := hz k (Finset.mem_univ k)
    rw [mul_eq_zero] at this
    rcases this with h1 | h1
    · exact absurd h1 (hw k).ne'
    · exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1)
  · intro hint c'
    simp only [hint, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, Finset.sum_const_zero]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hw k).le (sq_nonneg _)

end Miao.NumericalMethods.NP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The projection method for the stochastic growth model

Miao, *Economic Dynamics in Discrete Time*, §11.5 (pp. 373–376).

For the growth model `max E ∑ βᵗ u(C_t)`, `C_t + K_{t+1} = f(K_t, z_t)`,
`ln z_{t+1} = ρ ln z_t + σ ε_{t+1}`, the book rewrites the Euler equation (11.8)
for a policy `K' = g(K, z)` as the functional equation
`0 = f(k, z) − g(k, z) − (u')⁻¹(β ∫ I(k, z, ε) e^{−ε²/2}/√(2π) dε) ≡ F(g)(k, z)`.

* `np_growthF_iff_euler`: `F(g)(k, z) = 0` iff the Euler equation (11.8) holds at
  `(k, z)` (for positive consumption, with `(u')⁻¹` a two-sided inverse of `u'`
  on positive reals, e.g. CRRA `np_crra_inverse`).
* `np_gaussHermite_change`: the change of variables `ε = √2 y` behind the
  Gauss–Hermite approximation:
  `∫ I(ε) e^{−ε²/2}/√(2π) dε = π^{−1/2} ∫ I(√2 y) e^{−y²} dy`; hence when the
  Gauss–Hermite rule is exact the book's residual `R(k, z; c)` equals
  `F(ĝ)(k, z)` (`np_growth_residual_eq_F`).
* The truncation `z_m = exp(−4σ/√(1 − ρ²))`, `z_M = exp(4σ/√(1 − ρ²))` is four
  stationary standard deviations of `ln z` on each side (`np_ar1_stationary_variance`,
  `np_z_bounds`), and the normalisation `x = (2k − k_m − k_M)/(k_M − k_m)` maps
  `[k_m, k_M]` onto `[−1, 1]`, where the Chebyshev weight is defined
  (`np_normalize_mem_Icc`).

The numerical solution (choice of `c`, root finding, stability checks) is
algorithmic and not formalised.
-/

namespace Miao.NumericalMethods.NP

open Real MeasureTheory

/-- Miao, p. 374: `I(k, z, ε) = u'(f(g(k, z), z') − g(g(k, z), z')) f'(g(k, z), z')` with
`z' = exp(ρ ln z + σε)`. Here `up = u'` and `fk = ∂f/∂k`. -/
noncomputable def np_growthI (up : ℝ → ℝ) (f fk g : ℝ → ℝ → ℝ) (ρ σ k z ε : ℝ) : ℝ :=
  up (f (g k z) (exp (ρ * log z + σ * ε)) - g (g k z) (exp (ρ * log z + σ * ε))) *
    fk (g k z) (exp (ρ * log z + σ * ε))

/-- Miao, p. 374: the operator `F(g)(k, z) = f(k, z) − g(k, z) − (u')⁻¹(β ∫ I(k, z, ε) φ(ε) dε)`
with `φ` the standard normal density. -/
noncomputable def np_growthF (up upinv : ℝ → ℝ) (f fk g : ℝ → ℝ → ℝ) (β ρ σ k z : ℝ) : ℝ :=
  f k z - g k z - upinv (β * ∫ ε, np_growthI up f fk g ρ σ k z ε * (exp (-ε ^ 2 / 2) / √(2 * π)))

/-- Miao, (11.8) and p. 374: for positive consumption `f(k, z) − g(k, z)` and a positive
right-hand side, `F(g)(k, z) = 0` iff the Euler equation
`u'(f(k, z) − g(k, z)) = β E[u'(f(k', z') − g(k', z')) f'(k', z')]`, `k' = g(k, z)`, holds, where
`(u')⁻¹` is a two-sided inverse of `u'` on the positive reals. -/
theorem np_growthF_iff_euler {up upinv : ℝ → ℝ}
    (hinv1 : ∀ c, 0 < c → upinv (up c) = c) (hinv2 : ∀ y, 0 < y → up (upinv y) = y)
    (f fk g : ℝ → ℝ → ℝ) (β ρ σ k z : ℝ) (hc : 0 < f k z - g k z)
    (hE : 0 < β * ∫ ε, np_growthI up f fk g ρ σ k z ε * (exp (-ε ^ 2 / 2) / √(2 * π))) :
    np_growthF up upinv f fk g β ρ σ k z = 0 ↔
      up (f k z - g k z) =
        β * ∫ ε, np_growthI up f fk g ρ σ k z ε * (exp (-ε ^ 2 / 2) / √(2 * π)) := by
  unfold np_growthF
  constructor
  · intro h
    rw [sub_eq_zero] at h
    rw [h, hinv2 _ hE]
  · intro h
    rw [← h, hinv1 _ hc, sub_self]

/-- CRRA marginal utility `u'(c) = c^{−γ}` has the inverse `(u')⁻¹(y) = y^{−1/γ}` on the positive
reals (an instance of the hypotheses of `np_growthF_iff_euler`). -/
theorem np_crra_inverse {γ : ℝ} (hγ : 0 < γ) :
    (∀ c : ℝ, 0 < c → (c ^ (-γ)) ^ (-1 / γ) = c) ∧
      ∀ y : ℝ, 0 < y → (y ^ (-1 / γ)) ^ (-γ) = y := by
  have key : -γ * (-1 / γ) = 1 := by field_simp
  refine ⟨fun c hc => ?_, fun y hy => ?_⟩
  · rw [← rpow_mul hc.le, key, rpow_one]
  · rw [← rpow_mul hy.le, mul_comm, key, rpow_one]

/-- Miao, p. 374, the Gauss–Hermite change of variables `ε = √2 y`:
`∫ I(ε) e^{−ε²/2}/√(2π) dε = π^{−1/2} ∫ I(√2 y) e^{−y²} dy`. -/
theorem np_gaussHermite_change (I : ℝ → ℝ) :
    ∫ ε, I ε * (exp (-ε ^ 2 / 2) / √(2 * π)) = (√π)⁻¹ * ∫ y, I (√2 * y) * exp (-y ^ 2) := by
  set h : ℝ → ℝ := fun ε => I ε * (exp (-ε ^ 2 / 2) / √(2 * π)) with hh
  have hs2 : √2 ^ 2 = 2 := sq_sqrt (by norm_num)
  have hspi : 0 < √π := sqrt_pos.2 pi_pos
  have hs2pos : 0 < √2 := sqrt_pos.2 (by norm_num)
  have hsplit : √(2 * π) = √2 * √π := sqrt_mul (by norm_num) π
  have h1 : (fun y => I (√2 * y) * exp (-y ^ 2)) = fun y => √(2 * π) * h (√2 * y) := by
    funext y
    simp only [hh]
    have : -(√2 * y) ^ 2 / 2 = -y ^ 2 := by rw [mul_pow, hs2]; ring
    rw [this]
    have hne : √(2 * π) ≠ 0 := by rw [hsplit]; positivity
    field_simp
  rw [h1, integral_const_mul, Measure.integral_comp_mul_left h √2, abs_of_pos (inv_pos.2 hs2pos),
    hsplit, smul_eq_mul]
  field_simp

/-- Miao, p. 375: when the Gauss–Hermite rule with nodes `εⱼ` and weights `wⱼ` is exact for
`y ↦ I(k, z, √2 y)`, the residual `R(k, z; c) = f − ĝ − (u')⁻¹(βπ^{−1/2} ∑ⱼ I(k, z, √2 εⱼ) wⱼ)`
equals `F(ĝ)(k, z)`. -/
theorem np_growth_residual_eq_F (up upinv : ℝ → ℝ) (f fk g : ℝ → ℝ → ℝ) (β ρ σ k z : ℝ)
    {m : ℕ} (εq wq : Fin m → ℝ)
    (hexact : ∑ j, np_growthI up f fk g ρ σ k z (√2 * εq j) * wq j =
      ∫ y, np_growthI up f fk g ρ σ k z (√2 * y) * exp (-y ^ 2)) :
    f k z - g k z - upinv (β * ((√π)⁻¹ * ∑ j, np_growthI up f fk g ρ σ k z (√2 * εq j) * wq j)) =
      np_growthF up upinv f fk g β ρ σ k z := by
  rw [hexact, ← np_gaussHermite_change]
  rfl

/-- The stationary variance of the AR(1) `s' = ρs + σε` (Miao, p. 375): `v = ρ²v + σ²` iff
`v = σ²/(1 − ρ²)`, for `|ρ| < 1`. -/
theorem np_ar1_stationary_variance {ρ σ v : ℝ} (hρ : |ρ| < 1) :
    v = ρ ^ 2 * v + σ ^ 2 ↔ v = σ ^ 2 / (1 - ρ ^ 2) := by
  have h : 0 < 1 - ρ ^ 2 := by
    have : ρ ^ 2 < 1 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg ρ]
    linarith
  rw [eq_div_iff h.ne']
  constructor <;> intro e <;> linarith

/-- Miao, p. 375: the truncation `z_m = exp(−4σ/√(1 − ρ²))`, `z_M = exp(4σ/√(1 − ρ²))` satisfies
`z_m < 1 < z_M`, `z_m z_M = 1`, and `ln z_M` is four stationary standard deviations of `ln z`. -/
theorem np_z_bounds {ρ σ : ℝ} (hρ : |ρ| < 1) (hσ : 0 < σ) :
    exp (-4 * σ / √(1 - ρ ^ 2)) < 1 ∧ 1 < exp (4 * σ / √(1 - ρ ^ 2)) ∧
      exp (-4 * σ / √(1 - ρ ^ 2)) * exp (4 * σ / √(1 - ρ ^ 2)) = 1 ∧
        log (exp (4 * σ / √(1 - ρ ^ 2))) = 4 * √(σ ^ 2 / (1 - ρ ^ 2)) := by
  have h : 0 < 1 - ρ ^ 2 := by
    have : ρ ^ 2 < 1 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg ρ]
    linarith
  have hs : 0 < √(1 - ρ ^ 2) := sqrt_pos.2 h
  have hpos : 0 < 4 * σ / √(1 - ρ ^ 2) := by positivity
  refine ⟨?_, one_lt_exp_iff.2 hpos, ?_, ?_⟩
  · rw [exp_lt_one_iff, neg_mul, neg_div]
    linarith
  · rw [← exp_add, neg_mul, neg_div, neg_add_cancel, exp_zero]
  · rw [log_exp, sqrt_div (sq_nonneg σ), sqrt_sq hσ.le]
    ring

/-- Miao, p. 375: the normalisation `x = (2k − k_m − k_M)/(k_M − k_m)` maps `[k_m, k_M]` onto
`[−1, 1]` (endpoints to endpoints), the domain of the Chebyshev weight `(1 − x²)^{−1/2}`. -/
theorem np_normalize_mem_Icc {km kM : ℝ} (h : km < kM) (k : ℝ) :
    (k ∈ Set.Icc km kM ↔ (2 * k - km - kM) / (kM - km) ∈ Set.Icc (-1) 1) ∧
      (2 * km - km - kM) / (kM - km) = -1 ∧ (2 * kM - km - kM) / (kM - km) = 1 := by
  have hd : 0 < kM - km := sub_pos.2 h
  refine ⟨?_, by field_simp; ring, by field_simp; ring⟩
  simp only [Set.mem_Icc, le_div_iff₀ hd, div_le_iff₀ hd]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

end Miao.NumericalMethods.NP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Euler equations from the Bellman equation: the growth model and Exercise 11.3

Miao, *Economic Dynamics in Discrete Time*, (11.8)–(11.9) (pp. 374, 377) and
Exercise 11.3 (p. 384).

From the Bellman equation (11.9) `V(K, z) = max_{K'} u(f(K, z) − K') +
βE[V(K', z') | z]`, attained by an interior policy `K' = g(K, z)`, with `V`
differentiable in `K` and differentiation under the conditional expectation
allowed, the first-order condition and the envelope (Benveniste–Scheinkman)
condition give the Euler equation (11.8) (`eq_11_8`). The envelope step is
`np_envelope`: a differentiable function that dominates another near a point,
with equality there, has the same derivative.

Exercise 11.3 adds endogenous labour: `U(C, N) = (C^θ(1 − N)^{1−θ})^{1−γ}/(1 − γ)`
and `C + K' = (1 − δ)K + zK^αN^{1−α}`. We compute the marginal utilities and
products (`ex_11_3_UC`, `ex_11_3_FK`, `ex_11_3_FN`, `ex_11_3_total_N`) and derive
from the Bellman equation the intratemporal condition
`(1 − θ)C = θ(1 − N)(1 − α)zK^αN^{−α}` (`ex_11_3_intratemporal`), the capital
first-order condition and envelope condition, the Euler equation
`U_C(C, N) = βE[U_C(C', N')(1 − δ + αz'K'^{α−1}N'^{1−α})]` (`ex_11_3_euler`), and the
deterministic steady-state capital–labour ratio (`ex_11_3_steady_state`).

The conditional law of `z'` given `z` is an arbitrary family of measures `Q z`
(for the AR(1) of the book, the image of the standard normal under
`ε ↦ exp(ρ ln z + σε)`); differentiability of `K' ↦ E[V(K', z') | z]` with
derivative `E[V_K(K', z') | z]` is a hypothesis (it holds under the usual
domination conditions). The numerical solutions asked for in Exercise 11.3
(a)–(e) are computational and not formalised.
-/

namespace Miao.NumericalMethods.NP

open Filter Topology MeasureTheory

/-- The envelope step (Benveniste–Scheinkman): if `W ≤ V` near `K₀` with equality at `K₀`, and
both are differentiable at `K₀`, their derivatives agree. -/
theorem np_envelope {V W : ℝ → ℝ} {K0 V' W' : ℝ} (hle : ∀ᶠ K in 𝓝 K0, W K ≤ V K)
    (heq : W K0 = V K0) (hV : HasDerivAt V V' K0) (hW : HasDerivAt W W' K0) : V' = W' := by
  have hmin : IsLocalMin (fun K => V K - W K) K0 := by
    filter_upwards [hle] with K hK
    rw [heq, sub_self]
    linarith
  have := hmin.hasDerivAt_eq_zero (hV.sub hW)
  linarith

/-- **(11.8)** (Miao, p. 374), derived from the Bellman equation (11.9): if `g(K, z)` attains the
maximum in (11.9) in the interior `0 < g < f`, `u` is differentiable at positive consumption,
`f`, `V` are differentiable in `K` and `K' ↦ E[V(K', z')|z]` has derivative `E[V_K(K', z')|z]`,
then the first-order condition `u'(C) = βE[V_K(K', z')|z]`, the envelope condition
`V_K(K, z) = u'(C) f_K(K, z)` and the Euler equation
`u'(f(K, z) − g(K, z)) = βE[u'(f(K', z') − g(K', z')) f_K(K', z') | z]`, `K' = g(K, z)`, hold. -/
theorem eq_11_8 {u up : ℝ → ℝ} {f fK V VK g : ℝ → ℝ → ℝ} {β : ℝ} {Q : ℝ → Measure ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt u (up c) c)
    (hf : ∀ K z, HasDerivAt (fun K => f K z) (fK K z) K)
    (hV : ∀ K z, HasDerivAt (fun K => V K z) (VK K z) K)
    (hW : ∀ k z, HasDerivAt (fun k => ∫ z', V k z' ∂Q z) (∫ z', VK k z' ∂Q z) k)
    (hBell : ∀ K z k, 0 < k → k < f K z → u (f K z - k) + β * ∫ z', V k z' ∂Q z ≤ V K z)
    (hg : ∀ K z, 0 < g K z ∧ g K z < f K z ∧
      V K z = u (f K z - g K z) + β * ∫ z', V (g K z) z' ∂Q z) (K z : ℝ) :
    up (f K z - g K z) = β * ∫ z', VK (g K z) z' ∂Q z ∧
      VK K z = up (f K z - g K z) * fK K z ∧
        up (f K z - g K z) =
          β * ∫ z', up (f (g K z) z' - g (g K z) z') * fK (g K z) z' ∂Q z := by
  -- first-order condition at every state
  have foc : ∀ K z, up (f K z - g K z) = β * ∫ z', VK (g K z) z' ∂Q z := by
    intro K z
    obtain ⟨h0, h1, heq⟩ := hg K z
    have hc : 0 < f K z - g K z := sub_pos.2 h1
    have hd : HasDerivAt (fun k => u (f K z - k) + β * ∫ z', V k z' ∂Q z)
        (up (f K z - g K z) * (-1) + β * ∫ z', VK (g K z) z' ∂Q z) (g K z) := by
      have h2 := (hu _ hc).comp (g K z) ((hasDerivAt_id' (g K z)).const_sub (f K z))
      exact h2.add ((hW (g K z) z).const_mul β)
    have hmax : IsLocalMax (fun k => u (f K z - k) + β * ∫ z', V k z' ∂Q z) (g K z) := by
      filter_upwards [Ioo_mem_nhds h0 h1] with k hk
      rw [← heq]
      exact hBell K z k hk.1 hk.2
    have := hmax.hasDerivAt_eq_zero hd
    linarith
  -- envelope condition at every state
  have env : ∀ K z, VK K z = up (f K z - g K z) * fK K z := by
    intro K z
    obtain ⟨h0, h1, heq⟩ := hg K z
    have hc : 0 < f K z - g K z := sub_pos.2 h1
    have hlow : HasDerivAt (fun K' => u (f K' z - g K z) + β * ∫ z', V (g K z) z' ∂Q z)
        (up (f K z - g K z) * fK K z) K := by
      have h2 := (hu _ hc).comp K ((hf K z).sub_const (g K z))
      simpa using h2.add_const (β * ∫ z', V (g K z) z' ∂Q z)
    have hev : ∀ᶠ K' in 𝓝 K, g K z < f K' z :=
      (hf K z).continuousAt.eventually (lt_mem_nhds h1)
    refine np_envelope ?_ heq.symm (hV K z) hlow
    filter_upwards [hev] with K' hK'
    exact hBell K' z (g K z) h0 hK'
  refine ⟨foc K z, env K z, ?_⟩
  rw [foc K z]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun z' => env (g K z) z')

/-! ### Exercise 11.3: endogenous labour -/

/-- Exercise 11.3 (Miao, p. 384): period utility `U(C, N) = (C^θ(1 − N)^{1−θ})^{1−γ}/(1 − γ)`. -/
noncomputable def np_ex3U (θ γ C N : ℝ) : ℝ := (C ^ θ * (1 - N) ^ (1 - θ)) ^ (1 - γ) / (1 - γ)

/-- Exercise 11.3: output plus undepreciated capital `(1 − δ)K + zK^αN^{1−α}`. -/
noncomputable def np_ex3F (α δ K N z : ℝ) : ℝ := (1 - δ) * K + z * K ^ α * N ^ (1 - α)

/-- The composite `X = C^θ(1 − N)^{1−θ}`. -/
noncomputable def np_ex3X (θ C N : ℝ) : ℝ := C ^ θ * (1 - N) ^ (1 - θ)

theorem np_ex3X_pos {θ C N : ℝ} (hC : 0 < C) (hN : N < 1) : 0 < np_ex3X θ C N :=
  mul_pos (Real.rpow_pos_of_pos hC θ) (Real.rpow_pos_of_pos (sub_pos.2 hN) _)

/-- Exercise 11.3: `U_C(C, N) = θX^{1−γ}/C`. -/
theorem ex_11_3_UC {θ γ C N : ℝ} (hγ : γ ≠ 1) (hC : 0 < C) (hN : N < 1) :
    HasDerivAt (fun C => np_ex3U θ γ C N) (θ * np_ex3X θ C N ^ (1 - γ) / C) C := by
  have hX := np_ex3X_pos (θ := θ) hC hN
  have hg : (1 - γ) ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have h1 : HasDerivAt (fun C => C ^ θ * (1 - N) ^ (1 - θ))
      (θ * C ^ (θ - 1) * (1 - N) ^ (1 - θ)) C :=
    (Real.hasDerivAt_rpow_const (Or.inl hC.ne')).mul_const _
  have h2 := (h1.rpow_const (p := 1 - γ) (Or.inl hX.ne')).div_const (1 - γ)
  unfold np_ex3U
  convert h2 using 1
  have ha : 0 < (1 - N) ^ (1 - θ) := Real.rpow_pos_of_pos (sub_pos.2 hN) _
  unfold np_ex3X at hX ⊢
  rw [Real.rpow_sub_one hC.ne', Real.rpow_sub_one hX.ne']
  field_simp

/-- Exercise 11.3: `F_K = 1 − δ + αzK^{α−1}N^{1−α}`. -/
theorem ex_11_3_FK {α δ K N z : ℝ} (hK : 0 < K) :
    HasDerivAt (fun K => np_ex3F α δ K N z) (1 - δ + α * z * K ^ (α - 1) * N ^ (1 - α)) K := by
  have h := ((hasDerivAt_id' K).const_mul (1 - δ)).add
    (((Real.hasDerivAt_rpow_const (p := α) (Or.inl hK.ne')).const_mul z).mul_const (N ^ (1 - α)))
  unfold np_ex3F
  convert h using 1
  ring

/-- Exercise 11.3: `F_N = (1 − α)zK^αN^{−α}`. -/
theorem ex_11_3_FN {α δ K N z : ℝ} (hN : 0 < N) :
    HasDerivAt (fun N => np_ex3F α δ K N z) ((1 - α) * z * K ^ α * N ^ (-α)) N := by
  have h := (hasDerivAt_const N ((1 - δ) * K)).add
    ((Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hN.ne')).const_mul (z * K ^ α))
  unfold np_ex3F
  convert h using 1
  rw [show 1 - α - 1 = -α by ring]
  ring

/-- Exercise 11.3, the total derivative in `N` of `U(C(N), N)` when `C` depends on `N` with
`C'(N) = c'`: it is `U_C c' + U_N = X^{1−γ}(θc'/C − (1 − θ)/(1 − N))`. -/
theorem ex_11_3_total_N {θ γ : ℝ} (hγ : γ ≠ 1) {Cf : ℝ → ℝ} {c' N : ℝ} (hCf : HasDerivAt Cf c' N)
    (hC : 0 < Cf N) (hN : N < 1) :
    HasDerivAt (fun N => np_ex3U θ γ (Cf N) N)
      (np_ex3X θ (Cf N) N ^ (1 - γ) * (θ * c' / Cf N - (1 - θ) / (1 - N))) N := by
  have hX := np_ex3X_pos (θ := θ) hC hN
  have hg : (1 - γ) ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have h1N : 0 < 1 - N := sub_pos.2 hN
  have ha := hCf.rpow_const (p := θ) (Or.inl hC.ne')
  have hb := ((hasDerivAt_id' N).const_sub 1).rpow_const (p := 1 - θ) (Or.inl h1N.ne')
  have h2 := ((ha.mul hb).rpow_const (p := 1 - γ) (Or.inl hX.ne')).div_const (1 - γ)
  unfold np_ex3U
  convert h2 using 1
  simp only [Pi.mul_apply]
  unfold np_ex3X at hX ⊢
  rw [Real.rpow_sub_one hC.ne', Real.rpow_sub_one h1N.ne', Real.rpow_sub_one hX.ne']
  field_simp
  ring

/-- **Exercise 11.3** (Miao, p. 384), the first-order conditions and the Euler equation. Let `V`
solve the Bellman equation
`V(K, z) = max_{K', N} U((1 − δ)K + zK^αN^{1−α} − K', N) + βE[V(K', z') | z]`
with the maximum attained by an interior policy `(g_K, g_N)` (`K' > 0`, `0 < N < 1`, `C > 0`),
`V` differentiable in `K` and `K' ↦ E[V(K', z')|z]` with derivative `E[V_K(K', z')|z]`. Then, with
`C = F(K, N, z) − K'`, (i) the intratemporal condition `(1 − θ)C = θ(1 − N)(1 − α)zK^αN^{−α}`,
(ii) the capital first-order condition `U_C(C, N) = βE[V_K(K', z')|z]`, (iii) the envelope
condition `V_K(K, z) = U_C(C, N)(1 − δ + αzK^{α−1}N^{1−α})` and (iv) the Euler equation
`U_C(C, N) = βE[U_C(C', N')(1 − δ + αz'K'^{α−1}N'^{1−α}) | z]` hold. -/
theorem ex_11_3_euler {θ γ α δ β : ℝ} (hγ : γ ≠ 1) {V VK gK gN : ℝ → ℝ → ℝ}
    {Q : ℝ → Measure ℝ}
    (hV : ∀ K z, 0 < K → HasDerivAt (fun K => V K z) (VK K z) K)
    (hW : ∀ k z, HasDerivAt (fun k => ∫ z', V k z' ∂Q z) (∫ z', VK k z' ∂Q z) k)
    (hBell : ∀ K z k N, 0 < k → 0 < N → N < 1 → 0 < np_ex3F α δ K N z - k →
      np_ex3U θ γ (np_ex3F α δ K N z - k) N + β * ∫ z', V k z' ∂Q z ≤ V K z)
    (hg : ∀ K z, 0 < gK K z ∧ 0 < gN K z ∧ gN K z < 1 ∧
      0 < np_ex3F α δ K (gN K z) z - gK K z ∧
      V K z = np_ex3U θ γ (np_ex3F α δ K (gN K z) z - gK K z) (gN K z) +
        β * ∫ z', V (gK K z) z' ∂Q z)
    {K z : ℝ} (hK : 0 < K) :
    (1 - θ) * (np_ex3F α δ K (gN K z) z - gK K z) =
        θ * (1 - gN K z) * ((1 - α) * z * K ^ α * gN K z ^ (-α)) ∧
      θ * np_ex3X θ (np_ex3F α δ K (gN K z) z - gK K z) (gN K z) ^ (1 - γ) /
          (np_ex3F α δ K (gN K z) z - gK K z) = β * ∫ z', VK (gK K z) z' ∂Q z ∧
      VK K z = θ * np_ex3X θ (np_ex3F α δ K (gN K z) z - gK K z) (gN K z) ^ (1 - γ) /
          (np_ex3F α δ K (gN K z) z - gK K z) *
            (1 - δ + α * z * K ^ (α - 1) * gN K z ^ (1 - α)) ∧
      θ * np_ex3X θ (np_ex3F α δ K (gN K z) z - gK K z) (gN K z) ^ (1 - γ) /
          (np_ex3F α δ K (gN K z) z - gK K z) =
        β * ∫ z', θ * np_ex3X θ (np_ex3F α δ (gK K z) (gN (gK K z) z') z' - gK (gK K z) z')
            (gN (gK K z) z') ^ (1 - γ) /
              (np_ex3F α δ (gK K z) (gN (gK K z) z') z' - gK (gK K z) z') *
            (1 - δ + α * z' * gK K z ^ (α - 1) * gN (gK K z) z' ^ (1 - α)) ∂Q z := by
  -- (ii) capital first-order condition, at every state
  have focK : ∀ K z, θ * np_ex3X θ (np_ex3F α δ K (gN K z) z - gK K z) (gN K z) ^ (1 - γ) /
      (np_ex3F α δ K (gN K z) z - gK K z) = β * ∫ z', VK (gK K z) z' ∂Q z := by
    intro K z
    obtain ⟨h0, hN0, hN1, hc, heq⟩ := hg K z
    set F0 := np_ex3F α δ K (gN K z) z
    have hd : HasDerivAt (fun k => np_ex3U θ γ (F0 - k) (gN K z) + β * ∫ z', V k z' ∂Q z)
        (θ * np_ex3X θ (F0 - gK K z) (gN K z) ^ (1 - γ) / (F0 - gK K z) * (-1) +
          β * ∫ z', VK (gK K z) z' ∂Q z) (gK K z) := by
      have h2 := (ex_11_3_UC (θ := θ) (N := gN K z) hγ hc hN1).comp (gK K z)
        ((hasDerivAt_id' (gK K z)).const_sub F0)
      exact h2.add ((hW (gK K z) z).const_mul β)
    have hmax : IsLocalMax (fun k => np_ex3U θ γ (F0 - k) (gN K z) + β * ∫ z', V k z' ∂Q z)
        (gK K z) := by
      filter_upwards [Ioo_mem_nhds h0 (sub_pos.1 hc)] with k hk
      rw [← heq]
      exact hBell K z k (gN K z) hk.1 hN0 hN1 (sub_pos.2 hk.2)
    have := hmax.hasDerivAt_eq_zero hd
    linarith
  -- (iii) envelope condition, at every positive capital stock
  have env : ∀ K z, 0 < K → VK K z =
      θ * np_ex3X θ (np_ex3F α δ K (gN K z) z - gK K z) (gN K z) ^ (1 - γ) /
          (np_ex3F α δ K (gN K z) z - gK K z) *
            (1 - δ + α * z * K ^ (α - 1) * gN K z ^ (1 - α)) := by
    intro K z hK
    obtain ⟨h0, hN0, hN1, hc, heq⟩ := hg K z
    have hFK := ex_11_3_FK (α := α) (δ := δ) (N := gN K z) (z := z) hK
    have hlow : HasDerivAt (fun K' => np_ex3U θ γ (np_ex3F α δ K' (gN K z) z - gK K z) (gN K z) +
        β * ∫ z', V (gK K z) z' ∂Q z)
        (θ * np_ex3X θ (np_ex3F α δ K (gN K z) z - gK K z) (gN K z) ^ (1 - γ) /
          (np_ex3F α δ K (gN K z) z - gK K z) *
            (1 - δ + α * z * K ^ (α - 1) * gN K z ^ (1 - α))) K := by
      have h2 := (ex_11_3_UC (θ := θ) (N := gN K z) hγ hc hN1).comp K (hFK.sub_const (gK K z))
      simpa using h2.add_const (β * ∫ z', V (gK K z) z' ∂Q z)
    have hev : ∀ᶠ K' in 𝓝 K, 0 < np_ex3F α δ K' (gN K z) z - gK K z :=
      (hFK.sub_const (gK K z)).continuousAt.eventually (lt_mem_nhds hc)
    refine np_envelope ?_ heq.symm (hV K z hK) hlow
    filter_upwards [hev] with K' hK'
    exact hBell K' z (gK K z) (gN K z) h0 hN0 hN1 hK'
  -- (i) intratemporal condition
  have intra : (1 - θ) * (np_ex3F α δ K (gN K z) z - gK K z) =
      θ * (1 - gN K z) * ((1 - α) * z * K ^ α * gN K z ^ (-α)) := by
    obtain ⟨h0, hN0, hN1, hc, heq⟩ := hg K z
    have hFN := ex_11_3_FN (α := α) (δ := δ) (K := K) (z := z) hN0
    have hd := ex_11_3_total_N (θ := θ) hγ (hFN.sub_const (gK K z)) hc hN1
    have hd' := hd.add_const (β * ∫ z', V (gK K z) z' ∂Q z)
    have hmax : IsLocalMax (fun N => np_ex3U θ γ (np_ex3F α δ K N z - gK K z) N +
        β * ∫ z', V (gK K z) z' ∂Q z) (gN K z) := by
      have hev : ∀ᶠ N in 𝓝 (gN K z), 0 < np_ex3F α δ K N z - gK K z :=
        (hFN.sub_const (gK K z)).continuousAt.eventually (lt_mem_nhds hc)
      filter_upwards [hev, Ioo_mem_nhds hN0 hN1] with N hN hN'
      rw [← heq]
      exact hBell K z (gK K z) N h0 hN'.1 hN'.2 hN
    have h0' := hmax.hasDerivAt_eq_zero hd'
    have hX := np_ex3X_pos (θ := θ) hc hN1
    have hXg : 0 < np_ex3X θ (np_ex3F α δ K (gN K z) z - gK K z) (gN K z) ^ (1 - γ) :=
      Real.rpow_pos_of_pos hX _
    have h1N : 0 < 1 - gN K z := sub_pos.2 hN1
    have hbr : θ * ((1 - α) * z * K ^ α * gN K z ^ (-α)) / (np_ex3F α δ K (gN K z) z - gK K z) -
        (1 - θ) / (1 - gN K z) = 0 := by
      rcases mul_eq_zero.1 h0' with h | h
      · exact absurd h hXg.ne'
      · exact h
    field_simp at hbr
    linarith
  refine ⟨intra, focK K z, env K z hK, ?_⟩
  rw [focK K z]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun z' => env (gK K z) z' (hg K z).1)

/-- Exercise 11.3, the deterministic steady state (`z = 1`): the Euler equation at a steady state
`β(1 − δ + α(K/N)^{α−1}) = 1` holds iff `K/N = (α/(1/β − 1 + δ))^{1/(1−α)}`. -/
theorem ex_11_3_steady_state {α β δ x : ℝ} (hα1 : α < 1) (hx : 0 < x) (hβ : 0 < β)
    (hden : 0 < 1 / β - 1 + δ) (hα0 : 0 < α) :
    β * (1 - δ + α * x ^ (α - 1)) = 1 ↔ x = (α / (1 / β - 1 + δ)) ^ (1 / (1 - α)) := by
  have hq : 0 < α / (1 / β - 1 + δ) := div_pos hα0 hden
  have h1α : (1 - α) ≠ 0 := by linarith
  constructor
  · intro h
    have hxa : x ^ (α - 1) = (1 / β - 1 + δ) / α := by
      field_simp
      field_simp at h
      linarith
    have : x = (x ^ (α - 1)) ^ (1 / (α - 1)) := by
      rw [← Real.rpow_mul hx.le, mul_one_div_cancel (by linarith : α - 1 ≠ 0), Real.rpow_one]
    have hd' : 0 < (1 / β - 1 + δ) / α := div_pos hden hα0
    have hα1' : α - 1 ≠ 0 := by linarith
    rw [this, hxa, show α / (1 / β - 1 + δ) = ((1 / β - 1 + δ) / α)⁻¹ by rw [inv_div],
      Real.inv_rpow hd'.le, ← Real.rpow_neg hd'.le]
    congr 1
    field_simp
    ring
  · intro h
    have hxa : x ^ (α - 1) = (1 / β - 1 + δ) / α := by
      rw [h, ← Real.rpow_mul hq.le]
      have : 1 / (1 - α) * (α - 1) = -1 := by field_simp; ring
      rw [this, Real.rpow_neg_one, inv_div]
    rw [hxa]
    field_simp
    ring

end Miao.NumericalMethods.NP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The parameterized expectations approach: irreversible investment

Miao, *Economic Dynamics in Discrete Time*, §11.6.2 (pp. 381–383), (11.13)–(11.14).

With the irreversibility constraint `K' ≥ (1 − δ)K` (11.13) the first-order
conditions are `u'(f − g) − h = β∫m q`, `h(g − (1 − δ)k) = 0`,
`g − (1 − δ)k ≥ 0`, `h ≥ 0`, with
`m(k', z'; g, h) = u'(f(k', z') − g(k', z'))f'(k', z') − h(k', z')(1 − δ)`.

* `np_irreversible_kkt`: these Kuhn–Tucker conditions follow from the
  maximisation in the Bellman equation, with multiplier
  `h = u'(c) − βW'(g)`.
* `eq_11_14_envelope`: `m` is the derivative of the value function, as the text
  says ("`m` is the derivative of the value function").
* `eq_11_14_pos`: for the Cobb–Douglas technology `f(k, z) = zk^α + (1 − δ)k`,
  `m = u'(c)αzk^{α−1} + (1 − δ)e > 0` when `e = u'(c) − h ≥ 0`, which is the
  inequality in (11.14).
* PEA (p. 383): for any value `e > 0` of the conditional expectation, the
  formulas `g = max{(1 − δ)k, f − (u')⁻¹(e)}`, `h = u'(f − g) − e` give the unique
  solution of the system `u'(f − g) − h = e`, `h(g − (1 − δ)k) = 0`,
  `g ≥ (1 − δ)k`, `h ≥ 0` (`np_pea_kkt`, `np_pea_kkt_unique`). So the functional
  equation `F(e) = 0` is equivalent to the original first-order conditions.

The sufficiency of these conditions together with the transversality condition
(p. 382) is stated without proof in the text and is not formalised here.
-/

namespace Miao.NumericalMethods.NP

open Filter Topology

/-- The Kuhn–Tucker conditions under the irreversibility constraint (11.13) (Miao, p. 382),
derived from the Bellman maximisation `max_{(1−δ)k ≤ k' < f(k)} u(f(k) − k') + βW(k')` at an optimum
`g₀`: with `h = u'(c₀) − βW'(g₀)`, `c₀ = f(k) − g₀`, we have `h ≥ 0` and
`h(g₀ − (1 − δ)k) = 0`, and `u'(c₀) − h = βW'(g₀)`. -/
theorem np_irreversible_kkt {u W : ℝ → ℝ} {up : ℝ → ℝ} {W' β δ k fk g0 : ℝ}
    (hc : g0 < fk) (hlow : (1 - δ) * k ≤ g0)
    (hu : HasDerivAt u (up (fk - g0)) (fk - g0)) (hW : HasDerivAt W W' g0)
    (hmax : ∀ k', (1 - δ) * k ≤ k' → k' < fk → u (fk - k') + β * W k' ≤ u (fk - g0) + β * W g0) :
    0 ≤ up (fk - g0) - β * W' ∧ (up (fk - g0) - β * W') * (g0 - (1 - δ) * k) = 0 ∧
      up (fk - g0) - (up (fk - g0) - β * W') = β * W' := by
  set φ : ℝ → ℝ := fun k' => u (fk - k') + β * W k' with hφ
  have hd : HasDerivAt φ (up (fk - g0) * (-1) + β * W') g0 := by
    have h2 := hu.comp g0 ((hasDerivAt_id' g0).const_sub fk)
    exact h2.add (hW.const_mul β)
  -- the right-hand slope is nonpositive
  have hright : up (fk - g0) * (-1) + β * W' ≤ 0 := by
    have ht := hd.tendsto_slope_zero_right
    refine le_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hc)] with t ht'
    have hle := hmax (g0 + t) (by linarith [ht'.1]) (by linarith [ht'.2])
    simp only [smul_eq_mul, hφ]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 ht'.1.le) (by linarith)
  refine ⟨by linarith, ?_, by ring⟩
  rcases hlow.eq_or_lt with heq | hlt
  · rw [← heq, sub_self, mul_zero]
  · -- interior: a local maximum, so the derivative vanishes
    have hmaxl : IsLocalMax φ g0 := by
      filter_upwards [Ioo_mem_nhds hlt hc] with k' hk'
      exact hmax k' hk'.1.le hk'.2
    have := hmaxl.hasDerivAt_eq_zero hd
    have h0 : up (fk - g0) - β * W' = 0 := by linarith
    rw [h0, zero_mul]

/-- **(11.14)**, the envelope condition (Miao, p. 382): under (11.13), if `V(k) ≥ u(f(k) − k') +
βW(k')` for all feasible `k' ∈ [(1 − δ)k, f(k))` with equality at the optimum `g₀` for `k₀`, and
`V`, `f`, `u`, `W` are differentiable, then `V'(k₀) = u'(c₀)f'(k₀) − h(1 − δ) = m` with
`h = u'(c₀) − βW'(g₀)`. -/
theorem eq_11_14_envelope {u W V f : ℝ → ℝ} {up : ℝ → ℝ} {W' V' f' β δ k0 g0 : ℝ}
    (hc : g0 < f k0) (hlow : (1 - δ) * k0 ≤ g0)
    (hu : HasDerivAt u (up (f k0 - g0)) (f k0 - g0)) (hW : HasDerivAt W W' g0)
    (hf : HasDerivAt f f' k0) (hV : HasDerivAt V V' k0)
    (hBell : ∀ k k', (1 - δ) * k ≤ k' → k' < f k → u (f k - k') + β * W k' ≤ V k)
    (heq : V k0 = u (f k0 - g0) + β * W g0) :
    V' = up (f k0 - g0) * f' - (up (f k0 - g0) - β * W') * (1 - δ) := by
  set a : ℝ → ℝ := fun k => g0 + (1 - δ) * (k - k0) with ha
  have hda : HasDerivAt a (1 - δ) k0 := by
    have h := (((hasDerivAt_id' k0).sub_const k0).const_mul (1 - δ)).const_add g0
    rw [mul_one] at h
    exact h
  have ha0 : a k0 = g0 := by simp [ha]
  have hc' : HasDerivAt (fun k => f k - a k) (f' - (1 - δ)) k0 := hf.sub hda
  have hlowd : HasDerivAt (fun k => u (f k - a k) + β * W (a k))
      (up (f k0 - g0) * (f' - (1 - δ)) + β * (W' * (1 - δ))) k0 := by
    have h1 := hu.comp_of_eq k0 hc' (by rw [ha0])
    have h2 := hW.comp_of_eq k0 hda ha0.symm
    exact h1.add (h2.const_mul β)
  have hev : ∀ᶠ k in 𝓝 k0, a k < f k := by
    have hpos : 0 < f k0 - a k0 := by rw [ha0]; linarith
    filter_upwards [hc'.continuousAt.eventually (lt_mem_nhds hpos)] with k hk
    linarith
  have := np_envelope (V := V) (W := fun k => u (f k - a k) + β * W (a k)) ?_ ?_ hV hlowd
  · rw [this]
    ring
  · filter_upwards [hev] with k hk
    exact hBell k (a k) (by simp only [ha]; nlinarith) hk
  · simp only [ha0]
    exact heq.symm

/-- **(11.14)**, the inequality `m ≥ 0` (Miao, p. 382), for `f(k, z) = zk^α + (1 − δ)k`: with
`h = u'(c) − e`, `m = u'(c)f_k − h(1 − δ) = u'(c)αzk^{α−1} + (1 − δ)e`, which is positive when
`u'(c) > 0`, `e ≥ 0`, `k, z > 0`, `α > 0` and `δ ≤ 1`. -/
theorem eq_11_14_pos {upc e α δ k z : ℝ} (hup : 0 < upc) (he : 0 ≤ e) (hk : 0 < k) (hz : 0 < z)
    (hα : 0 < α) (hδ : δ ≤ 1) :
    upc * (α * z * k ^ (α - 1) + (1 - δ)) - (upc - e) * (1 - δ) =
        upc * (α * z * k ^ (α - 1)) + (1 - δ) * e ∧
      0 < upc * (α * z * k ^ (α - 1) + (1 - δ)) - (upc - e) * (1 - δ) := by
  have hk' : 0 < k ^ (α - 1) := Real.rpow_pos_of_pos hk _
  refine ⟨by ring, ?_⟩
  have : 0 < upc * (α * z * k ^ (α - 1)) := by positivity
  nlinarith [mul_nonneg (sub_nonneg.2 hδ) he]

/-- The PEA policy and multiplier (Miao, p. 383): `g = max{(1 − δ)k, f − (u')⁻¹(e)}` and
`h = u'(f − g) − e`; they solve the first-order system with expectation `e`. Hypotheses: `u'` is
strictly decreasing on the positive reals with inverse `(u')⁻¹` there, `e > 0` and
`f > (1 − δ)k` (positive consumption when the constraint binds). -/
theorem np_pea_kkt {up upinv : ℝ → ℝ} (hanti : StrictAntiOn up (Set.Ioi 0))
    (hinv : ∀ y, 0 < y → up (upinv y) = y ∧ 0 < upinv y) {e fk δ k : ℝ} (he : 0 < e)
    (hc : (1 - δ) * k < fk) :
    (1 - δ) * k ≤ max ((1 - δ) * k) (fk - upinv e) ∧
      0 ≤ up (fk - max ((1 - δ) * k) (fk - upinv e)) - e ∧
      (up (fk - max ((1 - δ) * k) (fk - upinv e)) - e) *
          (max ((1 - δ) * k) (fk - upinv e) - (1 - δ) * k) = 0 ∧
      0 < fk - max ((1 - δ) * k) (fk - upinv e) := by
  obtain ⟨hue, hpos⟩ := hinv e he
  refine ⟨le_max_left _ _, ?_⟩
  rcases le_total ((1 - δ) * k) (fk - upinv e) with h | h
  · rw [max_eq_right h, sub_sub_cancel, hue, sub_self, zero_mul]
    exact ⟨le_rfl, rfl, hpos⟩
  · rw [max_eq_left h, sub_self, mul_zero]
    have hlt : fk - (1 - δ) * k ≤ upinv e := by linarith
    have hpos' : 0 < fk - (1 - δ) * k := by linarith
    refine ⟨?_, rfl, hpos'⟩
    rcases hlt.eq_or_lt with h1 | h1
    · rw [h1, hue, sub_self]
    · have := hanti hpos' hpos h1
      rw [hue] at this
      linarith

/-- PEA, uniqueness (Miao, p. 383): any `(g, h)` with `u'(f − g) − h = e`, `h(g − (1 − δ)k) = 0`,
`g ≥ (1 − δ)k`, `h ≥ 0` and positive consumption is given by the PEA formulas
`g = max{(1 − δ)k, f − (u')⁻¹(e)}`, `h = u'(f − g) − e`. -/
theorem np_pea_kkt_unique {up upinv : ℝ → ℝ} (hanti : StrictAntiOn up (Set.Ioi 0))
    (hinv : ∀ y, 0 < y → up (upinv y) = y ∧ 0 < upinv y) {e fk δ k g h : ℝ} (he : 0 < e)
    (hfoc : up (fk - g) - h = e) (hcs : h * (g - (1 - δ) * k) = 0) (hg : (1 - δ) * k ≤ g)
    (hh : 0 ≤ h) (hc : 0 < fk - g) :
    g = max ((1 - δ) * k) (fk - upinv e) ∧ h = up (fk - g) - e := by
  obtain ⟨hue, hpos⟩ := hinv e he
  refine ⟨?_, by linarith⟩
  rcases hh.eq_or_lt with h0 | h0
  · -- `h = 0`: unconstrained, `f − g = (u')⁻¹(e)`
    subst h0
    have h1 : up (fk - g) = up (upinv e) := by rw [hue]; linarith
    have h2 : fk - g = upinv e := hanti.injOn hc hpos h1
    have h3 : g = fk - upinv e := by linarith
    rw [max_eq_right (by linarith), h3]
  · -- `h > 0`: the constraint binds
    have hb : g = (1 - δ) * k := by
      have := (mul_eq_zero.1 hcs).resolve_left h0.ne'
      linarith
    have h1 : up (upinv e) < up (fk - g) := by rw [hue]; linarith
    have h2 : fk - g < upinv e := by
      by_contra hcon
      push Not at hcon
      rcases hcon.eq_or_lt with h3 | h3
      · rw [h3] at h1
        exact lt_irrefl _ h1
      · exact lt_asymm h1 (hanti hpos hc h3)
    rw [max_eq_left (by linarith), hb]

end Miao.NumericalMethods.NP

set_option linter.style.longLine false
#print axioms Miao.NumericalMethods.nqQuad
#print axioms Miao.NumericalMethods.nqIsGaussRule
#print axioms Miao.NumericalMethods.nq_quad_exact_of_moments
#print axioms Miao.NumericalMethods.nq_gauss_exact
#print axioms Miao.NumericalMethods.nq_gauss_not_exact_two_mul
#print axioms Miao.NumericalMethods.nq_gauss_weights_nonneg
#print axioms Miao.NumericalMethods.nq_gauss_probability
#print axioms Miao.NumericalMethods.nq_legendre_change_of_variables
#print axioms Miao.NumericalMethods.nq_legendre_interval_exact
#print axioms Miao.NumericalMethods.nq_legendre_one_point
#print axioms Miao.NumericalMethods.nq_legendre_two_point
#print axioms Miao.NumericalMethods.nq_integral_Ioi_shift
#print axioms Miao.NumericalMethods.nq_laguerre_present_value
#print axioms Miao.NumericalMethods.nqProdQuad
#print axioms Miao.NumericalMethods.nq_prodQuad_prod
#print axioms Miao.NumericalMethods.nq_prod_gauss_exact
#print axioms Miao.NumericalMethods.nq_prodQuad_card
#print axioms Miao.NumericalMethods.nqChebNode
#print axioms Miao.NumericalMethods.nq_chebyshev_substitution
#print axioms Miao.NumericalMethods.nq_chebyshev_integrableOn
#print axioms Miao.NumericalMethods.nq_integral_cos_nat_mul
#print axioms Miao.NumericalMethods.nq_cheb_sum_cos
#print axioms Miao.NumericalMethods.nq_chebyshev_T_exact
#print axioms Miao.NumericalMethods.nq_chebyshev_exact_theta
#print axioms Miao.NumericalMethods.nq_chebyshev_exact
#print axioms Miao.NumericalMethods.nq_chebyshev_isGaussRule
#print axioms Miao.NumericalMethods.nq_normal_expectation_hermite
#print axioms Miao.NumericalMethods.nq_normal_expectation_gauss_hermite
#print axioms Miao.NumericalMethods.nq_integral_odd_eq_zero
#print axioms Miao.NumericalMethods.nq_integrable_pow_mul_exp_neg_sq
#print axioms Miao.NumericalMethods.nq_integral_exp_neg_sq
#print axioms Miao.NumericalMethods.nq_integral_sq_mul_exp_neg_sq
#print axioms Miao.NumericalMethods.nq_hermite_one_point
#print axioms Miao.NumericalMethods.nq_hermite_two_point
#print axioms Miao.NumericalMethods.nq_ar1_mean_fixed
#print axioms Miao.NumericalMethods.nq_ar1_variance_fixed
#print axioms Miao.NumericalMethods.nq_ar1_stationary_law
#print axioms Miao.NumericalMethods.nqTauchenGrid
#print axioms Miao.NumericalMethods.nq_tauchen_grid_first
#print axioms Miao.NumericalMethods.nq_tauchen_grid_last
#print axioms Miao.NumericalMethods.nq_tauchen_grid_step
#print axioms Miao.NumericalMethods.nq_tauchen_grid_symm
#print axioms Miao.NumericalMethods.nqTauchenCut
#print axioms Miao.NumericalMethods.nq_tauchen_cut_midpoint
#print axioms Miao.NumericalMethods.nq_tauchen_cut_monotone
#print axioms Miao.NumericalMethods.nq_tauchen_printed_I2_upper
#print axioms Miao.NumericalMethods.nq_tauchen_printed_IN_lower
#print axioms Miao.NumericalMethods.nqCell
#print axioms Miao.NumericalMethods.nq_cell_eq
#print axioms Miao.NumericalMethods.nq_cell_measurable
#print axioms Miao.NumericalMethods.nq_cells_sum_one
#print axioms Miao.NumericalMethods.nqTauchenProb
#print axioms Miao.NumericalMethods.nq_tauchen_law
#print axioms Miao.NumericalMethods.nq_tauchen_prob_eq
#print axioms Miao.NumericalMethods.nq_tauchen_stochastic
#print axioms Miao.NumericalMethods.nqCondDens
#print axioms Miao.NumericalMethods.nq_th_ratio
#print axioms Miao.NumericalMethods.nq_th_change_of_measure
#print axioms Miao.NumericalMethods.nq_th_conditional_expectation
#print axioms Miao.NumericalMethods.nqTHTilde
#print axioms Miao.NumericalMethods.nq_th_exact
#print axioms Miao.NumericalMethods.nq_th_rowsum_integral
#print axioms Miao.NumericalMethods.nq_th_rowsum_lt_one
#print axioms Miao.NumericalMethods.nq_normalize_stochastic
#print axioms Miao.NumericalMethods.nq_th_normalized_stochastic
#print axioms Miao.NumericalMethods.nq_sim_interval_volume
#print axioms Miao.NumericalMethods.nq_sim_unique
#print axioms Miao.NumericalMethods.nqCertEquiv
#print axioms Miao.NumericalMethods.nqQ
#print axioms Miao.NumericalMethods.eq_11_4
#print axioms Miao.NumericalMethods.eq_11_5
#print axioms Miao.NumericalMethods.nq_pert_taylor_first_order
#print axioms Miao.NumericalMethods.nq_h_hasDerivAt
#print axioms Miao.NumericalMethods.nq_h'_hasDerivAt_zero
#print axioms Miao.NumericalMethods.eq_11_7_s
#print axioms Miao.NumericalMethods.eq_11_7
#print axioms Miao.NumericalMethods.nq_Q_hasDerivAt
#print axioms Miao.NumericalMethods.nqShock
#print axioms Miao.NumericalMethods.nq_gauss_exp_integral
#print axioms Miao.NumericalMethods.nq_shock_exp
#print axioms Miao.NumericalMethods.eq_11_6_mgf
#print axioms Miao.NumericalMethods.eq_11_6
#print axioms Miao.NumericalMethods.nq_gauss_tilt
#print axioms Miao.NumericalMethods.nq_gauss_quad
#print axioms Miao.NumericalMethods.nqTilt
#print axioms Miao.NumericalMethods.nq_ex_11_2_tilt
#print axioms Miao.NumericalMethods.nq_ex_11_2_Q
#print axioms Miao.NumericalMethods.nq_ex_11_2_a
#print axioms Miao.NumericalMethods.nq_ex_11_2_b
#print axioms Miao.NumericalMethods.nq_ex_11_2_match
#print axioms Miao.NumericalMethods.ex_11_2
#print axioms Miao.NumericalMethods.ni_IsWeightingFunction
#print axioms Miao.NumericalMethods.ni_inner
#print axioms Miao.NumericalMethods.ni_Orthogonal
#print axioms Miao.NumericalMethods.ni_wnorm
#print axioms Miao.NumericalMethods.definition_11_3_1
#print axioms Miao.NumericalMethods.ni_inner_comm
#print axioms Miao.NumericalMethods.ni_inner_add_left
#print axioms Miao.NumericalMethods.ni_inner_smul_left
#print axioms Miao.NumericalMethods.ni_inner_self_nonneg
#print axioms Miao.NumericalMethods.ni_inner_sq_le
#print axioms Miao.NumericalMethods.ni_inner_self_not_homogeneous
#print axioms Miao.NumericalMethods.ni_wnorm_smul
#print axioms Miao.NumericalMethods.ni_wnorm_add_le
#print axioms Miao.NumericalMethods.ni_fhat
#print axioms Miao.NumericalMethods.ni_interpMatrix
#print axioms Miao.NumericalMethods.ni_interp_eq_iff
#print axioms Miao.NumericalMethods.ni_ssr
#print axioms Miao.NumericalMethods.ni_normal_equations
#print axioms Miao.NumericalMethods.ni_leastSquares_optimal
#print axioms Miao.NumericalMethods.ni_leastSquares_eq_interp
#print axioms Miao.NumericalMethods.ni_monomial
#print axioms Miao.NumericalMethods.ni_monomial_interpMatrix
#print axioms Miao.NumericalMethods.ni_monomial_interp_unique
#print axioms Miao.NumericalMethods.ni_monomial_interp_existsUnique
#print axioms Miao.NumericalMethods.ni_poly_interp_unique
#print axioms Miao.NumericalMethods.ni_monomials_not_orthogonal
#print axioms Miao.NumericalMethods.ni_iteratedDeriv_eval
#print axioms Miao.NumericalMethods.ni_poly_parts
#print axioms Miao.NumericalMethods.ni_legendreGen
#print axioms Miao.NumericalMethods.ni_legendre
#print axioms Miao.NumericalMethods.ni_legendre_eval_eq_iteratedDeriv
#print axioms Miao.NumericalMethods.ni_legendre_zero
#print axioms Miao.NumericalMethods.ni_legendre_natDegree_le
#print axioms Miao.NumericalMethods.ni_legendreGen_iterate_root
#print axioms Miao.NumericalMethods.ni_legendre_parts
#print axioms Miao.NumericalMethods.ni_legendre_orthogonal_low
#print axioms Miao.NumericalMethods.ni_legendre_orthogonal
#print axioms Miao.NumericalMethods.ni_affine_maps_Icc
#print axioms Miao.NumericalMethods.ni_legendre_shifted_orthogonal
#print axioms Miao.NumericalMethods.ni_integrableOn_pow_mul_exp_neg
#print axioms Miao.NumericalMethods.ni_integrableOn_poly_mul_exp_neg
#print axioms Miao.NumericalMethods.ni_tendsto_poly_mul_exp_neg
#print axioms Miao.NumericalMethods.ni_lagOp
#print axioms Miao.NumericalMethods.ni_hasDerivAt_poly_mul_exp_neg
#print axioms Miao.NumericalMethods.ni_iteratedDeriv_poly_mul_exp_neg
#print axioms Miao.NumericalMethods.ni_laguerre
#print axioms Miao.NumericalMethods.ni_laguerre_eval_eq_rodrigues
#print axioms Miao.NumericalMethods.ni_laguerre_zero
#print axioms Miao.NumericalMethods.ni_lagOp_natDegree_le
#print axioms Miao.NumericalMethods.ni_laguerre_natDegree_le
#print axioms Miao.NumericalMethods.ni_laguerre_weight
#print axioms Miao.NumericalMethods.ni_integral_lagOp
#print axioms Miao.NumericalMethods.ni_lagOp_iterate_eval_zero
#print axioms Miao.NumericalMethods.ni_laguerre_parts
#print axioms Miao.NumericalMethods.ni_laguerre_orthogonal_low
#print axioms Miao.NumericalMethods.ni_laguerre_orthogonal
#print axioms Miao.NumericalMethods.ni_integrable_pow_mul_exp_neg_sq
#print axioms Miao.NumericalMethods.ni_integrable_poly_mul_exp_neg_sq
#print axioms Miao.NumericalMethods.ni_tendsto_pow_mul_exp_neg_sq
#print axioms Miao.NumericalMethods.ni_tendsto_poly_mul_exp_neg_sq
#print axioms Miao.NumericalMethods.ni_hermOp
#print axioms Miao.NumericalMethods.ni_hasDerivAt_poly_mul_exp_neg_sq
#print axioms Miao.NumericalMethods.ni_iteratedDeriv_poly_mul_exp_neg_sq
#print axioms Miao.NumericalMethods.ni_hermite
#print axioms Miao.NumericalMethods.ni_hermite_eval_eq_rodrigues
#print axioms Miao.NumericalMethods.ni_hermite_zero
#print axioms Miao.NumericalMethods.ni_hermOp_natDegree_le
#print axioms Miao.NumericalMethods.ni_hermite_natDegree_le
#print axioms Miao.NumericalMethods.ni_hermite_weight
#print axioms Miao.NumericalMethods.ni_integral_hermOp
#print axioms Miao.NumericalMethods.ni_hermite_parts
#print axioms Miao.NumericalMethods.ni_hermite_orthogonal_low
#print axioms Miao.NumericalMethods.ni_hermite_orthogonal
#print axioms Miao.NumericalMethods.ni_cheb_recursion
#print axioms Miao.NumericalMethods.ni_cheb_cos
#print axioms Miao.NumericalMethods.ni_cheb_arccos
#print axioms Miao.NumericalMethods.ni_chebWeight
#print axioms Miao.NumericalMethods.ni_chebWeight_eq
#print axioms Miao.NumericalMethods.ni_chebWeight_isWeighting
#print axioms Miao.NumericalMethods.ni_inner_cheb_eq
#print axioms Miao.NumericalMethods.ni_cheb_orthogonal
#print axioms Miao.NumericalMethods.ni_cheb_norms
#print axioms Miao.NumericalMethods.ni_chebNode
#print axioms Miao.NumericalMethods.ni_chebNode_succ
#print axioms Miao.NumericalMethods.ni_cheb_roots
#print axioms Miao.NumericalMethods.ni_chebNode_injOn
#print axioms Miao.NumericalMethods.ni_cheb_extrema_value
#print axioms Miao.NumericalMethods.ni_cheb_extrema_injOn
#print axioms Miao.NumericalMethods.ni_cheb_abs_le_one
#print axioms Miao.NumericalMethods.ni_cheb_not_locally_const
#print axioms Miao.NumericalMethods.ni_cheb_localExtr_value
#print axioms Miao.NumericalMethods.ni_cheb_localMax_eq_one
#print axioms Miao.NumericalMethods.ni_cheb_localMin_eq_neg_one
#print axioms Miao.NumericalMethods.ni_cheb_isLocalExtrOn_iff
#print axioms Miao.NumericalMethods.ni_cheb_discrete_orthogonality
#print axioms Miao.NumericalMethods.ni_sum_fin_succ
#print axioms Miao.NumericalMethods.ni_chebPhi
#print axioms Miao.NumericalMethods.ni_chebGramDiag
#print axioms Miao.NumericalMethods.ni_chebPhi_gram
#print axioms Miao.NumericalMethods.ni_chebGramDiag_ne_zero
#print axioms Miao.NumericalMethods.ni_chebGram_isUnit
#print axioms Miao.NumericalMethods.ni_chebData
#print axioms Miao.NumericalMethods.ni_chebCoeff
#print axioms Miao.NumericalMethods.ni_chebCoeff_eq
#print axioms Miao.NumericalMethods.ni_chebCoeff_eq_ratio
#print axioms Miao.NumericalMethods.ni_chebInterpolant
#print axioms Miao.NumericalMethods.ni_chebInterpolant_nodes
#print axioms Miao.NumericalMethods.ni_chebTruncation_bound
#print axioms Miao.NumericalMethods.ni_chebInterp
#print axioms Miao.NumericalMethods.ni_chebInterp_spec
#print axioms Miao.NumericalMethods.ni_chebInterp_eq_coeff_form
#print axioms Miao.NumericalMethods.ni_lebesgueFn
#print axioms Miao.NumericalMethods.ni_lebesgue_inequality
#print axioms Miao.NumericalMethods.ni_supNorm
#print axioms Miao.NumericalMethods.ni_Theorem_11_3_1_bound
#print axioms Miao.NumericalMethods.theorem_11_3_1_counterexample
#print axioms Miao.NumericalMethods.ni_chebAngle
#print axioms Miao.NumericalMethods.ni_chebAngle_mem
#print axioms Miao.NumericalMethods.ni_cheb_deriv_cos
#print axioms Miao.NumericalMethods.ni_cheb_deriv_node
#print axioms Miao.NumericalMethods.ni_basis_mul_eq
#print axioms Miao.NumericalMethods.ni_sin_le_two_sin_half
#print axioms Miao.NumericalMethods.ni_basis_abs_le
#print axioms Miao.NumericalMethods.ni_harmonic_le
#print axioms Miao.NumericalMethods.ni_harmonic_sum_le
#print axioms Miao.NumericalMethods.ni_lebesgueFn_le
#print axioms Miao.NumericalMethods.ni_cheb_expand
#print axioms Miao.NumericalMethods.ni_dirPoly
#print axioms Miao.NumericalMethods.ni_fejPoly
#print axioms Miao.NumericalMethods.ni_jackPoly
#print axioms Miao.NumericalMethods.ni_jackK
#print axioms Miao.NumericalMethods.ni_dir
#print axioms Miao.NumericalMethods.ni_fej
#print axioms Miao.NumericalMethods.ni_dirPoly_eval
#print axioms Miao.NumericalMethods.ni_fejPoly_eval
#print axioms Miao.NumericalMethods.ni_jackK_eq
#print axioms Miao.NumericalMethods.ni_jackK_nonneg
#print axioms Miao.NumericalMethods.ni_jackK_continuous
#print axioms Miao.NumericalMethods.ni_jackK_even
#print axioms Miao.NumericalMethods.ni_jackK_periodic
#print axioms Miao.NumericalMethods.ni_jackPoly_natDegree
#print axioms Miao.NumericalMethods.ni_dir_identity
#print axioms Miao.NumericalMethods.ni_fej_identity
#print axioms Miao.NumericalMethods.ni_fej_abs_le
#print axioms Miao.NumericalMethods.ni_fej_ge
#print axioms Miao.NumericalMethods.ni_one_sub_cos_ge
#print axioms Miao.NumericalMethods.ni_fej_le
#print axioms Miao.NumericalMethods.ni_jackK_mass_ge
#print axioms Miao.NumericalMethods.ni_jackK_moment_le
#print axioms Miao.NumericalMethods.ni_conv_poly
#print axioms Miao.NumericalMethods.ni_jacksonC
#print axioms Miao.NumericalMethods.ni_jacksonC_pos
#print axioms Miao.NumericalMethods.ni_jackson_lipschitz
#print axioms Miao.NumericalMethods.ni_le_supNorm
#print axioms Miao.NumericalMethods.ni_supNorm_nonneg
#print axioms Miao.NumericalMethods.ni_supNorm_le
#print axioms Miao.NumericalMethods.ni_antideriv
#print axioms Miao.NumericalMethods.ni_antideriv_derivative
#print axioms Miao.NumericalMethods.ni_antideriv_natDegree
#print axioms Miao.NumericalMethods.ni_jackson_Ck
#print axioms Miao.NumericalMethods.theorem_11_3_1
#print axioms Miao.NumericalMethods.ni_IsSpline
#print axioms Miao.NumericalMethods.ni_spline_two_piecewise_linear
#print axioms Miao.NumericalMethods.ni_node_interval
#print axioms Miao.NumericalMethods.ni_affine_eq
#print axioms Miao.NumericalMethods.ni_linear_spline_unique
#print axioms Miao.NumericalMethods.ni_slope
#print axioms Miao.NumericalMethods.ni_linSpline
#print axioms Miao.NumericalMethods.ni_linSpline_piece
#print axioms Miao.NumericalMethods.ni_linear_spline_exists
#print axioms Miao.NumericalMethods.ni_cub
#print axioms Miao.NumericalMethods.ni_cub1
#print axioms Miao.NumericalMethods.ni_cub2
#print axioms Miao.NumericalMethods.ni_cub3
#print axioms Miao.NumericalMethods.ni_hasDerivAt_cub
#print axioms Miao.NumericalMethods.ni_hasDerivAt_cub1
#print axioms Miao.NumericalMethods.ni_hasDerivAt_cub2
#print axioms Miao.NumericalMethods.ni_cubic_condition_count
#print axioms Miao.NumericalMethods.ni_piece
#print axioms Miao.NumericalMethods.ni_CubicInterp
#print axioms Miao.NumericalMethods.ni_CubicSmooth
#print axioms Miao.NumericalMethods.ni_splineL
#print axioms Miao.NumericalMethods.ni_splineTarget
#print axioms Miao.NumericalMethods.ni_splineL_eq_iff
#print axioms Miao.NumericalMethods.ni_spline_existsUnique_of_homogeneous
#print axioms Miao.NumericalMethods.ni_cub_taylor
#print axioms Miao.NumericalMethods.ni_moment
#print axioms Miao.NumericalMethods.ni_moment_facts
#print axioms Miao.NumericalMethods.ni_moments_zero
#print axioms Miao.NumericalMethods.ni_moment_interior
#print axioms Miao.NumericalMethods.ni_naturalE
#print axioms Miao.NumericalMethods.ni_natural_homogeneous
#print axioms Miao.NumericalMethods.ni_natural_spline_existsUnique
#print axioms Miao.NumericalMethods.ni_clampedE
#print axioms Miao.NumericalMethods.ni_clamped_homogeneous
#print axioms Miao.NumericalMethods.ni_clamped_spline_existsUnique
#print axioms Miao.NumericalMethods.ni_notAKnotE
#print axioms Miao.NumericalMethods.ni_notAKnot_row
#print axioms Miao.NumericalMethods.ni_notAKnot_end
#print axioms Miao.NumericalMethods.ni_notAKnot_homogeneous
#print axioms Miao.NumericalMethods.ni_notAKnot_spline_existsUnique
#print axioms Miao.NumericalMethods.ni_notAKnot_not_unique_two
#print axioms Miao.NumericalMethods.ni_ppForm_exists
#print axioms Miao.NumericalMethods.ni_Bdeg
#print axioms Miao.NumericalMethods.ni_bspline
#print axioms Miao.NumericalMethods.ni_bspline_one
#print axioms Miao.NumericalMethods.ni_bspline_recursion
#print axioms Miao.NumericalMethods.ni_Bdeg_support
#print axioms Miao.NumericalMethods.ni_bspline_support
#print axioms Miao.NumericalMethods.ni_Bdeg_nonneg
#print axioms Miao.NumericalMethods.ni_bspline_nonneg
#print axioms Miao.NumericalMethods.ni_Bdeg_zero_on
#print axioms Miao.NumericalMethods.ni_Bdeg_piecewise_poly
#print axioms Miao.NumericalMethods.ni_bspline_piecewise_poly
#print axioms Miao.NumericalMethods.ni_bform_piecewise_poly
#print axioms Miao.NumericalMethods.ni_bookKnots
#print axioms Miao.NumericalMethods.ni_bookKnots_monotone
#print axioms Miao.NumericalMethods.ni_bookKnots_breaks
#print axioms Miao.NumericalMethods.ni_bspline_two
#print axioms Miao.NumericalMethods.ni_bspline_two_book_formula_false
#print axioms Miao.NumericalMethods.ni_tensorMatrix
#print axioms Miao.NumericalMethods.ni_tensorBasis
#print axioms Miao.NumericalMethods.ni_tensor_interpMatrix
#print axioms Miao.NumericalMethods.ni_tensorMatrix_mul
#print axioms Miao.NumericalMethods.ni_tensorMatrix_one
#print axioms Miao.NumericalMethods.ni_tensor_inverse
#print axioms Miao.NumericalMethods.ni_tensor_coeff
#print axioms Miao.NumericalMethods.ni_tensor_card
#print axioms Miao.NumericalMethods.ni_tensor_example_Φ₁
#print axioms Miao.NumericalMethods.ni_tensor_example_Φ₂
#print axioms Miao.NumericalMethods.ni_tensor_example_basis
#print axioms Miao.NumericalMethods.ni_tensor_example_X
#print axioms Miao.NumericalMethods.ni_tensor_example_Φ
#print axioms Miao.NumericalMethods.ni_tensor_example_invertible
#print axioms Miao.NumericalMethods.ex_11_1_f1_not_differentiable
#print axioms Miao.NumericalMethods.ex_11_1_f1_continuous
#print axioms Miao.NumericalMethods.ex_11_1_f2_smooth
#print axioms Miao.NumericalMethods.ni_uniformGrid
#print axioms Miao.NumericalMethods.ni_uniformGrid_strictMono
#print axioms Miao.NumericalMethods.ni_uniformGrid_ends
#print axioms Miao.NumericalMethods.ex_11_1
#print axioms Miao.NumericalMethods.ni_prod_odd_ge
#print axioms Miao.NumericalMethods.ni_prod_dist_eq
#print axioms Miao.NumericalMethods.ni_uniform_basis_lower
#print axioms Miao.NumericalMethods.ni_uniform_lebesgue_lower
#print axioms Miao.NumericalMethods.ni_uniformGrid_mem
#print axioms Miao.NumericalMethods.ni_uniformInterp
#print axioms Miao.NumericalMethods.ni_uniformInterp_apply
#print axioms Miao.NumericalMethods.ni_uniformInterp_eq_interpolate
#print axioms Miao.NumericalMethods.ni_linSpline_abs_le
#print axioms Miao.NumericalMethods.ni_uniformInterp_norm_ge
#print axioms Miao.NumericalMethods.ni_uniform_interp_not_convergent
#print axioms Miao.NumericalMethods.NP.IsMarkov
#print axioms Miao.NumericalMethods.NP.IsMarkov.mk
#print axioms Miao.NumericalMethods.NP.IsMarkov.nonneg
#print axioms Miao.NumericalMethods.NP.IsMarkov.rowsum
#print axioms Miao.NumericalMethods.NP.IsDistribution
#print axioms Miao.NumericalMethods.NP.IsDistribution.mk
#print axioms Miao.NumericalMethods.NP.IsDistribution.nonneg
#print axioms Miao.NumericalMethods.NP.IsDistribution.sum_eq_one
#print axioms Miao.NumericalMethods.NP.mulVec_apply_eq
#print axioms Miao.NumericalMethods.NP.IsMarkov.mul
#print axioms Miao.NumericalMethods.NP.IsMarkov.pow
#print axioms Miao.NumericalMethods.NP.IsMarkov.mulVec_le_mulVec
#print axioms Miao.NumericalMethods.NP.IsMarkov.mulVec_const
#print axioms Miao.NumericalMethods.NP.IsMarkov.abs_mulVec_le
#print axioms Miao.NumericalMethods.NP.IsMarkov.norm_mulVec_le
#print axioms Miao.NumericalMethods.NP.IsMarkov.abs_mulVec_sub_le
#print axioms Miao.NumericalMethods.NP.GloballyStable
#print axioms Miao.NumericalMethods.NP.IsContractionOn
#print axioms Miao.NumericalMethods.NP.IsContractionOn.mk
#print axioms Miao.NumericalMethods.NP.IsContractionOn.mapsTo
#print axioms Miao.NumericalMethods.NP.IsContractionOn.nonneg
#print axioms Miao.NumericalMethods.NP.IsContractionOn.lt_one
#print axioms Miao.NumericalMethods.NP.IsContractionOn.norm_sub_le
#print axioms Miao.NumericalMethods.NP.IsContractionOn.fixedPt_unique
#print axioms Miao.NumericalMethods.NP.IsContractionOn.iterate_mem
#print axioms Miao.NumericalMethods.NP.IsContractionOn.norm_iterate_sub_fixedPt_le
#print axioms Miao.NumericalMethods.NP.IsContractionOn.tendsto_iterate_fixedPt
#print axioms Miao.NumericalMethods.NP.IsContractionOn.exists_fixedPt
#print axioms Miao.NumericalMethods.NP.IsContractionOn.globallyStable_univ
#print axioms Miao.NumericalMethods.NP.fixedPt_le_of_le
#print axioms Miao.NumericalMethods.NP.le_fixedPt_of_le_apply
#print axioms Miao.NumericalMethods.NP.isContractionOn_of_blackwell
#print axioms Miao.NumericalMethods.NP.abs_sup'_sub_sup'_le
#print axioms Miao.NumericalMethods.NP.MDP
#print axioms Miao.NumericalMethods.NP.MDP.mk
#print axioms Miao.NumericalMethods.NP.MDP.Γ
#print axioms Miao.NumericalMethods.NP.MDP.Γ_nonempty
#print axioms Miao.NumericalMethods.NP.MDP.β
#print axioms Miao.NumericalMethods.NP.MDP.β_pos
#print axioms Miao.NumericalMethods.NP.MDP.β_lt_one
#print axioms Miao.NumericalMethods.NP.MDP.r
#print axioms Miao.NumericalMethods.NP.MDP.P
#print axioms Miao.NumericalMethods.NP.MDP.P_nonneg
#print axioms Miao.NumericalMethods.NP.MDP.P_rowsum
#print axioms Miao.NumericalMethods.NP.MDP.Feasible
#print axioms Miao.NumericalMethods.NP.MDP.IsFeasible
#print axioms Miao.NumericalMethods.NP.MDP.Policy
#print axioms Miao.NumericalMethods.NP.MDP.defaultPolicy
#print axioms Miao.NumericalMethods.NP.MDP.policy_nonempty
#print axioms Miao.NumericalMethods.NP.MDP.isDistribution_P
#print axioms Miao.NumericalMethods.NP.MDP.Pσ
#print axioms Miao.NumericalMethods.NP.MDP.Pσ_apply
#print axioms Miao.NumericalMethods.NP.MDP.isMarkov_Pσ
#print axioms Miao.NumericalMethods.NP.MDP.rσ
#print axioms Miao.NumericalMethods.NP.MDP.B
#print axioms Miao.NumericalMethods.NP.MDP.Tσ
#print axioms Miao.NumericalMethods.NP.MDP.Tσ_apply
#print axioms Miao.NumericalMethods.NP.MDP.Tσ_eq
#print axioms Miao.NumericalMethods.NP.MDP.Tσ_monotone
#print axioms Miao.NumericalMethods.NP.MDP.abs_Tσ_sub_le
#print axioms Miao.NumericalMethods.NP.MDP.isContractionOn_Tσ
#print axioms Miao.NumericalMethods.NP.MDP.vσ
#print axioms Miao.NumericalMethods.NP.MDP.isFixedPt_vσ
#print axioms Miao.NumericalMethods.NP.MDP.eq_vσ_of_isFixedPt
#print axioms Miao.NumericalMethods.NP.MDP.tendsto_iterate_Tσ
#print axioms Miao.NumericalMethods.NP.MDP.vσ_eq
#print axioms Miao.NumericalMethods.NP.MDP.norm_smul_Pσ_mulVec_le
#print axioms Miao.NumericalMethods.NP.MDP.isUnit_one_sub_smul_Pσ
#print axioms Miao.NumericalMethods.NP.MDP.vσ_eq_inv
#print axioms Miao.NumericalMethods.NP.MDP.norm_pow_smul_mulVec_le
#print axioms Miao.NumericalMethods.NP.MDP.summable_pow_smul_mulVec
#print axioms Miao.NumericalMethods.NP.MDP.iterate_Tσ_eq
#print axioms Miao.NumericalMethods.NP.MDP.iterate_Tσ_zero
#print axioms Miao.NumericalMethods.NP.MDP.vσ_eq_tsum
#print axioms Miao.NumericalMethods.NP.MDP.abs_vσ_le
#print axioms Miao.NumericalMethods.NP.MDP.T
#print axioms Miao.NumericalMethods.NP.MDP.T_apply
#print axioms Miao.NumericalMethods.NP.MDP.B_le_T
#print axioms Miao.NumericalMethods.NP.MDP.Tσ_le_T
#print axioms Miao.NumericalMethods.NP.MDP.B_mono
#print axioms Miao.NumericalMethods.NP.MDP.T_monotone
#print axioms Miao.NumericalMethods.NP.MDP.abs_B_sub_le
#print axioms Miao.NumericalMethods.NP.MDP.isContractionOn_T
#print axioms Miao.NumericalMethods.NP.MDP.IsGreedy
#print axioms Miao.NumericalMethods.NP.MDP.greedy
#print axioms Miao.NumericalMethods.NP.MDP.greedy_mem
#print axioms Miao.NumericalMethods.NP.MDP.isGreedy_greedy
#print axioms Miao.NumericalMethods.NP.MDP.greedyPolicy
#print axioms Miao.NumericalMethods.NP.MDP.isGreedy_iff_Tσ_eq_T
#print axioms Miao.NumericalMethods.NP.MDP.Tσ_eq_T_of_isGreedy
#print axioms Miao.NumericalMethods.NP.MDP.T_apply_eq_sup'
#print axioms Miao.NumericalMethods.NP.MDP.isGreatest_T
#print axioms Miao.NumericalMethods.NP.MDP.antiGreedy
#print axioms Miao.NumericalMethods.NP.MDP.antiGreedy_mem
#print axioms Miao.NumericalMethods.NP.MDP.isLeast_Tσ_antiGreedy
#print axioms Miao.NumericalMethods.NP.MDP.vstar
#print axioms Miao.NumericalMethods.NP.MDP.vσ_le_vstar
#print axioms Miao.NumericalMethods.NP.MDP.IsOptimal
#print axioms Miao.NumericalMethods.NP.MDP.isFixedPt_T_vstar
#print axioms Miao.NumericalMethods.NP.MDP.eq_vstar_of_isFixedPt
#print axioms Miao.NumericalMethods.NP.MDP.bellman_equation
#print axioms Miao.NumericalMethods.NP.MDP.tendsto_iterate_T
#print axioms Miao.NumericalMethods.NP.MDP.norm_iterate_T_sub_vstar_le
#print axioms Miao.NumericalMethods.NP.MDP.globallyStable_T
#print axioms Miao.NumericalMethods.NP.MDP.isOptimal_iff
#print axioms Miao.NumericalMethods.NP.MDP.isOptimal_iff_isGreedy
#print axioms Miao.NumericalMethods.NP.MDP.isOptimal_greedy_vstar
#print axioms Miao.NumericalMethods.NP.MDP.exists_isOptimal
#print axioms Miao.NumericalMethods.NP.MDP.subgradient_of_isGreedy
#print axioms Miao.NumericalMethods.NP.MDP.newton_step_eq_vσ
#print axioms Miao.NumericalMethods.NP.MDP.vσ_le_vσ_of_isGreedy
#print axioms Miao.NumericalMethods.NP.MDP.isOptimal_of_hpi_fixed
#print axioms Miao.NumericalMethods.NP.MDP.opi_one_step_eq_vfi
#print axioms Miao.NumericalMethods.NP.MDP.tendsto_opi_inner
#print axioms Miao.NumericalMethods.NP.np_residual_bound
#print axioms Miao.NumericalMethods.NP.np_residual_zero_iff
#print axioms Miao.NumericalMethods.NP.np_vfi_aposteriori
#print axioms Miao.NumericalMethods.NP.np_fixedPt_perturbation
#print axioms Miao.NumericalMethods.NP.MDP.np_horizonValue
#print axioms Miao.NumericalMethods.NP.MDP.np_horizonValue_const
#print axioms Miao.NumericalMethods.NP.MDP.np_iterate_T_zero_eq_max
#print axioms Miao.NumericalMethods.NP.MDP.np_hpi
#print axioms Miao.NumericalMethods.NP.MDP.np_hpi_feasible
#print axioms Miao.NumericalMethods.NP.MDP.np_hpi_mono
#print axioms Miao.NumericalMethods.NP.MDP.np_hpi_terminates
#print axioms Miao.NumericalMethods.NP.GrowthGrid
#print axioms Miao.NumericalMethods.NP.GrowthGrid.mk
#print axioms Miao.NumericalMethods.NP.GrowthGrid.kgrid
#print axioms Miao.NumericalMethods.NP.GrowthGrid.sgrid
#print axioms Miao.NumericalMethods.NP.GrowthGrid.pz
#print axioms Miao.NumericalMethods.NP.GrowthGrid.pz_markov
#print axioms Miao.NumericalMethods.NP.GrowthGrid.u
#print axioms Miao.NumericalMethods.NP.GrowthGrid.f
#print axioms Miao.NumericalMethods.NP.GrowthGrid.β
#print axioms Miao.NumericalMethods.NP.GrowthGrid.β_pos
#print axioms Miao.NumericalMethods.NP.GrowthGrid.β_lt_one
#print axioms Miao.NumericalMethods.NP.GrowthGrid.reward
#print axioms Miao.NumericalMethods.NP.GrowthGrid.trans
#print axioms Miao.NumericalMethods.NP.GrowthGrid.trans_rowsum
#print axioms Miao.NumericalMethods.NP.GrowthGrid.trans_nonneg
#print axioms Miao.NumericalMethods.NP.GrowthGrid.toMDP
#print axioms Miao.NumericalMethods.NP.GrowthGrid.toMDP_β
#print axioms Miao.NumericalMethods.NP.GrowthGrid.isFeasible
#print axioms Miao.NumericalMethods.NP.GrowthGrid.B_apply
#print axioms Miao.NumericalMethods.NP.GrowthGrid.eq_11_11
#print axioms Miao.NumericalMethods.NP.GrowthGrid.np_bellman_contraction
#print axioms Miao.NumericalMethods.NP.GrowthGrid.eq_11_10
#print axioms Miao.NumericalMethods.NP.GrowthGrid.eq_11_10_unique
#print axioms Miao.NumericalMethods.NP.GrowthGrid.np_vfi_tendsto
#print axioms Miao.NumericalMethods.NP.GrowthGrid.np_vfi_geometric
#print axioms Miao.NumericalMethods.NP.GrowthGrid.np_vfi_backward_induction
#print axioms Miao.NumericalMethods.NP.GrowthGrid.eq_11_12
#print axioms Miao.NumericalMethods.NP.GrowthGrid.eq_11_12_unique
#print axioms Miao.NumericalMethods.NP.GrowthGrid.eq_11_12_inv
#print axioms Miao.NumericalMethods.NP.GrowthGrid.np_pfi_improvement
#print axioms Miao.NumericalMethods.NP.GrowthGrid.np_pfi_stop_policy
#print axioms Miao.NumericalMethods.NP.GrowthGrid.np_pfi_stop_value
#print axioms Miao.NumericalMethods.NP.GrowthGrid.np_vstar_ge
#print axioms Miao.NumericalMethods.NP.GrowthGrid.np_pfi_terminates
#print axioms Miao.NumericalMethods.NP.GrowthGrid.np_pfi_newton
#print axioms Miao.NumericalMethods.NP.GrowthGrid.np_value_projection
#print axioms Miao.NumericalMethods.NP.GrowthGrid.np_mpi
#print axioms Miao.NumericalMethods.NP.np_growthGridExample
#print axioms Miao.NumericalMethods.NP.np_growthGridExample_vstar
#print axioms Miao.NumericalMethods.NP.FittedGrid
#print axioms Miao.NumericalMethods.NP.FittedGrid.mk
#print axioms Miao.NumericalMethods.NP.FittedGrid.kmin
#print axioms Miao.NumericalMethods.NP.FittedGrid.kmax
#print axioms Miao.NumericalMethods.NP.FittedGrid.kmin_le
#print axioms Miao.NumericalMethods.NP.FittedGrid.kgrid
#print axioms Miao.NumericalMethods.NP.FittedGrid.sgrid
#print axioms Miao.NumericalMethods.NP.FittedGrid.pz
#print axioms Miao.NumericalMethods.NP.FittedGrid.pz_markov
#print axioms Miao.NumericalMethods.NP.FittedGrid.u
#print axioms Miao.NumericalMethods.NP.FittedGrid.f
#print axioms Miao.NumericalMethods.NP.FittedGrid.β
#print axioms Miao.NumericalMethods.NP.FittedGrid.β_pos
#print axioms Miao.NumericalMethods.NP.FittedGrid.β_lt_one
#print axioms Miao.NumericalMethods.NP.FittedGrid.wt
#print axioms Miao.NumericalMethods.NP.FittedGrid.wt_nonneg
#print axioms Miao.NumericalMethods.NP.FittedGrid.wt_sum
#print axioms Miao.NumericalMethods.NP.FittedGrid.u_bdd
#print axioms Miao.NumericalMethods.NP.FittedGrid.cont
#print axioms Miao.NumericalMethods.NP.FittedGrid.obj
#print axioms Miao.NumericalMethods.NP.FittedGrid.fittedBellman
#print axioms Miao.NumericalMethods.NP.FittedGrid.cont_mono
#print axioms Miao.NumericalMethods.NP.FittedGrid.cont_add_const
#print axioms Miao.NumericalMethods.NP.FittedGrid.cont_le_norm
#print axioms Miao.NumericalMethods.NP.FittedGrid.bddAbove_obj
#print axioms Miao.NumericalMethods.NP.FittedGrid.np_fitted_contraction
#print axioms Miao.NumericalMethods.NP.FittedGrid.np_fitted_converges
#print axioms Miao.NumericalMethods.NP.np_linWeights
#print axioms Miao.NumericalMethods.NP.np_linWeights_averager
#print axioms Miao.NumericalMethods.NP.np_fittedGridExample
#print axioms Miao.NumericalMethods.NP.np_fittedGridExample_contraction
#print axioms Miao.NumericalMethods.NP.np_approx
#print axioms Miao.NumericalMethods.NP.np_residual
#print axioms Miao.NumericalMethods.NP.np_proj
#print axioms Miao.NumericalMethods.NP.np_quadIP
#print axioms Miao.NumericalMethods.NP.np_collocDir
#print axioms Miao.NumericalMethods.NP.np_momentDir
#print axioms Miao.NumericalMethods.NP.np_collocation_proj
#print axioms Miao.NumericalMethods.NP.np_collocation_iff
#print axioms Miao.NumericalMethods.NP.np_collocation_integral_degenerate
#print axioms Miao.NumericalMethods.NP.np_ls_hasFDerivAt
#print axioms Miao.NumericalMethods.NP.np_ls_foc
#print axioms Miao.NumericalMethods.NP.np_ls_affine_iff
#print axioms Miao.NumericalMethods.NP.np_ls_not_sufficient
#print axioms Miao.NumericalMethods.NP.np_galerkin_iff_orthogonal
#print axioms Miao.NumericalMethods.NP.np_galerkin_iff_ls
#print axioms Miao.NumericalMethods.NP.np_quadrature_proj_eq
#print axioms Miao.NumericalMethods.NP.np_quadrature_proj_congr
#print axioms Miao.NumericalMethods.NP.np_quadrature_iff_collocation
#print axioms Miao.NumericalMethods.NP.np_moments_iff_collocation
#print axioms Miao.NumericalMethods.NP.np_galerkin_quadrature_iff_collocation
#print axioms Miao.NumericalMethods.NP.np_regression_iff_interpolation
#print axioms Miao.NumericalMethods.NP.np_chebNode
#print axioms Miao.NumericalMethods.NP.np_footnote7_chebyshev
#print axioms Miao.NumericalMethods.NP.np_footnote7_counterexample
#print axioms Miao.NumericalMethods.NP.np_cheb_sum_T
#print axioms Miao.NumericalMethods.NP.np_cheb_not_dvd
#print axioms Miao.NumericalMethods.NP.np_cheb_discrete_orth
#print axioms Miao.NumericalMethods.NP.np_cheb_basis_det_ne_zero
#print axioms Miao.NumericalMethods.NP.np_cheb_regression_iff_collocation
#print axioms Miao.NumericalMethods.NP.np_cheb_galerkin_iff_collocation
#print axioms Miao.NumericalMethods.NP.np_cheb_tensor_orthogonal
#print axioms Miao.NumericalMethods.NP.np_growthI
#print axioms Miao.NumericalMethods.NP.np_growthF
#print axioms Miao.NumericalMethods.NP.np_growthF_iff_euler
#print axioms Miao.NumericalMethods.NP.np_crra_inverse
#print axioms Miao.NumericalMethods.NP.np_gaussHermite_change
#print axioms Miao.NumericalMethods.NP.np_growth_residual_eq_F
#print axioms Miao.NumericalMethods.NP.np_ar1_stationary_variance
#print axioms Miao.NumericalMethods.NP.np_z_bounds
#print axioms Miao.NumericalMethods.NP.np_normalize_mem_Icc
#print axioms Miao.NumericalMethods.NP.np_envelope
#print axioms Miao.NumericalMethods.NP.eq_11_8
#print axioms Miao.NumericalMethods.NP.np_ex3U
#print axioms Miao.NumericalMethods.NP.np_ex3F
#print axioms Miao.NumericalMethods.NP.np_ex3X
#print axioms Miao.NumericalMethods.NP.np_ex3X_pos
#print axioms Miao.NumericalMethods.NP.ex_11_3_UC
#print axioms Miao.NumericalMethods.NP.ex_11_3_FK
#print axioms Miao.NumericalMethods.NP.ex_11_3_FN
#print axioms Miao.NumericalMethods.NP.ex_11_3_total_N
#print axioms Miao.NumericalMethods.NP.ex_11_3_euler
#print axioms Miao.NumericalMethods.NP.ex_11_3_steady_state
#print axioms Miao.NumericalMethods.NP.np_irreversible_kkt
#print axioms Miao.NumericalMethods.NP.eq_11_14_envelope
#print axioms Miao.NumericalMethods.NP.eq_11_14_pos
#print axioms Miao.NumericalMethods.NP.np_pea_kkt
#print axioms Miao.NumericalMethods.NP.np_pea_kkt_unique
