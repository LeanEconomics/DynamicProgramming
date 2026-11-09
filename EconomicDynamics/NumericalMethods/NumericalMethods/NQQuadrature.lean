/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Topology.Algebra.Polynomial

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
