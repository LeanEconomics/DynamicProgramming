/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NumericalMethods.NQQuadrature
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim

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
