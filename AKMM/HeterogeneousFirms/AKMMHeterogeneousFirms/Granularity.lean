/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Idiosyncratic shocks and aggregate volatility (AKMM §22.7, (22.30))

AKMM, §22.7, pp. 681–682. GDP is the sum of the outputs of `N` firms, and firm growth rates
`σεᵢ` have `εᵢ` with variance one and no correlation across firms (the book assumes i.i.d.).

* GDP growth is the share-weighted average of firm growth (`granular_growth`).
* **(22.30)**: `σ_Y = σ √(Σ (yᵢ/Y)²)` (`eq_22_30`).
* **Equal sizes**: `σ_Y = σ/√N` (`granular_equal_sizes`), and `√(10⁶) = 1000` (p. 682); equal
  sizes give the smallest volatility for given `N` (`granular_herfindahl_ge`).
* Gabaix's result under Zipf's law (`σ_Y log N` converges in distribution) is not formalised (a
  generalised central limit theorem, beyond the text, decision 5); the parts that need no stable
  laws (i.i.d. sizes, the rank-size rule) are in `GranularLimits`.
-/

open MeasureTheory ProbabilityTheory

namespace AKMM.HeterogeneousFirms

/-- AKMM, p. 682: if `y_{i,t+1} = yᵢ(1 + σεᵢ)`, GDP growth `(Y_{t+1} − Y_t)/Y_t` is
`Σᵢ (yᵢ/Y)σεᵢ`. -/
theorem granular_growth {ι : Type*} [Fintype ι] (y e : ι → ℝ) (σ : ℝ) (hY : ∑ i, y i ≠ 0) :
    (∑ i, y i * (1 + σ * e i) - ∑ i, y i) / ∑ i, y i = ∑ i, y i / (∑ j, y j) * (σ * e i) := by
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by field_simp; ring

/-- AKMM, (22.30), p. 682: **aggregate volatility**. With firm shocks `εᵢ` of unit variance and
uncorrelated across firms, the variance of GDP growth `Σ sᵢσεᵢ` is `σ² Σ sᵢ²`, so its standard
deviation is `σ √(Σ sᵢ²)`, `sᵢ = yᵢ/Y`. -/
theorem eq_22_30 {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    [Fintype ι] [DecidableEq ι] {e : ι → Ω → ℝ} (he : ∀ i, MemLp (e i) 2 P)
    (hcov : ∀ i j, cov[(e i), (e j); P] = if i = j then 1 else 0) (s : ι → ℝ) {σ : ℝ}
    (hσ : 0 ≤ σ) :
    Var[(fun ω => ∑ i, s i * (σ * e i ω)); P] = σ ^ 2 * ∑ i, s i ^ 2 ∧
      Real.sqrt (Var[(fun ω => ∑ i, s i * (σ * e i ω)); P]) = σ * Real.sqrt (∑ i, s i ^ 2) := by
  have hX : ∀ i, MemLp (fun ω => s i * (σ * e i ω)) 2 P := fun i =>
    ((he i).const_mul σ).const_mul (s i)
  have hv : Var[(fun ω => ∑ i, s i * (σ * e i ω)); P] = σ ^ 2 * ∑ i, s i ^ 2 := by
    rw [variance_fun_sum hX]
    have hc : ∀ i j, cov[(fun ω => s i * (σ * e i ω)), (fun ω => s j * (σ * e j ω)); P] =
        if i = j then σ ^ 2 * s i ^ 2 else 0 := fun i j => by
      have e1 : (fun ω => s i * (σ * e i ω)) = fun ω => (s i * σ) * e i ω := by
        funext ω; ring
      have e2 : (fun ω => s j * (σ * e j ω)) = fun ω => (s j * σ) * e j ω := by
        funext ω; ring
      rw [e1, e2, covariance_const_mul_left, covariance_const_mul_right, hcov]
      split_ifs with h
      · subst h; ring
      · ring
    simp only [hc, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [Finset.mul_sum]
  refine ⟨hv, ?_⟩
  rw [hv, Real.sqrt_mul (sq_nonneg σ), Real.sqrt_sq hσ]

/-- AKMM, p. 682: **equal sizes**: with `sᵢ = 1/N`, `σ √(Σ sᵢ²) = σ/√N`. -/
theorem granular_equal_sizes {N : ℕ} (hN : 0 < N) (σ : ℝ) :
    σ * Real.sqrt (∑ _i : Fin N, (1 / (N : ℝ)) ^ 2) = σ / Real.sqrt N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    show (N : ℝ) * (1 / (N : ℝ)) ^ 2 = 1 / N by field_simp, Real.sqrt_div' _ hN'.le,
    Real.sqrt_one]
  ring

/-- AKMM, p. 682: with one million firms, `1/√N = 0.001`. -/
theorem granular_million : 1 / Real.sqrt (1000000 : ℝ) = 0.001 := by
  rw [show (1000000 : ℝ) = 1000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-- AKMM, p. 682: **equal sizes minimise aggregate volatility**: shares summing to one have
`Σ sᵢ² ≥ 1/N` (Cauchy–Schwarz), with equality at `sᵢ = 1/N`. -/
theorem granular_herfindahl_ge {N : ℕ} (hN : 0 < N) (s : Fin N → ℝ) (hs : ∑ i, s i = 1) :
    1 / (N : ℝ) ≤ ∑ i, s i ^ 2 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h0 : 0 ≤ ∑ i, (s i - 1 / N) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have e : ∑ i, (s i - 1 / N) ^ 2 = ∑ i, s i ^ 2 - 2 / N * ∑ i, s i + N * (1 / N) ^ 2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
    congr 1; congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, hs] at h0
  have : (N : ℝ) * (1 / N) ^ 2 = 1 / N := by field_simp
  rw [this] at h0
  have : 2 / (N : ℝ) * 1 = 2 * (1 / N) := by ring
  linarith

end AKMM.HeterogeneousFirms
