/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveUtility.PAVolatilityPuzzles
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Independence.Basic

/-!
# Lognormal Euler equations with IID standard normal shocks

Miao, *Economic Dynamics in Discrete Time*, §20.4.3 (pp. 723–729): the Bansal–Yaron shocks
`η_{t+1}, u_{t+1}, e_{t+1}, w_{t+1}` are IID `N(0, 1)`. Here they are `ξ : Fin n → Ω → ℝ`,
independent (`iIndepFun`) with law `N(0, 1)` under the time-`t` conditional probability `P`; a
concrete instance on `ℝⁿ` with the product Gaussian measure is `pa_stdNormal_pi`.

* `E exp(c + ∑ a_k ξ_k) = exp(c + ½ ∑ a_k²)` (`pa_integral_exp_shocks`), hence an Euler
  equation `E_t exp(·) = 1` is `c + ½ ∑ a_k² = 0` (`pa_euler_shocks_iff`).
* `Cov(∑ a_k ξ_k, ∑ b_k ξ_k) = ∑ a_k b_k` (`pa_cov_shocks`).
* The lognormal risk premium: if `m = c_m + a·ξ`, `r = c_r + b·ξ`, `E_t e^{m + r} = 1` and
  `E_t e^{m + r_f} = 1`, then `E_t r − r_f = −Cov_t(m, r) − ½ Var_t(r)`
  (`pa_lognormal_premium`), the step behind (20.53), (20.54) and (20.56).
* The variance of a sum of uncorrelated terms (`pa_cov_sum_uncorrelated`), used for the
  unconditional variances of §20.4.3.
-/

namespace Miao.RecursiveUtility

open MeasureTheory ProbabilityTheory Real

/-- The coordinates of `ℝⁿ` under the product of standard normal laws are IID `N(0, 1)`: a
concrete instance of the hypotheses used in this module. -/
theorem pa_stdNormal_pi (n : ℕ) :
    iIndepFun (fun (k : Fin n) (ω : Fin n → ℝ) => ω k)
        (Measure.pi fun _ => gaussianReal 0 1) ∧
      ∀ k, HasLaw (fun ω : Fin n → ℝ => ω k) (gaussianReal 0 1)
        (Measure.pi fun _ => gaussianReal 0 1) := by
  refine ⟨iIndepFun_pi (X := fun _ x => x) fun _ => aemeasurable_id, fun k => ?_⟩
  exact ⟨(measurable_pi_apply k).aemeasurable,
    (measurePreserving_eval (fun _ : Fin n => gaussianReal (0 : ℝ) 1) k).map_eq⟩

/-- `E exp(c + ∑ a_k ξ_k) = exp(c + ½ ∑ a_k²)` for IID standard normal `ξ`. -/
theorem pa_integral_exp_shocks {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {ξ : Fin n → Ω → ℝ} (hind : iIndepFun ξ P) (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P)
    (c : ℝ) (a : Fin n → ℝ) :
    ∫ ω, Real.exp (c + ∑ k, a k * ξ k ω) ∂P = Real.exp (c + (∑ k, a k ^ 2) / 2) := by
  have hind' : iIndepFun (fun k ω => a k * ξ k ω) P :=
    hind.comp (fun k x => a k * x) fun k => measurable_const_mul (a k)
  have hmeas : ∀ k, AEMeasurable (fun ω => a k * ξ k ω) P :=
    fun k => (hlaw k).aemeasurable.const_mul (a k)
  have hmgf := hind'.mgf_sum₀ hmeas Finset.univ (t := 1)
  have hsumfun : (∑ k, fun ω => a k * ξ k ω) = fun ω => ∑ k, a k * ξ k ω := by
    funext ω; simp [Finset.sum_apply]
  rw [hsumfun] at hmgf
  have hk : ∀ k, mgf (fun ω => a k * ξ k ω) P 1 = Real.exp (a k ^ 2 / 2) := by
    intro k
    rw [mgf_const_mul, mgf_gaussianReal (hlaw k)]
    simp
  simp only [hk] at hmgf
  simp only [mgf, one_mul] at hmgf
  simp only [Real.exp_add, integral_const_mul]
  rw [hmgf, ← Real.exp_sum, Finset.sum_div]

/-- An Euler equation `E_t exp(c + ∑ a_k ξ_k) = 1` with IID standard normal shocks holds iff
`c + ½ ∑ a_k² = 0`. -/
theorem pa_euler_shocks_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {ξ : Fin n → Ω → ℝ} (hind : iIndepFun ξ P) (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P)
    (c : ℝ) (a : Fin n → ℝ) :
    ∫ ω, Real.exp (c + ∑ k, a k * ξ k ω) ∂P = 1 ↔ c + (∑ k, a k ^ 2) / 2 = 0 := by
  rw [pa_integral_exp_shocks hind hlaw, Real.exp_eq_one_iff]

/-- `Cov(∑ a_k ξ_k, ∑ b_k ξ_k) = ∑ a_k b_k` for IID standard normal `ξ`; in particular
`Var(∑ a_k ξ_k) = ∑ a_k²`. -/
theorem pa_cov_shocks {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} {ξ : Fin n → Ω → ℝ} (hind : iIndepFun ξ P)
    (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P) (a b : Fin n → ℝ) :
    cov[fun ω => ∑ k, a k * ξ k ω, fun ω => ∑ k, b k * ξ k ω; P] = ∑ k, a k * b k := by
  have hL : ∀ k, MemLp (ξ k) 2 P := fun k => (hlaw k).memLp (memLp_id_gaussianReal 2)
  rw [covariance_fun_sum_fun_sum (fun k => (hL k).const_mul (a k))
    (fun k => (hL k).const_mul (b k))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k]
  · rw [covariance_const_mul_left, covariance_const_mul_right,
      covariance_self (hlaw k).aemeasurable, (hlaw k).variance_eq, variance_id_gaussianReal]
    simp
  · intro l _ hlk
    rw [covariance_const_mul_left, covariance_const_mul_right,
      (hind.indepFun (Ne.symm hlk)).covariance_eq_zero (hL k) (hL l)]
    simp
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- The lognormal risk premium (Miao, pp. 726–727): with `m = c_m + a·ξ` (log pricing kernel),
`r = c_r + b·ξ`, the Euler equations `E_t e^{m+r} = 1` and `E_t e^{m+r_f} = 1` give
`E_t r − r_f = −Cov_t(m, r) − ½ Var_t r`, i.e. `c_r − r_f = −∑ a_k b_k − ½ ∑ b_k²`. -/
theorem pa_lognormal_premium {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {ξ : Fin n → Ω → ℝ} (hind : iIndepFun ξ P) (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P)
    {cm cr rf : ℝ} {a b : Fin n → ℝ}
    (hr : ∫ ω, Real.exp ((cm + ∑ k, a k * ξ k ω) + (cr + ∑ k, b k * ξ k ω)) ∂P = 1)
    (hf : ∫ ω, Real.exp ((cm + ∑ k, a k * ξ k ω) + rf) ∂P = 1) :
    cr - rf = -(∑ k, a k * b k) - (∑ k, b k ^ 2) / 2 := by
  have hr' : ∫ ω, Real.exp ((cm + cr) + ∑ k, (a k + b k) * ξ k ω) ∂P = 1 := by
    rw [← hr]
    congr 1
    funext ω
    congr 1
    simp only [add_mul, Finset.sum_add_distrib]
    ring
  have hf' : ∫ ω, Real.exp ((cm + rf) + ∑ k, a k * ξ k ω) ∂P = 1 := by
    rw [← hf]
    congr 1
    funext ω
    congr 1
    ring
  rw [pa_euler_shocks_iff hind hlaw] at hr' hf'
  have : ∑ k, (a k + b k) ^ 2 = ∑ k, a k ^ 2 + 2 * ∑ k, a k * b k + ∑ k, b k ^ 2 := by
    simp only [add_sq, Finset.sum_add_distrib, Finset.mul_sum]
    exact congrArg₂ _ (congrArg₂ _ rfl (Finset.sum_congr rfl fun k _ => by ring)) rfl
  rw [this] at hr'
  linarith

/-- The variance of a sum of pairwise uncorrelated square-integrable terms is the sum of their
variances: `Cov(∑ Y_k, ∑ Y_k) = ∑ Cov(Y_k, Y_k)`. -/
theorem pa_cov_sum_uncorrelated {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ}
    {Y : Fin n → Ω → ℝ} (hY : ∀ k, MemLp (Y k) 2 P)
    (hunc : ∀ k l, k ≠ l → cov[Y k, Y l; P] = 0) :
    cov[fun ω => ∑ k, Y k ω, fun ω => ∑ k, Y k ω; P] = ∑ k, cov[Y k, Y k; P] := by
  rw [covariance_fun_sum_fun_sum hY hY]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k (fun l _ hlk => hunc k l (Ne.symm hlk))
    (fun h => absurd (Finset.mem_univ k) h)]

end Miao.RecursiveUtility
