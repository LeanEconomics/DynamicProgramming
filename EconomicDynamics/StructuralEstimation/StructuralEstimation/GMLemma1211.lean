/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StructuralEstimation.GMProbability
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.CramerWold

/-!
# Lemma 12.1.1: the central limit theorem for `√T g_T(θ₀)` (Miao, §12.1, p. 391)

Miao, p. 391, Lemma 12.1.1: under Assumptions 12.1.1, 12.1.5 and 12.1.9,
`√T g_T(θ₀) →d N(0, S)`. The book cites this (Hall 2005); it does **not** follow from
stationarity, ergodicity and a finite positive definite long-run variance alone (a CLT for
stationary ergodic sequences needs further dependence conditions, e.g. martingale differences
or mixing; Herrndorf 1983 constructs stationary ergodic sequences with finite long-run variance
that violate the CLT). `theorem_12_1_2` therefore takes the CLT as an explicit hypothesis; this
module proves it in the i.i.d. case, where `S = E h h'` (`lemma_12_1_1_iid`), via the
Cramér–Wold device and Mathlib's one-dimensional central limit theorem. With `S` the covariance
matrix `gm_covMat`, which is positive semidefinite (`gm_covMat_posSemidef`).
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- The second-moment matrix `S = E[u(x₀) u(x₀)']` (the covariance matrix when `E u = 0`). -/
noncomputable def gm_covMat {q : ℕ} (P : Measure Ω) (X : ℕ → Ω → E) (u : E → Fin q → ℝ) :
    Matrix (Fin q) (Fin q) ℝ :=
  Matrix.of fun i j => ∫ ω, u (X 0 ω) i * u (X 0 ω) j ∂P

omit [MeasurableSpace E] in
/-- `t'St = E[(t'u(x₀))²]`. -/
theorem gm_covMat_quad {q : ℕ} {P : Measure Ω} {X : ℕ → Ω → E} {u : E → Fin q → ℝ}
    (hL2 : ∀ i, MemLp (fun ω => u (X 0 ω) i) 2 P) (t : Fin q → ℝ) :
    t ⬝ᵥ (gm_covMat P X u).mulVec t = ∫ ω, (∑ i, t i * u (X 0 ω) i) ^ 2 ∂P := by
  have hint : ∀ i j, Integrable (fun ω => u (X 0 ω) i * u (X 0 ω) j) P := fun i j =>
    (hL2 i).integrable_mul (hL2 j)
  have hsq : (fun ω => (∑ i, t i * u (X 0 ω) i) ^ 2) =
      fun ω => ∑ i, ∑ j, t i * t j * (u (X 0 ω) i * u (X 0 ω) j) := by
    funext ω
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hsq, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (hint i j).const_mul _]
  simp only [dotProduct, Matrix.mulVec, gm_covMat, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (hint i j).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  ring

omit [MeasurableSpace E] in
/-- Miao, Assumption 12.1.9: the second-moment matrix `E[u u']` is positive semidefinite. -/
theorem gm_covMat_posSemidef {q : ℕ} {P : Measure Ω} {X : ℕ → Ω → E} {u : E → Fin q → ℝ}
    (hL2 : ∀ i, MemLp (fun ω => u (X 0 ω) i) 2 P) : (gm_covMat P X u).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun t => ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [gm_covMat, Matrix.of_apply, star_trivial]
    exact integral_congr_ae (ae_of_all _ fun ω => mul_comm _ _)
  · rw [star_trivial, gm_covMat_quad hL2]
    exact integral_nonneg fun ω => sq_nonneg _

/-- `√T · T⁻¹ = (√T)⁻¹`. -/
theorem gm_sqrt_mul_inv (x : ℝ) (hx : 0 ≤ x) : Real.sqrt x * x⁻¹ = (Real.sqrt x)⁻¹ := by
  rcases hx.eq_or_lt with h | h
  · simp [← h]
  · have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 h).ne'
    rw [show x⁻¹ = (Real.sqrt x)⁻¹ * (Real.sqrt x)⁻¹ by rw [← mul_inv, Real.mul_self_sqrt hx],
      ← mul_assoc, mul_inv_cancel₀ hs, one_mul]

/-- **Lemma 12.1.1** in the i.i.d. case (Miao, p. 391). If `x_t` are i.i.d. and
`u(x) = h(x, θ₀)` has `E u(x₀) = 0` and finite second moments, then
`√T g_T(θ₀) →d N(0, S)` with `S = E[u(x₀)u(x₀)']` (here the long-run variance of
Assumption 12.1.9 is `S = Γ₀`). Proved by the Cramér–Wold device from Mathlib's central limit
theorem. This shows the CLT hypothesis of `theorem_12_1_2` is satisfiable. -/
theorem lemma_12_1_1_iid {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → E}
    (hX : ∀ n, Measurable (X n)) (hind : iIndepFun X P) (hid : ∀ n, IdentDistrib (X n) (X 0) P P)
    {k q : ℕ} {h : E → (Fin k → ℝ) → Fin q → ℝ} {θ₀ : Fin k → ℝ}
    (hu : Measurable fun x => h x θ₀) (hL2 : ∀ i, MemLp (fun ω => h (X 0 ω) θ₀ i) 2 P)
    (hmean : ∀ i, ∫ ω, h (X 0 ω) θ₀ i ∂P = 0) :
    TendstoInDistribution
      (fun (T : ℕ) ω => gm_toE (Real.sqrt (T : ℝ) • gm_sampleMoment X h T ω θ₀)) atTop id
      (fun _ => P) (multivariateGaussian 0 (gm_covMat P X fun x => h x θ₀)) := by
  set u : E → Fin q → ℝ := fun x => h x θ₀ with hudef
  set S := gm_covMat P X u with hSdef
  have hS : S.PosSemidef := gm_covMat_posSemidef hL2
  have hui : ∀ i, Measurable fun x => u x i := fun i => measurable_pi_iff.1 hu i
  have hmeas : ∀ T : ℕ, AEMeasurable
      (fun ω => gm_toE (Real.sqrt (T : ℝ) • gm_sampleMoment X h T ω θ₀)) P := by
    intro T
    have hg : Measurable fun ω => gm_sampleMoment X h T ω θ₀ := measurable_pi_iff.2 fun i =>
      measurable_const.mul (Finset.measurable_fun_sum _ fun t _ => (hui i).comp (hX t))
    exact ((gm_continuous_toE q).measurable.comp (hg.const_smul (Real.sqrt (T : ℝ)))).aemeasurable
  rw [tendstoInDistribution_iff_tendstoInDistribution_inner aemeasurable_id hmeas]
  intro t
  set f : E → ℝ := fun x => ∑ i, t.ofLp i * u x i with hfdef
  have hfm : Measurable f := Finset.measurable_fun_sum _ fun i _ => measurable_const.mul (hui i)
  set Y : ℕ → Ω → ℝ := fun s ω => f (X s ω) with hYdef
  have hY0L2 : MemLp (Y 0) 2 P := by
    have := memLp_finsetSum' (μ := P) (p := 2) Finset.univ
      (f := fun i ω => t.ofLp i * u (X 0 ω) i) fun i _ => (hL2 i).const_mul _
    convert this using 1
    funext ω
    simp [hYdef, hfdef]
  have hY0mean : ∫ ω, Y 0 ω ∂P = 0 := by
    simp only [hYdef, hfdef]
    rw [integral_finsetSum _ fun i _ => ((hL2 i).integrable one_le_two).const_mul _]
    simp [integral_const_mul, hmean]
  have hvar : Var[Y 0; P] = t.ofLp ⬝ᵥ S.mulVec t.ofLp := by
    rw [variance_of_integral_eq_zero (X := Y 0) (hfm.comp (hX 0)).aemeasurable hY0mean, hSdef,
      gm_covMat_quad hL2]
  -- the law of `⟪Z, t⟫` for `Z ~ N(0, S)`
  have hlaw : HasLaw (fun z : EuclideanSpace ℝ (Fin q) => inner ℝ z t)
      (gaussianReal 0 Var[Y 0; P].toNNReal) (multivariateGaussian 0 S) := by
    refine ⟨by fun_prop, ?_⟩
    have hL := IsGaussian.map_eq_gaussianReal (μ := multivariateGaussian 0 S) (innerSL ℝ t)
    have hm0 : ∫ z, (innerSL ℝ t) z ∂(multivariateGaussian 0 S) = 0 := by
      rw [ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id,
        integral_id_multivariateGaussian, map_zero]
    have hfun : (⇑(innerSL ℝ t) : EuclideanSpace ℝ (Fin q) → ℝ) = fun z => inner ℝ z t := by
      funext z
      rw [innerSL_apply_apply, real_inner_comm]
    have hfun' : (⇑(innerSL ℝ t) : EuclideanSpace ℝ (Fin q) → ℝ) = fun z => inner ℝ t z := by
      funext z
      rw [innerSL_apply_apply]
    have hv0 : Var[⇑(innerSL ℝ t); multivariateGaussian 0 S] =
        t.ofLp ⬝ᵥ S.mulVec t.ofLp := by
      have hc := covarianceBilin_self (μ := multivariateGaussian 0 S) IsGaussian.memLp_two_id t
      rw [covarianceBilin_multivariateGaussian hS] at hc
      rw [hfun', ← hc]
    rw [hm0, hv0, ← hvar, hfun] at hL
    exact hL
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub hlaw hY0L2
    (hind.comp (fun _ => f) fun _ => hfm) fun s => (hid s).comp hfm
  rw [hY0mean] at hclt
  have heq : (fun (T : ℕ) ω =>
      inner ℝ (gm_toE (Real.sqrt (T : ℝ) • gm_sampleMoment X h T ω θ₀)) t) =
      fun (T : ℕ) ω => (Real.sqrt (T : ℝ))⁻¹ * (∑ s ∈ Finset.range T, Y s ω - T * 0) := by
    funext T ω
    rw [mul_zero, sub_zero, ← gm_sqrt_mul_inv T (Nat.cast_nonneg T)]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, gm_toE, star_trivial, dotProduct,
      Pi.smul_apply, smul_eq_mul, gm_sampleMoment, hYdef, hfdef, hudef, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => by ring
  rw [heq]
  exact hclt

end Miao.StructuralEstimation
