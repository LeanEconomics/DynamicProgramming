/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LinearQuadratic.RCHall
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Integral.Pi

/-!
# The standard normal shock satisfies the Gaussian identity

Miao, §9.6, pp. 321–322: the shocks are IID standard normal. Here we prove that the standard
normal law `N(0, I) = Measure.pi fun _ => gaussianReal 0 1` on `ℝ^{nε}` satisfies the moment
generating identity `RCGaussian` used in `RCRobustLQ`, for every symmetric `K` with `I − K > 0`
and every `b`:
`E exp(½ε'Kε + b'ε) = det(I − K)^{−1/2} exp(½b'(I − K)⁻¹b)`.

* `rc_gauss_1d`: the one-dimensional case, `E exp(½kx² + cx) = (1 − k)^{−1/2} exp(c²/(2(1 − k)))`
  for `k < 1`, by writing `π(x)exp(½kx² + cx)` as a multiple of the `N(c/(1 − k), 1/(1 − k))`
  density.
* `rc_std_map_eigen`: `N(0, I)` is invariant under the orthogonal eigenvector matrix `U` of `K`
  (from Mathlib's `stdGaussian` and its independence of the orthonormal basis).
* `rc_gaussian_std`: rotating by `U` diagonalises `K`, the integral factors into one-dimensional
  integrals, and `∏(1 − λᵢ) = det(I − K)`, `∑cᵢ²/(1 − λᵢ) = b'(I − K)⁻¹b` with `c = U'b`.
* Corollaries for the standard normal shock: `rc_R_quad_std`, `eq_9_51_9_55_std`,
  `rc_robust_bellman_std`, `ex_9_5_bellman_std`.
-/

open Matrix MeasureTheory ProbabilityTheory Real

namespace Miao.LinearQuadratic

/-- The one-dimensional Gaussian integral: for `k < 1`,
`E exp(½kx² + cx) = (1 − k)^{−1/2} exp(c²/(2(1 − k)))` under `N(0, 1)`. -/
theorem rc_gauss_1d {k : ℝ} (hk : k < 1) (c : ℝ) :
    Integrable (fun x => exp (1 / 2 * k * x ^ 2 + c * x)) (gaussianReal 0 1) ∧
      ∫ x, exp (1 / 2 * k * x ^ 2 + c * x) ∂(gaussianReal 0 1) =
        (√(1 - k))⁻¹ * exp (c ^ 2 / (2 * (1 - k))) := by
  have ha : 0 < 1 - k := by linarith
  have hv : (((1 - k)⁻¹).toNNReal : ℝ) = (1 - k)⁻¹ := Real.coe_toNNReal _ (inv_nonneg.2 ha.le)
  have hv0 : ((1 - k)⁻¹).toNNReal ≠ 0 := by
    intro h
    have := congrArg (fun z : NNReal => (z : ℝ)) h
    simp only [hv, NNReal.coe_zero] at this
    exact (inv_pos.2 ha).ne' this
  have hs : 0 < √(1 - k) := Real.sqrt_pos.2 ha
  have hpi : 0 < √(2 * π) := Real.sqrt_pos.2 (by positivity)
  have key : ∀ x, gaussianPDFReal 0 1 x * exp (1 / 2 * k * x ^ 2 + c * x) =
      ((√(1 - k))⁻¹ * exp (c ^ 2 / (2 * (1 - k)))) *
        gaussianPDFReal (c / (1 - k)) ((1 - k)⁻¹).toNNReal x := by
    intro x
    simp only [gaussianPDFReal, hv, NNReal.coe_one, mul_one, sub_zero]
    rw [Real.sqrt_mul (show (0 : ℝ) ≤ 2 * π by positivity) ((1 - k)⁻¹), Real.sqrt_inv]
    have h2 : 0 < √(2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
    have h3 : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
    have e : -x ^ 2 / 2 + (1 / 2 * k * x ^ 2 + c * x) =
        c ^ 2 / (2 * (1 - k)) + -(x - c / (1 - k)) ^ 2 / (2 * (1 - k)⁻¹) := by
      field_simp
      ring
    rw [mul_assoc, ← exp_add, e, exp_add]
    field_simp
  refine ⟨?_, ?_⟩
  · rw [gaussianReal_of_var_ne_zero _ one_ne_zero, integrable_withDensity_iff_integrable_smul'
      (measurable_gaussianPDF 0 1) (ae_of_all _ fun _ => gaussianPDF_lt_top)]
    simp only [toReal_gaussianPDF, smul_eq_mul, key]
    exact (integrable_gaussianPDFReal _ _).const_mul _
  · rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
    simp only [smul_eq_mul, key]
    rw [integral_const_mul, integral_gaussianPDFReal_eq_one _ hv0, mul_one]

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The standard normal law on `ℝ^{nε}` is invariant under the orthogonal eigenvector matrix of a
symmetric matrix: `(U·)_*N(0, I) = N(0, I)`. -/
theorem rc_std_map_eigen {K : Matrix E E ℝ} (hK : K.IsHermitian) :
    (Measure.pi fun _ : E => gaussianReal 0 1).map
        (fun x => (hK.eigenvectorUnitary : Matrix E E ℝ) *ᵥ x) =
      Measure.pi fun _ : E => gaussianReal 0 1 := by
  set ν := Measure.pi fun _ : E => gaussianReal 0 1
  set U : Matrix E E ℝ := (hK.eigenvectorUnitary : Matrix E E ℝ)
  have hΦ : (fun x : E → ℝ => ∑ i, x i • hK.eigenvectorBasis i) =
      (WithLp.toLp 2 : (E → ℝ) → EuclideanSpace ℝ E) ∘ fun x => U *ᵥ x := by
    funext x
    ext j
    simp [U, mulVec, dotProduct, mul_comm]
  have hto : Measurable (WithLp.toLp 2 : (E → ℝ) → EuclideanSpace ℝ E) := by fun_prop
  have hof : Measurable (WithLp.ofLp : EuclideanSpace ℝ E → (E → ℝ)) := by fun_prop
  have hT : Measurable fun x : E → ℝ => U *ᵥ x :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have h1 := map_pi_eq_stdGaussian (ι := E)
  rw [stdGaussian_eq_map_pi_orthonormalBasis hK.eigenvectorBasis, hΦ,
    ← Measure.map_map hto hT] at h1
  have h2 := congrArg (fun m : Measure (EuclideanSpace ℝ E) => m.map WithLp.ofLp) h1
  simp only [Measure.map_map hof hto] at h2
  have hid : (WithLp.ofLp : EuclideanSpace ℝ E → (E → ℝ)) ∘ WithLp.toLp 2 = id := by
    funext x; rfl
  rw [hid, Measure.map_id, Measure.map_id] at h2
  exact h2.symm

/-- **The standard normal shock satisfies `RCGaussian`** (Miao, p. 321): for symmetric `K` with
`I − K > 0`, `E exp(½ε'Kε + b'ε) = det(I − K)^{−1/2} exp(½b'(I − K)⁻¹b)` under
`ε ~ N(0, I)`, with the integrand integrable. -/
theorem rc_gaussian_std : RCGaussian (Measure.pi fun _ : E => gaussianReal 0 1) := by
  set ν := Measure.pi fun _ : E => gaussianReal 0 1 with hνdef
  have key : ∀ (K : Matrix E E ℝ) (b : E → ℝ), Kᵀ = K → (1 - K).PosDef →
      Integrable (fun e => exp (1 / 2 * (e ⬝ᵥ (K *ᵥ e)) + b ⬝ᵥ e)) ν ∧
      ∫ e, exp (1 / 2 * (e ⬝ᵥ (K *ᵥ e)) + b ⬝ᵥ e) ∂ν =
        (Real.sqrt (1 - K).det)⁻¹ * exp (1 / 2 * (b ⬝ᵥ ((1 - K)⁻¹ *ᵥ b))) := by
    intro K b hKs hpos
    have hK : K.IsHermitian := by
      rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact hKs
    set U : Matrix E E ℝ := (hK.eigenvectorUnitary : Matrix E E ℝ) with hUdef
    set lam := hK.eigenvalues
    have hstar : star U = Uᵀ := by
      rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
    have hUU : Uᵀ * U = 1 := by rw [← hstar]; exact Unitary.coe_star_mul_self _
    have hUU' : U * Uᵀ = 1 := by rw [← hstar]; exact Unitary.coe_mul_star_self _
    have hD : Uᵀ * K * U = diagonal lam := by
      have h2 := hK.conjStarAlgAut_star_eigenvectorUnitary
      simp only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star] at h2
      rw [← hstar]
      simpa using h2
    have hKU : K = U * diagonal lam * Uᵀ := by
      rw [← hD, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hUU', Matrix.one_mul, Matrix.mul_assoc,
        hUU', Matrix.mul_one]
    set c := Uᵀ *ᵥ b
    -- the quadratic form in the rotated coordinates
    have hquad : ∀ x : E → ℝ, (U *ᵥ x) ⬝ᵥ (K *ᵥ (U *ᵥ x)) = ∑ i, lam i * x i ^ 2 := by
      intro x
      rw [← SS.LQProblem.dotProduct_transpose_mul_mul, hD]
      simp only [dotProduct, mulVec_diagonal]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hlin : ∀ x : E → ℝ, b ⬝ᵥ (U *ᵥ x) = ∑ i, c i * x i := by
      intro x
      rw [dotProduct_mulVec, ← mulVec_transpose]
      rfl
    have hlam : ∀ i, lam i < 1 := by
      intro i
      set v := U *ᵥ Pi.single i (1 : ℝ)
      have hv : v ≠ 0 := by
        intro h0
        have : Uᵀ *ᵥ v = Pi.single i 1 := by
          simp only [v, mulVec_mulVec, hUU, one_mulVec]
        rw [h0, mulVec_zero] at this
        have := congrFun this i
        simp at this
      have h := (SS.LQProblem.posDef_iff_real.1 hpos).2 hv
      have hvv : v ⬝ᵥ v = 1 := by
        have : v ⬝ᵥ ((1 : Matrix E E ℝ) *ᵥ v) = Pi.single i (1 : ℝ) ⬝ᵥ
            ((Uᵀ * 1 * U) *ᵥ Pi.single i 1) :=
          SS.LQProblem.dotProduct_transpose_mul_mul U 1 _ |>.symm
        rw [one_mulVec, Matrix.mul_one, hUU, one_mulVec] at this
        rw [this]
        simp
      rw [sub_mulVec, one_mulVec, dotProduct_sub, hvv, hquad] at h
      have hs : ∑ j, lam j * (Pi.single i (1 : ℝ) : E → ℝ) j ^ 2 = lam i := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj; simp [hj]
        · simp
      linarith
    have h1d := fun i => rc_gauss_1d (hlam i) (c i)
    have hFT : (fun e => exp (1 / 2 * (e ⬝ᵥ (K *ᵥ e)) + b ⬝ᵥ e)) ∘ (fun x => U *ᵥ x) =
        fun x => ∏ i, exp (1 / 2 * lam i * x i ^ 2 + c i * x i) := by
      funext x
      simp only [Function.comp_apply, hquad, hlin, ← Real.exp_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    have hT : Measurable fun x : E → ℝ => U *ᵥ x :=
      (Continuous.matrix_mulVec continuous_const continuous_id).measurable
    have hFc : Continuous fun e : E → ℝ => exp (1 / 2 * (e ⬝ᵥ (K *ᵥ e)) + b ⬝ᵥ e) := by
      fun_prop
    have hmap := rc_std_map_eigen hK
    rw [← hνdef, ← hUdef] at hmap
    have hint : Integrable (fun e => exp (1 / 2 * (e ⬝ᵥ (K *ᵥ e)) + b ⬝ᵥ e)) ν := by
      rw [← hmap, integrable_map_measure hFc.aestronglyMeasurable hT.aemeasurable, hFT]
      exact Integrable.fintype_prod fun i => (h1d i).1
    refine ⟨hint, ?_⟩
    rw [← hmap, integral_map hT.aemeasurable hFc.aestronglyMeasurable]
    have e1 : ∫ x, exp (1 / 2 * ((U *ᵥ x) ⬝ᵥ (K *ᵥ (U *ᵥ x))) + b ⬝ᵥ (U *ᵥ x)) ∂ν =
        ∫ x, ∏ i, exp (1 / 2 * lam i * x i ^ 2 + c i * x i) ∂ν := by
      rw [← hFT]; rfl
    rw [e1, integral_fintype_prod_eq_prod (fun i x => exp (1 / 2 * lam i * x ^ 2 + c i * x))]
    simp only [fun i => (h1d i).2]
    -- the determinant and the exponent
    have h1K : 1 - K = U * diagonal (fun i => 1 - lam i) * Uᵀ := by
      rw [hKU, show (diagonal fun i => 1 - lam i) = 1 - diagonal lam by
        ext i j; by_cases h : i = j <;> simp [h, Matrix.diagonal, one_apply], Matrix.mul_sub,
        Matrix.sub_mul, Matrix.mul_one, hUU']
    have hdet : (1 - K).det = ∏ i, (1 - lam i) := by
      have hd : Uᵀ.det * U.det = 1 := by rw [← det_mul, hUU, det_one]
      rw [h1K, det_mul, det_mul, det_diagonal]
      linear_combination (∏ i, (1 - lam i)) * hd
    have hinv : (1 - K)⁻¹ = U * diagonal (fun i => (1 - lam i)⁻¹) * Uᵀ := by
      apply Matrix.inv_eq_left_inv
      have : (diagonal fun i => (1 - lam i)⁻¹ * (1 - lam i)) = 1 := by
        rw [← diagonal_one]
        congr 1
        funext i
        exact inv_mul_cancel₀ (by linarith [hlam i])
      rw [h1K]
      calc U * diagonal (fun i => (1 - lam i)⁻¹) * Uᵀ * (U * diagonal (fun i => 1 - lam i) * Uᵀ)
          = U * (diagonal (fun i => (1 - lam i)⁻¹) * (Uᵀ * U) * diagonal (fun i => 1 - lam i)) *
              Uᵀ := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hUU, Matrix.mul_one, diagonal_mul_diagonal, this, Matrix.mul_one, hUU']
    have hexp : b ⬝ᵥ ((1 - K)⁻¹ *ᵥ b) = ∑ i, c i ^ 2 / (1 - lam i) := by
      rw [hinv, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
      simp only [dotProduct, mulVec_diagonal]
      exact Finset.sum_congr rfl fun i _ => by
        change c i * ((1 - lam i)⁻¹ * c i) = _
        ring
    rw [hdet, hexp, Finset.prod_mul_distrib, ← Real.exp_sum, Finset.prod_inv_distrib,
      ← Real.sqrt_prod _ fun i _ => (by linarith [hlam i]), Finset.mul_sum]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : 1 - lam i ≠ 0 := by linarith [hlam i]
    field_simp
  exact ⟨inferInstance, fun K b hKs hpos => (key K b hKs hpos).1,
    fun K b hKs hpos => (key K b hKs hpos).2⟩

/-- Miao, p. 322, for the standard normal shock: `R(V)(x, u)` for the quadratic value function. -/
theorem rc_R_quad_std {X : Type*} [Fintype X] {θ : ℝ} (hθ : 0 < θ) {C : Matrix X E ℝ}
    {P : Matrix X X ℝ} (hP : Pᵀ = P) (hH : (rcH θ C P).PosDef) (y : X → ℝ) (d : ℝ) :
    rcR (Measure.pi fun _ : E => gaussianReal 0 1) (fun e => rcV P d (y + C *ᵥ e)) θ =
      -(1 / 2) * (y ⬝ᵥ (rcD θ C P *ᵥ y)) - d / 2 - θ / 2 * log (rcK θ C P)⁻¹.det :=
  (rc_R_quad rc_gaussian_std hθ hP hH y d).2

/-- **(9.51)–(9.55)** for IID standard normal shocks (Miao, pp. 321–323). -/
theorem eq_9_51_9_55_std {X U : Type*} [Fintype X] [Fintype U] [DecidableEq U]
    (L : LSProblem X U E) (hR : L.R.PosDef) (hβ : 0 ≤ L.β) (hβ1 : L.β < 1) {θ : ℝ}
    (hθ : 0 < θ) {P : Matrix X X ℝ} (hP : P.PosSemidef) (hH : (rcH θ L.C P).PosDef)
    (hfix : L.T (rcD θ L.C P) = P) (x : X → ℝ) :
    IsGreatest (Set.range (rcRobObj L (Measure.pi fun _ : E => gaussianReal 0 1) θ P
        (rcd L.β θ L.C P) x)) (rcV P (rcd L.β θ L.C P) x) ∧
      ∀ u, rcRobObj L (Measure.pi fun _ : E => gaussianReal 0 1) θ P (rcd L.β θ L.C P) x u =
          rcV P (rcd L.β θ L.C P) x ↔ u = -(L.F (rcD θ L.C P) *ᵥ x) :=
  eq_9_51_9_55 L rc_gaussian_std hR hβ hβ1 hθ hP hH hfix x

/-- The robust Bellman equation, with the minimisation over all likelihood ratios, for IID
standard normal shocks (Miao, pp. 320–323). -/
theorem rc_robust_bellman_std {X U : Type*} [Fintype X] [Fintype U] [DecidableEq U]
    (L : LSProblem X U E) (hR : L.R.PosDef) (hβ : 0 ≤ L.β) (hβ1 : L.β < 1) {θ : ℝ}
    (hθ : 0 < θ) {P : Matrix X X ℝ} (hP : P.PosSemidef) (hH : (rcH θ L.C P).PosDef)
    (hfix : L.T (rcD θ L.C P) = P) (x : X → ℝ) :
    ∃ w : (U → ℝ) → ℝ,
      (∀ u, IsLeast
        (rcObj (Measure.pi fun _ : E => gaussianReal 0 1)
            (fun e => rcV P (rcd L.β θ L.C P) (L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ e)) θ ''
          rcAdm (Measure.pi fun _ : E => gaussianReal 0 1)
            (fun e => rcV P (rcd L.β θ L.C P) (L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ e)) θ)
        (w u)) ∧
      IsGreatest (Set.range fun u => -(1 / 2) * L.loss x u + L.β * w u)
        (rcV P (rcd L.β θ L.C P) x) :=
  rc_robust_bellman L rc_gaussian_std hR hβ hβ1 hθ hP hH hfix x

/-- **Exercise 9.5** with an IID standard normal income shock: the robust Bellman equation holds
and the robust consumption rule is its unique maximiser. -/
theorem ex_9_5_bellman_std {b μ Rr ρ σ β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hR1 : 1 < Rr)
    (hρ : |ρ| < 1) (hκ : 1 < β * Rr ^ 2) {θ : ℝ} (hθ : 2 * rcHallK Rr ρ σ < θ)
    (x : Fin 3 → ℝ) :
    IsGreatest (Set.range (rcRobObj (rcHallRobust b μ Rr ρ σ β)
        (Measure.pi fun _ : Fin 1 => gaussianReal 0 1) θ (rcHallPθ b μ Rr ρ σ β θ)
        (rcd β θ (rcHallRobust b μ Rr ρ σ β).C (rcHallPθ b μ Rr ρ σ β θ)) x))
        (rcV (rcHallPθ b μ Rr ρ σ β θ)
          (rcd β θ (rcHallRobust b μ Rr ρ σ β).C (rcHallPθ b μ Rr ρ σ β θ)) x) ∧
      ∀ u, rcRobObj (rcHallRobust b μ Rr ρ σ β) (Measure.pi fun _ : Fin 1 => gaussianReal 0 1)
          θ (rcHallPθ b μ Rr ρ σ β θ)
          (rcd β θ (rcHallRobust b μ Rr ρ σ β).C (rcHallPθ b μ Rr ρ σ β θ)) x u =
          rcV (rcHallPθ b μ Rr ρ σ β θ)
            (rcd β θ (rcHallRobust b μ Rr ρ σ β).C (rcHallPθ b μ Rr ρ σ β θ)) x ↔
        u = -(rcHallGain b μ Rr ρ (rcHallQθ Rr ρ σ β θ) *ᵥ x) :=
  ex_9_5_bellman rc_gaussian_std hβ hβ1 hR1 hρ hκ hθ x

end Miao.LinearQuadratic
