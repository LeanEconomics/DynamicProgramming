/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StructuralEstimation.GMNormality

/-!
# A concrete instance of the GMM assumptions (Miao, §12.1, pp. 387–391)

Non-vacuity of the assumptions of Theorems 12.1.1 and 12.1.2 (Miao, pp. 387–391): a
degenerate but complete instance in which every hypothesis is verified in Lean.

The sample space is a point (`Unit` with the Dirac measure), the data are `x_t = 0`, the moment
function is the location model `h(x, θ) = θ − x` with `k = q = 1`, `Θ = [−1, 1]`, `θ₀ = 0` and
`W_T = W = I`. The process is stationary and ergodic (`gm_ex_isStationary`,
`gm_ex_isErgodic`), Assumptions 12.1.3, 12.1.4 and 12.1.7 hold (`gm_ex_assumption_12_1_3`,
`gm_ex_assumption_12_1_4`, `gm_ex_assumption_12_1_7`), so Theorem 12.1.1 applies
(`gm_ex_theorem_12_1_1`); with `∂h/∂θ = 1`, `S = 0` and the (trivial) central limit theorem
`√T g_T(θ₀) = 0 →d N(0, 0)`, every hypothesis of Theorem 12.1.2 holds and it applies too
(`gm_ex_theorem_12_1_2`).
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Filter Topology

/-- The constant data `x_t = 0` on a one-point sample space. -/
def gm_exX : ℕ → Unit → ℝ := fun _ _ => 0

/-- The location model `h(x, θ) = θ − x` (`k = q = 1`). -/
def gm_exH : ℝ → (Fin 1 → ℝ) → Fin 1 → ℝ := fun x θ i => θ i - x

/-- The parameter space `Θ = [−1, 1]`. -/
def gm_exΘ : Set (Fin 1 → ℝ) := Metric.closedBall 0 1

/-- The derivative `∂h_i/∂θ = e_i'`. -/
noncomputable def gm_exDh : ℝ → (Fin 1 → ℝ) → Fin 1 → (Fin 1 → ℝ) →L[ℝ] ℝ :=
  fun _ _ i => ContinuousLinearMap.proj i

theorem gm_ex_isStationary : IsStationary (Measure.dirac ()) gm_exX := fun _ _ => rfl

theorem gm_ex_isErgodic : IsErgodicProcess (Measure.dirac ()) gm_exX := by
  intro A hA _
  have hS : MeasurableSet (pathOf gm_exX ⁻¹' A) :=
    measurable_pathOf (fun _ => measurable_const) hA
  by_cases h : () ∈ pathOf gm_exX ⁻¹' A
  · exact Or.inr (Measure.dirac_apply_of_mem h)
  · left
    rw [Measure.dirac_apply' _ hS, Set.indicator_of_notMem h]

theorem gm_ex_popMoment (θ : Fin 1 → ℝ) :
    gm_popMoment (Measure.dirac ()) gm_exX gm_exH θ = θ := by
  funext i
  simp [gm_popMoment, gm_exH, gm_exX]

theorem gm_ex_compact : IsCompact gm_exΘ := isCompact_closedBall 0 1

theorem gm_ex_mem : (0 : Fin 1 → ℝ) ∈ gm_exΘ := Metric.mem_closedBall_self zero_le_one

theorem gm_ex_measurable : ∀ θ ∈ gm_exΘ, Measurable fun x => gm_exH x θ := fun _ _ =>
  measurable_pi_iff.2 fun _ => measurable_const.sub measurable_id

theorem gm_ex_continuous : ∀ x, ContinuousOn (gm_exH x) gm_exΘ := fun _ =>
  (continuous_pi fun i => (continuous_apply i).sub continuous_const).continuousOn

theorem gm_ex_assumption_12_1_3 :
    Assumption_12_1_3 (Measure.dirac ()) gm_exX gm_exH gm_exΘ 0 := fun θ _ => by
  rw [gm_ex_popMoment]

theorem gm_ex_assumption_12_1_7 : Assumption_12_1_7 (Measure.dirac ()) gm_exX gm_exH gm_exΘ := by
  refine ⟨fun x => 1 + |x|, by fun_prop, by simp only [gm_exX]; exact integrable_const _,
    fun x θ hθ => ?_⟩
  have hθ1 : ‖θ‖ ≤ 1 := mem_closedBall_zero_iff.1 hθ
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  have h1 := (norm_le_pi_norm θ i).trans hθ1
  simp only [gm_exH, Real.norm_eq_abs] at h1 ⊢
  have := abs_sub (θ i) x
  linarith

theorem gm_ex_assumption_12_1_4 : Assumption_12_1_4 (Measure.dirac ())
    (fun _ _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) 1 := by
  refine ⟨fun _ _ => Matrix.PosSemidef.one, Matrix.PosDef.one, fun i j => ?_⟩
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  simp only [dist_self]
  have : {x : Unit | ε ≤ 0} = ∅ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
    exact hε
  simp [this]

/-- Theorem 12.1.1 applies to the concrete instance: a GMM estimator exists and is consistent. -/
theorem gm_ex_theorem_12_1_1 : ∃ θh : ℕ → Unit → Fin 1 → ℝ, (∀ T ω, θh T ω ∈ gm_exΘ ∧
    ∀ θ ∈ gm_exΘ, gm_objective gm_exX gm_exH (fun _ _ => 1) T ω (θh T ω) ≤
      gm_objective gm_exX gm_exH (fun _ _ => 1) T ω θ) ∧
    TendstoInMeasure (Measure.dirac ()) θh atTop (fun _ => 0) := by
  obtain ⟨θh, hθh⟩ := gm_exists_estimator (X := gm_exX) gm_ex_compact ⟨0, gm_ex_mem⟩
    gm_ex_continuous (fun _ _ => (1 : Matrix (Fin 1) (Fin 1) ℝ))
  exact ⟨θh, hθh, theorem_12_1_1 (X := gm_exX) (fun _ => measurable_const)
    gm_ex_isStationary gm_ex_isErgodic
    gm_ex_compact gm_ex_mem gm_ex_measurable gm_ex_continuous gm_ex_assumption_12_1_3
    gm_ex_assumption_12_1_7 gm_ex_assumption_12_1_4 (fun T ω => (hθh T ω).1)
    fun T ω => (hθh T ω).2⟩

theorem gm_ex_popJac (θ : Fin 1 → ℝ) :
    gm_popJac (Measure.dirac ()) gm_exX gm_exDh θ = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [gm_popJac, gm_jacobian, gm_exDh]

theorem gm_ex_sampleJac {T : ℕ} (hT : 1 ≤ T) (ω : Unit) (θ : Fin 1 → ℝ) :
    gm_sampleJac gm_exX gm_exDh T ω θ = 1 := by
  have hT0 : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  ext i j
  fin_cases i
  fin_cases j
  simp [gm_sampleJac, gm_sampleDeriv, gm_jacobian, gm_exDh, hT0]

theorem gm_ex_sampleMoment_zero (T : ℕ) (ω : Unit) :
    gm_sampleMoment gm_exX gm_exH T ω 0 = 0 := by
  funext i
  simp [gm_sampleMoment, gm_exH, gm_exX]

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- `N(0, 0)` is the point mass at `0`. -/
theorem gm_ex_multivariateGaussian_zero :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) 0 = Measure.dirac 0 := by
  rw [multivariateGaussian, CFC.sqrt_zero (A := Matrix (Fin 1) (Fin 1) ℝ), map_zero]
  simp [Measure.map_const]

/-- Theorem 12.1.2 applies to the concrete instance (with `S = 0`): every hypothesis, including
the central limit theorem of Lemma 12.1.1, is verified, so `√T(θ̂_T − θ₀) →d N(0, 0)`. -/
theorem gm_ex_theorem_12_1_2 : ∃ θh : ℕ → Unit → Fin 1 → ℝ,
    TendstoInDistribution (fun (T : ℕ) ω => gm_toE (Real.sqrt (T : ℝ) • (θh T ω - 0))) atTop
      (fun z => gm_matE (-gm_M (gm_popJac (Measure.dirac ()) gm_exX gm_exDh 0) 1) (id z))
      (fun _ => Measure.dirac ()) (multivariateGaussian 0 0) := by
  obtain ⟨θh, hθh⟩ := gm_exists_estimator (X := gm_exX) gm_ex_compact ⟨0, gm_ex_mem⟩
    gm_ex_continuous (fun _ _ => (1 : Matrix (Fin 1) (Fin 1) ℝ))
  refine ⟨θh, (theorem_12_1_2 (X := gm_exX) (fun _ => measurable_const)
    gm_ex_isStationary gm_ex_isErgodic
    gm_ex_compact gm_ex_mem gm_ex_measurable gm_ex_continuous gm_ex_assumption_12_1_3
    gm_ex_assumption_12_1_7 gm_ex_assumption_12_1_4 (r := 1 / 2) (by norm_num) ?_
    (Dh := gm_exDh) ?_ ?_ ?_ ?_ Matrix.PosSemidef.zero ⟨aemeasurable_id, Measure.map_id⟩ ?_
    (fun _ => Subsingleton.measurable) (fun T ω => (hθh T ω).1)
    fun T ω => (hθh T ω).2).1⟩
  · intro θ hθ
    simp only [gm_exΘ, Metric.mem_closedBall, Metric.mem_ball] at hθ ⊢
    linarith
  · intro x θ _ i
    exact (hasFDerivAt_apply i θ).sub_const x
  · intro i j
    simp only [gm_ex_popJac]
    exact continuousAt_const
  · intro i j ε hε
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with T hT
    have : {ω : Unit | ∃ θ ∈ Metric.ball (0 : Fin 1 → ℝ) (1 / 2),
        ε ≤ |gm_sampleJac gm_exX gm_exDh T ω θ i j -
          gm_popJac (Measure.dirac ()) gm_exX gm_exDh θ i j|} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and,
        not_le]
      intro θ _
      rw [gm_ex_sampleJac hT, gm_ex_popJac, sub_self, abs_zero]
      exact hε
    rw [this, measure_empty]
  · rw [gm_ex_popJac]
    intro v w hvw
    simpa [Matrix.one_mulVec] using hvw
  · have heq : (fun (T : ℕ) (ω : Unit) => gm_toE (Real.sqrt (T : ℝ) •
        gm_sampleMoment gm_exX gm_exH T ω 0)) = fun _ _ => 0 := by
      funext T ω
      rw [gm_ex_sampleMoment_zero, smul_zero]
      rfl
    rw [heq]
    refine tendstoInDistribution_of_identDistrib 0 (fun _ => IdentDistrib.refl aemeasurable_const)
      ⟨aemeasurable_const, aemeasurable_id, ?_⟩
    rw [Measure.map_id, gm_ex_multivariateGaussian_zero, Measure.map_const]
    simp

end Miao.StructuralEstimation
