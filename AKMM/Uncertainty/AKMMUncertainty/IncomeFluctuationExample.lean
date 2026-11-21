/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMUncertainty.IncomeFluctuationStationary
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# A solved instance of the Figure 7.4 model

AKMM, §7.6, pp. 213–215. A two-state Markov income process (as in Figure 7.4), not i.i.d.:
`y ∈ {1, 2}`, `P = [3/4 1/4; 1/4 3/4]`, `r = 1` (`q = 1/2`), `β = 1/4` (`β(1 + r) = 1/2`),
`a̲ = 0` and `u(c) = c + log c` (`u′(c) = 1 + 1/c`). The consumer is impatient enough that the
borrowing constraint binds everywhere: `g(a, y) = 0` and `V(a, y) = u(a + y) + w_y`, with
`w = (I − βP)⁻¹βPU`, `U_y = u(y)`, solve the Bellman equation (`imf_example_bellman`, proved by
the tangent inequality for `u`), and all the standing assumptions and the extra hypotheses of
`imf_stationary` hold (`imf_example_standing`, `imf_example_hyps`), so that theorem's
conclusions hold for this economy (`imf_example_stationary`): none of the results of
`IncomeFluctuation` and `IncomeFluctuationStationary` is vacuous.

The instance also shows that the figure's picture of the high-income rule, "an intercept above
the 45 degree line" and accumulation "up to the point `ā` where the upper line crosses the
45-degree line", is a feature of the parameters behind the figure, not of the model: here every
state dissaves above `a̲` and the ergodic set is `{a̲}` (`imf_example_no_accumulation`).
-/

namespace AKMM.Uncertainty

open Real Set

/-- The example's utility `u(c) = c + log c`. -/
noncomputable def imf_exU (c : ℝ) : ℝ := c + Real.log c

/-- The example's marginal utility `u′(c) = 1 + 1/c`. -/
noncomputable def imf_exDU (c : ℝ) : ℝ := 1 + c⁻¹

/-- The example's income levels `y ∈ {1, 2}`. -/
def imf_exInc : Fin 2 → ℝ := ![1, 2]

/-- The example's transition matrix `P = [3/4 1/4; 1/4 3/4]` (persistent, not i.i.d.). -/
noncomputable def imf_exP : Fin 2 → Fin 2 → ℝ := ![![3 / 4, 1 / 4], ![1 / 4, 3 / 4]]

/-- The constants `w = (I − βP)⁻¹βPU` of the value function. -/
noncomputable def imf_exW : Fin 2 → ℝ :=
  ![(5 * imf_exU 1 + 2 * imf_exU 2) / 21, (2 * imf_exU 1 + 5 * imf_exU 2) / 21]

/-- The example's value function `V(a, y) = u(a + y) + w_y`. -/
noncomputable def imf_exV (y : Fin 2) (a : ℝ) : ℝ := imf_exU (a + imf_exInc y) + imf_exW y

/-- Its derivative `V₁(a, y) = 1 + 1/(a + y)`. -/
noncomputable def imf_exV1 (y : Fin 2) (a : ℝ) : ℝ := imf_exDU (a + imf_exInc y)

/-- The example's savings rule `g(a, y) = a̲ = 0`. -/
def imf_exG (_ : Fin 2) (_ : ℝ) : ℝ := 0

theorem imf_exInc_ge (y : Fin 2) : 1 ≤ imf_exInc y ∧ imf_exInc y ≤ 2 := by
  fin_cases y <;> norm_num [imf_exInc]

/-- The tangent inequality `u(x) ≤ u(x₀) + (x − x₀) + (x − x₀)/x₀` for `u = c + log c`. -/
theorem imf_exU_tangent {x x₀ : ℝ} (hx : 0 < x) (hx₀ : 0 < x₀) :
    imf_exU x ≤ imf_exU x₀ + (x - x₀) + (x - x₀) / x₀ := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx hx₀)
  rw [Real.log_div hx.ne' hx₀.ne'] at h
  have : x / x₀ - 1 = (x - x₀) / x₀ := by field_simp
  unfold imf_exU
  linarith

/-- The example's `(V, g)` solve the Bellman equation of p. 213 with `β = 1/4`, `q = 1/(1 + 1)`,
`a̲ = 0`. -/
theorem imf_example_bellman :
    im_Bellman imf_exU (1 / 4) (1 / (1 + 1)) imf_exP imf_exInc 0 imf_exV imf_exG := by
  intro y a ha
  obtain ⟨hy1, hy2⟩ := imf_exInc_ge y
  refine ⟨⟨le_rfl, by simp only [imf_exG]; linarith⟩, ?_, fun a' ha' hfeas => ?_⟩
  · simp only [imf_exV, imf_exG, Fin.sum_univ_two, zero_add]
    fin_cases y <;>
      simp [imf_exP, imf_exW, imf_exInc] <;> ring
  · have hc0 : 0 < a + imf_exInc y := by linarith
    have t0 := imf_exU_tangent (x := a + imf_exInc y - 1 / (1 + 1) * a') (by linarith) hc0
    have t1 := imf_exU_tangent (x := a' + 1) (x₀ := 1) (by linarith) one_pos
    have t2 := imf_exU_tangent (x := a' + 2) (x₀ := 2) (by linarith) two_pos
    have hneg : (a + imf_exInc y - 1 / (1 + 1) * a' - (a + imf_exInc y)) / (a + imf_exInc y) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hc0.le
    simp only [imf_exV, Fin.sum_univ_two]
    fin_cases y <;>
      simp only [imf_exP, imf_exInc, imf_exW, Fin.zero_eta, Fin.mk_one, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_one] at * <;>
      norm_num at t1 t2 ⊢ <;> linarith

/-- The example satisfies the standing assumptions of §7.6 (`imf_Standing`). -/
theorem imf_example_standing :
    imf_Standing imf_exU imf_exDU (1 / 4) 1 imf_exP imf_exInc 0 imf_exV imf_exV1 imf_exG := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun y y' => ?_, fun y => ?_,
    imf_example_bellman, fun c hc => ?_, fun c hc => ?_, fun c hc c' hc' hlt => ?_,
    fun y a ha => ?_, fun y a ha b hb hab => ?_⟩
  · fin_cases y <;> fin_cases y' <;> norm_num [imf_exP]
  · fin_cases y <;> norm_num [imf_exP, Fin.sum_univ_two]
  · exact (hasDerivAt_id c).add (Real.hasDerivAt_log hc.ne')
  · unfold imf_exDU; positivity
  · unfold imf_exDU
    linarith [inv_strictAntiOn hc hc' hlt]
  · obtain ⟨hy1, -⟩ := imf_exInc_ge y
    have hpos : 0 < a + imf_exInc y := by linarith
    have := ((hasDerivAt_id a).add_const (imf_exInc y)).add
      (Real.hasDerivAt_log hpos.ne' |>.comp a ((hasDerivAt_id a).add_const (imf_exInc y)))
    have h2 := this.add_const (imf_exW y)
    convert h2 using 1
    · funext x; simp only [imf_exV, imf_exU]; rfl
    · simp only [imf_exV1, imf_exDU, mul_one]
  · obtain ⟨hy1, -⟩ := imf_exInc_ge y
    simp only [mem_Ici] at ha hb
    unfold imf_exV1 imf_exDU
    have := inv_anti₀ (by linarith : 0 < a + imf_exInc y) (by linarith : a + imf_exInc y ≤
      b + imf_exInc y)
    linarith

/-- The example satisfies the extra hypotheses of `imf_stationary`: `u′` continuous, `r = 1 > 0`,
income spread `D = 1`, `β(1 + r)u′(c) < u′(c + 1)` for `c ≥ 2`, positive transition
probabilities. -/
theorem imf_example_hyps :
    ContinuousOn imf_exDU (Ioi 0) ∧ (0 : ℝ) < 1 ∧
      (∀ y y', imf_exInc y - imf_exInc y' ≤ 1) ∧
      (∃ C, ∀ c, C ≤ c → 0 < c → 1 / 4 * (1 + 1) * imf_exDU c < imf_exDU (c + 1)) ∧
      ∀ y y', 0 < imf_exP y y' := by
  refine ⟨continuousOn_const.add (continuousOn_inv₀.mono fun c hc => ne_of_gt hc), one_pos,
    fun y y' => ?_, ⟨2, fun c hc hc0 => ?_⟩, fun y y' => ?_⟩
  · linarith [imf_exInc_ge y, imf_exInc_ge y']
  · unfold imf_exDU
    have h1 : c⁻¹ ≤ 1 / 2 := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le two_pos hc
    have h2 : 0 < (c + 1)⁻¹ := by positivity
    linarith
  · fin_cases y <;> fin_cases y' <;> norm_num [imf_exP]

/-- **AKMM, Fig. 7.4, pp. 214–215, for the example**: `imf_stationary` applies, so there is an
upper bound `ā` and, on every `[0, b] × {1, 2}` with `b ≥ ā`, a unique stationary distribution
to which the distribution of `(a, y)` converges in total variation. -/
theorem imf_example_stationary :
    ∃ ab, 0 ≤ ab ∧ (∀ a, ab ≤ a → ∀ y, imf_exG y a < a) ∧ ∀ b, ab ≤ b →
      (∀ y a, a ∈ Icc 0 b → imf_exG y a ∈ Icc 0 b) ∧
      (∀ y, Measurable fun a : Icc (0 : ℝ) b => imf_exG y a) ∧
      ∀ (hmaps : ∀ y a, a ∈ Icc 0 b → imf_exG y a ∈ Icc 0 b)
        (hmeas : ∀ y, Measurable fun a : Icc (0 : ℝ) b => imf_exG y a),
        ProbabilityTheory.IsMarkovKernel (imf_kernel imf_exP imf_exG hmaps hmeas) ∧
        ∃ μs : MeasureTheory.Measure (Icc (0 : ℝ) b × Fin 2),
          MeasureTheory.IsProbabilityMeasure μs ∧
          Miao.MarkovProcesses.adjointOp (imf_kernel imf_exP imf_exG hmaps hmeas) μs = μs ∧
          (∀ ν : MeasureTheory.Measure (Icc (0 : ℝ) b × Fin 2),
            MeasureTheory.IsProbabilityMeasure ν →
            Miao.MarkovProcesses.adjointOp (imf_kernel imf_exP imf_exG hmaps hmeas) ν = ν →
              ν = μs) ∧
          ∀ l₀ : MeasureTheory.Measure (Icc (0 : ℝ) b × Fin 2),
            MeasureTheory.IsProbabilityMeasure l₀ →
            Miao.MarkovProcesses.ConvStrongly (fun n => Miao.MarkovProcesses.adjointOp
              (Miao.MarkovProcesses.kpow (imf_kernel imf_exP imf_exG hmaps hmeas) n) l₀) μs := by
  obtain ⟨hc, hr, hD, hU, hP⟩ := imf_example_hyps
  exact imf_stationary imf_example_standing hc hr hD hU hP

/-- AKMM, p. 214 (correction): the high-income rule need not lie above the 45-degree line. In
the example (which satisfies every assumption of §7.6) the constraint binds in both income
states, `g(a, y) = a̲ = 0 < a` for all `a > 0`, so no state accumulates and the ergodic set is
`{a̲}`. -/
theorem imf_example_no_accumulation :
    imf_Standing imf_exU imf_exDU (1 / 4) 1 imf_exP imf_exInc 0 imf_exV imf_exV1 imf_exG ∧
      (∀ y, imf_exG y 0 = 0) ∧ ∀ a, 0 < a → ∀ y, imf_exG y a < a :=
  ⟨imf_example_standing, fun _ => rfl, fun _ ha _ => ha⟩

end AKMM.Uncertainty
