/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# §21.3: why inequality matters for aggregates

AKMM, §21.3, pp. 656–661.

* **Education with a fixed cost** (§21.3.1, p. 657): `ed_educates`: a worker with wealth `W`
  educates iff the cost `F` can be self-financed (`W ≥ F`) and it pays (`w_s − F > w_u`);
  `ed_unconstrained`: with borrowing, wealth is irrelevant; `ed_fraction`: if `w_s − w_u > F` the
  mass educated is the mass with wealth at least `F`; `ed_wealth_matters`: two wealth
  distributions with the same mean educate different fractions.
* **MPCs and TANK** (§21.3.2, pp. 658–659): `mpc_binding`: at a binding borrowing limit
  consumption is cash on hand less the limit, so the MPC is `1`; `tank_mpc`: the hand-to-mouth
  share `γ = (M − m)/(1 − m)` delivers any aggregate MPC `M ∈ [m, 1]`.
* **A consumption externality** (p. 660): `ext_log_output`: with `y = A c^ω k^α`,
  `log y = log A + ω log c + α log k`, so with `ω = 0` output moves one-for-one with TFP and
  with `ω > 0` it also moves with consumption.
-/

namespace AKMM.Inequality

open Filter Topology MeasureTheory

/-- AKMM, p. 657: without borrowing, a worker with wealth `W` chooses education (lifetime income
`w_s − F`) over unskilled work (`w_u`) iff it is affordable and strictly better. -/
def ed_educates (ws wu F W : ℝ) : Prop := F ≤ W ∧ wu < ws - F

/-- An instance of `ed_educates`: `w_s = 3`, `w_u = 1`, `F = 1`, `W = 1`. -/
theorem ed_educates_example : ed_educates 3 1 1 1 := ⟨le_rfl, by norm_num⟩

/-- **AKMM, p. 657: "if `w_s − w_u > F`, it would pay off for the individual to obtain
education"**: with borrowing (no wealth requirement) the choice is independent of `W`. -/
theorem ed_unconstrained (ws wu F : ℝ) : wu < ws - F ↔ F < ws - wu := by
  constructor <;> intro h <;> linarith

/-- **AKMM, p. 657: "the fraction of individuals who would choose education … equals the
fraction of people with wealth above `F`".** If `w_s − w_u > F`, the set of educated wealth
levels is `[F, ∞)`, so for any wealth distribution `μ` the mass educated is `μ[F, ∞)`. -/
theorem ed_fraction {ws wu F : ℝ} (h : F < ws - wu) (μ : Measure ℝ) :
    μ {W | ed_educates ws wu F W} = μ (Set.Ici F) := by
  congr 1
  ext W
  simp only [ed_educates, Set.mem_ofPred_eq, Set.mem_Ici]
  constructor
  · exact fun h' => h'.1
  · exact fun h' => ⟨h', by linarith⟩

/-- **AKMM, p. 657: "the wealth distribution matters for educational attainment".** With
`w_s − w_u > F > 0`, everyone educates when all hold wealth `F`, but only half do when half hold
`0` and half `2F` (the same mean wealth). -/
theorem ed_wealth_matters {ws wu F : ℝ} (hF : 0 < F) (h : F < ws - wu) :
    (Measure.dirac F) {W | ed_educates ws wu F W} = 1 ∧
      ((1 / 2 : ENNReal) • Measure.dirac (0 : ℝ) + (1 / 2 : ENNReal) • Measure.dirac (2 * F) :
        Measure ℝ) {W | ed_educates ws wu F W} = 1 / 2 := by
  rw [ed_fraction h, ed_fraction h]
  refine ⟨?_, ?_⟩
  · rw [Measure.dirac_apply' _ measurableSet_Ici]
    simp
  · rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.dirac_apply' _ measurableSet_Ici, Measure.dirac_apply' _ measurableSet_Ici]
    have h0 : (0 : ℝ) ∉ Set.Ici F := by simp [hF]
    have h2 : 2 * F ∈ Set.Ici F := by simp only [Set.mem_Ici]; linarith
    simp [h0, h2]

/-- **AKMM, p. 658, fn and Figure 21.10: "those who are literally borrowing-constrained have a
marginal propensity of 1".** If near cash on hand `x` the agent is at the limit `a′ = a̲`, so
`c(z) = z − a̲` for `z` near `x`, then `∂c/∂x = 1`. -/
theorem mpc_binding {c : ℝ → ℝ} {x al : ℝ} (h : ∀ᶠ z in 𝓝 x, c z = z - al) :
    HasDerivAt c 1 x :=
  ((hasDerivAt_id x).sub_const al).congr_of_eventuallyEq h

/-- **AKMM, p. 659: TANK.** A fraction `γ` of hand-to-mouth agents (MPC `1`) and `1 − γ` rentiers
(MPC `m < 1`) give the aggregate MPC `γ + (1 − γ)m`; for any target `M ∈ [m, 1]` the share
`γ = (M − m)/(1 − m) ∈ [0, 1]` delivers it ("an aggregate MPC of, say, 0.5"). -/
theorem tank_mpc {m M : ℝ} (hm : m < 1) (hmM : m ≤ M) (hM : M ≤ 1) :
    0 ≤ (M - m) / (1 - m) ∧ (M - m) / (1 - m) ≤ 1 ∧
      (M - m) / (1 - m) * 1 + (1 - (M - m) / (1 - m)) * m = M := by
  have h1 : 0 < 1 - m := sub_pos.2 hm
  refine ⟨div_nonneg (by linarith) h1.le, (div_le_one h1).2 (by linarith), ?_⟩
  field_simp
  ring

/-- **AKMM, p. 660: output with a consumption externality.** For `y = A c^ω k^α` with positive
`A, c, k`: `log y = log A + ω log c + α log k`. With `ω = 0` a one-percent TFP shock raises output
by one percent whatever consumption does; with `ω > 0` the consumption response adds
`ω · Δlog c`. -/
theorem ext_log_output {A c k ω α : ℝ} (hA : 0 < A) (hc : 0 < c) (hk : 0 < k) :
    Real.log (A * c ^ ω * k ^ α) = Real.log A + ω * Real.log c + α * Real.log k := by
  rw [Real.log_mul (mul_pos hA (Real.rpow_pos_of_pos hc ω)).ne'
    (Real.rpow_pos_of_pos hk α).ne', Real.log_mul hA.ne' (Real.rpow_pos_of_pos hc ω).ne',
    Real.log_rpow hc, Real.log_rpow hk]

end AKMM.Inequality
