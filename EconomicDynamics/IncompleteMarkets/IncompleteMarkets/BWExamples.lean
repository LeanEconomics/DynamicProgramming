/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IncompleteMarkets.BWMoney
import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# A concrete endowment economy with valued fiat money (instances for §17.2)

Witnesses that Definition 17.2.1, the Bewley equilibrium with interest on currency
(`BWBewleyEqm`) and the fiat-money equilibrium of §17.2.2 are not vacuous.

The economy `bw_cycle`: the idiosyncratic state `s ∈ Bool` alternates deterministically
(`Q(·, s) = δ_{¬s}`, a two-state Markov chain), the endowment is `e(true) = 2`, `e(false) = 1`,
`β = 1/2` and `u(c) = min(c, 3/2)` (concave, nondecreasing, satiated at `3/2`). With `r = 0` and no
borrowing the household consumes `3/2` in the high state and saves the rest, and consumes up to
`3/2` in the low state:
`V(a, true) = 3`, `V(a, false) = min(a + 1, 3/2) + 3/2`,
`g(a, true) = a + 1/2`, `g(a, false) = a + 1 − min(a + 1, 3/2)` (`bw_cycle_bellman`).
The distribution `½δ_{(0, true)} + ½δ_{(1/2, false)}` is stationary (`bw_cycle_stationary`) with
mean asset holdings `1/4` (`bw_cycle_mean`), so `1/4 ∈ Ea(0; 0)` (`bw_cycle_EaSet`).

* `bw_cycle_fiat`: fiat money is valued, `p = 4M` (§17.2.2).
* `bw_cycle_huggett`: a Huggett equilibrium (Definition 17.2.1) with debt limit `1/4` and `r = 0`,
  obtained from Proposition 17.2.1.
* `bw_cycle_bewley`: a Bewley equilibrium with interest on currency (back-solving).
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The two-state cycle economy. -/
noncomputable def bw_cycle : BWEconomy Bool where
  β := 1 / 2
  u := fun c => min c (3 / 2)
  Q := Kernel.deterministic (fun s => !s) (Measurable.of_discrete)
  e := fun s => if s then 2 else 1

/-- The value function of the cycle economy. -/
noncomputable def bw_cycleV (a : ℝ) (s : Bool) : ℝ := if s then 3 else min (a + 1) (3 / 2) + 3 / 2

/-- The asset policy of the cycle economy. -/
noncomputable def bw_cycleG (a : ℝ) (s : Bool) : ℝ :=
  if s then a + 1 / 2 else a + 1 - min (a + 1) (3 / 2)

theorem bw_cycle_Q (s : Bool) : bw_cycle.Q s = Measure.dirac (!s) := by
  simp [bw_cycle, Kernel.deterministic_apply]

theorem bw_cycle_integral (f : Bool → ℝ) (s : Bool) : ∫ s', f s' ∂(bw_cycle.Q s) = f (!s) := by
  rw [bw_cycle_Q, integral_dirac]

/-- The household's problem (17.4) of the cycle economy at `r = 0`, `φ = 0`. -/
theorem bw_cycle_bellman : bw_cycle.Bellman 0 0 bw_cycle.e bw_cycleV bw_cycleG := by
  intro a s ha
  rw [neg_zero] at ha
  refine ⟨?_, fun a' _ => by rw [bw_cycle_Q]; exact Integrable.of_finite, ?_, fun a' ha' => ?_⟩
  · cases s <;> simp only [bw_cycleG, bw_cycle, Bool.false_eq_true, ↓reduceIte, Set.mem_Icc,
      neg_zero]
    · have := min_le_left (a + 1) (3 / 2)
      have : 0 ≤ min (a + 1) (3 / 2) := le_min (by linarith) (by norm_num)
      constructor <;> linarith
    · constructor <;> linarith
  · rw [bw_cycle_integral]
    cases s <;> simp only [bw_cycleG, bw_cycleV, bw_cycle, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false, Bool.not_true]
    · have : (1 + 0) * a + 1 - (a + 1 - min (a + 1) (3 / 2)) = min (a + 1) (3 / 2) := by ring
      rw [this, min_eq_left (min_le_right _ _)]
      norm_num
    · have h1 : (1 + 0) * a + 2 - (a + 1 / 2) = 3 / 2 := by ring
      have h2 : min (a + 1 / 2 + 1) (3 / 2 : ℝ) = 3 / 2 := min_eq_right (by linarith)
      rw [h1, h2, min_self]
      norm_num
  · rw [bw_cycle_integral]
    obtain ⟨h0, h1⟩ := ha'
    rw [neg_zero] at h0
    cases s <;> simp only [bw_cycleV, bw_cycle, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true] at h1 ⊢
    · have : min ((1 + 0) * a + 1 - a') (3 / 2) ≤ min (a + 1) (3 / 2) :=
        min_le_min (by linarith) le_rfl
      linarith
    · have := min_le_right ((1 + 0) * a + 2 - a') (3 / 2 : ℝ)
      have := min_le_right (a' + 1) (3 / 2 : ℝ)
      linarith

/-- The stationary distribution `½δ_{(0, true)} + ½δ_{(1/2, false)}` of the cycle economy. -/
noncomputable def bw_cycleLam : Measure (ℝ × Bool) :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac ((0 : ℝ), true) + (2⁻¹ : ℝ≥0∞) • Measure.dirac ((1 / 2 : ℝ), false)

theorem bw_cycleLam_isProb : IsProbabilityMeasure bw_cycleLam :=
  ⟨by simp [bw_cycleLam, ENNReal.inv_two_add_inv_two]⟩

theorem bw_cycleLam_supp : bw_cycleLam {p | p.1 < -0} = 0 := by
  simp [bw_cycleLam, Measure.dirac_apply]

/-- (17.8) for the cycle economy. -/
theorem bw_cycle_stationary : bw_cycle.Stationary bw_cycleG bw_cycleLam := by
  intro A B _ _
  simp only [bw_cycleLam, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply,
    lintegral_add_measure, lintegral_smul_measure, lintegral_dirac, bw_cycle_Q, smul_eq_mul]
  have g1 : bw_cycleG 0 true = 1 / 2 := by norm_num [bw_cycleG]
  have g2 : bw_cycleG (1 / 2) false = 0 := by
    simp only [bw_cycleG, Bool.false_eq_true, ↓reduceIte]
    rw [min_eq_right (by norm_num)]; norm_num
  rw [g1, g2]
  by_cases hA0 : (0 : ℝ) ∈ A <;> by_cases hA1 : (1 / 2 : ℝ) ∈ A <;>
    by_cases hBt : true ∈ B <;> by_cases hBf : false ∈ B <;>
    simp only [Set.indicator, Set.mem_prod, Bool.not_false, Bool.not_true, hA0, hA1, hBt, hBf] <;>
    simp [add_comm]

theorem bw_cycle_integrable : Integrable (fun p : ℝ × Bool => bw_cycleG p.1 p.2) bw_cycleLam :=
  ((integrable_dirac (by simp)).smul_measure (by simp)).add_measure
    ((integrable_dirac (by simp)).smul_measure (by simp))

/-- Mean asset holdings (money demand) in the cycle economy: `∫ g dλ = 1/4`. -/
theorem bw_cycle_mean : ∫ p, bw_cycleG p.1 p.2 ∂bw_cycleLam = 1 / 4 := by
  rw [bw_cycleLam, integral_add_measure, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac]
  · have g2 : bw_cycleG (1 / 2) false = 0 := by
      simp only [bw_cycleG, Bool.false_eq_true, ↓reduceIte]
      rw [min_eq_right (by norm_num)]; norm_num
    simp only [g2]
    norm_num [bw_cycleG]
  · exact (integrable_dirac (by simp)).smul_measure (by simp)
  · exact (integrable_dirac (by simp)).smul_measure (by simp)

/-- `1/4 ∈ Ea(0; 0)` in the cycle economy. -/
theorem bw_cycle_EaSet : (1 / 4 : ℝ) ∈ bw_cycle.EaSet 0 0 bw_cycle.e :=
  ⟨bw_cycleV, bw_cycleG, bw_cycleLam, bw_cycleLam_isProb, bw_cycleLam_supp, bw_cycle_bellman,
    bw_cycle_stationary, bw_cycle_integrable, bw_cycle_mean.symm⟩

/-- §17.2.2 (Miao, pp. 572–573) is not vacuous: in the cycle economy fiat money is valued; for any
money stock `M > 0` the price level `p = 4M` clears the money market, `Ea(0) = M/p`. -/
theorem bw_cycle_fiat (M : ℝ) (hM : 0 < M) :
    0 < 4 * M ∧ (1 / 4 : ℝ) = M / (4 * M) ∧ (1 / 4 : ℝ) ∈ bw_cycle.EaSet 0 0 bw_cycle.e := by
  refine ⟨by linarith, ?_, bw_cycle_EaSet⟩
  field_simp

/-- Definition 17.2.1 is not vacuous: the cycle economy with debt limit `1/4` has a stationary
recursive competitive equilibrium with `r = 0` (from Proposition 17.2.1). -/
theorem bw_cycle_huggett : ∃ eqm : BWHuggettEqm bw_cycle (1 / 4), eqm.r = 0 := by
  rw [definition_17_2_1]
  have := bw_EaSet_shift (d := -(1 / 4)) (φ' := 1 / 4) (y' := bw_cycle.e) bw_cycle_EaSet
    (by ring) (fun s => by ring)
  norm_num at this
  exact this

/-- `BWBewleyEqm` is not vacuous: the cycle economy has a Bewley equilibrium with (zero) interest
on currency, by back-solving. -/
theorem bw_cycle_bewley : ∃ B : BWBewleyEqm bw_cycle, B.rt = 0 := by
  rw [proposition_17_2_3_rates]
  obtain ⟨eqm, h⟩ := bw_cycle_huggett
  exact ⟨1 / 4, by norm_num, eqm, h⟩

end Miao.IncompleteMarkets
