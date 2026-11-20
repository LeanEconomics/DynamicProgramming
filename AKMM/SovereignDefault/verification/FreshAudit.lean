import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import CapitalMarketImperfections.DebtOverhangLaffer
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.BigOperators.Intervals
import RecursiveDecisionProcesses.Basics
import Mathlib.Topology.MetricSpace.Contracting
import RecursiveDecisionProcesses.Contracting
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecificLimits.Basic
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The two-period default model: default rule and bond price

AKMM, §24.3, pp. 739–741 and footnotes 8 and 14 (p. 741, p. 745). The endowment `Y₂` has law
`μ` (a probability measure on `ℝ`); a default costs the fraction `φ > 0` of `Y₂`; lenders are
risk neutral and do not discount.

* (24.3)–(24.4): the period-2 consumption under each choice, the default rule `D̂₂ = 1` iff
  `Y₂ < B₂/φ` is optimal with ties repaid (`eq_24_3`, `eq_24_4`, `tp_defaultRule_optimal`), and
  `Ĉ₂ = Y₂ − min(φY₂, B₂) = max(Y₂ − B₂, (1 − φ)Y₂)`, continuous and nonincreasing in `B₂`.
* (24.5): the zero-profit price `q₁(B₂) = E[1 − D̂₂]` equals `Pr(Y₂ ≥ B₂/φ) = 1 − F(B₂/φ)` when
  `Y₂` has no atoms (`eq_24_5`). The printed middle term `Pr(Y₂ < B₂/φ)` is the default
  probability, not the repayment probability (`eq_24_5_printed_false`).
* The price lies in `[0, 1]`, equals `1` at `B₂ = 0`, is nonincreasing, strictly decreasing where
  the law has positive mass on every interval, continuous, tends to `0`, and has derivative
  `−f(B₂/φ)/φ` where `F` has density `f` ("the bond price decreases with the number of bonds
  issued", p. 741).
* Footnote 8: income-contingent payments `b(Y₂) ≤ φY₂` are never defaulted on; the contingent
  schedule `B₂(1 − D̂₂)` raises the same revenue and gives at least as much (strictly more in
  default states with `Y₂ > 0`) period-2 consumption (`fn_8`).
* Footnote 14: if `F(· | Y₁)` decreases in `Y₁` (first-order stochastic dominance), then
  `q₁(B₂, Y₁) = 1 − F(B₂/φ | Y₁)` increases in `Y₁` (`fn_14`).
-/

namespace AKMM.SovereignDefault

open MeasureTheory Filter Topology ProbabilityTheory

/-- AKMM, (24.4), p. 740: the equilibrium default rule `D̂₂(B₂, Y₂) = 1` if `Y₂ < B₂/φ`, and `0`
otherwise. -/
noncomputable def defaultRule (φ B Y : ℝ) : ℝ := if Y < B / φ then 1 else 0

/-- AKMM, (24.3), p. 740: period-2 consumption given the default decision `D`,
`C₂ = Y₂ − DφY₂ − (1 − D)B₂`. -/
def cons2Of (φ B Y D : ℝ) : ℝ := Y - D * (φ * Y) - (1 - D) * B

/-- AKMM, p. 740: equilibrium period-2 consumption
`Ĉ₂(B₂, Y₂) = Y₂ − D̂₂φY₂ − (1 − D̂₂)B₂`. -/
noncomputable def cons2 (φ B Y : ℝ) : ℝ := cons2Of φ B Y (defaultRule φ B Y)

/-- AKMM, (24.3), p. 740: consumption is `Y₂ − B₂` under repayment and `Y₂ − φY₂` under
default. -/
theorem eq_24_3 (φ B Y : ℝ) : cons2Of φ B Y 0 = Y - B ∧ cons2Of φ B Y 1 = Y - φ * Y := by
  constructor <;> (unfold cons2Of; ring)

/-- The default rule takes the values `0` and `1`. -/
theorem tp_defaultRule_mem (φ B Y : ℝ) : defaultRule φ B Y = 0 ∨ defaultRule φ B Y = 1 := by
  unfold defaultRule
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The default rule in multiplied-out form: `D̂₂ = 1` iff `φY₂ < B₂`. -/
theorem tp_defaultRule_eq {φ : ℝ} (hφ : 0 < φ) (B Y : ℝ) :
    defaultRule φ B Y = if φ * Y < B then 1 else 0 := by
  unfold defaultRule
  simp only [lt_div_iff₀ hφ, mul_comm Y φ]

/-- AKMM, (24.4), p. 740: the government defaults iff the cost of defaulting `φY₂` is less than
the cost of paying `B₂`, i.e. iff default gives strictly more consumption. -/
theorem eq_24_4 {φ : ℝ} (hφ : 0 < φ) (B Y : ℝ) :
    defaultRule φ B Y = 1 ↔ cons2Of φ B Y 0 < cons2Of φ B Y 1 := by
  rw [(eq_24_3 φ B Y).1, (eq_24_3 φ B Y).2, tp_defaultRule_eq hφ]
  constructor
  · intro h
    split_ifs at h with h'
    · linarith
    · norm_num at h
  · intro h
    have : φ * Y < B := by linarith
    simp only [this, ↓reduceIte]

/-- AKMM, p. 740: the government repays when it is indifferent (`φY₂ = B₂`). -/
theorem tp_repay_at_indifference {φ : ℝ} (hφ : 0 < φ) {B Y : ℝ} (h : φ * Y = B) :
    defaultRule φ B Y = 0 := by
  rw [tp_defaultRule_eq hφ]
  have : ¬ φ * Y < B := by rw [h]; exact lt_irrefl _
  simp only [this, ↓reduceIte]

/-- AKMM, p. 740: `Ĉ₂(B₂, Y₂) = Y₂ − min(φY₂, B₂)`. -/
theorem tp_cons2_eq {φ : ℝ} (hφ : 0 < φ) (B Y : ℝ) : cons2 φ B Y = Y - min (φ * Y) B := by
  unfold cons2 cons2Of
  rw [tp_defaultRule_eq hφ]
  split_ifs with h
  · rw [min_eq_left (by linarith)]; ring
  · rw [min_eq_right (by linarith)]; ring

/-- AKMM, p. 740: the government picks the highest consumption,
`Ĉ₂ = max(Y₂ − B₂, Y₂ − φY₂)`. -/
theorem tp_cons2_eq_max {φ : ℝ} (hφ : 0 < φ) (B Y : ℝ) :
    cons2 φ B Y = max (Y - B) (Y - φ * Y) := by
  rw [tp_cons2_eq hφ]
  rcases le_total (φ * Y) B with h | h
  · rw [min_eq_left h, max_eq_right (by linarith)]
  · rw [min_eq_right h, max_eq_left (by linarith)]

/-- AKMM, (24.4), p. 740: the default rule is optimal: for every increasing `u` and every
decision `D ∈ {0, 1}`, `u(C₂(D)) ≤ u(Ĉ₂)`. -/
theorem tp_defaultRule_optimal {φ : ℝ} (hφ : 0 < φ) {u : ℝ → ℝ} (hu : Monotone u) (B Y D : ℝ)
    (hD : D = 0 ∨ D = 1) : u (cons2Of φ B Y D) ≤ u (cons2 φ B Y) := by
  apply hu
  rw [tp_cons2_eq_max hφ]
  rcases hD with rfl | rfl
  · rw [(eq_24_3 φ B Y).1]; exact le_max_left _ _
  · rw [(eq_24_3 φ B Y).2]; exact le_max_right _ _

/-- AKMM, p. 741: `Ĉ₂` is nonincreasing in `B₂`. -/
theorem tp_cons2_antitone {φ : ℝ} (hφ : 0 < φ) (Y : ℝ) : Antitone fun B => cons2 φ B Y := by
  intro B B' h
  simp only [tp_cons2_eq hφ]
  linarith [min_le_min_left (φ * Y) h]

/-- `Ĉ₂` is continuous in `B₂` (no jump at the threshold `B₂ = φY₂`). -/
theorem tp_cons2_continuous {φ : ℝ} (hφ : 0 < φ) (Y : ℝ) : Continuous fun B => cons2 φ B Y := by
  simp only [tp_cons2_eq hφ]
  fun_prop

/-- Bounds: `(1 − φ)Y₂ ≤ Ĉ₂ ≤ Y₂` for `B₂ ≥ 0` and `Y₂ ≥ 0`. -/
theorem tp_cons2_bounds {φ : ℝ} (hφ : 0 < φ) {B Y : ℝ} (hB : 0 ≤ B) (hY : 0 ≤ Y) :
    Y - φ * Y ≤ cons2 φ B Y ∧ cons2 φ B Y ≤ Y := by
  rw [tp_cons2_eq hφ]
  exact ⟨by linarith [min_le_left (φ * Y) B],
    by linarith [le_min (mul_nonneg hφ.le hY) hB]⟩

/-- `1 − D̂₂(B₂, Y₂)` is the indicator of `{Y₂ ≥ B₂/φ}`. -/
theorem tp_one_sub_defaultRule (φ B Y : ℝ) :
    1 - defaultRule φ B Y = (Set.Ici (B / φ)).indicator 1 Y := by
  unfold defaultRule Set.indicator
  by_cases h : Y < B / φ
  · have : Y ∉ Set.Ici (B / φ) := fun h' => absurd (Set.mem_Ici.1 h') (not_le.2 h)
    simp only [h, ↓reduceIte, this]; ring
  · have : Y ∈ Set.Ici (B / φ) := Set.mem_Ici.2 (not_lt.1 h)
    simp only [h, ↓reduceIte, this, Pi.one_apply]; ring

/-- AKMM, (24.5), p. 741: the bond price is the expected repayment per bond,
`q₁(B₂) = E[1 − D̂₂(B₂, Y₂)]`. -/
noncomputable def price (μ : Measure ℝ) (φ B : ℝ) : ℝ := ∫ y, (1 - defaultRule φ B y) ∂μ

/-- The price is the repayment probability `Pr(Y₂ ≥ B₂/φ)`. -/
theorem tp_price_eq_measure (μ : Measure ℝ) (φ B : ℝ) : price μ φ B = μ.real (Set.Ici (B / φ)) := by
  unfold price
  simp only [tp_one_sub_defaultRule]
  exact integral_indicator_one measurableSet_Ici

/-- With no atoms, `Pr(Y₂ ≥ x) = 1 − F(x)`. -/
theorem tp_measureReal_Ici {μ : Measure ℝ} [IsProbabilityMeasure μ] (hna : ∀ x, μ {x} = 0)
    (x : ℝ) : μ.real (Set.Ici x) = 1 - cdf μ x := by
  rw [cdf_eq_real]
  have h1 : Set.Ici x = (Set.Iio x)ᶜ := (Set.compl_Iio).symm
  have h2 : μ (Set.Iio x) = μ (Set.Iic x) := by
    rw [← Set.Iic_sdiff_right]
    exact measure_sdiff_null (hna x)
  rw [h1, measureReal_compl measurableSet_Iio, probReal_univ]
  simp only [Measure.real, h2]

/-- **AKMM, (24.5)**, p. 741: when `Y₂` has no atoms (it has a density), the price is the
repayment probability, `q₁(B₂) = Pr(Y₂ ≥ B₂/φ) = 1 − F(B₂/φ)`. -/
theorem eq_24_5 {μ : Measure ℝ} [IsProbabilityMeasure μ] (hna : ∀ x, μ {x} = 0) (φ B : ℝ) :
    price μ φ B = μ.real {y | B / φ ≤ y} ∧ price μ φ B = 1 - cdf μ (B / φ) :=
  ⟨tp_price_eq_measure μ φ B, (tp_price_eq_measure μ φ B).trans (tp_measureReal_Ici hna _)⟩

/-- AKMM, (24.5), p. 741, as printed: the middle term `Pr(Y₂ < B₂/φ)` is the default
probability, not the price. With `Y₂ ≥ 0` almost surely, at `B₂ = 0` the price is `1` while
`Pr(Y₂ < 0) = 0`. -/
theorem eq_24_5_printed_false {μ : Measure ℝ} [IsProbabilityMeasure μ] (h0 : μ (Set.Iio 0) = 0)
    (φ : ℝ) : price μ φ 0 = 1 ∧ μ.real {y | y < 0 / φ} = 0 := by
  have hs : {y : ℝ | y < 0 / φ} = Set.Iio 0 := by ext y; simp
  refine ⟨?_, by rw [hs, Measure.real, h0]; rfl⟩
  rw [tp_price_eq_measure, zero_div, ← Set.compl_Iio, measureReal_compl measurableSet_Iio,
    probReal_univ, Measure.real, h0]
  simp

/-- An admissible law: the uniform law on `[0, 1]` is a probability measure on `Y₂ ≥ 0` without
atoms. -/
theorem tp_uniform_admissible :
    IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) ∧
      (∀ x : ℝ, volume.restrict (Set.Icc (0 : ℝ) 1) {x} = 0) ∧
      volume.restrict (Set.Icc (0 : ℝ) 1) (Set.Iio 0) = 0 := by
  refine ⟨⟨by simp⟩, fun x => ?_, ?_⟩
  · rw [Measure.restrict_apply (measurableSet_singleton x)]
    exact measure_mono_null Set.inter_subset_left (Real.volume_singleton)
  rw [Measure.restrict_apply measurableSet_Iio]
  have : Set.Iio (0 : ℝ) ∩ Set.Icc 0 1 = ∅ := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_empty_iff_false,
      iff_false, not_and, not_le]; intro h h'; linarith
  rw [this, measure_empty]

/-- AKMM, p. 741: `q₁` is the competitive (zero-profit) price. A lender paying `p` per bond
expects the profit `q₁(B₂) − p` (no discounting): (i) bidding above `q₁` loses money in
expectation; (ii) at any bid below `q₁` a rival can bid slightly more and still profit, so it is
outbid. -/
theorem tp_zero_profit (μ : Measure ℝ) (φ B : ℝ) :
    (∀ p, price μ φ B < p → price μ φ B - p < 0) ∧
      ∀ p, p < price μ φ B → ∃ p', p < p' ∧ 0 < price μ φ B - p' := by
  refine ⟨fun p hp => by linarith, fun p hp => ⟨(p + price μ φ B) / 2, by linarith, by linarith⟩⟩

/-- The price lies in `[0, 1]`. -/
theorem tp_price_mem_Icc (μ : Measure ℝ) [IsProbabilityMeasure μ] (φ B : ℝ) :
    0 ≤ price μ φ B ∧ price μ φ B ≤ 1 := by
  rw [tp_price_eq_measure]
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

/-- AKMM, p. 739: with `Y₂ ≥ 0` almost surely, an unindebted government always repays, so
`q₁(0) = 1`. -/
theorem tp_price_zero {μ : Measure ℝ} [IsProbabilityMeasure μ] (h0 : μ (Set.Iio 0) = 0)
    (φ : ℝ) : price μ φ 0 = 1 :=
  (eq_24_5_printed_false h0 φ).1

/-- AKMM, p. 741: "the bond price decreases with the number of bonds issued" (weakly). -/
theorem tp_price_antitone (μ : Measure ℝ) [IsFiniteMeasure μ] {φ : ℝ} (hφ : 0 < φ) :
    Antitone (price μ φ) := by
  intro B B' h
  simp only [tp_price_eq_measure]
  exact measureReal_mono (Set.Ici_subset_Ici.2 (div_le_div_of_nonneg_right h hφ.le))

/-- AKMM, p. 741: the bond price strictly decreases in `B₂ ≥ 0` when the law of `Y₂` puts
positive mass on every interval of `[0, ∞)` (the book's `f(Y₂) > 0` for `Y₂ ≥ 0`). -/
theorem tp_price_strictAntiOn (μ : Measure ℝ) [IsFiniteMeasure μ] {φ : ℝ} (hφ : 0 < φ)
    (hpos : ∀ a b : ℝ, 0 ≤ a → a < b → 0 < μ (Set.Ioo a b)) :
    StrictAntiOn (price μ φ) (Set.Ici 0) := by
  intro B hB B' _ h
  simp only [tp_price_eq_measure]
  have hlt : B / φ < B' / φ := div_lt_div_of_pos_right h hφ
  have hsplit : Set.Ici (B / φ) = Set.Ico (B / φ) (B' / φ) ∪ Set.Ici (B' / φ) :=
    (Set.Ico_union_Ici_eq_Ici hlt.le).symm
  have hdisj : Disjoint (Set.Ico (B / φ) (B' / φ)) (Set.Ici (B' / φ)) :=
    Set.disjoint_left.2 fun y hy hy' => absurd (Set.mem_Ici.1 hy') (not_le.2 hy.2)
  rw [hsplit, measureReal_union hdisj measurableSet_Ici]
  have : 0 < μ.real (Set.Ico (B / φ) (B' / φ)) := by
    rw [Measure.real, ENNReal.toReal_pos_iff]
    exact ⟨(hpos _ _ (div_nonneg (Set.mem_Ici.1 hB) hφ.le) hlt).trans_le
      (measure_mono Set.Ioo_subset_Ico_self), measure_lt_top _ _⟩
  linarith

/-- The price tends to `0` as `B₂ → ∞` (`F(x) → 1`). -/
theorem tp_price_tendsto_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] {φ : ℝ} (hφ : 0 < φ) :
    Tendsto (price μ φ) atTop (𝓝 0) := by
  have hc : Tendsto (fun B : ℝ => 1 - cdf μ (B / φ - 1)) atTop (𝓝 0) := by
    have := (tendsto_cdf_atTop μ).comp
      ((tendsto_atTop_add_const_right _ (-1) (tendsto_id.atTop_div_const hφ)))
    simpa [sub_eq_add_neg] using (tendsto_const_nhds (x := (1 : ℝ))).sub this
  refine squeeze_zero (fun B => (tp_price_mem_Icc μ φ B).1) (fun B => ?_) hc
  rw [tp_price_eq_measure, cdf_eq_real, ← probReal_compl_eq_one_sub measurableSet_Iic]
  exact measureReal_mono (fun y hy => by
    simp only [Set.mem_Ici] at hy
    simp only [Set.mem_compl_iff, Set.mem_Iic, not_le]; linarith)

/-- With no atoms the price is continuous in `B₂`. -/
theorem tp_price_continuous {μ : Measure ℝ} [IsProbabilityMeasure μ] (hna : ∀ x, μ {x} = 0)
    (φ : ℝ) : Continuous (price μ φ) := by
  rw [continuous_iff_continuousAt]
  intro B₀
  apply continuousAt_of_dominated (bound := fun _ => 1)
  · exact Eventually.of_forall fun B => by
      simp only [tp_one_sub_defaultRule]
      exact (aestronglyMeasurable_const.indicator measurableSet_Ici)
  · exact Eventually.of_forall fun B => Eventually.of_forall fun y => by
      rw [tp_one_sub_defaultRule]
      simp only [Set.indicator, Pi.one_apply]
      split_ifs <;> norm_num
  · exact integrable_const _
  · have hnull : ∀ᵐ y ∂μ, y ≠ B₀ / φ := by
      rw [ae_iff]; simpa using hna (B₀ / φ)
    filter_upwards [hnull] with y hy
    have hcont : Continuous fun B : ℝ => B / φ := by fun_prop
    rcases lt_or_gt_of_ne hy with h | h
    · have hev : ∀ᶠ B in 𝓝 B₀, y < B / φ :=
        hcont.continuousAt.eventually (isOpen_Ioi.mem_nhds h)
      refine (continuousAt_const (y := (0 : ℝ))).congr (hev.mono fun B hB => ?_)
      simp only [defaultRule, hB, ↓reduceIte]; ring
    · have hev : ∀ᶠ B in 𝓝 B₀, B / φ < y :=
        hcont.continuousAt.eventually (isOpen_Iio.mem_nhds h)
      refine (continuousAt_const (y := (1 : ℝ))).congr (hev.mono fun B hB => ?_)
      simp only [defaultRule, not_lt.2 hB.le, ↓reduceIte]; ring

/-- AKMM, (24.6), p. 741, the price derivative: if `F` has derivative (density) `f` at `B₂/φ`,
then `dq₁/dB₂ = −f(B₂/φ)/φ`. -/
theorem tp_price_hasDerivAt {μ : Measure ℝ} [IsProbabilityMeasure μ] (hna : ∀ x, μ {x} = 0)
    {φ B f : ℝ} (hF : HasDerivAt (cdf μ) f (B / φ)) :
    HasDerivAt (price μ φ) (-(f / φ)) B := by
  have he : price μ φ = fun B => 1 - cdf μ (B / φ) := funext fun B => (eq_24_5 hna φ B).2
  rw [he]
  have hd : HasDerivAt (fun B : ℝ => B / φ) (1 / φ) B := (hasDerivAt_id B).div_const φ
  have h2 : HasDerivAt (fun B => 1 - cdf μ (B / φ)) (-(f * (1 / φ))) B :=
    HasDerivAt.const_sub 1 (HasDerivAt.comp B hF hd)
  convert h2 using 1
  ring

/-- **AKMM, footnote 8**, p. 741: with income-contingent payments `b(Y₂) ≤ φY₂` the government
never defaults (repaying is weakly better, and it repays at indifference). Moreover the
contingent schedule `b(Y₂) = B₂(1 − D̂₂(B₂, Y₂))` satisfies `0 ≤ b ≤ φY₂`, pays lenders exactly
what the non-contingent bond pays, and leaves the government at least the consumption `Ĉ₂`,
strictly more in default states with `Y₂ > 0`: income-contingent debt expands borrowing
opportunities and eliminates defaults. -/
theorem fn_8 {φ : ℝ} (hφ : 0 < φ) {B Y : ℝ} (hB : 0 ≤ B) (hY : 0 ≤ Y) :
    B * (1 - defaultRule φ B Y) ≤ φ * Y ∧ 0 ≤ B * (1 - defaultRule φ B Y) ∧
      cons2 φ B Y ≤ Y - B * (1 - defaultRule φ B Y) ∧
      (defaultRule φ B Y = 1 → 0 < Y → cons2 φ B Y < Y - B * (1 - defaultRule φ B Y)) := by
  unfold cons2 cons2Of
  rw [tp_defaultRule_eq hφ]
  split_ifs with h
  · refine ⟨by nlinarith, by norm_num, by nlinarith, fun _ hY' => by nlinarith⟩
  · refine ⟨by nlinarith, by linarith, by linarith, fun h1 => by norm_num at h1⟩

/-- AKMM, footnote 8: a contingent payment `b(Y₂) ≤ φY₂` is never defaulted on: the default
rule applied to `b(Y₂)` repays. -/
theorem tp_contingent_no_default {φ : ℝ} (hφ : 0 < φ) {b Y : ℝ} (hb : b ≤ φ * Y) :
    defaultRule φ b Y = 0 := by
  rw [tp_defaultRule_eq hφ]
  simp only [not_lt.2 hb, ↓reduceIte]

/-- AKMM, footnote 8: the contingent schedule `B₂(1 − D̂₂)` raises the same revenue
`E[B₂(1 − D̂₂)] = B₂q₁(B₂)` as the non-contingent bond. -/
theorem tp_contingent_revenue (μ : Measure ℝ) (φ B : ℝ) :
    ∫ y, B * (1 - defaultRule φ B y) ∂μ = B * price μ φ B := by
  unfold price
  exact integral_const_mul B _

/-- **AKMM, footnote 14**, p. 745: if the conditional c.d.f. `F(· | Y₁)` of period-2 income is
nonincreasing in period-1 income `Y₁` (first-order stochastic dominance), then the price
`q₁(B₂, Y₁) = 1 − F(B₂/φ | Y₁)` is nondecreasing in `Y₁`; strictly so under strict
dominance. -/
theorem fn_14 {μ : ℝ → Measure ℝ} [∀ y, IsProbabilityMeasure (μ y)]
    (hna : ∀ y x, μ y {x} = 0) (φ B : ℝ) :
    (Antitone (fun Y₁ => cdf (μ Y₁) (B / φ)) → Monotone (fun Y₁ => price (μ Y₁) φ B)) ∧
      (StrictAnti (fun Y₁ => cdf (μ Y₁) (B / φ)) →
        StrictMono (fun Y₁ => price (μ Y₁) φ B)) := by
  have he : ∀ Y₁, price (μ Y₁) φ B = 1 - cdf (μ Y₁) (B / φ) :=
    fun Y₁ => (eq_24_5 (hna Y₁) φ B).2
  refine ⟨fun h a b hab => ?_, fun h a b hab => ?_⟩
  · simp only [he]; linarith [h hab]
  · simp only [he]; linarith [h hab]

end AKMM.SovereignDefault

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The two-period default model: optimal borrowing and the Euler equation (24.6)

AKMM, §24.3, p. 741. The government chooses `B₂ ≥ 0` to maximise
`W(B₂) = u(B₂q₁(B₂)) + βE u(Ĉ₂(B₂, Y₂))`.

* **Existence** (`tp_exists_optimal`): if `u` is continuous, nondecreasing and strictly
  increasing on `[0, ∞)`, `E|u(Y₂)|`, `E|u((1 − φ)Y₂)|` and `E Y₂` are finite, `Y₂ ≥ 0` has no
  atoms and is positive with positive probability, then an optimal `B̂₂ ≥ 0` exists. The revenue
  `B₂q₁(B₂) ≤ φE[Y₂; Y₂ ≥ B₂/φ]` vanishes as `B₂ → ∞`, so `W` tends to a limit that some small
  positive debt beats; on a compact interval `W` is continuous.
* **The Laffer side** (`tp_laffer_side`): at an optimum `B̂₂ > 0` the revenue `B₂q₁(B₂)` cannot be
  decreasing, `q₁ + B₂ dq₁/dB₂ ≥ 0`: otherwise a write-down raises revenue (Obstfeld–Rogoff's
  `writedown_raises_value`, imported) and weakly raises `Ĉ₂`.
* **Leibniz rule** (`tp_hasDerivAt_expectedUtility`): for `0 < φ < 1` and concave increasing
  differentiable `u`, `d/dB₂ E u(Ĉ₂) = −E[u′(Ĉ₂)(1 − D̂₂)]`; the boundary term vanishes because
  `Ĉ₂` is continuous at `Y₂ = B₂/φ` and the threshold has probability zero.
* **(24.6)** (`eq_24_6`): at an interior optimum where `q₁` is differentiable,
  `u′(C₁)[q₁ + B₂ dq₁/dB₂] = βE[u′(Ĉ₂)(1 − D̂₂)]`.

Departure: `u` is real valued (the Inada condition `u′(0) = ∞` is not needed; `log` is excluded
from the existence theorem, which needs `u` continuous at `0`, but not from the Leibniz rule).
-/

namespace AKMM.SovereignDefault

open MeasureTheory Filter Topology ProbabilityTheory

/-- AKMM, p. 741: the period-1 objective `W(B₂) = u(B₂q₁(B₂)) + βE u(Ĉ₂(B₂, Y₂))`. -/
noncomputable def tp_objective (μ : Measure ℝ) (φ β : ℝ) (u : ℝ → ℝ) (B : ℝ) : ℝ :=
  u (B * price μ φ B) + β * ∫ y, u (cons2 φ B y) ∂μ

/-- `Ĉ₂` is continuous in `Y₂`. -/
theorem tp_cons2_continuous_Y {φ : ℝ} (hφ : 0 < φ) (B : ℝ) : Continuous fun Y => cons2 φ B Y := by
  simp only [tp_cons2_eq hφ]
  fun_prop

/-- `Ĉ₂` is `1`-Lipschitz in `B₂`. -/
theorem tp_cons2_lipschitz {φ : ℝ} (hφ : 0 < φ) (B B' Y : ℝ) :
    |cons2 φ B Y - cons2 φ B' Y| ≤ |B - B'| := by
  simp only [tp_cons2_eq hφ]
  have := abs_min_sub_min_le_max (φ * Y) B (φ * Y) B'
  rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)] at this
  rw [show Y - min (φ * Y) B - (Y - min (φ * Y) B') = -(min (φ * Y) B - min (φ * Y) B') by ring,
    abs_neg]
  exact this

/-- The revenue `B₂q₁(B₂)` vanishes as `B₂ → ∞` when `E Y₂ < ∞`:
`B₂ Pr(Y₂ ≥ B₂/φ) ≤ φE[Y₂; Y₂ ≥ B₂/φ] → 0`. -/
theorem tp_revenue_tendsto_zero {μ : Measure ℝ} [IsProbabilityMeasure μ] {φ : ℝ} (hφ : 0 < φ)
    (hY : Integrable (fun y : ℝ => y) μ) :
    Tendsto (fun B => B * price μ φ B) atTop (𝓝 0) := by
  have hT : Tendsto (fun B : ℝ => φ * ∫ y, (Set.Ici (B / φ)).indicator (fun y => y) y ∂μ)
      atTop (𝓝 (φ * 0)) := by
    refine Tendsto.const_mul φ ?_
    refine tendsto_integral_filter_of_dominated_convergence (l := (atTop : Filter ℝ))
      (F := fun B y => (Set.Ici (B / φ)).indicator (fun y : ℝ => y) y) (f := fun _ => (0 : ℝ))
      (fun y => |y|) ?_ ?_ hY.abs ?_ |>.trans_eq (by rw [integral_zero])
    · exact Eventually.of_forall fun B =>
        (hY.aestronglyMeasurable.indicator measurableSet_Ici)
    · exact Eventually.of_forall fun B => Eventually.of_forall fun y => by
        simp only [Set.indicator]; split_ifs <;> simp
    · refine Eventually.of_forall fun y => ?_
      have hev : ∀ᶠ B in atTop, y < B / φ :=
        (tendsto_id.atTop_div_const hφ).eventually (eventually_gt_atTop y)
      refine tendsto_const_nhds.congr' (hev.mono fun B hB => ?_)
      have : y ∉ Set.Ici (B / φ) := fun h => absurd (Set.mem_Ici.1 h) (not_le.2 hB)
      simp only [Set.indicator, this, ↓reduceIte]
  rw [mul_zero] at hT
  have hle : ∀ᶠ B in atTop, B * price μ φ B ≤
      φ * ∫ y, (Set.Ici (B / φ)).indicator (fun y => y) y ∂μ := by
    filter_upwards [eventually_ge_atTop 0] with B hB
    rw [price, ← integral_const_mul, ← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun y => ?_)
      ((hY.indicator measurableSet_Ici).const_mul φ) (Eventually.of_forall fun y => ?_)
    · simp only [tp_one_sub_defaultRule, Pi.zero_apply]
      exact mul_nonneg hB (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    · simp only [tp_one_sub_defaultRule, Set.indicator, Pi.one_apply]
      split_ifs with h
      · rw [Set.mem_Ici, div_le_iff₀ hφ] at h; linarith
      · simp
  have hge : ∀ᶠ B in atTop, 0 ≤ B * price μ φ B := by
    filter_upwards [eventually_ge_atTop 0] with B hB
    exact mul_nonneg hB (tp_price_mem_Icc μ φ B).1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT hge hle

/-- **Existence of an optimal `B₂`** (AKMM, p. 741). Under the hypotheses listed in the module
docstring the period-1 problem `max_{B₂ ≥ 0} W(B₂)` has a solution. -/
theorem tp_exists_optimal {μ : Measure ℝ} [IsProbabilityMeasure μ] (hna : ∀ x, μ {x} = 0)
    (h0 : μ (Set.Iio 0) = 0) (hpos : μ (Set.Ioi 0) ≠ 0) {φ β : ℝ} (hφ : 0 < φ) (hβ : 0 ≤ β)
    {u : ℝ → ℝ} (hu : Continuous u) (hmono : Monotone u) (hstrict : StrictMonoOn u (Set.Ici 0))
    (hiY : Integrable (fun y => u y) μ) (hiD : Integrable (fun y => u (y - φ * y)) μ)
    (hY : Integrable (fun y : ℝ => y) μ) :
    ∃ B₀, 0 ≤ B₀ ∧ ∀ B, 0 ≤ B → tp_objective μ φ β u B ≤ tp_objective μ φ β u B₀ := by
  have hy0 : ∀ᵐ y ∂μ, 0 ≤ y := by
    rw [ae_iff]; simp only [not_le]; exact h0
  have hmeasB : ∀ B, AEStronglyMeasurable (fun y => u (cons2 φ B y)) μ := fun B =>
    (hu.comp (tp_cons2_continuous_Y hφ B)).aestronglyMeasurable
  have hbound : ∀ B, 0 ≤ B → ∀ᵐ y ∂μ, ‖u (cons2 φ B y)‖ ≤ |u y| + |u (y - φ * y)| := by
    intro B hB
    filter_upwards [hy0] with y hy
    obtain ⟨h1, h2⟩ := tp_cons2_bounds hφ hB hy
    have a1 := hmono h1
    have a2 := hmono h2
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> cases abs_cases (u y) <;> cases abs_cases (u (y - φ * y)) <;> linarith
  have hint : ∀ B, 0 ≤ B → Integrable (fun y => u (cons2 φ B y)) μ := fun B hB =>
    (hiY.abs.add hiD.abs).mono' (hmeasB B) (hbound B hB)
  set G : ℝ → ℝ := fun B => ∫ y, u (cons2 φ B y) ∂μ with hG
  -- continuity of `G` on `[0, ∞)`
  have hGc : ContinuousOn G (Set.Ici 0) :=
    continuousOn_of_dominated (fun B _ => hmeasB B) (fun B hB => hbound B hB)
      (hiY.abs.add hiD.abs) (Eventually.of_forall fun y =>
        (hu.comp (tp_cons2_continuous hφ y)).continuousOn)
  -- the limit of `G`
  have hGlim : Tendsto G atTop (𝓝 (∫ y, u (y - φ * y) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun y => |u y| + |u (y - φ * y)|)
      (Eventually.of_forall fun B => hmeasB B) ?_ (hiY.abs.add hiD.abs) ?_
    · filter_upwards [eventually_ge_atTop 0] with B hB using hbound B hB
    · refine Eventually.of_forall fun y => tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop (φ * y)] with B hB
      rw [tp_cons2_eq hφ, min_eq_left hB.le]
  have hRc : Continuous fun B => B * price μ φ B := continuous_id.mul (tp_price_continuous hna φ)
  have hWc : ContinuousOn (tp_objective μ φ β u) (Set.Ici 0) :=
    ((hu.comp hRc).continuousOn).add (continuousOn_const.mul hGc)
  have hWlim : Tendsto (tp_objective μ φ β u) atTop
      (𝓝 (u 0 + β * ∫ y, u (y - φ * y) ∂μ)) :=
    ((hu.tendsto 0).comp (tp_revenue_tendsto_zero hφ hY)).add (hGlim.const_mul β)
  -- a debt level with positive revenue
  obtain ⟨x, hx, hxμ⟩ : ∃ x : ℝ, 0 < x ∧ μ (Set.Ici x) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    apply hpos
    have : Set.Ioi (0 : ℝ) = ⋃ n : ℕ, Set.Ici (1 / ((n : ℝ) + 1)) := by
      ext y
      simp only [Set.mem_Ioi, Set.mem_iUnion, Set.mem_Ici]
      constructor
      · intro hy
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hy
        exact ⟨n, hn.le⟩
      · rintro ⟨n, hn⟩
        exact lt_of_lt_of_le (by positivity) hn
    rw [this]
    exact measure_iUnion_null fun n => hcon _ (by positivity)
  set B₁ := φ * x with hB₁
  have hB₁0 : 0 < B₁ := mul_pos hφ hx
  have hR₁ : 0 < B₁ * price μ φ B₁ := by
    refine mul_pos hB₁0 ?_
    rw [tp_price_eq_measure, hB₁, mul_div_cancel_left₀ _ hφ.ne', Measure.real,
      ENNReal.toReal_pos_iff]
    exact ⟨pos_iff_ne_zero.2 hxμ, measure_lt_top _ _⟩
  have hGge : ∫ y, u (y - φ * y) ∂μ ≤ G B₁ := by
    refine integral_mono_ae hiD (hint B₁ hB₁0.le) ?_
    filter_upwards [hy0] with y hy using hmono (tp_cons2_bounds hφ hB₁0.le hy).1
  have hbeat : u 0 + β * ∫ y, u (y - φ * y) ∂μ < tp_objective μ φ β u B₁ := by
    have := hstrict (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hR₁.le) hR₁
    unfold tp_objective
    nlinarith [mul_le_mul_of_nonneg_left hGge hβ]
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hWlim.eventually (gt_mem_nhds hbeat))
  set M := max K B₁
  obtain ⟨B₀, hB₀, hmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := M)).exists_isMaxOn
    ⟨0, Set.left_mem_Icc.2 (hB₁0.le.trans (le_max_right _ _))⟩
    (hWc.mono Set.Icc_subset_Ici_self)
  refine ⟨B₀, hB₀.1, fun B hB => ?_⟩
  rcases le_or_gt B M with h | h
  · exact hmax ⟨hB, h⟩
  · have hB1 : B₁ ∈ Set.Icc 0 M := ⟨hB₁0.le, le_max_right _ _⟩
    exact ((hK B ((le_max_left _ _).trans h.le)).le).trans (hmax hB1)

/-- **The optimum is on the increasing side of the debt Laffer curve** (AKMM, p. 741, the
marginal revenue `q₁ + B₂dq₁/dB₂` in (24.6)): at an optimum `B̂₂ > 0` where the revenue
`R(B₂) = B₂q₁(B₂)` has derivative `r`, `r ≥ 0`. Proof: if `r < 0`, a small write-down raises
revenue (Obstfeld–Rogoff, p. 395, `writedown_raises_value`) and weakly raises `Ĉ₂`. -/
theorem tp_laffer_side {μ : Measure ℝ} {φ β : ℝ} (hφ : 0 < φ) (hβ : 0 ≤ β) {u : ℝ → ℝ}
    (hmono : Monotone u) (hstrict : StrictMonoOn u (Set.Ici 0))
    (hint : ∀ B, 0 ≤ B → Integrable (fun y => u (cons2 φ B y)) μ) [IsProbabilityMeasure μ]
    {B₀ r : ℝ} (hB₀ : 0 < B₀)
    (hopt : ∀ B, 0 ≤ B → tp_objective μ φ β u B ≤ tp_objective μ φ β u B₀)
    (hr : HasDerivAt (fun B => B * price μ φ B) r B₀) : 0 ≤ r := by
  by_contra hneg
  rw [not_le] at hneg
  have hev := ObstfeldRogoff.CapitalMarketImperfections.DebtOverhangLaffer.writedown_raises_value
    hr hneg
  have hpos : ∀ᶠ B in 𝓝[<] B₀, 0 < B := nhdsWithin_le_nhds (eventually_gt_nhds hB₀)
  obtain ⟨B, ⟨hB1, hB2⟩, hB3⟩ := ((hev.and hpos).and self_mem_nhdsWithin).exists
  have hR0 : 0 ≤ B₀ * price μ φ B₀ := mul_nonneg hB₀.le (tp_price_mem_Icc μ φ B₀).1
  have hu1 := hstrict (Set.mem_Ici.2 hR0) (Set.mem_Ici.2 (hR0.trans hB1.le)) hB1
  have hG : ∫ y, u (cons2 φ B₀ y) ∂μ ≤ ∫ y, u (cons2 φ B y) ∂μ :=
    integral_mono (hint B₀ hB₀.le) (hint B hB2.le) fun y =>
      hmono (tp_cons2_antitone hφ y (le_of_lt (Set.mem_Iio.1 hB3)))
  have := hopt B hB2.le
  unfold tp_objective at this
  nlinarith [mul_le_mul_of_nonneg_left hG hβ]

/-- **Leibniz rule for the expected period-2 utility** (AKMM, p. 741, the right-hand side of
(24.6)): for `0 < φ < 1`, `B₂ > 0`, `Y₂` without atoms and `u` differentiable, increasing and
concave on `(0, ∞)`, `d/dB₂ E u(Ĉ₂(B₂, Y₂)) = −E[u′(Ĉ₂)(1 − D̂₂)]`. -/
theorem tp_hasDerivAt_expectedUtility {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hna : ∀ x, μ {x} = 0) {φ : ℝ} (hφ : 0 < φ) (hφ1 : φ < 1) {u : ℝ → ℝ} (hum : Measurable u)
    (hd : ∀ c, 0 < c → DifferentiableAt ℝ u c) (hanti : AntitoneOn (deriv u) (Set.Ioi 0))
    (hnn : ∀ c, 0 < c → 0 ≤ deriv u c) {B₀ : ℝ} (hB₀ : 0 < B₀)
    (hint : Integrable (fun y => u (cons2 φ B₀ y)) μ) :
    HasDerivAt (fun B => ∫ y, u (cons2 φ B y) ∂μ)
      (-∫ y, deriv u (cons2 φ B₀ y) * (1 - defaultRule φ B₀ y) ∂μ) B₀ := by
  set c₀ := (1 - φ) * (B₀ / 2) / φ with hc₀
  have hc₀pos : 0 < c₀ := div_pos (mul_pos (by linarith) (by linarith)) hφ
  set L := deriv u c₀
  have hL : 0 ≤ L := hnn c₀ hc₀pos
  -- `u` is `L`-Lipschitz on `[c₀, ∞)`
  have hLip : LipschitzOnWith (Real.nnabs L) u (Set.Ici c₀) := by
    refine (convex_Ici c₀).lipschitzOnWith_of_nnnorm_hasDerivWithin_le (f' := deriv u)
      (fun c hc => ((hd c (hc₀pos.trans_le hc)).hasDerivAt).hasDerivWithinAt) fun c hc => ?_
    have hc' : 0 < c := hc₀pos.trans_le hc
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, Real.coe_nnabs,
      abs_of_nonneg (hnn c hc'), abs_of_nonneg hL]
    exact hanti hc₀pos hc' hc
  set F' : ℝ → ℝ := fun y => -(deriv u (cons2 φ B₀ y) * (1 - defaultRule φ B₀ y)) with hF'
  have hball : Metric.ball B₀ (B₀ / 2) ∈ 𝓝 B₀ := Metric.ball_mem_nhds _ (by linarith)
  have hmeas : ∀ B, AEStronglyMeasurable (fun y => u (cons2 φ B y)) μ := fun B =>
    (hum.comp (tp_cons2_continuous_Y hφ B).measurable).aestronglyMeasurable
  have hF'm : AEStronglyMeasurable F' μ := by
    have h1 : (fun y => 1 - defaultRule φ B₀ y) = (Set.Ici (B₀ / φ)).indicator 1 :=
      funext (tp_one_sub_defaultRule φ B₀)
    have h2 : Measurable fun y => 1 - defaultRule φ B₀ y := by
      rw [h1]; exact measurable_const.indicator measurableSet_Ici
    exact (((measurable_deriv u).comp (tp_cons2_continuous_Y hφ B₀).measurable).mul h2).neg
      |>.aestronglyMeasurable
  have hlip : ∀ y, LipschitzOnWith (Real.nnabs L) (fun B => u (cons2 φ B y))
      (Metric.ball B₀ (B₀ / 2)) := by
    intro y
    refine LipschitzOnWith.of_dist_le_mul fun B hB B' hB' => ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hB hB'
    rw [Real.coe_nnabs, abs_of_nonneg hL]
    by_cases hy : φ * y < B₀ / 2
    · rw [tp_cons2_eq hφ, tp_cons2_eq hφ, min_eq_left (by linarith), min_eq_left (by linarith),
        dist_self]
      exact mul_nonneg hL dist_nonneg
    · rw [not_lt] at hy
      have hy' : B₀ / 2 / φ ≤ y := by rw [div_le_iff₀ hφ]; linarith
      have hmem : ∀ B'', c₀ ≤ cons2 φ B'' y := fun B'' => by
        rw [tp_cons2_eq hφ, hc₀]
        have : (1 - φ) * (B₀ / 2) / φ ≤ (1 - φ) * y := by
          rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hy' (by linarith)
        linarith [min_le_left (φ * y) B'']
      have := (hLip.dist_le_mul _ (hmem B) _ (hmem B'))
      rw [Real.coe_nnabs, abs_of_nonneg hL] at this
      refine this.trans (mul_le_mul_of_nonneg_left ?_ hL)
      rw [Real.dist_eq, Real.dist_eq]
      exact tp_cons2_lipschitz hφ B B' y
  have hdiff : ∀ᵐ y ∂μ, HasDerivAt (fun B => u (cons2 φ B y)) (F' y) B₀ := by
    have hnull : ∀ᵐ y ∂μ, y ≠ B₀ / φ := by
      rw [ae_iff]; simpa using hna (B₀ / φ)
    filter_upwards [hnull] with y hy
    rcases lt_or_gt_of_ne hy with h | h
    · -- default region: locally constant
      have hφy : φ * y < B₀ := by rwa [lt_div_iff₀ hφ, mul_comm] at h
      have hev : (fun B => u (cons2 φ B y)) =ᶠ[𝓝 B₀] fun _ => u (y - φ * y) := by
        filter_upwards [eventually_gt_nhds hφy] with B hB
        rw [tp_cons2_eq hφ, min_eq_left hB.le]
      have hD : defaultRule φ B₀ y = 1 := by
        rw [tp_defaultRule_eq hφ]; simp only [hφy, ↓reduceIte]
      rw [hF']
      simp only [hD, sub_self, mul_zero, neg_zero]
      exact (hasDerivAt_const B₀ _).congr_of_eventuallyEq hev
    · -- repayment region
      have hφy : B₀ < φ * y := by rwa [div_lt_iff₀ hφ, mul_comm] at h
      have hpos : 0 < y - B₀ := by
        have : 0 < y := lt_trans (div_pos hB₀ hφ) h
        nlinarith
      have hev : (fun B => u (cons2 φ B y)) =ᶠ[𝓝 B₀] fun B => u (y - B) := by
        filter_upwards [eventually_lt_nhds hφy] with B hB
        rw [tp_cons2_eq hφ, min_eq_right hB.le]
      have hD : defaultRule φ B₀ y = 0 := by
        rw [tp_defaultRule_eq hφ]; simp only [not_lt.2 hφy.le, ↓reduceIte]
      have hc : cons2 φ B₀ y = y - B₀ := by rw [tp_cons2_eq hφ, min_eq_right hφy.le]
      have hd1 : HasDerivAt (fun B => u (y - B)) (deriv u (y - B₀) * (0 - 1)) B₀ :=
        HasDerivAt.comp B₀ (hd _ hpos).hasDerivAt ((hasDerivAt_const B₀ y).sub (hasDerivAt_id B₀))
      rw [hF']
      simp only [hD, hc, sub_zero, mul_one]
      convert hd1.congr_of_eventuallyEq hev using 1
      ring
  have := hasDerivAt_integral_of_dominated_loc_of_lip (bound := fun _ => L) hball
    (Eventually.of_forall hmeas) hint hF'm (Eventually.of_forall hlip) (integrable_const L) hdiff
  rw [hF'] at this
  simpa only [integral_neg] using this.2

/-- **AKMM, (24.6)**, p. 741: at an optimum `B̂₂ > 0` (with positive period-1 consumption, a
price differentiable at `B̂₂` with derivative `q′`, and the hypotheses of the Leibniz rule),
`u′(C₁)[q₁(B̂₂) + B̂₂q′] = βE[u′(Ĉ₂)(1 − D̂₂)]`. -/
theorem eq_24_6 {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hna : ∀ x, μ {x} = 0) {φ β : ℝ} (hφ : 0 < φ) (hφ1 : φ < 1) {u : ℝ → ℝ} (hum : Measurable u)
    (hd : ∀ c, 0 < c → DifferentiableAt ℝ u c) (hanti : AntitoneOn (deriv u) (Set.Ioi 0))
    (hnn : ∀ c, 0 < c → 0 ≤ deriv u c) {B₀ q' : ℝ} (hB₀ : 0 < B₀)
    (hint : Integrable (fun y => u (cons2 φ B₀ y)) μ)
    (hopt : ∀ B, 0 ≤ B → tp_objective μ φ β u B ≤ tp_objective μ φ β u B₀)
    (hq : HasDerivAt (price μ φ) q' B₀) (hC₁ : 0 < B₀ * price μ φ B₀) :
    deriv u (B₀ * price μ φ B₀) * (price μ φ B₀ + B₀ * q') =
      β * ∫ y, deriv u (cons2 φ B₀ y) * (1 - defaultRule φ B₀ y) ∂μ := by
  have hR : HasDerivAt (fun B => B * price μ φ B) (1 * price μ φ B₀ + B₀ * q') B₀ :=
    (hasDerivAt_id B₀).mul hq
  have hU := HasDerivAt.comp B₀ (hd _ hC₁).hasDerivAt hR
  have hG := tp_hasDerivAt_expectedUtility hna hφ hφ1 hum hd hanti hnn hB₀ hint
  have hW : HasDerivAt (tp_objective μ φ β u)
      (deriv u (B₀ * price μ φ B₀) * (1 * price μ φ B₀ + B₀ * q') +
        β * -∫ y, deriv u (cons2 φ B₀ y) * (1 - defaultRule φ B₀ y) ∂μ) B₀ :=
    hU.add (hG.const_mul β)
  have hmax : IsLocalMax (tp_objective μ φ β u) B₀ :=
    Filter.mem_of_superset (Ici_mem_nhds hB₀) fun B hB => hopt B hB
  have := hmax.hasDerivAt_eq_zero hW
  linarith

end AKMM.SovereignDefault

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Long-term debt: perpetuities with geometrically declining coupons

AKMM, §24.2.2 (24.2), p. 731; §24.4.1 (24.7)–(24.8), pp. 742–743; §24.4.2 (24.11), p. 744;
Appendix 24.A.2, pp. 902–903.

A bond issued in period `t` pays `δ(1 − δ)^{j−1}` in period `t + j`, `j ≥ 1`.

* (24.7): the stock `B_{t+1} = (1 − δ)B_t + I_t` has the closed form
  `B_t = (1 − δ)^t B₀ + Σ_{s<t}(1 − δ)^{t−1−s} I_s` (`eq_24_7`).
* **`B_t` is a sufficient state** (p. 742): the payment due in period `t + j` on all bonds
  outstanding at the start of `t` is `δ(1 − δ)^j B_t`, whatever the issuance history
  (`ltd_payments_sufficient`); in particular the period-`t` coupon is `δB_t` (`ltd_coupon_due`).
* (24.8) with (24.7) gives the repayment budget of (24.11),
  `C = Y − δB + q[B′ − (1 − δ)B]` (`eq_24_8`).
* The present value of one bond at rate `r` is `δ/(δ + r)` (p. 903), the risk-free price
  (`ltd_pv_bond`); the yield `i` of (p. 903) solves `q = δ/(δ + i)` (`ltd_yield`,
  `ltd_yield_iff`); the Macaulay duration is `(1 + i)/(δ + i)` (p. 902, `ltd_duration`); the
  annualised spread is positive iff `i > r` (`ltd_spread_pos_iff`).
* The haircut (24.2) (`eq_24_2`).

On p. 903 "the present value of future payment obligations ... `δB_t/(δ + r)`" is the value one
period before `t` of the payments on `B_t` (equivalently, the value at `t` of the payments
from `t + 1` on of the end-of-period stock `B_{t+1}`); valued at `t` the payments of `B_t`
are worth `δ(1 + r)B_t/(δ + r)` with the current coupon and `δ(1 − δ)B_t/(δ + r)` without it
(`ltd_pv_stock_timing`).
-/

namespace AKMM.SovereignDefault

open Finset

/-- AKMM, (24.7), p. 742: the debt stock `B_{t+1} = (1 − δ)B_t + I_t`, from `B₀` and issuance
`I`. -/
def ltd_stock (δ B₀ : ℝ) (I : ℕ → ℝ) : ℕ → ℝ
  | 0 => B₀
  | t + 1 => (1 - δ) * ltd_stock δ B₀ I t + I t

/-- **AKMM, (24.7)**, p. 742, closed form:
`B_t = (1 − δ)^t B₀ + Σ_{s<t} (1 − δ)^{t−1−s} I_s`. -/
theorem eq_24_7 (δ B₀ : ℝ) (I : ℕ → ℝ) (t : ℕ) :
    ltd_stock δ B₀ I t = (1 - δ) ^ t * B₀ + ∑ s ∈ range t, (1 - δ) ^ (t - 1 - s) * I s := by
  induction t with
  | zero => simp [ltd_stock]
  | succ n ih =>
    rw [ltd_stock, ih, sum_range_succ, mul_add, mul_sum]
    have : ∀ s ∈ range n, (1 - δ) * ((1 - δ) ^ (n - 1 - s) * I s) =
        (1 - δ) ^ (n + 1 - 1 - s) * I s := by
      intro s hs
      have hs' : s < n := mem_range.1 hs
      rw [← mul_assoc, ← pow_succ']
      congr 2
      omega
    rw [sum_congr rfl this]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul, pow_succ]
    ring

/-- The payment in period `t` on the bonds outstanding at the start of period `0` (`B₀` legacy
bonds, which pay `δ(1 − δ)^t` each in period `t`) and on the bonds issued in periods
`s < t` (`I_s` bonds paying `δ(1 − δ)^{t−s−1}` each). -/
def ltd_payment (δ B₀ : ℝ) (I : ℕ → ℝ) (t : ℕ) : ℝ :=
  δ * (1 - δ) ^ t * B₀ + ∑ s ∈ range t, δ * (1 - δ) ^ (t - s - 1) * I s

/-- AKMM, p. 743: the coupon due in period `t` is `δB_t`. -/
theorem ltd_coupon_due (δ B₀ : ℝ) (I : ℕ → ℝ) (t : ℕ) :
    ltd_payment δ B₀ I t = δ * ltd_stock δ B₀ I t := by
  rw [ltd_payment, eq_24_7, mul_add, mul_sum]
  congr 1
  · ring
  · refine sum_congr rfl fun s _ => ?_
    rw [show t - s - 1 = t - 1 - s by omega]
    ring

/-- **AKMM, p. 742: the current stock is a sufficient state.** Absent new issuance, the payment
due in period `t + j` on all bonds outstanding at the start of period `t` (issued before `t`)
is `δ(1 − δ)^j B_t`: it depends on the history only through `B_t`. -/
theorem ltd_payments_sufficient (δ B₀ : ℝ) (I : ℕ → ℝ) (t j : ℕ) :
    δ * (1 - δ) ^ (t + j) * B₀ + ∑ s ∈ range t, δ * (1 - δ) ^ (t + j - s - 1) * I s =
      δ * (1 - δ) ^ j * ltd_stock δ B₀ I t := by
  rw [eq_24_7, mul_add, mul_sum]
  congr 1
  · ring
  · refine sum_congr rfl fun s hs => ?_
    have hs' : s < t := mem_range.1 hs
    rw [show t + j - s - 1 = j + (t - 1 - s) by omega, pow_add]
    ring

/-- Two issuance histories with the same current stock owe the same future payments. -/
theorem ltd_same_stock_same_payments (δ B₀ B₀' : ℝ) (I I' : ℕ → ℝ) (t : ℕ)
    (h : ltd_stock δ B₀ I t = ltd_stock δ B₀' I' t) (j : ℕ) :
    δ * (1 - δ) ^ (t + j) * B₀ + ∑ s ∈ range t, δ * (1 - δ) ^ (t + j - s - 1) * I s =
      δ * (1 - δ) ^ (t + j) * B₀' + ∑ s ∈ range t, δ * (1 - δ) ^ (t + j - s - 1) * I' s := by
  rw [ltd_payments_sufficient, ltd_payments_sufficient, h]

/-- **AKMM, (24.8)**, p. 743, with (24.7): the budget `C_t + δB_t = Y_t + I_t q_t` with
`I_t = B_{t+1} − (1 − δ)B_t` is the repayment constraint of (24.11),
`C = Y − δB + q[B′ − (1 − δ)B]`. -/
theorem eq_24_8 (δ B₀ : ℝ) (I : ℕ → ℝ) (t : ℕ) (C Y q : ℝ)
    (h : C + δ * ltd_stock δ B₀ I t = Y + I t * q) :
    C = Y - δ * ltd_stock δ B₀ I t +
      q * (ltd_stock δ B₀ I (t + 1) - (1 - δ) * ltd_stock δ B₀ I t) := by
  rw [ltd_stock]
  linarith [mul_comm (I t) q]

/-- The geometric sum `Σ_{j≥0} δ(1 − δ)^j a^{j+1} = δa/(1 − (1 − δ)a)`. -/
theorem ltd_hasSum_coupons {δ a : ℝ} (h0 : 0 ≤ (1 - δ) * a) (h1 : (1 - δ) * a < 1) :
    HasSum (fun j : ℕ => δ * (1 - δ) ^ j * a ^ (j + 1)) (δ * a / (1 - (1 - δ) * a)) := by
  have := (hasSum_geometric_of_lt_one h0 h1).mul_left (δ * a)
  convert this using 1
  · funext j; rw [mul_pow, pow_succ]; ring
  · rw [div_eq_mul_inv]

/-- **AKMM, p. 903**: at the risk-free rate `r` (with `0 < δ ≤ 1`, `0 < δ + r`, `r > −1`), the
present value of the payments `δ(1 − δ)^{j−1}`, `j ≥ 1`, of one bond is `δ/(δ + r)`; `B` bonds
are worth `δB/(δ + r)`. -/
theorem ltd_pv_bond {δ r : ℝ} (hδ1 : δ ≤ 1) (hr : -1 < r) (hδr : 0 < δ + r) (B : ℝ) :
    HasSum (fun j : ℕ => δ * (1 - δ) ^ j / (1 + r) ^ (j + 1) * B) (δ / (δ + r) * B) := by
  have hr1 : 0 < 1 + r := by linarith
  have h0 : 0 ≤ (1 - δ) * (1 + r)⁻¹ := mul_nonneg (by linarith) (inv_nonneg.2 hr1.le)
  have h1 : (1 - δ) * (1 + r)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hr1]; linarith
  have := (ltd_hasSum_coupons h0 h1).mul_right B
  convert this using 1
  · funext j; rw [div_eq_mul_inv, ← inv_pow]
  · congr 1
    have hne : δ + r ≠ 0 := hδr.ne'
    rw [show 1 - (1 - δ) * (1 + r)⁻¹ = (δ + r) / (1 + r) by field_simp; ring]
    field_simp

/-- AKMM, p. 903, timing: valued at `t`, the payments `δ(1 − δ)^j B_t` (`j ≥ 0`) of the stock
`B_t` are worth `δ(1 + r)B_t/(δ + r)`; without the current coupon they are worth
`δ(1 − δ)B_t/(δ + r)`. The book's `δB_t/(δ + r)` is their value one period earlier. -/
theorem ltd_pv_stock_timing {δ r : ℝ} (hδ1 : δ ≤ 1) (hr : -1 < r) (hδr : 0 < δ + r) (B : ℝ) :
    HasSum (fun j : ℕ => δ * (1 - δ) ^ j * B / (1 + r) ^ j) (δ * (1 + r) / (δ + r) * B) ∧
      HasSum (fun j : ℕ => δ * (1 - δ) ^ (j + 1) * B / (1 + r) ^ (j + 1))
        (δ * (1 - δ) / (δ + r) * B) := by
  have hr1 : 0 < 1 + r := by linarith
  have h := ltd_pv_bond hδ1 hr hδr B
  constructor
  · have := h.mul_left (1 + r)
    convert this using 1
    · funext j; rw [pow_succ]; field_simp
    · ring
  · have := h.mul_left (1 - δ)
    convert this using 1
    · funext j; rw [pow_succ]; field_simp
    · ring

/-- AKMM, p. 903: the yield `i` of a bond priced at `q` solves
`q = Σ_{j≥1} δ(1 − δ)^{j−1}/(1 + i)^j`, i.e. `q = δ/(δ + i)`. -/
theorem ltd_yield {δ i : ℝ} (hδ1 : δ ≤ 1) (hi : -1 < i) (hδi : 0 < δ + i) :
    HasSum (fun j : ℕ => δ * (1 - δ) ^ j / (1 + i) ^ (j + 1)) (δ / (δ + i)) := by
  simpa using ltd_pv_bond hδ1 hi hδi 1

/-- AKMM, p. 903: for `q > 0` the yield is `i = δ(1 − q)/q`. -/
theorem ltd_yield_iff {δ i q : ℝ} (hδi : 0 < δ + i) (hq : 0 < q) :
    q = δ / (δ + i) ↔ i = δ * (1 - q) / q := by
  constructor
  · intro h
    rw [h]
    rcases eq_or_ne δ 0 with hδ | hδ
    · rw [h, hδ] at hq; simp at hq
    · field_simp
      ring
  · intro h
    rw [h] at hδi ⊢
    have hq' : q ≠ 0 := hq.ne'
    have : δ + δ * (1 - q) / q = δ / q := by field_simp; ring
    rcases eq_or_ne δ 0 with hδ | hδ
    · rw [hδ] at hδi; simp at hδi
    · rw [this]; field_simp

/-- The coupon `x_t` of one bond issued at date `0`: `x_0 = 0` and `x_t = δ(1 − δ)^{t−1}`. -/
noncomputable def ltd_coupon (δ : ℝ) (t : ℕ) : ℝ := if t = 0 then 0 else δ * (1 - δ) ^ (t - 1)

/-- **AKMM, p. 902**: the Macaulay duration
`Σ_t t x_t/(1 + i)^t / Σ_t x_t/(1 + i)^t` of the bond is `(1 + i)/(δ + i)` (with
`0 < δ ≤ 1`, `i ≥ 0`). -/
theorem ltd_duration {δ i : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hi : 0 ≤ i) :
    (∑' t, t * ltd_coupon δ t / (1 + i) ^ t) / (∑' t, ltd_coupon δ t / (1 + i) ^ t) =
      (1 + i) / (δ + i) := by
  set a := (1 + i)⁻¹ with ha
  have hi1 : 0 < 1 + i := by linarith
  have ha0 : 0 < a := inv_pos.2 hi1
  set z := (1 - δ) * a with hz
  have hz0 : 0 ≤ z := mul_nonneg (by linarith) ha0.le
  have hz1 : z < 1 := by
    rw [hz, ha, ← div_eq_mul_inv, div_lt_one hi1]; linarith
  have h1z : 0 < 1 - z := by linarith
  -- the two series, shifted by one
  have hS0 : HasSum (fun t : ℕ => ltd_coupon δ t / (1 + i) ^ t) (δ * a / (1 - z)) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, ltd_coupon, ↓reduceIte, zero_div,
      sub_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false, Nat.add_sub_cancel]
    convert ltd_hasSum_coupons hz0 hz1 using 1
    funext j
    rw [div_eq_mul_inv, ← inv_pow]
  have hgeo := hasSum_geometric_of_lt_one hz0 hz1
  have hnz : HasSum (fun n : ℕ => (n : ℝ) * z ^ n) (z / (1 - z) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs, abs_of_nonneg hz0]; exact hz1)
  have hS1 : HasSum (fun t : ℕ => t * ltd_coupon δ t / (1 + i) ^ t)
      (δ * a / (1 - z) ^ 2) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, ltd_coupon, ↓reduceIte, mul_zero,
      zero_div, sub_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false, Nat.add_sub_cancel]
    have := (hnz.add hgeo).mul_left (δ * a)
    convert this using 1
    · funext j
      rw [div_eq_mul_inv, ← inv_pow, ← ha, hz, mul_pow, pow_succ]
      push_cast
      ring
    · field_simp
      ring
  rw [hS1.tsum_eq, hS0.tsum_eq]
  have hδa : 0 < δ * a := mul_pos hδ ha0
  rw [div_div_div_cancel_left' _ _ hδa.ne', pow_two, div_mul_cancel_right₀ h1z.ne']
  rw [hz, ha, show 1 - (1 - δ) * (1 + i)⁻¹ = (δ + i) / (1 + i) by field_simp; ring, inv_div]

/-- AKMM, p. 903: the annualised spread `r^s = ((1 + i)/(1 + r))^4 − 1`. -/
noncomputable def ltd_spread (i r : ℝ) : ℝ := ((1 + i) / (1 + r)) ^ 4 - 1

/-- The annualised spread is positive iff the bond yield exceeds the risk-free rate. -/
theorem ltd_spread_pos_iff {i r : ℝ} (hi : -1 < i) (hr : -1 < r) :
    0 < ltd_spread i r ↔ r < i := by
  have hr1 : 0 < 1 + r := by linarith
  have hx : 0 ≤ (1 + i) / (1 + r) := div_nonneg (by linarith) hr1.le
  rw [ltd_spread, sub_pos]
  constructor
  · intro h
    by_contra hle
    rw [not_lt] at hle
    have : (1 + i) / (1 + r) ≤ 1 := by rw [div_le_one hr1]; linarith
    have := pow_le_one₀ hx this (n := 4)
    linarith
  · intro h
    have : 1 < (1 + i) / (1 + r) := by rw [one_lt_div hr1]; linarith
    exact one_lt_pow₀ this (by norm_num)

/-- AKMM, (24.2), p. 731: the present-value haircut
`1 − Σ_t x_t^{post}/(1 + i)^t / Σ_t x_t^{pre}/(1 + i)^t`. -/
noncomputable def ltd_haircut (post pre : ℕ → ℝ) (i : ℝ) : ℝ :=
  1 - (∑' t, post (t + 1) / (1 + i) ^ (t + 1)) / (∑' t, pre (t + 1) / (1 + i) ^ (t + 1))

/-- AKMM, (24.2), p. 731: the haircut is the fraction of the pre-restructuring present value
lost, and lies in `[0, 1]` when the new obligations are worth between `0` and the old. -/
theorem eq_24_2 (post pre : ℕ → ℝ) (i : ℝ)
    (hpre : 0 < ∑' t, pre (t + 1) / (1 + i) ^ (t + 1))
    (hpost0 : 0 ≤ ∑' t, post (t + 1) / (1 + i) ^ (t + 1))
    (hle : ∑' t, post (t + 1) / (1 + i) ^ (t + 1) ≤ ∑' t, pre (t + 1) / (1 + i) ^ (t + 1)) :
    ltd_haircut post pre i = ((∑' t, pre (t + 1) / (1 + i) ^ (t + 1)) -
        ∑' t, post (t + 1) / (1 + i) ^ (t + 1)) / ∑' t, pre (t + 1) / (1 + i) ^ (t + 1) ∧
      0 ≤ ltd_haircut post pre i ∧ ltd_haircut post pre i ≤ 1 := by
  unfold ltd_haircut
  refine ⟨by field_simp, ?_, ?_⟩
  · rw [sub_nonneg, div_le_one hpre]; exact hle
  · have := div_nonneg hpost0 hpre.le
    linarith

end AKMM.SovereignDefault

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The bond price recursion (24.12), (24.A.2) and (24.A.6)

AKMM, §24.4.2, (24.12), p. 744; Appendix 24.A.1, (24.A.2), p. 897 and (24.A.6), p. 900;
§24.4.4, p. 748 (one-period debt).

On a finite debt grid `Bd` and a finite income grid `Y` with Markov matrix `P` (Sargent and
Stachurski's `IsMarkov`, imported), the zero-profit price of a long-term bond given the
lenders' expected next-period behaviour is the fixed point of
`(Tq)(m, y) = (1 + r)⁻¹ Σ_j P(y, j)[1 − D(m, j)][δ + (1 − δ) Σ_h q(h, j) B(h | m, j)]`
(24.A.6), with a default probability `D ∈ [0, 1]` and a distribution `B(· | m, j)` over next
debt choices. The deterministic rules of (24.12)/(24.A.2) are the special case `D ∈ {0, 1}`,
`B(h | m, j) = 1{h = B̂(m, j)}`.

* `T` is a contraction of modulus `(1 − δ)/(1 + r) < 1` in the sup norm (`bp_contracting`), so
  the price exists, is unique and is the limit of the iteration (24.A.2) from any initial guess
  (`eq_24_A_6`, `eq_24_A_2`, `eq_24_12`); it lies in `[0, δ/(δ + r)]`, the upper end being the
  risk-free price, attained when the sovereign never defaults (`bp_riskfree`).
* **One-period debt** (`δ = 1`, p. 748): `q(m, y) = (1 + r)⁻¹ Σ_j P(y, j)[1 − D(m, j)]` depends
  only on the next-period default rule, not on the borrowing rule (`bp_one_period`,
  `bp_one_period_independent`); with long-term debt (`0 < δ < 1`) the borrowing rule of the
  next government changes today's price (`bp_long_term_depends_on_borrowing`), the source of
  the second time-inconsistency problem.

Departure: the book states (24.12) with a continuous income distribution `F(dY′ | Y)` and a
continuous debt choice; here both are on finite grids, the setting of Appendix 24.A.1.
-/

namespace AKMM.SovereignDefault

open Finset SargentStachurski.RecursiveDecisionProcesses

variable {Bd Y : Type*} [Fintype Bd] [Fintype Y]

/-- AKMM, (24.A.6), p. 900: the price operator with default probabilities `Dp` and borrowing
probabilities `Bp`. -/
noncomputable def bp_op (P : Matrix Y Y ℝ) (r δ : ℝ) (Dp : Bd → Y → ℝ) (Bp : Bd → Y → Bd → ℝ)
    (q : Bd → Y → ℝ) : Bd → Y → ℝ :=
  fun m y => (1 + r)⁻¹ * ∑ j, P y j * ((1 - Dp m j) * (δ + (1 - δ) * ∑ h, q h j * Bp m j h))

variable (P : Matrix Y Y ℝ) (r δ : ℝ) (Dp : Bd → Y → ℝ) (Bp : Bd → Y → Bd → ℝ) in
/-- The admissibility conditions of (24.A.6): `P` Markov, `D ∈ [0, 1]`, `B(· | m, j)` a
probability distribution, `δ ∈ [0, 1]`, `r > −1` and `δ + r > 0`. -/
structure BPAdmissible : Prop where
  markov : IsMarkov P
  D_nonneg : ∀ m j, 0 ≤ Dp m j
  D_le_one : ∀ m j, Dp m j ≤ 1
  B_nonneg : ∀ m j h, 0 ≤ Bp m j h
  B_sum : ∀ m j, ∑ h, Bp m j h = 1
  δ_nonneg : 0 ≤ δ
  δ_le_one : δ ≤ 1
  r_gt : -1 < r
  δr_pos : 0 < δ + r

/-- A concrete admissible specification: no default and staying at the current debt level,
for any Markov `P`, `δ ∈ [0, 1]`, `r > 0`. -/
theorem bp_admissible_example [DecidableEq Bd] {P : Matrix Y Y ℝ} (hP : IsMarkov P) {r δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hr : 0 < r) :
    BPAdmissible P r δ (fun _ _ => 0) (fun (m : Bd) (_ : Y) (h : Bd) => if m = h then 1 else 0)
    where
  markov := hP
  D_nonneg := fun _ _ => le_rfl
  D_le_one := fun _ _ => zero_le_one
  B_nonneg := fun _ _ _ => by split_ifs <;> norm_num
  B_sum := fun m _ => by simp
  δ_nonneg := hδ0
  δ_le_one := hδ1
  r_gt := by linarith
  δr_pos := by linarith

/-- The pointwise contraction estimate:
`|(Tq)(m, y) − (Tq′)(m, y)| ≤ (1 − δ)/(1 + r) ‖q − q′‖`. -/
theorem bp_op_sub_le {P : Matrix Y Y ℝ} {r δ : ℝ} {Dp : Bd → Y → ℝ} {Bp : Bd → Y → Bd → ℝ}
    (hA : BPAdmissible P r δ Dp Bp) (q q' : Bd → Y → ℝ) (m : Bd) (y : Y) :
    |bp_op P r δ Dp Bp q m y - bp_op P r δ Dp Bp q' m y| ≤ (1 - δ) / (1 + r) * ‖q - q'‖ := by
  have hr1 : 0 < 1 + r := by linarith [hA.r_gt]
  have hδ' : 0 ≤ 1 - δ := by linarith [hA.δ_le_one]
  have hcomp : ∀ h j, |q h j - q' h j| ≤ ‖q - q'‖ := fun h j => by
    have h1 := norm_le_pi_norm ((q - q') h) j
    have h2 := norm_le_pi_norm (q - q') h
    rw [Real.norm_eq_abs] at h1
    exact h1.trans h2
  have hinner : ∀ j, |∑ h, q h j * Bp m j h - ∑ h, q' h j * Bp m j h| ≤ ‖q - q'‖ := by
    intro j
    rw [← sum_sub_distrib]
    calc |∑ h, (q h j * Bp m j h - q' h j * Bp m j h)|
        ≤ ∑ h, |q h j * Bp m j h - q' h j * Bp m j h| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ h, ‖q - q'‖ * Bp m j h := sum_le_sum fun h _ => by
          rw [← sub_mul, abs_mul, abs_of_nonneg (hA.B_nonneg m j h)]
          exact mul_le_mul_of_nonneg_right (hcomp h j) (hA.B_nonneg m j h)
      _ = ‖q - q'‖ := by rw [← mul_sum, hA.B_sum, mul_one]
  have hdiff : bp_op P r δ Dp Bp q m y - bp_op P r δ Dp Bp q' m y =
      (1 + r)⁻¹ * ∑ j, P y j * ((1 - Dp m j) * ((1 - δ) *
        (∑ h, q h j * Bp m j h - ∑ h, q' h j * Bp m j h))) := by
    unfold bp_op
    rw [← mul_sub, ← sum_sub_distrib]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    ring
  rw [hdiff, abs_mul, abs_of_pos (inv_pos.2 hr1), div_eq_inv_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hr1.le)
  calc |∑ j, P y j * ((1 - Dp m j) * ((1 - δ) *
        (∑ h, q h j * Bp m j h - ∑ h, q' h j * Bp m j h)))|
      ≤ ∑ j, |P y j * ((1 - Dp m j) * ((1 - δ) *
        (∑ h, q h j * Bp m j h - ∑ h, q' h j * Bp m j h)))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, P y j * ((1 - δ) * ‖q - q'‖) := sum_le_sum fun j _ => by
        have hD0 : 0 ≤ 1 - Dp m j := by linarith [hA.D_le_one m j]
        have hD1 : 1 - Dp m j ≤ 1 := by linarith [hA.D_nonneg m j]
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (hA.markov.nonneg y j), abs_of_nonneg hD0,
          abs_of_nonneg hδ']
        refine mul_le_mul_of_nonneg_left ?_ (hA.markov.nonneg y j)
        calc (1 - Dp m j) * ((1 - δ) * |∑ h, q h j * Bp m j h - ∑ h, q' h j * Bp m j h|)
            ≤ 1 * ((1 - δ) * ‖q - q'‖) := mul_le_mul hD1
              (mul_le_mul_of_nonneg_left (hinner j) hδ')
              (mul_nonneg hδ' (abs_nonneg _)) zero_le_one
          _ = (1 - δ) * ‖q - q'‖ := one_mul _
    _ = (1 - δ) * ‖q - q'‖ := by rw [← sum_mul, hA.markov.rowsum, one_mul]

/-- AKMM, (24.12), (24.A.2), (24.A.6): the price operator is a contraction of modulus
`(1 − δ)/(1 + r) < 1` in the sup norm. -/
theorem bp_contracting {P : Matrix Y Y ℝ} {r δ : ℝ} {Dp : Bd → Y → ℝ} {Bp : Bd → Y → Bd → ℝ}
    (hA : BPAdmissible P r δ Dp Bp) :
    ContractingWith (Real.toNNReal ((1 - δ) / (1 + r))) (bp_op P r δ Dp Bp) := by
  have hr1 : 0 < 1 + r := by linarith [hA.r_gt]
  have hk0 : 0 ≤ (1 - δ) / (1 + r) := div_nonneg (by linarith [hA.δ_le_one]) hr1.le
  refine ⟨?_, LipschitzWith.of_dist_le_mul fun q q' => ?_⟩
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hk0, NNReal.coe_one, div_lt_one hr1]
    linarith [hA.δr_pos]
  · rw [Real.coe_toNNReal _ hk0, dist_eq_norm, dist_eq_norm]
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hk0 (norm_nonneg _))).2 fun m => ?_
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hk0 (norm_nonneg _))).2 fun y => ?_
    rw [Pi.sub_apply, Pi.sub_apply, Real.norm_eq_abs]
    exact bp_op_sub_le hA q q' m y

/-- The set of prices in `[0, δ/(δ + r)]` is mapped into itself. -/
theorem bp_op_mapsTo {P : Matrix Y Y ℝ} {r δ : ℝ} {Dp : Bd → Y → ℝ} {Bp : Bd → Y → Bd → ℝ}
    (hA : BPAdmissible P r δ Dp Bp) (q : Bd → Y → ℝ)
    (hq : ∀ m y, 0 ≤ q m y ∧ q m y ≤ δ / (δ + r)) (m : Bd) (y : Y) :
    0 ≤ bp_op P r δ Dp Bp q m y ∧ bp_op P r δ Dp Bp q m y ≤ δ / (δ + r) := by
  have hr1 : 0 < 1 + r := by linarith [hA.r_gt]
  have hδ' : 0 ≤ 1 - δ := by linarith [hA.δ_le_one]
  have hM : 0 ≤ δ / (δ + r) := div_nonneg hA.δ_nonneg hA.δr_pos.le
  have hin : ∀ j, 0 ≤ ∑ h, q h j * Bp m j h ∧ ∑ h, q h j * Bp m j h ≤ δ / (δ + r) := by
    intro j
    refine ⟨sum_nonneg fun h _ => mul_nonneg (hq h j).1 (hA.B_nonneg m j h), ?_⟩
    calc ∑ h, q h j * Bp m j h ≤ ∑ h, δ / (δ + r) * Bp m j h :=
          sum_le_sum fun h _ => mul_le_mul_of_nonneg_right (hq h j).2 (hA.B_nonneg m j h)
      _ = δ / (δ + r) := by rw [← mul_sum, hA.B_sum, mul_one]
  have hterm : ∀ j, 0 ≤ (1 - Dp m j) * (δ + (1 - δ) * ∑ h, q h j * Bp m j h) ∧
      (1 - Dp m j) * (δ + (1 - δ) * ∑ h, q h j * Bp m j h) ≤ δ + (1 - δ) * (δ / (δ + r)) := by
    intro j
    have hD0 : 0 ≤ 1 - Dp m j := by linarith [hA.D_le_one m j]
    have hD1 : 1 - Dp m j ≤ 1 := by linarith [hA.D_nonneg m j]
    have hX0 : 0 ≤ δ + (1 - δ) * ∑ h, q h j * Bp m j h :=
      add_nonneg hA.δ_nonneg (mul_nonneg hδ' (hin j).1)
    refine ⟨mul_nonneg hD0 hX0, ?_⟩
    calc (1 - Dp m j) * (δ + (1 - δ) * ∑ h, q h j * Bp m j h)
        ≤ 1 * (δ + (1 - δ) * ∑ h, q h j * Bp m j h) := mul_le_mul_of_nonneg_right hD1 hX0
      _ ≤ δ + (1 - δ) * (δ / (δ + r)) := by
          rw [one_mul]; linarith [mul_le_mul_of_nonneg_left (hin j).2 hδ']
  unfold bp_op
  refine ⟨mul_nonneg (inv_nonneg.2 hr1.le)
    (sum_nonneg fun j _ => mul_nonneg (hA.markov.nonneg y j) (hterm j).1), ?_⟩
  calc (1 + r)⁻¹ * ∑ j, P y j * ((1 - Dp m j) * (δ + (1 - δ) * ∑ h, q h j * Bp m j h))
      ≤ (1 + r)⁻¹ * ∑ j, P y j * (δ + (1 - δ) * (δ / (δ + r))) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hterm j).2 (hA.markov.nonneg y j)) (inv_nonneg.2 hr1.le)
    _ = δ / (δ + r) := by
        rw [← sum_mul, hA.markov.rowsum, one_mul]
        have : δ + r ≠ 0 := hA.δr_pos.ne'
        field_simp
        ring

/-- **AKMM, (24.A.6)**, p. 900: with default probabilities and borrowing probabilities, the
equilibrium bond price exists and is unique, and lies in `[0, δ/(δ + r)]`. -/
theorem eq_24_A_6 {P : Matrix Y Y ℝ} {r δ : ℝ} {Dp : Bd → Y → ℝ} {Bp : Bd → Y → Bd → ℝ}
    (hA : BPAdmissible P r δ Dp Bp) :
    ∃! q : Bd → Y → ℝ, Function.IsFixedPt (bp_op P r δ Dp Bp) q ∧
      ∀ m y, 0 ≤ q m y ∧ q m y ≤ δ / (δ + r) := by
  have hc := bp_contracting hA
  set S : Set (Bd → Y → ℝ) :=
    ⋂ m, ⋂ y, {q | 0 ≤ q m y ∧ q m y ≤ δ / (δ + r)} with hSdef
  have hSm : ∀ q, q ∈ S ↔ ∀ m y, 0 ≤ q m y ∧ q m y ≤ δ / (δ + r) := fun q => by
    simp only [hSdef, Set.mem_iInter, Set.mem_ofPred_eq]
  have hS : IsClosed S := by
    refine isClosed_iInter fun m => isClosed_iInter fun y => ?_
    have hc : Continuous fun q : Bd → Y → ℝ => q m y := by fun_prop
    exact (isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)
  have h0 : (fun _ _ => (0 : ℝ)) ∈ S := (hSm _).2 fun _ _ =>
    ⟨le_rfl, div_nonneg hA.δ_nonneg hA.δr_pos.le⟩
  have hit : ∀ n, (bp_op P r δ Dp Bp)^[n] (fun _ _ => 0) ∈ S := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (hSm _).2 fun m y => bp_op_mapsTo hA _ ((hSm _).1 ih) m y
  have hmem := hS.mem_of_tendsto (hc.tendsto_iterate_fixedPoint (fun _ _ => 0))
    (Filter.Eventually.of_forall hit)
  exact ⟨_, ⟨hc.fixedPoint_isFixedPt, (hSm _).1 hmem⟩, fun q hq => hc.fixedPoint_unique hq.1⟩

/-- **AKMM, (24.A.2)**, pp. 897–898: the price iteration `q_{I+1} = T q_I` converges from any
initial guess to the unique equilibrium price (for fixed default and borrowing rules). -/
theorem eq_24_A_2 {P : Matrix Y Y ℝ} {r δ : ℝ} {Dp : Bd → Y → ℝ} {Bp : Bd → Y → Bd → ℝ}
    (hA : BPAdmissible P r δ Dp Bp) (q₀ q : Bd → Y → ℝ)
    (hq : Function.IsFixedPt (bp_op P r δ Dp Bp) q) :
    Filter.Tendsto (fun n => (bp_op P r δ Dp Bp)^[n] q₀) Filter.atTop (nhds q) := by
  have hc := bp_contracting hA
  rw [hc.fixedPoint_unique hq]
  exact hc.tendsto_iterate_fixedPoint q₀

/-- AKMM, (24.12), p. 744: the price operator with deterministic rules `D̂` and `B̂`. -/
noncomputable def bp_op12 (P : Matrix Y Y ℝ) (r δ : ℝ) (D : Bd → Y → ℝ) (Bh : Bd → Y → Bd)
    (q : Bd → Y → ℝ) : Bd → Y → ℝ :=
  fun m y => (1 + r)⁻¹ * ∑ j, P y j * ((1 - D m j) * (δ + (1 - δ) * q (Bh m j) j))

/-- Deterministic rules are degenerate probabilities: (24.12) is (24.A.6) with
`B(h | m, j) = 1{h = B̂(m, j)}`. -/
theorem bp_op12_eq [DecidableEq Bd] (P : Matrix Y Y ℝ) (r δ : ℝ) (D : Bd → Y → ℝ)
    (Bh : Bd → Y → Bd) :
    bp_op12 P r δ D Bh = bp_op P r δ D (fun m j h => if Bh m j = h then 1 else 0) := by
  funext q m y
  unfold bp_op12 bp_op
  congr 1
  refine sum_congr rfl fun j _ => ?_
  simp [mul_ite, mul_one, mul_zero, sum_ite_eq]

omit [Fintype Bd] in
/-- **AKMM, (24.12)**, p. 744: given a default rule `D̂ ∈ {0, 1}` and a borrowing rule `B̂`, the
bond price function exists, is unique and lies in `[0, δ/(δ + r)]` (with `P` Markov,
`δ ∈ [0, 1]`, `r > −1`, `δ + r > 0`). -/
theorem eq_24_12 [Finite Bd] {P : Matrix Y Y ℝ} (hP : IsMarkov P) {r δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hr : -1 < r) (hδr : 0 < δ + r) (D : Bd → Y → ℝ)
    (hD : ∀ m j, D m j = 0 ∨ D m j = 1) (Bh : Bd → Y → Bd) :
    ∃! q : Bd → Y → ℝ, (∀ m y, q m y =
        (1 + r)⁻¹ * ∑ j, P y j * ((1 - D m j) * (δ + (1 - δ) * q (Bh m j) j))) ∧
      ∀ m y, 0 ≤ q m y ∧ q m y ≤ δ / (δ + r) := by
  classical
  let _ := Fintype.ofFinite Bd
  have hA : BPAdmissible P r δ D (fun m j h => if Bh m j = h then 1 else 0) :=
    { markov := hP
      D_nonneg := fun m j => by rcases hD m j with h | h <;> simp [h]
      D_le_one := fun m j => by rcases hD m j with h | h <;> simp [h]
      B_nonneg := fun _ _ _ => by split_ifs <;> norm_num
      B_sum := fun m j => by simp
      δ_nonneg := hδ0
      δ_le_one := hδ1
      r_gt := hr
      δr_pos := hδr }
  have he := eq_24_A_6 hA
  rw [← bp_op12_eq] at he
  have hiff : ∀ q : Bd → Y → ℝ, Function.IsFixedPt (bp_op12 P r δ D Bh) q ↔ ∀ m y, q m y =
      (1 + r)⁻¹ * ∑ j, P y j * ((1 - D m j) * (δ + (1 - δ) * q (Bh m j) j)) := fun q => by
    constructor
    · intro h m y
      exact (congrFun (congrFun h m) y).symm
    · intro h
      funext m y
      exact (h m y).symm
  simpa only [hiff] using he

/-- AKMM, p. 903: without default the bond sells at the risk-free price `δ/(δ + r)`. -/
theorem bp_riskfree {P : Matrix Y Y ℝ} (hP : IsMarkov P) {r : ℝ} (δ : ℝ) (hr : -1 < r)
    (hδr : 0 < δ + r) (Bp : Bd → Y → Bd → ℝ) (hBs : ∀ m j, ∑ h, Bp m j h = 1) :
    Function.IsFixedPt (bp_op P r δ (fun _ _ => 0) Bp) (fun _ _ => δ / (δ + r)) := by
  funext m y
  unfold bp_op
  have hr1 : 1 + r ≠ 0 := by linarith
  have hδr' : δ + r ≠ 0 := hδr.ne'
  simp only [sub_zero, one_mul, ← mul_sum, hBs, mul_one, ← sum_mul, hP.rowsum, one_mul]
  field_simp
  ring

omit [Fintype Bd] in
/-- **AKMM, p. 748: one-period debt.** With `δ = 1` the price operator does not depend on the
continuation price or the borrowing rule: `(Tq)(m, y) = (1 + r)⁻¹ Σ_j P(y, j)[1 − D̂(m, j)]`;
the period-`t` price depends only on the period-`t+1` default rule. -/
theorem bp_one_period (P : Matrix Y Y ℝ) (r : ℝ) (D : Bd → Y → ℝ) (Bh : Bd → Y → Bd)
    (q : Bd → Y → ℝ) (m : Bd) (y : Y) :
    bp_op12 P r 1 D Bh q m y = (1 + r)⁻¹ * ∑ j, P y j * (1 - D m j) := by
  unfold bp_op12
  simp only [sub_self, zero_mul, add_zero, mul_one]

omit [Fintype Bd] in
/-- AKMM, p. 748: with one-period debt two borrowing rules lead to the same equilibrium
price: the second time-inconsistency problem does not arise. -/
theorem bp_one_period_independent (P : Matrix Y Y ℝ) (r : ℝ) (D : Bd → Y → ℝ)
    (Bh Bh' : Bd → Y → Bd) (q q' : Bd → Y → ℝ)
    (hq : Function.IsFixedPt (bp_op12 P r 1 D Bh) q)
    (hq' : Function.IsFixedPt (bp_op12 P r 1 D Bh') q') : q = q' := by
  funext m y
  rw [← hq, ← hq']
  simp only [bp_one_period]

/-- AKMM, p. 748: **with long-term debt the next government's borrowing changes today's
price.** One income state, two debt levels (`false` low, `true` high); the sovereign repays at
low debt and defaults at high debt. If the next government stays at low debt the low-debt bond
sells at the risk-free `δ/(δ + r)`; if it moves to high debt (and then defaults) it sells at
`δ/(1 + r)`, which is strictly lower for `0 < δ < 1`. -/
theorem bp_long_term_depends_on_borrowing {r δ : ℝ} (hr : 0 ≤ r) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    let P : Matrix Unit Unit ℝ := fun _ _ => 1
    let D : Bool → Unit → ℝ := fun b _ => if b then 1 else 0
    Function.IsFixedPt (bp_op12 P r δ D (fun _ _ => false))
        (fun b _ => if b then 0 else δ / (δ + r)) ∧
      Function.IsFixedPt (bp_op12 P r δ D (fun _ _ => true))
        (fun b _ => if b then 0 else δ / (1 + r)) ∧
      δ / (1 + r) < δ / (δ + r) := by
  intro P D
  have hr1 : 0 < 1 + r := by linarith
  have hδr : 0 < δ + r := by linarith
  refine ⟨?_, ?_, div_lt_div_of_pos_left hδ0 hδr (by linarith)⟩
  · funext b u
    cases b <;> simp only [bp_op12, P, D, Finset.univ_unique, Finset.sum_singleton, one_mul,
      Bool.false_eq_true, ↓reduceIte, sub_zero, sub_self, zero_mul, mul_zero]
    field_simp
    ring
  · funext b u
    cases b <;> simp only [bp_op12, P, D, Finset.univ_unique, Finset.sum_singleton, one_mul,
      Bool.false_eq_true, ↓reduceIte, sub_zero, sub_self, zero_mul, mul_zero, add_zero]
    field_simp

end AKMM.SovereignDefault

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The sovereign's Bellman equations (24.9)–(24.11)

AKMM, §24.4.2, (24.9)–(24.11), pp. 743–744, and Appendix 24.A.1, (24.A.1), p. 897; Appendix
24.A.3, p. 904 (default regions).

For a given bond price function `q`, the sovereign's problem on a finite income grid (Markov
matrix `P`) and a finite debt grid (debt values `bond`, a zero-debt point `b₀`) is a recursive
decision process in the sense of Sargent and Stachurski (`RDP`, imported): states
`(y, b, excluded)`, actions `(b′, default)`. In good standing the sovereign either repays and
picks `b′`, with consumption `Y − δB + q(B′, Y)[B′ − (1 − δ)B]`, or defaults; while excluded
it consumes `Y − φ(Y)` and regains access with zero debt with probability `ψ`.

* The RDP satisfies Blackwell's conditions with modulus `β`, so its Bellman operator is a
  contraction (`sd_isContracting`); value function iteration (24.A.1) converges from any initial
  guess (`eq_24_A_1`).
* Its Bellman operator is (24.9) in good standing and (24.10) in exclusion (`sd_T_good`,
  `sd_T_excluded`); hence **(24.9)–(24.11) have exactly one solution `(V, V^D)`** with `V^R`
  given by (24.11) (`eq_24_9_to_24_11`).
* `V^R` is nonincreasing in debt for every continuation `V` (`sd_VR_antitone`), `V^D` does not
  depend on debt, so `V` is nonincreasing in debt (`sd_V_antitone`) and the default set
  `{Y : V^D(Y) > V^R(B, Y)}` grows with debt (`sd_default_set_mono`).

Sargent and Stachurski's own optimal-default RDP (Exercise 8.2.7) has one-period debt and a
constant price, so it is not reused; we build the book's RDP from their `RDP` structure and use
their Blackwell, contraction and global-stability theorems. Departure D4: finite grids.
-/

namespace AKMM.SovereignDefault

open Finset SargentStachurski.RecursiveDecisionProcesses

/-- The primitives of the quantitative model (§24.4.1, p. 742–743) on finite grids: income
levels `inc` with Markov matrix `P`, debt levels `bond` with a zero-debt point `b₀`, utility
`u`, default cost `φ(Y)`, discount factor `β ∈ [0, 1)`, re-entry probability `ψ ∈ [0, 1]` and
coupon decay `δ ∈ [0, 1]`. -/
structure SDModel (Y Bd : Type*) [Fintype Y] [Fintype Bd] where
  /-- Income levels. -/
  inc : Y → ℝ
  /-- The income transition matrix. -/
  P : Matrix Y Y ℝ
  /-- `P` is a Markov matrix. -/
  markov : IsMarkov P
  /-- Debt levels on the grid. -/
  bond : Bd → ℝ
  /-- The zero-debt grid point. -/
  b₀ : Bd
  /-- `B(b₀) = 0`. -/
  bond_b₀ : bond b₀ = 0
  /-- Utility. -/
  u : ℝ → ℝ
  /-- The income cost of default. -/
  φ : ℝ → ℝ
  /-- The discount factor. -/
  β : ℝ
  /-- `β ≥ 0`. -/
  β_nonneg : 0 ≤ β
  /-- `β < 1`. -/
  β_lt_one : β < 1
  /-- The re-entry probability. -/
  ψ : ℝ
  /-- `ψ ≥ 0`. -/
  ψ_nonneg : 0 ≤ ψ
  /-- `ψ ≤ 1`. -/
  ψ_le_one : ψ ≤ 1
  /-- The coupon decay rate. -/
  δ : ℝ
  /-- `δ ≥ 0`. -/
  δ_nonneg : 0 ≤ δ
  /-- `δ ≤ 1`. -/
  δ_le_one : δ ≤ 1

variable {Y Bd : Type*} [Fintype Y] [Fintype Bd]

namespace SDModel

variable (M : SDModel Y Bd)

/-- AKMM, (24.11), p. 744: consumption under repayment,
`C = Y − δB + q(B′, Y)[B′ − (1 − δ)B]`. -/
def cons (q : Bd → Y → ℝ) (y : Y) (b b' : Bd) : ℝ :=
  M.inc y - M.δ * M.bond b + q b' y * (M.bond b' - (1 - M.δ) * M.bond b)

/-- AKMM, (24.10), p. 744: the right-hand side of the default value,
`u(Y − φ(Y)) + βE[ψV(0, Y′) + (1 − ψ)V^D(Y′)]`, given `V` and `V^D`. -/
def defaultValue (V : Bd → Y → ℝ) (VD : Y → ℝ) (y : Y) : ℝ :=
  M.u (M.inc y - M.φ (M.inc y)) + M.β * ∑ j, M.P y j * (M.ψ * V M.b₀ j + (1 - M.ψ) * VD j)

/-- AKMM, (24.11), p. 744: the value of repaying,
`V^R(B, Y) = max_{B′} {u(C) + βE V(B′, Y′)}`, given the continuation value `V`. -/
noncomputable def repayValue (q : Bd → Y → ℝ) (V : Bd → Y → ℝ) (b : Bd) (y : Y) : ℝ :=
  univ.sup' ⟨M.b₀, mem_univ _⟩ fun b' => M.u (M.cons q y b b') + M.β * ∑ j, M.P y j * V b' j

/-- The sovereign's RDP for a given price `q`: states `(y, b, excluded)`, actions
`(b′, default)`. -/
noncomputable def rdp (q : Bd → Y → ℝ) : RDP (Y × Bd × Bool) (Bd × Bool) where
  Γ := fun s => bif s.2.2 then {(M.b₀, true)} else univ
  Γ_nonempty := fun s => ⟨(M.b₀, true), by rcases s with ⟨_, _, d⟩; cases d <;> simp⟩
  V := Set.univ
  B := fun s a v => bif a.2 then
      M.defaultValue (fun b j => v (j, b, false)) (fun j => v (j, M.b₀, true)) s.1
    else M.u (M.cons q s.1 s.2.1 a.1) + M.β * ∑ j, M.P s.1 j * v (j, a.1, false)
  mono := fun s a _ v _ w _ hvw => by
    rcases a with ⟨b', d⟩
    cases d
    · refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hvw _) (M.markov.nonneg _ _)) M.β_nonneg)
    · refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (M.markov.nonneg _ _)) M.β_nonneg)
      · exact mul_le_mul_of_nonneg_left (hvw _) M.ψ_nonneg
      · exact mul_le_mul_of_nonneg_left (hvw _) (by linarith [M.ψ_le_one])
  consistent := fun _ _ _ _ => Set.mem_univ _

/-- The sovereign's RDP satisfies Blackwell's conditions with modulus `β`, so it is
contracting (Sargent–Stachurski, Exercise 8.2.3). -/
theorem sd_isContracting (q : Bd → Y → ℝ) : (M.rdp q).IsContracting M.β := by
  refine RDP.SatisfiesBlackwell.isContracting ⟨M.β_nonneg, M.β_lt_one,
    fun _ _ _ _ => Set.mem_univ _, fun s a _ v _ c _ => le_of_eq ?_⟩
  have hs : ∀ (f : Y → ℝ), ∑ j, M.P s.1 j * (f j + c) = ∑ j, M.P s.1 j * f j + c := fun f => by
    simp only [mul_add, sum_add_distrib, ← sum_mul, M.markov.rowsum, one_mul]
  rcases a with ⟨b', d⟩
  cases d
  · change M.u _ + M.β * ∑ j, M.P s.1 j * (v (j, b', false) + c) =
      M.u _ + M.β * ∑ j, M.P s.1 j * v (j, b', false) + M.β * c
    rw [hs]
    ring
  · change M.u _ + M.β * ∑ j, M.P s.1 j * (M.ψ * (v (j, M.b₀, false) + c) +
        (1 - M.ψ) * (v (j, M.b₀, true) + c)) =
      M.u _ + M.β * ∑ j, M.P s.1 j * (M.ψ * v (j, M.b₀, false) +
        (1 - M.ψ) * v (j, M.b₀, true)) + M.β * c
    have : ∀ j, M.ψ * (v (j, M.b₀, false) + c) + (1 - M.ψ) * (v (j, M.b₀, true) + c) =
        (M.ψ * v (j, M.b₀, false) + (1 - M.ψ) * v (j, M.b₀, true)) + c := fun j => by ring
    simp only [this]
    rw [hs]
    ring

/-- The Bellman operator in good standing is (24.9):
`(Tv)(y, b, 0) = max{V^D(y), V^R(b, y)}`. -/
theorem sd_T_good (q : Bd → Y → ℝ) (v : Y × Bd × Bool → ℝ) (y : Y) (b : Bd) :
    (M.rdp q).T v (y, b, false) = max
      (M.defaultValue (fun b j => v (j, b, false)) (fun j => v (j, M.b₀, true)) y)
      (M.repayValue q (fun b j => v (j, b, false)) b y) := by
  change univ.sup' _ (fun a : Bd × Bool => bif a.2 then
      M.defaultValue (fun b j => v (j, b, false)) (fun j => v (j, M.b₀, true)) y
    else M.u (M.cons q y b a.1) + M.β * ∑ j, M.P y j * v (j, a.1, false)) = _
  apply le_antisymm
  · refine sup'_le _ _ fun a _ => ?_
    rcases a with ⟨b', d⟩
    cases d
    · exact (le_sup' (fun b' => M.u (M.cons q y b b') + M.β * ∑ j, M.P y j * v (j, b', false))
        (mem_univ b')).trans (le_max_right _ _)
    · exact le_max_left _ _
  · refine max_le (le_sup'_of_le _ (mem_univ (M.b₀, true)) le_rfl) ?_
    exact sup'_le _ _ fun b' _ => le_sup'_of_le _ (mem_univ (b', false)) le_rfl

/-- The Bellman operator in exclusion is (24.10): `(Tv)(y, b, 1) = V^D(y)`. -/
theorem sd_T_excluded (q : Bd → Y → ℝ) (v : Y × Bd × Bool → ℝ) (y : Y) (b : Bd) :
    (M.rdp q).T v (y, b, true) =
      M.defaultValue (fun b j => v (j, b, false)) (fun j => v (j, M.b₀, true)) y := by
  change ({(M.b₀, true)} : Finset (Bd × Bool)).sup' _ _ = _
  rw [sup'_singleton]
  rfl

/-- **AKMM, (24.A.1)**, p. 897: for a given price, value function iteration converges from any
initial guess to the unique fixed point of the Bellman operator (global stability). -/
theorem eq_24_A_1 (q : Bd → Y → ℝ) : GloballyStable (M.rdp q).T :=
  ((M.sd_isContracting q).isContractionOn_T).globallyStable_univ

/-- **AKMM, (24.9)–(24.11)**, pp. 743–744: for any bond price function `q`, there is exactly one
pair `(V, V^D)` such that `V(B, Y) = max{V^D(Y), V^R(B, Y)}` (24.9) and
`V^D(Y) = u(Y − φ(Y)) + βE[ψV(0, Y′) + (1 − ψ)V^D(Y′)]` (24.10), where
`V^R(B, Y) = max_{B′} {u(C) + βE V(B′, Y′)}` (24.11). -/
theorem eq_24_9_to_24_11 (q : Bd → Y → ℝ) :
    ∃! W : (Bd → Y → ℝ) × (Y → ℝ),
      (∀ b y, W.1 b y = max (W.2 y) (M.repayValue q W.1 b y)) ∧
        ∀ y, W.2 y = M.defaultValue W.1 W.2 y := by
  obtain ⟨v, hv, huniq, -⟩ := M.eq_24_A_1 q
  have hgood : ∀ y b, v (y, b, false) = max
      (M.defaultValue (fun b j => v (j, b, false)) (fun j => v (j, M.b₀, true)) y)
      (M.repayValue q (fun b j => v (j, b, false)) b y) := fun y b => by
    rw [← M.sd_T_good q v y b, hv.eq]
  have hexc : ∀ y b, v (y, b, true) =
      M.defaultValue (fun b j => v (j, b, false)) (fun j => v (j, M.b₀, true)) y := fun y b => by
    rw [← M.sd_T_excluded q v y b, hv.eq]
  refine ⟨((fun b y => v (y, b, false)), (fun y => v (y, M.b₀, true))), ⟨fun b y => ?_,
    fun y => hexc y M.b₀⟩, ?_⟩
  · simp only
    rw [hgood y b, ← hexc y M.b₀]
  · rintro ⟨V, VD⟩ ⟨h9, h10⟩
    set w : Y × Bd × Bool → ℝ := fun s => bif s.2.2 then VD s.1 else V s.2.1 s.1 with hw
    have hfix : Function.IsFixedPt (M.rdp q).T w := by
      funext s
      rcases s with ⟨y, b, d⟩
      cases d
      · rw [M.sd_T_good]
        change max (M.defaultValue V VD y) (M.repayValue q V b y) = V b y
        rw [← h10 y]
        exact (h9 b y).symm
      · rw [M.sd_T_excluded]
        change M.defaultValue V VD y = VD y
        exact (h10 y).symm
    have hwv := huniq w hfix
    have h1 : V = fun b y => v (y, b, false) := by
      funext b y; exact congrFun hwv (y, b, false)
    have h2 : VD = fun y => v (y, M.b₀, true) := by
      funext y; exact congrFun hwv (y, M.b₀, true)
    rw [h1, h2]

/-- AKMM, p. 745 and App. 24.A.3: **`V^R` is nonincreasing in debt.** For any continuation `V`,
if `u` is nondecreasing and `q ≥ 0`, more debt lowers the value of repaying:
`B(b) ≤ B(b′) ⇒ V^R(b′, Y) ≤ V^R(b, Y)`. -/
theorem sd_VR_antitone (hu : Monotone M.u) {q : Bd → Y → ℝ} (hq : ∀ b y, 0 ≤ q b y)
    (V : Bd → Y → ℝ) {b b' : Bd} (hbb : M.bond b ≤ M.bond b') (y : Y) :
    M.repayValue q V b' y ≤ M.repayValue q V b y := by
  refine sup'_le _ _ fun c _ => le_sup'_of_le _ (mem_univ c) ?_
  refine add_le_add (hu ?_) le_rfl
  unfold cons
  have hk : 0 ≤ M.δ + q c y * (1 - M.δ) :=
    add_nonneg M.δ_nonneg (mul_nonneg (hq c y) (by linarith [M.δ_le_one]))
  nlinarith [mul_le_mul_of_nonneg_left hbb hk]

/-- AKMM, p. 744: with `V^D` independent of debt, **`V` is nonincreasing in debt**: at the
solution of (24.9)–(24.11), `B(b) ≤ B(b′) ⇒ V(b′, Y) ≤ V(b, Y)`. -/
theorem sd_V_antitone (hu : Monotone M.u) {q : Bd → Y → ℝ} (hq : ∀ b y, 0 ≤ q b y)
    {V : Bd → Y → ℝ} {VD : Y → ℝ} (h9 : ∀ b y, V b y = max (VD y) (M.repayValue q V b y))
    {b b' : Bd} (hbb : M.bond b ≤ M.bond b') (y : Y) : V b' y ≤ V b y := by
  rw [h9 b' y, h9 b y]
  exact max_le_max le_rfl (M.sd_VR_antitone hu hq V hbb y)

/-- AKMM, p. 744 and App. 24.A.3, p. 904: **the default set grows with debt.** The sovereign
defaults when `V^D(Y) > V^R(B, Y)` (ties repaid); if it defaults with debt `b` it defaults with
any larger debt `b′`. -/
theorem sd_default_set_mono (hu : Monotone M.u) {q : Bd → Y → ℝ} (hq : ∀ b y, 0 ≤ q b y)
    (V : Bd → Y → ℝ) (VD : Y → ℝ) {b b' : Bd} (hbb : M.bond b ≤ M.bond b') :
    {y | M.repayValue q V b y < VD y} ⊆ {y | M.repayValue q V b' y < VD y} :=
  fun y hy => lt_of_le_of_lt (M.sd_VR_antitone hu hq V hbb y) hy

/-- AKMM, p. 744: the repayment set `{Y : V^R(B, Y) ≥ V^D(Y)}` shrinks with debt. -/
theorem sd_repay_set_antitone (hu : Monotone M.u) {q : Bd → Y → ℝ} (hq : ∀ b y, 0 ≤ q b y)
    (V : Bd → Y → ℝ) (VD : Y → ℝ) {b b' : Bd} (hbb : M.bond b ≤ M.bond b') :
    {y | VD y ≤ M.repayValue q V b' y} ⊆ {y | VD y ≤ M.repayValue q V b y} :=
  fun y hy => le_trans hy (M.sd_VR_antitone hu hq V hbb y)

end SDModel

/-- A concrete model: one income level, one debt level (`B = 0`), `u = id`, no default cost,
`β = 1/2`, `ψ = 1/2`, `δ = 1`. -/
noncomputable def sd_example : SDModel Unit Unit where
  inc := fun _ => 1
  P := fun _ _ => 1
  markov := ⟨fun _ _ => zero_le_one, fun _ => by simp⟩
  bond := fun _ => 0
  b₀ := ()
  bond_b₀ := rfl
  u := id
  φ := fun _ => 0
  β := 1 / 2
  β_nonneg := by norm_num
  β_lt_one := by norm_num
  ψ := 1 / 2
  ψ_nonneg := by norm_num
  ψ_le_one := by norm_num
  δ := 1
  δ_nonneg := zero_le_one
  δ_le_one := le_rfl

/-- In the example, with any price, `V = V^D = 2` solves (24.9)–(24.11). -/
theorem sd_example_solution (q : Unit → Unit → ℝ) :
    (∀ b y, (fun _ _ => (2 : ℝ)) b y =
        max ((fun _ => (2 : ℝ)) y) (sd_example.repayValue q (fun _ _ => 2) b y)) ∧
      ∀ y, (fun _ => (2 : ℝ)) y = sd_example.defaultValue (fun _ _ => 2) (fun _ => 2) y := by
  refine ⟨fun b y => ?_, fun y => ?_⟩
  · simp only [SDModel.repayValue, SDModel.cons, sd_example, univ_unique, sup'_singleton,
      sum_singleton, id]
    norm_num
  · simp only [SDModel.defaultValue, sd_example, univ_unique, sum_singleton, id]
    norm_num

end AKMM.SovereignDefault

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Markov perfect equilibrium, the borrowing condition (24.13) and (24.A.3)

AKMM, §24.4.3, pp. 744–745; §24.4.4, (24.13), p. 748; Appendix 24.A.1, (24.A.3), p. 898.

* **Definition (§24.4.3)**: value functions `V, V^R, V^D`, a default rule `D̂`, a borrowing rule
  `B̂` and a price `q` with (a) (24.9)–(24.11) at `q`, (b) (24.12) given `D̂, B̂`, (c) `D̂, B̂`
  optimal (`IsMPE`, with a proved instance `mpe_example`).
* **As a fixed point** (`mpe_iff_fixedPt`): with `(V, V^D)` the unique Bellman solution at `q`,
  `D̂` its tie-repaying default rule and `B̂` a selection of maximisers, the tuple is an MPE iff
  `q` is a fixed point of `q ↦ T_{D̂(q), B̂(q)} q`; every MPE's values and default rule are
  those induced by its price (`mpe_values_eq`). The map is not a contraction (the induced rules
  jump in `q`). Existence and uniqueness with one-period debt (beyond the text: Auclert–Rognlie,
  Aguiar–Amador, cited p. 901) are proved with a continuum of debt in `UniqueEquilibrium`; on
  grids they fail (`Multiplicity`).
* In every MPE: `q ∈ [0, δ/(δ + r)]` (`mpe_price_mem`), `V` is nonincreasing in debt
  (`mpe_V_antitone`) and the default rule is nondecreasing in debt (`mpe_default_mono`).
* **(24.13)** (`eq_24_13`): at an interior optimum,
  `u′(C)[q + ∂q/∂B′ (B′ − (1 − δ)B)] = −βE[V₁(B′, Y′)]`; the printed equation lacks the minus
  sign and is false whenever `βE[V₁] ≠ 0` (`eq_24_13_printed_false`, with an explicit instance
  `eq_24_13_printed_counterexample`); with `V₁ ≤ 0` the marginal revenue is nonnegative
  (`eq_24_13_sign`).
* **(24.A.3)** (`eq_24_A_3`): `d q(B̂(B, Y), Y)/dY = q₁ ∂B̂/∂Y + q₂`.
-/

namespace AKMM.SovereignDefault

open Finset SargentStachurski.RecursiveDecisionProcesses

variable {Y Bd : Type*} [Fintype Y] [Fintype Bd]

variable (M : SDModel Y Bd) (r : ℝ) (V VR : Bd → Y → ℝ) (VD : Y → ℝ) (D : Bd → Y → ℝ)
  (Bh : Bd → Y → Bd) (q : Bd → Y → ℝ) in
/-- **AKMM, §24.4.3**, pp. 744–745: a Markov perfect equilibrium `(V, V^R, V^D, D̂, B̂, q)`. -/
structure IsMPE : Prop where
  /-- (a) (24.9). -/
  eq_24_9 : ∀ b y, V b y = max (VD y) (VR b y)
  /-- (a) (24.10). -/
  eq_24_10 : ∀ y, VD y = M.defaultValue V VD y
  /-- (a) (24.11). -/
  eq_24_11 : ∀ b y, VR b y = M.repayValue q V b y
  /-- (b) (24.12) given `D̂` and `B̂`. -/
  eq_24_12 : ∀ m y, q m y = bp_op12 M.P r M.δ D Bh q m y
  /-- (c) the default rule is optimal (ties repaid). -/
  default_opt : ∀ b y, D b y = if VR b y < VD y then 1 else 0
  /-- (c) the borrowing rule attains the maximum in (24.11). -/
  borrow_opt : ∀ b y, M.u (M.cons q y b (Bh b y)) + M.β * ∑ j, M.P y j * V (Bh b y) j = VR b y

/-- A Markov perfect equilibrium of the one-state, one-debt-level example `sd_example`
(with `r > −1`): `V = V^R = V^D = 2`, no default, and `q = 1/(1 + r)`. -/
theorem mpe_example {r : ℝ} (hr : -1 < r) :
    IsMPE sd_example r (fun _ _ => 2) (fun _ _ => 2) (fun _ => 2) (fun _ _ => 0)
      (fun _ _ => ()) (fun _ _ => (1 + r)⁻¹) where
  eq_24_9 := fun b y => ((sd_example_solution _).1 b y).trans
    (by rw [(sd_example_solution (fun _ _ => (1 + r)⁻¹)).1 b y |>.symm]; simp)
  eq_24_10 := (sd_example_solution (fun _ _ => (1 + r)⁻¹)).2
  eq_24_11 := fun b y => by
    have := (sd_example_solution (fun _ _ => (1 + r)⁻¹)).1 b y
    simp only [SDModel.repayValue, SDModel.cons, sd_example, univ_unique, sup'_singleton,
      sum_singleton, id] at this ⊢
    norm_num
  eq_24_12 := fun m y => by
    have : (1 + r) ≠ 0 := by linarith
    simp only [bp_op12, sd_example, univ_unique, sum_singleton]
    ring
  default_opt := fun b y => by simp
  borrow_opt := fun b y => by
    simp only [SDModel.cons, sd_example, univ_unique, sum_singleton, id]
    norm_num

/-- The unique solution `(V, V^D)` of (24.9)–(24.11) at the price `q`. -/
noncomputable def SDModel.bellmanSol (M : SDModel Y Bd) (q : Bd → Y → ℝ) :
    (Bd → Y → ℝ) × (Y → ℝ) :=
  (M.eq_24_9_to_24_11 q).choose

/-- The induced default rule (ties repaid). -/
noncomputable def SDModel.inducedDefault (M : SDModel Y Bd) (q : Bd → Y → ℝ) (b : Bd) (y : Y) :
    ℝ :=
  if M.repayValue q (M.bellmanSol q).1 b y < (M.bellmanSol q).2 y then 1 else 0

/-- A selection of maximisers in (24.11). -/
noncomputable def SDModel.inducedBorrow (M : SDModel Y Bd) (q : Bd → Y → ℝ) (b : Bd) (y : Y) :
    Bd :=
  (univ.exists_max_image (fun b' => M.u (M.cons q y b b') +
    M.β * ∑ j, M.P y j * (M.bellmanSol q).1 b' j) ⟨M.b₀, mem_univ _⟩).choose

/-- The equilibrium map `q ↦ T_{D̂(q), B̂(q)} q` of (24.A.1)–(24.A.2). -/
noncomputable def SDModel.mpeMap (M : SDModel Y Bd) (r : ℝ) (q : Bd → Y → ℝ) : Bd → Y → ℝ :=
  bp_op12 M.P r M.δ (M.inducedDefault q) (M.inducedBorrow q) q

/-- The selection attains the maximum: `u(C(B̂)) + βE V(B̂, Y′) = V^R(B, Y)`. -/
theorem SDModel.inducedBorrow_spec (M : SDModel Y Bd) (q : Bd → Y → ℝ) (b : Bd) (y : Y) :
    M.u (M.cons q y b (M.inducedBorrow q b y)) +
        M.β * ∑ j, M.P y j * (M.bellmanSol q).1 (M.inducedBorrow q b y) j =
      M.repayValue q (M.bellmanSol q).1 b y := by
  have h := (univ.exists_max_image (fun b' => M.u (M.cons q y b b') +
    M.β * ∑ j, M.P y j * (M.bellmanSol q).1 b' j) ⟨M.b₀, mem_univ _⟩).choose_spec
  refine le_antisymm (le_sup' (fun b' => M.u (M.cons q y b b') +
    M.β * ∑ j, M.P y j * (M.bellmanSol q).1 b' j) (mem_univ _)) ?_
  exact sup'_le _ _ fun b' _ => h.2 b' (mem_univ _)

/-- **AKMM, §24.4.3, the MPE as a fixed point**: with the Bellman solution, default rule and
borrowing selection induced by `q`, the tuple is a Markov perfect equilibrium iff `q` is a fixed
point of the equilibrium map. -/
theorem mpe_iff_fixedPt (M : SDModel Y Bd) (r : ℝ) (q : Bd → Y → ℝ) :
    Function.IsFixedPt (M.mpeMap r) q ↔
      IsMPE M r (M.bellmanSol q).1 (M.repayValue q (M.bellmanSol q).1) (M.bellmanSol q).2
        (M.inducedDefault q) (M.inducedBorrow q) q := by
  have hs := (M.eq_24_9_to_24_11 q).choose_spec.1
  constructor
  · intro hfix
    exact { eq_24_9 := hs.1
            eq_24_10 := hs.2
            eq_24_11 := fun _ _ => rfl
            eq_24_12 := fun m y => (congrFun (congrFun hfix m) y).symm
            default_opt := fun _ _ => rfl
            borrow_opt := M.inducedBorrow_spec q }
  · intro h
    funext m y
    exact (h.eq_24_12 m y).symm

/-- AKMM, §24.4.3: in every MPE the value functions and the default rule are those induced by
the price `q`: `(V, V^D)` is the unique Bellman solution at `q`, `V^R` is (24.11) and `D̂` the
tie-repaying rule. -/
theorem mpe_values_eq {M : SDModel Y Bd} {r : ℝ} {V VR : Bd → Y → ℝ} {VD : Y → ℝ}
    {D : Bd → Y → ℝ} {Bh : Bd → Y → Bd} {q : Bd → Y → ℝ} (h : IsMPE M r V VR VD D Bh q) :
    (V, VD) = M.bellmanSol q ∧ VR = M.repayValue q V ∧ D = M.inducedDefault q := by
  have hu := (M.eq_24_9_to_24_11 q).choose_spec.2
  have hVR : VR = M.repayValue q V := funext fun b => funext fun y => h.eq_24_11 b y
  have hW : (V, VD) = M.bellmanSol q :=
    hu (V, VD) ⟨fun b y => by
      change V b y = max (VD y) (M.repayValue q V b y)
      rw [h.eq_24_9, hVR], h.eq_24_10⟩
  refine ⟨hW, hVR, funext fun b => funext fun y => ?_⟩
  rw [h.default_opt, SDModel.inducedDefault, ← hW, hVR]

/-- AKMM, (24.12) in equilibrium: in every MPE (with `r > −1`, `δ + r > 0`) the price lies in
`[0, δ/(δ + r)]`. -/
theorem mpe_price_mem {M : SDModel Y Bd} {r : ℝ} {V VR : Bd → Y → ℝ} {VD : Y → ℝ}
    {D : Bd → Y → ℝ} {Bh : Bd → Y → Bd} {q : Bd → Y → ℝ} (h : IsMPE M r V VR VD D Bh q)
    (hr : -1 < r) (hδr : 0 < M.δ + r) (m : Bd) (y : Y) :
    0 ≤ q m y ∧ q m y ≤ M.δ / (M.δ + r) := by
  classical
  have hD : ∀ m j, D m j = 0 ∨ D m j = 1 := fun m j => by
    rw [h.default_opt]; split_ifs <;> simp
  have hA : BPAdmissible M.P r M.δ D (fun m j h => if Bh m j = h then 1 else 0) :=
    { markov := M.markov
      D_nonneg := fun m j => by rcases hD m j with h | h <;> simp [h]
      D_le_one := fun m j => by rcases hD m j with h | h <;> simp [h]
      B_nonneg := fun _ _ _ => by split_ifs <;> norm_num
      B_sum := fun m j => by simp
      δ_nonneg := M.δ_nonneg
      δ_le_one := M.δ_le_one
      r_gt := hr
      δr_pos := hδr }
  have hfix : Function.IsFixedPt (bp_op M.P r M.δ D (fun m j h => if Bh m j = h then 1 else 0))
      q := by
    rw [← bp_op12_eq]
    funext m y
    exact (h.eq_24_12 m y).symm
  have hc := bp_contracting hA
  obtain ⟨q', ⟨hfix', hb'⟩, -⟩ := eq_24_A_6 hA
  rw [hc.fixedPoint_unique hfix, ← hc.fixedPoint_unique hfix']
  exact hb' m y

/-- AKMM, p. 744: in every MPE (with `u` nondecreasing, `r > −1`, `δ + r > 0`) the value `V`
is nonincreasing in debt. -/
theorem mpe_V_antitone {M : SDModel Y Bd} {r : ℝ} {V VR : Bd → Y → ℝ} {VD : Y → ℝ}
    {D : Bd → Y → ℝ} {Bh : Bd → Y → Bd} {q : Bd → Y → ℝ} (h : IsMPE M r V VR VD D Bh q)
    (hu : Monotone M.u) (hr : -1 < r) (hδr : 0 < M.δ + r) {b b' : Bd}
    (hbb : M.bond b ≤ M.bond b') (y : Y) : V b' y ≤ V b y :=
  M.sd_V_antitone hu (fun m y => (mpe_price_mem h hr hδr m y).1)
    (fun b y => by rw [h.eq_24_9, h.eq_24_11]) hbb y

/-- AKMM, p. 744 and App. 24.A.3: in every MPE the default rule is nondecreasing in debt: if the
sovereign defaults at `(b, Y)` it defaults at `(b′, Y)` for `B(b′) ≥ B(b)`. -/
theorem mpe_default_mono {M : SDModel Y Bd} {r : ℝ} {V VR : Bd → Y → ℝ} {VD : Y → ℝ}
    {D : Bd → Y → ℝ} {Bh : Bd → Y → Bd} {q : Bd → Y → ℝ} (h : IsMPE M r V VR VD D Bh q)
    (hu : Monotone M.u) (hr : -1 < r) (hδr : 0 < M.δ + r) {b b' : Bd}
    (hbb : M.bond b ≤ M.bond b') (y : Y) : D b y ≤ D b' y := by
  have hVR := M.sd_VR_antitone hu (fun m y => (mpe_price_mem h hr hδr m y).1) V hbb y
  rw [h.default_opt, h.default_opt, h.eq_24_11, h.eq_24_11]
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (lt_of_le_of_lt hVR h1) h2
  · exact zero_le_one
  · exact le_rfl

/-- **AKMM, (24.13)**, p. 748, corrected: at an interior optimum `B′` of
`u(Y − δB + q(B′)[B′ − (1 − δ)B]) + βΣ_j p_j V(B′, Y_j)` with `u`, `q` and each `V(·, Y_j)`
differentiable, `u′(C)[q + q′(B′ − (1 − δ)B)] = −βΣ_j p_j V₁(B′, Y_j)`. -/
theorem eq_24_13 {u q : ℝ → ℝ} {Vn : Y → ℝ → ℝ} {p : Y → ℝ} {β δ B Yc Bp u₁ q₁ : ℝ}
    {V₁ : Y → ℝ} (hu : HasDerivAt u u₁ (Yc - δ * B + q Bp * (Bp - (1 - δ) * B)))
    (hq : HasDerivAt q q₁ Bp) (hV : ∀ j, HasDerivAt (Vn j) (V₁ j) Bp)
    (hmax : IsLocalMax (fun x => u (Yc - δ * B + q x * (x - (1 - δ) * B)) +
      β * ∑ j, p j * Vn j x) Bp) :
    u₁ * (q Bp + q₁ * (Bp - (1 - δ) * B)) = -(β * ∑ j, p j * V₁ j) := by
  have hC : HasDerivAt (fun x => Yc - δ * B + q x * (x - (1 - δ) * B))
      (q₁ * (Bp - (1 - δ) * B) + q Bp * 1) Bp := by
    have := hq.mul ((hasDerivAt_id Bp).sub_const ((1 - δ) * B))
    simpa using this.const_add (Yc - δ * B)
  have hS : HasDerivAt (fun x => ∑ j, p j * Vn j x) (∑ j, p j * V₁ j) Bp :=
    HasDerivAt.fun_sum fun j _ => (hV j).const_mul (p j)
  have hg := (HasDerivAt.comp Bp hu hC).add (hS.const_mul β)
  have := hmax.hasDerivAt_eq_zero hg
  linarith

/-- AKMM, (24.13), p. 748, **as printed** (`… = βE[V₁]`, without the minus sign) it is false
whenever `βE[V₁] ≠ 0`: it is inconsistent with the first-order condition `eq_24_13`. -/
theorem eq_24_13_printed_false {u q : ℝ → ℝ} {Vn : Y → ℝ → ℝ} {p : Y → ℝ}
    {β δ B Yc Bp u₁ q₁ : ℝ} {V₁ : Y → ℝ}
    (hu : HasDerivAt u u₁ (Yc - δ * B + q Bp * (Bp - (1 - δ) * B)))
    (hq : HasDerivAt q q₁ Bp) (hV : ∀ j, HasDerivAt (Vn j) (V₁ j) Bp)
    (hmax : IsLocalMax (fun x => u (Yc - δ * B + q x * (x - (1 - δ) * B)) +
      β * ∑ j, p j * Vn j x) Bp) (hne : β * ∑ j, p j * V₁ j ≠ 0) :
    u₁ * (q Bp + q₁ * (Bp - (1 - δ) * B)) ≠ β * ∑ j, p j * V₁ j := by
  intro h
  have := eq_24_13 hu hq hV hmax
  apply hne
  linarith

/-- AKMM, (24.13), p. 748: an explicit instance of the hypotheses where the printed equation
fails. One income state, `u = id`, a constant price `q = β`, `V(B′) = −B′` (so `V₁ = −1 < 0`):
the objective is constant, every `B′` is optimal, the corrected condition reads `β = β` and the
printed one `β = −β`. -/
theorem eq_24_13_printed_counterexample {β : ℝ} (hβ : 0 < β) (δ B Yc Bp : ℝ) :
    IsLocalMax (fun x => id (Yc - δ * B + (fun _ => β) x * (x - (1 - δ) * B)) +
      β * ∑ _j : Unit, (1 : ℝ) * (fun x : ℝ => -x) x) Bp ∧
      (1 : ℝ) * ((fun _ => β) Bp + 0 * (Bp - (1 - δ) * B)) = -(β * ∑ _j : Unit, (1 : ℝ) * (-1)) ∧
      (1 : ℝ) * ((fun _ => β) Bp + 0 * (Bp - (1 - δ) * B)) ≠ β * ∑ _j : Unit, (1 : ℝ) * (-1) := by
  refine ⟨Filter.Eventually.of_forall fun x => le_of_eq ?_, by simp, ?_⟩
  · simp only [id, univ_unique, sum_singleton, one_mul]
    ring
  · simp only [univ_unique, sum_singleton, one_mul, zero_mul, add_zero]
    linarith

/-- AKMM, p. 748: with `V` nonincreasing in debt (`V₁ ≤ 0`), nonnegative probabilities and
`β ≥ 0`, the right-hand side `−βE[V₁]` of (24.13) is nonnegative, so at an optimum with
`u′(C) > 0` the marginal revenue `q + q′(B′ − (1 − δ)B)` is nonnegative. -/
theorem eq_24_13_sign {u q : ℝ → ℝ} {Vn : Y → ℝ → ℝ} {p : Y → ℝ} {β δ B Yc Bp u₁ q₁ : ℝ}
    {V₁ : Y → ℝ} (hu : HasDerivAt u u₁ (Yc - δ * B + q Bp * (Bp - (1 - δ) * B)))
    (hq : HasDerivAt q q₁ Bp) (hV : ∀ j, HasDerivAt (Vn j) (V₁ j) Bp)
    (hmax : IsLocalMax (fun x => u (Yc - δ * B + q x * (x - (1 - δ) * B)) +
      β * ∑ j, p j * Vn j x) Bp) (hu₁ : 0 < u₁) (hβ : 0 ≤ β) (hp : ∀ j, 0 ≤ p j)
    (hV₁ : ∀ j, V₁ j ≤ 0) : 0 ≤ q Bp + q₁ * (Bp - (1 - δ) * B) := by
  have h := eq_24_13 hu hq hV hmax
  have hs : ∑ j, p j * V₁ j ≤ 0 := sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hp j)
    (hV₁ j)
  have : 0 ≤ u₁ * (q Bp + q₁ * (Bp - (1 - δ) * B)) := by
    rw [h]; nlinarith [mul_nonpos_of_nonneg_of_nonpos hβ hs]
  by_contra hneg
  rw [not_le] at hneg
  linarith [mul_neg_of_pos_of_neg hu₁ hneg]

/-- **AKMM, (24.A.3)**, p. 898: the total derivative of the equilibrium price with respect to
income, `d q(B̂(B, Y), Y)/dY = q₁(B̂, Y) ∂B̂/∂Y + q₂(B̂, Y)`, for `q` differentiable at
`(B̂(B, Y), Y)` with derivative `L` (`q₁ = L(1, 0)`, `q₂ = L(0, 1)`). -/
theorem eq_24_A_3 {q : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {Bh : ℝ → ℝ} {Yc b' : ℝ}
    (hq : HasFDerivAt q L (Bh Yc, Yc)) (hB : HasDerivAt Bh b' Yc) :
    HasDerivAt (fun y => q (Bh y, y)) (L (1, 0) * b' + L (0, 1)) Yc := by
  have h := HasFDerivAt.comp_hasDerivAt (f := fun y => (Bh y, y)) Yc hq
    (hB.prodMk (hasDerivAt_id' Yc))
  have : ((b', 1) : ℝ × ℝ) = b' • ((1 : ℝ), (0 : ℝ)) + ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  have hv : L (b', 1) = L (1, 0) * b' + L (0, 1) := by
    rw [this, map_add, map_smul, smul_eq_mul, mul_comm]
  rw [← hv]
  exact h

end AKMM.SovereignDefault

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Extreme-value smoothing: logit choice probabilities and (24.A.6)

AKMM, Appendix 24.A.1, Method 3, (24.A.5)–(24.A.6), pp. 900–901 (Dvorkin, Sanchez, Sapriza
and Yurdagul, 2021).

With i.i.d. standard Gumbel shocks `ε_k` (c.d.f. `G(x) = exp(−e^{−x})`, density
`g(x) = e^{−x} exp(−e^{−x})`) added to the values `v_k` of finitely many alternatives, the
probability that alternative `h` is chosen is
`P_h(v) = ∫ g(x) Π_{k≠h} G(x + v_h − v_k) dx`
(condition on `ε_h = x`; the other shocks are independent).

* `∫ e^{−x} exp(−c e^{−x}) dx = 1/c` for `c > 0` (`ev_integral`), by the fundamental theorem of
  calculus on `ℝ`.
* **Logit** (`ev_logit`): `P_h(v) = e^{v_h}/Σ_k e^{v_k}`; the probabilities are positive, sum
  to one and are continuous in the values (`ev_logit_pos`, `ev_logit_sum`,
  `ev_logit_continuous`), so small changes in values move choice probabilities only a little,
  the smoothing the text describes.
* **Default and borrowing probabilities** (`ev_conditional_borrow`): with the default option
  and the debt choices as alternatives, the borrowing probabilities conditional on repayment
  are again logit over the debt choices (independence of irrelevant alternatives).
* **(24.A.6)** (`eq_24_A_6_logit`): with logit default and borrowing probabilities the bond
  price exists, is unique and lies in `[0, δ/(δ + r)]` (via `eq_24_A_6`).

The conditioning formula is derived from the product of the Gumbel laws in `GumbelProduct`
(`ev_logit_of_gumbel`).
-/

namespace AKMM.SovereignDefault

open MeasureTheory Filter Topology Finset

/-- The standard Gumbel c.d.f. `G(x) = exp(−e^{−x})`. -/
noncomputable def ev_gumbelCDF (x : ℝ) : ℝ := Real.exp (-Real.exp (-x))

/-- The standard Gumbel density `g(x) = e^{−x} exp(−e^{−x})`. -/
noncomputable def ev_gumbelPDF (x : ℝ) : ℝ := Real.exp (-x) * Real.exp (-Real.exp (-x))

/-- AKMM, p. 900: the probability that alternative `h` has the largest `v_k + ε_k`, given
i.i.d. Gumbel shocks: `P_h(v) = ∫ g(x) Π_{k≠h} G(x + v_h − v_k) dx`. -/
noncomputable def ev_choiceProb {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℝ) (h : ι) :
    ℝ :=
  ∫ x, ev_gumbelPDF x * ∏ k ∈ univ.erase h, ev_gumbelCDF (x + v h - v k)

/-- The antiderivative `exp(−c e^{−x})/c` of `e^{−x} exp(−c e^{−x})`. -/
theorem ev_hasDerivAt {c : ℝ} (hc : 0 < c) (x : ℝ) :
    HasDerivAt (fun x => Real.exp (-(c * Real.exp (-x))) / c)
      (Real.exp (-x) * Real.exp (-(c * Real.exp (-x)))) x := by
  have h1 : HasDerivAt (fun x => -(c * Real.exp (-x))) (c * Real.exp (-x)) x := by
    have := (((hasDerivAt_neg x).exp).const_mul c).neg
    convert this using 1
    ring
  have := (h1.exp).div_const c
  convert this using 1
  field_simp

/-- The density `e^{−x} exp(−c e^{−x})` is nonnegative and continuous. -/
theorem ev_density_continuous (c : ℝ) :
    Continuous fun x => Real.exp (-x) * Real.exp (-(c * Real.exp (-x))) := by
  fun_prop

/-- The limits of the antiderivative and the integrability of `e^{−x} exp(−c e^{−x})`. -/
theorem ev_integrable {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x => Real.exp (-(c * Real.exp (-x))) / c) atBot (𝓝 0) ∧
      Tendsto (fun x => Real.exp (-(c * Real.exp (-x))) / c) atTop (𝓝 (1 / c)) ∧
      Integrable fun x => Real.exp (-x) * Real.exp (-(c * Real.exp (-x))) := by
  set F : ℝ → ℝ := fun x => Real.exp (-(c * Real.exp (-x))) / c with hF
  set f : ℝ → ℝ := fun x => Real.exp (-x) * Real.exp (-(c * Real.exp (-x))) with hf
  have hd : ∀ x, HasDerivAt F (f x) x := ev_hasDerivAt hc
  have hpos : ∀ x, 0 ≤ f x := fun x => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have htop : Tendsto F atTop (𝓝 (1 / c)) := by
    have h1 : Tendsto (fun x : ℝ => -(c * Real.exp (-x))) atTop (𝓝 (-(c * 0))) :=
      (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul c).neg
    have h2 := (Real.continuous_exp.tendsto _).comp h1
    simp only [mul_zero, neg_zero, Real.exp_zero] at h2
    simpa [hF, one_div] using h2.div_const c
  have hbot : Tendsto F atBot (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => Real.exp (-x)) atBot atTop :=
      Real.tendsto_exp_atTop.comp tendsto_neg_atBot_atTop
    have h1 : Tendsto (fun x : ℝ => -(c * Real.exp (-x))) atBot atBot :=
      tendsto_neg_atTop_atBot.comp (h0.const_mul_atTop hc)
    have h2 := Real.tendsto_exp_atBot.comp h1
    simpa [hF] using h2.div_const c
  have hFnn : ∀ x, 0 ≤ F x := fun x => div_nonneg (Real.exp_pos _).le hc.le
  have hint : Integrable f := by
    have hIoi : IntegrableOn f (Set.Ioi 0) :=
      integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hd x) (fun x _ => hpos x) htop
    have hIic : IntegrableOn f (Set.Iic 0) := by
      refine integrableOn_Iic_of_intervalIntegral_norm_bounded (F 0) 0
        (a := fun n : ℕ => -(n : ℝ)) (l := atTop)
        (fun n => (ev_density_continuous c).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
        (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop) ?_
      refine Eventually.of_forall fun n => ?_
      have hn : -(n : ℝ) ≤ 0 := neg_nonpos.2 (Nat.cast_nonneg n)
      have heq : ∫ x in -(n : ℝ)..0, ‖f x‖ = ∫ x in -(n : ℝ)..0, f x :=
        intervalIntegral.integral_congr fun x _ => by
          simp only [Real.norm_eq_abs, abs_of_nonneg (hpos x)]
      rw [heq, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
        ((ev_density_continuous c).intervalIntegrable _ _)]
      linarith [hFnn (-(n : ℝ))]
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
    exact hIic.union hIoi
  exact ⟨hbot, htop, hint⟩

/-- `∫ e^{−x} exp(−c e^{−x}) dx = 1/c` for `c > 0`. -/
theorem ev_integral {c : ℝ} (hc : 0 < c) :
    ∫ x, Real.exp (-x) * Real.exp (-(c * Real.exp (-x))) = 1 / c := by
  obtain ⟨hbot, htop, hint⟩ := ev_integrable hc
  rw [integral_of_hasDerivAt_of_tendsto (ev_hasDerivAt hc) hint hbot htop, sub_zero]

/-- **Logit choice probabilities** (AKMM, p. 900, Method 3): with i.i.d. Gumbel shocks the
probability that alternative `h` is chosen is `e^{v_h}/Σ_k e^{v_k}`. -/
theorem ev_logit {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℝ) (h : ι) :
    ev_choiceProb v h = Real.exp (v h) / ∑ k, Real.exp (v k) := by
  set c := ∑ k, Real.exp (v k - v h) with hc
  have hcpos : 0 < c := by
    rw [hc, ← add_sum_erase _ _ (mem_univ h)]
    exact add_pos_of_pos_of_nonneg (Real.exp_pos _)
      (sum_nonneg fun _ _ => (Real.exp_pos _).le)
  have hpt : ∀ x, ev_gumbelPDF x * ∏ k ∈ univ.erase h, ev_gumbelCDF (x + v h - v k) =
      Real.exp (-x) * Real.exp (-(c * Real.exp (-x))) := by
    intro x
    unfold ev_gumbelPDF ev_gumbelCDF
    rw [← Real.exp_sum, mul_assoc, ← Real.exp_add]
    congr 2
    rw [hc, ← add_sum_erase _ _ (mem_univ h), sub_self, Real.exp_zero, add_mul, one_mul,
      sum_mul, neg_add, ← sum_neg_distrib]
    congr 1
    refine sum_congr rfl fun k _ => ?_
    rw [← Real.exp_add]
    congr 2
    ring
  unfold ev_choiceProb
  simp only [hpt]
  rw [ev_integral hcpos, hc]
  have hS : ∑ k, Real.exp (v k - v h) = (∑ k, Real.exp (v k)) / Real.exp (v h) := by
    rw [sum_div]
    exact sum_congr rfl fun k _ => by rw [Real.exp_sub]
  rw [hS, one_div, inv_div]

/-- The logit probabilities are positive. -/
theorem ev_logit_pos {ι : Type*} [Fintype ι] [Nonempty ι] (v : ι → ℝ) (h : ι) :
    0 < Real.exp (v h) / ∑ k, Real.exp (v k) :=
  div_pos (Real.exp_pos _) (sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty)

/-- The logit probabilities sum to one. -/
theorem ev_logit_sum {ι : Type*} [Fintype ι] [Nonempty ι] (v : ι → ℝ) :
    ∑ h, Real.exp (v h) / ∑ k, Real.exp (v k) = 1 := by
  rw [← sum_div, div_self (sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty).ne']

/-- The logit probabilities are continuous in the values (the smoothing of Method 3: a small
change in values never makes a choice probability jump). -/
theorem ev_logit_continuous {ι : Type*} [Fintype ι] [Nonempty ι] (h : ι) :
    Continuous fun v : ι → ℝ => Real.exp (v h) / ∑ k, Real.exp (v k) := by
  refine Continuous.div (by fun_prop) (by fun_prop) fun v => ?_
  exact (sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty).ne'

/-- AKMM, p. 900: with the default option (`none`) and the debt choices (`some h`) as
alternatives, the borrowing probabilities conditional on repayment,
`P(some h)/(1 − P(none))`, are logit over the debt choices. -/
theorem ev_conditional_borrow {ι : Type*} [Fintype ι] [Nonempty ι] (vD : ℝ) (W : ι → ℝ)
    (h : ι) :
    let v : Option ι → ℝ := fun o => o.elim vD W
    (Real.exp (v (some h)) / ∑ k, Real.exp (v k)) /
        (1 - Real.exp (v none) / ∑ k, Real.exp (v k)) =
      Real.exp (W h) / ∑ k, Real.exp (W k) := by
  intro v
  have hsum : ∑ k, Real.exp (v k) = Real.exp vD + ∑ k, Real.exp (W k) := by
    rw [Fintype.sum_option]
    rfl
  have hW : 0 < ∑ k, Real.exp (W k) := sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty
  have hT : 0 < Real.exp vD + ∑ k, Real.exp (W k) := add_pos (Real.exp_pos _) hW
  rw [hsum]
  change (Real.exp (W h) / _) / (1 - Real.exp vD / _) = _
  rw [show 1 - Real.exp vD / (Real.exp vD + ∑ k, Real.exp (W k)) =
      (∑ k, Real.exp (W k)) / (Real.exp vD + ∑ k, Real.exp (W k)) by field_simp; ring,
    div_div_div_cancel_right₀ hT.ne']

/-- **AKMM, (24.A.6)**, p. 900, with logit probabilities: if the default probability is
`e^{V^D}/(e^{V^D} + Σ_h e^{W_h})` and the borrowing probabilities are `e^{W_h}/Σ e^{W}`
(values `VDv`, `Wv` at each state), the bond price exists, is unique and lies in
`[0, δ/(δ + r)]`. -/
theorem eq_24_A_6_logit {Bd Y : Type*} [Fintype Bd] [Fintype Y] [Nonempty Bd]
    {P : Matrix Y Y ℝ} (hP : SargentStachurski.RecursiveDecisionProcesses.IsMarkov P)
    {r δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hr : -1 < r) (hδr : 0 < δ + r)
    (VDv : Bd → Y → ℝ) (Wv : Bd → Y → Bd → ℝ) :
    ∃! q : Bd → Y → ℝ, Function.IsFixedPt (bp_op P r δ
        (fun m j => Real.exp (VDv m j) / (Real.exp (VDv m j) + ∑ k, Real.exp (Wv m j k)))
        (fun m j h => Real.exp (Wv m j h) / ∑ k, Real.exp (Wv m j k))) q ∧
      ∀ m y, 0 ≤ q m y ∧ q m y ≤ δ / (δ + r) := by
  refine eq_24_A_6 ⟨hP, fun m j => ?_, fun m j => ?_, fun m j h => (ev_logit_pos _ h).le,
    fun m j => ev_logit_sum _, hδ0, hδ1, hr, hδr⟩
  · exact div_nonneg (Real.exp_pos _).le (add_pos (Real.exp_pos _)
      (sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty)).le
  · rw [div_le_one (add_pos (Real.exp_pos _) (sum_pos (fun _ _ => Real.exp_pos _)
      univ_nonempty))]
    exact le_add_of_nonneg_right (sum_nonneg fun _ _ => (Real.exp_pos _).le)

end AKMM.SovereignDefault

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Logit choice probabilities from independent Gumbel shocks

AKMM, Appendix 24.A.1, Method 3, p. 900: "the `ε` shocks follow an i.i.d. process"; the
probability that the sovereign picks an alternative "depends on `ε_m` taking a sufficiently
larger value relative to the other shocks".

The standard Gumbel law `γ` has density `g(x) = e^{−x} exp(−e^{−x})`; it is a probability
measure with c.d.f. `γ(−∞, a] = exp(−e^{−a})` (`gp_isProbabilityMeasure`, `gp_measure_Iic`).
For finitely many alternatives `k ∈ Fin (n + 1)` with values `v_k` and i.i.d. shocks
`ε ∼ γ^{⊗(n+1)}` (the product measure),
`Pr(v_i + ε_i ≥ v_k + ε_k for all k) = e^{v_i}/Σ_k e^{v_k}` (`ev_logit_of_gumbel`): the
probability is computed by splitting off the coordinate `i` (Mathlib's
`measurePreserving_piFinSuccAbove`), Tonelli, and `∫ e^{−x} exp(−c e^{−x}) dx = 1/c`. This
derives, rather than assumes, the conditioning formula used in `ExtremeValue`.
-/

namespace AKMM.SovereignDefault

open MeasureTheory Filter Topology Finset

/-- The standard Gumbel law, with density `ev_gumbelPDF`. -/
noncomputable abbrev ev_gumbel : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (ev_gumbelPDF x)

/-- The Gumbel density is continuous. -/
theorem gp_pdf_continuous : Continuous ev_gumbelPDF := by
  unfold ev_gumbelPDF; fun_prop

/-- The Gumbel density is integrable. -/
theorem gp_pdf_integrable : Integrable ev_gumbelPDF := by
  have h := (ev_integrable one_pos).2.2
  exact (by simpa only [one_mul] using h :
    Integrable fun x => Real.exp (-x) * Real.exp (-Real.exp (-x)))

/-- The Gumbel density is nonnegative. -/
theorem gp_pdf_nonneg (x : ℝ) : 0 ≤ ev_gumbelPDF x :=
  mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le

/-- The Gumbel c.d.f. is an antiderivative of the density. -/
theorem gp_hasDerivAt (x : ℝ) : HasDerivAt ev_gumbelCDF (ev_gumbelPDF x) x := by
  have h := ev_hasDerivAt one_pos x
  simp only [one_mul, div_one] at h
  exact h

/-- `∫_{(−∞, a]} g = exp(−e^{−a})`. -/
theorem gp_integral_Iic (a : ℝ) : ∫ x in Set.Iic a, ev_gumbelPDF x = ev_gumbelCDF a := by
  have hbot : Tendsto ev_gumbelCDF atBot (𝓝 0) := by
    have h := (ev_integrable one_pos).1
    exact (by simpa only [one_mul, div_one] using h :
      Tendsto (fun x => Real.exp (-Real.exp (-x))) atBot (𝓝 0))
  rw [integral_Iic_of_hasDerivAt_of_tendsto' (fun x _ => gp_hasDerivAt x)
    gp_pdf_integrable.integrableOn hbot, sub_zero]

/-- The Gumbel law of `(−∞, a]` is `exp(−e^{−a})`. -/
theorem gp_measure_Iic (a : ℝ) : ev_gumbel (Set.Iic a) = ENNReal.ofReal (ev_gumbelCDF a) := by
  rw [withDensity_apply _ measurableSet_Iic, ← gp_integral_Iic,
    ofReal_integral_eq_lintegral_ofReal gp_pdf_integrable.integrableOn
      (Eventually.of_forall gp_pdf_nonneg)]

/-- The Gumbel law is a probability measure. -/
theorem gp_isProbabilityMeasure : IsProbabilityMeasure ev_gumbel := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal gp_pdf_integrable (Eventually.of_forall gp_pdf_nonneg)]
  have h := ev_integral one_pos
  simp only [one_mul, div_one] at h
  rw [show (∫ x, ev_gumbelPDF x) = 1 from h, ENNReal.ofReal_one]

/-- **Logit from i.i.d. Gumbel shocks** (AKMM, p. 900, Method 3). With values `v_k`,
`k ∈ Fin (n + 1)`, and independent standard Gumbel shocks `ε_k` (the product law), the
probability that alternative `i` attains `max_k (v_k + ε_k)` is `e^{v_i}/Σ_k e^{v_k}`. -/
theorem ev_logit_of_gumbel {n : ℕ} (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (Measure.pi fun _ : Fin (n + 1) => ev_gumbel) {ε | ∀ k, v k + ε k ≤ v i + ε i} =
      ENNReal.ofReal (Real.exp (v i) / ∑ k, Real.exp (v k)) := by
  have hP : IsProbabilityMeasure ev_gumbel := gp_isProbabilityMeasure
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ev_gumbel) i
  set S : Set (ℝ × (Fin n → ℝ)) := {p | ∀ j, v (i.succAbove j) + p.2 j ≤ v i + p.1} with hSdef
  have hS : MeasurableSet S := by
    have : S = ⋂ j, {p : ℝ × (Fin n → ℝ) | v (i.succAbove j) + p.2 j ≤ v i + p.1} := by
      ext p; simp [hSdef]
    rw [this]
    exact MeasurableSet.iInter fun j => measurableSet_le (by fun_prop) (by fun_prop)
  have hA : {ε : Fin (n + 1) → ℝ | ∀ k, v k + ε k ≤ v i + ε i} = e ⁻¹' S := by
    ext ε
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hSdef, e,
      MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv, Equiv.coe_fn_symm_mk,
      Fin.removeNth]
    rw [Fin.forall_iff_succAbove i]
    simp
  rw [hA, hmp.measure_preimage hS.nullMeasurableSet, Measure.prod_apply hS]
  -- the sections are boxes
  have hsec : ∀ x : ℝ, Prod.mk x ⁻¹' S =
      Set.univ.pi fun j => Set.Iic (v i + x - v (i.succAbove j)) := by
    intro x
    ext p
    simp only [Set.mem_preimage, hSdef, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ,
      Set.mem_Iic, true_implies]
    exact forall_congr' fun j => by constructor <;> intro h <;> linarith
  simp only [hsec, Measure.pi_pi, gp_measure_Iic]
  -- move to a real integral
  set c := ∑ k, Real.exp (v k - v i) with hc
  have hcpos : 0 < c := sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty
  have hpt : ∀ x, ev_gumbelPDF x * ∏ j, ev_gumbelCDF (v i + x - v (i.succAbove j)) =
      Real.exp (-x) * Real.exp (-(c * Real.exp (-x))) := by
    intro x
    unfold ev_gumbelPDF ev_gumbelCDF
    rw [← Real.exp_sum, mul_assoc, ← Real.exp_add]
    congr 2
    rw [hc, Fin.sum_univ_succAbove _ i, sub_self, Real.exp_zero, add_mul, one_mul, sum_mul,
      neg_add, ← sum_neg_distrib]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [← Real.exp_add]
    congr 2
    ring
  have hmeasG : Measurable fun x => ∏ j, ENNReal.ofReal
      (ev_gumbelCDF (v i + x - v (i.succAbove j))) := by
    unfold ev_gumbelCDF; fun_prop
  rw [show ev_gumbel = volume.withDensity (fun x => ENNReal.ofReal (ev_gumbelPDF x)) from rfl,
    lintegral_withDensity_eq_lintegral_mul₀ (f := fun x => ENNReal.ofReal (ev_gumbelPDF x))
      gp_pdf_continuous.measurable.ennreal_ofReal.aemeasurable hmeasG.aemeasurable]
  have hfun : ((fun x => ENNReal.ofReal (ev_gumbelPDF x)) * fun x => ∏ j, ENNReal.ofReal
      (ev_gumbelCDF (v i + x - v (i.succAbove j)))) =
      fun x => ENNReal.ofReal (Real.exp (-x) * Real.exp (-(c * Real.exp (-x)))) := by
    funext x
    rw [Pi.mul_apply, ← ENNReal.ofReal_prod_of_nonneg (s := univ)
      (f := fun j => ev_gumbelCDF (v i + x - v (i.succAbove j))) (fun j _ => (Real.exp_pos _).le),
      ← ENNReal.ofReal_mul (gp_pdf_nonneg x), hpt x]
  rw [hfun, ← ofReal_integral_eq_lintegral_ofReal (ev_integrable hcpos).2.2
    (Eventually.of_forall fun x => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le),
    ev_integral hcpos]
  congr 1
  have hS' : ∑ k, Real.exp (v k - v i) = (∑ k, Real.exp (v k)) / Real.exp (v i) := by
    rw [sum_div]
    exact sum_congr rfl fun k _ => by rw [Real.exp_sub]
  rw [hc, hS', one_div, inv_div]

/-- The derived probability agrees with the conditioning formula of `ExtremeValue`. -/
theorem ev_choiceProb_eq_gumbel {n : ℕ} (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (Measure.pi fun _ : Fin (n + 1) => ev_gumbel) {ε | ∀ k, v k + ε k ≤ v i + ε i} =
      ENNReal.ofReal (ev_choiceProb v i) := by
  rw [ev_logit_of_gumbel, ev_logit]

end AKMM.SovereignDefault

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Calibration formulas and the iso-moment slope (App. 24.A.2–24.A.3)

AKMM, §24.4.1, pp. 742–743; Appendix 24.A.2, (24.A.7) and Table 24.A.1, pp. 901–902; Appendix
24.A.3, footnote 44 and p. 905.

* **CRRA** (p. 901): `u(c) = (c^{1−σ} − 1)/(1 − σ)` has `u′(c) = c^{−σ} > 0`, decreasing, so it
  satisfies the hypotheses of the two-period Euler equation (24.6) (`cal_crra_hasDerivAt`,
  `cal_crra_deriv_pos`, `cal_crra_deriv_antitone`).
* **(24.A.7)**: `φ(Y) = max{Y[λ₀Y + λ₁(Y − E Y)], 0}` is nonnegative, its loss fraction
  `φ(Y)/Y` is nondecreasing in `Y` when `λ₀ + λ₁ ≥ 0` (the assumption of p. 743), equals `λ₀`
  at `Y = E Y = 1` (`λ₀` is "the average fraction"), rises with `λ₀`, and rises with `λ₁`
  above mean income and falls with it below (p. 905) (`cal_phi_*`).
* **Table 24.A.1** (`μ = −σ_ε²/2`): for the AR(1) `log Y_t = (1 − ρ)μ + ρ log Y_{t−1} + ε_t` the
  stationary variance is `σ_ε²/(1 − ρ²)` (`cal_ar1_variance`), and with `log Y` Gaussian
  `E Y = exp(μ + σ_ε²/(2(1 − ρ²)))` (`cal_lognormal_mean`); `E Y = 1` requires
  `μ = −σ_ε²/(2(1 − ρ²))` (`cal_mean_one_iff`), and the printed `μ = −σ_ε²/2` gives `E Y > 1`
  whenever `ρ ≠ 0` (`cal_table_mu_printed_false`).
* **Footnote 44** (`fn_44`, `fn_44_exists`): the iso-moment curve `X(λ₀, λ₁) = X̄` exists near a
  point where `∂X/∂λ₁ ≠ 0` (Mathlib's bivariate implicit function theorem) and has slope
  `dλ₁/dλ₀ = −(∂X/∂λ₀)/(∂X/∂λ₁)`.
-/

namespace AKMM.SovereignDefault

open MeasureTheory ProbabilityTheory Filter Topology

/-- AKMM, p. 901: CRRA utility `u(c) = (c^{1−σ} − 1)/(1 − σ)`, `σ ≠ 1`. -/
noncomputable def cal_crra (σ c : ℝ) : ℝ := (c ^ (1 - σ) - 1) / (1 - σ)

/-- AKMM, p. 901: `u′(c) = c^{−σ}` for `c > 0`. -/
theorem cal_crra_hasDerivAt {σ c : ℝ} (hσ : σ ≠ 1) (hc : 0 < c) :
    HasDerivAt (cal_crra σ) (c ^ (-σ)) c := by
  have h1 : (1 - σ) ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
  have := ((Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hc.ne')).sub_const 1).div_const
    (1 - σ)
  have h2 : HasDerivAt (cal_crra σ) ((1 - σ) * c ^ (1 - σ - 1) / (1 - σ)) c := this
  convert h2 using 1
  rw [show 1 - σ - 1 = -σ by ring]
  field_simp

/-- `u′(c) = c^{−σ} > 0`. -/
theorem cal_crra_deriv_pos {σ c : ℝ} (hσ : σ ≠ 1) (hc : 0 < c) : 0 < deriv (cal_crra σ) c := by
  rw [(cal_crra_hasDerivAt hσ hc).deriv]
  exact Real.rpow_pos_of_pos hc _

/-- For `σ > 0`, `u′` is decreasing on `(0, ∞)` (concavity). -/
theorem cal_crra_deriv_antitone {σ : ℝ} (hσ : σ ≠ 1) (hσ0 : 0 < σ) :
    AntitoneOn (deriv (cal_crra σ)) (Set.Ioi 0) := by
  intro a ha b hb hab
  rw [(cal_crra_hasDerivAt hσ hb).deriv, (cal_crra_hasDerivAt hσ ha).deriv]
  exact Real.rpow_le_rpow_of_nonpos ha hab (by linarith)

/-- AKMM, (24.A.7), p. 901: the income cost of default
`φ(Y) = max{Y[λ₀Y + λ₁(Y − E Y)], 0}`. -/
noncomputable def cal_phi (lam0 lam1 EY Yv : ℝ) : ℝ := max (Yv * (lam0 * Yv + lam1 * (Yv - EY))) 0

/-- AKMM, p. 901: the cost of default is nonnegative. -/
theorem cal_phi_nonneg (lam0 lam1 EY Yv : ℝ) : 0 ≤ cal_phi lam0 lam1 EY Yv := le_max_right _ _

/-- The loss fraction: `φ(Y)/Y = max{λ₀Y + λ₁(Y − E Y), 0}` for `Y > 0`. -/
theorem cal_phi_div {lam0 lam1 EY Yv : ℝ} (hY : 0 < Yv) :
    cal_phi lam0 lam1 EY Yv / Yv = max (lam0 * Yv + lam1 * (Yv - EY)) 0 := by
  unfold cal_phi
  rw [div_eq_iff hY.ne', max_mul_of_nonneg _ _ hY.le, zero_mul, mul_comm]

/-- AKMM, p. 743: with `λ₀ + λ₁ ≥ 0`, (24.A.7) makes default proportionally more costly in good
times: `φ(Y)/Y` is nondecreasing in `Y > 0`. -/
theorem cal_phi_div_monotone {lam0 lam1 EY : ℝ} (hlam : 0 ≤ lam0 + lam1) :
    MonotoneOn (fun Yv => cal_phi lam0 lam1 EY Yv / Yv) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only
  rw [cal_phi_div ha, cal_phi_div hb]
  refine max_le_max ?_ le_rfl
  nlinarith

/-- AKMM, p. 901: with `E Y = 1`, at mean income the loss fraction is `λ₀` ("the average
fraction of income lost during defaults"), for `λ₀ ≥ 0`. -/
theorem cal_phi_at_mean {lam0 lam1 : ℝ} (h0 : 0 ≤ lam0) : cal_phi lam0 lam1 1 1 / 1 = lam0 := by
  rw [cal_phi_div one_pos]
  simp [max_eq_left h0]

/-- AKMM, p. 904: a higher `λ₀` raises the cost of default at every income `Y ≥ 0`. -/
theorem cal_phi_mono_lam0 {lam1 EY Yv : ℝ} (hY : 0 ≤ Yv) :
    Monotone fun lam0 => cal_phi lam0 lam1 EY Yv := by
  intro a b hab
  exact max_le_max (mul_le_mul_of_nonneg_left (by nlinarith) hY) le_rfl

/-- AKMM, p. 905: a higher `λ₁` makes default less costly below mean income and more costly
above it. -/
theorem cal_phi_lam1 {lam0 EY Yv : ℝ} (hY : 0 ≤ Yv) :
    (Yv ≤ EY → Antitone fun lam1 => cal_phi lam0 lam1 EY Yv) ∧
      (EY ≤ Yv → Monotone fun lam1 => cal_phi lam0 lam1 EY Yv) := by
  constructor
  · intro h a b hab
    exact max_le_max (mul_le_mul_of_nonneg_left (by nlinarith) hY) le_rfl
  · intro h a b hab
    exact max_le_max (mul_le_mul_of_nonneg_left (by nlinarith) hY) le_rfl

/-- AKMM, p. 742: the stationary variance `s² = σ_ε²/(1 − ρ²)` of
`log Y_t = (1 − ρ)μ + ρ log Y_{t−1} + ε_t` solves `s² = ρ²s² + σ_ε²`, and the stationary mean
`μ` solves `μ = (1 − ρ)μ + ρμ`. -/
theorem cal_ar1_variance {ρ σε μ : ℝ} (hρ : |ρ| < 1) :
    σε ^ 2 / (1 - ρ ^ 2) = ρ ^ 2 * (σε ^ 2 / (1 - ρ ^ 2)) + σε ^ 2 ∧ μ = (1 - ρ) * μ + ρ * μ := by
  have h : 0 < 1 - ρ ^ 2 := by
    have : ρ ^ 2 < 1 := by rw [← sq_abs]; nlinarith [abs_nonneg ρ]
    linarith
  refine ⟨?_, by ring⟩
  field_simp
  ring

/-- If `log Y ∼ N(μ, s²)` then `E Y = exp(μ + s²/2)`. -/
theorem cal_lognormal_mean {Ω : Type*} [MeasurableSpace Ω] {Pm : Measure Ω} {Z : Ω → ℝ} {μ : ℝ}
    {v : NNReal} (hZ : HasLaw Z (gaussianReal μ v) Pm) :
    ∫ ω, Real.exp (Z ω) ∂Pm = Real.exp (μ + v / 2) := by
  have h := mgf_gaussianReal hZ 1
  simp only [mgf, one_mul, one_pow, mul_one] at h
  rw [h]

/-- AKMM, p. 901: "the value for `μ` is chosen so that `E(Y) = 1`": with `log Y` Gaussian with
mean `μ` and the stationary variance `s²`, `E Y = 1` iff `μ = −s²/2`. -/
theorem cal_mean_one_iff {Ω : Type*} [MeasurableSpace Ω] {Pm : Measure Ω} {Z : Ω → ℝ} {μ : ℝ}
    {v : NNReal} (hZ : HasLaw Z (gaussianReal μ v) Pm) :
    ∫ ω, Real.exp (Z ω) ∂Pm = 1 ↔ μ = -(v / 2) := by
  rw [cal_lognormal_mean hZ, Real.exp_eq_one_iff]
  constructor <;> intro h <;> linarith

/-- **AKMM, Table 24.A.1**, p. 902, as printed: `μ = −σ_ε²/2`. With the stationary variance
`s² = σ_ε²/(1 − ρ²)` of the AR(1), this gives `E Y = exp(ρ²σ_ε²/(2(1 − ρ²))) > 1` whenever
`ρ ≠ 0` and `σ_ε ≠ 0`; the mean-one normalisation needs `μ = −σ_ε²/(2(1 − ρ²))`. -/
theorem cal_table_mu_printed_false {Ω : Type*} [MeasurableSpace Ω] {Pm : Measure Ω}
    {Z : Ω → ℝ} {ρ σε : ℝ} (hρ : |ρ| < 1) (hρ0 : ρ ≠ 0) (hσ : σε ≠ 0) {v : NNReal}
    (hv : (v : ℝ) = σε ^ 2 / (1 - ρ ^ 2)) (hZ : HasLaw Z (gaussianReal (-(σε ^ 2 / 2)) v) Pm) :
    1 < ∫ ω, Real.exp (Z ω) ∂Pm := by
  rw [cal_lognormal_mean hZ, hv]
  have h : 0 < 1 - ρ ^ 2 := by
    have : ρ ^ 2 < 1 := by rw [← sq_abs]; nlinarith [abs_nonneg ρ]
    linarith
  have hpos : 0 < -(σε ^ 2 / 2) + σε ^ 2 / (1 - ρ ^ 2) / 2 := by
    have e : -(σε ^ 2 / 2) + σε ^ 2 / (1 - ρ ^ 2) / 2 = ρ ^ 2 * σε ^ 2 / (2 * (1 - ρ ^ 2)) := by
      field_simp; ring
    rw [e]
    exact div_pos (mul_pos (pow_pos (abs_pos.2 hρ0) 2 |>.trans_eq (sq_abs ρ))
      (pow_pos (abs_pos.2 hσ) 2 |>.trans_eq (sq_abs σε))) (by linarith)
  have := Real.exp_lt_exp.2 hpos
  rwa [Real.exp_zero] at this

/-- **AKMM, footnote 44**, p. 903: along a differentiable iso-moment curve
`λ₁ = g(λ₀)` with `X(λ₀, g(λ₀)) = X̄` near `λ₀`, where `X` is differentiable with
`∂X/∂λ₁ ≠ 0`, the slope is `g′(λ₀) = −(∂X/∂λ₀)/(∂X/∂λ₁)`. -/
theorem fn_44 {X : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {g : ℝ → ℝ} {l0 g' Xbar : ℝ}
    (hX : HasFDerivAt X L (l0, g l0)) (hg : HasDerivAt g g' l0)
    (hlev : ∀ᶠ l in 𝓝 l0, X (l, g l) = Xbar) (h1 : L (0, 1) ≠ 0) :
    g' = -(L (1, 0) / L (0, 1)) := by
  have hc := HasFDerivAt.comp_hasDerivAt (f := fun l => (l, g l)) l0 hX
    ((hasDerivAt_id' l0).prodMk hg)
  have hconst : HasDerivAt (fun l => X (l, g l)) 0 l0 :=
    (hasDerivAt_const l0 Xbar).congr_of_eventuallyEq (hlev.mono fun l h => h)
  have h0 := hc.unique hconst
  have : ((1, g') : ℝ × ℝ) = (1 : ℝ) • ((1 : ℝ), (0 : ℝ)) + g' • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, one_mul] at h0
  field_simp
  linarith

/-- **AKMM, footnote 44**, p. 903, existence: if the moment function `X(λ₀, λ₁)` has partial
derivatives `X₀, X₁` near `(λ₀, λ₁)`, continuous there, with `X₁ ≠ 0` at the point, then the
implicit function theorem gives a curve `λ₁ = g(λ₀)` through the point on which `X` is constant
near `λ₀`, differentiable with slope `−X₀/X₁`. -/
theorem fn_44_exists {X X0 X1 : ℝ → ℝ → ℝ} {u : ℝ × ℝ}
    (d0 : ∀ᶠ w in 𝓝 u, HasDerivAt (X · w.2) (X0 w.1 w.2) w.1)
    (d1 : ∀ᶠ w in 𝓝 u, HasDerivAt (X w.1 ·) (X1 w.1 w.2) w.2)
    (c0 : ContinuousAt (Function.uncurry X0) u) (c1 : ContinuousAt (Function.uncurry X1) u)
    (h1 : X1 u.1 u.2 ≠ 0) :
    ∃ g : ℝ → ℝ, Tendsto g (𝓝 u.1) (𝓝 u.2) ∧ (∀ᶠ l in 𝓝 u.1, X l (g l) = X u.1 u.2) ∧
      HasDerivAt g (-(X0 u.1 u.2 / X1 u.1 u.2)) u.1 := by
  set f₁ : ℝ → ℝ → (ℝ →L[ℝ] ℝ) := fun a b => X0 a b • (1 : ℝ →L[ℝ] ℝ) with hf₁
  set f₂ : ℝ → ℝ → (ℝ →L[ℝ] ℝ) := fun a b => X1 a b • (1 : ℝ →L[ℝ] ℝ) with hf₂
  have df₁ : ∀ᶠ w in 𝓝 u, HasFDerivAt (X · w.2) (f₁ w.1 w.2) w.1 := by
    filter_upwards [d0] with w hw
    rw [hf₁]
    simp only
    rw [← ObstfeldRogoff.CapitalMarketImperfections.DebtOverhangLaffer.toSpanSingleton_eq_smul]
    exact hw.hasFDerivAt
  have df₂ : ∀ᶠ w in 𝓝 u, HasFDerivAt (X w.1 ·) (f₂ w.1 w.2) w.2 := by
    filter_upwards [d1] with w hw
    rw [hf₂]
    simp only
    rw [← ObstfeldRogoff.CapitalMarketImperfections.DebtOverhangLaffer.toSpanSingleton_eq_smul]
    exact hw.hasFDerivAt
  have cf₁ : ContinuousAt ↿f₁ u := c0.smul continuousAt_const
  have cf₂ : ContinuousAt ↿f₂ u := c1.smul continuousAt_const
  have if₂ : (f₂ u.1 u.2).IsInvertible :=
    ObstfeldRogoff.CapitalMarketImperfections.DebtOverhangLaffer.smul_one_isInvertible h1
  set g := implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂
  have hten := tendsto_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂
  have hlev := eventually_apply_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂
  have hgd := (hasStrictFDerivAt_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂).hasFDerivAt
    |>.hasDerivAt
  refine ⟨g, hten, hlev, ?_⟩
  -- identify the derivative through `fn_44`
  have hg0 : g u.1 = u.2 := by
    have := (eventually_apply_eq_iff_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂).self_of_nhds
    exact this.1 rfl
  have hXd : HasFDerivAt (Function.uncurry X)
      ((f₁ u.1 u.2).coprod (f₂ u.1 u.2)) (u.1, g u.1) := by
    rw [hg0]
    exact (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂).hasFDerivAt
  have hlev' : ∀ᶠ l in 𝓝 u.1, Function.uncurry X (l, g l) = X u.1 u.2 := hlev
  have hne : ((f₁ u.1 u.2).coprod (f₂ u.1 u.2)) (0, 1) ≠ 0 := by
    simp [hf₂, h1]
  have hval : (-(f₂ u.1 u.2).inverse ∘SL f₁ u.1 u.2) 1 = -(X0 u.1 u.2 / X1 u.1 u.2) := by
    rw [fn_44 hXd hgd hlev' hne]
    simp [hf₁, hf₂]
  rw [← hval]
  exact hgd

end AKMM.SovereignDefault

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Existence and uniqueness of the Markov perfect equilibrium with one-period debt

AKMM, Appendix 24.A.1, p. 901 ("Uniqueness"): "Auclert and Rognlie (2016) and Aguiar and
Amador (2019) show that in versions of the model with one-period bonds (i.e., when `δ = 1`), a
unique equilibrium exists. Furthermore, Aguiar and Amador (2019) show that the model can be
recast in a formulation that satisfies Blackwell's sufficient conditions." The book cites the
result without proof; this module proves it (beyond the text).

**Setting** (departure D10). The book's quantitative model of §24.4 with one-period debt
(`δ = 1`), finitely many income states (Markov matrix `P`), risk-neutral lenders with
`r > 0`, permanent exclusion after default (`ψ = 0`, the original Eaton–Gersovitz model) and a
*continuum* of debt levels: the sovereign may choose any `B′ ≤ B̄` (a borrowing limit
`B̄ ≥ 0`; saving, `B′ < 0`, is allowed), and states `B` range over `ℝ`. Utility `u : ℝ → ℝ`
is nondecreasing and uniformly continuous; for existence it is also satiated
(`u(c) = u(c̄)` for `c ≥ c̄`). The default cost is nonnegative, `φ(Y) ≥ 0`.

* The equilibrium (`IsOneMPE`) is the book's definition (§24.4.3, (24.9)–(24.12), (a)–(c)) at
  `δ = 1`, `ψ = 0`, with (24.11) a maximum over `B′ ≤ B̄` attained by the borrowing rule and
  values in the space of bounded functions.
* **Replication** (Auclert–Rognlie): if every debt the first price schedule lets the sovereign
  repay, the second lets it repay after a debt reduction `x`, then a sovereign facing the
  second schedule with debt `B − x/(1 + r)` does at least as well as one facing the first with
  debt `B` (`ue_replication`, with the revenue bound `ue_revenue`).
* **Uniqueness** (`ue_mpe_unique`): any two equilibria have the same values, default rule and
  prices. Iterating the replication shrinks the debt gap by `1/(1 + r)` each step.
* **Existence** (`ue_mpe_exists`): the debt capacities `b̄(Y)` (the largest debt repaid at
  income `Y`) are the fixed point of a map on `ℝ^Y` that is a contraction of modulus
  `1/(1 + r)` (the Blackwell recast; `ue_cutoff_lipschitz`). For a capacity vector the price
  is `q(B′, Y) = (1 + r)⁻¹ Pr(B′ ≤ b̄(Y′) | Y)`, the sovereign's Bellman equation is solved by
  monotone iteration (`ue_fixed_point`, Blackwell's monotonicity and discounting on bounded
  functions of an arbitrary state space), and at the fixed point the optimal borrowing exists
  because the objective is upper semicontinuous in `B′` and satiation makes very large savings
  useless (`ue_attain`).
* A concrete economy satisfying every hypothesis, with its unique equilibrium
  (`ue_example_exists_unique`).
-/

namespace AKMM.SovereignDefault

open Finset SargentStachurski.RecursiveDecisionProcesses

/-- The one-period-debt economy with a continuum of debt levels (departure D10): income levels
`inc` with Markov matrix `P`, utility `u`, default cost `φ`, discount factor `β ∈ [0, 1)`, the
lenders' rate `r > 0` and the borrowing limit `B̄ ≥ 0`. -/
structure UEModel (Y : Type*) [Fintype Y] where
  /-- Income levels. -/
  inc : Y → ℝ
  /-- The income transition matrix. -/
  P : Matrix Y Y ℝ
  /-- `P` is a Markov matrix. -/
  markov : IsMarkov P
  /-- Utility. -/
  u : ℝ → ℝ
  /-- The income cost of default. -/
  φ : ℝ → ℝ
  /-- The discount factor. -/
  β : ℝ
  /-- `β ≥ 0`. -/
  β_nonneg : 0 ≤ β
  /-- `β < 1`. -/
  β_lt_one : β < 1
  /-- The lenders' risk-free rate. -/
  r : ℝ
  /-- `r > 0`. -/
  r_pos : 0 < r
  /-- The borrowing limit `B̄`. -/
  bmax : ℝ
  /-- `B̄ ≥ 0`. -/
  bmax_nonneg : 0 ≤ bmax

/-- **Blackwell's sufficient conditions on an arbitrary state space** (monotone iteration): if
`T` maps functions with values in `[m, K]` into themselves, is monotone and discounts constants,
`T(f + k) ≤ Tf + βk`, then `T` has a fixed point with values in `[m, K]`. The iterates from the
constants `m` and `K` increase and decrease, are `β^n(K − m)` apart, and the supremum of the
increasing sequence is the fixed point. No metric on the function space is needed. -/
theorem ue_fixed_point {α γ : Type*} (T : (α → γ → ℝ) → α → γ → ℝ) {β m K : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hmK : m ≤ K)
    (hmono : ∀ f g : α → γ → ℝ, (∀ a c, m ≤ f a c) → (∀ a c, g a c ≤ K + (K - m)) →
      (∀ a c, f a c ≤ g a c) → ∀ a c, T f a c ≤ T g a c)
    (hdisc : ∀ (f : α → γ → ℝ) (k : ℝ), (∀ a c, m ≤ f a c ∧ f a c ≤ K) → 0 ≤ k →
      ∀ a c, T (fun a c => f a c + k) a c ≤ T f a c + β * k)
    (hbox : ∀ f : α → γ → ℝ, (∀ a c, m ≤ f a c ∧ f a c ≤ K) → ∀ a c, m ≤ T f a c ∧ T f a c ≤ K) :
    ∃ V : α → γ → ℝ, (∀ a c, T V a c = V a c) ∧ ∀ a c, m ≤ V a c ∧ V a c ≤ K := by
  set L : ℕ → α → γ → ℝ := fun n => T^[n] (fun _ _ => m) with hLdef
  set U : ℕ → α → γ → ℝ := fun n => T^[n] (fun _ _ => K) with hUdef
  have hLs : ∀ n, L (n + 1) = T (L n) := fun n => Function.iterate_succ_apply' T n _
  have hUs : ∀ n, U (n + 1) = T (U n) := fun n => Function.iterate_succ_apply' T n _
  have hL0 : L 0 = fun _ _ => m := rfl
  have hU0 : U 0 = fun _ _ => K := rfl
  have hKm : 0 ≤ K - m := by linarith
  have hL : ∀ n a c, m ≤ L n a c ∧ L n a c ≤ K := by
    intro n
    induction n with
    | zero => intro a c; rw [hL0]; exact ⟨le_rfl, hmK⟩
    | succ n ih => intro a c; rw [hLs]; exact hbox _ ih a c
  have hU : ∀ n a c, m ≤ U n a c ∧ U n a c ≤ K := by
    intro n
    induction n with
    | zero => intro a c; rw [hU0]; exact ⟨hmK, le_rfl⟩
    | succ n ih => intro a c; rw [hUs]; exact hbox _ ih a c
  have hLmono : ∀ n a c, L n a c ≤ L (n + 1) a c := by
    intro n
    induction n with
    | zero => intro a c; rw [hL0]; exact (hL 1 a c).1
    | succ n ih =>
      intro a c
      rw [hLs (n + 1)]
      conv_lhs => rw [hLs n]
      exact hmono _ _ (fun a c => (hL n a c).1) (fun a c => by linarith [(hL (n + 1) a c).2])
        ih a c
  have hUanti : ∀ n a c, U (n + 1) a c ≤ U n a c := by
    intro n
    induction n with
    | zero => intro a c; rw [hU0]; exact (hU 1 a c).2
    | succ n ih =>
      intro a c
      rw [hUs (n + 1)]
      conv_rhs => rw [hUs n]
      exact hmono _ _ (fun a c => (hU (n + 1) a c).1) (fun a c => by linarith [(hU n a c).2])
        ih a c
  have hLU : ∀ n a c, L n a c ≤ U n a c := by
    intro n
    induction n with
    | zero => intro a c; rw [hL0, hU0]; exact hmK
    | succ n ih =>
      intro a c
      rw [hLs, hUs]
      exact hmono _ _ (fun a c => (hL n a c).1) (fun a c => by linarith [(hU n a c).2]) ih a c
  have hgap : ∀ n a c, U n a c ≤ L n a c + β ^ n * (K - m) := by
    intro n
    induction n with
    | zero => intro a c; rw [hL0, hU0]; simp
    | succ n ih =>
      intro a c
      have hpow : β ^ n ≤ 1 := pow_le_one₀ hβ0 hβ1.le
      have hk : 0 ≤ β ^ n * (K - m) := mul_nonneg (pow_nonneg hβ0 n) hKm
      rw [hUs, hLs]
      calc T (U n) a c ≤ T (fun a c => L n a c + β ^ n * (K - m)) a c :=
            hmono _ _ (fun a c => (hU n a c).1)
              (fun a c => by nlinarith [(hL n a c).2]) ih a c
        _ ≤ T (L n) a c + β * (β ^ n * (K - m)) := hdisc _ _ (hL n) hk a c
        _ = T (L n) a c + β ^ (n + 1) * (K - m) := by ring
  have hbdd : ∀ a c, BddAbove (Set.range fun n => L n a c) := fun a c =>
    ⟨K, by rintro _ ⟨n, rfl⟩; exact (hL n a c).2⟩
  set V : α → γ → ℝ := fun a c => ⨆ n, L n a c with hVdef
  have hLV : ∀ n a c, L n a c ≤ V a c := fun n a c => le_ciSup (hbdd a c) n
  have hVU : ∀ n a c, V a c ≤ U n a c := by
    intro n a c
    refine ciSup_le fun k => ?_
    have hLm : Monotone fun n => L n a c := monotone_nat_of_le_succ fun n => hLmono n a c
    have hUa : Antitone fun n => U n a c := antitone_nat_of_succ_le fun n => hUanti n a c
    calc L k a c ≤ L (max k n) a c := hLm (le_max_left k n)
      _ ≤ U (max k n) a c := hLU _ a c
      _ ≤ U n a c := hUa (le_max_right k n)
  have hVbox : ∀ a c, m ≤ V a c ∧ V a c ≤ K := fun a c =>
    ⟨(hL 0 a c).1.trans (hLV 0 a c), (hVU 0 a c).trans (hU 0 a c).2⟩
  refine ⟨V, fun a c => le_antisymm ?_ ?_, hVbox⟩
  · have hle : ∀ n, T V a c ≤ V a c + β ^ n * (K - m) := fun n =>
      calc T V a c ≤ T (U n) a c :=
            hmono _ _ (fun a c => (hVbox a c).1) (fun a c => by linarith [(hU n a c).2])
              (hVU n) a c
        _ = U (n + 1) a c := by rw [hUs]
        _ ≤ U n a c := hUanti n a c
        _ ≤ L n a c + β ^ n * (K - m) := hgap n a c
        _ ≤ V a c + β ^ n * (K - m) := by linarith [hLV n a c]
    have ht : Filter.Tendsto (fun n : ℕ => V a c + β ^ n * (K - m)) Filter.atTop
        (nhds (V a c + 0 * (K - m))) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const _).const_add _
    rw [zero_mul, add_zero] at ht
    exact ge_of_tendsto' ht hle
  · refine ciSup_le fun n => ?_
    calc L n a c ≤ L (n + 1) a c := hLmono n a c
      _ = T (L n) a c := by rw [hLs]
      _ ≤ T V a c := hmono _ _ (fun a c => (hL n a c).1)
          (fun a c => by linarith [(hVbox a c).2]) (fun a c => hLV n a c) a c

variable {Y : Type*} [Fintype Y]

/-- Expectations under a Markov row are bounded by bounds on the integrand. -/
theorem ue_sum_le {P : Matrix Y Y ℝ} (hP : IsMarkov P) {f : Y → ℝ} {K : ℝ} (h : ∀ j, f j ≤ K)
    (y : Y) : ∑ j, P y j * f j ≤ K :=
  calc ∑ j, P y j * f j ≤ ∑ j, P y j * K :=
        sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j) (hP.nonneg y j)
    _ = K := by rw [← sum_mul, hP.rowsum, one_mul]

/-- Expectations under a Markov row are bounded below by lower bounds on the integrand. -/
theorem ue_le_sum {P : Matrix Y Y ℝ} (hP : IsMarkov P) {f : Y → ℝ} {K : ℝ} (h : ∀ j, K ≤ f j)
    (y : Y) : K ≤ ∑ j, P y j * f j :=
  calc K = ∑ j, P y j * K := by rw [← sum_mul, hP.rowsum, one_mul]
    _ ≤ ∑ j, P y j * f j := sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j) (hP.nonneg y j)

/-- Expectations under a Markov row are monotone. -/
theorem ue_sum_mono {P : Matrix Y Y ℝ} (hP : IsMarkov P) {f g : Y → ℝ} (h : ∀ j, f j ≤ g j)
    (y : Y) : ∑ j, P y j * f j ≤ ∑ j, P y j * g j :=
  sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j) (hP.nonneg y j)

/-- Expectations under a Markov row shift with constants. -/
theorem ue_sum_add {P : Matrix Y Y ℝ} (hP : IsMarkov P) (f : Y → ℝ) (c : ℝ) (y : Y) :
    ∑ j, P y j * (f j + c) = ∑ j, P y j * f j + c := by
  simp only [mul_add, sum_add_distrib, ← sum_mul, hP.rowsum, one_mul]

namespace UEModel

variable (M : UEModel Y)

/-- AKMM, (24.12) at `δ = 1`: the price `q(B′, Y) = (1 + r)⁻¹ Σ_j P(Y, j) a(B′, j)` given the
repayment indicator (or probability) `a = 1 − D̂`. -/
noncomputable def price (a : ℝ → Y → ℝ) (b' : ℝ) (y : Y) : ℝ :=
  (1 + M.r)⁻¹ * ∑ j, M.P y j * a b' j

/-- AKMM, (24.11) at `δ = 1`: the objective `u(Y − B + q(B′, Y)B′) + βE V(B′, Y′)` of the
repaying sovereign with debt `B` choosing `B′`. -/
def obj (q V : ℝ → Y → ℝ) (b : ℝ) (y : Y) (b' : ℝ) : ℝ :=
  M.u (M.inc y - b + q b' y * b') + M.β * ∑ j, M.P y j * V b' j

/-- AKMM, (24.10) at `ψ = 0`: the right-hand side `u(Y − φ(Y)) + βE V^D(Y′)`. -/
def defaultRHS (VD : Y → ℝ) (y : Y) : ℝ :=
  M.u (M.inc y - M.φ (M.inc y)) + M.β * ∑ j, M.P y j * VD j

end UEModel

variable (M : UEModel Y) (V VR : ℝ → Y → ℝ) (VD : Y → ℝ) (D : ℝ → Y → ℝ) (Bh : ℝ → Y → ℝ)
  (q : ℝ → Y → ℝ) in
/-- **AKMM, §24.4.3**, pp. 744–745, Markov perfect equilibrium with one-period debt (`δ = 1`),
permanent exclusion (`ψ = 0`) and a continuum of debt levels `B′ ≤ B̄` (departure D10): bounded
values `V`, `V^R`, `V^D`, a default rule `D̂`, a borrowing rule `B̂` and a price `q` with
(a) (24.9)–(24.11), (b) (24.12), (c) `D̂` and `B̂` optimal. -/
structure IsOneMPE : Prop where
  /-- Values lie in the space of bounded functions. -/
  bdd : ∃ K, ∀ b y, V b y ≤ K
  /-- (a) (24.9). -/
  eq_24_9 : ∀ b y, V b y = max (VD y) (VR b y)
  /-- (a) (24.10) with `ψ = 0`. -/
  eq_24_10 : ∀ y, VD y = M.defaultRHS VD y
  /-- (a) (24.11): `V^R` is an upper bound of the objective over `B′ ≤ B̄` ... -/
  eq_24_11 : ∀ b y b', b' ≤ M.bmax → M.obj q V b y b' ≤ VR b y
  /-- (b) (24.12) with `δ = 1`: `q(B′, Y) = (1 + r)⁻¹ E[1 − D̂(B′, Y′)]`. -/
  eq_24_12 : ∀ b' y, b' ≤ M.bmax → q b' y = (1 + M.r)⁻¹ * ∑ j, M.P y j * (1 - D b' j)
  /-- (c) the default rule is optimal (ties repaid). -/
  default_opt : ∀ b y, D b y = if VR b y < VD y then 1 else 0
  /-- The borrowing rule is feasible. -/
  borrow_le : ∀ b y, Bh b y ≤ M.bmax
  /-- (c) ... and the borrowing rule attains it, so (24.11) is a maximum. -/
  borrow_opt : ∀ b y, M.obj q V b y (Bh b y) = VR b y

/-- The repayment indicator of a vector of debt capacities `b̄`: `1{B′ ≤ b̄(Y′)}`. -/
noncomputable def ue_thr {Y : Type*} (bt : Y → ℝ) (b' : ℝ) (j : Y) : ℝ :=
  if b' ≤ bt j then 1 else 0

namespace UEModel

variable (M : UEModel Y)

/-- The price lies in `[0, (1 + r)⁻¹]` when the repayment indicator lies in `[0, 1]`. -/
theorem ue_price_mem {a : ℝ → Y → ℝ} {b' : ℝ} (ha : ∀ j, 0 ≤ a b' j ∧ a b' j ≤ 1) (y : Y) :
    0 ≤ M.price a b' y ∧ M.price a b' y ≤ (1 + M.r)⁻¹ := by
  have hr : 0 < (1 + M.r)⁻¹ := inv_pos.2 (by linarith [M.r_pos])
  unfold price
  exact ⟨mul_nonneg hr.le (ue_le_sum M.markov (fun j => (ha j).1) y),
    mul_le_of_le_one_right hr.le (ue_sum_le M.markov (fun j => (ha j).2) y)⟩

/-- Without default risk the price is the risk-free price `(1 + r)⁻¹`. -/
theorem ue_price_one {a : ℝ → Y → ℝ} {b' : ℝ} (ha : ∀ j, a b' j = 1) (y : Y) :
    M.price a b' y = (1 + M.r)⁻¹ := by
  unfold price
  simp only [ha, mul_one, M.markov.rowsum]

/-- The price is monotone in the repayment indicator. -/
theorem ue_price_mono {a a' : ℝ → Y → ℝ} {b' b'' : ℝ} (h : ∀ j, a b' j ≤ a' b'' j) (y : Y) :
    M.price a b' y ≤ M.price a' b'' y :=
  mul_le_mul_of_nonneg_left (ue_sum_mono M.markov h y) (inv_nonneg.2 (by linarith [M.r_pos]))

/-- **The revenue bound.** If every debt `B′` repaid under `a₁` is repaid under `a₂` after a
reduction `x ≥ 0`, and debt `B′ ≤ 0` is always repaid, then issuing `B′ − x` at the second price
raises at least the revenue of issuing `B′` at the first, less `x/(1 + r)`. -/
theorem ue_revenue {a₁ a₂ q₁ q₂ : ℝ → Y → ℝ} {x : ℝ} (hx : 0 ≤ x)
    (hq₁ : ∀ b' y, b' ≤ M.bmax → q₁ b' y = M.price a₁ b' y)
    (hq₂ : ∀ b' y, b' ≤ M.bmax → q₂ b' y = M.price a₂ b' y)
    (ha₁ : ∀ b' j, 0 ≤ a₁ b' j ∧ a₁ b' j ≤ 1)
    (hneg₁ : ∀ b' j, b' ≤ 0 → a₁ b' j = 1) (hneg₂ : ∀ b' j, b' ≤ 0 → a₂ b' j = 1)
    (hdom : ∀ b' j, b' ≤ M.bmax → a₁ b' j ≤ a₂ (b' - x) j) {b' : ℝ} (hb' : b' ≤ M.bmax)
    (y : Y) : q₁ b' y * b' - x * (1 + M.r)⁻¹ ≤ q₂ (b' - x) y * (b' - x) := by
  rw [hq₁ b' y hb', hq₂ (b' - x) y (by linarith)]
  have hp1 := M.ue_price_mem (fun j => ha₁ b' j) y
  have hp12 : M.price a₁ b' y ≤ M.price a₂ (b' - x) y :=
    M.ue_price_mono (fun j => hdom b' j hb') y
  rcases le_or_gt 0 (b' - x) with hpos | hneg
  · nlinarith [mul_le_mul_of_nonneg_right hp12 hpos, mul_le_mul_of_nonneg_right hp1.2 hx]
  · rw [M.ue_price_one (fun j => hneg₂ (b' - x) j hneg.le) y]
    rcases le_or_gt 0 b' with hb0 | hb0
    · nlinarith [mul_le_mul_of_nonneg_right hp1.2 hb0]
    · rw [M.ue_price_one (fun j => hneg₁ b' j hb0.le) y]
      linarith

/-- **The replication argument** (Auclert–Rognlie 2016). Let `V^R₁` be the supremum of the
objective at the prices `q₁` (approximated by feasible choices) and `V^R₂` an upper bound of the
objective at `q₂`, with `V_k = max(V^D, V^R_k)`, `V₁` bounded and `V₂` nonincreasing in debt. If
issuing `B′ − x` at `q₂` raises the revenue of `B′` at `q₁` less `g ≤ x`, then a sovereign with
debt `B − g` facing `q₂` does at least as well as one with debt `B` facing `q₁`:
`V^R₁(B, Y) ≤ V^R₂(B − g, Y)`. The proof bounds `e = sup (V₁(B) − V₂(B − g))` by `max(0, βe)`. -/
theorem ue_replication (hu : Monotone M.u) {q₁ q₂ V₁ V₂ VR₁ VR₂ : ℝ → Y → ℝ} {VD : Y → ℝ}
    {x g : ℝ} (hx : 0 ≤ x) (hgx : g ≤ x)
    (hV₁ : ∀ b y, V₁ b y = max (VD y) (VR₁ b y)) (hV₂ : ∀ b y, V₂ b y = max (VD y) (VR₂ b y))
    (hK : ∃ K, ∀ b y, V₁ b y ≤ K)
    (hsup : ∀ b y ε, 0 < ε → ∃ b', b' ≤ M.bmax ∧ VR₁ b y ≤ M.obj q₁ V₁ b y b' + ε)
    (hle : ∀ b y b', b' ≤ M.bmax → M.obj q₂ V₂ b y b' ≤ VR₂ b y)
    (hanti : ∀ b b' y, b ≤ b' → V₂ b' y ≤ V₂ b y)
    (hrev : ∀ b' y, b' ≤ M.bmax → q₁ b' y * b' - g ≤ q₂ (b' - x) y * (b' - x)) (b : ℝ)
    (y : Y) : VR₁ b y ≤ VR₂ (b - g) y := by
  obtain ⟨K, hK⟩ := hK
  have hV₂low : ∀ b j, -‖VD‖ ≤ V₂ b j := fun b j => by
    rw [hV₂]
    have h1 := norm_le_pi_norm VD j
    rw [Real.norm_eq_abs] at h1
    linarith [neg_abs_le (VD j), le_max_left (VD j) (VR₂ b j)]
  set e := ⨆ p : ℝ × Y, (V₁ p.1 p.2 - V₂ (p.1 - g) p.2) with he
  have hbdd : BddAbove (Set.range fun p : ℝ × Y => V₁ p.1 p.2 - V₂ (p.1 - g) p.2) :=
    ⟨K + ‖VD‖, by rintro _ ⟨p, rfl⟩; linarith [hK p.1 p.2, hV₂low (p.1 - g) p.2]⟩
  have hle_e : ∀ b j, V₁ b j ≤ V₂ (b - g) j + e := fun b j => by
    have h1 := le_ciSup hbdd (b, j)
    simp only at h1
    linarith
  have step1 : ∀ b y, VR₁ b y ≤ VR₂ (b - g) y + M.β * e := by
    intro b y
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨b', hb', hε'⟩ := hsup b y ε hε
    have hc : M.inc y - b + q₁ b' y * b' ≤ M.inc y - (b - g) + q₂ (b' - x) y * (b' - x) := by
      linarith [hrev b' y hb']
    have hs : ∑ j, M.P y j * V₁ b' j ≤ ∑ j, M.P y j * V₂ (b' - x) j + e := by
      rw [← ue_sum_add M.markov]
      exact ue_sum_mono M.markov (fun j => (hle_e b' j).trans
        (by linarith [hanti (b' - x) (b' - g) j (by linarith)])) y
    have h1 : M.obj q₁ V₁ b y b' ≤ M.obj q₂ V₂ (b - g) y (b' - x) + M.β * e := by
      unfold UEModel.obj
      nlinarith [hu hc, mul_le_mul_of_nonneg_left hs M.β_nonneg]
    have h2 := hle (b - g) y (b' - x) (by linarith)
    linarith
  have step2 : e ≤ max 0 (M.β * e) := by
    have : Nonempty Y := ⟨y⟩
    refine ciSup_le fun p => ?_
    rw [hV₁, hV₂]
    have h1 := step1 p.1 p.2
    have hA : max (VD p.2) (VR₁ p.1 p.2) ≤
        max (VD p.2) (VR₂ (p.1 - g) p.2) + max 0 (M.β * e) :=
      max_le (by linarith [le_max_left (VD p.2) (VR₂ (p.1 - g) p.2), le_max_left 0 (M.β * e)])
        (by linarith [le_max_right (VD p.2) (VR₂ (p.1 - g) p.2), le_max_right 0 (M.β * e)])
    linarith
  have step3 : e ≤ 0 := by
    by_contra hcon
    have hpos : 0 < e := lt_of_not_ge hcon
    have hbe : 0 ≤ M.β * e := mul_nonneg M.β_nonneg hpos.le
    rw [max_eq_right hbe] at step2
    nlinarith [M.β_lt_one]
  linarith [step1 b y, mul_nonpos_of_nonneg_of_nonpos M.β_nonneg step3]

/-- **Uniform continuity of the repayment value in debt.** If `V^R` is the supremum of the
objective over `B′ ≤ B̄` and `u` is uniformly continuous, then reducing debt by less than `η`
raises `V^R` by at most `ε`. -/
theorem ue_modulus (huc : UniformContinuous M.u) {q V VR : ℝ → Y → ℝ}
    (hsup : ∀ b y ε, 0 < ε → ∃ b', b' ≤ M.bmax ∧ VR b y ≤ M.obj q V b y b' + ε)
    (hle : ∀ b y b', b' ≤ M.bmax → M.obj q V b y b' ≤ VR b y) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ b y h, 0 ≤ h → h < η → VR (b - h) y ≤ VR b y + ε := by
  obtain ⟨η, hη, H⟩ := Metric.uniformContinuous_iff.1 huc (ε / 2) (half_pos hε)
  refine ⟨η, hη, fun b y h h0 hη' => ?_⟩
  obtain ⟨b', hb', hb'ε⟩ := hsup (b - h) y (ε / 2) (half_pos hε)
  have hd : dist (M.inc y - (b - h) + q b' y * b') (M.inc y - b + q b' y * b') < η := by
    rw [Real.dist_eq]
    have : M.inc y - (b - h) + q b' y * b' - (M.inc y - b + q b' y * b') = h := by ring
    rw [this, abs_of_nonneg h0]
    exact hη'
  have hu := H hd
  rw [Real.dist_eq] at hu
  have hu' := (abs_lt.1 hu).2
  have h2 := hle b y b' hb'
  unfold UEModel.obj at hb'ε h2
  linarith

/-- **`V^R` is nonincreasing in debt** when it is the supremum of the objective. -/
theorem ue_VR_antitone (hu : Monotone M.u) {q V VR : ℝ → Y → ℝ}
    (hsup : ∀ b y ε, 0 < ε → ∃ b', b' ≤ M.bmax ∧ VR b y ≤ M.obj q V b y b' + ε)
    (hle : ∀ b y b', b' ≤ M.bmax → M.obj q V b y b' ≤ VR b y) {b b'' : ℝ} (hbb : b ≤ b'')
    (y : Y) : VR b'' y ≤ VR b y := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨b', hb', hb'ε⟩ := hsup b'' y ε hε
  have h1 : M.obj q V b'' y b' ≤ M.obj q V b y b' := by
    unfold UEModel.obj
    have := hu (show M.inc y - b'' + q b' y * b' ≤ M.inc y - b + q b' y * b' by linarith)
    linarith
  linarith [hle b y b' hb']

/-- **Debt `B ≤ 0` is always repaid**: with `φ ≥ 0` and `u` nondecreasing, keeping `B′ = 0` is
worth at least `V^D(Y)`. -/
theorem ue_repay_nonpos (hu : Monotone M.u) (hφ : ∀ y, 0 ≤ M.φ (M.inc y))
    {q V VR : ℝ → Y → ℝ} {VD : Y → ℝ}
    (hle : ∀ b y b', b' ≤ M.bmax → M.obj q V b y b' ≤ VR b y) (hV : ∀ b y, VD y ≤ V b y)
    (hVD : ∀ y, VD y = M.defaultRHS VD y) {b : ℝ} (hb : b ≤ 0) (y : Y) : VD y ≤ VR b y := by
  have h1 := hle b y 0 M.bmax_nonneg
  have h2 : M.u (M.inc y - M.φ (M.inc y)) ≤ M.u (M.inc y - b + q 0 y * 0) :=
    hu (by linarith [hφ y])
  have h3 := mul_le_mul_of_nonneg_left (ue_sum_mono M.markov (fun j => hV 0 j) y) M.β_nonneg
  rw [hVD y]
  unfold UEModel.obj at h1
  unfold UEModel.defaultRHS
  linarith

/-- AKMM, (24.10) at `ψ = 0`: the default value is unique. -/
theorem ue_VD_unique {VD₁ VD₂ : Y → ℝ} (h₁ : ∀ y, VD₁ y = M.defaultRHS VD₁ y)
    (h₂ : ∀ y, VD₂ y = M.defaultRHS VD₂ y) : VD₁ = VD₂ := by
  funext y
  have : Nonempty Y := ⟨y⟩
  obtain ⟨j₀, hj₀⟩ := Finite.exists_max fun j => |VD₁ j - VD₂ j|
  have hdiff : VD₁ j₀ - VD₂ j₀ = M.β * ∑ j, M.P j₀ j * (VD₁ j - VD₂ j) := by
    rw [h₁ j₀, h₂ j₀]
    unfold UEModel.defaultRHS
    simp only [mul_sub, sum_sub_distrib]
    ring
  have hs : |∑ j, M.P j₀ j * (VD₁ j - VD₂ j)| ≤ |VD₁ j₀ - VD₂ j₀| :=
    calc |∑ j, M.P j₀ j * (VD₁ j - VD₂ j)| ≤ ∑ j, |M.P j₀ j * (VD₁ j - VD₂ j)| :=
          abs_sum_le_sum_abs _ _
      _ = ∑ j, M.P j₀ j * |VD₁ j - VD₂ j| := by
          refine sum_congr rfl fun j _ => ?_
          rw [abs_mul, abs_of_nonneg (M.markov.nonneg j₀ j)]
      _ ≤ |VD₁ j₀ - VD₂ j₀| := ue_sum_le M.markov hj₀ j₀
  have hle : |VD₁ j₀ - VD₂ j₀| ≤ M.β * |VD₁ j₀ - VD₂ j₀| := by
    calc |VD₁ j₀ - VD₂ j₀| = M.β * |∑ j, M.P j₀ j * (VD₁ j - VD₂ j)| := by
          rw [hdiff, abs_mul, abs_of_nonneg M.β_nonneg]
      _ ≤ M.β * |VD₁ j₀ - VD₂ j₀| := mul_le_mul_of_nonneg_left hs M.β_nonneg
  have h0 : |VD₁ j₀ - VD₂ j₀| = 0 := by
    nlinarith [abs_nonneg (VD₁ j₀ - VD₂ j₀), M.β_lt_one]
  have hy := hj₀ y
  rw [h0] at hy
  have := abs_nonneg (VD₁ y - VD₂ y)
  have h' : |VD₁ y - VD₂ y| = 0 := le_antisymm hy this
  linarith [abs_eq_zero.1 h']

/-- In an equilibrium `V^R` is approximated by feasible choices (here attained by `B̂`). -/
theorem ue_mpe_sup {V VR : ℝ → Y → ℝ} {VD : Y → ℝ} {D Bh q : ℝ → Y → ℝ}
    (h : IsOneMPE M V VR VD D Bh q) (b : ℝ) (y : Y) (ε : ℝ) (hε : 0 < ε) :
    ∃ b', b' ≤ M.bmax ∧ VR b y ≤ M.obj q V b y b' + ε :=
  ⟨Bh b y, h.borrow_le b y, by rw [h.borrow_opt]; linarith⟩

/-- One direction of uniqueness: in two equilibria, `V^R₁ ≤ V^R₂`. The debt-reduction gap
`x_n = B̄(1 + r)^{−n}` makes the repayment sets nested, `D̂₁(B′) = 0 ⇒ D̂₂(B′ − x_n) = 0`; each
replication step shrinks it by `1/(1 + r)`; uniform continuity closes the gap. -/
theorem ue_mpe_VR_le (hu : Monotone M.u) (huc : UniformContinuous M.u)
    (hφ : ∀ y, 0 ≤ M.φ (M.inc y)) {V₁ VR₁ D₁ Bh₁ q₁ V₂ VR₂ D₂ Bh₂ q₂ : ℝ → Y → ℝ}
    {VD₁ VD₂ : Y → ℝ} (h₁ : IsOneMPE M V₁ VR₁ VD₁ D₁ Bh₁ q₁)
    (h₂ : IsOneMPE M V₂ VR₂ VD₂ D₂ Bh₂ q₂) (b : ℝ) (y : Y) : VR₁ b y ≤ VR₂ b y := by
  have hVD : VD₁ = VD₂ := M.ue_VD_unique h₁.eq_24_10 h₂.eq_24_10
  subst hVD
  set ρ : ℝ := (1 + M.r)⁻¹ with hρ
  have hr1 : 0 < 1 + M.r := by linarith [M.r_pos]
  have hρ0 : 0 < ρ := inv_pos.2 hr1
  have hρ1 : ρ < 1 := inv_lt_one_of_one_lt₀ (by linarith [M.r_pos])
  set a₁ : ℝ → Y → ℝ := fun b j => 1 - D₁ b j with ha₁
  set a₂ : ℝ → Y → ℝ := fun b j => 1 - D₂ b j with ha₂
  have hrep₁ : ∀ b j, VD₁ j ≤ VR₁ b j → a₁ b j = 1 := fun b j h => by
    simp only [ha₁, h₁.default_opt, not_lt.2 h, ↓reduceIte, sub_zero]
  have hrep₂ : ∀ b j, VD₁ j ≤ VR₂ b j → a₂ b j = 1 := fun b j h => by
    simp only [ha₂, h₂.default_opt, not_lt.2 h, ↓reduceIte, sub_zero]
  have hdef₁ : ∀ b j, VR₁ b j < VD₁ j → a₁ b j = 0 := fun b j h => by
    simp only [ha₁, h₁.default_opt, h, ↓reduceIte, sub_self]
  have hmem₁ : ∀ b j, 0 ≤ a₁ b j ∧ a₁ b j ≤ 1 := fun b j => by
    rcases lt_or_ge (VR₁ b j) (VD₁ j) with h | h
    · rw [hdef₁ b j h]; norm_num
    · rw [hrep₁ b j h]; norm_num
  have hmem₂ : ∀ b j, 0 ≤ a₂ b j ∧ a₂ b j ≤ 1 := fun b j => by
    simp only [ha₂, h₂.default_opt]
    split_ifs <;> norm_num
  have hneg₁ : ∀ b j, b ≤ 0 → a₁ b j = 1 := fun b j hb =>
    hrep₁ b j (M.ue_repay_nonpos hu hφ h₁.eq_24_11
      (fun b y => by rw [h₁.eq_24_9]; exact le_max_left _ _) h₁.eq_24_10 hb j)
  have hneg₂ : ∀ b j, b ≤ 0 → a₂ b j = 1 := fun b j hb =>
    hrep₂ b j (M.ue_repay_nonpos hu hφ h₂.eq_24_11
      (fun b y => by rw [h₂.eq_24_9]; exact le_max_left _ _) h₁.eq_24_10 hb j)
  have hq₁ : ∀ b' y, b' ≤ M.bmax → q₁ b' y = M.price a₁ b' y := fun b' y hb' =>
    h₁.eq_24_12 b' y hb'
  have hq₂ : ∀ b' y, b' ≤ M.bmax → q₂ b' y = M.price a₂ b' y := fun b' y hb' =>
    h₂.eq_24_12 b' y hb'
  have hanti₂ : ∀ b b' y, b ≤ b' → V₂ b' y ≤ V₂ b y := fun b b' y hbb => by
    rw [h₂.eq_24_9, h₂.eq_24_9]
    exact max_le_max le_rfl (M.ue_VR_antitone hu (M.ue_mpe_sup h₂) h₂.eq_24_11 hbb y)
  set xs : ℕ → ℝ := fun n => M.bmax * ρ ^ n with hxs
  have hx0 : ∀ n, 0 ≤ xs n := fun n => mul_nonneg M.bmax_nonneg (pow_nonneg hρ0.le n)
  have hstep : ∀ n, (∀ b' j, b' ≤ M.bmax → a₁ b' j ≤ a₂ (b' - xs n) j) →
      ∀ b y, VR₁ b y ≤ VR₂ (b - xs (n + 1)) y := by
    intro n hdom b y
    have hxs1 : xs (n + 1) = xs n * ρ := by simp only [hxs, pow_succ]; ring
    refine M.ue_replication hu (hx0 n) (by rw [hxs1]; nlinarith [hx0 n]) h₁.eq_24_9
      h₂.eq_24_9 h₁.bdd (M.ue_mpe_sup h₁) h₂.eq_24_11 hanti₂ (fun b' y hb' => ?_) b y
    rw [hxs1]
    exact M.ue_revenue (hx0 n) hq₁ hq₂ hmem₁ hneg₁ hneg₂ hdom hb' y
  have hdom : ∀ n, ∀ b' j, b' ≤ M.bmax → a₁ b' j ≤ a₂ (b' - xs n) j := by
    intro n
    induction n with
    | zero =>
      intro b' j hb'
      rw [hneg₂ _ j (by simp only [hxs, pow_zero, mul_one]; linarith)]
      exact (hmem₁ b' j).2
    | succ n ih =>
      intro b' j _
      rcases lt_or_ge (VR₁ b' j) (VD₁ j) with h | h
      · rw [hdef₁ b' j h]; exact (hmem₂ _ j).1
      · rw [hrep₁ b' j h, hrep₂ _ j (h.trans (hstep n ih b' j))]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨η, hη, hmod⟩ := M.ue_modulus huc (M.ue_mpe_sup h₂) h₂.eq_24_11 hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hη (by linarith [M.bmax_nonneg] :
    (0 : ℝ) < M.bmax + 1)) hρ1
  have hxn : xs (n + 1) < η := by
    have h1 : ρ ^ (n + 1) ≤ ρ ^ n := pow_le_pow_of_le_one hρ0.le hρ1.le (Nat.le_succ n)
    have h2 : M.bmax * ρ ^ n < η := by
      have := (lt_div_iff₀ (by linarith [M.bmax_nonneg] : (0 : ℝ) < M.bmax + 1)).1 hn
      nlinarith [pow_nonneg hρ0.le n, M.bmax_nonneg]
    simp only [hxs]
    nlinarith [M.bmax_nonneg]
  have h1 := hstep n (hdom n) b y
  have h2 := hmod b y (xs (n + 1)) (hx0 (n + 1)) hxn
  linarith

/-- **Uniqueness of the Markov perfect equilibrium with one-period debt** (Auclert–Rognlie
2016; Aguiar–Amador 2019; AKMM, p. 901, beyond the text): with `u` nondecreasing and uniformly
continuous, `φ ≥ 0`, `r > 0`, any two equilibria have the same value functions `V`, `V^R`,
`V^D`, the same default rule `D̂` and the same prices `q(B′, Y)` for `B′ ≤ B̄`. (The borrowing
rule is unique up to the choice among maximisers.) -/
theorem ue_mpe_unique (hu : Monotone M.u) (huc : UniformContinuous M.u)
    (hφ : ∀ y, 0 ≤ M.φ (M.inc y)) {V₁ VR₁ D₁ Bh₁ q₁ V₂ VR₂ D₂ Bh₂ q₂ : ℝ → Y → ℝ}
    {VD₁ VD₂ : Y → ℝ} (h₁ : IsOneMPE M V₁ VR₁ VD₁ D₁ Bh₁ q₁)
    (h₂ : IsOneMPE M V₂ VR₂ VD₂ D₂ Bh₂ q₂) :
    V₁ = V₂ ∧ VR₁ = VR₂ ∧ VD₁ = VD₂ ∧ D₁ = D₂ ∧ ∀ b' y, b' ≤ M.bmax → q₁ b' y = q₂ b' y := by
  have hVD : VD₁ = VD₂ := M.ue_VD_unique h₁.eq_24_10 h₂.eq_24_10
  have hVR : VR₁ = VR₂ := funext fun b => funext fun y =>
    le_antisymm (M.ue_mpe_VR_le hu huc hφ h₁ h₂ b y) (M.ue_mpe_VR_le hu huc hφ h₂ h₁ b y)
  have hD : D₁ = D₂ := funext fun b => funext fun y => by
    rw [h₁.default_opt, h₂.default_opt, hVR, hVD]
  refine ⟨funext fun b => funext fun y => by rw [h₁.eq_24_9, h₂.eq_24_9, hVR, hVD], hVR, hVD,
    hD, fun b' y hb' => by rw [h₁.eq_24_12 b' y hb', h₂.eq_24_12 b' y hb', hD]⟩

/-- The utility of a satiated nondecreasing `u` is bounded by its satiation level. -/
theorem ue_u_le (hu : Monotone M.u) {cbar : ℝ} (hsat : ∀ c, cbar ≤ c → M.u c = M.u cbar)
    (c : ℝ) : M.u c ≤ M.u cbar := by
  rcases le_total c cbar with h | h
  · exact hu h
  · rw [hsat c h]

/-- The objective is bounded above when `u` and the continuation value are. -/
theorem ue_obj_le {ub K : ℝ} (hub : ∀ c, M.u c ≤ ub) {q V : ℝ → Y → ℝ}
    (hV : ∀ b j, V b j ≤ K) (b : ℝ) (y : Y) (b' : ℝ) : M.obj q V b y b' ≤ ub + M.β * K := by
  unfold obj
  have := mul_le_mul_of_nonneg_left (ue_sum_le M.markov (fun j => hV b' j) y) M.β_nonneg
  linarith [hub (M.inc y - b + q b' y * b')]

/-- The value of repaying as the supremum of the objective over `B′ ≤ B̄`. -/
noncomputable def VRsup (q V : ℝ → Y → ℝ) (b : ℝ) (y : Y) : ℝ :=
  ⨆ b' : ℝ, M.obj q V b y (min b' M.bmax)

/-- The Bellman operator of (24.9) and (24.11) given `V^D` and the prices `q`. -/
noncomputable def bell (VD : Y → ℝ) (q V : ℝ → Y → ℝ) (b : ℝ) (y : Y) : ℝ :=
  max (VD y) (M.VRsup q V b y)

/-- The debt capacity at income `Y`: the largest debt in `[0, B̄]` that is repaid. -/
noncomputable def cutoff (VD : Y → ℝ) (q V : ℝ → Y → ℝ) (j : Y) : ℝ :=
  sSup {b | 0 ≤ b ∧ b ≤ M.bmax ∧ VD j ≤ M.VRsup q V b j}

/-- The family defining `V^R` is bounded above. -/
theorem ue_VRsup_bdd {ub K : ℝ} (hub : ∀ c, M.u c ≤ ub) {q V : ℝ → Y → ℝ}
    (hV : ∀ b j, V b j ≤ K) (b : ℝ) (y : Y) :
    BddAbove (Set.range fun b' : ℝ => M.obj q V b y (min b' M.bmax)) :=
  ⟨ub + M.β * K, by rintro _ ⟨b', rfl⟩; exact M.ue_obj_le hub hV b y _⟩

/-- `V^R` bounds the objective at every feasible `B′`. -/
theorem ue_VRsup_le {ub K : ℝ} (hub : ∀ c, M.u c ≤ ub) {q V : ℝ → Y → ℝ}
    (hV : ∀ b j, V b j ≤ K) (b : ℝ) (y : Y) {b' : ℝ} (hb' : b' ≤ M.bmax) :
    M.obj q V b y b' ≤ M.VRsup q V b y := by
  have := le_ciSup (M.ue_VRsup_bdd hub (q := q) hV b y) b'
  rwa [min_eq_left hb'] at this

/-- `V^R` is approximated by feasible choices. -/
theorem ue_VRsup_sup (q V : ℝ → Y → ℝ) (b : ℝ) (y : Y) (ε : ℝ) (hε : 0 < ε) :
    ∃ b', b' ≤ M.bmax ∧ M.VRsup q V b y ≤ M.obj q V b y b' + ε := by
  have h : M.VRsup q V b y - ε < M.VRsup q V b y := by linarith
  obtain ⟨b'', hb''⟩ := exists_lt_of_lt_ciSup h
  exact ⟨min b'' M.bmax, min_le_right _ _, by linarith⟩

/-- `V^R` is bounded above. -/
theorem ue_VRsup_ub {ub K : ℝ} (hub : ∀ c, M.u c ≤ ub) {q V : ℝ → Y → ℝ}
    (hV : ∀ b j, V b j ≤ K) (b : ℝ) (y : Y) : M.VRsup q V b y ≤ ub + M.β * K :=
  ciSup_le fun _ => M.ue_obj_le hub hV b y _

/-- AKMM, (24.10) at `ψ = 0`: a default value exists, bounded by `ū/(1 − β)`. -/
theorem ue_VD_exists {ub : ℝ} (hub : ∀ c, M.u c ≤ ub) :
    ∃ VD : Y → ℝ, (∀ y, VD y = M.defaultRHS VD y) ∧ ∀ y, VD y ≤ ub / (1 - M.β) := by
  have h1β : 0 < 1 - M.β := by linarith [M.β_lt_one]
  set K := ub / (1 - M.β) with hK
  set A := ‖fun y => M.u (M.inc y - M.φ (M.inc y))‖ with hA
  set m := min K (-A / (1 - M.β)) with hm
  have hKK : ub + M.β * K = K := by rw [hK]; field_simp; ring
  have hmA : m ≤ -A + M.β * m := by
    have h1 : m ≤ -A / (1 - M.β) := min_le_right _ _
    rw [le_div_iff₀ h1β] at h1
    linarith
  have hAy : ∀ y, -A ≤ M.u (M.inc y - M.φ (M.inc y)) := fun y => by
    have h1 := norm_le_pi_norm (fun y => M.u (M.inc y - M.φ (M.inc y))) y
    rw [Real.norm_eq_abs] at h1
    linarith [neg_abs_le (M.u (M.inc y - M.φ (M.inc y)))]
  obtain ⟨W, hW, hWb⟩ := ue_fixed_point (α := Unit) (γ := Y)
    (fun f _ y => M.defaultRHS (f ()) y) M.β_nonneg M.β_lt_one (min_le_left _ _)
    (fun f g _ _ hfg _ y => by
      unfold defaultRHS
      linarith [mul_le_mul_of_nonneg_left
        (ue_sum_mono M.markov (fun j => hfg () j) y) M.β_nonneg])
    (fun f k _ _ _ y => by
      simp only [defaultRHS, ue_sum_add M.markov]
      linarith)
    (fun f hf _ y => by
      unfold defaultRHS
      refine ⟨?_, ?_⟩
      · have := mul_le_mul_of_nonneg_left (ue_le_sum M.markov (fun j => (hf () j).1) y)
          M.β_nonneg
        linarith [hAy y]
      · have := mul_le_mul_of_nonneg_left (ue_sum_le M.markov (fun j => (hf () j).2) y)
          M.β_nonneg
        linarith [hub (M.inc y - M.φ (M.inc y))])
  exact ⟨fun y => W () y, fun y => (hW () y).symm, fun y => (hWb () y).2⟩

/-- AKMM, (24.9) and (24.11) for given prices `q`: a bounded solution `V` exists (Blackwell's
conditions on the bounded functions of `(B, Y) ∈ ℝ × Y`, `ue_fixed_point`). -/
theorem ue_sol_exists {ub : ℝ} (hub : ∀ c, M.u c ≤ ub) {VD : Y → ℝ}
    (hVD : ∀ y, VD y ≤ ub / (1 - M.β)) (q : ℝ → Y → ℝ) :
    ∃ V : ℝ → Y → ℝ, (∀ b y, M.bell VD q V b y = V b y) ∧
      ∀ b y, min (ub / (1 - M.β)) (-‖VD‖) ≤ V b y ∧ V b y ≤ ub / (1 - M.β) := by
  have h1β : 0 < 1 - M.β := by linarith [M.β_lt_one]
  set K := ub / (1 - M.β) with hK
  have hKK : ub + M.β * K = K := by rw [hK]; field_simp; ring
  have hmVD : ∀ y, min K (-‖VD‖) ≤ VD y := fun y => by
    have h1 := norm_le_pi_norm VD y
    rw [Real.norm_eq_abs] at h1
    exact (min_le_right _ _).trans (by linarith [neg_abs_le (VD y)])
  refine ue_fixed_point (M.bell VD q) M.β_nonneg M.β_lt_one (min_le_left _ _) ?_ ?_ ?_
  · intro f g _ hg hfg b y
    refine max_le_max le_rfl (ciSup_mono (M.ue_VRsup_bdd hub hg b y) fun b' => ?_)
    unfold obj
    linarith [mul_le_mul_of_nonneg_left
      (ue_sum_mono M.markov (fun j => hfg (min b' M.bmax) j) y) M.β_nonneg]
  · intro f k hf hk b y
    have hS : M.VRsup q (fun a c => f a c + k) b y ≤ M.VRsup q f b y + M.β * k := by
      refine ciSup_le fun b' => ?_
      have h1 : M.obj q f b y (min b' M.bmax) ≤ M.VRsup q f b y :=
        le_ciSup (M.ue_VRsup_bdd hub (q := q) (fun a c => (hf a c).2) b y) b'
      have h2 : M.obj q (fun a c => f a c + k) b y (min b' M.bmax) =
          M.obj q f b y (min b' M.bmax) + M.β * k := by
        simp only [obj, ue_sum_add M.markov]
        ring
      rw [h2]
      linarith
    unfold bell
    exact max_le (by linarith [le_max_left (VD y) (M.VRsup q f b y), mul_nonneg M.β_nonneg hk])
      (by linarith [le_max_right (VD y) (M.VRsup q f b y)])
  · intro f hf b y
    refine ⟨(hmVD y).trans (le_max_left _ _), max_le (hVD y) ?_⟩
    have := M.ue_VRsup_ub hub (q := q) (fun a c => (hf a c).2) b y
    linarith

omit [Fintype Y] in
/-- The repayment indicator lies in `[0, 1]`. -/
theorem ue_thr_mem (bt : Y → ℝ) (b' : ℝ) (j : Y) : 0 ≤ ue_thr bt b' j ∧ ue_thr bt b' j ≤ 1 := by
  unfold ue_thr
  split_ifs <;> norm_num

omit [Fintype Y] in
/-- With nonnegative capacities, debt `B′ ≤ 0` is repaid. -/
theorem ue_thr_nonpos {bt : Y → ℝ} (hbt : ∀ j, 0 ≤ bt j) {b' : ℝ} (hb' : b' ≤ 0) (j : Y) :
    ue_thr bt b' j = 1 := by
  unfold ue_thr
  simp only [hb'.trans (hbt j), ↓reduceIte]

/-- **The Blackwell recast** (Aguiar–Amador 2019): the map from debt capacities to the
capacities they induce moves by at most `1/(1 + r)` times the change in the capacities:
`b̄′₁(Y) ≤ b̄′₂(Y) + ‖b̄₁ − b̄₂‖/(1 + r)`. It follows from the replication argument. -/
theorem ue_cutoff_le (hu : Monotone M.u) {ub : ℝ} (hub : ∀ c, M.u c ≤ ub)
    (hφ : ∀ y, 0 ≤ M.φ (M.inc y)) {VD : Y → ℝ} (hVD : ∀ y, VD y = M.defaultRHS VD y)
    {bt₁ bt₂ : Y → ℝ} (h0₁ : ∀ j, 0 ≤ bt₁ j) (h0₂ : ∀ j, 0 ≤ bt₂ j) {V₁ V₂ : ℝ → Y → ℝ}
    (hV₁ : ∀ b y, M.bell VD (M.price (ue_thr bt₁)) V₁ b y = V₁ b y)
    (hV₁b : ∀ b y, V₁ b y ≤ ub / (1 - M.β))
    (hV₂ : ∀ b y, M.bell VD (M.price (ue_thr bt₂)) V₂ b y = V₂ b y)
    (hV₂b : ∀ b y, V₂ b y ≤ ub / (1 - M.β)) (j : Y) :
    M.cutoff VD (M.price (ue_thr bt₁)) V₁ j ≤
      M.cutoff VD (M.price (ue_thr bt₂)) V₂ j + dist bt₁ bt₂ * (1 + M.r)⁻¹ := by
  have hx : 0 ≤ dist bt₁ bt₂ := dist_nonneg
  have hr1 : 0 < 1 + M.r := by linarith [M.r_pos]
  have hρ : (1 + M.r)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [M.r_pos])
  have hg0 : 0 ≤ dist bt₁ bt₂ * (1 + M.r)⁻¹ := mul_nonneg hx (inv_nonneg.2 hr1.le)
  have hgx : dist bt₁ bt₂ * (1 + M.r)⁻¹ ≤ dist bt₁ bt₂ := mul_le_of_le_one_right hx hρ
  have hE₁ : ∀ b y, V₁ b y = max (VD y) (M.VRsup (M.price (ue_thr bt₁)) V₁ b y) :=
    fun b y => by rw [← hV₁ b y]; rfl
  have hE₂ : ∀ b y, V₂ b y = max (VD y) (M.VRsup (M.price (ue_thr bt₂)) V₂ b y) :=
    fun b y => by rw [← hV₂ b y]; rfl
  have hsup₂ := M.ue_VRsup_sup (M.price (ue_thr bt₂)) V₂
  have hle₂ : ∀ b y b', b' ≤ M.bmax → M.obj (M.price (ue_thr bt₂)) V₂ b y b' ≤
      M.VRsup (M.price (ue_thr bt₂)) V₂ b y := fun b y _ hb' => M.ue_VRsup_le hub hV₂b b y hb'
  have hle₁ : ∀ b y b', b' ≤ M.bmax → M.obj (M.price (ue_thr bt₁)) V₁ b y b' ≤
      M.VRsup (M.price (ue_thr bt₁)) V₁ b y := fun b y _ hb' => M.ue_VRsup_le hub hV₁b b y hb'
  have hanti₂ : ∀ b b' y, b ≤ b' → V₂ b' y ≤ V₂ b y := fun b b' y h => by
    rw [hE₂, hE₂]
    exact max_le_max le_rfl (M.ue_VR_antitone hu hsup₂ hle₂ h y)
  have hdom : ∀ b' j, b' ≤ M.bmax → ue_thr bt₁ b' j ≤ ue_thr bt₂ (b' - dist bt₁ bt₂) j := by
    intro b' j _
    unfold ue_thr
    split_ifs with h1 h2
    · exact le_rfl
    · exfalso
      apply h2
      have h3 := dist_le_pi_dist bt₁ bt₂ j
      rw [Real.dist_eq] at h3
      linarith [le_abs_self (bt₁ j - bt₂ j)]
    · norm_num
    · exact le_rfl
  have hrep : ∀ b y, M.VRsup (M.price (ue_thr bt₁)) V₁ b y ≤
      M.VRsup (M.price (ue_thr bt₂)) V₂ (b - dist bt₁ bt₂ * (1 + M.r)⁻¹) y :=
    M.ue_replication hu hx hgx hE₁ hE₂ ⟨_, hV₁b⟩ (M.ue_VRsup_sup _ _) hle₂ hanti₂
      (fun b' y hb' => M.ue_revenue hx (fun _ _ _ => rfl) (fun _ _ _ => rfl) (ue_thr_mem bt₁)
        (fun _ j h => ue_thr_nonpos h0₁ h j) (fun _ j h => ue_thr_nonpos h0₂ h j) hdom hb' y)
  set S₁ := {b | 0 ≤ b ∧ b ≤ M.bmax ∧ VD j ≤ M.VRsup (M.price (ue_thr bt₁)) V₁ b j} with hS₁
  set S₂ := {b | 0 ≤ b ∧ b ≤ M.bmax ∧ VD j ≤ M.VRsup (M.price (ue_thr bt₂)) V₂ b j} with hS₂
  have h0S₁ : (0 : ℝ) ∈ S₁ := ⟨le_rfl, M.bmax_nonneg, M.ue_repay_nonpos hu hφ hle₁
    (fun b y => by rw [hE₁]; exact le_max_left _ _) hVD le_rfl j⟩
  have h0S₂ : (0 : ℝ) ∈ S₂ := ⟨le_rfl, M.bmax_nonneg, M.ue_repay_nonpos hu hφ hle₂
    (fun b y => by rw [hE₂]; exact le_max_left _ _) hVD le_rfl j⟩
  have hbdd₂ : BddAbove S₂ := ⟨M.bmax, fun b hb => hb.2.1⟩
  have hc0 : 0 ≤ sSup S₂ := le_csSup hbdd₂ h0S₂
  change sSup S₁ ≤ sSup S₂ + dist bt₁ bt₂ * (1 + M.r)⁻¹
  refine csSup_le ⟨0, h0S₁⟩ fun b hb => ?_
  obtain ⟨_, hbm, hbv⟩ := hb
  rcases le_or_gt 0 (b - dist bt₁ bt₂ * (1 + M.r)⁻¹) with h | h
  · have hmem : b - dist bt₁ bt₂ * (1 + M.r)⁻¹ ∈ S₂ :=
      ⟨h, by linarith, hbv.trans (hrep b j)⟩
    linarith [le_csSup hbdd₂ hmem]
  · linarith

/-- **The debt capacities are a fixed point of a contraction.** Given, for each capacity vector
`b̄`, a bounded solution of the Bellman equation at the prices `q = (1 + r)⁻¹ E 1{B′ ≤ b̄(Y′)}`,
the map `b̄ ↦` (the induced capacities) has a fixed point `b̄ ≥ 0` (Banach, modulus
`1/(1 + r)`, `ue_cutoff_le`). -/
theorem ue_capacity_fixed (hu : Monotone M.u) {ub : ℝ} (hub : ∀ c, M.u c ≤ ub)
    (hφ : ∀ y, 0 ≤ M.φ (M.inc y)) {VD : Y → ℝ} (hVD : ∀ y, VD y = M.defaultRHS VD y)
    (Vf : (Y → ℝ) → ℝ → Y → ℝ)
    (hVf : ∀ bt b y, M.bell VD (M.price (ue_thr bt)) (Vf bt) b y = Vf bt b y)
    (hVfb : ∀ bt b y, Vf bt b y ≤ ub / (1 - M.β)) :
    ∃ bt : Y → ℝ, (∀ j, 0 ≤ bt j) ∧ ∀ j, M.cutoff VD (M.price (ue_thr bt)) (Vf bt) j = bt j := by
  have hr1 : 0 < 1 + M.r := by linarith [M.r_pos]
  have hρ0 : 0 ≤ (1 + M.r)⁻¹ := inv_nonneg.2 hr1.le
  have hF0 : ∀ bt j, 0 ≤ M.cutoff VD (M.price (ue_thr bt)) (Vf bt) j := fun bt j => by
    have hE : ∀ b y, Vf bt b y = max (VD y) (M.VRsup (M.price (ue_thr bt)) (Vf bt) b y) :=
      fun b y => by rw [← hVf bt b y]; rfl
    have h0 : (0 : ℝ) ∈ {b | 0 ≤ b ∧ b ≤ M.bmax ∧
        VD j ≤ M.VRsup (M.price (ue_thr bt)) (Vf bt) b j} :=
      ⟨le_rfl, M.bmax_nonneg, M.ue_repay_nonpos hu hφ
        (fun b y _ hb' => M.ue_VRsup_le hub (hVfb bt) b y hb')
        (fun b y => by rw [hE]; exact le_max_left _ _) hVD le_rfl j⟩
    exact le_csSup ⟨M.bmax, fun b hb => hb.2.1⟩ h0
  set G : (Y → ℝ) → Y → ℝ := fun bt =>
    fun j => M.cutoff VD (M.price (ue_thr fun i => max (bt i) 0)) (Vf fun i => max (bt i) 0) j
    with hG
  have hdmax : ∀ a b : Y → ℝ, dist (fun i => max (a i) 0) (fun i => max (b i) 0) ≤ dist a b :=
    fun a b => (dist_pi_le_iff dist_nonneg).2 fun i => by
      rw [Real.dist_eq]
      exact (abs_max_sub_max_le_abs (a i) (b i) 0).trans (by
        rw [← Real.dist_eq]; exact dist_le_pi_dist a b i)
  have hone : ∀ a b : Y → ℝ, ∀ j, G a j ≤ G b j + (1 + M.r)⁻¹ * dist a b := fun a b j => by
    have h1 := M.ue_cutoff_le hu hub hφ hVD (fun i => le_max_right (a i) 0)
      (fun i => le_max_right (b i) 0) (hVf _) (hVfb _) (hVf _) (hVfb _) j
    have h2 := mul_le_mul_of_nonneg_right (hdmax a b) hρ0
    simp only [hG]
    linarith
  have hc : ContractingWith (Real.toNNReal (1 + M.r)⁻¹) G := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
    · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hρ0, NNReal.coe_one]
      exact inv_lt_one_of_one_lt₀ (by linarith [M.r_pos])
    · rw [Real.coe_toNNReal _ hρ0]
      refine (dist_pi_le_iff (mul_nonneg hρ0 dist_nonneg)).2 fun j => ?_
      rw [Real.dist_eq, abs_le]
      constructor
      · have h := hone b a j
        rw [dist_comm b a] at h
        linarith
      · linarith [hone a b j]
  set b₀ := ContractingWith.fixedPoint G hc with hb₀
  have hfix : G b₀ = b₀ := hc.fixedPoint_isFixedPt
  have hb0 : ∀ j, 0 ≤ b₀ j := fun j => by
    rw [← hfix]
    exact hF0 _ j
  have hmax : (fun i => max (b₀ i) 0) = b₀ := funext fun i => max_eq_left (hb0 i)
  refine ⟨b₀, hb0, fun j => ?_⟩
  have h := congrFun hfix j
  simp only [hG, hmax] at h
  exact h

/-- **Existence of the optimal borrowing** at the prices induced by nonnegative capacities: the
objective is upper semicontinuous in `B′` (the price `(1 + r)⁻¹ Σ P 1{B′ ≤ b̄}` jumps down,
and `1{B′ ≤ b̄}B′ = min(B′, b̄ 1{B′ ≤ b̄})` for `b̄ ≥ 0`; `V` is continuous in debt), and by
satiation saving beyond `K₀` (enough to consume `c̄` forever) is never better than saving `K₀`,
so the supremum over `B′ ≤ B̄` is a maximum over the compact `[−K₀, B̄]`. -/
theorem ue_attain (hu : Monotone M.u) (huc : UniformContinuous M.u) {cbar : ℝ}
    (hsat : ∀ c, cbar ≤ c → M.u c = M.u cbar) {VD : Y → ℝ} {bt : Y → ℝ} (hbt : ∀ j, 0 ≤ bt j)
    {V : ℝ → Y → ℝ} (hV : ∀ b y, M.bell VD (M.price (ue_thr bt)) V b y = V b y)
    (hVb : ∀ b y, V b y ≤ M.u cbar / (1 - M.β)) (b : ℝ) (y : Y) :
    ∃ b', b' ≤ M.bmax ∧
      M.obj (M.price (ue_thr bt)) V b y b' = M.VRsup (M.price (ue_thr bt)) V b y := by
  have hub := M.ue_u_le hu hsat
  have h1β : 0 < 1 - M.β := by linarith [M.β_lt_one]
  have hr1 : 0 < 1 + M.r := by linarith [M.r_pos]
  have hE : ∀ b y, V b y = max (VD y) (M.VRsup (M.price (ue_thr bt)) V b y) :=
    fun b y => by rw [← hV b y]; rfl
  have hle : ∀ b y b', b' ≤ M.bmax → M.obj (M.price (ue_thr bt)) V b y b' ≤
      M.VRsup (M.price (ue_thr bt)) V b y := fun b y _ hb' => M.ue_VRsup_le hub hVb b y hb'
  have hsup := M.ue_VRsup_sup (M.price (ue_thr bt)) V
  have hqneg : ∀ b' y, b' ≤ 0 → M.price (ue_thr bt) b' y = (1 + M.r)⁻¹ := fun b' y hb' =>
    M.ue_price_one (fun j => ue_thr_nonpos hbt hb' j) y
  -- `V` is continuous in debt
  have hcont : ∀ j, Continuous fun b => V b j := by
    intro j
    have hVR : Continuous fun b => M.VRsup (M.price (ue_thr bt)) V b j := by
      refine Metric.continuous_iff.2 fun b₀ ε hε => ?_
      obtain ⟨η, hη, hmod⟩ := M.ue_modulus huc hsup hle (half_pos hε)
      refine ⟨η, hη, fun b₁ hb₁ => ?_⟩
      rw [Real.dist_eq] at hb₁ ⊢
      have hb₁' := abs_lt.1 hb₁
      rw [abs_lt]
      rcases le_total b₁ b₀ with h | h
      · have h1 := M.ue_VR_antitone hu hsup hle h j
        have h2 := hmod b₀ j (b₀ - b₁) (by linarith) (by linarith)
        rw [sub_sub_cancel] at h2
        constructor <;> linarith
      · have h1 := M.ue_VR_antitone hu hsup hle h j
        have h2 := hmod b₁ j (b₁ - b₀) (by linarith) (by linarith)
        rw [sub_sub_cancel] at h2
        constructor <;> linarith
    have heq : (fun b => V b j) = fun b => max (VD j) (M.VRsup (M.price (ue_thr bt)) V b j) :=
      funext fun b => hE b j
    rw [heq]
    exact continuous_const.max hVR
  -- savings `K₀` give consumption `≥ c̄` forever
  set K₀ := max 0 ((cbar + ‖M.inc‖) * (1 + M.r) / M.r) with hK₀
  have hK₀0 : 0 ≤ K₀ := le_max_left _ _
  have hcons : ∀ j, cbar ≤ M.inc j - -K₀ + (1 + M.r)⁻¹ * -K₀ := fun j => by
    have hj : -‖M.inc‖ ≤ M.inc j := by
      have h1 := norm_le_pi_norm M.inc j
      rw [Real.norm_eq_abs] at h1
      linarith [neg_abs_le (M.inc j)]
    have h2 : (cbar + ‖M.inc‖) * (1 + M.r) / M.r ≤ K₀ := le_max_right _ _
    rw [div_le_iff₀ M.r_pos] at h2
    have h3 : cbar + ‖M.inc‖ ≤ K₀ * M.r / (1 + M.r) := by
      rw [le_div_iff₀ hr1]
      linarith
    have h4 : M.inc j - -K₀ + (1 + M.r)⁻¹ * -K₀ = M.inc j + K₀ * M.r / (1 + M.r) := by
      field_simp
      ring
    rw [h4]
    linarith
  have hw : ∀ j, M.u cbar / (1 - M.β) ≤ V (-K₀) j := by
    intro j
    have : Nonempty Y := ⟨j⟩
    obtain ⟨j₀, hj₀⟩ := Finite.exists_min fun j => V (-K₀) j
    have hge : ∀ j, M.u cbar + M.β * V (-K₀) j₀ ≤ V (-K₀) j := fun j => by
      have h1 := hle (-K₀) j (-K₀) (by linarith [M.bmax_nonneg])
      have h2 : M.obj (M.price (ue_thr bt)) V (-K₀) j (-K₀) =
          M.u cbar + M.β * ∑ i, M.P j i * V (-K₀) i := by
        unfold obj
        rw [hqneg (-K₀) j (by linarith), hsat _ (hcons j)]
      have h3 := mul_le_mul_of_nonneg_left (ue_le_sum M.markov (fun i => hj₀ i) j) M.β_nonneg
      rw [hE (-K₀) j]
      linarith [le_max_right (VD j) (M.VRsup (M.price (ue_thr bt)) V (-K₀) j)]
    have h5 := hge j₀
    have h6 : M.u cbar / (1 - M.β) ≤ V (-K₀) j₀ := by
      rw [div_le_iff₀ h1β]
      linarith
    exact h6.trans (hj₀ j)
  have hred : ∀ b', b' ≤ -K₀ →
      M.obj (M.price (ue_thr bt)) V b y b' ≤ M.obj (M.price (ue_thr bt)) V b y (-K₀) := by
    intro b' hb'
    unfold obj
    rw [hqneg b' y (by linarith), hqneg (-K₀) y (by linarith)]
    have h1 : M.u (M.inc y - b + (1 + M.r)⁻¹ * b') ≤ M.u (M.inc y - b + (1 + M.r)⁻¹ * -K₀) :=
      hu (by linarith [mul_le_mul_of_nonneg_left hb' (inv_nonneg.2 hr1.le)])
    have h2 : ∑ j, M.P y j * V b' j ≤ ∑ j, M.P y j * V (-K₀) j :=
      ue_sum_mono M.markov (fun j => (hVb b' j).trans (hw j)) y
    nlinarith [mul_le_mul_of_nonneg_left h2 M.β_nonneg]
  -- upper semicontinuity of the objective in `B′`
  have hrev : ∀ b', M.price (ue_thr bt) b' y * b' = (1 + M.r)⁻¹ *
      ∑ j, M.P y j * (b' ⊓ (Set.Iic (bt j)).indicator (fun _ => bt j) b') := by
    intro b'
    unfold price ue_thr
    rw [mul_assoc, sum_mul]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [mul_assoc]
    congr 1
    split_ifs with h
    · rw [Set.indicator_of_mem (Set.mem_Iic.2 h), one_mul, inf_eq_left.2 h]
    · rw [Set.indicator_of_notMem (fun h' => h (Set.mem_Iic.1 h')), zero_mul,
        inf_eq_right.2 (by linarith [hbt j, not_le.1 h])]
  have hsc : ∀ (c : ℝ) {f : ℝ → ℝ}, 0 ≤ c → UpperSemicontinuous f →
      UpperSemicontinuous fun x => c * f x := fun c f hc hf =>
    (continuous_const.mul continuous_id).comp_upperSemicontinuous hf
      (fun a b h => mul_le_mul_of_nonneg_left h hc)
  have ht : ∀ j, UpperSemicontinuous fun b' : ℝ =>
      b' ⊓ (Set.Iic (bt j)).indicator (fun _ => bt j) b' := fun j =>
    continuous_id.upperSemicontinuous.inf (isClosed_Iic.upperSemicontinuous_indicator (hbt j))
  have hR : UpperSemicontinuous fun b' : ℝ => (1 + M.r)⁻¹ *
      ∑ j, M.P y j * (b' ⊓ (Set.Iic (bt j)).indicator (fun _ => bt j) b') :=
    hsc _ (inv_nonneg.2 hr1.le)
      (upperSemicontinuous_sum fun j _ => hsc _ (M.markov.nonneg y j) (ht j))
  have hgc : Continuous fun z : ℝ => M.inc y - b + z := continuous_const.add continuous_id
  have hU : UpperSemicontinuous fun b' : ℝ => M.u (M.inc y - b + (1 + M.r)⁻¹ *
      ∑ j, M.P y j * (b' ⊓ (Set.Iic (bt j)).indicator (fun _ => bt j) b')) :=
    (huc.continuous.comp hgc).comp_upperSemicontinuous hR (fun a c h => hu (by linarith))
  have hC : Continuous fun b' : ℝ => M.β * ∑ j, M.P y j * V b' j :=
    continuous_const.mul (continuous_finsetSum _ fun j _ => continuous_const.mul (hcont j))
  have husc : UpperSemicontinuous fun b' => M.obj (M.price (ue_thr bt)) V b y b' := by
    have heq : (fun b' => M.obj (M.price (ue_thr bt)) V b y b') = fun b' =>
        M.u (M.inc y - b + (1 + M.r)⁻¹ *
          ∑ j, M.P y j * (b' ⊓ (Set.Iic (bt j)).indicator (fun _ => bt j) b')) +
        M.β * ∑ j, M.P y j * V b' j := funext fun b' => by
      unfold obj
      rw [hrev b']
    rw [heq]
    exact hU.add hC.upperSemicontinuous
  obtain ⟨bs, hbs, hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn
    (⟨0, by linarith, M.bmax_nonneg⟩ : (Set.Icc (-K₀) M.bmax).Nonempty) isCompact_Icc
    (husc.upperSemicontinuousOn _)
  refine ⟨bs, hbs.2, le_antisymm (hle b y bs hbs.2) (ciSup_le fun b'' => ?_)⟩
  rcases le_total (-K₀) (min b'' M.bmax) with h | h
  · exact isMaxOn_iff.1 hmax _ ⟨h, min_le_right _ _⟩
  · exact (hred _ h).trans (isMaxOn_iff.1 hmax _ ⟨le_rfl, by linarith [M.bmax_nonneg]⟩)

/-- **Existence of the Markov perfect equilibrium with one-period debt** (Auclert–Rognlie
2016; Aguiar–Amador 2019; AKMM, p. 901, beyond the text): with `u` nondecreasing, uniformly
continuous and satiated, `φ ≥ 0` and `r > 0`, an equilibrium exists. The prices are those of
the fixed-point capacities `b̄` (`ue_capacity_fixed`): `q(B′, Y) = (1 + r)⁻¹ Pr(B′ ≤ b̄(Y′))`. -/
theorem ue_mpe_exists (hu : Monotone M.u) (huc : UniformContinuous M.u) {cbar : ℝ}
    (hsat : ∀ c, cbar ≤ c → M.u c = M.u cbar) (hφ : ∀ y, 0 ≤ M.φ (M.inc y)) :
    ∃ (V VR : ℝ → Y → ℝ) (VD : Y → ℝ) (D Bh q : ℝ → Y → ℝ), IsOneMPE M V VR VD D Bh q := by
  have hub := M.ue_u_le hu hsat
  obtain ⟨VD, hVD, hVDle⟩ := M.ue_VD_exists hub
  have hsol := fun bt : Y → ℝ => M.ue_sol_exists hub hVDle (M.price (ue_thr bt))
  choose Vf hVf hVfb using hsol
  obtain ⟨bt, hbt0, hbt⟩ := M.ue_capacity_fixed hu hub hφ hVD Vf hVf
    (fun bt b y => (hVfb bt b y).2)
  have hVb : ∀ b y, Vf bt b y ≤ M.u cbar / (1 - M.β) := fun b y => (hVfb bt b y).2
  have hE : ∀ b y, Vf bt b y = max (VD y) (M.VRsup (M.price (ue_thr bt)) (Vf bt) b y) :=
    fun b y => by rw [← hVf bt b y]; rfl
  have hle : ∀ b y b', b' ≤ M.bmax → M.obj (M.price (ue_thr bt)) (Vf bt) b y b' ≤
      M.VRsup (M.price (ue_thr bt)) (Vf bt) b y := fun b y _ hb' => M.ue_VRsup_le hub hVb b y hb'
  have hsup := M.ue_VRsup_sup (M.price (ue_thr bt)) (Vf bt)
  have hatt := M.ue_attain hu huc hsat hbt0 (hVf bt) hVb
  choose Bh hBh hBhopt using hatt
  have hiff : ∀ b' j, b' ≤ M.bmax →
      (b' ≤ bt j ↔ VD j ≤ M.VRsup (M.price (ue_thr bt)) (Vf bt) b' j) := by
    intro b' j hb'
    set S := {b | 0 ≤ b ∧ b ≤ M.bmax ∧ VD j ≤ M.VRsup (M.price (ue_thr bt)) (Vf bt) b j}
      with hS
    have hbtS : bt j = sSup S := (hbt j).symm
    have hbdd : BddAbove S := ⟨M.bmax, fun b hb => hb.2.1⟩
    have h0S : (0 : ℝ) ∈ S := ⟨le_rfl, M.bmax_nonneg, M.ue_repay_nonpos hu hφ hle
      (fun b y => by rw [hE]; exact le_max_left _ _) hVD le_rfl j⟩
    constructor
    · intro h
      have hclosed : VD j ≤ M.VRsup (M.price (ue_thr bt)) (Vf bt) (bt j) j := by
        refine le_of_forall_pos_le_add fun ε hε => ?_
        obtain ⟨η, hη, hmod⟩ := M.ue_modulus huc hsup hle hε
        obtain ⟨s, hs, hslt⟩ := exists_lt_of_lt_csSup ⟨0, h0S⟩
          (by linarith : sSup S - η < sSup S)
        have hsle : s ≤ sSup S := le_csSup hbdd hs
        have h1 := hmod (sSup S) j (sSup S - s) (by linarith) (by linarith)
        rw [sub_sub_cancel] at h1
        rw [hbtS]
        linarith [hs.2.2]
      exact hclosed.trans (M.ue_VR_antitone hu hsup hle h j)
    · intro h
      rcases le_total b' 0 with h0 | h0
      · exact h0.trans (hbt0 j)
      · rw [hbtS]
        exact le_csSup hbdd ⟨h0, hb', h⟩
  refine ⟨Vf bt, M.VRsup (M.price (ue_thr bt)) (Vf bt), VD,
    fun b y => if M.VRsup (M.price (ue_thr bt)) (Vf bt) b y < VD y then 1 else 0, Bh,
    M.price (ue_thr bt), ?_⟩
  exact { bdd := ⟨_, hVb⟩
          eq_24_9 := hE
          eq_24_10 := hVD
          eq_24_11 := hle
          eq_24_12 := fun b' y hb' => by
            have hp : M.price (ue_thr bt) b' y =
                (1 + M.r)⁻¹ * ∑ j, M.P y j * ue_thr bt b' j := rfl
            rw [hp]
            congr 1
            refine sum_congr rfl fun j _ => ?_
            congr 1
            have hj := hiff b' j hb'
            have ht1 : ue_thr bt b' j = if b' ≤ bt j then 1 else 0 := rfl
            rw [ht1]
            split_ifs with h1 h2 h2
            · exact absurd (hj.1 h1) (not_le.2 h2)
            · norm_num
            · norm_num
            · exact absurd (hj.2 (not_lt.1 h2)) h1
          default_opt := fun _ _ => rfl
          borrow_le := hBh
          borrow_opt := hBhopt }

/-- **Existence and uniqueness** (AKMM, p. 901, beyond the text): under the hypotheses of
`ue_mpe_exists` there is a Markov perfect equilibrium, and all equilibria share their value
functions, default rule and prices (`ue_mpe_unique`). -/
theorem ue_mpe_exists_unique (hu : Monotone M.u) (huc : UniformContinuous M.u) {cbar : ℝ}
    (hsat : ∀ c, cbar ≤ c → M.u c = M.u cbar) (hφ : ∀ y, 0 ≤ M.φ (M.inc y)) :
    (∃ (V VR : ℝ → Y → ℝ) (VD : Y → ℝ) (D Bh q : ℝ → Y → ℝ), IsOneMPE M V VR VD D Bh q) ∧
      ∀ {V₁ VR₁ D₁ Bh₁ q₁ V₂ VR₂ D₂ Bh₂ q₂ : ℝ → Y → ℝ} {VD₁ VD₂ : Y → ℝ},
        IsOneMPE M V₁ VR₁ VD₁ D₁ Bh₁ q₁ → IsOneMPE M V₂ VR₂ VD₂ D₂ Bh₂ q₂ →
        V₁ = V₂ ∧ VR₁ = VR₂ ∧ VD₁ = VD₂ ∧ D₁ = D₂ ∧
          ∀ b' y, b' ≤ M.bmax → q₁ b' y = q₂ b' y :=
  ⟨M.ue_mpe_exists hu huc hsat hφ, fun h₁ h₂ => M.ue_mpe_unique hu huc hφ h₁ h₂⟩

end UEModel

/-- A concrete economy satisfying every hypothesis of `ue_mpe_exists_unique`: income `1` or `2`
(`false`, `true`), i.i.d. with probability `1/2`; utility `u(c) = min(c, 3)` (nondecreasing,
1-Lipschitz, satiated at `c̄ = 3`); default cost `φ(Y) = Y/4`; `β = 1/2`, `r = 1/4` and the
borrowing limit `B̄ = 1`. -/
noncomputable def ue_example : UEModel Bool where
  inc := fun y => if y then 2 else 1
  P := fun _ _ => 1 / 2
  markov := ⟨fun _ _ => by norm_num, fun _ => by rw [Fintype.sum_bool]; norm_num⟩
  u := fun c => min c 3
  φ := fun Yc => Yc / 4
  β := 1 / 2
  β_nonneg := by norm_num
  β_lt_one := by norm_num
  r := 1 / 4
  r_pos := by norm_num
  bmax := 1
  bmax_nonneg := zero_le_one

/-- The example meets the hypotheses: `u` nondecreasing, uniformly continuous and satiated at
`3`, `φ ≥ 0`. -/
theorem ue_example_hyp : Monotone ue_example.u ∧ UniformContinuous ue_example.u ∧
    (∀ c, 3 ≤ c → ue_example.u c = ue_example.u 3) ∧
    ∀ y, 0 ≤ ue_example.φ (ue_example.inc y) := by
  refine ⟨fun a b h => min_le_min_right 3 h, (LipschitzWith.id.min_const 3).uniformContinuous,
    fun c hc => ?_, fun y => ?_⟩
  · change min c 3 = min 3 3
    rw [min_eq_right hc, min_self]
  · change 0 ≤ (if y then (2 : ℝ) else 1) / 4
    split_ifs <;> norm_num

/-- **The example has a Markov perfect equilibrium, and it is unique** (in values, default
rule and prices): `ue_mpe_exists_unique` is not vacuous. -/
theorem ue_example_exists_unique :
    (∃ (V VR : ℝ → Bool → ℝ) (VD : Bool → ℝ) (D Bh q : ℝ → Bool → ℝ),
      IsOneMPE ue_example V VR VD D Bh q) ∧
      ∀ {V₁ VR₁ D₁ Bh₁ q₁ V₂ VR₂ D₂ Bh₂ q₂ : ℝ → Bool → ℝ} {VD₁ VD₂ : Bool → ℝ},
        IsOneMPE ue_example V₁ VR₁ VD₁ D₁ Bh₁ q₁ → IsOneMPE ue_example V₂ VR₂ VD₂ D₂ Bh₂ q₂ →
        V₁ = V₂ ∧ VR₁ = VR₂ ∧ VD₁ = VD₂ ∧ D₁ = D₂ ∧
          ∀ b' y, b' ≤ ue_example.bmax → q₁ b' y = q₂ b' y := by
  obtain ⟨h1, h2, h3, h4⟩ := ue_example_hyp
  exact ue_example.ue_mpe_exists_unique h1 h2 h3 h4

end AKMM.SovereignDefault

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Multiple Markov perfect equilibria on a finite debt grid

AKMM, Appendix 24.A.1, p. 901: "Aguiar and Amador (2020) show that there can be multiple
Markov equilibria in the model with long-term debt (`δ ∈ (0, 1)`), implying that the initial
guess plays a non-trivial role in the computation of the equilibrium." Beyond the text.

On the book's computational setting (finite grids, Appendix 24.A.1; the project's `SDModel`
and `IsMPE`, departure D4) we give explicit economies with two Markov perfect equilibria, both
verified analytically against every equilibrium condition (a)–(c) of §24.4.3:

* with long-term debt, `δ = 1/2` (`mu_grid_long_term_two_mpe`);
* and already with **one-period debt**, `δ = 1` (`mu_grid_one_period_two_mpe`). The uniqueness
  theorem for `δ = 1` (`ue_mpe_unique`) therefore needs a continuum of debt choices: on a grid
  it fails (correction 9). The economy satisfies every other hypothesis of `ue_mpe_unique`
  (`u = id` nondecreasing and uniformly continuous, `φ ≥ 0`, `r > 0`, `ψ = 0`).

The economy: one income level `Y = 1`, debt grid `{0, 1}` (`false`, `true`), `u = id`,
`φ = 1/4`, `β = 1/2`, permanent exclusion `ψ = 0`, `r = 1/4`. In the *good* equilibrium the
sovereign borrows `1` and rolls it over forever at the risk-free price; in the *bad* one lenders
expect default on debt `1`, the price of debt `1` is `0`, and a sovereign holding debt `1`
cannot roll it over, so it defaults: the expectation is self-fulfilling. Default yields
`V^D = (3/4)/(1 − 1/2) = 3/2`, between the bad and good values of repaying debt `1`. On a
continuum the sovereign would escape the bad equilibrium by issuing a little less debt
(the replication argument of `ue_replication`); on the grid the nearest lower debt is `0`.

This is not Aguiar–Amador's (2020) multiplicity, which arises with a continuum of debt levels
from debt dilution under long-term debt; that construction is not formalised.
-/

namespace AKMM.SovereignDefault

open Finset SargentStachurski.RecursiveDecisionProcesses

/-- The economy of the multiplicity examples, for a coupon decay `δ ∈ [0, 1]`: one income
level `1`, debt grid `{0, 1}`, `u = id`, `φ = 1/4`, `β = 1/2`, `ψ = 0`. -/
noncomputable def mu_econ (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) : SDModel Unit Bool where
  inc := fun _ => 1
  P := fun _ _ => 1
  markov := ⟨fun _ _ => zero_le_one, fun _ => by simp⟩
  bond := fun b => if b then 1 else 0
  b₀ := false
  bond_b₀ := rfl
  u := id
  φ := fun _ => 1 / 4
  β := 1 / 2
  β_nonneg := by norm_num
  β_lt_one := by norm_num
  ψ := 0
  ψ_nonneg := le_rfl
  ψ_le_one := zero_le_one
  δ := δ
  δ_nonneg := h0
  δ_le_one := h1

/-- The maximum over the two-point debt grid. -/
theorem mu_sup_bool (f : Bool → ℝ) :
    (univ : Finset Bool).sup' ⟨false, mem_univ _⟩ f = max (f true) (f false) := by
  refine le_antisymm (sup'_le _ _ fun b _ => ?_)
    (max_le (le_sup' f (mem_univ true)) (le_sup' f (mem_univ false)))
  cases b
  · exact le_max_right _ _
  · exact le_max_left _ _

/-- **Two Markov perfect equilibria with one-period debt on a grid** (`δ = 1`, `r = 1/4`).
Good: no default, `q ≡ 4/5`, the sovereign always issues `1`, `V(0) = 13/5`, `V(1) = 8/5`. Bad:
default on debt `1`, `q(0) = 4/5`, `q(1) = 0`, the sovereign issues `0`, `V(0) = 2`,
`V(1) = V^D = 3/2`, `V^R(1) = 1`. The prices of debt `1` differ. -/
theorem mu_grid_one_period_two_mpe :
    IsMPE (mu_econ 1 zero_le_one le_rfl) (1 / 4) (fun b _ => if b then 8 / 5 else 13 / 5)
        (fun b _ => if b then 8 / 5 else 13 / 5) (fun _ => 3 / 2) (fun _ _ => 0)
        (fun _ _ => true) (fun _ _ => 4 / 5) ∧
      IsMPE (mu_econ 1 zero_le_one le_rfl) (1 / 4) (fun b _ => if b then 3 / 2 else 2)
        (fun b _ => if b then 1 else 2) (fun _ => 3 / 2) (fun b _ => if b then 1 else 0)
        (fun _ _ => false) (fun b _ => if b then 0 else 4 / 5) ∧
      (fun _ _ => (4 / 5 : ℝ)) true () ≠ (fun (b : Bool) (_ : Unit) =>
        if b then (0 : ℝ) else 4 / 5) true () := by
  refine ⟨⟨fun b y => ?_, fun y => ?_, fun b y => ?_, fun m y => ?_, fun b y => ?_,
    fun b y => ?_⟩, ⟨fun b y => ?_, fun y => ?_, fun b y => ?_, fun m y => ?_, fun b y => ?_,
    fun b y => ?_⟩, by norm_num⟩ <;>
  (try simp only [SDModel.repayValue, SDModel.defaultValue, SDModel.cons, bp_op12, mu_econ,
    mu_sup_bool, univ_unique, sum_singleton, id]) <;>
  first | (cases b <;> norm_num) | (cases m <;> norm_num) | norm_num

/-- **Two Markov perfect equilibria with long-term debt on a grid** (`δ = 1/2`, `r = 1/4`;
AKMM, p. 901, Aguiar–Amador 2020 for the continuum). Good: no default, `q ≡ 2/3` (the
risk-free price `δ/(δ + r)`), the sovereign always issues up to `1`, `V(0) = 5/2`,
`V(1) = 5/3`. Bad: default on debt `1`, `q(0) = 2/3`, `q(1) = 0`, `V(0) = 2`, `V(1) = 3/2`,
`V^R(1) = 5/4`. The prices of debt `1` differ. -/
theorem mu_grid_long_term_two_mpe :
    IsMPE (mu_econ (1 / 2) (by norm_num) (by norm_num)) (1 / 4)
        (fun b _ => if b then 5 / 3 else 5 / 2) (fun b _ => if b then 5 / 3 else 5 / 2)
        (fun _ => 3 / 2) (fun _ _ => 0) (fun _ _ => true) (fun _ _ => 2 / 3) ∧
      IsMPE (mu_econ (1 / 2) (by norm_num) (by norm_num)) (1 / 4)
        (fun b _ => if b then 3 / 2 else 2) (fun b _ => if b then 5 / 4 else 2) (fun _ => 3 / 2)
        (fun b _ => if b then 1 else 0) (fun b _ => b) (fun b _ => if b then 0 else 2 / 3) ∧
      (fun _ _ => (2 / 3 : ℝ)) true () ≠ (fun (b : Bool) (_ : Unit) =>
        if b then (0 : ℝ) else 2 / 3) true () := by
  refine ⟨⟨fun b y => ?_, fun y => ?_, fun b y => ?_, fun m y => ?_, fun b y => ?_,
    fun b y => ?_⟩, ⟨fun b y => ?_, fun y => ?_, fun b y => ?_, fun m y => ?_, fun b y => ?_,
    fun b y => ?_⟩, by norm_num⟩ <;>
  (try simp only [SDModel.repayValue, SDModel.defaultValue, SDModel.cons, bp_op12, mu_econ,
    mu_sup_bool, univ_unique, sum_singleton, id]) <;>
  first | (cases b <;> norm_num) | (cases m <;> norm_num) | norm_num

end AKMM.SovereignDefault

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The limit of the finite-horizon game

AKMM, Appendix 24.A.1, pp. 899 and 901: the computation starts from "the solution in the final
period of a finite horizon model", `V₀^R(B, Y) = u(Y − δB)`, `V₀^D(Y) = u(Y − φ(Y))`,
`q₀(B′, Y) = 0`, `B̂₀(B, Y) = 0` and `D̂₀ = 1` iff `V₀^D > V₀^R` ("In the last period of the
finite horizon game, the sovereign has no access to credit markets and consumes all available
resources"), and "By using as initial guesses the equilibrium functions in the last period (T)
of a finite-horizon economy, we are finding the equilibrium that is the limit of the finite
horizon game as `T → ∞`." Beyond the text we prove this in the continuous-debt one-period
setting of `UniqueEquilibrium` (departure D10: `δ = 1`, `ψ = 0`, `B′ ≤ B̄` with saving).

* **The finite-horizon game** (`IsFHEqm`): stage `n` is the period with `n` periods left; stage
  `0` is the book's terminal period, stage `n + 1` solves (24.9)–(24.12) with the stage-`n`
  objects as continuation. The objects of stage `n` do not depend on the horizon `T ≥ n`, so
  the `T`-period game's equilibrium is the first `T + 1` stages of one sequence.
* **Uniqueness** by backward induction (`fh_unique`; no hypothesis on `u` is needed, and no
  replication argument: each stage is determined by the next).
* **Existence** (`fh_exists`, for `u` nondecreasing, uniformly continuous and satiated,
  `φ ≥ 0`): each stage's repayment set is a closed down-set, so prices come from debt
  capacities, the objective is upper semicontinuous in `B′`, and satiation bounds savings
  (`fh_attain`).
* **Convergence as `T → ∞`** to the unique Markov perfect equilibrium. With `ψ = 0` the
  default value is exogenous, and the comparison is on `V^R − V^D`. The finite-horizon
  differences never exceed the equilibrium one (`fh_upper`); conversely the equilibrium
  difference is bounded by the finite-horizon one after a debt reduction `g_n` plus an error
  `e_n = βⁿe₀` (`fh_lower`). A slope condition on `u` below the consumption the sovereign can
  reach turns the error into a further debt reduction `e_n/κ`, so the shift obeys
  `g_{n+1} = (g_n + e_n/κ)/(1 + r)`, a contraction of modulus `1/(1 + r)` moving with `n`.
  The general lemma (`fh_moving_contraction`): if `Φ` is a contraction and `Φ_n → Φ`
  uniformly, the iterates `x_{n+1} = Φ_n(x_n)` converge to the fixed point of `Φ`. So
  `g_n → 0`, and:
  - default sets converge (`fh_default_sets`): the sovereign defaults more with a finite
    horizon, and repays the equilibrium's repaid debts after a reduction `x_n → 0`;
  - debt capacities converge (`fh_capacity_tendsto`);
  - values `V`, `V^R`, `V^D` converge uniformly (`fh_values_tendsto`);
  - prices and default rules converge at every debt where the equilibrium default rule is
    locally constant to the right (`fh_price_tendsto`), i.e. everywhere except at the
    capacities, where the finite-horizon prices stay below (`q_{n+1} ≤ q`); and
    `q(B′ + x_n) ≤ q_{n+1}(B′)`.
* The concrete economy `ue_example` meets every hypothesis (`fh_example_limit`).

The slope condition (`κ(c′ − c) ≤ u(c′) − u(c)` for `c ≤ c′ ≤ c̄` with
`Y + B̄/(1 + r) ≤ c̄`) is beyond the book; it holds for `u = min(c, c̄)`.
-/

namespace AKMM.SovereignDefault

open Finset Filter Topology SargentStachurski.RecursiveDecisionProcesses

/-- **A perturbed linear recursion converges**: if `0 ≤ dₙ`, `d_{n+1} ≤ ρ dₙ + εₙ` with
`0 ≤ ρ < 1` and `εₙ → 0`, then `dₙ → 0`. -/
theorem fh_scalar {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {d ε : ℕ → ℝ} (hd0 : ∀ n, 0 ≤ d n)
    (hrec : ∀ n, d (n + 1) ≤ ρ * d n + ε n) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto d atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  have h1ρ : 0 < 1 - ρ := by linarith
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hε.eventually (Iio_mem_nhds
    (by positivity : (0 : ℝ) < η * (1 - ρ) / 2)))
  have hk : ∀ k, d (N₁ + k) ≤ ρ ^ k * d N₁ + η / 2 := by
    intro k
    induction k with
    | zero => simp; linarith
    | succ k ih =>
      have h2 := hrec (N₁ + k)
      have h3 : ε (N₁ + k) < η * (1 - ρ) / 2 := hN₁ (N₁ + k) (by omega)
      rw [show N₁ + (k + 1) = N₁ + k + 1 by ring, pow_succ]
      nlinarith [mul_le_mul_of_nonneg_left ih hρ0]
  have ht : Tendsto (fun k : ℕ => ρ ^ k * d N₁) atTop (𝓝 (0 * d N₁)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const _
  rw [zero_mul] at ht
  obtain ⟨K, hK⟩ := eventually_atTop.1 (ht.eventually (Iio_mem_nhds (half_pos hη)))
  refine ⟨N₁ + K, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = N₁ + k := ⟨n - N₁, by omega⟩
  have h1 := hk k
  have h2 : ρ ^ k * d N₁ < η / 2 := hK k (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hd0 _)]
  linarith

/-- **A contraction with a moving map** (the joint argument for the finite-horizon limit): let
`Φ` be a contraction of modulus `ρ < 1` with fixed point `x⋆`, and `Φₙ → Φ` uniformly,
`dist (Φₙ x) (Φ x) ≤ εₙ → 0`. Then the iterates `x_{n+1} = Φₙ(xₙ)` converge to `x⋆`. -/
theorem fh_moving_contraction {X : Type*} [MetricSpace X] (Φ : X → X) (Φs : ℕ → X → X)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hΦ : ∀ x y, dist (Φ x) (Φ y) ≤ ρ * dist x y)
    {xs : X} (hfix : Φ xs = xs) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hunif : ∀ n x, dist (Φs n x) (Φ x) ≤ ε n) {x : ℕ → X} (hx : ∀ n, x (n + 1) = Φs n (x n)) :
    Tendsto x atTop (𝓝 xs) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine fh_scalar hρ0 hρ1 (fun n => dist_nonneg) (fun n => ?_) hε
  calc dist (x (n + 1)) xs = dist (Φs n (x n)) (Φ xs) := by rw [hx, hfix]
    _ ≤ dist (Φs n (x n)) (Φ (x n)) + dist (Φ (x n)) (Φ xs) := dist_triangle _ _ _
    _ ≤ ε n + ρ * dist (x n) xs := add_le_add (hunif n _) (hΦ _ _)
    _ = ρ * dist (x n) xs + ε n := by ring

/-- The repayment indicator `1{a < c}` is `0` exactly when `c ≤ a`. -/
theorem fh_ite_zero (a c : ℝ) : (if a < c then (1 : ℝ) else 0) = 0 ↔ c ≤ a := by
  by_cases h : a < c
  · simp only [h, ↓reduceIte, one_ne_zero, false_iff, not_le]
  · simp only [h, ↓reduceIte, true_iff]
    exact not_lt.1 h

/-- The indicator `1{a < c}` lies in `[0, 1]`. -/
theorem fh_ite_mem (a c : ℝ) :
    0 ≤ 1 - (if a < c then (1 : ℝ) else 0) ∧ 1 - (if a < c then (1 : ℝ) else 0) ≤ 1 := by
  split_ifs <;> norm_num

/-- Revenue is bounded by `B̄/(1 + r)` when the price lies in `[0, (1 + r)⁻¹]`. -/
theorem fh_rev_le {p b' bmax s : ℝ} (hs : 0 ≤ s) (hp0 : 0 ≤ p) (hp1 : p ≤ s) (hb : b' ≤ bmax)
    (hbm : 0 ≤ bmax) : p * b' ≤ bmax * s := by
  rcases le_total 0 b' with h | h
  · nlinarith
  · nlinarith

variable {Y : Type*} [Fintype Y]

variable (M : UEModel Y) (T : ℕ) (V VR : ℕ → ℝ → Y → ℝ) (VD : ℕ → Y → ℝ)
  (D Bh q : ℕ → ℝ → Y → ℝ) in
/-- **The finite-horizon game** (AKMM, App. 24.A.1, p. 899; with one-period debt `δ = 1`,
`ψ = 0` and a continuum of debt levels `B′ ≤ B̄`, departure D10). Stage `n` has `n` periods
left; the game of horizon `T` has stages `0, …, T`. Stage `0` is the book's last period:
`V₀^R(B, Y) = u(Y − B)`, `V₀^D(Y) = u(Y − φ(Y))`, `q₀ = 0`, `B̂₀ = 0`. Stage `n + 1` satisfies
(24.9)–(24.12) with the stage-`n` objects as continuation: `V^D_{n+1} = u(Y − φ) + βE V^D_n`,
`q_{n+1}(B′, Y) = (1 + r)⁻¹ E[1 − D̂_n(B′, Y′)]`, and `V^R_{n+1}` the maximum of
`u(Y − B + q_{n+1}(B′, Y)B′) + βE V_n(B′, Y′)` over `B′ ≤ B̄`, attained by `B̂_{n+1}`. At every
stage `V_n = max(V^D_n, V^R_n)` and `D̂_n` is optimal (ties repaid). -/
structure IsFHEqm : Prop where
  /-- (24.9) at every stage. -/
  eq_24_9 : ∀ n ≤ T, ∀ b y, V n b y = max (VD n y) (VR n b y)
  /-- The default rule is optimal at every stage (ties repaid). -/
  default_opt : ∀ n ≤ T, ∀ b y, D n b y = if VR n b y < VD n y then 1 else 0
  /-- The last period: `V₀^D(Y) = u(Y − φ(Y))`. -/
  term_VD : ∀ y, VD 0 y = M.u (M.inc y - M.φ (M.inc y))
  /-- The last period: `V₀^R(B, Y) = u(Y − B)`. -/
  term_VR : ∀ b y, VR 0 b y = M.u (M.inc y - b)
  /-- The last period: `q₀ = 0`. -/
  term_q : ∀ b' y, q 0 b' y = 0
  /-- The last period: `B̂₀ = 0`. -/
  term_B : ∀ b y, Bh 0 b y = 0
  /-- (24.10) at `ψ = 0`, stage `n + 1`. -/
  eq_24_10 : ∀ n < T, ∀ y, VD (n + 1) y = M.defaultRHS (VD n) y
  /-- (24.11), stage `n + 1`: `V^R_{n+1}` bounds the objective ... -/
  eq_24_11 : ∀ n < T, ∀ b y b', b' ≤ M.bmax → M.obj (q (n + 1)) (V n) b y b' ≤ VR (n + 1) b y
  /-- (24.12) at `δ = 1`, stage `n + 1`. -/
  eq_24_12 : ∀ n < T, ∀ b' y, b' ≤ M.bmax →
    q (n + 1) b' y = (1 + M.r)⁻¹ * ∑ j, M.P y j * (1 - D n b' j)
  /-- The borrowing rule is feasible. -/
  borrow_le : ∀ n < T, ∀ b y, Bh (n + 1) b y ≤ M.bmax
  /-- ... and attains the maximum in (24.11). -/
  borrow_opt : ∀ n < T, ∀ b y, M.obj (q (n + 1)) (V n) b y (Bh (n + 1) b y) = VR (n + 1) b y

namespace UEModel

variable (M : UEModel Y)

/-- The objective depends on the price only at the chosen debt. -/
theorem fh_obj_congr {q₁ q₂ V : ℝ → Y → ℝ} {b : ℝ} {y : Y} {b' : ℝ} (h : q₁ b' y = q₂ b' y) :
    M.obj q₁ V b y b' = M.obj q₂ V b y b' := by
  unfold obj
  rw [h]

/-- **Uniqueness of the finite-horizon equilibrium** (backward induction): two equilibria of
the game of horizon `T` have the same values, default rules and prices at every stage. -/
theorem fh_unique {T : ℕ} {V₁ VR₁ D₁ Bh₁ q₁ V₂ VR₂ D₂ Bh₂ q₂ : ℕ → ℝ → Y → ℝ}
    {VD₁ VD₂ : ℕ → Y → ℝ} (h₁ : IsFHEqm M T V₁ VR₁ VD₁ D₁ Bh₁ q₁)
    (h₂ : IsFHEqm M T V₂ VR₂ VD₂ D₂ Bh₂ q₂) :
    ∀ n ≤ T, V₁ n = V₂ n ∧ VR₁ n = VR₂ n ∧ VD₁ n = VD₂ n ∧ D₁ n = D₂ n ∧
      ∀ b' y, b' ≤ M.bmax → q₁ n b' y = q₂ n b' y := by
  intro n
  induction n with
  | zero =>
    intro hT
    have hVD : VD₁ 0 = VD₂ 0 := funext fun y => by rw [h₁.term_VD, h₂.term_VD]
    have hVR : VR₁ 0 = VR₂ 0 := funext fun b => funext fun y => by rw [h₁.term_VR, h₂.term_VR]
    refine ⟨funext fun b => funext fun y => by
        rw [h₁.eq_24_9 0 hT, h₂.eq_24_9 0 hT, hVD, hVR], hVR, hVD,
      funext fun b => funext fun y => by rw [h₁.default_opt 0 hT, h₂.default_opt 0 hT, hVD, hVR],
      fun b' y _ => by rw [h₁.term_q, h₂.term_q]⟩
  | succ n ih =>
    intro hT
    have hnT : n < T := hT
    obtain ⟨hV, _, hVDn, hD, _⟩ := ih hnT.le
    have hVD : VD₁ (n + 1) = VD₂ (n + 1) := funext fun y => by
      rw [h₁.eq_24_10 n hnT, h₂.eq_24_10 n hnT, hVDn]
    have hq : ∀ b' y, b' ≤ M.bmax → q₁ (n + 1) b' y = q₂ (n + 1) b' y := fun b' y hb' => by
      rw [h₁.eq_24_12 n hnT b' y hb', h₂.eq_24_12 n hnT b' y hb', hD]
    have hVR : VR₁ (n + 1) = VR₂ (n + 1) := funext fun b => funext fun y => le_antisymm (by
        rw [← h₁.borrow_opt n hnT b y, M.fh_obj_congr (hq _ y (h₁.borrow_le n hnT b y)), hV]
        exact h₂.eq_24_11 n hnT b y _ (h₁.borrow_le n hnT b y)) (by
        rw [← h₂.borrow_opt n hnT b y, ← M.fh_obj_congr (hq _ y (h₂.borrow_le n hnT b y)), ← hV]
        exact h₁.eq_24_11 n hnT b y _ (h₂.borrow_le n hnT b y))
    refine ⟨funext fun b => funext fun y => by
        rw [h₁.eq_24_9 _ hT, h₂.eq_24_9 _ hT, hVD, hVR], hVR, hVD,
      funext fun b => funext fun y => by rw [h₁.default_opt _ hT, h₂.default_opt _ hT, hVD, hVR],
      hq⟩

/-- In a finite-horizon equilibrium the price lies in `[0, (1 + r)⁻¹]`. -/
theorem fh_q_mem {T : ℕ} {V VR D Bh q : ℕ → ℝ → Y → ℝ} {VD : ℕ → Y → ℝ}
    (h : IsFHEqm M T V VR VD D Bh q) {n : ℕ} (hn : n < T) {b' : ℝ} (hb' : b' ≤ M.bmax)
    (y : Y) : 0 ≤ q (n + 1) b' y ∧ q (n + 1) b' y ≤ (1 + M.r)⁻¹ := by
  rw [h.eq_24_12 n hn b' y hb']
  exact M.ue_price_mem (a := fun b j => 1 - D n b j) (fun j => by
    rw [h.default_opt n hn.le]; exact fh_ite_mem _ _) y

/-- In a Markov perfect equilibrium the price lies in `[0, (1 + r)⁻¹]`. -/
theorem fh_mpe_q_mem {V VR D Bh q : ℝ → Y → ℝ} {VD : Y → ℝ} (h : IsOneMPE M V VR VD D Bh q)
    {b' : ℝ} (hb' : b' ≤ M.bmax) (y : Y) : 0 ≤ q b' y ∧ q b' y ≤ (1 + M.r)⁻¹ := by
  rw [h.eq_24_12 b' y hb']
  exact M.ue_price_mem (a := fun b j => 1 - D b j) (fun j => by
    rw [h.default_opt]; exact fh_ite_mem _ _) y

/-- At every stage of the finite-horizon game debt `B ≤ 0` is repaid. -/
theorem fh_repay_nonpos (hu : Monotone M.u) (hφ : ∀ y, 0 ≤ M.φ (M.inc y)) {T : ℕ}
    {V VR D Bh q : ℕ → ℝ → Y → ℝ} {VD : ℕ → Y → ℝ} (h : IsFHEqm M T V VR VD D Bh q) {n : ℕ}
    (hn : n ≤ T) {b : ℝ} (hb : b ≤ 0) (y : Y) : VD n y ≤ VR n b y := by
  cases n with
  | zero => rw [h.term_VD, h.term_VR]; exact hu (by linarith [hφ y])
  | succ n =>
    have hnT : n < T := hn
    have h1 := h.eq_24_11 n hnT b y 0 M.bmax_nonneg
    have h2 : M.u (M.inc y - M.φ (M.inc y)) ≤ M.u (M.inc y - b + q (n + 1) 0 y * 0) :=
      hu (by linarith [hφ y])
    have h3 := mul_le_mul_of_nonneg_left (ue_sum_mono M.markov (fun j =>
      (by rw [h.eq_24_9 n hnT.le]; exact le_max_left _ _ : VD n j ≤ V n 0 j)) y) M.β_nonneg
    rw [h.eq_24_10 n hnT]
    unfold obj at h1
    unfold defaultRHS
    linarith

/-- At every stage the repayment value is nonincreasing in debt. -/
theorem fh_VR_antitone (hu : Monotone M.u) {T : ℕ} {V VR D Bh q : ℕ → ℝ → Y → ℝ}
    {VD : ℕ → Y → ℝ} (h : IsFHEqm M T V VR VD D Bh q) {n : ℕ} (hn : n ≤ T) {b b'' : ℝ}
    (hbb : b ≤ b'') (y : Y) : VR n b'' y ≤ VR n b y := by
  cases n with
  | zero => rw [h.term_VR, h.term_VR]; exact hu (by linarith)
  | succ n =>
    have hnT : n < T := hn
    exact M.ue_VR_antitone hu (fun b y ε hε => ⟨Bh (n + 1) b y, h.borrow_le n hnT b y, by
      rw [h.borrow_opt n hnT b y]; linarith⟩) (h.eq_24_11 n hnT) hbb y

/-- **A modulus uniform in the stage**: if `|c − c′| < η` implies `|u(c) − u(c′)| < ε`, then at
every stage reducing debt by `h < η` raises `V^R` by less than `ε`. -/
theorem fh_VR_mod {ε η : ℝ} (hη : ∀ c c' : ℝ, dist c c' < η → dist (M.u c) (M.u c') < ε)
    {T : ℕ} {V VR D Bh q : ℕ → ℝ → Y → ℝ} {VD : ℕ → Y → ℝ} (h : IsFHEqm M T V VR VD D Bh q)
    {n : ℕ} (hn : n ≤ T) {b h' : ℝ} (h0 : 0 ≤ h') (hlt : h' < η) (y : Y) :
    VR n (b - h') y ≤ VR n b y + ε := by
  have hd : ∀ c : ℝ, dist (c + h') c < η := fun c => by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg h0]; exact hlt
  cases n with
  | zero =>
    rw [h.term_VR, h.term_VR]
    have h1 := hη _ _ (hd (M.inc y - b))
    rw [Real.dist_eq] at h1
    rw [show M.inc y - (b - h') = M.inc y - b + h' by ring]
    linarith [(abs_lt.1 h1).2]
  | succ n =>
    have hnT : n < T := hn
    set bh := Bh (n + 1) (b - h') y
    rw [← h.borrow_opt n hnT (b - h') y]
    have h2 := h.eq_24_11 n hnT b y bh (h.borrow_le n hnT _ y)
    have h1 := hη _ _ (hd (M.inc y - b + q (n + 1) bh y * bh))
    rw [Real.dist_eq] at h1
    unfold obj at h2 ⊢
    rw [show M.inc y - (b - h') + q (n + 1) bh y * bh =
      M.inc y - b + q (n + 1) bh y * bh + h' by ring]
    linarith [(abs_lt.1 h1).2]

/-- **The slope of the repayment value**: if `κ(c′ − c) ≤ u(c′) − u(c)` for `c ≤ c′ ≤ c̄` and
`Y + B̄/(1 + r) ≤ c̄` (consumption under repayment with debt `B ≥ 0` never exceeds `c̄`), then at
every stage reducing a debt `B` by `h ≤ B` raises `V^R` by at least `κh`. -/
theorem fh_VR_slope {κ cbar : ℝ}
    (hslope : ∀ c c', c ≤ c' → c' ≤ cbar → κ * (c' - c) ≤ M.u c' - M.u c)
    (hcap : ∀ y, M.inc y + M.bmax * (1 + M.r)⁻¹ ≤ cbar) {T : ℕ} {V VR D Bh q : ℕ → ℝ → Y → ℝ}
    {VD : ℕ → Y → ℝ} (h : IsFHEqm M T V VR VD D Bh q) {n : ℕ} (hn : n ≤ T) {b h' : ℝ}
    (h0 : 0 ≤ h') (hbh : 0 ≤ b - h') (y : Y) : VR n b y + κ * h' ≤ VR n (b - h') y := by
  have hs : 0 ≤ M.bmax * (1 + M.r)⁻¹ :=
    mul_nonneg M.bmax_nonneg (inv_nonneg.2 (by linarith [M.r_pos]))
  cases n with
  | zero =>
    rw [h.term_VR, h.term_VR]
    have h1 := hslope (M.inc y - b) (M.inc y - (b - h')) (by linarith) (by linarith [hcap y])
    rw [show M.inc y - (b - h') - (M.inc y - b) = h' by ring] at h1
    linarith
  | succ n =>
    have hnT : n < T := hn
    set bh := Bh (n + 1) b y
    have hbh' : bh ≤ M.bmax := h.borrow_le n hnT b y
    rw [← h.borrow_opt n hnT b y]
    have h2 := h.eq_24_11 n hnT (b - h') y bh hbh'
    have hq := M.fh_q_mem h hnT hbh' y
    have hrev := fh_rev_le (inv_nonneg.2 (by linarith [M.r_pos])) hq.1 hq.2 hbh' M.bmax_nonneg
    have h1 := hslope (M.inc y - b + q (n + 1) bh y * bh) (M.inc y - (b - h') +
      q (n + 1) bh y * bh) (by linarith) (by linarith [hcap y])
    rw [show M.inc y - (b - h') + q (n + 1) bh y * bh - (M.inc y - b + q (n + 1) bh y * bh) = h'
      by ring] at h1
    unfold obj at h2 ⊢
    linarith

/-- **The one-step comparison** (replication with an error): if repayment under `a₁` implies
repayment under `a₂` after a debt reduction `x`, and the continuation differences
`W − W^D` satisfy `W₁(B′) − W₁^D ≤ W₂(B′ − x) − W₂^D + e`, then issuing `B̂ − x` at the second
prices with debt `B − x/(1 + r)` does as well as issuing `B̂` at the first with debt `B`, up to
`βe` and the difference of the continuation default values. -/
theorem fh_compare (hu : Monotone M.u) {q₁ q₂ a₁ a₂ W₁ W₂ : ℝ → Y → ℝ} {WD₁ WD₂ : Y → ℝ}
    {x e : ℝ} (hx : 0 ≤ x) (hq₁ : ∀ b' y, b' ≤ M.bmax → q₁ b' y = M.price a₁ b' y)
    (hq₂ : ∀ b' y, b' ≤ M.bmax → q₂ b' y = M.price a₂ b' y)
    (ha₁ : ∀ b' j, 0 ≤ a₁ b' j ∧ a₁ b' j ≤ 1) (hneg₁ : ∀ b' j, b' ≤ 0 → a₁ b' j = 1)
    (hneg₂ : ∀ b' j, b' ≤ 0 → a₂ b' j = 1)
    (hdom : ∀ b' j, b' ≤ M.bmax → a₁ b' j ≤ a₂ (b' - x) j)
    (hW : ∀ b' j, W₁ b' j - WD₁ j ≤ W₂ (b' - x) j - WD₂ j + e) {b bh : ℝ} (y : Y)
    (hbh : bh ≤ M.bmax) :
    M.obj q₁ W₁ b y bh - M.β * ∑ j, M.P y j * WD₁ j ≤
      M.obj q₂ W₂ (b - x * (1 + M.r)⁻¹) y (bh - x) - M.β * ∑ j, M.P y j * WD₂ j +
        M.β * e := by
  have hrev := M.ue_revenue hx hq₁ hq₂ ha₁ hneg₁ hneg₂ hdom hbh y
  have hU := hu (show M.inc y - b + q₁ bh y * bh ≤
    M.inc y - (b - x * (1 + M.r)⁻¹) + q₂ (bh - x) y * (bh - x) by linarith)
  have hs : ∑ j, M.P y j * W₁ bh j - ∑ j, M.P y j * WD₁ j ≤
      ∑ j, M.P y j * W₂ (bh - x) j - ∑ j, M.P y j * WD₂ j + e := by
    have h1 := ue_sum_mono M.markov (fun j => hW bh j) y
    have h2 := ue_sum_add M.markov (fun j => W₂ (bh - x) j - WD₂ j) e y
    simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib] at h1 h2
    linarith
  have hs2 := mul_le_mul_of_nonneg_left hs M.β_nonneg
  unfold obj
  nlinarith [hs2]

/-- **The finite horizon never repays more than the equilibrium**: at every stage
`V^R_n − V^D_n ≤ V^R − V^D`. -/
theorem fh_upper (hu : Monotone M.u) (hφ : ∀ y, 0 ≤ M.φ (M.inc y))
    {V VR D Bh q : ℕ → ℝ → Y → ℝ} {VD : ℕ → Y → ℝ} (hfh : ∀ T, IsFHEqm M T V VR VD D Bh q)
    {Vs VRs Ds Bhs qs : ℝ → Y → ℝ} {VDs : Y → ℝ} (hs : IsOneMPE M Vs VRs VDs Ds Bhs qs) :
    ∀ n b y, VR n b y - VD n y ≤ VRs b y - VDs y := by
  intro n
  induction n with
  | zero =>
    intro b y
    have h0 := hfh 0
    rw [h0.term_VR, h0.term_VD]
    have h1 := hs.eq_24_11 b y 0 M.bmax_nonneg
    have h3 := mul_le_mul_of_nonneg_left (ue_sum_mono M.markov (fun j =>
      (by rw [hs.eq_24_9]; exact le_max_left _ _ : VDs j ≤ Vs 0 j)) y) M.β_nonneg
    have h4 := hs.eq_24_10 y
    unfold obj at h1
    unfold defaultRHS at h4
    simp only [mul_zero, add_zero] at h1
    linarith
  | succ n ih =>
    intro b y
    have h := hfh (n + 1)
    have hn : n < n + 1 := Nat.lt_succ_self n
    have hdom : ∀ b' j, b' ≤ M.bmax → 1 - D n b' j ≤ 1 - Ds (b' - 0) j := by
      intro b' j _
      rw [sub_zero, h.default_opt n hn.le, hs.default_opt]
      have := ih b' j
      split_ifs <;> first | (norm_num; done) | (exfalso; linarith)
    have hW : ∀ b' j, V n b' j - VD n j ≤ Vs (b' - 0) j - VDs j + 0 := by
      intro b' j
      rw [sub_zero, add_zero, h.eq_24_9 n hn.le, hs.eq_24_9]
      have := ih b' j
      rcases le_total (VD n j) (VR n b' j) with h1 | h1
      · rw [max_eq_right h1]; linarith [le_max_right (VDs j) (VRs b' j)]
      · rw [max_eq_left h1]; linarith [le_max_left (VDs j) (VRs b' j)]
    have hneg₁ : ∀ b' j, b' ≤ 0 → 1 - D n b' j = 1 := fun b' j hb => by
      rw [h.default_opt n hn.le, (fh_ite_zero _ _).2 (M.fh_repay_nonpos hu hφ h hn.le hb j),
        sub_zero]
    have hneg₂ : ∀ b' j, b' ≤ 0 → 1 - Ds b' j = 1 := fun b' j hb => by
      rw [hs.default_opt, (fh_ite_zero _ _).2 (M.ue_repay_nonpos hu hφ hs.eq_24_11
        (fun b y => by rw [hs.eq_24_9]; exact le_max_left _ _) hs.eq_24_10 hb j), sub_zero]
    have hc := M.fh_compare hu le_rfl (q₁ := q (n + 1)) (q₂ := qs)
      (a₁ := fun b j => 1 - D n b j) (a₂ := fun b j => 1 - Ds b j) (W₁ := V n) (W₂ := Vs)
      (WD₁ := VD n) (WD₂ := VDs) (e := 0) (b := b)
      (fun b' y hb' => h.eq_24_12 n hn b' y hb') (fun b' y hb' => hs.eq_24_12 b' y hb')
      (fun b' j => by rw [h.default_opt n hn.le]; exact fh_ite_mem _ _) hneg₁ hneg₂ hdom hW y
      (h.borrow_le n hn b y)
    rw [h.borrow_opt n hn b y] at hc
    simp only [zero_mul, sub_zero, mul_zero, add_zero] at hc
    have h2 := hs.eq_24_11 b y (Bh (n + 1) b y) (h.borrow_le n hn b y)
    rw [h.eq_24_10 n hn, hs.eq_24_10 y]
    unfold defaultRHS
    linarith

/-- The debt-reduction sequence of the lower bound: `g₀ = B̄/(1 + r)` and
`g_{n+1} = (gₙ + βⁿe₀/κ)/(1 + r)`. -/
noncomputable def fhShift (e₀ κ : ℝ) : ℕ → ℝ
  | 0 => M.bmax * (1 + M.r)⁻¹
  | n + 1 => (fhShift e₀ κ n + M.β ^ n * e₀ / κ) * (1 + M.r)⁻¹

/-- The debt reductions are nonnegative. -/
theorem fh_shift_nonneg {e₀ κ : ℝ} (he₀ : 0 ≤ e₀) (hκ : 0 < κ) (n : ℕ) :
    0 ≤ M.fhShift e₀ κ n := by
  have hρ : 0 ≤ (1 + M.r)⁻¹ := inv_nonneg.2 (by linarith [M.r_pos])
  induction n with
  | zero => exact mul_nonneg M.bmax_nonneg hρ
  | succ n ih =>
    exact mul_nonneg (add_nonneg ih (div_nonneg (mul_nonneg (pow_nonneg M.β_nonneg n) he₀)
      hκ.le)) hρ

/-- **The debt reductions vanish**: `g_{n+1} = Φₙ(gₙ)` with `Φₙ(g) = (g + βⁿe₀/κ)/(1 + r)`,
which converges uniformly to the contraction `Φ(g) = g/(1 + r)` with fixed point `0`
(`fh_moving_contraction`). -/
theorem fh_shift_tendsto (e₀ κ : ℝ) : Tendsto (M.fhShift e₀ κ) atTop (𝓝 0) := by
  set ρ := (1 + M.r)⁻¹ with hρdef
  have hρ0 : 0 ≤ ρ := inv_nonneg.2 (by linarith [M.r_pos])
  have hρ1 : ρ < 1 := inv_lt_one_of_one_lt₀ (by linarith [M.r_pos])
  have hε : Tendsto (fun n : ℕ => |ρ * (M.β ^ n * e₀ / κ)|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ρ * (M.β ^ n * e₀ / κ)) atTop (𝓝 (ρ * (0 * e₀ / κ))) :=
      (((tendsto_pow_atTop_nhds_zero_of_lt_one M.β_nonneg M.β_lt_one).mul_const e₀).div_const
        κ).const_mul ρ
    rw [zero_mul, zero_div, mul_zero] at h1
    simpa using h1.abs
  refine fh_moving_contraction (fun z => ρ * z) (fun n z => ρ * z + ρ * (M.β ^ n * e₀ / κ))
    hρ0 hρ1 (fun a c => ?_) (mul_zero ρ) hε (fun n z => ?_) (fun n => ?_)
  · rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg hρ0]
  · rw [Real.dist_eq, add_sub_cancel_left]
  · change (M.fhShift e₀ κ n + M.β ^ n * e₀ / κ) * ρ = _
    ring

/-- **The base of the lower bound**: with `V ≤ K` in the equilibrium,
`V^R − V^D ≤ V^R_0(B − B̄/(1 + r)) − V^D_0 + β(|K| + ‖V^D‖)`. -/
theorem fh_base (hu : Monotone M.u) {V VR D Bh q : ℕ → ℝ → Y → ℝ} {VD : ℕ → Y → ℝ}
    (hfh : ∀ T, IsFHEqm M T V VR VD D Bh q) {Vs VRs Ds Bhs qs : ℝ → Y → ℝ} {VDs : Y → ℝ}
    (hs : IsOneMPE M Vs VRs VDs Ds Bhs qs) :
    ∃ e₀, 0 ≤ e₀ ∧ ∀ b y, VRs b y - VDs y ≤
      VR 0 (b - M.bmax * (1 + M.r)⁻¹) y - VD 0 y + e₀ := by
  obtain ⟨K, hK⟩ := hs.bdd
  refine ⟨M.β * (|K| + ‖VDs‖), mul_nonneg M.β_nonneg (add_nonneg (abs_nonneg K)
    (norm_nonneg _)), fun b y => ?_⟩
  have h0 := hfh 0
  rw [h0.term_VR, h0.term_VD, ← hs.borrow_opt b y]
  set bh := Bhs b y
  have hbh : bh ≤ M.bmax := hs.borrow_le b y
  have hq := M.fh_mpe_q_mem hs hbh y
  have hrev := fh_rev_le (inv_nonneg.2 (by linarith [M.r_pos])) hq.1 hq.2 hbh M.bmax_nonneg
  have hU := hu (show M.inc y - b + qs bh y * bh ≤ M.inc y - (b - M.bmax * (1 + M.r)⁻¹) by
    linarith)
  have hS := mul_le_mul_of_nonneg_left (ue_sum_le M.markov (fun j => hK bh j) y) M.β_nonneg
  have hlow : -‖VDs‖ ≤ ∑ j, M.P y j * VDs j := ue_le_sum M.markov (fun j => by
    have h1 := norm_le_pi_norm VDs j
    rw [Real.norm_eq_abs] at h1
    linarith [neg_abs_le (VDs j)]) y
  have hS2 := mul_le_mul_of_nonneg_left hlow M.β_nonneg
  have hKa := mul_le_mul_of_nonneg_left (le_abs_self K) M.β_nonneg
  rw [hs.eq_24_10 y]
  unfold obj defaultRHS
  nlinarith

/-- **The domination step** (an error turned into a debt reduction): if
`V^R − V^D ≤ V^R_n(B − g) − V^D_n + e` everywhere, then every debt the equilibrium repays is
repaid at stage `n` after the reduction `g + e/κ` (by the slope `fh_VR_slope`, or because debt
`≤ 0` is always repaid). -/
theorem fh_dom (hu : Monotone M.u) (hφ : ∀ y, 0 ≤ M.φ (M.inc y)) {κ cbar : ℝ} (hκ : 0 < κ)
    (hslope : ∀ c c', c ≤ c' → c' ≤ cbar → κ * (c' - c) ≤ M.u c' - M.u c)
    (hcap : ∀ y, M.inc y + M.bmax * (1 + M.r)⁻¹ ≤ cbar) {T : ℕ} {V VR D Bh q : ℕ → ℝ → Y → ℝ}
    {VD : ℕ → Y → ℝ} (h : IsFHEqm M T V VR VD D Bh q) {n : ℕ} (hn : n ≤ T)
    {VRs : ℝ → Y → ℝ} {VDs : Y → ℝ} {g e : ℝ} (he : 0 ≤ e)
    (hL : ∀ b y, VRs b y - VDs y ≤ VR n (b - g) y - VD n y + e) {b : ℝ} {j : Y}
    (hb : VDs j ≤ VRs b j) : VD n j ≤ VR n (b - (g + e / κ)) j := by
  rcases lt_or_ge (b - (g + e / κ)) 0 with hneg | hpos
  · exact M.fh_repay_nonpos hu hφ h hn hneg.le j
  · have h1 := hL b j
    have h2 := M.fh_VR_slope hslope hcap h hn (b := b - g) (h' := e / κ) (div_nonneg he hκ.le)
      (by linarith) j
    rw [show κ * (e / κ) = e by field_simp, show b - g - e / κ = b - (g + e / κ) by ring] at h2
    linarith

/-- **The lower bound**: at every stage
`V^R − V^D ≤ V^R_n(B − gₙ) − V^D_n + βⁿe₀`, with the debt reductions `gₙ = fhShift e₀ κ n`. The
induction step is the one-step comparison (`fh_compare`) with the domination of `fh_dom`. -/
theorem fh_lower (hu : Monotone M.u) (hφ : ∀ y, 0 ≤ M.φ (M.inc y)) {κ cbar : ℝ} (hκ : 0 < κ)
    (hslope : ∀ c c', c ≤ c' → c' ≤ cbar → κ * (c' - c) ≤ M.u c' - M.u c)
    (hcap : ∀ y, M.inc y + M.bmax * (1 + M.r)⁻¹ ≤ cbar) {V VR D Bh q : ℕ → ℝ → Y → ℝ}
    {VD : ℕ → Y → ℝ} (hfh : ∀ T, IsFHEqm M T V VR VD D Bh q) {Vs VRs Ds Bhs qs : ℝ → Y → ℝ}
    {VDs : Y → ℝ} (hs : IsOneMPE M Vs VRs VDs Ds Bhs qs) {e₀ : ℝ} (he₀ : 0 ≤ e₀)
    (hbase : ∀ b y, VRs b y - VDs y ≤ VR 0 (b - M.bmax * (1 + M.r)⁻¹) y - VD 0 y + e₀) :
    ∀ n b y, VRs b y - VDs y ≤ VR n (b - M.fhShift e₀ κ n) y - VD n y + M.β ^ n * e₀ := by
  intro n
  induction n with
  | zero => intro b y; rw [pow_zero, one_mul]; exact hbase b y
  | succ n ih =>
    intro b y
    have h := hfh (n + 1)
    have hn : n < n + 1 := Nat.lt_succ_self n
    set g := M.fhShift e₀ κ n with hgdef
    set e := M.β ^ n * e₀ with hedef
    have hg : 0 ≤ g := M.fh_shift_nonneg he₀ hκ n
    have he : 0 ≤ e := mul_nonneg (pow_nonneg M.β_nonneg n) he₀
    set x := g + e / κ with hxdef
    have hx : 0 ≤ x := add_nonneg hg (div_nonneg he hκ.le)
    have hdom : ∀ b' j, b' ≤ M.bmax → 1 - Ds b' j ≤ 1 - D n (b' - x) j := by
      intro b' j _
      rw [hs.default_opt, h.default_opt n hn.le]
      by_cases hd : VRs b' j < VDs j
      · simp only [hd, ↓reduceIte, sub_self]
        exact (fh_ite_mem _ _).1
      · rw [(fh_ite_zero _ _).2 (not_lt.1 hd),
          (fh_ite_zero _ _).2 (M.fh_dom hu hφ hκ hslope hcap h hn.le he ih (not_lt.1 hd))]
    have hW : ∀ b' j, Vs b' j - VDs j ≤ V n (b' - x) j - VD n j + e := by
      intro b' j
      rw [hs.eq_24_9, h.eq_24_9 n hn.le]
      have h1 := ih b' j
      have h2 := M.fh_VR_antitone hu h hn.le (show b' - x ≤ b' - g by
        linarith [div_nonneg he hκ.le]) j
      have h3 := le_max_left (VD n j) (VR n (b' - x) j)
      have h4 := le_max_right (VD n j) (VR n (b' - x) j)
      rcases le_total (VDs j) (VRs b' j) with h5 | h5
      · rw [max_eq_right h5]; linarith
      · rw [max_eq_left h5]; linarith
    have hneg₁ : ∀ b' j, b' ≤ 0 → 1 - Ds b' j = 1 := fun b' j hb => by
      rw [hs.default_opt, (fh_ite_zero _ _).2 (M.ue_repay_nonpos hu hφ hs.eq_24_11
        (fun b y => by rw [hs.eq_24_9]; exact le_max_left _ _) hs.eq_24_10 hb j), sub_zero]
    have hneg₂ : ∀ b' j, b' ≤ 0 → 1 - D n b' j = 1 := fun b' j hb => by
      rw [h.default_opt n hn.le, (fh_ite_zero _ _).2 (M.fh_repay_nonpos hu hφ h hn.le hb j),
        sub_zero]
    have hc := M.fh_compare hu hx (q₁ := qs) (q₂ := q (n + 1))
      (a₁ := fun b j => 1 - Ds b j) (a₂ := fun b j => 1 - D n b j) (W₁ := Vs) (W₂ := V n)
      (WD₁ := VDs) (WD₂ := VD n) (e := e) (b := b)
      (fun b' y hb' => hs.eq_24_12 b' y hb') (fun b' y hb' => h.eq_24_12 n hn b' y hb')
      (fun b' j => by rw [hs.default_opt]; exact fh_ite_mem _ _) hneg₁ hneg₂ hdom hW y
      (hs.borrow_le b y)
    rw [hs.borrow_opt b y] at hc
    have h2 := h.eq_24_11 n hn (b - x * (1 + M.r)⁻¹) y (Bhs b y - x)
      (by linarith [hs.borrow_le b y])
    have hsh : M.fhShift e₀ κ (n + 1) = x * (1 + M.r)⁻¹ := rfl
    rw [hsh, h.eq_24_10 n hn, hs.eq_24_10 y, pow_succ]
    unfold defaultRHS
    have : M.β ^ n * M.β * e₀ = M.β * e := by rw [hedef]; ring
    rw [this]
    linarith

/-- **The default values converge**: `|V^D_n − V^D| ≤ βⁿ‖V^D_0 − V^D‖`. -/
theorem fh_VD_bound {V VR D Bh q : ℕ → ℝ → Y → ℝ} {VD : ℕ → Y → ℝ}
    (hfh : ∀ T, IsFHEqm M T V VR VD D Bh q) {VDs : Y → ℝ}
    (hVDs : ∀ y, VDs y = M.defaultRHS VDs y) :
    ∀ n y, |VD n y - VDs y| ≤ M.β ^ n * ‖fun y => VD 0 y - VDs y‖ := by
  intro n
  induction n with
  | zero =>
    intro y
    rw [pow_zero, one_mul]
    have := norm_le_pi_norm (fun y => VD 0 y - VDs y) y
    rwa [Real.norm_eq_abs] at this
  | succ n ih =>
    intro y
    have h := hfh (n + 1)
    have hd : VD (n + 1) y - VDs y = M.β * ∑ j, M.P y j * (VD n j - VDs j) := by
      rw [h.eq_24_10 n (Nat.lt_succ_self n), hVDs y]
      unfold defaultRHS
      simp only [mul_sub, sum_sub_distrib]
      ring
    have hs : |∑ j, M.P y j * (VD n j - VDs j)| ≤ M.β ^ n * ‖fun y => VD 0 y - VDs y‖ :=
      calc |∑ j, M.P y j * (VD n j - VDs j)| ≤ ∑ j, |M.P y j * (VD n j - VDs j)| :=
            abs_sum_le_sum_abs _ _
        _ = ∑ j, M.P y j * |VD n j - VDs j| := by
            refine sum_congr rfl fun j _ => ?_
            rw [abs_mul, abs_of_nonneg (M.markov.nonneg y j)]
        _ ≤ _ := ue_sum_le M.markov ih y
    rw [hd, abs_mul, abs_of_nonneg M.β_nonneg, pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left hs M.β_nonneg]

/-- **The default sets converge** (AKMM, p. 901, beyond the text): with a finite horizon the
sovereign defaults at least as often (`D̂_n = 0 ⇒ D̂ = 0`), and every debt `B` the equilibrium
repays is repaid at stage `n` after a debt reduction `xₙ → 0`. -/
theorem fh_default_sets (hu : Monotone M.u) (hφ : ∀ y, 0 ≤ M.φ (M.inc y)) {κ cbar : ℝ}
    (hκ : 0 < κ) (hslope : ∀ c c', c ≤ c' → c' ≤ cbar → κ * (c' - c) ≤ M.u c' - M.u c)
    (hcap : ∀ y, M.inc y + M.bmax * (1 + M.r)⁻¹ ≤ cbar) {V VR D Bh q : ℕ → ℝ → Y → ℝ}
    {VD : ℕ → Y → ℝ} (hfh : ∀ T, IsFHEqm M T V VR VD D Bh q) {Vs VRs Ds Bhs qs : ℝ → Y → ℝ}
    {VDs : Y → ℝ} (hs : IsOneMPE M Vs VRs VDs Ds Bhs qs) :
    ∃ x : ℕ → ℝ, (∀ n, 0 ≤ x n) ∧ Tendsto x atTop (𝓝 0) ∧
      (∀ n b y, Ds b y = 0 → D n (b - x n) y = 0) ∧ ∀ n b y, D n b y = 0 → Ds b y = 0 := by
  obtain ⟨e₀, he₀, hbase⟩ := M.fh_base hu hfh hs
  have hL := M.fh_lower hu hφ hκ hslope hcap hfh hs he₀ hbase
  have hU := M.fh_upper hu hφ hfh hs
  refine ⟨fun n => M.fhShift e₀ κ n + M.β ^ n * e₀ / κ, fun n => add_nonneg
    (M.fh_shift_nonneg he₀ hκ n) (div_nonneg (mul_nonneg (pow_nonneg M.β_nonneg n) he₀) hκ.le),
    ?_, fun n b y hb => ?_, fun n b y hb => ?_⟩
  · have h1 := (M.fh_shift_tendsto e₀ κ).add (((tendsto_pow_atTop_nhds_zero_of_lt_one
      M.β_nonneg M.β_lt_one).mul_const e₀).div_const κ)
    simpa using h1
  · have h := hfh n
    rw [hs.default_opt] at hb
    rw [h.default_opt n le_rfl]
    exact (fh_ite_zero _ _).2 (M.fh_dom hu hφ hκ hslope hcap h le_rfl
      (mul_nonneg (pow_nonneg M.β_nonneg n) he₀) (hL n) ((fh_ite_zero _ _).1 hb))
  · have h := hfh n
    rw [h.default_opt n le_rfl] at hb
    rw [hs.default_opt]
    have := hU n b y
    exact (fh_ite_zero _ _).2 (by linarith [(fh_ite_zero _ _).1 hb])

/-- The debt capacity of a repayment value: the largest debt in `[0, B̄]` that is repaid. -/
noncomputable def fhCap (VR : ℝ → Y → ℝ) (VD : Y → ℝ) (j : Y) : ℝ :=
  sSup {b | 0 ≤ b ∧ b ≤ M.bmax ∧ VD j ≤ VR b j}

/-- **The debt capacities converge** (AKMM, p. 901, beyond the text): the finite-horizon
capacity `b̄ₙ(Y)` lies in `[b̄(Y) − xₙ, b̄(Y)]` with `xₙ → 0`, so `b̄ₙ(Y) → b̄(Y)`. -/
theorem fh_capacity_tendsto (hu : Monotone M.u) (hφ : ∀ y, 0 ≤ M.φ (M.inc y)) {κ cbar : ℝ}
    (hκ : 0 < κ) (hslope : ∀ c c', c ≤ c' → c' ≤ cbar → κ * (c' - c) ≤ M.u c' - M.u c)
    (hcap : ∀ y, M.inc y + M.bmax * (1 + M.r)⁻¹ ≤ cbar) {V VR D Bh q : ℕ → ℝ → Y → ℝ}
    {VD : ℕ → Y → ℝ} (hfh : ∀ T, IsFHEqm M T V VR VD D Bh q) {Vs VRs Ds Bhs qs : ℝ → Y → ℝ}
    {VDs : Y → ℝ} (hs : IsOneMPE M Vs VRs VDs Ds Bhs qs) :
    ∃ x : ℕ → ℝ, (∀ n, 0 ≤ x n) ∧ Tendsto x atTop (𝓝 0) ∧
      (∀ n j, M.fhCap VRs VDs j - x n ≤ M.fhCap (VR n) (VD n) j ∧
        M.fhCap (VR n) (VD n) j ≤ M.fhCap VRs VDs j) ∧
      ∀ j, Tendsto (fun n => M.fhCap (VR n) (VD n) j) atTop (𝓝 (M.fhCap VRs VDs j)) := by
  obtain ⟨x, hx0, hx, hdom, hrev⟩ := M.fh_default_sets hu hφ hκ hslope hcap hfh hs
  have hbound : ∀ n j, M.fhCap VRs VDs j - x n ≤ M.fhCap (VR n) (VD n) j ∧
      M.fhCap (VR n) (VD n) j ≤ M.fhCap VRs VDs j := by
    intro n j
    have h := hfh n
    have hzn : ∀ b, (D n b j = 0 ↔ VD n j ≤ VR n b j) := fun b => by
      rw [h.default_opt n le_rfl]; exact fh_ite_zero _ _
    have hzs : ∀ b, (Ds b j = 0 ↔ VDs j ≤ VRs b j) := fun b => by
      rw [hs.default_opt]; exact fh_ite_zero _ _
    have h0n : (0 : ℝ) ∈ {b | 0 ≤ b ∧ b ≤ M.bmax ∧ VD n j ≤ VR n b j} :=
      ⟨le_rfl, M.bmax_nonneg, M.fh_repay_nonpos hu hφ h le_rfl le_rfl j⟩
    have h0s : (0 : ℝ) ∈ {b | 0 ≤ b ∧ b ≤ M.bmax ∧ VDs j ≤ VRs b j} :=
      ⟨le_rfl, M.bmax_nonneg, M.ue_repay_nonpos hu hφ hs.eq_24_11
        (fun b y => by rw [hs.eq_24_9]; exact le_max_left _ _) hs.eq_24_10 le_rfl j⟩
    have hbs : BddAbove {b | 0 ≤ b ∧ b ≤ M.bmax ∧ VDs j ≤ VRs b j} :=
      ⟨M.bmax, fun b hb => hb.2.1⟩
    have hbn : BddAbove {b | 0 ≤ b ∧ b ≤ M.bmax ∧ VD n j ≤ VR n b j} :=
      ⟨M.bmax, fun b hb => hb.2.1⟩
    constructor
    · have : M.fhCap VRs VDs j ≤ M.fhCap (VR n) (VD n) j + x n := by
        unfold fhCap
        refine csSup_le ⟨0, h0s⟩ fun b hb => ?_
        rcases le_total (b - x n) 0 with h1 | h1
        · linarith [le_csSup hbn h0n]
        · have hm : b - x n ∈ {b | 0 ≤ b ∧ b ≤ M.bmax ∧ VD n j ≤ VR n b j} :=
            ⟨h1, by linarith [hb.2.1, hx0 n], (hzn _).1 (hdom n b j ((hzs b).2 hb.2.2))⟩
          linarith [le_csSup hbn hm]
      linarith
    · exact csSup_le_csSup hbs ⟨0, h0n⟩ fun b hb =>
        ⟨hb.1, hb.2.1, (hzs b).1 (hrev n b j ((hzn b).2 hb.2.2))⟩
  refine ⟨x, hx0, hx, hbound, fun j => ?_⟩
  have hl : Tendsto (fun n => M.fhCap VRs VDs j - x n) atTop (𝓝 (M.fhCap VRs VDs j - 0)) :=
    tendsto_const_nhds.sub hx
  rw [sub_zero] at hl
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds
    (fun n => (hbound n j).1) (fun n => (hbound n j).2)

/-- **The values converge uniformly** (AKMM, p. 901, beyond the text): `V^D_n → V^D`,
`V^R_n → V^R` and `V_n → V` uniformly in `(B, Y)`. -/
theorem fh_values_tendsto (hu : Monotone M.u) (huc : UniformContinuous M.u)
    (hφ : ∀ y, 0 ≤ M.φ (M.inc y)) {κ cbar : ℝ} (hκ : 0 < κ)
    (hslope : ∀ c c', c ≤ c' → c' ≤ cbar → κ * (c' - c) ≤ M.u c' - M.u c)
    (hcap : ∀ y, M.inc y + M.bmax * (1 + M.r)⁻¹ ≤ cbar) {V VR D Bh q : ℕ → ℝ → Y → ℝ}
    {VD : ℕ → Y → ℝ} (hfh : ∀ T, IsFHEqm M T V VR VD D Bh q) {Vs VRs Ds Bhs qs : ℝ → Y → ℝ}
    {VDs : Y → ℝ} (hs : IsOneMPE M Vs VRs VDs Ds Bhs qs) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ b y, |VD n y - VDs y| ≤ ε ∧ |VR n b y - VRs b y| ≤ ε ∧
      |V n b y - Vs b y| ≤ ε := by
  intro ε hε
  obtain ⟨e₀, he₀, hbase⟩ := M.fh_base hu hfh hs
  have hL := M.fh_lower hu hφ hκ hslope hcap hfh hs he₀ hbase
  have hU := M.fh_upper hu hφ hfh hs
  have hB := M.fh_VD_bound hfh hs.eq_24_10
  obtain ⟨η, hη, hηu⟩ := Metric.uniformContinuous_iff.1 huc (ε / 3) (by linarith)
  set C := ‖fun y => VD 0 y - VDs y‖
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one M.β_nonneg M.β_lt_one
  have t1 : ∀ᶠ n in atTop, M.fhShift e₀ κ n < η :=
    (M.fh_shift_tendsto e₀ κ).eventually (Iio_mem_nhds hη)
  have t2 : ∀ᶠ n in atTop, M.β ^ n * e₀ < ε / 3 := by
    have h1 := hpow.mul_const e₀
    rw [zero_mul] at h1
    exact h1.eventually (Iio_mem_nhds (by linarith))
  have t3 : ∀ᶠ n in atTop, M.β ^ n * C < ε / 3 := by
    have h1 := hpow.mul_const C
    rw [zero_mul] at h1
    exact h1.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((t1.and t2).and t3)
  refine ⟨N, fun n hn b y => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hN n hn
  have h := hfh n
  have hVD : |VD n y - VDs y| ≤ ε / 3 := (hB n y).trans h3.le
  have hm := M.fh_VR_mod (fun c c' hc => hηu hc) h le_rfl (b := b)
    (M.fh_shift_nonneg he₀ hκ n) h1 y
  have hu1 := hU n b y
  have hl1 := hL n b y
  have hVR : |VR n b y - VRs b y| ≤ ε := by
    rw [abs_le] at hVD ⊢
    constructor <;> linarith
  refine ⟨by linarith, hVR, ?_⟩
  rw [h.eq_24_9 n le_rfl, hs.eq_24_9]
  exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by linarith) hVR)

/-- **The prices and default rules converge** (AKMM, p. 901, beyond the text): the
finite-horizon prices lie between `q(B′ + xₙ)` and `q(B′)` with `xₙ → 0`; wherever the
equilibrium default rule is constant on some `[B, B + η]` (everywhere except at the
capacities), the default rules and prices of the finite-horizon game are eventually those of
the equilibrium. -/
theorem fh_price_tendsto (hu : Monotone M.u) (hφ : ∀ y, 0 ≤ M.φ (M.inc y)) {κ cbar : ℝ}
    (hκ : 0 < κ) (hslope : ∀ c c', c ≤ c' → c' ≤ cbar → κ * (c' - c) ≤ M.u c' - M.u c)
    (hcap : ∀ y, M.inc y + M.bmax * (1 + M.r)⁻¹ ≤ cbar) {V VR D Bh q : ℕ → ℝ → Y → ℝ}
    {VD : ℕ → Y → ℝ} (hfh : ∀ T, IsFHEqm M T V VR VD D Bh q) {Vs VRs Ds Bhs qs : ℝ → Y → ℝ}
    {VDs : Y → ℝ} (hs : IsOneMPE M Vs VRs VDs Ds Bhs qs) :
    ∃ x : ℕ → ℝ, (∀ n, 0 ≤ x n) ∧ Tendsto x atTop (𝓝 0) ∧
      (∀ n b' y, b' ≤ M.bmax → q (n + 1) b' y ≤ qs b' y) ∧
      (∀ n b' y, b' + x n ≤ M.bmax → qs (b' + x n) y ≤ q (n + 1) b' y) ∧
      ∀ b, (∃ η > 0, ∀ j, Ds (b + η) j = Ds b j) →
        ∀ᶠ n in atTop, (∀ j, D n b j = Ds b j) ∧ ∀ y, b ≤ M.bmax → q (n + 1) b y = qs b y := by
  obtain ⟨x, hx0, hx, hdom, hrev⟩ := M.fh_default_sets hu hφ hκ hslope hcap hfh hs
  have h01 : ∀ a c : ℝ, (if a < c then (1 : ℝ) else 0) = 0 ∨ (if a < c then (1 : ℝ) else 0) = 1 :=
    fun a c => by split_ifs <;> simp
  have hanti : ∀ {b b'' : ℝ}, b ≤ b'' → ∀ j, VRs b'' j ≤ VRs b j := fun hbb j =>
    M.ue_VR_antitone hu (M.ue_mpe_sup hs) hs.eq_24_11 hbb j
  have hDmono : ∀ {b b'' : ℝ}, b ≤ b'' → ∀ j, Ds b j ≤ Ds b'' j := fun hbb j => by
    rw [hs.default_opt, hs.default_opt]
    have := hanti hbb j
    split_ifs <;> first | (norm_num; done) | (exfalso; linarith)
  have hDle : ∀ n b j, Ds b j ≤ D n b j := fun n b j => by
    rcases h01 (VR n b j) (VD n j) with h | h
    · have h' : D n b j = 0 := by rw [(hfh n).default_opt n le_rfl]; exact h
      rw [h', hrev n b j h']
    · have h' : D n b j = 1 := by rw [(hfh n).default_opt n le_rfl]; exact h
      rw [h', hs.default_opt]
      linarith [(fh_ite_mem (VRs b j) (VDs j)).1]
  have hDle2 : ∀ n b j, D n b j ≤ Ds (b + x n) j := fun n b j => by
    rcases h01 (VRs (b + x n) j) (VDs j) with h | h
    · have h' : Ds (b + x n) j = 0 := by rw [hs.default_opt]; exact h
      have := hdom n (b + x n) j h'
      rw [add_sub_cancel_right] at this
      rw [this, h']
    · have h' : Ds (b + x n) j = 1 := by rw [hs.default_opt]; exact h
      rw [h', (hfh n).default_opt n le_rfl]
      linarith [(fh_ite_mem (VR n b j) (VD n j)).1]
  have hprice : ∀ n b' y, b' ≤ M.bmax → q (n + 1) b' y = M.price (fun b j => 1 - D n b j) b' y :=
    fun n b' y hb' => (hfh (n + 1)).eq_24_12 n (Nat.lt_succ_self n) b' y hb'
  have hprices : ∀ b' y, b' ≤ M.bmax → qs b' y = M.price (fun b j => 1 - Ds b j) b' y :=
    fun b' y hb' => hs.eq_24_12 b' y hb'
  refine ⟨x, hx0, hx, fun n b' y hb' => ?_, fun n b' y hb' => ?_, fun b ⟨η, hη, hloc⟩ => ?_⟩
  · rw [hprice n b' y hb', hprices b' y hb']
    exact M.ue_price_mono (fun j => by linarith [hDle n b' j]) y
  · rw [hprice n b' y (by linarith [hx0 n]), hprices _ y hb']
    exact M.ue_price_mono (fun j => by linarith [hDle2 n b' j]) y
  · filter_upwards [hx.eventually (Iio_mem_nhds hη)] with n hn
    have hD : ∀ j, D n b j = Ds b j := fun j => by
      have h1 := hDle n b j
      have h2 := hDle2 n b j
      have h3 := hDmono (show b + x n ≤ b + η by linarith) j
      have h4 := hloc j
      linarith
    refine ⟨hD, fun y hb => ?_⟩
    rw [hprice n b y hb, hprices b y hb]
    unfold price
    simp only [hD]

/-- **Optimal borrowing exists against a continuation continuous in debt** (the finite-horizon
version of `ue_attain`): at the prices of nonnegative capacities, with `W` continuous in debt
and savings beyond `K₀` useless (`W(B′) ≤ W(−K₀)` for `B′ ≤ −K₀`), the objective attains its
maximum over `B′ ≤ B̄`. -/
theorem fh_attain (hu : Monotone M.u) (huc : UniformContinuous M.u) {bt : Y → ℝ}
    (hbt : ∀ j, 0 ≤ bt j) {W : ℝ → Y → ℝ} (hWc : ∀ j, Continuous fun b => W b j) {K₀ : ℝ}
    (hK₀ : 0 ≤ K₀) (hWs : ∀ b' j, b' ≤ -K₀ → W b' j ≤ W (-K₀) j) (b : ℝ) (y : Y) :
    ∃ b', b' ≤ M.bmax ∧ ∀ b'', b'' ≤ M.bmax →
      M.obj (M.price (ue_thr bt)) W b y b'' ≤ M.obj (M.price (ue_thr bt)) W b y b' := by
  have hr1 : 0 < 1 + M.r := by linarith [M.r_pos]
  have hqneg : ∀ b' y, b' ≤ 0 → M.price (ue_thr bt) b' y = (1 + M.r)⁻¹ := fun b' y hb' =>
    M.ue_price_one (fun j => ue_thr_nonpos hbt hb' j) y
  have hred : ∀ b', b' ≤ -K₀ →
      M.obj (M.price (ue_thr bt)) W b y b' ≤ M.obj (M.price (ue_thr bt)) W b y (-K₀) := by
    intro b' hb'
    unfold obj
    rw [hqneg b' y (by linarith), hqneg (-K₀) y (by linarith)]
    have h1 : M.u (M.inc y - b + (1 + M.r)⁻¹ * b') ≤ M.u (M.inc y - b + (1 + M.r)⁻¹ * -K₀) :=
      hu (by linarith [mul_le_mul_of_nonneg_left hb' (inv_nonneg.2 hr1.le)])
    have h2 : ∑ j, M.P y j * W b' j ≤ ∑ j, M.P y j * W (-K₀) j :=
      ue_sum_mono M.markov (fun j => hWs b' j hb') y
    nlinarith [mul_le_mul_of_nonneg_left h2 M.β_nonneg]
  have hrev : ∀ b', M.price (ue_thr bt) b' y * b' = (1 + M.r)⁻¹ *
      ∑ j, M.P y j * (b' ⊓ (Set.Iic (bt j)).indicator (fun _ => bt j) b') := by
    intro b'
    unfold price ue_thr
    rw [mul_assoc, sum_mul]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [mul_assoc]
    congr 1
    split_ifs with h
    · rw [Set.indicator_of_mem (Set.mem_Iic.2 h), one_mul, inf_eq_left.2 h]
    · rw [Set.indicator_of_notMem (fun h' => h (Set.mem_Iic.1 h')), zero_mul,
        inf_eq_right.2 (by linarith [hbt j, not_le.1 h])]
  have hsc : ∀ (c : ℝ) {f : ℝ → ℝ}, 0 ≤ c → UpperSemicontinuous f →
      UpperSemicontinuous fun x => c * f x := fun c f hc hf =>
    (continuous_const.mul continuous_id).comp_upperSemicontinuous hf
      (fun a b h => mul_le_mul_of_nonneg_left h hc)
  have ht : ∀ j, UpperSemicontinuous fun b' : ℝ =>
      b' ⊓ (Set.Iic (bt j)).indicator (fun _ => bt j) b' := fun j =>
    continuous_id.upperSemicontinuous.inf (isClosed_Iic.upperSemicontinuous_indicator (hbt j))
  have hR : UpperSemicontinuous fun b' : ℝ => (1 + M.r)⁻¹ *
      ∑ j, M.P y j * (b' ⊓ (Set.Iic (bt j)).indicator (fun _ => bt j) b') :=
    hsc _ (inv_nonneg.2 hr1.le)
      (upperSemicontinuous_sum fun j _ => hsc _ (M.markov.nonneg y j) (ht j))
  have hgc : Continuous fun z : ℝ => M.inc y - b + z := continuous_const.add continuous_id
  have hU : UpperSemicontinuous fun b' : ℝ => M.u (M.inc y - b + (1 + M.r)⁻¹ *
      ∑ j, M.P y j * (b' ⊓ (Set.Iic (bt j)).indicator (fun _ => bt j) b')) :=
    (huc.continuous.comp hgc).comp_upperSemicontinuous hR (fun a c h => hu (by linarith))
  have hC : Continuous fun b' : ℝ => M.β * ∑ j, M.P y j * W b' j :=
    continuous_const.mul (continuous_finsetSum _ fun j _ => continuous_const.mul (hWc j))
  have husc : UpperSemicontinuous fun b' => M.obj (M.price (ue_thr bt)) W b y b' := by
    have heq : (fun b' => M.obj (M.price (ue_thr bt)) W b y b') = fun b' =>
        M.u (M.inc y - b + (1 + M.r)⁻¹ *
          ∑ j, M.P y j * (b' ⊓ (Set.Iic (bt j)).indicator (fun _ => bt j) b')) +
        M.β * ∑ j, M.P y j * W b' j := funext fun b' => by
      unfold obj
      rw [hrev b']
    rw [heq]
    exact hU.add hC.upperSemicontinuous
  obtain ⟨bs, hbs, hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn
    (⟨0, by linarith, M.bmax_nonneg⟩ : (Set.Icc (-K₀) M.bmax).Nonempty) isCompact_Icc
    (husc.upperSemicontinuousOn _)
  refine ⟨bs, hbs.2, fun b'' hb'' => ?_⟩
  rcases le_total (-K₀) b'' with h | h
  · exact isMaxOn_iff.1 hmax _ ⟨h, hb''⟩
  · exact (hred _ h).trans (isMaxOn_iff.1 hmax _ ⟨le_rfl, by linarith [M.bmax_nonneg]⟩)

/-- The constructed default values: `V^D_0 = u(Y − φ(Y))`, `V^D_{n+1} = u(Y − φ) + βE V^D_n`. -/
noncomputable def fhVD : ℕ → Y → ℝ
  | 0 => fun y => M.u (M.inc y - M.φ (M.inc y))
  | n + 1 => fun y => M.defaultRHS (fhVD n) y

/-- The constructed repayment values: `V^R_0(B, Y) = u(Y − B)` and `V^R_{n+1}` the supremum of
the objective at the prices `(1 + r)⁻¹E[1 − D̂_n]` with continuation `max(V^D_n, V^R_n)`. -/
noncomputable def fhVR : ℕ → ℝ → Y → ℝ
  | 0 => fun b y => M.u (M.inc y - b)
  | n + 1 => M.VRsup (M.price fun b' j => 1 - (if fhVR n b' j < M.fhVD n j then 1 else 0))
      (fun b y => max (M.fhVD n y) (fhVR n b y))

/-- The constructed values `V_n = max(V^D_n, V^R_n)`. -/
noncomputable def fhV (n : ℕ) (b : ℝ) (y : Y) : ℝ := max (M.fhVD n y) (M.fhVR n b y)

/-- The constructed default rules (ties repaid). -/
noncomputable def fhD (n : ℕ) (b : ℝ) (y : Y) : ℝ :=
  if M.fhVR n b y < M.fhVD n y then 1 else 0

/-- The constructed prices: `q₀ = 0`, `q_{n+1} = (1 + r)⁻¹E[1 − D̂_n]`. -/
noncomputable def fhq : ℕ → ℝ → Y → ℝ
  | 0 => fun _ _ => 0
  | n + 1 => M.price fun b' j => 1 - M.fhD n b' j

/-- The best value with `n` periods left: `U_0 = ū`, `U_{n+1} = ū + βUₙ`. -/
noncomputable def fhU (ub : ℝ) : ℕ → ℝ
  | 0 => ub
  | n + 1 => ub + M.β * fhU ub n

/-- **The stages of the constructed sequence**: values bounded by `Uₙ`, which a sovereign with
savings `K₀` attains; `V^R_n` continuous and nonincreasing in debt; debt `≤ 0` repaid. -/
theorem fh_stage (hu : Monotone M.u) (huc : UniformContinuous M.u) {cbar : ℝ}
    (hsat : ∀ c, cbar ≤ c → M.u c = M.u cbar) (hφ : ∀ y, 0 ≤ M.φ (M.inc y)) {K₀ : ℝ}
    (hcons : ∀ j, cbar ≤ M.inc j - -K₀ + (1 + M.r)⁻¹ * -K₀) (hK₀ : 0 ≤ K₀) (n : ℕ) :
    (∀ b j, M.fhV n b j ≤ M.fhU (M.u cbar) n) ∧ (∀ j, M.fhU (M.u cbar) n ≤ M.fhVR n (-K₀) j) ∧
      (∀ j, Continuous fun b => M.fhVR n b j) ∧
      (∀ b b' j, b ≤ b' → M.fhVR n b' j ≤ M.fhVR n b j) ∧
      ∀ b j, b ≤ 0 → M.fhVD n j ≤ M.fhVR n b j := by
  have hub := M.ue_u_le hu hsat
  have hr1 : 0 < 1 + M.r := by linarith [M.r_pos]
  induction n with
  | zero =>
    refine ⟨fun b j => max_le (hub _) (hub _), fun j => ?_,
      fun j => huc.continuous.comp (continuous_const.sub continuous_id),
      fun b b' j h => hu (by linarith), fun b j hb => hu (by linarith [hφ j])⟩
    have h1 : cbar ≤ M.inc j - -K₀ := by
      have := hcons j
      nlinarith [mul_nonneg (inv_nonneg.2 hr1.le) hK₀]
    exact le_of_eq (hsat _ h1).symm
  | succ n ih =>
    obtain ⟨ia, ib, ic, id, ie⟩ := ih
    have hR : M.fhVR (n + 1) = M.VRsup (M.fhq (n + 1)) (M.fhV n) := rfl
    have hVD1 : ∀ j, M.fhVD (n + 1) j = M.defaultRHS (M.fhVD n) j := fun j => rfl
    have hU1 : M.fhU (M.u cbar) (n + 1) = M.u cbar + M.β * M.fhU (M.u cbar) n := rfl
    have hle : ∀ b y b', b' ≤ M.bmax → M.obj (M.fhq (n + 1)) (M.fhV n) b y b' ≤
        M.VRsup (M.fhq (n + 1)) (M.fhV n) b y := fun b y _ hb' => M.ue_VRsup_le hub ia b y hb'
    have hsup := M.ue_VRsup_sup (M.fhq (n + 1)) (M.fhV n)
    have hVDW : ∀ b j, M.fhVD n j ≤ M.fhV n b j := fun b j => le_max_left _ _
    refine ⟨fun b j => ?_, fun j => ?_, fun j => ?_, fun b b' j h => ?_, fun b j hb => ?_⟩
    · change max (M.fhVD (n + 1) j) (M.fhVR (n + 1) b j) ≤ _
      rw [hR, hVD1, hU1]
      refine max_le ?_ (M.ue_VRsup_ub hub ia b j)
      unfold defaultRHS
      have := mul_le_mul_of_nonneg_left (ue_sum_le M.markov (fun i => (hVDW 0 i).trans
        (ia 0 i)) j) M.β_nonneg
      linarith [hub (M.inc j - M.φ (M.inc j))]
    · rw [hR, hU1]
      have h1 := hle (-K₀) j (-K₀) (by linarith [M.bmax_nonneg])
      have hq : M.fhq (n + 1) (-K₀) j = (1 + M.r)⁻¹ := by
        change M.price (fun b' j => 1 - M.fhD n b' j) (-K₀) j = _
        exact M.ue_price_one (fun i => by
          change 1 - (if M.fhVR n (-K₀) i < M.fhVD n i then 1 else 0) = 1
          rw [(fh_ite_zero _ _).2 (ie (-K₀) i (by linarith)), sub_zero]) j
      have h2 : M.obj (M.fhq (n + 1)) (M.fhV n) (-K₀) j (-K₀) =
          M.u cbar + M.β * ∑ i, M.P j i * M.fhV n (-K₀) i := by
        unfold obj
        rw [hq, hsat _ (hcons j)]
      have h3 : M.β * M.fhU (M.u cbar) n ≤ M.β * ∑ i, M.P j i * M.fhV n (-K₀) i :=
        mul_le_mul_of_nonneg_left (ue_le_sum M.markov (fun i => (ib i).trans
          (le_max_right _ _ : M.fhVR n (-K₀) i ≤ M.fhV n (-K₀) i)) j) M.β_nonneg
      linarith
    · rw [hR]
      refine Metric.continuous_iff.2 fun b₀ ε hε => ?_
      obtain ⟨η, hη, hmod⟩ := M.ue_modulus huc hsup hle (half_pos hε)
      refine ⟨η, hη, fun b₁ hb₁ => ?_⟩
      rw [Real.dist_eq] at hb₁ ⊢
      have hb₁' := abs_lt.1 hb₁
      rw [abs_lt]
      rcases le_total b₁ b₀ with h | h
      · have h1 := M.ue_VR_antitone hu hsup hle h j
        have h2 := hmod b₀ j (b₀ - b₁) (by linarith) (by linarith)
        rw [sub_sub_cancel] at h2
        constructor <;> linarith
      · have h1 := M.ue_VR_antitone hu hsup hle h j
        have h2 := hmod b₁ j (b₁ - b₀) (by linarith) (by linarith)
        rw [sub_sub_cancel] at h2
        constructor <;> linarith
    · rw [hR]
      exact M.ue_VR_antitone hu hsup hle h j
    · rw [hR, hVD1]
      have h1 := hle b j 0 M.bmax_nonneg
      have h2 : M.u (M.inc j - M.φ (M.inc j)) ≤ M.u (M.inc j - b + M.fhq (n + 1) 0 j * 0) :=
        hu (by linarith [hφ j])
      have h3 := mul_le_mul_of_nonneg_left (ue_sum_mono M.markov (fun i => hVDW 0 i) j)
        M.β_nonneg
      unfold obj at h1
      unfold defaultRHS
      linarith

/-- **The constructed repayment sets are thresholds**: if `V^R_n` is continuous and
nonincreasing in debt and debt `≤ 0` is repaid, then on `B′ ≤ B̄` the repayment indicator of
stage `n` is `1{B′ ≤ b̄(Y′)}` for capacities `b̄ ≥ 0`. -/
theorem fh_thr {n : ℕ} (ic : ∀ j, Continuous fun b => M.fhVR n b j)
    (id : ∀ b b' j, b ≤ b' → M.fhVR n b' j ≤ M.fhVR n b j)
    (ie : ∀ b j, b ≤ 0 → M.fhVD n j ≤ M.fhVR n b j) :
    ∃ bt : Y → ℝ, (∀ j, 0 ≤ bt j) ∧ ∀ b' j, b' ≤ M.bmax → 1 - M.fhD n b' j = ue_thr bt b' j := by
  refine ⟨fun j => sSup {b | 0 ≤ b ∧ b ≤ M.bmax ∧ M.fhVD n j ≤ M.fhVR n b j}, fun j =>
    le_csSup ⟨M.bmax, fun b hb => hb.2.1⟩ ⟨le_rfl, M.bmax_nonneg, ie 0 j le_rfl⟩,
    fun b' j hb' => ?_⟩
  set S := {b | 0 ≤ b ∧ b ≤ M.bmax ∧ M.fhVD n j ≤ M.fhVR n b j} with hS
  change 1 - (if M.fhVR n b' j < M.fhVD n j then (1 : ℝ) else 0) = if b' ≤ sSup S then 1 else 0
  have hne : S.Nonempty := ⟨0, le_rfl, M.bmax_nonneg, ie 0 j le_rfl⟩
  have hbdd : BddAbove S := ⟨M.bmax, fun b hb => hb.2.1⟩
  have hcl : IsClosed S := (isClosed_le continuous_const continuous_id).inter
    ((isClosed_le continuous_id continuous_const).inter (isClosed_le continuous_const (ic j)))
  have hmem : sSup S ∈ S := hcl.csSup_mem hne hbdd
  by_cases h : b' ≤ sSup S
  · have h1 : M.fhVD n j ≤ M.fhVR n b' j := hmem.2.2.trans (id b' (sSup S) j h)
    simp only [h, ↓reduceIte, not_lt.2 h1, sub_zero]
  · have hpos : 0 < b' := lt_of_le_of_lt hmem.1 (not_le.1 h)
    have hlt : M.fhVR n b' j < M.fhVD n j := by
      by_contra hc
      exact h (le_csSup hbdd ⟨hpos.le, hb', not_lt.1 hc⟩)
    simp only [h, hlt, ↓reduceIte, sub_self]

/-- **Existence of the finite-horizon equilibrium** (AKMM, App. 24.A.1, p. 899, beyond the
text): with `u` nondecreasing, uniformly continuous and satiated and `φ ≥ 0`, there is one
sequence of stage objects that is an equilibrium of the game of every horizon `T` (each stage
by backward induction, optimal borrowing by `fh_attain`). With `fh_unique`, the game of
horizon `T` has exactly these values, default rules and prices. -/
theorem fh_exists (hu : Monotone M.u) (huc : UniformContinuous M.u) {cbar : ℝ}
    (hsat : ∀ c, cbar ≤ c → M.u c = M.u cbar) (hφ : ∀ y, 0 ≤ M.φ (M.inc y)) :
    ∃ (V VR : ℕ → ℝ → Y → ℝ) (VD : ℕ → Y → ℝ) (D Bh q : ℕ → ℝ → Y → ℝ),
      ∀ T, IsFHEqm M T V VR VD D Bh q := by
  have hub := M.ue_u_le hu hsat
  have hr1 : 0 < 1 + M.r := by linarith [M.r_pos]
  set K₀ := max 0 ((cbar + ‖M.inc‖) * (1 + M.r) / M.r) with hK₀
  have hK₀0 : 0 ≤ K₀ := le_max_left _ _
  have hcons : ∀ j, cbar ≤ M.inc j - -K₀ + (1 + M.r)⁻¹ * -K₀ := fun j => by
    have hj : -‖M.inc‖ ≤ M.inc j := by
      have h1 := norm_le_pi_norm M.inc j
      rw [Real.norm_eq_abs] at h1
      linarith [neg_abs_le (M.inc j)]
    have h2 : (cbar + ‖M.inc‖) * (1 + M.r) / M.r ≤ K₀ := le_max_right _ _
    rw [div_le_iff₀ M.r_pos] at h2
    have h3 : cbar + ‖M.inc‖ ≤ K₀ * M.r / (1 + M.r) := by
      rw [le_div_iff₀ hr1]
      linarith
    have h4 : M.inc j - -K₀ + (1 + M.r)⁻¹ * -K₀ = M.inc j + K₀ * M.r / (1 + M.r) := by
      field_simp
      ring
    rw [h4]
    linarith
  have hst := M.fh_stage hu huc hsat hφ hcons hK₀0
  have hatt : ∀ n b y, ∃ b', b' ≤ M.bmax ∧
      M.obj (M.fhq (n + 1)) (M.fhV n) b y b' = M.fhVR (n + 1) b y := by
    intro n b y
    obtain ⟨ia, ib, ic, id, ie⟩ := hst n
    obtain ⟨bt, hbt0, hbt⟩ := M.fh_thr ic id ie
    have hWc : ∀ j, Continuous fun b => M.fhV n b j := fun j => continuous_const.max (ic j)
    have hWs : ∀ b' j, b' ≤ -K₀ → M.fhV n b' j ≤ M.fhV n (-K₀) j := fun b' j _ =>
      (ia b' j).trans ((ib j).trans (le_max_right _ _))
    obtain ⟨bs, hbs, hmax⟩ := M.fh_attain hu huc hbt0 hWc hK₀0 hWs b y
    have hobj : ∀ b'', b'' ≤ M.bmax → M.obj (M.fhq (n + 1)) (M.fhV n) b y b'' =
        M.obj (M.price (ue_thr bt)) (M.fhV n) b y b'' := fun b'' hb'' => M.fh_obj_congr (by
      change M.price (fun b' j => 1 - M.fhD n b' j) b'' y = M.price (ue_thr bt) b'' y
      unfold price
      simp only [hbt b'' _ hb''])
    refine ⟨bs, hbs, ?_⟩
    change _ = M.VRsup (M.fhq (n + 1)) (M.fhV n) b y
    refine le_antisymm (M.ue_VRsup_le hub ia b y hbs) (ciSup_le fun b'' => ?_)
    rw [hobj _ (min_le_right _ _), hobj _ hbs]
    exact hmax _ (min_le_right _ _)
  choose Bh' hBh hBhopt using hatt
  refine ⟨M.fhV, M.fhVR, M.fhVD, M.fhD, fun n => match n with
    | 0 => fun _ _ => 0
    | k + 1 => Bh' k, M.fhq, fun T => ?_⟩
  exact { eq_24_9 := fun _ _ _ _ => rfl
          default_opt := fun _ _ _ _ => rfl
          term_VD := fun _ => rfl
          term_VR := fun _ _ => rfl
          term_q := fun _ _ => rfl
          term_B := fun _ _ => rfl
          eq_24_10 := fun _ _ _ => rfl
          eq_24_11 := fun n _ b y _ hb' => M.ue_VRsup_le hub (hst n).1 b y hb'
          eq_24_12 := fun _ _ _ _ _ => rfl
          borrow_le := fun n _ b y => hBh n b y
          borrow_opt := fun n _ b y => hBhopt n b y }

end UEModel

/-- The example `ue_example` meets the slope condition of the convergence theorems: with
`u = min(c, 3)`, `κ = 1`, `c̄ = 3`, and `Y + B̄/(1 + r) ≤ 2 + 4/5 ≤ 3`. -/
theorem fh_example_hyp :
    (∀ c c', c ≤ c' → c' ≤ 3 → 1 * (c' - c) ≤ ue_example.u c' - ue_example.u c) ∧
      ∀ y, ue_example.inc y + ue_example.bmax * (1 + ue_example.r)⁻¹ ≤ 3 := by
  constructor
  · intro c c' h h'
    change 1 * (c' - c) ≤ min c' 3 - min c 3
    rw [min_eq_left h', min_eq_left (h.trans h')]
    linarith
  · intro y
    change (if y then (2 : ℝ) else 1) + 1 * (1 + 1 / 4)⁻¹ ≤ 3
    split_ifs <;> norm_num

/-- **The limit of the finite-horizon game in a concrete economy** (AKMM, App. 24.A.1, p. 901,
beyond the text): in `ue_example` the finite-horizon game has an equilibrium for every horizon,
the infinite-horizon game has a unique Markov perfect equilibrium (`ue_example_exists_unique`),
and as the horizon grows the finite-horizon values converge to the equilibrium values
uniformly and the debt capacities converge to the equilibrium capacities. -/
theorem fh_example_limit :
    ∃ (V VR : ℕ → ℝ → Bool → ℝ) (VD : ℕ → Bool → ℝ) (D Bh q : ℕ → ℝ → Bool → ℝ)
      (Vs VRs : ℝ → Bool → ℝ) (VDs : Bool → ℝ) (Ds Bhs qs : ℝ → Bool → ℝ),
      (∀ T, IsFHEqm ue_example T V VR VD D Bh q) ∧
      IsOneMPE ue_example Vs VRs VDs Ds Bhs qs ∧
      (∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ b y, |VD n y - VDs y| ≤ ε ∧ |VR n b y - VRs b y| ≤ ε ∧
        |V n b y - Vs b y| ≤ ε) ∧
      ∀ j, Tendsto (fun n => ue_example.fhCap (VR n) (VD n) j) atTop
        (𝓝 (ue_example.fhCap VRs VDs j)) := by
  obtain ⟨h1, h2, h3, h4⟩ := ue_example_hyp
  obtain ⟨hsl, hcap⟩ := fh_example_hyp
  obtain ⟨V, VR, VD, D, Bh, q, hfh⟩ := ue_example.fh_exists h1 h2 h3 h4
  obtain ⟨Vs, VRs, VDs, Ds, Bhs, qs, hs⟩ := ue_example.ue_mpe_exists h1 h2 h3 h4
  obtain ⟨_, _, _, _, hc⟩ := ue_example.fh_capacity_tendsto h1 h4 one_pos hsl hcap hfh hs
  exact ⟨V, VR, VD, D, Bh, q, Vs, VRs, VDs, Ds, Bhs, qs, hfh, hs,
    ue_example.fh_values_tendsto h1 h2 h4 one_pos hsl hcap hfh hs, hc⟩

end AKMM.SovereignDefault

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Two Markov perfect equilibria with long-term debt and a continuum of debt levels

AKMM, Appendix 24.A.1, p. 901: "Aguiar and Amador (2020) show that there can be multiple
Markov equilibria in the model with long-term debt (`δ ∈ (0, 1)`)". Beyond the text.

**The equilibrium with long-term debt** (`IsLongMPE`) is the book's definition (§24.4.3,
(a)–(c)) with the long-term bond of (24.7)–(24.8): the repaying sovereign with debt `B` choosing
`B′` consumes `C = Y − δB + q(B′, Y)(B′ − (1 − δ)B)` ((24.11)), and the price is (24.12),
`q(B′, Y) = (1 + r)⁻¹ E[(1 − D̂(B′, Y′))(δ + (1 − δ)q(B̂(B′, Y′), Y′))]`. The setting is that
of departure D10 (`UEModel`: permanent exclusion `ψ = 0`, any `B′ ≤ B̄` including saving,
states `B ∈ ℝ`, bounded values). At `δ = 1` the definition is exactly `IsOneMPE`
(`ld_one_iff`), so by `ue_mpe_exists_unique` an economy satisfying its hypotheses has exactly
one equilibrium with one-period debt.

**The economy** (`ld_econ`): deterministic income `Y = 2`, utility `u(c) = min(c, 1)`
(satiated at `c̄ = 1`), default cost `φ = 1/2`, `β = 1/2`, `r = 1/4`, borrowing limit
`B̄ = 7`. With `δ = 1/2` it has two Markov perfect equilibria (`ld_two_mpe`), both verified
against every condition of the definition:

* **no dilution**: the sovereign always issues up to the safe level `6` (or `7` when it
  defaults anyway), never defaults on debt `B ≤ 6`, and every safe bond trades at the
  risk-free price `δ/(r + δ) = 2/3`;
* **self-fulfilling dilution**: a sovereign with little debt (`B ≤ 2`) issues up to `B̄ = 7`,
  diluting its creditors, and defaults the next period; lenders anticipate it, so bonds
  `B′ ≤ 2` trade at `δ/(1 + r) = 2/5` (one coupon, then nothing), while `B′ ∈ (2, 6]` still
  trade at `2/3`.

The value functions and the default rule coincide (`V ≡ 2`, default iff `B > 6`); the prices
and the borrowing rules differ. The mechanism is that with `δ < 1` the price depends on the
borrowing rule lenders expect (`bp_long_term_depends_on_borrowing`): the low-debt sovereign is
satiated whichever debt it issues, and default at `7` costs it no utility (`Y − φ ≥ c̄`), so it
is indifferent, and lenders' beliefs select the rule. With `δ = 1` the price does not depend on
the borrowing rule, and the same economy has a unique equilibrium (`ld_one_period_unique`).

This is a multiplicity through indifference: it isolates the dilution channel of long-term
debt but is not Aguiar and Amador's (2020) construction, where the sovereign strictly prefers to
dilute and values differ across equilibria; that construction is not formalised.
-/

namespace AKMM.SovereignDefault

open Finset SargentStachurski.RecursiveDecisionProcesses

variable {Y : Type*} [Fintype Y]

namespace UEModel

variable (M : UEModel Y)

/-- AKMM, (24.11) with the long-term bond of (24.7)–(24.8): the objective
`u(Y − δB + q(B′, Y)(B′ − (1 − δ)B)) + βE V(B′, Y′)`. -/
def ldObj (δ : ℝ) (q V : ℝ → Y → ℝ) (b : ℝ) (y : Y) (b' : ℝ) : ℝ :=
  M.u (M.inc y - δ * b + q b' y * (b' - (1 - δ) * b)) + M.β * ∑ j, M.P y j * V b' j

/-- With one-period debt the long-term objective is the one-period objective. -/
theorem ld_obj_one (q V : ℝ → Y → ℝ) (b : ℝ) (y : Y) (b' : ℝ) :
    M.ldObj 1 q V b y b' = M.obj q V b y b' := by
  unfold ldObj obj
  simp only [one_mul, sub_self, zero_mul, sub_zero]

end UEModel

variable (M : UEModel Y) (δ : ℝ) (V VR : ℝ → Y → ℝ) (VD : Y → ℝ) (D Bh q : ℝ → Y → ℝ) in
/-- **AKMM, §24.4.3**, pp. 744–745, Markov perfect equilibrium with long-term debt of decay `δ`
((24.7)–(24.12)), permanent exclusion (`ψ = 0`) and a continuum of debt levels `B′ ≤ B̄`
(departure D10): bounded values `V`, `V^R`, `V^D`, a default rule `D̂`, a borrowing rule `B̂`
and a price `q` with (a) (24.9)–(24.11), (b) (24.12), (c) `D̂` and `B̂` optimal. -/
structure IsLongMPE : Prop where
  /-- Values lie in the space of bounded functions. -/
  bdd : ∃ K, ∀ b y, V b y ≤ K
  /-- (a) (24.9). -/
  eq_24_9 : ∀ b y, V b y = max (VD y) (VR b y)
  /-- (a) (24.10) with `ψ = 0`. -/
  eq_24_10 : ∀ y, VD y = M.defaultRHS VD y
  /-- (a) (24.11): `V^R` bounds the objective over `B′ ≤ B̄` ... -/
  eq_24_11 : ∀ b y b', b' ≤ M.bmax → M.ldObj δ q V b y b' ≤ VR b y
  /-- (b) (24.12). -/
  eq_24_12 : ∀ b' y, b' ≤ M.bmax → q b' y =
    (1 + M.r)⁻¹ * ∑ j, M.P y j * ((1 - D b' j) * (δ + (1 - δ) * q (Bh b' j) j))
  /-- (c) the default rule is optimal (ties repaid). -/
  default_opt : ∀ b y, D b y = if VR b y < VD y then 1 else 0
  /-- The borrowing rule is feasible. -/
  borrow_le : ∀ b y, Bh b y ≤ M.bmax
  /-- (c) ... and attains it. -/
  borrow_opt : ∀ b y, M.ldObj δ q V b y (Bh b y) = VR b y

/-- **The definition at `δ = 1`**: a Markov perfect equilibrium with long-term debt of decay
`δ = 1` is exactly a Markov perfect equilibrium with one-period debt (`IsOneMPE`). -/
theorem ld_one_iff (M : UEModel Y) (V VR : ℝ → Y → ℝ) (VD : Y → ℝ) (D Bh q : ℝ → Y → ℝ) :
    IsLongMPE M 1 V VR VD D Bh q ↔ IsOneMPE M V VR VD D Bh q := by
  have hp : ∀ b' y, (1 + M.r)⁻¹ * ∑ j, M.P y j * ((1 - D b' j) * (1 + (1 - 1) * q (Bh b' j) j))
      = (1 + M.r)⁻¹ * ∑ j, M.P y j * (1 - D b' j) := fun b' y => by
    simp only [sub_self, zero_mul, add_zero, mul_one]
  constructor
  · intro h
    exact { bdd := h.bdd
            eq_24_9 := h.eq_24_9
            eq_24_10 := h.eq_24_10
            eq_24_11 := fun b y b' hb' => by rw [← M.ld_obj_one]; exact h.eq_24_11 b y b' hb'
            eq_24_12 := fun b' y hb' => by rw [h.eq_24_12 b' y hb', hp]
            default_opt := h.default_opt
            borrow_le := h.borrow_le
            borrow_opt := fun b y => by rw [← M.ld_obj_one]; exact h.borrow_opt b y }
  · intro h
    exact { bdd := h.bdd
            eq_24_9 := h.eq_24_9
            eq_24_10 := h.eq_24_10
            eq_24_11 := fun b y b' hb' => by rw [M.ld_obj_one]; exact h.eq_24_11 b y b' hb'
            eq_24_12 := fun b' y hb' => by rw [h.eq_24_12 b' y hb', hp]
            default_opt := h.default_opt
            borrow_le := h.borrow_le
            borrow_opt := fun b y => by rw [M.ld_obj_one]; exact h.borrow_opt b y }

/-- The economy of the long-term multiplicity example: one income level `Y = 2`, utility
`u(c) = min(c, 1)`, default cost `φ = 1/2`, `β = 1/2`, `r = 1/4`, borrowing limit `B̄ = 7`. -/
noncomputable def ld_econ : UEModel Unit where
  inc := fun _ => 2
  P := fun _ _ => 1
  markov := ⟨fun _ _ => zero_le_one, fun _ => by simp⟩
  u := fun c => min c 1
  φ := fun _ => 1 / 2
  β := 1 / 2
  β_nonneg := by norm_num
  β_lt_one := by norm_num
  r := 1 / 4
  r_pos := by norm_num
  bmax := 7
  bmax_nonneg := by norm_num

/-- The repayment value of the example (both equilibria):
`V^R(B) = min(2 − B/2 + max(4 − B/3, 0), 1) + 1`. -/
noncomputable def ld_VR (b : ℝ) (_ : Unit) : ℝ := min (2 - b / 2 + max (4 - b / 3) 0) 1 + 1

/-- The default rule of the example (both equilibria): default iff `B > 6`. -/
noncomputable def ld_D (b : ℝ) (_ : Unit) : ℝ := if 6 < b then 1 else 0

/-- The no-dilution prices: `2/3` on `B′ ≤ 6`, `0` above. -/
noncomputable def ld_qG (b' : ℝ) (_ : Unit) : ℝ := if b' ≤ 6 then 2 / 3 else 0

/-- The dilution prices: `2/5` on `B′ ≤ 2`, `2/3` on `(2, 6]`, `0` above. -/
noncomputable def ld_qB (b' : ℝ) (_ : Unit) : ℝ :=
  if b' ≤ 2 then 2 / 5 else if b' ≤ 6 then 2 / 3 else 0

/-- The no-dilution borrowing rule: issue up to `6`, or `7` when `B > 12`. -/
noncomputable def ld_BG (b : ℝ) (_ : Unit) : ℝ := if b ≤ 12 then 6 else 7

/-- The dilution borrowing rule: issue up to `B̄ = 7` when `B ≤ 2`, else as without dilution. -/
noncomputable def ld_BB (b : ℝ) (_ : Unit) : ℝ := if b ≤ 2 then 7 else if b ≤ 12 then 6 else 7

/-- The repayment value is below the default value `2`, and below it exactly when `B > 6`. -/
theorem ld_VR_lt_iff (b : ℝ) : ld_VR b () ≤ 2 ∧ (ld_VR b () < 2 ↔ 6 < b) := by
  unfold ld_VR
  refine ⟨by linarith [min_le_right (2 - b / 2 + max (4 - b / 3) 0) 1], ?_⟩
  constructor
  · intro h
    by_contra hb
    have h1 : 1 ≤ 2 - b / 2 + max (4 - b / 3) 0 := by
      linarith [le_max_left (4 - b / 3) 0, not_lt.1 hb]
    rw [min_eq_right h1] at h
    linarith
  · intro hb
    have h1 : 2 - b / 2 + max (4 - b / 3) 0 < 1 := by
      rcases le_total (4 - b / 3) 0 with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    linarith [min_le_left (2 - b / 2 + max (4 - b / 3) 0) 1]

/-- The objective of the example at `δ = 1/2` with continuation value `2`. -/
theorem ld_obj_eq (q : ℝ → Unit → ℝ) (b b' : ℝ) :
    ld_econ.ldObj (1 / 2) q (fun _ _ => 2) b () b' =
      min (2 - b / 2 + q b' () * (b' - b / 2)) 1 + 1 := by
  simp only [UEModel.ldObj, ld_econ, univ_unique, sum_singleton]
  norm_num
  ring_nf

/-- The default value of the example is `2`. -/
theorem ld_VD_eq : ld_econ.defaultRHS (fun _ => 2) () = 2 := by
  simp only [UEModel.defaultRHS, ld_econ, univ_unique, sum_singleton]
  norm_num

/-- **Two Markov perfect equilibria with long-term debt** (`δ = 1/2`) in the continuous-debt
economy `ld_econ` (AKMM, p. 901, beyond the text). Both have `V ≡ V^D ≡ 2`, the repayment
value `ld_VR` and default iff `B > 6`. Without dilution (`ld_qG`, `ld_BG`) every safe bond
trades at `δ/(r + δ) = 2/3`; with self-fulfilling dilution (`ld_qB`, `ld_BB`) a sovereign
with debt `B ≤ 2` issues `B̄ = 7` and bonds `B′ ≤ 2` trade at `δ/(1 + r) = 2/5`. The prices
of debt `1` differ, and so do the borrowing rules at debt `0`. -/
theorem ld_two_mpe :
    IsLongMPE ld_econ (1 / 2) (fun _ _ => 2) ld_VR (fun _ => 2) ld_D ld_BG ld_qG ∧
      IsLongMPE ld_econ (1 / 2) (fun _ _ => 2) ld_VR (fun _ => 2) ld_D ld_BB ld_qB ∧
      ld_qG 1 () ≠ ld_qB 1 () ∧ ld_BG 0 () ≠ ld_BB 0 () := by
  have hbm : ld_econ.bmax = 7 := rfl
  have hr : (1 + ld_econ.r)⁻¹ = 4 / 5 := by simp only [ld_econ]; norm_num
  have h9 : ∀ b (_ : Unit), (2 : ℝ) = max 2 (ld_VR b ()) := fun b _ =>
    (max_eq_left (ld_VR_lt_iff b).1).symm
  have hdef : ∀ b (_ : Unit), ld_D b () = if ld_VR b () < 2 then 1 else 0 := fun b _ => by
    unfold ld_D
    by_cases h : 6 < b
    · simp only [h, (ld_VR_lt_iff b).2.2 h, ↓reduceIte]
    · have h' : ¬ ld_VR b () < 2 := fun h' => h ((ld_VR_lt_iff b).2.1 h')
      simp only [h, h', ↓reduceIte]
  have hsum : ∀ (f : Unit → ℝ), ∑ j, ld_econ.P () j * f j = f () := fun f => by
    simp only [ld_econ, univ_unique, sum_singleton, one_mul]
  -- the objective is bounded by the repayment value whenever `q(B′)(B′ − B/2) ≤ max(4 − B/3, 0)`
  have hle : ∀ (q : ℝ → Unit → ℝ) (b b' : ℝ), q b' () * (b' - b / 2) ≤ max (4 - b / 3) 0 →
      ld_econ.ldObj (1 / 2) q (fun _ _ => 2) b () b' ≤ ld_VR b () := fun q b b' h => by
    rw [ld_obj_eq]
    unfold ld_VR
    linarith [min_le_min_right 1 (show 2 - b / 2 + q b' () * (b' - b / 2) ≤
      2 - b / 2 + max (4 - b / 3) 0 by linarith)]
  have hrev : ∀ c b b' : ℝ, 0 ≤ c → c ≤ 2 / 3 → b' ≤ 6 → c * (b' - b / 2) ≤ max (4 - b / 3) 0 :=
    fun c b b' hc0 hc1 hb' => by
      rcases le_total 0 (b' - b / 2) with h | h
      · have : c * (b' - b / 2) ≤ 2 / 3 * (6 - b / 2) :=
          mul_le_mul hc1 (by linarith) h (by norm_num)
        exact le_max_of_le_left (by linarith)
      · exact le_max_of_le_right (mul_nonpos_of_nonneg_of_nonpos hc0 h)
  -- the repayment value at the safe issue `6`
  have hat6 : ∀ b : ℝ, b ≤ 12 → min (2 - b / 2 + 2 / 3 * (6 - b / 2)) 1 + 1 = ld_VR b () :=
    fun b hb => by
      unfold ld_VR
      rw [max_eq_left (by linarith : (0 : ℝ) ≤ 4 - b / 3)]
      ring_nf
  have hat7 : ∀ b : ℝ, 12 < b → min (2 - b / 2 + 0 * (7 - b / 2)) 1 + 1 = ld_VR b () :=
    fun b hb => by
      unfold ld_VR
      rw [max_eq_right (by linarith : 4 - b / 3 ≤ (0 : ℝ))]
      ring_nf
  refine ⟨⟨⟨2, fun _ _ => le_rfl⟩, h9, fun _ => ld_VD_eq.symm, fun b _ b' hb' => ?_,
    fun b' _ hb' => ?_, hdef, fun b _ => ?_, fun b _ => ?_⟩,
    ⟨⟨2, fun _ _ => le_rfl⟩, h9, fun _ => ld_VD_eq.symm, fun b _ b' hb' => ?_,
    fun b' _ hb' => ?_, hdef, fun b _ => ?_, fun b _ => ?_⟩, ?_, ?_⟩
  · -- good: (24.11)
    refine hle _ b b' ?_
    unfold ld_qG
    split_ifs with h
    · exact hrev _ b b' (by norm_num) le_rfl h
    · rw [zero_mul]; exact le_max_right _ _
  · -- good: (24.12)
    rw [hsum, hr]
    unfold ld_qG ld_D ld_BG
    split_ifs <;> (try norm_num) <;> linarith
  · -- good: feasibility
    unfold ld_BG; rw [hbm]; split_ifs <;> norm_num
  · -- good: optimality
    rw [ld_obj_eq]
    unfold ld_BG ld_qG
    by_cases h : b ≤ 12
    · simp only [h, le_refl (6 : ℝ), ↓reduceIte]; exact hat6 b h
    · simp only [h, (by norm_num : ¬ (7 : ℝ) ≤ 6), ↓reduceIte]; exact hat7 b (not_le.1 h)
  · -- dilution: (24.11)
    refine hle _ b b' ?_
    unfold ld_qB
    split_ifs with h1 h2
    · exact hrev _ b b' (by norm_num) (by norm_num) (by linarith)
    · exact hrev _ b b' (by norm_num) le_rfl h2
    · rw [zero_mul]; exact le_max_right _ _
  · -- dilution: (24.12)
    rw [hsum, hr]
    unfold ld_qB ld_D ld_BB
    split_ifs <;> (try norm_num) <;> linarith
  · -- dilution: feasibility
    unfold ld_BB; rw [hbm]; split_ifs <;> norm_num
  · -- dilution: optimality
    rw [ld_obj_eq]
    unfold ld_BB ld_qB
    by_cases h2 : b ≤ 2
    · simp only [h2, (by norm_num : ¬ (7 : ℝ) ≤ 2), (by norm_num : ¬ (7 : ℝ) ≤ 6), ↓reduceIte]
      unfold ld_VR
      rw [min_eq_right (by linarith : (1 : ℝ) ≤ 2 - b / 2 + 0 * (7 - b / 2)),
        min_eq_right (by linarith [le_max_left (4 - b / 3) 0] :
          (1 : ℝ) ≤ 2 - b / 2 + max (4 - b / 3) 0)]
    · simp only [h2, ↓reduceIte]
      by_cases h : b ≤ 12
      · simp only [h, (by norm_num : ¬ (6 : ℝ) ≤ 2), le_refl (6 : ℝ), ↓reduceIte]
        exact hat6 b h
      · simp only [h, (by norm_num : ¬ (7 : ℝ) ≤ 2),
          (by norm_num : ¬ (7 : ℝ) ≤ 6), ↓reduceIte]
        exact hat7 b (not_le.1 h)
  · unfold ld_qG ld_qB; norm_num
  · unfold ld_BG ld_BB; norm_num

/-- The dilution prices are never above the no-dilution prices, and strictly below them on
`B′ ≤ 2`. -/
theorem ld_dilution_lowers_prices (b' : ℝ) :
    ld_qB b' () ≤ ld_qG b' () ∧ (b' ≤ 2 → ld_qB b' () < ld_qG b' ()) := by
  unfold ld_qB ld_qG
  constructor
  · split_ifs <;> first | (norm_num; done) | (norm_num; linarith)
  · intro h
    simp only [h, (by linarith : b' ≤ 6), ↓reduceIte]
    norm_num

/-- The example meets the hypotheses of `ue_mpe_exists_unique`: `u = min(·, 1)` nondecreasing,
uniformly continuous and satiated at `1`, `φ ≥ 0`. -/
theorem ld_econ_hyp : Monotone ld_econ.u ∧ UniformContinuous ld_econ.u ∧
    (∀ c, 1 ≤ c → ld_econ.u c = ld_econ.u 1) ∧ ∀ y, 0 ≤ ld_econ.φ (ld_econ.inc y) := by
  refine ⟨fun a b h => min_le_min_right 1 h, (LipschitzWith.id.min_const 1).uniformContinuous,
    fun c hc => ?_, fun _ => by change (0 : ℝ) ≤ 1 / 2; norm_num⟩
  change min c 1 = min 1 1
  rw [min_eq_right hc, min_self]

/-- **With one-period debt the same economy has exactly one Markov perfect equilibrium**
(AKMM, p. 901; `ue_mpe_exists_unique` through `ld_one_iff`): it exists, and any two share
their values, default rule and prices. So the multiplicity of `ld_two_mpe` is due to `δ < 1`. -/
theorem ld_one_period_unique :
    (∃ (V VR : ℝ → Unit → ℝ) (VD : Unit → ℝ) (D Bh q : ℝ → Unit → ℝ),
      IsLongMPE ld_econ 1 V VR VD D Bh q) ∧
      ∀ {V₁ VR₁ D₁ Bh₁ q₁ V₂ VR₂ D₂ Bh₂ q₂ : ℝ → Unit → ℝ} {VD₁ VD₂ : Unit → ℝ},
        IsLongMPE ld_econ 1 V₁ VR₁ VD₁ D₁ Bh₁ q₁ → IsLongMPE ld_econ 1 V₂ VR₂ VD₂ D₂ Bh₂ q₂ →
        V₁ = V₂ ∧ VR₁ = VR₂ ∧ VD₁ = VD₂ ∧ D₁ = D₂ ∧
          ∀ b' y, b' ≤ ld_econ.bmax → q₁ b' y = q₂ b' y := by
  obtain ⟨h1, h2, h3, h4⟩ := ld_econ_hyp
  obtain ⟨hex, huniq⟩ := ld_econ.ue_mpe_exists_unique h1 h2 h3 h4
  obtain ⟨V, VR, VD, D, Bh, q, h⟩ := hex
  exact ⟨⟨V, VR, VD, D, Bh, q, (ld_one_iff _ _ _ _ _ _ _).2 h⟩, fun h₁ h₂ =>
    huniq ((ld_one_iff _ _ _ _ _ _ _).1 h₁) ((ld_one_iff _ _ _ _ _ _ _).1 h₂)⟩

end AKMM.SovereignDefault

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Self-fulfilling debt dilution: strict multiplicity with long-term debt

AKMM, Appendix 24.A.1, p. 901: "Aguiar and Amador (2020) show that there can be multiple
Markov equilibria in the model with long-term debt (`δ ∈ (0, 1)`)". Beyond the text.

**Setting** (departure D13). The book's model of §24.4 with the book's own asset lower bound
`B′ ≥ 0` (p. 744) and the borrowing limit `B′ ≤ B̄`: states and choices lie in `[0, B̄]`
(`IsBoundedLongMPE`, otherwise the definition `IsLongMPE` of (24.7)–(24.12), with permanent
exclusion `ψ = 0`). The same definition is used for `δ < 1` and for `δ = 1`.

**The economy** (`sfd_econ`). Two income states: normal times `H` (`true`, income `2`, default
cost `3/2`) and an absorbing crisis `L` (`false`, income `1`, default cost `1/7`), reached from
`H` with probability `λ = 1/5`; linear utility `u(c) = c`, `β = 1/2`, `r = 1/5`, `B̄ = 3/2`. With
`δ = 1/2` the risk-free price is `q* = δ/(r + δ) = 5/7`, and in the crisis the sovereign repays
exactly the debts `B ≤ 1` (the *safe zone*). Debt above `1` is lost when the crisis comes.

**Two Markov perfect equilibria at `δ = 1/2`** (`sfd_two_mpe`), both verified against every
condition at every state and every admissible `B′`:

* **no dilution** (`sfd_VRN`, `sfd_qN`, `sfd_BhN`): a sovereign in the safe zone keeps its
  debt at `1` and pays the risk-free price `5/7`; one with debt in `(1, 10/9]` deleverages to
  `1`; above `10/9` it stays at `B̄`;
* **self-fulfilling dilution** (`sfd_VRS`, `sfd_qS`, `sfd_BhS`): lenders expect a sovereign
  with debt in `(3/5, 1]` to borrow up to `B̄ = 3/2`, so they pay only `9/14 < 5/7` for such
  debt; at these prices diluting is strictly optimal (`sfd_strict_preference`), and debt below
  `3/5`, which is diluted one period later, trades at `29/42 < 5/7`.

The default rule is the same, but the **values differ** (`sfd_values_differ`: strictly lower
under dilution on `[0, 10/9)`), as do the prices (`sfd_dilution_lowers_prices`) and borrowing
rules. Higher legacy debt `(1 − δ)B` makes the low-price issue more attractive (the objective
contains `−(1 − δ)B q(B′)`): that is the dilution channel, and it is absent at `δ = 1`.

**With one-period debt the same economy has exactly one equilibrium** (`sfd_one_period_unique`,
proved directly: with `δ = 1` and linear utility `V^R(B, Y) = V^R(0, Y) − B`, the crisis capacity
is pinned at `6/7` and then prices and values are determined). So the multiplicity is due to
long-term debt.
-/

namespace AKMM.SovereignDefault

open Finset SargentStachurski.RecursiveDecisionProcesses

variable {Y : Type*} [Fintype Y]

variable (M : UEModel Y) (δ : ℝ) (V VR : ℝ → Y → ℝ) (VD : Y → ℝ) (D Bh q : ℝ → Y → ℝ) in
/-- **AKMM, §24.4.3**, pp. 744–745, Markov perfect equilibrium with long-term debt of decay `δ`
((24.7)–(24.12)) and permanent exclusion (`ψ = 0`), with the book's asset lower bound `B′ ≥ 0`
and the borrowing limit `B′ ≤ B̄` (departure D13): states and choices in `[0, B̄]`; bounded
values `V`, `V^R`, `V^D`, a default rule `D̂`, a borrowing rule `B̂` and a price `q` with
(a) (24.9)–(24.11), (b) (24.12), (c) `D̂` and `B̂` optimal. -/
structure IsBoundedLongMPE : Prop where
  /-- Values are bounded. -/
  bdd : ∃ K, ∀ b y, 0 ≤ b → b ≤ M.bmax → V b y ≤ K
  /-- (a) (24.9). -/
  eq_24_9 : ∀ b y, 0 ≤ b → b ≤ M.bmax → V b y = max (VD y) (VR b y)
  /-- (a) (24.10) with `ψ = 0`. -/
  eq_24_10 : ∀ y, VD y = M.defaultRHS VD y
  /-- (a) (24.11): `V^R` bounds the objective over `0 ≤ B′ ≤ B̄` ... -/
  eq_24_11 : ∀ b y b', 0 ≤ b → b ≤ M.bmax → 0 ≤ b' → b' ≤ M.bmax →
    M.ldObj δ q V b y b' ≤ VR b y
  /-- (b) (24.12). -/
  eq_24_12 : ∀ b' y, 0 ≤ b' → b' ≤ M.bmax → q b' y =
    (1 + M.r)⁻¹ * ∑ j, M.P y j * ((1 - D b' j) * (δ + (1 - δ) * q (Bh b' j) j))
  /-- (c) the default rule is optimal (ties repaid). -/
  default_opt : ∀ b y, 0 ≤ b → b ≤ M.bmax → D b y = if VR b y < VD y then 1 else 0
  /-- The borrowing rule is feasible. -/
  borrow_mem : ∀ b y, 0 ≤ b → b ≤ M.bmax → 0 ≤ Bh b y ∧ Bh b y ≤ M.bmax
  /-- (c) ... and attains it. -/
  borrow_opt : ∀ b y, 0 ≤ b → b ≤ M.bmax → M.ldObj δ q V b y (Bh b y) = VR b y

/-- The economy of the strict multiplicity example: normal times `true` (income `2`, default
cost `3/2`) and an absorbing crisis `false` (income `1`, default cost `1/7`), reached with
probability `1/5`; `u(c) = c`, `β = 1/2`, `r = 1/5`, borrowing limit `B̄ = 3/2`. -/
noncomputable def sfd_econ : UEModel Bool where
  inc := fun y => if y then 2 else 1
  P := fun y j => if y then (if j then 4 / 5 else 1 / 5) else (if j then 0 else 1)
  markov := ⟨fun y j => by cases y <;> cases j <;> norm_num,
    fun y => by cases y <;> norm_num [Fintype.sum_bool]⟩
  u := fun c => c
  φ := fun c => if c = 1 then 1 / 7 else 3 / 2
  β := 1 / 2
  β_nonneg := by norm_num
  β_lt_one := by norm_num
  r := 1 / 5
  r_pos := by norm_num
  bmax := 3 / 2
  bmax_nonneg := by norm_num

theorem sfd_bmax : sfd_econ.bmax = 3 / 2 := rfl

/-- The objective in normal times. -/
theorem sfd_obj_true (δ : ℝ) (q V : ℝ → Bool → ℝ) (b b' : ℝ) :
    sfd_econ.ldObj δ q V b true b' = 2 - δ * b + q b' true * (b' - (1 - δ) * b) +
      1 / 2 * (4 / 5 * V b' true + 1 / 5 * V b' false) := by
  simp only [UEModel.ldObj, sfd_econ, Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true]

/-- The objective in the crisis. -/
theorem sfd_obj_false (δ : ℝ) (q V : ℝ → Bool → ℝ) (b b' : ℝ) :
    sfd_econ.ldObj δ q V b false b' = 1 - δ * b + q b' false * (b' - (1 - δ) * b) +
      1 / 2 * V b' false := by
  simp only [UEModel.ldObj, sfd_econ, Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true]
  ring

/-- The price recursion (24.12) in normal times. -/
theorem sfd_price_true (δ : ℝ) (q D Bh : ℝ → Bool → ℝ) (b' : ℝ) :
    (1 + sfd_econ.r)⁻¹ * ∑ j, sfd_econ.P true j * ((1 - D b' j) * (δ + (1 - δ) * q (Bh b' j) j))
      = 5 / 6 * (4 / 5 * ((1 - D b' true) * (δ + (1 - δ) * q (Bh b' true) true)) +
        1 / 5 * ((1 - D b' false) * (δ + (1 - δ) * q (Bh b' false) false))) := by
  simp only [sfd_econ, Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true]
  norm_num

/-- The price recursion (24.12) in the crisis. -/
theorem sfd_price_false (δ : ℝ) (q D Bh : ℝ → Bool → ℝ) (b' : ℝ) :
    (1 + sfd_econ.r)⁻¹ * ∑ j, sfd_econ.P false j * ((1 - D b' j) * (δ + (1 - δ) * q (Bh b' j) j))
      = 5 / 6 * ((1 - D b' false) * (δ + (1 - δ) * q (Bh b' false) false)) := by
  simp only [sfd_econ, Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true]
  norm_num

/-- The default values: (24.10) in normal times and in the crisis. -/
theorem sfd_defaultRHS (VD : Bool → ℝ) :
    sfd_econ.defaultRHS VD true = 1 / 2 + 1 / 2 * (4 / 5 * VD true + 1 / 5 * VD false) ∧
      sfd_econ.defaultRHS VD false = 6 / 7 + 1 / 2 * VD false := by
  simp only [UEModel.defaultRHS, sfd_econ, Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true]
  norm_num

/-- The default values of the example: `47/42` in normal times, `12/7` in the crisis. -/
noncomputable def sfd_VD (y : Bool) : ℝ := if y then 47 / 42 else 12 / 7

/-- `sfd_VD` solves (24.10), and it is the only solution. -/
theorem sfd_VD_iff (VD : Bool → ℝ) : (∀ y, VD y = sfd_econ.defaultRHS VD y) ↔ VD = sfd_VD := by
  obtain ⟨h1, h2⟩ := sfd_defaultRHS VD
  constructor
  · intro h
    have ht := h true
    have hf := h false
    rw [h1] at ht
    rw [h2] at hf
    funext y
    cases y <;> simp only [sfd_VD, ↓reduceIte, Bool.false_eq_true] <;> linarith
  · rintro rfl y
    cases y
    · rw [h2]; simp only [sfd_VD, ↓reduceIte, Bool.false_eq_true]; norm_num
    · rw [h1]; simp only [sfd_VD, ↓reduceIte, Bool.false_eq_true]; norm_num

/-- The default rule of both equilibria at `δ = 1/2`: never in normal times; in the crisis
exactly on debt above the safe level `1`. -/
noncomputable def sfd_D (b : ℝ) (y : Bool) : ℝ := if y then 0 else if 1 < b then 1 else 0

/-- The crisis repayment value of both equilibria at `δ = 1/2`: `18/7 − (6/7)B`. -/
noncomputable def sfd_VRL (b : ℝ) : ℝ := 18 / 7 - 6 / 7 * b

/-- The crisis price of both equilibria at `δ = 1/2`: risk-free `5/7` on the safe zone. -/
noncomputable def sfd_qL (b : ℝ) : ℝ := if b ≤ 1 then 5 / 7 else 0

/-- The crisis value: `max(12/7, 18/7 − (6/7)B)` is `18/7 − (6/7)B` on the safe zone. -/
theorem sfd_VL_eq (b : ℝ) :
    max (sfd_VD false) (sfd_VRL b) = if b ≤ 1 then 18 / 7 - 6 / 7 * b else 12 / 7 := by
  simp only [sfd_VD, sfd_VRL, Bool.false_eq_true, ↓reduceIte]
  split_ifs with h
  · exact max_eq_right (by linarith)
  · exact max_eq_left (by linarith)

/-- **The crisis block at `δ = 1/2`** (both equilibria): with the crisis price `sfd_qL` and the
crisis value `max(12/7, sfd_VRL)`, issuing up to the safe level `1` is optimal at every debt
`B ∈ [0, 3/2]`, with value `sfd_VRL B`. -/
theorem sfd_crisis_block (q V : ℝ → Bool → ℝ) (hq : ∀ b', q b' false = sfd_qL b')
    (hV : ∀ b', V b' false = max (sfd_VD false) (sfd_VRL b')) (b : ℝ) (hb1 : b ≤ 3 / 2) :
    (∀ b', 0 ≤ b' → b' ≤ 3 / 2 → sfd_econ.ldObj (1 / 2) q V b false b' ≤ sfd_VRL b) ∧
      sfd_econ.ldObj (1 / 2) q V b false 1 = sfd_VRL b := by
  constructor
  · intro b' _ _
    rw [sfd_obj_false, hq, hV, sfd_VL_eq]
    unfold sfd_qL sfd_VRL
    split_ifs <;> linarith
  · rw [sfd_obj_false, hq, hV, sfd_VL_eq]
    unfold sfd_qL sfd_VRL
    norm_num
    ring

/-- The crisis block of the price recursion: with the crisis default rule `sfd_D` and borrowing
`1`, (24.12) gives `sfd_qL`. -/
theorem sfd_crisis_price (q Bh : ℝ → Bool → ℝ) (hq : ∀ b', q b' false = sfd_qL b')
    (hBh : ∀ b', Bh b' false = 1) (b' : ℝ) :
    q b' false = (1 + sfd_econ.r)⁻¹ * ∑ j, sfd_econ.P false j *
      ((1 - sfd_D b' j) * (1 / 2 + (1 - 1 / 2) * q (Bh b' j) j)) := by
  rw [sfd_price_false, hBh, hq, hq]
  unfold sfd_qL sfd_D
  simp only [Bool.false_eq_true, ↓reduceIte, le_refl]
  by_cases h : b' ≤ 1
  · simp only [h, not_lt.2 h, ↓reduceIte]
    norm_num
  · simp only [h, lt_of_not_ge h, ↓reduceIte]
    norm_num

/-- The crisis default rule: `sfd_VRL B < 12/7` iff `B > 1`. -/
theorem sfd_crisis_default (b : ℝ) :
    sfd_D b false = if sfd_VRL b < sfd_VD false then 1 else 0 := by
  unfold sfd_D sfd_VRL sfd_VD
  simp only [Bool.false_eq_true, ↓reduceIte]
  by_cases h : 1 < b
  · have h' : 18 / 7 - 6 / 7 * b < 12 / 7 := by linarith
    simp only [h, h', ↓reduceIte]
  · have h' : ¬ 18 / 7 - 6 / 7 * b < 12 / 7 := by linarith
    simp only [h, h', ↓reduceIte]

/-- The no-dilution repayment values: in normal times `89/21 − (6/7)B` up to `10/9` (the
sovereign holds or brings its debt to the safe level `1`) and `173/42 − (3/4)B` above (it stays
at `B̄`); in the crisis `sfd_VRL`. -/
noncomputable def sfd_VRN (b : ℝ) (y : Bool) : ℝ :=
  if y then (if b ≤ 10 / 9 then 89 / 21 - 6 / 7 * b else 173 / 42 - 3 / 4 * b) else sfd_VRL b

/-- The no-dilution prices: in normal times `5/7` (risk-free) on the safe zone `[0, 1]`, `4/7`
on `(1, 10/9]` (repaid unless the crisis comes, then deleveraged), `1/2` above; in the crisis
`sfd_qL`. -/
noncomputable def sfd_qN (b : ℝ) (y : Bool) : ℝ :=
  if y then (if b ≤ 1 then 5 / 7 else if b ≤ 10 / 9 then 4 / 7 else 1 / 2) else sfd_qL b

/-- The no-dilution borrowing rule: in normal times debt `1` from `B ≤ 10/9`, `B̄ = 3/2`
above; debt `1` in the crisis. -/
noncomputable def sfd_BhN (b : ℝ) (y : Bool) : ℝ :=
  if y then (if b ≤ 10 / 9 then 1 else 3 / 2) else 1

/-- The self-fulfilling-dilution repayment values: in normal times `437/105 − (23/28)B` up to
`3/5` and `173/42 − (3/4)B` above (the sovereign dilutes to `B̄`); in the crisis `sfd_VRL`. -/
noncomputable def sfd_VRS (b : ℝ) (y : Bool) : ℝ :=
  if y then (if b ≤ 3 / 5 then 437 / 105 - 23 / 28 * b else 173 / 42 - 3 / 4 * b) else sfd_VRL b

/-- The self-fulfilling-dilution prices: in normal times `29/42` on `[0, 3/5]`, `9/14` on
`(3/5, 1]` (lenders expect dilution to `B̄`), `1/2` above; in the crisis `sfd_qL`. -/
noncomputable def sfd_qS (b : ℝ) (y : Bool) : ℝ :=
  if y then (if b ≤ 3 / 5 then 29 / 42 else if b ≤ 1 then 9 / 14 else 1 / 2) else sfd_qL b

/-- The self-fulfilling-dilution borrowing rule: in normal times debt `1` from `B ≤ 3/5`,
`B̄ = 3/2` above; debt `1` in the crisis. -/
noncomputable def sfd_BhS (b : ℝ) (y : Bool) : ℝ :=
  if y then (if b ≤ 3 / 5 then 1 else 3 / 2) else 1

/-- In normal times the no-dilution repayment value exceeds the default value `47/42`. -/
theorem sfd_VN_true (b : ℝ) (hb1 : b ≤ 3 / 2) :
    max (sfd_VD true) (sfd_VRN b true) = sfd_VRN b true := by
  apply max_eq_right
  unfold sfd_VD sfd_VRN
  simp only [↓reduceIte]
  split_ifs <;> linarith

/-- In normal times the dilution repayment value exceeds the default value `47/42`. -/
theorem sfd_VS_true (b : ℝ) (hb1 : b ≤ 3 / 2) :
    max (sfd_VD true) (sfd_VRS b true) = sfd_VRS b true := by
  apply max_eq_right
  unfold sfd_VD sfd_VRS
  simp only [↓reduceIte]
  split_ifs <;> linarith

/-- **No dilution is a Markov perfect equilibrium** at `δ = 1/2` (AKMM, p. 901, beyond the
text): `sfd_VRN`, `sfd_D`, `sfd_BhN`, `sfd_qN` satisfy every condition of the definition at
every state `B ∈ [0, 3/2]` and against every `B′ ∈ [0, 3/2]`. -/
theorem sfd_no_dilution_mpe :
    IsBoundedLongMPE sfd_econ (1 / 2) (fun b y => max (sfd_VD y) (sfd_VRN b y)) sfd_VRN sfd_VD
      sfd_D sfd_BhN sfd_qN := by
  have hqL : ∀ b', sfd_qN b' false = sfd_qL b' := fun _ => rfl
  have hVL : ∀ b', (fun b y => max (sfd_VD y) (sfd_VRN b y)) b' false =
      max (sfd_VD false) (sfd_VRL b') := fun _ => rfl
  have hRL : ∀ b', sfd_VRN b' false = sfd_VRL b' := fun _ => rfl
  refine ⟨⟨5, fun b y _ hb1 => ?_⟩, fun _ _ _ _ => rfl, (sfd_VD_iff _).2 rfl,
    fun b y b' hb0 hb1 hb0' hb1' => ?_, fun b' y hb0' hb1' => ?_, fun b y _ hb1 => ?_,
    fun b y _ _ => ?_, fun b y hb0 hb1 => ?_⟩
  · -- bounded values
    rw [sfd_bmax] at hb1
    apply max_le
    · unfold sfd_VD; split_ifs <;> norm_num
    · unfold sfd_VRN sfd_VRL; split_ifs <;> linarith
  · -- (24.11)
    rw [sfd_bmax] at hb1 hb1'
    cases y
    · exact (sfd_crisis_block _ _ hqL hVL b hb1).1 b' hb0' hb1'
    · rw [sfd_obj_true, sfd_VN_true b' hb1', hRL, sfd_VL_eq]
      unfold sfd_VRN sfd_qN
      simp only [↓reduceIte]
      split_ifs <;> linarith
  · -- (24.12)
    cases y
    · exact sfd_crisis_price _ _ hqL (fun _ => rfl) b'
    · rw [sfd_price_true]
      unfold sfd_qN sfd_D sfd_BhN sfd_qL
      simp only [↓reduceIte, Bool.false_eq_true]
      rw [sfd_bmax] at hb1'
      by_cases h1 : b' ≤ 1
      · have h2 : b' ≤ 10 / 9 := by linarith
        simp only [h1, h2, not_lt.2 h1, ↓reduceIte]
        norm_num
      · by_cases h2 : b' ≤ 10 / 9
        · simp only [h1, h2, lt_of_not_ge h1, ↓reduceIte]
          norm_num
        · simp only [h1, h2, lt_of_not_ge h1, ↓reduceIte]
          norm_num
  · -- the default rule
    cases y
    · exact sfd_crisis_default b
    · rw [sfd_bmax] at hb1
      have h : ¬ sfd_VRN b true < sfd_VD true := by
        rw [not_lt, ← sfd_VN_true b hb1]
        exact le_max_left _ _
      simp only [sfd_D, h, ↓reduceIte]
  · -- feasibility
    rw [sfd_bmax]
    unfold sfd_BhN
    cases y
    · norm_num
    · simp only [↓reduceIte]
      split_ifs <;> norm_num
  · -- optimality
    rw [sfd_bmax] at hb1
    cases y
    · exact (sfd_crisis_block _ _ hqL hVL b hb1).2
    · rw [sfd_obj_true]
      unfold sfd_BhN
      simp only [↓reduceIte]
      by_cases h : b ≤ 10 / 9
      · simp only [h, ↓reduceIte]
        rw [sfd_VN_true 1 (by norm_num), hRL, sfd_VL_eq]
        unfold sfd_VRN sfd_qN
        simp only [h, ↓reduceIte]
        norm_num
        ring
      · simp only [h, ↓reduceIte]
        rw [sfd_VN_true (3 / 2) (by norm_num), hRL, sfd_VL_eq]
        unfold sfd_VRN sfd_qN
        simp only [h, ↓reduceIte]
        norm_num
        ring

/-- **Self-fulfilling dilution is a Markov perfect equilibrium** at `δ = 1/2` (AKMM, p. 901,
beyond the text): `sfd_VRS`, `sfd_D`, `sfd_BhS`, `sfd_qS` satisfy every condition of the
definition at every state `B ∈ [0, 3/2]` and against every `B′ ∈ [0, 3/2]`. -/
theorem sfd_dilution_mpe :
    IsBoundedLongMPE sfd_econ (1 / 2) (fun b y => max (sfd_VD y) (sfd_VRS b y)) sfd_VRS sfd_VD
      sfd_D sfd_BhS sfd_qS := by
  have hqL : ∀ b', sfd_qS b' false = sfd_qL b' := fun _ => rfl
  have hVL : ∀ b', (fun b y => max (sfd_VD y) (sfd_VRS b y)) b' false =
      max (sfd_VD false) (sfd_VRL b') := fun _ => rfl
  have hRL : ∀ b', sfd_VRS b' false = sfd_VRL b' := fun _ => rfl
  refine ⟨⟨5, fun b y _ hb1 => ?_⟩, fun _ _ _ _ => rfl, (sfd_VD_iff _).2 rfl,
    fun b y b' hb0 hb1 hb0' hb1' => ?_, fun b' y hb0' hb1' => ?_, fun b y _ hb1 => ?_,
    fun b y _ _ => ?_, fun b y hb0 hb1 => ?_⟩
  · -- bounded values
    rw [sfd_bmax] at hb1
    apply max_le
    · unfold sfd_VD; split_ifs <;> norm_num
    · unfold sfd_VRS sfd_VRL; split_ifs <;> linarith
  · -- (24.11)
    rw [sfd_bmax] at hb1 hb1'
    cases y
    · exact (sfd_crisis_block _ _ hqL hVL b hb1).1 b' hb0' hb1'
    · rw [sfd_obj_true, sfd_VS_true b' hb1', hRL, sfd_VL_eq]
      unfold sfd_VRS sfd_qS
      simp only [↓reduceIte]
      split_ifs <;> linarith
  · -- (24.12)
    cases y
    · exact sfd_crisis_price _ _ hqL (fun _ => rfl) b'
    · rw [sfd_price_true]
      unfold sfd_qS sfd_D sfd_BhS sfd_qL
      simp only [↓reduceIte, Bool.false_eq_true]
      rw [sfd_bmax] at hb1'
      by_cases h1 : b' ≤ 3 / 5
      · have h2 : b' ≤ 1 := by linarith
        simp only [h1, not_lt.2 h2, ↓reduceIte]
        norm_num
      · by_cases h2 : b' ≤ 1
        · simp only [h1, h2, not_lt.2 h2, ↓reduceIte]
          norm_num
        · simp only [h1, h2, lt_of_not_ge h2, ↓reduceIte]
          norm_num
  · -- the default rule
    cases y
    · exact sfd_crisis_default b
    · rw [sfd_bmax] at hb1
      have h : ¬ sfd_VRS b true < sfd_VD true := by
        rw [not_lt, ← sfd_VS_true b hb1]
        exact le_max_left _ _
      simp only [sfd_D, h, ↓reduceIte]
  · -- feasibility
    rw [sfd_bmax]
    unfold sfd_BhS
    cases y
    · norm_num
    · simp only [↓reduceIte]
      split_ifs <;> norm_num
  · -- optimality
    rw [sfd_bmax] at hb1
    cases y
    · exact (sfd_crisis_block _ _ hqL hVL b hb1).2
    · rw [sfd_obj_true]
      unfold sfd_BhS
      simp only [↓reduceIte]
      by_cases h : b ≤ 3 / 5
      · simp only [h, ↓reduceIte]
        rw [sfd_VS_true 1 (by norm_num), hRL, sfd_VL_eq]
        unfold sfd_VRS sfd_qS
        simp only [h, ↓reduceIte]
        norm_num
        ring
      · simp only [h, ↓reduceIte]
        rw [sfd_VS_true (3 / 2) (by norm_num), hRL, sfd_VL_eq]
        unfold sfd_VRS sfd_qS
        simp only [h, ↓reduceIte]
        norm_num
        ring

/-- **The two equilibria have different values**: in normal times the repayment value (and
the value) under self-fulfilling dilution is strictly below the no-dilution value at every debt
below `10/9`, and equal from `10/9` on. -/
theorem sfd_values_differ (b : ℝ) :
    (b < 10 / 9 → sfd_VRS b true < sfd_VRN b true) ∧
      (10 / 9 ≤ b → sfd_VRS b true = sfd_VRN b true) := by
  unfold sfd_VRS sfd_VRN
  simp only [↓reduceIte]
  constructor
  · intro h
    split_ifs <;> linarith
  · intro h
    have h1 : ¬ b ≤ 3 / 5 := by linarith
    by_cases h2 : b ≤ 10 / 9
    · have h3 : b = 10 / 9 := le_antisymm h2 h
      simp only [h1, h2, ↓reduceIte]
      rw [h3]
      norm_num
    · simp only [h1, h2, ↓reduceIte]

/-- **Expected dilution lowers prices**: the dilution prices are never above the no-dilution
prices, and in normal times strictly below them on `[0, 10/9]`. -/
theorem sfd_dilution_lowers_prices (b' : ℝ) (y : Bool) :
    sfd_qS b' y ≤ sfd_qN b' y ∧ (b' ≤ 10 / 9 → sfd_qS b' true < sfd_qN b' true) := by
  unfold sfd_qS sfd_qN
  constructor
  · cases y
    · exact le_rfl
    · simp only [↓reduceIte]
      split_ifs <;> linarith
  · intro h
    simp only [↓reduceIte]
    split_ifs <;> linarith

/-- **The sovereign strictly prefers to dilute when lenders expect it, and strictly prefers not
to when they do not**: at every debt `B ∈ (3/5, 10/9)` in normal times, facing the no-dilution
prices the sovereign strictly prefers debt `1` (safe) to `B̄ = 3/2`, and facing the dilution
prices it strictly prefers `B̄` to `1`. -/
theorem sfd_strict_preference (b : ℝ) (hb : 3 / 5 < b) (hb' : b < 10 / 9) :
    sfd_econ.ldObj (1 / 2) sfd_qN (fun b y => max (sfd_VD y) (sfd_VRN b y)) b true (3 / 2) <
        sfd_econ.ldObj (1 / 2) sfd_qN (fun b y => max (sfd_VD y) (sfd_VRN b y)) b true 1 ∧
      sfd_econ.ldObj (1 / 2) sfd_qS (fun b y => max (sfd_VD y) (sfd_VRS b y)) b true 1 <
        sfd_econ.ldObj (1 / 2) sfd_qS (fun b y => max (sfd_VD y) (sfd_VRS b y)) b true (3 / 2) := by
  have hRN : ∀ b', sfd_VRN b' false = sfd_VRL b' := fun _ => rfl
  have hRS : ∀ b', sfd_VRS b' false = sfd_VRL b' := fun _ => rfl
  rw [sfd_obj_true, sfd_obj_true, sfd_obj_true, sfd_obj_true, sfd_VN_true 1 (by norm_num),
    sfd_VN_true (3 / 2) (by norm_num), sfd_VS_true 1 (by norm_num),
    sfd_VS_true (3 / 2) (by norm_num), hRN, hRN, hRS, hRS, sfd_VL_eq, sfd_VL_eq]
  unfold sfd_qN sfd_qS sfd_VRN sfd_VRS
  norm_num
  constructor <;> linarith

/-- **Two Markov perfect equilibria with long-term debt and strictly different values** (AKMM,
p. 901, beyond the text; Aguiar–Amador's self-fulfilling debt dilution): at `δ = 1/2` the
economy `sfd_econ` has the no-dilution equilibrium and the self-fulfilling-dilution
equilibrium, with the same default rule, and the value at zero debt is strictly lower under
dilution. -/
theorem sfd_two_mpe :
    IsBoundedLongMPE sfd_econ (1 / 2) (fun b y => max (sfd_VD y) (sfd_VRN b y)) sfd_VRN sfd_VD
        sfd_D sfd_BhN sfd_qN ∧
      IsBoundedLongMPE sfd_econ (1 / 2) (fun b y => max (sfd_VD y) (sfd_VRS b y)) sfd_VRS
        sfd_VD sfd_D sfd_BhS sfd_qS ∧
      max (sfd_VD true) (sfd_VRS 0 true) < max (sfd_VD true) (sfd_VRN 0 true) := by
  refine ⟨sfd_no_dilution_mpe, sfd_dilution_mpe, ?_⟩
  rw [sfd_VN_true 0 (by norm_num), sfd_VS_true 0 (by norm_num)]
  exact (sfd_values_differ 0).1 (by norm_num)

/-- The objective at `δ = 1` in normal times. -/
theorem sfd_obj_one_true (q V : ℝ → Bool → ℝ) (b b' : ℝ) :
    sfd_econ.ldObj 1 q V b true b' =
      2 - b + q b' true * b' + 1 / 2 * (4 / 5 * V b' true + 1 / 5 * V b' false) := by
  rw [sfd_obj_true]
  ring

/-- The objective at `δ = 1` in the crisis. -/
theorem sfd_obj_one_false (q V : ℝ → Bool → ℝ) (b b' : ℝ) :
    sfd_econ.ldObj 1 q V b false b' = 1 - b + q b' false * b' + 1 / 2 * V b' false := by
  rw [sfd_obj_false]
  ring

/-- With one-period debt and linear utility the objective is the objective at zero debt
minus the debt. -/
theorem sfd_obj_one_shift (q V : ℝ → Bool → ℝ) (b b' : ℝ) (y : Bool) :
    sfd_econ.ldObj 1 q V b y b' = sfd_econ.ldObj 1 q V 0 y b' - b := by
  cases y
  · rw [sfd_obj_one_false, sfd_obj_one_false]; ring
  · rw [sfd_obj_one_true, sfd_obj_one_true]; ring

/-- The repayment values of the one-period-debt equilibrium: `30/7 − B` in normal times,
`18/7 − B` in the crisis. -/
noncomputable def sfd_VR1 (b : ℝ) (y : Bool) : ℝ := if y then 30 / 7 - b else 18 / 7 - b

/-- The default rule of the one-period-debt equilibrium: never in normal times; in the crisis
on debt above `6/7`. -/
noncomputable def sfd_D1 (b : ℝ) (y : Bool) : ℝ := if y then 0 else if 6 / 7 < b then 1 else 0

/-- The prices of the one-period-debt equilibrium: `5/6` on `[0, 6/7]`; above, `2/3` in normal
times and `0` in the crisis. -/
noncomputable def sfd_q1 (b : ℝ) (y : Bool) : ℝ :=
  if y then (if b ≤ 6 / 7 then 5 / 6 else 2 / 3) else (if b ≤ 6 / 7 then 5 / 6 else 0)

/-- The borrowing rule of the one-period-debt equilibrium: `B̄ = 3/2` in normal times, `6/7` in
the crisis. -/
noncomputable def sfd_Bh1 (_ : ℝ) (y : Bool) : ℝ := if y then 3 / 2 else 6 / 7

/-- **With one-period debt the economy has a Markov perfect equilibrium** (`δ = 1`): the
crisis capacity is `6/7`, and in normal times the sovereign borrows up to `B̄`. -/
theorem sfd_one_period_mpe :
    IsBoundedLongMPE sfd_econ 1 (fun b y => max (sfd_VD y) (sfd_VR1 b y)) sfd_VR1 sfd_VD sfd_D1
      sfd_Bh1 sfd_q1 := by
  have hVH : ∀ b', b' ≤ 3 / 2 → max (sfd_VD true) (sfd_VR1 b' true) = 30 / 7 - b' :=
    fun b' h => by
      unfold sfd_VD sfd_VR1
      simp only [↓reduceIte]
      exact max_eq_right (by linarith)
  have hVL : ∀ b', max (sfd_VD false) (sfd_VR1 b' false) =
      if b' ≤ 6 / 7 then 18 / 7 - b' else 12 / 7 := fun b' => by
    unfold sfd_VD sfd_VR1
    simp only [↓reduceIte, Bool.false_eq_true]
    split_ifs with h
    · exact max_eq_right (by linarith)
    · exact max_eq_left (by linarith)
  refine ⟨⟨5, fun b y _ hb1 => ?_⟩, fun _ _ _ _ => rfl, (sfd_VD_iff _).2 rfl,
    fun b y b' hb0 hb1 hb0' hb1' => ?_, fun b' y hb0' hb1' => ?_, fun b y _ hb1 => ?_,
    fun b y _ _ => ?_, fun b y hb0 hb1 => ?_⟩
  · apply max_le
    · unfold sfd_VD; split_ifs <;> norm_num
    · unfold sfd_VR1; split_ifs <;> linarith
  · rw [sfd_bmax] at hb1'
    cases y
    · rw [sfd_obj_one_false, hVL]
      unfold sfd_q1 sfd_VR1
      simp only [↓reduceIte, Bool.false_eq_true]
      split_ifs <;> linarith
    · rw [sfd_obj_one_true, hVH b' hb1', hVL]
      unfold sfd_q1 sfd_VR1
      simp only [↓reduceIte]
      split_ifs <;> linarith
  · cases y
    · rw [sfd_price_false]
      unfold sfd_q1 sfd_D1
      simp only [↓reduceIte, Bool.false_eq_true]
      by_cases h : b' ≤ 6 / 7
      · simp only [h, not_lt.2 h, ↓reduceIte]; norm_num
      · simp only [h, lt_of_not_ge h, ↓reduceIte]; norm_num
    · rw [sfd_price_true]
      unfold sfd_q1 sfd_D1
      simp only [↓reduceIte, Bool.false_eq_true]
      by_cases h : b' ≤ 6 / 7
      · simp only [h, not_lt.2 h, ↓reduceIte]; norm_num
      · simp only [h, lt_of_not_ge h, ↓reduceIte]; norm_num
  · rw [sfd_bmax] at hb1
    unfold sfd_D1 sfd_VR1 sfd_VD
    cases y
    · simp only [↓reduceIte, Bool.false_eq_true]
      by_cases h : 6 / 7 < b
      · have h' : 18 / 7 - b < 12 / 7 := by linarith
        simp only [h, h', ↓reduceIte]
      · have h' : ¬ 18 / 7 - b < 12 / 7 := by linarith
        simp only [h, h', ↓reduceIte]
    · have h' : ¬ 30 / 7 - b < 47 / 42 := by linarith
      simp only [h', ↓reduceIte]
  · rw [sfd_bmax]
    unfold sfd_Bh1
    cases y <;> norm_num
  · rw [sfd_bmax] at hb1
    cases y
    · rw [sfd_obj_one_false, hVL]
      unfold sfd_q1 sfd_VR1 sfd_Bh1
      norm_num
      ring
    · rw [sfd_obj_one_true, hVH _ (by unfold sfd_Bh1; norm_num), hVL]
      unfold sfd_q1 sfd_VR1 sfd_Bh1
      norm_num
      ring

/-- **Every Markov perfect equilibrium with one-period debt is the one of
`sfd_one_period_mpe`** (on the state space `[0, 3/2]`). With `δ = 1` and linear utility the
repayment value is `V^R(0, Y) − B` (the objective is the objective at zero debt minus `B`). The
default value solves (24.10); in normal times repaying at least matches defaulting (`φ ≥ B̄`).
In the crisis the debt capacity `V^R(0, L) − 12/7` is pinned at `6/7`: a larger value could not
be financed, a smaller one leaves a profitable debt issue below the capacity unused. Then prices
are determined, and so is `V^R(0, H) = 30/7`. -/
theorem sfd_one_period_char {V VR D Bh q : ℝ → Bool → ℝ} {VD : Bool → ℝ}
    (h : IsBoundedLongMPE sfd_econ 1 V VR VD D Bh q) :
    VD = sfd_VD ∧ ∀ b y, 0 ≤ b → b ≤ sfd_econ.bmax →
      VR b y = sfd_VR1 b y ∧ D b y = sfd_D1 b y ∧ q b y = sfd_q1 b y ∧
        V b y = max (sfd_VD y) (sfd_VR1 b y) := by
  have hVD : VD = sfd_VD := (sfd_VD_iff VD).1 h.eq_24_10
  have hbm := sfd_bmax
  have hVDt : VD true = 47 / 42 := by rw [hVD]; rfl
  have hVDf : VD false = 12 / 7 := by rw [hVD]; rfl
  -- the repayment value is `V^R(0, Y) − B`
  have hVR : ∀ b y, 0 ≤ b → b ≤ 3 / 2 → VR b y = VR 0 y - b := by
    intro b y hb0 hb1
    obtain ⟨hm0, hm1⟩ := h.borrow_mem b y hb0 (by rw [hbm]; exact hb1)
    obtain ⟨hn0, hn1⟩ := h.borrow_mem 0 y le_rfl (by rw [hbm]; norm_num)
    have e1 := h.borrow_opt b y hb0 (by rw [hbm]; exact hb1)
    have i1 := h.eq_24_11 0 y (Bh b y) le_rfl (by rw [hbm]; norm_num) hm0 hm1
    have e0 := h.borrow_opt 0 y le_rfl (by rw [hbm]; norm_num)
    have i0 := h.eq_24_11 b y (Bh 0 y) hb0 (by rw [hbm]; exact hb1) hn0 hn1
    rw [sfd_obj_one_shift] at e1 i0
    linarith
  have hVge : ∀ b y, 0 ≤ b → b ≤ 3 / 2 → VD y ≤ V b y := fun b y hb0 hb1 => by
    rw [h.eq_24_9 b y hb0 (by rw [hbm]; exact hb1)]
    exact le_max_left _ _
  have hdef : ∀ b y, 0 ≤ b → b ≤ 3 / 2 → D b y = if VR b y < VD y then 1 else 0 :=
    fun b y hb0 hb1 => h.default_opt b y hb0 (by rw [hbm]; exact hb1)
  have hprice : ∀ b' y, 0 ≤ b' → b' ≤ 3 / 2 → q b' y = (1 + sfd_econ.r)⁻¹ *
      ∑ j, sfd_econ.P y j * ((1 - D b' j) * (1 + (1 - 1) * q (Bh b' j) j)) :=
    fun b' y hb0 hb1 => h.eq_24_12 b' y hb0 (by rw [hbm]; exact hb1)
  -- in normal times the sovereign repays
  have hH : ∀ b, 0 ≤ b → b ≤ 3 / 2 → 47 / 42 ≤ VR b true := by
    intro b hb0 hb1
    have i := h.eq_24_11 b true 0 hb0 (by rw [hbm]; exact hb1) le_rfl (by rw [hbm]; norm_num)
    rw [sfd_obj_one_true, mul_zero] at i
    have h1 := hVge 0 true le_rfl (by norm_num)
    have h2 := hVge 0 false le_rfl (by norm_num)
    rw [hVDt] at h1
    rw [hVDf] at h2
    linarith
  have hDt : ∀ b, 0 ≤ b → b ≤ 3 / 2 → D b true = 0 := fun b hb0 hb1 => by
    rw [hdef b true hb0 hb1, hVDt]
    simp only [not_lt.2 (hH b hb0 hb1), ↓reduceIte]
  -- the crisis
  have hVf : ∀ b, 0 ≤ b → b ≤ 3 / 2 → V b false = max (12 / 7) (VR 0 false - b) :=
    fun b hb0 hb1 => by
      rw [h.eq_24_9 b false hb0 (by rw [hbm]; exact hb1), hVDf, hVR b false hb0 hb1]
  have hDf : ∀ b, 0 ≤ b → b ≤ 3 / 2 →
      D b false = if VR 0 false - b < 12 / 7 then 1 else 0 := fun b hb0 hb1 => by
    rw [hdef b false hb0 hb1, hVDf, hVR b false hb0 hb1]
  have hqf : ∀ b', 0 ≤ b' → b' ≤ 3 / 2 → q b' false = 5 / 6 * (1 - D b' false) :=
    fun b' hb0 hb1 => by
      rw [hprice b' false hb0 hb1, sfd_price_false]
      ring
  have hcL : VR 0 false = 18 / 7 := by
    obtain ⟨hn0, hn1⟩ := h.borrow_mem 0 false le_rfl (by rw [hbm]; norm_num)
    rw [hbm] at hn1
    have e := h.borrow_opt 0 false le_rfl (by rw [hbm]; norm_num)
    rw [sfd_obj_one_false, hqf _ hn0 hn1, hDf _ hn0 hn1, hVf _ hn0 hn1] at e
    apply le_antisymm
    · by_cases hlt : VR 0 false - Bh 0 false < 12 / 7
      · rw [max_eq_left hlt.le] at e
        simp only [hlt, ↓reduceIte] at e
        linarith
      · rw [max_eq_right (not_lt.1 hlt)] at e
        simp only [hlt, ↓reduceIte] at e
        linarith
    · by_contra hc
      rw [not_le] at hc
      by_cases h12 : 12 / 7 ≤ VR 0 false
      · have hs0 : 0 ≤ VR 0 false - 12 / 7 := by linarith
        have hs1 : VR 0 false - 12 / 7 ≤ 3 / 2 := by linarith
        have i := h.eq_24_11 0 false (VR 0 false - 12 / 7) le_rfl (by rw [hbm]; norm_num) hs0
          (by rw [hbm]; exact hs1)
        have hne : ¬ VR 0 false - (VR 0 false - 12 / 7) < 12 / 7 := by linarith
        rw [sfd_obj_one_false, hqf _ hs0 hs1, hDf _ hs0 hs1, hVf _ hs0 hs1] at i
        simp only [hne, ↓reduceIte] at i
        rw [max_eq_left (by linarith)] at i
        linarith
      · have i := h.eq_24_11 0 false 0 le_rfl (by rw [hbm]; norm_num) le_rfl
          (by rw [hbm]; norm_num)
        rw [sfd_obj_one_false, mul_zero] at i
        have h2 := hVge 0 false le_rfl (by norm_num)
        rw [hVDf] at h2
        linarith
  have hDf' : ∀ b, 0 ≤ b → b ≤ 3 / 2 → D b false = sfd_D1 b false := fun b hb0 hb1 => by
    rw [hDf b hb0 hb1, hcL]
    unfold sfd_D1
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hb : 6 / 7 < b
    · have h' : 18 / 7 - b < 12 / 7 := by linarith
      simp only [hb, h', ↓reduceIte]
    · have h' : ¬ 18 / 7 - b < 12 / 7 := by linarith
      simp only [hb, h', ↓reduceIte]
  have hqt : ∀ b', 0 ≤ b' → b' ≤ 3 / 2 → q b' true = 5 / 6 * (4 / 5 + 1 / 5 * (1 - D b' false)) :=
    fun b' hb0 hb1 => by
      rw [hprice b' true hb0 hb1, sfd_price_true, hDt b' hb0 hb1]
      ring
  -- normal times
  have hVt : ∀ b, 0 ≤ b → b ≤ 3 / 2 → V b true = VR 0 true - b := fun b hb0 hb1 => by
    rw [h.eq_24_9 b true hb0 (by rw [hbm]; exact hb1), hVDt, hVR b true hb0 hb1]
    exact max_eq_right (by rw [← hVR b true hb0 hb1]; exact hH b hb0 hb1)
  have hcH : VR 0 true = 30 / 7 := by
    obtain ⟨hn0, hn1⟩ := h.borrow_mem 0 true le_rfl (by rw [hbm]; norm_num)
    rw [hbm] at hn1
    have e := h.borrow_opt 0 true le_rfl (by rw [hbm]; norm_num)
    rw [sfd_obj_one_true, hqt _ hn0 hn1, hDf' _ hn0 hn1, hVt _ hn0 hn1, hVf _ hn0 hn1,
      hcL] at e
    have i := h.eq_24_11 0 true (3 / 2) le_rfl (by rw [hbm]; norm_num) (by norm_num)
      (by rw [hbm])
    rw [sfd_obj_one_true, hqt _ (by norm_num) le_rfl, hDf' _ (by norm_num) le_rfl,
      hVt _ (by norm_num) le_rfl, hVf _ (by norm_num) le_rfl, hcL] at i
    unfold sfd_D1 at e i
    simp only [Bool.false_eq_true, ↓reduceIte] at e i
    norm_num at i
    apply le_antisymm
    · by_cases hb : 6 / 7 < Bh 0 true
      · simp only [hb, ↓reduceIte] at e
        rw [max_eq_left (by linarith)] at e
        linarith
      · simp only [hb, ↓reduceIte] at e
        rw [max_eq_right (by linarith)] at e
        linarith
    · linarith
  refine ⟨hVD, fun b y hb0 hb1 => ?_⟩
  rw [hbm] at hb1
  have hq1 : q b y = sfd_q1 b y := by
    cases y
    · rw [hqf b hb0 hb1, hDf' b hb0 hb1]
      unfold sfd_D1 sfd_q1
      simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hb : b ≤ 6 / 7
      · simp only [hb, not_lt.2 hb, ↓reduceIte]; norm_num
      · simp only [hb, lt_of_not_ge hb, ↓reduceIte]; norm_num
    · rw [hqt b hb0 hb1, hDf' b hb0 hb1]
      unfold sfd_D1 sfd_q1
      simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hb : b ≤ 6 / 7
      · simp only [hb, not_lt.2 hb, ↓reduceIte]; norm_num
      · simp only [hb, lt_of_not_ge hb, ↓reduceIte]; norm_num
  have hVR1 : VR b y = sfd_VR1 b y := by
    rw [hVR b y hb0 hb1]
    unfold sfd_VR1
    cases y
    · rw [hcL]; rfl
    · rw [hcH]; rfl
  refine ⟨hVR1, ?_, hq1, ?_⟩
  · cases y
    · exact hDf' b hb0 hb1
    · rw [hDt b hb0 hb1]; rfl
  · rw [h.eq_24_9 b y hb0 (by rw [hbm]; exact hb1), hVR1, hVD]

/-- **With one-period debt the same economy has exactly one Markov perfect equilibrium**
(AKMM, p. 901, beyond the text): it exists (`sfd_one_period_mpe`), and any two equilibria have
the same default values and, at every state in `[0, B̄]`, the same values, repayment values,
default rule and prices (`sfd_one_period_char`). So the multiplicity of `sfd_two_mpe` is due to
long-term debt. -/
theorem sfd_one_period_unique :
    (∃ (V VR : ℝ → Bool → ℝ) (VD : Bool → ℝ) (D Bh q : ℝ → Bool → ℝ),
      IsBoundedLongMPE sfd_econ 1 V VR VD D Bh q) ∧
      ∀ {V₁ VR₁ D₁ Bh₁ q₁ V₂ VR₂ D₂ Bh₂ q₂ : ℝ → Bool → ℝ} {VD₁ VD₂ : Bool → ℝ},
        IsBoundedLongMPE sfd_econ 1 V₁ VR₁ VD₁ D₁ Bh₁ q₁ →
        IsBoundedLongMPE sfd_econ 1 V₂ VR₂ VD₂ D₂ Bh₂ q₂ →
        VD₁ = VD₂ ∧ ∀ b y, 0 ≤ b → b ≤ sfd_econ.bmax →
          V₁ b y = V₂ b y ∧ VR₁ b y = VR₂ b y ∧ D₁ b y = D₂ b y ∧ q₁ b y = q₂ b y := by
  refine ⟨⟨_, _, _, _, _, _, sfd_one_period_mpe⟩, fun h₁ h₂ => ?_⟩
  obtain ⟨e₁, f₁⟩ := sfd_one_period_char h₁
  obtain ⟨e₂, f₂⟩ := sfd_one_period_char h₂
  refine ⟨e₁.trans e₂.symm, fun b y hb0 hb1 => ?_⟩
  obtain ⟨a₁, b₁, c₁, d₁⟩ := f₁ b y hb0 hb1
  obtain ⟨a₂, b₂, c₂, d₂⟩ := f₂ b y hb0 hb1
  exact ⟨d₁.trans d₂.symm, a₁.trans a₂.symm, b₁.trans b₂.symm, c₁.trans c₂.symm⟩

/-- **Strict multiplicity due to long-term debt** (AKMM, p. 901; Aguiar and Amador 2020,
beyond the text): the economy `sfd_econ` has two Markov perfect equilibria at `δ = 1/2` with
strictly different values (`sfd_two_mpe`), and exactly one at `δ = 1`
(`sfd_one_period_unique`). -/
theorem sfd_strict_multiplicity :
    (∃ (V₁ VR₁ V₂ VR₂ : ℝ → Bool → ℝ) (VD : Bool → ℝ) (D Bh₁ q₁ Bh₂ q₂ : ℝ → Bool → ℝ),
      IsBoundedLongMPE sfd_econ (1 / 2) V₁ VR₁ VD D Bh₁ q₁ ∧
        IsBoundedLongMPE sfd_econ (1 / 2) V₂ VR₂ VD D Bh₂ q₂ ∧ V₂ 0 true < V₁ 0 true) ∧
      (∃ (V VR : ℝ → Bool → ℝ) (VD : Bool → ℝ) (D Bh q : ℝ → Bool → ℝ),
        IsBoundedLongMPE sfd_econ 1 V VR VD D Bh q) ∧
      ∀ {V₁ VR₁ D₁ Bh₁ q₁ V₂ VR₂ D₂ Bh₂ q₂ : ℝ → Bool → ℝ} {VD₁ VD₂ : Bool → ℝ},
        IsBoundedLongMPE sfd_econ 1 V₁ VR₁ VD₁ D₁ Bh₁ q₁ →
        IsBoundedLongMPE sfd_econ 1 V₂ VR₂ VD₂ D₂ Bh₂ q₂ →
        ∀ b y, 0 ≤ b → b ≤ sfd_econ.bmax → V₁ b y = V₂ b y := by
  obtain ⟨h1, h2, h3⟩ := sfd_two_mpe
  refine ⟨⟨_, _, _, _, _, _, _, _, _, _, h1, h2, h3⟩, sfd_one_period_unique.1,
    fun h₁ h₂ b y hb0 hb1 => ((sfd_one_period_unique.2 h₁ h₂).2 b y hb0 hb1).1⟩

end AKMM.SovereignDefault

set_option linter.style.longLine false
#print axioms AKMM.SovereignDefault.defaultRule
#print axioms AKMM.SovereignDefault.cons2Of
#print axioms AKMM.SovereignDefault.cons2
#print axioms AKMM.SovereignDefault.eq_24_3
#print axioms AKMM.SovereignDefault.tp_defaultRule_mem
#print axioms AKMM.SovereignDefault.tp_defaultRule_eq
#print axioms AKMM.SovereignDefault.eq_24_4
#print axioms AKMM.SovereignDefault.tp_repay_at_indifference
#print axioms AKMM.SovereignDefault.tp_cons2_eq
#print axioms AKMM.SovereignDefault.tp_cons2_eq_max
#print axioms AKMM.SovereignDefault.tp_defaultRule_optimal
#print axioms AKMM.SovereignDefault.tp_cons2_antitone
#print axioms AKMM.SovereignDefault.tp_cons2_continuous
#print axioms AKMM.SovereignDefault.tp_cons2_bounds
#print axioms AKMM.SovereignDefault.tp_one_sub_defaultRule
#print axioms AKMM.SovereignDefault.price
#print axioms AKMM.SovereignDefault.tp_price_eq_measure
#print axioms AKMM.SovereignDefault.tp_measureReal_Ici
#print axioms AKMM.SovereignDefault.eq_24_5
#print axioms AKMM.SovereignDefault.eq_24_5_printed_false
#print axioms AKMM.SovereignDefault.tp_uniform_admissible
#print axioms AKMM.SovereignDefault.tp_zero_profit
#print axioms AKMM.SovereignDefault.tp_price_mem_Icc
#print axioms AKMM.SovereignDefault.tp_price_zero
#print axioms AKMM.SovereignDefault.tp_price_antitone
#print axioms AKMM.SovereignDefault.tp_price_strictAntiOn
#print axioms AKMM.SovereignDefault.tp_price_tendsto_zero
#print axioms AKMM.SovereignDefault.tp_price_continuous
#print axioms AKMM.SovereignDefault.tp_price_hasDerivAt
#print axioms AKMM.SovereignDefault.fn_8
#print axioms AKMM.SovereignDefault.tp_contingent_no_default
#print axioms AKMM.SovereignDefault.tp_contingent_revenue
#print axioms AKMM.SovereignDefault.fn_14
#print axioms AKMM.SovereignDefault.tp_objective
#print axioms AKMM.SovereignDefault.tp_cons2_continuous_Y
#print axioms AKMM.SovereignDefault.tp_cons2_lipschitz
#print axioms AKMM.SovereignDefault.tp_revenue_tendsto_zero
#print axioms AKMM.SovereignDefault.tp_exists_optimal
#print axioms AKMM.SovereignDefault.tp_laffer_side
#print axioms AKMM.SovereignDefault.tp_hasDerivAt_expectedUtility
#print axioms AKMM.SovereignDefault.eq_24_6
#print axioms AKMM.SovereignDefault.ltd_stock
#print axioms AKMM.SovereignDefault.eq_24_7
#print axioms AKMM.SovereignDefault.ltd_payment
#print axioms AKMM.SovereignDefault.ltd_coupon_due
#print axioms AKMM.SovereignDefault.ltd_payments_sufficient
#print axioms AKMM.SovereignDefault.ltd_same_stock_same_payments
#print axioms AKMM.SovereignDefault.eq_24_8
#print axioms AKMM.SovereignDefault.ltd_hasSum_coupons
#print axioms AKMM.SovereignDefault.ltd_pv_bond
#print axioms AKMM.SovereignDefault.ltd_pv_stock_timing
#print axioms AKMM.SovereignDefault.ltd_yield
#print axioms AKMM.SovereignDefault.ltd_yield_iff
#print axioms AKMM.SovereignDefault.ltd_coupon
#print axioms AKMM.SovereignDefault.ltd_duration
#print axioms AKMM.SovereignDefault.ltd_spread
#print axioms AKMM.SovereignDefault.ltd_spread_pos_iff
#print axioms AKMM.SovereignDefault.ltd_haircut
#print axioms AKMM.SovereignDefault.eq_24_2
#print axioms AKMM.SovereignDefault.bp_op
#print axioms AKMM.SovereignDefault.BPAdmissible
#print axioms AKMM.SovereignDefault.BPAdmissible.mk
#print axioms AKMM.SovereignDefault.BPAdmissible.markov
#print axioms AKMM.SovereignDefault.BPAdmissible.D_nonneg
#print axioms AKMM.SovereignDefault.BPAdmissible.D_le_one
#print axioms AKMM.SovereignDefault.BPAdmissible.B_nonneg
#print axioms AKMM.SovereignDefault.BPAdmissible.B_sum
#print axioms AKMM.SovereignDefault.BPAdmissible.δ_nonneg
#print axioms AKMM.SovereignDefault.BPAdmissible.δ_le_one
#print axioms AKMM.SovereignDefault.BPAdmissible.r_gt
#print axioms AKMM.SovereignDefault.BPAdmissible.δr_pos
#print axioms AKMM.SovereignDefault.bp_admissible_example
#print axioms AKMM.SovereignDefault.bp_op_sub_le
#print axioms AKMM.SovereignDefault.bp_contracting
#print axioms AKMM.SovereignDefault.bp_op_mapsTo
#print axioms AKMM.SovereignDefault.eq_24_A_6
#print axioms AKMM.SovereignDefault.eq_24_A_2
#print axioms AKMM.SovereignDefault.bp_op12
#print axioms AKMM.SovereignDefault.bp_op12_eq
#print axioms AKMM.SovereignDefault.eq_24_12
#print axioms AKMM.SovereignDefault.bp_riskfree
#print axioms AKMM.SovereignDefault.bp_one_period
#print axioms AKMM.SovereignDefault.bp_one_period_independent
#print axioms AKMM.SovereignDefault.bp_long_term_depends_on_borrowing
#print axioms AKMM.SovereignDefault.SDModel
#print axioms AKMM.SovereignDefault.SDModel.mk
#print axioms AKMM.SovereignDefault.SDModel.inc
#print axioms AKMM.SovereignDefault.SDModel.P
#print axioms AKMM.SovereignDefault.SDModel.markov
#print axioms AKMM.SovereignDefault.SDModel.bond
#print axioms AKMM.SovereignDefault.SDModel.b₀
#print axioms AKMM.SovereignDefault.SDModel.bond_b₀
#print axioms AKMM.SovereignDefault.SDModel.u
#print axioms AKMM.SovereignDefault.SDModel.φ
#print axioms AKMM.SovereignDefault.SDModel.β
#print axioms AKMM.SovereignDefault.SDModel.β_nonneg
#print axioms AKMM.SovereignDefault.SDModel.β_lt_one
#print axioms AKMM.SovereignDefault.SDModel.ψ
#print axioms AKMM.SovereignDefault.SDModel.ψ_nonneg
#print axioms AKMM.SovereignDefault.SDModel.ψ_le_one
#print axioms AKMM.SovereignDefault.SDModel.δ
#print axioms AKMM.SovereignDefault.SDModel.δ_nonneg
#print axioms AKMM.SovereignDefault.SDModel.δ_le_one
#print axioms AKMM.SovereignDefault.SDModel.cons
#print axioms AKMM.SovereignDefault.SDModel.defaultValue
#print axioms AKMM.SovereignDefault.SDModel.repayValue
#print axioms AKMM.SovereignDefault.SDModel.rdp
#print axioms AKMM.SovereignDefault.SDModel.sd_isContracting
#print axioms AKMM.SovereignDefault.SDModel.sd_T_good
#print axioms AKMM.SovereignDefault.SDModel.sd_T_excluded
#print axioms AKMM.SovereignDefault.SDModel.eq_24_A_1
#print axioms AKMM.SovereignDefault.SDModel.eq_24_9_to_24_11
#print axioms AKMM.SovereignDefault.SDModel.sd_VR_antitone
#print axioms AKMM.SovereignDefault.SDModel.sd_V_antitone
#print axioms AKMM.SovereignDefault.SDModel.sd_default_set_mono
#print axioms AKMM.SovereignDefault.SDModel.sd_repay_set_antitone
#print axioms AKMM.SovereignDefault.sd_example
#print axioms AKMM.SovereignDefault.sd_example_solution
#print axioms AKMM.SovereignDefault.IsMPE
#print axioms AKMM.SovereignDefault.IsMPE.mk
#print axioms AKMM.SovereignDefault.IsMPE.eq_24_9
#print axioms AKMM.SovereignDefault.IsMPE.eq_24_10
#print axioms AKMM.SovereignDefault.IsMPE.eq_24_11
#print axioms AKMM.SovereignDefault.IsMPE.eq_24_12
#print axioms AKMM.SovereignDefault.IsMPE.default_opt
#print axioms AKMM.SovereignDefault.IsMPE.borrow_opt
#print axioms AKMM.SovereignDefault.mpe_example
#print axioms AKMM.SovereignDefault.SDModel.bellmanSol
#print axioms AKMM.SovereignDefault.SDModel.inducedDefault
#print axioms AKMM.SovereignDefault.SDModel.inducedBorrow
#print axioms AKMM.SovereignDefault.SDModel.mpeMap
#print axioms AKMM.SovereignDefault.SDModel.inducedBorrow_spec
#print axioms AKMM.SovereignDefault.mpe_iff_fixedPt
#print axioms AKMM.SovereignDefault.mpe_values_eq
#print axioms AKMM.SovereignDefault.mpe_price_mem
#print axioms AKMM.SovereignDefault.mpe_V_antitone
#print axioms AKMM.SovereignDefault.mpe_default_mono
#print axioms AKMM.SovereignDefault.eq_24_13
#print axioms AKMM.SovereignDefault.eq_24_13_printed_false
#print axioms AKMM.SovereignDefault.eq_24_13_printed_counterexample
#print axioms AKMM.SovereignDefault.eq_24_13_sign
#print axioms AKMM.SovereignDefault.eq_24_A_3
#print axioms AKMM.SovereignDefault.ev_gumbelCDF
#print axioms AKMM.SovereignDefault.ev_gumbelPDF
#print axioms AKMM.SovereignDefault.ev_choiceProb
#print axioms AKMM.SovereignDefault.ev_hasDerivAt
#print axioms AKMM.SovereignDefault.ev_density_continuous
#print axioms AKMM.SovereignDefault.ev_integrable
#print axioms AKMM.SovereignDefault.ev_integral
#print axioms AKMM.SovereignDefault.ev_logit
#print axioms AKMM.SovereignDefault.ev_logit_pos
#print axioms AKMM.SovereignDefault.ev_logit_sum
#print axioms AKMM.SovereignDefault.ev_logit_continuous
#print axioms AKMM.SovereignDefault.ev_conditional_borrow
#print axioms AKMM.SovereignDefault.eq_24_A_6_logit
#print axioms AKMM.SovereignDefault.ev_gumbel
#print axioms AKMM.SovereignDefault.gp_pdf_continuous
#print axioms AKMM.SovereignDefault.gp_pdf_integrable
#print axioms AKMM.SovereignDefault.gp_pdf_nonneg
#print axioms AKMM.SovereignDefault.gp_hasDerivAt
#print axioms AKMM.SovereignDefault.gp_integral_Iic
#print axioms AKMM.SovereignDefault.gp_measure_Iic
#print axioms AKMM.SovereignDefault.gp_isProbabilityMeasure
#print axioms AKMM.SovereignDefault.ev_logit_of_gumbel
#print axioms AKMM.SovereignDefault.ev_choiceProb_eq_gumbel
#print axioms AKMM.SovereignDefault.cal_crra
#print axioms AKMM.SovereignDefault.cal_crra_hasDerivAt
#print axioms AKMM.SovereignDefault.cal_crra_deriv_pos
#print axioms AKMM.SovereignDefault.cal_crra_deriv_antitone
#print axioms AKMM.SovereignDefault.cal_phi
#print axioms AKMM.SovereignDefault.cal_phi_nonneg
#print axioms AKMM.SovereignDefault.cal_phi_div
#print axioms AKMM.SovereignDefault.cal_phi_div_monotone
#print axioms AKMM.SovereignDefault.cal_phi_at_mean
#print axioms AKMM.SovereignDefault.cal_phi_mono_lam0
#print axioms AKMM.SovereignDefault.cal_phi_lam1
#print axioms AKMM.SovereignDefault.cal_ar1_variance
#print axioms AKMM.SovereignDefault.cal_lognormal_mean
#print axioms AKMM.SovereignDefault.cal_mean_one_iff
#print axioms AKMM.SovereignDefault.cal_table_mu_printed_false
#print axioms AKMM.SovereignDefault.fn_44
#print axioms AKMM.SovereignDefault.fn_44_exists
#print axioms AKMM.SovereignDefault.UEModel
#print axioms AKMM.SovereignDefault.UEModel.mk
#print axioms AKMM.SovereignDefault.UEModel.inc
#print axioms AKMM.SovereignDefault.UEModel.P
#print axioms AKMM.SovereignDefault.UEModel.markov
#print axioms AKMM.SovereignDefault.UEModel.u
#print axioms AKMM.SovereignDefault.UEModel.φ
#print axioms AKMM.SovereignDefault.UEModel.β
#print axioms AKMM.SovereignDefault.UEModel.β_nonneg
#print axioms AKMM.SovereignDefault.UEModel.β_lt_one
#print axioms AKMM.SovereignDefault.UEModel.r
#print axioms AKMM.SovereignDefault.UEModel.r_pos
#print axioms AKMM.SovereignDefault.UEModel.bmax
#print axioms AKMM.SovereignDefault.UEModel.bmax_nonneg
#print axioms AKMM.SovereignDefault.ue_fixed_point
#print axioms AKMM.SovereignDefault.ue_sum_le
#print axioms AKMM.SovereignDefault.ue_le_sum
#print axioms AKMM.SovereignDefault.ue_sum_mono
#print axioms AKMM.SovereignDefault.ue_sum_add
#print axioms AKMM.SovereignDefault.UEModel.price
#print axioms AKMM.SovereignDefault.UEModel.obj
#print axioms AKMM.SovereignDefault.UEModel.defaultRHS
#print axioms AKMM.SovereignDefault.IsOneMPE
#print axioms AKMM.SovereignDefault.IsOneMPE.mk
#print axioms AKMM.SovereignDefault.IsOneMPE.bdd
#print axioms AKMM.SovereignDefault.IsOneMPE.eq_24_9
#print axioms AKMM.SovereignDefault.IsOneMPE.eq_24_10
#print axioms AKMM.SovereignDefault.IsOneMPE.eq_24_11
#print axioms AKMM.SovereignDefault.IsOneMPE.eq_24_12
#print axioms AKMM.SovereignDefault.IsOneMPE.default_opt
#print axioms AKMM.SovereignDefault.IsOneMPE.borrow_le
#print axioms AKMM.SovereignDefault.IsOneMPE.borrow_opt
#print axioms AKMM.SovereignDefault.ue_thr
#print axioms AKMM.SovereignDefault.UEModel.ue_price_mem
#print axioms AKMM.SovereignDefault.UEModel.ue_price_one
#print axioms AKMM.SovereignDefault.UEModel.ue_price_mono
#print axioms AKMM.SovereignDefault.UEModel.ue_revenue
#print axioms AKMM.SovereignDefault.UEModel.ue_replication
#print axioms AKMM.SovereignDefault.UEModel.ue_modulus
#print axioms AKMM.SovereignDefault.UEModel.ue_VR_antitone
#print axioms AKMM.SovereignDefault.UEModel.ue_repay_nonpos
#print axioms AKMM.SovereignDefault.UEModel.ue_VD_unique
#print axioms AKMM.SovereignDefault.UEModel.ue_mpe_sup
#print axioms AKMM.SovereignDefault.UEModel.ue_mpe_VR_le
#print axioms AKMM.SovereignDefault.UEModel.ue_mpe_unique
#print axioms AKMM.SovereignDefault.UEModel.ue_u_le
#print axioms AKMM.SovereignDefault.UEModel.ue_obj_le
#print axioms AKMM.SovereignDefault.UEModel.VRsup
#print axioms AKMM.SovereignDefault.UEModel.bell
#print axioms AKMM.SovereignDefault.UEModel.cutoff
#print axioms AKMM.SovereignDefault.UEModel.ue_VRsup_bdd
#print axioms AKMM.SovereignDefault.UEModel.ue_VRsup_le
#print axioms AKMM.SovereignDefault.UEModel.ue_VRsup_sup
#print axioms AKMM.SovereignDefault.UEModel.ue_VRsup_ub
#print axioms AKMM.SovereignDefault.UEModel.ue_VD_exists
#print axioms AKMM.SovereignDefault.UEModel.ue_sol_exists
#print axioms AKMM.SovereignDefault.UEModel.ue_thr_mem
#print axioms AKMM.SovereignDefault.UEModel.ue_thr_nonpos
#print axioms AKMM.SovereignDefault.UEModel.ue_cutoff_le
#print axioms AKMM.SovereignDefault.UEModel.ue_capacity_fixed
#print axioms AKMM.SovereignDefault.UEModel.ue_attain
#print axioms AKMM.SovereignDefault.UEModel.ue_mpe_exists
#print axioms AKMM.SovereignDefault.UEModel.ue_mpe_exists_unique
#print axioms AKMM.SovereignDefault.ue_example
#print axioms AKMM.SovereignDefault.ue_example_hyp
#print axioms AKMM.SovereignDefault.ue_example_exists_unique
#print axioms AKMM.SovereignDefault.mu_econ
#print axioms AKMM.SovereignDefault.mu_sup_bool
#print axioms AKMM.SovereignDefault.mu_grid_one_period_two_mpe
#print axioms AKMM.SovereignDefault.mu_grid_long_term_two_mpe
#print axioms AKMM.SovereignDefault.fh_scalar
#print axioms AKMM.SovereignDefault.fh_moving_contraction
#print axioms AKMM.SovereignDefault.fh_ite_zero
#print axioms AKMM.SovereignDefault.fh_ite_mem
#print axioms AKMM.SovereignDefault.fh_rev_le
#print axioms AKMM.SovereignDefault.IsFHEqm
#print axioms AKMM.SovereignDefault.IsFHEqm.mk
#print axioms AKMM.SovereignDefault.IsFHEqm.eq_24_9
#print axioms AKMM.SovereignDefault.IsFHEqm.default_opt
#print axioms AKMM.SovereignDefault.IsFHEqm.term_VD
#print axioms AKMM.SovereignDefault.IsFHEqm.term_VR
#print axioms AKMM.SovereignDefault.IsFHEqm.term_q
#print axioms AKMM.SovereignDefault.IsFHEqm.term_B
#print axioms AKMM.SovereignDefault.IsFHEqm.eq_24_10
#print axioms AKMM.SovereignDefault.IsFHEqm.eq_24_11
#print axioms AKMM.SovereignDefault.IsFHEqm.eq_24_12
#print axioms AKMM.SovereignDefault.IsFHEqm.borrow_le
#print axioms AKMM.SovereignDefault.IsFHEqm.borrow_opt
#print axioms AKMM.SovereignDefault.UEModel.fh_obj_congr
#print axioms AKMM.SovereignDefault.UEModel.fh_unique
#print axioms AKMM.SovereignDefault.UEModel.fh_q_mem
#print axioms AKMM.SovereignDefault.UEModel.fh_mpe_q_mem
#print axioms AKMM.SovereignDefault.UEModel.fh_repay_nonpos
#print axioms AKMM.SovereignDefault.UEModel.fh_VR_antitone
#print axioms AKMM.SovereignDefault.UEModel.fh_VR_mod
#print axioms AKMM.SovereignDefault.UEModel.fh_VR_slope
#print axioms AKMM.SovereignDefault.UEModel.fh_compare
#print axioms AKMM.SovereignDefault.UEModel.fh_upper
#print axioms AKMM.SovereignDefault.UEModel.fhShift
#print axioms AKMM.SovereignDefault.UEModel.fh_shift_nonneg
#print axioms AKMM.SovereignDefault.UEModel.fh_shift_tendsto
#print axioms AKMM.SovereignDefault.UEModel.fh_base
#print axioms AKMM.SovereignDefault.UEModel.fh_dom
#print axioms AKMM.SovereignDefault.UEModel.fh_lower
#print axioms AKMM.SovereignDefault.UEModel.fh_VD_bound
#print axioms AKMM.SovereignDefault.UEModel.fh_default_sets
#print axioms AKMM.SovereignDefault.UEModel.fhCap
#print axioms AKMM.SovereignDefault.UEModel.fh_capacity_tendsto
#print axioms AKMM.SovereignDefault.UEModel.fh_values_tendsto
#print axioms AKMM.SovereignDefault.UEModel.fh_price_tendsto
#print axioms AKMM.SovereignDefault.UEModel.fh_attain
#print axioms AKMM.SovereignDefault.UEModel.fhVD
#print axioms AKMM.SovereignDefault.UEModel.fhVR
#print axioms AKMM.SovereignDefault.UEModel.fhV
#print axioms AKMM.SovereignDefault.UEModel.fhD
#print axioms AKMM.SovereignDefault.UEModel.fhq
#print axioms AKMM.SovereignDefault.UEModel.fhU
#print axioms AKMM.SovereignDefault.UEModel.fh_stage
#print axioms AKMM.SovereignDefault.UEModel.fh_thr
#print axioms AKMM.SovereignDefault.UEModel.fh_exists
#print axioms AKMM.SovereignDefault.fh_example_hyp
#print axioms AKMM.SovereignDefault.fh_example_limit
#print axioms AKMM.SovereignDefault.UEModel.ldObj
#print axioms AKMM.SovereignDefault.UEModel.ld_obj_one
#print axioms AKMM.SovereignDefault.IsLongMPE
#print axioms AKMM.SovereignDefault.IsLongMPE.mk
#print axioms AKMM.SovereignDefault.IsLongMPE.bdd
#print axioms AKMM.SovereignDefault.IsLongMPE.eq_24_9
#print axioms AKMM.SovereignDefault.IsLongMPE.eq_24_10
#print axioms AKMM.SovereignDefault.IsLongMPE.eq_24_11
#print axioms AKMM.SovereignDefault.IsLongMPE.eq_24_12
#print axioms AKMM.SovereignDefault.IsLongMPE.default_opt
#print axioms AKMM.SovereignDefault.IsLongMPE.borrow_le
#print axioms AKMM.SovereignDefault.IsLongMPE.borrow_opt
#print axioms AKMM.SovereignDefault.ld_one_iff
#print axioms AKMM.SovereignDefault.ld_econ
#print axioms AKMM.SovereignDefault.ld_VR
#print axioms AKMM.SovereignDefault.ld_D
#print axioms AKMM.SovereignDefault.ld_qG
#print axioms AKMM.SovereignDefault.ld_qB
#print axioms AKMM.SovereignDefault.ld_BG
#print axioms AKMM.SovereignDefault.ld_BB
#print axioms AKMM.SovereignDefault.ld_VR_lt_iff
#print axioms AKMM.SovereignDefault.ld_obj_eq
#print axioms AKMM.SovereignDefault.ld_VD_eq
#print axioms AKMM.SovereignDefault.ld_two_mpe
#print axioms AKMM.SovereignDefault.ld_dilution_lowers_prices
#print axioms AKMM.SovereignDefault.ld_econ_hyp
#print axioms AKMM.SovereignDefault.ld_one_period_unique
#print axioms AKMM.SovereignDefault.IsBoundedLongMPE
#print axioms AKMM.SovereignDefault.IsBoundedLongMPE.mk
#print axioms AKMM.SovereignDefault.IsBoundedLongMPE.bdd
#print axioms AKMM.SovereignDefault.IsBoundedLongMPE.eq_24_9
#print axioms AKMM.SovereignDefault.IsBoundedLongMPE.eq_24_10
#print axioms AKMM.SovereignDefault.IsBoundedLongMPE.eq_24_11
#print axioms AKMM.SovereignDefault.IsBoundedLongMPE.eq_24_12
#print axioms AKMM.SovereignDefault.IsBoundedLongMPE.default_opt
#print axioms AKMM.SovereignDefault.IsBoundedLongMPE.borrow_mem
#print axioms AKMM.SovereignDefault.IsBoundedLongMPE.borrow_opt
#print axioms AKMM.SovereignDefault.sfd_econ
#print axioms AKMM.SovereignDefault.sfd_bmax
#print axioms AKMM.SovereignDefault.sfd_obj_true
#print axioms AKMM.SovereignDefault.sfd_obj_false
#print axioms AKMM.SovereignDefault.sfd_price_true
#print axioms AKMM.SovereignDefault.sfd_price_false
#print axioms AKMM.SovereignDefault.sfd_defaultRHS
#print axioms AKMM.SovereignDefault.sfd_VD
#print axioms AKMM.SovereignDefault.sfd_VD_iff
#print axioms AKMM.SovereignDefault.sfd_D
#print axioms AKMM.SovereignDefault.sfd_VRL
#print axioms AKMM.SovereignDefault.sfd_qL
#print axioms AKMM.SovereignDefault.sfd_VL_eq
#print axioms AKMM.SovereignDefault.sfd_crisis_block
#print axioms AKMM.SovereignDefault.sfd_crisis_price
#print axioms AKMM.SovereignDefault.sfd_crisis_default
#print axioms AKMM.SovereignDefault.sfd_VRN
#print axioms AKMM.SovereignDefault.sfd_qN
#print axioms AKMM.SovereignDefault.sfd_BhN
#print axioms AKMM.SovereignDefault.sfd_VRS
#print axioms AKMM.SovereignDefault.sfd_qS
#print axioms AKMM.SovereignDefault.sfd_BhS
#print axioms AKMM.SovereignDefault.sfd_VN_true
#print axioms AKMM.SovereignDefault.sfd_VS_true
#print axioms AKMM.SovereignDefault.sfd_no_dilution_mpe
#print axioms AKMM.SovereignDefault.sfd_dilution_mpe
#print axioms AKMM.SovereignDefault.sfd_values_differ
#print axioms AKMM.SovereignDefault.sfd_dilution_lowers_prices
#print axioms AKMM.SovereignDefault.sfd_strict_preference
#print axioms AKMM.SovereignDefault.sfd_two_mpe
#print axioms AKMM.SovereignDefault.sfd_obj_one_true
#print axioms AKMM.SovereignDefault.sfd_obj_one_false
#print axioms AKMM.SovereignDefault.sfd_obj_one_shift
#print axioms AKMM.SovereignDefault.sfd_VR1
#print axioms AKMM.SovereignDefault.sfd_D1
#print axioms AKMM.SovereignDefault.sfd_q1
#print axioms AKMM.SovereignDefault.sfd_Bh1
#print axioms AKMM.SovereignDefault.sfd_one_period_mpe
#print axioms AKMM.SovereignDefault.sfd_one_period_char
#print axioms AKMM.SovereignDefault.sfd_one_period_unique
#print axioms AKMM.SovereignDefault.sfd_strict_multiplicity
