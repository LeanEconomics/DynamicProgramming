/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

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
