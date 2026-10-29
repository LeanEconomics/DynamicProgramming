/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import HarrisRecurrence.StochasticComparison

/-!
# Theorem 9.5.6: increment analysis with `2 + ε` moments (MT §9.5.3)

Meyn and Tweedie, Theorem 9.5.6, p. 227, which the book states without proof. The chain lives
on `ℝ₊`, with increments `W_x = Φ₁ − x` under `P_x`, mean drift `m(x)` (`meanDrift`) and second
moment `v(x)` (`incrementVar`), and `sup_x E_x|W_x|^{2+ε} ≤ B` (`HasMomentBound`).

* **Theorem 9.5.6 (ii)** (`theorem_9_5_6_ii`): if `m(x) ≥ θ v(x)/2x` for large `x` with `θ > 1`,
  the chain is transient. Test function `V(x) = 1 − (1 + x)^{−α}` with
  `α = min((θ − 1)/2, ε/2)`: the expansion of (9.67) on `{|W_x| ≤ η(1 + x)}`
  (`rpow_neg_le_quadratic`), on the tail `{|u| > η}` the bound `(1 + Φ₁)^{−α} ≤ 1` together
  with `1 − αu + (α/η)u² ≥ 0`, and the tail estimates
  `E[W²; |W| > s] ≤ B/s^ε`, `P(|W| > s) ≤ B/s^{2+ε}` (`setIntegral_sq_tail_le`,
  `measure_tail_le`); `α < ε` makes the tail cost `O(x^{α−2−ε}) = o(x^{−2})`.
* **Theorem 9.5.6 (i)** (`theorem_9_5_6_i`): if `m(x) ≤ v(x)/2x + K x^{−1−δ}` for large `x` with
  `δ > 0`, the chain is Harris recurrent. Test function `V(x) = log log(x + e)`, as the book
  suggests: with `s = log(x + e)`, `u = W_x/(x + e)` and `η = 1/(8s)`, on `{|u| ≤ η}` both layers
  of the logarithm are expanded to second order (`log_one_add_le_quadratic`), giving
  `V(x + W) − V(x) ≤ u/s − u²(1/(2(1 + η)²s) + 8/(25(1 + η)²s²))`
  (`loglog_step_le`), and the second-order term `≈ v/(2x² s²)` dominates `m/(xs) − v/(2x²s)`,
  `K x^{−2−δ}/s` and the tail cost `O(s^{1+ε}x^{−2−ε})`.

**Supporting results.** `rpow_neg_step_le` and `integral_rpow_neg_le_of_moment` (the
expansion for (ii)), `transient_of_rpow_drift` (Theorem 8.4.2 with `1 − (1 + x)^{−α}`),
`loglogCoeff` (the coefficient `D(s)`), `loglogCoeff_mul_bounds` (`1/2 + 1/(9s) ≤ D(s)s ≤ 1`),
`integrable_loglog` and `integral_loglog_le` (the expansion for (i)).

**Hypotheses.** The book's standing assumptions for §9.5.3 (a `δ₀`-irreducible T-chain with
`v(x)` bounded from zero) are replaced by what the proofs use: a maximal irreducibility measure
`ψ`; in (i) the sets `[0, c]` are petite, in (ii) every tail `(c, ∞)` is in `B⁺(X)`; and
`v(x) ≥ v₀ > 0` for large `x` (without it the conclusions fail: for `v ≡ 0` the chain is
deterministic). In (i) the constant `K` may have either sign.
-/

namespace MeynTweedie.HarrisRecurrence

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

/-- **The moment bound** of Theorem 9.5.6: `E_x|Φ₁ − x|^{2+ε} ≤ B` for every `x`. -/
def HasMomentBound (P : Kernel ℝ≥0 ℝ≥0) (ε B : ℝ) : Prop :=
  ∀ x : ℝ≥0, Integrable (fun y : ℝ≥0 => |(y : ℝ) - x| ^ (2 + ε)) (P x) ∧
    ∫ y, |(y : ℝ) - x| ^ (2 + ε) ∂P x ≤ B

/-! ### Moments and tails of the increment -/

/-- `|t| ≤ 1 + |t|^{2+ε}` and `t² ≤ 1 + |t|^{2+ε}`. -/
theorem abs_le_one_add_rpow {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    |t| ≤ 1 + |t| ^ (2 + ε) ∧ t ^ 2 ≤ 1 + |t| ^ (2 + ε) := by
  have h0 : 0 ≤ |t| ^ (2 + ε) := Real.rpow_nonneg (abs_nonneg t) _
  rcases le_or_gt |t| 1 with h | h
  · constructor
    · linarith
    · have : t ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg t]
      linarith
  · have h1 : |t| ^ (1 : ℝ) ≤ |t| ^ (2 + ε) :=
      Real.rpow_le_rpow_of_exponent_le h.le (by linarith)
    have h2 : |t| ^ (2 : ℝ) ≤ |t| ^ (2 + ε) :=
      Real.rpow_le_rpow_of_exponent_le h.le (by linarith)
    rw [Real.rpow_one] at h1
    rw [Real.rpow_two, sq_abs] at h2
    constructor <;> linarith

/-- The increment is integrable. -/
theorem integrable_incr {P : Kernel ℝ≥0 ℝ≥0} [IsMarkovKernel P] {ε B : ℝ} (hε : 0 < ε)
    (hM : HasMomentBound P ε B) (x : ℝ≥0) :
    Integrable (fun y : ℝ≥0 => (y : ℝ) - x) (P x) :=
  ((integrable_const 1).add (hM x).1).mono'
    (measurable_coe_nnreal_real.sub measurable_const).aestronglyMeasurable
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact (abs_le_one_add_rpow hε _).1)

/-- The squared increment is integrable. -/
theorem integrable_incr_sq {P : Kernel ℝ≥0 ℝ≥0} [IsMarkovKernel P] {ε B : ℝ} (hε : 0 < ε)
    (hM : HasMomentBound P ε B) (x : ℝ≥0) :
    Integrable (fun y : ℝ≥0 => ((y : ℝ) - x) ^ 2) (P x) :=
  ((integrable_const 1).add (hM x).1).mono'
    ((measurable_coe_nnreal_real.sub measurable_const).pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact (abs_le_one_add_rpow hε _).2)

/-- The tail set `{|Φ₁ − x| > s}`. -/
def incrTail (x : ℝ≥0) (s : ℝ) : Set ℝ≥0 := {y | s < |(y : ℝ) - x|}

/-- The tail set is measurable. -/
theorem measurableSet_incrTail (x : ℝ≥0) (s : ℝ) : MeasurableSet (incrTail x s) :=
  measurableSet_lt measurable_const
    (continuous_abs.measurable.comp (measurable_coe_nnreal_real.sub measurable_const))

/-- `E_x[W²; |W| > s] ≤ B/s^ε`. -/
theorem setIntegral_sq_tail_le {P : Kernel ℝ≥0 ℝ≥0} [IsMarkovKernel P] {ε B : ℝ} (hε : 0 < ε)
    (hM : HasMomentBound P ε B) (x : ℝ≥0) {s : ℝ} (hs : 0 < s) :
    ∫ y in incrTail x s, ((y : ℝ) - x) ^ 2 ∂P x ≤ B / s ^ ε := by
  have hT := measurableSet_incrTail x s
  calc ∫ y in incrTail x s, ((y : ℝ) - x) ^ 2 ∂P x
      ≤ ∫ y in incrTail x s, |(y : ℝ) - x| ^ (2 + ε) / s ^ ε ∂P x := by
        refine setIntegral_mono_on (integrable_incr_sq hε hM x).integrableOn
          ((hM x).1.div_const _).integrableOn hT fun y hy => ?_
        simp only [incrTail, mem_ofPred_eq] at hy
        have hpos : 0 < |(y : ℝ) - x| := hs.trans hy
        rw [le_div_iff₀ (Real.rpow_pos_of_pos hs _), Real.rpow_add hpos, Real.rpow_two,
          sq_abs]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs.le hy.le hε.le) (sq_nonneg _)
    _ ≤ ∫ y, |(y : ℝ) - x| ^ (2 + ε) / s ^ ε ∂P x :=
        setIntegral_le_integral ((hM x).1.div_const _)
          (Eventually.of_forall fun y => div_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
            (Real.rpow_nonneg hs.le _))
    _ ≤ B / s ^ ε := by
        rw [integral_div]
        exact div_le_div_of_nonneg_right (hM x).2 (Real.rpow_nonneg hs.le _)

/-- `P_x(|W| > s) ≤ B/s^{2+ε}`. -/
theorem measure_tail_le {P : Kernel ℝ≥0 ℝ≥0} [IsMarkovKernel P] {ε B : ℝ} (hε : 0 < ε)
    (hM : HasMomentBound P ε B) (x : ℝ≥0) {s : ℝ} (hs : 0 < s) :
    (P x (incrTail x s)).toReal ≤ B / s ^ (2 + ε) := by
  have hT := measurableSet_incrTail x s
  have hs2 : 0 < s ^ (2 + ε) := Real.rpow_pos_of_pos hs _
  calc (P x (incrTail x s)).toReal = ∫ y in incrTail x s, (1 : ℝ) ∂P x := by
        rw [setIntegral_const, smul_eq_mul, mul_one]; rfl
    _ ≤ ∫ y in incrTail x s, |(y : ℝ) - x| ^ (2 + ε) / s ^ (2 + ε) ∂P x := by
        refine setIntegral_mono_on (integrableOn_const) ((hM x).1.div_const _).integrableOn hT
          fun y hy => ?_
        simp only [incrTail, mem_ofPred_eq] at hy
        rw [le_div_iff₀ hs2, one_mul]
        exact Real.rpow_le_rpow hs.le hy.le (by linarith)
    _ ≤ ∫ y, |(y : ℝ) - x| ^ (2 + ε) / s ^ (2 + ε) ∂P x :=
        setIntegral_le_integral ((hM x).1.div_const _)
          (Eventually.of_forall fun y => div_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
            hs2.le)
    _ ≤ B / s ^ (2 + ε) := by
        rw [integral_div]
        exact div_le_div_of_nonneg_right (hM x).2 hs2.le

/-! ### Theorem 9.5.6 (ii): transience -/

/-- **The pointwise bound behind (9.67)** with unbounded increments: for `a > 0`, `a + w ≥ 1` and
`u = w/a`, `(a + w)^{−α} ≤ a^{−α}(1 − αu + Ku²/2)` plus, on `{|w| > ηa}`, the correction
`a^{−α}(α/η)u² + 1`, where `K = α(α + 1)(1 − η)^{−α−2}`. -/
theorem rpow_neg_step_le {α η a w : ℝ} (hα : 0 < α) (hη : 0 < η) (hη1 : η < 1) (ha : 0 < a)
    (haw : 1 ≤ a + w) :
    (a + w) ^ (-α) ≤ (a ^ α)⁻¹ - (a ^ α)⁻¹ * α / a * w +
      (a ^ α)⁻¹ * (α * (α + 1) * (1 - η) ^ (-α - 2)) / (2 * a ^ 2) * w ^ 2 +
      (if η * a < |w| then (a ^ α)⁻¹ * (α / η) / a ^ 2 * w ^ 2 + 1 else 0) := by
  set K := α * (α + 1) * (1 - η) ^ (-α - 2)
  have hK : 0 ≤ K := by
    have : 0 ≤ (1 - η) ^ (-α - 2) := Real.rpow_nonneg (by linarith) _
    positivity
  have hr : 0 < a ^ α := Real.rpow_pos_of_pos ha _
  set u := w / a
  have hw : w = a * u := by simp only [u]; field_simp
  have hu1 : 0 ≤ 1 + u := by
    have : 1 + u = (a + w) / a := by simp only [u]; field_simp
    rw [this]; exact div_nonneg (by linarith) ha.le
  have hsplit : (a + w) ^ (-α) = (a ^ α)⁻¹ * (1 + u) ^ (-α) := by
    rw [show a + w = a * (1 + u) by linear_combination hw, Real.mul_rpow ha.le hu1,
      Real.rpow_neg ha.le]
  have hq : (a ^ α)⁻¹ - (a ^ α)⁻¹ * α / a * w + (a ^ α)⁻¹ * K / (2 * a ^ 2) * w ^ 2 =
      (a ^ α)⁻¹ * (1 - α * u + K / 2 * u ^ 2) := by
    rw [hw]; field_simp
  have hc : (a ^ α)⁻¹ * (α / η) / a ^ 2 * w ^ 2 = (a ^ α)⁻¹ * (α / η * u ^ 2) := by
    rw [hw]; field_simp
  rw [hq, hc]
  split_ifs with h
  · -- the tail: `(a + w)^{−α} ≤ 1` and the bracket is nonnegative
    have hle : (a + w) ^ (-α) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos haw (by linarith)
    have hu : η < |u| := by
      rw [abs_div, abs_of_pos ha, lt_div_iff₀ ha]; exact h
    have hbr : 0 ≤ 1 - α * u + K / 2 * u ^ 2 + α / η * u ^ 2 := by
      rcases le_or_gt u 0 with hu0 | hu0
      · have : 0 ≤ -(α * u) := by nlinarith
        have : 0 ≤ α / η * u ^ 2 := by positivity
        have : 0 ≤ K / 2 * u ^ 2 := by positivity
        linarith
      · rw [abs_of_pos hu0] at hu
        have : α * u ≤ α / η * u ^ 2 := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hη]
          nlinarith [mul_nonneg (mul_pos hα hu0).le (sub_nonneg.2 hu.le)]
        have : 0 ≤ K / 2 * u ^ 2 := by positivity
        linarith
    have : 0 ≤ (a ^ α)⁻¹ * (1 - α * u + K / 2 * u ^ 2 + α / η * u ^ 2) :=
      mul_nonneg (inv_nonneg.2 hr.le) hbr
    nlinarith
  · -- the body: the quadratic expansion
    push Not at h
    have hu : u ∈ Icc (-η) η := by
      rw [mem_Icc, ← abs_le, abs_div, abs_of_pos ha, div_le_iff₀ ha]; exact h
    rw [hsplit, add_zero]
    exact mul_le_mul_of_nonneg_left (rpow_neg_le_quadratic hα hη.le hη1 hu)
      (inv_nonneg.2 hr.le)

/-- **The drift of `(1 + x)^{−α}`** under the moment bound: with `a = 1 + x` and the constant
`K = α(α + 1)(1 − η)^{−α−2}`,
`E_x(1 + Φ₁)^{−α} ≤ a^{−α}(1 − αm/a + Kv/(2a²)) + a^{−α}(α/η)B/((ηa)^ε a²) + B/(ηa)^{2+ε}`. -/
theorem integral_rpow_neg_le_of_moment {P : Kernel ℝ≥0 ℝ≥0} [IsMarkovKernel P] {ε B : ℝ}
    (hε : 0 < ε) (hM : HasMomentBound P ε B) {α η : ℝ} (hα : 0 < α) (hη : 0 < η)
    (hη1 : η < 1) (x : ℝ≥0) :
    ∫ y, (1 + (y : ℝ)) ^ (-α) ∂P x ≤
      ((1 + (x : ℝ)) ^ α)⁻¹ - ((1 + (x : ℝ)) ^ α)⁻¹ * α / (1 + x) * meanDrift P x +
      ((1 + (x : ℝ)) ^ α)⁻¹ * (α * (α + 1) * (1 - η) ^ (-α - 2)) / (2 * (1 + (x : ℝ)) ^ 2) *
        incrementVar P x +
      (((1 + (x : ℝ)) ^ α)⁻¹ * (α / η) / (1 + (x : ℝ)) ^ 2 * (B / (η * (1 + x)) ^ ε) +
        B / (η * (1 + x)) ^ (2 + ε)) := by
  set a : ℝ := 1 + x
  have ha : 0 < a := by simp only [a]; linarith [NNReal.coe_nonneg x]
  set c0 := (a ^ α)⁻¹
  set c1 := (a ^ α)⁻¹ * α / a
  set c2 := (a ^ α)⁻¹ * (α * (α + 1) * (1 - η) ^ (-α - 2)) / (2 * a ^ 2)
  set c3 := (a ^ α)⁻¹ * (α / η) / a ^ 2
  have hc3 : 0 ≤ c3 := by
    have : 0 < a ^ α := Real.rpow_pos_of_pos ha _
    positivity
  set T := incrTail x (η * a)
  have hT : MeasurableSet T := measurableSet_incrTail x _
  have hs : 0 < η * a := mul_pos hη ha
  have i1 := integrable_incr hε hM x
  have i2 := integrable_incr_sq hε hM x
  have i3 : Integrable (fun y : ℝ≥0 => c3 * ((y : ℝ) - x) ^ 2 + 1) (P x) :=
    (i2.const_mul c3).add (integrable_const 1)
  have j1 : Integrable (fun y : ℝ≥0 => c1 * ((y : ℝ) - x)) (P x) := i1.const_mul c1
  have j2 : Integrable (fun y : ℝ≥0 => c2 * ((y : ℝ) - x) ^ 2) (P x) := i2.const_mul c2
  have j3 : Integrable (fun y : ℝ≥0 => T.indicator (fun y : ℝ≥0 => c3 * ((y : ℝ) - x) ^ 2 + 1) y)
      (P x) := i3.indicator hT
  have j01 : Integrable (fun y : ℝ≥0 => c0 - c1 * ((y : ℝ) - x)) (P x) :=
    (integrable_const c0).sub j1
  have j012 : Integrable (fun y : ℝ≥0 => c0 - c1 * ((y : ℝ) - x) + c2 * ((y : ℝ) - x) ^ 2)
      (P x) := j01.add j2
  have hgm : Measurable fun y : ℝ≥0 => (1 + (y : ℝ)) ^ (-α) :=
    (measurable_const.add measurable_coe_nnreal_real).pow_const _
  have hint : Integrable (fun y : ℝ≥0 => (1 + (y : ℝ)) ^ (-α)) (P x) :=
    Integrable.of_bound hgm.aestronglyMeasurable 1 (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith [NNReal.coe_nonneg y]) _)]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [NNReal.coe_nonneg y])
        (by linarith))
  have hpt : ∀ y : ℝ≥0, (1 + (y : ℝ)) ^ (-α) ≤ c0 - c1 * ((y : ℝ) - x) +
      c2 * ((y : ℝ) - x) ^ 2 + T.indicator (fun y : ℝ≥0 => c3 * ((y : ℝ) - x) ^ 2 + 1) y := by
    intro y
    have e : (1 : ℝ) + y = a + ((y : ℝ) - x) := by simp only [a]; ring
    have h := rpow_neg_step_le (w := (y : ℝ) - x) hα hη hη1 ha
      (by rw [← e]; linarith [NNReal.coe_nonneg y])
    rw [← e] at h
    by_cases hy : y ∈ T
    · rw [indicator_of_mem hy]
      have : η * a < |(y : ℝ) - x| := hy
      simp only [this, ↓reduceIte] at h
      simp only [c0, c1, c2, c3]
      linarith
    · rw [indicator_of_notMem hy]
      have : ¬ η * a < |(y : ℝ) - x| := hy
      simp only [this, ↓reduceIte, add_zero] at h
      simp only [c0, c1, c2]
      linarith
  have hS := setIntegral_sq_tail_le hε hM x hs
  have hp := measure_tail_le hε hM x hs
  calc ∫ y, (1 + (y : ℝ)) ^ (-α) ∂P x
      ≤ ∫ y, (c0 - c1 * ((y : ℝ) - x) + c2 * ((y : ℝ) - x) ^ 2 +
          T.indicator (fun y : ℝ≥0 => c3 * ((y : ℝ) - x) ^ 2 + 1) y) ∂P x :=
        integral_mono hint (j012.add j3) hpt
    _ = c0 - c1 * meanDrift P x + c2 * incrementVar P x +
          (c3 * ∫ y in T, ((y : ℝ) - x) ^ 2 ∂P x + (P x T).toReal) := by
        rw [integral_add j012 j3, integral_add j01 j2, integral_sub (integrable_const _) j1,
          integral_const, integral_const_mul, integral_const_mul, integral_indicator hT,
          integral_add (i2.const_mul c3).integrableOn integrableOn_const, integral_const_mul,
          setIntegral_const, meanDrift, incrementVar]
        simp [Measure.real]
    _ ≤ c0 - c1 * meanDrift P x + c2 * incrementVar P x +
          (c3 * (B / (η * a) ^ ε) + B / (η * a) ^ (2 + ε)) := by
        gcongr


/-- **Transience from a power drift.** If the tails `(c, ∞)` are in `B⁺(X)` and
`E_x(1 + Φ₁)^{−α} ≤ (1 + x)^{−α}` for `x > x₁`, then the chain is transient (Theorem 8.4.2 with
`V(x) = 1 − (1 + x)^{−α}`). -/
theorem transient_of_rpow_drift {P : Kernel ℝ≥0 ℝ≥0} [IsMarkovKernel P] {ψ : Measure ℝ≥0}
    (hψ : IsMaximalIrreducibility P ψ) (hψpos : ∀ c : ℝ≥0, 0 < ψ (Ioi c)) {α : ℝ}
    (hα : 0 < α) {x₁ : ℝ}
    (hdrift : ∀ x : ℝ≥0, x₁ < x →
      ∫ y, (1 + (y : ℝ)) ^ (-α) ∂P x ≤ (1 + (x : ℝ)) ^ (-α)) :
    IsTransientChain P ψ := by
  set V : ℝ≥0 → ℝ := fun y => 1 - (1 + (y : ℝ)) ^ (-α)
  have hgm : Measurable fun y : ℝ≥0 => (1 + (y : ℝ)) ^ (-α) :=
    (measurable_const.add measurable_coe_nnreal_real).pow_const _
  have hVm : Measurable V := measurable_const.sub hgm
  have hle1 : ∀ y : ℝ≥0, (1 + (y : ℝ)) ^ (-α) ≤ 1 := fun y =>
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [NNReal.coe_nonneg y]) (by linarith)
  have hge0 : ∀ y : ℝ≥0, 0 ≤ (1 + (y : ℝ)) ^ (-α) := fun y =>
    Real.rpow_nonneg (by linarith [NNReal.coe_nonneg y]) _
  have hV0 : ∀ y, 0 ≤ V y := fun y => by simp only [V]; linarith [hle1 y]
  have hVle : ∀ y, V y ≤ 1 := fun y => by simp only [V]; linarith [hge0 y]
  have hVmono : ∀ y z : ℝ≥0, V y ≤ V z ↔ y ≤ z := by
    intro y z
    constructor
    · intro h
      by_contra hyz
      push Not at hyz
      have hlt : (1 + (z : ℝ)) ^ (-α) > (1 + (y : ℝ)) ^ (-α) :=
        Real.rpow_lt_rpow_of_neg (by linarith [NNReal.coe_nonneg z])
          (by have := NNReal.coe_lt_coe.2 hyz; linarith) (by linarith)
      simp only [V] at h
      linarith
    · intro h
      simp only [V]
      have : (1 + (z : ℝ)) ^ (-α) ≤ (1 + (y : ℝ)) ^ (-α) :=
        Real.rpow_le_rpow_of_nonpos (by linarith [NNReal.coe_nonneg y])
          (by have := NNReal.coe_le_coe.2 h; linarith) (by linarith)
      linarith
  have hU : (⋃ n : ℕ, Iic (Real.toNNReal x₁ + n)) = univ := by
    refine eq_univ_of_forall fun y => mem_iUnion.2 ?_
    obtain ⟨n, hn⟩ := exists_nat_ge y
    exact ⟨n, le_add_left hn⟩
  have hpos : 0 < ψ (⋃ n : ℕ, Iic (Real.toNNReal x₁ + n)) := by
    rw [hU]; exact pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨n, hn⟩ := exists_measure_pos_of_iUnion hpos
  set x₂ := Real.toNNReal x₁ + n
  have hset : {y : ℝ≥0 | V y ≤ V x₂} = Iic x₂ := by ext y; simp [hVmono]
  refine (theorem_8_4_2 P hψ).2 ⟨V, V x₂, hVm, hV0, ⟨1, hVle⟩, hV0 _, ?_, ?_, fun x hx => ?_⟩
  · rw [hset]; exact hn
  · rw [hset, compl_Iic]; exact hψpos x₂
  · rw [hset, mem_compl_iff, mem_Iic, not_le] at hx
    have hx' : x₁ < x := by
      have h1 : (x₁ : ℝ) ≤ (Real.toNNReal x₁ : ℝ) := Real.le_coe_toNNReal x₁
      have h2 : ((Real.toNNReal x₁ : ℝ≥0) : ℝ) ≤ (x₂ : ℝ) := by
        simp only [x₂, NNReal.coe_add, NNReal.coe_natCast]; linarith [Nat.cast_nonneg (α := ℝ) n]
      have h3 : (x₂ : ℝ) < x := by exact_mod_cast hx
      linarith
    have hint : Integrable (fun y : ℝ≥0 => (1 + (y : ℝ)) ^ (-α)) (P x) :=
      Integrable.of_bound hgm.aestronglyMeasurable 1 (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hge0 y)]; exact hle1 y)
    simp only [driftR, V]
    rw [integral_sub (integrable_const _) hint, integral_const]
    simp only [measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul, Measure.real]
    linarith [hdrift x hx']

/-- **Theorem 9.5.6 (ii)** (MT p. 227, proof omitted in the book): a `ψ`-irreducible chain on
`ℝ₊` whose tails `(c, ∞)` are all in `B⁺(X)`, with `sup_x E_x|W_x|^{2+ε} ≤ B` (`ε > 0`),
`v(x) ≥ v₀ > 0` and `m(x) ≥ θ v(x)/2x` for `x > x₀` and some `θ > 1`, is transient. The test
function is `V(x) = 1 − (1 + x)^{−α}` with `α = min((θ − 1)/2, ε/2)`. -/
theorem theorem_9_5_6_ii {P : Kernel ℝ≥0 ℝ≥0} [IsMarkovKernel P] {ψ : Measure ℝ≥0}
    (hψ : IsMaximalIrreducibility P ψ) (hψpos : ∀ c : ℝ≥0, 0 < ψ (Ioi c)) {ε B : ℝ}
    (hε : 0 < ε) (hM : HasMomentBound P ε B) {v₀ : ℝ} (hv₀ : 0 < v₀) {θ : ℝ} (hθ : 1 < θ)
    {x₀ : ℝ≥0} (hv : ∀ x, x₀ < x → v₀ ≤ incrementVar P x)
    (hm : ∀ x, x₀ < x → θ * incrementVar P x / (2 * x) ≤ meanDrift P x) :
    IsTransientChain P ψ := by
  have hB : 0 ≤ B :=
    (integral_nonneg fun y => Real.rpow_nonneg (abs_nonneg _) _).trans (hM 0).2
  set α := min ((θ - 1) / 2) (ε / 2)
  have hα : 0 < α := lt_min (by linarith) (by linarith)
  have hαθ : α ≤ (θ - 1) / 2 := min_le_left _ _
  have hαε : α < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  -- an `η ∈ (0, 1/2]` with `(α + 1)(1 − η)^{−α−2} < θ`
  have hcont : ContinuousAt (fun δ : ℝ => (1 - δ) ^ (-α - 2)) 0 :=
    ((continuous_const.sub continuous_id).continuousAt).rpow_const (Or.inl (by norm_num))
  have hκ : (1 - (0 : ℝ)) ^ (-α - 2) < θ / (α + 1) := by
    rw [sub_zero, Real.one_rpow, lt_div_iff₀ (by linarith)]
    linarith
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 (hcont.eventually (gt_mem_nhds hκ))
  set η := min (ρ / 2) (1 / 2)
  have hη : 0 < η := lt_min (by linarith) (by norm_num)
  have hη1 : η < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hηκ : (1 - η) ^ (-α - 2) < θ / (α + 1) := by
    refine hball ?_
    rw [Real.dist_eq, sub_zero, abs_of_pos hη]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  set K := α * (α + 1) * (1 - η) ^ (-α - 2)
  have hK : K < α * θ := by
    have : (α + 1) * (1 - η) ^ (-α - 2) < θ := by
      rw [lt_div_iff₀ (by linarith)] at hηκ; linarith
    have e : K = α * ((α + 1) * (1 - η) ^ (-α - 2)) := by simp only [K]; ring
    rw [e]; exact mul_lt_mul_of_pos_left this hα
  set c := (α * θ - K) * v₀ / 2
  have hc : 0 < c := by
    have : 0 < α * θ - K := by linarith
    positivity
  -- the tail errors vanish at infinity
  set E : ℝ → ℝ := fun a => α / η * (B / (η * a) ^ ε) + a ^ α * a ^ 2 * (B / (η * a) ^ (2 + ε))
  have hE : Tendsto E atTop (𝓝 0) := by
    have h1 : Tendsto (fun a : ℝ => α / η * (B / (η * a) ^ ε)) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := B)).div_atTop
        ((tendsto_rpow_atTop hε).comp (tendsto_id.const_mul_atTop hη))
      simpa using this.const_mul (α / η)
    have h2 : Tendsto (fun a : ℝ => a ^ α * a ^ 2 * (B / (η * a) ^ (2 + ε))) atTop (𝓝 0) := by
      have h3 : Tendsto (fun a : ℝ => B / η ^ (2 + ε) / a ^ (ε - α)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_rpow_atTop (by linarith))
      refine h3.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with a ha
      have hsplit : a ^ (2 + ε) = a ^ α * a ^ 2 * a ^ (ε - α) := by
        rw [show 2 + ε = α + 2 + (ε - α) by ring, Real.rpow_add ha, Real.rpow_add ha,
          Real.rpow_two]
      rw [Real.mul_rpow hη.le ha.le, hsplit]
      have : 0 < a ^ α := Real.rpow_pos_of_pos ha _
      have : 0 < a ^ (ε - α) := Real.rpow_pos_of_pos ha _
      have : 0 < η ^ (2 + ε) := Real.rpow_pos_of_pos hη _
      field_simp
    simpa using h1.add h2
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hE.eventually (gt_mem_nhds hc))
  refine transient_of_rpow_drift hψ hψpos hα (x₁ := max (x₀ : ℝ) N) fun x hx => ?_
  have hx0 : x₀ < x := by
    have := lt_of_le_of_lt (le_max_left _ _) hx; exact_mod_cast this
  have hxpos : (0 : ℝ) < x := lt_of_le_of_lt (NNReal.coe_nonneg x₀) (by exact_mod_cast hx0)
  set a : ℝ := 1 + x
  have ha : 0 < a := by simp only [a]; linarith
  have hxN : N ≤ a := by
    have := lt_of_le_of_lt (le_max_right _ _) hx; simp only [a]; linarith
  have hEa := hN a hxN
  have h1 := integral_rpow_neg_le_of_moment hε hM hα hη hη1 x
  have hv' := hv x hx0
  have hm' := hm x hx0
  have hv0 := incrementVar_nonneg P x
  set m := meanDrift P x
  set v := incrementVar P x
  set r := a ^ α
  have hr : 0 < r := Real.rpow_pos_of_pos ha _
  set S := B / (η * a) ^ ε
  set p := B / (η * a) ^ (2 + ε)
  -- `α m a ≥ αθ v/2`
  have hma : θ * v / 2 ≤ m * a := by
    have h0 : 0 ≤ θ * v / (2 * x) := by positivity
    have : θ * v / 2 = θ * v / (2 * x) * x := by field_simp
    rw [this]
    have hm0 : 0 ≤ m := h0.trans hm'
    calc θ * v / (2 * x) * x ≤ m * x := mul_le_mul_of_nonneg_right hm' hxpos.le
      _ ≤ m * a := mul_le_mul_of_nonneg_left (by simp only [a]; linarith) hm0
  have hneg : -(α * m * a) + K * v / 2 + (α / η * S + r * a ^ 2 * p) ≤ 0 := by
    have hEa' : α / η * S + r * a ^ 2 * p < c := hEa
    have : (α * θ - K) * v₀ ≤ (α * θ - K) * v := mul_le_mul_of_nonneg_left hv' (by linarith)
    have : α * (θ * v / 2) ≤ α * (m * a) := mul_le_mul_of_nonneg_left hma hα.le
    simp only [c] at hEa'
    nlinarith
  rw [Real.rpow_neg ha.le]
  refine h1.trans ?_
  have key : r⁻¹ - r⁻¹ * α / a * m + r⁻¹ * K / (2 * a ^ 2) * v + (r⁻¹ * (α / η) / a ^ 2 * S + p) =
      r⁻¹ + r⁻¹ / a ^ 2 * (-(α * m * a) + K * v / 2 + (α / η * S + r * a ^ 2 * p)) := by
    field_simp; ring
  rw [key]
  have : r⁻¹ / a ^ 2 * (-(α * m * a) + K * v / 2 + (α / η * S + r * a ^ 2 * p)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
  linarith


/-! ### Theorem 9.5.6 (i): Harris recurrence -/

/-- The second-order coefficient of the log-log expansion: with `η = 1/(8s)`,
`D(s) = 1/(2(1 + η)²s) + 8/(25(1 + η)²s²)`. -/
noncomputable def loglogCoeff (s : ℝ) : ℝ :=
  1 / (2 * (1 + 1 / (8 * s)) ^ 2 * s) + 8 / (25 * (1 + 1 / (8 * s)) ^ 2 * s ^ 2)

/-- **The pointwise log-log bound** (`loglog_step_le`): for `a ≥ e`, `a + w ≥ e`, `s = log a`,
`η = 1/(8s)` and `D = D(s)`,
`log log(a + w) − log log a ≤ w/(as) − D w²/a² + 1{|w| > ηa} D w²/a²`. -/
theorem loglog_step_le {a w : ℝ} (ha : Real.exp 1 ≤ a) (haw : Real.exp 1 ≤ a + w) :
    Real.log (Real.log (a + w)) - Real.log (Real.log a) ≤
      w / (a * Real.log a) - loglogCoeff (Real.log a) / a ^ 2 * w ^ 2 +
      (if 1 / (8 * Real.log a) * a < |w| then loglogCoeff (Real.log a) / a ^ 2 * w ^ 2
        else 0) := by
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos 1) ha
  have haw0 : 0 < a + w := lt_of_lt_of_le (Real.exp_pos 1) haw
  set s := Real.log a
  have hs1 : 1 ≤ s := (Real.le_log_iff_exp_le ha0).2 ha
  have hs0 : 0 < s := by linarith
  set u := w / a
  have hw : w = a * u := by simp only [u]; field_simp
  have h1u : 0 < 1 + u := by
    have : 1 + u = (a + w) / a := by simp only [u]; field_simp
    rw [this]; exact div_pos haw0 ha0
  have hlogaw : Real.log (a + w) = s + Real.log (1 + u) := by
    rw [show a + w = a * (1 + u) by linear_combination hw, Real.log_mul ha0.ne' h1u.ne']
  set ℓ := Real.log (1 + u)
  have hpos : 1 ≤ s + ℓ := by rw [← hlogaw]; exact (Real.le_log_iff_exp_le haw0).2 haw
  have hΔ : Real.log (Real.log (a + w)) - Real.log s = Real.log (1 + ℓ / s) := by
    rw [hlogaw, ← Real.log_div (by linarith) hs0.ne']
    congr 1; field_simp
  have hℓu : ℓ ≤ u := by have := Real.log_le_sub_one_of_pos h1u; linarith
  have hz : 0 < 1 + ℓ / s := by
    have : 1 + ℓ / s = (s + ℓ) / s := by field_simp
    rw [this]; exact div_pos (by linarith) hs0
  have hglob : Real.log (1 + ℓ / s) ≤ u / s := by
    have := Real.log_le_sub_one_of_pos hz
    have : ℓ / s ≤ u / s := div_le_div_of_nonneg_right hℓu hs0.le
    linarith
  have hwu : w / (a * s) = u / s := by rw [hw]; field_simp
  have hwu2 : loglogCoeff s / a ^ 2 * w ^ 2 = loglogCoeff s * u ^ 2 := by rw [hw]; field_simp
  rw [hΔ, hwu, hwu2]
  split_ifs with h
  · linarith
  · push Not at h
    set η := 1 / (8 * s)
    have hη0 : 0 < η := by positivity
    have hη8 : η ≤ 1 / 8 := by
      simp only [η]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have hu : u ∈ Icc (-η) η := by
      rw [mem_Icc, ← abs_le, abs_div, abs_of_pos ha0, div_le_iff₀ ha0]; exact h
    have hq := log_one_add_le_quadratic hη0.le (by linarith) hu
    have hlow : u / (1 + u) ≤ ℓ := by
      have h2 := Real.log_le_sub_one_of_pos (inv_pos.2 h1u)
      rw [Real.log_inv] at h2
      have : u / (1 + u) = 1 - (1 + u)⁻¹ := by field_simp; ring
      linarith
    have hsq : u ^ 2 / (1 + η) ^ 2 ≤ ℓ ^ 2 := by
      rcases le_or_gt 0 u with hu0 | hu0
      · have h3 : u / (1 + η) ≤ ℓ := by
          refine le_trans ?_ hlow
          exact div_le_div_of_nonneg_left hu0 h1u (by linarith [hu.2])
        rw [← div_pow]
        exact pow_le_pow_left₀ (div_nonneg hu0 (by linarith)) h3 2
      · have h4 : u ^ 2 ≤ ℓ ^ 2 := by nlinarith
        refine le_trans (div_le_self (sq_nonneg _) ?_) h4
        nlinarith
    have hℓabs : ℓ / s ∈ Icc (-(1 / 4 : ℝ)) (1 / 4) := by
      have hl1 : -(1 / 7 : ℝ) ≤ u / (1 + u) := by
        rw [le_div_iff₀ h1u]; linarith [hu.1]
      have habs : |ℓ| ≤ 1 / 4 := abs_le.2 ⟨by linarith, by linarith [hu.2]⟩
      rw [mem_Icc, ← abs_le, abs_div, abs_of_pos hs0]
      exact (div_le_self (abs_nonneg _) hs1).trans habs
    have hq2 := log_one_add_le_quadratic (by norm_num) (by norm_num) hℓabs
    have e1 : ℓ / s ≤ u / s - u ^ 2 / (2 * (1 + η) ^ 2) / s := by
      rw [← sub_div]; exact div_le_div_of_nonneg_right hq hs0.le
    have e2 : 8 / 25 * (u ^ 2 / (1 + η) ^ 2) / s ^ 2 ≤
        (ℓ / s) ^ 2 / (2 * (1 + 1 / 4) ^ 2) := by
      have e : (ℓ / s) ^ 2 / (2 * (1 + 1 / 4) ^ 2) = 8 / 25 * ℓ ^ 2 / s ^ 2 := by
        field_simp; ring
      rw [e]
      exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
    have e3 : loglogCoeff s * u ^ 2 =
        u ^ 2 / (2 * (1 + η) ^ 2) / s + 8 / 25 * (u ^ 2 / (1 + η) ^ 2) / s ^ 2 := by
      simp only [loglogCoeff, η]; field_simp
    linarith

/-- `log log(Φ₁ + e)` is integrable under the moment bound. -/
theorem integrable_loglog {P : Kernel ℝ≥0 ℝ≥0} [IsMarkovKernel P] {ε B : ℝ} (hε : 0 < ε)
    (hM : HasMomentBound P ε B) (x : ℝ≥0) :
    Integrable (fun y : ℝ≥0 => Real.log (Real.log ((y : ℝ) + Real.exp 1))) (P x) := by
  refine ((integrable_incr hε hM x).abs.add (integrable_const ((x : ℝ) + Real.exp 1))).mono'
    (Real.measurable_log.comp (Real.measurable_log.comp
      (measurable_coe_nnreal_real.add measurable_const))).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  have hy : (0 : ℝ) ≤ y := y.2
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hpos : 0 < (y : ℝ) + Real.exp 1 := by linarith
  have hL : 1 ≤ Real.log ((y : ℝ) + Real.exp 1) :=
    (Real.le_log_iff_exp_le hpos).2 (by linarith)
  have h0 : 0 ≤ Real.log (Real.log ((y : ℝ) + Real.exp 1)) := Real.log_nonneg hL
  have h1 := Real.log_le_sub_one_of_pos (show 0 < Real.log ((y : ℝ) + Real.exp 1) by linarith)
  have h2 := Real.log_le_sub_one_of_pos hpos
  have h3 := le_abs_self ((y : ℝ) - x)
  rw [Real.norm_eq_abs, abs_of_nonneg h0, Pi.add_apply]
  linarith

/-- **The drift of `log log(x + e)`** under the moment bound (from `loglog_step_le`): with
`a = x + e`, `s = log a`, `η = 1/(8s)` and `D = D(s)`,
`E_x log log(Φ₁ + e) ≤ log log a + m/(as) − Dv/a² + (D/a²) B/(ηa)^ε`. -/
theorem integral_loglog_le {P : Kernel ℝ≥0 ℝ≥0} [IsMarkovKernel P] {ε B : ℝ} (hε : 0 < ε)
    (hM : HasMomentBound P ε B) (x : ℝ≥0) :
    ∫ y, Real.log (Real.log ((y : ℝ) + Real.exp 1)) ∂P x ≤
      Real.log (Real.log ((x : ℝ) + Real.exp 1)) +
      meanDrift P x / (((x : ℝ) + Real.exp 1) * Real.log ((x : ℝ) + Real.exp 1)) -
      loglogCoeff (Real.log ((x : ℝ) + Real.exp 1)) / ((x : ℝ) + Real.exp 1) ^ 2 *
        incrementVar P x +
      loglogCoeff (Real.log ((x : ℝ) + Real.exp 1)) / ((x : ℝ) + Real.exp 1) ^ 2 *
        (B / (1 / (8 * Real.log ((x : ℝ) + Real.exp 1)) * ((x : ℝ) + Real.exp 1)) ^ ε) := by
  set a : ℝ := (x : ℝ) + Real.exp 1
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hxa : Real.exp 1 ≤ a := by simp only [a]; linarith [NNReal.coe_nonneg x]
  have ha0 : 0 < a := by linarith
  set s := Real.log a
  have hs0 : 0 < s := lt_of_lt_of_le one_pos ((Real.le_log_iff_exp_le ha0).2 hxa)
  set L0 := Real.log s
  set c1 := 1 / (a * s)
  set c2 := loglogCoeff s / a ^ 2
  have hc2 : 0 ≤ c2 := by simp only [c2, loglogCoeff]; positivity
  set T := incrTail x (1 / (8 * s) * a)
  have hT : MeasurableSet T := measurableSet_incrTail x _
  have hsT : 0 < 1 / (8 * s) * a := by positivity
  have i1 := integrable_incr hε hM x
  have i2 := integrable_incr_sq hε hM x
  have j1 : Integrable (fun y : ℝ≥0 => c1 * ((y : ℝ) - x)) (P x) := i1.const_mul c1
  have j2 : Integrable (fun y : ℝ≥0 => c2 * ((y : ℝ) - x) ^ 2) (P x) := i2.const_mul c2
  have j3 : Integrable (fun y : ℝ≥0 => T.indicator (fun y : ℝ≥0 => c2 * ((y : ℝ) - x) ^ 2) y)
      (P x) := j2.indicator hT
  have j01 : Integrable (fun y : ℝ≥0 => L0 + c1 * ((y : ℝ) - x)) (P x) :=
    (integrable_const L0).add j1
  have j012 : Integrable (fun y : ℝ≥0 => L0 + c1 * ((y : ℝ) - x) - c2 * ((y : ℝ) - x) ^ 2)
      (P x) := j01.sub j2
  have hpt : ∀ y : ℝ≥0, Real.log (Real.log ((y : ℝ) + Real.exp 1)) ≤
      L0 + c1 * ((y : ℝ) - x) - c2 * ((y : ℝ) - x) ^ 2 +
        T.indicator (fun y : ℝ≥0 => c2 * ((y : ℝ) - x) ^ 2) y := by
    intro y
    have e : (y : ℝ) + Real.exp 1 = a + ((y : ℝ) - x) := by simp only [a]; ring
    have h := loglog_step_le (w := (y : ℝ) - x) hxa (by rw [← e]; linarith [NNReal.coe_nonneg y])
    rw [← e] at h
    have hc1 : ((y : ℝ) - x) / (a * s) = c1 * ((y : ℝ) - x) := by simp only [c1]; ring
    rw [hc1] at h
    by_cases hy : y ∈ T
    · rw [indicator_of_mem hy]
      have hc : 1 / (8 * s) * a < |(y : ℝ) - x| := hy
      split_ifs at h with h'
      · linarith
      · exact absurd hc h'
    · rw [indicator_of_notMem hy]
      have hc : ¬ 1 / (8 * s) * a < |(y : ℝ) - x| := hy
      split_ifs at h with h'
      · exact absurd h' hc
      · linarith
  have hS := setIntegral_sq_tail_le hε hM x hsT
  calc ∫ y, Real.log (Real.log ((y : ℝ) + Real.exp 1)) ∂P x
      ≤ ∫ y, (L0 + c1 * ((y : ℝ) - x) - c2 * ((y : ℝ) - x) ^ 2 +
          T.indicator (fun y : ℝ≥0 => c2 * ((y : ℝ) - x) ^ 2) y) ∂P x :=
        integral_mono (integrable_loglog hε hM x) (j012.add j3) hpt
    _ = L0 + c1 * meanDrift P x - c2 * incrementVar P x +
          c2 * ∫ y in T, ((y : ℝ) - x) ^ 2 ∂P x := by
        rw [integral_add j012 j3, integral_sub j01 j2, integral_add (integrable_const _) j1,
          integral_const, integral_const_mul, integral_const_mul, integral_indicator hT,
          integral_const_mul, meanDrift, incrementVar]
        simp [Measure.real]
    _ ≤ L0 + c1 * meanDrift P x - c2 * incrementVar P x +
          c2 * (B / (1 / (8 * s) * a) ^ ε) := by gcongr
    _ = _ := by simp only [L0, c1, c2]; ring

/-- `D(s)s ∈ [1/2 + 1/(9s), 1]` for `s ≥ 1`. -/
theorem loglogCoeff_mul_bounds {s : ℝ} (hs : 1 ≤ s) :
    1 / 2 + 1 / (9 * s) ≤ loglogCoeff s * s ∧ loglogCoeff s * s ≤ 1 := by
  have hs0 : 0 < s := by linarith
  set t := 1 / s
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by simp only [t]; rw [div_le_one hs0]; exact hs
  set q := (1 + t / 8) ^ 2
  have hq1 : 1 ≤ q := by simp only [q]; nlinarith
  have hq0 : 0 < q := by linarith
  set iq := 1 / q
  have hiq1 : 1 - t / 4 ≤ iq := by
    simp only [iq]; rw [le_div_iff₀ hq0]; simp only [q]
    have : (1 - t / 4) * (1 + t / 8) ^ 2 = 1 - 3 * t ^ 2 / 64 - t ^ 3 / 256 := by ring
    rw [this]; nlinarith [pow_pos ht0 2, pow_pos ht0 3]
  have hiq2 : 64 / 81 ≤ iq := by
    simp only [iq]; rw [le_div_iff₀ hq0]; simp only [q]; nlinarith
  have hiq3 : iq ≤ 1 := by simp only [iq]; rw [div_le_one hq0]; exact hq1
  have e : loglogCoeff s * s = iq / 2 + 8 / 25 * (iq * t) := by
    simp only [loglogCoeff, iq, q, t]; field_simp
  have e9 : 1 / (9 * s) = t / 9 := by simp only [t]; field_simp
  have p1 : 64 / 81 * t ≤ iq * t := mul_le_mul_of_nonneg_right hiq2 ht0.le
  have p2 : iq * t ≤ 1 * t := mul_le_mul_of_nonneg_right hiq3 ht0.le
  rw [e, e9]
  constructor <;> linarith

/-- **Theorem 9.5.6 (i)** (MT p. 227, proof omitted in the book): a `ψ`-irreducible chain on
`ℝ₊` whose sets `[0, c]` are petite, with `sup_x E_x|W_x|^{2+ε} ≤ B` (`ε > 0`), `v(x) ≥ v₀ > 0`
and `m(x) ≤ v(x)/2x + K x^{−1−δ}` for `x > x₀` and some `δ > 0`, is Harris recurrent. The test
function is `V(x) = log log(x + e)` and the conclusion comes from Theorem 9.1.8. -/
theorem theorem_9_5_6_i {P : Kernel ℝ≥0 ℝ≥0} [IsMarkovKernel P] {ψ : Measure ℝ≥0}
    (hψ : IsMaximalIrreducibility P ψ) (hpet : ∀ c : ℝ≥0, IsPetite P (Iic c)) {ε B : ℝ}
    (hε : 0 < ε) (hM : HasMomentBound P ε B) {v₀ : ℝ} (hv₀ : 0 < v₀) {K δ : ℝ} (hδ : 0 < δ)
    {x₀ : ℝ≥0} (hv : ∀ x, x₀ < x → v₀ ≤ incrementVar P x)
    (hm : ∀ x, x₀ < x → meanDrift P x ≤ incrementVar P x / (2 * x) + K * (x : ℝ) ^ (-1 - δ)) :
    IsHarris P ψ := by
  have hB : 0 ≤ B :=
    (integral_nonneg fun y => Real.rpow_nonneg (abs_nonneg _) _).trans (hM 0).2
  set e := Real.exp 1
  have he : 0 < e := Real.exp_pos 1
  set C := |K| * (2 * 2 ^ δ)
  have hC : 0 ≤ C := by positivity
  -- the error function and its limit
  set G : ℝ → ℝ := fun a => 18 * Real.log a * (C * a ^ (-δ) + B * (8 * Real.log a) ^ ε / a ^ ε)
  have hG : Tendsto G atTop (𝓝 0) := by
    have L1 := (isLittleO_log_rpow_rpow_atTop 1 hδ).tendsto_div_nhds_zero
    have L2 := (isLittleO_log_rpow_rpow_atTop (1 + ε) hε).tendsto_div_nhds_zero
    have hlim := ((L1.const_mul C).add (L2.const_mul (B * 8 ^ ε))).const_mul 18
    simp only [mul_zero, add_zero] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with a ha
    have ha0 : 0 < a := by linarith
    have hl : 0 < Real.log a := Real.log_pos ha
    simp only [G]
    rw [Real.rpow_one, Real.rpow_neg ha0.le, Real.mul_rpow (by norm_num) hl.le,
      Real.rpow_add hl, Real.rpow_one]
    have : 0 < a ^ δ := Real.rpow_pos_of_pos ha0 _
    have : 0 < a ^ ε := Real.rpow_pos_of_pos ha0 _
    field_simp
  have hG0 : Tendsto (fun a : ℝ => Real.log a / a) atTop (𝓝 0) := by
    have := (isLittleO_log_rpow_rpow_atTop 1 one_pos).tendsto_div_nhds_zero
    simpa only [Real.rpow_one] using this
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hG.eventually (gt_mem_nhds hv₀)).and
    (hG0.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (18 * e) by positivity))))
  set x₁ : ℝ := max (x₀ : ℝ) (max N e)
  have hdrift : ∀ x : ℝ≥0, x₁ < x → ∫ y, Real.log (Real.log ((y : ℝ) + e)) ∂P x ≤
      Real.log (Real.log ((x : ℝ) + e)) := by
    intro x hx
    have hx0 : x₀ < x := by
      have := lt_of_le_of_lt (le_max_left _ _) hx; exact_mod_cast this
    have hxN : N < x := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hx
    have hxe : e < x := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hx
    have hxpos : (0 : ℝ) < x := by linarith
    set a : ℝ := (x : ℝ) + e
    have ha0 : 0 < a := by simp only [a]; linarith
    have hxa : e ≤ a := by simp only [a]; linarith
    have ha2 : a ≤ 2 * x := by simp only [a]; linarith
    set s := Real.log a
    have hs1 : 1 ≤ s := (Real.le_log_iff_exp_le ha0).2 hxa
    have hs0 : 0 < s := by linarith
    obtain ⟨hGa, hGa0⟩ := hN a (by simp only [a]; linarith)
    have h1 := integral_loglog_le hε hM x
    have hv' := hv x hx0
    have hm' := hm x hx0
    have hv0 := incrementVar_nonneg P x
    set m := meanDrift P x
    set v := incrementVar P x
    set D := loglogCoeff s
    obtain ⟨hDs1, hDs2⟩ := loglogCoeff_mul_bounds hs1
    set S := B / (1 / (8 * s) * a) ^ ε
    have hS0 : 0 ≤ S := div_nonneg hB (Real.rpow_nonneg (by positivity) _)
    -- the error terms
    have hSeq : S = B * (8 * s) ^ ε / a ^ ε := by
      have : 1 / (8 * s) * a = a / (8 * s) := by ring
      simp only [S]; rw [this, Real.div_rpow ha0.le (by positivity)]
      have : 0 < a ^ ε := Real.rpow_pos_of_pos ha0 _
      have : 0 < (8 * s) ^ ε := Real.rpow_pos_of_pos (by positivity) _
      field_simp
    have hX : (x : ℝ) ^ (-1 - δ) * a ≤ 2 * 2 ^ δ * a ^ (-δ) := by
      have hxδ : (x : ℝ) ^ (-1 - δ) = (x : ℝ) ^ (-δ) / x := by
        rw [show -1 - δ = -δ - 1 by ring, Real.rpow_sub_one hxpos.ne']
      have hle : (x : ℝ) ^ (-δ) ≤ (a / 2) ^ (-δ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      have h2 : (a / 2) ^ (-δ) = 2 ^ δ * a ^ (-δ) := by
        rw [Real.div_rpow ha0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        field_simp
      have h3 : (x : ℝ) ^ (-δ) * (a / x) ≤ (x : ℝ) ^ (-δ) * 2 :=
        mul_le_mul_of_nonneg_left (by rw [div_le_iff₀ hxpos]; linarith)
          (Real.rpow_nonneg hxpos.le _)
      rw [hxδ, show (x : ℝ) ^ (-δ) / x * a = (x : ℝ) ^ (-δ) * (a / x) by ring]
      have : 0 ≤ 2 ^ δ * a ^ (-δ) := by positivity
      nlinarith
    have hmK : m * a ≤ v * a / (2 * x) + C * a ^ (-δ) := by
      have hK1 : K * (x : ℝ) ^ (-1 - δ) ≤ |K| * (x : ℝ) ^ (-1 - δ) :=
        mul_le_mul_of_nonneg_right (le_abs_self K) (Real.rpow_nonneg hxpos.le _)
      have hm2 : m ≤ v / (2 * x) + |K| * (x : ℝ) ^ (-1 - δ) := by linarith
      have := mul_le_mul_of_nonneg_right hm2 ha0.le
      have hKX := mul_le_mul_of_nonneg_left hX (abs_nonneg K)
      calc m * a ≤ (v / (2 * x) + |K| * (x : ℝ) ^ (-1 - δ)) * a := this
        _ = v * a / (2 * x) + |K| * ((x : ℝ) ^ (-1 - δ) * a) := by ring
        _ ≤ v * a / (2 * x) + |K| * (2 * 2 ^ δ * a ^ (-δ)) := by linarith
        _ = v * a / (2 * x) + C * a ^ (-δ) := by simp only [C]; ring
    -- `e/(2x) ≤ 1/(18s)`
    have hE1 : e / (2 * x) ≤ 1 / (18 * s) := by
      have h0 : s < 1 / (18 * e) * a := (div_lt_iff₀ ha0).1 hGa0
      have h1 : 18 * e * s < a := by
        have := mul_lt_mul_of_pos_left h0 (by positivity : (0 : ℝ) < 18 * e)
        rwa [show 18 * e * (1 / (18 * e) * a) = a by field_simp] at this
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    have hva : v * a / (2 * x) = v / 2 + v * (e / (2 * x)) := by
      simp only [a]; field_simp
    have hvE : v * (e / (2 * x)) ≤ v * (1 / (18 * s)) := mul_le_mul_of_nonneg_left hE1 hv0
    have hDv : (1 / 2 + 1 / (9 * s)) * v ≤ D * s * v := mul_le_mul_of_nonneg_right hDs1 hv0
    have hDS : D * s * S ≤ 1 * S := mul_le_mul_of_nonneg_right hDs2 hS0
    have hG' : 18 * s * (C * a ^ (-δ) + S) < v₀ := by rw [hSeq]; simpa [G, mul_div_assoc] using hGa
    have hv18 : v₀ * (1 / (18 * s)) ≤ v * (1 / (18 * s)) :=
      mul_le_mul_of_nonneg_right hv' (by positivity)
    have hG'' : C * a ^ (-δ) + S < v₀ * (1 / (18 * s)) := by
      rw [show v₀ * (1 / (18 * s)) = v₀ / (18 * s) by ring, lt_div_iff₀ (by positivity)]
      linarith
    have h9 : 1 / (9 * s) = 2 * (1 / (18 * s)) := by field_simp; ring
    have hnum : m * a - D * s * v + D * s * S ≤ 0 := by nlinarith
    have key : m / (a * s) - D / a ^ 2 * v + D / a ^ 2 * S =
        (m * a - D * s * v + D * s * S) / (a ^ 2 * s) := by field_simp
    have : (m * a - D * s * v + D * s * S) / (a ^ 2 * s) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hnum (by positivity)
    linarith
  -- the test function `V(x) = log log(x + e)` and Theorem 9.1.8
  set V : ℝ≥0 → ℝ≥0 := fun y => Real.toNNReal (Real.log (Real.log ((y : ℝ) + e)))
  have hVm : Measurable V := (Real.measurable_log.comp (Real.measurable_log.comp
    (measurable_coe_nnreal_real.add measurable_const))).real_toNNReal
  have hlog1 : ∀ y : ℝ≥0, 1 ≤ Real.log ((y : ℝ) + e) := fun y =>
    (Real.le_log_iff_exp_le (by linarith [NNReal.coe_nonneg y])).2
      (by linarith [NNReal.coe_nonneg y])
  have hVcoe : ∀ y : ℝ≥0, (V y : ℝ) = Real.log (Real.log ((y : ℝ) + e)) := fun y =>
    Real.coe_toNNReal _ (Real.log_nonneg (hlog1 y))
  have hpetV : ∀ n : ℕ, IsPetite P {y | V y ≤ n} := fun n =>
    isPetite_of_subset (hpet (Real.toNNReal (Real.exp (Real.exp n))))
      (measurableSet_le hVm measurable_const) fun y hy => by
        simp only [mem_ofPred_eq] at hy
        have h1 : Real.log (Real.log ((y : ℝ) + e)) ≤ n := by
          have := NNReal.coe_le_coe.2 hy
          rwa [hVcoe] at this
        have h2 : Real.log ((y : ℝ) + e) ≤ Real.exp n := by
          rw [← Real.log_le_iff_le_exp (by linarith [hlog1 y])]; exact h1
        have h3 : (y : ℝ) + e ≤ Real.exp (Real.exp n) := by
          rw [← Real.log_le_iff_le_exp (by linarith [NNReal.coe_nonneg y])]; exact h2
        rw [mem_Iic, ← NNReal.coe_le_coe, Real.coe_toNNReal _ (Real.exp_pos _).le]
        linarith
  refine theorem_9_1_8 hψ (hpet (Real.toNNReal x₁)) hVm hpetV fun x hx => ?_
  simp only [mem_Iic, not_le] at hx
  have hx' : x₁ < x := by
    have := NNReal.coe_lt_coe.2 hx
    rwa [Real.coe_toNNReal _ ((NNReal.coe_nonneg x₀).trans (le_max_left _ _))] at this
  rw [drift_nonpos_iff]
  have heq : ∀ y : ℝ≥0, ((V y : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (Real.log (Real.log ((y : ℝ) + e))) := fun y => by
    rw [← hVcoe]; exact (ENNReal.ofReal_coe_nnreal).symm
  simp_rw [heq]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_loglog hε hM x)
    (Eventually.of_forall fun y => Real.log_nonneg (hlog1 y))]
  exact ENNReal.ofReal_le_ofReal (hdrift x hx')

end MeynTweedie.HarrisRecurrence
