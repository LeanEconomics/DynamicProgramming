/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import HarrisRecurrence.DriftCriteria
import HarrisRecurrence.SmallSetsModels

/-!
# Classifying random walk on `ℝ₊` (MT §8.5.1–8.5.2)

Meyn and Tweedie, §8.5, pp. 193–195. The walk is `halfLineWalkKernel Γ` on `ℝ≥0`,
`Φₙ = [Φₙ₋₁ + Wₙ]⁺` (RWHL1), with increment law `Γ` on `ℝ` of finite mean `β = ∫ w Γ(dw)`.

**Tools.**
* `lintegral_halfLine`, `integral_halfLine`: `∫ P(x, dy) f(y) = ∫ Γ(dw) f([x + w]⁺)`.
* `isPetite_of_subset`, `halfLine_isPetite_Iic`: if `Γ(−∞, 0) > 0`, every `[0, c]` is petite
  (it is small, `halfLine_isSmallSet_Iic`), so a function with bounded sublevel sets is unbounded
  off petite sets.
* `halfLine_neg_pos_of_mean_neg`, `halfLine_neg_pos_of_mean_zero`: `Γ(−∞, 0) > 0` follows from
  `β < 0`, and from `β = 0` with `E[W²] > 0`.

**Results.**
* **Proposition 8.5.1** (`proposition_8_5_1`, p. 193): `β < 0` makes the walk recurrent;
  `halfLine_drift_neg` is the drift (8.54), `∫ P(x, dy) y ≤ x − ε` for `x > x₀`.
* `log_one_add_le`: `log(1 + u) ≤ u − (u²/2) 1{u < 0}` for `u > −1`.
* **Lemma 8.5.2** (`lemma_8_5_2`, p. 194): for `A ⊆ {s + tw > 0}`, `E[log(s + tW); A] ≤`
  `Γ(A) log s + (t/s) E[W; A] − (t²/2s²) E[W²; A ∩ {tW < 0}]`.
* `tendsto_setIntegral_zero`, `tendsto_mul_setIntegral_abs_zero`: tail integrals of an
  integrable function vanish, and `x E[|W|; |W| ≥ s x] → 0`.
* **Lemma 8.5.3** (`lemma_8_5_3_i`, `lemma_8_5_3_ii`, p. 194): the limits (8.56) and, for
  `E[W] = 0`, (8.57).
* **Proposition 8.5.4** (`proposition_8_5_4`, p. 195): `β = 0` with `0 < E[W²] < ∞` makes the
  walk recurrent, with the test function `V(x) = log(1 + x)`.

**Corrections.**
* Lemma 8.5.2 needs `log(s + tW)` integrable on `A` (otherwise the left side is not defined);
  this is a hypothesis.
* In Proposition 8.5.4 the test function (8.58) with a cut-off `R` is not needed:
  `V(x) = log(1 + x)` on all of `ℝ₊` works, with `C = [0, x₁]` for a large `x₁`. The book's
  estimate `U₁(x) = o(x⁻²)` is replaced by the explicit bound
  `E[W; W > −x] = −E[W; W ≤ −x] ≤ E[W²; W ≤ −x]/x`.
-/

namespace MeynTweedie.HarrisRecurrence

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

/-! ### The kernel of the walk on `ℝ₊` -/

/-- `∫ P(x, dy) f(y) = ∫ Γ(dw) f([x + w]⁺)` for the walk on `ℝ₊`. -/
theorem lintegral_halfLine (Γ : Measure ℝ) [SFinite Γ] (x : ℝ≥0) {f : ℝ≥0 → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ y, f y ∂halfLineWalkKernel Γ x = ∫⁻ w, f (Real.toNNReal (x + w)) ∂Γ := by
  have hm : Measurable fun w : ℝ => halfLineStep (x, w) :=
    measurable_halfLineStep.comp measurable_prodMk_left
  rw [halfLineWalkKernel, recursionKernel_apply Γ measurable_halfLineStep x, lintegral_map hf hm]
  rfl

/-- `∫ P(x, dy) f(y) = ∫ Γ(dw) f([x + w]⁺)` for real `f`. -/
theorem integral_halfLine (Γ : Measure ℝ) [SFinite Γ] (x : ℝ≥0) {f : ℝ≥0 → ℝ}
    (hf : Measurable f) :
    ∫ y, f y ∂halfLineWalkKernel Γ x = ∫ w, f (Real.toNNReal (x + w)) ∂Γ := by
  have hm : Measurable fun w : ℝ => halfLineStep (x, w) :=
    measurable_halfLineStep.comp measurable_prodMk_left
  rw [halfLineWalkKernel, recursionKernel_apply Γ measurable_halfLineStep x,
    integral_map hm.aemeasurable hf.aestronglyMeasurable]
  rfl

/-- A measurable subset of a petite set is petite. -/
theorem isPetite_of_subset {X : Type*} [MeasurableSpace X] {P : Kernel X X} {A B : Set X}
    (hA : IsPetite P A) (hB : MeasurableSet B) (hBA : B ⊆ A) : IsPetite P B := by
  obtain ⟨a, ν, -, ha, hν, hle⟩ := hA
  exact ⟨a, ν, hB, ha, hν, fun x hx => hle x (hBA hx)⟩

/-- If `Γ(−∞, 0) > 0`, every `[0, c]` is petite for the walk on `ℝ₊`. -/
theorem halfLine_isPetite_Iic (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (h : 0 < Γ (Iio 0))
    (c : ℝ≥0) : IsPetite (halfLineWalkKernel Γ) (Iic c) := by
  obtain ⟨m, δ, -, hs⟩ := halfLine_isSmallSet_Iic Γ h c
  exact ⟨_, _, proposition_5_5_3 hs⟩

/-- `Γ(−∞, 0) > 0` when the mean is negative. -/
theorem halfLine_neg_pos_of_mean_neg (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hβ : ∫ w, w ∂Γ < 0) : 0 < Γ (Iio 0) := by
  rw [pos_iff_ne_zero]
  intro h0
  have : ∀ᵐ w ∂Γ, 0 ≤ w := by
    have := measure_eq_zero_iff_ae_notMem.1 h0
    exact this.mono fun w hw => not_lt.1 hw
  exact absurd (integral_nonneg_of_ae this) (not_le.2 hβ)

/-- `Γ(−∞, 0) > 0` when the mean is zero and `E[W²] > 0`. -/
theorem halfLine_neg_pos_of_mean_zero (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => w) Γ) (hβ : ∫ w, w ∂Γ = 0) (hvar : 0 < ∫ w, w ^ 2 ∂Γ) :
    0 < Γ (Iio 0) := by
  rw [pos_iff_ne_zero]
  intro h0
  have hnn : ∀ᵐ w ∂Γ, 0 ≤ w :=
    (measure_eq_zero_iff_ae_notMem.1 h0).mono fun w hw => not_lt.1 hw
  have hz : (fun w => w) =ᵐ[Γ] 0 := (integral_eq_zero_iff_of_nonneg_ae hnn hW).1 hβ
  have h2 : (fun w : ℝ => w ^ 2) =ᵐ[Γ] 0 := hz.mono fun w hw => by
    simp only [Pi.zero_apply] at hw ⊢; rw [hw]; ring
  have : ∫ w, w ^ 2 ∂Γ = 0 := by rw [integral_congr_ae h2]; simp
  exact hvar.ne' this

/-! ### Proposition 8.5.1 -/

/-- **The drift (8.54)** (MT p. 193): if `β < 0` there are `x₀` and `ε > 0` with
`∫ P(x, dy) y ≤ x − ε` for `x > x₀`. -/
theorem halfLine_drift_neg (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => w) Γ) (hβ : ∫ w, w ∂Γ < 0) :
    ∃ x₀ : ℝ≥0, ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ≥0, x₀ < x →
      ∫ y, (y : ℝ) ∂halfLineWalkKernel Γ x ≤ x - ε := by
  -- `E[max(W, −n)] → β`
  have hlim : Tendsto (fun n : ℕ => ∫ w, max w (-(n : ℝ)) ∂Γ) atTop (𝓝 (∫ w, w ∂Γ)) := by
    refine tendsto_integral_of_dominated_convergence (fun w => |w|)
      (fun n => (measurable_id.max measurable_const).aestronglyMeasurable) hW.abs
      (fun n => Eventually.of_forall fun w => ?_) (Eventually.of_forall fun w => ?_)
    · rw [Real.norm_eq_abs, abs_le]
      constructor
      · exact (neg_abs_le w).trans (le_max_left _ _)
      · exact max_le (le_abs_self w) (by linarith [abs_nonneg w, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (⌈-w⌉₊)] with n hn
      have : -(n : ℝ) ≤ w := by
        have := Nat.le_ceil (-w)
        have h2 : (⌈-w⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      exact (max_eq_left this).symm
  have hβ2 : ∫ w, w ∂Γ < (∫ w, w ∂Γ) / 2 := by linarith
  obtain ⟨n₀, hn₀⟩ := ((hlim.eventually (gt_mem_nhds hβ2))).exists
  refine ⟨n₀, -((∫ w, w ∂Γ) / 2), by linarith, fun x hx => ?_⟩
  have hint : Integrable (fun w => max w (-(n₀ : ℝ))) Γ :=
    (hW.abs.add (integrable_const (n₀ : ℝ))).mono' (measurable_id.max measurable_const
      ).aestronglyMeasurable (Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs]
        rcases le_total w (-(n₀ : ℝ)) with h | h
        · rw [max_eq_right h, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
          simp only [Pi.add_apply]; linarith [abs_nonneg w]
        · rw [max_eq_left h]; simp only [Pi.add_apply]; linarith [Nat.cast_nonneg (α := ℝ) n₀])
  have hint2 : Integrable (fun w => max ((x : ℝ) + w) 0) Γ :=
    ((integrable_const (x : ℝ)).add hW.abs).mono'
      ((measurable_const.add measurable_id).max measurable_const).aestronglyMeasurable
      (Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        simp only [Pi.add_apply]
        exact max_le (by linarith [le_abs_self w]) (by positivity))
  rw [integral_halfLine Γ x measurable_coe_nnreal_real]
  simp_rw [Real.coe_toNNReal']
  calc ∫ w, max ((x : ℝ) + w) 0 ∂Γ ≤ ∫ w, (x + max w (-(n₀ : ℝ))) ∂Γ := by
        refine integral_mono hint2 ((integrable_const _).add hint) fun w => ?_
        have hx' : (n₀ : ℝ) ≤ x := by exact_mod_cast hx.le
        rcases le_total ((x : ℝ) + w) 0 with h | h
        · rw [max_eq_right h]; linarith [le_max_right w (-(n₀ : ℝ))]
        · rw [max_eq_left h]; linarith [le_max_left w (-(n₀ : ℝ))]
    _ = x + ∫ w, max w (-(n₀ : ℝ)) ∂Γ := by
        rw [integral_add (integrable_const _) hint, integral_const]; simp
    _ ≤ x - -((∫ w, w ∂Γ) / 2) := by linarith

/-- **Proposition 8.5.1** (MT p. 193): random walk on a half line with negative mean increment is
recurrent. The test function is `V(x) = x`, with `C = [0, x₀]`. -/
theorem proposition_8_5_1 (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => w) Γ) (hβ : ∫ w, w ∂Γ < 0) {ψ : Measure ℝ≥0}
    (hψ : haveI := isMarkovKernel_halfLineWalkKernel Γ
      IsMaximalIrreducibility (halfLineWalkKernel Γ) ψ) :
    haveI := isMarkovKernel_halfLineWalkKernel Γ
    IsRecurrentChain (halfLineWalkKernel Γ) ψ := by
  have := isMarkovKernel_halfLineWalkKernel Γ
  have hneg := halfLine_neg_pos_of_mean_neg Γ hβ
  obtain ⟨x₀, ε, hε, hdr⟩ := halfLine_drift_neg Γ hW hβ
  refine (theorem_8_4_3 _ hψ (halfLine_isPetite_Iic Γ hneg x₀) (V := id) measurable_id
    (fun n => halfLine_isPetite_Iic Γ hneg n) (fun x hx => ?_)).1
  simp only [mem_Iic, not_le] at hx
  rw [drift_nonpos_iff]
  have hint : Integrable (fun y : ℝ≥0 => (y : ℝ)) (halfLineWalkKernel Γ x) := by
    have : Integrable (fun w => ((Real.toNNReal ((x : ℝ) + w) : ℝ≥0) : ℝ)) Γ := by
      simp_rw [Real.coe_toNNReal']
      exact ((integrable_const (x : ℝ)).add hW.abs).mono'
        ((measurable_const.add measurable_id).max measurable_const).aestronglyMeasurable
        (Eventually.of_forall fun w => by
          rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
          simp only [Pi.add_apply]
          exact max_le (by linarith [le_abs_self w]) (by positivity))
    have hm : Measurable fun w : ℝ => halfLineStep (x, w) :=
      measurable_halfLineStep.comp measurable_prodMk_left
    rw [halfLineWalkKernel, recursionKernel_apply Γ measurable_halfLineStep x,
      integrable_map_measure measurable_coe_nnreal_real.aestronglyMeasurable hm.aemeasurable]
    exact this
  have h1 : ∫⁻ y, ((id y : ℝ≥0) : ℝ≥0∞) ∂halfLineWalkKernel Γ x =
      ENNReal.ofReal (∫ y, (y : ℝ) ∂halfLineWalkKernel Γ x) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun y => y.2)]
    simp
  rw [h1, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal ((hdr x hx).trans (by simp; linarith))

/-! ### Lemma 8.5.2 -/

/-- `log(1 + u) ≤ u − (u²/2) 1{u < 0}` for `u > −1` (proof of Lemma 8.5.2, MT p. 194). -/
theorem log_one_add_le {u : ℝ} (hu : -1 < u) :
    Real.log (1 + u) ≤ u - u ^ 2 / 2 * (if u < 0 then 1 else 0) := by
  split_ifs with h
  · have habs : |(-u)| < 1 := by rw [abs_of_pos (by linarith)]; linarith
    have hs := Real.hasSum_pow_div_log_of_abs_lt_one habs
    rw [sub_neg_eq_add] at hs
    have := sum_le_hasSum (Finset.range 2) (fun n _ => div_nonneg (pow_nonneg (by linarith) _)
      (by positivity)) hs
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_one] at this
    norm_num at this
    nlinarith
  · have := Real.log_le_sub_one_of_pos (show 0 < 1 + u by linarith)
    simp only [mul_zero, sub_zero]
    linarith

/-- **Lemma 8.5.2** (MT p. 194): for `s > 0`, `t ∈ ℝ` and `A ⊆ {w : s + tw > 0}` on which
`log(s + tW)` is integrable,
`E[log(s + tW); A] ≤ Γ(A) log s + (t/s) E[W; A] − (t²/(2s²)) E[W²; A ∩ {tW < 0}]`. -/
theorem lemma_8_5_2 (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (hW : Integrable (fun w => w) Γ)
    (hW2 : Integrable (fun w => w ^ 2) Γ) {s : ℝ} (hs : 0 < s) (t : ℝ) {A : Set ℝ}
    (hA : MeasurableSet A) (hAsub : A ⊆ {w | 0 < s + t * w})
    (hlog : IntegrableOn (fun w => Real.log (s + t * w)) A Γ) :
    ∫ w in A, Real.log (s + t * w) ∂Γ ≤ (Γ A).toReal * Real.log s + t / s * ∫ w in A, w ∂Γ -
      t ^ 2 / (2 * s ^ 2) * ∫ w in A ∩ {w | t * w < 0}, w ^ 2 ∂Γ := by
  have hm : MeasurableSet {w : ℝ | t * w < 0} := measurableSet_lt (measurable_const.mul
    measurable_id) measurable_const
  set g : ℝ → ℝ := fun w => Real.log s + t / s * w -
    t ^ 2 / (2 * s ^ 2) * ({w : ℝ | t * w < 0}.indicator (fun w => w ^ 2) w) with hg
  have hgint : IntegrableOn g A Γ :=
    (((integrable_const _).add (hW.const_mul _)).sub
      ((hW2.indicator hm).const_mul _)).integrableOn
  calc ∫ w in A, Real.log (s + t * w) ∂Γ ≤ ∫ w in A, g w ∂Γ := by
        refine setIntegral_mono_on hlog hgint hA fun w hw => ?_
        have hpos : 0 < s + t * w := hAsub hw
        have hu : -1 < t * w / s := by
          rw [lt_div_iff₀ hs]; linarith
        have hsplit : Real.log (s + t * w) = Real.log s + Real.log (1 + t * w / s) := by
          rw [← Real.log_mul hs.ne' (ne_of_gt (by linarith))]
          congr 1; field_simp
        rw [hsplit, hg]
        dsimp only
        have := log_one_add_le hu
        by_cases hneg : t * w < 0
        · have hu' : t * w / s < 0 := div_neg_of_neg_of_pos hneg hs
          simp only [hu', ite_true, mul_one] at this
          rw [indicator_of_mem (show w ∈ {w : ℝ | t * w < 0} from hneg)]
          have e : (t * w / s) ^ 2 / 2 = t ^ 2 / (2 * s ^ 2) * w ^ 2 := by field_simp
          have e2 : t * w / s = t / s * w := by ring
          linarith
        · have hu' : ¬ t * w / s < 0 := fun h => hneg (by
            have := (div_neg_iff.1 h); rcases this with ⟨_, h2⟩ | ⟨h1, _⟩
            · linarith
            · exact h1)
          simp only [hu', ite_false, mul_zero, sub_zero] at this
          rw [indicator_of_notMem (show w ∉ {w : ℝ | t * w < 0} from hneg), mul_zero, sub_zero]
          have e2 : t * w / s = t / s * w := by ring
          linarith
    _ = _ := by
        rw [hg]
        dsimp only
        have i1 : IntegrableOn (fun w => Real.log s + t / s * w) A Γ :=
          ((integrable_const _).add (hW.const_mul _)).integrableOn
        have i2 : IntegrableOn (fun w => t ^ 2 / (2 * s ^ 2) *
            {w : ℝ | t * w < 0}.indicator (fun w => w ^ 2) w) A Γ :=
          ((hW2.indicator hm).const_mul _).integrableOn
        have i3 : IntegrableOn (fun _ : ℝ => Real.log s) A Γ := (integrable_const _).integrableOn
        have i4 : IntegrableOn (fun w : ℝ => t / s * w) A Γ := (hW.const_mul _).integrableOn
        rw [integral_sub i1 i2, integral_add i3 i4, setIntegral_const, integral_const_mul,
          integral_const_mul, setIntegral_indicator hm]
        simp [measureReal_def]

/-! ### Lemma 8.5.3 -/

/-- Tail integrals vanish: if every `w` eventually leaves `S x`, then `∫_{S x} f → 0` for
integrable `f` (dominated convergence). -/
theorem tendsto_setIntegral_zero (Γ : Measure ℝ) {f : ℝ → ℝ} (hf : Integrable f Γ)
    {S : ℝ → Set ℝ} (hS : ∀ x, MeasurableSet (S x)) (hlim : ∀ w, ∀ᶠ x in atTop, w ∉ S x) :
    Tendsto (fun x => ∫ w in S x, f w ∂Γ) atTop (𝓝 0) := by
  simp_rw [← integral_indicator (hS _)]
  have := tendsto_integral_filter_of_dominated_convergence (l := atTop)
    (F := fun x => (S x).indicator f) (f := 0) (fun w => ‖f w‖)
    (Eventually.of_forall fun x => (hf.indicator (hS x)).aestronglyMeasurable)
    (Eventually.of_forall fun x => Eventually.of_forall fun w => norm_indicator_le_norm_self f w)
    hf.norm (Eventually.of_forall fun w => tendsto_const_nhds.congr'
      ((hlim w).mono fun x hx => (indicator_of_notMem hx f).symm))
  simpa using this

/-- `x E[|W|; S x] → 0` when every `w` eventually leaves `S x` and `|w| ≥ s x` on `S x`, for
`E[W²] < ∞`. -/
theorem tendsto_mul_setIntegral_abs_zero (Γ : Measure ℝ) [IsFiniteMeasure Γ]
    (hW : Integrable (fun w => w) Γ) (hW2 : Integrable (fun w => w ^ 2) Γ) {S : ℝ → Set ℝ}
    (hS : ∀ x, MeasurableSet (S x)) (hlim : ∀ w, ∀ᶠ x in atTop, w ∉ S x) {s : ℝ} (hs : 0 < s)
    (hbig : ∀ᶠ x in atTop, ∀ w ∈ S x, s * x ≤ |w|) :
    Tendsto (fun x => x * ∫ w in S x, |w| ∂Γ) atTop (𝓝 0) := by
  have hT := (tendsto_setIntegral_zero Γ hW2 hS hlim).const_mul (1 / s)
  rw [mul_zero] at hT
  refine squeeze_zero' ?_ ?_ hT
  · filter_upwards [eventually_ge_atTop 0] with x hx
    exact mul_nonneg hx (setIntegral_nonneg (hS x) fun w _ => abs_nonneg w)
  · filter_upwards [eventually_ge_atTop 0, hbig] with x hx hxb
    rw [← integral_const_mul, ← integral_const_mul]
    refine setIntegral_mono_on (hW.abs.const_mul x).integrableOn (hW2.const_mul _).integrableOn
      (hS x) fun w hw => ?_
    have := hxb w hw
    rw [show 1 / s * w ^ 2 = |w| * |w| / s by rw [← sq_abs]; ring, le_div_iff₀ hs]
    nlinarith [abs_nonneg w]

/-- **Lemma 8.5.3**, (8.56) (MT p. 194): for `E[W²] < ∞`, `s > 0`, `t ∈ ℝ`,
`−x E[W; W < t − sx] → 0` and `x E[W; W > t + sx] → 0` as `x → ∞`. -/
theorem lemma_8_5_3_i (Γ : Measure ℝ) [IsFiniteMeasure Γ] (hW : Integrable (fun w => w) Γ)
    (hW2 : Integrable (fun w => w ^ 2) Γ) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    Tendsto (fun x => -x * ∫ w in {w | w < t - s * x}, w ∂Γ) atTop (𝓝 0) ∧
      Tendsto (fun x => x * ∫ w in {w | t + s * x < w}, w ∂Γ) atTop (𝓝 0) := by
  have hs2 : 0 < s / 2 := by positivity
  constructor
  · have hc := tendsto_mul_setIntegral_abs_zero Γ hW hW2 (S := fun x => {w | w < t - s * x})
      (fun x => measurableSet_lt measurable_id measurable_const)
      (fun w => (eventually_ge_atTop ((t - w) / s)).mono fun x hx => by
        simp only [mem_ofPred_eq, not_lt]
        rw [div_le_iff₀ hs] at hx; linarith) hs2
      ((eventually_ge_atTop (2 * |t| / s)).mono fun x hx w hw => by
        simp only [mem_ofPred_eq] at hw
        rw [div_le_iff₀ hs] at hx
        rw [abs_of_neg (by linarith [le_abs_self t, abs_nonneg t, mul_comm x s])]
        linarith [neg_abs_le t, le_abs_self t, mul_comm x s])
    refine squeeze_zero_norm' ?_ hc
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hx]
    exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hx
  · have hc := tendsto_mul_setIntegral_abs_zero Γ hW hW2 (S := fun x => {w | t + s * x < w})
      (fun x => measurableSet_lt measurable_const measurable_id)
      (fun w => (eventually_ge_atTop ((w - t) / s)).mono fun x hx => by
        simp only [mem_ofPred_eq, not_lt]
        rw [div_le_iff₀ hs] at hx; linarith) hs2
      ((eventually_ge_atTop (2 * |t| / s)).mono fun x hx w hw => by
        simp only [mem_ofPred_eq] at hw
        rw [div_le_iff₀ hs] at hx
        rw [abs_of_pos (by linarith [neg_abs_le t, abs_nonneg t, mul_comm x s])]
        linarith [neg_abs_le t, mul_comm x s])
    refine squeeze_zero_norm' ?_ hc
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx]
    exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hx

/-- **Lemma 8.5.3**, (8.57) (MT p. 194): if moreover `E[W] = 0`, then
`−x E[W; W > t − sx] → 0` and `x E[W; W < t + sx] → 0` as `x → ∞`. -/
theorem lemma_8_5_3_ii (Γ : Measure ℝ) [IsFiniteMeasure Γ] (hW : Integrable (fun w => w) Γ)
    (hW2 : Integrable (fun w => w ^ 2) Γ) (hβ : ∫ w, w ∂Γ = 0) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    Tendsto (fun x => -x * ∫ w in {w | t - s * x < w}, w ∂Γ) atTop (𝓝 0) ∧
      Tendsto (fun x => x * ∫ w in {w | w < t + s * x}, w ∂Γ) atTop (𝓝 0) := by
  have hs2 : 0 < s / 2 := by positivity
  -- `E[W; S] = −E[W; Sᶜ]`
  have hcompl : ∀ S : Set ℝ, MeasurableSet S → ∫ w in Sᶜ, w ∂Γ = -∫ w in S, w ∂Γ := fun S hS => by
    have := integral_add_compl hS hW
    rw [hβ] at this; linarith
  constructor
  · have hc := tendsto_mul_setIntegral_abs_zero Γ hW hW2 (S := fun x => {w | w ≤ t - s * x})
      (fun x => measurableSet_le measurable_id measurable_const)
      (fun w => (eventually_gt_atTop ((t - w) / s)).mono fun x hx => by
        simp only [mem_ofPred_eq, not_le]
        rw [div_lt_iff₀ hs] at hx; linarith) hs2
      ((eventually_ge_atTop (2 * |t| / s + 1)).mono fun x hx w hw => by
        simp only [mem_ofPred_eq] at hw
        have hx' : 2 * |t| + s ≤ s * x := by
          have := (div_le_iff₀ hs).1 (show 2 * |t| / s ≤ x - 1 by linarith)
          linarith [mul_comm x s, sub_mul x 1 s]
        rw [abs_of_neg (by linarith [le_abs_self t, abs_nonneg t])]
        linarith [neg_abs_le t, le_abs_self t])
    refine squeeze_zero_norm' ?_ hc
    filter_upwards [eventually_ge_atTop 0] with x hx
    have hset : {w : ℝ | t - s * x < w} = {w | w ≤ t - s * x}ᶜ := by ext w; simp
    rw [hset, hcompl {w | w ≤ t - s * x} (measurableSet_le measurable_id measurable_const),
      Real.norm_eq_abs, neg_mul_neg, abs_mul, abs_of_nonneg hx]
    exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hx
  · have hc := tendsto_mul_setIntegral_abs_zero Γ hW hW2 (S := fun x => {w | t + s * x ≤ w})
      (fun x => measurableSet_le measurable_const measurable_id)
      (fun w => (eventually_gt_atTop ((w - t) / s)).mono fun x hx => by
        simp only [mem_ofPred_eq, not_le]
        rw [div_lt_iff₀ hs] at hx; linarith) hs2
      ((eventually_ge_atTop (2 * |t| / s)).mono fun x hx w hw => by
        simp only [mem_ofPred_eq] at hw
        rw [div_le_iff₀ hs] at hx
        have hx' : 0 ≤ x := by
          by_contra hneg
          push Not at hneg
          have := mul_neg_of_neg_of_pos hneg hs
          linarith [abs_nonneg t]
        rw [abs_of_nonneg (by linarith [neg_abs_le t, abs_nonneg t, mul_comm x s])]
        linarith [neg_abs_le t, mul_comm x s])
    refine squeeze_zero_norm' ?_ hc
    filter_upwards [eventually_ge_atTop 0] with x hx
    have hset : {w : ℝ | w < t + s * x} = {w | t + s * x ≤ w}ᶜ := by ext w; simp
    rw [hset, hcompl {w | t + s * x ≤ w} (measurableSet_le measurable_const measurable_id),
      Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hx]
    exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hx

/-! ### Proposition 8.5.4 -/

/-- `E[W²] < ∞` implies `E|W| < ∞` on a probability space. -/
theorem integrable_of_integrable_sq (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW2 : Integrable (fun w => w ^ 2) Γ) : Integrable (fun w => w) Γ :=
  ((integrable_const 1).add hW2).mono' measurable_id.aestronglyMeasurable
    (Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs]
      simp only [Pi.add_apply]
      nlinarith [abs_nonneg w, sq_abs w])

/-- **Proposition 8.5.4** (MT p. 195): random walk on a half line whose increment has mean
`β = 0` and finite positive variance `0 < E[W²] < ∞` is recurrent. The test function is
`V(x) = log(1 + x)`: by Lemma 8.5.2, for large `x`,
`E_x[V(Φ₁)] ≤ V(x) + E[W²; W ≤ −x]/(x(1 + x)) − E[W²; −x < W < 0]/(2(1 + x)²) ≤ V(x)`. -/
theorem proposition_8_5_4 (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW2 : Integrable (fun w => w ^ 2) Γ) (hβ : ∫ w, w ∂Γ = 0) (hvar : 0 < ∫ w, w ^ 2 ∂Γ)
    {ψ : Measure ℝ≥0}
    (hψ : haveI := isMarkovKernel_halfLineWalkKernel Γ
      IsMaximalIrreducibility (halfLineWalkKernel Γ) ψ) :
    haveI := isMarkovKernel_halfLineWalkKernel Γ
    IsRecurrentChain (halfLineWalkKernel Γ) ψ := by
  have := isMarkovKernel_halfLineWalkKernel Γ
  have hW := integrable_of_integrable_sq Γ hW2
  have hneg := halfLine_neg_pos_of_mean_zero Γ hW hβ hvar
  -- `c = E[W²; W < 0] > 0`
  set c := ∫ w in Iio 0, w ^ 2 ∂Γ with hc
  have hcpos : 0 < c := by
    rw [hc, setIntegral_pos_iff_support_of_nonneg_ae (Eventually.of_forall fun w => sq_nonneg w)
      hW2.integrableOn]
    have : Function.support (fun w : ℝ => w ^ 2) ∩ Iio 0 = Iio 0 := by
      ext w
      simp only [mem_inter_iff, Function.mem_support, mem_Iio, ne_eq, pow_eq_zero_iff,
        OfNat.ofNat_ne_zero, not_false_eq_true]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨h.ne, h⟩
    rwa [this]
  -- `T(x) = E[W²; W ≤ −x] → 0`
  have hT := tendsto_setIntegral_zero Γ hW2 (S := fun x => Iic (-x))
    (fun x => measurableSet_Iic)
    (fun w => (eventually_gt_atTop (-w)).mono fun x hx => by simp only [mem_Iic]; linarith)
  obtain ⟨a₀, ha₀⟩ := eventually_atTop.1 (hT.eventually (gt_mem_nhds (show (0 : ℝ) < c / 5 by
    positivity)))
  set x₁ : ℝ≥0 := Real.toNNReal (max a₀ 1) with hx₁
  -- the test function
  set V : ℝ≥0 → ℝ≥0 := fun y => Real.toNNReal (Real.log (1 + y)) with hV
  have hVm : Measurable V :=
    (Real.measurable_log.comp (measurable_const.add measurable_coe_nnreal_real)).real_toNNReal
  have hVcoe : ∀ y : ℝ≥0, (V y : ℝ) = Real.log (1 + y) := fun y => by
    rw [hV, Real.coe_toNNReal _ (Real.log_nonneg (by linarith [NNReal.coe_nonneg y]))]
  have hpet : ∀ n : ℕ, IsPetite (halfLineWalkKernel Γ) {y | V y ≤ n} := fun n =>
    isPetite_of_subset (halfLine_isPetite_Iic Γ hneg (Real.toNNReal (Real.exp n)))
      (measurableSet_le hVm measurable_const) fun y hy => by
        simp only [mem_ofPred_eq] at hy
        have h1 : Real.log (1 + y) ≤ n := by
          have := NNReal.coe_le_coe.2 hy
          rwa [hVcoe] at this
        have h2 : 1 + (y : ℝ) ≤ Real.exp n := by
          rw [← Real.log_le_iff_le_exp (by linarith [NNReal.coe_nonneg y])]; exact h1
        rw [mem_Iic, ← NNReal.coe_le_coe, Real.coe_toNNReal _ (Real.exp_pos _).le]
        linarith
  refine (theorem_8_4_3 _ hψ (halfLine_isPetite_Iic Γ hneg x₁) hVm hpet (fun x hx => ?_)).1
  simp only [mem_Iic, not_le] at hx
  have hxa : a₀ ≤ (x : ℝ) := by
    have := NNReal.coe_lt_coe.2 hx
    rw [hx₁, Real.coe_toNNReal _ (by positivity)] at this
    linarith [le_max_left a₀ 1]
  have hx1 : (1 : ℝ) ≤ x := by
    have := NNReal.coe_lt_coe.2 hx
    rw [hx₁, Real.coe_toNNReal _ (by positivity)] at this
    linarith [le_max_right a₀ 1]
  have hx0 : (0 : ℝ) < x := by linarith
  have hTx := ha₀ x hxa
  set T := ∫ w in Iic (-(x : ℝ)), w ^ 2 ∂Γ with hTdef
  set a : ℝ := 1 + x with ha
  have ha0 : 0 < a := by linarith
  -- the real drift inequality
  set g : ℝ → ℝ := fun w => Real.log (1 + max ((x : ℝ) + w) 0) with hg
  have hgnn : ∀ w, 0 ≤ g w := fun w => Real.log_nonneg (by linarith [le_max_right ((x : ℝ) + w) 0])
  have hgint : Integrable g Γ := ((integrable_const (x : ℝ)).add hW.abs).mono'
    ((Real.measurable_log.comp (measurable_const.add ((measurable_const.add measurable_id).max
      measurable_const)))).aestronglyMeasurable (Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hgnn w)]
        simp only [Pi.add_apply, hg]
        have h1 := Real.log_le_sub_one_of_pos (show 0 < 1 + max ((x : ℝ) + w) 0 by
          linarith [le_max_right ((x : ℝ) + w) 0])
        have h2 : max ((x : ℝ) + w) 0 ≤ x + |w| :=
          max_le (by linarith [le_abs_self w]) (by positivity)
        linarith)
  have hm1 : MeasurableSet (Ioi (-(x : ℝ))) := measurableSet_Ioi
  have hm2 : MeasurableSet (Ioo (-(x : ℝ)) 0) := measurableSet_Ioo
  set h : ℝ → ℝ := fun w => Real.log a + 1 / a * (Ioi (-(x : ℝ))).indicator (fun w => w) w -
    1 / (2 * a ^ 2) * (Ioo (-(x : ℝ)) 0).indicator (fun w => w ^ 2) w with hh
  have hhint : Integrable h Γ :=
    ((integrable_const _).add ((hW.indicator hm1).const_mul _)).sub
      ((hW2.indicator hm2).const_mul _)
  have hgh : ∀ w, g w ≤ h w := fun w => by
    simp only [hg, hh]
    by_cases hw : -(x : ℝ) < w
    · have hxw : 0 ≤ (x : ℝ) + w := by linarith
      rw [max_eq_left hxw, indicator_of_mem (show w ∈ Ioi (-(x : ℝ)) from hw)]
      have hu : -1 < w / a := by rw [lt_div_iff₀ ha0]; linarith
      have hsplit : Real.log (1 + (x + w)) = Real.log a + Real.log (1 + w / a) := by
        rw [← Real.log_mul ha0.ne' (ne_of_gt (by linarith))]
        congr 1; field_simp; ring
      rw [hsplit]
      have := log_one_add_le hu
      by_cases hw0 : w < 0
      · have hu0 : w / a < 0 := div_neg_of_neg_of_pos hw0 ha0
        simp only [hu0, ite_true, mul_one] at this
        rw [indicator_of_mem (show w ∈ Ioo (-(x : ℝ)) 0 from ⟨hw, hw0⟩)]
        have e : (w / a) ^ 2 / 2 = 1 / (2 * a ^ 2) * w ^ 2 := by field_simp
        have e2 : w / a = 1 / a * w := by ring
        linarith
      · have hu0 : ¬ w / a < 0 := fun h' => hw0 (by
          rcases div_neg_iff.1 h' with ⟨_, h2⟩ | ⟨h1, _⟩
          · linarith
          · exact h1)
        simp only [hu0, ite_false, mul_zero, sub_zero] at this
        rw [indicator_of_notMem (show w ∉ Ioo (-(x : ℝ)) 0 from fun h' => hw0 h'.2), mul_zero,
          sub_zero]
        have e2 : w / a = 1 / a * w := by ring
        linarith
    · have hxw : (x : ℝ) + w ≤ 0 := by linarith
      rw [max_eq_right hxw, add_zero, Real.log_one,
        indicator_of_notMem (show w ∉ Ioi (-(x : ℝ)) from hw),
        indicator_of_notMem (show w ∉ Ioo (-(x : ℝ)) 0 from fun h' => hw h'.1), mul_zero,
        mul_zero, add_zero, sub_zero]
      exact Real.log_nonneg (by linarith)
  -- the pieces of `∫ h`
  have hI1 : ∫ w in Ioi (-(x : ℝ)), w ∂Γ ≤ T / x := by
    have hcompl : Ioi (-(x : ℝ)) = (Iic (-(x : ℝ)))ᶜ := by ext; simp
    have hsum := integral_add_compl (measurableSet_Iic (a := -(x : ℝ))) hW
    rw [hβ, ← hcompl] at hsum
    have hle : -∫ w in Iic (-(x : ℝ)), w ∂Γ ≤ T / x := by
      rw [← integral_neg, hTdef, ← integral_div]
      refine setIntegral_mono_on hW.neg.integrableOn (hW2.div_const _).integrableOn
        measurableSet_Iic fun w hw => ?_
      simp only [mem_Iic] at hw
      rw [le_div_iff₀ hx0]
      nlinarith
    linarith
  have hI2 : ∫ w in Ioo (-(x : ℝ)) 0, w ^ 2 ∂Γ = c - T := by
    have hunion : Iio (0 : ℝ) = Iic (-(x : ℝ)) ∪ Ioo (-(x : ℝ)) 0 := by
      ext w; simp only [mem_Iio, mem_union, mem_Iic, mem_Ioo]
      constructor
      · intro h; by_cases hw : w ≤ -(x : ℝ)
        · exact Or.inl hw
        · exact Or.inr ⟨by linarith, h⟩
      · rintro (h | h)
        · linarith
        · exact h.2
    have hdisj : Disjoint (Iic (-(x : ℝ))) (Ioo (-(x : ℝ)) 0) :=
      Set.disjoint_left.2 fun w h1 h2 => by simp only [mem_Iic, mem_Ioo] at h1 h2; linarith
    rw [hc, hunion, setIntegral_union hdisj hm2 hW2.integrableOn hW2.integrableOn, hTdef]
    ring
  have hint_h : ∫ w, h w ∂Γ = Real.log a + 1 / a * ∫ w in Ioi (-(x : ℝ)), w ∂Γ -
      1 / (2 * a ^ 2) * ∫ w in Ioo (-(x : ℝ)) 0, w ^ 2 ∂Γ := by
    simp only [hh]
    have i1 : Integrable (fun w => Real.log a + 1 / a * (Ioi (-(x : ℝ))).indicator
        (fun w => w) w) Γ := (integrable_const _).add ((hW.indicator hm1).const_mul _)
    have i2 : Integrable (fun w => 1 / (2 * a ^ 2) * (Ioo (-(x : ℝ)) 0).indicator
        (fun w => w ^ 2) w) Γ := (hW2.indicator hm2).const_mul _
    have i3 : Integrable (fun _ : ℝ => Real.log a) Γ := integrable_const _
    have i4 : Integrable (fun w => 1 / a * (Ioi (-(x : ℝ))).indicator (fun w => w) w) Γ :=
      (hW.indicator hm1).const_mul _
    rw [integral_sub i1 i2, integral_add i3 i4, integral_const, integral_const_mul,
      integral_const_mul, integral_indicator hm1, integral_indicator hm2]
    simp
  have hdrift : ∫ w, g w ∂Γ ≤ Real.log a := by
    have h1 := integral_mono hgint hhint hgh
    rw [hint_h, hI2] at h1
    have h2 : 1 / a * ∫ w in Ioi (-(x : ℝ)), w ∂Γ ≤ 1 / a * (T / x) :=
      mul_le_mul_of_nonneg_left hI1 (by positivity)
    have h3 : 1 / a * (T / x) ≤ 2 * T / a ^ 2 := by
      have hT0 : 0 ≤ T := setIntegral_nonneg measurableSet_Iic fun w _ => sq_nonneg w
      rw [show 1 / a * (T / x) = T / (a * x) by field_simp,
        div_le_div_iff₀ (by positivity) (by positivity)]
      have : a ≤ 2 * x := by linarith
      have h5 := mul_le_mul_of_nonneg_left this (mul_nonneg hT0 ha0.le)
      nlinarith [h5]
    have h4 : 2 * T / a ^ 2 - 1 / (2 * a ^ 2) * (c - T) ≤ 0 := by
      rw [show 2 * T / a ^ 2 - 1 / (2 * a ^ 2) * (c - T) = (5 * T - c) / (2 * a ^ 2) by
        field_simp; ring]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    linarith
  -- back to the lintegral
  rw [drift_nonpos_iff, lintegral_halfLine Γ x (f := fun y => ((V y : ℝ≥0) : ℝ≥0∞))
    (measurable_coe_nnreal_ennreal.comp hVm)]
  have hcoe : ∀ w, ((V (Real.toNNReal ((x : ℝ) + w)) : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (g w) :=
    fun w => by
      rw [← ENNReal.ofReal_coe_nnreal, hVcoe, Real.coe_toNNReal']
  simp_rw [hcoe]
  rw [← ofReal_integral_eq_lintegral_ofReal hgint (Eventually.of_forall hgnn),
    ← ENNReal.ofReal_coe_nnreal, hVcoe]
  exact ENNReal.ofReal_le_ofReal hdrift

end MeynTweedie.HarrisRecurrence
