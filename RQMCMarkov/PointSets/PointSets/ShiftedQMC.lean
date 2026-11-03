/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PointSets.Unbiased
import PointSets.VanDerCorput

/-! # Randomly shifted QMC in one dimension

Post #1 says RQMC "happily happens to provide convergence of the estimator at least as fast as
QMC", and post #2 randomizes QMC sets by a random shift. The simplest such randomization is the
random shift modulo 1 (Cranley-Patterson 1976; L'Ecuyer 2016): `zᵢ = fract (xᵢ + U)` with
`U ~ Uniform[0,1)`. The law of `U` is `uniformIco = volume.restrict [0,1)` (from
`PointSets.MonteCarlo`). The marginal uniformity of each `zᵢ` is
`measurePreserving_fract_add` (in `Unbiased`).

**Results.**
* `integral_qmcEstimate_shiftMod`: the shifted estimator is unbiased, `E[Q(z)] = ∫₀¹ f`
  (a one-dimensional restatement of `integral_sampleMean_shiftMod1` in `qmcEstimate` notation).
* `localDiscrepancy_shiftMod_le`, `starDiscrepancy_shiftMod_le`: **deterministically, for every
  shift `u`, `D*ₙ(z) ≤ 2 D*ₙ(x)`**, since an interval `[0,t)` pulls back under the shift to one
  interval or the union of two intervals of `[0,1)`.
* `abs_shiftedError_le`: for every shift, `|Q(z) - ∫ f| ≤ 2 V(f) D*ₙ(x)` (Koksma).
* `integral_sq_shiftedError_le`, `sqrt_integral_sq_shiftedError_le`: the mean squared error of
  the randomly shifted estimator is at most `(2 V(f) D*ₙ(x))²`, and its root-mean-square error is
  at most `2 V(f) D*ₙ(x)`: RQMC by a random shift converges at least as fast as the Koksma bound
  of the QMC set it randomizes.
* `sqrt_integral_sq_shiftedError_vanDerCorput_le`, `tendsto_sqrt_mul_rmse_vanDerCorput`: for the
  randomly shifted van der Corput sequence, RMSE `≤ 4 V(f) (log n + 1)/n`, so `√n · RMSE → 0`,
  faster than MC's `σ/√n`.

**Correction (precise reading of "at least as fast as QMC").** The statement holds for the
worst-case (Koksma) error bounds and rates, with a factor `2`; it is false for the error on a
given integrand. `shiftedMidpoint_counterexample`: for the one-point midpoint rule `{1/2}` and
`f(x) = x`, the QMC error is `0` but the randomly shifted estimator has mean squared error
`1/12 > 0`.
-/

namespace RQMCMarkov.PointSets

open MeasureTheory Filter Topology

/-- The random shift modulo 1 of a point sequence: `zᵢ = fract (xᵢ + u)`. -/
noncomputable def shiftMod (x : ℕ → ℝ) (u : ℝ) : ℕ → ℝ := fun i => Int.fract (x i + u)

/-- Shifted points lie in `[0,1)`. -/
theorem shiftMod_inUnitIco (x : ℕ → ℝ) (u : ℝ) (n : ℕ) : InUnitIco (shiftMod x u) n :=
  fun _ _ => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- Only the fractional part of the shift matters. -/
theorem shiftMod_fract (x : ℕ → ℝ) (u : ℝ) : shiftMod x (Int.fract u) = shiftMod x u := by
  funext i
  unfold shiftMod
  rw [← Int.fract_add_intCast (x i + Int.fract u) ⌊u⌋, add_assoc, Int.fract_add_floor]

/-- The fractional part of `y ∈ [0,2)`: `y` if `y < 1`, else `y - 1`. -/
theorem fract_of_lt_one {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) : Int.fract y = y :=
  Int.fract_eq_self.mpr ⟨h0, h1⟩

/-- The fractional part of `y ∈ [1,2)` is `y - 1`. -/
theorem fract_of_one_le {y : ℝ} (h1 : 1 ≤ y) (h2 : y < 2) : Int.fract y = y - 1 := by
  rw [← Int.fract_sub_one]
  exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩

/-- Shifted count, case `t ≤ u`: `#{zᵢ < t} + #{xᵢ < 1 - u} = #{xᵢ < 1 - u + t}`. -/
theorem countBelow_shiftMod_of_le {x : ℕ → ℝ} {n : ℕ} (hx : InUnitIco x n) {u t : ℝ}
    (hu : u ∈ Set.Ico (0 : ℝ) 1) (ht0 : 0 ≤ t) (htu : t ≤ u) :
    countBelow (shiftMod x u) n t + countBelow x n (1 - u) = countBelow x n (1 - u + t) := by
  unfold countBelow
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hxi0 := (hx i (Finset.mem_range.mp hi)).1
  have hxi1 := (hx i (Finset.mem_range.mp hi)).2
  have hu0 := hu.1
  have hu1 := hu.2
  unfold shiftMod
  rcases lt_or_ge (x i + u) 1 with h | h
  · rw [fract_of_lt_one (by linarith) h]
    split_ifs <;> first | rfl | (exfalso; linarith)
  · rw [fract_of_one_le h (by linarith)]
    split_ifs <;> first | rfl | (exfalso; linarith)

/-- Shifted count, case `u < t ≤ 1`: `#{zᵢ < t} + #{xᵢ < 1 - u} = #{xᵢ < t - u} + n`. -/
theorem countBelow_shiftMod_of_lt {x : ℕ → ℝ} {n : ℕ} (hx : InUnitIco x n) {u t : ℝ}
    (hu : u ∈ Set.Ico (0 : ℝ) 1) (htu : u < t) (ht1 : t ≤ 1) :
    countBelow (shiftMod x u) n t + countBelow x n (1 - u) = countBelow x n (t - u) + n := by
  unfold countBelow
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  have hsum : ∑ i ∈ Finset.range n, ((if shiftMod x u i < t then 1 else 0) +
      (if x i < 1 - u then 1 else 0)) =
      ∑ i ∈ Finset.range n, ((if x i < t - u then 1 else 0) + 1) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hxi0 := (hx i (Finset.mem_range.mp hi)).1
    have hxi1 := (hx i (Finset.mem_range.mp hi)).2
    have hu0 := hu.1
    have hu1 := hu.2
    unfold shiftMod
    rcases lt_or_ge (x i + u) 1 with h | h
    · rw [fract_of_lt_one (by linarith) h]
      split_ifs <;> first | rfl | (exfalso; linarith)
    · rw [fract_of_one_le h (by linarith)]
      split_ifs <;> first | rfl | (exfalso; linarith)
  rw [hsum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

/-- The signed local discrepancy `#{xᵢ < a}/n - a` at `a ∈ [0,1]` is at most `D*ₙ` in absolute
value. -/
theorem abs_countBelow_div_sub_le (x : ℕ → ℝ) (n : ℕ) {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    |(countBelow x n a : ℝ) / n - a| ≤ starDiscrepancy x n :=
  localDiscrepancy_le_starDiscrepancy x n ha

/-- **The shift at most doubles the local discrepancy**: for `u ∈ [0,1)` and `t ∈ [0,1]`,
`|#{zᵢ < t}/n - t| ≤ 2 D*ₙ(x)`. -/
theorem localDiscrepancy_shiftMod_le {x : ℕ → ℝ} {n : ℕ} (hx : InUnitIco x n) {u t : ℝ}
    (hu : u ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    localDiscrepancy (shiftMod x u) n t ≤ 2 * starDiscrepancy x n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h1 := localDiscrepancy_le_starDiscrepancy x 0 (Set.right_mem_Icc.mpr zero_le_one)
    unfold localDiscrepancy at h1 ⊢
    rw [Nat.cast_zero, div_zero, zero_sub, abs_neg, abs_one] at h1
    rw [Nat.cast_zero, div_zero, zero_sub, abs_neg, abs_of_nonneg ht.1]
    linarith [ht.2]
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  unfold localDiscrepancy
  have ha : 1 - u ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hA := abs_countBelow_div_sub_le x n ha
  rcases le_or_gt t u with htu | htu
  · have hcount := countBelow_shiftMod_of_le hx hu ht.1 htu
    have hcR : (countBelow (shiftMod x u) n t : ℝ) =
        countBelow x n (1 - u + t) - countBelow x n (1 - u) := by
      rw [← hcount, Nat.cast_add]
      ring
    have hb : 1 - u + t ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hu.2, ht.1], by linarith⟩
    have hB := abs_countBelow_div_sub_le x n hb
    have heq : (countBelow (shiftMod x u) n t : ℝ) / n - t =
        ((countBelow x n (1 - u + t) : ℝ) / n - (1 - u + t)) -
          ((countBelow x n (1 - u) : ℝ) / n - (1 - u)) := by
      rw [hcR, sub_div]
      ring
    rw [heq]
    exact (abs_sub _ _).trans (by linarith)
  · have hcount := countBelow_shiftMod_of_lt hx hu htu ht.2
    have hcR : (countBelow (shiftMod x u) n t : ℝ) =
        countBelow x n (t - u) + n - countBelow x n (1 - u) := by
      rw [← Nat.cast_add, ← hcount, Nat.cast_add]
      ring
    have hb : t - u ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [hu.1, ht.2]⟩
    have hB := abs_countBelow_div_sub_le x n hb
    have heq : (countBelow (shiftMod x u) n t : ℝ) / n - t =
        ((countBelow x n (t - u) : ℝ) / n - (t - u)) -
          ((countBelow x n (1 - u) : ℝ) / n - (1 - u)) := by
      rw [hcR, sub_div, add_div, div_self hpos.ne']
      ring
    rw [heq]
    exact (abs_sub _ _).trans (by linarith)

/-- **A random shift at most doubles the star discrepancy**: for every shift `u ∈ ℝ` and every
point set in `[0,1)`, `D*ₙ(fract (x + u)) ≤ 2 D*ₙ(x)`. -/
theorem starDiscrepancy_shiftMod_le {x : ℕ → ℝ} {n : ℕ} (hx : InUnitIco x n) (u : ℝ) :
    starDiscrepancy (shiftMod x u) n ≤ 2 * starDiscrepancy x n := by
  rw [← shiftMod_fract x u]
  exact starDiscrepancy_le_of_forall _ _ fun t ht =>
    localDiscrepancy_shiftMod_le hx ⟨Int.fract_nonneg u, Int.fract_lt_one u⟩ ht

/-- **Koksma for every shift**: `|Q(fract (x + u)) - ∫₀¹ f| ≤ 2 V(f) D*ₙ(x)`. -/
theorem abs_shiftedError_le {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc 0 1)) {x : ℕ → ℝ}
    {n : ℕ} (hx : InUnitIco x n) (hn : 0 < n) (u : ℝ) :
    |qmcEstimate f (shiftMod x u) n - ∫ t in (0 : ℝ)..1, f t| ≤
      2 * totalVariation f * starDiscrepancy x n := by
  have h := koksma_boundedVariationOn hf (shiftMod_inUnitIco x u n) hn
  have hV : 0 ≤ totalVariation f := ENNReal.toReal_nonneg
  calc _ ≤ _ := h
    _ ≤ totalVariation f * (2 * starDiscrepancy x n) :=
        mul_le_mul_of_nonneg_left (starDiscrepancy_shiftMod_le hx u) hV
    _ = _ := by ring

/-- **Unbiasedness of the randomly shifted estimator** (one-dimensional `qmcEstimate` form):
for `U ~ Uniform[0,1)` and `f` integrable on `[0,1]`, `E[(1/n) ∑ f(fract (xᵢ + U))] = ∫₀¹ f`,
for any points `x` and `n ≥ 1`. -/
theorem integral_qmcEstimate_shiftMod {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 1)
    (x : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    ∫ u, qmcEstimate f (shiftMod x u) n ∂uniformIco = ∫ t in (0 : ℝ)..1, f t := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hfU : Integrable f uniformIco := by
    rw [uniformIco_eq_restrict_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hf
  have hcomp : ∀ c : ℝ, ∫ u, f (Int.fract (c + u)) ∂uniformIco = ∫ y, f y ∂uniformIco := by
    intro c
    have hmp := measurePreserving_fract_add c
    rw [← integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hfU.1),
      hmp.map_eq]
  have hint : ∀ i ∈ Finset.range n, Integrable (fun u => f (shiftMod x u i)) uniformIco :=
    fun i _ => (measurePreserving_fract_add (x i)).integrable_comp_of_integrable hfU
  unfold qmcEstimate
  rw [integral_div, integral_finsetSum _ hint]
  have hsum : ∑ i ∈ Finset.range n, ∫ u, f (shiftMod x u i) ∂uniformIco =
      ∑ _i ∈ Finset.range n, ∫ y, f y ∂uniformIco := by
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold shiftMod
    rw [← hcomp (x i)]
  rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_cancel_left₀ _ hpos.ne',
    intervalIntegral.integral_of_le zero_le_one, uniformIco_eq_restrict_Ioc]

/-- **Mean squared error of randomly shifted QMC.** For `f` of bounded variation, `n ≥ 1`
points in `[0,1)` and `U ~ Uniform[0,1)`:
`E[(Q(fract (x + U)) - ∫₀¹ f)²] ≤ (2 V(f) D*ₙ(x))²`. -/
theorem integral_sq_shiftedError_le {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc 0 1))
    {x : ℕ → ℝ} {n : ℕ} (hx : InUnitIco x n) (hn : 0 < n) :
    ∫ u, (qmcEstimate f (shiftMod x u) n - ∫ t in (0 : ℝ)..1, f t) ^ 2 ∂uniformIco ≤
      (2 * totalVariation f * starDiscrepancy x n) ^ 2 := by
  have := isProbabilityMeasure_uniformIco
  have hbound : ∀ᵐ u ∂uniformIco,
      ‖(qmcEstimate f (shiftMod x u) n - ∫ t in (0 : ℝ)..1, f t) ^ 2‖ ≤
        (2 * totalVariation f * starDiscrepancy x n) ^ 2 := by
    refine Eventually.of_forall fun u => ?_
    rw [Real.norm_eq_abs, abs_pow, ← sq_abs (2 * totalVariation f * starDiscrepancy x n)]
    exact pow_le_pow_left₀ (abs_nonneg _)
      ((abs_shiftedError_le hf hx hn u).trans (le_abs_self _)) 2
  have h := norm_integral_le_of_norm_le_const hbound
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

/-- **Root-mean-square error of randomly shifted QMC**: `√E[(Q - ∫ f)²] ≤ 2 V(f) D*ₙ(x)`, i.e.
RQMC by a random shift converges at least as fast as the Koksma bound of the QMC set. -/
theorem sqrt_integral_sq_shiftedError_le {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc 0 1))
    {x : ℕ → ℝ} {n : ℕ} (hx : InUnitIco x n) (hn : 0 < n) :
    Real.sqrt (∫ u, (qmcEstimate f (shiftMod x u) n - ∫ t in (0 : ℝ)..1, f t) ^ 2 ∂uniformIco) ≤
      2 * totalVariation f * starDiscrepancy x n := by
  have hV : 0 ≤ totalVariation f := ENNReal.toReal_nonneg
  have hD := starDiscrepancy_nonneg x n
  calc _ ≤ Real.sqrt ((2 * totalVariation f * starDiscrepancy x n) ^ 2) :=
        Real.sqrt_le_sqrt (integral_sq_shiftedError_le hf hx hn)
    _ = _ := Real.sqrt_sq (by positivity)

/-- **Randomly shifted van der Corput sequence**: RMSE `≤ 4 V(f) (log n + 1)/n`. -/
theorem sqrt_integral_sq_shiftedError_vanDerCorput_le {f : ℝ → ℝ}
    (hf : BoundedVariationOn f (Set.Icc 0 1)) {n : ℕ} (hn : 0 < n) :
    Real.sqrt (∫ u, (qmcEstimate f (shiftMod vanDerCorput u) n - ∫ t in (0 : ℝ)..1, f t) ^ 2
      ∂uniformIco) ≤ 2 * totalVariation f * (2 * (Real.log n + 1) / n) := by
  have hV : 0 ≤ totalVariation f := ENNReal.toReal_nonneg
  exact (sqrt_integral_sq_shiftedError_le hf (vanDerCorput_inUnitIco n) hn).trans
    (mul_le_mul_of_nonneg_left (starDiscrepancy_vanDerCorput_le_log hn) (by positivity))

/-- **Randomly shifted van der Corput beats MC**: `√n · RMSE → 0`, i.e. the RMSE is
`o(n^{-1/2})`, while MC has RMSE exactly `σ(f)/√n`. -/
theorem tendsto_sqrt_mul_rmse_vanDerCorput {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc 0 1)) :
    Tendsto (fun n : ℕ => Real.sqrt n * Real.sqrt (∫ u, (qmcEstimate f (shiftMod vanDerCorput u) n -
      ∫ t in (0 : ℝ)..1, f t) ^ 2 ∂uniformIco)) atTop (𝓝 0) := by
  have h := tendsto_sqrt_mul_vanDerCorput_bound.const_mul (2 * totalVariation f)
  rw [mul_zero] at h
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ h
  filter_upwards [eventually_gt_atTop 0] with n hn
  have := mul_le_mul_of_nonneg_left (sqrt_integral_sq_shiftedError_vanDerCorput_le hf hn)
    (Real.sqrt_nonneg (n : ℝ))
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **Counterexample: RQMC need not beat QMC on a given integrand.** For the one-point midpoint
rule `{1/2}` and `f(x) = x`, the QMC error is `0`, while the randomly shifted estimator
`fract (1/2 + U)` has mean squared error `1/12`. -/
theorem shiftedMidpoint_counterexample :
    qmcEstimate (fun t => t) (midpointRule 1) 1 - ∫ t in (0 : ℝ)..1, t = 0 ∧
      ∫ u, (qmcEstimate (fun t => t) (shiftMod (midpointRule 1) u) 1 -
        ∫ t in (0 : ℝ)..1, t) ^ 2 ∂uniformIco = 1 / 12 := by
  have hI : ∫ t in (0 : ℝ)..1, t = 1 / 2 := by
    rw [integral_id]
    norm_num
  have hQ : ∀ y : ℕ → ℝ, qmcEstimate (fun t => t) y 1 = y 0 := by
    intro y
    unfold qmcEstimate
    rw [Finset.sum_range_one, Nat.cast_one, div_one]
  have hm : midpointRule 1 0 = 1 / 2 := by
    unfold midpointRule
    norm_num
  refine ⟨by rw [hQ, hm, hI, sub_self], ?_⟩
  simp only [hQ, hI]
  have hmp := measurePreserving_fract_add (1 / 2)
  have hcont : Continuous fun y : ℝ => (y - 1 / 2) ^ 2 := by fun_prop
  have hcomp : ∫ u, (Int.fract (1 / 2 + u) - 1 / 2) ^ 2 ∂uniformIco =
      ∫ y, (y - 1 / 2) ^ 2 ∂uniformIco := by
    have h := integral_map (μ := uniformIco) hmp.measurable.aemeasurable
      (f := fun y : ℝ => (y - 1 / 2) ^ 2) (by rw [hmp.map_eq]; exact hcont.aestronglyMeasurable)
    rw [hmp.map_eq] at h
    exact h.symm
  have hval : ∫ y, (y - 1 / 2) ^ 2 ∂uniformIco = 1 / 12 := by
    rw [uniformIco_eq_restrict_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_comp_sub_right (fun y : ℝ => y ^ 2) (1 / 2), integral_pow]
    norm_num
  have hshift : ∀ u, shiftMod (midpointRule 1) u 0 = Int.fract (1 / 2 + u) := by
    intro u
    unfold shiftMod
    rw [hm]
  simp only [hshift]
  rw [hcomp, hval]

end RQMCMarkov.PointSets
