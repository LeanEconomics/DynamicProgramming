/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PointSets.Stratified
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The randomly shifted lattice rule is not asymptotically normal (post #2)

Post #2: "If we use an RQMC estimator with a randomly-shifted lattice rule, the limiting
distribution as `n → ∞` is usually a spline, not a normal distribution" (L'Ecuyer, Munger and
Tuffin 2010). Reading, in one dimension: the rank-1 lattice with generator `1`, `{i/n : i < n}`,
randomly shifted, is the common-shift stratified rule `μ̂ₙ(U) = (1/n) Σᵢ f((i + U)/n)` with
`U ~ U[0,1)` (as point SETS, `{fract (i/n + U)} = {(i + fract (n U))/n}`; we work with the labelling
`(i + U)/n`, which makes the convergence below almost sure; `ShiftLimitLattice` proves the
identification and transfers the results to the lattice labelling).

## Main results

* `scaled_error_id`: for `f(x) = x`, `n (μ̂ₙ(u) − 1/2) = u − 1/2` EXACTLY, for every `n ≥ 1` and
  every `u`; `hasLaw_scaled_error_id`: so the scaled error has law `U[−1/2, 1/2)` for every `n`.
* `cell_error_le`: on one cell `[a, a + h]`, for `C¹` `f` whose derivative varies by at most `ε`,
  `|f(a + u h) − (1/h)∫ₐ^{a+h} f − (u − 1/2)(f(a + h) − f(a))| ≤ 3 ε h`.
* `tendsto_scaled_error`: for `f` that is `C¹` on `[0,1]` and every `u ∈ [0,1]`,
  `n (μ̂ₙ(u) − ∫₀¹ f) → (f(1) − f(0)) (u − 1/2)`.
* `ae_tendsto_scaled_error`, `tendstoInDistribution_scaled_error`: hence almost surely, and in
  distribution, `n (μ̂ₙ(U) − μ) → (f(1) − f(0)) (U − 1/2)`.
* `map_mul_sub_half_uniformIco`: the limit law is uniform on `[−|c|/2, |c|/2]`, `c = f(1) − f(0)`,
  with density `1/|c|` — a degree-0 spline — whenever `f(1) ≠ f(0)` (a point mass at 0 otherwise).
* `ne_gaussianReal_of_measure_Ioi_eq_zero`: a law with bounded support is not a Gaussian
  `gaussianReal m v` with `v ≠ 0`; `limit_law_ne_gaussianReal` and
  `not_tendstoInDistribution_scaled_error_gaussian`: the scaled error `n (μ̂ₙ − μ)` does not
  converge in distribution to any non-degenerate normal law.
* `tendsto_sqrt_scaled_error`, `ae_tendsto_sqrt_scaled_error`,
  `not_tendstoInDistribution_sqrt_scaled_error_gaussian`: at the MC scale `√n`,
  `√n (μ̂ₙ − μ) → 0` almost surely, so the estimator is not asymptotically normal at the `√n`
  scale either (contrast `tendstoInDistribution_sampleMean_iid` for MC).

**Hypotheses.** `C¹` on `[0,1]` is `∀ x ∈ [0,1], HasDerivWithinAt f (f' x) [0,1] x` with `f'`
continuous on `[0,1]`. The random statements also assume `f` measurable (`f` is otherwise
unconstrained outside `[0,1]`).

**Precision.** "Usually a spline": in one dimension with the generator-1 lattice the limit is
exactly the uniform law (degree-0 spline) for every `C¹` `f` with `f(1) ≠ f(0)`, and the point mass
at `0` (a degenerate law, still not a non-degenerate normal) when `f(1) = f(0)` — then the error is
`o(1/n)` and a finer scale is needed. Owen scrambling's CLT (Loh 2003) is not formalised here.
-/

namespace RQMCMarkov.PointSets

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `∫ f dU[0,1) = ∫₀¹ f`. -/
theorem integral_uniformIco_eq_intervalIntegral (f : ℝ → ℝ) :
    ∫ x, f x ∂uniformIco = ∫ x in (0 : ℝ)..1, f x := by
  rw [uniformIco_eq_restrict_Ioc, intervalIntegral.integral_of_le zero_le_one]

/-- `Σ_{i<n} i = n (n − 1)/2`, in `ℝ`. -/
theorem sum_range_natCast (n : ℕ) : ∑ i ∈ Finset.range n, (i : ℝ) = n * (n - 1) / 2 := by
  induction n with
  | zero => rw [Finset.sum_range_zero, Nat.cast_zero, zero_mul, zero_div]
  | succ k ih =>
      rw [Finset.sum_range_succ, ih, Nat.cast_succ]
      ring

/-- **The scaled error for `f(x) = x` is exactly `u − 1/2`**: for every `n ≥ 1` and every `u`,
`n ((1/n) Σᵢ (i + u)/n − 1/2) = u − 1/2`. -/
theorem scaled_error_id {n : ℕ} (hn : n ≠ 0) (u : ℝ) :
    (n : ℝ) * (sampleMean n id (fun i ↦ stratumMap n i u) - 1 / 2) = u - 1 / 2 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  unfold sampleMean
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ id (stratumMap n k u)) n]
  simp only [id, stratumMap]
  rw [← Finset.sum_div, Finset.sum_add_distrib, sum_range_natCast, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  field_simp
  ring

/-- The law of `U − 1/2`, `U ~ U[0,1)`, is the uniform law on `[−1/2, 1/2)`. -/
theorem map_sub_half_uniformIco :
    uniformIco.map (fun u ↦ u - 1 / 2) = volume.restrict (Ico (-(1 / 2) : ℝ) (1 / 2)) := by
  have hfun : (fun u : ℝ ↦ u - 1 / 2) = fun u ↦ -(1 / 2) + u := by
    funext u
    ring
  have hpre : (fun u : ℝ ↦ -(1 / 2) + u) ⁻¹' Ico (-(1 / 2)) (1 / 2) = Ico 0 1 := by
    ext u
    simp only [mem_preimage, mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  change (volume.restrict (Ico (0 : ℝ) 1)).map _ = _
  rw [hfun, ← hpre, ← Measure.restrict_map (measurable_const_add _) measurableSet_Ico,
    map_add_left_eq_self]

/-- **The scaled error for `f(x) = x` is uniform on `[−1/2, 1/2)` for every `n ≥ 1`**: with
`U ~ U[0,1)`, `n (μ̂ₙ(U) − 1/2) ~ U[−1/2, 1/2)`. No normal limit is possible. -/
theorem hasLaw_scaled_error_id {n : ℕ} (hn : n ≠ 0) {P : Measure Ω} {U : Ω → ℝ}
    (hU : HasLaw U uniformIco P) :
    HasLaw (fun ω ↦ (n : ℝ) * (sampleMean n id (fun i ↦ stratumMap n i (U ω)) - 1 / 2))
      (volume.restrict (Ico (-(1 / 2) : ℝ) (1 / 2))) P := by
  have hfun : (fun ω ↦ (n : ℝ) * (sampleMean n id (fun i ↦ stratumMap n i (U ω)) - 1 / 2)) =
      (fun u ↦ u - 1 / 2) ∘ U := by
    funext ω
    exact scaled_error_id hn (U ω)
  rw [hfun, ← map_sub_half_uniformIco]
  exact (hasLaw_map (measurable_sub_const _).aemeasurable).comp hU

/-- **Error on one cell.** If `f` is differentiable on `[a, a + h]` (`h > 0`) with
`|f'(x) − f'(a)| ≤ ε` there, then for `u ∈ [0,1]`
`|f(a + u h) − (1/h) ∫ₐ^{a+h} f − (u − 1/2)(f(a + h) − f(a))| ≤ 3 ε h`. -/
theorem cell_error_le {f f' : ℝ → ℝ} {a h ε : ℝ} (hh : 0 < h)
    (hf : ∀ x ∈ Icc a (a + h), HasDerivWithinAt f (f' x) (Icc a (a + h)) x)
    (hε : ∀ x ∈ Icc a (a + h), |f' x - f' a| ≤ ε) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    |f (a + u * h) - h⁻¹ * (∫ x in a..a + h, f x) - (u - 1 / 2) * (f (a + h) - f a)| ≤
      3 * ε * h := by
  have hah : a ≤ a + h := by linarith
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hε a (left_mem_Icc.2 hah))
  set g : ℝ → ℝ := fun x ↦ f x - f' a * x with hg
  have hgd : ∀ x ∈ Icc a (a + h), HasDerivWithinAt g (f' x - f' a) (Icc a (a + h)) x := by
    intro x hx
    exact ((hf x hx).sub ((hasDerivWithinAt_id x _).const_mul (f' a))).congr_deriv (by ring)
  have hgc : ContinuousOn g (Icc a (a + h)) := fun x hx ↦ (hgd x hx).continuousWithinAt
  have hmvt : ∀ y ∈ Icc a (a + h), |g y - g a| ≤ ε * h := by
    intro y hy
    have := norm_image_sub_le_of_norm_deriv_le_segment' hgd
      (fun x hx ↦ by rw [Real.norm_eq_abs]; exact hε x (Ico_subset_Icc_self hx)) y hy
    rw [Real.norm_eq_abs] at this
    exact this.trans (mul_le_mul_of_nonneg_left (by linarith [hy.2]) hε0)
  have huIcc : uIcc a (a + h) = Icc a (a + h) := uIcc_of_le hah
  have hint1 : IntervalIntegrable (fun x ↦ g x - g a) volume a (a + h) :=
    ContinuousOn.intervalIntegrable (by rw [huIcc]; exact hgc.sub continuousOn_const)
  have hint2 : IntervalIntegrable (fun x ↦ g a + f' a * x) volume a (a + h) :=
    (continuous_const.add (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hfx : ∀ x, f x = (g x - g a) + (g a + f' a * x) := fun x ↦ by
    simp only [hg]
    ring
  have hI : (∫ x in a..a + h, f x) =
      (∫ x in a..a + h, (g x - g a)) + (g a * h + f' a * (((a + h) ^ 2 - a ^ 2) / 2)) := by
    rw [intervalIntegral.integral_congr (fun x _ ↦ hfx x),
      intervalIntegral.integral_add hint1 hint2,
      intervalIntegral.integral_add (f := fun _ ↦ g a) (g := fun x ↦ f' a * x)
        intervalIntegrable_const ((continuous_const.mul continuous_id).intervalIntegrable _ _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id,
      smul_eq_mul]
    ring
  set I := ∫ x in a..a + h, (g x - g a) with hIdef
  have hIb : |I| ≤ ε * h * h := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := a + h)
      (f := fun x ↦ g x - g a) (C := ε * h) (fun x hx ↦ by
        rw [Real.norm_eq_abs]
        rw [uIoc_of_le hah] at hx
        exact hmvt x (Ioc_subset_Icc_self hx))
    rw [Real.norm_eq_abs, add_sub_cancel_left, abs_of_pos hh] at this
    rw [hIdef]
    exact this
  have hE : f (a + u * h) - h⁻¹ * (∫ x in a..a + h, f x) - (u - 1 / 2) * (f (a + h) - f a) =
      (g (a + u * h) - g a) - h⁻¹ * I - (u - 1 / 2) * (g (a + h) - g a) := by
    rw [hI]
    simp only [hg]
    field_simp
    ring
  rw [hE]
  have hu' : a + u * h ∈ Icc a (a + h) := ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩
  have h1 := abs_le.1 (hmvt _ hu')
  have h2 : |h⁻¹ * I| ≤ ε * h := by
    rw [abs_mul, abs_inv, abs_of_pos hh]
    calc h⁻¹ * |I| ≤ h⁻¹ * (ε * h * h) := mul_le_mul_of_nonneg_left hIb (inv_nonneg.2 hh.le)
      _ = ε * h := by field_simp
  have h3 : |(u - 1 / 2) * (g (a + h) - g a)| ≤ ε * h := by
    rw [abs_mul]
    have hu2 : |u - 1 / 2| ≤ 1 := abs_le.2 ⟨by linarith [hu.1], by linarith [hu.2]⟩
    calc |u - 1 / 2| * |g (a + h) - g a| ≤ 1 * (ε * h) :=
          mul_le_mul hu2 (hmvt _ (right_mem_Icc.2 hah)) (abs_nonneg _) zero_le_one
      _ = ε * h := one_mul _
  have h2' := abs_le.1 h2
  have h3' := abs_le.1 h3
  exact abs_le.2 ⟨by linarith [h1.1, h2'.2, h3'.2], by linarith [h1.2, h2'.1, h3'.1]⟩

/-- **The scaled error of the randomly shifted lattice converges** (L'Ecuyer–Munger–Tuffin
2010, generator `1`, one dimension): if `f` is `C¹` on `[0,1]`, then for every `u ∈ [0,1]`,
`n ((1/n) Σᵢ f((i + u)/n) − ∫₀¹ f) → (f(1) − f(0)) (u − 1/2)` as `n → ∞`. -/
theorem tendsto_scaled_error {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) *
        (sampleMean n f (fun i ↦ stratumMap n i u) - ∫ x in (0 : ℝ)..1, f x))
      atTop (𝓝 ((f 1 - f 0) * (u - 1 / 2))) := by
  have hcont : ContinuousOn f (Icc 0 1) := fun x hx ↦ (hf x hx).continuousWithinAt
  have huc : UniformContinuousOn f' (Icc 0 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf'
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.1 huc (ε / 4) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  refine ⟨N + 1, fun n hn ↦ ?_⟩
  have hnN : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hnz : n ≠ 0 := by
    rintro rfl
    rw [Nat.cast_zero] at hn0
    exact lt_irrefl 0 hn0
  set h : ℝ := 1 / n with hhdef
  have hh : 0 < h := by positivity
  have hhδ : h < δ := by
    rw [hhdef, div_lt_iff₀ hn0]
    rw [div_lt_iff₀ hδ] at hN
    nlinarith
  set a : ℕ → ℝ := fun k ↦ (k : ℝ) / n with hadef
  have ha : ∀ k : ℕ, a k + h = a (k + 1) := by
    intro k
    simp only [hadef, hhdef]
    push_cast
    ring
  have ha0 : a 0 = 0 := by simp only [hadef, Nat.cast_zero, zero_div]
  have han : a n = 1 := by simp only [hadef]; exact div_self hn0.ne'
  have hcell : ∀ k < n, Icc (a k) (a k + h) ⊆ Icc 0 1 := by
    intro k hk x hx
    have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
    have hak : 0 ≤ a k := by simp only [hadef]; positivity
    have hak1 : a k + h ≤ 1 := by
      rw [ha k, hadef]
      simp only
      rw [div_le_one hn0]
      push_cast
      exact hk'
    exact ⟨hak.trans hx.1, hx.2.trans hak1⟩
  -- the sample mean, the integral and the telescoping sum, cell by cell
  have hsumf : (n : ℝ) * sampleMean n f (fun i ↦ stratumMap n i u) =
      ∑ k ∈ Finset.range n, f (a k + u * h) := by
    unfold sampleMean
    rw [← mul_assoc, mul_inv_cancel₀ hn0.ne', one_mul,
      Fin.sum_univ_eq_sum_range (fun k ↦ f (stratumMap n k u)) n]
    refine Finset.sum_congr rfl (fun k _ ↦ ?_)
    congr 1
    simp only [stratumMap, hadef, hhdef]
    ring
  have hint : (∫ x in (0 : ℝ)..1, f x) = ∑ k ∈ Finset.range n, ∫ x in a k..a k + h, f x := by
    have hii : ∀ k < n, IntervalIntegrable f volume (a k) (a (k + 1)) := by
      intro k hk
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le (by rw [← ha k]; linarith), ← ha k]
      exact hcont.mono (hcell k hk)
    rw [← ha0, ← han, ← intervalIntegral.sum_integral_adjacent_intervals hii]
    refine Finset.sum_congr rfl (fun k _ ↦ ?_)
    rw [ha k]
  have htel : ∑ k ∈ Finset.range n, (f (a k + h) - f (a k)) = f 1 - f 0 := by
    rw [Finset.sum_congr rfl (fun k _ ↦ by rw [ha k]),
      Finset.sum_range_sub (fun k ↦ f (a k)) n, han, ha0]
  have hid : (n : ℝ) * (sampleMean n f (fun i ↦ stratumMap n i u) - ∫ x in (0 : ℝ)..1, f x) -
      (f 1 - f 0) * (u - 1 / 2) = ∑ k ∈ Finset.range n,
        (f (a k + u * h) - h⁻¹ * (∫ x in a k..a k + h, f x) -
          (u - 1 / 2) * (f (a k + h) - f (a k))) := by
    have hhinv : h⁻¹ = n := by rw [hhdef, one_div, inv_inv]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← hsumf, ← hint, htel, hhinv]
    ring
  -- each cell contributes at most `3 (ε/4) h`
  have hbound : ∀ k ∈ Finset.range n, |f (a k + u * h) - h⁻¹ * (∫ x in a k..a k + h, f x) -
      (u - 1 / 2) * (f (a k + h) - f (a k))| ≤ 3 * (ε / 4) * h := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    have hsub := hcell k hk'
    refine cell_error_le hh (fun x hx ↦ (hf x (hsub hx)).mono hsub) (fun x hx ↦ ?_) hu
    have hdist : dist x (a k) < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hx.1])]
      linarith [hx.2]
    exact (hδf x (hsub hx) (a k) (hsub (left_mem_Icc.2 (by linarith))) hdist).le
  rw [Real.dist_eq, hid]
  calc |∑ k ∈ Finset.range n, (f (a k + u * h) - h⁻¹ * (∫ x in a k..a k + h, f x) -
          (u - 1 / 2) * (f (a k + h) - f (a k)))|
      ≤ ∑ k ∈ Finset.range n, |f (a k + u * h) - h⁻¹ * (∫ x in a k..a k + h, f x) -
          (u - 1 / 2) * (f (a k + h) - f (a k))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range n, 3 * (ε / 4) * h := Finset.sum_le_sum hbound
    _ = 3 * ε / 4 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hhdef]
        field_simp
    _ < ε := by linarith

/-- A uniform draw lies in `[0,1)` almost surely. -/
theorem ae_mem_Ico_of_hasLaw {P : Measure Ω} {U : Ω → ℝ} (hU : HasLaw U uniformIco P) :
    ∀ᵐ ω ∂P, U ω ∈ Ico (0 : ℝ) 1 := by
  have h : ∀ᵐ x ∂(P.map U), x ∈ Ico (0 : ℝ) 1 := by
    rw [hU.map_eq]
    exact ae_restrict_mem measurableSet_Ico
  exact ae_of_ae_map hU.aemeasurable h

/-- The common-shift estimate is a measurable function of the shift, for measurable `f`. -/
theorem measurable_sampleMean_stratumMap {f : ℝ → ℝ} (hfm : Measurable f) (n : ℕ) :
    Measurable fun u ↦ sampleMean n f (fun i ↦ stratumMap n i u) := by
  change Measurable fun u ↦ (n : ℝ)⁻¹ * ∑ i : Fin n, f (stratumMap n i u)
  refine Measurable.const_mul ?_ _
  exact Finset.measurable_fun_sum _ (fun i _ ↦ (hfm.comp (measurable_stratumMap n i) :))

/-- **Almost sure convergence of the scaled error** (L'Ecuyer–Munger–Tuffin 2010, one
dimension, generator `1`): for `f` `C¹` on `[0,1]` and `U ~ U[0,1)`,
`n (μ̂ₙ(U) − ∫₀¹ f) → (f(1) − f(0)) (U − 1/2)` almost surely. -/
theorem ae_tendsto_scaled_error {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) {P : Measure Ω} {U : Ω → ℝ} (hU : HasLaw U uniformIco P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ (n : ℝ) *
        (sampleMean n f (fun i ↦ stratumMap n i (U ω)) - ∫ x in (0 : ℝ)..1, f x))
      atTop (𝓝 ((f 1 - f 0) * (U ω - 1 / 2))) := by
  filter_upwards [ae_mem_Ico_of_hasLaw hU] with ω hω
  exact tendsto_scaled_error hf hf' (Ico_subset_Icc_self hω)

/-- **Convergence in distribution of the scaled error**: for measurable `f`, `C¹` on `[0,1]`,
`n (μ̂ₙ(U) − ∫₀¹ f) ⇒ (f(1) − f(0)) (U − 1/2)`. -/
theorem tendstoInDistribution_scaled_error {f f' : ℝ → ℝ} (hfm : Measurable f)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) {P : Measure Ω} [IsProbabilityMeasure P] {U : Ω → ℝ}
    (hU : HasLaw U uniformIco P) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (n : ℝ) *
        (sampleMean n f (fun i ↦ stratumMap n i (U ω)) - ∫ x in (0 : ℝ)..1, f x))
      atTop (fun ω ↦ (f 1 - f 0) * (U ω - 1 / 2)) (fun _ ↦ P) P :=
  tendstoInDistribution_of_ae_tendsto
    (fun n ↦ (((measurable_sampleMean_stratumMap hfm n).sub_const _).const_mul _).comp_aemeasurable
      hU.aemeasurable)
    (((measurable_id'.sub_const _).const_mul _).comp_aemeasurable hU.aemeasurable)
    (ae_tendsto_scaled_error hf hf' hU)

/-- **The limit law is uniform** (a degree-0 spline): for `c ≠ 0`, the law of `c (U − 1/2)`,
`U ~ U[0,1)`, is the uniform law on `[−|c|/2, |c|/2]`, with density `1/|c|`. -/
theorem map_mul_sub_half_uniformIco {c : ℝ} (hc : c ≠ 0) :
    uniformIco.map (fun u ↦ c * (u - 1 / 2)) =
      ENNReal.ofReal |c|⁻¹ • volume.restrict (Icc (-(|c| / 2)) (|c| / 2)) := by
  have hcpos : 0 < |c| := abs_pos.2 hc
  have hcomp : (fun u : ℝ ↦ c * (u - 1 / 2)) = (fun x ↦ c * x) ∘ (fun u ↦ u - 1 / 2) := rfl
  have hpre : (fun x : ℝ ↦ c * x) ⁻¹' Icc (-(|c| / 2)) (|c| / 2) = Icc (-(1 / 2)) (1 / 2) := by
    ext x
    simp only [mem_preimage, mem_Icc]
    rw [← abs_le, ← abs_le, abs_mul]
    constructor
    · intro h
      have h' : |c| * |x| ≤ |c| * (1 / 2) := by linarith
      exact le_of_mul_le_mul_left h' hcpos
    · intro h
      nlinarith
  rw [hcomp, ← Measure.map_map (measurable_const_mul c) (measurable_sub_const _),
    map_sub_half_uniformIco, Measure.restrict_congr_set Ico_ae_eq_Icc, ← hpre,
    ← Measure.restrict_map (measurable_const_mul c) measurableSet_Icc,
    Real.map_volume_mul_left hc, Measure.restrict_smul, abs_inv]

/-- **A law with bounded support is not a non-degenerate Gaussian**: if `ν((M, ∞)) = 0`, then
`ν ≠ gaussianReal m v` for every `m` and every `v ≠ 0`. -/
theorem ne_gaussianReal_of_measure_Ioi_eq_zero {ν : Measure ℝ} {M : ℝ} (hM : ν (Ioi M) = 0)
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : ν ≠ gaussianReal m v := by
  rintro rfl
  have h0 : volume (Ioi M) = 0 := gaussianReal_absolutelyContinuous' m hv hM
  rw [Real.volume_Ioi] at h0
  exact ENNReal.top_ne_zero h0

/-- **The limit law of the scaled error is not normal**: for every `c` (in particular
`c = f(1) − f(0)`), the law of `c (U − 1/2)` is not `gaussianReal m v` with `v ≠ 0`. -/
theorem limit_law_ne_gaussianReal (c : ℝ) {P : Measure Ω} {U : Ω → ℝ}
    (hU : HasLaw U uniformIco P) (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    P.map (fun ω ↦ c * (U ω - 1 / 2)) ≠ gaussianReal m v := by
  refine ne_gaussianReal_of_measure_Ioi_eq_zero (M := |c|) ?_ m hv
  have hmeas : AEMeasurable (fun ω ↦ c * (U ω - 1 / 2)) P :=
    ((measurable_id'.sub_const _).const_mul _).comp_aemeasurable hU.aemeasurable
  rw [Measure.map_apply_of_aemeasurable hmeas measurableSet_Ioi, measure_eq_zero_iff_ae_notMem]
  filter_upwards [ae_mem_Ico_of_hasLaw hU] with ω hω
  intro h
  rw [mem_preimage, mem_Ioi] at h
  have hb : |U ω - 1 / 2| ≤ 1 := abs_le.2 ⟨by linarith [hω.1], by linarith [hω.2]⟩
  have h1 : c * (U ω - 1 / 2) ≤ |c| * 1 :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hb (abs_nonneg c))
  linarith

/-- **The randomly shifted lattice is not asymptotically normal** (post #2): for measurable `f`,
`C¹` on `[0,1]`, the scaled error `n (μ̂ₙ(U) − ∫₀¹ f)` does not converge in distribution to any
`N(m, v)` with `v ≠ 0`. -/
theorem not_tendstoInDistribution_scaled_error_gaussian {f f' : ℝ → ℝ} (hfm : Measurable f)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) {P : Measure Ω} [IsProbabilityMeasure P] {U : Ω → ℝ}
    (hU : HasLaw U uniformIco P) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Y : Ω' → ℝ} (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (hY : HasLaw Y (gaussianReal m v) P') :
    ¬ TendstoInDistribution (fun (n : ℕ) ω ↦ (n : ℝ) *
        (sampleMean n f (fun i ↦ stratumMap n i (U ω)) - ∫ x in (0 : ℝ)..1, f x))
      atTop Y (fun _ ↦ P) P' := by
  intro h
  have heq := tendstoInDistribution_unique _ (tendstoInDistribution_scaled_error hfm hf hf' hU) h
  rw [hY.map_eq] at heq
  exact limit_law_ne_gaussianReal _ hU m hv heq

/-- **At the MC scale `√n` the error vanishes**: for `f` `C¹` on `[0,1]` and `u ∈ [0,1]`,
`√n (μ̂ₙ(u) − ∫₀¹ f) → 0`. -/
theorem tendsto_sqrt_scaled_error {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n : ℕ ↦ Real.sqrt n *
        (sampleMean n f (fun i ↦ stratumMap n i u) - ∫ x in (0 : ℝ)..1, f x)) atTop (𝓝 0) := by
  have h2 : Tendsto (fun n : ℕ ↦ (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have h := (tendsto_scaled_error hf hf' hu).mul h2
  rw [mul_zero] at h
  refine h.congr (fun n ↦ ?_)
  rw [mul_right_comm, ← div_eq_mul_inv, Real.div_sqrt]

/-- **Almost surely, `√n (μ̂ₙ(U) − ∫₀¹ f) → 0`.** -/
theorem ae_tendsto_sqrt_scaled_error {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) {P : Measure Ω} {U : Ω → ℝ} (hU : HasLaw U uniformIco P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ Real.sqrt n *
        (sampleMean n f (fun i ↦ stratumMap n i (U ω)) - ∫ x in (0 : ℝ)..1, f x))
      atTop (𝓝 0) := by
  filter_upwards [ae_mem_Ico_of_hasLaw hU] with ω hω
  exact tendsto_sqrt_scaled_error hf hf' (Ico_subset_Icc_self hω)

/-- **Not asymptotically normal at the `√n` scale either**: `√n (μ̂ₙ(U) − ∫₀¹ f)` does not
converge in distribution to any `N(m, v)` with `v ≠ 0` (it converges to the point mass at `0`).
Contrast MC, `tendstoInDistribution_sampleMean_iid`. -/
theorem not_tendstoInDistribution_sqrt_scaled_error_gaussian {f f' : ℝ → ℝ} (hfm : Measurable f)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) {P : Measure Ω} [IsProbabilityMeasure P] {U : Ω → ℝ}
    (hU : HasLaw U uniformIco P) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Y : Ω' → ℝ} (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (hY : HasLaw Y (gaussianReal m v) P') :
    ¬ TendstoInDistribution (fun (n : ℕ) ω ↦ Real.sqrt n *
        (sampleMean n f (fun i ↦ stratumMap n i (U ω)) - ∫ x in (0 : ℝ)..1, f x))
      atTop Y (fun _ ↦ P) P' := by
  intro h
  have h0 : TendstoInDistribution (fun (n : ℕ) ω ↦ Real.sqrt n *
        (sampleMean n f (fun i ↦ stratumMap n i (U ω)) - ∫ x in (0 : ℝ)..1, f x))
      atTop (fun _ ↦ (0 : ℝ)) (fun _ ↦ P) P :=
    tendstoInDistribution_of_ae_tendsto
      (fun n ↦ (((measurable_sampleMean_stratumMap hfm n).sub_const _).const_mul
        _).comp_aemeasurable hU.aemeasurable)
      aemeasurable_const (ae_tendsto_sqrt_scaled_error hf hf' hU)
  have heq := tendstoInDistribution_unique _ h0 h
  rw [hY.map_eq] at heq
  refine ne_gaussianReal_of_measure_Ioi_eq_zero (M := 0) ?_ m hv heq
  rw [Measure.map_apply measurable_const measurableSet_Ioi,
    preimage_const_of_notMem (s := Ioi (0 : ℝ)) (fun h ↦ lt_irrefl (0 : ℝ) h), measure_empty]

end RQMCMarkov.PointSets
