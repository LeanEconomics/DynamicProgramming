/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OwenScrambling.ShiftLimit
import OwenScrambling.Stratified

/-!
# Exact asymptotics of the stratified (= Owen-scrambled net) variance: `n³ σₙ² → ∫ f'²/12`

By `Owen1DScramble`, the Owen-scrambled `(0,m,1)`-net in base `b` has the law of independent
stratified sampling with `n = bᵐ` cells, so its variance is
`σₙ² = stratVar n f = n⁻² Σᵢ Var(f | cell i)` (`variance_stratified_eq`). `Stratified` bounds it
by `K²/(12 n³)` for `K`-Lipschitz `f`; here we find its exact first-order behaviour.

## Main results

* `stratVar`, `stratVar_nonneg`: `σₙ² = n⁻² Σᵢ Var_{u ~ U[0,1)} f((i + u)/n)`.
* `abs_variance_add_sub_le`: `|Var(X + Y) − Var(X)| ≤ 2η(2A + η)` when `|X| ≤ A`, `|Y| ≤ η`.
* `abs_sub_sub_deriv_mul_le`: the mean value bound `|f(y) − f(a) − f'(a)(y − a)| ≤ ε h` on a cell
  `[a, a + h]` where `f'` varies by at most `ε`.
* `abs_variance_cell_sub_le`: `|Var_u f(a + u h) − (f'(a) h)²/12| ≤ ε (7L + 25ε) h²`, `|f'(a)| ≤ L`.
* `abs_integral_sq_deriv_sub_le`: `|∫ₐ^{a+h} f'² − f'(a)² h| ≤ ε (2L + ε) h`;
  `abs_inv_mul_variance_cell_sub_le` combines the two cell estimates.
* `tendsto_cube_mul_stratVar`: for `f` `C¹` on `[0,1]`, `n³ σₙ² → (1/12) ∫₀¹ f'(x)² dx`, so the
  RMSE is `σₙ ~ n^{-3/2} (∫ f'²/12)^{1/2}` (Owen 1997's rate in one dimension).
* `integral_sq_deriv_pos`: if `f` is not constant on `[0,1]` then `∫₀¹ f'² > 0`, so then
  `σₙ > 0` for all large `n` (`eventually_stratVar_pos`).
* `stratVar_const`: for constant `f`, `σₙ = 0` for every `n` (the estimator is exact).

**Hypotheses.** `C¹` on `[0,1]` is as in `ShiftLimit`: `HasDerivWithinAt f (f' x) [0,1] x` for
`x ∈ [0,1]` with `f'` continuous on `[0,1]`.
-/

namespace RQMCMarkov.OwenScrambling

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The variance of the independent stratified estimator with `n` equal cells (and of the
Owen-scrambled net, `n = bᵐ`): `σₙ² = n⁻² Σᵢ Var_{u ~ U[0,1)} f((i + u)/n)`. -/
noncomputable def stratVar (n : ℕ) (f : ℝ → ℝ) : ℝ :=
  ((n : ℝ)⁻¹) ^ 2 * ∑ i : Fin n, Var[fun u ↦ f (stratumMap n i u); uniformIco]

/-- `σₙ² ≥ 0`. -/
theorem stratVar_nonneg (n : ℕ) (f : ℝ → ℝ) : 0 ≤ stratVar n f :=
  mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ ↦ variance_nonneg _ _)

/-- **Perturbation of a variance**: if `|X| ≤ A` and `|Y| ≤ η` a.s., then
`|Var(X + Y) − Var(X)| ≤ 2η(2A + η)`. -/
theorem abs_variance_add_sub_le {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) {A η : ℝ}
    (hXA : ∀ᵐ ω ∂μ, |X ω| ≤ A) (hYη : ∀ᵐ ω ∂μ, |Y ω| ≤ η) :
    |Var[fun ω ↦ X ω + Y ω; μ] - Var[X; μ]| ≤ 2 * η * (2 * A + η) := by
  have hXL : MemLp X 2 μ := MemLp.of_bound hX A (hXA.mono fun ω h ↦ by rwa [Real.norm_eq_abs])
  have hYL : MemLp Y 2 μ := MemLp.of_bound hY η (hYη.mono fun ω h ↦ by rwa [Real.norm_eq_abs])
  have hXYL : MemLp (fun ω ↦ X ω + Y ω) 2 μ := hXL.add hYL
  have hXi := hXL.integrable one_le_two
  have hYi := hYL.integrable one_le_two
  rw [variance_eq_sub hXYL, variance_eq_sub hXL]
  change |(∫ ω, (X ω + Y ω) ^ 2 ∂μ - (∫ ω, (X ω + Y ω) ∂μ) ^ 2) -
    (∫ ω, X ω ^ 2 ∂μ - (∫ ω, X ω ∂μ) ^ 2)| ≤ _
  have e1 : ∫ ω, (X ω + Y ω) ^ 2 ∂μ - ∫ ω, X ω ^ 2 ∂μ = ∫ ω, Y ω * (2 * X ω + Y ω) ∂μ := by
    rw [← integral_sub hXYL.integrable_sq hXL.integrable_sq]
    congr 1
    funext ω
    ring
  rw [integral_add hXi hYi]
  have hbd : ∀ {g : Ω → ℝ} {C : ℝ}, (∀ᵐ ω ∂μ, |g ω| ≤ C) → |∫ ω, g ω ∂μ| ≤ C := by
    intro g C hg
    have h := norm_integral_le_of_norm_le_const (μ := μ) (f := g) (C := C)
      (hg.mono fun ω h ↦ by rwa [Real.norm_eq_abs])
    rwa [probReal_univ, mul_one, Real.norm_eq_abs] at h
  have b2 : |∫ ω, X ω ∂μ| ≤ A := hbd hXA
  have b3 : |∫ ω, Y ω ∂μ| ≤ η := hbd hYη
  have hA0 : 0 ≤ A := (abs_nonneg _).trans b2
  have hη0 : 0 ≤ η := (abs_nonneg _).trans b3
  have b1 : |∫ ω, Y ω * (2 * X ω + Y ω) ∂μ| ≤ η * (2 * A + η) := by
    refine hbd ?_
    filter_upwards [hXA, hYη] with ω h1 h2
    rw [abs_mul]
    have h3 : |2 * X ω + Y ω| ≤ 2 * A + η := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_two]
      linarith
    exact mul_le_mul h2 h3 (abs_nonneg _) hη0
  have b4 : |(∫ ω, Y ω ∂μ) * (2 * (∫ ω, X ω ∂μ) + ∫ ω, Y ω ∂μ)| ≤ η * (2 * A + η) := by
    rw [abs_mul]
    have h3 : |2 * (∫ ω, X ω ∂μ) + ∫ ω, Y ω ∂μ| ≤ 2 * A + η := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_two]
      linarith
    exact mul_le_mul b3 h3 (abs_nonneg _) hη0
  have heq : (∫ ω, (X ω + Y ω) ^ 2 ∂μ - (∫ ω, X ω ∂μ + ∫ ω, Y ω ∂μ) ^ 2) -
      (∫ ω, X ω ^ 2 ∂μ - (∫ ω, X ω ∂μ) ^ 2) = ∫ ω, Y ω * (2 * X ω + Y ω) ∂μ -
        (∫ ω, Y ω ∂μ) * (2 * (∫ ω, X ω ∂μ) + ∫ ω, Y ω ∂μ) := by
    rw [← e1]
    ring
  rw [heq]
  calc |∫ ω, Y ω * (2 * X ω + Y ω) ∂μ - (∫ ω, Y ω ∂μ) * (2 * (∫ ω, X ω ∂μ) + ∫ ω, Y ω ∂μ)|
      ≤ |∫ ω, Y ω * (2 * X ω + Y ω) ∂μ| +
          |(∫ ω, Y ω ∂μ) * (2 * (∫ ω, X ω ∂μ) + ∫ ω, Y ω ∂μ)| := abs_sub _ _
    _ ≤ η * (2 * A + η) + η * (2 * A + η) := add_le_add b1 b4
    _ = 2 * η * (2 * A + η) := by ring

/-- **Mean value bound on a cell**: if `f' ` varies by at most `ε` on `[a, a + h]`, then
`|f(y) − f(a) − f'(a)(y − a)| ≤ ε h` for `y ∈ [a, a + h]`. -/
theorem abs_sub_sub_deriv_mul_le {f f' : ℝ → ℝ} {a h ε : ℝ} (hh : 0 < h)
    (hf : ∀ x ∈ Icc a (a + h), HasDerivWithinAt f (f' x) (Icc a (a + h)) x)
    (hε : ∀ x ∈ Icc a (a + h), |f' x - f' a| ≤ ε) {y : ℝ} (hy : y ∈ Icc a (a + h)) :
    |f y - f a - f' a * (y - a)| ≤ ε * h := by
  have hah : a ≤ a + h := by linarith
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hε a (left_mem_Icc.2 hah))
  set g : ℝ → ℝ := fun x ↦ f x - f' a * x with hg
  have hgd : ∀ x ∈ Icc a (a + h), HasDerivWithinAt g (f' x - f' a) (Icc a (a + h)) x := by
    intro x hx
    exact ((hf x hx).sub ((hasDerivWithinAt_id x _).const_mul (f' a))).congr_deriv (by ring)
  have := norm_image_sub_le_of_norm_deriv_le_segment' hgd
    (fun x hx ↦ by rw [Real.norm_eq_abs]; exact hε x (Ico_subset_Icc_self hx)) y hy
  rw [Real.norm_eq_abs] at this
  have heq : g y - g a = f y - f a - f' a * (y - a) := by
    simp only [hg]
    ring
  rw [← heq]
  exact this.trans (mul_le_mul_of_nonneg_left (by linarith [hy.2]) hε0)

/-- **Variance on one cell**: if `f` is differentiable on `[a, a + h]` with `|f' − f'(a)| ≤ ε` there
and `|f'(a)| ≤ L`, then `|Var_{u ~ U[0,1)} f(a + u h) − (f'(a) h)²/12| ≤ ε (7L + 25ε) h²`. -/
theorem abs_variance_cell_sub_le {f f' : ℝ → ℝ} {a h ε L : ℝ} (hh : 0 < h)
    (hf : ∀ x ∈ Icc a (a + h), HasDerivWithinAt f (f' x) (Icc a (a + h)) x)
    (hε : ∀ x ∈ Icc a (a + h), |f' x - f' a| ≤ ε) (hL : |f' a| ≤ L) :
    |Var[fun u ↦ f (a + u * h); uniformIco] - (f' a * h) ^ 2 / 12| ≤
      ε * (7 * L + 25 * ε) * h ^ 2 := by
  have := isProbabilityMeasure_uniformIco
  have hah : a ≤ a + h := by linarith
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hε a (left_mem_Icc.2 hah))
  have hL0 : 0 ≤ L := (abs_nonneg _).trans hL
  set Δ : ℝ := f (a + h) - f a with hΔ
  set c : ℝ := h⁻¹ * ∫ x in a..a + h, f x with hc
  set X : ℝ → ℝ := fun u ↦ -Δ / 2 + Δ * u with hX
  set Y : ℝ → ℝ := fun u ↦ f (a + u * h) - c - X u with hY
  have hfc : ContinuousOn f (Icc a (a + h)) := fun x hx ↦ (hf x hx).continuousWithinAt
  have hmaps : MapsTo (fun u : ℝ ↦ a + u * h) (Ico 0 1) (Icc a (a + h)) := fun u hu ↦
    ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩
  have hgc : ContinuousOn (fun u ↦ f (a + u * h)) (Ico 0 1) :=
    hfc.comp (continuous_const.add (continuous_id.mul continuous_const)).continuousOn hmaps
  have hgm : AEStronglyMeasurable (fun u ↦ f (a + u * h)) uniformIco :=
    hgc.aestronglyMeasurable measurableSet_Ico
  have hXc : Continuous X := continuous_const.add (continuous_const.mul continuous_id)
  have hXm : AEStronglyMeasurable X uniformIco := hXc.aestronglyMeasurable
  have hYm : AEStronglyMeasurable Y uniformIco := (hgm.sub aestronglyMeasurable_const).sub hXm
  have hfun : (fun u ↦ f (a + u * h)) = fun u ↦ c + (X u + Y u) := by
    funext u
    simp only [hY]
    ring
  have hVar : Var[fun u ↦ f (a + u * h); uniformIco] = Var[fun u ↦ X u + Y u; uniformIco] := by
    rw [hfun, variance_const_add (X := fun u ↦ X u + Y u) (hXm.add hYm) c]
  have hVX : Var[X; uniformIco] = Δ ^ 2 / 12 := variance_uniformIco_affine (-Δ / 2) Δ
  have hXb : ∀ᵐ u ∂uniformIco, |X u| ≤ |Δ| / 2 := by
    refine ae_restrict_of_forall_mem measurableSet_Ico (fun u hu ↦ ?_)
    have heq : X u = Δ * (u - 1 / 2) := by
      simp only [hX]
      ring
    rw [heq, abs_mul]
    have hu2 : |u - 1 / 2| ≤ 1 / 2 := abs_le.2 ⟨by linarith [hu.1], by linarith [hu.2]⟩
    calc |Δ| * |u - 1 / 2| ≤ |Δ| * (1 / 2) := mul_le_mul_of_nonneg_left hu2 (abs_nonneg _)
      _ = |Δ| / 2 := by ring
  have hYb : ∀ᵐ u ∂uniformIco, |Y u| ≤ 3 * ε * h := by
    refine ae_restrict_of_forall_mem measurableSet_Ico (fun u hu ↦ ?_)
    have heq : Y u = f (a + u * h) - h⁻¹ * (∫ x in a..a + h, f x) -
        (u - 1 / 2) * (f (a + h) - f a) := by
      simp only [hY, hX, hc, hΔ]
      ring
    rw [heq]
    exact cell_error_le hh hf hε (Ico_subset_Icc_self hu)
  have hmvt := abs_sub_sub_deriv_mul_le hh hf hε (right_mem_Icc.2 hah)
  rw [add_sub_cancel_left] at hmvt
  have hΔb : |Δ| ≤ (L + ε) * h := by
    have h1 : |f' a * h| ≤ L * h := by
      rw [abs_mul, abs_of_pos hh]
      exact mul_le_mul_of_nonneg_right hL hh.le
    have h2 : |Δ| ≤ |Δ - f' a * h| + |f' a * h| := by
      have := abs_add_le (Δ - f' a * h) (f' a * h)
      rwa [sub_add_cancel] at this
    linarith
  have b1 : |Var[fun u ↦ X u + Y u; uniformIco] - Δ ^ 2 / 12| ≤
      6 * ε * (L + 4 * ε) * h ^ 2 := by
    rw [← hVX]
    refine (abs_variance_add_sub_le hXm hYm hXb hYb).trans ?_
    have hle : 2 * (|Δ| / 2) + 3 * ε * h ≤ (L + ε) * h + 3 * ε * h := by linarith
    calc 2 * (3 * ε * h) * (2 * (|Δ| / 2) + 3 * ε * h)
        ≤ 2 * (3 * ε * h) * ((L + ε) * h + 3 * ε * h) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = 6 * ε * (L + 4 * ε) * h ^ 2 := by ring
  have b2 : |Δ ^ 2 / 12 - (f' a * h) ^ 2 / 12| ≤ ε * (2 * L + ε) * h ^ 2 / 12 := by
    have heq : Δ ^ 2 / 12 - (f' a * h) ^ 2 / 12 = (Δ - f' a * h) * (Δ + f' a * h) / 12 := by
      ring
    have h3 : |Δ + f' a * h| ≤ (2 * L + ε) * h := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos hh]
      have := mul_le_mul_of_nonneg_right hL hh.le
      linarith
    rw [heq, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 12)]
    have h4 : |Δ - f' a * h| * |Δ + f' a * h| ≤ (ε * h) * ((2 * L + ε) * h) :=
      mul_le_mul hmvt h3 (abs_nonneg _) (by positivity)
    calc |Δ - f' a * h| * |Δ + f' a * h| / 12 ≤ (ε * h) * ((2 * L + ε) * h) / 12 :=
          div_le_div_of_nonneg_right h4 (by norm_num)
      _ = ε * (2 * L + ε) * h ^ 2 / 12 := by ring
  rw [hVar]
  have key : ε * (7 * L + 25 * ε) * h ^ 2 -
      (6 * ε * (L + 4 * ε) * h ^ 2 + ε * (2 * L + ε) * h ^ 2 / 12) =
        ε * h ^ 2 * (5 * L / 6 + 11 * ε / 12) := by ring
  have hpos : 0 ≤ ε * h ^ 2 * (5 * L / 6 + 11 * ε / 12) := by positivity
  have htri : |Var[fun u ↦ X u + Y u; uniformIco] - (f' a * h) ^ 2 / 12| ≤
      |Var[fun u ↦ X u + Y u; uniformIco] - Δ ^ 2 / 12| +
        |Δ ^ 2 / 12 - (f' a * h) ^ 2 / 12| := abs_sub_le _ _ _
  linarith

/-- **Integral of `f'²` on one cell**: if `|f' − f'(a)| ≤ ε` on `[a, a + h]` and `|f'(a)| ≤ L`,
then `|∫ₐ^{a+h} f'² − f'(a)² h| ≤ ε (2L + ε) h`. -/
theorem abs_integral_sq_deriv_sub_le {f' : ℝ → ℝ} {a h ε L : ℝ} (hh : 0 < h)
    (hc : ContinuousOn f' (Icc a (a + h))) (hε : ∀ x ∈ Icc a (a + h), |f' x - f' a| ≤ ε)
    (hL : |f' a| ≤ L) :
    |(∫ x in a..a + h, f' x ^ 2) - f' a ^ 2 * h| ≤ ε * (2 * L + ε) * h := by
  have hah : a ≤ a + h := by linarith
  have hint : IntervalIntegrable (fun x ↦ f' x ^ 2) MeasureTheory.volume a (a + h) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hah]
    exact hc.pow 2
  have heq : (∫ x in a..a + h, f' x ^ 2) - f' a ^ 2 * h =
      ∫ x in a..a + h, (f' x ^ 2 - f' a ^ 2) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left, mul_comm]
  rw [heq]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := a + h)
    (f := fun x ↦ f' x ^ 2 - f' a ^ 2) (C := ε * (2 * L + ε)) (fun x hx ↦ by
      rw [uIoc_of_le hah] at hx
      have hx' := hε x (Ioc_subset_Icc_self hx)
      rw [Real.norm_eq_abs]
      have hfac : f' x ^ 2 - f' a ^ 2 = (f' x - f' a) * (f' x - f' a + 2 * f' a) := by ring
      rw [hfac, abs_mul]
      have h2 : |f' x - f' a + 2 * f' a| ≤ ε + 2 * L := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_two]
        linarith
      have hε0 : 0 ≤ ε := (abs_nonneg _).trans hx'
      calc |f' x - f' a| * |f' x - f' a + 2 * f' a| ≤ ε * (ε + 2 * L) :=
            mul_le_mul hx' h2 (abs_nonneg _) hε0
        _ = ε * (2 * L + ε) := by ring)
  rw [Real.norm_eq_abs, add_sub_cancel_left, abs_of_pos hh] at h
  exact h

/-- **One cell, combined**: `|h⁻¹ Var_u f(a + u h) − (1/12) ∫ₐ^{a+h} f'²| ≤ c(ε, L) h` with
`c(ε, L) = ε (7L + 25ε) + ε (2L + ε)/12`. -/
theorem abs_inv_mul_variance_cell_sub_le {f f' : ℝ → ℝ} {a h ε L : ℝ} (hh : 0 < h)
    (hf : ∀ x ∈ Icc a (a + h), HasDerivWithinAt f (f' x) (Icc a (a + h)) x)
    (hc : ContinuousOn f' (Icc a (a + h))) (hε : ∀ x ∈ Icc a (a + h), |f' x - f' a| ≤ ε)
    (hL : |f' a| ≤ L) :
    |h⁻¹ * Var[fun u ↦ f (a + u * h); uniformIco] - (∫ x in a..a + h, f' x ^ 2) / 12| ≤
      (ε * (7 * L + 25 * ε) + ε * (2 * L + ε) / 12) * h := by
  have h1 := abs_variance_cell_sub_le hh hf hε hL
  have h2 := abs_integral_sq_deriv_sub_le hh hc hε hL
  have heq : h⁻¹ * Var[fun u ↦ f (a + u * h); uniformIco] - (∫ x in a..a + h, f' x ^ 2) / 12 =
      h⁻¹ * (Var[fun u ↦ f (a + u * h); uniformIco] - (f' a * h) ^ 2 / 12) -
        ((∫ x in a..a + h, f' x ^ 2) - f' a ^ 2 * h) / 12 := by
    field_simp
    ring
  rw [heq]
  have hinv : 0 < h⁻¹ := inv_pos.2 hh
  have b1 : |h⁻¹ * (Var[fun u ↦ f (a + u * h); uniformIco] - (f' a * h) ^ 2 / 12)| ≤
      ε * (7 * L + 25 * ε) * h := by
    rw [abs_mul, abs_of_pos hinv]
    calc h⁻¹ * |Var[fun u ↦ f (a + u * h); uniformIco] - (f' a * h) ^ 2 / 12|
        ≤ h⁻¹ * (ε * (7 * L + 25 * ε) * h ^ 2) := mul_le_mul_of_nonneg_left h1 hinv.le
      _ = ε * (7 * L + 25 * ε) * h := by
          field_simp
  have b2 : |((∫ x in a..a + h, f' x ^ 2) - f' a ^ 2 * h) / 12| ≤ ε * (2 * L + ε) / 12 * h := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 12)]
    calc |(∫ x in a..a + h, f' x ^ 2) - f' a ^ 2 * h| / 12 ≤ ε * (2 * L + ε) * h / 12 :=
          div_le_div_of_nonneg_right h2 (by norm_num)
      _ = ε * (2 * L + ε) / 12 * h := by ring
  calc |h⁻¹ * (Var[fun u ↦ f (a + u * h); uniformIco] - (f' a * h) ^ 2 / 12) -
        ((∫ x in a..a + h, f' x ^ 2) - f' a ^ 2 * h) / 12|
      ≤ |h⁻¹ * (Var[fun u ↦ f (a + u * h); uniformIco] - (f' a * h) ^ 2 / 12)| +
        |((∫ x in a..a + h, f' x ^ 2) - f' a ^ 2 * h) / 12| := abs_sub _ _
    _ ≤ ε * (7 * L + 25 * ε) * h + ε * (2 * L + ε) / 12 * h := add_le_add b1 b2
    _ = (ε * (7 * L + 25 * ε) + ε * (2 * L + ε) / 12) * h := by ring

/-- **The exact rate of the stratified (= Owen-scrambled net) variance**: for `f` `C¹` on
`[0,1]`, `n³ σₙ² → (1/12) ∫₀¹ f'(x)² dx` as `n → ∞`. -/
theorem tendsto_cube_mul_stratVar {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 3 * stratVar n f) atTop
      (𝓝 ((∫ x in (0 : ℝ)..1, f' x ^ 2) / 12)) := by
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn hf'
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0 (left_mem_Icc.2 zero_le_one))
  have huc : UniformContinuousOn f' (Icc 0 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf'
  rw [Metric.tendsto_atTop]
  intro ε' hε'
  set K : ℝ := 9 * L + 26 with hK
  have hKpos : 0 < K := by positivity
  set ε : ℝ := min 1 (ε' / (2 * K)) with hεdef
  have hεpos : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεK : ε * K ≤ ε' / 2 := by
    have := min_le_right 1 (ε' / (2 * K))
    rw [← hεdef] at this
    calc ε * K ≤ ε' / (2 * K) * K := mul_le_mul_of_nonneg_right this hKpos.le
      _ = ε' / 2 := by field_simp
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.1 huc ε hεpos
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
  -- the scaled variance and the integral, cell by cell
  have hvar : (n : ℝ) ^ 3 * stratVar n f =
      ∑ k ∈ Finset.range n, h⁻¹ * Var[fun u ↦ f (a k + u * h); uniformIco] := by
    unfold stratVar
    rw [Fin.sum_univ_eq_sum_range (fun k ↦ Var[fun u ↦ f (stratumMap n k u); uniformIco]) n,
      ← mul_assoc, Finset.mul_sum]
    have hc : (n : ℝ) ^ 3 * ((n : ℝ)⁻¹) ^ 2 = h⁻¹ := by
      rw [hhdef, one_div, inv_inv]
      field_simp
    rw [hc]
    refine Finset.sum_congr rfl (fun k _ ↦ ?_)
    have hfun : (fun u ↦ f (stratumMap n k u)) = fun u ↦ f (a k + u * h) := by
      funext u
      congr 1
      simp only [stratumMap, hadef, hhdef]
      ring
    rw [hfun]
  have hint : (∫ x in (0 : ℝ)..1, f' x ^ 2) =
      ∑ k ∈ Finset.range n, ∫ x in a k..a k + h, f' x ^ 2 := by
    have hii : ∀ k < n, IntervalIntegrable (fun x ↦ f' x ^ 2) volume (a k) (a (k + 1)) := by
      intro k hk
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le (by rw [← ha k]; linarith), ← ha k]
      exact (hf'.mono (hcell k hk)).pow 2
    rw [← ha0, ← han, ← intervalIntegral.sum_integral_adjacent_intervals hii]
    refine Finset.sum_congr rfl (fun k _ ↦ ?_)
    rw [ha k]
  have hid : (n : ℝ) ^ 3 * stratVar n f - (∫ x in (0 : ℝ)..1, f' x ^ 2) / 12 =
      ∑ k ∈ Finset.range n, (h⁻¹ * Var[fun u ↦ f (a k + u * h); uniformIco] -
        (∫ x in a k..a k + h, f' x ^ 2) / 12) := by
    rw [hvar, hint, Finset.sum_div, ← Finset.sum_sub_distrib]
  have hbound : ∀ k ∈ Finset.range n, |h⁻¹ * Var[fun u ↦ f (a k + u * h); uniformIco] -
      (∫ x in a k..a k + h, f' x ^ 2) / 12| ≤
        (ε * (7 * L + 25 * ε) + ε * (2 * L + ε) / 12) * h := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    have hsub := hcell k hk'
    have hak : a k ∈ Icc (0 : ℝ) 1 := hsub (left_mem_Icc.2 (by linarith))
    refine abs_inv_mul_variance_cell_sub_le hh (fun x hx ↦ (hf x (hsub hx)).mono hsub)
      (hf'.mono hsub) (fun x hx ↦ ?_) ?_
    · have hdist : dist x (a k) < δ := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith [hx.1])]
        linarith [hx.2]
      have := hδf x (hsub hx) (a k) hak hdist
      rw [Real.dist_eq] at this
      exact this.le
    · have := hL (a k) hak
      rwa [Real.norm_eq_abs] at this
  have hcK : ε * (7 * L + 25 * ε) + ε * (2 * L + ε) / 12 ≤ ε * K := by
    have h1 : ε * (7 * L + 25 * ε) ≤ ε * (7 * L + 25) := by
      have : 7 * L + 25 * ε ≤ 7 * L + 25 := by linarith
      exact mul_le_mul_of_nonneg_left this hεpos.le
    have h2 : ε * (2 * L + ε) / 12 ≤ ε * (2 * L + 1) := by
      have : ε * (2 * L + ε) ≤ ε * (2 * L + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hεpos.le
      have h0 : 0 ≤ ε * (2 * L + 1) := by positivity
      linarith
    have h3 : ε * (7 * L + 25) + ε * (2 * L + 1) = ε * K := by
      rw [hK]
      ring
    linarith
  rw [Real.dist_eq, hid]
  calc |∑ k ∈ Finset.range n, (h⁻¹ * Var[fun u ↦ f (a k + u * h); uniformIco] -
          (∫ x in a k..a k + h, f' x ^ 2) / 12)|
      ≤ ∑ k ∈ Finset.range n, |h⁻¹ * Var[fun u ↦ f (a k + u * h); uniformIco] -
          (∫ x in a k..a k + h, f' x ^ 2) / 12| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range n, (ε * (7 * L + 25 * ε) + ε * (2 * L + ε) / 12) * h :=
        Finset.sum_le_sum hbound
    _ = ε * (7 * L + 25 * ε) + ε * (2 * L + ε) / 12 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hhdef]
        field_simp
    _ ≤ ε * K := hcK
    _ ≤ ε' / 2 := hεK
    _ < ε' := by linarith

/-- **A non-constant `C¹` function has `∫₀¹ f'² > 0`.** -/
theorem integral_sq_deriv_pos {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) (hnc : ∃ x ∈ Icc (0 : ℝ) 1, f x ≠ f 0) :
    0 < ∫ x in (0 : ℝ)..1, f' x ^ 2 := by
  have hcont : ContinuousOn (fun x ↦ f' x ^ 2) (Icc 0 1) := hf'.pow 2
  rcases (intervalIntegral.integral_nonneg zero_le_one
      (fun x _ ↦ sq_nonneg (f' x))).lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  have hzero : ∀ x ∈ Icc (0 : ℝ) 1, f' x ^ 2 = 0 := by
    have hii : IntervalIntegrable (fun x ↦ f' x ^ 2) volume 0 1 :=
      hcont.intervalIntegrable_of_Icc zero_le_one
    have h := (intervalIntegral.integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun x ↦ sq_nonneg (f' x)) hii).1 heq.symm
    rw [Ioc_eq_empty (not_lt.2 zero_le_one), union_empty,
      Measure.restrict_congr_set Ioc_ae_eq_Icc] at h
    have hEq := Measure.eqOn_of_ae_eq h hcont continuousOn_const (fun x hx ↦ by
      rwa [interior_Icc, closure_Ioo zero_ne_one])
    exact fun x hx ↦ hEq hx
  obtain ⟨x, hx, hfx⟩ := hnc
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hf (C := 0) (fun y hy ↦ by
    rw [Real.norm_eq_abs, (pow_eq_zero_iff two_ne_zero).1 (hzero y (Ico_subset_Icc_self hy)),
      abs_zero]) x hx
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at h
  exact hfx h

/-- **The scrambled-net variance is eventually positive** for non-constant `C¹` `f`: since
`n³ σₙ² → ∫ f'²/12 > 0`, `σₙ² > 0` for all large `n`. -/
theorem eventually_stratVar_pos {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) (hnc : ∃ x ∈ Icc (0 : ℝ) 1, f x ≠ f 0) :
    ∀ᶠ n : ℕ in atTop, 0 < stratVar n f := by
  have hpos : 0 < (∫ x in (0 : ℝ)..1, f' x ^ 2) / 12 :=
    div_pos (integral_sq_deriv_pos hf hf' hnc) (by norm_num)
  filter_upwards [(tendsto_cube_mul_stratVar hf hf').eventually (lt_mem_nhds hpos)] with n hn
  exact pos_of_mul_pos_right hn (by positivity)

/-- **Constant integrands are integrated exactly**: `σₙ² = 0` for every `n` when `f` is constant,
so the normalised error `(μ̂ₙ − μ)/σₙ` is `0/0` and no CLT can hold. -/
theorem stratVar_const (n : ℕ) (c : ℝ) : stratVar n (fun _ ↦ c) = 0 := by
  have := isProbabilityMeasure_uniformIco
  have h0 : ∀ i : Fin n, Var[fun u ↦ (fun _ : ℝ ↦ c) (stratumMap n i u); uniformIco] = 0 := by
    intro i
    have h := variance_const_add (μ := uniformIco) (X := (0 : ℝ → ℝ)) aestronglyMeasurable_const c
    rw [variance_zero] at h
    have hfun : (fun u ↦ (fun _ : ℝ ↦ c) (stratumMap n i u)) = fun ω ↦ c + (0 : ℝ → ℝ) ω := by
      funext u
      rw [Pi.zero_apply, add_zero]
    rw [hfun, h]
  unfold stratVar
  rw [Finset.sum_eq_zero (fun i _ ↦ h0 i), mul_zero]

end RQMCMarkov.OwenScrambling
