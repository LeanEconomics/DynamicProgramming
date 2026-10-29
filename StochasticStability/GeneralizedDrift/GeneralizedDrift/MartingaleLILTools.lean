/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.LILUpper

/-!
# Exponential supermartingales and truncation for the martingale LIL

Copied for Chapter 19 from the Chapter 17 project
(`LimitTheorems/MartingaleLILTools.lean`), with the namespace changed to
`MeynTweedie.GeneralizedDrift` and the imports to `GeneralizedDrift.*`.

Tools for the law of the iterated logarithm for martingale differences (`MartingaleLILUpper`,
`MartingaleLILLower`, Stout, *Ann. Math. Statist.* 41 (1970)), used for the LIL of MT
Theorems 17.0.1 (iv), 17.5.3 and 17.5.4 (pp. 422, 452) through the Poisson martingale (17.43).
Everything is stated through integrals against bounded weights `F`, so that conditional
expectations enter only through their defining property.

* `one_add_add_sq_le_exp` (`1 + x + x²(1 − |x|)/2 ≤ eˣ` for `|x| ≤ 1`),
  `exp_sub_sq_le_one_add` (`e^{y−y²} ≤ 1 + y` for `0 ≤ y ≤ 1`).
* **The exponential steps** (`integral_mul_exp_le`, `integral_mul_exp_ge`): for `|X| ≤ c`,
  `∫ F X = 0` and `∫ F X²` compared with `∫ F u`,
  `∫ F e^{λX} ≤ ∫ F e^{λ²(1+λc)u/2}` and `∫ F e^{λ²(1−2λc)u/2} ≤ ∫ F e^{λX}`.
* `IsBddMartDiff` (bounded martingale differences with predictable weights `uⱼ`), `IsVarLe`,
  `IsVarGe` (`uⱼ` above / below the conditional variance), and the exponential super- and
  submartingales `exp(λ Sₙ − κ Vₙ)`: `IsBddMartDiff.integral_exp_succ_le`,
  `IsBddMartDiff.integral_exp_succ_ge`, `IsBddMartDiff.integral_exp_le`,
  `IsBddMartDiff.integral_exp_ge`; restriction to predictable events
  (`IsBddMartDiff.indicator`, `IsVarLe.indicator`, `IsVarGe.indicator`).
* **Ville's maximal inequality** (`measureReal_exists_ge_le`):
  `a P(∃ n ≤ N, Mₙ ≥ a) ≤ E[M₀]` for non-negative supermartingales.
* `integral_mul_condExp` (pull-out), `clampAbs`, `sum_ite_threshold` (sums stopped when the
  running total passes a threshold).
* **Truncation** (`truncMD`, `truncMean`, `condVarMD`): `Dⱼ 1{|Dⱼ| ≤ bⱼ}` recentred by its
  (clamped) conditional mean is a bounded martingale difference (`integral_mul_truncMD`) whose
  conditional variance is at most `E[Dⱼ² | 𝓕ⱼ]` (`integral_mul_truncMD_sq_le`), and the mean is
  controlled by the tail (`integral_abs_truncMean_le`).
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-! ### Elementary inequalities -/

/-- `1 + x + x²(1 − |x|)/2 ≤ eˣ` for `|x| ≤ 1`. -/
theorem one_add_add_sq_le_exp {x : ℝ} (hx : |x| ≤ 1) :
    1 + x + x ^ 2 * (1 - |x|) / 2 ≤ Real.exp x := by
  have h := Real.exp_bound hx (n := 3) (by norm_num)
  have e : ∑ m ∈ Finset.range 3, x ^ m / (m.factorial : ℝ) = 1 + x + x ^ 2 / 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    push_cast
    ring
  rw [e] at h
  have h2 : |x| ^ 3 * ((Nat.succ 3 : ℕ) / ((Nat.factorial 3 : ℕ) * (3 : ℕ)) : ℝ) =
      |x| ^ 3 * (2 / 9) := by
    norm_num [Nat.factorial]
  rw [h2] at h
  have h3 : |x| ^ 3 = x ^ 2 * |x| := by
    rw [pow_succ, ← sq_abs x]
  have h4 := (abs_le.1 h).1
  have h5 : 0 ≤ x ^ 2 * |x| := by positivity
  nlinarith

/-- `e^{y − y²} ≤ 1 + y` for `0 ≤ y ≤ 1`. -/
theorem exp_sub_sq_le_one_add {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Real.exp (y - y ^ 2) ≤ 1 + y := by
  have h1 : |y - y ^ 2| ≤ y := by
    rw [abs_le]; constructor <;> nlinarith
  have h := exp_le_one_add_add_sq (h1.trans hy1)
  have h3 : (y - y ^ 2) ^ 2 ≤ y ^ 2 := by
    nlinarith [mul_nonneg (pow_nonneg hy0 3) (by linarith : (0 : ℝ) ≤ 2 - y)]
  have h4 : 1 + |y - y ^ 2| ≤ 2 := by linarith
  have h5 : (y - y ^ 2) ^ 2 * (1 + |y - y ^ 2|) / 2 ≤ y ^ 2 := by
    nlinarith [sq_nonneg (y - y ^ 2)]
  linarith

/-! ### Integrability of bounded functions -/

/-- Bounded measurable functions are integrable for a finite measure. -/
theorem integrable_of_abs_le {Q : Measure Ω} [IsFiniteMeasure Q] {f : Ω → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) : Integrable f Q :=
  Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hC ω)

/-- A product of two bounded measurable functions is integrable for a finite measure. -/
theorem integrable_mul_of_abs_le {Q : Measure Ω} [IsFiniteMeasure Q] {F g : Ω → ℝ}
    (hFm : Measurable F) (hgm : Measurable g) {C G : ℝ} (hF : ∀ ω, |F ω| ≤ C)
    (hg : ∀ ω, |g ω| ≤ G) : Integrable (fun ω => F ω * g ω) Q :=
  integrable_of_abs_le (hFm.mul hgm) (C := C * G) fun ω => by
    rw [abs_mul]; exact mul_le_mul (hF ω) (hg ω) (abs_nonneg _) ((abs_nonneg _).trans (hF ω))

/-! ### One step of the exponential supermartingale -/

/-- **The upper exponential step**: for `F ≥ 0` bounded, `|X| ≤ c`, `0 ≤ u ≤ B`,
`∫ F X = 0` and `∫ F X² ≤ ∫ F u`, and `0 ≤ λ`, `λc ≤ 1`, `κ ≥ λ²(1 + λc)/2`:
`∫ F e^{λX} ≤ ∫ F e^{κu}`. -/
theorem integral_mul_exp_le {Q : Measure Ω} [IsFiniteMeasure Q] {F X u : Ω → ℝ}
    (hFm : Measurable F) (hF0 : ∀ ω, 0 ≤ F ω) {C : ℝ} (hFb : ∀ ω, |F ω| ≤ C)
    (hXm : Measurable X) {c : ℝ} (hc : 0 ≤ c) (hXb : ∀ ω, |X ω| ≤ c) (hum : Measurable u)
    (hu0 : ∀ ω, 0 ≤ u ω) {B : ℝ} (huB : ∀ ω, u ω ≤ B)
    (h1 : ∫ ω, F ω * X ω ∂Q = 0) (h2 : ∫ ω, F ω * X ω ^ 2 ∂Q ≤ ∫ ω, F ω * u ω ∂Q)
    {l κ : ℝ} (hl : 0 ≤ l) (hlc : l * c ≤ 1) (hκ : l ^ 2 * (1 + l * c) / 2 ≤ κ) :
    ∫ ω, F ω * Real.exp (l * X ω) ∂Q ≤ ∫ ω, F ω * Real.exp (κ * u ω) ∂Q := by
  set K := l ^ 2 * (1 + l * c) / 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hX2b : ∀ ω, |X ω ^ 2| ≤ c ^ 2 := fun ω => by
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hXb ω) 2
  have hub : ∀ ω, |u ω| ≤ B := fun ω => by rw [abs_of_nonneg (hu0 ω)]; exact huB ω
  have hFi : Integrable F Q := integrable_of_abs_le hFm hFb
  have hFXi : Integrable (fun ω => F ω * X ω) Q := integrable_mul_of_abs_le hFm hXm hFb hXb
  have hFX2i : Integrable (fun ω => F ω * X ω ^ 2) Q :=
    integrable_mul_of_abs_le hFm (hXm.pow_const 2) hFb hX2b
  have hFui : Integrable (fun ω => F ω * u ω) Q := integrable_mul_of_abs_le hFm hum hFb hub
  have hFeX : Integrable (fun ω => F ω * Real.exp (l * X ω)) Q := by
    refine integrable_mul_of_abs_le hFm (Real.continuous_exp.measurable.comp
      (hXm.const_mul l)) hFb (G := Real.exp (l * c)) fun ω => ?_
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (abs_le.1 (hXb ω)).2 hl)
  have hFeu : Integrable (fun ω => F ω * Real.exp (κ * u ω)) Q := by
    refine integrable_mul_of_abs_le hFm (Real.continuous_exp.measurable.comp
      (hum.const_mul κ)) hFb (G := Real.exp (|κ| * B)) fun ω => ?_
    rw [abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hub ω) (abs_nonneg _)
  have hpt : ∀ ω, F ω * Real.exp (l * X ω) ≤ F ω + l * (F ω * X ω) + K * (F ω * X ω ^ 2) :=
    fun ω => by
      have habs : |l * X ω| ≤ l * c := by
        rw [abs_mul, abs_of_nonneg hl]; exact mul_le_mul_of_nonneg_left (hXb ω) hl
      have h3 := exp_le_one_add_add_sq (habs.trans hlc)
      have h4 : (l * X ω) ^ 2 * (1 + |l * X ω|) / 2 ≤ K * X ω ^ 2 := by
        have := sq_nonneg (l * X ω)
        rw [hK]
        nlinarith
      have h5 : Real.exp (l * X ω) ≤ 1 + l * X ω + K * X ω ^ 2 := by linarith
      have := mul_le_mul_of_nonneg_left h5 (hF0 ω)
      linarith
  have hpt2 : ∀ ω, F ω + K * (F ω * u ω) ≤ F ω * Real.exp (κ * u ω) := fun ω => by
    have h3 : 1 + K * u ω ≤ Real.exp (κ * u ω) := by
      have := Real.add_one_le_exp (K * u ω)
      have h4 : K * u ω ≤ κ * u ω := mul_le_mul_of_nonneg_right hκ (hu0 ω)
      have := Real.exp_le_exp.2 h4
      linarith
    have := mul_le_mul_of_nonneg_left h3 (hF0 ω)
    linarith
  have hlin : Integrable (fun ω => F ω + l * (F ω * X ω) + K * (F ω * X ω ^ 2)) Q :=
    (hFi.add (hFXi.const_mul l)).add (hFX2i.const_mul K)
  have hlin2 : Integrable (fun ω => F ω + K * (F ω * u ω)) Q := hFi.add (hFui.const_mul K)
  calc ∫ ω, F ω * Real.exp (l * X ω) ∂Q
      ≤ ∫ ω, (F ω + l * (F ω * X ω) + K * (F ω * X ω ^ 2)) ∂Q := integral_mono hFeX hlin hpt
    _ = ∫ ω, F ω ∂Q + l * ∫ ω, F ω * X ω ∂Q + K * ∫ ω, F ω * X ω ^ 2 ∂Q := by
        rw [integral_add (f := fun ω => F ω + l * (F ω * X ω))
          (g := fun ω => K * (F ω * X ω ^ 2)) (hFi.add (hFXi.const_mul l)) (hFX2i.const_mul K),
          integral_add (f := F) (g := fun ω => l * (F ω * X ω)) hFi (hFXi.const_mul l),
          integral_const_mul, integral_const_mul]
    _ ≤ ∫ ω, F ω ∂Q + K * ∫ ω, F ω * u ω ∂Q := by
        rw [h1, mul_zero, add_zero]
        linarith [mul_le_mul_of_nonneg_left h2 hK0]
    _ = ∫ ω, (F ω + K * (F ω * u ω)) ∂Q := by
        rw [integral_add (f := F) (g := fun ω => K * (F ω * u ω)) hFi (hFui.const_mul K),
          integral_const_mul]
    _ ≤ ∫ ω, F ω * Real.exp (κ * u ω) ∂Q := integral_mono hlin2 hFeu hpt2

/-- **The lower exponential step**: for `F ≥ 0` bounded, `|X| ≤ c`, `0 ≤ u ≤ c²`,
`∫ F X = 0` and `∫ F u ≤ ∫ F X²`, and `0 ≤ λ`, `λc ≤ 1`, `κ ≤ λ²(1 − 2λc)/2`:
`∫ F e^{κu} ≤ ∫ F e^{λX}`. -/
theorem integral_mul_exp_ge {Q : Measure Ω} [IsFiniteMeasure Q] {F X u : Ω → ℝ}
    (hFm : Measurable F) (hF0 : ∀ ω, 0 ≤ F ω) {C : ℝ} (hFb : ∀ ω, |F ω| ≤ C)
    (hXm : Measurable X) {c : ℝ} (hc : 0 ≤ c) (hXb : ∀ ω, |X ω| ≤ c) (hum : Measurable u)
    (hu0 : ∀ ω, 0 ≤ u ω) (huc : ∀ ω, u ω ≤ c ^ 2)
    (h1 : ∫ ω, F ω * X ω ∂Q = 0) (h2 : ∫ ω, F ω * u ω ∂Q ≤ ∫ ω, F ω * X ω ^ 2 ∂Q)
    {l κ : ℝ} (hl : 0 ≤ l) (hlc : l * c ≤ 1) (hκ : κ ≤ l ^ 2 * (1 - 2 * (l * c)) / 2) :
    ∫ ω, F ω * Real.exp (κ * u ω) ∂Q ≤ ∫ ω, F ω * Real.exp (l * X ω) ∂Q := by
  set K := l ^ 2 * (1 - l * c) / 2 with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ 1 - l * c := by linarith
    positivity
  have hX2b : ∀ ω, |X ω ^ 2| ≤ c ^ 2 := fun ω => by
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hXb ω) 2
  have hub : ∀ ω, |u ω| ≤ c ^ 2 := fun ω => by rw [abs_of_nonneg (hu0 ω)]; exact huc ω
  have hFi : Integrable F Q := integrable_of_abs_le hFm hFb
  have hFXi : Integrable (fun ω => F ω * X ω) Q := integrable_mul_of_abs_le hFm hXm hFb hXb
  have hFX2i : Integrable (fun ω => F ω * X ω ^ 2) Q :=
    integrable_mul_of_abs_le hFm (hXm.pow_const 2) hFb hX2b
  have hFui : Integrable (fun ω => F ω * u ω) Q := integrable_mul_of_abs_le hFm hum hFb hub
  have hFeX : Integrable (fun ω => F ω * Real.exp (l * X ω)) Q := by
    refine integrable_mul_of_abs_le hFm (Real.continuous_exp.measurable.comp
      (hXm.const_mul l)) hFb (G := Real.exp (l * c)) fun ω => ?_
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (abs_le.1 (hXb ω)).2 hl)
  have hFeu : Integrable (fun ω => F ω * Real.exp (κ * u ω)) Q := by
    refine integrable_mul_of_abs_le hFm (Real.continuous_exp.measurable.comp
      (hum.const_mul κ)) hFb (G := Real.exp (|κ| * c ^ 2)) fun ω => ?_
    rw [abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hub ω) (abs_nonneg _)
  have hpt : ∀ ω, F ω + l * (F ω * X ω) + K * (F ω * X ω ^ 2) ≤ F ω * Real.exp (l * X ω) :=
    fun ω => by
      have habs : |l * X ω| ≤ l * c := by
        rw [abs_mul, abs_of_nonneg hl]; exact mul_le_mul_of_nonneg_left (hXb ω) hl
      have h3 := one_add_add_sq_le_exp (habs.trans hlc)
      have h4 : K * X ω ^ 2 ≤ (l * X ω) ^ 2 * (1 - |l * X ω|) / 2 := by
        have := sq_nonneg (l * X ω)
        rw [hK]
        nlinarith
      have h5 : 1 + l * X ω + K * X ω ^ 2 ≤ Real.exp (l * X ω) := by linarith
      have := mul_le_mul_of_nonneg_left h5 (hF0 ω)
      linarith
  have hpt2 : ∀ ω, F ω * Real.exp (κ * u ω) ≤ F ω + K * (F ω * u ω) := fun ω => by
    set A := l ^ 2 * u ω / 2 with hA
    set a := l * c with ha
    have hA0 : 0 ≤ A := by have := hu0 ω; positivity
    have ha0 : 0 ≤ a := by positivity
    have hAa : A ≤ a ^ 2 / 2 := by
      rw [hA, ha, mul_pow]
      have := mul_le_mul_of_nonneg_left (huc ω) (sq_nonneg l)
      linarith
    have hy : K * u ω = A * (1 - a) := by rw [hK, hA, ha]; ring
    have hy0 : 0 ≤ K * u ω := mul_nonneg hK0 (hu0 ω)
    have ha2 : a ^ 2 ≤ 1 := by nlinarith
    have hy1 : K * u ω ≤ 1 := by
      rw [hy]
      have : A * (1 - a) ≤ A := by nlinarith
      linarith
    have h3 := exp_sub_sq_le_one_add hy0 hy1
    have h4 : κ * u ω ≤ K * u ω - (K * u ω) ^ 2 := by
      have h5 : κ * u ω ≤ A * (1 - 2 * a) := by
        have := mul_le_mul_of_nonneg_right hκ (hu0 ω)
        rw [hA, ha]
        linarith
      rw [hy]
      have h6 : (A * (1 - a)) ^ 2 ≤ A * (a ^ 2 / 2) * (1 - a) := by
        have h7 : 0 ≤ 1 - a := by linarith
        have h8 : A * (1 - a) ≤ a ^ 2 / 2 := by nlinarith
        have h9 : 0 ≤ A * (1 - a) := mul_nonneg hA0 h7
        nlinarith
      have h10 : A * (1 - 2 * a) ≤ A * (1 - a) - A * (a ^ 2 / 2) * (1 - a) := by
        have : 0 ≤ a - a ^ 2 / 2 + a ^ 3 / 2 := by nlinarith
        nlinarith
      linarith
    have h11 : Real.exp (κ * u ω) ≤ 1 + K * u ω := (Real.exp_le_exp.2 h4).trans h3
    have := mul_le_mul_of_nonneg_left h11 (hF0 ω)
    linarith
  have hlin : Integrable (fun ω => F ω + l * (F ω * X ω) + K * (F ω * X ω ^ 2)) Q :=
    (hFi.add (hFXi.const_mul l)).add (hFX2i.const_mul K)
  have hlin2 : Integrable (fun ω => F ω + K * (F ω * u ω)) Q := hFi.add (hFui.const_mul K)
  calc ∫ ω, F ω * Real.exp (κ * u ω) ∂Q
      ≤ ∫ ω, (F ω + K * (F ω * u ω)) ∂Q := integral_mono hFeu hlin2 hpt2
    _ = ∫ ω, F ω ∂Q + K * ∫ ω, F ω * u ω ∂Q := by
        rw [integral_add (f := F) (g := fun ω => K * (F ω * u ω)) hFi (hFui.const_mul K),
          integral_const_mul]
    _ ≤ ∫ ω, F ω ∂Q + l * ∫ ω, F ω * X ω ∂Q + K * ∫ ω, F ω * X ω ^ 2 ∂Q := by
        rw [h1, mul_zero, add_zero]
        linarith [mul_le_mul_of_nonneg_left h2 hK0]
    _ = ∫ ω, (F ω + l * (F ω * X ω) + K * (F ω * X ω ^ 2)) ∂Q := by
        rw [integral_add (f := fun ω => F ω + l * (F ω * X ω))
          (g := fun ω => K * (F ω * X ω ^ 2)) (hFi.add (hFXi.const_mul l)) (hFX2i.const_mul K),
          integral_add (f := F) (g := fun ω => l * (F ω * X ω)) hFi (hFXi.const_mul l),
          integral_const_mul, integral_const_mul]
    _ ≤ ∫ ω, F ω * Real.exp (l * X ω) ∂Q := integral_mono hlin hFeX hpt

/-! ### Bounded martingale differences and their exponential supermartingales -/

variable (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (X u : ℕ → Ω → ℝ) (c B : ℝ) in
/-- **Bounded martingale differences with weights**: `Xⱼ` is `𝓕ⱼ₊₁`-measurable, `|Xⱼ| ≤ c`, and
`∫ F Xⱼ = 0` for every bounded `𝓕ⱼ`-measurable `F` (that is, `E[Xⱼ | 𝓕ⱼ] = 0`); the weights
`uⱼ` (the intended conditional variances) are `𝓕ⱼ`-measurable with `0 ≤ uⱼ ≤ B`. -/
structure IsBddMartDiff : Prop where
  meas_X : ∀ j, Measurable[ℱ (j + 1)] (X j)
  meas_u : ∀ j, Measurable[ℱ j] (u j)
  abs_X_le : ∀ j ω, |X j ω| ≤ c
  u_nonneg : ∀ j ω, 0 ≤ u j ω
  u_le : ∀ j ω, u j ω ≤ B
  orth : ∀ j (F : Ω → ℝ) (C : ℝ), Measurable[ℱ j] F → (∀ ω, |F ω| ≤ C) →
    ∫ ω, F ω * X j ω ∂Q = 0

variable (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (X u : ℕ → Ω → ℝ) in
/-- `uⱼ` dominates the conditional variance of `Xⱼ`: `∫ F Xⱼ² ≤ ∫ F uⱼ` for bounded
`𝓕ⱼ`-measurable `F ≥ 0`. -/
def IsVarLe : Prop :=
  ∀ j (F : Ω → ℝ) (C : ℝ), Measurable[ℱ j] F → (∀ ω, 0 ≤ F ω) → (∀ ω, |F ω| ≤ C) →
    ∫ ω, F ω * X j ω ^ 2 ∂Q ≤ ∫ ω, F ω * u j ω ∂Q

variable (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (X u : ℕ → Ω → ℝ) in
/-- `uⱼ` is dominated by the conditional variance of `Xⱼ`: `∫ F uⱼ ≤ ∫ F Xⱼ²` for bounded
`𝓕ⱼ`-measurable `F ≥ 0`. -/
def IsVarGe : Prop :=
  ∀ j (F : Ω → ℝ) (C : ℝ), Measurable[ℱ j] F → (∀ ω, 0 ≤ F ω) → (∀ ω, |F ω| ≤ C) →
    ∫ ω, F ω * u j ω ∂Q ≤ ∫ ω, F ω * X j ω ^ 2 ∂Q

/-- The partial sums over `[n₀, n)` of adapted increments are `𝓕ₙ`-measurable. -/
theorem measurable_sum_Ico {ℱ : Filtration ℕ mΩ} {Y : ℕ → Ω → ℝ}
    (hY : ∀ j, Measurable[ℱ (j + 1)] (Y j)) (n₀ n : ℕ) :
    Measurable[ℱ n] fun ω => ∑ j ∈ Finset.Ico n₀ n, Y j ω :=
  Finset.measurable_sum _ fun j hj =>
    (hY j).mono (ℱ.mono (Nat.succ_le_of_lt (Finset.mem_Ico.1 hj).2)) le_rfl

/-- The partial sums over `[n₀, n]` of predictable weights are `𝓕ₙ`-measurable. -/
theorem measurable_sum_Ico_succ {ℱ : Filtration ℕ mΩ} {Y : ℕ → Ω → ℝ}
    (hY : ∀ j, Measurable[ℱ j] (Y j)) (n₀ n : ℕ) :
    Measurable[ℱ n] fun ω => ∑ j ∈ Finset.Ico n₀ (n + 1), Y j ω :=
  Finset.measurable_sum _ fun j hj =>
    (hY j).mono (ℱ.mono (Nat.le_of_lt_succ (Finset.mem_Ico.1 hj).2)) le_rfl

omit mΩ in
/-- `|Σ_{j ∈ [n₀, n)} Xⱼ| ≤ (n − n₀) c` for `|Xⱼ| ≤ c`. -/
theorem abs_sum_Ico_le {Y : ℕ → Ω → ℝ} {c : ℝ} (hY : ∀ j ω, |Y j ω| ≤ c) (n₀ n : ℕ) (ω : Ω) :
    |∑ j ∈ Finset.Ico n₀ n, Y j ω| ≤ (n - n₀ : ℕ) * c := by
  calc |∑ j ∈ Finset.Ico n₀ n, Y j ω| ≤ ∑ j ∈ Finset.Ico n₀ n, |Y j ω| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.Ico n₀ n, c := Finset.sum_le_sum fun j _ => hY j ω
    _ = (n - n₀ : ℕ) * c := by rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]

/-- **The exponential supermartingale, one step**: under `IsBddMartDiff` and `IsVarLe`, for
`0 ≤ λ`, `λc ≤ 1`, `κ ≥ λ²(1 + λc)/2` and bounded `𝓕ₙ`-measurable `F ≥ 0`,
`∫ F exp(λ S_{n+1} − κ V_{n+1}) ≤ ∫ F exp(λ Sₙ − κ Vₙ)`, where `Sₙ = Σ_{[n₀,n)} Xⱼ` and
`Vₙ = Σ_{[n₀,n)} uⱼ`. -/
theorem IsBddMartDiff.integral_exp_succ_le {Q : Measure Ω} [IsFiniteMeasure Q]
    {ℱ : Filtration ℕ mΩ} {X u : ℕ → Ω → ℝ} {c B : ℝ} (h : IsBddMartDiff Q ℱ X u c B)
    (hv : IsVarLe Q ℱ X u) (hc : 0 ≤ c) {l κ : ℝ} (hl : 0 ≤ l) (hlc : l * c ≤ 1)
    (hκ : l ^ 2 * (1 + l * c) / 2 ≤ κ) {n₀ n : ℕ} (hn : n₀ ≤ n) {F : Ω → ℝ} {C : ℝ}
    (hFm : Measurable[ℱ n] F) (hF0 : ∀ ω, 0 ≤ F ω) (hFb : ∀ ω, |F ω| ≤ C) :
    ∫ ω, F ω * Real.exp (l * ∑ j ∈ Finset.Ico n₀ (n + 1), X j ω -
        κ * ∑ j ∈ Finset.Ico n₀ (n + 1), u j ω) ∂Q ≤
      ∫ ω, F ω * Real.exp (l * ∑ j ∈ Finset.Ico n₀ n, X j ω -
        κ * ∑ j ∈ Finset.Ico n₀ n, u j ω) ∂Q := by
  have hκ0 : 0 ≤ κ := le_trans (by positivity) hκ
  set G : Ω → ℝ := fun ω => F ω * Real.exp (l * ∑ j ∈ Finset.Ico n₀ n, X j ω -
    κ * ∑ j ∈ Finset.Ico n₀ (n + 1), u j ω) with hG
  have hGm : Measurable[ℱ n] G :=
    hFm.mul (Real.continuous_exp.measurable.comp (((measurable_sum_Ico h.meas_X n₀ n).const_mul
      l).sub ((measurable_sum_Ico_succ h.meas_u n₀ n).const_mul κ)))
  have hG0 : ∀ ω, 0 ≤ G ω := fun ω => mul_nonneg (hF0 ω) (Real.exp_pos _).le
  have hGb : ∀ ω, |G ω| ≤ C * Real.exp (l * ((n - n₀ : ℕ) * c)) := fun ω => by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul (hFb ω) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
      ((abs_nonneg _).trans (hFb ω))
    have h1 := (abs_le.1 (abs_sum_Ico_le h.abs_X_le n₀ n ω)).2
    have h2 : 0 ≤ ∑ j ∈ Finset.Ico n₀ (n + 1), u j ω :=
      Finset.sum_nonneg fun j _ => h.u_nonneg j ω
    nlinarith [mul_nonneg hκ0 h2]
  have hL : (fun ω => F ω * Real.exp (l * ∑ j ∈ Finset.Ico n₀ (n + 1), X j ω -
      κ * ∑ j ∈ Finset.Ico n₀ (n + 1), u j ω)) = fun ω => G ω * Real.exp (l * X n ω) := by
    ext ω
    simp only [hG, Finset.sum_Ico_succ_top hn]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hR : (fun ω => F ω * Real.exp (l * ∑ j ∈ Finset.Ico n₀ n, X j ω -
      κ * ∑ j ∈ Finset.Ico n₀ n, u j ω)) = fun ω => G ω * Real.exp (κ * u n ω) := by
    ext ω
    simp only [hG, Finset.sum_Ico_succ_top hn]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hL, hR]
  exact integral_mul_exp_le (hGm.mono (ℱ.le n) le_rfl) hG0 hGb
    ((h.meas_X n).mono (ℱ.le (n + 1)) le_rfl) hc (h.abs_X_le n)
    ((h.meas_u n).mono (ℱ.le n) le_rfl) (h.u_nonneg n) (h.u_le n)
    (h.orth n G _ hGm hGb) (hv n G _ hGm hG0 hGb) hl hlc hκ

/-- **The exponential supermartingale, lower step**: under `IsBddMartDiff` with `B = c²` and
`IsVarGe`, for `0 ≤ λ`, `λc ≤ 1`, `κ ≤ λ²(1 − 2λc)/2` and bounded `𝓕ₙ`-measurable `F ≥ 0`,
`∫ F exp(λ Sₙ − κ Vₙ) ≤ ∫ F exp(λ S_{n+1} − κ V_{n+1})`. -/
theorem IsBddMartDiff.integral_exp_succ_ge {Q : Measure Ω} [IsFiniteMeasure Q]
    {ℱ : Filtration ℕ mΩ} {X u : ℕ → Ω → ℝ} {c : ℝ} (h : IsBddMartDiff Q ℱ X u c (c ^ 2))
    (hv : IsVarGe Q ℱ X u) (hc : 0 ≤ c) {l κ : ℝ} (hl : 0 ≤ l) (hlc : l * c ≤ 1)
    (hκ : κ ≤ l ^ 2 * (1 - 2 * (l * c)) / 2) {n₀ n : ℕ} (hn : n₀ ≤ n) {F : Ω → ℝ} {C : ℝ}
    (hFm : Measurable[ℱ n] F) (hF0 : ∀ ω, 0 ≤ F ω) (hFb : ∀ ω, |F ω| ≤ C) :
    ∫ ω, F ω * Real.exp (l * ∑ j ∈ Finset.Ico n₀ n, X j ω -
        κ * ∑ j ∈ Finset.Ico n₀ n, u j ω) ∂Q ≤
      ∫ ω, F ω * Real.exp (l * ∑ j ∈ Finset.Ico n₀ (n + 1), X j ω -
        κ * ∑ j ∈ Finset.Ico n₀ (n + 1), u j ω) ∂Q := by
  set G : Ω → ℝ := fun ω => F ω * Real.exp (l * ∑ j ∈ Finset.Ico n₀ n, X j ω -
    κ * ∑ j ∈ Finset.Ico n₀ (n + 1), u j ω) with hG
  have hGm : Measurable[ℱ n] G :=
    hFm.mul (Real.continuous_exp.measurable.comp (((measurable_sum_Ico h.meas_X n₀ n).const_mul
      l).sub ((measurable_sum_Ico_succ h.meas_u n₀ n).const_mul κ)))
  have hG0 : ∀ ω, 0 ≤ G ω := fun ω => mul_nonneg (hF0 ω) (Real.exp_pos _).le
  have hGb : ∀ ω, |G ω| ≤
      C * Real.exp (l * ((n - n₀ : ℕ) * c) + |κ| * ((n + 1 - n₀ : ℕ) * c ^ 2)) := fun ω => by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul (hFb ω) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
      ((abs_nonneg _).trans (hFb ω))
    have h1 := (abs_le.1 (abs_sum_Ico_le h.abs_X_le n₀ n ω)).2
    have h2 : |∑ j ∈ Finset.Ico n₀ (n + 1), u j ω| ≤ (n + 1 - n₀ : ℕ) * c ^ 2 :=
      abs_sum_Ico_le (fun j ω => by rw [abs_of_nonneg (h.u_nonneg j ω)]; exact h.u_le j ω)
        n₀ (n + 1) ω
    have h3 : -(κ * ∑ j ∈ Finset.Ico n₀ (n + 1), u j ω) ≤
        |κ| * ((n + 1 - n₀ : ℕ) * c ^ 2) := by
      refine (neg_le_abs _).trans ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    nlinarith
  have hL : (fun ω => F ω * Real.exp (l * ∑ j ∈ Finset.Ico n₀ (n + 1), X j ω -
      κ * ∑ j ∈ Finset.Ico n₀ (n + 1), u j ω)) = fun ω => G ω * Real.exp (l * X n ω) := by
    ext ω
    simp only [hG, Finset.sum_Ico_succ_top hn]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hR : (fun ω => F ω * Real.exp (l * ∑ j ∈ Finset.Ico n₀ n, X j ω -
      κ * ∑ j ∈ Finset.Ico n₀ n, u j ω)) = fun ω => G ω * Real.exp (κ * u n ω) := by
    ext ω
    simp only [hG, Finset.sum_Ico_succ_top hn]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hL, hR]
  exact integral_mul_exp_ge (hGm.mono (ℱ.le n) le_rfl) hG0 hGb
    ((h.meas_X n).mono (ℱ.le (n + 1)) le_rfl) hc (h.abs_X_le n)
    ((h.meas_u n).mono (ℱ.le n) le_rfl) (h.u_nonneg n) (h.u_le n)
    (h.orth n G _ hGm hGb) (hv n G _ hGm hG0 hGb) hl hlc hκ

/-- **The exponential supermartingale bound**: under `IsBddMartDiff` and `IsVarLe`, for
bounded `𝓕_{n₀}`-measurable `F ≥ 0` and `n ≥ n₀`, `∫ F exp(λ Sₙ − κ Vₙ) ≤ ∫ F`. -/
theorem IsBddMartDiff.integral_exp_le {Q : Measure Ω} [IsFiniteMeasure Q]
    {ℱ : Filtration ℕ mΩ} {X u : ℕ → Ω → ℝ} {c B : ℝ} (h : IsBddMartDiff Q ℱ X u c B)
    (hv : IsVarLe Q ℱ X u) (hc : 0 ≤ c) {l κ : ℝ} (hl : 0 ≤ l) (hlc : l * c ≤ 1)
    (hκ : l ^ 2 * (1 + l * c) / 2 ≤ κ) {n₀ n : ℕ} (hn : n₀ ≤ n) {F : Ω → ℝ} {C : ℝ}
    (hFm : Measurable[ℱ n₀] F) (hF0 : ∀ ω, 0 ≤ F ω) (hFb : ∀ ω, |F ω| ≤ C) :
    ∫ ω, F ω * Real.exp (l * ∑ j ∈ Finset.Ico n₀ n, X j ω -
        κ * ∑ j ∈ Finset.Ico n₀ n, u j ω) ∂Q ≤ ∫ ω, F ω ∂Q := by
  induction n, hn using Nat.le_induction with
  | base => simp only [Finset.Ico_self, Finset.sum_empty, mul_zero, sub_zero, Real.exp_zero,
      mul_one, le_refl]
  | succ n hn ih =>
    exact (h.integral_exp_succ_le hv hc hl hlc hκ hn (hFm.mono (ℱ.mono hn) le_rfl) hF0
      hFb).trans ih

/-- **The exponential submartingale bound**: under `IsBddMartDiff` with `B = c²` and `IsVarGe`,
for bounded `𝓕_{n₀}`-measurable `F ≥ 0` and `n ≥ n₀`, `∫ F ≤ ∫ F exp(λ Sₙ − κ Vₙ)`. -/
theorem IsBddMartDiff.integral_exp_ge {Q : Measure Ω} [IsFiniteMeasure Q]
    {ℱ : Filtration ℕ mΩ} {X u : ℕ → Ω → ℝ} {c : ℝ} (h : IsBddMartDiff Q ℱ X u c (c ^ 2))
    (hv : IsVarGe Q ℱ X u) (hc : 0 ≤ c) {l κ : ℝ} (hl : 0 ≤ l) (hlc : l * c ≤ 1)
    (hκ : κ ≤ l ^ 2 * (1 - 2 * (l * c)) / 2) {n₀ n : ℕ} (hn : n₀ ≤ n) {F : Ω → ℝ} {C : ℝ}
    (hFm : Measurable[ℱ n₀] F) (hF0 : ∀ ω, 0 ≤ F ω) (hFb : ∀ ω, |F ω| ≤ C) :
    ∫ ω, F ω ∂Q ≤ ∫ ω, F ω * Real.exp (l * ∑ j ∈ Finset.Ico n₀ n, X j ω -
        κ * ∑ j ∈ Finset.Ico n₀ n, u j ω) ∂Q := by
  induction n, hn using Nat.le_induction with
  | base => simp only [Finset.Ico_self, Finset.sum_empty, mul_zero, sub_zero, Real.exp_zero,
      mul_one, le_refl]
  | succ n hn ih =>
    exact ih.trans (h.integral_exp_succ_ge hv hc hl hlc hκ hn (hFm.mono (ℱ.mono hn) le_rfl)
      hF0 hFb)

/-! ### Weighted martingale differences -/

/-- Restricting martingale differences to `𝓕ⱼ`-measurable events `Aⱼ` (the martingale
transform by the predictable indicators `1_{Aⱼ}`) keeps `IsBddMartDiff`. -/
theorem IsBddMartDiff.indicator {Q : Measure Ω} {ℱ : Filtration ℕ mΩ} {X u : ℕ → Ω → ℝ}
    {c B : ℝ} (h : IsBddMartDiff Q ℱ X u c B) (hc : 0 ≤ c) (hB : 0 ≤ B) {A : ℕ → Set Ω}
    (hA : ∀ j, MeasurableSet[ℱ j] (A j)) :
    IsBddMartDiff Q ℱ (fun j => (A j).indicator (X j)) (fun j => (A j).indicator (u j)) c B where
  meas_X j := (h.meas_X j).indicator (ℱ.mono (Nat.le_succ j) _ (hA j))
  meas_u j := (h.meas_u j).indicator (hA j)
  abs_X_le j ω := by
    by_cases hω : ω ∈ A j
    · rw [indicator_of_mem hω]; exact h.abs_X_le j ω
    · rw [indicator_of_notMem hω, abs_zero]; exact hc
  u_nonneg j ω := by
    by_cases hω : ω ∈ A j
    · rw [indicator_of_mem hω]; exact h.u_nonneg j ω
    · rw [indicator_of_notMem hω]
  u_le j ω := by
    by_cases hω : ω ∈ A j
    · rw [indicator_of_mem hω]; exact h.u_le j ω
    · rw [indicator_of_notMem hω]; exact hB
  orth j F C hFm hFb := by
    have e : (fun ω => F ω * (A j).indicator (X j) ω) =
        fun ω => (A j).indicator F ω * X j ω := by
      ext ω
      by_cases hω : ω ∈ A j
      · rw [indicator_of_mem hω, indicator_of_mem hω]
      · rw [indicator_of_notMem hω, indicator_of_notMem hω, mul_zero, zero_mul]
    rw [e]
    refine h.orth j _ C (hFm.indicator (hA j)) fun ω => ?_
    by_cases hω : ω ∈ A j
    · rw [indicator_of_mem hω]; exact hFb ω
    · rw [indicator_of_notMem hω, abs_zero]; exact (abs_nonneg _).trans (hFb ω)

/-- Restricting to `𝓕ⱼ`-measurable events keeps `IsVarLe`. -/
theorem IsVarLe.indicator {Q : Measure Ω} {ℱ : Filtration ℕ mΩ} {X u : ℕ → Ω → ℝ}
    (h : IsVarLe Q ℱ X u) {A : ℕ → Set Ω} (hA : ∀ j, MeasurableSet[ℱ j] (A j)) :
    IsVarLe Q ℱ (fun j => (A j).indicator (X j)) (fun j => (A j).indicator (u j)) := by
  intro j F C hFm hF0 hFb
  have e1 : (fun ω => F ω * (A j).indicator (X j) ω ^ 2) =
      fun ω => (A j).indicator F ω * X j ω ^ 2 := by
    ext ω
    by_cases hω : ω ∈ A j
    · rw [indicator_of_mem hω, indicator_of_mem hω]
    · rw [indicator_of_notMem hω, indicator_of_notMem hω]; ring
  have e2 : (fun ω => F ω * (A j).indicator (u j) ω) =
      fun ω => (A j).indicator F ω * u j ω := by
    ext ω
    by_cases hω : ω ∈ A j
    · rw [indicator_of_mem hω, indicator_of_mem hω]
    · rw [indicator_of_notMem hω, indicator_of_notMem hω, mul_zero, zero_mul]
  rw [e1, e2]
  refine h j _ C (hFm.indicator (hA j)) (fun ω => ?_) fun ω => ?_
  · by_cases hω : ω ∈ A j
    · rw [indicator_of_mem hω]; exact hF0 ω
    · rw [indicator_of_notMem hω]
  · by_cases hω : ω ∈ A j
    · rw [indicator_of_mem hω]; exact hFb ω
    · rw [indicator_of_notMem hω, abs_zero]; exact (abs_nonneg _).trans (hFb ω)

/-- Restricting to `𝓕ⱼ`-measurable events keeps `IsVarGe`. -/
theorem IsVarGe.indicator {Q : Measure Ω} {ℱ : Filtration ℕ mΩ} {X u : ℕ → Ω → ℝ}
    (h : IsVarGe Q ℱ X u) {A : ℕ → Set Ω} (hA : ∀ j, MeasurableSet[ℱ j] (A j)) :
    IsVarGe Q ℱ (fun j => (A j).indicator (X j)) (fun j => (A j).indicator (u j)) := by
  intro j F C hFm hF0 hFb
  have e1 : (fun ω => F ω * (A j).indicator (X j) ω ^ 2) =
      fun ω => (A j).indicator F ω * X j ω ^ 2 := by
    ext ω
    by_cases hω : ω ∈ A j
    · rw [indicator_of_mem hω, indicator_of_mem hω]
    · rw [indicator_of_notMem hω, indicator_of_notMem hω]; ring
  have e2 : (fun ω => F ω * (A j).indicator (u j) ω) =
      fun ω => (A j).indicator F ω * u j ω := by
    ext ω
    by_cases hω : ω ∈ A j
    · rw [indicator_of_mem hω, indicator_of_mem hω]
    · rw [indicator_of_notMem hω, indicator_of_notMem hω, mul_zero, zero_mul]
  rw [e1, e2]
  refine h j _ C (hFm.indicator (hA j)) (fun ω => ?_) fun ω => ?_
  · by_cases hω : ω ∈ A j
    · rw [indicator_of_mem hω]; exact hF0 ω
    · rw [indicator_of_notMem hω]
  · by_cases hω : ω ∈ A j
    · rw [indicator_of_mem hω]; exact hFb ω
    · rw [indicator_of_notMem hω, abs_zero]; exact (abs_nonneg _).trans (hFb ω)

/-! ### Ville's maximal inequality -/

/-- `∫ 1_B f = ∫_B f`. -/
theorem integral_indicator_one_mul {Q : Measure Ω} {B : Set Ω} (hB : MeasurableSet B)
    (f : Ω → ℝ) : ∫ ω, B.indicator (fun _ => (1 : ℝ)) ω * f ω ∂Q = ∫ ω in B, f ω ∂Q := by
  rw [← integral_indicator hB]
  congr 1
  ext ω
  by_cases hω : ω ∈ B
  · rw [indicator_of_mem hω, indicator_of_mem hω, one_mul]
  · rw [indicator_of_notMem hω, indicator_of_notMem hω, zero_mul]

/-- **Ville's maximal inequality** for non-negative supermartingales, in the integrated form
`∫_B M_{n+1} ≤ ∫_B Mₙ` for `B ∈ 𝓕ₙ`: `a P(∃ n ≤ N, Mₙ ≥ a) ≤ E[M₀]`. The proof is the
first-passage argument. -/
theorem measureReal_exists_ge_le {Q : Measure Ω} [IsFiniteMeasure Q] {ℱ : Filtration ℕ mΩ}
    {M : ℕ → Ω → ℝ} (hMm : ∀ n, Measurable[ℱ n] (M n)) (hM0 : ∀ n ω, 0 ≤ M n ω)
    (hMi : ∀ n, Integrable (M n) Q)
    (hsup : ∀ n (B : Set Ω), MeasurableSet[ℱ n] B →
      ∫ ω in B, M (n + 1) ω ∂Q ≤ ∫ ω in B, M n ω ∂Q) (a : ℝ) (N : ℕ) :
    a * Q.real {ω | ∃ n ≤ N, a ≤ M n ω} ≤ ∫ ω, M 0 ω ∂Q := by
  set H : ℕ → Set Ω := fun n => {ω | ∀ k < n, M k ω < a} with hH
  set E : ℕ → Set Ω := fun n => {ω | ∃ k < n, a ≤ M k ω} with hE
  set T : ℕ → Set Ω := fun n => H n ∩ {ω | a ≤ M n ω} with hT
  have hHm : ∀ n, MeasurableSet[ℱ n] (H n) := fun n => by
    have e : H n = ⋂ k ∈ Finset.range n, M k ⁻¹' Iio a := by
      ext ω
      simp only [hH, mem_ofPred_eq, mem_iInter, Finset.mem_range, mem_preimage, mem_Iio]
    rw [e]
    exact Finset.measurableSet_biInter _ fun k hk =>
      ℱ.mono (Finset.mem_range.1 hk).le _ (hMm k measurableSet_Iio)
  have hHm' : ∀ n, MeasurableSet (H n) := fun n => ℱ.le n _ (hHm n)
  have hTm : ∀ n, MeasurableSet (T n) := fun n =>
    (hHm' n).inter ((hMm n).mono (ℱ.le n) le_rfl measurableSet_Ici)
  have hH1 : ∀ n, H (n + 1) = H n \ T n := fun n => by
    ext ω
    simp only [hH, hT, mem_ofPred_eq, Set.mem_sdiff, mem_inter_iff]
    constructor
    · intro h
      exact ⟨fun k hk => h k (by omega), fun hT' => absurd hT'.2 (not_le.2 (h n (by omega)))⟩
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
      · exact h1 k hk
      · rw [hk]; exact lt_of_not_ge fun h3 => h2 ⟨h1, h3⟩
  have hE1 : ∀ n, E (n + 1) = E n ∪ T n := fun n => by
    ext ω
    simp only [hE, hT, hH, mem_ofPred_eq, mem_union, mem_inter_iff]
    constructor
    · rintro ⟨k, hk, hak⟩
      by_cases hex : ∃ k < n, a ≤ M k ω
      · exact Or.inl hex
      · push Not at hex
        right
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
        · exact absurd hak (not_le.2 (hex k hk))
        · rw [hk] at hak; exact ⟨hex, hak⟩
    · rintro (⟨k, hk, hak⟩ | ⟨_, hak⟩)
      · exact ⟨k, by omega, hak⟩
      · exact ⟨n, by omega, hak⟩
  have hdisj : ∀ n, Disjoint (E n) (T n) := fun n => by
    rw [Set.disjoint_left]
    rintro ω ⟨k, hk, hak⟩ ⟨hH', _⟩
    exact absurd hak (not_le.2 (hH' k hk))
  have hclaim : ∀ n, a * Q.real (E n) + ∫ ω in H n, M n ω ∂Q ≤ ∫ ω, M 0 ω ∂Q := by
    intro n
    induction n with
    | zero =>
      have e1 : E 0 = ∅ := by
        ext ω; simp only [hE, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_exists]
        intro k hk; omega
      have e2 : H 0 = univ := by
        ext ω; simp only [hH, mem_ofPred_eq, mem_univ, iff_true]
        intro k hk; omega
      rw [e1, e2, measureReal_empty, mul_zero, zero_add, setIntegral_univ]
    | succ n ih =>
      have hTn : MeasurableSet[ℱ n] (T n) := (hHm n).inter (hMm n measurableSet_Ici)
      have h1 : ∫ ω in H (n + 1), M (n + 1) ω ∂Q ≤ ∫ ω in H (n + 1), M n ω ∂Q :=
        hsup n _ (by rw [hH1 n]; exact (hHm n).diff hTn)
      have h2 : ∫ ω in H n, M n ω ∂Q = ∫ ω in H (n + 1), M n ω ∂Q + ∫ ω in T n, M n ω ∂Q := by
        rw [← setIntegral_union (disjoint_sdiff_left.mono_left (by rw [hH1 n]))
          (hTm n) (hMi n).integrableOn (hMi n).integrableOn]
        congr 1
        rw [hH1 n, sdiff_union_of_subset inter_subset_left]
      have h3 : a * Q.real (T n) ≤ ∫ ω in T n, M n ω ∂Q :=
        setIntegral_ge_of_const_le_real (hTm n) (measure_ne_top _ _)
          (fun ω hω => hω.2) (hMi n).integrableOn
      have h4 : Q.real (E (n + 1)) = Q.real (E n) + Q.real (T n) := by
        rw [hE1 n]
        exact measureReal_union₀ (hTm n).nullMeasurableSet (hdisj n).aedisjoint
      rw [h4]
      nlinarith
  have hfin := hclaim (N + 1)
  have he : {ω | ∃ n ≤ N, a ≤ M n ω} = E (N + 1) := by
    ext ω
    simp only [hE, mem_ofPred_eq]
    constructor
    · rintro ⟨k, hk, h⟩; exact ⟨k, by omega, h⟩
    · rintro ⟨k, hk, h⟩; exact ⟨k, by omega, h⟩
  rw [he]
  have : 0 ≤ ∫ ω in H (N + 1), M (N + 1) ω ∂Q := setIntegral_nonneg (hHm' _) fun ω _ => hM0 _ ω
  linarith

/-! ### Conditional expectations against bounded weights -/

/-- `∫ g E[f | m] = ∫ g f` for bounded `m`-measurable `g` (the pull-out property). -/
theorem integral_mul_condExp {Q : Measure Ω} [IsFiniteMeasure Q] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {g f : Ω → ℝ} (hg : Measurable[m] g) {C : ℝ} (hgb : ∀ ω, |g ω| ≤ C)
    (hf : Integrable f Q) : ∫ ω, g ω * Q[f | m] ω ∂Q = ∫ ω, g ω * f ω ∂Q := by
  have h1 : Q[g * f | m] =ᵐ[Q] g * Q[f | m] :=
    condExp_stronglyMeasurable_mul_of_bound hm hg.stronglyMeasurable hf C
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hgb ω)
  calc ∫ ω, g ω * Q[f | m] ω ∂Q = ∫ ω, Q[g * f | m] ω ∂Q :=
        (integral_congr_ae h1).symm
    _ = ∫ ω, (g * f) ω ∂Q := integral_condExp hm
    _ = ∫ ω, g ω * f ω ∂Q := rfl

/-- The clamp `x ↦ max (−b) (min b x)` to `[−b, b]`. -/
noncomputable def clampAbs (b x : ℝ) : ℝ := max (-b) (min b x)

/-- The clamp is measurable. -/
theorem measurable_clampAbs (b : ℝ) : Measurable (clampAbs b) :=
  measurable_const.max (measurable_const.min measurable_id)

/-- `|clamp_b x| ≤ b` for `b ≥ 0`. -/
theorem abs_clampAbs_le {b : ℝ} (hb : 0 ≤ b) (x : ℝ) : |clampAbs b x| ≤ b :=
  abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- `|clamp_b x| ≤ |x|` for `b ≥ 0`. -/
theorem abs_clampAbs_le_abs {b : ℝ} (hb : 0 ≤ b) (x : ℝ) : |clampAbs b x| ≤ |x| :=
  abs_le.2 ⟨le_max_of_le_right (le_min (by linarith [abs_nonneg x]) (neg_abs_le x)),
    max_le (by linarith [abs_nonneg x]) ((min_le_right _ _).trans (le_abs_self x))⟩

/-- The clamp does not move points of `[−b, b]`. -/
theorem clampAbs_of_abs_le {b x : ℝ} (h : |x| ≤ b) : clampAbs b x = x := by
  rw [clampAbs, min_eq_right (abs_le.1 h).2, max_eq_right (abs_le.1 h).1]

/-! ### Threshold sums -/

omit mΩ in
/-- **Threshold sums**: for `vⱼ ≥ 0`, `Wₙ = Σ_{j<n} vⱼ` and `b ≥ 0`, the sum
`Rₙ = Σ_{j<n} vⱼ 1{W_{j+1} ≤ b}` satisfies `Rₙ ≤ b`, `Rₙ = Wₙ` when `Wₙ ≤ b`, and
`Rₙ ≥ min(Wₙ, b − c)` when every `vⱼ ≤ c`. -/
theorem sum_ite_threshold {v : ℕ → ℝ} (hv : ∀ j, 0 ≤ v j) {b c : ℝ} (hb : 0 ≤ b)
    (hvc : ∀ j, v j ≤ c) (n : ℕ) :
    (∑ j ∈ Finset.range n, (if ∑ i ∈ Finset.range (j + 1), v i ≤ b then v j else 0)) ≤ b ∧
      (∑ i ∈ Finset.range n, v i ≤ b →
        ∑ j ∈ Finset.range n, (if ∑ i ∈ Finset.range (j + 1), v i ≤ b then v j else 0) =
          ∑ i ∈ Finset.range n, v i) ∧
      min (∑ i ∈ Finset.range n, v i) (b - c) ≤
        ∑ j ∈ Finset.range n, (if ∑ i ∈ Finset.range (j + 1), v i ≤ b then v j else 0) := by
  induction n with
  | zero =>
    refine ⟨?_, fun _ => ?_, ?_⟩
    · rw [Finset.sum_range_zero]; exact hb
    · rw [Finset.sum_range_zero, Finset.sum_range_zero]
    · rw [Finset.sum_range_zero, Finset.sum_range_zero]; exact min_le_left _ _
  | succ n ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    rw [Finset.sum_range_succ (fun j => if ∑ i ∈ Finset.range (j + 1), v i ≤ b then v j else 0)]
    have hW : ∑ i ∈ Finset.range (n + 1), v i = ∑ i ∈ Finset.range n, v i + v n :=
      Finset.sum_range_succ v n
    by_cases h : ∑ i ∈ Finset.range (n + 1), v i ≤ b
    · have hn : ∑ i ∈ Finset.range n, v i ≤ b := by linarith [hv n]
      have e := ih2 hn
      simp only [h, ite_true]
      rw [e, ← hW]
      exact ⟨h, fun _ => rfl, min_le_left _ _⟩
    · simp only [h, ite_false, add_zero]
      refine ⟨ih1, fun h' => False.elim h', ?_⟩
      push Not at h
      by_cases hn : ∑ i ∈ Finset.range n, v i ≤ b
      · rw [ih2 hn]
        have := hvc n
        exact (min_le_right _ _).trans (by linarith)
      · push Not at hn
        have : min (∑ i ∈ Finset.range n, v i) (b - c) = b - c := by
          rw [min_eq_right]; linarith [hvc n, hv n]
        rw [this] at ih3
        exact (min_le_right _ _).trans ih3

/-! ### Truncated martingale differences -/

/-- The conditional mean `E[Dⱼ 1{|Dⱼ| ≤ bⱼ} | 𝓕ⱼ]` of the truncated difference, clamped to
`[−bⱼ, bⱼ]` (which changes it only on a null set). -/
noncomputable def truncMean (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) (b : ℕ → ℝ)
    (j : ℕ) (ω : Ω) : ℝ :=
  clampAbs (b j) (Q[fun ω => lilTrunc (b j) (D j ω) | ℱ j] ω)

/-- The truncated recentred martingale differences
`Dⱼ 1{|Dⱼ| ≤ bⱼ} − E[Dⱼ 1{|Dⱼ| ≤ bⱼ} | 𝓕ⱼ]`. -/
noncomputable def truncMD (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) (b : ℕ → ℝ)
    (j : ℕ) (ω : Ω) : ℝ :=
  lilTrunc (b j) (D j ω) - truncMean Q ℱ D b j ω

/-- The clamped conditional mean is `𝓕ⱼ`-measurable. -/
theorem measurable_truncMean (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ)
    (b : ℕ → ℝ) (j : ℕ) : Measurable[ℱ j] (truncMean Q ℱ D b j) :=
  (measurable_clampAbs (b j)).comp stronglyMeasurable_condExp.measurable

/-- The clamped conditional mean is at most `bⱼ` in absolute value. -/
theorem abs_truncMean_le (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) {b : ℕ → ℝ}
    (hb : ∀ j, 0 ≤ b j) (j : ℕ) (ω : Ω) : |truncMean Q ℱ D b j ω| ≤ b j :=
  abs_clampAbs_le (hb j) _

/-- The clamped conditional mean is a version of the conditional mean. -/
theorem truncMean_ae_eq {Q : Measure Ω} [IsFiniteMeasure Q] (ℱ : Filtration ℕ mΩ)
    (D : ℕ → Ω → ℝ) {b : ℕ → ℝ} (hb : ∀ j, 0 ≤ b j) (j : ℕ) :
    truncMean Q ℱ D b j =ᵐ[Q] Q[fun ω => lilTrunc (b j) (D j ω) | ℱ j] := by
  filter_upwards [ae_bdd_abs_condExp_of_ae_bdd_abs (μ := Q) (m := ℱ j)
    (f := fun ω => lilTrunc (b j) (D j ω)) (R := b j)
    (Eventually.of_forall fun ω => abs_lilTrunc_le (hb j) _)] with ω hω
  exact clampAbs_of_abs_le hω

/-- The truncated differences are `𝓕ⱼ₊₁`-measurable. -/
theorem measurable_truncMD (Q : Measure Ω) {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ}
    (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k)) (b : ℕ → ℝ) (j : ℕ) :
    Measurable[ℱ (j + 1)] (truncMD Q ℱ D b j) :=
  ((measurable_lilTrunc (b j)).comp (hD j).measurable).sub
    ((measurable_truncMean Q ℱ D b j).mono (ℱ.mono (Nat.le_succ j)) le_rfl)

/-- `|truncMD| ≤ 2bⱼ`. -/
theorem abs_truncMD_le (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) {b : ℕ → ℝ}
    (hb : ∀ j, 0 ≤ b j) (j : ℕ) (ω : Ω) : |truncMD Q ℱ D b j ω| ≤ 2 * b j := by
  have h1 := abs_lilTrunc_le (hb j) (D j ω)
  have h2 := abs_truncMean_le Q ℱ D hb j ω
  calc |truncMD Q ℱ D b j ω| ≤ |lilTrunc (b j) (D j ω)| + |truncMean Q ℱ D b j ω| :=
        abs_sub _ _
    _ ≤ 2 * b j := by linarith

/-- `∫ F mⱼ = ∫ F Dⱼ 1{|Dⱼ| ≤ bⱼ}` for the clamped mean `mⱼ` and bounded `𝓕ⱼ`-measurable `F`. -/
theorem integral_mul_truncMean {Q : Measure Ω} [IsFiniteMeasure Q] {ℱ : Filtration ℕ mΩ}
    {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k)) {b : ℕ → ℝ}
    (hb : ∀ j, 0 ≤ b j) (j : ℕ) {F : Ω → ℝ} {C : ℝ} (hFm : Measurable[ℱ j] F)
    (hFb : ∀ ω, |F ω| ≤ C) :
    ∫ ω, F ω * truncMean Q ℱ D b j ω ∂Q = ∫ ω, F ω * lilTrunc (b j) (D j ω) ∂Q := by
  have hTi : Integrable (fun ω => lilTrunc (b j) (D j ω)) Q :=
    integrable_of_abs_le ((measurable_lilTrunc _).comp ((hD j).measurable.mono (ℱ.le _)
      le_rfl)) fun ω => abs_lilTrunc_le (hb j) _
  rw [← integral_mul_condExp (ℱ.le j) hFm hFb hTi]
  refine integral_congr_ae ?_
  filter_upwards [truncMean_ae_eq ℱ D hb j] with ω hω
  rw [hω]

/-- **The truncated differences are martingale differences**: `∫ F · truncMD = 0` for bounded
`𝓕ⱼ`-measurable `F`. -/
theorem integral_mul_truncMD {Q : Measure Ω} [IsFiniteMeasure Q] {ℱ : Filtration ℕ mΩ}
    {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k)) {b : ℕ → ℝ}
    (hb : ∀ j, 0 ≤ b j) (j : ℕ) {F : Ω → ℝ} {C : ℝ} (hFm : Measurable[ℱ j] F)
    (hFb : ∀ ω, |F ω| ≤ C) : ∫ ω, F ω * truncMD Q ℱ D b j ω ∂Q = 0 := by
  have hDm : Measurable (D j) := (hD j).measurable.mono (ℱ.le _) le_rfl
  have hFm' : Measurable F := hFm.mono (ℱ.le j) le_rfl
  have hTb : ∀ ω, |lilTrunc (b j) (D j ω)| ≤ b j := fun ω => abs_lilTrunc_le (hb j) _
  have h1 : Integrable (fun ω => F ω * lilTrunc (b j) (D j ω)) Q :=
    integrable_mul_of_abs_le hFm' ((measurable_lilTrunc _).comp hDm) hFb hTb
  have h2 : Integrable (fun ω => F ω * truncMean Q ℱ D b j ω) Q :=
    integrable_mul_of_abs_le hFm' ((measurable_truncMean Q ℱ D b j).mono (ℱ.le j) le_rfl) hFb
      (abs_truncMean_le Q ℱ D hb j)
  have e : (fun ω => F ω * truncMD Q ℱ D b j ω) =
      fun ω => F ω * lilTrunc (b j) (D j ω) - F ω * truncMean Q ℱ D b j ω := by
    ext ω; rw [truncMD, mul_sub]
  rw [e, integral_sub h1 h2, integral_mul_truncMean hD hb j hFm hFb, sub_self]

/-- **The conditional variance of the truncated differences**: for bounded `𝓕ⱼ`-measurable
`F ≥ 0`, `∫ F truncMD² = ∫ F Tⱼ² − ∫ F mⱼ²`, `Tⱼ = Dⱼ 1{|Dⱼ| ≤ bⱼ}`, `mⱼ` the clamped mean. -/
theorem integral_mul_truncMD_sq {Q : Measure Ω} [IsFiniteMeasure Q] {ℱ : Filtration ℕ mΩ}
    {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k)) {b : ℕ → ℝ}
    (hb : ∀ j, 0 ≤ b j) (j : ℕ) {F : Ω → ℝ} {C : ℝ} (hFm : Measurable[ℱ j] F)
    (hFb : ∀ ω, |F ω| ≤ C) :
    ∫ ω, F ω * truncMD Q ℱ D b j ω ^ 2 ∂Q =
      ∫ ω, F ω * lilTrunc (b j) (D j ω) ^ 2 ∂Q - ∫ ω, F ω * truncMean Q ℱ D b j ω ^ 2 ∂Q := by
  have hDm : Measurable (D j) := (hD j).measurable.mono (ℱ.le _) le_rfl
  have hFm' : Measurable F := hFm.mono (ℱ.le j) le_rfl
  set T : Ω → ℝ := fun ω => lilTrunc (b j) (D j ω) with hT
  set m : Ω → ℝ := truncMean Q ℱ D b j with hm
  have hTm : Measurable T := (measurable_lilTrunc _).comp hDm
  have hmm : Measurable[ℱ j] m := measurable_truncMean Q ℱ D b j
  have hmm' : Measurable m := hmm.mono (ℱ.le j) le_rfl
  have hTb : ∀ ω, |T ω| ≤ b j := fun ω => abs_lilTrunc_le (hb j) _
  have hmb : ∀ ω, |m ω| ≤ b j := abs_truncMean_le Q ℱ D hb j
  have hT2b : ∀ ω, |T ω ^ 2| ≤ b j ^ 2 := fun ω => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hTb ω) 2
  have hm2b : ∀ ω, |m ω ^ 2| ≤ b j ^ 2 := fun ω => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hmb ω) 2
  have hFmb : ∀ ω, |F ω * m ω| ≤ C * b j := fun ω => by
    rw [abs_mul]; exact mul_le_mul (hFb ω) (hmb ω) (abs_nonneg _) ((abs_nonneg _).trans (hFb ω))
  -- `∫ F m T = ∫ F m²`
  have hcross : ∫ ω, (F ω * m ω) * T ω ∂Q = ∫ ω, (F ω * m ω) * m ω ∂Q := by
    have := integral_mul_truncMean (Q := Q) hD hb j (hFm.mul hmm) hFmb
    exact this.symm
  have i1 : Integrable (fun ω => F ω * T ω ^ 2) Q :=
    integrable_mul_of_abs_le hFm' (hTm.pow_const 2) hFb hT2b
  have i2 : Integrable (fun ω => (F ω * m ω) * T ω) Q :=
    integrable_mul_of_abs_le (hFm'.mul hmm') hTm hFmb hTb
  have i3 : Integrable (fun ω => (F ω * m ω) * m ω) Q :=
    integrable_mul_of_abs_le (hFm'.mul hmm') hmm' hFmb hmb
  have i4 : Integrable (fun ω => F ω * m ω ^ 2) Q :=
    integrable_mul_of_abs_le hFm' (hmm'.pow_const 2) hFb hm2b
  have e : (fun ω => F ω * truncMD Q ℱ D b j ω ^ 2) =
      fun ω => F ω * T ω ^ 2 - 2 * ((F ω * m ω) * T ω) + (F ω * m ω) * m ω := by
    ext ω; simp only [truncMD, hT, hm]; ring
  have e2 : (fun ω => (F ω * m ω) * m ω) = fun ω => F ω * m ω ^ 2 := by
    ext ω; ring
  rw [e, integral_add (f := fun ω => F ω * T ω ^ 2 - 2 * ((F ω * m ω) * T ω))
    (g := fun ω => (F ω * m ω) * m ω) (i1.sub (i2.const_mul 2)) i3,
    integral_sub (f := fun ω => F ω * T ω ^ 2) (g := fun ω => 2 * ((F ω * m ω) * T ω)) i1
      (i2.const_mul 2), integral_const_mul, hcross, e2]
  ring

/-- The conditional variance `E[Dⱼ² | 𝓕ⱼ]`, made non-negative everywhere. -/
noncomputable def condVarMD (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) (j : ℕ)
    (ω : Ω) : ℝ :=
  max 0 (Q[fun ω => D j ω ^ 2 | ℱ j] ω)

/-- The conditional variance is `𝓕ⱼ`-measurable. -/
theorem measurable_condVarMD (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) (j : ℕ) :
    Measurable[ℱ j] (condVarMD Q ℱ D j) :=
  measurable_const.max stronglyMeasurable_condExp.measurable

/-- The conditional variance is non-negative. -/
theorem condVarMD_nonneg (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) (j : ℕ)
    (ω : Ω) : 0 ≤ condVarMD Q ℱ D j ω :=
  le_max_left _ _

/-- `condVarMD` is a version of `E[Dⱼ² | 𝓕ⱼ]`. -/
theorem condVarMD_ae_eq (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) (j : ℕ) :
    condVarMD Q ℱ D j =ᵐ[Q] Q[fun ω => D j ω ^ 2 | ℱ j] := by
  filter_upwards [condExp_nonneg (μ := Q) (m := ℱ j) (f := fun ω => D j ω ^ 2)
    (Eventually.of_forall fun ω => sq_nonneg (D j ω))] with ω hω
  exact max_eq_right hω

/-- `∫ F Dⱼ² = ∫ F E[Dⱼ² | 𝓕ⱼ]` for bounded `𝓕ⱼ`-measurable `F`. -/
theorem integral_mul_condVarMD {Q : Measure Ω} [IsFiniteMeasure Q] {ℱ : Filtration ℕ mΩ}
    {D : ℕ → Ω → ℝ} (hL2 : ∀ k, MemLp (D k) 2 Q) (j : ℕ) {F : Ω → ℝ} {C : ℝ}
    (hFm : Measurable[ℱ j] F) (hFb : ∀ ω, |F ω| ≤ C) :
    ∫ ω, F ω * condVarMD Q ℱ D j ω ∂Q = ∫ ω, F ω * D j ω ^ 2 ∂Q := by
  rw [← integral_mul_condExp (ℱ.le j) hFm hFb (hL2 j).integrable_sq]
  refine integral_congr_ae ?_
  filter_upwards [condVarMD_ae_eq Q ℱ D j] with ω hω
  rw [hω]

/-- **`E[Dⱼ²|𝓕ⱼ]` dominates the conditional variance of the truncated differences.** -/
theorem integral_mul_truncMD_sq_le {Q : Measure Ω} [IsFiniteMeasure Q] {ℱ : Filtration ℕ mΩ}
    {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) {b : ℕ → ℝ} (hb : ∀ j, 0 ≤ b j) (j : ℕ) {F : Ω → ℝ} {C : ℝ}
    (hFm : Measurable[ℱ j] F) (hF0 : ∀ ω, 0 ≤ F ω) (hFb : ∀ ω, |F ω| ≤ C) :
    ∫ ω, F ω * truncMD Q ℱ D b j ω ^ 2 ∂Q ≤ ∫ ω, F ω * condVarMD Q ℱ D j ω ∂Q := by
  have hDm : Measurable (D j) := (hD j).measurable.mono (ℱ.le _) le_rfl
  have hFm' : Measurable F := hFm.mono (ℱ.le j) le_rfl
  rw [integral_mul_truncMD_sq hD hb j hFm hFb, integral_mul_condVarMD hL2 j hFm hFb]
  have hmb : ∀ ω, |truncMean Q ℱ D b j ω ^ 2| ≤ b j ^ 2 := fun ω => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_truncMean_le Q ℱ D hb j ω) 2
  have h1 : 0 ≤ ∫ ω, F ω * truncMean Q ℱ D b j ω ^ 2 ∂Q :=
    integral_nonneg fun ω => mul_nonneg (hF0 ω) (sq_nonneg _)
  have h2 : ∫ ω, F ω * lilTrunc (b j) (D j ω) ^ 2 ∂Q ≤ ∫ ω, F ω * D j ω ^ 2 ∂Q := by
    refine integral_mono (integrable_mul_of_abs_le hFm' (((measurable_lilTrunc _).comp
      hDm).pow_const 2) hFb (G := b j ^ 2) fun ω => ?_) ?_ fun ω =>
        mul_le_mul_of_nonneg_left (lilTrunc_sq_le _ _) (hF0 ω)
    · rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_lilTrunc_le (hb j) _) 2
    · exact (hL2 j).integrable_sq.bdd_mul hFm'.aestronglyMeasurable
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hFb ω)
  linarith

/-- **The truncated tails are small**: if `E[Dⱼ | 𝓕ⱼ] = 0`, the clamped conditional mean
satisfies `E|mⱼ| ≤ E|Dⱼ − Dⱼ 1{|Dⱼ| ≤ bⱼ}|`. -/
theorem integral_abs_truncMean_le {Q : Measure Ω} [IsFiniteMeasure Q] {ℱ : Filtration ℕ mΩ}
    {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hint : ∀ k, Integrable (D k) Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0) {b : ℕ → ℝ}
    (hb : ∀ j, 0 ≤ b j) (j : ℕ) :
    ∫ ω, |truncMean Q ℱ D b j ω| ∂Q ≤ ∫ ω, |D j ω - lilTrunc (b j) (D j ω)| ∂Q := by
  have hDm : Measurable (D j) := (hD j).measurable.mono (ℱ.le _) le_rfl
  have hTi : Integrable (fun ω => lilTrunc (b j) (D j ω)) Q :=
    integrable_of_abs_le ((measurable_lilTrunc _).comp hDm) fun ω => abs_lilTrunc_le (hb j) _
  have hsub := condExp_sub (m := ℱ j) hTi (hint j)
  have hae : ∀ᵐ ω ∂Q, |truncMean Q ℱ D b j ω| ≤
      |Q[fun ω => lilTrunc (b j) (D j ω) - D j ω | ℱ j] ω| := by
    filter_upwards [hsub, h0 j] with ω h1 h2
    have h3 : Q[fun ω => lilTrunc (b j) (D j ω) - D j ω | ℱ j] ω =
        Q[fun ω => lilTrunc (b j) (D j ω) | ℱ j] ω := by
      rw [show (fun ω => lilTrunc (b j) (D j ω) - D j ω) =
        (fun ω => lilTrunc (b j) (D j ω)) - D j from rfl, h1, Pi.sub_apply, h2,
        Pi.zero_apply, sub_zero]
    rw [h3]
    exact abs_clampAbs_le_abs (hb j) _
  calc ∫ ω, |truncMean Q ℱ D b j ω| ∂Q
      ≤ ∫ ω, |Q[fun ω => lilTrunc (b j) (D j ω) - D j ω | ℱ j] ω| ∂Q :=
        integral_mono_ae (integrable_of_abs_le (continuous_abs.measurable.comp
          ((measurable_truncMean Q ℱ D b j).mono (ℱ.le j) le_rfl)) (C := b j) fun ω => by
            rw [abs_abs]; exact abs_truncMean_le Q ℱ D hb j ω)
          integrable_condExp.abs hae
    _ ≤ ∫ ω, |lilTrunc (b j) (D j ω) - D j ω| ∂Q := integral_abs_condExp_le _
    _ = ∫ ω, |D j ω - lilTrunc (b j) (D j ω)| ∂Q := by
        congr 1; ext ω; exact abs_sub_comm _ _

end MeynTweedie.GeneralizedDrift
