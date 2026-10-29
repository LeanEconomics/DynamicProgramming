/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.MartingaleLILTools

/-!
# Kolmogorov's lower bound and the blocks of the martingale LIL

Copied for Chapter 19 from the Chapter 17 project
(`LimitTheorems/MartingaleLILBlock.lean`), with the namespace changed to
`MeynTweedie.GeneralizedDrift` and the imports to `GeneralizedDrift.*`.

Tools for the lower half of the LIL for martingale differences (`MartingaleLILLower`, Stout,
*Ann. Math. Statist.* 41 (1970); Stout, *Almost Sure Convergence* (1974), §5.2–5.4), used for the
LIL of MT Theorems 17.0.1 (iv), 17.5.3 and 17.5.4 (pp. 422, 452) without a minorization.

The i.i.d. lower half (`LILLower`) uses the CLT on independent sub-blocks; for martingales the
blocks are not independent, and the proof here is Kolmogorov's lower exponential bound applied
conditionally on the past. A block started at `n₀` is the truncated martingale run until its
conditional variance reaches a budget `B` (`blockSet`, `blockSum`, `blockVar`); its conditional
variance then lies in `[B − c², B]` (`blockVar_bounds`), so the exponential super- and
submartingales of `MartingaleLILTools` give two-sided moment generating function bounds on every
`G ∈ 𝓕_{n₀}` (`setIntegral_exp_blockSum_le`, `setIntegral_exp_blockSum_ge`), and Kolmogorov's
argument turns these into a conditional lower tail bound (`mdBlock_lower_bound`). A conditional
second Borel–Cantelli lemma (`ae_frequently_of_cond_lower`) finishes the lower half.

* `integral_exp_le_split`, **`kolmogorov_lower`**: Kolmogorov's lower exponential bound
  `ν(Y > x) ≥ (ν(Ω)/2) e^{−x²(1+12h)/2} − error` from moment generating function bounds at three
  points.
* `truncVar` (the clamped conditional variance of `truncMD`), `truncVar_ae_eq`,
  `integral_mul_truncVar`, and `truncVar_ge`: almost surely
  `E[Dⱼ² | 𝓕ⱼ] − 2 E[Dⱼ² 1{Dⱼ² ≥ K} | 𝓕ⱼ] ≤ truncVar` when `K ≤ bⱼ²` (conditional Jensen).
* `isBddMartDiff_block`, `abs_blockSum_le`, `measurable_blockSum`, `blockSum_eq_of_budget`,
  `tendsto_measureReal_budget`, `setIntegral_exp_le_amgm`.
* **`mdBlock_lower_bound`**: `P(G ∩ A) ≥ (P(G)/2) e^{−x²(1+12h)/2}` for `G ∈ 𝓕_{n₀}`, where `A` is
  "the block sum over `[n₀, n₁)` exceeds `x√B`, or the budget is not used up in `[n₀, n₁)`".
* `truncMD_congr`, `truncVar_congr`, `blockSum_congr`, `exists_sum_indicator_eq` (a block is a
  partial sum `S_T − S_{n₀}`), `mem_blockSet_of_le`.
* **`ae_frequently_of_cond_lower`** (conditional second Borel–Cantelli lemma): if
  `P(G ∩ Aₖ) ≥ pₖ P(G)` for `G ∈ 𝓕_{nₖ}`, `Aₖ ∈ 𝓕_{n_{k+1}}` and `Σ pₖ = ∞`, then `Aₖ` i.o. a.s.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **The three-region split of the moment generating function**: for `0 ≤ t' ≤ t ≤ t''` and
any `x, M`, `∫ e^{tY} ≤ e^{(t−t')x} ∫ e^{t'Y} + e^{tM} ν(Y > x) + e^{−(t''−t)M} ∫ e^{t''Y}`. -/
theorem integral_exp_le_split {ν : Measure Ω} [IsFiniteMeasure ν] {Y : Ω → ℝ}
    (hYm : Measurable Y) {t' t t'' x M : ℝ} (ht' : 0 ≤ t') (ht : t' ≤ t) (ht'' : t ≤ t'')
    (hi' : Integrable (fun ω => Real.exp (t' * Y ω)) ν)
    (hi : Integrable (fun ω => Real.exp (t * Y ω)) ν)
    (hi'' : Integrable (fun ω => Real.exp (t'' * Y ω)) ν) :
    ∫ ω, Real.exp (t * Y ω) ∂ν ≤ Real.exp ((t - t') * x) * ∫ ω, Real.exp (t' * Y ω) ∂ν +
      Real.exp (t * M) * ν.real {ω | x < Y ω} +
        Real.exp (-((t'' - t) * M)) * ∫ ω, Real.exp (t'' * Y ω) ∂ν := by
  have hS : MeasurableSet {ω | x < Y ω} := measurableSet_lt measurable_const hYm
  have hpt : ∀ ω, Real.exp (t * Y ω) ≤ Real.exp ((t - t') * x) * Real.exp (t' * Y ω) +
      Real.exp (t * M) * {ω | x < Y ω}.indicator (fun _ => (1 : ℝ)) ω +
        Real.exp (-((t'' - t) * M)) * Real.exp (t'' * Y ω) := fun ω => by
    have e1 := Real.exp_pos ((t - t') * x)
    have e2 := Real.exp_pos (t' * Y ω)
    have e3 := Real.exp_pos (t * M)
    have e4 := Real.exp_pos (-((t'' - t) * M))
    have e5 := Real.exp_pos (t'' * Y ω)
    have hind : 0 ≤ {ω | x < Y ω}.indicator (fun _ => (1 : ℝ)) ω :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) ω
    by_cases h1 : Y ω ≤ x
    · have : Real.exp (t * Y ω) ≤ Real.exp ((t - t') * x) * Real.exp (t' * Y ω) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.2 (by nlinarith)
      nlinarith [mul_nonneg e3.le hind, mul_nonneg e4.le e5.le]
    · push Not at h1
      by_cases h2 : Y ω ≤ M
      · have hmem : ω ∈ {ω | x < Y ω} := h1
        rw [indicator_of_mem hmem, mul_one]
        have : Real.exp (t * Y ω) ≤ Real.exp (t * M) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h2 (ht'.trans ht))
        nlinarith [mul_nonneg e1.le e2.le, mul_nonneg e4.le e5.le]
      · push Not at h2
        have : Real.exp (t * Y ω) ≤ Real.exp (-((t'' - t) * M)) * Real.exp (t'' * Y ω) := by
          rw [← Real.exp_add]
          exact Real.exp_le_exp.2 (by nlinarith)
        nlinarith [mul_nonneg e1.le e2.le, mul_nonneg e3.le hind]
  have hind_i : Integrable (fun ω => Real.exp (t * M) *
      {ω | x < Y ω}.indicator (fun _ => (1 : ℝ)) ω) ν :=
    ((integrable_const (1 : ℝ)).indicator hS).const_mul _
  have hsum : Integrable (fun ω => Real.exp ((t - t') * x) * Real.exp (t' * Y ω) +
      Real.exp (t * M) * {ω | x < Y ω}.indicator (fun _ => (1 : ℝ)) ω +
        Real.exp (-((t'' - t) * M)) * Real.exp (t'' * Y ω)) ν :=
    ((hi'.const_mul _).add hind_i).add (hi''.const_mul _)
  refine (integral_mono hi hsum hpt).trans (le_of_eq ?_)
  rw [integral_add (f := fun ω => Real.exp ((t - t') * x) * Real.exp (t' * Y ω) +
      Real.exp (t * M) * {ω | x < Y ω}.indicator (fun _ => (1 : ℝ)) ω)
      (g := fun ω => Real.exp (-((t'' - t) * M)) * Real.exp (t'' * Y ω))
      ((hi'.const_mul _).add hind_i) (hi''.const_mul _),
    integral_add (f := fun ω => Real.exp ((t - t') * x) * Real.exp (t' * Y ω))
      (g := fun ω => Real.exp (t * M) * {ω | x < Y ω}.indicator (fun _ => (1 : ℝ)) ω)
      (hi'.const_mul _) hind_i, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_indicator hS, setIntegral_const, smul_eq_mul, mul_one]

/-- **Kolmogorov's lower exponential bound** from moment generating function bounds (the
argument of Kolmogorov's lower inequality, Stout 1974, §5.2): let `1 ≤ x`, `0 < h ≤ 1/4`,
`0 ≤ α ≤ h²/4` and `h²x² ≥ log 4`. If `∫ e^{τY} dν ≤ ν(Ω) e^{τ²(1+α)/2}` for `τ = x` and
`τ = x(1+4h)`, and `∫ e^{tY} dν ≥ ν(Ω) e^{t²(1−α)/2} − E` for `t = x(1+2h)`, then
`ν(Y > x) ≥ (ν(Ω)/2) e^{−x²(1+12h)/2} − e^{−t x(1+4h)} E`. -/
theorem kolmogorov_lower {ν : Measure Ω} [IsFiniteMeasure ν] {Y : Ω → ℝ} (hYm : Measurable Y)
    {x h α E : ℝ} (hx : 1 ≤ x) (hh0 : 0 < h) (hh : h ≤ 1 / 4) (hα0 : 0 ≤ α)
    (hα : α ≤ h ^ 2 / 4) (hxh : Real.log 4 ≤ h ^ 2 * x ^ 2)
    (hi : ∀ τ : ℝ, Integrable (fun ω => Real.exp (τ * Y ω)) ν)
    (hU1 : ∫ ω, Real.exp (x * Y ω) ∂ν ≤ ν.real univ * Real.exp (x ^ 2 / 2 * (1 + α)))
    (hU2 : ∫ ω, Real.exp ((x * (1 + 4 * h)) * Y ω) ∂ν ≤
      ν.real univ * Real.exp ((x * (1 + 4 * h)) ^ 2 / 2 * (1 + α)))
    (hL : ν.real univ * Real.exp ((x * (1 + 2 * h)) ^ 2 / 2 * (1 - α)) - E ≤
      ∫ ω, Real.exp ((x * (1 + 2 * h)) * Y ω) ∂ν) :
    ν.real univ / 2 * Real.exp (-(x ^ 2 / 2 * (1 + 12 * h))) -
        Real.exp (-((x * (1 + 2 * h)) * (x * (1 + 4 * h)))) * E ≤ ν.real {ω | x < Y ω} := by
  set P := ν.real univ with hP
  have hP0 : 0 ≤ P := measureReal_nonneg
  set t := x * (1 + 2 * h) with ht
  set M := x * (1 + 4 * h) with hM
  have hx0 : 0 < x := by linarith
  have hsplit := integral_exp_le_split hYm (t' := x) (t := t) (t'' := M) (x := x) (M := M)
    hx0.le (by rw [ht]; nlinarith) (by rw [ht, hM]; nlinarith) (hi x) (hi t) (hi M)
  set a0 := t ^ 2 / 2 * (1 - α) with ha0
  set a1 := (t - x) * x + x ^ 2 / 2 * (1 + α) with ha1
  set a3 := -((M - t) * M) + M ^ 2 / 2 * (1 + α) with ha3
  have hb1 : (1 + 2 * h) ^ 2 ≤ 9 / 4 := by nlinarith
  have hb2 : (1 + 4 * h) ^ 2 ≤ 4 := by nlinarith
  have hX20 : 0 ≤ x ^ 2 := sq_nonneg x
  -- the exponents
  have hd1 : a1 + Real.log 4 ≤ a0 := by
    have e : a0 - a1 = x ^ 2 * (2 * h ^ 2 - α * ((1 + 2 * h) ^ 2 + 1) / 2) := by
      rw [ha0, ha1, ht]; ring
    have h1 : α * ((1 + 2 * h) ^ 2 + 1) ≤ h ^ 2 / 4 * (13 / 4) :=
      mul_le_mul hα (by linarith) (by positivity) (by positivity)
    have h2 : h ^ 2 ≤ 2 * h ^ 2 - α * ((1 + 2 * h) ^ 2 + 1) / 2 := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hX20
    linarith
  have hd3 : a3 + Real.log 4 ≤ a0 := by
    have e : a0 - a3 = x ^ 2 * (2 * h ^ 2 - α * ((1 + 2 * h) ^ 2 + (1 + 4 * h) ^ 2) / 2) := by
      rw [ha0, ha3, ht, hM]; ring
    have h1 : α * ((1 + 2 * h) ^ 2 + (1 + 4 * h) ^ 2) ≤ h ^ 2 / 4 * (25 / 4) :=
      mul_le_mul hα (by linarith) (by positivity) (by positivity)
    have h2 : h ^ 2 ≤ 2 * h ^ 2 - α * ((1 + 2 * h) ^ 2 + (1 + 4 * h) ^ 2) / 2 := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hX20
    linarith
  have hd4 : -(x ^ 2 / 2 * (1 + 12 * h)) ≤ a0 - t * M := by
    have e : a0 - t * M = -(x ^ 2 / 2 * ((1 + 2 * h) * (1 + 6 * h + α * (1 + 2 * h)))) := by
      rw [ha0, ht, hM]; ring
    have h1 : α * (1 + 2 * h) ≤ h ^ 2 / 4 * (3 / 2) :=
      mul_le_mul hα (by linarith) (by positivity) (by positivity)
    have h4 : h ^ 2 ≤ h / 4 := by nlinarith
    have h5 : (1 + 2 * h) * (α * (1 + 2 * h)) ≤ (3 / 2) * (h ^ 2 / 4 * (3 / 2)) :=
      mul_le_mul (by linarith) h1 (by positivity) (by norm_num)
    have h2 : (1 + 2 * h) * (1 + 6 * h + α * (1 + 2 * h)) ≤ 1 + 12 * h := by
      have e2 : (1 + 2 * h) * (1 + 6 * h + α * (1 + 2 * h)) =
          1 + 8 * h + 12 * h ^ 2 + (1 + 2 * h) * (α * (1 + 2 * h)) := by ring
      rw [e2]
      linarith
    have h3 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ x ^ 2 / 2 by positivity)
    rw [e]
    linarith
  have hl4 : Real.exp (Real.log 4) = 4 := Real.exp_log (by norm_num)
  have hE1 : Real.exp a1 ≤ Real.exp a0 / 4 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4), ← hl4, ← Real.exp_add]
    exact Real.exp_le_exp.2 hd1
  have hE3 : Real.exp a3 ≤ Real.exp a0 / 4 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4), ← hl4, ← Real.exp_add]
    exact Real.exp_le_exp.2 hd3
  -- the split
  have hT1 : Real.exp ((t - x) * x) * ∫ ω, Real.exp (x * Y ω) ∂ν ≤ P * Real.exp a1 := by
    calc Real.exp ((t - x) * x) * ∫ ω, Real.exp (x * Y ω) ∂ν
        ≤ Real.exp ((t - x) * x) * (P * Real.exp (x ^ 2 / 2 * (1 + α))) :=
          mul_le_mul_of_nonneg_left hU1 (Real.exp_pos _).le
      _ = P * Real.exp a1 := by rw [ha1, Real.exp_add]; ring
  have hT3 : Real.exp (-((M - t) * M)) * ∫ ω, Real.exp (M * Y ω) ∂ν ≤ P * Real.exp a3 := by
    calc Real.exp (-((M - t) * M)) * ∫ ω, Real.exp (M * Y ω) ∂ν
        ≤ Real.exp (-((M - t) * M)) * (P * Real.exp (M ^ 2 / 2 * (1 + α))) :=
          mul_le_mul_of_nonneg_left hU2 (Real.exp_pos _).le
      _ = P * Real.exp a3 := by rw [ha3, Real.exp_add]; ring
  have hmain : P / 2 * Real.exp a0 - E ≤ Real.exp (t * M) * ν.real {ω | x < Y ω} := by
    have := mul_le_mul_of_nonneg_left hE1 hP0
    have := mul_le_mul_of_nonneg_left hE3 hP0
    linarith
  have htM := Real.exp_pos (t * M)
  have hfin : P / 2 * Real.exp (a0 - t * M) - Real.exp (-(t * M)) * E ≤
      ν.real {ω | x < Y ω} := by
    rw [Real.exp_sub, Real.exp_neg]
    have e : P / 2 * (Real.exp a0 / Real.exp (t * M)) - (Real.exp (t * M))⁻¹ * E =
        (P / 2 * Real.exp a0 - E) / Real.exp (t * M) := by
      field_simp
    rw [e, div_le_iff₀ htM]
    linarith
  have h5 : P / 2 * Real.exp (-(x ^ 2 / 2 * (1 + 12 * h))) ≤ P / 2 * Real.exp (a0 - t * M) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hd4) (by positivity)
  linarith

/-! ### The conditional variance of the truncated differences -/

/-- The conditional variance `E[truncMDⱼ² | 𝓕ⱼ]` of the truncated differences, clamped to
`[0, (2bⱼ)²]` (which changes it only on a null set). -/
noncomputable def truncVar (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) (b : ℕ → ℝ)
    (j : ℕ) (ω : Ω) : ℝ :=
  max 0 (min ((2 * b j) ^ 2) (Q[fun ω => truncMD Q ℱ D b j ω ^ 2 | ℱ j] ω))

/-- `truncVar` is `𝓕ⱼ`-measurable. -/
theorem measurable_truncVar (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ)
    (b : ℕ → ℝ) (j : ℕ) : Measurable[ℱ j] (truncVar Q ℱ D b j) :=
  measurable_const.max (measurable_const.min stronglyMeasurable_condExp.measurable)

/-- `truncVar ≥ 0`. -/
theorem truncVar_nonneg (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) (b : ℕ → ℝ)
    (j : ℕ) (ω : Ω) : 0 ≤ truncVar Q ℱ D b j ω :=
  le_max_left _ _

/-- `truncVar ≤ (2bⱼ)²`. -/
theorem truncVar_le (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) (b : ℕ → ℝ)
    (j : ℕ) (ω : Ω) : truncVar Q ℱ D b j ω ≤ (2 * b j) ^ 2 :=
  max_le (sq_nonneg _) (min_le_left _ _)

/-- `truncVar` is a version of `E[truncMDⱼ² | 𝓕ⱼ]`. -/
theorem truncVar_ae_eq {Q : Measure Ω} [IsFiniteMeasure Q] (ℱ : Filtration ℕ mΩ)
    (D : ℕ → Ω → ℝ) {b : ℕ → ℝ} (hb : ∀ j, 0 ≤ b j) (j : ℕ) :
    truncVar Q ℱ D b j =ᵐ[Q] Q[fun ω => truncMD Q ℱ D b j ω ^ 2 | ℱ j] := by
  have hb2 : ∀ ω, |truncMD Q ℱ D b j ω ^ 2| ≤ (2 * b j) ^ 2 := fun ω => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_truncMD_le Q ℱ D hb j ω) 2
  filter_upwards [ae_bdd_abs_condExp_of_ae_bdd_abs (μ := Q) (m := ℱ j)
    (f := fun ω => truncMD Q ℱ D b j ω ^ 2) (R := (2 * b j) ^ 2) (Eventually.of_forall hb2),
    condExp_nonneg (μ := Q) (m := ℱ j) (f := fun ω => truncMD Q ℱ D b j ω ^ 2)
      (Eventually.of_forall fun ω => sq_nonneg _)] with ω h1 h2
  have h2' : (0 : ℝ) ≤ Q[fun ω => truncMD Q ℱ D b j ω ^ 2 | ℱ j] ω := h2
  rw [truncVar, min_eq_right (abs_le.1 h1).2, max_eq_right h2']

/-- `∫ F truncVar = ∫ F truncMD²` for bounded `𝓕ⱼ`-measurable `F`. -/
theorem integral_mul_truncVar {Q : Measure Ω} [IsFiniteMeasure Q] {ℱ : Filtration ℕ mΩ}
    {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k)) {b : ℕ → ℝ}
    (hb : ∀ j, 0 ≤ b j) (j : ℕ) {F : Ω → ℝ} {C : ℝ} (hFm : Measurable[ℱ j] F)
    (hFb : ∀ ω, |F ω| ≤ C) :
    ∫ ω, F ω * truncVar Q ℱ D b j ω ∂Q = ∫ ω, F ω * truncMD Q ℱ D b j ω ^ 2 ∂Q := by
  have hXi : Integrable (fun ω => truncMD Q ℱ D b j ω ^ 2) Q :=
    integrable_of_abs_le (((measurable_truncMD Q hD b j).mono (ℱ.le _) le_rfl).pow_const 2)
      (C := (2 * b j) ^ 2) fun ω => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_truncMD_le Q ℱ D hb j ω) 2
  rw [← integral_mul_condExp (ℱ.le j) hFm hFb hXi]
  refine integral_congr_ae ?_
  filter_upwards [truncVar_ae_eq ℱ D hb j] with ω hω
  rw [hω]

/-- **The truncation loses little conditional variance**: if `E[Dⱼ | 𝓕ⱼ] = 0` and `K ≤ bⱼ²`,
then almost surely `E[Dⱼ² | 𝓕ⱼ] − 2 E[Dⱼ² 1{Dⱼ² ≥ K} | 𝓕ⱼ] ≤ truncVar`. -/
theorem truncVar_ge {Q : Measure Ω} [IsFiniteMeasure Q] {ℱ : Filtration ℕ mΩ}
    {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0) {b : ℕ → ℝ}
    (hb : ∀ j, 0 ≤ b j) (j : ℕ) {K : ℝ} (hK : K ≤ b j ^ 2) :
    ∀ᵐ ω ∂Q, condVarMD Q ℱ D j ω -
        2 * Q[fun ω => {ω | K ≤ D j ω ^ 2}.indicator (fun ω => D j ω ^ 2) ω | ℱ j] ω ≤
      truncVar Q ℱ D b j ω := by
  have hm := ℱ.le j
  have hDm : Measurable (D j) := (hD j).measurable.mono (ℱ.le _) le_rfl
  set T : Ω → ℝ := fun ω => lilTrunc (b j) (D j ω) with hT
  set mm : Ω → ℝ := truncMean Q ℱ D b j with hmm
  set X : Ω → ℝ := truncMD Q ℱ D b j with hX
  set R : Ω → ℝ := fun ω => D j ω ^ 2 - T ω ^ 2 with hR
  have hTm : Measurable T := (measurable_lilTrunc _).comp hDm
  have hmmm : Measurable[ℱ j] mm := measurable_truncMean Q ℱ D b j
  have hTb : ∀ ω, |T ω| ≤ b j := fun ω => abs_lilTrunc_le (hb j) _
  have hmb : ∀ ω, |mm ω| ≤ b j := abs_truncMean_le Q ℱ D hb j
  have hTi : Integrable T Q := integrable_of_abs_le hTm hTb
  have hT2i : Integrable (fun ω => T ω ^ 2) Q :=
    integrable_of_abs_le (hTm.pow_const 2) (C := b j ^ 2) fun ω => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hTb ω) 2
  have hm2i : Integrable (fun ω => mm ω ^ 2) Q :=
    integrable_of_abs_le ((hmmm.mono hm le_rfl).pow_const 2) (C := b j ^ 2) fun ω => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hmb ω) 2
  have hD2i : Integrable (fun ω => D j ω ^ 2) Q := (hL2 j).integrable_sq
  have hRi : Integrable R Q := hD2i.sub hT2i
  have hX2i : Integrable (fun ω => X ω ^ 2) Q :=
    integrable_of_abs_le (((measurable_truncMD Q hD b j).mono (ℱ.le _) le_rfl).pow_const 2)
      (C := (2 * b j) ^ 2) fun ω => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_truncMD_le Q ℱ D hb j ω) 2
  -- (a) `E[X² | 𝓕] = E[T² | 𝓕] − m²`
  have ha : (fun ω => Q[fun ω => T ω ^ 2 | ℱ j] ω - mm ω ^ 2) =ᵐ[Q]
      Q[fun ω => X ω ^ 2 | ℱ j] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq hm hX2i (fun s _ _ =>
      (integrable_condExp.sub hm2i).integrableOn) (fun s hs _ => ?_)
      ((stronglyMeasurable_condExp.sub ((hmmm.pow_const 2).stronglyMeasurable))
        |>.aestronglyMeasurable)
    have hs' : MeasurableSet s := hm s hs
    have h1 := integral_mul_truncMD_sq (Q := Q) hD hb j (F := s.indicator fun _ => (1 : ℝ))
      (C := 1) (measurable_const.indicator hs) (fun ω => by
        by_cases hω : ω ∈ s
        · rw [indicator_of_mem hω, abs_one]
        · rw [indicator_of_notMem hω, abs_zero]; exact zero_le_one)
    rw [integral_indicator_one_mul hs', integral_indicator_one_mul hs',
      integral_indicator_one_mul hs'] at h1
    rw [integral_sub integrable_condExp.integrableOn hm2i.integrableOn,
      setIntegral_condExp hm hT2i hs, h1]
  -- (b) `E[T² | 𝓕] = E[D² | 𝓕] − E[R | 𝓕]`
  have hb' : Q[fun ω => T ω ^ 2 | ℱ j] =ᵐ[Q]
      Q[fun ω => D j ω ^ 2 | ℱ j] - Q[R | ℱ j] := by
    have e : (fun ω => T ω ^ 2) = (fun ω => D j ω ^ 2) - R := by
      ext ω; simp only [hR, Pi.sub_apply]; ring
    rw [e]
    exact condExp_sub hD2i hRi _
  -- (c) `m² ≤ E[R | 𝓕]` (conditional Jensen)
  have hc : ∀ᵐ ω ∂Q, mm ω ^ 2 ≤ Q[R | ℱ j] ω := by
    have hTD : Integrable (fun ω => T ω - D j ω) Q := hTi.sub ((hL2 j).integrable one_le_two)
    have hJ := (even_two.convexOn_pow (𝕜 := ℝ)).map_condExp_le_univ (m := ℱ j) hm
      (continuous_pow 2).lowerSemicontinuous hTD (by
        have e : ((fun x : ℝ => x ^ 2) ∘ fun ω => T ω - D j ω) = R := by
          ext ω
          simp only [Function.comp_apply, hR, hT, lilTrunc]
          split_ifs <;> ring
        rw [e]; exact hRi)
    have e2 : ((fun x : ℝ => x ^ 2) ∘ fun ω => T ω - D j ω) = R := by
      ext ω
      simp only [Function.comp_apply, hR, hT, lilTrunc]
      split_ifs <;> ring
    rw [e2] at hJ
    have hsub := condExp_sub (m := ℱ j) hTi ((hL2 j).integrable one_le_two)
    filter_upwards [hJ, hsub, h0 j, truncMean_ae_eq ℱ D hb j] with ω h1 h2 h3 h4
    have h5 : mm ω = Q[fun ω => T ω - D j ω | ℱ j] ω := by
      rw [show (fun ω => T ω - D j ω) = T - D j from rfl, h2, Pi.sub_apply, h3,
        Pi.zero_apply, sub_zero]
      exact h4
    rw [h5]
    exact h1
  -- (d) `E[R | 𝓕] ≤ E[D² 1{D² ≥ K} | 𝓕]`
  have hd : Q[R | ℱ j] ≤ᵐ[Q]
      Q[fun ω => {ω | K ≤ D j ω ^ 2}.indicator (fun ω => D j ω ^ 2) ω | ℱ j] := by
    refine condExp_mono hRi (hD2i.indicator (measurableSet_le measurable_const
      (hDm.pow_const 2))) (Eventually.of_forall fun ω => ?_)
    simp only [hR, hT, lilTrunc]
    split_ifs with h1
    · rw [sub_self]
      exact Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω
    · push Not at h1
      have h2 : K ≤ D j ω ^ 2 := by
        have : b j ^ 2 < D j ω ^ 2 := by
          rw [← sq_abs (D j ω)]
          exact pow_lt_pow_left₀ h1 (hb j) two_ne_zero
        linarith
      rw [Set.indicator_of_mem (show ω ∈ {ω | K ≤ D j ω ^ 2} from h2)]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, le_refl]
  filter_upwards [ha, hb', hc, hd, condVarMD_ae_eq Q ℱ D j, truncVar_ae_eq ℱ D hb j]
    with ω h1 h2 h3 h4 h5 h6
  rw [h6, ← h1, h5]
  simp only [Pi.sub_apply] at h2
  rw [h2]
  linarith

/-! ### The blocks of the lower half -/

/-- The predictable event that the block started at `n₀` has not used up its conditional
variance budget `B` by step `j`: `n₀ ≤ j` and `Σ_{i ∈ [n₀, j]} truncVarᵢ ≤ B`. -/
def blockSet (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) (b : ℕ → ℝ) (n₀ : ℕ)
    (B : ℝ) (j : ℕ) : Set Ω :=
  {ω | n₀ ≤ j ∧ ∑ i ∈ Finset.Ico n₀ (j + 1), truncVar Q ℱ D b i ω ≤ B}

/-- The block sum `Σ_{j ∈ [n₀, H)} truncMDⱼ 1_{blockSetⱼ}`: the truncated martingale run from
`n₀` until its conditional variance budget `B` is used up. -/
noncomputable def blockSum (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) (b : ℕ → ℝ)
    (n₀ : ℕ) (B : ℝ) (H : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.Ico n₀ H, (blockSet Q ℱ D b n₀ B j).indicator (truncMD Q ℱ D b j) ω

/-- The conditional variance `Σ_{j ∈ [n₀, H)} truncVarⱼ 1_{blockSetⱼ}` of the block sum. -/
noncomputable def blockVar (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) (b : ℕ → ℝ)
    (n₀ : ℕ) (B : ℝ) (H : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.Ico n₀ H, (blockSet Q ℱ D b n₀ B j).indicator (truncVar Q ℱ D b j) ω

/-- The block events are predictable. -/
theorem measurableSet_blockSet (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ)
    (b : ℕ → ℝ) (n₀ : ℕ) (B : ℝ) (j : ℕ) : MeasurableSet[ℱ j] (blockSet Q ℱ D b n₀ B j) :=
  (MeasurableSet.const _).inter
    (measurable_sum_Ico_succ (measurable_truncVar Q ℱ D b) n₀ j measurableSet_Iic)

/-- The block budget: `blockVar ≤ B`, and `blockVar ≥ B − c²` once the budget is reached
(`c = 2L`, `bⱼ ≤ L`). -/
theorem blockVar_bounds (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) {b : ℕ → ℝ}
    {L : ℝ} (hb0 : ∀ j, 0 ≤ b j) (hbL : ∀ j, b j ≤ L) (n₀ : ℕ) {B : ℝ} (hB : 0 ≤ B) (H : ℕ)
    (ω : Ω) : blockVar Q ℱ D b n₀ B H ω ≤ B ∧
      (B ≤ ∑ j ∈ Finset.Ico n₀ H, truncVar Q ℱ D b j ω →
        B - (2 * L) ^ 2 ≤ blockVar Q ℱ D b n₀ B H ω) := by
  set v : ℕ → ℝ := fun i => truncVar Q ℱ D b (n₀ + i) ω with hv
  have hv0 : ∀ i, 0 ≤ v i := fun i => truncVar_nonneg Q ℱ D b _ ω
  have hvc : ∀ i, v i ≤ (2 * L) ^ 2 := fun i =>
    (truncVar_le Q ℱ D b _ ω).trans (pow_le_pow_left₀ (by linarith [hb0 (n₀ + i)])
      (by linarith [hbL (n₀ + i)]) 2)
  have e1 : blockVar Q ℱ D b n₀ B H ω = ∑ i ∈ Finset.range (H - n₀),
      (if ∑ i' ∈ Finset.range (i + 1), v i' ≤ B then v i else 0) := by
    rw [blockVar, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e2 : ∑ i' ∈ Finset.Ico n₀ (n₀ + i + 1), truncVar Q ℱ D b i' ω =
        ∑ i' ∈ Finset.range (i + 1), v i' := by
      rw [Finset.sum_Ico_eq_sum_range, show n₀ + i + 1 - n₀ = i + 1 by omega]
    by_cases h : ∑ i' ∈ Finset.range (i + 1), v i' ≤ B
    · have hmem : ω ∈ blockSet Q ℱ D b n₀ B (n₀ + i) := ⟨by omega, by rw [e2]; exact h⟩
      rw [indicator_of_mem hmem]; simp only [h, ite_true]; rfl
    · have hmem : ω ∉ blockSet Q ℱ D b n₀ B (n₀ + i) := fun hm => h (by rw [← e2]; exact hm.2)
      rw [indicator_of_notMem hmem]; simp only [h, ite_false]
  have e3 : ∑ j ∈ Finset.Ico n₀ H, truncVar Q ℱ D b j ω = ∑ i ∈ Finset.range (H - n₀), v i :=
    Finset.sum_Ico_eq_sum_range _ _ _
  obtain ⟨h1, -, h3⟩ := sum_ite_threshold hv0 hB hvc (H - n₀)
  rw [e1, e3]
  refine ⟨h1, fun hBW => le_trans ?_ h3⟩
  exact le_min (by linarith [sq_nonneg (2 * L)]) le_rfl

/-- The weighted truncated differences of a block are bounded martingale differences whose
weights are their exact conditional variances. -/
theorem isBddMartDiff_block {Q : Measure Ω} [IsFiniteMeasure Q] {ℱ : Filtration ℕ mΩ}
    {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k)) {b : ℕ → ℝ} {L : ℝ}
    (hb0 : ∀ j, 0 ≤ b j) (hbL : ∀ j, b j ≤ L) (n₀ : ℕ) (B : ℝ) :
    IsBddMartDiff Q ℱ (fun j => (blockSet Q ℱ D b n₀ B j).indicator (truncMD Q ℱ D b j))
        (fun j => (blockSet Q ℱ D b n₀ B j).indicator (truncVar Q ℱ D b j)) (2 * L)
        ((2 * L) ^ 2) ∧
      IsVarLe Q ℱ (fun j => (blockSet Q ℱ D b n₀ B j).indicator (truncMD Q ℱ D b j))
        (fun j => (blockSet Q ℱ D b n₀ B j).indicator (truncVar Q ℱ D b j)) ∧
      IsVarGe Q ℱ (fun j => (blockSet Q ℱ D b n₀ B j).indicator (truncMD Q ℱ D b j))
        (fun j => (blockSet Q ℱ D b n₀ B j).indicator (truncVar Q ℱ D b j)) := by
  have hL0 : 0 ≤ L := (hb0 0).trans (hbL 0)
  have hbase : IsBddMartDiff Q ℱ (truncMD Q ℱ D b) (truncVar Q ℱ D b) (2 * L) ((2 * L) ^ 2) :=
    { meas_X := measurable_truncMD Q hD b
      meas_u := measurable_truncVar Q ℱ D b
      abs_X_le := fun j ω => (abs_truncMD_le Q ℱ D hb0 j ω).trans (by linarith [hbL j])
      u_nonneg := truncVar_nonneg Q ℱ D b
      u_le := fun j ω => (truncVar_le Q ℱ D b j ω).trans (pow_le_pow_left₀
        (by linarith [hb0 j]) (by linarith [hbL j]) 2)
      orth := fun j F C hFm hFb => integral_mul_truncMD hD hb0 j hFm hFb }
  have hle : IsVarLe Q ℱ (truncMD Q ℱ D b) (truncVar Q ℱ D b) := fun j F C hFm _ hFb =>
    (integral_mul_truncVar hD hb0 j hFm hFb).symm.le
  have hge : IsVarGe Q ℱ (truncMD Q ℱ D b) (truncVar Q ℱ D b) := fun j F C hFm _ hFb =>
    (integral_mul_truncVar hD hb0 j hFm hFb).le
  exact ⟨hbase.indicator (by positivity) (sq_nonneg _)
      (measurableSet_blockSet Q ℱ D b n₀ B),
    hle.indicator (measurableSet_blockSet Q ℱ D b n₀ B),
    hge.indicator (measurableSet_blockSet Q ℱ D b n₀ B)⟩

/-- The block sums are bounded. -/
theorem abs_blockSum_le (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) {b : ℕ → ℝ}
    {L : ℝ} (hb0 : ∀ j, 0 ≤ b j) (hbL : ∀ j, b j ≤ L) (n₀ : ℕ) (B : ℝ) (H : ℕ) (ω : Ω) :
    |blockSum Q ℱ D b n₀ B H ω| ≤ (H - n₀ : ℕ) * (2 * L) := by
  refine abs_sum_Ico_le (fun j ω => ?_) n₀ H ω
  by_cases hω : ω ∈ blockSet Q ℱ D b n₀ B j
  · rw [indicator_of_mem hω]
    exact (abs_truncMD_le Q ℱ D hb0 j ω).trans (by linarith [hbL j])
  · rw [indicator_of_notMem hω, abs_zero]; linarith [hb0 j, hbL j]

/-- The block sums are measurable. -/
theorem measurable_blockSum (Q : Measure Ω) {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ}
    (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k)) (b : ℕ → ℝ) (n₀ : ℕ) (B : ℝ) (H : ℕ) :
    Measurable (blockSum Q ℱ D b n₀ B H) :=
  (measurable_sum_Ico (fun j => (measurable_truncMD Q hD b j).indicator
    (ℱ.mono (Nat.le_succ j) _ (measurableSet_blockSet Q ℱ D b n₀ B j))) n₀ H).mono
    (ℱ.le H) le_rfl

omit mΩ in
/-- The weight `1_G` lies in `[0, 1]`. -/
theorem indicator_one_bounds {G : Set Ω} :
    (∀ ω, 0 ≤ G.indicator (fun _ => (1 : ℝ)) ω) ∧ ∀ ω, |G.indicator (fun _ => (1 : ℝ)) ω| ≤ 1 :=
  ⟨fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω, fun ω => by
    by_cases hω : ω ∈ G
    · rw [indicator_of_mem hω, abs_one]
    · rw [indicator_of_notMem hω, abs_zero]; exact zero_le_one⟩

/-- **The upper moment bound for a block**: for `G ∈ 𝓕_{n₀}`, `0 ≤ λ` and `2λL ≤ 1`,
`∫_G e^{λ Y_H} ≤ P(G) exp(λ²(1 + 2λL) B/2)`, `Y_H = blockSum … H`. -/
theorem setIntegral_exp_blockSum_le {Q : Measure Ω} [IsFiniteMeasure Q] {ℱ : Filtration ℕ mΩ}
    {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k)) {b : ℕ → ℝ} {L : ℝ}
    (hb0 : ∀ j, 0 ≤ b j) (hbL : ∀ j, b j ≤ L) {n₀ H : ℕ} (hH : n₀ ≤ H) {B : ℝ} (hB : 0 ≤ B)
    {G : Set Ω} (hG : MeasurableSet[ℱ n₀] G) {l : ℝ} (hl : 0 ≤ l) (hlc : l * (2 * L) ≤ 1) :
    ∫ ω in G, Real.exp (l * blockSum Q ℱ D b n₀ B H ω) ∂Q ≤
      Q.real G * Real.exp (l ^ 2 * (1 + l * (2 * L)) / 2 * B) := by
  have hL0 : 0 ≤ L := (hb0 0).trans (hbL 0)
  obtain ⟨hbmd, hle, -⟩ := isBddMartDiff_block (Q := Q) hD hb0 hbL n₀ B
  set κ := l ^ 2 * (1 + l * (2 * L)) / 2 with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have h1 := hbmd.integral_exp_le hle (by positivity) hl hlc le_rfl hH
    (F := G.indicator fun _ => (1 : ℝ)) (C := 1) (measurable_const.indicator hG)
    indicator_one_bounds.1 indicator_one_bounds.2
  have hG' : MeasurableSet G := ℱ.le n₀ _ hG
  rw [integral_indicator_one_mul hG', integral_indicator hG', setIntegral_const,
    smul_eq_mul, mul_one] at h1
  have hYm := measurable_blockSum Q hD b n₀ B H
  have hVm : Measurable (blockVar Q ℱ D b n₀ B H) :=
    (measurable_sum_Ico (fun j => ((measurable_truncVar Q ℱ D b j).indicator
      (measurableSet_blockSet Q ℱ D b n₀ B j)).mono (ℱ.mono (Nat.le_succ j)) le_rfl) n₀ H).mono
      (ℱ.le H) le_rfl
  have hpt : ∀ ω, Real.exp (l * blockSum Q ℱ D b n₀ B H ω) ≤ Real.exp (κ * B) *
      Real.exp (l * blockSum Q ℱ D b n₀ B H ω - κ * blockVar Q ℱ D b n₀ B H ω) := fun ω => by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left (blockVar_bounds Q ℱ D hb0 hbL n₀ hB H ω).1 hκ0
    linarith
  have hYb := abs_blockSum_le Q ℱ D hb0 hbL n₀ B H
  have hi1 : Integrable (fun ω => Real.exp (l * blockSum Q ℱ D b n₀ B H ω)) Q :=
    integrable_of_abs_le (Real.continuous_exp.measurable.comp (hYm.const_mul l))
      (C := Real.exp (l * ((H - n₀ : ℕ) * (2 * L)))) fun ω => by
        rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (abs_le.1 (hYb ω)).2 hl)
  have hVb : ∀ ω, 0 ≤ blockVar Q ℱ D b n₀ B H ω := fun ω => Finset.sum_nonneg fun j _ =>
    Set.indicator_nonneg (fun ω _ => truncVar_nonneg Q ℱ D b j ω) ω
  have hi2 : Integrable (fun ω => Real.exp (κ * B) *
      Real.exp (l * blockSum Q ℱ D b n₀ B H ω - κ * blockVar Q ℱ D b n₀ B H ω)) Q :=
    (integrable_of_abs_le (f := fun ω => Real.exp (l * blockSum Q ℱ D b n₀ B H ω -
      κ * blockVar Q ℱ D b n₀ B H ω)) (Real.continuous_exp.measurable.comp ((hYm.const_mul l).sub
      (hVm.const_mul κ))) (C := Real.exp (l * ((H - n₀ : ℕ) * (2 * L)))) fun ω => by
        rw [abs_of_pos (Real.exp_pos _)]
        refine Real.exp_le_exp.2 ?_
        have := mul_le_mul_of_nonneg_left (abs_le.1 (hYb ω)).2 hl
        nlinarith [mul_nonneg hκ0 (hVb ω)]).const_mul _
  calc ∫ ω in G, Real.exp (l * blockSum Q ℱ D b n₀ B H ω) ∂Q
      ≤ ∫ ω in G, Real.exp (κ * B) *
          Real.exp (l * blockSum Q ℱ D b n₀ B H ω - κ * blockVar Q ℱ D b n₀ B H ω) ∂Q :=
        setIntegral_mono hi1.integrableOn hi2.integrableOn hpt
    _ = Real.exp (κ * B) * ∫ ω in G,
          Real.exp (l * blockSum Q ℱ D b n₀ B H ω - κ * blockVar Q ℱ D b n₀ B H ω) ∂Q :=
        integral_const_mul _ _
    _ ≤ Real.exp (κ * B) * Q.real G := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = Q.real G * Real.exp (κ * B) := mul_comm _ _

/-- **The lower moment bound for a block**: for `G ∈ 𝓕_{n₀}`, `0 ≤ λ` and `4λL ≤ 1`, with
`κ = λ²(1 − 4λL)/2` and `NE = {Σ_{j ∈ [n₀, H)} truncVarⱼ < B}` (budget not reached by `H`),
`P(G) e^{κ(B − 4L²)} − e^{κ(B − 4L²)} ∫_{NE} e^{λ Y_H} ≤ ∫_G e^{λ Y_H}`. -/
theorem setIntegral_exp_blockSum_ge {Q : Measure Ω} [IsFiniteMeasure Q] {ℱ : Filtration ℕ mΩ}
    {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k)) {b : ℕ → ℝ} {L : ℝ}
    (hb0 : ∀ j, 0 ≤ b j) (hbL : ∀ j, b j ≤ L) {n₀ H : ℕ} (hH : n₀ ≤ H) {B : ℝ} (hB : 0 ≤ B)
    {G : Set Ω} (hG : MeasurableSet[ℱ n₀] G) {l : ℝ} (hl : 0 ≤ l)
    (hlc : 2 * (l * (2 * L)) ≤ 1) :
    Q.real G * Real.exp (l ^ 2 * (1 - 2 * (l * (2 * L))) / 2 * (B - (2 * L) ^ 2)) -
        Real.exp (l ^ 2 * (1 - 2 * (l * (2 * L))) / 2 * (B - (2 * L) ^ 2)) *
          ∫ ω in {ω | ∑ j ∈ Finset.Ico n₀ H, truncVar Q ℱ D b j ω < B},
            Real.exp (l * blockSum Q ℱ D b n₀ B H ω) ∂Q ≤
      ∫ ω in G, Real.exp (l * blockSum Q ℱ D b n₀ B H ω) ∂Q := by
  have hL0 : 0 ≤ L := (hb0 0).trans (hbL 0)
  obtain ⟨hbmd, -, hge⟩ := isBddMartDiff_block (Q := Q) hD hb0 hbL n₀ B
  set κ := l ^ 2 * (1 - 2 * (l * (2 * L))) / 2 with hκ
  have hκ0 : 0 ≤ κ := by have : 0 ≤ 1 - 2 * (l * (2 * L)) := by linarith
                         positivity
  set c2 := (2 * L) ^ 2 with hc2
  set Y := blockSum Q ℱ D b n₀ B H with hY
  set V := blockVar Q ℱ D b n₀ B H with hV
  set NE := {ω | ∑ j ∈ Finset.Ico n₀ H, truncVar Q ℱ D b j ω < B} with hNE
  have hNEm : MeasurableSet NE := measurableSet_lt
    (Finset.measurable_sum _ fun j _ => (measurable_truncVar Q ℱ D b j).mono (ℱ.le j) le_rfl)
    measurable_const
  have h1 := hbmd.integral_exp_ge hge (by positivity) hl (by linarith) le_rfl hH
    (F := G.indicator fun _ => (1 : ℝ)) (C := 1) (measurable_const.indicator hG)
    indicator_one_bounds.1 indicator_one_bounds.2
  have hG' : MeasurableSet G := ℱ.le n₀ _ hG
  rw [integral_indicator_one_mul hG', integral_indicator hG', setIntegral_const,
    smul_eq_mul, mul_one] at h1
  change Q.real G ≤ ∫ ω in G, Real.exp (l * Y ω - κ * V ω) ∂Q at h1
  have hYm : Measurable Y := measurable_blockSum Q hD b n₀ B H
  have hVm : Measurable V :=
    (measurable_sum_Ico (fun j => ((measurable_truncVar Q ℱ D b j).indicator
      (measurableSet_blockSet Q ℱ D b n₀ B j)).mono (ℱ.mono (Nat.le_succ j)) le_rfl) n₀ H).mono
      (ℱ.le H) le_rfl
  have hYb := abs_blockSum_le Q ℱ D hb0 hbL n₀ B H
  have hVb : ∀ ω, 0 ≤ V ω := fun ω => Finset.sum_nonneg fun j _ =>
    Set.indicator_nonneg (fun ω _ => truncVar_nonneg Q ℱ D b j ω) ω
  have hi1 : Integrable (fun ω => Real.exp (l * Y ω)) Q :=
    integrable_of_abs_le (Real.continuous_exp.measurable.comp (hYm.const_mul l))
      (C := Real.exp (l * ((H - n₀ : ℕ) * (2 * L)))) fun ω => by
        rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (abs_le.1 (hYb ω)).2 hl)
  have hi2 : Integrable (fun ω => Real.exp (l * Y ω - κ * V ω)) Q :=
    integrable_of_abs_le (f := fun ω => Real.exp (l * Y ω - κ * V ω))
      (Real.continuous_exp.measurable.comp ((hYm.const_mul l).sub (hVm.const_mul κ)))
      (C := Real.exp (l * ((H - n₀ : ℕ) * (2 * L)))) fun ω => by
        rw [abs_of_pos (Real.exp_pos _)]
        refine Real.exp_le_exp.2 ?_
        have := mul_le_mul_of_nonneg_left (abs_le.1 (hYb ω)).2 hl
        nlinarith [mul_nonneg hκ0 (hVb ω)]
  have hsplit := integral_inter_add_sdiff (μ := Q) (s := G)
    (f := fun ω => Real.exp (l * Y ω - κ * V ω)) hNEm hi2.integrableOn
  have hA : ∫ ω in G ∩ NE, Real.exp (l * Y ω - κ * V ω) ∂Q ≤
      ∫ ω in NE, Real.exp (l * Y ω) ∂Q := by
    refine (setIntegral_mono_set hi2.integrableOn (Eventually.of_forall fun ω =>
      (Real.exp_pos _).le) (Eventually.of_forall inter_subset_right)).trans ?_
    refine setIntegral_mono hi2.integrableOn hi1.integrableOn fun ω => Real.exp_le_exp.2 ?_
    nlinarith [mul_nonneg hκ0 (hVb ω)]
  have hBd : ∫ ω in G \ NE, Real.exp (l * Y ω - κ * V ω) ∂Q ≤
      Real.exp (-(κ * (B - c2))) * ∫ ω in G, Real.exp (l * Y ω) ∂Q := by
    rw [← integral_const_mul]
    have hi3 : Integrable (fun ω => Real.exp (-(κ * (B - c2))) * Real.exp (l * Y ω)) Q :=
      hi1.const_mul _
    refine (setIntegral_mono_on hi2.integrableOn hi3.integrableOn (hG'.diff hNEm)
      fun ω hω => ?_).trans (setIntegral_mono_set hi3.integrableOn (Eventually.of_forall
        fun ω => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
        (Eventually.of_forall sdiff_subset))
    have hω2 : B ≤ ∑ j ∈ Finset.Ico n₀ H, truncVar Q ℱ D b j ω := by
      have := hω.2
      simp only [hNE, mem_ofPred_eq, not_lt] at this
      exact this
    have h4 := (blockVar_bounds Q ℱ D hb0 hbL n₀ hB H ω).2 hω2
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left h4 hκ0
    change -(κ * (B - c2)) + l * Y ω ≥ l * Y ω - κ * V ω
    linarith
  have hEpos := Real.exp_pos (κ * (B - c2))
  have hmain : Q.real G ≤ Real.exp (-(κ * (B - c2))) * ∫ ω in G, Real.exp (l * Y ω) ∂Q +
      ∫ ω in NE, Real.exp (l * Y ω) ∂Q := by linarith
  have h5 := mul_le_mul_of_nonneg_left hmain hEpos.le
  rw [mul_add, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at h5
  linarith

/-- The arithmetic–geometric bound `∫_S e^{λY} ≤ (r/2) ∫ e^{2λY} + P(S)/(2r)`, `r > 0`. -/
theorem setIntegral_exp_le_amgm {Q : Measure Ω} [IsFiniteMeasure Q] {Y : Ω → ℝ}
    {l : ℝ} (hi1 : Integrable (fun ω => Real.exp (l * Y ω)) Q)
    (hi2 : Integrable (fun ω => Real.exp ((2 * l) * Y ω)) Q) (S : Set Ω) {r : ℝ} (hr : 0 < r) :
    ∫ ω in S, Real.exp (l * Y ω) ∂Q ≤
      r / 2 * ∫ ω, Real.exp ((2 * l) * Y ω) ∂Q + Q.real S / (2 * r) := by
  have hpt : ∀ ω, Real.exp (l * Y ω) ≤ r / 2 * Real.exp ((2 * l) * Y ω) + 1 / (2 * r) :=
    fun ω => by
      have e : Real.exp ((2 * l) * Y ω) = Real.exp (l * Y ω) ^ 2 := by
        rw [sq, ← Real.exp_add]; ring_nf
      rw [e]
      have h1 : r / 2 * Real.exp (l * Y ω) ^ 2 + 1 / (2 * r) - Real.exp (l * Y ω) =
          (r * Real.exp (l * Y ω) - 1) ^ 2 / (2 * r) := by
        field_simp; ring
      have h2 : 0 ≤ (r * Real.exp (l * Y ω) - 1) ^ 2 / (2 * r) := by positivity
      linarith
  have hi3 : Integrable (fun ω => r / 2 * Real.exp ((2 * l) * Y ω) + 1 / (2 * r)) Q :=
    (hi2.const_mul _).add (integrable_const _)
  calc ∫ ω in S, Real.exp (l * Y ω) ∂Q
      ≤ ∫ ω in S, (r / 2 * Real.exp ((2 * l) * Y ω) + 1 / (2 * r)) ∂Q :=
        setIntegral_mono hi1.integrableOn hi3.integrableOn hpt
    _ = r / 2 * ∫ ω in S, Real.exp ((2 * l) * Y ω) ∂Q + Q.real S / (2 * r) := by
        rw [integral_add (hi2.const_mul _).integrableOn (integrable_const _).integrableOn,
          integral_const_mul, setIntegral_const, smul_eq_mul]
        ring
    _ ≤ r / 2 * ∫ ω, Real.exp ((2 * l) * Y ω) ∂Q + Q.real S / (2 * r) := by
        have := setIntegral_le_integral (s := S) hi2 (Eventually.of_forall fun ω =>
          (Real.exp_pos ((2 * l) * Y ω)).le)
        have := mul_le_mul_of_nonneg_left this (show 0 ≤ r / 2 by positivity)
        linarith

/-- Once the budget is used up inside `[n₀, n₁)`, the block sum stops moving. -/
theorem blockSum_eq_of_budget (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ)
    (b : ℕ → ℝ) {n₀ n₁ H : ℕ} (hn : n₀ ≤ n₁) (hH : n₁ ≤ H) {B : ℝ} {ω : Ω}
    (h : B < ∑ j ∈ Finset.Ico n₀ n₁, truncVar Q ℱ D b j ω) :
    blockSum Q ℱ D b n₀ B H ω = blockSum Q ℱ D b n₀ B n₁ ω := by
  rw [blockSum, blockSum, ← Finset.sum_Ico_consecutive _ hn hH]
  have : ∑ j ∈ Finset.Ico n₁ H, (blockSet Q ℱ D b n₀ B j).indicator (truncMD Q ℱ D b j) ω =
      0 := by
    refine Finset.sum_eq_zero fun j hj => indicator_of_notMem (fun hm => ?_) _
    have hj' := Finset.mem_Ico.1 hj
    have h2 : ∑ i ∈ Finset.Ico n₀ n₁, truncVar Q ℱ D b i ω ≤
        ∑ i ∈ Finset.Ico n₀ (j + 1), truncVar Q ℱ D b i ω :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl (by omega))
        fun i _ _ => truncVar_nonneg Q ℱ D b i ω
    linarith [hm.2]
  rw [this, add_zero]

/-- If the conditional variances sum to more than `B` almost surely, the probability that the
budget is not reached by time `H` tends to `0`. -/
theorem tendsto_measureReal_budget {Q : Measure Ω} [IsFiniteMeasure Q] {ℱ : Filtration ℕ mΩ}
    (D : ℕ → Ω → ℝ) (b : ℕ → ℝ) (n₀ : ℕ) {B : ℝ}
    (hinf : ∀ᵐ ω ∂Q, ∃ H, B ≤ ∑ j ∈ Finset.Ico n₀ H, truncVar Q ℱ D b j ω) :
    Tendsto (fun H => Q.real {ω | ∑ j ∈ Finset.Ico n₀ H, truncVar Q ℱ D b j ω < B}) atTop
      (𝓝 0) := by
  set NE : ℕ → Set Ω := fun H => {ω | ∑ j ∈ Finset.Ico n₀ H, truncVar Q ℱ D b j ω < B}
    with hNE
  have hm : ∀ H, MeasurableSet (NE H) := fun H => measurableSet_lt
    (Finset.measurable_sum _ fun j _ => (measurable_truncVar Q ℱ D b j).mono (ℱ.le j) le_rfl)
    measurable_const
  have hanti : Antitone NE := fun H H' hHH' ω hω => by
    have h2 : ∑ j ∈ Finset.Ico n₀ H, truncVar Q ℱ D b j ω ≤
        ∑ j ∈ Finset.Ico n₀ H', truncVar Q ℱ D b j ω :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl hHH')
        fun i _ _ => truncVar_nonneg Q ℱ D b i ω
    exact lt_of_le_of_lt h2 hω
  have h0 : Q (⋂ H, NE H) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hinf] with ω ⟨H, hH⟩ hω
    exact absurd hH (not_le.2 (mem_iInter.1 hω H))
  have ht := tendsto_measure_iInter_atTop (μ := Q) (fun H => (hm H).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rw [h0] at ht
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
  rw [ENNReal.toReal_zero] at h2
  exact h2

/-- **The conditional lower bound for a block** (Kolmogorov's lower exponential bound for
martingales, conditionally on `𝓕_{n₀}`): let the truncation levels satisfy `0 ≤ bⱼ ≤ L`, let the
conditional variances sum to at least `B > 0` almost surely, and let `1 ≤ x`, `0 < h ≤ 1/4`,
`0 ≤ α ≤ h²/4`, `h²x² ≥ log 4` and `4x · 2L/√B ≤ α`. Then for every `G ∈ 𝓕_{n₀}` and `n₁ ≥ n₀`,
`P(G ∩ A) ≥ (P(G)/2) e^{−x²(1+12h)/2}`, where `A` is the event that the block sum over `[n₀, n₁)`
exceeds `x√B` or the budget `B` is not used up within `[n₀, n₁)`. -/
theorem mdBlock_lower_bound {Q : Measure Ω} [IsProbabilityMeasure Q] {ℱ : Filtration ℕ mΩ}
    {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k)) {b : ℕ → ℝ} {L : ℝ}
    (hb0 : ∀ j, 0 ≤ b j) (hbL : ∀ j, b j ≤ L) {n₀ n₁ : ℕ} (hn : n₀ ≤ n₁) {B : ℝ} (hB : 0 < B)
    {x h α : ℝ} (hx : 1 ≤ x) (hh0 : 0 < h) (hh : h ≤ 1 / 4) (hα0 : 0 ≤ α) (hα : α ≤ h ^ 2 / 4)
    (hxh : Real.log 4 ≤ h ^ 2 * x ^ 2) (hc : 4 * (x * (2 * L / √B)) ≤ α)
    (hinf : ∀ᵐ ω ∂Q, ∃ H, B ≤ ∑ j ∈ Finset.Ico n₀ H, truncVar Q ℱ D b j ω)
    {G : Set Ω} (hG : MeasurableSet[ℱ n₀] G) :
    Q.real G / 2 * Real.exp (-(x ^ 2 / 2 * (1 + 12 * h))) ≤
      Q.real (G ∩ ({ω | x * √B < blockSum Q ℱ D b n₀ B n₁ ω} ∪
        {ω | ∑ j ∈ Finset.Ico n₀ n₁, truncVar Q ℱ D b j ω ≤ B})) := by
  have hL0 : 0 ≤ L := (hb0 0).trans (hbL 0)
  set c := 2 * L with hcdef
  have hc0 : 0 ≤ c := by positivity
  set sB := √B with hsBdef
  have hsB : 0 < sB := Real.sqrt_pos.2 hB
  have hsB2 : sB ^ 2 = B := Real.sq_sqrt hB.le
  set c' := c / sB with hc'def
  have hc'0 : 0 ≤ c' := by positivity
  have hx0 : 0 < x := by linarith
  have hα1 : α ≤ 1 / 64 := by nlinarith
  have hxc : x * c' ≤ α / 4 := by linarith
  have hc'1 : c' ≤ x * c' := le_mul_of_one_le_left hc'0 hx
  set t := x * (1 + 2 * h) with ht
  set M := x * (1 + 4 * h) with hM
  have ht0 : 0 ≤ t := by positivity
  have htx : t ≤ 3 / 2 * x := by rw [ht]; nlinarith
  have hMx : M ≤ 2 * x := by rw [hM]; nlinarith
  have htc : t * c' ≤ 3 / 2 * (x * c') := by
    have := mul_le_mul_of_nonneg_right htx hc'0; linarith
  have hMc : M * c' ≤ 2 * (x * c') := by
    have := mul_le_mul_of_nonneg_right hMx hc'0; linarith
  have hc'2 : c' ^ 2 ≤ x * c' := by
    have h1 : c' ≤ 1 := by linarith
    have : c' ^ 2 ≤ c' := by nlinarith
    linarith
  have hG' : MeasurableSet G := ℱ.le n₀ _ hG
  set A := {ω | x * √B < blockSum Q ℱ D b n₀ B n₁ ω} ∪
    {ω | ∑ j ∈ Finset.Ico n₀ n₁, truncVar Q ℱ D b j ω ≤ B} with hA
  set main := Q.real G / 2 * Real.exp (-(x ^ 2 / 2 * (1 + 12 * h))) with hmain
  set a₀ := t ^ 2 / 2 * (1 - α) with ha₀
  set K := Real.exp (-(t * M)) * Real.exp a₀ with hK
  have hK0 : 0 ≤ K := by positivity
  set C₂ := Real.exp ((2 * (t / sB)) ^ 2 * (1 + 2 * (t / sB) * c) / 2 * B) with hC₂
  -- the bound for each horizon `H ≥ n₁` and each `r > 0`
  have hH : ∀ r > 0, ∀ H ≥ n₁, main - K * (r / 2 * C₂ +
      Q.real {ω | ∑ j ∈ Finset.Ico n₀ H, truncVar Q ℱ D b j ω < B} / (2 * r)) ≤
        Q.real (G ∩ A) := by
    intro r hr H hH1
    have hnH : n₀ ≤ H := hn.trans hH1
    set Y := blockSum Q ℱ D b n₀ B H with hY
    have hYm : Measurable Y := measurable_blockSum Q hD b n₀ B H
    have hYb := abs_blockSum_le Q ℱ D hb0 hbL n₀ B H
    have hint : ∀ l : ℝ, Integrable (fun ω => Real.exp (l * Y ω)) Q := fun l =>
      integrable_of_abs_le (Real.continuous_exp.measurable.comp (hYm.const_mul l))
        (C := Real.exp (|l| * ((H - n₀ : ℕ) * c))) fun ω => by
          rw [abs_of_pos (Real.exp_pos _)]
          refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hYb ω) (abs_nonneg _)
    set Y' : Ω → ℝ := fun ω => Y ω / sB with hY'
    have hY'm : Measurable Y' := hYm.div_const _
    have hconv : ∀ τ : ℝ, ∫ ω, Real.exp (τ * Y' ω) ∂(Q.restrict G) =
        ∫ ω in G, Real.exp (τ / sB * Y ω) ∂Q := fun τ => by
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [hY']
      congr 1
      ring
    have hνuniv : (Q.restrict G).real univ = Q.real G := by
      rw [measureReal_restrict_apply_univ]
    have hupper : ∀ τ : ℝ, 0 ≤ τ → τ * c' ≤ α →
        ∫ ω, Real.exp (τ * Y' ω) ∂(Q.restrict G) ≤
          (Q.restrict G).real univ * Real.exp (τ ^ 2 / 2 * (1 + α)) := fun τ hτ hτc => by
      rw [hconv, hνuniv]
      have hl : 0 ≤ τ / sB := by positivity
      have hlc : τ / sB * c ≤ 1 := by
        have : τ / sB * c = τ * c' := by rw [hc'def]; ring
        rw [this]; linarith
      refine (setIntegral_exp_blockSum_le hD hb0 hbL hnH hB.le hG hl hlc).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) measureReal_nonneg
      have e : (τ / sB) ^ 2 * (1 + τ / sB * (2 * L)) / 2 * B = τ ^ 2 / 2 * (1 + τ * c') := by
        rw [hc'def, hcdef, ← hsB2]; field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hU1 := hupper x hx0.le (by linarith)
    have hU2 := hupper M (by positivity) (by linarith)
    -- the lower moment bound
    set NE := {ω | ∑ j ∈ Finset.Ico n₀ H, truncVar Q ℱ D b j ω < B} with hNE
    have hNEm : MeasurableSet NE := measurableSet_lt
      (Finset.measurable_sum _ fun j _ => (measurable_truncVar Q ℱ D b j).mono (ℱ.le j) le_rfl)
      measurable_const
    set I := ∫ ω in NE, Real.exp (t / sB * Y ω) ∂Q with hI
    have hlow : (Q.restrict G).real univ * Real.exp (t ^ 2 / 2 * (1 - α)) -
        Real.exp a₀ * I ≤ ∫ ω, Real.exp (t * Y' ω) ∂(Q.restrict G) := by
      rw [hconv, hνuniv]
      have hl : 0 ≤ t / sB := by positivity
      have hlc : 2 * (t / sB * (2 * L)) ≤ 1 := by
        have : 2 * (t / sB * (2 * L)) = 2 * (t * c') := by rw [hc'def, hcdef]; ring
        rw [this]; linarith
      have h1 := setIntegral_exp_blockSum_ge (Q := Q) hD hb0 hbL hnH hB.le hG hl hlc
      set κB := (t / sB) ^ 2 * (1 - 2 * (t / sB * (2 * L))) / 2 * (B - (2 * L) ^ 2) with hκB
      have e : κB = t ^ 2 / 2 * ((1 - 2 * (t * c')) * (1 - c' ^ 2)) := by
        rw [hκB, hc'def, hcdef, ← hsB2]; field_simp
      have hκa : a₀ ≤ κB := by
        rw [e, ha₀]
        have h2 : 1 - α ≤ (1 - 2 * (t * c')) * (1 - c' ^ 2) := by
          have h3 : 0 ≤ 2 * (t * c') * c' ^ 2 := by positivity
          have e3 : (1 - 2 * (t * c')) * (1 - c' ^ 2) =
              1 - 2 * (t * c') - c' ^ 2 + 2 * (t * c') * c' ^ 2 := by ring
          rw [e3]
          linarith
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
      have hIG : 0 ≤ ∫ ω in G, Real.exp (t / sB * Y ω) ∂Q :=
        setIntegral_nonneg hG' fun ω _ => (Real.exp_pos _).le
      by_cases hsg : 0 ≤ Q.real G - I
      · have h5 : Real.exp a₀ * (Q.real G - I) ≤ Real.exp κB * (Q.real G - I) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hκa) hsg
        have : Q.real G * Real.exp (t ^ 2 / 2 * (1 - α)) - Real.exp a₀ * I =
            Real.exp a₀ * (Q.real G - I) := by rw [ha₀]; ring
        rw [this]
        linarith
      · push Not at hsg
        have : Q.real G * Real.exp (t ^ 2 / 2 * (1 - α)) - Real.exp a₀ * I =
            Real.exp a₀ * (Q.real G - I) := by rw [ha₀]; ring
        rw [this]
        have := mul_neg_of_pos_of_neg (Real.exp_pos a₀) hsg
        linarith
    have hkol := kolmogorov_lower (ν := Q.restrict G) hY'm hx hh0 hh hα0 hα hxh
      (fun τ => (hint (τ / sB)).integrableOn.congr_fun (fun ω _ => by
        simp only [hY']; congr 1; ring) hG') hU1 hU2 hlow
    rw [hνuniv] at hkol
    -- the event of the Kolmogorov bound lies in `A`
    have hsub : {ω | x < Y' ω} ⊆ A := fun ω hω => by
      have h1 : x * √B < Y ω := by
        have := hω
        simp only [hY', mem_ofPred_eq] at this
        rw [lt_div_iff₀ hsB] at this
        exact this
      by_cases hb : B < ∑ j ∈ Finset.Ico n₀ n₁, truncVar Q ℱ D b j ω
      · left
        change x * √B < blockSum Q ℱ D b n₀ B n₁ ω
        rw [← blockSum_eq_of_budget Q ℱ D b hn hH1 hb]
        exact h1
      · right; exact not_lt.1 hb
    have hsub2 : (Q.restrict G).real {ω | x < Y' ω} ≤ Q.real (G ∩ A) := by
      rw [measureReal_restrict_apply (measurableSet_lt measurable_const hY'm), inter_comm]
      exact measureReal_mono (inter_subset_inter_right G hsub)
    -- the error term
    have hI_le : I ≤ r / 2 * C₂ + Q.real NE / (2 * r) := by
      have h1 := setIntegral_exp_le_amgm (hint (t / sB)) (hint (2 * (t / sB))) NE hr
      have h2 := setIntegral_exp_blockSum_le (Q := Q) hD hb0 hbL hnH hB.le
        (G := univ) MeasurableSet.univ (l := 2 * (t / sB)) (by positivity) (by
          have : 2 * (t / sB) * (2 * L) = 2 * (t * c') := by rw [hc'def, hcdef]; ring
          rw [this]; linarith)
      rw [setIntegral_univ, probReal_univ, one_mul] at h2
      have h3 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ r / 2 by positivity)
      rw [hC₂, hcdef]
      linarith
    have hE : Real.exp (-(t * M)) * (Real.exp a₀ * I) ≤
        K * (r / 2 * C₂ + Q.real NE / (2 * r)) := by
      have h6 := mul_le_mul_of_nonneg_left hI_le hK0
      have h7 : Real.exp (-(t * M)) * (Real.exp a₀ * I) = K * I := by rw [hK]; ring
      rw [h7]; exact h6
    have : main - K * (r / 2 * C₂ + Q.real NE / (2 * r)) ≤
        Q.real G / 2 * Real.exp (-(x ^ 2 / 2 * (1 + 12 * h))) -
          Real.exp (-(t * M)) * (Real.exp a₀ * I) := by rw [hmain]; linarith
    exact this.trans (hkol.trans hsub2)
  -- let `H → ∞`, then `r → 0`
  have hr : ∀ r > 0, main - K * (r / 2 * C₂) ≤ Q.real (G ∩ A) := by
    intro r hr
    have ht := tendsto_measureReal_budget (Q := Q) D b n₀ hinf
    have hlim : Tendsto (fun H => main - K * (r / 2 * C₂ +
        Q.real {ω | ∑ j ∈ Finset.Ico n₀ H, truncVar Q ℱ D b j ω < B} / (2 * r))) atTop
        (𝓝 (main - K * (r / 2 * C₂ + 0 / (2 * r)))) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul (tendsto_const_nhds.add
        (ht.div_const _)))
    rw [zero_div, add_zero] at hlim
    exact le_of_tendsto hlim (eventually_atTop.2 ⟨n₁, fun H hH1 => hH r hr H hH1⟩)
  have hC₂0 : 0 < C₂ := Real.exp_pos _
  refine le_of_forall_pos_le_add fun ε hε => ?_
  by_cases hK' : K = 0
  · have := hr 1 one_pos
    rw [hK', zero_mul, sub_zero] at this
    linarith
  · have hKpos : 0 < K := lt_of_le_of_ne hK0 (Ne.symm hK')
    have := hr (2 * ε / (K * C₂)) (by positivity)
    have e : K * (2 * ε / (K * C₂) / 2 * C₂) = ε := by field_simp
    rw [e] at this
    linarith

/-! ### Blocks as partial sums, and changing the truncation levels -/

/-- The truncated differences depend on the level sequence only through its current value. -/
theorem truncMD_congr (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) {b b' : ℕ → ℝ}
    {j : ℕ} (h : b j = b' j) : truncMD Q ℱ D b j = truncMD Q ℱ D b' j := by
  funext ω
  simp only [truncMD, truncMean, h]

/-- `truncVar` depends on the level sequence only through its current value. -/
theorem truncVar_congr (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) {b b' : ℕ → ℝ}
    {j : ℕ} (h : b j = b' j) : truncVar Q ℱ D b j = truncVar Q ℱ D b' j := by
  funext ω
  simp only [truncVar, truncMD_congr Q ℱ D h, h]

/-- The block sums over `[n₀, n₁)` only see the levels below `n₁`. -/
theorem blockSum_congr (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) {b b' : ℕ → ℝ}
    {n₀ n₁ : ℕ} (h : ∀ j < n₁, b j = b' j) (B : ℝ) :
    blockSum Q ℱ D b n₀ B n₁ = blockSum Q ℱ D b' n₀ B n₁ := by
  funext ω
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := (Finset.mem_Ico.1 hj).2
  have hset : blockSet Q ℱ D b n₀ B j = blockSet Q ℱ D b' n₀ B j := by
    ext ω'
    simp only [blockSet, mem_ofPred_eq]
    rw [Finset.sum_congr rfl fun i hi => congrFun (truncVar_congr Q ℱ D (b := b) (b' := b')
      (h i (by have := (Finset.mem_Ico.1 hi).2; omega))) ω']
  rw [hset, truncMD_congr Q ℱ D (h j hj')]

omit mΩ in
/-- **A block is a partial sum**: if membership in `Sⱼ` is inherited downwards on `[n₀, ∞)`,
then `Σ_{j ∈ [n₀, n₁)} 1_{Sⱼ}(ω) fⱼ(ω) = Σ_{j ∈ [n₀, T)} fⱼ(ω)` for some `T ∈ [n₀, n₁]`. -/
theorem exists_sum_indicator_eq {S : ℕ → Set Ω} {ω : Ω} {n₀ : ℕ}
    (hS : ∀ i j, n₀ ≤ i → i ≤ j → ω ∈ S j → ω ∈ S i) (f : ℕ → Ω → ℝ) {n₁ : ℕ}
    (hn : n₀ ≤ n₁) : ∃ T, n₀ ≤ T ∧ T ≤ n₁ ∧
      ∑ j ∈ Finset.Ico n₀ n₁, (S j).indicator (f j) ω = ∑ j ∈ Finset.Ico n₀ T, f j ω := by
  have key : ∃ T, n₀ ≤ T ∧ T ≤ n₁ ∧ (∀ j, n₀ ≤ j → j < T → ω ∈ S j) ∧
      ∀ j, T ≤ j → j < n₁ → ω ∉ S j := by
    induction n₁, hn using Nat.le_induction with
    | base => exact ⟨n₀, le_rfl, le_rfl, fun j h1 h2 => absurd h2 (not_lt.2 h1),
        fun j h1 h2 => absurd h2 (not_lt.2 h1)⟩
    | succ n hn ih =>
      obtain ⟨T, h1, h2, h3, h4⟩ := ih
      by_cases hmem : ω ∈ S n
      · have hT : T = n := by
          by_contra hne
          exact h4 T le_rfl (lt_of_le_of_ne h2 hne) (hS T n h1 h2 hmem)
        refine ⟨n + 1, by omega, le_rfl, fun j hj1 hj2 => ?_, fun j hj1 hj2 => by omega⟩
        exact hS j n hj1 (by omega) hmem
      · refine ⟨T, h1, by omega, h3, fun j hj1 hj2 => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj2 with hj | hj
        · exact h4 j hj1 hj
        · rw [hj]; exact hmem
  obtain ⟨T, h1, h2, h3, h4⟩ := key
  refine ⟨T, h1, h2, ?_⟩
  rw [← Finset.sum_Ico_consecutive _ h1 h2]
  have e1 : ∑ j ∈ Finset.Ico n₀ T, (S j).indicator (f j) ω = ∑ j ∈ Finset.Ico n₀ T, f j ω :=
    Finset.sum_congr rfl fun j hj => indicator_of_mem (h3 j (Finset.mem_Ico.1 hj).1
      (Finset.mem_Ico.1 hj).2) _
  have e2 : ∑ j ∈ Finset.Ico T n₁, (S j).indicator (f j) ω = 0 :=
    Finset.sum_eq_zero fun j hj => indicator_of_notMem (h4 j (Finset.mem_Ico.1 hj).1
      (Finset.mem_Ico.1 hj).2) _
  rw [e1, e2, add_zero]

/-- The block events are inherited downwards. -/
theorem mem_blockSet_of_le (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) (b : ℕ → ℝ)
    {n₀ : ℕ} {B : ℝ} {ω : Ω} {i j : ℕ} (hi : n₀ ≤ i) (hij : i ≤ j)
    (h : ω ∈ blockSet Q ℱ D b n₀ B j) : ω ∈ blockSet Q ℱ D b n₀ B i := by
  refine ⟨hi, le_trans ?_ h.2⟩
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl (by omega))
    fun k _ _ => truncVar_nonneg Q ℱ D b k ω

/-! ### The conditional second Borel–Cantelli lemma -/

/-- **A conditional second Borel–Cantelli lemma**: let `Aₖ ∈ 𝓕_{n_{k+1}}` (`n` monotone) and
`pₖ ≥ 0` with `Σ pₖ = ∞`, and suppose that for `k ≥ k₀` and every `G ∈ 𝓕_{nₖ}`,
`P(G ∩ Aₖ) ≥ pₖ P(G)`. Then almost surely `Aₖ` happens for infinitely many `k`. -/
theorem ae_frequently_of_cond_lower {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {n : ℕ → ℕ} (hn : Monotone n) {A : ℕ → Set Ω}
    (hA : ∀ k, MeasurableSet[ℱ (n (k + 1))] (A k)) {p : ℕ → ℝ} (hp0 : ∀ k, 0 ≤ p k)
    (hps : ¬ Summable p) {k₀ : ℕ}
    (hlow : ∀ k ≥ k₀, ∀ G : Set Ω, MeasurableSet[ℱ (n k)] G →
      p k * Q.real G ≤ Q.real (G ∩ A k)) :
    ∀ᵐ ω ∂Q, ∃ᶠ k in atTop, ω ∈ A k := by
  set C : ℕ → ℕ → Set Ω := fun K L => ⋂ k ∈ Finset.Ico K L, (A k)ᶜ with hC
  have hclaim : ∀ K ≥ k₀, ∀ L ≥ K, MeasurableSet[ℱ (n L)] (C K L) ∧
      Q.real (C K L) ≤ Real.exp (-∑ k ∈ Finset.Ico K L, p k) := by
    intro K hK L hL
    induction L, hL using Nat.le_induction with
    | base =>
      have e : C K K = univ := by
        ext ω; simp only [hC, Finset.Ico_self, Finset.notMem_empty, mem_iInter, mem_univ,
          iff_true]
        intro k hk; exact absurd hk id
      rw [e, Finset.Ico_self, Finset.sum_empty, neg_zero, Real.exp_zero, probReal_univ]
      exact ⟨MeasurableSet.univ, le_rfl⟩
    | succ L hL ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have e : C K (L + 1) = C K L ∩ (A L)ᶜ := by
        ext ω
        simp only [hC, mem_iInter, mem_inter_iff, Finset.mem_Ico]
        constructor
        · intro h
          exact ⟨fun k hk => h k ⟨hk.1, by omega⟩, h L ⟨hL, by omega⟩⟩
        · rintro ⟨h1, h2⟩ k hk
          rcases Nat.lt_succ_iff_lt_or_eq.1 hk.2 with hk2 | hk2
          · exact h1 k ⟨hk.1, hk2⟩
          · rw [hk2]; exact h2
      rw [e]
      have hm1 : MeasurableSet[ℱ (n (L + 1))] (C K L) := ℱ.mono (hn (Nat.le_succ L)) _ ih1
      refine ⟨hm1.inter (hA L).compl, ?_⟩
      have hAm : MeasurableSet (A L) := ℱ.le _ _ (hA L)
      have h1 := hlow L (hK.trans hL) (C K L) ih1
      have h2 : Q.real (C K L ∩ (A L)ᶜ) = Q.real (C K L) - Q.real (C K L ∩ A L) := by
        have := measureReal_inter_add_sdiff (μ := Q) (s := C K L) hAm
        change Q.real (C K L \ A L) = _
        linarith
      rw [h2, Finset.sum_Ico_succ_top hL, neg_add, Real.exp_add]
      have h3 : 1 - p L ≤ Real.exp (-p L) := Real.one_sub_le_exp_neg _
      have h4 : 0 ≤ Q.real (C K L) := measureReal_nonneg
      have h5 : (1 - p L) * Q.real (C K L) ≤ Real.exp (-p L) * Q.real (C K L) :=
        mul_le_mul_of_nonneg_right h3 h4
      have h6 : Real.exp (-p L) * Q.real (C K L) ≤
          Real.exp (-p L) * Real.exp (-∑ k ∈ Finset.Ico K L, p k) :=
        mul_le_mul_of_nonneg_left ih2 (Real.exp_pos _).le
      nlinarith
  have hdiv : Tendsto (fun L => ∑ k ∈ Finset.range L, p k) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hp0).1 hps
  have hK : ∀ K, ∀ᵐ ω ∂Q, ∃ k ≥ K, ω ∈ A k := by
    intro K
    set K' := max K k₀ with hK'
    set S := ⋂ k, ⋂ (_ : K' ≤ k), (A k)ᶜ with hS
    have hle : ∀ L ≥ K', Q.real S ≤ Real.exp (-∑ k ∈ Finset.Ico K' L, p k) := fun L hL =>
      (measureReal_mono fun ω hω => by
        simp only [hC, mem_iInter, Finset.mem_Ico]
        intro k hk
        exact (mem_iInter.1 (mem_iInter.1 hω k) hk.1)).trans
        (hclaim K' (le_max_right _ _) L hL).2
    have hlim : Tendsto (fun L => Real.exp (-∑ k ∈ Finset.Ico K' L, p k)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun L => ∑ k ∈ Finset.Ico K' L, p k) atTop atTop := by
        have h2 : Tendsto (fun L => ∑ k ∈ Finset.range L, p k -
            ∑ k ∈ Finset.range K', p k) atTop atTop := tendsto_atTop_add_const_right _ _ hdiv
        refine h2.congr' (eventually_atTop.2 ⟨K', fun L hL => ?_⟩)
        change _ = ∑ k ∈ Finset.Ico K' L, p k
        rw [Finset.sum_Ico_eq_sub _ hL]
      exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
    have h0 : Q.real S ≤ 0 :=
      ge_of_tendsto hlim (eventually_atTop.2 ⟨K', fun L hL => hle L hL⟩)
    have hS0 : Q S = 0 := by
      rw [← measureReal_eq_zero_iff]
      exact le_antisymm h0 measureReal_nonneg
    rw [measure_eq_zero_iff_ae_notMem] at hS0
    filter_upwards [hS0] with ω hω
    simp only [hS, mem_iInter, not_forall, mem_compl_iff, not_not] at hω
    obtain ⟨k, hk1, hk2⟩ := hω
    exact ⟨k, le_trans (le_max_left _ _) hk1, hk2⟩
  filter_upwards [ae_all_iff.2 hK] with ω hω
  rw [Filter.frequently_atTop]
  exact hω

end MeynTweedie.GeneralizedDrift
