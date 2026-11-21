/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OperatorsFixedPoints.Basics
import SearchAndMatching.JDBasics
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# A simple model of unemployment (the lake model)

AKMM, §20.3, pp. 595–597. Workers are employed or unemployed, the labour force is `1`, an
unemployed worker finds a job with probability `λ` and an employed worker loses it with
probability `σ`, both in `(0, 1)`. Unemployment follows `u_{t+1} = (1 − λ)u_t + σ(1 − u_t)`
(20.1).

* `eq_20_1`, `lakeNext`: the law of motion; `eq_20_2`: the unique steady state `ū = σ/(λ + σ)`,
  decreasing in `λ` and increasing in `σ` (`lake_ubar_anti_lam`, `lake_ubar_mono_sigma`).
* `lake_diff`, `lake_gap`: `u_{t+1} − u_t = (1 − λ − σ)(u_t − u_{t−1})` and
  `u_{t+1} − ū = (1 − λ − σ)(u_t − ū)`; `lake_abs_lt_one`: `|1 − λ − σ| < 1`.
* `lake_isContraction`, `lake_globallyStable`: the map is a contraction of modulus
  `|1 − λ − σ|` and globally stable (Sargent–Stachurski's `IsContractionOn`, `GloballyStable`);
  `lake_closed_form`, `lake_tendsto`, `lake_cauchy`: `u_t − ū = (1 − λ − σ)ᵗ(u_0 − ū)` (via
  Miao's `jd_affine_sol`), so `u_t → ū` and `(u_t)` is Cauchy.
* `lake_duration_series`, `lake_duration_recursion`: the expected duration of unemployment is
  `D = Σ_k (k + 1)λ(1 − λ)ᵏ = 1/λ`, and `D = 1/λ` is the unique solution of
  `D = λ·1 + (1 − λ)(1 + D)`.

Departure: the book says `|1 − λ − σ| ∈ (0, 1)`; it is `0` when `λ + σ = 1`
(`lake_abs_eq_zero_example`), so the correct range is `[0, 1)`. The numerical illustration
(`ū ≈ 7.0%`, `7.2%` after six months) is not formalised.
-/

namespace AKMM.FrictionalLaborMarkets

open Filter Topology

/-- AKMM, (20.1), p. 595: the lake-model map `u ↦ (1 − λ)u + σ(1 − u)`. -/
def lakeNext (lam σ u : ℝ) : ℝ := (1 - lam) * u + σ * (1 - u)

/-- AKMM, (20.1), p. 595: the law of motion is affine, `u_{t+1} = (1 − λ − σ)u_t + σ`. -/
theorem eq_20_1 (lam σ u : ℝ) : lakeNext lam σ u = (1 - lam - σ) * u + σ := by
  unfold lakeNext; ring

/-- AKMM, (20.2), p. 596: `ū = σ/(λ + σ)` is the unique steady state of (20.1). -/
theorem eq_20_2 {lam σ : ℝ} (h : 0 < lam + σ) (u : ℝ) :
    lakeNext lam σ u = u ↔ u = σ / (lam + σ) := by
  rw [eq_div_iff h.ne', lakeNext]
  constructor <;> intro hu <;> linarith

/-- AKMM, p. 596: the steady-state unemployment rate decreases in the job-finding probability. -/
theorem lake_ubar_anti_lam {σ lam₁ lam₂ : ℝ} (hσ : 0 < σ) (h₁ : 0 < lam₁) (h : lam₁ < lam₂) :
    σ / (lam₂ + σ) < σ / (lam₁ + σ) :=
  div_lt_div_of_pos_left hσ (by linarith) (by linarith)

/-- AKMM, p. 596: the steady-state unemployment rate increases in the separation probability. -/
theorem lake_ubar_mono_sigma {lam σ₁ σ₂ : ℝ} (hlam : 0 < lam) (h₁ : 0 < σ₁) (h : σ₁ < σ₂) :
    σ₁ / (lam + σ₁) < σ₂ / (lam + σ₂) := by
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- AKMM, p. 596: `u_{t+1} − u_t = (1 − λ − σ)(u_t − u_{t−1})`. -/
theorem lake_diff {lam σ : ℝ} {u : ℕ → ℝ} (hu : ∀ t, u (t + 1) = lakeNext lam σ (u t)) (t : ℕ) :
    u (t + 2) - u (t + 1) = (1 - lam - σ) * (u (t + 1) - u t) := by
  rw [hu (t + 1), hu t, eq_20_1, eq_20_1]; ring

/-- AKMM, p. 596: `u_{t+1} − ū = (1 − λ − σ)(u_t − ū)`. -/
theorem lake_gap {lam σ : ℝ} (h : 0 < lam + σ) (u : ℝ) :
    lakeNext lam σ u - σ / (lam + σ) = (1 - lam - σ) * (u - σ / (lam + σ)) := by
  rw [eq_20_1]; field_simp; ring

/-- AKMM, p. 596: for `λ, σ ∈ (0, 1)`, `|1 − λ − σ| < 1`. -/
theorem lake_abs_lt_one {lam σ : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) (hs0 : 0 < σ)
    (hs1 : σ < 1) : |1 - lam - σ| < 1 := by
  rw [abs_lt]; constructor <;> linarith

/-- AKMM, p. 596 (correction): `|1 − λ − σ|` can be `0`, e.g. `λ = σ = 1/2`, so the printed
range `(0, 1)` should be `[0, 1)`. -/
theorem lake_abs_eq_zero_example : |1 - (1 / 2 : ℝ) - 1 / 2| = 0 := by norm_num

/-- AKMM, p. 596: the lake map is a contraction of modulus `|1 − λ − σ|` on `ℝ`. -/
theorem lake_isContraction {lam σ : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) (hs0 : 0 < σ)
    (hs1 : σ < 1) :
    SargentStachurski.OperatorsFixedPoints.IsContractionOn (lakeNext lam σ) Set.univ
      |1 - lam - σ| where
  mapsTo := fun _ _ ↦ trivial
  nonneg := abs_nonneg _
  lt_one := lake_abs_lt_one hl0 hl1 hs0 hs1
  norm_sub_le := fun u _ v _ ↦ by
    rw [eq_20_1, eq_20_1, Real.norm_eq_abs, Real.norm_eq_abs,
      show (1 - lam - σ) * u + σ - ((1 - lam - σ) * v + σ) = (1 - lam - σ) * (u - v) by ring,
      abs_mul]

/-- AKMM, p. 596: the lake map is globally stable: a unique steady state to which every path
converges. -/
theorem lake_globallyStable {lam σ : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) (hs0 : 0 < σ)
    (hs1 : σ < 1) : SargentStachurski.OperatorsFixedPoints.GloballyStable (lakeNext lam σ) :=
  (lake_isContraction hl0 hl1 hs0 hs1).globallyStable_univ

/-- AKMM, p. 596: the closed form `u_t − ū = (1 − λ − σ)ᵗ(u_0 − ū)`. -/
theorem lake_closed_form {lam σ : ℝ} (h : 0 < lam + σ) {u : ℕ → ℝ}
    (hu : ∀ t, u (t + 1) = lakeNext lam σ (u t)) (t : ℕ) :
    u t - σ / (lam + σ) = (1 - lam - σ) ^ t * (u 0 - σ / (lam + σ)) := by
  have ha : (1 - lam - σ) ≠ 1 := by intro h'; linarith
  have hu' : ∀ t, u (t + 1) = (1 - lam - σ) * u t + σ := fun t ↦ by rw [hu t, eq_20_1]
  have e : σ / (1 - (1 - lam - σ)) = σ / (lam + σ) := by congr 1; ring
  have := Miao.SearchAndMatching.jd_affine_sol ha hu' t
  rwa [e] at this

/-- AKMM, p. 596: the unemployment rate converges to its steady state `σ/(λ + σ)`. -/
theorem lake_tendsto {lam σ : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) (hs0 : 0 < σ) (hs1 : σ < 1)
    {u : ℕ → ℝ} (hu : ∀ t, u (t + 1) = lakeNext lam σ (u t)) :
    Tendsto u atTop (𝓝 (σ / (lam + σ))) := by
  have hu' : ∀ t, u (t + 1) = (1 - lam - σ) * u t + σ := fun t ↦ by rw [hu t, eq_20_1]
  have e : σ / (1 - (1 - lam - σ)) = σ / (lam + σ) := by congr 1; ring
  have := Miao.SearchAndMatching.jd_affine_tendsto (lake_abs_lt_one hl0 hl1 hs0 hs1) hu'
  rwa [e] at this

/-- AKMM, p. 596: the unemployment rate is a Cauchy sequence. -/
theorem lake_cauchy {lam σ : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) (hs0 : 0 < σ) (hs1 : σ < 1)
    {u : ℕ → ℝ} (hu : ∀ t, u (t + 1) = lakeNext lam σ (u t)) : CauchySeq u :=
  (lake_tendsto hl0 hl1 hs0 hs1 hu).cauchySeq

/-- AKMM, p. 596: the expected duration of unemployment computed as a series,
`D = λ·1 + (1 − λ)λ·2 + (1 − λ)²λ·3 + ⋯ = 1/λ`. -/
theorem lake_duration_series {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam ≤ 1) :
    HasSum (fun k : ℕ ↦ lam * (1 - lam) ^ k * ((k : ℝ) + 1)) (1 / lam) := by
  have hr : ‖(1 - lam : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hr
  have h2 := hasSum_geometric_of_lt_one (r := 1 - lam) (by linarith) (by linarith)
  have h3 := (h1.add h2).mul_left lam
  have e : lam * ((1 - lam) / (1 - (1 - lam)) ^ 2 + (1 - (1 - lam))⁻¹) = 1 / lam := by
    rw [show 1 - (1 - lam) = lam by ring]
    field_simp; ring
  rw [e] at h3
  convert h3 using 1
  funext k; ring

/-- AKMM, p. 597: the recursive formulation `D = λ·1 + (1 − λ)(1 + D)` has the unique solution
`D = 1/λ`. -/
theorem lake_duration_recursion {lam : ℝ} (hl0 : 0 < lam) (D : ℝ) :
    D = lam * 1 + (1 - lam) * (1 + D) ↔ D = 1 / lam := by
  rw [eq_div_iff hl0.ne']
  constructor <;> intro h <;> nlinarith

end AKMM.FrictionalLaborMarkets
