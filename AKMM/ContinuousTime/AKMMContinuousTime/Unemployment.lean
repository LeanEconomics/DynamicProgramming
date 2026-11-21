/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMContinuousTime.Mangasarian

/-!
# Unemployment flows

AKMM, §9.4 (pp. 259–260): (9.44) `u̇ = (N − u)σ − uλ` with separation rate `σ > 0`, job-finding
rate `λ > 0` and population `N`.

* The steady state `ū = σN/(σ + λ)` is the unique rest point (`unemployment_steady_state`).
* Every solution is `u(t) = ū + (u(0) − ū)e^{−(σ+λ)t}` (existence and uniqueness, the latter
  by Sargent–Stachurski's Example 10.1.1); so unemployment converges to `ū` from every initial
  value, monotonically in distance (`unemployment_solution`, `unemployment_unique`,
  `unemployment_converges`).
* The steady-state unemployment rate `ū/N = σ/(σ + λ)` is strictly increasing in `σ` and
  strictly decreasing in `λ` (`unemployment_rate_comparative_statics`).
-/

namespace AKMM.ContinuousTime

open Filter Topology

/-- AKMM, p. 260: the steady state of (9.44): `(N − u)σ − uλ = 0` iff `u = ū = σN/(σ + λ)`; and
the rate is `ū/N = σ/(σ + λ)`. -/
theorem unemployment_steady_state {N σ lam u : ℝ} (hσ : 0 < σ) (hlam : 0 < lam) (hN : N ≠ 0) :
    ((N - u) * σ - u * lam = 0 ↔ u = σ * N / (σ + lam)) ∧
      σ * N / (σ + lam) / N = σ / (σ + lam) := by
  have hs : σ + lam ≠ 0 := by positivity
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · rw [eq_div_iff hs]; linarith
  · rw [h]; field_simp; ring
  · field_simp

/-- AKMM, (9.44), p. 260: `u(t) = ū + (u₀ − ū)e^{−(σ+λ)t}` solves `u̇ = (N − u)σ − uλ` with
`u(0) = u₀`. -/
theorem unemployment_solution (N σ lam u₀ t : ℝ) (hs : σ + lam ≠ 0) :
    HasDerivAt (fun s => σ * N / (σ + lam) + (u₀ - σ * N / (σ + lam)) *
        Real.exp (-(σ + lam) * s))
      ((N - (σ * N / (σ + lam) + (u₀ - σ * N / (σ + lam)) * Real.exp (-(σ + lam) * t))) * σ -
        (σ * N / (σ + lam) + (u₀ - σ * N / (σ + lam)) * Real.exp (-(σ + lam) * t)) * lam) t := by
  have h := (SargentStachurski.ContinuousTime.hasDerivAt_exp_mul (-(σ + lam))
    (u₀ - σ * N / (σ + lam)) t).const_add (σ * N / (σ + lam))
  convert h using 1
  · funext s; ring
  · field_simp
    ring

/-- AKMM, (9.44), p. 260: every solution of `u̇ = (N − u)σ − uλ` on `[0, ∞)` is
`u(t) = ū + (u(0) − ū)e^{−(σ+λ)t}`. -/
theorem unemployment_unique {N σ lam : ℝ} {u : ℝ → ℝ} (hs : σ + lam ≠ 0)
    (hu : ∀ t, 0 ≤ t → HasDerivAt u ((N - u t) * σ - u t * lam) t) {t : ℝ} (ht : 0 ≤ t) :
    u t = σ * N / (σ + lam) + (u 0 - σ * N / (σ + lam)) * Real.exp (-(σ + lam) * t) := by
  set ub := σ * N / (σ + lam)
  have hd : ∀ s, 0 ≤ s → HasDerivAt (fun x => u x - ub) (-(σ + lam) * (u s - ub)) s := by
    intro s hs'
    convert (hu s hs').sub_const ub using 1
    simp only [ub]
    field_simp
    ring
  have h := SargentStachurski.ContinuousTime.eq_exp_of_hasDerivAt rfl hd ht
  linarith

/-- AKMM, p. 260: "unemployment converges to the steady-state value, regardless of the initial
unemployment": for `σ, λ > 0` every solution of (9.44) tends to `ū`, and its distance from `ū`
is nonincreasing. -/
theorem unemployment_converges {N σ lam : ℝ} {u : ℝ → ℝ} (hσ : 0 < σ) (hlam : 0 < lam)
    (hu : ∀ t, 0 ≤ t → HasDerivAt u ((N - u t) * σ - u t * lam) t) :
    Tendsto u atTop (𝓝 (σ * N / (σ + lam))) ∧
      AntitoneOn (fun t => |u t - σ * N / (σ + lam)|) (Set.Ici 0) := by
  have hs : 0 < σ + lam := by linarith
  have hform := fun t (ht : 0 ≤ t) => unemployment_unique hs.ne' hu ht
  refine ⟨?_, fun s hs' t ht hst => ?_⟩
  · have h := ((mangasarian_exp_neg_tendsto hs).const_mul (u 0 - σ * N / (σ + lam))).const_add
      (σ * N / (σ + lam))
    rw [mul_zero, add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [hform t ht]
  · simp only
    rw [hform s hs', hform t ht, add_sub_cancel_left, add_sub_cancel_left, abs_mul, abs_mul,
      abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (abs_nonneg _)

/-- AKMM, p. 260: the steady-state unemployment rate `σ/(σ + λ)` is strictly increasing in the
separation rate `σ` and strictly decreasing in the job-finding rate `λ`. -/
theorem unemployment_rate_comparative_statics {lam σ : ℝ} (hlam : 0 < lam) (hσ : 0 < σ) :
    StrictMonoOn (fun x => x / (x + lam)) (Set.Ioi 0) ∧
      StrictAntiOn (fun y => σ / (σ + y)) (Set.Ioi 0) := by
  refine ⟨fun x hx y hy hxy => ?_, fun x hx y hy hxy => ?_⟩
  · simp only [Set.mem_Ioi] at hx hy
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  · simp only [Set.mem_Ioi] at hx hy
    exact div_lt_div_of_pos_left hσ (by linarith) (by linarith)

end AKMM.ContinuousTime
