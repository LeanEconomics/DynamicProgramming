/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveUtility.AABasics
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Limits of log-exponential certainty equivalents

Miao, §20.2.2, pp. 694–700. The limits that the text takes in passing from one specification to
another all reduce to two facts about the cumulant generating function
`Λ(t) = ln E_p exp(t v)` on a finite state space.

* `Λ(0) = 0` and `Λ'(0) = E_p v` (`aa_logmgf_hasDerivAt`), hence
  `t⁻¹ ln E_p exp(t v) → E_p v` as `t → 0` (`aa_tendsto_logmgf`).
* The soft minimum: if every state has positive probability,
  `−k⁻¹ ln E_p exp(−k v) → min v` as `k → ∞` (`aa_tendsto_softmin`), with the two-sided bound
  `min v ≤ −k⁻¹ ln E_p exp(−k v) ≤ min v − k⁻¹ ln p(s*)` (`aa_softmin_bounds`).

They are applied in `AAVariational` (`θ → ∞`), and in `AASmoothAmbiguity` (`ρ → 1`, `γ → 1`,
`η → ∞`, equations (20.16)–(20.18)).
-/

namespace Miao.RecursiveUtility

open Finset Filter Topology

variable {S : Type*} [Fintype S]

/-- The cumulant generating function `Λ(t) = ln ∑ₛ p(s) exp(t v(s))` has `Λ'(0) = E_p v`. -/
theorem aa_logmgf_hasDerivAt {p : S → ℝ} (hp : SS.IsDistribution p) (v : S → ℝ) :
    HasDerivAt (fun t => Real.log (∑ s, p s * Real.exp (t * v s))) (aa_E p v) 0 := by
  have hsum : HasDerivAt (fun t => ∑ s, p s * Real.exp (t * v s))
      (∑ s, p s * (Real.exp (0 * v s) * (1 * v s))) 0 := by
    apply HasDerivAt.fun_sum
    intro s _
    exact (((hasDerivAt_id (0 : ℝ)).mul_const (v s)).exp).const_mul (p s)
  have h1 : (∑ s, p s * Real.exp (0 * v s)) = 1 := by
    simp [hp.sum_eq_one]
  have := hsum.log (by rw [h1]; exact one_ne_zero)
  rw [h1, div_one] at this
  simpa [aa_E] using this

/-- `t⁻¹ ln E_p exp(t v) → E_p v` as `t → 0`, `t ≠ 0`. -/
theorem aa_tendsto_logmgf {p : S → ℝ} (hp : SS.IsDistribution p) (v : S → ℝ) :
    Tendsto (fun t => t⁻¹ * Real.log (∑ s, p s * Real.exp (t * v s))) (𝓝[≠] 0)
      (𝓝 (aa_E p v)) := by
  have := (hasDerivAt_iff_tendsto_slope_zero.1 (aa_logmgf_hasDerivAt hp v))
  simpa [hp.sum_eq_one] using this

/-- The soft-minimum bounds: for `k > 0` and a state `s*` minimising `v`,
`v(s*) ≤ −k⁻¹ ln E_p exp(−k v) ≤ v(s*) − k⁻¹ ln p(s*)`, provided `p(s*) > 0`. -/
theorem aa_softmin_bounds {p : S → ℝ} (hp : SS.IsDistribution p) (v : S → ℝ) {s₀ : S}
    (hmin : ∀ s, v s₀ ≤ v s) (hps : 0 < p s₀) {k : ℝ} (hk : 0 < k) :
    v s₀ ≤ -k⁻¹ * Real.log (∑ s, p s * Real.exp (-k * v s)) ∧
      -k⁻¹ * Real.log (∑ s, p s * Real.exp (-k * v s)) ≤ v s₀ - k⁻¹ * Real.log (p s₀) := by
  have hlow : p s₀ * Real.exp (-k * v s₀) ≤ ∑ s, p s * Real.exp (-k * v s) :=
    Finset.single_le_sum (f := fun s => p s * Real.exp (-k * v s))
      (fun s _ => mul_nonneg (hp.nonneg s) (Real.exp_pos _).le) (Finset.mem_univ s₀)
  have hup : ∑ s, p s * Real.exp (-k * v s) ≤ Real.exp (-k * v s₀) := by
    calc ∑ s, p s * Real.exp (-k * v s) ≤ ∑ s, p s * Real.exp (-k * v s₀) :=
          Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.2 (by nlinarith [hmin s])) (hp.nonneg s)
      _ = Real.exp (-k * v s₀) := by rw [← Finset.sum_mul, hp.sum_eq_one, one_mul]
  have hpos0 : 0 < p s₀ * Real.exp (-k * v s₀) := mul_pos hps (Real.exp_pos _)
  have hpos : 0 < ∑ s, p s * Real.exp (-k * v s) := hpos0.trans_le hlow
  have hk' : 0 < k⁻¹ := inv_pos.2 hk
  constructor
  · have h1 := Real.log_le_log hpos hup
    rw [Real.log_exp] at h1
    have h2 : k⁻¹ * Real.log (∑ s, p s * Real.exp (-k * v s)) ≤ k⁻¹ * (-k * v s₀) :=
      mul_le_mul_of_nonneg_left h1 hk'.le
    have h3 : k⁻¹ * (-k * v s₀) = -v s₀ := by field_simp
    linarith
  · have h1 := Real.log_le_log hpos0 hlow
    rw [Real.log_mul hps.ne' (Real.exp_pos _).ne', Real.log_exp] at h1
    have h2 : k⁻¹ * (Real.log (p s₀) + -k * v s₀) ≤
        k⁻¹ * Real.log (∑ s, p s * Real.exp (-k * v s)) := mul_le_mul_of_nonneg_left h1 hk'.le
    have h3 : k⁻¹ * (Real.log (p s₀) + -k * v s₀) = k⁻¹ * Real.log (p s₀) - v s₀ := by
      field_simp
      ring
    linarith

/-- **The soft minimum** (used for (20.18)): if `p(s*) > 0` at a minimiser `s*` of `v`, then
`−k⁻¹ ln E_p exp(−k v) → min v` as `k → ∞`. -/
theorem aa_tendsto_softmin {p : S → ℝ} (hp : SS.IsDistribution p) (v : S → ℝ) {s₀ : S}
    (hmin : ∀ s, v s₀ ≤ v s) (hps : 0 < p s₀) :
    Tendsto (fun k => -k⁻¹ * Real.log (∑ s, p s * Real.exp (-k * v s))) atTop (𝓝 (v s₀)) := by
  have hup : Tendsto (fun k : ℝ => v s₀ - k⁻¹ * Real.log (p s₀)) atTop (𝓝 (v s₀)) := by
    have := (tendsto_inv_atTop_zero.mul_const (Real.log (p s₀))).const_sub (v s₀)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with k hk
    exact (aa_softmin_bounds hp v hmin hps hk).1
  · filter_upwards [eventually_gt_atTop 0] with k hk
    exact (aa_softmin_bounds hp v hmin hps hk).2

end Miao.RecursiveUtility
