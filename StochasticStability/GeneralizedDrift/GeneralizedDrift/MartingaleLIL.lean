/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.MartingaleLILLower
import GeneralizedDrift.IIDLIL

/-!
# The Hartman–Wintner law of the iterated logarithm for martingales

Copied for Chapter 19 from the Chapter 17 project
(`LimitTheorems/MartingaleLIL.lean`), with the namespace changed to
`MeynTweedie.GeneralizedDrift` and the imports to `GeneralizedDrift.*`.

**The martingale LIL** (`hasLIL_martingale`; Stout, *Ann. Math. Statist.* 41 (1970), and Stout,
*Almost Sure Convergence* (1974), §5.4): let `Dⱼ` be martingale differences with respect to a
filtration `𝓕` (`Dⱼ` is `𝓕ⱼ₊₁`-measurable and `E[Dⱼ | 𝓕ⱼ] = 0`), identically distributed and
square integrable, and suppose that the conditional variances and the conditional truncated
second moments satisfy the ergodic theorem: almost surely
`(1/n) Σ_{j<n} E[Dⱼ² | 𝓕ⱼ] → σ² = E[D₀²]` and, for every `K ∈ ℕ`,
`(1/n) Σ_{j<n} E[Dⱼ² 1{Dⱼ² ≥ K} | 𝓕ⱼ] → E[D₀² 1{D₀² ≥ K}]`. Then almost surely
`Sₙ = Σ_{j<n} Dⱼ` obeys the LIL with constant `σ` (`HasLIL`, the `ε`-form of
`limsup Sₙ/√(2 n log log n) = σ`, `liminf = −σ`). The case `σ = 0` is included.

These hypotheses hold for stationary ergodic square-integrable martingale differences, and in
particular for the Poisson martingale `Mₙ(g)` (17.43) of a positive Harris chain under `P_π`
(MT p. 448; `MartingaleLILChains`), which gives the LIL of MT Theorems 17.0.1 (iv), 17.5.3 and
17.5.4 (pp. 422, 452) without a minorization.

* `hasLIL_martingale`, `limsup_liminf_martingale` (the `Filter.limsup`/`liminf` form).
* `martingale_lil_tail_neg`: the tail hypothesis for `−Dⱼ`.

The upper half is `martingale_lil_upper` (`MartingaleLILUpper`), the lower half
`martingale_lil_lower` (`MartingaleLILLower`).
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The tail hypothesis of the martingale LIL passes from `Dⱼ` to `−Dⱼ`. -/
theorem martingale_lil_tail_neg {Q : Measure Ω} {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ}
    (hT : ∀ K : ℕ, ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n,
      Q[fun ω => {ω | (K : ℝ) ≤ D k ω ^ 2}.indicator (fun ω => D k ω ^ 2) ω | ℱ k] ω) / n)
      atTop (𝓝 (∫ ω, {ω | (K : ℝ) ≤ D 0 ω ^ 2}.indicator (fun ω => D 0 ω ^ 2) ω ∂Q))) :
    ∀ K : ℕ, ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n,
      Q[fun ω => {ω | (K : ℝ) ≤ (-D k ω) ^ 2}.indicator (fun ω => (-D k ω) ^ 2) ω | ℱ k] ω) / n)
      atTop (𝓝 (∫ ω, {ω | (K : ℝ) ≤ (-D 0 ω) ^ 2}.indicator (fun ω => (-D 0 ω) ^ 2) ω ∂Q)) := by
  intro K
  simp_rw [neg_sq]
  exact hT K

/-- **The Hartman–Wintner LIL for martingales** (Stout 1970): for identically distributed
square-integrable martingale differences `Dⱼ` whose conditional variances and conditional
truncated second moments satisfy the ergodic theorem, almost surely `Σ_{j<n} Dⱼ` obeys the LIL
with constant `σ = √(E[D₀²])`. -/
theorem hasLIL_martingale {Q : Measure Ω} [IsProbabilityMeasure Q] {ℱ : Filtration ℕ mΩ}
    {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0) (hident : ∀ k, IdentDistrib (D k) (D 0) Q Q)
    (hL2 : MemLp (D 0) 2 Q)
    (hV : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n,
      Q[fun ω => D k ω ^ 2 | ℱ k] ω) / n) atTop (𝓝 (∫ ω, D 0 ω ^ 2 ∂Q)))
    (hT : ∀ K : ℕ, ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n,
      Q[fun ω => {ω | (K : ℝ) ≤ D k ω ^ 2}.indicator (fun ω => D k ω ^ 2) ω | ℱ k] ω) / n)
      atTop (𝓝 (∫ ω, {ω | (K : ℝ) ≤ D 0 ω ^ 2}.indicator (fun ω => D 0 ω ^ 2) ω ∂Q))) :
    ∀ᵐ ω ∂Q, HasLIL (fun n => ∑ j ∈ Finset.range n, D j ω) (√(∫ ω, D 0 ω ^ 2 ∂Q)) := by
  obtain ⟨n1, n2, n3, n4, n5⟩ := martingale_lil_hyps_neg hD h0 hident hL2 hV
  have n6 := martingale_lil_tail_neg hT
  have hsq : √(∫ ω, (-D 0 ω) ^ 2 ∂Q) = √(∫ ω, D 0 ω ^ 2 ∂Q) := by simp_rw [neg_sq]
  have h1 : ∀ᵐ ω ∂Q, ∀ k : ℕ, ∀ᶠ n in atTop, ∑ j ∈ Finset.range n, D j ω ≤
      (√(∫ ω, D 0 ω ^ 2 ∂Q) + 1 / ((k : ℝ) + 1)) * lilScale n :=
    ae_all_iff.2 fun k => martingale_lil_upper hD h0 hident hL2 hV (by positivity)
  have h2 : ∀ᵐ ω ∂Q, ∀ k : ℕ, ∃ᶠ n in atTop, (√(∫ ω, D 0 ω ^ 2 ∂Q) - 1 / ((k : ℝ) + 1)) *
      lilScale n ≤ ∑ j ∈ Finset.range n, D j ω :=
    ae_all_iff.2 fun k => martingale_lil_lower hD h0 hident hL2 hV hT (by positivity)
  have h3 : ∀ᵐ ω ∂Q, ∀ k : ℕ, ∀ᶠ n in atTop, -∑ j ∈ Finset.range n, D j ω ≤
      (√(∫ ω, D 0 ω ^ 2 ∂Q) + 1 / ((k : ℝ) + 1)) * lilScale n :=
    ae_all_iff.2 fun k => martingale_lil_upper_neg hD h0 hident hL2 hV (by positivity)
  have h4 : ∀ᵐ ω ∂Q, ∀ k : ℕ, ∃ᶠ n in atTop, (√(∫ ω, D 0 ω ^ 2 ∂Q) - 1 / ((k : ℝ) + 1)) *
      lilScale n ≤ -∑ j ∈ Finset.range n, D j ω := by
    refine ae_all_iff.2 fun k => ?_
    have h := martingale_lil_lower n1 n2 n3 n4 n5 n6 (ε := 1 / ((k : ℝ) + 1)) (by positivity)
    rw [hsq] at h
    filter_upwards [h] with ω hω
    refine hω.mono fun n hn => ?_
    rwa [Finset.sum_neg_distrib] at hn
  filter_upwards [h1, h2, h3, h4] with ω a b c d
  exact ⟨lilBound_of_nat fun k => ⟨a k, b k⟩, lilBound_of_nat fun k => ⟨c k, d k⟩⟩

/-- **The martingale LIL in `limsup`/`liminf` form**: under the hypotheses of
`hasLIL_martingale`, almost surely `limsup Sₙ/√(2 n log log n) = σ` and
`liminf Sₙ/√(2 n log log n) = −σ`. -/
theorem limsup_liminf_martingale {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0) (hident : ∀ k, IdentDistrib (D k) (D 0) Q Q)
    (hL2 : MemLp (D 0) 2 Q)
    (hV : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n,
      Q[fun ω => D k ω ^ 2 | ℱ k] ω) / n) atTop (𝓝 (∫ ω, D 0 ω ^ 2 ∂Q)))
    (hT : ∀ K : ℕ, ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n,
      Q[fun ω => {ω | (K : ℝ) ≤ D k ω ^ 2}.indicator (fun ω => D k ω ^ 2) ω | ℱ k] ω) / n)
      atTop (𝓝 (∫ ω, {ω | (K : ℝ) ≤ D 0 ω ^ 2}.indicator (fun ω => D 0 ω ^ 2) ω ∂Q))) :
    ∀ᵐ ω ∂Q, limsup (fun n => (∑ j ∈ Finset.range n, D j ω) / lilScale n) atTop =
        √(∫ ω, D 0 ω ^ 2 ∂Q) ∧
      liminf (fun n => (∑ j ∈ Finset.range n, D j ω) / lilScale n) atTop =
        -√(∫ ω, D 0 ω ^ 2 ∂Q) := by
  filter_upwards [hasLIL_martingale hD h0 hident hL2 hV hT] with ω hω
  exact ⟨hω.limsup_eq, hω.liminf_eq⟩

end MeynTweedie.GeneralizedDrift
