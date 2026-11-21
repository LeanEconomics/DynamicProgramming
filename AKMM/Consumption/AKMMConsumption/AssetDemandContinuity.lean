/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import WeakConvergence.Parameters

/-!
# Continuity of aggregate asset demand

AKMM, §11.4.1, "Existence", p. 317: "`A(r) = ∫a′(a, y; r)dλ*_r` … `A(r)` is continuous if both
`a′` and `λ*_r` are, in turn, continuous in `r`", with the continuity of `λ*_r` from Stokey,
Lucas and Prescott, Theorems 12.12–12.13.

On a compact metric state space `S` with Markov kernels `P_r` that are jointly continuous in
`(s, r)` and have unique invariant probability measures `μ_r`, SLP Theorem 12.13 (reused,
`StokeyLucasPrescott.WeakConvergence.theorem_12_13`) makes `r ↦ μ_r` weakly continuous. If the
policy `a′(·; r)` is a bounded continuous function of the state that depends continuously on `r`
in the sup norm (the theorem of the maximum), then `A(r) = ∫a′(·; r)dμ_r` is (sequentially)
continuous (`hg_A_continuous`), and so continuous on any metric parameter space
(`hg_A_continuousOn`).
-/

namespace AKMM.Consumption

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction
  StokeyLucasPrescott.WeakConvergence

variable {S Θ : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S] [MetricSpace Θ]

/-- **AKMM, p. 317: `A(r)` is continuous.** Let `S` be compact, the transitions `P_θ` Markov and
jointly continuous (`P_{θₙ}(sₙ) → P_{θ₀}(s₀)` weakly), `μ_θ` the unique invariant probability
measure of `P_θ`, and the policies `f_θ ∈ C_b(S)` continuous in `θ` in the sup norm. Then
`θₙ → θ₀` implies `∫f_{θₙ}dμ_{θₙ} → ∫f_{θ₀}dμ_{θ₀}`. -/
theorem hg_A_continuous [CompactSpace S] (P : Θ → Kernel S S) [∀ θ, IsMarkovKernel (P θ)]
    (hcont : ∀ (s : ℕ → S) (θ : ℕ → Θ) (s₀ : S) (θ₀ : Θ), Tendsto s atTop (𝓝 s₀) →
      Tendsto θ atTop (𝓝 θ₀) → ConvWeak (fun n => P (θ n) (s n)) (P θ₀ s₀))
    (μ : Θ → Measure S) [∀ θ, IsProbabilityMeasure (μ θ)]
    (hfix : ∀ θ, adjointOp (P θ) (μ θ) = μ θ)
    (huniq : ∀ θ (ν : Measure S), IsProbabilityMeasure ν → adjointOp (P θ) ν = ν → ν = μ θ)
    (f : Θ → S →ᵇ ℝ) (hf : Continuous f) {θ : ℕ → Θ} {θ₀ : Θ} (hθ : Tendsto θ atTop (𝓝 θ₀)) :
    Tendsto (fun n => ∫ s, f (θ n) s ∂μ (θ n)) atTop (𝓝 (∫ s, f θ₀ s ∂μ θ₀)) := by
  have hw := theorem_12_13 P hcont μ hfix huniq hθ
  have h2 := hw (f θ₀)
  -- `|∫(fₙ − f₀)dμₙ| ≤ ‖fₙ − f₀‖ → 0`
  have hfn : Tendsto (fun n => f (θ n)) atTop (𝓝 (f θ₀)) := (hf.tendsto θ₀).comp hθ
  have h1 : Tendsto (fun n => ∫ s, (f (θ n) - f θ₀) s ∂μ (θ n)) atTop (𝓝 0) := by
    have hn : Tendsto (fun n => ‖f (θ n) - f θ₀‖) atTop (𝓝 0) := by
      have := (continuous_norm.tendsto 0).comp (tendsto_sub_nhds_zero_iff.2 hfn)
      rw [norm_zero] at this
      exact this
    refine squeeze_zero_norm (fun n => ?_) hn
    calc ‖∫ s, (f (θ n) - f θ₀) s ∂μ (θ n)‖ ≤ ‖f (θ n) - f θ₀‖ * (μ (θ n)).real Set.univ :=
          norm_integral_le_of_norm_le_const (Eventually.of_forall fun s =>
            BoundedContinuousFunction.norm_coe_le_norm _ s)
      _ = ‖f (θ n) - f θ₀‖ := by simp
  have := h1.add h2
  rw [zero_add] at this
  refine this.congr fun n => ?_
  simp only [BoundedContinuousFunction.coe_sub, Pi.sub_apply]
  rw [integral_sub ((f (θ n)).integrable _) ((f θ₀).integrable _)]
  ring

/-- AKMM, p. 317: under the hypotheses of `hg_A_continuous`, `A(θ) = ∫f_θdμ_θ` is continuous. -/
theorem hg_A_continuousOn [CompactSpace S] (P : Θ → Kernel S S) [∀ θ, IsMarkovKernel (P θ)]
    (hcont : ∀ (s : ℕ → S) (θ : ℕ → Θ) (s₀ : S) (θ₀ : Θ), Tendsto s atTop (𝓝 s₀) →
      Tendsto θ atTop (𝓝 θ₀) → ConvWeak (fun n => P (θ n) (s n)) (P θ₀ s₀))
    (μ : Θ → Measure S) [∀ θ, IsProbabilityMeasure (μ θ)]
    (hfix : ∀ θ, adjointOp (P θ) (μ θ) = μ θ)
    (huniq : ∀ θ (ν : Measure S), IsProbabilityMeasure ν → adjointOp (P θ) ν = ν → ν = μ θ)
    (f : Θ → S →ᵇ ℝ) (hf : Continuous f) : Continuous fun θ => ∫ s, f θ s ∂μ θ := by
  rw [continuous_iff_seqContinuous]
  intro θ θ₀ hθ
  exact hg_A_continuous P hcont μ hfix huniq f hf hθ

end AKMM.Consumption
