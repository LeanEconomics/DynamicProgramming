/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.MartingaleLILChains
import GeneralizedDrift.LimitApplications

/-!
# The LIL of Theorems 17.0.1 (iv), 17.5.3, 17.5.4 and of §17.6, without a minorization

Copied for Chapter 19 from the Chapter 17 project
(`LimitTheorems/MartingaleLILApplications.lean`), with the namespace changed to
`MeynTweedie.GeneralizedDrift` and the imports to `GeneralizedDrift.*`.

Meyn and Tweedie, Theorem 17.0.1 (iv) (p. 422), Theorems 17.5.3 and 17.5.4 (pp. 452–453),
Proposition 17.6.1 and Theorem 17.6.2 (pp. 454–456): "the CLT and LIL hold". Each CLT of these
results is proved in the project through a solution `ĝ` of Poisson's equation with
`ĝ, Pĝ ∈ L²(π)` (Lemma 17.5.2 (i)); the LIL follows from the same solution by
`hasLIL_pathSum_poisson` (the martingale LIL for `Mₙ(g)`, `MartingaleLILChains`), from every
initial state, with the constant of the CLT. Unlike `ChainLIL`, no one-step minorization and no
split-chain moment condition is assumed. The case `γ_g = 0` is included (the LIL with constant
`0` says `Sₙ(ḡ) = o(√(n log log n))`); the book assumes `γ_g² > 0`.

* **Theorem 17.5.3**, the LIL (`theorem_17_5_3_lil_poisson`): under the CLT moment condition and
  `|g| ≤ f`, `Sₙ(ḡ)` obeys the LIL with constant `γ_g = √(π(ĝ² − (Pĝ)²))`.
* **Theorem 17.5.4**, the LIL (`theorem_17_5_4_lil_poisson`): for `V`-uniformly ergodic chains
  and `g² ≤ V`.
* **Theorem 17.0.1 (iv)**, the LIL (`theorem_17_0_1_iv_lil_poisson`), with the constant
  `√γ_g²`, `γ_g²` the series (17.3).
* **Proposition 17.6.1**, the LIL (`proposition_17_6_1_lil_poisson`): random walk on a half line,
  `g(x) = x`.
* **Theorem 17.6.2**, the LIL (`theorem_17_6_2_lil_poisson`): the scalar linear model, with the
  constant `√(σ²/(1 − α)²)`.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X]

/-- **Theorem 17.5.3** (MT p. 452), the LIL: for an ergodic (positive Harris, aperiodic) chain
under the CLT moment condition and `|g| ≤ f`, from every initial state, `Sₙ(ḡ)`, `ḡ = g − π(g)`,
obeys the LIL with constant `γ_g = √(π(ĝ² − (Pĝ)²))`, `ĝ = Σₙ (Pⁿg − π(g))`, the constant of the
CLT `theorem_17_5_3_clt`. -/
theorem theorem_17_5_3_lil_poisson {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hph : IsPositiveHarris P ψ) (hap : IsAperiodic P ψ) {f : X → ℝ≥0∞} (hf : Measurable f)
    (hf1 : ∀ x, 1 ≤ f x) {C : Set X} {V : X → ℝ≥0∞} {b : ℝ≥0∞} (hpet : IsPetite P C)
    (hV : Measurable V) (hVfin : ∀ x, V x ≠ ∞) (hb : b ≠ ∞) (hdrift : DriftV3 P V f b C)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    (hπV2 : ∫⁻ x, V x ^ 2 ∂π ≠ ∞) {g : X → ℝ} (hgm : Measurable g)
    (hgf : ∀ x, ENNReal.ofReal |g x| ≤ f x) (x : X) :
    haveI := isMarkovKernel_pathKernel P
    ∀ᵐ ω ∂pathKernel P x, HasLIL (fun n => pathSum (fun y => g y - ∫ z, g z ∂π) n ω)
      (√(∫ x, (poissonSeries P π g x ^ 2 - kernelInt P (poissonSeries P π g) x ^ 2) ∂π)) := by
  obtain ⟨R, -, hL⟩ := lemma_17_5_2_i hph.1.1 hap hf hf1 hpet hV hVfin hb hdrift hπ hπV2
  obtain ⟨hsol, hghm, -, -, hgh2, hPgh2⟩ := hL g hgm hgf
  exact hasLIL_pathSum_poisson_initial hph.1 hπ hsol hgm hghm hgh2 hPgh2 x

/-- **Theorem 17.5.4** (MT p. 453), the LIL: for a positive Harris, aperiodic chain satisfying
(V4) for `V ≥ 1` finite and a petite set (a `V`-uniformly ergodic chain) and `g² ≤ V`, from every
initial state, `Sₙ(ḡ)` obeys the LIL with constant `γ_g = √(π(ĝ² − (Pĝ)²))`. -/
theorem theorem_17_5_4_lil_poisson {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hph : IsPositiveHarris P ψ) (hap : IsAperiodic P ψ) {V : X → ℝ≥0∞}
    (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) (hVfin : ∀ x, V x ≠ ∞) {ρ b : ℝ≥0∞} (hρ : ρ < 1)
    (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C) (h : DriftV4 P V ρ b C) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {g : X → ℝ} (hgm : Measurable g)
    (hg : ∀ x, ENNReal.ofReal (g x ^ 2) ≤ V x) (x : X) :
    haveI := isMarkovKernel_pathKernel P
    ∀ᵐ ω ∂pathKernel P x, HasLIL (fun n => pathSum (fun y => g y - ∫ z, g z ∂π) n ω)
      (√(∫ x, (poissonSeries P π g x ^ 2 - kernelInt P (poissonSeries P π g) x ^ 2) ∂π)) := by
  obtain ⟨ρ', b', C', hρ', hb', hC', h3, hπV2⟩ := lemma_17_5_1 hph.1.1 hap hV hV1 hVfin hρ hb
    hC h hπ
  have hct : (1 - ρ')⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hρ').ne'
  have hWm : Measurable fun x => V x ^ (1 / 2 : ℝ) := hV.pow_const _
  have hW1 : ∀ x, 1 ≤ V x ^ (1 / 2 : ℝ) := fun x => by
    have := ENNReal.rpow_le_rpow (hV1 x) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rwa [ENNReal.one_rpow] at this
  exact theorem_17_5_3_lil_poisson hph hap hWm hW1 hC' (hWm.const_mul _) (fun x =>
    ENNReal.mul_ne_top hct (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (hVfin x)))
    (ENNReal.mul_ne_top hct hb') h3 hπ hπV2 hgm (ofReal_abs_le_sqrt hg) x

/-- **Theorem 17.0.1** (iv), the LIL (MT p. 422), without a minorization: under the hypotheses
of (ii) (aperiodic, (V4) for `V ≥ 1` finite and a petite set, `g² ≤ V`), from every initial
state, `Sₙ(ḡ)` obeys the LIL with constant `γ_g = √γ_g²`, `γ_g²` the series (17.3) (the constant
of the CLT `theorem_17_0_1_iv`). -/
theorem theorem_17_0_1_iv_lil_poisson {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hph : IsPositiveHarris P ψ) (hap : IsAperiodic P ψ) {V : X → ℝ≥0∞}
    (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) (hVfin : ∀ x, V x ≠ ∞) {ρ b : ℝ≥0∞} (hρ : ρ < 1)
    (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C) (h : DriftV4 P V ρ b C) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {g : X → ℝ} (hgm : Measurable g)
    (hg : ∀ x, ENNReal.ofReal (g x ^ 2) ≤ V x) (x : X) :
    haveI := isMarkovKernel_pathKernel P
    ∀ᵐ ω ∂pathKernel P x, HasLIL (fun n => pathSum (fun y => g y - ∫ z, g z ∂π) n ω)
      (√(asymptoticVariance P π g)) := by
  obtain ⟨-, -, -, -, -, h6, -⟩ := theorem_17_5_4 hph hap hV hV1 hVfin hρ hb hC h hπ hgm hg
  have heq : asymptoticVariance P π g =
      ∫ x, (poissonSeries P π g x ^ 2 - kernelInt P (poissonSeries P π g) x ^ 2) ∂π := h6.symm
  rw [heq]
  exact theorem_17_5_4_lil_poisson hph hap hV hV1 hVfin hρ hb hC h hπ hgm hg x

/-- **Proposition 17.6.1** (MT p. 454), the LIL: if the increment law has mean `β < 0` and a
finite fifth moment, then for the invariant probability `π` of random walk on a half line, from
every initial state, `Σ_{k=1}^n (Φₖ − π(Φ))` obeys the LIL with constant `γ = √γ²`, `γ²` the
autocovariance series (17.3) (the constant of `proposition_17_6_1_clt`). -/
theorem proposition_17_6_1_lil_poisson (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => w) Γ) (hβ : ∫ w, w ∂Γ < 0)
    (hint : ∀ l ≤ 5, Integrable (fun w => |w| ^ l) Γ) {π : Measure ℝ≥0} [IsProbabilityMeasure π]
    (hπ : haveI := isMarkovKernel_halfLineWalkKernel Γ; IsInvariant (halfLineWalkKernel Γ) π)
    (x : ℝ≥0) :
    haveI := isMarkovKernel_halfLineWalkKernel Γ
    haveI := isMarkovKernel_pathKernel (halfLineWalkKernel Γ)
    ∀ᵐ ω ∂pathKernel (halfLineWalkKernel Γ) x,
      HasLIL (fun n => pathSum (fun y : ℝ≥0 => (y : ℝ) - ∫ z, (z : ℝ) ∂π) n ω)
        (√(asymptoticVariance (halfLineWalkKernel Γ) π fun y : ℝ≥0 => (y : ℝ))) := by
  have := isMarkovKernel_halfLineWalkKernel Γ
  obtain ⟨ψ, -, hap, hph, c, hc0, hct, X₀, D, hD, hpet, hdrift, hπV⟩ :=
    halfLine_cltMoment Γ hW hβ hint
  rw [(proposition_17_6_1_variance Γ hW hβ hint hπ).2.2.2]
  exact theorem_17_5_3_lil_poisson (f := fun x : ℝ≥0 => (x : ℝ≥0∞) + 1)
    (V := fun x : ℝ≥0 => c⁻¹ * (x : ℝ≥0∞) ^ 2) hph hap
    (measurable_coe_nnreal_ennreal.add measurable_const)
    (fun x => le_add_self) hpet ((measurable_coe_nnreal_ennreal.pow_const 2).const_mul _)
    (fun x => ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hc0) (ENNReal.pow_ne_top
      ENNReal.coe_ne_top)) (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hc0) hD) hdrift hπ
    (hπV π inferInstance hπ) NNReal.continuous_coe.measurable ofReal_abs_coe_le x

/-- **Theorem 17.6.2** (MT p. 456), the LIL, for the scalar linear model `Xₖ₊₁ = αXₖ + Wₖ₊₁`:
under the hypotheses of `theorem_17_6_2`, from every initial state, `Σ_{k=1}^n Xₖ` obeys the
LIL with constant `√(σ²/(1 − α)²)`, `σ² = E W²` (the constant of `theorem_17_6_2_clt`). -/
theorem theorem_17_6_2_lil_poisson (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {α : ℝ}
    (hα : |α| < 1) (hW1 : Integrable (fun w => w) Γ) (hW2 : Integrable (fun w => w ^ 2) Γ)
    (h0 : ∫ w, w ∂Γ = 0) {ψ : Measure ℝ}
    (hψ : haveI := isMarkovKernel_ar1Kernel Γ α; IsMaximalIrreducibility (ar1Kernel Γ α) ψ)
    (hap : IsAperiodic (ar1Kernel Γ α) ψ)
    (hcpt : ∀ K : Set ℝ, IsCompact K → IsPetite (ar1Kernel Γ α) K) {π : Measure ℝ}
    [IsProbabilityMeasure π] (hπ : haveI := isMarkovKernel_ar1Kernel Γ α
      IsInvariant (ar1Kernel Γ α) π) (x : ℝ) :
    haveI := isMarkovKernel_ar1Kernel Γ α
    haveI := isMarkovKernel_pathKernel (ar1Kernel Γ α)
    ∀ᵐ ω ∂pathKernel (ar1Kernel Γ α) x, HasLIL (fun n => pathSum (fun y => y) n ω)
      (√((∫ w, w ^ 2 ∂Γ) / (1 - α) ^ 2)) := by
  have := isMarkovKernel_ar1Kernel Γ α
  obtain ⟨⟨ρ, c, hρ, hc, C, hC, hdrift⟩, hph, hres⟩ :=
    theorem_17_6_2 Γ hα hW1 hW2 h0 hψ hap hcpt
  obtain ⟨hm, hvar, -⟩ := hres π hπ
  have hVm : Measurable fun x : ℝ => ‖x‖ₑ ^ 2 + 1 :=
    (measurable_enorm.pow_const 2).add measurable_const
  have hg : ∀ x : ℝ, ENNReal.ofReal (x ^ 2) ≤ ‖x‖ₑ ^ 2 + 1 := fun x => by
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    exact le_self_add
  rw [← hvar]
  have h := theorem_17_0_1_iv_lil_poisson hph hap hVm (fun x => le_add_self) (fun x =>
    ENNReal.add_ne_top.2 ⟨ENNReal.pow_ne_top enorm_ne_top, ENNReal.one_ne_top⟩) hρ hc hC hdrift
    hπ (g := fun y : ℝ => y) measurable_id hg x
  rw [hm] at h
  simp only [sub_zero] at h
  exact h

end MeynTweedie.GeneralizedDrift
