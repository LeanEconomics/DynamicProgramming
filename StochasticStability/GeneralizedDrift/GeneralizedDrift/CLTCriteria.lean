/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.CLTTransfer

/-!
# The CLT through Poisson's equation (MT §17.4.2 (CLT part), §17.5, Theorem 17.0.1)

Copied for Chapter 19 from the Chapter 17 project
(`LimitTheorems/CLTCriteria.lean`), with the namespace changed to
`MeynTweedie.GeneralizedDrift` and the imports to `GeneralizedDrift.*`.

Meyn and Tweedie, Theorem 17.4.5 (CLT part, p. 448), Lemmas 17.5.1–17.5.2 and Theorems 17.5.3,
17.5.4 (pp. 450–454), and Theorem 17.0.1 (p. 422). `ĝ` solves Poisson's equation
`ĝ − Pĝ = g − c`, `Dₖ = ĝ(Φₖ₊₁) − Pĝ(Φₖ)` are the increments of the martingale `Mₙ(g)` (17.43),
and `γ_g² = π(ĝ² − (Pĝ)²)` (17.46).

**The martingale.**
* `integral_sq_sum_of_martingale`: orthogonal increments, `E[(Σ_{k<n} Dₖ)²] = Σ E[Dₖ²]`.
* `poisson_increment_props`: under `P_π`, the `Dₖ` are `𝓕ₖ₊₁`-measurable, square integrable,
  with `E[Dₖ | 𝓕ₖ] = 0` and `E[Dₖ²] = γ_g²`.

**Results.**
* **Theorem 17.4.5**, the CLT (`theorem_17_4_5_clt_stationary`, p. 448): for a Harris chain
  with invariant probability `π` and a solution `ĝ` with `ĝ, Pĝ ∈ L²(π)`,
  `n^{−1/2} Sₙ(g − c) ⇒ N(0, γ_g²)` under `P_π`; `theorem_17_4_5_clt`: under every `P_x` when
  the chain is aperiodic (for every period now proved in `PeriodicCLT`,
  `theorem_17_4_5_clt_periodic`). The functional CLT (Theorem 17.4.4 and the FCLT part of
  Theorem 17.4.5) is proved in `FunctionalCLT` (`theorem_17_4_4`, `theorem_17_4_5_max`).
* **(17.4)** `tendsto_variance_poisson`: `(1/n) E_π[Sₙ(g − c)²] → γ_g²`.

The martingale CLT is `martingale_clt` (McLeish), proved in `MartingaleCLT`.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Orthogonality of martingale increments -/

/-- For martingale differences (`Dₖ` `𝓕ₖ₊₁`-measurable, `E[Dₖ | 𝓕ₖ] = 0`, `Dₖ ∈ L²`),
`E[(Σ_{k<n} Dₖ)²] = Σ_{k<n} E[Dₖ²]`. -/
theorem integral_sq_sum_of_martingale {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ}
    (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k)) (hL2 : ∀ k, MemLp (D k) 2 Q)
    (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0) (n : ℕ) :
    ∫ ω, (∑ k ∈ Finset.range n, D k ω) ^ 2 ∂Q = ∑ k ∈ Finset.range n, ∫ ω, D k ω ^ 2 ∂Q := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hS2 : MemLp (fun ω => ∑ k ∈ Finset.range n, D k ω) 2 Q :=
      memLp_finsetSum _ fun k _ => hL2 k
    have hSm : StronglyMeasurable[ℱ n] fun ω => ∑ k ∈ Finset.range n, D k ω := by
      refine (Finset.measurable_sum _ fun k hk => ?_).stronglyMeasurable
      exact (hD k).measurable.mono (ℱ.mono (Nat.succ_le_of_lt (Finset.mem_range.1 hk))) le_rfl
    have hcross : ∫ ω, (∑ k ∈ Finset.range n, D k ω) * D n ω ∂Q = 0 :=
      integral_mul_eq_zero_of_condExp (ℱ.le n) hSm (hS2.integrable_mul (hL2 n))
        ((hL2 n).integrable one_le_two) (h0 n)
    have hexp : (fun ω => (∑ k ∈ Finset.range (n + 1), D k ω) ^ 2) = fun ω =>
        (∑ k ∈ Finset.range n, D k ω) ^ 2 + 2 * ((∑ k ∈ Finset.range n, D k ω) * D n ω) +
          D n ω ^ 2 := by
      ext ω; rw [Finset.sum_range_succ]; ring
    have hi1 : Integrable (fun ω => (∑ k ∈ Finset.range n, D k ω) ^ 2) Q := hS2.integrable_sq
    have hi2 : Integrable (fun ω => 2 * ((∑ k ∈ Finset.range n, D k ω) * D n ω)) Q :=
      (hS2.integrable_mul (hL2 n)).const_mul 2
    have e1 := integral_add (hi1.add hi2) (hL2 n).integrable_sq
    have e2 := integral_add hi1 hi2
    simp only [Pi.add_apply] at e1 e2
    rw [hexp, e1, e2, integral_const_mul, hcross, ih, Finset.sum_range_succ]
    ring

/-! ### The increments of `Mₙ(g)` under `P_π` -/

/-- The increments `Dₖ = ĝ(Φₖ₊₁) − Pĝ(Φₖ)` under `P_π`: adapted, square integrable, centred,
with `E[Dₖ²] = π(ĝ² − (Pĝ)²)`. -/
theorem poisson_increment_props (P : Kernel X X) [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {gh : X → ℝ} (hghm : Measurable gh)
    (hgh2 : MemLp gh 2 π) (hPgh2 : MemLp (kernelInt P gh) 2 π) :
    (∀ k, StronglyMeasurable[natFilt (k + 1)]
      (fun ω : ℕ → X => gh (ω (k + 1)) - kernelInt P gh (ω k))) ∧
    (∀ k, MemLp (fun ω : ℕ → X => gh (ω (k + 1)) - kernelInt P gh (ω k)) 2 (pathMeasure P π)) ∧
    (∀ k, (pathMeasure P π)[fun ω : ℕ → X => gh (ω (k + 1)) - kernelInt P gh (ω k) |
      natFilt k] =ᵐ[pathMeasure P π] 0) ∧
    ∀ k, ∫ ω, (gh (ω (k + 1)) - kernelInt P gh (ω k)) ^ 2 ∂pathMeasure P π =
      ∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π := by
  have := isProbabilityMeasure_pathMeasure P π
  have hPm := measurable_kernelInt P hghm
  have hlaw : ∀ j, (pathMeasure P π).map (fun ω => ω j) = π := fun j => hπ.map_coord j
  have hL2 : ∀ (h : X → ℝ), MemLp h 2 π → ∀ j,
      MemLp (fun ω : ℕ → X => h (ω j)) 2 (pathMeasure P π) := fun h h2 j => by
    have : MemLp h 2 ((pathMeasure P π).map fun ω => ω j) := by rw [hlaw j]; exact h2
    exact this.comp_of_map (measurable_pi_apply j).aemeasurable
  refine ⟨fun k => ?_, fun k => (hL2 gh hgh2 (k + 1)).sub (hL2 _ hPgh2 k), fun k => ?_,
    integral_sq_poissonMart_increment P hπ hghm hgh2 hPgh2⟩
  · exact ((hghm.comp (measurable_coord_natFilt (k + 1))).sub
      ((hPm.comp (measurable_coord_natFilt k)).mono ((natFilt (X := X)).mono
        (Nat.le_succ k)) le_rfl)).stronglyMeasurable
  · have h1 := condExp_sub (m := natFilt k) (integrable_coord_of_invariant P hπ
      (hgh2.integrable one_le_two) (k + 1)) (integrable_coord_of_invariant P hπ
        (hPgh2.integrable one_le_two) k) (μ := pathMeasure P π)
    have h2 := condExp_poisson_increment P hπ hghm (hgh2.integrable one_le_two) k
    have h3 : (pathMeasure P π)[fun ω => kernelInt P gh (ω k) | natFilt k] =
        fun ω => kernelInt P gh (ω k) :=
      condExp_of_stronglyMeasurable ((natFilt (X := X)).le k)
        (hPm.comp (measurable_coord_natFilt k)).stronglyMeasurable
        (integrable_coord_of_invariant P hπ (hPgh2.integrable one_le_two) k)
    have h4 : (pathMeasure P π)[fun ω : ℕ → X => gh (ω (k + 1)) - kernelInt P gh (ω k) |
        natFilt k] =ᵐ[pathMeasure P π] (pathMeasure P π)[fun ω => gh (ω (k + 1)) | natFilt k] -
          (pathMeasure P π)[fun ω => kernelInt P gh (ω k) | natFilt k] := h1
    filter_upwards [h4, h2] with ω e1 e2
    rw [e1, Pi.sub_apply, e2, h3, sub_self, Pi.zero_apply]

/-! ### Theorem 17.4.5: the CLT -/

/-- A real function of fixed law, divided by `√n`, tends to `0` in probability: for
`h ∈ L²(π)` and an invariant `π`, `n^{−1/2} h(Φ_{k(n)}) → 0` in `P_π`-probability. -/
theorem measureReal_le_of_sq {π : Measure X} [IsProbabilityMeasure π] {h : X → ℝ}
    (hh2 : MemLp h 2 π) {a : ℝ} (ha : 0 < a) :
    π.real {x | a ≤ |h x|} ≤ (∫ x, h x ^ 2 ∂π) / a ^ 2 := by
  have h1 := mul_meas_ge_le_integral_of_nonneg (μ := π) (f := fun x => h x ^ 2)
    (Eventually.of_forall fun x => sq_nonneg _) hh2.integrable_sq (a ^ 2)
  have hset : {x | a ≤ |h x|} = {x | a ^ 2 ≤ h x ^ 2} := by
    ext x
    simp only [mem_ofPred_eq]
    rw [← sq_abs (h x)]
    exact (pow_le_pow_iff_left₀ ha.le (abs_nonneg _) two_ne_zero).symm
  rw [hset, le_div_iff₀ (by positivity), mul_comm]
  exact h1

/-- **Theorem 17.4.5**, the CLT (MT p. 448), for the stationary chain: for a Harris chain with
invariant probability `π` and a solution `ĝ` of `ĝ − Pĝ = g − c` with `ĝ, Pĝ ∈ L²(π)`,
`n^{−1/2} Sₙ(g − c)` converges in distribution under `P_π` to `N(0, γ_g²)`,
`γ_g² = π(ĝ² − (Pĝ)²)` (17.46). -/
theorem theorem_17_4_5_clt_stationary [MeasurableSpace.CountablyGenerated X] {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hH : IsHarris P ψ) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {g gh : X → ℝ} {c : ℝ}
    (hsol : IsPoissonSolution P g gh c) (hghm : Measurable gh) (hgm : Measurable g)
    (hgh2 : MemLp gh 2 π) (hPgh2 : MemLp (kernelInt P gh) 2 π)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 (∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π).toNNReal) P') :
    haveI := isProbabilityMeasure_pathMeasure P π
    TendstoInDistribution (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * pathSum (fun x => g x - c) n ω)
      atTop Z (fun _ => pathMeasure P π) P' := by
  have := isProbabilityMeasure_pathMeasure P π
  have hPm := measurable_kernelInt P hghm
  obtain ⟨hD, hL2, h0, hsq⟩ := poisson_increment_props P hπ hghm hgh2 hPgh2
  set D : ℕ → (ℕ → X) → ℝ := fun k ω => gh (ω (k + 1)) - kernelInt P gh (ω k) with hDdef
  set σ2 := ∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π with hσ2
  have hσ : 0 ≤ σ2 := by rw [← hsq 0]; exact integral_nonneg fun ω => sq_nonneg _
  -- the LLN for `Dₖ²`
  have hvar : ∀ᵐ ω ∂pathMeasure P π, Tendsto (fun n : ℕ =>
      (∑ k ∈ Finset.range n, D k ω ^ 2) / n) atTop (𝓝 σ2) := by
    set F : (ℕ → X) → ℝ := fun ω => (gh (ω 1) - kernelInt P gh (ω 0)) ^ 2 with hF
    have hFm : Measurable F :=
      ((hghm.comp (measurable_pi_apply 1)).sub (hPm.comp (measurable_pi_apply 0))).pow_const 2
    have hFi : Integrable F (pathMeasure P π) := (hL2 0).integrable_sq
    have hb := ae_tendsto_birkhoffAverage_of_ergodic (measurePreserving_shift hπ 1) hFm hFi
      (ergodic_pathMeasure hH π)
    have hFint : ∫ ω, F ω ∂pathMeasure P π = σ2 := hsq 0
    rw [hFint] at hb
    filter_upwards [hb] with ω hω
    refine hω.congr fun n => ?_
    rw [birkhoffAverage_shift_eq]
    congr 1
  have hbdd : ∀ n : ℕ, ∑ k ∈ Finset.range n, ∫ ω, D k ω ^ 2 ∂pathMeasure P π ≤ σ2 * n := by
    intro n
    simp_rw [hDdef, hsq]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
  have hM := martingale_clt hD hL2 h0 hσ hvar hbdd hZ
  -- the remainder `n^{−1/2}(Pĝ(Φ₀) − Pĝ(Φₙ)) → 0` in probability
  have hRm : ∀ n : ℕ, Measurable fun ω : ℕ → X =>
      (√(n : ℝ))⁻¹ * (kernelInt P gh (ω 0) - kernelInt P gh (ω n)) := fun n =>
    measurable_const.mul ((hPm.comp (measurable_pi_apply 0)).sub
      (hPm.comp (measurable_pi_apply n)))
  have hR : TendstoInMeasure (pathMeasure P π) (fun (n : ℕ) ω =>
      (√(n : ℝ))⁻¹ * (kernelInt P gh (ω 0) - kernelInt P gh (ω n))) atTop (fun _ => 0) := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    suffices hreal : Tendsto (fun n : ℕ => (pathMeasure P π).real {ω | ε ≤ dist
        ((√(n : ℝ))⁻¹ * (kernelInt P gh (ω 0) - kernelInt P gh (ω n))) 0}) atTop (𝓝 0) by
      have := ENNReal.tendsto_ofReal hreal
      rw [ENNReal.ofReal_zero] at this
      exact this.congr fun n => ofReal_measureReal
    set B := ∫ x, kernelInt P gh x ^ 2 ∂π with hB
    have hbound : ∀ n : ℕ, 1 ≤ n → (pathMeasure P π).real {ω | ε ≤ dist
        ((√(n : ℝ))⁻¹ * (kernelInt P gh (ω 0) - kernelInt P gh (ω n))) 0} ≤
        2 * (B / (ε * √(n : ℝ) / 2) ^ 2) := by
      intro n hn
      have hn' : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
      have ha : 0 < ε * √(n : ℝ) / 2 := by positivity
      have hsub : {ω : ℕ → X | ε ≤ dist ((√(n : ℝ))⁻¹ *
          (kernelInt P gh (ω 0) - kernelInt P gh (ω n))) 0} ⊆
          {ω | ε * √(n : ℝ) / 2 ≤ |kernelInt P gh (ω 0)|} ∪
            {ω | ε * √(n : ℝ) / 2 ≤ |kernelInt P gh (ω n)|} := by
        intro ω hω
        simp only [mem_ofPred_eq, Real.dist_eq, sub_zero, abs_mul,
          abs_of_pos (inv_pos.2 hn')] at hω
        rw [inv_mul_eq_div, le_div_iff₀ hn'] at hω
        by_contra hnot
        simp only [mem_union, mem_ofPred_eq, not_or, not_le] at hnot
        have := abs_sub (kernelInt P gh (ω 0)) (kernelInt P gh (ω n))
        linarith
      have hk : ∀ j, (pathMeasure P π).real {ω | ε * √(n : ℝ) / 2 ≤ |kernelInt P gh (ω j)|} =
          π.real {x | ε * √(n : ℝ) / 2 ≤ |kernelInt P gh x|} := by
        intro j
        have hset : MeasurableSet {x | ε * √(n : ℝ) / 2 ≤ |kernelInt P gh x|} :=
          measurableSet_le measurable_const (measurable_abs_of_measurable hPm)
        rw [show π.real {x | ε * √(n : ℝ) / 2 ≤ |kernelInt P gh x|} =
            ((pathMeasure P π).map fun ω => ω j).real
              {x | ε * √(n : ℝ) / 2 ≤ |kernelInt P gh x|} by rw [hπ.map_coord j],
          map_measureReal_apply (measurable_pi_apply j) hset]
        rfl
      calc (pathMeasure P π).real {ω | ε ≤ dist ((√(n : ℝ))⁻¹ *
            (kernelInt P gh (ω 0) - kernelInt P gh (ω n))) 0}
          ≤ (pathMeasure P π).real ({ω | ε * √(n : ℝ) / 2 ≤ |kernelInt P gh (ω 0)|} ∪
            {ω | ε * √(n : ℝ) / 2 ≤ |kernelInt P gh (ω n)|}) := measureReal_mono hsub
        _ ≤ (pathMeasure P π).real {ω | ε * √(n : ℝ) / 2 ≤ |kernelInt P gh (ω 0)|} +
            (pathMeasure P π).real {ω | ε * √(n : ℝ) / 2 ≤ |kernelInt P gh (ω n)|} :=
            measureReal_union_le _ _
        _ = 2 * π.real {x | ε * √(n : ℝ) / 2 ≤ |kernelInt P gh x|} := by rw [hk, hk]; ring
        _ ≤ 2 * (B / (ε * √(n : ℝ) / 2) ^ 2) := by
            gcongr; exact measureReal_le_of_sq hPgh2 ha
    have hlim : Tendsto (fun n : ℕ => 2 * (B / (ε * √(n : ℝ) / 2) ^ 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => (ε * √(n : ℝ) / 2) ^ 2) atTop atTop := by
        have := (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
          (show 0 < ε / 2 by positivity)
        refine (tendsto_pow_atTop two_ne_zero).comp (this.congr fun n => ?_)
        simp only [Function.comp_apply]; ring
      have h2 := (tendsto_const_nhds (x := B)).div_atTop h1
      have h3 := h2.const_mul 2
      rwa [mul_zero] at h3
    refine squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg)
      (eventually_atTop.2 ⟨1, hbound⟩) hlim
  -- combine
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ Z hM ?_ fun n =>
    (measurable_const.mul (measurable_pathSum (hgm.sub measurable_const) n)).aemeasurable
  refine hR.congr_left fun n => Eventually.of_forall fun ω => ?_
  simp only [Pi.sub_apply]
  rw [pathSum_eq_poissonMart hsol n ω, poissonMart]
  ring

/-- **Theorem 17.4.5**, the CLT from every initial state, for an aperiodic positive Harris
chain. -/
theorem theorem_17_4_5_clt [MeasurableSpace.CountablyGenerated X] {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hph : IsPositiveHarris P ψ) (hap : IsAperiodic P ψ)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) {g gh : X → ℝ} {c : ℝ}
    (hsol : IsPoissonSolution P g gh c) (hghm : Measurable gh) (hgm : Measurable g)
    (hgh2 : MemLp gh 2 π) (hPgh2 : MemLp (kernelInt P gh) 2 π)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 (∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π).toNNReal) P')
    (x : X) :
    haveI := isMarkovKernel_pathKernel P
    TendstoInDistribution (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * pathSum (fun x => g x - c) n ω)
      atTop Z (fun _ => pathKernel P x) P' :=
  tendstoInDistribution_pathKernel_of_stationary hph hap hπ (hgm.sub measurable_const)
    (theorem_17_4_5_clt_stationary hph.1 hπ hsol hghm hgm hgh2 hPgh2 hZ) x

/-! ### The asymptotic variance (17.4) -/

/-- **(17.4)**, (17.56): `(1/n) E_π[Sₙ(g − c)²] → γ_g² = π(ĝ² − (Pĝ)²)`. -/
theorem tendsto_variance_poisson (P : Kernel X X) [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {g gh : X → ℝ} {c : ℝ}
    (hsol : IsPoissonSolution P g gh c) (hghm : Measurable gh) (hgh2 : MemLp gh 2 π)
    (hPgh2 : MemLp (kernelInt P gh) 2 π) :
    Tendsto (fun n : ℕ => (∫ ω, pathSum (fun x => g x - c) n ω ^ 2 ∂pathMeasure P π) / n)
      atTop (𝓝 (∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π)) := by
  have := isProbabilityMeasure_pathMeasure P π
  have hPm := measurable_kernelInt P hghm
  obtain ⟨hD, hL2, h0, hsq⟩ := poisson_increment_props P hπ hghm hgh2 hPgh2
  set σ2 := ∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π with hσ2
  have hσ : 0 ≤ σ2 := by rw [← hsq 0]; exact integral_nonneg fun ω => sq_nonneg _
  set M : ℕ → (ℕ → X) → ℝ := fun n ω => ∑ k ∈ Finset.range n,
    (gh (ω (k + 1)) - kernelInt P gh (ω k)) with hM
  set R : ℕ → (ℕ → X) → ℝ := fun n ω => kernelInt P gh (ω 0) - kernelInt P gh (ω n) with hR
  have hlaw : ∀ j, (pathMeasure P π).map (fun ω => ω j) = π := fun j => hπ.map_coord j
  have hcoordL2 : ∀ j, MemLp (fun ω : ℕ → X => kernelInt P gh (ω j)) 2 (pathMeasure P π) :=
    fun j => by
      have : MemLp (kernelInt P gh) 2 ((pathMeasure P π).map fun ω => ω j) := by
        rw [hlaw j]; exact hPgh2
      exact this.comp_of_map (measurable_pi_apply j).aemeasurable
  have hML2 : ∀ n, MemLp (M n) 2 (pathMeasure P π) := fun n =>
    memLp_finsetSum _ fun k _ => hL2 k
  have hRL2 : ∀ n, MemLp (R n) 2 (pathMeasure P π) := fun n => (hcoordL2 0).sub (hcoordL2 n)
  have hEM : ∀ n, ∫ ω, M n ω ^ 2 ∂pathMeasure P π = n * σ2 := by
    intro n
    rw [hM, integral_sq_sum_of_martingale hD hL2 h0 n]
    simp_rw [hsq]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  set B := ∫ x, kernelInt P gh x ^ 2 ∂π with hB
  have hER : ∀ n, ∫ ω, R n ω ^ 2 ∂pathMeasure P π ≤ 4 * B := by
    intro n
    have hint_sq : ∀ j, ∫ ω, kernelInt P gh (ω j) ^ 2 ∂pathMeasure P π = B := fun j => by
      rw [hB, show ∫ x, kernelInt P gh x ^ 2 ∂π = ∫ x, kernelInt P gh x ^ 2 ∂((pathMeasure P π).map
        fun ω => ω j) by rw [hlaw j], integral_map (measurable_pi_apply j).aemeasurable
        (hPm.pow_const 2).aestronglyMeasurable]
    calc ∫ ω, R n ω ^ 2 ∂pathMeasure P π ≤ ∫ ω, (2 * kernelInt P gh (ω 0) ^ 2 +
          2 * kernelInt P gh (ω n) ^ 2) ∂pathMeasure P π := by
          refine integral_mono (hRL2 n).integrable_sq
            (((hcoordL2 0).integrable_sq.const_mul 2).add ((hcoordL2 n).integrable_sq.const_mul 2))
            fun ω => ?_
          simp only [hR]
          nlinarith [sq_nonneg (kernelInt P gh (ω 0) + kernelInt P gh (ω n))]
      _ = 4 * B := by
          rw [integral_add ((hcoordL2 0).integrable_sq.const_mul 2)
            ((hcoordL2 n).integrable_sq.const_mul 2), integral_const_mul, integral_const_mul,
            hint_sq, hint_sq]
          ring
  have hB0 : 0 ≤ B := integral_nonneg fun x => sq_nonneg _
  have hS : ∀ n ω, pathSum (fun x => g x - c) n ω = M n ω + R n ω := fun n ω => by
    rw [pathSum_eq_poissonMart hsol n ω, poissonMart]
    simp only [hM, hR]
    ring
  -- `|(1/n) E Sₙ² − σ²| ≤ δ σ² + (1 + 1/δ) 4B/n`
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ := ε / (2 * (σ2 + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt ((1 + δ⁻¹) * (4 * B) / (ε / 2))
  refine ⟨N + 1, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hNn : (N : ℝ) < n := by exact_mod_cast (show N < n by omega)
  have hexp : ∫ ω, pathSum (fun x => g x - c) n ω ^ 2 ∂pathMeasure P π =
      ∫ ω, M n ω ^ 2 ∂pathMeasure P π + ∫ ω, (2 * (M n ω * R n ω) + R n ω ^ 2)
        ∂pathMeasure P π := by
    have hiA : Integrable (fun ω => 2 * (M n ω * R n ω) + R n ω ^ 2) (pathMeasure P π) :=
      (((hML2 n).integrable_mul (hRL2 n)).const_mul 2).add (hRL2 n).integrable_sq
    have hsum := integral_add (hML2 n).integrable_sq hiA
    rw [← hsum]
    congr 1; ext ω; rw [hS]; ring
  have hcross : |∫ ω, (2 * (M n ω * R n ω) + R n ω ^ 2) ∂pathMeasure P π| ≤
      δ * (n * σ2) + (1 + δ⁻¹) * (4 * B) := by
    have hpt : ∀ ω, |2 * (M n ω * R n ω) + R n ω ^ 2| ≤ δ * M n ω ^ 2 + (1 + δ⁻¹) * R n ω ^ 2 := by
      intro ω
      have h1 : |2 * (M n ω * R n ω)| ≤ δ * M n ω ^ 2 + δ⁻¹ * R n ω ^ 2 := by
        rw [abs_le]
        have hd : δ * δ⁻¹ = 1 := mul_inv_cancel₀ hδpos.ne'
        constructor
        · nlinarith [sq_nonneg (δ * M n ω + R n ω), inv_pos.2 hδpos,
            mul_nonneg (inv_pos.2 hδpos).le (sq_nonneg (δ * M n ω + R n ω))]
        · nlinarith [sq_nonneg (δ * M n ω - R n ω), inv_pos.2 hδpos,
            mul_nonneg (inv_pos.2 hδpos).le (sq_nonneg (δ * M n ω - R n ω))]
      have h2 := abs_add_le (2 * (M n ω * R n ω)) (R n ω ^ 2)
      rw [abs_of_nonneg (sq_nonneg (R n ω))] at h2
      linarith
    have hiA : Integrable (fun ω => 2 * (M n ω * R n ω) + R n ω ^ 2) (pathMeasure P π) :=
      (((hML2 n).integrable_mul (hRL2 n)).const_mul 2).add (hRL2 n).integrable_sq
    have hiM : Integrable (fun ω => δ * M n ω ^ 2) (pathMeasure P π) :=
      (hML2 n).integrable_sq.const_mul δ
    have hiR : Integrable (fun ω => (1 + δ⁻¹) * R n ω ^ 2) (pathMeasure P π) :=
      (hRL2 n).integrable_sq.const_mul _
    have hiB : Integrable (fun ω => δ * M n ω ^ 2 + (1 + δ⁻¹) * R n ω ^ 2) (pathMeasure P π) :=
      hiM.add hiR
    have e1 : ∫ ω, (δ * M n ω ^ 2 + (1 + δ⁻¹) * R n ω ^ 2) ∂pathMeasure P π =
        δ * ∫ ω, M n ω ^ 2 ∂pathMeasure P π + (1 + δ⁻¹) * ∫ ω, R n ω ^ 2 ∂pathMeasure P π := by
      rw [integral_add hiM hiR, integral_const_mul, integral_const_mul]
    calc |∫ ω, (2 * (M n ω * R n ω) + R n ω ^ 2) ∂pathMeasure P π|
        ≤ ∫ ω, |2 * (M n ω * R n ω) + R n ω ^ 2| ∂pathMeasure P π :=
          abs_integral_le_integral_abs
      _ ≤ ∫ ω, (δ * M n ω ^ 2 + (1 + δ⁻¹) * R n ω ^ 2) ∂pathMeasure P π :=
          integral_mono hiA.abs hiB hpt
      _ = δ * (n * σ2) + (1 + δ⁻¹) * ∫ ω, R n ω ^ 2 ∂pathMeasure P π := by
          rw [e1, hEM]
      _ ≤ δ * (n * σ2) + (1 + δ⁻¹) * (4 * B) := by
          gcongr; exact hER n
  rw [Real.dist_eq, hexp, hEM, add_div, mul_div_cancel_left₀ _ hn0.ne']
  rw [show σ2 + (∫ ω, (2 * (M n ω * R n ω) + R n ω ^ 2) ∂pathMeasure P π) / n - σ2 =
    (∫ ω, (2 * (M n ω * R n ω) + R n ω ^ 2) ∂pathMeasure P π) / n by ring, abs_div,
    abs_of_pos hn0, div_lt_iff₀ hn0]
  have h1 : δ * (n * σ2) < ε / 2 * n := by
    rw [hδ]
    have : ε / (2 * (σ2 + 1)) * σ2 < ε / 2 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    nlinarith
  have h2 : (1 + δ⁻¹) * (4 * B) < ε / 2 * n := by
    have := (div_lt_iff₀ (show (0 : ℝ) < ε / 2 by positivity)).1 (hN.trans hNn)
    linarith
  linarith

end MeynTweedie.GeneralizedDrift
