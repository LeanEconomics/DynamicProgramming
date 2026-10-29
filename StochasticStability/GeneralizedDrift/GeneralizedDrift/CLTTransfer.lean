/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.MartingaleCLT
import GeneralizedDrift.PoissonEquation
import GeneralizedDrift.AperiodicErgodic

/-!
# Limit theorems from the stationary chain to every initial state (MT §17.1.2, §17.4–17.5)

Copied for Chapter 19 from the Chapter 17 project
(`LimitTheorems/CLTTransfer.lean`), with the namespace changed to
`MeynTweedie.GeneralizedDrift` and the imports to `GeneralizedDrift.*`.

The CLT of Theorem 17.4.5 and Theorem 17.5.3 is first obtained for the stationary chain `P_π`.
The book passes to every initial condition by "an obvious generalization of Proposition 17.1.6".
Proposition 17.1.6 is about events, and the CLT is not an event; this module supplies the two
transfers that are needed.

* `lln_pathFunctional`: the LLN for functionals of the whole path, `(1/n) Σ_{k<n} F(θᵏΦ) → E_π[F]`
  `P_x`-a.s. for every `x`, for a Harris chain with invariant probability `π` and `F ∈ L¹(P_π)`
  (ergodic Birkhoff theorem plus Proposition 17.1.6). It gives the LLN for `(ĝ(Φₖ₊₁) − Pĝ(Φₖ))²`.
* `tendstoInDistribution_pathKernel_of_stationary`: for an aperiodic positive Harris chain, if
  `n^{−1/2} Sₙ(g)` converges in distribution under `P_π`, it converges to the same limit under
  every `P_x`. The proof compares characteristic functions: after `m` steps the law of the chain
  is within `‖Pᵐ(x, ·) − π‖` of `π` in total variation (Theorem 13.3.3), and the first `m` terms
  are negligible after division by `√n`.

**Hypotheses.** The transfer uses aperiodicity (total variation convergence); every CLT of
§17.5 is for an ergodic, hence aperiodic, chain. The transfer for every period is now proved in
`PeriodicCLT` (`tendstoInDistribution_pathKernel_of_stationary_periodic`).
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### The LLN for path functionals -/

omit [MeasurableSpace X] in
/-- The event that the averages of `F ∘ θᵏ` converge to `c` is shift invariant. -/
theorem isShiftInvariant_tendsto_birkhoffAverage (F : (ℕ → X) → ℝ) (c : ℝ) :
    IsShiftInvariant {ω : ℕ → X | Tendsto (fun n => birkhoffAverage ℝ (shift 1) F n ω) atTop
      (𝓝 c)} := by
  refine isShiftInvariant_of_preimage ?_
  ext ω
  simp only [mem_preimage, mem_ofPred_eq]
  exact ⟨tendsto_birkhoffAverage_of_apply, tendsto_birkhoffAverage_apply⟩

/-- **The LLN for path functionals**: for a Harris chain with invariant probability `π` and a
measurable `F ∈ L¹(P_π)`, `(1/n) Σ_{k<n} F(θᵏΦ) → E_π[F]`, `P_x`-a.s., for every `x`. -/
theorem lln_pathFunctional [MeasurableSpace.CountablyGenerated X] {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hHar : IsHarris P ψ) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {F : (ℕ → X) → ℝ} (hFm : Measurable F)
    (hFi : Integrable F (pathMeasure P π)) (x : X) :
    ∀ᵐ ω ∂pathKernel P x, Tendsto (fun n => birkhoffAverage ℝ (shift 1) F n ω) atTop
      (𝓝 (∫ ω, F ω ∂pathMeasure P π)) := by
  have := isProbabilityMeasure_pathMeasure P π
  have := isMarkovKernel_pathKernel P
  have hmp := measurePreserving_shift hπ 1
  have hb := ae_tendsto_birkhoffAverage_of_ergodic hmp hFm hFi (ergodic_pathMeasure hHar π)
  have hE : MeasurableSet {ω : ℕ → X | Tendsto (fun n => birkhoffAverage ℝ (shift 1) F n ω)
      atTop (𝓝 (∫ ω, F ω ∂pathMeasure P π))} :=
    measurableSet_tendsto (𝓝 _) fun n => measurable_birkhoffAverage (measurable_shift 1) hFm n
  have h1 := (mem_ae_iff_prob_eq_one hE).1 hb
  exact (mem_ae_iff_prob_eq_one hE).2 (proposition_17_1_6 hHar hE
    (isShiftInvariant_tendsto_birkhoffAverage F _) π h1 x)

omit [MeasurableSpace X] in
/-- `birkhoffAverage` of `F` along the shift is `(1/n) Σ_{k<n} F(θᵏω)`. -/
theorem birkhoffAverage_shift_eq (F : (ℕ → X) → ℝ) (n : ℕ) (ω : ℕ → X) :
    birkhoffAverage ℝ (shift 1) F n ω = (∑ k ∈ Finset.range n, F (shift k ω)) / n := by
  rw [birkhoffAverage_eq_div, birkhoffSum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [shift_one_iterate]

/-! ### From the stationary chain to every initial state -/

/-- `∫ f d(κ ∘ₘ ν) = ∫ ∫ f dκ(y) ν(dy)` for complex integrable `f`. -/
theorem integral_measure_comp_complex {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (κ : Kernel Y Z) [IsSFiniteKernel κ] (ν : Measure Y) [SFinite ν] {f : Z → ℂ}
    (hf : Integrable f (κ ∘ₘ ν)) : ∫ z, f z ∂(κ ∘ₘ ν) = ∫ y, ∫ z, f z ∂κ y ∂ν := by
  rw [Measure.comp_eq_comp_const_apply] at hf ⊢
  rw [Kernel.integral_comp hf, Kernel.const_apply]

/-- `P_x ∘ (θᵐ)⁻¹ = P_{Pᵐ(x, ·)}`. -/
theorem pathKernel_map_shift (P : Kernel X X) [IsMarkovKernel P] (x : X) (m : ℕ) :
    (pathKernel P x).map (shift m) = pathMeasure P ((P ^ m : Kernel X X) x) := by
  have := isMarkovKernel_pathKernel P
  have h := markov_measure P (Measure.dirac x) (n := m) (G := univ) MeasurableSet.univ
  simp only [Measure.restrict_univ, pathMeasure_dirac] at h
  rw [h, pathKernel_map_coord, pathMeasure_eq_comp]

/-- `|∫ h dν − ∫ h dπ| ≤ 2 ‖ν − π‖` for complex `h` with `‖h‖ ≤ 1`. -/
theorem norm_integral_sub_le_two_tvNorm {ν π : Measure X} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure π] {h : X → ℂ} (hm : Measurable h) (h1 : ∀ x, ‖h x‖ ≤ 1) :
    ‖∫ x, h x ∂ν - ∫ x, h x ∂π‖ ≤ 2 * tvNorm ν π := by
  have hint : ∀ μ : Measure X, IsProbabilityMeasure μ → Integrable h μ := fun μ _ =>
    Integrable.of_bound hm.aestronglyMeasurable 1 (Eventually.of_forall h1)
  have hre : |∫ x, (h x).re ∂ν - ∫ x, (h x).re ∂π| ≤ tvNorm ν π :=
    abs_integral_sub_le_tvNorm ν π (Complex.measurable_re.comp hm) fun x =>
      (Complex.abs_re_le_norm _).trans (h1 x)
  have him : |∫ x, (h x).im ∂ν - ∫ x, (h x).im ∂π| ≤ tvNorm ν π :=
    abs_integral_sub_le_tvNorm ν π (Complex.measurable_im.comp hm) fun x =>
      (Complex.abs_im_le_norm _).trans (h1 x)
  have er : ∀ μ : Measure X, IsProbabilityMeasure μ → (∫ x, h x ∂μ).re = ∫ x, (h x).re ∂μ :=
    fun μ hμ => by
      have := Complex.reCLM.integral_comp_comm (hint μ hμ)
      simpa [Complex.reCLM_apply] using this.symm
  have ei : ∀ μ : Measure X, IsProbabilityMeasure μ → (∫ x, h x ∂μ).im = ∫ x, (h x).im ∂μ :=
    fun μ hμ => by
      have := Complex.imCLM.integral_comp_comm (hint μ hμ)
      simpa [Complex.imCLM_apply] using this.symm
  calc ‖∫ x, h x ∂ν - ∫ x, h x ∂π‖
      ≤ |(∫ x, h x ∂ν - ∫ x, h x ∂π).re| + |(∫ x, h x ∂ν - ∫ x, h x ∂π).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |∫ x, (h x).re ∂ν - ∫ x, (h x).re ∂π| + |∫ x, (h x).im ∂ν - ∫ x, (h x).im ∂π| := by
        rw [Complex.sub_re, Complex.sub_im, er ν inferInstance, er π inferInstance,
          ei ν inferInstance, ei π inferInstance]
    _ ≤ 2 * tvNorm ν π := by linarith

omit [MeasurableSpace X] in
/-- `Sₙ = Sₘ + Sₙ₋ₘ ∘ θᵐ` for `m ≤ n`. -/
theorem pathSum_split (g : X → ℝ) {m n : ℕ} (hmn : m ≤ n) (ω : ℕ → X) :
    pathSum g n ω = pathSum g m ω + pathSum g (n - m) (shift m ω) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [Nat.add_sub_cancel_left, pathSum, pathSum, pathSum, Finset.sum_range_add]
  congr 1

/-- **Transfer of the CLT** from the stationary chain to every initial state, for an aperiodic
positive Harris chain. -/
theorem tendstoInDistribution_pathKernel_of_stationary [MeasurableSpace.CountablyGenerated X]
    {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} (hph : IsPositiveHarris P ψ)
    (hap : IsAperiodic P ψ) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {g : X → ℝ} (hg : Measurable g) {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Z : Ω' → ℝ}
    (h : haveI := isProbabilityMeasure_pathMeasure P π
      TendstoInDistribution (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * pathSum g n ω) atTop Z
        (fun _ => pathMeasure P π) P') (x : X) :
    haveI := isMarkovKernel_pathKernel P
    TendstoInDistribution (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * pathSum g n ω) atTop Z
      (fun _ => pathKernel P x) P' := by
  have := isProbabilityMeasure_pathMeasure P π
  have := isMarkovKernel_pathKernel P
  have hSm : ∀ n : ℕ, Measurable fun ω : ℕ → X => (√(n : ℝ))⁻¹ * pathSum g n ω := fun n =>
    measurable_const.mul (measurable_pathSum hg n)
  refine TendstoInDistribution.of_tendsto_charFun (fun n => (hSm n).aemeasurable)
    h.aemeasurable_limit fun t => ?_
  set φ := charFun (P'.map Z) t with hφ
  -- the characteristic functions as integrals
  have hcf : ∀ (μ : Measure (ℕ → X)) (n : ℕ), charFun (μ.map fun ω => (√(n : ℝ))⁻¹ *
      pathSum g n ω) t = ∫ ω, Complex.exp ((t : ℂ) * (((√(n : ℝ))⁻¹ * pathSum g n ω : ℝ) : ℂ) *
        Complex.I) ∂μ := by
    intro μ n
    have hcont : Continuous fun y : ℝ => Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I) := by
      fun_prop
    rw [charFun_apply_real, integral_map (hSm n).aemeasurable hcont.aestronglyMeasurable]
  simp_rw [hcf]
  set E : (ℕ → X) → ℕ → ℕ → ℂ := fun ω n j => Complex.exp ((t : ℂ) *
    (((√(n : ℝ))⁻¹ * pathSum g j ω : ℝ) : ℂ) * Complex.I) with hE
  have hEm : ∀ n j, Measurable fun ω => E ω n j := fun n j =>
    Complex.measurable_exp.comp ((measurable_const.mul (Complex.measurable_ofReal.comp
      (measurable_const.mul (measurable_pathSum hg j)))).mul measurable_const)
  have hE1 : ∀ ω n j, ‖E ω n j‖ = 1 := fun ω n j => by
    simp only [hE]
    rw [show (t : ℂ) * (((√(n : ℝ))⁻¹ * pathSum g j ω : ℝ) : ℂ) * Complex.I =
      ((t * ((√(n : ℝ))⁻¹ * pathSum g j ω) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hEint : ∀ (μ : Measure (ℕ → X)) [IsProbabilityMeasure μ] n j,
      Integrable (fun ω => E ω n j) μ := fun μ _ n j =>
    Integrable.of_bound (hEm n j).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => (hE1 ω n j).le)
  -- for each `m`: the stationary part converges
  have hstat : ∀ m : ℕ, Tendsto (fun n => ∫ ω, E ω n (n - m) ∂pathMeasure P π) atTop (𝓝 φ) := by
    intro m
    have hN : Tendsto (fun n : ℕ => n - m) atTop atTop := tendsto_sub_atTop_nat m
    have hc : Tendsto (fun n : ℕ => √((n - m : ℕ) : ℝ) / √(n : ℝ)) atTop (𝓝 1) := by
      have h1 : Tendsto (fun n : ℕ => ((n - m : ℕ) : ℝ) / n) atTop (𝓝 1) := by
        have h2 : Tendsto (fun n : ℕ => 1 - (m : ℝ) / n) atTop (𝓝 (1 - 0)) :=
          tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
        rw [sub_zero] at h2
        refine h2.congr' (eventually_atTop.2 ⟨m + 1, fun n hn => ?_⟩)
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
        change (1 : ℝ) - m / n = ((n - m : ℕ) : ℝ) / n
        rw [Nat.cast_sub (by omega)]
        field_simp
      have h3 := (Real.continuous_sqrt.tendsto _).comp h1
      rw [Real.sqrt_one] at h3
      refine h3.congr fun n => ?_
      rw [Function.comp_apply, Real.sqrt_div' _ (Nat.cast_nonneg n)]
    have hX := tendstoInDistribution_const_mul_seq (tendstoInDistribution_comp_index h hN) hc
    rw [show (fun ω => 1 * Z ω) = Z from funext fun ω => one_mul _] at hX
    have hcf' := hX.tendsto_charFun t
    rw [← hφ] at hcf'
    refine hcf'.congr' (eventually_atTop.2 ⟨m + 1, fun n hn => ?_⟩)
    have hmeas : Measurable fun ω => √((n - m : ℕ) : ℝ) / √(n : ℝ) *
        ((√((n - m : ℕ) : ℝ))⁻¹ * pathSum g (n - m) ω) :=
      measurable_const.mul (measurable_const.mul (measurable_pathSum hg _))
    have hcont : Continuous fun y : ℝ => Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I) := by
      fun_prop
    rw [charFun_apply_real, integral_map hmeas.aemeasurable hcont.aestronglyMeasurable]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [hE]
    congr 2
    have hn0 : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < n by omega))
    have hnm0 : (0 : ℝ) < √((n - m : ℕ) : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast (show 0 < n - m by omega))
    have c1 : ((√((n - m : ℕ) : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnm0.ne'
    have c2 : ((√(n : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    push_cast
    field_simp
  -- for each `m`: the first `m` terms are negligible
  have hfirst : ∀ m : ℕ, Tendsto (fun n => ∫ ω, (E ω n n - E (shift m ω) n (n - m))
      ∂pathKernel P x) atTop (𝓝 0) := by
    intro m
    have hpt : ∀ ω, Tendsto (fun n => E ω n n - E (shift m ω) n (n - m)) atTop (𝓝 0) := by
      intro ω
      have hfac : ∀ n, m ≤ n → E ω n n - E (shift m ω) n (n - m) =
          E (shift m ω) n (n - m) * (Complex.exp ((t : ℂ) *
            (((√(n : ℝ))⁻¹ * pathSum g m ω : ℝ) : ℂ) * Complex.I) - 1) := by
        intro n hmn
        simp only [hE]
        rw [pathSum_split g hmn ω, mul_sub, mul_one, ← Complex.exp_add]
        congr 2
        push_cast
        ring
      have hlim : Tendsto (fun n : ℕ => Complex.exp ((t : ℂ) *
          (((√(n : ℝ))⁻¹ * pathSum g m ω : ℝ) : ℂ) * Complex.I) - 1) atTop (𝓝 0) := by
        have hsq : Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
        have h2 := hsq.mul_const (pathSum g m ω)
        rw [zero_mul] at h2
        have h3 : Continuous fun y : ℝ => Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I) - 1 := by
          fun_prop
        have h4 := (h3.tendsto 0).comp h2
        rw [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, sub_self] at h4
        exact h4
      have hnorm : Tendsto (fun n : ℕ => ‖Complex.exp ((t : ℂ) *
          (((√(n : ℝ))⁻¹ * pathSum g m ω : ℝ) : ℂ) * Complex.I) - 1‖) atTop (𝓝 0) := by
        simpa using hlim.norm
      exact squeeze_zero_norm' (eventually_atTop.2 ⟨m, fun n hn => by
        rw [hfac n hn, norm_mul, hE1, one_mul]⟩) hnorm
    have h1 := tendsto_integral_of_dominated_convergence (μ := pathKernel P x)
      (F := fun n ω => E ω n n - E (shift m ω) n (n - m)) (f := fun _ => (0 : ℂ))
      (fun _ => (2 : ℝ)) (fun n => ((hEm n n).sub ((hEm n (n - m)).comp
        (measurable_shift m))).aestronglyMeasurable) (integrable_const 2)
      (fun n => Eventually.of_forall fun ω => (norm_sub_le _ _).trans (by
        rw [hE1, hE1]; norm_num)) (Eventually.of_forall hpt)
    simpa using h1
  -- the Markov property at time `m` and total variation
  have hmarkov : ∀ m n, ∫ ω, E (shift m ω) n (n - m) ∂pathKernel P x =
      ∫ y, ∫ ω, E ω n (n - m) ∂pathKernel P y ∂(P ^ m : Kernel X X) x := by
    intro m n
    have := isMarkovKernel_pow P m
    rw [← integral_map (measurable_shift m).aemeasurable (hEm n (n - m)).aestronglyMeasurable,
      pathKernel_map_shift, pathMeasure_eq_comp]
    have := isProbabilityMeasure_pathMeasure P ((P ^ m : Kernel X X) x)
    rw [integral_measure_comp_complex]
    rw [← pathMeasure_eq_comp]
    exact hEint _ n (n - m)
  have hstatm : ∀ m n, ∫ ω, E ω n (n - m) ∂pathMeasure P π =
      ∫ y, ∫ ω, E ω n (n - m) ∂pathKernel P y ∂π := by
    intro m n
    rw [pathMeasure_eq_comp, integral_measure_comp_complex]
    rw [← pathMeasure_eq_comp]
    exact hEint _ n (n - m)
  have hhm : ∀ n j, Measurable fun y => ∫ ω, E ω n j ∂pathKernel P y := fun n j =>
    (StronglyMeasurable.integral_kernel (hEm n j).stronglyMeasurable).measurable
  have hh1 : ∀ n j y, ‖∫ ω, E ω n j ∂pathKernel P y‖ ≤ 1 := fun n j y =>
    (norm_integral_le_of_norm_le_const (C := 1) (Eventually.of_forall fun ω =>
      (hE1 ω n j).le)).trans (by simp)
  have htv : Tendsto (fun m => tvNorm ((P ^ m : Kernel X X) x) π) atTop (𝓝 0) :=
    theorem_13_3_3_dirac hph hap hπ x
  -- the ε-argument
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, hm⟩ := (Metric.tendsto_atTop.1 htv) (ε / 6) (by positivity)
  have hm' := hm m le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (tvNorm_nonneg _ _)] at hm'
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.1 (hfirst m)) (ε / 3) (by positivity)
  obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.1 (hstat m)) (ε / 3) (by positivity)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h1 := hN₁ n (le_of_max_le_left hn)
  have h2 := hN₂ n (le_of_max_le_right hn)
  rw [dist_eq_norm, sub_zero] at h1
  rw [dist_eq_norm] at h2 ⊢
  have h3 : ‖∫ ω, E (shift m ω) n (n - m) ∂pathKernel P x -
      ∫ ω, E ω n (n - m) ∂pathMeasure P π‖ ≤ 2 * (ε / 6) := by
    have := isMarkovKernel_pow P m
    rw [hmarkov, hstatm]
    exact (norm_integral_sub_le_two_tvNorm (hhm n (n - m)) (hh1 n (n - m))).trans
      (by linarith)
  have hEsh : Integrable (fun ω => E (shift m ω) n (n - m)) (pathKernel P x) :=
    Integrable.of_bound ((hEm n (n - m)).comp (measurable_shift m)).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => (hE1 _ n (n - m)).le)
  have hsplit : ∫ ω, E ω n n ∂pathKernel P x - φ =
      ∫ ω, (E ω n n - E (shift m ω) n (n - m)) ∂pathKernel P x +
        (∫ ω, E (shift m ω) n (n - m) ∂pathKernel P x - ∫ ω, E ω n (n - m) ∂pathMeasure P π) +
        (∫ ω, E ω n (n - m) ∂pathMeasure P π - φ) := by
    rw [integral_sub (hEint _ n n) hEsh]
    ring
  rw [hsplit]
  calc ‖∫ ω, (E ω n n - E (shift m ω) n (n - m)) ∂pathKernel P x +
        (∫ ω, E (shift m ω) n (n - m) ∂pathKernel P x - ∫ ω, E ω n (n - m) ∂pathMeasure P π) +
        (∫ ω, E ω n (n - m) ∂pathMeasure P π - φ)‖
      ≤ ‖∫ ω, (E ω n n - E (shift m ω) n (n - m)) ∂pathKernel P x‖ +
        ‖∫ ω, E (shift m ω) n (n - m) ∂pathKernel P x - ∫ ω, E ω n (n - m) ∂pathMeasure P π‖ +
        ‖∫ ω, E ω n (n - m) ∂pathMeasure P π - φ‖ := norm_add₃_le
    _ < ε / 3 + 2 * (ε / 6) + ε / 3 := by linarith
    _ = ε := by ring

end MeynTweedie.GeneralizedDrift
