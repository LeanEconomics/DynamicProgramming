/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.MartingaleFCLTGeneral
import LimitTheorems.CLTCriteria
import LimitTheorems.PeriodicErgodic
import Mathlib.Analysis.Convex.Integral

/-!
# The functional CLT for Markov chains (MT §17.4.2)

Meyn and Tweedie, Theorem 17.4.4 (p. 447) and Theorem 17.4.5 (p. 448). `ĝ` solves Poisson's
equation `ĝ − Pĝ = g − c` (17.37), `γ_g² = π(ĝ² − (Pĝ)²)` (17.46), and
`sumPath g n = sₙ` is the interpolated partial-sum process (17.45) of `Sₙ(g) = Σ_{k=1}^n g(Φₖ)`.
Brownian motion is `wienerMeasure` on `C([0,1], ℝ)` (`BrownianMotion`).

**Tools.**
* `memLp_kernelInt_of_memLp`: `π(ĝ²) < ∞` implies `π((Pĝ)²) < ∞` (Jensen, as in the book).
* `pathMeasure_map_shift`, `integral_shift_eq`: the law of `θᵐΦ` under `P_μ` is `P_{μPᵐ}`.
* `ae_eventually_abs_le_sqrt`: the running maximum `max_{k≤2n} |h(Φₖ)| / √n → 0` a.s. from every
  initial law for `h ∈ L²(π)` (Theorem 17.3.3 for `h²`, via the LLN).
* `tendstoInDistribution_pathMeasure_of_stationary`: the transfer from `P_π` to every `P_μ` that
  the book calls "an obvious generalization of Proposition 17.1.6", for random elements of a
  metric space whose value moves little when the path is shifted. It uses Theorem 13.3.4 (i)
  (phase-averaged total variation convergence), so no aperiodicity is needed.
* `supPath_polygonal`: `sup_t sₙ(t) = max_{0≤k≤n} S_k`.
* (D.8) for `Mₙ(g)` (MT p. 448): `condExp_sq_poisson_increment`,
  `E_π[(ĝ(Φₖ₊₁) − Pĝ(Φₖ))² | 𝓕ₖ^Φ] = Pĝ²(Φₖ) − (Pĝ(Φₖ))²` (from the variance formula
  `integral_sq_sub_integral_eq`), and `condVar_poisson_tendsto`, the LLN for these conditional
  variances with limit `γ_g²`; (D.9) for `Mₙ(g)`: `lindeberg_poisson`.
* (17.48): `norm_sumPath_sub_polygonal_poissonMart_le`,
  `‖sₙ − mₙ‖ ≤ |Pĝ(Φ₀)| + max_{1≤k≤n} |Pĝ(Φₖ)|`.

**Results.**
* **Theorem 17.4.4** (`theorem_17_4_4`): for a positive Harris chain with a solution `ĝ ∈ L²(π)`
  and `γ_g² > 0`, `(nγ_g²)^{−1/2} sₙ ⇒ B` under `P_μ` for every initial distribution `μ`
  (`theorem_17_4_4_initial_state`: under every `P_x`);
  `theorem_17_4_4_stationary` is the case `μ = π`, proved as in the book: Theorem D.6.4
  (`theorem_D_6_4`, `MartingaleFCLTGeneral`) for the martingale `Mₙ(g)` (17.43), whose increments
  satisfy (D.8) and (D.9) under `P_π` (`condVar_poisson_tendsto`, `lindeberg_poisson`), and the
  sup-norm bound (17.48).
* **Theorem 17.4.5** (FCLT part): `theorem_17_4_5_endpoint` (`u(1)`:
  `(nγ_g²)^{−1/2} Sₙ ⇒ B(1)`), `theorem_17_4_5_max` (`max u`:
  `(nγ_g²)^{−1/2} max_{1≤k≤n} Sₖ ⇒ max_t B(t)`), and the CLT `theorem_17_4_5_clt_harris`
  (`n^{−1/2} Sₙ ⇒ N(0, γ_g²)` from every initial distribution, as a consequence of the FCLT, as in
  the book; `PeriodicCLT` proves the same CLT directly by characteristic functions).

**Hypotheses.** The book's `g` is centred, `c = π(g)`; here `c` is any constant with
`ĝ − Pĝ = g − c` (then necessarily `c = π(g)` when `g ∈ L¹(π)`). The book writes "a.s. [P_*]" for
the conclusion; it means convergence in distribution under every initial distribution.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Preliminaries -/

/-- **Jensen's inequality for the kernel** (MT p. 447): if `π` is invariant, `ĝ ∈ L²(π)` and `ĝ`
is integrable for every `P(x, ·)`, then `Pĝ ∈ L²(π)`. -/
theorem memLp_kernelInt_of_memLp {P : Kernel X X} [IsMarkovKernel P] {π : Measure X}
    (hπ : IsInvariant P π) {h : X → ℝ} (hhm : Measurable h) (hPi : ∀ x, Integrable h (P x))
    (hh2 : MemLp h 2 π) : MemLp (kernelInt P h) 2 π := by
  have hPm := measurable_kernelInt P hhm
  rw [memLp_two_iff_integrable_sq hPm.aestronglyMeasurable]
  refine ⟨(hPm.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => sq_nonneg _)]
  have hpt : ∀ x, ENNReal.ofReal (kernelInt P h x ^ 2) ≤ ∫⁻ y, ENNReal.ofReal (h y ^ 2) ∂P x := by
    intro x
    by_cases hx : Integrable (fun y => h y ^ 2) (P x)
    · have hJ := ConvexOn.map_integral_le (μ := P x) (even_two.convexOn_pow (𝕜 := ℝ))
        (continuous_pow 2).continuousOn isClosed_univ (Eventually.of_forall fun _ => mem_univ _)
        (hPi x) hx
      rw [← ofReal_integral_eq_lintegral_ofReal hx (Eventually.of_forall fun y => sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal hJ
    · have : ∫⁻ y, ENNReal.ofReal (h y ^ 2) ∂P x = ∞ := by
        by_contra hne
        refine hx ⟨(hhm.pow_const 2).aestronglyMeasurable, ?_⟩
        rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y => sq_nonneg _)]
        exact lt_top_iff_ne_top.2 hne
      rw [this]; exact le_top
  calc ∫⁻ x, ENNReal.ofReal (kernelInt P h x ^ 2) ∂π
      ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (h y ^ 2) ∂P x ∂π := lintegral_mono hpt
    _ = ∫⁻ y, ENNReal.ofReal (h y ^ 2) ∂(P ∘ₘ π) := (Measure.lintegral_bind
        (Kernel.aemeasurable _) (hhm.pow_const 2).ennreal_ofReal.aemeasurable).symm
    _ = ∫⁻ y, ENNReal.ofReal (h y ^ 2) ∂π := by rw [hπ]
    _ < ∞ := by
        have := hh2.integrable_sq.2
        rwa [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y => sq_nonneg _)] at this

/-- `P_μ ∘ (θᵐ)⁻¹ = P_{μPᵐ}`: the path after time `m` is the chain started at the law of `Φₘ`. -/
theorem pathMeasure_map_shift (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (m : ℕ) :
    (pathMeasure P μ).map (shift m) = pathMeasure P ((P ^ m : Kernel X X) ∘ₘ μ) := by
  have h := markov_measure P μ (n := m) (G := univ) MeasurableSet.univ
  simp only [Measure.restrict_univ] at h
  rw [h, pathMeasure_map_coord, pathMeasure_eq_comp]

/-- `∫ f d(κ ∘ μ) = ∫ ∫ f dκ(y) μ(dy)` for real integrable `f`. -/
theorem integral_measure_comp_real {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (κ : Kernel Y Z) [IsSFiniteKernel κ] (ν : Measure Y) [SFinite ν] {f : Z → ℝ}
    (hf : Integrable f (κ ∘ₘ ν)) : ∫ z, f z ∂(κ ∘ₘ ν) = ∫ y, ∫ z, f z ∂κ y ∂ν := by
  rw [Measure.comp_eq_comp_const_apply] at hf ⊢
  rw [Kernel.integral_comp hf, Kernel.const_apply]

/-- The Markov property at time `m` for a bounded functional: `E_μ[F ∘ θᵐ] = ∫ E_y[F] (μPᵐ)(dy)`. -/
theorem integral_shift_eq (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {F : (ℕ → X) → ℝ} (hF : Measurable F) {B : ℝ}
    (hB : ∀ ω, |F ω| ≤ B) (m : ℕ) :
    ∫ ω, F (shift m ω) ∂pathMeasure P μ =
      ∫ y, ∫ ω, F ω ∂pathKernel P y ∂((P ^ m : Kernel X X) ∘ₘ μ) := by
  have := isMarkovKernel_pathKernel P
  have := isMarkovKernel_pow P m
  have : IsProbabilityMeasure ((P ^ m : Kernel X X) ∘ₘ μ) := inferInstance
  have := isProbabilityMeasure_pathMeasure P ((P ^ m : Kernel X X) ∘ₘ μ)
  rw [← integral_map (measurable_shift m).aemeasurable hF.aestronglyMeasurable,
    pathMeasure_map_shift, pathMeasure_eq_comp]
  refine integral_measure_comp_real _ _ ?_
  rw [← pathMeasure_eq_comp]
  exact Integrable.of_bound hF.aestronglyMeasurable B
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hB ω)

/-! ### From the stationary chain to every initial distribution -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Transfer of convergence in distribution** (the "obvious generalization of Proposition
17.1.6" in the proof of Theorem 17.4.4, MT p. 447), for random elements `Yₙ(Φ)` of a metric
space: let the chain be positive Harris with invariant probability `π`. If `Yₙ ⇒ Z` under `P_π`,
and for every `j` the shifted path changes `Yₙ` by a vanishing amount,
`dist(Yₙ(θʲΦ), Yₙ(Φ)) → 0` `P_μ`-a.s., then `Yₙ ⇒ Z` under `P_μ`.

The proof tests against bounded Lipschitz functions. By Theorem 13.3.4 (i) the phase-averaged
law `d⁻¹ Σ_{r<d} μP^{dN+r}` of `Φ_{dN+r}` is close to `π` in total variation, so by the Markov
property `E_μ[f(Yₙ ∘ θ^{dN+r})]`, averaged over `r`, is close to `E_π[f(Yₙ)]`; and
`E_μ[f(Yₙ ∘ θʲ)] − E_μ[f(Yₙ)] → 0` by dominated convergence. -/
theorem tendstoInDistribution_pathMeasure_of_stationary {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} (hph : IsPositiveHarris P ψ) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {Y : ℕ → (ℕ → X) → E} (hYm : ∀ n, Measurable (Y n))
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → E}
    (h : haveI := isProbabilityMeasure_pathMeasure P π
      TendstoInDistribution Y atTop Z (fun _ => pathMeasure P π) P')
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hshift : ∀ j, ∀ᵐ ω ∂pathMeasure P μ,
      Tendsto (fun n => dist (Y n (shift j ω)) (Y n ω)) atTop (𝓝 0)) :
    haveI := isProbabilityMeasure_pathMeasure P μ
    TendstoInDistribution Y atTop Z (fun _ => pathMeasure P μ) P' := by
  have := isProbabilityMeasure_pathMeasure P π
  have := isProbabilityMeasure_pathMeasure P μ
  have := isMarkovKernel_pathKernel P
  obtain ⟨d, hper⟩ := exists_isPeriod P hph.2.1
  have hd : 0 < d := hper.1
  refine ⟨fun n => (hYm n).aemeasurable, h.aemeasurable_limit, ?_⟩
  have hZ := h.aemeasurable_limit
  refine (tendsto_iff_forall_lipschitz_integral_tendsto (μs := fun n =>
    (⟨(pathMeasure P μ).map (Y n), inferInstance⟩ : ProbabilityMeasure E))
    (μ := ⟨P'.map Z, inferInstance⟩)).2 fun f hfC hfL => ?_
  have hlim := (tendsto_iff_forall_lipschitz_integral_tendsto.1 h.tendsto) f hfC hfL
  obtain ⟨C, hC⟩ := hfC
  obtain ⟨L, hL⟩ := hfL
  have hfm : Measurable f := hL.continuous.measurable
  simp only [ProbabilityMeasure.coe_mk] at hlim ⊢
  rw [integral_map hZ hfm.aestronglyMeasurable] at hlim ⊢
  simp_rw [integral_map (hYm _).aemeasurable hfm.aestronglyMeasurable] at hlim ⊢
  set β := ∫ ω, f (Z ω) ∂P'
  -- a bound for `f` on the range of the `Yₙ`
  obtain ⟨ω₀⟩ : Nonempty (ℕ → X) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have := measure_univ (μ := pathMeasure P μ)
    rw [univ_eq_empty_iff.2 hne, measure_empty] at this
    exact zero_ne_one this
  set B := |f (Y 0 ω₀)| + C with hB
  have hfB : ∀ e, |f e| ≤ B := fun e => by
    have h1 := hC e (Y 0 ω₀)
    rw [Real.dist_eq] at h1
    have h2 := abs_sub_abs_le_abs_sub (f e) (f (Y 0 ω₀))
    simp only [hB]; linarith
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hfB (Y 0 ω₀))
  have hFm : ∀ n, Measurable fun ω => f (Y n ω) := fun n => hfm.comp (hYm n)
  -- the stationary part: `hₙ(y) = E_y[f(Yₙ)]`
  set Hk : ℕ → X → ℝ := fun n y => ∫ ω, f (Y n ω) ∂pathKernel P y with hhn
  have hhnm : ∀ n, Measurable (Hk n) := fun n =>
    (StronglyMeasurable.integral_kernel (hFm n).stronglyMeasurable).measurable
  have hhnB : ∀ n y, |Hk n y| ≤ B := fun n y => by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := B) (Eventually.of_forall fun ω => ?_)).trans
      (by simp)
    rw [Real.norm_eq_abs]; exact hfB _
  have hstat : ∀ n, ∫ ω, f (Y n ω) ∂pathMeasure P π = ∫ y, Hk n y ∂π := fun n => by
    rw [pathMeasure_eq_comp]
    refine integral_measure_comp_real _ _ ?_
    rw [← pathMeasure_eq_comp]
    exact Integrable.of_bound (hFm n).aestronglyMeasurable B
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hfB _)
  have hshiftint : ∀ n j, ∫ ω, f (Y n (shift j ω)) ∂pathMeasure P μ =
      ∫ y, Hk n y ∂((P ^ j : Kernel X X) ∘ₘ μ) := fun n j =>
    integral_shift_eq P μ (hFm n) (fun ω => hfB _) j
  -- the ε-argument
  rw [Metric.tendsto_atTop]
  intro ε hε
  have htv := theorem_13_3_4_i hph hper hπ μ
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.1 htv) (ε / (4 * (B + 1))) (by positivity)
  have hN₁' := hN₁ N₁ le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (tvNorm_nonneg _ _)] at hN₁'
  change tvNorm (phaseAvg P d N₁ μ) π < ε / (4 * (B + 1)) at hN₁'
  have := isFiniteMeasure_phaseAvg (P := P) hd N₁ μ
  -- the shift by `d N₁ + r` changes little
  have hgap : ∀ r, Tendsto (fun n => ∫ ω, f (Y n ω) ∂pathMeasure P μ -
      ∫ ω, f (Y n (shift (d * N₁ + r) ω)) ∂pathMeasure P μ) atTop (𝓝 0) := by
    intro r
    have h1 := tendsto_integral_of_dominated_convergence (μ := pathMeasure P μ)
      (F := fun n ω => f (Y n ω) - f (Y n (shift (d * N₁ + r) ω))) (f := fun _ => (0 : ℝ))
      (fun _ => 2 * B) (fun n => ((hFm n).sub ((hFm n).comp
        (measurable_shift _))).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]
        calc |f (Y n ω) - f (Y n (shift (d * N₁ + r) ω))|
            ≤ |f (Y n ω)| + |f (Y n (shift (d * N₁ + r) ω))| := abs_sub _ _
          _ ≤ B + B := add_le_add (hfB _) (hfB _)
          _ = 2 * B := by ring)
      ((hshift (d * N₁ + r)).mono fun ω hω => by
        have h2 : Tendsto (fun n => (L : ℝ) * dist (Y n (shift (d * N₁ + r) ω)) (Y n ω))
            atTop (𝓝 0) := by simpa using hω.const_mul (L : ℝ)
        refine squeeze_zero_norm (fun n => ?_) h2
        rw [Real.norm_eq_abs, ← Real.dist_eq, dist_comm]
        exact hL.dist_le_mul _ _)
    simp only [integral_zero] at h1
    refine h1.congr fun n => ?_
    exact integral_sub (f := fun ω => f (Y n ω))
      (g := fun ω => f (Y n (shift (d * N₁ + r) ω)))
      (Integrable.of_bound (hFm n).aestronglyMeasurable B
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hfB _))
      (Integrable.of_bound ((hFm n).comp (measurable_shift _)).aestronglyMeasurable B
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hfB _))
  have hev : ∀ᶠ n in atTop, ∀ r ∈ Finset.range d, |∫ ω, f (Y n ω) ∂pathMeasure P μ -
      ∫ ω, f (Y n (shift (d * N₁ + r) ω)) ∂pathMeasure P μ| < ε / 4 := by
    rw [Finset.eventually_all]
    intro r _
    have := (hgap r).eventually (Metric.ball_mem_nhds 0 (show 0 < ε / 4 by positivity))
    filter_upwards [this] with n hn
    simpa [Real.dist_eq] using hn
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 hev
  obtain ⟨N₃, hN₃⟩ := (Metric.tendsto_atTop.1 hlim) (ε / 4) (by positivity)
  refine ⟨max N₂ N₃, fun n hn => ?_⟩
  have h2 := hN₂ n (le_of_max_le_left hn)
  have h3 := hN₃ n (le_of_max_le_right hn)
  rw [Real.dist_eq] at h3 ⊢
  -- the phase average of the shifted means
  have hint : ∀ r, Integrable (Hk n) ((P ^ (d * N₁ + r) : Kernel X X) ∘ₘ μ) := fun r => by
    have := isMarkovKernel_pow P (d * N₁ + r)
    exact Integrable.of_bound (hhnm n).aestronglyMeasurable B
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hhnB n y)
  have havg : ∫ y, Hk n y ∂phaseAvg P d N₁ μ = (d : ℝ)⁻¹ *
      ∑ r ∈ Finset.range d, ∫ ω, f (Y n (shift (d * N₁ + r) ω)) ∂pathMeasure P μ := by
    rw [phaseAvg, integral_smul_measure, integral_finsetSum_measure fun r _ => hint r]
    simp_rw [hshiftint]
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  have htvb : |∫ y, Hk n y ∂phaseAvg P d N₁ μ - ∫ y, Hk n y ∂π| ≤
      (B + 1) * tvNorm (phaseAvg P d N₁ μ) π := by
    have h1 := abs_integral_sub_le_tvNorm (phaseAvg P d N₁ μ) π
      (f := fun y => Hk n y / (B + 1)) ((hhnm n).div_const _) fun y => by
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < B + 1), div_le_one (by positivity)]
        linarith [hhnB n y]
    rw [integral_div, integral_div, ← sub_div, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < B + 1), div_le_iff₀ (by positivity)] at h1
    linarith
  have hsum : |∫ ω, f (Y n ω) ∂pathMeasure P μ - ∫ y, Hk n y ∂phaseAvg P d N₁ μ| < ε / 4 := by
    rw [havg]
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have e : ∫ ω, f (Y n ω) ∂pathMeasure P μ - (d : ℝ)⁻¹ *
        ∑ r ∈ Finset.range d, ∫ ω, f (Y n (shift (d * N₁ + r) ω)) ∂pathMeasure P μ =
        (d : ℝ)⁻¹ * ∑ r ∈ Finset.range d, (∫ ω, f (Y n ω) ∂pathMeasure P μ -
          ∫ ω, f (Y n (shift (d * N₁ + r) ω)) ∂pathMeasure P μ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_sub,
        ← mul_assoc, inv_mul_cancel₀ hd'.ne', one_mul]
    rw [e, abs_mul, abs_of_pos (inv_pos.2 hd')]
    calc (d : ℝ)⁻¹ * |∑ r ∈ Finset.range d, (∫ ω, f (Y n ω) ∂pathMeasure P μ -
          ∫ ω, f (Y n (shift (d * N₁ + r) ω)) ∂pathMeasure P μ)|
        ≤ (d : ℝ)⁻¹ * ∑ r ∈ Finset.range d, |∫ ω, f (Y n ω) ∂pathMeasure P μ -
          ∫ ω, f (Y n (shift (d * N₁ + r) ω)) ∂pathMeasure P μ| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
      _ < (d : ℝ)⁻¹ * ∑ _r ∈ Finset.range d, ε / 4 :=
          mul_lt_mul_of_pos_left (Finset.sum_lt_sum_of_nonempty
            (Finset.nonempty_range_iff.2 hd.ne') h2) (by positivity)
      _ = ε / 4 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
            inv_mul_cancel₀ hd'.ne', one_mul]
  have htv' : (B + 1) * tvNorm (phaseAvg P d N₁ μ) π ≤ ε / 4 := by
    have := mul_le_mul_of_nonneg_left hN₁'.le (by positivity : (0 : ℝ) ≤ B + 1)
    rwa [mul_div_assoc', mul_comm 4, ← div_div, mul_div_cancel_left₀ _ (by positivity)] at this
  rw [hstat] at h3
  have t1 := abs_sub_le (∫ ω, f (Y n ω) ∂pathMeasure P μ) (∫ y, Hk n y ∂phaseAvg P d N₁ μ) β
  have t2 := abs_sub_le (∫ y, Hk n y ∂phaseAvg P d N₁ μ) (∫ y, Hk n y ∂π) β
  linarith

/-! ### The running maximum -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- The running maximum in `L²` (Theorem 17.3.3 applied to `h²`, MT p. 437): for a Harris chain
with invariant probability `π` and `h ∈ L²(π)`, from every initial distribution, almost surely
for every `ε > 0` eventually `|h(Φₖ)| ≤ ε √n` for all `k ≤ 2n`. -/
theorem ae_eventually_abs_le_sqrt {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hH : IsHarris P ψ) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {h : X → ℝ} (hm : Measurable h) (h2 : MemLp h 2 π) (μ : Measure X) [IsProbabilityMeasure μ] :
    ∀ᵐ ω ∂pathMeasure P μ, ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ k ≤ 2 * n, |h (ω k)| ≤ ε * √(n : ℝ) := by
  filter_upwards [lln_of_harris_measure hH hπ (hm.pow_const 2) h2.integrable_sq μ] with ω hω
  intro ε hε
  have hu : Tendsto (fun n : ℕ => (∑ j ∈ Finset.range n, h (ω (j + 1)) ^ 2) / n) atTop
      (𝓝 (∫ y, h y ^ 2 ∂π)) := hω.congr fun n => by rw [pathSum]
  have h1 := eventually_le_mul_of_tendsto_average (fun j => sq_nonneg (h (ω (j + 1)))) hu
    (show 0 < ε ^ 2 / 2 by positivity)
  have h2n : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_id.const_mul_atTop' (by norm_num)
  have h0 : ∀ᶠ n : ℕ in atTop, |h (ω 0)| ≤ ε * √(n : ℝ) := by
    have : Tendsto (fun n : ℕ => ε * √(n : ℝ)) atTop atTop :=
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hε
    exact this.eventually_ge_atTop _
  filter_upwards [h2n.eventually h1, h0] with n hn hn0 k hk
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact hn0
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h3 := hn j (by omega)
  push_cast at h3
  have h4 : h (ω (j + 1)) ^ 2 ≤ (ε * √(n : ℝ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    linarith
  exact abs_le_of_sq_le_sq' h4 (by positivity) |> fun h5 => abs_le.2 h5

/-! ### The conditions (D.8) for the martingale `Mₙ(g)` -/

/-- The variance formula `∫ (h − ∫ h dν)² dν = ∫ h² dν − (∫ h dν)²` for a probability `ν`. -/
theorem integral_sq_sub_integral_eq {ν : Measure X} [IsProbabilityMeasure ν] {h : X → ℝ}
    (hi : Integrable h ν) (h2 : Integrable (fun y => h y ^ 2) ν) :
    ∫ y, (h y - ∫ z, h z ∂ν) ^ 2 ∂ν = ∫ y, h y ^ 2 ∂ν - (∫ y, h y ∂ν) ^ 2 := by
  set a := ∫ z, h z ∂ν with ha
  have e : (fun y => (h y - a) ^ 2) = fun y => h y ^ 2 - 2 * a * h y + a ^ 2 := by
    ext y; ring
  rw [e, integral_add (f := fun y => h y ^ 2 - 2 * a * h y) (g := fun _ => a ^ 2)
    (h2.sub (hi.const_mul _)) (integrable_const _),
    integral_sub (f := fun y => h y ^ 2) (g := fun y => 2 * a * h y) h2 (hi.const_mul _),
    integral_const_mul, integral_const, probReal_univ, one_smul, ← ha]
  ring

/-- The conditional variance of the increments of `Mₙ(g)` (MT p. 448):
`E_π[(ĝ(Φₖ₊₁) − Pĝ(Φₖ))² | 𝓕ₖ^Φ] = Pĝ²(Φₖ) − (Pĝ(Φₖ))²`. -/
theorem condExp_sq_poisson_increment {P : Kernel X X} [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) {gh : X → ℝ} (hghm : Measurable gh)
    (hPi : ∀ x, Integrable gh (P x)) (hgh2 : MemLp gh 2 π) (k : ℕ) :
    (pathMeasure P π)[fun ω => (gh (ω (k + 1)) - kernelInt P gh (ω k)) ^ 2 | natFilt k]
      =ᵐ[pathMeasure P π]
      fun ω => kernelInt P (fun y => gh y ^ 2) (ω k) - kernelInt P gh (ω k) ^ 2 := by
  have := isProbabilityMeasure_pathMeasure P π
  have := isMarkovKernel_pathKernel P
  have hPm := measurable_kernelInt P hghm
  have hPgh2 := memLp_kernelInt_of_memLp hπ hghm hPi hgh2
  set H : (ℕ → X) → ℝ := fun ω => (gh (ω 1) - kernelInt P gh (ω 0)) ^ 2 with hH
  have hHm : Measurable H :=
    ((hghm.comp (measurable_pi_apply 1)).sub (hPm.comp (measurable_pi_apply 0))).pow_const 2
  have hHk : (fun ω : ℕ → X => (gh (ω (k + 1)) - kernelInt P gh (ω k)) ^ 2) =
      fun ω => H (shift k ω) := by
    ext ω; simp only [hH, shift, add_zero]
  have hint : Integrable (fun ω => H (shift k ω)) (pathMeasure P π) := by
    rw [← hHk]
    have hL2 := (poisson_increment_props P hπ hghm hgh2 hPgh2).2.1 k
    exact hL2.integrable_sq
  have h1 := markov_property P π k hHm hint
  rw [hHk]
  -- the good set: `ĝ²` is `P(x, ·)`-integrable
  have hgood : ∀ᵐ x ∂π, Integrable (fun y => gh y ^ 2) (P x) := by
    have h2 : Integrable (fun y => gh y ^ 2) (P ∘ₘ π) := by rw [hπ]; exact hgh2.integrable_sq
    exact ((Measure.integrable_comp_iff h2.1).1 h2).1
  have hgood' : ∀ᵐ ω ∂pathMeasure P π, Integrable (fun y => gh y ^ 2) (P (ω k)) := by
    have : ∀ᵐ x ∂(pathMeasure P π).map (fun ω => ω k),
        Integrable (fun y => gh y ^ 2) (P x) := by rw [hπ.map_coord k]; exact hgood
    exact ae_of_ae_map (measurable_pi_apply k).aemeasurable this
  filter_upwards [h1, hgood'] with ω e1 e2
  rw [e1]
  set x := ω k
  -- under `P_x`, `Φ₀ = x` as far as `Pĝ` sees
  have hx0 : ∀ᵐ ω' ∂pathKernel P x, kernelInt P gh (ω' 0) = kernelInt P gh x := by
    have hE : MeasurableSet {y : X | kernelInt P gh y ≠ kernelInt P gh x} :=
      (measurableSet_eq_fun hPm measurable_const).compl
    rw [ae_iff]
    change (pathKernel P x) ((fun ω' : ℕ → X => ω' 0) ⁻¹' {y | kernelInt P gh y ≠
        kernelInt P gh x}) = 0
    rw [← Measure.map_apply (measurable_pi_apply 0) hE, pathKernel_map_coord P x 0,
      pow_zero_apply, Measure.dirac_apply' _ hE]
    simp
  have hcongr : ∫ ω', H ω' ∂pathKernel P x =
      ∫ ω', (gh (ω' 1) - kernelInt P gh x) ^ 2 ∂pathKernel P x :=
    integral_congr_ae (hx0.mono fun ω' h => by simp only [hH, h])
  rw [hcongr, integral_coord_eq P (h := fun y => (gh y - kernelInt P gh x) ^ 2)
    ((hghm.sub measurable_const).pow_const 2) x 1, pow_one]
  exact integral_sq_sub_integral_eq (hPi x) e2

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Condition (D.8) for `Mₙ(g)`** (MT p. 448): by the LLN,
`(1/n) Σ_{k<n} E_π[(ĝ(Φₖ₊₁) − Pĝ(Φₖ))² | 𝓕ₖ^Φ] → π(Pĝ² − (Pĝ)²) = γ_g²` `P_π`-a.s. -/
theorem condVar_poisson_tendsto {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hH : IsHarris P ψ) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {gh : X → ℝ} (hghm : Measurable gh) (hPi : ∀ x, Integrable gh (P x)) (hgh2 : MemLp gh 2 π) :
    ∀ᵐ ω ∂pathMeasure P π, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n,
      (pathMeasure P π)[fun ω => (gh (ω (k + 1)) - kernelInt P gh (ω k)) ^ 2 | natFilt k] ω) /
        n) atTop (𝓝 (∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π)) := by
  have := isProbabilityMeasure_pathMeasure P π
  have hPm := measurable_kernelInt P hghm
  have hPgh2 := memLp_kernelInt_of_memLp hπ hghm hPi hgh2
  set f : X → ℝ := fun x => kernelInt P (fun y => gh y ^ 2) x - kernelInt P gh x ^ 2 with hf
  have hfm : Measurable f := (measurable_kernelInt P (hghm.pow_const 2)).sub (hPm.pow_const 2)
  have hP2i : Integrable (kernelInt P (fun y => gh y ^ 2)) π :=
    integrable_kernelInt P hπ (hghm.pow_const 2) hgh2.integrable_sq
  have hfi : Integrable f π := hP2i.sub hPgh2.integrable_sq
  have hP2int : ∫ x, kernelInt P (fun y => gh y ^ 2) x ∂π = ∫ x, gh x ^ 2 ∂π := by
    have h1 : Integrable (fun y => gh y ^ 2) (P ∘ₘ π) := by rw [hπ]; exact hgh2.integrable_sq
    have h2 := integral_measure_comp_real P π h1
    rw [hπ] at h2
    exact h2.symm
  have hfint : ∫ x, f x ∂π = ∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π := by
    rw [integral_sub hP2i hPgh2.integrable_sq, hP2int,
      integral_sub hgh2.integrable_sq hPgh2.integrable_sq]
  set F : (ℕ → X) → ℝ := fun ω => f (ω 0) with hF
  have hFm : Measurable F := hfm.comp (measurable_pi_apply 0)
  have hFi : Integrable F (pathMeasure P π) := integrable_coord_of_invariant P hπ hfi 0
  have hFint : ∫ ω, F ω ∂pathMeasure P π = ∫ x, f x ∂π := by
    rw [show ∫ x, f x ∂π = ∫ x, f x ∂((pathMeasure P π).map fun ω => ω 0) by
      rw [hπ.map_coord 0], integral_map (measurable_pi_apply 0).aemeasurable
      hfm.aestronglyMeasurable]
  have hb := ae_tendsto_birkhoffAverage_of_ergodic (measurePreserving_shift hπ 1) hFm hFi
    (ergodic_pathMeasure hH π)
  rw [hFint, hfint] at hb
  filter_upwards [hb, ae_all_iff.2 fun k => condExp_sq_poisson_increment hπ hghm hPi hgh2 k]
    with ω hω hce
  refine hω.congr fun n => ?_
  rw [birkhoffAverage_shift_eq]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hce k]
  simp only [hF, hf, shift, add_zero]

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Condition (D.9) for `Mₙ(g)`** (MT p. 448): for every `ε > 0`, `P_π`-a.s.,
`(1/n) Σ_{k<n} E_π[Dₖ² 1{Dₖ² ≥ εn} | 𝓕ₖ^Φ] → 0`, `Dₖ = ĝ(Φₖ₊₁) − Pĝ(Φₖ)`. By the LLN the averages
with a fixed level `b` tend to `E_π[D₀² 1{D₀² ≥ b}]`, which is small for large `b`. -/
theorem lindeberg_poisson {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hH : IsHarris P ψ) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {gh : X → ℝ} (hghm : Measurable gh) (hPi : ∀ x, Integrable gh (P x)) (hgh2 : MemLp gh 2 π)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂pathMeasure P π, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n,
      (pathMeasure P π)[fun ω => {ω | ε * n ≤ (gh (ω (k + 1)) - kernelInt P gh (ω k)) ^ 2}.indicator
        (fun ω => (gh (ω (k + 1)) - kernelInt P gh (ω k)) ^ 2) ω | natFilt k] ω) / n) atTop
      (𝓝 0) := by
  have := isProbabilityMeasure_pathMeasure P π
  have := isMarkovKernel_pathKernel P
  have hPm := measurable_kernelInt P hghm
  have hPgh2 := memLp_kernelInt_of_memLp hπ hghm hPi hgh2
  set H : (ℕ → X) → ℝ := fun ω => (gh (ω 1) - kernelInt P gh (ω 0)) ^ 2 with hHdef
  have hHm : Measurable H :=
    ((hghm.comp (measurable_pi_apply 1)).sub (hPm.comp (measurable_pi_apply 0))).pow_const 2
  have hHi : Integrable H (pathMeasure P π) :=
    ((poisson_increment_props P hπ hghm hgh2 hPgh2).2.1 0).integrable_sq
  set Hc : ℝ → (ℕ → X) → ℝ := fun c => {ω | c ≤ H ω}.indicator H with hHc
  have hHcm : ∀ c, Measurable (Hc c) := fun c =>
    hHm.indicator (measurableSet_le measurable_const hHm)
  have hHc0 : ∀ c ω, 0 ≤ Hc c ω := fun c ω =>
    Set.indicator_nonneg (fun ω _ => sq_nonneg _) ω
  have hHcle : ∀ c ω, Hc c ω ≤ H ω := fun c ω =>
    Set.indicator_le_self' (fun ω _ => sq_nonneg _) ω
  have hHcmono : ∀ c c' ω, c ≤ c' → Hc c' ω ≤ Hc c ω := fun c c' ω hcc =>
    Set.indicator_le_indicator_of_subset (fun _ h => hcc.trans h) (fun _ => sq_nonneg _) ω
  have hHci : ∀ c, Integrable (Hc c) (pathMeasure P π) := fun c => hHi.indicator
    (measurableSet_le measurable_const hHm)
  set h : ℝ → X → ℝ := fun c x => ∫ ω, Hc c ω ∂pathKernel P x with hh
  -- the good set: `H` is `P_x`-integrable
  have hgood : ∀ᵐ x ∂π, Integrable H (pathKernel P x) := by
    have h2 : Integrable H (pathKernel P ∘ₘ π) := by rw [← pathMeasure_eq_comp]; exact hHi
    exact ((Measure.integrable_comp_iff h2.1).1 h2).1
  have hgood' : ∀ k, ∀ᵐ ω ∂pathMeasure P π, Integrable H (pathKernel P (ω k)) := fun k => by
    have : ∀ᵐ x ∂(pathMeasure P π).map (fun ω => ω k), Integrable H (pathKernel P x) := by
      rw [hπ.map_coord k]; exact hgood
    exact ae_of_ae_map (measurable_pi_apply k).aemeasurable this
  -- the Markov property
  have hshiftH : ∀ (c : ℝ) (k : ℕ), (fun ω : ℕ → X =>
      {ω | c ≤ (gh (ω (k + 1)) - kernelInt P gh (ω k)) ^ 2}.indicator
        (fun ω => (gh (ω (k + 1)) - kernelInt P gh (ω k)) ^ 2) ω) =
      fun ω => Hc c (shift k ω) := fun c k => by
    ext ω
    simp only [hHc, hHdef, Set.indicator_apply, mem_ofPred_eq, shift, add_zero]
  have hmk : ∀ (c : ℝ) (k : ℕ), (pathMeasure P π)[fun ω => Hc c (shift k ω) | natFilt k]
      =ᵐ[pathMeasure P π] fun ω => h c (ω k) := fun c k => by
    have hint : Integrable (fun ω => Hc c (shift k ω)) (pathMeasure P π) := by
      have h1 := hHci c
      rw [← (measurePreserving_shift hπ k).map_eq] at h1
      exact h1.comp_measurable (measurable_shift k)
    exact markov_property P π k (hHcm c) hint
  -- the LLN at a fixed level `b`
  have hlln : ∀ b : ℕ, ∀ᵐ ω ∂pathMeasure P π, Tendsto (fun n : ℕ =>
      (∑ k ∈ Finset.range n, h b (ω k)) / n) atTop (𝓝 (∫ ω, Hc b ω ∂pathMeasure P π)) := by
    intro b
    have hhm : Measurable (h b) :=
      (StronglyMeasurable.integral_kernel (hHcm b).stronglyMeasurable).measurable
    have hhi : Integrable (h b) π := by
      have h2 : Integrable (Hc b) (pathKernel P ∘ₘ π) := by
        rw [← pathMeasure_eq_comp]; exact hHci b
      refine (((Measure.integrable_comp_iff h2.1).1 h2).2).congr
        (Eventually.of_forall fun x => ?_)
      simp only [hh]
      congr 1
      ext ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hHc0 _ ω)]
    have hFi : Integrable (fun ω : ℕ → X => h b (ω 0)) (pathMeasure P π) :=
      integrable_coord_of_invariant P hπ hhi 0
    have hFint : ∫ ω, h b (ω 0) ∂pathMeasure P π = ∫ ω, Hc b ω ∂pathMeasure P π := by
      rw [show ∫ ω, h b (ω 0) ∂pathMeasure P π = ∫ x, h b x ∂π by
        rw [show ∫ x, h b x ∂π = ∫ x, h b x ∂((pathMeasure P π).map fun ω => ω 0) by
          rw [hπ.map_coord 0], integral_map (measurable_pi_apply 0).aemeasurable
          hhm.aestronglyMeasurable]]
      rw [pathMeasure_eq_comp, integral_measure_comp_real]
      rw [← pathMeasure_eq_comp]; exact hHci b
    have hb := ae_tendsto_birkhoffAverage_of_ergodic (measurePreserving_shift hπ 1)
      (hhm.comp (measurable_pi_apply 0)) hFi (ergodic_pathMeasure hH π)
    rw [show (h (b : ℝ) ∘ fun f : ℕ → X => f 0) = fun ω => h b (ω 0) from rfl, hFint] at hb
    filter_upwards [hb] with ω hω
    refine hω.congr fun n => ?_
    rw [birkhoffAverage_shift_eq]
    congr 1
  -- `E_π[H 1{H ≥ b}] → 0`
  have htail : Tendsto (fun b : ℕ => ∫ ω, Hc b ω ∂pathMeasure P π) atTop (𝓝 0) := by
    have h1 := tendsto_integral_of_dominated_convergence (μ := pathMeasure P π)
      (F := fun b : ℕ => Hc b) (f := fun _ => (0 : ℝ)) H
      (fun b => (hHcm b).aestronglyMeasurable) hHi
      (fun b => Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hHc0 _ ω)]; exact hHcle _ ω)
      (Eventually.of_forall fun ω => by
        refine tendsto_const_nhds.congr' ?_
        obtain ⟨N, hN⟩ := exists_nat_gt (H ω)
        filter_upwards [eventually_ge_atTop N] with b hb
        have : H ω < b := hN.trans_le (by exact_mod_cast hb)
        simp only [hHc]
        rw [Set.indicator_of_notMem (show ω ∉ {ω | (b : ℝ) ≤ H ω} by
          simp only [mem_ofPred_eq, not_le]; exact this)])
    simpa using h1
  -- combine
  filter_upwards [ae_all_iff.2 hlln, ae_all_iff.2 fun n : ℕ => ae_all_iff.2 fun k : ℕ =>
    hmk (ε * n) k, ae_all_iff.2 hgood'] with ω hω hmω hgω
  have hcongr : ∀ n : ℕ, (∑ k ∈ Finset.range n,
      (pathMeasure P π)[fun ω => {ω | ε * n ≤ (gh (ω (k + 1)) - kernelInt P gh (ω k)) ^ 2}.indicator
        (fun ω => (gh (ω (k + 1)) - kernelInt P gh (ω k)) ^ 2) ω | natFilt k] ω) / n =
      (∑ k ∈ Finset.range n, h (ε * n) (ω k)) / n := fun n => by
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hshiftH (ε * n) k, hmω n k]
  simp_rw [hcongr]
  have hnn : ∀ (c : ℝ) k, 0 ≤ h c (ω k) := fun c k => integral_nonneg fun ω' => hHc0 c ω'
  have hmono : ∀ (c c' : ℝ) k, c ≤ c' → h c' (ω k) ≤ h c (ω k) := fun c c' k hcc =>
    integral_mono ((hgω k).mono' (hHcm c').aestronglyMeasurable (Eventually.of_forall fun ω' => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hHc0 _ ω')]; exact hHcle _ ω'))
      ((hgω k).mono' (hHcm c).aestronglyMeasurable (Eventually.of_forall fun ω' => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hHc0 _ ω')]; exact hHcle _ ω'))
      fun ω' => hHcmono c c' ω' hcc
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨b, hb⟩ := (htail.eventually (gt_mem_nhds (show (0 : ℝ) < δ / 2 by positivity))).exists
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.1 (hω b)) (δ / 2) (by positivity)
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt ((b : ℝ) / ε)
  refine ⟨max N₁ (N₂ + 1), fun n hn => ?_⟩
  have h1 := hN₁ n (le_of_max_le_left hn)
  rw [Real.dist_eq] at h1 ⊢
  have hbn : (b : ℝ) ≤ ε * n := by
    have : (N₂ : ℝ) + 1 ≤ n := by exact_mod_cast le_of_max_le_right hn
    rw [div_lt_iff₀ hε] at hN₂
    nlinarith
  have hle : (∑ k ∈ Finset.range n, h (ε * n) (ω k)) / n ≤
      (∑ k ∈ Finset.range n, h b (ω k)) / n :=
    div_le_div_of_nonneg_right (Finset.sum_le_sum fun k _ => hmono b (ε * n) k hbn)
      (Nat.cast_nonneg n)
  have h0 : 0 ≤ (∑ k ∈ Finset.range n, h (ε * n) (ω k)) / n :=
    div_nonneg (Finset.sum_nonneg fun k _ => hnn _ k) (Nat.cast_nonneg n)
  rw [sub_zero, abs_of_nonneg h0]
  have h2 := (abs_lt.1 h1).2
  linarith

/-! ### Theorem 17.4.4 -/

/-- The interpolated partial-sum process (17.45), MT p. 447:
`sₙ(t) = S_{⌊nt⌋}(g) + (nt − ⌊nt⌋)(S_{⌊nt⌋+1}(g) − S_{⌊nt⌋}(g))`, `Sₙ(g) = Σ_{k=1}^n g(Φₖ)`. -/
noncomputable def sumPath (g : X → ℝ) (n : ℕ) (ω : ℕ → X) : C(unitInterval, ℝ) :=
  polygonal n fun k => pathSum g k ω

/-- `sumPath` is measurable in the path. -/
theorem measurable_sumPath [MeasurableSpace C(unitInterval, ℝ)] [BorelSpace C(unitInterval, ℝ)]
    {g : X → ℝ} (hg : Measurable g) (n : ℕ) : Measurable (sumPath g n) :=
  measurable_polygonal_comp (fun k => measurable_pathSum hg k) n

/-- **The sup-norm comparison (17.48)** (MT p. 447): the interpolated sums `sₙ` of `g − c` and the
interpolated martingale `mₙ` (17.47) of `Mₖ(g)` differ by at most
`|Pĝ(Φ₀)| + max_{1≤k≤n} |Pĝ(Φₖ)|` in sup norm. -/
theorem norm_sumPath_sub_polygonal_poissonMart_le {P : Kernel X X} {g gh : X → ℝ} {c : ℝ}
    (hsol : IsPoissonSolution P g gh c) (n : ℕ) (ω : ℕ → X) :
    ‖sumPath (fun x => g x - c) n ω - polygonal n (fun k => poissonMart P gh k ω)‖ ≤
      |kernelInt P gh (ω 0)| + ⨆ k : Fin n, |kernelInt P gh (ω (k + 1))| := by
  rw [sumPath, ← polygonal_sub]
  refine norm_polygonal_le fun k hk => ?_
  simp only [Pi.sub_apply]
  rw [pathSum_eq_poissonMart hsol k ω]
  have hsup0 : 0 ≤ ⨆ k : Fin n, |kernelInt P gh (ω (k + 1))| :=
    Real.iSup_nonneg fun _ => abs_nonneg _
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp only [add_sub_cancel_right, sub_self, abs_zero]
    positivity
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hbdd : BddAbove (Set.range fun k : Fin n => |kernelInt P gh (ω (k + 1))|) :=
    (Set.finite_range _).bddAbove
  have h1 : |kernelInt P gh (ω (j + 1))| ≤ ⨆ k : Fin n, |kernelInt P gh (ω (k + 1))| :=
    le_ciSup (f := fun k : Fin n => |kernelInt P gh (ω (k + 1))|) hbdd ⟨j, by omega⟩
  calc |poissonMart P gh (j + 1) ω + kernelInt P gh (ω 0) - kernelInt P gh (ω (j + 1)) -
        poissonMart P gh (j + 1) ω| = |kernelInt P gh (ω 0) - kernelInt P gh (ω (j + 1))| := by
          ring_nf
    _ ≤ |kernelInt P gh (ω 0)| + |kernelInt P gh (ω (j + 1))| := abs_sub _ _
    _ ≤ _ := by linarith

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 17.4.4 for the stationary chain** (`Φ₀ ∼ π`): for a Harris chain with invariant
probability `π` and a solution `ĝ ∈ L²(π)` of Poisson's equation `ĝ − Pĝ = g − c` with
`γ_g² = π(ĝ² − (Pĝ)²) > 0`, `(nγ_g²)^{−1/2} sₙ ⇒ B` under `P_π`. -/
theorem theorem_17_4_4_stationary [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hH : IsHarris P ψ) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {g gh : X → ℝ} {c : ℝ} (hsol : IsPoissonSolution P g gh c) (hghm : Measurable gh)
    (hgm : Measurable g) (hgh2 : MemLp gh 2 π)
    (hγ : 0 < ∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π) :
    haveI := isProbabilityMeasure_wienerMeasure
    haveI := isProbabilityMeasure_pathMeasure P π
    TendstoInDistribution (fun (n : ℕ) ω =>
      (√((n : ℝ) * ∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π))⁻¹ •
      sumPath (fun x => g x - c) n ω) atTop id (fun _ => pathMeasure P π) wienerMeasure := by
  have := isProbabilityMeasure_wienerMeasure
  have := isProbabilityMeasure_pathMeasure P π
  set γ2 := ∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π with hγ2
  have hPm := measurable_kernelInt P hghm
  have hPgh2 := memLp_kernelInt_of_memLp hπ hghm (fun x => (hsol x).1) hgh2
  obtain ⟨hD, hL2, h0, -⟩ := poisson_increment_props P hπ hghm hgh2 hPgh2
  set D : ℕ → (ℕ → X) → ℝ := fun k ω => gh (ω (k + 1)) - kernelInt P gh (ω k) with hDdef
  -- (D.8) and (D.9) hold by the LLN (MT p. 448)
  have hcv := condVar_poisson_tendsto hH hπ hghm (fun x => (hsol x).1) hgh2
  have hM := theorem_D_6_4 hD hL2 h0 hγ hcv fun ε hε =>
    lindeberg_poisson hH hπ hghm (fun x => (hsol x).1) hgh2 hε
  -- the comparison (17.48)
  have hYm : ∀ n : ℕ, Measurable fun ω => (√((n : ℝ) * γ2))⁻¹ •
      sumPath (fun x => g x - c) n ω := fun n =>
    (measurable_sumPath (g := fun x => g x - c) (hgm.sub measurable_const) n).const_smul
      ((√((n : ℝ) * γ2))⁻¹)
  refine tendstoInDistribution_of_ae_norm_sub_tendsto hM ?_ fun n => (hYm n).aemeasurable
  filter_upwards [ae_eventually_abs_le_sqrt hH hπ hPm hPgh2 π] with ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hsγ : 0 < √γ2 := Real.sqrt_pos.2 hγ
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hω (ε * √γ2 / 4) (by positivity)).and
    (eventually_ge_atTop 1))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hn1, hn2⟩ := hN n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn2
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  set a := (√((n : ℝ) * γ2))⁻¹ with ha
  have ha' : a = (√(n : ℝ))⁻¹ * (√γ2)⁻¹ := by rw [ha, Real.sqrt_mul hn0.le, mul_inv]
  have hrw : a • sumPath (fun x => g x - c) n ω - polygonal n (fun k => (√(γ2 * n))⁻¹ *
      ∑ i ∈ Finset.range k, D i ω) = polygonal n (fun k => a * (kernelInt P gh (ω 0) -
        kernelInt P gh (ω k))) := by
    rw [sumPath, ← polygonal_const_mul, ← polygonal_sub]
    congr 1
    funext k
    simp only [Pi.sub_apply]
    rw [pathSum_eq_poissonMart hsol k ω, poissonMart, mul_comm γ2]
    ring
  rw [hrw]
  have hb : ∀ k ≤ n, |a * (kernelInt P gh (ω 0) - kernelInt P gh (ω k))| ≤ ε / 2 := by
    intro k hk
    have h1 := hn1 0 (by omega)
    have h2 := hn1 k (by omega)
    rw [abs_mul, abs_of_pos (by positivity : 0 < a), ha']
    calc (√(n : ℝ))⁻¹ * (√γ2)⁻¹ * |kernelInt P gh (ω 0) - kernelInt P gh (ω k)|
        ≤ (√(n : ℝ))⁻¹ * (√γ2)⁻¹ * (ε * √γ2 / 4 * √(n : ℝ) + ε * √γ2 / 4 * √(n : ℝ)) :=
          mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add h1 h2)) (by positivity)
      _ = ε / 2 := by field_simp; ring
  exact (norm_polygonal_le hb).trans_lt (by linarith)

omit [MeasurableSpace X] in
/-- `|Sⱼ(g)| ≤ j ε √n` along the path shifted by `k` when all the `|g(Φᵢ)|`, `i ≤ k + j`, are at
most `ε √n`. -/
theorem abs_pathSum_shift_le {g : X → ℝ} {ω : ℕ → X} {b : ℝ} (j k : ℕ)
    (hb : ∀ i ≤ k + j, |g (ω i)| ≤ b) : |pathSum g j (shift k ω)| ≤ j * b := by
  rw [pathSum]
  calc |∑ i ∈ Finset.range j, g (shift k ω (i + 1))|
      ≤ ∑ i ∈ Finset.range j, |g (shift k ω (i + 1))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range j, b := Finset.sum_le_sum fun i hi => by
        simp only [shift]
        exact hb _ (by have := Finset.mem_range.1 hi; omega)
    _ = j * b := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 17.4.4** (MT p. 447), the functional CLT: let the chain be positive Harris with
invariant probability `π`, and let `ĝ` solve Poisson's equation `ĝ − Pĝ = g − c` with
`π(ĝ²) < ∞` and `γ_g² = π(ĝ² − (Pĝ)²) > 0` (17.46). Then for every initial distribution `μ`,
`(nγ_g²)^{−1/2} sₙ ⇒ B` (standard Brownian motion, `wienerMeasure`) under `P_μ`, where `sₙ` is the
interpolated partial-sum process (17.45) of `g − c`. -/
theorem theorem_17_4_4 [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hph : IsPositiveHarris P ψ) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {g gh : X → ℝ} {c : ℝ} (hsol : IsPoissonSolution P g gh c) (hghm : Measurable gh)
    (hgm : Measurable g) (hgh2 : MemLp gh 2 π)
    (hγ : 0 < ∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π) (μ : Measure X)
    [IsProbabilityMeasure μ] :
    haveI := isProbabilityMeasure_wienerMeasure
    haveI := isProbabilityMeasure_pathMeasure P μ
    TendstoInDistribution (fun (n : ℕ) ω =>
      (√((n : ℝ) * ∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π))⁻¹ •
      sumPath (fun x => g x - c) n ω) atTop id (fun _ => pathMeasure P μ) wienerMeasure := by
  have := isProbabilityMeasure_wienerMeasure
  have := isProbabilityMeasure_pathMeasure P μ
  set γ2 := ∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π with hγ2
  have hPgh2 := memLp_kernelInt_of_memLp hπ hghm (fun x => (hsol x).1) hgh2
  have hgbm : Measurable fun x => g x - c := hgm.sub measurable_const
  have hgb2 : MemLp (fun x => g x - c) 2 π := by
    have e : (fun x => g x - c) = fun x => gh x - kernelInt P gh x :=
      funext fun x => ((hsol x).2).symm
    rw [e]; exact hgh2.sub hPgh2
  have hYm : ∀ n : ℕ, Measurable fun ω => (√((n : ℝ) * γ2))⁻¹ •
      sumPath (fun x => g x - c) n ω := fun n =>
    (measurable_sumPath (g := fun x => g x - c) hgbm n).const_smul ((√((n : ℝ) * γ2))⁻¹)
  refine tendstoInDistribution_pathMeasure_of_stationary hph hπ hYm
    (theorem_17_4_4_stationary hph.1 hπ hsol hghm hgm hgh2 hγ) μ fun j => ?_
  filter_upwards [ae_eventually_abs_le_sqrt hph.1 hπ hgbm hgb2 μ] with ω hω
  rw [Metric.tendsto_atTop]
  intro η hη
  have hsγ : 0 < √γ2 := Real.sqrt_pos.2 hγ
  set ε := η * √γ2 / (4 * (j + 1)) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 (((hω ε hε0).and (eventually_ge_atTop 1)).and
    (eventually_ge_atTop j))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨⟨hn1, hn2⟩, hnj⟩ := hN n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn2
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
  rw [Real.dist_eq, sub_zero, dist_eq_norm, abs_of_nonneg (norm_nonneg _)]
  set a := (√((n : ℝ) * γ2))⁻¹ with ha
  have ha' : a = (√(n : ℝ))⁻¹ * (√γ2)⁻¹ := by rw [ha, Real.sqrt_mul hn0.le, mul_inv]
  have hrw : a • sumPath (fun x => g x - c) n (shift j ω) - a • sumPath (fun x => g x - c) n ω =
      polygonal n (fun k => a * (pathSum (fun x => g x - c) j (shift k ω) -
        pathSum (fun x => g x - c) j ω)) := by
    rw [sumPath, sumPath, ← polygonal_const_mul, ← polygonal_const_mul, ← polygonal_sub]
    congr 1
    funext k
    simp only [Pi.sub_apply]
    have e1 := pathSum_split (fun x => g x - c) (m := j) (n := j + k) (by omega) ω
    have e2 := pathSum_split (fun x => g x - c) (m := k) (n := k + j) (by omega) ω
    rw [Nat.add_sub_cancel_left] at e1 e2
    rw [add_comm k j] at e2
    rw [← mul_sub]
    congr 1
    linarith
  rw [hrw]
  have hb : ∀ k ≤ n, |a * (pathSum (fun x => g x - c) j (shift k ω) -
      pathSum (fun x => g x - c) j ω)| ≤ η / 2 := by
    intro k hk
    have h1 := abs_pathSum_shift_le (g := fun x => g x - c) (ω := ω) j k
      (fun i hi => hn1 i (by omega))
    have h2 : |pathSum (fun x => g x - c) j ω| ≤ j * (ε * √(n : ℝ)) := by
      have := abs_pathSum_shift_le (g := fun x => g x - c) (ω := ω) j 0
        (fun i hi => hn1 i (by omega))
      simpa [shift] using this
    rw [abs_mul, abs_of_pos (by positivity : 0 < a), ha']
    have hj : (j : ℝ) / (j + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    calc (√(n : ℝ))⁻¹ * (√γ2)⁻¹ * |pathSum (fun x => g x - c) j (shift k ω) -
          pathSum (fun x => g x - c) j ω|
        ≤ (√(n : ℝ))⁻¹ * (√γ2)⁻¹ * (j * (ε * √(n : ℝ)) + j * (ε * √(n : ℝ))) :=
          mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add h1 h2)) (by positivity)
      _ = η / 2 * ((j : ℝ) / (j + 1)) := by rw [hε]; field_simp; ring
      _ ≤ η / 2 := mul_le_of_le_one_right (by positivity) hj
  exact (norm_polygonal_le hb).trans_lt (by linarith)

variable [MeasurableSpace.CountablyGenerated X] in
/-- Theorem 17.4.4 from an initial state `x`: `(nγ_g²)^{−1/2} sₙ ⇒ B` under `P_x`. -/
theorem theorem_17_4_4_initial_state [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hph : IsPositiveHarris P ψ) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {g gh : X → ℝ} {c : ℝ} (hsol : IsPoissonSolution P g gh c) (hghm : Measurable gh)
    (hgm : Measurable g) (hgh2 : MemLp gh 2 π)
    (hγ : 0 < ∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π) (x : X) :
    haveI := isProbabilityMeasure_wienerMeasure
    haveI := isMarkovKernel_pathKernel P
    TendstoInDistribution (fun (n : ℕ) ω =>
      (√((n : ℝ) * ∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π))⁻¹ •
      sumPath (fun x => g x - c) n ω) atTop id (fun _ => pathKernel P x) wienerMeasure := by
  have := isProbabilityMeasure_wienerMeasure
  have := isMarkovKernel_pathKernel P
  have h := theorem_17_4_4 hph hπ hsol hghm hgm hgh2 hγ (Measure.dirac x)
  convert h using 2
  rw [pathMeasure_dirac]

/-! ### Theorem 17.4.5: the functionals `u(1)` and `max u` -/

/-- The supremum of a polygonal path is the largest of its nodes:
`sup_t polygonal n s (t) = max_{k ≤ n} s k`. -/
theorem supPath_polygonal (n : ℕ) (s : ℕ → ℝ) :
    supPath (polygonal n s) = (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one s := by
  refine le_antisymm ((supPath_le_iff _).2 fun t => ?_) (Finset.sup'_le _ _ fun k hk => ?_)
  · have hfl := floor_natCast_mul_le n t
    have hmem : ∀ k ≤ n, s k ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one s :=
      fun k hk => Finset.le_sup' s (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
    by_cases hlt : (⌊(n : ℝ) * t⌋₊ : ℝ) < (n : ℝ) * t
    · exact (polygonal_mem_between n s t).2.trans
        (max_le (hmem _ hfl) (hmem _ (floor_add_one_le_of_lt n t hlt)))
    · have heq : (n : ℝ) * t = ⌊(n : ℝ) * t⌋₊ :=
        le_antisymm (not_lt.1 hlt) (Nat.floor_le (natCast_mul_mem_Icc n t).1)
      rw [polygonal_apply_of_mul_eq s t heq]
      exact hmem _ hfl
  · have hk' : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    rw [← polygonal_grid s hk']
    exact le_supPath _ _

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 17.4.5**, the functional `u(1)` (MT p. 448): under the conditions of Theorem 17.4.4,
for every initial distribution, `(nγ_g²)^{−1/2} Sₙ(g − c) ⇒ B(1)`, a standard normal variable. -/
theorem theorem_17_4_5_endpoint [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hph : IsPositiveHarris P ψ) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {g gh : X → ℝ} {c : ℝ} (hsol : IsPoissonSolution P g gh c) (hghm : Measurable gh)
    (hgm : Measurable g) (hgh2 : MemLp gh 2 π)
    (hγ : 0 < ∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π) (μ : Measure X)
    [IsProbabilityMeasure μ] :
    haveI := isProbabilityMeasure_wienerMeasure
    haveI := isProbabilityMeasure_pathMeasure P μ
    TendstoInDistribution (fun (n : ℕ) ω =>
      (√((n : ℝ) * ∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π))⁻¹ *
      pathSum (fun x => g x - c) n ω) atTop (fun f : C(unitInterval, ℝ) => f 1)
      (fun _ => pathMeasure P μ) wienerMeasure := by
  have := isProbabilityMeasure_wienerMeasure
  have := isProbabilityMeasure_pathMeasure P μ
  have h := tendstoInDistribution_eval_one (theorem_17_4_4 hph hπ hsol hghm hgm hgh2 hγ μ)
  have hfun : (fun (n : ℕ) (ω : ℕ → X) =>
      ((√((n : ℝ) * ∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π))⁻¹ •
        sumPath (fun x => g x - c) n ω) 1) = fun (n : ℕ) ω =>
      (√((n : ℝ) * ∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π))⁻¹ *
        pathSum (fun x => g x - c) n ω := by
    funext n ω
    rw [ContinuousMap.smul_apply, sumPath, polygonal_one_point, smul_eq_mul]
  rw [hfun] at h
  exact h

variable [MeasurableSpace.CountablyGenerated X] in
/-- **The CLT of Theorem 17.4.5** (MT p. 448) for every positive Harris chain and every initial
distribution, from the FCLT and the functional `u(1)`: `n^{−1/2} Sₙ(g − c) ⇒ N(0, γ_g²)`. -/
theorem theorem_17_4_5_clt_harris [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hph : IsPositiveHarris P ψ) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {g gh : X → ℝ} {c : ℝ} (hsol : IsPoissonSolution P g gh c) (hghm : Measurable gh)
    (hgm : Measurable g) (hgh2 : MemLp gh 2 π)
    (hγ : 0 < ∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π) (μ : Measure X)
    [IsProbabilityMeasure μ] {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 (∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π).toNNReal) P') :
    haveI := isProbabilityMeasure_pathMeasure P μ
    TendstoInDistribution (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * pathSum (fun x => g x - c) n ω)
      atTop Z (fun _ => pathMeasure P μ) P' := by
  have := isProbabilityMeasure_wienerMeasure
  have := isProbabilityMeasure_pathMeasure P μ
  set γ2 := ∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π with hγ2
  have hsγ : 0 < √γ2 := Real.sqrt_pos.2 hγ
  have h1 := (theorem_17_4_5_endpoint hph hπ hsol hghm hgm hgh2 hγ μ).continuous_comp
    (g := fun y : ℝ => √γ2 * y) (continuous_const.mul continuous_id)
  have hfun : (fun (n : ℕ) (ω : ℕ → X) => √γ2 * ((√((n : ℝ) * γ2))⁻¹ *
      pathSum (fun x => g x - c) n ω)) =
      fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * pathSum (fun x => g x - c) n ω := by
    funext n ω
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Real.sqrt_mul hn0.le, mul_inv]
    field_simp
  simp only [Function.comp_def] at h1
  rw [hfun] at h1
  refine tendstoInDistribution_congr_limit_law h1 hZ.aemeasurable ?_
  have hm : Measurable fun f : C(unitInterval, ℝ) => f 1 := continuous_eval_one_C01.measurable
  have e : (fun x : C(unitInterval, ℝ) => √γ2 * x 1) =
      (fun y : ℝ => √γ2 * y) ∘ (fun f : C(unitInterval, ℝ) => f 1) := rfl
  have hcm : Measurable fun y : ℝ => √γ2 * y := measurable_id.const_mul _
  rw [hZ.map_eq, e, ← Measure.map_map hcm hm,
    wienerMeasure_map_eval_one, gaussianReal_map_const_mul, mul_zero]
  congr 1
  ext
  rw [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, mul_one, Real.sq_sqrt hγ.le,
    Real.coe_toNNReal _ hγ.le]

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 17.4.5**, the functional `max u` (MT p. 448): under the conditions of Theorem 17.4.4,
for every initial distribution, `(nγ_g²)^{−1/2} max_{1≤k≤n} Sₖ(g − c) ⇒ max_{0≤t≤1} B(t)`. -/
theorem theorem_17_4_5_max [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hph : IsPositiveHarris P ψ) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {g gh : X → ℝ} {c : ℝ} (hsol : IsPoissonSolution P g gh c) (hghm : Measurable gh)
    (hgm : Measurable g) (hgh2 : MemLp gh 2 π)
    (hγ : 0 < ∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π) (μ : Measure X)
    [IsProbabilityMeasure μ] :
    haveI := isProbabilityMeasure_wienerMeasure
    haveI := isProbabilityMeasure_pathMeasure P μ
    TendstoInDistribution (fun (n : ℕ) ω =>
      (√((n : ℝ) * ∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π))⁻¹ *
      ⨆ k : Fin n, pathSum (fun x => g x - c) (k + 1) ω) atTop supPath
      (fun _ => pathMeasure P μ) wienerMeasure := by
  have := isProbabilityMeasure_wienerMeasure
  have := isProbabilityMeasure_pathMeasure P μ
  set γ2 := ∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π with hγ2
  have hgbm : Measurable fun x => g x - c := hgm.sub measurable_const
  have h := tendstoInDistribution_supPath (theorem_17_4_4 hph hπ hsol hghm hgm hgh2 hγ μ)
  set a : ℕ → ℝ := fun n => (√((n : ℝ) * γ2))⁻¹ with ha
  have ha0 : ∀ n, 0 ≤ a n := fun n => inv_nonneg.2 (Real.sqrt_nonneg _)
  set T : ℕ → (ℕ → X) → ℕ → ℝ := fun n ω k => a n * pathSum (fun x => g x - c) k ω with hT
  have hsup : ∀ n ω, supPath (a n • sumPath (fun x => g x - c) n ω) =
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (T n ω) := fun n ω => by
    rw [sumPath, ← polygonal_const_mul, supPath_polygonal]
  have hYm : ∀ n : ℕ, Measurable fun ω => a n * ⨆ k : Fin n,
      pathSum (fun x => g x - c) (k + 1) ω := fun n =>
    measurable_const.mul (Measurable.iSup fun k => measurable_pathSum hgbm _)
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ h ?_ fun n => (hYm n).aemeasurable
  refine tendstoInMeasure_of_tendsto_ae (fun n => ((hYm n).sub ((continuous_supPath.measurable).comp
    ((measurable_sumPath hgbm n).const_smul (a n)))).aestronglyMeasurable) ?_
  refine Eventually.of_forall fun ω => ?_
  simp only [Pi.sub_apply, Pi.zero_apply]
  -- `|a max_{1≤k≤n} Sₖ − max_{0≤k≤n} a Sₖ| ≤ a |S₁|`
  have hbound : ∀ n : ℕ, 1 ≤ n → |a n * (⨆ k : Fin n, pathSum (fun x => g x - c) (k + 1) ω) -
      supPath (a n • sumPath (fun x => g x - c) n ω)| ≤ a n * |g (ω 1) - c| := by
    intro n hn
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    rw [hsup, Real.mul_iSup_of_nonneg (ha0 n)]
    set M := ⨆ k : Fin n, a n * pathSum (fun x => g x - c) (k + 1) ω with hM
    have hbdd : BddAbove (Set.range fun k : Fin n => a n * pathSum (fun x => g x - c) (k + 1) ω) :=
      (Set.finite_range _).bddAbove
    have hT1 : T n ω 1 ≤ M := le_ciSup (f := fun k : Fin n =>
      a n * pathSum (fun x => g x - c) (k + 1) ω) hbdd ⟨0, hn⟩
    have hle1 : M ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (T n ω) :=
      ciSup_le fun k => Finset.le_sup' (T n ω) (Finset.mem_range.2 (by omega))
    have hle2 : (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (T n ω) ≤ max 0 M := by
      refine Finset.sup'_le _ _ fun k hk => ?_
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simp [hT, pathSum]
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        exact (le_ciSup (f := fun k : Fin n => a n * pathSum (fun x => g x - c) (k + 1) ω) hbdd
          ⟨j, by have := Finset.mem_range.1 hk; omega⟩).trans (le_max_right _ _)
    have hT1' : T n ω 1 = a n * (g (ω 1) - c) := by simp [hT, pathSum]
    rw [hT1'] at hT1
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    have h3 : -(a n * (g (ω 1) - c)) ≤ a n * |g (ω 1) - c| := by
      rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_le_abs _) (ha0 n)
    rcases le_total 0 M with hM0 | hM0
    · rw [max_eq_right hM0] at hle2; nlinarith [abs_nonneg (g (ω 1) - c), ha0 n]
    · rw [max_eq_left hM0] at hle2; linarith
  have ha_lim : Tendsto a atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => √((n : ℝ) * γ2)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hγ)
    exact h1.inv_tendsto_atTop
  have hlim : Tendsto (fun n => a n * |g (ω 1) - c|) atTop (𝓝 0) := by
    simpa using ha_lim.mul_const |g (ω 1) - c|
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs]
  exact hbound n hn

end MeynTweedie.LimitTheorems
