/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.CLTMoment
import GeneralizedDrift.GeometricModels

/-!
# Applications of the CLT (MT §17.6)

Copied for Chapter 19 from the Chapter 17 project
(`LimitTheorems/LimitApplications.lean`), with the namespace changed to
`MeynTweedie.GeneralizedDrift` and the imports to `GeneralizedDrift.*`.

Meyn and Tweedie, Proposition 17.6.1 and Theorem 17.6.2, pp. 454–456.

**`V`-uniform chains are positive Harris.**
* `isPositiveHarris_of_driftV4`: a `ψ`-irreducible chain satisfying (V4) for a petite set and a
  finite `V ≥ 1` is positive Harris (Theorem 9.1.8 with the petite sublevel sets of
  Lemma 15.2.2, and positivity through (V3)).

**Random walk on a half line** (§17.6.1). `halfLineWalkKernel Γ` is `Φₙ₊₁ = [Φₙ + Wₙ₊₁]⁺`.
* `halfLine_cltMoment`: with `E[W] < 0` and `E|W|⁵ < ∞`, the CLT moment condition holds with
  `f(x) = x + 1` and `V(x) = c⁻¹x²` (from (14.29)), and `π(V²) < ∞` (Proposition 14.4.1).
* **Proposition 17.6.1** (`proposition_17_6_1`, p. 454): the walk is positive Harris and
  aperiodic; for its invariant probability `π`, the CLT holds for `{Φₖ}` from every initial state
  (`proposition_17_6_1_clt`), with `γ² = lim (1/n) E_π[Sₙ(Φ − π(Φ))²]` given by the absolutely
  convergent autocovariance series (17.3) (`proposition_17_6_1_variance`).

**The linear model** (§17.6.2), for `n = p = 1`: `ar1Kernel Γ α` is `Xₖ₊₁ = αXₖ + Wₖ₊₁`.
* `ar1_driftV4_sq`: (V4) for `V(x) = x² + 1` when `|α| < 1`, `E W² < ∞` and compact sets are
  petite; `ar1_integral_id`, `ar1_integral_sq`, `ar1_integrable_pow`, `ar1_integral_pow`
  (`∫ y Pⁿ(x, dy) = αⁿx`), `ar1_stationary_moments` (`π(x) = 0`, `π(x²) = σ²/(1 − α²)`).
* **Theorem 17.6.2** (`theorem_17_6_2`, p. 456): the model is `V`-uniformly ergodic and positive
  Harris, and `γ² = σ²/(1 − α)²`, which is `(I − F)⁻¹ G Σ_W Gᵀ (I − Fᵀ)⁻¹` for `F = α`, `G = 1`,
  computed from the autocovariances `E_π[X₀Xₖ] = αᵏ σ²/(1 − α²)`; `theorem_17_6_2_clt`:
  `n^{−1/2} Σ_{k=1}^n Xₖ ⇒ N(0, σ²/(1 − α)²)` under every `P_x`.

**Hypotheses and omissions.** For the linear model `ψ`-irreducibility, aperiodicity and the
petiteness of compact sets are assumed, as in `ar1_geometricErgodic`: the book obtains them from
(LSS4), (LCM3) through the T-chain property (Proposition 6.3.5). The vector model
`Xₖ₊₁ = FXₖ + GWₖ₊₁` on `ℝⁿ` is in `GapsVectorLinear`: (V4) for `V(x) = 1 + xᵀMx` with the
Lyapunov matrix of (12.34) (`lss_driftV4`), the variance formula and the CLT for `c ⬝ Xₖ`
(`theorem_17_6_2_vector`, `theorem_17_6_2_vector_clt`), and the vector-valued CLT mentioned
after the proof, by Cramér–Wold (`theorem_17_6_2_vector_clt_vec`). The LIL for
Proposition 17.6.1 and Theorem 17.6.2 is in `MartingaleLILApplications`.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X]

/-! ### (V4) gives positive Harris recurrence -/

/-- A `ψ`-irreducible chain satisfying (V4) for a petite set `C` and a finite `V ≥ 1` is positive
Harris. -/
theorem isPositiveHarris_of_driftV4 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {V : X → ℝ≥0∞} (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    (hVfin : ∀ x, V x ≠ ∞) {ρ b : ℝ≥0∞} (hρ : ρ < 1) (hb : b ≠ ∞) {C : Set X}
    (hC : IsPetite P C) (h : DriftV4 P V ρ b C) : IsPositiveHarris P ψ := by
  have hU := lemma_15_2_2_ii hV hV1 hρ hb hC h
  have hcoe : ∀ x, ((V x).toNNReal : ℝ≥0∞) = V x := fun x => ENNReal.coe_toNNReal (hVfin x)
  have hH : IsHarris P ψ := by
    refine theorem_9_1_8 hψ hC (V := fun x => (V x).toNNReal) hV.ennreal_toNNReal
      (fun n => ?_) fun x hx => ?_
    · have hset : {x | (V x).toNNReal ≤ (n : ℝ≥0)} = {x | V x ≤ (n : ℝ≥0∞)} := by
        ext x
        simp only [mem_ofPred_eq]
        rw [← ENNReal.coe_le_coe, hcoe, ENNReal.coe_natCast]
      have := hU (n : ℝ≥0∞) (ENNReal.natCast_ne_top n)
      rw [← hset] at this
      exact this
    · rw [drift_nonpos_iff]
      simp_rw [hcoe]
      refine (h x).trans ?_
      rw [indicator_of_notMem hx, add_zero]
      exact mul_le_of_le_one_left' hρ.le
  have hct : (1 - ρ)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hρ).ne'
  obtain ⟨x₀⟩ : Nonempty X := by
    by_contra hX
    rw [not_nonempty_iff] at hX
    exact hψ.1 (Measure.eq_zero_of_isEmpty ψ)
  exact ⟨hH, (isPositive_of_driftV3 hψ hV hV1 hC (hV.const_mul _) (ENNReal.mul_ne_top hct hb)
    (ENNReal.mul_ne_top hct (hVfin x₀)) (h.driftV3_scaled hV hρ)).1⟩

/-! ### Random walk on a half line -/

/-- The CLT moment condition for random walk on a half line: with `E[W] < 0` and `E|W|⁵ < ∞`,
there are `c > 0`, `X₀`, `D < ∞` such that (V3) holds with `V(x) = c⁻¹x²`, `f(x) = x + 1` and the
petite set `[0, X₀]`, and `π(V²) < ∞` for every invariant probability `π`; the walk is
`ψ`-irreducible, aperiodic and positive Harris. -/
theorem halfLine_cltMoment (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => w) Γ) (hβ : ∫ w, w ∂Γ < 0)
    (hint : ∀ l ≤ 5, Integrable (fun w => |w| ^ l) Γ) :
    haveI := isMarkovKernel_halfLineWalkKernel Γ
    ∃ ψ : Measure ℝ≥0, IsMaximalIrreducibility (halfLineWalkKernel Γ) ψ ∧
      IsAperiodic (halfLineWalkKernel Γ) ψ ∧ IsPositiveHarris (halfLineWalkKernel Γ) ψ ∧
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ ∃ X₀ : ℝ≥0, ∃ D : ℝ≥0∞, D ≠ ∞ ∧
        IsPetite (halfLineWalkKernel Γ) (Iic X₀) ∧
        DriftV3 (halfLineWalkKernel Γ) (fun x => c⁻¹ * (x : ℝ≥0∞) ^ 2)
          (fun x => (x : ℝ≥0∞) + 1) (c⁻¹ * D) (Iic X₀) ∧
        ∀ π : Measure ℝ≥0, IsProbabilityMeasure π → IsInvariant (halfLineWalkKernel Γ) π →
          ∫⁻ x, (c⁻¹ * (x : ℝ≥0∞) ^ 2) ^ 2 ∂π ≠ ∞ := by
  have := isMarkovKernel_halfLineWalkKernel Γ
  obtain ⟨ψ, hψ, hap, hph, -, hπ⟩ := proposition_14_4_1 Γ hW hβ 4 hint
  obtain ⟨c, hc0, hct, X₀, D, hD, hdrift⟩ := halfLine_drift_14_29 Γ hW hβ 4 hint
  have hneg := halfLine_neg_pos_of_mean_neg Γ hβ
  refine ⟨ψ, hψ, hap, hph, c, hc0.ne', hct, X₀, D, hD, halfLine_isPetite_Iic Γ hneg X₀,
    fun x => ?_, fun π hπp hinv => ?_⟩
  · have h1 := hdrift 1 (by norm_num) x
    simp only [pow_one] at h1
    rw [show (1 : ℕ) + 1 = 2 from rfl] at h1
    have hm : Measurable fun y : ℝ≥0 => (y : ℝ≥0∞) ^ 2 :=
      measurable_coe_nnreal_ennreal.pow_const 2
    rw [lintegral_const_mul _ hm]
    have key : c⁻¹ * (c * ((x : ℝ≥0∞) + 1)) = (x : ℝ≥0∞) + 1 := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hc0.ne' hct, one_mul]
    have h2 : c⁻¹ * (∫⁻ y, (y : ℝ≥0∞) ^ 2 ∂halfLineWalkKernel Γ x + c * ((x : ℝ≥0∞) + 1)) ≤
        c⁻¹ * ((x : ℝ≥0∞) ^ 2 + (Iic X₀).indicator (fun _ => D) x) := by gcongr
    rw [mul_add, key, mul_add] at h2
    refine h2.trans (le_of_eq ?_)
    congr 1
    by_cases hx : x ∈ Iic X₀
    · rw [indicator_of_mem hx, indicator_of_mem hx]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]
  · obtain ⟨h4, -⟩ := hπ π hπp hinv
    have hm : Measurable fun y : ℝ≥0 => (y : ℝ≥0∞) ^ 4 :=
      measurable_coe_nnreal_ennreal.pow_const 4
    have heq : (fun x : ℝ≥0 => (c⁻¹ * (x : ℝ≥0∞) ^ 2) ^ 2) =
        fun x : ℝ≥0 => c⁻¹ ^ 2 * (x : ℝ≥0∞) ^ 4 := funext fun x => by
      rw [mul_pow, ← pow_mul]
    rw [heq, lintegral_const_mul _ hm]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 hc0.ne')) h4

/-- `|x| ≤ x + 1` on `ℝ≥0`. -/
theorem ofReal_abs_coe_le (x : ℝ≥0) : ENNReal.ofReal |(x : ℝ)| ≤ (x : ℝ≥0∞) + 1 := by
  rw [abs_of_nonneg x.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  exact le_self_add

/-- **Proposition 17.6.1** (MT p. 454), stability: if the increment law has mean `β < 0` and a
finite fifth moment, random walk on a half line is positive Harris and aperiodic, with an
invariant probability with finite fourth moment. -/
theorem proposition_17_6_1 (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => w) Γ) (hβ : ∫ w, w ∂Γ < 0)
    (hint : ∀ l ≤ 5, Integrable (fun w => |w| ^ l) Γ) :
    haveI := isMarkovKernel_halfLineWalkKernel Γ
    ∃ ψ : Measure ℝ≥0, IsPositiveHarris (halfLineWalkKernel Γ) ψ ∧
      IsAperiodic (halfLineWalkKernel Γ) ψ ∧ ∃ π : Measure ℝ≥0, IsProbabilityMeasure π ∧
        IsInvariant (halfLineWalkKernel Γ) π ∧ ∫⁻ x, (x : ℝ≥0∞) ^ 4 ∂π ≠ ∞ := by
  have := isMarkovKernel_halfLineWalkKernel Γ
  obtain ⟨ψ, -, hap, hph, -, hπ⟩ := proposition_14_4_1 Γ hW hβ 4 hint
  obtain ⟨π, hπp, hinv⟩ := hph.2.2
  exact ⟨ψ, hph, hap, π, hπp, hinv, (hπ π hπp hinv).1⟩

/-- **Proposition 17.6.1** (MT pp. 454–455), the asymptotic variance: under the hypotheses of
`proposition_17_6_1`, `γ² = π(ĝ² − (Pĝ)²) ≥ 0` is the limit of `(1/n) E_π[Sₙ(Φ − π(Φ))²]` and the
sum `Σ_{k ∈ ℤ} E_π[Φ̄₀ Φ̄ₖ]` of the autocovariances, which converges absolutely. -/
theorem proposition_17_6_1_variance (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => w) Γ) (hβ : ∫ w, w ∂Γ < 0)
    (hint : ∀ l ≤ 5, Integrable (fun w => |w| ^ l) Γ) {π : Measure ℝ≥0} [IsProbabilityMeasure π]
    (hπ : haveI := isMarkovKernel_halfLineWalkKernel Γ; IsInvariant (halfLineWalkKernel Γ) π) :
    haveI := isMarkovKernel_halfLineWalkKernel Γ
    0 ≤ asymptoticVariance (halfLineWalkKernel Γ) π (fun y : ℝ≥0 => (y : ℝ)) ∧
    Summable (fun k : ℕ => |∫ ω, ((ω 0 : ℝ) - ∫ y, (y : ℝ) ∂π) * ((ω k : ℝ) - ∫ y, (y : ℝ) ∂π)
      ∂pathMeasure (halfLineWalkKernel Γ) π|) ∧
    Tendsto (fun n : ℕ => (∫ ω, pathSum (fun x : ℝ≥0 => (x : ℝ) - ∫ y, (y : ℝ) ∂π) n ω ^ 2
      ∂pathMeasure (halfLineWalkKernel Γ) π) / n) atTop
      (𝓝 (asymptoticVariance (halfLineWalkKernel Γ) π (fun y : ℝ≥0 => (y : ℝ)))) ∧
    asymptoticVariance (halfLineWalkKernel Γ) π (fun y : ℝ≥0 => (y : ℝ)) =
      ∫ x, (poissonSeries (halfLineWalkKernel Γ) π (fun y : ℝ≥0 => (y : ℝ)) x ^ 2 -
        kernelInt (halfLineWalkKernel Γ) (poissonSeries (halfLineWalkKernel Γ) π
          (fun y : ℝ≥0 => (y : ℝ))) x ^ 2) ∂π := by
  have := isMarkovKernel_halfLineWalkKernel Γ
  obtain ⟨ψ, hψ, hap, -, c, hc0, hct, X₀, D, hD, hpet, hdrift, hπV⟩ :=
    halfLine_cltMoment Γ hW hβ hint
  obtain ⟨-, -, h3, h4, h5, h6⟩ := theorem_17_5_3 (f := fun x : ℝ≥0 => (x : ℝ≥0∞) + 1)
    (V := fun x : ℝ≥0 => c⁻¹ * (x : ℝ≥0∞) ^ 2) hψ hap
    (measurable_coe_nnreal_ennreal.add measurable_const) (fun x => le_add_self) hpet
    ((measurable_coe_nnreal_ennreal.pow_const 2).const_mul _)
    (fun x => ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hc0) (ENNReal.pow_ne_top
      ENNReal.coe_ne_top)) (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hc0) hD) hdrift hπ
    (hπV π inferInstance hπ) NNReal.continuous_coe.measurable ofReal_abs_coe_le
  have heq : asymptoticVariance (halfLineWalkKernel Γ) π (fun y : ℝ≥0 => (y : ℝ)) =
      ∫ x, (poissonSeries (halfLineWalkKernel Γ) π (fun y : ℝ≥0 => (y : ℝ)) x ^ 2 -
        kernelInt (halfLineWalkKernel Γ) (poissonSeries (halfLineWalkKernel Γ) π
          (fun y : ℝ≥0 => (y : ℝ))) x ^ 2) ∂π := h6.symm
  rw [heq]
  exact ⟨h3, h5, h4, rfl⟩
/-- **Proposition 17.6.1** (MT p. 454), the CLT: under the hypotheses of `proposition_17_6_1`, for
the invariant probability `π`, `n^{−1/2} Σ_{k=1}^n (Φₖ − π(Φ)) ⇒ N(0, γ²)` under every `P_x`,
with `γ²` the autocovariance series (17.3). The LIL is `proposition_17_6_1_lil_poisson`. -/
theorem proposition_17_6_1_clt (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hW : Integrable (fun w => w) Γ) (hβ : ∫ w, w ∂Γ < 0)
    (hint : ∀ l ≤ 5, Integrable (fun w => |w| ^ l) Γ) {π : Measure ℝ≥0} [IsProbabilityMeasure π]
    (hπ : haveI := isMarkovKernel_halfLineWalkKernel Γ; IsInvariant (halfLineWalkKernel Γ) π)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → ℝ}
    (hZ : haveI := isMarkovKernel_halfLineWalkKernel Γ
      HasLaw Z (gaussianReal 0
        (asymptoticVariance (halfLineWalkKernel Γ) π fun y : ℝ≥0 => (y : ℝ)).toNNReal) P')
    (x : ℝ≥0) :
    haveI := isMarkovKernel_halfLineWalkKernel Γ
    haveI := isMarkovKernel_pathKernel (halfLineWalkKernel Γ)
    TendstoInDistribution (fun (n : ℕ) ω =>
      (√(n : ℝ))⁻¹ * pathSum (fun y : ℝ≥0 => (y : ℝ) - ∫ z, (z : ℝ) ∂π) n ω)
      atTop Z (fun _ => pathKernel (halfLineWalkKernel Γ) x) P' := by
  have := isMarkovKernel_halfLineWalkKernel Γ
  obtain ⟨ψ, -, hap, hph, c, hc0, hct, X₀, D, hD, hpet, hdrift, hπV⟩ :=
    halfLine_cltMoment Γ hW hβ hint
  rw [(proposition_17_6_1_variance Γ hW hβ hint hπ).2.2.2] at hZ
  exact theorem_17_5_3_clt (f := fun x : ℝ≥0 => (x : ℝ≥0∞) + 1)
    (V := fun x : ℝ≥0 => c⁻¹ * (x : ℝ≥0∞) ^ 2) hph hap
    (measurable_coe_nnreal_ennreal.add measurable_const)
    (fun x => le_add_self) hpet ((measurable_coe_nnreal_ennreal.pow_const 2).const_mul _)
    (fun x => ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hc0) (ENNReal.pow_ne_top
      ENNReal.coe_ne_top)) (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hc0) hD) hdrift hπ
    (hπV π inferInstance hπ) NNReal.continuous_coe.measurable ofReal_abs_coe_le hZ x


/-! ### The scalar linear model (Theorem 17.6.2 with `n = p = 1`) -/

/-- (V4) for the AR(1) model `Xₖ₊₁ = αXₖ + Wₖ₊₁` with `V(x) = x² + 1`, when `|α| < 1`,
`E W² < ∞` and compact sets are petite (MT (12.34) for `n = 1`). -/
theorem ar1_driftV4_sq (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {α : ℝ} (hα : |α| < 1)
    (hW : ∫⁻ w, ‖w‖ₑ ^ 2 ∂Γ ≠ ∞)
    (hcpt : ∀ K : Set ℝ, IsCompact K → IsPetite (ar1Kernel Γ α) K) :
    haveI := isMarkovKernel_ar1Kernel Γ α
    ∃ ρ c : ℝ≥0∞, ρ < 1 ∧ c ≠ ∞ ∧ ∃ C, IsPetite (ar1Kernel Γ α) C ∧
      DriftV4 (ar1Kernel Γ α) (fun x => ‖x‖ₑ ^ 2 + 1) ρ c C := by
  have := isMarkovKernel_ar1Kernel Γ α
  have hVm : Measurable fun x : ℝ => ‖x‖ₑ ^ 2 + 1 :=
    (measurable_enorm.pow_const 2).add measurable_const
  have hV1 : ∀ x : ℝ, 1 ≤ ‖x‖ₑ ^ 2 + 1 := fun x => le_add_self
  have hρ : ∫⁻ w, ‖α + 0 * w‖ₑ ^ 2 ∂Γ < 1 := by
    simp only [zero_mul, add_zero, lintegral_const, measure_univ, mul_one]
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), ENNReal.ofReal_lt_one,
      sq_abs]
    have := abs_lt.1 hα
    nlinarith
  obtain ⟨lam, L, hlam, hL, h⟩ := bilinear_le_mul_add Γ α 0 (k := 2) (by norm_num) hW hρ
  rw [← ar1Kernel_eq_bilinearKernel] at h
  exact (lemma_15_2_8 hVm hV1).2 ⟨isUnboundedOffPetite_enorm_pow hcpt (by norm_num), lam, L,
    hlam, hL, h⟩

/-- The AR(1) mean: `∫ y P(x, dy) = αx` when `E W = 0`. -/
theorem ar1_integral_id (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (α : ℝ)
    (hW1 : Integrable (fun w => w) Γ) (h0 : ∫ w, w ∂Γ = 0) (x : ℝ) :
    ∫ y, y ∂ar1Kernel Γ α x = α * x := by
  have hφ : Measurable fun w : ℝ => α * (x, w).1 + (x, w).2 :=
    (measurable_ar1Step α).comp measurable_prodMk_left
  rw [ar1Kernel, recursionKernel_apply Γ (measurable_ar1Step α) x,
    integral_map hφ.aemeasurable (f := fun y : ℝ => y) measurable_id.aestronglyMeasurable]
  simp only
  rw [integral_add (integrable_const _) hW1, integral_const, probReal_univ, one_smul, h0,
    add_zero]

/-- The AR(1) second moment: `∫ y² P(x, dy) = α²x² + E W²` when `E W = 0`. -/
theorem ar1_integral_sq (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (α : ℝ)
    (hW1 : Integrable (fun w => w) Γ) (hW2 : Integrable (fun w => w ^ 2) Γ)
    (h0 : ∫ w, w ∂Γ = 0) (x : ℝ) :
    ∫ y, y ^ 2 ∂ar1Kernel Γ α x = α ^ 2 * x ^ 2 + ∫ w, w ^ 2 ∂Γ := by
  have hφ : Measurable fun w : ℝ => α * (x, w).1 + (x, w).2 :=
    (measurable_ar1Step α).comp measurable_prodMk_left
  rw [ar1Kernel, recursionKernel_apply Γ (measurable_ar1Step α) x,
    integral_map hφ.aemeasurable (f := fun y : ℝ => y ^ 2)
      (measurable_id.pow_const 2).aestronglyMeasurable]
  have heq : (fun w : ℝ => (α * (x, w).1 + (x, w).2) ^ 2) =
      fun w => (α ^ 2 * x ^ 2 + 2 * (α * x) * w) + w ^ 2 := funext fun w => by
    simp only; ring
  have hi1 : Integrable (fun w : ℝ => α ^ 2 * x ^ 2 + 2 * (α * x) * w) Γ :=
    (integrable_const _).add (hW1.const_mul _)
  rw [heq, integral_add hi1 hW2, integral_add (integrable_const _) (hW1.const_mul _),
    integral_const, probReal_univ, one_smul, integral_const_mul, h0, mul_zero, add_zero]

/-- Moments of `Pⁿ(x, ·)` for AR(1) under (V4): `y` and `y²` are integrable. -/
theorem ar1_integrable_pow (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {α : ℝ} {ρ c : ℝ≥0∞}
    (hρ : ρ < 1) (hc : c ≠ ∞) {C : Set ℝ}
    (hC : haveI := isMarkovKernel_ar1Kernel Γ α; IsPetite (ar1Kernel Γ α) C)
    (h : DriftV4 (ar1Kernel Γ α) (fun x => ‖x‖ₑ ^ 2 + 1) ρ c C) (n : ℕ) (x : ℝ) :
    Integrable (fun y : ℝ => y) ((ar1Kernel Γ α ^ n : Kernel ℝ ℝ) x) ∧
      Integrable (fun y : ℝ => y ^ 2) ((ar1Kernel Γ α ^ n : Kernel ℝ ℝ) x) := by
  have := isMarkovKernel_ar1Kernel Γ α
  have := isMarkovKernel_pow (ar1Kernel Γ α) n
  have hVm : Measurable fun x : ℝ => ‖x‖ₑ ^ 2 + 1 :=
    (measurable_enorm.pow_const 2).add measurable_const
  have hCm : MeasurableSet C := by obtain ⟨_, _, hm, -⟩ := hC; exact hm
  have hPn : ∫⁻ y, (‖y‖ₑ ^ 2 + 1) ∂(ar1Kernel Γ α ^ n : Kernel ℝ ℝ) x ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.pow_ne_top
      enorm_ne_top, ENNReal.one_ne_top⟩, ENNReal.mul_ne_top hc (ENNReal.natCast_ne_top n)⟩)
      (h.pow_le hVm hρ.le hCm n x)
  refine ⟨⟨measurable_id.aestronglyMeasurable, ?_⟩,
    ⟨(measurable_id.pow_const 2).aestronglyMeasurable, ?_⟩⟩
  · refine lt_of_le_of_lt (lintegral_mono fun y => ?_) hPn.lt_top
    rcases le_total ‖y‖ₑ 1 with hy | hy
    · exact hy.trans le_add_self
    · calc ‖y‖ₑ = ‖y‖ₑ ^ 1 := (pow_one _).symm
        _ ≤ ‖y‖ₑ ^ 2 := pow_le_pow_right₀ hy (by norm_num)
        _ ≤ ‖y‖ₑ ^ 2 + 1 := le_self_add
  · change ∫⁻ y, ‖y ^ 2‖ₑ ∂_ < ∞
    simp_rw [enorm_pow]
    exact lt_of_le_of_lt (lintegral_mono fun y => le_self_add) hPn.lt_top

/-- `∫ y Pⁿ(x, dy) = αⁿ x` for AR(1) with `E W = 0`, under (V4). -/
theorem ar1_integral_pow (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {α : ℝ}
    (hW1 : Integrable (fun w => w) Γ) (h0 : ∫ w, w ∂Γ = 0) {ρ c : ℝ≥0∞} (hρ : ρ < 1)
    (hc : c ≠ ∞) {C : Set ℝ}
    (hC : haveI := isMarkovKernel_ar1Kernel Γ α; IsPetite (ar1Kernel Γ α) C)
    (h : DriftV4 (ar1Kernel Γ α) (fun x => ‖x‖ₑ ^ 2 + 1) ρ c C) (n : ℕ) (x : ℝ) :
    ∫ y, y ∂(ar1Kernel Γ α ^ n : Kernel ℝ ℝ) x = α ^ n * x := by
  have := isMarkovKernel_ar1Kernel Γ α
  induction n generalizing x with
  | zero => rw [pow_zero_apply, integral_dirac, pow_zero, one_mul]
  | succ n ih =>
    have := isMarkovKernel_pow (ar1Kernel Γ α) n
    have hi := (ar1_integrable_pow Γ hρ hc hC h (n + 1) x).1
    rw [pow_succ] at hi ⊢
    change ∫ y, y ∂((ar1Kernel Γ α ^ n : Kernel ℝ ℝ) ∘ₖ ar1Kernel Γ α) x = _
    rw [Kernel.integral_comp hi]
    simp_rw [ih]
    rw [integral_const_mul, ar1_integral_id Γ α hW1 h0 x]
    ring

/-- The stationary moments of AR(1) with `E W = 0` and `|α| < 1`: `π(x) = 0` and
`π(x²) = E W²/(1 − α²)`. -/
theorem ar1_stationary_moments (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {α : ℝ} (hα : |α| < 1)
    (hW1 : Integrable (fun w => w) Γ) (hW2 : Integrable (fun w => w ^ 2) Γ)
    (h0 : ∫ w, w ∂Γ = 0) {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : IsInvariant (ar1Kernel Γ α) π) (hπ1 : Integrable (fun y : ℝ => y) π)
    (hπ2 : Integrable (fun y : ℝ => y ^ 2) π) :
    ∫ y, y ∂π = 0 ∧ ∫ y, y ^ 2 ∂π = (∫ w, w ^ 2 ∂Γ) / (1 - α ^ 2) := by
  have := isMarkovKernel_ar1Kernel Γ α
  have ha := abs_lt.1 hα
  have hpi1 : ∫ y, y ∂π = α * ∫ y, y ∂π := by
    conv_lhs => rw [← hπ]
    rw [integral_measure_comp _ _ (by rw [hπ]; exact hπ1)]
    simp_rw [ar1_integral_id Γ α hW1 h0]
    rw [integral_const_mul]
  have hpi2 : ∫ y, y ^ 2 ∂π = α ^ 2 * ∫ y, y ^ 2 ∂π + ∫ w, w ^ 2 ∂Γ := by
    conv_lhs => rw [← hπ]
    rw [integral_measure_comp _ _ (by rw [hπ]; exact hπ2)]
    simp_rw [ar1_integral_sq Γ α hW1 hW2 h0]
    rw [integral_add (hπ2.const_mul _) (integrable_const _), integral_const_mul, integral_const,
      probReal_univ, one_smul]
  have h1 : (1 : ℝ) - α ≠ 0 := by linarith
  have h2 : (1 : ℝ) - α ^ 2 ≠ 0 := by nlinarith
  refine ⟨?_, ?_⟩
  · have : (1 - α) * ∫ y, y ∂π = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h h1
    · exact h
  · rw [eq_div_iff h2]
    linarith

/-- **Theorem 17.6.2** (MT p. 456) for the scalar linear model `Xₖ₊₁ = αXₖ + Wₖ₊₁` (`n = p = 1`,
`c = 1`): if `|α| < 1` (LSS5), `E W = 0`, `E W² = σ² < ∞`, and the chain is `ψ`-irreducible and
aperiodic with compact sets petite (the book's (LSS4), (LCM3) through Proposition 6.3.5), then
the model is `V`-uniformly ergodic for `V(x) = x² + 1` ((V4) for a petite set), positive Harris,
and for its invariant probability `π` the asymptotic variance (17.3) of `Yₖ = Xₖ` is
`γ² = σ²/(1 − α)² = (1 − F)⁻¹ G Σ_W G (1 − F)⁻¹`, the limit of `(1/n) E_π[Sₙ(X)²]`. -/
theorem theorem_17_6_2 (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {α : ℝ} (hα : |α| < 1)
    (hW1 : Integrable (fun w => w) Γ) (hW2 : Integrable (fun w => w ^ 2) Γ)
    (h0 : ∫ w, w ∂Γ = 0) {ψ : Measure ℝ}
    (hψ : haveI := isMarkovKernel_ar1Kernel Γ α; IsMaximalIrreducibility (ar1Kernel Γ α) ψ)
    (hap : IsAperiodic (ar1Kernel Γ α) ψ)
    (hcpt : ∀ K : Set ℝ, IsCompact K → IsPetite (ar1Kernel Γ α) K) :
    haveI := isMarkovKernel_ar1Kernel Γ α
    (∃ ρ c : ℝ≥0∞, ρ < 1 ∧ c ≠ ∞ ∧ ∃ C, IsPetite (ar1Kernel Γ α) C ∧
      DriftV4 (ar1Kernel Γ α) (fun x => ‖x‖ₑ ^ 2 + 1) ρ c C) ∧
    IsPositiveHarris (ar1Kernel Γ α) ψ ∧
    ∀ (π : Measure ℝ) [IsProbabilityMeasure π], IsInvariant (ar1Kernel Γ α) π →
      ∫ y, y ∂π = 0 ∧
      asymptoticVariance (ar1Kernel Γ α) π (fun y => y) = (∫ w, w ^ 2 ∂Γ) / (1 - α) ^ 2 ∧
      Tendsto (fun n : ℕ => (∫ ω, pathSum (fun x => x) n ω ^ 2
        ∂pathMeasure (ar1Kernel Γ α) π) / n) atTop (𝓝 ((∫ w, w ^ 2 ∂Γ) / (1 - α) ^ 2)) := by
  have := isMarkovKernel_ar1Kernel Γ α
  have hWl : ∫⁻ w, ‖w‖ₑ ^ 2 ∂Γ ≠ ∞ := by
    have h := hW2.2.ne
    simp_rw [enorm_pow] at h
    exact h
  obtain ⟨ρ, c, hρ, hc, C, hC, hdrift⟩ := ar1_driftV4_sq Γ hα hWl hcpt
  have hVm : Measurable fun x : ℝ => ‖x‖ₑ ^ 2 + 1 :=
    (measurable_enorm.pow_const 2).add measurable_const
  have hV1 : ∀ x : ℝ, 1 ≤ ‖x‖ₑ ^ 2 + 1 := fun x => le_add_self
  have hVfin : ∀ x : ℝ, ‖x‖ₑ ^ 2 + 1 ≠ ∞ := fun x =>
    ENNReal.add_ne_top.2 ⟨ENNReal.pow_ne_top enorm_ne_top, ENNReal.one_ne_top⟩
  have hph := isPositiveHarris_of_driftV4 hψ hVm hV1 hVfin hρ hc hC hdrift
  refine ⟨⟨ρ, c, hρ, hc, C, hC, hdrift⟩, hph, fun π _ hπ => ?_⟩
  have := isProbabilityMeasure_pathMeasure (ar1Kernel Γ α) π
  -- moments of `π`
  obtain ⟨-, hgeo⟩ := geometric_ergodic_of_driftV4 hψ hap hVm hV1 hρ hc hC hdrift (hVfin 0)
  have hπV := (hgeo π hπ).1
  have hπ2 : Integrable (fun y : ℝ => y ^ 2) π := ⟨(measurable_id.pow_const 2).aestronglyMeasurable,
    by
      change ∫⁻ y, ‖y ^ 2‖ₑ ∂π < ∞
      simp_rw [enorm_pow]
      exact lt_of_le_of_lt (lintegral_mono fun y => le_self_add) hπV.lt_top⟩
  have hπ1 : Integrable (fun y : ℝ => y) π := by
    refine ⟨measurable_id.aestronglyMeasurable, lt_of_le_of_lt (lintegral_mono fun y => ?_)
      hπV.lt_top⟩
    rcases le_total ‖y‖ₑ 1 with hy | hy
    · exact hy.trans le_add_self
    · calc ‖y‖ₑ = ‖y‖ₑ ^ 1 := (pow_one _).symm
        _ ≤ ‖y‖ₑ ^ 2 := pow_le_pow_right₀ hy (by norm_num)
        _ ≤ ‖y‖ₑ ^ 2 + 1 := le_self_add
  obtain ⟨hm, hs⟩ := ar1_stationary_moments Γ hα hW1 hW2 h0 hπ hπ1 hπ2
  set s := ∫ y, y ^ 2 ∂π with hsdef
  set σ2 := ∫ w, w ^ 2 ∂Γ with hσ2
  -- the autocovariances `E_π[X₀ Xₖ] = αᵏ s`
  have hlaw : ∀ j, (pathMeasure (ar1Kernel Γ α) π).map (fun ω => ω j) = π := fun j =>
    hπ.map_coord j
  have hL2 : ∀ j, MemLp (fun ω : ℕ → ℝ => ω j) 2 (pathMeasure (ar1Kernel Γ α) π) := fun j => by
    have h2 : MemLp (fun y : ℝ => y) 2 π :=
      (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 hπ2
    have : MemLp (fun y : ℝ => y) 2 ((pathMeasure (ar1Kernel Γ α) π).map fun ω => ω j) := by
      rw [hlaw j]; exact h2
    exact this.comp_of_map (measurable_pi_apply j).aemeasurable
  have hcov : ∀ k, ∫ ω, ω 0 * ω k ∂pathMeasure (ar1Kernel Γ α) π = α ^ k * s := fun k => by
    rw [integral_coord_zero_mul _ π (h₁ := fun y : ℝ => y) (h₂ := fun y : ℝ => y) measurable_id
      measurable_id k ((hL2 0).integrable_mul (hL2 k))
      ((hL2 k).integrable one_le_two)]
    simp_rw [ar1_integral_pow Γ hW1 h0 hρ hc hC hdrift]
    rw [hsdef, ← integral_const_mul]
    congr 1; ext x; ring
  have h1 : (1 : ℝ) - α ≠ 0 := by linarith [(abs_lt.1 hα).2]
  have h2 : (1 : ℝ) + α ≠ 0 := by linarith [(abs_lt.1 hα).1]
  have hgeom : ∑' k : ℕ, α ^ (k + 1) * s = α / (1 - α) * s := by
    rw [tsum_mul_right]
    congr 1
    simp_rw [pow_succ]
    rw [tsum_mul_right, tsum_geometric_of_abs_lt_one hα]
    field_simp
  have hvar : asymptoticVariance (ar1Kernel Γ α) π (fun y => y) = σ2 / (1 - α) ^ 2 := by
    rw [asymptoticVariance]
    simp only [hm, sub_zero]
    have e0 : ∫ ω, ω 0 ^ 2 ∂pathMeasure (ar1Kernel Γ α) π = s := by
      rw [show (∫ ω, ω 0 ^ 2 ∂pathMeasure (ar1Kernel Γ α) π) =
        ∫ ω, ω 0 * ω 0 ∂pathMeasure (ar1Kernel Γ α) π by simp_rw [sq], hcov 0, pow_zero, one_mul]
    rw [e0]
    simp_rw [hcov]
    rw [hgeom, hs]
    have h3 : (1 : ℝ) - α ^ 2 = (1 - α) * (1 + α) := by ring
    rw [h3]
    field_simp
    ring
  refine ⟨hm, hvar, ?_⟩
  -- the variance limit from Theorem 17.5.4
  have hg : ∀ x : ℝ, ENNReal.ofReal (x ^ 2) ≤ ‖x‖ₑ ^ 2 + 1 := fun x => by
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    exact le_self_add
  obtain ⟨-, -, -, h4, -, h6, -⟩ := theorem_17_5_4 hph hap hVm hV1 hVfin hρ hc hC hdrift hπ
    (g := fun y : ℝ => y) measurable_id hg
  have heq : asymptoticVariance (ar1Kernel Γ α) π (fun y => y) =
      ∫ x, (poissonSeries (ar1Kernel Γ α) π (fun y => y) x ^ 2 -
        kernelInt (ar1Kernel Γ α) (poissonSeries (ar1Kernel Γ α) π (fun y => y)) x ^ 2) ∂π :=
    h6.symm
  rw [← heq, hvar] at h4
  simp only [hm, sub_zero] at h4
  exact h4

/-- **Theorem 17.6.2** (MT p. 456), the CLT, for the scalar linear model: under the hypotheses of
`theorem_17_6_2`, `n^{−1/2} Σ_{k=1}^n Xₖ ⇒ N(0, σ²/(1 − α)²)` under every `P_x`. The LIL is
`theorem_17_6_2_lil_poisson`. -/
theorem theorem_17_6_2_clt (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {α : ℝ} (hα : |α| < 1)
    (hW1 : Integrable (fun w => w) Γ) (hW2 : Integrable (fun w => w ^ 2) Γ)
    (h0 : ∫ w, w ∂Γ = 0) {ψ : Measure ℝ}
    (hψ : haveI := isMarkovKernel_ar1Kernel Γ α; IsMaximalIrreducibility (ar1Kernel Γ α) ψ)
    (hap : IsAperiodic (ar1Kernel Γ α) ψ)
    (hcpt : ∀ K : Set ℝ, IsCompact K → IsPetite (ar1Kernel Γ α) K) {π : Measure ℝ}
    [IsProbabilityMeasure π] (hπ : haveI := isMarkovKernel_ar1Kernel Γ α
      IsInvariant (ar1Kernel Γ α) π)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 ((∫ w, w ^ 2 ∂Γ) / (1 - α) ^ 2).toNNReal) P') (x : ℝ) :
    haveI := isMarkovKernel_ar1Kernel Γ α
    haveI := isMarkovKernel_pathKernel (ar1Kernel Γ α)
    TendstoInDistribution (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * pathSum (fun y => y) n ω)
      atTop Z (fun _ => pathKernel (ar1Kernel Γ α) x) P' := by
  have := isMarkovKernel_ar1Kernel Γ α
  obtain ⟨⟨ρ, c, hρ, hc, C, hC, hdrift⟩, hph, hres⟩ :=
    theorem_17_6_2 Γ hα hW1 hW2 h0 hψ hap hcpt
  obtain ⟨hm, hvar, -⟩ := hres π hπ
  have hVm : Measurable fun x : ℝ => ‖x‖ₑ ^ 2 + 1 :=
    (measurable_enorm.pow_const 2).add measurable_const
  have hg : ∀ x : ℝ, ENNReal.ofReal (x ^ 2) ≤ ‖x‖ₑ ^ 2 + 1 := fun x => by
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    exact le_self_add
  rw [← hvar] at hZ
  have h := theorem_17_0_1_iv hph hap hVm (fun x => le_add_self) (fun x =>
    ENNReal.add_ne_top.2 ⟨ENNReal.pow_ne_top enorm_ne_top, ENNReal.one_ne_top⟩) hρ hc hC hdrift
    hπ (g := fun y : ℝ => y) measurable_id hg hZ x
  simp only [hm, sub_zero] at h
  exact h

end MeynTweedie.GeneralizedDrift
