/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.PositiveNull
import LimitTheorems.DriftHarris
import LimitTheorems.TChainModels
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Invariant measures for general models (MT §10.5)

Meyn and Tweedie, §10.5, pp. 247–253.

**Random walk** (§10.5.1).
* `isInvariant_randomWalk` (10.35): a translation invariant measure (Lebesgue measure on `ℝ`, or
  any right invariant measure on an additive group) is invariant for random walk, for every
  increment law, transient or recurrent; `isInvariant_volume_randomWalk` on `ℝ`.
* **Proposition 10.5.1** (`proposition_10_5_1`, p. 248): random walk on `ℝ` is never positive.
* **Proposition 10.5.2** (`proposition_10_5_2`, p. 248): for a recurrent random walk on `ℝ`, a
  set `A` with `0 < μ^{Leb}(A) < ∞` and `Φ₀` uniform on `A`, the mean number of visits to `B`
  before (and at) the return to `A` is `μ^{Leb}(B)/μ^{Leb}(A)`; `proposition_10_5_2_ratio`:
  hence `E[N_A(B)]/E[N_A(C)] = μ^{Leb}(B)/μ^{Leb}(C)`.
  `proposition_10_5_2_spreadOut`: the book's hypotheses (spread-out increments with mean zero
  and finite variance, and a `ψ`-irreducible chain) give recurrence, through Propositions 6.3.2,
  9.4.5 and Theorem 9.2.2.

**Limits are invariant** ((10.4), p. 232).
* `tendsto_lintegral_of_setwise`: setwise convergence of (sub)probabilities `νₙ(A) → γ(A)`
  implies `∫ f dνₙ → ∫ f dγ` for measurable `0 ≤ f ≤ 1` (through the layer-cake formula and
  dominated convergence);
* `isInvariant_of_tendsto` (10.4): if `μPⁿ(A) → γ(A)` for every `A`, then `γ` is invariant.

**Linear models** (§10.5.4).
* `ar1Kernel_comp`: for the AR(1) model `Xₙ₊₁ = αXₙ + Wₙ₊₁`, `πP` is the law of `αY + W` with
  `Y ∼ π` and `W ∼ Γ` independent, `πP = (π ∘ (α·)⁻¹) ∗ Γ`;
* `isInvariant_ar1_gaussian`: with Gaussian noise `N(0, σ²)`, `N(0, v)` is invariant when
  `v = α² v + σ²`; `isInvariant_ar1_gaussian_stable`: for `|α| < 1` the invariant law is
  `N(0, σ²/(1 − α²))`, the scalar case of `π = N(0, Σ)` with `Σ = Σₖ F^k G Gᵀ (Fᵀ)^k`.

**See also.** The null recurrence of the mean-zero random walk (p. 248) is
`randomWalk_null_recurrent` in `QueueInvariantMinimal`. §10.5.2 (the forward recurrence time
skeleton `V⁺_δ`) is in `RenewalInvariant`, Theorems 10.5.3–10.5.4 (ladder chains and the
GI/G/1 queue) in `LadderInvariant` and `GIG1Invariant`, and the general linear model (the law
of `Σ Fⁱ G Wᵢ`) in `LinearInvariant`.

**Hypotheses.** Proposition 10.5.2 takes `μ^{Leb}(A) < ∞` (the book's "bounded" `A`), and
assumes the chain `ψ`-irreducible, as the book does implicitly.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

/-! ### Random walk -/

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G] in
/-- (10.35), MT p. 247: a right invariant measure `μ` on an additive group is invariant for
random walk with any increment law `Γ`: `∫ μ(dy) Γ(A − y) = μ(A)`. -/
theorem isInvariant_randomWalk (Γ : Measure G) [IsProbabilityMeasure Γ] (μ : Measure G)
    [SFinite μ] [μ.IsAddRightInvariant] : IsInvariant (randomWalkKernel Γ) μ := by
  ext A hA
  rw [measure_kernel_apply μ _ hA]
  simp_rw [randomWalkKernel_apply' Γ _ hA]
  have hm : Measurable fun p : G × G => A.indicator (1 : G → ℝ≥0∞) (p.1 + p.2) :=
    (measurable_one.indicator hA).comp measurable_add_step
  have h1 : ∀ x, Γ {w | x + w ∈ A} = ∫⁻ w, A.indicator 1 (x + w) ∂Γ := fun x => by
    rw [← lintegral_indicator_one (s := {w | x + w ∈ A}) (measurable_const_add x hA)]
    refine lintegral_congr fun w => ?_
    by_cases h : x + w ∈ A
    · simp only [indicator, mem_ofPred_eq, h, ite_true, Pi.one_apply]
    · simp only [indicator, mem_ofPred_eq, h, ite_false]
  simp_rw [h1]
  rw [lintegral_lintegral_swap hm.aemeasurable]
  have h2 : ∀ w, ∫⁻ x, A.indicator (1 : G → ℝ≥0∞) (x + w) ∂μ = μ A := fun w => by
    rw [← measure_preimage_add_right μ w A,
      ← lintegral_indicator_one (s := (· + w) ⁻¹' A) (measurable_add_const w hA)]
    refine lintegral_congr fun x => ?_
    by_cases h : x + w ∈ A
    · simp only [indicator, mem_preimage, h, ite_true, Pi.one_apply]
    · simp only [indicator, mem_preimage, h, ite_false]
  simp_rw [h2]
  rw [lintegral_const, measure_univ, mul_one]

/-- (10.35) on `ℝ`: Lebesgue measure is invariant for random walk on the line. -/
theorem isInvariant_volume_randomWalk (Γ : Measure ℝ) [IsProbabilityMeasure Γ] :
    IsInvariant (randomWalkKernel Γ) volume :=
  isInvariant_randomWalk Γ volume

/-- **Proposition 10.5.1** (MT p. 248): random walk on `ℝ` is never positive recurrent. -/
theorem proposition_10_5_1 (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (ψ : Measure ℝ) :
    haveI := isMarkovKernel_randomWalkKernel Γ
    ¬ IsPositive (randomWalkKernel Γ) ψ := by
  have := isMarkovKernel_randomWalkKernel Γ
  intro hpos
  have hσ : IsSubinvariantMeasure (randomWalkKernel Γ) volume :=
    ⟨inferInstance, (isInvariant_volume_randomWalk Γ).isSubinvariant⟩
  obtain ⟨c, hc, he⟩ := hpos.eq_smul_stationaryDist hσ
  have := isProbabilityMeasure_stationaryDist hpos
  have hu := congrArg (fun m : Measure ℝ => m univ) he
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, Real.volume_univ] at hu
  exact hc hu.symm

/-- The uniform distribution on a set `A` of finite positive Lebesgue measure. -/
noncomputable def uniformOn (A : Set ℝ) : Measure ℝ := (volume A)⁻¹ • volume.restrict A

/-- **Proposition 10.5.2** (MT p. 248): for a recurrent random walk on `ℝ`, a set `A` with
`0 < μ^{Leb}(A) < ∞` and `Φ₀` uniform on `A`, the mean number of visits to `B` up to the return
to `A`, `E[N_A(B)] = ∫ uniform_A(dy) U_A(y, B)`, is `μ^{Leb}(B) / μ^{Leb}(A)`. -/
theorem proposition_10_5_2 (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {ψ : Measure ℝ}
    (hrec : haveI := isMarkovKernel_randomWalkKernel Γ; IsRecurrentChain (randomWalkKernel Γ) ψ)
    {A : Set ℝ} (hA : MeasurableSet A) (hA0 : volume A ≠ 0) (hAfin : volume A ≠ ∞)
    {B : Set ℝ} (hB : MeasurableSet B) :
    ∫⁻ y, tabooPotKernel (randomWalkKernel Γ) hA y B ∂uniformOn A = volume B / volume A := by
  have := isMarkovKernel_randomWalkKernel Γ
  have hπ : IsInvariantMeasure (randomWalkKernel Γ) volume :=
    ⟨inferInstance, isInvariant_volume_randomWalk Γ⟩
  have hψA : 0 < ψ A := by
    refine pos_iff_ne_zero.2 fun h => hA0 ?_
    exact (theorem_10_4_9_equiv hrec hπ (by simp [← Measure.measure_univ_eq_zero])).1 h
  have hmin := theorem_10_4_9 hrec hπ hA hψA hAfin
  rw [uniformOn, lintegral_smul_measure, ← minimalMeasure_apply _ hA _ hB, hmin, smul_eq_mul,
    ENNReal.div_eq_inv_mul]

/-- Proposition 10.5.2, the ratio form: `E[N_A(B)] / E[N_A(C)] = μ^{Leb}(B) / μ^{Leb}(C)` (in
`[0, ∞]`; the book takes `C` bounded with `μ^{Leb}(C) > 0`). -/
theorem proposition_10_5_2_ratio (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {ψ : Measure ℝ}
    (hrec : haveI := isMarkovKernel_randomWalkKernel Γ; IsRecurrentChain (randomWalkKernel Γ) ψ)
    {A : Set ℝ} (hA : MeasurableSet A) (hA0 : volume A ≠ 0) (hAfin : volume A ≠ ∞)
    {B C : Set ℝ} (hB : MeasurableSet B) (hC : MeasurableSet C) :
    (∫⁻ y, tabooPotKernel (randomWalkKernel Γ) hA y B ∂uniformOn A) /
        ∫⁻ y, tabooPotKernel (randomWalkKernel Γ) hA y C ∂uniformOn A =
      volume B / volume C := by
  rw [proposition_10_5_2 Γ hrec hA hA0 hAfin hB, proposition_10_5_2 Γ hrec hA hA0 hAfin hC,
    div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inr (ENNReal.inv_ne_top.2 hA0)) (Or.inr (ENNReal.inv_ne_zero.2 hAfin)),
    inv_inv, div_eq_mul_inv]
  calc volume B * (volume A)⁻¹ * ((volume C)⁻¹ * volume A)
      = volume B * (volume C)⁻¹ * ((volume A)⁻¹ * volume A) := by ring
    _ = volume B * (volume C)⁻¹ := by rw [ENNReal.inv_mul_cancel hA0 hAfin, mul_one]

/-- Proposition 10.5.2 under the book's hypotheses: a `ψ`-irreducible random walk on `ℝ` with
spread-out increments of mean zero and finite variance is recurrent (Propositions 6.3.2, 9.4.5 and
Theorem 9.2.2), so the conclusion of `proposition_10_5_2` holds. -/
theorem proposition_10_5_2_spreadOut (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hs : IsSpreadOut Γ) (hW2 : Integrable (fun w => w ^ 2) Γ) (hβ : ∫ w, w ∂Γ = 0)
    {ψ : Measure ℝ}
    (hψ : haveI := isMarkovKernel_randomWalkKernel Γ;
      IsMaximalIrreducibility (randomWalkKernel Γ) ψ)
    {A : Set ℝ} (hA : MeasurableSet A) (hA0 : volume A ≠ 0) (hAfin : volume A ≠ ∞)
    {B : Set ℝ} (hB : MeasurableSet B) :
    ∫⁻ y, tabooPotKernel (randomWalkKernel Γ) hA y B ∂uniformOn A = volume B / volume A := by
  have := isMarkovKernel_randomWalkKernel Γ
  have hT := (proposition_6_3_2 Γ).2 hs
  have hH : IsHarris (randomWalkKernel Γ) ψ :=
    (theorem_9_2_2_ii hψ hT).2 (proposition_9_4_5 Γ hW2 hβ)
  exact proposition_10_5_2 Γ hH.isRecurrentChain hA hA0 hAfin hB

/-! ### Limits of `μPⁿ` are invariant -/

variable {X : Type*} [MeasurableSpace X] in
/-- Setwise convergence `νₙ(A) → γ(A)` of measures with `νₙ(X) ≤ 1` implies
`∫ f dνₙ → ∫ f dγ` for every measurable `f` with `0 ≤ f ≤ 1` (MT p. 232). -/
theorem tendsto_lintegral_of_setwise {ν : ℕ → Measure X} (hν : ∀ n, ν n univ ≤ 1)
    {γ : Measure X} (h : ∀ A, MeasurableSet A → Tendsto (fun n => ν n A) atTop (𝓝 (γ A)))
    {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, f x ≤ 1) :
    Tendsto (fun n => ∫⁻ x, f x ∂ν n) atTop (𝓝 (∫⁻ x, f x ∂γ)) := by
  have hfr : ∀ x, f x = ENNReal.ofReal (f x).toReal := fun x =>
    (ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (hf1 x))).symm
  have hlc : ∀ ρ : Measure X, ∫⁻ x, f x ∂ρ = ∫⁻ t in Ioi 0, ρ {a | t < (f a).toReal} := by
    intro ρ
    rw [lintegral_congr hfr]
    exact lintegral_eq_lintegral_meas_lt ρ (ae_of_all _ fun _ => ENNReal.toReal_nonneg)
      hf.ennreal_toReal.aemeasurable
  simp_rw [hlc]
  have hset : ∀ t : ℝ, MeasurableSet {a | t < (f a).toReal} := fun t =>
    measurableSet_lt measurable_const hf.ennreal_toReal
  refine tendsto_lintegral_of_dominated_convergence ((Iio (1 : ℝ)).indicator 1)
    (fun n => Antitone.measurable fun s t hst => measure_mono fun a ha =>
      lt_of_le_of_lt hst ha) (fun n => ae_of_all _ fun t => ?_) ?_
    (ae_of_all _ fun t => h _ (hset t))
  · by_cases ht : t < 1
    · rw [indicator_of_mem (show t ∈ Iio 1 from ht), Pi.one_apply]
      exact (measure_mono (subset_univ _)).trans (hν n)
    · have : {a | t < (f a).toReal} = ∅ := by
        refine eq_empty_of_forall_notMem fun a ha => ht ?_
        have h1 : (f a).toReal ≤ 1 := by
          have := ENNReal.toReal_mono ENNReal.one_ne_top (hf1 a)
          rwa [ENNReal.toReal_one] at this
        exact lt_of_lt_of_le ha h1
      simp [this]
  · rw [lintegral_indicator_one measurableSet_Iio, Measure.restrict_apply measurableSet_Iio,
      Iio_inter_Ioi, Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top

variable {X : Type*} [MeasurableSpace X] in
/-- (10.4), MT p. 232: if the laws `μPⁿ` converge setwise to `γ`, then `γ` is invariant. -/
theorem isInvariant_of_tendsto (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {γ : Measure X}
    (h : ∀ A, MeasurableSet A → Tendsto (fun n => ((P ^ n : Kernel X X) ∘ₘ μ) A) atTop
      (𝓝 (γ A))) : IsInvariant P γ := by
  ext A hA
  have hν : ∀ n, ((P ^ n : Kernel X X) ∘ₘ μ) univ ≤ 1 := fun n => by
    have := isMarkovKernel_pow P n
    rw [comp_apply_univ, measure_univ]
  have h1 := tendsto_lintegral_of_setwise hν h (Kernel.measurable_coe P hA)
    (fun x => prob_le_one)
  have h2 : ∀ n, ∫⁻ x, P x A ∂((P ^ n : Kernel X X) ∘ₘ μ) =
      ((P ^ (n + 1) : Kernel X X) ∘ₘ μ) A := fun n => by
    rw [← measure_kernel_apply _ _ hA, Measure.comp_assoc, pow_add_eq P n 1, pow_one]
  simp_rw [h2] at h1
  rw [measure_kernel_apply _ _ hA]
  exact tendsto_nhds_unique h1 ((h A hA).comp (tendsto_add_atTop_nat 1))

/-! ### The AR(1) model -/

/-- For AR(1), `πP` is the law of `αY + W`: `πP = (π ∘ (α·)⁻¹) ∗ Γ`. -/
theorem ar1Kernel_comp (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (α : ℝ) (π : Measure ℝ)
    [SFinite π] : ar1Kernel Γ α ∘ₘ π = (π.map (α * ·)) ∗ Γ := by
  ext A hA
  have hmeas : Measurable fun y => ∫⁻ w, A.indicator (1 : ℝ → ℝ≥0∞) (y + w) ∂Γ :=
    ((measurable_one.indicator hA).comp measurable_add).lintegral_prod_right'
  rw [measure_kernel_apply _ _ hA]
  symm
  rw [← lintegral_indicator_one hA, Measure.lintegral_conv (measurable_one.indicator hA),
    lintegral_map hmeas (measurable_const_mul α)]
  refine lintegral_congr fun x => ?_
  rw [ar1Kernel_apply' Γ α x hA,
    ← lintegral_indicator_one (s := {w | α * x + w ∈ A}) (measurable_const_add (α * x) hA)]
  refine lintegral_congr fun w => ?_
  by_cases h : α * x + w ∈ A
  · simp [indicator, h]
  · simp [indicator, h]

/-- §10.5.4, Gaussian case: for AR(1) with `N(0, σ²)` noise, `N(0, v)` is invariant when
`v = α² v + σ²`. -/
theorem isInvariant_ar1_gaussian (α : ℝ) (σ2 v : ℝ≥0)
    (hv : v = (.mk (α ^ 2) (sq_nonneg α) : ℝ≥0) * v + σ2) :
    IsInvariant (ar1Kernel (gaussianReal 0 σ2) α) (gaussianReal 0 v) := by
  unfold IsInvariant
  rw [ar1Kernel_comp, gaussianReal_map_const_mul, gaussianReal_conv_gaussianReal, mul_zero,
    zero_add, ← hv]

/-- §10.5.4, Gaussian case: for `|α| < 1` the AR(1) model with `N(0, σ²)` noise has the
invariant probability `N(0, σ²/(1 − α²))` (MT p. 253). -/
theorem isInvariant_ar1_gaussian_stable {α : ℝ} (hα : |α| < 1) (σ2 : ℝ≥0) :
    IsInvariant (ar1Kernel (gaussianReal 0 σ2) α)
      (gaussianReal 0 (σ2 / (1 - (.mk (α ^ 2) (sq_nonneg α) : ℝ≥0)))) := by
  refine isInvariant_ar1_gaussian α σ2 _ ?_
  set a : ℝ≥0 := .mk (α ^ 2) (sq_nonneg α) with ha_def
  have ha : α ^ 2 < 1 := by
    have := sq_lt_sq' (by linarith [abs_lt.1 hα]) (abs_lt.1 hα).2
    simpa using this
  have ha1 : a < 1 := by
    rw [← NNReal.coe_lt_coe, ha_def]
    simpa using ha
  have h1a : (1 - a) ≠ 0 := (tsub_pos_of_lt ha1).ne'
  calc σ2 / (1 - a) = σ2 / (1 - a) * (a + (1 - a)) := by
        rw [add_tsub_cancel_of_le ha1.le, mul_one]
    _ = a * (σ2 / (1 - a)) + (1 - a) * (σ2 / (1 - a)) := by ring
    _ = a * (σ2 / (1 - a)) + σ2 := by rw [mul_div_cancel₀ σ2 h1a]

end MeynTweedie.LimitTheorems
